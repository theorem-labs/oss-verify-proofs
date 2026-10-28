(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx As0StepLib As0Tables
     ArtMem ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepot_b BatUnwind_b
     BatAllocG_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtBridge. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatAllocate3_b BatInv_b BatInvMallocPure_b BatInvMalloc_b BatLift_b BatWrapPure_b BatWrapKit_b BatWrapMallocH_b BatWrapMallocX_b BatWrapMallocC_b BatWrapMalloc_b BatIfaceLaws_b
     BatWrapMallocLC_b BatWrapMallocL_b BatFxQ_b BatFxBatch2_b BatFxBatch3_b BatFxDrain_b BatFxImg_b BatImgCell_b BatFreeTop3_b BatInvFreePure_b BatInvFree_b BatInvRepX_b BatInvDrain_b BatWrapFreeA_b BatWrapFreeC_b
     BatRecycle5A_b BatRecycle5I_b BatRecycle5T_b BatRecycle5C_b BatRecycle5D_b BatRecycle5E_b BatRecycle5F_b BatRecycle5_b BatInvRecycleA_b BatInvRecycleC_b BatInvRecycleD_b BatInvRecycleE_b BatInvRecycle_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIfaceABx ShadowRLawsB.      (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section Post.
Variable FSG : Type.

Definition art_rcy_post (rn : art_run) (Gq : art_gs FSG) (LB' : list (Z * Z)) (Sp : Z) (M10 M' : word -> option byte) (G' : art_gs FSG) (evs : list aev) : Prop :=
  art_alloc_rep FSG rn G' LB' M' /\ art_rt_ghost FSG rn G' M'
  /\ g_log FSG G' = g_log FSG Gq ++ evs /\ g_fs FSG G' = g_fs FSG Gq /\ g_depot FSG G' = g_depot FSG Gq /\ g_sec_committed FSG G' = g_sec_committed FSG Gq
  /\ (forall ev, In ev evs -> (exists a l, ev = AMadvise a l) \/ (exists a l, ev = AMunmap a l)) /\ art_cost_sum evs = 0
  /\ (forall c, cl_mu (g_cls FSG G' c) = cl_mu (g_cls FSG Gq c) /\ cl_mfa (g_cls FSG G' c) = cl_mfa (g_cls FSG Gq c))
  /\ (length (art_live (g_log FSG G')) <= length (art_live (g_log FSG Gq)))%nat /\ (length (g_sec FSG G') <= length (g_sec FSG Gq))%nat
  /\ (forall c, 1 <= c <= 30 ->
        Z.of_nat (length (cl_free (g_cls FSG G' c))) + Z.of_nat (length (cl_cache (g_cls FSG G' c))) + art_nq (g_qt FSG G' ++ g_qg FSG G')
        <= Z.of_nat (length (cl_free (g_cls FSG Gq c))) + Z.of_nat (length (cl_cache (g_cls FSG Gq c))) + art_nq (g_qt FSG Gq ++ g_qg FSG Gq))
  /\ art_nq (g_qt FSG G' ++ g_qg FSG G') <= art_nq (g_qt FSG Gq ++ g_qg FSG Gq)
  /\ wrA M' (Sp - 4096) 4096
  /\ exists FPR : Z -> Prop,
       (forall x : word, ~ FPR (U x) -> M' x = M10 x)
       /\ (forall z, in_ev_ranges evs z -> FPR z)
       /\ (forall b0 a, In b0 LB' -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPR a)
       /\ (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPR a)
       /\ (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ FPR a)
       /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPR a)
       /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ FPR a)
       /\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ FPR a)
       /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
             (forall p, In p (art_live (g_log FSG Gq)) -> apart (fst p) (snd p) lo len) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPR a).
End Post.

Lemma art_statics_qmax : forall rn (M : word -> option byte), art_rt_statics rn M -> cellA M (0x13c8b0 + 64) 8 (2 ^ 28).
Proof. intros rn M H. unfold art_rt_statics in H. decompose [and] H. assumption. Qed.

Lemma art_batch_list_first_r : forall (M0 : word -> option byte) bs f l, bs <> [] -> art_batch_list M0 bs f l -> exists b0, In b0 bs /\ f = bt_addr b0.
Proof. intros M0 [|b r] f l NE BL; [contradiction|]. cbn [art_batch_list] in BL. destruct BL as (E & _). exists b. split; [left; reflexivity|exact E]. Qed.

Lemma art_last_app_ne : forall (A : Type) (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d NE. destruct (exists_last NE) as (l' & x & ->). rewrite app_assoc, !last_last. reflexivity.
Qed.

Lemma art_nq_comm : forall a b, art_nq (a ++ b) = art_nq (b ++ a).
Proof. intros a b. rewrite !art_nq_app. lia. Qed.

Section RcyRun.
Variable FSG : Type.
Variable RESV : list (Z * Z).
Variables BUDGET LENMAX KMAX : Z.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.
#[local] Abbreviation EVOK := (art_EVOK RESV BUDGET LENMAX KMAX).

#[using="Type"] Lemma art_wf_rcy_aruns : forall (Q : list aev -> machine_state -> Prop) (R regs' : bvmap 5 word) (M10 rom : word -> option byte) (raw0 : word) (rn : art_run) (Gq : art_gs FSG)
    (LB' : list (Z * Z)) (Sp u bound : Z),
  art_alloc_rep_b FSG bound rn Gq LB' M10 -> g_qt FSG Gq <> [] ->
  2 ^ 28 < art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq) ->
  art_rt_ghost FSG rn Gq M10 ->
  (forall p, In p (art_live (g_log FSG Gq)) ->
     0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
     /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
  (forall p p', In p (art_live (g_log FSG Gq)) -> In p' (art_live (g_log FSG Gq)) -> fst p <> fst p' -> apart (fst p) (snd p) (fst p') (snd p')) ->
  (forall p, In p (art_live (g_log FSG Gq)) -> fst p mod 4096 = 0 /\ snd p mod 4096 = 0) ->
  (forall p, In p (art_live (g_log FSG Gq)) -> wrA M10 (BatPoison_b.SB + fst p / 8) (snd p / 8)) ->
  (forall c, 1 <= c <= 30 -> Z.of_nat (length (cl_free (g_cls FSG Gq c))) + Z.of_nat (length (cl_cache (g_cls FSG Gq c))) + art_nq (g_qt FSG Gq ++ g_qg FSG Gq) <= 65536) ->
  art_nq (g_qt FSG Gq ++ g_qg FSG Gq) <= 2 ^ 15 ->
  getr regs' 1 = (0x56a84 : bv 64)%bv -> getr regs' 2 = Z_to_bv 64 (Sp - 2208) -> getr regs' 4 = Z_to_bv 64 (rn_tp rn) -> getr regs' 10 = Z_to_bv 64 0x13c8b0 -> getr regs' 11 = Z_to_bv 64 (rn_t rn + 80) ->
  getr regs' 12 = Z_to_bv 64 (rn_t rn + 208) -> getr regs' 13 = Z_to_bv 64 (Sp - 2128) ->
  (forall r : reg, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr R r) ->
  ret_ok raw0 -> rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 -> 0 <= u < 2 ^ 64 ->
  art_free3_epi M10 Sp u raw0 R -> wrA M10 (Sp - 4096) 4096 ->
  (forall regsF (M' : word -> option byte) (G' : art_gs FSG) (evs : list aev),
      getr regsF 2 = Z_to_bv 64 Sp ->
      (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsF r = getr R r) ->
      art_rcy_post FSG rn Gq LB' Sp M10 M' G' evs ->
      Q (g_log FSG Gq ++ evs) (mkst regsF raw0 M' rom)) ->
  aruns ASEGS EVOK GR Q (g_log FSG Gq) (mkst regs' (0x542b0 : word) M10 rom).
Proof.
  intros Q R regs' M10 rom raw0 rn Gq LB' Sp u bound REPB NEq BIG GHOST LIVE LIVE2 LIVE3 LIVESH ROOM NRET Q1 Q2 Q4 Q10 Q11 Q12 Q13 QK Hret HHI HS47 Hu EPI W10 K.
  pose proof REPB as (ROK & ST & TH & (_ & PRIM & _) & CH & SECR & QR & _).
  destruct QR as ((ft & lt & Ct80 & Ct88 & Ct96 & Ct104 & BLt) & (fg & lg & Cg160 & Cg168 & Cg176 & Cg184 & BLg) & _ & _ & Cmx & _ & _ & ITEMS & _ & BCH).
  pose proof (art_statics_qmax rn M10 ST) as C16. destruct TH as (Wt & _). pose proof GHOST as (GT1 & GT23 & GT4 & GT5).
  pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
  destruct (PRIM 24 ltac:(lia)) as (RC24 & OK24 & _). pose proof OK24 as (_ & (_ & Haumu24) & _ & _ & _ & Hmu324 & _). destruct RC24 as [_ RR24].
  pose proof RR24 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wu24).
  assert (POS : forall b it, In b (g_qt FSG Gq ++ g_qg FSG Gq) -> In it (bt_items b) -> 0 <= snd it).
  { intros b it Hb Hit. destruct (ITEMS b it Hb Hit) as [(c & w & Hc & V & St)|(s & Hs & Hq & Esu & Esn)].
    - specialize (CH c Hc). cbv zeta in CH. destruct CH as (_ & _ & _ & III). specialize (III w V). rewrite St in III. destruct III as (_ & _ & (bb & _ & _ & _ & _ & Hn0) & _). clear - Hn0. lia.
    - destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & SALL & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (SALL i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
      rewrite Hq in P9. destruct P9 as ((bb & _ & _ & _ & _ & Hn0) & _). rewrite <- Esn. clear - Hn0. lia. }
  destruct (art_batches_bytes_ge (g_qt FSG Gq) (fun b it Hb Hi => POS b it (in_or_app _ _ _ (or_introl Hb)) Hi)) as (BYt & _).
  destruct (art_batches_bytes_ge (g_qg FSG Gq) (fun b it Hb Hi => POS b it (in_or_app _ _ _ (or_intror Hb)) Hi)) as (BYg & _).
  assert (ADDRB : forall b0, In b0 (g_qt FSG Gq ++ g_qg FSG Gq) -> rn_spb rn + 24 * 2 ^ 32 <= bt_addr b0 /\ bt_addr b0 + 8192 <= rn_spb rn + 24 * 2 ^ 32 + cl_mu (g_cls FSG Gq 24)).
  { intros b0 Hb0. destruct (BCH b0 Hb0) as (w0 & Ew0 & (V0 & V1 & _) & _). rewrite art_class_size_24 in V1. rewrite Ew0. clear - V0 V1 Haumu24. lia. }
  destruct (art_batch_list_first_r M10 _ ft lt NEq BLt) as (bf & Hbf & Eft). destruct (ADDRB bf (in_or_app _ _ _ (or_introl Hbf))) as (F0 & F1).
  pose proof (art_batch_list_last M10 _ ft lt NEq BLt) as Elt.
  destruct (ADDRB (art_lastb (g_qt FSG Gq)) (in_or_app _ _ _ (or_introl (BatFxQ_b.art_last_in _ _ _ NEq)))) as (T0 & T1).
  assert (HL : 1 <= Z.of_nat (length (g_qt FSG Gq))) by (clear - NEq; destruct (g_qt FSG Gq); [contradiction|cbn [length]; lia]).
  set (sp := Sp - 2208) in *.
  assert (HGB : Z.of_nat (length (g_qg FSG Gq)) <> 0 -> 0x696000 <= lg /\ lg + 8 <= rn_HI rn /\ apart (rn_t rn + 80) 32 lg 8 /\ wrA M10 lg 8).
  { intros NG. assert (NEg : g_qg FSG Gq <> []) by (intros E; apply NG; rewrite E; reflexivity).
    pose proof (art_batch_list_last M10 _ fg lg NEg BLg) as Elg.
    destruct (ADDRB (art_lastb (g_qg FSG Gq)) (in_or_app _ _ _ (or_intror (BatFxQ_b.art_last_in _ _ _ NEg)))) as (L0 & L1). rewrite <- Elg in L0, L1.
    unfold apart in G11 |- *. split; [clear - L0 G4; lia|]. split; [clear - L1 Hmu324 G6 Eris; lia|]. split; [clear - L0 L1 Hmu324 G11; lia|].
    eapply wr_sub; [exact Wu24| |]; clear - L0 L1; lia. }
  assert (HGB' : Z.of_nat (length (g_qg FSG Gq)) <> 0 -> 0x696000 <= lg /\ lg + 8 < 2 ^ 64 /\ apart (sp - 48) 48 lg 8 /\ apart (rn_t rn + 80) 32 lg 8 /\ wrA M10 lg 8).
  { intros NG. destruct (HGB NG) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [clear - X2 G2; lia|]. split; [unfold apart, sp; clear - X2 HHI; lia|]. split; assumption. }
  assert (Ac : apart (sp - 48) 48 (rn_t rn + 80) 32) by (unfold apart, sp; clear - G8 HHI; lia).
  assert (W48 : wrA M10 (sp - 48) 48) by (eapply wr_sub; [exact W10|unfold sp; clear; lia|unfold sp; clear; lia]).
  assert (Wc : wrA M10 (rn_t rn + 80) 32) by (eapply wr_sub; [exact Wt|clear; lia|clear; lia]).
  assert (Wq : wrA M10 (0x13c8b0 + 152) 40) by (apply art_img_wr; lia).
  (* [comment removed for export] *)
  destruct (art_drain_mem_facts M10 (0x56a84 : bv 64)%bv regs' sp (rn_t rn + 80) (Z.of_nat (length (g_qt FSG Gq))) ft lt (art_batches_bytes (g_qt FSG Gq))
              (Z.of_nat (length (g_qg FSG Gq))) lg (art_batches_bytes (g_qg FSG Gq))
              ltac:(unfold sp; clear - HHI G1; lia) ltac:(unfold sp; clear - HS47; lia) ltac:(clear - G7; lia) ltac:(clear - G8 G2; lia) ltac:(clear - G9; lia) Ac HGB' W48 Wc Wq)
    as (GR1 & AG1 & E1 & E2 & E3 & E4 & E160 & E176 & E184 & E168a & E168b & _ & _ & _ & _ & _ & ELK).
  set (M1 := art_drain_mem M10 sp (0x56a84 : bv 64)%bv regs' (rn_t rn + 80) (Z.of_nat (length (g_qt FSG Gq))) ft lt (art_batches_bytes (g_qt FSG Gq))
                (Z.of_nat (length (g_qg FSG Gq))) lg (art_batches_bytes (g_qg FSG Gq))) in *.
  assert (HSP : rn_HI rn <= sp - 48) by (unfold sp; clear - HHI; lia).
  assert (AGR : art_agree (art_drain_W FSG rn Gq sp lg) M10 M1) by exact AG1.
  pose proof (art_alloc_rep_drain_x FSG rn Gq LB' M10 M1 bound sp ft lt fg lg REPB NEq BLt Cg168 BLg HSP GR1 AGR
                (conj E1 (conj E2 (conj E3 (conj E4 (conj E160 (conj E176 (conj E184 (conj ELK (conj E168a E168b))))))))) LIVE) as REPX.
  set (Gd := art_gs_drain Gq) in *.
  assert (PERM : forall b, In b (g_qt FSG Gd ++ g_qg FSG Gd) -> In b (g_qt FSG Gq ++ g_qg FSG Gq)).
  { intros b Hb. unfold Gd in Hb. cbn [art_gs_drain g_qt g_qg app] in Hb. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [right|left]; exact Hb. }
  assert (GHOSTd : art_rt_ghost FSG rn Gd M1).
  { split; [intros b it Hb Hit; exact (GT1 b it (PERM b Hb) Hit)|]. split; [exact GT23|]. split.
    - intros b Hb. pose proof (GT4 b (PERM b Hb)) as B. destruct (ADDRB b (PERM b Hb)) as (A0 & A1).
      apply (art_byte_at_eq M10 M1); [|exact B]. apply (art_drn_shadow FSG rn Gq LB' M10 M1 bound sp fg lg REPB BLg HSP AGR).
      unfold HeapIfaceA.S, HeapIfaceA.SB. assert (0 <= bt_addr b / 8) by (apply Z.div_pos; [clear - A0 G4|]; lia).
      assert (bt_addr b / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; [lia|]; clear - A1 Hmu324 G6 G2 Eris; lia). lia.
    - apply (art_drn_cell_img FSG rn Gq LB' M10 M1 bound sp fg lg REPB BLg HSP AGR); [lia|cbn; lia|left; cbn; lia|exact GT5]. }
  assert (NEd : g_qg FSG Gd <> []).
  { unfold Gd. cbn [art_gs_drain g_qg]. intros E. apply app_eq_nil in E. exact (NEq (proj2 E)). }
  assert (ENQ : art_nq (g_qg FSG Gd) = art_nq (g_qt FSG Gq ++ g_qg FSG Gq)) by (unfold Gd; cbn [art_gs_drain g_qg]; apply art_nq_comm).
  assert (ROOMd : forall c, 1 <= c <= 30 -> Z.of_nat (length (cl_free (g_cls FSG Gd c))) + Z.of_nat (length (cl_cache (g_cls FSG Gd c))) + art_nq (g_qg FSG Gd) <= 65536).
  { intros c Hc. rewrite ENQ. exact (ROOM c Hc). }
  assert (LIVESHd : forall p, In p (art_live (g_log FSG Gd)) -> wrA M1 (BatPoison_b.SB + fst p / 8) (snd p / 8)) by (intros p Hp; eapply wr_grows; [exact GR1|exact (LIVESH p Hp)]).
  assert (EBY : art_batches_bytes (g_qg FSG Gd) = art_batches_bytes (g_qg FSG Gq) + art_batches_bytes (g_qt FSG Gq)) by (unfold Gd; cbn [art_gs_drain g_qg]; apply art_batches_bytes_app).
  destruct (art_batches_exist FSG rn Gd LB' M1 _ _ REPX GHOSTd (g_qg FSG Gd) (fun b Hb => in_or_app _ _ b (or_intror Hb))) as (xs & XS).
  set (gq := map (art_rb_q (rn_spb rn)) xs). set (k := art_rcy_npop 0xe666661 gq).
  assert (Hk : (k <= length xs)%nat) by (unfold k; pose proof (art_rcy_npop_le 0xe666661 gq) as X; unfold gq in X; rewrite length_map in X; exact X).
  destruct (art_entry_merge FSG rn Gd LB' M1 _ _ REPX xs XS ltac:(rewrite ENQ; exact NRET) ltac:(rewrite EBY; exact BIG)) as (MRG & QB54 & QBM). fold gq in MRG, QB54, QBM.
  destruct (art_entry_qlist FSG rn Gd LB' M1 _ _ REPX xs XS NEd) as (QC160 & QC168 & QC184 & QLST & _). fold gq in QC160, QC168, QC184, QLST.
  destruct (art_entry_qin FSG rn Gd LB' M1 _ _ REPX GHOSTd xs XS) as (QIN & Q24). fold gq in QIN, Q24.
  assert (ELT : lt = bt_addr (art_lastb (g_qg FSG Gd))).
  { rewrite Elt. unfold Gd. cbn [art_gs_drain g_qg]. unfold art_lastb. rewrite (art_last_app_ne _ _ _ _ NEq). reflexivity. }
  assert (LEN2 : 2 * (Z.of_nat (length (g_qg FSG Gq)) + Z.of_nat (length (g_qt FSG Gq))) <= 2 ^ 15).
  { pose proof REPB as (_ & _ & _ & _ & _ & _ & QR' & _). destruct QR' as (_ & _ & _ & _ & _ & _ & NEI & _).
    pose proof (art_nq_len (g_qt FSG Gq ++ g_qg FSG Gq) NEI) as X. rewrite length_app in X. clear - X NRET. lia. }
  assert (EQG : gq = map art_qb (g_qg FSG Gd)) by (unfold gq; exact (art_batches_ok_q FSG rn Gd M1 _ _ XS)).
  assert (ELEN : length xs = length (g_qg FSG Gd)) by (symmetry; exact (Forall2_length XS)).
  pose proof (art_drain_rcy_aruns (rn_HI rn) (rn_t rn) (rn_ctx rn) (rn_tp rn) (rn_key rn) (rn_tsd rn) (rn_spb rn) (rn_ris rn) (rn_qs rn) (rn_parr rn) GEO Htpd Htsdd EVOK GR
                (firstn k xs) (skipn k xs) (fun lg st => aruns ASEGS EVOK GR Q lg st) (g_log FSG Gq) regs' M10 rom (0x56a84 : bv 64)%bv sp (Z.of_nat (length (g_qt FSG Gq))) ft lt (art_batches_bytes (g_qt FSG Gq))
                (Z.of_nat (length (g_qg FSG Gq))) lg (art_batches_bytes (g_qg FSG Gq)) 0xe666661 (Sp - 2128) (art_gr FSG Gd)) as MT.
  cbv zeta in MT. rewrite (firstn_skipn k xs) in MT. fold M1 in MT. unfold gq in *.
  apply (aruns_bind ASEGS EVOK GR (fun lg st => aruns ASEGS EVOK GR Q lg st) Q); [|intros lg0 st X; exact X].
  apply MT; clear MT.
  - exact Q1.
  - unfold ret_ok. bveq.
  - exact Q2.
  - exact Q4.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact Q13.
  - unfold sp. clear - HHI. lia.
  - unfold sp. clear - HS47. lia.
  - clear - HHI G1 HS47. lia.
  - clear - HL LEN2. lia.
  - rewrite Eft. clear - F0 F1 G4 Hmu324 G6 G2 Eris. lia.
  - rewrite Elt. clear - T0 T1 G4 Hmu324 G6 G2 Eris. lia.
  - clear - BYt. lia.
  - clear - BYg. lia.
  - exact BIG.
  - clear. lia.
  - clear - LEN2. lia.
  - exact HGB.
  - eapply wr_sub; [exact W10|unfold sp; clear; lia|unfold sp; clear; lia].
  - exact Wc.
  - exact Cmx.
  - exact C16.
  - exact GT5.
  - clear. lia.
  - exact Ct80.
  - replace (rn_t rn + 80 + 8) with (rn_t rn + 88) by (clear; lia). exact Ct88.
  - replace (rn_t rn + 80 + 16) with (rn_t rn + 96) by (clear; lia). exact Ct96.
  - replace (rn_t rn + 80 + 24) with (rn_t rn + 104) by (clear; lia). exact Ct104.
  - exact Cg160.
  - intros _. exact Cg176.
  - exact Cg184.
  - rewrite EQG, <- art_batches_bytes_q. exact EBY.
  - rewrite length_map, ELEN. unfold Gd. cbn [art_gs_drain g_qg]. rewrite length_app. clear. lia.
  - rewrite length_firstn. fold k. clear - Hk. lia.
  - apply Forall_forall. intros x Hx. exact (proj1 (Forall_forall _ _) (art_entry_rb_ok FSG rn Gd LB' M1 _ _ REPX GHOSTd xs XS) x (art_in_firstn _ k xs x Hx)).
  - exact MRG.
  - exact QB54.
  - exact QBM.
  - rewrite EQG. exact (art_entry_qsep FSG rn Gd LB' M1 _ _ REPX eq_refl).
  - exact QIN.
  - exact Q24.
  - exact (art_entry_sepr FSG rn Gd LB' M1 _ _ REPX eq_refl LIVE LIVE2 xs XS k).
  - exact (art_entry_sepi FSG rn Gd LB' M1 _ _ REPX eq_refl LIVE LIVE2 xs XS k).
  - exact (art_entry_wl FSG rn Gd LB' M1 _ _ REPX xs XS).
  - exact QC168.
  - rewrite ELT. exact QLST.
  - apply (art_entry_inv FSG rn Gd LB' M1 _ _ REPX GHOSTd LIVE LIVE2 LIVE3 ROOMd NEd LIVESHd). exact (art_work_pre_len FSG rn Gd M1 xs XS k).
  - exact (art_entry_pre FSG rn Gd LB' M1 _ _ REPX GHOSTd eq_refl LIVE xs XS k).
  - exact (art_entry_sep FSG rn Gd LB' M1 _ _ REPX eq_refl LIVE LIVE2 xs XS k).
  - exact (art_entry_mem FSG rn Gd LB' M1 _ _ REPX xs XS k).
  - exact (art_entry_evok FSG rn Gd LB' M1 _ _ REPX eq_refl LIVE LIVE3 xs XS k RESV BUDGET LENMAX KMAX).
  - intros regsR M' R1' R2' RK' INV' TRQ C160 C168 C184 C176a C176b Clk QL' HREST.
    assert (HSP5 : rn_HI rn <= sp - 512) by (unfold sp; clear - HHI; lia).
    destruct (art_alloc_rep_recycle FSG rn Gd LB' M1 _ _ REPX GHOSTd eq_refl LIVE LIVE2 LIVE3 xs XS k ROOMd NEd M' sp lt HSP5 INV' TRQ C160 C168 C184 C176a C176b Clk QL' HREST) as (REP' & GH').
    pose proof TRQ as (FRQ & WRQ & _ & _).
    pose proof (art_rcy_agr FSG rn Gd M1 xs k M' sp TRQ) as AGQ.
    (* [comment removed for export] *)
    assert (TEPI : forall a v, sp <= a -> a + 8 <= Sp -> cellA M10 a 8 v -> cellA M' a 8 v).
    { intros a v Ha Ha' C. apply (cell_agree M10 M'); [|unfold sp in Ha; clear - Ha HHI G1; lia|clear - Ha' HS47; cbn; lia|exact C].
      intros x Hx. rewrite (FRQ x ltac:(clear - Hx Ha; lia)). apply AGR. unfold art_drain_W. cbn [art_out fst snd]. cbn in Hx.
      destruct (Z.eqb_spec (Z.of_nat (length (g_qg FSG Gq))) 0) as [E|NG].
      - unfold sp in *. clear - Hx Ha HHI G1 G8. repeat split; try exact I; lia.
      - destruct (HGB NG) as (_ & X6 & _). unfold sp in *. clear - Hx Ha HHI G1 G8 X6. repeat split; try exact I; lia. }
    assert (EPI' : art_free3_epi M' Sp u raw0 R).
    { destruct EPI as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15). unfold art_free3_epi.
      repeat split; (apply TEPI; [unfold sp; clear; lia|clear; lia|assumption]). }
    destruct (art_free3_tail R regsR M' rom raw0 Sp u R2' Hret ltac:(clear - HHI G1; lia) HS47 Hu
                ltac:(intros r Hr; rewrite RK' by (cbn [In] in Hr |- *; clear - Hr; tauto); apply QK; exact Hr) EPI') as (regsF & RUN2 & PF2 & PF1 & PKF).
    eapply ar_steps; [exact RUN2|]. apply ar_done.
    apply (K regsF M' (art_gs_rcy FSG Gd xs k) (art_rels_events (art_rb_work (firstn k xs))) PF2 PKF).
    set (work := art_rb_work (firstn k xs)) in *.
    assert (WLEN : Z.of_nat (length work) = art_nq (firstn k (g_qg FSG Gd))) by exact (art_work_len FSG rn Gd M1 _ _ (art_forall2_firstn _ _ _ k _ _ XS)).
    assert (NQS : art_nq (g_qg FSG Gd) = art_nq (firstn k (g_qg FSG Gd)) + art_nq (skipn k (g_qg FSG Gd))) by (rewrite <- art_nq_app, firstn_skipn; reflexivity).
    pose proof (art_nq_nonneg' (firstn k (g_qg FSG Gd))) as NQ0.
    destruct (art_drn_out_bundle FSG rn Gq LB' M10 bound sp fg lg REPB BLg HSP LIVE) as (DB & DSH & DST & DIM & DFS & DDT & DTH).
    destruct (art_rcy_out_bundle FSG rn Gd LB' M1 _ _ REPX GHOSTd eq_refl LIVE LIVE2 LIVE3 xs XS k ROOMd sp HSP5) as (RB & RST & RIM & RFS & RDT & RTH & RSH).
    fold work in RB, RST, RIM, RFS, RDT, RTH, RSH, AGQ.
    match type of AGQ with art_agree ?W _ _ => set (Wtot := W) in * end.
    unfold art_rcy_post.
    split; [exact REP'|]. split; [exact GH'|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (art_rels_events_kinds work)|]. split; [exact (art_rels_events_cost work)|].
    split. { intros c. destruct (art_steps_au work (art_gr FSG Gd) c) as (_ & X2 & X3). split; [exact X2|exact X3]. }
    split; [exact (art_live_rcy_len work (g_log FSG Gq))|]. split; [exact (art_sec_rcy_len work (g_sec FSG Gq))|].
    assert (TOT : forall c, 1 <= c <= 30 ->
              Z.of_nat (length (cl_cache (g_cls FSG (art_gs_rcy FSG Gd xs k) c))) + Z.of_nat (length (cl_free (g_cls FSG (art_gs_rcy FSG Gd xs k) c)))
              <= Z.of_nat (length (cl_cache (g_cls FSG Gq c))) + Z.of_nat (length (cl_free (g_cls FSG Gq c))) + Z.of_nat (length work)).
    { intros c Hc. exact (art_steps_total work (art_gr FSG Gd) c (art_rg_ok_gr FSG rn Gd LB' M1 _ _ REPX GHOSTd) (art_entry_pre FSG rn Gd LB' M1 _ _ REPX GHOSTd eq_refl LIVE xs XS k) Hc). }
    split. { intros c Hc. specialize (TOT c Hc). cbn [art_gs_rcy g_qt g_qg app] in *. rewrite <- ENQ, NQS. clear - TOT WLEN. lia. }
    split. { cbn [art_gs_rcy g_qt g_qg app]. rewrite <- ENQ, NQS. clear - NQ0. lia. }
    split. { apply WRQ; [clear - HHI G1; lia|clear - HS47; lia|left; clear - HHI; lia|]. eapply wr_grows; [exact GR1|exact W10]. }
    exists (fun z => ~ art_out (art_drain_W FSG rn Gq sp lg) z \/ ~ art_out Wtot z).
    assert (NF : forall a, art_out (art_drain_W FSG rn Gq sp lg) a -> art_out Wtot a -> ~ (~ art_out (art_drain_W FSG rn Gq sp lg) a \/ ~ art_out Wtot a)) by (intros a O1 O2 [X|X]; [exact (X O1)|exact (X O2)]).
    split.
    { intros x N. destruct (art_out_dec (art_drain_W FSG rn Gq sp lg) (U x)) as [O1|NO1]; [|exfalso; apply N; left; exact NO1].
      destruct (art_out_dec Wtot (U x)) as [O2|NO2]; [|exfalso; apply N; right; exact NO2]. rewrite (AGQ x O2). exact (AGR x O1). }
    split.
    { intros z (ev & Hev & Hz). right.
      destruct (art_rcy_ev_range work ev z) as (mb & ms & m & b1 & n0 & Hin & Hr); [|exact Hev|exact Hz|].
      - intros mb ms m b1 n0 Hin. pose proof (art_pre_geo FSG rn Gd LB' M1 _ _ REPX _ (proj1 (art_work_ok FSG rn Gd LB' M1 _ _ REPX xs XS _ (art_work_pre_in xs k _ Hin)))) as GE. cbn [art_el_geo] in GE.
        destruct (LIVE _ GE) as (L0 & L1 & _). destruct (LIVE3 _ GE) as (A1 & A2). cbn [fst snd] in *. split; [exact A1|]. split; [exact A2|]. clear - L0 L1. lia.
      - destruct (art_rels_fp_sec_in (rn_t rn) (rn_spb rn) (rn_ris rn) (rn_parr rn) (sp - 192) work (art_gr FSG Gd) mb ms m b1 n0 Hin) as (I1 & I2).
        unfold Wtot. destruct Hr as [Hr|Hr].
        + apply (art_in_not_out _ (mb, ms) z); [apply in_or_app; right; apply in_or_app; left; exact I1|exact Hr].
        + apply (art_in_not_out _ (BatPoison_b.SB + mb / 8, ms / 8) z); [apply in_or_app; right; apply in_or_app; left; exact I2|exact Hr]. }
    split; [intros b0 a Hb0 Ha; apply NF; [exact (DB b0 a Hb0 Ha)|exact (RB b0 a Hb0 Ha)]|].
    split. { intros a Ha Ns. apply NF; [apply DST; [clear - Ha; lia|unfold sp; clear - Ns; lia]|apply RST; [clear - Ha; lia|unfold sp; clear - Ns; lia]]. }
    split. { intros a Ha NZ. assert (X : ~ (0x13c580 <= a < 0x1d1980)) by (intros X; apply NZ; unfold art_zone_statics; clear - X; lia).
             apply NF; [apply DIM; [exact Ha|clear - X; lia]|apply RIM; [exact Ha|clear - X; lia|clear - X; lia]]. }
    split; [intros a Ha; apply NF; [exact (DFS a Ha)|exact (RFS a Ha)]|].
    split; [intros a Ha; apply NF; [exact (DDT a Ha)|exact (RDT a Ha)]|].
    split; [intros a Ha; apply NF; [apply DTH; clear - Ha; lia|apply RTH; clear - Ha; lia]|].
    intros lo len a H0 H1 H47 Hkk Hl Ha. apply NF.
    + apply DSH. pose proof (art_S_ge lo 0 ltac:(lia)) as B0. pose proof (art_S_lt (lo + len - 1) (2 ^ 44) ltac:(clear - H47; lia)) as B1. clear - Ha B0 B1. lia.
    + apply (RSH lo len a H0 H1 H47); [unfold apart; clear - Hkk Kspb H1; lia|exact Hl|exact Ha].
Qed.
End RcyRun.

(* [comment removed for export] *)
Section LiveShadow.
#[using="Type"] Lemma art_live_shadow_wr : forall MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A (M : word -> option byte) model p,
  BInv ASEGS MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A M model -> In p (art_live log) ->
  0 < fst p -> 0 < snd p -> fst p + snd p <= 2 ^ 47 -> (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p) -> fst p mod 4096 = 0 -> snd p mod 4096 = 0 ->
  wrA (mrestrict (bhid A model) M) (BatPoison_b.SB + fst p / 8) (snd p / 8).
Proof.
  intros MAPS0 RESV0 NOACC0 CEIL BASE BUDGET log A M model [r len] B0 Hp H0 H1 H47 Hsh A1 A2. cbn [fst snd] in *.
  pose proof (Z.div_mod r 4096 ltac:(lia)) as D1. rewrite A1 in D1. pose proof (Z.div_mod len 4096 ltac:(lia)) as D2. rewrite A2 in D2.
  assert (E1 : 8 * (r / 8) = r). { replace r with ((512 * (r / 4096)) * 8) at 1 by lia. rewrite Z_div_mult by lia. lia. }
  assert (E2 : 8 * (len / 8) = len). { replace len with ((512 * (len / 4096)) * 8) at 1 by lia. rewrite Z_div_mult by lia. lia. }
  assert (WIN : In (art_shlo r, art_shhi r len) A) by (apply (bi_windows _ _ _ _ _ _ _ _ _ _ _ B0); apply art_log_window; apply art_live_in_log; exact Hp).
  pose proof (art_window_allowed A r len r len WIN ltac:(lia) ltac:(lia) H1 ltac:(lia) H47 E1 E2) as SA.
  assert (Q0 : 0 <= r / 8) by (apply Z.div_pos; lia). unfold BatPoison_b.SB.
  apply art_wr_of_bytes; [lia|lia|]. intros i Hi.
  set (x := 2147450880 + r / 8 + i).
  assert (INS : in_shadow_of r len x). { unfold in_shadow_of, HeapIfaceA.S, HeapIfaceA.SB, x. replace (r + len - 1) with (8 * (r / 8 + len / 8 - 1) + 7) by lia.
    replace ((8 * (r / 8 + len / 8 - 1) + 7) / 8) with (r / 8 + len / 8 - 1) by (apply Z.div_unique with 7; lia). lia. }
  pose proof (art_allowed_vis (m_vm_lazy model) A (Z_to_bv 64 x) (SA x INS)) as VIS.
  assert (DEF : M (Z_to_bv 64 x) <> None).
  { apply (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B0). rewrite art_u_lit by (unfold x; lia). unfold in_shadow_rw, LSH_LO, LSH_HI, HSH_LO, HSH_HI, x. destruct Hsh as [Hs|Hs]; [left|right]; lia. }
  unfold byte_at, mrestrict, bhid. fold x. rewrite VIS. destruct (M (Z_to_bv 64 x)) as [b|] eqn:E; [|contradiction]. exists (U b). f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End LiveShadow.

Lemma art_objs_in_r : forall rn, In (ar_fs (rn_ar rn), FS_BYTES) (art_objs rn) /\ In (0x10000, 0x41000) (art_objs rn) /\ In (0x51000, 0xe0000) (art_objs rn)
  /\ In (0x131000, 0x8000) (art_objs rn) /\ In (0x139000, 0x55d000) (art_objs rn).
Proof. intros rn. unfold art_objs. cbn [In]. tauto. Qed.

(* [comment removed for export] *)
Section ExitClientR.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.

#[using="HLlo HLhi HLst"] Lemma art_wfc_client_r : forall rn LB FF LK (A A' : list (Z * Z)) (M M1 : word -> option byte) (FPT : Z -> Prop) (LV : list (Z * Z)) (Sp u n qr : Z),
  art_run_ok rn -> art_client_ok rn LB FF LK A M -> incl A A' ->
  (forall x : word, ~ FPT (U x) -> M1 x = M x) ->
  (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPT a) ->
  (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPT a) ->
  (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ FPT a) ->
  (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPT a) ->
  (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> (forall p, In p LV -> apart (fst p) (snd p) lo len) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT a) ->
  (forall p, In p LV -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
  (0x696000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES) -> 1 <= qr ->
  (forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f)) ->
  (forall a, Sp - 4096 <= a < Sp -> M1 (Z_to_bv 64 a) <> None) ->
  art_client_ok rn (lb_remove u LB) FF LK A' M1 /\ aheap_pres L (rn_ar rn) (lb_remove u LB) FF Sp 4096 M M1.
Proof.
  intros rn LB FF LK A A' M M1 FPT LV Sp u n qr ROK CLI INC FRF NFPB NFPS NFPI NFS NSH LVF (U1 & U2 & Uf) Hq0 FSIN SCR1.
  pose proof ROK as ROK'. rok_open14 ROK'. geo_open GEO.
  destruct CLI as (CB & CND & CSA1 & CSA2 & CS1 & CS2 & CS3 & CS4 & CS5 & CS6 & CSI & CSP & CS16).
  assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ FPT a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha N. apply FRF. rewrite art_u_lit by lia. exact N. }
  assert (HIeq : ahl_ceil (rn_ar rn) = rn_HI rn) by reflexivity.
  assert (SHA : forall a0 n0, shadow_allowed A a0 n0 -> shadow_allowed A' a0 n0).
  { intros a0 n0 SA x Hx. apply (art_page_allowedb_incl A A' _ INC). exact (SA x Hx). }
  assert (SHB : forall b, In b (lb_remove u LB) -> 0 <= fst b -> fst b + snd b <= rn_HI rn -> 0 < snd b -> HAJ.shadow_blkR M (fst b) (snd b) -> HAJ.shadow_blkR M1 (fst b) (snd b)).
  { intros b Hb Hb0 Hb1 Hnb SB0.
    assert (T : forall j, 0 <= j -> (j < snd b / 8 \/ (j = snd b / 8 /\ snd b mod 8 <> 0)) -> forall v, byte_at M (HeapIfaceA.S (fst b) + j) v -> byte_at M1 (HeapIfaceA.S (fst b) + j) v).
    { intros j Hj0 Hj v Bt.
      pose proof (art_S_blk_hi (fst b) (snd b) j Hnb Hj) as H1. pose proof (art_S_ge (fst b) 0 ltac:(lia)) as H0. pose proof (art_S_lt (fst b + snd b - 1) (2 ^ 44) ltac:(clear - Hb1 G2; lia)) as H2.
      apply (art_byte_at_eq M M1); [|exact Bt]. apply EQ; [clear - H0 H1 H2 Hj0; lia|]. apply (NFPB b _ Hb). right. unfold in_shadow_of. clear - H1 Hj0. lia. }
    exact (shadow_blkR_tby M M1 (fst b) (snd b) Hnb T SB0). }
  split.
  - unfold art_client_ok. split; [|split; [|split; [exact (SHA _ _ CSA1)|split; [exact (SHA _ _ CSA2)|repeat split; first [assumption|exact (SHA _ _ CSI)|lia]]]]].
    + intros b Hb. pose proof (art_lb_remove_in u LB b Hb) as Hb'. destruct (CB b Hb') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
      split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|]. split; [exact B6|].
      split. { intros i Hi. rewrite EQ; [exact (B7 i Hi)|rewrite HIeq in B5; clear - B1 B5 Hi G2; lia|]. apply (NFPB b _ Hb). left. clear - Hi. lia. }
      split; [apply SHB; [exact Hb|clear - B1; lia|rewrite HIeq in B5; exact B5|exact B4|exact B8]|]. split; [exact (SHA _ _ B9)|].
      split. { intros b' Hb2. apply B10. apply NoDup_ListNoDup in CND. pose proof (art_lb_remove_gone u LB b CND Hb) as Nu.
               rewrite (art_lb_remove_comm u (fst b) LB ltac:(intros E; apply Nu; symmetry; exact E)) in Hb2. exact (art_lb_remove_in u _ b' Hb2). }
      split; [exact B11|exact B12].
    + apply NoDup_ListNoDup. apply art_lb_remove_nodup. apply NoDup_ListNoDup. exact CND.
  - split.
    + intros a Ha CLa. apply EQ; [exact Ha|]. unfold aclient, aclient_g in CLa.
      destruct CLa as [(b & Hb & Hr)|[((C1 & C2) & C3)|[((C1 & C2) & C3)|[(f & Hf & R1 & R2)|[SH|[(f & Hf & SH)|(b & Hb & SH)]]]]]].
      * apply (NFPB b a Hb). left. exact Hr.
      * apply NFPS; [rewrite HIeq in C1; clear - C1 C2; lia|exact C3].
      * rewrite HLlo in C1. rewrite HLhi in C2. apply NFPI; [lia|]. intros D. apply C3. apply HLst. exact D.
      * destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & _). apply NFS. clear - R1 F1 F2. lia.
      * apply (NSH (ahl_ceil (rn_ar rn)) (2 ^ 47 - ahl_ceil (rn_ar rn)) a); [rewrite HIeq; clear - G1; lia|rewrite HIeq; clear - G2; lia|clear; lia|rewrite HIeq; right; clear - Kend; lia|rewrite HIeq; right; exact U2| |exact SH].
        intros p Hp. destruct (LVF p Hp) as (_ & L1 & L2 & _). rewrite HIeq. unfold apart. clear - L1 L2. lia.
      * destruct (FSIN f (in_or_app _ _ _ (or_introl Hf))) as (F1 & F2 & F3). unfold FS_BYTES in *.
        apply (NSH (ff_addr f) (ff_bytes (ff_class f)) a); [clear - F1 Flo; lia|exact F3|clear - F2 Fhi G2; lia|unfold apart in Afkb; clear - F1 F2 Afkb; lia|unfold apart in Uf; clear - F1 F2 Uf Hq0; lia| |exact SH].
        intros p Hp. destruct (LVF p Hp) as (_ & _ & _ & OB). pose proof (OB (ar_fs (rn_ar rn), FS_BYTES) (proj1 (art_objs_in_r rn))) as Ap. cbn [fst snd] in Ap. unfold apart, FS_BYTES in *. clear - Ap F1 F2. lia.
      * apply (NFPB b a Hb). right. exact SH.
    + intros a Ha. exact (SCR1 a Ha).
Qed.
End ExitClientR.

(* [comment removed for export] *)
Section Finish.
Variable FSG : Type.
Variable FSINV : art_run -> FSG -> list fframe -> list fframe -> (word -> option byte) -> Prop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable L : asan_layout.
Hypothesis HLlo : hl_img_lo L = 0x10000.
Hypothesis HLhi : hl_img_hi L = 0x696000.
Hypothesis HLst : forall a, art_zone_statics a -> hl_rt_static L a.
(* [comment removed for export] *)
Hypothesis FSLAW2 : forall gfs FF LK (M M' : word -> option byte), FSINV rn gfs FF LK M -> (forall x : word, art_fs_zone rn (U x) -> M' x = M x) ->
  (forall a : word, in_shadow_rw (U a) -> M' a <> None) -> FSINV rn gfs FF LK M'.
Hypothesis FS_IN : forall gfs FF LK M, FSINV rn gfs FF LK M ->
  forall f, In f (FF ++ LK) -> ar_fs (rn_ar rn) <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= ar_fs (rn_ar rn) + FS_BYTES /\ 0 < ff_bytes (ff_class f).
Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Definition art_fpl_bundle (G : art_gs FSG) (LB : list (Z * Z)) (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (M M10 : word -> option byte) : Prop :=
  let Gfr := art_gs_free G (rn_spb rn) k u n kb in
  let FPL := art_free_fpl FSG rn G Sp u q16 qr km in
  mem_grows M M10
  /\ (forall x : word, ~ FPL (U x) -> M10 x = M x)
  /\ (forall b0 a, In b0 (lb_remove u LB) -> (fst b0 <= a < fst b0 + snd b0 \/ in_shadow_of (fst b0) (snd b0) a) -> ~ FPL a)
  /\ (forall a, rn_HI rn <= a < 2 ^ 64 -> ~ (Sp - 4096 <= a < Sp) -> ~ FPL a)
  /\ (forall a, 0x10000 <= a < 0x696000 -> ~ art_zone_statics a -> ~ FPL a)
  /\ (forall a, ar_fs (rn_ar rn) <= a < ar_fs (rn_ar rn) + FS_BYTES -> ~ FPL a)
  /\ (forall a, rn_dtls rn <= a < rn_dtls rn + 4096 -> ~ FPL a)
  /\ (forall a, rn_t rn + 72 <= a < rn_t rn + 80 -> ~ FPL a)
  /\ (forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
        (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPL a)
  /\ (0x696000 <= u - 16 /\ u + 8 * qr <= rn_HI rn /\ apart (u - 16) (16 + 8 * qr) (ar_fs (rn_ar rn)) FS_BYTES).

Definition art_free_pkg3 (G : art_gs FSG) (LB : list (Z * Z)) (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (Mr0 Mr' : word -> option byte) (G' : art_gs FSG) (evs : list aev) : Prop :=
  exists M10 : word -> option byte,
    art_fpl_bundle G LB Sp u n q16 qr km kb k Mr0 M10
    /\ art_rcy_post FSG rn (art_gs_free G (rn_spb rn) k u n kb) (lb_remove u LB) Sp M10 Mr' G' evs.

#[using="Type"] Lemma art_in_ev_ranges_app : forall l1 l2 z, in_ev_ranges (l1 ++ l2) z -> in_ev_ranges l1 z \/ in_ev_ranges l2 z.
Proof. intros l1 l2 z (ev & Hev & Hz). apply in_app_or in Hev. destruct Hev as [H|H]; [left|right]; exists ev; split; assumption. Qed.

#[using="HLlo HLhi HLst FSLAW2 FS_IN"] Theorem art_wf_finish3 : forall (G : art_gs FSG) (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A A' : list (Z * Z)) (M M1 : word -> option byte) (model model' : Model)
    (log' : list aev) (Sp u n q16 qr km : Z) (kb : nat) (k : art_fk) (G' : art_gs FSG) (evs : list aev),
  let cl24 := g_cls FSG G 24 in
  let newb := art_free_newb (g_qt FSG G) in
  art_run_ok rn -> art_cls_ok 24 cl24 -> cl_mu cl24 = 262144 * km ->
  (newb = true -> cl_cache cl24 = [] -> art_cls_needs_populate 24 cl24 = true -> cl_mu cl24 + 262144 <= 3758096384
     /\ art_cls_mfa' cl24 (Z.of_nat (length (cl_free cl24)) + art_cls_new 24 cl24) <= 536870912) ->
  FSINV rn (g_fs FSG G) FF LK M -> art_credit_ok FSG BUDGET rn G LB cr -> art_client_ok rn LB FF LK A M -> art_kn_ok MAPS0 RESV0 rn ->
  art_lazy_ok FSG rn G A (m_vm_lazy model) -> art_eager_ok LB A (m_vm_lazy model) ->
  g_depot FSG G = Datatypes.S kb -> In (u, n) LB -> 1 <= qr -> rn_HI rn + 4096 <= Sp - 4096 -> Sp < 2 ^ 47 ->
  (forall p, In p (art_live (g_log FSG G)) ->
     0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (fst p + snd p <= 0x7fff7000 \/ 0x10007fff8000 <= fst p)
     /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))) ->
  log' = g_log FSG G ++ art_enq_events newb (rn_spb rn) cl24 ++ evs ->
  BInv ASEGS MAPS0 RESV0 NOACC0 (rn_HI rn) BASE BUDGET log' A' M1 model' ->
  bhist A M model (g_log FSG G) log' A' M1 model' ->
  art_free_pkg3 G LB Sp u n q16 qr km kb k (mrestrict (bhid A model) M) (mrestrict (bhid A' model') M1) G' evs ->
  art_ri_inv FSG MAPS0 RESV0 NOACC0 BASE BUDGET FSINV rn (lb_remove u LB) FF LK cr A' M1 (vml_of model')
  /\ aheap_pres L (rn_ar rn) (lb_remove u LB) FF Sp 4096 M M1.
Proof.
  intros G LB FF LK cr A A' M M1 model model' log' Sp u n q16 qr km kb k G' evs cl24 newb ROK OK Emu Room FS CRED CLI KN LZ EG Edep Hin Hq0 HHI HS47 LIVE Elog B1 BH (M10 & FPLB & POST).
  set (Gfr := art_gs_free G (rn_spb rn) k u n kb) in *. set (Mr0 := mrestrict (bhid A model) M) in *. set (Mr' := mrestrict (bhid A' model') M1) in *.
  destruct FPLB as (GRW & FRL & NFPB & NFPS & NFPI & NFS & NDT & NTH & NSH & UF).
  destruct POST as (REP' & _ & ELG & EFS & EDP & ESC & KINDS & COST & EMU & LLEN & SLEN & CNT & NQLE & WSCR & FPR & FRR & EVR & RB & RST & RIM & RFS & RDT & RTH & RSH).
  set (FPL := art_free_fpl FSG rn G Sp u q16 qr km) in *. set (FPT3 := fun z => FPL z \/ FPR z).
  assert (ELIVE : art_live (g_log FSG Gfr) = art_live (g_log FSG G)) by (unfold Gfr; apply art_frep_live_eq).
  assert (NF : forall a, ~ FPL a -> ~ FPR a -> ~ FPT3 a) by (intros a N1 N2 [X|X]; [exact (N1 X)|exact (N2 X)]).
  (* [comment removed for export] *)
  assert (FR3 : forall x : word, ~ FPT3 (U x) -> Mr' x = Mr0 x).
  { intros x N. rewrite (FRR x ltac:(intros X; apply N; right; exact X)). apply FRL. intros X. apply N. left. exact X. }
  assert (EVL : forall sfx, log' = g_log FSG G ++ sfx -> forall z, in_ev_ranges sfx z -> FPT3 z).
  { intros sfx El z Hz. rewrite Elog in El. apply app_inv_head in El. subst sfx. apply art_in_ev_ranges_app in Hz. destruct Hz as [Hz|Hz]; [left|right; exact (EVR z Hz)].
    unfold FPL, art_free_fpl. right. apply (art_enq_events_in_fp _ _ _ _ _ _ _ _ _ _ _ cl24 z OK Emu); [|exact Hz]. intros E1 E2 E3. exact (proj2 (Room E1 E2 E3)). }
  pose proof (art_lift_frame A A' M M1 model model' (g_log FSG G) log' BH FPT3 FR3 EVL) as FRF.
  pose proof BH as (sfx & Esfx & INC & BH2 & _ & BH4 & BH5).
  assert (Esfx' : sfx = art_enq_events newb (rn_spb rn) cl24 ++ evs). { rewrite Elog in Esfx. apply app_inv_head in Esfx. symmetry. exact Esfx. }
  assert (NONULL : forall len r, ~ In (AMmapNull len r) sfx).
  { intros len r Hev. rewrite Esfx' in Hev. apply in_app_or in Hev. destruct Hev as [Hev|Hev].
    - unfold art_enq_events in Hev. destruct newb; [exact (art_ca_events_no_null _ _ _ _ _ Hev)|destruct Hev].
    - destruct (KINDS _ Hev) as [(a & l & E)|(a & l & E)]; discriminate E. }
  assert (NONR : forall a l, ~ In (AMmapFixedNR a l) sfx).
  { intros a l Hev. rewrite Esfx' in Hev. apply in_app_or in Hev. destruct Hev as [Hev|Hev].
    - unfold art_enq_events in Hev. destruct newb; [exact (art_ca_events_no_nr _ _ _ _ _ Hev)|destruct Hev].
    - destruct (KINDS _ Hev) as [(a0 & l0 & E)|(a0 & l0 & E)]; discriminate E. }
  assert (B5' : forall x : word, page_in_ranges (page_base x) (m_vm_lazy model') = true -> page_in_ranges (page_base x) (m_vm_lazy model) = true).
  { intros x Hx. destruct (BH5 x Hx) as [Hl|(a & l & Hev & _)]; [exact Hl|]. exfalso. exact (NONR _ _ Hev). }
  (* [comment removed for export] *)
  pose proof ROK as ROK'. rok_open14 ROK'. pose proof GEO as GEO'. geo_open GEO'.
  pose proof REP' as (_ & _ & _ & (_ & PRIM' & _) & _). destruct (PRIM' 24 ltac:(lia)) as ((_ & RR') & OK' & _).
  destruct RR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Wfa' & Wu'). pose proof OK' as (_ & (Hau0' & Haumu') & _ & _ & _ & Hmu3' & _ & (Hmfa0' & Hmfa1') & _).
  assert (VIS : forall x : word, (rn_spb rn + 24 * 2 ^ 32 <= U x < rn_spb rn + 24 * 2 ^ 32 + cl_mu (g_cls FSG G' 24)
                        \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa (g_cls FSG G' 24)) -> bhid A' model' x = false).
  { intros x [Hx|Hx].
    - apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + 24 * 2 ^ 32) (cl_mu (g_cls FSG G' 24)) ltac:(clear - G4; lia) ltac:(clear - G6 G2 Eris Hmu3'; lia) ltac:(right; clear - G4; lia) Wu' x Hx).
    - apply (art_vis_of_wr (bhid A' model') M1 (rn_spb rn + 24 * 2 ^ 32 + 3758096384) (cl_mfa (g_cls FSG G' 24)) ltac:(clear - G4; lia) ltac:(clear - G6 G2 Eris Hmfa1'; lia) ltac:(right; clear - G4; lia) Wfa' x Hx). }
  (* [comment removed for export] *)
  assert (LZ' : art_lazy_ok FSG rn G' A' (m_vm_lazy model')).
  { apply (art_lazy_ok_step FSG rn G G' A (m_vm_lazy model) A' (m_vm_lazy model') LZ INC).
    - intros x Hx. exact (proj1 (BH2 x Hx)).
    - intros wd Hwd. destruct (BH4 wd Hwd) as [Hi|(len & r & Hev & _)]; [exact Hi|]. exfalso. exact (NONULL _ _ Hev).
    - exact B5'.
    - intros x C.
      assert (C1 : art_committed FSG rn Gfr (U x) \/ (rn_spb rn + 24 * 2 ^ 32 <= U x < rn_spb rn + 24 * 2 ^ 32 + cl_mu (g_cls FSG G' 24)
                        \/ rn_spb rn + 24 * 2 ^ 32 + 3758096384 <= U x < rn_spb rn + 24 * 2 ^ 32 + 3758096384 + cl_mfa (g_cls FSG G' 24))).
      { unfold art_committed in C |- *. destruct C as [RI|[(c0 & Hc0 & Zc)|(PC & P)]]; [left; left; exact RI| |left; right; right; split; [rewrite <- ESC; exact PC|exact P]].
        destruct (EMU c0) as (X1 & X2). rewrite X1, X2 in Zc. left. right. left. exists c0. split; [exact Hc0|exact Zc]. }
      destruct C1 as [C1|V]; [|right; exact (VIS x V)].
      destruct (art_free_committed FSG rn G u n kb k false (U x) C1) as [C0|V]; [left; exact C0|right]. apply VIS.
      destruct (EMU 24) as (X1 & X2). rewrite X1, X2. unfold Gfr. cbn [art_gs_free g_cls]. rewrite Z.eqb_refl. exact V. }
  assert (EG' : art_eager_ok (lb_remove u LB) A' (m_vm_lazy model')) by exact (art_eager_ok_remove LB A (m_vm_lazy model) A' (m_vm_lazy model') u EG (bi_awf _ _ _ _ _ _ _ _ _ _ _ B1) B5').
  (* [comment removed for export] *)
  assert (NSH3 : forall lo len a, 0 <= lo -> 0 < len -> lo + len <= 2 ^ 47 -> (lo + len <= rn_kbase rn \/ rn_kbase rn + 0x2000011000 <= lo) ->
            (lo + len <= u - 16 \/ u + 8 * qr <= lo) -> (forall p, In p (art_live (g_log FSG G)) -> apart (fst p) (snd p) lo len) -> HeapIfaceA.S lo <= a <= HeapIfaceA.S (lo + len - 1) -> ~ FPT3 a).
  { intros lo len a H0 H1 H47 Hk Hu Hl Ha. apply NF; [exact (NSH lo len a H0 H1 H47 Hk Hu Ha)|]. apply (RSH lo len a H0 H1 H47 Hk); [|exact Ha]. intros p Hp. rewrite ELIVE in Hp. exact (Hl p Hp). }
  (* [comment removed for export] *)
  assert (SCR1 : forall a, Sp - 4096 <= a < Sp -> M1 (Z_to_bv 64 a) <> None).
  { intros a Ha. pose proof (art_wr_wview ASEGS Mr' (Sp - 4096) 4096 ltac:(clear - HHI G1; lia) ltac:(clear - HS47; lia) WSCR (Z_to_bv 64 a)) as V.
    rewrite art_u_lit in V by (clear - Ha HHI G1 HS47; lia). specialize (V ltac:(clear - Ha; lia)). rewrite art_wview_off in V by (rewrite art_u_lit by (clear - Ha HHI G1 HS47; lia); right; clear - Ha HHI G1; lia).
    unfold Mr', mrestrict in V. destruct (bhid A' model' (Z_to_bv 64 a)); [exfalso; apply V; reflexivity|exact V]. }
  assert (LVF : forall p, In p (art_live (g_log FSG G)) -> 0 < fst p /\ 0 < snd p /\ fst p + snd p <= rn_HI rn /\ (forall o, In o (art_objs rn) -> apart (fst p) (snd p) (fst o) (snd o))).
  { intros p Hp. destruct (LIVE p Hp) as (X0 & X1 & X2 & _ & X4). split; [exact X0|]. split; [exact X1|]. split; [exact X2|exact X4]. }
  destruct (art_wfc_client_r L HLlo HLhi HLst rn LB FF LK A A' M M1 FPT3 (art_live (g_log FSG G)) Sp u n qr ROK CLI INC FRF
              ltac:(intros b0 a Hb0 Ha; apply NF; [exact (NFPB b0 a Hb0 Ha)|exact (RB b0 a Hb0 Ha)])
              ltac:(intros a Ha Ns; apply NF; [exact (NFPS a Ha Ns)|exact (RST a Ha Ns)])
              ltac:(intros a Ha NZ; apply NF; [exact (NFPI a Ha NZ)|exact (RIM a Ha NZ)])
              ltac:(intros a Ha; apply NF; [exact (NFS a Ha)|exact (RFS a Ha)])
              NSH3 LVF UF Hq0 (FS_IN _ _ _ _ FS) SCR1) as (CLI' & AHP).
  split; [|exact AHP].
  (* [comment removed for export] *)
  exists G'. cbn [vml_of fst snd]. fold Mr'.
  split; [exact REP'|]. split.
  { rewrite EFS. unfold Gfr. cbn [art_gs_free g_fs]. apply (FSLAW2 (g_fs FSG G) FF LK M M1 FS); [|exact (bi_shdef _ _ _ _ _ _ _ _ _ _ _ B1)]. intros x Hz. apply FRF. destruct UF as (U1 & U2 & Uf). unfold FS_BYTES in *.
    destruct Hz as [Z|[Z|[Z|[(Z & NS)|[Z|Z]]]]].
    - apply NF; [apply NFS|apply RFS]; unfold FS_BYTES; exact Z.
    - apply NF; [apply NTH|apply RTH]; exact Z.
    - apply (NSH3 (ar_fs (rn_ar rn)) 0xb09000 (U x)); [clear - Flo; lia|clear; lia|clear - Fhi G2; lia|unfold apart in Afkb; clear - Afkb; lia|unfold apart in Uf; clear - Uf Hq0; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & _ & _ & OB). pose proof (OB (ar_fs (rn_ar rn), FS_BYTES) (proj1 (art_objs_in_r rn))) as Ap. cbn [fst snd] in Ap. unfold FS_BYTES in Ap. exact Ap.
      + pose proof (art_S_pred (ar_fs (rn_ar rn) + 0xb09000)). unfold FS_BYTES in Z. clear - Z H. lia.
    - apply NF; [apply NFPI|apply RIM]; assumption.
    - apply (NSH3 0x10000 (0x696000 - 0x10000) (U x)); [clear; lia|clear; lia|clear; lia|left; clear - G4 Kspb; lia|left; clear - U1; lia| |].
      + intros p Hp. destruct (LVF p Hp) as (_ & P1 & _ & OB).
        destruct (art_objs_in_r rn) as (_ & I1 & I2 & I3 & I4).
        pose proof (OB _ I1) as A1. pose proof (OB _ I2) as A2. pose proof (OB _ I3) as A3. pose proof (OB _ I4) as A4.
        cbn [fst snd] in A1, A2, A3, A4. unfold apart in *. clear - A1 A2 A3 A4 P1. lia.
      + pose proof (art_S_pred 0x696000). replace (0x10000 + (0x696000 - 0x10000) - 1) with (0x696000 - 1) by lia. clear - Z H. lia.
    - apply NF; [apply NDT|apply RDT]; exact Z. }
  split. { assert (ELOG : g_log FSG G' = log') by (rewrite ELG, Elog; unfold Gfr; cbn [art_gs_free g_log]; rewrite app_assoc; reflexivity). rewrite ELOG. exact (BINV_intro _ _ _ _ _ _ _ _ _ _ _ B1). }
  split.
  { (* [comment removed for export] *)
    pose proof (art_wfx_credit FSG BUDGET rn G LB cr u n kb k false OK CRED Edep Hin) as CR1. cbv zeta in CR1. fold Gfr in CR1.
    destruct CR1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8). unfold art_credit_ok, art_nret in *.
    split; [exact C1|]. split; [exact C2|]. split; [rewrite ELG, art_cost_sum_app, COST; clear - C3; lia|]. split; [clear - C4 LLEN; lia|]. split; [clear - C5 SLEN; lia|].
    split; [rewrite EDP; exact C6|]. split; [clear - C7 NQLE; lia|].
    intros c0 Hc0. destruct (C8 c0 Hc0) as (K1 & K2). destruct (EMU c0) as (X1 & _). rewrite X1. split; [exact K1|]. specialize (CNT c0 Hc0). clear - K2 CNT. lia. }
  split; [exact CLI'|]. split; [exact KN|]. split; [exact LZ'|exact EG'].
Qed.
End Finish.
