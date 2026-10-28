(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Cells Mem Frame. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog BnBase BnModel BnTree ApBase ApLogic.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface D_defs I_lkit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA BnIfaceA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import BnRepDefs BnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rw_cells_app_l : forall (m : mem) a cs1 cs2, rw_cells ctasegs m a (cs1 ++ cs2) -> rw_cells ctasegs m a cs1.
Proof.
  intros m a cs1 cs2 ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  split; [split; [exact W1 | exact Hb1]|].
  destruct Hw as (X1 & X2 & X3). rewrite cells_size_app, Nat2Z.inj_add in X2, X3.
  split; [exact X1|]. split; [lia|]. intros i Hi. apply X3. lia.
Qed.

Lemma rw_cells_app_join : forall (m : mem) a cs1 cs2,
  rw_cells ctasegs m a cs1 -> rw_cells ctasegs m (a + Z.of_nat (cells_size cs1)) cs2 -> rw_cells ctasegs m a (cs1 ++ cs2).
Proof.
  intros m a cs1 cs2 ((W1 & B1) & (X1 & X2 & X3)) ((W2 & B2) & (Y1 & Y2 & Y3)).
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [exact X1|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply X3; lia|].
    replace (a + i) with (a + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Y3. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_skip : forall (m : mem) a cs1 cs2 n, rw_cells ctasegs m a (cs1 ++ cs2) -> Z.of_nat (cells_size cs1) = n -> rw_cells ctasegs m (a + n) cs2.
Proof. intros m a cs1 cs2 n H <-. exact (rw_cells_app_r m a cs1 cs2 H). Qed.

(* [comment removed for export] *)
Fixpoint cb_first (n : nat) (cs : list cell) : list cell :=
  match n, cs with S n', c :: cs' => CB (csize c) (cbytes c) :: cb_first n' cs' | _, _ => cs end.

Lemma cb_first_props : forall n cs, cells_wf cs -> cells_wf (cb_first n cs) /\ cells_bytes (cb_first n cs) = cells_bytes cs /\ cells_size (cb_first n cs) = cells_size cs.
Proof.
  induction n as [|n IH]; intros cs W; [cbn; auto|]. destruct cs as [|c cs]; [cbn; auto|].
  cbn [cells_wf] in W. destruct W as [Wc Wr]. destruct (IH cs Wr) as (I1 & I2 & I3).
  cbn [cb_first cells_wf cells_bytes cells_size cell_wf csize cbytes]. rewrite I2, I3.
  split; [split; [exact (cbytes_length c Wc) | exact I1]|]. split; reflexivity.
Qed.

Lemma rw_cells_cb_first : forall (m : mem) a cs n, rw_cells ctasegs m a cs -> rw_cells ctasegs m a (cb_first n cs).
Proof.
  intros m a cs n H. pose proof H as [[W _] _]. destruct (cb_first_props n cs W) as (P1 & P2 & P3).
  exact (rw_cells_recast m a cs _ H P1 P2 P3).
Qed.

(* [comment removed for export] *)
Definition fr_list (nl ns : nat) (cs : list cell) : list cell :=
  cb_first nl (firstn nl cs) ++ CB (cells_size (firstn ns (skipn nl cs))) (cells_bytes (firstn ns (skipn nl cs))) :: skipn ns (skipn nl cs).

Lemma rw_cells_fr_list : forall (m : mem) a cs nl ns, rw_cells ctasegs m a cs -> rw_cells ctasegs m a (fr_list nl ns cs).
Proof.
  intros m a cs nl ns H. unfold fr_list.
  rewrite <- (firstn_skipn nl cs) in H. rewrite <- (firstn_skipn ns (skipn nl cs)) in H.
  apply (rw_cells_merge ctasegs m a (firstn nl cs) (firstn ns (skipn nl cs)) (skipn ns (skipn nl cs))) in H.
  pose proof H as [[W _] _]. apply cells_wf_app in W as [W1 W2].
  destruct (cb_first_props nl (firstn nl cs) W1) as (P1 & P2 & P3).
  apply (rw_cells_recast m a _ _ H).
  - apply cells_wf_app. split; [exact P1 | exact W2].
  - rewrite !cells_bytes_app, P2. reflexivity.
  - rewrite !cells_size_app, P3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fr_saved : forall (m : mem) spa loc g junk gj (sav tail : list cell) SPv,
  rw_cells ctasegs m spa ((loc ++ [CB g junk]) ++ tail) ->
  junk = gj ++ cells_bytes sav -> cells_wf sav ->
  Z.of_nat (cells_size (loc ++ [CB g junk])) = SPv - spa - Z.of_nat (cells_size tail) ->
  rw_cells ctasegs m (SPv - Z.of_nat (cells_size sav) - Z.of_nat (cells_size tail)) (sav ++ tail).
Proof.
  intros m spa loc g junk gj sav tail SPv H EJ WS SZ.
  rewrite <- app_assoc in H. pose proof (rw_cells_app_r m spa loc _ H) as R. cbn [app] in R.
  pose proof R as [[WR _] _]. cbn [cells_wf cell_wf] in WR. destruct WR as [LJ WT].
  assert (LG : (g = length gj + cells_size sav)%nat) by (rewrite <- LJ, EJ, length_app, (cells_bytes_length sav WS); reflexivity).
  assert (R2 : rw_cells ctasegs m (spa + Z.of_nat (cells_size loc)) ([CB (length gj) gj] ++ (sav ++ tail))).
  { apply (rw_cells_recast m _ _ _ R).
    - cbn [app cells_wf cell_wf]. split; [reflexivity|]. apply cells_wf_app. split; assumption.
    - cbn [app cells_bytes cbytes]. rewrite cells_bytes_app, EJ, <- app_assoc. reflexivity.
    - cbn [app cells_size csize]. rewrite cells_size_app, LG. lia. }
  pose proof (rw_cells_app_r m _ [CB (length gj) gj] _ R2) as R3. cbn [cells_size csize] in R3.
  rewrite cells_size_app in SZ. cbn [cells_size csize] in SZ.
  replace (SPv - Z.of_nat (cells_size sav) - Z.of_nat (cells_size tail)) with (spa + Z.of_nat (cells_size loc) + Z.of_nat (length gj + 0)) by lia.
  exact R3.
Qed.

(* [comment removed for export] *)
Lemma fr_whole : forall (m : mem) spa cs n, rw_cells ctasegs m spa cs -> Z.of_nat (cells_size cs) = n -> exists jall, rw_cells ctasegs m spa [CB (Z.to_nat n) jall].
Proof.
  intros m spa cs n H <-. destruct (rw_cells_forget ctasegs m spa cs H) as (j & R). exists j. rewrite Nat2Z.id. exact R.
Qed.


Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma implA_reframe : forall {A} (t : btree bptr A) Σ Σ' (Q : A -> rts RT -> machine_state -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> rt_live RT Σ' = rt_live RT Σ ->
  implA t Σ' Q ms -> implA t Σ Q ms.
Proof.
  intros A t Σ Σ' Q ms EA EM EL H X Φ D S L. eapply cps_conseq; [exact (H X Φ D S ltac:(eapply linked_same; [exact L| rewrite EL; reflexivity])) | | intros c Hc; exact Hc].
  intros c Hc. exact (ASTA_reframe Σ Σ' _ c EA EM Hc).
Qed.

Lemma implAp_reframe : forall {A} (t : aprog bptr A) Σ Σ' (Q : A -> rts RT -> machine_state -> Prop) ms,
  rt_allow RT Σ' = rt_allow RT Σ -> (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) -> rt_live RT Σ' = rt_live RT Σ ->
  implAp t Σ' Q ms -> implAp t Σ Q ms.
Proof.
  intros A t Σ Σ' Q ms EA EM EL H X Φ D S L. eapply cps_conseq; [exact (H X Φ D S ltac:(eapply linked_same; [exact L| rewrite EL; reflexivity])) | | intros c Hc; exact Hc].
  intros c Hc. exact (ASTA_reframe Σ Σ' _ c EA EM Hc).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma frame_release_cellsA : forall Σ OW LB m f k,
  @BnHeapA.AHEAP (push AR f k) Σ OW LB m -> (forall b, In b LB -> off_fr f k b) ->
  exists fl, rw_cells ctasegs m fl [C1 (Z_to_bv 8 1)] /\ ro_cells ctasegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
    /\ 0 < fl /\ fl + 1 <= ACEIL /\ (fl + 1 <= f \/ f + fs_size k <= fl) /\ (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl)
    /\ (fl + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fl)
    /\ (forall b, In b (OW ++ LB) -> fl < blk_addr b \/ blk_addr b + blk_size b <= fl)
    /\ forall m', munch [(fl, fl + 1)] m m' -> wmono ctasegs m m' -> rw_cells ctasegs m' fl [C1 (Z_to_bv 8 0)] ->
         exists Σ', @BnHeapA.AHEAP AR Σ' OW LB m' /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ
                    /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo) /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = FR /\ rt_sp0 RT Σ' = rt_sp0 RT Σ.
Proof.
  intros Σ OW LB m f k H OFF. pose proof H as (HA & HS & HFr & (FW & PB & LBr & P1 & P2 & FP & AP) & ND & F1 & F2).
  cbn [ar_FR ar_RT ar_SP0 push amb] in HFr, HS.
  destruct (af_frame_release RT AF Σ m f k FR HA HFr) as (Σ' & fl & C1 & NC & L0 & L1 & L2 & L3 & L4 & C2 & REL).
  exists fl. split; [exact C1|]. split; [exact C2|]. split; [exact L0|].
  split; [unfold BnHeapA.ACEIL; rewrite <- HS; exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|].
  split.
  { intros b Hb. destruct (Z_lt_dec fl (blk_addr b)) as [X|X]; [left; exact X|]. destruct (Z_le_dec (blk_addr b + blk_size b) fl) as [Y|Y]; [right; exact Y|].
    exfalso. apply NC. rewrite HFr. change ((f, k) :: FR) with (@ar_FR (push AR f k)).
    apply (@AH_aclient (push AR f k) Σ OW LB m USTACK_TOP fl H). right; right. exists b. split; [exact Hb | lia]. }
  intros m' MU WM CF. destruct (REL m' MU WM CF) as (ART' & EF' & EL' & ES' & EC' & EA' & EM').
  exists Σ'. split; [| exact (conj EC' (conj EA' (conj EM' (conj EL' (conj EF' ES')))))].
  split; [exact ART'|]. split; [rewrite ES'; exact HS|]. split; [exact EF'|]. split; [| exact (conj ND (conj F1 F2))].
  split.
  - unfold fr_wr in FW |- *. cbn [ar_FR push amb] in FW. apply Forall_cons_iff in FW as [_ FW].
    eapply Forall_impl; [| exact FW]. intros [f' k'] [X1 X2]. cbn [fst snd] in *. split; eapply wr_at_transport; eassumption.
  - exists PB, LBr. split; [exact P1|]. split; [rewrite EL'; exact P2|]. split; [| exact AP].
    apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) FP b Hb) as PK.
    assert (HbL : In b LB) by (eapply Permutation_in; [symmetry; exact P1 | apply in_or_app; left; exact Hb]).
    pose proof (pb_ok_pop Σ OW LB m b f k H PK (OFF b HbL)) as (PI & Hn & WR & AC).
    split; [exact PI|]. split; [exact Hn|]. split; [exact (wr_at_transport ctasegs m m' _ _ WR WM)|].
    eapply acc_agree; [apply (agree_on_of_munch_nw _ _ _ MU) | exact AC |].
    intros i Hi. cbn [outside]. split; [| exact I].
    destruct PK as (PI' & _). pose proof (@pb_shadow_range (push AR f k) Σ OW LB m b i H PI' Hi) as SR. unfold SHLO, SHHI in SR. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fr3_heap : forall Σ OW LB m m' f k spl sph n1 n2,
  In (f, k) FR -> AHEAP Σ OW LB m -> munch [(spl, sph); (f, f + n1); (shad f, shad f + n2)] m m' -> wmono ctasegs m m' ->
  ACEIL <= spl -> sph <= USTACK_TOP -> n1 <= fs_size k - 8 -> n2 <= fs_size k / 8 ->
  (forall b, In b LB -> off_fr f k b) -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' f k spl sph n1 n2 Hf H MU WM L1 L2 N1 N2 OFF.
  eapply (AH_frame_fr Σ OW LB m m' _ f k Hf H MU WM); [| exact OFF].
  constructor; [left; left; cbn [fst snd]; lia|].
  constructor; [right; left; cbn [fst snd]; lia|].
  constructor; [right; right; cbn [fst snd]; lia| constructor].
Qed.

(* [comment removed for export] *)
Lemma fr3_outside : forall Σ OW LB m0 f k spl sph (L : list block) a,
  AHEAP Σ OW LB m0 -> fr_geo f k -> ACEIL <= spl -> spl <= sph ->
  (forall b, In b L -> In b (OW ++ LB)) -> (forall b, In b L -> off_fr f k b) ->
  aclient_addr L sph a ->
  ~ (spl <= a < sph) /\ ~ (f <= a < f + fs_size k) /\ ~ (shad f <= a < shad f + fs_size k / 8).
Proof.
  intros Σ OW LB m0 f k spl sph L a H (G1 & G2 & G3 & G4 & G5) L1 L2 INC OFF Ha.
  pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (fs_size_pos k) as (FS1 & _). destruct (fs_size_div8 k) as (FS2 & FS3).
  assert (SHR : 2147450880 <= shad f /\ shad f + fs_size k / 8 <= 17594333495296).
  { rewrite <- shad_fr_end. unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha G3 SHR C2 L1 L2 FS1. lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    clear - Hin Hr G4 SHR C1 L1 L2. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (OFF b Hb) as O. pose proof (AH_offsh _ _ _ _ b H (INC b Hb)) as OS. pose proof (AH_range_gen _ _ _ _ b H (INC b Hb)) as (_ & _ & _ & BC & _).
    unfold off_fr, SHLO, SHHI in *. clear - O OS BC Hr SHR L1 L2. lia.
Qed.

(* [comment removed for export] *)
Lemma fr3_agree : forall Σ OW LB m0 m m' f k spl sph n1 n2 (L : list block),
  AHEAP Σ OW LB m0 -> munch [(spl, sph); (f, f + n1); (shad f, shad f + n2)] m m' ->
  fr_geo f k -> n1 <= fs_size k -> n2 <= fs_size k / 8 ->
  ACEIL <= spl -> spl <= sph -> (forall b, In b L -> In b (OW ++ LB)) -> (forall b, In b L -> off_fr f k b) ->
  agree_on (aclient_addr L sph) m m'.
Proof.
  intros Σ OW LB m0 m m' f k spl sph n1 n2 L H MU GEO N1 N2 L1 L2 INC OFF.
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside].
  pose proof (fr3_outside Σ OW LB m0 f k spl sph L a H GEO L1 L2 INC OFF Ha) as NF.
  clear - NF N1 N2. lia.
Qed.

(* [comment removed for export] *)
Lemma stack_munch_agree : forall Σ OW LB m m1 W sp, AHEAP Σ OW LB m -> munch W m m1 -> Forall (fun iv => ACEIL <= fst iv /\ snd iv <= sp) W ->
  agree_on (aclient_addr (OW ++ LB) sp) m m1.
Proof.
  intros Σ OW LB m m1 W sp HEAP MU HW. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. clear MU.
  induction HW as [|[x y] W [H1 H2] HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH].
  intros Hx. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia | |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
Qed.

(* [comment removed for export] *)
Lemma AH_ow_off_fr : forall Σ OW LB m f k b, AHEAP Σ OW LB m -> In (f, k) FR -> In b OW -> off_fr f k b.
Proof.
  intros Σ OW LB m f k b H Hf Hb. pose proof (AH_live_ow _ _ _ _ b H Hb) as HL.
  destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R). specialize (R _ _ HL). unfold off_fr. lia.
Qed.

(* [comment removed for export] *)
Lemma fl_agree : forall Σ OW LB m0 m m' fl sph (L : list block),
  AHEAP Σ OW LB m0 -> munch [(fl, fl + 1)] m m' ->
  fl + 1 <= ACEIL -> ACEIL <= sph -> (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl) ->
  (forall b, In b L -> fl < blk_addr b \/ blk_addr b + blk_size b <= fl) ->
  agree_on (aclient_addr L sph) m m'.
Proof.
  intros Σ OW LB m0 m m' fl sph L H MU L1 L2 L3 OFF.
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha L1 L2. lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A in L3.
    clear - Hin Hr L3. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (OFF b Hb) as O. clear - O Hr. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma cps_step_rt : forall Σ ms (R : rts RT -> machine_state -> Prop) (E : rts RT -> Prop) (Q : config -> Prop),
  cps ctasegs (ASTA RT Σ PMc (eq ms)) (fun c => exists Σ', ASTA RT Σ' PMc (R Σ') c /\ E Σ') ->
  (forall Σ' ms', R Σ' ms' -> E Σ' -> cps ctasegs (ASTA RT Σ' PMc (eq ms')) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq ms)) Q.
Proof.
  intros Σ ms R E Q H1 H2. eapply cps_seq; [exact H1|]. intros T c (Σ' & Hc & HE) Hk.
  destruct (ASTA_unpack RT Σ' PMc (R Σ') c Hc) as (ms' & HR & Hc'). exact (H2 Σ' ms' HR HE T c Hc' Hk).
Qed.

(* [comment removed for export] *)
Lemma stack_malloc_cpsAp : forall (k : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z),
  (k <= 4)%nat -> AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + RT_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A ->
  (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz (e_stack_malloc_g k)) fc None m (seg_rom ctasegs))))
            (fun c => exists Σ1, ASTA RT Σ1 PMc (sm_postA k ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo m Σ1) c
                      /\ rt_live RT Σ1 = rt_live RT Σ).
Proof.
  intros until lo. intros Hk HEAP ST CEIL LO SPT SP16 MI -> HLEN CRED.
  unfold MallocRep.wz in *.
  pose proof (AH_frames _ _ _ _ HEAP) as EFR.
  eapply cps_conseq; [ eapply (rc2_stack_malloc RT (@ar_RC2 AR) k Hk Σ PMc) with (lo := lo); try reflexivity | intros c Hc; exact Hc | ].
  - exact ar_PMc_fdfs.
  - exact ar_PMc_ms.
  - rewrite EFR. exact HLEN.
  - exact CRED.
  - exact (AH_art _ _ _ _ HEAP).
  - exact MI.
  - rewrite <- (Z_to_bv_bv_unsigned sp). eapply call_okA; [exact HEAP | exact ST | exact CEIL | exact LO | exact SPT | exact SP16].
  - intros c (Σ1 & f & Hc & EF1 & EL1 & ES1 & EC1 & F0 & F64 & FTOP). exists Σ1. split; [| exact EL1].
    eapply ASTA_conseq; [exact Hc|]. clear Hc.
    intros ms (m1 & RS & (ART1 & MI1 & WM1 & ST1) & PRES & W1 & W2).
    destruct RS as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F1 & fc1 & ->).
    destruct (AH_enter Σ Σ1 OW LB m m1 f k _ HEAP ART1 EF1 EL1 ES1 PRES W1 W2) as (HEAP1 & FRESH).
    unfold sm_postA, MallocRep.wz. do 16 eexists. exists m1, f. split; [reflexivity|].
    split; [exact MI1|]. split; [exact ST1|]. split; [exact WM1|].
    split; [eapply (AH_agree _ _ _ _ _ _ _ HEAP); rewrite <- EFR; exact PRES|].
    split; [exact HEAP1|]. split; [exact FRESH|]. split; [exact EC1|].
    split; [exact (@AH_fr_geo (push AR f k) Σ1 OW LB m1 f k HEAP1 (or_introl eq_refl))|].
    pose proof (fs_size_pos k) as (FS1 & _). destruct (fs_size_div8 k) as (_ & FS2).
    split; [exact (wr_at_rw_CB m1 f _ W1 ltac:(lia)) | exact (wr_at_rw_CB m1 (shad f) _ W2 ltac:(lia))].
Qed.

(* [comment removed for export] *)
Lemma implAp_post : forall {A} (t : aprog bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implAp t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> implAp (ARet a) Σ' Q ms') -> implAp t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HK X Φ D S L T c Hc Hk.
  apply (H X Φ D S L T c Hc).
  intros c' (a & X' & Σ' & HΦ & L' & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (HK a Σ' ms' HQ1 X' Φ D ltac:(cbn [asafe]; exact HΦ) L' T c' Hc'' Hk).
Qed.

(* [comment removed for export] *)
Lemma implAp_of_cps : forall {A} (t : aprog bptr A) Σ Σ1 (Q : A -> rts RT -> machine_state -> Prop) ms ms1,
  (forall K : config -> Prop, cps ctasegs (ASTA RT Σ1 PMc (eq ms1)) K -> cps ctasegs (ASTA RT Σ PMc (eq ms)) K) ->
  rt_live RT Σ1 = rt_live RT Σ ->
  implAp t Σ1 Q ms1 -> implAp t Σ Q ms.
Proof.
  intros A t Σ Σ1 Q ms ms1 HC EL H X Φ D S L. apply HC. apply (H X Φ D S). eapply linked_same; [exact L | rewrite EL; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma implAp_elim : forall {A} (t : aprog bptr A) Σ Σ1 (Q : A -> rts RT -> machine_state -> Prop) ms1 X Φ D,
  implAp t Σ1 Q ms1 -> asafe t X Φ -> linked D Σ X -> rt_live RT Σ1 = rt_live RT Σ ->
  cps ctasegs (ASTA RT Σ1 PMc (eq ms1)) (fun c => exists a X' Σ', Φ a X' /\ linked D Σ' X' /\ ASTA RT Σ' PMc (Q a Σ') c).
Proof.
  intros A t Σ Σ1 Q ms1 X Φ D H S L EL. apply (H X Φ D S). eapply linked_same; [exact L | rewrite EL; reflexivity].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lib_addr_aclient : forall (OW LB : list block) SP a, lib_addr OW a -> aclient_addr (OW ++ LB) SP a.
Proof.
  intros OW LB SP a [Ha|(b & Hb & Hr)].
  - right; left. exact (ar_LIBW_cs a (LIBW_S_A a Ha)).
  - right; right. exists b. split; [apply in_or_app; left; exact Hb| exact Hr].
Qed.

Lemma data_cells_rt : forall st m m' OW LB E bo SP,
  ap_state st m OW E bo -> data_cells m OW st -> agree_on (aclient_addr (OW ++ LB) SP) m m' -> data_cells m' OW st.
Proof.
  intros st m m' OW LB E bo SP AS DC AG. pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)).
  eapply data_cells_agree; [exact DC | | exact OD]. eapply agree_on_mono; [exact AG|]. intros a Ha. exact (lib_addr_aclient OW LB SP a Ha).
Qed.

(* [comment removed for export] *)
Lemma blocks_kept_pre : forall K (st' : ApState.ap_st bptr) (OW OW' LB : list block) SP m0 m m',
  (forall b, In b K -> In b OW) -> agree_on (aclient_addr (OW ++ LB) SP) m0 m -> blocks_kept K st' OW' m m' -> blocks_kept K st' OW' m0 m'.
Proof.
  intros K st' OW OW' LB SP m0 m m' KOW AG (B1 & B2 & B3). split; [exact B1|]. split; [exact B2|].
  intros a Ha Hin. rewrite (B3 a Ha Hin). apply AG; [exact Ha|]. right; right. eapply in_block_mono; [| exact Hin].
  intros b Hb. apply in_or_app. left. exact (KOW b Hb).
Qed.

Lemma blocks_kept_post : forall K (st' : ApState.ap_st bptr) (OW' LB : list block) SP m m' m'',
  blocks_kept K st' OW' m m' -> agree_on (aclient_addr (OW' ++ LB) SP) m' m'' -> blocks_kept K st' OW' m m''.
Proof.
  intros K st' OW' LB SP m m' m'' (B1 & B2 & B3) AG. split; [exact B1|]. split; [exact B2|].
  intros a Ha Hin. rewrite <- (B3 a Ha Hin). apply AG; [exact Ha|]. right; right. eapply in_block_mono; [| exact Hin].
  intros b Hb. apply in_or_app. left. exact (B1 b Hb).
Qed.

(* [comment removed for export] *)
Lemma ax_pres_of_aclient : forall (L LB : list block) SP SP' X m m',
  agree_on (aclient_addr (L ++ LB) SP') m m' -> SP' <= SP -> ax_pres LB SP X m m'.
Proof.
  intros L LB SP SP' X m m' AG LE. unfold ax_pres. eapply agree_on_mono; [exact AG|].
  intros a [_ [Ha|[Ha|(b & Hb & Hr)]]]; [left; lia | right; left; exact Ha | right; right].
  exists b. split; [apply in_or_app; right; exact Hb | exact Hr].
Qed.

Lemma ax_pres_lower : forall (LB : list block) SP SP' X m m', ax_pres LB SP' X m m' -> SP' <= SP -> ax_pres LB SP X m m'.
Proof. intros LB SP SP' X m m' H LE. eapply ax_pres_weaken; [exact H | exact LE | intros b Hb; exact Hb | intros a Ha; exact Ha]. Qed.

(* [comment removed for export] *)
Lemma pro_closeA : forall Σ (st : ApState.ap_st bptr) m OW LB E bo (sp : word) lo STACK COST FRAMES f k Σ1 m1 spa Fb,
  ap_preA Σ st m OW LB E bo sp lo STACK COST FRAMES ->
  @BnHeapA.AHEAP (push AR f k) Σ1 OW LB m1 ->
  stk ctasegs m1 lo spa -> mem_inv ctasegs m1 ->
  agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1 ->
  rt_credit RT Σ1 = rt_credit RT Σ - 1 ->
  spa mod 32 = 0 -> bv_unsigned sp - Fb - 16 <= spa -> spa <= bv_unsigned sp - Fb -> 0 <= Fb -> Fb + 16 <= STACK ->
  1 <= COST -> 1 <= FRAMES ->
  @ap_preA (push AR f k) Σ1 st m1 OW LB E bo (Z_to_bv 64 spa) lo (STACK - Fb - 16) (COST - 1) (FRAMES - 1).
Proof.
  intros until Fb. intros (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM) HEAP1 ST1 MI1 AG CR1 SPA32 SPAL SPAH FB0 FBS C1 F1.
  pose proof (AH_ceil _ _ _ _ HEAP) as (X1 & X2 & X3). unfold SEGTOP_A, SHHI, STACK_WIN in X1, X2, X3.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (clear - ST; destruct ST as [H _]; exact H).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - LO0 LOSP SPAL SPAH SPR FB0 FBS; lia).
  unfold ap_preA. rewrite ESPA. cbn [ar_FR ar_RT ar_SP0 push amb length].
  split; [exact HEAP1|]. split; [eapply ap_state_rt; [exact AS | exact AG]|]. split; [exact IDS|].
  split; [eapply data_cells_rt; [exact AS | exact DC | exact AG]|].
  split; [exact ST1|]. split; [exact CEIL|]. split; [clear - LOSP SPAL; lia|].
  split; [clear - TOP SPAH FB0; lia|]. split; [clear - SPA32; Z.div_mod_to_equations; lia|].
  split; [exact MI1|]. split; [clear - CRED CR1 C1; lia|]. split; [clear - FRM F1; lia|]. rewrite Nat2Z.inj_succ. clear - FRM F1. lia.
Qed.

(* [comment removed for export] *)
Lemma epi_closeA : forall {A} (RES : A * ApState.ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop) (r : A * ApState.ap_st bptr)
    (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
    Σ (st : ApState.ap_st bptr) m OW LB E bo lo STACK COST FRAMES f k (spw : word) Σ1 m1 C1 Σk mk OWk (K : list block) bo' Σ' m',
  ap_preA Σ st m OW LB E bo sp lo STACK COST FRAMES ->
  agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1 -> rt_credit RT Σ1 = rt_credit RT Σ - 1 ->
  bv_unsigned spw <= bv_unsigned sp ->
  @ap_preA (push AR f k) Σk (snd r) mk OWk LB E bo' spw lo 0 0 0 ->
  ax_pres LB (bv_unsigned spw) LIBW_A m1 mk -> rt_credit RT Σ1 - C1 <= rt_credit RT Σk -> blocks_kept K (snd r) OWk m1 mk ->
  (forall b, In b K -> In b OW) -> C1 + 1 <= COST ->
  AHEAP Σ' OWk LB m' -> rt_credit RT Σ' = rt_credit RT Σk -> stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
  agree_on (aclient_addr (OWk ++ LB) (bv_unsigned spw)) mk m' ->
  RES r OWk m' a0 bo' ->
  ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K COST RES r Σ'
    (MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom ctasegs)).
Proof.
  intros until m'. intros PRE AG0 CR1 LE PREk AXk CRk BK KOW HC HEAP' CR' ST' MI' AGk HRES.
  pose proof PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
  pose proof PREk as (HEAPk & ASk & IDSk & DCk & STk & CEILk & LOSPk & TOPk & AL16k & MIk & CREDk & FRMk).
  cbn [ar_FR ar_RT ar_SP0 push amb] in CREDk.
  unfold ap_postA. do 17 eexists. exists m', OWk, bo'. split; [reflexivity|].
  split.
  { unfold ap_preA. split; [exact HEAP'|]. split; [eapply ap_state_rt; [exact ASk | exact AGk]|]. split; [exact IDSk|].
    split; [eapply data_cells_rt; [exact ASk | exact DCk | exact AGk]|]. split; [exact ST'|]. split; [exact CEIL|]. split; [clear - LOSPk LE; lia|].
    split; [exact TOP|]. split; [exact AL16|]. split; [exact MI'|]. split; [clear - CREDk CR'; lia|]. clear - FRM. lia. }
  split.
  { eapply ax_pres_trans; [eapply (ax_pres_of_aclient OW LB); [exact AG0 | clear; lia]|].
    eapply ax_pres_trans; [eapply ax_pres_lower; [exact AXk | exact LE]|].
    eapply (ax_pres_of_aclient OWk LB); [exact AGk | exact LE]. }
  split; [clear - CRED CR1 CRk HC CR'; lia|].
  split; [| exact HRES].
  eapply (blocks_kept_post K (snd r) OWk LB); [| exact AGk]. eapply (blocks_kept_pre K (snd r) OW OWk LB); [exact KOW | exact AG0 | exact BK].
Qed.

End WithRT.
