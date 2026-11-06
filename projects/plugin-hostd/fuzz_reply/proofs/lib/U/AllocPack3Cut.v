From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO16 YL01 YK1j YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocSlots.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocMallocPath AllocFreePath AllocBound.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPack AllocPackRoom AllocReallocOK.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract AllocCut AllocForm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPack3 AllocPack3Room ContractT AllocFormT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import AllocPack3Malloc AllocPack3Free AllocPack3FreeR.
Import ListNotations.
Local Open Scope Z_scope.

Lemma bcount_pos A p n : In (p, n) (user_blocks A) -> 1 <= bcount A (band n).
Proof.
  intros Hin. unfold bcount.
  assert (H : In (p, n) (List.filter (fun b => band (snd b) =? band n) (user_blocks A)))
    by (apply (proj2 (List.filter_In _ _ _)); split; [exact Hin | cbn [snd]; apply Z.eqb_refl]).
  destruct (List.filter _ _); [contradiction | cbn [length]; lia].
Qed.

Lemma leaves_yields {X} : forall (P : X -> Prop) (t : itree astate X) tr a, leaves P t -> yields t tr a -> P a.
Proof.
  induction t as [a' | q s k IH | e]; intros [|[q' z] tr] a Hl H; cbn in *; try contradiction.
  - subst. exact Hl.
  - destruct H as (-> & Hz & H). exact (IH z tr a (Hl z Hz) H).
Qed.

Lemma GALL3_caps64 : 845 <= GALL3 (repeat 64 49) (repeat 8 49).
Proof. apply Z.leb_le. vm_compute. reflexivity. Qed.

Lemma realloc_pack3_ok04 A b p k n : WF A -> In (p, k) (user_blocks A) -> res_ok_pack3 A b -> room_pack3 b n ->
  ok04 mgrant (realloc (Some p) n A).
Proof.
  intros HW Hin HR HRm.
  exact (realloc_ok04 A p k n HW Hin (proj1 HR) (proj1 (room_pack3_n b n HRm)) (pack3_room4 A b n HW HR HRm)
    (room_pack3_req b n HRm)).
Qed.


Lemma malloc_pack3_step A b n tr r A' : WF A -> res_ok_pack3 A b -> room_pack3 b n ->
  cpath04 (malloc n A) tr (r, A') -> (exists q, r = Some q) /\ res_ok_pack3 A' (pb3_malloc b n).
Proof using.
  intros HW HR HRm Hp.
  pose proof (pack3_room4 A b n HW HR HRm) as R4. pose proof (room_pack3_n b n HRm) as [[Hn0 _] Hov].
  pose proof HRm as (_ & Hcap & _).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) HII Hn0 R4) as [_ HLV].
  destruct (malloc_cpath04_some n A tr (r, A') Hov Hp) as [q Hq]. cbn [fst] in Hq. subst r.
  split; [exists q; reflexivity|].
  pose proof (cpath04_yields _ _ _ Hp) as Hy.
  pose proof (leaves_cpath04 _ _ _ _ HLV Hp) as HP. unfold MPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  pose proof (malloc_wf A n tr (Some q) A' HW Hn0 Hy) as HW'.
  destruct (malloc_blocks A n tr (Some q) A' HW Hn0 Hy) as (l1 & l2 & E1 & E2 & _).
  destruct (blocks_add_counts A A' q n l1 l2 E1 E2) as (C1 & C2).
  pose proof (malloc_SI A n tr (Some q) A' HW HSI Hn0 Hy) as HSI'.
  destruct (malloc_pack3 A n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr (Some q) A' HW HSI HGS HNL HNR HPS HPC
    HUP HMS HlC HlL HlM Hlv Hn0 Hy) as (HPS' & HPC' & HUP' & HMS').
  pose proof (malloc_hand A n tr (Some q) A' HW HSI HNR Hn0 Hp) as Hh'.
  pose proof (AllocPackRoom.band_range n Hn0) as Hb.
  pose proof (Hlv (band n) Hb) as Hlvb.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band n) 1 HlL Hb Hlv0 ltac:(lia)) as [HlL' Hlv'].
  pose proof (nused_pack3 A' (p3_cap b) (p3_mcap b) (lv_add (p3_live b) (band n) 1) (p3_mis b) HW' HSI' HPS' HPC' HUP'
    HlC HlL' Hlv') as NU.
  unfold res_ok_pack3, pb3_malloc. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II' (conj HSI' (conj (malloc_GS A n tr (Some q) A' HW HGS Hn0 Hy)
    (conj (malloc_NL A n tr (Some q) A' HW HNL Hn0 Hy) (conj (malloc_noraw A n tr (Some q) A' HNR Hy)
    (conj (malloc_MB A n tr (Some q) A' HW HMB Hn0 Hy) (conj HPS' (conj HPC' (conj HUP' (conj HMS' _)))))))))).
  split; [lia|]. split; [exact HlL'|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros j Hj; split; [exact (Hlv' j Hj) | exact (proj2 (Hlv j Hj))]|]. split; lia.
Qed.

Lemma free_pack3_step A b p n tr u A' : WF A -> In (p, n) (user_blocks A) -> res_ok_pack3 A b ->
  cpath04 (free (Some p) A) tr (u, A') -> res_ok_pack3 A' (pb3_free b n p).
Proof using.
  intros HW Hin HR Hcp. destruct u.
  pose proof (free_reqs_ok A p n HW Hin) as RQ.
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  pose proof (OK4_free (Some p) A RQ HII) as [_ HLV].
  pose proof (cpath04_yields _ _ _ Hcp) as Hy.
  pose proof (leaves_cpath04 _ _ _ _ HLV Hcp) as HP. unfold FPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  destruct (free_blocks A p n tr A' HW Hin Hy) as (l1 & l2 & E1 & E2).
  destruct (blocks_del_counts A A' p n l1 l2 HW E1 E2) as (C1 & C2 & C3 & C4).
  destruct (free_pack3 A p n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr tt A' HW HSI HPS HPC HUP HMS Hin Hy)
    as (HPS' & HPC' & HUP' & HMS').
  pose proof (free_hand A p n tr A' HW Hin Hy) as Hh'.
  assert (Hn0 : 0 <= n) by lia.
  pose proof (AllocPackRoom.band_range n Hn0) as Hb.
  pose proof (bcount_pos A p n Hin) as Hbc. pose proof (proj1 HUP (band n) Hb) as Hbl.
  pose proof (Hlv (band n) Hb) as Hlvb.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band n) (-1) HlL Hb Hlv0 ltac:(lia)) as [HlL' Hlv'].
  unfold res_ok_pack3, pb3_free. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II' (conj (free_SI A p n tr A' HW HSI Hin Hy) (conj (free_GS A p n tr A' HW HGS Hin Hy)
    (conj (free_NL A p n tr A' HW HNL Hin Hy) (conj (free_noraw A p n tr A' HW Hin HNR Hy)
    (conj (free_MB A p n tr A' HW HMB Hin Hy) (conj HPS' (conj HPC' (conj HUP' (conj HMS' _)))))))))).
  split; [lia|]. split; [exact HlL'|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros j Hj; split; [exact (Hlv' j Hj) | exact (proj2 (Hlv j Hj))]|]. split; lia.
Qed.

Lemma realloc_pack3_hand A b p k n tr r A' : WF A -> In (p, k) (user_blocks A) -> res_ok_pack3 A b -> room_pack3 b n ->
  cpath04 (realloc (Some p) n A) tr (r, A') -> hand A' <= Z.max (hand A) (GALL3 (p3_cap b) (p3_mcap b)).
Proof using.
  intros HW Hin HR HRm Hp.
  pose proof (room_pack3_n b n HRm) as [[Hn0 _] _]. pose proof HRm as (_ & Hcap & _).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  destruct (ra_cases canswer04 A p k n tr r A' HW Hin (rpath_cpath04 _ _ _ Hp)) as [[_ ->]|(g & am & i & fr & _ & _ & _ & _ & _ & _ & C)];
    [lia|].
  destruct C as [(_ & _ & ->)|[(_ & _ & _ & _ & ->)|[(_ & _ & _ & _ & ->)|(tr' & Hm)]]];
    try (match goal with |- hand ?X <= _ => assert (E : hand X = hand A) by reflexivity; rewrite E; lia end).
  destruct (ra_move canswer04 p n A tr' r A' Hm) as (tr1 & q & s1 & H1 & Hq).
  pose proof (cpath04_rpath _ _ _ H1) as H1'. pose proof (cpath04_yields _ _ _ H1') as Y1.
  pose proof (malloc_hand A n tr1 q s1 HW HSI HNR Hn0 H1') as Hh1.
  pose proof (malloc_wf A n tr1 q s1 HW Hn0 Y1) as HW1.
  pose proof (malloc_SI A n tr1 q s1 HW HSI Hn0 Y1) as HSI1.
  destruct (malloc_pack3 A n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr1 q s1 HW HSI HGS HNL HNR HPS HPC HUP HMS
    HlC HlL HlM Hlv Hn0 Y1) as (HPS1 & HPC1 & HUP1 & _).
  pose proof (AllocPackRoom.band_range n Hn0) as Hb. pose proof (Hlv (band n) Hb) as Hlvb.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band n) 1 HlL Hb Hlv0 ltac:(lia)) as [HlL' Hlv'].
  assert (NU : nused s1 <= GALL3 (p3_cap b) (p3_mcap b)).
  { destruct q as [q|].
    - exact (nused_pack3 s1 (p3_cap b) (p3_mcap b) _ _ HW1 HSI1 HPS1 HPC1 HUP1 HlC HlL' Hlv').
    - exact (nused_pack3 s1 (p3_cap b) (p3_mcap b) _ _ HW1 HSI1 HPS1 HPC1 HUP1 HlC HlL Hlv0). }
  destruct q as [q|]; [|destruct Hq as [_ ->]; lia].
  destruct Hq as [_ (tr2 & H2)].
  destruct (malloc_blocks A n tr1 (Some q) s1 HW Hn0 Y1) as (l1 & l2 & E1 & E2 & _).
  pose proof (in_after_malloc A s1 l1 l2 q n (p, k) E1 E2 Hin) as Hin1.
  pose proof (free_hand s1 p k tr2 A' HW1 Hin1 (cpath04_yields _ _ _ (cpath04_rpath _ _ _ H2))) as Hh2.
  lia.
Qed.

Lemma realloc_pack3_step A b p k n tr r A' : WF A -> In (p, k) (user_blocks A) -> res_ok_pack3 A b -> room_pack3 b n ->
  cpath04 (realloc (Some p) n A) tr (r, A') -> exists q, r = Some q /\ res_ok_pack3 A' (pb3_realloc b k n p q).
Proof using.
  intros HW Hin HR HRm Hp.
  pose proof (room_pack3_n b n HRm) as [Hn Ov]. pose proof HRm as (_ & Hcap & Hmc & _).
  destruct (realloc_cpath04_some A p k n tr r A' HW Hin Ov Hp) as [q ->].
  exists q. split; [reflexivity|].
  pose proof (realloc_II A p k n tr (Some q) A' HW Hin (proj1 HR) Hn (pack3_room4 A b n HW HR HRm) (room_pack3_req b n HRm) Hp)
    as II'.
  pose proof (realloc_pack3_hand A b p k n tr (Some q) A' HW Hin HR HRm Hp) as Hh'.
  pose proof (cpath04_yields _ _ _ Hp) as Hy.
  pose proof (ub_le_ubytes A p k HW Hin) as HKU.
  assert (HK : 0 <= k) by (apply (ub_nonneg A HW (p, k)); exact Hin).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  pose proof (realloc_wf A p k n tr (Some q) A' HW Hin (proj1 Hn) Hy) as HW'.
  destruct (realloc_inv A p k n tr (Some q) A' HW Hin (proj1 Hn) Hy HSI HGS HNL HNR) as (HSI' & HGS' & HNL' & HNR').
  destruct (realloc_counts A p k n tr (Some q) A' HW Hin (proj1 Hn) Hy) as (C1 & C2).
  pose proof (realloc_MB A p k n tr (Some q) A' HW Hin (proj1 Hn) Hy HMB) as HMB'.
  destruct ((realloc_pack3 malloc_pack3) A p k n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr q A' HW HSI HGS HNL HNR HPS HPC HUP
    HMS HlC HlL HlM Hlv Hin (proj1 Hn) Hmc Hy) as (HPS' & HPC' & HUP' & HMS').
  pose proof (AllocPackRoom.band_range n (proj1 Hn)) as Hbn. pose proof (AllocPackRoom.band_range k HK) as Hbk.
  pose proof (Hlv (band n) Hbn) as Hlvn. pose proof (Hlv (band k) Hbk) as Hlvk.
  pose proof (bcount_pos A p k Hin) as Hbc. pose proof (proj1 HUP (band k) Hbk) as Hbl.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band k) (-1) HlL Hbk Hlv0 ltac:(lia)) as [L1 V1].
  assert (Hn1 : 0 <= znth (band n) (lv_add (p3_live b) (band k) (-1)) + 1 <= znth (band n) (p3_cap b)).
  { rewrite znth_lv_add by (try rewrite HlL; lia).
    destruct (band n =? band k) eqn:E; [apply Z.eqb_eq in E; rewrite E|]; lia. }
  destruct (lv_add_bounds _ (p3_cap b) (band n) 1 L1 Hbn V1 Hn1) as [HlL' Hlv'].
  unfold res_ok_pack3, pb3_realloc. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II' (conj HSI' (conj HGS' (conj HNL' (conj HNR' (conj HMB' (conj HPS' (conj HPC' (conj HUP' (conj HMS' _)))))))))).
  split; [lia|]. split; [exact HlL'|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros j Hj; split; [exact (Hlv' j Hj) | exact (proj2 (Hlv j Hj))]|]. split; lia.
Qed.

Lemma malloc_pack3_cpath A b n tr q A' : WF A -> res_ok_pack3 A b -> room_pack3 b n ->
  cpath (malloc n A) tr (Some q, A') -> res_ok_pack3 A' (pb3_malloc b n).
Proof using.
  intros HW HR HRm Hp. pose proof (room_pack3_n b n HRm) as [[Hn0 _] _].
  exact (proj2 (malloc_pack3_step A b n tr (Some q) A' HW HR HRm (malloc_some_cpath04 A n tr q A' HW Hn0 Hp))).
Qed.

Lemma free_pack3_cpath A b p n tr u A' : WF A -> In (p, n) (user_blocks A) -> res_ok_pack3 A b ->
  cpath (free (Some p) A) tr (u, A') -> res_ok_pack3 A' (pb3_free b n p).
Proof using.
  intros HW Hin HR Hp. exact (free_pack3_step A b p n tr u A' HW Hin HR (free_cpath04 A p n tr (u, A') HW Hin Hp)).
Qed.

Lemma malloc_pack3_yields A b n tr q A' : WF A -> res_ok_pack3 A b -> room_pack3 b n ->
  yields (malloc n A) tr (Some q, A') -> hand A' <= GALL3 (p3_cap b) (p3_mcap b) -> res_ok_pack3 A' (pb3_malloc b n).
Proof using.
  intros HW HR HRm Hy Hh'.
  pose proof (pack3_room4 A b n HW HR HRm) as R4. pose proof (room_pack3_n b n HRm) as [[Hn0 _] Hov].
  pose proof HRm as (_ & Hcap & _).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) HII Hn0 R4) as [_ HLV].
  pose proof (leaves_yields _ _ _ _ HLV Hy) as HP. unfold MPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  pose proof (malloc_wf A n tr (Some q) A' HW Hn0 Hy) as HW'.
  destruct (malloc_blocks A n tr (Some q) A' HW Hn0 Hy) as (l1 & l2 & E1 & E2 & _).
  destruct (blocks_add_counts A A' q n l1 l2 E1 E2) as (C1 & C2).
  pose proof (malloc_SI A n tr (Some q) A' HW HSI Hn0 Hy) as HSI'.
  destruct (malloc_pack3 A n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr (Some q) A' HW HSI HGS HNL HNR HPS HPC
    HUP HMS HlC HlL HlM Hlv Hn0 Hy) as (HPS' & HPC' & HUP' & HMS').
  pose proof (AllocPackRoom.band_range n Hn0) as Hb.
  pose proof (Hlv (band n) Hb) as Hlvb.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band n) 1 HlL Hb Hlv0 ltac:(lia)) as [HlL' Hlv'].
  unfold res_ok_pack3, pb3_malloc. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II' (conj HSI' (conj (malloc_GS A n tr (Some q) A' HW HGS Hn0 Hy)
    (conj (malloc_NL A n tr (Some q) A' HW HNL Hn0 Hy) (conj (malloc_noraw A n tr (Some q) A' HNR Hy)
    (conj (malloc_MB A n tr (Some q) A' HW HMB Hn0 Hy) (conj HPS' (conj HPC' (conj HUP' (conj HMS' _)))))))))).
  split; [lia|]. split; [exact HlL'|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros j Hj; split; [exact (Hlv' j Hj) | exact (proj2 (Hlv j Hj))]|]. split; lia.
Qed.

Lemma free_pack3_yields A b p n tr A' : WF A -> In (p, n) (user_blocks A) -> res_ok_pack3 A b ->
  yields (free (Some p) A) tr (tt, A') -> res_ok_pack3 A' (pb3_free b n p).
Proof using.
  intros HW Hin HR Hy.
  pose proof (free_reqs_ok A p n HW Hin) as RQ.
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & HPS & HPC & HUP & HMS & Hub & HlL & HlC & HlM & Hlv & Hby & Hh).
  pose proof (OK4_free (Some p) A RQ HII) as [_ HLV].
  pose proof (leaves_yields _ _ _ _ HLV Hy) as HP. unfold FPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  destruct (free_blocks A p n tr A' HW Hin Hy) as (l1 & l2 & E1 & E2).
  destruct (blocks_del_counts A A' p n l1 l2 HW E1 E2) as (C1 & C2 & C3 & C4).
  destruct (free_pack3 A p n (p3_cap b) (p3_mcap b) (p3_live b) (p3_mis b) tr tt A' HW HSI HPS HPC HUP HMS Hin Hy)
    as (HPS' & HPC' & HUP' & HMS').
  pose proof (free_hand A p n tr A' HW Hin Hy) as Hh'.
  assert (Hn0 : 0 <= n) by lia.
  pose proof (AllocPackRoom.band_range n Hn0) as Hb.
  pose proof (bcount_pos A p n Hin) as Hbc. pose proof (proj1 HUP (band n) Hb) as Hbl.
  pose proof (Hlv (band n) Hb) as Hlvb.
  assert (Hlv0 : forall j, 0 <= j < 49 -> 0 <= znth j (p3_live b) <= znth j (p3_cap b))
    by (intros j Hj; exact (proj1 (Hlv j Hj))).
  destruct (lv_add_bounds (p3_live b) (p3_cap b) (band n) (-1) HlL Hb Hlv0 ltac:(lia)) as [HlL' Hlv'].
  unfold res_ok_pack3, pb3_free. cbn [p3_live p3_bytes p3_cap p3_mis p3_mcap].
  refine (conj II' (conj (free_SI A p n tr A' HW HSI Hin Hy) (conj (free_GS A p n tr A' HW HGS Hin Hy)
    (conj (free_NL A p n tr A' HW HNL Hin Hy) (conj (free_noraw A p n tr A' HW Hin HNR Hy)
    (conj (free_MB A p n tr A' HW HMB Hin Hy) (conj HPS' (conj HPC' (conj HUP' (conj HMS' _)))))))))).
  split; [lia|]. split; [exact HlL'|]. split; [exact HlC|]. split; [exact HlM|].
  split; [intros j Hj; split; [exact (Hlv' j Hj) | exact (proj2 (Hlv j Hj))]|]. split; lia.
Qed.

Lemma pack3_laws : FormLawsT pack3_form.
Proof using.
  split.
  - intros A b H. exact (proj1 H).
  - exact room_pack3_n.
  - intros A b n HW HR HRm. pose proof (room_pack3_n b n HRm) as [[Hn0 _] _].
    exact (proj1 (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) (proj1 HR) Hn0 (pack3_room4 A b n HW HR HRm))).
  - exact malloc_pack3_step.
  - exact free_pack3_step.
  - exact realloc_pack3_ok04.
  - exact realloc_pack3_step.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Let MR := aa_MR API.

Theorem pack3_malloc_contract : AllocExtra B MR -> ro_apart_b B = true -> malloc_contract_rt B API pack3_form.
Proof using. exact (malloc_contract_formT B API pack3_form pack3_laws). Qed.

Theorem pack3_free_contract : AllocExtra B MR -> ro_apart_b B = true -> free_contract_rt B API pack3_form.
Proof using. exact (free_contract_formT B API pack3_form pack3_laws). Qed.

Theorem pack3_calloc_contract : AllocExtra B MR -> ro_apart_b B = true ->
  forall pc, calloc_contract_rt B API pack3_form pc.
Proof using. exact (calloc_contract_formT B API pack3_form pack3_laws). Qed.

Theorem pack3_realloc_null_contract : AllocExtra B MR -> ro_apart_b B = true -> realloc_null_realizes B MR ->
  forall pc, ms_realloc B = Some pc -> realloc_null_contract_rt B API pack3_form pc.
Proof using.
  exact (realloc_null_contract_formT B API pack3_form pack3_laws).
Qed.

Theorem pack3_realloc_contract : AllocExtra B MR -> ro_apart_b B = true -> realloc_realizes B MR -> realloc_safe_p ->
  forall pc, ms_realloc B = Some pc -> realloc_contract_rt B API pack3_form pc.
Proof using.
  exact (realloc_contract_formT B API pack3_form pack3_laws).
Qed.
End c.

