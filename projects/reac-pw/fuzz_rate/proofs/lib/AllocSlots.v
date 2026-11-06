(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YN03.v, with its module paths and module names changed; 425 of its 462 lines of code are new or changed and 499 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AllocCut.v, with its module paths and module names changed; 69 of its 140 lines of code are new or changed and 391 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/AllocCf.v, with its module paths changed; 218 of its 242 lines of code are new or changed and 116 lines of the source are left out. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import PlaceCap.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import AllocSI AllocGS AllocCount AllocBound AllocDepth AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib Require Import AllocMB AllocMallocMB AllocFreeMB AllocReallocMB AllocMallocPath AllocFreePath.
Import ListNotations.
Local Open Scope Z_scope.

Record sbound := SB { sb_live : Z; sb_bytes : Z; sb_cap : Z }.

Definition HCAP (c : Z) : Z := 13 * c + 48.

Definition NA (c : Z) : Z := HCAP c / METAS_PER_AREA + 1.

Definition P2 (c : Z) : Z := HCAP c / METAS_PER_AREA + 41.

Definition SLOTS_BOUND (c : Z) : Z := c + 48 + (NA c + 1) + 40.

Definition AREA_BOUND (c : Z) : Z := 2 * PGSZ * P2 c.

Definition LIVE_BOUND (c bytes : Z) : Z := MMAX * (c + 48) + bytes + PGSZ * (NA c + 1) + AREA_BOUND c.

Definition RQ_BOUND (c n : Z) : Z := Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (AREA_BOUND c).

Definition CAPOK (c bytes n : Z) : Prop :=
  LIVE_BOUND c bytes + 3 * PGSZ + AREA_BOUND c + Z.max MMAX (page_round (n + IB + UNIT)) <= MG_LIVE /\
  SLOTS_BOUND c + 5 + KRES <= slot_cap (RQ_BOUND c n) /\ RQ_BOUND c n + PGSZ <= MG_REQ /\
  HCAP c < METAS_PER_AREA * (2 ^ 40 - 41).

Definition res_ok_slots (A : astate) (b : sbound) : Prop :=
  II A /\ SI A /\ GS A /\ NL A /\ noraw A /\ MB A /\ nblocks A <= sb_live b /\ ubytes A <= sb_bytes b /\
  0 <= sb_live b <= sb_cap b /\ 0 <= sb_bytes b /\ hand A <= HCAP (sb_cap b).

Definition room_slots (b : sbound) (n : Z) : Prop :=
  0 <= n /\ sb_live b + 1 <= sb_cap b /\ CAPOK (sb_cap b) (sb_bytes b + n) n.

Definition sb_malloc (b : sbound) (n : Z) : sbound := SB (sb_live b + 1) (sb_bytes b + n) (sb_cap b).

Definition sb_free (b : sbound) (n : Z) : sbound := SB (sb_live b - 1) (sb_bytes b - n) (sb_cap b).

Definition sb_realloc (b : sbound) (k n : Z) : sbound := SB (sb_live b) (sb_bytes b - k + n) (sb_cap b).

Lemma nareas_hand s : II s -> nareas s <= hand s / METAS_PER_AREA + 1.
Proof.
  intros (_ & _ & _ & Hamc & _). unfold hand in *.
  assert (H : nareas s - 1 <= (METAS_PER_AREA * nareas s - amc s) / METAS_PER_AREA).
  { apply Z.div_le_lower_bound; unfold METAS_PER_AREA in *; lia. }
  lia.
Qed.

Lemma shift_small s H : II s -> hand s <= H -> H < METAS_PER_AREA * (2 ^ 40 - 41) ->
  shift s < 40 /\ 2 ^ shift s <= H / METAS_PER_AREA + 41.
Proof.
  intros HII Hh HH. pose proof HII as (_ & Hsh & _ & _ & _ & _ & _ & _ & Hm & _).
  assert (P40 : 2 ^ 40 = 1099511627776) by reflexivity. rewrite P40 in HH.
  assert (Hk : shift s < 40).
  { destruct (Z.lt_ge_cases (shift s) 40) as [L|L]; [exact L|]. exfalso.
    pose proof (Z.pow_gt_lin_r 2 (shift s - 40) ltac:(lia) ltac:(lia)) as G.
    assert (E : 2 ^ shift s = 2 ^ 40 * 2 ^ (shift s - 40)).
    { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite P40 in E. unfold METAS_PER_AREA in *. lia. }
  split; [exact Hk|].
  assert (D : 2 ^ shift s - 1 - shift s <= H / METAS_PER_AREA).
  { apply Z.div_le_lower_bound; unfold METAS_PER_AREA in *; lia. }
  lia.
Qed.

Lemma slots_room4 : forall A b n, WF A -> res_ok_slots A b -> room_slots b n -> ROOM4 A n.
Proof.
  intros A b n HW (HII & HSI & HGS & HNL & HNR & (MB1 & MB2) & Hnb & Hub & Hlv & Hby & Hh) (Hn & Hcap & C1 & C2 & C3 & C4).
  pose proof (map_count_bound A HW HSI) as T4.
  pose proof (map_bytes_bound A HW HSI HGS) as T7.
  pose proof (nareas_hand A HII) as NA1.
  destruct (shift_small A (HCAP (sb_cap b)) HII Hh C4) as [SH1 SH2].
  pose proof HII as (_ & Hsh & _ & _ & Hrt & _).
  assert (HD : hand A / METAS_PER_AREA <= HCAP (sb_cap b) / METAS_PER_AREA).
  { apply Z.div_le_mono; [unfold METAS_PER_AREA; lia | exact Hh]. }
  assert (BK : brk_bytes A / PGSZ <= nareas A + 1).
  { apply Z.div_le_upper_bound; [unfold PGSZ; lia|]. unfold PGSZ in *. lia. }
  pose proof (page_round_ge (n + IB + UNIT)) as PR.
  assert (MX0 : 0 < MMAX) by (unfold MMAX; reflexivity).
  assert (AR : area A <= AREA_BOUND (sb_cap b)) by (unfold area, AREA_BOUND, P2; unfold PGSZ in *; lia).
  assert (RQ1 : Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A) <= RQ_BOUND (sb_cap b) n).
  { unfold RQ_BOUND. lia. }
  assert (SC : slot_cap (RQ_BOUND (sb_cap b) n) <= slot_cap (Z.max (Z.max MMAX (page_round (n + IB + UNIT))) (area A))).
  { apply slot_cap_anti. lia. }
  unfold ROOM4. split; [|split; [|split]].
  - unfold LIVE_UB. rewrite Hrt. unfold LIVE_BOUND, AREA_BOUND, NA, P2 in *. unfold PGSZ, MMAX in *. lia.
  - unfold SLOT_UB. unfold SLOTS_BOUND, NA in C2. lia.
  - unfold RQ_BOUND in C3. unfold PGSZ in *. lia.
  - unfold RQ_BOUND in C3. unfold PGSZ in *. lia.
Qed.

Lemma ubytes_zsum s : ubytes s = zsum snd (user_blocks s).
Proof. reflexivity. Qed.

Lemma blocks_del_counts s s' p n l1 l2 : WF s ->
  user_blocks s = l1 ++ (p, n) :: l2 -> user_blocks s' = l1 ++ l2 ->
  nblocks s' = nblocks s - 1 /\ ubytes s' = ubytes s - n /\ 0 <= n <= ubytes s /\ 1 <= nblocks s.
Proof.
  intros HW E1 E2. unfold nblocks. rewrite !ubytes_zsum, E1, E2, !zsum_app, !length_app, zsum_cons.
  cbn [length snd]. assert (Hn : 0 <= n) by (apply (ub_nonneg s HW (p, n)); rewrite E1; apply in_app_iff; right; left; reflexivity).
  assert (H1 : 0 <= zsum snd l1) by (apply zsum_nonneg; intros x Hx; apply (ub_nonneg s HW); rewrite E1; apply in_app_iff; left; exact Hx).
  assert (H2 : 0 <= zsum snd l2) by (apply zsum_nonneg; intros x Hx; apply (ub_nonneg s HW); rewrite E1; apply in_app_iff; right; right; exact Hx).
  lia.
Qed.

Lemma blocks_add_counts s s' q n l1 l2 :
  user_blocks s' = l1 ++ (q, n) :: l2 -> user_blocks s = l1 ++ l2 ->
  nblocks s' = nblocks s + 1 /\ ubytes s' = ubytes s + n.
Proof.
  intros E1 E2. unfold nblocks. rewrite !ubytes_zsum, E1, E2, !zsum_app, !length_app, zsum_cons.
  cbn [length snd]. lia.
Qed.

Lemma room_slots_n b n : room_slots b n -> 0 <= n < 2 ^ 62 /\ size_overflows n = false.
Proof.
  intros (Hn0 & _ & _ & _ & C3 & _). pose proof (page_round_ge (n + IB + UNIT)) as PG. unfold PGSZ in C3.
  assert (R : page_round (n + IB + UNIT) <= RQ_BOUND (sb_cap b) n) by (unfold RQ_BOUND; lia).
  split; [unfold MG_REQ, IB, UNIT in *; lia|]. unfold size_overflows. apply Z.leb_gt. unfold MG_REQ, IB, UNIT in *. lia.
Qed.

Lemma room_slots_req b n : room_slots b n -> page_round (n + IB + UNIT) + PGSZ <= MG_REQ.
Proof.
  intros (_ & _ & _ & _ & C3 & _).
  assert (R : page_round (n + IB + UNIT) <= RQ_BOUND (sb_cap b) n) by (unfold RQ_BOUND; lia). lia.
Qed.

Lemma res_ok_slots_init c : 0 <= c -> res_ok_slots init_state (SB 0 0 c).
Proof.
  intros Hc. unfold res_ok_slots. cbn [sb_live sb_bytes sb_cap].
  refine (conj II_init (conj SI_init (conj GS_init (conj NL_init (conj noraw_init (conj MB_init _)))))).
  unfold nblocks, ubytes, hand, nareas, HCAP. cbn. lia.
Qed.

Lemma malloc_slots_ok04 A b n : WF A -> res_ok_slots A b -> room_slots b n -> ok04 mgrant (malloc n A).
Proof.
  intros HW HR HRm. pose proof (slots_room4 A b n HW HR HRm) as R4. pose proof (room_slots_n b n HRm) as [Hn _].
  exact (proj1 (OK4_malloc n A (malloc_reqs_ok A n HW (proj1 Hn)) (proj1 HR) (proj1 Hn) R4)).
Qed.

Lemma malloc_slots_step A b n tr r A' : WF A -> res_ok_slots A b -> room_slots b n ->
  cpath04 (malloc n A) tr (r, A') -> (exists q, r = Some q) /\ res_ok_slots A' (sb_malloc b n).
Proof.
  intros HW HR HRm Hp.
  pose proof (slots_room4 A b n HW HR HRm) as R4. pose proof (room_slots_n b n HRm) as [[Hn0 _] Hov].
  pose proof HRm as (_ & Hcap & _).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & Hnb & Hub & Hlv & Hby & Hh).
  pose proof (OK4_malloc n A (malloc_reqs_ok A n HW Hn0) HII Hn0 R4) as [_ HLV].
  destruct (malloc_cpath04_some n A tr (r, A') Hov Hp) as [q Hq]. cbn [fst] in Hq. subst r.
  split; [exists q; reflexivity|].
  pose proof (cpath04_yields _ _ _ Hp) as Hy.
  pose proof (leaves_cpath04 _ _ _ _ HLV Hp) as HP. unfold MPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  pose proof (malloc_wf A n tr (Some q) A' HW Hn0 Hy) as HW'.
  destruct (malloc_blocks A n tr (Some q) A' HW Hn0 Hy) as (l1 & l2 & E1 & E2 & _).
  destruct (blocks_add_counts A A' q n l1 l2 E1 E2) as (C1 & C2).
  pose proof (malloc_SI A n tr (Some q) A' HW HSI Hn0 Hy) as HSI'.
  pose proof (malloc_NL A n tr (Some q) A' HW HNL Hn0 Hy) as HNL'.
  pose proof (malloc_hand A n tr (Some q) A' HW HSI HNR Hn0 Hp) as Hh'.
  pose proof (nused_bound_depth A' HW' HSI' HNL') as NU.
  unfold res_ok_slots, sb_malloc. cbn [sb_live sb_bytes sb_cap].
  refine (conj II' (conj HSI' (conj (malloc_GS A n tr (Some q) A' HW HGS Hn0 Hy)
    (conj HNL' (conj (malloc_noraw A n tr (Some q) A' HNR Hy) (conj (malloc_MB A n tr (Some q) A' HW HMB Hn0 Hy) _)))))).
  unfold HCAP in *. repeat split; lia.
Qed.

Lemma free_slots_step A b p n tr u A' : WF A -> In (p, n) (user_blocks A) -> res_ok_slots A b ->
  cpath04 (free (Some p) A) tr (u, A') -> res_ok_slots A' (sb_free b n).
Proof.
  intros HW Hin HR Hcp. destruct u.
  pose proof (free_reqs_ok A p n HW Hin) as RQ.
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & Hnb & Hub & Hlv & Hby & Hh).
  pose proof (OK4_free (Some p) A RQ HII) as [_ HLV].
  pose proof (cpath04_yields _ _ _ Hcp) as Hy.
  pose proof (leaves_cpath04 _ _ _ _ HLV Hcp) as HP. unfold FPost in HP. cbn [snd] in HP. destruct HP as (II' & _).
  destruct (free_blocks A p n tr A' HW Hin Hy) as (l1 & l2 & E1 & E2).
  destruct (blocks_del_counts A A' p n l1 l2 HW E1 E2) as (C1 & C2 & C3 & C4).
  unfold res_ok_slots, sb_free. cbn [sb_live sb_bytes sb_cap].
  pose proof (free_hand A p n tr A' HW Hin Hy) as Hh'.
  refine (conj II' (conj (free_SI A p n tr A' HW HSI Hin Hy) (conj (free_GS A p n tr A' HW HGS Hin Hy)
    (conj (free_NL A p n tr A' HW HNL Hin Hy) (conj (free_noraw A p n tr A' HW Hin HNR Hy) (conj (free_MB A p n tr A' HW HMB Hin Hy) _)))))).
  repeat split; lia.
Qed.

Lemma malloc_slots_cpath A b n tr q A' : WF A -> res_ok_slots A b -> room_slots b n ->
  cpath (malloc n A) tr (Some q, A') -> res_ok_slots A' (sb_malloc b n).
Proof.
  intros HW HR HRm Hp. pose proof (room_slots_n b n HRm) as [[Hn0 _] _].
  exact (proj2 (malloc_slots_step A b n tr (Some q) A' HW HR HRm (malloc_some_cpath04 A n tr q A' HW Hn0 Hp))).
Qed.

Lemma free_slots_cpath A b p n tr u A' : WF A -> In (p, n) (user_blocks A) -> res_ok_slots A b ->
  cpath (free (Some p) A) tr (u, A') -> res_ok_slots A' (sb_free b n).
Proof.
  intros HW Hin HR Hp.
  exact (free_slots_step A b p n tr u A' HW Hin HR (free_cpath04 A p n tr (u, A') HW Hin Hp)).
Qed.

Lemma sb_free_malloc b n : sb_free (sb_malloc b n) n = b.
Proof. destruct b as [l y c]. unfold sb_free, sb_malloc. cbn. f_equal; lia. Qed.

Lemma ub_le_ubytes s p k : WF s -> In (p, k) (user_blocks s) -> k <= ubytes s.
Proof.
  intros HW Hin. destruct (in_split _ _ Hin) as (l1 & l2 & E).
  rewrite ubytes_zsum, E, zsum_app, zsum_cons. cbn [snd].
  assert (0 <= zsum snd l1) by (apply zsum_nonneg; intros x Hx; apply (ub_nonneg s HW); rewrite E; apply in_app_iff; left; exact Hx).
  assert (0 <= zsum snd l2) by (apply zsum_nonneg; intros x Hx; apply (ub_nonneg s HW); rewrite E; apply in_app_iff; right; right; exact Hx).
  lia.
Qed.

Lemma realloc_slots_step A b p k n tr r A' : WF A -> In (p, k) (user_blocks A) -> res_ok_slots A b -> room_slots b n ->
  cpath04 (realloc (Some p) n A) tr (r, A') -> II A' ->
  WF A' /\ match r with Some _ => res_ok_slots A' (sb_realloc b k n) | None => res_ok_slots A' b end.
Proof.
  intros HW Hin HR HRm Hp II'.
  pose proof (room_slots_n b n HRm) as [[Hn0 _] _]. pose proof HRm as (_ & Hcap & _).
  destruct HR as (HII & HSI & HGS & HNL & HNR & HMB & Hnb & Hub & Hlv & Hby & Hh).
  pose proof (cpath04_yields _ _ _ Hp) as Hy.
  pose proof (realloc_wf A p k n tr r A' HW Hin Hn0 Hy) as HW'.
  destruct (realloc_inv A p k n tr r A' HW Hin Hn0 Hy HSI HGS HNL HNR) as (HSI' & HGS' & HNL' & HNR').
  pose proof (realloc_hand_bound A p k n tr r A' HW Hin Hn0 HSI HNL HNR Hp) as Hh'.
  pose proof (realloc_counts A p k n tr r A' HW Hin Hn0 Hy) as HC.
  pose proof (realloc_MB A p k n tr r A' HW Hin Hn0 Hy HMB) as HMB'.
  split; [exact HW'|].
  assert (HK : 0 <= k) by (apply (ub_nonneg A HW (p, k)); exact Hin). pose proof (ub_le_ubytes A p k HW Hin) as HKU.
  assert (HH : hand A' <= HCAP (sb_cap b)) by (unfold HCAP in *; lia).
  destruct r as [q|].
  - destruct HC as (C1 & C2). unfold res_ok_slots, sb_realloc. cbn [sb_live sb_bytes sb_cap].
    refine (conj II' (conj HSI' (conj HGS' (conj HNL' (conj HNR' (conj HMB' _)))))). repeat split; lia.
  - unfold res_ok_slots. unfold nblocks, ubytes. rewrite HC.
    refine (conj II' (conj HSI' (conj HGS' (conj HNL' (conj HNR' (conj HMB' _)))))). unfold nblocks, ubytes in *. repeat split; lia.
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable MR : MR_t.
Let segs := ms_segs B.

Theorem malloc_SR_slots :
  malloc_realizes B MR ->
  forall L A regs mem md n b,
  call_pre B MR L A regs mem md -> getr regs 10 = Z_to_bv 64 n -> res_ok_slots A b -> room_slots b n ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_malloc B)) mem (seg_rom segs)) md)
    (fun c' => exists p A' tr, cpath04 (malloc n A) tr (Some p, A') /\
       malloc_leaf B MR L A regs mem md n (Some p, A') c' /\ res_ok_slots A' (sb_malloc b n)).
Proof.
  intros HM L A regs mem md n b Hpre Hn HR HRm.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  pose proof (room_slots_n b n HRm) as [Hn62 _].
  eapply SR_mono; [apply (malloc_SR_ok B MR HM L A regs mem md n Hpre Hn Hn62 (malloc_slots_ok04 A b n HW HR HRm))|].
  intros c' ([r A'] & tr & Hp & HL).
  destruct (malloc_slots_step A b n tr r A' HW HR HRm Hp) as [[q ->] HR'].
  exists q, A', tr. auto.
Qed.

Theorem free_SR_slots :
  free_realizes B MR ->
  forall L A regs mem md p n b,
  call_pre B MR L A regs mem md -> In (p, n) (user_blocks A) -> getr regs 10 = Z_to_bv 64 (ptr_addr L p) ->
  res_ok_slots A b ->
  SR segs (mkCfg (mkst regs (Z_to_bv 64 (ms_free B)) mem (seg_rom segs)) md)
    (fun c' => exists A' tr, cpath04 (free (Some p) A) tr (tt, A') /\
       free_leaf B MR L A regs mem md p n (tt, A') c' /\ res_ok_slots A' (sb_free b n)).
Proof.
  intros HF L A regs mem md p n b Hpre Hin Hp HR.
  assert (HW : WF A) by (destruct Hpre as (_ & HW & _); exact HW).
  pose proof (free_reqs_ok A p n HW Hin) as RQ.
  pose proof (OK4_free (Some p) A RQ (proj1 HR)) as [HOK _].
  eapply SR_mono; [apply (free_SR_ok B MR HF L A regs mem md p n Hpre Hin Hp HOK)|].
  intros c' ([[] A'] & tr & Hcp & HL). exists A', tr. split; [exact Hcp|]. split; [exact HL|].
  exact (free_slots_step A b p n tr tt A' HW Hin HR Hcp).
Qed.
End c.
