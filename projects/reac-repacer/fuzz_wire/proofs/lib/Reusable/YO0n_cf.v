(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YO0n.v, with its module paths changed. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YK15 YM02.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import
YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03
YO0p YO0j YO0m YO0l YO0n YO0d_cf YO03_cf YO0j_cf YO0m_cf YO0l_cf.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Notation amc s := (st_avail_meta_count s).
Theorem OKC_malloc X n s : reqs_ok (malloc n s) -> II s -> 0 <= n -> page_round (n + IB + UNIT) <= MG_REQ ->
LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= X -> OKC X (fun _ => True) (malloc n s).
Proof using.
intros RQ HII Hn R4 RX. pose proof HII as (NN & Hsh & _).
pose proof (area_nonneg s HII) as HA.
assert (PR0 : 0 < page_round (n + IB + UNIT)) by (pose proof (page_round_ge (n + IB + UNIT)); unfold IB, UNIT in *; lia).
unfold malloc in RQ |- *.
destruct (size_overflows n) eqn:Eo; [apply OKC_ret; exact I|].
destruct (MMAP_THRESHOLD <=? n) eqn:Em.
-
pose proof (page_round_bounds (n + IB + UNIT) ltac:(unfold IB, UNIT; lia)) as PB.
rq_bind RQ RQ1 RQ2.
eapply OKC_bind_y.
{ apply (OKC_ask_room X (KMmapRW (n + IB + UNIT)) s (fun x => snd x = s)); [ | intros b; reflexivity].
intros _. cbn [req_len]. pose proof (LIVE_UB_ok s NN). unfold PGSZ in *. lia. }
intros ok s1 tr1 Hy1 E1. cbn [snd] in E1. subst s1. specialize (RQ2 tr1 ok s Hy1). clear RQ1 Hy1.
destruct ok; cbn [negb] in RQ2 |- *; [|apply OKC_ret; exact I].
apply OKC_bind_new_region. rq_new_region RQ2.
match goal with |- OKC _ _ (bind _ _ ?sx) => set (s1 := sx) in * end.
destruct (app_measures s s1 (mkRegion RkMap (page_round (n + IB + UNIT)) [] true) eq_refl eq_refl eq_refl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
pose proof (app_regs_nn s s1 (mkRegion RkMap (page_round (n + IB + UNIT)) [] true) eq_refl NN ltac:(cbn [rg_len]; lia)) as NN1.
cbn [f_mapb f_mapc f_brkb f_resvb f_resvc is_map is_brk is_resv rg_kind rg_live rg_len andb] in A1, A2, A3, A4, A5.
assert (A8 : shift s1 = shift s) by reflexivity. assert (A9 : acnt s1 = acnt s) by reflexivity. assert (A10 : amc s1 = amc s) by reflexivity.
assert (II1 : II s1).
{ pose proof HII as (_ & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9). unfold II.
pose proof (maps_le_app s s1 (mkRegion RkMap (page_round (n + IB + UNIT)) [] true) eq_refl X9 ltac:(unfold f_mapb, is_map; cbn [rg_live rg_kind rg_len andb]; lia)) as ML1.
unfold hand in *. rewrite A3, A4, A5, A6, A8, A9, A10. repeat match goal with |- _ /\ _ => split end; try assumption; try lia. }
assert (L1 : LIVE_UB s1 = LIVE_UB s + page_round (n + IB + UNIT)) by (unfold LIVE_UB; lia).
rq_bind RQ2 RQ3 RQ4.
eapply OKC_bind_y; [apply (OKC_frame_meas X step_seq s1); auto with presK presC presR|].
intros u2 s2 tr2 Hy2 E2. cbn [snd] in E2. specialize (RQ4 tr2 u2 s2 Hy2). clear RQ3 Hy2.
pose proof (meas_eq_all _ _ E2) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E2 II1) as II2.
rq_bind RQ4 RQ5 RQ6.
eapply OKC_bind_y.
{ apply OKC_alloc_meta; [exact RQ5 | exact II2 |]. intros _. unfold ROOMmX. rewrite Q9, Q4, A8. unfold area, PGSZ in *. lia. }
intros og s3 tr3 Hy3 HP3. clear Hy3.
destruct og as [g|]; apply OKC_presR_TT; cfgo.
-
apply Z.leb_gt in Em. unfold MMAP_THRESHOLD in Em.
x_get. rq_get RQ.
match goal with |- OKC _ _ (bind _ (fun r => bind (match r with Some gi => ret (Some gi) | None => bind (alloc_slot _ ?sc _) _ end) _) _) =>
set (scz := sc) in * end.
rq_bind RQ RQ1 RQ2.
eapply OKC_bind_y; [apply OKC_frame_meas; [kgo | cgo | cfgo]|].
intros r s1 tr1 Hy1 E1. cbn [snd] in E1. specialize (RQ2 tr1 r s1 Hy1). clear RQ1 Hy1.
pose proof (meas_eq_all _ _ E1) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10).
pose proof (meas_eq_II _ _ E1 HII) as II1.
rq_bind RQ2 RQ3 RQ4.
eapply (OKC_bind_y X (fun _ => True)).
{ destruct r as [gi|]; [apply OKC_ret; exact I|].
rq_bind RQ3 RQ5 RQ6.
eapply OKC_bind_y.
{ apply (proj1 (OKC_alloc_both X NEST_FUEL ltac:(unfold NEST_FUEL; lia)) scz n s1); [exact RQ5 | | lia].
split; [exact II1|]. left. unfold area in *. rewrite Q9, Q4. unfold PGSZ in *. lia. }
intros idx s2 tr2 Hy2 HP2. apply OKC_presR_TT. cfgo. }
intros gi s4 tr4 Hy4 _. apply OKC_presR_TT. cfgo.
Qed.
Theorem roomcf_malloc : forall n s X, reqs_ok (malloc n s) -> II s -> 0 <= n -> ROOM4 s n ->
LIVE_UB s + 3 * PGSZ + area s + Z.max MMAX (page_round (n + IB + UNIT)) <= X -> roomcf X (malloc n s).
Proof using.
intros n s X RQ HII Hn (R1 & R2 & R3 & R4) RX. exact (proj1 (OKC_malloc X n s RQ HII Hn R4 RX)).
Qed.
Theorem roomcf_free : forall p s X, reqs_ok (free p s) -> II s -> LIVE_UB s <= X -> roomcf X (free p s).
Proof using. intros p s X _ _ _. exact (r_free p X s). Qed.
End d.
