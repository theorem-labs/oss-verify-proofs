(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require ExecutableSpecs VmMapsDisjoint.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd Qc6I QJFf QVsB QCiC Qpj5 QvDJ QKyU Q67d Qgp5 Q7t6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs LinuxProcessSemantics.LinuxProcessSem.Checks.VmMapsDisjoint.
Import Qcrs QUcd Qc6I QJFf QVsB.
Import QCiC.Mq1 Qpj5.Mq1 QvDJ.Mq0 QCiC QKyU Q67d Qgp5 Q7t6.
Import ListNotations.
Import Qc6I.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof. intros. apply mmap_len_bound. assumption. Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. vm_compute. reflexivity. Qed.

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
- constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
- apply IH; assumption.
Qed.

Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
unfold bv_modulus in *.
apply in_app_or in Hin as [Hin|Hin].
- destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
- destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
- exists (a, sz). split; [left; reflexivity| exact Hin].
- destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

Lemma iv_subtract_disjoint : forall a sz lo hi,
bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
(bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
iv_subtract a sz lo hi = [(a, sz)].
Proof.
intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
destruct Hd as [Hd|Hd].
- replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
- replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
- intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
- apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
intros a sz lo hi Hlh Hwf. unfold iv_subtract.
pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
- constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
- constructor; [intros e' []| constructor].
- constructor; [intros e' []| constructor].
- constructor.
Qed.

Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph].

Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
match ph with
| BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_top (m_vmmaps mo)
/\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
| BPDead => True
end.

Lemma KL_rephase : forall L ph pbrk pbrk' mo,
KL L pbrk mo -> phase_inv ph L pbrk' mo -> KL (set_brkph ph L) pbrk' mo.
Proof. intros L ph pbrk pbrk' mo K Hph. kl_open K; constructor; cbn; auto. Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
(In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
/\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
intros L pbrk mo b l K Hin. pose proof alloc_ceiling_lt.
assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
{ destruct Hin as [Hin|[k Hin]]; [pose proof (kl_groups _ _ _ K _ _ Hin)| pose proof (kl_metas _ _ _ K _ _ _ Hin)]; tauto. }
pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
- apply elo_went. lia.
- apply ehi_went; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
In x (ld_resv L)
\/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
\/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
\/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
- left; exact H.
- right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
- right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
- right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. pose proof (Z.land_nonneg (-x) (PGSZ - 1)). unfold PGSZ in *. lia. Qed.

Definition OWN (X : list bptr) (G : PState -> Model -> Prop) : assn PState := fun s mo =>
(exists L, creach (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L))
/\ List.NoDup (map fst X) /\ G s mo.

Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

End Mq0.

From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= Stdlib.omega.PreOmega.Z.to_euclidean_division_equations.
Local Set Keyed Unification.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qgp5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qgp5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qdyg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qdyg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhFR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhFR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9dL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9dL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsc9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsc9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QcxL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QcxL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QchP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QchP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrTb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QV5O.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QV5O. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTxS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTxS. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjEq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjEq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfGI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfGI.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). Local Ltac Stdlib.micromega.Zify.zify_internal_to_euclidean_division_equations ::= QdTa.mkr__zify_internal_to_euclidean_division_equations_5.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition fold_f (s : Z) : bool := forallb (fun off => negb (s <? off) || ((0 <=? fold_off off s) && (fold_off off s <=? s))) (zrange 0 256).

Section EF.
Variables (st : mstate) (g : aptr) (idx n off : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let gm := default (0%N, 0) (m_mem mr).
Let c : aptr := aadd gm (UNIT + stride * idx).
Let e : aptr := aadd c (stride - IB).
Let p0 : aptr := if off =? 0 then c else aadd c (UNIT * off).
Let res := snd e - snd p0 - n.
Let q := (snd p0 - (snd gm + UNIT)) / UNIT.

Definition ef_list : list (aptr * Z) :=
(if negb (off =? 0) then [(aadd c (-2), off); (aadd (aadd c (-2)) 1, Z.shiftr off 8); (aadd c (-3), 224); (aadd p0 (-4), 0)] else [])
++ [(aadd p0 (-2), q); (aadd (aadd p0 (-2)) 1, Z.shiftr q 8); (aadd p0 (-3), idx)]
++ (if negb (res =? 0) then [(aadd e (- res), 0)] else [])
++ (if 5 <=? res then [(aadd e (-4), res); (aadd (aadd e (-4)) 1, Z.shiftr res 8); (aadd (aadd e (-4)) 2, Z.shiftr res 16); (aadd (aadd e (-4)) 3, Z.shiftr res 24); (aadd e (-5), 0)] else [])
++ [(aadd p0 (-3), Z.land idx 31 + Z.shiftl (if 5 <=? res then 5 else res) 5)].

End EF.

Fixpoint lastw (l : list (aptr * Z)) (r : aptr) (acc : option Z) : option Z :=
match l with
| [] => acc
| (a, v) :: l' => lastw l' r (if aptr_eqb a r then Some v else acc)
end.

