(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0h.v (donor image sha256 7093581aab04), with its module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0i YO0d YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG0f YG0v YG0n YG0s YG08.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold ASAN_CEIL in H2.
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma w64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia. Qed.
Lemma w64_uw : forall x : word, w64 (bv_unsigned x) = x.
Proof. intros x. unfold w64. apply Z_to_bv_bv_unsigned. Qed.
Definition uw (x : word) : Z := bv_unsigned x.
Definition wz (e : word * word) : Z * Z := (uw (fst e), uw (snd e)).
Lemma wiv_wz : forall e, wiv (wz e) = e.
Proof. intros [a b]. unfold wiv, wz. cbn. rewrite !w64_uw. reflexivity. Qed.
Lemma wz_wiv : forall p, 0 <= fst p < 2 ^ 64 -> 0 <= snd p < 2 ^ 64 -> wz (wiv p) = p.
Proof. intros [a b] Ha Hb. unfold wiv, wz, uw. cbn in *. rewrite !w64_unsigned by lia. reflexivity. Qed.
Lemma uw_range : forall x : word, 0 <= uw x < 2 ^ 64.
Proof. intros x. unfold uw. apply u64_range. Qed.
Lemma iv_subtract_disjoint : forall (a sz : word) lo hi,
lo <= hi -> 0 < uw sz -> uw a + uw sz <= lo \/ hi <= uw a -> iv_subtract a sz lo hi = [(a, sz)].
Proof.
intros a sz lo hi Hlh Hsz Hd. pose proof (uw_range a). pose proof (uw_range sz). unfold uw in *. unfold iv_subtract.
destruct (Z.ltb_spec (bv_unsigned a) lo) as [E1|E1]; destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [E2|E2]; cbn [app]; try lia.
- replace (Z.min (bv_unsigned sz) (lo - bv_unsigned a)) with (bv_unsigned sz) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
- replace (Z.max (bv_unsigned a) hi) with (bv_unsigned a) by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma iv_subtract_inside : forall b s lo hi,
0 <= b -> b <= lo -> lo <= hi -> hi <= b + s -> b + s < 2 ^ 64 ->
iv_subtract (w64 b) (w64 s) lo hi = (if b <? lo then [(w64 b, w64 (lo - b))] else []) ++ (if hi <? b + s then [(w64 hi, w64 (b + s - hi))] else []).
Proof.
intros b s lo hi H0 H1 H2 H3 H4. unfold iv_subtract. rewrite !w64_unsigned by lia.
replace (Z.min s (lo - b)) with (lo - b) by lia. replace (Z.max b hi) with hi by lia. reflexivity.
Qed.
Lemma iv_subtract_nonempty : forall (a sz : word) lo hi q, 0 < uw sz -> In q (iv_subtract a sz lo hi) -> 0 < uw (snd q).
Proof.
intros a sz lo hi q Hsz Hq. pose proof (uw_range a). pose proof (uw_range sz). unfold uw in *. unfold iv_subtract in Hq.
apply in_app_iff in Hq.
destruct Hq as [Hq|Hq].
- destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [snd].
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia). lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hq]. destruct Hq as [<-|[]]. cbn [snd].
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia). lia.
Qed.
Lemma maps_subtract_nonempty : forall l lo hi, (forall q, In q l -> 0 < uw (snd q)) -> forall q, In q (maps_subtract l lo hi) -> 0 < uw (snd q).
Proof.
induction l as [|[a sz] l IH]; intros lo hi Hl q Hq; [destruct Hq|]. cbn [maps_subtract] in Hq. apply in_app_iff in Hq as [Hq|Hq].
- apply (iv_subtract_nonempty a sz lo hi q); [exact (Hl (a, sz) (or_introl eq_refl)) | exact Hq].
- apply (IH lo hi); [intros q' Hq'; apply Hl; right; exact Hq' | exact Hq].
Qed.
Lemma maps_subtract_app : forall l1 l2 lo hi, maps_subtract (l1 ++ l2) lo hi = maps_subtract l1 lo hi ++ maps_subtract l2 lo hi.
Proof. induction l1 as [|[a sz] t IH]; intros l2 lo hi; cbn; [reflexivity|]. rewrite IH, app_assoc. reflexivity. Qed.
Lemma maps_subtract_id : forall l lo hi, lo <= hi ->
(forall e, In e l -> 0 < uw (snd e) /\ (uw (fst e) + uw (snd e) <= lo \/ hi <= uw (fst e))) -> maps_subtract l lo hi = l.
Proof.
induction l as [|[a sz] t IH]; intros lo hi Hlh H; cbn; [reflexivity|].
destruct (H (a, sz) (or_introl eq_refl)) as [P Q]. cbn in P, Q. rewrite (iv_subtract_disjoint a sz lo hi Hlh P Q), (IH lo hi Hlh). reflexivity.
intros e He. apply H. right. exact He.
Qed.
Lemma region_free_app : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = region_free l1 lo n && region_free l2 lo n.
Proof. induction l1 as [|[a sz] t IH]; intros l2 lo n; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.
Lemma region_free_intro : forall l (lo n : word),
(forall e, In e l -> uw (fst e) + uw (snd e) <= uw lo \/ uw lo + uw n <= uw (fst e)) -> region_free l lo n = true.
Proof.
induction l as [|[a sz] t IH]; intros lo n H; cbn; [reflexivity|].
rewrite IH by (intros e He; apply H; right; exact He).
destruct (H (a, sz) (or_introl eq_refl)) as [D|D]; cbn [fst snd] in D; unfold uw in D; unfold iv_overlap;
destruct (Z.ltb_spec (bv_unsigned lo) (bv_unsigned a + bv_unsigned sz)); destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned lo + bv_unsigned n)); cbn; try reflexivity; exfalso; lia.
Qed.
Lemma region_free_reserved : forall (sgs : list Segment) lo len,
(forall sg, In sg sgs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) ->
kImgEnd + 4096 <= lo -> 0 <= len -> lo + len < 2 ^ 64 ->
region_free (segments_reserved sgs) (w64 lo) (w64 len) = true.
Proof.
intros sgs lo len IMG H1 H2 H3. apply region_free_intro. intros e He. unfold segments_reserved in He. apply in_map_iff in He as (sg & <- & Hsg).
destruct (IMG sg Hsg) as [G1 G2]. unfold segment_reservation. cbn [fst snd]. left.
unfold page_round_up_Z, page_round_down_Z, page_size.
set (b := Z.of_N (seg_base sg)) in *. set (z := Z.of_N (seg_size sg)) in *.
pose proof (Z.div_mod b 4096 ltac:(lia)). pose proof (Z.mod_pos_bound b 4096 ltac:(lia)).
pose proof (Z.div_mod (b + z + 4096 - 1) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (b + z + 4096 - 1) 4096 ltac:(lia)).
unfold kImgEnd in *. unfold uw, w64.
rewrite !Z_to_bv_unsigned. rewrite !bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia). lia.
Qed.
Lemma pairwise_zdisjoint_In : forall l x y, pairwise zdisjoint l -> In x l -> In y l -> x = y \/ zdisjoint x y.
Proof.
induction l as [|h t IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [left; reflexivity | right; exact (proj1 (Forall_forall _ _) F y Hy) | |].
- right. pose proof (proj1 (Forall_forall _ _) F x Hx) as D. unfold zdisjoint in *. lia.
- exact (IH x y P Hx Hy).
Qed.
Lemma pairwise_filter : forall (f : Z * Z -> bool) l, pairwise zdisjoint l -> pairwise zdisjoint (List.filter f l).
Proof.
induction l as [|h t IH]; intros P; cbn; [exact I|]. destruct P as [F P]. destruct (f h); cbn; [|exact (IH P)].
split; [|exact (IH P)]. apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) F y Hy).
Qed.
Lemma iv_subtract_within : forall (a sz : word) lo hi x, 0 <= lo -> 0 <= hi < 2 ^ 64 ->
In x (iv_subtract a sz lo hi) -> uw a <= uw (fst x) /\ uw (fst x) + uw (snd x) <= uw a + uw sz.
Proof.
intros a sz lo hi x Hlo Hhi Hx. pose proof (uw_range a). pose proof (uw_range sz). unfold uw in *. unfold iv_subtract in Hx.
apply in_app_iff in Hx. destruct Hx as [Hx|Hx].
- destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hx]. destruct Hx as [<-|[]]. cbn [fst snd].
rewrite Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia). lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hx]. destruct Hx as [<-|[]]. cbn [fst snd].
rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64%N) with (2 ^ 64); lia). lia.
Qed.
Lemma maps_subtract_within : forall l lo hi x, 0 <= lo -> 0 <= hi < 2 ^ 64 ->
In x (maps_subtract l lo hi) -> exists e, In e l /\ uw (fst e) <= uw (fst x) /\ uw (fst x) + uw (snd x) <= uw (fst e) + uw (snd e).
Proof.
intros l lo hi x Hlo Hhi Hx. induction l as [|[a sz] t IH]; [destruct Hx|]. cbn [maps_subtract] in Hx. apply in_app_iff in Hx as [Hx|Hx].
- exists (a, sz). split; [left; reflexivity|]. exact (iv_subtract_within a sz lo hi x Hlo Hhi Hx).
- destruct (IH Hx) as (e0 & He0 & X). exists e0. split; [right; exact He0 | exact X].
Qed.
Section K3.
Variable segs : list Segment.
Variables (U : list (list Z)) (pp cc bb : Z).
Variables (ly : alayout) (S : astate) (md md' : Model) (c : Z).
Hypothesis LO : layout_ok ly.
Hypothesis W : WfP U pp cc bb S.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis L : ALedger segs ly S md.
Lemma al_img_env' : forall sg, In sg segs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd.
Proof.
intros sg Hsg. pose proof (al_img _ _ _ _ L sg Hsg) as [I1 I2]. pose proof (lo_img ly LO) as (J0 & J1 & J2 & J3).
rewrite J0 in I1, I2. unfold kImgLo in *. lia.
Qed.
Hypothesis RES : vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md).
Hypothesis LIM : vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md).
Hypothesis MMB : vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md).
Hypothesis ISP : vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
Lemma TOPeq : alloc_top (m_vmmaps md') = alloc_top (m_vmmaps md).
Proof. unfold alloc_top. rewrite ISP. reflexivity. Qed.
Hypothesis SPL : sec_placed ly S.
Hypothesis COV : forall x, ~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize) ->
YK0g.covered (vm_noaccess (m_vmmaps md') ++ m_vm_lazy md') x = YK0g.covered (vm_noaccess (m_vmmaps md) ++ m_vm_lazy md) x.
Hypothesis NAF : forall lo n, region_free (vm_noaccess (m_vmmaps md)) lo n = true -> region_free (vm_noaccess (m_vmmaps md')) lo n = true.
Local Notation r := (reg S c).
Local Notation n := kUserMapSize.
Lemma HL : (Z.to_nat c < length (st_regions S))%nat.
Proof. rewrite (wf_len_regions _ _ _ _ _ W). lia. Qed.
Lemma reg_upd : forall r', reg (upd_reg c r' S) c = r'.
Proof. intros r'. unfold upd_reg. apply reg_upd_same; [lia | exact HL]. Qed.
Lemma reg_upd_ne : forall r' c', 0 <= c' -> c' <> c -> reg (upd_reg c r' S) c' = reg S c'.
Proof. intros r' c' H1 H2. unfold upd_reg. apply reg_upd_other; lia. Qed.
Lemma sec_extents_upd : forall r', sec_extents ly (upd_reg c r' S) = sec_extents ly S.
Proof. reflexivity. Qed.
Lemma sec_live_upd : forall r', sec_live_bytes (upd_reg c r' S) = sec_live_bytes S.
Proof. reflexivity. Qed.
Lemma sec_reserved_upd : forall r', st_sec_reserved (upd_reg c r' S) = st_sec_reserved S.
Proof. reflexivity. Qed.
Lemma sec_extents_off_prim : forall e x, In e (sec_extents ly S) -> fst e <= x < fst e + snd e ->
~ (ly_prim ly <= x < ly_prim ly + kPrimResvSize).
Proof.
intros e x He Hx. destruct SPL as [_ PD].
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
assert (D : zdisjoint e (ly_prim ly, kPrimResvSize)).
{ clear - PD He INP. induction (sec_extents ly S) as [|y t IH]; [destruct He|]. cbn [app] in PD. destruct PD as [F PD].
destruct He as [<-|He]; [| exact (IH He PD)].
exact (proj1 (Forall_forall _ _) F _ ltac:(apply in_app_iff; right; exact INP)). }
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma esec_K3 : esec (vm_noaccess (m_vmmaps md')) (m_vm_lazy md') (sec_extents ly S) = esec (vm_noaccess (m_vmmaps md)) (m_vm_lazy md) (sec_extents ly S).
Proof.
apply esec_ext.
- destruct SPL as [PF _]. pose proof (sec_extents_sizes64P U pp cc bb ly S W) as SZ. apply Forall_forall. intros e He.
pose proof (proj1 (Forall_forall _ _) PF e He) as (_ & [H1 H2] & H3). pose proof (proj1 (Forall_forall _ _) SZ e He) as H4. cbn beta in H4.
clear - H1 H2 H3 H4. ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. lia.
- intros e x He Hx. apply COV. exact (sec_extents_off_prim e x He Hx).
Qed.
Lemma prim_committed_upd : forall r',
prim_committed (upd_reg c r' S) = prim_committed S - (rg_mapped_user r + rg_mapped_fa r) + (rg_mapped_user r' + rg_mapped_fa r').
Proof. intros r'. unfold upd_reg. apply prim_committed_set_region; [lia | exact HL]. Qed.
Lemma cls : cls_ok c r (cache S c) (st_cache_inited S) (chunk_offs S c) (batch_offs S c).
Proof. exact (wf_classes _ _ _ _ _ W c Hc). Qed.
Lemma mu_fa_facts : 0 <= rg_mapped_user r <= kUserMapSize * EV_MAX /\ rg_mapped_user r mod kUserMapSize = 0 /\
0 <= rg_mapped_fa r <= kFreeArrayMax /\ rg_mapped_fa r mod kFreeArrayMapSize = 0.
Proof.
pose proof cls as C. pose proof (wr_alloc _ _ _ _ _ _ C). pose proof (wr_mapped_al _ _ _ _ _ _ C). pose proof (wr_fa _ _ _ _ _ _ C). pose proof (wr_fa_bound _ _ _ _ _ _ C).
pose proof (mapped_user_bound U pp cc bb S c W Hc). pose proof (wf_slack _ _ _ _ _ W). unfold kUserMapSize in *.
split; [nia|]. split; [assumption|]. split; [|tauto]. split; [tauto | assumption].
Qed.
Lemma holes_shape : forall h, In h (rg_holes r) ->
(h = (rg_mapped_user r, kUserMapSize) /\ rg_mapped_user r + kUserMapSize <= kFreeArrayOffset) \/
(h = (kFreeArrayOffset + rg_mapped_fa r, kFreeArrayMapSize) /\ rg_mapped_fa r + kFreeArrayMapSize <= kFreeArrayMax).
Proof. intros h Hh. exfalso. exact (proj1 (Forall_forall _ _) (proj1 (wr_holes _ _ _ _ _ _ cls)) h Hh). Qed.
Lemma holes_shape_any : forall c' h, 1 <= c' <= 31 -> In h (rg_holes (reg S c')) ->
(h = (rg_mapped_user (reg S c'), kUserMapSize) /\ rg_mapped_user (reg S c') + kUserMapSize <= kFreeArrayOffset) \/
(h = (kFreeArrayOffset + rg_mapped_fa (reg S c'), kFreeArrayMapSize) /\ rg_mapped_fa (reg S c') + kFreeArrayMapSize <= kFreeArrayMax).
Proof. intros c' h Hc' Hh. exfalso. exact (proj1 (Forall_forall _ _) (proj1 (wr_holes _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) h Hh). Qed.
Definition offU : Z := rg_mapped_user r.
Definition addrU : Z := region_base ly c + offU.
Definition rUp : region := mkRegion (offU + n) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r) (del_hole offU (rg_holes r)).
Definition rUm : region := mkRegion offU (rg_alloc_user r) (rg_mapped_fa r) (rg_free r) (add_hole (offU, n) (rg_holes r)).
Definition SUp : astate := upd_reg c rUp S.
Definition SUm : astate := upd_reg c rUm S.
Lemma filter_holes_id : ~ In (offU, n) (rg_holes r) -> List.filter (fun h' => negb (fst h' =? offU)) (rg_holes r) = rg_holes r.
Proof.
intros Hn. pose proof mu_fa_facts as (M1 & _ & M3 & _).
assert (A : forall h, In h (rg_holes r) -> fst h <> offU).
{ intros h Hh E. destruct (holes_shape h Hh) as [[-> _]|[-> _]]; [exact (Hn Hh)|]. cbn in E. unfold offU, kFreeArrayOffset, kUserMapSize, EV_MAX in *. lia. }
induction (rg_holes r) as [|h t IH]; [reflexivity|]. cbn. destruct (Z.eqb_spec (fst h) offU) as [E|NE]; [exfalso; exact (A h (or_introl eq_refl) E)|].
cbn. f_equal. apply IH; [intros Hin; apply Hn; right; exact Hin | intros h' Hh'; apply A; right; exact Hh'].
Qed.
Lemma prim_hole_at_same : forall S', (forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) ->
forall a, prim_hole_at ly S' a <-> prim_hole_at ly S a.
Proof.
intros S' H a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hh & Ha); exists c', h; [rewrite H in Hh by lia | rewrite <- H in Hh by lia]; auto.
Qed.
Lemma cut_ok_mono : forall S', (forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c')) ->
forall x, cut_ok ly S x -> cut_ok ly S' x.
Proof.
intros S' H x [X|[X|(c' & Hc' & [(k & E & B)|(k & E & B)])]]; [left; exact X | right; left; exact X | |]; right; right; exists c'; split; [exact Hc'| |exact Hc'|];
destruct (H c' Hc') as [H1 H2]; [left | right]; exists k; split; [exact E | lia | exact E | lia].
Qed.
Lemma ALedger_user_granted_piece :
~ In (offU, n) (rg_holes r) ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
ALedger segs ly SUp md'.
Proof.
intros Hn VM EG. pose proof (filter_holes_id Hn) as FH. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg SUp c') = rg_holes (reg S c')).
{ intros c' Hc'. unfold SUp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn; unfold del_hole; exact FH | rewrite reg_upd_ne by lia; reflexivity]. }
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg SUp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg SUp c')).
{ intros c' Hc'. unfold SUp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn [rg_mapped_user rg_mapped_fa rUp]; unfold offU, kUserMapSize; lia | rewrite reg_upd_ne by lia; lia]. }
constructor; rewrite ?RES, ?LIM, ?VM, ?TOPeq, ?sec_extents_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
+ eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|]. split; apply (cut_ok_mono SUp MONO); assumption.
+ intros a Ha. rewrite (P3 a Ha). rewrite (prim_hole_at_same SUp HOLES a). tauto.
- unfold SUp. rewrite ?sec_extents_upd, esec_K3, sec_reserved_upd, prim_committed_upd. cbn [rg_mapped_user rg_mapped_fa rUp]. unfold offU, kUserMapSize in *. lia.
Qed.
Lemma prim_bounds : kHighMemBeg <= ly_prim ly /\ ly_prim ly <= region_base ly c /\ addrU + n <= region_base ly c + kFreeArrayOffset /\
region_base ly c + kFreeArrayOffset + kFreeArrayMax <= ly_prim ly + kPrimResvSize /\ 0 <= offU.
Proof.
pose proof mu_fa_facts as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
unfold addrU, offU, region_base. fold r. rewrite region_off_eq by lia.
unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize, kUserMapSize, EV_MAX, n in *. repeat split; try lia; nia.
Qed.
Lemma prim_hi : ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ASAN_CEIL < 2 ^ 63.
Proof.
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
ceil; unfold ASAN_CEIL in *. split; lia.
Qed.
Lemma perm_facts : forall z, In z (perm_maps ly) -> 0 <= fst z /\ 0 <= snd z /\ fst z + snd z < 2 ^ 63 /\ zdisjoint z (ly_prim ly, kPrimResvSize).
Proof.
intros z Hz. pose proof (lo_disj ly LO) as DJ. pose proof (lo_extra ly LO) as (_ & EF & ED). pose proof (lo_ctx ly LO) as CX.
pose proof (lo_app ly LO) as HI.
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
assert (OWN : forall e, In e (owned_extents ly) -> e <> (ly_prim ly, kPrimResvSize) -> 0 <= fst e /\ 0 <= snd e /\ fst e + snd e <= ASAN_CEIL /\ zdisjoint e (ly_prim ly, kPrimResvSize)).
{ intros e He Hne. pose proof (proj1 (Forall_forall _ _) HI e He) as [H1 H2]. unfold in_app in *.
destruct (pairwise_zdisjoint_In _ _ _ DJ ltac:(unfold static_extents; apply in_app_iff; left; exact He) INP) as [E|D]; [exfalso; exact (Hne E)|].
assert (0 <= snd e) by (unfold owned_extents in He; cbn in He; unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize in He;
repeat (destruct He as [<-|He]; [cbn; lia|]); destruct He).
ceil; unfold kHighMemBeg, kLowShadowBeg, ASAN_CEIL in *. repeat split; try lia. exact D. }
assert (OWN' : forall e, In e (owned_extents ly) -> e <> (ly_prim ly, kPrimResvSize) -> 0 <= fst e /\ 0 <= snd e /\ fst e + snd e < 2 ^ 63 /\ zdisjoint e (ly_prim ly, kPrimResvSize)).
{ intros e He Hne. destruct (OWN e He Hne) as (A1 & A2 & A3 & A4). ceil; unfold ASAN_CEIL in A3. repeat split; try lia. exact A4. }
unfold perm_maps in Hz. apply in_app_iff in Hz as [Hz|Hz].
- cbn in Hz. destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]].
+ apply OWN'; [unfold owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kThreadObjSize, kPrimResvSize in E2; lia].
+ apply OWN'; [unfold owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kFakeStackSize, kPrimResvSize in E2; lia].
+ apply OWN'; [unfold owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kNodesBlockSize, kPrimResvSize in E2; lia].
+ apply OWN'; [unfold owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kStoreBlockSize, kPrimResvSize in E2; lia].
+ destruct (OWN (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto) ltac:(intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPrimResvSize in E2; lia)) as (C1 & _ & C3 & _).
cbn [fst snd] in *. ceil; unfold kCtxMapSize, ASAN_CEIL in *. repeat split; try lia. exact CX.
+ apply OWN'; [unfold owned_extents; cbn; tauto | intros E; pose proof (f_equal snd E) as E2; cbn in E2; unfold kPrimResvSize in E2; lia].
- pose proof (proj1 (Forall_forall _ _) EF z Hz) as (Z1 & Z2 & Z3 & Z4 & Z5).
destruct (pairwise_zdisjoint_In _ _ _ ED ltac:(apply in_app_iff; left; exact Hz) ltac:(apply in_app_iff; right; exact INP)) as [E|D].
+ exfalso. rewrite E in Z2. cbn [snd] in Z2. unfold kPrimResvSize in Z2. lia.
+ ceil; unfold ASAN_CEIL in *. repeat split; try lia. exact D.
Qed.
Lemma ALedger_user_granted_hole :
In (offU, n) (rg_holes r) ->
vm_maps (m_vmmaps md') = wiv (addrU, n) :: vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
ALedger segs ly SUp md'.
Proof.
intros Hh VM EG. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15]. pose proof prim_bounds as (B1 & B2 & B3 & B4 & B5).
pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
assert (HOLESc : rg_holes (reg SUp c) = del_hole offU (rg_holes r)) by (unfold SUp; rewrite reg_upd; reflexivity).
assert (HOLESo : forall c', 1 <= c' <= 31 -> c' <> c -> rg_holes (reg SUp c') = rg_holes (reg S c')) by (intros c' Hc' NE; unfold SUp; rewrite reg_upd_ne by lia; reflexivity).
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg SUp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg SUp c')).
{ intros c' Hc'. unfold SUp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn [rg_mapped_user rg_mapped_fa rUp]; unfold offU, kUserMapSize; lia | rewrite reg_upd_ne by lia; lia]. }
assert (HOLE' : forall a, prim_hole_at ly SUp a <-> prim_hole_at ly S a /\ ~ in_zr a (addrU, n)).
{ intros a. unfold prim_hole_at. split.
- intros (c' & h & Hc' & Hin & Ha). destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite HOLESc in Hin. unfold del_hole in Hin. apply filter_In in Hin as [Hin Hne]. apply negb_true_iff in Hne. apply Z.eqb_neq in Hne.
split; [exists c, h; auto|]. intros X. destruct (holes_shape h Hin) as [[-> _]|[-> _]]; cbn in Hne; [exact (Hne eq_refl)|].
unfold in_zr, addrU, offU in Ha, X. cbn [fst snd] in Ha, X. unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, EV_MAX, n in *. fold r in Ha. lia.
+ rewrite HOLESo in Hin by lia. split; [exists c', h; auto|]. intros X.
pose proof (holes_shape_any c' h Hc' Hin) as SH.
pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'.
pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as AL'.
unfold in_zr, addrU, offU, region_base in Ha, X. cbn [fst snd] in Ha, X. rewrite !region_off_eq in Ha, X by lia.
destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Ha; unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *;
clear - Ha X NE MB' FB' F0' M1 Hc Hc' SL' AL' SB; lia.
- intros ((c' & h & Hc' & Hin & Ha) & NX). destruct (Z.eq_dec c' c) as [->|NE].
+ exists c, h. rewrite HOLESc. split; [lia|]. split; [|exact Ha]. unfold del_hole. apply filter_In. split; [exact Hin|].
apply negb_true_iff, Z.eqb_neq. intros E. apply NX. destruct (holes_shape h Hin) as [[-> _]|[-> _]]; cbn in E.
* unfold in_zr, addrU, offU in Ha |- *. cbn [fst snd] in Ha |- *. fold r. fold r in Ha. exact Ha.
* exfalso. unfold offU, kFreeArrayOffset, kUserMapSize, EV_MAX in *. fold r in E. lia.
+ exists c', h. rewrite HOLESo by lia. auto. }
constructor; rewrite ?RES, ?LIM, ?VM, ?TOPeq, ?sec_extents_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
-
destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists ((addrU, n) :: pieces). split; [split; [|split]|].
+ apply Forall_cons; [|eapply Forall_impl; [|exact P1]; intros p (A & B & C); split; [exact A|]; split; apply (cut_ok_mono SUp MONO); assumption].
cbn [fst snd]. split; [unfold kUserMapSize; lia|].
pose proof (Z.div_exact (rg_mapped_user r) 262144 ltac:(lia)) as DX. unfold kUserMapSize in M2.
split; (right; right; exists c; split; [exact Hc|]; left); [exists (offU / kUserMapSize) | exists (offU / kUserMapSize + 1)];
unfold addrU, SUp; rewrite reg_upd; cbn [rg_mapped_user rUp]; unfold offU, kUserMapSize in *; split; lia.
+
cbn. split; [|exact P2]. apply Forall_forall. intros p Hp. unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec (fst p) (addrU + n)) as [X1|X1]; [|left; lia]. destruct (Z_lt_le_dec addrU (fst p + snd p)) as [X2|X2]; [|right; lia]. exfalso.
destruct (proj1 (P4 p) Hp) as (_ & Q0 & Q1 & Q2).
assert (HA : exists a, in_zr a p /\ addrU <= a < addrU + n).
{ destruct (Z_lt_le_dec addrU (fst p)); [exists (fst p) | exists addrU]; unfold in_zr, kUserMapSize in *; split; lia. }
destruct HA as (a & Ha1 & Ha2).
apply (proj1 (P3 a ltac:(clear - Ha2 B2 B3 B4 B5; unfold addrU, offU, kUserMapSize, kFreeArrayMax, kFreeArrayOffset in *; lia)) (proj2 (Exists_exists _ _) (ex_intro _ p (conj Hp Ha1)))).
exists c, (offU, n). split; [exact Hc|]. split; [exact Hh|]. unfold in_zr, addrU in Ha2 |- *. cbn [fst snd]. exact Ha2.
+ intros a Ha. rewrite (HOLE' a). split.
* intros HE [Hh' NX]. apply Exists_cons in HE as [HE|HE]; [exact (NX HE)|]. exact (proj1 (P3 a Ha) HE Hh').
* intros NH. destruct (Z_lt_le_dec a addrU) as [Y1|Y1]; [|destruct (Z_lt_le_dec a (addrU + n)) as [Y2|Y2]; [apply Exists_cons_hd; unfold in_zr; cbn; lia|]];
apply Exists_cons_tl; apply (proj2 (P3 a Ha)); intros Hh'; apply NH; split; [exact Hh' | unfold in_zr; cbn [fst snd]; lia | exact Hh' | unfold in_zr; cbn [fst snd]; lia].
+ intros p. cbn. rewrite (P4 p). unfold wiv. cbn [fst snd]. split.
* intros [<-|(I1 & I2 & I3 & I4)]; [|auto]. cbn [fst snd]. split; [left; reflexivity|]. split; [unfold kUserMapSize; lia|]. clear - B2 B3 B4 B5; unfold addrU, offU, kUserMapSize, kFreeArrayMax, kFreeArrayOffset in *; lia.
* intros ([E|I1] & I2 & I3 & I4); [|right; auto]. left.
destruct p as [b l]. unfold wiv in E. cbn [fst snd] in E, I2, I3, I4.
pose proof prim_hi as [C1 C2]. pose proof prim_bounds as (D1 & D2 & D3 & D4 & D5).
pose proof (f_equal (fun x => bv_unsigned (fst x)) E) as U1. pose proof (f_equal (fun x => bv_unsigned (snd x)) E) as U2. cbn [fst snd] in U1, U2.
rewrite !w64_unsigned in U1 by (clear - C1 C2 D1 D2 D3 D4 D5 I2 I3 I4; unfold addrU, offU, kHighMemBeg, kPrimResvSize, kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *; lia).
rewrite !w64_unsigned in U2 by (clear - C1 C2 D1 D2 D3 D4 D5 I2 I3 I4; unfold kHighMemBeg, kPrimResvSize, kUserMapSize in *; lia). rewrite U1, U2. reflexivity.
- right. exact L5.
- right. exact L6.
- intros e He. right. exact (L7 e He).
- intros e He. destruct He as [<-|He]; [|exact (L8 e He)].
apply Exists_exists. exists (ly_prim ly, kPrimResvSize). split.
+ unfold lazy_zones. apply in_or_app. left. cbn. do 4 right. left. reflexivity.
+ pose proof prim_hi as [C1 C2]. unfold wiv. cbn [fst snd].
rewrite !w64_unsigned by (clear - C1 C2 B1 B2 B3 B4 B5; unfold addrU, offU, kHighMemBeg, kPrimResvSize, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *; lia).
clear - C1 C2 B1 B2 B3 B4 B5. unfold addrU, offU, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia.
- unfold SUp. rewrite ?sec_extents_upd, esec_K3, sec_reserved_upd, prim_committed_upd. cbn [rg_mapped_user rg_mapped_fa rUp]. unfold offU, kUserMapSize in *. lia.
Qed.
Lemma maps_subtract_In : forall l lo hi x, In x (maps_subtract l lo hi) <-> exists e, In e l /\ In x (iv_subtract (fst e) (snd e) lo hi).
Proof.
induction l as [|[a sz] t IH]; intros lo hi x; cbn.
- split; [intros [] | intros (e & [] & _)].
- rewrite in_app_iff, IH. split.
+ intros [H|(e & He & Hx)]; [exists (a, sz); auto | exists e; auto].
+ intros (e & [<-|He] & Hx); [left; exact Hx | right; exists e; auto].
Qed.
Lemma no_cut_inside : forall x, cut_ok ly S x -> ~ (addrU < x < addrU + n).
Proof.
intros x CX HX. pose proof prim_bounds as (B1 & B2 & B3 & B4 & B5). pose proof mu_fa_facts as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
unfold addrU, offU, region_base in HX, B2, B3, B4. rewrite region_off_eq in HX, B2, B3, B4 by lia.
destruct CX as [->|[->|(c' & Hc' & [(k & -> & Bk)|(k & -> & Bk)])]]; unfold region_base, fa_base in *; rewrite ?region_off_eq in HX by lia; try rewrite ?region_off_eq in Bk by lia.
- unfold kUserMapSize in *. lia.
- unfold kUserMapSize, kPrimResvSize, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
pose proof (wr_mapped_al _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as AL'.
destruct (Z.eq_dec c' c) as [->|NE].
+
apply Z.mod_divide in M2 as [q Hq]; [|unfold kUserMapSize; lia]. unfold kUserMapSize, EV_MAX in *. lia.
+ unfold kUserMapSize, EV_MAX in *. lia.
- pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'. pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'.
unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax, EV_MAX in *. lia.
Qed.
Lemma no_hole_in_range : ~ In (offU, n) (rg_holes r) -> forall a, addrU <= a < addrU + n -> ~ prim_hole_at ly S a.
Proof.
intros Hn a Ha (c' & h & Hc' & Hin & Hx). pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
pose proof (holes_shape_any c' h Hc' Hin) as SH.
pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'.
pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as AL'.
unfold in_zr, addrU, offU, region_base in Ha, Hx. cbn [fst snd] in Hx. rewrite !region_off_eq in Ha, Hx by lia.
destruct (Z.eq_dec c' c) as [->|NE].
- destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Hx; [exact (Hn Hin)|]. unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *. lia.
- destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Hx; unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *;
clear - Ha Hx NE MB' FB' F0' M1 Hc Hc' SL' AL' SB; lia.
Qed.
Lemma zones_vs_prim : sec_placed ly S -> forall z, In z (lazy_zones ly ++ sec_extents ly S) ->
z = (ly_prim ly, kPrimResvSize) \/ zdisjoint z (ly_prim ly, kPrimResvSize).
Proof.
intros [_ PD] z Hz. pose proof (lo_disj ly LO) as DJ. pose proof (lo_extra ly LO) as (_ & EF & ED). pose proof (lo_ctx ly LO) as CX.
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
assert (STA : forall y, In y (static_extents ly) -> y = (ly_prim ly, kPrimResvSize) \/ zdisjoint y (ly_prim ly, kPrimResvSize)).
{ intros y Hy. destruct (pairwise_zdisjoint_In _ _ _ DJ Hy INP) as [E|D]; [left; exact E | right; exact D]. }
apply in_app_iff in Hz as [Hz|Hz].
- unfold lazy_zones in Hz. cbn [app] in Hz.
destruct Hz as [<-|[<-|[<-|[<-|[<-|[<-|[<-|Hz]]]]]]].
+ right. unfold zdisjoint. cbn [fst snd]. left. unfold kLowShadowBeg, kLowShadowEnd, kHighMemBeg in *. lia.
+ right. unfold zdisjoint. cbn [fst snd]. left. unfold kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
+ right. unfold zdisjoint. cbn [fst snd]. left. unfold kLowShadowEnd, kHighShadowBeg, kHighMemBeg in *. lia.
+ destruct (STA (ly_SB ly, kStoreBlockSize) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as [E|D]; [|right; exact D].
exfalso. pose proof (f_equal snd E) as E2. cbn in E2. unfold kStoreBlockSize, kPrimResvSize in E2. lia.
+ left. reflexivity.
+ destruct (STA (ly_Q ly, kPtrArrayResv) ltac:(unfold static_extents, owned_extents; cbn; tauto)) as [E|D]; [|right; exact D].
exfalso. pose proof (f_equal snd E) as E2. cbn in E2. unfold kPtrArrayResv, kPrimResvSize in E2. lia.
+ right. exact CX.
+ apply in_app_iff in Hz as [Hz|Hz]; [|exact (STA z Hz)].
right. destruct (pairwise_zdisjoint_In _ _ _ ED ltac:(apply in_app_iff; left; exact Hz) ltac:(apply in_app_iff; right; exact INP)) as [E|D]; [|exact D].
exfalso. pose proof (proj1 (Forall_forall _ _) EF z Hz) as (_ & SZ & _). rewrite E in SZ. cbn [snd] in SZ. unfold kPrimResvSize in SZ. lia.
- destruct (pairwise_zdisjoint_In _ _ _ PD ltac:(apply in_app_iff; left; exact Hz) ltac:(apply in_app_iff; right; exact INP)) as [E|D]; [left; exact E | right; exact D].
Qed.
Lemma ALedger_user_place_piece :
~ In (offU, n) (rg_holes r) ->
region_free (vm_reserved (m_vmmaps md)) (w64 addrU) (w64 n) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 addrU) (w64 n) = true.
Proof.
intros Hn. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof prim_bounds as (B1 & B2 & B3 & B4 & B5). pose proof prim_hi as [C1 C2].
assert (R : ly_prim ly <= addrU /\ addrU + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= addrU /\ addrU + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2. unfold addrU, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
split.
- rewrite L3. apply (region_free_reserved segs); [exact al_img_env' | exact R3 | unfold kUserMapSize; lia | lia].
- destruct L4 as (pieces & (P1 & P2 & P3) & P4).
destruct (proj1 (Exists_exists _ _) (proj2 (P3 addrU ltac:(unfold kUserMapSize in *; lia)) (no_hole_in_range Hn addrU ltac:(unfold kUserMapSize; lia)))) as (P0 & HP & Hin).
pose proof (proj1 (Forall_forall _ _) P1 P0 HP) as (Q0 & _ & QE). pose proof (no_cut_inside _ QE) as NC. unfold in_zr in Hin.
destruct (proj1 (P4 P0) HP) as (V0 & _ & Q3 & Q4).
unfold map_contains. apply (proj2 (existsb_exists _ _)). exists (wiv P0). split; [exact V0|].
unfold wiv. cbn [fst snd]. rewrite !w64_unsigned by (clear - Q0 Q3 Q4 C1 C2 B1 R1 R2 R4 Hin; unfold kHighMemBeg, kUserMapSize in *; lia).
apply andb_true_intro. split; apply Z.leb_le; unfold kUserMapSize in *; lia.
Qed.
Lemma ALedger_user_place_hole :
In (offU, n) (rg_holes r) -> sec_placed ly S ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < uw (snd e)) ->
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 addrU) (w64 n) = true.
Proof.
intros Hh PL NZ. pose proof (zones_vs_prim PL) as ZP. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof prim_bounds as (B1 & B2 & B3 & B4 & B5). pose proof prim_hi as [C1 C2].
assert (R : ly_prim ly <= addrU /\ addrU + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= addrU /\ addrU + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2. unfold addrU, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
rewrite region_free_app. apply andb_true_intro. split; [rewrite L3; apply (region_free_reserved segs); [exact al_img_env' | exact R3 | unfold kUserMapSize; lia | lia]|].
apply region_free_intro. intros e He. pose proof (L8 e He) as X. apply Exists_exists in X as (z & Hz & Z1 & Z2).
pose proof (NZ e He) as Pe. pose proof (uw_range (fst e)) as U1. pose proof (uw_range (snd e)) as U2. unfold uw in *.
rewrite !w64_unsigned by (clear - R1 R2 R4 B1; unfold kHighMemBeg, kUserMapSize in *; lia).
destruct (ZP z Hz) as [->|D].
-
cbn [fst snd] in Z1, Z2. destruct L4 as (pieces & (P1 & P2 & P3) & P4).
assert (HP : In (wz e) pieces).
{ apply (proj2 (P4 (wz e))). rewrite wiv_wz. unfold wz, uw. cbn [fst snd]. repeat split; [exact He | lia | lia | lia]. }
destruct (Z_lt_le_dec addrU (bv_unsigned (fst e) + bv_unsigned (snd e))) as [Y|Y]; [|left; exact Y].
destruct (Z_lt_le_dec (bv_unsigned (fst e)) (addrU + n)) as [Y'|Y']; [|right; exact Y']. exfalso.
set (a := Z.max addrU (bv_unsigned (fst e))).
assert (Ha1 : in_zr a (wz e)) by (unfold in_zr, wz, uw; cbn [fst snd]; lia).
assert (Ha2 : addrU <= a < addrU + n) by (unfold kUserMapSize in *; lia).
apply (proj1 (P3 a ltac:(lia)) (proj2 (Exists_exists _ _) (ex_intro _ (wz e) (conj HP Ha1)))).
exists c, (offU, n). split; [exact Hc|]. split; [exact Hh|]. unfold in_zr, addrU in Ha2 |- *. cbn [fst snd]. exact Ha2.
-
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma ALedger_kept : vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) -> eager_used md' <= eager_used md -> ALedger segs ly S md'.
Proof. intros VM EG. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15]. constructor; rewrite ?RES, ?LIM, ?VM, ?TOPeq; try assumption; try (destruct L15 as [N1 N2]; split; apply NAF; assumption). rewrite esec_K3. lia. Qed.
Hypothesis HFA : rg_mapped_fa r + n <= kFreeArrayMax.
Definition offF : Z := kFreeArrayOffset + rg_mapped_fa r.
Definition addrF : Z := region_base ly c + offF.
Definition rFp : region := mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r + n) (rg_free r) (del_hole offF (rg_holes r)).
Definition rFm : region := mkRegion (rg_mapped_user r) (rg_alloc_user r) (rg_mapped_fa r) (rg_free r) (add_hole (offF, n) (rg_holes r)).
Definition SFp : astate := upd_reg c rFp S.
Definition SFm : astate := upd_reg c rFm S.
Lemma filter_holes_idF : ~ In (offF, n) (rg_holes r) -> List.filter (fun h' => negb (fst h' =? offF)) (rg_holes r) = rg_holes r.
Proof.
intros Hn. pose proof mu_fa_facts as (M1 & _ & M3 & _).
assert (A : forall h, In h (rg_holes r) -> fst h <> offF).
{ intros h Hh E. destruct (holes_shape h Hh) as [[-> _]|[-> _]]; cbn in E; [unfold offF, kFreeArrayOffset, kUserMapSize, EV_MAX in *; lia|]. exact (Hn Hh). }
induction (rg_holes r) as [|h t IH]; [reflexivity|]. cbn. destruct (Z.eqb_spec (fst h) offF) as [E|NE]; [exfalso; exact (A h (or_introl eq_refl) E)|].
cbn. f_equal. apply IH; [intros Hin; apply Hn; right; exact Hin | intros h' Hh'; apply A; right; exact Hh'].
Qed.
Lemma prim_hole_at_sameF : forall S', (forall c', 1 <= c' <= 31 -> rg_holes (reg S' c') = rg_holes (reg S c')) ->
forall a, prim_hole_at ly S' a <-> prim_hole_at ly S a.
Proof.
intros S' H a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hh & Ha); exists c', h; [rewrite H in Hh by lia | rewrite <- H in Hh by lia]; auto.
Qed.
Lemma cut_ok_monoF : forall S', (forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg S' c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg S' c')) ->
forall x, cut_ok ly S x -> cut_ok ly S' x.
Proof.
intros S' H x [X|[X|(c' & Hc' & [(k & E & B)|(k & E & B)])]]; [left; exact X | right; left; exact X | |]; right; right; exists c'; split; [exact Hc'| |exact Hc'|];
destruct (H c' Hc') as [H1 H2]; [left | right]; exists k; split; [exact E | lia | exact E | lia].
Qed.
Lemma ALedger_fa_granted_piece :
~ In (offF, n) (rg_holes r) ->
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
ALedger segs ly SFp md'.
Proof.
intros Hn VM EG. pose proof (filter_holes_idF Hn) as FH. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
assert (HOLES : forall c', 1 <= c' <= 31 -> rg_holes (reg SFp c') = rg_holes (reg S c')).
{ intros c' Hc'. unfold SFp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn; unfold del_hole; exact FH | rewrite reg_upd_ne by lia; reflexivity]. }
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg SFp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg SFp c')).
{ intros c' Hc'. unfold SFp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn [rg_mapped_user rg_mapped_fa rFp]; unfold offF, kUserMapSize; lia | rewrite reg_upd_ne by lia; lia]. }
constructor; rewrite ?RES, ?LIM, ?VM, ?TOPeq, ?sec_extents_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
- destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists pieces. split; [split; [|split; [exact P2|]]|exact P4].
+ eapply Forall_impl; [|exact P1]. intros p (A & B & C). split; [exact A|]. split; apply (cut_ok_monoF SFp MONO); assumption.
+ intros a Ha. rewrite (P3 a Ha). rewrite (prim_hole_at_sameF SFp HOLES a). tauto.
- unfold SFp. rewrite ?sec_extents_upd, esec_K3, sec_reserved_upd, prim_committed_upd. cbn [rg_mapped_user rg_mapped_fa rFp]. unfold offF, kUserMapSize in *. lia.
Qed.
Lemma prim_boundsF : kHighMemBeg <= ly_prim ly /\ ly_prim ly <= region_base ly c /\ addrF + n <= region_base ly c + kFreeArrayOffset + kFreeArrayMax /\
region_base ly c + kFreeArrayOffset + kFreeArrayMax <= ly_prim ly + kPrimResvSize /\ kFreeArrayOffset <= offF.
Proof.
pose proof mu_fa_facts as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2].
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
pose proof HFA as HF. unfold addrF, offF, region_base in *. rewrite region_off_eq by lia.
unfold kFreeArrayOffset, kFreeArrayMax, kPrimResvSize, kSpaceSize, kUserMapSize, EV_MAX in *. repeat split; try lia; nia.
Qed.
Lemma prim_hiF : ly_prim ly + kPrimResvSize <= ASAN_CEIL /\ ASAN_CEIL < 2 ^ 63.
Proof.
pose proof (lo_high ly LO) as HP. unfold in_high in HP.
ceil; unfold ASAN_CEIL in *. split; lia.
Qed.
Lemma ALedger_fa_granted_hole :
In (offF, n) (rg_holes r) ->
vm_maps (m_vmmaps md') = wiv (addrF, n) :: vm_maps (m_vmmaps md) ->
eager_used md' <= eager_used md + n ->
ALedger segs ly SFp md'.
Proof.
intros Hh VM EG. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15]. pose proof prim_boundsF as (B1 & B2 & B3 & B4 & B5).
pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
assert (HOLESc : rg_holes (reg SFp c) = del_hole offF (rg_holes r)) by (unfold SFp; rewrite reg_upd; reflexivity).
assert (HOLESo : forall c', 1 <= c' <= 31 -> c' <> c -> rg_holes (reg SFp c') = rg_holes (reg S c')) by (intros c' Hc' NE; unfold SFp; rewrite reg_upd_ne by lia; reflexivity).
assert (MONO : forall c', 1 <= c' <= 31 -> rg_mapped_user (reg S c') <= rg_mapped_user (reg SFp c') /\ rg_mapped_fa (reg S c') <= rg_mapped_fa (reg SFp c')).
{ intros c' Hc'. unfold SFp. destruct (Z.eq_dec c' c) as [->|NE]; [rewrite reg_upd; cbn [rg_mapped_user rg_mapped_fa rFp]; unfold offF, kUserMapSize; lia | rewrite reg_upd_ne by lia; lia]. }
assert (HOLE' : forall a, prim_hole_at ly SFp a <-> prim_hole_at ly S a /\ ~ in_zr a (addrF, n)).
{ intros a. unfold prim_hole_at. split.
- intros (c' & h & Hc' & Hin & Ha). destruct (Z.eq_dec c' c) as [->|NE].
+ rewrite HOLESc in Hin. unfold del_hole in Hin. apply filter_In in Hin as [Hin Hne]. apply negb_true_iff in Hne. apply Z.eqb_neq in Hne.
split; [exists c, h; auto|]. intros X. destruct (holes_shape h Hin) as [[-> UB]|[-> _]]; cbn in Hne; [| exfalso; apply Hne; reflexivity].
unfold in_zr, addrF, offF in Ha, X. cbn [fst snd] in Ha, X. unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, EV_MAX in *. lia.
+ rewrite HOLESo in Hin by lia. split; [exists c', h; auto|]. intros X.
pose proof (holes_shape_any c' h Hc' Hin) as SH.
pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'.
pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as AL'.
unfold in_zr, addrF, offF, region_base in Ha, X. cbn [fst snd] in Ha, X. rewrite !region_off_eq in Ha, X by lia.
destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Ha; unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *;
clear - Ha X NE MB' FB' F0' M1 M3 HFA Hc Hc' SL' AL' SB; lia.
- intros ((c' & h & Hc' & Hin & Ha) & NX). destruct (Z.eq_dec c' c) as [->|NE].
+ exists c, h. rewrite HOLESc. split; [lia|]. split; [|exact Ha]. unfold del_hole. apply filter_In. split; [exact Hin|].
apply negb_true_iff, Z.eqb_neq. intros E. apply NX. destruct (holes_shape h Hin) as [[-> _]|[-> _]]; cbn in E.
* exfalso. unfold offF, kFreeArrayOffset, kUserMapSize, EV_MAX in *. lia.
* unfold in_zr, addrF, offF in Ha |- *. cbn [fst snd] in Ha |- *. unfold kUserMapSize, kFreeArrayMapSize in *. lia.
+ exists c', h. rewrite HOLESo by lia. auto. }
constructor; rewrite ?RES, ?LIM, ?VM, ?TOPeq, ?sec_extents_upd; try assumption; try (intros zz Hzz; first [exact (L10 zz Hzz) | right; exact (L10 zz Hzz)]); try (intros zz Hzz; first [exact (L11 zz Hzz) | right; exact (L11 zz Hzz)]); try (destruct L15 as [N1 N2]; split; apply NAF; assumption).
-
destruct L4 as (pieces & (P1 & P2 & P3) & P4). exists ((addrF, n) :: pieces). split; [split; [|split]|].
+ apply Forall_cons; [|eapply Forall_impl; [|exact P1]; intros p (A & B & C); split; [exact A|]; split; apply (cut_ok_monoF SFp MONO); assumption].
cbn [fst snd]. split; [unfold kUserMapSize; lia|].
pose proof (Z.div_exact (rg_mapped_fa r) 262144 ltac:(lia)) as DX. unfold kFreeArrayMapSize in M4.
split; (right; right; exists c; split; [exact Hc|]; right); [exists (rg_mapped_fa r / kFreeArrayMapSize) | exists (rg_mapped_fa r / kFreeArrayMapSize + 1)];
unfold addrF, SFp, fa_base, region_base; rewrite reg_upd; cbn [rg_mapped_fa rFp]; unfold offF, kUserMapSize, kFreeArrayMapSize in *; split; lia.
+
cbn. split; [|exact P2]. apply Forall_forall. intros p Hp. unfold zdisjoint. cbn [fst snd].
destruct (Z_lt_le_dec (fst p) (addrF + n)) as [X1|X1]; [|left; lia]. destruct (Z_lt_le_dec addrF (fst p + snd p)) as [X2|X2]; [|right; lia]. exfalso.
destruct (proj1 (P4 p) Hp) as (_ & Q0 & Q1 & Q2).
assert (HA : exists a, in_zr a p /\ addrF <= a < addrF + n).
{ destruct (Z_lt_le_dec addrF (fst p)); [exists (fst p) | exists addrF]; unfold in_zr, kUserMapSize in *; split; lia. }
destruct HA as (a & Ha1 & Ha2).
apply (proj1 (P3 a ltac:(clear - Ha2 B2 B3 B4 B5; unfold addrF, offF, kUserMapSize, kFreeArrayMax, kFreeArrayOffset in *; lia)) (proj2 (Exists_exists _ _) (ex_intro _ p (conj Hp Ha1)))).
exists c, (offF, n). split; [exact Hc|]. split; [exact Hh|]. unfold in_zr, addrF in Ha2 |- *. cbn [fst snd]. exact Ha2.
+ intros a Ha. rewrite (HOLE' a). split.
* intros HE [Hh' NX]. apply Exists_cons in HE as [HE|HE]; [exact (NX HE)|]. exact (proj1 (P3 a Ha) HE Hh').
* intros NH. destruct (Z_lt_le_dec a addrF) as [Y1|Y1]; [|destruct (Z_lt_le_dec a (addrF + n)) as [Y2|Y2]; [apply Exists_cons_hd; unfold in_zr; cbn; lia|]];
apply Exists_cons_tl; apply (proj2 (P3 a Ha)); intros Hh'; apply NH; split; [exact Hh' | unfold in_zr; cbn [fst snd]; lia | exact Hh' | unfold in_zr; cbn [fst snd]; lia].
+ intros p. cbn. rewrite (P4 p). unfold wiv. cbn [fst snd]. split.
* intros [<-|(I1 & I2 & I3 & I4)]; [|auto]. cbn [fst snd]. split; [left; reflexivity|]. split; [unfold kUserMapSize; lia|]. clear - B2 B3 B4 B5; unfold addrF, offF, kUserMapSize, kFreeArrayMax, kFreeArrayOffset in *; lia.
* intros ([E|I1] & I2 & I3 & I4); [|right; auto]. left.
destruct p as [b l]. unfold wiv in E. cbn [fst snd] in E, I2, I3, I4.
pose proof prim_hiF as [C1 C2]. pose proof prim_boundsF as (D1 & D2 & D3 & D4 & D5).
pose proof (f_equal (fun x => bv_unsigned (fst x)) E) as U1. pose proof (f_equal (fun x => bv_unsigned (snd x)) E) as U2. cbn [fst snd] in U1, U2.
rewrite !w64_unsigned in U1 by (clear - C1 C2 D1 D2 D3 D4 D5 I2 I3 I4; unfold addrF, offF, kHighMemBeg, kPrimResvSize, kUserMapSize, kFreeArrayOffset, kFreeArrayMax in *; lia).
rewrite !w64_unsigned in U2 by (clear - C1 C2 D1 D2 D3 D4 D5 I2 I3 I4; unfold kHighMemBeg, kPrimResvSize, kUserMapSize in *; lia). rewrite U1, U2. reflexivity.
- right. exact L5.
- right. exact L6.
- intros e He. right. exact (L7 e He).
- intros e He. destruct He as [<-|He]; [|exact (L8 e He)].
apply Exists_exists. exists (ly_prim ly, kPrimResvSize). split.
+ unfold lazy_zones. apply in_or_app. left. cbn. do 4 right. left. reflexivity.
+ pose proof prim_hiF as [C1 C2]. unfold wiv. cbn [fst snd].
rewrite !w64_unsigned by (clear - C1 C2 B1 B2 B3 B4 B5; unfold addrF, offF, kHighMemBeg, kPrimResvSize, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *; lia).
clear - C1 C2 B1 B2 B3 B4 B5. unfold addrF, offF, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia.
- unfold SFp. rewrite ?sec_extents_upd, esec_K3, sec_reserved_upd, prim_committed_upd. cbn [rg_mapped_user rg_mapped_fa rFp]. unfold offF, kUserMapSize in *. lia.
Qed.
Lemma maps_subtract_InF : forall l lo hi x, In x (maps_subtract l lo hi) <-> exists e, In e l /\ In x (iv_subtract (fst e) (snd e) lo hi).
Proof.
induction l as [|[a sz] t IH]; intros lo hi x; cbn.
- split; [intros [] | intros (e & [] & _)].
- rewrite in_app_iff, IH. split.
+ intros [H|(e & He & Hx)]; [exists (a, sz); auto | exists e; auto].
+ intros (e & [<-|He] & Hx); [left; exact Hx | right; exists e; auto].
Qed.
Lemma no_cut_insideF : forall x, cut_ok ly S x -> ~ (addrF < x < addrF + n).
Proof.
intros x CX HX. pose proof prim_boundsF as (B1 & B2 & B3 & B4 & B5). pose proof mu_fa_facts as (M1 & M2 & M3 & M4). pose proof (lo_space_in ly LO) as [S1 S2]. pose proof HFA as HF.
unfold addrF, offF, region_base in HX, B2, B3, B4. rewrite region_off_eq in HX, B2, B3, B4 by lia.
destruct CX as [->|[->|(c' & Hc' & [(k & -> & Bk)|(k & -> & Bk)])]]; unfold region_base, fa_base in *; rewrite ?region_off_eq in HX by lia; try rewrite ?region_off_eq in Bk by lia.
- unfold kUserMapSize, kFreeArrayOffset in *. lia.
- unfold kUserMapSize, kPrimResvSize, kSpaceSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
- pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
unfold kUserMapSize, kFreeArrayOffset, kFreeArrayMax, EV_MAX in *. lia.
- pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'. pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'.
destruct (Z.eq_dec c' c) as [->|NE].
+
apply Z.mod_divide in M4 as [q Hq]; [|unfold kFreeArrayMapSize; lia]. unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax in *. lia.
+ unfold kUserMapSize, kFreeArrayMapSize, kFreeArrayOffset, kFreeArrayMax, EV_MAX in *. lia.
Qed.
Lemma no_hole_in_rangeF : ~ In (offF, n) (rg_holes r) -> forall a, addrF <= a < addrF + n -> ~ prim_hole_at ly S a.
Proof.
intros Hn a Ha (c' & h & Hc' & Hin & Hx). pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
pose proof (holes_shape_any c' h Hc' Hin) as SH.
pose proof (mapped_user_bound U pp cc bb S c' W Hc') as MB'. pose proof (wr_fa_bound _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as FB'.
pose proof (proj1 (wr_fa _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc'))) as F0'. pose proof (wf_slack _ _ _ _ _ W) as SL'.
pose proof (wr_alloc _ _ _ _ _ _ (wf_classes _ _ _ _ _ W c' Hc')) as AL'.
unfold in_zr, addrF, offF, region_base in Ha, Hx. cbn [fst snd] in Hx. rewrite !region_off_eq in Ha, Hx by lia.
destruct (Z.eq_dec c' c) as [->|NE].
- destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Hx; [|exact (Hn Hin)]. unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *. lia.
- destruct SH as [[-> SB]|[-> SB]]; cbn [fst snd] in Hx; unfold kFreeArrayOffset, kUserMapSize, kFreeArrayMapSize, kFreeArrayMax, EV_MAX in *;
clear - Ha Hx NE MB' FB' F0' M1 M3 HFA Hc Hc' SL' AL' SB; lia.
Qed.
Lemma pairwise_zdisjoint_InF : forall l x y, pairwise zdisjoint l -> In x l -> In y l -> x = y \/ zdisjoint x y.
Proof.
induction l as [|h t IH]; intros x y P Hx Hy; [destruct Hx|]. cbn in P. destruct P as [F P].
destruct Hx as [<-|Hx], Hy as [<-|Hy]; [left; reflexivity | right; exact (proj1 (Forall_forall _ _) F y Hy) | |].
- right. pose proof (proj1 (Forall_forall _ _) F x Hx) as D. unfold zdisjoint in *. lia.
- exact (IH x y P Hx Hy).
Qed.
Lemma pairwise_filterF : forall (f : Z * Z -> bool) l, pairwise zdisjoint l -> pairwise zdisjoint (List.filter f l).
Proof.
induction l as [|h t IH]; intros P; cbn; [exact I|]. destruct P as [F P]. destruct (f h); cbn; [|exact (IH P)].
split; [|exact (IH P)]. apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) F y Hy).
Qed.
Lemma ALedger_fa_place_piece :
~ In (offF, n) (rg_holes r) ->
region_free (vm_reserved (m_vmmaps md)) (w64 addrF) (w64 n) = true /\
map_contains (vm_maps (m_vmmaps md)) (w64 addrF) (w64 n) = true.
Proof.
intros Hn. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof prim_boundsF as (B1 & B2 & B3 & B4 & B5). pose proof prim_hiF as [C1 C2]. pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
assert (R : ly_prim ly <= addrF /\ addrF + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= addrF /\ addrF + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2 M3. unfold addrF, offF, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
split.
- rewrite L3. apply (region_free_reserved segs); [exact al_img_env' | exact R3 | unfold kUserMapSize; lia | lia].
- destruct L4 as (pieces & (P1 & P2 & P3) & P4).
destruct (proj1 (Exists_exists _ _) (proj2 (P3 addrF ltac:(unfold kUserMapSize in *; lia)) (no_hole_in_rangeF Hn addrF ltac:(unfold kUserMapSize; lia)))) as (P0 & HP & Hin).
pose proof (proj1 (Forall_forall _ _) P1 P0 HP) as (Q0 & _ & QE). pose proof (no_cut_insideF _ QE) as NC. unfold in_zr in Hin.
destruct (proj1 (P4 P0) HP) as (V0 & _ & Q3 & Q4).
unfold map_contains. apply (proj2 (existsb_exists _ _)). exists (wiv P0). split; [exact V0|].
unfold wiv. cbn [fst snd]. rewrite !w64_unsigned by (clear - Q0 Q3 Q4 C1 C2 B1 R1 R2 R4 Hin; unfold kHighMemBeg, kUserMapSize in *; lia).
apply andb_true_intro. split; apply Z.leb_le; unfold kUserMapSize in *; lia.
Qed.
Lemma ALedger_fa_place_hole :
In (offF, n) (rg_holes r) -> sec_placed ly S ->
(forall e, In e (vm_maps (m_vmmaps md)) -> 0 < uw (snd e)) ->
region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 addrF) (w64 n) = true.
Proof.
intros Hh PL NZ. pose proof (zones_vs_prim PL) as ZP. destruct L as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13 L14 L15].
pose proof prim_boundsF as (B1 & B2 & B3 & B4 & B5). pose proof prim_hiF as [C1 C2]. pose proof mu_fa_facts as (M1 & M2 & M3 & M4).
assert (R : ly_prim ly <= addrF /\ addrF + n <= ly_prim ly + kPrimResvSize /\ kImgEnd + 4096 <= addrF /\ addrF + n < 2 ^ 63).
{ clear - B1 B2 B3 B4 B5 C1 C2 M3. unfold addrF, offF, kHighMemBeg, kImgEnd, kFreeArrayOffset, kFreeArrayMax, kUserMapSize in *. lia. }
destruct R as (R1 & R2 & R3 & R4).
rewrite region_free_app. apply andb_true_intro. split; [rewrite L3; apply (region_free_reserved segs); [exact al_img_env' | exact R3 | unfold kUserMapSize; lia | lia]|].
apply region_free_intro. intros e He. pose proof (L8 e He) as X. apply Exists_exists in X as (z & Hz & Z1 & Z2).
pose proof (NZ e He) as Pe. pose proof (uw_range (fst e)) as U1. pose proof (uw_range (snd e)) as U2. unfold uw in *.
rewrite !w64_unsigned by (clear - R1 R2 R4 B1; unfold kHighMemBeg, kUserMapSize in *; lia).
destruct (ZP z Hz) as [->|D].
- cbn [fst snd] in Z1, Z2. destruct L4 as (pieces & (P1 & P2 & P3) & P4).
assert (HP : In (wz e) pieces).
{ apply (proj2 (P4 (wz e))). rewrite wiv_wz. unfold wz, uw. cbn [fst snd]. repeat split; [exact He | lia | lia | lia]. }
destruct (Z_lt_le_dec addrF (bv_unsigned (fst e) + bv_unsigned (snd e))) as [Y|Y]; [|left; exact Y].
destruct (Z_lt_le_dec (bv_unsigned (fst e)) (addrF + n)) as [Y'|Y']; [|right; exact Y']. exfalso.
set (a := Z.max addrF (bv_unsigned (fst e))).
assert (Ha1 : in_zr a (wz e)) by (unfold in_zr, wz, uw; cbn [fst snd]; lia).
assert (Ha2 : addrF <= a < addrF + n) by (unfold kUserMapSize in *; lia).
apply (proj1 (P3 a ltac:(lia)) (proj2 (Exists_exists _ _) (ex_intro _ (wz e) (conj HP Ha1)))).
exists c, (offF, n). split; [exact Hc|]. split; [exact Hh|]. unfold in_zr, addrF in Ha2 |- *. cbn [fst snd]. exact Ha2.
- unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
End K3.
End d.
