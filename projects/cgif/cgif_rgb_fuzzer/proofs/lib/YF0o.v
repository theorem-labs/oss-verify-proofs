(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0s YK0j YQ0j YQ0c YQ0b YQ0i YQ09 YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG06 YG03 YG0h YG10 YG0u YG0d YG0m.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Lemma amrealE_then_SRr {imgk : img} {R} : forall (t : itree astate R) W c (P Q : R -> world tfxsegs -> config -> Prop),
amrealE tfxsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfxsegs W' c' (Q r)) -> amrealE tfxsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [amrealE] in *.
- eapply SRrF_bind; [img_try (img_exact H)|]. intros W' c' _ HP. img_exact (SRr_F _ _ _ _ (HPQ r W' c' HP)).
- eapply SRrF_mono; [img_try (img_exact H)|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists J, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; eapply IH; [img_try (img_exact (H8 i Hi)) | img_try (img_exact HPQ)]).
destruct Hk as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact HR) | img_try (img_exact HPQ)].
- img_exact H.
- img_exact I.
Qed.
Lemma amreal_then_SRr {imgk : img} {R} : forall (t : itree astate R) W c (P Q : R -> world tfxsegs -> config -> Prop),
amreal tfxsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfxsegs W' c' (Q r)) -> amreal tfxsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [amreal] in *.
- eapply SRr_bind; [img_try (img_exact H)|]. intros W' c' _ HP. img_exact (HPQ r W' c' HP).
- eapply SRr_mono; [img_try (img_exact H)|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hd & H8); exists J, nx, bit, sp, i0;
repeat (split; [img_try (assumption)|]); intros i Hi; specialize (H8 i Hi); destruct (Z.eqb (bit i) 1);
[eapply IH; [img_try (img_exact H8) | img_try (img_exact HPQ)] | eapply amrealE_then_SRr; [img_try (img_exact H8) | img_try (img_exact HPQ)]]).
destruct Hk as (z & Hz & HR). exists z. split; [img_try (img_exact Hz)|]. eapply IH; [img_try (img_exact HR) | img_try (img_exact HPQ)].
- img_exact H.
- img_exact I.
Qed.
Lemma kept_of_aview2 {imgk : img} : forall (E : env) (H H' : word -> bool) (m m' : word -> option byte) r,
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
aview tfxsegs H' m' a = aview tfxsegs H m a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
aview tfxsegs H' m' a = aview tfxsegs H m a /\ TFX_IMG_END <= a < 2 ^ 64) ->
region_kept tfxsegs E (mrestrict H m) (mrestrict H' m') r.
Proof.
intros E H H' m m' r Hext Hwin. split.
- intros a Ha. pose proof (Hext a Ha) as EQ. unfold aview in EQ.
destruct (mbyte tfxsegs (mrestrict H' m') a) as [b'|], (mbyte tfxsegs (mrestrict H m) a) as [b|]; cbn in EQ; try discriminate; [|img_refl].
injection EQ as EQ. f_equal. img_apply bv_eq. img_exact EQ.
- intros a Ha Hw. destruct (Hwin a Ha) as [EQ Hh]. img_apply apresent_writable; [img_try (img_exact Hh)|].
pose proof (writable_high_apresent H m a Hh Hw) as P. apply apresent_mbyte in P as [b Hb].
assert (A : aview tfxsegs H m a = Some (bv_unsigned b)) by (img_try (unfold aview; rewrite Hb; img_refl)).
rewrite <- EQ in A. apply aview_some in A as (b' & Hb' & _). img_exact (mbyte_high_apresent H' m' a b' Hh Hb').
Qed.
Fixpoint smem_upd (rs : smem) (i : nat) (r' : YQ0b.region) : smem :=
match rs, i with
| [], _ => []
| _ :: t, O => r' :: t
| r :: t, S j => r :: smem_upd t j r'
end.
Definition same_frame (r r' : YQ0b.region) : Prop :=
YQ0b.r_base r' = YQ0b.r_base r /\ YQ0b.r_lo r' = YQ0b.r_lo r /\ YQ0b.r_hi r' = YQ0b.r_hi r /\
YQ0b.r_wlo r' = YQ0b.r_wlo r /\ YQ0b.r_whi r' = YQ0b.r_whi r.
Lemma smem_upd_nth : forall rs i r r', nth_error rs i = Some r ->
exists l1 l2, rs = l1 ++ r :: l2 /\ smem_upd rs i r' = l1 ++ r' :: l2.
Proof.
induction rs as [|x t IH]; intros i r r' H; [img_try (destruct i; discriminate)|].
destruct i as [|j]; cbn in H |- *.
- injection H as ->. exists [], t. split; img_refl.
- destruct (IH j r r' H) as (l1 & l2 & -> & ->). exists (x :: l1), l2. split; img_refl.
Qed.
Lemma all_disjoint_app : forall E r l1 l2, YQ0b.all_disjoint E r (l1 ++ l2) <-> YQ0b.all_disjoint E r l1 /\ YQ0b.all_disjoint E r l2.
Proof. intros E r l1 l2. induction l1 as [|x t IH]; cbn; tauto. Qed.

Lemma pairwise_disjoint_upd : forall E l1 r r' l2, same_frame r r' ->
YQ0b.pairwise_disjoint E (l1 ++ r :: l2) -> YQ0b.pairwise_disjoint E (l1 ++ r' :: l2).
Proof.
intros E l1 r r' l2 SF. induction l1 as [|x t IH]; cbn; intros [A P].
- split; [|img_try (img_exact P)]. destruct SF as (B & L & Hh & _ & _).
clear P. induction l2 as [|y u IH2]; cbn in A |- *; [img_try (img_exact I)|]. destruct A as [A1 A2]. split; [|img_try (img_exact (IH2 A2))].
unfold YQ0b.extent_disjoint in *. rewrite B, L, Hh. img_exact A1.
- split; [|img_try (img_exact (IH P))]. apply all_disjoint_app in A as [A1 A2]. img_apply all_disjoint_app. split; [img_try (img_exact A1)|]. cbn in A2 |- *.
destruct A2 as [A3 A4]. split; [|img_try (img_exact A4)]. destruct SF as (B & L & Hh & _ & _). unfold YQ0b.extent_disjoint in *. rewrite B, L, Hh. img_exact A3.
Qed.
Lemma regions_wf_app : forall l1 l2, YQ0b.regions_wf (l1 ++ l2) = (YQ0b.regions_wf l1 && YQ0b.regions_wf l2)%bool.
Proof. intros l1 l2. induction l1 as [|x t IH]; cbn; [img_refl|]. rewrite IH, Bool.andb_assoc. img_refl. Qed.
Lemma st_ok_set_region {imgk : img} : forall E ss ms i r r',
YQ0i.st_ok tfxsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> same_frame r r' -> YQ0b.region_wf r' = true ->
Forall (YQ0b.chunk_ok tfxsegs E (ms_mem ms) (base_val E (YQ0b.r_base r'))) (YQ0b.r_chunks r') ->
YQ0i.st_ok tfxsegs E (mkSS (ss_pc ss) (ss_regs ss) (smem_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r r' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Wf & O & D) & H9) Hi SF Hwf Hcs.
destruct (smem_upd_nth _ _ _ r' Hi) as (l1 & l2 & El & ->). rewrite El in Wf, O, D.
unfold YQ0i.st_ok; cbn. repeat (split; [img_try (assumption)|]). split; [|img_try (img_exact H9)]. split; [|img_try (split)].
- rewrite regions_wf_app in Wf |- *. cbn in Wf |- *. rewrite Hwf. apply andb_prop in Wf as [A Bc]. apply andb_prop in Bc as [_ C]. rewrite A, C. img_refl.
- apply Forall_app in O as [O1 O2]. inversion O2 as [|x t Or Ot]; (subst; cbv beta). img_apply Forall_app. split; [img_try (img_exact O1)|]. constructor; [|img_try (img_exact Ot)].
destruct Or as (Q1 & Q2 & Q3 & _). destruct SF as (B & L & Hh & Wl & Wh). unfold YQ0b.region_ok. rewrite B, L, Hh, Wl, Wh.
split; [img_try (img_exact Q1)|]. split; [img_try (img_exact Q2)|]. split; [img_try (img_exact Q3)|]. rewrite <- B. img_exact Hcs.
- img_exact (pairwise_disjoint_upd E l1 r r' l2 SF D).
Qed.
Lemma chunk_ok_zero_mb {imgk : img} : forall E m base off len,
(forall i, 0 <= i < len -> mbyte tfxsegs m (base + off + i) = Some (Z_to_bv 8 0)) ->
YQ0b.chunk_ok tfxsegs E m base (YQ0b.mkChunk off (CZero len)).
Proof.
intros E m base off len H i Hi. cbn [YQ0b.c_off YQ0b.c_val YQ0b.c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [img_refl|]. img_exact (H i Hi).
Qed.
Lemma val_mem4_bytes {imgk : img} : forall m a v, val_mem tfxsegs m a 4 v <->
(mbyte tfxsegs m a = Some (Z_to_bv 8 (YP0g.le_byte v 4 0)) /\ mbyte tfxsegs m (a + 1) = Some (Z_to_bv 8 (YP0g.le_byte v 4 1)) /\
mbyte tfxsegs m (a + 2) = Some (Z_to_bv 8 (YP0g.le_byte v 4 2)) /\ mbyte tfxsegs m (a + 3) = Some (Z_to_bv 8 (YP0g.le_byte v 4 3))).
Proof.
intros m a v. unfold val_mem. split.
- intros H. pose proof (H 0%nat ltac:(img_lia)) as H0. pose proof (H 1%nat ltac:(img_lia)) as H1. pose proof (H 2%nat ltac:(img_lia)) as H2. pose proof (H 3%nat ltac:(img_lia)) as H3.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3. rewrite Z.add_0_r in H0. tauto.
- intros (H0 & H1 & H2 & H3) k Hk. destruct k as [|[|[|[|k]]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; [img_try (rewrite Z.add_0_r; img_exact H0) | img_try (img_exact H1) | img_try (img_exact H2) | img_try (img_exact H3) | img_lia].
Qed.
Lemma val_mem1_byte {imgk : img} : forall m a v, val_mem tfxsegs m a 1 v <-> mbyte tfxsegs m a = Some (Z_to_bv 8 (YP0g.le_byte v 1 0)).
Proof.
intros m a v. unfold val_mem. split.
- intros H. pose proof (H 0%nat ltac:(img_lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. img_exact H0.
- intros H0 k Hk. destruct k as [|k]; [img_try (cbn [Z.of_nat]; rewrite Z.add_0_r; img_exact H0) | img_lia].
Qed.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. img_apply bv_eq. rewrite Z_to_bv_unsigned. img_change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. img_change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. img_apply Z.mod_small. img_exact Hv.
Qed.
Lemma bytes3_of {imgk : img} : forall m a (z : byte),
mbyte tfxsegs m (a + 1) = Some z -> mbyte tfxsegs m (a + 2) = Some z -> mbyte tfxsegs m (a + 3) = Some z ->
forall i, 0 <= i < 3 -> mbyte tfxsegs m (0 + (a + 1) + i) = Some z.
Proof.
intros m a z B1 B2 B3 i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2) by img_lia. destruct C as [ -> | [ -> | -> ] ];
[img_try (replace (0 + (a + 1) + 0) with (a + 1) by img_lia) | img_try (replace (0 + (a + 1) + 1) with (a + 2) by img_lia) | img_try (replace (0 + (a + 1) + 2) with (a + 3) by img_lia)]; assumption.
Qed.
Lemma bytes4_of {imgk : img} : forall m a (z : byte),
mbyte tfxsegs m a = Some z -> mbyte tfxsegs m (a + 1) = Some z -> mbyte tfxsegs m (a + 2) = Some z -> mbyte tfxsegs m (a + 3) = Some z ->
forall i, 0 <= i < 4 -> mbyte tfxsegs m (0 + a + i) = Some z.
Proof.
intros m a z B0 B1 B2 B3 i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by img_lia. destruct C as [ -> | [ -> | [ -> | -> ] ] ];
[img_try (replace (0 + a + 0) with a by img_lia) | img_try (replace (0 + a + 1) with (a + 1) by img_lia) | img_try (replace (0 + a + 2) with (a + 2) by img_lia) | img_try (replace (0 + a + 3) with (a + 3) by img_lia)]; assumption.
Qed.
Lemma zcanon_negadd : forall a b, 0 <= b <= a -> a < M64 -> zcanon (zcanon (b * zcanon (-1)) + a) = a - b.
Proof.
intros a b H H2. unfold zcanon. img_change ((-1) mod M64) with (M64 - 1).
rewrite Zplus_mod_idemp_l. replace (b * (M64 - 1) + a) with ((a - b) + b * M64) by img_lia.
unfold M64 in *. rewrite Z_mod_plus_full. img_apply Z.mod_small. img_lia.
Qed.
Definition A_Drain {imgk : img} : Z := (0x33530 + D_150).
Definition A_Recycle {imgk : img} : Z := (0x336d4 + D_150).
Definition A_DoRecycle {imgk : img} : Z := (0x33a3c + D_150).
Definition A_RChunk {imgk : img} : Z := (0x33b74 + D_150).
Definition A_CDealloc {imgk : img} : Z := (0x33f78 + D_150).
Definition A_SDealloc {imgk : img} : Z := (0x34140 + D_150).
Definition A_QUAR {imgk : img} : Z := A_ALLOCATOR + o_quar.
Definition DSTACK : Z := 4096.
Definition transfer_g (X : astate) : qcache :=
mkQC (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X)).
Definition recycle_body (g : qcache) : M unit :=
mcheck (2 * (kBatchBytes * Z.of_nat (length (qc_list g))) <=? qc_bytes g) 209216 ;;
let '(g', popped) := pop_batches 100000%nat g [] in
modify (set_qglobal g') ;;
do_recycle 100000%nat popped.
Definition drain_body (X : astate) : M unit :=
let g := transfer_g X in
put (set_qglobal g (set_qthread qc0 X)) ;;
(if qc_bytes g <=? kQuarantineMax then ret tt else recycle_body g).
Lemma maybe_drain_eq : forall X,
maybe_drain X = if qc_bytes (st_qthread X) <=? kQuarantineCacheMax then ret tt X else drain_body X X.
Proof.
intros X. unfold maybe_drain, drain_body. unfold bind at 1. unfold get. cbn [ibind].
destruct (qc_bytes (st_qthread X) <=? kQuarantineCacheMax); img_refl.
Qed.
Lemma maybe_drain_drain : forall X, kQuarantineCacheMax < qc_bytes (st_qthread X) -> maybe_drain X = drain_body X X.
Proof. intros X H. rewrite maybe_drain_eq. destruct (Z.leb_spec (qc_bytes (st_qthread X)) kQuarantineCacheMax); [img_lia | img_refl]. Qed.
Lemma drain_body_apost : forall U pp cc bb X,
WfP U pp cc bb X -> qloose X   -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
apost (drain_body X X) (fun r => WfP U pp cc bb (snd r) /\ fframe X (snd r) /\
qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd r)) <= Z.max (qc_bytes (st_qglobal X)) kQuarantineMax /\
unq (snd r) = unq X).
Proof.
intros U pp cc bb X W QL HD. rewrite <- (maybe_drain_drain X HD). intros tr r Hp.
assert (REG : st_nev X <= EV_MAX \/ (Z.of_nat (length (st_chunks X)) <= 2 ^ 23 /\ qc_bytes (st_qglobal X) + qc_bytes (st_qthread X) <= 2 ^ 36)).
{ destruct (wf_regime _ _ _ _ _ W) as [Hs|[_ HC]]; [img_try (left; img_exact Hs) | img_try (right)]. pose proof (wf_slack _ _ _ _ _ W) as (_ & C0 & _). destruct QL as (Q1 & Q2 & _). split; img_lia. }
destruct (atok_apath _ true _ tr r (maybe_drain_ok U pp cc bb X true W REG) Hp) as (ns' & A). img_exact A.
Qed.
Lemma aowned_same_cf : forall B ly S1 S2 a, st_chunks S2 = st_chunks S1 -> st_fs S2 = st_fs S1 -> aowned B ly S2 a -> aowned B ly S1 a.
Proof. intros B ly S1 S2 a E1 E2 H. unfold aowned, aclient_byte, sec_extents, frames in *. rewrite E1, E2 in H. img_exact H. Qed.
Section e. Context {imgk : img}.
Variable B : asyms.
Definition drain_pre {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly X W mem md /\
kQuarantineCacheMax < qc_bytes (st_qthread X) /\ qloose X /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - DSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 A_QUAR /\ getr regs 11 = w64 (ly_T ly + t_qc) /\ getr regs 12 = w64 (ly_T ly + t_cache).
Definition drain_leaf {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.
Definition tfx_drain_spec {imgk : img} : Prop :=
forall ly X W regs mem md,
drain_pre ly X W regs mem md ->
amreal tfxsegs (drain_body X X) W (cfg_at tfxsegs A_Drain regs mem md) (drain_leaf ly X W regs mem md).
Definition DRSTACK : Z := 2048.
Definition LFRAME : Z := 80.
Definition plist_cells (tmp : Z) (P : list batch) : list acell :=
qc_cells (ANum tmp) (mkQC P (sum_bytes P)).
Definition dr_pre {imgk : img} (ly : alayout) (X : astate) (P : list batch) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly X W mem md /\
RI (as_universe B) 0 0 0 X P /\ qc_bytes (st_qthread X) = 0 /\ qc_bytes (st_qglobal X) <= kQuarantineMax /\
Forall (cell_holds B ly (aview tfxsegs (w_H W) mem)) (plist_cells (spZ regs) P) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DRSTACK <= spZ regs /\ spZ regs + 32 <= ly_stk_hi ly /\
(forall a, spZ regs - DRSTACK <= a < spZ regs + 32 -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 11 = getr regs 2 /\ getr regs 12 = w64 (ly_T ly + t_cache) /\
Z.of_nat (length P) < 100000 /\ st_cache_inited X = true.
Definition dr_leaf {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B DRSTACK ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32) ly (snd r) W' regs' mem' md' /\
(forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') mem' a).
Definition tfx_dorecycle_spec {imgk : img} : Prop :=
forall ly X P W regs mem md,
dr_pre ly X P W regs mem md ->
amreal tfxsegs (do_recycle 100000%nat P X) W (cfg_at tfxsegs A_DoRecycle regs mem md) (dr_leaf ly X W regs mem md).
Definition KSTACK : Z := 512.
Definition cd_pre {imgk : img} (ly : alayout) (X : astate) (c off : Z) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly X W mem md /\ st_cache_inited X = true /\ 1 <= c <= 30 /\
0 <= off - region_off c < rg_alloc_user (reg X c) /\ (off - region_off c) mod class_size c = 0 /\
~ In (off - region_off c) (class_elems X c) /\
4 * (Z.of_nat (length (class_elems X c)) + 1 + (0 + bslack c 0 + 2 * (EV_MAX - st_nev X))) <= rg_mapped_fa (reg X c) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - KSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 (ly_T ly + t_cache) /\ getr regs 11 = w64 A_ALLOCATOR /\ getr regs 12 = w64 c /\ getr regs 13 = w64 (ly_space ly + off).
Definition puser (ly : alayout) (X : astate) (a : Z) : Prop :=
exists c, 1 <= c <= 31 /\ region_base ly c <= a < region_base ly c + rg_alloc_user (reg X c).
Definition cd_leaf {imgk : img} (ly : alayout) (X : astate) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B KSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a) /\
st_cache_inited (snd r) = true.
Definition tfx_cdealloc_spec {imgk : img} : Prop :=
forall ly X c off W regs mem md,
cd_pre ly X c off W regs mem md ->
amreal tfxsegs (cache_dealloc c off X) W (cfg_at tfxsegs A_CDealloc regs mem md) (cd_leaf ly X W regs mem md).
Definition rcc_pre {imgk : img} (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfxsegs B ly X W mem md /\ st_cache_inited X = true /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK <= spZ regs /\ spZ regs <= cbp /\ cbp + 16 <= ly_stk_hi ly /\ cbp mod 8 = 0 /\
(forall a, spZ regs - KSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\ (forall a, cbp <= a < cbp + 16 -> apresent (w_H W) mem a) /\
val_mem tfxsegs (mrestrict (w_H W) mem) cbp 8 (ly_T ly + t_cache) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 cbp /\ getr regs 11 = w64 (ck_base B ly k + ck_rz k - kChunkHeaderSize).
Definition rcc_leaf {imgk : img} (ly : alayout) (X : astate) (k : chunk) (W : world tfxsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfxsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfxsegs (raZ regs) regs' mem' md' /\
acall_post tfxsegs B KSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
aview tfxsegs (w_H W') mem' a = aview tfxsegs (w_H W) mem a) /\
st_cache_inited (snd r) = true.
Definition tfx_rchunk_spec {imgk : img} : Prop :=
forall ly X k cbp W regs mem md,
rcc_pre ly X k cbp W regs mem md ->
amreal tfxsegs (recycle_chunk k X) W (cfg_at tfxsegs A_RChunk regs mem md) (rcc_leaf ly X k W regs mem md).
End e.
End d.
