(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG06 YG03 YG0f YG0v YG0n YG0d YG0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Lemma amreal_then_SRr {R} : forall (t : itree astate R) W c (P Q : R -> world tfibsegs -> config -> Prop),
amreal tfibsegs t W c P -> (forall r W' c', P r W' c' -> SRr tfibsegs W' c' (Q r)) -> amreal tfibsegs t W c Q.
Proof.
induction t as [r | q s k IH | pc | f]; intros W c P Q H HPQ; cbn [amreal] in *.
- eapply SRr_bind; [exact H|]. intros W' c' _ HP. exact (HPQ r W' c' HP).
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk. destruct q; cbn beta iota in *;
try (destruct Hk as (J & nx & bit & sp & i0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); exists J, nx, bit, sp, i0;
repeat (split; [assumption|]); intros i Hi; eapply IH; [exact (H8 i Hi) | exact HPQ]).
destruct Hk as (z & Hz & HR). exists z. split; [exact Hz|]. eapply IH; [exact HR | exact HPQ].
- exact H.
- exact I.
Qed.
Lemma kept_of_aview2 : forall (E : env) (H H' : word -> bool) (m m' : word -> option byte) r,
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
aview tfibsegs H' m' a = aview tfibsegs H m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
aview tfibsegs H' m' a = aview tfibsegs H m a /\ TFIB_IMG_END <= a < 2 ^ 64) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H' m') r.
Proof.
intros E H H' m m' r Hext Hwin. split.
- intros a Ha. pose proof (Hext a Ha) as EQ. unfold aview in EQ.
destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) a) as [b|]; cbn in EQ; try discriminate; [|reflexivity].
injection EQ as EQ. f_equal. apply bv_eq. exact EQ.
- intros a Ha Hw. destruct (Hwin a Ha) as [EQ Hh]. apply apresent_writable; [exact Hh|].
pose proof (writable_high_apresent H m a Hh Hw) as P. apply apresent_mbyte in P as [b Hb].
assert (A : aview tfibsegs H m a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- EQ in A. apply aview_some in A as (b' & Hb' & _). exact (mbyte_high_apresent H' m' a b' Hh Hb').
Qed.
Fixpoint smem_upd (rs : smem) (i : nat) (r' : YP09.region) : smem :=
match rs, i with
| [], _ => []
| _ :: t, O => r' :: t
| r :: t, S j => r :: smem_upd t j r'
end.
Definition same_frame (r r' : YP09.region) : Prop :=
YP09.r_base r' = YP09.r_base r /\ YP09.r_lo r' = YP09.r_lo r /\ YP09.r_hi r' = YP09.r_hi r /\
YP09.r_wlo r' = YP09.r_wlo r /\ YP09.r_whi r' = YP09.r_whi r.
Lemma smem_upd_nth : forall rs i r r', nth_error rs i = Some r ->
exists l1 l2, rs = l1 ++ r :: l2 /\ smem_upd rs i r' = l1 ++ r' :: l2.
Proof.
induction rs as [|x t IH]; intros i r r' H; [destruct i; discriminate|].
destruct i as [|j]; cbn in H |- *.
- injection H as ->. exists [], t. split; reflexivity.
- destruct (IH j r r' H) as (l1 & l2 & -> & ->). exists (x :: l1), l2. split; reflexivity.
Qed.
Lemma all_disjoint_app : forall E r l1 l2, YP09.all_disjoint E r (l1 ++ l2) <-> YP09.all_disjoint E r l1 /\ YP09.all_disjoint E r l2.
Proof. intros E r l1 l2. induction l1 as [|x t IH]; cbn; tauto. Qed.
Lemma all_disjoint_same : forall E x r r' l, same_frame r r' -> YP09.all_disjoint E x l -> In r l ->
YP09.extent_disjoint E x r'.
Proof.
intros E x r r' l (B & L & Hh & _ & _) Hd Hin. induction l as [|y t IH]; [destruct Hin|]. cbn in Hd. destruct Hd as [D1 D2].
destruct Hin as [->|Hin]; [|exact (IH D2 Hin)]. unfold YP09.extent_disjoint in *. rewrite B, L, Hh. exact D1.
Qed.
Lemma pairwise_disjoint_upd : forall E l1 r r' l2, same_frame r r' ->
YP09.pairwise_disjoint E (l1 ++ r :: l2) -> YP09.pairwise_disjoint E (l1 ++ r' :: l2).
Proof.
intros E l1 r r' l2 SF. induction l1 as [|x t IH]; cbn; intros [A P].
- split; [|exact P]. destruct SF as (B & L & Hh & _ & _).
clear P. induction l2 as [|y u IH2]; cbn in A |- *; [exact I|]. destruct A as [A1 A2]. split; [|exact (IH2 A2)].
unfold YP09.extent_disjoint in *. rewrite B, L, Hh. exact A1.
- split; [|exact (IH P)]. apply all_disjoint_app in A as [A1 A2]. apply all_disjoint_app. split; [exact A1|]. cbn in A2 |- *.
destruct A2 as [A3 A4]. split; [|exact A4]. destruct SF as (B & L & Hh & _ & _). unfold YP09.extent_disjoint in *. rewrite B, L, Hh. exact A3.
Qed.
Lemma regions_wf_app : forall l1 l2, YP09.regions_wf (l1 ++ l2) = (YP09.regions_wf l1 && YP09.regions_wf l2)%bool.
Proof. intros l1 l2. induction l1 as [|x t IH]; cbn; [reflexivity|]. rewrite IH, Bool.andb_assoc. reflexivity. Qed.
Lemma st_ok_set_region : forall E ss ms i r r',
YP0l.st_ok tfibsegs E ss ms -> nth_error (ss_mem ss) i = Some r -> same_frame r r' -> YP09.region_wf r' = true ->
Forall (YP09.chunk_ok tfibsegs E (ms_mem ms) (base_val E (YP09.r_base r'))) (YP09.r_chunks r') ->
YP0l.st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (smem_upd (ss_mem ss) i r') (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms i r r' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Wf & O & D) & H9) Hi SF Hwf Hcs.
destruct (smem_upd_nth _ _ _ r' Hi) as (l1 & l2 & El & ->). rewrite El in Wf, O, D.
unfold YP0l.st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- rewrite regions_wf_app in Wf |- *. cbn in Wf |- *. rewrite Hwf. apply andb_prop in Wf as [A Bc]. apply andb_prop in Bc as [_ C]. rewrite A, C. reflexivity.
- apply Forall_app in O as [O1 O2]. inversion O2 as [|x t Or Ot]; subst. apply Forall_app. split; [exact O1|]. constructor; [|exact Ot].
destruct Or as (Q1 & Q2 & Q3 & _). destruct SF as (B & L & Hh & Wl & Wh). unfold YP09.region_ok. rewrite B, L, Hh, Wl, Wh.
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. rewrite <- B. exact Hcs.
- exact (pairwise_disjoint_upd E l1 r r' l2 SF D).
Qed.
Lemma chunk_ok_zero_mb : forall E m base off len,
(forall i, 0 <= i < len -> mbyte tfibsegs m (base + off + i) = Some (Z_to_bv 8 0)) ->
YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CZero len)).
Proof.
intros E m base off len H i Hi. cbn [YP09.c_off YP09.c_val YP09.c_len cv_len cbyte] in Hi |- *.
exists (Z_to_bv 8 0). split; [reflexivity|]. exact (H i Hi).
Qed.
Lemma val_mem4_bytes : forall m a v, val_mem tfibsegs m a 4 v <->
(mbyte tfibsegs m a = Some (Z_to_bv 8 (YO0f.le_byte v 4 0)) /\ mbyte tfibsegs m (a + 1) = Some (Z_to_bv 8 (YO0f.le_byte v 4 1)) /\
mbyte tfibsegs m (a + 2) = Some (Z_to_bv 8 (YO0f.le_byte v 4 2)) /\ mbyte tfibsegs m (a + 3) = Some (Z_to_bv 8 (YO0f.le_byte v 4 3))).
Proof.
intros m a v. unfold val_mem. split.
- intros H. pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1. pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in H0, H1, H2, H3. rewrite Z.add_0_r in H0. tauto.
- intros (H0 & H1 & H2 & H3) k Hk. destruct k as [|[|[|[|k]]]]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; [rewrite Z.add_0_r; exact H0 | exact H1 | exact H2 | exact H3 | lia].
Qed.
Lemma val_mem1_byte : forall m a v, val_mem tfibsegs m a 1 v <-> mbyte tfibsegs m a = Some (Z_to_bv 8 (YO0f.le_byte v 1 0)).
Proof.
intros m a v. unfold val_mem. split.
- intros H. pose proof (H 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0. rewrite Z.add_0_r in H0. exact H0.
- intros H0 k Hk. destruct k as [|k]; [cbn [Z.of_nat]; rewrite Z.add_0_r; exact H0 | lia].
Qed.
Lemma denot_by_zev : forall (E : env) t v, svpure t = true -> 0 <= v < 2 ^ 64 -> zev (rho_of E) t = v -> sv_denot E t = Z_to_bv 64 v.
Proof.
intros E t v Hp Hv Hz. apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_unsigned (sv_denot E t)) with (U E t).
rewrite (U_zev E t Hp), Hz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). symmetry. apply Z.mod_small. exact Hv.
Qed.
Lemma bytes3_of : forall m a (z : byte),
mbyte tfibsegs m (a + 1) = Some z -> mbyte tfibsegs m (a + 2) = Some z -> mbyte tfibsegs m (a + 3) = Some z ->
forall i, 0 <= i < 3 -> mbyte tfibsegs m (0 + (a + 1) + i) = Some z.
Proof.
intros m a z B1 B2 B3 i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2) by lia. destruct C as [ -> | [ -> | -> ] ];
[replace (0 + (a + 1) + 0) with (a + 1) by lia | replace (0 + (a + 1) + 1) with (a + 2) by lia | replace (0 + (a + 1) + 2) with (a + 3) by lia]; assumption.
Qed.
Lemma bytes4_of : forall m a (z : byte),
mbyte tfibsegs m a = Some z -> mbyte tfibsegs m (a + 1) = Some z -> mbyte tfibsegs m (a + 2) = Some z -> mbyte tfibsegs m (a + 3) = Some z ->
forall i, 0 <= i < 4 -> mbyte tfibsegs m (0 + a + i) = Some z.
Proof.
intros m a z B0 B1 B2 B3 i Hi.
assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia. destruct C as [ -> | [ -> | [ -> | -> ] ] ];
[replace (0 + a + 0) with a by lia | replace (0 + a + 1) with (a + 1) by lia | replace (0 + a + 2) with (a + 2) by lia | replace (0 + a + 3) with (a + 3) by lia]; assumption.
Qed.
Lemma zcanon_negadd : forall a b, 0 <= b <= a -> a < M64 -> zcanon (zcanon (b * zcanon (-1)) + a) = a - b.
Proof.
intros a b H H2. unfold zcanon. change ((-1) mod M64) with (M64 - 1).
rewrite Zplus_mod_idemp_l. replace (b * (M64 - 1) + a) with ((a - b) + b * M64) by lia.
unfold M64 in *. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Definition A_Drain : Z := 0x32f28.
Definition A_Recycle : Z := 0x330cc.
Definition A_DoRecycle : Z := 0x33434.
Definition A_RChunk : Z := 0x3356c.
Definition A_CDealloc : Z := 0x33970.
Definition A_SDealloc : Z := 0x33b38.
Definition A_QUAR : Z := A_ALLOCATOR + o_quar.
Definition DSTACK : Z := 4096.
Definition transfer_g (X : astate) : qcache :=
mkQC (qc_list (st_qglobal X) ++ qc_list (st_qthread X)) (qc_bytes (st_qglobal X) + qc_bytes (st_qthread X)).
Definition recycle_body (g : qcache) : M unit :=
mcheck (2 * (kBatchBytes * Z.of_nat (length (qc_list g))) <=? qc_bytes g) 209280 ;;
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
destruct (qc_bytes (st_qthread X) <=? kQuarantineCacheMax); reflexivity.
Qed.
Lemma maybe_drain_drain : forall X, kQuarantineCacheMax < qc_bytes (st_qthread X) -> maybe_drain X = drain_body X X.
Proof. intros X H. rewrite maybe_drain_eq. destruct (Z.leb_spec (qc_bytes (st_qthread X)) kQuarantineCacheMax); [lia | reflexivity]. Qed.
Lemma drain_body_apost : forall U pp cc bb X,
WfP U pp cc bb X -> qloose X   -> kQuarantineCacheMax < qc_bytes (st_qthread X) ->
apost (drain_body X X) (fun r => WfP U pp cc bb (snd r) /\ fframe X (snd r) /\
qc_bytes (st_qthread (snd r)) <= kQuarantineCacheMax /\ qc_bytes (st_qglobal (snd r)) <= Z.max (qc_bytes (st_qglobal X)) kQuarantineMax /\
unq (snd r) = unq X).
Proof.
intros U pp cc bb X W QL HD. rewrite <- (maybe_drain_drain X HD). intros tr r Hp.
assert (REG : st_nev X <= EV_MAX \/ (Z.of_nat (length (st_chunks X)) <= 2 ^ 23 /\ qc_bytes (st_qglobal X) + qc_bytes (st_qthread X) <= 2 ^ 36)).
{ destruct (wf_regime _ _ _ _ _ W) as [Hs|[_ HC]]; [left; exact Hs | right]. pose proof (wf_slack _ _ _ _ _ W) as (_ & C0 & _). destruct QL as (Q1 & Q2 & _). split; lia. }
destruct (atok_apath _ true _ tr r (maybe_drain_ok U pp cc bb X true W REG) Hp) as (ns' & A). exact A.
Qed.
Lemma aowned_same_cf : forall B ly S1 S2 a, st_chunks S2 = st_chunks S1 -> st_fs S2 = st_fs S1 -> aowned B ly S2 a -> aowned B ly S1 a.
Proof. intros B ly S1 S2 a E1 E2 H. unfold aowned, aclient_byte, sec_extents, frames in *. rewrite E1, E2 in H. exact H. Qed.
Section e.
Variable B : asyms.
Definition drain_pre (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly X W mem md /\
kQuarantineCacheMax < qc_bytes (st_qthread X) /\ qloose X /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DSTACK <= spZ regs /\ spZ regs <= ly_stk_hi ly /\
(forall a, spZ regs - DSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 A_QUAR /\ getr regs 11 = w64 (ly_T ly + t_qc) /\ getr regs 12 = w64 (ly_T ly + t_cache).
Definition drain_leaf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B DSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md'.
Definition tfib_drain_spec : Prop :=
forall ly X W regs mem md,
drain_pre ly X W regs mem md ->
amreal tfibsegs (drain_body X X) W (cfg_at tfibsegs A_Drain regs mem md) (drain_leaf ly X W regs mem md).
Definition DRSTACK : Z := 2048.
Definition LFRAME : Z := 80.
Definition plist_cells (tmp : Z) (P : list batch) : list acell :=
qc_cells (ANum tmp) (mkQC P (sum_bytes P)).
Definition dr_pre (ly : alayout) (X : astate) (P : list batch) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly X W mem md /\
RI (as_universe B) 0 0 0 X P /\ qc_bytes (st_qthread X) = 0 /\ qc_bytes (st_qglobal X) <= kQuarantineMax /\
Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (plist_cells (spZ regs) P) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + DRSTACK <= spZ regs /\ spZ regs + 32 <= ly_stk_hi ly /\
(forall a, spZ regs - DRSTACK <= a < spZ regs + 32 -> apresent (w_H W) mem a) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 11 = getr regs 2 /\ getr regs 12 = w64 (ly_T ly + t_cache) /\
Z.of_nat (length P) < 100000 /\ st_cache_inited X = true.
Definition dr_leaf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B DRSTACK ly X W regs mem md (fun a => spZ regs <= a < spZ regs + 32) ly (snd r) W' regs' mem' md' /\
(forall a, spZ regs <= a < spZ regs + 32 -> apresent (w_H W') mem' a).
Definition tfib_dorecycle_spec : Prop :=
forall ly X P W regs mem md,
dr_pre ly X P W regs mem md ->
amreal tfibsegs (do_recycle 100000%nat P X) W (cfg_at tfibsegs A_DoRecycle regs mem md) (dr_leaf ly X W regs mem md).
Definition KSTACK : Z := 512.
Definition cd_pre (ly : alayout) (X : astate) (c off : Z) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly X W mem md /\ st_cache_inited X = true /\ 1 <= c <= 30 /\
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
Definition cd_leaf (ly : alayout) (X : astate) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B KSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
st_cache_inited (snd r) = true.
Definition tfib_cdealloc_spec : Prop :=
forall ly X c off W regs mem md,
cd_pre ly X c off W regs mem md ->
amreal tfibsegs (cache_dealloc c off X) W (cfg_at tfibsegs A_CDealloc regs mem md) (cd_leaf ly X W regs mem md).
Definition rcc_pre (ly : alayout) (X : astate) (k : chunk) (cbp : Z) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) : Prop :=
AR tfibsegs B ly X W mem md /\ st_cache_inited X = true /\
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)) /\
YK0s.ret_ok (getr regs 1) /\ 4096 <= raZ regs /\
spZ regs mod 16 = 0 /\ ly_stk_lo ly + KSTACK <= spZ regs /\ spZ regs <= cbp /\ cbp + 16 <= ly_stk_hi ly /\ cbp mod 8 = 0 /\
(forall a, spZ regs - KSTACK <= a < spZ regs -> apresent (w_H W) mem a) /\ (forall a, cbp <= a < cbp + 16 -> apresent (w_H W) mem a) /\
val_mem tfibsegs (mrestrict (w_H W) mem) cbp 8 (ly_T ly + t_cache) /\
getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 10 = w64 cbp /\ getr regs 11 = w64 (ck_base B ly k + ck_rz k - kChunkHeaderSize).
Definition rcc_leaf (ly : alayout) (X : astate) (k : chunk) (W : world tfibsegs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model)
(r : unit * astate) (W' : world tfibsegs) (c' : config) : Prop :=
exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
acall_post tfibsegs B KSTACK ly X W regs mem md (fun _ => False) ly (snd r) W' regs' mem' md' /\
(forall a, 0 <= a < 2 ^ 64 -> puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) ->
aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
st_cache_inited (snd r) = true.
Definition tfib_rchunk_spec : Prop :=
forall ly X k cbp W regs mem md,
rcc_pre ly X k cbp W regs mem md ->
amreal tfibsegs (recycle_chunk k X) W (cfg_at tfibsegs A_RChunk regs mem md) (rcc_leaf ly X k W regs mem md).
End e.
End d.
