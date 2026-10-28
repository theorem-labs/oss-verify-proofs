(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP0e YP09 YP03.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFIB_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in *.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Definition XJ (a : Z) : Prop := TFIB_OOM <= a < TFIB_OOM + 1.
Lemma XJ_dec : forall a, {XJ a} + {~ XJ a}.
Proof. intros a. unfold XJ. destruct (Z_le_gt_dec TFIB_OOM a); [destruct (Z_lt_ge_dec a (TFIB_OOM + 1)); [left; lia | right; lia] | right; lia]. Qed.
Section f.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfibsegs) (mem mem' : word -> option byte) (md md' : Model).
Hypothesis TS : TfibSyms B.
Hypothesis HAR : AR tfibsegs B ly S W mem md.
Let rd0 : reader := aview tfibsegs (w_H W) mem.
Let rd' : reader := aview tfibsegs (w_H W) mem'.
Hypothesis AG0 : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ XJ a -> rd' a = rd0 a.
Hypothesis VIS : forall a, rd0 a <> None -> rd' a <> None.
Hypothesis Hvm : m_vmmaps md' = m_vmmaps md.
Hypothesis Hlz : m_vm_lazy md' = m_vm_lazy md.
Hypothesis He : eager_used md' = eager_used md.
Hypothesis HK : forall a, in_band_rw a -> w_H W (YG0n.w64 a) = true -> mem' (YG0n.w64 a) = mem (YG0n.w64 a).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Let IMG : img_cover ly := img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)).
Lemma AGX : forall a, aowned B ly S a -> ~ XJ a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfibsegs B ly S W mem md a HAR Ho) as Ra.
ceil.   apply AG0; [clear - Ra CR0; lia | exact Ho | exact Hx].
Qed.
Lemma Z_high : forall a, kHighMemBeg <= a -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, kHighMemBeg in *. lia. Qed.
Lemma Z_shadow : forall a, SHADOW_OFF <= a -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, SHADOW_OFF in *. lia. Qed.
Lemma Z_inst : forall a, TFIB_INST <= a < TFIB_INST + 3632 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_INST in *. lia. Qed.
Lemma Z_ial : forall a, TFIB_IAL_LO <= a < TFIB_IAL_HI -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_IAL_LO, TFIB_IAL_HI in *. lia. Qed.
Lemma Z_flag : forall a, TFIB_IAL_FLAG <= a < TFIB_IAL_FLAG + 2 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_IAL_FLAG in *. lia. Qed.
Lemma Z_depot : forall a, TFIB_DEPOT <= a < TFIB_DEPOT + 4 * 2 ^ 20 + 32 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_DEPOT in *. lia. Qed.
Lemma Z_store : forall a, TFIB_STORE <= a < TFIB_STORE + 32 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_STORE in *. lia. Qed.
Lemma Z_tls : forall a, TFIB_TP - 256 <= a < TFIB_TP + 256 \/ TFIB_TSD <= a < TFIB_TSD + 8 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFIB_OOM, TFIB_TP, TFIB_TSD in *. lia. Qed.
Lemma Z_zone : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ XJ a.
Proof. intros x sz a Z3 Ha Hx. apply (zone3_apart_img x sz a Z3); [|exact Ha]. unfold XJ, TFIB_OOM, TFIB_IMG_LO, TFIB_IMG_END in *. lia. Qed.
Lemma ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e).
Proof.
intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly LY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)).
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ zone3 (ly_Q ly) kPtrArrayResv /\ zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_F ly) kFakeStackSize /\
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\ ly_prim ly <= ly_space ly.
Proof.
pose proof (lo_high ly LY) as [P _]. pose proof (lo_space_in ly LY) as [SP _].
split; [exact P|].
repeat match goal with |- _ /\ _ => split end; try exact SP;
match goal with |- zone3 ?x ?sz => exact (ZI (x, sz) ltac:(unfold owned_extents; cbn [In]; tauto)) end.
Qed.
Lemma Z_secx : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XJ a.
Proof.
intros e a Hex Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e Hex) as (_ & HIA & _).
assert (D9 : zdisjoint e (ly_img ly)).
{ exact (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(unfold static_extents; apply in_app_iff; right; cbn; tauto)). }
assert (SZ : 0 <= snd e) by (clear - Ha; lia).
exact (Z_zone (fst e) (snd e) a (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(destruct e; exact D9)) Ha).
Qed.
Lemma Z_chunk : forall k a, In k (st_chunks S) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XJ a.
Proof.
intros k a Hk Ha. pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG].
- destruct GG as (Gc & _ & _ & _ & Gbase & Gx & _). pose proof (region_in_prim ly (prim_class o) LY ltac:(clear - Gc; lia)) as (_ & _ & _ & R4 & _).
apply Z_high. clear - Ha Gbase Gx R4. lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _). apply (Z_secx _ a Gin). cbn [fst snd]. clear - Ha Gbase Gext. unfold kPage in *. lia.
Qed.
Lemma keep_cells : forall lst (Zn : Z -> Prop), (forall a, Zn a -> ~ XJ a) -> incl lst (acells B ly S) ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> Zn (aeval B ly (c_at cc) + k)) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst Zn LOC INC RNG. apply Forall_forall. intros cc Hc.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc))|].
intros k Hk. apply AGX.
- exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- apply LOC. exact (proj1 (Forall_forall _ _) RNG cc Hc k Hk).
Qed.
Lemma rng_high : forall lst, Forall (fun cc => kHighMemBeg <= aeval B ly (c_at cc)) lst ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> kHighMemBeg <= aeval B ly (c_at cc) + k) lst.
Proof. intros lst H. eapply Forall_impl; [|exact H]. cbv beta. intros cc Hc k Hk. lia. Qed.
Lemma keep_high : forall lst, incl lst (acells B ly S) -> Forall (fun cc => kHighMemBeg <= aeval B ly (c_at cc)) lst -> Forall (cell_holds B ly rd') lst.
Proof. intros lst INC H. exact (keep_cells lst (fun a => kHighMemBeg <= a) Z_high INC (rng_high lst H)). Qed.
Lemma keep_zone : forall x sz lst, zone3 x sz -> incl lst (acells B ly S) ->
Forall (fun cc => x <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= x + sz) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros x sz lst Z3 INC H. apply (keep_cells lst (fun a => x <= a < x + sz) (fun a Ha => Z_zone x sz a Z3 Ha) INC).
eapply Forall_impl; [|exact H]. cbv beta. intros cc [H1 H2] k Hk. lia.
Qed.
Tactic Notation "acells_at" integer(n) := intros x Hx; unfold acells; do n (apply in_app_iff; right); first [apply in_app_iff; left; exact Hx | exact Hx].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S) (zseq 1 31)).
Proof.
apply keep_high; [acells_at 0|]. pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells, kRegionInfoOff.
repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S) (zseq 1 31)).
Proof.
pose proof HI as (_ & _ & PT & _). apply (keep_zone (ly_T ly) kThreadObjSize _ PT); [acells_at 1|].
apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold cache_cells.
pose proof (class_ok c' ltac:(clear - Hc'; lia)) as (_ & _ & _ & Kmc & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(clear - Hc'; lia)) as CL. unfold wf_class in CL.
destruct (st_cache_inited S) eqn:CI.
- rewrite ?CI in CL. pose proof (wr_cache _ _ _ _ _ _ CL) as [PM PL].
apply Forall_cons; [cbn; unfold t_cache, kThreadObjSize; lia|]. apply Forall_cons; [cbn; unfold t_cache, kThreadObjSize; lia|]. apply Forall_cons; [cbn; unfold t_cache, kThreadObjSize; lia|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin. cbn. unfold t_cache, kThreadObjSize. lia.
- repeat (apply Forall_cons; [cbn; unfold t_cache, kThreadObjSize; lia|]). apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
apply (keep_cells _ (fun a => exists k, In k (st_chunks S) /\ ck_base B ly k <= a < ck_base B ly k + ck_extent k));
[intros a (k & Hk & Ha); exact (Z_chunk k a Hk Ha) | acells_at 2 |].
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
pose proof (req_size_bounds (ck_req k) ltac:(clear - G7; lia)) as (_ & Q1 & _).
clear GG. unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
- repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; intros kk Hkk; cbn in Hkk; exists k; split; [exact Hk|]; rewrite ?EA2, ?EA, ?EA0; lia|]). apply Forall_nil.
- destruct (ck_rz k =? 16); [apply Forall_nil|]. repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; intros kk Hkk; cbn in Hkk; exists k; split; [exact Hk|]; rewrite ?EA2, ?EA, ?EA0; lia|]). apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S).
Proof.
assert (INC : incl (sec_cells S) (acells B ly S)) by (acells_at 3).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & PQ & _).
unfold sec_cells in *.
assert (LI : forall o, 0 <= o < 3632 -> forall k, 0 <= k < 1 -> TFIB_INST <= aeval B ly (AInst o) + k < TFIB_INST + 3632) by (intros o Ho k Hk; cbn; rewrite EI; lia).
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons]].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval]; rewrite EI; unfold o_sec_reserved, o_sec_n, o_sec_mutex in *; cbn in Hk; lia | apply Forall_nil]
end.
apply Forall_app. split.
-
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR.
apply (keep_zone (ly_Q ly) kPtrArrayResv _ PQ); [intros x Hx; apply INC; do 3 right; apply in_app_iff; left; exact Hx|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin.
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
-
apply (keep_cells _ (fun a => exists e, In e (sec_extents ly S) /\ fst e <= a < fst e + snd e));
[intros a (e & Hex & Ha); exact (Z_secx e a Hex Ha) | intros x Hx; apply INC; do 3 right; apply in_app_iff; right; exact Hx |].
apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (req_size_bounds (ck_req k) ltac:(clear - G7; lia)) as (_ & Q1 & _).
repeat (apply Forall_cons; [cbn [c_at c_w c8 z8 aeval aoff]; intros kk Hkk; cbn in Hkk; eexists; split; [exact Gin|]; cbn [fst snd]; clear - Hkk Gbase Gext G5 G8 Q1; unfold kPage in *; lia|]). apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
induction bl as [|b t IH]; intros Hincl INC; [apply Forall_nil|]. cbn [batch_cells].
assert (Hb : kHighMemBeg <= ly_space ly + b_self b).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; split; [reflexivity | apply Hincl; left; reflexivity]).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1 X2].
assert (RO : region_off kBatchClass = 24 * 2 ^ 32) by reflexivity. subst x. rewrite RO in X1. clear - X1 P SP. lia. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_app; split]]].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_high [cc] ltac:(intros y [<-|[]]; apply INC; cbn; tauto) ltac:(apply Forall_cons; [cbn; lia | apply Forall_nil])) cc (or_introl eq_refl))
end.
- apply keep_high; [intros y Hy; apply INC; do 3 right; apply in_app_iff; left; exact Hy|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & _). cbn. lia.
- apply IH; [intros y Hy; apply Hincl; right; exact Hy | intros y Hy; apply INC; do 3 right; apply in_app_iff; right; exact Hy].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S).
Proof.
assert (INC : incl (quar_cells S) (acells B ly S)) by (acells_at 4).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & _ & PT & _).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
apply Forall_cons; [|apply Forall_cons].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval]; rewrite EI; cbn in Hk; lia | apply Forall_nil]
end.
apply Forall_app. split.
- do 4 (apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_zone (ly_T ly) kThreadObjSize [cc] PT ltac:(intros y [<-|[]]; apply INC; right; right; apply in_app_iff; left; cbn; tauto) ltac:(apply Forall_cons; [cbn; unfold kThreadObjSize; lia | apply Forall_nil])) cc (or_introl eq_refl)) end|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; left; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. left. do 4 right. exact Hy.
- do 4 (apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(intros x [<-|[]]; apply INC; right; right; apply in_app_iff; right; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval aoff]; rewrite EI; cbn in Hk; lia | apply Forall_nil] end|]).
apply keep_batches; [intros b Hb; unfold all_batches; apply in_app_iff; right; exact Hb|].
intros y Hy. apply INC. right; right. apply in_app_iff. right. do 4 right. exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S).
Proof.
pose proof HI as (_ & _ & _ & PF & _). apply (keep_zone (ly_F ly) kFakeStackSize _ PF); [acells_at 5|].
unfold fs_cells. apply Forall_cons; [cbn; unfold kFakeStackSize; lia|]. apply Forall_cons; [cbn; unfold kFakeStackSize; lia|].
apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin. cbn. unfold kFakeStackSize. lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S).
Proof.
assert (INC : incl (depot_cells ly S) (acells B ly S)) by (acells_at 6).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
unfold depot_cells in *.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_depot ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1]; intros k Hk; cbn [aeval]; rewrite ED; unfold d_nuniq, d_map1 in *; cbn in Hk; lia | apply Forall_nil]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_store ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1]; intros k Hk; cbn [aeval]; rewrite ES; unfold s_total, s_block0 in *; cbn in Hk; lia | apply Forall_nil]
end.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S).
Proof.
assert (INC : incl (ialloc_cells B S) (acells B ly S)) by (acells_at 7).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3. pose proof (ts_ial_hi B TS) as E4.
unfold ialloc_cells in *.
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_flag ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1 z1]; intros k Hk; cbn [aeval]; rewrite E3; cbn in Hk; lia | apply Forall_nil]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_ial ltac:(intros x [<-|[]]; apply INC; cbn; tauto) _) cc (or_introl eq_refl));
apply Forall_cons; [cbn [c_at c_w c8 z8 z4 c4 c1 z1]; intros k Hk; cbn [aeval]; rewrite E1, E2; unfold TFIB_IAL_LO, TFIB_IAL_W, TFIB_IAL_HI; cbn in Hk; lia | apply Forall_nil]
end.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof HI as (_ & _ & PT & _). apply (keep_zone (ly_T ly) kThreadObjSize _ PT); [acells_at 8|].
unfold thread_cells. apply Forall_cons; [cbn; unfold t_unwinding, kThreadObjSize; lia | apply Forall_nil].
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S).
Proof.
unfold acells.
apply Forall_app; split; [exact cells_regions|]. apply Forall_app; split; [exact cells_caches|]. apply Forall_app; split; [exact cells_chunks|].
apply Forall_app; split; [exact cells_sec|]. apply Forall_app; split; [exact cells_quar|]. apply Forall_app; split; [exact cells_fs|].
apply Forall_app; split; [exact cells_depot|]. apply Forall_app; split; [exact cells_ialloc | exact cells_thread].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S.
Proof.
intros c' i vv Hc' Hi HV k Hk. pose proof HI as (P & _).
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk) | eapply own_fa; [exact MA | exact Hc' | clear - Hi Hk FL FB; numconst; lia] |].
apply Z_high. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2 P. numconst. lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S.
Proof.
intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB. pose proof HI as (_ & _ & _ & PF & _).
rewrite AGX; [exact (am_flags _ _ _ _ MA cid pos Hc Hp) | unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [exact MA | lia] |].
apply (Z_zone _ _ _ PF). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S.
Proof.
pose proof (ts_depot B TS) as ED. pose proof HI as (_ & _ & _ & _ & PNB & _).
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). lia. }
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. apply AGX.
- destruct Ha as [Ha|Ha].
+ apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa5850, 0x5c8650 - 0xa5850). split; [cbn; tauto|]. unfold in_zr; cbn. unfold TFIB_DEPOT, d_tab_words in Ha. lia.
+ apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [unfold core_extents; cbn; tauto | cbn [fst snd]; lia].
- destruct Ha as [Ha|Ha]; [apply Z_depot; unfold d_tab_words in *; lia | apply (Z_zone _ _ _ PNB); lia]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|]. left. rewrite ED. unfold d_tab_words in *. lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
+ intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. right. unfold kNodesBlockSize. lia.
+ intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. right. unfold kNodesBlockSize. lia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' S.
Proof.
intros g vv Hg8 HV.
rewrite AGX; [exact (am_shadow _ _ _ _ MA g vv Hg8 HV) | exact (ashadow_owned B ly S rd0 g vv MA HV) |].
apply Z_shadow. unfold shadow_addr.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
pose proof (Z.div_pos g 8). clear - Hg0 C1 H. unfold in_app in C1. numconst. lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|discriminate].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). pose proof HI as (P & _).
assert (0 <= g); [|pose proof (Z.div_pos g 8); lia].
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(lia)) as (R1 & R2 & _).
pose proof (region_off_eq c' ltac:(lia)) as RO.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base, region_base in *; rewrite RO in *; clear - Hlo R1 R2 P Hc'; numconst; lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. unfold in_app in C1. numconst. unfold kPage in *. lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi) | eapply own_shadow_zero; [exact MA | exact Hr | exact Hi] |].
apply Z_shadow. unfold shadow_addr.
assert (0 <= fst r); [|pose proof (Z.div_pos (fst r) 8); lia].
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst]. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). clear - T7. numconst. lia.
- exact (proj1 (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr)).
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S) /\ Forall (range_vis B ly rd') (aareas S) /\ Forall (range_vis B ly rd') (aclient S).
Proof.
split; [|split]; (eapply Forall_range_vis_keep; [exact VIS|]); [exact (am_junk _ _ _ _ MA) | exact (am_areas _ _ _ _ MA) | exact (am_client _ _ _ _ MA)].
Qed.
Definition abs_cell_okJ (cc : acell) : bool :=
match c_at cc with
| ANum a => (a + Z.max 1 (Z.of_nat (c_w cc)) <=? TFIB_OOM) || (TFIB_OOM + 1 <=? a)
| _ => false
end.
Lemma abs_cells_okJ : forallb abs_cell_okJ (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
apply Forall_forall. intros cc Hin.
apply (YG0q.cell_holds_agree B ly rd0); [exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin)|].
intros k Hk. apply AGX; [exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk)|].
rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. pose proof HI as (P & PQ & PT & PF & PNB & PSB & PC & PD & SP).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ apply Z_high; clear - Hk P SP; numconst; lia
| apply (Z_zone _ _ _ PT); clear - Hk; numconst; lia
| apply (Z_zone _ _ _ PC); clear - Hk; numconst; lia
| apply (Z_zone _ _ _ PD); clear - Hk; numconst; lia
| apply (Z_zone _ _ _ PF); clear - Hk; numconst; unfold kFakeStackSize; lia
| apply (Z_zone _ _ _ PQ); clear - Hk; numconst; unfold kPtrArrayResv; lia
| apply Z_tls; clear - Hk; lia
| apply Z_inst; clear - Hk; unfold o_space, o_rinfo, o_sec_chunks; lia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okJ cc Hin) as Hc. unfold abs_cell_okJ in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; unfold XJ; lia.
Qed.
Theorem AR_oom : AR tfibsegs B ly S W mem' md'.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|split; [|split; [|split]]].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ exact Mwf.
+ exact Mun.
+ exact Msy.
+ exact Mly.
+ exact Mpl.
+ exact const_final.
+ exact Mcow.
+ exact cells_final.
+ exact fa_final.
+ exact flags_final.
+ exact depot_final.
+ exact shadow_final.
+ exact zshadow_final.
+ exact (proj1 vis_final).
+ exact (proj1 (proj2 vis_final)).
+ exact (proj2 (proj2 vis_final)).
+
apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact MA | cbn; tauto |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia.
* apply Z_ial. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *; lia.
+ exact Mts.
+   exact Msi.
- eapply ALedger_same; [exact L | exact Hvm | exact Hlz | exact He].
- exact BUD.
- exact (amwf_same md md' Hvm Hlz MW).
- exact (ahs_transfer tfibsegs B ly S S (w_H W) mem mem' (al_img_env tfibsegs ly S md LY L) M0 HS0 VIS HK ltac:(intros a _ C; exact C) eq_refl
ltac:(intros g Hg Happ HF _; apply AGX; [eapply hfree_shadow_owned; [exact M0 | exact Hg | exact Happ | exact HF]
| pose proof (shadow_addr_band_rw g Happ) as SB; unfold XJ; clear - SB; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *; lia])).
Qed.
End f.
End c.
