(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0c YQ0b YQ04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00 YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Ltac numconst := ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, t_qc, ASTACK, TFX_IMG_END, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, kMaxSize in *.
Section c. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Local Open Scope am_scope.
Definition XJ {imgk : img} (a : Z) : Prop := TFX_OOM <= a < TFX_OOM + 1.

Section f. Context {imgk : img}.
Variables (B : asyms) (ly : alayout) (S : astate) (W : world tfxsegs) (mem mem' : word -> option byte) (md md' : Model).
Hypothesis TS : TfxSyms B.
Hypothesis HAR : AR tfxsegs B ly S W mem md.
Let rd0 : reader := aview tfxsegs (w_H W) mem.
Let rd' : reader := aview tfxsegs (w_H W) mem'.
Hypothesis AG0 : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> ~ XJ a -> rd' a = rd0 a.
Hypothesis VIS : forall a, rd0 a <> None -> rd' a <> None.
Hypothesis Hvm : m_vmmaps md' = m_vmmaps md.
Hypothesis Hlz : m_vm_lazy md' = m_vm_lazy md.
Hypothesis He : eager_used md' = eager_used md.
Hypothesis HK : forall a, in_band_rw a -> w_H W (YG0u.w64 a) = true -> mem' (YG0u.w64 a) = mem (YG0u.w64 a).
Let MA : ARm B ly S rd0 := proj1 HAR.
Let WF : Wf (as_universe B) S := am_wf B ly S rd0 MA.
Let LY : layout_ok ly := am_layout B ly S rd0 MA.
Let IMG : img_cover ly := img_cover_of_ledger ly _ _ (proj1 (proj2 HAR)).
Lemma AGX : forall a, aowned B ly S a -> ~ XJ a -> rd' a = rd0 a.
Proof.
intros a Ho Hx. pose proof (AR_owned_low_law_ok tfxsegs B ly S W mem md a HAR Ho) as Ra.
ceil.   img_apply AG0; [img_try (clear - Ra CR0; img_lia) | img_try (img_exact Ho) | img_try (img_exact Hx)].
Qed.
Lemma Z_high : forall a, kHighMemBeg <= a -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, kHighMemBeg in *. img_lia. Qed.
Lemma Z_shadow : forall a, SHADOW_OFF <= a -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, SHADOW_OFF in *. img_lia. Qed.
Lemma Z_inst : forall a, TFX_INST <= a < TFX_INST + 3632 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_INST in *. img_lia. Qed.
Lemma Z_ial : forall a, TFX_IAL_LO <= a < TFX_IAL_HI -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_IAL_LO, TFX_IAL_HI in *. img_lia. Qed.
Lemma Z_flag : forall a, TFX_IAL_FLAG <= a < TFX_IAL_FLAG + 2 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_IAL_FLAG in *. img_lia. Qed.
Lemma Z_depot : forall a, TFX_DEPOT <= a < TFX_DEPOT + 4 * 2 ^ 20 + 32 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_DEPOT in *. img_lia. Qed.
Lemma Z_store : forall a, TFX_STORE <= a < TFX_STORE + 32 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_STORE in *. img_lia. Qed.
Lemma Z_tls : forall a, TFX_TP - 256 <= a < TFX_TP + 256 \/ TFX_TSD <= a < TFX_TSD + 8 -> ~ XJ a.
Proof. intros a Ha Hx. unfold XJ, TFX_OOM, TFX_TP, TFX_TSD in *. img_lia. Qed.
Lemma Z_zone : forall x sz a, zone3 x sz -> x <= a < x + sz -> ~ XJ a.
Proof. intros x sz a Z3 Ha Hx. img_apply (zone3_apart_img x sz a Z3); [|img_try (img_exact Ha)]. unfold XJ, TFX_OOM, TFX_IMG_LO, TFX_IMG_END in *. img_lia. Qed.
Lemma ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e).
Proof.
intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly LY) as PD.
img_exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(img_try (unfold static_extents; rewrite <- app_assoc; img_refl)) PD ltac:(img_try (img_apply in_app_iff; left; img_exact Hex)) ltac:(img_try (left; img_refl))). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; (subst; cbv beta); cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; img_lia. }
img_exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(img_try (destruct e; img_exact D9))).
Qed.
Lemma HI : kHighMemBeg <= ly_prim ly /\ zone3 (ly_Q ly) kPtrArrayResv /\ zone3 (ly_T ly) kThreadObjSize /\ zone3 (ly_F ly) kFakeStackSize /\
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\ zone3 (ly_C ly) 256 /\ zone3 (ly_D ly) 4096 /\ ly_prim ly <= ly_space ly.
Proof.
pose proof (lo_high ly LY) as [P _]. pose proof (lo_space_in ly LY) as [SP _].
split; [img_try (img_exact P)|].
repeat match goal with |- _ /\ _ => split end; try img_exact SP;
match goal with |- zone3 ?x ?sz => img_exact (ZI (x, sz) ltac:(img_try (unfold owned_extents; cbn [In]; tauto))) end.
Qed.
Lemma Z_secx : forall e a, In e (sec_extents ly S) -> fst e <= a < fst e + snd e -> ~ XJ a.
Proof.
intros e a Hex Ha. pose proof (am_placed _ _ _ _ MA) as [PL PD]. pose proof (proj1 (Forall_forall _ _) PL e Hex) as (_ & HIA & _).
assert (D9 : zdisjoint e (ly_img ly)).
{ img_exact (pairwise_In zdisjoint _ e (ly_img ly) (sec_extents ly S) (static_extents ly) eq_refl PD Hex ltac:(img_try (unfold static_extents; img_apply in_app_iff; right; cbn; tauto))). }
assert (SZ : 0 <= snd e) by (img_try (clear - Ha; img_lia)).
img_exact (Z_zone (fst e) (snd e) a (zone3_intro ly (fst e) (snd e) IMG SZ HIA ltac:(img_try (destruct e; img_exact D9))) Ha).
Qed.
Lemma Z_chunk : forall k a, In k (st_chunks S) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ~ XJ a.
Proof.
intros k a Hk Ha. pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG].
- destruct GG as (Gc & _ & _ & _ & Gbase & Gx & _). pose proof (region_in_prim ly (prim_class o) LY ltac:(img_try (clear - Gc; img_lia))) as (_ & _ & _ & R4 & _).
img_apply Z_high. clear - Ha Gbase Gx R4. img_lia.
- destruct GG as (_ & _ & Gbase & Gext & Gin & _). img_apply (Z_secx _ a Gin). cbn [fst snd]. clear - Ha Gbase Gext. unfold kPage in *. img_lia.
Qed.
Lemma keep_cells : forall lst (Zn : Z -> Prop), (forall a, Zn a -> ~ XJ a) -> incl lst (acells B ly S) ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> Zn (aeval B ly (c_at cc) + k)) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros lst Zn LOC INC RNG. img_apply Forall_forall. intros cc Hc.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ MA) cc (INC cc Hc)))|].
intros k Hk. img_apply AGX.
- img_exact (proj1 (Forall_forall _ _) (acells_owned B ly S rd0 MA) cc (INC cc Hc) k Hk).
- img_apply LOC. img_exact (proj1 (Forall_forall _ _) RNG cc Hc k Hk).
Qed.
Lemma rng_high : forall lst, Forall (fun cc => kHighMemBeg <= aeval B ly (c_at cc)) lst ->
Forall (fun cc => forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w cc)) -> kHighMemBeg <= aeval B ly (c_at cc) + k) lst.
Proof. intros lst H. eapply Forall_impl; [|img_try (img_exact H)]. cbv beta. intros cc Hc k Hk. img_lia. Qed.
Lemma keep_high : forall lst, incl lst (acells B ly S) -> Forall (fun cc => kHighMemBeg <= aeval B ly (c_at cc)) lst -> Forall (cell_holds B ly rd') lst.
Proof. intros lst INC H. img_exact (keep_cells lst (fun a => kHighMemBeg <= a) Z_high INC (rng_high lst H)). Qed.
Lemma keep_zone : forall x sz lst, zone3 x sz -> incl lst (acells B ly S) ->
Forall (fun cc => x <= aeval B ly (c_at cc) /\ aeval B ly (c_at cc) + Z.max 1 (Z.of_nat (c_w cc)) <= x + sz) lst ->
Forall (cell_holds B ly rd') lst.
Proof.
intros x sz lst Z3 INC H. img_apply (keep_cells lst (fun a => x <= a < x + sz) (fun a Ha => Z_zone x sz a Z3 Ha) INC).
eapply Forall_impl; [|img_try (img_exact H)]. cbv beta. intros cc [H1 H2] k Hk. img_lia.
Qed.
Tactic Notation "acells_at" integer(n) := intros x Hx; unfold acells; do n (img_apply in_app_iff; right); first [img_apply in_app_iff; left; img_exact Hx | img_exact Hx].
Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells S) (zseq 1 31)).
Proof.
img_apply keep_high; [img_try (acells_at 0)|]. pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold region_cells, kRegionInfoOff.
repeat (img_apply Forall_cons; [img_try (cbn; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_caches : Forall (cell_holds B ly rd') (flat_map (cache_cells S) (zseq 1 31)).
Proof.
pose proof HI as (_ & _ & PT & _). img_apply (keep_zone (ly_T ly) kThreadObjSize _ PT); [img_try (acells_at 1)|].
img_apply Forall_flat_map'. intros c' Hc'. apply zseq_In in Hc'. unfold cache_cells.
pose proof (class_ok c' ltac:(img_try (clear - Hc'; img_lia))) as (_ & _ & _ & Kmc & _).
pose proof (wf_classes _ _ _ _ _ WF c' ltac:(img_try (clear - Hc'; img_lia))) as CL. unfold wf_class in CL.
destruct (st_cache_inited S) eqn:CI.
- rewrite ?CI in CL. pose proof (wr_cache _ _ _ _ _ _ CL) as [PM PL].
img_apply Forall_cons; [img_try (cbn; unfold t_cache, kThreadObjSize; img_lia)|]. img_apply Forall_cons; [img_try (cbn; unfold t_cache, kThreadObjSize; img_lia)|]. img_apply Forall_cons; [img_try (cbn; unfold t_cache, kThreadObjSize; img_lia)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i v] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin. cbn. unfold t_cache, kThreadObjSize. img_lia.
- repeat (img_apply Forall_cons; [img_try (cbn; unfold t_cache, kThreadObjSize; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks S)).
Proof.
img_apply (keep_cells _ (fun a => exists k, In k (st_chunks S) /\ ck_base B ly k <= a < ck_base B ly k + ck_extent k));
[img_try (intros a (k & Hk & Ha); img_exact (Z_chunk k a Hk Ha)) | img_try (acells_at 2) |].
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d).
{ intros d. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d').
{ intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg k) as [|o|r o|c'' p']; try solve [destruct GG]; cbn; img_lia. }
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by img_refl.
pose proof (req_size_bounds (ck_req k) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
clear GG. unfold chunk_cells, kChunkHeaderSize. img_apply Forall_app. split.
- repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z1 z2 z4 c1 c2 c4]; intros kk Hkk; cbn in Hkk; exists k; split; [img_exact Hk|]; rewrite ?EA2, ?EA, ?EA0; img_lia)|]). img_apply Forall_nil.
- destruct (ck_rz k =? 16); [img_try (img_apply Forall_nil)|]. repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w z8 c8]; intros kk Hkk; cbn in Hkk; exists k; split; [img_exact Hk|]; rewrite ?EA2, ?EA, ?EA0; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma cells_sec : Forall (cell_holds B ly rd') (sec_cells S).
Proof.
assert (INC : incl (sec_cells S) (acells B ly S)) by (img_try (acells_at 3)).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & PQ & _).
unfold sec_cells in *.
assert (LI : forall o, 0 <= o < 3632 -> forall k, 0 <= k < 1 -> TFX_INST <= aeval B ly (AInst o) + k < TFX_INST + 3632) by (img_try (intros o Ho k Hk; cbn; rewrite EI; img_lia)).
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons])].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval]; rewrite EI; unfold o_sec_reserved, o_sec_n, o_sec_mutex in *; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
img_apply Forall_app. split.
-
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR.
img_apply (keep_zone (ly_Q ly) kPtrArrayResv _ PQ); [img_try (intros x Hx; img_apply INC; do 3 right; img_apply in_app_iff; left; img_exact Hx)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i r] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin.
cbn. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. img_lia.
-
img_apply (keep_cells _ (fun a => exists e, In e (sec_extents ly S) /\ fst e <= a < fst e + snd e));
[img_try (intros a (e & Hex & Ha); img_exact (Z_secx e a Hex Ha)) | img_try (intros x Hx; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hx) |].
img_apply Forall_flat_map'. intros k Hk.
pose proof (chunk_facts B ly S rd0 k MA Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
destruct (ck_beg k) as [|o|r o|c' p'] eqn:Eb; try img_apply Forall_nil.
destruct GG as (_ & _ & Gbase & Gext & Gin & _).
pose proof (req_size_bounds (ck_req k) ltac:(img_try (clear - G7; img_lia))) as (_ & Q1 & _).
repeat (img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 aeval aoff]; intros kk Hkk; cbn in Hkk; eexists; split; [img_exact Gin|]; cbn [fst snd]; clear - Hkk Gbase Gext G5 G8 Q1; unfold kPage in *; img_lia)|]). img_apply Forall_nil.
Qed.
Lemma keep_batches : forall bl, incl bl (all_batches S) -> incl (batch_cells bl) (acells B ly S) -> Forall (cell_holds B ly rd') (batch_cells bl).
Proof.
pose proof HI as (P & _ & _ & _ & _ & _ & _ & _ & SP).
induction bl as [|b t IH]; intros Hincl INC; [img_try (img_apply Forall_nil)|]. cbn [batch_cells].
assert (Hb : kHighMemBeg <= ly_space ly + b_self b).
{ pose proof (wf_classes _ _ _ _ _ WF kBatchClass ltac:(img_try (unfold kBatchClass; img_lia))) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs S kBatchClass)) by (img_try (rewrite batch_offs_24; img_apply in_map_iff; exists b; split; [img_refl | img_try (img_apply Hincl; left; img_refl)])).
pose proof (proj1 (Forall_forall _ _) (wr_elems _ _ _ _ _ _ CL) x ltac:(img_try (rewrite !in_app_iff; tauto))) as [X1 X2].
assert (RO : region_off kBatchClass = 24 * 2 ^ 32) by img_refl. (subst x; cbv beta). rewrite RO in X1. clear - X1 P SP. img_lia. }
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_app; split]])].
1-3: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_high [cc] ltac:(img_try (intros y [<-|[]]; img_apply INC; cbn; tauto)) ltac:(img_try (img_apply Forall_cons; [img_try (cbn; img_lia) | img_try (img_apply Forall_nil)]))) cc (or_introl eq_refl))
end.
- img_apply keep_high; [img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; left; img_exact Hy)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i k] & <- & _). cbn. img_lia.
- img_apply IH; [img_try (intros y Hy; img_apply Hincl; right; img_exact Hy) | img_try (intros y Hy; img_apply INC; do 3 right; img_apply in_app_iff; right; img_exact Hy)].
Qed.
Lemma cells_quar : Forall (cell_holds B ly rd') (quar_cells S).
Proof.
assert (INC : incl (quar_cells S) (acells B ly S)) by (img_try (acells_at 4)).
pose proof (ts_inst B TS) as EI. pose proof HI as (_ & _ & PT & _).
unfold quar_cells, qc_cells in *. unfold o_q_cmutex, o_q_rmutex, o_q_size, t_qc in *.
img_apply Forall_cons; [|img_try (img_apply Forall_cons)].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval]; rewrite EI; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
img_apply Forall_app. split.
- do 4 (img_apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_zone (ly_T ly) kThreadObjSize [cc] PT ltac:(img_try (intros y [<-|[]]; img_apply INC; right; right; img_apply in_app_iff; left; cbn; tauto)) ltac:(img_try (img_apply Forall_cons; [img_try (cbn; unfold kThreadObjSize; img_lia) | img_try (img_apply Forall_nil)]))) cc (or_introl eq_refl)) end|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; left; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. left. do 4 right. img_exact Hy.
- do 4 (img_apply Forall_cons; [lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_inst ltac:(img_try (intros x [<-|[]]; img_apply INC; right; right; img_apply in_app_iff; right; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z1 c1]; intros k Hk; cbn [aeval aoff]; rewrite EI; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)] end|]).
img_apply keep_batches; [img_try (intros b Hb; unfold all_batches; img_apply in_app_iff; right; img_exact Hb)|].
intros y Hy. img_apply INC. right; right. img_apply in_app_iff. right. do 4 right. img_exact Hy.
Qed.
Lemma cells_fs : Forall (cell_holds B ly rd') (fs_cells S).
Proof.
pose proof HI as (_ & _ & _ & PF & _). img_apply (keep_zone (ly_F ly) kFakeStackSize _ PF); [img_try (acells_at 5)|].
unfold fs_cells. img_apply Forall_cons; [img_try (cbn; unfold kFakeStackSize; img_lia)|]. img_apply Forall_cons; [img_try (cbn; unfold kFakeStackSize; img_lia)|].
img_apply Forall_forall. intros cc Hcc. apply in_map_iff in Hcc as ([i h] & <- & Hin). apply in_combine_l in Hin. apply in_seq in Hin. cbn. unfold kFakeStackSize. img_lia.
Qed.
Lemma cells_depot : Forall (cell_holds B ly rd') (depot_cells ly S).
Proof.
assert (INC : incl (depot_cells ly S) (acells B ly S)) by (img_try (acells_at 6)).
pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
unfold depot_cells in *.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_depot ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1]; intros k Hk; cbn [aeval]; rewrite ED; unfold d_nuniq, d_map1 in *; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_store ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1]; intros k Hk; cbn [aeval]; rewrite ES; unfold s_total, s_block0 in *; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
Qed.
Lemma cells_ialloc : Forall (cell_holds B ly rd') (ialloc_cells B S).
Proof.
assert (INC : incl (ialloc_cells B S) (acells B ly S)) by (img_try (acells_at 7)).
pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_w B TS) as E2. pose proof (ts_ial_flag B TS) as E3. pose proof (ts_ial_hi B TS) as E4.
unfold ialloc_cells in *.
img_apply Forall_cons; [|img_try (img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_cons; [|img_apply Forall_nil]]])].
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_flag ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1 z1]; intros k Hk; cbn [aeval]; rewrite E3; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
1-2: lazymatch goal with |- cell_holds _ _ _ ?cc =>
refine (proj1 (Forall_forall _ _) (keep_cells [cc] _ Z_ial ltac:(img_try (intros x [<-|[]]; img_apply INC; cbn; tauto)) _) cc (or_introl eq_refl));
img_apply Forall_cons; [img_try (cbn [c_at c_w c8 z8 z4 c4 c1 z1]; intros k Hk; cbn [aeval]; rewrite E1, E2; unfold TFX_IAL_LO, TFX_IAL_W, TFX_IAL_HI; cbn in Hk; img_lia) | img_try (img_apply Forall_nil)]
end.
Qed.
Lemma cells_thread : Forall (cell_holds B ly rd') thread_cells.
Proof.
pose proof HI as (_ & _ & PT & _). img_apply (keep_zone (ly_T ly) kThreadObjSize _ PT); [img_try (acells_at 8)|].
unfold thread_cells. img_apply Forall_cons; [img_try (cbn; unfold t_unwinding, kThreadObjSize; img_lia) | img_try (img_apply Forall_nil)].
Qed.
Lemma cells_final : Forall (cell_holds B ly rd') (acells B ly S).
Proof.
unfold acells.
img_apply Forall_app; split; [img_try (img_exact cells_regions)|]. img_apply Forall_app; split; [img_try (img_exact cells_caches)|]. img_apply Forall_app; split; [img_try (img_exact cells_chunks)|].
img_apply Forall_app; split; [img_try (img_exact cells_sec)|]. img_apply Forall_app; split; [img_try (img_exact cells_quar)|]. img_apply Forall_app; split; [img_try (img_exact cells_fs)|].
img_apply Forall_app; split; [img_try (img_exact cells_depot)|]. img_apply Forall_app; split; [img_try (img_exact cells_ialloc) | img_try (img_exact cells_thread)].
Qed.
Lemma fa_final : fa_entries_ok ly rd' S.
Proof.
intros c' i vv Hc' Hi HV k Hk. pose proof HI as (P & _).
pose proof (wf_classes _ _ _ _ _ WF c' Hc') as CL. pose proof (wr_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wr_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ CL)) as F0.
pose proof (region_in_prim ly c' LY Hc') as (R1 & R2 & _).
rewrite AGX; [img_try (img_exact (am_fa _ _ _ _ MA c' i vv Hc' Hi HV k Hk)) | img_try (eapply own_fa; [img_exact MA | img_exact Hc' | clear - Hi Hk FL FB; numconst; img_lia]) |].
img_apply Z_high. unfold fa_base. unfold region_base in R1, R2. clear - Hi Hk FL FB F0 R1 R2 P. numconst. img_lia.
Qed.
Lemma flags_final : fs_flags_ok ly rd' S.
Proof.
intros cid pos Hc Hp. pose proof (flag_off_bounds cid pos Hc Hp) as FB. pose proof HI as (_ & _ & _ & PF & _).
rewrite AGX; [img_try (img_exact (am_flags _ _ _ _ MA cid pos Hc Hp)) | img_try (unfold flag_addr, kFakeFlagsOff in *; eapply own_F_low; [img_exact MA | img_lia]) |].
img_apply (Z_zone _ _ _ PF). unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. img_lia.
Qed.
Lemma depot_final : depot_ok B ly rd' S.
Proof.
pose proof (ts_depot B TS) as ED. pose proof HI as (_ & _ & _ & _ & PNB & _).
assert (IDB : depot_ids S <= 4097).
{ pose proof (wf_depot _ _ _ _ _ WF) as [ND INC]. pose proof (ts_universe B TS) as (U1' & _ & _). unfold depot_ids, DEPOT_MAX in *.
pose proof (NoDup_incl_length ND INC). img_lia. }
assert (EZ : forall a, (TFX_DEPOT <= a < TFX_DEPOT + 4 * d_tab_words) \/ (ly_NB ly + 16 <= a < ly_NB ly + kNodesBlockSize) -> rd' a = rd0 a).
{ intros a Ha. img_apply AGX.
- destruct Ha as [Ha|Ha].
+ img_apply (own_static B ly S rd0 a MA). rewrite (ts_owned B TS). unfold Tfx_owned_static. img_apply Exists_exists.
eexists. split; [img_try (right; right; right; left; img_refl)|]. unfold in_zr; cbn. unfold TFX_DEPOT, d_tab_words in Ha. img_lia.
+ img_apply (own_core B ly S rd0 (ly_NB ly, kNodesBlockSize) a MA); [img_try (unfold core_extents; cbn; tauto) | img_try (cbn [fst snd]; img_lia)].
- destruct Ha as [Ha|Ha]; [img_try (img_apply Z_depot; unfold d_tab_words in *; img_lia) | img_try (img_apply (Z_zone _ _ _ PNB); img_lia)]. }
unfold depot_ok, depot_ids, depot_traces in *.
destruct (am_depot _ _ _ _ MA) as (heads & links & H1 & H2 & H3). exists heads, links. split; [|img_try (split; [|img_exact H3])].
- intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [img_try (img_exact Hh)|]. intros k Hk. rewrite EZ; [img_try (img_exact (Hr k Hk))|]. left. rewrite ED. unfold d_tab_words in *. img_lia.
- intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [img_try (img_exact L1)|]. split.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L2 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
+ intros k Hk. rewrite EZ; [img_try (img_exact (L3 k Hk))|]. right. unfold kNodesBlockSize. img_lia.
Qed.
Lemma shadow_final : shadow_ok B ly rd' S.
Proof.
intros g vv Hg8 HV.
rewrite AGX; [img_try (img_exact (am_shadow _ _ _ _ MA g vv Hg8 HV)) | img_try (img_exact (ashadow_owned B ly S rd0 g vv MA HV)) |].
img_apply Z_shadow. unfold shadow_addr.
unfold ashadow in HV. destruct (find_chunk_at B ly (st_chunks S) g) as [k0|] eqn:F0.
- apply find_chunk_at_In in F0 as [Hk0 Hg0]. pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _).
pose proof (Z.div_pos g 8). clear - Hg0 C1 H. unfold in_app in C1. numconst. img_lia.
- destruct (in_rangesb g (fa_poison_ranges ly S)) eqn:IR; [|img_try (discriminate)].
apply in_rangesb_true in IR as (lo & len & Hin & Hlo). pose proof HI as (P & _).
assert (0 <= g); [|img_try (pose proof (Z.div_pos g 8); img_lia)].
unfold fa_poison_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
+ apply in_flat_map in Hin as (c' & Hc' & Hin). apply zseq_In in Hc'.
pose proof (region_in_prim ly c' LY ltac:(img_lia)) as (R1 & R2 & _).
pose proof (region_off_eq c' ltac:(img_lia)) as RO.
destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold fa_base, region_base in *; rewrite RO in *; clear - Hlo R1 R2 P Hc'; numconst; img_lia.
+ apply in_flat_map in Hin as (k0 & Hk0 & Hin). pose proof (chunk_facts B ly S rd0 k0 MA Hk0) as (C1 & C2 & _ & _ & _ & _ & _ & _ & GG).
destruct (ck_beg k0) as [|o|r o|c'' p']; try solve [destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
destruct GG as (_ & _ & Gbase & Gext & _). clear - Hlo C1 C2 Gbase Gext. unfold in_app in C1. numconst. unfold kPage in *. img_lia.
Qed.
Lemma zshadow_final : zshadow_ok B ly rd'.
Proof.
unfold zshadow_ok. img_apply Forall_forall. intros r Hr i Hi. unfold shadow_of_addr. img_change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
rewrite AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (am_zshadow _ _ _ _ MA) r Hr i Hi)) | img_try (eapply own_shadow_zero; [img_exact MA | img_exact Hr | img_exact Hi]) |].
img_apply Z_shadow. unfold shadow_addr.
assert (0 <= fst r); [|img_try (pose proof (Z.div_pos (fst r) 8); img_lia)].
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr].
- cbn [fst]. pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). clear - T7. numconst. img_lia.
- img_exact (proj1 (proj1 (Forall_forall _ _) (aso_zshadow _ (am_syms _ _ _ _ MA)) r Hr)).
Qed.
Lemma vis_final : Forall (range_vis B ly rd') (ajunk B ly S) /\ Forall (range_vis B ly rd') (aareas S) /\ Forall (range_vis B ly rd') (aclient S).
Proof.
split; [|img_try (split)]; (eapply Forall_range_vis_keep; [img_try (img_exact VIS)|]); [img_try (img_exact (am_junk _ _ _ _ MA)) | img_try (img_exact (am_areas _ _ _ _ MA)) | img_try (img_exact (am_client _ _ _ _ MA))].
Qed.
Definition abs_cell_okJ {imgk : img} (cc : acell) : bool :=
match c_at cc with
| ANum a => (a + Z.max 1 (Z.of_nat (c_w cc)) <=? TFX_OOM) || (TFX_OOM + 1 <=? a)
| _ => false
end.
Lemma abs_cells_okJ : forallb abs_cell_okJ (Tfx_const_abs ++ Tfx_const_shadow) = true.
Proof. img_case; lazymatch goal with |- _ = ?r_ => vm_cast_no_check (@eq_refl _ r_) end. Qed.
Lemma const_final : Forall (cell_holds B ly rd') (as_const B ly).
Proof.
img_apply Forall_forall. intros cc Hin.
img_apply (YG0w.cell_holds_agree B ly rd0); [img_try (img_exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ MA) cc Hin))|].
intros k Hk. img_apply AGX; [img_try (img_exact (proj1 (Forall_forall _ _) (const_cells_owned B ly S rd0 MA) cc Hin k Hk))|].
rewrite (ts_const B TS ly) in Hin. unfold Tfx_const in Hin. apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfx_const_sym in Hin. cbn [In] in Hin. pose proof HI as (P & PQ & PT & PF & PNB & PSB & PC & PD & SP).
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof (am_tsd _ _ _ _ MA) as ETSD. rewrite (ts_tsd B TS) in ETSD.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [img_try (cbn [c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD in *;
first [ img_apply Z_high; clear - Hk P SP; numconst; img_lia
| img_apply (Z_zone _ _ _ PT); clear - Hk; numconst; img_lia
| img_apply (Z_zone _ _ _ PC); clear - Hk; numconst; img_lia
| img_apply (Z_zone _ _ _ PD); clear - Hk; numconst; img_lia
| img_apply (Z_zone _ _ _ PF); clear - Hk; numconst; unfold kFakeStackSize; img_lia
| img_apply (Z_zone _ _ _ PQ); clear - Hk; numconst; unfold kPtrArrayResv; img_lia
| img_apply Z_tls; clear - Hk; img_lia
| img_apply Z_inst; clear - Hk; unfold o_space, o_rinfo, o_sec_chunks; img_lia ]) |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okJ cc Hin) as Hc. unfold abs_cell_okJ in Hc.
destruct (c_at cc) eqn:Ea; try discriminate. cbn [aeval].
apply Bool.orb_prop in Hc as [Hc|Hc]; apply Z.leb_le in Hc; unfold XJ; img_lia.
Qed.
Theorem AR_oom : AR tfxsegs B ly S W mem' md'.
Proof.
pose proof HAR as (M0 & L & BUD & MW & HS0).
split; [|img_try (split; [|split; [|split]])].
- destruct M0 as [Mwf Mun Msy Mly Mpl Mco Mcow Mce Mfa Mfl Mde Msh Mzs Mju Mar Mcl Mze Mts Msi].
constructor.
+ img_exact Mwf.
+ img_exact Mun.
+ img_exact Msy.
+ img_exact Mly.
+ img_exact Mpl.
+ img_exact const_final.
+ img_exact Mcow.
+ img_exact cells_final.
+ img_exact fa_final.
+ img_exact flags_final.
+ img_exact depot_final.
+ img_exact shadow_final.
+ img_exact zshadow_final.
+ img_exact (proj1 vis_final).
+ img_exact (proj1 (proj2 vis_final)).
+ img_exact (proj2 (proj2 vis_final)).
+
img_apply Forall_forall. intros r Hr i Hi. rewrite <- (proj1 (Forall_forall _ _) Mze r Hr i Hi). img_apply AGX.
* pose proof (aso_ialloc _ Msy) as [I1 I2].
eapply (own_area B ly S rd0 (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [img_try (img_exact MA) | img_try (cbn; tauto) |].
unfold ialloc_zero in Hr. cbn [fst snd]. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; img_lia.
* img_apply Z_ial. unfold ialloc_zero in Hr. pose proof (ts_ial_lo B TS) as E1. pose proof (ts_ial_hi B TS) as E2. pose proof (ts_ial_w B TS) as E3.
destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; rewrite ?E1, ?E2, ?E3 in *; unfold TFX_IAL_LO, TFX_IAL_HI, TFX_IAL_W in *; img_lia.
+ img_exact Mts.
+   img_exact Msi.
- eapply ALedger_same; [img_try (img_exact L) | img_try (img_exact Hvm) | img_try (img_exact Hlz) | img_try (img_exact He)].
- img_exact BUD.
- img_exact (amwf_same md md' Hvm Hlz MW).
- img_exact (ahs_transfer tfxsegs B ly S S (w_H W) mem mem' (al_img_env tfxsegs ly S md LY L) M0 HS0 VIS HK ltac:(img_try (intros a _ C; img_exact C)) eq_refl
ltac:(img_try (intros g Hg Happ HF _; img_apply AGX; [img_try (eapply hfree_shadow_owned; [img_exact M0 | img_exact Hg | img_exact Happ | img_exact HF])
| img_try (pose proof (shadow_addr_band_rw g Happ) as SB; unfold XJ; clear - SB; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_OOM in *; img_lia)]))).
Qed.
End f.
End c.
