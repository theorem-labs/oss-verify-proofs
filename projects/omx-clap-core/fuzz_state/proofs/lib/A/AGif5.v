(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGif5.v (a working branch 84ee52cd012, file sha256 079585b7ae98) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 22 image addresses moved by code-verified function pairs (77 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: the low shadow band of the constant cells ends at 0x800b4000 (the page above fs's last constant shadow cell, which ends at 0x800b34c4; AF0m.v Tfib_const_shadow), as in fs's AFju.v, instead of the donor's 0x80050000 (the relocation tool had moved it to 0x80050398); two image addresses the tool left at their cgif values are moved as in fs's AFju.v / AFjz.v: 667336 (0xa2ec8) -> 674696 (0xa4b88) and the second 0xa5ad0 of the owned static range -> 0xa7790; fs's depot invariant (FS-INSTANCE.md 1.3, L): depot_ids_boundS takes depot_inv and gives 20481 (AFix.v:357-361 form), depot_ids_after and depot_mem_ok_agreeS are at 20482; the instance's trace premise is fs's `fun tr S => tr_admit (as_universe B) S tr` (FS-INSTANCE.md 1.4, L) in ifaceS_cgif / ifaceS_cgif_w and in depot_S / post_null_S / post_model / post_grant_g / post_grant_S (fs's YG07.malloc_ok takes tr_admit), and depot_S gives the depot callee fs's areq_ok premise by YG01.tr_admit_len. *)
(* The cgif_file instance of the SECONDARY interface AGif4.AIfaceS: ARX = ARX_cgif (inst = TFIB_INST /\ AR),
   AOX = aowned, rpre = aregime /\ qmeter, mt = malloc, lpost = qtight and AGif1's depot post dpost_cgif.  It is the
   secondary twin of AGif1.iface_cgif.  The fields come from the released secondary route:
   - the view from the ARm facts AGjv reads (cell_lit / cell_sym / cell_state / vis_present, ws_reserved);
   - the shape from AGk0.malloc_secondary_eq, freshness from AFib.KS_fresh;
   - the depot callee from tfib_depot_spec, by AGju.D1W_ok's script with the world free;
   - the kernel fields from AR's ledger and wf (YG08.mroom_slack as in AGjs.slackS, AFia.sec_grant_exists_AR,
     AFia.grant_zone / grant_apart / grant_shadow_zero);
   - the refusal post from AGic.AR_snull and AR_tick (AGk0.refuseS);
   - the grant post from AGjy.AR_transport, with the ledger of the grown layout as in AGk0.LED0 / LED1 and the
     frame clause as in AGjz.LEAF_S; Wf and qtight of the final state from YG07.malloc_ok / YG0d.atok_apath_flag
     along the granted path of the tree. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG08 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0b YG0g YG0h YG0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1h AF0l AF0m AF0x AFl0 AFia AFib.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YF06.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK0v YK13 YP0n YA05 YA09.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFff.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhy AGhy AGi9 AGjm AFi3 AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AGif0n AGif2 AGif4 AllocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif AGif1 AGic AGjy.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif AGif4cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require ImgBase ImgBaseAG ImgBaseAGS.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
(* AGjm.size_facts at cgif's own bound: AGjm states it for n < AGi9.SEC_NMAX; at n < MALLOC_MAX the rounded size
   and the map keep their old bounds (a multiple of 8, resp. of a page, below n + 8, resp. n + 12296). *)
Lemma size_facts_m : forall n, 64513 <= n < MALLOC_MAX ->
64520 <= AGjm.R8v n <= MALLOC_MAX /\ AGjm.R8v n mod 8 = 0 /\ n <= AGjm.R8v n < n + 8 /\
64512 <= AGjm.N8D n <= n /\ AGjm.N8D n mod 8 = 0 /\ n < AGjm.N8D n + 8 /\
AGjm.NDv n = AGjm.R8v n + 4096 /\ 73728 <= AGjm.MSv n <= MALLOC_MAX + 8192 /\ AGjm.MSv n mod 4096 = 0 /\
AGjm.NDv n + 4096 <= AGjm.MSv n < AGjm.NDv n + 8192 /\
0 <= AGjm.TLv n <= 4088 /\ AGjm.TLv n mod 8 = 0 /\ 2048 <= AGjm.RLv n <= 2048 + 4088 /\ AGjm.RLv n mod 8 = 0.
Proof.
intros n Hn. pose proof (AGjm.size_facts n (nrange_sec n Hn)) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14).
assert (R8m : AGjm.R8v n <= MALLOC_MAX).
{ pose proof Z2 as Q. apply Z.mod_divide in Q as [q Hq]; [|lia]. unfold MALLOC_MAX in *. lia. }
assert (MSm : AGjm.MSv n <= MALLOC_MAX + 8192).
{ pose proof Z9 as Q. apply Z.mod_divide in Q as [p Hp]; [|lia]. unfold MALLOC_MAX in *. lia. }
repeat split; lia.
Qed.
(* At cgif's sizes the map has at most 65538 pages, so the by_size_log index stays at most 28: the instance's
   cell BSLv stays in AGic.AR_snull's window (INSTv + 296 .. INSTv + 392), below the walk's wider bound. *)
Lemma LGv_m : forall n, 64513 <= n < MALLOC_MAX -> AGjm.LGv n <= 28.
Proof.
intros n Hn. pose proof (size_facts_m n Hn) as (_ & _ & _ & _ & _ & _ & _ & Z8 & _).
unfold AGjm.LGv. unfold MALLOC_MAX in Z8.
assert (Hp : 18 <= AGjm.MSv n / 4096 <= 65538) by (split; [apply Z.div_le_lower_bound; lia | apply Z.div_le_upper_bound; lia]).
pose proof (Z.log2_le_mono (AGjm.MSv n / 4096) 65538 ltac:(lia)) as L2.
rewrite (eq_refl : Z.log2 65538 = 16) in L2. lia.
Qed.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].

(* A byte of a val_mem fact, read through aview (AGk0.val_mem_aview). *)
Lemma vm_aview : forall (Hh : word -> bool) m a (w : nat) v k, val_mem tfibsegs (mrestrict Hh m) a w v -> (k < w)%nat ->
aview tfibsegs Hh m (a + Z.of_nat k) = Some (YG0f.le_byte v w k).
Proof.
intros Hh m a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal.
apply unsigned_lit_small8. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma vm_view_some : forall (Hh : word -> bool) m base (w : nat) v u, val_mem tfibsegs (mrestrict Hh m) base w v ->
base <= u < base + Z.of_nat w -> aview tfibsegs Hh m u <> None.
Proof.
intros Hh m base w v u HV Hu. replace u with (base + Z.of_nat (Z.to_nat (u - base))) by lia.
rewrite (vm_aview Hh m base w v (Z.to_nat (u - base)) HV ltac:(lia)). discriminate.
Qed.
Lemma apresent_view : forall (Hh : word -> bool) m u, apresent Hh m u -> aview tfibsegs Hh m u <> None.
Proof. intros Hh m u [Hh0 [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh0, Hb. cbn. discriminate. Qed.
(* The image's read-write window is always visible (AB1h.tfib_rw_window). *)
Lemma rw_view : forall (Hh : word -> bool) m a, 0x9f000 <= a < 0x5fd000 -> aview tfibsegs Hh m a <> None.
Proof.
intros Hh m a Ha. apply AFib.writable_visible; [lia|]. unfold writable_at. change tfibsegs with AB1h.TSEGS.
apply AB1h.tfib_rw_window. rewrite unsigned_lit_small by lia. exact Ha.
Qed.
Lemma zr_dec : forall lo hi a : Z, (lo <= a < hi) \/ ~ (lo <= a < hi).
Proof. intros lo hi a. lia. Qed.

Section b.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model facts of AR.                                                                                               *)
Section m.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model).
Hypothesis HAR : AR tfibsegs B ly S W mem md.

(* The owned extents are in the heap bands (AGic.ZI). *)
Lemma ar_zone : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e).
Proof.
intros e Hex. pose proof (am_layout _ _ _ _ (proj1 HAR)) as LY. pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG.
pose proof (proj1 (Forall_forall _ _) (lo_app ly LY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly LY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)).
Qed.
Lemma ar_zones : zone3 (ly_Q ly) kPtrArrayResv /\ zone3 (ly_T ly) kThreadObjSize.
Proof.
split; [exact (ar_zone (ly_Q ly, kPtrArrayResv) ltac:(unfold owned_extents; cbn [In]; tauto))
| exact (ar_zone (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn [In]; tauto))].
Qed.

(* The thread object's fixed cell and the secondary allocator's cells of the model (AGjv.cell_state). *)
Lemma ar_cell_state : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w x.
Proof.
intros c e w x Hin ->. apply (cell_holds_val_mem B ly (w_H W) mem e w (ANum x)).
exact (proj1 (Forall_forall _ _) (am_cells _ _ _ _ (proj1 HAR)) _ Hin).
Qed.
Lemma ar_sec_in : forall c, In c (sec_cells S) -> In c (acells B ly S).
Proof. intros c Hc. unfold acells. do 3 (apply in_or_app; right). apply in_or_app. left. exact Hc. Qed.

(* A junk or area range of the model is visible; off the image, its bytes are present (AGjv.vis_present). *)
Lemma ar_range_view : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros e len a Hin Ha.
assert (RV : range_vis B ly (aview tfibsegs (w_H W) mem) (e, len)).
{ destruct Hin as [Hin|Hin]; [exact (proj1 (Forall_forall _ _) (am_junk _ _ _ _ (proj1 HAR)) _ Hin) | exact (proj1 (Forall_forall _ _) (am_areas _ _ _ _ (proj1 HAR)) _ Hin)]. }
specialize (RV (a - aeval B ly e) ltac:(cbn [snd]; lia)). cbn [fst] in RV. replace (aeval B ly e + (a - aeval B ly e)) with a in RV by lia. exact RV.
Qed.
Lemma ar_range_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem a.
Proof.
intros e len a Hin Ha Ho. pose proof (ar_range_view e len a Hin Ha) as V. unfold aview in V.
destruct (mbyte tfibsegs (mrestrict (w_H W) mem) a) as [b|] eqn:E; [|exfalso; exact (V eq_refl)].
exact (mbyte_off_apresent (w_H W) mem a b Ho E).
Qed.

(* The out-of-memory byte, the thread object's write windows and the instance object are the allocator's
   (AGk0.oom_owned, AGjz.OWN_T / OWN_I), errno is not (AGk0.errno_not_owned). *)
Lemma ar_oom_owned : aowned B ly S TFIB_OOM.
Proof.
apply (own_area B ly S _ (as_oom_byte B, 1) TFIB_OOM (proj1 HAR)); [unfold asyms_areas; cbn; tauto|].
cbn [fst snd]. rewrite (ts_oom B TS). lia.
Qed.
Lemma ar_T_owned : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> aowned B ly S a.
Proof. intros a Ha. apply (own_core B ly S _ (ly_T ly, kThreadObjSize) a (proj1 HAR)); [unfold core_extents; cbn; tauto | exact Ha]. Qed.
Lemma ar_inst_owned : forall a, TFIB_INST <= a < 0xa7788 -> aowned B ly S a.
Proof.
intros a Ha. apply (own_static B ly S _ a (proj1 HAR)). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
exists (0xa48d8, 0xa7788 - 0xa48d8). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd]. unfold TFIB_INST in Ha. lia.
Qed.
Lemma ar_errno_not_owned : forall a, TFIB_ERRNO <= a < TFIB_ERRNO + 4 -> ~ aowned B ly S a.
Proof.
intros a Ha O.
assert (IMGa : in_img tfibsegs a).
{ unfold in_img. change tfibsegs with AB1h.TSEGS. unfold AB1h.TSEGS. eexists. split; [do 3 right; left; reflexivity|]. cbn. unfold TFIB_ERRNO in Ha. lia. }
apply (proj1 (AR_owned_image_law_ok tfibsegs B ly S W mem md a HAR IMGa)) in O.
rewrite (ts_owned B TS) in O. unfold Tfib_owned_static in O. apply Exists_exists in O as (r & Hr & [X1 X2]). cbn [In] in Hr. unfold TFIB_ERRNO in Ha.
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [cbn [fst snd] in X1, X2; lia|] | False => destruct Hr end.
Qed.
End m.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* (c) the kernel fields.                                                                                           *)
Lemma mwf_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md -> amwf md.
Proof. intros ly S W mem md (_ & _ & _ & MW & _). exact MW. Qed.

Lemma room_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md -> qmeter S ->
eager_used md + A_bytes (w_A W) + 2 ^ 30 <= vm_limit (m_vmmaps md).
Proof.
intros ly S W mem md HAR HQ. pose proof HAR as (M & L & [AB0 _] & _ & _).
pose proof (mroom_slack tfibsegs (as_universe B) ly S md md (A_bytes (w_A W)) (A_bytes (w_A W)) 0 (am_wf _ _ _ _ M) L AB0
(qmeter_room S HQ) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)) as MS.
unfold VM_HEAD in MS. lia.
Qed.

Lemma ledger_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
vm_reserved (m_vmmaps md) = segments_reserved tfibsegs /\
(forall sg, In sg tfibsegs -> 4096 <= Z.of_N (seg_base sg) /\ Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <= kImgEnd) /\
In (wiv (ly_Q ly, kPtrArrayResv)) (vm_maps (m_vmmaps md)) /\
YM05.ceil_of_top (alloc_top (m_vmmaps md)).
Proof.
intros ly S W mem md (M & L & _). pose proof (am_layout _ _ _ _ M) as LY.
split; [exact (al_reserved _ _ _ _ L)|]. split; [exact (al_img_env tfibsegs ly S md LY L)|].
split; [exact (al_Q _ _ _ _ L) | exact (al_top _ _ _ _ L)].
Qed.

(* The model the kernel node asks, with the walk's materialized pages: its ledger and wf are AR's (AGk0.LN / MWN). *)
Lemma ledger_wvb : forall ly S md mat, ALedger tfibsegs ly S md -> ALedger tfibsegs ly S (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros ly S md mat L. exact (ALedger_same tfibsegs ly S md _ L (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)). Qed.
Lemma amwf_wvb : forall md mat, amwf md -> amwf (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros md mat MW. exact (amwf_same md _ (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW). Qed.

Lemma grant_AR : forall ly S W mem md mat sz, AR tfibsegs B ly S W mem md -> 0 < sz <= YF06.NOB ->
exists a, grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true.
Proof.
intros ly S W mem md mat sz (M & L & _ & MW & _) Hsz.
exact (AFia.sec_grant_exists_AR B ly S _ _ sz M (ledger_wvb ly S md mat L) (amwf_wvb md mat MW) Hsz).
Qed.

Lemma apart_AR : forall ly S W mem md mat sz (a : word), AR tfibsegs B ly S W mem md ->
0 < sz <= MALLOC_MAX + 4 * 4096 -> sz mod 4096 = 0 ->
grant_ok_na_pin (with_vm_backing (m_vm_lazy md) mat md) a sz = true ->
zone3 (bv_unsigned a) sz /\
Forall (zdisjoint (bv_unsigned a, sz)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S) /\
(forall g, g mod 8 = 0 -> bv_unsigned a <= g -> g + 8 <= bv_unsigned a + sz ->
   mem (Z_to_bv 64 (shadow_addr g)) = Some (Z_to_bv 8 0)).
Proof.
intros ly S W mem md mat sz a (M & L & _ & _ & [_ HZ]) Hsz Hal HG. pose proof (ledger_wvb ly S md mat L) as LN.
split; [exact (AFia.grant_zone B ly S _ _ a sz M LN Hsz Hal HG)|].
split; [exact (AFia.grant_apart B ly S _ _ a sz M LN Hsz Hal HG)|].
intros g Hg G1 G2. exact (AFia.grant_shadow_zero B ly S _ _ a sz M LN Hsz Hal HG mem g HZ Hg G1 G2).
Qed.

Lemma fresh_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
forall k', In k' (st_chunks S) -> sptr_eqb (ck_beg k') (PSec (length (st_secs S)) kPage) = false.
Proof. intros ly S W mem md (M & _). exact (AFib.KS_fresh S (as_universe B) 0 0 0 (am_wf _ _ _ _ M)). Qed.

(* (b) the tree at a secondary size (AGk0.malloc_secondary_eq). *)
Lemma shape_S : forall n tr S, 64513 <= n < MALLOC_MAX -> from_primary n = false ->
malloc n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) 3 ;;
                 ob <- sec_alloc n ;; ImgBaseAGS.malloc_K_t 12 n tr ob) S.
Proof. intros n tr S _ FP. unfold malloc, ImgBaseAGS.malloc_K_t. rewrite FP. reflexivity. Qed.

(* (a) The view (AGif2.sview) of an AR pre-state at the cgif instance: the released ARm facts AGjv reads
   (cell_lit / cell_sym for the instance's constant cells, cell_state for the counters and the unwinding flag,
   vis_present for the stats windows and the committed pointer array, ws_reserved for the counters' bounds). *)
Lemma view_AR : forall ly S W mem md, AR tfibsegs B ly S W mem md ->
sview B W ly TFIB_INST mem (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S).
Proof.
intros ly S W mem md HAR. pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LY.
pose proof (img_cover_of_ledger ly S md (proj1 (proj2 HAR))) as IMG. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (ts_inst B TS) as EI. pose proof (ar_zones ly S W mem md HAR) as [ZQ ZT].
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ WF)) as [_ WA].
assert (CL : forall a w x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a w x) by (intros a w x E; exact (tfib_const_lookup B TS ly S (w_H W) mem a w x M E)).
assert (CY : forall e w e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (aeval B ly e) w (aeval B ly e'))
by (intros e w e' E; exact (tfib_const_lookup_sym B TS ly S (w_H W) mem e w e' M E)).
assert (MTX0 : val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_sec_mutex) 1 0).
{ replace (TFIB_INST + o_sec_mutex) with (aeval B ly (AInst o_sec_mutex)) by (cbn; rewrite EI; reflexivity).
  eapply (ar_cell_state ly S W mem md HAR); [apply (ar_sec_in ly S); right; right; left; reflexivity | reflexivity]. }
assert (MTX1 : val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_sec_mutex + 1) 1 0) by (apply CL; vm_compute; reflexivity).
assert (MTX2 : val_mem tfibsegs (mrestrict (w_H W) mem) (TFIB_INST + o_sec_mutex + 2) 2 0) by (apply CL; vm_compute; reflexivity).
assert (OFFT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a ZT Ha)).
assert (OFFQ : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a ZQ Ha)).
constructor.
all: cbn [ImgBase.im_segs ImgBase.im_tp ImgBase.im_tsd ImgBase.im_oom ImgBase.im_errno ImgBase.im_img_cover AImg_cgif].
- exact LY.
- exact IMG.
- rewrite (am_tsd _ _ _ _ M). exact (ts_tsd B TS).
- exact (am_const _ _ _ _ M).
- replace (TFIB_INST + o_space) with (aeval B ly (AInst o_space)) by (cbn; rewrite EI; reflexivity).
  replace (ly_space ly) with (aeval B ly (ASp 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- replace (TFIB_INST + o_sec_chunks) with (aeval B ly (AInst o_sec_chunks)) by (cbn; rewrite EI; reflexivity).
  replace (ly_Q ly) with (aeval B ly (AQ 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- replace (TFIB_INST + 80) with (aeval B ly (AInst 80)) by (cbn; rewrite EI; reflexivity).
  replace (ly_Q ly) with (aeval B ly (AQ 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- replace (TFIB_INST + o_sec_reserved) with (aeval B ly (AInst o_sec_reserved)) by (cbn; rewrite EI; reflexivity).
  eapply (ar_cell_state ly S W mem md HAR); [apply (ar_sec_in ly S); left; reflexivity | reflexivity].
- replace (TFIB_INST + o_sec_n) with (aeval B ly (AInst o_sec_n)) by (cbn; rewrite EI; reflexivity).
  eapply (ar_cell_state ly S W mem md HAR); [apply (ar_sec_in ly S); right; left; reflexivity | reflexivity].
- intros k Hk. destruct k as [|[|[|[|k]]]]; [| | | | lia].
  + rewrite (MTX0 0%nat ltac:(lia)). reflexivity.
  + replace (TFIB_INST + o_sec_mutex + Z.of_nat 1) with (TFIB_INST + o_sec_mutex + 1 + Z.of_nat 0) by lia.
    rewrite (MTX1 0%nat ltac:(lia)). reflexivity.
  + replace (TFIB_INST + o_sec_mutex + Z.of_nat 2) with (TFIB_INST + o_sec_mutex + 2 + Z.of_nat 0) by lia.
    rewrite (MTX2 0%nat ltac:(lia)). reflexivity.
  + replace (TFIB_INST + o_sec_mutex + Z.of_nat 3) with (TFIB_INST + o_sec_mutex + 2 + Z.of_nat 1) by lia.
    rewrite (MTX2 1%nat ltac:(lia)). reflexivity.
- replace (ly_T ly + t_unwinding) with (aeval B ly (AT t_unwinding)) by reflexivity.
  eapply (ar_cell_state ly S W mem md HAR); [|reflexivity]. unfold acells. do 8 (apply in_or_app; right). left. reflexivity.
- intros a Ha. destruct (Z_lt_le_dec a (ly_T ly + t_stats)) as [L|L].
  + apply (ar_range_present ly S W mem md HAR (AT t_cache_stats) (t_stats - t_cache_stats) a).
    * left. unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto.
    * cbn [aeval]. unfold t_cache_stats, t_stats in *. lia.
    * apply OFFT. unfold t_cache_stats, t_unwinding, kThreadObjSize in *. lia.
  + apply (ar_range_present ly S W mem md HAR (AT t_stats) (t_unwinding - t_stats) a).
    * left. unfold ajunk. right; right. do 5 (apply in_or_app; right). apply in_or_app; left. unfold thread_junk. cbn. tauto.
    * cbn [aeval]. unfold t_stats, t_unwinding in *. lia.
    * apply OFFT. unfold t_cache_stats, t_unwinding, kThreadObjSize in *. lia.
- intros a Ha. apply rw_view. unfold TFIB_INST, o_sec_stats, o_sec_mutex in *. lia.
- intros a Ha. apply rw_view. unfold TFIB_INST, o_comb_stats in *. lia.
- intros a Ha. apply (ar_range_present ly S W mem md HAR (AQ 0) (8 * st_sec_reserved S) a).
  + right. unfold aareas. apply in_app_iff. right. left. reflexivity.
  + cbn [aeval]. lia.
  + apply OFFQ. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv in *. lia.
- unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia.
- split; [unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *; lia | exact WA].
Qed.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* The depot callee at a later world (ifs_depot): the released AGju.D1W_ok script, with the world free.             *)
(* The mutex's pad bytes, and the const-cell zone CZS of the secondary walk (AGju.padb / abs_cell_okS / const_cells_CZ at
   the cgif instance). *)
Definition padbI (c : acell) : bool :=
match c_at c with ANum a => (TFIB_INST + o_sec_mutex + 1 <=? a) && (a + Z.max 1 (Z.of_nat (c_w c)) <=? TFIB_INST + o_sec_mutex + 4) | _ => false end.
Definition abs_cell_okS (c : acell) : bool :=
match c_at c with
| ANum a => let e := a + Z.max 1 (Z.of_nat (c_w c)) in
(0x10000 <=? a) && (((e <=? 0x5fd000) && ((e <=? TFIB_INST + o_sec_reserved) || (TFIB_INST + o_sec_sorted + 1 <=? a))
&& ((e <=? TFIB_INST + o_sec_stats) || (TFIB_INST + o_sec_stats + 32 <=? a))
&& ((e <=? TFIB_INST + 296) || (TFIB_INST + 408 <=? a))
&& ((e <=? TFIB_INST + o_sec_mutex) || (TFIB_INST + o_sec_mutex + 4 <=? a))
&& ((e <=? 0xa4b88) || (0xa4bb0 <=? a)))
|| ((0x7fff8000 <=? a) && (e <=? 0x800b4000))
|| ((TFIB_INST + o_sec_mutex + 1 <=? a) && (e <=? TFIB_INST + o_sec_mutex + 4)))
| _ => false
end.
Lemma abs_cells_okS : forallb abs_cell_okS (Tfib_const_abs ++ Tfib_const_shadow) = true.
Proof. vm_compute. reflexivity. Qed.
(* AGif4.CZS at the cgif instances, with its image addresses as numbers (cbn leaves AGjm.SHBv folded). *)
Definition CZSc (ly : alayout) (inst a : Z) : Prop :=
((0x10000 <= a < inst + o_sec_reserved) \/ (inst + o_sec_sorted + 1 <= a < inst + o_sec_stats) \/
 (inst + o_sec_stats + 32 <= a < inst + 296) \/ (inst + 408 <= a < inst + o_sec_mutex) \/
 (inst + o_sec_mutex + 4 <= a < inst + o_comb_stats) \/ (inst + o_comb_stats + 40 <= a < 0x5fd000)) \/
(0x7fff8000 <= a < 0x800b4000) \/ (ly_T ly <= a < ly_T ly + 80) \/ (ly_C ly <= a < ly_C ly + 160) \/
(TFIB_TSD <= a < TFIB_TSD + 8) \/ (ly_D ly <= a < ly_D ly + 4096).
Lemma CZS_cgif : AGif4.CZS = CZSc. Proof. reflexivity. Qed.
Lemma const_cells_CZS : forall ly, ly_tsd ly = TFIB_TSD -> forall c k, In c (as_const B ly) -> 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
if padbI c then TFIB_INST + o_sec_mutex + 1 <= aeval B ly (c_at c) + k < TFIB_INST + o_sec_mutex + 4
else AGif4.CZS ly TFIB_INST (aeval B ly (c_at c) + k).
Proof.
intros ly HTSD c k Hin Hk. rewrite (ts_const B TS ly) in Hin. unfold Tfib_const in Hin.
pose proof (ts_tp B TS) as ETP. pose proof (ts_inst B TS) as EIN. pose proof HTSD as ETSD.
clear - Hin Hk ETP EIN ETSD.
apply in_app_iff in Hin as [Hin|Hin].
- unfold Tfib_const_sym in Hin. cbn [In] in Hin. rewrite CZS_cgif. unfold CZSc.
repeat match type of Hin with
| _ \/ _ => destruct Hin as [<-|Hin]; [cbn [padbI c_at c_w aeval aoff z8 z4 z1 c8 c4 c1] in *; cbn in Hk; rewrite ?ETP, ?EIN, ?ETSD;
unfold TFIB_TP, TFIB_INST, TFIB_TSD, o_space, o_rinfo, o_sec_chunks, o_sec, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, kStackSpan in *;
first [ do 2 right; left; zlia | do 3 right; left; zlia | do 4 right; left; zlia | do 5 right; zlia
| left; left; zlia | left; do 5 right; zlia ] |]
| False => destruct Hin
end.
- pose proof (proj1 (forallb_forall _ _) abs_cells_okS c Hin) as Hc. unfold abs_cell_okS in Hc. unfold padbI.
destruct (c_at c) eqn:Ea; try discriminate. cbn [aeval]. cbv zeta in Hc.
apply andb_prop in Hc as [Hz Hc]. apply Z.leb_le in Hz.
rewrite CZS_cgif. unfold CZSc.
destruct (Z.leb_spec (TFIB_INST + o_sec_mutex + 1) z) as [P1|P1]; destruct (Z.leb_spec (z + Z.max 1 (Z.of_nat (c_w c))) (TFIB_INST + o_sec_mutex + 4)) as [P2|P2]; cbn [andb];
[ unfold TFIB_INST, o_sec_mutex in *; zlia | | |];
(apply Bool.orb_prop in Hc; destruct Hc as [Hc|Hc]; [apply Bool.orb_prop in Hc; destruct Hc as [Hc|Hc]|];
[ repeat (apply andb_prop in Hc; destruct Hc as [Hc ?X]);
repeat match goal with H : _ || _ = true |- _ => rewrite Bool.orb_true_iff, !Z.leb_le in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end;
unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *; left;
lazymatch goal with |- 0x10000 <= ?x < _ \/ _ =>
destruct (Z_lt_le_dec x (674008 + 112)) as [L1|G1]; [left; zlia|];
destruct (Z_lt_le_dec x (674008 + 136)) as [L2|G2]; [right; left; zlia|];
destruct (Z_lt_le_dec x (674008 + 296)) as [L3|G3]; [do 2 right; left; zlia|];
destruct (Z_lt_le_dec x (674008 + 680)) as [L4|G4]; [do 3 right; left; zlia|];
destruct (Z_lt_le_dec x 674696) as [L5|G5]; [do 4 right; left; zlia|];
do 5 right; zlia
end
| apply andb_prop in Hc as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2; right; left; zlia
| apply andb_prop in Hc as [H1 H2]; exfalso; first [discriminate H1 | discriminate H2 | apply Z.leb_le in H1; apply Z.leb_le in H2; unfold TFIB_INST, o_sec_mutex, o_comb_stats in *; zlia] ]).
Qed.
Lemma CZS_range : forall ly, layout_ok ly -> forall a, AGif4.CZS ly TFIB_INST a -> 0 <= a < 2 ^ 64.
Proof.
intros ly LY a Ha. pose proof (lo_app ly LY) as HA. pose proof ASAN_CEIL_range as [CR _].
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC. pose proof (Forall_nth' _ _ 7 _ HA eq_refl) as ID.
cbv beta in IT, IC, ID. cbn [fst snd] in IT, IC, ID.
rewrite CZS_cgif in Ha. unfold CZSc in Ha.
unfold in_app, TFIB_TSD, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats, kThreadObjSize, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.

(* Cells and the depot's memory facts read only their own bytes (AGix.cell_holds_agree / cell_holds_agree2 /
   depot_mem_ok_agree, AGju.depot_mem_ok_ext over AGjm.DZONE). *)
Lemma cell_holds_agree : forall ly (rd rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) -> rd' (aeval B ly (c_at c) + k) = rd (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd c -> cell_holds B ly rd' c.
Proof.
intros ly rd rd' c He Hc. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. rewrite He by lia. exact (Hc k Hk).
- destruct Hc as (b & Hb & Hm). exists b. split; [|exact Hm]. rewrite <- (Z.add_0_r (aeval B ly (c_at c))). rewrite He by lia. rewrite Z.add_0_r. exact Hb.
Qed.
Lemma cell_holds_agree2 : forall ly (rd1 rd2 rd' : reader) c,
(forall k, 0 <= k < Z.max 1 (Z.of_nat (c_w c)) ->
rd' (aeval B ly (c_at c) + k) = rd1 (aeval B ly (c_at c) + k) \/ rd' (aeval B ly (c_at c) + k) = rd2 (aeval B ly (c_at c) + k)) ->
cell_holds B ly rd1 c -> cell_holds B ly rd2 c -> cell_holds B ly rd' c.
Proof.
intros ly rd1 rd2 rd' c He H1 H2. unfold cell_holds in *. destruct (c_val c) as [e|m vv].
- intros k Hk. destruct (He (Z.of_nat k) ltac:(lia)) as [E|E]; rewrite E; [exact (H1 k Hk) | exact (H2 k Hk)].
- destruct H1 as (b1 & Hb1 & Hm1). destruct H2 as (b2 & Hb2 & Hm2).
destruct (He 0 ltac:(lia)) as [E|E]; rewrite Z.add_0_r in E; rewrite E; [exists b1 | exists b2]; tauto.
Qed.
Lemma depot_ids_boundS : forall S' nv, depot_inv (as_universe B) nv (st_depot S') -> depot_ids S' <= 20481.
Proof.
intros S' nv D. pose proof (depot_inv_cap _ _ _ (ts_universe B TS) D) as C. unfold depot_ids. unfold DEPOT_CAP in C.
clear - C. lia.
Qed.
Lemma depot_ids_after : forall S z tr, Wf (as_universe B) S -> depot_ids (depot_after z tr S) <= 20482.
Proof.
intros S z tr WF. pose proof (depot_ids_boundS S _ (wf_depot _ _ _ _ _ WF)) as DB.
unfold depot_after. destruct (z =? 0); [lia|]. unfold depot_ids in *. cbn [st_depot set_depot]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma depot_mem_ok_agreeS : forall ly S' (rd rd' : reader), depot_ids S' <= 20482 ->
(forall a, AGjm.DZONE ly a -> rd' a = rd a) -> depot_mem_ok B ly S' rd -> depot_mem_ok B ly S' rd'.
Proof.
intros ly S' rd rd' HID He (D1' & D2 & D3). pose proof (ts_depot B TS) as ED. pose proof (ts_store B TS) as ES.
assert (EZ : forall a, (TFIB_DEPOT <= a < TFIB_DEPOT + d_map1 + 8) \/ (TFIB_STORE <= a < TFIB_STORE + 32) \/
(ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize) -> rd' a = rd a).
{ intros a Ha. apply He. unfold AGjm.DZONE, TFIB_DEPOT, TFIB_STORE, d_map1 in *. lia. }
split; [|split].
- apply Forall_forall. intros c Hc. apply (cell_holds_agree ly rd); [| exact (proj1 (Forall_forall _ _) D1' c Hc)].
intros k Hk. apply EZ. unfold depot_cells in Hc. cbn in Hc.
destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; cbn [c_at c_w aeval aoff z4 z8 c4 c8] in *; cbn in Hk; rewrite ?ED, ?ES; unfold d_nuniq, d_map1, s_total, s_block0 in *; zlia.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
+ intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. rewrite EZ; [exact (Hr k Hk)|].
rewrite ED. unfold d_tab_words, d_map1 in *. zlia.
+ intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split.
* intros k Hk. rewrite EZ; [exact (L2 k Hk)|]. unfold kNodesBlockSize. zlia.
* intros k Hk. rewrite EZ; [exact (L3 k Hk)|]. unfold kNodesBlockSize. zlia.
- apply Forall_forall. intros r Hr i Hi. rewrite EZ; [exact (proj1 (Forall_forall _ _) D3 r Hr i Hi)|].
cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd aeval aoff] in *; rewrite ?ED, ?ES; unfold d_nuniq, d_map1 in *; zlia.
Qed.
Lemma depot_mem_ok_rdext : forall ly S' (rd rd' : reader), rd_ext rd rd' -> depot_mem_ok B ly S' rd -> depot_mem_ok B ly S' rd'.
Proof.
intros ly S' rd rd' Hx (D1' & D2 & D3). split; [|split].
- eapply Forall_cell_holds_ext; eassumption.
- destruct D2 as (heads & links & H1 & H2 & H3). exists heads, links. split; [|split; [|exact H3]].
+ intros b Hb. destruct (H1 b Hb) as [Hh Hr]. split; [exact Hh|]. intros k Hk. apply Hx, Hr, Hk.
+ intros id Hid. destruct (H2 id Hid) as (L1 & L2 & L3). split; [exact L1|]. split; intros k Hk; apply Hx; auto.
- eapply Forall_range_vis_ext; eassumption.
Qed.
Lemma depot_at0S : forall ly S rd, ARm B ly S rd -> depot_mem_ok B ly S rd.
Proof.
intros ly S rd HARm. split; [|split].
- apply Forall_forall. intros c Hc. apply (proj1 (Forall_forall _ _) (am_cells B ly S rd HARm)).
unfold acells. do 6 (apply in_or_app; right). apply in_or_app. left. exact Hc.
- exact (am_depot B ly S rd HARm).
- apply Forall_forall. intros r Hr. cbn in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]].
1-3: apply (proj1 (Forall_forall _ _) (am_junk B ly S rd HARm)); unfold ajunk; right; right; do 6 (apply in_or_app; right); apply in_or_app; left; cbn; tauto.
all: apply (proj1 (Forall_forall _ _) (am_areas B ly S rd HARm)); unfold aareas; do 3 (apply in_or_app; right); cbn; tauto.
Qed.
Lemma footprint_DZ : forall ly a, depot_footprint B ly a -> AGjm.DZONE ly a.
Proof.
intros ly a FP. unfold depot_footprint, AGjm.DZONE in *. rewrite (ts_depot B TS), (ts_store B TS) in FP.
unfold TFIB_DEPOT, TFIB_STORE, d_map1 in FP. lia.
Qed.
(* The depot zone is never hidden: its image part is the read-write window (AFff.rw_unhidden), its node and store
   blocks are visible model areas off the image. *)
Lemma DZ_unhidden : forall ly S W mem md, AR tfibsegs B ly S W mem md -> forall a, AGjm.DZONE ly a -> w_H W (Z_to_bv 64 a) = false.
Proof.
intros ly S W mem md HAR a Ha. unfold AGjm.DZONE in Ha. destruct Ha as [Ha|[Ha|Ha]].
- apply AFff.rw_unhidden. lia.
- refine (proj1 (ar_range_present ly S W mem md HAR (ANB 0) kNodesBlockSize a _ _ _)).
  + right. unfold aareas. do 3 (apply in_or_app; right). cbn. tauto.
  + cbn [aeval]. lia.
  + exact (zone3_off_img _ _ a (ar_zone ly S W mem md HAR (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn [In]; tauto)) Ha).
- refine (proj1 (ar_range_present ly S W mem md HAR (ASB 0) kStoreBlockSize a _ _ _)).
  + right. unfold aareas. do 3 (apply in_or_app; right). cbn. tauto.
  + cbn [aeval]. lia.
  + exact (zone3_off_img _ _ a (ar_zone ly S W mem md HAR (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn [In]; tauto)) Ha).
Qed.

Lemma depot_S : tfib_depot_spec B ->
forall inst ly S W mem0 md0 tr (Wy : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
(inst = TFIB_INST /\ AR tfibsegs B ly S W mem0 md0) -> tr_admit (as_universe B) S tr ->
(forall x : word, w_H W x = false -> w_H Wy x = false) ->
(forall x : word, AGjm.DZONE ly (bv_unsigned x) \/ AGif4.CZS ly inst (bv_unsigned x) -> mem x = mem0 x) ->
(forall k, 1 <= k < 4 -> aview tfibsegs (w_H Wy) mem (inst + o_sec_mutex + k) = Some 0) ->
getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H Wy) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
(forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H Wy) mem a) ->
SRr tfibsegs Wy (mkCfg (mkst regs (Z_to_bv 64 A_StackDepotPut) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = Wy /\ exists z regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\
  (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
     ~ AGjm.DZONE ly (bv_unsigned x) -> mem' x = mem x) /\
  (forall a, apresent (w_H Wy) mem a -> apresent (w_H Wy) mem' a) /\
  dpost_cgif B inst ly S W tr z mem').
Proof.
intros HD1 inst ly S W mem0 md0 tr Wy regs mem md buf [-> HAR] Htr MONy MEQ MUT0 R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES.
pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LY. pose proof (img_cover_of_ledger ly S md0 (proj1 (proj2 HAR))) as IMG.
pose proof (am_wf _ _ _ _ M) as WF. assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ M); exact (ts_tsd B TS)).
assert (RX : forall m, rd_ext (aview tfibsegs (w_H W) m) (aview tfibsegs (w_H Wy) m)).
{ intros m. apply aview_ext; [apply w_Hoff|]. intros x Hx. destruct (w_H W x) eqn:E; [reflexivity|]. rewrite (MONy x E) in Hx. discriminate Hx. }
pose proof (DZ_unhidden ly S W mem0 md0 HAR) as DZU.
assert (DZR : forall a, AGjm.DZONE ly a -> 0 <= a < 2 ^ 64).
{ intros a Ha. pose proof (ar_zone ly S W mem0 md0 HAR (ly_NB ly, kNodesBlockSize) ltac:(unfold owned_extents; cbn [In]; tauto)) as ZN.
  pose proof (ar_zone ly S W mem0 md0 HAR (ly_SB ly, kStoreBlockSize) ltac:(unfold owned_extents; cbn [In]; tauto)) as ZS.
  cbn [fst snd] in ZN, ZS. unfold AGjm.DZONE in Ha. clear - Ha ZN ZS. zlia. }
assert (CST : Forall (cell_holds B ly (aview tfibsegs (w_H Wy) mem)) (as_const B ly)).
{ apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) c Hc) as HOLD.
  pose proof (const_cells_CZS ly HTSD c) as CCZ. destruct (padbI c) eqn:Ep.
  - pose proof Hc as Hc'. rewrite (ts_const B TS ly) in Hc'. unfold Tfib_const in Hc'. apply in_app_iff in Hc' as [Hc'|Hc'].
    { exfalso. revert Ep Hc'. clear. intros Ep Hc'. unfold Tfib_const_sym in Hc'. cbn [In] in Hc'.
      repeat match type of Hc' with _ \/ _ => destruct Hc' as [<-|Hc']; [discriminate Ep|] | False => destruct Hc' end. }
    pose proof (proj1 (forallb_forall _ _) (eq_refl : forallb (fun c => negb (padbI c) || match c_val c with AV (ANum 0) => true | _ => false end) (Tfib_const_abs ++ Tfib_const_shadow) = true) c Hc') as CK.
    cbn beta in CK. rewrite Ep in CK. cbn [negb orb] in CK.
    unfold padbI in Ep. unfold cell_holds. destruct (c_at c) eqn:Ea; try discriminate Ep. cbn [aeval] in CCZ |- *.
    destruct (c_val c) as [e|mk vv]; [|discriminate CK]. destruct e; try discriminate CK.
    lazymatch goal with |- context [aeval _ _ (ANum ?zz)] => destruct zz; try discriminate CK end.
    intros k Hk. cbn [aeval]. pose proof (CCZ (Z.of_nat k) Hc ltac:(lia)) as Pk.
    lazymatch goal with |- _ (?a + Z.of_nat k) = _ =>
    replace (a + Z.of_nat k) with (TFIB_INST + o_sec_mutex + (a + Z.of_nat k - (TFIB_INST + o_sec_mutex))) by lia end.
    rewrite MUT0 by lia. f_equal. clear. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity.
  - apply (Forall_inv (l := [])). apply (Forall_cell_holds_ext B ly _ _ _ (RX mem)). apply Forall_cons; [|apply Forall_nil].
    apply (cell_holds_agree ly (aview tfibsegs (w_H W) mem0)); [| exact HOLD].
    intros k Hk. pose proof (CCZ k Hc Hk) as Z1. pose proof (CZS_range ly LY _ Z1) as Ra.
    apply aview_same. apply MEQ. right. rewrite unsigned_lit_small by exact Ra. exact Z1. }
assert (DEP : depot_mem_ok B ly S (aview tfibsegs (w_H Wy) mem)).
{ apply (depot_mem_ok_rdext ly S _ _ (RX mem)). apply (depot_mem_ok_agreeS ly S (aview tfibsegs (w_H W) mem0)).
  - pose proof (depot_ids_boundS S _ (wf_depot _ _ _ _ _ WF)). lia.
  - intros a Ha. apply aview_same. apply MEQ. left. rewrite unsigned_lit_small by exact (DZR a Ha). exact Ha.
  - exact (depot_at0S ly S _ M). }
eapply SRr_mono.
{ exact (HD1 Wy ly S regs mem md buf tr LY IMG WF (tr_admit_len _ _ _ (ts_universe B TS) Htr) CST DEP R10 R11 R3 R4 R1 BUF B8 BL BH BD S16 SL SH PRES). }
intros W' c' Hle (-> & z & regs' & mem' & mat & -> & AOK & RP & FR & PR' & DEP' & CST'). split; [reflexivity|].
exists z, regs', mem', mat. split; [reflexivity|]. split; [exact RP|]. split.
{ intros x N1 N2. apply FR; [exact N1|]. intros FP. apply N2. exact (footprint_DZ ly _ FP). }
split; [exact PR'|]. split; [exact AOK|]. split.
- apply (depot_mem_ok_agreeS ly _ (aview tfibsegs (w_H Wy) mem')); [exact (depot_ids_after S z tr WF) | | exact DEP'].
  intros a Ha. unfold aview, mbyte, mrestrict. rewrite (DZU a Ha), (MONy _ (DZU a Ha)). reflexivity.
- apply Forall_forall. intros c Hc.
  apply (cell_holds_agree2 ly (aview tfibsegs (w_H Wy) mem') (aview tfibsegs (w_H W) mem0));
  [| exact (proj1 (Forall_forall _ _) CST' c Hc) | exact (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) c Hc)].
  intros k Hk. unfold aview, mbyte, mrestrict.
  destruct (w_H W (Z_to_bv 64 (aeval B ly (c_at c) + k))) eqn:E; [right; reflexivity | left; rewrite (MONy _ E); reflexivity].
Qed.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* (d) The refusal arm (AGk0.refuseS's model half): AR of the post-state by AGic.AR_snull, then AR_tick.             *)
Lemma w64_inst : forall (regs0 : bvmap 5 word), getr regs0 11 = YG0d.w64 TFIB_INST -> bv_unsigned (getr regs0 11) = TFIB_INST.
Proof. intros regs0 E. rewrite E. unfold YG0d.w64. apply unsigned_lit_small. unfold TFIB_INST. lia. Qed.

Lemma post_null_S : forall inst ly S W mem0 md0 n tr regs0 regs' mem' mat,
(inst = TFIB_INST /\ AR tfibsegs B ly S W mem0 md0) -> (aregime S /\ qmeter S) -> 64513 <= n < MALLOC_MAX ->
blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
wframe W ly regs0 mem0 tr -> getr regs0 11 = YG0d.w64 inst ->
AGif4.snull W ly regs0 mem0 inst n (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) 0 regs' mem' ->
(inst = TFIB_INST /\ AR tfibsegs B ly (set_nev (st_nev S + 1) S) W mem' (with_vm_backing (m_vm_lazy md0) mat md0)) /\
qtight (set_nev (st_nev S + 1) S) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B AFSTACK_G regs0 a ->
   aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem0 a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B ly (set_nev (st_nev S + 1) S) (bv_unsigned x) ->
   ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> mem' x = mem0 x).
Proof.
intros inst ly S W mem0 md0 n tr regs0 regs' mem' mat [-> HAR] [Hev HQ] Nr Hlive Htr WFR Hi11 SN.
pose proof (AGif4.sn_MEQ _ _ _ _ _ _ _ _ _ _ _ SN) as MEQ. pose proof (AGif4.sn_PRS _ _ _ _ _ _ _ _ _ _ _ SN) as PRS.
pose proof (AGif4.sn_PRW _ _ _ _ _ _ _ _ _ _ _ SN) as PRT. pose proof (AGif4.sn_VISI _ _ _ _ _ _ _ _ _ _ _ SN) as VISI.
pose proof (AGif4.sn_Voom _ _ _ _ _ _ _ _ _ _ _ SN) as VOOM. pose proof (AGif4.sn_Vunw _ _ _ _ _ _ _ _ _ _ _ SN) as Vunw.
pose proof (AGif4.sn_Vres _ _ _ _ _ _ _ _ _ _ _ SN) as Vres. pose proof (AGif4.sn_Vnch _ _ _ _ _ _ _ _ _ _ _ SN) as Vnch.
pose proof (AGif4.sn_Vmtx _ _ _ _ _ _ _ _ _ _ _ SN) as Vmtx. clear SN.
(* the snull facts in the walk's names (the image-free record states them over ImgBase / ImgBaseAGS) *)
change (forall x : word, ~ AGjm.WINP ly regs0 n (bv_unsigned x) -> bv_unsigned x <> TFIB_OOM ->
  ~ (TFIB_ERRNO <= bv_unsigned x < TFIB_ERRNO + 4) -> mem' x = mem0 x) in MEQ.
change (forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem' a) in PRS.
change (forall a, AGjm.WINT ly a -> apresent (w_H W) mem' a) in PRT.
change (forall a, AGjm.WINI regs0 n a -> aview tfibsegs (w_H W) mem' a <> None) in VISI.
change (val_mem tfibsegs (mrestrict (w_H W) mem') TFIB_OOM 1 1) in VOOM.
change (val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0) in Vunw.
change (val_mem tfibsegs (mrestrict (w_H W) mem') (TFIB_INST + o_sec_reserved) 8 (st_sec_reserved S)) in Vres.
change (val_mem tfibsegs (mrestrict (w_H W) mem') (TFIB_INST + o_sec_n) 8 (Z.of_nat (length (st_sec_arr S)))) in Vnch.
change (val_mem tfibsegs (mrestrict (w_H W) mem') (TFIB_INST + o_sec_mutex) 4 0) in Vmtx.
destruct WFR as (Hsp & Htrlen & Hso & Hbp & Hpres0).
(* AGif0n's wframe states the stack need with ImgBaseAG's copy of AFSTACK *)
unfold ImgBaseAG.AFSTACK in Hsp.
pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LY. pose proof (am_wf _ _ _ _ M) as WF.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR.
pose proof (w64_inst regs0 Hi11) as EI11.
assert (Hinst : 651264 <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 3680 <= 1221024 /\ bv_unsigned (getr regs0 11) mod 8 = 0).
{ rewrite EI11. unfold TFIB_INST. split; [lia|]. split; [lia|]. reflexivity. }
assert (HB : TFIB_INST + 296 <= AGjm.BSLv regs0 n <= TFIB_INST + 392).
{ pose proof (AGjm.BSLv_range ly regs0 n tr (Z.of_nat (length (st_sec_arr S))) 0 0 Htrlen Hinst (nrange_sec n Nr)
    ltac:(unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *; lia)) as HB0.
  pose proof (LGv_m n Nr) as LG. unfold AGjm.BSLv in HB0 |- *. rewrite EI11 in HB0 |- *. lia. }
set (bsl := AGjm.BSLv regs0 n) in *.
pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). pose proof (ar_zones ly S W mem0 md0 HAR) as [_ ZT].
set (sp0 := bv_unsigned (getr regs0 2)) in *.
set (md' := with_vm_backing (m_vm_lazy md0) mat md0).
assert (NW : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> ~ AGjm.WINT ly a -> ~ AGjm.WINI regs0 n a -> a <> TFIB_OOM ->
  ~ (TFIB_ERRNO <= a < TFIB_ERRNO + 4) -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra N1 N2 N3 N4 N5. apply MEQ; rewrite unsigned_lit_small by exact Ra; [|exact N4 | exact N5].
  unfold AGjm.WINP. fold sp0. intros [X|[X|X]]; tauto. }
assert (WINI_E : forall a, AGjm.WINI regs0 n a ->
  (TFIB_INST + o_sec_reserved <= a < TFIB_INST + o_sec_sorted + 1) \/ (TFIB_INST + o_sec_stats <= a < TFIB_INST + o_sec_stats + 32) \/
  (bsl <= a < bsl + 8) \/ (TFIB_INST + o_sec_mutex <= a < TFIB_INST + o_sec_mutex + 4) \/ (TFIB_INST + o_comb_stats <= a < TFIB_INST + o_comb_stats + 40)).
{ intros a X. unfold AGjm.WINI in X. fold bsl in X. rewrite EI11 in X. exact X. }
assert (ARF : AR tfibsegs B ly S W mem' md').
{ apply (AGic.AR_snull B ly S W mem0 mem' md0 md' bsl HB TS HAR).
  - intros a Ra Ho NX. apply aview_same. apply NW; [exact Ra | | | | |].
    + intros ST. exact (AR_stack_law_ok tfibsegs B ly S W mem0 md0 a HAR ltac:(clear - ST Hsp; destruct Hsp as (S1 & _ & S3 & _); unfold AFSTACK in *; lia) Ho).
    + intros X. apply NX. unfold AGic.XN. unfold AGjm.WINT, t_unwinding in X. clear - X. lia.
    + intros X. apply NX. unfold AGic.XN. pose proof (WINI_E a X) as Y. clear - Y. unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. lia.
    + intros ->. apply NX. unfold AGic.XN. left. lia.
    + intros X. exact (ar_errno_not_owned ly S W mem0 md0 HAR a X Ho).
  - intros a0 HV0. set (a := bv_unsigned (Z_to_bv 64 a0)).
    assert (Ra : 0 <= a < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (Z_to_bv 64 a0)) as R; change (bv_modulus 64) with (2 ^ 64) in R; exact R).
    assert (Ex : Z_to_bv 64 a = Z_to_bv 64 a0) by (subst a; apply Z_to_bv_bv_unsigned).
    assert (AV : forall (Hh : word -> bool) m, aview tfibsegs Hh m a0 = aview tfibsegs Hh m a) by (intros Hh m; unfold aview, mbyte, mrestrict; rewrite Ex; reflexivity).
    rewrite AV in HV0 |- *. clearbody a. clear Ex AV a0.
    destruct (zr_dec (sp0 - AFSTACK) sp0 a) as [D1|D1]; [apply apresent_view; apply PRS; exact D1|].
    assert (DT : AGjm.WINT ly a \/ ~ AGjm.WINT ly a) by (clear; unfold AGjm.WINT; lia). destruct DT as [D2|D2]; [apply apresent_view; apply PRT; exact D2|].
    assert (DI : AGjm.WINI regs0 n a \/ ~ AGjm.WINI regs0 n a) by (clear; unfold AGjm.WINI; lia). destruct DI as [D3|D3]; [exact (VISI a D3)|].
    destruct (Z.eq_dec a TFIB_OOM) as [->|D4]; [apply (vm_view_some _ _ _ _ _ _ VOOM); cbn; lia|].
    destruct (zr_dec TFIB_ERRNO (TFIB_ERRNO + 4) a) as [D5|D5]; [apply rw_view; unfold TFIB_ERRNO in *; lia|].
    rewrite (aview_same (w_H W) mem0 mem' a (NW a Ra D1 D2 D3 D4 D5)). exact HV0.
  - pose proof (vm_aview _ _ _ _ _ 0%nat Vunw ltac:(lia)) as X. rewrite Z.add_0_r in X. exact X.
  - intros k Hk. exact (vm_aview _ _ _ _ _ k Vres Hk).
  - intros k Hk. exact (vm_aview _ _ _ _ _ k Vnch Hk).
  - intros k Hk. replace k with (Z.of_nat (Z.to_nat k)) by lia. rewrite (vm_aview _ _ _ _ _ (Z.to_nat k) Vmtx ltac:(lia)). f_equal.
    clear - Hk. unfold YG0f.le_byte. rewrite Z.shiftr_0_l. reflexivity.
  - unfold md'. apply m_vmmaps_wvb.
  - unfold md'. apply m_vm_lazy_wvb.
  - unfold md'. apply eager_used_wvb.
  - intros a Ha _. unfold YG0n.w64. apply NW.
    + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
    + clear - Ha Hsp T7. destruct Hsp as (S1 & _). unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, AFSTACK in *. lia.
    + clear - Ha ZT. unfold in_band_rw, zone3, zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, AGjm.WINT, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, t_unwinding, kThreadObjSize in *. ceil. unfold ASAN_CEIL in *. lia.
    + intros X. pose proof (WINI_E a X) as Y. clear - Ha HB Y. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. lia.
    + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_OOM in *. lia.
    + clear - Ha. unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFIB_ERRNO in *. lia. }
split; [split; [reflexivity | exact (AR_tick B ly S W mem' md' ARF Hev)]|].
split; [exact (qmeter_tight S HQ)|].
(* the frame, on the raw bytes: off what the allocator owns before the call and off the scratch *)
assert (RAW : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ ascratch B AFSTACK_G regs0 a -> mem' (Z_to_bv 64 a) = mem0 (Z_to_bv 64 a)).
{ intros a Ra NO NS. apply NW; [exact Ra | | | | |].
  - intros ST. apply NS. unfold ascratch, spZ, AFSTACK_G. left. unfold AFSTACK in ST. exact ST.
  - intros X. apply NO. apply (ar_T_owned ly S W mem0 md0 HAR a). clear - X. unfold AGjm.WINT, t_unwinding in X. unfold kThreadObjSize. lia.
  - intros X. apply NO. apply (ar_inst_owned ly S W mem0 md0 HAR a). pose proof (WINI_E a X) as Y. clear - Y HB.
    unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. lia.
  - intros ->. exact (NO (ar_oom_owned ly S W mem0 md0 HAR)).
  - intros X. apply NS. unfold ascratch. right. rewrite (ts_errno B TS). exact X. }
split; [intros a Ra NO NS; apply aview_same; exact (RAW a Ra NO NS)|].
intros x NO _ NS. pose proof (bv_unsigned_in_range 64 x) as Rx. change (bv_modulus 64) with (2 ^ 64) in Rx.
rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (RAW _ Rx NO NS).
Qed.
(* ---------------------------------------------------------------------------------------------------------------- *)
(* (d) The grant arm, at the granted base [mb]: the model's sizes and final state, the grown layout and its ledger
   (AGjy's lyF / SF_parts / SEF / placed_finalG, AGk0's LED0 / LED1), the owned set (AGjz's OWN_* / NEWOWN) and the
   frame clause (AGjz.LEAF_S's).                                                                                    *)
Lemma nores50 : mmap_noreserve_b (Z_to_bv 64 50) = false. Proof. reflexivity. Qed.
Lemma grant_piece_shape : forall (a k : word) md, let md' := grant_md false (Z_to_bv 64 50) a k md in
vm_maps (m_vmmaps md') = vm_maps (m_vmmaps md) /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) /\
vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md).
Proof.
intros a k md. cbv zeta. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn. repeat split; reflexivity.
Qed.
Lemma grant50_isp : forall (a k : word) md, vm_init_sp (m_vmmaps (grant_md false (Z_to_bv 64 50) a k md)) = vm_init_sp (m_vmmaps md).
Proof.
intros a k md. unfold grant_md, fixedin_ok_model, fixedin_ok_vmmaps, with_mmap_replacement, with_mmap_backing. rewrite nores50. cbn.
destruct md as [fd [maps lazy mat] io fs pr lim tm]. cbn. destruct maps; cbn; reflexivity.
Qed.

(* Wf and qtight of the final state, from malloc's contract (YG07.malloc_ok) along the granted path of the tree:
   the map is granted, the pointer-array commit (when the array is full) is granted, the depot answers [z], and no
   shadow remap is asked at these sizes. *)
Lemma post_model : forall S n tr z grow,
Wf (as_universe B) S -> aregime S -> 64513 <= n < MALLOC_MAX -> blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
(grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) -> aok S (KDepot tr) z ->
Wf (as_universe B) (AGif4.SFSz S n tr z grow) /\ (qtight S -> qtight (AGif4.SFSz S n tr z grow)).
Proof.
intros S n tr z grow WF Hev Nr Hlive Htr Hgrow AOK.
assert (RZ : rz_size n = 2048).
{ unfold rz_size, rz_log. unfold MALLOC_MAX in Nr. rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
  (proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by lia. reflexivity. }
assert (RS : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (R8 : rounded_size n = AGjm.R8v n) by (unfold rounded_size, round_up, AGjm.R8v; rewrite Z.max_l by lia; replace (n + 8 - 1) with (n + 7) by lia; reflexivity).
assert (FP : from_primary n = false) by (unfold from_primary, needed_primary; rewrite R8, RZ; apply Z.leb_gt; unfold kMaxSize, AGjm.R8v;
  pose proof (Z.div_mod (n+7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n+7) 8 ltac:(lia)); lia).
assert (ND : needed_size n = AGjm.NDv n) by (unfold needed_size, needed_primary, AGjm.NDv; rewrite FP, R8, RZ; lia).
assert (MS : sec_map_size n = AGjm.MSv n) by (unfold sec_map_size, round_up, AGjm.MSv, kPage; rewrite ND; replace (AGjm.NDv n + 4096 - 1) with (AGjm.NDv n + 4095) by lia; reflexivity).
pose proof (malloc_ok (as_universe B) S n tr (ts_universe B TS) WF Hev ltac:(lia) Hlive Htr) as AT.
rewrite (shape_S n tr S Nr FP) in AT.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF)) as WR.
assert (EM : (n <? kMaxAllowedMalloc - kPage) = true) by (apply Z.ltb_lt; unfold kMaxAllowedMalloc, kPage, MALLOC_MAX in *; lia).
assert (EI : (Z.of_nat (length (st_sec_arr S)) <? kMaxNumChunks) = true) by (apply Z.ltb_lt; unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *; lia).
assert (NRM : needs_remap n = false).
{ unfold needs_remap, kClearShadowMmapThreshold. apply Z.leb_gt. apply Z.div_lt_upper_bound; [lia|]. unfold MALLOC_MAX in Nr. lia. }
unfold bind at 1 in AT. cbn [tick modify ibind] in AT.
unfold bind at 1 in AT. unfold mcheck in AT. rewrite EM in AT. cbn [ret ibind] in AT.
unfold bind at 1, sec_alloc, bind at 1, askz in AT. cbn [ibind atok] in AT.
destruct AT as [_ AT]. specialize (AT 1 (or_intror eq_refl)).
cbn [YG00.bind ibind YG00.get YG00.put YG00.modify YG00.ret YG00.mcheck set_nev set_secs set_sec_arr set_sec_reserved st_sec_arr st_secs st_sec_reserved st_nev Z.eqb progz] in AT.
rewrite EI in AT. cbn [YG00.bind ibind YG00.ret YG00.put YG00.modify YG00.mcheck] in AT.
Local Ltac stepA AT := cbn [YG00.bind ibind YG00.get YG00.put YG00.modify YG00.ret YG00.mcheck YG00.askz depot_put AGif0n.malloc_K_t atok progz aGranted
  YG00.ck_n YG00.ck_req YG00.ck_beg malloc_post ImgBaseAGS.malloc_K_t] in AT; try change (1 =? 0) with false in AT; try change (1 =? 1) with true in AT.
Local Ltac tailA AT RS NRM := stepA AT; unfold ck_n in AT; cbn [ck_req] in AT; rewrite RS, NRM in AT; stepA AT.
Local Ltac depA AT := stepA AT;
  (destruct (depot_ids _ + 1 <? kDepotIdsPerBlock) eqn:D1 in AT; [|stepA AT; destruct AT]); stepA AT;
  (destruct (kStartFramesMax + depot_frames _ + Z.of_nat (length _) + 1 <? kStoreFramesPerBlock) eqn:D2 in AT; [|stepA AT; destruct AT]).
Local Ltac finA AT WF MS ND Ez g :=
  let WF' := fresh "WF'" in let QT := fresh "QT" in destruct AT as (WF' & _ & _ & _ & _ & QT);
  unfold AGif4.SFSz; change ImgBaseAGS.sfinal with AFib.sfinal; change ImgBaseAGS.MSv with AGjm.MSv; change ImgBaseAGS.NDv with AGjm.NDv;
  rewrite <- MS, <- ND;
  rewrite <- (AFib.sfinal_eq _ _ _ _ (sec_map_size _) (needed_size _) g (AFib.KS_fresh _ (as_universe B) 0 0 0 WF));
  unfold AFib.s_dep, depot_after;
  first [rewrite (proj2 (Z.eqb_eq _ 0) Ez) | rewrite (proj2 (Z.eqb_neq _ 0) Ez)];
  exact (conj WF' QT).
destruct grow eqn:Eg.
- replace (Z.of_nat (length (st_sec_arr S)) =? st_sec_reserved S) with true in AT by (symmetry; apply Z.eqb_eq; apply Hgrow; reflexivity).
  stepA AT. destruct AT as [_ AT]. specialize (AT 1 (or_intror eq_refl)). stepA AT.
  destruct AT as [_ AT]. specialize (AT z AOK). stepA AT.
  destruct (Z.eqb_spec z 0) as [Ez|Ez].
  + tailA AT RS NRM. finA AT WF MS ND Ez true.
  + depA AT. tailA AT RS NRM. finA AT WF MS ND Ez true.
- replace (Z.of_nat (length (st_sec_arr S)) =? st_sec_reserved S) with false in AT
    by (symmetry; apply Z.eqb_neq; intros X; apply Hgrow in X; discriminate X).
  stepA AT. destruct AT as [_ AT]. specialize (AT z AOK). stepA AT.
  destruct (Z.eqb_spec z 0) as [Ez|Ez].
  + tailA AT RS NRM. finA AT WF MS ND Ez false.
  + depA AT. tailA AT RS NRM. finA AT WF MS ND Ez false.
Qed.

Section g.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (mem0 : word -> option byte) (md0 : Model).
Variables (regs0 : bvmap 5 word) (n : Z) (tr : list Z) (mb : Z).
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis EI11 : bv_unsigned (getr regs0 11) = TFIB_INST.
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Let NrangeS : 64513 <= n < SEC_NMAX := nrange_sec n Nrange.
Hypothesis Hmap : mb mod 4096 = 0 /\ AGjm.mzone mb (AGjm.MSv n).
Hypothesis GAP : Forall (zdisjoint (mb, AGjm.MSv n)) (static_extents ly ++ vis0_zones ly ++ sec_extents ly S).
Local Notation MSv := (AGjm.MSv n).
Local Notation idx := (Z.of_nat (length (st_sec_arr S))).
Local Notation res := (st_sec_reserved S).
Local Notation lyF := (set_ly_sec ly (AFib.rS S) mb).
Local Notation SF g z := (AGif4.SFSz S n tr z g).

Lemma Mg : ARm B ly S (aview tfibsegs (w_H W) mem0). Proof. exact (proj1 HAR). Qed.
Lemma LYg : layout_ok ly. Proof. exact (am_layout _ _ _ _ Mg). Qed.
Lemma WFg : Wf (as_universe B) S. Proof. exact (am_wf _ _ _ _ Mg). Qed.
Lemma Hinst_g : 651264 <= bv_unsigned (getr regs0 11) /\ bv_unsigned (getr regs0 11) + 3680 <= 1221024 /\ bv_unsigned (getr regs0 11) mod 8 = 0.
Proof. rewrite EI11. unfold TFIB_INST. split; [lia|]. split; [lia|]. reflexivity. Qed.
Lemma Hidx_g : 0 <= idx < kMaxNumChunks.
Proof. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WFg)) as R. unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia. Qed.
Lemma Hres_g : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Proof.
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WFg)) as R. pose proof (ws_reserved_al _ (wf_secondary _ _ _ _ _ WFg)) as [_ RA].
unfold kMaxNumChunks, kPtrArrayEntriesPerCommit in *. split; [lia | exact RA].
Qed.
Local Ltac mf := pose proof (AGjm.map_facts ly regs0 n tr idx res mb Htrlen Hinst_g NrangeS Hidx_g Hres_g Hmap) as
  (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & SM1 & SM2 & SM3 & PBE & SMA);
  pose proof (AGjm.map_zoneN ly regs0 n tr idx res mb Htrlen Hinst_g NrangeS Hidx_g Hres_g Hmap) as MZ.
Local Ltac sf := pose proof (size_facts_m n Nrange) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & _).

Lemma lyF_le : layout_le (length (st_secs S)) ly lyF.
Proof. unfold AFib.rS. apply set_ly_sec_le. Qed.
Lemma lyF_sec : ly_sec lyF (AFib.rS S) = mb.
Proof. unfold set_ly_sec. cbn. rewrite PeanoNat.Nat.eqb_refl. reflexivity. Qed.
Lemma lyF_eqs : ly_prim lyF = ly_prim ly /\ ly_space lyF = ly_space ly /\ ly_Q lyF = ly_Q ly /\ ly_T lyF = ly_T ly /\ ly_C lyF = ly_C ly /\
ly_F lyF = ly_F ly /\ ly_NB lyF = ly_NB ly /\ ly_SB lyF = ly_SB ly /\ ly_top lyF = ly_top ly /\ ly_stk_lo lyF = ly_stk_lo ly /\
ly_stk_hi lyF = ly_stk_hi ly /\ ly_tsd lyF = ly_tsd ly /\ ly_tr0 lyF = ly_tr0 ly /\ ly_extra lyF = ly_extra ly /\ ly_D lyF = ly_D ly /\
ly_vis0 lyF = ly_vis0 ly.
Proof. unfold set_ly_sec. cbn. repeat split; reflexivity. Qed.
Lemma staticF : static_extents lyF = static_extents ly /\ vis0_zones lyF = vis0_zones ly /\ core_extents lyF = core_extents ly /\
owned_extents lyF = owned_extents ly.
Proof. unfold set_ly_sec, static_extents, vis0_zones, core_extents, owned_extents. cbn. repeat split; reflexivity. Qed.

Lemma sizesK : needed_size n = AGjm.NDv n /\ sec_map_size n = MSv /\ req_size n = n /\ rz_size n = 2048 /\ from_primary n = false /\
ck_n (AFib.KS S n) = n /\ ck_rz (AFib.KS S n) = 2048 /\ ck_extent (AFib.KS S n) = MSv - 4096 /\ ck_req (AFib.KS S n) = n /\
ck_beg (AFib.KS S n) = PSec (AFib.rS S) 4096 /\ ck_state (AFib.KS S n) = CAllocated.
Proof.
pose proof Nrange as NR. unfold MALLOC_MAX in NR.
assert (RZ : rz_size n = 2048).
{ unfold rz_size, rz_log. rewrite (proj2 (Z.leb_gt n 48)), (proj2 (Z.leb_gt n 96)), (proj2 (Z.leb_gt n 448)), (proj2 (Z.leb_gt n 3968)),
(proj2 (Z.leb_gt n 16128)), (proj2 (Z.leb_gt n 32256)), (proj2 (Z.leb_gt n 64512)) by lia. reflexivity. }
assert (RS : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (R8 : rounded_size n = AGjm.R8v n) by (unfold rounded_size, round_up, AGjm.R8v; rewrite Z.max_l by lia; replace (n + 8 - 1) with (n + 7) by lia; reflexivity).
assert (FP : from_primary n = false) by (unfold from_primary, needed_primary; rewrite R8, RZ; apply Z.leb_gt; unfold kMaxSize, AGjm.R8v;
  pose proof (Z.div_mod (n+7) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (n+7) 8 ltac:(lia)); lia).
assert (ND : needed_size n = AGjm.NDv n) by (unfold needed_size, needed_primary, AGjm.NDv; rewrite FP, R8, RZ; lia).
assert (MS : sec_map_size n = MSv) by (unfold sec_map_size, round_up, AGjm.MSv, kPage; rewrite ND; replace (AGjm.NDv n + 4096 - 1) with (AGjm.NDv n + 4095) by lia; reflexivity).
unfold AFib.KS, ck_n, ck_rz, ck_extent, ck_req, ck_beg, ck_state. cbn [YG00.ck_req YG00.ck_beg YG00.ck_state].
rewrite RS, RZ, FP, MS. unfold kPage. repeat split; try reflexivity; lia.
Qed.

Lemma SF_parts : forall g z,
(forall c, reg (SF g z) c = reg S c) /\ frames (SF g z) = frames S /\ st_sec_arr (SF g z) = st_sec_arr S ++ [AFib.rS S] /\
st_sec_reserved (SF g z) = (if g then res + kPtrArrayEntriesPerCommit else res) /\ st_chunks (SF g z) = st_chunks S ++ [AFib.KS S n] /\
st_nev (SF g z) = st_nev S + 1 /\ st_regions (SF g z) = st_regions S /\ st_depot (SF g z) = st_depot (depot_after z tr S) /\
st_secs (SF g z) = st_secs S ++ [mkSec MSv (AGjm.NDv n) true].
Proof.
intros g z. unfold AGif4.SFSz, ImgBaseAGS.sfinal, ImgBaseAGS.resF, ImgBaseAGS.depF, reg, frames. cbn.
repeat split; try reflexivity. unfold depot_after. destruct (z =? 0); reflexivity.
Qed.

Lemma SEF : forall g z, sec_extents lyF (SF g z) = sec_extents ly S ++ [(mb, MSv)].
Proof.
intros g z. pose proof (SF_parts g z) as (_ & _ & _ & _ & Rck & _). pose proof sizesK as (_ & MS & _ & _ & _ & _ & _ & _ & KQ & KB & _).
unfold sec_extents at 1. rewrite Rck, flat_map_app. pose proof (sec_extents_le ly lyF S _ _ _ _ lyF_le WFg) as SE. unfold sec_extents in SE at 1. rewrite SE.
cbn [flat_map]. rewrite KB, KQ, MS, lyF_sec, app_nil_r. reflexivity.
Qed.

Lemma placedF : forall g z, sec_placed lyF (SF g z).
Proof.
intros g z. pose proof (am_placed _ _ _ _ Mg) as [PL PD]. mf. pose proof staticF as (ES & _).
unfold sec_placed. rewrite (SEF g z), ES. split.
- apply Forall_app. split; [exact PL|]. constructor; [|apply Forall_nil]. cbn [fst snd]. unfold page_aligned, in_app.
  clear - M1 M2 M3 MZ. ceil. unfold zone3, TFIB_IMG_LO, ASAN_CEIL, kLowShadowBeg, kHighMemBeg, TFIB_IMG_END in *. repeat split; zlia.
- apply pairwise_app_inv in PD as (P1 & P2 & P3). apply pairwise_app; [apply pairwise_app; [exact P1 | cbn; split; [apply Forall_nil | exact I] |] | exact P2 |].
  + intros x y Hx [<-|[]]. apply zdisjoint_sym. apply (proj1 (Forall_forall _ _) GAP). rewrite !in_app_iff. right; right. exact Hx.
  + intros x y Hx Hy. apply in_app_iff in Hx as [Hx|[<-|[]]]; [exact (P3 x y Hx Hy)|].
    apply (proj1 (Forall_forall _ _) GAP). rewrite !in_app_iff. left. exact Hy.
Qed.

Lemma Hmap_apart_g : zdisjoint (mb, MSv) (ly_T ly, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (ly_Q ly, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Proof.
assert (G : forall e, In e (static_extents ly ++ vis0_zones ly) -> zdisjoint (mb, MSv) e)
  by (intros e He; apply (proj1 (Forall_forall _ _) GAP); rewrite app_assoc; apply in_app_iff; left; exact He).
repeat split; apply G; unfold static_extents, owned_extents, vis0_zones; rewrite ?in_app_iff; cbn [In]; tauto.
Qed.

(* The ledger of the grown layout: the anonymous map (YG0j.ALedger_anon, AGk0.LED0) and, when the pointer array was
   full, its next commit (YG0j.ALedger_qcommit', AGk0.LED1). *)
Lemma LED0 : forall z (mdN : Model), aregime S -> amwf mdN -> ALedger tfibsegs ly S mdN ->
grant_ok_na_pin mdN (YG0d.w64 mb) MSv = true ->
ALedger tfibsegs lyF (SF false z) (mmap_model (YG0d.w64 mb) (YG0d.w64 MSv) mdN).
Proof.
intros z mdN Hev MWN LN GOK. pose proof (SF_parts false z) as (Rreg & _ & _ & Rres & _ & Rnev & Rregs & _).
sf. mf.
assert (UMS : bv_unsigned (YG0d.w64 MSv) = MSv) by (unfold YG0d.w64; apply unsigned_lit_small; clear - Z8; unfold MALLOC_MAX in Z8; lia).
assert (Umb : bv_unsigned (YG0d.w64 mb) = mb) by (unfold YG0d.w64; apply unsigned_lit_small; clear - M1 M2 Z8 MZ; ceil; unfold zone3, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; zlia).
apply (YG0j.ALedger_anon tfibsegs (as_universe B) 0 0 0 ly S (SF false z) mdN (YG0d.w64 mb) (YG0d.w64 MSv) (AFib.rS S) mb LYg WFg (am_placed _ _ _ _ Mg) MWN LN).
- rewrite UMS. exact GOK.
- exact Hev.
- rewrite UMS. clear - Z8. unfold MALLOC_MAX in *. lia.
- rewrite UMS. exact Z9.
- intros c Hc. exact (Rreg c).
- unfold prim_committed. rewrite Rregs. reflexivity.
- rewrite Umb, UMS. exact (SEF false z).
- exact Rnev.
- rewrite Rres. reflexivity.
Qed.
Lemma LED1 : forall z (mdV md5 : Model), idx = res -> amwf mdV -> ALedger tfibsegs lyF (SF false z) mdV ->
md5 = grant_md false (Z_to_bv 64 50) (YG0d.w64 (AGjm.QSv ly idx)) (YG0d.w64 131072) mdV ->
eager_used md5 <= eager_used mdV + 131072 ->
ALedger tfibsegs lyF (SF true z) md5.
Proof.
intros z mdV md5 Heq MWV LV E5 EG. pose proof (SF_parts false z) as (Rreg0 & _ & _ & Rres0 & _ & Rnev0 & Rregs0 & _).
pose proof (SF_parts true z) as (Rreg1 & _ & _ & Rres1 & _ & Rnev1 & Rregs1 & _). sf.
pose proof (ar_zones ly S W mem0 md0 HAR) as [ZQ _]. pose proof (AGjm.high_facts ly regs0 tr idx res LYg (img_cover_of_ledger ly S md0 (proj1 (proj2 HAR))) Htrlen Hinst_g Hidx_g Hres_g) as
  (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & F11 & _).
pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WFg)) as WR. pose proof Hres_g as [_ RA].
assert (QA : (ly_Q ly + 8 * res) mod 4096 = 0).
{ apply Z.mod_divide in F11 as [q Hq]; [|lia]. apply Z.mod_divide in RA as [r Hr]; [|unfold kPtrArrayEntriesPerCommit; lia].
  rewrite Hq, Hr. unfold kPtrArrayEntriesPerCommit. replace (q * 4096 + 8 * (r * 16384)) with ((q + 32 * r) * 4096) by lia. apply Z.mod_mul. lia. }
assert (UQa : bv_unsigned (YG0d.w64 (AGjm.QSv ly idx)) = AGjm.QSv ly idx).
{ unfold YG0d.w64, AGjm.QSv. apply unsigned_lit_small. rewrite Heq. clear - F9 F10 WR. ceil.
  unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia. }
assert (UQb : bv_unsigned (YG0d.w64 131072) = 131072) by (unfold YG0d.w64; apply unsigned_lit_small; lia).
pose proof (grant_piece_shape (YG0d.w64 (AGjm.QSv ly idx)) (YG0d.w64 131072) mdV) as (VM & RES & LIM & MMB). cbv zeta in VM, RES, LIM, MMB.
subst md5.
apply (YG0j.ALedger_qcommit' tfibsegs lyF (SF false z) (SF true z) mdV).
- apply set_ly_sec_ok. exact LYg.
- rewrite (SEF false z). apply Forall_app. split; [exact (YG08.sec_extents_sizes64P _ 0 0 0 ly S WFg)|]. constructor; [|constructor].
  cbn [snd]. clear - Z8 Z9. unfold MALLOC_MAX in Z8. lia.
- exact (placedF false z).
- exact LV.
- exact VM.
- exact RES.
- exact LIM.
- exact MMB.
- apply grant50_isp.
- intros x Hx. destruct MWV as [(W1 & W2 & W3' & _ & W5) _].
  apply (YG0j.cov_grant_md false (Z_to_bv 64 50) (YG0d.w64 (AGjm.QSv ly idx)) (YG0d.w64 131072) mdV x).
  + unfold YK0g.model_ivs_wf. split; [|split; [|split; [|exact W5]]]; intros q Hq; [exact (W1 q Hq) | exact (W2 q Hq) | exact (W3' q Hq)].
  + rewrite UQa, UQb. unfold AGjm.QSv. rewrite Heq. clear - F9 F10 WR. ceil.
    unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
  + rewrite UQa, UQb. intros Hin. apply Hx. pose proof lyF_eqs as (_ & _ & EQ & _). rewrite EQ. unfold AGjm.QSv in Hin. rewrite Heq in Hin.
    clear - Hin WR. unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *. lia.
- unfold kPtrArrayEntriesPerCommit. lia.
- intros c Hc. rewrite (Rreg1 c), (Rreg0 c). reflexivity.
- rewrite (SEF true z), (SEF false z). reflexivity.
- unfold prim_committed. rewrite Rregs1, Rregs0. reflexivity.
- rewrite Rnev1, Rnev0. reflexivity.
- rewrite Rres1, Rres0. reflexivity.
- exact (YG0g.naf_grant_md false (Z_to_bv 64 50) mdV _ _ MWV).
Qed.

(* The owned set at the pre-state and at the final state (AGjz.OWN_T / OWN_I / OWN_Q / OWN_D / band_core / OWN_SH /
   OWN_BANDhid / NEWOWN). *)
Lemma own_Tg : forall a, AGjm.WINT ly a -> aowned B ly S a.
Proof. intros a Hw. apply (ar_T_owned ly S W mem0 md0 HAR a). unfold AGjm.WINT, t_unwinding in Hw. unfold kThreadObjSize. lia. Qed.
Lemma own_Ig : forall a, AGjm.WINI regs0 n a -> aowned B ly S a.
Proof.
intros a Hw. pose proof (AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst_g NrangeS Hidx_g) as HB. rewrite EI11 in HB.
apply (ar_inst_owned ly S W mem0 md0 HAR a). unfold AGjm.WINI in Hw. rewrite EI11 in Hw.
unfold TFIB_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, o_comb_stats in *. lia.
Qed.
Lemma own_Qg : forall a, ly_Q ly <= a < ly_Q ly + kPtrArrayResv -> aowned B ly S a.
Proof. intros a Ha. apply (own_core B ly S _ (ly_Q ly, kPtrArrayResv) a Mg); [unfold core_extents; cbn; tauto | exact Ha]. Qed.
Lemma own_Dg : forall a, AGjm.DZONE ly a -> aowned B ly S a.
Proof.
intros a Hd. unfold AGjm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- apply (own_static B ly S _ a Mg). rewrite (ts_owned B TS). unfold Tfib_owned_static. apply Exists_exists.
  exists (0xa7790, 0x5ca590 - 0xa7790). split; [cbn; tauto|]. unfold in_zr. cbn [fst snd]. clear - Hd. lia.
- apply (own_core B ly S _ (ly_NB ly, kNodesBlockSize) a Mg); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Hd].
- apply (own_core B ly S _ (ly_SB ly, kStoreBlockSize) a Mg); [unfold core_extents; cbn; tauto | cbn [fst snd]; exact Hd].
Qed.
Lemma band_core : forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) ->
Exists (fun r => in_zr a (shadow_addr (fst r), (snd r + 7) / 8)) (static_extents ly ++ sec_extents ly S ++ zero_shadow_ranges B ly ++ as_owned_static B ++ [hm_zone; lm_zone]).
Proof.
intros a Ha. apply Exists_exists. pose proof hm_zone_shadow as [E1 E2].
destruct Ha as [LO|HI].
- exists lm_zone. split; [repeat (apply in_app_iff; right); right; left; reflexivity|].
  unfold in_zr, lm_zone, shadow_addr, SHADOW_OFF. cbn [fst snd]. clear - LO. unfold kLowMemEnd, kLowShadowBeg, kLowShadowEnd in *.
  repeat match goal with |- context[(?x + 7) / 8] => let v := eval vm_compute in ((x + 7) / 8) in change ((x + 7) / 8) with v end. change (0 / 8) with 0. zlia.
- exists hm_zone. split; [repeat (apply in_app_iff; right); left; reflexivity|].
  unfold in_zr. cbn [fst snd] in *. rewrite E1. rewrite E1 in E2. clear - HI E2. zlia.
Qed.
Lemma own_SHg : forall a, AGjm.SMv mb <= a < AGjm.SMv mb + MSv / 8 -> aowned B ly S a.
Proof.
intros a Ha. mf. sf.
split; [do 4 right; apply band_core; clear - Ha MZ; unfold kLowShadowEnd, kHighShadowBeg, kHighShadowEnd; zlia|].
pose proof (Z.div_mod MSv 8 ltac:(zlia)) as DM8. assert (MM8 : MSv mod 8 = 0) by (clear - Z9 MZ; apply Z.mod_divide in Z9 as [u Hu]; [|zlia]; rewrite Hu; replace (u * 4096) with ((u * 512) * 8) by zlia; apply Z.mod_mul; zlia).
eapply (nc_shadow B ly S _ a mb MSv Mg).
- apply Z.mod_divide in M3 as [p Hp]; [|zlia]. rewrite Hp. replace (p * 4096) with ((p * 512) * 8) by zlia. apply Z.mod_mul. zlia.
- clear - M1 MZ. unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in M1. zlia.
- clear - M2 MZ. ceil; unfold ASAN_CEIL, kHighMemEnd in *. zlia.
- apply (proj1 (Forall_forall _ _) GAP). apply in_app_iff. left. unfold static_extents, owned_extents. apply in_app_iff. left. cbn. tauto.
- rewrite <- SMA. replace ((MSv + 7) / 8) with (MSv / 8); [clear - Ha MZ; zlia|].
  clear - MM8 Z8 MZ. apply Z.mod_divide in MM8 as [u Hu]; [|zlia]. rewrite Hu. rewrite Z.div_mul by zlia. rewrite Z.div_add_l by zlia. change (7 / 8) with 0. zlia.
Qed.
Lemma own_BANDg : forall a, (2147450880 <= a < kLowShadowEnd) \/ (kHighShadowBeg <= a < kHighShadowEnd) -> w_H W (Z_to_bv 64 a) = true -> aowned B ly S a.
Proof.
intros a Ha Hh. split; [do 4 right; apply band_core; exact Ha|].
assert (HB : in_band_rw a) by (clear - Ha; unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *; zlia).
intros C. apply (client_band_vis B ly S _ a Mg HB C). apply aview_band_hidden; [exact (al_img_env tfibsegs ly S _ LYg (proj1 (proj2 HAR))) | exact HB | exact Hh].
Qed.
Lemma NEWOWN : forall (g : bool) (z : Z), forall a, mb <= a < mb + MSv -> ~ (AGjm.Uv mb <= a < AGjm.Uv mb + n) -> aowned B lyF (SF g z) a.
Proof.
intros g z a Ha Hnu. mf. pose proof (SF_parts g z) as (_ & Rfr & _ & _ & Rck & _).
pose proof sizesK as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST). pose proof Hmap_apart_g as (_ & _ & MP3 & _).
split.
- do 3 right. left. rewrite (SEF g z). apply Exists_exists. exists (mb, MSv). split; [apply in_app_iff; right; left; reflexivity | unfold in_zr; cbn [fst snd]; exact Ha].
- intros [(k & Hk & Hst & Hr)|(cp & Hcp & Hr)].
  + rewrite Rck in Hk. apply in_app_iff in Hk as [Hk|[<-|[]]].
    * unfold ck_user in Hr. rewrite (sptr_addr_le B ly lyF (length (st_secs S)) _ lyF_le (AFib.padd_lt S _ _ (AFib.chunk_lt S _ _ _ _ WFg k Hk))) in Hr.
      fold (ck_user k) in Hr. pose proof (YG0s.chunk_facts B ly S _ k Mg Hk) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _). rewrite G4 in Hr. unfold ck_n in Hr.
      destruct (extent_zone B ly S _ k Mg Hk) as [[X1 X2]|(m & len & Hin & X1 & X2)].
      -- unfold zdisjoint in MP3. cbn [fst snd] in MP3. clear - Ha Hr X1 X2 MP3 G8 G5 MZ. zlia.
      -- pose proof (proj1 (Forall_forall _ _) GAP (m, len) ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Hin)) as D. unfold zdisjoint in D. cbn [fst snd] in D.
         clear - Ha Hr X1 X2 D G8 G5 MZ. unfold kPage in *. zlia.
    * apply Hnu. unfold ck_user in Hr. cbn [YG00.ck_beg AFib.KS padd sptr_addr sptr_exp aeval] in Hr.
      change (YG00.ck_rz (AFib.KS S n)) with (ck_rz (AFib.KS S n)) in Hr. rewrite KR, KN, lyF_sec in Hr. unfold AGjm.Uv. unfold kPage in Hr. clear - Hr MZ. zlia.
  + unfold frames in Hcp, Rfr. rewrite Rfr in Hcp. destruct cp as [cid pos]. cbn [fst snd] in Hr.
    pose proof (YG0s.frame_facts B ly S _ cid pos Mg Hcp) as (C1 & C2 & F1 & F2 & FA & P1 & P2 & P3 & P4 & _). pose proof (Z.mul_nonneg_nonneg cid (2 ^ 20) ltac:(zlia) ltac:(zlia)).
    pose proof lyF_eqs as (_ & _ & _ & _ & _ & E6 & _). unfold frame_addr, in_zr in Hr. rewrite E6 in Hr. cbn [fst snd] in Hr.
    pose proof (proj1 (Forall_forall _ _) GAP (ly_F ly, kFakeStackSize) ltac:(apply in_app_iff; left; unfold static_extents, owned_extents; apply in_app_iff; left; cbn; tauto)) as D.
    unfold zdisjoint in D. cbn [fst snd] in D.
    destruct Hr as [Hr|Hr].
    * clear - Ha Hr D P1 P2 C1 H MZ. unfold kFakeFramesOff in *. zlia.
    * pose proof (shadow_range_below (ly_F ly + fs_frame_off cid pos) (fs_frame_bytes cid) ltac:(clear - F1 P1 H MZ; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kFakeFramesOff in *; zlia) ltac:(clear - P4 MZ; zlia) ltac:(clear - F1 P2 MZ; ceil; unfold zone3, TFIB_IMG_LO, in_app, ASAN_CEIL, kHighMemEnd, kLowShadowBeg, kHighMemBeg, kFakeStackSize in *; zlia)) as SBel.
      pose proof (Z.div_pos (ly_F ly + fs_frame_off cid pos) 8 ltac:(clear - F1 P1 H MZ; unfold in_app, kFakeFramesOff in *; zlia) ltac:(zlia)) as SB0.
      clear - Ha Hr SBel SB0 M1 MZ. unfold shadow_addr, SHADOW_OFF, zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *. zlia.
Qed.

(* The new block's shadow hull (AGjs.SH_hull). *)
Lemma SH_hull : AGif4.SHLO mb <= shadow_addr mb /\ shadow_addr mb + MSv / 8 <= AGif4.SHHI mb MSv /\
AGif4.SHHI mb MSv - AGif4.SHLO mb <= MSv / 8 + 8192 /\ AGif4.SHLO mb mod 4096 = 0 /\ AGif4.SHHI mb MSv mod 4096 = 0 /\ AGif4.SHLO mb <= AGif4.SHHI mb MSv.
Proof.
sf. unfold AGif4.SHLO, AGif4.SHHI.
pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(zlia)) as D1. pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(zlia)) as B1.
pose proof (Z.div_mod (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)) as D2. pose proof (Z.mod_pos_bound (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)) as B2.
repeat split; first [apply Z_mod_mult | zlia].
Qed.

(* The frame clause of the grant arm on the raw bytes: the walk wrote only its windows, the next pointer-array commit
   and the depot's zone, and all of them are the allocator's before or after the call, or scratch. *)
Lemma frame_grant_raw : forall (grow : bool) z (mem' : word -> option byte),
(forall x : word, ~ AGjm.WIN ly regs0 n idx mb (bv_unsigned x) -> ~ (grow = true /\ AGif4.QRz ly res (bv_unsigned x)) ->
   ~ AGif4.DXz ly (bv_unsigned (getr regs0 2)) (bv_unsigned x) -> mem' x = mem0 x) ->
forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B lyF (SF grow z) (bv_unsigned x) ->
~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> ~ (AGjm.Uv mb <= bv_unsigned x < AGjm.Uv mb + req_size n) -> mem' x = mem0 x.
Proof.
intros grow z mem' fMEQF x NO NO' NS NE.
pose proof sizesK as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
pose proof Hidx_g as HI. pose proof Hres_g as [HRS _].
assert (NE' : ~ (AGjm.Uv mb <= bv_unsigned x < AGjm.Uv mb + n)) by (rewrite RS in NE; exact NE).
assert (NST : ~ (bv_unsigned (getr regs0 2) - AFSTACK <= bv_unsigned x < bv_unsigned (getr regs0 2)))
  by (intros Hs; apply NS; unfold ascratch, spZ, AFSTACK_G; left; exact Hs).
apply fMEQF.
- intros Hw. unfold AGjm.WIN, AGjm.WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
  + exact (NST Hw).
  + exact (NO (own_Tg _ Hw)).
  + exact (NO (own_Ig _ Hw)).
  + apply NO, own_Qg. unfold AGjm.QSv in Hw. clear - Hw HI HRS. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia.
  + exact (NO' (NEWOWN grow z _ Hw NE')).
  + exact (NO (own_SHg _ Hw)).
- intros [_ Hq]. apply NO, own_Qg. unfold AGif4.QRz in Hq. clear - Hq HRS HI. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. lia.
- intros [Hs|Hd]; [apply NST; clear - Hs; unfold DEP_STK, AFSTACK, ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; lia | exact (NO (own_Dg _ Hd))].
Qed.

(* The frame clause of the grant arm (AGjz.LEAF_S). *)
Lemma frame_grant : forall (grow : bool) z (Wz : world tfibsegs) (mem' : word -> option byte),
(grow = true <-> idx = res) -> Wf (as_universe B) (SF grow z) ->
(forall x : word, w_H W x = false -> w_H Wz x = false) ->
(forall x : word, ~ (mb <= bv_unsigned x < mb + MSv) -> ~ (AGif4.SHLO mb <= bv_unsigned x < AGif4.SHHI mb MSv) ->
   ~ (grow = true /\ AGjm.QSv ly idx <= bv_unsigned x < AGjm.QSv ly idx + 131072) -> w_H Wz x = w_H W x) ->
(forall x : word, ~ AGjm.WIN ly regs0 n idx mb (bv_unsigned x) -> ~ (grow = true /\ AGif4.QRz ly res (bv_unsigned x)) ->
   ~ AGif4.DXz ly (bv_unsigned (getr regs0 2)) (bv_unsigned x) -> mem' x = mem0 x) ->
forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B lyF (SF grow z) a ->
~ ascratch B AFSTACK_G regs0 a -> ~ (AGjm.Uv mb <= a < AGjm.Uv mb + req_size n) ->
aview tfibsegs (w_H Wz) mem' a = aview tfibsegs (w_H W) mem0 a.
Proof.
intros grow z Wz mem' Hgrow WF' MONf HOUT fMEQF a Ra NO NO' NS NE. mf. sf.
pose proof sizesK as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
pose proof Hidx_g as HI. pose proof Hres_g as [HRS _]. pose proof SH_hull as (H1 & H2 & H3 & _).
assert (NE' : ~ (AGjm.Uv mb <= a < AGjm.Uv mb + n)) by (rewrite RS in NE; exact NE).
assert (NST : ~ (bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2))) by (intros Hs; apply NS; unfold ascratch, spZ, AFSTACK_G; left; exact Hs).
set (x := Z_to_bv 64 a). assert (Ux : bv_unsigned x = a) by (subst x; apply unsigned_lit_small; exact Ra).
assert (MEQa : mem' x = mem0 x).
{ apply fMEQF; rewrite Ux.
  - intros Hw. unfold AGjm.WIN, AGjm.WINM in Hw. destruct Hw as [Hw|[Hw|[Hw|[Hw|[Hw|Hw]]]]].
    + exact (NST Hw).
    + exact (NO (own_Tg a Hw)).
    + exact (NO (own_Ig a Hw)).
    + apply NO, own_Qg. unfold AGjm.QSv in Hw. clear - Hw HI HRS. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia.
    + exact (NO' (NEWOWN grow z a Hw NE')).
    + exact (NO (own_SHg a Hw)).
  - intros [_ Hq]. apply NO, own_Qg. unfold AGif4.QRz in Hq. clear - Hq HRS HI. unfold kPtrArrayEntriesPerCommit, kPtrArrayResv, kMaxNumChunks in *. lia.
  - intros [Hs|Hd]; [apply NST; clear - Hs; unfold DEP_STK, AFSTACK, ImgBaseAGS.DEP_STK, ImgBaseAGS.AFSTACK in *; lia | exact (NO (own_Dg a Hd))]. }
destruct (w_H W x) eqn:EhW.
- destruct (w_H Wz x) eqn:EhZ.
  + unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ. reflexivity.
  + exfalso. destruct (zr_dec mb (mb + MSv) a) as [D1|D1]; [exact (NO' (NEWOWN grow z a D1 NE'))|].
    destruct (zr_dec (AGif4.SHLO mb) (AGif4.SHHI mb MSv) a) as [D2|D2].
    { apply NO. apply own_BANDg; [| subst x; exact EhW]. clear - D2 H1 H2 SM1 SM2 H3 M1 M2 M3 Z8 SMA MZ.
      unfold AGif4.SHLO, AGif4.SHHI, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in *.
      pose proof (Z.div_mod (shadow_addr mb) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb) 4096 ltac:(zlia)).
      pose proof (Z.div_mod (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)). pose proof (Z.mod_pos_bound (shadow_addr mb + MSv / 8 + 4095) 4096 ltac:(zlia)).
      pose proof (Z.div_mod MSv 8 ltac:(zlia)). pose proof (Z.mod_pos_bound MSv 8 ltac:(zlia)). zlia. }
    destruct grow eqn:Eg.
    * destruct (zr_dec (AGjm.QSv ly idx) (AGjm.QSv ly idx + 131072) a) as [D3|D3].
      { apply NO, own_Qg. pose proof (proj1 Hgrow eq_refl) as EIR. pose proof (ws_reserved _ (wf_secondary _ _ _ _ _ WF')) as WR.
        pose proof (SF_parts true z) as (_ & _ & Rarr & Rres & _). rewrite Rarr, Rres, length_app in WR. cbn [length] in WR.
        unfold AGjm.QSv in D3. clear - D3 HI HRS EIR WR. unfold kPtrArrayResv, kMaxNumChunks, kPtrArrayEntriesPerCommit in *. lia. }
      rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | rewrite Ux; intros [_ Hq]; exact (D3 Hq)].
    * rewrite (HOUT x) in EhZ; [congruence | rewrite Ux; exact D1 | rewrite Ux; exact D2 | intros [E _]; discriminate E].
- pose proof (MONf x EhW) as EhZ. unfold aview, mbyte, mrestrict. subst x. rewrite EhW, EhZ, MEQa. reflexivity.
Qed.

Lemma user_addr : sptr_addr B lyF (ck_user (AFib.KS S n)) = AGjm.Uv mb.
Proof.
pose proof sizesK as (ND & MS & RS & RZ & FP & KN & KR & KE & KQ & KB & KST).
unfold ck_user. cbn [YG00.ck_beg AFib.KS padd sptr_addr sptr_exp aeval].
change (YG00.ck_rz (AFib.KS S n)) with (ck_rz (AFib.KS S n)). rewrite KR, lyF_sec. unfold AGjm.Uv, kPage. lia.
Qed.

(* The grant arm's post at the granted base: AR of the final state (AGjy.AR_transport, with fin_facts from sfin and
   wz_facts from skern), qtight, the grown layout, the result's address and the frame clause. *)
Lemma post_grant_g : forall grow z (Wz : world tfibsegs) mdz regs' (mem' : word -> option byte),
aregime S -> qmeter S -> blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
wframe W ly regs0 mem0 tr ->
(grow = true <-> idx = res) ->
AGif4.skern grow W Wz md0 mdz ly mb MSv (AGjm.QSv ly idx) ->
AGif4.sfin W ly regs0 mem0 TFIB_INST n tr idx res mb (fun zz m => dpost_cgif B TFIB_INST ly S W tr zz m) grow z Wz regs' mem' ->
aok S (KDepot tr) z ->
AR tfibsegs B lyF (SF grow z) Wz mem' mdz /\ qtight (SF grow z) /\ layout_le (length (st_secs S)) ly lyF /\
sptr_addr B lyF (ck_user (AFib.KS S n)) = AGjm.Uv mb /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B lyF (SF grow z) a ->
   ~ ascratch B AFSTACK_G regs0 a -> ~ (AGjm.Uv mb <= a < AGjm.Uv mb + req_size n) ->
   aview tfibsegs (w_H Wz) mem' a = aview tfibsegs (w_H W) mem0 a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B lyF (SF grow z) (bv_unsigned x) ->
   ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> ~ (AGjm.Uv mb <= bv_unsigned x < AGjm.Uv mb + req_size n) -> mem' x = mem0 x).
Proof using All.
intros grow z Wz mdz regs' mem' Hev HQ Hlive Htr WFR Hgrow SK SFN AOK.
pose proof (post_model S n tr z grow WFg Hev Nrange Hlive Htr Hgrow AOK) as [WF' QTi]. pose proof (QTi (qmeter_tight S HQ)) as QT'.
pose proof SK as [Hmbr (mat & matV & mat' & Emdz & GOK & MW2 & EG) LEz IOz MWz MONz VISM VISH VISQ ABz INCz AMAPz AHULLz OUTz].
set (mdN := with_vm_backing (m_vm_lazy md0) mat md0) in *.
assert (LN : ALedger tfibsegs ly S mdN) by exact (ledger_wvb ly S md0 mat (proj1 (proj2 HAR))).
assert (MWN : amwf mdN) by exact (amwf_wvb md0 mat (mwf_AR ly S W mem0 md0 HAR)).
(* the ledger of the grown layout at the kernel's model *)
assert (LEDz : ALedger tfibsegs lyF (SF grow z) mdz).
{ pose proof (LED0 z mdN Hev MWN LN GOK) as L0.
  destruct grow eqn:Eg; unfold AGif4.sec_md in Emdz; cbv beta iota zeta in Emdz; subst mdz.
  - set (md2 := mmap_model (YG0d.w64 mb) (YG0d.w64 MSv) mdN) in *.
    set (mdV := with_vm_backing (m_vm_lazy md2) matV md2).
    set (md5 := grant_md false (Z_to_bv 64 50) (YG0d.w64 (AGjm.QSv ly idx)) (YG0d.w64 131072) mdV).
    apply (ALedger_same tfibsegs lyF (SF true z) md5); [| apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb].
    apply (LED1 z mdV md5 (proj1 Hgrow eq_refl)).
    + exact (amwf_same md2 mdV (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) MW2).
    + exact (ALedger_same tfibsegs lyF (SF false z) md2 mdV L0 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)).
    + reflexivity.
    + pose proof (EG eq_refl) as E. rewrite eager_used_wvb in E. unfold mdV. rewrite eager_used_wvb. exact E.
  - exact (ALedger_same tfibsegs lyF (SF false z) _ _ L0 (m_vmmaps_wvb _ _ _) (m_vm_lazy_wvb _ _ _) (eager_used_wvb _ _)). }
(* the machine post, over the final world *)
destruct SFN as [[memD [DPm [PRD EQD]]] MEQF PRS PRmap PRsh PRq PRW VISW R10 RCS Vsh Vzs Vpb Vunw Vres Vnch Vmtx Vpad Vslot Vh0 Vh8 Vh16 Vh24 Vmag Vbk Vst Vb1 Vb2 Vn Vfill].
cbv beta in DPm. destruct DPm as (_ & DEPD & CSTD).
assert (RXz : forall m, rd_ext (aview tfibsegs (w_H W) m) (aview tfibsegs (w_H Wz) m)) by (intros m; apply aview_ext; [apply w_Hoff | exact LEz]).
pose proof (depot_mem_ok_rdext ly _ _ _ (RXz memD) DEPD) as DEPDz.
pose proof (Forall_cell_holds_ext B ly _ _ _ (RXz memD) CSTD) as CSTDz.
(* the walk's frame and the seed's junk atoms, which the transport's section reads *)
destruct WFR as (Hsp & _ & Hso & Hbp & Hpres0).
pose proof LYg as LY. pose proof (img_cover_of_ledger ly S md0 (proj1 (proj2 HAR))) as IMG.
assert (HTSD : ly_tsd ly = TFIB_TSD) by (rewrite (am_tsd _ _ _ _ Mg); exact (ts_tsd B TS)).
assert (HIS : as_inst B = bv_unsigned (getr regs0 11)) by (rewrite EI11; exact (ts_inst B TS)).
pose proof Hinst_g as Hinst. pose proof Hidx_g as Hidx. pose proof Hres_g as Hres. pose proof Hmap_apart_g as Hmap_apart. pose proof Mg as HARm.
pose proof (view_AR ly S W mem0 md0 HAR) as SV.
pose proof (AGjm.BSLv_range ly regs0 n tr idx res mb Htrlen Hinst_g NrangeS Hidx_g) as HB. rewrite EI11 in HB.
destruct (AGif2.sv_junk_values B W ly TFIB_INST mem0 idx res TS SV (AGjm.BSLv regs0 n) ltac:(unfold o_sec_stats; lia) ltac:(unfold o_sec_mutex; lia)) as
  (j0 & j1 & j2 & j3 & j4 & j5 & j6 & j7 & j8 & j9 & i1 & i2 & i3 & Hj0 & Hj1 & Hj2 & Hj3 & Hj4 & Hj5 & Hj9 & Hj6 & Hj7 & Hj8 & Hi1 & Hi2 & Hi3).
rewrite <- EI11 in Hj6, Hj7, Hi1, Hi2, Hi3.
(* fin_facts' instance cells are at the walk's x11 (instance-relative); the sfin facts are at TFIB_INST *)
rewrite <- EI11 in Vres, Vnch, Vmtx, Vpad.
assert (VISQ' : grow = true -> forall x : word, AGif4.QRz ly res (bv_unsigned x) -> w_H Wz x = false).
{ intros Eg x Hx. apply (VISQ Eg x). pose proof (proj1 Hgrow Eg) as EIR. unfold AGif4.QRz in Hx. unfold AGjm.QSv. rewrite EIR.
  unfold kPtrArrayEntriesPerCommit in Hx. lia. }
assert (ART : AR tfibsegs B lyF (SF grow z) Wz mem' mdz).
{ unfold AGif4.SFSz. change ImgBaseAGS.sfinal with AFib.sfinal. change ImgBaseAGS.MSv with AGjm.MSv. change ImgBaseAGS.NDv with AGjm.NDv.
  eapply AGjy.AR_transport; try eassumption; try reflexivity.
  all: try (econstructor; eassumption).
  all: try exact (conj WF' QT').
  Unshelve. all: first [exact (fun (_ : Z) (_ : word -> option byte) => True) | exact (@nil word) | exact regs0 | exact 0]. }
split; [exact ART|]. split; [exact QT'|]. split; [exact lyF_le|]. split; [exact user_addr|].
split; [intros a Ra NO NO' NS NE; exact (frame_grant grow z Wz mem' Hgrow WF' MONz OUTz MEQF a Ra NO NO' NS NE)|].
exact (frame_grant_raw grow z mem' MEQF).
Qed.
End g.

Lemma post_grant_S : forall inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem',
(inst = TFIB_INST /\ AR tfibsegs B ly S W mem0 md0) -> (aregime S /\ qmeter S) -> 64513 <= n < MALLOC_MAX ->
blocks_bytes S + n <= LIVE_MAX -> tr_admit (as_universe B) S tr ->
wframe W ly regs0 mem0 tr -> getr regs0 11 = YG0d.w64 inst ->
(grow = true <-> Z.of_nat (length (st_sec_arr S)) = st_sec_reserved S) ->
AGif4.skern grow W Wz md0 mdz ly mb (AGjm.MSv n) (AGjm.QSv ly (Z.of_nat (length (st_sec_arr S)))) ->
AGif4.sfin W ly regs0 mem0 inst n tr (Z.of_nat (length (st_sec_arr S))) (st_sec_reserved S) mb
  (fun zz m => dpost_cgif B inst ly S W tr zz m) grow z Wz regs' mem' ->
aok S (KDepot tr) z ->
(inst = TFIB_INST /\ AR tfibsegs B (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) Wz mem' mdz) /\
qtight (AGif4.SFSz S n tr z grow) /\
layout_le (length (st_secs S)) ly (AGif4.lyFz ly S mb) /\
sptr_addr B (AGif4.lyFz ly S mb) (ck_user (AFib.KS S n)) = AGjm.Uv mb /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) a ->
   ~ ascratch B AFSTACK_G regs0 a -> ~ (AGjm.Uv mb <= a < AGjm.Uv mb + req_size n) ->
   aview tfibsegs (w_H Wz) mem' a = aview tfibsegs (w_H W) mem0 a) /\
(forall x : word, ~ aowned B ly S (bv_unsigned x) -> ~ aowned B (AGif4.lyFz ly S mb) (AGif4.SFSz S n tr z grow) (bv_unsigned x) ->
   ~ ascratch B AFSTACK_G regs0 (bv_unsigned x) -> ~ (AGjm.Uv mb <= bv_unsigned x < AGjm.Uv mb + req_size n) -> mem' x = mem0 x).
Proof.
intros inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' [-> HAR] [Hev HQ] Nr Hlive Htr WFR Hi11 Hgrow SK SFN AOK.
pose proof (AGif4.sk_mbr _ _ _ _ _ _ _ _ _ SK) as Hmbr. destruct (AGif4.sk_md _ _ _ _ _ _ _ _ _ SK) as (mat & matV & mat' & _ & GOK & _).
pose proof (size_facts_m n Nr) as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
pose proof (apart_AR ly S W mem0 md0 mat (AGjm.MSv n) (YG0d.w64 mb) HAR ltac:(unfold MALLOC_MAX in *; lia) Z9 GOK) as (ZN & GAP & _).
pose proof (AFia.grant_parts _ _ _ GOK) as (AL & _).
assert (Umb : bv_unsigned (YG0d.w64 mb) = mb) by (unfold YG0d.w64; apply unsigned_lit_small; exact Hmbr).
rewrite Umb in ZN, GAP, AL.
pose proof (w64_inst regs0 Hi11) as EI11. pose proof WFR as (_ & Htrlen & _).
pose proof (post_grant_g ly S W mem0 md0 regs0 n tr mb HAR Htrlen EI11 Nr (conj AL ZN) GAP grow z Wz mdz regs' mem'
  Hev HQ Hlive Htr WFR Hgrow SK SFN AOK) as (A1 & A2 & A3 & A4 & A5 & A6).
split; [split; [reflexivity | exact A1]|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5 | exact A6].
Qed.

End b.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interface, discharged at cgif_file's instance.                                                               *)
Theorem ifaceS_cgif (B : asyms) (cf : Z) : TfibSyms B -> tfib_depot_spec B ->
AGif4.AIfaceS B (fun tr S => tr_admit (as_universe B) S tr) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX
  qtight (dpost_cgif B) 3 12.
Proof.
intros TS HD1. constructor.
- intros inst ly S W mem md n [-> HAR] _ _. exact (view_AR B TS ly S W mem md HAR).
- intros n tr S Nr FP. exact (shape_S n tr S Nr FP).
- intros inst ly S W mem md [_ HAR]. exact (fresh_AR B ly S W mem md HAR).
- intros inst ly S W mem0 md0 tr Wy regs mem md buf HARX. exact (depot_S B TS HD1 inst ly S W mem0 md0 tr Wy regs mem md buf HARX).
- intros inst ly S W mem md [_ HAR]. exact (mwf_AR B ly S W mem md HAR).
- intros inst ly S W mem md n [_ HAR] [_ HQ]. exact (room_AR B ly S W mem md HAR HQ).
- intros inst ly S W mem md [_ HAR]. exact (ledger_AR B ly S W mem md HAR).
- intros inst ly S W mem md mat sz [_ HAR] Hsz. exact (grant_AR B ly S W mem md mat sz HAR Hsz).
- intros inst ly S W mem md mat sz a [_ HAR]. exact (apart_AR B ly S W mem md mat sz a HAR).
- intros inst ly S W mem md [_ HAR]. exact (ar_oom_owned B TS ly S W mem md HAR).
- intros inst ly S W mem0 md0 n tr regs0 regs' mem' mat HARX HRP Nr Hlive Htr WFR Hi11 SN.
  exact (post_null_S B TS inst ly S W mem0 md0 n tr regs0 regs' mem' mat HARX HRP Nr Hlive Htr WFR Hi11 SN).
- intros inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HARX HRP Nr Hlive Htr WFR Hi11 Hgrow SK SFN AOK.
  exact (post_grant_S B TS inst ly S W mem0 md0 n tr regs0 mb grow z Wz mdz regs' mem' HARX HRP Nr Hlive Htr WFR Hi11 Hgrow SK SFN AOK).
Qed.

(* The widened interface at cgif's own constants (NMAXW = MALLOC_MAX, NOBW = ImgBaseAGS.NOB, ROOMW = 2 ^ 30, the
   model's VM_HEAD), the form AGio.alloc_sec_w takes. *)
Theorem ifaceS_cgif_w (B : asyms) (cf : Z) : TfibSyms B -> tfib_depot_spec B ->
AGif4.AIfaceSw B (fun tr S => tr_admit (as_universe B) S tr) malloc (ARX_cgif B) (aowned B) rpre_cgif MALLOC_MAX LIVE_MAX
  qtight (dpost_cgif B) 3 12 MALLOC_MAX ImgBaseAGS.NOB (2 ^ 30).
Proof. intros TS HD1. exact (AGif4.AIfaceS_w _ _ _ _ _ _ _ _ _ _ _ _ (ifaceS_cgif B cf TS HD1)). Qed.
End a.

(* AGio.alloc_sec_w's three premises on the bounds (the walk's own cap, the instance's grant-existence bound NOBW
   and its room ROOMW), at cgif_file's values (NMAXW = MALLOC_MAX, NOBW = ImgBaseAGS.NOB = 2 ^ 29, ROOMW = the
   model's VM_HEAD = 2 ^ 30) and at the shared preset instance's (NMAXW = 2 ^ 28 + 2 ^ 27, the same NOBW and
   ROOMW).  Arithmetic only: no instance's constant appears in a statement of the walk or of the interface. *)
Lemma nmaxw_cgif_ok : MALLOC_MAX + 4 * 4096 <= 2 ^ 29 /\ MALLOC_MAX + 4 * 4096 <= ImgBaseAGS.NOB /\
2 * (MALLOC_MAX + 4 * 4096) + (MALLOC_MAX + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= 2 ^ 30.
Proof. unfold MALLOC_MAX, ImgBaseAGS.NOB. repeat split; vm_compute; discriminate. Qed.
Example sec_w_preset_room : 402653184 + 4 * 4096 <= 2 ^ 29 /\ 402653184 + 4 * 4096 <= ImgBaseAGS.NOB /\
2 * (402653184 + 4 * 4096) + (402653184 + 4 * 4096) / 8 + 8192 + 2 ^ 19 <= 2 ^ 30.
Proof. unfold ImgBaseAGS.NOB. repeat split; vm_compute; discriminate. Qed.
