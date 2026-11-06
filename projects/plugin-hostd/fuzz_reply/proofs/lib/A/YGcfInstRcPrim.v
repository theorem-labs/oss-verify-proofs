(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/YGcfInstRcPrim.v (commit f02099425ace, round-3 cf layer, field round 3 (d0377850faa + 91bb9319bae); reply-rccf; file sha256 8d5974deaca8) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b (second hand of the lane): the PRIMARY arm of
   __asan::QuarantineCallback::Recycle's read fields over the drain's cut
   relation, the cf twin of YFf3.rc_fin_ARm (YFf3.v:678).
   rule 24: no function proved (kind: relational transport of the RChunk post to the cf cut relation ARcfR).

   Lane B1's slice H4 states the read fields of Recycle over an opaque cut relation (DMrcReads.v at
   commit cfe12703b567, proofs/cgif/cgif_file_fuzzer/lib/DMrcReads.v: rc_head_t, rc_model_t, rc_prim_fh_t,
   rc_prim_step_t; rc_prim_room_t at commit 6fdbdd538bcf).  This file proves four of
   them at the cf instance, GENERICALLY over ImgBase.AImg (im_segs), with
     ARXr := YGcfInstDrainR.ARXr_cf B IOK Hp, AOX := aowned B, DRq := YGcfInstDrainR.DRq_cf B NMAXD,
   in the fields' own shape, so B1 instantiates IM at its unit's image when it plugs them in:
   - [rc_head_cf]: the chunk at the head of DRq_cf is live, quarantined and no longer in the quarantine's items
     (RIx_cf's item facts; H4's field at commit f713e8280c3);
   - [rc_model_cf]: along every path of recycle_chunk, DRq_cf moves to the rest of the list (H4's revised field, the
     MODEL half alone; [rc_model_full_cf] / [rc_model_puser_cf] / [rc_model_aox_cf] keep the puser and owned-set
     conjuncts the first text carried, from YG03cf.recycle_chunk_okx_cf);
   - [rc_prim_step_cf]: the STEP transport of the primary arm (no map change).  The memory premise is the walk's OWN
     frame, as F12 is worded: the view keeps every byte off the walk's window YFf3.D (the stack window, the chunk's
     header words, the thread stats words, the chunk's shadow), every visible byte stays visible, the chunk's shadow
     reads shHeapLeftRz, and the hidden band bytes keep their memory.  The conclusion is H4's five conjuncts:
     ARXr_cf at YFf3.X1 (the chunk deleted), CacheDealloc's model premises [cd_model_cf] for the user object, the
     window in the owned set or the stack scratch, the owned set shrinks, and puser off the chunk's own extent is
     apart from the window.  (H4 DROPPED the sixth conjunct, puser grows: it is definitional.)
  - [rc_prim_room_cf]: H4's ROOM field (rc_prim_room_t, DMrcReads.v:99-103 at commit 6fdbdd538bcf), the growth
    arm's byte budget at the call, from AbudgetRestate's room of record at the drain cut (YGcfRoomCf.room_rec_cf_of_cut
    with the pending allowance and the unit's admission cf_hull_ok from DRq_cf's conjuncts) and
    YGcfCker.room_wA_parts_R.
   [cd_model_cf] is DMwalkIF.cd_model (DMwalkIF.v:457-468 at cfe12703b567) VERBATIM, restated here because DMwalkIF is
   stated over cgif's image.  Its RMAXD premise here is [HRMAX]: kFreeArrayOffset <= RMAXD.  With DMwalkIF.rmaxd_ok
   (2 ^ 31 <= RMAXD <= kFreeArrayOffset, DMwalkIF.v:307) that pins RMAXD = kFreeArrayOffset at the cf instance, which
   is the value DMwalkIF.v:302-306 names for cf: a cf class's mapped user part reaches kFreeArrayOffset, so no
   smaller RMAXD can bound rg_alloc_user there.
   rc_prim_fh_t (the cut-read seed, cgif's YFfr.FH_ok over YFgs.REG0's image literals) is NOT here: its discharge is
   B1 H4's at the unit's image (ReallocPrimary, 2026-10-30).
   Memory premise (H4's revision 01:59Z, reviewer RevRcReads): the walk's own frame, plus [CONST'], the constant
   cells of the image hold after the call (the cf twin of YFf3's CONST' hypothesis, YFf3.v:47; the walk discharges
   it from the image's const table, so NO image fact enters this file).
   The free-side ledger conjunct (abudget_ok_cf's A_bytes (w_A W) <= abudget_cf S) is carried, not discharged: the
   primary arm changes neither w_A nor abudget_cf ([abudget_X1]).
   Image-free otherwise and event-free (no event-count term, no event regime and no event-keyed budget appears). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03cf YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import YGcfInstDrainR YGcfInstDrainRL.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfInstBase YGcfInstDrainX.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfDIface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcfRoomCf YGcfCker YGcfAbudget YGcfSecsStep YGcfRoomStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AFeu AFf3.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope Z_scope.
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg} {DI : DImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The model premise's text.                                                                                        *)
(* DMwalkIF.cd_model (DMwalkIF.v:457-468 at cfe12703b567), verbatim. *)
Definition cd_model_cf (RMAXD : Z) (S : astate) (c off : Z) : Prop :=
1 <= c <= 30 /\ st_cache_inited S = true /\
Z.of_nat (length (pc_chunks (cache S c))) <= max_cached c /\
pc_max (cache S c) = max_cached c /\
0 <= off - region_off c /\ off - region_off c < rg_alloc_user (reg S c) /\
(off - region_off c) mod class_size c = 0 /\ ~ In (off - region_off c) (class_elems S c) /\
rg_alloc_user (reg S c) <= RMAXD /\ rg_alloc_user (reg S c) mod class_size c = 0 /\
0 <= fa_len (rg_free (reg S c)) /\ 4 * fa_len (rg_free (reg S c)) <= rg_mapped_fa (reg S c) /\
rg_mapped_fa (reg S c) <= kFreeArrayMax /\ rg_mapped_fa (reg S c) mod kFreeArrayMapSize = 0 /\
fa_len (rg_free (reg S c)) + max_cached c / 2 <= 2 ^ 27 /\
(rg_mapped_fa (reg S c) < 4 * (fa_len (rg_free (reg S c)) + max_cached c / 2) ->
 rg_mapped_fa (reg S c) + kFreeArrayMapSize <= kFreeArrayMax).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Generic helpers.                                                                                                 *)
Lemma pairwise_nth_f : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Lemma Forall_flat_map_in : forall {A C} (Q : C -> Prop) (f : A -> list C) l x, Forall Q (flat_map f l) -> In x l -> Forall Q (f x).
Proof. intros A C Q f l x H Hx. apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) H). apply in_flat_map. exists x. auto. Qed.

(* copy of YFex.v:70 *)
Lemma find_chunk_at_app_cf : forall B ly l1 l2 g,
find_chunk_at B ly (l1 ++ l2) g = match find_chunk_at B ly l1 g with Some x => Some x | None => find_chunk_at B ly l2 g end.
Proof. intros B ly l1 l2 g. induction l1 as [|x t IH]; cbn; [reflexivity|]. destruct (_ && _); [reflexivity | exact IH]. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The primary step at the relation.                                                                                *)
Section M.
Variable B : asyms.
Variable ly : alayout.
Variable X : astate.
Variable Hp : list Z.
Variables (kq : chunk) (off sp : Z).
Variables (W : world im_segs) (mem mem' : word -> option byte) (md : Model).
Local Notation rd := (aview im_segs (w_H W) mem).
Local Notation rd' := (aview im_segs (w_H W) mem').
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation base := (ck_base B ly kq).
Local Notation uu := (ck_base B ly kq + ck_rz kq).
Local Notation nn := (ck_n kq).
Local Notation kc := (prim_class off).
Local Notation X1 := (AFf3.X1 X kq).
Local Notation DDk := (AFf3.D B ly kq sp).
Local Notation DHk := (AFf3.DH B ly kq).

Hypothesis MR : ARcfR im_segs B ly X Hp W mem md.
Hypothesis Hk : In kq (st_chunks X).
Hypothesis Hst : ck_state kq = CQuarantined.
Hypothesis Hb : ck_beg kq = PPrim off.
Hypothesis Hni : ~ In (ck_beg kq) (map ck_beg (q_items X)).
Hypothesis Hsp : ly_stk_lo ly + AFeu.KSTACK <= sp <= ly_stk_hi ly.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> ~ DDk a -> rd' a = rd a.
Hypothesis VIS : forall a, rd a <> None -> rd' a <> None.
Hypothesis NEW_sh : forall a, DHk a -> rd a <> None -> rd' a = Some shHeapLeftRz.
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).

Lemma rM : ARmcfR B ly X Hp rd. Proof. exact (proj1 MR). Qed.
Lemma rLO : layout_ok ly. Proof. exact (amr_layout _ _ _ _ _ rM). Qed.
Lemma rWF : WfR_cf (as_universe B) 0 0 0 X. Proof. exact (amr_wfr _ _ _ _ _ rM). Qed.
Lemma rSY : asyms_ok B. Proof. exact (amr_syms _ _ _ _ _ rM). Qed.
Lemma rLED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.

(* the static extents: 0 prim, 1 Q, 2 T, 3 F, 4 NB, 5 SB, 6 C, 7 D, 8 stack, 9 image *)
Lemma SX : forall i j x y, (i < j)%nat -> nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y ->
zdisjoint x y.
Proof. intros i j x y Hij Hi Hj. exact (pairwise_nth_f zdisjoint _ i j x y (lo_disj _ rLO) Hij Hi Hj). Qed.
Ltac sx i j := let D := fresh "DJ" in pose proof (SX i j _ _ ltac:(lia) eq_refl eq_refl) as D; unfold zdisjoint in D; cbn [fst snd] in D.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The state after the deletion.                                                                                    *)
Lemma SPLIT : exists l1 l2, st_chunks X = l1 ++ kq :: l2 /\ st_chunks X1 = l1 ++ l2 /\
~ In (ck_beg kq) (map ck_beg l1) /\ ~ In (ck_beg kq) (map ck_beg l2).
Proof.
destruct (In_split_beg _ _ Hk (wfr_chunks_nodup _ _ _ _ _ rWF)) as (l1 & l2 & E & N1 & N2). exists l1, l2.
split; [exact E|]. split; [|split; [exact N1 | exact N2]]. unfold AFf3.X1. cbn [st_chunks set_chunks]. rewrite E.
apply del_chunk_present. exact N1.
Qed.

Lemma DEL : WfR_cf (as_universe B) 0 0 0 X1 /\ 1 <= kc <= 30 /\ 0 <= off - region_off kc < rg_alloc_user (reg X kc) /\
(off - region_off kc) mod class_size kc = 0 /\ ~ In (off - region_off kc) (class_elems X1 kc).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
assert (EX : X1 = set_chunks (l1 ++ l2) X) by (unfold AFf3.X1; rewrite <- E1; reflexivity).
rewrite EX. destruct (WfR_del_prim_cf (as_universe B) 0 0 0 X l1 kq l2 off rWF E Hb Hst Hni) as (W1 & G1 & G2 & G3 & G4 & _).
cbv zeta in *. split; [exact W1|]. split; [exact G1|]. split; [exact G2|]. split; [exact G3 | exact G4].
Qed.

Lemma X1_cinit : st_cache_inited X1 = st_cache_inited X. Proof. reflexivity. Qed.
Lemma X1_cache : st_cache X1 = st_cache X. Proof. reflexivity. Qed.
Lemma X1_sec_arr : st_sec_arr X1 = st_sec_arr X. Proof. reflexivity. Qed.
Lemma X1_sec_res : st_sec_reserved X1 = st_sec_reserved X. Proof. reflexivity. Qed.
Lemma X1_regions : st_regions X1 = st_regions X. Proof. reflexivity. Qed.
Lemma frames' : frames X1 = frames X. Proof. reflexivity. Qed.
Lemma all_batches' : all_batches X1 = all_batches X. Proof. reflexivity. Qed.

Lemma fa_poison' : fa_poison_ranges ly X1 = fa_poison_ranges ly X.
Proof. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold fa_poison_ranges, reg. rewrite X1_regions, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma sec_extents' : sec_extents ly X1 = sec_extents ly X.
Proof. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_extents. rewrite E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma aareas' : aareas X1 = aareas X.
Proof. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold aareas, reg. rewrite X1_regions, X1_sec_res, E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma sec_live' : sec_live_bytes X1 = sec_live_bytes X.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_live_bytes. rewrite E1, E. clear E E1.
induction l1 as [|y t IH]; cbn; [rewrite Hb; reflexivity | rewrite IH; reflexivity].
Qed.
Lemma sec_live_hulls' : sec_live_hulls X1 = sec_live_hulls X.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_live_hulls. rewrite E1, E. clear E E1.
induction l1 as [|y t IH]; cbn; [rewrite Hb; reflexivity | rewrite IH; reflexivity].
Qed.
Lemma sec_cells_X1 : sec_cells X1 = sec_cells X.
Proof. destruct SPLIT as (l1 & l2 & E & E1 & _). unfold sec_cells. rewrite E1, E, !flat_map_app. cbn [flat_map]. rewrite Hb. reflexivity. Qed.
Lemma abudget_X1 : abudget_cf X1 = abudget_cf X.
Proof. unfold abudget_cf. rewrite sec_live', (cf_hull_frame X X1 eq_refl sec_live_hulls'). reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The geometry.                                                                                                    *)
Lemma geom_base : 1 <= kc <= 30 /\ base = region_base ly kc + (off - region_off kc) /\ 0 <= off - region_off kc /\
(off - region_off kc) mod class_size kc = 0 /\ (off - region_off kc) + class_size kc <= rg_alloc_user (reg X kc) /\
rg_alloc_user (reg X kc) <= rg_mapped_user (reg X kc) <= kFreeArrayOffset.
Proof.
pose proof (RL.chunk_facts_cf B ly X Hp _ kq rM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Hb in GG. cbv zeta in GG.
destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
split; [exact C1|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|]. split; [exact C8 | exact C9].
Qed.

Lemma geom_rz : base mod 16 = 0 /\ 16 <= ck_rz kq <= 2048 /\ ck_rz kq mod 16 = 0 /\ 1 <= nn /\
ck_rz kq + nn <= ck_extent kq /\ ck_extent kq = class_size kc /\ 32 <= class_size kc <= kMaxSize /\
sptr_addr B ly (ck_user kq) = uu /\ 0 <= ck_req kq.
Proof.
pose proof (RL.chunk_facts_cf B ly X Hp _ kq rM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Hb in GG. cbv zeta in GG.
destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9).
pose proof (req_size_bounds (ck_req kq) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (class_ok (prim_class off) ltac:(lia)) as (K1 & K2 & K3 & _).
assert (K0 : 32 <= class_size (prim_class off)) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
unfold ck_n. split; [exact G3|]. split; [exact G5|]. split; [exact G6|]. split; [lia|]. split; [exact G8|].
split; [exact C4|]. split; [lia|]. split; [exact G4 | lia].
Qed.

Lemma k_prim : ly_prim ly <= base /\ base + ck_extent kq <= ly_prim ly + kPrimResvSize /\ kHighMemBeg <= base /\
region_base ly kc <= base /\ base + ck_extent kq <= region_base ly kc + kFreeArrayOffset.
Proof.
pose proof geom_base as (G1 & G2 & G3 & G4 & G5 & G6). pose proof geom_rz as (_ & _ & _ & _ & _ & R6 & _).
pose proof (region_in_prim ly kc rLO ltac:(lia)) as (R1 & R2 & _ & R4 & _). unfold kFreeArrayOffset in *. lia.
Qed.

Lemma k_space : base + ck_extent kq <= SB + kRegionInfoOff.
Proof.
pose proof k_prim as (_ & _ & _ & _ & K5). pose proof geom_base as (G1 & _).
pose proof (region_off_eq kc ltac:(lia)) as RO. unfold region_base in K5. rewrite RO in K5.
unfold kFreeArrayOffset, kRegionInfoOff in *. nia.
Qed.

Lemma rT : in_app T kThreadObjSize /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ ly_stk_lo ly mod 4096 = 0.
Proof.
pose proof (lo_high _ rLO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IT.
cbn [fst snd] in IT. pose proof (lo_top _ rLO) as (_ & _ & _ & T4 & T5 & _ & T7). unfold page_aligned in T5.
split; [exact IT|]. split; [lia|]. split; [lia|]. split; [exact T7|]. split; [exact T4 | exact T5].
Qed.

Lemma u_al8 : uu mod 8 = 0 /\ base mod 8 = 0 /\ ck_rz kq mod 8 = 0.
Proof.
pose proof geom_rz as (B16 & _ & R16 & _).
assert (B8 : base mod 8 = 0) by (pose proof B16 as B0; apply Z.mod_divide in B0 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (2 * q); lia).
assert (R8 : ck_rz kq mod 8 = 0) by (pose proof R16 as R0; apply Z.mod_divide in R0 as [q Hq]; [|lia]; apply Z.mod_divide; [lia|]; exists (2 * q); lia).
split; [|split; [exact B8 | exact R8]]. apply Z.mod_divide in B8 as [q Hq]; [|lia]. apply Z.mod_divide in R8 as [q' Hq']; [|lia].
apply Z.mod_divide; [lia|]. exists (q + q'). lia.
Qed.

Lemma ext_rounded : ck_rz kq + (nn + 7) / 8 * 8 <= ck_extent kq /\ 1 <= nn /\ 0 <= (nn + 7) / 8 /\ nn <= (nn + 7) / 8 * 8 < nn + 8.
Proof.
pose proof (RL.chunk_facts_cf B ly X Hp _ kq rM Hk) as (_ & _ & _ & _ & G5 & _ & G7 & G8 & GG). unfold ck_n.
pose proof (req_size_bounds (ck_req kq) ltac:(lia)) as (Q1 & Q2 & Q3).
pose proof (rounded_size_bounds (ck_req kq) ltac:(lia)) as [R1 R2].
assert (DV : (req_size (ck_req kq) + 7) / 8 * 8 <= rounded_size (ck_req kq) /\
  req_size (ck_req kq) <= (req_size (ck_req kq) + 7) / 8 * 8 < req_size (ck_req kq) + 8).
{ pose proof (Z.div_mod (req_size (ck_req kq) + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (req_size (ck_req kq) + 7) 8 ltac:(lia)).
  apply Z.mod_divide in R2 as [q Hq]; [|lia]. nia. }
assert (RZX : ck_rz kq + rounded_size (ck_req kq) <= ck_extent kq).
{ unfold ck_extent, ck_rz. destruct (from_primary (ck_req kq)) eqn:P.
  - pose proof (primary_geometry (ck_req kq) ltac:(lia) P) as (_ & [_ P2] & _). unfold needed_size in P2. rewrite P in P2.
    unfold needed_primary in P2. lia.
  - pose proof (secondary_geometry (ck_req kq) ltac:(lia) P) as (_ & S2 & _ & [S4 _] & _). unfold needed_primary in S2.
    pose proof (rz_size_bounds (ck_req kq)). lia. }
pose proof (Z.div_pos (req_size (ck_req kq) + 7) 8). lia.
Qed.

(* The chunk's shadow is in the high shadow, under the chunk's extent. *)
Lemma DH_zone : forall a, DHk a -> (kHighShadowBeg <= a < kHighMemBeg) /\
SHADOW_OFF + base / 8 <= a < SHADOW_OFF + (base + ck_extent kq) / 8.
Proof.
intros a Ha. unfold AFf3.DH, shadow_addr in Ha.
pose proof u_al8 as (U8 & B8 & R8). pose proof k_prim as (KP1 & KP2 & KP3 & _). pose proof ext_rounded as (ER & _ & QP & _).
pose proof rT as (_ & H1 & H2 & _). pose proof geom_rz as (_ & GRZ & _).
apply Z.mod_divide in B8 as [b0 Hb0]; [|lia]. apply Z.mod_divide in R8 as [r0 Hr0]; [|lia].
assert (E1 : (base + ck_rz kq) / 8 = b0 + r0) by (rewrite Hb0, Hr0; replace (b0 * 8 + r0 * 8) with ((b0 + r0) * 8) by lia; apply Z_div_mult; lia).
assert (E2 : base / 8 = b0) by (rewrite Hb0; apply Z_div_mult; lia).
rewrite E1 in Ha.
assert (E3 : 8 * (b0 + r0 + (nn + 7) / 8) <= base + ck_extent kq) by lia.
assert (E4 : b0 + r0 + (nn + 7) / 8 <= (base + ck_extent kq) / 8) by (apply Z.div_le_lower_bound; lia).
assert (E5 : (base + ck_extent kq) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; ceil; unfold ASAN_CEIL in *; lia).
assert (E6 : kHighMemBeg / 8 <= b0) by (rewrite <- E2; apply Z.div_le_mono; lia).
change (0x7fffff800000 / 8) with 17592184995840 in E5. change (kHighMemBeg / 8) with 2199291686912 in E6.
rewrite E2. unfold kHighShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.

Lemma DH_iff : forall g, g mod 8 = 0 -> (DHk (shadow_addr g) <-> uu <= g < uu + (nn + 7) / 8 * 8).
Proof.
intros g Hg. pose proof u_al8 as (U8 & _ & _). unfold AFf3.DH, shadow_addr.
apply Z.mod_divide in Hg as [c0 Hc0]; [|lia]. apply Z.mod_divide in U8 as [a Ha]; [|lia]. rewrite Hc0, Ha.
rewrite !Z_div_mult by lia. pose proof (Z.div_pos (nn + 7) 8). pose proof geom_rz as (_ & _ & _ & NN & _). nia.
Qed.

Lemma D_cases : forall a, DDk a ->
(ly_stk_lo ly <= a < ly_stk_hi ly) \/ (base <= a < base + ck_extent kq) \/ (T + t_stats + 40 <= a < T + t_stats + 56) \/
(kHighShadowBeg <= a < kHighMemBeg /\ DHk a).
Proof.
intros a Ha. unfold AFf3.D in Ha. destruct Ha as [Y|[Y|[Y|Y]]].
- left. unfold AFf3.DS, AFeu.KSTACK in *. lia.
- right; left. pose proof geom_rz as (_ & R2 & _ & NN & R5 & _ & R7 & _).
  unfold AFf3.DK, AFf3.Mv, kChunkHeaderSize in Y. destruct Y as [Y|[_ Y]]; lia.
- right; right; left. exact Y.
- right; right; right. split; [exact (proj1 (DH_zone a Y)) | exact Y].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Bytes off the window.                                                                                            *)
Definition okk (a : Z) : Prop :=
~ (base <= a < base + ck_extent kq) /\ ~ (T + t_stats + 40 <= a < T + t_stats + 56) /\ ~ DHk a.

Lemma owned_rng : forall a, aowned B ly X a -> 0 <= a < 2 ^ 64.
Proof.
intros a Ha. pose proof (RL.AR_owned_low_law_ok_cf im_segs B ly X Hp W mem md a MR Ha) as [L1 L2].
ceil. unfold ASAN_CEIL in *. lia.
Qed.

Lemma AGk : forall a, aowned B ly X a -> okk a -> rd' a = rd a.
Proof.
intros a Ho [NK [NJ NH]]. apply AG; [exact (owned_rng a Ho)|]. intros HD.
apply D_cases in HD as [Y|[Y|[Y|[_ Y]]]].
- exact (RL.AR_stack_law_ok_cf im_segs B ly X Hp W mem md a MR Y Ho).
- exact (NK Y).
- exact (NJ Y).
- exact (NH Y).
Qed.

Lemma okk_far : forall a, ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) -> ~ (T <= a < T + kThreadObjSize) ->
~ (kHighShadowBeg <= a < kHighMemBeg) -> okk a.
Proof.
intros a NP NT NS. pose proof k_prim as (KP1 & KP2 & _).
split; [lia|]. split; [unfold t_stats, kThreadObjSize in *; lia|]. intros HD. exact (NS (proj1 (DH_zone a HD))).
Qed.

Lemma okk_T : forall a, T <= a < T + kThreadObjSize -> ~ (T + t_stats + 40 <= a < T + t_stats + 56) -> okk a.
Proof.
intros a Ha NJ. pose proof k_prim as (KP1 & KP2 & _). pose proof rT as (IT & _).
split; [sx 0%nat 2%nat; unfold kThreadObjSize in *; lia|]. split; [exact NJ|]. intros HD.
destruct (DH_zone a HD) as [[Z1 Z2] _]. ceil.
destruct IT as [IT0 [IT1|[IT2 IT3]]]; unfold kThreadObjSize, kLowShadowBeg, kHighShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okk_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ (base <= a < base + ck_extent kq) -> okk a.
Proof.
intros a Ha NK. split; [exact NK|]. pose proof rT as (_ & H1 & _).
split; [sx 0%nat 2%nat; unfold t_stats, kThreadObjSize in *; lia|]. intros HD.
destruct (DH_zone a HD) as [[Z1 Z2] _]. unfold kHighMemBeg in *. lia.
Qed.

Lemma okk_static : forall j e a, (3 <= j <= 7)%nat \/ j = 1%nat -> nth_error (static_extents ly) j = Some e ->
fst e <= a < fst e + snd e -> okk a.
Proof.
intros j e a Hj He Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app _ rLO) e ltac:(unfold static_extents in He; rewrite nth_error_app1 in He by (cbn; lia);
  eapply nth_error_In; exact He)) as HE. cbn [fst snd] in HE.
apply okk_far.
- intros HP. pose proof (SX 0%nat j _ _ ltac:(lia) eq_refl He) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
- intros HT. assert (j <> 2)%nat by lia. destruct (Nat.lt_ge_cases j 2).
  + pose proof (SX j 2%nat _ _ ltac:(lia) He eq_refl) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
  + pose proof (SX 2%nat j _ _ ltac:(lia) eq_refl He) as D0. unfold zdisjoint in D0. cbn [fst snd] in D0. lia.
- intros HS. ceil. destruct HE as [H0 [HL|[HH1 HH2]]]; unfold kLowShadowBeg, kHighShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okk_img : forall a, in_zr a (ly_img ly) -> okk a.
Proof.
intros a Ha. pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _). unfold in_zr in Ha. rewrite I1 in Ha.
apply okk_far.
- intros HP. sx 0%nat 9%nat. unfold kImgLo, kImgEnd in *. lia.
- intros HT. sx 2%nat 9%nat. unfold kImgLo, kImgEnd in *. lia.
- intros HS. unfold kImgLo, kImgEnd, kHighShadowBeg in *. lia.
Qed.

Lemma okk_sec : forall e a, In e (sec_extents ly X) -> fst e <= a < fst e + snd e -> okk a.
Proof.
intros e a He Ha.
assert (D : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint e y).
{ intros j y Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ rM)) He).
  eapply nth_error_In. exact Hj. }
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ rM)) e He) as (_ & IA & _).
apply okk_far.
- intros HP. pose proof (D 0%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- intros HT. pose proof (D 2%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- intros HS. ceil. destruct IA as [H0 [HL|[HH1 HH2]]]; unfold kLowShadowBeg, kHighShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okk_hsh : forall a, SHADOW_OFF <= a < kHighMemBeg -> ~ DHk a -> okk a.
Proof.
intros a Ha NH. pose proof k_prim as (KP1 & KP2 & KP3 & _). pose proof rT as (IT & _).
split; [lia|]. split; [|exact NH]. intros HJ.
destruct IT as [IT0 [IT1|[IT2 IT3]]]; unfold t_stats, kThreadObjSize, kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

Lemma okk_chunk : forall y a, In y (st_chunks X) -> ck_beg y <> ck_beg kq -> ck_base B ly y <= a < ck_base B ly y + ck_extent y -> okk a.
Proof.
intros y a Hy Hne Ha. pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (Y1 & _).
split; [lia|]. split.
- destruct (RL.extent_zone_cf B ly X Hp _ y rM Hy) as [[P1 P2]|(m & len & Hin & E1 & E2)].
  + sx 0%nat 2%nat. unfold t_stats, kThreadObjSize in *. lia.
  + assert (DT : zdisjoint (m, len) (ly_T ly, kThreadObjSize)).
    { eapply (pairwise_In zdisjoint _ (m, len) _ (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ rM)) Hin).
      unfold static_extents, owned_extents. cbn. tauto. }
    unfold zdisjoint, kPage, t_stats, kThreadObjSize in *. cbn [fst snd] in DT. lia.
- intros HD. destruct (DH_zone a HD) as [[Z1 Z2] _]. ceil.
  destruct Y1 as [Y0 [YL|[YH1 YH2]]]; unfold kLowShadowBeg, kHighShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma okk_rinfo : forall a, SB + kRegionInfoOff <= a < SB + kRegionInfoOff + 4096 -> okk a.
Proof.
intros a Ha. pose proof (lo_space_in _ rLO) as [S1 S2]. pose proof k_space as KS.
apply okk_prim; unfold kRegionInfoOff, kSpaceSize in *; lia.
Qed.

Lemma okk_fa : forall c' a, 1 <= c' <= 31 -> fa_base ly c' <= a < fa_base ly c' + kFreeArrayMax -> okk a.
Proof.
intros c' a Hc' Ha. pose proof (region_in_prim ly c' rLO Hc') as (R1 & R2 & _).
pose proof k_prim as (KP1 & KP2 & KP3 & KP4 & KP5). pose proof geom_base as (G1 & _).
pose proof (region_off_eq c' ltac:(lia)) as RO'. pose proof (region_off_eq kc ltac:(lia)) as RO.
unfold fa_base in Ha. unfold region_base in *.
apply okk_prim; [unfold kFreeArrayOffset, kFreeArrayMax in *; lia|]. intros HK.
rewrite RO' in Ha. rewrite RO in KP4, KP5. unfold kFreeArrayOffset, kFreeArrayMax in *.
destruct (Z.lt_trichotomy c' kc) as [L|[E|L]]; [nia | subst; lia | nia].
Qed.

Lemma batch_geom : forall b, In b (all_batches X) ->
exists x, SB + b_self b = region_base ly kBatchClass + x /\ 0 <= x /\ x mod kBatchBytes = 0 /\
x + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= kFreeArrayOffset /\
In x (batch_offs X kBatchClass).
Proof.
intros b Hbb. pose proof (wfr_classes _ _ _ _ _ rWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (x := b_self b - region_off kBatchClass).
assert (INB : In x (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) x ltac:(rewrite !in_app_iff; tauto)) as [X1' X2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in X2, AA.
exists x. unfold kBatchBytes. split; [unfold region_base; subst x; lia|]. split; [lia|]. split; [exact X2|].
split; [|split; [lia | exact INB]].
apply Z.mod_divide in X2 as [q Hq]; [|lia]. apply Z.mod_divide in AA as [q' Hq']; [|lia]. nia.
Qed.

Lemma batch_vs_k : forall b, In b (all_batches X) -> zdisjoint (SB + b_self b, kBatchBytes) (base, ck_extent kq).
Proof.
intros b Hbb. destruct (batch_geom b Hbb) as (xb & Eb & Pb & Ab & Ub & [AU MU] & INB).
pose proof geom_base as (G1 & G2 & G3 & G4 & G5 & G6). pose proof geom_rz as (_ & _ & _ & _ & _ & R6 & _).
pose proof (wfr_classes _ _ _ _ _ rWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wrc_nodup _ _ _ _ _ _ CL) as ND. rewrite app_assoc in ND. apply NoDup_app_iff in ND as (_ & ND & _).
apply NoDup_app_iff in ND as (_ & _ & NDx).
unfold zdisjoint. cbn [fst snd]. rewrite Eb.
destruct (Z.eq_dec kc kBatchClass) as [Ec|Hc].
- pose proof (In_chunk_offs X kq off Hk Hb) as IK. rewrite Ec in *. set (xk := off - region_off kBatchClass) in *.
  assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in *.
  assert (xk <> xb). { intros E. apply (NDx xk); [exact IK | rewrite E; exact INB]. }
  unfold kBatchBytes in *. apply Z.mod_divide in G4 as [q1 Hq1]; [|lia]. apply Z.mod_divide in Ab as [q2 Hq2]; [|lia].
  assert (q1 <> q2) by (intros E; subst; lia). rewrite R6, G2. nia.
- pose proof (region_in_prim ly kc rLO ltac:(lia)) as (R1' & R2' & _).
  pose proof (region_in_prim ly kBatchClass rLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
  rewrite R6, G2. unfold region_base, kBatchBytes, kFreeArrayOffset in *. rewrite !region_off_eq in * by (unfold kBatchClass; lia).
  unfold kBatchClass in *.
  destruct (Z.lt_ge_cases kc 24).
  + pose proof (Z.mul_le_mono_nonneg_r (kc + 1) 24 (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
  + pose proof (Z.mul_le_mono_nonneg_r (24 + 1) kc (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma okk_batch : forall b a, In b (all_batches X) -> SB + b_self b <= a < SB + b_self b + kBatchBytes -> okk a.
Proof.
intros b a Hbb Ha. destruct (batch_geom b Hbb) as (xb & Eb & Pb & _ & Ub & [AU MU] & _).
pose proof (region_in_prim ly kBatchClass rLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (batch_vs_k b Hbb) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
apply okk_prim; [unfold kBatchBytes, kFreeArrayOffset in *; lia | lia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cells.                                                                                                       *)
Lemma oldc : forall c, In c (acells_cf B ly X) -> cell_holds B ly rd c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (amr_cells _ _ _ _ _ rM) c Hc). Qed.
Lemma ownc : forall c, In c (acells_cf B ly X) -> cell_bytes_owned B ly X c.
Proof. intros c Hc. exact (proj1 (Forall_forall _ _) (RL.acells_owned_cf B ly X Hp _ rM) c Hc). Qed.

Lemma cells_xfer : forall l, Forall (cell_bytes_owned B ly X) l ->
Forall (fun c => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okk (aeval B ly (c_at c) + j)) l ->
Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros l OW OK H. apply Forall_forall. intros c Hc.
eapply cell_holds_agree; [exact (proj1 (Forall_forall _ _) H c Hc)|]. intros j Hj.
exact (AGk _ (proj1 (Forall_forall _ _) OW c Hc j Hj) (proj1 (Forall_forall _ _) OK c Hc j Hj)).
Qed.

Lemma cells_rng : forall lo len l, (forall a, lo <= a < lo + len -> okk a) ->
Forall (fun c => lo <= aeval B ly (c_at c) /\ aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= lo + len) l ->
Forall (cell_bytes_owned B ly X) l -> Forall (cell_holds B ly rd) l -> Forall (cell_holds B ly rd') l.
Proof.
intros lo len l OK R OW H. apply (cells_xfer l OW); [|exact H].
eapply Forall_impl; [|exact R]. intros c [R1 R2] j Hj. apply OK. lia.
Qed.

Lemma img_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ rSY) r Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.
Lemma img_inst : forall a, as_inst B <= a < as_inst B + 3632 -> in_zr a (ly_img ly).
Proof. intros a Ha. apply (img_area (as_inst B, 3632)); [unfold asyms_areas; cbn; tauto | exact Ha]. Qed.
Lemma okk_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> okk a.
Proof. intros r a Hr Ha. exact (okk_img a (img_area r a Hr Ha)). Qed.

Ltac fcons := apply Forall_cons; [cbn; lia|].

Lemma cells_regions : Forall (cell_holds B ly rd') (flat_map (region_cells_cf X) (zseq 1 31)).
Proof.
apply cells_xfer.
- apply Forall_forall. intros c HIN. apply ownc. unfold acells_cf. rewrite !in_app_iff. left. exact HIN.
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (cl & Hcl & Hc). apply zseq_In in Hcl.
  unfold region_cells_cf, region_cells, z8, z1, c8, c1 in Hc. cbn [removelast] in Hc.
  assert (HA : SB + kRegionInfoOff + 128 * cl <= aeval B ly (c_at c) /\
    aeval B ly (c_at c) + Z.max 1 (Z.of_nat (c_w c)) <= SB + kRegionInfoOff + 128 * cl + 64).
  { destruct Hc as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; cbn [c_at c_w aeval aoff]; lia. }
  intros j Hj. apply okk_rinfo. lia.
- apply Forall_forall. intros c HIN. apply oldc. unfold acells_cf. rewrite !in_app_iff. left. exact HIN.
Qed.

Lemma cells_cache : forall c, 1 <= c <= 31 -> Forall (cell_holds B ly rd) (cache_cells X c) -> Forall (cell_holds B ly rd') (cache_cells X c).
Proof.
intros c Hc O. apply (cells_rng (T + t_cache + 80) (80 * 31)); [| |exact (RL.cache_cells_owned_cf B ly X Hp _ c rM Hc) | exact O].
- intros a Ha. apply okk_T; unfold t_cache, t_stats, kThreadObjSize in *; lia.
- pose proof (wfr_classes _ _ _ _ _ rWF c Hc) as CL. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. pose proof (class_ok c Hc) as (_ & _ & _ & K4 & _).
  unfold cache_cells, t_cache. destruct (st_cache_inited X).
  + destruct WC as [PM PL]. repeat fcons. apply Forall_forall. intros x Hx. apply in_map_iff in Hx as ([i v] & <- & Hiv).
    cbn [fst snd c_at c_w z4 c4 aeval aoff]. apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
  + repeat fcons. apply Forall_nil.
Qed.

Lemma cells_chunk : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg kq ->
Forall (cell_holds B ly rd) (chunk_cells y) -> Forall (cell_holds B ly rd') (chunk_cells y).
Proof.
intros y Hy Hne O. pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
apply (cells_rng (ck_base B ly y) (ck_rz y)); [| |exact (RL.chunk_cells_owned_cf B ly X Hp _ y rM Hy) | exact O].
- intros a Ha. apply (okk_chunk y a Hy Hne). pose proof (req_size_bounds (ck_req y) ltac:(lia)) as (_ & Q1 & _). lia.
- assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg y)) d) = ck_base B ly y + d).
  { intros d. unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg y)) d) d') = ck_base B ly y + d + d').
  { intros d d'. unfold ck_base, sptr_addr. destruct (ck_beg y) as [|o|r o|c p]; try solve [destruct GG]; cbn; lia. }
  assert (EA0 : aeval B ly (sptr_exp (ck_beg y)) = ck_base B ly y) by reflexivity.
  unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz y) 16); [apply Forall_nil|].
    assert (32 <= ck_rz y). { apply Z.mod_divide in G6 as [q Hq]; [|lia]. lia. }
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
    apply Forall_nil.
Qed.

Lemma cells_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks X1)).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
pose proof (amr_cells _ _ _ _ _ rM) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & _ & C3 & _).
rewrite E, flat_map_app in C3. cbn [flat_map] in C3. apply Forall_app in C3 as [C3a C3b]. apply Forall_app in C3b as [_ C3b].
rewrite E1, flat_map_app, Forall_app. split.
- apply Forall_flat_map'. intros y Hy. apply cells_chunk;
  [rewrite E; apply in_app_iff; left; exact Hy | intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy |
   exact (Forall_flat_map_in _ _ _ y C3a Hy)].
- apply Forall_flat_map'. intros y Hy. apply cells_chunk;
  [rewrite E; apply in_app_iff; right; right; exact Hy | intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy |
   exact (Forall_flat_map_in _ _ _ y C3b Hy)].
Qed.

Lemma cells_sec : Forall (cell_holds B ly rd) (sec_cells X) -> Forall (cell_holds B ly rd') (sec_cells X).
Proof.
intros O. apply (cells_xfer _ (RL.sec_cells_owned_cf B ly X Hp _ rM)); [|exact O].
assert (OI : forall d w, 0 <= d -> d + w <= 3632 -> forall j, 0 <= j < w -> okk (as_inst B + d + j)).
{ intros d w Hd Hw j Hj. apply okk_img. apply img_inst. lia. }
unfold sec_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; unfold o_sec_reserved in *; apply (OI 112 8); lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; unfold o_sec_n in *; apply (OI 120 8); lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; unfold o_sec_mutex in *; apply (OI 680 1); lia|].
apply Forall_app. split.
- pose proof (wsc_reserved _ (wfr_secondary _ _ _ _ _ rWF)) as SRES.
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  intros j Hj. cbn [c_at c_w aeval fst snd c8] in *.
  apply (okk_static 1 (ly_Q ly, kPtrArrayResv)); [right; reflexivity | reflexivity |
    cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia].
- apply Forall_forall. intros c Hc. apply in_flat_map in Hc as (k0 & Hk0 & Hc).
  pose proof (RL.chunk_facts_cf B ly X Hp _ k0 rM Hk0) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k0) as [|o|r o|c' p] eqn:Eb; try solve [destruct Hc].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (SM : 4096 + 17 <= sec_map_size (ck_req k0)) by (pose proof (req_size_bounds (ck_req k0) ltac:(lia)) as (_ & Q1 & _); unfold kPage in *; lia).
  destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply (okk_sec _ _ Gin); cbn [fst snd]; lia.
Qed.

Definition cell_in (lo len : Z) (ce : acell) : Prop :=
lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len.

(* copy of YFf3.v:422 *)
Lemma batch_cells_within : forall l ce, In ce (batch_cells l) ->
exists b2, In b2 l /\ cell_in (SB + b_self b2) (24 + 8 * Z.of_nat (length (b_items b2))) ce.
Proof.
induction l as [|b2 t IH]; intros ce Hce; [destruct Hce|]. cbn [batch_cells] in Hce.
destruct Hce as [<-|[<-|[<-|Hce]]]; try (exists b2; split; [left; reflexivity | unfold cell_in; cbn; lia]).
apply in_app_iff in Hce as [Hce|Hce].
- apply in_map_iff in Hce as ([i y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. exists b2.
  split; [left; reflexivity | unfold cell_in; cbn; lia].
- destruct (IH ce Hce) as (b3 & H3 & R3). exists b3. split; [right; exact H3 | exact R3].
Qed.

Lemma quar_okk : Forall (fun c => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okk (aeval B ly (c_at c) + j)) (quar_cells X).
Proof.
assert (OI : forall a, as_inst B <= a < as_inst B + 3632 -> okk a).
{ intros a Ha. apply okk_img. apply img_inst. lia. }
assert (BB : forall l, incl l (all_batches X) -> Forall (fun c => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w c)) -> okk (aeval B ly (c_at c) + j)) (batch_cells l)).
{ intros l IL. apply Forall_forall. intros ce Hce j Hj. destruct (batch_cells_within l ce Hce) as (b2 & I2 & [R1 R2]).
  pose proof (IL b2 I2) as Hb2.
  pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wfr_quarantine _ _ _ _ _ rWF)) b2 Hb2) as [L1 L2].
  apply (okk_batch b2 _ Hb2). unfold kBatchSlots, kBatchBytes in *. lia. }
unfold quar_cells, qc_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval z1 c1] in *; apply OI; unfold o_q_cmutex in *; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval z1 c1] in *; apply OI; unfold o_q_rmutex in *; lia|].
apply Forall_app. split.
- assert (OT : forall a, T + t_qc <= a < T + t_qc + 32 -> okk a).
  { intros a Ha. apply okk_T; unfold t_qc, t_stats, kThreadObjSize in *; lia. }
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OT; lia|].
  apply BB. intros b Hbb. unfold all_batches. apply in_app_iff. left. exact Hbb.
- apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval aoff z8 c8] in *; apply OI; unfold o_q_size in *; lia|].
  apply BB. intros b Hbb. unfold all_batches. apply in_app_iff. right. exact Hbb.
Qed.

Lemma cells_quar : Forall (cell_holds B ly rd) (quar_cells X) -> Forall (cell_holds B ly rd') (quar_cells X).
Proof. intros O. exact (cells_xfer _ (RL.quar_cells_owned_cf B ly X Hp _ rM) quar_okk O). Qed.

Lemma cells_fs : Forall (cell_holds B ly rd) (fs_cells X) -> Forall (cell_holds B ly rd') (fs_cells X).
Proof.
intros O. apply (cells_rng (ly_F ly) kFakeFramesOff); [| |exact (RL.fs_cells_owned_cf B ly X Hp _ rM) | exact O].
- intros a Ha. apply (okk_static 3 (ly_F ly, kFakeStackSize)); [left; lia | reflexivity | cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia].
- unfold fs_cells, kFakeFramesOff. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
  apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma cells_depot : Forall (cell_holds B ly rd) (depot_cells ly X) -> Forall (cell_holds B ly rd') (depot_cells ly X).
Proof.
intros O. apply (cells_xfer _ (RL.depot_cells_owned_cf B ly X Hp _ rM)); [|exact O].
unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c4 z4] in *; apply (okk_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply (okk_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply (okk_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply (okk_area (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_nil.
Qed.

Lemma cells_ialloc : Forall (cell_holds B ly rd) (ialloc_cells B X) -> Forall (cell_holds B ly rd') (ialloc_cells B X).
Proof.
intros O. apply (cells_xfer _ (RL.ialloc_cells_owned_cf B ly X Hp _ rM)); [|exact O].
pose proof (aso_ialloc _ rSY) as [I1 I2]. unfold ialloc_cells. cbv zeta.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply (okk_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply (okk_area (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (okk_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (okk_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_nil.
Qed.

Lemma cells_thread : Forall (cell_holds B ly rd) thread_cells -> Forall (cell_holds B ly rd') thread_cells.
Proof.
intros O. apply (cells_xfer _ (RL.thread_cells_owned_cf B ly X Hp _ rM)); [|exact O].
unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
intros j Hj. cbn [c_at c_w aeval c1 z1] in *. apply okk_T; unfold t_unwinding, t_stats, kThreadObjSize in *; lia.
Qed.

Lemma cells_X1 : Forall (cell_holds B ly rd') (acells_cf B ly X1).
Proof.
pose proof (amr_cells _ _ _ _ _ rM) as C. unfold acells_cf in C. rewrite !Forall_app in C.
destruct C as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
unfold acells_cf. rewrite !Forall_app.
split; [exact cells_regions|].
split; [apply Forall_flat_map'; intros c Hc0; pose proof Hc0 as Hc; apply zseq_In in Hc;
  exact (cells_cache c ltac:(lia) (Forall_flat_map_in _ _ _ c O2 Hc0))|].
split; [exact cells_chunks|].
split; [rewrite sec_cells_X1; exact (cells_sec O4)|].
split; [exact (cells_quar O5)|].
split; [exact (cells_fs O6)|].
split; [exact (cells_depot O7)|].
split; [exact (cells_ialloc O8) | exact (cells_thread O9)].
Qed.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* The shadow.                                                                                                      *)
Lemma head_off_k : forall g, in_head Hp g = true -> ~ (base <= g < base + ck_extent kq).
Proof.
intros g H Hg. unfold in_head in H. apply existsb_exists in H as (p & Hpp & Hpg).
apply andb_prop in Hpg as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (proj1 (Forall_forall _ _) (amr_hp_live _ _ _ _ _ rM) p Hpp) as (y & Hy & Hsy & Ep & Hn).
pose proof (RL.chunk_facts_cf B ly X Hp _ y rM Hy) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & _).
assert (Hne : ck_beg y <> ck_beg kq).
{ intros Eq. destruct SPLIT as (l1 & l2 & E & _ & N1 & N2). rewrite E in Hy.
  apply in_app_iff in Hy as [X0|[<-|X0]]; [apply N1 | rewrite Hst in Hsy; discriminate | apply N2]; rewrite <- Eq; apply in_map; exact X0. }
pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0.
unfold ck_n in Hn. rewrite Y4 in Ep. subst p. lia.
Qed.

(* The weak shadow (CfF2b 68f3ef3b4ba): a granule's shadow keeps its value, or the granule is a pending chunk's user
   granule and its shadow is present.  At X1 a pending chunk other than kq is still pending; kq's own user granules
   are the window part DHk, which the call writes (NEW_sh). *)
Lemma FIN : forall g v,
(rd (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v) \/ (pending_user_cf B ly X g /\ rd (shadow_addr g) <> None)) ->
rd' (shadow_addr g) = rd (shadow_addr g) -> ~ (uu <= g < uu + (nn + 7) / 8 * 8) ->
rd' (shadow_addr g) = Some (if in_head Hp g then shUserPoison else v) \/ (pending_user_cf B ly X1 g /\ rd' (shadow_addr g) <> None).
Proof.
intros g v [L|[(k & (Hk' & Hstk & Hnik) & HR) HP]] EQ NU; rewrite EQ; [left; exact L|].
right. split; [|exact HP]. exists k. split; [|exact HR]. split; [|split; [exact Hstk | exact Hnik]].
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). rewrite E1. rewrite E in Hk'.
apply in_app_iff in Hk' as [H|[<-|H]]; [apply in_app_iff; left; exact H | exfalso; unfold ck_n in *; lia | apply in_app_iff; right; exact H].
Qed.

Lemma shadow_X1 : shadow_ok_weak_cf B ly Hp rd' X1.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
pose proof geom_rz as (R1 & R2 & R3 & NN & EXT & _). pose proof u_al8 as (U8 & B8 & R8).
pose proof ext_rounded as (ER & _ & QP & _).
intros g v Hg8 HS'. pose proof (amr_shadow _ _ _ _ _ rM g) as SH.
pose proof (fun v0 => RL.ashadow_owned_cf B ly X Hp _ g v0 rM) as OWS.
pose proof (fun v0 => RL.ashadow_low_cf B ly X Hp _ g v0 rM) as LOWS.
unfold ashadow in HS', SH, OWS, LOWS. rewrite E1, fa_poison' in HS'. rewrite E in SH, OWS, LOWS.
rewrite find_chunk_at_app_cf in HS', SH, OWS, LOWS. cbn [find_chunk_at] in SH, OWS, LOWS.
assert (OTHER : forall y, In y (st_chunks X) -> ck_beg y <> ck_beg kq -> ck_base B ly y <= g < ck_base B ly y + ck_extent y ->
  aowned B ly X (shadow_addr g) -> SHADOW_OFF <= shadow_addr g < kHighMemBeg -> rd' (shadow_addr g) = rd (shadow_addr g)).
{ intros y Hy Hne Hgy HO HL. apply AGk; [exact HO|]. apply okk_hsh; [exact HL|]. intros HD. apply (DH_iff g Hg8) in HD.
  pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. lia. }
destruct (find_chunk_at B ly l1 g) as [y|] eqn:F1.
- apply find_chunk_at_In in F1 as [Hy Hgy].
  assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; left; exact Hy).
  assert (Hne : ck_beg y <> ck_beg kq) by (intros Ey; apply N1; rewrite <- Ey; apply in_map; exact Hy).
  apply (FIN g v (SH v Hg8 HS')); [exact (OTHER y Hy' Hne Hgy (OWS _ eq_refl) (LOWS _ eq_refl))|].
  intros [U1 U2]. pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy' Hk Hne) as DJ0. unfold zdisjoint in DJ0.
  cbn [fst snd] in DJ0. lia.
- destruct ((ck_base B ly kq <=? g) && (g <? ck_base B ly kq + ck_extent kq)) eqn:TK.
  + apply andb_prop in TK as [T1 T2]. apply Z.leb_le in T1. apply Z.ltb_lt in T2.
    assert (F2 : find_chunk_at B ly l2 g = None).
    { destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2; [|reflexivity]. exfalso. apply find_chunk_at_In in F2 as [Hy Hgy].
      assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
      assert (Hne : ck_beg y <> ck_beg kq) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
      pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy' Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. lia. }
    rewrite F2 in HS'. destruct (in_rangesb g (fa_poison_ranges ly X)) eqn:RG; [|discriminate]. injection HS' as <-.
    assert (IH0 : in_head Hp g = false) by (destruct (in_head Hp g) eqn:IH; [exfalso; exact (head_off_k g IH ltac:(lia)) | reflexivity]).
    pose proof (OWS _ eq_refl) as HO. pose proof (LOWS _ eq_refl) as HL.
    apply Z.mod_divide in Hg8 as [c0 Hc0]; [|lia]. pose proof B8 as B8'. apply Z.mod_divide in B8' as [b0 Hb0]; [|lia].
    pose proof R8 as R8'. apply Z.mod_divide in R8' as [r0 Hr0]; [|lia].
    assert (J : (g - ck_base B ly kq) / 8 = c0 - b0).
    { rewrite Hc0, Hb0. replace (c0 * 8 - b0 * 8) with ((c0 - b0) * 8) by lia. apply Z_div_mult. lia. }
    assert (RU : ck_rz kq / 8 = r0). { rewrite Hr0. apply Z_div_mult. lia. }
    assert (G8 : g mod 8 = 0) by (rewrite Hc0; apply Z_mod_mult).
    rewrite J in SH. unfold chunk_granule in SH. rewrite RU, Hst in SH.
    set (q := (nn + 7) / 8) in *.
    destruct (Z_lt_le_dec (c0 - b0) r0) as [C1|C1].
    * replace (c0 - b0 <? r0) with true in SH by (symmetry; apply Z.ltb_lt; exact C1).
      apply (FIN g _ (SH _ G8 eq_refl)); [|intros [U1 U2]; unfold ck_n in *; nia].
      apply AGk; [exact HO|]. apply okk_hsh; [exact HL|]. intros HD. apply (DH_iff g G8) in HD. nia.
    * replace (c0 - b0 <? r0) with false in SH by (symmetry; apply Z.ltb_ge; exact C1).
      destruct (Z_lt_le_dec (c0 - b0) (r0 + q)) as [C2|C2].
      -- left. rewrite IH0. apply NEW_sh; [apply (DH_iff g G8); nia|].
         replace (c0 - b0 <? r0 + q) with true in SH by (symmetry; apply Z.ltb_lt; exact C2).
         destruct (SH shHeapFreed G8 eq_refl) as [SL|[_ SP]]; [rewrite SL; discriminate | exact SP].
      -- replace (c0 - b0 <? r0 + q) with false in SH by (symmetry; apply Z.ltb_ge; exact C2).
         apply (FIN g _ (SH _ G8 eq_refl)); [|intros [U1 U2]; unfold ck_n in *; nia].
         apply AGk; [exact HO|]. apply okk_hsh; [exact HL|]. intros HD. apply (DH_iff g G8) in HD. nia.
  + assert (NK : ~ (ck_base B ly kq <= g < ck_base B ly kq + ck_extent kq)).
    { intros X0. assert (TT : (ck_base B ly kq <=? g) && (g <? ck_base B ly kq + ck_extent kq) = true)
        by (apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia). rewrite TT in TK. discriminate. }
    destruct (find_chunk_at B ly l2 g) as [y|] eqn:F2.
    * apply find_chunk_at_In in F2 as [Hy Hgy].
      assert (Hy' : In y (st_chunks X)) by (rewrite E; apply in_app_iff; right; right; exact Hy).
      assert (Hne : ck_beg y <> ck_beg kq) by (intros Ey; apply N2; rewrite <- Ey; apply in_map; exact Hy).
      apply (FIN g v (SH v Hg8 HS')); [exact (OTHER y Hy' Hne Hgy (OWS _ eq_refl) (LOWS _ eq_refl))|].
      intros [U1 U2]. pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy' Hk Hne) as DJ0. unfold zdisjoint in DJ0.
      cbn [fst snd] in DJ0. lia.
    * apply (FIN g v (SH v Hg8 HS')); [|intros [U1 U2]; apply NK; lia].
      apply AGk; [exact (OWS _ HS')|]. apply okk_hsh; [exact (LOWS _ HS')|]. intros HD. apply (DH_iff g Hg8) in HD. apply NK. lia.
Qed.

Lemma zshadow_X1 : zshadow_ok B ly rd'.
Proof.
pose proof (amr_zshadow _ _ _ _ _ rM) as ZS. unfold zshadow_ok in ZS |- *. apply Forall_forall. intros r Hr i Hi.
pose proof (proj1 (Forall_forall _ _) ZS r Hr i Hi) as Z0. unfold shadow_of_addr in Z0 |- *.
change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)) in Z0 |- *.
rewrite AGk; [exact Z0 | exact (RL.own_shadow_zero_cf B ly X Hp _ r i rM Hr Hi)|].
apply okk_hsh; [exact (RL.zshadow_low_cf B ly X Hp _ r i rM Hr Hi)|]. intros HD.
pose proof (DH_zone _ HD) as [[Z1 Z2] _].
unfold zero_shadow_ranges in Hr. destruct Hr as [<-|Hr]; cbn [fst snd] in Hi, Z1, Z2, HD |- *.
- pose proof rT as (_ & _ & _ & H4 & H5 & H6). apply Z.mod_divide in H6 as [s0 Hs0]; [|lia].
  assert (E8 : shadow_addr (ly_stk_lo ly) + i = shadow_addr (ly_stk_lo ly + 8 * i)).
  { unfold shadow_addr. rewrite Hs0. replace (s0 * 4096) with ((512 * s0) * 8) by lia.
    replace (512 * s0 * 8 + 8 * i) with ((512 * s0 + i) * 8) by lia. rewrite !Z_div_mult by lia. lia. }
  rewrite E8 in HD. apply (DH_iff (ly_stk_lo ly + 8 * i) ltac:(rewrite Hs0; replace (s0 * 4096 + 8 * i) with ((512 * s0 + i) * 8) by lia; apply Z_mod_mult)) in HD.
  pose proof (Z.mul_div_le (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)) as MD.
  sx 0%nat 8%nat. pose proof k_prim as (KP1 & KP2 & _). pose proof ext_rounded as (ER & _ & QP & _).
  pose proof geom_rz as (_ & GRZ & _). set (q := (nn + 7) / 8) in *. nia.
- pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r ltac:(apply in_app_iff; right; exact Hr)) as [R1 R2].
  pose proof (lo_img _ rLO) as (I1 & I2 & I3 & _). rewrite I1 in R1, R2. unfold shadow_addr in Z1, Z2.
  assert (SP : 0 < snd r).
  { destruct (Z_lt_le_dec 0 (snd r)) as [Hpos|Hle]; [exact Hpos|]. exfalso.
    assert (snd r / 8 <= 0) by (apply Z.div_le_upper_bound; lia). lia. }
  assert (RB : 0 <= fst r /\ fst r + snd r <= 6778880) by (unfold kImgLo, kImgEnd in *; lia).
  assert (D1 : fst r / 8 <= 847360) by (apply Z.div_le_upper_bound; lia).
  assert (D0 : 0 <= fst r / 8) by (apply Z.div_pos; lia).
  assert (D3 : i < 6778880) by (pose proof (Z.div_le_upper_bound (snd r) 8 (snd r) ltac:(lia) ltac:(lia)) as DU; lia).
  unfold kHighShadowBeg, SHADOW_OFF in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The visible ranges.                                                                                              *)
Lemma vis_keep : forall Lr, Forall (range_vis B ly rd) Lr -> Forall (range_vis B ly rd') Lr.
Proof. intros Lr H. exact (Forall_range_vis_keep B ly rd rd' Lr VIS H). Qed.

Lemma junk_X1 : Forall (range_vis B ly rd') (ajunk_cf B ly X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_junk _ _ _ _ _ rM) as J.
unfold ajunk_cf in J |- *. unfold quar_junk, cache_junk, cache, sec_junk in J |- *.
rewrite all_batches', X1_cinit, X1_cache, X1_sec_arr, X1_sec_res, E1. rewrite E in J.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J].
apply Forall_app in J as [J3 J]. apply Forall_app in J as [J4 J]. apply Forall_app in J as [J5 J]. apply Forall_app in J as [J6 J].
apply Forall_cons; [intros i Hi; apply VIS; exact (J1 i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J2 i Hi)|].
apply Forall_app. split; [exact (vis_keep _ J3)|]. apply Forall_app. split; [exact (vis_keep _ J4)|].
apply Forall_app. split.
{ rewrite flat_map_app in J5 |- *. cbn [flat_map] in J5. apply Forall_app in J5 as [J5a J5]. apply Forall_app in J5 as [_ J5b].
  apply Forall_app. split; [exact (vis_keep _ J5a) | exact (vis_keep _ J5b)]. }
apply Forall_app. split; [|exact (vis_keep _ J)].
apply Forall_cons_iff in J6 as [J6a J6]. apply Forall_cons_iff in J6 as [J6b J6]. apply Forall_cons_iff in J6 as [J6c J6].
apply Forall_cons; [intros i Hi; apply VIS; exact (J6a i Hi)|]. apply Forall_cons; [intros i Hi; apply VIS; exact (J6b i Hi)|].
apply Forall_cons; [intros i Hi; apply VIS; exact (J6c i Hi)|].
rewrite flat_map_app in J6 |- *. cbn [flat_map] in J6. rewrite Hb in J6. cbn [app] in J6. exact (vis_keep _ J6).
Qed.

Lemma client_X1 : Forall (range_vis B ly rd') (aclient X1).
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_client _ _ _ _ _ rM) as A.
unfold aclient in A |- *. rewrite frames', E1. rewrite E in A. rewrite flat_map_app in A |- *. cbn [flat_map] in A.
unfold chunk_user at 2 in A. rewrite Hst in A. cbn [app] in A. exact (vis_keep _ A).
Qed.

Lemma hp_X1 : Forall (fun p => exists k, In k (st_chunks X1) /\ ck_state k = CAllocated /\ p = sptr_addr B ly (ck_user k) /\ cf_head <= ck_n k) Hp.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2). pose proof (amr_hp_live _ _ _ _ _ rM) as H.
eapply Forall_impl; [|exact H]. cbv beta. intros p (y & Hy & Hsy & Ep & Hn). exists y. split; [|exact (conj Hsy (conj Ep Hn))].
rewrite E1. rewrite E in Hy. apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The two machine cells of ARmcfR at X1: no byte of them is in the walk's window.                                  *)
Lemma exh_X1 : YGcfInstDrainX.EXH_OFF_OK -> exh_cell_cf B ly X rd -> exh_cell_cf B ly X1 rd'.
Proof.
intros EXO HE. apply (YGcfInstBase.exh_cell_cf_frame B ly ly X X1 rd rd' HE); [intros c; reflexivity|].
intros c Hc. destruct EXO as (E1 & _).
assert (EA : aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) = ly_space ly + kRegionInfoOff + (128 * c + cf_exh_off))
  by (cbn; lia).
rewrite EA. apply AGk.
- apply (RL.own_rinfo_cf B ly X Hp _ _ rM). unfold kRegionInfoOff in *. lia.
- apply okk_rinfo. unfold kRegionInfoOff in *. lia.
Qed.

Lemma errb_X1 : errb_obj_owned_t B -> errb_cells_cf B ly X rd -> errb_cells_cf B ly X1 rd'.
Proof.
intros EOO HEB. apply (YGcfInstBase.errb_cells_cf_frame B ly ly X X1 rd rd' HEB); try reflexivity.
- intros a Ha. pose proof (EOO a Ha) as HS. apply AGk; [exact (RL.own_static_cf B ly X Hp _ a rM HS)|]. apply okk_img.
  apply Exists_exists in HS as (r0 & Hr0 & Hin).
  pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r0 ltac:(apply in_app_iff; left; exact Hr0)) as [Z1 Z2].
  unfold in_zr in *. lia.
- exact VIS.
Qed.

(* Printf's two cells at X1 (field round 3): owned static, inside the image. *)
Lemma pf_X1 : pf_cells_owned_t B -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd'.
Proof.
intros PO HP. apply (YG0qcf.pf_cells_frame_cf B ly rd rd'); [|exact HP].
intros a Ha. pose proof (proj1 (proj1 PO a Ha)) as HS. apply AGk; [exact (RL.own_static_cf B ly X Hp _ a rM HS)|]. apply okk_img.
apply Exists_exists in HS as (r0 & Hr0 & Hin).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ rM) r0 ltac:(apply in_app_iff; left; exact Hr0)) as [Z1 Z2].
unfold in_zr in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cut record at the step.                                                                                      *)
Lemma ARmcfR_X1 : ARmcfR B ly X1 Hp rd'.
Proof.
pose proof rM as M0.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor.
- exact (proj1 DEL).
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- unfold sec_placed. rewrite sec_extents'. exact Xplaced.
- exact CONST'.
- exact Xcowned.
- exact cells_X1.
- intros c i v Hc Hi Hv kk Hkk. change (reg X1 c) with (reg X c) in *.
  pose proof (wfr_classes _ _ _ _ _ Xwf c Hc) as CL. pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL.
  pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
  assert (FA : fa_base ly c <= fa_base ly c + 4 * i + Z.of_nat kk < fa_base ly c + kFreeArrayMax) by lia.
  rewrite (AGk _ (RL.own_fa_cf B ly X Hp _ c _ rM Hc FA) (okk_fa c _ Hc FA)). exact (Xfa c i v Hc Hi Hv kk Hkk).
- intros cid pos Hc Hpos. pose proof (flag_off_bounds cid pos Hc Hpos) as FB.
  assert (OW : aowned B ly X (flag_addr ly cid pos)) by (unfold flag_addr, kFakeFlagsOff in *; eapply RL.own_F_low_cf; [exact rM | lia]).
  assert (OK : okk (flag_addr ly cid pos)) by (apply (okk_static 3 (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |
    cbn [fst snd]; unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *; lia]).
  rewrite (AGk _ OW OK). exact (Xflags cid pos Hc Hpos).
- destruct Xdepot as (heads & links & D1 & D2 & D3). exists heads, links. split; [|split; [|exact D3]].
  + intros b Hb0. destruct (D1 b Hb0) as [H1 H2]. split; [exact H1|]. intros kk Hkk.
    assert (Ha : as_depot B <= as_depot B + 4 * b + Z.of_nat kk < as_depot B + 4 * 2 ^ 20 + 32) by (unfold d_tab_words in Hb0; lia).
    assert (OW : aowned B ly X (as_depot B + 4 * b + Z.of_nat kk)) by
      (eapply (RL.own_area_cf B ly X Hp _ (as_depot B, 4 * 2 ^ 20 + 32)); [exact rM | cbn; tauto | cbn [fst snd]; lia]).
    assert (OK : okk (as_depot B + 4 * b + Z.of_nat kk)) by (apply (okk_area (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]).
    rewrite (AGk _ OW OK). exact (H2 kk Hkk).
  + intros id Hid. change (depot_ids X1) with (depot_ids X) in Hid. destruct (D2 id Hid) as (H1 & H2 & H3). split; [exact H1|].
    assert (NB : depot_ids X <= 4097).
    { unfold depot_ids. pose proof (depot_len_bound _ _ Xuni (wfr_depot _ _ _ _ _ Xwf)) as DL. unfold DEPOT_MAX in DL. lia. }
    assert (OR : forall x, ly_NB ly + 16 * id <= x < ly_NB ly + 16 * id + 16 -> rd' x = rd x).
    { intros x Hx.
      assert (OW : aowned B ly X x) by
        (eapply (RL.own_core_cf B ly X Hp _ (ly_NB ly, kNodesBlockSize)); [exact rM | unfold core_extents; cbn; tauto | cbn; unfold kNodesBlockSize; lia]).
      assert (OK : okk x) by (apply (okk_static 4 (ly_NB ly, kNodesBlockSize)); [left; lia | reflexivity | cbn [fst snd]; unfold kNodesBlockSize; lia]).
      exact (AGk _ OW OK). }
    split; intros kk Hkk; rewrite OR by lia; [exact (H2 kk Hkk) | exact (H3 kk Hkk)].
- exact shadow_X1.
- exact zshadow_X1.
- exact junk_X1.
- rewrite aareas'. exact (vis_keep _ Xareas).
- exact client_X1.
- apply Forall_forall. intros r Hr i Hi. pose proof (aso_ialloc _ Xsyms) as [I1 I2].
  assert (Ha : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
  { unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
  assert (OW : aowned B ly X (aeval B ly (fst r) + i)) by
    (eapply (RL.own_area_cf B ly X Hp _ (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [exact rM | cbn; tauto | exact Ha]).
  assert (OK : okk (aeval B ly (fst r) + i)) by (apply (okk_area (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | exact Ha]).
  rewrite (AGk _ OW OK). exact (proj1 (Forall_forall _ _) Xzero r Hr i Hi).
- exact Xtsd.
- exact Ximg.
- exact hp_X1.
- unfold xs_placed_cf. rewrite sec_extents'. exact Xxs.
- exact (exh_X1 (YGcfInstDrainX.EXH_OFF_OK_of_t (proj1 Xown)) Xexh).
- exact (errb_X1 (proj1 (proj2 Xown)) Xerrb).
- exact Xown.
- exact (pf_X1 Xpfo Xpf).
- exact Xpfo.
Qed.

Lemma ALedger_X1 : ALedger_cf im_segs ly X1 md.
Proof.
pose proof rLED as L. destruct L.
constructor; unfold eager_cf in *; try (rewrite sec_extents'); assumption.
Qed.

Lemma aclient_X1 : forall a, aclient_byte B ly X1 a -> aclient_byte B ly X a.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
intros a [(y & Hy & Hsy & Hr)|H2]; [left | right; exact H2].
exists y. split; [|split; [exact Hsy | exact Hr]]. rewrite E. rewrite E1 in Hy.
apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left; exact Hy | right; right; exact Hy].
Qed.

Lemma ARcfR_X1 : forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
ARcfR im_segs B ly X1 Hp W mem' md'.
Proof.
intros md' Ev El Ee HK. pose proof MR as (M & LED & BUD & MW & HSH).
split; [exact ARmcfR_X1|]. split; [|split; [|split]].
- eapply YG0qcf.ALedger_same_cf; [exact ALedger_X1 | exact Ev | exact El | exact Ee].
- destruct BUD as (BU1 & BU2 & BU3). split; [rewrite abudget_X1; exact BU1|]. split; [|exact BU3].
  unfold asecA in *. rewrite sec_extents'. exact BU2.
- exact (amwf_same md md' Ev El MW).
- refine (RL.ahs_transfer_cf im_segs B ly X Hp X1 (w_H W) mem mem' _ M HSH VIS HK _ sec_extents' _).
  + eapply RL.al_img_env_cf; [exact rLO | exact LED].
  + intros a _ C. exact (aclient_X1 a C).
  + intros g Hg Hga HF _. apply AGk; [eapply RL.hfree_shadow_owned_cf; [exact rM | exact Hg | exact Hga | exact HF]|].
    pose proof u_al8 as (U8 & _ & _). pose proof geom_rz as (_ & R2 & _ & NN & R5 & _).
    pose proof (Z.div_pos (nn + 7) 8 ltac:(lia) ltac:(lia)) as QP.
    pose proof (RL.hfree_shadow_off_range_cf B ly X Hp _ kq uu nn g rM Hk ltac:(lia) ltac:(lia) U8 ltac:(lia) Hg HF) as NR.
    destruct (shadow_addr_bounds g ltac:(destruct Hga; lia)) as [SB1 SB2].
    assert (SB3 : shadow_addr g < kHighMemBeg).
    { apply SB2. ceil. destruct Hga as [Hga0 [HL|[HH1 HH2]]]; unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia. }
    apply okk_hsh; [lia|]. intros HD. apply NR. unfold AFf3.DH in HD. exact HD.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The owned set, the window and the user ranges.                                                                   *)
Lemma own_ext_k : forall a, base <= a < base + ck_extent kq -> aowned B ly X a.
Proof.
intros a Ha.
assert (NB : forall y, In y (st_chunks X) -> ck_state y = CAllocated ->
  ~ (ck_base B ly y + ck_rz y <= a < ck_base B ly y + ck_rz y + req_size (ck_req y))).
{ intros y Hy Hsy Hr. pose proof (RL.user_in_extent_cf B ly X Hp _ y a rM Hy Hr) as HE.
  assert (Hne : ck_beg y <> ck_beg kq).
  { intros Eq. destruct SPLIT as (l1 & l2 & E & _ & N1 & N2). rewrite E in Hy.
    apply in_app_iff in Hy as [X0|[<-|X0]]; [apply N1 | rewrite Hst in Hsy; discriminate | apply N2]; rewrite <- Eq; apply in_map; exact X0. }
  pose proof (RL.chunks_disjoint_cf B ly X Hp _ y kq rM Hy Hk Hne) as DJ0. unfold zdisjoint in DJ0. cbn [fst snd] in DJ0. lia. }
pose proof k_prim as (KP1 & KP2 & _).
exact (RL.own_prim_nonuser_cf B ly X Hp _ a rM ltac:(lia) NB).
Qed.

Lemma D_owned : forall a, DDk a -> aowned B ly X a \/ AFf3.DS sp a.
Proof.
intros a HD. unfold AFf3.D in HD. destruct HD as [Y|[Y|[Y|Y]]].
- right. exact Y.
- left. apply own_ext_k. pose proof geom_rz as (_ & R2 & _ & NN & R5 & _ & R7 & _).
  unfold AFf3.DK, AFf3.Mv, kChunkHeaderSize in Y. destruct Y as [Y|[_ Y]]; lia.
- left. eapply (RL.own_core_cf B ly X Hp _ (ly_T ly, kThreadObjSize) a rM); [unfold core_extents; cbn; tauto|].
  cbn [fst snd]. unfold AFf3.DJ, t_stats, kThreadObjSize in *. lia.
- left. pose proof u_al8 as (U8 & _ & _). apply Z.mod_divide in U8 as [a0 Hua]; [|lia].
  unfold AFf3.DH, shadow_addr in Y. rewrite Hua, Z_div_mult in Y by lia.
  replace a with (shadow_addr ((a0 + (a - (SHADOW_OFF + a0))) * 8)).
  2:{ unfold shadow_addr. rewrite Z_div_mult by lia. lia. }
  apply (RL.own_shadow_prim_cf B ly X Hp _ _ rM). pose proof ext_rounded as (ER & _ & QP & _). pose proof k_prim as (KP1 & KP2 & _).
  pose proof geom_rz as (_ & RZ & _). clear - Y ER QP KP1 KP2 Hua RZ. nia.
Qed.

Lemma aowned_X1 : forall a, aowned B ly X1 a -> aowned B ly X a.
Proof.
destruct SPLIT as (l1 & l2 & E & E1 & N1 & N2).
intros a [Z NC]. split.
- unfold aowned in Z. rewrite sec_extents' in Z. exact Z.
- intros C. apply NC. destruct C as [(y & Hy & Hsy & Hr)|H2]; [left | right; exact H2].
  exists y. split; [|split; [exact Hsy | exact Hr]]. rewrite E1. rewrite E in Hy.
  apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
Qed.

Lemma puser_X1 : forall a, YFeuC.puser ly X a -> YFeuC.puser ly X1 a.
Proof. intros a H. exact H. Qed.

Lemma puser_notD : forall a, YFeuC.puser ly X a -> ~ (base <= a < base + ck_extent kq) -> ~ DDk a.
Proof.
intros a (c' & Hc' & Hr) NK HD. pose proof (region_in_prim ly c' rLO Hc') as (R1 & R2 & _).
pose proof (wfr_classes _ _ _ _ _ rWF c' Hc') as CL. pose proof (wrc_alloc _ _ _ _ _ _ CL) as A1.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB. pose proof rT as (_ & H1 & _).
apply D_cases in HD as [Y|[Y|[Y|[Y _]]]].
- sx 0%nat 8%nat. unfold kFreeArrayOffset in *. lia.
- exact (NK Y).
- sx 0%nat 2%nat. unfold t_stats, kThreadObjSize, kFreeArrayOffset in *. lia.
- unfold kFreeArrayOffset, kHighMemBeg in *. lia.
Qed.

Lemma cdm : forall RMAXD, kFreeArrayOffset <= RMAXD -> st_cache_inited X = true -> cd_model_cf RMAXD X1 kc off.
Proof.
intros RMAXD HR Hci. pose proof DEL as (W1 & G1 & G2 & G3 & G4).
pose proof (wfr_classes _ _ _ _ _ W1 kc ltac:(lia)) as CL.
pose proof (wrc_cache _ _ _ _ _ _ CL) as WC. change (st_cache_inited X1) with (st_cache_inited X) in WC. rewrite Hci in WC.
destruct WC as [PM PL].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as A. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AL.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F0 FM]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_runs _ _ _ _ _ _ CL) as RU.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB. pose proof (fa_len_nonneg _ RU) as FN.
pose proof (class_elems_count_cf _ _ _ _ _ kc W1 ltac:(lia)) as [CC1 CC2].
pose proof (class_ok kc ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6).
assert (M2 : max_cached kc / 2 <= 8) by (apply Z.div_le_upper_bound; lia).
assert (M0 : 0 <= max_cached kc / 2) by (apply Z.div_pos; lia).
change (reg X1 kc) with (reg X kc) in *. change (cache X1 kc) with (cache X kc) in *.
assert (LC : 0 <= Z.of_nat (length (pc_chunks (cache X kc)))) by lia.
unfold cd_model_cf. change (st_cache_inited X1) with (st_cache_inited X). change (reg X1 kc) with (reg X kc).
change (cache X1 kc) with (cache X kc).
unfold kFreeArrayOffset, kFreeArrayMax, kFreeArrayMapSize in *. change (2 ^ 27) with 134217728 in *.
split; [exact G1|]. split; [exact Hci|]. split; [exact PL|]. split; [exact PM|].
split; [lia|]. split; [lia|]. split; [exact G3|]. split; [exact G4|]. split; [lia|]. split; [exact AL|].
split; [exact FN|]. split; [exact FL|]. split; [exact FB|]. split; [exact FM|]. split; [lia|]. intros HG. lia.
Qed.
End M.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The cut-read interface of the primary seed (lane B1 H4's measured text, adopted VERBATIM
   by ReallocPrimary 2026-10-30 02:0xZ): what YFgs.free_hyps reads of the cut relation and the recycle invariant at a
   primary chunk.  H4 discharges rc_prim_fh_t from it at the unit's image; [rc_fh_cut_facts_cf] below proves it at the
   cf instance, so no unit assumes it. *)
Section fh.
Definition rc_fh_cut_facts (B : asyms)
  (ARXr : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
  (DRq : astate -> list chunk -> list Z -> Prop) : Prop :=
forall inst ly X k ks zs W mem md off,
ARXr inst ly X W mem md -> DRq X (k :: ks) zs -> ck_beg k = PPrim off ->
let rd := aview im_segs (w_H W) mem in
let c := prim_class off in
(* CF1  the instance object is the binary's allocator object *)
inst = as_inst B /\
(* CF2  the layout, the image window, the TSD slot *)
layout_ok ly /\ im_img_cover ly /\ ly_tsd ly = as_tsd B /\
(* CF3  the image's constant cells (REG0's literal and symbolic image cells) *)
Forall (cell_holds B ly rd) (as_const B ly) /\
(* CF4  k is a quarantined primary chunk of class c, inside the class's mapped user part *)
ck_state k = CQuarantined /\ 1 <= c <= 30 /\
0 <= off - region_off c /\ (off - region_off c) mod class_size c = 0 /\
off - region_off c + class_size c <= rg_mapped_user (reg X c) <= kFreeArrayOffset /\
16 <= ck_rz k <= 2048 /\ ck_rz k mod 16 = 0 /\ 0 <= ck_req k /\ ck_rz k + ck_n k <= class_size c /\
(* CF5  k's header cells (state byte, mask byte, zero half, size word) and, when rz <> 16, its magic cells *)
Forall (cell_holds B ly rd) (chunk_cells k) /\
(* CF6  class c's mapped-user word in the region-info page *)
cell_holds B ly rd (z8 (aoff (ASp (kRegionInfoOff + 128 * c)) 48) (rg_mapped_user (reg X c))) /\
(* CF7  visible: class c's mapped user part, the region-info page, the thread's stats words *)
range_vis B ly rd (ASp (region_off c), rg_mapped_user (reg X c)) /\
range_vis B ly rd (ASp kRegionInfoOff, 4096) /\
range_vis B ly rd (AT t_stats, t_unwinding - t_stats) /\
(* CF8  the shadow byte of every user granule of k is visible *)
(forall g, g mod 8 = 0 -> ck_base B ly k + ck_rz k <= g < ck_base B ly k + ck_rz k + ck_n k ->
  rd (shadow_addr g) <> None).
End fh.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The fields.                                                                                                      *)
Section F.
Variable B : asyms.
Variable IOK : Z -> Prop.
Variable Hp : list Z.
(* DRq_cf's size bound (CfF2b 2337319d6c4): a parameter, so the small arm (kQuarantineMax) and the big arm
   (NMAXD_big_cf) both instantiate these fields. *)
Variable NMAXD : Z.

(* H4's model ARM SPLIT field (commit a337c4d4e0f7, proofs/cgif/cgif_file_fuzzer/lib/DMrc.v:59): the recycled chunk is
   a primary chunk, or a live secondary whose map and pointer-array slot exist. *)
Theorem rc_split_cf : forall X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
(exists off, ck_beg k = PPrim off) \/
(exists r o sm i, ck_beg k = PSec r o /\ nth_error (st_secs X) r = Some sm /\ nth_error (st_sec_arr X) i = Some r).
Proof.
intros X k ks zs ((WF & IT & _) & _).
apply Forall_app in IT as [IT _]. apply Forall_cons_iff in IT as [[Hk Hst] _].
pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ WF) k Hk) as [Hn CK].
pose proof (wfr_secondary _ _ _ _ _ WF) as XS.
destruct (ck_beg k) as [|off|r off|c p] eqn:Eb; try solve [destruct CK].
- left. exists off. reflexivity.
- right. destruct CK as (P1 & P2 & sm & Q1 & Q2 & Q3 & Q4).
  assert (INA : In r (st_sec_arr X)) by (apply (wsc_arr_chunks _ XS r); exists k; split; [exact Hk | rewrite Eb, P2; reflexivity]).
  destruct (In_nth_error _ _ INA) as [i Hi].
  exists r, off, sm, i. split; [reflexivity | split; [exact Q1 | exact Hi]].
Qed.

(* B1's rc_head_t at DRq := DRq_cf B NMAXD (commit f713e8280c3, DMrcReads.v:56-58): the head chunk is live, quarantined, and
   not among the quarantine's items (RIx_cf: the items are live and quarantined, and NoDup over items ++ q_items). *)
Theorem rc_head_cf : forall X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
In k (st_chunks X) /\ ck_state k = CQuarantined /\ ~ In (ck_beg k) (map ck_beg (q_items X)).
Proof.
intros X k ks zs ((W & IT & ND & _) & _).
change (flat_map b_items []) with (@nil chunk) in IT, ND. rewrite app_nil_r in IT, ND.
apply Forall_cons_iff in IT as [[Hk Hst] _].
cbn [app map] in ND. apply NoDup_cons_iff in ND as [Hnk _].
split; [exact Hk|]. split; [exact Hst|].
intros Hin. apply Hnk. rewrite map_app. apply in_app_iff. right. exact Hin.
Qed.

(* The interface above, PROVED at the cf instance: no unit assumes it.  The two image premises are the layer's own
   names: YGcfInstBase.IOK_ok (the instance object) and YGcfDIface.IMG_COVER (the image window from the ledger). *)
Theorem rc_fh_cut_facts_cf : YGcfInstBase.IOK_ok B IOK -> YGcfDIface.IMG_COVER -> rc_fh_cut_facts B (ARXr_cf B IOK Hp) (DRq_cf B NMAXD).
Proof.
intros HIOK HIMG inst ly X k ks zs W mem md off (HI & HA & HX) DR Hb. cbv zeta.
pose proof (proj1 HA) as M. pose proof (proj1 (proj2 HA)) as LED.
destruct DR as ((WF & IT & ND & _) & _).
change (flat_map b_items []) with (@nil chunk) in IT. rewrite app_nil_r in IT.
apply Forall_cons_iff in IT as [[Hk Hst] _].
pose proof (RL.chunk_facts_cf B ly X Hp _ k M Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG). rewrite Hb in GG. cbv zeta in GG.
destruct GG as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & [C9 C10]).
pose proof (amr_cells _ _ _ _ _ M) as CELLS. pose proof (amr_areas _ _ _ _ _ M) as AREAS.
pose proof (amr_junk _ _ _ _ _ M) as JUNK.
split; [exact (HIOK _ HI)|].
split; [exact (amr_layout _ _ _ _ _ M)|].
split; [exact (HIMG ly X md LED)|].
split; [exact (amr_tsd _ _ _ _ _ M)|].
split; [exact (amr_const _ _ _ _ _ M)|].
split; [exact Hst|]. split; [exact C1|]. split; [exact C6|]. split; [exact C7|].
split; [split; [lia | exact C10]|].
split; [exact G5|]. split; [exact G6|]. split; [lia|].
split; [unfold ck_n; lia|].
(* CF5 *)
unfold acells_cf in CELLS. rewrite !Forall_app in CELLS.
destruct CELLS as (CR & _ & CC & _).
split; [exact (Forall_flat_map_in _ _ _ k CC Hk)|].
(* CF6 *)
split.
{ apply (proj1 (Forall_forall _ _) (Forall_flat_map_in _ _ _ (prim_class off) CR
    ltac:(unfold zseq; apply in_map_iff; exists (Z.to_nat (prim_class off - 1)); split; [lia|];
          apply in_seq; lia))).
  unfold region_cells_cf, region_cells. cbn [removelast]. right; right; right; right; right; right; left. reflexivity. }
(* CF7 *)
split.
{ apply (proj1 (Forall_forall _ _) AREAS). unfold aareas. rewrite !in_app_iff. left.
  apply in_flat_map. exists (prim_class off).
  split; [unfold zseq; apply in_map_iff; exists (Z.to_nat (prim_class off - 1)); split; [lia|]; apply in_seq; lia | left; reflexivity]. }
split.
{ apply (proj1 (Forall_forall _ _) AREAS). unfold aareas. rewrite !in_app_iff. do 3 right.
  right; right; right; right; left. reflexivity. }
split.
{ apply (proj1 (Forall_forall _ _) JUNK). unfold ajunk_cf. do 2 right. rewrite !in_app_iff. do 5 right. left.
  unfold thread_junk. right; right; left. reflexivity. }
(* CF8 *)
intros g Hg8 Hgr.
assert (HS : ashadow B ly X g = Some (chunk_granule k ((g - ck_base B ly k) / 8))).
{ unfold ashadow. rewrite (RL.find_chunk_at_hit_cf B ly X Hp _ (st_chunks X) k g M ltac:(apply incl_refl)
    (wfr_chunks_nodup _ _ _ _ _ (amr_wfr _ _ _ _ _ M)) Hk ltac:(pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _); unfold ck_n in Hgr; lia)).
  reflexivity. }
exact (shadow_present_weak_cf B ly Hp _ X g _ (amr_shadow _ _ _ _ _ M) Hg8 HS).
Qed.

(* B1's rc_model_t (H4's revision 01:59Z: the MODEL half alone) at DRq := DRq_cf B NMAXD.  [rc_model_puser_cf] and
   [rc_model_aox_cf] keep the two conjuncts the first text carried, for any caller that still needs them. *)
Theorem rc_model_full_cf : forall X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
apost (recycle_chunk k X) (fun r =>
  DRq_cf B NMAXD (snd r) ks zs /\ (forall ly a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a) /\
  (forall ly a, aowned B ly (snd r) a -> aowned B ly X a)).
Proof.
intros X k ks zs (RX & CD & UQ & Q1 & Q2 & SZ & PB & CI & HHO) tr r Hpath.
destruct RX as (W & IT & ND & BL & SF & NDS).
change (flat_map b_items []) with (@nil chunk) in IT, ND. change (map b_self []) with (@nil Z) in SF, NDS.
rewrite app_nil_r in IT, ND, SF, NDS.
apply Forall_cons_iff in IT as [[Hk Hst] ITr].
cbn [app map] in ND. apply NoDup_cons_iff in ND as [Hnk NDr].
assert (Hni : ~ In (ck_beg k) (map ck_beg (q_items X))).
{ intros Hin. apply Hnk. rewrite map_app. apply in_app_iff. right. exact Hin. }
pose proof (recycle_chunk_okx_cf (as_universe B) 0 0 0 X k true W Hk Hst Hni) as OK.
destruct (atok_apath _ true _ tr r OK Hpath) as [ns' RPX].
pose proof (recycle_post_xfr_cf _ _ _ _ _ _ _ _ RPX) as XF.
pose proof (YGcfRoomStep.ipost_apath _ _ tr r (YGcfSecsStep.ss_rchunk k X) Hpath) as [SN ST].
destruct RPX as [RP _]. destruct r as [u s1]. unfold recycle_post_cf in RP. cbn [snd] in RP, XF, SN, ST |- *.
destruct RP as (W1 & (l1 & l2 & E & E1) & Rqt & Rqg & Rnev & Rfs & Rdep & SE & AU & CE & MF & LEN & CIN).
assert (EQI : q_items s1 = q_items X) by (unfold q_items, all_batches; rewrite Rqt, Rqg; reflexivity).
pose proof (unq_del_cf X s1 l1 k l2 E E1 Hst Rqt Rqg) as UQ1.
split; [|split].
- split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  + unfold RIx_cf. change (flat_map b_items []) with (@nil chunk). change (map b_self []) with (@nil Z). rewrite !app_nil_r.
    split; [exact W1|]. split.
    * apply Forall_forall. intros k' Hk'. pose proof (proj1 (Forall_forall _ _) ITr k' Hk') as [H1 H2]. split; [|exact H2].
      rewrite E1. rewrite E in H1. apply in_app_iff in H1 as [H1|[<-|H1]]; [apply in_app_iff; left; exact H1 | exfalso | apply in_app_iff; right; exact H1].
      apply Hnk. rewrite map_app. apply in_app_iff. left. apply in_map. exact Hk'.
    * split; [rewrite EQI; exact NDr|]. split; [constructor|]. split; [|exact NDS].
      eapply Forall_impl; [|exact SF]. cbv beta. intros z (Z1 & Z2 & Z3). rewrite AU by (unfold kBatchClass; lia).
      split; [exact Z1 | split; [exact Z2|]]. intros Hin. exact (Z3 (CE kBatchClass _ ltac:(unfold kBatchClass; lia) Hin)).
  + intros c Hc. rewrite (xfr_cdef_cf _ _ _ XF c Hc). cbv beta. rewrite Z.mul_0_r, Z.sub_0_r. exact (CD c Hc).
  + rewrite UQ1. rewrite items_n_cons_cf in UQ. lia.
  + rewrite Rqt. exact Q1.
  + rewrite Rqg. exact Q2.
  + exact (Forall_inv_tail SZ).
  + rewrite items_n_cons_cf in PB. pose proof (proj1 (Forall_forall _ _) (wfr_chunks _ _ _ _ _ W) k Hk) as [Hn0 _].
    assert (NK : 0 <= ck_n k) by (unfold ck_n; pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (Q0' & Q1' & Q2'); lia).
    lia.
  + intros [(k0 & Hk0 & Hp0)|Hz]; apply CIN; apply CI; [left; exists k0; split; [right; exact Hk0 | exact Hp0] | right; exact Hz].
  + (* the unit's admission: recycle_chunk keeps both meters (YGcfSecsStep.ss_rchunk) *)
    exact (cf_hull_counts s1 X (eq_sym SN) (eq_sym ST) HHO).
- intros ly a (c' & Hc' & Hr). exists c'. split; [exact Hc'|]. rewrite AU by lia. exact Hr.
- intros ly a [Z NC]. split.
  + assert (SI : forall e, In e (sec_extents ly s1) -> In e (sec_extents ly X)).
    { intros e He. unfold sec_extents in *. rewrite E1 in He. rewrite E. apply in_flat_map in He as (y & Hy & He).
      apply in_flat_map. exists y. split; [|exact He]. apply in_app_iff in Hy as [Hy|Hy]; apply in_app_iff; [left | right; right]; exact Hy. }
    destruct Z as [Z|[Z|[Z|[Z|Z]]]]; [left; exact Z | right; left; exact Z | right; right; left; exact Z | |].
    * do 3 right; left. apply Exists_exists in Z as (e & He & Hz). apply Exists_exists. exists e. split; [exact (SI e He) | exact Hz].
    * do 4 right. apply Exists_exists in Z as (r & Hr & Hz). apply Exists_exists. exists r. split; [|exact Hz].
      rewrite !in_app_iff in Hr |- *. destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr | right; left; exact (SI r Hr) | right; right; exact Hr].
  + intros C. apply NC. destruct C as [(y & Hy & Hsy & Hr)|(fp & Hcp & Hr)].
    * left. exists y. split; [|split; [exact Hsy | exact Hr]]. rewrite E1. rewrite E in Hy.
      apply in_app_iff in Hy as [Hy|[<-|Hy]]; [apply in_app_iff; left; exact Hy | rewrite Hst in Hsy; discriminate | apply in_app_iff; right; exact Hy].
    * right. exists fp. split; [unfold frames in *; rewrite Rfs; exact Hcp | exact Hr].
Qed.

Theorem rc_model_cf : forall X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
apost (recycle_chunk k X) (fun r => DRq_cf B NMAXD (snd r) ks zs).
Proof.
intros X k ks zs D tr r Hp0. exact (proj1 (rc_model_full_cf X k ks zs D tr r Hp0)).
Qed.

Theorem rc_model_puser_cf : forall ly X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
apost (recycle_chunk k X) (fun r => forall a, YFeuC.puser ly X a -> YFeuC.puser ly (snd r) a).
Proof.
intros ly X k ks zs D tr r Hp0. exact (proj1 (proj2 (rc_model_full_cf X k ks zs D tr r Hp0)) ly).
Qed.

Theorem rc_model_aox_cf : forall ly X k ks zs, DRq_cf B NMAXD X (k :: ks) zs ->
apost (recycle_chunk k X) (fun r => forall a, aowned B ly (snd r) a -> aowned B ly X a).
Proof.
intros ly X k ks zs D tr r Hp0. exact (proj2 (proj2 (rc_model_full_cf X k ks zs D tr r Hp0)) ly).
Qed.

Variable RMAXD : Z.
Hypothesis HRMAX : kFreeArrayOffset <= RMAXD.


(* B1's rc_prim_step_t at ARXr := ARXr_cf B IOK Hp, AOX := aowned B, DRq := DRq_cf B NMAXD, cd_model := cd_model_cf. *)
Theorem rc_prim_step_cf : forall inst ly X k ks zs cbp W regs mem md off mem' md',
rcc_pre_x B (ARXr_cf B IOK Hp) inst ly X k cbp W regs mem md -> DRq_cf B NMAXD X (k :: ks) zs -> ck_beg k = PPrim off ->
(forall a, 0 <= a < 2 ^ 64 -> ~ AFf3.D B ly k (spZ regs) a -> aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
(forall a, aview im_segs (w_H W) mem a <> None -> aview im_segs (w_H W) mem' a <> None) ->
(forall a, AFf3.DH B ly k a -> aview im_segs (w_H W) mem a <> None -> aview im_segs (w_H W) mem' a = Some shHeapLeftRz) ->
(forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
Forall (cell_holds B ly (aview im_segs (w_H W) mem')) (as_const B ly) ->
m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARXr_cf B IOK Hp inst ly (AFf3.X1 X k) W mem' md' /\
cd_model_cf RMAXD (AFf3.X1 X k) (prim_class off) off /\
(forall a, 0 <= a < 2 ^ 64 -> AFf3.D B ly k (spZ regs) a -> aowned B ly X a \/ AFf3.DS (spZ regs) a) /\
(forall a, aowned B ly (AFf3.X1 X k) a -> aowned B ly X a) /\
(forall a, YFeuC.puser ly X a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k) -> ~ AFf3.D B ly k (spZ regs) a).
Proof.
intros inst ly X k ks zs cbp W regs mem md off mem' md' PRE DR Hb AG VIS NEW HK CONST Ev El Ee.
destruct PRE as ((HI & HA & HX) & Hci & _ & _ & _ & Hlo & Hcb1 & Hcb2 & _).
destruct DR as ((WF & IT & ND & _) & _).
change (flat_map b_items []) with (@nil chunk) in IT, ND. rewrite app_nil_r in IT, ND.
apply Forall_cons_iff in IT as [[Hk Hst] _].
cbn [app map] in ND. apply NoDup_cons_iff in ND as [Hnk _].
assert (Hni : ~ In (ck_beg k) (map ck_beg (q_items X))).
{ intros Hin. apply Hnk. rewrite map_app. apply in_app_iff. right. exact Hin. }
assert (Hsp : ly_stk_lo ly + AFeu.KSTACK <= spZ regs <= ly_stk_hi ly) by (unfold AFeu.KSTACK, KSTACK_CF in *; lia).
split; [split; [exact HI | split]|].
- eapply ARcfR_X1; eassumption.
- intros e He. rewrite Ev. exact (HX e He).
- split; [eapply cdm; eassumption|].
  split; [intros a _ HD; eapply D_owned; eassumption|].
  split; [eapply aowned_X1; eassumption|].
  eapply puser_notD; eassumption.
Qed.

(* H4's ROOM field (rc_prim_room_t, commit 6fdbdd538bcf, proofs/cgif/cgif_file_fuzzer/lib/DMrcReads.v:99-103), its
   text at ARXr := ARXr_cf B IOK Hp and DRq := DRq_cf B NMAXD: at Recycle's call for a primary chunk, the growth arm's
   byte budget.  The cut's room of record is AbudgetRestate's YGcfRoomCf.room_rec_cf_of_cut, with the pending
   allowance qloose_cut from DRq_cf's own conjuncts (YGcfRoomCf.qloose_cut_of_pending) and the unit's admission
   cf_hull_ok from DRq_cf's ninth conjunct; YGcfCker.room_wA_parts_R
   turns it into the budget for n := 2 * kUserMapSize + 32768 <= CF_HEAD.  The growth guard is not needed. *)
Theorem rc_prim_room_cf : forall inst ly X k ks zs cbp W regs mem md off,
rcc_pre_x B (ARXr_cf B IOK Hp) inst ly X k cbp W regs mem md -> DRq_cf B NMAXD X (k :: ks) zs -> ck_beg k = PPrim off ->
(rg_mapped_fa (reg X (prim_class off)) < 4 * (fa_len (rg_free (reg X (prim_class off))) + max_cached (prim_class off) / 2) ->
 eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768 <= vm_limit (m_vmmaps md)).
Proof.
intros inst ly X k ks zs cbp W regs mem md off (H & _) D _ _.
destruct H as (_ & (M & L & (HA & _) & _) & _).
destruct D as (_ & _ & HU & HT & HG & _ & HN & _ & HHO).
pose proof (YGcfRoomCf.qloose_cut_of_pending X (k :: ks) HU HT HG HN) as QL.
pose proof (amr_wfr _ _ _ _ _ M) as WF.
pose proof (YGcfRoomCf.room_rec_cf_of_cut _ ly X md WF QL HHO) as R.
replace (eager_used md + A_bytes (w_A W) + 2 * kUserMapSize + 32768)
  with (eager_used md + A_bytes (w_A W) + (2 * kUserMapSize + 32768)) by lia.
apply (YGcfCker.room_wA_parts_R _ _ ly X md W _ WF L HA R).
apply Z.leb_le. reflexivity.
Qed.
End F.
End U.
