(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the generic cf instance layer, lane F2b: the MEMORY side of F12, the
   step transport of the drain's cut relation across SizeClassAllocator64LocalCache::Deallocate's no-growth arm.
   rule 24: no function proved (kind: relation-level facts about the walk's own frame).

   The cf twin of YFez.cd_fin_ARm (YFez.v:769) over ARmcfR.  The memory premise is the walk's own frame, as lane B1
   words F12: [cdwin], the twin of YFgk.WIN (YFgk.v:237-240) - the stack window below the entry sp, the cache's count
   word and new slot, the cache's stats word, and (only when the cache is full) the three region-info words and the
   free-array entries the drain writes; [MEQ] mem' = mem off it, [PRES] every byte of it is present after the call,
   and at_RETK's written values.  This file carries the window's geometry and the per-family facts that every cell,
   entry, flag, depot word, shadow byte and junk range of the relation that the call does NOT write is apart from it
   ([ok], [ok_T] .. [ok_fa]), with [AGok] / [VIS] for the reads; the words it DOES write from at_RETK's values
   ([cm_region_c], [cm_cache_c], [cm_fa], [cm_cache_junk_c]); the record ([cm_ARmcfR]) and the relation's outer
   conjuncts ([cm_ALedger], [cm_ARcfR]); and the top [cd_step_cf]: ARXr_cf at the step's end state, with the owned
   set shrinking ([cm_aowned]).  YGcfInstDrainCd.v is the model half.  The free-side ledger conjunct (abudget_ok_cf's
   first) is carried unchanged (cd_abudget: the step changes no byte count), so it stays the OPEN premise it is at
   the step's start.
   Image-free (ImgBase.AImg only) and event-free (no event-count term, no event regime, no event-keyed budget). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0s YK0i YP0m YP0e YP09 YP0l YP06 YO0d YK08 YP03.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04 YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0k YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf YG0qcf YG0tcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfTok YG03cf YFfh YGcfXs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ImgBaseDG DMspec DMiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfImgRows.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YGcfInstDrainR YGcfInstDrainRL YGcfInstDrainCd YGcfInstDrainX.
From Stdlib Require Import List.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Ltac ceil := let H := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H.

Section U. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {IM : AImg}.
Local Open Scope am_scope.

Lemma pairwise_nth_f : forall {A} (R : A -> A -> Prop) l i j x y, pairwise R l -> (i < j)%nat ->
nth_error l i = Some x -> nth_error l j = Some y -> R x y.
Proof.
intros A R l. induction l as [|h t IH]; intros i j x y HP Hij Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; destruct j as [|j]; try lia.
- cbn in Hi, Hj. injection Hi as <-. exact (proj1 (Forall_forall _ _) HF y (nth_error_In _ _ Hj)).
- cbn in Hi, Hj. exact (IH i j x y HP ltac:(lia) Hi Hj).
Qed.

Lemma cm_combine_snoc {A : Type} : forall (l : list A) (s : nat) x,
combine (seq s (S (length l))) (l ++ [x]) = combine (seq s (length l)) l ++ [((s + length l)%nat, x)].
Proof.
induction l as [|a t IH]; intros s x; [cbn; rewrite Nat.add_0_r; reflexivity|].
cbn [length]. rewrite <- (cons_seq (S (length t)) s), <- (cons_seq (length t) s). cbn [combine app]. rewrite IH, Nat.add_succ_r. reflexivity.
Qed.
Lemma in_combine_seq : forall (l0 : list Z) (s i : nat) vv, In (i, vv) (combine (seq s (length l0)) l0) -> (s <= i)%nat /\ nth_error l0 (i - s) = Some vv.
Proof.
induction l0 as [|y t IH]; intros s i vv H; [destruct H|]. cbn [length combine seq] in H. destruct H as [H|H].
- injection H as <- <-. split; [lia|]. rewrite Nat.sub_diag. reflexivity.
- destruct (IH _ _ _ H) as [H1 H2]. split; [lia|]. replace (i - s)%nat with (Datatypes.S (i - Datatypes.S s)) by lia. cbn [nth_error]. exact H2.
Qed.
Lemma nth_error_combine_seq : forall (l0 : list Z) (s i : nat) vv, nth_error l0 i = Some vv -> In ((s + i)%nat, vv) (combine (seq s (length l0)) l0).
Proof.
induction l0 as [|y t IH]; intros s i vv H; [destruct i; discriminate|]. cbn [length combine seq]. destruct i as [|i].
- cbn in H. injection H as <-. left. f_equal. lia.
- right. replace (s + Datatypes.S i)%nat with (Datatypes.S s + i)%nat by lia. apply IH. exact H.
Qed.

Lemma cm_nth_error_run_elems : forall m lo sz j, (j < m)%nat -> nth_error (run_elems lo sz m) j = Some (lo + Z.of_nat j * sz).
Proof.
induction m as [|m IH]; intros lo sz j Hj; [lia|]. cbn [run_elems]. destruct j as [|j]; cbn [nth_error]; [f_equal; lia|].
rewrite IH by lia. f_equal. lia.
Qed.
Lemma cm_fa_nth_elems : forall sz fl j, runs_ok fl -> 0 <= j -> fa_nth sz fl j = nth_error (fa_elems sz fl) (Z.to_nat j).
Proof.
intros sz fl. induction fl as [|[lo k|o] t IH]; intros j Hr Hj.
- cbn. destruct (Z.to_nat j); reflexivity.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_run.
  destruct (Z.ltb_spec j k).
  + rewrite nth_error_app1 by (rewrite run_elems_length; lia). rewrite cm_nth_error_run_elems by lia. f_equal. rewrite Z2Nat.id by lia. reflexivity.
  + rewrite nth_error_app2 by (rewrite run_elems_length; lia). rewrite run_elems_length. rewrite IH by (assumption || lia). f_equal. lia.
- inversion Hr as [|x y Hk Ht]; subst. cbn [fa_nth]. rewrite fa_elems_cons_one. destruct (Z.eqb_spec j 0) as [->|Hne]; [reflexivity|].
  replace (Z.to_nat j) with (Datatypes.S (Z.to_nat (j - 1))) by lia. cbn [nth_error]. apply IH; [assumption | lia].
Qed.

Lemma cm_nth_skipn {A : Type} : forall n (l : list A) i, nth_error (skipn n l) i = nth_error l (n + i).
Proof. induction n as [|n IH]; intros l i; [reflexivity|]. destruct l as [|y t]; [destruct i; reflexivity|]. cbn. apply IH. Qed.

Section M.
Variable B : asyms.
Variable ly : alayout.
Variable X : astate.
Variables (c off sp0 : Z).
Variables (W : world im_segs) (mem mem' : word -> option byte) (md : Model) (Hp : list Z).
Local Notation rd := (aview im_segs (w_H W) mem).
Local Notation rd' := (aview im_segs (w_H W) mem').
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).

Hypothesis MR : ARcfR im_segs B ly X Hp W mem md.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis Hci : st_cache_inited X = true.
Hypothesis Hpm : pc_max (cache X c) = max_cached c.
Hypothesis Hsp : ly_stk_lo ly + 320 <= sp0 <= ly_stk_hi ly.
(* the no-growth room the walk tests (DMwalkIF.cd_model's free-array clause, YFfh.cache_dealloc_eq_full) *)
Hypothesis Hroom : (Z.of_nat (length (pc_chunks (cache X c))) =? max_cached c) = true ->
4 * (fa_len (rg_free (reg X c)) + max_cached c / 2) <= rg_mapped_fa (reg X c).

Lemma cmM : ARmcfR B ly X Hp rd. Proof. exact (proj1 MR). Qed.
Lemma cmLO : layout_ok ly. Proof. exact (amr_layout _ _ _ _ _ cmM). Qed.
Lemma cmWF : WfR_cf (as_universe B) 0 0 0 X. Proof. exact (amr_wfr _ _ _ _ _ cmM). Qed.
Lemma cmSY : asyms_ok B. Proof. exact (amr_syms _ _ _ _ _ cmM). Qed.
Lemma cmLED : ALedger_cf im_segs ly X md. Proof. exact (proj1 (proj2 MR)). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The window (the twin of YFgk.WIN).                                                                               *)
Definition cmcnt : Z := Z.of_nat (length (pc_chunks (cache X c))).
Definition cmMAX : Z := max_cached c.
Definition cmN : Z := cmMAX / 2.
Definition cmCNTP : Z := if cmcnt =? cmMAX then cmcnt - cmN else cmcnt.
Definition cmPC : Z := T + t_cache + 80 * c.
Definition cmSLOT : Z := cmPC + 16 + 4 * cmCNTP.
Definition cmRG : Z := SB + kRegionInfoOff + 128 * c.
Definition cmFA : Z := fa_base ly c.
Definition cmold : Z := fa_len (rg_free (reg X c)).
Definition cmDST : Z := cmFA + 4 * cmold.
Definition cmfull : bool := cmcnt =? cmMAX.

Definition cmWRG (a : Z) : Prop :=
(cmRG <= a < cmRG + 8) \/ (cmRG + 16 <= a < cmRG + 24) \/ (cmRG + 80 <= a < cmRG + 88).
Definition cmwinF (a : Z) : Prop :=
(cmPC <= a < cmPC + 4) \/ (cmSLOT <= a < cmSLOT + 4) \/ (T + t_cache + 2576 <= a < T + t_cache + 2584).
Definition cmwinR (a : Z) : Prop := cmfull = true /\ (cmWRG a \/ (cmDST <= a < cmDST + 4 * cmN)).
Definition cdwin (a : Z) : Prop := (sp0 - 320 <= a < sp0) \/ cmwinF a \/ cmwinR a.
Definition ok (a : Z) : Prop := 0 <= a < 2 ^ 64 /\ ~ cdwin a.
Definition okr (lo len : Z) : Prop := forall a, lo <= a < lo + len -> ok a.

Hypothesis MEQ : forall x : word, ~ cdwin (bv_unsigned x) -> mem' x = mem x.
Hypothesis PRES : forall a, cdwin a -> apresent (w_H W) mem' a.
(* The image's constant cells at the call's memory.  cgif's transport takes exactly this as a hypothesis
   (YFez.v:92 CONST'), because a const cell may sit anywhere the image puts it, including the thread object the call
   writes; the WALK discharges it from the unit's const table. *)
Hypothesis CONST' : Forall (cell_holds B ly rd') (as_const B ly).
(* The words the call writes, with their values (the twin of YFgk.at_RETK, YFgk.v:401-405): the cache's count, the new
   slot (the object's offset in its region, in 16-byte units), and, when the cache is full, the region's first word,
   its free-array length and the drained half's entries copied from the cache's top slots into the free array. *)
Hypothesis NEW_cnt : val_mem im_segs (mrestrict (w_H W) mem') cmPC 4 (cmCNTP + 1).
Hypothesis NEW_slot : val_mem im_segs (mrestrict (w_H W) mem') cmSLOT 4 ((off - region_off c) / 16).
Hypothesis NEW_rg0 : cmfull = true -> val_mem im_segs (mrestrict (w_H W) mem') cmRG 8 0.
Hypothesis NEW_rg16 : cmfull = true -> val_mem im_segs (mrestrict (w_H W) mem') (cmRG + 16) 8 (cmold + cmN).
Hypothesis NEW_fa : cmfull = true -> forall i v, 0 <= i < cmN ->
  val_mem im_segs (mrestrict (w_H W) mem) (cmPC + 16 + 4 * (cmcnt - cmN) + 4 * i) 4 v ->
  val_mem im_segs (mrestrict (w_H W) mem') (cmDST + 4 * i) 4 v.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The geometry.                                                                                                    *)
Lemma cmSX : forall i j x y, (i < j)%nat -> nth_error (static_extents ly) i = Some x -> nth_error (static_extents ly) j = Some y ->
zdisjoint x y.
Proof. intros i j x y Hij Hi Hj. exact (pairwise_nth_f zdisjoint _ i j x y (lo_disj _ cmLO) Hij Hi Hj). Qed.
Ltac sx i j := let D := fresh "DJ" in pose proof (cmSX i j _ _ ltac:(lia) eq_refl eq_refl) as D; unfold zdisjoint in D; cbn [fst snd] in D.

Lemma cm_class : 32 <= class_size c <= kMaxSize /\ 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6).
assert (CS : 32 <= class_size c) by (apply Z.mod_divide in K2 as [q Hq]; [|lia]; nia).
repeat split; lia.
Qed.

Lemma cm_reg : 0 <= cmold /\ 4 * cmold <= rg_mapped_fa (reg X c) /\ 0 <= rg_mapped_fa (reg X c) <= kFreeArrayMax /\
0 <= cmcnt <= max_cached c.
Proof.
pose proof (wfr_classes _ _ _ _ _ cmWF c ltac:(lia)) as CL.
pose proof (wrc_fa _ _ _ _ _ _ CL) as [F1 F2]. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as F3.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as F4. pose proof (wrc_runs _ _ _ _ _ _ CL) as RU.
pose proof (fa_len_nonneg _ RU) as F0. pose proof (wrc_cache _ _ _ _ _ _ CL) as WC.
rewrite Hci in WC. destruct WC as [C1 C2]. unfold cmold, cmcnt. repeat split; lia.
Qed.

Lemma cm_T : kHighMemBeg <= ly_prim ly /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
4096 <= T /\ in_app T kThreadObjSize /\ ly_prim ly <= SB /\ SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\
kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd /\ region_off c = c * 2 ^ 32.
Proof.
pose proof (lo_high _ cmLO) as IP. unfold in_high in IP. cbn [fst snd] in IP.
pose proof (proj1 (Forall_forall _ _) (lo_app _ cmLO) (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as IT.
cbn [fst snd] in IT. pose proof (lo_top _ cmLO) as (_ & _ & _ & T4 & _ & _ & T7).
pose proof (lo_space_in _ cmLO) as [S1 S2]. pose proof (region_off_eq c ltac:(lia)) as RO.
pose proof IT as IT'. unfold in_app in IT'. repeat split; try exact IT; try exact RO; lia.
Qed.

Lemma cm_PC : T + t_cache + 80 <= cmPC /\ cmPC + 80 <= T + t_cache + 2480 /\ 0 <= cmCNTP /\ cmCNTP + 1 <= max_cached c.
Proof.
pose proof cm_class as (_ & K3 & K4). pose proof cm_reg as (_ & _ & _ & C2).
apply Z.mod_divide in K4 as [q Hq]; [|lia].
assert (EN : cmN = q) by (unfold cmN, cmMAX; rewrite Hq; apply Z_div_mult; lia).
unfold cmPC, cmCNTP, cmcnt, cmMAX in *. rewrite EN.
destruct (Z.eqb_spec (Z.of_nat (length (pc_chunks (cache X c)))) (max_cached c)) as [E|NE];
unfold t_cache; repeat split; lia.
Qed.

Lemma cm_RG : SB + kRegionInfoOff <= cmRG /\ cmRG + 128 <= SB + kRegionInfoOff + 4096.
Proof. unfold cmRG, kRegionInfoOff. lia. Qed.

Lemma cm_DST : cmfull = true -> SB + region_off c + kFreeArrayOffset <= cmDST /\ cmDST + 4 * cmN <= SB + region_off c + 2 ^ 32.
Proof.
intros Hf. pose proof cm_reg as (R0 & R1 & R2 & R3).
unfold cmDST, cmFA, cmN, cmMAX, cmold, fa_base, kFreeArrayOffset, kFreeArrayMax in *. lia.
Qed.

(* Every address of the window is in the thread object, in the primary reserve, or on the stack. *)
Lemma cdwin_cases : forall a, cdwin a ->
(T <= a < T + kThreadObjSize /\ cmwinF a) \/ (ly_prim ly <= a < ly_prim ly + kPrimResvSize /\ cmwinR a) \/
(ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros a [Hs|[Hf|Hr]].
- right; right. lia.
- left. split; [|exact Hf]. pose proof cm_PC as (P1 & P2 & P3 & P4). pose proof cm_class as (_ & K3 & _).
  unfold cmwinF, cmSLOT, cmPC, kThreadObjSize, t_cache in *. lia.
- right; left. split; [|exact Hr]. pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
  pose proof cm_RG as [G1 G2]. destruct Hr as [Hfu Hw].
  pose proof (region_in_prim ly c cmLO ltac:(lia)) as (R1 & R2 & _).
  destruct Hw as [Hw|Hw]; [unfold cmWRG, kRegionInfoOff, kSpaceSize in *; lia|].
  destruct (cm_DST Hfu) as [D1 D2]. unfold region_base in R1, R2. unfold kFreeArrayOffset in *. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The zones that are apart from the window.                                                                        *)
Lemma in_app_64 : forall lo len a, in_app lo len -> lo <= a < lo + len -> 0 <= a < 2 ^ 64.
Proof. intros lo len a [H0 [HL|[H1 H2]]] Ha; ceil; unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia. Qed.

Lemma ok_T : forall a, T <= a < T + kThreadObjSize -> ~ cmwinF a -> ok a.
Proof.
intros a Ha NF. pose proof cm_T as (H1 & H2 & H3 & H4 & _).
split; [exact (in_app_64 _ _ a H4 Ha)|]. intros HD.
destruct (cdwin_cases a HD) as [[_ Y]|[[Y _]|Y]]; [exact (NF Y)|sx 0%nat 2%nat; unfold kThreadObjSize in *; lia|sx 2%nat 8%nat; unfold kThreadObjSize in *; lia].
Qed.

Lemma ok_prim : forall a, ly_prim ly <= a < ly_prim ly + kPrimResvSize -> ~ cmwinR a -> ok a.
Proof.
intros a Ha NR. pose proof cm_T as (H1 & H2 & _).
split; [exact (in_app_64 (ly_prim ly) kPrimResvSize a (in_high_app (ly_prim ly) kPrimResvSize (lo_high _ cmLO)) Ha)|]. intros HD.
destruct (cdwin_cases a HD) as [[Y _]|[[_ Y]|Y]]; [sx 0%nat 2%nat; unfold kThreadObjSize in *; lia | exact (NR Y) | sx 0%nat 8%nat; lia].
Qed.

Lemma ok_static : forall j e a, (3 <= j <= 7)%nat \/ j = 1%nat -> nth_error (static_extents ly) j = Some e ->
fst e <= a < fst e + snd e -> ok a.
Proof.
intros j e a Hj He Ha.
pose proof (proj1 (Forall_forall _ _) (lo_app _ cmLO) e ltac:(unfold static_extents in He; rewrite nth_error_app1 in He by (cbn; lia);
  eapply nth_error_In; exact He)) as HE. cbn [fst snd] in HE.
split; [exact (in_app_64 _ _ a HE Ha)|]. intros HD.
destruct (cdwin_cases a HD) as [[Y _]|[[Y _]|Y]].
- assert (j <> 2)%nat by lia. destruct (Nat.lt_ge_cases j 2).
  + pose proof (cmSX j 2%nat _ _ ltac:(lia) He eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kThreadObjSize in *. lia.
  + pose proof (cmSX 2%nat j _ _ ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. unfold kThreadObjSize in *. lia.
- pose proof (cmSX 0%nat j _ _ ltac:(lia) eq_refl He) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
- pose proof (cmSX j 8%nat _ _ ltac:(lia) He eq_refl) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

Lemma ok_img : forall a, in_zr a (ly_img ly) -> ok a.
Proof.
intros a Ha. pose proof (lo_img _ cmLO) as (I1 & I2 & I3 & _). unfold in_zr in Ha. rewrite I1 in Ha.
pose proof cm_T as (H1 & H2 & H3 & H4 & _). ceil.
split; [unfold kImgLo, kImgEnd in *; lia|]. intros HD.
destruct (cdwin_cases a HD) as [[Y _]|[[Y _]|Y]].
- sx 2%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
- sx 0%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
- sx 8%nat 9%nat. unfold in_zr, kImgLo, kImgEnd in *. lia.
Qed.

Lemma ok_shadow : forall a, SHADOW_OFF <= a < kHighMemBeg -> ok a.
Proof.
intros a Ha. pose proof cm_T as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
destruct H4 as [HT0 [HTL|[HTH HTC]]]; ceil;
split; try (unfold SHADOW_OFF, kHighMemBeg in *; lia); intros HD;
destruct (cdwin_cases a HD) as [[Y _]|[[Y _]|Y]];
unfold kThreadObjSize, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma ok_lowband : forall a, kLowShadowBeg <= a < kHighMemBeg -> ok a.
Proof.
intros a Ha. pose proof cm_T as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
destruct H4 as [HT0 [HTL|[HTH HTC]]]; ceil;
split; try (unfold kLowShadowBeg, kHighMemBeg in *; lia); intros HD;
destruct (cdwin_cases a HD) as [[Y _]|[[Y _]|Y]];
unfold kThreadObjSize, kLowShadowBeg, kHighMemBeg in *; lia.
Qed.

Lemma ok_sec : forall e a, In e (sec_extents ly X) -> fst e <= a < fst e + snd e -> ok a.
Proof.
intros e a He Ha.
assert (D : forall j y, nth_error (static_extents ly) j = Some y -> zdisjoint e y).
{ intros j y Hj. eapply (pairwise_In zdisjoint _ e y (sec_extents ly X) (static_extents ly) eq_refl (proj2 (amr_placed _ _ _ _ _ cmM)) He).
  eapply nth_error_In. exact Hj. }
pose proof (proj1 (Forall_forall _ _) (proj1 (amr_placed _ _ _ _ _ cmM)) e He) as (_ & IA & _).
split; [exact (in_app_64 _ _ a IA Ha)|]. intros HD.
destruct (cdwin_cases a HD) as [[Y _]|[[Y _]|Y]].
- pose proof (D 2%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. unfold kThreadObjSize in *. lia.
- pose proof (D 0%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
- pose proof (D 8%nat _ eq_refl) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ. lia.
Qed.

(* The region-info words and the free-array entries of OTHER classes, and of [c] outside what the call writes. *)
Lemma ok_rinfo : forall c' a, 1 <= c' <= 31 -> SB + kRegionInfoOff + 128 * c' <= a < SB + kRegionInfoOff + 128 * c' + 128 ->
(c' = c -> cmfull = true -> ~ cmWRG a) -> ok a.
Proof.
intros c' a Hc' Ha NW. pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
apply ok_prim; [unfold kRegionInfoOff, kSpaceSize in *; lia|]. intros [Hf [Hw|Hw]].
- destruct (Z.eq_dec c' c) as [->|NE]; [exact (NW eq_refl Hf Hw)|].
  unfold cmWRG, cmRG in Hw. destruct (Z.lt_trichotomy c' c) as [L|[->|L]]; [lia | lia | lia].
- destruct (cm_DST Hf) as [D1 D2]. pose proof (region_in_prim ly c cmLO ltac:(lia)) as (R1 & R2 & _).
  unfold region_base in R1, R2. pose proof (region_off_eq c ltac:(lia)) as RO.
  unfold kRegionInfoOff, kFreeArrayOffset, kSpaceSize in *. rewrite RO in *. nia.
Qed.

Lemma ok_fa : forall c' i, 1 <= c' <= 31 -> 0 <= i -> 4 * i + 4 <= kFreeArrayMax -> (c' = c -> cmfull = true -> i < cmold) ->
okr (fa_base ly c' + 4 * i) 4.
Proof.
intros c' i Hc' Hi Hi2 LOW a Ha. pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
pose proof (region_off_eq c' ltac:(lia)) as RO'. pose proof (region_off_eq c ltac:(lia)) as RO.
unfold fa_base in Ha. pose proof (region_in_prim ly c' cmLO ltac:(lia)) as (R1 & R2 & _). unfold region_base in R1, R2.
apply ok_prim; [unfold kFreeArrayOffset, kFreeArrayMax in *; lia|]. intros [Hf [Hw|Hw]].
- unfold cmWRG, cmRG in Hw. unfold kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax, kSpaceSize in *.
  rewrite RO' in Ha. nia.
- destruct (Z.eq_dec c' c) as [->|NE].
  + pose proof (LOW eq_refl Hf). unfold cmDST, cmFA, fa_base in Hw. lia.
  + destruct (cm_DST Hf) as [D1 D2]. rewrite RO' in Ha. rewrite RO in D1, D2.
    unfold kFreeArrayOffset, kFreeArrayMax in *. destruct (Z.lt_trichotomy c' c) as [L|[->|L]]; [nia | lia | nia].
Qed.

Lemma ok_chunk : forall k a, In k (st_chunks X) -> ck_base B ly k <= a < ck_base B ly k + ck_extent k -> ok a.
Proof.
intros k a Hk Ha. destruct (RL.extent_zone_cf B ly X Hp _ k cmM Hk) as [[P1 P2]|(m & len & Hin & E1 & E2)].
- pose proof (RL.chunk_facts_cf B ly X Hp _ k cmM Hk) as CF. unfold RL.cfacts_cf in CF.
  destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k) as [|o|r o|cc pp] eqn:Eb; try solve [destruct GG].
  + cbv zeta in GG. destruct GG as (Gc & _ & _ & Gext & Gbase & Gx & Gxm & Gxs & Gal).
    set (c2 := prim_class o) in *.
    apply ok_prim; [lia|]. intros [Hf [Hw|Hw]].
    * unfold cmWRG, cmRG in Hw. pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
      pose proof (region_off_eq c2 ltac:(lia)) as RO2. unfold region_base in Gbase. rewrite RO2 in Gbase.
      unfold kRegionInfoOff, kSpaceSize, kFreeArrayOffset in *. nia.
    * destruct (cm_DST Hf) as [D1 D2]. pose proof (region_off_eq c2 ltac:(lia)) as RO2.
      pose proof (region_off_eq c ltac:(lia)) as RO. unfold region_base in Gbase. rewrite RO2 in Gbase.
      rewrite RO in D1, D2. unfold kFreeArrayOffset, kFreeArrayMax in *.
      destruct (Z.lt_trichotomy c2 c) as [L|[E|L]]; [nia | rewrite E in *; lia | nia].
  + destruct GG as (-> & _ & Gbase & Gext & Gin & _). exact (ok_sec _ a Gin ltac:(unfold kPage in *; cbn [fst snd]; lia)).
- exact (ok_sec (m, len) a Hin ltac:(cbn [fst snd]; unfold kPage in *; lia)).
Qed.

Lemma ok_batch : forall b a, In b (all_batches X) -> ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ok a.
Proof.
intros b a Hb Ha.
pose proof (wfr_classes _ _ _ _ _ cmWF kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
set (xb := b_self b - region_off kBatchClass).
assert (INB : In xb (batch_offs X kBatchClass)) by (rewrite batch_offs_24; apply in_map_iff; exists b; auto).
pose proof (proj1 (Forall_forall _ _) (wrc_elems _ _ _ _ _ _ CL) xb ltac:(rewrite !in_app_iff; tauto)) as [Z1 Z2].
pose proof (wrc_alloc _ _ _ _ _ _ CL) as AL. pose proof (wrc_alloc_al _ _ _ _ _ _ CL) as AA.
pose proof (wrc_mapped_bound _ _ _ _ _ _ CL) as MB.
assert (CS : class_size kBatchClass = 8192) by reflexivity. rewrite CS in Z2, AA.
assert (XB : xb + 8192 <= rg_alloc_user (reg X kBatchClass))
  by (apply Z.mod_divide in Z2 as [q Hq]; [|lia]; apply Z.mod_divide in AA as [q' Hq']; [|lia]; nia).
pose proof (region_in_prim ly kBatchClass cmLO ltac:(unfold kBatchClass; lia)) as (R1 & R2 & _).
pose proof (region_off_eq kBatchClass ltac:(unfold kBatchClass; lia)) as RO24.
pose proof (region_off_eq c ltac:(lia)) as RO.
pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
unfold region_base in R1, R2. unfold kBatchBytes in *.
apply ok_prim; [unfold xb in *; rewrite RO24 in *; unfold kFreeArrayOffset, kBatchClass in *; lia|]. intros [Hf [Hw|Hw]].
- unfold cmWRG, cmRG in Hw. unfold xb in *. rewrite RO24 in *. unfold kRegionInfoOff, kSpaceSize, kFreeArrayOffset, kBatchClass in *. lia.
- destruct (cm_DST Hf) as [D1 D2]. rewrite RO in D1, D2. unfold xb in *. rewrite RO24 in *.
  unfold kFreeArrayOffset, kFreeArrayMax, kBatchClass in *.
  destruct (Z.lt_trichotomy 24 c) as [L|[E|L]]; [nia | lia | nia].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The reads.                                                                                                       *)
Lemma AGok : forall a, ok a -> rd' a = rd a.
Proof.
intros a [H1 H2]. unfold aview, mbyte, mrestrict. rewrite (MEQ (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by exact H1. exact H2.
Qed.

Lemma VIS : forall a, rd a <> None -> rd' a <> None.
Proof.
intros a Hv. unfold aview, mbyte, mrestrict in Hv |- *.
assert (EX : Z_to_bv 64 (bv_unsigned (Z_to_bv 64 a)) = Z_to_bv 64 a) by apply Z_to_bv_bv_unsigned.
assert (DEC : cdwin (bv_unsigned (Z_to_bv 64 a)) \/ ~ cdwin (bv_unsigned (Z_to_bv 64 a)))
  by (unfold cdwin, cmwinF, cmwinR, cmWRG; destruct cmfull; lia).
destruct DEC as [Hw|Hw].
- destruct (PRES _ Hw) as [Hh [bb Hb]]. rewrite EX in Hh, Hb. rewrite Hh, Hb. discriminate.
- rewrite (MEQ (Z_to_bv 64 a) Hw). exact Hv.
Qed.

Lemma cell_xfer : forall ce, cell_holds B ly rd ce ->
(forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) -> cell_holds B ly rd' ce.
Proof. intros ce Hce Hok. eapply (cell_holds_agree B ly rd rd' ce Hce). intros j Hj. apply AGok, Hok, Hj. Qed.

Lemma cells_xfer : forall L lo len, okr lo len -> Forall (fun ce => lo <= aeval B ly (c_at ce) /\ aeval B ly (c_at ce) + Z.max 1 (Z.of_nat (c_w ce)) <= lo + len) L ->
Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L lo len OK IN OLD. apply Forall_forall. intros ce Hce. apply cell_xfer; [exact (proj1 (Forall_forall _ _) OLD ce Hce)|].
intros j Hj. destruct (proj1 (Forall_forall _ _) IN ce Hce) as [I1 I2]. apply OK. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The families the call does not write.  [cdS] is YGcfInstDrainCd's state; its cells differ from X's only in class
   [c]'s region and cache words, so every other family is X's, and every byte of it is off the window.             *)
Lemma cmOLD : forall ce, In ce (acells_cf B ly X) -> cell_holds B ly rd ce.
Proof. intros ce Hce. exact (proj1 (Forall_forall _ _) (amr_cells _ _ _ _ _ cmM) ce Hce). Qed.
Lemma cmOWN : forall ce, In ce (acells_cf B ly X) -> cell_bytes_owned B ly X ce.
Proof. intros ce Hce. exact (proj1 (Forall_forall _ _) (RL.acells_owned_cf B ly X Hp _ cmM) ce Hce). Qed.

Ltac fcons := apply Forall_cons; [cbn; lia|].

Lemma cm_region_other : forall c', 1 <= c' <= 31 -> c' <> c -> Forall (cell_holds B ly rd) (region_cells_cf X c') ->
Forall (cell_holds B ly rd') (region_cells_cf X c').
Proof.
intros c' Hc' Hne O. pose proof cm_T as (_ & _ & _ & _ & S1 & S2 & _).
apply (cells_xfer _ (SB + kRegionInfoOff + 128 * c') 128); [|  |exact O].
- intros a Ha. apply (ok_rinfo c'); [lia | lia | intros -> _; exfalso; exact (Hne eq_refl)].
- unfold region_cells_cf, region_cells. cbv zeta. cbn [removelast].
  repeat (apply Forall_cons; [cbn [c_at c_w z8 z1 c8 c1 aeval aoff]; cbn; lia|]). apply Forall_nil.
Qed.

Lemma cm_cache_other : forall c', 1 <= c' <= 31 -> c' <> c -> Forall (cell_holds B ly rd) (cache_cells X c') ->
Forall (cell_holds B ly rd') (cache_cells X c').
Proof.
intros c' Hc' Hne O. pose proof cm_PC as (P1 & P2 & P3 & P4). pose proof cm_class as (_ & K3 & _).
apply (cells_xfer _ (T + t_cache + 80 * c') 80); [| |exact O].
- intros a Ha. apply ok_T; [unfold t_cache, kThreadObjSize in *; lia|].
  unfold cmwinF, cmSLOT, cmPC, t_cache in *. intros [Y|[Y|Y]]; [nia | nia | lia].
- pose proof (wrc_cache _ _ _ _ _ _ (wfr_classes _ _ _ _ _ cmWF c' ltac:(lia))) as WC. rewrite Hci in WC. destruct WC as [_ PL].
  pose proof (class_ok c' ltac:(lia)) as (_ & _ & _ & K4' & _).
  unfold cache_cells, t_cache. rewrite Hci. repeat fcons.
  apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv). cbn [fst snd c_at c_w z4 c4 aeval aoff].
  apply in_combine_l in Hiv. apply in_seq in Hiv. cbn. lia.
Qed.

Lemma cm_chunks : Forall (cell_holds B ly rd') (flat_map chunk_cells (st_chunks X)).
Proof.
apply Forall_flat_map'. intros k Hk.
pose proof (RL.chunk_facts_cf B ly X Hp _ k cmM Hk) as CF. unfold RL.cfacts_cf in CF.
destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
assert (EA : forall d, aeval B ly (aoff (sptr_exp (ck_beg k)) d) = ck_base B ly k + d)
  by (intros d; unfold ck_base, sptr_addr; destruct (ck_beg k) as [|o|r o|cc pp]; try solve [destruct GG]; cbn; lia).
assert (EA2 : forall d d', aeval B ly (aoff (aoff (sptr_exp (ck_beg k)) d) d') = ck_base B ly k + d + d')
  by (intros d d'; unfold ck_base, sptr_addr; destruct (ck_beg k) as [|o|r o|cc pp]; try solve [destruct GG]; cbn; lia).
assert (EA0 : aeval B ly (sptr_exp (ck_beg k)) = ck_base B ly k) by reflexivity.
pose proof (req_size_bounds (ck_req k) ltac:(lia)) as (_ & Q1 & _).
apply (cells_xfer _ (ck_base B ly k) (ck_rz k)).
- intros a Ha. exact (ok_chunk k a Hk ltac:(lia)).
- unfold chunk_cells, kChunkHeaderSize. apply Forall_app. split.
  + repeat (apply Forall_cons; [cbn [c_at c_w z1 z2 z4 c1 c2 c4]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
  + destruct (Z.eqb_spec (ck_rz k) 16); [apply Forall_nil|].
    assert (32 <= ck_rz k) by (apply Z.mod_divide in G6 as [q Hq]; [|lia]; lia).
    repeat (apply Forall_cons; [cbn [c_at c_w z8 c8]; rewrite ?EA2, ?EA, ?EA0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil.
- apply Forall_forall. intros ce Hce. apply cmOLD. unfold acells_cf. rewrite !in_app_iff.
  right; right; left. apply in_flat_map. exists k. split; [exact Hk | exact Hce].
Qed.

Lemma cm_img_area : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> in_zr a (ly_img ly).
Proof.
intros r a Hr Ha. pose proof (proj1 (Forall_forall _ _) (aso_cover _ cmSY) r Hr) as E.
apply Exists_exists in E as (r' & Hr' & [Z1 Z2]).
pose proof (proj1 (Forall_forall _ _) (amr_static_img _ _ _ _ _ cmM) r' ltac:(apply in_app_iff; left; exact Hr')) as [I1 I2].
unfold in_zr. lia.
Qed.

Lemma cm_inst_ok : forall a, as_inst B <= a < as_inst B + 3632 -> ok a.
Proof.
intros a Ha. apply ok_img. apply (cm_img_area (as_inst B, 3632)); [cbn; tauto | cbn [fst snd]; lia].
Qed.

Lemma cells_ok_xfer : forall L, Forall (fun ce => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) L ->
Forall (cell_holds B ly rd) L -> Forall (cell_holds B ly rd') L.
Proof.
intros L OK O. apply Forall_forall. intros ce Hce. apply cell_xfer;
[exact (proj1 (Forall_forall _ _) O ce Hce) | exact (proj1 (Forall_forall _ _) OK ce Hce)].
Qed.

Lemma cm_area_ok : forall r a, In r (asyms_areas B) -> fst r <= a < fst r + snd r -> ok a.
Proof. intros r a Hr Ha. exact (ok_img a (cm_img_area r a Hr Ha)). Qed.

Lemma cm_sec : Forall (cell_holds B ly rd) (sec_cells X) -> Forall (cell_holds B ly rd') (sec_cells X).
Proof.
intros O. pose proof (wfr_secondary _ _ _ _ _ cmWF) as XS. destruct XS as [Snd Sac Sal Sres Sral].
apply cells_ok_xfer; [|exact O]. unfold sec_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply cm_inst_ok; unfold o_sec_reserved; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *; apply cm_inst_ok; unfold o_sec_n; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cm_inst_ok; unfold o_sec_mutex; lia|].
apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i r] & <- & Hir). apply in_combine_l in Hir. apply in_seq in Hir.
  intros j Hj. cbn [c_at c_w aeval fst snd c8] in *.
  apply (ok_static 1%nat (ly_Q ly, kPtrArrayResv)); [right; reflexivity | reflexivity |
    cbn [fst snd]; unfold kPtrArrayResv, kPtrArrayEntriesPerCommit in *; lia].
- apply Forall_forall. intros ce Hce. apply in_flat_map in Hce as (k0 & Hk0 & Hce).
  pose proof (RL.chunk_facts_cf B ly X Hp _ k0 cmM Hk0) as CF. unfold RL.cfacts_cf in CF.
  destruct CF as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & GG).
  destruct (ck_beg k0) as [|o|r o|cc pp] eqn:Eb; try solve [destruct Hce].
  destruct GG as (-> & _ & Gbase & Gext & Gin & _).
  assert (SM : 4096 + 17 <= sec_map_size (ck_req k0))
    by (pose proof (req_size_bounds (ck_req k0) ltac:(lia)) as (_ & Q1 & _); unfold kPage in *; lia).
  destruct Hce as [<-|[<-|[<-|[<-|[]]]]]; intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
    apply (ok_sec _ _ Gin); cbn [fst snd]; lia.
Qed.

Lemma cm_batch_cells_ok : forall l, incl l (all_batches X) ->
Forall (fun ce => forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> ok (aeval B ly (c_at ce) + j)) (batch_cells l).
Proof.
intros l. induction l as [|b t IH]; intros Hincl; [apply Forall_nil|]. cbn [batch_cells].
pose proof (wq_batches _ (wfr_quarantine _ _ _ _ _ cmWF)) as BL.
pose proof (proj1 (Forall_forall _ _) BL b (Hincl b (or_introl eq_refl))) as [L1 L2]. unfold kBatchSlots in L2.
assert (OKB : forall a, ly_space ly + b_self b <= a < ly_space ly + b_self b + kBatchBytes -> ok a)
  by (intros a Ha; exact (ok_batch b a (Hincl b (or_introl eq_refl)) Ha)).
unfold kBatchBytes in OKB.
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w c8 z8 batch_exp aeval aoff] in *; apply OKB; lia|].
apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i k] & <- & Hik). apply in_combine_l in Hik. apply in_seq in Hik.
  intros j Hj. cbn [fst snd c_at c_w c8 batch_exp aeval aoff] in *. apply OKB. lia.
- apply IH. intros x Hx. apply Hincl. right. exact Hx.
Qed.

Lemma cm_quar : Forall (cell_holds B ly rd) (quar_cells X) -> Forall (cell_holds B ly rd') (quar_cells X).
Proof.
intros O. pose proof cm_PC as (P1 & P2 & P3 & P4). pose proof cm_class as (_ & K3 & _).
assert (OKT : forall a, T + t_qc <= a < T + t_qc + 32 -> ok a).
{ intros a Ha. apply ok_T; [unfold t_qc, kThreadObjSize in *; lia|].
  unfold cmwinF, cmSLOT, cmPC, t_qc, t_cache in *. intros [Y|[Y|Y]]; lia. }
apply cells_ok_xfer; [|exact O]. unfold quar_cells, qc_cells.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cm_inst_ok; unfold o_q_cmutex, o_quar; lia|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *; apply cm_inst_ok; unfold o_q_rmutex, o_quar; lia|].
apply Forall_app. split.
- do 4 (apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8 aoff] in *; apply OKT; unfold t_qc in *; lia|]).
  apply cm_batch_cells_ok. intros b Hb. unfold all_batches. apply in_app_iff. left. exact Hb.
- do 4 (apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8 aoff] in *;
    apply cm_inst_ok; unfold o_q_size, o_quar; lia|]).
  apply cm_batch_cells_ok. intros b Hb. unfold all_batches. apply in_app_iff. right. exact Hb.
Qed.

Lemma cm_fs : Forall (cell_holds B ly rd) (fs_cells X) -> Forall (cell_holds B ly rd') (fs_cells X).
Proof.
intros O. apply (cells_xfer _ (ly_F ly) kFakeFramesOff); [| |exact O].
- intros a Ha. apply (ok_static 3%nat (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |
    cbn [fst snd]; unfold kFakeFramesOff, kFakeStackSize in *; lia].
- unfold fs_cells, kFakeFramesOff. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia|].
  apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i h] & <- & Hih). apply in_combine_l in Hih. apply in_seq in Hih. cbn. lia.
Qed.

Lemma cm_depot : Forall (cell_holds B ly rd) (depot_cells ly X) -> Forall (cell_holds B ly rd') (depot_cells ly X).
Proof.
intros O. apply cells_ok_xfer; [|exact O]. unfold depot_cells, d_nuniq, d_map1, s_total, s_block0.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c4 z4] in *;
  apply (cm_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cm_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cm_area_ok (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cm_area_ok (as_store B, 32)); [cbn; tauto | cbn [fst snd]; lia]|]. apply Forall_nil.
Qed.

Lemma cm_ialloc : Forall (cell_holds B ly rd) (ialloc_cells B X) -> Forall (cell_holds B ly rd') (ialloc_cells B X).
Proof.
intros O. pose proof (aso_ialloc _ cmSY) as [I1 I2].
apply cells_ok_xfer; [|exact O]. unfold ialloc_cells. cbv zeta.
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (cm_area_ok (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c1 z1] in *;
  apply (cm_area_ok (as_ialloc_flag B, 2)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cm_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|].
apply Forall_cons; [intros j Hj; cbn [c_at c_w aeval c8 z8] in *;
  apply (cm_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | cbn [fst snd]; lia]|]. apply Forall_nil.
Qed.

Lemma cm_thread : Forall (cell_holds B ly rd) thread_cells -> Forall (cell_holds B ly rd') thread_cells.
Proof.
intros O. pose proof cm_PC as (P1 & P2 & P3 & P4). pose proof cm_class as (_ & K3 & _).
apply cells_ok_xfer; [|exact O]. unfold thread_cells. apply Forall_cons; [|apply Forall_nil].
intros j Hj. cbn [c_at c_w aeval c1 z1] in *. apply ok_T; [unfold t_unwinding, kThreadObjSize in *; lia|].
unfold cmwinF, cmSLOT, cmPC, t_unwinding, t_cache in *. intros [Y|[Y|Y]]; lia.
Qed.

Lemma cm_const : Forall (cell_holds B ly rd') (as_const B ly).
Proof. exact CONST'. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The words the call writes.                                                                                      *)
Lemma cm_unsigned8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hz. Qed.

Lemma cm_val_aview : forall a (w : nat) v k, val_mem im_segs (mrestrict (w_H W) mem') a w v -> (k < w)%nat ->
rd' (a + Z.of_nat k) = Some (le_byte v w k).
Proof.
intros a w v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map].
change (YG0f.le_byte v w k) with (YO0f.le_byte v w k). f_equal. apply cm_unsigned8.
unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

Lemma cmHlen : (Z.to_nat c < length (st_cache X))%nat. Proof. rewrite (wfr_len_cache _ _ _ _ _ cmWF). lia. Qed.
Lemma cmHlenr : (Z.to_nat c < length (st_regions X))%nat. Proof. rewrite (wfr_len_regions _ _ _ _ _ cmWF). lia. Qed.
Lemma cm_fullE : cdfull X c = cmfull. Proof. unfold cdfull, cmfull, cmcnt, cmMAX. rewrite Hpm. reflexivity. Qed.

Lemma cmN_eq : 2 * cmN = max_cached c /\ 1 <= cmN <= 8.
Proof.
pose proof cm_class as (_ & K3 & K4). apply Z.mod_divide in K4 as [q Hq]; [|lia].
unfold cmN, cmMAX. rewrite Hq, Z_div_mult by lia. lia.
Qed.

Lemma cm_kept_len : Z.of_nat (length (cdkept X c)) = cmCNTP.
Proof.
pose proof cmN_eq as [N1 N2]. pose proof cm_reg as (_ & _ & _ & C2).
unfold cdkept, cmCNTP. rewrite cm_fullE. unfold cmfull. unfold kkeep.
destruct (Z.eqb_spec cmcnt cmMAX) as [E|NE]; [|reflexivity].
rewrite length_firstn, Hpm. unfold cmcnt, cmMAX in *. fold cmN. unfold cmN, cmMAX in *. lia.
Qed.

Lemma cm_drained_len : cmfull = true -> length (kdrained c X) = Z.to_nat cmN.
Proof.
intros Hf. pose proof cmN_eq as [N1 N2]. unfold cmfull in Hf. apply Z.eqb_eq in Hf.
unfold kdrained. rewrite length_skipn, Hpm. unfold cmcnt, cmMAX in Hf. unfold cmN, cmMAX in *. lia.
Qed.

Lemma cm_region_c : Forall (cell_holds B ly rd) (region_cells_cf X c) ->
Forall (cell_holds B ly rd') (region_cells_cf (cdS X c off) c).
Proof.
intros OLDR. pose proof cm_RG as [G1 G2].
assert (ER : forall d, aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c)) d) = cmRG + d) by (intros d; unfold cmRG; cbn; lia).
assert (ER0 : aeval B ly (ASp (kRegionInfoOff + 128 * c)) = cmRG) by (unfold cmRG; cbn; lia).
assert (OKX : forall d, 0 <= d < 128 -> ~ (cmfull = true /\ (d < 8 \/ 16 <= d < 24 \/ 80 <= d < 88)) -> ok (cmRG + d)).
{ intros d Hd NW. apply (ok_rinfo c); [lia | unfold cmRG in *; lia |]. intros _ Hf Hw. apply NW.
  split; [exact Hf|]. unfold cmWRG in Hw. lia. }
unfold region_cells_cf, region_cells in OLDR |- *. cbv zeta in OLDR |- *. cbn [removelast] in OLDR |- *.
rewrite (cd_reg_c X c off Hc cmHlen cmHlenr). rewrite cm_fullE.
apply Forall_cons_iff in OLDR as [O0 OLDR]. apply Forall_cons_iff in OLDR as [O8 OLDR].
apply Forall_cons_iff in OLDR as [O16 OLDR]. apply Forall_cons_iff in OLDR as [O24 OLDR].
apply Forall_cons_iff in OLDR as [O32 OLDR]. apply Forall_cons_iff in OLDR as [O40 OLDR].
apply Forall_cons_iff in OLDR as [O48 OLDR]. apply Forall_cons_iff in OLDR as [O56 _].
Ltac rcell O ER ER0 OKX := apply (cell_xfer _ O); intros j Hj; cbn [c_at c_w z8 z1 c8 c1] in Hj |- *; rewrite ?ER, ?ER0;
  match goal with |- ok ?a => replace a with (cmRG + (a - cmRG)) by lia end; apply OKX; [lia | intros [_ Y]; lia].
destruct cmfull eqn:Hf.
- apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z8 c8]. intros kk Hkk. rewrite ER0. rewrite (cm_val_aview cmRG 8 0 kk (NEW_rg0 eq_refl) Hkk). reflexivity. }
  apply Forall_cons. { rcell O8 ER ER0 OKX. }
  apply Forall_cons.
  { cbn [cell_holds c_at c_val c_w z8 c8 rg_free]. intros kk Hkk. rewrite ER.
    rewrite (cm_val_aview (cmRG + 16) 8 (cmold + cmN) kk (NEW_rg16 eq_refl) Hkk). cbn [aeval]. do 2 f_equal.
    pose proof (fa_push_list_spec (class_size c) (rg_free (reg X c)) (kdrained c X)) as (_ & EL & _).
    rewrite EL, (cm_drained_len Hf). pose proof cmN_eq as [_ N2]. unfold cmold. lia. }
  apply Forall_cons. { rcell O24 ER ER0 OKX. }
  apply Forall_cons. { rcell O32 ER ER0 OKX. }
  apply Forall_cons. { rcell O40 ER ER0 OKX. }
  apply Forall_cons. { rcell O48 ER ER0 OKX. }
  apply Forall_cons; [|apply Forall_nil]. { rcell O56 ER ER0 OKX. }
- repeat (apply Forall_cons; [match goal with |- cell_holds _ _ _ ?ce => apply (cell_xfer ce); [assumption|];
    intros j Hj; cbn [c_at c_w z8 z1 c8 c1] in Hj |- *; rewrite ?ER, ?ER0;
    match goal with |- ok ?a => replace a with (cmRG + (a - cmRG)) by lia end; apply OKX; [lia | intros [Hf' _]; discriminate] end|]).
  apply Forall_nil.
Qed.

Lemma cm_cache_c : Forall (cell_holds B ly rd) (cache_cells X c) ->
Forall (cell_holds B ly rd') (cache_cells (cdS X c off) c).
Proof.
intros OLDC. pose proof cm_PC as (P1 & P2 & P3 & P4). pose proof cm_class as (_ & K3 & _). pose proof cm_kept_len as KL.
unfold cache_cells in OLDC |- *. rewrite (cdS_cinit X c off Hci). rewrite Hci in OLDC.
rewrite (cd_cache_c X c off Hc cmHlen cmHlenr). cbn [pc_chunks pc_max].
apply Forall_cons_iff in OLDC as [_ OLDC]. apply Forall_cons_iff in OLDC as [O2 OLDC]. apply Forall_cons_iff in OLDC as [O3 OLDC].
assert (OKC : forall a, cmPC + 4 <= a < cmPC + 16 + 4 * cmCNTP -> ok a).
{ intros a Ha. apply ok_T; [unfold cmPC, t_cache, kThreadObjSize in *; lia|]. unfold cmwinF, cmSLOT, cmPC, t_cache in *. lia. }
apply Forall_cons.
{ cbn [cell_holds c_at c_val c_w z4 c4 aeval]. intros kk Hkk.
  replace (T + (t_cache + 80 * c)) with cmPC by (unfold cmPC; lia).
  rewrite (cm_val_aview cmPC 4 (cmCNTP + 1) kk NEW_cnt Hkk). rewrite length_app. cbn [length]. do 2 f_equal. lia. }
apply Forall_cons. { apply (cell_xfer _ O2). intros j Hj. cbn in Hj |- *. apply OKC. unfold cmPC in *. lia. }
apply Forall_cons. { apply (cell_xfer _ O3). intros j Hj. cbn in Hj |- *. apply OKC. unfold cmPC in *. lia. }
rewrite length_app. cbn [length]. rewrite Nat.add_1_r, cm_combine_snoc, map_app. apply Forall_app. split.
- apply Forall_forall. intros ce Hce. apply in_map_iff in Hce as ([i v] & <- & Hiv).
  assert (Hiv' : In (i, v) (combine (seq 0 (length (pc_chunks (cache X c)))) (pc_chunks (cache X c)))).
  { apply in_combine_seq in Hiv as [_ Hiv]. rewrite Nat.sub_0_r in Hiv. apply (nth_error_combine_seq _ 0 i v).
    unfold cdkept in Hiv. rewrite cm_fullE in Hiv. destruct cmfull eqn:Hf; [|exact Hiv].
    unfold kkeep in Hiv. rewrite nth_error_firstn in Hiv. destruct (Nat.ltb_spec i (length (pc_chunks (cache X c)) - Z.to_nat (pc_max (cache X c) / 2)));
    [exact Hiv | discriminate]. }
  apply in_combine_l in Hiv. apply in_seq in Hiv.
  apply (cell_xfer _ (proj1 (Forall_forall _ _) OLDC _ ltac:(apply in_map_iff; exists (i, v); split; [reflexivity | exact Hiv']))).
  intros j Hj. cbn in Hj |- *. apply OKC. unfold cmPC in *. lia.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd cell_holds c_at c_val c_w z4 c4 aeval aoff]. intros kk Hkk.
  match goal with |- rd' ?a = _ => replace a with (cmSLOT + Z.of_nat kk) by (unfold cmSLOT, cmPC; rewrite ?Nat.add_0_l; lia) end.
  rewrite (cm_val_aview cmSLOT 4 _ kk NEW_slot Hkk). reflexivity.
Qed.

Lemma cm_aview_val : forall a (w : nat) v, (forall k, (k < w)%nat -> rd (a + Z.of_nat k) = Some (le_byte v w k)) ->
val_mem im_segs (mrestrict (w_H W) mem) a w v.
Proof.
intros a w v H k Hk. specialize (H k Hk). unfold aview in H.
destruct (mbyte im_segs (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:E; [|discriminate].
cbn [option_map] in H. injection H as Hb. f_equal. rewrite <- (Z_to_bv_bv_unsigned _ b) at 1. f_equal. exact Hb.
Qed.

Lemma cm_fa : fa_entries_ok ly rd' (cdS X c off).
Proof.
pose proof (amr_fa _ _ _ _ _ cmM) as XF.
intros c' i v Hc' Hi Hv k Hk.
pose proof (wfr_classes _ _ _ _ _ cmWF c' Hc') as CL'.
pose proof (wrc_runs _ _ _ _ _ _ CL') as RU'. pose proof (wrc_fa_len _ _ _ _ _ _ CL') as FL'.
pose proof (wrc_fa _ _ _ _ _ _ CL') as [F1' F2']. pose proof (wrc_fa_bound _ _ _ _ _ _ CL') as FB'.
destruct (Z.eq_dec c' c) as [->|NE].
2:{ rewrite (cd_reg_other X c off Hc cmHlen cmHlenr c' ltac:(lia) NE) in Hi, Hv.
    rewrite AGok; [exact (XF c' i v Hc' Hi Hv k Hk)|].
    apply (ok_fa c' i Hc' ltac:(lia) ltac:(unfold kFreeArrayMax in *; lia) ltac:(intros E; exfalso; exact (NE E))). lia. }
pose proof (wfr_classes _ _ _ _ _ cmWF c Hc') as CL. pose proof (wrc_runs _ _ _ _ _ _ CL) as RU.
pose proof (wrc_fa_len _ _ _ _ _ _ CL) as FL. pose proof (wrc_fa_bound _ _ _ _ _ _ CL) as FB.
pose proof cm_reg as (R0 & R1 & R2 & R3). pose proof cmN_eq as [N1 N2].
rewrite (cd_reg_c X c off Hc cmHlen cmHlenr), cm_fullE in Hi, Hv.
assert (Hfd : cmfull = true \/ cmfull = false) by (destruct cmfull; auto).
destruct Hfd as [Hf|Hf]; rewrite Hf in Hi, Hv.
2:{ rewrite AGok; [exact (XF c i v Hc' Hi Hv k Hk)|].
    apply (ok_fa c i Hc' ltac:(lia) ltac:(unfold kFreeArrayMax in *; lia) ltac:(intros _ HF; rewrite HF in Hf; discriminate Hf)). lia. }
cbn [rg_free] in Hi, Hv.
pose proof (fa_push_list_spec (class_size c) (rg_free (reg X c)) (kdrained c X)) as (PE1 & PE2 & PE3).
rewrite PE2, (cm_drained_len Hf) in Hi. rewrite PE2, (cm_drained_len Hf) in Hv. rewrite Z2Nat.id in Hi, Hv by lia.
fold cmold in Hi, Hv.
rewrite (cm_fa_nth_elems _ _ (cmold + cmN - 1 - i) (PE3 RU) ltac:(lia)), PE1 in Hv.
pose proof (cm_drained_len Hf) as DL.
destruct (Z_lt_le_dec i cmold) as [Lo|Hi2].
- rewrite nth_error_app2 in Hv by (rewrite length_rev, DL; lia). rewrite length_rev, DL in Hv.
  assert (EI : (Z.to_nat (cmold + cmN - 1 - i) - Z.to_nat cmN)%nat = Z.to_nat (cmold - 1 - i)) by lia.
  rewrite EI, <- (cm_fa_nth_elems _ _ (cmold - 1 - i) RU ltac:(lia)) in Hv.
  rewrite AGok; [exact (XF c i v Hc' ltac:(unfold cmold in *; lia) Hv k Hk)|].
  apply (ok_fa c i Hc' ltac:(lia) ltac:(unfold cmold, kFreeArrayMax in *; lia) ltac:(intros _ _; exact Lo)). lia.
- set (jj := i - cmold).
  rewrite nth_error_app1 in Hv by (rewrite length_rev, DL; lia).
  rewrite nth_error_rev in Hv. rewrite DL in Hv. rewrite (proj2 (Nat.ltb_lt _ _)) in Hv by lia.
  assert (EJ : (Z.to_nat cmN - S (Z.to_nat (cmold + cmN - 1 - i)))%nat = Z.to_nat jj) by (unfold jj; lia).
  rewrite EJ in Hv. unfold kdrained in Hv. rewrite cm_nth_skipn in Hv.
  (* the old cache slot that held this object *)
  pose proof (amr_cells _ _ _ _ _ cmM) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & C2 & _).
  pose proof (proj1 (Forall_forall _ _) C2) as C2'.
  assert (OLDS : Forall (cell_holds B ly rd) (cache_cells X c)).
  { apply Forall_forall. intros ce Hce. apply C2'. apply in_flat_map. exists c. split; [apply In_zseq; lia | exact Hce]. }
  unfold cache_cells in OLDS. rewrite Hci in OLDS.
  do 3 (apply Forall_cons_iff in OLDS as [_ OLDS]).
  set (ii := (length (pc_chunks (cache X c)) - Z.to_nat (pc_max (cache X c) / 2) + Z.to_nat jj)%nat) in Hv.
  pose proof (proj1 (Forall_forall _ _) OLDS (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat ii)) (v / 16))
    ltac:(apply in_map_iff; exists (ii, v); split; [reflexivity | apply (nth_error_combine_seq _ 0 ii v); exact Hv])) as SL.
  cbn [cell_holds c_at c_val c_w z4 c4 aeval aoff] in SL.
  assert (VM : val_mem im_segs (mrestrict (w_H W) mem) (cmPC + 16 + 4 * (cmcnt - cmN) + 4 * jj) 4 (v / 16)).
  { apply cm_aview_val. intros kk Hkk. rewrite <- (SL kk Hkk). f_equal.
    unfold ii, cmPC, cmcnt, cmN, cmMAX. rewrite Hpm. unfold cmfull, cmcnt, cmMAX in Hf. apply Z.eqb_eq in Hf. lia. }
  pose proof (NEW_fa Hf jj (v / 16) ltac:(unfold jj; lia) VM) as VM'.
  replace (fa_base ly c + 4 * i + Z.of_nat k) with (cmDST + 4 * jj + Z.of_nat k) by (unfold cmDST, cmFA, jj; lia).
  exact (cm_val_aview _ 4 _ k VM' Hk).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The record at the cut.                                                                                           *)
Local Notation S' := (cdS X c off).

Lemma cm_drained_le : (length (kdrained c X) <= Z.to_nat cmN)%nat.
Proof. pose proof cmN_eq as [N1 N2]. unfold kdrained. rewrite length_skipn, Hpm. unfold cmN, cmMAX in *. lia. Qed.

Lemma cm_room_cd : cd_room X c.
Proof.
unfold cd_room. intros HF. unfold cdfull in HF. rewrite Hpm in HF. pose proof (Hroom HF) as HR.
pose proof cm_drained_le. pose proof cmN_eq as [N1 N2]. unfold cmN, cmMAX in *. lia.
Qed.

Lemma cm_region_eq : forall c', 0 <= c' -> c' <> c -> region_cells_cf S' c' = region_cells_cf X c'.
Proof. intros c' H1 H2. unfold region_cells_cf, region_cells. rewrite (cd_reg_other X c off Hc cmHlen cmHlenr c' H1 H2). reflexivity. Qed.
Lemma cm_cache_eq : forall c', 0 <= c' -> c' <> c -> cache_cells S' c' = cache_cells X c'.
Proof.
intros c' H1 H2. unfold cache_cells. rewrite (cdS_cinit X c off Hci), Hci, (cd_cache_other X c off Hc cmHlen cmHlenr c' H1 H2).
reflexivity.
Qed.
Lemma cm_cachej_eq : forall c', 0 <= c' -> c' <> c -> cache_junk S' c' = cache_junk X c'.
Proof.
intros c' H1 H2. unfold cache_junk. rewrite (cdS_cinit X c off Hci), Hci, (cd_cache_other X c off Hc cmHlen cmHlenr c' H1 H2).
reflexivity.
Qed.
Lemma cm_sec_eq : sec_cells S' = sec_cells X.
Proof. unfold sec_cells. rewrite (cdS_sec_res X c off), (cdS_sec_arr X c off), (cdS_chunks X c off). reflexivity. Qed.
Lemma cm_secj_eq : sec_junk S' = sec_junk X.
Proof. unfold sec_junk. rewrite (cdS_sec_res X c off), (cdS_sec_arr X c off), (cdS_chunks X c off). reflexivity. Qed.
Lemma cm_quar_eq : quar_cells S' = quar_cells X.
Proof. unfold quar_cells. rewrite (cdS_qthread X c off), (cdS_qglobal X c off). reflexivity. Qed.
Lemma cm_quarj_eq : quar_junk S' = quar_junk X.
Proof. unfold quar_junk. rewrite (cd_all_batches X c off). reflexivity. Qed.
Lemma cm_fs_eq : fs_cells S' = fs_cells X.
Proof. unfold fs_cells. rewrite (cdS_fs X c off). reflexivity. Qed.
Lemma cm_depot_eq : depot_cells ly S' = depot_cells ly X.
Proof. unfold depot_cells, depot_ids, depot_frames, depot_traces. rewrite (cdS_depot X c off). reflexivity. Qed.
Lemma cm_ialloc_eq : ialloc_cells B S' = ialloc_cells B X.
Proof. unfold ialloc_cells. rewrite (cdS_inited X c off). reflexivity. Qed.

Lemma FMI {A0 : Type} : forall (f : Z -> list A0) (P : A0 -> Prop) c', 1 <= c' <= 31 ->
Forall P (flat_map f (zseq 1 31)) -> Forall P (f c').
Proof.
intros f P c' Hc' H. apply Forall_forall. intros y Hy. apply (proj1 (Forall_forall _ _) H). apply in_flat_map.
exists c'. split; [apply In_zseq; lia | exact Hy].
Qed.

Lemma cm_cells : Forall (cell_holds B ly rd') (acells_cf B ly S').
Proof.
pose proof (amr_cells _ _ _ _ _ cmM) as C. unfold acells_cf in C. rewrite !Forall_app in C.
destruct C as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
unfold acells_cf. rewrite !Forall_app.
split.
{ apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  destruct (Z.eq_dec c' c) as [->|NE].
  - apply cm_region_c. exact (FMI _ _ c ltac:(lia) O1).
  - rewrite (cm_region_eq c' ltac:(lia) NE). exact (cm_region_other c' ltac:(lia) NE (FMI _ _ c' ltac:(lia) O1)). }
split.
{ apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  destruct (Z.eq_dec c' c) as [->|NE].
  - apply cm_cache_c. exact (FMI _ _ c ltac:(lia) O2).
  - rewrite (cm_cache_eq c' ltac:(lia) NE). exact (cm_cache_other c' ltac:(lia) NE (FMI _ _ c' ltac:(lia) O2)). }
split. { rewrite (cdS_chunks X c off). exact cm_chunks. }
split. { rewrite cm_sec_eq. exact (cm_sec O4). }
split. { rewrite cm_quar_eq. exact (cm_quar O5). }
split. { rewrite cm_fs_eq. exact (cm_fs O6). }
split. { rewrite cm_depot_eq. exact (cm_depot O7). }
split. { rewrite cm_ialloc_eq. exact (cm_ialloc O8). }
exact (cm_thread O9).
Qed.

Lemma cm_rv : forall l, Forall (range_vis B ly rd) l -> Forall (range_vis B ly rd') l.
Proof. intros l H. eapply Forall_impl; [|exact H]. intros r Hr i Hi. exact (VIS _ (Hr i Hi)). Qed.

Lemma cm_cache_junk_c : Forall (cell_holds B ly rd) (cache_cells X c) -> Forall (range_vis B ly rd) (cache_junk X c) ->
Forall (range_vis B ly rd') (cache_junk S' c).
Proof.
intros OLDC OJ. pose proof cm_kept_len as KL. pose proof cm_PC as (P1 & P2 & P3 & P4).
pose proof cm_class as (_ & K3 & _). pose proof cm_reg as (_ & _ & _ & C2). pose proof cmN_eq as [N1 N2].
unfold cache_junk in OJ |- *. rewrite (cdS_cinit X c off Hci). rewrite Hci in OJ.
rewrite (cd_cache_c X c off Hc cmHlen cmHlenr). cbn [pc_chunks].
apply Forall_cons_iff in OJ as [OJ _]. apply Forall_cons; [|apply Forall_nil].
intros i Hi. cbn [fst snd aeval] in Hi, OJ |- *. rewrite length_app in Hi |- *. cbn [length] in Hi |- *.
rewrite Nat2Z.inj_add in Hi |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hi |- *. rewrite KL in Hi |- *.
apply VIS. unfold cmcnt in *.
assert (HiZ : 0 <= i < 64 - 4 * (cmCNTP + 1)) by lia.
destruct (Z_lt_le_dec (4 * (cmCNTP + 1) + i) (4 * Z.of_nat (length (pc_chunks (cache X c))))) as [L|L].
- unfold cache_cells in OLDC. rewrite Hci in OLDC. do 3 (apply Forall_cons_iff in OLDC as [_ OLDC]).
  set (j := Z.to_nat ((4 * (cmCNTP + 1) + i) / 4)).
  assert (Hj4 : 4 * Z.of_nat j <= 4 * (cmCNTP + 1) + i < 4 * Z.of_nat j + 4) by (unfold j; rewrite Z2Nat.id by lia; lia).
  assert (Hj : (j < length (pc_chunks (cache X c)))%nat) by lia.
  destruct (nth_error (pc_chunks (cache X c)) j) as [v|] eqn:Ev; [|apply nth_error_None in Ev; lia].
  pose proof (proj1 (Forall_forall _ _) OLDC (z4 (aoff (AT (t_cache + 80 * c)) (16 + 4 * Z.of_nat j)) (v / 16))
    ltac:(apply in_map_iff; exists (j, v); split; [reflexivity | apply (nth_error_combine_seq _ 0 j v); exact Ev])) as SL.
  eapply (ch_some_x B ly rd _ _ _ _ SL). cbn [aeval aoff Z.of_nat Pos.of_succ_nat Pos.succ]. lia.
- match goal with |- rd ?a <> None => replace a with
    (ly_T ly + (t_cache + 80 * c + 16 + 4 * Z.of_nat (length (pc_chunks (cache X c)))) +
     (4 * (cmCNTP + 1) + i - 4 * Z.of_nat (length (pc_chunks (cache X c))))) by lia end.
  apply OJ. cbn [fst snd]. lia.
Qed.

Lemma cm_junk : Forall (range_vis B ly rd') (ajunk_cf B ly S').
Proof.
pose proof (amr_junk _ _ _ _ _ cmM) as J. unfold ajunk_cf in J |- *.
apply Forall_cons_iff in J as [J1 J]. apply Forall_cons_iff in J as [J2 J]. rewrite !Forall_app in J.
destruct J as (J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10).
pose proof (amr_cells _ _ _ _ _ cmM) as C. unfold acells_cf in C. rewrite !Forall_app in C. destruct C as (_ & O2 & _).
apply Forall_cons; [intros i Hi; exact (VIS _ (J1 i Hi))|].
apply Forall_cons; [intros i Hi; exact (VIS _ (J2 i Hi))|].
rewrite !Forall_app.
split; [exact (cm_rv _ J3)|].
split.
{ apply Forall_flat_map'. intros c' Hc0. apply zseq_In in Hc0.
  destruct (Z.eq_dec c' c) as [->|NE].
  - exact (cm_cache_junk_c (FMI _ _ c ltac:(lia) O2) (FMI _ _ c ltac:(lia) J4)).
  - rewrite (cm_cachej_eq c' ltac:(lia) NE). exact (cm_rv _ (FMI _ _ c' ltac:(lia) J4)). }
split; [rewrite (cdS_chunks X c off); exact (cm_rv _ J5)|].
split; [rewrite cm_secj_eq; exact (cm_rv _ J6)|].
split; [rewrite cm_quarj_eq; exact (cm_rv _ J7)|].
split; [exact (cm_rv _ J8)|].
split; [exact (cm_rv _ J9) | exact (cm_rv _ J10)].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The remaining fields of the record, and the relation's outer conjuncts.                                          *)
Lemma cm_flags : fs_flags_ok ly rd' S'.
Proof.
intros cid pos Hc' Hpos. rewrite (cd_frames X c off). pose proof (flag_off_bounds cid pos Hc' Hpos) as FB.
rewrite AGok; [exact (amr_flags _ _ _ _ _ cmM cid pos Hc' Hpos)|].
apply (ok_static 3%nat (ly_F ly, kFakeStackSize)); [left; lia | reflexivity |].
cbn [fst snd]. unfold flag_addr, kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *. lia.
Qed.

Lemma cm_depot_ok : depot_ok B ly rd' S'.
Proof.
pose proof (amr_depot _ _ _ _ _ cmM) as (heads & links & D1 & D2 & D3).
unfold depot_ok. unfold depot_ids, depot_traces in *. rewrite (cdS_depot X c off).
exists heads, links. split; [|split; [|exact D3]].
- intros b Hb. destruct (D1 b Hb) as [E1 E2]. split; [exact E1|]. intros k Hk.
  rewrite AGok; [exact (E2 k Hk)|]. apply (cm_area_ok (as_depot B, 4 * 2 ^ 20 + 32)); [cbn; tauto | cbn [fst snd]; unfold d_tab_words in Hb; lia].
- intros id Hid. destruct (D2 id Hid) as (E1 & E2 & E3). split; [exact E1|].
  assert (NB : Z.of_nat (length (st_depot X)) <= 4097).
  { pose proof (depot_len_bound _ _ (amr_universe _ _ _ _ _ cmM) (wfr_depot _ _ _ _ _ cmWF)) as DL. unfold DEPOT_MAX in DL. lia. }
  assert (OR : forall x, ly_NB ly + 16 * id <= x < ly_NB ly + 16 * id + 16 -> rd' x = rd x).
  { intros x Hx. apply AGok. apply (ok_static 4%nat (ly_NB ly, kNodesBlockSize)); [left; lia | reflexivity |].
    cbn [fst snd]. unfold kNodesBlockSize. lia. }
  split; intros k Hk; rewrite OR by lia; [exact (E2 k Hk) | exact (E3 k Hk)].
Qed.

(* The step changes no chunk and no queue, so the shadow's exemption set is the cut's (YGcfInstDrainR's weak form);
   every governed byte is in the low band, which the step's window misses. *)
Lemma cm_shadow : shadow_ok_weak_cf B ly Hp rd' S'.
Proof.
assert (EQQ : forall b, In b (map ck_beg (q_items S')) -> In b (map ck_beg (q_items X))).
{ unfold q_items, all_batches. rewrite (cdS_qthread X c off), (cdS_qglobal X c off). intros b Hb; exact Hb. }
apply (shadow_weak_ext_cf B ly X S' Hp rd rd' (cdS_chunks X c off) EQQ
  (fun g => cd_ashadow ly X c off Hc cmHlen cmHlenr B g)); [|exact (amr_shadow _ _ _ _ _ cmM)].
intros g v Hg Hv0. pose proof (RL.ashadow_low_cf B ly X Hp _ g v cmM Hv0) as SL.
apply AGok. apply ok_lowband. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.

Lemma cm_zshadow : zshadow_ok B ly rd'.
Proof.
pose proof (amr_zshadow _ _ _ _ _ cmM) as Z0. unfold zshadow_ok in *. apply Forall_forall. intros r Hr i Hi.
unfold shadow_of_addr. fold (shadow_addr (fst r)). change (SHADOW_OFF + fst r / 8) with (shadow_addr (fst r)).
pose proof (RL.zshadow_low_cf B ly X Hp _ r i cmM Hr Hi) as ZL.
rewrite AGok; [exact (proj1 (Forall_forall _ _) Z0 r Hr i Hi)|]. apply ok_lowband. unfold SHADOW_OFF, kLowShadowBeg in *. lia.
Qed.

Lemma cm_zero : Forall (range_zero B ly rd') (ialloc_zero B).
Proof.
pose proof (amr_zero _ _ _ _ _ cmM) as Z0. pose proof (aso_ialloc _ cmSY) as [I1 I2].
apply Forall_forall. intros r Hr i Hi.
assert (Ha : as_ialloc_lo B <= aeval B ly (fst r) + i < as_ialloc_lo B + (as_ialloc_hi B - as_ialloc_lo B)).
{ unfold ialloc_zero in Hr. destruct Hr as [<-|[<-|[]]]; cbn [fst snd aeval] in *; lia. }
rewrite AGok; [exact (proj1 (Forall_forall _ _) Z0 r Hr i Hi)|].
apply (cm_area_ok (as_ialloc_lo B, as_ialloc_hi B - as_ialloc_lo B)); [cbn; tauto | exact Ha].
Qed.

(* The relation's two machine cells across the step (field round 2): the step changes no region's holes and no secondary, and
   its writes (cdwin) miss the exhausted bytes (RegionInfo + cf_exh_off, outside cmWRG) and the buffer's object
   (owned static, inside the image). *)
Lemma cm_exh_eq : forall c', exh_mem_cf S' c' = exh_mem_cf X c'.
Proof.
assert (H : forall c'', 0 <= c'' -> rg_holes (reg S' c'') = rg_holes (reg X c'')).
{ intros c'' H0. destruct (Z.eq_dec c'' c) as [->|NE].
  - rewrite (cd_reg_c X c off Hc cmHlen cmHlenr). destruct (cdfull X c); reflexivity.
  - rewrite (cd_reg_other X c off Hc cmHlen cmHlenr c'' H0 NE). reflexivity. }
intros c'. unfold exh_mem_cf. destruct (Z_lt_le_dec c' 0) as [N|N]; [|rewrite (H c' N); reflexivity].
assert (E : forall s : astate, reg s c' = reg s 0).
{ intros s. unfold reg, znth. replace (Z.to_nat c') with (Z.to_nat 0) by lia. reflexivity. }
rewrite !E. rewrite (H 0 ltac:(lia)). reflexivity.
Qed.

Lemma cm_exh : EXH_OFF_OK -> exh_cell_cf B ly X rd -> exh_cell_cf B ly S' rd'.
Proof.
intros EXO HE. apply (exh_cell_cf_frame B ly ly X S' rd rd' HE cm_exh_eq).
intros c' Hc'. unfold EXH_OFF_OK in EXO.
change (aeval B ly (aoff (ASp (kRegionInfoOff + 128 * c')) cf_exh_off)) with (SB + (kRegionInfoOff + 128 * c' + cf_exh_off)).
apply AGok. apply (ok_rinfo c').
- exact Hc'.
- unfold kRegionInfoOff; lia.
- intros _ _ HW. unfold cmWRG, cmRG in HW.
destruct (Z.eq_dec c' c) as [->|NE]; lia.
Qed.

Lemma cm_errb : errb_obj_owned_t B -> errb_cells_cf B ly X rd -> errb_cells_cf B ly S' rd'.
Proof.
intros EOO HEB.
pose proof (cdS_secs X c off) as ES.
apply (errb_cells_cf_frame B ly ly X S' rd rd' HEB);
  [unfold errb_mapped_cf; rewrite ES; reflexivity
  |unfold errb_data_cf; rewrite ES; reflexivity
  |unfold errb_cap_cf, errb_e; rewrite ES; reflexivity
  |unfold errb_size_cf; rewrite ES; reflexivity | |].
- intros a Ha. apply AGok. apply ok_img.
  pose proof (EOO a Ha) as OS. pose proof (amr_static_img _ _ _ _ _ cmM) as SI. apply Exists_exists in OS as (r & Hr & Ha').
  pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
  unfold zr_sub, in_zr in *. lia.
- exact VIS.
Qed.

(* Printf's two cells across the step (field round 3): owned static, inside the image, so the step's writes miss them. *)
Lemma cm_pf : pf_cells_owned_t B -> pf_cells_cf B ly rd -> pf_cells_cf B ly rd'.
Proof.
intros PO HP. apply (pf_cells_frame_cf B ly rd rd'); [|exact HP].
intros a Ha. apply AGok. apply ok_img.
pose proof (proj1 (proj1 PO a Ha)) as OS. pose proof (amr_static_img _ _ _ _ _ cmM) as SI. apply Exists_exists in OS as (r & Hr & Ha').
pose proof (proj1 (Forall_forall _ _) SI r ltac:(apply in_app_iff; left; exact Hr)) as SUB.
unfold zr_sub, in_zr in *. lia.
Qed.

Lemma cm_ARmcfR : 0 <= off - region_off c < rg_alloc_user (reg X c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems X c) -> ARmcfR B ly S' Hp rd'.
Proof.
intros Hx Hxm Hxni. pose proof cmM as M0.
destruct M0 as [Xwf Xuni Xsyms Xlay Xplaced Xconst Xcowned Xcells Xfa Xflags Xdepot Xshadow Xzsh Xjunk Xareas Xclient
  Xzero Xtsd Ximg Xhp Xxs Xexh Xerrb Xown Xpf Xpfo].
constructor.
- exact (cd_WfR X c off Hc Hci cmHlen cmHlenr cm_room_cd _ 0 0 0 Xwf Hx Hxm Hxni).
- exact Xuni.
- exact Xsyms.
- exact Xlay.
- exact (cd_sec_placed ly X c off Xplaced).
- exact cm_const.
- exact Xcowned.
- exact cm_cells.
- exact cm_fa.
- exact cm_flags.
- exact cm_depot_ok.
- exact cm_shadow.
- exact cm_zshadow.
- exact cm_junk.
- rewrite (cd_aareas X c off Hc cmHlen cmHlenr). exact (cm_rv _ Xareas).
- rewrite (cd_aclient X c off). exact (cm_rv _ Xclient).
- exact cm_zero.
- exact Xtsd.
- exact Ximg.
- rewrite (cdS_chunks X c off). exact Xhp.
- exact (cd_xs_placed ly X c off Xxs).
- exact (cm_exh (EXH_OFF_OK_of_t (proj1 Xown)) Xexh).
- exact (cm_errb (proj1 (proj2 Xown)) Xerrb).
- exact Xown.
- exact (cm_pf Xpfo Xpf).
- exact Xpfo.
Qed.

(* the ledger reads the regions' mapped fields and holes, the secondaries and the errbuf: all unchanged *)
Lemma cm_cut_ok : forall x, cut_ok ly S' x <-> cut_ok ly X x.
Proof.
intros x. unfold cut_ok. split; intros [H|[H|(c' & Hc' & H)]]; try (left; exact H); try (right; left; exact H);
right; right; exists c'; split; [exact Hc'| |exact Hc'|];
destruct (cd_reg_fields X c off Hc cmHlen cmHlenr c' ltac:(lia)) as (E1 & E2 & E3 & E4); rewrite ?E1, ?E3 in *; exact H.
Qed.
Lemma cm_hole : forall a, prim_hole_at ly S' a <-> prim_hole_at ly X a.
Proof.
intros a. unfold prim_hole_at. split; intros (c' & h & Hc' & Hh & Ha); exists c', h; split; [exact Hc'| |exact Hc'|];
destruct (cd_reg_fields X c off Hc cmHlen cmHlenr c' ltac:(lia)) as (E1 & E2 & E3 & E4); rewrite ?E4 in *; exact (conj Hh Ha).
Qed.

Lemma cm_ALedger : forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ALedger_cf im_segs ly S' md'.
Proof.
intros md' Ev El Ee. pose proof (YG0qcf.ALedger_same_cf im_segs ly X md md' cmLED Ev El Ee) as L.
destruct L as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17].
constructor; try assumption.
- destruct A4 as (pieces & (PF & PD & PH) & PI). exists pieces. split; [|exact PI]. split; [|split; [exact PD|]].
  + eapply Forall_impl; [|exact PF]. intros p (P1 & P2 & P3). split; [exact P1|]. split; apply cm_cut_ok; assumption.
  + intros a Ha. rewrite (PH a Ha). split; intros N HH; apply N; apply cm_hole; [exact HH|]. exact HH.
- rewrite (cd_sec_extents ly X c off). exact A7.
- intros e He. pose proof (A8 e He) as HE. unfold errb_zone in *. rewrite (cd_sec_extents ly X c off), (cd_xs ly X c off). exact HE.
- (* the eager bound reads the committed primary, the reserved secondaries and the secondaries' / errbuf's maps,
     none of which the no-growth step changes *)
  assert (EE : eager_cf ly S' md' = eager_cf ly X md').
  { unfold eager_cf, errb_zone. rewrite (cd_prim_committed X c off Hc cmHlen cmHlenr), (cdS_sec_res X c off),
      (cd_sec_extents ly X c off), (cd_xs ly X c off). reflexivity. }
  rewrite EE. exact A9.
- rewrite (cd_sec_extents ly X c off). exact A12.
- (* the errbuf extent is the entry's *)
  intros e He. rewrite (cd_xs ly X c off) in He. exact (A17 e He).
Qed.

Lemma cm_ARcfR : 0 <= off - region_off c < rg_alloc_user (reg X c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems X c) ->
forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARcfR im_segs B ly S' Hp W mem' md'.
Proof.
intros Hx Hxm Hxni md' Ev El Ee. pose proof MR as (M & LED & (BU & SA & BV) & MW & HSH).
split; [exact (cm_ARmcfR Hx Hxm Hxni)|]. split; [exact (cm_ALedger md' Ev El Ee)|].
split; [split; [rewrite (cd_abudget X c off Hc cmHlen cmHlenr); exact BU | split; [|exact BV]]|].
{ intros e He. rewrite (cd_sec_extents ly X c off) in He. exact (SA e He). }
split; [exact (amwf_same md md' Ev El MW)|].
refine (RL.ahs_transfer_cf im_segs B ly X Hp S' (w_H W) mem mem' _ M HSH VIS _ _ _ _).
- eapply RL.al_img_env_cf; [exact cmLO | exact cmLED].
- intros a Ha _. unfold w64. apply MEQ. rewrite unsigned_lit_small.
  + intros HD. destruct (ok_lowband a ltac:(unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia)) as [_ NW].
    exact (NW HD).
  + unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
- intros a _ CB. unfold aclient_byte in *. rewrite (cdS_chunks X c off), (cd_frames X c off) in CB. exact CB.
- exact (cd_sec_extents ly X c off).
- intros g Hg Hga HF _. apply AGok. apply ok_lowband. pose proof (shadow_addr_band_rw g Hga) as SB.
  unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *. lia.
Qed.

Lemma cm_aowned : forall a, aowned B ly S' a -> aowned B ly X a.
Proof.
intros a H. unfold aowned, aclient_byte in *. rewrite (cd_sec_extents ly X c off), (cdS_chunks X c off), (cd_frames X c off) in H.
exact H.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* F12: the drain's cut relation across the no-growth CacheDealloc step.                                            *)
Section N.
Variable IOK : Z -> Prop.
Variable inst : Z.
Hypothesis HI : IOK inst.
Hypothesis HXM : xs_mapped_cf ly X md.

Theorem cd_step_cf : forall S', cache_dealloc c off X = IRet (tt, S') ->
0 <= off - region_off c < rg_alloc_user (reg X c) -> (off - region_off c) mod class_size c = 0 ->
~ In (off - region_off c) (class_elems X c) ->
forall md', m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
ARXr_cf B IOK Hp inst ly S' W mem' md' /\ (forall a, aowned B ly S' a -> aowned B ly X a).
Proof.
intros S' E Hx Hxm Hxni md' Ev El Ee.
rewrite (cd_eq X c off Hc Hci cmHlen cmHlenr cm_room_cd) in E. injection E as <-.
split; [split; [exact HI | split; [exact (cm_ARcfR Hx Hxm Hxni md' Ev El Ee)|]] | exact cm_aowned].
intros e He. rewrite (cd_xs ly X c off) in He. rewrite Ev. exact (HXM e He).
Qed.
End N.

End M.
End U.
