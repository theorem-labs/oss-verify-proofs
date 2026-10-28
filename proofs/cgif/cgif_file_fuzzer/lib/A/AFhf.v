(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YN3v YI04 YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFeq AFeu AFf2.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma le_byte_mod64 : forall v k, YG0f.le_byte (v mod 2 ^ 64) 8 k = YG0f.le_byte v 8 k.
Proof. intros v k. unfold YG0f.le_byte. change (8 * Z.of_nat 8) with 64. rewrite Z.mod_mod by lia. reflexivity. Qed.
Lemma val_mem_mod64 : forall m a v, val_mem tfibsegs m a 8 v -> val_mem tfibsegs m a 8 (v mod 2 ^ 64).
Proof. intros m a v Hv k Hk. rewrite <- le_byte_eq, le_byte_mod64, le_byte_eq. exact (Hv k Hk). Qed.
Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma mod64_range : forall v, 0 <= v mod 2 ^ 64 < 2 ^ 64.
Proof. intros v. apply Z.mod_pos_bound. lia. Qed.
Lemma wvb_self : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma same_io_refl : forall m, same_io m m. Proof. intros. repeat split; reflexivity. Qed.
Lemma same_io_trans : forall m1 m2 m3, same_io m1 m2 -> same_io m2 m3 -> same_io m1 m3.
Proof. intros m1 m2 m3 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). unfold same_io. rewrite B1, B2, B3, B4. repeat split; assumption. Qed.
Lemma same_io_with_vm_backing : forall l p md, same_io md (with_vm_backing l p md). Proof. intros. repeat split; reflexivity. Qed.
Lemma AR_model_same : forall B ly S W mem md md',
AR tfibsegs B ly S W mem md -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
AR tfibsegs B ly S W mem md'.
Proof.
intros B ly S W mem md md' (M & L & Bu & MW & HS) Hv Hl He. split; [exact M|]. split; [exact (ALedger_same tfibsegs ly S md md' L Hv Hl He) |].
split; [exact Bu|]. split; [exact (amwf_same md md' Hv Hl MW) | exact HS].
Qed.
Lemma AR_wvb : forall B ly S W mem md mat, AR tfibsegs B ly S W mem md -> AR tfibsegs B ly S W mem (with_vm_backing (m_vm_lazy md) mat md).
Proof. intros B ly S W mem md mat HA. apply (AR_model_same B ly S W mem md _ HA); [apply m_vmmaps_wvb | apply m_vm_lazy_wvb | apply eager_used_wvb]. Qed.
Lemma val_mem_aview_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v,
(forall k, (k < n)%nat -> aview tfibsegs H' m' (a + Z.of_nat k) = aview tfibsegs H m (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v HA Hv k Hk. pose proof (Hv k Hk) as E. pose proof (HA k Hk) as A. unfold aview in A. rewrite E in A. cbn [option_map] in A.
destruct (mbyte tfibsegs (mrestrict H' m') (a + Z.of_nat k)) as [b'|]; cbn [option_map] in A; [|discriminate].
injection A as A. f_equal. apply bv_eq. rewrite A. reflexivity.
Qed.
Lemma apresent_aview_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a,
TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H' m' a = aview tfibsegs H m a -> apresent H m a -> apresent H' m' a.
Proof.
intros H H' m m' a Ha HA P0. apply apresent_mbyte in P0 as [b Hb].
assert (A : aview tfibsegs H m a = Some (bv_unsigned b)) by (unfold aview; rewrite Hb; reflexivity).
rewrite <- HA in A. apply aview_some in A as (b' & Hb' & _). exact (mbyte_high_apresent H' m' a b' Ha Hb').
Qed.
Section e.
Variable B : asyms.
Variable ly : alayout.
Local Notation SB := (ly_space ly).
Definition bslot (z a : Z) : Prop := SB + z <= a < SB + z + kBatchBytes.
Definition slot_ok (X : astate) (z : Z) : Prop :=
0 <= z - region_off kBatchClass < rg_alloc_user (reg X kBatchClass) /\ (z - region_off kBatchClass) mod class_size kBatchClass = 0 /\
~ In (z - region_off kBatchClass) (class_elems X kBatchClass).
Lemma RIx_slots : forall U pp cc bb X its P selfs z,
RIx U pp cc bb X its P selfs -> In z (selfs ++ map b_self P) -> slot_ok X z.
Proof. intros U pp cc bb X its P selfs z (_ & _ & _ & _ & SF & _) Hz. exact (proj1 (Forall_forall _ _) SF z Hz). Qed.
Lemma class_size_24 : class_size kBatchClass = 8192. Proof. reflexivity. Qed.
Lemma region_off_24 : region_off kBatchClass = 24 * 2 ^ 32. Proof. reflexivity. Qed.
Lemma slot_carved : forall X rd z, ARm B ly X rd -> slot_ok X z ->
0 <= z - region_off kBatchClass /\ z - region_off kBatchClass + kBatchBytes <= rg_alloc_user (reg X kBatchClass) /\
rg_alloc_user (reg X kBatchClass) <= rg_mapped_user (reg X kBatchClass) <= 2 ^ 31.
Proof.
intros X rd z M (Z1 & Z2 & _). pose proof (am_wf _ _ _ _ M) as W.
pose proof (wf_classes _ _ _ _ _ W kBatchClass ltac:(unfold kBatchClass; lia)) as CL.
pose proof (wr_alloc _ _ _ _ _ _ CL) as A1. pose proof (wr_alloc_al _ _ _ _ _ _ CL) as A2.
pose proof (mapped_user_bound (as_universe B) 0 0 0 X kBatchClass W ltac:(unfold kBatchClass; lia)) as MB. unfold kUserMapSize, EV_MAX in MB.
rewrite class_size_24 in Z2, A2. unfold kBatchBytes. split; [lia|]. split; [|lia]. clear - Z1 Z2 A2. lia.
Qed.
Lemma slot_puser : forall X rd z, ARm B ly X rd -> slot_ok X z -> forall a, bslot z a -> puser ly X a.
Proof.
intros X rd z M SZ a Ha. pose proof (slot_carved X rd z M SZ) as (C1 & C2 & C3). unfold bslot in Ha. unfold puser.
exists kBatchClass. split; [unfold kBatchClass; lia|]. unfold region_base. lia.
Qed.
Lemma slot_high : forall X rd z, ARm B ly X rd -> slot_ok X z -> forall a, bslot z a ->
ly_prim ly <= a < ly_prim ly + kPrimResvSize /\ kHighMemBeg <= a < ASAN_CEIL /\ TFIB_IMG_END <= a < 2 ^ 64.
Proof.
intros X rd z M SZ a Ha. pose proof (slot_carved X rd z M SZ) as (C1 & C2 & C3). unfold bslot in Ha.
pose proof (region_in_prim ly kBatchClass (am_layout _ _ _ _ M) ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5). unfold region_base in *.
ceil; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kBatchBytes, ASAN_CEIL, kHighMemBeg, TFIB_IMG_END in *. lia.
Qed.
Lemma slot_not_stack : forall X rd z, ARm B ly X rd -> slot_ok X z -> forall a, bslot z a -> ~ (ly_stk_lo ly <= a < ly_stk_hi ly).
Proof.
intros X rd z M SZ a Ha Hs. pose proof (slot_high X rd z M SZ a Ha) as ((P1 & P2) & _).
pose proof (lo_disj ly (am_layout _ _ _ _ M)) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & _). pose proof (Forall_nth_f _ _ 7 _ DP eq_refl) as PSTK.
unfold zdisjoint in PSTK. cbn [fst snd] in PSTK. lia.
Qed.
Lemma slot_vs_chunk : forall X rd z k, ARm B ly X rd -> slot_ok X z -> In k (st_chunks X) ->
forall a, bslot z a -> ~ (ck_base B ly k <= a < ck_base B ly k + ck_extent k).
Proof.
intros X rd z k M SZ Hk a Ha Hin. pose proof (slot_carved X rd z M SZ) as (C1 & C2 & C3). pose proof SZ as (Z1 & Z2 & Z3).
pose proof (chunk_facts B ly X rd k M Hk) as CF. unfold cfacts in CF. destruct CF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & CK).
pose proof (region_in_prim ly kBatchClass (am_layout _ _ _ _ M) ltac:(unfold kBatchClass; lia)) as (R1 & R2 & R3 & R4 & R5).
unfold bslot in Ha. rewrite class_size_24 in Z2. unfold region_base in *. rewrite region_off_24 in *.
destruct (ck_beg k) as [|off|r o|c p] eqn:Eb; try solve [destruct CK].
-
cbv zeta in CK. destruct CK as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9).
set (c := prim_class off) in *. set (x := off - region_off c) in *.
rewrite (region_off_eq c) in K5 by lia.
destruct (Z.eq_dec c kBatchClass) as [Ec|Nc].
+
assert (INx : In x (class_elems X kBatchClass)).
{ rewrite <- Ec. unfold class_elems. rewrite !in_app_iff. right; right; left. subst x c. exact (In_chunk_offs X k off Hk Eb). }
assert (NE : x <> z - 24 * 2 ^ 32) by (intros E; apply Z3; rewrite <- E; exact INx).
rewrite Ec in K4, K7. rewrite class_size_24 in K4, K7. rewrite K4 in Hin. rewrite Ec in K5. unfold kBatchClass in K5. unfold kBatchBytes in *.
clear - Ha Hin K5 K7 Z2 NE. nia.
+
rewrite K4 in Hin. unfold kBatchClass in Nc. unfold kBatchBytes in *.
pose proof (class_ok c ltac:(lia)) as (Q1 & _).
assert (c <= 23 \/ 25 <= c) as [Lc|Lc] by lia; clear - Ha Hin K5 K6 K8 K9 C1 C2 C3 Lc Q1; nia.
-
destruct CK as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
pose proof (am_placed _ _ _ _ M) as [_ PD].
pose proof (pairwise_app_inv zdisjoint (sec_extents ly X) (static_extents ly) PD) as (_ & _ & CR).
assert (INP : In (ly_prim ly, kPrimResvSize) (static_extents ly)) by (unfold static_extents, owned_extents; cbn; tauto).
pose proof (CR _ _ K5 INP) as DJ. unfold zdisjoint in DJ. cbn [fst snd] in DJ.
rewrite K3, K4 in Hin. unfold kPage, kBatchBytes in *. lia.
Qed.
End e.
Section f.
Variable B : asyms.
Variable ly : alayout.
Local Notation SB := (ly_space ly).
Definition items_ok (l : list batch) : Prop := Forall (fun b => (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat) l.
Lemma batch_own_cells_in_slot : forall b nx ce, (length (b_items b) <= Z.to_nat kBatchSlots)%nat -> In ce (batch_own_cells b nx) ->
forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> bslot ly (b_self b) (aeval B ly (c_at ce) + j).
Proof.
intros b nx ce Hlen Hce j Hj. unfold bslot, kBatchBytes. unfold kBatchSlots in Hlen.
unfold batch_own_cells in Hce. destruct Hce as [<-|[<-|[<-|Hce]]].
1-3: cbn in Hj |- *; lia.
apply in_map_iff in Hce as ([i y] & <- & Hiy). apply in_combine_l in Hiy. apply in_seq in Hiy. cbn in Hj |- *. lia.
Qed.
Lemma batch_cells_in_slots : forall l ce, items_ok l -> In ce (batch_cells l) ->
exists b, In b l /\ forall j, 0 <= j < Z.max 1 (Z.of_nat (c_w ce)) -> bslot ly (b_self b) (aeval B ly (c_at ce) + j).
Proof.
intros l ce Hl Hce. apply In_batch_cells in Hce as (i & b & Hi & Hce). exists b. split; [exact (nth_error_In _ _ Hi)|].
apply (batch_own_cells_in_slot b (next_exp l i) ce); [|exact Hce]. exact (proj2 (proj1 (Forall_forall _ _) Hl b (nth_error_In _ _ Hi))).
Qed.
Lemma batch_cells_xfer : forall l (rd rd' : reader), items_ok l ->
(forall b a, In b l -> bslot ly (b_self b) a -> rd' a = rd a) ->
Forall (cell_holds B ly rd) (batch_cells l) -> Forall (cell_holds B ly rd') (batch_cells l).
Proof.
intros l rd rd' Hl AG OLD. apply Forall_forall. intros ce Hce.
apply (cell_holds_agree B ly rd rd' ce (proj1 (Forall_forall _ _) OLD ce Hce)). intros j Hj.
destruct (batch_cells_in_slots l ce Hl Hce) as (b & Hb & Hs). exact (AG b _ Hb (Hs j Hj)).
Qed.
Lemma batch_cells_tail : forall rd b t, Forall (cell_holds B ly rd) (batch_cells (b :: t)) -> Forall (cell_holds B ly rd) (batch_cells t).
Proof. intros rd b t H. cbn [batch_cells] in H. apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H]. apply Forall_app in H as [_ H]. exact H. Qed.
Definition firstaddr (l : list batch) : Z := match l with [] => 0 | b :: _ => SB + b_self b end.
Lemma hdr_addr : forall k, match ck_beg k with PPrim _ | PSec _ _ => True | _ => False end ->
aeval B ly (sptr_exp (ck_hdr k)) = ck_base B ly k + ck_rz k - kChunkHeaderSize.
Proof. intros k Hk. unfold ck_hdr. change (aeval B ly (sptr_exp (padd (ck_beg k) (ck_rz k - kChunkHeaderSize)))) with (sptr_addr B ly (padd (ck_beg k) (ck_rz k - kChunkHeaderSize))). rewrite (sptr_addr_padd B ly _ _ Hk). unfold ck_base. lia. Qed.
Lemma batch_head_cells : forall H mem b t, Forall (cell_holds B ly (aview tfibsegs H mem)) (batch_cells (b :: t)) ->
let m := mrestrict H mem in
val_mem tfibsegs m (SB + b_self b) 8 (firstaddr t) /\ val_mem tfibsegs m (SB + b_self b + 8) 8 (b_bytes b) /\
val_mem tfibsegs m (SB + b_self b + 16) 8 (Z.of_nat (length (b_items b))) /\
(forall i k, nth_error (b_items b) i = Some k -> val_mem tfibsegs m (SB + b_self b + 24 + 8 * Z.of_nat i) 8 (aeval B ly (sptr_exp (ck_hdr k)))).
Proof.
intros H mem b t HC. cbn [batch_cells] in HC.
apply Forall_cons_iff in HC as [C0 HC]. apply Forall_cons_iff in HC as [C8 HC]. apply Forall_cons_iff in HC as [C16 HC]. apply Forall_app in HC as [CI _].
cbv zeta. split; [|split; [|split]].
- pose proof (cell_holds_val_mem B ly H mem _ 8 _ C0) as V. cbn [aeval batch_exp] in V. destruct t as [|b' t']; cbn [aeval batch_exp] in V; exact V.
- pose proof (cell_holds_val_mem B ly H mem _ 8 _ C8) as V. cbn [aeval aoff batch_exp] in V. eapply val_mem_addr; [exact V | lia].
- pose proof (cell_holds_val_mem B ly H mem _ 8 _ C16) as V. cbn [aeval aoff batch_exp] in V. eapply val_mem_addr; [exact V | lia].
- intros i k Hi.
assert (IN : In (i, k) (combine (seq 0 (length (b_items b))) (b_items b))).
{ replace i with (0 + i)%nat by lia. revert Hi. generalize 0%nat as s. generalize (b_items b) as l. induction i as [|i IH]; intros l s Hi.
- destruct l as [|k0 l]; [discriminate|]. cbn in Hi. injection Hi as ->. cbn. left. f_equal. lia.
- destruct l as [|k0 l]; [discriminate|]. cbn in Hi. cbn. right. replace (s + S i)%nat with (S s + i)%nat by lia. exact (IH l (S s) Hi). }
pose proof (proj1 (Forall_forall _ _) CI _ (in_map _ _ _ IN)) as C. cbn [fst snd] in C.
pose proof (cell_holds_val_mem B ly H mem _ 8 _ C) as V. cbn [aeval aoff batch_exp] in V. eapply val_mem_addr; [exact V | lia].
Qed.
End f.
End d.
