(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YP09 YN3v YI04 YK0s YK04 YA0i YA0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AF0m AF0x AFl0 AFl1 AFeu AFf2 AFhf AFh9.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Variables (ly : alayout) (X0 : astate) (W0 : world tfibsegs) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Definition sp0 : Z := bv_unsigned (getr regs0 2).
Definition sp1 : Z := sp0 - YFRAME.
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation U := (as_universe B).
Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Definition hdra (k : chunk) : Z := aeval B ly (sptr_exp (ck_hdr k)).
Definition SY (a : Z) : Prop := sp0 - DRSTACK <= a < sp0 + 32.
Record acc (X : astate) (W : world tfibsegs) (mem : word -> option byte) (md : Model) : Prop := {
acc_AR : AR tfibsegs B ly X W mem md;
acc_wle : wle W0 W;
acc_io : same_io md0 md;
acc_own : forall a, aowned B ly X a -> aowned B ly X0 a;
acc_frame : forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly X0 a -> ~ aowned B ly X a -> ~ ascratch B DRSTACK regs0 a -> ~ (sp0 <= a < sp0 + 32) ->
aview tfibsegs (w_H W) mem a = aview tfibsegs (w_H W0) mem0 a;
acc_pres : forall a, SY a -> apresent (w_H W) mem a;
acc_inited : st_cache_inited X = true
}.
Definition common_regs (regs : bvmap 5 word) : Prop :=
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\ getr regs 26 = getr regs0 26 /\ getr regs 27 = getr regs0 27.
Definition loop_regs (regs : bvmap 5 word) : Prop :=
getr regs 2 = w64 sp1 /\ getr regs 8 = w64 sp0 /\ getr regs 9 = w64 A_ALLOCATOR /\ getr regs 18 = w64 (A_ALLOCATOR + 64) /\
getr regs 19 = w64 (A_ALLOCATOR + 688) /\ getr regs 21 = w64 (2 ^ 37).
Definition frame_cells (W : world tfibsegs) (mem : word -> option byte) : Prop :=
val_mem tfibsegs (mrestrict (w_H W) mem) (sp1 + 8) 8 (T + t_cache) /\ AFh9.saved_cells regs0 (mrestrict (w_H W) mem).
Definition tmp_cells (W : world tfibsegs) (mem : word -> option byte) (rest : list batch) (lz qb : Z) : Prop :=
let m := mrestrict (w_H W) mem in
val_mem tfibsegs m sp0 8 (zlen rest) /\ val_mem tfibsegs m (sp0 + 8) 8 (firstaddr ly rest) /\
val_mem tfibsegs m (sp0 + 16) 8 lz /\ val_mem tfibsegs m (sp0 + 24) 8 qb /\ 0 <= lz < ASAN_CEIL /\ 0 <= qb < 2 ^ 64.
Record ost (X : astate) (rest : list batch) (lz qb : Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
o_acc : acc X W mem md;
o_rix : RIx U 0 0 0 X [] rest [];
o_ne : rest <> [];
o_len : zlen rest < 100000;
o_cregs : common_regs regs;
o_lregs : loop_regs regs;
o_a0 : getr regs 10 = w64 (zlen rest);
o_frame : frame_cells W mem;
o_tmp : tmp_cells W mem rest lz qb;
o_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells rest)
}.
Definition batch_regs (regs : bvmap 5 word) (b : batch) : Prop :=
getr regs 20 = w64 (SB + b_self b) /\ getr regs 22 = w64 (zlen (b_items b)) /\ getr regs 24 = w64 (zlen (b_items b) + 16).
Record rcst (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
rc_acc : acc X W mem md;
rc_rix : RIx U 0 0 0 X its t [b_self b];
rc_items : exists done, b_items b = done ++ its /\ length done = i;
rc_ne : its <> [];
rc_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
rc_len : zlen t < 100000;
rc_cregs : common_regs regs;
rc_lregs : loop_regs regs;
rc_bregs : batch_regs regs b;
rc_ra : getr regs 1 = w64 0x334f8;
rc_a0 : getr regs 10 = w64 (sp1 + 8);
rc_a1 : forall k ks, its = k :: ks -> getr regs 11 = w64 (hdra k);
rc_s7 : getr regs 23 = w64 (SB + b_self b + 152 + 8 * Z.of_nat i);
rc_s9 : getr regs 25 = w64 (16 + Z.of_nat i);
rc_frame : frame_cells W mem;
rc_tmp : tmp_cells W mem t lz qb;
rc_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
Record rst (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
r_acc : acc X W mem md;
r_rix : RIx U 0 0 0 X its t [b_self b];
r_items : exists done, b_items b = done ++ its /\ length done = i;
r_i : (1 <= i)%nat;
r_blen : (1 <= length (b_items b) <= Z.to_nat kBatchSlots)%nat;
r_len : zlen t < 100000;
r_cregs : common_regs regs;
r_lregs : loop_regs regs;
r_bregs : batch_regs regs b;
r_s7 : getr regs 23 = w64 (SB + b_self b + 144 + 8 * Z.of_nat i);
r_s9 : getr regs 25 = w64 (15 + Z.of_nat i);
r_frame : frame_cells W mem;
r_tmp : tmp_cells W mem t lz qb;
r_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells (b :: t))
}.
Record cdst (X : astate) (b : batch) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
cd_acc : acc X W mem md;
cd_rix : RIx U 0 0 0 X [] t [b_self b];
cd_len : zlen t < 100000;
cd_cregs : common_regs regs;
cd_lregs : loop_regs regs;
cd_ra : getr regs 1 = w64 0x33530;
cd_a0 : getr regs 10 = w64 (T + t_cache);
cd_a1 : getr regs 11 = w64 A_ALLOCATOR;
cd_a2 : getr regs 12 = w64 kBatchClass;
cd_a3 : getr regs 13 = w64 (SB + b_self b);
cd_frame : frame_cells W mem;
cd_tmp : tmp_cells W mem t lz qb;
cd_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Record qst (X : astate) (t : list batch) (lz qb : Z)
(W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop := {
q_acc : acc X W mem md;
q_rix : RIx U 0 0 0 X [] t [];
q_len : zlen t < 100000;
q_cregs : common_regs regs;
q_lregs : loop_regs regs;
q_frame : frame_cells W mem;
q_tmp : tmp_cells W mem t lz qb;
q_cells : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (batch_cells t)
}.
Definition OST (X : astate) (rest : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x334ac regs mem md /\ ost X rest lz qb W regs mem md.
Definition RCST (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_RChunk regs mem md /\ rcst X b t its i lz qb W regs mem md.
Definition RST (X : astate) (b : batch) (t : list batch) (its : list chunk) (i : nat) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x334f8 regs mem md /\ rst X b t its i lz qb W regs mem md.
Definition CDST (X : astate) (b : batch) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs A_CDealloc regs mem md /\ cdst X b t lz qb W regs mem md.
Definition QST (X : astate) (t : list batch) (W : world tfibsegs) (c : config) : Prop :=
exists lz qb regs mem md, c = cfg_at tfibsegs 0x33530 regs mem md /\ qst X t lz qb W regs mem md.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = zlen l + 1.
Proof. intros A x l. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros A l1 l2. unfold zlen. rewrite length_app. lia. Qed.
Lemma SY_not_owned : forall X W mem md a, AR tfibsegs B ly X W mem md ->
ly_stk_lo ly + DRSTACK <= sp0 -> sp0 + 32 <= ly_stk_hi ly -> SY a -> ~ aowned B ly X a.
Proof. intros X W mem md a HA H1 H2 Ha. apply (AR_stack_law_ok tfibsegs B ly X W mem md a HA). unfold SY in Ha. lia. Qed.
Lemma val_mem_keep : forall (W W' : world tfibsegs) mem mem' a (n : nat) v,
(forall a', a <= a' < a + Z.of_nat n -> aview tfibsegs (w_H W') mem' a' = aview tfibsegs (w_H W) mem a') ->
val_mem tfibsegs (mrestrict (w_H W) mem) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem') a n v.
Proof. intros W W' mem mem' a n v AG Hv. eapply val_mem_aview_xfer; [|exact Hv]. intros k Hk. apply AG. lia. Qed.
Lemma frame_cells_keep : forall (W W' : world tfibsegs) mem mem',
(forall a, sp1 <= a < sp0 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
frame_cells W mem -> frame_cells W' mem'.
Proof.
intros W W' mem mem' AG [CB SV]. split.
- eapply val_mem_keep; [|exact CB]. intros a' Ha'. apply AG. unfold sp1, YFRAME in *. cbn in Ha'. lia.
- intros k r Hk. pose proof (SV k r Hk) as V. eapply val_mem_keep; [|exact V]. intros a' Ha'. apply AG.
assert (K : (k < 11)%nat).
{ change 11%nat with (length AFh9.SAVED). apply (proj1 (nth_error_Some _ _)). rewrite Hk. discriminate. }
unfold sp1, sp0, YFRAME in *. cbn [Z.of_nat] in Ha'. lia.
Qed.
Lemma tmp_cells_keep : forall (W W' : world tfibsegs) mem mem' rest lz qb,
(forall a, sp0 <= a < sp0 + 32 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
tmp_cells W mem rest lz qb -> tmp_cells W' mem' rest lz qb.
Proof.
intros W W' mem mem' rest lz qb AG (V0 & V8 & V16 & V24 & R1 & R2). unfold tmp_cells. cbv zeta.
split; [|split; [|split; [|split; [|split; [exact R1 | exact R2]]]]]; (eapply val_mem_keep; [|eassumption]); intros a' Ha'; apply AG; cbn in Ha'; lia.
Qed.
End e.
End d.
