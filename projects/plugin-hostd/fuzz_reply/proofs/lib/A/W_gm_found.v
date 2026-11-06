(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: one cut lemma of fuzz_reply's gesture_model ASan walk (lane W4,
   sub-lane W4Gesture.WalkGestureModel), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v.
   gm_found walks 0x85c58 .. 0x85d4b: the byte after the LAST space of the line has been found, and the
   function decides between "begin" (list_push), "end" of a held key (list_drop) and nothing (return).
   The entry pc is A_gm_found = A_gesture_model + 0xbc; the premises are gesture_model's own, plus the
   machine state its prefix leaves and the two model facts the prefix has established.
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record)): Section c proves pb_gm_found_x over a generic
   allocator relation ARx (Section hypotheses LAWS HP0 TL HG MTL ABCMP LFIND LPUSH LDROP HLITG HLITB HLITE, the callees
   at their _x specs); Section r re-derives gm_found, statement unchanged, at ARx := W_journal_x.ARi0. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
(* C3: lp_spec's room is the peak of list_push's trace; lp_tr_peak_le turns gm_spec's sum into it *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_tr_peak.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_contract_xR W_contract_xR_g3 W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The model's side: lib/Prog/RelayModel.v:239-277 (gesture, upd), read the way gesture_model's code reads a line.
   Copied verbatim from A/W_gesture_model.v (W4Gesture.WalkGestureModel owns that file). *)
Module GM.
Import RelayModel.
Lemma lsf_none : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = None.
Proof.
induction l as [|b l IH]; intros i H; [reflexivity|].
cbn [last_space_from]. rewrite IH by (intros k Hk; apply (H (Datatypes.S k)); cbn; lia).
destruct (Z.eqb_spec b SPACE) as [E|E]; [exfalso; apply (H 0%nat); [cbn; lia | exact E] | reflexivity].
Qed.
Lemma lsf : forall l i j, (j < length l)%nat -> nth j l 0 = SPACE ->
(forall k, (j < k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = Some (i + j)%nat.
Proof.
induction l as [|b l IH]; intros i j Hj HS HN; [cbn in Hj; lia|].
cbn [last_space_from]. destruct j as [|j].
- rewrite lsf_none by (intros k Hk; apply (HN (Datatypes.S k)); cbn; lia).
cbn in HS. rewrite HS. cbn. f_equal. lia.
- rewrite (IH (Datatypes.S i) j) by (cbn in *; first [lia | exact HS | intros k Hk; apply (HN (Datatypes.S k)); lia]).
f_equal. lia.
Qed.
Lemma eqb_true : forall a b, list_eqb a b = true <-> a = b.
Proof. intros a b. unfold list_eqb. destruct (list_eq_dec Z.eq_dec a b); split; intros H; congruence. Qed.
Lemma eqb_len : forall a b, length a <> length b -> list_eqb a b = false.
Proof. intros a b H. destruct (list_eqb a b) eqn:E; [|reflexivity]. apply eqb_true in E. subst. contradiction. Qed.
Lemma short : forall l, (length l <= 13)%nat -> gesture l = None.
Proof. intros l H. unfold gesture. rewrite (proj2 (Nat.ltb_ge 13 (length l)) H), !andb_false_r. reflexivity. Qed.
Lemma nok : forall l, firstn 13 l <> K_GESTURE -> gesture l = None.
Proof.
intros l H. unfold gesture. destruct (list_eqb (firstn 13 l) K_GESTURE) eqn:E; [|reflexivity].
exfalso. apply H. apply eqb_true. exact E.
Qed.
Lemma nosp : forall l, nth 13 l 0 <> SPACE -> gesture l = None.
Proof. intros l H. unfold gesture. rewrite (proj2 (Z.eqb_neq _ _) H), andb_false_r. cbn [andb]. reflexivity. Qed.
Lemma at_j : forall l j, (13 < length l)%nat -> firstn 13 l = K_GESTURE -> nth 13 l 0 = SPACE ->
last_space_from 0 l = Some j ->
gesture l = if Nat.ltb 13 j then
if list_eqb (skipn (Datatypes.S j) l) W_BEGIN then Some (GBegin, firstn j l)
else if list_eqb (skipn (Datatypes.S j) l) W_END then Some (GEnd, firstn j l) else None
else None.
Proof.
intros l j H1 H2 H3 H4. unfold gesture.
rewrite (proj2 (eqb_true _ _) H2), (proj2 (Z.eqb_eq _ _) H3), (proj2 (Nat.ltb_lt _ _) H1), H4.
reflexivity.
Qed.
Lemma upd_none : forall G l, gesture l = None -> upd G l = G.
Proof. intros G l H. unfold upd. rewrite H. reflexivity. Qed.
Lemma upd_begin_in : forall G l x, gesture l = Some (GBegin, x) -> In x G -> upd G l = G.
Proof.
intros G l x H I. unfold upd. rewrite H.
replace (existsb (list_eqb x) G) with true; [reflexivity|].
symmetry. apply existsb_exists. exists x. split; [exact I | apply eqb_true; reflexivity].
Qed.
Lemma filter_out : forall x G, ~ In x G -> List.filter (fun y => negb (list_eqb x y)) G = G.
Proof.
intros x G. induction G as [|y G IH]; intros N; [reflexivity|].
cbn [List.filter]. destruct (list_eqb x y) eqn:E.
- exfalso. apply eqb_true in E. subst. apply N. left. reflexivity.
- cbn [negb]. f_equal. apply IH. intros I. apply N. right. exact I.
Qed.
Lemma upd_end_out : forall G l x, gesture l = Some (GEnd, x) -> ~ In x G -> upd G l = G.
Proof. intros G l x H N. unfold upd. rewrite H. exact (filter_out x G N). Qed.
Lemma upd_begin_new : forall G l x, gesture l = Some (GBegin, x) -> ~ In x G -> upd G l = G ++ [x].
Proof.
intros G l x H N. unfold upd. rewrite H.
replace (existsb (list_eqb x) G) with false; [reflexivity|].
symmetry. apply not_true_iff_false. intros E. apply existsb_exists in E as (y & Iy & Ey).
apply eqb_true in Ey. subst. exact (N Iy).
Qed.
Lemma filter_nth : forall (G : list (list Z)) i, List.NoDup G -> (i < length G)%nat ->
List.filter (fun y => negb (list_eqb (nth i G []) y)) G = firstn i G ++ skipn (Datatypes.S i) G.
Proof.
induction G as [|y G IH]; intros i ND Hi; [cbn in Hi; lia|].
inversion ND as [|y' G' Ny NDG]; subst.
destruct i as [|i].
- cbn [nth List.filter firstn skipn app]. rewrite (proj2 (eqb_true y y) eq_refl). cbn [negb].
apply filter_out. exact Ny.
- cbn [nth List.filter firstn skipn app].
assert (Ny' : nth i G [] <> y).
{ intros E. apply Ny. rewrite <- E. apply nth_In. cbn in Hi. lia. }
destruct (list_eqb (nth i G []) y) eqn:E; [apply eqb_true in E; exfalso; exact (Ny' E)|].
cbn [negb]. f_equal. apply IH; [exact NDG | cbn in Hi; lia].
Qed.
Lemma upd_end_at : forall G l i, gesture l = Some (GEnd, nth i G []) -> List.NoDup G -> (i < length G)%nat ->
upd G l = firstn i G ++ skipn (Datatypes.S i) G.
Proof. intros G l i H ND Hi. unfold upd. rewrite H. exact (filter_nth G i ND Hi). Qed.
End GM.

(* ---- plain list facts the walk needs. ---- *)
Lemma gfL_eq_of_nth : forall (l m : list Z), length l = length m ->
(forall i, (i < length m)%nat -> nth i l 0 = nth i m 0) -> l = m.
Proof.
induction l as [|a l IH]; intros m Hl Hn; destruct m as [|b m]; try (cbn in Hl; lia); [reflexivity|].
f_equal; [exact (Hn 0%nat ltac:(cbn; lia))|].
apply IH; [cbn in Hl; lia | intros i Hi; exact (Hn (Datatypes.S i) ltac:(cbn; lia))].
Qed.
Lemma gfL_nth_skipn : forall (l : list Z) m n, nth n (skipn m l) 0 = nth (m + n) l 0.
Proof.
intros l m. revert l. induction m as [|m IH]; intros l n; [reflexivity|].
destruct l as [|a l]; cbn [skipn]; [destruct n; reflexivity | apply IH].
Qed.
Lemma gfL_skipn_eq : forall (l m : list Z) n, (n + length m = length l)%nat ->
(forall i, (i < length m)%nat -> nth (n + i) l 0 = nth i m 0) -> skipn n l = m.
Proof.
intros l m n Hlen Hn. apply gfL_eq_of_nth; [rewrite length_skipn; lia|].
intros i Hi. rewrite gfL_nth_skipn. exact (Hn i Hi).
Qed.
Lemma gfL_nth_firstn : forall n (l : list Z) i, (i < n)%nat -> nth i (firstn n l) 0 = nth i l 0.
Proof.
induction n as [|n IH]; intros l i Hi; [lia|].
destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
destruct i as [|i]; cbn [nth]; [reflexivity | apply IH; lia].
Qed.
Lemma gfL_split_nth : forall (l : list (list Z)) i, (i < length l)%nat ->
l = firstn i l ++ nth i l [] :: skipn (Datatypes.S i) l.
Proof.
induction l as [|a l IH]; intros i Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|].
cbn [firstn nth skipn app]. f_equal. apply IH. cbn in Hi. lia.
Qed.
Lemma gfL_in_nth : forall (l : list (list Z)) x, In x l -> exists i, (i < length l)%nat /\ nth i l [] = x.
Proof.
induction l as [|a l IH]; intros x Hx; [destruct Hx|].
destruct Hx as [<- | Hx]; [exists 0%nat; split; [cbn; lia | reflexivity]|].
destruct (IH x Hx) as (i & Hi & Hn). exists (Datatypes.S i). split; [cbn; lia | exact Hn].
Qed.
(* bzs = map bz is injective: bz b = bv_unsigned b *)
Lemma gfL_bz_inj : forall a b : byte, bz a = bz b -> a = b.
Proof. intros a b H. apply bv_eq. exact H. Qed.
Lemma gfL_bzs_inj : forall x y : list byte, bzs x = bzs y -> x = y.
Proof.
induction x as [|a x IH]; intros [|b y] H; cbn in H; try discriminate; [reflexivity|].
injection H as H1 H2. f_equal; [exact (gfL_bz_inj a b H1) | exact (IH y H2)].
Qed.
Lemma gfL_bzs_len : forall x : list byte, length (bzs x) = length x.
Proof. intros x. unfold bzs. apply length_map. Qed.
Lemma gfL_bzs_firstn : forall n (x : list byte), bzs (firstn n x) = firstn n (bzs x).
Proof.
induction n as [|n IH]; intros [|a x]; try reflexivity.
unfold bzs in *. cbn [firstn map]. f_equal. apply IH.
Qed.
(* 64-bit add and subtract of two known words, as the symbolic engine leaves them *)
Lemma gfL_alu_add : forall x y, alu64 ALU_ADD (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x + y).
Proof.
intros x y. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. symmetry. apply Zplus_mod.
Qed.
Lemma gfL_alu_sub : forall x y, alu64 ALU_SUB (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x - y).
Proof.
intros x y. rewrite zalu64_sound. unfold zalu64. cbn [zalu_raw].
rewrite Z_to_bv64_canon. apply Z_to_bv64_eq_mod. unfold zcanon, M64. symmetry. apply Zminus_mod.
Qed.
(* the U value of the engine's two-atom sum and of a negation *)
Lemma gfL_U_add : forall E n m x y, ew E n = Z_to_bv 64 x -> ew E m = Z_to_bv 64 y ->
0 <= x + y < 2 ^ 64 -> U E (SAlu ALU_ADD (SOff n 0) (SOff m 0)) = x + y.
Proof.
intros E n m x y Hn Hm Hr. unfold U. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, Hn, Hm, gfL_alu_add.
apply unsigned_lit_small. exact Hr.
Qed.
Lemma gfL_U_neg : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= - x < 2 ^ 64 ->
U E (SAlu ALU_SUB (SLit 0) (SOff n 0)) = - x.
Proof.
intros E n x Hn Hr. unfold U. cbn [sv_denot].
rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned, Hn.
change (Z_to_bv 64 0) with (Z_to_bv 64 0). rewrite gfL_alu_sub.
rewrite Z.sub_0_l in *. apply unsigned_lit_small. exact Hr.
Qed.
(* a run keeps every byte it does not hide: mem_grows of the restricted memories carries apresent *)
Lemma gfL_pres_of_grows : forall (Hb : word -> bool) (m m' : word -> option byte) a,
mem_grows (mrestrict Hb m) (mrestrict Hb m') -> apresent Hb m a -> apresent Hb m' a.
Proof.
intros Hb m m' a HGr [Hh [b Hb']]. split; [exact Hh|].
assert (Hm : mrestrict Hb m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb'; discriminate).
pose proof (HGr (Z_to_bv 64 a) Hm) as Hm'. unfold mrestrict in Hm'. rewrite Hh in Hm'.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
cbn in Hm'. exfalso. apply Hm'. reflexivity.
Qed.
(* gesture_model's epilogue restores ra, s0..s3 and sp; x20..x27, gp and tp it never writes. *)
Lemma gfL_pres : forall (regs regsc regs' : bvmap 5 word),
spZ regsc = spZ regs - 48 ->
(forall r, 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall r, 20 <= r <= 27 -> getr regs' (Z_to_bv 5 r) = getr regsc (Z_to_bv 5 r)) ->
getr regs' 2 = Z_to_bv 64 (bv_unsigned (getr regsc 2) + 48) ->
getr regs' 3 = getr regsc 3 -> getr regs' 4 = getr regsc 4 ->
getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
aregs_preserved regs regs'.
Proof.
intros regs regsc regs' Hsp HC2027 H3c H4c H2027 P2 P3 P4 P8 P9 P18 P19 r Hr.
assert (Hcase : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ (20 <= r <= 27))
by (unfold acallee_saved in Hr; lia).
destruct Hcase as [->|[->|[->|[->|[->|[->|[->|Hr2]]]]]]].
- replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity).
  rewrite P2. unfold spZ in Hsp. rewrite Hsp.
  replace (bv_unsigned (getr regs 2) - 48 + 48) with (bv_unsigned (getr regs 2)) by lia.
  apply Z_to_bv_bv_unsigned.
- replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P3. exact H3c.
- replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P4. exact H4c.
- replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). exact P8.
- replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). exact P9.
- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). exact P18.
- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). exact P19.
- rewrite (H2027 r Hr2). exact (HC2027 r Hr2).
Qed.
(* a record of the vector is 16 bytes (two little-endian words), so the vector holds AREC * cap bytes *)
Lemma gfL_text_rec_len : forall r, length (HarnessRep.text_rec r) = 16%nat.
Proof. intros r. unfold HarnessRep.text_rec. rewrite length_app. cbn. reflexivity. Qed.
Lemma gfL_concat_text_len : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH, gfL_text_rec_len. lia.
Qed.
Lemma vec_len : forall l,
Z.of_nat (length (HarnessRep.hl_junk l)) = AREC * (HarnessRep.hl_cap l - HarnessRep.hl_n l) ->
Z.of_nat (length (bzs (concat (map HarnessRep.text_rec (HarnessRep.hl_recs l)) ++ HarnessRep.hl_junk l)))
= AREC * HarnessRep.hl_cap l.
Proof.
intros l HJ. unfold bzs. rewrite length_map, length_app, gfL_concat_text_len.
unfold HarnessRep.hl_n in HJ. unfold AREC in *. lia.
Qed.
Lemma gfL_texts_nth : forall (l : hlist) i, (i < length (hl_recs l))%nat ->
nth i (texts l) [] = bzs (snd (nth i (hl_recs l) (0, []))).
Proof.
intros l i Hi. unfold texts.
rewrite (nth_indep _ [] (bzs (snd (0, [])))) by (rewrite length_map; exact Hi).
apply (map_nth (fun r => bzs (snd r))).
Qed.
Lemma gfL_texts_len : forall l : hlist, length (texts l) = length (hl_recs l).
Proof. intros l. unfold texts. apply length_map. Qed.
Lemma gfL_unsigned_mod : forall z, bv_unsigned (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof.
intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). reflexivity.
Qed.
Lemma gfL_bv_mod : forall a b, a mod 2 ^ 64 = b mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b.
Proof. intros a b Hm. apply bv_eq. rewrite !gfL_unsigned_mod. exact Hm. Qed.
(* ---- list facts of the three tail arms: list_find's answer, list_drop's and list_push's lists ---- *)
Lemma gfL_nth_firstnA : forall {A} n (l : list A) i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A n. induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
destruct i as [|i]; cbn [nth]; [reflexivity | apply IH; lia].
Qed.
Lemma gfL_in_firstn : forall {A} n (l : list A) x, In x (firstn n l) -> In x l.
Proof. intros A n l x Hx. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact Hx. Qed.
Lemma gfL_in_skipn : forall {A} n (l : list A) x, In x (skipn n l) -> In x l.
Proof. intros A n l x Hx. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact Hx. Qed.
Lemma gfL_split_nthA : forall {A} (l : list A) i d, (i < length l)%nat ->
l = firstn i l ++ nth i l d :: skipn (Datatypes.S i) l.
Proof.
intros A l. induction l as [|a l IH]; intros i d Hi; [cbn in Hi; lia|].
destruct i as [|i]; [reflexivity|].
cbn [firstn nth skipn app]. f_equal. apply IH. cbn in Hi. lia.
Qed.
Lemma gfL_nodup_drop : forall {A} (l : list A) i, List.NoDup l -> List.NoDup (firstn i l ++ skipn (Datatypes.S i) l).
Proof.
intros A l. induction l as [|a l IH]; intros i ND; [destruct i; cbn; constructor|].
inversion ND as [|a' l' Na NDl]; subst.
destruct i as [|i]; cbn [firstn skipn app]; [exact NDl|].
constructor; [|exact (IH i NDl)].
intros Hin. apply Na. apply in_app_or in Hin as [Hin|Hin];
[exact (gfL_in_firstn _ _ _ Hin) | exact (gfL_in_skipn _ _ _ Hin)].
Qed.
Lemma gfL_bzs_nth : forall (x : list byte) n, nth n (bzs x) 0 = bv_unsigned (nth n x (Z_to_bv 8 0)).
Proof.
intros x n. unfold bzs. change (bv_unsigned (nth n x (Z_to_bv 8 0))) with (bz (nth n x (Z_to_bv 8 0))).
rewrite <- (map_nth bz x (Z_to_bv 8 0) n). destruct (Nat.lt_ge_cases n (length x)) as [Hl|Hl].
- apply nth_indep. rewrite length_map. exact Hl.
- rewrite !nth_overflow by (rewrite length_map; exact Hl). vm_compute. reflexivity.
Qed.
Lemma gfL_texts_drop : forall (l : hlist) i,
texts (ldrop_list l i) = firstn i (texts l) ++ skipn (Datatypes.S i) (texts l).
Proof. intros l i. unfold texts, ldrop_list. cbn [hl_recs]. rewrite map_app, firstn_map, skipn_map. reflexivity. Qed.
Lemma gfL_texts_push : forall (l l' : hlist) d x, hl_recs l' = hl_recs l ++ [(d, x)] -> texts l' = texts l ++ [bzs x].
Proof. intros l l' d x Hr. unfold texts. rewrite Hr, map_app. reflexivity. Qed.
Lemma gfL_notin_texts : forall (l : hlist) (x : list byte),
(forall kk, (kk < length (hl_recs l))%nat -> snd (nth kk (hl_recs l) (0, [])) <> x) -> ~ In (bzs x) (texts l).
Proof.
intros l x Hn Hin. destruct (gfL_in_nth _ _ Hin) as (i & Hi & Hni).
rewrite gfL_texts_len in Hi. rewrite gfL_texts_nth in Hni by exact Hi.
apply (Hn i Hi). apply gfL_bzs_inj. exact Hni.
Qed.
Lemma gfL_match_nth : forall (l : hlist) x j, lfind_match l x j ->
(j < length (texts l))%nat /\ nth j (texts l) [] = bzs x.
Proof.
intros l x j (Hj & Hs & _). rewrite gfL_texts_len. split; [exact Hj|].
rewrite gfL_texts_nth by exact Hj. rewrite Hs. reflexivity.
Qed.
Lemma gfL_perm_snoc : forall {A} (y : A) (V R rest : list A), Permutation (y :: V ++ R ++ rest) ((V ++ R ++ [y]) ++ rest).
Proof.
intros A y V R rest. rewrite <- !app_assoc. cbn [app].
rewrite (app_assoc V R rest), (app_assoc V R (y :: rest)). apply Permutation_middle.
Qed.
Lemma gfL_perm_drop : forall {A} (x : A) (b1 b2 V F K rest : list A),
Permutation (b1 ++ x :: b2) ((V ++ F ++ x :: K) ++ rest) -> Permutation (b1 ++ b2) ((V ++ F ++ K) ++ rest).
Proof.
intros A x b1 b2 V F K rest HP. apply (Permutation_cons_inv (a := x)).
eapply perm_trans; [apply Permutation_middle|]. eapply perm_trans; [exact HP|].
rewrite <- !app_assoc. cbn [app].
rewrite (app_assoc V F (x :: K ++ rest)), (app_assoc V F (K ++ rest)).
apply Permutation_sym. apply Permutation_middle.
Qed.
(* the registers a callee keeps, read at their usual literals *)
Lemma gfL_prv : forall regs regs1, aregs_preserved regs regs1 ->
getr regs1 2 = getr regs 2 /\ getr regs1 3 = getr regs 3 /\ getr regs1 4 = getr regs 4 /\ getr regs1 8 = getr regs 8.
Proof.
intros regs regs1 HP.
repeat split; [replace (2%bv : bv 5) with (Z_to_bv 5 2) by (apply bv_eq; reflexivity)
| replace (3%bv : bv 5) with (Z_to_bv 5 3) by (apply bv_eq; reflexivity)
| replace (4%bv : bv 5) with (Z_to_bv 5 4) by (apply bv_eq; reflexivity)
| replace (8%bv : bv 5) with (Z_to_bv 5 8) by (apply bv_eq; reflexivity)]; apply HP; unfold acallee_saved; lia.
Qed.
(* a branch on an atom against x0, and list_find's two answers under blt / bge *)
Lemma gfL_bt_atom : forall c E n v, ew E n = v ->
branch_taken c (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = branch_taken c v (Z_to_bv 64 0).
Proof. intros c E n v Hv. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Hv. reflexivity. Qed.
Lemma gfL_blt_nat : forall j, 0 <= j < 2 ^ 63 -> branch_taken BC_LT (Z_to_bv 64 j) (Z_to_bv 64 0) = false.
Proof.
intros j Hj. rewrite YO0c.branch_lt, !unsigned_lit_small by lia. rewrite !YO0b.s64_small by lia.
apply Z.ltb_ge. lia.
Qed.
Lemma gfL_bge_nat : forall j, 0 <= j < 2 ^ 63 -> branch_taken BC_GE (Z_to_bv 64 j) (Z_to_bv 64 0) = true.
Proof.
intros j Hj. rewrite YO0c.branch_ge, !unsigned_lit_small by lia. rewrite !YO0b.s64_small by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma gfL_blt_m1 : branch_taken BC_LT (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gfL_bge_m1 : branch_taken BC_GE (Z_to_bv 64 (-1)) (Z_to_bv 64 0) = false.
Proof. vm_compute. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Definition A_gesture_model : Z := AF_fr_gesture_model.
Definition A_gesture_modelP : Z := BASE + A_gesture_model.
(* the scan loop's head (0x85c18), the byte after the last space (0x85c58), the shared epilogue (0x85ce8) *)
Definition A_gm_loop : Z := A_gesture_model + 0x7c.
Definition A_gm_found : Z := A_gesture_model + 0xbc.
Definition A_gm_ret : Z := A_gesture_model + 0x14c.
(* the registers a run never wrote are still their entry atoms (aregs_preserved_of_st_ok, by register list) *)
Lemma gf_reg_kept : forall E ss (ms : machine_state) (regs0 : bvmap 5 word) extra (Hb : word -> bool) (L : list (bv 5)),
st_ok_pi SEGS VAL E ss (restrict Hb ms) -> env_agree 32 (Ereg regs0 extra) E ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) L = true ->
forall r : bv 5, In r L -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms regs0 extra Hb L HS HA Hcs r Hin.
destruct HA as [HA _].
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_pi_restrict_reg Hb E ss ms r HS), Hq. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite HA by (pose proof (u5_range r); lia).
rewrite ew_Ereg_reg, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition GF_CS : list (bv 5) := [3; 4; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma gf_cs_in : forall r : Z, 20 <= r <= 27 -> In (Z_to_bv 5 r : bv 5) GF_CS.
Proof.
intros r Hr. unfold GF_CS. cbn [In].
assert (Hc : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
subst. repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
(* ---- gesture_model's charge (W_contract.v gm_cost, the trace's: Prog/HarnessTr.v gesture_model_tr), read by the
   line's gesture and the held texts, at any meter M: list_push's on a begin of a key not held, list_drop's one free on
   an end of a held key, nothing else. ---- *)
Lemma gf_ex_in : forall (x : list Z) G, In x G -> existsb (RelayModel.list_eqb x) G = true.
Proof. intros x G I. apply existsb_exists. exists x. split; [exact I | apply GM.eqb_true; reflexivity]. Qed.
Lemma gf_ex_out : forall (x : list Z) G, ~ In x G -> existsb (RelayModel.list_eqb x) G = false.
Proof.
intros x G N. apply not_true_iff_false. intros E. apply existsb_exists in E as (y & Iy & Ey).
apply GM.eqb_true in Ey. subst. exact (N Iy).
Qed.
Lemma gf_cost_none : forall M (H : hlist) ln, RelayModel.gesture (bzs ln) = None -> gm_cost M H ln = 0.
Proof. intros M H ln Hg. unfold gm_cost. rewrite Hg. reflexivity. Qed.
Lemma gf_cost_begin_in : forall M (H : hlist) ln x,
RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, x) -> In x (texts H) -> gm_cost M H ln = 0.
Proof. intros M H ln x Hg I. unfold gm_cost. rewrite Hg, (gf_ex_in x _ I). reflexivity. Qed.
Lemma gf_cost_begin_new : forall M (H : hlist) ln x,
RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, x) -> ~ In x (texts H) ->
gm_cost M H ln = lp_cost M H (Z.of_nat (length x)).
Proof. intros M H ln x Hg N. unfold gm_cost. rewrite Hg, (gf_ex_out x _ N). reflexivity. Qed.
Lemma gf_cost_end_in : forall M (H : hlist) ln x,
RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, x) -> In x (texts H) -> gm_cost M H ln = mo_free M.
Proof. intros M H ln x Hg I. unfold gm_cost. rewrite Hg, (gf_ex_in x _ I). reflexivity. Qed.
Lemma gf_cost_end_out : forall M (H : hlist) ln x,
RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, x) -> ~ In x (texts H) -> gm_cost M H ln = 0.
Proof. intros M H ln x Hg N. unfold gm_cost. rewrite Hg, (gf_ex_out x _ N). reflexivity. Qed.
(* ---- THE GENERIC WALK (route (b), step 3): gm_found over any allocator relation ARx with its laws.  The Section
   hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation) and HP0 (the unit's hidden-head set is
   empty in every ARx state, a Theorem Labs lane's ruling: W_journal_x Section hp0's range_addressable_of_block_hp0_x /
   shadow_hull_vis_of_block_hp0_x).  The callees are their _x specs at the same PST / ARx. ---- *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
(* the room round (W_contract_x.v Section w4): the room parameter, after MT as the kit's spec Sections take it *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
(* the three literals are addressable with a visible shadow hull in every ARx state (W_shadow_pin.v ashp over ARx,
   W_contract_x.ashp_x; at the AR instance W_shadow_pin_fr.v ashp_gesture_13_fr / ashp_begin_5_fr / ashp_end_3_fr). *)
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
(* ---- the room round at gesture_model's call sites.  gm_cost MT_rk (W_contract.v gm_cost; MT_rk counts one per
   allocator call) is list_push's count at a begin of a key not held and list_drop's one free at an end of a held key,
   0 elsewhere; an arm that makes no allocator call has room 0 there, and gm_rm_down drops it to kr (roomp's rp_RMM).
   ---- *)
Lemma gm_rm_down : forall S k kr, rp_RM RP S (k + kr) -> rp_RM RP S kr.
Proof. intros S k kr HR. exact (RMM_of RP S kr (k + kr) ltac:(lia) HR). Qed.
(* list_push's budget at the begin arm: the whole budget *)
Lemma gm_rm_push : forall S (H : hlist) ln x kr,
RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, x) -> ~ In x (texts H) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> rp_RM RP S (Z.to_nat (lp_cost MT_rk H (Z.of_nat (length x))) + kr).
Proof. intros S H ln x kr Hg N HR. rewrite (gf_cost_begin_new MT_rk H ln x Hg N) in HR. exact HR. Qed.
(* list_drop's budget at the end arm: the whole budget *)
Lemma gm_rm_drop : forall S (H : hlist) ln x kr,
RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, x) -> In x (texts H) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> rp_RM RP S (Z.to_nat (mo_free MT_rk) + kr).
Proof. intros S H ln x kr Hg I HR. rewrite (gf_cost_end_in MT_rk H ln x Hg I) in HR. exact HR. Qed.
(* list_push's count premise at the key (any length m) from gesture_model's size-independent peak gm_pk *)
Lemma gm_cnt_push : forall (H : hlist) m l, cnt_ok_pk RP (gm_pk H) l -> cnt_ok_pk RP (lp_peak H m) l.
Proof.
intros H m l Hc. apply (cnt_ok_pk_mono RP (gm_pk H) _ l l); [|exact Hc].
intros P. unfold gm_pk, lp_peak. cbv beta. destruct (P (lp_vbytes H) && lp_grow H), (P (m + 1)%Z); lia.
Qed.
(* list_drop's count premise (ldrop_pk) from any peak *)
Lemma gm_cnt_drop : forall pk l, cnt_ok_pk RP pk l -> cnt_ok_pk RP ldrop_pk l.
Proof. intros pk l Hc. apply (cnt_ok_pk_mono RP pk _ l l); [|exact Hc]. intros P. unfold ldrop_pk. cbv beta. lia. Qed.

Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx G 0 []).

(* The symbolic state at 0x85c58.  Atoms 0..31 are gesture_model's registers THERE (sp = spZ regs - 48,
   s0 = LINE, s1 = HA, s2 = len, s3 = SB, a0 = j); atoms 32..37 are SB and the five words the prologue
   saved, which the epilogue loads back, so the frame region is read-only with five known chunks. *)
Definition Bxf : sv := SOff 32 0.
Definition gf_frame : YP09.region := YP09.mkRegion (Some 2%nat) 8 48 0 0
[YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
 YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
 YP09.mkChunk 40 (CVal 8 (SOff 37 0))].
Definition gf_regions : smem := [ gf_frame ].
Definition gf_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_gf : sstate := mkSS A_gm_found sr_atoms gf_regions None gf_facts.
Definition gf_SH : list shent := [].
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gf_extra (regs : bvmap 5 word) : list word :=
[Z_to_bv 64 SB; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 1].
(* the one region writes nothing, so every address is outside its writable window *)
Ltac gf_outw :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gf gf_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val gf_frame] in Hr; lia | ]);
destruct Hin.

Lemma gf_entry : forall W (regs regsc : bvmap 5 word) memc ly,
astk_ok GM_STK ly (spZ regs) -> spZ regsc = spZ regs - GM_FRAME ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (gf_extra regs))) ss_gf
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxf gf_SH (Eimg (Ereg regsc (gf_extra regs))) (mrestrict (w_H W) memc).
Proof.
intros W regs regsc memc ly Hstk Hsp VRA V8 V9 V18 V19.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity.
assert (HR : 2 ^ 46 <= spZ regs - 48 <= 2 ^ 47 /\ (spZ regs - 48) mod 16 = 0).
{ split; [unfold GM_STK, GM_FRAME, LP_STK, ASTACK, alloc_ceiling in *; lia|].
  rewrite Zminus_mod, Hal16. reflexivity. }
destruct HR as [HR1 HR2].
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (gf_extra regs))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regsc 2)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite E2; unfold spZ in Hsp |- *; unfold GM_FRAME in Hsp; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = getr regs 8)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = getr regs 9)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = getr regs 18)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew E 36 = getr regs 19)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 4)).
assert (E37 : ew E 37 = getr regs 1)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 5)).
assert (BVR : forall w : word, 0 <= bv_unsigned w < 2 ^ 64)
by (intros w; pose proof (bv_unsigned_in_range 64 w) as Hw; change (bv_modulus 64) with (2 ^ 64) in Hw; lia).
split.
- unfold ss_gf. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gf_regions, gf_frame; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat apply Forall_cons; try apply Forall_nil.
* apply (chunk_ok_val SEGS E _ (spZ regs - 48) 8 8 (SOff 36 0) (bv_unsigned (getr regs 19)));
[cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (BVR (getr regs 19)); cbn; lia | cbn; lia |].
replace (spZ regs - 48 + 8) with (spZ regs - 40) by lia. exact V19.
* apply (chunk_ok_val SEGS E _ (spZ regs - 48) 16 8 (SOff 35 0) (bv_unsigned (getr regs 18)));
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (BVR (getr regs 18)); cbn; lia | cbn; lia |].
replace (spZ regs - 48 + 16) with (spZ regs - 32) by lia. exact V18.
* apply (chunk_ok_val SEGS E _ (spZ regs - 48) 24 8 (SOff 34 0) (bv_unsigned (getr regs 9)));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (BVR (getr regs 9)); cbn; lia | cbn; lia |].
replace (spZ regs - 48 + 24) with (spZ regs - 24) by lia. exact V9.
* apply (chunk_ok_val SEGS E _ (spZ regs - 48) 32 8 (SOff 33 0) (bv_unsigned (getr regs 8)));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (BVR (getr regs 8)); cbn; lia | cbn; lia |].
replace (spZ regs - 48 + 32) with (spZ regs - 16) by lia. exact V8.
* apply (chunk_ok_val SEGS E _ (spZ regs - 48) 40 8 (SOff 37 0) (bv_unsigned (getr regs 1)));
[cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (BVR (getr regs 1)); cbn; lia | cbn; lia |].
replace (spZ regs - 48 + 40) with (spZ regs - 8) by lia. exact VRA.
+ apply pairwise_disjoint_of_extents. unfold gf_regions, gf_frame, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I | exact I]].
cbn [gf_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
- unfold sh_ok, gf_SH. constructor.
Qed.

(* What an environment of this walk keeps through every call: the image, the registers at 0x85c58 (atoms
   0..31) and the five saved words (atoms 33..37).  A call havocs atoms from 38 up only. *)
Definition gf_env (Ev : env) (regsc regs : bvmap 5 word) : Prop :=
img_env VAL A_LIM Ev /\ env_agree 32 (Ereg regsc (gf_extra regs)) Ev /\
ew Ev 33 = getr regs 8 /\ ew Ev 34 = getr regs 9 /\ ew Ev 35 = getr regs 18 /\
ew Ev 36 = getr regs 19 /\ ew Ev 37 = getr regs 1.
Lemma gf_env_havoc : forall Ev regsc regs k ws, gf_env Ev regsc regs -> (38 <= k)%nat ->
(k + length ws <= A_TEXT)%nat -> gf_env (havoc Ev k ws) regsc regs.
Proof.
intros Ev regsc regs k ws (HI & HA & H33 & H34 & H35 & H36 & H37) Hk Hw.
split; [apply img_env_havoc; [exact HI | exact Hw]|].
split; [apply env_agree_havoc_ge; [lia | exact HA]|].
rewrite !YN3v.ew_havoc_old by lia. repeat split; assumption.
Qed.
(* The epilogue (0x85ce8 .. 0x85cfc) leaves ra, s0..s3 at the saved words and sp at sp + 48; gp, tp and
   s4..s11 were never written: the registers at the ret (or at a tail call's target) are the caller's. *)
Definition gf_ret_sr : list (bv 5 * sv) :=
[(1%bv, SOff 37 0); (2%bv, SOff 2 48); (8%bv, SOff 33 0); (9%bv, SOff 34 0); (18%bv, SOff 35 0); (19%bv, SOff 36 0)].
Lemma gf_ret_regs : forall Ev ss ms (Hb : word -> bool) regsc regs,
st_ok_pi SEGS VAL Ev ss (restrict Hb ms) -> gf_env Ev regsc regs ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = getr regs 3 -> getr regsc 4 = getr regs 4 ->
(forall r, 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
forallb (fun p : bv 5 * sv => sv_eqb (sr_get (ss_regs ss) (fst p)) (snd p)) gf_ret_sr = true ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) GF_CS = true ->
aregs_preserved regs (ms_regs ms) /\ getr (ms_regs ms) 1 = getr regs 1.
Proof.
intros Ev ss ms Hb regsc regs HS (HI & HAE & H33 & H34 & H35 & H36 & H37) Hsp H3 H4 H2027 Hr Hcs.
assert (RG : forall (r : bv 5) e, In (r, e) gf_ret_sr -> getr (ms_regs ms) r = sv_denot Ev e).
{ intros r e Hin. pose proof (proj1 (forallb_forall _ _) Hr _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
  cbn [fst snd] in Hq. rewrite (st_ok_pi_restrict_reg Hb Ev ss ms r HS), Hq. reflexivity. }
assert (KC : forall r : bv 5, In r GF_CS -> getr (ms_regs ms) r = getr regsc r)
by (intros r Hin; exact (gf_reg_kept Ev ss ms regsc (gf_extra regs) Hb GF_CS HS HAE Hcs r Hin)).
assert (E2 : ew Ev 2 = getr regsc 2)
by (rewrite (proj1 HAE 2%nat ltac:(lia)); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
pose proof (RG 1%bv (SOff 37 0) ltac:(unfold gf_ret_sr; left; reflexivity)) as P1.
pose proof (RG 2%bv (SOff 2 48) ltac:(unfold gf_ret_sr; right; left; reflexivity)) as P2.
pose proof (RG 8%bv (SOff 33 0) ltac:(unfold gf_ret_sr; do 2 right; left; reflexivity)) as P8.
pose proof (RG 9%bv (SOff 34 0) ltac:(unfold gf_ret_sr; do 3 right; left; reflexivity)) as P9.
pose proof (RG 18%bv (SOff 35 0) ltac:(unfold gf_ret_sr; do 4 right; left; reflexivity)) as P18.
pose proof (RG 19%bv (SOff 36 0) ltac:(unfold gf_ret_sr; do 5 right; left; reflexivity)) as P19.
cbn [sv_denot] in P1, P2, P8, P9, P18, P19.
rewrite Z.add_0_r, Z_to_bv_bv_unsigned in P1, P8, P9, P18, P19.
split.
- apply (gfL_pres regs regsc (ms_regs ms)).
  + unfold GM_FRAME in Hsp. exact Hsp.
  + exact H2027.
  + exact H3.
  + exact H4.
  + intros r Hr'. apply KC. apply gf_cs_in. exact Hr'.
  + rewrite P2, E2. reflexivity.
  + apply KC. unfold GF_CS. left. reflexivity.
  + apply KC. unfold GF_CS. right. left. reflexivity.
  + rewrite P8, H33. reflexivity.
  + rewrite P9, H34. reflexivity.
  + rewrite P18, H35. reflexivity.
  + rewrite P19, H36. reflexivity.
- rewrite P1, H37. reflexivity.
Qed.

(* two live blocks of positive size at one address are one block (their extents are disjoint).  The ARx blocks law
   does not carry cgif's `0 <= n`, so the two sizes come as premises. *)
Lemma gf_same_base : forall ly S Hp W mem md p n m, ARx ly S Hp W mem md ->
In (p, n) (ablocks B ly S) -> In (p, m) (ablocks B ly S) -> 1 <= req_size n -> 1 <= req_size m -> n = m.
Proof.
intros ly S hp W mem md p n m HAR Hn Hm Hn1 Hm1.
destruct (alx_sep _ _ _ LAWS ly S hp W mem md HAR) as [Hpw _]. apply pairwise_app_l in Hpw as [Hpw _].
revert Hpw Hn Hm. induction (ablocks B ly S) as [|b l IH]; intros Hpw Hn Hm; [destruct Hn|].
cbn [map pairwise] in Hpw. destruct Hpw as [Hf Hpw]. rewrite Forall_forall in Hf.
destruct Hn as [Hn | Hn]; destruct Hm as [Hm | Hm].
- rewrite Hn in Hm. injection Hm as Hm. exact Hm.
- subst b. specialize (Hf (p, req_size m) (in_map (fun b => (fst b, req_size (snd b))) l (p, m) Hm)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
- subst b. specialize (Hf (p, req_size n) (in_map (fun b => (fst b, req_size (snd b))) l (p, n) Hn)).
  unfold zdisjoint in Hf. cbn [fst snd] in Hf. lia.
- exact (IH Hpw Hn Hm).
Qed.
Lemma gfL_blk_fp : forall bl b a, In b bl -> 0 <= snd b -> fst b <= a < fst b + snd b -> inFP (blk_FP bl) a.
Proof.
intros bl b a Hin Hn Ha. exists (fst b, fst b + req_size (snd b)). split.
- exact (in_map (fun b => (fst b, fst b + req_size (snd b))) bl b Hin).
- cbn [fst snd]. pose proof (req_size_pos (snd b) Hn). lia.
Qed.
Lemma gfL_blk_fp_r : forall bl b a, In b bl -> fst b <= a < fst b + req_size (snd b) -> inFP (blk_FP bl) a.
Proof.
intros bl b a Hin Ha. exists (fst b, fst b + req_size (snd b)). split; [|exact Ha].
exact (in_map (fun b => (fst b, fst b + req_size (snd b))) bl b Hin).
Qed.
(* the list, the ROM and the line survive every step that keeps the bytes below the stack window *)
Lemma gf_alist_kept : forall W ly S regs mem HA H mem1,
alist_at B ly S W mem (HA + 80) H true ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
alist_at B ly S W mem1 (HA + 80) H true.
Proof.
intros W ly S regs mem HA H mem1 HL FPLO ABL KEEP PRES.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
apply (alist_at_kept B ly S W mem ly S W mem1 (HA + 80) H true HL); [|exact ABL].
intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
- apply KEEP; unfold spZ, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
- intros Hw. apply (writable_kept (w_H W) mem mem1 a); [intros Hp; apply PRES; exact Hp | exact Hw].
Qed.
Lemma gf_rom_kept : forall W regs mem mem1,
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
rom_view SEGS W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
rom_view SEGS W mem1.
Proof.
intros W regs mem mem1 IMG HROM KEEP a Hin.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
assert (Hi : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
destruct (IMG a Hi) as [Ha0 Ha1].
rewrite KEEP; [exact (HROM a Hin) | unfold spZ, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia | lia].
Qed.
(* errno's four bytes are image bytes, so they lie below gesture_model's frame (the image is below kLowMemEnd, the
   frame above alloc_ceiling): every view kept outside the frame keeps errno's *)
Lemma gf_errno_out : forall W ly S Hp regs mem md ch, afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
forall j, 0 <= j < 4 -> 0 <= as_errno B + j < 2 ^ 64 /\ ~ (spZ regs - GM_STK <= as_errno B + j < spZ regs).
Proof.
intros W ly S hp regs mem md ch HPRE j Hj.
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _). pose proof Hstk as (_ & _ & Hceil & Hslo & _).
pose proof (pal_env B TL) as (_ & HeImg & _).
pose proof (pa_segs_low _ (HeImg (as_errno B + j) ltac:(lia))) as Hl.
pose proof ASAN_CEIL_range as (Hc & _). unfold ASAN_CEIL in Hc. unfold kLowMemEnd in *. split; [lia | lia].
Qed.

(* the machine state of the walk after a run, under a fixed name *)
Ltac gf_ms HS :=
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?m) => m
| st_ok _ _ _ (restrict _ ?m) => m
end.
Ltac gf_name HS nm := let m := gf_ms HS in rename m into nm.
(* the bytes outside the stack window and the present bytes, carried over one run of this walk *)
Ltac gf_kp HS Wv regsv memv KO PO mo KN PN :=
let mn := gf_ms HS in
lazymatch goal with
| Hf : frame_of _ _ (mrestrict (w_H Wv) mo) (mrestrict (w_H Wv) (ms_mem mn)),
  Hg : mem_grows (mrestrict (w_H Wv) mo) (mrestrict (w_H Wv) (ms_mem mn)) |- _ =>
  assert (KN : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regsv - GM_STK <= a < spZ regsv) ->
    aview SEGS (w_H Wv) (ms_mem mn) a = aview SEGS (w_H Wv) memv a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hno := fresh "Hno" in
      intros a Ha Hno; rewrite (aview_kept_out _ _ (w_H Wv) mo (ms_mem mn) Hf a Ha) by gf_outw;
      exact (KO a Ha Hno));
  assert (PN : forall a, apresent (w_H Wv) memv a -> apresent (w_H Wv) (ms_mem mn) a)
  by (let a := fresh "a" in let Hp := fresh "Hp" in
      intros a Hp; exact (gfL_pres_of_grows _ _ _ a Hg (PO a Hp)))
end.

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the walk at a world relation R, R a Section variable with its laws R_refl /
   R_trans / WLE_R.  Against the strict texts below: ajournal_gx_x SEGS B PST ARx -> ajournal_gx_xR SEGS B PST ARx R
   (AJG -> AJGR), SRr SEGS -> SRrG SEGS R, gm_post_x B PST ARx -> gm_post_xR B PST ARx R, the callees list_push /
   list_drop at their R contracts (LPUSH_R : lp_spec_xR, LDROP_R : ldrop_spec_xR; list_find, bcmp and the literals stay
   strict leaf facts, lifted by SRr_SRrG (WLE_R)), the runs and the branch their SRrG forms (W_journal_x.v
   paj_run_x_xG / paj_run_to_x_xG, W_kit.v paj_branch_xR), the binds SRrG_bind (R_trans), the kit's journal lemmas
   their _xR twins.  The strict texts after End wR are these at R := wle (LPUSH / LDROP give LPUSH_R / LDROP_R at wle by
   W_contract_xR.lp_spec_x_wle / W_contract_xR_g3.ldrop_spec_x_wle, by conversion). ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Hypothesis LPUSH_R : lp_spec_xR B PST ARx R MT RP G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP_R : ldrop_spec_xR B PST ARx R MT RP G (BASE + AF_fr_list_drop).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
#[local] Abbreviation AJGR := (ajournal_gx_xR SEGS B PST ARx R G 0 []).
(* :658 gf_callS: W_journal_x.v gx_callS_xR is its text over R *)
Lemma gf_callS_xR : forall G0 W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G0 ->
ajournal_gx_xR SEGS B PST ARx R G0 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_xR SEGS B PST ARx R G0 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRrG SEGS R W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_xR SEGS B PST ARx R G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_xR SEGS B PST ARx R G0 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. exact (gx_callS_xR SEGS B PST ARx LAWS pa_segs_low R_trans). Qed.
(* :700 gf_frames *)
Lemma gf_frames_xR : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_xR SEGS B PST ARx R G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
frames S' = own ++ frames S.
Proof.
intros G0 XO OUT STK sp0 FP ly S hp W mem md own ly' S' hp' W' mem' md' k (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _). exact Hfrs.
Qed.
(* :778 gf_ret_post *)
Lemma gf_ret_post_xR : forall W ly S Hp regs mem md ch HA (ln : list byte) H r m md2 mat' kk (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall rr, In rr (alist_fp (HA + 80) H) -> forall a, fst rr <= a < snd rr -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
gm_cost MT H ln = 0 ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
AJGR GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W m md2 kk ->
aregs_preserved regs r -> getr r 1 = getr regs 1 ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) m a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a) ->
RelayModel.upd (texts H) (bzs ln) = texts H ->
gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr W
(mkCfg (mkst r (v_jalr (getr r 1) 0) m (seg_rom SEGS)) (with_vm_backing (m_vm_lazy md2) mat' md2)).
Proof.
intros W ly S hp regs mem md ch HA ln H r m md2 mat' kk kr HPRE HL ND FPLO ABL COST0 HRM HJ HPR R1 PRES KEEP HU.
pose proof HPRE as (HAR & Hra & _).
unfold gm_post_xR. exists ly, S, hp, r, m, (with_vm_backing (m_vm_lazy md2) mat' md2), kk, H.
split; [rewrite R1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low G 0 []); exact HJ|].
split; [exact HPR|].
split; [intros a _ _ _ Hp; apply PRES; exact Hp|].
split; [intros ie Hie; destruct (gf_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; exact (KEEP _ Hr Hn)|].
split; [exact (gf_alist_kept W ly S regs mem HA H m HL FPLO ABL KEEP PRES)|].
split; [exact ND|].
split; [symmetry; exact HU|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite COST0; apply (mo_le_refl MT MTL)|].
(* no allocator call on this path: the budget is dropped *)
exact (gm_rm_down S _ kr HRM).
Qed.

(* :815 gf_lfind_call: list_find stays a strict leaf contract (LFIND), lifted by SRr_SRrG (WLE_R); its post
   journal is weakened to R by W_journal_x.ajournal_gx_xR_mono *)
Lemma gf_lfind_call_xR : forall W ly S Hp regs mem md HA LINE (ln : list byte) H (js q k : Z) regs1 mem1 md1 kc raw,
AJGR GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
spZ regs <= 2 ^ 47 ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 -> (HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> q <= LINE -> LINE + Z.of_nat (length ln) <= q + req_size k ->
0 <= js < Z.of_nat (length ln) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
spZ regs1 = spZ regs - 48 ->
getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regs1 8 = w64 LINE ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 LINE -> getr regs1 12 = w64 js ->
SRrG SEGS R W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_find)) mem1 (seg_rom SEGS)) md1)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 k2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJGR GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem2 md2 k2 /\
 aregs_preserved regs1 regs2 /\
 (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - LFIND_STK <= a < spZ regs - 48) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) /\
 ((exists j, lfind_match H (firstn (Z.to_nat js) ln) j /\ getr regs2 10 = w64 (Z.of_nat j)) \/
  ((forall kk, (kk < length (hl_recs H))%nat -> snd (nth kk (hl_recs H) (0, [])) <> firstn (Z.to_nat js) ln) /\
   getr regs2 10 = Z_to_bv 64 (-1)))).
Proof.
intros W ly S hp regs mem md HA LINE ln H js q k regs1 mem1 md1 kc raw
HJ H47 BLK IMG HL FPLO ABL HinG HZS HA8 GL LN Hq Hq1 Hq2 Hjs KEEP PRES Hsp Hgp Htp Hra Hraw Hra4 H8 H10 H11 H12.
pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Hsp0. change (bv_modulus 64) with (2 ^ 64) in Hsp0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as HAR1. apply ajournal_gx_AR_xR in HAR1.
pose proof (gf_alist_kept W ly S regs mem HA H mem1 HL FPLO ABL KEEP PRES) as HL1.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem1 md1 q k HAR1 Hq) as (_ & Hq4 & Hqc & _).
destruct (BLK q k LINE Hq ltac:(lia)) as [HL0 HLhi].
assert (LAimg : forall a, HA + 80 <= a < HA + 96 -> in_img SEGS a) by (intros a Ha; exact (proj1 (HG a (HinG a Ha)))).
pose proof (pa_img_range (HA + 80) (LAimg (HA + 80) ltac:(lia))) as HLA0.
pose proof (pa_segs_low (HA + 95) (LAimg (HA + 95) ltac:(lia))) as HLA1.
assert (GA1 : forall j, (j < length ln)%nat ->
aview SEGS (w_H W) mem1 (LINE + Z.of_nat j) = Some (nth j (bzs ln) 0)).
{ intros j Hj. destruct (BLK q k (LINE + Z.of_nat j) Hq ltac:(lia)) as [Ha0 Hahi].
  rewrite KEEP by (unfold spZ, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
  destruct (GL j ltac:(rewrite gfL_bzs_len; exact Hj)) as [Hv Hr].
  exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
assert (Lsb : Z.of_nat (length (firstn (Z.to_nat js) ln)) = js) by (rewrite length_firstn; lia).
eapply SRrG_mono.
{ eapply (gf_callS_xR G W regs1 mem1 _ GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp md1 kc
    LFIND_STK [] (-48) raw []
    (fun ly2 S2 hp2 W2 regs2 mem2 md2 => ly2 = ly /\ S2 = S /\ hp2 = hp /\ W2 = W /\
      (forall a, apresent (w_H W) mem1 a -> apresent (w_H W2) mem2 a) /\
      (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - LFIND_STK <= a < spZ regs - 48) ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem1 a) /\
      ((exists j, lfind_match H (firstn (Z.to_nat js) ln) j /\ getr regs2 10 = w64 (Z.of_nat j)) \/
       ((forall kk, (kk < length (hl_recs H))%nat -> snd (nth kk (hl_recs H) (0, [])) <> firstn (Z.to_nat js) ln) /\
        getr regs2 10 = Z_to_bv 64 (-1))))
    HG HJ).
  - rewrite Hsp. lia.
  - reflexivity.
  - lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK. lia.
  - unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK. lia.
  - exact Hgp.
  - exact Htp.
  - exact Hra.
  - exact Hraw.
  - exact Hra4.
  - apply achain_low. unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE1. apply (SRr_SRrG SEGS R WLE_R). eapply SRr_mono.
    { eapply (LFIND W ly S hp regs1 mem1 md1 [] (HA + 80) H true LINE (firstn (Z.to_nat js) ln) HPRE1).
      + exact H10.
      + exact H11.
      + rewrite Lsb. exact H12.
      + exact HL1.
      + exact HA8.
      + lia.
      + lia.
      + exact (azs_range_addressable_x B ARx LAWS ly S hp W mem1 md1 _ 16 HAR1 HZS).
      + intros a Ha. destruct (IMG a (LAimg a ltac:(lia))) as [Ha0 Ha1]. rewrite Hsp.
        unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      + lia.
      + rewrite Lsb. lia.
      + rewrite Lsb. unfold APARTIAL in LN. lia.
      + intros i Hi. rewrite Lsb in Hi. replace (LINE + i) with (LINE + Z.of_nat (Z.to_nat i)) by lia.
        rewrite GA1 by lia. f_equal. rewrite gfL_bzs_nth, gfL_nth_firstnA by lia. reflexivity.
      + intros a Ha. rewrite Lsb in Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Ha1]. rewrite Hsp.
        unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      + rewrite Lsb. apply (amem_range_of_block_x SEGS B ARx LAWS ly S hp W mem1 md1 q k LINE js HAR1 Hq); lia.
      + rewrite Lsb. apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem1 md1 q k LINE js HAR1 Hq); lia.
      + rewrite Lsb. intros Hpos. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W mem1 md1 q k LINE js HAR1 Hq); lia. }
    cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HPR3 & HK3 & HRES3).
    exists ly, S, hp, regs3, mem3, md3, 0. split; [rewrite Hra; reflexivity|]. split; [eapply ajournal_gx_xR_mono; [exact WLE_R | exact HJ3]|]. split; [exact HP3|].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HPR3|].
    split; [rewrite Hsp in HK3; exact HK3 | exact HRES3].
  - intros a Ha. exfalso. exact (inFP_nil a Ha). }
cbv beta. intros W2 c2 _ (ly2 & S2 & hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & _ & HP & (-> & -> & -> & -> & HPR & HK & HRES)).
split; [reflexivity|]. exists regs2, mem2, md2, (kc + k1).
split; [reflexivity|]. split; [exact HJc|]. split; [exact HP|]. split; [exact HPR|]. split; [exact HK | exact HRES].
Qed.

(* :920 gf_drop_tail: list_drop by LDROP_R (ldrop_spec_xR), its post ldrop_post_xR *)
Lemma gf_drop_tail_xR : forall W ly S Hp regs mem md ch HA (ln : list byte) H (js : Z) regs1 mem1 md1 kc j (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
AJGR GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 -> (HA + 80) mod 8 = 0 ->
AREC * hl_cap H < 2 ^ 32 -> mo_ok MT S (gm_cost MT H ln) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> cnt_ok_pk RP ldrop_pk (ablocks B ly S) ->
rom_view SEGS W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
aregs_preserved regs regs1 -> getr regs1 1 = getr regs 1 ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 (Z.of_nat j) ->
lfind_match H (firstn (Z.to_nat js) ln) j ->
RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, firstn (Z.to_nat js) (bzs ln)) ->
SRrG SEGS R W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem1 (seg_rom SEGS)) md1)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Proof.
intros W ly S hp regs mem md ch HA ln H js regs1 mem1 md1 kc j kr HPRE HJ BLK IMG HL ND FPLO ABL HinG HZS HA8 HAREC MOK
HRM HCNT HROM KEEP PRES PRV R1 H10 H11 HM GEND.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (gfL_prv regs regs1 PRV) as (R2 & R3 & R4 & R8).
pose proof (gf_alist_kept W ly S regs mem HA H mem1 HL FPLO ABL KEEP PRES) as HL1.
pose proof (gf_rom_kept W regs mem mem1 IMG HROM KEEP) as ROM1.
pose proof HM as (Hj & Hsnd & _).
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
assert (Hcap : 0 < hl_cap H) by (unfold hl_n in L5; lia).
destruct L6 as [(Hc0 & _) | (_ & Hinv & _)]; [lia|].
assert (Hrj : In (nth j (hl_recs H) (0, [])) (hl_recs H)) by (apply nth_In; exact Hj).
rewrite Forall_forall in L9. destruct (L9 _ Hrj) as (Rin & _).
assert (LAimg : forall a, HA + 80 <= a < HA + 96 -> in_img SEGS a) by (intros a Ha; exact (proj1 (HG a (HinG a Ha)))).
pose proof (pa_img_range (HA + 80) (LAimg (HA + 80) ltac:(lia))) as HLA0.
pose proof (pa_segs_low (HA + 95) (LAimg (HA + 95) ltac:(lia))) as HLA1.
assert (Ecap : (hl_cap H =? 0) = false) by (apply Z.eqb_neq; lia).
(* the end of a held key: gesture_model's charge is list_drop's one free *)
assert (HKIN : In (firstn (Z.to_nat js) (bzs ln)) (texts H)).
{ destruct (gfL_match_nth H (firstn (Z.to_nat js) ln) j HM) as [Hjl Hnj].
  rewrite <- gfL_bzs_firstn, <- Hnj. apply nth_In. exact Hjl. }
pose proof (gf_cost_end_in MT H ln _ GEND HKIN) as CE.
eapply SRrG_mono.
{ eapply (gf_callS_xR G W regs1 mem1 _ GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp md1 kc
    LDROP_STK [(hl_v H, hl_v H + AREC * hl_cap H);
      (fst (nth j (hl_recs H) (0, [])),
       fst (nth j (hl_recs H) (0, [])) + req_size (Z.of_nat (length (snd (nth j (hl_recs H) (0, []))))+ 1))]
    0 (getr regs 1) ch
    (fun ly2 S2 hp2 W2 regs2 mem2 md2 => apres_kept B W mem1 W2 mem2 /\
      (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem1 (as_errno B + j)) /\
      alist_at B ly2 S2 W2 mem2 (HA + 80) (ldrop_list H j) true /\
      (exists b1 b2, ablocks B ly S = b1 ++ (fst (nth j (hl_recs H) (0, [])),
        Z.of_nat (length (snd (nth j (hl_recs H) (0, [])))) + 1) :: b2 /\ ablocks B ly2 S2 = b1 ++ b2) /\
      mo_le MT S S2 (mo_free MT) /\ rp_RM RP S2 kr)
    HG HJ).
  - unfold spZ. rewrite R2. lia.
  - reflexivity.
  - lia.
  - unfold LDROP_STK, LDROP_FRAME, ASTACK. lia.
  - unfold LDROP_STK, LDROP_FRAME, GM_STK, GM_FRAME, LP_STK, ASTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - exact Hra.
  - exact Hra4.
  - rewrite Z.add_0_r. replace (s0Z regs1) with (s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply KEEP; lia.
  - intros HPRE1. eapply SRrG_mono.
    { eapply (LDROP_R W ly S hp regs1 mem1 md1 ch (HA + 80) H true j HPRE1) with (kr := kr).
      + exact H10.
      + exact H11.
      + exact HL1.
      + exact Hj.
      + exact HA8.
      + lia.
      + (* list_drop's memmove premise: the capacity form (A's ldrop_spec until W1 eb49c578595) or the moved-bytes form
           AREC * (n - 1 - j) (B's, and A's from eb49c578595): both follow from HAREC, 0 <= j and n <= cap *)
        pose proof HL1 as (_ & _ & _ & _ & Lnc & _). pose proof (Nat2Z.is_nonneg j). unfold hl_n in *.
        unfold AREC in *. lia.
      + exact HZS.
      + intros a Ha. split; [exact (HinG a ltac:(lia))|]. destruct (IMG a (LAimg a ltac:(lia))) as [Ha0 Ha1].
        unfold spZ in *. rewrite R2. unfold LDROP_STK, LDROP_FRAME, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      + intros a Ha. pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs].
        destruct (BLK _ _ a Hinv ltac:(lia)) as [Ha0 Ha1].
        unfold spZ in *. rewrite R2. unfold LDROP_STK, LDROP_FRAME, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      + rewrite <- CE. exact MOK.
      + exact (gm_rm_drop S H ln _ kr GEND HKIN HRM).
      + exact HCNT.
      + exact ROM1. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & hp3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HAK3 & HE3 & HL3 & HB3 & HM3 & HRM3).
    exists ly3, S3, hp3, regs3, mem3, md3, 1. split; [rewrite R1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
    split; [exact HAK3|]. split; [exact HE3|]. split; [exact HL3|]. split; [exact HB3|]. split; [exact HM3 | exact HRM3].
  - intros a Ha. left. destruct Ha as (rr & Hr & Hra'). cbn [In] in Hr.
    destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hra'.
    + split.
      * apply (gfL_blk_fp _ (hl_v H, AREC * hl_cap H)); [|cbn [snd]; unfold AREC; lia | cbn [fst snd]; exact Hra'].
        unfold list_blks. rewrite Ecap. apply in_or_app. left. left. reflexivity.
      * exists (hl_v H), (AREC * hl_cap H). split; [exact Hinv|].
        pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs]. lia.
    + split.
      * apply (gfL_blk_fp_r _ (fst (nth j (hl_recs H) (0, [])), Z.of_nat (length (snd (nth j (hl_recs H) (0, [])))) + 1));
        [|cbn [fst snd]; exact Hra'].
        unfold list_blks. apply in_or_app. right.
        exact (in_map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) _ _ Hrj).
      * exists (fst (nth j (hl_recs H) (0, []))), (Z.of_nat (length (snd (nth j (hl_recs H) (0, [])))) + 1).
        split; [exact Rin | exact Hra']. }
cbv beta. intros W2 c2 _ (ly2 & S2 & hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & _ & HP & (HAK & HE2 & HL2 & HB2 & HM2 & HRM2)).
unfold gm_post_xR. exists ly2, S2, hp2, regs2, mem2, md2, (kc + k1), (ldrop_list H j).
split; [reflexivity|].
split; [exact HJc|].
split; [exact (aregs_preserved_trans _ _ _ PRV HP)|].
split; [intros a Hi Ho He Hp; apply HAK; [exact Hi | exact Ho | exact He | apply PRES; exact Hp]|].
split; [intros ie Hie; rewrite (HE2 ie Hie); destruct (gf_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; exact (KEEP _ Hr Hn)|].
split; [exact HL2|].
split; [rewrite gfL_texts_drop; apply (proj2 (NoDup_ListNoDup _)); apply gfL_nodup_drop;
  exact (proj1 (NoDup_ListNoDup _) ND)|].
split.
{ rewrite gfL_texts_drop. symmetry.
  apply GM.upd_end_at; [| exact (proj1 (NoDup_ListNoDup _) ND) | rewrite gfL_texts_len; exact Hj].
  rewrite GEND, gfL_texts_nth by exact Hj. rewrite Hsnd, gfL_bzs_firstn. reflexivity. }
split.
{ unfold ldrop_list, hl_n. cbn [hl_cap hl_recs].
  rewrite (proj2 (Z.ltb_ge _ _)) by (rewrite length_app, length_firstn, length_skipn; lia). reflexivity. }
split.
{ intros rest HPq. destruct HB2 as (b1 & b2 & E1 & E2). rewrite E2. rewrite E1 in HPq.
  unfold list_blks in HPq |- *. unfold ldrop_list. cbn [hl_cap hl_v hl_recs].
  assert (Hsplit : map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs H) =
    map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (firstn j (hl_recs H)) ++
    (fst (nth j (hl_recs H) (0, [])), Z.of_nat (length (snd (nth j (hl_recs H) (0, [])))) + 1) ::
    map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (skipn (Datatypes.S j) (hl_recs H))).
  { rewrite (gfL_split_nthA (hl_recs H) j (0, []) Hj) at 1. rewrite map_app. reflexivity. }
  rewrite Hsplit in HPq. rewrite map_app. exact (gfL_perm_drop _ b1 b2 _ _ _ rest HPq). }
split; [rewrite (gf_frames_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc); reflexivity|].
split; [rewrite CE; exact HM2|].
exact HRM2.
Qed.

(* :1062 gf_push_tail: list_push by LPUSH_R (lp_spec_xR), its post lp_post_xR *)
Lemma gf_push_tail_xR : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H (js q k : Z) regs1 mem1 md1 kc (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
AJGR GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
(lp_grow H = true -> lp_vbytes H < MMAX) ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> cnt_ok_pk RP (lp_peak H js) (ablocks B ly S) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
aregs_preserved regs regs1 -> getr regs1 1 = getr regs 1 ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 LINE -> getr regs1 12 = w64 js ->
0 <= js < Z.of_nat (length ln) ->
(forall kk, (kk < length (hl_recs H))%nat -> snd (nth kk (hl_recs H) (0, [])) <> firstn (Z.to_nat js) ln) ->
RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, firstn (Z.to_nat js) (bzs ln)) ->
SRrG SEGS R W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_push)) mem1 (seg_rom SEGS)) md1)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Proof.
intros W ly S hp regs mem md ch HA LINE ln H js q k regs1 mem1 md1 kc kr HPRE HJ BLK IMG HL ND FPLO ABL HinG HZS HA8
GL NZ LN Hq Hqb Hq1 Hq2 HGROW HROOM MOK HRM HCNT KEEP PRES PRV R1 H10 H11 H12 Hjs HNM GBEG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (gfL_prv regs regs1 PRV) as (R2 & R3 & R4 & R8).
pose proof (gf_alist_kept W ly S regs mem HA H mem1 HL FPLO ABL KEEP PRES) as HL1.
pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
assert (CAP0 : 0 <= hl_cap H) by (unfold hl_n in L5; lia).
assert (Lx : Z.of_nat (length (firstn (Z.to_nat js) ln)) = js) by (rewrite length_firstn; lia).
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR Hq) as (_ & Hq4 & _).
assert (Hqv : q <> hl_v H).
{ intros Hqe. destruct L6 as [(Hc0 & Hv0) | (Hcp & Hinv & _)]; [lia|].
  apply Hqb. rewrite Hqe in Hq |- *.
  pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [Hrs1 _].
  rewrite (gf_same_base ly S hp W mem md (hl_v H) k (AREC * hl_cap H) HAR Hq Hinv ltac:(lia) Hrs1).
  unfold list_blks. rewrite (proj2 (Z.eqb_neq (hl_cap H) 0) ltac:(lia)). apply in_or_app. left. left. reflexivity. }
assert (GL1 : garr8 SEGS (mrestrict (w_H W) mem1) LINE (bzs (firstn (Z.to_nat js) ln))).
{ assert (GLm : garr8 SEGS (mrestrict (w_H W) mem1) LINE (bzs ln)).
  { apply (garr8_frame SEGS (arm W mem) _ LINE (bzs ln) GL). intros a Ha. apply (mbyte_of_aview SEGS).
    rewrite gfL_bzs_len in Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Ha1].
    apply KEEP; unfold spZ, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia. }
  rewrite gfL_bzs_firstn. rewrite <- (firstn_skipn (Z.to_nat js) (bzs ln)) in GLm.
  apply garr8_app in GLm as [GLm _]. exact GLm. }
(* a begin of a key not held: gesture_model's charge is list_push's at the key, js bytes *)
assert (NIN : ~ In (firstn (Z.to_nat js) (bzs ln)) (texts H))
by (rewrite <- gfL_bzs_firstn; exact (gfL_notin_texts H _ HNM)).
assert (Lxb : Z.of_nat (length (firstn (Z.to_nat js) (bzs ln))) = js) by (rewrite length_firstn, gfL_bzs_len; lia).
assert (CI : gm_cost MT H ln = lp_cost MT H js) by (rewrite (gf_cost_begin_new MT H ln _ GBEG NIN), Lxb; reflexivity).
eapply SRrG_mono.
{ eapply (gf_callS_xR G W regs1 mem1 _ GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md [] ly S hp md1 kc
    LP_STK (lp_FP H) 0 (getr regs 1) ch
    (fun ly2 S2 hp2 W2 regs2 mem2 md2 => exists (l' : hlist) (d : Z),
      alist_at B ly2 S2 W2 mem2 (HA + 80) l' true /\
      hl_recs l' = hl_recs H ++ [(d, firstn (Z.to_nat js) ln)] /\
      hl_cap l' = ListRep.grow_cap (hl_n H) (hl_cap H) /\
      (lp_grow H = false -> hl_v l' = hl_v H) /\
      (forall rest,
       Permutation (ablocks B ly S) ((if lp_grow H && negb (hl_cap H =? 0) then [(hl_v H, AREC * hl_cap H)] else []) ++ rest) ->
       Permutation (ablocks B ly2 S2)
         ((d, Z.of_nat (length (firstn (Z.to_nat js) ln)) + 1) ::
          (if lp_grow H then [(hl_v l', AREC * hl_cap l')] else []) ++ rest)) /\
      apres_kept B W mem1 W2 mem2 /\
      (forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) mem1 (as_errno B + j)) /\ frames S2 = frames S /\
      mo_le MT S S2 (lp_cost MT H (Z.of_nat (length (firstn (Z.to_nat js) ln)))) /\ rp_RM RP S2 kr)
    HG HJ).
  - unfold spZ. rewrite R2. lia.
  - reflexivity.
  - lia.
  - unfold LP_STK, ASTACK. lia.
  - unfold GM_STK, GM_FRAME, LP_STK, ASTACK. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - exact R1.
  - exact Hra.
  - exact Hra4.
  - rewrite Z.add_0_r. replace (s0Z regs1) with (s0Z regs) by (unfold s0Z; rewrite R8; reflexivity).
    apply (achain_kept ly (aview SEGS (w_H W) mem) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch); [lia | lia |].
    intros a Ha. apply KEEP; lia.
  - intros HPRE1. eapply SRrG_mono.
    { eapply (LPUSH_R W ly S hp regs1 mem1 md1 ch (HA + 80) LINE H true (firstn (Z.to_nat js) ln) q k HPRE1) with (kr := kr).
      + exact H10.
      + exact H11.
      + rewrite Lx. exact H12.
      + exact HA8.
      + exact HL1.
      + intros a Ha. exact (HinG a ltac:(lia)).
      + exact HZS.
      + exact HGROW.
      + rewrite Lx. unfold APARTIAL in LN. lia.
      + pose proof (lp_tr_peak_le H _ CAP0 (Nat2Z.is_nonneg (length (firstn (Z.to_nat js) ln)))) as LPK.
        rewrite Lx in LPK |- *. lia.
      + exact Hq.
      + exact Hqv.
      + exact Hq1.
      + rewrite Lx. lia.
      + exact GL1.
      + intros _. split; [intros Hin; apply NZ; exact (gfL_in_firstn _ _ _ Hin) | rewrite Lx; lia].
      + intros Hf. discriminate Hf.
      + rewrite Lx, <- CI. exact MOK.
      + rewrite Lx, <- Lxb. exact (gm_rm_push S H ln _ kr GBEG NIN HRM).
      + rewrite Lx. exact HCNT. }
    cbv beta. intros W3 c3 _ (ly3 & S3 & hp3 & regs3 & mem3 & md3 & kk3 & l3 & d3 & -> & HJ3 & HP3 & HL3 & HR3 & HC3 & HV3
      & HPm3 & HAK3 & HE3 & HF3 & HM3 & HRM3).
    exists ly3, S3, hp3, regs3, mem3, md3, kk3. split; [rewrite R1; reflexivity|]. split; [exact HJ3|]. split; [exact HP3|].
    exists l3, d3. split; [exact HL3|]. split; [exact HR3|]. split; [exact HC3|]. split; [exact HV3|].
    split; [exact HPm3|]. split; [exact HAK3|]. split; [exact HE3|]. split; [exact HF3|]. split; [exact HM3 | exact HRM3].
  - intros a Ha. left. revert Ha. unfold lp_FP. destruct (hl_cap H =? 0) eqn:Ec; intros Ha;
    [exfalso; exact (inFP_nil a Ha)|]. apply Z.eqb_neq in Ec.
    destruct Ha as (rr & [<- | []] & Hra'). cbn [fst snd] in Hra'.
    destruct L6 as [(Hc0 & _) | (_ & Hinv & _)]; [lia|].
    split.
    + apply (gfL_blk_fp _ (hl_v H, AREC * hl_cap H)); [|cbn [snd]; unfold AREC; lia | cbn [fst snd]; exact Hra'].
      unfold list_blks. rewrite (proj2 (Z.eqb_neq _ _) Ec). apply in_or_app. left. left. reflexivity.
    + exists (hl_v H), (AREC * hl_cap H). split; [exact Hinv|].
      pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs]. lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & hp2 & regs2 & mem2 & md2 & k1 & -> & HJc & _ & HP &
  (l' & d & HL2 & HR2 & HC2 & HV2 & HPm2 & HAK & HE2 & HF2 & HM2 & HRM2)).
unfold gm_post_xR. exists ly2, S2, hp2, regs2, mem2, md2, (kc + k1), l'.
split; [reflexivity|].
split; [exact HJc|].
split; [exact (aregs_preserved_trans _ _ _ PRV HP)|].
split; [intros a Hi Ho He Hp; apply HAK; [exact Hi | exact Ho | exact He | apply PRES; exact Hp]|].
split; [intros ie Hie; rewrite (HE2 ie Hie); destruct (gf_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; exact (KEEP _ Hr Hn)|].
split; [exact HL2|].
split.
{ rewrite (gfL_texts_push H l' d _ HR2), gfL_bzs_firstn.
  apply (proj2 (NoDup_ListNoDup _)). apply (Permutation_NoDup (Permutation_cons_append _ _)).
  constructor; [exact NIN | exact (proj1 (NoDup_ListNoDup _) ND)]. }
split.
{ rewrite (gfL_texts_push H l' d _ HR2), gfL_bzs_firstn. symmetry. exact (GM.upd_begin_new _ _ _ GBEG NIN). }
split.
{ unfold hl_n. rewrite HR2, length_app. cbn [length]. rewrite (proj2 (Z.ltb_lt _ _)) by lia. exact HC2. }
split.
{ intros rest HPq. unfold list_blks in HPq |- *. rewrite HR2, map_app. cbn [map fst snd].
  rewrite <- app_assoc in HPq.
  destruct (lp_grow H) eqn:Eg.
  - assert (Ec' : (hl_cap l' =? 0) = false).
    { apply Z.eqb_neq. rewrite HC2. unfold ListRep.grow_cap. unfold lp_grow in Eg. rewrite Eg.
      destruct (Z.eqb_spec (hl_cap H) 0); lia. }
    rewrite Ec'. specialize (HPm2 (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs H) ++ rest)).
    assert (EV : (if true && negb (hl_cap H =? 0) then [(hl_v H, AREC * hl_cap H)] else []) =
      (if hl_cap H =? 0 then [] else [(hl_v H, AREC * hl_cap H)])) by (destruct (hl_cap H =? 0); reflexivity).
    rewrite EV in HPm2. specialize (HPm2 HPq).
    eapply perm_trans; [exact HPm2|]. apply gfL_perm_snoc.
  - assert (Hcap' : hl_cap l' = hl_cap H)
    by (rewrite HC2; unfold ListRep.grow_cap; unfold lp_grow in Eg; rewrite Eg; reflexivity).
    rewrite Hcap', (HV2 eq_refl).
    specialize (HPm2 ((if hl_cap H =? 0 then [] else [(hl_v H, AREC * hl_cap H)]) ++
      map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs H) ++ rest) HPq).
    rewrite app_nil_l in HPm2. eapply perm_trans; [exact HPm2|]. apply gfL_perm_snoc. }
split; [exact HF2|].
split; [rewrite CI, <- Lx; exact HM2|].
exact HRM2.
Qed.

(* :1249 gf_ret_tail at R: the return moves no world, so the strict step is lifted by SRr_SRrG (WLE_R); a return
   through the epilogue with the held list unchanged; leaves the model goal upd (texts H) _ = texts H *)
Ltac gf_ret_tail_xR RETv HS Wv regsv memv KO PO mo ENVx HJx Hspc H3c H4c HC HPRE HL ND FPLO ABL COST0 HRMx :=
let KN := fresh "KN" in let PN := fresh "PN" in let PRV := fresh "PRV" in let RV1 := fresh "RV1" in
let mat := fresh "mat" in
gf_kp HS Wv regsv memv KO PO mo KN PN;
destruct (gf_ret_regs _ _ _ _ _ regsv HS ENVx Hspc H3c H4c HC ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as [PRV RV1];
apply (SRr_SRrG SEGS R WLE_R);
eapply (RETv _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat;
apply (gf_ret_post_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat _ _ HPRE HL ND FPLO ABL COST0 HRMx HJx PRV RV1 PN KN).

(* :1259 pb_gm_found_x *)
Lemma pb_gm_found_xR : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Proof.
intros W ly S hp regs mem md ch HA LINE ln H q k js regsc memc mdc
HPRE H10 H11 H12 HL ND HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT
HFK HSPC Hspc Hgpc Htpc Hc8 Hc9 Hc18 Hc19 H2027 VRA V8 V9 V18 V19 KEEP0 PRES0 HJ0 HLSF HJS Hc10.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (gf_entry W regs regsc memc ly Hstk Hspc VRA V8 V9 V18 V19) as [HS SHOK].
remember (Eimg (Ereg regsc (gf_extra regs))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regsc 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsc 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsc 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 LINE) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 8 8%bv eq_refl); exact Hc8).
assert (E9 : ew E 9 = Z_to_bv 64 HA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 9 9%bv eq_refl); exact Hc9).
assert (E10 : ew E 10 = Z_to_bv 64 (js + 1 - Z.of_nat (length ln))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 10 10%bv eq_refl); exact Hc10).
assert (E18 : ew E 18 = Z_to_bv 64 (Z.of_nat (length ln))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 18 18%bv eq_refl); exact Hc18).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl); exact Hc19).
assert (E33 : ew E 33 = getr regs 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = getr regs 9) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
assert (E35 : ew E 35 = getr regs 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 3)).
assert (E36 : ew E 36 = getr regs 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 4)).
assert (E37 : ew E 37 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 5)).
assert (E262 : ew E 262%nat = Z_to_bv 64 (VAL (A_OBJ 21))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E264 : ew E 264%nat = Z_to_bv 64 (VAL (A_OBJ 23))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E265 : ew E 265%nat = Z_to_bv 64 (VAL (A_OBJ 24))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs - 48) by (rewrite E2; unfold spZ in Hspc |- *; unfold GM_FRAME in Hspc; lia).
assert (HAE : env_agree 32 (Ereg regsc (gf_extra regs)) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (ENV0 : gf_env E regsc regs)
by (split; [exact HEI|]; split; [exact HAE|]; repeat split; assumption).
assert (H3c : getr regsc 3 = getr regs 3) by (rewrite Hgpc, Hgp; reflexivity).
assert (H4c : getr regsc 4 = getr regs 4) by (rewrite Htpc, Htp; reflexivity).
assert (HC2027 : forall r, 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r))
by (intros r Hr; apply H2027; [unfold acallee_saved; lia | lia]).
assert (SP47 : spZ regs <= 2 ^ 47)
by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK, alloc_ceiling in *; lia).
assert (HAimg : forall a, HA + 80 <= a < HA + 96 -> in_img SEGS a)
by (intros a Ha; exact (proj1 (HG a (HinG a Ha)))).
pose proof (pa_img_range (HA + 80) (HAimg (HA + 80) ltac:(lia))) as HAR0.
assert (LWE : length RelayModel.W_END = 3%nat) by reflexivity.
assert (LWB : length RelayModel.W_BEGIN = 5%nat) by reflexivity.
(* ---- bounds every arm needs: the list's bytes and the image are below this frame. ---- *)
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq1 : 1 <= req_size k) by lia.
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros p n a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S hp W mem md p n HAR Hin) as (_ & Hp4 & Hpc & _).
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (IMG : forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK).
{ intros a Hin. pose proof (pa_segs_low a Hin) as Hl.
unfold kLowMemEnd, GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; [lia | lia]. }
assert (FPLO : forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r ->
0 <= a /\ a < spZ regs - GM_STK).
{ intros r Hr a Ha. pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
unfold alist_fp in Hr. destruct Hr as [<- | Hr].
- cbn [fst snd] in Ha. apply IMG. apply (proj1 (HG a (HinG a ltac:(lia)))).
- apply in_app_or in Hr as [Hr | Hr].
+ destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hr; [destruct Hr|].
destruct Hr as [<- | []]. apply Z.eqb_neq in Ec.
destruct L6 as [(Hc0 & _) | (Hc0 & Hinv & Hj & _)]; [lia|].
pose proof (vec_len H Hj) as Hlen. unfold gfp in Ha. cbn [fst snd] in Ha. rewrite Hlen in Ha.
pose proof (req_size_pos (AREC * hl_cap H) ltac:(unfold AREC; lia)) as [_ Hrs].
apply (BLK (hl_v H) (AREC * hl_cap H) a Hinv). lia.
+ apply in_map_iff in Hr as (rec & <- & Hrec). unfold gfp in Ha. cbn [fst snd] in Ha.
rewrite Forall_forall in L9. destruct (L9 rec Hrec) as (Rin & _).
pose proof (req_size_pos (Z.of_nat (length (snd rec)) + 1) ltac:(lia)) as [_ Hrs].
apply (BLK (fst rec) (Z.of_nat (length (snd rec)) + 1) a Rin).
unfold bzs in Ha. rewrite length_map, length_app in Ha. cbn [length] in Ha. lia. }
assert (ABL : forall b, In b (alist_blks H) -> In b (ablocks B ly S)).
{ intros b Hb. pose proof HL as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9).
unfold alist_blks in Hb. apply in_app_or in Hb as [Hb | Hb].
- destruct (hl_cap H =? 0) eqn:Ec; cbn [In] in Hb; [destruct Hb|].
destruct Hb as [<- | []]. apply Z.eqb_neq in Ec.
destruct L6 as [(Hc0 & _) | (_ & Hinv & _)]; [lia | exact Hinv].
- apply in_map_iff in Hb as (rec & <- & Hrec). rewrite Forall_forall in L9.
exact (proj1 (L9 rec Hrec)). }
(* the line's bytes, as the ASan view at this point *)
assert (GA : forall j, (j < length ln)%nat ->
aview SEGS (w_H W) mem (LINE + Z.of_nat j) = Some (nth j (bzs ln) 0)).
{ intros j Hj. destruct (GL j ltac:(unfold bzs; rewrite length_map; exact Hj)) as [Hv Hr].
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
psrr_branch_tok RUNG BRR HS SHOK Bspan.
- (* last = 14: the line's only space is byte 13, so it names no gesture *)
rewrite branch_eq_U, (gfL_U_add E 10 18 _ _ E10 E18 ltac:(lia)), U_lit in Hc by lia.
assert (Hjs13 : js = 13)
by (destruct (Z.eqb_spec (js + 1 - Z.of_nat (length ln) + Z.of_nat (length ln)) 14); [lia | discriminate]).
assert (GNONE : RelayModel.gesture (bzs ln) = None).
{ rewrite (GM.at_j (bzs ln) (Z.to_nat js) ltac:(rewrite gfL_bzs_len; lia) HFK HSPC HLSF).
replace (Z.to_nat js) with 13%nat by lia. reflexivity. }
paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gf_outw.
rewrite (aview_kept_out E _ (w_H W) memc (ms_mem ms) HFr a Ha) by gf_outw.
apply KEEP0; [exact Ha | exact Hno]. }
assert (PRES : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (gfL_pres_of_grows _ _ _ a K2 (gfL_pres_of_grows _ _ _ a K1 (PRES0 a Hp))) end. }
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
assert (PRESV : aregs_preserved regs (ms_regs ms0)).
{ apply (gfL_pres regs regsc).
- unfold spZ in Hspc |- *. unfold GM_FRAME in Hspc. lia.
- intros r Hr. apply H2027; [unfold acallee_saved; lia | lia].
- rewrite Hgpc, Hgp. reflexivity.
- rewrite Htpc, Htp. reflexivity.
- intros r Hr. apply (gf_reg_kept E _ ms0 regsc (gf_extra regs) (w_H W) GF_CS HS HAE
  ltac:(vm_compute; reflexivity)). apply gf_cs_in. exact Hr.
- rewrite P2, E2. reflexivity.
- rewrite P3, E3. reflexivity.
- rewrite P4, E4. reflexivity.
- rewrite P8, E33. reflexivity.
- rewrite P9, E34. reflexivity.
- rewrite P18, E35. reflexivity.
- rewrite P19, E36. reflexivity. }
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold gm_post_xR.
lazymatch goal with |- exists _ _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
exists ly, S, hp, r, m, d, 0, H end.
split; [cbn [ms_regs]; rewrite P1, E37, Hra; reflexivity|].
split; [cbn [ms_mem]; apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs G 0 []); exact HJ0|].
split; [exact PRESV|].
split; [intros a _ _ _ Hp; apply PRES; exact Hp|].
split; [intros ie Hie; destruct (gf_errno_out W ly S hp regs mem md ch HPRE ie Hie) as [Hr Hn]; cbn [ms_mem]; exact (KEEP _ Hr Hn)|].
split.
{ cbn [ms_mem]. apply (alist_at_kept B ly S W mem ly S W (ms_mem ms0) (HA + 80) H true HL).
- intros r Hr a Ha. destruct (FPLO r Hr a Ha) as [Ha0 Hahi]. split.
  + apply KEEP; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  + intros Hw. apply (writable_kept (w_H W) mem (ms_mem ms0) a); [intros Hp; apply PRES; exact Hp | exact Hw].
- exact ABL. }
split; [exact ND|].
split; [symmetry; apply GM.upd_none; exact GNONE|].
split; [destruct (Z.ltb_spec (hl_n H) (hl_n H)); [lia | reflexivity]|].
split; [intros rest Hperm; exact Hperm|].
split; [reflexivity|].
split; [rewrite (gf_cost_none MT H ln GNONE); apply (mo_le_refl MT MTL)|].
exact (gm_rm_down S _ kr HRM).
- (* 14 < last: the word after the last space is len - last bytes long *)
rewrite branch_eq_U, (gfL_U_add E 10 18 _ _ E10 E18 ltac:(lia)), U_lit in Hc by lia.
assert (Hjs : 13 < js)
by (destruct (Z.eqb_spec (js + 1 - Z.of_nat (length ln) + Z.of_nat (length ln)) 14); [discriminate | lia]).
assert (GJ : RelayModel.gesture (bzs ln) =
if RelayModel.list_eqb (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_BEGIN
then Some (RelayModel.GBegin, firstn (Z.to_nat js) (bzs ln))
else if RelayModel.list_eqb (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_END
then Some (RelayModel.GEnd, firstn (Z.to_nat js) (bzs ln)) else None).
{ rewrite (GM.at_j (bzs ln) (Z.to_nat js) ltac:(rewrite gfL_bzs_len; lia) HFK HSPC HLSF).
rewrite (proj2 (Nat.ltb_lt 13 (Z.to_nat js)) ltac:(lia)). reflexivity. }
assert (WLEN : Z.of_nat (length (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)))
= Z.of_nat (length ln) - js - 1) by (rewrite length_skipn, gfL_bzs_len; lia).
clear Hc.
paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms) (ms_mem ms0) HFr0 a Ha) by gf_outw.
rewrite (aview_kept_out E _ (w_H W) memc (ms_mem ms) HFr a Ha) by gf_outw.
apply KEEP0; [exact Ha | exact Hno]. }
assert (PRES2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Hp. lazymatch goal with
| K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
  K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
  exact (gfL_pres_of_grows _ _ _ a K2 (gfL_pres_of_grows _ _ _ a K1 (PRES0 a Hp))) end. }
assert (LITLO : forall (oi : nat) (n : Z), (oi < 33)%nat -> 0 <= n <= 16 ->
0 <= VAL (A_OBJ oi) + n /\ VAL (A_OBJ oi) + n < spZ regs - GM_STK).
{ intros oi n Hi Hn. pose proof (pa_obj_img oi Hi) as Hobj.
unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *. split; lia. }
pose proof (pa_val_range (A_OBJ 23)) as HV23. pose proof (pa_val_range (A_OBJ 24)) as HV24.
pose proof (pa_obj_img 23 ltac:(lia)) as HO23. pose proof (pa_obj_img 24 ltac:(lia)) as HO24.
psrr_branch_tok RUNG BRR HS SHOK Bspan.
+ (* the word is 3 bytes: compare it with "end" *)
rewrite branch_eq_U, (gfL_U_neg E 10 _ E10 ltac:(lia)), U_lit in Hc by lia.
assert (HW3 : Z.of_nat (length ln) = js + 4)
by (destruct (Z.eqb_spec (- (js + 1 - Z.of_nat (length ln))) 3); [lia | discriminate]).
clear Hc.
paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (12%bv : bv 5) T12.
assert (KEEPA : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms1) a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (aview_kept_out E _ (w_H W) (ms_mem ms0) (ms_mem ms1) HFr1 a Ha) by gf_outw.
apply KEEP2; [exact Ha | exact Hno]. }
assert (PRESA : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Hp. lazymatch goal with
| K3 : mem_grows (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) (ms_mem ms1)) |- _ =>
  exact (gfL_pres_of_grows _ _ _ a K3 (PRES2 a Hp)) end. }
assert (UspA : spZ (ms_regs ms1) = spZ regs - 48) by (unfold spZ; rewrite T2, Usp; reflexivity).
pose proof HJ0 as HARc. apply ajournal_gx_AR_xR in HARc.
assert (GAW : forall i, (i < 3)%nat ->
aview SEGS (w_H W) (ms_mem ms1) (LINE + js + 1 + Z.of_nat i)
= Some (nth (Datatypes.S (Z.to_nat js) + i)%nat (bzs ln) 0)).
{ intros i Hi. destruct (BLK q k (LINE + js + 1 + Z.of_nat i) Hq ltac:(lia)) as [Ha0 Hahi].
rewrite (KEEPA (LINE + js + 1 + Z.of_nat i) ltac:(lia) ltac:(lia)).
replace (LINE + js + 1 + Z.of_nat i) with (LINE + Z.of_nat (Datatypes.S (Z.to_nat js) + i)) by lia.
apply GA. lia. }
assert (LITE : forall i, (i < 3)%nat ->
aview SEGS (w_H W) (ms_mem ms1) (VAL (A_OBJ 24) + Z.of_nat i) = Some (nth i RelayModel.W_END 0)).
{ intros i Hi. destruct (LITLO 24%nat (Z.of_nat i) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
rewrite (KEEPA (VAL (A_OBJ 24) + Z.of_nat i) ltac:(lia) ltac:(lia)).
destruct (LE i ltac:(vm_compute; lia)) as [Hv Hr].
change (VAL A_lit_end) with (VAL (A_OBJ 24)) in Hv.
exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_bcmp) ABCMP G 0 ([] : list (Z * Z)) W (ms_regs ms1) (ms_mem ms1)
GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md ([] : list (Z * Z)) ly S hp _ 0
(LINE + js + 1) (VAL (A_OBJ 24)) 3 (-48) (Z_to_bv 64 (BASE + 14840)) HG eq_refl HJ0).
- rewrite T10, E8, E10, E18, !gfL_alu_add. f_equal. lia.
- rewrite T11, E265. reflexivity.
- exact T12.
- lia.
- lia.
- unfold ASAN_CEIL in *. lia.
- lia.
- lia.
- rewrite UspA. lia.
- reflexivity.
- lia.
- rewrite WS. unfold ESTACK. lia.
- rewrite T3, E3. exact Hgpc.
- rewrite T4, E4. exact Htpc.
- exact T1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (LINE + js + 1 + Z.of_nat (Z.to_nat (a - (LINE + js + 1)))) by lia.
    rewrite GAW by lia. discriminate.
  + rewrite UspA. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 24%nat (a - VAL (A_OBJ 24)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi]. split.
  + replace a with (VAL (A_OBJ 24) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 24)))) by lia.
    rewrite LITE by lia. discriminate.
  + rewrite UspA. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- intros a Ha. destruct (LITLO 24%nat (a - VAL (A_OBJ 24)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
  unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
- apply (amem_range_of_block_x SEGS B ARx LAWS ly S hp W (ms_mem ms1) _ q k (LINE + js + 1) 3 HARc Hq); lia.
- apply amem_range_high; [lia | left; lia | unfold ASAN_CEIL in *; lia].
- apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms1) _ q k (LINE + js + 1) 3 HARc Hq); lia.
- intros _. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem ms1) _ q k (LINE + js + 1) 3 HARc Hq); lia.
- exact (proj1 (HLITE ly S hp W (ms_mem ms1) _ HARc)).
- intros Hn0. exact (proj2 (HLITE ly S hp W (ms_mem ms1) _ HARc) Hn0). }
cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2).
jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
    unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
  - intros a Ha. exfalso. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (ENVa : gf_env Ea regsc regs).
{ rewrite HEa. apply gf_env_havoc; [exact ENV0 | lia | rewrite length_map; cbv; lia]. }
assert (HEIa : img_env VAL A_LIM Ea) by exact (proj1 ENVa).
assert (OLDa : forall n, (n < 38)%nat -> ew Ea n = ew E n)
by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
clear HEa.
assert (SHOKa : sh_ok SEGS Bxf gf_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, gf_SH; constructor).
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs - 48) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp).
assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha Hno.
rewrite (Hfr2 a Ha ltac:(unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
apply KEEPA; [exact Ha | exact Hno]. }
assert (PRESB : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
by (intros a Hp; apply Hpres2; apply PRESA; exact Hp).
assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64)
by (pose proof (bv_unsigned_in_range 64 v) as Hr0; change (bv_modulus 64) with (2 ^ 64) in Hr0; lia).
prreg HS (10%bv : bv 5) R10.
assert (F42 : ew Ea 42 = Z_to_bv 64 (bv_unsigned v))
by (rewrite Z_to_bv_bv_unsigned, <- R10; exact Hres).
assert (CMPE : v = w64 0 <-> skipn (Datatypes.S (Z.to_nat js)) (bzs ln) = RelayModel.W_END).
{ rewrite Hcmp. split.
  - intros Hall. apply gfL_eq_of_nth.
    + rewrite LWE. apply Nat2Z.inj. rewrite WLEN. lia.
    + intros i Hi. rewrite LWE in Hi. rewrite gfL_nth_skipn.
      specialize (Hall (Z.of_nat i) ltac:(lia)).
      rewrite (GAW i ltac:(lia)), (LITE i ltac:(lia)) in Hall. injection Hall as Hall. exact Hall.
  - intros HW i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (GAW (Z.to_nat i) ltac:(lia)), (LITE (Z.to_nat i) ltac:(lia)).
    f_equal. rewrite <- HW, gfL_nth_skipn. reflexivity. }
psrr_branch_tok RUNG BRR HS SHOKa Bspan.
* (* the word is "end": look the key up among the held ones *)
  rewrite branch_eq_U, (U_atom Ea 42 (bv_unsigned v) F42 Hvr), U_lit in Hc by lia.
  assert (Hv0 : v = w64 0).
  { apply bv_eq. destruct (Z.eqb_spec (bv_unsigned v) 0) as [E0|E0]; [|discriminate Hc].
    rewrite E0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (WEND : skipn (Datatypes.S (Z.to_nat js)) (bzs ln) = RelayModel.W_END)
  by (apply (proj1 CMPE); exact Hv0).
  assert (GEND : RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, firstn (Z.to_nat js) (bzs ln))).
  { rewrite GJ, WEND,
    (GM.eqb_len RelayModel.W_END RelayModel.W_BEGIN ltac:(rewrite LWE, LWB; discriminate)),
    (proj2 (GM.eqb_true RelayModel.W_END RelayModel.W_END) eq_refl). reflexivity. }
  clear Hc.
  paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa Bspan AF_fr_list_find.
  { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
  gf_name HS msE.
  gf_kp HS W regs mem KEEPB PRESB mem2 KEEPE PRESE.
  pmkst HS.
  prreg HS (1%bv : bv 5) Y1. prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3.
  prreg HS (4%bv : bv 5) Y4. prreg HS (8%bv : bv 5) Y8.
  prreg HS (10%bv : bv 5) Y10. prreg HS (11%bv : bv 5) Y11. prreg HS (12%bv : bv 5) Y12.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (gf_lfind_call_xR W ly S hp regs mem md HA LINE ln H js q k (ms_regs msE) (ms_mem msE) _ _
      (Z_to_bv 64 (BASE + 14892)) HJ2 SP47 BLK IMG HL FPLO ABL HinG HZS HA8 GL LN Hq Hq1 Hq2
      ltac:(lia) KEEPE PRESE).
    - unfold spZ. rewrite Y2, (OLDa 2%nat ltac:(lia)). exact Usp.
    - rewrite Y3, (OLDa 3%nat ltac:(lia)), E3. exact Hgpc.
    - rewrite Y4, (OLDa 4%nat ltac:(lia)), E4. exact Htpc.
    - exact Y1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - rewrite Y8, (OLDa 8%nat ltac:(lia)), E8. reflexivity.
    - rewrite Y10, (OLDa 9%nat ltac:(lia)), E9, unsigned_lit_small by lia. reflexivity.
    - rewrite Y11, (OLDa 8%nat ltac:(lia)), E8. reflexivity.
    - rewrite Y12, (OLDa 10%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)), E10, E18, gfL_alu_add.
      apply gfL_bv_mod. rewrite gfL_unsigned_mod, <- Z.add_assoc, Zplus_mod_idemp_l. f_equal. lia. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & k3 & -> & HJ3 & HP3 & HPR3 & HK3 & HRES3).
  jafter_call_keep_pi HS 54%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
  match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspa.
    - intros a Ha. apply (mbyte_of_aview SEGS). apply HK3;
      unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
    - intros a Ha. exfalso. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
  remember (havoc Ea 54 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
  assert (ENVb : gf_env Eb regsc regs).
  { rewrite HEb. apply gf_env_havoc; [exact ENVa | lia | rewrite length_map; cbv; lia]. }
  assert (HEIb : img_env VAL A_LIM Eb) by exact (proj1 ENVb).
  assert (OLDb : forall n, (n < 54)%nat -> ew Eb n = ew Ea n)
  by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
  clear HEb.
  assert (SHOKb : sh_ok SEGS Bxf gf_SH Eb (mrestrict (w_H W) mem3)) by (unfold sh_ok, gf_SH; constructor).
  assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
  { intros a Ha Hno.
    rewrite (HK3 a Ha ltac:(unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
    apply KEEPE; [exact Ha | exact Hno]. }
  assert (PRESF : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem3 a)
  by (intros a Hp; apply HPR3; apply PRESE; exact Hp).
  prreg HS (10%bv : bv 5) R10b.
  destruct HRES3 as [(j & HM & Hj10) | (HNM & Hm1)].
  -- assert (Hjlt : 0 <= Z.of_nat j < 2 ^ 63).
    { destruct HM as (Hjl & _). pose proof HL as (_ & _ & _ & _ & L5 & _). unfold hl_n in L5. lia. }
    assert (F58 : ew Eb 58 = Z_to_bv 64 (Z.of_nat j)) by (rewrite <- R10b; exact Hj10).
    psrr_branch_tok RUNG BRR HS SHOKb Bspan.
    ++ exfalso. rewrite (gfL_bt_atom BC_LT Eb 58 _ F58), gfL_blt_nat in Hc by lia. discriminate Hc.
    ++ (* the key is held at j: drop it *)
      clear Hc.
      paj_run_to_tok_xR RUNTOG HS HJ3 SHOKb Bspan AF_fr_list_drop.
      { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
      gf_name HS msD.
      gf_kp HS W regs mem KEEPF PRESF mem3 KEEPD PRESD.
      pmkst HS.
      destruct (gf_ret_regs _ _ _ _ _ regs HS ENVb Hspc H3c H4c HC2027
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [PRVD RVD1].
      prreg HS (10%bv : bv 5) D10. prreg HS (11%bv : bv 5) D11.
      eapply (gf_drop_tail_xR W ly S hp regs mem md ch HA ln H js (ms_regs msD) (ms_mem msD) _ _ j kr
        HPRE HJ3 BLK IMG HL ND FPLO ABL HinG HZS HA8 HAREC MOK HRM (gm_cnt_drop _ _ HCNT) HROM KEEPD PRESD PRVD RVD1).
      ** rewrite D10, (OLDb 9%nat ltac:(lia)), (OLDa 9%nat ltac:(lia)), E9, unsigned_lit_small by lia.
         reflexivity.
      ** rewrite D11, F58. reflexivity.
      ** exact HM.
      ** exact GEND.
  -- assert (F58 : ew Eb 58 = Z_to_bv 64 (-1)) by (rewrite <- R10b; exact Hm1).
    psrr_branch_tok RUNG BRR HS SHOKb Bspan.
    ++ (* the key is not held: nothing to do *)
      clear Hc.
      paj_run_tok_xR RUNG HS HJ3 SHOKb Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
      assert (HKNI : ~ In (firstn (Z.to_nat js) (bzs ln)) (texts H))
      by (rewrite <- gfL_bzs_firstn; exact (gfL_notin_texts H _ HNM)).
      pose proof (gf_cost_end_out MT H ln _ GEND HKNI) as COST0.
      gf_ret_tail_xR RET HS W regs mem KEEPF PRESF mem3 ENVb HJ3 Hspc H3c H4c HC2027 HPRE HL ND FPLO ABL COST0 HRM.
      apply (GM.upd_end_out _ _ _ GEND). exact HKNI.
    ++ exfalso. rewrite (gfL_bt_atom BC_LT Eb 58 _ F58), gfL_blt_m1 in Hc. discriminate Hc.
* (* the word is 3 bytes but not "end": no gesture *)
  rewrite branch_eq_U, (U_atom Ea 42 (bv_unsigned v) F42 Hvr), U_lit in Hc by lia.
  assert (WNE : skipn (Datatypes.S (Z.to_nat js)) (bzs ln) <> RelayModel.W_END).
  { intros HW. pose proof (proj2 CMPE HW) as Hv0. rewrite Hv0 in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. cbn in Hc. discriminate Hc. }
  assert (LSK3 : length (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) = 3%nat)
  by (apply Nat2Z.inj; rewrite WLEN; lia).
  assert (GNONE : RelayModel.gesture (bzs ln) = None).
  { rewrite GJ, (GM.eqb_len (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_BEGIN
      ltac:(rewrite LSK3, LWB; discriminate)).
    destruct (RelayModel.list_eqb (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_END) eqn:Ee;
    [exfalso; apply WNE; apply GM.eqb_true; exact Ee | reflexivity]. }
  clear Hc.
  paj_run_tok_xR RUNG HS HJ2 SHOKa Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
  pose proof (gf_cost_none MT H ln GNONE) as COST0.
  gf_ret_tail_xR RET HS W regs mem KEEPB PRESB mem2 ENVa HJ2 Hspc H3c H4c HC2027 HPRE HL ND FPLO ABL COST0 HRM.
  apply GM.upd_none. exact GNONE.
+ (* the word is not 3 bytes: it can only be "begin" (5 bytes) *)
  rewrite branch_eq_U, (gfL_U_neg E 10 _ E10 ltac:(lia)), U_lit in Hc by lia.
  assert (HW3n : Z.of_nat (length ln) <> js + 4)
  by (destruct (Z.eqb_spec (- (js + 1 - Z.of_nat (length ln))) 3); [discriminate | lia]).
  clear Hc.
  paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
  gf_name HS msB.
  gf_kp HS W regs mem KEEP2 PRES2 (ms_mem ms0) KEEPB0 PRESB0.
  psrr_branch_tok RUNG BRR HS SHOK Bspan.
  * (* the word is neither 3 nor 5 bytes: no gesture *)
    rewrite branch_ne_U, (gfL_U_neg E 10 _ E10 ltac:(lia)), U_lit in Hc by lia.
    assert (HW5n : Z.of_nat (length ln) <> js + 6)
    by (destruct (Z.eqb_spec (- (js + 1 - Z.of_nat (length ln))) 5); [cbn in Hc; discriminate | lia]).
    clear Hc.
    assert (GNONE : RelayModel.gesture (bzs ln) = None).
    { rewrite GJ,
      (GM.eqb_len (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_BEGIN
        ltac:(rewrite LWB; intros HE; apply (f_equal Z.of_nat) in HE; rewrite WLEN in HE; lia)),
      (GM.eqb_len (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_END
        ltac:(rewrite LWE; intros HE; apply (f_equal Z.of_nat) in HE; rewrite WLEN in HE; lia)).
      reflexivity. }
    paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
    pose proof (gf_cost_none MT H ln GNONE) as COST0.
    gf_ret_tail_xR RET HS W regs mem KEEPB0 PRESB0 (ms_mem msB) ENV0 HJ0 Hspc H3c H4c HC2027
      HPRE HL ND FPLO ABL COST0 HRM.
    apply GM.upd_none. exact GNONE.
  * (* the word is 5 bytes: compare it with "begin" *)
    rewrite branch_ne_U, (gfL_U_neg E 10 _ E10 ltac:(lia)), U_lit in Hc by lia.
    assert (HW5 : Z.of_nat (length ln) = js + 6)
    by (destruct (Z.eqb_spec (- (js + 1 - Z.of_nat (length ln))) 5); [lia | cbn in Hc; discriminate]).
    clear Hc.
    assert (LSK5 : length (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) = 5%nat)
    by (apply Nat2Z.inj; rewrite WLEN; lia).
    paj_run_tok_xR RUNG HS HJ0 SHOK Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
    gf_name HS msC.
    gf_kp HS W regs mem KEEPB0 PRESB0 (ms_mem msB) KEEPC PRESC.
    pmkst HS.
    prreg HS (1%bv : bv 5) T1b. prreg HS (2%bv : bv 5) T2b. prreg HS (3%bv : bv 5) T3b.
    prreg HS (4%bv : bv 5) T4b. prreg HS (10%bv : bv 5) T10b. prreg HS (11%bv : bv 5) T11b.
    prreg HS (12%bv : bv 5) T12b.
    assert (UspC : spZ (ms_regs msC) = spZ regs - 48) by (unfold spZ; rewrite T2b, Usp; reflexivity).
    pose proof HJ0 as HARc2. apply ajournal_gx_AR_xR in HARc2.
    assert (GAW5 : forall i, (i < 5)%nat ->
    aview SEGS (w_H W) (ms_mem msC) (LINE + js + 1 + Z.of_nat i)
    = Some (nth (Datatypes.S (Z.to_nat js) + i)%nat (bzs ln) 0)).
    { intros i Hi. destruct (BLK q k (LINE + js + 1 + Z.of_nat i) Hq ltac:(lia)) as [Ha0 Hahi].
      rewrite (KEEPC (LINE + js + 1 + Z.of_nat i) ltac:(lia) ltac:(lia)).
      replace (LINE + js + 1 + Z.of_nat i) with (LINE + Z.of_nat (Datatypes.S (Z.to_nat js) + i)) by lia.
      apply GA. lia. }
    assert (LITB : forall i, (i < 5)%nat ->
    aview SEGS (w_H W) (ms_mem msC) (VAL (A_OBJ 23) + Z.of_nat i) = Some (nth i RelayModel.W_BEGIN 0)).
    { intros i Hi. destruct (LITLO 23%nat (Z.of_nat i) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
      rewrite (KEEPC (VAL (A_OBJ 23) + Z.of_nat i) ltac:(lia) ltac:(lia)).
      destruct (LB i ltac:(vm_compute; lia)) as [Hv Hr].
      change (VAL A_lit_begin) with (VAL (A_OBJ 23)) in Hv.
      exact (aview_of_val_mem1 SEGS (w_H W) mem _ _ Hv Hr). }
    eapply (SRrG_bind SEGS R R_trans).
    { eapply (aj_bcmp_gx_at_xR B PST ARx LAWS R_trans WLE_R (SIGMA WS_bcmp) ABCMP G 0 ([] : list (Z * Z)) W (ms_regs msC) (ms_mem msC)
      GM_STK (spZ regs) (blk_FP (list_blks H)) ly S hp W mem md ([] : list (Z * Z)) ly S hp _ 0
      (LINE + js + 1) (VAL (A_OBJ 23)) 5 (-48) (Z_to_bv 64 (BASE + 14756)) HG eq_refl HJ0).
      - rewrite T10b, E8, E10, E18, !gfL_alu_add. f_equal. lia.
      - rewrite T11b, E264. reflexivity.
      - exact T12b.
      - lia.
      - lia.
      - lia.
      - lia.
      - lia.
      - rewrite UspC. lia.
      - reflexivity.
      - lia.
      - rewrite WS. unfold ESTACK. lia.
      - rewrite T3b, E3. exact Hgpc.
      - rewrite T4b, E4. exact Htpc.
      - exact T1b.
      - apply ret_ok_codeptr_v; [lia | reflexivity].
      - intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi]. split.
        + replace a with (LINE + js + 1 + Z.of_nat (Z.to_nat (a - (LINE + js + 1)))) by lia.
          rewrite GAW5 by lia. discriminate.
        + rewrite UspC. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      - intros a Ha. destruct (LITLO 23%nat (a - VAL (A_OBJ 23)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi]. split.
        + replace a with (VAL (A_OBJ 23) + Z.of_nat (Z.to_nat (a - VAL (A_OBJ 23)))) by lia.
          rewrite LITB by lia. discriminate.
        + rewrite UspC. unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      - intros a Ha. destruct (BLK q k a Hq ltac:(lia)) as [Ha0 Hahi].
        unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      - intros a Ha. destruct (LITLO 23%nat (a - VAL (A_OBJ 23)) ltac:(lia) ltac:(lia)) as [Ha0 Hahi].
        unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *. lia.
      - apply (amem_range_of_block_x SEGS B ARx LAWS ly S hp W (ms_mem msC) _ q k (LINE + js + 1) 5 HARc2 Hq); lia.
      - apply amem_range_high; [lia | left; lia | unfold ASAN_CEIL in *; lia].
      - apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem msC) _ q k (LINE + js + 1) 5 HARc2 Hq); lia.
      - intros _. apply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W (ms_mem msC) _ q k (LINE + js + 1) 5 HARc2 Hq); lia.
      - exact (proj1 (HLITB ly S hp W (ms_mem msC) _ HARc2)).
      - intros Hn0. exact (proj2 (HLITB ly S hp W (ms_mem msC) _ HARc2) Hn0). }
    cbv beta. intros W2 c2 Hwle2 (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2).
    jafter_call_keep_pi HS 38%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
    match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
    { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
      split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
      - intros a Ha. apply (mbyte_of_aview SEGS). apply Hfr2;
        unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
      - intros a Ha. exfalso. lia. }
    clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
    remember (havoc E 38 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
    assert (ENVa : gf_env Ea regsc regs).
    { rewrite HEa. apply gf_env_havoc; [exact ENV0 | lia | rewrite length_map; cbv; lia]. }
    assert (HEIa : img_env VAL A_LIM Ea) by exact (proj1 ENVa).
    assert (OLDa : forall n, (n < 38)%nat -> ew Ea n = ew E n)
    by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
    clear HEa.
    assert (SHOKa : sh_ok SEGS Bxf gf_SH Ea (mrestrict (w_H W) mem2)) by (unfold sh_ok, gf_SH; constructor).
    assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs - 48) by (rewrite (OLDa 2%nat ltac:(lia)); exact Usp).
    assert (KEEPB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
    aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
    { intros a Ha Hno.
      rewrite (Hfr2 a Ha ltac:(unfold ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
      apply KEEPC; [exact Ha | exact Hno]. }
    assert (PRESB : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a)
    by (intros a Hp; apply Hpres2; apply PRESC; exact Hp).
    assert (Hvr : 0 <= bv_unsigned v < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 64 v) as Hr0; change (bv_modulus 64) with (2 ^ 64) in Hr0; lia).
    prreg HS (10%bv : bv 5) R10.
    assert (F42 : ew Ea 42 = Z_to_bv 64 (bv_unsigned v))
    by (rewrite Z_to_bv_bv_unsigned, <- R10; exact Hres).
    assert (CMPB : v = w64 0 <-> skipn (Datatypes.S (Z.to_nat js)) (bzs ln) = RelayModel.W_BEGIN).
    { rewrite Hcmp. split.
      - intros Hall. apply gfL_eq_of_nth.
        + rewrite LWB, LSK5. reflexivity.
        + intros i Hi. rewrite LWB in Hi. rewrite gfL_nth_skipn.
          specialize (Hall (Z.of_nat i) ltac:(lia)).
          rewrite (GAW5 i ltac:(lia)), (LITB i ltac:(lia)) in Hall. injection Hall as Hall. exact Hall.
      - intros HW i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
        rewrite (GAW5 (Z.to_nat i) ltac:(lia)), (LITB (Z.to_nat i) ltac:(lia)).
        f_equal. rewrite <- HW, gfL_nth_skipn. reflexivity. }
    psrr_branch_tok RUNG BRR HS SHOKa Bspan.
    -- (* the word is not "begin": no gesture *)
      rewrite branch_ne_U, (U_atom Ea 42 (bv_unsigned v) F42 Hvr), U_lit in Hc by lia.
      assert (WNB : skipn (Datatypes.S (Z.to_nat js)) (bzs ln) <> RelayModel.W_BEGIN).
      { intros HW. pose proof (proj2 CMPB HW) as Hv0. rewrite Hv0 in Hc.
        unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia. cbn in Hc. discriminate Hc. }
      assert (GNONE : RelayModel.gesture (bzs ln) = None).
      { rewrite GJ.
        rewrite (GM.eqb_len (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_END
          ltac:(rewrite LSK5, LWE; discriminate)).
        destruct (RelayModel.list_eqb (skipn (Datatypes.S (Z.to_nat js)) (bzs ln)) RelayModel.W_BEGIN) eqn:Ee;
        [exfalso; apply WNB; apply GM.eqb_true; exact Ee | reflexivity]. }
      clear Hc.
      paj_run_tok_xR RUNG HS HJ2 SHOKa Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
      pose proof (gf_cost_none MT H ln GNONE) as COST0.
      gf_ret_tail_xR RET HS W regs mem KEEPB PRESB mem2 ENVa HJ2 Hspc H3c H4c HC2027
        HPRE HL ND FPLO ABL COST0 HRM.
      apply GM.upd_none. exact GNONE.
    -- (* the word is "begin": push the key if it is not held *)
      rewrite branch_ne_U, (U_atom Ea 42 (bv_unsigned v) F42 Hvr), U_lit in Hc by lia.
      assert (Hv0 : v = w64 0).
      { apply bv_eq. destruct (Z.eqb_spec (bv_unsigned v) 0) as [E0|E0]; [|cbn in Hc; discriminate Hc].
        rewrite E0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
      assert (WBEG : skipn (Datatypes.S (Z.to_nat js)) (bzs ln) = RelayModel.W_BEGIN)
      by (apply (proj1 CMPB); exact Hv0).
      assert (GBEG : RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, firstn (Z.to_nat js) (bzs ln))).
      { rewrite GJ, WBEG, (proj2 (GM.eqb_true RelayModel.W_BEGIN RelayModel.W_BEGIN) eq_refl). reflexivity. }
      clear Hc.
      paj_run_to_tok_xR RUNTOG HS HJ2 SHOKa Bspan AF_fr_list_find.
      { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
      gf_name HS msE.
      gf_kp HS W regs mem KEEPB PRESB mem2 KEEPE PRESE.
      pmkst HS.
      prreg HS (1%bv : bv 5) Y1. prreg HS (2%bv : bv 5) Y2. prreg HS (3%bv : bv 5) Y3.
      prreg HS (4%bv : bv 5) Y4. prreg HS (8%bv : bv 5) Y8.
      prreg HS (10%bv : bv 5) Y10. prreg HS (11%bv : bv 5) Y11. prreg HS (12%bv : bv 5) Y12.
      eapply (SRrG_bind SEGS R R_trans).
      { eapply (gf_lfind_call_xR W ly S hp regs mem md HA LINE ln H js q k (ms_regs msE) (ms_mem msE) _ _
          (Z_to_bv 64 (BASE + 14780)) HJ2 SP47 BLK IMG HL FPLO ABL HinG HZS HA8 GL LN Hq Hq1 Hq2
          ltac:(lia) KEEPE PRESE).
        - unfold spZ. rewrite Y2, (OLDa 2%nat ltac:(lia)). exact Usp.
        - rewrite Y3, (OLDa 3%nat ltac:(lia)), E3. exact Hgpc.
        - rewrite Y4, (OLDa 4%nat ltac:(lia)), E4. exact Htpc.
        - exact Y1.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - rewrite unsigned_lit_small by lia. lia.
        - rewrite Y8, (OLDa 8%nat ltac:(lia)), E8. reflexivity.
        - rewrite Y10, (OLDa 9%nat ltac:(lia)), E9, unsigned_lit_small by lia. reflexivity.
        - rewrite Y11, (OLDa 8%nat ltac:(lia)), E8. reflexivity.
        - rewrite Y12, (OLDa 10%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)), E10, E18, gfL_alu_add.
          apply gfL_bv_mod. rewrite gfL_unsigned_mod, <- Z.add_assoc, Zplus_mod_idemp_l. f_equal. lia. }
      cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & k3 & -> & HJ3 & HP3 & HPR3 & HK3 & HRES3).
      jafter_call_keep_pi HS 54%nat regs3 (mrestrict (w_H W) mem3) HP3 [0]%nat HS3.
      match type of HS3 with ?ty -> _ => assert (HRK : ty); [|specialize (HS3 HRK); clear HRK] end.
      { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
        split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Uspa.
        - intros a Ha. apply (mbyte_of_aview SEGS). apply HK3;
          unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
        - intros a Ha. exfalso. lia. }
      clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
      remember (havoc Ea 54 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
      assert (ENVb : gf_env Eb regsc regs).
      { rewrite HEb. apply gf_env_havoc; [exact ENVa | lia | rewrite length_map; cbv; lia]. }
      assert (HEIb : img_env VAL A_LIM Eb) by exact (proj1 ENVb).
      assert (OLDb : forall n, (n < 54)%nat -> ew Eb n = ew Ea n)
      by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
      clear HEb.
      assert (SHOKb : sh_ok SEGS Bxf gf_SH Eb (mrestrict (w_H W) mem3)) by (unfold sh_ok, gf_SH; constructor).
      assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
      aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
      { intros a Ha Hno.
        rewrite (HK3 a Ha ltac:(unfold LFIND_STK, LFIND_FRAME, ESTACK, GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia)).
        apply KEEPE; [exact Ha | exact Hno]. }
      assert (PRESF : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem3 a)
      by (intros a Hp; apply HPR3; apply PRESE; exact Hp).
      prreg HS (10%bv : bv 5) R10b.
      destruct HRES3 as [(j & HM & Hj10) | (HNM & Hm1)].
      ++ assert (Hjlt : 0 <= Z.of_nat j < 2 ^ 63).
         { destruct HM as (Hjl & _). pose proof HL as (_ & _ & _ & _ & L5 & _). unfold hl_n in L5. lia. }
         assert (F58 : ew Eb 58 = Z_to_bv 64 (Z.of_nat j)) by (rewrite <- R10b; exact Hj10).
         psrr_branch_tok RUNG BRR HS SHOKb Bspan.
         ** (* the key is already held: nothing to do *)
           clear Hc.
           paj_run_tok_xR RUNG HS HJ3 SHOKb Bspan. { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
           assert (HKIN : In (firstn (Z.to_nat js) (bzs ln)) (texts H)).
           { destruct (gfL_match_nth H (firstn (Z.to_nat js) ln) j HM) as [Hjl Hnj].
             rewrite <- gfL_bzs_firstn, <- Hnj. apply nth_In. exact Hjl. }
           pose proof (gf_cost_begin_in MT H ln _ GBEG HKIN) as COST0.
           gf_ret_tail_xR RET HS W regs mem KEEPF PRESF mem3 ENVb HJ3 Hspc H3c H4c HC2027
             HPRE HL ND FPLO ABL COST0 HRM.
           apply (GM.upd_begin_in _ _ _ GBEG). exact HKIN.
         ** exfalso. rewrite (gfL_bt_atom BC_GE Eb 58 _ F58), gfL_bge_nat in Hc by lia. discriminate Hc.
      ++ assert (F58 : ew Eb 58 = Z_to_bv 64 (-1)) by (rewrite <- R10b; exact Hm1).
         psrr_branch_tok RUNG BRR HS SHOKb Bspan.
         ** exfalso. rewrite (gfL_bt_atom BC_GE Eb 58 _ F58), gfL_bge_m1 in Hc. discriminate Hc.
         ** (* the key is new: push it *)
           clear Hc.
           paj_run_to_tok_xR RUNTOG HS HJ3 SHOKb Bspan AF_fr_list_push.
           { apply awr_ok_x_of0. intros a Ha. exfalso. revert Ha. gf_outw. }
           gf_name HS msP.
           gf_kp HS W regs mem KEEPF PRESF mem3 KEEPP PRESP.
           pmkst HS.
           destruct (gf_ret_regs _ _ _ _ _ regs HS ENVb Hspc H3c H4c HC2027
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [PRVP RVP1].
           prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
           eapply (gf_push_tail_xR W ly S hp regs mem md ch HA LINE ln H js q k (ms_regs msP) (ms_mem msP) _ _ kr
             HPRE HJ3 BLK IMG HL ND FPLO ABL HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 HGROW HROOM MOK
             HRM (gm_cnt_push H js _ HCNT) KEEPP PRESP PRVP RVP1).
           --- rewrite P10, (OLDb 9%nat ltac:(lia)), (OLDa 9%nat ltac:(lia)), E9, unsigned_lit_small by lia.
               reflexivity.
           --- rewrite P11, (OLDb 8%nat ltac:(lia)), (OLDa 8%nat ltac:(lia)), E8. reflexivity.
           --- rewrite P12, (OLDb 10%nat ltac:(lia)), (OLDb 18%nat ltac:(lia)),
                 (OLDa 10%nat ltac:(lia)), (OLDa 18%nat ltac:(lia)), E10, E18, gfL_alu_add.
               apply gfL_bv_mod. rewrite gfL_unsigned_mod, <- Z.add_assoc, Zplus_mod_idemp_l. f_equal. lia.
           --- lia.
           --- exact HNM.
           --- exact GBEG.
Qed.
End wR.
(* the strict texts are the R section's at R := wle: each R premise at wle is the strict hypothesis of the same role,
   and the three laws hold for wle *)
#[local] Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

(* A call to a program function inside this walk: W_gesture_end.v gx_callS (the donor's cl_callS, YC85.v:383,
   over ajournal_gx, composed with W_journal.v ajournal_gx_sub), restated here over ajournal_gx_x (the ghost lists
   after S / Sc / S2); o = 0 is a tail call. *)
Lemma gf_callS : forall G0 W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1
(o : Z) raw ch1 (K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
gx_ok SEGS B G0 ->
ajournal_gx_x SEGS B PST ARx G0 0 [] STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx_x SEGS B PST ARx G0 0 [] STK1 (spZ regsc) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
  aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
 in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 ajournal_gx_x SEGS B PST ARx G0 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
 ajournal_gx_x SEGS B PST ARx G0 0 [] STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof. eapply (gf_callS_xR (@wle SEGS)); wle_inst. Qed.
Lemma gf_frames : forall G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k,
ajournal_gx_x SEGS B PST ARx G0 XO OUT STK sp0 FP ly S Hp W mem md own ly' S' Hp' W' mem' md' k ->
frames S' = own ++ frames S.
Proof. eapply (gf_frames_xR (@wle SEGS)); wle_inst. Qed.
(* gesture_model's return when the held list does not change (H' = H): the post from the final state; no allocator
   call, so the charge is 0 (COST0, from the arm's gesture case) *)
Lemma gf_ret_post : forall W ly S Hp regs mem md ch HA (ln : list byte) H r m md2 mat' kk (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall rr, In rr (alist_fp (HA + 80) H) -> forall a, fst rr <= a < snd rr -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
gm_cost MT H ln = 0 ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W m md2 kk ->
aregs_preserved regs r -> getr r 1 = getr regs 1 ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) m a) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) m a = aview SEGS (w_H W) mem a) ->
RelayModel.upd (texts H) (bzs ln) = texts H ->
gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr W
(mkCfg (mkst r (v_jalr (getr r 1) 0) m (seg_rom SEGS)) (with_vm_backing (m_vm_lazy md2) mat' md2)).
Proof. eapply (gf_ret_post_xR (@wle SEGS)); wle_inst. Qed.

(* list_find (HA + 80, LINE, js) at 0x85ca4 / 0x85d14: gesture_model's sp - 48 is list_find's sp, and the
   key is the line's first js bytes (the bytes before its last space). *)
Lemma gf_lfind_call : forall W ly S Hp regs mem md HA LINE (ln : list byte) H (js q k : Z) regs1 mem1 md1 kc raw,
AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
spZ regs <= 2 ^ 47 ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 -> (HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> q <= LINE -> LINE + Z.of_nat (length ln) <= q + req_size k ->
0 <= js < Z.of_nat (length ln) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
spZ regs1 = spZ regs - 48 ->
getr regs1 3 = w64 (as_gp B) -> getr regs1 4 = w64 (as_tp B) ->
getr regs1 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regs1 8 = w64 LINE ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 LINE -> getr regs1 12 = w64 js ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_find)) mem1 (seg_rom SEGS)) md1)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2 k2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem2 md2 k2 /\
 aregs_preserved regs1 regs2 /\
 (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) /\
 (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 48 - LFIND_STK <= a < spZ regs - 48) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a) /\
 ((exists j, lfind_match H (firstn (Z.to_nat js) ln) j /\ getr regs2 10 = w64 (Z.of_nat j)) \/
  ((forall kk, (kk < length (hl_recs H))%nat -> snd (nth kk (hl_recs H) (0, [])) <> firstn (Z.to_nat js) ln) /\
   getr regs2 10 = Z_to_bv 64 (-1)))).
Proof. eapply (gf_lfind_call_xR (@wle SEGS)); wle_inst. Qed.

(* list_drop (HA + 80, j) by tail call at 0x85d3c: an "end" of the held key j *)
Lemma gf_drop_tail : forall W ly S Hp regs mem md ch HA (ln : list byte) H (js : Z) regs1 mem1 md1 kc j (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 -> (HA + 80) mod 8 = 0 ->
AREC * hl_cap H < 2 ^ 32 -> mo_ok MT S (gm_cost MT H ln) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> cnt_ok_pk RP ldrop_pk (ablocks B ly S) ->
rom_view SEGS W mem ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
aregs_preserved regs regs1 -> getr regs1 1 = getr regs 1 ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 (Z.of_nat j) ->
lfind_match H (firstn (Z.to_nat js) ln) j ->
RelayModel.gesture (bzs ln) = Some (RelayModel.GEnd, firstn (Z.to_nat js) (bzs ln)) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_drop)) mem1 (seg_rom SEGS)) md1)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
Proof. eapply (gf_drop_tail_xR (@wle SEGS)); wle_inst. Qed.

(* list_push (HA + 80, LINE, js) by tail call at 0x85cd0: a "begin" of a key not held *)
Lemma gf_push_tail : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H (js q k : Z) regs1 mem1 md1 kc (kr : nat),
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
AJG GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W mem1 md1 kc ->
(forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall a, in_img SEGS a -> 0 <= a /\ a < spZ regs - GM_STK) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall r, In r (alist_fp (HA + 80) H) -> forall a, fst r <= a < snd r -> 0 <= a /\ a < spZ regs - GM_STK) ->
(forall b, In b (alist_blks H) -> In b (ablocks B ly S)) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
(lp_grow H = true -> lp_vbytes H < MMAX) ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) -> cnt_ok_pk RP (lp_peak H js) (ablocks B ly S) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) mem1 a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) ->
aregs_preserved regs regs1 -> getr regs1 1 = getr regs 1 ->
getr regs1 10 = w64 (HA + 80) -> getr regs1 11 = w64 LINE -> getr regs1 12 = w64 js ->
0 <= js < Z.of_nat (length ln) ->
(forall kk, (kk < length (hl_recs H))%nat -> snd (nth kk (hl_recs H) (0, [])) <> firstn (Z.to_nat js) ln) ->
RelayModel.gesture (bzs ln) = Some (RelayModel.GBegin, firstn (Z.to_nat js) (bzs ln)) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AF_fr_list_push)) mem1 (seg_rom SEGS)) md1)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
Proof. eapply (gf_push_tail_xR (@wle SEGS)); wle_inst. Qed.

(* a return through the epilogue with the held list unchanged; leaves the model goal upd (texts H) _ = texts H *)
Ltac gf_ret_tail RETv HS Wv regsv memv KO PO mo ENVx HJx Hspc H3c H4c HC HPRE HL ND FPLO ABL COST0 HRMx :=
let KN := fresh "KN" in let PN := fresh "PN" in let PRV := fresh "PRV" in let RV1 := fresh "RV1" in
let mat := fresh "mat" in
gf_kp HS Wv regsv memv KO PO mo KN PN;
destruct (gf_ret_regs _ _ _ _ _ regsv HS ENVx Hspc H3c H4c HC ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity)) as [PRV RV1];
eapply (RETv _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat;
apply (gf_ret_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat _ _ HPRE HL ND FPLO ABL COST0 HRMx HJx PRV RV1 PN KN).

Lemma pb_gm_found_x : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
Proof. eapply (pb_gm_found_xR (@wle SEGS)); wle_inst. Qed.
End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): gm_found's statement is the AR walk's,
   unchanged, now a corollary of pb_gm_found_x at ARx := ARi0 (cgif's AR with the head set empty), PST := [].  The
   Section takes LX0 (the laws at ARi0, a Theorem Labs lane's rulings (a) and HP0) in place of LAWS; HP0 at ARi0 is ARi0_hp0;
   the callees' AR contracts become their generic ones at ARi0 through the kit's bridges (W_contract_x
   lfind_spec_x_of_AR0 / lp_spec_x_of_AR0 / ldrop_spec_x_of_AR0 / ashp_x_ARi0_of, W_sites_x abcmp_realizes_x_of_AR0);
   the entry, the journal and the post through W_journal_x afn_pre_x_ARi0_of_AR / ajournal_gx_AR_x_ARi0 and
   W_contract_x gm_post_x_AR0. ---- *)
Section r.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec B G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec B MT G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec B MT G (BASE + AF_fr_list_drop).
Hypothesis HLITG : ashp B (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp B (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp B (VAL A_lit_end) 3.
Lemma gm_found : forall W ly S regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre SEGS B GM_STK ly S W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx SEGS B G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S W mem md [] ly S W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js + 1 - Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post B MT G regs ly S W mem md HA H ln).
Proof.
intros W ly S regs mem md ch HA LINE ln H q k js regsc memc mdc HPRE. intros.
pose proof (ARi0_hp0 SEGS B) as HP0.
pose proof (abcmp_realizes_x_of_AR0 SEGS B _ ABCMP) as ABCMPx.
pose proof (lfind_spec_x_of_AR0 B _ _ LFIND) as LFINDx.
pose proof (lp_spec_x_of_AR0 B _ _ _ _ LPUSH) as LPUSHx.
pose proof (ldrop_spec_x_of_AR0 B _ _ _ LDROP) as LDROPx.
pose proof (ashp_x_ARi0_of B _ _ HLITB) as HLITBx. pose proof (ashp_x_ARi0_of B _ _ HLITE) as HLITEx.
pose proof (afn_pre_x_ARi0_of_AR SEGS B _ _ _ _ _ _ _ _ HPRE) as HPREx.
lazymatch goal with HJ : context [@W_journal.ajournal_gx] |- _ =>
  pose proof HJ as HJx; apply ajournal_gx_AR_x_ARi0 with (Hp := []) in HJx end.
eapply SRr_mono.
{ eapply (pb_gm_found_x B MT RP_AR MMAX G [] (ARi0 SEGS B)) with (kr := 0%nat); try eassumption.
  all: first [exact (rp_RM_AR _ _) | apply cnt_ok_pk_AR; unfold gm_pk; cbn; lia]. }
cbv beta. intros W2 c2 _ HQ. exact (gm_post_x_AR0 B MT G regs ly S [] W mem md HA H ln _ W2 c2 HQ).
Qed.
End r.
End b.
End a.
