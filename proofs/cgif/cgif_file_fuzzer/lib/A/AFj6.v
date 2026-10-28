(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YI04.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d AFhy AFi1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma Zbv_add_unsigned : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
intros x k. apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma unwind_of_chain_length : forall pc0 ch, (1 <= length (unwind_of_chain pc0 ch) <= 30)%nat.
Proof.
intros pc0 ch. unfold unwind_of_chain, kUnwindMax. rewrite firstn_length. cbn [length]. lia.
Qed.
Lemma val_mem_addr : forall m a a' (n : nat) v, val_mem tfibsegs m a n v -> a = a' -> val_mem tfibsegs m a' n v.
Proof. intros m a a' n v H <-. exact H. Qed.
Lemma le_byte_zero : forall w k, YO0f.le_byte 0 w k = 0.
Proof. intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia). rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma land_m8_64 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 8) = a - a mod 8.
Proof.
intros a Ha. change (2 ^ 64 - 8) with (Z.land (- 2 ^ 3) (Z.ones 64)).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(lia)). apply Z.mod_small. lia.
Qed.
Lemma land_m8_48 : forall a, 0 <= a < 2 ^ 48 -> Z.land a (2 ^ 48 - 8) = a - a mod 8.
Proof.
intros a Ha. change (2 ^ 48 - 8) with (Z.land (- 2 ^ 3) (Z.ones 48)).
rewrite Z.land_assoc, Z.land_ones by lia. rewrite land_neg_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(lia)). apply Z.mod_small. lia.
Qed.
Lemma div8_bounds : forall x, 0 <= x -> 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.
Lemma land_7_mod : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma lxor_ones64 : forall u, 0 <= u < 2 ^ 64 -> Z.lxor u (2 ^ 64 - 1) = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. change (2 ^ 64 - 1) with (Z.ones 64).
assert (D : Z.ldiff u (Z.ones 64) = 0).
{ destruct (Z.eq_dec u 0) as [->|Hnz]; [reflexivity|]. apply Z.ldiff_ones_r_low; [lia|]. apply Z.log2_lt_pow2; lia. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) u D).
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit u i); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite (Z.bits_above_log2 u i); [reflexivity| lia |].
destruct (Z.eq_dec u 0) as [->|Hnz]; [cbn; lia|]. apply (Z.lt_le_trans _ 64); [apply Z.log2_lt_pow2; lia | lia].
Qed.
Definition hdr_byte1 (jb : Z) : Z :=
zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (jb + 0)) (zcanon (-4)))) (zcanon 1))) (zcanon 143))) (zcanon 16))) (zcanon 243))) (zcanon 0)).
Lemma hdr_byte1_ok : forall jb, 0 <= jb <= 255 -> 0 <= hdr_byte1 jb < 256 /\ Z.land (hdr_byte1 jb) 127 = 17.
Proof.
intros jb Hjb.
assert (C : forallb (fun i => let b := hdr_byte1 (Z.of_nat i) in (0 <=? b) && (b <? 256) && (Z.land b 127 =? 17)) (seq 0 256) = true) by (vm_compute; reflexivity).
pose proof (forallb_seq_In _ 256 (Z.to_nat jb) C ltac:(lia)) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by lia.
apply andb_prop in Hx as [Hx H3]. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.
Lemma chunk_val_at : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YP09.r_chunks r) j = Some (YP09.mkChunk off (CVal n e)) ->
a = base_val E (YP09.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfibsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
Lemma ltHAV (k : nat) : Nat.ltb k aHAV = true -> (k < aHAV)%nat.
Proof. intros H. apply Nat.ltb_lt. exact H. Qed.
Lemma st_ok_forget2 : forall k E ss ss' (H : word -> bool) ms (clob : list (bv 5)),
st_ok tfibsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss) = ss' ->
st_ok tfibsegs (havoc E k (map (getr (ms_regs ms)) clob)) ss' (restrict H ms).
Proof.
intros k E ss ss' H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz <-.
pose proof (st_ok_forget k E ss H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz) as X.
rewrite <- (st_ok_restrict_mkst tfibsegs H E ss ms HS Hrv) in X. exact X.
Qed.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; zlia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with t end;
apply U_eq_by_zev; [reflexivity | reflexivity |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ reflexivity | reflexivity | cbn [base_val YP09.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := eval vm_compute in p in change p with q end
| cbn; lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := eval vm_compute in (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
eq_refl eq_refl ltac:(vm_compute; reflexivity)) as HS2; clear HS; rename HS2 into HS
end.
Lemma Forall_nth' {A} (P : A -> Prop) (l : list A) (i : nat) (x : A) : Forall P l -> nth_error l i = Some x -> P x.
Proof. intros HF He. exact (proj1 (Forall_forall P l) HF x (nth_error_In l i He)). Qed.
Lemma pairwise_ij {A} (R : A -> A -> Prop) : forall (l : list A) (i j : nat) (x y : A),
pairwise R l -> nth_error l i = Some x -> nth_error l (i + S j)%nat = Some y -> R x y.
Proof.
induction l as [|a l IH]; intros i j x y HP Hi Hj; [destruct i; discriminate|].
destruct HP as [HF HP]. destruct i as [|i]; cbn in Hi, Hj.
- injection Hi as <-. exact (Forall_nth' _ l j y HF Hj).
- exact (IH i j x y HP Hi Hj).
Qed.
Lemma zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. lia. Qed.
Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Section g.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (cl cnt v csz j0 jb j1 j2 j3 j4 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Definition RZ : Z := 16.
Definition NPv : Z := Z.max n 1.
Definition R8v : Z := (Z.max n 8 + 7) / 8 * 8.
Definition N8D : Z := NPv / 8 * 8.
Definition Pv : Z := T + t_cache + 80 * cl.
Definition PVv : Z := Pv + 16 + 4 * (cnt - 1).
Definition Kv : Z := SB + cl * 2 ^ 32 + 16 * v.
Definition SHBv : Z := 0x7fff8000.
Definition SKv : Z := SHBv + Kv / 8.
Definition SSLOTv : Z := T + t_stats + 112 + 8 * cl.
Definition PBv : Z := SHBv + (Kv + RZ + N8D) / 8.
Definition Uv : Z := Kv + RZ.
Definition SUv : Z := SHBv + Uv / 8.
Definition FILv : Z := NPv.
Definition NDv : Z := R8v + RZ.
Definition tr : list Z := call_trace ly 0x52bcc regs0 ch.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 (Z.of_nat (length tr)); w64 j0; w64 R8v; w64 cl;
w64 Pv; w64 cnt; w64 v; w64 csz; w64 PVv; w64 Kv; w64 jb; w64 SHBv; w64 SKv; w64 j1; w64 j2; w64 j3;
w64 SSLOTv; w64 j4; w64 PBv; w64 N8D; w64 (N8D / 8);
w64 0; w64 RZ; w64 (Uv - 16); w64 Uv; w64 SUv; w64 NPv; w64 NDv ].
Definition E0 : env := Ereg regs0 XW.
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. exact (Er 10 10%bv eq_refl). Qed.
Lemma E4 : ew E0 4 = getr regs0 4. Proof. exact (Er 4 4%bv eq_refl). Qed.
Lemma EaP : ew E0 40 = w64 Pv. Proof. reflexivity. Qed.
Lemma EaR8 : ew E0 38 = w64 R8v. Proof. reflexivity. Qed.
Lemma EaK : ew E0 45 = w64 Kv. Proof. reflexivity. Qed.
Lemma EaSK : ew E0 48 = w64 SKv. Proof. reflexivity. Qed.
Lemma EaSSLOT : ew E0 52 = w64 SSLOTv. Proof. reflexivity. Qed.
Lemma EaPB : ew E0 54 = w64 PBv. Proof. reflexivity. Qed.
Lemma EaPV : ew E0 44 = w64 PVv. Proof. reflexivity. Qed.
Lemma EaRZ : ew E0 58 = w64 RZ. Proof. reflexivity. Qed.
Lemma EaU : ew E0 60 = w64 Uv. Proof. reflexivity. Qed.
Lemma EaSU : ew E0 61 = w64 SUv. Proof. reflexivity. Qed.
Lemma EaFIL : ew E0 62 = w64 FILv. Proof. reflexivity. Qed.
Lemma EaNP : ew E0 62 = w64 NPv. Proof. reflexivity. Qed.
Lemma EaND : ew E0 63 = w64 NDv. Proof. reflexivity. Qed.
Definition WINT (a : Z) : Prop :=
(Pv <= a < Pv + 4) \/ (T + 2768 <= a < T + 2824) \/ (SSLOTv <= a < SSLOTv + 8) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Definition PBW (odd : bool) (a : Z) : Prop := odd = true /\ PBv <= a < PBv + 1.
Definition WIN (odd : bool) (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0) \/ WINT a \/ ((Kv <= a < Kv + 16) \/ (Uv - 16 <= a < Uv)) \/ PBW odd a.
Definition win_in_WIN (odd : bool) (E : env) (a : Z) (t : option nat * Z * Z) : Prop :=
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN odd a.
Hypotheses (Hcl : 1 <= cl <= 31) (Hv : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32) (Hcnt : 1 <= cnt <= 16) (Hjb : 0 <= jb <= 255).
Hypothesis Hv2 : v mod 2 = 0.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn : getr regs0 10 = w64 n.
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfibsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Lemma HCdisj : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (ly_C ly <= a < ly_C ly + 256).
Proof.
pose proof (pairwise_ij _ _ 6 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as CS. unfold zdisjoint in CS. cbn [fst snd] in CS.
intros a Ha. lia.
Qed.
Definition DZONE (a : Z) : Prop :=
(0x177ec8 <= a < 0x5c8650) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Lemma HC_NB : zdisjoint (ly_C ly, 256) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (ly_C ly, 256) (ly_SB ly, kStoreBlockSize).
Proof.
split; apply zdisjoint_sym;
[ exact (pairwise_ij _ _ 4 1 _ _ (lo_disj ly LY) eq_refl eq_refl) | exact (pairwise_ij _ _ 5 0 _ _ (lo_disj ly LY) eq_refl eq_refl) ].
Qed.
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfibsegs (mrestrict (w_H W) mem0) PBv 1 250.
Lemma HCX : zdisjoint (ly_C ly, 256) (ly_prim ly, kPrimResvSize) /\ zdisjoint (ly_C ly, 256) (ly_T ly, kThreadObjSize).
Proof.
split; apply zdisjoint_sym;
[ exact (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) | exact (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) ].
Qed.
Lemma tr_length : (1 <= length tr <= 30)%nat.
Proof. unfold tr, call_trace. destruct (frame0_ok ly regs0); [apply unwind_of_chain_length | cbn; lia]. Qed.
Lemma Kv_range : ly_space ly <= Kv /\ Kv + 2 ^ 16 <= ly_space ly + kSpaceSize.
Proof.
unfold Kv, SB, kSpaceSize. split; [nia|].
assert (cl * 2 ^ 32 <= 31 * 2 ^ 32) by nia. change (2 ^ 37) with (31 * 2 ^ 32 + 2 ^ 32). lia.
Qed.
Lemma high_facts :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= ly_space ly /\
ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (T <= a < T + kThreadObjSize) /\ ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)).
Proof.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD. pose proof (lo_space_in ly LY) as HSP.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC. cbn beta in IT, IC. cbn [fst snd] in IT, IC.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
clear HA HD. split; [exact ZT|]. clear ZT.
unfold in_high, in_app, zdisjoint, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. unfold T in *.
pose proof ASAN_CEIL_range as [CR _].
split; [clear - IT CR; lia|]. do 4 (split; [clear TS PS ZC; lia|]).
split; [exact ZC|]. split; [clear - IC CR; lia|].
intros a Ha; split; intros Hx; [clear PS | clear TS]; clear ZC; lia.
Qed.
Lemma blocks_facts :
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\
zdisjoint (T, kThreadObjSize) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (T, kThreadObjSize) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (ly_prim ly, kPrimResvSize) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (ly_prim ly, kPrimResvSize) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (ly_NB ly, kNodesBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_SB ly, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_prim ly, kPrimResvSize) (T, kThreadObjSize).
Proof.
pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 4 _ HI eq_refl) as I4. pose proof (Forall_nth' _ _ 5 _ HI eq_refl) as I5. cbn beta in I4, I5. cbn [fst snd] in I4, I5.
split; [exact (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; lia) I4 (pairwise_ij _ _ 4 4 _ _ HD eq_refl eq_refl))|].
split; [exact (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; lia) I5 (pairwise_ij _ _ 5 3 _ _ HD eq_refl eq_refl))|].
split; [exact (pairwise_ij _ _ 2 1 _ _ HD eq_refl eq_refl)|]. split; [exact (pairwise_ij _ _ 2 2 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij _ _ 0 3 _ _ HD eq_refl eq_refl)|]. split; [exact (pairwise_ij _ _ 0 4 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij _ _ 4 3 _ _ HD eq_refl eq_refl)|]. split; [exact (pairwise_ij _ _ 5 2 _ _ HD eq_refl eq_refl)|].
exact (pairwise_ij _ _ 0 1 _ _ HD eq_refl eq_refl).
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 high_facts) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & F7 & _). exact (zone3_off_img _ _ a F7 Ha). Qed.
Lemma off_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 blocks_facts) Ha). Qed.
Lemma off_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 (proj2 blocks_facts)) Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| apply off_NB; unfold kNodesBlockSize; tac
| apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Lemma K0_facts : RZ = 16 /\ 0 <= n <= 48 /\ 1 <= NPv <= 48 /\ (n = 0 -> NPv = 1) /\ (1 <= n -> NPv = n) /\
8 <= R8v <= 48 /\ R8v mod 8 = 0 /\ NPv <= R8v /\ n <= R8v /\ 0 <= N8D <= NPv /\ N8D mod 8 = 0 /\ NPv < N8D + 8 /\
FILv = NPv /\ NDv = R8v + 16 /\ 24 <= NDv <= 64 /\ N8D = NPv / 8 * 8 /\ R8v = (Z.max n 8 + 7) / 8 * 8.
Proof.
clear - Nrange. unfold NDv, FILv, N8D, R8v, NPv, RZ.
pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (Z.max n 8 + 7) 8 ltac:(lia)) as M1.
pose proof (Z.div_mod (Z.max n 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (Z.max n 1) 8 ltac:(lia)) as M2.
assert (A1 : (Z.max n 8 + 7) / 8 * 8 mod 8 = 0) by (apply Z_mod_mult).
assert (A2 : Z.max n 1 / 8 * 8 mod 8 = 0) by (apply Z_mod_mult).
repeat split; first [exact A1 | exact A2 | lia].
Qed.
Lemma RZ_num : RZ = 16 /\ RZ / 8 = 2 /\ 0 <= n <= 48 /\ 1 <= NPv <= 48 /\ 8 <= R8v <= 48 /\ NPv <= R8v /\ 0 <= N8D <= NPv /\ NPv < N8D + 8 /\ FILv = NPv.
Proof. pose proof K0_facts as KF. clear - KF. unfold RZ in *. repeat split; try lia. Qed.
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
Lemma derived_ranges :
kHighMemBeg <= Kv /\ Kv + 2 ^ 16 <= ASAN_CEIL /\ Kv mod 16 = 0 /\
0x2008fff7000 <= SKv /\ SKv + 2 ^ 13 <= kHighMemBeg /\
0x2008fff7000 <= PBv /\ PBv + 1 <= kHighMemBeg /\ PBv = SKv + RZ / 8 + N8D / 8 /\
T + t_cache + 80 <= Pv /\ Pv + 80 <= T + 2768 /\ Pv + 16 <= PVv /\ PVv + 4 <= Pv + 80 /\
T + 2912 + 8 <= SSLOTv /\ SSLOTv + 8 <= T + t_unwinding /\
0 <= N8D <= NPv /\ NPv <= R8v <= 48 /\ NPv < N8D + 8 /\ N8D mod 8 = 0 /\ R8v mod 8 = 0 /\
SUv = SKv + RZ / 8 /\ PBv = SUv + N8D / 8 /\ Uv = Kv + RZ /\ 0x2008fff7000 <= SUv /\ RZ / 8 = 2 /\ RZ = 16 /\
FILv = NPv /\ 1 <= NPv <= 48 /\ NDv = R8v + RZ /\ 24 <= NDv <= 64 /\ 0 <= n <= 48 /\
(140735332483072 <= ASAN_CEIL <= 140737479966720).
Proof.
pose proof K0_facts as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6 & RF7 & RF8 & RF9 & RF10 & RF11 & RF12 & RF13 & RF14 & RF15 & RF16 & RF17).
pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _). pose proof Kv_range as [HK1 HK2]. pose proof (lo_space_al ly LY) as HAL.
assert (HKal : Kv mod 16 = 0).
{ clear - HAL. unfold Kv, SB. rewrite <- Zplus_mod_idemp_l, <- (Zplus_mod_idemp_l (ly_space ly)).
replace (ly_space ly mod 16) with 0.
2:{ symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 65536); [exists 4096; reflexivity|]. apply Znumtheory.Zmod_divide; [lia|exact HAL]. }
replace (cl * 2 ^ 32) with ((cl * 2 ^ 28) * 16) by lia. rewrite Z.add_0_l, Z_mod_mult, Z.add_0_l, Z.mul_comm, Z_mod_mult. reflexivity. }
apply Z.mod_divide in RF11 as [nq Hnq]; [|lia].
assert (E16 : Kv = 16 * (Kv / 16)) by (pose proof (Z.div_mod Kv 16 ltac:(lia)); lia).
assert (EK8 : Kv / 8 = 2 * (Kv / 16)) by (rewrite E16 at 1; replace (16 * (Kv / 16)) with ((2 * (Kv / 16)) * 8) by lia; apply Z.div_mul; lia).
assert (EU8 : (Kv + RZ) / 8 = 2 * (Kv / 16) + 2).
{ unfold RZ. rewrite E16 at 1. replace (16 * (Kv / 16) + 16) with ((2 * (Kv / 16) + 2) * 8) by lia. apply Z.div_mul. lia. }
assert (EN8 : N8D / 8 = nq) by (rewrite Hnq; apply Z.div_mul; lia).
assert (EP8 : (Kv + RZ + N8D) / 8 = 2 * (Kv / 16) + 2 + nq).
{ unfold RZ. rewrite E16, Hnq at 1. replace (16 * (Kv / 16) + 16 + nq * 8) with ((2 * (Kv / 16) + 2 + nq) * 8) by lia. apply Z.div_mul. lia. }
unfold PVv, SKv, PBv, SUv, Uv, Pv, SSLOTv, SHBv. rewrite EP8, EU8, EK8, EN8. change (RZ / 8) with 2.
set (q16 := Kv / 16) in *. clearbody q16.
unfold Kv, SB, T in *.
clear - RF1 RF2 RF3 RF6 RF7 RF8 RF9 RF10 RF12 RF13 RF14 RF15 Hnq F1 F2 F3 F4 F5 F6 HK1 HK2 HKal E16 Hcl Hcnt Hv.
ceil; unfold kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize, t_cache, t_stats, t_unwinding, kThreadObjSize in *.
repeat split; try lia.
Qed.
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Definition CLk : sv := SAlu ALU_SRL (SOff aR8 47) (SLit 5).
Lemma CLk_E : forall E : env, (forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> zev (rho_of E) CLk = cl.
Proof.
intros E HE. pose proof K0_facts as (_ & _ & _ & _ & _ & R6 & _).
unfold CLk. cbn [zev zalu_raw]. unfold rho_of. rewrite (HE aR8 (ltHAV aR8 eq_refl)). unfold aR8. rewrite EaR8. unfold w64. rewrite unsigned_lit_small by lia.
rewrite Hcl_def. unfold class_id, RZ. replace (R8v + 16 <=? 512) with true by (symmetry; apply Z.leb_le; lia).
rewrite (zcanon_id (R8v + 47)) by (unfold M64; lia). rewrite (zcanon_id 5) by (unfold M64; lia).
change (Z.land 5 63) with 5. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
replace (R8v + 16 + 31) with (R8v + 47) by lia. apply zcanon_id. unfold M64.
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Definition WIN1 (odd : bool) (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ WINT a \/ ((Kv <= a < Kv + 16) \/ (Uv - 16 <= a < Uv)) \/ PBW odd a.
Lemma WIN1_WIN : forall odd a, WIN1 odd a -> WIN odd a.
Proof. intros odd a H. unfold WIN1, WIN, IFRAME, ASTACK in *. destruct H as [H|[H|H]]; [left; lia | left; lia | right; exact H]. Qed.
Lemma WIN_odd : forall a, WIN false a -> WIN true a.
Proof. intros a H. unfold WIN, PBW in *. destruct H as [H|[H|[H|[H _]]]]; [tauto|tauto|tauto|discriminate]. Qed.
Lemma WIN1_odd : forall a, WIN1 false a -> WIN1 true a.
Proof. intros a H. unfold WIN1, PBW in *. destruct H as [H|[H|[H|[H|[H _]]]]]; [tauto|tauto|tauto|tauto|discriminate]. Qed.
Definition WSKEL (odd : bool) : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, 0); (Some 32%nat, 2768, 2800); (Some 32%nat, t_unwinding, t_unwinding + 1); (Some 32%nat, 2800, 2824);
(Some 52%nat, 0, 8); (Some 40%nat, 0, 4); (Some 45%nat, 0, 16); (Some 60%nat, -16, 0)] ++ (if odd then [(Some 54%nat, 0, 1)] else []).
Definition WSKEL1 (odd : bool) : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, - IFRAME); (Some 2%nat, -64, 0); (Some 32%nat, 2768, 2800); (Some 32%nat, t_unwinding, t_unwinding + 1); (Some 32%nat, 2800, 2824);
(Some 52%nat, 0, 8); (Some 40%nat, 0, 4); (Some 45%nat, 0, 16); (Some 60%nat, -16, 0)] ++ (if odd then [(Some 54%nat, 0, 1)] else []).
Definition win_sub (t u : option nat * Z * Z) : bool :=
obase_eqb (fst (fst t)) (fst (fst u)) && (snd (fst u) <=? snd (fst t)) && (snd t <=? snd u).
Lemma win_sub_sound : forall E a t u, win_sub t u = true ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t ->
base_val E (fst (fst u)) + snd (fst u) <= a < base_val E (fst (fst u)) + snd u.
Proof.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Lemma WSKEL_WIN : forall odd (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t (WSKEL odd) ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN odd a.
Proof.
intros odd E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF.
unfold WSKEL in Hin. apply in_app_iff in Hin as [Hin|Hin].
- cbn [In] in Hin. unfold WIN, WINT.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by lia;
rewrite ?E2, ?EaT, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
- destruct odd; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (clear; cbv; lia).
rewrite EaPB in Hr. unfold w64 in Hr. unfold kHighMemBeg in DR. rewrite unsigned_lit_small in Hr by lia.
unfold WIN, PBW. right; right; right. split; [reflexivity | lia].
Qed.
Lemma WSKEL1_WIN1 : forall odd (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t (WSKEL1 odd) ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WIN1 odd a.
Proof.
intros odd E a t HE Hin Hr. pose proof derived_ranges as DR. pose proof high_facts as HF.
unfold WSKEL1 in Hin. apply in_app_iff in Hin as [Hin|Hin].
- cbn [In] in Hin. unfold WIN1, WINT.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, t_cache, t_unwinding, kThreadObjSize, aHAV, IFRAME in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite HE in Hr by lia;
rewrite ?E2, ?EaT, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
unfold sp0 in *; lia.
- destruct odd; [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (clear; cbv; lia).
rewrite EaPB in Hr. unfold w64 in Hr. unfold kHighMemBeg in DR. rewrite unsigned_lit_small in Hr by lia.
unfold WIN1, PBW. right; right; right; right. split; [reflexivity | lia].
Qed.
Lemma windows_WIN : forall odd (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN odd a.
Proof.
intros odd E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
exact (WSKEL_WIN odd E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma windows_WIN1 : forall odd (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL1 odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN1 odd a.
Proof.
intros odd E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
exact (WSKEL1_WIN1 odd E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma frame_WIN1 : forall odd (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL1 odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN1 odd (bv_unsigned x) -> m' x = m x.
Proof. intros odd E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WIN1 odd E rs _ HE Hb Hw). Qed.
Lemma WIN_not_high : forall odd a, sp0 <= a < ly_top ly -> ~ WIN odd a.
Proof.
intros odd a Ha Hw. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof Kv_range as HK. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
destruct (F9 a) as [N1 N2]; [unfold ASTACK in *; lia|].
pose proof RZ_num as RZN. ceil; unfold WIN, WINT, PBW, zone3, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize, kThreadObjSize, ASTACK, t_cache, t_unwinding, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *. lia.
Qed.
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfib_unwind_spec.
Hypothesis SEED : st_ok tfibsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 0x52930) mem0 (seg_rom tfibsegs))).
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Definition SKEL_TAIL : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0K).
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly).
Proof.
pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. clear HD.
destruct Hsp as (S1 & S2 & S3 & S4). unfold zdisjoint, kThreadObjSize, ASTACK, kPrimResvSize in *. cbn [fst snd] in *. unfold T.
split; [clear PS CS; lia|]. split; [clear TS CS; lia|]. clear TS PS; lia.
Qed.
Lemma stack_ivs2 :
(ly_NB ly + kNodesBlockSize <= sp0 - ASTACK \/ sp0 <= ly_NB ly) /\ (ly_SB ly + kStoreBlockSize <= sp0 - ASTACK \/ sp0 <= ly_SB ly).
Proof.
pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij _ _ 4 3 _ _ HD eq_refl eq_refl) as NS. pose proof (pairwise_ij _ _ 5 2 _ _ HD eq_refl eq_refl) as BS. clear HD.
destruct Hsp as (S1 & S2 & S3 & S4). unfold zdisjoint, ASTACK, kNodesBlockSize, kStoreBlockSize in *. cbn [fst snd] in *.
split; [clear BS; lia | clear NS; lia].
Qed.
Lemma DZONE_disj : forall odd a, DZONE a ->
~ WIN odd a /\ ~ (Kv + RZ <= a < Kv + RZ + NPv) /\ ~ (SUv <= a < SUv + N8D / 8) /\ ~ (sp0 - ASTACK <= a < sp0).
Proof.
intros odd a Ha. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & PNB & PSB & _). pose proof stack_ivs2 as (NBS & SBS).
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_top ly LY) as (_ & _ & _ & T4 & _ & _ & T7).
unfold zdisjoint in TNB, TSB, PNB, PSB. cbn [fst snd] in TNB, TSB, PNB, PSB. unfold DZONE, WIN, WINT, PBW in *.
pose proof RZ_num as RZN. ceil; unfold zone3, zone3cases, kHighMemBeg, ASAN_CEIL, kHighMemEnd, t_cache, t_unwinding, t_stats, kThreadObjSize, ASTACK, kSpaceSize, kPrimResvSize,
kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg in *. unfold T in *.
destruct Ha as [Ha|[Ha|Ha]].
- clear NBhi SBhi TNB TSB PNB PSB NBS SBS HKR HSP. repeat split; lia.
- clear SBhi TSB PSB SBS F1 F2 F7 F8. repeat split; lia.
- clear NBhi TNB PNB NBS F1 F2 F7 F8. repeat split; lia.
Qed.
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)) /\
((hi <= 0x177ec8 \/ 0x5c8650 <= lo) /\ (hi <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= lo) /\
(hi <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= lo)) /\
((hi <= SUv \/ PBv <= lo) /\ (hi <= Kv + RZ \/ Kv + RZ + 4096 <= lo) /\ (hi <= PBv \/ PBv + 1 <= lo)).
Lemma zone_lit : forall lo hi wlo whi,
TFIB_IMG_LO <= lo -> hi <= 0x177ec8 \/ 0x5c8650 <= lo -> hi <= TFIB_IMG_END -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof derived_ranges as DR. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 DR NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivs as (DT & _ & _). pose proof blocks_facts as (_ & _ & TNB & TSB & _ & _ & _ & _ & PT).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in TNB, TSB, PT. cbn [fst snd] in TNB, TSB, PT. numconst. unfold T in *.
clear - Hz0 Hz1 Hz2 DR F1 F2 F3 F4 F5 F6 DT TNB TSB PT HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof stack_ivs as (_ & _ & DC). pose proof HC_NB as (CNB & CSB). pose proof HCX as (CP & _).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in CNB, CSB, CP. cbn [fst snd] in CNB, CSB, CP. numconst.
clear - Hz0 Hz1 Hz2 DR F3 F4 F5 F6 F7 F8 DC CNB CSB CP HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. lia.
Qed.
Lemma zone_K : forall lo hi wlo whi,
Kv <= lo -> hi <= Kv + RZ -> (whi <= wlo \/ (Kv <= wlo /\ whi <= Kv + RZ)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & _).
pose proof stack_ivs as (_ & DP & _). pose proof blocks_facts as (_ & _ & _ & _ & PNB & PSB & _).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in PNB, PSB. cbn [fst snd] in PNB, PSB. numconst.
clear - Hz0 Hz1 Hz2 DR F3 F4 F5 F6 DP PNB PSB HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. lia.
Qed.
Lemma zone_SH : forall lo hi wlo whi,
0x2008fff7000 <= lo -> hi <= kHighMemBeg -> hi <= SUv -> (whi <= wlo \/ (lo <= wlo /\ whi <= hi)) ->
RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof derived_ranges as DR. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 DR NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. lia.
Qed.
Lemma tail_ext_ok : forall (E : env) r,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAIL ->
let b := base_val E (YP09.r_base r) in
(b + YP09.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YP09.r_lo r) /\ 0 <= b + YP09.r_lo r /\ b + YP09.r_hi r <= 2 ^ 64 /\
(YP09.r_whi r <= YP09.r_wlo r \/ (TFIB_IMG_END <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= 2 ^ 64) \/ (0 <= b + YP09.r_wlo r /\ b + YP09.r_whi r <= TFIB_IMG_LO)) /\
((b + YP09.r_hi r <= 0x177ec8 \/ 0x5c8650 <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= b + YP09.r_lo r)) /\
((b + YP09.r_hi r <= SUv \/ PBv <= b + YP09.r_lo r) /\ (b + YP09.r_hi r <= Kv + RZ \/ Kv + RZ + 4096 <= b + YP09.r_lo r) /\
(b + YP09.r_hi r <= PBv \/ PBv + 1 <= b + YP09.r_lo r)).
Proof.
intros E r HE Hin. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
let sk := eval vm_compute in SKEL_TAIL in change SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB, ?EaPV; unfold w64;
rewrite ?unsigned_lit_small by (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T in *; lia).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R) by (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia) end.
all: first [ apply zone_lit; clear - DR; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_SH; clear - DR; numconst; lia
| apply zone_K; clear - DR; numconst; lia
| apply zone_T; clear - DR F1 F2; numconst; unfold T in *; lia
| apply zone_C; clear - DR F7 F8; numconst; lia ].
Qed.
Definition at_ST (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WIN false (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).
Definition at_ST2 (ss : sstate) (z : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env) regs2 mem2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 0x318cc) mem2 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WIN false (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
regs_preserved (ms_regs ms) regs2 /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem2 x = ms_mem ms x) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) /\
DPOST z mem2.
Definition at_S2 (odd : bool) (ss : sstate) (z : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env) memD,
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfibsegs E' ss (restrict (w_H W) ms) /\
DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
(forall x : word, DZONE (bv_unsigned x) -> ms_mem ms x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> ms_mem ms x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) PBv 1 (NPv mod 8)).
Definition at_RET (odd : bool) (z : Z) (W' : world tfibsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (Kv + RZ) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + NPv) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, WINT a \/ (Kv <= a < Kv + RZ + NPv) \/ PBW odd a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfibsegs m (Kv + RZ - 16) 1 2 /\ val_mem tfibsegs m (Kv + RZ - 15) 1 (hdr_byte1 jb) /\
val_mem tfibsegs m (Kv + RZ - 14) 2 0 /\ val_mem tfibsegs m (Kv + RZ - 12) 4 NPv /\
val_mem tfibsegs m Pv 4 (cnt - 1) /\ val_mem tfibsegs m (T + t_unwinding) 1 0 /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfibsegs m PBv 1 (NPv mod 8)) /\
(forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + FILv -> mem' x = Some (Z_to_bv 8 190)).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_WIN1 odd E rs m1 m2 HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Lemma memset_stretch : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); [lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(pose proof (u64_range x); unfold TFIB_IMG_END in *; lia) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
destruct (tfib_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfibsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia) SOK
ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. f_equal. rewrite Z.add_0_r.
change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by lia. change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [lia|]. symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [lia | exact Hrpc]. }
change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [rewrite H10', H10; reflexivity|].
apply Hfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- exact H10'.
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H W x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
subst m1full. unfold munrestrict. rewrite Hh. subst m1 bs. rewrite wbytes_repeat_spec by (rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia).
rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [reflexivity|].
symmetry. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfibsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfibsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qmeter S.
Lemma case0_sizes :
rz_log n = 0 /\ rz_size n = RZ /\ rounded_size n = R8v /\ needed_primary n = R8v + RZ /\
from_primary n = true /\ needed_size n = R8v + RZ /\ req_size n = NPv.
Proof.
clear - Nrange. unfold RZ.
assert (L : rz_log n = 0) by (unfold rz_log; destruct (Z.leb_spec n 48); [reflexivity|lia]).
assert (RS : rz_size n = 16) by (unfold rz_size; rewrite L; reflexivity).
assert (R8 : rounded_size n = R8v) by (unfold rounded_size, round_up, R8v; f_equal; f_equal; lia).
assert (NP : needed_primary n = R8v + 16) by (unfold needed_primary; rewrite R8, RS; reflexivity).
assert (FP : from_primary n = true).
{ unfold from_primary. rewrite NP. apply Z.leb_le. unfold R8v, kMaxSize.
pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 7) 8 ltac:(lia)). lia. }
repeat split; try assumption.
- unfold needed_size. rewrite FP. exact NP.
- unfold req_size, NPv. destruct (Z.eqb_spec n 0); lia.
Qed.
Lemma Kv_is_sptr : Kv = sptr_addr B ly (PPrim (region_off cl + off)).
Proof. clear - Hoff_def Hcl. unfold Kv, SB, sptr_addr. cbn. rewrite region_off_eq by lia. lia. Qed.
End g.
End f.
