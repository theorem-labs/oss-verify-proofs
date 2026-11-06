(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG00 YG0a YG01 YG04 YG03 YG0h YG10 YG0u YG0d YG0y YG0w.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF00 YF03.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3y.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Lemma Zbv_add_unsigned : forall x k, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + k) = Z_to_bv 64 (x + k).
Proof.
intros x k. img_apply Z_to_bv64_eq_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
img_change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. img_refl.
Qed.
Lemma unwind_of_chain_length : forall pc0 ch, (1 <= length (unwind_of_chain pc0 ch) <= 30)%nat.
Proof.
intros pc0 ch. unfold unwind_of_chain, kUnwindMax. rewrite firstn_length. cbn [length]. img_lia.
Qed.
Lemma val_mem_addr {imgk : img} : forall m a a' (n : nat) v, val_mem tfxsegs m a n v -> a = a' -> val_mem tfxsegs m a' n v.
Proof. intros m a a' n v H <-. img_exact H. Qed.
Lemma le_byte_zero : forall w k, YP0g.le_byte 0 w k = 0.
Proof. intros w k. unfold YP0g.le_byte. rewrite Z.mod_0_l by (img_try (img_apply Z.pow_nonzero; img_lia)). rewrite Z.shiftr_0_l. img_refl. Qed.
Lemma land_m8_64 : forall a, 0 <= a < 2 ^ 64 -> Z.land a (2 ^ 64 - 8) = a - a mod 8.
Proof.
intros a Ha. img_change (2 ^ 64 - 8) with (Z.land (- 2 ^ 3) (Z.ones 64)).
rewrite Z.land_assoc, Z.land_ones by img_lia. rewrite land_neg_pow2 by img_lia. img_change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(img_lia)). img_apply Z.mod_small. img_lia.
Qed.
Lemma land_m8_48 : forall a, 0 <= a < 2 ^ 48 -> Z.land a (2 ^ 48 - 8) = a - a mod 8.
Proof.
intros a Ha. img_change (2 ^ 48 - 8) with (Z.land (- 2 ^ 3) (Z.ones 48)).
rewrite Z.land_assoc, Z.land_ones by img_lia. rewrite land_neg_pow2 by img_lia. img_change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound a 8 ltac:(img_lia)). img_apply Z.mod_small. img_lia.
Qed.
Lemma div8_bounds : forall x, 0 <= x -> 8 * (x / 8) <= x < 8 * (x / 8) + 8.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound x 8 ltac:(img_lia)). img_lia. Qed.
Lemma land_7_mod : forall a, 0 <= a -> Z.land a 7 = a mod 8.
Proof. intros a Ha. img_change 7 with (Z.ones 3). rewrite Z.land_ones by img_lia. img_refl. Qed.
Lemma lxor_ones64 {imgk : img} : forall u, 0 <= u < 2 ^ 64 -> Z.lxor u (2 ^ 64 - 1) = 2 ^ 64 - 1 - u.
Proof.
intros u Hu. img_change (2 ^ 64 - 1) with (Z.ones 64).
assert (D : Z.ldiff u (Z.ones 64) = 0).
{ destruct (Z.eq_dec u 0) as [->|Hnz]; [img_refl|]. img_apply Z.ldiff_ones_r_low; [img_lia|]. img_apply Z.log2_lt_pow2; img_lia. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) u D).
img_apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.ltb_spec i 64).
- rewrite Z.ones_spec_low by img_lia. destruct (Z.testbit u i); img_refl.
- rewrite Z.ones_spec_high by img_lia. rewrite (Z.bits_above_log2 u i); [img_refl| img_lia |].
destruct (Z.eq_dec u 0) as [->|Hnz]; [img_try (cbn; img_lia)|]. img_apply (Z.lt_le_trans _ 64); [img_try (img_apply Z.log2_lt_pow2; img_lia) | img_lia].
Qed.
Definition hdr_byte1 (jb : Z) : Z :=
zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (Z.lor (zcanon (Z.land (zcanon (jb + 0)) (zcanon (-4)))) (zcanon 1))) (zcanon 143))) (zcanon 16))) (zcanon 243))) (zcanon 0)).
Lemma hdr_byte1_ok {imgk : img} : forall jb, 0 <= jb <= 255 -> 0 <= hdr_byte1 jb < 256 /\ Z.land (hdr_byte1 jb) 127 = 17.
Proof.
intros jb Hjb.
assert (C : forallb (fun i => let b := hdr_byte1 (Z.of_nat i) in (0 <=? b) && (b <? 256) && (Z.land b 127 =? 17)) (seq 0 256) = true) by (img_try ((img_case; vm_compute); img_refl)).
pose proof (forallb_seq_In _ 256 (Z.to_nat jb) C ltac:(img_lia)) as Hx. cbn beta in Hx. rewrite Z2Nat.id in Hx by img_lia.
apply andb_prop in Hx as [Hx H3]. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. img_lia.
Qed.
Lemma chunk_val_at {imgk : img} : forall (H : word -> bool) E ss ms i j r off (n : BinNums.N) e v a,
st_ok tfxsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
nth_error (YQ0b.r_chunks r) j = Some (YQ0b.mkChunk off (CVal n e)) ->
a = base_val E (YQ0b.r_base r) + off ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem tfxsegs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros H E ss ms i j r off n e v a HS Hi Hj -> He Hv Hn. eapply st_ok_chunk_val; eassumption. Qed.
Lemma ltHAV (k : nat) : Nat.ltb k aHAV = true -> (k < aHAV)%nat.
Proof. intros H. img_apply Nat.ltb_lt. img_exact H. Qed.
Lemma st_ok_forget2 {imgk : img} : forall k E ss ss' (H : word -> bool) ms (clob : list (bv 5)),
st_ok tfxsegs E ss (restrict H ms) -> ss_resv ss = None -> ss_atoms_lt k ss = true ->
regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss) = ss' ->
st_ok tfxsegs (havoc E k (map (getr (ms_regs ms)) clob)) ss' (restrict H ms).
Proof.
intros k E ss ss' H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz <-.
pose proof (st_ok_forget k E ss H ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz) as X.
rewrite <- (st_ok_restrict_mkst tfxsegs H E ss ms HS Hrv) in X. img_exact X.
Qed.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize, kPtrArrayResv, kMaxNumChunks in *; img_lia ].
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; zlia))
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c
end.
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in *.
Ltac pin_zev :=
lazymatch goal with |- U _ _ = U _ (sr_get ?sr ?r) => let t := img_ev (sr_get sr r) in img_change (sr_get sr r) with t end;
img_apply U_eq_by_zev; [img_refl | img_refl |]; cbn [zev zalu_raw zmd_raw]; unfold rho_of.
Ltac memv HS i j :=
lazymatch goal with |- val_mem _ _ ?a ?n ?v =>
let nn := lazymatch n with 1%nat => constr:(1%N) | 2%nat => constr:(2%N) | 4%nat => constr:(4%N) | _ => constr:(8%N) end in
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
eapply (chunk_val_at H E ss ms i j _ _ nn _ v a HS);
[ img_refl | img_refl | cbn [base_val YQ0b.r_base]
| | lazymatch goal with |- _ <= _ < ?p => let q := img_ev constr:(p) in img_change p with q end
| cbn; img_lia ]
end
end.
Ltac forget_regs HS k clob :=
lazymatch type of HS with st_ok _ ?E ?ss (restrict ?H ?ms) =>
let ss' := img_ev (ss_after_stretch ss (ss_mem ss) k clob (ss_pc ss)) in
let HS2 := fresh "HSf" in
pose proof (st_ok_forget2 k E ss ss' H ms clob HS eq_refl
ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl)) ltac:(img_try ((img_case; vm_compute); img_refl))
eq_refl eq_refl ltac:(img_try ((img_case; vm_compute); img_refl))) as HS2; clear HS; rename HS2 into HS
end.
Lemma Forall_nth' {A} (P : A -> Prop) (l : list A) (i : nat) (x : A) : Forall P l -> nth_error l i = Some x -> P x.
Proof. intros HF He. img_exact (proj1 (Forall_forall P l) HF x (nth_error_In l i He)). Qed.
Lemma pairwise_ij {A} (R : A -> A -> Prop) : forall (l : list A) (i j : nat) (x y : A),
pairwise R l -> nth_error l i = Some x -> nth_error l (i + S j)%nat = Some y -> R x y.
Proof.
induction l as [|a l IH]; intros i j x y HP Hi Hj; [img_try (destruct i; discriminate)|].
destruct HP as [HF HP]. destruct i as [|i]; cbn in Hi, Hj.
- injection Hi as <-. img_exact (Forall_nth' _ l j y HF Hj).
- img_exact (IH i j x y HP Hi Hj).
Qed.
Lemma zdisjoint_sym : forall a b, zdisjoint a b -> zdisjoint b a.
Proof. intros a b H. unfold zdisjoint in *. img_lia. Qed.
Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
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
Definition tr : list Z := call_trace ly (0x533a4 + D_2c4) regs0 ch.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 (Z.of_nat (length tr)); w64 j0; w64 R8v; w64 cl;
w64 Pv; w64 cnt; w64 v; w64 csz; w64 PVv; w64 Kv; w64 jb; w64 SHBv; w64 SKv; w64 j1; w64 j2; w64 j3;
w64 SSLOTv; w64 j4; w64 PBv; w64 N8D; w64 (N8D / 8);
w64 0; w64 RZ; w64 (Uv - 16); w64 Uv; w64 SUv; w64 NPv; w64 NDv ].
Definition E0 : env := Ereg regs0 XW.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. img_exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. img_exact (Er 10 10%bv eq_refl). Qed.
Lemma E4 : ew E0 4 = getr regs0 4. Proof. img_exact (Er 4 4%bv eq_refl). Qed.
Lemma EaP : ew E0 40 = w64 Pv. Proof. img_refl. Qed.
Lemma EaR8 : ew E0 38 = w64 R8v. Proof. img_refl. Qed.
Lemma EaK : ew E0 45 = w64 Kv. Proof. img_refl. Qed.
Lemma EaSK : ew E0 48 = w64 SKv. Proof. img_refl. Qed.
Lemma EaSSLOT : ew E0 52 = w64 SSLOTv. Proof. img_refl. Qed.
Lemma EaPB : ew E0 54 = w64 PBv. Proof. img_refl. Qed.
Lemma EaPV : ew E0 44 = w64 PVv. Proof. img_refl. Qed.
Lemma EaRZ : ew E0 58 = w64 RZ. Proof. img_refl. Qed.
Lemma EaU : ew E0 60 = w64 Uv. Proof. img_refl. Qed.
Lemma EaSU : ew E0 61 = w64 SUv. Proof. img_refl. Qed.
Lemma EaFIL : ew E0 62 = w64 FILv. Proof. img_refl. Qed.
Lemma EaNP : ew E0 62 = w64 NPv. Proof. img_refl. Qed.
Lemma EaND : ew E0 63 = w64 NDv. Proof. img_refl. Qed.
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
Hypothesis Htp : getr regs0 4 = w64 TFX_TP.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Hsp : ly_stk_lo ly + ASTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hch : if sp0 + 16 <? ly_top ly
then (if bad_next sp0 (ly_top ly) (bv_unsigned (getr regs0 8)) then ch = []
else sp0 + 16 <= bv_unsigned (getr regs0 8) /\
fpchain (rdword (aview tfxsegs (w_H W) mem0)) (bv_unsigned (getr regs0 8)) (ly_top ly) ch)
else ch = [].
Lemma HCdisj : forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (ly_C ly <= a < ly_C ly + 256).
Proof.
pose proof (pairwise_ij _ _ 6 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as CS. unfold zdisjoint in CS. cbn [fst snd] in CS.
intros a Ha. img_lia.
Qed.
Definition DZONE (a : Z) : Prop :=
((0x17c088 + D_10c0) <= a < (0x5cc810 + D_10c0)) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Lemma HC_NB : zdisjoint (ly_C ly, 256) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (ly_C ly, 256) (ly_SB ly, kStoreBlockSize).
Proof.
split; img_apply zdisjoint_sym;
[ img_try (img_exact (pairwise_ij _ _ 4 1 _ _ (lo_disj ly LY) eq_refl eq_refl)) | img_try (img_exact (pairwise_ij _ _ 5 0 _ _ (lo_disj ly LY) eq_refl eq_refl)) ].
Qed.
Hypothesis HKpres : forall a, Kv <= a < Kv + RZ + R8v -> apresent (w_H W) mem0 a.
Hypothesis HSKpres : forall a, SKv <= a < SKv + (RZ + R8v) / 8 -> apresent (w_H W) mem0 a.
Hypothesis HPB250 : NPv mod 8 <> 0 -> val_mem tfxsegs (mrestrict (w_H W) mem0) PBv 1 250.
Lemma HCX : zdisjoint (ly_C ly, 256) (ly_prim ly, kPrimResvSize) /\ zdisjoint (ly_C ly, 256) (ly_T ly, kThreadObjSize).
Proof.
split; img_apply zdisjoint_sym;
[ img_try (img_exact (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl)) | img_try (img_exact (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl)) ].
Qed.
Lemma tr_length : (1 <= length tr <= 30)%nat.
Proof. unfold tr, call_trace. destruct (frame0_ok ly regs0); [img_try (img_apply unwind_of_chain_length) | img_try (cbn; img_lia)]. Qed.
Lemma Kv_range : ly_space ly <= Kv /\ Kv + 2 ^ 16 <= ly_space ly + kSpaceSize.
Proof.
unfold Kv, SB, kSpaceSize. split; [img_try (nia)|].
assert (cl * 2 ^ 32 <= 31 * 2 ^ 32) by nia. img_change (2 ^ 37) with (31 * 2 ^ 32 + 2 ^ 32). img_lia.
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
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
clear HA HD. split; [img_try (img_exact ZT)|]. clear ZT.
unfold in_high, in_app, zdisjoint, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. unfold T in *.
pose proof ASAN_CEIL_range as [CR _].
split; [img_try (clear - IT CR; img_lia)|]. do 4 (split; [img_try (clear TS PS ZC; img_lia)|]).
split; [img_try (img_exact ZC)|]. split; [img_try (clear - IC CR; img_lia)|].
intros a Ha; split; intros Hx; [img_try (clear PS) | img_try (clear TS)]; clear ZC; img_lia.
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
split; [img_try (img_exact (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; img_lia) I4 (pairwise_ij _ _ 4 4 _ _ HD eq_refl eq_refl)))|].
split; [img_try (img_exact (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; img_lia) I5 (pairwise_ij _ _ 5 3 _ _ HD eq_refl eq_refl)))|].
split; [img_try (img_exact (pairwise_ij _ _ 2 1 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 2 2 _ _ HD eq_refl eq_refl))|].
split; [img_try (img_exact (pairwise_ij _ _ 0 3 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 0 4 _ _ HD eq_refl eq_refl))|].
split; [img_try (img_exact (pairwise_ij _ _ 4 3 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 5 2 _ _ HD eq_refl eq_refl))|].
img_exact (pairwise_ij _ _ 0 1 _ _ HD eq_refl eq_refl).
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 high_facts) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & F7 & _). img_exact (zone3_off_img _ _ a F7 Ha). Qed.
Lemma off_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 blocks_facts) Ha). Qed.
Lemma off_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 (proj2 blocks_facts)) Ha). Qed.
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| img_apply off_NB; unfold kNodesBlockSize; tac
| img_apply off_SB; unfold kStoreBlockSize; tac
| unfold off_img; unfold TFX_IMG_LO; unfold TFX_IMG_END; tac ].
Hypothesis Nrange : 0 <= n <= 48.
Lemma K0_facts : RZ = 16 /\ 0 <= n <= 48 /\ 1 <= NPv <= 48 /\ (n = 0 -> NPv = 1) /\ (1 <= n -> NPv = n) /\
8 <= R8v <= 48 /\ R8v mod 8 = 0 /\ NPv <= R8v /\ n <= R8v /\ 0 <= N8D <= NPv /\ N8D mod 8 = 0 /\ NPv < N8D + 8 /\
FILv = NPv /\ NDv = R8v + 16 /\ 24 <= NDv <= 64 /\ N8D = NPv / 8 * 8 /\ R8v = (Z.max n 8 + 7) / 8 * 8.
Proof.
clear - Nrange. unfold NDv, FILv, N8D, R8v, NPv, RZ.
pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(img_lia)) as D1. pose proof (Z.mod_pos_bound (Z.max n 8 + 7) 8 ltac:(img_lia)) as M1.
pose proof (Z.div_mod (Z.max n 1) 8 ltac:(img_lia)) as D2. pose proof (Z.mod_pos_bound (Z.max n 1) 8 ltac:(img_lia)) as M2.
assert (A1 : (Z.max n 8 + 7) / 8 * 8 mod 8 = 0) by (img_try (img_apply Z_mod_mult)).
assert (A2 : Z.max n 1 / 8 * 8 mod 8 = 0) by (img_try (img_apply Z_mod_mult)).
repeat split; first [img_exact A1 | img_exact A2 | img_lia].
Qed.
Lemma RZ_num : RZ = 16 /\ RZ / 8 = 2 /\ 0 <= n <= 48 /\ 1 <= NPv <= 48 /\ 8 <= R8v <= 48 /\ NPv <= R8v /\ 0 <= N8D <= NPv /\ NPv < N8D + 8 /\ FILv = NPv.
Proof. pose proof K0_facts as KF. clear - KF. unfold RZ in *. repeat split; try img_lia. Qed.
Ltac numconst ::= (ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, TFX_IMG_LO, kLowShadowBeg, UNW_STK, BST_SIZE, DEP_STK in * ); try pose proof RZ_num as RZN.
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
2:{ symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 65536); [img_try (exists 4096; img_refl)|]. img_apply Znumtheory.Zmod_divide; [img_lia|img_try (img_exact HAL)]. }
replace (cl * 2 ^ 32) with ((cl * 2 ^ 28) * 16) by img_lia. rewrite Z.add_0_l, Z_mod_mult, Z.add_0_l, Z.mul_comm, Z_mod_mult. img_refl. }
apply Z.mod_divide in RF11 as [nq Hnq]; [|img_lia].
assert (E16 : Kv = 16 * (Kv / 16)) by (img_try (pose proof (Z.div_mod Kv 16 ltac:(img_lia)); img_lia)).
assert (EK8 : Kv / 8 = 2 * (Kv / 16)) by (img_try (rewrite E16 at 1; replace (16 * (Kv / 16)) with ((2 * (Kv / 16)) * 8) by img_lia; img_apply Z.div_mul; img_lia)).
assert (EU8 : (Kv + RZ) / 8 = 2 * (Kv / 16) + 2).
{ unfold RZ. rewrite E16 at 1. replace (16 * (Kv / 16) + 16) with ((2 * (Kv / 16) + 2) * 8) by img_lia. img_apply Z.div_mul. img_lia. }
assert (EN8 : N8D / 8 = nq) by (img_try (rewrite Hnq; img_apply Z.div_mul; img_lia)).
assert (EP8 : (Kv + RZ + N8D) / 8 = 2 * (Kv / 16) + 2 + nq).
{ unfold RZ. rewrite E16, Hnq at 1. replace (16 * (Kv / 16) + 16 + nq * 8) with ((2 * (Kv / 16) + 2 + nq) * 8) by img_lia. img_apply Z.div_mul. img_lia. }
unfold PVv, SKv, PBv, SUv, Uv, Pv, SSLOTv, SHBv. rewrite EP8, EU8, EK8, EN8. img_change (RZ / 8) with 2.
set (q16 := Kv / 16) in *. clearbody q16.
unfold Kv, SB, T in *.
clear - RF1 RF2 RF3 RF6 RF7 RF8 RF9 RF10 RF12 RF13 RF14 RF15 Hnq F1 F2 F3 F4 F5 F6 HK1 HK2 HKal E16 Hcl Hcnt Hv.
ceil; unfold kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize, t_cache, t_stats, t_unwinding, kThreadObjSize in *.
repeat split; try img_lia.
Qed.
Hypothesis Hcl_def : cl = class_id (R8v + RZ).
Definition CLk : sv := SAlu ALU_SRL (SOff aR8 47) (SLit 5).
Lemma CLk_E : forall E : env, (forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> zev (rho_of E) CLk = cl.
Proof.
intros E HE. pose proof K0_facts as (_ & _ & _ & _ & _ & R6 & _).
unfold CLk. cbn [zev zalu_raw]. unfold rho_of. rewrite (HE aR8 (ltHAV aR8 eq_refl)). unfold aR8. rewrite EaR8. unfold w64. rewrite unsigned_lit_small by img_lia.
rewrite Hcl_def. unfold class_id, RZ. replace (R8v + 16 <=? 512) with true by (img_try (symmetry; img_apply Z.leb_le; img_lia)).
rewrite (zcanon_id (R8v + 47)) by (img_try (unfold M64; img_lia)). rewrite (zcanon_id 5) by (img_try (unfold M64; img_lia)).
img_change (Z.land 5 63) with 5. rewrite Z.shiftr_div_pow2 by img_lia. img_change (2 ^ 5) with 32.
replace (R8v + 16 + 31) with (R8v + 47) by img_lia. img_apply zcanon_id. unfold M64.
split; [img_try (img_apply Z.div_pos; img_lia) | img_try (img_apply Z.div_lt_upper_bound; img_lia)].
Qed.
Definition WIN1 (odd : bool) (a : Z) : Prop :=
(sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ WINT a \/ ((Kv <= a < Kv + 16) \/ (Uv - 16 <= a < Uv)) \/ PBW odd a.
Lemma WIN1_WIN : forall odd a, WIN1 odd a -> WIN odd a.
Proof. intros odd a H. unfold WIN1, WIN, IFRAME, ASTACK in *. destruct H as [H|[H|H]]; [img_try (left; img_lia) | img_try (left; img_lia) | img_try (right; img_exact H)]. Qed.
Lemma WIN_odd : forall a, WIN false a -> WIN true a.
Proof. intros a H. unfold WIN, PBW in *. destruct H as [H|[H|[H|[H _]]]]; [img_try (tauto)|img_try (tauto)|img_try (tauto)|img_try (discriminate)]. Qed.
Lemma WIN1_odd : forall a, WIN1 false a -> WIN1 true a.
Proof. intros a H. unfold WIN1, PBW in *. destruct H as [H|[H|[H|[H|[H _]]]]]; [img_try (tauto)|img_try (tauto)|img_try (tauto)|img_try (tauto)|img_try (discriminate)]. Qed.
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
- apply Nat.eqb_eq in H1. (subst; cbv beta). img_lia.
- img_lia.
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
cbn [fst snd base_val] in Hr; rewrite HE in Hr by img_lia;
rewrite ?E2, ?EaT, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0 in *; img_lia.
- destruct odd; [|img_try (destruct Hin)]. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (img_try (clear; (img_case; cbv); img_lia)).
rewrite EaPB in Hr. unfold w64 in Hr. unfold kHighMemBeg in DR. rewrite unsigned_lit_small in Hr by img_lia.
unfold WIN, PBW. right; right; right. split; [img_refl | img_lia].
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
cbn [fst snd base_val] in Hr; rewrite HE in Hr by img_lia;
rewrite ?E2, ?EaT, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia;
unfold sp0 in *; img_lia.
- destruct odd; [|img_try (destruct Hin)]. destruct Hin as [<-|[]]. cbn [fst snd base_val] in Hr. rewrite HE in Hr by (img_try (clear; (img_case; cbv); img_lia)).
rewrite EaPB in Hr. unfold w64 in Hr. unfold kHighMemBeg in DR. rewrite unsigned_lit_small in Hr by img_lia.
unfold WIN1, PBW. right; right; right; right. split; [img_refl | img_lia].
Qed.
Lemma windows_WIN : forall odd (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN odd a.
Proof.
intros odd E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
img_exact (WSKEL_WIN odd E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma windows_WIN1 : forall odd (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL1 odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WIN1 odd a.
Proof.
intros odd E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub).
img_exact (WSKEL1_WIN1 odd E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma frame_WIN1 : forall odd (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) (WSKEL1 odd) || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN1 odd (bv_unsigned x) -> m' x = m x.
Proof. intros odd E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN1 odd E rs _ HE Hb Hw). Qed.
Lemma WIN_not_high : forall odd a, sp0 <= a < ly_top ly -> ~ WIN odd a.
Proof.
intros odd a Ha Hw. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
pose proof Kv_range as HK. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
destruct (F9 a) as [N1 N2]; [img_try (unfold ASTACK in *; img_lia)|].
pose proof RZ_num as RZN. ceil; unfold WIN, WINT, PBW, zone3, kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize, kThreadObjSize, ASTACK, t_cache, t_unwinding, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg in *. img_lia.
Qed.
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Hypothesis SEED : st_ok tfxsegs E0 SS0K (restrict (w_H W) (mkst regs0 (w64 (0x53104 + D_2c4)) mem0 (seg_rom tfxsegs))).
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)]. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. img_apply apresent_writable_off; [img_try (img_exact Hh)|]. img_apply Hpr. img_apply writable_off_apresent; [img_try (img_exact Hh) | img_try (img_exact Hw)].
Qed.
Definition SKEL_TAIL {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0K).
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly).
Proof.
pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. clear HD.
destruct Hsp as (S1 & S2 & S3 & S4). unfold zdisjoint, kThreadObjSize, ASTACK, kPrimResvSize in *. cbn [fst snd] in *. unfold T.
split; [img_try (clear PS CS; img_lia)|]. split; [img_try (clear TS CS; img_lia)|]. clear TS PS; img_lia.
Qed.
Lemma stack_ivs2 :
(ly_NB ly + kNodesBlockSize <= sp0 - ASTACK \/ sp0 <= ly_NB ly) /\ (ly_SB ly + kStoreBlockSize <= sp0 - ASTACK \/ sp0 <= ly_SB ly).
Proof.
pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij _ _ 4 3 _ _ HD eq_refl eq_refl) as NS. pose proof (pairwise_ij _ _ 5 2 _ _ HD eq_refl eq_refl) as BS. clear HD.
destruct Hsp as (S1 & S2 & S3 & S4). unfold zdisjoint, ASTACK, kNodesBlockSize, kStoreBlockSize in *. cbn [fst snd] in *.
split; [img_try (clear BS; img_lia) | img_try (clear NS; img_lia)].
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
kNodesBlockSize, kStoreBlockSize, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg in *. unfold T in *.
destruct Ha as [Ha|[Ha|Ha]].
- clear NBhi SBhi TNB TSB PNB PSB NBS SBS HKR HSP. repeat split; img_lia.
- clear SBhi TSB PSB SBS F1 F2 F7 F8. repeat split; img_lia.
- clear NBhi TNB PNB NBS F1 F2 F7 F8. repeat split; img_lia.
Qed.
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFX_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFX_IMG_LO)) /\
((hi <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= lo) /\ (hi <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= lo) /\
(hi <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= lo)) /\
((hi <= SUv \/ PBv <= lo) /\ (hi <= Kv + RZ \/ Kv + RZ + 4096 <= lo) /\ (hi <= PBv \/ PBv + 1 <= lo)).
Lemma zone_lit : forall lo hi wlo whi,
TFX_IMG_LO <= lo -> hi <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= lo -> hi <= TFX_IMG_END -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof derived_ranges as DR. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 DR NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivs as (DT & _ & _). pose proof blocks_facts as (_ & _ & TNB & TSB & _ & _ & _ & _ & PT).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in TNB, TSB, PT. cbn [fst snd] in TNB, TSB, PT. numconst. unfold T in *.
clear - Hz0 Hz1 Hz2 DR F1 F2 F3 F4 F5 F6 DT TNB TSB PT HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof stack_ivs as (_ & _ & DC). pose proof HC_NB as (CNB & CSB). pose proof HCX as (CP & _).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in CNB, CSB, CP. cbn [fst snd] in CNB, CSB, CP. numconst.
clear - Hz0 Hz1 Hz2 DR F3 F4 F5 F6 F7 F8 DC CNB CSB CP HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_K : forall lo hi wlo whi,
Kv <= lo -> hi <= Kv + RZ -> (whi <= wlo \/ (Kv <= wlo /\ whi <= Kv + RZ)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_ranges as DR. pose proof high_facts as (_ & _ & F3 & F4 & F5 & F6 & _).
pose proof stack_ivs as (_ & DP & _). pose proof blocks_facts as (_ & _ & _ & _ & PNB & PSB & _).
pose proof Kv_range as HKR. pose proof (lo_space_in ly LY) as HSP.
unfold RFACTS. unfold zdisjoint in PNB, PSB. cbn [fst snd] in PNB, PSB. numconst.
clear - Hz0 Hz1 Hz2 DR F3 F4 F5 F6 DP PNB PSB HKR HSP. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_SH : forall lo hi wlo whi,
0x2008fff7000 <= lo -> hi <= kHighMemBeg -> hi <= SUv -> (whi <= wlo \/ (lo <= wlo /\ whi <= hi)) ->
RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof derived_ranges as DR. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 DR NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma tail_ext_ok : forall (E : env) r,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAIL ->
let b := base_val E (YQ0b.r_base r) in
(b + YQ0b.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YQ0b.r_lo r) /\ 0 <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= 2 ^ 64 /\
(YQ0b.r_whi r <= YQ0b.r_wlo r \/ (TFX_IMG_END <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= 2 ^ 64) \/ (0 <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= TFX_IMG_LO)) /\
((b + YQ0b.r_hi r <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= b + YQ0b.r_lo r)) /\
((b + YQ0b.r_hi r <= SUv \/ PBv <= b + YQ0b.r_lo r) /\ (b + YQ0b.r_hi r <= Kv + RZ \/ Kv + RZ + 4096 <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= PBv \/ PBv + 1 <= b + YQ0b.r_lo r)).
Proof.
intros E r HE Hin. pose proof derived_ranges as DR. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
let sk := img_ev constr:(SKEL_TAIL) in img_change SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); img_lia)); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaK, ?EaU, ?EaSK, ?EaSSLOT, ?EaPB, ?EaPV; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T in *; img_lia)).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R) by (img_try (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)) end.
all: first [ img_apply zone_lit; clear - DR; numconst; unfold TFX_TSD, TFX_TP; img_lia
| img_apply zone_SH; clear - DR; numconst; img_lia
| img_apply zone_K; clear - DR; numconst; img_lia
| img_apply zone_T; clear - DR F1 F2; numconst; unfold T in *; img_lia
| img_apply zone_C; clear - DR F7 F8; numconst; img_lia ].
Qed.
Definition at_ST (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WIN false (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).
Definition at_ST2 (ss : sstate) (z : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env) regs2 mem2,
c' = mkCfg (mkst regs2 (Z_to_bv 64 (0x31cc8 + D_150)) mem2 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WIN false (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)) /\
regs_preserved (ms_regs ms) regs2 /\
(forall x : word, ~ (sp0 - 2272 - DEP_STK <= bv_unsigned x < sp0 - 2272) -> ~ DZONE (bv_unsigned x) -> mem2 x = ms_mem ms x) /\
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem2 a) /\
DPOST z mem2.
Definition at_S2 (odd : bool) (ss : sstate) (z : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env) memD,
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
(forall x : word, DZONE (bv_unsigned x) -> ms_mem ms x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> ms_mem ms x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) PBv 1 (NPv mod 8)).
Definition at_RET (odd : bool) (z : Z) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (Kv + RZ) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, DZONE a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, DZONE (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ WIN odd (bv_unsigned x) -> ~ DZONE (bv_unsigned x) -> ~ (Kv + RZ <= bv_unsigned x < Kv + RZ + NPv) ->
~ (SUv <= bv_unsigned x < SUv + N8D / 8) -> mem' x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, WINT a \/ (Kv <= a < Kv + RZ + NPv) \/ PBW odd a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem tfxsegs m (Kv + RZ - 16) 1 2 /\ val_mem tfxsegs m (Kv + RZ - 15) 1 (hdr_byte1 jb) /\
val_mem tfxsegs m (Kv + RZ - 14) 2 0 /\ val_mem tfxsegs m (Kv + RZ - 12) 4 NPv /\
val_mem tfxsegs m Pv 4 (cnt - 1) /\ val_mem tfxsegs m (T + t_unwinding) 1 0 /\
(forall x : word, SUv <= bv_unsigned x < SUv + N8D / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem tfxsegs m PBv 1 (NPv mod 8)) /\
(forall x : word, Kv + RZ <= bv_unsigned x < Kv + RZ + FILv -> mem' x = Some (Z_to_bv 8 190)).
Ltac frame_acc HE :=
match goal with
| MEQ : (forall x : word, ~ WIN1 ?odd (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WIN1 odd (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WIN1 odd E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Lemma memset_stretch : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ img_apply store_ok_of_all; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); [img_lia|]. intros x Hx.
pose proof (apresent_writable (w_H W) (ms_mem ms) (bv_unsigned x) ltac:(img_try (pose proof (u64_range x); unfold TFX_IMG_END in *; img_lia)) (Hpres (bv_unsigned x) ltac:(img_lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw. }
destruct (tfx_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfxsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)) SOK
ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; img_lia)).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by img_lia. f_equal. rewrite Z.add_0_r.
img_change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by img_lia. img_change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [img_lia|]. symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_lia | img_try (img_exact Hrpc)]. }
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
destruct (base.decide (r = 10%bv)) as [->|N10]; [img_try (rewrite H10', H10; img_refl)|].
img_apply Hfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- img_exact H10'.
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros x Hx. destruct (Hpres (bv_unsigned x) Hx) as [Hh _]. rewrite Z_to_bv_bv_unsigned in Hh.
(subst m1full; cbv beta). unfold munrestrict. rewrite Hh. (subst m1 bs; cbv beta). rewrite wbytes_repeat_spec by (img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)).
rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)).
replace ((d <=? bv_unsigned x) && (bv_unsigned x <? d + Z.of_nat (Z.to_nat len))) with true; [img_refl|].
symmetry. img_apply andb_true_intro. split; [img_try (img_apply Z.leb_le) | img_try (img_apply Z.ltb_lt)]; img_lia.
Qed.
Variables (B : asyms) (S : astate) (l : list Z) (off : Z).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Hypothesis Hcsz_def : csz = class_size cl.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W) mem0) SSLOTv 8 j4.
Hypothesis Hjb_def : val_mem tfxsegs (mrestrict (w_H W) mem0) (Kv + RZ - 15) 1 jb.
Hypothesis HQT : qtight S.
Lemma case0_sizes :
rz_log n = 0 /\ rz_size n = RZ /\ rounded_size n = R8v /\ needed_primary n = R8v + RZ /\
from_primary n = true /\ needed_size n = R8v + RZ /\ req_size n = NPv.
Proof.
clear - Nrange. unfold RZ.
assert (L : rz_log n = 0) by (img_try (unfold rz_log; destruct (Z.leb_spec n 48); [img_refl|img_lia])).
assert (RS : rz_size n = 16) by (img_try (unfold rz_size; rewrite L; img_refl)).
assert (R8 : rounded_size n = R8v) by (img_try (unfold rounded_size, round_up, R8v; f_equal; f_equal; img_lia)).
assert (NP : needed_primary n = R8v + 16) by (img_try (unfold needed_primary; rewrite R8, RS; img_refl)).
assert (FP : from_primary n = true).
{ unfold from_primary. rewrite NP. img_apply Z.leb_le. unfold R8v, kMaxSize.
pose proof (Z.div_mod (Z.max n 8 + 7) 8 ltac:(img_lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 7) 8 ltac:(img_lia)). img_lia. }
repeat split; try assumption.
- unfold needed_size. rewrite FP. img_exact NP.
- unfold req_size, NPv. destruct (Z.eqb_spec n 0); img_lia.
Qed.
Lemma Kv_is_sptr : Kv = sptr_addr B ly (PPrim (region_off cl + off)).
Proof. clear - Hoff_def Hcl. unfold Kv, SB, sptr_addr. cbn. rewrite region_off_eq by img_lia. img_lia. Qed.
End g.
End f.
