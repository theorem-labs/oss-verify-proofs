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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64 YF3v YF3w YF3x YF41 YF6z YF07.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Export YF6q.
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
Lemma ltHAV (k : nat) : Nat.ltb k sHAV = true -> (k < sHAV)%nat.
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
Definition mzone {imgk : img} (x sz : Z) : Prop := zone3 x sz.
Lemma mzone_zone3 {imgk : img} : forall x sz, mzone x sz -> zone3 x sz. Proof. intros x sz H. img_exact H. Qed.
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (n : Z) (ch : list (Z * Z * Z)).
Variables (idx res j0 j1 j2 j3 j4 j5 j6 j7 j8 j9 i1 i2 i3 : Z).
Variable mb : Z.
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Let Qb : Z := ly_Q ly.
Definition R8v : Z := (n + 7) / 8 * 8.
Definition N8D : Z := n / 8 * 8.
Definition NDv : Z := R8v + 4096.
Definition MSv : Z := (NDv + 4095) / 4096 * 4096 + 4096.
Definition SHBv : Z := 0x7fff8000.
Definition QSv : Z := Qb + 8 * idx.
Definition Kv : Z := mb + 4096.
Definition Uv : Z := mb + 6144.
Definition ENDv : Z := mb + 4096 + NDv.
Definition TLv : Z := MSv - 4096 - NDv.
Definition UEv : Z := mb + 6144 + R8v.
Definition RLv : Z := MSv - R8v - 6144.
Definition SMv : Z := SHBv + mb / 8.
Definition PBv : Z := SHBv + (mb + 6144 + N8D) / 8.
Definition LGv : Z := Z.log2 (MSv / 4096) + 12.
Definition BSLv {imgk : img} : Z := TFX_INST + 168 + 8 * LGv.
Definition tr : list Z := call_trace ly (0x53640 + D_2c4) regs0 ch.
Definition XW : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 (Z.of_nat (length tr)); w64 j0; w64 R8v;
w64 Qb; w64 res; w64 idx; w64 MSv; w64 j5; w64 j6; w64 mb; w64 ENDv; w64 SHBv; w64 TLv;
w64 j1; w64 j2; w64 j3; w64 QSv; w64 j4; w64 j7; w64 BSLv; w64 j8; w64 j9; w64 i1; w64 i2; w64 i3;
w64 SMv; w64 UEv; w64 NDv; w64 RLv; w64 N8D; w64 PBv; w64 0; w64 0; w64 0 ].
Definition E0 : env := Ereg regs0 XW.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XW k r Hk). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E4 : ew E0 4 = getr regs0 4. Proof. img_exact (Er 4 4%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. img_exact (Er 8 8%bv eq_refl). Qed.
Lemma E10 : ew E0 10 = getr regs0 10. Proof. img_exact (Er 10 10%bv eq_refl). Qed.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma EaR8 : ew E0 38 = w64 R8v. Proof. img_refl. Qed.
Lemma EaQ : ew E0 39 = w64 Qb. Proof. img_refl. Qed.
Lemma EaRES : ew E0 40 = w64 res. Proof. img_refl. Qed.
Lemma EaNCH : ew E0 41 = w64 idx. Proof. img_refl. Qed.
Lemma EaMS : ew E0 42 = w64 MSv. Proof. img_refl. Qed.
Lemma EaMAP : ew E0 45 = w64 mb. Proof. img_refl. Qed.
Lemma EaEND : ew E0 46 = w64 ENDv. Proof. img_refl. Qed.
Lemma EaSHB : ew E0 47 = w64 SHBv. Proof. img_refl. Qed.
Lemma EaTL : ew E0 48 = w64 TLv. Proof. img_refl. Qed.
Lemma EaQS : ew E0 52 = w64 QSv. Proof. img_refl. Qed.
Lemma EaBSL : ew E0 55 = w64 BSLv. Proof. img_refl. Qed.
Lemma EaSM : ew E0 61 = w64 SMv. Proof. img_refl. Qed.
Lemma EaUE : ew E0 62 = w64 UEv. Proof. img_refl. Qed.
Lemma EaND : ew E0 63 = w64 NDv. Proof. img_refl. Qed.
Lemma EaRL : ew E0 64 = w64 RLv. Proof. img_refl. Qed.
Lemma EaN8D : ew E0 65 = w64 N8D. Proof. img_refl. Qed.
Lemma EaPB : ew E0 66 = w64 PBv. Proof. img_refl. Qed.
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
Hypothesis Nrange : 64513 <= n < MALLOC_MAX.
Hypothesis Hidx : 0 <= idx < kMaxNumChunks.
Hypothesis Hres : idx <= res <= kMaxNumChunks /\ res mod kPtrArrayEntriesPerCommit = 0.
Lemma mod0_of_mul : forall k b, 0 < b -> (k * b) mod b = 0.
Proof. intros k b Hb. img_apply Z_mod_mult. Qed.
Lemma size_facts :
64520 <= R8v <= MALLOC_MAX /\ R8v mod 8 = 0 /\ n <= R8v < n + 8 /\
64512 <= N8D <= n /\ N8D mod 8 = 0 /\ n < N8D + 8 /\
NDv = R8v + 4096 /\ 73728 <= MSv <= MALLOC_MAX + 8192 /\ MSv mod 4096 = 0 /\ NDv + 4096 <= MSv < NDv + 8192 /\
0 <= TLv <= 4088 /\ TLv mod 8 = 0 /\ 2048 <= RLv <= 2048 + 4088 /\ RLv mod 8 = 0.
Proof.
unfold TLv, RLv, MSv, NDv, R8v, N8D, MALLOC_MAX in *. clear - Nrange.
pose proof (Z.div_mod (n + 7) 8 ltac:(img_lia)) as A1. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(img_lia)) as A2.
pose proof (Z.div_mod n 8 ltac:(img_lia)) as B1. pose proof (Z.mod_pos_bound n 8 ltac:(img_lia)) as B2.
set (p := (n + 7) / 8) in *. set (p' := n / 8) in *.
pose proof (Z.div_mod (p * 8 + 4096 + 4095) 4096 ltac:(img_lia)) as C1. pose proof (Z.mod_pos_bound (p * 8 + 4096 + 4095) 4096 ltac:(img_lia)) as C2.
set (q := (p * 8 + 4096 + 4095) / 4096) in *.
assert (M1 : (p * 8) mod 8 = 0) by (img_try (img_apply mod0_of_mul; img_lia)).
assert (M2 : (p' * 8) mod 8 = 0) by (img_try (img_apply mod0_of_mul; img_lia)).
assert (M3 : (q * 4096 + 4096) mod 4096 = 0) by (img_try (replace (q * 4096 + 4096) with ((q + 1) * 4096) by img_lia; img_apply mod0_of_mul; img_lia)).
assert (M4 : (q * 4096 + 4096 - 4096 - (p * 8 + 4096)) mod 8 = 0).
{ replace (q * 4096 + 4096 - 4096 - (p * 8 + 4096)) with ((q * 512 - p - 512) * 8) by img_lia. img_apply mod0_of_mul; img_lia. }
assert (M5 : (q * 4096 + 4096 - p * 8 - 6144) mod 8 = 0).
{ replace (q * 4096 + 4096 - p * 8 - 6144) with ((q * 512 - p - 256) * 8) by img_lia. img_apply mod0_of_mul; img_lia. }
repeat split; try assumption; clear M1 M2 M3 M4 M5; nia.
Qed.
Lemma tr_length : (1 <= length tr <= 30)%nat.
Proof. unfold tr, call_trace. destruct (frame0_ok ly regs0); [img_try (img_apply unwind_of_chain_length) | img_try (cbn; img_lia)]. Qed.
Lemma high_facts :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ zone3 Qb kPtrArrayResv /\ Qb + kPtrArrayResv <= ASAN_CEIL /\ Qb mod 4096 = 0 /\
T mod 4096 = 0 /\ SB mod 65536 = 0 /\ ly_C ly mod 8 = 0 /\
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly ->
~ (T <= a < T + kThreadObjSize) /\ ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize) /\ ~ (Qb <= a < Qb + kPtrArrayResv) /\ ~ (ly_C ly <= a < ly_C ly + 256)).
Proof.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD. pose proof (lo_space_in ly LY) as HSP.
pose proof (Forall_nth' _ _ 1 _ HA eq_refl) as IQ. pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC.
cbn beta in IQ, IT, IC. cbn [fst snd] in IQ, IT, IC.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 1 6 _ _ HD eq_refl eq_refl) as QS. pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS.
pose proof (lo_Q_al ly LY) as QA. pose proof (lo_T_al ly LY) as TA. pose proof (lo_space_al ly LY) as SA. pose proof (lo_C_al ly LY) as CA.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly Qb kPtrArrayResv IMG ltac:(img_try (clear_all; unfold kPtrArrayResv; img_lia)) IQ (pairwise_ij _ _ 1 7 _ _ HD eq_refl eq_refl)) as ZQ.
clear HA HD. pose proof ASAN_CEIL_range as [CR _].
unfold in_high, in_app, zdisjoint, page_aligned, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. unfold T, SB, Qb in *.
split; [img_try (img_exact ZT)|]. split; [img_try (clear - IT CR; img_lia)|]. do 4 (split; [img_try (clear TS PS QS CS ZT ZC ZQ; img_lia)|]).
split; [img_try (img_exact ZC)|]. split; [img_try (clear - IC CR; img_lia)|]. split; [img_try (img_exact ZQ)|]. split; [img_try (clear - IQ CR; img_lia)|].
do 4 (split; [img_try (clear TS PS QS CS ZT ZC ZQ; img_lia)|]).
intros a Ha; repeat split; intros Hx; [img_try (clear PS QS CS) | img_try (clear TS QS CS) | img_try (clear TS PS CS) | img_try (clear TS PS QS)]; clear ZT ZC ZQ; img_lia.
Qed.
Lemma stack_ivs :
(T + kThreadObjSize <= sp0 - ASTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - ASTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - ASTACK \/ sp0 <= ly_C ly) /\ (Qb + kPtrArrayResv <= sp0 - ASTACK \/ sp0 <= Qb).
Proof.
pose proof (lo_disj ly LY) as HD.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. pose proof (pairwise_ij _ _ 1 6 _ _ HD eq_refl eq_refl) as QS. clear HD.
destruct Hsp as (S1 & S2 & S3 & S4). unfold zdisjoint, kThreadObjSize, ASTACK, kPrimResvSize, kPtrArrayResv in *. cbn [fst snd] in *. unfold T, Qb.
split; [img_try (clear PS CS QS; img_lia)|]. split; [img_try (clear TS CS QS; img_lia)|]. split; [img_try (clear TS PS QS; img_lia)|]. clear TS PS CS; img_lia.
Qed.
Lemma HCX : zdisjoint (ly_C ly, 256) (ly_prim ly, kPrimResvSize) /\ zdisjoint (ly_C ly, 256) (ly_T ly, kThreadObjSize) /\ zdisjoint (Qb, kPtrArrayResv) (ly_T ly, kThreadObjSize) /\ zdisjoint (ly_C ly, 256) (Qb, kPtrArrayResv).
Proof.
pose proof (lo_disj ly LY) as HD. unfold Qb.
split; [|img_try (split; [|split])];
[ img_try (img_apply zdisjoint_sym; img_exact (pairwise_ij _ _ 0 5 _ _ HD eq_refl eq_refl)) | img_try (img_apply zdisjoint_sym; img_exact (pairwise_ij _ _ 2 3 _ _ HD eq_refl eq_refl))
| img_try (img_exact (pairwise_ij _ _ 1 0 _ _ HD eq_refl eq_refl)) | img_try (img_apply zdisjoint_sym; img_exact (pairwise_ij _ _ 1 4 _ _ HD eq_refl eq_refl)) ].
Qed.
Hypothesis Hpres0 : forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis Hmap : mb mod 4096 = 0 /\ mzone mb MSv.
Hypothesis Hmap_apart :
zdisjoint (mb, MSv) (T, kThreadObjSize) /\ zdisjoint (mb, MSv) (ly_C ly, kCtxMapSize) /\
zdisjoint (mb, MSv) (ly_prim ly, kPrimResvSize) /\ zdisjoint (mb, MSv) (Qb, kPtrArrayResv) /\
zdisjoint (mb, MSv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (mb, MSv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (mb, MSv) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly).
Lemma map_facts :
TFX_IMG_END <= mb /\ mb + MSv <= ASAN_CEIL /\ mb mod 4096 = 0 /\ Kv = mb + 4096 /\ Uv = mb + 6144 /\
ENDv = Uv + R8v + 2048 /\ UEv = Uv + R8v /\ ENDv mod 8 = 0 /\ UEv mod 8 = 0 /\ mb + MSv = ENDv + TLv /\ mb + MSv = UEv + RLv /\
kLowShadowBeg + TFX_IMG_END / 8 <= SMv /\ SMv + MSv / 8 <= kHighShadowEnd /\ SMv mod 512 = 0 /\ PBv = SMv + 768 + N8D / 8 /\ SMv = shadow_addr mb.
Proof.
pose proof Hmap as [M1 HZ]. unfold mzone, zone3 in HZ. destruct HZ as (M0 & M2 & MZ). pose proof size_facts as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & Z10 & Z11 & Z12 & Z13 & Z14).
ceil; unfold zone3cases, Kv, Uv, ENDv, UEv, TLv, RLv, SMv, PBv, SHBv, shadow_addr, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END, ASAN_CEIL, MALLOC_MAX in *.
apply Z.mod_divide in M1 as [qm Hqm]; [|img_lia]. apply Z.mod_divide in Z2 as [q8 Hq8]; [|img_lia]. apply Z.mod_divide in Z5 as [qn Hqn]; [|img_lia].
repeat split; try img_lia.
all: try (rewrite Hqm, Hq8; replace (qm * 4096 + 6144 + q8 * 8 + 2048) with ((qm * 512 + 1024 + q8) * 8) by img_lia; img_apply Z_mod_mult).
all: try (rewrite Hqm, Hq8; replace (qm * 4096 + 6144 + q8 * 8) with ((qm * 512 + 768 + q8) * 8) by img_lia; img_apply Z_mod_mult).
all: try (rewrite Hqm; replace (qm * 4096 / 8) with (qm * 512) by (img_try (symmetry; img_apply Z.div_unique_exact; img_lia)); img_apply Z.mod_divide; [img_lia|]; exists (68719411200 + qm); img_lia).
all: try (rewrite Hqm, Hqn; replace (qm * 4096 + 6144 + qn * 8) with ((qm * 512 + 768 + qn) * 8) by img_lia; rewrite Z_div_mult by img_lia;
replace (qm * 4096 / 8) with (qm * 512) by (img_try (symmetry; img_apply Z.div_unique_exact; img_lia)); img_lia).
all: try (rewrite Hqm; replace (qm * 4096 / 8) with (qm * 512) by (img_try (symmetry; img_apply Z.div_unique_exact; img_lia)); img_lia).
Qed.
Lemma map_zone :
(TFX_IMG_END <= mb /\ mb + MSv <= kLowShadowBeg /\ kLowShadowBeg + TFX_IMG_END / 8 <= SMv /\ SMv + MSv / 8 <= kLowShadowEnd) \/
(kHighMemBeg <= mb /\ mb + MSv <= ASAN_CEIL /\ kHighShadowBeg <= SMv /\ SMv + MSv / 8 <= kHighShadowEnd).
Proof.
pose proof Hmap as [M1 HZ]. unfold mzone, zone3 in HZ. destruct HZ as (M0 & M2 & MZ). pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _).
ceil; unfold zone3cases, SMv, SHBv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFX_IMG_LO, TFX_IMG_END, ASAN_CEIL, MALLOC_MAX in *.
apply Z.mod_divide in M1 as [qm Hqm]; [|img_lia]. assert (Hd : mb / 8 = qm * 512) by (img_try (rewrite Hqm; symmetry; img_apply Z.div_unique_exact; img_lia)). rewrite Hd.
assert (HM8 : 8 * (MSv / 8) <= MSv) by (img_try (img_apply Z.mul_div_le; img_lia)). pose proof (Z.mul_div_le MSv 8 ltac:(img_lia)). img_lia.
Qed.
Lemma map_zoneN :
((6287360 + D_1000) <= mb /\ mb + MSv <= 2147446784 /\ 2148217856 <= SMv /\ SMv + MSv / 8 <= 2415881728) \/
(17594333495296 <= mb /\ mb + MSv <= ASAN_CEIL /\ 140735332483072 <= ASAN_CEIL <= 140737479966720 /\
2201439137792 <= SMv /\ SMv + MSv / 8 <= 17594333495296).
Proof.
pose proof map_zone as MZ. pose proof Hmap as [M3 _]. pose proof map_facts as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SMA).
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & _ & Z9 & _).
rewrite SMA in MZ |- *. unfold shadow_addr, SHADOW_OFF in *. clear - MZ M1 M3 Z9 rc. ceil.
unfold kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFX_IMG_END in *.
apply Z.mod_divide in M3 as [p Hp]; [|img_lia]. apply Z.mod_divide in Z9 as [u Hu]; [|img_lia]. rewrite Hp, Hu in *.
replace (p * 4096) with ((p * 512) * 8) in * by img_lia. replace (u * 4096) with ((u * 512) * 8) in * by img_lia. rewrite !Z.div_mul in * by img_lia. img_lia.
Qed.
Lemma map_in_band : forall a, SMv <= a < SMv + MSv / 8 -> in_band_rw a.
Proof. intros a Ha. unfold in_band_rw. pose proof map_zone as MZ. clear - Ha MZ. unfold kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, TFX_IMG_END in *. img_lia. Qed.
Lemma map_off_img : forall a, mb <= a < mb + MSv -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (mzone_zone3 _ _ (proj2 Hmap)) Ha). Qed.
Definition WINT (a : Z) : Prop :=
(T + 2768 <= a < T + 2824) \/ (T + 2872 <= a < T + 2888) \/ (T + 2904 <= a < T + 2912) \/ (T + t_unwinding <= a < T + t_unwinding + 1).
Definition WINI {imgk : img} (a : Z) : Prop :=
(TFX_INST + o_sec_reserved <= a < TFX_INST + o_sec_sorted + 1) \/ (TFX_INST + o_sec_stats <= a < TFX_INST + o_sec_stats + 32) \/
(BSLv <= a < BSLv + 8) \/ (TFX_INST + o_sec_mutex <= a < TFX_INST + o_sec_mutex + 4) \/ ((0xa6e08 + D_10c0) <= a < (0xa6e30 + D_10c0)).
Definition WINM (a : Z) : Prop := (QSv <= a < QSv + 8) \/ (mb <= a < mb + MSv) \/ (SMv <= a < SMv + MSv / 8).
Definition WIN (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ WINT a \/ WINI a \/ WINM a.
Definition WINN (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ WINT a \/ (TFX_OOM <= a < TFX_OOM + 1) \/ (TFX_ERRNO <= a < TFX_ERRNO + 4).
Definition WINP (a : Z) : Prop := (sp0 - ASTACK <= a < sp0) \/ WINT a \/ WINI a.
Lemma WINP_WIN : forall a, WINP a -> WIN a.
Proof. intros a H. unfold WIN. unfold WINP in H. destruct H as [H|[H|H]]; [img_try (left) | img_try (right; left) | img_try (right; right; left)]; img_exact H. Qed.
Definition WIN1P (a : Z) : Prop := (sp0 - ASTACK <= a < sp0 - IFRAME) \/ (sp0 - 64 <= a < sp0) \/ WINT a \/ WINI a.
Definition WIN1 (a : Z) : Prop := WIN1P a \/ WINM a.
Lemma WIN1P_WINP : forall a, WIN1P a -> WINP a.
Proof. intros a H. unfold WIN1P, WINP, IFRAME, ASTACK in *. destruct H as [H|[H|H]]; [img_try (left; img_lia) | img_try (left; img_lia) | img_try (right; img_exact H)]. Qed.
Lemma WIN1_WIN : forall a, WIN1 a -> WIN a.
Proof. intros a [H|H]; [img_try (apply WINP_WIN, WIN1P_WINP, H) | img_try (unfold WIN; right; right; right; img_exact H)]. Qed.
Lemma WIN1P_WIN1 : forall a, WIN1P a -> WIN1 a.
Proof. intros a H. left. img_exact H. Qed.
Lemma LGv_range : 16 <= LGv <= 28.
Proof.
pose proof size_facts as (_ & _ & _ & _ & _ & _ & _ & Z8 & Z9 & _). unfold LGv, MALLOC_MAX in *. clear - Z8 Z9.
assert (Hp : 18 <= MSv / 4096 <= 65538).
{ split; [img_try (img_apply Z.div_le_lower_bound; img_lia) | img_try (img_apply Z.div_le_upper_bound; img_lia)]. }
pose proof (Z.log2_le_mono 18 (MSv / 4096) ltac:(img_lia)) as L1. pose proof (Z.log2_le_mono (MSv / 4096) 65538 ltac:(img_lia)) as L2.
rewrite (eq_refl : Z.log2 18 = 4) in L1. rewrite (eq_refl : Z.log2 65538 = 16) in L2. img_lia.
Qed.
Lemma BSLv_range : TFX_INST + 296 <= BSLv <= TFX_INST + 392.
Proof. pose proof LGv_range. unfold BSLv. img_lia. Qed.
Definition WSKELP {imgk : img} : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, 0); (Some 32%nat, 2768, 2800); (Some 32%nat, t_unwinding, t_unwinding + 1); (Some 32%nat, 2800, 2824);
(Some 32%nat, 2872, 2888); (Some 32%nat, 2904, 2912);
(None, TFX_INST + o_sec_reserved, TFX_INST + o_sec_sorted + 1); (None, TFX_INST + o_sec_stats, TFX_INST + o_sec_stats + 32);
(None, TFX_INST + o_sec_mutex, TFX_INST + o_sec_mutex + 4); (None, (0xa6e08 + D_10c0), (0xa6e30 + D_10c0)); (Some aBSL, 0, 8)].
Definition WSKEL1P {imgk : img} : list (option nat * Z * Z) :=
[(Some 2%nat, - ASTACK, - IFRAME); (Some 2%nat, -64, 0)] ++ tl WSKELP.
Definition WMAP : list (option nat * Z * Z) := [(Some aQS, 0, 8); (Some aMAP, 0, 6144); (Some aPBS, 0, 1)].
Definition WSKEL {imgk : img} : list (option nat * Z * Z) := WSKELP ++ WMAP.
Definition WSKEL1 {imgk : img} : list (option nat * Z * Z) := WSKEL1P ++ WMAP.
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
Definition in_win (E : env) (a : Z) (t : option nat * Z * Z) : Prop :=
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t.
Lemma WSKELP_WINP : forall (E : env) a t,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In t WSKELP -> in_win E a t -> WINP a.
Proof. try clear Hmap_apart; try clear Hmap.
intros E a t HE Hin Hr. pose proof high_facts as (F1 & F2 & _). pose proof BSLv_range as HB. unfold in_win in Hr.
unfold WSKELP in Hin. cbn [In] in Hin. unfold WINP, WINT, WINI.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, sHAV, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, aBSL in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by img_lia;
rewrite ?E2, ?EaT, ?EaBSL in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia; unfold sp0 in *; img_lia.
Qed.
Lemma WSKEL1P_WIN1P : forall (E : env) a t,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In t WSKEL1P -> in_win E a t -> WIN1P a.
Proof. try clear Hmap_apart; try clear Hmap.
intros E a t HE Hin Hr. pose proof high_facts as (F1 & F2 & _). pose proof BSLv_range as HB. unfold in_win in Hr.
unfold WSKEL1P, WSKELP in Hin. cbn [tl app In] in Hin. unfold WIN1P, WINT, WINI.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, t_unwinding, kThreadObjSize, sHAV, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex, aBSL, IFRAME in *.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; rewrite ?HE in Hr by img_lia;
rewrite ?E2, ?EaT, ?EaBSL in Hr; unfold w64 in Hr; rewrite ?unsigned_lit_small in Hr by img_lia; unfold sp0 in *; img_lia.
Qed.
Lemma WMAP_WINM : forall (E : env) a t,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In t WMAP -> in_win E a t -> WINM a.
Proof.
intros E a t HE Hin Hr. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & F10 & _).
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _ & PB & _).
pose proof size_facts as (_ & _ & Z3 & Z4 & _ & _ & Z7 & Z8 & _ & Z10 & _). pose proof Hidx as HI.
unfold in_win in Hr. unfold WMAP in Hin. cbn [In] in Hin. unfold WINM.
ceil; unfold zone3, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFX_IMG_END, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, MALLOC_MAX, sHAV, aQS, aMAP, aPBS in *.
pose proof Nrange as NR. clear - HE Hr Hin F9 F10 M1 M2 SM1 SM2 PB Z3 Z4 Z7 Z8 Z10 HI NR CR CR0.
destruct Hin as [<-|[<-|[<-|[]]]]; cbn [fst snd base_val] in Hr; rewrite HE in Hr by img_lia.
- rewrite EaQS in Hr. unfold w64 in Hr. unfold QSv in *. rewrite unsigned_lit_small in Hr by img_lia. img_lia.
- rewrite EaMAP in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by img_lia. img_lia.
- rewrite EaPB in Hr. unfold w64 in Hr. rewrite PB in Hr. rewrite unsigned_lit_small in Hr by img_lia.
right; right. assert (HND : 8 * (N8D / 8) <= N8D) by (img_try (img_apply Z.mul_div_le; img_lia)).
assert (HM : N8D / 8 + 1024 <= MSv / 8) by (img_try (img_apply Z.div_le_lower_bound; img_lia)). img_lia.
Qed.
Lemma WSKEL_WIN : forall (E : env) a t,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In t WSKEL -> in_win E a t -> WIN a.
Proof.
intros E a t HE Hin Hr. unfold WSKEL in Hin. apply in_app_iff in Hin as [Hin|Hin].
- img_apply WINP_WIN. img_exact (WSKELP_WINP E a t HE Hin Hr).
- unfold WIN. right; right; right. img_exact (WMAP_WINM E a t HE Hin Hr).
Qed.
Lemma WSKEL1_WIN1 : forall (E : env) a t,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In t WSKEL1 -> in_win E a t -> WIN1 a.
Proof.
intros E a t HE Hin Hr. unfold WSKEL1 in Hin. apply in_app_iff in Hin as [Hin|Hin].
- left. img_exact (WSKEL1P_WIN1P E a t HE Hin Hr).
- right. img_exact (WMAP_WINM E a t HE Hin Hr).
Qed.
Lemma windows_in : forall (K : list (option nat * Z * Z)) (P : Z -> Prop) (E : env) rs a,
(forall t a, In t K -> in_win E a t -> P a) ->
forallb (fun t => existsb (win_sub t) K || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> P a.
Proof.
intros K P E rs a HK Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_apply (HK u a Hinu). img_exact (win_sub_sound E a _ u Hsub Hr).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma windows_WINP : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELP || (snd t <=? snd (fst t))) (windows rs) = true -> in_wrange E rs a -> WINP a.
Proof. intros E rs a HE. img_apply windows_in. intros t x Ht Hx. img_exact (WSKELP_WINP E x t HE Ht Hx). Qed.
Lemma windows_WIN1P : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL1P || (snd t <=? snd (fst t))) (windows rs) = true -> in_wrange E rs a -> WIN1P a.
Proof. intros E rs a HE. img_apply windows_in. intros t x Ht Hx. img_exact (WSKEL1P_WIN1P E x t HE Ht Hx). Qed.
Lemma windows_WIN : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL || (snd t <=? snd (fst t))) (windows rs) = true -> in_wrange E rs a -> WIN a.
Proof. intros E rs a HE. img_apply windows_in. intros t x Ht Hx. img_exact (WSKEL_WIN E x t HE Ht Hx). Qed.
Lemma windows_WIN1 : forall (E : env) rs a,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL1 || (snd t <=? snd (fst t))) (windows rs) = true -> in_wrange E rs a -> WIN1 a.
Proof. intros E rs a HE. img_apply windows_in. intros t x Ht Hx. img_exact (WSKEL1_WIN1 E x t HE Ht Hx). Qed.
Lemma frame_WIN1P : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL1P || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN1P (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN1P E rs _ HE Hb Hw). Qed.
Lemma frame_WIN1 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKEL1 || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WIN1 (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WIN1 E rs _ HE Hb Hw). Qed.
Lemma WINP_not_high : forall a, sp0 <= a < ly_top ly -> ~ WINP a.
Proof.
intros a Ha Hw. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F15).
pose proof (lo_top ly LY) as (_ & T2 & _ & _ & _ & _ & T7). pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _).
destruct (F15 a) as (N1 & _ & _ & _); [img_try (clear - Ha S1 S3 T2; unfold ASTACK in *; img_lia)|].
clear - Ha Hw N1 T7 S1 S3 T2 HB.
unfold WINP, WINT, WINI, kHighMemBeg, kThreadObjSize, ASTACK, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold T in *. img_lia.
Qed.
Lemma WIN_not_high : forall a, sp0 <= a < ly_top ly -> ~ WIN a.
Proof.
intros a Ha [Hw|[Hw|[Hw|Hw]]]; [img_apply (WINP_not_high a Ha); unfold WINP; ((left; img_exact Hw) || (right; left; img_exact Hw) || (right; right; img_exact Hw)) .. |].
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F15).
pose proof (lo_top ly LY) as (_ & T2 & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof Hidx as HI.
destruct Hsp as (S1 & _ & S3 & _).
destruct (F15 a) as (_ & _ & N3 & _); [img_try (clear - Ha S1 S3 T2; unfold ASTACK in *; img_lia)|].
clear - Ha Hw N3 T7 S1 S3 T2 SC M1 M2 SM1 SM2 HI.
ceil; unfold zone3, WINM, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFX_IMG_END, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK in *. unfold Qb in *. img_lia.
Qed.
Variables (mat0 : list word).
Let H0 := w_H W.
Let cfg0 : config := mkCfg (mkst regs0 (w64 (0x53108 + D_2c4)) mem0 (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis U1 : tfx_unwind_spec.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. intros E r rs H. induction rs as [|r' rs IH]; cbn; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)]. Qed.
Lemma img_rw_writable : forall (m : word -> option byte) a, (0xa1000 + D_1000) <= a < (0x5ff000 + D_1000) -> writable_at tfxsegs m a.
Proof. intros m a Ha. unfold writable_at. img_apply YF07.tfx_rw_window. rewrite unsigned_lit_small by img_lia. img_exact Ha. Qed.
Lemma kept_of_frame : forall (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H W) m a -> apresent (w_H W) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
((0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) \/ ((0xa1000 + D_1000) <= a < (0x5ff000 + D_1000))) ->
region_kept tfxsegs E (mrestrict (w_H W) m) (mrestrict (w_H W) m1) r.
Proof.
intros E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. destruct (Hwin a Ha) as [Hh|Hrw].
+ pose proof (Hh : off_img a) as Hh'. img_apply apresent_writable_off; [img_try (img_exact Hh')|]. img_apply Hpr. img_apply writable_off_apresent; [img_try (img_exact Hh') | img_try (img_exact Hw)].
+ img_apply img_rw_writable. img_exact Hrw.
Qed.
Definition SKEL_TAIL {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl SREG0).
Lemma blocks_facts :
zone3 (ly_NB ly) kNodesBlockSize /\ zone3 (ly_SB ly) kStoreBlockSize /\
zdisjoint (T, kThreadObjSize) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (T, kThreadObjSize) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (Qb, kPtrArrayResv) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (Qb, kPtrArrayResv) (ly_SB ly, kStoreBlockSize) /\
zdisjoint (ly_NB ly, kNodesBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_SB ly, kStoreBlockSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) /\
zdisjoint (ly_C ly, 256) (ly_NB ly, kNodesBlockSize) /\ zdisjoint (ly_C ly, 256) (ly_SB ly, kStoreBlockSize).
Proof.
pose proof (lo_app ly LY) as HI. pose proof (lo_disj ly LY) as HD.
pose proof (Forall_nth' _ _ 4 _ HI eq_refl) as I4. pose proof (Forall_nth' _ _ 5 _ HI eq_refl) as I5. cbn beta in I4, I5. cbn [fst snd] in I4, I5. unfold T, Qb.
split; [img_try (img_exact (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; img_lia) I4 (pairwise_ij _ _ 4 4 _ _ HD eq_refl eq_refl)))|].
split; [img_try (img_exact (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; img_lia) I5 (pairwise_ij _ _ 5 3 _ _ HD eq_refl eq_refl)))|].
split; [img_try (img_exact (pairwise_ij _ _ 2 1 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 2 2 _ _ HD eq_refl eq_refl))|].
split; [img_try (img_exact (pairwise_ij _ _ 1 2 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 1 3 _ _ HD eq_refl eq_refl))|].
split; [img_try (img_exact (pairwise_ij _ _ 4 3 _ _ HD eq_refl eq_refl))|]. split; [img_try (img_exact (pairwise_ij _ _ 5 2 _ _ HD eq_refl eq_refl))|].
split; img_apply zdisjoint_sym; [img_try (img_exact (pairwise_ij _ _ 4 1 _ _ HD eq_refl eq_refl)) | img_try (img_exact (pairwise_ij _ _ 5 0 _ _ HD eq_refl eq_refl))].
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 high_facts) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & F7 & _). img_exact (zone3_off_img _ _ a F7 Ha). Qed.
Lemma off_Q : forall a, Qb <= a < Qb + kPtrArrayResv -> off_img a.
Proof. intros a Ha. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _). img_exact (zone3_off_img _ _ a F9 Ha). Qed.
Lemma off_NB : forall a, ly_NB ly <= a < ly_NB ly + kNodesBlockSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 blocks_facts) Ha). Qed.
Lemma off_SB : forall a, ly_SB ly <= a < ly_SB ly + kStoreBlockSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 (proj2 blocks_facts)) Ha). Qed.
Lemma off_shadow : forall a, kLowShadowBeg <= a < kHighMemBeg -> off_img a.
Proof. intros a Ha. unfold off_img, kLowShadowBeg, kHighMemBeg, TFX_IMG_LO, TFX_IMG_END in *. img_lia. Qed.
Ltac off_by tac :=
first [ img_apply off_img_high; tac | img_apply off_T; tac | img_apply off_C; tac | img_apply off_Q; tac | img_apply off_NB; tac | img_apply off_SB; tac
| img_apply map_off_img; tac | img_apply off_shadow; tac
| unfold off_img; unfold TFX_IMG_LO; unfold TFX_IMG_END; tac ].
Definition DZONE (a : Z) : Prop :=
((0x17c088 + D_10c0) <= a < (0x5cc810 + D_10c0)) \/ (ly_NB ly <= a < ly_NB ly + kNodesBlockSize) \/ (ly_SB ly <= a < ly_SB ly + kStoreBlockSize).
Variable DPOST : Z -> (word -> option byte) -> Prop.
Lemma DZONE_disj : forall a, DZONE a -> ~ WIN a /\ ~ (sp0 - ASTACK <= a < sp0).
Proof.
intros a Ha. pose proof high_facts as (F1 & _ & _ & _ & _ & _ & _ & _ & F9 & _).
pose proof blocks_facts as (NBhi & SBhi & TNB & TSB & QNB & QSB & NBS & SBS & _).
destruct Hsp as (S1 & _ & S3 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof Hidx as HI.
destruct Hmap_apart as (_ & _ & _ & _ & MNB & MSB & _).
unfold zdisjoint in TNB, TSB, QNB, QSB, NBS, SBS, MNB, MSB. cbn [fst snd] in TNB, TSB, QNB, QSB, NBS, SBS, MNB, MSB.
clear - Ha F1 F9 NBhi SBhi TNB TSB QNB QSB NBS SBS T7 HB M1 M2 SM1 SM2 HI MNB MSB S1 S3.
unfold DZONE, WIN, WINT, WINI, WINM, QSv in *.
ceil; unfold zone3, zone3cases, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFX_IMG_LO, TFX_IMG_END, ASAN_CEIL, t_unwinding, kThreadObjSize, ASTACK, kPtrArrayResv, kMaxNumChunks,
kNodesBlockSize, kStoreBlockSize, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *. unfold T, Qb in *.
destruct Ha as [Ha|[Ha|Ha]].
- clear TNB TSB QNB QSB NBS SBS MNB MSB. split; img_lia.
- clear SBhi TSB QSB SBS MSB. split; img_lia.
- clear NBhi TNB QNB NBS MNB. split; img_lia.
Qed.
Definition RFACTS (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - ASTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFX_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ ((0xa1000 + D_1000) <= wlo /\ whi <= (0x17c088 + D_10c0)) \/ (0 <= wlo /\ whi <= TFX_IMG_LO)) /\
((hi <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= lo) /\ (hi <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= lo) /\
(hi <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= lo)) /\
((TFX_IMG_LO <= lo /\ hi <= TFX_IMG_END) \/ (T <= lo /\ hi <= T + kThreadObjSize) \/ (ly_C ly <= lo /\ hi <= ly_C ly + 256)).
Lemma zone_lit : forall lo hi wlo whi,
TFX_IMG_LO <= lo -> hi <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= lo -> hi <= TFX_IMG_END -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_irw : forall lo hi wlo whi,
(0xa1000 + D_1000) <= lo -> hi <= (0x17c088 + D_10c0) -> lo <= wlo -> whi <= hi -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof blocks_facts as (NBhi & SBhi & _).
destruct Hsp as (S1 & _). pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7).
unfold RFACTS. numconst. clear - Hz0 Hz1 Hz2 Hz3 NBhi SBhi S1 T7. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_T : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof high_facts as (F1 & F2 & _).
pose proof stack_ivs as (DT & _ & _). pose proof blocks_facts as (_ & _ & TNB & TSB & _).
unfold RFACTS. unfold zdisjoint in TNB, TSB. cbn [fst snd] in TNB, TSB. numconst. unfold T in *.
clear - Hz0 Hz1 Hz2 F1 F2 DT TNB TSB. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma zone_C : forall lo hi wlo whi,
ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTS lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof high_facts as (_ & _ & _ & _ & _ & _ & F7 & F8 & _).
pose proof stack_ivs as (_ & _ & DC & _). pose proof blocks_facts as (_ & _ & _ & _ & _ & _ & _ & _ & CNB & CSB).
unfold RFACTS. unfold zdisjoint in CNB, CSB. cbn [fst snd] in CNB, CSB. numconst.
clear - Hz0 Hz1 Hz2 F7 F8 DC CNB CSB. ceil. unfold ASAN_CEIL, zone3cases in *. numconst. img_lia.
Qed.
Lemma tail_ext_ok : forall (E : env) r,
(forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAIL ->
let b := base_val E (YQ0b.r_base r) in
(b + YQ0b.r_hi r <= sp0 - ASTACK \/ sp0 <= b + YQ0b.r_lo r) /\ 0 <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= 2 ^ 64 /\
(YQ0b.r_whi r <= YQ0b.r_wlo r \/ (TFX_IMG_END <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= 2 ^ 64) \/
((0xa1000 + D_1000) <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= (0x17c088 + D_10c0)) \/ (0 <= b + YQ0b.r_wlo r /\ b + YQ0b.r_whi r <= TFX_IMG_LO)) /\
((b + YQ0b.r_hi r <= (0x17c088 + D_10c0) \/ (0x5cc810 + D_10c0) <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_NB ly \/ ly_NB ly + kNodesBlockSize <= b + YQ0b.r_lo r) /\
(b + YQ0b.r_hi r <= ly_SB ly \/ ly_SB ly + kStoreBlockSize <= b + YQ0b.r_lo r)) /\
((TFX_IMG_LO <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= TFX_IMG_END) \/ (T <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= T + kThreadObjSize) \/
(ly_C ly <= b + YQ0b.r_lo r /\ b + YQ0b.r_hi r <= ly_C ly + 256)).
Proof.
intros E r HE Hin. pose proof high_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _). pose proof BSLv_range as HB.
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
let sk := img_ev constr:(SKEL_TAIL) in img_change SKEL_TAIL with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); img_lia)); rewrite ?E2, ?EaT, ?EaC, ?EaBSL; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - F1 F2 F3 F4 F5 F6 F7 F8 HB; numconst; unfold TFX_INST in *; unfold T in *; img_lia)).
all: lazymatch goal with |- (?b + ?hi' <= ?s \/ ?s' <= ?b' + ?lo') /\ ?B /\ ?C /\ (?whi' <= ?wlo' \/ ?D) /\ ?R =>
enough (RF : (b + hi' <= s \/ s' <= b' + lo') /\ B /\ C /\ (b + whi' <= b + wlo' \/ D) /\ R) by (img_try (clear - RF; destruct RF as (X1 & X2 & X3 & X4 & X5); refine (conj X1 (conj X2 (conj X3 (conj _ X5)))); clear - X4; unfold TFX_IMG_LO, TFX_IMG_END in *; img_lia)) end.
all: first [ img_apply zone_lit; clear; numconst; unfold TFX_TSD, TFX_TP, TFX_INST; img_lia
| img_apply zone_irw; clear - HB; numconst; unfold TFX_INST in *; img_lia
| img_apply zone_T; clear - F1 F2; numconst; unfold T in *; img_lia
| img_apply zone_C; clear - F7 F8; numconst; img_lia ].
Qed.
Lemma RFACTS_map : forall lo hi wlo whi, RFACTS lo hi wlo whi ->
(hi <= mb \/ mb + MSv <= lo) /\ (hi <= SMv \/ SMv + MSv / 8 <= lo).
Proof.
intros lo hi wlo whi (_ & _ & _ & _ & _ & HZ). pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _).
pose proof high_facts as (F1 & F2 & _ & _ & _ & _ & F7 & F8 & _). pose proof map_zone as MZ.
destruct Hmap_apart as (MT & MC & _). unfold zdisjoint in MT, MC. cbn [fst snd] in MT, MC.
clear - HZ M1 M2 SM1 SM2 F1 F2 F7 F8 MT MC MZ.
ceil; unfold zone3, zone3cases, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFX_IMG_LO, TFX_IMG_END, ASAN_CEIL, kThreadObjSize, kCtxMapSize in *. unfold T in *. img_lia.
Qed.
Definition at_ST (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < sHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINP (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall i, (i < length tr)%nat -> val_mem tfxsegs (mrestrict (w_H W) (ms_mem ms)) (sp0 - IFRAME + 16 + 8 * Z.of_nat i) 8 (nth i tr 0)).
Lemma memset_stretch : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
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
intros k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 HK.
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
Ltac clearM := try clear DPOST; try clear Hmap_apart; try clear Hmap.
Definition at_S (Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree sHAV E0 E' /\
st_ok tfxsegs E' ss (restrict (w_H Wx) ms) /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_N (Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree sHAV E0 E' /\
st_ok_ecall tfxsegs E' ss (restrict (w_H Wx) ms) /\ ss_resv ss = None /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_RETS (Wx : world tfxsegs) (v : word) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (w64 (0x323bc + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 10 = v /\
MIDST_top regs0 (Z.of_nat (length tr)) (w_H Wx) regs' mem' /\
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) mem' a) /\
P mem'.
Definition pstable (Xw : Z -> Prop) (P : (word -> option byte) -> Prop) : Prop :=
forall m m' : word -> option byte, (forall x : word, ~ Xw (bv_unsigned x) -> m' x = m x) -> P m -> P m'.
Definition stack_shaped (ss : sstate) : bool :=
(existsb (win_eqb (Some 2%nat, - ASTACK, - IFRAME)) (windows (ss_mem ss))
|| (existsb (win_eqb (Some 2%nat, - ASTACK, - 2336)) (windows (ss_mem ss)) && existsb (win_eqb (Some 2%nat, - 2336, - IFRAME)) (windows (ss_mem ss))))
&& existsb (win_eqb (Some 2%nat, -64, 0)) (windows (ss_mem ss)).
Lemma window_present : forall (Hh : word -> bool) (E' : env) rs (m : word -> option byte) b wlo whi a,
mem_ok tfxsegs E' (mrestrict Hh m) rs -> In (b, wlo, whi) (windows rs) ->
base_val E' b + wlo <= a < base_val E' b + whi -> TFX_IMG_END <= a < 2 ^ 64 -> apresent Hh m a.
Proof. clearM.
intros Hh E' rs m b wlo whi a (_ & Hrs & _) Hin Ha Hhi. unfold windows in Hin. apply in_map_iff in Hin as (r & Hr & Hinr).
injection Hr as E1 E2 E3. (subst b wlo whi; cbv beta).
pose proof (proj1 (Forall_forall _ _) Hrs _ Hinr) as (_ & _ & Hw & _).
img_apply writable_high_apresent; [img_try (img_exact Hhi)|].
replace a with (base_val E' (YQ0b.r_base r) + (a - base_val E' (YQ0b.r_base r))) by img_lia. img_apply Hw. img_lia.
Qed.
Lemma stack_present_of : forall (Hh : word -> bool) (E' : env) ss (m m1 : word -> option byte) (Xw : Z -> Prop),
env_agree sHAV E0 E' -> stack_shaped ss = true -> (forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ Xw a) ->
mem_ok tfxsegs E' (mrestrict Hh m) (ss_mem ss) ->
(forall x : word, ~ Xw (bv_unsigned x) -> m x = m1 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent Hh m1 a) ->
forall a, sp0 - ASTACK <= a < sp0 -> apresent Hh m a.
Proof. clearM.
intros Hh E' ss m m1 Xw [HE _] Hsh MID HM FR PRS a Ha.
pose proof (lo_top ly LY) as (_ & T2 & _ & T4 & _ & _ & T7). destruct Hsp as (S1 & _ & S3 & _). pose proof (u64_range (getr regs0 2)) as U2.
assert (B2 : base_val E' (Some 2%nat) = sp0) by (img_try (cbn [base_val]; rewrite (HE 2%nat ltac:(unfold sHAV; img_lia)), E2; img_refl)).
unfold stack_shaped in Hsh. apply andb_prop in Hsh as [H1 H2].
apply existsb_exists in H2 as (t2 & Hin2 & Heq2). apply win_eqb_eq in Heq2. (subst t2; cbv beta).
destruct (Z_lt_le_dec a (sp0 - IFRAME)) as [Hlo|Hge].
- apply Bool.orb_prop in H1 as [H1|H1].
+ apply existsb_exists in H1 as (t1 & Hin1 & Heq1). apply win_eqb_eq in Heq1. (subst t1; cbv beta).
img_apply (window_present Hh E' (ss_mem ss) m _ _ _ a HM Hin1); [img_try (rewrite B2; img_lia) | img_try (clear - Ha S1 T7 U2; numconst; unfold sp0 in *; img_lia)].
+ apply andb_prop in H1 as [H1a H1b].
apply existsb_exists in H1a as (t1 & Hin1 & Heq1). apply win_eqb_eq in Heq1. (subst t1; cbv beta).
apply existsb_exists in H1b as (t3 & Hin3 & Heq3). apply win_eqb_eq in Heq3. (subst t3; cbv beta).
destruct (Z_lt_le_dec a (sp0 - 2336)) as [Hlo2|Hge2].
* img_apply (window_present Hh E' (ss_mem ss) m _ _ _ a HM Hin1); [img_try (rewrite B2; img_lia) | img_try (clear - Ha S1 T7 U2; numconst; unfold sp0 in *; img_lia)].
* img_apply (window_present Hh E' (ss_mem ss) m _ _ _ a HM Hin3); [img_try (rewrite B2; unfold IFRAME in *; img_lia) | img_try (clear - Ha S1 T7 U2; numconst; unfold sp0 in *; img_lia)].
- destruct (Z_lt_le_dec a (sp0 - 64)) as [Hmid|Htop].
+ img_apply (apresent_same Hh m1); [img_try (img_apply FR; rewrite unsigned_lit_small by (clear - Ha S1 T7 U2; numconst; unfold sp0 in *; img_lia); img_apply MID; img_lia) | img_try (img_apply PRS; img_lia)].
+ img_apply (window_present Hh E' (ss_mem ss) m _ _ _ a HM Hin2); [img_try (rewrite B2; img_lia) | img_try (clear - Ha S1 T7 U2; numconst; unfold sp0 in *; img_lia)].
Qed.
Lemma mid_not_WIN1P : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1P a.
Proof. clearM.
intros a Ha Hw. pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F15).
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof BSLv_range as HB. destruct Hsp as (S1 & _ & S3 & _).
destruct (F15 a) as (N1 & _ & _ & _); [img_try (clear - Ha S1 S3; unfold ASTACK, IFRAME in *; img_lia)|].
clear - Ha Hw N1 T7 S1 S3 HB.
unfold WIN1P, WINT, WINI, kHighMemBeg, kThreadObjSize, ASTACK, IFRAME, t_unwinding, TFX_INST, o_sec_reserved, o_sec_sorted, o_sec_stats, o_sec_mutex in *.
unfold T in *. img_lia.
Qed.
Lemma mid_not_WIN1 : forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ WIN1 a.
Proof.
intros a Ha [Hw|Hw]; [img_try (img_exact (mid_not_WIN1P a Ha Hw))|].
pose proof high_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F15).
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). pose proof (lo_stk_ceil ly LY) as SC.
pose proof map_facts as (M1 & M2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SM1 & SM2 & _). pose proof Hidx as HI. destruct Hsp as (S1 & _ & S3 & _).
destruct (F15 a) as (_ & _ & N3 & _); [img_try (clear - Ha S1 S3; unfold ASTACK, IFRAME in *; img_lia)|].
clear - Ha Hw N3 T7 S1 S3 SC M1 M2 SM1 SM2 HI.
ceil; unfold zone3, WINM, QSv, kHighMemBeg, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, TFX_IMG_END, ASAN_CEIL, kPtrArrayResv, kMaxNumChunks, ASTACK, IFRAME in *. unfold Qb in *. img_lia.
Qed.
Definition wins_ok (K : list (option nat * Z * Z)) (rs : smem) : bool :=
forallb (fun t => existsb (win_sub t) K || (snd t <=? snd (fst t))) (windows rs).
Lemma at_S_run_gen : forall (K : list (option nat * Z * Z)) (Xw : Z -> Prop),
(forall (E : env) rs a, (forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok K rs = true -> in_wrange E rs a -> Xw a) ->
(forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ Xw a) ->
forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, Xw a -> X a) -> wins_ok K (ss_mem ss) = true -> pstable Xw P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. clearM.
intros K Xw HK MID Wx tbl tblok stop md X P ss ss' st W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfxsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfxsegs E' ss' (restrict (w_H Wx) ms')) by (img_try (destruct st; [img_try (img_exact HS') | img_try (destruct Hst) | img_try (img_exact HS')])). clear HS'.
assert (FR : forall x : word, ~ Xw (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x).
{ intros x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (HK E' (ss_mem ss) _ (proj1 HE) Hwin Hw). }
img_apply SRr_ret. split; [img_refl|]. exists ms', mat', E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS'')|].
split; [|img_try (split)].
- intros x Hx. rewrite (FR x) by (img_try (intros Hw; img_exact (Hx (HX _ Hw)))). img_exact (MEQ x Hx).
- pose proof (st_ok_mem_ok tfxsegs E' ss' _ HS'') as HM. cbn [ms_mem restrict] in HM.
img_exact (stack_present_of (w_H Wx) E' ss' (ms_mem ms') (ms_mem ms) Xw HE Hsc MID HM FR PRS).
- img_exact (HP _ _ FR HPm).
Qed.
Lemma at_S_run_ecall_gen : forall (K : list (option nat * Z * Z)) (Xw : Z -> Prop),
(forall (E : env) rs a, (forall k, (k < sHAV)%nat -> ew E k = ew E0 k) -> wins_ok K rs = true -> in_wrange E rs a -> Xw a) ->
(forall a, sp0 - IFRAME <= a < sp0 - 64 -> ~ Xw a) ->
forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, Xw a -> X a) -> wins_ok K (ss_mem ss) = true -> pstable Xw P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. clearM.
intros K Xw HK MID Wx tbl tblok stop md X P ss ss' W' c' HR Hrun Hrv HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfxsegs tbl tblok Hwx Wx FUEL stop E' ss ss' RS_ecall ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
img_apply SRr_ret. split; [img_refl|]. exists ms', mat', E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS')|]. split; [img_try (img_exact Hrv)|].
assert (FR : forall x : word, ~ Xw (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x).
{ intros x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (HK E' (ss_mem ss) _ (proj1 HE) Hwin Hw). }
split; [|img_try (split)].
- intros x Hx. rewrite (FR x) by (img_try (intros Hw; img_exact (Hx (HX _ Hw)))). img_exact (MEQ x Hx).
- destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss' ms' HS' Hrv) as (regs & mem & Hms & _ & HM & _).
assert (Em : ms_mem ms' = mem) by (img_try (rewrite Hms; img_refl)). rewrite Em in FR |- *. rewrite <- Em in HM |- *. rewrite Em in HM |- *.
img_exact (stack_present_of (w_H Wx) E' ss' mem (ms_mem ms) Xw HE Hsc MID HM FR PRS).
- img_exact (HP _ _ FR HPm).
Qed.
Lemma at_S_runP : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1P a -> X a) -> wins_ok WSKEL1P (ss_mem ss) = true -> pstable WIN1P P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. clearM. img_exact (at_S_run_gen WSKEL1P WIN1P windows_WIN1P mid_not_WIN1P). Qed.
Lemma at_S_runM : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WIN1 a -> X a) -> wins_ok WSKEL1 (ss_mem ss) = true -> pstable WIN1 P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_S Wx md X P ss').
Proof. img_exact (at_S_run_gen WSKEL1 WIN1 windows_WIN1 mid_not_WIN1). Qed.
Lemma at_S_run_ecallP : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1P a -> X a) -> wins_ok WSKEL1P (ss_mem ss) = true -> pstable WIN1P P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. clearM. img_exact (at_S_run_ecall_gen WSKEL1P WIN1P windows_WIN1P mid_not_WIN1P). Qed.
Lemma at_S_run_ecallM : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_S Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WIN1 a -> X a) -> wins_ok WSKEL1 (ss_mem ss) = true -> pstable WIN1 P -> stack_shaped ss' = true ->
SRr tfxsegs W' c' (at_N Wx md X P ss').
Proof. img_exact (at_S_run_ecall_gen WSKEL1 WIN1 windows_WIN1 mid_not_WIN1). Qed.
Lemma at_S_pin : forall (Wx : world tfxsegs) md X P ss W' c' (r : bv 5) (e : sv),
at_S Wx md X P ss W' c' -> r <> 0%bv ->
sv_atoms_lt sHAV e = true -> sv_atoms_lt sHAV (sr_get (ss_regs ss) r) = true ->
U E0 e = U E0 (sr_get (ss_regs ss) r) ->
at_S Wx md X P (pin ss r e) W' c'.
Proof. clearM.
intros Wx md X P ss W' c' r e HR Hr Hae Has HU.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold pin. img_apply st_ok_pin_regU; [img_try (img_exact HS) | img_try (img_exact Hr) |].
rewrite (U_agree sHAV E0 E' e HE Hae), (U_agree sHAV E0 E' _ HE Has). img_exact HU.
Qed.
Lemma at_S_arm : forall (Wx : world tfxsegs) md X P ss W' c' (cnd : branch_cond) (tk : bool) (a b : sv),
at_S Wx md X P ss W' c' ->
sv_atoms_lt sHAV a = true -> sv_atoms_lt sHAV b = true ->
branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk ->
at_S Wx md X P (arm cnd tk a b ss) W' c'.
Proof. clearM.
intros Wx md X P ss W' c' cnd tk a b HR Ha Hb Ht.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold arm. rewrite <- (sv_denot_agree sHAV E0 E' a HE Ha), <- (sv_denot_agree sHAV E0 E' b HE Hb) in Ht.
destruct tk; [img_try (img_apply st_ok_add_cond; [img_exact HS | img_exact Ht]) | img_try (img_apply st_ok_add_cond_neg; [img_exact HS | img_exact Ht])].
Qed.
Lemma at_S_forget : forall (Wx : world tfxsegs) md X P ss W' c' (k : nat) (clob : list (bv 5)),
at_S Wx md X P ss W' c' -> (sHAV <= k)%nat -> ss_resv ss = None ->
ss_atoms_lt k ss = true -> regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
at_S Wx md X P (forget ss k clob) W' c'.
Proof. clearM.
intros Wx md X P ss W' c' k clob HR Hk Hrv Hat Hwf Hnc Hma Hnd Hnz.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, (havoc E' k (map (getr (ms_regs ms)) clob)). split; [img_refl|].
split; [img_try (img_exact (env_agree_havoc_ge sHAV k E0 E' _ Hk HE))|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
pose proof (st_ok_forget k E' ss (w_H Wx) ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz) as X'. unfold forget.
rewrite <- (st_ok_restrict_mkst tfxsegs (w_H Wx) E' ss ms HS Hrv) in X'. img_exact X'.
Qed.
Lemma at_S_noconds : forall (Wx : world tfxsegs) md X P ss W' c', at_S Wx md X P ss W' c' -> at_S Wx md X P (noconds ss) W' c'.
Proof. clearM.
intros Wx md X P ss W' c' HR. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold noconds. img_apply st_ok_prune. img_exact HS.
Qed.
Lemma at_S_weaken : forall (Wx : world tfxsegs) md X X' (P P' : (word -> option byte) -> Prop) ss W' c',
at_S Wx md X P ss W' c' -> (forall a, X a -> X' a) -> (forall m, P m -> P' m) -> at_S Wx md X' P' ss W' c'.
Proof. clearM.
intros Wx md X X' P P' ss W' c' HR HX HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS)|].
split; [img_try (intros x Hx; img_apply MEQ; intros H; img_exact (Hx (HX _ H)))|]. split; [img_try (img_exact PRS) | img_try (img_exact (HP _ HPm))].
Qed.
Lemma at_S_facts : forall (Wx : world tfxsegs) md X (P Q : (word -> option byte) -> Prop) ss W' c',
at_S Wx md X P ss W' c' ->
(forall (E' : env) ms, env_agree sHAV E0 E' -> st_ok tfxsegs E' ss (restrict (w_H Wx) ms) -> Q (ms_mem ms)) ->
at_S Wx md X (fun m => P m /\ Q m) ss W' c'.
Proof. clearM.
intros Wx md X P Q ss W' c' HR HQ. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS)|]. split; [img_try (img_exact HPm) | img_try (img_exact (HQ E' ms HE HS))].
Qed.
Lemma at_S_strengthen : forall (Wx : world tfxsegs) md X (P P' : (word -> option byte) -> Prop) ss W' c',
at_S Wx md X P ss W' c' ->
(forall m, (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) -> (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> P' m) ->
at_S Wx md X P' ss W' c'.
Proof. clearM.
intros Wx md X P P' ss W' c' HR HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS) | img_try (img_exact (HP _ MEQ PRS HPm))].
Qed.
Lemma at_S_eq : forall (Wx : world tfxsegs) md X P ss ss' W' c', at_S Wx md X P ss W' c' -> ss = ss' -> at_S Wx md X P ss' W' c'.
Proof. clearM. intros Wx md X P ss ss' W' c' H <-. img_exact H. Qed.
Lemma at_S_open : forall (Wx : world tfxsegs) md X P ss W' c',
at_S Wx md X P ss W' c' ->
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\ env_agree sHAV E0 E' /\ st_ok tfxsegs E' ss (restrict (w_H Wx) ms) /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\ (forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\ P (ms_mem ms).
Proof. clearM. intros Wx md X P ss W' c' H. img_exact H. Qed.
Definition CSAVEDS : list (bv 5) := [3; 23; 24; 25; 26; 27]%bv.
Lemma sv_denot_SOff0 : forall (E' : env) k, sv_denot E' (SOff k 0) = ew E' k.
Proof. clear. intros E' k. cbn [sv_denot]. rewrite Z.add_0_r. img_apply Z_to_bv_bv_unsigned. Qed.
Lemma at_S_ret : forall (Wx : world tfxsegs) md X P ss W' c' (e : sv),
at_S Wx md X P ss W' c' -> ss_resv ss = None -> ss_pc ss = (0x323bc + D_150) ->
MIDCHK ss = true -> sr_get (ss_regs ss) 10%bv = e -> sv_atoms_lt sHAV e = true ->
sr_get (ss_regs ss) 4%bv = SLit TFX_TP ->
Forall (fun r : bv 5 => sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVEDS ->
SRr tfxsegs W' c' (at_RETS Wx (sv_denot E0 e) md X P).
Proof. clearM.
intros Wx md X P ss W' c' e HR Hrv Hpc HM H10 He H4 Hcs. pose proof Hra as Hra'. clear Hra'.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
pose proof (midchk_ok sHAV XW regs0 E' (w_H Wx) ss ms ltac:(img_try (unfold sHAV; img_lia)) HS HE HM) as (HMl & HMr & HMf).
img_change (ew (Ereg regs0 XW) 36) with (w64 (Z.of_nat (length tr))) in HMl. pose proof tr_length as TL. unfold w64 in HMl. rewrite unsigned_lit_small in HMl by img_lia.
assert (RG : forall r : bv 5, sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> (Z.to_nat (bv_unsigned r) < sHAV)%nat -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr Hlt. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms r HS), Hr, sv_denot_SOff0, (proj1 HE _ Hlt). img_apply (Er _ r). rewrite Z2Nat.id; [img_refl | img_try (pose proof (bv_unsigned_in_range 5 r); img_lia)]. }
img_apply SRr_ret. split; [img_refl|]. exists (ms_regs ms), (ms_mem ms), mat.
split. { f_equal. etransitivity; [img_try (img_exact (st_ok_restrict_mkst tfxsegs (w_H Wx) E' ss ms HS Hrv))|]. rewrite Hpc. img_refl. }
split. { rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 10 HS), H10. img_exact (sv_denot_agree sHAV E0 E' e HE He). }
split.
{ split; [|img_try (split; [img_exact HMl | split; [img_exact HMr | img_exact HMf]])].
intros r Hr. destruct (bv_eqb r 4%bv) eqn:E4.
- apply bv_eqb_eq in E4. (subst r; cbv beta). rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 4 HS), H4. cbn [sv_denot]. symmetry. img_exact Htp.
- assert (N4 : r <> 4%bv) by (img_try (intros ->; rewrite bv_eqb_refl in E4; discriminate E4)).
assert (IN : In r CSAVEDS).
{ unfold CSAVEDS. cbn [In] in Hr. cbn [In].
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [img_try (first [exfalso; img_apply N4; img_refl | tauto]) |] | False => destruct Hr end. }
img_apply RG; [img_try (img_exact (proj1 (Forall_forall _ _) Hcs r IN))|].
pose proof (bv_unsigned_in_range 5 r) as B. img_change (bv_modulus 5) with 32 in B. unfold sHAV. img_lia. }
split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS) | img_try (img_exact HPm)].
Qed.
Lemma kept_of_frame2 : forall (Hh : word -> bool) (E : env) (m m1 : word -> option byte) (R : Z -> Prop) r,
(forall x : word, ~ R (bv_unsigned x) -> m1 x = m x) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
region_kept tfxsegs E (mrestrict Hh m) (mrestrict Hh m1) r.
Proof. clearM.
intros Hh E m m1 R r Hfr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. destruct (Hwin a Ha) as [Hno Hr]. img_apply (writable_at_eq tfxsegs (mrestrict Hh m)); [|img_try (img_exact Hw)].
unfold mrestrict. rewrite (Hfr (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_exact Hno)). img_refl.
Qed.
Lemma at_N_cont : forall (Wx Wy : world tfxsegs) (md' : Model) X (P' : (word -> option byte) -> Prop) ss (e : sv) (v : word) (R : Z -> Prop)
(mem' : word -> option byte) ms (E' : env),
env_agree sHAV E0 E' ->
st_ok_ecall tfxsegs E' ss (restrict (w_H Wx) ms) -> ss_resv ss = None ->
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall a, sp0 - ASTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) ->
hsub (w_H Wy) (w_H Wx) ->
sv_denot E' e = v -> no_cdata (ss_mem ss) = true ->
(forall x : word, ~ R (bv_unsigned x) -> mem' x = ms_mem ms x) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, sp0 - ASTACK <= a < sp0 -> ~ R a) ->
P' mem' ->
at_S Wy md' (fun a => X a \/ R a) P' (resume ss e (ss_mem ss) (ss_facts ss)) Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfxsegs)) md').
Proof. clearM.
intros Wx Wy md' X P' ss e v R mem' ms E' HE HS Hrv MEQ PRS Hsub He Hnc Hfr Hext Hwin HsR HP'.
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (Er' : ms_regs ms = regs) by (img_try (rewrite Hms; img_refl)). assert (Em' : ms_mem ms = mem) by (img_try (rewrite Hms; img_refl)).
rewrite Er'. rewrite Em' in MEQ, PRS, Hfr. clear Hms Er' Em'.
pose proof (lo_top ly LY) as (_ & _ & _ & _ & _ & _ & T7). destruct Hsp as (S1 & _). pose proof (u64_range (getr regs0 2)) as SPhi.
split; [img_refl|]. exists (mkst (regupd regs 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfxsegs)), (m_vm_materialized md'), E'.
split; [img_try (rewrite with_vm_backing_id; img_refl)|]. split; [img_try (img_exact HE)|]. split; [|img_try (split; [|split])].
- rewrite restrict_mkst_fx. img_apply (st_ok_resume_sv tfxsegs E' ss regs (mrestrict (w_H Wy) mem') e v Hregs); [| img_try (img_exact HG) | img_try (img_exact He)].
img_apply (mem_ok_kept tfxsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem') (ss_mem ss));
[img_try (img_exact (mem_ok_mrestrict_hsub tfxsegs (w_H Wx) (w_H Wy) E' mem (ss_mem ss) (w_Hoff Wx) Hsub Hmem)) | img_try (img_exact Hnc) |].
img_apply Forall_forall. intros r Hr. img_exact (kept_of_frame2 (w_H Wy) E' mem mem' R r Hfr (fun a Ha => Hext r a Hr Ha) (fun a Ha => Hwin r a Hr Ha)).
- intros x Hx. cbn [ms_mem mkst]. rewrite (Hfr x) by (img_try (intros HRx; img_apply Hx; right; img_exact HRx)). img_apply MEQ. intros HXx; img_apply Hx; left; img_exact HXx.
- intros a Ha. cbn [ms_mem mkst]. destruct (PRS a Ha) as [Hh [b Hb]]. split.
+ destruct (w_H Wy (Z_to_bv 64 a)) eqn:Ey; [|img_refl]. rewrite (Hsub _ Ey) in Hh. discriminate Hh.
+ exists b. rewrite (Hfr (Z_to_bv 64 a)); [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by (img_try (clear - Ha S1 T7 SPhi; numconst; unfold sp0 in *; img_lia)). img_exact (HsR a Ha).
- cbn [ms_mem mkst]. img_exact HP'.
Qed.
Variables (B : asyms) (S : astate).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hidx_def : idx = Z.of_nat (length (st_sec_arr S)).
Hypothesis Hres_def : res = st_sec_reserved S.
Hypothesis Hj0 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2784) 8 j0.
Hypothesis Hj1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2800) 8 j1.
Hypothesis Hj2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2808) 8 j2.
Hypothesis Hj3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2816) 8 j3.
Hypothesis Hj4 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2872) 8 j4.
Hypothesis Hj5 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2880) 8 j5.
Hypothesis Hj9 : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2904) 8 j9.
Hypothesis Hj6 : val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e18 + D_10c0) 8 j6.
Hypothesis Hj7 : val_mem tfxsegs (mrestrict (w_H W) mem0) (0xa6e20 + D_10c0) 8 j7.
Hypothesis Hj8 : val_mem tfxsegs (mrestrict (w_H W) mem0) BSLv 8 j8.
Hypothesis Hi1 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats) 8 i1.
Hypothesis Hi2 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 16) 8 i2.
Hypothesis Hi3 : val_mem tfxsegs (mrestrict (w_H W) mem0) (TFX_INST + o_sec_stats + 24) 8 i3.
Hypothesis HQT : qtight S.
End g.
End f.
