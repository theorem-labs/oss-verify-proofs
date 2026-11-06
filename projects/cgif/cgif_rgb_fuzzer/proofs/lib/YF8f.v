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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF8r YF8s YF8t.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF64.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YE01.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF09 YF0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK0u.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF4q YF8g YF3w YF8i.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section e. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (img_try (unfold M64; img_lia))
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := img_ev (Z.land a b) in img_change (Z.land a b) with c
end.
Ltac zlia := first [ img_lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFX_IMG_LO, TFX_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; img_lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFX_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFX_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
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
Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Section f. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Let sp0 : Z := bv_unsigned (getr regs0 2).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Definition Pr : Z := T + t_cache + 80 * c.
Definition RGv : Z := SB + kRegionInfoOff + 128 * c.
Definition RBv : Z := SB + c * 2 ^ 32.
Definition FAv : Z := RBv + kFreeArrayOffset.
Definition SHBv : Z := 0x7fff8000.
Definition SRCv : Z := FAv + 4 * (nf - n).
Definition DSTv : Z := Pr + 16.
Definition XWR : list word :=
[ w64 T; w64 (ly_C ly); w64 SB; w64 (ly_top ly); w64 c; w64 Pr; w64 maxc; w64 n; w64 csz; w64 RGv; w64 RBv; w64 FAv;
w64 nf; w64 mf; w64 au; w64 mu; w64 SHBv; w64 j64; w64 jna; w64 jnf; w64 jsm; w64 jm1; w64 jm2 ].
Definition E0 : env := Ereg regs0 XWR.
Lemma EaT : ew E0 32 = w64 T. Proof. img_refl. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. img_refl. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. img_refl. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. img_refl. Qed.
Lemma EaCL : ew E0 36 = w64 c. Proof. img_refl. Qed.
Lemma EaP : ew E0 37 = w64 Pr. Proof. img_refl. Qed.
Lemma EaMAX : ew E0 38 = w64 maxc. Proof. img_refl. Qed.
Lemma EaN : ew E0 39 = w64 n. Proof. img_refl. Qed.
Lemma EaCSZ : ew E0 40 = w64 csz. Proof. img_refl. Qed.
Lemma EaRG : ew E0 41 = w64 RGv. Proof. img_refl. Qed.
Lemma EaRB : ew E0 42 = w64 RBv. Proof. img_refl. Qed.
Lemma EaFA : ew E0 43 = w64 FAv. Proof. img_refl. Qed.
Lemma EaNF : ew E0 44 = w64 nf. Proof. img_refl. Qed.
Lemma EaMF : ew E0 45 = w64 mf. Proof. img_refl. Qed.
Lemma EaAU : ew E0 46 = w64 au. Proof. img_refl. Qed.
Lemma EaMU : ew E0 47 = w64 mu. Proof. img_refl. Qed.
Lemma EaSHB : ew E0 48 = w64 SHBv. Proof. img_refl. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XWR k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. img_exact (Er 8 8%bv eq_refl). Qed.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HcR : 1 <= c <= 31.
Hypothesis Hmax : maxc = max_cached c.
Hypothesis Hn : n = maxc / 2.
Hypothesis Hcsz : csz = class_size c.
Hypothesis Hnf : 0 <= nf /\ 4 * nf <= mf.
Hypothesis Hmf : 0 <= mf <= kFreeArrayMax /\ mf mod kFreeArrayMapSize = 0.
Hypothesis Hmu : 0 <= au <= mu /\ mu <= kFreeArrayOffset /\ mu mod kUserMapSize = 0 /\ au mod 16 = 0.
Hypotheses (Hj64 : 0 <= j64 < 2 ^ 32) (Hjna : 0 <= jna < 2 ^ 64) (Hjnf : 0 <= jnf < 2 ^ 64)
(Hjsm : 0 <= jsm < 2 ^ 64) (Hjm1 : 0 <= jm1 < 2 ^ 64) (Hjm2 : 0 <= jm2 < 2 ^ 64).
Hypothesis Hsp : ly_stk_lo ly + RSTACK <= sp0 /\ sp0 <= ly_stk_hi ly /\ sp0 mod 16 = 0.
Hypothesis Hra : YK0s.ret_ok (getr regs0 1).
Hypothesis Hra4096 : 4096 <= bv_unsigned (getr regs0 1).
Hypothesis Htp : getr regs0 4 = w64 TFX_TP.
Hypothesis Ha0 : getr regs0 10 = w64 (T + t_cache).
Hypothesis Ha1 : getr regs0 11 = w64 Pr.
Hypothesis Ha2 : getr regs0 12 = w64 A_ALLOCATOR.
Hypothesis Ha3 : getr regs0 13 = w64 c.
Lemma class_facts : 2 <= maxc <= 16 /\ maxc mod 2 = 0 /\ 1 <= n <= 8 /\ 16 <= csz <= kMaxSize /\ csz mod 16 = 0.
Proof.
pose proof (class_ok c ltac:(img_lia)) as (K1 & K2 & K3 & K4 & K5 & K6).
set (q := Z.max 1 (Z.min 8 (1024 / class_size c))).
assert (Q : 1 <= q <= 8) by (img_try ((subst q; cbv beta); img_lia)).
assert (M : maxc = q * 2) by (img_try (rewrite Hmax; unfold max_cached; (subst q; cbv beta); img_lia)).
assert (N : n = q) by (img_try (rewrite Hn, M, Z_div_mult by img_lia; img_refl)).
apply Z.mod_divide in K2 as [r Hr]; [|img_lia].
split; [img_lia|]. split; [img_try (rewrite M; img_apply Z_mod_mult)|]. split; [img_lia|]. split; [img_try (rewrite Hcsz; img_lia)|].
rewrite Hcsz, Hr. replace (r * 32) with ((r * 2) * 16) by img_lia. img_apply Z_mod_mult.
Qed.
Lemma high_factsR :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= ly_space ly /\
ly_space ly + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ ly_space ly mod 65536 = 0 /\
(forall a, ly_stk_lo ly <= a < ly_stk_hi ly -> ~ (T <= a < T + kThreadObjSize) /\ ~ (ly_prim ly <= a < ly_prim ly + kPrimResvSize)).
Proof.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD. pose proof (lo_space_in ly LY) as HSP. pose proof (lo_space_al ly LY) as HAL.
pose proof (Forall_nth' _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth' _ _ 6 _ HA eq_refl) as IC. cbn beta in IT, IC. cbn [fst snd] in IT, IC.
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(img_try (clear_all; unfold kThreadObjSize; img_lia)) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(img_try (clear_all; img_lia)) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
clear HA HD. split; [img_try (img_exact ZT)|]. clear ZT.
unfold in_high, in_app, zdisjoint, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. unfold T in *.
pose proof ASAN_CEIL_range as [CR _].
split; [img_try (clear - IT CR; img_lia)|]. do 4 (split; [img_try (clear TS PS ZC; img_lia)|]).
split; [img_try (img_exact ZC)|]. split; [img_try (clear - IC CR; img_lia)|]. split; [img_try (img_exact HAL)|].
intros a Ha; split; intros Hx; [img_try (clear PS) | img_try (clear TS)]; clear ZC; img_lia.
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. img_exact (zone3_off_img _ _ a (proj1 high_factsR) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof high_factsR as (_ & _ & _ & _ & _ & _ & F7 & _). img_exact (zone3_off_img _ _ a F7 Ha). Qed.
Ltac off_by tac :=
first [ img_apply off_img_high; tac
| img_apply off_T; unfold kThreadObjSize; tac
| img_apply off_C; tac
| unfold off_img; unfold TFX_IMG_LO; unfold TFX_IMG_END; tac ].
Lemma derived_rangesR :
4096 <= Pr   /\ Pr + 80 <= T + 2768 /\ Pr mod 16 = 0 /\ T + t_cache + 80 <= Pr /\
kHighMemBeg <= RGv /\ RGv + 128 <= ASAN_CEIL /\ RGv mod 128 = 0 /\ ly_prim ly <= RGv /\ ly_space ly + kSpaceSize <= RGv /\
kHighMemBeg <= RBv /\ RBv + 2 ^ 32 <= ly_space ly + kSpaceSize /\ RBv mod 65536 = 0 /\ ly_space ly <= RBv /\
FAv = RBv + kFreeArrayOffset /\ FAv mod 4096 = 0 /\
ly_space ly + kSpaceSize = SB + kRegionInfoOff /\ RGv + 128 <= ly_space ly + kSpaceSize + 4096 /\ ly_space ly + kSpaceSize + 4096 <= ASAN_CEIL /\
SRCv = FAv + 4 * (nf - n) /\ DSTv = Pr + 16 /\ (n <= nf -> FAv <= SRCv /\ SRCv + 4 * n <= FAv + mf) /\
(140735332483072 <= ASAN_CEIL <= 140737479966720).
Proof.
pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & _). pose proof class_facts as (C1 & C2 & C3 & _).
pose proof (lo_T_al ly LY) as TAL. unfold page_aligned in TAL. pose proof Hnf as [N1 N2].
apply Z.mod_divide in F9 as [qs Hqs]; [|img_lia]. apply Z.mod_divide in TAL as [qt Hqt]; [|img_lia].
unfold SRCv, DSTv. unfold FAv. unfold Pr, RGv, RBv. unfold T, SB in *.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in *.
assert (M1 : (ly_T ly + 208 + 80 * c) mod 16 = 0) by (img_try (rewrite Hqt; img_apply Z.mod_divide; [img_lia|]; exists (qt * 256 + 13 + 5 * c); img_lia)).
assert (M2 : (ly_space ly + 2 ^ 37 + 128 * c) mod 128 = 0) by (img_try (rewrite Hqs; img_apply Z.mod_divide; [img_lia|]; exists (qs * 512 + 2 ^ 30 + c); img_lia)).
assert (M3 : (ly_space ly + c * 2 ^ 32) mod 65536 = 0) by (img_try (rewrite Hqs; img_apply Z.mod_divide; [img_lia|]; exists (qs + c * 65536); img_lia)).
assert (M4 : (ly_space ly + c * 2 ^ 32 + 3758096384) mod 4096 = 0) by (img_try (rewrite Hqs; img_apply Z.mod_divide; [img_lia|]; exists (qs * 16 + c * 2 ^ 20 + 917504); img_lia)).
repeat split; try assumption; img_lia.
Qed.
Definition WINR0 (a : Z) : Prop :=
(sp0 - RSTACK <= a < sp0) \/ (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/
(T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888).
Definition WINR (a : Z) : Prop := WINR0 a \/ (DSTv <= a < DSTv + 4 * n).
Lemma WINR0_WINR : forall a, WINR0 a -> WINR a.
Proof. intros a H. left. img_exact H. Qed.
Definition WSKELR : list (option nat * Z * Z) :=
[(Some 2%nat, - RSTACK, 0); (Some rP, 0, 16); (Some rRG, 0, 128); (Some rT, 2768, 2800); (Some rT, 2872, 2888)].
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
Lemma WSKELR_WINR0 : forall (E : env) a t,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In t WSKELR ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINR0 a.
Proof.
intros E a t HE Hin Hr. unfold WSKELR in Hin. cbn [In] in Hin. unfold WINR0.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; unfold rP, rRG, rT in Hr; rewrite HE in Hr by (img_try (unfold aHAV; img_lia));
rewrite ?E2, ?EaT, ?EaP, ?EaRG in Hr; unfold w64 in Hr;
pose proof derived_rangesR as DR; pose proof high_factsR as HF; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize in DR, HF;
rewrite ?unsigned_lit_small in Hr by img_lia; unfold sp0 in *; img_lia.
Qed.
Lemma windows_WINR0 : forall (E : env) rs a,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINR0 a.
Proof.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELR_WINR0 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma frame_WINR0 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINR0 (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINR0 E rs _ HE Hb Hw). Qed.
Ltac frame_accR HE :=
match goal with
| MEQ : (forall x : word, ~ WINR0 (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ WINR0 (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_WINR0 E rs m1 m2 HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Definition at_R (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a).
Definition at_RC (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md0) mat md0) /\
(forall k, (k < aHAV)%nat -> ew E' k = ew E0 k) /\
st_ok tfxsegs E' ss (restrict (w_H W) ms) /\
(forall x : word, ~ WINR (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) (ms_mem ms) a) /\
(forall k, 0 <= k < 4 * n -> ms_mem ms (w64 (DSTv + k)) = mem0 (w64 (SRCv + k))) /\
(forall a, DSTv <= a < DSTv + 4 * n -> apresent (w_H W) (ms_mem ms) a).
Definition at_RET2 (W' : world tfxsegs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 1 /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ WINR (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem' a) /\
(forall a, (Pr <= a < Pr + 16) \/ (DSTv <= a < DSTv + 4 * n) \/ (RGv <= a < RGv + 128) \/
(T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H W) mem' a) /\
(forall k, 0 <= k < 4 * n -> mem' (w64 (DSTv + k)) = mem0 (w64 (SRCv + k))) /\
let m := mrestrict (w_H W) mem' in
val_mem tfxsegs m Pr 4 n /\ val_mem tfxsegs m (Pr + 4) 4 maxc /\ val_mem tfxsegs m (Pr + 8) 8 csz /\
val_mem tfxsegs m RGv 8 0 /\ val_mem tfxsegs m (RGv + 8) 8 0 /\ val_mem tfxsegs m (RGv + 16) 8 (nf - n) /\
val_mem tfxsegs m (RGv + 24) 8 mf /\ val_mem tfxsegs m (RGv + 32) 8 au /\ val_mem tfxsegs m (RGv + 40) 8 0 /\
val_mem tfxsegs m (RGv + 48) 8 mu /\ val_mem tfxsegs m (RGv + 56) 8 0 /\ val_mem tfxsegs m (RGv + 68) 1 0.
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
Definition SKEL_TAILR {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0R).
Definition RFACTSR (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - RSTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFX_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFX_IMG_LO)) /\
(hi <= DSTv \/ DSTv + 32 <= lo).
Lemma stack_ivsR :
(T + kThreadObjSize <= sp0 - RSTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - RSTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - RSTACK \/ sp0 <= ly_C ly) /\ kHighMemBeg <= sp0 - RSTACK /\ sp0 <= kHighMemEnd.
Proof.
pose proof (lo_disj ly LY) as HD. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. clear HD.
destruct Hsp as (S1 & S3 & S4). unfold zdisjoint, kThreadObjSize, RSTACK, kPrimResvSize in *. cbn [fst snd] in *. unfold T.
split; [img_try (clear PS CS; img_lia)|]. split; [img_try (clear TS CS; img_lia)|]. split; [img_try (clear TS PS; img_lia)|]. clear TS PS CS. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
Qed.
Lemma zone_litR : forall lo hi wlo whi, TFX_IMG_LO <= lo -> hi <= TFX_IMG_END -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof stack_ivsR as (_ & _ & _ & S1 & _). pose proof high_factsR as (F1 & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR S1 F1 HcR. numconst. unfold zone3cases, DSTv, Pr, T in *. numconst. img_lia.
Qed.
Lemma zone_TR : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> (hi <= DSTv \/ DSTv + 32 <= lo) ->
RFACTSR lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof high_factsR as (F1 & F2 & _). pose proof stack_ivsR as (DT & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 Hz3 F1 F2 DT. numconst. unfold zone3cases in *. numconst. unfold T in *. img_lia.
Qed.
Lemma zone_CR : forall lo hi wlo whi, ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof stack_ivsR as (_ & _ & DC & _).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. unfold zdisjoint in CT. cbn [fst snd] in CT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F7 F8 DC CT. numconst. unfold zone3cases in *. numconst. unfold T in *. img_lia.
Qed.
Lemma zone_RGR : forall lo hi wlo whi,
RGv <= lo -> hi <= RGv + 128 -> (whi <= wlo \/ (RGv <= wlo /\ whi <= RGv + 128)) -> RFACTSR lo hi wlo whi.
Proof.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (_ & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F3 F4 F5 F6 DP PT. numconst. unfold zone3cases in *. numconst. unfold T, SB in *. img_lia.
Qed.
Lemma slots_not_WINR0 : forall a, DSTv <= a < DSTv + 64 -> ~ WINR0 a.
Proof.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; img_lia.
Qed.
Lemma fa_not_WINR0 : forall a, FAv <= a < FAv + 2 ^ 29 -> ~ WINR0 a.
Proof.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; img_lia.
Qed.
Lemma tail_ext_okR : forall (E : env) r,
(forall k, (k < aHAV)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILR ->
let b := base_val E (YQ0b.r_base r) in
RFACTSR (b + YQ0b.r_lo r) (b + YQ0b.r_hi r) (b + YQ0b.r_wlo r) (b + YQ0b.r_whi r).
Proof.
intros E r HE Hin. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
let sk := img_ev constr:(SKEL_TAILR) in img_change SKEL_TAILR with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); img_lia)); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG, ?EaSB, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T, SB, SHBv in *; img_lia)).
all: lazymatch goal with |- RFACTSR _ _ _ _ => idtac end.
all: first [ img_apply zone_litR; clear - DR; numconst; unfold TFX_TSD, TFX_TP; img_lia
| img_apply zone_RGR; clear - DR; numconst; img_lia
| img_apply zone_TR; clear - DR F1 F2; numconst; unfold T in *; img_lia
| img_apply zone_CR; clear - DR F7 F8; numconst; img_lia ].
Qed.
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R RJ2 W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Lemma rdn_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
exists bs, rdn tfxsegs m (Z_to_bv 64 a) nn = Some bs /\ length bs = nn.
Proof.
intros m nn. induction nn as [|nn IH]; intros a Hp Ha Hnw.
- exists []. split; img_refl.
- destruct (Hp 0 ltac:(img_lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [img_try (intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by img_lia; img_apply Hp; img_lia) | img_lia | img_lia |].
exists (b :: bs). split; [|img_try (cbn; img_lia)]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [img_try (rewrite Hbs; img_refl)|].
img_apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
img_change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. img_refl.
Qed.
Lemma store_ok_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
store_ok tfxsegs m (Z_to_bv 64 a) nn = true.
Proof.
intros m nn a Hp Ha Hnw. destruct nn as [|n']; [img_refl|].
img_apply store_ok_of_all; [img_try (rewrite unsigned_lit_small by img_lia; img_lia)|].
intros x Hx. rewrite unsigned_lit_small in Hx by img_lia.
destruct (Hp (bv_unsigned x - a) ltac:(img_lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by img_lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma cpy4_stretch : forall (k : nat) (E : env) ss ms md (d src len : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = (0x36980 + D_150) ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 20 = Z_to_bv 64 src -> getr (ms_regs ms) 13 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 (d + len) ->
4 <= len -> len mod 4 = 0 -> 0 <= d -> d + len < 2 ^ 64 -> 0 <= src -> src + len < 2 ^ 64 ->
(d + len <= src \/ src + len <= d) ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall a, src <= a < src + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [12; 13; 20]%bv))
(ss_after_stretch ss (ss_mem ss) k [12; 13; 20]%bv (0x36994 + D_150))
(restrict (w_H W) (mkst regs' (Z_to_bv 64 (0x36994 + D_150)) mem' (seg_rom tfxsegs))) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall j, 0 <= j < len -> mem' (w64 (d + j)) = ms_mem ms (w64 (src + j))) ->
SRr tfxsegs W (mkCfg (mkst regs' (Z_to_bv 64 (0x36994 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs W (mkCfg ms md) Q.
Proof.
intros k E ss ms md d src len Q HS Hrv Hpc Hat Hnc H20 H13 H11 Hlen Hl4 Hd Hdl Hs Hsl Hdisj Hpd Hps Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H W) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H W) (ms_mem ms)).
destruct (rdn_of_presentR mr (Z.to_nat len) src) as (bs & Hbs & Hbl);
[ img_try (intros i Hi; destruct (Hps (src + i) ltac:(img_lia)) as [Hh [b Hb]]; exists b; unfold mr, mrestrict; rewrite Hh; img_exact Hb)
| img_try (unfold TFX_IMG_END in *; img_lia) | img_lia |].
assert (HOK : mcH mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs).
{ img_apply MCH; [img_try (unfold TFX_IMG_END in *; img_lia) | img_lia | img_try (rewrite Hbl; img_exact Hbs) | | | |]; rewrite ?unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); try img_lia.
rewrite Hbl. img_apply store_ok_of_presentR; [|img_try (unfold TFX_IMG_END in *; img_lia)|img_lia].
intros i Hi. destruct (Hpd (d + i) ltac:(img_lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. img_exact Hb. }
destruct (tfx_cpy4_run mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs (seg_rom tfxsegs) (ms_regs ms) HOK Hl4 Hlen H20 H13
ltac:(img_try (rewrite H11; unfold at_; rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_refl)))
as (regs' & Hms & R20 & R13 & R11 & Rfr).
eapply (SRr_msteps tfxsegs Hwx W _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
img_change (unrestrict (w_H W) (ms_mem ms) (mkst regs' (Z_to_bv 64 (0x36994 + D_150) : word) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 (0x36994 + D_150) : word) (munrestrict (w_H W) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H W) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H W) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H W) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); rewrite Hbl; img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H W) ms) regs' m1 (ss_mem ss) (0x36994 + D_150) [12; 13; 20]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
img_apply Rfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H W x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros j Hj. destruct (Hpd (d + j) ltac:(img_lia)) as [Hh _]. destruct (Hps (src + j) ltac:(img_lia)) as [Hh' [b' Hb']].
(subst m1full; cbv beta). unfold munrestrict, w64. rewrite Hh. (subst m1; cbv beta).
rewrite (wbytes_inside bs mr (Z_to_bv 64 d) (Z_to_bv 64 (d + j))) by (img_try (rewrite ?unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); rewrite ?Hbl; img_lia)).
rewrite !unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)). replace (Z.to_nat (d + j - d)) with (Z.to_nat j) by (img_try (f_equal; img_lia)).
pose proof (rdn_nth tfxsegs mr (Z.to_nat len) (Z_to_bv 64 src) bs (Z.to_nat j) Hbs ltac:(img_lia)) as R1.
replace (Z_to_bv 64 src + nat_to_word (Z.to_nat j))%bv with (Z_to_bv 64 (src + j)) in R1
by (img_try (img_apply bv_eq; rewrite bv_add_unsigned; unfold nat_to_word; rewrite !Z_to_bv_unsigned; unfold bv_wrap; img_change (bv_modulus 64) with (2 ^ 64);
rewrite Z2Nat.id, <- Z.add_mod, !Z.mod_small by (unfold TFX_IMG_END in *; img_lia); img_refl)).
cbn [rdn] in R1. (subst mr; cbv beta). unfold mrestrict in R1. rewrite Hh', Hb' in R1. cbn in R1. injection R1 as <-. rewrite Hb'. img_refl.
Qed.
Variables (B : asyms) (S : astate).
Hypothesis TS : TfxSyms B.
Hypothesis HTSD : ly_tsd ly = TFX_TSD.
Hypothesis HARm : ARm B ly S (aview tfxsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hchunks : pc_chunks (cache S c) = [].
Hypothesis Hnf_def : nf = fa_len (rg_free (reg S c)).
Hypothesis Hmf_def : mf = rg_mapped_fa (reg S c).
Hypothesis Hau_def : au = rg_alloc_user (reg S c).
Hypothesis Hmu_def : mu = rg_mapped_user (reg S c).
Hypothesis Hj64v : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 64) 4 j64.
Hypothesis Hjnav : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 72) 8 jna.
Hypothesis Hjnfv : val_mem tfxsegs (mrestrict (w_H W) mem0) (RGv + 80) 8 jnf.
Hypothesis Hjsmv : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm.
Hypothesis Hjm1v : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfxsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2.
Hypothesis HQL : qloose S.
Lemma Pr_is : Pr = ly_T ly + t_cache + 80 * c. Proof. img_refl. Qed.
Lemma RGv_is : RGv = ly_space ly + kRegionInfoOff + 128 * c. Proof. img_refl. Qed.
Lemma FAv_is : FAv = fa_base ly c.
Proof. clear - HcR. unfold FAv, RBv, fa_base, SB. rewrite region_off_eq by img_lia. img_refl. Qed.
Lemma RBv_is : RBv = region_base ly c.
Proof. clear - HcR. unfold RBv, region_base, SB. rewrite region_off_eq by img_lia. img_refl. Qed.
End f.
End e.
