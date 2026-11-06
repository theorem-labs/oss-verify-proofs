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
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF3v YF4q YF8g YF7x YF3w YF7z YF66 YF65.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YF04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0h.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0h.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
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
Section g. Context {imgk : img}.
Variables (W : world tfxsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model) (c : Z).
Variables (maxc n nf mf au mu csz j64 jna jnf jsm jm1 jm2 : Z).
Variables (need tot adr sha mu2 nce ncg nfe nfg fadr shf mf2 aue aug : Z).
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
w64 nf; w64 mf; w64 au; w64 mu; w64 SHBv; w64 j64; w64 jna; w64 jnf; w64 jsm; w64 jm1; w64 jm2;
w64 need; w64 tot; w64 adr; w64 sha; w64 mu2; w64 nce; w64 ncg; w64 nfe; w64 nfg; w64 fadr; w64 shf; w64 mf2; w64 aue; w64 aug ].
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
Lemma EaNEED : ew E0 55 = w64 need. Proof. img_refl. Qed.
Lemma EaTOT : ew E0 56 = w64 tot. Proof. img_refl. Qed.
Lemma EaADR : ew E0 57 = w64 adr. Proof. img_refl. Qed.
Lemma EaSHA : ew E0 58 = w64 sha. Proof. img_refl. Qed.
Hypothesis IMG : img_cover ly.
Lemma EaMU2 : ew E0 59 = w64 mu2. Proof. img_refl. Qed.
Lemma EaNCe : ew E0 60 = w64 nce. Proof. img_refl. Qed.
Lemma EaNCg : ew E0 61 = w64 ncg. Proof. img_refl. Qed.
Lemma EaNFe : ew E0 62 = w64 nfe. Proof. img_refl. Qed.
Lemma EaNFg : ew E0 63 = w64 nfg. Proof. img_refl. Qed.
Lemma EaFADR : ew E0 64 = w64 fadr. Proof. img_refl. Qed.
Lemma EaSHF : ew E0 65 = w64 shf. Proof. img_refl. Qed.
Lemma EaMF2 : ew E0 66 = w64 mf2. Proof. img_refl. Qed.
Lemma EaAUe : ew E0 67 = w64 aue. Proof. img_refl. Qed.
Lemma EaAUg : ew E0 68 = w64 aug. Proof. img_refl. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. img_exact (ew_Ereg_nat regs0 XWR k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. img_exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. img_exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. img_exact (Er 8 8%bv eq_refl). Qed.
Hypothesis LY : layout_ok ly.
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
Hypothesis Hnlt : nf < n.
Hypothesis Hcarved : mu - au < kUserMapSize + kMaxSize.
Hypothesis Hau_al : au mod csz = 0.
Hypothesis Hneed : need = n - nf.
Hypothesis Htot : tot = au + need * csz.
Hypothesis Hadr : adr = RBv + mu.
Hypothesis Hsha : sha = SHBv + adr / 8.
Hypothesis Hmu2 : mu2 = mu + kUserMapSize.
Hypothesis Hnce : nce = (mu - au) / csz.
Hypothesis Hncg : ncg = (mu2 - au) / csz.
Hypothesis Hnfe : nfe = nf + nce.
Hypothesis Hnfg : nfg = nf + ncg.
Hypothesis Hfadr : fadr = FAv + mf.
Hypothesis Hshf : shf = SHBv + fadr / 8.
Hypothesis Hmf2 : mf2 = mf + kFreeArrayMapSize.
Hypothesis Haue : aue = au + nce * csz.
Hypothesis Haug : aug = au + ncg * csz.
Ltac clear3 := try clear Hnlt Hcarved Hau_al Hneed Htot Hadr Hsha Hmu2 Hnce Hncg Hnfe Hnfg Hfadr Hshf Hmf2 Haue Haug.
Lemma class_facts : 2 <= maxc <= 16 /\ maxc mod 2 = 0 /\ 1 <= n <= 8 /\ 16 <= csz <= kMaxSize /\ csz mod 16 = 0.
Proof. clear3.
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
Proof. clear3.
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
Proof. clear3.
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
Proof. clear3.
intros E a [[bt lt] ht] [[bu lu] hu] Hs Hr. unfold win_sub in Hs. cbn [fst snd] in *.
apply andb_prop in Hs as [Hs H3]. apply andb_prop in Hs as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
destruct bt as [x|], bu as [y|]; cbn in H1; try discriminate.
- apply Nat.eqb_eq in H1. (subst; cbv beta). img_lia.
- img_lia.
Qed.
Lemma WSKELR_WINR0 : forall (E : env) a t,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In t WSKELR ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINR0 a.
Proof. clear3.
intros E a t HE Hin Hr. unfold WSKELR in Hin. cbn [In] in Hin. unfold WINR0.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; unfold rP, rRG, rT in Hr; rewrite HE in Hr by (img_try (unfold aHAV3; img_lia));
rewrite ?E2, ?EaT, ?EaP, ?EaRG in Hr; unfold w64 in Hr;
pose proof derived_rangesR as DR; pose proof high_factsR as HF; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize in DR, HF;
rewrite ?unsigned_lit_small in Hr by img_lia; unfold sp0 in *; img_lia.
Qed.
Lemma windows_WINR0 : forall (E : env) rs a,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINR0 a.
Proof. clear3.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). img_exact (WSKELR_WINR0 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. img_lia.
Qed.
Lemma frame_WINR0 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINR0 (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros E rs m m' HE Hb HF x Hx. img_apply HF. intros Hw. img_apply Hx. img_exact (windows_WINR0 E rs _ HE Hb Hw). Qed.
Lemma frame_X : forall (X : Z -> Prop) (E : env) rs (m m' : word -> option byte),
(forall a, WINR0 a -> X a) ->
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ X (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros X E rs m m' HX HE Hb HF x Hx. img_apply (frame_WINR0 E rs m m'); [img_try (img_exact HE) | img_try (img_exact Hb) | img_try (img_exact HF) |]. intros Hw. apply Hx, HX, Hw. Qed.
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (img_try (intros x Hx; transitivity (m1 x); [img_try (img_exact (frame_X X E rs m1 m2 HX HE ltac:((img_case; vm_compute); img_refl) HFx x Hx)) | img_try (img_exact (MEQ x Hx))]));
clear MEQ HFx; rename MEQ' into MEQ
end.
Definition W_DST (a : Z) : Prop := DSTv <= a < DSTv + 4 * n.
Definition W_FE (nf' : Z) (a : Z) : Prop := FAv + 4 * nf <= a < FAv + 4 * nf'.
Definition W_UW (a : Z) : Prop := adr <= a < adr + kUserMapSize.
Definition W_USH (a : Z) : Prop := sha <= a < sha + kUserMapSize / 8.
Definition W_FW (a : Z) : Prop := fadr <= a < fadr + kFreeArrayMapSize.
Definition W_FSH (a : Z) : Prop := shf <= a < shf + kFreeArrayMapSize / 8.
Definition at_R3 (Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree aHAV3 E0 E' /\
st_ok tfxsegs E' ss (restrict (w_H Wx) ms) /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_N3 (Wx : world tfxsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree aHAV3 E0 E' /\
st_ok_ecall tfxsegs E' ss (restrict (w_H Wx) ms) /\ ss_resv ss = None /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_RET3 {imgk : img} (Wx : world tfxsegs) (v : Z) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (W' : world tfxsegs) (c' : config) : Prop :=
W' = Wx /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 10 = Z_to_bv 64 v /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) mem' a) /\
P mem'.
Definition P_cells (Wx : world tfxsegs) (cnt nfv mfv auv muv : Z) (m' : word -> option byte) : Prop :=
let m := mrestrict (w_H Wx) m' in
(forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H Wx) m' a) /\
val_mem tfxsegs m Pr 4 cnt /\ val_mem tfxsegs m (Pr + 4) 4 maxc /\ val_mem tfxsegs m (Pr + 8) 8 csz /\
val_mem tfxsegs m RGv 8 0 /\ val_mem tfxsegs m (RGv + 8) 8 0 /\ val_mem tfxsegs m (RGv + 16) 8 nfv /\
val_mem tfxsegs m (RGv + 24) 8 mfv /\ val_mem tfxsegs m (RGv + 32) 8 auv /\ val_mem tfxsegs m (RGv + 40) 8 0 /\
val_mem tfxsegs m (RGv + 48) 8 muv /\ val_mem tfxsegs m (RGv + 56) 8 0 /\ val_mem tfxsegs m (RGv + 68) 1 0.
Fixpoint chunk_index (cs : list YQ0b.chunk) (off : Z) : nat :=
match cs with [] => 0%nat | ch :: t => if YQ0b.c_off ch =? off then 0%nat else Datatypes.S (chunk_index t off) end.
Definition pstable (P : (word -> option byte) -> Prop) : Prop :=
forall m m' : word -> option byte, (forall x : word, ~ WINR0 (bv_unsigned x) -> m' x = m x) -> P m -> P m'.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. clear3. intros E r rs H. induction rs as [|r' rs IH]; cbn; [img_try (img_exact I)|]. split; [img_try (img_apply H; left; img_refl) | img_try (img_apply IH; intros x Hx; img_apply H; right; img_exact Hx)]. Qed.
Lemma kept_of_frame : forall (Wx : world tfxsegs) (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m1 a) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
region_kept tfxsegs E (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m1) r.
Proof. clear3.
intros Wx E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. img_apply apresent_writable_off; [img_try (img_exact Hh)|]. img_apply Hpr. img_apply writable_off_apresent; [img_try (img_exact Hh) | img_try (img_exact Hw)].
Qed.
Lemma kept_of_frame2 : forall (Hh : word -> bool) (E : env) (m m1 : word -> option byte) (R : Z -> Prop) r,
(forall x : word, ~ R (bv_unsigned x) -> m1 x = m x) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
region_kept tfxsegs E (mrestrict Hh m) (mrestrict Hh m1) r.
Proof. clear3.
intros Hh E m m1 R r Hfr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. img_apply mbyte_mrestrict_same. img_apply Hfr. rewrite unsigned_lit_small by img_lia. img_exact Hno.
- intros a Ha Hw. destruct (Hwin a Ha) as [Hno Hr]. img_apply (writable_at_eq tfxsegs (mrestrict Hh m)); [|img_try (img_exact Hw)].
unfold mrestrict. rewrite (Hfr (Z_to_bv 64 a)) by (img_try (rewrite unsigned_lit_small by img_lia; img_exact Hno)). img_refl.
Qed.
Definition SKEL_TAILR {imgk : img} : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0R3).
Definition RFACTSR (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - RSTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFX_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFX_IMG_LO)) /\
(hi <= DSTv \/ DSTv + 32 <= lo).
Lemma stack_ivsR :
(T + kThreadObjSize <= sp0 - RSTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - RSTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - RSTACK \/ sp0 <= ly_C ly) /\ kHighMemBeg <= sp0 - RSTACK /\ sp0 <= kHighMemEnd.
Proof. clear3.
pose proof (lo_disj ly LY) as HD. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. clear HD.
destruct Hsp as (S1 & S3 & S4). unfold zdisjoint, kThreadObjSize, RSTACK, kPrimResvSize in *. cbn [fst snd] in *. unfold T.
split; [img_try (clear PS CS; img_lia)|]. split; [img_try (clear TS CS; img_lia)|]. split; [img_try (clear TS PS; img_lia)|]. clear TS PS CS. unfold kHighMemBeg, kHighMemEnd in *. img_lia.
Qed.
Lemma zone_litR : forall lo hi wlo whi, TFX_IMG_LO <= lo -> hi <= TFX_IMG_END -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof stack_ivsR as (_ & _ & _ & S1 & _). pose proof high_factsR as (F1 & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR S1 F1 HcR. numconst. unfold zone3cases, DSTv, Pr, T in *. numconst. img_lia.
Qed.
Lemma zone_TR : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> (hi <= DSTv \/ DSTv + 32 <= lo) ->
RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof high_factsR as (F1 & F2 & _). pose proof stack_ivsR as (DT & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 Hz3 F1 F2 DT. numconst. unfold zone3cases in *. numconst. unfold T in *. img_lia.
Qed.
Lemma zone_CR : forall lo hi wlo whi, ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof stack_ivsR as (_ & _ & DC & _).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. unfold zdisjoint in CT. cbn [fst snd] in CT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F7 F8 DC CT. numconst. unfold zone3cases in *. numconst. unfold T in *. img_lia.
Qed.
Lemma zone_RGR : forall lo hi wlo whi,
RGv <= lo -> hi <= RGv + 128 -> (whi <= wlo \/ (RGv <= wlo /\ whi <= RGv + 128)) -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (_ & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F3 F4 F5 F6 DP PT. numconst. unfold zone3cases in *. numconst. unfold T, SB in *. img_lia.
Qed.
Lemma slots_not_WINR0 : forall a, DSTv <= a < DSTv + 64 -> ~ WINR0 a.
Proof. clear3.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; img_lia.
Qed.
Lemma fa_not_WINR0 : forall a, FAv <= a < FAv + 2 ^ 29 -> ~ WINR0 a.
Proof. clear3.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; img_lia.
Qed.
Lemma tail_ext_okR : forall (E : env) r,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILR ->
let b := base_val E (YQ0b.r_base r) in
RFACTSR (b + YQ0b.r_lo r) (b + YQ0b.r_hi r) (b + YQ0b.r_wlo r) (b + YQ0b.r_whi r).
Proof. clear3.
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
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Lemma rdn_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
exists bs, rdn tfxsegs m (Z_to_bv 64 a) nn = Some bs /\ length bs = nn.
Proof. clear3.
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
Proof. clear3.
intros m nn a Hp Ha Hnw. destruct nn as [|n']; [img_refl|].
img_apply store_ok_of_all; [img_try (rewrite unsigned_lit_small by img_lia; img_lia)|].
intros x Hx. rewrite unsigned_lit_small in Hx by img_lia.
destruct (Hp (bv_unsigned x - a) ltac:(img_lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by img_lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma cpy4_stretch : forall (Wx : world tfxsegs) (k : nat) (E : env) ss ms md (d src len : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = (0x36980 + D_150) ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 20 = Z_to_bv 64 src -> getr (ms_regs ms) 13 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 (d + len) ->
4 <= len -> len mod 4 = 0 -> 0 <= d -> d + len < 2 ^ 64 -> 0 <= src -> src + len < 2 ^ 64 ->
(d + len <= src \/ src + len <= d) ->
(forall a, d <= a < d + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall a, src <= a < src + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [12; 13; 20]%bv))
(ss_after_stretch ss (ss_mem ss) k [12; 13; 20]%bv (0x36994 + D_150))
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 (0x36994 + D_150)) mem' (seg_rom tfxsegs))) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall j, 0 <= j < len -> mem' (w64 (d + j)) = ms_mem ms (w64 (src + j))) ->
SRr tfxsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 (0x36994 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md d src len Q HS Hrv Hpc Hat Hnc H20 H13 H11 Hlen Hl4 Hd Hdl Hs Hsl Hdisj Hpd Hps Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
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
eapply (SRr_msteps tfxsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
img_change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 (0x36994 + D_150) : word) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 (0x36994 + D_150) : word) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); rewrite Hbl; img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) (0x36994 + D_150) [12; 13; 20]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
img_apply Rfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [img_refl|].
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
Lemma facts3 :
1 <= need <= 8 /\ n * csz <= kMaxSize /\ need * csz <= kMaxSize /\ 16 <= tot /\ tot = au + need * csz /\
kHighMemBeg <= adr /\ adr + kUserMapSize <= RBv + 2 ^ 32 /\ adr mod 65536 = 0 /\ RBv <= adr /\ adr = RBv + mu /\
sha = SHBv + adr / 8 /\ sha mod 4096 = 0 /\ 2201439137792 <= sha /\ sha + 32768 <= 17594332479488 /\
mu2 = mu + kUserMapSize /\
0 <= nce /\ nce * csz <= mu - au < nce * csz + csz /\ 0 <= ncg /\ ncg * csz <= mu2 - au < ncg * csz + csz /\
nce < 2 ^ 16 /\ ncg < 2 ^ 16 /\ nfe = nf + nce /\ nfg = nf + ncg /\
fadr = FAv + mf /\ fadr mod 65536 = 0 /\ FAv mod 65536 = 0 /\ shf = SHBv + fadr / 8 /\ shf mod 4096 = 0 /\
2201439137792 <= shf /\ shf + 32768 <= 17594332479488 /\ kHighMemBeg <= fadr /\ fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize /\
mf2 = mf + kFreeArrayMapSize /\ aue = au + nce * csz /\ aug = au + ncg * csz /\ aue mod 16 = 0 /\ aug mod 16 = 0.
Proof.
pose proof class_facts as (K1 & K2 & K3 & K4 & K5). pose proof derived_rangesR as DR. pose proof Hnf as [N0 N1]. pose proof Hmu as ([U0 U1] & U2 & U3 & U4).
pose proof Hmf as [[M0 M1] M2].
pose proof (class_ok c HcR) as (_ & C32 & _ & _ & _ & CM). rewrite <- Hcsz, <- Hmax in CM. rewrite <- Hcsz in C32.
assert (NC8 : n * csz <= kMaxSize) by (img_try (rewrite Hn; img_exact CM)).
assert (NE1 : 1 <= need) by (img_try (clear - Hneed Hnlt; img_lia)). assert (NE2 : need <= 8) by (img_try (clear - Hneed N0 K3; img_lia)).
assert (NCSZ : need * csz <= kMaxSize) by (img_try (rewrite Hneed; clear - NC8 N0 Hnlt K3 K4; unfold kMaxSize in *; nia)).
assert (T16 : 16 <= tot) by (img_try (rewrite Htot; clear - NE1 K4 U0; nia)).
pose proof (Z.div_mod (mu - au) csz ltac:(img_try (clear - K4; img_lia))) as D1. pose proof (Z.mod_pos_bound (mu - au) csz ltac:(img_try (clear - K4; img_lia))) as B1.
pose proof (Z.div_mod (mu2 - au) csz ltac:(img_try (clear - K4; img_lia))) as D2. pose proof (Z.mod_pos_bound (mu2 - au) csz ltac:(img_try (clear - K4; img_lia))) as B2.
assert (P1 : 0 <= nce) by (img_try (rewrite Hnce; img_apply Z.div_pos; [img_try (clear - U0 U1; img_lia) | img_try (clear - K4; img_lia)])).
assert (P2 : 0 <= ncg) by (img_try (rewrite Hncg, Hmu2; img_apply Z.div_pos; [img_try (clear - U0 U1; unfold kUserMapSize; img_lia) | img_try (clear - K4; img_lia)])).
assert (E1a : nce * csz <= mu - au) by (img_try (rewrite Hnce; clear - D1 B1 K4; nia)). assert (E1b : mu - au < nce * csz + csz) by (img_try (rewrite Hnce; clear - D1 B1 K4; nia)).
assert (E2a : ncg * csz <= mu2 - au) by (img_try (rewrite Hncg; clear - D2 B2 K4; nia)). assert (E2b : mu2 - au < ncg * csz + csz) by (img_try (rewrite Hncg; clear - D2 B2 K4; nia)).
assert (S1 : nce < 2 ^ 16) by (img_try (clear - E1a Hcarved K4 P1; unfold kUserMapSize, kMaxSize in *; nia)).
assert (S2 : ncg < 2 ^ 16) by (img_try (pose proof E2a as E; rewrite Hmu2 in E; clear - E Hcarved K4 P2; unfold kUserMapSize, kMaxSize in *; nia)).
assert (RBAL : RBv mod 65536 = 0) by (img_try (clear - DR; tauto)).
pose proof RBAL as RBAL'. apply Z.mod_divide in RBAL' as [qb Hqb]; [|img_try (clear; img_lia)].
pose proof U3 as U3'. apply Z.mod_divide in U3' as [qu Hqu]; [|img_try (clear; unfold kUserMapSize; img_lia)].
pose proof M2 as M2'. apply Z.mod_divide in M2' as [qm Hqm]; [|img_try (clear; unfold kFreeArrayMapSize; img_lia)].
assert (AAL : adr mod 65536 = 0) by (img_try (rewrite Hadr, Hqb, Hqu; img_apply Z.mod_divide; [img_try (clear; img_lia)|]; exists (qb + 4 * qu); unfold kUserMapSize; clear; img_lia)).
assert (FAE : FAv = RBv + kFreeArrayOffset) by (img_try (clear - DR; tauto)).
assert (FAL : FAv mod 65536 = 0).
{ rewrite FAE, Hqb. img_apply Z.mod_divide; [img_try (clear; img_lia)|]. exists (qb + 57344). unfold kFreeArrayOffset. clear; img_lia. }
assert (FDAL : fadr mod 65536 = 0).
{ rewrite Hfadr, FAE, Hqb, Hqm. img_apply Z.mod_divide; [img_try (clear; img_lia)|]. exists (qb + 57344 + 4 * qm). unfold kFreeArrayOffset, kFreeArrayMapSize. clear; img_lia. }
assert (SHAL : forall x, x mod 65536 = 0 -> (SHBv + x / 8) mod 4096 = 0).
{ clear. intros x Hx. apply Z.mod_divide in Hx as [q Hq]; [|img_lia]. rewrite Hq. replace (q * 65536) with (q * 8192 * 8) by img_lia. rewrite Z.div_mul by img_lia.
img_apply Z.mod_divide; [img_lia|]. exists (524280 + 2 * q). unfold SHBv. img_lia. }
pose proof K5 as K5'. apply Z.mod_divide in K5' as [qc Hqc]; [|img_try (clear; img_lia)]. pose proof U4 as U4'. apply Z.mod_divide in U4' as [qa Hqa]; [|img_try (clear; img_lia)].
assert (AUE16 : aue mod 16 = 0) by (img_try (rewrite Haue, Hqa, Hqc; img_apply Z.mod_divide; [img_try (clear; img_lia)|]; exists (qa + nce * qc); clear; img_lia)).
assert (AUG16 : aug mod 16 = 0) by (img_try (rewrite Haug, Hqa, Hqc; img_apply Z.mod_divide; [img_try (clear; img_lia)|]; exists (qa + ncg * qc); clear; img_lia)).
pose proof (SHAL adr AAL) as SAL. pose proof (SHAL fadr FDAL) as SFL. rewrite <- Hsha in SAL. rewrite <- Hshf in SFL.
assert (A1 : kHighMemBeg <= adr) by (img_try (rewrite Hadr; clear - DR U0 U1; numconst; img_lia)).
assert (A2 : RBv <= adr) by (img_try (rewrite Hadr; clear - U0 U1; img_lia)).
assert (A3 : adr + kUserMapSize <= RBv + 2 ^ 32) by (img_try (rewrite Hadr; clear - U0 U1 U2; numconst; img_lia)).
assert (SH1 : 2201439137792 <= sha) by (img_try (rewrite Hsha; pose proof (Z.div_le_mono kHighMemBeg adr 8 ltac:(clear; img_lia) A1) as X; clear - X; unfold SHBv, kHighMemBeg in *; img_change (17594333495296 / 8) with 2199291686912 in X; img_lia)).
assert (ACE : adr <= ASAN_CEIL) by (img_try (clear - DR A3 U2; numconst; img_lia)).
assert (SH2 : sha + 32768 <= 17594332479488).
{ rewrite Hsha. ceil. pose proof (Z.div_le_mono adr 140737479966720 8 ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - ACE CR0; unfold ASAN_CEIL in *; img_lia))) as X. clear - X. unfold SHBv. img_change (140737479966720 / 8) with 17592184995840 in X. img_lia. }
assert (F1 : kHighMemBeg <= fadr) by (img_try (rewrite Hfadr, FAE; clear - DR M0; numconst; img_lia)).
assert (F2 : fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize) by (img_try (rewrite Hfadr, FAE; clear - M0 M1; numconst; img_lia)).
assert (FCE : fadr <= ASAN_CEIL) by (img_try (clear - DR F2; numconst; img_lia)).
assert (SF1 : 2201439137792 <= shf) by (img_try (rewrite Hshf; pose proof (Z.div_le_mono kHighMemBeg fadr 8 ltac:(clear; img_lia) F1) as X; clear - X; unfold SHBv, kHighMemBeg in *; img_change (17594333495296 / 8) with 2199291686912 in X; img_lia)).
assert (SF2 : shf + 32768 <= 17594332479488).
{ rewrite Hshf. ceil. pose proof (Z.div_le_mono fadr 140737479966720 8 ltac:(img_try (clear; img_lia)) ltac:(img_try (clear - FCE CR0; unfold ASAN_CEIL in *; img_lia))) as X. clear - X. unfold SHBv. img_change (140737479966720 / 8) with 17592184995840 in X. img_lia. }
repeat split; assumption.
Qed.
Definition RFACTS3 (lo hi wlo whi : Z) : Prop :=
RFACTSR lo hi wlo whi /\ (hi <= RBv \/ RBv + 2 ^ 32 <= lo \/ hi <= lo) /\ (hi <= 2201439137792 \/ kHighMemBeg <= lo \/ hi <= lo).
Lemma tail_ext_ok3 : forall (E : env) r,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILR ->
let b := base_val E (YQ0b.r_base r) in
RFACTS3 (b + YQ0b.r_lo r) (b + YQ0b.r_hi r) (b + YQ0b.r_wlo r) (b + YQ0b.r_whi r).
Proof. clear3.
intros E r HE Hin. split; [img_try (img_exact (tail_ext_okR E r HE Hin))|].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC.
unfold zdisjoint in PT, PC. cbn [fst snd] in PT, PC.
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YQ0b.r_base YQ0b.r_lo YQ0b.r_hi YQ0b.r_wlo YQ0b.r_whi].
let sk := img_ev constr:(SKEL_TAILR) in img_change SKEL_TAILR with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [img_try (injection Hin as <- <- <- <- <-)|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (img_try (clear - HE; (img_case; cbv); img_lia)); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG, ?EaSB, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (img_try (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T, SB, SHBv in *; img_lia)).
all: unfold Pr, RGv, RBv in *; clear - DR F1 F2 F3 F4 F5 F6 F7 F8 PT PC HcR; numconst; unfold TFX_TSD, TFX_TP, SHBv, T, SB in *; zlia.
Qed.
Lemma stack_ext_ok3 : (sp0 <= RBv \/ RBv + 2 ^ 32 <= sp0 - RSTACK) /\ kHighMemBeg <= sp0 - RSTACK.
Proof. clear3.
pose proof stack_ivsR as (_ & SP & _ & S4 & _). pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
unfold RBv in *. clear - SP S4 DR F4 F5 HcR. numconst. unfold SB in *. img_lia.
Qed.
Definition scratch_headed (ss : sstate) : Prop :=
exists cs, nth_error (ss_mem ss) 0 = Some (YQ0b.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs).
Lemma mem_ok_scratch_present : forall (Wx : world tfxsegs) (E' : env) ss (m : word -> option byte),
env_agree aHAV3 E0 E' -> scratch_headed ss -> mem_ok tfxsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a.
Proof. clear3.
intros Wx E' ss m [HE _] [cs Hnth] (_ & Hrs & _) a Ha. pose proof stack_ivsR as (_ & _ & _ & S4 & S5). pose proof (u64_range (getr regs0 2)) as U.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hnth)) as (_ & _ & Hw & _).
cbn [YQ0b.r_base YQ0b.r_wlo YQ0b.r_whi base_val] in Hw. rewrite (HE 2%nat ltac:(img_try (unfold aHAV3; img_lia))), E2 in Hw.
img_apply writable_high_apresent; [img_try (clear - Ha S4 S5 U; numconst; unfold sp0, TFX_IMG_END in *; img_lia)|].
replace a with (bv_unsigned (getr regs0 2) + (a - sp0)) by (img_try (unfold sp0; img_lia)). img_apply Hw. unfold sp0 in *. img_lia.
Qed.
Lemma at_R3_run : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' st W' c',
at_R3 Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WINR0 a -> X a) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
pstable P -> scratch_headed ss' ->
SRr tfxsegs W' c' (at_R3 Wx md X P ss').
Proof. clear3.
intros Wx tbl tblok stop md X P ss ss' st W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfxsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfxsegs E' ss' (restrict (w_H Wx) ms')) by (img_try (destruct st; [img_try (img_exact HS') | img_try (destruct Hst) | img_try (img_exact HS')])). clear HS'.
img_apply SRr_ret. split; [img_refl|]. exists ms', mat', E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS'')|].
assert (FR : forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) by (img_try (intros x Hx; img_exact (frame_X WINR0 E' _ _ _ (fun a H => H) (proj1 HE) Hwin HF x Hx))).
split; [|img_try (split)].
- intros x Hx. rewrite (FR x) by (img_try (intros Hw; img_exact (Hx (HX _ Hw)))). img_exact (MEQ x Hx).
- img_exact (mem_ok_scratch_present Wx E' ss' (ms_mem ms') HE Hsc (st_ok_mem_ok tfxsegs E' ss' _ HS'')).
- img_exact (HP _ _ FR HPm).
Qed.
Lemma at_R3_run_ecall : forall (Wx : world tfxsegs) tbl (tblok : table_ok tfxsegs tbl) stop md X P ss ss' W' c',
at_R3 Wx md X P ss W' c' ->
sym_run_toN_sh tfxsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WINR0 a -> X a) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
pstable P -> scratch_headed ss' ->
SRr tfxsegs W' c' (at_N3 Wx md X P ss').
Proof. clear3.
intros Wx tbl tblok stop md X P ss ss' W' c' HR Hrun Hrv HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfxsegs tbl tblok Hwx Wx FUEL stop E' ss ss' RS_ecall ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
img_apply SRr_ret. split; [img_refl|]. exists ms', mat', E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS')|]. split; [img_try (img_exact Hrv)|].
assert (FR : forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) by (img_try (intros x Hx; img_exact (frame_X WINR0 E' _ _ _ (fun a H => H) (proj1 HE) Hwin HF x Hx))).
split; [|img_try (split)].
- intros x Hx. rewrite (FR x) by (img_try (intros Hw; img_exact (Hx (HX _ Hw)))). img_exact (MEQ x Hx).
- destruct HS' as (_ & _ & _ & _ & _ & _ & _ & HM & _). cbn [ms_mem restrict] in HM. img_exact (mem_ok_scratch_present Wx E' ss' (ms_mem ms') HE Hsc HM).
- img_exact (HP _ _ FR HPm).
Qed.
Lemma at_R3_pin : forall (Wx : world tfxsegs) md X P ss W' c' (r : bv 5) (e : sv),
at_R3 Wx md X P ss W' c' -> r <> 0%bv ->
sv_atoms_lt aHAV3 e = true -> sv_atoms_lt aHAV3 (sr_get (ss_regs ss) r) = true ->
U E0 e = U E0 (sr_get (ss_regs ss) r) ->
at_R3 Wx md X P (pin ss r e) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' r e HR Hr Hae Has HU.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold pin. img_apply st_ok_pin_regU; [img_try (img_exact HS) | img_try (img_exact Hr) |].
rewrite (U_agree aHAV3 E0 E' e HE Hae), (U_agree aHAV3 E0 E' _ HE Has). img_exact HU.
Qed.
Lemma at_R3_arm : forall (Wx : world tfxsegs) md X P ss W' c' (cnd : branch_cond) (tk : bool) (a b : sv),
at_R3 Wx md X P ss W' c' ->
sv_atoms_lt aHAV3 a = true -> sv_atoms_lt aHAV3 b = true ->
branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk ->
at_R3 Wx md X P (arm cnd tk a b ss) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' cnd tk a b HR Ha Hb Ht.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold arm. rewrite <- (sv_denot_agree aHAV3 E0 E' a HE Ha), <- (sv_denot_agree aHAV3 E0 E' b HE Hb) in Ht.
destruct tk; [img_try (img_apply st_ok_add_cond; [img_exact HS | img_exact Ht]) | img_try (img_apply st_ok_add_cond_neg; [img_exact HS | img_exact Ht])].
Qed.
Lemma at_R3_forget : forall (Wx : world tfxsegs) md X P ss W' c' (k : nat) (clob : list (bv 5)),
at_R3 Wx md X P ss W' c' -> (aHAV3 <= k)%nat -> ss_resv ss = None ->
ss_atoms_lt k ss = true -> regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
at_R3 Wx md X P (forget ss k clob) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' k clob HR Hk Hrv Hat Hwf Hnc Hma Hnd Hnz.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, (havoc E' k (map (getr (ms_regs ms)) clob)). split; [img_refl|].
split; [img_try (img_exact (env_agree_havoc_ge aHAV3 k E0 E' _ Hk HE))|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
pose proof (st_ok_forget k E' ss (w_H Wx) ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz) as X'. unfold forget.
rewrite <- (st_ok_restrict_mkst tfxsegs (w_H Wx) E' ss ms HS Hrv) in X'. img_exact X'.
Qed.
Lemma at_R3_noconds : forall (Wx : world tfxsegs) md X P ss W' c', at_R3 Wx md X P ss W' c' -> at_R3 Wx md X P (noconds ss) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' HR. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [|img_try (img_exact (conj MEQ (conj PRS HPm)))].
unfold noconds. img_apply st_ok_prune. img_exact HS.
Qed.
Lemma at_R3_weaken : forall (Wx : world tfxsegs) md X X' (P P' : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' -> (forall a, X a -> X' a) -> (forall m, P m -> P' m) -> at_R3 Wx md X' P' ss W' c'.
Proof. clear3.
intros Wx md X X' P P' ss W' c' HR HX HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. repeat (split; [assumption||img_refl|]).
split; [img_try (intros x Hx; img_apply MEQ; intros H; img_exact (Hx (HX _ H)))|]. split; [img_try (img_exact PRS) | img_try (img_exact (HP _ HPm))].
Qed.
Lemma at_R3_facts : forall (Wx : world tfxsegs) md X (P Q : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' ->
(forall (E' : env) ms, env_agree aHAV3 E0 E' -> st_ok tfxsegs E' ss (restrict (w_H Wx) ms) -> Q (ms_mem ms)) ->
at_R3 Wx md X (fun m => P m /\ Q m) ss W' c'.
Proof. clear3.
intros Wx md X P Q ss W' c' HR HQ. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS)|]. split; [img_try (img_exact HPm) | img_try (img_exact (HQ E' ms HE HS))].
Qed.
Lemma at_R3_strengthen : forall (Wx : world tfxsegs) md X (P P' : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' ->
(forall m, (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) -> (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> P' m) ->
at_R3 Wx md X P' ss W' c'.
Proof. clear3.
intros Wx md X P P' ss W' c' HR HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [img_refl|]. exists ms, mat, E'. split; [img_refl|]. split; [img_try (img_exact HE)|]. split; [img_try (img_exact HS)|]. split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS) | img_try (img_exact (HP _ MEQ PRS HPm))].
Qed.
Lemma at_R3_eq : forall (Wx : world tfxsegs) md X P ss ss' W' c', at_R3 Wx md X P ss W' c' -> ss = ss' -> at_R3 Wx md X P ss' W' c'.
Proof. clear3. intros Wx md X P ss ss' W' c' H <-. img_exact H. Qed.
Definition CSAVED : list (bv 5) := [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma sv_denot_SOff0 : forall (E' : env) k, sv_denot E' (SOff k 0) = ew E' k.
Proof. clear. intros E' k. cbn [sv_denot]. rewrite Z.add_0_r. img_apply Z_to_bv_bv_unsigned. Qed.
Lemma at_R3_ret : forall (Wx : world tfxsegs) md X P ss W' c' (v : Z),
at_R3 Wx md X P ss W' c' -> ss_resv ss = None -> ss_pc ss = (0x36764 + D_150) ->
sr_get (ss_regs ss) 1%bv = SOff 1 0 -> sr_get (ss_regs ss) 10%bv = SLit v ->
sr_get (ss_regs ss) 4%bv = SLit TFX_TP ->
Forall (fun r : bv 5 => sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVED ->
SRr tfxsegs W' c' (at_RET3 Wx v md X P).
Proof. clear3.
intros Wx md X P ss W' c' v HR Hrv Hpc H1 H10 H4 Hcs.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_ret_at tfxsegs tfxtbl_rtA tfxtbl_rtA_ok Hwx Wx E' ss ms _ _ HS Hrv); [img_try (rewrite Hpc; (img_case; vm_compute); img_refl)|].
intros mat'. rewrite wvb_collapse.
assert (RG : forall r : bv 5, sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> (Z.to_nat (bv_unsigned r) < aHAV3)%nat -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr Hlt. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms r HS), Hr, sv_denot_SOff0, (proj1 HE _ Hlt). img_apply (Er _ r). rewrite Z2Nat.id; [img_refl | img_try (pose proof (bv_unsigned_in_range 5 r); img_lia)]. }
assert (R1 : getr (ms_regs ms) 1 = getr regs0 1) by (img_try (img_apply RG; [img_try (img_exact H1) | img_try ((img_case; cbv); img_lia)])).
rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra.
split; [img_refl|]. exists (ms_regs ms), (ms_mem ms), mat'. split; [img_refl|].
split. { rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 10 HS), H10. img_refl. }
split. { intros r Hr. destruct (bv_eqb r 4%bv) eqn:E4.
- apply bv_eqb_eq in E4. (subst r; cbv beta). rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 4 HS), H4. cbn [sv_denot]. symmetry. img_exact Htp.
- assert (N4 : r <> 4%bv) by (img_try (intros ->; rewrite bv_eqb_refl in E4; discriminate E4)).
assert (IN : In r CSAVED).
{ unfold CSAVED. cbn [In] in Hr. cbn [In].
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [img_try (first [exfalso; img_apply N4; img_refl | tauto]) |] | False => destruct Hr end. }
img_apply RG; [img_try (img_exact (proj1 (Forall_forall _ _) Hcs r IN))|].
pose proof (bv_unsigned_in_range 5 r) as B. img_change (bv_modulus 5) with 32 in B. unfold aHAV3. img_lia. }
split; [img_try (img_exact MEQ)|]. split; [img_try (img_exact PRS) | img_try (img_exact HPm)].
Qed.
Lemma at_N3_cont : forall (Wx Wy : world tfxsegs) (md' : Model) X (P' : (word -> option byte) -> Prop) ss (e : sv) (v : word) (R : Z -> Prop)
(mem' : word -> option byte) ms (E' : env),
env_agree aHAV3 E0 E' ->
st_ok_ecall tfxsegs E' ss (restrict (w_H Wx) ms) -> ss_resv ss = None ->
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) ->
hsub (w_H Wy) (w_H Wx) ->
sv_denot E' e = v -> no_cdata (ss_mem ss) = true ->
(forall x : word, ~ R (bv_unsigned x) -> mem' x = ms_mem ms x) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E' (YQ0b.r_base r) + YQ0b.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, sp0 - RSTACK <= a < sp0 -> ~ R a) ->
P' mem' ->
at_R3 Wy md' (fun a => X a \/ R a) P' (resume ss e (ss_mem ss) (ss_facts ss)) Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfxsegs)) md').
Proof. clear3.
intros Wx Wy md' X P' ss e v R mem' ms E' HE HS Hrv MEQ PRS Hsub He Hnc Hfr Hext Hwin HsR HP'.
destruct (st_ok_ecall_shape_r tfxsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (Er' : ms_regs ms = regs) by (img_try (rewrite Hms; img_refl)). assert (Em' : ms_mem ms = mem) by (img_try (rewrite Hms; img_refl)).
rewrite Er'. rewrite Em' in MEQ, PRS, Hfr. clear Hms Er' Em'.
pose proof stack_ext_ok3 as [_ SPlo]. pose proof (u64_range (getr regs0 2)) as SPhi.
split; [img_refl|]. exists (mkst (regupd regs 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfxsegs)), (m_vm_materialized md'), E'.
split; [img_try (rewrite with_vm_backing_id; img_refl)|]. split; [img_try (img_exact HE)|]. split; [|img_try (split; [|split])].
- rewrite restrict_mkst_fx. img_apply (st_ok_resume_sv tfxsegs E' ss regs (mrestrict (w_H Wy) mem') e v Hregs); [| img_try (img_exact HG) | img_try (img_exact He)].
img_apply (mem_ok_kept tfxsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem') (ss_mem ss));
[img_try (img_exact (mem_ok_mrestrict_hsub tfxsegs (w_H Wx) (w_H Wy) E' mem (ss_mem ss) (w_Hoff Wx) Hsub Hmem)) | img_try (img_exact Hnc) |].
img_apply Forall_forall. intros r Hr. img_exact (kept_of_frame2 (w_H Wy) E' mem mem' R r Hfr (fun a Ha => Hext r a Hr Ha) (fun a Ha => Hwin r a Hr Ha)).
- intros x Hx. cbn [ms_mem mkst]. rewrite (Hfr x) by (img_try (intros HRx; img_apply Hx; right; img_exact HRx)). img_apply MEQ. intros HXx; img_apply Hx; left; img_exact HXx.
- intros a Ha. cbn [ms_mem mkst]. destruct (PRS a Ha) as [Hh [b Hb]]. split.
+ destruct (w_H Wy (Z_to_bv 64 a)) eqn:Ey; [|img_refl]. rewrite (Hsub _ Ey) in Hh. discriminate Hh.
+ exists b. rewrite (Hfr (Z_to_bv 64 a)); [img_try (img_exact Hb)|]. rewrite unsigned_lit_small by (img_try (clear - Ha SPlo SPhi; numconst; unfold sp0 in *; img_lia)). img_exact (HsR a Ha).
- cbn [ms_mem mkst]. img_exact HP'.
Qed.
Lemma memset_stretch3 : forall (Wx : world tfxsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = tfx_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFX_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_wlo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_whi r ->
(0 <= a < TFX_IMG_LO) \/ (TFX_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfxsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ img_apply store_ok_of_all; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); [img_lia|]. intros x Hx.
pose proof (apresent_writable (w_H Wx) (ms_mem ms) (bv_unsigned x) ltac:(img_try (pose proof (u64_range x); unfold TFX_IMG_END in *; img_lia)) (Hpres (bv_unsigned x) ltac:(img_lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. img_exact Hw. }
destruct (tfx_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfxsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)) SOK
ltac:(img_try (rewrite unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (img_try ((subst bs; cbv beta); rewrite repeat_length; img_lia)).
eapply (SRr_msteps tfxsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by img_lia. f_equal. rewrite Z.add_0_r.
img_change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by img_lia. img_change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [img_lia|]. symmetry. img_apply Znumtheory.Zdivide_mod. img_apply (Z.divide_trans _ 4); [img_try (exists 2; img_refl)|].
img_apply Znumtheory.Zmod_divide; [img_lia | img_try (img_exact Hrpc)]. }
img_change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfxsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) d).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
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
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [img_refl|].
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
Lemma nth_Z_to_le_bytes4 : forall v (t : nat) d, (t < 4)%nat -> nth t (Z_to_le_bytes 4 v) d = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat t)).
Proof. clear.
intros v t d Ht. destruct t as [|[|[|[|t]]]]; [| | | |img_lia]; cbn [Z_to_le_bytes nth]; rewrite ?Z.shiftr_shiftr by img_lia.
- img_change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. img_refl.
- img_refl.
- img_refl.
- img_refl.
Qed.
Lemma popfree_stretch : forall (Wx : world tfxsegs) (k : nat) (E : env) ss ms md (e cst sz cnt : Z) (Q : world tfxsegs -> config -> Prop),
st_ok tfxsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = (0x36cd0 + D_150) ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 0 -> getr (ms_regs ms) 11 = Z_to_bv 64 e -> getr (ms_regs ms) 12 = Z_to_bv 64 cst ->
getr (ms_regs ms) 21 = Z_to_bv 64 sz -> getr (ms_regs ms) 19 = Z_to_bv 64 cnt ->
1 <= cnt -> 4 * cnt <= e -> e < 2 ^ 64 -> 0 <= cst -> 0 <= sz -> cst + cnt * sz < 2 ^ 36 -> TFX_IMG_END <= e - 4 * cnt ->
(forall a, e - 4 * cnt <= a < e -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= e - 4 * cnt \/ e <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfxsegs (havoc E k (map (getr regs') [10; 12; 14; 15]%bv))
(ss_after_stretch ss (ss_mem ss) k [10; 12; 14; 15]%bv (0x36cf0 + D_150))
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 (0x36cf0 + D_150)) mem' (seg_rom tfxsegs))) ->
(forall x : word, ~ (e - 4 * cnt <= bv_unsigned x < e) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall i, 0 <= i < cnt -> val_mem tfxsegs (mrestrict (w_H Wx) mem') (e - 4 - 4 * i) 4 ((cst + i * sz) / 16)) ->
SRr tfxsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 (0x36cf0 + D_150)) mem' (seg_rom tfxsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfxsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md e cst sz cnt Q HS Hrv Hpc Hat Hnc H10 H11 H12 H21 H19 Hcnt Hce He Hcst Hsz Hov Himg Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfxsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
assert (SOK : store_ok tfxsegs mr (Z_to_bv 64 (e - 4 * cnt)) (Z.to_nat (4 * (cnt - 0))) = true).
{ img_apply store_ok_of_presentR; [|img_try (unfold TFX_IMG_END in *; img_lia)|img_lia]. intros i Hi. destruct (Hpres (e - 4 * cnt + i) ltac:(img_lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. img_exact Hb. }
destruct (tfx_popfree_spec (ms_regs ms) mr 0 e cst sz cnt H10 H11 H12 H21 H19 ltac:(img_lia) ltac:(img_lia) Hcst Hsz ltac:(img_lia) SOK)
as (regs' & Hms & R10 & R12 & R14 & R15 & Rfr).
img_change tfx_loaded_segments with tfxsegs in Hms.
replace (Z_to_bv 64 tfx_popfree_head : word) with (Z_to_bv 64 (0x36cd0 + D_150) : word) in Hms by img_refl.
eapply (SRr_msteps tfxsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. img_exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
set (bs := pf_bytes cst sz (Z.to_nat (cnt - 0))) in *.
assert (Hbl : Z.of_nat (length bs) = 4 * cnt) by (img_try ((subst bs; cbv beta); rewrite pf_bytes_length; img_lia)).
img_change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 (tfx_popfree_head + 32)) (wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs) (seg_rom tfxsegs)))
with (mkst regs' (Z_to_bv 64 (tfx_popfree_head + 32)) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs)) (seg_rom tfxsegs)).
replace (Z_to_bv 64 (tfx_popfree_head + 32) : word) with (Z_to_bv 64 (0x36cf0 + D_150) : word) by img_refl.
set (m1 := wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. img_exact Em. }
assert (FR1 : forall x : word, ~ (e - 4 * cnt <= bv_unsigned x < e) -> m1 x = mr x).
{ intros x Hx. (subst m1; cbv beta). destruct (Z_lt_le_dec (bv_unsigned x) (e - 4 * cnt)).
- img_apply wbytes_below; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia.
- img_apply wbytes_above; rewrite unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)); img_lia. }
assert (GR1 : mem_grows mr m1) by (img_try ((subst m1; cbv beta); img_apply wbytes_grows)).
img_apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
img_apply (st_ok_after_stretch tfxsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) (0x36cf0 + D_150) [10; 12; 14; 15]%bv HS Hrv);
[ img_try (unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; img_refl)
| img_try (img_exact (proj1 (st_ok_mem_ok tfxsegs E ss _ HS))) | img_try (img_exact Hnc) | img_try (img_exact Hm') | img_try (img_apply submem_refl) | img_refl | img_refl | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
img_apply Rfr; intros ->; img_apply Hr; tauto.
+ img_apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [img_refl|].
rewrite unsigned_lit_small by (img_try (img_exact (Hext64 r a Hr Ha))). destruct (Hext r Hr) as [X|[X|X]]; img_lia.
* intros a Ha Hw. img_apply (writable_at_grows tfxsegs mr m1 a GR1 Hw).
- intros x Hx. (subst m1full; cbv beta). unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [img_refl|].
rewrite (FR1 x Hx). (subst mr; cbv beta). unfold mrestrict. rewrite Hh. img_refl.
- intros a [Hh [b Hb]]. split; [img_try (img_exact Hh)|]. (subst m1full; cbv beta). unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (img_try (img_apply GR1; (subst mr; cbv beta); unfold mrestrict; rewrite Hh, Hb; discriminate)).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [img_try (exists b'; img_refl) | img_try (exfalso; img_apply NN; img_refl)].
- intros i Hi. rewrite Hm1. intros t Ht. (subst m1; cbv beta). unfold mbyte.
rewrite (wbytes_inside bs mr (Z_to_bv 64 (e - 4 * cnt)) (Z_to_bv 64 (e - 4 - 4 * i + Z.of_nat t)))
by (img_try (rewrite !unsigned_lit_small by (unfold TFX_IMG_END in *; img_lia); img_lia)).
rewrite !unsigned_lit_small by (img_try (unfold TFX_IMG_END in *; img_lia)). f_equal.
replace (Z.to_nat (e - 4 - 4 * i + Z.of_nat t - (e - 4 * cnt))) with (Z.to_nat (4 * (cnt - 1 - i)) + t)%nat by img_lia.
(subst bs; cbv beta). rewrite (pf_bytes_nth cst sz (Z.to_nat (cnt - 0)) (cnt - 1 - i) t) by img_lia.
replace (Z.of_nat (Z.to_nat (cnt - 0)) - 1 - (cnt - 1 - i)) with i by img_lia.
rewrite nth_Z_to_le_bytes4 by img_exact Ht. symmetry. img_apply le_byte_small; [|img_try (img_exact Ht)].
img_change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). split; [img_try (img_apply Z.div_pos; nia)|]. img_apply Z.div_lt_upper_bound; [img_lia|]. nia.
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
Hypothesis HAR : AR tfxsegs B ly S W mem0 md0.
Lemma Pr_is : Pr = ly_T ly + t_cache + 80 * c. Proof. img_refl. Qed.
Lemma RGv_is : RGv = ly_space ly + kRegionInfoOff + 128 * c. Proof. img_refl. Qed.
Lemma FAv_is : FAv = fa_base ly c.
Proof. clear - HcR. unfold FAv, RBv, fa_base, SB. rewrite region_off_eq by img_lia. img_refl. Qed.
Lemma RBv_is : RBv = region_base ly c.
Proof. clear - HcR. unfold RBv, region_base, SB. rewrite region_off_eq by img_lia. img_refl. Qed.
End g.
End f.
