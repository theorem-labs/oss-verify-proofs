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
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB1q AF0l AF0m AF0x AFl0 AFl1.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1w AE3d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YE06.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB19 AF0n.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK0u.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFhy AFis AFkp AFk6 AFhz AFk8.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YFk4.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AFk3.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Ltac zcanon_simp :=
repeat match goal with
| |- context [zcanon ?x] =>
lazymatch x with
| context [zcanon _] => fail
| context [Z.shiftl _ _] => fail | context [Z.shiftr _ _] => fail | context [Z.land _ _] => fail
| context [Z.lor _ _] => fail | context [Z.lxor _ _] => fail
| _ => rewrite (zcanon_id x) by (unfold M64; lia)
end
end.
Ltac is_zlit a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac land_lits :=
repeat match goal with
| |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
end.
Ltac zlia := first [ lia | ceil; unfold zone3, zone3cases, off_img, in_app, app_addr, in_band_rw, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kNodesBlockSize, kStoreBlockSize, kPrimResvSize, kSpaceSize in *; lia ].
Ltac numconst := ceil; unfold zone3, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, TFIB_IMG_LO, kLowShadowBeg,
t_cache, t_unwinding, t_stats, ASTACK, TFIB_IMG_END, UNW_STK, BST_SIZE, DEP_STK, kFreeArrayOffset, kRegionInfoOff, kFreeArrayMax, kFreeArrayMapSize, kUserMapSize, RSTACK, kMaxSize in *.
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
Ltac clear_all := repeat match goal with H : _ |- _ => clear H end.
Section g.
Variables (W : world tfibsegs) (ly : alayout).
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
Lemma EaT : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaSB : ew E0 34 = w64 SB. Proof. reflexivity. Qed.
Lemma EaTOP : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.
Lemma EaCL : ew E0 36 = w64 c. Proof. reflexivity. Qed.
Lemma EaP : ew E0 37 = w64 Pr. Proof. reflexivity. Qed.
Lemma EaMAX : ew E0 38 = w64 maxc. Proof. reflexivity. Qed.
Lemma EaN : ew E0 39 = w64 n. Proof. reflexivity. Qed.
Lemma EaCSZ : ew E0 40 = w64 csz. Proof. reflexivity. Qed.
Lemma EaRG : ew E0 41 = w64 RGv. Proof. reflexivity. Qed.
Lemma EaRB : ew E0 42 = w64 RBv. Proof. reflexivity. Qed.
Lemma EaFA : ew E0 43 = w64 FAv. Proof. reflexivity. Qed.
Lemma EaNF : ew E0 44 = w64 nf. Proof. reflexivity. Qed.
Lemma EaMF : ew E0 45 = w64 mf. Proof. reflexivity. Qed.
Lemma EaAU : ew E0 46 = w64 au. Proof. reflexivity. Qed.
Lemma EaMU : ew E0 47 = w64 mu. Proof. reflexivity. Qed.
Lemma EaSHB : ew E0 48 = w64 SHBv. Proof. reflexivity. Qed.
Lemma EaNEED : ew E0 55 = w64 need. Proof. reflexivity. Qed.
Lemma EaTOT : ew E0 56 = w64 tot. Proof. reflexivity. Qed.
Lemma EaADR : ew E0 57 = w64 adr. Proof. reflexivity. Qed.
Lemma EaSHA : ew E0 58 = w64 sha. Proof. reflexivity. Qed.
Hypothesis IMG : img_cover ly.
Lemma EaMU2 : ew E0 59 = w64 mu2. Proof. reflexivity. Qed.
Lemma EaNCe : ew E0 60 = w64 nce. Proof. reflexivity. Qed.
Lemma EaNCg : ew E0 61 = w64 ncg. Proof. reflexivity. Qed.
Lemma EaNFe : ew E0 62 = w64 nfe. Proof. reflexivity. Qed.
Lemma EaNFg : ew E0 63 = w64 nfg. Proof. reflexivity. Qed.
Lemma EaFADR : ew E0 64 = w64 fadr. Proof. reflexivity. Qed.
Lemma EaSHF : ew E0 65 = w64 shf. Proof. reflexivity. Qed.
Lemma EaMF2 : ew E0 66 = w64 mf2. Proof. reflexivity. Qed.
Lemma EaAUe : ew E0 67 = w64 aue. Proof. reflexivity. Qed.
Lemma EaAUg : ew E0 68 = w64 aug. Proof. reflexivity. Qed.
Lemma Er (k : nat) (r : bv 5) : Z.of_nat k = bv_unsigned r -> ew E0 k = getr regs0 r.
Proof. intros Hk. exact (ew_Ereg_nat regs0 XWR k r Hk). Qed.
Lemma E2 : ew E0 2 = getr regs0 2. Proof. exact (Er 2 2%bv eq_refl). Qed.
Lemma E1 : ew E0 1 = getr regs0 1. Proof. exact (Er 1 1%bv eq_refl). Qed.
Lemma E8 : ew E0 8 = getr regs0 8. Proof. exact (Er 8 8%bv eq_refl). Qed.
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
Hypothesis Htp : getr regs0 4 = w64 TFIB_TP.
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
pose proof (class_ok c ltac:(lia)) as (K1 & K2 & K3 & K4 & K5 & K6).
set (q := Z.max 1 (Z.min 8 (1024 / class_size c))).
assert (Q : 1 <= q <= 8) by (subst q; lia).
assert (M : maxc = q * 2) by (rewrite Hmax; unfold max_cached; subst q; lia).
assert (N : n = q) by (rewrite Hn, M, Z_div_mult by lia; reflexivity).
apply Z.mod_divide in K2 as [r Hr]; [|lia].
split; [lia|]. split; [rewrite M; apply Z_mod_mult|]. split; [lia|]. split; [rewrite Hcsz; lia|].
rewrite Hcsz, Hr. replace (r * 32) with ((r * 2) * 16) by lia. apply Z_mod_mult.
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
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) IC (pairwise_ij _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
clear HA HD. split; [exact ZT|]. clear ZT.
unfold in_high, in_app, zdisjoint, kLowShadowBeg, kHighMemBeg in *. cbn [fst snd] in *. unfold T in *.
pose proof ASAN_CEIL_range as [CR _].
split; [clear - IT CR; lia|]. do 4 (split; [clear TS PS ZC; lia|]).
split; [exact ZC|]. split; [clear - IC CR; lia|]. split; [exact HAL|].
intros a Ha; split; intros Hx; [clear PS | clear TS]; clear ZC; lia.
Qed.
Lemma off_T : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 high_factsR) Ha). Qed.
Lemma off_C : forall a, ly_C ly <= a < ly_C ly + 256 -> off_img a.
Proof. intros a Ha. pose proof high_factsR as (_ & _ & _ & _ & _ & _ & F7 & _). exact (zone3_off_img _ _ a F7 Ha). Qed.
Ltac off_by tac :=
first [ apply off_img_high; tac
| apply off_T; unfold kThreadObjSize; tac
| apply off_C; tac
| unfold off_img; unfold TFIB_IMG_LO; unfold TFIB_IMG_END; tac ].
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
apply Z.mod_divide in F9 as [qs Hqs]; [|lia]. apply Z.mod_divide in TAL as [qt Hqt]; [|lia].
unfold SRCv, DSTv. unfold FAv. unfold Pr, RGv, RBv. unfold T, SB in *.
ceil; unfold zone3, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, t_cache, kRegionInfoOff, kFreeArrayOffset, kFreeArrayMax in *.
assert (M1 : (ly_T ly + 208 + 80 * c) mod 16 = 0) by (rewrite Hqt; apply Z.mod_divide; [lia|]; exists (qt * 256 + 13 + 5 * c); lia).
assert (M2 : (ly_space ly + 2 ^ 37 + 128 * c) mod 128 = 0) by (rewrite Hqs; apply Z.mod_divide; [lia|]; exists (qs * 512 + 2 ^ 30 + c); lia).
assert (M3 : (ly_space ly + c * 2 ^ 32) mod 65536 = 0) by (rewrite Hqs; apply Z.mod_divide; [lia|]; exists (qs + c * 65536); lia).
assert (M4 : (ly_space ly + c * 2 ^ 32 + 3758096384) mod 4096 = 0) by (rewrite Hqs; apply Z.mod_divide; [lia|]; exists (qs * 16 + c * 2 ^ 20 + 917504); lia).
repeat split; try assumption; lia.
Qed.
Definition WINR0 (a : Z) : Prop :=
(sp0 - RSTACK <= a < sp0) \/ (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/
(T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888).
Definition WINR (a : Z) : Prop := WINR0 a \/ (DSTv <= a < DSTv + 4 * n).
Lemma WINR0_WINR : forall a, WINR0 a -> WINR a.
Proof. intros a H. left. exact H. Qed.
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
- apply Nat.eqb_eq in H1. subst. lia.
- lia.
Qed.
Lemma WSKELR_WINR0 : forall (E : env) a t,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In t WSKELR ->
base_val E (fst (fst t)) + snd (fst t) <= a < base_val E (fst (fst t)) + snd t -> WINR0 a.
Proof. clear3.
intros E a t HE Hin Hr. unfold WSKELR in Hin. cbn [In] in Hin. unfold WINR0.
repeat match type of Hin with _ \/ _ => destruct Hin as [<-|Hin] | False => destruct Hin end;
cbn [fst snd base_val] in Hr; unfold rP, rRG, rT in Hr; rewrite HE in Hr by (unfold aHAV3; lia);
rewrite ?E2, ?EaT, ?EaP, ?EaRG in Hr; unfold w64 in Hr;
pose proof derived_rangesR as DR; pose proof high_factsR as HF; ceil; unfold kHighMemBeg, ASAN_CEIL, kThreadObjSize, kSpaceSize in DR, HF;
rewrite ?unsigned_lit_small in Hr by lia; unfold sp0 in *; lia.
Qed.
Lemma windows_WINR0 : forall (E : env) rs a,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
in_wrange E rs a -> WINR0 a.
Proof. clear3.
intros E rs a HE Hb Hw. destruct (in_wrange_windows E rs a Hw) as (b & lo & hi & Hin & Hr).
pose proof (proj1 (forallb_forall _ _) Hb _ Hin) as Ht. cbn beta in Ht. apply Bool.orb_prop in Ht as [Ht|Ht].
- apply existsb_exists in Ht as (u & Hinu & Hsub). exact (WSKELR_WINR0 E a u HE Hinu (win_sub_sound E a _ u Hsub Hr)).
- cbn [fst snd] in Ht. apply Z.leb_le in Ht. lia.
Qed.
Lemma frame_WINR0 : forall (E : env) rs (m m' : word -> option byte),
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ WINR0 (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros E rs m m' HE Hb HF x Hx. apply HF. intros Hw. apply Hx. exact (windows_WINR0 E rs _ HE Hb Hw). Qed.
Lemma frame_X : forall (X : Z -> Prop) (E : env) rs (m m' : word -> option byte),
(forall a, WINR0 a -> X a) ->
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows rs) = true ->
frame_of E rs m m' -> forall x : word, ~ X (bv_unsigned x) -> m' x = m x.
Proof. clear3. intros X E rs m m' HX HE Hb HF x Hx. apply (frame_WINR0 E rs m m'); [exact HE | exact Hb | exact HF |]. intros Hw. apply Hx, HX, Hw. Qed.
Ltac frame_acc3 HX HE :=
match goal with
| MEQ : (forall x : word, ~ ?X (bv_unsigned x) -> ?m1 x = ?mb x), HFx : frame_of ?E ?rs ?m1 ?m2 |- _ =>
let MEQ' := fresh "MEQ" in
assert (MEQ' : forall x : word, ~ X (bv_unsigned x) -> m2 x = mb x)
by (intros x Hx; transitivity (m1 x); [exact (frame_X X E rs m1 m2 HX HE ltac:(vm_compute; reflexivity) HFx x Hx) | exact (MEQ x Hx)]);
clear MEQ HFx; rename MEQ' into MEQ
end.
Definition W_DST (a : Z) : Prop := DSTv <= a < DSTv + 4 * n.
Definition W_FE (nf' : Z) (a : Z) : Prop := FAv + 4 * nf <= a < FAv + 4 * nf'.
Definition W_UW (a : Z) : Prop := adr <= a < adr + kUserMapSize.
Definition W_USH (a : Z) : Prop := sha <= a < sha + kUserMapSize / 8.
Definition W_FW (a : Z) : Prop := fadr <= a < fadr + kFreeArrayMapSize.
Definition W_FSH (a : Z) : Prop := shf <= a < shf + kFreeArrayMapSize / 8.
Definition at_R3 (Wx : world tfibsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree aHAV3 E0 E' /\
st_ok tfibsegs E' ss (restrict (w_H Wx) ms) /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_N3 (Wx : world tfibsegs) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (ss : sstate) (W' : world tfibsegs) (c' : config) : Prop :=
W' = Wx /\ exists ms mat (E' : env),
c' = mkCfg ms (with_vm_backing (m_vm_lazy md) mat md) /\
env_agree aHAV3 E0 E' /\
st_ok_ecall tfibsegs E' ss (restrict (w_H Wx) ms) /\ ss_resv ss = None /\
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) /\
P (ms_mem ms).
Definition at_RET3 (Wx : world tfibsegs) (v : Z) (md : Model) (X : Z -> Prop) (P : (word -> option byte) -> Prop) (W' : world tfibsegs) (c' : config) : Prop :=
W' = Wx /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
getr regs' 10 = Z_to_bv 64 v /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(forall x : word, ~ X (bv_unsigned x) -> mem' x = mem0 x) /\
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) mem' a) /\
P mem'.
Definition P_cells (Wx : world tfibsegs) (cnt nfv mfv auv muv : Z) (m' : word -> option byte) : Prop :=
let m := mrestrict (w_H Wx) m' in
(forall a, (Pr <= a < Pr + 16) \/ (RGv <= a < RGv + 128) \/ (T + 2768 <= a < T + 2800) \/ (T + 2872 <= a < T + 2888) -> apresent (w_H Wx) m' a) /\
val_mem tfibsegs m Pr 4 cnt /\ val_mem tfibsegs m (Pr + 4) 4 maxc /\ val_mem tfibsegs m (Pr + 8) 8 csz /\
val_mem tfibsegs m RGv 8 0 /\ val_mem tfibsegs m (RGv + 8) 8 0 /\ val_mem tfibsegs m (RGv + 16) 8 nfv /\
val_mem tfibsegs m (RGv + 24) 8 mfv /\ val_mem tfibsegs m (RGv + 32) 8 auv /\ val_mem tfibsegs m (RGv + 40) 8 0 /\
val_mem tfibsegs m (RGv + 48) 8 muv /\ val_mem tfibsegs m (RGv + 56) 8 0 /\ val_mem tfibsegs m (RGv + 68) 1 0.
Fixpoint chunk_index (cs : list YP09.chunk) (off : Z) : nat :=
match cs with [] => 0%nat | ch :: t => if YP09.c_off ch =? off then 0%nat else Datatypes.S (chunk_index t off) end.
Definition pstable (P : (word -> option byte) -> Prop) : Prop :=
forall m m' : word -> option byte, (forall x : word, ~ WINR0 (bv_unsigned x) -> m' x = m x) -> P m -> P m'.
Lemma all_disjoint_of_forall : forall (E : env) r rs,
(forall r', In r' rs -> extent_disjoint E r r') -> all_disjoint E r rs.
Proof. clear3. intros E r rs H. induction rs as [|r' rs IH]; cbn; [exact I|]. split; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx]. Qed.
Lemma kept_of_frame : forall (Wx : world tfibsegs) (E : env) (m m1 : word -> option byte) (X : Z -> Prop) r,
(forall x : word, ~ X (bv_unsigned x) -> m1 x = m x) ->
(forall a, apresent (w_H Wx) m a -> apresent (w_H Wx) m1 a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
~ X a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
region_kept tfibsegs E (mrestrict (w_H Wx) m) (mrestrict (w_H Wx) m1) r.
Proof. clear3.
intros Wx E m m1 X r Hfr Hpr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. pose proof (Hwin a Ha : off_img a) as Hh. apply apresent_writable_off; [exact Hh|]. apply Hpr. apply writable_off_apresent; [exact Hh | exact Hw].
Qed.
Lemma kept_of_frame2 : forall (Hh : word -> bool) (E : env) (m m1 : word -> option byte) (R : Z -> Prop) r,
(forall x : word, ~ R (bv_unsigned x) -> m1 x = m x) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
region_kept tfibsegs E (mrestrict Hh m) (mrestrict Hh m1) r.
Proof. clear3.
intros Hh E m m1 R r Hfr Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Hno Hr]. apply mbyte_mrestrict_same. apply Hfr. rewrite unsigned_lit_small by lia. exact Hno.
- intros a Ha Hw. destruct (Hwin a Ha) as [Hno Hr]. apply (writable_at_eq tfibsegs (mrestrict Hh m)); [|exact Hw].
unfold mrestrict. rewrite (Hfr (Z_to_bv 64 a)) by (rewrite unsigned_lit_small by lia; exact Hno). reflexivity.
Qed.
Definition SKEL_TAILR : list (option nat * Z * Z * Z * Z) := skeleton (tl REG0R3).
Definition RFACTSR (lo hi wlo whi : Z) : Prop :=
(hi <= sp0 - RSTACK \/ sp0 <= lo) /\ 0 <= lo /\ hi <= 2 ^ 64 /\
(whi <= wlo \/ (TFIB_IMG_END <= wlo /\ whi <= 2 ^ 64) \/ (0 <= wlo /\ whi <= TFIB_IMG_LO)) /\
(hi <= DSTv \/ DSTv + 32 <= lo).
Lemma stack_ivsR :
(T + kThreadObjSize <= sp0 - RSTACK \/ sp0 <= T) /\ (ly_prim ly + kPrimResvSize <= sp0 - RSTACK \/ sp0 <= ly_prim ly) /\
(ly_C ly + 256 <= sp0 - RSTACK \/ sp0 <= ly_C ly) /\ kHighMemBeg <= sp0 - RSTACK /\ sp0 <= kHighMemEnd.
Proof. clear3.
pose proof (lo_disj ly LY) as HD. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (pairwise_ij _ _ 2 5 _ _ HD eq_refl eq_refl) as TS. pose proof (pairwise_ij _ _ 0 7 _ _ HD eq_refl eq_refl) as PS.
pose proof (pairwise_ij _ _ 6 1 _ _ HD eq_refl eq_refl) as CS. clear HD.
destruct Hsp as (S1 & S3 & S4). unfold zdisjoint, kThreadObjSize, RSTACK, kPrimResvSize in *. cbn [fst snd] in *. unfold T.
split; [clear PS CS; lia|]. split; [clear TS CS; lia|]. split; [clear TS PS; lia|]. clear TS PS CS. unfold kHighMemBeg, kHighMemEnd in *. lia.
Qed.
Lemma zone_litR : forall lo hi wlo whi, TFIB_IMG_LO <= lo -> hi <= TFIB_IMG_END -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof stack_ivsR as (_ & _ & _ & S1 & _). pose proof high_factsR as (F1 & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR S1 F1 HcR. numconst. unfold zone3cases, DSTv, Pr, T in *. numconst. lia.
Qed.
Lemma zone_TR : forall lo hi wlo whi,
T <= lo -> hi <= T + kThreadObjSize -> (whi <= wlo \/ (T <= wlo /\ whi <= T + kThreadObjSize)) -> (hi <= DSTv \/ DSTv + 32 <= lo) ->
RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2 Hz3. pose proof high_factsR as (F1 & F2 & _). pose proof stack_ivsR as (DT & _).
unfold RFACTSR. clear - Hz0 Hz1 Hz2 Hz3 F1 F2 DT. numconst. unfold zone3cases in *. numconst. unfold T in *. lia.
Qed.
Lemma zone_CR : forall lo hi wlo whi, ly_C ly <= lo -> hi <= ly_C ly + 256 -> whi <= wlo -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof stack_ivsR as (_ & _ & DC & _).
pose proof (pairwise_ij _ _ 2 3 _ _ (lo_disj ly LY) eq_refl eq_refl) as CT. unfold zdisjoint in CT. cbn [fst snd] in CT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F7 F8 DC CT. numconst. unfold zone3cases in *. numconst. unfold T in *. lia.
Qed.
Lemma zone_RGR : forall lo hi wlo whi,
RGv <= lo -> hi <= RGv + 128 -> (whi <= wlo \/ (RGv <= wlo /\ whi <= RGv + 128)) -> RFACTSR lo hi wlo whi.
Proof. clear3.
intros lo hi wlo whi Hz0 Hz1 Hz2. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (_ & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold RFACTSR. clear - Hz0 Hz1 Hz2 DR F1 F2 F3 F4 F5 F6 DP PT. numconst. unfold zone3cases in *. numconst. unfold T, SB in *. lia.
Qed.
Lemma slots_not_WINR0 : forall a, DSTv <= a < DSTv + 64 -> ~ WINR0 a.
Proof. clear3.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; lia.
Qed.
Lemma fa_not_WINR0 : forall a, FAv <= a < FAv + 2 ^ 29 -> ~ WINR0 a.
Proof. clear3.
intros a Ha Hw. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
pose proof stack_ivsR as (DT & DP & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. unfold zdisjoint in PT. cbn [fst snd] in PT.
unfold WINR0 in Hw. clear - Ha Hw DR F1 F2 F3 F4 F5 F6 DT DP PT. numconst. unfold T, SB in *. destruct Hw as [Hw|[Hw|[Hw|[Hw|Hw]]]]; lia.
Qed.
Lemma tail_ext_okR : forall (E : env) r,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILR ->
let b := base_val E (YP09.r_base r) in
RFACTSR (b + YP09.r_lo r) (b + YP09.r_hi r) (b + YP09.r_wlo r) (b + YP09.r_whi r).
Proof. clear3.
intros E r HE Hin. pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
let sk := eval vm_compute in SKEL_TAILR in change SKEL_TAILR with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG, ?EaSB, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T, SB, SHBv in *; lia).
all: lazymatch goal with |- RFACTSR _ _ _ _ => idtac end.
all: first [ apply zone_litR; clear - DR; numconst; unfold TFIB_TSD, TFIB_TP; lia
| apply zone_RGR; clear - DR; numconst; lia
| apply zone_TR; clear - DR F1 F2; numconst; unfold T in *; lia
| apply zone_CR; clear - DR F7 F8; numconst; lia ].
Qed.
Variables (mat0 : list word) (msJ : machine_state).
Let cfg0 : config := mkCfg msJ (with_vm_backing (m_vm_lazy md0) mat0 md0).
Hypothesis SEEDJ : at_R3 W md0 WINR0 (fun _ => True) R3_J W cfg0.
Hypothesis Hpres0R : forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H W) mem0 a.
Hypothesis HslotPres : forall a, DSTv <= a < DSTv + 64 -> apresent (w_H W) mem0 a.
Hypothesis HfaPres : forall a, FAv <= a < FAv + mf -> apresent (w_H W) mem0 a.
Lemma rdn_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
exists bs, rdn tfibsegs m (Z_to_bv 64 a) nn = Some bs /\ length bs = nn.
Proof. clear3.
intros m nn. induction nn as [|nn IH]; intros a Hp Ha Hnw.
- exists []. split; reflexivity.
- destruct (Hp 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
destruct (IH (a + 1)) as (bs & Hbs & Hlen); [intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hp; lia | lia | lia |].
exists (b :: bs). split; [|cbn; lia]. cbn [rdn]. rewrite Hb.
replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)); [rewrite Hbs; reflexivity|].
apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_unsigned 1) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma store_ok_of_presentR : forall (m : word -> option byte) nn a,
(forall i, 0 <= i < Z.of_nat nn -> exists b, m (Z_to_bv 64 (a + i)) = Some b) -> 0 <= a -> a + Z.of_nat nn <= 2 ^ 64 ->
store_ok tfibsegs m (Z_to_bv 64 a) nn = true.
Proof. clear3.
intros m nn a Hp Ha Hnw. destruct nn as [|n']; [reflexivity|].
apply store_ok_of_all; [rewrite unsigned_lit_small by lia; lia|].
intros x Hx. rewrite unsigned_lit_small in Hx by lia.
destruct (Hp (bv_unsigned x - a) ltac:(lia)) as [b Hb]. replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in Hb by lia.
rewrite Z_to_bv_bv_unsigned in Hb. unfold wview. rewrite Hb. discriminate.
Qed.
Lemma cpy4_stretch : forall (Wx : world tfibsegs) (k : nat) (E : env) ss ms md (d src len : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = 0x36378 ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 20 = Z_to_bv 64 src -> getr (ms_regs ms) 13 = Z_to_bv 64 d -> getr (ms_regs ms) 11 = Z_to_bv 64 (d + len) ->
4 <= len -> len mod 4 = 0 -> 0 <= d -> d + len < 2 ^ 64 -> 0 <= src -> src + len < 2 ^ 64 ->
(d + len <= src \/ src + len <= d) ->
(forall a, d <= a < d + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall a, src <= a < src + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [12; 13; 20]%bv))
(ss_after_stretch ss (ss_mem ss) k [12; 13; 20]%bv 0x3638c)
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 0x3638c) mem' (seg_rom tfibsegs))) ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall j, 0 <= j < len -> mem' (w64 (d + j)) = ms_mem ms (w64 (src + j))) ->
SRr tfibsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 0x3638c) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md d src len Q HS Hrv Hpc Hat Hnc H20 H13 H11 Hlen Hl4 Hd Hdl Hs Hsl Hdisj Hpd Hps Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
destruct (rdn_of_presentR mr (Z.to_nat len) src) as (bs & Hbs & Hbl);
[ intros i Hi; destruct (Hps (src + i) ltac:(lia)) as [Hh [b Hb]]; exists b; unfold mr, mrestrict; rewrite Hh; exact Hb
| unfold TFIB_IMG_END in *; lia | lia |].
assert (HOK : mcH mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs).
{ split; [unfold TFIB_IMG_END in *; lia | lia | rewrite Hbl; exact Hbs | | | |]; rewrite ?unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); try lia.
rewrite Hbl. apply store_ok_of_presentR; [|unfold TFIB_IMG_END in *; lia|lia].
intros i Hi. destruct (Hpd (d + i) ltac:(lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. exact Hb. }
destruct (tfib_cpy4_run mr (Z_to_bv 64 d) (Z_to_bv 64 src) len bs (seg_rom tfibsegs) (ms_regs ms) HOK Hl4 Hlen H20 H13
ltac:(rewrite H11; unfold at_; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); reflexivity))
as (regs' & Hms & R20 & R13 & R11 & Rfr).
replace (Z_to_bv 64 222072 : word) with (0x36378%bv : word) by (apply bv_eq; reflexivity).
eapply (SRr_msteps tfibsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (0x3638c : word) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (0x3638c : word) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); rewrite Hbl; lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
replace (0x3638c%bv : word) with (Z_to_bv 64 0x3638c : word) by (apply bv_eq; reflexivity).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) 0x3638c [12; 13; 20]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
apply Rfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros j Hj. destruct (Hpd (d + j) ltac:(lia)) as [Hh _]. destruct (Hps (src + j) ltac:(lia)) as [Hh' [b' Hb']].
subst m1full. unfold munrestrict, w64. rewrite Hh. subst m1.
rewrite (wbytes_inside bs mr (Z_to_bv 64 d) (Z_to_bv 64 (d + j))) by (rewrite ?unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); rewrite ?Hbl; lia).
rewrite !unsigned_lit_small by (unfold TFIB_IMG_END in *; lia). replace (Z.to_nat (d + j - d)) with (Z.to_nat j) by (f_equal; lia).
pose proof (rdn_nth tfibsegs mr (Z.to_nat len) (Z_to_bv 64 src) bs (Z.to_nat j) Hbs ltac:(lia)) as R1.
replace (Z_to_bv 64 src + nat_to_word (Z.to_nat j))%bv with (Z_to_bv 64 (src + j)) in R1
by (apply bv_eq; rewrite bv_add_unsigned; unfold nat_to_word; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Z2Nat.id, <- Z.add_mod, !Z.mod_small by (unfold TFIB_IMG_END in *; lia); reflexivity).
cbn [rdn] in R1. subst mr. unfold mrestrict in R1. rewrite Hh', Hb' in R1. cbn in R1. injection R1 as <-. rewrite Hb'. reflexivity.
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
assert (NC8 : n * csz <= kMaxSize) by (rewrite Hn; exact CM).
assert (NE1 : 1 <= need) by (clear - Hneed Hnlt; lia). assert (NE2 : need <= 8) by (clear - Hneed N0 K3; lia).
assert (NCSZ : need * csz <= kMaxSize) by (rewrite Hneed; clear - NC8 N0 Hnlt K3 K4; unfold kMaxSize in *; nia).
assert (T16 : 16 <= tot) by (rewrite Htot; clear - NE1 K4 U0; nia).
pose proof (Z.div_mod (mu - au) csz ltac:(clear - K4; lia)) as D1. pose proof (Z.mod_pos_bound (mu - au) csz ltac:(clear - K4; lia)) as B1.
pose proof (Z.div_mod (mu2 - au) csz ltac:(clear - K4; lia)) as D2. pose proof (Z.mod_pos_bound (mu2 - au) csz ltac:(clear - K4; lia)) as B2.
assert (P1 : 0 <= nce) by (rewrite Hnce; apply Z.div_pos; [clear - U0 U1; lia | clear - K4; lia]).
assert (P2 : 0 <= ncg) by (rewrite Hncg, Hmu2; apply Z.div_pos; [clear - U0 U1; unfold kUserMapSize; lia | clear - K4; lia]).
assert (E1a : nce * csz <= mu - au) by (rewrite Hnce; clear - D1 B1 K4; nia). assert (E1b : mu - au < nce * csz + csz) by (rewrite Hnce; clear - D1 B1 K4; nia).
assert (E2a : ncg * csz <= mu2 - au) by (rewrite Hncg; clear - D2 B2 K4; nia). assert (E2b : mu2 - au < ncg * csz + csz) by (rewrite Hncg; clear - D2 B2 K4; nia).
assert (S1 : nce < 2 ^ 16) by (clear - E1a Hcarved K4 P1; unfold kUserMapSize, kMaxSize in *; nia).
assert (S2 : ncg < 2 ^ 16) by (pose proof E2a as E; rewrite Hmu2 in E; clear - E Hcarved K4 P2; unfold kUserMapSize, kMaxSize in *; nia).
assert (RBAL : RBv mod 65536 = 0) by (clear - DR; tauto).
pose proof RBAL as RBAL'. apply Z.mod_divide in RBAL' as [qb Hqb]; [|clear; lia].
pose proof U3 as U3'. apply Z.mod_divide in U3' as [qu Hqu]; [|clear; unfold kUserMapSize; lia].
pose proof M2 as M2'. apply Z.mod_divide in M2' as [qm Hqm]; [|clear; unfold kFreeArrayMapSize; lia].
assert (AAL : adr mod 65536 = 0) by (rewrite Hadr, Hqb, Hqu; apply Z.mod_divide; [clear; lia|]; exists (qb + 4 * qu); unfold kUserMapSize; clear; lia).
assert (FAE : FAv = RBv + kFreeArrayOffset) by (clear - DR; tauto).
assert (FAL : FAv mod 65536 = 0).
{ rewrite FAE, Hqb. apply Z.mod_divide; [clear; lia|]. exists (qb + 57344). unfold kFreeArrayOffset. clear; lia. }
assert (FDAL : fadr mod 65536 = 0).
{ rewrite Hfadr, FAE, Hqb, Hqm. apply Z.mod_divide; [clear; lia|]. exists (qb + 57344 + 4 * qm). unfold kFreeArrayOffset, kFreeArrayMapSize. clear; lia. }
assert (SHAL : forall x, x mod 65536 = 0 -> (SHBv + x / 8) mod 4096 = 0).
{ clear. intros x Hx. apply Z.mod_divide in Hx as [q Hq]; [|lia]. rewrite Hq. replace (q * 65536) with (q * 8192 * 8) by lia. rewrite Z.div_mul by lia.
apply Z.mod_divide; [lia|]. exists (524280 + 2 * q). unfold SHBv. lia. }
pose proof K5 as K5'. apply Z.mod_divide in K5' as [qc Hqc]; [|clear; lia]. pose proof U4 as U4'. apply Z.mod_divide in U4' as [qa Hqa]; [|clear; lia].
assert (AUE16 : aue mod 16 = 0) by (rewrite Haue, Hqa, Hqc; apply Z.mod_divide; [clear; lia|]; exists (qa + nce * qc); clear; lia).
assert (AUG16 : aug mod 16 = 0) by (rewrite Haug, Hqa, Hqc; apply Z.mod_divide; [clear; lia|]; exists (qa + ncg * qc); clear; lia).
pose proof (SHAL adr AAL) as SAL. pose proof (SHAL fadr FDAL) as SFL. rewrite <- Hsha in SAL. rewrite <- Hshf in SFL.
assert (A1 : kHighMemBeg <= adr) by (rewrite Hadr; clear - DR U0 U1; numconst; lia).
assert (A2 : RBv <= adr) by (rewrite Hadr; clear - U0 U1; lia).
assert (A3 : adr + kUserMapSize <= RBv + 2 ^ 32) by (rewrite Hadr; clear - U0 U1 U2; numconst; lia).
assert (SH1 : 2201439137792 <= sha) by (rewrite Hsha; pose proof (Z.div_le_mono kHighMemBeg adr 8 ltac:(clear; lia) A1) as X; clear - X; unfold SHBv, kHighMemBeg in *; change (17594333495296 / 8) with 2199291686912 in X; lia).
assert (ACE : adr <= ASAN_CEIL) by (clear - DR A3 U2; numconst; lia).
assert (SH2 : sha + 32768 <= 17594332479488).
{ rewrite Hsha. ceil. pose proof (Z.div_le_mono adr 140737479966720 8 ltac:(clear; lia) ltac:(clear - ACE CR0; unfold ASAN_CEIL in *; lia)) as X. clear - X. unfold SHBv. change (140737479966720 / 8) with 17592184995840 in X. lia. }
assert (F1 : kHighMemBeg <= fadr) by (rewrite Hfadr, FAE; clear - DR M0; numconst; lia).
assert (F2 : fadr + kFreeArrayMapSize <= RBv + 2 ^ 32 + kFreeArrayMapSize) by (rewrite Hfadr, FAE; clear - M0 M1; numconst; lia).
assert (FCE : fadr <= ASAN_CEIL) by (clear - DR F2; numconst; lia).
assert (SF1 : 2201439137792 <= shf) by (rewrite Hshf; pose proof (Z.div_le_mono kHighMemBeg fadr 8 ltac:(clear; lia) F1) as X; clear - X; unfold SHBv, kHighMemBeg in *; change (17594333495296 / 8) with 2199291686912 in X; lia).
assert (SF2 : shf + 32768 <= 17594332479488).
{ rewrite Hshf. ceil. pose proof (Z.div_le_mono fadr 140737479966720 8 ltac:(clear; lia) ltac:(clear - FCE CR0; unfold ASAN_CEIL in *; lia)) as X. clear - X. unfold SHBv. change (140737479966720 / 8) with 17592184995840 in X. lia. }
repeat split; assumption.
Qed.
Definition RFACTS3 (lo hi wlo whi : Z) : Prop :=
RFACTSR lo hi wlo whi /\ (hi <= RBv \/ RBv + 2 ^ 32 <= lo \/ hi <= lo) /\ (hi <= 2201439137792 \/ kHighMemBeg <= lo \/ hi <= lo).
Lemma tail_ext_ok3 : forall (E : env) r,
(forall k, (k < aHAV3)%nat -> ew E k = ew E0 k) -> In (skel r) SKEL_TAILR ->
let b := base_val E (YP09.r_base r) in
RFACTS3 (b + YP09.r_lo r) (b + YP09.r_hi r) (b + YP09.r_wlo r) (b + YP09.r_whi r).
Proof. clear3.
intros E r HE Hin. split; [exact (tail_ext_okR E r HE Hin)|].
pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
pose proof (pairwise_ij _ _ 0 1 _ _ (lo_disj ly LY) eq_refl eq_refl) as PT. pose proof (pairwise_ij _ _ 0 5 _ _ (lo_disj ly LY) eq_refl eq_refl) as PC.
unfold zdisjoint in PT, PC. cbn [fst snd] in PT, PC.
destruct r as [bs lo hi wlo whi cs]. unfold skel in Hin. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi].
let sk := eval vm_compute in SKEL_TAILR in change SKEL_TAILR with sk in Hin. cbn [In] in Hin.
repeat match type of Hin with _ \/ _ => destruct Hin as [Hin|Hin]; [injection Hin as <- <- <- <- <-|] | False => destruct Hin end.
all: cbn [base_val].
all: rewrite ?HE by (clear - HE; cbv; lia); rewrite ?E2, ?EaT, ?EaC, ?EaP, ?EaRG, ?EaSB, ?EaSHB; unfold w64;
rewrite ?unsigned_lit_small by (clear - DR F1 F2 F3 F4 F5 F6 F7 F8; numconst; unfold T, SB, SHBv in *; lia).
all: unfold Pr, RGv, RBv in *; clear - DR F1 F2 F3 F4 F5 F6 F7 F8 PT PC HcR; numconst; unfold TFIB_TSD, TFIB_TP, SHBv, T, SB in *; zlia.
Qed.
Lemma stack_ext_ok3 : (sp0 <= RBv \/ RBv + 2 ^ 32 <= sp0 - RSTACK) /\ kHighMemBeg <= sp0 - RSTACK.
Proof. clear3.
pose proof stack_ivsR as (_ & SP & _ & S4 & _). pose proof derived_rangesR as DR. pose proof high_factsR as (F1 & F2 & F3 & F4 & F5 & F6 & _).
unfold RBv in *. clear - SP S4 DR F4 F5 HcR. numconst. unfold SB in *. lia.
Qed.
Definition scratch_headed (ss : sstate) : Prop :=
exists cs, nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 2%nat) (- RSTACK) 0 (- RSTACK) 0 cs).
Lemma mem_ok_scratch_present : forall (Wx : world tfibsegs) (E' : env) ss (m : word -> option byte),
env_agree aHAV3 E0 E' -> scratch_headed ss -> mem_ok tfibsegs E' (mrestrict (w_H Wx) m) (ss_mem ss) ->
forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a.
Proof. clear3.
intros Wx E' ss m [HE _] [cs Hnth] (_ & Hrs & _) a Ha. pose proof stack_ivsR as (_ & _ & _ & S4 & S5). pose proof (u64_range (getr regs0 2)) as U.
pose proof (proj1 (Forall_forall _ _) Hrs _ (nth_error_In _ _ Hnth)) as (_ & _ & Hw & _).
cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw. rewrite (HE 2%nat ltac:(unfold aHAV3; lia)), E2 in Hw.
apply writable_high_apresent; [clear - Ha S4 S5 U; numconst; unfold sp0, TFIB_IMG_END in *; lia|].
replace a with (bv_unsigned (getr regs0 2) + (a - sp0)) by (unfold sp0; lia). apply Hw. unfold sp0 in *. lia.
Qed.
Lemma at_R3_run : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' st W' c',
at_R3 Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', st) -> match st with RS_ecall => False | _ => True end ->
(forall a, WINR0 a -> X a) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
pstable P -> scratch_headed ss' ->
SRr tfibsegs W' c' (at_R3 Wx md X P ss').
Proof. clear3.
intros Wx tbl tblok stop md X P ss ss' st W' c' HR Hrun Hst HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfibsegs tbl tblok Hwx Wx FUEL stop E' ss ss' st ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
assert (HS'' : st_ok tfibsegs E' ss' (restrict (w_H Wx) ms')) by (destruct st; [exact HS' | destruct Hst | exact HS']). clear HS'.
apply SRr_ret. split; [reflexivity|]. exists ms', mat', E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS''|].
assert (FR : forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) by (intros x Hx; exact (frame_X WINR0 E' _ _ _ (fun a H => H) (proj1 HE) Hwin HF x Hx)).
split; [|split].
- intros x Hx. rewrite (FR x) by (intros Hw; exact (Hx (HX _ Hw))). exact (MEQ x Hx).
- exact (mem_ok_scratch_present Wx E' ss' (ms_mem ms') HE Hsc (st_ok_mem_ok tfibsegs E' ss' _ HS'')).
- exact (HP _ _ FR HPm).
Qed.
Lemma at_R3_run_ecall : forall (Wx : world tfibsegs) tbl (tblok : table_ok tfibsegs tbl) stop md X P ss ss' W' c',
at_R3 Wx md X P ss W' c' ->
sym_run_toN_sh tfibsegs tbl FUEL stop ss = (ss', RS_ecall) -> ss_resv ss' = None ->
(forall a, WINR0 a -> X a) ->
forallb (fun t => existsb (win_sub t) WSKELR || (snd t <=? snd (fst t))) (windows (ss_mem ss)) = true ->
pstable P -> scratch_headed ss' ->
SRr tfibsegs W' c' (at_N3 Wx md X P ss').
Proof. clear3.
intros Wx tbl tblok stop md X P ss ss' W' c' HR Hrun Hrv HX Hwin HP Hsc.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_run_to_sh_gen tfibsegs tbl tblok Hwx Wx FUEL stop E' ss ss' RS_ecall ms _ _ HS Hrun).
intros ms' mat' HS' HF HFr. rewrite wvb_collapse.
apply SRr_ret. split; [reflexivity|]. exists ms', mat', E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS'|]. split; [exact Hrv|].
assert (FR : forall x : word, ~ WINR0 (bv_unsigned x) -> ms_mem ms' x = ms_mem ms x) by (intros x Hx; exact (frame_X WINR0 E' _ _ _ (fun a H => H) (proj1 HE) Hwin HF x Hx)).
split; [|split].
- intros x Hx. rewrite (FR x) by (intros Hw; exact (Hx (HX _ Hw))). exact (MEQ x Hx).
- destruct HS' as (_ & _ & _ & _ & _ & _ & _ & HM & _). cbn [ms_mem restrict] in HM. exact (mem_ok_scratch_present Wx E' ss' (ms_mem ms') HE Hsc HM).
- exact (HP _ _ FR HPm).
Qed.
Lemma at_R3_pin : forall (Wx : world tfibsegs) md X P ss W' c' (r : bv 5) (e : sv),
at_R3 Wx md X P ss W' c' -> r <> 0%bv ->
sv_atoms_lt aHAV3 e = true -> sv_atoms_lt aHAV3 (sr_get (ss_regs ss) r) = true ->
U E0 e = U E0 (sr_get (ss_regs ss) r) ->
at_R3 Wx md X P (pin ss r e) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' r e HR Hr Hae Has HU.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
unfold pin. apply st_ok_pin_regU; [exact HS | exact Hr |].
rewrite (U_agree aHAV3 E0 E' e HE Hae), (U_agree aHAV3 E0 E' _ HE Has). exact HU.
Qed.
Lemma at_R3_arm : forall (Wx : world tfibsegs) md X P ss W' c' (cnd : branch_cond) (tk : bool) (a b : sv),
at_R3 Wx md X P ss W' c' ->
sv_atoms_lt aHAV3 a = true -> sv_atoms_lt aHAV3 b = true ->
branch_taken cnd (sv_denot E0 a) (sv_denot E0 b) = tk ->
at_R3 Wx md X P (arm cnd tk a b ss) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' cnd tk a b HR Ha Hb Ht.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
unfold arm. rewrite <- (sv_denot_agree aHAV3 E0 E' a HE Ha), <- (sv_denot_agree aHAV3 E0 E' b HE Hb) in Ht.
destruct tk; [apply st_ok_add_cond; [exact HS | exact Ht] | apply st_ok_add_cond_neg; [exact HS | exact Ht]].
Qed.
Lemma at_R3_forget : forall (Wx : world tfibsegs) md X P ss W' c' (k : nat) (clob : list (bv 5)),
at_R3 Wx md X P ss W' c' -> (aHAV3 <= k)%nat -> ss_resv ss = None ->
ss_atoms_lt k ss = true -> regions_wf (ss_mem ss) = true -> no_cdata (ss_mem ss) = true -> mem_atoms_lt k (ss_mem ss) = true ->
reg_nodup clob = true -> forallb (fun r : bv 5 => negb (bv_eqb r 0)) clob = true ->
at_R3 Wx md X P (forget ss k clob) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' k clob HR Hk Hrv Hat Hwf Hnc Hma Hnd Hnz.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, (havoc E' k (map (getr (ms_regs ms)) clob)). split; [reflexivity|].
split; [exact (env_agree_havoc_ge aHAV3 k E0 E' _ Hk HE)|]. split; [|exact (conj MEQ (conj PRS HPm))].
pose proof (st_ok_forget k E' ss (w_H Wx) ms clob HS Hrv Hat Hwf Hnc Hma Hnd Hnz) as X'. unfold forget.
rewrite <- (st_ok_restrict_mkst tfibsegs (w_H Wx) E' ss ms HS Hrv) in X'. exact X'.
Qed.
Lemma at_R3_noconds : forall (Wx : world tfibsegs) md X P ss W' c', at_R3 Wx md X P ss W' c' -> at_R3 Wx md X P (noconds ss) W' c'.
Proof. clear3.
intros Wx md X P ss W' c' HR. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [|exact (conj MEQ (conj PRS HPm))].
unfold noconds. apply st_ok_prune. exact HS.
Qed.
Lemma at_R3_weaken : forall (Wx : world tfibsegs) md X X' (P P' : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' -> (forall a, X a -> X' a) -> (forall m, P m -> P' m) -> at_R3 Wx md X' P' ss W' c'.
Proof. clear3.
intros Wx md X X' P P' ss W' c' HR HX HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. repeat (split; [assumption||reflexivity|]).
split; [intros x Hx; apply MEQ; intros H; exact (Hx (HX _ H))|]. split; [exact PRS | exact (HP _ HPm)].
Qed.
Lemma at_R3_facts : forall (Wx : world tfibsegs) md X (P Q : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' ->
(forall (E' : env) ms, env_agree aHAV3 E0 E' -> st_ok tfibsegs E' ss (restrict (w_H Wx) ms) -> Q (ms_mem ms)) ->
at_R3 Wx md X (fun m => P m /\ Q m) ss W' c'.
Proof. clear3.
intros Wx md X P Q ss W' c' HR HQ. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS|]. split; [exact MEQ|]. split; [exact PRS|]. split; [exact HPm | exact (HQ E' ms HE HS)].
Qed.
Lemma at_R3_strengthen : forall (Wx : world tfibsegs) md X (P P' : (word -> option byte) -> Prop) ss W' c',
at_R3 Wx md X P ss W' c' ->
(forall m, (forall x : word, ~ X (bv_unsigned x) -> m x = mem0 x) -> (forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) m a) -> P m -> P' m) ->
at_R3 Wx md X P' ss W' c'.
Proof. clear3.
intros Wx md X P P' ss W' c' HR HP. destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm).
split; [reflexivity|]. exists ms, mat, E'. split; [reflexivity|]. split; [exact HE|]. split; [exact HS|]. split; [exact MEQ|]. split; [exact PRS | exact (HP _ MEQ PRS HPm)].
Qed.
Lemma at_R3_eq : forall (Wx : world tfibsegs) md X P ss ss' W' c', at_R3 Wx md X P ss W' c' -> ss = ss' -> at_R3 Wx md X P ss' W' c'.
Proof. clear3. intros Wx md X P ss ss' W' c' H <-. exact H. Qed.
Definition CSAVED : list (bv 5) := [2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma sv_denot_SOff0 : forall (E' : env) k, sv_denot E' (SOff k 0) = ew E' k.
Proof. clear. intros E' k. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma at_R3_ret : forall (Wx : world tfibsegs) md X P ss W' c' (v : Z),
at_R3 Wx md X P ss W' c' -> ss_resv ss = None -> ss_pc ss = 0x3615c ->
sr_get (ss_regs ss) 1%bv = SOff 1 0 -> sr_get (ss_regs ss) 10%bv = SLit v ->
sr_get (ss_regs ss) 4%bv = SLit TFIB_TP ->
Forall (fun r : bv 5 => sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0) CSAVED ->
SRr tfibsegs W' c' (at_RET3 Wx v md X P).
Proof. clear3.
intros Wx md X P ss W' c' v HR Hrv Hpc H1 H10 H4 Hcs.
destruct HR as (-> & ms & mat & E' & -> & HE & HS & MEQ & PRS & HPm). pose proof Hwx_tfa as Hwx.
eapply (SRr_ret_at tfibsegs tfibtbl_rtA tfibtbl_rtA_ok Hwx Wx E' ss ms _ _ HS Hrv); [rewrite Hpc; vm_compute; reflexivity|].
intros mat'. rewrite wvb_collapse.
assert (RG : forall r : bv 5, sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> (Z.to_nat (bv_unsigned r) < aHAV3)%nat -> getr (ms_regs ms) r = getr regs0 r).
{ intros r Hr Hlt. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms r HS), Hr, sv_denot_SOff0, (proj1 HE _ Hlt). apply (Er _ r). rewrite Z2Nat.id; [reflexivity | pose proof (bv_unsigned_in_range 5 r); lia]. }
assert (R1 : getr (ms_regs ms) 1 = getr regs0 1) by (apply RG; [exact H1 | cbv; lia]).
rewrite R1. unfold YK0s.ret_ok in Hra. rewrite Hra.
split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), mat'. split; [reflexivity|].
split. { rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 10 HS), H10. reflexivity. }
split. { intros r Hr. destruct (bv_eqb r 4%bv) eqn:E4.
- apply bv_eqb_eq in E4. subst r. rewrite (st_ok_reg_denot (w_H Wx) E' ss ms 4 HS), H4. cbn [sv_denot]. symmetry. exact Htp.
- assert (N4 : r <> 4%bv) by (intros ->; rewrite bv_eqb_refl in E4; discriminate E4).
assert (IN : In r CSAVED).
{ unfold CSAVED. cbn [In] in Hr. cbn [In].
repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr]; [first [exfalso; apply N4; reflexivity | tauto] |] | False => destruct Hr end. }
apply RG; [exact (proj1 (Forall_forall _ _) Hcs r IN)|].
pose proof (bv_unsigned_in_range 5 r) as B. change (bv_modulus 5) with 32 in B. unfold aHAV3. lia. }
split; [exact MEQ|]. split; [exact PRS | exact HPm].
Qed.
Lemma at_N3_cont : forall (Wx Wy : world tfibsegs) (md' : Model) X (P' : (word -> option byte) -> Prop) ss (e : sv) (v : word) (R : Z -> Prop)
(mem' : word -> option byte) ms (E' : env),
env_agree aHAV3 E0 E' ->
st_ok_ecall tfibsegs E' ss (restrict (w_H Wx) ms) -> ss_resv ss = None ->
(forall x : word, ~ X (bv_unsigned x) -> ms_mem ms x = mem0 x) ->
(forall a, sp0 - RSTACK <= a < sp0 -> apresent (w_H Wx) (ms_mem ms) a) ->
hsub (w_H Wy) (w_H Wx) ->
sv_denot E' e = v -> no_cdata (ss_mem ss) = true ->
(forall x : word, ~ R (bv_unsigned x) -> mem' x = ms_mem ms x) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_lo r <= a < base_val E' (YP09.r_base r) + YP09.r_hi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E' (YP09.r_base r) + YP09.r_wlo r <= a < base_val E' (YP09.r_base r) + YP09.r_whi r -> ~ R a /\ 0 <= a < 2 ^ 64) ->
(forall a, sp0 - RSTACK <= a < sp0 -> ~ R a) ->
P' mem' ->
at_R3 Wy md' (fun a => X a \/ R a) P' (resume ss e (ss_mem ss) (ss_facts ss)) Wy
(mkCfg (mkst (regupd (ms_regs ms) 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfibsegs)) md').
Proof. clear3.
intros Wx Wy md' X P' ss e v R mem' ms E' HE HS Hrv MEQ PRS Hsub He Hnc Hfr Hext Hwin HsR HP'.
destruct (st_ok_ecall_shape_r tfibsegs (w_H Wx) E' ss ms HS Hrv) as (regs & mem & Hms & Hregs & Hmem & HG).
assert (Er' : ms_regs ms = regs) by (rewrite Hms; reflexivity). assert (Em' : ms_mem ms = mem) by (rewrite Hms; reflexivity).
rewrite Er'. rewrite Em' in MEQ, PRS, Hfr. clear Hms Er' Em'.
pose proof stack_ext_ok3 as [_ SPlo]. pose proof (u64_range (getr regs0 2)) as SPhi.
split; [reflexivity|]. exists (mkst (regupd regs 10%bv v) (v_addi (Z_to_bv 64 (ss_pc ss)) 4) mem' (seg_rom tfibsegs)), (m_vm_materialized md'), E'.
split; [rewrite with_vm_backing_id; reflexivity|]. split; [exact HE|]. split; [|split; [|split]].
- rewrite restrict_mkst_fx. apply (st_ok_resume_sv tfibsegs E' ss regs (mrestrict (w_H Wy) mem') e v Hregs); [| exact HG | exact He].
apply (mem_ok_kept tfibsegs E' (mrestrict (w_H Wy) mem) (mrestrict (w_H Wy) mem') (ss_mem ss));
[exact (mem_ok_mrestrict_hsub tfibsegs (w_H Wx) (w_H Wy) E' mem (ss_mem ss) (w_Hoff Wx) Hsub Hmem) | exact Hnc |].
apply Forall_forall. intros r Hr. exact (kept_of_frame2 (w_H Wy) E' mem mem' R r Hfr (fun a Ha => Hext r a Hr Ha) (fun a Ha => Hwin r a Hr Ha)).
- intros x Hx. cbn [ms_mem mkst]. rewrite (Hfr x) by (intros HRx; apply Hx; right; exact HRx). apply MEQ. intros HXx; apply Hx; left; exact HXx.
- intros a Ha. cbn [ms_mem mkst]. destruct (PRS a Ha) as [Hh [b Hb]]. split.
+ destruct (w_H Wy (Z_to_bv 64 a)) eqn:Ey; [|reflexivity]. rewrite (Hsub _ Ey) in Hh. discriminate Hh.
+ exists b. rewrite (Hfr (Z_to_bv 64 a)); [exact Hb|]. rewrite unsigned_lit_small by (clear - Ha SPlo SPhi; numconst; unfold sp0 in *; lia). exact (HsR a Ha).
- cbn [ms_mem mkst]. exact HP'.
Qed.
Lemma memset_stretch3 : forall (Wx : world tfibsegs) (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = tfib_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TFIB_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= d \/ d + len <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
(0 <= a < TFIB_IMG_LO) \/ (TFIB_IMG_END <= a < 2 ^ 64)) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr tfibsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md d len retpc Q HS Hrv Hpc Hat Hnc H10 H12 H1 Hlen Hd Hdl Hrpc Hrpc' Hpres Hext Hext64 Hwin HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 d) (Z.to_nat len) = true).
{ apply store_ok_of_all; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); [lia|]. intros x Hx.
pose proof (apresent_writable (w_H Wx) (ms_mem ms) (bv_unsigned x) ltac:(pose proof (u64_range x); unfold TFIB_IMG_END in *; lia) (Hpres (bv_unsigned x) ltac:(lia))) as Hw.
unfold writable_at in Hw. rewrite Z_to_bv_bv_unsigned in Hw. exact Hw. }
destruct (tfib_memset (Z_to_bv 64 d) (getr (ms_regs ms) 11) (Z_to_bv 64 len) (Z.to_nat len) mr (seg_rom tfibsegs) (ms_regs ms)
H10 eq_refl H12 ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia) SOK
ltac:(rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia))
as (regs' & Hms & H10' & Hfr).
set (bs := repeat (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256)) (Z.to_nat len)) in Hms.
assert (Hlenbs : Z.of_nat (length bs) = len) by (subst bs; rewrite repeat_length; lia).
eapply (SRr_msteps tfibsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
rewrite H1. replace (v_jalr (Z_to_bv 64 retpc) 0) with (Z_to_bv 64 retpc).
2:{ unfold v_jalr, jalr_tgtZ. rewrite unsigned_lit_small by lia. f_equal. rewrite Z.add_0_r.
change (-2) with (- 2 ^ 1). rewrite land_neg_pow2 by lia. change (2 ^ 1) with 2.
replace (retpc mod 2) with 0; [lia|]. symmetry. apply Znumtheory.Zdivide_mod. apply (Z.divide_trans _ 4); [exists 2; reflexivity|].
apply Znumtheory.Zmod_divide; [lia | exact Hrpc]. }
change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 retpc) (wbytes mr (Z_to_bv 64 d) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 retpc) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 d) bs)) (seg_rom tfibsegs)).
set (m1 := wbytes mr (Z_to_bv 64 d) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (d <= bv_unsigned x < d + len) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) d).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) retpc [11; 12; 13; 14; 15; 16]%bv HS Hrv);
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
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [reflexivity|].
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
Lemma nth_Z_to_le_bytes4 : forall v (t : nat) d, (t < 4)%nat -> nth t (Z_to_le_bytes 4 v) d = Z_to_bv 8 (Z.shiftr v (8 * Z.of_nat t)).
Proof. clear.
intros v t d Ht. destruct t as [|[|[|[|t]]]]; [| | | |lia]; cbn [Z_to_le_bytes nth]; rewrite ?Z.shiftr_shiftr by lia.
- change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.
Lemma popfree_stretch : forall (Wx : world tfibsegs) (k : nat) (E : env) ss ms md (e cst sz cnt : Z) (Q : world tfibsegs -> config -> Prop),
st_ok tfibsegs E ss (restrict (w_H Wx) ms) -> ss_resv ss = None -> ss_pc ss = 0x366c8 ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 0 -> getr (ms_regs ms) 11 = Z_to_bv 64 e -> getr (ms_regs ms) 12 = Z_to_bv 64 cst ->
getr (ms_regs ms) 21 = Z_to_bv 64 sz -> getr (ms_regs ms) 19 = Z_to_bv 64 cnt ->
1 <= cnt -> 4 * cnt <= e -> e < 2 ^ 64 -> 0 <= cst -> 0 <= sz -> cst + cnt * sz < 2 ^ 36 -> TFIB_IMG_END <= e - 4 * cnt ->
(forall a, e - 4 * cnt <= a < e -> apresent (w_H Wx) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_hi r <= e - 4 * cnt \/ e <= base_val E (YP09.r_base r) + YP09.r_lo r
\/ YP09.r_hi r <= YP09.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok tfibsegs (havoc E k (map (getr regs') [10; 12; 14; 15]%bv))
(ss_after_stretch ss (ss_mem ss) k [10; 12; 14; 15]%bv 0x366e8)
(restrict (w_H Wx) (mkst regs' (Z_to_bv 64 0x366e8) mem' (seg_rom tfibsegs))) ->
(forall x : word, ~ (e - 4 * cnt <= bv_unsigned x < e) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H Wx) (ms_mem ms) a -> apresent (w_H Wx) mem' a) ->
(forall i, 0 <= i < cnt -> val_mem tfibsegs (mrestrict (w_H Wx) mem') (e - 4 - 4 * i) 4 ((cst + i * sz) / 16)) ->
SRr tfibsegs Wx (mkCfg (mkst regs' (Z_to_bv 64 0x366e8) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr tfibsegs Wx (mkCfg ms md) Q.
Proof. clear3.
intros Wx k E ss ms md e cst sz cnt Q HS Hrv Hpc Hat Hnc H10 H11 H12 H21 H19 Hcnt Hce He Hcst Hsz Hov Himg Hpres Hext Hext64 HK.
pose proof Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H Wx) E _ _ HS Hrv) as Hshape. rewrite Hpc in Hshape. rewrite Hshape.
set (mr := mrestrict (w_H Wx) (ms_mem ms)).
assert (SOK : store_ok tfibsegs mr (Z_to_bv 64 (e - 4 * cnt)) (Z.to_nat (4 * (cnt - 0))) = true).
{ apply store_ok_of_presentR; [|unfold TFIB_IMG_END in *; lia|lia]. intros i Hi. destruct (Hpres (e - 4 * cnt + i) ltac:(lia)) as [Hh [b Hb]]. exists b. unfold mr, mrestrict. rewrite Hh. exact Hb. }
destruct (tfib_popfree_spec (ms_regs ms) mr 0 e cst sz cnt H10 H11 H12 H21 H19 ltac:(lia) ltac:(lia) Hcst Hsz ltac:(lia) SOK)
as (regs' & Hms & R10 & R12 & R14 & R15 & Rfr).
change Asan.M.loaded_segments with tfibsegs in Hms.
replace (Z_to_bv 64 tfib_popfree_head : word) with (Z_to_bv 64 0x366c8 : word) in Hms by reflexivity.
eapply (SRr_msteps tfibsegs Hwx Wx _ _ md Q). { rewrite restrict_mkst_fx. exact Hms. }
intros model' Hsame Hcln. rewrite (same_but_materialized_wvb md model' Hsame).
set (bs := pf_bytes cst sz (Z.to_nat (cnt - 0))) in *.
assert (Hbl : Z.of_nat (length bs) = 4 * cnt) by (subst bs; rewrite pf_bytes_length; lia).
change (unrestrict (w_H Wx) (ms_mem ms) (mkst regs' (Z_to_bv 64 (tfib_popfree_head + 32)) (wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs) (seg_rom tfibsegs)))
with (mkst regs' (Z_to_bv 64 (tfib_popfree_head + 32)) (munrestrict (w_H Wx) (ms_mem ms) (wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs)) (seg_rom tfibsegs)).
replace (Z_to_bv 64 (tfib_popfree_head + 32) : word) with (Z_to_bv 64 0x366e8 : word) by reflexivity.
set (m1 := wbytes mr (Z_to_bv 64 (e - 4 * cnt)) bs) in *. set (m1full := munrestrict (w_H Wx) (ms_mem ms) m1).
assert (Hm1 : mrestrict (w_H Wx) m1full = m1).
{ pose proof (f_equal ms_mem (restrict_unrestrict_clean (w_H Wx) (ms_mem ms) _ Hcln)) as Em. cbn [ms_mem restrict unrestrict mkst] in Em. exact Em. }
assert (FR1 : forall x : word, ~ (e - 4 * cnt <= bv_unsigned x < e) -> m1 x = mr x).
{ intros x Hx. subst m1. destruct (Z_lt_le_dec (bv_unsigned x) (e - 4 * cnt)).
- apply wbytes_below; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia.
- apply wbytes_above; rewrite unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia. }
assert (GR1 : mem_grows mr m1) by (subst m1; apply wbytes_grows).
apply (HK regs' m1full (m_vm_materialized model')).
- rewrite restrict_mkst_fx, Hm1.
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' Hrv']. apply andb_prop in Hat' as [Hat' HG]. apply andb_prop in Hat' as [Hr' Hm'].
apply (st_ok_after_stretch tfibsegs k E ss (restrict (w_H Wx) ms) regs' m1 (ss_mem ss) 0x366e8 [10; 12; 14; 15]%bv HS Hrv);
[ unfold ss_atoms_lt; rewrite Hr', Hm', HG, Hrv'; reflexivity
| exact (proj1 (st_ok_mem_ok tfibsegs E ss _ HS)) | exact Hnc | exact Hm' | apply submem_refl | reflexivity | reflexivity | | ].
+ intros r Hr. cbn [ms_regs restrict]. apply reg_in_false in Hr. cbn [In] in Hr.
apply Rfr; intros ->; apply Hr; tauto.
+ apply Forall_forall. intros r Hr. cbn [ms_mem restrict]. fold mr. split.
* intros a Ha. unfold mbyte. rewrite (FR1 (Z_to_bv 64 a)); [reflexivity|].
rewrite unsigned_lit_small by (exact (Hext64 r a Hr Ha)). destruct (Hext r Hr) as [X|[X|X]]; lia.
* intros a Ha Hw. apply (writable_at_grows tfibsegs mr m1 a GR1 Hw).
- intros x Hx. subst m1full. unfold munrestrict. destruct (w_H Wx x) eqn:Hh; [reflexivity|].
rewrite (FR1 x Hx). subst mr. unfold mrestrict. rewrite Hh. reflexivity.
- intros a [Hh [b Hb]]. split; [exact Hh|]. subst m1full. unfold munrestrict. rewrite Hh.
assert (NN : m1 (Z_to_bv 64 a) <> None) by (apply GR1; subst mr; unfold mrestrict; rewrite Hh, Hb; discriminate).
destruct (m1 (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply NN; reflexivity].
- intros i Hi. rewrite Hm1. intros t Ht. subst m1. unfold mbyte.
rewrite (wbytes_inside bs mr (Z_to_bv 64 (e - 4 * cnt)) (Z_to_bv 64 (e - 4 - 4 * i + Z.of_nat t)))
by (rewrite !unsigned_lit_small by (unfold TFIB_IMG_END in *; lia); lia).
rewrite !unsigned_lit_small by (unfold TFIB_IMG_END in *; lia). f_equal.
replace (Z.to_nat (e - 4 - 4 * i + Z.of_nat t - (e - 4 * cnt))) with (Z.to_nat (4 * (cnt - 1 - i)) + t)%nat by lia.
subst bs. rewrite (pf_bytes_nth cst sz (Z.to_nat (cnt - 0)) (cnt - 1 - i) t) by lia.
replace (Z.of_nat (Z.to_nat (cnt - 0)) - 1 - (cnt - 1 - i)) with i by lia.
rewrite nth_Z_to_le_bytes4 by exact Ht. symmetry. apply le_byte_small; [|exact Ht].
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). split; [apply Z.div_pos; nia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Variables (B : asyms) (S : astate).
Hypothesis TS : TfibSyms B.
Hypothesis HTSD : ly_tsd ly = TFIB_TSD.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hgp : getr regs0 3 = w64 (as_gp B).
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hchunks : pc_chunks (cache S c) = [].
Hypothesis Hnf_def : nf = fa_len (rg_free (reg S c)).
Hypothesis Hmf_def : mf = rg_mapped_fa (reg S c).
Hypothesis Hau_def : au = rg_alloc_user (reg S c).
Hypothesis Hmu_def : mu = rg_mapped_user (reg S c).
Hypothesis Hj64v : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 64) 4 j64.
Hypothesis Hjnav : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 72) 8 jna.
Hypothesis Hjnfv : val_mem tfibsegs (mrestrict (w_H W) mem0) (RGv + 80) 8 jnf.
Hypothesis Hjsmv : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2792) 8 jsm.
Hypothesis Hjm1v : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2872) 8 jm1.
Hypothesis Hjm2v : val_mem tfibsegs (mrestrict (w_H W) mem0) (T + 2880) 8 jm2.
Hypothesis HQL : qloose S.
Hypothesis HAR : AR tfibsegs B ly S W mem0 md0.
Lemma Pr_is : Pr = ly_T ly + t_cache + 80 * c. Proof. reflexivity. Qed.
Lemma RGv_is : RGv = ly_space ly + kRegionInfoOff + 128 * c. Proof. reflexivity. Qed.
Lemma FAv_is : FAv = fa_base ly c.
Proof. clear - HcR. unfold FAv, RBv, fa_base, SB. rewrite region_off_eq by lia. reflexivity. Qed.
Lemma RBv_is : RBv = region_base ly c.
Proof. clear - HcR. unfold RBv, region_base, SB. rewrite region_off_eq by lia. reflexivity. Qed.
End g.
End f.
