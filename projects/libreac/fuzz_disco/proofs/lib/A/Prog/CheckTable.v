(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8q.v:156-158;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACbk.v:76-79; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:200-203, 287-290,
   358-363, for libreac/fuzz_identity's asan-ubsan build (lib/B). The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8h.v:75-78, 95-98, 104-107. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_family_of.v, with its module paths, module names and numbers changed; 807 of its 905 lines of code are new or changed and 749 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC4b YC1h YC85.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YA0j YK00.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
Section h.
Variable B : asyms.
Definition TCHECK_TABLE_STK : Z := 96 + 2 * ESTACK.
Definition tcheck_table_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base (fx := fq) SEGS B TCHECK_TABLE_STK [] regs ly S W mem md 0 (fun ly' S' W' _ mem' _ => Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_TABLE_STK <= a < spZ regs) ->
         aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a)).
Definition tcheck_table_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t : Z) (T : list byte),
  afn_pre SEGS B TCHECK_TABLE_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> t + 400 <= 2 ^ 63 ->
  length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
  amem_range t 400 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 ->
  (t + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= t) ->
  off_img t 400 ->
  tbl_T1 T -> tbl_T2 T -> tbl_T3 T ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_check_table) regs mem md) (tcheck_table_post fq regs ly S W mem md).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Definition CBx : sv := SOff 32 0.
Definition CBspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ct_SH : list shent := [ mkSHE 10 0 400 ].
Definition ct_rv (T : list byte) (i : nat) : Z := u_at T (48 * Z.of_nat i + 8) 4.
Definition ct_role_chunk (i : nat) : YP09.chunk := YP09.mkChunk (48 * Z.of_nat i + 8) (CVal 4 (SOff (33 + i) 0)).
Definition ct_tbl_region (k : nat) : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 400 0 0 (YP09.mkChunk 384 (CVal 4 (SLit (Z.of_nat k))) :: map ct_role_chunk (seq 0 k)).
Definition ct_regions (k : nat) : smem := [ stack_region 96; got_regionP; bcell_regionP 32; ct_tbl_region k ].
Fixpoint ct_keepidx (rs : smem) (i : nat) : list nat :=
match rs with
| [] => []
| r :: l => match YP09.r_base r with
| Some 2%nat => i :: ct_keepidx l (S i)
| Some 10%nat => i :: ct_keepidx l (S i)
| _ => ct_keepidx l (S i)
end
end.
Definition ct_facts (k : nat) : facts :=
mkFacts ([ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] ++
map (fun i => ((33 + i)%nat, mkAF 0 2 0)) (seq 0 k)) [] [].
Definition ss_ct (k : nat) : sstate := mkSS AF_check_table sr_atoms (ct_regions k) None (ct_facts k).
Definition ct_extra (T : list byte) : list word :=
[ Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (ct_rv T 0); Z_to_bv 64 (ct_rv T 1); Z_to_bv 64 (ct_rv T 2); Z_to_bv 64 (ct_rv T 3);
Z_to_bv 64 (ct_rv T 4); Z_to_bv 64 (ct_rv T 5); Z_to_bv 64 (ct_rv T 6); Z_to_bv 64 (ct_rv T 7) ].
Definition EC (regs : bvmap 5 word) (T : list byte) : env := Eimg (Ereg regs (ct_extra T)).
Lemma ct_getr8 : forall (regs : bvmap 5 word) v (r : bv 5), r <> 8%bv -> getr (regupd regs 8 v) r = getr regs r.
Proof. intros regs v r Hr. unfold getr. destruct (bv_eqb r 0); [reflexivity|]. exact (regupd_other regs 8 v r Hr). Qed.
Lemma ct_spZ8 : forall (regs : bvmap 5 word) v, spZ (regupd regs 8 v) = spZ regs.
Proof. intros regs v. unfold spZ. rewrite ct_getr8; [reflexivity|]. intros X. apply (f_equal bv_unsigned) in X. discriminate X. Qed.
Lemma ct_sub_nth : forall (T : list byte) (j w k : nat), (k < w)%nat ->
nth_error (sub T (Z.of_nat j) w) k = nth_error T (j + k).
Proof. intros T j w k Hk. unfold sub. rewrite Nat2Z.id, nth_error_firstn. destruct (Nat.ltb_spec k w); [|lia]. apply nth_error_skipn. Qed.
Lemma ct_garr8_nth : forall (m : word -> option byte) base (L : list byte) j b,
garr8 SEGS m base (map bv_unsigned L) -> nth_error L j = Some b ->
mbyte SEGS m (base + Z.of_nat j) = Some b.
Proof.
intros m base L j b G Hj.
assert (Hl : (j < length L)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
rewrite (garr8_mbyte SEGS m base (map bv_unsigned L) j G) by (rewrite length_map; exact Hl).
f_equal. rewrite (nth_error_nth (map bv_unsigned L) j 0 (map_nth_error bv_unsigned j L Hj)). apply Z_to_bv_bv_unsigned.
Qed.
Lemma ct_aview_nth : forall H (m : word -> option byte) base (L : list byte) j b,
garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> nth_error L j = Some b ->
aview SEGS H m (base + Z.of_nat j) = Some (bv_unsigned b).
Proof. intros H m base L j b G Hj. unfold aview. rewrite (ct_garr8_nth _ base L j b G Hj). reflexivity. Qed.
Lemma ct_aview_some : forall H (m : word -> option byte) base (L : list byte) a,
garr8 SEGS (mrestrict H m) base (map bv_unsigned L) -> base <= a < base + Z.of_nat (length L) ->
aview SEGS H m a <> None.
Proof.
intros H m base L a G Ha.
destruct (nth_error L (Z.to_nat (a - base))) as [b|] eqn:Hb; [|apply nth_error_None in Hb; lia].
replace a with (base + Z.of_nat (Z.to_nat (a - base))) by lia. rewrite (ct_aview_nth H m base L _ b G Hb). discriminate.
Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma ct_swrap_small : forall u, 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u -> bv_swrap 32 u = u.
Proof. intros u Hu Hs. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with 4294967296 in *. change (2 ^ (Z.of_N 32 - 1)) with 2147483648 in *. lia. Qed.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma ct_u_val : forall H (m : word -> option byte) t (T : list byte) (p : nat), length T = 400%nat ->
garr8 SEGS (mrestrict H m) t (map bv_unsigned T) -> (p + 4 <= 400)%nat ->
val_mem SEGS (mrestrict H m) (t + Z.of_nat p) 4 (u_at T (Z.of_nat p) 4).
Proof.
intros H m t T p LT GT Hp k Hk.
assert (Hlen : length (sub T (Z.of_nat p) 4) = 4%nat) by (unfold sub; rewrite length_firstn, length_skipn, Nat2Z.id, LT; lia).
pose proof (bytes_le_to_Z_bound (sub T (Z.of_nat p) 4)) as Hb1. pose proof (bytes_le_to_Z_nonneg (sub T (Z.of_nat p) 4)) as Hb0. rewrite Hlen in Hb1.
destruct (nth_error T (p + k)) as [b|] eqn:Hb2; [|apply nth_error_None in Hb2; lia].
replace (t + Z.of_nat p + Z.of_nat k) with (t + Z.of_nat (p + k)) by lia.
rewrite (ct_garr8_nth _ t T (p + k) b GT Hb2). f_equal.
rewrite le_byte_small by first [lia | unfold u_at; split; [exact Hb0 | exact Hb1]].
rewrite <- (ct_sub_nth T p 4 k Hk) in Hb2.
pose proof (YA0j.nth_error_le_byte _ _ _ Hb2) as Hv.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. unfold u_at. rewrite <- Hv. first [reflexivity | symmetry; apply Z.mod_small; apply (u8_range b)].
Qed.
Lemma ct_u4_range : forall (T : list byte) p, 0 <= u_at T p 4 < 2 ^ 32.
Proof.
intros T p. unfold u_at. pose proof (bytes_le_to_Z_nonneg (sub T p 4)) as H0.
pose proof (bytes_le_to_Z_bound (sub T p 4)) as H1. unfold sub in *. rewrite length_firstn in H1.
pose proof (Nat.le_min_l 4 (length (skipn (Z.to_nat p) T))) as Hm.
split; [lia|]. eapply Z.lt_le_trans; [exact H1|]. apply Z.pow_le_mono_r; lia.
Qed.
Lemma ct_ncase : forall (T : list byte), tbl_T1 T -> exists k, (k <= 8)%nat /\ n_of T = Z.of_nat k /\ u_at T 384 4 = Z.of_nat k.
Proof.
intros T HT1. unfold tbl_T1, n_of, s32_at in *. pose proof (ct_u4_range T 384) as HB.
assert (HE : bv_swrap 32 (u_at T 384 4) = u_at T 384 4) by (apply ct_swrap_small; [exact HB | lia]).
rewrite HE in *. exists (Z.to_nat (u_at T 384 4)). split; [lia|]. split; lia.
Qed.
Lemma ct_roles_bound : forall (T : list byte) k, tbl_T2 T -> n_of T = Z.of_nat k ->
forall i, (i < k)%nat -> 0 <= ct_rv T i <= 2.
Proof.
intros T k HT2 Hn i Hi. unfold ct_rv.
pose proof (HT2 (Z.of_nat i) ltac:(lia)) as HR. unfold role_of_e, s32_at in HR.
pose proof (ct_u4_range T (48 * Z.of_nat i + 8)) as HB.
assert (HE : bv_swrap 32 (u_at T (48 * Z.of_nat i + 8) 4) = u_at T (48 * Z.of_nat i + 8) 4)
by (apply ct_swrap_small; [exact HB | lia]).
rewrite HE in HR. lia.
Qed.
Lemma ct_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof.
intros E l1. induction l1 as [|[nn f] l1 IH]; intros l2 H1 H2; [exact H2|].
cbn [app atoms_ok] in *. split; [exact (proj1 H1) | apply IH; [exact (proj2 H1) | exact H2]].
Qed.
Lemma ct_atoms_roles : forall E (g : nat -> afact) l,
(forall i, In i l -> afact_ok E (33 + i)%nat (g i)) -> atoms_ok E (map (fun i => ((33 + i)%nat, g i)) l).
Proof.
intros E g l. induction l as [|a l IH]; intros H; [exact I|].
cbn [map atoms_ok]. split; [apply H; left; reflexivity | apply IH; intros i Hi; apply H; right; exact Hi].
Qed.
Lemma ct_atoms_forall : forall E l, (forall nn f, In (nn, f) l -> afact_ok E nn f) -> atoms_ok E l.
Proof.
intros E l. induction l as [|[nn f] l IH]; intros H; [exact I|].
cbn [atoms_ok]. split; [apply H; left; reflexivity | apply IH; intros n' f' Hin; apply H; right; exact Hin].
Qed.
Lemma ct_mac2 : forall H (m : word -> option byte) t (T : list byte) i j,
length T = 400%nat -> 0 <= i <= 7 -> 0 <= j <= 7 ->
garr8 SEGS (mrestrict H m) t (map bv_unsigned T) ->
((forall o, 0 <= o < 6 -> aview SEGS H m (t + 48 * i + o) = aview SEGS H m (t + 48 * j + o)) <-> mac_of T i = mac_of T j).
Proof.
intros H m t T i j LT Ri Rj GT. unfold mac_of.
assert (NT : forall (x : Z) k, 0 <= x <= 7 -> (k < 6)%nat -> nth_error (sub T (48 * x) 6) k = nth_error T (Z.to_nat (48 * x) + k)).
{ intros x k Hx Hk. replace (48 * x) with (Z.of_nat (Z.to_nat (48 * x))) at 1 by lia. apply ct_sub_nth. exact Hk. }
assert (VT : forall (x : Z) k b, 0 <= x <= 7 -> nth_error T (Z.to_nat (48 * x) + k) = Some b ->
aview SEGS H m (t + 48 * x + Z.of_nat k) = Some (bv_unsigned b)).
{ intros x k b Hx Hb. replace (t + 48 * x + Z.of_nat k) with (t + Z.of_nat (Z.to_nat (48 * x) + k)) by lia.
exact (ct_aview_nth H m t T _ b GT Hb). }
split.
- intros HE. apply nth_error_ext. intros k. destruct (Nat.lt_ge_cases k 6) as [Hk|Hk].
+ rewrite (NT i k Ri Hk), (NT j k Rj Hk).
destruct (nth_error T (Z.to_nat (48 * i) + k)) as [b1|] eqn:E1; [|apply nth_error_None in E1; lia].
destruct (nth_error T (Z.to_nat (48 * j) + k)) as [b2|] eqn:E2; [|apply nth_error_None in E2; lia].
pose proof (HE (Z.of_nat k) ltac:(lia)) as Hq. rewrite (VT i k b1 Ri E1), (VT j k b2 Rj E2) in Hq.
injection Hq as Hq. f_equal. apply bv_eq. exact Hq.
+ rewrite (proj2 (nth_error_None (sub T (48 * i) 6) k) ltac:(unfold sub; rewrite length_firstn, length_skipn, LT; lia)).
rewrite (proj2 (nth_error_None (sub T (48 * j) 6) k) ltac:(unfold sub; rewrite length_firstn, length_skipn, LT; lia)). reflexivity.
- intros HE o Ho. pose proof (NT i (Z.to_nat o) Ri ltac:(lia)) as Hi1. pose proof (NT j (Z.to_nat o) Rj ltac:(lia)) as Hj1.
rewrite HE in Hi1. rewrite Hj1 in Hi1.
destruct (nth_error T (Z.to_nat (48 * j) + Z.to_nat o)) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
replace o with (Z.of_nat (Z.to_nat o)) by lia.
rewrite (VT j (Z.to_nat o) b Rj Eb). rewrite (VT i (Z.to_nat o) b Ri ltac:(symmetry; exact Hi1)). reflexivity.
Qed.
Lemma ct_hull_sub : forall rd a n a' n', shadow_hull_vis rd a n -> 0 <= a -> a <= a' -> a' + n' <= a + n -> 0 < n' ->
shadow_hull_vis rd a' n'.
Proof.
intros rd a n a' n' HV Ha H1 H2 Hn s Hs. apply HV. unfold shadow_addr in *.
pose proof (Z.div_le_mono a a' 8 ltac:(lia) H1) as D1.
pose proof (Z.div_le_mono (a' + n' - 1) (a + n - 1) 8 ltac:(lia) ltac:(lia)) as D2.
pose proof (Z.div_le_mono (SHADOW_OFF + a / 8) (SHADOW_OFF + a' / 8) 8 ltac:(lia) ltac:(lia)) as D3.
pose proof (Z.div_le_mono (SHADOW_OFF + (a' + n' - 1) / 8) (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia) ltac:(lia)) as D4.
lia.
Qed.
Lemma ct_meq_frame : forall E rs (H : word -> bool) (m0 m1 m2 : word -> option byte) lo hi,
frame_of E rs (mrestrict H m1) (mrestrict H m2) ->
(forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> lo <= a < hi) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m1 a = aview SEGS H m0 a) ->
forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS H m2 a = aview SEGS H m0 a.
Proof.
intros E rs H m0 m1 m2 lo hi HF Hw HM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m1 m2 (fun a => lo <= a < hi) HF Hw a Ha Hn). exact (HM a Ha Hn).
Qed.
Lemma ct_entry : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t : Z) (T : list byte) (k : nat),
afn_pre SEGS B TCHECK_TABLE_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> amem_range t 400 -> off_img t 400 ->
(t + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= t) ->
length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
(k <= 8)%nat -> u_at T 384 4 = Z.of_nat k -> (forall i, (i < k)%nat -> 0 <= ct_rv T i <= 2) ->
st_ok_pi (fx := fq) SEGS VAL (EC regs T) (ss_ct k)
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_check_table)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ct_SH (EC regs T) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch t T k HPRE H10 Ht0 Ht8 AMt OIt DTt LT GT RAt Hk Hn Hroles.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite ct_spZ8 in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := EC regs T).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (ct_extra T)) q) by (intros q Hq; subst E; unfold EC; apply Eimg_low; exact Hq).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (ERv : forall i, (i < 8)%nat -> ew E (33 + i)%nat = Z_to_bv 64 (ct_rv T i)).
{ intros i Hi. rewrite EL by (unfold A_TEXT; lia).
destruct i as [|[|[|[|[|[|[|[|i]]]]]]]]; try (exfalso; lia);
[ exact (ew_Ereg_extra regs (ct_extra T) 1) | exact (ew_Ereg_extra regs (ct_extra T) 2)
| exact (ew_Ereg_extra regs (ct_extra T) 3) | exact (ew_Ereg_extra regs (ct_extra T) 4)
| exact (ew_Ereg_extra regs (ct_extra T) 5) | exact (ew_Ereg_extra regs (ct_extra T) 6)
| exact (ew_Ereg_extra regs (ct_extra T) 7) | exact (ew_Ereg_extra regs (ct_extra T) 8) ]. }
assert (E66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EC; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some q) = v).
{ intros q v Hq Hv. cbn [base_val]. rewrite Hq. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_ct. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ destruct k as [|[|[|[|[|[|[|[|[|kk]]]]]]]]]; try (exfalso; lia); vm_compute; reflexivity.
+ unfold ct_regions, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* unfold ct_tbl_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia).
split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia|]. split; [intros o Ho; lia|].
constructor.
-- apply (chunk_ok_val SEGS E _ t 384 4 (SLit (Z.of_nat k)) (Z.of_nat k));
[cbn [sv_denot]; reflexivity | zside | zside |].
rewrite <- Hn. change 384 with (Z.of_nat 384) at 1. apply (ct_u_val (w_H W) mem t T 384%nat LT GT ltac:(lia)).
-- apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (i & <- & Hi). apply in_seq in Hi.
unfold ct_role_chunk.
apply (chunk_ok_val SEGS E _ t (48 * Z.of_nat i + 8) 4 (SOff (33 + i) 0) (ct_rv T i));
[cbn [sv_denot]; rewrite (ERv i ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (ct_u4_range T (48 * Z.of_nat i + 8)); unfold ct_rv; zside | zside |].
unfold ct_rv. replace (48 * Z.of_nat i + 8) with (Z.of_nat (48 * i + 8)%nat) by lia.
apply (ct_u_val (w_H W) mem t T (48 * i + 8)%nat LT GT ltac:(lia)).
+ apply pairwise_disjoint_of_extents. unfold ct_regions, stack_region, got_regionP, bcell_regionP, ct_tbl_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OIt DTt. clear. unfold off_img, IMG_LO, IMG_TOP in *. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ct_facts f_atoms]. apply ct_atoms_app.
* cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, !unsigned_lit_small by (unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
pose proof (Z.div_mod t 8 ltac:(lia)) as Dt. rewrite Ht8 in Dt.
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 AMt Ht0 Ht8 Dt. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros.
repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia | match goal with |- ?g => idtac "FACTFAIL" g; fail end].
* apply (ct_atoms_roles E (fun _ => mkAF 0 2 0) (seq 0 k)). intros i Hi. apply in_seq in Hi.
unfold afact_ok. cbn [af_lo af_hi af_al2].
pose proof (Hroles i ltac:(lia)) as HRi.
rewrite (ERv i ltac:(lia)), unsigned_lit_small by lia.
rewrite Z.pow_0_r, Z.mod_1_r. split; [lia | split; [reflexivity | lia]].
- unfold sh_ok, ct_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 t 400 t 0 400 RAt).
+ unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia.
+ lia. + lia.
+ intros x Hx. revert AMt Hx. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros. lia.
Qed.
(* The walk of check_table by loop invariants, after the image-Y twin lib/Y/Prog/CheckTable.v:
   ct_inner is the inner loop at +0xbc (one bcmp call), ct_outer the outer loop at +0x80; the entry
   state ss_ct0 keeps the table size n as atom 33, so one walk covers every n. *)
Definition ct_tab_region0 : YP09.region := YP09.mkRegion (Some 10%nat) 0 400 0 0 [YP09.mkChunk 384 (CVal 4 (SOff 33 0))].
Definition ct_regions0 : smem := [stack_region 96; got_regionP; bcell_regionP 32; ct_tab_region0].
Definition ct_facts0 : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 8 (2 ^ 47 - 401) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (33%nat, mkAF 0 8 0)] [] [].
Definition ss_ct0 : sstate := mkSS AF_check_table sr_atoms ct_regions0 None ct_facts0.
Definition ct_extra0 (n : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; n].
Lemma ct_entry0 : forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (t n : Z) (T : list byte),
afn_pre SEGS B TCHECK_TABLE_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
getr regs 10 = w64 t -> 0 < t -> t mod 8 = 0 -> amem_range t 400 -> off_img t 400 ->
(t + 400 <= spZ regs - TCHECK_TABLE_STK \/ spZ regs <= t) ->
length T = 400%nat -> garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 ->
0 <= n <= 8 -> u_at T 384 4 = n ->
st_ok_pi (fx := fq) SEGS VAL (Eimg (Ereg regs (ct_extra0 n))) ss_ct0
(restrict (w_H W) (mkst (fx := fq) regs (Z_to_bv 64 (BASE + AF_check_table)) mem (seg_rom SEGS)))
/\ sh_ok SEGS CBx ct_SH (Eimg (Ereg regs (ct_extra0 n))) (mrestrict (w_H W) mem).
Proof.
intros fq ly S W regs mem md ch t n T HPRE H10 Ht0 Ht8 AMt OIt DTt LT GT RAt Hn Hn4.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite ct_spZ8 in Hstk, Hpres.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 66 ltac:(unfold disco_nobj; lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 1 ltac:(unfold disco_nobj; lia)) as HgotR.
unfold IMG_LO, IMG_TOP in HcellR, HgotR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ct_extra0 n))).
assert (EL : forall q, (q < A_TEXT)%nat -> ew E q = ew (Ereg regs (ct_extra0 n)) q) by (intros q Hq; subst E; apply Eimg_low; exact Hq).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E66 : ew E (A_OBJ 66) = Z_to_bv 64 (VAL (A_OBJ 66))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall q v, ew E q = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some q) = v).
{ intros q v Hq Hv. cbn [base_val]. rewrite Hq. apply unsigned_lit_small. exact Hv. }
split.
- unfold ss_ct0. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ct_regions0, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 66) 0) (VAL (A_OBJ 66)));
[cbn [sv_denot]; rewrite E66, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 66)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 66)) 0 8 (SOff 32 0) SHADOW_OFF);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* unfold ct_tab_region0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia).
split; [lia|]. split; [unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ t 384 4 (SOff 33 0) n);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite <- Hn4. change 384 with (Z.of_nat 384) at 1. apply (ct_u_val (w_H W) mem t T 384%nat LT GT ltac:(lia)).
+ apply pairwise_disjoint_of_extents. unfold ct_regions0, stack_region, got_regionP, bcell_regionP, ct_tab_region0, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite (VB 10%nat t E10) by (unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia).
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1o) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 66) (VAL (A_OBJ 66)) E66) by (pose proof (pa_val_range (A_OBJ 66)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR OIt DTt. clear. unfold off_img, IMG_LO, IMG_TOP in *. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ct_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, amem_range, kLowMemEnd, kHighMemEnd in *; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
pose proof (Z.div_mod t 8 ltac:(lia)) as Dt. rewrite Ht8 in Dt.
revert Hslo Hshi H47 Hceil C1 WS Hstk0 Hal16 AMt Ht0 Ht8 Dt Hn. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros.
repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia].
- unfold sh_ok, ct_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E CBx 10 t 400 t 0 400 RAt).
+ unfold U, CBx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF; lia.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold amem_range, kLowMemEnd, kHighMemEnd in AMt; lia.
+ lia. + lia.
+ intros x Hx. revert AMt Hx. clear. unfold amem_range, kLowMemEnd, kHighMemEnd, kHighMemBeg, SHADOW_OFF. intros. lia.
Qed.
Ltac ct_awr Usp :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha); cbn [In] in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
    first [ exfalso; lia
          | left; rewrite Usp in Ha; lia ] | ]); try destruct Hin.
Ltac ct_wr Usp :=
  let aw := fresh "aw" in let rw := fresh "rw" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros aw (rw & Hin & Ha);
  lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rw rs1) in Hin end;
  cbn [In] in Hin; cbv beta;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Ha;
     first [ exfalso; lia
           | rewrite Usp in Ha; lia ] | ]); try destruct Hin.
Lemma ct_kept_run : forall segs (H : word -> bool) E rs (m m' m0 : word -> option byte) lo hi,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m a = aview segs H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs H m' a = aview segs H m0 a.
Proof.
intros segs H E rs m m' m0 lo hi HF HW HK a Ha Hn. rewrite <- (HK a Ha Hn). apply aview_eq_of. apply HF.
rewrite unsigned_lit_small by lia. intros X. apply Hn. apply HW. exact X.
Qed.
Lemma ct_mbyte_of_aview : forall H (m m' : word -> option byte) a,
  aview SEGS H m' a = aview SEGS H m a -> mbyte SEGS (mrestrict H m') a = mbyte SEGS (mrestrict H m) a.
Proof.
intros H m m' a E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H m') a) as [b'|], (mbyte SEGS (mrestrict H m) a) as [b|]; cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma ct_garr8_kept : forall H (m m' : word -> option byte) p L,
  (forall a, p <= a < p + Z.of_nat (length L) -> aview SEGS H m' a = aview SEGS H m a) ->
  garr8 SEGS (mrestrict H m) p L -> garr8 SEGS (mrestrict H m') p L.
Proof.
intros H m m' p L HE HG j Hj. destruct (HG j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. cbn in Hk. pose proof (Hv k Hk) as Hb.
rewrite (ct_mbyte_of_aview H m m' (p + Z.of_nat j + Z.of_nat k)); [exact Hb|].
replace (p + Z.of_nat j + Z.of_nat k) with (p + (Z.of_nat j + Z.of_nat k)) by lia. apply HE. lia.
Qed.
Definition L_OUT : Z := 0x2a80.
Definition L_IN : Z := 0x2abc.
Definition L_EPI : Z := 0x2afc.
Definition LSTK : Z := 2 * ESTACK.
Definition CT_Bx : sv := SOff 19 0.
Definition sr_lit : list sv := sr_set sr_atoms 25%bv (SLit 3).
Definition LKEPT : list (bv 5) := [2; 3; 4; 8; 19; 20; 23; 25; 27]%bv.
Definition LKEPTA : list (bv 5) := [2; 3; 4; 8; 19; 20; 23; 27]%bv.
Definition ct_kept0 (regs0 regs : bvmap 5 word) : Prop := forall r, In r LKEPT -> getr regs r = getr regs0 r.
Definition ct_r0 (regs0 : bvmap 5 word) (sp0 t n : Z) : Prop :=
  getr regs0 2 = Z_to_bv 64 (sp0 - 96) /\ getr regs0 3 = w64 (as_gp B) /\ getr regs0 4 = w64 (as_tp B) /\
  getr regs0 8 = Z_to_bv 64 t /\ getr regs0 19 = Z_to_bv 64 SHADOW_OFF /\ getr regs0 20 = Z_to_bv 64 n /\
  getr regs0 23 = Z_to_bv 64 n /\ getr regs0 25 = Z_to_bv 64 3.
Definition ct_tab (W : world SEGS) (sp0 t : Z) (T : list byte) (mem : word -> option byte) : Prop :=
  0 < t /\ t mod 8 = 0 /\ length T = 400%nat /\ garr8 SEGS (mrestrict (w_H W) mem) t (map bv_unsigned T) /\
  amem_range t 400 /\ range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF t 400 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) t 400 /\ (t + 400 <= sp0 - TCHECK_TABLE_STK \/ sp0 <= t) /\
  tbl_T1 T /\ tbl_T2 T /\ tbl_T3 T.
Definition ct_mem (W : world SEGS) (sp0 : Z) (mem memc : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - TCHECK_TABLE_STK <= a < sp0) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a.
Definition ct_lpost (fq : YK11.FPState) (regs0 : bvmap 5 word) (W : world SEGS) (sp0 : Z) (mem : word -> option byte)
  (lyc : alayout) (Sc : astate) (memL : word -> option byte) (mdL : Model) : world SEGS -> config -> Prop :=
  fun W' c' => W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + L_EPI)) mem' (seg_rom SEGS)) md' /\
    ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W mem' md' 0 /\
    ct_kept0 regs0 regs' /\ ct_mem W sp0 mem mem'.
Lemma ct_kept0_step : forall regs0 regs regs', ct_kept0 regs0 regs -> getr regs0 25 = Z_to_bv 64 3 ->
  (forall r, In r LKEPTA -> getr regs' r = getr regs r) -> getr regs' 25 = Z_to_bv 64 3 -> ct_kept0 regs0 regs'.
Proof.
intros regs0 regs regs' HK H25 HA G25 r Hr. cbv [LKEPT In] in Hr.
repeat (destruct Hr as [<-|Hr]; [first [rewrite G25; symmetry; exact H25
  | rewrite HA by (cbv; tauto); apply HK; cbv; tauto] |]). destruct Hr.
Qed.
Lemma ct_denot48 : forall E nb ni b x, ew E nb = Z_to_bv 64 b -> ew E ni = Z_to_bv 64 x -> 0 <= b -> 0 <= x < 8 -> b + 48 * x < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff nb 0) (SMd M_MUL (SOff ni 0) (SLit 48))) = Z_to_bv 64 (b + 48 * x).
Proof.
intros E nb ni b x Hb Hx Rb Rx Rbx. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit, (U_atom E ni x Hx), (U_atom E nb b Hb) by lia.
rewrite (zcanon_id 48) by (unfold M64; lia). rewrite (zcanon_id (x * 48)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ct_memc : forall W sp0 t T mem memc, ct_tab W sp0 t T mem -> ct_mem W sp0 mem memc -> alloc_ceiling <= sp0 - TCHECK_TABLE_STK ->
  garr8 SEGS (mrestrict (w_H W) memc) t (map bv_unsigned T) /\ range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF t 400 /\
  shadow_hull_vis (aview SEGS (w_H W) memc) t 400.
Proof.
intros W sp0 t T mem memc (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3) HM Hc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
split; [|split].
- apply (ct_garr8_kept (w_H W) mem memc t); [|exact HGT].
  intros a Ha. rewrite length_map, HLT in Ha. apply HM; lia.
- apply (range_addressable_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) memc) (sp0 - TCHECK_TABLE_STK) sp0 t 400); [intros s Hs1 Hs2; apply HM; assumption | lia | lia | lia | exact HRA].
- apply (shadow_hull_vis_kept_win (aview SEGS (w_H W) mem) (aview SEGS (w_H W) memc) (sp0 - TCHECK_TABLE_STK) sp0 t 400); [intros s Hs1 Hs2; apply HM; assumption | lia | lia | lia | lia | exact HSV].
Qed.
Lemma ct_bcmp_ne : forall W sp0 t T mem memT i j (v : word),
  ct_tab W sp0 t T mem -> garr8 SEGS (mrestrict (w_H W) memT) t (map bv_unsigned T) -> 0 <= i -> i < j -> j < n_of T ->
  (v = w64 0 <-> forall k, 0 <= k < 6 -> aview SEGS (w_H W) memT (t + 48 * i + k) = aview SEGS (w_H W) memT (t + 48 * j + k)) ->
  v <> w64 0.
Proof.
intros W sp0 t T mem memT i j v Htab HG Hi Hij Hjn Hcmp Hv.
destruct Htab as (_ & _ & HLT & _ & _ & _ & _ & _ & T1 & _ & T3). unfold tbl_T1 in T1.
apply (T3 i j Hi Hij Hjn). apply (proj1 (ct_mac2 (w_H W) memT t T i j HLT ltac:(lia) ltac:(lia) HG)). exact (proj1 Hcmp Hv).
Qed.
Lemma ct_bv_pos : forall v : word, v <> w64 0 -> 1 <= bv_unsigned v <= 2 ^ 64 - 1.
Proof.
intros v Hv. pose proof (bv_unsigned_in_range 64 v) as R. change (bv_modulus 64) with (2 ^ 64) in R.
destruct (Z.eq_dec (bv_unsigned v) 0) as [E0|E0]; [|lia]. exfalso. apply Hv. apply bv_eq. rewrite E0. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Definition in_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 1 (2 ^ 47 - 401) 3)] [] [].
Definition ss_in : sstate := mkSS L_IN sr_lit [] None in_facts.
Ltac ct_fin HS HJ Kn HKP :=
  pmkst HS; apply SRr_ret; split; [reflexivity|];
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] => exists (ms_regs msx), (ms_mem msx), mdx end;
  split; [reflexivity|]; split; [exact HJ|]; split; [exact HKP | exact Kn].
(* The inner loop at L_IN (+0xbc): s1 (x9) = t + 48 i, s2 (x18) = t + 48 j, s10 (x26) = n - j counts down;
   s5 (x21) = i + 1, s6 (x22) = t + 48 (i + 1) and s8 (x24) = n - 1 - i pass through to the outer loop. *)
Lemma ct_inner : forall (fq : YK11.FPState) (k : nat) (j i : Z) W sp0 t T mem lyc Sc memL mdL (regs0 regs : bvmap 5 word) memc mdc,
  ct_tab W sp0 t T mem -> ct_r0 regs0 sp0 t (n_of T) ->
  Z.of_nat k = n_of T - j -> 0 <= i -> i + 1 <= j < n_of T ->
  ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc mdc 0 ->
  ct_mem W sp0 mem memc -> ct_kept0 regs0 regs ->
  getr regs 9 = Z_to_bv 64 (t + 48 * i) -> getr regs 18 = Z_to_bv 64 (t + 48 * j) ->
  getr regs 21 = Z_to_bv 64 (i + 1) -> getr regs 22 = Z_to_bv 64 (t + 48 * (i + 1)) ->
  getr regs 24 = Z_to_bv 64 (n_of T - 1 - i) -> getr regs 26 = Z_to_bv 64 (n_of T - j) ->
  (forall (regs' : bvmap 5 word) memc' mdc', i + 1 < n_of T ->
     ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc' mdc' 0 -> ct_mem W sp0 mem memc' ->
     ct_kept0 regs0 regs' -> getr regs' 21 = Z_to_bv 64 (i + 1) -> getr regs' 22 = Z_to_bv 64 (t + 48 * (i + 1 + 1)) ->
     getr regs' 24 = Z_to_bv 64 (n_of T - 1 - (i + 1)) ->
     SRr SEGS W (mkCfg (mkst (fx := fq) regs' (Z_to_bv 64 (BASE + L_OUT)) memc' (seg_rom SEGS)) mdc') (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL)) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + L_IN)) memc (seg_rom SEGS)) mdc) (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL).
Proof.
intros fq k. induction k as [|k IH]; intros j i W sp0 t T mem lyc Sc memL mdL regs0 regs memc mdc Htab H0 Hk Hi Hj HJ HM HK G9 G18 G21 G22 G24 G26 HOUT; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Htab as (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3).
pose proof H0 as (R2 & R3 & R4 & R8 & R19 & R20 & R23 & R25).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLS : LSTK = 8192) by reflexivity. assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
unfold tbl_T1 in T1. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (Q2 : getr regs 2 = Z_to_bv 64 (sp0 - 96)) by (rewrite (HK 2%bv ltac:(cbv; tauto)); exact R2).
assert (Q3 : getr regs 3 = w64 (as_gp B)) by (rewrite (HK 3%bv ltac:(cbv; tauto)); exact R3).
assert (Q4 : getr regs 4 = w64 (as_tp B)) by (rewrite (HK 4%bv ltac:(cbv; tauto)); exact R4).
assert (Q8 : getr regs 8 = Z_to_bv 64 t) by (rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8).
assert (Q23 : getr regs 23 = Z_to_bv 64 (n_of T)) by (rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23).
assert (Q25 : getr regs 25 = Z_to_bv 64 3) by (rewrite (HK 25%bv ltac:(cbv; tauto)); exact R25).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 96)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Q2).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact Q8).
assert (E9 : ew E 9 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact G9).
assert (E18 : ew E 18 = Z_to_bv 64 (t + 48 * j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact G18).
assert (E21 : ew E 21 = Z_to_bv 64 (i + 1)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact G21).
assert (E22 : ew E 22 = Z_to_bv 64 (t + 48 * (i + 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact G22).
assert (E23 : ew E 23 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact Q23).
assert (E24 : ew E 24 = Z_to_bv 64 (n_of T - 1 - i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact G24).
assert (E26 : ew E 26 = Z_to_bv 64 (n_of T - j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact G26).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_in (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_IN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_in. apply pa_entry_st_ok_full.
  - rewrite HE. unfold sr_lit. repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]). apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - exact I.
  - split; [|split; [exact I | exact I]]. cbn [in_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, E8, !unsigned_lit_small by lia.
    change (2 ^ 4) with 16. change (2 ^ 3) with 8.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia]. }
assert (SHOK : sh_ok SEGS CT_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HE.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)).
paj_run_tok RUN HS HJ SHOK CBspan; [ct_awr Usp |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) HM) as K1. clear HF HFr HG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (1%bv : bv 5) Rra.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
destruct (ct_memc W sp0 t T mem (ms_mem ms) Htab K1 ltac:(lia)) as (HGm & HRAm & HSVm).
eapply SRr_bind.
{ eapply (aj_bcmp_at (fx := fq) SEGS B LAWS Hsegs (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W (ms_regs ms) (ms_mem ms) LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc _ 0
    (t + 48 * i) (t + 48 * j) 6 0 (Z_to_bv 64 (BASE + 10956)) HJ).
  - rewrite Ra0, E9. reflexivity.
  - rewrite Ra1, E18. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia. - lia. - lia. - lia. - lia.
  - unfold spZ. rewrite Rsp, Usp. lia.
  - reflexivity. - lia. - rewrite HLS. lia.
  - rewrite Rgp, E3. exact Q3.
  - rewrite Rtp, E4. exact Q4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply (ct_aview_some (w_H W) (ms_mem ms) t T a HGm); rewrite HLT; cbn; lia | unfold spZ; rewrite Rsp, Usp, HES; lia].
  - intros a Ha. split; [apply (ct_aview_some (w_H W) (ms_mem ms) t T a HGm); rewrite HLT; cbn; lia | unfold spZ; rewrite Rsp, Usp, HES; lia].
  - intros a Ha. rewrite HES. lia.
  - intros a Ha. rewrite HES. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd. lia.
  - apply (range_addressable_sub _ _ t 400); [exact HRAm | lia | lia].
  - intros _. apply (ct_hull_sub _ t 400); [exact HSVm | lia | lia | lia | lia].
  - apply (range_addressable_sub _ _ t 400); [exact HRAm | lia | lia].
  - intros _. apply (ct_hull_sub _ t 400); [exact HSVm | lia | lia | lia | lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & Hpr2).
pose proof (ct_bcmp_ne W sp0 t T mem (ms_mem ms) i j v Htab HGm Hi ltac:(lia) ltac:(lia) Hcmp) as V0.
assert (K2 : ct_mem W sp0 mem mem2).
{ intros a Ha Hn. rewrite (Hfr a Ha) by (rewrite HES; lia). exact (K1 a Ha Hn). }
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 (@nil nat) HS2.
specialize (HS2 (Forall_nil _)). clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 34 _) as Eh eqn:HEh in HS.
assert (HEIh : img_env VAL A_LIM Eh) by (rewrite HEh; apply img_env_havoc; [assumption | cbv; lia]).
assert (OLD : forall n, (n < 34)%nat -> ew Eh n = ew E n) by (intros n Hn; rewrite HEh; apply ew_havoc_old; exact Hn).
assert (HAEh : env_agree 32 (Ereg regs []) Eh) by (rewrite HEh; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEh.
prreg HS (10%bv : bv 5) Rv.
assert (F38 : afact_ok Eh 38 (mkAF 1 (2 ^ 64 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite <- Rv, Hv. pose proof (ct_bv_pos v V0). rewrite Z.pow_0_r, Z.mod_1_r. lia. }
apply (st_ok_pi_add_fact Eh _ _ 38 _ HS) in F38. clear HS. rename F38 into HS.
assert (SHOK2 : sh_ok SEGS CT_Bx [] Eh (mrestrict (w_H W) mem2)) by constructor.
assert (Usp2 : bv_unsigned (ew Eh 2) = sp0 - 96) by (rewrite OLD by lia; exact Usp).
assert (F18 : ew Eh 18 = Z_to_bv 64 (t + 48 * j)) by (rewrite OLD by lia; exact E18).
assert (F21 : ew Eh 21 = Z_to_bv 64 (i + 1)) by (rewrite OLD by lia; exact E21).
assert (F22 : ew Eh 22 = Z_to_bv 64 (t + 48 * (i + 1))) by (rewrite OLD by lia; exact E22).
assert (F23 : ew Eh 23 = Z_to_bv 64 (n_of T)) by (rewrite OLD by lia; exact E23).
assert (F24 : ew Eh 24 = Z_to_bv 64 (n_of T - 1 - i)) by (rewrite OLD by lia; exact E24).
assert (F26 : ew Eh 26 = Z_to_bv 64 (n_of T - j)) by (rewrite OLD by lia; exact E26).
paj_run_tok RUN HS HJ2 SHOK2 CBspan; [ct_awr Usp2 |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K2) as K3. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK2 CBspan.
- rewrite branch_ne_U, (U_atom_off Eh 26 (n_of T - j) (-1) F26 ltac:(lia) ltac:(lia)), U_lit in Hc by lia.
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ2 SHOK2 CBspan L_IN; [ct_awr Usp2 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K3) as K4. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] (LKEPTA ++ [9; 21; 22; 24]%bv) HS HAEh ltac:(vm_compute; reflexivity)) as HKk.
  cbn [ms_regs restrict] in HKk.
  prreg HS (18%bv : bv 5) N18. prreg HS (26%bv : bv 5) N26. prreg HS (25%bv : bv 5) N25.
  rewrite F18, unsigned_lit_small in N18 by lia. rewrite F26, unsigned_lit_small in N26 by lia.
  pmkst HS.
  apply (IH (j + 1) i W sp0 t T mem lyc Sc memL mdL regs0 _ _ _ Htab H0 ltac:(lia) Hi ltac:(lia) HJ2 K4).
  + apply (ct_kept0_step regs0 regs); [exact HK | exact R25 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N25].
  + rewrite (HKk 9%bv ltac:(cbv; tauto)). exact G9.
  + rewrite N18. f_equal. lia.
  + rewrite (HKk 21%bv ltac:(cbv; tauto)). exact G21.
  + rewrite (HKk 22%bv ltac:(cbv; tauto)). exact G22.
  + rewrite (HKk 24%bv ltac:(cbv; tauto)). exact G24.
  + rewrite N26. f_equal. lia.
  + exact HOUT.
- rewrite branch_ne_U, (U_atom_off Eh 26 (n_of T - j) (-1) F26 ltac:(lia) ltac:(lia)), U_lit in Hc by lia.
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ2 SHOK2 CBspan; [ct_awr Usp2 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K3) as K4. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK2 CBspan.
  + exfalso. rewrite branch_eq_U, (U_atom Eh 21 (i + 1) F21 ltac:(lia)), (U_atom Eh 23 (n_of T) F23 ltac:(lia)) in Hc0.
    apply Z.eqb_eq in Hc0. lia.
  + paj_run_to_tok RUNTO HS HJ2 SHOK2 CBspan L_OUT; [ct_awr Usp2 |].
    pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp2) K4) as K5. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] (LKEPTA ++ [21]%bv) HS HAEh ltac:(vm_compute; reflexivity)) as HKk.
    cbn [ms_regs restrict] in HKk.
    prreg HS (22%bv : bv 5) N22. prreg HS (24%bv : bv 5) N24. prreg HS (25%bv : bv 5) N25.
    rewrite F22, unsigned_lit_small in N22 by lia. rewrite F24, unsigned_lit_small in N24 by lia.
    pmkst HS.
    apply (HOUT _ _ _ ltac:(lia) HJ2 K5).
    * apply (ct_kept0_step regs0 regs); [exact HK | exact R25 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N25].
    * rewrite (HKk 21%bv ltac:(cbv; tauto)). exact G21.
    * rewrite N22. f_equal. lia.
    * rewrite N24. f_equal. lia.
Qed.
(* The outer loop at L_OUT (+0x80): s5 (x21) = i, s6 (x22) = t + 48 (i + 1), s8 (x24) = n - 1 - i; the table
   entry i is region 32 (atom 32 = t + 48 i, aliased to s0 + 48 s5), its role at offset 8 is atom 33. *)
Definition out_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 48 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 33 0))].
Definition out_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF 1 (2 ^ 47 - 401) 3); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
           (21%nat, mkAF 0 7 0); (32%nat, mkAF 1 (2 ^ 47 - 65) 3); (33%nat, mkAF 0 2 0)] []
          [(SAlu ALU_ADD (SOff 8 0) (SMd M_MUL (SOff 21 0) (SLit 48)), SOff 32 0)].
Definition ss_out : sstate := mkSS L_OUT sr_lit [out_region] None out_facts.
Definition out_extra (t i r : Z) : list word := map (Z_to_bv 64) [t + 48 * i; r].
Lemma ct_outer : forall (fq : YK11.FPState) (k : nat) (i : Z) W sp0 t T mem lyc Sc memL mdL (regs0 regs : bvmap 5 word) memc mdc,
  ct_tab W sp0 t T mem -> ct_r0 regs0 sp0 t (n_of T) ->
  Z.of_nat k = n_of T - i -> 0 <= i < n_of T ->
  ajournal SEGS B LSTK (sp0 - 96) [] lyc Sc W memL mdL [] lyc Sc W memc mdc 0 ->
  ct_mem W sp0 mem memc -> ct_kept0 regs0 regs ->
  getr regs 21 = Z_to_bv 64 i -> getr regs 22 = Z_to_bv 64 (t + 48 * (i + 1)) -> getr regs 24 = Z_to_bv 64 (n_of T - 1 - i) ->
  SRr SEGS W (mkCfg (mkst (fx := fq) regs (Z_to_bv 64 (BASE + L_OUT)) memc (seg_rom SEGS)) mdc) (ct_lpost fq regs0 W sp0 mem lyc Sc memL mdL).
Proof.
intros fq k. induction k as [|k IH]; intros i W sp0 t T mem lyc Sc memL mdL regs0 regs memc mdc Htab H0 Hk Hi HJ HM HK G21 G22 G24; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof Htab as (Ht0 & Ht8 & HLT & HGT & HAM & HRA & HSV & HOW & T1 & T2 & T3).
pose proof H0 as (R2 & R3 & R4 & R8 & R19 & R20 & R23 & R25).
pose proof HJ as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop) & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLS : LSTK = 8192) by reflexivity. assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity. assert (HES : ESTACK = 4096) by reflexivity.
unfold tbl_T1 in T1. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HAM.
assert (Q2 : getr regs 2 = Z_to_bv 64 (sp0 - 96)) by (rewrite (HK 2%bv ltac:(cbv; tauto)); exact R2).
assert (Q8 : getr regs 8 = Z_to_bv 64 t) by (rewrite (HK 8%bv ltac:(cbv; tauto)); exact R8).
assert (Q19 : getr regs 19 = Z_to_bv 64 SHADOW_OFF) by (rewrite (HK 19%bv ltac:(cbv; tauto)); exact R19).
assert (Q20 : getr regs 20 = Z_to_bv 64 (n_of T)) by (rewrite (HK 20%bv ltac:(cbv; tauto)); exact R20).
assert (Q23 : getr regs 23 = Z_to_bv 64 (n_of T)) by (rewrite (HK 23%bv ltac:(cbv; tauto)); exact R23).
assert (Q25 : getr regs 25 = Z_to_bv 64 3) by (rewrite (HK 25%bv ltac:(cbv; tauto)); exact R25).
destruct (ct_memc W sp0 t T mem memc Htab HM ltac:(lia)) as (HGc & HRAc & HSVc).
pose proof (ct_roles_bound T (Z.to_nat (n_of T)) T2 ltac:(lia) (Z.to_nat i) ltac:(lia)) as RR.
unfold ct_rv in RR. rewrite Z2Nat.id in RR by lia.
pose proof (ct_u_val (w_H W) memc t T (Z.to_nat (48 * i + 8)) HLT HGc ltac:(lia)) as VR.
rewrite Z2Nat.id in VR by lia.
remember (u_at T (48 * i + 8) 4) as rv eqn:Hrv.
remember (Eimg (Ereg regs (out_extra t i rv))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (out_extra t i rv)) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (sp0 - 96)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Q2).
assert (E8 : ew E 8 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 8 8%bv eq_refl); exact Q8).
assert (E19 : ew E 19 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact Q19).
assert (E20 : ew E 20 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact Q20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact G21).
assert (E22 : ew E 22 = Z_to_bv 64 (t + 48 * (i + 1))) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact G22).
assert (E23 : ew E 23 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 23 23%bv eq_refl); exact Q23).
assert (E24 : ew E 24 = Z_to_bv 64 (n_of T - 1 - i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact G24).
assert (E32 : ew E 32 = Z_to_bv 64 (t + 48 * i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite E2; apply unsigned_lit_small; lia).
assert (A32 : (t + 48 * i) mod 8 = 0) by (replace (t + 48 * i) with (t + (6 * i) * 8) by lia; rewrite Z_mod_plus_full; exact Ht8).
assert (HS : st_ok_pi SEGS VAL E ss_out (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + L_OUT)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_out. apply pa_entry_st_ok_full.
  - rewrite HE. unfold sr_lit. repeat (apply regs_ok_pin; [| intros X; discriminate X | cbn [sv_denot]; assumption]). apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, out_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (t + 48 * i) 8 4 _ rv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    replace (t + 48 * i + 8) with (t + (48 * i + 8)) by lia. exact VR.
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [exact I|]].
    + cbn [out_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite Usp, E8, E19, E21, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia].
    + cbn [out_facts f_alias alias_ok]. split; [|exact I].
      rewrite (ct_denot48 E 8 21 t i E8 E21) by lia. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (SHOK : sh_ok SEGS CT_Bx [] E (mrestrict (w_H W) memc)) by constructor.
clear HE.
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS). pose (BR := paj_branch (fx := fq) (PI := PI)).
paj_run_tok RUN HS HJ SHOK CBspan;
  [ eapply (obl_of_range SEGS (w_H W) memc E CT_Bx _ 4 t 400 HRAc);
    [ unfold CT_Bx; rewrite (U_atom E 19 SHADOW_OFF E19) by (unfold SHADOW_OFF; lia); reflexivity
    | rewrite (U_atom_off E 32 (t + 48 * i) 8 E32) by lia; lia
    | rewrite (U_atom_off E 32 (t + 48 * i) 8 E32) by lia; lia ]
  | ct_awr Usp | ].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) HM) as K1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK CBspan.
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F21 : ew Ex 21 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E21);
    assert (F20 : ew Ex 20 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E20);
    rewrite branch_geu_U, (U_atom_off Ex 21 i 1 F21 ltac:(lia) ltac:(lia)), (U_atom Ex 20 (n_of T) F20 ltac:(lia)) in Hc end.
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_tok RUN HS HJ SHOK CBspan; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK CBspan.
  + paj_run_to_tok RUNTO HS HJ SHOK CBspan L_EPI; [ct_awr Usp |].
    pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K2) as K3. clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LKEPTA HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKk.
    cbn [ms_regs restrict] in HKk.
    prreg HS (25%bv : bv 5) N25.
    ct_fin HS HJ K3 (ct_kept0_step regs0 regs _ HK R25 HKk N25).
  + exfalso. lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
      assert (F21b : ew Ex 21 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E21);
      assert (F23b : ew Ex 23 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E23);
      rewrite branch_eq_U, (U_atom_off Ex 21 i 1 F21b ltac:(lia) ltac:(lia)), (U_atom Ex 23 (n_of T) F23b ltac:(lia)) in Hc0 end.
    apply Z.eqb_neq in Hc0. lia.
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F21 : ew Ex 21 = Z_to_bv 64 i) by (cbn [ew ewset Nat.eqb]; exact E21);
    assert (F20 : ew Ex 20 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E20);
    rewrite branch_geu_U, (U_atom_off Ex 21 i 1 F21 ltac:(lia) ltac:(lia)), (U_atom Ex 20 (n_of T) F20 ltac:(lia)) in Hc end.
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK CBspan L_IN; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (sp0 - TCHECK_TABLE_STK) sp0 HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ (LKEPTA ++ [22; 24]%bv) HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKk.
  cbn [ms_regs restrict] in HKk.
  prreg HS (9%bv : bv 5) N9. prreg HS (18%bv : bv 5) N18. prreg HS (21%bv : bv 5) N21. prreg HS (26%bv : bv 5) N26.
  prreg HS (25%bv : bv 5) N25.
  rewrite E32 in N9. rewrite E22 in N18. rewrite E21, unsigned_lit_small in N21 by lia. rewrite E24 in N26.
  pmkst HS.
  apply (ct_inner fq (Z.to_nat (n_of T - (i + 1))) (i + 1) i W sp0 t T mem lyc Sc memL mdL regs0 _ _ _ Htab H0 ltac:(lia) ltac:(lia) ltac:(lia) HJ K2).
  + apply (ct_kept0_step regs0 regs); [exact HK | exact R25 | intros r Hr; apply HKk; apply in_app_iff; left; exact Hr | exact N25].
  + exact N9.
  + exact N18.
  + exact N21.
  + rewrite (HKk 22%bv ltac:(cbv; tauto)). exact G22.
  + rewrite (HKk 24%bv ltac:(cbv; tauto)). exact G24.
  + rewrite N26. f_equal. lia.
  + intros regs' memc' mdc' Hlt HJ' HM' HK' H21' H22' H24'.
    exact (IH (i + 1) W sp0 t T mem lyc Sc memL mdL regs0 regs' memc' mdc' Htab H0 ltac:(lia) ltac:(lia) HJ' HM' HK' H21' H22' H24').
Qed.
Definition CT_CLOB : list (bv 5) := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 21; 22; 24; 26; 28; 29; 30; 31]%bv.
Lemma ct_clob_kept : forall r : bv 5, reg_in r CT_CLOB = false -> r = 0%bv \/ In r LKEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.
Theorem pb_check_table : tcheck_table_spec.
Proof.
unfold tcheck_table_spec.
intros fq ly S W regs mem md ch t T HPRE HRO H10 Ht0 Ht8 Ht63 LT GT AMt RAt SHt DTt OIt T1 T2 T3.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (ct_ncase T T1) as (k & Hk & Hnof & Hn4).
assert (Hn : 0 <= n_of T <= 8) by exact T1.
assert (Hn4' : u_at T 384 4 = n_of T) by lia.
destruct (ct_entry0 fq ly S W regs mem md ch t (n_of T) T HPRE H10 Ht0 Ht8 AMt OIt DTt LT GT RAt Hn Hn4') as [HS SHOK].
clear k Hk Hnof Hn4.
pose proof (ajournal_init SEGS B TCHECK_TABLE_STK [] ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch HPRE) as HJ.
rewrite ct_spZ8 in HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite ct_spZ8 in Hstk, Hpres.
assert (N1 : (1%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N3 : (3%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
assert (N4 : (4%bv : bv 5) <> 8%bv) by (intros X; apply (f_equal bv_unsigned) in X; discriminate X).
unfold raZ in Hra4. rewrite (ct_getr8 regs _ 1 N1) in Hra, Hra4. rewrite (ct_getr8 regs _ 3 N3) in Hgp. rewrite (ct_getr8 regs _ 4 N4) in Htp.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TCHECK_TABLE_STK = 8288) by reflexivity.
remember (Eimg (Ereg regs (ct_extra0 (n_of T)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ct_extra0 (n_of T))) E) by (rewrite HE; split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 t) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (n_of T)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_check_table)) with (Z_to_bv 64 (BASE + AF_check_table)).
pose (RUN := paj_run (fx := fq) B LAWS). pose (RUNTO := paj_run_to (fx := fq) B LAWS).
pose (BR := paj_branch (fx := fq) (PI := PI)). pose (RET := paj_ret_at (fx := fq) (PL := PL_disco) (PI := PI)).
assert (K0 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - TCHECK_TABLE_STK <= a < spZ regs) -> aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by reflexivity.
paj_run_tok RUN HS HJ SHOK CBspan; [ct_awr Usp |].
pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K0) as K1. clear HF HFr HG K0.
psrr_branch_tok RUN BR HS SHOK CBspan.
- paj_run_tok RUN HS HJ SHOK CBspan; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG K1.
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold tcheck_table_post. apply apost_base_same_fx.
  eexists ly, S, _, _, _.
  split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ct_extra0 (n_of T)) HS); [env_agree_chain HAE | vm_compute; reflexivity]|].
  split; [apply Permutation_refl | exact K2].
- lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (F33 : ew Ex 33 = Z_to_bv 64 (n_of T)) by (cbn [ew ewset Nat.eqb]; exact E33);
    rewrite branch_eq_U, (U_atom Ex 33 (n_of T) F33 ltac:(lia)), U_lit in Hc by lia end.
  apply Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK CBspan L_OUT; [ct_awr Usp |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp) K1) as K2. clear HF HFr HG K1.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [3; 4; 27]%bv HS ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKm.
  cbn [ms_regs restrict] in HKm.
  prreg HS (2%bv : bv 5) M2. prreg HS (8%bv : bv 5) M8. prreg HS (19%bv : bv 5) M19. prreg HS (20%bv : bv 5) M20.
  prreg HS (21%bv : bv 5) M21. prreg HS (22%bv : bv 5) M22. prreg HS (23%bv : bv 5) M23.
  prreg HS (24%bv : bv 5) M24. prreg HS (25%bv : bv 5) M25.
  rewrite Usp in M2. replace (spZ regs + -96) with (spZ regs - 96) in M2 by lia.
  rewrite E10 in M8. rewrite E32 in M19. rewrite E33 in M20. rewrite E33 in M23.
  rewrite E10, unsigned_lit_small in M22 by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMt; lia).
  rewrite E33, unsigned_lit_small in M24 by lia.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ ?msX) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ss) got_regionP) in
    pose proof (st_ok_pi_submem E ss (restrict (w_H W) msX) [r0] HS ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity)) as HS1 end.
  clear HS. rename HS1 into HS.
  lazymatch goal with |- SRr _ _ (mkCfg ?msX ?mdX) _ =>
    pose proof (ajournal_sub_init SEGS B TCHECK_TABLE_STK (spZ regs) [] ly S W mem md [] ly S W (ms_mem msX) mdX 0 LSTK (spZ regs - 96) [] (-96) HJ
      ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(unfold LSTK, ESTACK; lia) ltac:(rewrite WS; unfold LSTK, ESTACK; lia)) as HJL;
    assert (Htab : ct_tab W (spZ regs) t T mem) by exact (conj Ht0 (conj Ht8 (conj LT (conj GT (conj AMt (conj RAt (conj SHt (conj DTt (conj T1 (conj T2 T3))))))))));
    assert (H0 : ct_r0 (ms_regs msX) (spZ regs) t (n_of T)) by
      (repeat split; first [exact M2 | rewrite (HKm 3%bv ltac:(cbv; tauto)); exact Hgp | rewrite (HKm 4%bv ltac:(cbv; tauto)); exact Htp
        | exact M8 | exact M19 | exact M20 | exact M23 | exact M25]) end.
  pmkst HS.
  eapply SRr_bind.
  { apply (ct_outer fq (Z.to_nat (n_of T)) 0 W (spZ regs) t T mem ly S _ _ _ _ _ _ Htab H0 ltac:(lia) ltac:(lia) HJL K2
      (fun r _ => eq_refl) M21 ltac:(rewrite M22; f_equal; lia) ltac:(rewrite M24; f_equal; lia)). }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJL3 & HK3 & HM3).
  pose proof (ajournal_sub SEGS B LAWS Hsegs _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 LSTK (spZ regs - 96) [] [] ly S W mem3 md3 0 HJ HJL3
    ltac:(rewrite WS; unfold LSTK, ESTACK; lia) ltac:(lia)) as HJ3.
  match type of HJ3 with ?P -> _ => assert (HFP : P); [|specialize (HJ3 HFP); clear HFP] end.
  { intros a Ha. exfalso. exact (inFP_nil _ Ha). }
  cbn [app] in HJ3. replace (0 + 0) with 0 in HJ3 by reflexivity.
  jafter_stretch_pi HS 34%nat regs3 (mrestrict (w_H W) mem3) CT_CLOB L_EPI HS2.
  match type of HS2 with ?P -> ?Q -> _ => assert (HP : P); [|assert (HQ : Q); [|specialize (HS2 HP HQ); clear HP HQ]] end.
  { intros r0 Hr0. cbn [ms_regs restrict]. destruct (ct_clob_kept r0 Hr0) as [-> | Hin]; [rewrite !getr_zero; reflexivity | exact (HK3 r0 Hin)]. }
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
    eapply (region_kept_stack_sub SEGS B E); [exact HJL3 | exact HJ3 | exact Usp | lia | rewrite WS; lia | lia | lia | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 34 _) as Et eqn:HEt in HS.
  assert (HEIt : img_env VAL A_LIM Et) by (rewrite HEt; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDt : forall n, (n < 34)%nat -> ew Et n = ew E n) by (intros n Hn0; rewrite HEt; apply ew_havoc_old; exact Hn0).
  assert (HAEt : env_agree 32 (Ereg regs (ct_extra0 (n_of T))) Et) by (rewrite HEt; apply env_agree_havoc_ge; [lia | exact HAE]).
  clear HEt.
  assert (Usp3 : bv_unsigned (ew Et 2) = spZ regs) by (rewrite OLDt by lia; exact Usp).
  assert (SHOK3 : sh_ok SEGS CBx [] Et (mrestrict (w_H W) mem3)) by constructor.
  paj_run_tok RUN HS HJ3 SHOK3 CBspan; [ct_awr Usp3 |].
  pose proof (ct_kept_run SEGS (w_H W) _ _ _ _ mem (spZ regs - TCHECK_TABLE_STK) (spZ regs) HFr ltac:(ct_wr Usp3) HM3) as K4. clear HF HFr HG.
  prreg HS (1%bv : bv 5) R1.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold tcheck_table_post. apply apost_base_same_fx.
  eexists ly, S, _, _, _.
  split; [cbn [ms_regs]; rewrite R1, OLDt, E1, Hra by lia; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ3|].
  split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (ct_extra0 (n_of T)) HS); [env_agree_chain HAEt | vm_compute; reflexivity]|].
  split; [apply Permutation_refl | exact K4].
Qed.
End h.
End f.
End d.
