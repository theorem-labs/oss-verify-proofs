(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PWorldH8.v, with its module paths changed; 73 of its 297 lines of code are new or changed and 183 lines of the source are left out. *)
(* w_H8 (YA0n.v:25) for a start-up world whose hidden set has the shape of W1's (lib/{A,B}/AD2i.v:506):
   hull1 a = hid a && negb (argH E a) && negb (sliverb sp a).  On the two shadow bands, such a set is constant on
   each 8-byte-aligned word (H1_H8), under the side conditions below.  The start-up set (lib/{A,B}/AD2i.v,
   generated) applies H1_H8 at its W1 (AD2i.v:767) and discharges the side conditions for its own image; this file
   proves the lemma once, for any atable, argH, env, hand-off state, model and sp.

   Mirror of omx-clap-core/fuzz_manifest's lib/A/FMworldH8.v (file sha256 91a975126209; donor not released), where fm's facts about its
   own image are hypotheses here:
   - Hband: fm's band_facts (FMworldH8.v:184): each band byte is mapped, not noaccess, and lazy;
   - Hhull: the image hull ends at or below kLowShadowBeg (fm: img_hi TFIB = 0x5f7000);
   - Hsoff: shadow_off is SHADOW_OFF (fm: cbn [shadow_off TFIB]);
   - Hchk: avis8_chk stk ch, the stack entry stk is in a_vis ch and every other entry has a base and a length that
     pa says are multiples of 4096 (fm: avis8_all :49, vm_compute over HS_tfib_list);
   - Hstk_lo, Hstk_sum: fm's uSTK_lo (:279) and uSTK_sum (:285) for stk, whose app window is [usp - 8388608, 2 ^ 47);
   - Hsp, HargH: valid_sp sp and argH above YA02.TOP sp (AD2i's Hsp and ARGH; fm: usp_range, argH0_high).

   Why it holds (fm's text).  On a band byte every disjunct of vis (YA0e.v:137-143) but in_allow is decided:
   Hband says the byte is mapped, is not noaccess and is lazy, the image hull ends below the low band, and
   TOP = usp - 8388608 lies above both bands.  So there hull1 = negb (in_allow || sliverb).  in_allow runs over
   a_vis ch (YA0e.v:124-134).  Every entry of a_vis ch has a base and a length that are multiples of 4096, except
   stk; a multiple of 4096 is a multiple of 8 in app space and, after the division by 8, in shadow space, so every
   window of every other entry has ends that are multiples of 8.  stk's app window starts at usp - 8388608, above
   both bands, and its shadow window is [SL, SHE) with SL = shadow_off + (usp - 8388608) / 8, which usp's
   16-alignment can leave unaligned, and SHE = shadow_off + 2 ^ 47 / 8.  sliverb (YD1h.v:10) is exactly [S0, SL)
   with S0 = shadow_off + run_ceil usp / 8, so the union of the two is [S0, SHE), whose ends are multiples of 8
   (run_ceil is page-aligned).

   Also here: fm's vis0_word_gen (in_vis0 is constant on each 8-byte-aligned word when every ly_vis0 range has
   ends that are multiples of 8) and the negative control poke_no_world. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0r YM05 YD1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- expressions whose value is a multiple of 4096 ---- *)
Fixpoint pa (e : expr) : bool :=
match e with
| ELit z => Z.eqb (z mod 4096) 0
| EAlu op a b => match op with ALU_ADD => (pa a && pa b)%bool | _ => false end
| EMd op a b => match op with M_MUL => (pa a || pa b)%bool | _ => false end
| _ => false
end.

(* ---- a_vis entries: page-aligned at both ends, except the stack entry stk ---- *)
Definition avis8_chk (stk : expr * expr) (c : acs) : bool :=
(existsb (fun p => pair_eqb p stk) (a_vis c)
 && forallb (fun p => pair_eqb p stk || (pa (fst p) && pa (snd p)))%bool (a_vis c))%bool.

Lemma existsb_orb : forall (X : Type) (f g : X -> bool) (l : list X),
(existsb f l || existsb g l)%bool = existsb (fun x => (f x || g x)%bool) l.
Proof.
intros X f g l. induction l as [|x l IH]; cbn [existsb]; [reflexivity|].
rewrite <- IH. destruct (f x), (g x), (existsb f l), (existsb g l); reflexivity.
Qed.

(* existsb with one member of the list treated apart *)
Lemma existsb_one_out : forall (X : Type) (x : X) (l : list X) (f g : X -> bool) (b b' : bool),
In x l ->
(forall y, In y l -> f y = true -> y = x \/ g y = true) ->
(forall y, In y l -> g y = true -> y = x \/ f y = true) ->
(f x || b)%bool = (g x || b')%bool ->
(existsb f l || b)%bool = (existsb g l || b')%bool.
Proof.
intros X x l f g b b' Hx Hfg Hgf Hxx.
apply Bool.eq_iff_eq_true. split; intros H.
- apply orb_true_iff in H as [H|H].
  + apply existsb_exists in H as (y & Hy & Hfy). destruct (Hfg y Hy Hfy) as [->|Hg].
    * assert (T : (g x || b')%bool = true) by (rewrite <- Hxx, Hfy; reflexivity).
      apply orb_true_iff in T as [T|T]; apply orb_true_iff;
      [left; apply existsb_exists; exists x; exact (conj Hx T) | right; exact T].
    * apply orb_true_iff. left. apply existsb_exists. exists y. exact (conj Hy Hg).
  + assert (T : (g x || b')%bool = true) by (rewrite <- Hxx, H; apply orb_true_r).
    apply orb_true_iff in T as [T|T]; apply orb_true_iff;
    [left; apply existsb_exists; exists x; exact (conj Hx T) | right; exact T].
- apply orb_true_iff in H as [H|H].
  + apply existsb_exists in H as (y & Hy & Hgy). destruct (Hgf y Hy Hgy) as [->|Hf].
    * assert (T : (f x || b)%bool = true) by (rewrite Hxx, Hgy; reflexivity).
      apply orb_true_iff in T as [T|T]; apply orb_true_iff;
      [left; apply existsb_exists; exists x; exact (conj Hx T) | right; exact T].
    * apply orb_true_iff. left. apply existsb_exists. exists y. exact (conj Hy Hf).
  + assert (T : (f x || b)%bool = true) by (rewrite Hxx, H; apply orb_true_r).
    apply orb_true_iff in T as [T|T]; apply orb_true_iff;
    [left; apply existsb_exists; exists x; exact (conj Hx T) | right; exact T].
Qed.

(* a half-open range with ends a multiple of 8 does not tell the bytes of a word apart *)
Lemma range_const : forall lo hi z, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= z ->
((lo <=? z) && (z <? hi))%bool = ((lo <=? z - z mod 8) && (z - z mod 8 <? hi))%bool.
Proof.
intros lo hi z Hlo Hhi Hz.
pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as Hm. pose proof (Z.div_mod z 8 ltac:(lia)) as Hd.
apply Z.mod_divide in Hlo as [ql ->]; [|lia]. apply Z.mod_divide in Hhi as [qh ->]; [|lia].
remember (z / 8) as k. remember (z mod 8) as r. clear Heqk Heqr.
destruct (Z.leb_spec (ql * 8) z), (Z.leb_spec (ql * 8) (z - r)),
         (Z.ltb_spec z (qh * 8)), (Z.ltb_spec (z - r) (qh * 8));
cbn [andb]; first [reflexivity | exfalso; lia].
Qed.

(* the Prop form of range_const *)
Lemma range_const_P : forall lo hi z, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= z ->
(lo <= z < hi <-> lo <= z - z mod 8 < hi).
Proof.
intros lo hi z Hlo Hhi Hz.
pose proof (Z.mod_pos_bound z 8 ltac:(lia)) as Hm. pose proof (Z.div_mod z 8 ltac:(lia)) as Hd.
apply Z.mod_divide in Hlo as [ql ->]; [|lia]. apply Z.mod_divide in Hhi as [qh ->]; [|lia].
remember (z / 8) as k. remember (z mod 8) as r. clear Heqk Heqr. lia.
Qed.

(* two half-open ranges that meet *)
Lemma range_join : forall lo mid hi z, lo <= mid -> mid <= hi ->
((((mid <=? z) && (z <? hi)) || ((lo <=? z) && (z <? mid)))%bool = ((lo <=? z) && (z <? hi))%bool).
Proof.
intros lo mid hi z H1 H2.
destruct (Z.leb_spec lo z), (Z.leb_spec mid z), (Z.ltb_spec z mid), (Z.ltb_spec z hi);
cbn [andb orb]; first [reflexivity | exfalso; lia].
Qed.

(* in_vis0 is constant on an 8-byte-aligned word whenever every ly_vis0 range has ends that are
   multiples of 8.  layout_ok does not give that (lo_vis0, YG0f.v:332-333, only places each range
   inside the shadow of a vis0 zone), so the hypothesis is explicit; each image discharges it (fm: vis0_ends). *)
Lemma vis0_word_gen : forall ly : alayout,
Forall (fun v => fst v mod 8 = 0 /\ (fst v + snd v) mod 8 = 0) (ly_vis0 ly) ->
forall a, 0 <= a -> (in_vis0 ly a <-> in_vis0 ly (a - a mod 8)).
Proof.
intros ly HF a Ha.
assert (KEY : forall v, In v (ly_vis0 ly) -> (in_zr a v <-> in_zr (a - a mod 8) v)).
{ intros v Hv. destruct (proj1 (Forall_forall _ _) HF v Hv) as [H1 H2].
  unfold in_zr. apply range_const_P; [exact H1 | exact H2 | exact Ha]. }
unfold in_vis0. split; intros H;
apply Exists_exists in H as (v & Hv & Hin); apply Exists_exists; exists v; split; try exact Hv;
apply (KEY v Hv); exact Hin.
Qed.

(* W1's hidden set (AD2i.v:506): HID minus the argument area minus the sliver *)
Definition hull1 (A : atable) (argH : env -> word -> bool) (E : env) (ch : acs) (model : Model) (sp : word)
: word -> bool :=
fun a => (hid A (YA02.TOP sp) argH E ch model a && negb (argH E a) && negb (sliverb sp a))%bool.

Section g.
Variables (A : atable) (argH : env -> word -> bool) (E : env) (ch : acs) (model : Model) (sp : word).
Variable stk : expr * expr.
Hypothesis Hsp : valid_sp sp.
Hypothesis HargH : forall a : word, argH E a = true -> YA02.TOP sp <= bv_unsigned a.
Hypothesis Hhull : img_hi A <= kLowShadowBeg.
Hypothesis Hsoff : shadow_off A = SHADOW_OFF.
Hypothesis Hband : forall x : word, in_band_rw (bv_unsigned x) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base x) (m_vm_lazy model) = true
/\ in_ivs (bv_unsigned x) (vm_maps (m_vmmaps model)) = true.
Hypothesis Hchk : avis8_chk stk ch = true.
Hypothesis Hstk_lo : uE E (fst stk) = bv_unsigned sp - 8388608.
Hypothesis Hstk_sum : eqm (uE E (fst stk) + uE E (snd stk)) (2 ^ 47).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).

(* ---- usp lies above both bands (valid_sp, Run.v; fm: usp_range) ---- *)
Lemma top_band : kHighShadowEnd + 8388608 <= usp.
Proof. pose proof Hsp as (Hlo & _ & _). unfold sp_window_lo in Hlo. unfold kHighShadowEnd. lia. Qed.

(* ---- values modulo 2 ^ 64 ---- *)
Lemma uE_bound : forall e, 0 <= u e < 2 ^ 64.
Proof. intros e. unfold uE. pose proof (bv_unsigned_in_range 64 (edenot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma eqm_mod4096 : forall x y : Z, eqm x y -> x mod 4096 = y mod 4096.
Proof.
intros x y [q Hq]. rewrite Hq. replace (q * 2 ^ 64) with (q * 2 ^ 52 * 4096) by lia. apply Z_mod_plus_full.
Qed.
Lemma eqm_of_eq : forall x y : Z, x = y -> eqm x y.
Proof. intros x y ->. apply eqm_refl. Qed.
Lemma uE_lit_eqm : forall z, eqm (u (ELit z)) z.
Proof. intros z. unfold uE. cbn [edenot]. apply eqm_u_lit. Qed.
Lemma uE_add_eqm : forall a b, eqm (u (EAlu ALU_ADD a b)) (u a + u b).
Proof. intros a b. unfold uE. cbn [edenot]. apply u_add_eqm. Qed.
Lemma uE_mul_eqm : forall a b, eqm (u (EMd M_MUL a b)) (u a * u b).
Proof. intros a b. unfold uE. cbn [edenot]. apply u_mul_eqm. Qed.
Lemma pa_ok : forall e, pa e = true -> u e mod 4096 = 0.
Proof.
intros e.
induction e as [z|v|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|sx lo n x IHx|sx kk i n];
cbn [pa]; intros Hp; try discriminate Hp.
- rewrite (eqm_mod4096 _ _ (uE_lit_eqm _)). apply Z.eqb_eq. exact Hp.
- destruct op; try discriminate Hp. apply andb_prop in Hp as [P1 P2].
  rewrite (eqm_mod4096 _ _ (uE_add_eqm x y)).
  rewrite Z.add_mod by lia. rewrite (IHx P1), (IHy P2). reflexivity.
- destruct op; try discriminate Hp.
  rewrite (eqm_mod4096 _ _ (uE_mul_eqm x y)).
  rewrite Z.mul_mod by lia. apply orb_prop in Hp as [P|P];
  [rewrite (IHx P), Z.mul_0_l | rewrite (IHy P), Z.mul_0_r]; apply Z.mod_0_l; lia.
Qed.

(* ---- the entries of a_vis ch ---- *)
Lemma stk_in : In stk (a_vis ch).
Proof.
pose proof Hchk as X. unfold avis8_chk in X. apply andb_prop in X as [X _].
apply existsb_exists in X as (p & Hp & He). apply pair_eqb_eq in He. subst p. exact Hp.
Qed.
Lemma avis8_entry : forall p, In p (a_vis ch) ->
p = stk \/ (pa (fst p) = true /\ pa (snd p) = true).
Proof.
intros p Hp. pose proof Hchk as X. unfold avis8_chk in X. apply andb_prop in X as [_ X].
pose proof (proj1 (forallb_forall _ _) X p Hp) as Y. cbn beta in Y. apply orb_prop in Y as [Y|Y].
- left. apply pair_eqb_eq. exact Y.
- right. apply andb_prop in Y as [Y1 Y2]. exact (conj Y1 Y2).
Qed.

(* ---- in_allow as one existsb ---- *)
Definition Qc (p : expr * expr) (z : Z) : bool :=
(((u (fst p) <=? z) && (z <? u (fst p) + u (snd p)))
 || ((shadow_off A + u (fst p) / 8 <=? z) && (z <? shadow_off A + (u (fst p) + u (snd p)) / 8)))%bool.
Lemma in_allow_Qc : forall z, in_allow A E ch z = existsb (fun p => Qc p z) (a_vis ch).
Proof.
intros z. unfold in_allow, in_vis, in_sh, sh_lo, sh_hi. rewrite existsb_orb. reflexivity.
Qed.
Lemma Qc_const : forall p z, 0 <= z -> pa (fst p) = true -> pa (snd p) = true ->
Qc p z = Qc p (z - z mod 8).
Proof.
intros p z Hz P1 P2. pose proof (pa_ok _ P1) as A1. pose proof (pa_ok _ P2) as A2.
pose proof (uE_bound (fst p)) as B1. pose proof (uE_bound (snd p)) as B2.
assert (S1 : (u (fst p) + u (snd p)) mod 4096 = 0) by (rewrite Z.add_mod by lia; rewrite A1, A2; reflexivity).
assert (M8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx as [q ->]; [|lia]. replace (q * 4096) with (q * 512 * 8) by lia. apply Z_mod_mult. }
assert (D8 : forall x, x mod 4096 = 0 -> (shadow_off A + x / 8) mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx as [q ->]; [|lia].
  replace (q * 4096) with (q * 512 * 8) by lia. rewrite Z.div_mul by lia.
  replace (shadow_off A + q * 512) with ((268431360 + q * 64) * 8) by (rewrite Hsoff; unfold SHADOW_OFF; lia). apply Z_mod_mult. }
unfold Qc. f_equal.
- apply range_const; [apply M8; exact A1 | apply M8; exact S1 | exact Hz].
- apply range_const; [apply D8; exact A1 | apply D8; exact S1 | exact Hz].
Qed.

(* ---- the stack entry stk ---- *)
#[local] Notation SOFF := (shadow_off A).
#[local] Notation SL := (SOFF + (usp - 8388608) / 8).
#[local] Notation S0 := (SOFF + run_ceil usp / 8).
#[local] Notation SHE := (SOFF + (u (fst stk) + u (snd stk)) / 8).

Lemma stk_app_above : kHighShadowEnd <= u (fst stk).
Proof. pose proof top_band as UR. rewrite Hstk_lo. lia. Qed.
Lemma S0_le_SL : S0 <= SL.
Proof.
pose proof top_band as UR.
assert (run_ceil usp <= usp - 8388608) by (unfold run_ceil; change stack_max_size with 8388608; apply page_floor_le).
assert (run_ceil usp / 8 <= (usp - 8388608) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma SL_le_SHE : SL <= SHE.
Proof.
pose proof (uE_bound (snd stk)) as B2. rewrite Hstk_lo.
assert ((usp - 8388608) / 8 <= (usp - 8388608 + u (snd stk)) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma S0_mod8 : S0 mod 8 = 0.
Proof.
assert (RC : run_ceil usp mod 4096 = 0) by (unfold run_ceil, page_floor; apply Z_mod_mult).
apply Z.mod_divide in RC as [q Hq]; [|lia]. rewrite Hq.
replace (q * 4096) with (q * 512 * 8) by lia. rewrite Z.div_mul by lia.
replace (SOFF + q * 512) with ((268431360 + q * 64) * 8) by (rewrite Hsoff; unfold SHADOW_OFF; lia). apply Z_mod_mult.
Qed.
Lemma SHE_mod8 : SHE mod 8 = 0.
Proof.
pose proof Hstk_sum as [q Hq]. rewrite Hq.
replace (2 ^ 47 + q * 2 ^ 64) with ((2 ^ 44 + q * 2 ^ 61) * 8) by lia. rewrite Z.div_mul by lia.
replace (SOFF + (2 ^ 44 + q * 2 ^ 61)) with ((268431360 + (2 ^ 41 + q * 2 ^ 58)) * 8) by (rewrite Hsoff; unfold SHADOW_OFF; lia).
apply Z_mod_mult.
Qed.

(* ---- hull1 on the band ---- *)
Lemma H1_band : forall z, in_band_rw z ->
hull1 A argH E ch model sp (Z_to_bv 64 z)
= negb (in_allow A E ch z || sliverb sp (Z_to_bv 64 z))%bool.
Proof.
intros z Hz. pose proof top_band as UR. unfold kHighShadowEnd in UR.
assert (RG : 0 <= z < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hz; lia).
assert (UZ : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; lia).
destruct (Hband (Z_to_bv 64 z) ltac:(rewrite UZ; exact Hz)) as (Hna & Hlz & Hmp).
rewrite UZ in Hna, Hmp.
assert (HA : argH E (Z_to_bv 64 z) = false).
{ destruct (argH E (Z_to_bv 64 z)) eqn:Eh; [exfalso|reflexivity].
  pose proof (HargH (Z_to_bv 64 z) Eh) as HT.
  rewrite UZ in HT. unfold YA02.TOP in HT.
  unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hz. lia. }
assert (HH : in_hull A z = false).
{ unfold in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
  pose proof Hhull as HL. unfold kLowShadowBeg in HL.
  unfold in_band_rw, kLowShadowBeg, kHighShadowBeg in Hz. lia. }
assert (HT : (YA02.TOP sp <=? z) = false).
{ apply Z.leb_gt. unfold YA02.TOP. unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hz. lia. }
unfold hull1, hid, vis. rewrite UZ, HA, HH, HT, Hna, Hlz, Hmp.
cbn [orb andb negb]. destruct (in_allow A E ch z), (sliverb sp (Z_to_bv 64 z)); reflexivity.
Qed.

Theorem H1_H8 : forall a : Z, in_band_rw a ->
hull1 A argH E ch model sp (Z_to_bv 64 a)
= hull1 A argH E ch model sp (Z_to_bv 64 (a - a mod 8)).
Proof.
intros a Ha. pose proof top_band as UR.
assert (RG : 0 <= a < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hm. pose proof (Z.div_mod a 8 ltac:(lia)) as Hd.
assert (Ha8 : in_band_rw (a - a mod 8)).
{ unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha |- *. lia. }
assert (RG8 : 0 <= a - a mod 8 < 2 ^ 64) by lia.
assert (UZ : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
assert (UZ8 : bv_unsigned (Z_to_bv 64 (a - a mod 8)) = a - a mod 8) by (apply u64_lit; lia).
rewrite (H1_band a Ha), (H1_band _ Ha8). f_equal.
rewrite !in_allow_Qc.
(* the sliver, as a range *)
assert (SLV : forall z, 0 <= z < 2 ^ 64 -> sliverb sp (Z_to_bv 64 z) = ((S0 <=? z) && (z <? SL))%bool).
{ intros z Hzr. unfold sliverb. rewrite (u64_lit z) by lia. rewrite Hsoff. reflexivity. }
rewrite (SLV a ltac:(lia)), (SLV (a - a mod 8) ltac:(lia)).
(* stk's own contribution, joined with the sliver *)
assert (STK : forall z, in_band_rw z -> 0 <= z < 2 ^ 64 ->
  (Qc stk z || ((S0 <=? z) && (z <? SL)))%bool = ((S0 <=? z) && (z <? SHE))%bool).
{ intros z Hzb Hzr. pose proof stk_app_above as AB. pose proof S0_le_SL as O1. pose proof SL_le_SHE as O2.
  assert (NV : ((u (fst stk) <=? z) && (z <? u (fst stk) + u (snd stk)))%bool = false).
  { apply andb_false_iff. left. apply Z.leb_gt.
    unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hzb. unfold kHighShadowEnd in AB. lia. }
  unfold Qc. rewrite NV. cbn [orb]. rewrite Hstk_lo in O2 |- *.
  apply range_join; [exact O1 | exact O2]. }
apply (existsb_one_out _ stk (a_vis ch) (fun p => Qc p a) (fun p => Qc p (a - a mod 8))).
- exact stk_in.
- intros y Hy Hfy. destruct (avis8_entry y Hy) as [->|[P1 P2]]; [left; reflexivity|].
  right. rewrite <- (Qc_const y a ltac:(lia) P1 P2). exact Hfy.
- intros y Hy Hgy. destruct (avis8_entry y Hy) as [->|[P1 P2]]; [left; reflexivity|].
  right. rewrite (Qc_const y a ltac:(lia) P1 P2). exact Hgy.
- rewrite (STK a Ha ltac:(lia)), (STK _ Ha8 ltac:(lia)).
  apply range_const; [exact S0_mod8 | exact SHE_mod8 | lia].
Qed.

End g.

(* ---- negative control: a one-byte change of a hidden set breaks w_H8 ----
   Hpoke hides exactly kHighShadowBeg + 1 and nothing else.  It satisfies the world's other law on its hidden set,
   w_Hoff = H_off_segments (YA0n.v:23), for any image whose hull ends at or below kLowShadowBeg (poke_H_off),
   because that address lies outside every segment; w_H8 is what stops it.  So no world over any segment list has
   it as its hidden set, and the field is not vacuous. *)
Definition POKE : Z := kHighShadowBeg + 1.
Definition Hpoke : word -> bool := fun a => Z.eqb (bv_unsigned a) POKE.
Lemma poke_H_off : forall (segs : list Segment) (A : atable),
(forall a : word, in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None) ->
img_hi A <= kLowShadowBeg -> H_off_segments segs Hpoke.
Proof.
intros segs A Hseg Hhi a Ha. unfold Hpoke in Ha. apply Z.eqb_eq in Ha.
apply Hseg. unfold APSG.in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
rewrite Ha. unfold POKE, kHighShadowBeg. unfold kLowShadowBeg in Hhi. lia.
Qed.
Lemma poke_not_H8 :
~ (forall a : Z, in_band_rw a -> Hpoke (Z_to_bv 64 a) = Hpoke (Z_to_bv 64 (a - a mod 8))).
Proof.
intros H.
assert (HB : in_band_rw POKE) by (unfold in_band_rw, POKE, kHighShadowBeg, kHighShadowEnd; lia).
assert (M : POKE mod 8 = 1) by (vm_compute; reflexivity).
assert (U1 : bv_unsigned (Z_to_bv 64 POKE) = POKE)
by (apply u64_lit; unfold POKE, kHighShadowBeg; lia).
assert (U2 : bv_unsigned (Z_to_bv 64 (POKE - POKE mod 8)) = POKE - POKE mod 8)
by (apply u64_lit; rewrite M; unfold POKE, kHighShadowBeg; lia).
specialize (H POKE HB). unfold Hpoke in H. rewrite U1, U2, M, Z.eqb_refl in H.
symmetry in H. apply Z.eqb_eq in H. unfold POKE, kHighShadowBeg in H. lia.
Qed.
Lemma poke_no_world : forall (segs : list Segment) (W : world segs), w_H W <> Hpoke.
Proof. intros segs W HW. apply poke_not_H8. rewrite <- HW. exact (w_H8 W). Qed.
