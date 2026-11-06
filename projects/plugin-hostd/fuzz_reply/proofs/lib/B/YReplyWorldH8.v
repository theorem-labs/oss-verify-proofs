(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/omx-clap-core/fuzz_preset/lib/A/PWorldH8.v, with its module paths, module names and addresses changed. *)
(* Modified by Theorem Labs, 2026-10: copied from this harness's lib/A/ReplyWorldH8.v (adapted from proofs/omx-clap-core/fuzz_manifest/lib/A/FMworldH8.v 3e35620c52e, as plugin-hostd/fuzz_command's lib/B/YCmdWorldH8.v of 5f4acbb7d0d's chain is) for plugin-hostd/fuzz_reply's ASan+UBSan build: module paths changed (lib/A to lib/B, AB01/AD1g/AD2i to YB01/YD1g/YD2i, image Asan to AsanUbsan); avis8_all runs by vm_compute on image B's own 50 hand-off states (lib/B/YB01.v); the image hull ends at 0x5fc000; the line references are this tree's. *)
(* w_H8 (YA0n.v:24) for reply's image-B entry world W1 (YD2i.v:773): on the two shadow bands, H1 is constant on
   each 8-byte-aligned word.  YD2i states it as its section hypothesis H1_8 and this file proves it;
   YD1d, YD1f and YD1p pass the proof in.

   Why it holds.  On a band byte every disjunct of vis (YA0e.v:139-145) but in_allow is decided:
   band_facts below says the byte is mapped, is not noaccess and is lazy, the image hull ends at
   0x5fc000, and TOP = usp - 8388608 lies above both bands.  So there H1 = negb (in_allow || sliverb).
   in_allow runs over a_vis ch (YA0e.v:126-136).  Every entry of every a_vis of HS_tfib_list
   (YB01.v:600) has a base and a length that are multiples of 4096, except STK_P (YD1g.v:100); a
   multiple of 4096 is a multiple of 8 in app space and, after the division by 8, in shadow space, so
   every window of every other entry has ends that are multiples of 8.  STK_P's app window starts at
   usp - 8388608, above both bands, and its shadow window is [SL, SHE) with
   SL = shadow_off + (usp - 8388608) / 8, which usp's 16-alignment can leave unaligned, and
   SHE = shadow_off + 2 ^ 47 / 8.  sliverb (YD1h.v:10) is exactly [S0, SL) with
   S0 = shadow_off + run_ceil usp / 8, so the union of the two is [S0, SHE), whose ends are multiples
   of 8 (run_ceil is page-aligned). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG01 YG0f YG0v YG0n YG0r YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YD1g YD2i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- expressions whose value is a multiple of 4096 ---- *)
Fixpoint pa (e : expr) : bool :=
match e with
| ELit z => Z.eqb (z mod 4096) 0
| EAlu op a b => match op with ALU_ADD => (pa a && pa b)%bool | _ => false end
| EMd op a b => match op with M_MUL => (pa a || pa b)%bool | _ => false end
| _ => false
end.

(* ---- a_vis entries: page-aligned at both ends, except STK_P ---- *)
Definition avis8_chk (c : acs) : bool :=
(existsb (fun p => pair_eqb p YD1g.STK_P) (a_vis c)
 && forallb (fun p => pair_eqb p YD1g.STK_P || (pa (fst p) && pa (snd p)))%bool (a_vis c))%bool.
Lemma avis8_all : forallb avis8_chk HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.

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
   multiples of 8.  layout_ok does not give that (lo_vis0, YG0f.v:335-336, only places each range
   inside the shadow of a vis0 zone), so the hypothesis is explicit; vis0_ends discharges it below. *)
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

Section f. Context {fx : YK11.FPState}.
Section g.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation vm := (vm_maps (m_vmmaps model)).

Ltac inst H := try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition band_vals := ltac:(get @YD1g.band_vals).
#[local] Definition vm_In' := ltac:(get @YD1g.vm_In').
#[local] Definition tfib_hole_maps := ltac:(get @YD1g.tfib_hole_maps).
#[local] Definition uS0 := ltac:(get @YD1g.uS0).
#[local] Definition uSp0 := ltac:(get @YD1g.uSp0).
#[local] Definition usp_range := ltac:(get @YD1g.usp_range).
#[local] Ltac vin := apply vm_In'; cbn; tauto.

(* ---- the bands are mapped, not noaccess, and lazy (YD1d.v:113-135) ---- *)
Lemma band_in_maps : forall a, in_band_rw a ->
(bv_unsigned (fst (YD1g.dLow E)) <= a < bv_unsigned (fst (YD1g.dLow E)) + bv_unsigned (snd (YD1g.dLow E)))
\/ (bv_unsigned (fst (YD1g.dHigh E)) <= a < bv_unsigned (fst (YD1g.dHigh E)) + bv_unsigned (snd (YD1g.dHigh E))).
Proof.
intros a Ha. pose proof band_vals as (VL & _ & VH). unfold wzp in VL, VH.
apply (f_equal fst) in VL as L1; apply (f_equal snd) in VL as L2.
apply (f_equal fst) in VH as Y1; apply (f_equal snd) in VH as Y2.
cbn [fst snd] in L1, L2, Y1, Y2. rewrite L1, L2, Y1, Y2.
unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha. lia.
Qed.

Lemma band_facts : forall x : word, in_band_rw (bv_unsigned x) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false
/\ page_in_ranges (page_base x) (m_vm_lazy model) = true
/\ in_ivs (bv_unsigned x) vm = true.
Proof.
intros x Hx. pose proof (ho_kinds TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as K.
rewrite tfib_hole_maps in K.
assert (KD : forall m, In m YD1g.TFIB_TAIL12 -> am_kind m = KRWLAZY ->
bv_unsigned (fst (YD1g.dmm E m)) <= bv_unsigned x < bv_unsigned (fst (YD1g.dmm E m)) + bv_unsigned (snd (YD1g.dmm E m)) ->
in_ivs (bv_unsigned x) (vm_noaccess (m_vmmaps model)) = false /\ page_in_ranges (page_base x) (m_vm_lazy model) = true).
{ intros m Hm Hk Hr. apply (proj1 (Forall_forall _ _) K m); [apply in_app_iff; right; apply in_app_iff; right; exact Hm | exact Hk | exact Hr]. }
assert (IN : forall d, In d vm -> bv_unsigned (fst d) <= bv_unsigned x < bv_unsigned (fst d) + bv_unsigned (snd d) -> in_ivs (bv_unsigned x) vm = true).
{ intros d Hd Hr. unfold in_ivs. apply existsb_exists. exists d. split; [exact Hd|].
  apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
destruct (band_in_maps (bv_unsigned x) Hx) as [R0|R0].
- destruct (KD (YD1g.mk (ELit 2147446784) 268435456 KRWLAZY) ltac:(cbn; tauto) eq_refl R0) as [A1 A2].
  split; [exact A1|]. split; [exact A2|]. apply (IN (YD1g.dLow E)); [vin | exact R0].
- destruct (KD (YD1g.mk (ELit 2201439137792) 15392894357504 KRWLAZY) ltac:(cbn; tauto) eq_refl R0) as [A1 A2].
  split; [exact A1|]. split; [exact A2|]. apply (IN (YD1g.dHigh E)); [vin | exact R0].
Qed.

(* ---- values modulo 2 ^ 64 ---- *)
Lemma eqm_mod4096 : forall x y : Z, eqm x y -> x mod 4096 = y mod 4096.
Proof.
intros x y [q Hq]. rewrite Hq. replace (q * 2 ^ 64) with (q * 2 ^ 52 * 4096) by lia. apply Z_mod_plus_full.
Qed.
Lemma eqm_of_eq : forall x y : Z, x = y -> eqm x y.
Proof. intros x y ->. apply eqm_refl. Qed.
Lemma uE_lit_eqm : forall z, eqm (u (ELit z)) z.
Proof. intros z. unfold uE. cbn [edenot]. apply eqm_u_lit. Qed.
Lemma uE_mul_eqm : forall a b, eqm (u (EMd M_MUL a b)) (u a * u b).
Proof. intros a b. unfold uE. cbn [edenot]. apply u_mul_eqm. Qed.
Lemma uE_mul_lit_eqm : forall k b, eqm (u (EMd M_MUL (ELit k) b)) (k * u b).
Proof.
intros k b. eapply eqm_trans; [apply uE_mul_eqm|].
apply eqm_mul_r. apply uE_lit_eqm.
Qed.
Lemma pa_ok : forall e, pa e = true -> u e mod 4096 = 0.
Proof.
intros e.
induction e as [z|v|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|op x IHx y IHy|sx lo n x IHx|sx kk i n];
cbn [pa]; intros Hp; try discriminate Hp.
- rewrite (eqm_mod4096 _ _ (uE_lit_eqm _)). apply Z.eqb_eq. exact Hp.
- destruct op; try discriminate Hp. apply andb_prop in Hp as [P1 P2].
  rewrite (eqm_mod4096 _ _ (YD1g.uE_add_eqm E x y)).
  rewrite Z.add_mod by lia. rewrite (IHx P1), (IHy P2). reflexivity.
- destruct op; try discriminate Hp.
  rewrite (eqm_mod4096 _ _ (uE_mul_eqm x y)).
  rewrite Z.mul_mod by lia. apply orb_prop in Hp as [P|P];
  [rewrite (IHx P), Z.mul_0_l | rewrite (IHy P), Z.mul_0_r]; apply Z.mod_0_l; lia.
Qed.

(* ---- the entries of a_vis ch ---- *)
Lemma avis8_ch : avis8_chk ch = true.
Proof. exact (proj1 (forallb_forall _ _) avis8_all ch (HS_tfib_In h ch Hch)). Qed.
Lemma stk_in : In YD1g.STK_P (a_vis ch).
Proof.
pose proof avis8_ch as X. unfold avis8_chk in X. apply andb_prop in X as [X _].
apply existsb_exists in X as (p & Hp & He). apply pair_eqb_eq in He. subst p. exact Hp.
Qed.
Lemma avis8_entry : forall p, In p (a_vis ch) ->
p = YD1g.STK_P \/ (pa (fst p) = true /\ pa (snd p) = true).
Proof.
intros p Hp. pose proof avis8_ch as X. unfold avis8_chk in X. apply andb_prop in X as [_ X].
pose proof (proj1 (forallb_forall _ _) X p Hp) as Y. cbn beta in Y. apply orb_prop in Y as [Y|Y].
- left. apply pair_eqb_eq. exact Y.
- right. apply andb_prop in Y as [Y1 Y2]. exact (conj Y1 Y2).
Qed.

(* ---- in_allow as one existsb ---- *)
Definition Qc (p : expr * expr) (z : Z) : bool :=
(((u (fst p) <=? z) && (z <? u (fst p) + u (snd p)))
 || ((shadow_off TFIB + u (fst p) / 8 <=? z) && (z <? shadow_off TFIB + (u (fst p) + u (snd p)) / 8)))%bool.
Lemma in_allow_Qc : forall z, in_allow TFIB E ch z = existsb (fun p => Qc p z) (a_vis ch).
Proof.
intros z. unfold in_allow, in_vis, in_sh, sh_lo, sh_hi. rewrite existsb_orb. reflexivity.
Qed.
Lemma Qc_const : forall p z, 0 <= z -> pa (fst p) = true -> pa (snd p) = true ->
Qc p z = Qc p (z - z mod 8).
Proof.
intros p z Hz P1 P2. pose proof (pa_ok _ P1) as A1. pose proof (pa_ok _ P2) as A2.
pose proof (YD1g.uE_bound E (fst p)) as B1. pose proof (YD1g.uE_bound E (snd p)) as B2.
assert (S1 : (u (fst p) + u (snd p)) mod 4096 = 0) by (rewrite Z.add_mod by lia; rewrite A1, A2; reflexivity).
assert (M8 : forall x, x mod 4096 = 0 -> x mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx as [q ->]; [|lia]. replace (q * 4096) with (q * 512 * 8) by lia. apply Z_mod_mult. }
assert (D8 : forall x, x mod 4096 = 0 -> (shadow_off TFIB + x / 8) mod 8 = 0).
{ intros x Hx. apply Z.mod_divide in Hx as [q ->]; [|lia].
  replace (q * 4096) with (q * 512 * 8) by lia. rewrite Z.div_mul by lia.
  replace (shadow_off TFIB + q * 512) with ((268431360 + q * 64) * 8) by (cbn; lia). apply Z_mod_mult. }
unfold Qc. f_equal.
- apply range_const; [apply M8; exact A1 | apply M8; exact S1 | exact Hz].
- apply range_const; [apply D8; exact A1 | apply D8; exact S1 | exact Hz].
Qed.

(* ---- STK_P ---- *)
Lemma uSTK_lo : u (fst YD1g.STK_P) = usp - 8388608.
Proof.
pose proof usp_range as [UR _]. pose proof uS0 as US.
unfold YD1g.STK_P. cbn [fst].
rewrite (YD1g.uE_add_neglit E YD1g.eSp0 (-8388608) ltac:(lia) ltac:(rewrite US; lia)). rewrite US. lia.
Qed.
Lemma uSTK_sum : eqm (u (fst YD1g.STK_P) + u (snd YD1g.STK_P)) (2 ^ 47).
Proof.
pose proof usp_range as [UR _]. pose proof uS0 as US. pose proof uSp0 as [UV _].
assert (HS : eqm (u (snd YD1g.STK_P)) (140737496743936 - usp)).
{ unfold YD1g.STK_P. cbn [snd].
  eapply eqm_trans; [apply (YD1g.uE_add_eqm E)|].
  eapply eqm_trans;
  [apply eqm_add; [apply (YD1g.uE_add_eqm E) | apply eqm_u_lit]|].
  eapply eqm_trans;
  [apply eqm_add; [apply eqm_add; [apply (uE_mul_lit_eqm (-32768) (EVar 0)) | apply (uE_mul_lit_eqm (-16) (EVar 6))] | apply eqm_refl]|].
  rewrite !(YD1g.uE_var E). rewrite <- US, UV. apply eqm_of_eq. lia. }
rewrite uSTK_lo. eapply eqm_trans; [apply eqm_add; [apply eqm_refl | exact HS]|].
apply eqm_of_eq. lia.
Qed.

#[local] Notation SOFF := (shadow_off TFIB).
#[local] Notation SL := (SOFF + (usp - 8388608) / 8).
#[local] Notation S0 := (SOFF + run_ceil usp / 8).
#[local] Notation SHE := (SOFF + (u (fst YD1g.STK_P) + u (snd YD1g.STK_P)) / 8).

Lemma stk_app_above : kHighShadowEnd <= u (fst YD1g.STK_P).
Proof. pose proof usp_range as [UR _]. rewrite uSTK_lo. unfold kHighShadowEnd. lia. Qed.
Lemma S0_le_SL : S0 <= SL.
Proof.
pose proof usp_range as [UR _].
assert (run_ceil usp <= usp - 8388608) by (unfold run_ceil; change stack_max_size with 8388608; apply page_floor_le).
assert (run_ceil usp / 8 <= (usp - 8388608) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
Lemma SL_le_SHE : SL <= SHE.
Proof.
pose proof (YD1g.uE_bound E (snd YD1g.STK_P)) as B2. rewrite uSTK_lo.
assert ((usp - 8388608) / 8 <= (usp - 8388608 + u (snd YD1g.STK_P)) / 8) by (apply Z.div_le_mono; lia).
lia.
Qed.
Lemma S0_mod8 : S0 mod 8 = 0.
Proof.
assert (RC : run_ceil usp mod 4096 = 0) by (unfold run_ceil, page_floor; apply Z_mod_mult).
apply Z.mod_divide in RC as [q Hq]; [|lia]. rewrite Hq.
replace (q * 4096) with (q * 512 * 8) by lia. rewrite Z.div_mul by lia.
replace (SOFF + q * 512) with ((268431360 + q * 64) * 8) by (cbn; lia). apply Z_mod_mult.
Qed.
Lemma SHE_mod8 : SHE mod 8 = 0.
Proof.
destruct uSTK_sum as [q Hq]. rewrite Hq.
replace (2 ^ 47 + q * 2 ^ 64) with ((2 ^ 44 + q * 2 ^ 61) * 8) by lia. rewrite Z.div_mul by lia.
replace (SOFF + (2 ^ 44 + q * 2 ^ 61)) with ((268431360 + (2 ^ 41 + q * 2 ^ 58)) * 8) by (cbn; lia).
apply Z_mod_mult.
Qed.

(* ---- H1 on the band ---- *)
Lemma H1_band : forall z, in_band_rw z ->
YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 z)
= negb (in_allow TFIB E ch z || sliverb sp (Z_to_bv 64 z))%bool.
Proof.
intros z Hz. pose proof usp_range as [UR _].
assert (RG : 0 <= z < 2 ^ 64) by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Hz; lia).
assert (UZ : bv_unsigned (Z_to_bv 64 z) = z) by (apply u64_lit; lia).
destruct (band_facts (Z_to_bv 64 z) ltac:(rewrite UZ; exact Hz)) as (Hna & Hlz & Hmp).
rewrite UZ in Hna, Hmp.
assert (HA : argH E (Z_to_bv 64 z) = false).
{ destruct (argH E (Z_to_bv 64 z)) eqn:Eh; [exfalso|reflexivity].
  pose proof (YA02.argH0_high TPH sp rdraw argv envp uid hw Hsp Hva E (Z_to_bv 64 z) Eh) as HT.
  rewrite UZ in HT. unfold YA02.TOP in HT.
  unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hz. lia. }
assert (HH : in_hull TFIB z = false).
{ unfold in_hull. cbn [img_lo img_hi TFIB]. apply andb_false_iff. right. apply Z.ltb_ge.
  unfold in_band_rw, kLowShadowBeg, kHighShadowBeg in Hz. lia. }
assert (HT : (YA02.TOP sp <=? z) = false).
{ apply Z.leb_gt. unfold YA02.TOP. unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hz. lia. }
unfold YD2i.H1, hid, vis. rewrite UZ, HA, HH, HT, Hna, Hlz, Hmp.
cbn [orb andb negb]. destruct (in_allow TFIB E ch z), (sliverb sp (Z_to_bv 64 z)); reflexivity.
Qed.

Theorem H1_H8 : forall a : Z, in_band_rw a ->
YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 a)
= YD2i.H1 sp rdraw inp ch E model (Z_to_bv 64 (a - a mod 8)).
Proof.
intros a Ha. pose proof usp_range as [UR _].
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
{ intros z Hzr. unfold sliverb. rewrite (u64_lit z) by lia. cbn [shadow_off TFIB]. reflexivity. }
rewrite (SLV a ltac:(lia)), (SLV (a - a mod 8) ltac:(lia)).
(* STK_P's own contribution, joined with the sliver *)
assert (STK : forall z, in_band_rw z -> 0 <= z < 2 ^ 64 ->
  (Qc YD1g.STK_P z || ((S0 <=? z) && (z <? SL)))%bool = ((S0 <=? z) && (z <? SHE))%bool).
{ intros z Hzb Hzr. pose proof stk_app_above as AB. pose proof S0_le_SL as O1. pose proof SL_le_SHE as O2.
  assert (NV : ((u (fst YD1g.STK_P) <=? z) && (z <? u (fst YD1g.STK_P) + u (snd YD1g.STK_P)))%bool = false).
  { apply andb_false_iff. left. apply Z.leb_gt.
    unfold in_band_rw, kLowShadowEnd, kHighShadowEnd in Hzb. unfold kHighShadowEnd in AB. lia. }
  unfold Qc. rewrite NV. cbn [orb]. rewrite uSTK_lo in O2 |- *.
  apply range_join; [exact O1 | exact O2]. }
apply (existsb_one_out _ YD1g.STK_P (a_vis ch) (fun p => Qc p a) (fun p => Qc p (a - a mod 8))).
- exact stk_in.
- intros y Hy Hfy. destruct (avis8_entry y Hy) as [->|[P1 P2]]; [left; reflexivity|].
  right. rewrite <- (Qc_const y a ltac:(lia) P1 P2). exact Hfy.
- intros y Hy Hgy. destruct (avis8_entry y Hy) as [->|[P1 P2]]; [left; reflexivity|].
  right. rewrite (Qc_const y a ltac:(lia) P1 P2). exact Hgy.
- rewrite (STK a Ha ltac:(lia)), (STK _ Ha8 ltac:(lia)).
  apply range_const; [exact S0_mod8 | exact SHE_mod8 | lia].
Qed.

(* ---- the companion fact: in_vis0 is constant on an 8-byte-aligned band word ----
   ahs_pres (YG0n.v:442-444) gives presence only for a band byte that is hidden or not in_vis0, so a
   reader of a whole 8-byte-aligned shadow word needs to know that its eight bytes agree on in_vis0.
   They do: reply's image-B ly_vis0 is VIS0 = map shz VZ (YD1g.v:742-744), and every zone of VZ is a vm map or
   one of ly_T, ly_C, ly_D and the region-info page, each with a base and a length that are multiples
   of 4096 (vm_bound YD1g.v:471, uT/uC/uD :378-380, uSp :420), so each VIS0 range has both ends at a
   multiple of 8. *)
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
Ltac getr L := let H := fresh "L" in pose proof L as H; inst H; try specialize (H rc); inst H;
try specialize (H Hceil); inst H; exact H.
#[local] Definition uT := ltac:(getr @YD1g.uT).
#[local] Definition uC := ltac:(getr @YD1g.uC).
#[local] Definition uD := ltac:(getr @YD1g.uD).
#[local] Definition uSp := ltac:(getr @YD1g.uSp).
#[local] Definition extra_In := ltac:(getr @YD1g.extra_In).
#[local] Definition vm_bound := ltac:(getr @YD1g.vm_bound).
Lemma VZ_pages : forall z, In z (YD1g.VZ E model) -> fst z mod 4096 = 0 /\ snd z mod 4096 = 0.
Proof.
intros z Hz. pose proof uT as [HT _]. pose proof uC as [HCc _]. pose proof uD as [HD _].
pose proof uSp as (_ & S2 & _ & _).
unfold YD1g.VZ in Hz. apply in_app_iff in Hz as [Hz|Hz].
- destruct Hz as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd].
  + rewrite HT. split; [rewrite Z.mul_comm; apply Z_mod_mult | reflexivity].
  + rewrite HCc. split; [rewrite Z.mul_comm; apply Z_mod_mult | reflexivity].
  + rewrite HD. split; [rewrite Z.mul_comm; apply Z_mod_mult | reflexivity].
  + split; [| reflexivity]. unfold kRegionInfoOff.
    apply Z.mod_divide in S2 as [q Hq]; [|lia]. rewrite Hq.
    replace (q * 65536 + 2 ^ 37) with ((16 * q + 33554432) * 4096) by lia. apply Z_mod_mult.
- destruct (extra_In z Hz) as (iv & -> & Hiv & _).
  destruct (vm_bound iv Hiv) as (_ & B2 & B3 & _). unfold wzp. cbn [fst snd]. exact (conj B2 B3).
Qed.
Lemma vis0_ends :
Forall (fun v => fst v mod 8 = 0 /\ (fst v + snd v) mod 8 = 0) (ly_vis0 (YD1g.ly0 ch E model)).
Proof.
cbn [ly_vis0 YD1g.ly0]. apply Forall_forall. intros v Hv.
unfold YD1g.VIS0 in Hv. apply in_map_iff in Hv as (z & <- & Hz).
destruct (VZ_pages z Hz) as [Hb Hl].
apply Z.mod_divide in Hb as [q Hq]; [|lia]. apply Z.mod_divide in Hl as [r Hr]; [|lia].
unfold YD1g.shz, shadow_addr. cbn [fst snd]. rewrite Hq, Hr.
replace (q * 4096) with (q * 512 * 8) by lia. replace (r * 4096) with (r * 512 * 8) by lia.
rewrite !Z.div_mul by lia. split.
- replace (SHADOW_OFF + q * 512) with ((268431360 + q * 64) * 8) by (unfold SHADOW_OFF; lia). apply Z_mod_mult.
- replace (SHADOW_OFF + q * 512 + r * 512) with ((268431360 + q * 64 + r * 64) * 8) by (unfold SHADOW_OFF; lia).
  apply Z_mod_mult.
Qed.
Lemma vis0_word : forall a, 0 <= a ->
(in_vis0 (YD1g.ly0 ch E model) a <-> in_vis0 (YD1g.ly0 ch E model) (a - a mod 8)).
Proof. exact (vis0_word_gen (YD1g.ly0 ch E model) vis0_ends). Qed.

End g.
End f.

(* ---- negative control: a one-byte change of a hidden set breaks w_H8 ----
   Hpoke hides exactly kHighShadowBeg + 1 and nothing else.  It satisfies the world's other law on
   its hidden set, w_Hoff = H_off_segments (YA0n.v:22), because that address lies outside every
   segment of fuzz_reply.asan-ubsan; w_H8 is what stops it.  So no world over TSEGS has it as its hidden set, and
   the field is not vacuous. *)
Definition POKE : Z := kHighShadowBeg + 1.
Definition Hpoke : word -> bool := fun a => Z.eqb (bv_unsigned a) POKE.
Lemma poke_H_off : H_off_segments TSEGS Hpoke.
Proof.
intros a Ha. unfold Hpoke in Ha. apply Z.eqb_eq in Ha.
apply tfib_in_hull. unfold APSG.in_hull. apply andb_false_iff. right. apply Z.ltb_ge.
rewrite Ha. unfold POKE, kHighShadowBeg. change (img_hi TFIB) with 0x5fc000. lia.
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
Lemma poke_no_world : forall W : world TSEGS, w_H W <> Hpoke.
Proof. intros W HW. apply poke_not_H8. rewrite <- HW. exact (w_H8 W). Qed.
