(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound AsanAcct AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame.
Import ListNotations. Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.
Inductive zexp : Type :=
| ZLit (z : Z)
| ZV (n : nat)
| ZAdd (a b : zexp)
| ZMul (a b : zexp)
| ZAnd (a b : zexp)
| ZLtu (a b : zexp).
Definition two64 : Z := 2 ^ 64.
Fixpoint zv (V : nat -> Z) (e : zexp) : Z :=
match e with
| ZLit z => z
| ZV n => V n
| ZAdd a b => zv V a + zv V b
| ZMul a b => zv V a * zv V b
| ZAnd a b => Z.land (zv V a) (zv V b)
| ZLtu a b => Z.b2z (zv V a mod two64 <? zv V b mod two64)
end.
Fixpoint zexp_eqb (x y : zexp) : bool :=
match x, y with
| ZLit a, ZLit b => Z.eqb a b
| ZV a, ZV b => Nat.eqb a b
| ZAdd a b, ZAdd a' b' | ZMul a b, ZMul a' b' | ZAnd a b, ZAnd a' b' | ZLtu a b, ZLtu a' b' =>
zexp_eqb a a' && zexp_eqb b b'
| _, _ => false
end.
Lemma zexp_eqb_eq : forall x y, zexp_eqb x y = true -> x = y.
Proof.
induction x; destruct y; cbn; intros H; try discriminate;
repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H as [? ?] end;
f_equal; auto; first [apply Z.eqb_eq; assumption | apply Nat.eqb_eq; assumption].
Qed.
Fixpoint zexp_of (e : expr) : option zexp :=
match e with
| ELit z => Some (ZLit z)
| EVar n => Some (ZV n)
| EAlu ALU_ADD a b => match zexp_of a, zexp_of b with Some x, Some y => Some (ZAdd x y) | _, _ => None end
| EAlu ALU_AND a b => match zexp_of a, zexp_of b with Some x, Some y => Some (ZAnd x y) | _, _ => None end
| EAlu ALU_SLTU a b => match zexp_of a, zexp_of b with Some x, Some y => Some (ZLtu x y) | _, _ => None end
| EMd M_MUL a b => match zexp_of a, zexp_of b with Some x, Some y => Some (ZMul x y) | _, _ => None end
| _ => None
end.
Definition mkaddr (b : zexp) (k : Z) : zexp :=
match b with
| ZLit z => ZLit (z + k)
| _ => if Z.eqb k 0 then b else ZAdd b (ZLit k)
end.
Lemma zv_mkaddr : forall V b k, zv V (mkaddr b k) = zv V b + k.
Proof. intros V b k. unfold mkaddr. destruct b; cbn; try lia; destruct (Z.eqb_spec k 0); cbn; lia. Qed.
Definition uev (E : env) (n : nat) : Z := bv_unsigned (ev E n).
Lemma uev_range : forall E n, 0 <= uev E n < two64.
Proof. intros E n. unfold uev, two64. pose proof (bv_unsigned_in_range 64 (ev E n)) as H. unfold bv_modulus in H. exact H. Qed.
Lemma land_wrap : forall a b, bv_wrap 64 (Z.land a b) = Z.land (bv_wrap 64 a) (bv_wrap 64 b).
Proof.
intros a b. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, !bv_wrap_spec, Z.land_spec by lia.
destruct (bool_decide _); cbn; [reflexivity|]. reflexivity.
Qed.
Lemma zexp_of_sound : forall E e ze, zexp_of e = Some ze -> Z_to_bv 64 (zv (uev E) ze) = edenot E e.
Proof.
intros E e. induction e; intros ze Hz; cbn in Hz; try discriminate.
- injection Hz as <-. reflexivity.
- injection Hz as <-. cbn. apply Z_to_bv_bv_unsigned.
- destruct op; try discriminate;
destruct (zexp_of e1) as [x|] eqn:E1; try discriminate; destruct (zexp_of e2) as [y|] eqn:E2; try discriminate;
injection Hz as <-; cbn [zv edenot]; rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl); unfold alu64, alu.
+ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. symmetry. apply bv_wrap_add_idemp.
+ unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64. cbn [Z.of_N].
destruct (_ <? _); reflexivity.
+ apply bv_eq. rewrite bv_and_unsigned, !Z_to_bv_unsigned. apply land_wrap.
- destruct op; try discriminate.
destruct (zexp_of e1) as [x|] eqn:E1; try discriminate; destruct (zexp_of e2) as [y|] eqn:E2; try discriminate.
injection Hz as <-. cbn [zv edenot]. rewrite <- (IHe1 x eq_refl), <- (IHe2 y eq_refl). unfold mul_div.
apply bv_eq. rewrite bv_mul_unsigned, !Z_to_bv_unsigned. symmetry. apply bv_wrap_mul_idemp.
Qed.
Corollary zexp_of_unsigned : forall E e z, zexp_of e = Some z -> bv_unsigned (edenot E e) = zv (uev E) z mod two64.
Proof. intros E e z Hz. rewrite <- (zexp_of_sound E e z Hz), Z_to_bv_unsigned. reflexivity. Qed.
Definition vranges := list (nat * Z * Z).
Fixpoint vr_lookup (VR : vranges) (n : nat) : Z * Z :=
match VR with
| [] => (0, two64 - 1)
| (k, lo, hi) :: r => if Nat.eqb k n then (Z.max lo 0, Z.min hi (two64 - 1)) else vr_lookup r n
end.
Definition vr_sound (V : nat -> Z) (VR : vranges) : Prop :=
(forall n, 0 <= V n < two64) /\ Forall (fun t => match t with (n, lo, hi) => lo <= V n <= hi end) VR.
Lemma vr_lookup_sound : forall V VR n, vr_sound V VR -> fst (vr_lookup VR n) <= V n <= snd (vr_lookup VR n).
Proof.
intros V VR n [HV HF]. induction HF as [|[[k lo] hi] r Hk HF IH]; cbn.
- specialize (HV n). Local Ltac2 Set LiaHints.tbl := fun () => "0020=58472179047.97522815414.3 00000700;S2HV2HkS2HV".
lia.
- destruct (Nat.eqb_spec k n); [subst; cbn; specialize (HV n); lia | exact IH].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition itv_scale (c : Z) (lo hi : Z) : Z * Z := (Z.min (c * lo) (c * hi), Z.max (c * lo) (c * hi)).
Lemma itv_scale_sound : forall c lo hi y, lo <= y <= hi -> fst (itv_scale c lo hi) <= c * y <= snd (itv_scale c lo hi).
Proof. intros c lo hi y Hy. unfold itv_scale; cbn. destruct (Z.le_gt_cases 0 c); nia. Qed.
Fixpoint zbnd (VR : vranges) (e : zexp) : option (Z * Z) :=
match e with
| ZLit z => Some (z, z)
| ZV n => Some (vr_lookup VR n)
| ZAdd a b => match zbnd VR a, zbnd VR b with Some (la, ha), Some (lb, hb) => Some (la + lb, ha + hb) | _, _ => None end
| ZMul a b =>
match zbnd VR a, zbnd VR b with
| Some (la, ha), Some (lb, hb) =>
if Z.eqb la ha then Some (itv_scale la lb hb)
else if Z.eqb lb hb then Some (itv_scale lb la ha) else None
| _, _ => None
end
| ZLtu _ _ => Some (0, 1)
| ZAnd _ _ => None
end.
Lemma zbnd_sound : forall V VR e lo hi, vr_sound V VR -> zbnd VR e = Some (lo, hi) -> lo <= zv V e <= hi.
Proof.
intros V VR e. induction e; intros lo hi HV Hb; cbn in Hb |- *.
- injection Hb as <- <-. Local Ltac2 Set LiaHints.tbl := fun () => "0060>11758773501.7 23443255125.1327033437629.1843985553841.4 44568475821.1746990400797.7 00000100<00D00E00M00NSS4IHe14IHe2S4IHe21eSS4IHe11eS".
lia.
- injection Hb as E1. pose proof (vr_lookup_sound V VR n HV) as H. rewrite E1 in H. exact H.
- destruct (zbnd VR e1) as [[la ha]|] eqn:Ea; [|discriminate]. destruct (zbnd VR e2) as [[lb hb]|] eqn:Eb; [|discriminate].
injection Hb as <- <-. specialize (IHe1 la ha HV eq_refl). specialize (IHe2 lb hb HV eq_refl). lia.
- destruct (zbnd VR e1) as [[la ha]|] eqn:Ea; [|discriminate]. destruct (zbnd VR e2) as [[lb hb]|] eqn:Eb; [|discriminate].
specialize (IHe1 la ha HV eq_refl). specialize (IHe2 lb hb HV eq_refl).
destruct (Z.eqb_spec la ha).
+ pose proof (itv_scale_sound la lb hb (zv V e2) IHe2) as X.
destruct (itv_scale la lb hb) as [l' h']; cbn in X. injection Hb as <- <-.
replace (zv V e1) with la by lia. exact X.
+ destruct (Z.eqb_spec lb hb); [|discriminate].
pose proof (itv_scale_sound lb la ha (zv V e1) IHe1) as X.
destruct (itv_scale lb la ha) as [l' h']; cbn in X. injection Hb as <- <-.
replace (zv V e2) with lb by lia. rewrite Z.mul_comm. exact X.
- discriminate.
- injection Hb as <- <-. destruct (_ <? _); cbn; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition exact_ok (VR : vranges) (b : zexp) : bool :=
match zbnd VR b with Some (lo, hi) => (0 <=? lo) && (hi <? two64) | None => false end.
Lemma exact_ok_sound : forall V VR b, vr_sound V VR -> exact_ok VR b = true -> 0 <= zv V b < two64.
Proof.
intros V VR b HV H. unfold exact_ok in H. destruct (zbnd VR b) as [[lo hi]|] eqn:Eb; [|discriminate].
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
pose proof (zbnd_sound V VR b lo hi HV Eb). Local Ltac2 Set LiaHints.tbl := fun () => "0010>41485462161.10000009S2H12H21H".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Fixpoint var_ranges (kn : list kentry) : vranges :=
match kn with
| [] => []
| KRange (EVar n) lo hi :: r => (n, lo, hi) :: var_ranges r
| _ :: r => var_ranges r
end.
Lemma var_ranges_sound : forall segs E M kn, know_ok segs E M kn -> vr_sound (uev E) (var_ranges kn).
Proof.
intros segs E M kn HK. split; [apply uev_range|].
induction kn as [|K r IH]; cbn; [constructor|].
inversion HK as [|K' r' HK1 HKr]; subst.
destruct K; try (apply IH; exact HKr). destruct e; try (apply IH; exact HKr).
constructor; [|apply IH; exact HKr]. cbn in HK1. unfold uev. exact HK1.
Qed.
Inductive mfact : Type :=
| MCell (a : zexp) (w : nat) (v : zexp)
| MZeroC (a : zexp) (n : Z)
| MRo (a : zexp) (w : nat) (v : zexp)
| MZero (a : zexp) (n : Z)
| MFill (a : zexp) (n : Z) (c : Z)
| MImg (lo hi : Z)
| MWr (a : zexp) (n : Z)
| MZeroS (a : zexp) (n : zexp)
| MWrS (a : zexp) (n : zexp).
Inductive pfact : Type :=
| PVar (n : nat) (lo hi : Z)
| PRange (e : zexp) (lo hi : Z)
| PDisj (a1 : zexp) (n1 : Z) (a2 : zexp) (n2 : Z)
| PDisjS (a1 n1 a2 n2 : zexp).
Definition cellw (w : nat) (z : Z) : cell :=
match w with
| 8%nat => C8 (Z_to_bv 64 z)
| 4%nat => C4 (Z_to_bv 64 z)
| 2%nat => C2 (Z_to_bv 64 z)
| _ => C1 (Z_to_bv 8 z)
end.
Definition is_cellw (w : nat) : bool :=
match w with 8%nat | 4%nat | 2%nat | 1%nat => true | _ => false end.
Definition zeros (n : Z) : list byte := repeat (Z_to_bv 8 0) (Z.to_nat n).
Definition sym_len (VR : vranges) (n : expr) (z : zexp) : bool :=
match zexp_of n with Some nz => zexp_eqb z nz && exact_ok VR nz | None => false end.
Lemma sym_len_sound0 : forall E VR ne n, vr_sound (uev E) VR -> sym_len VR ne n = true ->
bv_unsigned (edenot E ne) = zv (uev E) n /\ 0 <= zv (uev E) n < two64.
Proof.
intros E VR ne n HV H. unfold sym_len in H. destruct (zexp_of ne) as [nz|] eqn:Hn; [|discriminate].
apply andb_prop in H as [H1 H2]. apply zexp_eqb_eq in H1. subst nz.
pose proof (exact_ok_sound _ VR n HV H2) as R. rewrite (zexp_of_unsigned E ne n Hn).
unfold two64 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0020=21601465420.833605602172.8000003006S1RS1R".
rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section WithSegs.
Variable segs : list Segment.
Definition mfact_ok (V : nat -> Z) (m : word -> option byte) (f : mfact) : Prop :=
match f with
| MCell a w v => rw_cells segs m (zv V a) [cellw w (zv V v)]
| MZeroC a n => rw_cells segs m (zv V a) [CB (Z.to_nat n) (zeros n)]
| MRo a w v => bytes_at segs m (zv V a) (word_to_le_bytes w (Z_to_bv 64 (zv V v)))
| MZero a n => forall i, 0 <= i < n -> m (wa (zv V a + i)) = Some (Z_to_bv 8 0)
| MFill a n c => forall i, 0 <= i < n -> m (wa (zv V a + i)) = Some (Z_to_bv 8 c)
| MImg lo hi => forall i, lo <= i < hi -> m (wa i) = None
| MWr a n => wr_at segs m (zv V a) n
| MZeroS a n => forall i, 0 <= i < zv V n -> m (wa (zv V a + i)) = Some (Z_to_bv 8 0)
| MWrS a n => wr_at segs m (zv V a) (zv V n)
end.
Definition pfact_ok (V : nat -> Z) (f : pfact) : Prop :=
match f with
| PVar n lo hi => lo <= V n <= hi
| PRange e lo hi => lo <= zv V e mod two64 <= hi
| PDisj a1 n1 a2 n2 => zv V a1 + n1 <= zv V a2 \/ zv V a2 + n2 <= zv V a1
| PDisjS a1 n1 a2 n2 => zv V a1 + zv V n1 <= zv V a2 \/ zv V a2 + zv V n2 <= zv V a1
end.
Definition addr_match (VR : vranges) (sa : saddr) (a : zexp) : bool :=
match zexp_of (a_base sa) with
| Some bz => zexp_eqb a (mkaddr bz (a_off sa)) && exact_ok VR bz
| None => false
end.
Definition val_match (e : expr) (v : zexp) : bool :=
match zexp_of e with Some vz => zexp_eqb v vz | None => false end.
Definition lit_len (n : expr) (z : Z) : bool :=
match n with ELit z' => Z.eqb z z' && (0 <=? z) && (z <? two64) | _ => false end.
Definition covered (kn : list kentry) (sa : saddr) (n : Z) : bool :=
existsb (fun K => match K with
| KWr sa2 (ELit n2) => expr_eqb (a_base sa) (a_base sa2) && (a_off sa2 <=? a_off sa)
&& (a_off sa + n <=? a_off sa2 + n2) && (0 <=? n2) && (n2 <? two64) && (0 <=? n)
| _ => false end) kn.
Definition mjustify (kn : list kentry) (VR : vranges) (HLO HHI : Z) (f : mfact) : bool :=
existsb (fun K =>
match f, K with
| MCell a w v, KWord sa w' e =>
if Nat.eqb w w' && is_cellw w && addr_match VR sa a && val_match e v then covered kn sa (Z.of_nat w) else false
| MZeroC a n, KZero sa ne => if lit_len ne n && addr_match VR sa a then covered kn sa n else false
| MZeroC a n, KWord sa w (ELit 0) => if Z.eqb n (Z.of_nat w) && addr_match VR sa a then covered kn sa n else false
| MRo a w v, KWord sa w' e => Nat.eqb w w' && addr_match VR sa a && val_match e v
| MZero a n, KZero sa ne => lit_len ne n && addr_match VR sa a
| MFill a n c, KFill sa ne c' => Z.eqb c c' && lit_len ne n && addr_match VR sa a
| MImg lo hi, KImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi' && (HLO <=? lo) && (hi <=? HHI)
| MWr a n, KWr sa ne => lit_len ne n && addr_match VR sa a
| MZeroS a n, KZero sa ne => sym_len VR ne n && addr_match VR sa a
| MWrS a n, KWr sa ne => sym_len VR ne n && addr_match VR sa a
| _, _ => false
end) kn.
Definition pjustify (kn : list kentry) (VR : vranges) (f : pfact) : bool :=
existsb (fun K =>
match f, K with
| PVar n lo hi, KRange (EVar n') lo' hi' => Nat.eqb n n' && Z.eqb lo lo' && Z.eqb hi hi'
| PRange e lo hi, KRange e' lo' hi' => val_match e' e && Z.eqb lo lo' && Z.eqb hi hi'
| PDisj a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
lit_len ne1 n1 && lit_len ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
| PDisjS a1 n1 a2 n2, KDisj sa1 ne1 sa2 ne2 =>
sym_len VR ne1 n1 && sym_len VR ne2 n2 && addr_match VR sa1 a1 && addr_match VR sa2 a2
| _, _ => false
end) kn.
Section Sound.
Variable E : env.
Variable hidp : word -> bool.
Variable FULL : word -> option byte.
Variable KN : list kentry.
Variables HLO HHI : Z.
#[local] Abbreviation V := (uev E).
#[local] Abbreviation MR := (mrestrict hidp FULL).
Hypothesis KOK : know_ok segs E MR KN.
Hypothesis HID_rom : forall a, hidp a = true -> seg_rom segs a = None.
Hypothesis HULL_vis : forall a, HLO <= bv_unsigned a < HHI -> hidp a = false.
Let VRS : vr_sound V (var_ranges KN) := var_ranges_sound segs E MR KN KOK.
#[using="KOK"] Lemma kn_In : forall K, In K KN -> kentry_ok segs E MR K.
Proof. intros K HK. exact (proj1 (Forall_forall _ _) KOK K HK). Qed.
#[using="Type"] Lemma lit_len_sound : forall ne n, lit_len ne n = true -> elenZ E ne = n /\ 0 <= n < two64.
Proof.
intros ne n H. unfold lit_len in H. destruct ne; try discriminate.
apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst.
unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64 in *.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>24861558984.1443321408928.1400000700>S2H32H2S2H32H2".
rewrite Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="segs hidp FULL KOK VRS"] Lemma sym_len_sound : forall ne n, sym_len (var_ranges KN) ne n = true -> elenZ E ne = zv V n /\ 0 <= zv V n < two64.
Proof. intros ne n H. unfold elenZ. exact (sym_len_sound0 E _ ne n VRS H). Qed.
#[using="segs hidp FULL KOK VRS"] Lemma addr_match_sound : forall sa a, addr_match (var_ranges KN) sa a = true -> zv V a = estart E sa.
Proof.
intros sa a H. unfold addr_match in H. destruct (zexp_of (a_base sa)) as [bz|] eqn:Hb; [|discriminate].
apply andb_prop in H as [H1 H2]. apply zexp_eqb_eq in H1. subst a.
rewrite zv_mkaddr. unfold estart. rewrite (zexp_of_unsigned E _ _ Hb).
pose proof (exact_ok_sound V _ bz VRS H2). unfold two64 in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>16930478510.16000003S1H".
rewrite Z.mod_small by lia. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma val_match_sound : forall e v, val_match e v = true -> Z_to_bv 64 (zv V v) = edenot E e.
Proof.
intros e v H. unfold val_match in H. destruct (zexp_of e) as [vz|] eqn:He; [|discriminate].
apply zexp_eqb_eq in H. subst. apply zexp_of_sound. exact He.
Qed.
#[using="Type"] Lemma MR_some : forall a b, MR a = Some b -> FULL a = Some b.
Proof. intros a b. unfold mrestrict. destruct (hidp a); [discriminate| auto]. Qed.
#[using="HID_rom"] Lemma mrd_MR : forall a b, mrd segs MR a = Some b -> mrd segs FULL a = Some b.
Proof.
intros a b. unfold mrd, mrestrict. destruct (hidp a) eqn:Hh.
- rewrite (HID_rom a Hh). discriminate.
- destruct (FULL a); auto.
Qed.
#[using="HID_rom"] Lemma rdn_MR : forall n a bs, rdn segs MR a n = Some bs -> rdn segs FULL a n = Some bs.
Proof.
induction n as [|n IH]; intros a bs H; [exact H|].
rewrite rdn_unfold in H |- *. fold (mrd segs MR a) in H.
change (match MR a with Some b => Some b | None => seg_rom segs a end) with (mrd segs MR a) in H.
destruct (mrd segs MR a) as [b|] eqn:Hm; [|discriminate].
rewrite (mrd_MR a b Hm). destruct (rdn segs MR (a + 1)%bv n) as [r|] eqn:Hr; [|discriminate].
rewrite (IH _ _ Hr). exact H.
Qed.
#[using="Type"] Lemma wview_MR : forall a, wview segs MR a <> None -> wview segs FULL a <> None.
Proof.
intros a. unfold wview, mrestrict. destruct (hidp a); destruct (FULL a); congruence.
Qed.
#[using="Type"] Lemma rdn_bytes_at : forall n A bs, 0 <= A -> A + Z.of_nat n <= two64 ->
rdn segs FULL (wa A) n = Some bs -> bytes_at segs FULL A bs.
Proof.
induction n as [|n IH]; intros A bs HA HB H.
- cbn in H. injection H as <-. Local Ltac2 Set LiaHints.tbl := fun () => "0090>13568532762.1614366268853.2519014448958.2524931808907.1424933921787.2334379521251.203801704398.23 40669649743.1463596540956.2200000700C00O00V00b00f00o01301?S2HB2HiS2HB4Hlen2HiS2HB4Hlen2HiS2HA2HBS2HA2HB4HlenS2HBS2HB4HlenS2HBS2HA2HB4Hlen".
split; [lia|]. split; [cbn; unfold two64 in *; lia|]. intros i Hi. cbn in Hi. lia.
- rewrite rdn_unfold in H.
change (match FULL (wa A) with Some b => Some b | None => seg_rom segs (wa A) end) with (mrd segs FULL (wa A)) in H.
destruct (mrd segs FULL (wa A)) as [b|] eqn:Hm; [|discriminate].
destruct (rdn segs FULL (wa A + 1)%bv n) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
rewrite wa_succ in Hr.
assert (HB' : A + 1 + Z.of_nat n <= two64) by lia.
pose proof (rdn_length _ _ _ _ _ Hr) as Hlen.
destruct (IH (A + 1) r ltac:(lia) HB' Hr) as (_ & _ & IHr).
split; [lia|]. split; [cbn [length]; rewrite Hlen; unfold two64 in HB; lia|].
intros [|i] Hi; cbn [nth_error].
+ rewrite Z.add_0_r. exact Hm.
+ replace (A + Z.of_nat (S i)) with (A + 1 + Z.of_nat i) by lia. apply IHr. cbn in Hi. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="hidp KOK"] Lemma covered_sound : forall sa n, covered KN sa n = true ->
forall i, 0 <= i < n -> wview segs FULL (wa (estart E sa + i)) <> None.
Proof.
intros sa n H i Hi. unfold covered in H. apply existsb_exists in H as (K & HK & HKm).
destruct K; try discriminate. destruct n0; try discriminate.
repeat (apply andb_prop in HKm as [HKm ?]).
apply Z.leb_le in H3. apply Z.leb_le in H2. apply Z.leb_le in H1. apply Z.ltb_lt in H0. apply Z.leb_le in H.
pose proof (kn_In _ HK) as [Hfl Hst]. cbn [kentry_ok] in Hfl, Hst.
assert (Elen : elenZ E (ELit z) = z).
{ unfold elenZ. cbn [edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64 in *. apply Z.mod_small. Local Ltac2 Set LiaHints.tbl := fun () => "0050>16031950642.2824863664910.2629987338659.2734267120903.289735785859.28 00000700>00?00C00JS2H22HiS2H12H0SS2EbS2H32Hi".
lia. }
rewrite Elen in Hst, Hfl.
assert (Eb : estart E sa = estart E a + (a_off sa - a_off a)).
{ unfold estart. apply expr_eqb_eq in HKm. rewrite HKm. lia. }
specialize (Hst (a_off sa - a_off a + i) 1%nat ltac:(lia) ltac:(cbn; lia)).
apply wview_MR. cbn [RiscvSemantics.store_ok] in Hst.
replace (estart E sa + i) with (estart E a + (a_off sa - a_off a + i)) by lia.
destruct (wview segs MR _); [discriminate| discriminate Hst].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma word_to_le_bytes_zero : forall w, word_to_le_bytes w (Z_to_bv 64 0) = zeros (Z.of_nat w).
Proof.
intros w. unfold word_to_le_bytes, zeros. rewrite Nat2Z.id. rewrite Z_to_bv_unsigned. change (bv_wrap 64 0) with 0.
induction w as [|w IH]; [reflexivity|]. cbn [Z_to_le_bytes repeat]. rewrite Z.shiftr_0_l. f_equal. exact IH.
Qed.
#[using="Type"] Lemma cellw_bytes : forall w z, is_cellw w = true ->
cbytes (cellw w z) = word_to_le_bytes w (Z_to_bv 64 z) /\ csize (cellw w z) = w /\ cell_wf (cellw w z).
Proof.
intros w z Hw. unfold is_cellw in Hw.
destruct w as [|[|[|[|[|[|[|[|[|w]]]]]]]]]; try discriminate; cbn -[Z_to_bv word_to_le_bytes le8 le4 le2];
repeat split; try reflexivity.
unfold word_to_le_bytes. cbn [Z_to_le_bytes]. f_equal.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_mod_divide; [reflexivity|]. exists (2 ^ 56). reflexivity.
Qed.
#[using="hidp KOK HID_rom HULL_vis VRS"] Lemma mjustify_sound : forall f, mjustify KN (var_ranges KN) HLO HHI f = true -> mfact_ok V FULL f.
Proof.
intros f H. unfold mjustify in H. apply existsb_exists in H as (K & HK & HKm).
pose proof (kn_In K HK) as KOKK.
destruct f; destruct K; try discriminate; cbn [kentry_ok] in KOKK; cbn [mfact_ok].
-
match type of HKm with (if ?c then _ else _) = true => destruct c eqn:HKc; [|discriminate HKm]; rename HKm into H; rename HKc into HKm end.
repeat (apply andb_prop in HKm as [HKm ?]). apply Nat.eqb_eq in HKm. subst w0.
pose proof (addr_match_sound _ _ H1) as Ea. pose proof (val_match_sound _ _ H0) as Ev.
destruct KOKK as (Hw & Hfl & Hrd). pose proof (flat_u _ _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
pose proof (cellw_bytes w (zv V v) H2) as (Cb & Cs & Cwf).
split.
+ split; [cbn; split; [exact Cwf| exact I]|]. cbn [cells_bytes]. rewrite app_nil_r, Cb, Ev, Ea.
Local Ltac2 Set LiaHints.tbl := fun () => "00E0>10351595562.2713327152726.2513327152726.2813329428807.3318065023120.272425008819.26 30147832930.2130670142800.3330672203861.2530672203861.2630672419393.2530672419393.2836962134385.2447024461702.2748893931326.2549969523241.2549969523241.26548305750.28  62280508270.2462280508270.2566253720165.2100000400;00B00L00P00T00]00g00k00o01601=01A01E01I01M01Q01X01\01`01jS2HiS2Hw2F4S2Hw2F4S2Hw2F42CsS2HiS2HnS2H01H2HiS2Hw2F12CsS2F1S2F1S2Hw2F1S2Hw2F1S2HiS2HiS2F4S2F4S2F4S2F32HiS2HiS2HiS2K12K22Hi".
apply (rdn_bytes_at w); [lia| unfold two64; lia|]. apply rdn_MR. unfold wa. rewrite <- Hu, Z_to_bv_bv_unsigned. exact Hrd.
+ cbn [cells_size]. rewrite Cs, Nat.add_0_r, Ea. split; [lia|]. split; [unfold two64 in *; lia|].
apply covered_sound. exact H.
-
destruct v; try discriminate. destruct z; try discriminate.
match type of HKm with (if ?c then _ else _) = true => destruct c eqn:HKc; [|discriminate HKm]; rename HKm into H; rename HKc into HKm end.
repeat (apply andb_prop in HKm as [HKm ?]). apply Z.eqb_eq in HKm. subst n.
pose proof (addr_match_sound _ _ H0) as Ea.
destruct KOKK as (Hw & Hfl & Hrd). pose proof (flat_u _ _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
split.
+ split; [cbn; split; [unfold zeros; rewrite repeat_length; reflexivity| exact I]|].
cbn [cells_bytes cbytes]. rewrite app_nil_r, Ea, <- word_to_le_bytes_zero.
apply (rdn_bytes_at w); [lia| unfold two64; lia|]. apply rdn_MR. unfold wa. rewrite <- Hu, Z_to_bv_bv_unsigned. exact Hrd.
+ cbn [cells_size csize]. rewrite Nat.add_0_r, Nat2Z.id, Ea. split; [lia|]. split; [unfold two64 in *; lia|].
apply covered_sound. exact H.
-
match type of HKm with (if ?c then _ else _) = true => destruct c eqn:HKc; [|discriminate HKm]; rename HKm into H; rename HKc into HKm end.
repeat (apply andb_prop in HKm as [HKm ?]). apply lit_len_sound in HKm as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ H0) as Ea. destruct KOKK as (Hfl & Hz). destruct Hfl as (F1 & F2 & F3 & F4).
split.
+ split; [cbn; split; [unfold zeros; rewrite repeat_length; reflexivity| exact I]|].
cbn [cells_bytes cbytes]. rewrite app_nil_r, Ea. split; [lia|]. split; [unfold zeros; rewrite repeat_length, Z2Nat.id by lia; unfold two64 in *; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi.
rewrite (nth_error_repeat (Z_to_bv 8 0) Hi). unfold mrd, wa. rewrite (MR_some _ _ (Hz (Z.of_nat i) ltac:(lia))). reflexivity.
+ cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id, Ea by lia. split; [lia|]. split; [unfold two64 in *; lia|].
apply covered_sound. exact H.
-
repeat (apply andb_prop in HKm as [HKm ?]). apply Nat.eqb_eq in HKm. subst w0.
pose proof (addr_match_sound _ _ H0) as Ea. pose proof (val_match_sound _ _ H) as Ev.
destruct KOKK as (Hw & Hfl & Hrd). pose proof (flat_u _ _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
rewrite Ev, Ea. apply (rdn_bytes_at w); [lia| unfold two64; lia|]. apply rdn_MR. unfold wa. rewrite <- Hu, Z_to_bv_bv_unsigned. exact Hrd.
-
apply andb_prop in HKm as [HKm Ha]. apply lit_len_sound in HKm as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ Ha) as Ea. destruct KOKK as (Hfl & Hz). rewrite Ea.
intros i Hi. apply MR_some. unfold wa. apply Hz. lia.
-
repeat (apply andb_prop in HKm as [HKm ?]). apply Z.eqb_eq in HKm. subst c0.
apply lit_len_sound in H0 as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ H) as Ea. destruct KOKK as (Hfl & Hz). rewrite Ea.
intros i Hi. apply MR_some. unfold wa. apply Hz. lia.
-
repeat (apply andb_prop in HKm as [HKm ?]). apply Z.eqb_eq in HKm. apply Z.eqb_eq in H1. subst lo0 hi0.
apply Z.leb_le in H0. apply Z.leb_le in H. destruct KOKK as (K1 & K2 & K3).
intros i Hi. specialize (K3 i Hi). unfold mrestrict in K3.
rewrite (HULL_vis (Z_to_bv 64 i)) in K3; [exact K3|]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
rewrite Z.mod_small by lia. lia.
-
apply andb_prop in HKm as [HKm Ha]. apply lit_len_sound in HKm as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ Ha) as Ea. destruct KOKK as (Hfl & Hst). destruct Hfl as (F1 & F2 & F3 & F4). rewrite Ea.
split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
specialize (Hst i 1%nat ltac:(lia) ltac:(cbn; lia)). apply wview_MR. cbn [RiscvSemantics.store_ok] in Hst.
destruct (wview segs MR _); [discriminate| discriminate Hst].
-
apply andb_prop in HKm as [HKm Ha]. apply sym_len_sound in HKm as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ Ha) as Ea. destruct KOKK as (Hfl & Hz). rewrite Ea.
intros i Hi. apply MR_some. unfold wa. apply Hz. lia.
-
apply andb_prop in HKm as [HKm Ha]. apply sym_len_sound in HKm as [En Hn]. rewrite En in KOKK.
pose proof (addr_match_sound _ _ Ha) as Ea. destruct KOKK as (Hfl & Hst). destruct Hfl as (F1 & F2 & F3 & F4). rewrite Ea.
split; [lia|]. split; [unfold two64 in *; lia|]. intros i Hi.
specialize (Hst i 1%nat ltac:(lia) ltac:(cbn; lia)). apply wview_MR. cbn [RiscvSemantics.store_ok] in Hst.
destruct (wview segs MR _); [discriminate| discriminate Hst].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="segs hidp FULL KOK VRS"] Lemma pjustify_sound : forall f, pjustify KN (var_ranges KN) f = true -> pfact_ok V f.
Proof.
intros f H. unfold pjustify in H. apply existsb_exists in H as (K & HK & HKm).
pose proof (kn_In K HK) as KOKK.
destruct f; destruct K; try discriminate; cbn [kentry_ok] in KOKK; cbn [pfact_ok].
- destruct e; try discriminate. repeat (apply andb_prop in HKm as [HKm ?]).
apply Nat.eqb_eq in HKm. apply Z.eqb_eq in H0. apply Z.eqb_eq in H. subst. unfold uev. exact KOKK.
- repeat (apply andb_prop in HKm as [HKm ?]). apply Z.eqb_eq in H0. apply Z.eqb_eq in H. subst.
pose proof (val_match_sound _ _ HKm) as Ev. rewrite <- Ev, Z_to_bv_unsigned in KOKK. exact KOKK.
- repeat (apply andb_prop in HKm as [HKm ?]).
apply lit_len_sound in HKm as [E1 _]. apply lit_len_sound in H1 as [E2 _].
rewrite (addr_match_sound _ _ H0), (addr_match_sound _ _ H). rewrite E1, E2 in KOKK. exact KOKK.
-
repeat (apply andb_prop in HKm as [HKm ?]).
apply sym_len_sound in HKm as [E1 _]. apply sym_len_sound in H1 as [E2 _].
rewrite (addr_match_sound _ _ H0), (addr_match_sound _ _ H). rewrite E1, E2 in KOKK. exact KOKK.
Qed.
#[using="hidp KOK HID_rom HULL_vis VRS"] Theorem export_sound : forall MF PF,
forallb (mjustify KN (var_ranges KN) HLO HHI) MF = true ->
forallb (pjustify KN (var_ranges KN)) PF = true ->
Forall (mfact_ok V FULL) MF /\ Forall (pfact_ok V) PF.
Proof.
intros MF PF HM HP. split.
- apply Forall_forall. intros f Hf. apply mjustify_sound. exact (proj1 (forallb_forall _ _) HM f Hf).
- apply Forall_forall. intros f Hf. apply pjustify_sound. exact (proj1 (forallb_forall _ _) HP f Hf).
Qed.
End Sound.
Definition mfact_eqb (f g : mfact) : bool :=
match f, g with
| MCell a w v, MCell a' w' v' => zexp_eqb a a' && Nat.eqb w w' && zexp_eqb v v'
| MZeroC a n, MZeroC a' n' => zexp_eqb a a' && Z.eqb n n'
| MRo a w v, MRo a' w' v' => zexp_eqb a a' && Nat.eqb w w' && zexp_eqb v v'
| MZero a n, MZero a' n' => zexp_eqb a a' && Z.eqb n n'
| MFill a n c, MFill a' n' c' => zexp_eqb a a' && Z.eqb n n' && Z.eqb c c'
| MImg lo hi, MImg lo' hi' => Z.eqb lo lo' && Z.eqb hi hi'
| MWr a n, MWr a' n' => zexp_eqb a a' && Z.eqb n n'
| MZeroS a n, MZeroS a' n' => zexp_eqb a a' && zexp_eqb n n'
| MWrS a n, MWrS a' n' => zexp_eqb a a' && zexp_eqb n n'
| _, _ => false
end.
#[using="Type"] Lemma mfact_eqb_eq : forall f g, mfact_eqb f g = true -> f = g.
Proof.
intros f g H. destruct f, g; cbn in H; try discriminate;
repeat match goal with K : (_ && _) = true |- _ => apply andb_prop in K as [? K] end;
repeat match goal with
| K : zexp_eqb _ _ = true |- _ => apply zexp_eqb_eq in K
| K : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in K
| K : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in K end; subst; reflexivity.
Qed.
#[using="Type"] Lemma mfact_find : forall V m (l : list mfact) f,
Forall (mfact_ok V m) l -> existsb (mfact_eqb f) l = true -> mfact_ok V m f.
Proof.
intros V m l f HF HE. apply existsb_exists in HE as (g & Hin & Hg). apply mfact_eqb_eq in Hg. subst g.
exact (proj1 (Forall_forall _ _) HF f Hin).
Qed.
#[using="Type"] Lemma mimg_cover : forall V m l lo hi,
Forall (mfact_ok V m) l ->
existsb (fun f => match f with MImg lo' hi' => (lo' <=? lo) && (hi <=? hi') | _ => false end) l = true ->
forall i, lo <= i < hi -> m (wa i) = None.
Proof.
intros V m l lo hi HF HE i Hi. apply existsb_exists in HE as (f & Hin & Hf).
destruct f; try discriminate. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HF _ Hin) as K. cbn in K. apply K. Local Ltac2 Set LiaHints.tbl := fun () => "0010>68164613342.1500000:S2H12H22Hi".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma mwr_find : forall V m l a n,
Forall (mfact_ok V m) l ->
existsb (fun f => match f with MWr a' n' => zexp_eqb a' a && (n' =? n) | _ => false end) l = true ->
wr_at segs m (zv V a) n.
Proof.
intros V m l a n HF HE. apply existsb_exists in HE as (f & Hin & Hf).
destruct f; try discriminate. apply andb_prop in Hf as [H1 H2]. apply zexp_eqb_eq in H1. apply Z.eqb_eq in H2. subst.
exact (proj1 (Forall_forall _ _) HF _ Hin).
Qed.
#[using="Type"] Lemma mzero_rw_cells : forall m A n,
(forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) -> wr_at segs m A n -> 0 <= n ->
rw_cells segs m A [CB (Z.to_nat n) (zeros n)].
Proof.
intros m A n Hz (W1 & W2 & W3) Hn. split.
- split; [cbn; split; [unfold zeros; rewrite repeat_length; reflexivity| exact I]|].
cbn [cells_bytes cbytes]. rewrite app_nil_r. Local Ltac2 Set LiaHints.tbl := fun () => "0040=23369229869.92424960062.9 24931803367.9548305750.11 00000400800<00@S2W2S2HnS2W1S2Hi".
split; [lia|]. split; [unfold zeros; rewrite repeat_length, Z2Nat.id by lia; lia|].
intros i Hi. unfold zeros in Hi |- *. rewrite repeat_length in Hi. rewrite (nth_error_repeat (Z_to_bv 8 0) Hi).
unfold mrd. rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
- cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. split; [lia|]. split; [lia|]. exact W3.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma overlay_zero_rw : forall m lo n,
0 <= lo -> lo + n <= two64 -> 0 <= n ->
(forall i, 0 <= i < n -> m (wa (lo + i)) = Some (Z_to_bv 8 0)) ->
wr_at segs m lo n /\ rw_cells segs m lo [CB (Z.to_nat n) (zeros n)].
Proof.
intros m lo n Hlo Hhi Hn Hz.
assert (W : wr_at segs m lo n).
{ Local Ltac2 Set LiaHints.tbl := fun () => "0020=29430564257.851604226999.800000500:S3HloS3Hhi".
split; [lia|]. split; [unfold two64 in Hhi; lia|]. intros i Hi. unfold wview. rewrite (Hz i Hi). discriminate. }
split; [exact W|]. apply mzero_rw_cells; assumption.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma wr_at_stk : forall m lo hi,
wr_at segs m lo (hi - lo) -> (forall a, lo <= a < hi -> find_segment segs a 1 = None) -> stk segs m lo hi.
Proof.
intros m lo hi (W1 & W2 & W3) Hseg. Local Ltac2 Set LiaHints.tbl := fun () => "0050>23425304537.1029443148594.8 52371395569.8 56765667309.1157242057209.1000000400800<00F00GS2HaS2W1S2W2S2W12W22HaS".
split; [lia|]. split; [lia|]. intros a Ha.
specialize (W3 (a - lo) ltac:(lia)). replace (lo + (a - lo)) with a in W3 by lia. split; [exact W3|].
unfold wview in W3. unfold mrd. destruct (m (wa a)) as [b|] eqn:Hm; [exists b; reflexivity|].
rewrite wa_unsigned in W3 by lia. rewrite (Hseg a Ha) in W3. congruence.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End WithSegs.
Definition in_ivs (z : Z) (l : list (word * word)) : Prop :=
exists iv, In iv l /\ bv_unsigned (fst iv) <= z < bv_unsigned (fst iv) + bv_unsigned (snd iv).
Definition ivs_sep (l : list (word * word)) : Prop :=
forall i j p q, (i < j)%nat -> nth_error l i = Some p -> nth_error l j = Some q ->
bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q)
\/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Fixpoint ivs_sum (l : list (word * word)) : Z :=
match l with [] => 0 | iv :: r => bv_unsigned (snd iv) + ivs_sum r end.
Definition pagedown (z : Z) : Z := z / 4096 * 4096.
Definition pageup (z : Z) : Z := (z + 4095) / 4096 * 4096.
Definition allow_of (shoff : Z) (V : nat -> Z) (vis : list (zexp * zexp)) : list (Z * Z) :=
flat_map (fun bn : zexp * zexp => let b := zv V (fst bn) in let n := zv V (snd bn) in
[(pagedown b, pageup (b + n)); (pagedown (shoff + b / 8), pageup (shoff + (b + n) / 8))]) vis.
Definition aallowed (A : list (Z * Z)) (p : word) : Prop :=
exists iv, In iv A /\ fst iv <= bv_unsigned p /\ bv_unsigned p + 4096 <= snd iv.
Fixpoint ivz_bytes (A : list (Z * Z)) : Z :=
match A with [] => 0 | iv :: r => (snd iv - fst iv) + ivz_bytes r end.
Definition ivz_wf (A : list (Z * Z)) : Prop :=
Forall (fun iv => fst iv <= snd iv /\ fst iv mod 4096 = 0 /\ snd iv mod 4096 = 0) A.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma nodup_length_le : forall {X} (d : forall x y : X, {x = y} + {x <> y}) (l : list X), (length (nodup d l) <= length l)%nat.
Proof. intros X d l. Local Ltac2 Set LiaHints.tbl := fun () => "0030=19080268573.23492888893.6 44061344169.6000001005009SS2IHS2IH".
induction l as [|x l IH]; cbn; [lia|]. destruct (in_dec d x l); cbn; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition word_eq_dec : forall x y : word, {x = y} + {x <> y} := fun x y => bv_eq_dec 64 x y.
Definition pages_of (iv : Z * Z) : list word :=
map (fun k => wa (fst iv + 4096 * Z.of_nat k)) (seq 0 (Z.to_nat ((snd iv - fst iv) / 4096))).
Lemma ivz_bytes_pages : forall A, ivz_wf A ->
Z.of_nat (length (flat_map pages_of A)) = ivz_bytes A / 4096 /\ 0 <= ivz_bytes A /\ ivz_bytes A mod 4096 = 0.
Proof.
intros A HW. induction HW as [|iv r Hiv HW IH]; cbn; [repeat split; reflexivity|].
rewrite length_app, Nat2Z.inj_add. unfold pages_of at 1. rewrite length_map, length_seq.
destruct IH as (IH1 & IH2 & IH3). destruct Hiv as (H1 & H2 & H3). rewrite IH1.
Local Ltac2 Set LiaHints.tbl := fun () => "0030=18926747563.921050967175.95086834734.9 00000100G00KSS2H12H22H33IH13IH23IH3S2H1".
rewrite Z2Nat.id by (apply Z.div_pos; lia). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma aallowed_fin : forall A, ivz_wf A ->
exists L : list word, List.NoDup L /\ Z.of_nat (length L) <= ivz_bytes A / 4096 /\
forall p : word, bv_unsigned p mod 4096 = 0 -> aallowed A p -> In p L.
Proof.
intros A HW. exists (nodup word_eq_dec (flat_map pages_of A)).
split; [apply NoDup_nodup|]. split.
- pose proof (nodup_length_le word_eq_dec (flat_map pages_of A)). pose proof (ivz_bytes_pages A HW) as (E & _). Local Ltac2 Set LiaHints.tbl := fun () => "0050>18928402731.1147856414421.115084892846.11 5556316622.11 8425643803.4  00000100200600;00@SSS2W1S3HloS1H1E".
lia.
- intros p Hp (iv & Hin & Hlo & Hhi). apply nodup_In. apply in_flat_map. exists iv. split; [exact Hin|].
pose proof (proj1 (Forall_forall _ _) HW iv Hin) as (W1 & W2 & W3). cbn in W1, W2, W3.
unfold pages_of. apply in_map_iff. exists (Z.to_nat ((bv_unsigned p - fst iv) / 4096)).
split.
+ rewrite Z2Nat.id by (apply Z.div_pos; lia). unfold wa.
replace (fst iv + 4096 * ((bv_unsigned p - fst iv) / 4096)) with (bv_unsigned p) by nia. apply Z_to_bv_bv_unsigned.
+ apply in_seq. split; [lia|]. cbn. apply Z2Nat.inj_lt; try (apply Z.div_pos; lia). apply Z.div_lt_upper_bound; [lia|]. nia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Fixpoint vis_match (VR : vranges) (ps : list (expr * expr)) (vis : list (zexp * zexp)) : bool :=
match ps, vis with
| [], [] => true
| (eb, en) :: ps', (bz, n) :: vis' =>
match zexp_of eb with
| Some bz' => zexp_eqb bz bz' && exact_ok VR bz && sym_len VR en n && vis_match VR ps' vis'
| None => false
end
| _, _ => false
end.
Lemma vis_match_sound : forall E VR ps vis, vr_sound (uev E) VR -> vis_match VR ps vis = true ->
Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
bv_unsigned (edenot E (fst p)) = zv (uev E) (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv (uev E) (snd bn)
/\ 0 <= zv (uev E) (snd bn)) ps vis.
Proof.
intros E VR ps. induction ps as [|[eb en] ps IH]; intros [|[bz n] vis] HV H; cbn -[sym_len exact_ok zexp_eqb zexp_of] in H; try discriminate; [constructor|].
destruct (zexp_of eb) as [bz'|] eqn:Hb; [|discriminate].
repeat (apply andb_prop in H as [H ?]). apply zexp_eqb_eq in H. subst bz'.
constructor; [|apply IH; assumption]. cbn. split; [|].
- rewrite (zexp_of_unsigned E eb bz Hb). pose proof (exact_ok_sound _ VR bz HV H2). unfold two64 in *. apply Z.mod_small. Local Ltac2 Set LiaHints.tbl := fun () => "0020>16930478510.1547070039894.16000003007S1HS2E2".
lia.
- pose proof (sym_len_sound0 E VR en n HV H1) as [E1 E2]. split; [exact E1| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Inductive lentry : Type :=
| LMap (b : zexp) (n : Z) (k : mkind)
| LFog (n : Z).
Fixpoint ledger_den (V : nat -> Z) (l : list lentry) (maps : list (word * word)) : Prop :=
match l with
| [] => maps = []
| LMap b n _ :: l' => exists maps', maps = (wa (zv V b), wa n) :: maps' /\ ledger_den V l' maps'
| LFog n :: l' => ledger_den V l' maps
\/ exists iv maps', maps = iv :: maps' /\ bv_unsigned (snd iv) <= n /\ ledger_den V l' maps'
end.
Definition lentry_kind_ok (V : nat -> Z) (mo : Model) (e : lentry) : Prop :=
match e with
| LMap b n KNONE | LMap b n KNONELAZY => In (wa (zv V b), wa n) (vm_noaccess (m_vmmaps mo))
| LMap b n KRWLAZY => forall a : word, zv V b <= bv_unsigned a < zv V b + n ->
~ in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps mo))
/\ page_in_ranges (page_base a) (m_vm_lazy mo) = true
| _ => True
end.
Fixpoint ledger_xmatch (VR : vranges) (ms : list amap) (l : list lentry) : bool :=
match ms, l with
| [], [] => true
| m :: ms', e :: l' =>
(match e with
| LMap b n k => negb (is_fog m) && mkind_eqb (am_kind m) k
&& match zexp_of (am_base m) with Some bz => zexp_eqb b bz && exact_ok VR bz | None => false end
&& lit_len (am_len m) n
| LFog n => is_fog m && lit_len (am_len m) n
end) && ledger_xmatch VR ms' l'
| _, _ => false
end.
Lemma in_ivs_APS : forall z l, APS.in_ivs z l = true <-> in_ivs z l.
Proof.
intros z l. unfold APS.in_ivs, in_ivs. rewrite existsb_exists. split.
- intros (iv & Hin & H). apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists iv. Local Ltac2 Set LiaHints.tbl := fun () => "0030=13004177900.629098237283.56824733639.5 00000700:00=S2H12H2S1HS1H".
split; [exact Hin| lia].
- intros (iv & Hin & H). exists iv. split; [exact Hin|]. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Section LedgerSound.
Variable E : env.
Variable VR : vranges.
Hypothesis HV : vr_sound (uev E) VR.
#[using="HV"] Lemma lmap_match_den : forall m b n,
match zexp_of (am_base m) with Some bz => zexp_eqb b bz && exact_ok VR bz | None => false end = true ->
lit_len (am_len m) n = true ->
APS.amap_den E m = (wa (zv (uev E) b), wa n) /\ bv_unsigned (edenot E (am_base m)) = zv (uev E) b /\ bv_unsigned (edenot E (am_len m)) = n.
Proof.
intros m b n Hb Hn. destruct (zexp_of (am_base m)) as [bz|] eqn:Ez; [|discriminate].
apply andb_prop in Hb as [H1 H2]. apply zexp_eqb_eq in H1. subst bz.
pose proof (exact_ok_sound _ VR b HV H2) as Hr. pose proof (zexp_of_sound E _ _ Ez) as Hs.
unfold lit_len in Hn. destruct (am_len m) eqn:El; try discriminate.
repeat (apply andb_prop in Hn as [Hn ?]). apply Z.eqb_eq in Hn. apply Z.leb_le in H0. apply Z.ltb_lt in H. subst z.
unfold APS.amap_den. rewrite El, <- Hs. cbn [edenot]. unfold wa. split; [reflexivity|].
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus, two64 in *. cbn [Z.of_N]. Local Ltac2 Set LiaHints.tbl := fun () => "0030>39717587108.1350776678035.1361929755223.1300000100500;SS2HrS2H01H".
rewrite !Z.mod_small by lia. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HV"] Lemma ledger_den_sound : forall ms l maps,
ledger_xmatch VR ms l = true -> APS.maps_match E ms maps -> ledger_den (uev E) l maps.
Proof.
induction ms as [|m ms IH]; intros [|e l] maps HX HM; cbn in HX; try discriminate; [exact HM|].
apply andb_prop in HX as [He HX']. cbn [APS.maps_match] in HM. destruct e as [b n k|n]; cbn [ledger_den].
- repeat (apply andb_prop in He as [He ?]). apply negb_true_iff in He. rewrite He in HM.
destruct HM as (maps' & -> & HM'). destruct (lmap_match_den m b n H0 H) as (Ed & _ & _).
exists maps'. rewrite Ed. split; [reflexivity| apply IH; assumption].
- apply andb_prop in He as [Hf Hn]. rewrite Hf in HM.
unfold lit_len in Hn. destruct (am_len m) eqn:El; try discriminate.
repeat (apply andb_prop in Hn as [Hn ?]). apply Z.eqb_eq in Hn. apply Z.leb_le in H0. apply Z.ltb_lt in H. subst z.
destruct HM as [HM | (iv & maps' & -> & Hsz & HM')].
+ left. apply IH; assumption.
+ right. exists iv, maps'. split; [reflexivity|]. split; [|apply IH; assumption].
unfold APS.uE in Hsz. rewrite ?El in Hsz. cbn [edenot] in Hsz. rewrite Z_to_bv_unsigned in Hsz.
unfold bv_wrap, bv_modulus, two64 in *. cbn [Z.of_N] in Hsz. Local Ltac2 Set LiaHints.tbl := fun () => "0010>61931851531.17000006S2H01H".
rewrite Z.mod_small in Hsz by lia. exact Hsz.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="HV"] Lemma ledger_kinds_sound : forall ms l mo,
ledger_xmatch VR ms l = true ->
Forall (fun m => am_kind m = KNONE \/ am_kind m = KNONELAZY -> In (APS.amap_den E m) (vm_noaccess (m_vmmaps mo))) ms ->
Forall (fun m => am_kind m = KRWLAZY ->
forall a : word, bv_unsigned (edenot E (am_base m)) <= bv_unsigned a < bv_unsigned (edenot E (am_base m)) + bv_unsigned (edenot E (am_len m)) ->
APS.in_ivs (bv_unsigned a) (vm_noaccess (m_vmmaps mo)) = false
/\ page_in_ranges (page_base a) (m_vm_lazy mo) = true) ms ->
Forall (lentry_kind_ok (uev E) mo) l.
Proof.
induction ms as [|m ms IH]; intros [|e l] mo HX HN HK; cbn in HX; try discriminate; [constructor|].
apply andb_prop in HX as [He HX']. inversion HN as [|m' ms' HN1 HNr]; subst. inversion HK as [|m' ms' HK1 HKr]; subst.
constructor; [|apply IH; assumption].
destruct e as [b n k|n]; cbn [lentry_kind_ok]; [|exact I].
repeat (apply andb_prop in He as [He ?]). destruct (lmap_match_den m b n H0 H) as (Ed & Eb & En).
assert (Hk : am_kind m = k) by (destruct (am_kind m), k; try reflexivity; discriminate H1).
destruct k; try exact I.
- intros a Ha. rewrite <- Eb, <- En in Ha. destruct (HK1 Hk a Ha) as [X Y]. split; [|exact Y].
intros Hin. apply in_ivs_APS in Hin. congruence.
- rewrite <- Ed. apply HN1. left. exact Hk.
- rewrite <- Ed. apply HN1. right. exact Hk.
Qed.
End LedgerSound.
Lemma reg_get_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 n,
(1 <= n <= 31)%nat ->
reg_get (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
(Z_to_bv 5 (Z.of_nat n))
= nth n [w0; x1; x2; x3; x4; x5; x6; x7; x8; x9; x10; x11; x12; x13; x14; x15; x16; x17; x18; x19; x20; x21; x22; x23; x24; x25; x26; x27; x28; x29; x30; x31] w0.
Proof. intros. do 32 (destruct n as [|n]; [reflexivity || lia|]). Local Ltac2 Set LiaHints.tbl := fun () => "0010>39868525732.33000003S1H".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma regs_ok_nth : forall E sr R, AX2S.regs_ok E sr R ->
forall n, (1 <= n <= 31)%nat -> reg_get R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0)).
Proof.
intros E sr R H n Hn. unfold AX2S.regs_ok, AS.PropExec.getr, sr_get, ridx in H.
specialize (H (Z_to_bv 5 (Z.of_nat n))).
Local Ltac2 Set LiaHints.tbl := fun () => "0030=48826935356.57309732485.5 7309732485.6 000004005009S2HnFS2Hn".
do 32 (destruct n as [|n]; [first [lia | exact H] |]). lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma is_x0_of_nat : forall n, (n < 32)%nat -> is_x0 (Z_to_bv 5 (Z.of_nat n)) = false -> (1 <= n <= 31)%nat.
Proof. intros n Hn H. Local Ltac2 Set LiaHints.tbl := fun () => "0010=42311782046.3000004S2Hn".
destruct n as [|n]; [cbv in H; discriminate| lia]. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma seps_ivs_sep : forall l, APS.seps l -> ivs_sep l.
Proof.
intros l H. induction H as [|p l Hp Hs IH]; intros i j a b Hij Hi Hj.
- destruct i; discriminate.
- Local Ltac2 Set LiaHints.tbl := fun () => "0040>10907088295.123705733907.10 3705733907.11 3705733907.12 00000500:00?00@S3HijS3HijS3HijF".
destruct i as [|i]; destruct j as [|j]; try lia; cbn in Hi, Hj.
+ injection Hi as <-. apply nth_error_In in Hj. pose proof (proj1 (Forall_forall _ _) Hp b Hj) as X.
unfold APS.iv_disjoint in X. exact X.
+ eapply IH; [|exact Hi|exact Hj]. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Lemma allowA_allow_of : forall (A : atable) E (ps : list (expr * expr)) (vis : list (zexp * zexp)),
Forall2 (fun (p : expr * expr) (bn : zexp * zexp) =>
bv_unsigned (edenot E (fst p)) = zv (uev E) (fst bn) /\ bv_unsigned (edenot E (snd p)) = zv (uev E) (snd bn)
/\ 0 <= zv (uev E) (snd bn)) ps vis ->
flat_map (APS.allow1 A E) ps = allow_of (shadow_off A) (uev E) vis.
Proof.
intros A E ps vis H. induction H as [|[eb en] [bz n] ps vis (H1 & H2 & H3) H IH]; [reflexivity|].
cbn [flat_map allow_of]. cbn in H1, H2. unfold APS.allow1, APS.sh_lo, APS.sh_hi, APS.uE. cbn [fst snd].
rewrite H1, H2. unfold allow_of in IH. cbn [flat_map] in IH. unfold APS.allow1, APS.sh_lo, APS.sh_hi, APS.uE in IH. rewrite IH. reflexivity.
Qed.
Lemma page_allowedb_aallowed : forall A p, page_allowedb A p = true -> aallowed A p.
Proof.
intros A p H. unfold page_allowedb in H. apply existsb_exists in H as (iv & Hin & Hb).
apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists iv. unfold page_size in H2. Local Ltac2 Set LiaHints.tbl := fun () => "0010=33591350574.6000007S2H12H2".
split; [exact Hin| lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Fixpoint pvranges (l : list pfact) : vranges :=
match l with
| [] => []
| PVar n lo hi :: r => (n, lo, hi) :: pvranges r
| _ :: r => pvranges r
end.
Lemma pvranges_sound : forall V l, (forall n, 0 <= V n < two64) -> Forall (pfact_ok V) l -> vr_sound V (pvranges l).
Proof.
intros V l HV HF. split; [exact HV|]. induction HF as [|f r Hf HF IH]; cbn; [constructor|].
destruct f; try exact IH. constructor; [exact Hf| exact IH].
Qed.
Definition range_clear (S : list (Z * Z)) (VR : vranges) (bn : zexp * zexp) : bool :=
match zbnd VR (fst bn), zbnd VR (ZAdd (fst bn) (snd bn)) with
| Some (lo, _), Some (_, hi) => forallb (fun s => (hi <=? fst s) || (snd s <=? lo)) S
| _, _ => false
end.
Lemma range_clear_sound : forall V VR S bn a, vr_sound V VR -> range_clear S VR bn = true ->
(exists s, In s S /\ fst s <= a < snd s) -> ~ (zv V (fst bn) <= a < zv V (fst bn) + zv V (snd bn)).
Proof.
intros V VR S bn a HV HC (s & Hs & Ha) Hin. unfold range_clear in HC.
destruct (zbnd VR (fst bn)) as [[lo hi]|] eqn:Eb; [|discriminate].
destruct (zbnd VR (ZAdd (fst bn) (snd bn))) as [[lo2 hi2]|] eqn:Eb2; [|discriminate].
pose proof (zbnd_sound V VR (fst bn) lo hi HV Eb) as Hb.
pose proof (zbnd_sound V VR (ZAdd (fst bn) (snd bn)) lo2 hi2 HV Eb2) as Hb2. cbn [zv] in Hb2.
pose proof (proj1 (forallb_forall _ _) HC s Hs) as X. cbn in X. apply orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.
Lemma Forall2_In_l : forall {A B} (R : A -> B -> Prop) l1 l2 x,
Forall2 R l1 l2 -> In x l1 -> exists y, In y l2 /\ R x y.
Proof.
intros A B R l1 l2 x H. induction H as [|a b l1 l2 Hab H IH]; intros Hin; [destruct Hin|].
destruct Hin as [<-|Hin]; [exists b; split; [left; reflexivity| exact Hab]|].
destruct (IH Hin) as (y & Hy & HR). exists y. split; [right; exact Hy| exact HR].
Qed.
Lemma ledger_den_In : forall V l maps b n k,
ledger_den V l maps -> In (LMap b n k) l -> In (wa (zv V b), wa n) maps.
Proof.
intros V l. induction l as [|e l IH]; intros maps b n k HD Hin; [destruct Hin|].
destruct Hin as [->|Hin]; cbn in HD.
- destruct HD as (maps' & -> & _). left. reflexivity.
- destruct e as [b' n' k'|n'].
+ destruct HD as (maps' & -> & HD'). right. eapply IH; eauto.
+ destruct HD as [HD' | (iv & maps' & -> & _ & HD')]; [eapply IH; eauto| right; eapply IH; eauto].
Qed.
