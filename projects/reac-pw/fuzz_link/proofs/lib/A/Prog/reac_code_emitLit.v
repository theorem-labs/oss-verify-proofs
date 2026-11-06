(* reac_code_emit on image A: the three .rodata literals of its first line ("%s: %s " at LA_FMT_SS, "reac-pw" at
   LA_S_REACPW, "E_NOT_MARKED" at LA_S_E_NOT_MARKED; reac_code_emit_c.v) at a later state of the walk.

   The contract's Pre gives `acstr_at` and `astr_rt_ok` of each literal at the entry memory. At the fprintf call
   (+0x11c) the walk needs them at the call's memory, after the prologue, frame_alloc_0 and the frame's header.
   - The bytes of a literal and of the rest of its NUL's word are read-only image bytes outside the runtime's statics
     and errno, so `arodata_okP` at both memories gives them the image's value at both (em_lit_keep's key step); the
     walk carries arodata_okP at every cut (reac_code_emitDefs.v em_kept).
   - The shadow of a literal is not kept by akept (a global's shadow is none of akept's classes); at every AR state
     it is zero over the literal's row of the instance's zero-shadow table, and the hull past the row is the
     instance's constant shadow cells (LinkWalkZsh.v zsh_range_find / zsh_hull_find).
   The checks over the image (read-only segment, no static, the shadow rows and cells) are computations at tfibsegs
   (HSEGS) and at the instance's tables (TB).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable LinkSyms LinkList LinkAddr LinkPa PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- the computed checks over the image ---- *)
Definition em_ro_b (lo hi : Z) : bool :=
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    AB1v.tfibsegs.
Definition em_nostatic_b (lo hi : Z) : bool :=
  forallb (fun r : Z * Z => (hi <=? fst r) || (fst r + snd r <=? lo)) Tfib_owned_static.

Lemma em_ro_of_b : forall rlo rhi lo hi a, em_ro_b lo hi = true -> lo <= a < hi -> in_roP AB1v.tfibsegs rlo rhi a.
Proof.
  intros rlo rhi lo hi a H Ha. unfold em_ro_b in H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [Hc H2]. apply andb_true_iff in Hc as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.leb_le in H2.
  left. exists s. split; [exact Hs|]. split; [exact H0 | lia].
Qed.

Lemma em_nostatic_of_b : forall lo hi a, em_nostatic_b lo hi = true -> lo <= a < hi ->
  ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros lo hi a H Ha Hex. unfold em_nostatic_b in H. rewrite forallb_forall in H.
  apply Exists_exists in Hex as (r & Hr & Hin). specialize (H r Hr). unfold in_zr in Hin.
  apply orb_true_iff in H as [H | H]; apply Z.leb_le in H; lia.
Qed.

(* two byte views that agree on the value agree on the byte *)
Lemma em_opt_byte_eq : forall x y : option byte,
  option_map (fun b : byte => bv_unsigned b) x = option_map (fun b : byte => bv_unsigned b) y -> x = y.
Proof.
  intros [x|] [y|] H; cbn [option_map] in H; try discriminate H; [|reflexivity].
  injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
Variables rlo rhi : Z.

(* the rest of the NUL's word: image bytes, which the segments' contents always back *)
Definition em_tail_b (q : Z) : bool :=
  forallb (fun i => match seg_rom AB1v.tfibsegs (Z_to_bv 64 (q + 1 + Z.of_nat i)) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (7 - q mod 8))).

Lemma em_tail_of_b : forall q b, em_tail_b q = true -> q < b < q - q mod 8 + 8 ->
  exists x, seg_rom AB1v.tfibsegs (Z_to_bv 64 b) = Some x.
Proof.
  intros q b H Hb. unfold em_tail_b in H. rewrite forallb_forall in H.
  pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Hm.
  specialize (H (Z.to_nat (b - q - 1)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (q + 1 + (b - q - 1)) with b in H by lia.
  destruct (seg_rom AB1v.tfibsegs (Z_to_bv 64 b)) as [x|]; [exists x; reflexivity | discriminate H].
Qed.

(* the shadow hull of [x, x + n): each of its bytes is a byte of a zero-shadow row or a constant shadow cell of the
   instance (checked by computation) *)
Definition em_zrow_b (s : Z) : bool :=
  existsb (fun r : Z * Z => (SHADOW_OFF + fst r / 8 <=? s) && (s <? SHADOW_OFF + fst r / 8 + snd r / 8)) Tfib_zero_shadow.
Definition em_hull_b (ly : alayout) (x n : Z) : bool :=
  forallb (fun i => em_zrow_b (shadow_addr x / 8 * 8 + Z.of_nat i) || const_byte_b ly (shadow_addr x / 8 * 8 + Z.of_nat i))
    (seq 0 (Z.to_nat (shadow_addr (x + n - 1) / 8 * 8 + 8 - shadow_addr x / 8 * 8))).

Lemma em_hull_vis : forall ly S rd x n, ARm B ly S rd -> em_hull_b ly x n = true -> shadow_hull_vis rd x n.
Proof.
  intros ly S rd x n HM H s Hs. unfold em_hull_b in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (s - shadow_addr x / 8 * 8)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (shadow_addr x / 8 * 8 + (s - shadow_addr x / 8 * 8)) with s in H by lia.
  apply orb_true_iff in H as [H | H].
  - unfold em_zrow_b in H. apply existsb_exists in H as ([lo len] & Hin & Hc).
    apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in H1, H2.
    pose proof (zsh_row_zero B TB ly S rd lo len HM Hin) as HZ. unfold zero_shadow, shadow_of_addr in HZ.
    replace s with (SHADOW_OFF + lo / 8 + (s - (SHADOW_OFF + lo / 8))) by lia.
    rewrite HZ by lia. discriminate.
  - exact (const_byte_vis B TB ly S rd s HM H).
Qed.

(* a constant shadow cell of the instance, by computation *)
Definition em_cval (ly : alayout) (s : Z) : option Z :=
  match cell_lookup (Tfib_const ly) (ANum s) with
  | Some (ACell (ANum a') w (AV (ANum v))) => if (a' =? s) && Nat.ltb 0 w then Some (le_byte v w 0) else None
  | _ => None
  end.

Lemma em_cval_rd : forall ly S rd s v, ARm B ly S rd -> em_cval ly s = Some v -> rd s = Some v.
Proof.
  intros ly S rd s v HM Hb. unfold em_cval in Hb.
  destruct (cell_lookup (Tfib_const ly) (ANum s)) as [[ca w cv]|] eqn:HL; [|discriminate Hb].
  destruct ca; try discriminate Hb. destruct cv as [e|]; [|discriminate Hb].
  destruct e; try discriminate Hb.
  destruct ((z =? s) && Nat.ltb 0 w) eqn:Hc; [|discriminate Hb]. injection Hb as <-.
  apply andb_prop in Hc as [Ha Hw]. apply Z.eqb_eq in Ha. apply Nat.ltb_lt in Hw. subst z.
  pose proof (proj1 (Forall_forall (cell_holds B ly rd) (as_const B ly)) (am_const B ly S rd HM)
    (ACell (ANum s) w (AV (ANum z0))) ltac:(rewrite (ts_const B TB ly); exact (cell_lookup_In _ _ _ HL))) as Hc.
  unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
  specialize (Hc 0%nat Hw). rewrite Z.add_0_r in Hc. exact Hc.
Qed.

(* every byte of [p, p + k) has its shadow in a zero row, or in a constant cell that admits it *)
Definition em_ra_b (ly : alayout) (p k : Z) : bool :=
  forallb (fun i =>
    em_zrow_b (shadow_addr (p + Z.of_nat i)) ||
    match em_cval ly (shadow_addr (p + Z.of_nat i)) with
    | Some v => ((p + Z.of_nat i) mod 8 <? v) && (v <? 8)
    | None => false
    end) (seq 0 (Z.to_nat k)).

Lemma em_ra : forall ly S rd p k, ARm B ly S rd -> em_ra_b ly p k = true -> range_addressable rd SHADOW_OFF p k.
Proof.
  intros ly S rd p k HM H x Hx. unfold em_ra_b in H. rewrite forallb_forall in H.
  specialize (H (Z.to_nat (x - p)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in H by lia. replace (p + (x - p)) with x in H by lia.
  unfold shadow_of_addr. change (SHADOW_OFF + x / 8) with (shadow_addr x).
  apply orb_true_iff in H as [H | H].
  - unfold em_zrow_b in H. apply existsb_exists in H as ([lo len] & Hin & Hc).
    apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. cbn [fst snd] in H1, H2.
    pose proof (zsh_row_zero B TB ly S rd lo len HM Hin) as HZ. unfold zero_shadow, shadow_of_addr in HZ.
    exists 0. split; [|left; reflexivity].
    replace (shadow_addr x) with (SHADOW_OFF + lo / 8 + (shadow_addr x - (SHADOW_OFF + lo / 8))) by lia.
    apply HZ. lia.
  - destruct (em_cval ly (shadow_addr x)) as [v|] eqn:Hv; [|discriminate H].
    apply andb_prop in H as [H1 H2]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2.
    exists v. split; [exact (em_cval_rd ly S rd _ v HM Hv) | right; lia].
Qed.

(* A read-only image C string, outside the statics and errno, with its shadow, at a later AR state. *)
Lemma em_lit_keep : forall (W : world pa_segs) memc ly2 S2 (W2 : world pa_segs) mem2 md2
    (regs : bvmap 5 word) K (p : Z) (s : list byte),
  AR pa_segs B ly2 S2 W2 mem2 md2 ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W2) mem2) ->
  em_ro_b p (p + Z.of_nat (length s) + 1) = true ->
  em_nostatic_b p (p + Z.of_nat (length s) + 1) = true ->
  p + Z.of_nat (length s) + 1 <= TFIB_ERRNO ->
  em_tail_b (p + Z.of_nat (length s)) = true ->
  (forall ly, em_ra_b ly p (Z.of_nat (length s) + 1) = true) ->
  (forall ly, em_hull_b ly p (Z.of_nat (length s) + 1) = true) ->
  acstr_at pa_segs (rdW W memc) p s -> astr_rt_ok pa_segs regs K (rdW W memc) p s ->
  acstr_at pa_segs (rdW W2 mem2) p s /\ astr_rt_ok pa_segs regs K (rdW W2 mem2) p s.
Proof.
  intros W memc ly2 S2 W2 mem2 md2 regs K p s HAR2 HRO1 HRO2 Hro Hst Her Htl Hr Hc
    ((H0 & H64 & Hb) & Hnz) (Hp & Hl & Ham & Hra & Hhull & Htail & Hap).
  set (n := Z.of_nat (length s)) in *.
  assert (KEY : forall a, p <= a < p + n + 1 ->
    aview pa_segs (w_H W2) mem2 a = aview pa_segs (w_H W) memc a).
  { intros a Ha.
    assert (Hro' : in_roP pa_segs rlo rhi a) by (rewrite HSEGS; exact (em_ro_of_b rlo rhi _ _ a Hro Ha)).
    assert (Hst' : ~ Exists (in_zr a) (as_owned_static B))
      by (rewrite (ts_owned B TB); exact (em_nostatic_of_b _ _ a Hst Ha)).
    assert (Her' : ~ (as_errno B <= a < as_errno B + 4)) by (rewrite (ts_errno B TB); lia).
    rewrite (HRO2 a Hro' Hst' Her'), (HRO1 a Hro' Hst' Her'). reflexivity. }
  assert (KEYB : forall a, p <= a < p + n + 1 -> mbyte pa_segs (rdW W2 mem2) a = mbyte pa_segs (rdW W memc) a)
    by (intros a Ha; apply em_opt_byte_eq; exact (KEY a Ha)).
  destruct HAR2 as (HM & _).
  split.
  - split; [|exact Hnz]. split; [exact H0|]. split; [exact H64|].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite KEYB by (subst n; lia). exact (Hb i ltac:(rewrite length_app; cbn [length]; lia)).
  - split; [exact Hp|]. split; [exact Hl|]. split; [exact Ham|].
    split; [exact (em_ra ly2 S2 _ p (n + 1) HM (Hr ly2))|].
    split; [exact (em_hull_vis ly2 S2 _ p (n + 1) HM (Hc ly2))|].
    split; [|exact Hap].
    intros b Hbr. destruct (em_tail_of_b (p + n) b Htl Hbr) as (x & Hx).
    unfold ard, mbyte. destruct (mrestrict (w_H W2) mem2 (Z_to_bv 64 b)); [discriminate|].
    rewrite HSEGS, Hx. discriminate.
Qed.

Definition em_lit_ok (p : Z) (s : list byte) : Prop :=
  em_ro_b p (p + Z.of_nat (length s) + 1) = true /\
  em_nostatic_b p (p + Z.of_nat (length s) + 1) = true /\
  p + Z.of_nat (length s) + 1 <= TFIB_ERRNO /\
  em_tail_b (p + Z.of_nat (length s)) = true /\
  (forall ly, em_ra_b ly p (Z.of_nat (length s) + 1) = true) /\
  (forall ly, em_hull_b ly p (Z.of_nat (length s) + 1) = true).

(* the three literals' checks, by computation *)
Ltac em_lit_checks :=
  unfold em_lit_ok;
  split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|]; split; [vm_compute; congruence|];
  split; [vm_compute; reflexivity|]; split; intros ly; vm_compute; reflexivity.

Lemma em_lit_fmt : em_lit_ok LA_FMT_SS S_FMT_SS.
Proof. em_lit_checks. Qed.
Lemma em_lit_reacpw : em_lit_ok LA_S_REACPW S_REACPW.
Proof. em_lit_checks. Qed.
Lemma em_lit_enm : em_lit_ok LA_S_E_NOT_MARKED S_E_NOT_MARKED.
Proof. em_lit_checks. Qed.

Lemma em_lit_keep_ok : forall (W : world pa_segs) memc ly2 S2 (W2 : world pa_segs) mem2 md2
    (regs : bvmap 5 word) K (p : Z) (s : list byte),
  em_lit_ok p s ->
  AR pa_segs B ly2 S2 W2 mem2 md2 ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W) memc) ->
  arodata_okP pa_segs rlo rhi B (aview pa_segs (w_H W2) mem2) ->
  acstr_at pa_segs (rdW W memc) p s -> astr_rt_ok pa_segs regs K (rdW W memc) p s ->
  acstr_at pa_segs (rdW W2 mem2) p s /\ astr_rt_ok pa_segs regs K (rdW W2 mem2) p s.
Proof.
  intros W memc ly2 S2 W2 mem2 md2 regs K p s (H1 & H2 & H3 & H4 & H5 & H6) HAR2 HRO1 HRO2 Hc Hrt.
  exact (em_lit_keep W memc ly2 S2 W2 mem2 md2 regs K p s HAR2 HRO1 HRO2 H1 H2 H3 H4 H5 H6 Hc Hrt).
Qed.

End a.
