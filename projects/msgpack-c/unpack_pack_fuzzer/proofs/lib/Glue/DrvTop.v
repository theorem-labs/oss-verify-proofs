(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound OblsLib Ops CtrSys StdioWrite DrvShape DrvRoot DrvLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepS PlanS FXN CertS OL Ops CtrS SW DrvShape DrvRoot DrvLib.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module DrvTop.

Definition splink_holds (args : list word) (model : Model) : Prop :=
  match args with [w] => bv_unsigned w = bv_unsigned (vm_init_sp (m_vmmaps model)) | _ => False end.
Definition SPLINK : opcomp := oc_pure splink_holds.
Definition SPLINK_OPS : list opinst := [OpI 6%uint63 [VP 1%uint63 wzero]].

Definition clear_ops (st : sstate) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (s_facts st) [] (s_priv st) (s_next st).

Lemma clear_ops_sound : forall segs OPS E st ms m,
  (forall o z, In o (s_ops st) -> ~ op_cov1 OPS (op_id o) (map (den E) (op_args o)) z) ->
  st_ok segs OPS E st ms m -> st_ok segs OPS E (clear_ops st) ms m.
Proof.
  intros segs OPS E st ms m NV HS.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub0 Hfacts Hop Hapart0 Hmf Hcov Hminv].
  constructor; cbn [clear_ops s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  all: try solve [constructor].
  intros a Ha. apply (FXN.cov_keep OPS E (s_ops st) [] a); [|exact (Hcov a Ha)].
  intros o Ho [z Hcz]. destruct (NV o z Ho Hcz).
Qed.

Definition no_heap_ops (st : sstate) : bool := forallb (fun o => negb (PrimInt63.eqb (op_id o) 1%uint63)) (s_ops st).

Definition cells_public_b (priv : list (int * int)) (R0 : IMap.t region) : bool :=
  match IMap.find 0%uint63 R0 with
  | None => true
  | Some r => bst_b (rg_cells r) &&
      IMap.forallb (fun g gr => PrimInt63.ltb g (PrimInt63.lsl 1%uint63 58%uint63) &&
         forallb (fun c => PrimInt63.leb (c_idx c) 8%uint63 && PrimInt63.leb (c_w c) 8%uint63 &&
                           negb (in_priv_b priv (PrimInt63.add (PrimInt63.lsl g 3%uint63) (c_idx c)) (c_w c))) (g_cells gr)) (rg_cells r)
  end.

Lemma cells_public_b_sound : forall priv R0, cells_public_b priv R0 = true -> abs_cells_public priv R0.
Proof.
  intros priv R0 H r g gr c Hr Hg Hc i Hi. unfold cells_public_b in H. rewrite Hr in H.
  apply andb_prop in H as [HB H]. apply bst_b_sound in HB.
  pose proof (proj1 (IMap.forallb_spec _ (rg_cells r) HB) H g gr Hg) as Q. cbn beta in Q.
  apply andb_prop in Q as [Qg Q]. apply ltb_spec in Qg.
  pose proof (proj1 (forallb_forall _ _) Q c Hc) as Qc. cbn beta in Qc.
  apply andb_prop in Qc as [Qc Qp]. apply andb_prop in Qc as [Qi Qw]. apply leb_spec in Qi. apply leb_spec in Qw.
  change (to_Z 8%uint63) with 8 in Qi, Qw. apply negb_true_iff in Qp.
  assert (Hl58 : to_Z (PrimInt63.lsl 1%uint63 58%uint63) = 2 ^ 58) by reflexivity. rewrite Hl58 in Qg.
  pose proof (int_range g). pose proof (int_range (c_idx c)). pose proof (int_range (c_w c)).
  assert (Hsh : to_Z (PrimInt63.lsl g 3%uint63) = 8 * to_Z g).
  { rewrite lsl_spec. change (2 ^ to_Z 3%uint63) with 8. rewrite wB_two63, Z.mul_comm. apply Z.mod_small. rewrite two63_eq. lia. }
  assert (Hk : keyZ g = to_Z g).
  { unfold keyZ, Mem.keyZ. destruct (PrimInt63.ltb g bit62i) eqn:C; [reflexivity|]. exfalso.
    assert (C' : PrimInt63.ltb g bit62i = true) by (apply ltb_spec; change (to_Z bit62i) with (2 ^ 62); lia). congruence. }
  assert (Ha : to_Z (PrimInt63.add (PrimInt63.lsl g 3%uint63) (c_idx c)) = 8 * to_Z g + to_Z (c_idx c)).
  { rewrite add_spec, Hsh, wB_two63. apply Z.mod_small. rewrite two63_eq. lia. }
  rewrite Hk. apply (in_priv_b_false priv _ (c_w c) _ Qp); rewrite Ha; [rewrite two63_eq; lia | lia].
Qed.

Section Bridge.
Variables (segs : list Segment) (R : drun).

Definition apart_at (D : sstate) : Prop :=
  forall E, r_PB R (eb E) -> IMap.bst (s_regs D) -> ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E (s_facts D) ->
  ops_apart segs (OPS R) E (s_ops D) (s_regs D) (s_priv D).

Theorem drv_bridge' : forall rm ghi (M D : sstate) E ms model,
  drv_of_main segs rm ghi (s_ops D) (s_priv D) M = Some D ->
  st_ok segs (OPS R) E M ms model -> r_PB R (eb E) -> s_ops M = [] -> (s_resv M = RNone \/ s_resv M = RUnk) ->
  ops_hold (OPS R) E (s_ops D) (ms_mem ms) model -> apart_at D -> abs_cells_public (s_priv D) (s_regs D) ->
  st_ok segs (OPS R) E D ms model.
Proof.
  intros rm ghi M D E ms model H HS HPB Hops0 Hrv Hops Hap Hpub.
  pose proof H as H'. unfold drv_of_main in H.
  destruct (remat segs M rm) as [st1|] eqn:H1; [|discriminate H].
  destruct (prune1 st1 ghi) as [st2|] eqn:H2; [|discriminate H].
  destruct (remat_sound segs R E rm M st1 ms model HS Hops0 Hrv H1) as (HS1 & _).
  destruct (prune1_sound segs R E st1 ghi st2 ms model HS1 H2) as (HS2 & _).
  assert (Hrf : s_regs D = s_regs st2 /\ s_facts D = s_facts st2).
  { unfold with_ops_priv in H. destruct (s_ops st2); [|discriminate H]. destruct (s_priv st2); [|discriminate H]. injection H as <-. split; reflexivity. }
  destruct Hrf as [Hregs Hfacts].
  apply (drv_bridge segs R rm ghi (s_ops D) (s_priv D) M D E ms model H' HS Hops0 Hrv Hops); [| exact Hpub].
  apply Hap; [exact HPB | rewrite Hregs; exact (so_bst _ _ _ _ _ _ HS2) | exact (so_zero _ _ _ _ _ _ HS2) | rewrite Hfacts; exact (so_facts _ _ _ _ _ _ HS2)].
Qed.
End Bridge.

Section Apart.
Variable segs : list Segment.
Variable R : drun.

Variable BL : list (int * Z).
Hypothesis HBL : forall E j c, r_PB R (eb E) -> In (j, c) BL -> bv_unsigned (den E (VBlob false j (VL wzero) 8%uint63)) <= c.

Definition inZ (L : list (Z * Z)) (a : Z) : Prop := Exists (fun iv => fst iv <= a < snd iv) L.

Definition segs_within (IV : list (Z * Z)) (sgs : list Segment) : bool :=
  forallb (fun s => existsb (fun iv => (fst iv <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? snd iv)) IV) sgs.
Lemma segs_within_sound : forall IV sgs a seg, segs_within IV sgs = true -> find_segment sgs a 1 = Some seg -> inZ IV a.
Proof.
  intros IV sgs a seg H Hf. destruct (MemP.find_segment_In sgs a 1 seg Hf) as (Hin & H1 & H2).
  pose proof (proj1 (forallb_forall _ _) H seg Hin) as Q. cbn beta in Q. apply existsb_exists in Q as (iv & Hiv & Q).
  apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. apply Exists_exists. exists iv. split; [exact Hiv| lia].
Qed.

Definition ivs_in_priv (L : list (Z * Z)) (priv : list (int * int)) : bool :=
  forallb (fun iv => existsb (fun p => (to_Z (fst p) <=? fst iv) && (snd iv <=? to_Z (snd p))) priv) L.
Lemma ivs_in_priv_sound : forall L priv a, ivs_in_priv L priv = true -> inZ L a -> in_priv priv a.
Proof.
  intros L priv a H Ha. apply Exists_exists in Ha as (iv & Hiv & Ha).
  pose proof (proj1 (forallb_forall _ _) H iv Hiv) as Q. cbn beta in Q. apply existsb_exists in Q as (p & Hp & Q).
  apply andb_prop in Q as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. unfold in_priv. apply Exists_exists. exists p. split; [exact Hp| lia].
Qed.

Definition ivs_below (L : list (Z * Z)) (b : Z) : bool := forallb (fun iv => snd iv <=? b) L.
Lemma ivs_below_sound : forall L b a, ivs_below L b = true -> inZ L a -> a < b.
Proof.
  intros L b a H Ha. apply Exists_exists in Ha as (iv & Hiv & Ha).
  pose proof (proj1 (forallb_forall _ _) H iv Hiv) as Q. cbn beta in Q. apply Z.leb_le in Q. lia.
Qed.

Fixpoint cover_from (fuel : nat) (lo hi : Z) (L : list (Z * Z)) : bool :=
  match fuel with
  | O => hi <=? lo
  | S f => if hi <=? lo then true else
           match find (fun iv => (fst iv <=? lo) && (lo <? snd iv)) L with
           | Some iv => cover_from f (snd iv) hi L
           | None => false
           end
  end.
Lemma cover_from_sound : forall fuel lo hi L a, cover_from fuel lo hi L = true -> lo <= a < hi -> inZ L a.
Proof.
  induction fuel as [|f IH]; intros lo hi L a H Ha; cbn [cover_from] in H.
  - apply Z.leb_le in H. lia.
  - destruct (Z.leb_spec hi lo); [lia|].
    destruct (find (fun iv => (fst iv <=? lo) && (lo <? snd iv))%bool L) as [iv|] eqn:F; [|discriminate H].
    apply find_some in F as [Hin Hc]. apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1. apply Z.ltb_lt in C2.
    destruct (Z.lt_ge_cases a (snd iv)).
    + apply Exists_exists. exists iv. split; [exact Hin| lia].
    + exact (IH (snd iv) hi L a H ltac:(lia)).
Qed.
Definition covered (IV L : list (Z * Z)) : bool := forallb (fun h => cover_from (S (length L)) (fst h) (snd h) L) IV.
Lemma covered_sound : forall IV L a, covered IV L = true -> inZ IV a -> inZ L a.
Proof.
  intros IV L a H Ha. apply Exists_exists in Ha as (h & Hh & Ha).
  pose proof (proj1 (forallb_forall _ _) H h Hh) as Q. cbn beta in Q. exact (cover_from_sound _ _ _ L a Q Ha).
Qed.
Definition privZ (priv : list (int * int)) : list (Z * Z) := map (fun p => (to_Z (fst p), to_Z (snd p))) priv.
Lemma privZ_in : forall priv a, inZ (privZ priv) a -> in_priv priv a.
Proof.
  intros priv a H. unfold inZ, privZ in H. apply Exists_exists in H as (iv & Hiv & Ha). apply in_map_iff in Hiv as (p & <- & Hp).
  unfold in_priv. apply Exists_exists. exists p. split; [exact Hp| exact Ha].
Qed.
Lemma inZ_app : forall L1 L2 a, inZ (L1 ++ L2) a -> inZ L1 a \/ inZ L2 a.
Proof. intros L1 L2 a H. unfold inZ in H. apply Exists_app in H. exact H. Qed.

Definition WOFF : Z := 8388608.
Definition WLEN : Z := 140737488355328.
Definition HMAX : Z := 4294967296.
Definition SPLO : Z := 8589934592.

Definition ranged (fs : list fact) (k : int) (lo hi : Z) : bool :=
  existsb (fun f => match f with FRange k' l h => PrimInt63.eqb k' k && (lo <=? w2Z l) && (w2Z h <=? hi) | _ => false end%bool) fs.

Definition linked (fs : list fact) (k : int) : bool :=
  match decide_ltu fs (VP k wzero) (VP 1%uint63 wzero) with Some false => true | _ => false end.
Definition hi_bounded (fs : list fact) (h : sv) : bool :=
  match h with
  | VL c => w2Z c <=? HMAX
  | _ => existsb (fun f => match f with FULe a (VL c) => sv_eqb a h && (w2Z c <=? HMAX) | _ => false end%bool) fs
         || match h with
            | VBlob false j (VL o) n => weqb o wzero && PrimInt63.eqb n 8%uint63 && existsb (fun jc => PrimInt63.eqb (fst jc) j && (snd jc <=? HMAX)) BL
            | _ => false end
  end%bool.
Definition based_chk (fs : list fact) (R : IMap.t region) : bool :=
  ranged fs 1%uint63 SPLO WLEN &&
  IMap.forallb (fun k r => PrimInt63.eqb k 0%uint63 ||
     ((if PrimInt63.eqb k 1%uint63 then (- WOFF <=? keyZ (rg_lo r)) else (0 <=? keyZ (rg_lo r)) && linked fs k && ranged fs k 0 WLEN)
      && hi_bounded fs (rg_hi r)))%bool R.

Lemma ranged_sound : forall E fs k lo hi, facts_hold E fs -> ranged fs k lo hi = true -> lo <= bv_unsigned (ev E k) <= hi.
Proof.
  intros E fs k lo hi HF H. unfold ranged in H. apply existsb_exists in H as (f & Hf & H).
  destruct f; try discriminate H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_correct in H1. subst. apply Z.leb_le in H2. apply Z.leb_le in H3.
  pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Q. cbn [fact_holds] in Q. lia.
Qed.
Lemma den_VP_w2Z : forall E k o, bv_unsigned (den E (VP k o)) = (bv_unsigned (ev E k) + w2Z o) mod two64.
Proof. intros E k o. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned. reflexivity. Qed.
Lemma den_VP_zero : forall E k o, weqb o wzero = true -> bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k).
Proof.
  intros E k o H. rewrite den_VP_w2Z. apply weqb_w2Z in H. rewrite H. change (w2Z wzero) with 0. rewrite Z.add_0_r.
  apply Z.mod_small. pose proof (bv_unsigned_in_range _ (ev E k)) as R0. rewrite bv_modulus_64 in R0. exact R0.
Qed.
Lemma linked_sound : forall E fs k, facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 -> linked fs k = true ->
  bv_unsigned (ev E 1%uint63) <= bv_unsigned (ev E k).
Proof.
  intros E fs k HF Hz H. unfold linked in H.
  destruct (decide_ltu fs (VP k wzero) (VP 1%uint63 wzero)) as [[|]|] eqn:D; try discriminate H.
  pose proof (proj1 (ltu_iff _ _ false) (decide_ltu_sound E fs HF _ _ _ D)) as Q. cbn beta iota in Q.
  rewrite <- (den_VP_zero E k wzero (weqb_refl wzero)), <- (den_VP_zero E 1%uint63 wzero (weqb_refl wzero)). exact Q.
Qed.
Lemma hi_bounded_sound : forall E fs h, r_PB R (eb E) -> facts_hold E fs -> hi_bounded fs h = true -> bv_unsigned (den E h) <= HMAX.
Proof.
  intros E fs h HPB HF H.
  assert (GB : forall j o n, weqb o wzero && PrimInt63.eqb n 8%uint63 && existsb (fun jc => PrimInt63.eqb (fst jc) j && (snd jc <=? HMAX)) BL = true ->
               bv_unsigned (den E (VBlob false j (VL o) n)) <= HMAX).
  { intros j o n X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply weqb_eq in X1. apply Uint63.eqb_correct in X2. subst o n.
    apply existsb_exists in X3 as ([j' c] & Hin & X3). cbn [fst snd] in X3. apply andb_prop in X3 as [X4 X5].
    apply Uint63.eqb_correct in X4. apply Z.leb_le in X5. subst j'. pose proof (HBL E j c HPB Hin). lia. }
  assert (G : existsb (fun f => match f with FULe a (VL c) => sv_eqb a h && (w2Z c <=? HMAX) | _ => false end%bool) fs = true ->
              bv_unsigned (den E h) <= HMAX).
  { intros X. apply existsb_exists in X as (f & Hf & X). pose proof (proj1 (Forall_forall _ _) HF _ Hf) as Q.
    destruct f as [| | |a b| | | |]; try discriminate X. destruct b as [c| | | | | | | | | |]; try discriminate X.
    apply andb_prop in X as [X1 X2]. apply sv_eqb_eq in X1. apply Z.leb_le in X2. subst a. cbn [fact_holds] in Q.
    cbn [den] in Q. rewrite wbv_unsigned in Q. lia. }
  destruct h as [c| | | | | | | |sx j o n| |]; cbn [hi_bounded] in H;
    try (apply orb_prop in H; destruct H as [H|H]; [exact (G H) | try discriminate H]).
  - apply Z.leb_le in H. cbn [den]. rewrite wbv_unsigned. exact H.
  - destruct sx; [discriminate H|]. destruct o as [o| | | | | | | | | |]; try discriminate H. exact (GB j o n H).
Qed.

Theorem based_chk_sound : forall fs RG E, r_PB R (eb E) -> IMap.bst RG -> ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> based_chk fs RG = true ->
  SPLO <= bv_unsigned (ev E 1%uint63) <= WLEN /\
  forall a, in_based E RG a -> bv_unsigned (ev E 1%uint63) - WOFF <= a < bv_unsigned (ev E 1%uint63) - WOFF + WLEN.
Proof.
  intros fs RG E HPB HB Hz HF H. unfold based_chk in H. apply andb_prop in H as [Hsp H].
  pose proof (ranged_sound E fs 1%uint63 SPLO WLEN HF Hsp) as SP. split; [exact SP|].
  intros a (k & r & Hk & Kk & Ha). pose proof (proj1 (IMap.forallb_spec _ RG HB) H k r Hk) as Q. cbn beta in Q.
  rewrite Kk in Q. cbn [orb] in Q. apply andb_prop in Q as [Q Qh].
  pose proof (hi_bounded_sound E fs (rg_hi r) HPB HF Qh) as HI. unfold hiZ in Ha.
  destruct (PrimInt63.eqb k 1%uint63) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. apply Z.leb_le in Q. unfold loZ in Ha. unfold SPLO, WLEN, WOFF, HMAX in *. lia.
  - apply andb_prop in Q as [Q Qr]. apply andb_prop in Q as [Ql Qk]. apply Z.leb_le in Ql.
    pose proof (linked_sound E fs k HF Hz Qk) as LK. pose proof (ranged_sound E fs k 0 WLEN HF Qr) as RK.
    unfold loZ in Ha. unfold SPLO, WLEN, WOFF, HMAX in *. lia.
Qed.

Variable WNOFF : w64.
Hypothesis WNOFF_val : w2Z WNOFF = two64 - WOFF.
Definition HARGS : list sv := [VL wzero; VL wzero; VL (W64 false 1%uint63); VP 1%uint63 WNOFF; VL (W64 false 140737488355328%uint63); VL wzero].
Definition wlo (E : env) : Z := bv_unsigned (den E (VP 1%uint63 WNOFF)).
Variables (IMG IMGX PFP : list (Z * Z)).
Hypothesis heap_fp : forall E a, inZ (oc_fp (r_heap R) (map (den E) HARGS)) a -> ~ inZ IMGX a /\ ~ (wlo E <= a < wlo E + WLEN).
Hypothesis pool_fp : forall w a, inZ (oc_fp (r_ext R 7%uint63) [w]) a -> inZ PFP a.

Variable RSv : Z.
Hypothesis RSv_eq : r_RS R = RSv.
Definition RSFP : list (Z * Z) := [(RSv, RSv + 65536)].
Definition apart_chk (D : sstate) : bool :=
  based_chk (s_facts D) (s_regs D) && segs_within IMG segs && covered IMG (IMGX ++ privZ (s_priv D)) &&
  ivs_in_priv (PFP ++ RSFP) (s_priv D) && ivs_below (PFP ++ RSFP) (SPLO - WOFF).

Lemma wlo_val : forall E, SPLO <= bv_unsigned (ev E 1%uint63) <= WLEN -> wlo E = bv_unsigned (ev E 1%uint63) - WOFF.
Proof.
  intros E H. unfold wlo. rewrite den_VP_w2Z, WNOFF_val. unfold SPLO, WLEN, WOFF, two64 in *.
  replace (bv_unsigned (ev E 1%uint63) + (18446744073709551616 - 8388608)) with ((bv_unsigned (ev E 1%uint63) - 8388608) + 1 * 18446744073709551616) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Theorem apart_chk_sound : forall D sel x y,
  s_ops D = [OpI 7%uint63 [sel]; OpI 1%uint63 HARGS; OpI 5%uint63 []; OpI 3%uint63 [x; y]] ->
  apart_chk D = true -> apart_at segs R D.
Proof.
  intros D sel x y HO H E HPB HB Hz HF. unfold apart_chk in H.
  apply andb_prop in H as [H Hbelow]. apply andb_prop in H as [H Hpriv]. apply andb_prop in H as [H Hcov]. apply andb_prop in H as [Hb Hsegs].
  destruct (based_chk_sound _ _ E HPB HB Hz HF Hb) as [SP BASED]. pose proof (wlo_val E SP) as WLO.
  assert (LOW : forall a, inZ (PFP ++ RSFP) a -> ~ in_based E (s_regs D) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv D) a)).
  { intros a Ha. split.
    - intros IB. pose proof (BASED a IB). pose proof (ivs_below_sound _ _ a Hbelow Ha). unfold SPLO, WOFF in *. lia.
    - intros _. exact (ivs_in_priv_sound _ _ a Hpriv Ha). }
  unfold ops_apart. rewrite HO. unfold OPS, CtrSys.OPS.
  repeat apply Forall_cons; try apply Forall_nil; cbn [op_id op_args]; rewrite mk_fp; intros a Ha.
  - rewrite (comp_ext (r_heap R) (FD3 (r_p1 R) (r_file R)) (RSTAGE (r_file R) (r_RS R) (r_RSr R)) FD3DIR FDINIT (r_ext R) 7%uint63) in Ha by reflexivity.
    cbn [map] in Ha. apply LOW. unfold inZ. apply Exists_app. left. exact (pool_fp _ a Ha).
  - rewrite comp_1 in Ha. destruct (heap_fp E a Ha) as [NX NW]. split.
    + intros IB. apply NW. pose proof (BASED a IB). lia.
    + intros [seg Hseg]. pose proof (segs_within_sound IMG segs a seg Hsegs Hseg) as HI.
      destruct (inZ_app _ _ a (covered_sound _ _ a Hcov HI)) as [X|X]; [exfalso; exact (NX X)| exact (privZ_in _ a X)].
  - rewrite comp_5 in Ha. cbn in Ha. inversion Ha.
  - rewrite comp_3 in Ha. apply LOW. unfold inZ. apply Exists_app. right. unfold RSFP. cbn [RSTAGE oc_fp rstage_fp map] in Ha.
    unfold RS_LEN in Ha. rewrite RSv_eq in Ha. exact Ha.
Qed.

Definition id_subst (n : nat) : subst :=
  mk_subst (map (fun i => (Uint63.of_Z (Z.of_nat i), VP (Uint63.of_Z (Z.of_nat i)) wzero)) (seq 0 n)).
Definition drv_chk (rm : list (int * int)) (ghi : int) (M D : sstate) : bool :=
  match drv_of_main segs rm ghi (s_ops D) (s_priv D) (clear_ops M) with
  | Some D' => sstate_wfb D && entails D' D (id_subst (Z.to_nat (to_Z (s_next D)))) &&
               cells_public_b (s_priv D') (s_regs D') && apart_chk D'
               && no_heap_ops M
  | None => false
  end.

Theorem drv_bridgeE : forall rm ghi (M D : sstate) E ms model sel x y,
  s_ops D = [OpI 7%uint63 [sel]; OpI 1%uint63 HARGS; OpI 5%uint63 []; OpI 3%uint63 [x; y]] ->
  drv_chk rm ghi M D = true ->
  st_ok segs (OPS R) E M ms model -> r_PB R (eb E) -> (s_resv M = RNone \/ s_resv M = RUnk) ->
  ops_hold (OPS R) E (s_ops D) (ms_mem ms) model ->
  exists E', eb E' = eb E /\ st_ok segs (OPS R) E' D ms model.
Proof.
  intros rm ghi M0 D E ms model sel x y HO H HS0 HPB Hrv0 Hops. unfold drv_chk in H.
  assert (NV : forall o z, In o (s_ops M0) -> ~ op_cov1 (OPS R) (op_id o) (map (den E) (op_args o)) z).
  { intros o z Ho Hz. pose proof (r_tm_cov1 R _ _ _ Hz) as Hid.
    destruct (drv_of_main segs rm ghi (s_ops D) (s_priv D) (clear_ops M0)); [|discriminate H].
    apply andb_prop in H as [_ Hnh]. unfold no_heap_ops in Hnh.
    pose proof (proj1 (forallb_forall _ _) Hnh o Ho) as X. cbn beta in X. rewrite Hid in X. discriminate X. }
  pose proof (clear_ops_sound segs (OPS R) E M0 ms model NV HS0) as HS. set (M := clear_ops M0) in *.
  assert (Hops0 : s_ops M = []) by reflexivity. assert (Hrv : s_resv M = RNone \/ s_resv M = RUnk) by exact Hrv0.
  clearbody M. clear HS0 Hrv0.
  destruct (drv_of_main segs rm ghi (s_ops D) (s_priv D) M) as [D'|] eqn:HD; [|discriminate H].
  apply andb_prop in H as [H _]. apply andb_prop in H as [H Hap]. apply andb_prop in H as [H Hpub]. apply andb_prop in H as [Hwf Hen].
  assert (E' : s_ops D' = s_ops D /\ s_priv D' = s_priv D).
  { unfold drv_of_main in HD. destruct (remat segs M rm) as [st1|]; [|discriminate HD]. destruct (prune1 st1 ghi) as [st2|]; [|discriminate HD].
    unfold with_ops_priv in HD. destruct (s_ops st2); [|discriminate HD]. destruct (s_priv st2); [|discriminate HD]. injection HD as <-. split; reflexivity. }
  destruct E' as [Eo Ep].
  assert (HS' : st_ok segs (OPS R) E D' ms model).
  { apply (drv_bridge' segs R rm ghi M D' E ms model); try assumption.
    - rewrite Eo, Ep. exact HD.
    - rewrite Eo. exact Hops.
    - apply (apart_chk_sound D' sel x y); [rewrite Eo; exact HO | exact Hap].
    - apply cells_public_b_sound. exact Hpub. }
  exists (subst_env E (id_subst (Z.to_nat (to_Z (s_next D))))). split; [reflexivity|].
  exact (entails_sound segs (OPS R) E D' D _ ms model Hwf Hen HS').
Qed.
End Apart.

Section ImageBytes.
Variable segs : list Segment.

Definition range_untouched (r : region) (lo n : Z) : bool :=
  forallb (fun g => match IMap.find (of_Z g) (rg_cells r) with None => true | Some _ => false end)
          (map (fun i => lo / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1)))).

Definition range_in_image (lo n : Z) : bool :=
  forallb (fun i => match img_byte segs (lo + Z.of_nat i) with Some _ => true | None => false end) (seq 0 (Z.to_nat n)).

Lemma image_bytes : forall OPS E st ms m r lo n,
  st_ok segs OPS E st ms m -> s_priv st = [] -> IMap.find 0%uint63 (s_regs st) = Some r -> rg_bg r = BGImage ->
  0 <= lo -> lo + n < 2 ^ 62 ->
  range_untouched r lo n = true -> range_in_image lo n = true ->
  forall i, 0 <= i < n -> rb segs (ms_mem ms) (lo + i) = img_byte segs (lo + i).
Proof.
  intros OPS E st ms m r lo n HS Hpriv Hr Hbg Hlo Hhi HU HI i Hi.
  pose proof (so_reg _ _ _ _ _ _ HS 0%uint63 r Hr) as RO. pose proof (so_zero _ _ _ _ _ _ HS) as Hz.
  assert (IMG : exists b, img_byte segs (lo + i) = Some b).
  { unfold range_in_image in HI. pose proof (proj1 (forallb_forall _ _) HI (Z.to_nat i) ltac:(apply in_seq; lia)) as Q. cbn beta in Q.
    rewrite Z2Nat.id in Q by lia. destruct (img_byte segs (lo + i)); [eexists; reflexivity | discriminate Q]. }
  destruct IMG as [b Hb].
  pose proof (ro_bg _ _ _ _ _ _ RO (lo + i)) as BG.
  assert (U : uncovered r (lo + i)).
  { intros g gr Hg Hf. exfalso. unfold range_untouched in HU.
    assert (Hgi : In ((lo + i) / 8) (map (fun j => lo / 8 + Z.of_nat j) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1))))).
    { apply in_map_iff. exists (Z.to_nat ((lo + i) / 8 - lo / 8)). split.
      - rewrite Z2Nat.id; [lia|]. apply Z.le_0_sub. apply Z.div_le_mono; lia.
      - apply in_seq. split; [lia|]. assert ((lo + i) / 8 <= (lo + n - 1) / 8) by (apply Z.div_le_mono; lia).
        assert (lo / 8 <= (lo + i) / 8) by (apply Z.div_le_mono; lia). lia. }
    pose proof (proj1 (forallb_forall _ _) HU _ Hgi) as Q. cbn beta in Q.
    assert (Hgk : of_Z ((lo + i) / 8) = g).
    { apply to_Z_inj. rewrite of_Z_spec, wB_two63, Z.mod_small.
      - unfold keyZ, Mem.keyZ in Hg. destruct (PrimInt63.ltb g bit62i) eqn:C; [lia|]. apply Bool.not_true_iff_false in C.
        exfalso. apply C. apply ltb_spec. change (to_Z bit62i) with (2 ^ 62). pose proof (int_range g).
        assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia.
      - rewrite two63_eq. split; [apply Z.div_pos; lia|]. assert ((lo + i) / 8 < 2 ^ 62) by (apply Z.div_lt_upper_bound; lia). lia. }
    rewrite Hgk, Hf in Q. discriminate Q. }
  assert (P2 : 0 <= lo + i < two63 / 2 /\ (exists bs, memory_read segs (Z_to_bv 64 (lo + i)) 1 = Some bs) /\ ~ in_priv (s_priv st) (lo + i)).
  { split; [rewrite two63_eq; change (2 ^ 63 / 2) with (2 ^ 62); lia|]. split.
    - unfold img_byte, rom_of in Hb. destruct (memory_read segs (Z_to_bv 64 (lo + i)) 1) as [bs|]; [eexists; reflexivity | discriminate Hb].
    - rewrite Hpriv. intros X. unfold in_priv in X. apply Exists_exists in X. destruct X as (iv & [] & _). }
  specialize (BG ltac:(intros K; discriminate K) (fun _ => P2) U).
  unfold bg_byte in BG. rewrite Hbg, Hb in BG. rewrite Hz in BG. change (bv_unsigned (Z_to_bv 64 0)) with 0 in BG.
  rewrite Z.add_0_l in BG. rewrite BG, Hb. reflexivity.
Qed.

Definition range_zero (lo n : Z) : bool :=
  forallb (fun i => match img_byte segs (lo + Z.of_nat i) with Some b => Z.eqb (bv_unsigned b) 0 | None => false end) (seq 0 (Z.to_nat n)).
Lemma range_zero_in_image : forall lo n, range_zero lo n = true -> range_in_image lo n = true.
Proof.
  intros lo n H. unfold range_zero, range_in_image in *. apply forallb_forall. intros i Hi.
  pose proof (proj1 (forallb_forall _ _) H i Hi) as Q. cbn beta in Q. destruct (img_byte segs (lo + Z.of_nat i)); [reflexivity | discriminate Q].
Qed.
Lemma image_zeros : forall OPS E st ms m r lo n,
  st_ok segs OPS E st ms m -> s_priv st = [] -> IMap.find 0%uint63 (s_regs st) = Some r -> rg_bg r = BGImage ->
  0 <= lo -> lo + n < 2 ^ 62 ->
  range_untouched r lo n = true -> range_zero lo n = true ->
  forall i, 0 <= i < n -> rb segs (ms_mem ms) (lo + i) = Some (Z_to_bv 8 0).
Proof.
  intros OPS E st ms m r lo n HS Hpriv Hr Hbg Hlo Hhi HU HZ i Hi.
  rewrite (image_bytes OPS E st ms m r lo n HS Hpriv Hr Hbg Hlo Hhi HU (range_zero_in_image lo n HZ) i Hi).
  unfold range_zero in HZ. pose proof (proj1 (forallb_forall _ _) HZ (Z.to_nat i) ltac:(apply in_seq; lia)) as Q. cbn beta in Q.
  rewrite Z2Nat.id in Q by lia. destruct (img_byte segs (lo + i)) as [b|]; [|discriminate Q]. apply Z.eqb_eq in Q.
  f_equal. apply bv_eq. rewrite Q. reflexivity.
Qed.
End ImageBytes.

End DrvTop.
