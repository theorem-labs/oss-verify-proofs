(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

(* [comment removed for export] *)
Class ScfgP : Type := MkScfgP { SCFG : SpuriousCfg }.

Module L5.
Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition u8_at (M : word -> option byte) (a : Z) (b : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 1 = Some [Z_to_bv 8 b].
Definition u64_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 v)).
Definition u32_at (M : word -> option byte) (a : Z) (v : Z) : Prop :=
  rdn segs M (Z_to_bv 64 a) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 v)).
Definition bytes_at (M : word -> option byte) (p : Z) (bs : list Z) : Prop :=
  forall i, (i < length bs)%nat -> u8_at M (p + Z.of_nat i) (nth i bs 0).
Definition limbs_at (M : word -> option byte) (q : Z) (ws : list Z) : Prop :=
  forall i, (i < length ws)%nat -> u64_at M (q + 8 * Z.of_nat i) (nth i ws 0).
(* [comment removed for export] *)
Definition defined (M : word -> option byte) (a n : Z) : Prop :=
  forall i, 0 <= i < n -> M (Z_to_bv 64 (a + i)) <> None.
(* [comment removed for export] *)
Definition writable (M : word -> option byte) (a n : Z) : Prop :=
  forall d (k : nat), 0 <= d -> d + Z.of_nat k <= n -> store_ok segs M (Z_to_bv 64 (a + d)) k = true.
(* [comment removed for export] *)
Definition img_clear (M : word -> option byte) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.
(* [comment removed for export] *)
Definition hull_lo : Z := fold_right Z.min (2 ^ 64) (map (fun s => Z.of_N (seg_base s)) segs).
Definition hull_hi : Z := fold_right Z.max 0 (map (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s)) segs).
Definition hull_apart (a n : Z) : Prop := a + n <= hull_lo \/ hull_hi <= a.
Lemma hull_apart_sub a n a' n' : hull_apart a n -> a <= a' -> a' + n' <= a + n -> hull_apart a' n'.
Proof. unfold hull_apart. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition range : Type := (Z * Z)%type.
Definition in_rng (r : range) (a : Z) : Prop := fst r <= a < fst r + snd r.
Definition outside (F : list range) (a : Z) : Prop := forall r, In r F -> ~ in_rng r a.
Definition frame_but (F : list range) (M M' : word -> option byte) : Prop :=
  forall x : word, outside F (bv_unsigned x) -> M' x = M x.

Lemma frame_but_refl F M : frame_but F M M.
Proof. intros x _. reflexivity. Qed.
Lemma outside_app F G a : outside (F ++ G) a <-> outside F a /\ outside G a.
Proof. unfold outside. split. intros H; split; intros r Hr; apply H; apply in_app_iff; auto. intros [H1 H2] r Hr. apply in_app_iff in Hr. destruct Hr; auto. Qed.
Lemma frame_but_mono F G M M' : (forall a, outside G a -> outside F a) -> frame_but F M M' -> frame_but G M M'.
Proof. intros HFG HF x Hx. apply HF. apply HFG. exact Hx. Qed.
Lemma frame_but_trans F G M M' M'' : frame_but F M M' -> frame_but G M' M'' -> frame_but (F ++ G) M M''.
Proof. intros H1 H2 x Hx. apply outside_app in Hx. destruct Hx as [HxF HxG]. rewrite (H2 x HxG). apply H1. exact HxF. Qed.
Lemma frame_but_weaken F G M M' : incl F G -> frame_but F M M' -> frame_but G M M'.
Proof. intros Hi. apply frame_but_mono. intros a HG r Hr. apply HG. apply Hi. exact Hr. Qed.

Lemma unsigned_lit a : 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros H. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. exact H. Qed.

(* [comment removed for export] *)
Lemma rdn_frame (M M' : word -> option byte) F : frame_but F M M' ->
  forall n a, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> outside F i) ->
  rdn segs M' (Z_to_bv 64 a) n = rdn segs M (Z_to_bv 64 a) n.
Proof.
  intros HF. induction n as [|n IH]; intros a Ha Hn Hout. reflexivity.
  cbn [rdn]. rewrite (HF (Z_to_bv 64 a)). 2: { rewrite unsigned_lit by lia. apply Hout. lia. }
  replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
  2: { apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
       change (bv_unsigned (1%bv : bv 64)) with 1. rewrite <- Zplus_mod_idemp_l. reflexivity. }
  rewrite (IH (a + 1)); [reflexivity | lia | lia | intros i Hi; apply Hout; lia].
Qed.
Lemma u64_at_frame M M' F a v : frame_but F M M' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, a <= i < a + 8 -> outside F i) -> u64_at M a v -> u64_at M' a v.
Proof. intros HF Ha H8 Ho Hu. unfold u64_at. rewrite (rdn_frame M M' F HF 8%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; apply Ho; cbn in Hi; lia. Qed.
Lemma u8_at_frame M M' F a b : frame_but F M M' -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  outside F a -> u8_at M a b -> u8_at M' a b.
Proof. intros HF Ha H1 Ho Hu. unfold u8_at. rewrite (rdn_frame M M' F HF 1%nat a Ha ltac:(cbn; lia)). exact Hu. intros i Hi; cbn in Hi. replace i with a by lia. exact Ho. Qed.
Lemma limbs_at_frame M M' F q ws : frame_but F M M' -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall i, q <= i < q + 8 * Z.of_nat (length ws) -> outside F i) -> limbs_at M q ws -> limbs_at M' q ws.
Proof. intros HF Hq Hh Ho HL i Hi. eapply u64_at_frame. exact HF. lia. lia. intros j Hj; apply Ho; lia. apply HL; exact Hi. Qed.
Lemma defined_grows M M' a n : mem_grows M M' -> defined M a n -> defined M' a n.
Proof. intros G D i Hi. apply G. apply D. exact Hi. Qed.
Lemma writable_grows M M' a n : mem_grows M M' -> writable M a n -> writable M' a n.
Proof. intros G W d k Hd Hk. eapply store_ok_mono. exact G. apply W; assumption. Qed.
Lemma writable_sub M a n a' n' : writable M a n -> a <= a' -> a' + n' <= a + n -> writable M a' n'.
Proof. intros W H1 H2 d k Hd Hk. replace (a' + d) with (a + (a' - a + d)) by lia. apply W; lia. Qed.
Lemma defined_sub M a n a' n' : defined M a n -> a <= a' -> a' + n' <= a + n -> defined M a' n'.
Proof. intros D H1 H2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply D; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma regs_preserved_refl R : regs_preserved R R.
Proof. intros r _; reflexivity. Qed.
Lemma regs_preserved_trans R R' R'' : regs_preserved R R' -> regs_preserved R' R'' -> regs_preserved R R''.
Proof. intros A B r Hr. rewrite (B r Hr). apply A. exact Hr. Qed.
(* [comment removed for export] *)
Definition ra_ok (r : Z) : Prop := 0 <= r < 2 ^ 47 /\ r mod 2 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive bstore : Type := BInl (v0 v1 : Z) | BDyn (cap : Z) (q : Z).
Record bigobj : Type := BO { bo_fb : Z; bo_len : nat; bo_st : bstore }.
Definition bo_dyn (b : bigobj) : bool := Z.testbit (bo_fb b) 0.
Definition bo_neg (b : bigobj) : bool := Z.testbit (bo_fb b) 1.
Definition bo_cap (b : bigobj) : Z := match bo_st b with BInl _ _ => 2 | BDyn c _ => c end.
(* [comment removed for export] *)
Definition bo_data (o : Z) (b : bigobj) : Z := match bo_st b with BInl _ _ => o + 16 | BDyn _ q => q end.

Definition big_at (M : word -> option byte) (o : Z) (b : bigobj) : Prop :=
  u8_at M o (bo_fb b) /\ 0 <= bo_fb b < 256 /\
  u64_at M (o + 8) (Z.of_nat (bo_len b)) /\
  match bo_st b with
  | BInl v0 v1 => Z.testbit (bo_fb b) 0 = false /\ u64_at M (o + 16) v0 /\ u64_at M (o + 24) v1 /\ (bo_len b <= 2)%nat
                  /\ 0 <= v0 < 2 ^ 64 /\ 0 <= v1 < 2 ^ 64
  | BDyn cap q => Z.testbit (bo_fb b) 0 = true /\ u64_at M (o + 16) cap /\ u64_at M (o + 24) q
                  /\ Z.of_nat (bo_len b) <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47
                  /\ hull_apart q (8 * cap)   (* [comment removed for export] *)
  end.
(* [comment removed for export] *)
Definition bo_with_len (b : bigobj) (n : nat) : bigobj := BO (bo_fb b) n (bo_st b).
Definition bo_with_fb (b : bigobj) (fb : Z) : bigobj := BO fb (bo_len b) (bo_st b).

(* [comment removed for export] *)
Lemma fb_dyn_nonneg fb : 0 <= fb < 256 -> fb mod 4 = 1 <-> (Z.testbit fb 0 = true /\ Z.testbit fb 1 = false).
Proof.
  intros Hfb.
  replace (Z.testbit fb 1) with (Z.testbit (fb / 2) 0) by (rewrite (Z.div2_bits fb 0) by lia; reflexivity).
  rewrite !Z.bit0_odd.
  pose proof (Zmod_odd fb) as M1. pose proof (Zmod_odd (fb / 2)) as M2.
  pose proof (Z.div_mod fb 2 ltac:(lia)) as D1. pose proof (Z.div_mod (fb / 2) 2 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound fb 2 ltac:(lia)) as B1. pose proof (Z.mod_pos_bound (fb / 2) 2 ltac:(lia)) as B2.
  assert (E4: fb mod 4 = 2 * ((fb / 2) mod 2) + fb mod 2).
  { symmetry. apply (Zmod_unique fb 4 ((fb / 2) / 2)). lia. lia. }
  rewrite E4. destruct (Z.odd fb), (Z.odd (fb / 2)); split; intros H; try lia; destruct H; try discriminate; lia.
Qed.

(* [comment removed for export] *)
Lemma land253_nonneg fb : 0 <= fb < 256 -> Z.testbit fb 1 = false -> Z.land fb 253 = fb.
Proof.
  intros Hfb B1. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 1) as [->|Hi1]. { rewrite B1. reflexivity. }
  destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
  - replace (Z.testbit 253 i) with true. apply Bool.andb_true_r.
    assert (Hc : i = 0 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
    destruct Hc as [->|[->|[->|[->|[->|[->| ->]]]]]]; reflexivity.
  - assert (Z.testbit fb i = false) as ->.
    { apply Z.testbit_false. lia. rewrite Z.div_small. reflexivity. split. lia.
      apply Z.lt_le_trans with (2 ^ 8). lia. apply Z.pow_le_mono_r; lia. }
    reflexivity.
Qed.

Lemma land_byte_range a m : 0 <= m < 256 -> 0 <= Z.land a m < 256.
Proof.
  intros Hm. replace m with (Z.land m (Z.ones 8)) by (rewrite Z.land_ones, Z.mod_small; lia).
  rewrite Z.land_assoc. rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

(* [comment removed for export] *)
Fixpoint limbs_val (ws : list Z) : Z := match ws with [] => 0 | w :: r => w + 2 ^ 64 * limbs_val r end.

(* [comment removed for export] *)
Definition lstr_short (M : word -> option byte) (o : Z) (s : list Z) : Prop :=
  (length s <= 22)%nat /\ u8_at M o (2 * Z.of_nat (length s)) /\ bytes_at M (o + 1) s /\ u8_at M (o + 1 + Z.of_nat (length s)) 0.
Definition lstr_long (M : word -> option byte) (o : Z) (s : list Z) (w0 p : Z) : Prop :=
  Z.testbit w0 0 = true /\ u64_at M o w0 /\ u64_at M (o + 8) (Z.of_nat (length s)) /\ u64_at M (o + 16) p /\
  bytes_at M p s /\ u8_at M (p + Z.of_nat (length s)) 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Context {SCFG_P : ScfgP}.
Lemma cps_of_msteps (fx fx' : FPState) R pc M R' pc' M' model K :
  m_halted model = None -> m_vm_lazy model = [] ->
  msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) ->
  srealizes segs SCFG (mkCfg (@mkst fx' R' pc' M' (seg_rom segs)) model) K ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof. intros Hh Hl Hms Hk. eapply srz_msteps; eauto. Qed.

(* [comment removed for export] *)
Lemma run_cps (Q : FPState -> bvmap 5 word -> (word -> option byte) -> Prop) (fx : FPState) R pc M pc' model K :
  m_halted model = None -> m_vm_lazy model = [] ->
  (exists (fx' : FPState) R' M', msteps segs (@mkst fx R pc M (seg_rom segs)) (@mkst fx' R' pc' M' (seg_rom segs)) /\ Q fx' R' M') ->
  (forall (fx' : FPState) R' M', Q fx' R' M' -> srealizes segs SCFG (mkCfg (@mkst fx' R' pc' M' (seg_rom segs)) model) K) ->
  srealizes segs SCFG (mkCfg (@mkst fx R pc M (seg_rom segs)) model) K.
Proof. intros Hh Hl (fx' & R' & M' & Hms & HQ) HK. eapply cps_of_msteps; eauto. Qed.

End WithSegs.
End L5.
