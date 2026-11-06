(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Agree.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Globals.
Import ListNotations.
Open Scope Z_scope.

Definition SHADOW_OFF : Z := 0x7fff8000.
Definition A0_GOT_SHADOW : Z := 0xaa0d0.
Definition A0_SHADOW_CELL : Z := 0xb38f8.
Definition A0_GOT_UAR : Z := 0xaa128.
Definition A0_UAR_CELL : Z := 0xb3900.

Definition sh (A : Z) : Z := A / 8 + SHADOW_OFF.

Definition app_mem (A n : Z) : Prop := (0 <= A /\ A + n <= 0x7fff8000) \/ (0x10007fff8000 <= A /\ A + n <= 2^47).

Definition shadow_cells (ks : list Z) : list cell := map (fun k => C1 (Z_to_bv 8 k)) ks.
Definition shadow_zero_cells (n : nat) : list cell := shadow_cells (repeat 0 n).

Lemma shadow_cells_app : forall a b, shadow_cells (a ++ b) = shadow_cells a ++ shadow_cells b.
Proof. intros; unfold shadow_cells; apply map_app. Qed.
Lemma cells_size_shadow : forall ks, cells_size (shadow_cells ks) = length ks.
Proof. induction ks; cbn; auto. Qed.
Lemma cell_at_shadow : forall ks i, (i < length ks)%nat -> cell_at (shadow_cells ks) i = Some (C1 (Z_to_bv 8 (nth i ks 0))).
Proof.
  induction ks as [|k ks IH]; intros i Hi; cbn in *. lia.
  destruct i; cbn. reflexivity. rewrite Nat.sub_0_r. rewrite IH by lia. reflexivity.
Qed.

Section WithSegs.
Variable segs : list Segment.
Definition asan_globals (m : word -> option byte) : Prop :=
  rw_cells segs m A0_GOT_SHADOW [C8 (Z_to_bv 64 A0_SHADOW_CELL)] /\ rw_cells segs m A0_SHADOW_CELL [C8 (Z_to_bv 64 SHADOW_OFF)]
  /\ rw_cells segs m A0_GOT_UAR [C8 (Z_to_bv 64 A0_UAR_CELL)] /\ rw_cells segs m A0_UAR_CELL [C4 (Z_to_bv 64 1)].

Definition desc_cells1 (d : Z * Z * Z * Z * Z * Z * Z * Z) : list cell :=
  match d with (b, sz, srz, nm, md, dy, loc, odr) =>
    [C8 (Z_to_bv 64 b); C8 (Z_to_bv 64 sz); C8 (Z_to_bv 64 srz); C8 (Z_to_bv 64 nm); C8 (Z_to_bv 64 md); C8 (Z_to_bv 64 dy); C8 (Z_to_bv 64 loc); C8 (Z_to_bv 64 odr)] end.
Definition desc_cells (ds : list (Z * Z * Z * Z * Z * Z * Z * Z)) : list cell := flat_map desc_cells1 ds.
Definition dtor_cells (m : word -> option byte) : Prop :=
  (exists fw, rw_cells segs m 721472 [C8 fw]) /\ (exists b0 b1 b2, rw_cells segs m 6184864 [C1 b0; C1 b1; C1 b2])
  /\ rw_cells segs m 0xaad58 [C8 (Z_to_bv 64 0xaedc0); C8 (Z_to_bv 64 0xb0240)]
  /\ rw_cells segs m 0xaa0b0 [C8 (Z_to_bv 64 0x1433a0)]
  /\ rw_cells segs m 0x1454a0 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ rw_cells segs m 0xb315c [C1 (Z_to_bv 8 1)]
  /\ rw_cells segs m 0xb11b0 [C8 (Z_to_bv 64 0)]
  /\ rw_cells segs m 0xaedc0 (desc_cells A0_DESCS).

Definition env_layout (m : word -> option byte) : Prop :=
  rw_cells segs m 0xaa0d8 [C8 (Z_to_bv 64 0xb45e8); C8 (Z_to_bv 64 0xb45f0); C8 (Z_to_bv 64 0xb45e0)]
  /\ rw_cells segs m 0xb45e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition env_shadow (m : word -> option byte) : Prop :=
  rw_cells segs m 0xaa0d0 [C8 (Z_to_bv 64 0xb38f8)] /\ rw_cells segs m 0xb38f8 [C8 (Z_to_bv 64 0x7fff8000)].

Definition env_inited (m : word -> option byte) : Prop := rw_cells segs m 0xb45d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
Definition env_ric (m : word -> option byte) : Prop := rw_cells segs m 0xaac38 [C8 (Z_to_bv 64 0xb45d9)].

Definition env_real_mem (m : word -> option byte) : Prop := rw_cells segs m 0xabf78 [C8 (Z_to_bv 64 0xa1e18); C8 (Z_to_bv 64 0xa221c)].

Definition env_cf (m : word -> option byte) : Prop := rw_cells segs m 0xaa0c0 [C8 (Z_to_bv 64 0x145428); C8 (Z_to_bv 64 0xb10f8)].

Definition env_flags (m : word -> option byte) : Prop :=
  rw_cells segs m 0x145518 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                           C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition env_real_str (m : word -> option byte) : Prop :=
  rw_cells segs m 0xabde8 [C8 (Z_to_bv 64 0xa2468)] /\ rw_cells segs m 0xabe20 [C8 (Z_to_bv 64 0xa1d1c)]
  /\ rw_cells segs m 0xabf28 [C8 (Z_to_bv 64 0xa27c8)].
Definition env_real_io (m : word -> option byte) : Prop :=
  rw_cells segs m 0xabe30 [C8 (Z_to_bv 64 0xa8a84); C8 (Z_to_bv 64 0x9b0bc)]
  /\ rw_cells segs m 0xabe68 [C8 (Z_to_bv 64 0xa1628); C8 (Z_to_bv 64 0x9b344)].

Definition env_ckpf (m : word -> option byte) : Prop :=
  rw_cells segs m 0x145478 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

Definition env_aflags (m : word -> option byte) : Prop :=
  rw_cells segs m 0xb1110 [C4 (Z_to_bv 64 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].

Definition env_real_lib (m : word -> option byte) : Prop :=
  rw_cells segs m 0xabe08 [C8 (Z_to_bv 64 0xa280c)]
  /\ rw_cells segs m 0xabe58 [C8 (Z_to_bv 64 0xa17ec); C8 (Z_to_bv 64 0x9dd7c)]
  /\ rw_cells segs m 0xabe88 [C8 (Z_to_bv 64 0x999cc)]
  /\ rw_cells segs m 0xabf50 [C8 (Z_to_bv 64 0xa1afc); C8 (Z_to_bv 64 0xa1c64); C8 (Z_to_bv 64 0xa192c)].

Definition env_real_lib2 (m : word -> option byte) : Prop := rw_cells segs m 0xabf48 [C8 (Z_to_bv 64 0xa2690)].

Definition env_got_rms (m : word -> option byte) : Prop := rw_cells segs m 0xaa0f0 [C8 (Z_to_bv 64 0xabf80)].
Definition env_got_rmem (m : word -> option byte) : Prop := rw_cells segs m 0xaa0f8 [C8 (Z_to_bv 64 0xabf78)].

Definition env_real_cmp (m : word -> option byte) : Prop :=
  rw_cells segs m 0xabe10 [C8 (Z_to_bv 64 0xa2314)] /\ rw_cells segs m 0xabe18 [C8 (Z_to_bv 64 0xa1de8)].
Definition icpt_env (m : word -> option byte) : Prop :=
  env_shadow m /\ env_layout m /\ env_inited m /\ env_ric m /\ env_real_mem m
  /\ env_cf m /\ env_flags m /\ env_real_str m /\ env_real_io m
  /\ env_ckpf m /\ env_aflags m /\ env_real_lib m /\ env_real_lib2 m /\ env_got_rms m /\ env_got_rmem m /\ env_real_cmp m.

Definition asan_env (m : word -> option byte) : Prop := asan_globals m /\ dtor_cells m /\ icpt_env m.
#[using="Type"] Lemma asan_env_globals : forall m, asan_env m -> asan_globals m.
Proof. intros m [H _]; exact H. Qed.
#[using="Type"] Lemma asan_env_icpt : forall m, asan_env m -> icpt_env m.
Proof. intros m (_ & _ & H); exact H. Qed.

Definition env_safe (W : list ivl) : Prop :=
  Forall (fun iv => 0x609000 <= fst iv \/ snd iv <= 0x32000
                    \/ (0xaeac8 <= fst iv /\ snd iv <= 0xaed18)
                    \/ (0xb0290 <= fst iv /\ snd iv <= 0xb0291)
                    \/ (0x606fc0 <= fst iv /\ snd iv <= 0x607480)
                    \/ (0x5d5f40 <= fst iv /\ snd iv <= 0x5e5fa0)
                    \/ (0x5e68c8 <= fst iv /\ snd iv <= 0x5e68d0)
                    \/ (0x6069b0 <= fst iv /\ snd iv <= 0x6069b8)
                    \/ (0x6069c0 <= fst iv /\ snd iv <= 0x6069d8)
                    \/ (0x606be0 <= fst iv /\ snd iv <= 0x606be4)
                    \/ (0x606c00 <= fst iv /\ snd iv <= 0x606c08)
                    \/ (0xb0298 <= fst iv /\ snd iv <= 0xb10f8)
                    \/ (0x1857c8 <= fst iv /\ snd iv <= 0x5957f8)
                    \/ (0xb4b00 <= fst iv /\ snd iv <= 0x135b30)
                    \/ (0x143388 <= fst iv /\ snd iv <= 0x14338c)) W.

#[using="Type"] Lemma rw_cells_transport_mo : forall W (m m' : word -> option byte) A cs,
  rw_cells segs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
  - destruct Hw as (Ha & Hn & Hw). split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
    assert (O : outside W (bv_unsigned (wa (A + i)))) by (eapply disjoint_outside; [exact D|]; rewrite wa_unsigned by lia; lia).
    specialize (Hw i Hi). unfold wview in *. rewrite (MU _ O). exact Hw.
Qed.

Definition env_cell_list : list (Z * Z) :=
  [(0xaa0d0, 8); (0xaa128, 8); (0xb0240, 8); (0xb38f8, 8); (0xb3900, 4); (0x5e5fa0, 3);
   (0xaa0c0, 16); (0xaa0d8, 24); (0xaac38, 8); (0xabde8, 8); (0xabe20, 8); (0xabe30, 16); (0xabe68, 16); (0xabf28, 8);
   (0xabf78, 16); (0xb45d8, 2); (0xb45e0, 24); (0x145518, 16);
   (0x145478, 8); (0xb1110, 8); (0xabe08, 8); (0xabe58, 16); (0xabe88, 8); (0xabf50, 24); (0xabf48, 8);
   (0xaa0f0, 8); (0xaa0f8, 8); (0xaad58, 16); (0xaa0b0, 8); (0x1454a0, 8); (0xb315c, 1); (0xb11b0, 8); (0xaedc0, 5248);
   (0xabe10, 8); (0xabe18, 8)].
#[using="Type"] Lemma env_safe_cells : forall W, env_safe W -> forall A n, In (A, n) env_cell_list -> disjoint_from W A n.
Proof.
  intros W SAFE A n HIn. unfold env_safe in SAFE. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SAFE as [|x l S1 S2]; subst. split; [| apply IH; exact S2]. cbn in S1. unfold env_cell_list in HIn.
  repeat (destruct HIn as [E|HIn]; [inversion E; subst; lia|]). destruct HIn.
Qed.

#[using="Type"] Lemma asan_env_frame_m : forall m m' W, asan_env m -> munch W m m' -> env_safe W -> asan_env m'.
Proof.
  intros m m' W ((G1 & G2 & G3 & G4) & H & IE) MU SAFE.
  unfold A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL in *.
  pose proof (env_safe_cells W SAFE) as DJ.
  Ltac asf_cell G MU DJ := eapply rw_cells_transport_mo; [exact G| exact MU| cbn [cells_size csize Nat.add]; apply DJ; vm_compute; repeat first [ left; reflexivity | right ]].
  split; [| split].
  - unfold asan_globals, A0_GOT_SHADOW, A0_SHADOW_CELL, A0_GOT_UAR, A0_UAR_CELL.
    split; [asf_cell G1 MU DJ|]. split; [asf_cell G2 MU DJ|]. split; [asf_cell G3 MU DJ| asf_cell G4 MU DJ].
  - destruct H as ([fw HF] & (b0 & b1 & b2 & HO) & D1 & D2 & D3 & D4 & D5 & D6). split; [| split].
    + exists fw. asf_cell HF MU DJ.
    + exists b0, b1, b2. asf_cell HO MU DJ.
    + split; [asf_cell D1 MU DJ|]. split; [asf_cell D2 MU DJ|]. split; [asf_cell D3 MU DJ|]. split; [asf_cell D4 MU DJ|]. split; [asf_cell D5 MU DJ|].
      eapply rw_cells_transport_mo; [exact D6| exact MU|]. replace (Z.of_nat (cells_size (desc_cells A0_DESCS))) with 5248 by (vm_compute; reflexivity).
      apply DJ. vm_compute. repeat first [ left; reflexivity | right ].
  - destruct IE as ((E1 & E2) & (L1 & L2) & I1 & R1 & M1 & C1 & F1 & (S1 & S2 & S3) & (O1 & O2) & K1 & A1 & (B1 & B2 & B3 & B4) & B5 & B6 & B7 & (B8a & B8b)).
    unfold icpt_env, env_shadow, env_layout, env_inited, env_ric, env_real_mem, env_cf, env_flags, env_real_str, env_real_io, env_ckpf, env_aflags, env_real_lib, env_real_lib2, env_got_rms, env_got_rmem, env_real_cmp in *.
    split; [split; [asf_cell E1 MU DJ| asf_cell E2 MU DJ]|]. split; [split; [asf_cell L1 MU DJ| asf_cell L2 MU DJ]|].
    split; [asf_cell I1 MU DJ|]. split; [asf_cell R1 MU DJ|]. split; [asf_cell M1 MU DJ|]. split; [asf_cell C1 MU DJ|]. split; [asf_cell F1 MU DJ|].
    split; [split; [asf_cell S1 MU DJ| split; [asf_cell S2 MU DJ| asf_cell S3 MU DJ]]|]. split; [split; [asf_cell O1 MU DJ| asf_cell O2 MU DJ]|].
    split; [asf_cell K1 MU DJ|]. split; [asf_cell A1 MU DJ|].
    split; [split; [asf_cell B1 MU DJ|]; split; [asf_cell B2 MU DJ|]; split; [asf_cell B3 MU DJ| asf_cell B4 MU DJ]|]. split; [asf_cell B5 MU DJ|]. split; [asf_cell B6 MU DJ|]. split; [asf_cell B7 MU DJ|]. split; [asf_cell B8a MU DJ| asf_cell B8b MU DJ].
Qed.
#[using="Type"] Lemma asan_env_frame : forall m m' W, asan_env m -> munch W m m' -> wmono segs m m' -> env_safe W -> asan_env m'.
Proof. intros m m' W AE MU _ SAFE. exact (asan_env_frame_m m m' W AE MU SAFE). Qed.

#[using="Type"] Lemma shadow_read : forall (m : word -> option byte) A ks i a,
  rw_cells segs m (sh A) (shadow_cells ks) -> (i < length ks)%nat ->
  a = wa (sh A + Z.of_nat i) ->
  ov_read_bytes segs m a 1 = Some [Z_to_bv 8 (nth i ks 0)].
Proof.
  intros m A ks i a SH Hi Ha.
  exact (rw_cells_read_at segs m (sh A) (shadow_cells ks) i (C1 (Z_to_bv 8 (nth i ks 0))) 1 a SH (cell_at_shadow ks i Hi) eq_refl Ha).
Qed.
End WithSegs.

Definition gkeep (m m' : word -> option byte) (x : word) : Prop :=
  m' x = m x \/ (m x = None /\ seg_rom asegs x = None /\ ro_addr asegs x = false).
Lemma gkeep_refl : forall m x, gkeep m m x.
Proof. intros m x. left. reflexivity. Qed.
Lemma gkeep_of_eq : forall m m' x, m' x = m x -> gkeep m m' x.
Proof. intros m m' x E. left. exact E. Qed.
Lemma gkeep_trans : forall m1 m2 m3 x, gkeep m1 m2 x -> gkeep m2 m3 x -> gkeep m1 m3 x.
Proof.
  intros m1 m2 m3 x [E1|(E0 & R0 & NR)] [E2|(E0' & R0' & NR')].
  - left. rewrite E2. exact E1.
  - right. rewrite <- E1. auto.
  - right. auto.
  - right. auto.
Qed.

Lemma gkeep_mrd : forall m m' x b, gkeep m m' x -> mrd asegs m x = Some b -> mrd asegs m' x = Some b.
Proof. intros m m' x b [E|(E0 & R0 & _)] Hr; unfold mrd in *; [rewrite E; exact Hr| rewrite E0, R0 in Hr; discriminate]. Qed.
Lemma gkeep_mrd_eq : forall m m' x, gkeep m m' x -> mrd asegs m x <> None -> mrd asegs m' x = mrd asegs m x.
Proof. intros m m' x G Hr. destruct (mrd asegs m x) as [b|] eqn:E; [| congruence]. exact (gkeep_mrd m m' x b G E). Qed.
Lemma gkeep_eq : forall m m' x, gkeep m m' x -> mrd asegs m x <> None -> m' x = m x.
Proof. intros m m' x [E|(E0 & R0 & _)] Hr; [exact E|]. unfold mrd in Hr. rewrite E0, R0 in Hr. congruence. Qed.
Lemma gkeep_some : forall m m' x b, gkeep m m' x -> m x = Some b -> m' x = Some b.
Proof. intros m m' x b [E|(E0 & _)] Hm; [rewrite E; exact Hm| congruence]. Qed.

Lemma bytes_at_gkeep : forall m m' A bs, bytes_at asegs m A bs ->
  (forall i, (i < length bs)%nat -> gkeep m m' (wa (A + Z.of_nat i))) -> bytes_at asegs m' A bs.
Proof.
  intros m m' A bs (H0 & H1 & HB) HK. split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (HB i Hi) as Hr. destruct (nth_error bs i) as [b|] eqn:En; [| exfalso; apply nth_error_None in En; lia].
  exact (gkeep_mrd m m' _ b (HK i Hi) Hr).
Qed.

Definition gmunch (W : list (Z * Z)) (m m' : word -> option byte) : Prop :=
  forall x, outside W (bv_unsigned x) -> m' x = m x \/ (m x = None /\ seg_rom asegs x = None /\ ro_addr asegs x = false).
Lemma gmunch_gkeep : forall W m m' x, gmunch W m m' -> outside W (bv_unsigned x) -> gkeep m m' x.
Proof. intros W m m' x G Hx. exact (G x Hx). Qed.
Lemma gmunch_gkeep_at : forall W m m' a, gmunch W m m' -> 0 <= a < 2^64 -> outside W a -> gkeep m m' (wa a).
Proof. intros W m m' a G Ha Hx. apply (G (wa a)). rewrite wa_unsigned by lia. exact Hx. Qed.
Lemma gmunch_of_munch_z : forall W m m', munch W m m' -> gmunch W m m'.
Proof. intros W m m' MU x Hx. left. exact (MU x Hx). Qed.

Definition gagree_on (P : Z -> Prop) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2^64 -> P a -> gkeep m m' (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).
Lemma gagree_on_refl : forall P m, gagree_on P m m.
Proof. intros P m a _ _. split; [apply gkeep_refl| auto]. Qed.
Lemma gagree_on_trans : forall P m1 m2 m3, gagree_on P m1 m2 -> gagree_on P m2 m3 -> gagree_on P m1 m3.
Proof. intros P m1 m2 m3 H1 H2 a Ha HP. destruct (H1 a Ha HP) as [E1 W1]. destruct (H2 a Ha HP) as [E2 W2]. split; [exact (gkeep_trans _ _ _ _ E1 E2)| auto]. Qed.
Lemma gagree_on_mono : forall (P P' : Z -> Prop) m m', gagree_on P m m' -> (forall a, P' a -> P a) -> gagree_on P' m m'.
Proof. intros P P' m m' H HP a Ha Hp. apply H; auto. Qed.
Lemma gagree_on_of_agree : forall P m m', agree_on asegs P m m' -> gagree_on P m m'.
Proof. intros P m m' H a Ha Hp. destruct (H a Ha Hp) as [E Wv]. split; [left; exact E| exact Wv]. Qed.
Lemma gagree_mrd : forall P m m' a b, gagree_on P m m' -> 0 <= a < 2^64 -> P a -> mrd asegs m (wa a) = Some b -> mrd asegs m' (wa a) = Some b.
Proof. intros P m m' a b H Ha Hp Hr. exact (gkeep_mrd m m' (wa a) b (proj1 (H a Ha Hp)) Hr). Qed.
Lemma bytes_at_gagree : forall P m m' A bs,
  gagree_on P m m' -> bytes_at asegs m A bs -> (forall a, A <= a < A + Z.of_nat (length bs) -> P a) -> bytes_at asegs m' A bs.
Proof.
  intros P m m' A bs HP HB HR. pose proof HB as (H0 & H1 & _). apply (bytes_at_gkeep m m' A bs HB). intros i Hi.
  exact (proj1 (HP (A + Z.of_nat i) ltac:(lia) ltac:(apply HR; lia))).
Qed.
Lemma wr_at_gagree : forall P m m' A n, gagree_on P m m' -> wr_at asegs m A n -> (forall a, A <= a < A + n -> P a) -> wr_at asegs m' A n.
Proof.
  intros P m m' A n HP (H0 & H1 & HW) HR. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (HP (A + i) ltac:(lia) ltac:(apply HR; lia)) as [_ Wv]. apply Wv. apply HW. exact Hi.
Qed.
Lemma rw_cells_gagree : forall P m m' A cs,
  gagree_on P m m' -> rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> P a) -> rw_cells asegs m' A cs.
Proof.
  intros P m m' A cs HP [[Hwf HB] HW] HR. split; [split; [exact Hwf|]|].
  - eapply bytes_at_gagree; eauto. rewrite cells_bytes_length by assumption. assumption.
  - eapply wr_at_gagree; eauto.
Qed.
Lemma stk_gagree : forall P m m' lo hi, gagree_on P m m' -> stk asegs m lo hi -> (forall a, lo <= a < hi -> P a) -> stk asegs m' lo hi.
Proof.
  intros P m m' lo hi HP (H1 & H2 & Hs) HR. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (Hs a Ha) as [Hw [b Hb]]. destruct (HP a ltac:(lia) (HR a Ha)) as [G Wv].
  split; [exact (Wv Hw)|]. exists b. exact (gkeep_mrd m m' (wa a) b G Hb).
Qed.
Lemma gagree_on_of_gmunch : forall W m m', gmunch W m m' -> wmono asegs m m' -> gagree_on (fun a => outside W a) m m'.
Proof. intros W m m' G WM a Ha Ho. split; [exact (gmunch_gkeep_at W m m' a G Ha Ho)| intros Hw; apply WM; exact Hw]. Qed.
Lemma gagree_on_of_munch : forall W m m', munch W m m' -> wmono asegs m m' -> gagree_on (fun a => outside W a) m m'.
Proof. intros W m m' MU WM. apply gagree_on_of_gmunch; [apply gmunch_of_munch_z; exact MU| exact WM]. Qed.

Definition acc (m : word -> option byte) (a : Z) : Prop :=
  exists k, bytes_at asegs m (sh a) [Z_to_bv 8 k] /\ (k = 0 \/ (0 < k < 8 /\ a mod 8 < k)).
Definition accessible (m : word -> option byte) (A n : Z) : Prop := forall a, A <= a < A + n -> acc m a.

Definition sh_readable (m : word -> option byte) (A n : Z) : Prop :=
  0 < n -> forall a, sh A - sh A mod 8 <= a < sh (A + n - 1) - sh (A + n - 1) mod 8 + 8 -> exists v, mrd asegs m (wa a) = Some v.

Lemma accessible_sub : forall m A n A' n', accessible m A n -> A <= A' -> A' + n' <= A + n -> accessible m A' n'.
Proof. intros m A n A' n' H H1 H2 a Ha. apply H. lia. Qed.
Lemma sh_readable_sub : forall m A n A' n', sh_readable m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> sh_readable m A' n'.
Proof.
  intros m A n A' n' H H1 H2 H3 Hn a Ha. apply H; [lia|]. unfold sh, SHADOW_OFF in *.
  assert (A / 8 <= A' / 8) by (apply Z.div_le_mono; lia). assert ((A' + n' - 1) / 8 <= (A + n - 1) / 8) by (apply Z.div_le_mono; lia).
  Z.div_mod_to_equations. lia.
Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof.
  intros x Hx.
  assert (D : x = Z.lor (Z.shiftl (Z.shiftr x 5) 5) (x mod 2^5)).
  { rewrite <- Z.ldiff_ones_r by lia. rewrite <- Z.land_ones by lia.
    symmetry. apply Z.lor_ldiff_and. }
  rewrite D at 1. rewrite zb_land_lor_distr_l.
  replace (Z.land (x mod 2^5) 18446744073709551584) with 0.
  2:{ symmetry. change 18446744073709551584 with (576460752303423487 * 2^5).
      rewrite Z.land_comm. apply eq_sym. symmetry.
      apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases n 5) as [LT|GE].
      - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
      - replace (Z.testbit (x mod 2^5) n) with false; [apply Bool.andb_false_r|].
        symmetry. pose proof (Z.mod_pos_bound x (2^5) ltac:(lia)) as B.
        destruct (Z.eq_dec (x mod 2^5) 0) as [E|NZ]; [rewrite E; apply Z.bits_0|].
        apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 5); [|lia]. apply Z.log2_lt_pow2; lia. }
  rewrite Z.lor_0_r.
  change 18446744073709551584 with (Z.shiftl (Z.ones 59) 5).
  rewrite <- Z.shiftl_land. rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (x / 2^5) (2^59)).
  2:{ split. apply Z.div_pos; lia. apply Z.div_lt_upper_bound; lia. }
  change (2^5) with 32. pose proof (Z.div_mod x 32). lia.
Qed.

Lemma shiftr3_div : forall x, Z.shiftr x 3 = x / 8.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Ltac shadow_addr_tac :=
  unfold wa, sh, SHADOW_OFF; f_equal;
  rewrite ?shiftr3_div; rewrite ?unsigned_lit by lia;
  first [ lia | nia ].

Ltac shadow_load shH ii appaddr gg :=
  lazymatch type of shH with rw_cells ?segs ?m ?SA ?cs =>
    let c := eval_cell_at cs ii in
    lazymatch c with Some (C1 ?b) =>
      let H := fresh "SHR" in
      assert (H : ov_read_bytes segs m (Z_to_bv 64 (Z.add (Z.shiftr (bv_unsigned (Z_to_bv 64 appaddr)) 3) gg)) 1 = Some [b]);
      [ apply (rw_cells_read_at segs m SA cs ii (C1 b) 1); [ exact shH | cells_cbv; reflexivity | reflexivity | shadow_addr_tac ]
      | idtac ]
    end
  end.

Ltac shadow_cells_lit H := unfold shadow_zero_cells, shadow_cells in H; cbn [map repeat] in H; unfold sh, SHADOW_OFF in H.

Ltac lit_branch :=
  lazymatch goal with |- evt _ _ (MS _ _ (if ?c then ?a else ?b) _ _ _ _) =>
    first [ replace (if c then a else b) with a by (vm_compute; reflexivity)
          | replace (if c then a else b) with b by (vm_compute; reflexivity) ] end.
Ltac asan_check shH ii appaddr gg := shadow_load shH ii appaddr gg; step; step; lit_branch.
