(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec ShapeAlg SpinAlg AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanNodesAux CatExec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow R_sizeclass HandoffKit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_iface D_defs R_cache_defs R_prim_defs R_thread R_m2s R_poison R_setshadow R_leaves R_depot_defs R_fs_defs R_glue_defs R_sec_defs R_tlsgetaddr R_intalloc RT_state RT_rep HandoffImage HandoffCLX RT_frame RT_init RT_init_img RT_init_vis TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Local Instance rim_fx : PropExec.FPState := PropExec.fx0.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.
Lemma u64_lit : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite u_lit64. unfold two64. apply Z.mod_small. exact Hz. Qed.

Definition sa_of (e : expr) (off : Z) : saddr := let '(b, o) := split_lit e in SA b (o + off).

Definition below47 (ch : acs) (e : expr) (off n : Z) : bool :=
  let '(b, o) := split_lit e in
  match base_range (kn ch) b with
  | Some (lo, hi) => (Z.leb 0 (lo + o) && Z.ltb (hi + o) (2 ^ 64) && Z.leb 0 (lo + o + off) && Z.leb (hi + o + off + n) (2 ^ 47))%bool
  | None => false
  end.

Definition sym_wr (ch : acs) (e : expr) (off n : Z) : bool :=
  (below47 ch e off n && Z.leb 0 n && let '(b, o) := split_lit e in kwritable (kn ch) (kn ch) b (o + off) n)%bool.

Definition sym_cells (ch : acs) (e : expr) (off : Z) (cs : list cell) : bool :=
  (cells_wfb cs && sym_wr ch e off (Z.of_nat (cells_size cs))
   && let '(b, o) := split_lit e in
      match kread_bytes bsegs (cells_size cs) (kn ch) b (o + off) with
      | Some zs => blist_eqb (cells_bytes cs) (map (Z_to_bv 8) zs)
      | None => false
      end)%bool.

Definition sym_word (ch : acs) (e : expr) (off : Z) (w : nat) (v : expr) : bool :=
  (Nat.leb w 8 && sym_wr ch e off (Z.of_nat w)
   && match kw_at ch e off w with Some v' => expr_eqb v' v | None => false end)%bool.

Definition sym_zero (ch : acs) (e : expr) (off n : Z) : bool :=
  (sym_wr ch e off n && let '(b, o) := split_lit e in kzero_x (kn ch) (kn ch) b (o + off) (ELit n))%bool.

Section Prim.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation M := (APS.Mr A argH E ch model FULL).

Lemma rim_know : know_ok bsegs E M (kn ch).
Proof. exact (APS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HC). Qed.

Lemma sa_of_start : forall e off, let '(b, o) := split_lit e in 0 <= uE E b + o < 2 ^ 64 -> estart E (sa_of e off) = uE E e + off.
Proof.
  intros e off. unfold sa_of. destruct (split_lit e) as [b o] eqn:Hs. intros Hr.
  pose proof (APS.split_lit_denot E e b o Hs) as D. unfold estart, uE in *. cbn [a_base a_off]. rewrite D.
  rewrite u64_lit by lia. lia.
Qed.

Lemma below47_sound : forall e off n, below47 ch e off n = true ->
  0 <= estart E (sa_of e off) /\ estart E (sa_of e off) + n <= 2 ^ 47 /\ estart E (sa_of e off) = uE E e + off.
Proof.
  intros e off n H. pose proof (sa_of_start e off) as S. unfold below47 in H. unfold sa_of in *.
  destruct (split_lit e) as [b o] eqn:Hs. destruct (base_range (kn ch) b) as [[lo hi]|] eqn:Hb; [|discriminate].
  apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1]. apply andb_prop in H as [H0 H0'].
  apply Z.leb_le in H0. apply Z.ltb_lt in H0'. apply Z.leb_le in H1. apply Z.leb_le in H2.
  destruct (base_range_sound bsegs E M (kn ch) b lo hi rim_know Hb) as [B1 B2].
  unfold estart, uE in *. cbn [a_base a_off] in *. specialize (S ltac:(lia)). lia.
Qed.

Lemma rim_wview : forall a : word, wview bsegs M a <> None -> bv_unsigned a < 2 ^ 47 -> wview bsegs m a <> None.
Proof.
  intros a Hw Hlt. unfold wview in *. destruct (M a) as [bb|] eqn:Hm.
  - rewrite (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA' a ltac:(rewrite Hm; discriminate) Hlt), Hm.
    discriminate.
  - destruct (APS.in_hull A (bv_unsigned a)) eqn:Hin.
    + destruct (hk_hull bsegs A nx0 LIMIT SINV argH FS0 HULL_ok argH_high E ch R FULL model HC A' HA' a Hin) as [E1 E2].
      rewrite E1, <- E2, Hm. exact Hw.
    + rewrite (SEGS_in_hull a Hin) in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma sym_wr_sound : forall e off n, sym_wr ch e off n = true ->
  wr_at bsegs m (uE E e + off) n /\ 0 <= uE E e + off /\ uE E e + off + n <= 2 ^ 47.
Proof.
  intros e off n H. unfold sym_wr in H. apply andb_prop in H as [H Hk]. apply andb_prop in H as [Hb Hn]. apply Z.leb_le in Hn.
  destruct (below47_sound e off n Hb) as (B1 & B2 & B3). rewrite <- B3.
  unfold sa_of in *. destruct (split_lit e) as [b o] eqn:Hs.
  destruct (APSX.kwritable_sound bsegs E M (kn ch) (kn ch) b (o + off) n rim_know rim_know Hk Hn) as (W & _ & _).
  split; [|split; lia]. split; [lia|]. split; [lia|]. intros i Hi.
  pose proof (store_ok_wview bsegs M _ _ (Z.to_nat i) W ltac:(lia)) as Wi.
  rewrite u64_lit in Wi by lia. rewrite Z2Nat.id in Wi by lia.
  apply rim_wview; [exact Wi|]. rewrite wa_unsigned by lia. lia.
Qed.

Lemma sym_cells_sound : forall e off cs, sym_cells ch e off cs = true -> rw_cells bsegs m (uE E e + off) cs.
Proof.
  intros e off cs H. unfold sym_cells in H. apply andb_prop in H as [H Hr]. apply andb_prop in H as [Hwf Hw].
  destruct (sym_wr_sound e off _ Hw) as (W & W1 & W2).
  pose proof (sym_wr_sound e off _ Hw) as _.
  unfold sym_wr in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hb _].
  destruct (below47_sound e off _ Hb) as (B1 & B2 & B3).
  unfold sa_of in B1, B2, B3. destruct (split_lit e) as [b o] eqn:Hs.
  destruct (kread_bytes bsegs (cells_size cs) (kn ch) b (o + off)) as [zs|] eqn:Hk; [|discriminate].
  apply blist_eqb_eq in Hr.
  destruct (APSX.kread_bytes_sound bsegs E M (kn ch) (cells_size cs) b (o + off) zs rim_know Hk B1 ltac:(lia)) as (Hrd & Hlen & _).
  rewrite rdn_AS_Lib in Hrd. apply rdn_bytes_at in Hrd; [| rewrite u64_lit by lia; lia].
  rewrite u64_lit in Hrd by lia. rewrite B3 in Hrd.
  split; [split; [exact (cells_wfb_sound cs Hwf)|]|exact W].
  rewrite Hr. apply (hk_bytes_at bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA');
    [rewrite length_map, Hlen; lia | exact Hrd].
Qed.

Lemma sym_word_sound : forall e off w v, sym_word ch e off w v = true ->
  bytes_at bsegs m (uE E e + off) (word_to_le_bytes w (edenot E v)) /\ wr_at bsegs m (uE E e + off) (Z.of_nat w).
Proof.
  intros e off w v H. unfold sym_word in H. apply andb_prop in H as [H Hv]. apply andb_prop in H as [Hw8 Hw]. apply Nat.leb_le in Hw8.
  destruct (sym_wr_sound e off _ Hw) as (W & W1 & W2). split; [|exact W].
  unfold sym_wr in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hb _].
  destruct (below47_sound e off _ Hb) as (B1 & B2 & B3).
  destruct (kw_at ch e off w) as [v'|] eqn:Hk; [|discriminate]. apply expr_eqb_eq in Hv. subst v'.
  unfold kw_at in Hk. unfold sa_of in B1, B2, B3. destruct (split_lit e) as [b o] eqn:Hs.
  apply kw_find_in in Hk.
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ w v Hk ltac:(lia)) as X.
  rewrite B3 in X. exact X.
Qed.

Lemma sym_zero_sound : forall e off n, sym_zero ch e off n = true ->
  wr_at bsegs m (uE E e + off) n /\ 0 <= uE E e + off /\ uE E e + off + n <= 2 ^ 47
  /\ forall i, 0 <= i < n -> m (Z_to_bv 64 (uE E e + off + i)) = Some (Z_to_bv 8 0).
Proof.
  intros e off n H. unfold sym_zero in H. apply andb_prop in H as [Hw Hz].
  destruct (sym_wr_sound e off _ Hw) as (W & W1 & W2). split; [exact W|]. split; [exact W1|]. split; [exact W2|].
  unfold sym_wr in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hb Hn]. apply Z.leb_le in Hn.
  destruct (below47_sound e off _ Hb) as (B1 & B2 & B3).
  unfold sa_of in B1, B2, B3. destruct (split_lit e) as [b o] eqn:Hs.
  destruct (APSX.kzero_x_sound bsegs E M (kn ch) (kn ch) b (o + off) (ELit n) rim_know rim_know Hz) as (Z1 & _ & _).
  rewrite (APS.elenZ_lit E n) in Z1 by lia. intros i Hi. specialize (Z1 i Hi). rewrite B3 in Z1.
  rewrite (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA'); [exact Z1 | rewrite Z1; discriminate|].
  rewrite u64_lit by lia. lia.
Qed.

Lemma sym_zero_bytes : forall e off n, sym_zero ch e off n = true -> bytes_at bsegs m (uE E e + off) (repeat (Z_to_bv 8 0) (Z.to_nat n)).
Proof.
  intros e off n H. destruct (sym_zero_sound e off n H) as (_ & W1 & W2 & Z).
  assert (Hn : 0 <= n) by (unfold sym_zero, sym_wr in H; repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end;
                           match goal with X : Z.leb 0 n = true |- _ => apply Z.leb_le in X; exact X end).
  split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
  rewrite nth_error_repeat by lia. unfold mrd. unfold wa. rewrite (Z (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

Lemma sym_zero_cells400 : forall e off, sym_zero ch e off 400 = true ->
  rw_cells bsegs m (uE E e + off) [CB 400 (repeat (Z_to_bv 8 0) 400)].
Proof.
  intros e off H. pose proof (sym_zero_bytes e off 400 H) as Hb. destruct (sym_zero_sound e off 400 H) as (W & _ & _ & _).
  split; [split|].
  - cbn [cells_wf cell_wf]. split; [apply repeat_length | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. exact W.
Qed.

Lemma sym_zero_cellsZ15 : forall e off, sym_zero ch e off 120 = true -> rw_cells bsegs m (uE E e + off) Z15.
Proof.
  intros e off H. pose proof (sym_zero_bytes e off 120 H) as Hb. destruct (sym_zero_sound e off 120 H) as (W & _ & _ & _).
  split; [split|].
  - cbn. repeat split.
  - replace (cells_bytes Z15) with (repeat (Z_to_bv 8 0) (Z.to_nat 120)) by (vm_compute; reflexivity). exact Hb.
  - exact W.
Qed.

End Prim.

Definition lit_word (ch : acs) (a : Z) (w : nat) (v : expr) : bool :=
  (Nat.leb w 8 && Z.leb 0 a && Z.leb (a + Z.of_nat w) (2 ^ 47) && seg_rw_ok bsegs a (Z.of_nat w)
   && match kw_at ch (ELit 0) a w with Some v' => expr_eqb v' v | None => false end)%bool.

Lemma rw_cells_of : forall (m : mem) a cs, cells_wf cs -> bytes_at bsegs m a (cells_bytes cs) -> wr_at bsegs m a (Z.of_nat (cells_size cs)) ->
  rw_cells bsegs m a cs.
Proof. intros m a cs Hwf Hb Hw. split; [split; assumption | exact Hw]. Qed.

Section Prim2.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').

Lemma lit_word_sound : forall a w v, lit_word ch a w v = true ->
  bytes_at bsegs m a (word_to_le_bytes w (edenot E v)) /\ wr_at bsegs m a (Z.of_nat w).
Proof.
  intros a w v H. unfold lit_word in H.
  repeat match type of H with (_ && _)%bool = true => apply andb_prop in H as [H ?X] end.
  match goal with X1 : Nat.leb w 8 = true, X2 : Z.leb 0 a = true, X3 : Z.leb (a + _) _ = true, X4 : seg_rw_ok _ _ _ = true,
                  X5 : match kw_at _ _ _ _ with _ => _ end = true |- _ =>
    apply Nat.leb_le in X1; apply Z.leb_le in X2; apply Z.leb_le in X3; rename X4 into Hs; rename X5 into Hk end.
  split; [| exact (proj1 (seg_rw_ok_sound bsegs a _ Hs m))].
  destruct (kw_at ch (ELit 0) a w) as [v'|] eqn:Hf; [|discriminate]. apply expr_eqb_eq in Hk. subst v'.
  unfold kw_at in Hf. cbn [split_lit] in Hf. apply kw_find_in in Hf.
  pose proof (hk_kword bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ w v Hf) as X.
  unfold estart in X. cbn [a_base a_off edenot] in X. rewrite u64_lit in X by lia. rewrite !Z.add_0_l in X.
  exact (X ltac:(lia)).
Qed.

Lemma lit_word8 : forall a v, lit_word ch a 8 v = true -> rw_cells bsegs m a [C8 (edenot E v)].
Proof.
  intros a v H. destruct (lit_word_sound a 8 v H) as [B W]. apply rw_cells_of; [repeat split| |exact W].
  change (cells_bytes [C8 (edenot E v)]) with (le8 (edenot E v) ++ []). rewrite app_nil_r. exact B.
Qed.
Lemma lit_word4 : forall a v, lit_word ch a 4 v = true -> rw_cells bsegs m a [C4 (edenot E v)].
Proof.
  intros a v H. destruct (lit_word_sound a 4 v H) as [B W]. apply rw_cells_of; [repeat split| |exact W].
  change (cells_bytes [C4 (edenot E v)]) with (le4 (edenot E v) ++ []). rewrite app_nil_r. exact B.
Qed.
Lemma sym_word8 : forall e off v, sym_word ch e off 8 v = true -> rw_cells bsegs m (uE E e + off) [C8 (edenot E v)].
Proof.
  intros e off v H. destruct (sym_word_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' e off 8 v H) as [B W].
  apply rw_cells_of; [repeat split| |exact W].
  change (cells_bytes [C8 (edenot E v)]) with (le8 (edenot E v) ++ []). rewrite app_nil_r. exact B.
Qed.

Lemma zw_uE : forall e, Z_to_bv 64 (uE E e) = edenot E e.
Proof. intros e. unfold uE. apply Z_to_bv_bv_unsigned. Qed.

End Prim2.

Lemma wr_at_merge : forall (m : mem) a n1 n2, wr_at bsegs m a n1 -> wr_at bsegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at bsegs m a (n1 + n2).
Proof.
  intros m a n1 n2 (A1 & A2 & W1) (B1 & B2 & W2) H1 H2. split; [lia|]. split; [lia|]. intros i Hi.
  destruct (Z.ltb_spec0 i n1); [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Lemma rw_cells_cons : forall (m : mem) a c cs, rw_cells bsegs m a [c] -> rw_cells bsegs m (a + Z.of_nat (csize c)) cs ->
  rw_cells bsegs m a (c :: cs).
Proof.
  intros m a c cs [[Hw1 Hb1] W1] [[Hw2 Hb2] W2]. cbn [cells_wf cells_bytes cells_size] in *. rewrite app_nil_r in Hb1.
  rewrite Nat.add_0_r in W1. split; [split; [split; [exact (proj1 Hw1) | exact Hw2]|]|].
  - apply bytes_at_app. split; [exact Hb1|]. rewrite cbytes_length by exact (proj1 Hw1). exact Hb2.
  - rewrite Nat2Z.inj_add. apply wr_at_merge; [exact W1 | exact W2 | lia | lia].
Qed.

Lemma edenot_eaddz : forall E e z, edenot E (eaddz e z) = Z_to_bv 64 (uE E e + z).
Proof.
  intros E e z. unfold eaddz. rewrite mkAlu_denot. apply bv_eq. rewrite u_add64. cbn [edenot]. rewrite u_lit64, Z_to_bv_unsigned.
  unfold uE, two64, bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

Definition zw8 (z : Z) : cell := C8 (Z_to_bv 64 z).
Definition zw4 (z : Z) : cell := C4 (Z_to_bv 64 z).
Definition zb1 (z : Z) : cell := C1 (Z_to_bv 8 z).

Definition consts_lit : list (Z * list cell) :=
  [ (i_spacebeg + 8, [zw8 0xffffffff]); (i_premapped, [zb1 0]);
    (0x17fea8, [zw8 0x219420]); (0x17feb8, [zw8 0x21b4a8]); (0x219420, [zw8 4096]); (0x21b538, [zw8 0]); (0x21b5ac, [zb1 0]);
    (g_tsd_key_inited, [zb1 1]); (g_tsd_key, [zw4 0]); (pth_tsd, [zw8 g_pthread_tsd_main]);
    (0x17fec8, [zw8 0x189978; zw8 0x18a668; zw8 0x18a670; zw8 0x18a660]); (0x189978, [zw8 SHB]); (0x18a660, [zw8 kHighMemEnd; zw8 0; zw8 0]);
    (g_got_real_memset, [zw8 g_real_memset]); (g_real_memset, [zw8 musl_memset_entry]);
    (g_can_poison, [zb1 1]); (g_cf_clear_shadow_mmap_threshold, [zw8 0xffffffffffffffff]); (0x18a67c, [zw4 30]);
    (0x187138, [zw8 (2 ^ 40)]); (0x187140, [C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]); (0x20bbe2, [zb1 0]); (0x21b4ca, [zb1 1]);
    (0x17fec0, [zw8 0x187178]); (0x187178 + 44, [zw4 4096]); (0x187178 + 52, [zw4 190]); (0x187178 + 85, [zb1 1]); (0x6be3e8 + 16, [zw4 0]);
    (0x180b28, [zw8 16]); (0x21b440, [zw8 0]); (0x1891dc, [zb1 1]);
    (0x21b448, [zw8 0]); (0x186630, [zw8 0x10000000; zw8 0xE666661; zw8 0x100000]); (0x1871a8, [zw4 0]);

    (0x17ff08, [zw8 1]); (0x21b583, [zb1 1]); (0x21b59c, [zb1 1]); (0x180cb8, [zw8 0x6de428]); (0x6de6a8, [zw8 4096]) ].

Definition consts_ro : list (Z * list cell) :=
  [ (g_GOT_shadow_offset_cell, [zw8 g_shadow_memory_dynamic_address]); (g_shadow_memory_dynamic_address, [zw8 SHB]);
    (g_GOT_detect_uar, [zw8 g_detect_stack_use_after_return]); (g_detect_stack_use_after_return, [zw4 1]);
    (0x21b59d, [zb1 0]); (0x21b5a4, [zb1 1]); (0x17fec0, [zw8 0x187178]); (0x17fef0, [zw8 0x181f38]); (0x181f38, [zw8 0x171db0]);
    (0x187195, [zb1 1]); (0x21b4ca, [zb1 1]); (0x180cb8, [zw8 0x6de428]); (0x180cb8, [zw8 0x6de428]);
    (0x180a30, [zw8 0x18a659]); (0x18a659, [zb1 1]); (0x181f40, [zw8 0x1721b4]); (0x181d78, [zw8 0x171cb4]); (0x181ee8, [zw8 0x1728e4]);
    (0x181d48, [zw8 0x1726a4]); (0x21b5a3, [zb1 1]);
      (0x181ed0, [zw8 0x158680]) ].

Definition hs_consts_ok (ch : acs) : bool :=
  (forallb (fun p => hs_rw_cells ch (fst p) (snd p)) consts_lit && forallb (fun p => hs_cells ch (fst p) (snd p)) consts_ro
   && lit_word ch i_spacebeg 8 (eSB ch) && lit_word ch i_regioninfo 8 (eaddz (eSB ch) (2 ^ 37))
   && lit_word ch g_pthread_tsd_main 8 (eTCX ch) && sym_word ch (eTCX ch) 0x98 8 (eT ch)
   && sym_word ch (eT ch) off_t_stack_top 8 (eTop ch) && sym_word ch (eT ch) (off_t_stack_top + 8) 8 (eaddz (eTop ch) (-0x800000))
   && sym_cells ch (eT ch) off_t_stack_switching [zb1 0] && sym_cells ch (eT ch) 0xc60 [zb1 0]
   && sym_cells ch (eTCX ch) 8 [zw4 0] && sym_zero ch (eT ch) 2768 400
   && sym_word ch (eT ch) 0 8 (eTCX ch)

   && forallb (fun p => hs_rw_cells ch (fst p) (snd p)) io_rw && forallb (fun p => hs_cells ch (fst p) (snd p)) io_ro

   && sym_word ch (eT ch) 72 8 (eFSB ch)

   && hs_rw_cells ch 0x1891c0 [zw8 0x1891c8] && lit_word ch 0x1891c8 8 (eMT ch) && sym_zero ch (eMT ch) 0x24798 120 && sym_zero ch (eMT ch) 0x1b5760 120)%bool.

Ltac in_lit := repeat (first [ left; reflexivity | right ]).

Section Consts.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation L := (lay0 A E ch model).

Lemma lit_cells_in : forall l, forallb (fun p => hs_rw_cells ch (fst p) (snd p)) l = true ->
  forall a cs, In (a, cs) l -> rw_cells bsegs m a cs.
Proof.
  intros l H a cs Hin. apply (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').
  exact (proj1 (forallb_forall _ _) H (a, cs) Hin).
Qed.
Lemma ro_cells_in : forall l, forallb (fun p => hs_cells ch (fst p) (snd p)) l = true ->
  forall a cs, In (a, cs) l -> ro_cells bsegs m a cs.
Proof.
  intros l H a cs Hin. apply (hi_ro_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA').
  exact (proj1 (forallb_forall _ _) H (a, cs) Hin).
Qed.

Lemma rim_consts : hs_consts_ok ch = true -> consts_rep L m.
Proof.
  intros H. unfold hs_consts_ok in H.
  apply andb_prop in H as [H MT4]. apply andb_prop in H as [H MT3]. apply andb_prop in H as [H MT2]. apply andb_prop in H as [H MT1].
  apply andb_prop in H as [H W14]. apply andb_prop in H as [H Wio2]. apply andb_prop in H as [H Wio1].
  apply andb_prop in H as [H W13]. apply andb_prop in H as [H W12]. apply andb_prop in H as [H W11].
  apply andb_prop in H as [H W10]. apply andb_prop in H as [H W9]. apply andb_prop in H as [H W8]. apply andb_prop in H as [H W7]. apply andb_prop in H as [H W6].
  apply andb_prop in H as [H W5]. apply andb_prop in H as [H W4]. apply andb_prop in H as [H W3]. apply andb_prop in H as [Hlit Hro].
  pose proof (lit_cells_in consts_lit Hlit) as LC. pose proof (ro_cells_in consts_ro Hro) as RC.
  pose proof (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as LW.
  pose proof (sym_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as SW.
  unfold consts_rep. cbn [l_SB l_TCX l_T l_top lay0].
  split.
  { unfold inst_cells, RIS_of. split; [|apply LC; in_lit].
    apply rw_cells_cons; [rewrite zw_uE; exact (LW _ _ W3)|]. apply rw_cells_cons; [apply LC; in_lit|].
    cbn [csize]. pose proof (LW _ _ W4) as Yris.
    rewrite edenot_eaddz in Yris. unfold i_spacebeg, i_regioninfo in *. replace (g_instance + 32 + Z.of_nat 8 + Z.of_nat 8) with (g_instance + 48) by lia.
    exact Yris. }
  split.
  { unfold mm_gcells. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold thread_cells, tsd_cells. split; [split; [apply LC; in_lit|]; split; [apply LC; in_lit|]; split; [apply LC; in_lit| rewrite zw_uE; exact (LW _ _ W5)]|].
    rewrite zw_uE. exact (SW _ _ _ W6). }
  split.
  { unfold m2s_cells. split; [apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold ps_cells. split; [apply LC; in_lit|]. split; [unfold m2s_cells; split; [apply LC; in_lit|]; split; apply LC; in_lit|].
    split; [unfold setshadow_cells; split; apply LC; in_lit|]. split; apply LC; in_lit. }
  split.
  { unfold stack_cells. split.
    - apply rw_cells_cons; [rewrite zw_uE; exact (SW _ _ _ W7)|].
      cbn [csize]. pose proof (SW _ _ _ W8) as Y. rewrite edenot_eaddz in Y.
      replace (uE E (eT ch) + off_t_stack_top + Z.of_nat 8) with (uE E (eT ch) + (off_t_stack_top + 8)) by lia. exact Y.
    - exact (sym_cells_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W9). }
  split.
  { unfold client_consts. split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; apply RC; in_lit. }
  unfold icells_rep. cbn [l_T lay0].
  split; [exact (sym_cells_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W10)|].
  split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; [apply RC; in_lit|].
  split; [apply RC; in_lit|]. split; [apply RC; in_lit|]. split; [apply LC; in_lit|]. split; [apply RC; in_lit|].
  repeat (split; [first [apply RC; solve [in_lit] | apply LC; solve [in_lit]]|]).
  split; [exact (sym_cells_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W11)|].
  split.
  { eapply rw_cells_stk; [| exact (sym_zero_cells400 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W12)].
    cbn [cells_size csize Nat.add]. lia. }
  split; [pose proof (SW _ _ _ W13) as Y; rewrite Z.add_0_r in Y; rewrite zw_uE; exact Y|].
  split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
  split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].

  split.
  { split; [exact (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ MT1)|].
    split; [pose proof (LW _ _ MT2) as Y; cbn [l_MT lay0]; rewrite zw_uE; exact Y|].
    cbn [l_MT lay0]. split; [exact (sym_zero_cellsZ15 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ MT3)
                      | exact (sym_zero_cellsZ15 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ MT4)]. }
  split; [apply Forall_forall; intros [a cs] Hin; exact (lit_cells_in io_rw Wio1 a cs Hin)|].
  split; [apply Forall_forall; intros [a cs] Hin; exact (ro_cells_in io_ro Wio2 a cs Hin)|].
  split; [pose proof (SW _ _ _ W14) as Y14; cbn [l_FSB lay0] in Y14 |- *; rewrite zw_uE; exact Y14|].
  apply RC; in_lit.
Qed.

End Consts.

Definition hs_zero_ok (ch : acs) : bool :=
  (sym_zero ch (eSB ch) (2 ^ 37 + 128) (128 * 31)
   && sym_zero ch (eT ch) 0x50 (0xc60 - 0x50)
   && lit_word ch i_sec_chunks 8 (ePAB ch) && hs_rw_cells ch i_sec_nres [zw8 0; zw8 0] && hs_rw_cells ch i_sec_mutex [zb1 0]
   && hs_rw_cells ch (i_sec_mutex + 1) [CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]
   && hs_rw_cells ch i_q_global [zw8 0; zw8 0; zw8 0; zw8 0] && hs_rw_cells ch i_q_cmutex [zb1 0; zb1 0; C2 (Z_to_bv 64 0)]

   && hs_rw_cells ch i_sec_page [zw8 4096] && lit_word ch i_sec_range 8 (ePAB ch)
   && hs_rw_cells ch i_sec_sorted [CB 40 (repeat (Z_to_bv 8 0) 40)] && hs_rw_cells ch i_sec_bylog [CB 512 (repeat (Z_to_bv 8 0) 512)]
   && hs_rw_cells ch i_gstat_alloc [zw8 0; zw8 0] && hs_rw_cells ch 0x17feb0 [zw8 0x181f78] && hs_rw_cells ch 0x181f78 [zw8 sec_name])%bool.

Lemma u64s_zero : forall n, u64s (repeat (Z_to_bv 64 0) n) = repeat (Z_to_bv 8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. replace (8 * S n)%nat with (8 + 8 * n)%nat by lia.
  cbn [repeat u64s]. rewrite IH, repeat_app. reflexivity.
Qed.

Section Zero.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation Σ0 := (sigma0 A E ch model).

Lemma zero_cells : forall e off n o cs, sym_zero ch e off n = true -> cells_wf cs -> 0 <= o -> o + Z.of_nat (cells_size cs) <= n ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) -> rw_cells bsegs m (uE E e + off + o) cs.
Proof.
  intros e off n o cs H Hwf Ho Hle Hz.
  destruct (sym_zero_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' e off n H) as (W & W1 & W2 & Z).
  split; [split; [exact Hwf|]|].
  - rewrite Hz. split; [lia|]. split; [rewrite repeat_length; lia|]. intros i Hi. rewrite repeat_length in Hi.
    rewrite nth_error_repeat by lia. unfold mrd, wa. replace (uE E e + off + o + Z.of_nat i) with (uE E e + off + (o + Z.of_nat i)) by lia.
    rewrite (Z (o + Z.of_nat i) ltac:(lia)). reflexivity.
  - destruct W as (_ & _ & W). split; [lia|]. split; [lia|]. intros i Hi.
    replace (uE E e + off + o + i) with (uE E e + off + (o + i)) by lia. apply W. lia.
Qed.

Lemma zero_cells0 : forall e off n cs, sym_zero ch e off n = true -> cells_wf cs -> Z.of_nat (cells_size cs) <= n ->
  cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs) -> rw_cells bsegs m (uE E e + off) cs.
Proof. intros e off n cs H Hw Hl Hz. rewrite <- (Z.add_0_r (uE E e + off)). apply (zero_cells e off n 0 cs H Hw); lia || exact Hz. Qed.

Lemma rim_zero : hs_zero_ok ch = true ->
  (forall c, 1 <= c <= 31 -> ri_lock m (rinfo (RIS_of (l_SB (lay Σ0))) c) 0
              /\ ri_core m (rinfo (RIS_of (l_SB (lay Σ0))) c) 0 0 0 0
              /\ ri_tail m (rinfo (RIS_of (l_SB (lay Σ0))) c) (Z_to_bv 64 0) (Z_to_bv 8 0) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] 0 0 0 0 0 0)
  /\ cache_rep Σ0 m /\ sec_rep Σ0 m /\ quar_rep Σ0 m.
Proof.
  intros H. unfold hs_zero_ok in H.
  apply andb_prop in H as [H W14]. apply andb_prop in H as [H W13]. apply andb_prop in H as [H W12]. apply andb_prop in H as [H W11].
  apply andb_prop in H as [H W10]. apply andb_prop in H as [H W9]. apply andb_prop in H as [H W8].
  apply andb_prop in H as [H W7]. apply andb_prop in H as [H W6]. apply andb_prop in H as [H W5p]. apply andb_prop in H as [H W5]. apply andb_prop in H as [H W4].
  apply andb_prop in H as [H W3]. apply andb_prop in H as [Zris Zt].
  pose proof (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as LC.
  split.
  { intros c Hc. unfold ri_lock, ri_core, ri_tail, rinfo, RIS_of. cbn [lay sigma0 sigma_init l_SB lay0].
    replace (uE E (eSB ch) + 2 ^ 37 + 128 * c) with (uE E (eSB ch) + (2 ^ 37 + 128) + (128 * (c - 1))) by lia.
    split; [apply (zero_cells _ _ _ _ _ Zris); [repeat split | lia | cbn; lia | reflexivity]|].
    split.
    - replace (uE E (eSB ch) + (2 ^ 37 + 128) + 128 * (c - 1) + 16) with (uE E (eSB ch) + (2 ^ 37 + 128) + (128 * (c - 1) + 16)) by lia.
      apply (zero_cells _ _ _ _ _ Zris); [repeat split | lia | cbn; lia | reflexivity].
    - replace (uE E (eSB ch) + (2 ^ 37 + 128) + 128 * (c - 1) + 64) with (uE E (eSB ch) + (2 ^ 37 + 128) + (128 * (c - 1) + 64)) by lia.
      apply (zero_cells _ _ _ _ _ Zris); [repeat split | lia | cbn; lia | reflexivity]. }
  split.
  { unfold cache_rep. intros c Hc. unfold pclass_rep, pc_cells, pc_addr. cbn [lay sigma0 sigma_init l_T lay0 ca ca_init length].
    split.
    - replace (uE E (eT ch) + 208 + 80 * c) with (uE E (eT ch) + 0x50 + (128 + 80 * c)) by lia.
      apply (zero_cells _ _ _ _ _ Zt); [repeat split | lia | cbn; lia | reflexivity].
    - exists (repeat (Z_to_bv 64 0) 16). split; [|split; reflexivity].
      assert (X : rw_cells bsegs m (uE E (eT ch) + 0x50 + (128 + 80 * c + 16)) [CB 64 (repeat (Z_to_bv 8 0) 64)]).
      { apply (zero_cells _ _ _ _ _ Zt); [cbn; split; [reflexivity | exact I] | lia | cbn; lia | reflexivity]. }
      destruct X as [[_ Xb] Xw]. split.
      + replace (uE E (eT ch) + 208 + 80 * c + 16) with (uE E (eT ch) + 0x50 + (128 + 80 * c + 16)) by lia.
        cbn in Xb |- *. exact Xb.
      + replace (uE E (eT ch) + 208 + 80 * c + 16) with (uE E (eT ch) + 0x50 + (128 + 80 * c + 16)) by lia. exact Xw. }
  split.
  { unfold sec_rep, sec_core. cbn [lay sigma0 sigma_init l_PAB lay0 sec sec_nres length]. split.
    - split; [rewrite zw_uE; exact (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W3)|].
      split; [exact (LC _ _ W4) | exact (LC _ _ W5)].
    - split; [exact (LC _ _ W5p)|]. split.
      + exists []. split; [|split; reflexivity]. pose proof (u64_range (edenot E (ePAB ch))) as Rp. unfold uE. unfold u64arr. cbn [length Z.of_nat].
        split; [change (u64s []) with (@nil byte); apply bytes_at_nil; lia | split; [lia|]; split; [lia|]; intros i Hi; lia].
      + split; [exact (LC _ _ W8)|].
        split; [unfold sec_range; rewrite zw_uE; exact (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W9)|].
        split; [unfold sec_junk; split; [|split] | unfold name_cells; split; [exact (LC _ _ W13) | exact (LC _ _ W14)]].
        * exists (Z_to_bv 8 0), (repeat (Z_to_bv 8 0) 7), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0).
          apply (sec_relist _ _ _ _ (LC _ _ W10)); [repeat split | reflexivity].
        * exists (repeat (Z_to_bv 64 0) 64). split; [reflexivity|]. destruct (LC _ _ W11) as [[_ Hb] Hw]. unfold u64arr.
          rewrite u64s_zero. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb|].
          cbn [cells_size csize] in Hw. exact Hw.
        * exists (Z_to_bv 64 0), (Z_to_bv 64 0). exact (LC _ _ W12). }
  { unfold quar_rep, qcache_rep, qcacheT. cbn [lay sigma0 sigma_init l_T lay0 ql qg length map last fold_right qchain].
    split; [split; [apply (zero_cells0 _ _ _ _ Zt); [repeat split | cbn; lia | reflexivity] | exact I]|].
    split; [split; [exact (LC _ _ W6) | exact I]|]. exact (LC _ _ W7). }
Qed.

End Zero.

Definition E4_lo : Z := 0x2008fff7000.
Definition E4_len : Z := 0xdfff0001000.
Definition is_E4 (mp : amap) : bool :=
  (expr_eqb (am_base mp) (ELit E4_lo) && expr_eqb (am_len mp) (ELit E4_len) && mkind_eqb (am_kind mp) KRWLAZY)%bool.

Definition prim_q (ch : acs) : expr := eaddz (eSB ch) (2 ^ 32).
Definition prim_qlen : Z := 31 * 2 ^ 32.

Definition slice_p (k : list kentry) (p : expr * expr) : bool :=
  (expr_eqb (eadd (fst p) (snd p)) e_band && match xhi_each k (snd p) with Some h => Z.ltb h 4096 | None => false end)%bool.

Definition hs_primsh_ok (A : atable) (ch : acs) : bool :=
  let k := kn ch in
  let '(qb, qk) := split_lit (prim_q ch) in
  let '(sb, sk, sn) := shadow_of A k (prim_q ch) (ELit prim_qlen) in
  (below47 ch (prim_q ch) 0 prim_qlen && existsb is_E4 (a_maps ch)
   && xinside k sb sk sn (ELit 0) E4_lo (ELit E4_len)
   && forallb (fun p => let '(pb, pk) := split_lit (fst p) in

                        ((if flat_x k pb pk (snd p) then true else flat_xe k pb pk (snd p))
                         && (if (if ranges_apart_x k qb qk (ELit prim_qlen) pb pk (snd p) then true
                                 else shadow_apart_each k qb qk (ELit prim_qlen) pb pk (snd p)) then true
                             else slice_p k p)
                         && (if ranges_apart_x k sb sk sn pb pk (snd p) then true else shadow_apart_each k sb sk sn pb pk (snd p)))%bool)
              (a_vis ch))%bool.

Lemma shadow_of_len : forall (A : atable) E M k b n sb sk sn, know_ok bsegs E M k -> shadow_of A k b n = (sb, sk, sn) ->
  elenZ E sn = uE E n / 8.
Proof.
  intros A E M k b n sb sk sn HK H. unfold shadow_of in H.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection H as <- <- <-.
  unfold elenZ. rewrite (mkSrl_denot bsegs E M k n 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
  rewrite u_srl64. rewrite u64_lit by lia. reflexivity.
Qed.

Lemma shadow_of_den : forall (A : atable) E M k b n sb sk sn, know_ok bsegs E M k -> shadow_of A k b n = (sb, sk, sn) ->
  0 <= shadow_off A <= 2 ^ 47 -> 0 <= estart E (SA sb sk) < 2 ^ 64 ->
  estart E (SA sb sk) = shadow_off A + uE E b / 8 /\ elenZ E sn = uE E n / 8.
Proof.
  intros A E M k b n sb sk sn HK H Hoff Hst. unfold shadow_of in H.
  destruct (split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A)))) as [sb' sk'] eqn:Hss. injection H as <- <- <-.
  assert (Usrl : forall e, bv_unsigned (edenot E (mkSrl k e 3)) = uE E e / 8).
  { intros e. rewrite (mkSrl_denot bsegs E M k e 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
    rewrite u_srl64. rewrite u64_lit by lia. reflexivity. }
  split; [|unfold elenZ; apply Usrl].
  pose proof (APS.split_lit_denot E _ sb' sk' Hss) as D. unfold eadd in D. rewrite mkAlu_denot in D. cbn [edenot] in D.
  apply (f_equal bv_unsigned) in D. rewrite u_add64, Usrl, u_lit64 in D. rewrite u64_lit in D by (unfold estart in Hst; cbn [a_base a_off] in Hst; lia).
  pose proof (u64_range (edenot E b)) as Rb. unfold two64 in D. rewrite (Z.mod_small (shadow_off A)) in D by lia.
  assert (Hb8 : 0 <= uE E b / 8 < 2 ^ 61).
  { unfold uE. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite Z.mod_small in D by lia. unfold estart. cbn [a_base a_off]. lia.
Qed.

Section PrimSh.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).

#[local] Notation m := (mH FULL model A').
#[local] Notation M := (APS.Mr A argH E ch model FULL).

Lemma rim_primsh : hs_primsh_ok A ch = true -> uE E (prim_q ch) + prim_qlen + 4096 <= uE E e_band ->
  (forall a : word, shad (uE E (prim_q ch)) <= bv_unsigned a < shad (uE E (prim_q ch) + prim_qlen) -> page_allowedb A' (page_base a) = true) ->
  forall z, shad (uE E (prim_q ch)) <= z < shad (uE E (prim_q ch) + prim_qlen) -> m (Z_to_bv 64 z) = Some (Z_to_bv 8 0).
Proof.
  intros H HQB HAL z Hz. pose proof (rim_know A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as HK.
  unfold hs_primsh_ok in H. destruct (split_lit (prim_q ch)) as [qb qk] eqn:Hq.
  destruct (shadow_of A (kn ch) (prim_q ch) (ELit prim_qlen)) as [[sb sk] sn] eqn:Hsh.
  apply andb_prop in H as [H Hall]. apply andb_prop in H as [H Hins]. apply andb_prop in H as [Hb47 HE4].
  destruct (below47_sound A nx0 LIMIT SINV argH FS0 E ch R FULL model HC _ _ _ Hb47) as (B1 & B2 & B3).
  unfold sa_of in B1, B2, B3. rewrite Hq in B1, B2, B3. rewrite Z.add_0_r in B1, B2, B3.
  pose proof (xinside_sound bsegs E M (kn ch) sb sk sn (ELit 0) E4_lo (ELit E4_len) HK Hins) as [I1 I2].
  unfold estart in I1, I2. cbn [a_base a_off edenot] in I1, I2. rewrite u64_lit in I1, I2 by lia.
  rewrite (APS.elenZ_lit E E4_len) in I2 by (unfold E4_len; lia).
  destruct (shadow_of_den A E M (kn ch) _ _ sb sk sn HK Hsh ltac:(rewrite Hshoff; unfold SHB; lia)
              ltac:(unfold estart; cbn [a_base a_off]; pose proof (u64_range (edenot E sn)); unfold elenZ in I2; unfold E4_lo, E4_len in *; lia))
    as [S1 S2].
  rewrite Hshoff in S1. unfold uE in S2. cbn [edenot] in S2. rewrite u64_lit in S2 by (unfold prim_qlen; lia).
  assert (Hzr : estart E (SA sb sk) <= z < estart E (SA sb sk) + elenZ E sn).
  { rewrite S1, S2. unfold shad, prim_qlen in *. unfold uE in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  unfold estart in Hzr. cbn [a_base a_off] in Hzr. unfold elenZ in Hzr, I2.
  assert (Rz : 0 <= z < 2 ^ 64) by (unfold E4_lo, E4_len in *; lia).
  set (a := Z_to_bv 64 z). assert (Ua : bv_unsigned a = z) by (unfold a; apply u64_lit; exact Rz).

  apply existsb_exists in HE4 as (mp & Hmp & HmpE). unfold is_E4 in HmpE.
  apply andb_prop in HmpE as [HmpE Hkind]. apply andb_prop in HmpE as [Hbase Hlen].
  apply expr_eqb_eq in Hbase. apply expr_eqb_eq in Hlen. apply APS.mkind_eqb_eq in Hkind.
  assert (Zin : bv_unsigned (edenot E (am_base mp)) <= z < bv_unsigned (edenot E (am_base mp)) + bv_unsigned (edenot E (am_len mp))).
  { rewrite Hbase, Hlen. cbn [edenot]. rewrite !u64_lit by (unfold E4_lo, E4_len; lia). unfold E4_lo, E4_len in *. lia. }
  assert (Hnf : is_fog mp = false) by (unfold is_fog, is_tok_kind; rewrite Hkind; reflexivity).
  assert (Hm1 : APS.in_ivs (bv_unsigned a) (vm_maps (m_vmmaps model)) = true).
  { eapply APS.in_ivs_maps_match; [exact (APS.co_maps _ _ _ _ _ _ _ _ _ _ _ _ HC) | exact Hmp | exact Hnf |]. rewrite Ua. exact Zin. }
  destruct (proj1 (Forall_forall _ _) (APS.co_kinds _ _ _ _ _ _ _ _ _ _ _ _ HC) mp Hmp Hkind a ltac:(rewrite Ua; exact Zin)) as [Hna Hlz].
  pose proof (APS.alloc_top_cs _ _ _ _ _ _ _ _ _ _ _ _ HC) as HaC. unfold CEIL, ATOPMAX in HaC.
  assert (Hargh : argH E a = false).
  { destruct (argH E a) eqn:Ha; [|reflexivity]. pose proof (argH_high _ _ Ha) as X. unfold CEIL in X. unfold E4_lo, E4_len in *. lia. }

  assert (Hold : APS.in_allow A E ch (bv_unsigned a) = false).
  { unfold APS.in_allow. apply orb_false_iff.
    assert (P : forall p, In p (a_vis ch) ->
              ((APS.uE E (fst p) <=? bv_unsigned a) && (bv_unsigned a <? APS.uE E (fst p) + APS.uE E (snd p)))%bool = false
              /\ ((APS.sh_lo A E p <=? bv_unsigned a) && (bv_unsigned a <? APS.sh_hi A E p))%bool = false).
    { intros p Hp. pose proof (proj1 (forallb_forall _ _) Hall p Hp) as Hpp. cbv beta in Hpp.
      destruct (split_lit (fst p)) as [pb pk] eqn:Hps.
      apply andb_prop in Hpp as [Hpp Hap2]. apply andb_prop in Hpp as [Hpf Hap1].
      destruct (APS.flat_x_or_e_sound bsegs E _ (kn ch) pb pk (snd p) HK Hpf) as (Fp1 & Fp2 & Fp3).
      pose proof (APS.u_of_split E (fst p) pb pk Hps ltac:(lia)) as Up.
      assert (A1 : estart E (SA qb qk) + elenZ E (ELit prim_qlen) <= estart E (SA pb pk)
                   \/ estart E (SA pb pk) + elenZ E (snd p) <= estart E (SA qb qk)).
      { apply orb_prop in Hap1 as [Hap1|Hslice].
        2:{
          unfold slice_p in Hslice. apply andb_prop in Hslice as [Seq Sxe]. apply expr_eqb_eq in Seq.
          destruct (xhi_each (kn ch) (snd p)) as [h|] eqn:Hxe; [|discriminate]. apply Z.ltb_lt in Sxe.
          pose proof (APS.xhi_each_sound bsegs E _ (kn ch) (snd p) h HK Hxe) as Nh.
          pose proof (u64_range (edenot E (fst p))) as R1. pose proof (u64_range (edenot E (snd p))) as R2.
          assert (Hd : uE E e_band = (uE E (fst p) + uE E (snd p)) mod 2 ^ 64).
          { rewrite <- Seq. unfold eadd, uE. rewrite mkAlu_denot, u_add64. reflexivity. }
          rewrite (APS.elenZ_lit E prim_qlen) by (unfold prim_qlen; lia). unfold estart. cbn [a_base a_off].
          unfold estart in Up, B3. cbn [a_base a_off] in Up, B3. rewrite <- Up.
          pose proof (u64_range (edenot E e_band)) as Rb. unfold uE in *.
          destruct (Z_lt_le_dec (bv_unsigned (edenot E (fst p)) + bv_unsigned (edenot E (snd p))) (2 ^ 64)) as [Lt|Ge].
          - rewrite Z.mod_small in Hd by lia. left. unfold prim_qlen in *. lia.
          - exfalso. rewrite (Z.mod_eq _ (2 ^ 64)) in Hd by lia.
            assert (Q1 : 1 <= (bv_unsigned (edenot E (fst p)) + bv_unsigned (edenot E (snd p))) / 2 ^ 64) by (apply Z.div_le_lower_bound; lia).
            assert (Q2 : (bv_unsigned (edenot E (fst p)) + bv_unsigned (edenot E (snd p))) / 2 ^ 64 < 2) by (apply Z.div_lt_upper_bound; lia).
            assert (Qe : (bv_unsigned (edenot E (fst p)) + bv_unsigned (edenot E (snd p))) / 2 ^ 64 = 1) by lia.
            rewrite Qe in Hd. pose proof (u64_range (edenot E (prim_q ch))). unfold prim_qlen in *. lia. }
        apply orb_prop in Hap1 as [Hap1|Hap1]; [exact (ranges_apart_x_sound bsegs E M (kn ch) _ _ _ _ _ _ HK Hap1)|].
        unfold shadow_apart_each in Hap1. destruct (xhi_each (kn ch) (snd p)) as [h|] eqn:Hxe; [|discriminate].
        apply andb_prop in Hap1 as [Hh Hap1]. apply Z.ltb_lt in Hh.
        pose proof (APS.xhi_each_sound bsegs E _ (kn ch) (snd p) h HK Hxe) as Nh. pose proof (u64_range (edenot E (snd p))) as Rn.
        pose proof (ranges_apart_x_sound bsegs E M (kn ch) _ _ _ _ _ _ HK Hap1) as X.
        rewrite (APS.elenZ_lit E h) in X by (unfold two64 in Hh; lia). unfold elenZ in *. lia. }
      assert (A2 : estart E (SA sb sk) + elenZ E sn <= estart E (SA pb pk) \/ estart E (SA pb pk) + elenZ E (snd p) <= estart E (SA sb sk)).
      { apply orb_prop in Hap2 as [Hap2|Hap2]; [exact (ranges_apart_x_sound bsegs E M (kn ch) _ _ _ _ _ _ HK Hap2)|].
        unfold shadow_apart_each in Hap2. destruct (xhi_each (kn ch) (snd p)) as [h|] eqn:Hxe; [|discriminate].
        apply andb_prop in Hap2 as [Hh Hap2]. apply Z.ltb_lt in Hh.
        pose proof (APS.xhi_each_sound bsegs E _ (kn ch) (snd p) h HK Hxe) as Nh. pose proof (u64_range (edenot E (snd p))) as Rn.
        pose proof (ranges_apart_x_sound bsegs E M (kn ch) _ _ _ _ _ _ HK Hap2) as X.
        rewrite (APS.elenZ_lit E h) in X by (unfold two64 in Hh; lia). unfold elenZ in *. lia. }
      rewrite (APS.elenZ_lit E prim_qlen) in A1 by (unfold prim_qlen; lia).
      unfold estart in A1, A2, Fp1, Fp2, Fp3, B1, B2, B3, Up. cbn [a_base a_off] in A1, A2, Fp1, Fp2, Fp3, B1, B2, B3, Up.
      unfold elenZ in A1, A2. unfold APS.sh_lo, APS.sh_hi, APS.uE. rewrite Hshoff, Up, Ua. rewrite B3 in A1.
      pose proof (u64_range (edenot E (snd p))) as Rn.
      unfold uE in *. unfold prim_qlen, shad, SHB in *.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      split; apply andb_false_iff.
      - destruct A2 as [X|X]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
      - destruct A1 as [X|X]; [left; apply Z.leb_gt | right; apply Z.ltb_ge]; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    unfold APS.in_vis, APS.in_sh. split; apply APS.existsb_false_forall; intros p Hp; [exact (proj1 (P p Hp)) | exact (proj2 (P p Hp))]. }
  assert (Hhid : APS.hid A argH E ch model a = true).
  { unfold APS.hid. rewrite Hargh. cbn [orb]. apply negb_true_iff. unfold APS.vis.
    rewrite Hm1, Hna, Hlz, Hold. cbn [negb orb andb].
    assert (Hih : APS.in_hull A (bv_unsigned a) = false).
    { unfold APS.in_hull. apply andb_false_iff. right. apply Z.ltb_ge. rewrite Hsegtop. unfold SEGTOP_A, E4_lo, E4_len in *. lia. }
    assert (Hat : (alloc_top (m_vmmaps model) <=? bv_unsigned a) = false) by (apply Z.leb_gt; unfold E4_lo, E4_len in *; lia).
    rewrite Hih, Hat. reflexivity. }
  assert (Hsw : APS.in_sw (bv_unsigned a) = true).
  { unfold APS.in_sw. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; unfold SW_LO, KHI, E4_lo, E4_len in *; lia. }
  pose proof (APS.co_zero _ _ _ _ _ _ _ _ _ _ _ _ HC a Hhid Hm1 Hna Hlz (or_intror Hsw)) as Hz0.

  unfold mH, mrestrict, HID. fold a.
  assert (Hpa : page_allowedb A' (page_base a) = true) by (apply HAL; rewrite Ua; exact Hz).
  unfold mkH. rewrite Hpa. cbn [negb andb]. rewrite andb_false_r. cbn [orb].
  replace (2 ^ 47 <=? bv_unsigned a) with false by (symmetry; apply Z.leb_gt; rewrite Ua; unfold E4_lo, E4_len in *; lia).
  exact Hz0.
Qed.

End PrimSh.

Definition eFSBsh (ch : acs) : expr := eaddz (mkSrl (kn ch) (eFSB ch) 3) SHB.
Definition eDTVB (ch : acs) : expr := kwv ch (eDTV ch) 24 8.
Definition eTB (ch : acs) : expr := kwv ch (eT ch) 48 8.
Definition eTE (ch : acs) : expr := kwv ch (eT ch) 56 8.

Definition tga_lit : list (Z * list cell) :=
  [ (0x18a658, [zb1 1]); (g_real_tls_get_addr, [zw8 musl_tls_get_addr_entry]); (g_dtv_ptr, [zw8 g_dtv]); (g_dtv1, [zw8 dtv1_val]);
    (R_tlsgetaddr.g_got_common_flags, [zw8 g_common_flags]); (g_intercept_tls_get_addr, [zb1 1]);
    (g_got_verbosity, [zw8 g_current_verbosity]); (g_current_verbosity, [zw4 0]);
    (g_tls_index, [zw8 1; zw8 0xfffffffffffff800]); (g_got_dtls_off, [zw8 8]) ].

Definition hs_fs_ok (ch : acs) : bool :=
  (sym_cells ch (eFSB ch) 0x58 [zw8 20; zb1 0] && sym_zero ch (eFSB ch) 0 0x58 && sym_zero ch (eFSB ch) 0x1000 0xb08000
   && sym_zero ch (eFSBsh ch) 0x1200 0x160000 && lit_word ch tpA 8 (eFSB ch)
   && forallb (fun p => hs_rw_cells ch (fst p) (snd p)) tga_lit
   && lit_word ch g_tls_dtls 8 (eDTV ch) && sym_word ch (eDTV ch) 24 8 (eDTVB ch) && fact_ok (kn ch) (KRange (eDTVB ch) 1 (2 ^ 64 - 1))
   && sym_word ch (eT ch) 48 8 (eTB ch) && sym_word ch (eT ch) 56 8 (eTE ch) && fact_ok (kn ch) (KAlign (eFSB ch) 8))%bool.

Section FS.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation Σ0 := (sigma0 A E ch model).

Lemma uE_eFSBsh : uE E (eFSB ch) < 2 ^ 48 -> uE E (eFSBsh ch) = shad (uE E (eFSB ch)).
Proof.
  intros Hb. pose proof (rim_know A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as HK.
  unfold eFSBsh. unfold uE at 1. rewrite edenot_eaddz. rewrite u_lit64. unfold two64. unfold uE at 1.
  rewrite (mkSrl_denot bsegs E _ (kn ch) (eFSB ch) 3 (Z_to_bv 64 3) HK) by (rewrite u64_lit by lia; reflexivity).
  unfold shad. rewrite u_srl64, (u64_lit 3) by lia. change (2 ^ (3 mod 64)) with 8. unfold uE in *.
  pose proof (u64_range (edenot E (eFSB ch))) as R0. apply Z.mod_small. unfold SHB.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma zero_u8arr : forall e off n o k, sym_zero ch e off n = true -> 0 <= o -> o + Z.of_nat k <= n ->
  u8arr bsegs m (uE E e + off + o) (repeat (Z_to_bv 8 0) k).
Proof.
  intros e off n o k H Ho Hk.
  destruct (zero_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' e off n o [CB k (repeat (Z_to_bv 8 0) k)] H
              ltac:(cbn; rewrite repeat_length; split; [reflexivity | exact I]) Ho ltac:(cbn; lia) ltac:(cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity)) as [[_ B] W].
  split; [cbn in B; rewrite app_nil_r in B; exact B|]. cbn in W. rewrite repeat_length. rewrite Nat.add_0_r in W. exact W.
Qed.

Lemma rim_fs : hs_fs_ok ch = true -> fs_rep Σ0 m.
Proof.
  intros H. unfold hs_fs_ok in H.
  apply andb_prop in H as [H W11]. apply andb_prop in H as [H W10]. apply andb_prop in H as [H W9]. apply andb_prop in H as [H W8].
  apply andb_prop in H as [H W7]. apply andb_prop in H as [H W6]. apply andb_prop in H as [H W5]. apply andb_prop in H as [H W4].
  apply andb_prop in H as [H W3]. apply andb_prop in H as [H W2]. apply andb_prop in H as [W0 W1].
  pose proof (zero_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as ZC.
  pose proof (sym_zero_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W2) as (_ & F1 & F2 & _).
  assert (HFsh : uE E (eFSBsh ch) = shad (uE E (eFSB ch))) by (apply uE_eFSBsh; lia).
  assert (HF8 : uE E (eFSB ch) mod 8 = 0).
  { pose proof (APS.fact_ok_sound bsegs E _ (kn ch) _ (rim_know A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) W11) as K. cbn [kentry_ok] in K.
    unfold uE. lia. }
  unfold fs_rep. cbn [lay sigma0 sigma_init l_FSB l_DTV l_T lay0 fs0 fsc0 fs4].
  assert (CLS : forall c, c = 5 \/ c = 0 \/ c = 4 \/ c = 1 \/ c = 3 \/ c = 2 -> fs_cls_rep (uE E (eFSB ch)) c (fs0_init c) m).
  { intros c Hc. unfold fs_cls_rep, fs0_init. cbn [fss_hint fss_flags].
    assert (HNF : 0 < NF c <= 2 ^ 14) by (destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]; subst c; unfold NF; cbn; lia).
    split; [|split].
    - unfold fs_hint. replace (uE E (eFSB ch) + 8 * c) with (uE E (eFSB ch) + 0 + 8 * c) by lia.
      apply (ZC _ _ _ _ _ W1); [repeat split | lia | cbn; destruct Hc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; lia | reflexivity].
    - unfold fs_flags, fl_base. rewrite map_repeat. change (b8 0) with (Z_to_bv 8 0).
      replace (uE E (eFSB ch) + 0x1000 + flags_off c) with (uE E (eFSB ch) + 0x1000 + flags_off c) by lia.
      apply (zero_u8arr _ _ _ _ _ W2); [destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]; subst c; cbv [flags_off]; lia
                                        | rewrite Z2Nat.id by lia; destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]; subst c; cbv [flags_off NF]; lia].
    - unfold fs_free_frames. intros p Hp _. split.
      + exists (repeat (Z_to_bv 8 0) (Z.to_nat (fsz c))). unfold frame_addr.
        replace (uE E (eFSB ch) + 0x9000 + c * 2 ^ 20 + p * fsz c) with (uE E (eFSB ch) + 0x1000 + (0x8000 + c * 2 ^ 20 + p * fsz c)) by lia.
        assert (Hfr : 0 <= 0x8000 + c * 2 ^ 20 + p * fsz c /\ 0x8000 + c * 2 ^ 20 + p * fsz c + fsz c <= 0xb08000 /\ 0 < fsz c).
        { destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]; subst c; cbv [fsz NF] in *; lia. }
        apply (ZC _ _ _ _ _ W2); [cbn; rewrite repeat_length; split; [reflexivity | exact I] | lia
                                 | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; lia
                                 | cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity].
      + exists (repeat (Z_to_bv 8 0) (Z.to_nat (fsz c / 8))). unfold frame_addr, shad.
        assert (Hfr : 0 <= c * 2 ^ 20 + p * fsz c /\ (c * 2 ^ 20 + p * fsz c) / 8 + fsz c / 8 <= 0x160000 /\ 0 < fsz c /\ fsz c mod 8 = 0).
        { Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
          destruct Hc as [Hc | [Hc | [Hc | [Hc | [Hc | Hc]]]]]; subst c; cbv [fsz NF] in *; lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        assert (E8 : (uE E (eFSB ch) + 0x9000 + c * 2 ^ 20 + p * fsz c) / 8 + SHB
                     = uE E (eFSBsh ch) + 0x1200 + ((c * 2 ^ 20 + p * fsz c) / 8)).
        { rewrite HFsh. unfold shad.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
          Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
        rewrite E8.
        apply (ZC _ _ _ _ _ W3); [cbn; rewrite repeat_length; split; [reflexivity | exact I] | apply Z.div_pos; lia
                                 | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (apply Z.div_pos; lia); lia
                                 | cbn; rewrite app_nil_r, Nat.add_0_r; reflexivity]. }
  split.
  { apply fs_gstate_of_const; [exact (OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf_nt _) | exact (sym_cells_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W0)|].

    intros c Hc. pose proof (oflags_range c Hc) as (R1 & R2 & R3). unfold fl_base. change (b8 0) with (Z_to_bv 8 0).
    replace (uE E (eFSB ch) + 0x1000 + flags_off c) with (uE E (eFSB ch) + 0x1000 + flags_off c) by lia.
    apply (zero_u8arr _ _ _ _ _ W2); [lia | rewrite Z2Nat.id by lia; lia]. }
  split; [apply CLS; left; reflexivity|]. split; [apply CLS; right; left; reflexivity|]. split; [apply CLS; right; right; left; reflexivity|].
  split; [apply CLS; right; right; right; left; reflexivity|]. split; [apply CLS; right; right; right; right; left; reflexivity|]. split; [apply CLS; right; right; right; right; right; reflexivity|].
  split; [rewrite zw_uE; exact (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W4)|].
  split.
  - exists (uE E (eDTVB ch)). split.
    + pose proof (APS.fact_ok_sound bsegs E _ (kn ch) _ (rim_know A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) W8) as K. cbn [kentry_ok] in K. unfold uE. lia.
    + pose proof (lit_cells_in A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ W5) as LC.
      unfold tga_cells, dtls_cells. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
      split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
      split; [apply LC; in_lit|]. split; [apply LC; in_lit|]. split; [apply LC; in_lit|].
      split; [rewrite zw_uE; exact (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W6)|].
      rewrite zw_uE. exact (sym_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W7).
  - split; [|unfold fs_busy; cbn [frames sigma0 sigma_init]; constructor].
    exists (edenot E (eTB ch)), (edenot E (eTE ch)). unfold ttls_cells.
    apply rw_cells_cons; [exact (sym_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W9)|].
    cbn [csize]. replace (uE E (eT ch) + 48 + Z.of_nat 8) with (uE E (eT ch) + 56) by lia.
    exact (sym_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W10).
Qed.

End FS.

Definition hs_dep_ok (ch : acs) : bool :=
  match lit_of (eH1 ch), lit_of (ef0 ch) with
  | Some h1, Some f0 =>
      (forallb (fun b => (Z.leb 0 b && Z.ltb b (2 ^ 20) && hs_rw_cells ch (d_tab + 4 * b) [zw4 (tab_of [h1] b)])%bool) [bkt h1]
       && hs_rw_cells ch d_nuniq [zw4 1] && lit_word ch d_map1 8 (eDNB ch)
       && sym_word ch (eDNB ch) 16 8 (eH1 ch) && sym_cells ch (eDNB ch) 24 [zw4 0; zw4 1] && sym_zero ch (eDNB ch) 32 (2 ^ 20 - 32)
       && lit_word ch s_total 8 (ef0 ch) && lit_word ch s_data0 8 (eSSB ch) && lit_word ch s_stored0 4 (ef0 ch)
       && Z.leb 0 f0 && Z.ltb f0 (2 ^ 20) && sym_zero ch (eSSB ch) (8 * f0) (2 ^ 23 - 8 * f0))%bool
  | _, _ => false
  end.

Section Dep.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation Σ0 := (sigma0 A E ch model).

Lemma zero_stk : forall e off n, sym_zero ch e off n = true -> stk bsegs m (uE E e + off) (uE E e + off + n).
Proof.
  intros e off n H.
  destruct (sym_zero_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' e off n H) as ((_ & _ & W) & W1 & W2 & Z).
  split; [lia|]. split; [lia|]. intros a Ha. split.
  - replace a with (uE E e + off + (a - (uE E e + off))) by lia. apply W. lia.
  - exists (Z_to_bv 8 0). unfold mrd, wa. replace a with (uE E e + off + (a - (uE E e + off))) by lia. rewrite Z by lia. reflexivity.
Qed.

Lemma lit_uE : forall e z, lit_of e = Some z -> uE E e = z.
Proof.
  intros e z H. destruct e; try discriminate. cbn in H. injection H as <-. unfold uE. cbn [edenot]. rewrite u_lit64. reflexivity.
Qed.

Lemma rim_dep : hs_dep_ok ch = true ->
  (forall h1 b, lit_of (eH1 ch) = Some h1 -> 0 <= b < 2 ^ 20 -> b <> bkt h1 -> rw_cells bsegs m (d_tab + 4 * b) [zw4 0]) ->
  dep_rep (lay Σ0) (dep Σ0) m.
Proof.
  intros H HDEPZ. unfold hs_dep_ok in H.
  destruct (lit_of (eH1 ch)) as [h1|] eqn:Hh1; [|discriminate]. destruct (lit_of (ef0 ch)) as [f0|] eqn:Hf0; [|discriminate].
  apply andb_prop in H as [H W11]. apply andb_prop in H as [H W10]. apply andb_prop in H as [H W9]. apply andb_prop in H as [H W8].
  apply andb_prop in H as [H W7]. apply andb_prop in H as [H W6]. apply andb_prop in H as [H W5]. apply andb_prop in H as [H W4].
  apply andb_prop in H as [H W3]. apply andb_prop in H as [H W2]. apply andb_prop in H as [Wtab Wn].
  apply Z.leb_le in W9. apply Z.ltb_lt in W10.
  pose proof (lit_uE _ _ Hh1) as Uh. pose proof (lit_uE _ _ Hf0) as Uf.
  pose proof (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as LC.
  pose proof (lit_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as LW8.
  unfold dep_rep, depot_rep, d_n, sigma0, sigma_init, dep0. cbn [lay dep lay0 l_DNB l_SSB d_hs d_tot length].
  change (hash_of [uE E (eH1 ch)] 1) with (uE E (eH1 ch)). rewrite Uh. rewrite Uf.
  split.
  { intros b Hb. unfold DEP_BK in Hb. apply in_BK_ALL in Hb. destruct (Z.eq_dec b (bkt h1)) as [->|Hne].
    - pose proof (proj1 (forallb_forall _ _) Wtab (bkt h1) (or_introl eq_refl)) as X. cbv beta in X.
      apply andb_prop in X as [X Y]. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      split; [lia | exact (LC _ _ Y)].
    - split; [exact Hb|]. unfold tab_of. cbn [lastidx]. rewrite (proj2 (Z.eqb_neq (bkt h1) b)) by congruence. cbn [Z.eqb].
      exact (HDEPZ h1 b eq_refl Hb Hne). }
  split; [exact (LC _ _ Wn)|].
  split; [rewrite zw_uE; exact (LW8 _ _ W2)|].
  split.
  { intros i Hi. assert (i = 1) by lia. subst i. exists (Z_to_bv 64 1).
    apply rw_cells_cons; [rewrite <- Uh, zw_uE; exact (sym_word8 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W3)|].
    cbn [csize]. replace (uE E (eDNB ch) + 16 * 1 + Z.of_nat 8) with (uE E (eDNB ch) + 24) by lia.
    exact (sym_cells_sound A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ _ W4). }
  split.
  { replace (uE E (eDNB ch) + 16 * (Z.of_nat 1 + 1)) with (uE E (eDNB ch) + 32) by lia.
    replace (uE E (eDNB ch) + 2 ^ 20) with (uE E (eDNB ch) + 32 + (2 ^ 20 - 32)) by lia. exact (zero_stk _ _ _ W5). }
  split; [rewrite <- Uf, zw_uE; exact (LW8 _ _ W6)|].
  split; [rewrite zw_uE; exact (LW8 _ _ W7)|].
  split; [rewrite <- Uf, zw_uE; exact (lit_word4 A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' _ _ W8)|].
  replace (uE E (eSSB ch) + 2 ^ 23) with (uE E (eSSB ch) + 8 * f0 + (2 ^ 23 - 8 * f0)) by lia. exact (zero_stk _ _ _ W11).
Qed.

End Dep.

Definition hs_ia_ok (ch : acs) : bool :=
  (hs_rw_cells ch g_ia_word [zw4 0] && hs_rw_cells ch IAP [zb1 0] && hs_rw_cells ch (IAP + 0x81008) [CB 40 (repeat (Z_to_bv 8 0) 40)]
   && hs_rw_cells ch 0x17fea8 [zw8 0x219420] && hs_rw_cells ch 0x219420 [zw8 4096])%bool.

Lemma u8arr_of_seg : forall (m : mem) a n, seg_rw_ok bsegs a n = true -> 0 <= n -> exists bs, Z.of_nat (length bs) = n /\ u8arr bsegs m a bs.
Proof.
  intros m a n H Hn. destruct (seg_rw_ok_sound bsegs a n H m) as [W S].
  destruct (stk_bytes bsegs m a (Z.to_nat n) ltac:(rewrite Z2Nat.id by lia; exact S)) as (bs & Hl & B).
  exists bs. split; [rewrite Hl; apply Z2Nat.id; lia|]. split; [exact B|]. rewrite Hl, Z2Nat.id by lia. exact W.
Qed.

Section IA.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation Σ0 := (sigma0 A E ch model).

Lemma rim_ia : hs_ia_ok ch = true -> ia_rep Σ0 m.
Proof.
  intros H. unfold hs_ia_ok in H.
  apply andb_prop in H as [H W4]. apply andb_prop in H as [H W3]. apply andb_prop in H as [H W2]. apply andb_prop in H as [W0 W1].
  pose proof (hi_rw_cells A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA') as LC.
  unfold ia_rep. exists false. unfold ia_state.
  split; [exact (LC _ _ W0)|]. split; [exists (Z_to_bv 8 0); exact (LC _ _ W1)|].
  split; [exact (u8arr_of_seg m _ _ seg_rw_IAP1 ltac:(lia))|]. split; [exact (u8arr_of_seg m _ _ seg_rw_IAP2 ltac:(lia))|].
  split; [exact (u8arr_of_seg m _ _ seg_rw_IAP3 ltac:(lia))|]. split; [exists (repeat (Z_to_bv 8 0) 40); exact (LC _ _ W2)|].
  split; [exact (LC _ _ W3) | exact (LC _ _ W4)].
Qed.

End IA.

Fixpoint kknown_at (k : list kentry) (cur : Z) : option Z :=
  match k with
  | [] => None
  | KZero (SA (ELit b) o) (ELit n) :: r =>
      if (Z.leb 0 b && Z.ltb b (2 ^ 64) && Z.leb 0 n && Z.ltb n (2 ^ 64) && Z.leb (b + o) cur && Z.ltb cur (b + o + n))%bool
      then Some (b + o + n) else kknown_at r cur
  | KFill (SA (ELit b) o) (ELit n) _ :: r =>
      if (Z.leb 0 b && Z.ltb b (2 ^ 64) && Z.leb 0 n && Z.ltb n (2 ^ 64) && Z.leb (b + o) cur && Z.ltb cur (b + o + n))%bool
      then Some (b + o + n) else kknown_at r cur
  | KWord (SA (ELit b) o) w _ :: r =>
      if (Z.leb 0 b && Z.ltb b (2 ^ 64) && Z.leb (b + o) cur && Z.ltb cur (b + o + Z.of_nat w))%bool
      then Some (b + o + Z.of_nat w) else kknown_at r cur
  | _ :: r => kknown_at r cur
  end.
Fixpoint known_cover (k : list kentry) (cur hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb hi cur then true else match kknown_at k cur with Some h => known_cover k h hi f | None => false end
  end.

Definition kzero2 (k : list kentry) (sb : expr) (sk : Z) (sn : expr) : bool :=
  existsb (fun K1 => match K1 with
    | KZero (SA b1 o1) n1 =>
        (expr_eqb b1 sb && Z.eqb o1 sk
         && existsb (fun K2 => match K2 with
                               | KZero (SA b2 o2) n2 =>
                                   (expr_eqb (eadd (eaddz b1 o1) n1) (eaddz b2 o2) && expr_eqb (eadd (eaddz b2 o2) n2) (eadd (eaddz sb sk) sn))%bool
                               | _ => false
                               end) k)%bool
    | _ => false
    end) k.

Definition kzero2L (k : list kentry) (sb : expr) (sk : Z) (sn : expr) : bool :=
  let tgt := eadd (eaddz sb sk) sn in
  existsb (fun K1 => match K1 with
    | KZero (SA b1 o1) n1 =>
        if (expr_eqb b1 sb && Z.eqb o1 sk)%bool then
          let t1 := eadd (eaddz b1 o1) n1 in
          existsb (fun K2 => match K2 with
                             | KZero (SA b2 o2) n2 =>
                                 if expr_eqb t1 (eaddz b2 o2) then expr_eqb (eadd (eaddz b2 o2) n2) tgt else false
                             | _ => false
                             end) k
        else false
    | _ => false
    end) k.
Lemma existsb_ext_rim : forall {X} (f g : X -> bool) l, (forall x, f x = g x) -> existsb f l = existsb g l.
Proof. intros X f g l H. induction l as [|x l IH]; [reflexivity|]. cbn [existsb]. rewrite H, IH. reflexivity. Qed.

Lemma kzero2L_eq : forall k sb sk sn, kzero2L k sb sk sn = kzero2 k sb sk sn.
Proof.
  intros k sb sk sn. unfold kzero2L, kzero2. apply existsb_ext_rim. intros K1.
  destruct K1 as [|[b1 o1] n1| | | | | | | |]; reflexivity.
Qed.

Lemma kzero2_sound : forall E M k sb sk sn, know_ok bsegs E M k -> kzero2 k sb sk sn = true ->
  0 <= estart E (SA sb sk) -> estart E (SA sb sk) + elenZ E sn < 2 ^ 64 ->
  forall i, 0 <= i < elenZ E sn -> M (Z_to_bv 64 (estart E (SA sb sk) + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E M k sb sk sn HK H H0 H1 i Hi. unfold kzero2 in H. apply existsb_exists in H as (K1 & HK1 & H).
  destruct K1 as [|[b1 o1] n1| | | | | | | |]; try discriminate.
  apply andb_prop in H as [H H2]. apply andb_prop in H as [Hb Ho]. apply expr_eqb_eq in Hb. apply Z.eqb_eq in Ho. subst b1 o1.
  apply existsb_exists in H2 as (K2 & HK2 & H2). destruct K2 as [|[b2 o2] n2| | | | | | | |]; try discriminate.
  apply andb_prop in H2 as [E1 E2]. apply expr_eqb_eq in E1. apply expr_eqb_eq in E2.
  pose proof (proj1 (Forall_forall _ _) HK _ HK1) as Z1. pose proof (proj1 (Forall_forall _ _) HK _ HK2) as Z2.
  cbn [kentry_ok] in Z1, Z2. destruct Z1 as [(F1a & F1b & F1c & F1d) Z1]. destruct Z2 as [(F2a & F2b & F2c & F2d) Z2].
  apply (f_equal (fun e => bv_unsigned (edenot E e))) in E1. apply (f_equal (fun e => bv_unsigned (edenot E e))) in E2. cbv beta in E1, E2. unfold eadd in E1, E2.
  unfold eaddz in E1, E2. rewrite !mkAlu_denot, !u_add64 in E1. rewrite !mkAlu_denot, !u_add64 in E2. cbn [edenot] in E1, E2.
  rewrite !u_lit64 in E1, E2. unfold two64 in E1, E2. unfold estart in *. cbn [a_base a_off] in *. unfold elenZ, uE in *.
  set (S0 := bv_unsigned (edenot E sb) + sk) in *. set (S2 := bv_unsigned (edenot E b2) + o2) in *.
  assert (AM : forall x kk, 0 <= x + kk < 2 ^ 64 -> (x + kk mod 2 ^ 64) mod 2 ^ 64 = x + kk).
  { intros x kk Hx. rewrite Z.add_mod_idemp_r by lia. apply Z.mod_small. exact Hx. }
  rewrite (AM (bv_unsigned (edenot E sb)) sk) in E1, E2 by (fold S0; lia).
  rewrite (AM (bv_unsigned (edenot E b2)) o2) in E1, E2 by (fold S2; lia). fold S0 S2 in E1, E2.
  destruct (Z_lt_le_dec i (bv_unsigned (edenot E n1))) as [Lt|Ge]; [exact (Z1 i ltac:(lia))|].
  clearbody S0 S2.
  assert (HS2 : S2 = S0 + bv_unsigned (edenot E n1) /\ i - bv_unsigned (edenot E n1) < bv_unsigned (edenot E n2)).
  { destruct (Z.eq_dec (S0 + bv_unsigned (edenot E n1)) (2 ^ 64)) as [X|X]; [lia|].
    rewrite Z.mod_small in E1 by lia. subst S2. split; [reflexivity|].
    destruct (Z.eq_dec (S0 + bv_unsigned (edenot E n1) + bv_unsigned (edenot E n2)) (2 ^ 64)) as [Y|Y].
    - lia.
    - rewrite (Z.mod_small (S0 + bv_unsigned (edenot E n1) + bv_unsigned (edenot E n2))) in E2 by lia.
      rewrite Z.mod_small in E2 by lia. lia. }
  destruct HS2 as [HS2 Hl]. replace (S0 + i) with (S2 + (i - bv_unsigned (edenot E n1))) by lia. apply Z2. lia.
Qed.

Fixpoint sh_scan (k : list kentry) (g hi : Z) (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S f => match know_byte_lit bsegs k (ELit 0) (g + SHB) with
           | Some z => ((z =? 0) || ((0 <? z) && (z <? 8) && (Z.min hi (8 * g + 8) - 1 - 8 * g <? z))) && sh_scan k (g + 1) hi f
           | None => false
           end
  end.
Definition static_rng_ok (ch : acs) (r : Z * Z) : bool :=
  let lo := fst r in let hi := snd r in
  sh_scan (klit_cut (shad lo) (shad hi + 1) (kn ch)) (lo / 8) hi (Z.to_nat ((hi - 1) / 8 - lo / 8 + 1)).
Definition hs_static_ok (ch : acs) : bool := forallb (static_rng_ok ch) CS_ACC.

Lemma sh_scan_nth : forall k f g hi, sh_scan k g hi f = true -> forall j, (j < f)%nat ->
  exists z, know_byte_lit bsegs k (ELit 0) (g + Z.of_nat j + SHB) = Some z
    /\ (z = 0 \/ (0 < z < 8 /\ Z.min hi (8 * (g + Z.of_nat j) + 8) - 1 - 8 * (g + Z.of_nat j) < z)).
Proof.
  intros k f. induction f as [|f IH]; intros g hi H j Hj; [lia|]. cbn [sh_scan] in H.
  destruct (know_byte_lit bsegs k (ELit 0) (g + SHB)) as [z|] eqn:Hk; [|discriminate]. apply andb_prop in H as [H1 H2].
  destruct j as [|j].
  - exists z. replace (g + Z.of_nat 0) with g by lia. split; [exact Hk|]. apply orb_prop in H1 as [X|X]; [left; apply Z.eqb_eq; exact X|].
    right. apply andb_prop in X as [X X3]. apply andb_prop in X as [X1 X2]. apply Z.ltb_lt in X1, X2, X3. lia.
  - destruct (IH (g + 1) hi H2 j ltac:(lia)) as (z' & Hz' & Hc). exists z'. replace (g + Z.of_nat (S j)) with (g + 1 + Z.of_nat j) by lia. split; assumption.
Qed.

Definition hs_shadow_ok (A : atable) (ch : acs) : bool :=
  (let '(sb, sk, sn) := shadow_of A (kn ch) e_band e_bandlen in
   ((if kzero_x (kn ch) (kn ch) sb sk sn then true else kzero2L (kn ch) sb sk sn) && kwritable_x (kn ch) (kn ch) sb sk sn))
  && kwritable (kn ch) (kn ch) (ELit 0) 0x7fffa000 0xda000 && known_cover (kn ch) 0x7fffa000 0x800d4000 (S (length (kn ch)))
  && hs_static_ok ch.

Lemma kknown_at_sound : forall E M k cur h, know_ok bsegs E M k -> kknown_at k cur = Some h ->
  cur < h /\ forall z, cur <= z < h -> mrd bsegs M (wa z) <> None.
Proof.
  intros E M k cur h HK. induction k as [|K r IH]; intros H; [discriminate|].
  apply Forall_cons_iff in HK as [HKK HKr].
  destruct K as [[b o] w v|[b o] n| | | | | |  |[b o] n c|]; cbn [kknown_at] in H; try exact (IH HKr H).
  - destruct b as [bz| | | | | | |]; try exact (IH HKr H).
    destruct (Z.leb 0 bz && Z.ltb bz (2 ^ 64) && Z.leb (bz + o) cur && Z.ltb cur (bz + o + Z.of_nat w))%bool eqn:X; [|exact (IH HKr H)].
    injection H as <-. repeat match type of X with (_ && _)%bool = true => apply andb_prop in X as [X ?Y] end.
    repeat match goal with Y : Z.leb _ _ = true |- _ => apply Z.leb_le in Y | Y : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Y end.
    apply Z.leb_le in X. split; [lia|]. intros z Hz. cbn [kentry_ok] in HKK. destruct HKK as (Hw & Hfl & Hr).
    rewrite rdn_AS_Lib in Hr. unfold flat, estart in Hfl. cbn [a_base a_off edenot] in Hfl. rewrite u_lit64 in Hfl. unfold two64 in Hfl.
    rewrite Z.mod_small in Hfl by lia.
    apply rdn_bytes_at in Hr; [|unfold adenot, v_addi; cbn [a_base a_off edenot]; rewrite u64_lit; [rewrite u_lit64; unfold two64; rewrite Z.mod_small by lia; lia|
                                  rewrite u_lit64; unfold two64; rewrite Z.mod_small by lia; lia]].
    destruct Hr as (_ & Hlen & Hr). rewrite length_N_to_le_bytes in Hlen.
    assert (Ha : bv_unsigned (adenot E (SA (ELit bz) o)) = bz + o).
    { unfold adenot, v_addi. cbn [a_base a_off edenot]. rewrite u64_lit; [rewrite u_lit64; unfold two64; rewrite Z.mod_small by lia; reflexivity|].
      rewrite u_lit64; unfold two64; rewrite Z.mod_small by lia; lia. }
    rewrite Ha in Hr. specialize (Hr (Z.to_nat (z - (bz + o))) ltac:(rewrite length_N_to_le_bytes; lia)).
    replace (bz + o + Z.of_nat (Z.to_nat (z - (bz + o)))) with z in Hr by lia. rewrite Hr.
    rewrite nth_error_nth' with (d := Z_to_bv 8 0) by (rewrite length_N_to_le_bytes; lia). discriminate.
  - destruct b as [bz| | | | | | |]; try exact (IH HKr H). destruct n as [nz| | | | | | |]; try exact (IH HKr H).
    destruct (Z.leb 0 bz && Z.ltb bz (2 ^ 64) && Z.leb 0 nz && Z.ltb nz (2 ^ 64) && Z.leb (bz + o) cur && Z.ltb cur (bz + o + nz))%bool eqn:X;
      [|exact (IH HKr H)].
    injection H as <-. repeat match type of X with (_ && _)%bool = true => apply andb_prop in X as [X ?Y] end.
    repeat match goal with Y : Z.leb _ _ = true |- _ => apply Z.leb_le in Y | Y : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Y end.
    apply Z.leb_le in X. split; [lia|]. intros z Hz. cbn [kentry_ok] in HKK. destruct HKK as [_ Hz0].
    unfold estart, elenZ in Hz0. cbn [a_base a_off edenot] in Hz0. rewrite !u_lit64 in Hz0. unfold two64 in Hz0.
    rewrite !Z.mod_small in Hz0 by lia. unfold mrd, wa. replace z with (bz + o + (z - (bz + o))) by lia. rewrite Hz0 by lia. discriminate.
  - destruct b as [bz| | | | | | |]; try exact (IH HKr H). destruct n as [nz| | | | | | |]; try exact (IH HKr H).
    destruct (Z.leb 0 bz && Z.ltb bz (2 ^ 64) && Z.leb 0 nz && Z.ltb nz (2 ^ 64) && Z.leb (bz + o) cur && Z.ltb cur (bz + o + nz))%bool eqn:X;
      [|exact (IH HKr H)].
    injection H as <-. repeat match type of X with (_ && _)%bool = true => apply andb_prop in X as [X ?Y] end.
    repeat match goal with Y : Z.leb _ _ = true |- _ => apply Z.leb_le in Y | Y : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Y end.
    apply Z.leb_le in X. split; [lia|]. intros z Hz. cbn [kentry_ok] in HKK. destruct HKK as [_ Hz0].
    unfold estart, elenZ in Hz0. cbn [a_base a_off edenot] in Hz0. rewrite !u_lit64 in Hz0. unfold two64 in Hz0.
    rewrite !Z.mod_small in Hz0 by lia. unfold mrd, wa. replace z with (bz + o + (z - (bz + o))) by lia. rewrite Hz0 by lia. discriminate.
Qed.

Lemma known_cover_sound : forall E M k fuel cur hi, know_ok bsegs E M k -> known_cover k cur hi fuel = true ->
  forall z, cur <= z < hi -> mrd bsegs M (wa z) <> None.
Proof.
  intros E M k fuel. induction fuel as [|f IH]; intros cur hi HK H z Hz; cbn [known_cover] in H; [discriminate|].
  destruct (Z.leb_spec0 hi cur); [lia|].
  destruct (kknown_at k cur) as [h|] eqn:Hk; [|discriminate].
  destruct (kknown_at_sound E M k cur h HK Hk) as [Hlt Hcov].
  destruct (Z.ltb_spec0 z h); [apply Hcov; lia | exact (IH h hi HK H z ltac:(lia))].
Qed.

Section Shadow.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis Hshoff : shadow_off A = SHB.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.

#[local] Notation m := (mH FULL model A').
#[local] Notation M := (APS.Mr A argH E ch model FULL).
#[local] Notation Σ0 := (sigma0 A E ch model).
#[local] Notation sp0 := (bv_unsigned (vm_init_sp (m_vmmaps model))).

Lemma rim_readable : forall z, 0 <= z < 2 ^ 47 -> M (Z_to_bv 64 z) <> None -> mrd bsegs m (wa z) = M (Z_to_bv 64 z).
Proof.
  intros z Hz H. unfold mrd, wa. rewrite (hk_mr_some bsegs A nx0 LIMIT SINV argH FS0 HULL_ok E ch R FULL model HC A' HA'); [|exact H|rewrite u64_lit by lia; lia].
  destruct (M (Z_to_bv 64 z)); [reflexivity | exfalso; apply H; reflexivity].
Qed.

Lemma rim_shadow : hs_shadow_ok A ch = true -> sp0 mod 16 = 0 ->
  stk bsegs m (sp0 - 0x800000) (uE E (eTop ch)) ->
  shadow_rep (lay Σ0) m.
Proof.
  intros H Hsp16 HSTKWIN. pose proof (rim_know A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as HK. unfold hs_shadow_ok in H.
  apply andb_prop in H as [H Hstat].
  destruct (shadow_of A (kn ch) e_band e_bandlen) as [[sb sk] sn] eqn:Hsh.
  apply andb_prop in H as [H Hcov]. apply andb_prop in H as [H Hiw]. apply andb_prop in H as [Hz Hw].
  destruct (APSX.kwritable_x_sound bsegs E M (kn ch) (kn ch) sb sk sn HK HK Hw) as (W1 & Z2 & Z3).
  pose proof (ri_band A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as Hb. pose proof (ri_sp0 A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as (Hsp & Hlo & Hhi).
  assert (Hbl : uE E e_bandlen = 2 ^ 47 + 0x800000 - sp0).
  { unfold e_bandlen, esub, uE. rewrite mkAlu_denot, u_sub64. cbn [edenot]. rewrite u_lit64. unfold two64. rewrite Hsp. unfold uE.
    unfold sp_window_lo, sp_window_hi in *. rewrite (Z.mod_small (2 ^ 47 + 8388608)) by lia.
    pose proof (u64_range (edenot E e_sp0)). unfold uE in Hsp. rewrite Z.mod_small; lia. }
  pose proof (shadow_of_len A E M (kn ch) _ _ sb sk sn HK Hsh) as S2. rewrite Hbl in S2.
  assert (Hst : 0 <= estart E (SA sb sk) < 2 ^ 64).
  { unfold sp_window_lo, sp_window_hi in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  destruct (shadow_of_den A E M (kn ch) _ _ sb sk sn HK Hsh ltac:(rewrite Hshoff; unfold SHB; lia) Hst) as [S1 _].
  rewrite Hshoff, Hb in S1.
  unfold shadow_rep, sigma0, sigma_init. cbn [lay]. unfold l_ACEIL, STACK_WIN, lay0. cbn [l_sp0].
  set (S0 := estart E (SA sb sk)) in *.
  assert (HS0 : shad (sp0 - 0x800000) = S0) by (unfold shad; lia).
  assert (HL : (2 ^ 47 - (sp0 - 0x800000)) / 8 = elenZ E sn).
  { rewrite S2. f_equal. lia. }
  assert (Hq : exists q, sp0 = 16 * q).
  { pose proof (Z.div_mod sp0 16 ltac:(lia)) as D. rewrite Hsp16 in D. exists (sp0 / 16). lia. }
  assert (HE : shad (2 ^ 47) = S0 + elenZ E sn).
  { rewrite <- HL, <- HS0. destruct Hq as [q Hq]. rewrite Hq. unfold shad.
    replace (16 * q - 8388608) with (8 * (2 * q - 1048576)) by lia. replace (2 ^ 47 - 8 * (2 * q - 1048576)) with (8 * (2 ^ 44 - (2 * q - 1048576))) by lia.
    rewrite !(Z.mul_comm 8), !Z.div_mul by lia. change (2 ^ 47 / 8) with (2 ^ 44). lia. }
  assert (Hrng : S0 + elenZ E sn <= 2 ^ 47) by (rewrite <- HE; unfold shad, SHB; change (2 ^ 47 / 8) with (2 ^ 44); lia).
  assert (Z1 : forall i, 0 <= i < elenZ E sn -> M (Z_to_bv 64 (S0 + i)) = Some (Z_to_bv 8 0)).
  { destruct (kzero_x (kn ch) (kn ch) sb sk sn) eqn:Hz1; [exact (proj1 (APSX.kzero_x_sound bsegs E M (kn ch) (kn ch) sb sk sn HK HK Hz1)) |].
    rewrite kzero2L_eq in Hz. exact (kzero2_sound E M (kn ch) sb sk sn HK Hz Z2 ltac:(lia)). }
  split; [|split; [|split; [|split]]].
  - rewrite HS0, HL. split; [lia|]. split; [unfold zrun; rewrite repeat_length; rewrite Z2Nat.id by (pose proof (u64_range (edenot E sn)); unfold elenZ; lia); lia|].
    intros i Hi. unfold zrun in Hi. rewrite repeat_length in Hi. unfold zrun. rewrite nth_error_repeat by exact Hi.
    assert (Hi' : 0 <= Z.of_nat i < elenZ E sn) by (rewrite <- (Z2Nat.id (elenZ E sn)) by (pose proof (u64_range (edenot E sn)); unfold elenZ; lia); lia).
    rewrite rim_readable; [rewrite (Z1 (Z.of_nat i) Hi'); reflexivity | lia | rewrite (Z1 (Z.of_nat i) Hi'); discriminate].
  - rewrite HS0, HE. split; [lia|]. split; [lia|]. intros a Ha. split.
    + pose proof (W1 (Z.to_nat (S0 + elenZ E sn - S0)) ltac:(rewrite Z2Nat.id by lia; lia)) as St.
      pose proof (store_ok_wview bsegs M _ _ (Z.to_nat (a - S0)) St ltac:(lia)) as Wi.
      rewrite u64_lit in Wi by lia. rewrite Z2Nat.id in Wi by lia. replace (S0 + (a - S0)) with a in Wi by lia.
      apply (rim_wview A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'); [exact Wi|]. rewrite wa_unsigned by lia. lia.
    + exists (Z_to_bv 8 0). rewrite rim_readable; [|lia|]; replace a with (S0 + (a - S0)) by lia; rewrite (Z1 (a - S0)) by lia; [reflexivity|discriminate].
  - change (pg_dn (shad 0x10000)) with 0x7fffa000. change (shad SEGTOP_A) with 0x800d4000.
    destruct (APSX.kwritable_sound bsegs E M (kn ch) (kn ch) (ELit 0) 0x7fffa000 0xda000 HK HK Hiw ltac:(lia)) as (St & _ & _).
    unfold estart in St. cbn [a_base a_off edenot] in St. rewrite u_lit64 in St. change (0 mod two64 + 0x7fffa000) with 0x7fffa000 in St.
    split; [lia|]. split; [lia|]. intros a Ha. split.
    + pose proof (store_ok_wview bsegs M _ _ (Z.to_nat (a - 0x7fffa000)) St ltac:(lia)) as Wi.
      rewrite u64_lit in Wi by lia. rewrite Z2Nat.id in Wi by lia. replace (0x7fffa000 + (a - 0x7fffa000)) with a in Wi by lia.
      apply (rim_wview A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'); [exact Wi|]. rewrite wa_unsigned by lia. lia.
    + pose proof (known_cover_sound E M (kn ch) _ _ _ HK Hcov a Ha) as Hn.
      rewrite (hk_mrd bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA' (wa a) Hn) by (rewrite wa_unsigned by lia; lia).
      destruct (mrd bsegs M (wa a)) as [bb|]; [exists bb; reflexivity | exfalso; apply Hn; reflexivity].
  -
    unfold static_acc. apply Forall_forall. intros [qlo qhi] qHin. unfold hs_static_ok in Hstat. pose proof (proj1 (forallb_forall _ _) Hstat _ qHin) as qX.
    unfold static_rng_ok in qX. cbn [fst snd] in qX |- *.
    assert (qHr : 0x10000 <= qlo /\ qlo < qhi /\ qhi <= 0x6dfdd8).
    { unfold CS_ACC in qHin. repeat (destruct qHin as [qHin|qHin]; [injection qHin as <- <-; lia|]). destruct qHin. }
    pose proof (know_ok_filter bsegs E M (klit_keep (shad qlo) (shad qhi + 1)) (kn ch) HK) as qHK.
    intros qi qHi. set (qa := qlo + qi).
    assert (qHa : 0 <= qa / 8 - qlo / 8 < (qhi - 1) / 8 - qlo / 8 + 1).
    { unfold qa. split; [assert (qlo / 8 <= (qlo + qi) / 8) by (apply Z.div_le_mono; lia); lia
                        | assert ((qlo + qi) / 8 <= (qhi - 1) / 8) by (apply Z.div_le_mono; lia); lia]. }
    destruct (sh_scan_nth _ _ _ _ qX (Z.to_nat (qa / 8 - qlo / 8)) ltac:(apply Nat2Z.inj_lt; rewrite !Z2Nat.id by lia; lia)) as (qz & qHz & qHc).
    rewrite Z2Nat.id in qHz, qHc by lia. replace (qlo / 8 + (qa / 8 - qlo / 8)) with (qa / 8) in qHz, qHc by lia.
    assert (qB : 0 <= qa / 8 + SHB /\ qa / 8 + SHB + 1 <= 2 ^ 47) by (unfold SHB; pose proof (Z.div_pos qa 8 ltac:(unfold qa; lia) ltac:(lia));
      assert (qa / 8 <= 0x6dfdd8) by (apply Z.div_le_upper_bound; unfold qa; lia); lia).
    assert (qFl : flat E (SA (ELit 0) (qa / 8 + SHB)) 1) by (unfold flat, estart; cbn [a_base a_off edenot]; rewrite u_lit64; unfold two64; rewrite Z.mod_0_l by lia; lia).
    destruct (know_byte_lit_sound bsegs E M _ _ _ _ qHK qHz qFl) as (qRd & qzr).
    rewrite rdn_AS_Lib in qRd. apply rdn_bytes_at in qRd; [|rewrite (flat_u E _ _ qFl); unfold estart; cbn [a_base a_off edenot]; rewrite u_lit64; unfold two64; rewrite Z.mod_0_l by lia; lia].
    rewrite (flat_u E _ _ qFl) in qRd. unfold estart in qRd. cbn [a_base a_off edenot] in qRd. rewrite u_lit64 in qRd. unfold two64 in qRd. rewrite Z.mod_0_l, Z.add_0_l in qRd by lia.
    exists (Z_to_bv 8 qz). split.
    + unfold shad. apply (hk_bytes_at bsegs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A' HA'); [cbn; lia | exact qRd].
    + unfold sh_ok. assert (qU : bv_unsigned (Z_to_bv 8 qz) = qz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; lia).
      rewrite qU.
      destruct qHc as [Y|Y]; [left; exact Y | right].
      pose proof (Z.div_mod qa 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound qa 8 ltac:(lia)) as B. split; [lia|].
      assert (qa mod 8 <= Z.min qhi (8 * (qa / 8) + 8) - 1 - 8 * (qa / 8)) by (unfold qa in *; lia). lia.
  -   cbn [l_top]. exact HSTKWIN.
Qed.

End Shadow.

Definition hs_rt_ok (A : atable) (ch : acs) : bool :=
  (hs_lay_ok ch && hs_consts_ok ch && hs_zero_ok ch && hs_primsh_ok A ch && hs_fs_ok ch && hs_dep_ok ch && hs_ia_ok ch
   && hs_shadow_ok A ch && hs_vis_ok A ch)%bool.

Lemma page_allowed_range : forall l lo hi (x : word), In (pg_dn lo, pg_up hi) l -> lo <= bv_unsigned x < hi ->
  page_allowedb l (page_base x) = true.
Proof.
  intros l lo hi x Hin Hx. unfold page_allowedb. apply existsb_exists. exists (pg_dn lo, pg_up hi). split; [exact Hin|].
  cbn [fst snd]. destruct (page_base_le' x) as (P1 & P2 & P3). unfold pg_dn, pg_up, page_size.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  apply andb_true_intro; split; apply Z.leb_le; lia.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section Init.
Variables (A : atable) (nx0 : nat) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment bsegs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis Hsegtop : img_hi A = SEGTOP_A.
Hypothesis Hshoff : shadow_off A = SHB.
Hypothesis Hlim : LIMIT = VMLIMIT.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok bsegs A nx0 LIMIT SINV argH FS0 E ch R FULL model.
Hypothesis HT : hs_rt_ok A ch = true.

#[local] Notation Σ0 := (sigma0 A E ch model).
#[local] Notation A0 := (rtA_allow (sigma0 A E ch model)).
#[local] Notation m := (mH FULL model (rtA_allow (sigma0 A E ch model))).
#[local] Notation sp0 := (bv_unsigned (vm_init_sp (m_vmmaps model))).

Hypothesis HSTKWIN : forall top, top mod 4096 = 0 -> top < sp0 - 0xa0 + 4096 -> stk bsegs m (sp0 - 0x800000) top.
Hypothesis HDEPZ : forall h1 b, lit_of (eH1 ch) = Some h1 -> 0 <= b < 2 ^ 20 -> b <> bkt h1 -> rw_cells bsegs m (d_tab + 4 * b) [zw4 0].

Lemma ri_tests : hs_lay_ok ch = true /\ hs_consts_ok ch = true /\ hs_zero_ok ch = true /\ hs_primsh_ok A ch = true
  /\ hs_fs_ok ch = true /\ hs_dep_ok ch = true /\ hs_ia_ok ch = true /\ hs_shadow_ok A ch = true /\ hs_vis_ok A ch = true.
Proof.
  pose proof HT as H. unfold hs_rt_ok in H.
  apply andb_prop in H as [H T9]. apply andb_prop in H as [H T8]. apply andb_prop in H as [H T7]. apply andb_prop in H as [H T6]. apply andb_prop in H as [H T5].
  apply andb_prop in H as [H T4]. apply andb_prop in H as [H T3]. apply andb_prop in H as [T1 T2].
  repeat split; assumption.
Qed.

Lemma ri_HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A0 p = true.
Proof. exact (ri_allow A E ch model). Qed.

Lemma ri_prim : prim_rep Σ0 m.
Proof.
  pose proof ri_tests as (T1 & _ & T3 & T4 & _).
  pose proof (rim_zero A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T3) as (RI & _).
  pose proof (ri_layout_ok A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1) as HL.
  assert (Hq : uE E (prim_q ch) = uE E (eSB ch) + 2 ^ 32).
  { unfold prim_q, uE at 1. rewrite edenot_eaddz. rewrite u64_lit; [reflexivity|]. unfold layout_ok in HL. cbn [lay0 l_SB l_PRB] in HL.
    destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL, STACK_WIN in P3. cbn [lay0 l_sp0] in P3.
    pose proof (u64_range (edenot E (eSB ch))). pose proof (u64_range (vm_init_sp (m_vmmaps model))). unfold uE in *. lia. }
  assert (SH : forall z, shad (uE E (eSB ch) + 2 ^ 32) <= z < shad (uE E (eSB ch) + 2 ^ 37) -> m (Z_to_bv 64 z) = Some (Z_to_bv 8 0)).
  { intros z Hz. rewrite <- Hq in Hz.
    apply (rim_primsh A nx0 LIMIT SINV argH FS0 argH_high Hsegtop Hshoff E ch R FULL model HC A0 T4);
      [ rewrite Hq, (ri_band A nx0 LIMIT SINV argH FS0 E ch R FULL model HC); unfold prim_qlen; unfold layout_ok in HL;
        destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _); unfold l_ACEIL, STACK_WIN in P3; cbn [lay0 l_sp0 l_SB l_PRB] in *; lia
      | | rewrite Hq; rewrite Hq in Hz; unfold prim_qlen; replace (uE E (eSB ch) + 2 ^ 32 + 31 * 2 ^ 32) with (uE E (eSB ch) + 2 ^ 37) by lia; exact Hz].
    intros a Ha. unfold rtA_allow, sigma0, sigma_init. cbn [aw lay app]. apply APS.page_allowedb_app_r.
    apply (page_allowed_range _ (shad (uE E (eSB ch))) (shad (uE E (eSB ch) + 2 ^ 37))); [unfold allow_main; cbn [lay0 l_SB]; right; left; reflexivity|].
    rewrite Hq in Ha. unfold shad, prim_qlen in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
  unfold prim_rep. intros c Hc. cbn [pr sigma0 sigma_init]. unfold reg_rep, reg0. cbn [r_st r_fl r_mfa r_muser length]. cbn [lay lay0 l_SB].
  destruct (RI c Hc) as (R1 & R2 & R3).
  rewrite Z.mul_0_r. split; [exact R1|]. split; [exact R2|]. split; [eexists _, _, _, _, _, _, _, _, _; exact R3|].
  change (l_SB (lay Σ0)) with (uE E (eSB ch)).
  assert (HSB : 0 <= uE E (eSB ch) < 2 ^ 47).
  { unfold layout_ok in HL. destruct HL as (_ & _ & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & Hsb & _). unfold l_ACEIL, STACK_WIN in P3. cbn [lay0 l_sp0 l_SB l_PRB] in *.
    pose proof (u64_range (edenot E (eSB ch))). pose proof (u64_range (vm_init_sp (m_vmmaps model))). unfold uE in *.
    pose proof (ri_sp0 A nx0 LIMIT SINV argH FS0 E ch R FULL model HC) as (_ & _ & Hhi). unfold sp_window_hi in Hhi. lia. }
  unfold rb, fa. split.
  { exists []. split; [|split; reflexivity]. unfold fl_arr, u32arr, fa, rb. change (u32s []) with (@nil byte). cbn [length Z.of_nat].
    split; [apply bytes_at_nil; lia|]. split; [lia|]. split; [lia|]. intros i Hi; lia. }
  split; [split; [lia|]; split; [lia|]; intros a Ha; lia|].
  split.
  { change (farun ((0 - 0) / 8)) with (@nil byte). apply bytes_at_nil. unfold shad, SHB.
    assert (0 <= (uE E (eSB ch) + c * 2 ^ 32 + 0) / 8 <= 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
  assert (Hin : shad (uE E (eSB ch) + 2 ^ 32) <= shad (uE E (eSB ch) + c * 2 ^ 32)
                /\ shad (uE E (eSB ch) + c * 2 ^ 32 + 2 ^ 32) <= shad (uE E (eSB ch) + 2 ^ 37)).
  { unfold shad. split; apply Z.add_le_mono_r; apply Z.div_le_mono; lia. }
  assert (B1 : 0 <= (uE E (eSB ch) + c * 2 ^ 32) / 8) by (apply Z.div_pos; lia).
  assert (B2 : (uE E (eSB ch) + 2 ^ 37) / 8 <= 2 ^ 61) by (apply Z.div_le_upper_bound; lia).
  split; [unfold shad, SHB in *; lia|]. split; [unfold shad, SHB in *; lia|]. intros a Ha.
  assert (Hz : m (wa a) = Some (Z_to_bv 8 0)) by (apply SH; lia).
  unfold mrd. rewrite Hz. split; [unfold wview; rewrite Hz; discriminate | exists (Z_to_bv 8 0); reflexivity].
Qed.

Lemma ri_art : ART_A Σ0 m.
Proof.
  pose proof ri_tests as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  pose proof (rim_zero A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T3) as (_ & Zc & Zs & Zq).
  pose proof (ri_layout_ok A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1) as HL.
  apply ART_intro.
  - exact (ri_rt_wf A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1).
  - exact (rim_consts A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T2).
  - exact ri_prim.
  - exact Zc.
  - unfold chunk_rep. cbn [pr sec sigma0 sigma_init r_st reg0]. split; [intros c i st _ Hn; destruct i; discriminate | intros k s' Hk; destruct k; discriminate].
  - exact Zs.
  - exact Zq.
  - exact (rim_dep A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T6 HDEPZ).
  - exact (rim_fs A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T5).
  - exact (rim_ia A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high E ch R FULL model HC A0 ri_HA' T7).
  - apply (rim_shadow A nx0 LIMIT SINV argH FS0 SEGS_in_hull HULL_ok argH_high Hshoff E ch R FULL model HC A0 ri_HA' T8).
    + unfold layout_ok in HL. cbn [lay0 l_sp0] in HL. exact (proj1 (proj2 HL)).
    + unfold layout_ok in HL. cbn [lay0 l_sp0 l_top] in HL. destruct HL as (_ & _ & HT1 & HT2 & _). exact (HSTKWIN _ HT2 (proj2 HT1)).
  -
    assert (Tsl : hs_shlazy_ok ch = true) by (unfold hs_lay_ok in T1; apply andb_prop in T1 as [_ Tsl]; exact Tsl).
    intros a Hs Hp Hlo Hx.
    exact (rim_vis A nx0 LIMIT SINV argH FS0 Hsegtop Hshoff E ch R FULL model HC A0 T9 Tsl a Hs Hp Hlo
             (vis_premise_filter (vm_maps (m_vmmaps model)) _ Hx)).
Qed.

Theorem rt_init_glue :
  (forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb (rtA_allow Σ0) p = true)
  /\ A_wf (rtA_allow Σ0) /\ MInv (rtA_allow Σ0) model /\ ARTM_A Σ0 model /\ rtA_sp0 Σ0 = sp0
  /\ ART_A Σ0 m /\ sigma0_ok RTA Σ0 (sp0 - USP_OFF).
Proof.
  pose proof ri_tests as (T1 & _).
  split; [exact ri_HA'|]. split; [exact (ri_awf A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1)|].
  split; [exact (ri_minv A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1 Hlim)|].
  split; [exact (ri_artm A nx0 LIMIT SINV argH FS0 E ch R FULL model HC T1 Hlim)|].
  split; [reflexivity|]. split; [exact ri_art|]. exact (ri_sig A nx0 LIMIT SINV argH FS0 E ch R FULL model HC).
Qed.

End Init.
