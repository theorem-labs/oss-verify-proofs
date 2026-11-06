(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.

Abbreviation amem := (word -> option byte).

(* [comment removed for export] *)
Definition SH_LO : Z := 2147450880.          (* [comment removed for export] *)
Definition SH_HI : Z := 17594333495296.      (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint app_fp (W : list ivl) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (hi <= SH_LO \/ SH_HI <= lo) /\ app_fp W'
  end.

(* [comment removed for export] *)

Lemma shad_range : forall x, 0 <= x < 2^47 -> SH_LO <= x / 8 + 2147450880 < SH_HI.
Proof. intros x Hx. unfold SH_LO, SH_HI. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
Definition sanchor (X SHX : Z) : Prop := X mod 8 = 0 /\ SHX = X / 8 + 2147450880.

Lemma sanchor_addr : forall X SHX o, sanchor X SHX -> (X + o) / 8 + 2147450880 = SHX + o / 8.
Proof.
  intros X SHX o [A E]. subst SHX.
  assert (EX : X = 8 * (X / 8)) by (pose proof (Z.div_mod X 8 ltac:(lia)); lia).
  rewrite EX at 1. replace (8 * (X / 8) + o) with (o + (X / 8) * 8) by lia. rewrite Z.div_add by lia. lia.
Qed.
Lemma sanchor_addr0 : forall X SHX, sanchor X SHX -> X / 8 + 2147450880 = SHX.
Proof. intros X SHX [_ E]. symmetry. exact E. Qed.
Lemma sanchor_addr_lit : forall X SHX o q, sanchor X SHX -> o / 8 = q -> (X + o) / 8 + 2147450880 = SHX + q.
Proof. intros X SHX o q A E. rewrite (sanchor_addr X SHX o A), E. reflexivity. Qed.
Lemma sanchor_intro : forall X, X mod 8 = 0 -> sanchor X (X / 8 + 2147450880).
Proof. intros X H. split; [exact H| reflexivity]. Qed.

(* [comment removed for export] *)
Lemma sanchor_half_lit : forall X SHX o q, sanchor X SHX -> o / 8 - 2147450880 = q -> (X + o) / 8 = SHX + q.
Proof. intros X SHX o q A E. pose proof (sanchor_addr X SHX o A). lia. Qed.
Lemma sanchor_half0 : forall X SHX, sanchor X SHX -> X / 8 = SHX + -2147450880.
Proof. intros X SHX A. pose proof (sanchor_addr0 X SHX A). lia. Qed.
Lemma zadd_lit_fold : forall s a b c : Z, a + b = c -> s + a + b = s + c.
Proof. intros. lia. Qed.

(* [comment removed for export] *)
Definition saddr (X SHX : Z) : Prop := SHX = X / 8 + 2147450880.
Lemma saddr_intro : forall X, saddr X (X / 8 + 2147450880).
Proof. intros X. reflexivity. Qed.
Lemma saddr_addr0 : forall X SHX, saddr X SHX -> X / 8 + 2147450880 = SHX.
Proof. intros X SHX E. symmetry. exact E. Qed.

(* [comment removed for export] *)
Lemma sxb_z8 : sxb z8 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma zxb_z8 : zxb z8 = Z_to_bv 64 0. Proof. reflexivity. Qed.

Lemma byte_zero : forall b : byte, bv_unsigned b = 0 -> b = z8.
Proof. intros b H. apply bv_eq. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sxb_small : forall b : byte, 0 <= bv_unsigned b < 128 -> sxb b = Z_to_bv 64 (bv_unsigned b).
Proof.
  intros b H. unfold sxb. f_equal. unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 8) with 8. change (2 ^ 8) with 256. change (256 / 2) with 128.
  rewrite Z.mod_small by lia. lia.
Qed.

Section Kit.
Variable segs : list Segment.

Lemma bytes_at1_read : forall (m : amem) a b, bytes_at segs m a [b] -> ov_read_bytes segs m (Z_to_bv 64 a) 1 = Some [b].
Proof.
  intros m a b H. pose proof (bytes_at_read segs m a [b] 0 1 H ltac:(lia) ltac:(cbn; lia)) as R.
  replace (a + 0) with a in R by lia. exact R.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma acc_byte0 : forall (m : amem) a n x,
  acc segs m a n -> a <= x -> 8 * (x / 8) + 8 <= a + n -> bytes_at segs m (shad x) [z8].
Proof.
  intros m a n x H Hx Hg.
  set (y := 8 * (x / 8) + 7).
  assert (Hy : x <= y) by (subst y; pose proof (Z.div_mod x 8 ltac:(lia)); pose proof (Z.mod_pos_bound x 8 ltac:(lia)); lia).
  destruct (H (y - a) ltac:(lia)) as (b & Hb & Hok). replace (a + (y - a)) with y in * by lia.
  assert (Ey : shad y = shad x).
  { unfold shad. f_equal. subst y. replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (My : y mod 8 = 7).
  { subst y. replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
  rewrite Ey in Hb. destruct Hok as [H0 | [Hr Hm]]; [| lia].
  rewrite (byte_zero b H0) in Hb. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma acc_check : forall (m : amem) a n x s,
  acc segs m a n -> a <= x -> x + s <= a + n -> 0 < s <= 8 ->
  exists b, bytes_at segs m (shad x) [b] /\
            (bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ x mod 8 + s - 1 < bv_unsigned b)).
Proof.
  intros m a n x s H Hx Hs Hsz.
  destruct (H (x - a) ltac:(lia)) as (b & Hb & Hok). replace (a + (x - a)) with x in * by lia.
  exists b. split; [exact Hb|].
  destruct Hok as [H0 | [Hr Hm]]; [left; exact H0|].
  destruct (Z_lt_dec (x mod 8 + s - 1) 8) as [Hin | Hout].
  - (* [comment removed for export] *)
    destruct (H (x + s - 1 - a) ltac:(lia)) as (b' & Hb' & Hok'). replace (a + (x + s - 1 - a)) with (x + s - 1) in * by lia.
    assert (Es : shad (x + s - 1) = shad x).
    { unfold shad. f_equal. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
      symmetry. apply (Z.div_unique (x + s - 1) 8 (x / 8) (x mod 8 + s - 1)); lia. }
    assert (Ms : (x + s - 1) mod 8 = x mod 8 + s - 1).
    { pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
      symmetry. apply (Z.mod_unique (x + s - 1) 8 (x / 8) (x mod 8 + s - 1)); lia. }
    rewrite Es in Hb'.
    assert (Eb : b' = b).
    { destruct Hb as (_ & _ & R). destruct Hb' as (_ & _ & R'). specialize (R 0%nat ltac:(cbn; lia)). specialize (R' 0%nat ltac:(cbn; lia)).
      cbn in R, R'. rewrite R in R'. congruence. }
    subst b'. destruct Hok' as [H0' | [_ Hm']]; [left; exact H0'| right; split; [exact Hr| lia]].
  - (* [comment removed for export] *)
    left. set (y := 8 * (x / 8) + 7).
    pose proof (Z.div_mod x 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as MB.
    destruct (H (y - a) ltac:(subst y; lia)) as (b' & Hb' & Hok'). replace (a + (y - a)) with y in * by lia.
    assert (Ey : shad y = shad x).
    { unfold shad. f_equal. subst y. replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
    assert (My : y mod 8 = 7).
    { subst y. replace (8 * (x / 8) + 7) with (7 + (x / 8) * 8) by lia. rewrite Z.mod_add by lia. reflexivity. }
    rewrite Ey in Hb'.
    assert (Eb : b' = b).
    { destruct Hb as (_ & _ & R). destruct Hb' as (_ & _ & R'). specialize (R 0%nat ltac:(cbn; lia)). specialize (R' 0%nat ltac:(cbn; lia)).
      cbn in R, R'. rewrite R in R'. congruence. }
    subst b'. destruct Hok' as [H0' | [_ Hm']]; [exact H0'| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition shzW (W : list ivl) (m0 : amem) (lo hi : Z) : Prop :=
  forall (m : amem) (x : Z), munch W m0 m -> lo <= x < hi ->
    ov_read_bytes segs m (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [z8].

(* [comment removed for export] *)
Definition shpW (W : list ivl) (m0 : amem) (lo hi : Z) : Prop :=
  forall (m : amem) (x s : Z), munch W m0 m -> lo <= x -> x + s <= hi -> 0 < s <= 8 ->
    exists b, ov_read_bytes segs m (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [b] /\
              (bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ x mod 8 + s - 1 < bv_unsigned b)).

Lemma munch_shadow_read : forall W (m0 m : amem) x b,
  app_fp W -> munch W m0 m -> 0 <= x < 2^47 -> bytes_at segs m0 (shad x) [b] ->
  ov_read_bytes segs m (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [b].
Proof.
  intros W m0 m x b AF MU Hx Hb. apply bytes_at1_read.
  apply (bytes_at_transport segs W m0 m _ _ Hb MU).
  cbn [length]. change (Z.of_nat 1) with 1. unfold shad, SHB.
  pose proof (shad_range x Hx) as R.
  clear - AF R. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  cbn in AF. destruct AF as [A1 A2]. split; [lia| exact (IH A2)].
Qed.

(* [comment removed for export] *)
Lemma shzW_of_acc : forall W (m0 : amem) a n lo hi,
  acc segs m0 a n -> app_fp W -> 0 <= a -> a + n <= 2^47 ->
  a <= lo -> 8 * ((hi + 7) / 8) <= a + n -> shzW W m0 lo hi.
Proof.
  intros W m0 a n lo hi H AF Ha Hn Hlo Hhi m x MU Hx.
  apply (munch_shadow_read W m0 m x z8 AF MU); [lia|].
  apply (acc_byte0 m0 a n x H); [lia|].
  assert (x / 8 <= (hi + 7) / 8 - 1).
  { assert (x / 8 < (hi + 7) / 8); [| lia].
    apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.div_mod (hi + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (hi + 7) 8 ltac:(lia)). lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma shpW_of_acc : forall W (m0 : amem) a n,
  acc segs m0 a n -> app_fp W -> 0 <= a -> a + n <= 2^47 -> shpW W m0 a (a + n).
Proof.
  intros W m0 a n H AF Ha Hn m x s MU Hx Hs Hsz.
  destruct (acc_check m0 a n x s H Hx Hs Hsz) as (b & Hb & Hok).
  exists b. split; [| exact Hok].
  apply (munch_shadow_read W m0 m x b AF MU); [lia| exact Hb].
Qed.

(* [comment removed for export] *)
Lemma sh_of_ushadow : forall W (m0 : amem) X N,
  bytes_at segs m0 (shad X) (ushadow N) -> X mod 8 = 0 -> 0 <= X -> 0 <= N -> X + N <= 2^47 -> app_fp W ->
  shzW W m0 X (X + 8 * (N / 8)) /\ shpW W m0 X (X + N).
Proof.
  intros W m0 X N HB HX H0 HN HT AF.
  pose proof (acc_ushadow segs m0 X N HX H0 HN HB) as ACC.
  split; [| exact (shpW_of_acc W m0 X N ACC AF H0 HT)].
  apply (shzW_of_acc W m0 X N X (X + 8 * (N / 8)) ACC AF H0 HT); [lia|].
  assert (E : (X + 8 * (N / 8) + 7) / 8 = X / 8 + N / 8).
  { assert (EX : X = 8 * (X / 8)) by (pose proof (Z.div_mod X 8 ltac:(lia)); lia).
    rewrite EX at 1. replace (8 * (X / 8) + 8 * (N / 8) + 7) with (7 + (X / 8 + N / 8) * 8) by lia.
    rewrite Z.div_add by lia. reflexivity. }
  rewrite E. pose proof (Z.div_mod X 8 ltac:(lia)). pose proof (Z.div_mod N 8 ltac:(lia)). pose proof (Z.mod_pos_bound N 8 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma shzW_sub : forall W W' (m0 m1 : amem) lo hi lo' hi',
  shzW W m0 lo hi -> munch W m0 m1 -> sub_fp W' W -> lo <= lo' -> hi' <= hi -> shzW W' m1 lo' hi'.
Proof.
  intros W W' m0 m1 lo hi lo' hi' H MU SF Hlo Hhi m x MU' Hx.
  apply H; [| lia]. apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.
Lemma shpW_sub : forall W W' (m0 m1 : amem) lo hi lo' hi',
  shpW W m0 lo hi -> munch W m0 m1 -> sub_fp W' W -> lo <= lo' -> hi' <= hi -> shpW W' m1 lo' hi'.
Proof.
  intros W W' m0 m1 lo hi lo' hi' H MU SF Hlo Hhi m x s MU' Hx Hs Hsz.
  apply H; [| lia | lia | lia]. apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU').
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma shzW_anchor : forall W (m0 m : amem) lo hi X SHX q,
  shzW W m0 lo hi -> sanchor X SHX -> munch W m0 m -> lo <= X + 8 * q -> X + 8 * q < hi ->
  ov_read_bytes segs m (Z_to_bv 64 (SHX + q)) 1 = Some [z8].
Proof.
  intros W m0 m lo hi X SHX q H A MU H1 H2.
  pose proof (H m (X + 8 * q) MU ltac:(lia)) as R.
  rewrite (sanchor_addr X SHX (8 * q) A) in R. replace (8 * q / 8) with q in R; [exact R|].
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Lemma shzW_saddr : forall W (m0 m : amem) lo hi X SHX,
  shzW W m0 lo hi -> saddr X SHX -> munch W m0 m -> lo <= X -> X < hi ->
  ov_read_bytes segs m (Z_to_bv 64 SHX) 1 = Some [z8].
Proof.
  intros W m0 m lo hi X SHX H A MU H1 H2. pose proof (H m X MU ltac:(lia)) as R.
  rewrite (saddr_addr0 X SHX A) in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma shpW_rd : forall W (m0 m : amem) lo hi x s,
  shpW W m0 lo hi -> munch W m0 m -> lo <= x -> x + s <= hi -> 0 < s <= 8 ->
  exists b, ov_read_bytes segs m (Z_to_bv 64 (x / 8 + 2147450880)) 1 = Some [b] /\
            (bv_unsigned b = 0 \/ (0 < bv_unsigned b < 8 /\ x mod 8 + s - 1 < bv_unsigned b)).
Proof. intros W m0 m lo hi x s H MU H1 H2 H3. exact (H m x s MU H1 H2 H3). Qed.

End Kit.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lts_small : forall u k, 0 <= u < 2^63 -> 0 <= k < 2^63 -> bv_lts (Z_to_bv 64 u) (Z_to_bv 64 k) = (u <? k).
Proof.
  intros u k Hu Hk. unfold bv_lts. rewrite !signed_lit_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition akey (p base : Z) : Prop := True.
(* [comment removed for export] *)
Ltac az_base0 e :=
  lazymatch e with
  | Z.add ?a _ => az_base0 a
  | Z.sub ?a _ => az_base0 a
  | _ => e
  end.
Ltac az_base e :=
  let k := az_base0 e in
  lazymatch goal with
  | _ : akey k ?b |- _ => b
  | _ => k
  end.

(* [comment removed for export] *)
Ltac asan_range_tac := lia.
Ltac asan_shz_load :=
  lazymatch goal with
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 (?x / 8 + 2147450880)) 1] =>
      let kx := az_base x in
      first
      [ match goal with
        | SH : shzW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
            let kl := az_base0 lo in constr_eq kx kl;
            first [ rewrite (SH m x MU ltac:(asan_range_tac))
                  | fail 2 "asan: cannot prove that" x "lies in the region" lo hi ]
        end
      | match goal with
        | SH : shzW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
            rewrite (SH m x MU ltac:(asan_range_tac))
        end ]
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 (?SHX + ?q)) 1] =>
      match goal with
      | A : sanchor ?X SHX, SH : shzW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
          let kx := az_base X in let kl := az_base0 lo in constr_eq kx kl;
          rewrite (shzW_anchor segs W m0 m lo hi X SHX q SH A MU ltac:(asan_range_tac) ltac:(asan_range_tac))
      end
  | |- context [ov_read_bytes ?segs ?m (Z_to_bv 64 ?SHX) 1] =>
      match goal with
      | A : saddr ?X SHX, SH : shzW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
          let kx := az_base X in let kl := az_base0 lo in constr_eq kx kl;
          rewrite (shzW_saddr segs W m0 m lo hi X SHX SH A MU ltac:(asan_range_tac) ltac:(asan_range_tac))
      end
  end;
  load_post; rewrite ?sxb_z8, ?zxb_z8.

(* [comment removed for export] *)
Ltac a_chunk_has A cs0 E n :=
  is_Zlit A;
  let ok := eval vm_compute in (andb (Z.leb A E) (Z.leb (E - A + Z.of_nat n) (Z.of_nat (cells_size cs0)))) in
  lazymatch ok with true => idtac | _ => fail "not this chunk" end.
Ltac asan_lit_load :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := Lib.Step.addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        a_chunk_has A cs0 E n;
        let kn := eval vm_compute in (Z.to_nat (E - A)) in
        Lib.Step.split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := Lib.Step.eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [Lib.Step.cells_cbv; reflexivity | reflexivity | Lib.Step.addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        a_chunk_has A cs0 E n;
        let kn := eval vm_compute in (Z.to_nat (E - A)) in
        Lib.Step.split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := Lib.Step.eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [Lib.Step.cells_cbv; reflexivity | reflexivity | Lib.Step.addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs) by (rewrite <- HR; f_equal; Lib.ZBridge.word_eq_tac) ]
    end
  end;
  load_post.

(* [comment removed for export] *)
Ltac asan_solve_load :=
  lazymatch goal with
  | |- context [ov_read_bytes _ _ ?a _] =>
      let E := Lib.Step.addr_expr a in
      lazymatch E with
      | Z0 => asan_lit_load
      | Zpos _ => asan_lit_load
      | Zneg _ => asan_lit_load
      | _ => first [ Lib.Step.solve_load_base | asan_shz_load ]
      end
  end.

(* [comment removed for export] *)
Ltac a_lit_branch :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
      let c' := eval vm_compute in c in
      lazymatch c' with
      | true => change c with true; cbv iota
      | false => change c with false; cbv iota
      end
  end.

(* [comment removed for export] *)
Ltac a_closed_cond c :=
  lazymatch c with
  | negb ?c1 => a_closed_cond c1
  | bv_eqb (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_ltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  | bv_lts (Z_to_bv 64 ?a) (Z_to_bv 64 ?b) => is_Zlit a; is_Zlit b
  end.
Ltac a_try_lit_branch :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => first [ a_closed_cond c; a_lit_branch | idtac ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac a_at_pc p :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq p q
  end.
Ltac a_pc_is_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => is_Zlit q
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac a_norm := idtac.
Ltac astep := wstep; a_norm; a_try_lit_branch.
Ltac arun_to p :=
  first [ a_at_pc p
        | a_pc_is_lit; astep; arun_to p
        | fail 1 "arun_to: stopped at an open branch / non-literal pc before reaching" p ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac a_sub_fp :=
  unfold sub_fp; cbn [outside]; let x := fresh "x" in let Ho := fresh "Ho" in intros x Ho; repeat split; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac sh_norm :=
  repeat match goal with
  | A : sanchor ?X ?SHX |- context [(?X + ?o) / 8 + 2147450880] =>
      is_Zlit o; let q := eval vm_compute in (o / 8)%Z in
      rewrite (sanchor_addr_lit X SHX o q A eq_refl)
  | A : sanchor ?X ?SHX |- context [?X / 8 + 2147450880] => rewrite (sanchor_addr0 X SHX A)
  | A : saddr ?X ?SHX |- context [?X / 8 + 2147450880] => rewrite (saddr_addr0 X SHX A)
  | A : sanchor ?X ?SHX |- context [(?X + ?o) / 8] =>
      is_Zlit o; let q := eval vm_compute in (o / 8 - 2147450880)%Z in
      rewrite (sanchor_half_lit X SHX o q A eq_refl)
  | A : sanchor ?X ?SHX |- context [?X / 8] => rewrite (sanchor_half0 X SHX A)
  end.
(* [comment removed for export] *)
Ltac sh_fold :=
  repeat match goal with
  | A : sanchor _ ?SHX |- context [?SHX + ?a + ?b] =>
      is_Zlit a; is_Zlit b; let c := eval vm_compute in (a + b)%Z in
      rewrite (zadd_lit_fold SHX a b c eq_refl)
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ack_rd x s :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
      let kx := az_base x in
      first
      [ match goal with
        | SH : shpW segs ?W ?m0 ?lo ?hi, MU : munch ?W ?m0 m |- _ =>
            let kl := az_base lo in constr_eq kx kl;
            let b := fresh "shb" in let RD := fresh "RDsh" in let OK := fresh "OKsh" in
            destruct (shpW_rd segs W m0 m lo hi x s SH MU ltac:(lia) ltac:(lia) ltac:(lia)) as (b & RD & OK);
            wstep; clear RD
        end
      | fail 1 "ack_rd: no shpW region fact / munch for" x ]
  end.

(* [comment removed for export] *)
Ltac a_reg_val R n :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 n)) in
  eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => (Z_to_bv 64 0) end).

(* [comment removed for export] *)
Ltac a_diff_regs R1 R2 :=
  let rec go n acc :=
    lazymatch n with
    | 0%Z => acc
    | _ => let v1 := a_reg_val R1 n in let v2 := a_reg_val R2 n in
           let n' := eval vm_compute in (n - 1)%Z in
           lazymatch v1 with
           | v2 => go n' acc
           | _ => go n' constr:(n :: acc)
           end
    end in
  go 31%Z constr:(@nil Z).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac a_slow_branch :=
  zb_masks;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      lazymatch c with
      | context [bv_lts (Z_to_bv 64 ?u) (Z_to_bv 64 ?k)] =>
          rewrite (lts_small u k) by lia;
          replace (u <? k) with true by (symmetry; apply Z.ltb_lt; lia);
          cbv beta iota delta [negb]
      end
  end.
Ltac a_slow_run back :=
  first [ a_at_pc back
        | lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end;
          first [ a_slow_branch | notrap ]; a_slow_run back
        | a_pc_is_lit; wstep; a_slow_run back
        | fail 1 "ack_merge: slow path stuck before the merge pc" back ].

Ltac ack_merge_at_branch :=
  lazymatch goal with
  | OK : bv_unsigned ?shb = 0 \/ _ |- evt ?segs ?Q (MS ?R ?F (if ?c then ?pa else ?pb) ?fc ?rv ?m ?ro) =>
      (* [comment removed for export] *)
      let cf := eval pattern shb in c in
      let c0 := lazymatch cf with ?f _ => eval cbv beta in (f z8) end in
      let c0v := eval vm_compute in c0 in
      let back := lazymatch c0v with true => pa | false => pb end in
      let Rm := fresh "Rm" in evar (Rm : word -> word -> bvmap 5 word);
      let CONT := fresh "CONT" in
      cut (forall v1 v2 : word, evt segs Q (MS (Rm v1 v2) F back fc rv m ro));
      [ intro CONT;
        let OKr := fresh "OKr" in let OKl := fresh "OKl" in
        destruct OK as [OK | [OKr OKl]];
        [ idtac
        | (* [comment removed for export] *)
          rewrite (sxb_small shb) by lia;
          let kb := fresh "kb" in
          set (kb := bv_unsigned shb) in *; clearbody kb;
          notrap;
          let backz := lazymatch back with Z_to_bv 64 ?q => q end in
          a_slow_run backz;
          lazymatch goal with
          | |- evt _ _ (MS ?Rs _ _ _ _ _ _) =>
              let ds := a_diff_regs Rs R in
              lazymatch ds with
              | (?d1 :: nil)%list =>
                  let p1 := eval vm_compute in (bv_key (Z_to_bv 5 d1)) in
                  let f := eval cbv beta iota delta [tset mkR] in (fun (v1 v2 : word) => tset p1 v1 R) in
                  let e := eval unfold Rm in Rm in unify e f;
                  let x1 := a_reg_val Rs d1 in
                  exact (CONT x1 (Z_to_bv 64 0))
              | (?d1 :: ?d2 :: nil)%list =>
                  let p1 := eval vm_compute in (bv_key (Z_to_bv 5 d1)) in
                  let p2 := eval vm_compute in (bv_key (Z_to_bv 5 d2)) in
                  let f := eval cbv beta iota delta [tset mkR] in (fun (v1 v2 : word) => tset p1 v1 (tset p2 v2 R)) in
                  let e := eval unfold Rm in Rm in unify e f;
                  let x1 := a_reg_val Rs d1 in let x2 := a_reg_val Rs d2 in
                  exact (CONT x1 x2)
              | _ => fail 1 "ack_merge: the slow path changed more than two registers:" ds
              end
          end ];
        (* [comment removed for export] *)
        let E := fresh "Esh" in
        pose proof (byte_zero shb OK) as E; subst shb;
        rewrite ?sxb_z8; a_lit_branch;
        first [ exact (CONT (Z_to_bv 64 0) (Z_to_bv 64 0)) | eapply CONT ]
      | let shk := fresh "shk" in let shu := fresh "shu" in
        intros shk shu; subst Rm; cbv beta; clear OK; try clear shb ]
  | _ => fail "ack_merge: no open partial-granule reader (OKsh) / goal not at a branch"
  end.

(* [comment removed for export] *)
Ltac ack_merge := try (a_pc_is_lit; wstep); ack_merge_at_branch.

(* [comment removed for export] *)
Ltac a_zstep_nofb := ltac2:(Control.enter (fun () => Control.once (fun () => StepFast.sf_step true))).
Ltac astep_nf := a_zstep_nofb; bz32; a_norm; a_try_lit_branch.
Ltac arun :=
  first [ a_pc_is_lit; astep_nf; arun
        | lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "arun: stopped at" pc end ].
