(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg StoreOk LibWritev RefMemcpyLib.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Cli Require Import CliSpecG.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie ExBytes.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxLazy AxLin AxRel AxVal AxBytes AxMem AxMemC AxZZ AxBg AxState AxStep AxSys AxJoin AxJoinSound AxEntryRel AxEntryAg AsanWLazy AsanWBase AsanSBase AsanWEntry AsanWEb AsanWEbLoad AsanWWritev AsanWSw AsanWStdio AxSum AsanSRipA AsanSCode AxWordsInt AxTabs.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxModelRel AxFd AxFinal AxSumLibc AxSumStr AxSumMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition is_strbyte (x : xb) : option (Z * Z) :=
  match x with
  | BF [(v, c)] o O =>
      let q := to_Z v - 1099511627776 in
      if (c =? 1) &&& w_eqb o w_zero &&& (0 <=? q) &&& (q <? 137438953472) then Some (q / 131072, q mod 131072) else None
  | _ => None
  end.

Lemma is_strbyte_inv (x : xb) (k j : Z) : is_strbyte x = Some (k, j) ->
  x = BF [(strvar k j, 1)] w_zero 0 /\ 0 <= k < 1048576 /\ 0 <= j < 131072.
Proof.
  unfold is_strbyte. destruct x as [| |ts o i]; try discriminate. destruct ts as [|[v c] [|]]; try discriminate.
  destruct i; [|discriminate]. cbv zeta.
  destruct (c =? 1) eqn:Ec; [|discriminate]. destruct (w_eqb o w_zero) eqn:Eo; [|discriminate].
  destruct (0 <=? to_Z v - 1099511627776) eqn:E0; [|discriminate]. destruct (to_Z v - 1099511627776 <? 137438953472) eqn:E1; [|discriminate].
  intros H. injection H as <- <-. apply Z.eqb_eq in Ec. apply w_eqb_eq in Eo. apply Z.leb_le in E0. apply Z.ltb_lt in E1. subst c o.
  set (q := to_Z v - 1099511627776) in *.
  pose proof (Z.div_mod q 131072 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound q 131072 ltac:(lia)) as Hm.
  assert (Hk : 0 <= q / 131072 < 1048576) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  split; [|split; [exact Hk | exact Hm]].
  f_equal. f_equal. f_equal. unfold strvar. change (2 ^ 40) with 1099511627776. change (2 ^ 17) with 131072.
  replace (1099511627776 + q / 131072 * 131072 + q mod 131072) with (to_Z v) by (unfold q in *; lia).
  symmetry. apply of_to_Z.
Qed.

(* [comment removed for export] *)
Lemma strbyte_val (ρ : valuation) (k j : Z) (y : byte) :
  xb_z ρ (BF [(strvar k j, 1)] w_zero 0) (bv_unsigned y) -> y = Z_to_bv 8 (ρ (strvar k j)).
Proof.
  cbn [xb_z]. unfold smod, zbyte. cbn [teval]. change (wZ w_zero) with 0. change (2 ^ (8 * Z.of_nat 0)) with 1.
  rewrite Z.div_1_r. intros H. apply bv_eq. rewrite H, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  replace (1 * ρ (strvar k j) + 0 + 0) with (ρ (strvar k j)) by ring.
  unfold two64. change 18446744073709551616 with (256 * 72057594037927936).
  rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

(* [comment removed for export] *)
Fixpoint take_run (k j : Z) (n : nat) (l : list piece) : option (list piece) :=
  match n with
  | O => Some l
  | S n' =>
      match l with
      | PB x :: r =>
          match is_strbyte x with
          | Some (k', j') => if (k' =? k) &&& (j' =? j) then take_run k (j + 1) n' r else None
          | None => None
          end
      | _ => None
      end
  end.

Lemma take_run_sound (ρ : valuation) (k : Z) : forall (n : nat) (j : Z) (l rest : list piece) (o : list byte),
  take_run k j n l = Some rest -> pieces_val ρ l o ->
  exists o', o = map (fun i => Z_to_bv 8 (ρ (strvar k (j + Z.of_nat i)))) (seq 0 n) ++ o' /\ pieces_val ρ rest o'.
Proof.
  induction n as [|n IH]; intros j l rest o H Hv.
  - injection H as <-. exists o. split; [reflexivity | exact Hv].
  - cbn [take_run] in H. destruct l as [|[x|k0] r]; try discriminate.
    destruct (is_strbyte x) as [[k' j']|] eqn:Ex; [|discriminate].
    destruct (k' =? k) eqn:Ek; [|discriminate]. destruct (j' =? j) eqn:Ej; [|discriminate].
    apply Z.eqb_eq in Ek. apply Z.eqb_eq in Ej. subst k' j'.
    destruct (is_strbyte_inv x k j Ex) as [-> _].
    cbn [pieces_val] in Hv. destruct Hv as (y & o1 & -> & Hy & Hr).
    destruct (IH (j + 1) r rest o1 H Hr) as (o' & -> & Hrest). exists o'. split; [|exact Hrest].
    cbn [seq map app]. rewrite (strbyte_val ρ k j y Hy). rewrite Z.add_0_r. f_equal. f_equal.
    rewrite <- seq_shift, map_map. apply map_ext. intros i. f_equal. f_equal. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition try_run (s : store) (l : list piece) : option (Z * list piece) :=
  match l with
  | PB x :: _ =>
      match is_strbyte x with
      | Some (k, 0) =>
          match lrange s (lvar (lenvar k) 1) with
          | Some (lo, hi) =>
              if (lo =? hi) &&& (1 <=? lo) &&& (lo <? 131072) then
                match take_run k 0 (Z.to_nat lo) l with Some rest => Some (k, rest) | None => None end
              else None
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Lemma try_run_sound (ρ : valuation) (s : store) (l rest : list piece) (k : Z) (o : list byte) :
  sat ρ s -> try_run s l = Some (k, rest) -> pieces_val ρ l o -> pieces_val ρ (PS k :: rest) o /\ (length rest < length l)%nat.
Proof.
  intros Hs H Hv. unfold try_run in H. destruct l as [|[x|k0] r]; try discriminate.
  destruct (is_strbyte x) as [[k' j']|] eqn:Ex; [|discriminate]. destruct j'; try discriminate.
  destruct (lrange s (lvar (lenvar k') 1)) as [[lo hi]|] eqn:El; [|discriminate].
  destruct (lo =? hi) eqn:E1; [|discriminate]. destruct (1 <=? lo) eqn:E2; [|discriminate]. destruct (lo <? 131072) eqn:E3; [|discriminate].
  destruct (take_run k' 0 (Z.to_nat lo) (PB x :: r)) as [rest'|] eqn:Et; [|discriminate]. injection H as <- <-.
  apply Z.eqb_eq in E1. apply Z.leb_le in E2. apply Z.ltb_lt in E3. subst hi.
  pose proof (lrange_sound ρ s _ Hs _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X.
  assert (Hlen : ρ (lenvar k') = lo) by lia.
  destruct (is_strbyte_inv x k' 0 Ex) as (_ & Hk & _).
  split.
  - destruct (take_run_sound ρ k' (Z.to_nat lo) 0 _ _ o Et Hv) as (o' & -> & Hrest).
    cbn [pieces_val]. exists o'. split; [|exact Hrest]. f_equal. unfold dec_str.
    replace ((0 <=? k') && (k' <? 1048576)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite Hlen, Z.mod_small by lia. reflexivity.
  - clear - Et E2. assert (Hn : (1 <= Z.to_nat lo)%nat) by lia. revert Et Hn. generalize (Z.to_nat lo) as n. generalize 0 as j.
    assert (G : forall n j (l rest : list piece), take_run k' j n l = Some rest -> (length rest + n <= length l)%nat).
    { induction n as [|n IH]; intros j l rest H; [injection H as <-; lia|]. cbn [take_run] in H.
      destruct l as [|[x0|k0] r0]; try discriminate. destruct (is_strbyte x0) as [[k1 j1]|]; [|discriminate].
      destruct ((k1 =? k') &&& (j1 =? j)); [|discriminate]. specialize (IH _ _ _ H). cbn [length]. lia. }
    intros j n Et Hn. specialize (G _ _ _ _ Et). lia.
Qed.

(* [comment removed for export] *)
Fixpoint norm (s : store) (fuel : nat) (l : list piece) : list piece :=
  match fuel with
  | O => l
  | S f =>
      match l with
      | [] => []
      | p :: r => match try_run s l with Some (k, rest) => PS k :: norm s f rest | None => p :: norm s f r end
      end
  end.

Lemma norm_sound (ρ : valuation) (s : store) : sat ρ s -> forall (fuel : nat) (l : list piece) (o : list byte),
  pieces_val ρ l o -> pieces_val ρ (norm s fuel l) o.
Proof.
  intros Hs. induction fuel as [|f IH]; intros l o Hv; [exact Hv|]. cbn [norm]. destruct l as [|p r]; [exact Hv|].
  destruct (try_run s (p :: r)) as [[k rest]|] eqn:Et.
  - destruct (try_run_sound ρ s _ _ _ o Hs Et Hv) as [Hv' _]. cbn [pieces_val] in *. destruct Hv' as (o' & -> & Hr).
    exists o'. split; [reflexivity | exact (IH rest o' Hr)].
  - destruct p as [x|k]; cbn [pieces_val] in *.
    + destruct Hv as (y & o1 & -> & Hy & Hr). exists y, o1. split; [reflexivity|]. split; [exact Hy | exact (IH r o1 Hr)].
    + destruct Hv as (o1 & -> & Hr). exists o1. split; [reflexivity | exact (IH r o1 Hr)].
Qed.

(* [comment removed for export] *)
Definition with_out (am : amodel) (o : list piece) : amodel :=
  AM (am_maps am) (am_brk0 am) (am_brk am) (am_tid am) (am_shadow am) (am_next am) (am_atop am) o (am_exp am) (am_fd am).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma le8_word (bs : list byte) : length bs = 8%nat -> word_to_le_bytes 8 (load_word SZ8 false bs) = bs.
Proof.
  intros Hl. unfold load_word, le_bytes_to_word. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb.
  pose proof (bytes_le_to_Z_nonneg bs) as Hb0.
  rewrite bv_extract_unsigned, Z.shiftr_0_r, Z_to_bv_unsigned. rewrite !bv_wrap64_mod, Z.mod_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Inductive ioent : Type := EL (l : list xb) | ES (k : Z).

Definition e_pieces (e : ioent) : list piece := match e with EL l => map PB l | ES k => [PS k] end.
Definition e_len (e : ioent) : lin := match e with EL l => (Z.of_nat (length l), []) | ES k => (0, t_len k) end.
Definition e_lo (s : store) (e : ioent) : Z :=
  match e with
  | EL l => Z.of_nat (length l)
  | ES k => match lrange s (lvar (lenvar k) 1) with Some (lo, _) => Z.max lo 0 | None => 0 end
  end.

Lemma pieces_PB (ρ : valuation) (l : list xb) (bs : list byte) : Forall2 (xb_bv ρ) l bs -> pieces_val ρ (map PB l) bs.
Proof.
  induction 1 as [|x b l bs Hx _ IH]; cbn [map pieces_val]; [reflexivity|]. exists b, bs. split; [reflexivity|]. split; [exact Hx | exact IH].
Qed.

Lemma dec_str_argv (ρ : valuation) (k : Z) : eb_facts ρ -> 0 <= k < ρ v_argc -> dec_str k ρ = nth (Z.to_nat k) (dec_argv ρ) [].
Proof.
  intros HF Hk. pose proof HF as (Hargc & _ & Hstr & _). destruct (Hstr k Hk) as [Hl _].
  unfold dec_str, dec_argv, dec_strs.
  replace ((0 <=? k) && (k <? 1048576)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  rewrite (nth_map_seq0 _ (Z.to_nat (ρ v_argc)) (Z.to_nat k) []) by lia. rewrite Z2Nat.id by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

Section Ent.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

(* [comment removed for export] *)
Definition ent_words (s : store) (A : list region) (viov : xv) (i : Z) : option (xv * xv) :=
  match a_load4 segs s A (xv_off viov (16 * i)) 8, a_load4 segs s A (xv_off viov (16 * i + 8)) 8 with
  | Some l1, Some l2 => Some (val_of_bytes s SZ8 false l1, val_of_bytes s SZ8 false l2)
  | _, _ => None
  end.

Lemma ent_words_sound (ρ : valuation) (s : store) (A : list region) (m : word -> option byte) (viov : xv) (iov : bv 64) (i : Z) (vb vn : xv) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> xv_val ρ viov iov -> xaddr viov <> None -> ent_words s A viov i = Some (vb, vn) ->
  exists b n : word, rdn segs m (Z_to_bv 64 (bv_unsigned iov + 16 * i)) 8 = Some (word_to_le_bytes 8 b)
                  /\ rdn segs m (Z_to_bv 64 (bv_unsigned iov + (16 * i + 8))) 8 = Some (word_to_le_bytes 8 n)
                  /\ xv_val ρ vb b /\ xv_val ρ vn n.
Proof.
  intros Hs HM Hhs Hv Hx H. unfold ent_words in H.
  destruct (a_load4 segs s A (xv_off viov (16 * i)) 8) as [l1|] eqn:E1; [|discriminate].
  destruct (a_load4 segs s A (xv_off viov (16 * i + 8)) 8) as [l2|] eqn:E2; [|discriminate]. injection H as <- <-.
  destruct (a_load4_sound segs ρ s A m _ _ 8 l1 Hlow Hs HM Hhs (xv_off_sound ρ viov iov (16 * i) Hv Hx) ltac:(lia) E1) as [bs1 [Hr1 HF1]].
  destruct (a_load4_sound segs ρ s A m _ _ 8 l2 Hlow Hs HM Hhs (xv_off_sound ρ viov iov (16 * i + 8) Hv Hx) ltac:(lia) E2) as [bs2 [Hr2 HF2]].
  pose proof (rdn_length _ _ _ _ _ Hr1) as L1. pose proof (rdn_length _ _ _ _ _ Hr2) as L2.
  exists (load_word SZ8 false bs1), (load_word SZ8 false bs2).
  rewrite (le8_word bs1 L1), (le8_word bs2 L2). split; [exact Hr1|]. split; [exact Hr2|].
  split; apply val_of_bytes_sound; first [exact Hs | assumption | (rewrite (Forall2_length HF1); exact L1) | (rewrite (Forall2_length HF2); exact L2)].
Qed.

(* [comment removed for export] *)
Definition buf_ok (s : store) (am : amodel) (iovf : lin) (cnt : Z) (tb : terms) (ob : w64) (L : Z) : bool :=
  let bf := (wS ob, tb) in
  rbetween 2 s bf 0 (140737488355328 - L)
  &&& (rprove 2 s (lsub iovf bf) L ||| rprove 2 s (lsub bf iovf) (16 * cnt))
  &&& ((L =? 0) ||| rprove 2 s (lsub bf (am_atop am)) 0 ||| (match tb with [] => in_segn segs (wS ob) L | _ => false end)).

(* [comment removed for export] *)
Definition ent_of (s : store) (A : list region) (am : amodel) (iovf : lin) (cnt : Z) (vb vn : xv) : option ioent :=
  match vn with
  | XL w =>
      let L := wZ w in
      match xaddr vb with
      | Some (tb, ob) =>
          if (L <? 1000) &&& buf_ok s am iovf cnt tb ob L then
            if L =? 0 then Some (EL []) else match mc_load segs s A vb (Z.to_nat L) with Some l => Some (EL l) | None => None end
          else None
      | None => None
      end
  | XS tn on =>
      match str_k s vb with
      | Some k =>
          if teqb tn (t_len k) &&& (wZ on =? 0) then Some (ES k)
          else (* [comment removed for export] *)
            let f := canon_form s tn on in
            if teqb (fst f) (t_len k) &&& (wZ (snd f) =? 0) then Some (ES k) else None
      | None => None
      end
  | _ => None
  end.

(* [comment removed for export] *)
Definition ent_good (ρ : valuation) (s : store) (m : word -> option byte) (model : Model) (iovp cnt : Z) (e : ioent) (b n : word) (bs : list byte) : Prop :=
  rdn segs m b (word_to_nat n) = Some bs /\ bv_unsigned b + bv_unsigned n <= TASK_SIZE
  /\ (bv_unsigned b + bv_unsigned n <= iovp \/ iovp + 16 * cnt <= bv_unsigned b)
  /\ no_lazy model (bv_unsigned b) (bv_unsigned b + bv_unsigned n)
  /\ pieces_val ρ (e_pieces e) bs /\ bv_unsigned n = leval ρ (e_len e) /\ e_lo s e <= bv_unsigned n <= 131071.

Lemma ent_of_sound (fs0 : Fs.Fs) (ρ : valuation) (s : store) (A : list region) (am : amodel) (m : word -> option byte) (model : Model)
    (ph : PhdrInfo) (o : w64) (cnt : Z) (vb vn : xv) (b n : word) (e : ioent) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> MR segs fs0 ρ am model -> find_entry A = Some ph -> atop_is_sp am = true ->
  - 8388608 <= wS o -> wS o + 16 * cnt <= 0 -> 0 <= cnt ->
  xv_val ρ vb b -> xv_val ρ vn n -> ent_of s A am (wS o, sp_terms) cnt vb vn = Some e ->
  exists bs, ent_good ρ s m model (sp_val ρ + wS o) cnt e b n bs.
Proof.
  intros Hs HM Hhs Hmod Efe Eat Ho1 Ho2 Hcnt Hvb Hvn H.
  destruct (eb_of_R segs ρ A m ph HM Efe) as [nR Heb]. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & Hq1 & Hs2). unfold sp_window_lo, sp_window_hi in *.
  pose proof (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat) as Hatop.
  unfold ent_of in H. destruct vn as [w|tn on| | | |]; try discriminate.
  - (* [comment removed for export] *)
    cbv zeta in H. destruct (xaddr vb) as [[tb ob]|] eqn:Ea; [|discriminate].
    destruct (wZ w <? 1000) eqn:EL1; [|discriminate]. destruct (buf_ok s am (wS o, sp_terms) cnt tb ob (wZ w)) eqn:Eok; [|discriminate].
    apply Z.ltb_lt in EL1. cbn [xv_val] in Hvn. pose proof (wZ_range w) as Hw.
    unfold buf_ok in Eok. cbv zeta in Eok. apply land_true in Eok as [Eok Enl]. apply land_true in Eok as [Ebt Edj].
    pose proof (rbetween_sound ρ s 2 _ _ _ Hs Ebt) as Hbr.
    assert (Hbv : bv_unsigned b = leval ρ (wS ob, tb)) by (apply (addr_form_val' ρ vb b tb ob (140737488355328 - wZ w) Hvb Ea Hbr); unfold FastWord.two64; lia).
    assert (Hdj : bv_unsigned b + bv_unsigned n <= sp_val ρ + wS o \/ sp_val ρ + wS o + 16 * cnt <= bv_unsigned b).
    { assert (Eiov : leval ρ (wS o, sp_terms) = sp_val ρ + wS o) by (unfold leval, sp_val; cbn [fst snd]; ring).
      apply lor_true in Edj as [X|X]; pose proof (rprove_sound ρ s 2 _ _ Hs X) as Y; rewrite leval_lsub, Eiov in Y; [left | right]; lia. }
    assert (Hnl : no_lazy model (bv_unsigned b) (bv_unsigned b + bv_unsigned n)).
    { apply lor_true in Enl as [Enl|Enl]; [apply lor_true in Enl as [Enl|Enl]|].
      - apply Z.eqb_eq in Enl. intros p z _ Hz. lia.
      - apply (no_lazy_above segs fs0 ρ am model _ _ Hmod). pose proof (rprove_sound ρ s 2 _ _ Hs Enl) as Y. rewrite leval_lsub in Y.
        rewrite (mr_atop segs fs0 ρ _ _ Hmod). lia.
      - destruct tb; [|discriminate]. rewrite Hvn. replace (bv_unsigned b) with (wS ob) by (rewrite Hbv; unfold leval; cbn [fst snd teval]; lia).
        exact (no_lazy_imgn segs Hlow model _ _ (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) Enl). }
    destruct (wZ w =? 0) eqn:E0.
    + injection H as <-. apply Z.eqb_eq in E0. exists []. unfold ent_good, word_to_nat. rewrite Hvn, E0 in *. cbn [e_pieces e_len e_lo map length pieces_val].
      unfold TASK_SIZE, leval. cbn [fst snd teval Z.of_nat]. repeat split; first [reflexivity | lia | assumption | idtac].
      all: destruct Hdj; lia.
    + apply Z.eqb_neq in E0. destruct (mc_load segs s A vb (Z.to_nat (wZ w))) as [l|] eqn:El; [|discriminate]. injection H as <-.
      assert (Hn1 : (1 <= Z.to_nat (wZ w) < 1000)%nat) by lia.
      destruct (mc_load_sound segs Hlow ρ s A m vb b _ l Hs HM Hhs Hvb ltac:(rewrite Ea; discriminate) Hn1 El) as [bs [Hrd HF2]].
      pose proof (Forall2_length HF2) as Hll. pose proof (rdn_length _ _ _ _ _ Hrd) as Hlb.
      exists bs. unfold ent_good, word_to_nat. rewrite Hvn. cbn [e_pieces e_len e_lo]. unfold TASK_SIZE, leval. cbn [fst snd teval].
      split; [exact Hrd|]. split; [lia|]. split; [rewrite Hvn in Hdj; exact Hdj|]. split; [rewrite Hvn in Hnl; exact Hnl|].
      split; [exact (pieces_PB ρ l bs HF2)|]. lia.
  - (* [comment removed for export] *)
    destruct (str_k s vb) as [k|] eqn:Ek; [|discriminate].
    assert (Hx : e = ES k /\ exists on', wZ on' = 0 /\ bv_unsigned n = smod ρ (t_len k) on').
    { cbn [xv_val] in Hvn. destruct (teqb tn (t_len k) &&& (wZ on =? 0)) eqn:E1.
      - injection H as <-. apply land_true in E1 as [Etn Eon]. apply teqb_eq in Etn. apply Z.eqb_eq in Eon. subst tn.
        split; [reflexivity|]. exists on. split; assumption.
      - cbv zeta in H. destruct (teqb (fst (canon_form s tn on)) (t_len k) &&& (wZ (snd (canon_form s tn on)) =? 0)) eqn:E2; [|discriminate].
        injection H as <-. apply land_true in E2 as [Etn Eon]. apply teqb_eq in Etn. apply Z.eqb_eq in Eon. split; [reflexivity|].
        exists (snd (canon_form s tn on)). split; [exact Eon|]. rewrite <- Etn, (canon_form_sound ρ s tn on Hs). exact Hvn. }
    destruct Hx as [-> [on' [Eon Hvn']]]. clear H Hvn.
    destruct (str_k_sound ρ s vb b k Hs HF Hvb Ek) as [Hk Hba].
    destruct (eb_argvk segs ph ρ m nR k Heb Hk) as [[Hrd Hnf] Hlen]. set (bs := nth (Z.to_nat k) (dec_argv ρ) []) in *.
    assert (Hlk : 0 <= ρ (lenvar k) <= 131071 /\ str_addr ρ k + ρ (lenvar k) + 1 <= sp_val ρ + 184 + 8 * ρ v_argc + 8 * ρ v_envc + 8 * ρ v_q
                  /\ sp_val ρ <= str_addr ρ k /\ 0 <= k < ρ v_argc).
    { unfold str_addr. destruct Hk as [->|[-> H2]]; cbn [Z.eqb]; [lia|]. destruct (Hq1 H2) as [Hl1 Hq1']. lia. }
    destruct Hlk as (Hlk0 & Hlk1 & Hlk2 & Hlk3).
    assert (Hn : bv_unsigned n = ρ (lenvar k)).
    { rewrite Hvn'. unfold smod, t_len. cbn [teval]. rewrite Eon. rewrite Z.mod_small by (unfold FastWord.two64; lia). lia. }
    assert (Eb : b = Z_to_bv 64 (str_addr ρ k)) by (apply word_lit_w; exact Hba).
    exists bs. unfold ent_good, word_to_nat. rewrite Hn, Hba. cbn [e_pieces e_len e_lo]. unfold TASK_SIZE.
    split.
    { rewrite Eb. pose proof (rdn_firstn' segs m _ _ _ (length bs) Hrd ltac:(lia)) as X.
      rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r in X. replace (Z.to_nat (ρ (lenvar k))) with (length bs) by lia. exact X. }
    split; [lia|]. split; [right; lia|].
    split; [apply (no_lazy_above segs fs0 ρ am model _ _ Hmod); rewrite Hatop; lia|].
    split.
    { cbn [pieces_val]. exists []. split; [|reflexivity]. rewrite app_nil_r. symmetry. exact (dec_str_argv ρ k HF Hlk3). }
    split; [unfold leval, t_len; cbn [fst snd teval]; lia|].
    destruct (lrange s (lvar (lenvar k) 1)) as [[lo hi]|] eqn:El; [|lia].
    pose proof (lrange_sound ρ s _ Hs _ El) as X. cbn [fst snd] in X. unfold leval, lvar in X. cbn [fst snd teval] in X. lia.
Qed.

End Ent.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sw_code_ok (segs : list Segment) (b sr : Z) : bool :=
  words_ok_f segs b SW_WORDS &&& words_ok_f segs sr SR_WORDS &&& jal_ok_f segs b 0x8c 1 sr &&& jal_ok_f segs b 0x114 1 sr.

Lemma sw_code_sound (segs : list Segment) (b sr : Z) :
  (0 <= b /\ b + 0x200 <= 2 ^ 47 /\ 0 <= sr /\ sr + 0x40 <= 2 ^ 47 /\ b mod 4 = 0) -> sw_code_ok segs b sr = true ->
  exists (wj1 wj2 : Z) (ij1 ij2 : bv 21), SWCode segs b sr wj1 wj2 ij1 ij2.
Proof.
  intros Hbnd H. unfold sw_code_ok in H. rewrite !jal_ok_f_eq in H.
  apply land_true in H as [H HJ2]. apply land_true in H as [H HJ1]. apply land_true in H as [HW HR].
  apply words_ok_f_eq in HW. apply words_ok_f_eq in HR.
  exact (swcode_ck segs b sr HW HR HJ1 HJ2 Hbnd).
Qed.

(* [comment removed for export] *)
Definition fd2_ok (segs : list Segment) (mem : list region) (f : Z) : bool :=
  match a_load segs mem (XL (wofZ (f + 120))) 4 with
  | Some l => match all_lit l with
              | Some [b0; b1; b2; b3] => (b0 =? 2)%uint63 &&& (b1 =? 0)%uint63 &&& (b2 =? 0)%uint63 &&& (b3 =? 0)%uint63
              | _ => false
              end
  | None => false
  end.

Lemma fd2_ok_sound (segs : list Segment) (ρ : valuation) (A : list region) (m : word -> option byte) (f : Z) :
  RMem segs ρ A m -> 0 <= f + 120 < 2 ^ 64 -> fd2_ok segs A f = true ->
  rdn segs m (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 2)).
Proof.
  intros HM Hf H. unfold fd2_ok in H. destruct (a_load segs A (XL (wofZ (f + 120))) 4) as [l|] eqn:El; [|discriminate].
  destruct (all_lit l) as [[|b0 [|b1 [|b2 [|b3 [|]]]]]|] eqn:Ea; try discriminate.
  apply land_true in H as [H H3]. apply land_true in H as [H H2]. apply land_true in H as [H0 H1].
  apply Uint63.eqb_spec in H0, H1, H2, H3. subst.
  assert (Hv : xv_val ρ (XL (wofZ (f + 120))) (Z_to_bv 64 (f + 120))).
  { cbn [xv_val]. rewrite wZ_wofZ, Z_to_bv_unsigned. reflexivity. }
  destruct (a_load_sound segs ρ A m _ _ 4 l HM Hv ltac:(lia) El) as [bs [Hrd HF]]. rewrite Hrd. f_equal.
  apply all_lit_map in Ea. subst l.
  inversion HF as [|x0 y0 l0 r0 X0 HF0]; subst. inversion HF0 as [|x1 y1 l1 r1 X1 HF1]; subst.
  inversion HF1 as [|x2 y2 l2 r2 X2 HF2]; subst. inversion HF2 as [|x3 y3 l3 r3 X3 HF3]; subst. inversion HF3; subst.
  unfold xb_bv in *. cbn [xb_z] in *.
  assert (G : forall (y : byte) (z : Z), bv_unsigned y = z -> y = Z_to_bv 8 z) by (intros y z <-; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite (G y0 _ X0), (G y1 _ X1), (G y2 _ X2), (G y3 _ X3). reflexivity.
Qed.

(* [comment removed for export] *)
Definition ents_of (segs : list Segment) (s : store) (A : list region) (am : amodel) (iovf : lin) (viov : xv) (cnt : Z) : option (list ioent) :=
  match ent_words segs s A viov 0 with
  | Some (vb, vn) =>
      match ent_of segs s A am iovf cnt vb vn with
      | Some e0 =>
          if cnt =? 1 then Some [e0] else
          match ent_words segs s A viov 1 with
          | Some (vb1, vn1) => match ent_of segs s A am iovf cnt vb1 vn1 with Some e1 => Some [e0; e1] | None => None end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

(* [comment removed for export] *)
Definition total_of (es : list ioent) : option lin :=
  match es with
  | [e] => Some (e_len e)
  | [EL l0; e1] => Some (Z.of_nat (length l0) + fst (e_len e1), snd (e_len e1))
  | [ES k; EL l1] => Some (Z.of_nat (length l1), t_len k)
  | _ => None
  end.

Lemma total_of_val (ρ : valuation) (es : list ioent) (T : lin) : total_of es = Some T ->
  leval ρ T = fold_right (fun e acc => leval ρ (e_len e) + acc) 0 es.
Proof.
  unfold total_of. destruct es as [|e0 [|e1 [|e2 r]]]; try discriminate.
  - destruct e0; intros H; cbv beta iota in H; injection H as <-; cbn [fold_right e_len]; cbv beta; lia.
  - destruct e0 as [l0|k], e1 as [l1|k1]; intros H; cbv beta iota in H; try discriminate H; injection H as <-;
      cbn [fold_right e_len]; cbv beta; unfold leval; cbn [fst snd teval]; lia.
  - destruct e0, e1; discriminate.
Qed.

Definition total_is (v : xv) (T : lin) : bool :=
  match v with
  | XL w => (wZ w =? fst T) &&& (match snd T with [] => true | _ => false end)
  | XS ts o => (wZ o =? fst T) &&& teqb ts (snd T)
  | _ => false
  end.

Lemma total_is_sound (ρ : valuation) (v : xv) (x : word) (T : lin) :
  xv_val ρ v x -> total_is v T = true -> 0 <= leval ρ T < 2 ^ 64 -> bv_unsigned x = leval ρ T.
Proof.
  intros Hv H Hr. unfold total_is in H. destruct v as [w|ts o| | | |]; try discriminate; apply land_true in H as [H1 H2]; apply Z.eqb_eq in H1; cbn [xv_val] in Hv.
  - destruct T as [c [|]]; [|discriminate]. cbn [fst snd] in *. unfold leval. cbn [fst snd teval]. lia.
  - apply teqb_eq in H2. destruct T as [c t]. cbn [fst snd] in *. subst ts. rewrite Hv. unfold smod, leval in *. cbn [fst snd] in *.
    rewrite H1. replace (teval ρ t + c) with (c + teval ρ t) by ring. apply Z.mod_small. unfold FastWord.two64. lia.
Qed.

(* [comment removed for export] *)
Lemma CLOB_nz (r : reg) : In r CLOB -> bv_unsigned r <> 0.
Proof.
  unfold CLOB. cbn [In]. intros H. repeat (destruct H as [<-|H]; [vm_compute; discriminate|]). destruct H.
Qed.

Definition sum_stdio (T : img_tabs) (segs : list Segment) (A : AST) : option (list AST) :=
  let b := wZ (a_pc A) - 0x88 in
  let s := a_facts A in
  let regs := a_regs A in
  match sw_params T b, xlit (aget regs 17%uint63), xlit (aget regs 10%uint63), aget regs 11%uint63,
        xlit (aget regs 12%uint63), xlit (aget regs 18%uint63), xlit (aget regs 9%uint63), find_entry (a_mem A) with
  | Some sr, Some a7, Some fd, XS ts o, Some cnt, Some cnt', Some f, Some ph =>
      if sw_code_ok segs b sr &&& (a7 =? 66) &&& (fd =? 2) &&& teqb ts sp_terms &&& (- 8388608 <=? wS o) &&& (wS o + 16 * cnt <=? 0)
         &&& ((cnt =? 1) ||| (cnt =? 2)) &&& (cnt' =? cnt) &&& xv_eqb (aget regs 19%uint63) (aget regs 11%uint63)
         &&& atop_is_sp (a_model A) &&& (0 <=? f) &&& in_segn segs (f + 120) 4 &&& fd2_ok segs (a_mem A) f
         &&& pc_ok (wofZ (b + 0x94)) then
        match ents_of segs s (a_mem A) (a_model A) (wS o, sp_terms) (XS ts o) cnt with
        | Some es =>
            match total_of es with
            | Some Tt =>
                if total_is (aget regs 22%uint63) Tt &&& (1 <=? fold_right (fun e acc => e_lo s e + acc) 0 es) then
                  match a_store segs (a_mem A) (XS ts o) (repeat BT (Z.to_nat (16 * cnt))) with
                  | Some mem' =>
                      let out := am_out (a_model A) ++ concat (map e_pieces es) in
                      Some [AS (wofZ (b + 0x94)) (clob CLOB regs) (resv_drop (a_resv A)) mem' s
                               (with_out (a_model A) (norm s (length out) out)) (a_budget A) (a_steps A + 1)]
                  | None => None
                  end
                else None
            | None => None
            end
        | None => None
        end
      else None
  | _, _, _, _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma R_out (segs : list Segment) (LIM : Z) (fs0 : Fs.Fs) (ρ : valuation) (A : AST) (c : config) (o : list piece) :
  R segs amodel (MR segs fs0 ρ) LIM ρ A c ->
  R segs amodel (MR segs fs0 ρ) LIM ρ (AS (a_pc A) (a_regs A) (a_resv A) (a_mem A) (a_facts A) (with_out (a_model A) o) (a_budget A) (a_steps A)) c.
Proof.
  intros [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15].
  constructor; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  exact (MR_out segs fs0 ρ (a_model A) (cfg_model c) o H8).
Qed.

Section EntS.
Variable segs : list Segment.
Hypothesis Hlow : segs_low segs.

Lemma ents_of_sound (fs0 : Fs.Fs) (ρ : valuation) (s : store) (A : list region) (am : amodel) (m : word -> option byte) (model : Model)
    (ph : PhdrInfo) (o : w64) (cnt : Z) (es : list ioent) :
  sat ρ s -> RMem segs ρ A m -> hs_ok ρ A m -> MR segs fs0 ρ am model -> find_entry A = Some ph -> atop_is_sp am = true ->
  - 8388608 <= wS o -> wS o + 16 * cnt <= 0 -> cnt = 1 \/ cnt = 2 ->
  ents_of segs s A am (wS o, sp_terms) (XS sp_terms o) cnt = Some es ->
  exists (ents : list (word * word)) (bss : list (list byte)),
    Z.of_nat (length ents) = cnt /\ iov_array segs m (Z_to_bv 64 (sp_val ρ + wS o)) ents /\ iov_bufs segs m ents bss /\ iov_bufs_ok ents
    /\ bufs_disj (sp_val ρ + wS o) (sp_val ρ + wS o + 16 * cnt) ents /\ iov_nl model ents
    /\ pieces_val ρ (concat (map e_pieces es)) (concat bss)
    /\ iovs_total ents = fold_right (fun e acc => leval ρ (e_len e) + acc) 0 es
    /\ fold_right (fun e acc => e_lo s e + acc) 0 es <= iovs_total ents <= 262142.
Proof.
  intros Hs HM Hhs Hmod Efe Eat Ho1 Ho2 Hcnt H.
  destruct (eb_of_R segs ρ A m ph HM Efe) as [nR Heb]. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & _ & Hs2). unfold sp_window_lo, sp_window_hi in *.
  set (iovp := sp_val ρ + wS o) in *.
  assert (Hiov : 0 <= iovp /\ iovp + 32 < 2 ^ 64) by (unfold iovp; lia).
  assert (Hu : bv_unsigned (Z_to_bv 64 iovp) = iovp) by (apply u_wz; lia).
  assert (Hv : xv_val ρ (XS sp_terms o) (Z_to_bv 64 iovp)).
  { cbn [xv_val]. rewrite Hu. unfold smod. change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o), Zplus_mod_idemp_r.
    symmetry. apply Z.mod_small. unfold FastWord.two64, iovp in *. lia. }
  assert (Hx : xaddr (XS sp_terms o) <> None) by discriminate.
  unfold ents_of in H.
  destruct (ent_words segs s A (XS sp_terms o) 0) as [[vb vn]|] eqn:Ew0; [|discriminate].
  destruct (ent_of segs s A am (wS o, sp_terms) cnt vb vn) as [e0|] eqn:Ee0; [|discriminate].
  destruct (ent_words_sound segs Hlow ρ s A m _ _ 0 vb vn Hs HM Hhs Hv Hx Ew0) as (b0 & n0 & Hrb0 & Hrn0 & Hvb0 & Hvn0).
  rewrite Hu in Hrb0, Hrn0. replace (iovp + 16 * 0) with iovp in Hrb0 by lia. replace (iovp + (16 * 0 + 8)) with (iovp + 8) in Hrn0 by lia.
  destruct (ent_of_sound segs Hlow fs0 ρ s A am m model ph o cnt vb vn b0 n0 e0 Hs HM Hhs Hmod Efe Eat Ho1 Ho2 ltac:(lia) Hvb0 Hvn0 Ee0)
    as (bs0 & G1 & G2 & G3 & G4 & G5 & G6 & G7). fold iovp in G3.
  destruct (cnt =? 1) eqn:Ec.
  - injection H as <-. apply Z.eqb_eq in Ec. exists [(b0, n0)], [bs0].
    cbn [length iov_array iov_bufs iov_bufs_ok bufs_disj iov_nl map concat iovs_total fold_right]. rewrite Hu, !app_nil_r.
    repeat split; first [assumption | lia | idtac].
  - apply Z.eqb_neq in Ec. assert (Ec2 : cnt = 2) by lia.
    destruct (ent_words segs s A (XS sp_terms o) 1) as [[vb1 vn1]|] eqn:Ew1; [|discriminate].
    destruct (ent_of segs s A am (wS o, sp_terms) cnt vb1 vn1) as [e1|] eqn:Ee1; [|discriminate]. injection H as <-.
    destruct (ent_words_sound segs Hlow ρ s A m _ _ 1 vb1 vn1 Hs HM Hhs Hv Hx Ew1) as (b1 & n1 & Hrb1 & Hrn1 & Hvb1 & Hvn1).
    rewrite Hu in Hrb1, Hrn1. replace (iovp + 16 * 1) with (iovp + 16) in Hrb1 by lia. replace (iovp + (16 * 1 + 8)) with (iovp + 16 + 8) in Hrn1 by lia.
    destruct (ent_of_sound segs Hlow fs0 ρ s A am m model ph o cnt vb1 vn1 b1 n1 e1 Hs HM Hhs Hmod Efe Eat Ho1 Ho2 ltac:(lia) Hvb1 Hvn1 Ee1)
      as (bs1 & K1 & K2 & K3 & K4 & K5 & K6 & K7). fold iovp in K3.
    assert (Hu16 : bv_unsigned (Z_to_bv 64 (iovp + 16)) = iovp + 16) by (apply u_wz; lia).
    exists [(b0, n0); (b1, n1)], [bs0; bs1].
    cbn [length iov_array iov_bufs iov_bufs_ok bufs_disj iov_nl map concat iovs_total fold_right]. rewrite Hu, Hu16, !app_nil_r.
    repeat split; first [assumption | lia | idtac].
    exact (pieces_val_app_intro ρ _ _ _ _ G5 K5).
Qed.

End EntS.

Lemma Forall2_BT (ρ : valuation) (k : nat) : Forall2 (xb_bv ρ) (repeat BT k) (repeat (Z_to_bv 8 0) k).
Proof. induction k as [|k IH]; cbn [repeat]; constructor; [exact I | exact IH]. Qed.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section StdioSound.
Variable T : img_tabs.
Hypothesis HT : tabs_ok T = true.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.
Hypothesis KT_emit : forall ρ o bs, KT ρ (o ++ bs) [] -> t_eq (KT ρ o) (t_emit (W 2 bs) (KT ρ (o ++ bs))).

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

(* [comment removed for export] *)
Lemma stdio_succ_R (ρ : valuation) (A : AST) (ms ms' : machine_state) (model : Model) (b : Z) (o : w64) (n : nat) (mem' : list region)
    (out : list piece) :
  R segs amodel (MR segs fs0 ρ) LIM ρ A (mkCfg ms model) ->
  sp_window_lo <= sp_val ρ <= sp_window_hi -> atop_is_sp (a_model A) = true ->
  - 8388608 <= wS o -> wS o + Z.of_nat n <= 0 -> (1 <= n < 1000)%nat ->
  a_store segs (a_mem A) (XS sp_terms o) (repeat BT n) = Some mem' ->
  pc_ok (wofZ (b + 0x94)) = true -> 0 <= b + 0x94 < 2 ^ 64 ->
  SWF ms ms' (sp_val ρ + wS o) (sp_val ρ + wS o + Z.of_nat n) -> ms_pc_val ms' = pcw b 0x94 ->
  R segs amodel (MR segs fs0 ρ) LIM ρ
    (AS (wofZ (b + 0x94)) (clob CLOB (a_regs A)) (resv_drop (a_resv A)) mem' (a_facts A) (with_out (a_model A) out) (a_budget A) (a_steps A + 1))
    (mkCfg ms' model).
Proof.
  intros HR Hsp Eat Ho1 Ho2 Hn Est Epc Hb94 HF Hpc'.
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  unfold sp_window_lo, sp_window_hi in Hsp.
  set (iovp := sp_val ρ + wS o) in *.
  assert (Hu : bv_unsigned (Z_to_bv 64 iovp) = iovp) by (apply u_wz; unfold iovp; lia).
  assert (Hv : xv_val ρ (XS sp_terms o) (Z_to_bv 64 iovp)).
  { cbn [xv_val]. rewrite Hu. unfold smod. change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o), Zplus_mod_idemp_r.
    symmetry. apply Z.mod_small. unfold FastWord.two64, iovp in *. lia. }
  destruct HF as [F1 F2 F3 F4 F5 F6 F7 F8].
  assert (Hsf : Forall2 same_fields (a_mem A) mem') by exact (a_store_fields segs (a_mem A) mem' _ _ Est).
  destruct (a_store_sound segs ρ (a_mem A) mem' (ms_mem ms) _ _ (repeat BT n) (repeat (Z_to_bv 8 0) n) Hmem Hv
              ltac:(rewrite repeat_length; exact Hn) (Forall2_BT ρ n) Est) as [Hok _].
  rewrite repeat_length in Hok.
  assert (Hfr : forall x : word, ~ (iovp <= bv_unsigned x < iovp + Z.of_nat n) -> ms_mem ms' x = ms_mem ms x) by exact F7.
  assert (Hss' : forall z, in_ss z -> ms_mem ms' (wz z) = ms_mem ms (wz z)).
  { intros z Hz. apply F7. unfold in_ss, ls_beg, ls_end, hs_beg, hs_hi in Hz. rewrite u_wz by lia. unfold iovp. lia. }
  apply (R_out segs LIM fs0 ρ (AS (wofZ (b + 0x94)) (clob CLOB (a_regs A)) (resv_drop (a_resv A)) mem' (a_facts A) (a_model A) (a_budget A) (a_steps A + 1))).
  apply (R_build segs amodel (MR segs fs0 ρ) LIM ρ (MR_mat segs fs0 ρ) A _ ms ms' model model HR);
    cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget].
  - rewrite Hpc'. rewrite wbv_wofZ by exact Hb94. reflexivity.
  - exact Epc.
  - exact F1.
  - exact (RRegs_clob ρ (a_regs A) ms ms' CLOB Hregs F6 CLOB_nz).
  - destruct (a_resv A); cbn [resv_drop RResv] in *; try exact I. destruct F5 as [X|X]; rewrite X; [exact Hres | reflexivity].
  - exact F2.
  - apply (a_store_BT_havoc segs ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms') _ _ n Hmem Hv ltac:(lia) ltac:(lia) Est); [|exact F8].
    intros x Hx. apply Hfr. rewrite Hu in Hx. exact Hx.
  - exact (hs_ok_out ρ (a_mem A) mem' (ms_mem ms) (ms_mem ms') Hsf Hss' Hhs).
  - apply (mem_cov_range segs model (ms_mem ms) (ms_mem ms') iovp n Hcov ltac:(unfold iovp; lia) ltac:(unfold AxAcct.two64, iovp; lia) Hok Hfr).
  - exact (comp_inv_geom segs ρ (a_mem A) mem' model Hsf Hcomp).
  - apply (na_ok_geom segs ρ (a_mem A) mem' model _ Hsf).
    apply (na_ok_range segs ρ (a_mem A) model (ms_mem ms) (ms_mem ms') iovp n Hnaok ltac:(unfold iovp; lia) ltac:(unfold AxAcct.two64, iovp; lia) Hok Hfr).
  - reflexivity.
  - exact Hsat.
  - left. split; [reflexivity | lia].
Qed.

Theorem sum_stdio_sound (A : AST) (l : list AST) : sum_stdio T segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ [ms model] HR o' Ho. unfold sum_stdio in Hs. cbv zeta in Hs.
  destruct (sw_params T (wZ (a_pc A) - 0x88)) as [sr|] eqn:Ep; [|discriminate].
  destruct (xlit (aget (a_regs A) 17%uint63)) as [a7|] eqn:E17; [|discriminate].
  destruct (xlit (aget (a_regs A) 10%uint63)) as [fd|] eqn:E10; [|discriminate].
  destruct (aget (a_regs A) 11%uint63) as [| ts o | | | |] eqn:E11; try discriminate.
  destruct (xlit (aget (a_regs A) 12%uint63)) as [cnt|] eqn:E12; [|discriminate].
  destruct (xlit (aget (a_regs A) 18%uint63)) as [cnt'|] eqn:E18; [|discriminate].
  destruct (xlit (aget (a_regs A) 9%uint63)) as [f|] eqn:E9; [|discriminate].
  destruct (find_entry (a_mem A)) as [ph|] eqn:Efe; [|discriminate].
  destruct (sw_code_ok segs (wZ (a_pc A) - 0x88) sr) eqn:Hcode; [|discriminate].
  destruct (sw_code_sound segs _ sr (sw_params_bnd T HT _ _ Ep) Hcode) as (wj1 & wj2 & ij1 & ij2 & HSW).
  destruct (a7 =? 66) eqn:Ea7; [|discriminate]. apply Z.eqb_eq in Ea7. subst a7.
  destruct (fd =? 2) eqn:Efd; [|discriminate]. apply Z.eqb_eq in Efd. subst fd.
  destruct (teqb ts sp_terms) eqn:Ets; [|discriminate]. apply teqb_eq in Ets. subst ts.
  destruct (- 8388608 <=? wS o) eqn:Eo1; [|discriminate]. apply Z.leb_le in Eo1.
  destruct (wS o + 16 * cnt <=? 0) eqn:Eo2; [|discriminate]. apply Z.leb_le in Eo2.
  destruct ((cnt =? 1) ||| (cnt =? 2)) eqn:Ecnt; [|discriminate].
  destruct (cnt' =? cnt) eqn:Ecnt'; [|discriminate]. apply Z.eqb_eq in Ecnt'. subst cnt'.
  destruct (xv_eqb (aget (a_regs A) 19%uint63) (XS sp_terms o)) eqn:E19; [|discriminate]. apply xv_eqb_eq in E19.
  destruct (atop_is_sp (a_model A)) eqn:Eat; [|discriminate].
  destruct (0 <=? f) eqn:Ef0; [|discriminate]. apply Z.leb_le in Ef0.
  destruct (in_segn segs (f + 120) 4) eqn:Efs; [|discriminate].
  destruct (fd2_ok segs (a_mem A) f) eqn:Efd2; [|discriminate].
  destruct (pc_ok (wofZ (wZ (a_pc A) - 0x88 + 0x94))) eqn:Epc; [|discriminate].
  destruct (ents_of segs (a_facts A) (a_mem A) (a_model A) (wS o, sp_terms) (XS sp_terms o) cnt) as [es|] eqn:Ees; [|discriminate].
  destruct (total_of es) as [Tt|] eqn:ET; [|discriminate].
  destruct (total_is (aget (a_regs A) 22%uint63) Tt) eqn:Eti; [|discriminate].
  destruct (1 <=? fold_right (fun e acc => e_lo (a_facts A) e + acc) 0 es) eqn:Elo; [|discriminate]. apply Z.leb_le in Elo.
  destruct (a_store segs (a_mem A) (XS sp_terms o) (repeat BT (Z.to_nat (16 * cnt)))) as [mem'|] eqn:Est; [|discriminate].
  injection Hs as <-.
  assert (Hcnt : cnt = 1 \/ cnt = 2) by (apply lor_true in Ecnt as [X|X]; apply Z.eqb_eq in X; [left | right]; exact X).
  pose proof HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok]. cbn [cfg_ms cfg_model] in *.
  set (b := wZ (a_pc A) - 0x88) in *.
  destruct (eb_of_R segs ρ (a_mem A) (ms_mem ms) ph Hmem Efe) as [nR Heb]. pose proof (eb_rel_facts ph ρ _ _ _ Heb) as HF.
  pose proof (eb_layout ρ HF) as (Hs1 & Hargc & Henvc & Hl0 & Hq0 & _ & Hs2).
  assert (Hsp : sp_window_lo <= sp_val ρ <= sp_window_hi) by (unfold sp_window_lo, sp_window_hi in *; lia).
  unfold sp_window_lo, sp_window_hi in Hs1, Hs2.
  pose proof (atop_is_sp_sound segs fs0 ρ _ _ Hmod Eat) as Hatop.
  set (iovp := sp_val ρ + wS o) in *.
  assert (Hu : bv_unsigned (Z_to_bv 64 iovp) = iovp) by (apply u_wz; unfold iovp; lia).
  assert (Hv : xv_val ρ (XS sp_terms o) (Z_to_bv 64 iovp)).
  { cbn [xv_val]. rewrite Hu. unfold smod. change (teval ρ sp_terms) with (sp_val ρ). rewrite <- (wS_mod o), Zplus_mod_idemp_r.
    symmetry. apply Z.mod_small. unfold FastWord.two64, iovp in *. lia. }
  destruct (ents_of_sound segs Hlow fs0 ρ (a_facts A) (a_mem A) (a_model A) (ms_mem ms) model ph o cnt es Hsat Hmem Hhs Hmod Efe Eat Eo1 Eo2 Hcnt Ees)
    as (ents & bss & Hlen & Harr & Hbufs & Hbok & Hdisj & Hnlb & Hpv & Htot & Htlo). fold iovp in Harr, Hdisj.
  rewrite <- (total_of_val ρ es Tt ET) in Htot.
  assert (Hn16 : Z.of_nat (Z.to_nat (16 * cnt)) = 16 * cnt) by lia.
  assert (Hnn : (1 <= Z.to_nat (16 * cnt) < 1000)%nat) by lia.
  assert (Hb94 : 0 <= b + 0x94 < 2 ^ 64) by (pose proof (wZ_range (a_pc A)); pose proof (pc_ok_spec _ Epc) as [_ X]; unfold b, FastWord.two64 in *; lia).
  assert (Hb0 : 0 <= b).
  { destruct HSW as [_ _ _ _ _ _ _ _ _ _ X]. lia. }
  destruct (in_segn_low segs (f + 120) 4 Hlow Efs) as [Hf1 Hf2]. unfold ls_beg in Hf2.
  (* [comment removed for export] *)
  assert (G : forall (r : reg) (k : int) (z : Z), ri r = k -> xlit (aget (a_regs A) k) = Some z -> rg ms r = Z_to_bv 64 z).
  { intros r k z Hk E. apply word_lit_w. exact (reg_lit ρ _ ms r k z Hregs Hk E). }
  assert (H11 : rg ms 11%bv = Z_to_bv 64 iovp).
  { apply word_lit_w. change 11%uint63 with (ri 11%bv) in E11. rewrite <- Hu. pose proof (Hregs 11%bv) as X. rewrite E11 in X. cbn [xv_val] in *. lia. }
  assert (H19 : rg ms 19%bv = Z_to_bv 64 iovp).
  { apply word_lit_w. rewrite <- Hu. pose proof (Hregs 19%bv) as X. change (ri 19%bv) with 19%uint63 in X. rewrite E19 in X. cbn [xv_val] in *. lia. }
  assert (H22 : rg ms 22%bv = Z_to_bv 64 (iovs_total ents)).
  { apply word_lit_w. rewrite Htot. apply (total_is_sound ρ _ _ Tt (Hregs 22%bv) Eti). rewrite <- Htot. lia. }
  (* [comment removed for export] *)
  set (bsout := concat bss) in *.
  set (out := am_out (a_model A) ++ concat (map e_pieces es)) in *.
  assert (Hout : pieces_val ρ (norm (a_facts A) (length out) out) (o' ++ bsout)).
  { apply (norm_sound ρ _ Hsat). exact (pieces_val_app_intro ρ _ _ _ _ Ho Hpv). }
  set (B := AS (wofZ (b + 0x94)) (clob CLOB (a_regs A)) (resv_drop (a_resv A)) mem' (a_facts A)
               (with_out (a_model A) (norm (a_facts A) (length out) out)) (a_budget A) (a_steps A + 1)) in *.
  assert (HB : forall ms', SWF ms ms' iovp (iovp + 16 * cnt) -> ms_pc_val ms' = pcw b 0x94 -> realizes_cfg segs cfg (mkCfg ms' model) (KT ρ (o' ++ bsout))).
  { intros ms' HF' Hpc'. refine (HS B (or_introl eq_refl) ρ (mkCfg ms' model) _ (o' ++ bsout) Hout).
    apply (stdio_succ_R ρ A ms ms' model b o (Z.to_nat (16 * cnt)) mem' _ HR Hsp Eat Eo1 ltac:(lia) Hnn Est Epc Hb94); [|exact Hpc'].
    fold iovp. rewrite Hn16. exact HF'. }
  (* [comment removed for export] *)
  assert (Hne : KT ρ (o' ++ bsout) []).
  { apply (realizes_cfg_nonempty segs cfg (mkCfg (setx ms 0%bv w0 (pcw b 0x94) (ms_resv ms) (ms_mem ms)) model)). apply HB; [|reflexivity].
    constructor; cbn [setx ms_svc_pending ms_rom ms_fregs ms_fcsr ms_resv ms_mem];
      first [apply mem_grows_refl | reflexivity | (left; reflexivity) | (intros r _; apply rg_setx_x0) | (intros x _; reflexivity)]. }
  apply (rzc_conseq segs cfg _ (t_emit (W 2 bsout) (KT ρ (o' ++ bsout)))); [|apply t_eq_sym; exact (KT_emit ρ o' bsout Hne)].
  destruct (a_store_sound segs ρ (a_mem A) mem' (ms_mem ms) _ _ (repeat BT (Z.to_nat (16 * cnt))) (repeat (Z_to_bv 8 0) (Z.to_nat (16 * cnt))) Hmem Hv
              ltac:(rewrite repeat_length; exact Hnn) (Forall2_BT ρ _) Est) as [Hok _].
  rewrite repeat_length in Hok.
  apply (stdio_write_loop segs cfg b sr wj1 wj2 ij1 ij2 HSW
           ms model (KT ρ (o' ++ bsout)) 2 f iovp ents bss Hsvc Hrom).
  - rewrite Hpc. unfold wbv, pcw. f_equal. unfold b. lia.
  - exact Hh.
  - exact (G 17%bv 17%uint63 66 eq_refl E17).
  - exact (G 10%bv 10%uint63 2 eq_refl E10).
  - exact H11.
  - exact H19.
  - rewrite Hlen. exact (G 12%bv 12%uint63 cnt eq_refl E12).
  - rewrite Hlen. exact (G 18%bv 18%uint63 cnt eq_refl E18).
  - exact H22.
  - exact (G 9%bv 9%uint63 f eq_refl E9).
  - lia.
  - lia.
  - exact (fd_rel_lookup2 fs0 ρ _ _ (mr_fds segs fs0 ρ _ _ Hmod)).
  - lia.
  - exact (fd2_ok_sound segs ρ (a_mem A) (ms_mem ms) f Hmem ltac:(lia) Efd2).
  - exact Ef0.
  - lia.
  - unfold iovp. lia.
  - rewrite Hlen. unfold TASK_SIZE, iovp. lia.
  - exact Harr.
  - exact Hbufs.
  - exact Hbok.
  - replace (16 * length ents)%nat with (Z.to_nat (16 * cnt)) by lia. exact Hok.
  - left. unfold iovp. lia.
  - rewrite Hlen. exact Hdisj.
  - apply (no_lazy_above segs fs0 ρ _ model _ _ Hmod). rewrite Hatop. unfold iovp. lia.
  - replace (f + 124) with (f + 120 + 4) by lia.
    exact (no_lazy_imgn segs Hlow model _ _ (mr_res segs fs0 ρ _ _ Hmod) (mr_lazy_res segs fs0 ρ _ _ Hmod) Efs).
  - exact Hnlb.
  - intros ms' HF' Hpc' _ _. rewrite Hlen in HF'. exact (HB ms' HF' Hpc').
Qed.

End StdioSound.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
