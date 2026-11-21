(** * Bridge.Infl.IBits — pair I4 of PAIRS.md: the inflate bit accumulator and the two-level
    table decode, S5 vs RT.

    S5 keeps the reader in its registers ([IS.ir_next]/[ir_have]/[ir_hold]/[ir_bits]) over
    the call's input array; RT in a [BR].  [brel w b] relates them.  Each S5 macro
    ([PULLBYTE], [NEEDBITS], [BITS], [HOLD], [DROPBITS], [INITBITS], [BYTEBITS], [DECODE1],
    [DECODE2]) is shown to move S5's registers exactly as RT's matching function moves the
    [BR], in the form [macro w = ARun v (wset_r w (setbr (w_r w) b'))], so an arm's proof
    rewrites each macro in place.

    S5 wraps [hold] to 64 bits and [bits]/[have] to 32; RT computes on [Z].  They agree
    because [bits <= 39], [hold < 2^bits] and the input stays below [2^32] bytes.  S5's
    [NEEDBITS] and [DECODE] loops have fuel 8 and fall through quietly when it runs out;
    RT's fail.  8 is enough because a request is at most 32 bits and, under [tview], a
    table entry needs at most 15. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require S5IFields.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(** S5's reader registers and input against RT's [BR]. *)
Definition brel (w : IS.iw) (b : RB.BR) : Prop :=
  let r := IS.w_r w in let c := IS.w_c w in
  IS.ir_hold r = RB.br_hold b /\ IS.ir_bits r = RB.br_bits b
  /\ IS.ir_next r = RB.br_next b /\ IS.ir_have r = RB.br_have b
  /\ 0 <= IS.ir_next r /\ 0 <= IS.ir_have r /\ IS.ir_next r + IS.ir_have r < 2 ^ 32
  /\ 0 <= IS.ir_bits r <= 39 /\ 0 <= IS.ir_hold r < 2 ^ IS.ir_bits r
  /\ (forall i, 0 <= i -> arr_get (IS.ic_input c) i = RB.br_in b i /\ 0 <= RB.br_in b i < 256).

(** S5's registers once RT's reader has moved to [b]. *)
Definition setbr (r : IS.iregs) (b : RB.BR) : IS.iregs :=
  IS.mkIR (RB.br_next b) (RB.br_have b) (IS.ir_put r) (IS.ir_left r) (RB.br_hold b) (RB.br_bits b)
          (IS.ir_in r) (IS.ir_out r) (IS.ir_ret r).

Definition wbr (w : IS.iw) (b : RB.BR) : IS.iw := IS.wset_r w (setbr (IS.w_r w) b).

(** [icore] carries [brel] for RT's live reader. *)
Lemma icore_brel : forall w q, icore w q -> brel w (RI.q_br q).
Proof.
  intros w q H. unfold icore, iw_rel in H. cbv zeta in H.
  destruct H as ((_ & Hh & Hb & Hn & Hv & Hn0 & Hv0 & _) & _ & Hbr & Hhr & _ & Hin & _ & _ & Hnv & _).
  exact (conj Hh (conj Hb (conj Hn (conj Hv (conj Hn0 (conj Hv0 (conj Hnv (conj Hbr (conj Hhr Hin))))))))).
Qed.

(* ------------------------------------------------------------------------- *)
(* Kit                                                                       *)
(* ------------------------------------------------------------------------- *)

Lemma iregs_ext : forall r1 r2 : IS.iregs,
  IS.ir_next r1 = IS.ir_next r2 -> IS.ir_have r1 = IS.ir_have r2 -> IS.ir_put r1 = IS.ir_put r2 ->
  IS.ir_left r1 = IS.ir_left r2 -> IS.ir_hold r1 = IS.ir_hold r2 -> IS.ir_bits r1 = IS.ir_bits r2 ->
  IS.ir_in r1 = IS.ir_in r2 -> IS.ir_out r1 = IS.ir_out r2 -> IS.ir_ret r1 = IS.ir_ret r2 -> r1 = r2.
Proof. intros [] []; cbn; intros; subst; reflexivity. Qed.

Lemma iw_eta_r : forall w r, IS.w_r w = r -> IS.wset_r w r = w.
Proof. intros [s c r0] r H. cbn in H. subst. reflexivity. Qed.

Lemma wbr_s : forall w b, IS.w_s (wbr w b) = IS.w_s w.
Proof. intros. unfold wbr. autorewrite with s5w. reflexivity. Qed.
Lemma wbr_c : forall w b, IS.w_c (wbr w b) = IS.w_c w.
Proof. intros. unfold wbr. autorewrite with s5w. reflexivity. Qed.
Lemma wbr_r : forall w b, IS.w_r (wbr w b) = setbr (IS.w_r w) b.
Proof. intros. unfold wbr. autorewrite with s5w. reflexivity. Qed.
Lemma wbr_wbr : forall w b1 b2, wbr (wbr w b1) b2 = wbr w b2.
Proof. reflexivity. Qed.

Ltac setbr_cbn :=
  cbn [setbr IS.ir_next IS.ir_have IS.ir_put IS.ir_left IS.ir_hold IS.ir_bits IS.ir_in IS.ir_out
       IS.ir_ret RB.br_in RB.br_next RB.br_have RB.br_hold RB.br_bits RB.br_dropbits RB.br_initbits].

Lemma wbr_id : forall w b, brel w b -> wbr w b = w.
Proof.
  intros w b (Hh & Hbt & Hn & Hv & _).
  unfold wbr. apply iw_eta_r. apply iregs_ext; setbr_cbn; congruence.
Qed.

(** [brel] for the moved reader, from the facts about the new [BR]. *)
Lemma brel_wbr : forall w b b',
  brel w b -> RB.br_in b' = RB.br_in b ->
  0 <= RB.br_next b' -> 0 <= RB.br_have b' -> RB.br_next b' + RB.br_have b' < 2 ^ 32 ->
  0 <= RB.br_bits b' <= 39 -> 0 <= RB.br_hold b' < 2 ^ RB.br_bits b' ->
  brel (wbr w b') b'.
Proof.
  intros w b b' Hb Hin Hn Hv Hnv Hbt Hh.
  destruct Hb as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hi).
  unfold brel. cbv zeta. rewrite wbr_r, wbr_c. setbr_cbn. rewrite Hin.
  exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl
          (conj Hn (conj Hv (conj Hnv (conj Hbt (conj Hh Hi))))))))).
Qed.

Lemma abind_ARun : forall {A B} (m : IS.AM A) (f : A -> IS.AM B) w a w',
  m w = IS.ARun a w' -> IS.abind m f w = f a w'.
Proof. intros A B m f w a w' H. unfold IS.abind. rewrite H. reflexivity. Qed.

Lemma pull_bound : forall h n x, 0 <= n -> 0 <= h < 2 ^ n -> 0 <= x < 256 ->
  0 <= h + x * 2 ^ n < 2 ^ (n + 8).
Proof.
  intros h n x Hn Hh Hx. rewrite Z.pow_add_r by lia.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia). change (2 ^ 8) with 256. nia.
Qed.

Lemma shiftr_bound : forall h m n, 0 <= n <= m -> 0 <= h < 2 ^ m -> 0 <= Z.shiftr h n < 2 ^ (m - n).
Proof.
  intros h m n Hn Hh. rewrite Z.shiftr_div_pow2 by lia.
  assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|].
  apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
  replace (n + (m - n)) with m by lia. lia.
Qed.

Lemma land_mask_range : forall hold n, 0 <= n -> 0 <= Z.land hold (Z.shiftl 1 n - 1) < 2 ^ n.
Proof.
  intros hold n Hn. rewrite Z.shiftl_1_l.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.

Lemma sub_index_range : forall hold cb op, 0 <= cb -> 0 <= op ->
  0 <= Z.shiftr (Z.land hold (Z.shiftl 1 (cb + op) - 1)) cb < 2 ^ op.
Proof.
  intros hold cb op Hc Ho.
  pose proof (land_mask_range hold (cb + op) ltac:(lia)) as H.
  pose proof (shiftr_bound _ (cb + op) cb ltac:(lia) H) as H2.
  replace (cb + op - cb) with op in H2 by lia. exact H2.
Qed.

(** S5's [BITS] index is RT's [br_bits_of] for requests of at most 32 bits. *)
Lemma bitsv_eq : forall hold n, 0 <= n <= 32 ->
  IA.BITSv hold n = Z.land hold (Z.shiftl 1 n - 1).
Proof.
  intros hold n Hn. unfold IA.BITSv, OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateFast.zmask.
  rewrite Z.shiftl_1_l.
  assert (Hp : 0 < 2 ^ n) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp32 : 2 ^ n <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia).
  rewrite (wrap32_id (2 ^ n - 1)) by lia.
  unfold wrap32.
  replace (2 ^ n - 1) with (Z.ones n) by (rewrite Z.ones_equiv; lia).
  change 4294967295 with (Z.ones 32).
  rewrite (Z.land_ones hold 32) by lia.
  rewrite !Z.land_ones by lia.
  apply Z.mod_mod_divide. exists (2 ^ (32 - n)). rewrite <- Z.pow_add_r by lia. f_equal; lia.
Qed.

(** S5's packed table entries read back. *)
Lemma enc_op : forall h, code_rng h -> IS.code_op (RBa.code_enc h) = RBa.c_op h.
Proof.
  intros h (Ho & Hb & Hv). unfold IS.code_op, RBa.code_enc.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  symmetry. apply Z.mod_unique with (q := RBa.c_bits h + 256 * RBa.c_val h); lia.
Qed.

Lemma enc_bits : forall h, code_rng h -> IS.code_bits (RBa.code_enc h) = RBa.c_bits h.
Proof.
  intros h (Ho & Hb & Hv). unfold IS.code_bits, RBa.code_enc.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- (Z.div_unique (RBa.c_op h + 256 * RBa.c_bits h + 65536 * RBa.c_val h) 256
                (RBa.c_bits h + 256 * RBa.c_val h) (RBa.c_op h)) by lia.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  symmetry. apply Z.mod_unique with (q := RBa.c_val h); lia.
Qed.

Lemma enc_val : forall h, code_rng h -> IS.code_val (RBa.code_enc h) = RBa.c_val h.
Proof.
  intros h (Ho & Hb & Hv). unfold IS.code_val, RBa.code_enc.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  rewrite <- (Z.div_unique (RBa.c_op h + 256 * RBa.c_bits h + 65536 * RBa.c_val h) 65536
                (RBa.c_val h) (RBa.c_op h + 256 * RBa.c_bits h)) by lia.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. change (2 ^ 16) with 65536.
  apply Z.mod_small. lia.
Qed.

(** One-step unfoldings of S5's two fuelled loops. *)
Lemma needbits_k_S : forall k n w, IA.NEEDBITS_k (S k) n w =
  if IS.ir_bits (IS.w_r w) <? n then IS.abind IA.PULLBYTE (fun _ => IA.NEEDBITS_k k n) w
  else IS.ARun tt w.
Proof.
  intros k n w.
  change (IA.NEEDBITS_k (S k) n w) with
    ((if IS.ir_bits (IS.w_r w) <? n then IS.abind IA.PULLBYTE (fun _ => IA.NEEDBITS_k k n)
      else IS.aret tt) w).
  destruct (IS.ir_bits (IS.w_r w) <? n); reflexivity.
Qed.

Lemma decode_k_O : forall p sidx sneed w,
  IA.DECODE_k O p sidx sneed w = IS.ARun (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w)))) w.
Proof. reflexivity. Qed.

Lemma decode_k_S : forall k p sidx sneed w,
  IA.DECODE_k (S k) p sidx sneed w =
  if sneed (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w)))) <=? IS.ir_bits (IS.w_r w)
  then IS.ARun (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w)))) w
  else IS.abind IA.PULLBYTE (fun _ => IA.DECODE_k k p sidx sneed) w.
Proof.
  intros k p sidx sneed w.
  change (IA.DECODE_k (S k) p sidx sneed w) with
    ((if sneed (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w)))) <=? IS.ir_bits (IS.w_r w)
      then IS.aret (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w))))
      else IS.abind IA.PULLBYTE (fun _ => IA.DECODE_k k p sidx sneed)) w).
  destruct (sneed (IS.code_at (IS.w_s w) p (sidx (IS.ir_hold (IS.w_r w)))) <=? IS.ir_bits (IS.w_r w));
    reflexivity.
Qed.

(** RT's two fetch loops as one loop, indexed from [hold]. *)
Fixpoint gfetch (f : nat) (ix : Z -> Z) (t : RBa.ztbl) (cb : RBa.Code -> Z) (b : RB.BR)
  : RI.Fetch :=
  match f with
  | O => RI.FetchFuel
  | S k =>
      if Z.leb (cb (t (ix (RB.br_hold b)))) (RB.br_bits b) then RI.FetchOk (t (ix (RB.br_hold b))) b
      else match RB.br_pullbyte b with
           | None => RI.FetchLeave b
           | Some b' => gfetch k ix t cb b'
           end
  end.

Lemma fetch_gfetch : forall f t nb b,
  RI.inf_fetch_go f t nb b = gfetch f (fun hold => Z.land hold (Z.shiftl 1 nb - 1)) t RBa.c_bits b.
Proof.
  induction f as [|f IH]; intros t nb b; cbn [RI.inf_fetch_go gfetch]; [reflexivity|].
  unfold RB.br_bits_of.
  destruct (Z.leb _ _); [reflexivity|].
  destruct (RB.br_pullbyte b); [apply IH|reflexivity].
Qed.

Lemma fetch2_gfetch : forall f t lst b,
  RI.inf_fetch2_go f t lst b =
  gfetch f (fun hold => RBa.c_val lst
                        + Z.shiftr (Z.land hold (Z.shiftl 1 (RBa.c_bits lst + RBa.c_op lst) - 1))
                                   (RBa.c_bits lst))
         t (fun h => RBa.c_bits lst + RBa.c_bits h) b.
Proof.
  induction f as [|f IH]; intros t lst b; cbn [RI.inf_fetch2_go gfetch]; [reflexivity|].
  unfold RB.br_bits_of.
  destruct (Z.leb _ _); [reflexivity|].
  destruct (RB.br_pullbyte b); [apply IH|reflexivity].
Qed.

(* ------------------------------------------------------------------------- *)
(* The macros                                                                *)
(* ------------------------------------------------------------------------- *)

Lemma pullbyte_sim : forall w b b',
  brel w b -> RB.br_bits b < 32 -> RB.br_pullbyte b = Some b' ->
  IA.PULLBYTE w = IS.ARun tt (wbr w b') /\ brel (wbr w b') b'.
Proof.
  intros w b b' Hb Hlt Hp.
  pose proof Hb as (Hh & Hbt & Hn & Hv & Hn0 & Hv0 & Hnv & Hbr & Hhr & Hi).
  rewrite Hbt in Hbr, Hhr. rewrite Hh in Hhr. rewrite Hn, Hv in Hnv. rewrite Hn in Hn0.
  rewrite Hv in Hv0.
  unfold RB.br_pullbyte in Hp.
  destruct (Z.eqb_spec (RB.br_have b) 0) as [E|E]; [discriminate|].
  injection Hp as <-.
  destruct (Hi (RB.br_next b) Hn0) as [Hx Hxr].
  pose proof (pull_bound (RB.br_hold b) (RB.br_bits b) (RB.br_in b (RB.br_next b))
                (proj1 Hbr) Hhr Hxr) as Hpb.
  assert (H39 : 2 ^ (RB.br_bits b + 8) <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia).
  assert (H64 : 2 ^ 39 < 2 ^ 64) by (cbv; reflexivity).
  assert (Hxp : 0 <= RB.br_in b (RB.br_next b) * 2 ^ RB.br_bits b)
    by (apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]).
  split.
  - unfold IA.PULLBYTE. cbv zeta.
    rewrite Hv, (proj2 (Z.eqb_neq _ _) E).
    f_equal. unfold wbr. f_equal. apply iregs_ext; setbr_cbn; try reflexivity.
    + rewrite Hn. reflexivity.
    + apply wrap32_id. lia.
    + rewrite Hn, Hh, Hbt, Hx. unfold shl64.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (wrap64_id (_ * _)) by lia.
      apply wrap64_id. lia.
    + rewrite Hbt. apply wrap32_id. lia.
  - apply (brel_wbr w b _ Hb); setbr_cbn; try reflexivity; try lia.
    rewrite Z.shiftl_mul_pow2 by lia. exact Hpb.
Qed.

Lemma needbits_go_sim : forall f k w b b' n,
  brel w b -> n <= 32 -> n <= RB.br_bits b + 8 * Z.of_nat k ->
  RI.inf_nb_go f n b = RI.NBOk b' ->
  IA.NEEDBITS_k k n w = IS.ARun tt (wbr w b') /\ brel (wbr w b') b'
  /\ n <= RB.br_bits b' /\ RB.br_in b' = RB.br_in b
  /\ RB.br_next b' + RB.br_have b' = RB.br_next b + RB.br_have b.
Proof.
  induction f as [|f IH]; intros k w b b' n Hb Hn32 Hk Hf; cbn [RI.inf_nb_go] in Hf;
    pose proof Hb as (_ & Hbt & _).
  - destruct (Z.ltb_spec (RB.br_bits b) n) as [L|L]; [discriminate|].
    injection Hf as <-. rewrite (wbr_id w b Hb).
    split; [|split; [exact Hb|split; [exact L|split; reflexivity]]].
    destruct k as [|k]; [reflexivity|].
    rewrite needbits_k_S, Hbt, (proj2 (Z.ltb_ge _ _) L). reflexivity.
  - destruct (Z.ltb_spec (RB.br_bits b) n) as [L|L].
    + destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
      destruct k as [|k]; [lia|].
      destruct (pullbyte_sim w b b1 Hb ltac:(lia) Hp) as [Hpw Hb1].
      pose proof (RB.br_pullbyte_step b b1 Hp) as (Hv1 & Hn1 & Hbt1 & Hin1).
      destruct (IH k (wbr w b1) b1 b' n Hb1 Hn32 ltac:(lia) Hf) as (E & Hb' & Hn' & Hin' & Hsum).
      rewrite wbr_wbr in E, Hb'.
      split; [|split; [exact Hb'|split; [exact Hn'|split; [congruence|lia]]]].
      rewrite needbits_k_S, Hbt, (proj2 (Z.ltb_lt _ _) L), (abind_ARun _ _ _ _ _ Hpw).
      exact E.
    + injection Hf as <-. rewrite (wbr_id w b Hb).
      split; [|split; [exact Hb|split; [exact L|split; reflexivity]]].
      destruct k as [|k]; [reflexivity|].
      rewrite needbits_k_S, Hbt, (proj2 (Z.ltb_ge _ _) L). reflexivity.
Qed.

Lemma needbits_sim : forall w b b' n,
  brel w b -> 0 <= n <= 32 -> RI.inf_nb n b = RI.NBOk b' ->
  IA.NEEDBITS n w = IS.ARun tt (wbr w b') /\ brel (wbr w b') b'
  /\ n <= RB.br_bits b' /\ RB.br_in b' = RB.br_in b
  /\ RB.br_next b' + RB.br_have b' = RB.br_next b + RB.br_have b.
Proof.
  intros w b b' n Hb Hn Hf. unfold RI.inf_nb in Hf. unfold IA.NEEDBITS.
  pose proof Hb as (_ & Hbt & _ & _ & _ & _ & _ & Hbr & _). rewrite Hbt in Hbr.
  exact (needbits_go_sim _ 8 w b b' n Hb ltac:(lia) ltac:(lia) Hf).
Qed.

Lemma bits_sim : forall w b n,
  brel w b -> 0 <= n <= 32 -> IA.BITS n w = IS.ARun (RB.br_bits_of n b) w.
Proof.
  intros w b n Hb Hn. pose proof Hb as (Hh & _).
  unfold IA.BITS, IS.gr. rewrite Hh, (bitsv_eq _ _ Hn). reflexivity.
Qed.

Lemma hold_sim : forall w b, brel w b -> IA.HOLD w = IS.ARun (RB.br_hold b) w.
Proof. intros w b Hb. pose proof Hb as (Hh & _). unfold IA.HOLD, IS.gr. rewrite Hh. reflexivity. Qed.

Lemma dropbits_sim : forall w b n,
  brel w b -> 0 <= n <= RB.br_bits b ->
  IA.DROPBITS n w = IS.ARun tt (wbr w (RB.br_dropbits n b)) /\ brel (wbr w (RB.br_dropbits n b)) (RB.br_dropbits n b).
Proof.
  intros w b n Hb Hn.
  pose proof Hb as (Hh & Hbt & Hnx & Hv & Hn0 & Hv0 & Hnv & Hbr & Hhr & _).
  rewrite Hbt in Hbr, Hhr. rewrite Hh in Hhr. rewrite Hnx, Hv in Hnv. rewrite Hnx in Hn0.
  rewrite Hv in Hv0.
  split.
  - unfold IA.DROPBITS, IS.ur. f_equal. unfold wbr. f_equal.
    apply iregs_ext; autorewrite with s5ir_bits s5ir_hold; setbr_cbn;
      try reflexivity; try assumption.
    + rewrite Hh. reflexivity.
    + rewrite Hbt. apply wrap32_id. lia.
  - apply (brel_wbr w b _ Hb); setbr_cbn; try reflexivity; try lia.
    apply shiftr_bound; [lia|exact Hhr].
Qed.

Lemma initbits_sim : forall w b,
  brel w b -> IA.INITBITS w = IS.ARun tt (wbr w (RB.br_initbits b)) /\ brel (wbr w (RB.br_initbits b)) (RB.br_initbits b).
Proof.
  intros w b Hb.
  pose proof Hb as (Hh & Hbt & Hnx & Hv & Hn0 & Hv0 & Hnv & _).
  rewrite Hnx, Hv in Hnv. rewrite Hnx in Hn0. rewrite Hv in Hv0.
  split.
  - unfold IA.INITBITS, IS.ur. f_equal. unfold wbr. f_equal.
    apply iregs_ext; autorewrite with s5ir_bits s5ir_hold; setbr_cbn;
      try reflexivity; try assumption.
  - apply (brel_wbr w b _ Hb); setbr_cbn; try reflexivity; lia.
Qed.

Lemma bytebits_sim : forall w b,
  brel w b -> IA.BYTEBITS w = IS.ARun tt (wbr w (RB.br_bytebits b)) /\ brel (wbr w (RB.br_bytebits b)) (RB.br_bytebits b).
Proof.
  intros w b Hb.
  pose proof Hb as (_ & Hbt & _ & _ & _ & _ & _ & Hbr & _). rewrite Hbt in Hbr.
  assert (Hk : 0 <= Z.land (RB.br_bits b) 7 <= RB.br_bits b).
  { change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
    pose proof (Z.mod_pos_bound (RB.br_bits b) 8 ltac:(lia)).
    pose proof (Z.mod_le (RB.br_bits b) 8 ltac:(lia) ltac:(lia)). lia. }
  destruct (dropbits_sim w b _ Hb Hk) as [E Hb'].
  unfold RB.br_bytebits. split; [|exact Hb'].
  rewrite <- E. unfold IA.BYTEBITS, IA.DROPBITS, IS.ur. cbv zeta. rewrite Hbt. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* The two-level decode                                                      *)
(* ------------------------------------------------------------------------- *)

(** The common loop: S5's [DECODE_k] against [gfetch], when every index the accumulator can
    form selects an entry S5 packs as RT's and that needs at most 15 bits. *)
Lemma decode_k_sim : forall p sidx sneed t ridx cb s,
  (forall hold, 0 <= hold ->
     IS.code_at s p (sidx hold) = RBa.code_enc (t (ridx hold))
     /\ sneed (RBa.code_enc (t (ridx hold))) = cb (t (ridx hold)) /\ cb (t (ridx hold)) <= 15) ->
  forall f k w b h b',
  brel w b -> IS.w_s w = s -> 16 <= RB.br_bits b + 8 * Z.of_nat k ->
  gfetch f ridx t cb b = RI.FetchOk h b' ->
  IA.DECODE_k k p sidx sneed w = IS.ARun (RBa.code_enc h) (wbr w b') /\ brel (wbr w b') b'
  /\ RB.br_in b' = RB.br_in b /\ RB.br_next b' + RB.br_have b' = RB.br_next b + RB.br_have b
  /\ h = t (ridx (RB.br_hold b')) /\ cb h <= RB.br_bits b'.
Proof.
  intros p sidx sneed t ridx cb s Ht f.
  induction f as [|f IH]; intros k w b h b' Hb Hs Hk Hf; cbn [gfetch] in Hf; [discriminate|].
  pose proof Hb as (Hh & Hbt & _ & _ & _ & _ & _ & Hbr & Hhr & _).
  rewrite Hbt in Hbr, Hhr. rewrite Hh in Hhr.
  destruct (Ht (RB.br_hold b) (proj1 Hhr)) as (Ec & En & E15).
  destruct (Z.leb_spec (cb (t (ridx (RB.br_hold b)))) (RB.br_bits b)) as [L|L].
  - injection Hf as <- <-.
    rewrite (wbr_id w b Hb).
    split; [|split; [exact Hb|split; [reflexivity|split; [reflexivity|split; [reflexivity|exact L]]]]].
    destruct k as [|k].
    + rewrite decode_k_O, Hh, Hs, Ec. reflexivity.
    + rewrite decode_k_S, Hh, Hs, Ec, En, Hbt, (proj2 (Z.leb_le _ _) L). reflexivity.
  - destruct (RB.br_pullbyte b) as [b1|] eqn:Hp; [|discriminate].
    destruct k as [|k]; [lia|].
    destruct (pullbyte_sim w b b1 Hb ltac:(lia) Hp) as [Hpw Hb1].
    pose proof (RB.br_pullbyte_step b b1 Hp) as (Hv1 & Hn1 & Hbt1 & Hin1).
    destruct (IH k (wbr w b1) b1 h b' Hb1 (eq_trans (wbr_s w b1) Hs) ltac:(lia) Hf)
      as (E & Hb' & Hin' & Hsum & Eh & Lc).
    rewrite wbr_wbr in E, Hb'.
    split; [|split; [exact Hb'|split; [congruence|split; [lia|split; assumption]]]].
    rewrite decode_k_S, Hh, Hs, Ec, En, Hbt, (proj2 (Z.leb_gt _ _) L), (abind_ARun _ _ _ _ _ Hpw).
    exact E.
Qed.

(** Root lookup ([inflate.c:1036-1040]).  S5 returns the packed entry, RT the record. *)
Lemma decode1_sim : forall w b b' p g root k h,
  brel w b -> tview (IS.code_at (IS.w_s w) p) g root k ->
  RI.inf_fetch g root b = RI.FetchOk h b' ->
  IA.DECODE1 p root w = IS.ARun (RBa.code_enc h) (wbr w b') /\ brel (wbr w b') b'
  /\ RB.br_in b' = RB.br_in b /\ RB.br_next b' + RB.br_have b' = RB.br_next b + RB.br_have b
  /\ (exists x, 0 <= x < 2 ^ root /\ x = RB.br_bits_of root b' /\ h = g x)
  /\ RBa.c_bits h <= RB.br_bits b'.
Proof.
  intros w b b' p g root k h Hb Htv Hf.
  destruct Htv as [Hroot Htv].
  unfold RI.inf_fetch in Hf. rewrite fetch_gfetch in Hf.
  unfold IA.DECODE1.
  pose proof Hb as (_ & Hbt & _ & _ & _ & _ & _ & Hbr & _). rewrite Hbt in Hbr.
  match goal with |- IA.DECODE_k _ _ ?si ?sn _ = _ /\ _ =>
    match type of Hf with gfetch _ ?ri _ ?c _ = _ =>
      assert (Ht : forall hold, 0 <= hold ->
                IS.code_at (IS.w_s w) p (si hold) = RBa.code_enc (g (ri hold))
                /\ sn (RBa.code_enc (g (ri hold))) = c (g (ri hold)) /\ c (g (ri hold)) <= 15);
      [| pose proof (decode_k_sim p si sn g ri c (IS.w_s w) Ht) as Hd]
    end
  end.
  { intros hold Hh. cbv beta. rewrite (bitsv_eq hold root ltac:(lia)).
    destruct (Htv _ (land_mask_range hold root ltac:(lia))) as (Ef & Hr & Hcb & _).
    rewrite Ef in Hcb |- *. rewrite (enc_bits _ Hr) in Hcb |- *.
    split; [reflexivity|split; [reflexivity|lia]]. }
  destruct (Hd _ 8%nat w b h b' Hb eq_refl ltac:(lia) Hf) as (E & Hb' & Hin & Hsum & Eh & Lc).
  split; [exact E|]. split; [exact Hb'|]. split; [exact Hin|]. split; [exact Hsum|].
  split; [|exact Lc].
  pose proof Hb' as (Hh' & _ & _ & _ & _ & _ & _ & _ & Hhr' & _).
  exists (RB.br_bits_of root b'). split; [|split; [reflexivity|exact Eh]].
  unfold RB.br_bits_of. apply land_mask_range. lia.
Qed.

(** Sub-table lookup ([inflate.c:1043-1047]), from a root entry [g x] that is a link. *)
Lemma decode2_sim : forall w b b' p g root k x h,
  brel w b -> tview (IS.code_at (IS.w_s w) p) g root k ->
  0 <= x < 2 ^ root -> tsub k (RBa.c_op (g x)) = true -> RBa.c_bits (g x) <= RB.br_bits b ->
  RI.inf_fetch2 g (g x) b = RI.FetchOk h b' ->
  IA.DECODE2 p (RBa.code_enc (g x)) w = IS.ARun (RBa.code_enc h) (wbr w b') /\ brel (wbr w b') b'
  /\ RB.br_in b' = RB.br_in b /\ RB.br_next b' + RB.br_have b' = RB.br_next b + RB.br_have b
  /\ (exists y, 0 <= y < 2 ^ RBa.c_op (g x) /\ h = g (RBa.c_val (g x) + y))
  /\ RBa.c_bits (g x) + RBa.c_bits h <= RB.br_bits b'.
Proof.
  intros w b b' p g root k x h Hb Htv Hx Hsub _ Hf.
  destruct Htv as [Hroot Htv].
  destruct (Htv x Hx) as (Ef & Hr & _ & _ & Hs).
  pose proof Hr as Hr'. unfold code_rng in Hr'.
  rewrite Ef, (enc_op _ Hr) in Hs.
  destruct (Hs Hsub) as (Eb & Hop1 & Hop15 & Hy).
  rewrite (enc_bits _ Hr) in Eb. rewrite (enc_val _ Hr) in Hy.
  cbv zeta in Hy.
  unfold RI.inf_fetch2 in Hf. rewrite fetch2_gfetch in Hf.
  unfold IA.DECODE2.
  pose proof Hb as (_ & Hbt & _ & _ & _ & _ & _ & Hbr & _). rewrite Hbt in Hbr.
  match goal with |- IA.DECODE_k _ _ ?si ?sn _ = _ /\ _ =>
    match type of Hf with gfetch _ ?ri _ ?c _ = _ =>
      assert (Ht : forall hold, 0 <= hold ->
                IS.code_at (IS.w_s w) p (si hold) = RBa.code_enc (g (ri hold))
                /\ sn (RBa.code_enc (g (ri hold))) = c (g (ri hold)) /\ c (g (ri hold)) <= 15);
      [| pose proof (decode_k_sim p si sn g ri c (IS.w_s w) Ht) as Hd]
    end
  end.
  { intros hold Hh. cbv beta.
    rewrite (enc_val _ Hr), (enc_bits _ Hr), (enc_op _ Hr).
    rewrite (bitsv_eq hold (RBa.c_bits (g x) + RBa.c_op (g x)) ltac:(lia)).
    assert (Hyr : 0 <= Z.shiftr (Z.land hold (Z.shiftl 1 (RBa.c_bits (g x) + RBa.c_op (g x)) - 1))
                                (RBa.c_bits (g x)) < 2 ^ RBa.c_op (g x))
      by (apply sub_index_range; lia).
    destruct (Hy _ Hyr) as (Ez & Hrz & Hcbz & _ & _).
    pose proof Hrz as Hrz'. unfold code_rng in Hrz'.
    rewrite Ez, (enc_bits _ Hrz) in Hcbz.
    split; [exact Ez|]. rewrite (enc_bits _ Hrz).
    split; [apply wrap32_id; lia|lia]. }
  destruct (Hd _ 8%nat w b h b' Hb eq_refl ltac:(lia) Hf) as (E & Hb' & Hin & Hsum & Eh & Lc).
  cbv beta in Eh, Lc.
  split; [exact E|]. split; [exact Hb'|]. split; [exact Hin|]. split; [exact Hsum|].
  split; [|exact Lc].
  eexists. split; [|exact Eh].
  apply sub_index_range; lia.
Qed.

(** S5 reads the fields of a packed entry back. *)
Lemma code_op_enc : forall h, code_rng h -> IS.code_op (RBa.code_enc h) = RBa.c_op h.
Proof. exact enc_op. Qed.
Lemma code_bits_enc : forall h, code_rng h -> IS.code_bits (RBa.code_enc h) = RBa.c_bits h.
Proof. exact enc_bits. Qed.
Lemma code_val_enc : forall h, code_rng h -> IS.code_val (RBa.code_enc h) = RBa.c_val h.
Proof. exact enc_val. Qed.
