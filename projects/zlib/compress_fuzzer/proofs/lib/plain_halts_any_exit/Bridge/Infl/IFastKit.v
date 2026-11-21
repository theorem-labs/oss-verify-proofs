(** * Bridge.Infl.IFastKit — pair I16 kit: the per-trip relation of S5's and RT's
    [inflate_fast] loops, and the facts every trip step uses.

    S5 runs the loop on an [ffs] (its locals, including the output array), RT on an [IfSt].
    [frel N f s] relates them: the four scalars agree, and the two output buffers agree on
    the whole buffer [[0, N)] (S5's array has exactly [N] slots).  [rng s] is the C's ranges
    on RT's side (bits at most 39, hold below 2^bits).  [xrel x c sS N] relates the read-only
    contexts and carries the table views.

    [xent]/[xview] are the extra table-entry facts the fast path needs beyond [IInv.tent]
    (see NEEDS.md of pci-fast): extra bits at most 5 (lengths) / 13 (distances), and every
    entry the fast path chains on is a [tsub] link. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateFast.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Module IF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z.InflateFast.
Module RIF := OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel.InflateFast.

(* ------------------------------------------------------------------------- *)
(* 1.  Arithmetic                                                            *)
(* ------------------------------------------------------------------------- *)

Lemma fk_wrap32_u32 : forall z, wrap32 z = RBa.u32 z.
Proof. intros z. unfold wrap32, RBa.u32. change 4294967295 with (Z.ones 32). now rewrite Z.land_ones by lia. Qed.

Lemma fk_wrap8_u8 : forall z, wrap8 z = RBa.u8 z.
Proof. intros z. unfold wrap8, RBa.u8. change 255 with (Z.ones 8). now rewrite Z.land_ones by lia. Qed.

Lemma fk_pow_pos : forall n, 0 <= n -> 0 < 2 ^ n.
Proof. intros n Hn. apply Z.pow_pos_nonneg; lia. Qed.

Lemma fk_land_low : forall h n, 0 <= n -> Z.land h (Z.shiftl 1 n - 1) = h mod 2 ^ n.
Proof.
  intros h n Hn. rewrite Z.shiftl_1_l. replace (2 ^ n - 1) with (Z.ones n).
  - now apply Z.land_ones.
  - rewrite Z.ones_equiv. lia.
Qed.

Lemma fk_zmask : forall n, 0 <= n <= 32 -> IF.zmask n = Z.shiftl 1 n - 1.
Proof.
  intros n Hn. unfold IF.zmask. apply wrap32_id. rewrite Z.shiftl_1_l.
  pose proof (fk_pow_pos n ltac:(lia)).
  assert (2 ^ n <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma fk_low_wrap32 : forall h n, 0 <= n <= 32 ->
  Z.land (wrap32 h) (Z.shiftl 1 n - 1) = Z.land h (Z.shiftl 1 n - 1).
Proof.
  intros h n Hn. rewrite !fk_land_low by lia. rewrite wrap32_mod.
  apply Z.mod_mod_divide. exists (2 ^ (32 - n)). rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

Lemma fk_low_range : forall h n, 0 <= n -> 0 <= Z.land h (Z.shiftl 1 n - 1) < 2 ^ n.
Proof. intros h n Hn. rewrite fk_land_low by lia. apply Z.mod_pos_bound. now apply fk_pow_pos. Qed.

Lemma fk_pull_bound : forall h b n, 0 <= h < 2 ^ n -> 0 <= b < 256 -> 0 <= n ->
  0 <= h + b * 2 ^ n < 2 ^ (n + 8).
Proof.
  intros h b n Hh Hb Hn. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  pose proof (fk_pow_pos n Hn). nia.
Qed.

Lemma fk_drop_bound : forall h b n, 0 <= h < 2 ^ b -> 0 <= n <= b ->
  0 <= Z.shiftr h n < 2 ^ (b - n).
Proof.
  intros h b n Hh Hn. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (fk_pow_pos n ltac:(lia)). split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; [lia|]. rewrite <- Z.pow_add_r by lia.
    replace (n + (b - n)) with b by lia. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 2.  Packed table entries                                                  *)
(* ------------------------------------------------------------------------- *)

Lemma fk_code_op : forall h, code_rng h -> IS.code_op (RBa.code_enc h) = RBa.c_op h.
Proof.
  intros [op bits val] (Ho & Hb & Hv). unfold IS.code_op, RBa.code_enc.
  cbn [RBa.c_op RBa.c_bits RBa.c_val] in *.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  replace (op + 256 * bits + 65536 * val) with (op + (bits + 256 * val) * 256) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma fk_code_bits : forall h, code_rng h -> IS.code_bits (RBa.code_enc h) = RBa.c_bits h.
Proof.
  intros [op bits val] (Ho & Hb & Hv). unfold IS.code_bits, RBa.code_enc.
  cbn [RBa.c_op RBa.c_bits RBa.c_val] in *.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace (op + 256 * bits + 65536 * val) with (op + (bits + 256 * val) * 256) by ring.
  rewrite Z.div_add by lia. rewrite (Z.div_small op 256) by lia. rewrite Z.add_0_l.
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  replace (bits + 256 * val) with (bits + val * 256) by ring.
  rewrite Z.mod_add by lia. apply Z.mod_small; lia.
Qed.

Lemma fk_code_val : forall h, code_rng h -> IS.code_val (RBa.code_enc h) = RBa.c_val h.
Proof.
  intros [op bits val] (Ho & Hb & Hv). unfold IS.code_val, RBa.code_enc.
  cbn [RBa.c_op RBa.c_bits RBa.c_val] in *.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  replace (op + 256 * bits + 65536 * val) with ((op + 256 * bits) + val * 65536) by ring.
  rewrite Z.div_add by lia. rewrite (Z.div_small (op + 256 * bits) 65536) by lia. rewrite Z.add_0_l.
  change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

(** The extra entry facts (NEEDS N2, N3), on S5's packed entry like [tent]. *)
Definition xent (k : tkind) (e : Z) : Prop :=
  let op := IS.code_op e in
  match k with
  | KCodes => True
  | KLens => (Z.land op 16 <> 0 -> Z.land op 15 <= 5)
             /\ (op <> 0 -> Z.land op 16 = 0 -> Z.land op 64 = 0 -> Z.land op 240 = 0)
  | KDists => (Z.land op 16 <> 0 -> Z.land op 15 <= 13)
              /\ (Z.land op 16 = 0 -> Z.land op 64 = 0 -> Z.land op 240 = 0)
  end.

(** [xent] on every entry [tview] describes. *)
Definition xview (f : Z -> Z) (root : Z) (k : tkind) : Prop :=
  forall x, 0 <= x < 2 ^ root ->
    xent k (f x) /\
    (tsub k (IS.code_op (f x)) = true ->
       forall y, 0 <= y < 2 ^ IS.code_op (f x) -> xent k (f (IS.code_val (f x) + y))).

(** [IInv.tent] now carries [xent] (NEEDS.md N2, N3, adopted 2026-10-20). *)
Lemma tent_xent : forall k e, tent k e -> xent k e.
Proof. intros [| |] e H; unfold tent, xent in *; cbv zeta in *; tauto. Qed.

(** So [xview] is a corollary of [tview]. *)
Lemma xview_of_tview : forall f g root k, (forall e, tent k e -> xent k e) ->
  tview f g root k -> xview f root k.
Proof.
  intros f g root k Himp [_ Hall] x Hx.
  destruct (Hall x Hx) as (_ & _ & _ & Ht & Hsub).
  split; [exact (Himp _ Ht)|].
  intros Hts y Hy. destruct (Hsub Hts) as (_ & _ & _ & Hy').
  destruct (Hy' y Hy) as (_ & _ & _ & _ & Ht2). exact (Himp _ Ht2).
Qed.

Definition xviews_blk (w : IS.iw) : Prop :=
  let s := IS.w_s w in
  xview (IS.code_at s (IS.is_lencode s)) (IS.is_lenbits s) KLens
  /\ xview (IS.code_at s (IS.is_distcode s)) (IS.is_distbits s) KDists.

(** The entry facts on RT's record. *)
Definition lent (h : RBa.Code) : Prop :=
  code_rng h
  /\ (Z.land (RBa.c_op h) 16 <> 0 ->
        Z.land (RBa.c_op h) 15 <= 5 /\ RBa.c_val h + 2 ^ Z.land (RBa.c_op h) 15 <= 259)
  /\ (RBa.c_op h <> 0 -> Z.land (RBa.c_op h) 16 = 0 -> Z.land (RBa.c_op h) 64 = 0 ->
        Z.land (RBa.c_op h) 240 = 0).

Definition dent (h : RBa.Code) : Prop :=
  code_rng h /\ RBa.c_op h <> 0
  /\ (Z.land (RBa.c_op h) 16 <> 0 ->
        Z.land (RBa.c_op h) 15 <= 13 /\ 1 <= RBa.c_val h
        /\ RBa.c_val h + 2 ^ Z.land (RBa.c_op h) 15 <= 32769)
  /\ (Z.land (RBa.c_op h) 16 = 0 -> Z.land (RBa.c_op h) 64 = 0 -> Z.land (RBa.c_op h) 240 = 0).

Definition kent (k : tkind) (h : RBa.Code) : Prop :=
  match k with KLens => lent h | KDists => dent h | KCodes => code_rng h end.

Lemma fk_kent : forall k h, code_rng h -> tent k (RBa.code_enc h) -> xent k (RBa.code_enc h) -> kent k h.
Proof.
  intros k h Hr Ht Hx. unfold tent, xent in *. cbv zeta in Ht, Hx.
  rewrite fk_code_op, fk_code_val in Ht by exact Hr. rewrite fk_code_op in Hx by exact Hr.
  destruct k; cbn [kent]; unfold lent, dent; tauto.
Qed.

(** What a decode reads, from [tview] + [xview], on RT's records. *)
Lemma fk_view_at : forall F g root k x,
  tview F g root k -> xview F root k -> 0 <= x < 2 ^ root ->
  F x = RBa.code_enc (g x) /\ kent k (g x) /\ RBa.c_bits (g x) <= root
  /\ (tsub k (RBa.c_op (g x)) = true ->
       RBa.c_bits (g x) = root /\ 1 <= RBa.c_op (g x) /\ root + RBa.c_op (g x) <= 15
       /\ forall y, 0 <= y < 2 ^ RBa.c_op (g x) ->
            F (RBa.c_val (g x) + y) = RBa.code_enc (g (RBa.c_val (g x) + y))
            /\ kent k (g (RBa.c_val (g x) + y))
            /\ RBa.c_bits (g (RBa.c_val (g x) + y)) <= 15 - root
            /\ tsub k (RBa.c_op (g (RBa.c_val (g x) + y))) = false).
Proof.
  intros F g root k x [Hroot Hall] Hxv Hx.
  destruct (Hall x Hx) as (Heq & Hr & Hb & Ht & Hsub).
  destruct (Hxv x Hx) as (Hxe & Hxsub).
  rewrite Heq in Hb, Ht, Hsub, Hxe, Hxsub.
  rewrite fk_code_bits in Hb by exact Hr.
  rewrite fk_code_op in Hsub, Hxsub by exact Hr.
  rewrite fk_code_val in Hsub, Hxsub by exact Hr.
  split; [exact Heq|]. split; [now apply fk_kent|]. split; [exact Hb|].
  intros Hts. destruct (Hsub Hts) as (Hb2 & Ho1 & Ho2 & Hy).
  rewrite fk_code_bits in Hb2 by exact Hr.
  split; [exact Hb2|]. split; [exact Ho1|]. split; [exact Ho2|].
  intros y Hyr. destruct (Hy y Hyr) as (Heq2 & Hr2 & Hb3 & Hts2 & Ht2).
  pose proof (Hxsub Hts y Hyr) as Hxe2. cbv zeta in Heq2, Hb3, Hts2, Ht2.
  rewrite Heq2 in Hb3, Hts2, Ht2, Hxe2.
  rewrite fk_code_bits in Hb3 by exact Hr2. rewrite fk_code_op in Hts2 by exact Hr2.
  split; [exact Heq2|]. split; [now apply fk_kent|]. split; [exact Hb3|exact Hts2].
Qed.

(* ------------------------------------------------------------------------- *)
(* 3.  The relations                                                         *)
(* ------------------------------------------------------------------------- *)

(** RT's absolute bit position: the next unconsumed input bit. *)
Definition Q (s : RIF.IfSt) : Z := 8 * RIF.f_in s - RIF.f_bits s.

Record frel (N : Z) (f : IF.ffs) (s : RIF.IfSt) : Prop := mkFrel {
  fr_in   : IF.f_in f = RIF.f_in s;
  fr_out  : IF.f_out f = RIF.f_out s;
  fr_hold : IF.f_hold f = RIF.f_hold s;
  fr_bits : IF.f_bits f = RIF.f_bits s;
  fr_len  : arr_len (IF.f_ob f) = N;
  fr_buf  : arr_rel (IF.f_ob f) (RIF.f_buf s) 0 N }.

Record rng (s : RIF.IfSt) : Prop := mkRng {
  rg_bits : 0 <= RIF.f_bits s <= 39;
  rg_hold : 0 <= RIF.f_hold s < 2 ^ RIF.f_bits s;
  rg_in   : 0 <= RIF.f_in s;
  rg_out  : 0 <= RIF.f_out s }.

Record xrel (x : IF.ffx) (c : RIF.IfCtx) (sS : IS.inflate_state) (N : Z) : Prop := mkXrel {
  xr_in     : forall i, 0 <= i -> arr_get (IF.x_input x) i = RIF.f_inbuf c i /\ 0 <= RIF.f_inbuf c i < 256;
  xr_last   : IF.x_last x = RIF.f_last c;
  xr_end    : IF.x_end x = RIF.f_end c;
  xr_N      : RIF.f_end c + 257 = N;
  xr_Nlt    : N < 2 ^ 31;
  xr_beg    : IF.x_beg x = 0;
  xr_fbeg   : RIF.f_beg c = 0;
  xr_whave  : RIF.f_whave c = 0;
  xr_sane   : RIF.f_sane c = 1;
  xr_lmask  : IF.x_lmask x = RIF.f_lmask c;
  xr_flmask : RIF.f_lmask c = Z.shiftl 1 (IS.is_lenbits sS) - 1;
  xr_dmask  : IF.x_dmask x = RIF.f_dmask c;
  xr_fdmask : RIF.f_dmask c = Z.shiftl 1 (IS.is_distbits sS) - 1;
  xr_lview  : tview (IS.code_at sS (IS.is_lencode sS)) (RIF.f_lcode c) (IS.is_lenbits sS) KLens;
  xr_dview  : tview (IS.code_at sS (IS.is_distcode sS)) (RIF.f_dcode c) (IS.is_distbits sS) KDists;
  xr_lx     : xview (IS.code_at sS (IS.is_lencode sS)) (IS.is_lenbits sS) KLens;
  xr_dx     : xview (IS.code_at sS (IS.is_distcode sS)) (IS.is_distbits sS) KDists }.

(* ------------------------------------------------------------------------- *)
(* 4.  The primitive moves                                                   *)
(* ------------------------------------------------------------------------- *)

Lemma fk_drop : forall N f s n, frel N f s -> frel N (IF.fdrop f n) (RIF.if_drop n s).
Proof.
  intros N f s n [Hi Ho Hh Hb Hl Hbuf]. unfold IF.fdrop, RIF.if_drop.
  constructor; cbn [IF.fset_bits IF.fset_hold IF.f_in IF.f_out IF.f_hold IF.f_bits IF.f_ob
                    RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits RIF.f_buf]; try assumption.
  - now rewrite Hh.
  - now rewrite Hb, fk_wrap32_u32.
Qed.

Lemma fk_drop_rng : forall n s, rng s -> 0 <= n <= RIF.f_bits s ->
  rng (RIF.if_drop n s) /\ RIF.f_bits (RIF.if_drop n s) = RIF.f_bits s - n
  /\ Q (RIF.if_drop n s) = Q s + n.
Proof.
  intros n s [Rb Rh Ri Ro] Hn. unfold Q, RIF.if_drop.
  cbn [RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits].
  rewrite RBa.u32_id by lia.
  split; [|split; lia]. constructor; cbn [RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits]; try lia.
  now apply fk_drop_bound.
Qed.

Lemma fk_pull : forall x c sS N f s, xrel x c sS N -> frel N f s -> rng s -> RIF.f_bits s < 31 ->
  frel N (IF.fpull x f) (RIF.if_load1 c s) /\ rng (RIF.if_load1 c s)
  /\ RIF.f_bits (RIF.if_load1 c s) = RIF.f_bits s + 8 /\ RIF.f_in (RIF.if_load1 c s) = RIF.f_in s + 1
  /\ Q (RIF.if_load1 c s) = Q s.
Proof.
  intros x c sS N f s X [Hi Ho Hh Hb Hl Hbuf] [Rb Rh Ri Ro] H31.
  destruct (xr_in _ _ _ _ X (RIF.f_in s) Ri) as [Hin Hbyte].
  pose proof (fk_pull_bound _ _ _ Rh Hbyte ltac:(lia)) as Hpb.
  assert (H39 : 2 ^ (RIF.f_bits s + 8) <= 2 ^ 39) by (apply Z.pow_le_mono_r; lia).
  unfold IF.fpull, RIF.if_load1, Q.
  cbn [IF.fset_in IF.fset_bits IF.fset_hold IF.f_in IF.f_out IF.f_hold IF.f_bits IF.f_ob
       RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits RIF.f_buf].
  rewrite Hi, Hb, Hh, Hin.
  assert (Hsh : shl64 (RIF.f_inbuf c (RIF.f_in s)) (RIF.f_bits s)
                = Z.shiftl (RIF.f_inbuf c (RIF.f_in s)) (RIF.f_bits s)).
  { unfold shl64. apply wrap64_id. rewrite Z.shiftl_mul_pow2 by lia.
    pose proof (fk_pow_pos (RIF.f_bits s) ltac:(lia)). split; [nia|].
    assert (2 ^ 39 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). nia. }
  rewrite Hsh. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite wrap64_id.
  2:{ assert (2 ^ 39 < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia). lia. }
  rewrite wrap32_id by lia.
  split; [constructor; cbn [IF.f_in IF.f_out IF.f_hold IF.f_bits IF.f_ob RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits RIF.f_buf]; first [reflexivity | assumption]|].
  split; [constructor; cbn [RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits]; lia|].
  split; [reflexivity|]. split; [reflexivity|]. lia.
Qed.

Lemma fk_set_len : forall N f s v, frel N f s -> frel N (IF.fset_len f v) s.
Proof. intros N f s v [Hi Ho Hh Hb Hl Hbuf]. now constructor. Qed.
Lemma fk_set_dist : forall N f s v, frel N f s -> frel N (IF.fset_dist f v) s.
Proof. intros N f s v [Hi Ho Hh Hb Hl Hbuf]. now constructor. Qed.
Lemma fk_set_op : forall N f s v, frel N f s -> frel N (IF.fset_op f v) s.
Proof. intros N f s v [Hi Ho Hh Hb Hl Hbuf]. now constructor. Qed.
Lemma fk_set_from : forall N f s v, frel N f s -> frel N (IF.fset_from f v) s.
Proof. intros N f s v [Hi Ho Hh Hb Hl Hbuf]. now constructor. Qed.

(** [*out++ = v], the literal write. *)
Lemma fk_put : forall N f s v, frel N f s -> 0 <= RIF.f_out s < N ->
  frel N (IF.fset_out (IF.fset_ob f (arr_set (IF.f_ob f) (IF.f_out f) v)) (IF.f_out f + 1))
         (RIF.if_put v s).
Proof.
  intros N f s v [Hi Ho Hh Hb Hl Hbuf] Hout. unfold RIF.if_put.
  constructor; cbn [IF.fset_out IF.fset_ob IF.f_in IF.f_out IF.f_hold IF.f_bits IF.f_ob
                    RIF.f_in RIF.f_out RIF.f_hold RIF.f_bits RIF.f_buf]; try congruence.
  - now rewrite arr_len_set.
  - rewrite Ho. apply arr_rel_set; [exact Hbuf|]. intros _. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(* 5.  Copies                                                                *)
(* ------------------------------------------------------------------------- *)

(** [n] single-byte copies on S5's side, innermost first (as RT's [if_copyn]). *)
Fixpoint cpn (n : nat) (x : IF.ffx) (f : IF.ffs) : IF.ffs :=
  match n with O => f | S k => cpn k x (IF.cp1 x f) end.

Lemma fk_cp1 : forall x c N f s i, frel N f s -> IF.f_from f = IF.FOut i ->
  0 <= i < N -> 0 <= RIF.f_out s < N ->
  frel N (IF.cp1 x f) (RIF.if_put (RIF.if_read c s (RIF.SrcOut i)) s)
  /\ IF.f_from (IF.cp1 x f) = IF.FOut (i + 1).
Proof.
  intros x c N f s i F Hfr Hi Ho. unfold IF.cp1. rewrite Hfr.
  cbn [IF.from_succ RIF.if_read].
  replace (arr_get (IF.f_ob f) i) with (RIF.f_buf s i) by (symmetry; apply (fr_buf _ _ _ F); lia).
  split; [|cbn [IF.f_from IF.fset_from IF.fset_out IF.fset_ob]; rewrite Hfr; reflexivity].
  pose proof (fk_put N f s (RIF.f_buf s i) F Ho) as H.
  destruct H as [Hi' Ho' Hh' Hb' Hl' Hbuf']. constructor; assumption.
Qed.

Lemma fk_cpn : forall x c n N f s i, frel N f s -> IF.f_from f = IF.FOut i ->
  0 <= i < RIF.f_out s -> RIF.f_out s + Z.of_nat n <= N ->
  frel N (cpn n x f) (fst (RIF.if_copyn n c s (RIF.SrcOut i)))
  /\ IF.f_from (cpn n x f) = IF.FOut (i + Z.of_nat n).
Proof.
  intros x c n. induction n as [|n IH]; intros N f s i F Hfr Hi Hn.
  - cbn [cpn RIF.if_copyn fst]. rewrite Z.add_0_r. now split.
  - cbn [cpn RIF.if_copyn].
    destruct (fk_cp1 x c N f s i F Hfr ltac:(lia) ltac:(lia)) as [F1 Hfr1].
    cbn [RIF.if_bump].
    destruct (IH N _ _ (i + 1) F1 Hfr1) as [F2 Hfr2].
    + cbn [RIF.if_put RIF.f_out]. lia.
    + cbn [RIF.if_put RIF.f_out]. lia.
    + split; [exact F2|]. rewrite Hfr2. f_equal. lia.
Qed.

Lemma fk_flen_cp1 : forall x f, IF.f_len (IF.cp1 x f) = IF.f_len f.
Proof. intros x [fi fo fh fb fl fd fop ffr fob]. reflexivity. Qed.

Lemma fk_cp1_len : forall x f v, IF.cp1 x (IF.fset_len f v) = IF.fset_len (IF.cp1 x f) v.
Proof. intros x [fi fo fh fb fl fd fop ffr fob] v. reflexivity. Qed.

Lemma fk_cpn_len : forall n x f v, cpn n x (IF.fset_len f v) = IF.fset_len (cpn n x f) v.
Proof.
  induction n as [|n IH]; intros x f v; [reflexivity|].
  cbn [cpn]. rewrite fk_cp1_len. apply IH.
Qed.

Lemma fk_len_len : forall f a b, IF.fset_len (IF.fset_len f a) b = IF.fset_len f b.
Proof. intros [fi fo fh fb fl fd fop ffr fob] a b. reflexivity. Qed.

Lemma fk_cpn_add : forall a b x f, cpn (a + b) x f = cpn b x (cpn a x f).
Proof. induction a as [|a IH]; intros b x f; [reflexivity|]. cbn [cpn Nat.add]. apply IH. Qed.

Definition do3_body (x : IF.ffx) : IF.ffs -> bool * IF.ffs :=
  fun f => let f := IF.cp1 x (IF.cp1 x (IF.cp1 x f)) in
           let f := IF.fset_len f (wrap32 (IF.f_len f - 3)) in
           (2 <? IF.f_len f, f).

Lemma fk_do3_eq : forall x f, IF.copy_do3 x f = loopZ (IF.f_len f + 1) (do3_body x) f.
Proof. reflexivity. Qed.

Lemma fk_do3_body : forall x f, do3_body x f
  = (2 <? wrap32 (IF.f_len f - 3), IF.fset_len (cpn 3 x f) (wrap32 (IF.f_len f - 3))).
Proof.
  intros x f. unfold do3_body. cbv zeta. cbn [cpn IF.f_len IF.fset_len].
  rewrite !fk_flen_cp1. reflexivity.
Qed.

Lemma fk_do3_loop : forall x q f n r, (1 <= q)%nat -> IF.f_len f = 3 * Z.of_nat q + r ->
  0 <= r <= 2 -> Z.of_nat q <= n -> 3 * Z.of_nat q + r < 2 ^ 32 ->
  loopZ n (do3_body x) f = IF.fset_len (cpn (3 * q) x f) r.
Proof.
  intros x q. induction q as [|q IH]; intros f n r Hq Hl Hr Hn Hlt; [lia|].
  rewrite loopZ_step by lia. rewrite fk_do3_body, Hl.
  rewrite (wrap32_id (3 * Z.of_nat (S q) + r - 3)) by lia.
  cbv beta iota.
  destruct q as [|q].
  - replace (2 <? 3 * Z.of_nat 1 + r - 3) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (3 * Z.of_nat 1 + r - 3) with r by lia. reflexivity.
  - replace (2 <? 3 * Z.of_nat (S (S q)) + r - 3) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (IH _ (n - 1) r) by (cbn [IF.f_len IF.fset_len]; lia).
    rewrite fk_cpn_len, fk_len_len.
    replace (3 * S (S q))%nat with (3 + 3 * S q)%nat by lia.
    rewrite fk_cpn_add. reflexivity.
Qed.

Lemma fk_tail : forall x g r, 0 <= r <= 2 ->
  IF.copy_tail x (IF.fset_len g r) = IF.fset_len (cpn (Z.to_nat r) x g) r.
Proof.
  intros x g r Hr. unfold IF.copy_tail. cbn [IF.f_len IF.fset_len].
  assert (r = 0 \/ r = 1 \/ r = 2) as [ -> | [ -> | -> ] ] by lia.
  - reflexivity.
  - cbn [Z.eqb negb Z.ltb Z.compare]. rewrite fk_cp1_len. reflexivity.
  - cbn [Z.eqb negb Z.ltb Z.compare]. rewrite fk_cp1_len.
    cbn [IF.f_len IF.fset_len Z.ltb Z.compare]. rewrite fk_cp1_len. reflexivity.
Qed.

(** S5's direct copy is [len] single-byte copies. *)
Lemma fk_copy_s5 : forall x f, 3 <= IF.f_len f <= 258 ->
  IF.copy_tail x (IF.copy_do3 x f)
  = IF.fset_len (cpn (Z.to_nat (IF.f_len f)) x f) (IF.f_len f mod 3).
Proof.
  intros x f Hl. rewrite fk_do3_eq.
  pose proof (Z.div_mod (IF.f_len f) 3 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (IF.f_len f) 3 ltac:(lia)) as Hm.
  assert (Hq : 1 <= IF.f_len f / 3) by (apply Z.div_le_lower_bound; lia).
  rewrite (fk_do3_loop x (Z.to_nat (IF.f_len f / 3)) f _ (IF.f_len f mod 3)) by lia.
  rewrite fk_tail by lia. rewrite <- fk_cpn_add.
  f_equal. f_equal. lia.
Qed.

Lemma fk_copyn_add : forall a b c s r,
  RIF.if_copyn (a + b) c s r
  = RIF.if_copyn b c (fst (RIF.if_copyn a c s r)) (snd (RIF.if_copyn a c s r)).
Proof. induction a as [|a IH]; intros b c s r; [reflexivity|]. cbn [RIF.if_copyn Nat.add]. apply IH. Qed.

Lemma fk_copy3w_ok : forall k c s r len, 0 <= len < 2 ^ 32 -> len / 3 < Z.of_nat k ->
  RIF.if_copy3w k c s r len = Some (RIF.if_copyn (3 * Z.to_nat (len / 3)) c s r, len mod 3).
Proof.
  induction k as [|k IH]; intros c s r len Hl Hk.
  - pose proof (Z.div_pos len 3 ltac:(lia) ltac:(lia)). lia.
  - cbn [RIF.if_copy3w]. destruct (Z.ltb_spec 2 len) as [H2|H2].
    + destruct (RIF.if_copyn 3 c s r) as [s1 r1] eqn:E.
      rewrite RBa.u32_id by lia.
      assert (Hd : len / 3 = (len - 3) / 3 + 1).
      { replace len with ((len - 3) + 1 * 3) at 1 by ring. now rewrite Z.div_add by lia. }
      assert (Hm : len mod 3 = (len - 3) mod 3).
      { replace len with ((len - 3) + 1 * 3) at 1 by ring. now rewrite Z.mod_add by lia. }
      pose proof (Z.div_pos (len - 3) 3 ltac:(lia) ltac:(lia)).
      rewrite IH by lia. rewrite Hd, Hm.
      replace (3 * Z.to_nat ((len - 3) / 3 + 1))%nat with (3 + 3 * Z.to_nat ((len - 3) / 3))%nat by lia.
      rewrite fk_copyn_add, E. reflexivity.
    + rewrite (Z.div_small len 3) by lia. rewrite (Z.mod_small len 3) by lia. reflexivity.
Qed.

Lemma fk_copy3w_none : forall k c s r len, 3 * Z.of_nat k <= len < 2 ^ 32 ->
  RIF.if_copy3w k c s r len = None.
Proof.
  induction k as [|k IH]; intros c s r len Hl; [reflexivity|].
  cbn [RIF.if_copy3w]. replace (2 <? len) with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (RIF.if_copyn 3 c s r) as [s1 r1]. rewrite RBa.u32_id by lia. apply IH. lia.
Qed.

Lemma fk_copytail : forall c s r l, 0 <= l <= 2 ->
  RIF.if_copytail c s r l = fst (RIF.if_copyn (Z.to_nat l) c s r).
Proof.
  intros c s r l Hl. unfold RIF.if_copytail.
  assert (l = 0 \/ l = 1 \/ l = 2) as [ -> | [ -> | -> ] ] by lia; reflexivity.
Qed.

Lemma fk_copydirect_ok : forall c s r len, 3 <= len <= 258 ->
  RIF.if_copydirect c s r len = Some (fst (RIF.if_copyn (Z.to_nat len) c s r)).
Proof.
  intros c s r len Hl. unfold RIF.if_copydirect.
  destruct (RIF.if_copyn 3 c s r) as [s1 r1] eqn:E.
  rewrite RBa.u32_id by lia. unfold RIF.copy_fuel.
  pose proof (Z.div_mod (len - 3) 3 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (len - 3) 3 ltac:(lia)) as Hm.
  pose proof (Z.div_pos (len - 3) 3 ltac:(lia) ltac:(lia)) as Hq.
  rewrite fk_copy3w_ok by lia.
  destruct (RIF.if_copyn (3 * Z.to_nat ((len - 3) / 3)) c s1 r1) as [s2 r2] eqn:E2.
  rewrite fk_copytail by lia. f_equal.
  replace (Z.to_nat len) with (3 + (3 * Z.to_nat ((len - 3) / 3) + Z.to_nat ((len - 3) mod 3)))%nat by lia.
  rewrite fk_copyn_add, E. cbn [fst snd]. rewrite fk_copyn_add, E2. reflexivity.
Qed.

Lemma fk_copydirect_none : forall c s r len, 0 <= len < 3 -> RIF.if_copydirect c s r len = None.
Proof.
  intros c s r len Hl. unfold RIF.if_copydirect.
  destruct (RIF.if_copyn 3 c s r) as [s1 r1].
  assert (Hu : RBa.u32 (len - 3) = len - 3 + 4294967296).
  { unfold RBa.u32. symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
  rewrite Hu. unfold RIF.copy_fuel. rewrite fk_copy3w_none by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(* 6.  One level of each decode, with the intermediate states as arguments   *)
(* ------------------------------------------------------------------------- *)

(** Unfolding a decode level by [cbn] substitutes every [let]-bound state into
    every use (a 200 KB term for one [dodist] level).  These definitions cut the
    body at its states instead; each [*_S] lemma is [reflexivity]. *)

(** RT, [if_dodist]. *)
Definition rd_win (c : RIF.IfCtx) (len : Z) (s3 : RIF.IfSt) (dist od : Z) : RIF.IfBody :=
  let ow := RBa.u32 (dist - od) in
  if Z.ltb (RIF.f_whave c) ow && negb (Z.eqb (RIF.f_sane c) 0) then RIF.BodyBad s3 RIF.MSG_DIST_FAR
  else let '(s4, r4, len4) := RIF.if_winphase c s3 dist ow len in
       match RIF.if_copy3w RIF.copy_fuel c s4 r4 len4 with
       | None => RIF.BodyFuel
       | Some (s5, r5, l5) => RIF.BodyOk (RIF.if_copytail c s5 r5 l5)
       end.

Definition rd_tail (c : RIF.IfCtx) (len : Z) (s3 : RIF.IfSt) (dist : Z) : RIF.IfBody :=
  let od := RBa.u32 (RIF.f_out s3 - RIF.f_beg c) in
  if Z.ltb od dist then rd_win c len s3 dist od
  else match RIF.if_copydirect c s3 (RIF.SrcOut (RIF.f_out s3 - dist)) len with
       | None => RIF.BodyFuel
       | Some s5 => RIF.BodyOk s5
       end.

Definition rd_load2 (c : RIF.IfCtx) (e : Z) (s1 : RIF.IfSt) : RIF.IfSt :=
  if Z.ltb (RIF.f_bits s1) e
  then let sa := RIF.if_load1 c s1 in if Z.ltb (RIF.f_bits sa) e then RIF.if_load1 c sa else sa
  else s1.

Definition rd_base (c : RIF.IfCtx) (len : Z) (s1 : RIF.IfSt) (h : RBa.Code) : RIF.IfBody :=
  let e := Z.land (RBa.c_op h) 15 in
  rd_tail c len (RIF.if_drop e (rd_load2 c e s1)) (RBa.c_val h + RIF.if_low e (rd_load2 c e s1)).

Definition rd_lvl (k : nat) (c : RIF.IfCtx) (len : Z) (s1 : RIF.IfSt) (h : RBa.Code) : RIF.IfBody :=
  if negb (Z.eqb (Z.land (RBa.c_op h) 16) 0) then rd_base c len s1 h
  else if Z.eqb (Z.land (RBa.c_op h) 64) 0
  then RIF.if_dodist k c len s1 (RIF.f_dcode c (RBa.c_val h + RIF.if_low (RBa.c_op h) s1))
  else RIF.BodyBad s1 RIF.MSG_DIST_CODE.

Lemma fk_rd_S : forall k c len s h,
  RIF.if_dodist (S k) c len s h = rd_lvl k c len (RIF.if_drop (RBa.c_bits h) s) h.
Proof. reflexivity. Qed.

(** RT, [if_dolen]. *)
Definition rl_ext (c : RIF.IfCtx) (h : RBa.Code) (s1 : RIF.IfSt) : Z * RIF.IfSt :=
  let e := Z.land (RBa.c_op h) 15 in
  if Z.eqb e 0 then (RBa.c_val h, s1)
  else let sa := if Z.ltb (RIF.f_bits s1) e then RIF.if_load1 c s1 else s1 in
       (RBa.c_val h + RIF.if_low e sa, RIF.if_drop e sa).

Definition rl_dist (c : RIF.IfCtx) (len : Z) (s2 : RIF.IfSt) : RIF.IfBody :=
  let s3 := RIF.if_refill15 c s2 in
  RIF.if_dodist RIF.tbl_fuel c len s3 (RIF.f_dcode c (Z.land (RIF.f_hold s3) (RIF.f_dmask c))).

Definition rl_lvl (k : nat) (c : RIF.IfCtx) (s1 : RIF.IfSt) (h : RBa.Code) : RIF.IfBody :=
  if Z.eqb (RBa.c_op h) 0 then RIF.BodyOk (RIF.if_put (RBa.u8 (RBa.c_val h)) s1)
  else if negb (Z.eqb (Z.land (RBa.c_op h) 16) 0) then
    let '(len, s2) := rl_ext c h s1 in rl_dist c len s2
  else if Z.eqb (Z.land (RBa.c_op h) 64) 0
  then RIF.if_dolen k c s1 (RIF.f_lcode c (RBa.c_val h + RIF.if_low (RBa.c_op h) s1))
  else if negb (Z.eqb (Z.land (RBa.c_op h) 32) 0) then RIF.BodyEob s1
  else RIF.BodyBad s1 RIF.MSG_LIT_LEN_CODE.

Lemma fk_rl_S : forall k c s h,
  RIF.if_dolen (S k) c s h = rl_lvl k c (RIF.if_drop (RBa.c_bits h) s) h.
Proof. intros. cbn [RIF.if_dolen]. unfold rl_lvl, rl_ext, rl_dist. cbv beta zeta. reflexivity. Qed.

Lemma fk_body_eq : forall c s, RIF.if_body c s
  = RIF.if_dolen RIF.tbl_fuel c (RIF.if_refill15 c s)
      (RIF.f_lcode c (Z.land (RIF.f_hold (RIF.if_refill15 c s)) (RIF.f_lmask c))).
Proof. intros. unfold RIF.if_body. cbv beta zeta. reflexivity. Qed.

(** S5, [dodist].  [sd_win] is the window branch, verbatim. *)
Definition sd_win (x : IF.ffx) (f : IF.ffs) (op : Z) : IF.fstep :=
  let op := wrap32 (IF.f_dist f - op) in
  if (IF.x_whave x <? op) && negb (IF.x_sane x =? 0) then
    IF.FBreak (IF.fset_op f op) IS.BAD (Some IF.MSG_ff_invalid_distance_too_far_back)
  else
  let f := IF.fset_op f op in
  let f :=
    if IF.x_wnext x =? 0 then
      let f := IF.fset_from f (IF.FWin (IF.x_wsize x - IF.f_op f)) in
      if IF.f_op f <? IF.f_len f then
        let f := IF.fset_len f (wrap32 (IF.f_len f - IF.f_op f)) in
        let f := IF.copy_op x f in
        IF.fset_from f (IF.FOut (IF.f_out f - IF.f_dist f))
      else f
    else if IF.x_wnext x <? IF.f_op f then
      let f := IF.fset_from f (IF.FWin (IF.x_wsize x + IF.x_wnext x - IF.f_op f)) in
      let f := IF.fset_op f (wrap32 (IF.f_op f - IF.x_wnext x)) in
      if IF.f_op f <? IF.f_len f then
        let f := IF.fset_len f (wrap32 (IF.f_len f - IF.f_op f)) in
        let f := IF.copy_op x f in
        let f := IF.fset_from f (IF.FWin 0) in
        if IF.x_wnext x <? IF.f_len f then
          let f := IF.fset_op f (IF.x_wnext x) in
          let f := IF.fset_len f (wrap32 (IF.f_len f - IF.f_op f)) in
          let f := IF.copy_op x f in
          IF.fset_from f (IF.FOut (IF.f_out f - IF.f_dist f))
        else f
      else f
    else
      let f := IF.fset_from f (IF.FWin (IF.x_wnext x - IF.f_op f)) in
      if IF.f_op f <? IF.f_len f then
        let f := IF.fset_len f (wrap32 (IF.f_len f - IF.f_op f)) in
        let f := IF.copy_op x f in
        IF.fset_from f (IF.FOut (IF.f_out f - IF.f_dist f))
      else f in
  let f := IF.copy_while3 x f in
  IF.FCont (IF.copy_tail x f).

Definition sd_tail (x : IF.ffx) (f : IF.ffs) : IF.fstep :=
  let op := wrap32 (IF.f_out f - IF.x_beg x) in
  if op <? IF.f_dist f then sd_win x f op
  else let f := IF.fset_from f (IF.FOut (IF.f_out f - IF.f_dist f)) in
       let f := IF.copy_do3 x f in
       IF.FCont (IF.copy_tail x f).

Definition sd_load2 (x : IF.ffx) (op : Z) (f : IF.ffs) : IF.ffs :=
  if IF.f_bits f <? op then let f := IF.fpull x f in if IF.f_bits f <? op then IF.fpull x f else f
  else f.

Definition sd_base (x : IF.ffx) (here : Z) (f : IF.ffs) : IF.fstep :=
  let f := IF.fset_dist f (IS.code_val here) in
  let op := Z.land (IS.code_op here) 15 in
  let f := sd_load2 x op f in
  let f := IF.fset_dist f (wrap32 (IF.f_dist f + Z.land (wrap32 (IF.f_hold f)) (IF.zmask op))) in
  let f := IF.fdrop f op in
  sd_tail x f.

Definition sd_lvl (k : nat) (x : IF.ffx) (s : IS.inflate_state) (here : Z) (f : IF.ffs) : IF.fstep :=
  if negb (Z.land (IS.code_op here) 16 =? 0) then sd_base x here f
  else if Z.land (IS.code_op here) 64 =? 0 then
    IF.dodist k x s (IS.code_at s (IS.is_distcode s)
                       (IS.code_val here + Z.land (IF.f_hold f) (IF.zmask (IS.code_op here)))) f
  else IF.FBreak f IS.BAD (Some IF.MSG_ff_invalid_distance_code).

Lemma fk_sd_S : forall k x s here f,
  IF.dodist (S k) x s here f = sd_lvl k x s here (IF.fdrop f (IS.code_bits here)).
Proof. intros. cbn [IF.dodist]. unfold sd_lvl, sd_base, sd_load2, sd_tail, sd_win. cbv beta zeta. reflexivity. Qed.

(** S5, [dolen]. *)
Definition sl_lit (here : Z) (f : IF.ffs) : IF.fstep :=
  let f := IF.fset_ob f (arr_set (IF.f_ob f) (IF.f_out f) (wrap8 (IS.code_val here))) in
  IF.FCont (IF.fset_out f (IF.f_out f + 1)).

Definition sl_ext (x : IF.ffx) (here : Z) (f : IF.ffs) : IF.ffs :=
  let f := IF.fset_len f (IS.code_val here) in
  let op := Z.land (IS.code_op here) 15 in
  if negb (op =? 0) then
    let f := if IF.f_bits f <? op then IF.fpull x f else f in
    let f := IF.fset_len f (wrap32 (IF.f_len f + Z.land (wrap32 (IF.f_hold f)) (IF.zmask op))) in
    IF.fdrop f op
  else f.

Definition sl_dist (x : IF.ffx) (s : IS.inflate_state) (f : IF.ffs) : IF.fstep :=
  let f := IF.fpull2_if x f in
  let here := IS.code_at s (IS.is_distcode s) (Z.land (IF.f_hold f) (IF.x_dmask x)) in
  IF.dodist 4 x s here f.

Definition sl_lvl (k : nat) (x : IF.ffx) (s : IS.inflate_state) (here : Z) (f : IF.ffs) : IF.fstep :=
  if IS.code_op here =? 0 then sl_lit here f
  else if negb (Z.land (IS.code_op here) 16 =? 0) then sl_dist x s (sl_ext x here f)
  else if Z.land (IS.code_op here) 64 =? 0 then
    IF.dolen k x s (IS.code_at s (IS.is_lencode s)
                      (IS.code_val here + Z.land (IF.f_hold f) (IF.zmask (IS.code_op here)))) f
  else if negb (Z.land (IS.code_op here) 32 =? 0) then IF.FBreak f IS.TYPE None
  else IF.FBreak f IS.BAD (Some IF.MSG_ff_invalid_literal_length_code).

Lemma fk_sl_S : forall k x s here f,
  IF.dolen (S k) x s here f = sl_lvl k x s here (IF.fdrop f (IS.code_bits here)).
Proof. intros. cbn [IF.dolen]. unfold sl_lvl, sl_lit, sl_ext, sl_dist. cbv beta zeta. reflexivity. Qed.

Lemma fk_trip_eq : forall x s f, IF.fast_trip x s f
  = IF.dolen 4 x s (IS.code_at s (IS.is_lencode s) (Z.land (IF.f_hold (IF.fpull2_if x f)) (IF.x_lmask x)))
      (IF.fpull2_if x f).
Proof. intros. unfold IF.fast_trip. cbv beta zeta. reflexivity. Qed.

(** [if_dodist] never ends a block. *)
Lemma fk_dodist_not_eob : forall k c len s h s', RIF.if_dodist k c len s h <> RIF.BodyEob s'.
Proof.
  induction k as [|k IH]; intros c len s h s'; [discriminate|].
  rewrite fk_rd_S. unfold rd_lvl.
  destruct (negb (Z.land (RBa.c_op h) 16 =? 0)).
  - unfold rd_base, rd_tail. cbv zeta.
    destruct (_ <? _).
    + unfold rd_win. cbv zeta. destruct (_ && _); [discriminate|].
      destruct (RIF.if_winphase _ _ _ _ _) as [[s4 r4] len4].
      destruct (RIF.if_copy3w _ _ _ _ _) as [[[s5 r5] l5]|]; discriminate.
    + destruct (RIF.if_copydirect _ _ _ _); discriminate.
  - destruct (Z.land (RBa.c_op h) 64 =? 0); [apply IH|discriminate].
Qed.

(** [op & 240 = 0] clears bits 16, 32 and 64. *)
Lemma fk_l240 : forall op, Z.land op 240 = 0 ->
  Z.land op 16 = 0 /\ Z.land op 32 = 0 /\ Z.land op 64 = 0.
Proof.
  intros op H.
  assert (G : forall m, Z.land 240 m = m -> Z.land op m = 0).
  { intros m Hm. rewrite <- Hm, Z.land_assoc, H. apply Z.land_0_l. }
  split; [apply G; reflexivity|]. split; apply G; reflexivity.
Qed.
