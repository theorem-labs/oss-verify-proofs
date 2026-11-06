(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), part Q:
   pnQ proves PvB_NCut.v's pnQ_stmt, the arm's outcome pn_out turned
   into pv_Qm, the memory part of parse_value's post (PvB_Defs.v pv_Qm). No machine code is walked here.
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search (04:10Z, `proof-index
   parse_value`, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in the delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (04:21Z): no released srealizes-form proof of this program's parse_value.
   - PURE (grammar only, no image; image A's number arm can reuse it): the model's number arm
     (PjGrammar.jr_number, through PvB_Model.pvm_number) read at the machine's cut facts: pnq_num_refuse (the first
     digit is missing, or a 0 is followed by a digit: refused before any allocation) and pnq_num_go (the token is the
     scanned span x[0, m), the allocation outcome, then the whole-and-finite test). pnq_bits_range: strtod's bits are
     a 64-bit word (a port of the plain layer's f128_to_d range proof, re-proved here, not cited).
   - PACKAGING: the four outcomes of pn_out ((a) refused, (b) fuzz_malloc NULL, (c) allocated but not whole or not
     finite, (d) read) against pv_Qm, the batch kit's post (PvB_Defs.v at the batch kit's tip 240b06ed4fd4): the ledger move
     rd_ledger_move with g_most, the grant-all trace gt = [EAlloc (S m)] (pnq_gt_go) and the refused peak (pnq_move_*,
     pnq_oks_*, pnq_rpeak1: the statements of PvB_D_Str.v's pvs_move_* / pvs_oks_* / pvs_rpeak1, kept here so segment N
     does not depend on segment D's file), the room invariant room_live_cf (pv_reader0's rd_room for (a), the cut's own
     conjunct for (b)-(d)), the room post rp_post (PvB_Room.v; (a) and (b) make no event, so rp_nil turns the keep they
     carry into it; (c) and (d) carry pn_rp1, the rp_post of EAlloc (S m)), the OUTCOME pv_outc over the grant-all run
     ((a) PvB_Defs.pv_outc_nil; (b) is off the grant-all run: at cnt = fail the run's fail-counter clause is false, at
     cnt <> fail the cut's pn_null_off; (c) / (d) keep g_ran_out, the grant-all result is the [true] one, and pn_rp1
     moves the position), blocks move, frames clause, peak bound, the live-bytes bound blocks_bytes S' <= blocks_bytes
     S + prh_held tr (blocks_bytes is the sum of the allocator blocks, pnq_bb), lsum D = held tr, and per result the
     free-order tie pv_ftie (the number is a leaf: its frees are lf of its trace, PvB_Frees.pvf_frees_leaf; an
     all-zero header for (a) / (b), pvf_zero_foR; the str block for (c), pvf_hdr_leaf_foR; the JNum node for (d),
     pvf_node_leaf_foR), the node (pj_fdR for (a)-(c), pj_nodeR (JNum txt bits) and its capacity words pj_ncapR,
     pvf_ncap_leaf, for (d)). The node's bytes are writable after the arm because they lie off the image (LAWS: the
     allocator's client-image law for a block or a fake frame, the stack above the image), as PvB_D_Lit.v does for
     the literal arms.
   Section hypotheses: hl (the harness-block head length AR_laws_x is stated at, YCbqG.v:36-39) and LAWS (the kit's
   AR_laws_x at hl; PvB_D_Lit.v / PvB_A.v take it). The refusal case of arm (b) closes by the batch kit's re-keyed prh_oks
   (g_ran_out set only when the refused request is at most g_most) and the refused peak prh_refused_peak: no run
   condition is carried (the interim premises over PvB_NOks.v's pn_oks_ran / pn_oks_peak are gone).
   Numerals: 43 45 46 48 57 69 101 (WORD: ASCII bytes of the number characters) 123 91 34 116 102 110 (WORD: the
   dispatch bytes) 0 3 (WORD: node tags) 4 8 16 24 56 (LENGTH: the node layout) 256 2 ^ 32 2 ^ 64 4294967296
   18446744073709551616 (LENGTH: byte / word ranges) 4096 (LENGTH: the app floor of prhPv_node) 33 (DERIVED:
   PjGrammar.MAXD + 1, pj_in_afterR's depth bound) 52 63 64 (LENGTH: bit positions of a double) 1 (LENGTH: counts).
   No ADDRESS (port_addr_check self-pair on image B: NON-ADDRESS-SAME 227, SAME-GEOMETRY 1 = the 4096). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_Model PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c PvB_Frees.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar PjTree PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure: lists ---- *)

Lemma pnq_skipn_cons : forall (x : list Z) (i : nat), (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
induction x as [|b x IH]; intros i Hi; [cbn [length] in Hi; lia|].
destruct i as [|i]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn [length] in Hi. lia.
Qed.

Lemma pnq_skipn_all : forall (x : list Z) (i : nat), (length x <= i)%nat -> skipn i x = [].
Proof.
induction x as [|b x IH]; intros i Hi; [destruct i; reflexivity|].
destruct i as [|i]; [cbn [length] in Hi; lia|]. cbn [skipn]. apply IH. cbn [length] in Hi. lia.
Qed.

Lemma pnq_nth_skipn : forall (x : list Z) (i k : nat), nth k (skipn i x) 0 = nth (i + k) x 0.
Proof.
induction x as [|b x IH]; intros i k; [destruct i; destruct k; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma pnq_len_firstn : forall (x : list Z) (m : nat), (m <= length x)%nat -> length (firstn m x) = m.
Proof. intros x m H. rewrite length_firstn. lia. Qed.

(* a run of number characters of a suffix of tb is at most tb's longest run (PjRoundTrip.maxrun); the one copy,
   cited by pnq_tok_short below and so by PvB_ND.v's strtod row *)
Lemma pnq_mr_run : forall (x : list Z) (m c : nat), Forall (fun z => PjGrammar.numch z = true) (firstn m x) ->
  (m <= length x)%nat -> (c + m <= PjRoundTrip.mr c x)%nat.
Proof.
induction x as [|b r IH]; intros m c H Hm.
- cbn in Hm. assert (m = 0%nat) by lia. subst m. cbn. lia.
- destruct m as [|m]; [rewrite Nat.add_0_r; apply PjRoundTrip.mr_ge|].
  cbn [firstn] in H. inversion H as [|? ? Hb Hr]; subst. cbn [PjRoundTrip.mr]. rewrite Hb.
  cbn [length] in Hm. specialize (IH m (S c) Hr ltac:(lia)). lia.
Qed.

Lemma pnq_mr_suffix : forall (tb : list Z) (k c : nat), (PjRoundTrip.mr 0 (skipn k tb) <= PjRoundTrip.mr c tb)%nat.
Proof.
induction tb as [|b r IH]; intros k c.
- rewrite skipn_nil. cbn. lia.
- destruct k as [|k].
  + cbn [skipn]. apply PjRoundTrip.mr_mono. lia.
  + cbn [skipn]. specialize (IH k 0%nat). cbn [PjRoundTrip.mr].
    destruct (PjGrammar.numch b).
    * pose proof (PjRoundTrip.mr_mono r 0 (S c) ltac:(lia)). lia.
    * lia.
Qed.

Lemma pnq_maxrun : forall (tb : list Z) (k m : nat),
  Forall (fun z => PjGrammar.numch z = true) (firstn m (skipn k tb)) -> (m <= length (skipn k tb))%nat ->
  (m <= PjRoundTrip.maxrun tb)%nat.
Proof.
intros tb k m H Hm. unfold PjRoundTrip.maxrun.
pose proof (pnq_mr_run (skipn k tb) m 0 H Hm). pose proof (pnq_mr_suffix tb k 0). lia.
Qed.

(* x[0, m) is x[0, j), the byte x[j], then the j + 1 .. m - 1 rest *)
Lemma pnq_firstn_split : forall (x : list Z) (j m : nat), (j < m)%nat -> (j < length x)%nat ->
  firstn m x = firstn j x ++ nth j x 0 :: firstn (m - S j) (skipn (S j) x).
Proof.
induction x as [|b x IH]; intros j m Hjm Hj; [cbn [length] in Hj; lia|].
destruct m as [|m]; [lia|].
destruct j as [|j].
- cbn. rewrite Nat.sub_0_r. reflexivity.
- cbn. f_equal. cbn [length] in Hj. apply IH; lia.
Qed.

(* span numch stops exactly where the machine's scan stopped *)
Lemma pnq_span : forall (z : list Z) (k : nat), (k <= length z)%nat ->
  Forall (fun b => PjGrammar.numch b = true) (firstn k z) ->
  (k = length z \/ PjGrammar.numch (nth k z 0) = false) ->
  PjGrammar.span PjGrammar.numch z = (firstn k z, skipn k z).
Proof.
induction z as [|b z IH]; intros k Hk Hf Hs.
- cbn [length] in Hk. assert (k = 0%nat) by lia. subst k. reflexivity.
- destruct k as [|k].
  + destruct Hs as [Hs|Hs]; [cbn [length] in Hs; discriminate Hs|].
    cbn [nth] in Hs. cbn [PjGrammar.span]. rewrite Hs. reflexivity.
  + cbn [firstn] in Hf. pose proof (Forall_inv Hf) as Hb. pose proof (Forall_inv_tail Hf) as Hf'.
    cbn [length] in Hk. cbn [length nth] in Hs.
    assert (Hs' : k = length z \/ PjGrammar.numch (nth k z 0) = false)
      by (destruct Hs as [Hs|Hs]; [left; lia|right; exact Hs]).
    cbn [PjGrammar.span]. rewrite Hb. rewrite (IH k ltac:(lia) Hf' Hs'). reflexivity.
Qed.

Lemma pnq_numch_range : forall b, PjGrammar.numch b = true -> 43 <= b <= 101.
Proof.
intros b H. unfold PjGrammar.numch, PjGrammar.digit in H.
destruct (Z.leb_spec 48 b), (Z.leb_spec b 57), (Z.eqb_spec b 46), (Z.eqb_spec b 101), (Z.eqb_spec b 69),
  (Z.eqb_spec b 43), (Z.eqb_spec b 45); cbn in H; try discriminate; lia.
Qed.

(* the token x[0, m) is number characters: the optional minus, then the scanned span *)
Lemma pnq_txt_numch : forall c y (m : nat), (pn_sg c < m)%nat -> pn_span (c :: y) (pn_sg c) m ->
  Forall (fun b => PjGrammar.numch b = true) (firstn m (c :: y)).
Proof.
intros c y m Hm Hsp. unfold pn_span, pn_sg in Hm, Hsp. revert Hm Hsp.
destruct (Z.eqb_spec c 45) as [E|E]; intros Hm Hsp; cbv beta iota in Hm, Hsp.
- subst c. destruct m as [|m]; [lia|].
  assert (H1 : skipn 1 (45 :: y) = y) by reflexivity. rewrite H1 in Hsp.
  replace (S m - 1)%nat with m in Hsp by lia.
  cbn [firstn]. constructor; [reflexivity|exact Hsp].
- rewrite Nat.sub_0_r in Hsp. exact Hsp.
Qed.

(* ---- pure: the number arm of the model at the machine's cut facts ---- *)

(* the dispatch: a first byte that is none of the six dispatch bytes is the number arm *)
Lemma pnq_value : forall sm d rest c y ok, PjGrammar.skip rest = c :: y ->
  c <> 123 -> c <> 91 -> c <> 34 -> c <> 116 -> c <> 102 -> c <> 110 ->
  PjGrammar.jr_value sm d rest ok = PjGrammar.jr_number sm (c :: y) ok.
Proof.
intros sm d rest c y ok Hs H1 H2 H3 H4 H5 H6. rewrite pvm_unfold, Hs. cbv beta iota.
rewrite (proj2 (Z.eqb_neq c 123) H1), (proj2 (Z.eqb_neq c 91) H2), (proj2 (Z.eqb_neq c 34) H3),
  (proj2 (Z.eqb_neq c 116) H4), (proj2 (Z.eqb_neq c 102) H5), (proj2 (Z.eqb_neq c 110) H6).
reflexivity.
Qed.

Section m.
Variable sm : list Z -> Z * Z.

(* (a): no first digit, or a leading zero before a digit: refused, no allocation *)
Lemma pnq_num_refuse : forall c y ok, ~ pn_lead (c :: y) (pn_sg c) ->
  PjGrammar.jr_number sm (c :: y) ok = (None, [], ok).
Proof.
intros c y ok Hl. rewrite pvm_number. cbv beta iota zeta.
change (if c =? 45 then 1%nat else 0%nat) with (pn_sg c).
destruct (Nat.lt_ge_cases (pn_sg c) (length (c :: y))) as [Hj|Hj].
2:{ rewrite (pnq_skipn_all (c :: y) (pn_sg c) Hj). reflexivity. }
rewrite (pnq_skipn_cons (c :: y) (pn_sg c) Hj). cbv beta iota.
destruct (PjGrammar.digit (nth (pn_sg c) (c :: y) 0)) eqn:Ed; [|reflexivity].
cbn [negb].
match goal with |- context [if andb ?A ?M then _ else _] =>
  assert (E2 : andb A M = true); [|rewrite E2; reflexivity] end.
destruct (Z.eqb_spec (nth (pn_sg c) (c :: y) 0) 48) as [H48|H48].
2:{ exfalso. apply Hl. split; [exact Hj|]. split; [exact Ed|]. intros (H & _). exact (H48 H). }
cbn [andb].
destruct (Nat.lt_ge_cases (S (pn_sg c)) (length (c :: y))) as [HSj|HSj].
2:{ exfalso. apply Hl. split; [exact Hj|]. split; [exact Ed|]. intros (_ & H & _). lia. }
rewrite (pnq_skipn_cons (c :: y) (S (pn_sg c)) HSj). cbv beta iota.
destruct (PjGrammar.digit (nth (S (pn_sg c)) (c :: y) 0)) eqn:Ed1; [reflexivity|].
exfalso. apply Hl. split; [exact Hj|]. split; [exact Ed|]. intros (_ & _ & H). rewrite Ed1 in H. discriminate H.
Qed.

(* (b)-(d): a first digit, no leading zero before a digit, the scan stopped at m: the token is x[0, m), the rest
   after it x[m ..), and the outcome is the allocation's and then the whole-and-finite test's *)
Lemma pnq_num_go : forall c y ok (m : nat),
  pn_lead (c :: y) (pn_sg c) -> (pn_sg c < m <= length (c :: y))%nat ->
  pn_span (c :: y) (pn_sg c) m -> pn_stop (c :: y) m ->
  PjGrammar.jr_number sm (c :: y) ok =
  let (bk, ok1) := PjGrammar.take ok in
  if bk then
    (if PjGrammar.whole sm (firstn m (c :: y))
     then (Some (PjTree.JNum (firstn m (c :: y)) (snd (sm (firstn m (c :: y)))), skipn m (c :: y)),
           [PjGrammar.EAlloc (S m)], ok1)
     else (None, [PjGrammar.EAlloc (S m)], ok1))
  else (None, [PjGrammar.EFail (S m)], ok1).
Proof.
intros c y ok m Hl Hm Hsp Hst. destruct Hl as (Hj & Hd & Hnz).
rewrite pvm_number. cbv beta iota zeta.
change (if c =? 45 then 1%nat else 0%nat) with (pn_sg c).
rewrite (pnq_skipn_cons (c :: y) (pn_sg c) Hj). cbv beta iota.
rewrite Hd. cbn [negb].
match goal with |- context [if andb ?A ?M then _ else _] =>
  assert (E2 : andb A M = false); [|rewrite E2] end.
{ destruct (Z.eqb_spec (nth (pn_sg c) (c :: y) 0) 48) as [H48|H48]; [|reflexivity].
  cbn [andb].
  destruct (Nat.lt_ge_cases (S (pn_sg c)) (length (c :: y))) as [HSj|HSj].
  - rewrite (pnq_skipn_cons (c :: y) (S (pn_sg c)) HSj). cbv beta iota.
    destruct (PjGrammar.digit (nth (S (pn_sg c)) (c :: y) 0)) eqn:Ed1; [|reflexivity].
    exfalso. apply Hnz. split; [exact H48|]. split; [exact HSj|first [exact Ed1 | reflexivity]].
  - rewrite (pnq_skipn_all (c :: y) (S (pn_sg c)) HSj). reflexivity. }
cbv beta iota.
assert (HL : length (skipn (S (pn_sg c)) (c :: y)) = (length (c :: y) - S (pn_sg c))%nat)
  by apply length_skipn.
assert (HF : Forall (fun b => PjGrammar.numch b = true)
               (firstn (m - S (pn_sg c)) (skipn (S (pn_sg c)) (c :: y)))).
{ unfold pn_span in Hsp. rewrite (pnq_skipn_cons (c :: y) (pn_sg c) Hj) in Hsp.
  replace (m - pn_sg c)%nat with (S (m - S (pn_sg c))) in Hsp by lia.
  cbn [firstn] in Hsp. exact (Forall_inv_tail Hsp). }
assert (HS : (m - S (pn_sg c))%nat = length (skipn (S (pn_sg c)) (c :: y)) \/
             PjGrammar.numch (nth (m - S (pn_sg c)) (skipn (S (pn_sg c)) (c :: y)) 0) = false).
{ unfold pn_stop in Hst. destruct Hst as [Hst|Hst]; [left; rewrite HL; lia|right].
  rewrite pnq_nth_skipn. replace (S (pn_sg c) + (m - S (pn_sg c)))%nat with m by lia. exact Hst. }
assert (Hk : (m - S (pn_sg c) <= length (skipn (S (pn_sg c)) (c :: y)))%nat) by (rewrite HL; lia).
rewrite (pnq_span _ _ Hk HF HS). cbv beta iota.
rewrite <- (pnq_firstn_split (c :: y) (pn_sg c) m ltac:(lia) Hj).
rewrite skipn_skipn. replace (m - S (pn_sg c) + S (pn_sg c))%nat with m by lia.
rewrite (pnq_len_firstn (c :: y) m ltac:(lia)).
reflexivity.
Qed.

(* the grant-all run (ok = []) at a scanned token: its trace is the one allocation EAlloc (S m), and its result is the
   granted one's (ok = [true]) *)
Lemma pnq_gt_go : forall c y (m : nat),
  pn_lead (c :: y) (pn_sg c) -> (pn_sg c < m <= length (c :: y))%nat ->
  pn_span (c :: y) (pn_sg c) m -> pn_stop (c :: y) m ->
  snd (fst (PjGrammar.jr_number sm (c :: y) [])) = [PjGrammar.EAlloc (S m)] /\
  fst (PjGrammar.jr_number sm (c :: y) []) = fst (PjGrammar.jr_number sm (c :: y) [true]).
Proof.
intros c y m Hl Hm Hsp Hst.
rewrite (pnq_num_go c y [] m Hl Hm Hsp Hst), (pnq_num_go c y [true] m Hl Hm Hsp Hst). cbn [PjGrammar.take].
destruct (PjGrammar.whole sm (firstn m (c :: y))); split; reflexivity.
Qed.

End m.

(* ---- pure: strtod's bits are a 64-bit word (the double SoftFloat.f128_to_d packs) ---- *)

Definition pnq_r64 (z : Z) : Prop := Z.shiftr z 64 = 0.

Lemma pnq_r64_iff : forall z, pnq_r64 z <-> 0 <= z < 2 ^ 64.
Proof.
intro z. unfold pnq_r64. rewrite Z.shiftr_div_pow2 by lia. split.
- intro H. pose proof (Z.div_mod z (2 ^ 64) ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound z (2 ^ 64) ltac:(lia)) as Bd.
  rewrite H in E. set (r := z mod 2 ^ 64) in *. lia.
- intro H. apply Z.div_small. exact H.
Qed.

Lemma pnq_r64_lor : forall a b, pnq_r64 a -> pnq_r64 b -> pnq_r64 (Z.lor a b).
Proof. unfold pnq_r64. intros a b Ha Hb. rewrite Z.shiftr_lor, Ha, Hb. reflexivity. Qed.

Lemma pnq_r64_land : forall a b, pnq_r64 a -> pnq_r64 b -> pnq_r64 (Z.land a b).
Proof. unfold pnq_r64. intros a b Ha Hb. rewrite Z.shiftr_land, Ha, Hb. reflexivity. Qed.

Lemma pnq_r64_lxor : forall a b, pnq_r64 a -> pnq_r64 b -> pnq_r64 (Z.lxor a b).
Proof. unfold pnq_r64. intros a b Ha Hb. rewrite Z.shiftr_lxor, Ha, Hb. reflexivity. Qed.

Lemma pnq_r64_shr : forall x n, pnq_r64 x -> pnq_r64 n -> pnq_r64 (Z.shiftr x n).
Proof.
intros x n Hx Hn. apply pnq_r64_iff in Hn. unfold pnq_r64 in *.
rewrite Z.shiftr_shiftr by lia. rewrite Z.add_comm. rewrite <- Z.shiftr_shiftr by lia.
rewrite Hx. apply Z.shiftr_0_l.
Qed.

Lemma pnq_r64_wrap : forall x, pnq_r64 (SoftFloat.wrap64 x).
Proof. intro x. apply pnq_r64_iff. apply SoftFloat.wrap64_range. Qed.

Lemma pnq_r64_if : forall (c : bool) a b, pnq_r64 a -> pnq_r64 b -> pnq_r64 (if c then a else b).
Proof. intros [|] a b Ha Hb; assumption. Qed.

Lemma pnq_r64_snd_if : forall (c : bool) (p q : Z * Z),
  pnq_r64 (snd p) -> pnq_r64 (snd q) -> pnq_r64 (snd (if c then p else q)).
Proof. intros [|] p q Hp Hq; assumption. Qed.

Lemma pnq_r64_snd_pair : forall x y : Z, pnq_r64 y -> pnq_r64 (snd (x, y)).
Proof. intros x y H. exact H. Qed.

Lemma pnq_r64_trunc : forall s r, pnq_r64 s -> pnq_r64 (SoftFloat.trunc_round s r).
Proof.
intros s r Hs. unfold SoftFloat.trunc_round, SoftFloat.add64.
destruct (negb _); [apply pnq_r64_wrap|].
destruct (negb (negb _)); [apply pnq_r64_wrap|exact Hs].
Qed.

Ltac pnq_r64_go :=
  repeat match goal with
  | |- pnq_r64 (snd (if _ then _ else _)) => apply pnq_r64_snd_if
  | |- pnq_r64 (snd (_, _)) => apply pnq_r64_snd_pair
  | |- pnq_r64 (if _ then _ else _) => apply pnq_r64_if
  | |- pnq_r64 (Z.lor _ _) => apply pnq_r64_lor
  | |- pnq_r64 (Z.land _ _) => apply pnq_r64_land
  | |- pnq_r64 (Z.lxor _ _) => apply pnq_r64_lxor
  | |- pnq_r64 (Z.shiftr _ _) => apply pnq_r64_shr
  | |- pnq_r64 (SoftFloat.wrap64 _) => apply pnq_r64_wrap
  | |- pnq_r64 (SoftFloat.trunc_round _ _) => apply pnq_r64_trunc
  | |- pnq_r64 (Zpos _) => reflexivity
  | |- pnq_r64 Z0 => reflexivity
  | H : pnq_r64 ?z |- pnq_r64 ?z => exact H
  end.

Lemma pnq_to_d : forall a, 0 <= SoftFloat.f128_to_d a < 2 ^ 64.
Proof.
intro a. apply pnq_r64_iff.
cbv beta zeta delta [SoftFloat.f128_to_d SoftFloat.lo64 SoftFloat.hi64 SoftFloat.shl64
  SoftFloat.add64 SoftFloat.sub64 SoftFloat.eqz64 SoftFloat.nez64 SoftFloat.sext32
  SoftFloat.zext32 SoftFloat.sra63 SoftFloat.not64 SoftFloat.b2z SoftFloat.DQUIET
  SoftFloat.M32 SoftFloat.ONES64].
match goal with |- pnq_r64 (match ?p with _ => _ end) =>
  assert (H : pnq_r64 (snd p)) by pnq_r64_go; revert H; destruct p as [e s] end.
cbv beta iota delta [snd]. intro H. pnq_r64_go.
Qed.

Lemma pnq_bits_range : forall txt bits c, strtod_c.strtod_model txt = Some (bits, c) -> 0 <= bits < 2 ^ 64.
Proof.
intros txt bits c H. unfold strtod_c.strtod_model, FloatScan.scan_strtod in H. cbv zeta in H.
destruct (FloatScan.floatscan _ _ _ _) as [[f y]|]; [|discriminate].
injection H as <- _. apply pnq_to_d.
Qed.

(* ---- pure: the ledger moves of the arm's outcomes (the batch kit's rd_ledger_move: g_most, the grant-all trace gt, the refused
   peak; the statements of PvB_D_Str.v pvs_move_none / pvs_move_one / pvs_oks_cf / pvs_oks_refused / pvs_oks_granted /
   pvs_rpeak1) ---- *)

(* (a): no allocator call *)
Lemma pnq_move_none : forall Lam peak cnt fail ran most gt,
  0 <= cnt < 2 ^ 64 -> 0 <= Ledger.lsum Lam <= peak ->
  rd_ledger_move Lam peak cnt fail ran most [] gt [] [] Lam peak cnt fail ran.
Proof.
intros Lam peak cnt fail ran most gt Hc Hl.
unfold rd_ledger_move, prh_oks, fail_afterR. cbn [PjGrammar.calls hpeakR].
split; [split; [intros i Hi; lia | split; [left; reflexivity | intros i Hi; lia]]|].
split; [rewrite Z.add_0_r, Z.mod_small by lia; reflexivity|].
split; [split; [intros H; lia | intros _; reflexivity]|].
split; [apply Permutation_refl|].
split; [apply Permutation_refl|].
split; [reflexivity|].
unfold prh_refused_peak. cbn [List.seq map fold_right]. lia.
Qed.

(* one allocator call *)
Lemma pnq_move_one : forall Lam peak cnt fail ran most (b : bool) gt tr D Lam' peak' cnt' fail' ran',
  PjGrammar.calls tr = 1%nat ->
  prh_oks [b] cnt fail 1 (prh_ev_reqs tr) most ran ran' ->
  cnt' = (cnt + 1) mod 2 ^ 64 ->
  (cnt = fail -> fail' = SIZE_MAXZ) -> (cnt <> fail -> fail' = fail) ->
  Permutation Lam' (D ++ Lam) -> Permutation (map snd D) (map Z.of_nat (lszR tr)) ->
  Z.of_nat (length D) = nliveR tr ->
  peak' = Z.max (Z.max peak (Ledger.lsum Lam + hpeakR tr))
    (prh_refused_peak [b] cnt fail 1 (map (Z.add (Ledger.lsum Lam)) (prh_ev_helds gt))) ->
  rd_ledger_move Lam peak cnt fail ran most [b] gt tr D Lam' peak' cnt' fail' ran'.
Proof.
intros Lam peak cnt fail ran most b gt tr D Lam' peak' cnt' fail' ran' Hcl Hok Hc Hf1 Hf2 HP1 HP2 HN HPk.
unfold rd_ledger_move, fail_afterR. rewrite Hcl.
split; [exact Hok|]. split; [exact Hc|].
split; [split; [intros H; apply Hf1; lia | intros H; apply Hf2; lia]|].
split; [exact HP1|]. split; [exact HP2|]. split; [exact HN|exact HPk].
Qed.

(* the harness's fail counter refuses the call: no refusal by the allocator, g_ran_out kept *)
Lemma pnq_oks_cf : forall cnt fail ns most ran, cnt = fail -> prh_oks [false] cnt fail 1 ns most ran ran.
Proof.
intros cnt fail ns most ran E. unfold prh_oks.
split; [intros i Hi _; destruct i as [|i]; [reflexivity|lia]|].
split; [left; reflexivity|].
intros i Hi Hr _. destruct i as [|i]; [|lia]. exfalso. unfold prh_refused in Hr. cbn [nth Z.of_nat] in Hr.
rewrite Z.add_0_r, (proj2 (Z.eqb_eq cnt fail) E) in Hr. discriminate Hr.
Qed.

(* the allocator refuses a request n: g_ran_out set exactly when n is at most g_most (the batch kit's re-keyed prh_oks) *)
Lemma pnq_oks_refused : forall cnt fail n most ran, cnt <> fail ->
  prh_oks [false] cnt fail 1 [n] most ran (if n <=? most then 1 else ran).
Proof.
intros cnt fail n most ran E. unfold prh_oks.
assert (Hr0 : prh_refused [false] cnt fail 0 = true).
{ unfold prh_refused. cbn [nth Z.of_nat]. rewrite Z.add_0_r, (proj2 (Z.eqb_neq cnt fail) E). reflexivity. }
split; [intros i Hi Hf; destruct i as [|i]; [cbn [Z.of_nat] in Hf; lia|lia]|].
split.
- destruct (Z.leb_spec n most) as [Hle|Hgt];
    [right; split; [reflexivity|exists 0%nat; split; [lia|split; [exact Hr0|cbn [nth]; exact Hle]]]
    |left; reflexivity].
- intros i Hi _ Hm. destruct i as [|i]; [|lia]. cbn [nth] in Hm. destruct (Z.leb_spec n most); [reflexivity|lia].
Qed.

(* the call is granted: g_ran_out kept *)
Lemma pnq_oks_granted : forall cnt fail ns most ran, cnt <> fail -> prh_oks [true] cnt fail 1 ns most ran ran.
Proof.
intros cnt fail ns most ran E. unfold prh_oks.
split; [intros i Hi Hf; destruct i as [|i]; [cbn [Z.of_nat] in Hf; lia|lia]|].
split; [left; reflexivity|].
intros i Hi Hr _. destruct i as [|i]; [|lia]. unfold prh_refused in Hr. cbn [nth negb andb] in Hr. discriminate Hr.
Qed.

(* the refused peak of one call *)
Lemma pnq_rpeak1 : forall (b : bool) cnt fail h,
  prh_refused_peak [b] cnt fail 1 [h] = Z.max (if negb b && negb (cnt =? fail) then Z.min SIZE_MAXZ h else 0) 0.
Proof.
intros b cnt fail h. unfold prh_refused_peak, prh_refused. cbn [List.seq map fold_right nth Z.of_nat].
rewrite Z.add_0_r. reflexivity.
Qed.

(* (b): one fuzz_malloc call of n + 1 user bytes that returned NULL, at the grant-all trace [EAlloc (S n)]: the
   chosen failure (g_fail_at reset, the rest kept) or the allocator's refusal (#102's refused(): g_peak raised to
   max (g_peak, min (SIZE_MAX, g_live + n + 1)), g_ran_out := 1 when n + 1 <= g_most; PRH_FnAlloc.v prh_alloc_post
   arm 2), which the batch kit's re-keyed prh_oks and the refused peak state exactly *)
Lemma pnq_move_fail : forall Lam peak cnt fail ran most peak' fail' ran' (n : nat), 0 <= Ledger.lsum Lam <= peak ->
  (cnt = fail /\ peak' = peak /\ fail' = SIZE_MAXZ /\ ran' = ran \/
   cnt <> fail /\ peak' = Z.max peak (Z.min SIZE_MAXZ (Ledger.lsum Lam + (Z.of_nat n + 1))) /\ fail' = fail /\
   ran' = (if Z.of_nat n + 1 <=? most then 1 else ran)) ->
  rd_ledger_move Lam peak cnt fail ran most [false] [PjGrammar.EAlloc (S n)] [PjGrammar.EFail (S n)] [] Lam peak'
    ((cnt + 1) mod 2 ^ 64) fail' ran'.
Proof.
intros Lam peak cnt fail ran most peak' fail' ran' n Hl Hc.
destruct Hc as [(E & -> & -> & ->)|(E & -> & -> & ->)].
- apply pnq_move_one; [reflexivity | exact (pnq_oks_cf _ _ _ _ _ E) | reflexivity | intros _; reflexivity |
    intros H; exfalso; exact (H E) | apply Permutation_refl | apply Permutation_refl | reflexivity |].
  change (prh_ev_helds [PjGrammar.EAlloc (S n)]) with [Z.of_nat (S n)]. cbn [map]. rewrite pnq_rpeak1.
  rewrite (proj2 (Z.eqb_eq _ _) E). cbn [negb andb hpeakR PjGrammar.held_ev]. clear - Hl. lia.
- apply pnq_move_one; [reflexivity | | reflexivity | intros H; exfalso; exact (E H) | intros _; reflexivity |
    apply Permutation_refl | apply Permutation_refl | reflexivity |].
  + replace (Z.of_nat n + 1) with (Z.of_nat (S n)) by lia.
    change (prh_ev_reqs [PjGrammar.EFail (S n)]) with [Z.of_nat (S n)].
    exact (pnq_oks_refused _ _ _ _ _ E).
  + change (prh_ev_helds [PjGrammar.EAlloc (S n)]) with [Z.of_nat (S n)]. cbn [map]. rewrite pnq_rpeak1.
    rewrite (proj2 (Z.eqb_neq _ _) E). cbn [negb andb hpeakR PjGrammar.held_ev]. unfold SIZE_MAXZ.
    clear - Hl. lia.
Qed.

(* (c), (d): one fuzz_malloc call that returned a block of n + 1 user bytes, kept *)
Lemma pnq_move_alloc : forall Lam peak cnt fail ran most res (n : nat), cnt <> fail -> 0 <= Ledger.lsum Lam ->
  rd_ledger_move Lam peak cnt fail ran most [true] [PjGrammar.EAlloc (S n)] [PjGrammar.EAlloc (S n)]
    [(res, Z.of_nat n + 1)] ((res, Z.of_nat n + 1) :: Lam) (Z.max peak (Ledger.lsum Lam + (Z.of_nat n + 1)))
    ((cnt + 1) mod 2 ^ 64) fail ran.
Proof.
intros Lam peak cnt fail ran most res n Hne Hl.
apply pnq_move_one; [reflexivity | exact (pnq_oks_granted _ _ _ _ _ Hne) | reflexivity |
  intros H; exfalso; exact (Hne H) | intros _; reflexivity | apply Permutation_refl | | reflexivity |].
- cbn [map snd lszR fold_left lsz_evR]. rewrite Nat2Z.inj_succ. apply Permutation_refl.
- change (prh_ev_helds [PjGrammar.EAlloc (S n)]) with [Z.of_nat (S n)]. cbn [map]. rewrite pnq_rpeak1.
  cbn [negb andb hpeakR PjGrammar.held_ev]. clear - Hl. lia.
Qed.

Lemma pnq_after : forall segs m q text len p d tb,
  pj_in_okR segs m q text len p d tb -> pj_in_afterR segs m q text len d 33.
Proof.
intros segs m q text len p d tb (V1 & V2 & V3 & Hrw & _ & _ & _ & Hp & _ & _ & _ & Hd).
exists p, d. split; [lia|]. split; [lia|]. split; [exact V1|]. split; [exact V2|]. split; [exact V3|exact Hrw].
Qed.

(* the allocator's live bytes are the sum of its blocks' sizes (YCbq.blocks_bytes_bsum's statement; PvB_D_Str.v
   pvs_bb) *)
Lemma pnq_bb : forall (B0 : asyms) ly S, blocks_bytes S = bsum (ablocks B0 ly S).
Proof.
intros B0 ly S. unfold blocks_bytes, ablocks, blocks, bsum.
induction (st_chunks S) as [|c l IH]; cbn; [reflexivity|].
destruct (is_alloc c); cbn; rewrite IH; reflexivity.
Qed.

(* ---- memory ---- *)

#[local] Instance PIBq : PrhImg := prh_img_B.
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the kit rule: the allocator's laws over ARx (YCbqG.v AR_laws_x) at the head length hl, as PvB_A.v / PvB_D_Lit.v
   take it *)
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.

(* a byte off the image that the memory shows is a byte the memory holds, so it is writable *)
Lemma pnq_wr : forall (m : word -> option byte) x b, 0 <= x < 2 ^ 64 -> ~ in_img SEGS x ->
  mbyte SEGS m x = Some b -> writable_at SEGS m x.
Proof.
intros m x b Hx Hn Hb. unfold writable_at, wview. unfold mbyte in Hb. revert Hb.
destruct (m (Z_to_bv 64 x)) as [b'|]; intros Hb; [discriminate|].
rewrite (seg_rom_none SEGS x Hx Hn) in Hb. discriminate Hb.
Qed.

Lemma pnq_byte0 : forall H (m : word -> option byte) x, aview SEGS H m x = Some 0 ->
  mbyte SEGS (mrestrict H m) x = Some (Z_to_bv 8 0).
Proof.
intros H m x E. unfold aview in E. revert E.
destruct (mbyte SEGS (mrestrict H m) x) as [b|]; intros E; [|discriminate E].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.

Lemma pnq_zero_at : forall H (m : word -> option byte) v x, pj_zeroR SEGS (mrestrict H m) v -> v <= x < v + 56 ->
  aview SEGS H m x = Some 0.
Proof.
intros H m v x Hz Hx. unfold pj_zeroR, garr8 in Hz.
destruct (Hz (Z.to_nat (x - v))) as [Hv _]; [rewrite repeat_length; lia|].
specialize (Hv 0%nat ltac:(lia)). rewrite nth_repeat in Hv.
replace (v + Z.of_nat (Z.to_nat (x - v)) + Z.of_nat 0) with x in Hv by lia.
unfold aview. rewrite Hv. reflexivity.
Qed.

Lemma pnq_le0 : forall (n k : nat), le_byte 0 n k = 0.
Proof.
intros n k. unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. reflexivity.
Qed.

(* n zero bytes are the value 0, and back *)
Lemma pnq_val0 : forall (m : word -> option byte) a (n : nat),
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m x = Some (Z_to_bv 8 0)) -> val_mem SEGS m a n 0.
Proof.
intros m a n H k Hk. rewrite H by lia. do 2 f_equal. symmetry. exact (pnq_le0 n k).
Qed.

Lemma pnq_val0_byte : forall (m : word -> option byte) a x, val_mem SEGS m a 8 0 -> a <= x < a + 8 ->
  mbyte SEGS m x = Some (Z_to_bv 8 0).
Proof.
intros m a x H Hx. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (a + (x - a)) with x in Hb by lia.
rewrite Hb, pnq_le0. reflexivity.
Qed.

Lemma pnq_vm_byte : forall (m : word -> option byte) a (n : nat) w x, val_mem SEGS m a n w ->
  a <= x < a + Z.of_nat n -> exists b, mbyte SEGS m x = Some b.
Proof.
intros m a n w x H Hx. pose proof (H (Z.to_nat (x - a)) ltac:(lia)) as Hb.
rewrite Z2Nat.id in Hb by lia. replace (a + (x - a)) with x in Hb by lia. eexists; exact Hb.
Qed.

(* the header of a node off the image: the type word ty, num at + 8, str at + 16, every other field 0 *)
Lemma pnq_hdr : forall (m : word -> option byte) v ty num str, v mod 8 = 0 -> 0 <= v -> v + 56 < 2 ^ 64 ->
  (forall x, v <= x < v + 56 -> ~ in_img SEGS x) ->
  0 <= ty < 2 ^ 32 -> val_mem SEGS m v 4 ty ->
  0 <= num < 2 ^ 64 -> val_mem SEGS m (v + 8) 8 num ->
  0 <= str < 2 ^ 64 -> val_mem SEGS m (v + 16) 8 str ->
  (forall x, v + 4 <= x < v + 8 \/ v + 24 <= x < v + 56 -> mbyte SEGS m x = Some (Z_to_bv 8 0)) ->
  pj_hdrR SEGS m v ty num str 0 0 0 0.
Proof.
intros m v ty num str Hal H0 H64 NI Hty Hv Hnum Hvn Hstr Hvs Hz.
assert (E64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (U : forall a, v + 24 <= a -> a + 8 <= v + 56 -> rd_u64 SEGS m a 0).
{ intros a H1 H2. split; [lia|]. apply pnq_val0. intros x Hx. apply Hz. lia. }
assert (VIS : forall x, v <= x < v + 56 -> exists b, mbyte SEGS m x = Some b).
{ intros x Hx.
  destruct (Z_lt_le_dec x (v + 4)) as [H1|H1]; [exact (pnq_vm_byte m v 4 ty x Hv ltac:(lia))|].
  destruct (Z_lt_le_dec x (v + 8)) as [H2|H2]; [eexists; apply Hz; lia|].
  destruct (Z_lt_le_dec x (v + 16)) as [H3|H3]; [exact (pnq_vm_byte m (v + 8) 8 num x Hvn ltac:(lia))|].
  destruct (Z_lt_le_dec x (v + 24)) as [H4|H4]; [exact (pnq_vm_byte m (v + 16) 8 str x Hvs ltac:(lia))|].
  eexists; apply Hz; lia. }
split; [split; [exact Hal|]|].
{ intros x Hx. destruct (VIS x Hx) as [b Hb]. exact (pnq_wr m x b ltac:(lia) (NI x Hx) Hb). }
split; [split; [exact Hty | exact Hv]|].
split; [split; [exact Hnum | exact Hvn]|].
split; [split; [exact Hstr | exact Hvs]|].
split; [apply U; lia|]. split; [apply U; lia|]. split; [apply U; lia|]. apply U; lia.
Qed.

(* a node with no kids / keys block and at most its str block, freeable at any depth *)
Lemma pnq_fd : forall (m : word -> option byte) lblk v ty num str D d,
  pj_hdrR SEGS m v ty num str 0 0 0 0 -> NoDup D -> pj_apartR D v ->
  (str = 0 /\ D = [] \/ exists k, lblk str k /\ D = [(str, k)]) ->
  pj_fdR SEGS m lblk d v D.
Proof.
intros m lblk v ty num str D d HH HN HA HS.
assert (Hsh : forall Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop, Pi false 0 0 0 [] ->
          pj_fshapeR SEGS m lblk Pi v D).
{ intros Pi HPi. split; [exact HN|]. split; [exact HA|].
  exists ty, num, str, 0, 0, 0, 0, false, D, [], [], [].
  split; [exact HH|].
  split; [exact HS|].
  split; [left; split; [reflexivity|split; reflexivity]|].
  split; [left; split; [reflexivity|split; reflexivity]|].
  split; [cbn [app]; rewrite app_nil_r; apply Permutation_refl|exact HPi]. }
destruct d as [|d]; cbn [pj_fdR]; apply Hsh; [split; reflexivity | reflexivity].
Qed.

(* the node's bytes lie off the image (the client-image law of LAWS for the block or the fake frame that holds it, the
   stack above the image otherwise) *)
Lemma pnq_node_off : forall en, pv_pre B ARx en ->
  4096 <= pe_v en /\ pe_v en mod 8 = 0 /\ pe_v en + 56 < 2 ^ 64 /\
  (forall x, pe_v en <= x < pe_v en + 56 -> ~ in_img SEGS x).
Proof.
intros en HPRE.
destruct HPRE as (Hfpre & _ & _ & _ & _ & _ & _ & _ & Hrd & _ & _).
destruct Hfpre as ((HAR & _ & _ & _ & _ & Hstk & _) & _).
destruct Hstk as (_ & HSTK0 & Hceil & Hslo & _).
destruct Hrd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & _ & Hled0 & _ & _).
destruct Hnode as (Hv4 & Hv8 & _ & _ & Hat & Hamr & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (V64 : 0 <= pe_v en /\ pe_v en + 56 < 2 ^ 64) by (unfold amem_range in Hamr; lia).
split; [exact Hv4|]. split; [exact Hv8|]. split; [lia|].
intros x Hx.
destruct Hat as [(a0 & k & Hin & H1 & H2) | [(b & m & Hin & _ & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]]].
- destruct Hled0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (a0, k) Hin) as (Hk0 & Hab0 & _). cbn [fst snd] in Hk0, Hab0.
  pose proof (@cf_head_nonneg cp) as Hcf.
  apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ (a0 - cf_head) (k + cf_head) x HAR Hab0).
  unfold req_size. destruct (Z.eqb_spec (k + cf_head) 0); lia.
- apply (blk_img_x SEGS B ARx LAWS _ _ _ _ _ _ b m x HAR Hin).
  unfold req_size. destruct (Z.eqb_spec m 0); lia.
- apply (frm_img_x SEGS B ARx LAWS _ _ _ _ _ _ cid pos' x HAR Hin). lia.
- intros Hi. pose proof (@pa_segs_low _ B_prog_listing PA x Hi) as Hlo. lia.
Qed.

(* the token is shorter than 2 ^ 30: x[0, m) is a run of number characters of the text tb (x = skip rest is a suffix
   of tb, PvB_Model.pvm_skip_rest), so m <= maxrun tb < 2 ^ 30 (rd_pre's maxrun bound). Read by arm (d) below (the
   kit's PRH_Reader.v pj_cstrR `length + 1 < 2 ^ 32`) and by PvB_ND.v at the strtod row. *)
Lemma pnq_tok_short : forall en c y (m : nat), pv_pre B ARx en -> PjGrammar.skip (pe_rest en) = c :: y ->
  (pn_sg c < m <= length (c :: y))%nat -> pn_span (c :: y) (pn_sg c) m -> Z.of_nat m < 2 ^ 30.
Proof.
intros en c y m HPRE Hsk Hm Hsp.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
pose proof HRDP as (_ & _ & _ & _ & Hcur0 & _ & _ & _ & _ & _ & _ & Hmaxrun & _).
pose proof Hcur0 as (_ & _ & _ & _ & _ & _ & _ & Hp0 & Hlen0 & _).
pose proof (pvm_skip_rest (pe_tb en) (pe_text en) (pe_len en) (pe_p en) Hlen0 Hp0) as [Hrest1 _].
change (rest_atR (pe_tb en) (pe_text en) (pe_p en)) with (pe_rest en) in Hrest1. rewrite Hsk in Hrest1.
assert (HSK : skipn (Z.to_nat (pn_p1 en (c :: y) - pe_text en)) (pe_tb en) = c :: y) by exact Hrest1.
pose proof (pnq_txt_numch c y m (proj1 Hm) Hsp) as HNUM.
assert (Hmr : (m <= PjRoundTrip.maxrun (pe_tb en))%nat).
{ apply (pnq_maxrun (pe_tb en) (Z.to_nat (pn_p1 en (c :: y) - pe_text en)) m); rewrite HSK; [exact HNUM | lia]. }
lia.
Qed.

(* ---- THE PACKAGING: the arm's outcome is parse_value's post part ---- *)
Theorem pnQ : pnQ_stmt B ARx.
Proof.
intros en pos code lyc Sc Hpc W' mem HPRE HOUT.
assert (E64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
assert (E32 : 2 ^ 32 = 4294967296) by reflexivity.
pose proof (pnq_node_off en HPRE) as (Hv4 & Hv8 & V64 & NIMG).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hrd0 & _ & _).
destruct Hrd0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & _ & Hled0 & _ & _).
destruct Hnode as (_ & _ & _ & Hz0 & _ & _ & _ & _).
pose proof Hled0 as ((_ & _ & _ & _ & _ & _ & _ & Hlive0 & _ & Hcnt0 & _) & _).
pose proof (@cf_head_nonneg cp) as Hch.
(* the node's bytes the arm did not write are the entry's zeros *)
assert (ZK : forall NW : Z -> Prop,
  (forall a, pe_v en <= a < pe_v en + 56 -> ~ NW a ->
     aview SEGS (w_H W') mem a = aview SEGS (w_H (pe_W en)) (pe_mem en) a) ->
  forall x, pe_v en <= x < pe_v en + 56 -> ~ NW x -> mbyte SEGS (rdW W' mem) x = Some (Z_to_bv 8 0)).
{ intros NW Hk x Hx Hn. apply pnq_byte0. rewrite (Hk x Hx Hn). exact (pnq_zero_at _ _ _ x Hz0 Hx). }
destruct HOUT as (c & y & HOUT). cbv zeta in HOUT.
destruct HOUT as (Hsk & Hc1 & Hc2 & Hc3 & Hc4 & Hc5 & Hc6 & HARM).
assert (HJ : forall ok, PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok =
  PjGrammar.jr_number prh_jr_strtod (c :: y) ok) by (intros ok; apply pnq_value; assumption).
(* the number is a leaf: its frees are lf of its trace (PvB_Frees.pvf_frees_leaf) *)
assert (Efr : forall ok, prhPv_frees (pe_d en) (pe_rest en) ok =
  PresetReqAt.lf (snd (fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) ok))))
  by (intros ok; exact (PvB_Frees.pvf_frees_leaf _ _ ok c y Hsk Hc1 Hc2)).
(* the grant-all run at a scanned token: the one allocation EAlloc (S m), the granted result (pnq_gt_go) *)
assert (HG : forall m, pn_lead (c :: y) (pn_sg c) -> (pn_sg c < m <= length (c :: y))%nat ->
  pn_span (c :: y) (pn_sg c) m -> pn_stop (c :: y) m ->
  pe_gt en = [PjGrammar.EAlloc (S m)] /\
  fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) []) =
  fst (PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [true])).
{ intros m Hl Hm Hsp Hst. unfold pe_gt, prhPv_gtrace. rewrite !HJ.
  exact (pnq_gt_go prh_jr_strtod c y m Hl Hm Hsp Hst). }
unfold pv_Qm.
destruct HARM as [HA|[HA|[HA|HA]]].
- (* (a) refused before any allocation: the node as at entry, the cursor at p1, the allocator state pv_reader0's *)
  destruct HA as (Ecode & Hnl & EHp & (Rfr & Rab & Rbb & (Rlive & _ & _) & Rin & _ & _ & Rv & _ & Rled & Rpos & Rsec)).
  assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [] = (None, [], []))
    by (rewrite HJ; exact (pnq_num_refuse prh_jr_strtod c y [] Hnl)).
  assert (Z0 : forall x, pe_v en <= x < pe_v en + 56 -> mbyte SEGS (rdW W' mem) x = Some (Z_to_bv 8 0))
    by (intros x Hx; exact (ZK (fun _ => False) (fun a Ha _ => Rv a Ha) x Hx (fun H => H))).
  assert (HH : pj_hdrR SEGS (rdW W' mem) (pe_v en) 0 0 0 0 0 0 0).
  { apply pnq_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | | lia | | lia | | intros x Hx; apply Z0; lia];
      apply pnq_val0; intros x Hx; apply Z0; lia. }
  exists [], None, [], [], [], (pe_Lam en), (pe_peak en), (pe_cnt en), (pe_fail en), (pe_ran en).
  split; [exact HM|]. split; [rewrite EHp; exact Rled|].
  split; [exact Rlive|].
  (* no allocator call: no hull use (the meters are the entry's, pv_reader0's secs_same) *)
  split; [exact (PresetHullBudget.hull_used_same (pe_S en) Sc _ Rsec)|].
  split; [exact (rp_nil [] _ _ eq_refl Rpos)|].
  split.
  { apply (pv_outc_nil en None [] Sc); [unfold pe_gt, prhPv_gtrace; rewrite HM; reflexivity
      | rewrite HM; reflexivity | exact Rpos]. }
  (* no call: no injected failure to reach *)
  split; [intros sm x os i H0 hist _ _ _ F; exfalso; unfold pe_gt, prhPv_gtrace in F; rewrite HM in F; cbn in F;
    lia|].
  split; [apply pnq_move_none; lia|].
  split; [intros a k []|].
  split; [rewrite Rab; apply Permutation_refl|].
  split; [cbv beta; rewrite Rfr; apply Permutation_refl|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) []) as Hh; rewrite HM in Hh; exact Hh|].
  split; [rewrite Rbb; unfold prh_held; cbn [PjGrammar.held PjGrammar.calls]; lia|].
  split; [reflexivity|].
  split; [exact Ecode|].
  (* the free order: none (the empty trace's lf), the node's header all zero *)
  split.
  { intros _ n _. exists []. split; [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) 0 HH)|].
    rewrite Efr, HM. reflexivity. }
  split; [exact (pnq_after _ _ _ _ _ _ _ _ Rin)|].
  apply (pnq_fd _ _ _ 0 0 0); [exact HH | constructor | intros b x [] | left; split; reflexivity].
- (* (b) fuzz_malloc returned NULL, v->str = 0 stored; off the grant-all run *)
  destruct HA as (Ecode & Hl & m & lyc0 & Sc0 & W0 & mem0 & Hm & Hsp & Hst & HR0 & HAP & Hroom &
    (Hpos & Hnull & Hhull) & Hfr & Hrd & Hv16).
  destruct HR0 as (Rfr & Rab & Rbb & _ & _ & _ & _ & _ & _ & _).
  destruct Hrd as (Rin & _ & Rv & _).
  assert (HAP' : exists peak' fail' ran', Hpc = pe_Hp en /\ ablocks B lyc Sc = ablocks B lyc0 Sc0 /\
    prh_ledger B lyc Sc Hpc W' mem (pe_Lam en) peak' ((pe_cnt en + 1) mod 2 ^ 64) fail' ran' (pe_most en)
      (pe_own en) /\
    (pe_cnt en = pe_fail en /\ peak' = pe_peak en /\ fail' = SIZE_MAXZ /\ ran' = pe_ran en \/
     pe_cnt en <> pe_fail en /\
     peak' = Z.max (pe_peak en) (Z.min SIZE_MAXZ (Ledger.lsum (pe_Lam en) + (Z.of_nat m + 1))) /\
     fail' = pe_fail en /\ ran' = (if Z.of_nat m + 1 <=? pe_most en then 1 else pe_ran en))).
  { destruct HAP as [(Ecf & _ & EHp & Eab & Hled) | [(Ecf & _ & EHp & Eab & _ & _ & Hled) | (_ & Hres & _)]].
    - exists (pe_peak en), SIZE_MAXZ, (pe_ran en). split; [exact EHp|]. split; [exact Eab|]. split; [exact Hled|].
      left; split; [exact Ecf|split; [reflexivity|split; reflexivity]].
    - eexists _, (pe_fail en), _. split; [exact EHp|]. split; [exact Eab|]. split; [exact Hled|].
      right; split; [exact Ecf|split; [reflexivity|split; reflexivity]].
    - clear - Hres Hch. lia. }
  destruct HAP' as (peak' & fail' & ran' & EHp & Eab & Hled & Hdisj).
  assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [false] =
               (None, [PjGrammar.EFail (S m)], [])).
  { rewrite HJ, (pnq_num_go prh_jr_strtod c y [false] m Hl Hm Hsp Hst). reflexivity. }
  destruct (HG m Hl Hm Hsp Hst) as (Egt & _).
  assert (Z0 : forall x, pe_v en <= x < pe_v en + 56 -> mbyte SEGS (rdW W' mem) x = Some (Z_to_bv 8 0)).
  { intros x Hx. destruct (Z_lt_le_dec x (pe_v en + 16)) as [H1|H1];
      [apply (ZK _ Rv x Hx); cbv beta; lia|].
    destruct (Z_lt_le_dec x (pe_v en + 24)) as [H2|H2];
      [apply (pnq_val0_byte _ (pe_v en + 16) x Hv16); lia|].
    apply (ZK _ Rv x Hx); cbv beta; lia. }
  assert (HH : pj_hdrR SEGS (rdW W' mem) (pe_v en) 0 0 0 0 0 0 0).
  { apply pnq_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | | lia | | lia | | intros x Hx; apply Z0; lia];
      apply pnq_val0; intros x Hx; apply Z0; lia. }
  exists [false], None, [PjGrammar.EFail (S m)], [], [], (pe_Lam en), peak', ((pe_cnt en + 1) mod 2 ^ 64),
    fail', ran'.
  split; [exact HM|]. split; [exact Hled|]. split; [exact Hroom|].
  split; [rewrite Egt; exact Hhull|].
  split; [exact (rp_nil [PjGrammar.EFail (S m)] _ _ eq_refl Hpos)|].
  split.
  { (* no grant-all run reaches this arm: at cnt = fail the run's fail-counter clause is false (one call), at
       cnt <> fail the consumed granted request returns no NULL (the cut's pn_null_off) *)
    unfold pv_outc. intros sm x os i H0 hist P R C F. exfalso. rewrite Egt in R, C, F.
    destruct (Z.eq_dec (pe_cnt en) (pe_fail en)) as [E|E].
    - cbn [PjGrammar.calls PjGrammar.is_call] in F. clear - E F. lia.
    - exact (Hnull E sm x os i H0 hist P R C). }
  (* the injected reading: its window is the one call (cnt <= fail < cnt + 1), so the refusal is the chosen one *)
  split.
  { intros sm x os i H0 hist _ _ _ F j Hj _. rewrite Egt in F.
    cbn [PjGrammar.calls PjGrammar.is_call] in F, Hj. clear - F Hj. lia. }
  split; [rewrite Egt; apply (pnq_move_fail _ _ _ _ _ (pe_most en)); [clear - Hlive0; lia | exact Hdisj]|].
  split; [intros a k []|].
  split; [rewrite Eab, Rab; apply Permutation_refl|].
  split; [cbv beta; rewrite Hfr, Rfr; apply Permutation_refl|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [false]) as Hh; rewrite HM in Hh; exact Hh|].
  split; [rewrite (pnq_bb B lyc Sc), Eab, <- (pnq_bb B lyc0 Sc0), Rbb; unfold prh_held;
    cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [reflexivity|].
  split; [exact Ecode|].
  (* the free order: none (lf of a refused trace), the node's header all zero (v->str = 0) *)
  split.
  { intros _ n _. exists []. split; [exact (PvB_Frees.pvf_zero_foR SEGS _ _ n (pe_v en) 0 HH)|].
    rewrite Efr, HM. reflexivity. }
  split; [exact (pnq_after _ _ _ _ _ _ _ _ Rin)|].
  apply (pnq_fd _ _ _ 0 0 0); [exact HH | constructor | intros b x [] | left; split; reflexivity].
- (* (c) allocated, but not whole or not finite: the block stays the node's str *)
  destruct HA as (Ecode & Hl & m & res & bits & cn & Hm & Hsp & Hst & Hok & Hfr & Hroom & Hpos & Hrd & Hv16 & Hv8' &
    Hgarr & Hsm & Hcn & Hbad).
  destruct Hok as (Ecf & Hres & _ & _ & Hr64 & Hfresh & Hap & EHp & Eab & _ & _ & Hled).
  destruct Hrd as (Rin & _ & Rv & _).
  pose proof (pnq_bits_range _ _ _ Hsm) as Hb64.
  assert (Hlt : length (firstn m (c :: y)) = m) by (apply pnq_len_firstn; lia).
  assert (Hsm' : prh_jr_strtod (firstn m (c :: y)) = (cn, bits)).
  { unfold prh_jr_strtod. unfold strtod_c.strtod_model in Hsm. rewrite Hsm. reflexivity. }
  assert (Hwh : PjGrammar.whole prh_jr_strtod (firstn m (c :: y)) = false).
  { unfold PjGrammar.whole. rewrite Hsm', Hlt. cbn [fst snd].
    destruct Hbad as [Hb|Hb]; [rewrite (proj2 (Z.eqb_neq cn (Z.of_nat m)) Hb); reflexivity|].
    rewrite Hb. apply Bool.andb_false_r. }
  assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [true] =
               (None, [PjGrammar.EAlloc (S m)], [])).
  { rewrite HJ, (pnq_num_go prh_jr_strtod c y [true] m Hl Hm Hsp Hst). cbn [PjGrammar.take]. rewrite Hwh.
    reflexivity. }
  destruct (HG m Hl Hm Hsp Hst) as (Egt & Ej0).
  assert (HH : pj_hdrR SEGS (rdW W' mem) (pe_v en) 0 bits res 0 0 0 0).
  { apply pnq_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | | exact Hb64 | exact Hv8' | lia | exact Hv16 |].
    - apply pnq_val0. intros x Hx. apply (ZK _ Rv x); cbv beta; lia.
    - intros x Hx. apply (ZK _ Rv x); cbv beta; lia. }
  assert (HND : NoDup [(res, Z.of_nat m + 1)])
    by (first [apply NoDup_singleton | constructor; [intros Hin; inversion Hin | constructor]]).
  assert (HAPT : pj_apartR [(res, Z.of_nat m + 1)] (pe_v en)).
  { intros b x [<-|[]] Hx. unfold pj_holdsR in Hx. cbn [fst snd] in Hx. apply (Hap x). lia. }
  exists [true], None, [PjGrammar.EAlloc (S m)], [], [(res, Z.of_nat m + 1)], ((res, Z.of_nat m + 1) :: pe_Lam en),
    (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat m + 1))), ((pe_cnt en + 1) mod 2 ^ 64), (pe_fail en),
    (pe_ran en).
  split; [exact HM|]. split; [exact Hled|]. split; [exact Hroom|].
  split; [rewrite Egt; exact (proj2 Hpos)|].
  split; [exact (proj1 Hpos)|].
  split.
  { (* the grant-all run: g_ran_out kept, the granted result, the position moved by pn_rp1 *)
    unfold pv_outc. intros sm x os i H0 hist P R _ _. split; [reflexivity|].
    split; [rewrite Ej0, HM; reflexivity|].
    rewrite Egt in R |- *. exact (proj2 (proj1 Hpos) sm x os i H0 hist P R). }
  (* the injected reading: the one call granted (ok = [true]), no failed outcome *)
  split.
  { intros sm x os i H0 hist _ _ _ _ j Hj Hn. cbn [PjGrammar.calls PjGrammar.is_call] in Hj.
    assert (Ej : j = 0%nat) by (clear - Hj; lia). subst j. cbn in Hn. discriminate Hn. }
  split; [rewrite Egt; apply pnq_move_alloc; [exact Ecf | clear - Hlive0; lia]|].
  split; [intros a k [Eak|[]]; injection Eak as <- <-; exact Hfresh|].
  split; [rewrite Eab; unfold prhReader_ab; cbn [map fst snd]; apply Permutation_app_comm|].
  split; [cbv beta; rewrite Hfr; apply Permutation_refl|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [true]) as Hh; rewrite HM in Hh; exact Hh|].
  split; [rewrite (pnq_bb B lyc Sc), Eab, bsum_app, <- (pnq_bb B (pe_ly en) (pe_S en)); unfold prh_held, bsum;
    cbn [fold_right snd PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [exact Ecode|].
  (* the free order: the str block, the model's lf of the granted trace *)
  split.
  { intros HHD n _. exists [(res, Z.of_nat m + 1)]. split.
    - apply (PvB_Frees.pvf_hdr_leaf_foR SEGS _ _ n (pe_v en) _ 0 bits res HH);
        [right; exists (Z.of_nat m + 1); split; [left; reflexivity|reflexivity] | exact HND | exact HAPT].
    - rewrite Efr, HM. cbn [fst snd map]. rewrite PvB_Frees.pvf_lf_one, HHD. f_equal. lia. }
  split; [exact (pnq_after _ _ _ _ _ _ _ _ Rin)|].
  apply (pnq_fd _ _ _ 0 bits res); [exact HH | exact HND | exact HAPT |].
  right. exists (Z.of_nat m + 1). split; [left; reflexivity|reflexivity].
- (* (d) read: the node is JNum txt bits, the cursor past the token *)
  destruct HA as (Ecode & Hl & m & res & bits & Hm & Hsp & Hst & Hok & Hfr & Hroom & Hrp1 & Hrd & Hv0 & Hv16 & Hv8' &
    Hgarr & Hsm & Hfin).
  destruct Hok as (Ecf & Hres & _ & _ & Hr64 & Hfresh & Hap & EHp & Eab & _ & _ & Hled).
  destruct Hrd as (Rin & _ & Rv & _).
  pose proof (pnq_bits_range _ _ _ Hsm) as Hb64.
  assert (Hlt : length (firstn m (c :: y)) = m) by (apply pnq_len_firstn; lia).
  assert (Hsm' : prh_jr_strtod (firstn m (c :: y)) = (Z.of_nat m, bits)).
  { unfold prh_jr_strtod. unfold strtod_c.strtod_model in Hsm. rewrite Hsm. reflexivity. }
  assert (Hwh : PjGrammar.whole prh_jr_strtod (firstn m (c :: y)) = true).
  { unfold PjGrammar.whole. rewrite Hsm', Hlt. cbn [fst snd]. rewrite Z.eqb_refl, Hfin. reflexivity. }
  assert (HM : PjGrammar.jr_value prh_jr_strtod (pe_d en) (pe_rest en) [true] =
               (Some (PjTree.JNum (firstn m (c :: y)) bits, skipn m (c :: y)), [PjGrammar.EAlloc (S m)], [])).
  { rewrite HJ, (pnq_num_go prh_jr_strtod c y [true] m Hl Hm Hsp Hst). cbn [PjGrammar.take]. rewrite Hwh, Hsm'.
    reflexivity. }
  destruct (HG m Hl Hm Hsp Hst) as (Egt & Ej0).
  (* the node: a number leaf holding the token's block *)
  assert (HNODE : pj_nodeR SEGS (rdW W' mem) (prh_lin ((res, Z.of_nat m + 1) :: pe_Lam en)) (pe_v en)
    (PjTree.JNum (firstn m (c :: y)) bits) [(res, Z.of_nat m + 1)]).
  { cbn [pj_nodeR PjTree.tag].
    split; [first [apply NoDup_singleton | constructor; [intros Hin; inversion Hin | constructor]]|].
    split; [intros b x [<-|[]] Hx; unfold pj_holdsR in Hx; cbn [fst snd] in Hx; apply (Hap x); lia|].
    exists bits, res, 0, 0, 0, 0.
    split.
    { apply pnq_hdr; [exact Hv8 | lia | lia | exact NIMG | lia | exact Hv0 | exact Hb64 | exact Hv8' | lia | exact Hv16 |].
      intros x Hx. apply (ZK _ Rv x); cbv beta; lia. }
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists (Z.of_nat m + 1). split; [|reflexivity].
    split; [left; reflexivity|]. split; [rewrite Hlt; lia|].
    (* the kit's pj_cstrR bound (PRH_Reader.v 91d2dbd40054): the token is shorter than 2 ^ 30 *)
    split; [pose proof (pnq_tok_short en c y m HPRE Hsk Hm Hsp) as H30;
      assert (E30 : 2 ^ 30 = 1073741824) by reflexivity; rewrite Hlt; lia|].
    split; [|exact Hgarr].
    eapply Forall_impl; [|exact (pnq_txt_numch c y m (proj1 Hm) Hsp)].
    intros b Hb. pose proof (pnq_numch_range b Hb). lia. }
  exists [true], (Some (PjTree.JNum (firstn m (c :: y)) bits, skipn m (c :: y))), [PjGrammar.EAlloc (S m)], [],
    [(res, Z.of_nat m + 1)], ((res, Z.of_nat m + 1) :: pe_Lam en),
    (Z.max (pe_peak en) (Ledger.lsum (pe_Lam en) + (Z.of_nat m + 1))), ((pe_cnt en + 1) mod 2 ^ 64), (pe_fail en),
    (pe_ran en).
  split; [exact HM|]. split; [exact Hled|]. split; [exact Hroom|].
  split; [rewrite Egt; exact (proj2 Hrp1)|].
  split; [exact (proj1 Hrp1)|].
  split.
  { (* the grant-all run: g_ran_out kept, the granted result, the position moved by pn_rp1 *)
    unfold pv_outc. intros sm x os i H0 hist P R _ _. split; [reflexivity|].
    split; [rewrite Ej0, HM; reflexivity|].
    rewrite Egt in R |- *. exact (proj2 (proj1 Hrp1) sm x os i H0 hist P R). }
  (* the injected reading: the one call granted (ok = [true]), no failed outcome *)
  split.
  { intros sm x os i H0 hist _ _ _ _ j Hj Hn. cbn [PjGrammar.calls PjGrammar.is_call] in Hj.
    assert (Ej : j = 0%nat) by (clear - Hj; lia). subst j. cbn in Hn. discriminate Hn. }
  split; [rewrite Egt; apply pnq_move_alloc; [exact Ecf | clear - Hlive0; lia]|].
  split; [intros a k [Eak|[]]; injection Eak as <- <-; exact Hfresh|].
  split; [rewrite Eab; unfold prhReader_ab; cbn [map fst snd]; apply Permutation_app_comm|].
  split; [cbv beta; rewrite Hfr; apply Permutation_refl|].
  split; [pose proof (pvm_hpeak prh_jr_strtod (pe_d en) (pe_rest en) [true]) as Hh; rewrite HM in Hh; exact Hh|].
  split; [rewrite (pnq_bb B lyc Sc), Eab, bsum_app, <- (pnq_bb B (pe_ly en) (pe_S en)); unfold prh_held, bsum;
    cbn [fold_right snd PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call]; lia|].
  split; [cbn [Ledger.lsum PjGrammar.held PjGrammar.held_ev]; lia|].
  split; [exact Ecode|].
  (* the free order: the node's one block, the model's lf of the granted trace *)
  split.
  { intros HHD n _. exists [(res, Z.of_nat m + 1)]. split.
    - exact (PvB_Frees.pvf_node_leaf_foR SEGS _ _ n (pe_v en) _ _ HNODE
        ltac:(intros ? E; discriminate E) ltac:(intros ? E; discriminate E)).
    - rewrite Efr, HM. cbn [fst snd map]. rewrite PvB_Frees.pvf_lf_one, HHD. f_equal. lia. }
  split.
  { assert (Hpos : pe_text en + pe_len en - Z.of_nat (length (skipn m (c :: y))) = pn_p1 en (c :: y) + Z.of_nat m).
    { unfold pn_p1. rewrite length_skipn. lia. }
    rewrite Hpos. exact Rin. }
  split; [exact HNODE|].
  split; [exact (PvB_Frees.pvf_ncap_leaf SEGS _ (pe_v en) (PjTree.JNum (firstn m (c :: y)) bits)
    ltac:(intros ? E; discriminate E) ltac:(intros ? E; discriminate E))|].
  pose proof (PjGrammar.G10_1 prh_jr_strtod (pe_d en) (pe_rest en) [true] _ _ _ _ HM) as Hg.
  cbn [PjGrammar.held PjGrammar.held_ev Ledger.lsum] in Hg |- *. lia.
Qed.

End c.
