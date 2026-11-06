(* reac-pw/fuzz_segconf: FFR proved. segconf's printf family FR_seg (lib/B/Rt/RtPFSeg.v, the image-B wrapper-layer owner) renders each
   of refuse's 19 formats (refuse_pft.REFUSE_ALL_FMTS: the two address prefixes and the 17 refusal formats) at
   SegModel.fmt's text, for the arguments refuse's callers give (refuse_pft.ffr_family, which the image-A walk of
   the image-A G3 walk owner assumed). A sub-lane of the image-B refuse walk lane (the image-B G3 walk owner), 2026-10-30. A model lemma: no function of the
   binary is walked here.

   IMAGE-INDEPENDENT: this file Requires no listing, no Pa* engine module and no image module of its own; the image
   copy of the image-A G3 walk owner takes it to lib/A by changing the Require paths only.

   The proof:
   - each of the 19 formats is lexed (rbf_lex) into tokens (literal bytes, %s, %d, %zu, %.24s) whose bytes
     (rbf_render) are the format again; rbf_chk_all checks this, and that each literal byte is in 1 .. 255 and not
     '%', and that the format is not empty, by one vm_compute on the closed list REFUSE_ALL_FMTS;
   - rbf_text, by induction on the tokens: seg_parse gives the pieces (PRel (PLit b), PRel Ps, PRel Pd, Pzu, P24s),
     the arguments are APtr s for %s and %.24s, AInt z for %d, AU64 z for %zu (rbf_rel), and seg_text renders
     SegModel.fmt's text: cut_nul s = s for a NUL-free s (rbf_cut), pf_dec z = SegModel.dec z for 0 <= z < 2 ^ 31
     (rbf_dec: pf_digits and dec_go are the same digit loop, and 11 digits of fuel are enough below 10 ^ 11), and
     pf_udec z = SegModel.dec z for 0 <= z (rbf_udec); no piece is %.*s, so seg_prec_pos holds;
   - the reader facts: ffr_arg's string facts give pf_arg_asan's (rbf_ptr; the read span seg_spec.cstr_span w s
     is str_end w s - w, rbf_span) and the two slack facts cmd_args_slack / cmd_args_amem; ffr_fmt gives fmt_at
     (rbf_fmt_at) and the two bounds 0x10000 <= f, f + |fmt| + 1 <= gotw. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_pft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======== the formats as tokens ======== *)
Inductive rbf_tok : Type := rtL (b : Z) | rtS | rtD | rtZU | rt24S.

(* a token's bytes: the literal byte, "%s", "%d", "%zu", "%.24s" *)
Fixpoint rbf_render (ts : list rbf_tok) : list Z :=
  match ts with
  | [] => []
  | rtL b :: r => b :: rbf_render r
  | rtS :: r => 37 :: 115 :: rbf_render r
  | rtD :: r => 37 :: 100 :: rbf_render r
  | rtZU :: r => 37 :: 122 :: 117 :: rbf_render r
  | rt24S :: r => 37 :: 46 :: 50 :: 52 :: 115 :: rbf_render r
  end.

(* the lexer, run on closed formats only (rbf_chk_all) *)
Fixpoint rbf_lex (f : list Z) : option (list rbf_tok) :=
  match f with
  | [] => Some []
  | c :: f1 =>
      if c =? 37 then
        match f1 with
        | c1 :: f2 =>
            if c1 =? 115 then option_map (cons rtS) (rbf_lex f2)
            else if c1 =? 100 then option_map (cons rtD) (rbf_lex f2)
            else match f2 with
                 | c2 :: f3 =>
                     if (c1 =? 122) && (c2 =? 117) then option_map (cons rtZU) (rbf_lex f3)
                     else match f3 with
                          | c3 :: c4 :: f5 =>
                              if (c1 =? 46) && (c2 =? 50) && (c3 =? 52) && (c4 =? 115)
                              then option_map (cons rt24S) (rbf_lex f5) else None
                          | _ => None
                          end
                 | [] => None
                 end
        | [] => None
        end
      else option_map (cons (rtL c)) (rbf_lex f1)
  end.

(* a literal byte is 1 .. 255 and not '%' *)
Definition rbf_tokb (t : rbf_tok) : bool :=
  match t with rtL b => negb (b =? 37) && ((0 <? b) && (b <? 256)) | _ => true end.

Definition rbf_chk (f : list Z) : bool :=
  match rbf_lex f with
  | Some ts => SegModel.leqb (rbf_render ts) f && forallb rbf_tokb ts && negb (Nat.eqb (length f) 0)
  | None => false
  end.

Lemma rbf_chk_all : forallb rbf_chk REFUSE_ALL_FMTS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rbf_lex_ok : forall fmt, In fmt REFUSE_ALL_FMTS ->
  exists ts, rbf_render ts = fmt /\ forallb rbf_tokb ts = true /\ fmt <> [].
Proof.
intros fmt Hin. pose proof rbf_chk_all as H. rewrite forallb_forall in H. specialize (H fmt Hin).
unfold rbf_chk in H. destruct (rbf_lex fmt) as [ts|]; [|discriminate H].
apply andb_prop in H as [H Hne]. apply andb_prop in H as [Heq Htok].
apply SegModel.leqb_eq in Heq. exists ts. split; [exact Heq|]. split; [exact Htok|].
intros ->. discriminate Hne.
Qed.

(* ======== one step of each function at each token ======== *)
Lemma rbf_eq_L : forall b r, (b =? 37) = false -> (0 <? b) && (b <? 256) = true ->
  seg_parse (b :: r) = option_map (cons (PRel (PLit b))) (seg_parse r) /\
  seg_spec.conv_kinds (b :: r) = seg_spec.conv_kinds r /\
  (forall xs, SegModel.fmt (b :: r) xs = b :: SegModel.fmt r xs).
Proof.
intros b r H1 H2. split; [|split; [|intros xs]].
- cbn [seg_parse]. rewrite H1, H2. reflexivity.
- cbn [seg_spec.conv_kinds]. rewrite H1. reflexivity.
- cbn [SegModel.fmt]. rewrite H1. reflexivity.
Qed.

Lemma rbf_eq_S : forall r,
  seg_parse (37 :: 115 :: r) = option_map (cons (PRel Ps)) (seg_parse r) /\
  seg_spec.conv_kinds (37 :: 115 :: r) = true :: seg_spec.conv_kinds r /\
  (forall s xs, SegModel.fmt (37 :: 115 :: r) (SegModel.AS s :: xs) = SegModel.cut_nul s ++ SegModel.fmt r xs).
Proof. intros r. split; [reflexivity|split; [reflexivity|intros s xs; reflexivity]]. Qed.

Lemma rbf_eq_D : forall r,
  seg_parse (37 :: 100 :: r) = option_map (cons (PRel Pd)) (seg_parse r) /\
  seg_spec.conv_kinds (37 :: 100 :: r) = false :: seg_spec.conv_kinds r /\
  (forall z xs, SegModel.fmt (37 :: 100 :: r) (SegModel.AI z :: xs) = SegModel.dec z ++ SegModel.fmt r xs).
Proof. intros r. split; [reflexivity|split; [reflexivity|intros z xs; reflexivity]]. Qed.

Lemma rbf_eq_ZU : forall r,
  seg_parse (37 :: 122 :: 117 :: r) = option_map (cons Pzu) (seg_parse r) /\
  seg_spec.conv_kinds (37 :: 122 :: 117 :: r) = false :: seg_spec.conv_kinds r /\
  (forall z xs, SegModel.fmt (37 :: 122 :: 117 :: r) (SegModel.AI z :: xs) = SegModel.dec z ++ SegModel.fmt r xs).
Proof. intros r. split; [reflexivity|split; [reflexivity|intros z xs; reflexivity]]. Qed.

Lemma rbf_eq_24S : forall r,
  seg_parse (37 :: 46 :: 50 :: 52 :: 115 :: r) = option_map (cons P24s) (seg_parse r) /\
  seg_spec.conv_kinds (37 :: 46 :: 50 :: 52 :: 115 :: r) = true :: seg_spec.conv_kinds r /\
  (forall s xs, SegModel.fmt (37 :: 46 :: 50 :: 52 :: 115 :: r) (SegModel.AS s :: xs) =
     firstn 24 (SegModel.cut_nul s) ++ SegModel.fmt r xs).
Proof. intros r. split; [reflexivity|split; [reflexivity|intros s xs; reflexivity]]. Qed.

(* ======== the texts of the conversions ======== *)
Lemma rbf_cut : forall s, Forall (fun c => 0 < c < 256) s -> SegModel.cut_nul s = s.
Proof.
induction 1 as [|c s Hc Hs IH]; [reflexivity|].
cbn [SegModel.cut_nul]. destruct (Z.eqb_spec c 0); [lia|]. rewrite IH. reflexivity.
Qed.

Lemma rbf_dg_S : forall n x acc, SegModel.dec_go (S n) x acc =
  if x <? 10 then (48 + x mod 10) :: acc else SegModel.dec_go n (x / 10) ((48 + x mod 10) :: acc).
Proof. reflexivity. Qed.

Lemma rbf_dg_pf : forall n x acc, 0 <= x -> pf_digits n x acc = SegModel.dec_go n x acc.
Proof.
induction n as [|n IH]; intros x acc Hx; [reflexivity|].
rewrite rbf_dg_S. cbn [pf_digits].
destruct (Z.ltb_spec x 10) as [Hlt|Hge].
- rewrite (Z.mod_small x 10) by lia. reflexivity.
- apply IH. apply Z.div_pos; lia.
Qed.

Lemma rbf_dg_fuel : forall n x acc, 0 <= x < 10 ^ Z.of_nat (S n) ->
  forall m, SegModel.dec_go (S n + m) x acc = SegModel.dec_go (S n) x acc.
Proof.
induction n as [|n IH]; intros x acc Hx m.
- change (10 ^ Z.of_nat 1) with 10 in Hx.
  change (S 0 + m)%nat with (S m). rewrite !rbf_dg_S.
  destruct (Z.ltb_spec x 10); [reflexivity|lia].
- change (S (S n) + m)%nat with (S (S n + m)).
  rewrite (rbf_dg_S (S n + m) x acc), (rbf_dg_S (S n) x acc).
  destruct (Z.ltb_spec x 10); [reflexivity|].
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia.
  apply IH. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma rbf_dec : forall z, 0 <= z < 2 ^ 31 -> pf_dec z = SegModel.dec z.
Proof.
intros z Hz. unfold pf_dec, SegModel.dec.
destruct (Z.ltb_spec z 0); [lia|]. cbv beta iota.
rewrite rbf_dg_pf by lia.
assert (H11 : 0 <= z < 10 ^ Z.of_nat (S 10)).
{ change (10 ^ Z.of_nat (S 10)) with 100000000000. lia. }
change 20%nat with (S 10 + 9)%nat. rewrite (rbf_dg_fuel 10 z [] H11 9). reflexivity.
Qed.

Lemma rbf_udec : forall z, 0 <= z -> pf_udec z = SegModel.dec z.
Proof.
intros z Hz. unfold pf_udec, SegModel.dec.
destruct (Z.ltb_spec z 0); [lia|]. cbv beta iota. apply rbf_dg_pf; lia.
Qed.

(* ======== the argument shapes ======== *)
(* the argument of a conversion: APtr s for %s and %.24s, AInt z for %d, AU64 z for %zu *)
Definition rbf_rel (x : SegModel.arg) (a : pf_arg) : Prop :=
  match x, a with
  | SegModel.AS s, APtr s' => s' = s
  | SegModel.AI z, AInt z' => z' = z
  | SegModel.AI z, AU64 z' => z' = z
  | _, _ => False
  end.

(* what the text needs of an argument (ffr_arg gives it) *)
Definition rbf_xok (x : SegModel.arg) : Prop :=
  match x with SegModel.AS s => Forall (fun c => 0 < c < 256) s | SegModel.AI z => 0 <= z < 2 ^ 31 end.

(* the text: the pieces seg_parse reads, the arguments, seg_text's text is SegModel.fmt's *)
Lemma rbf_text : forall ts xs,
  forallb rbf_tokb ts = true ->
  seg_spec.conv_kinds (rbf_render ts) = map seg_spec.arg_is_s xs ->
  Forall rbf_xok xs ->
  exists qs args, seg_parse (rbf_render ts) = Some qs /\ Forall2 rbf_rel xs args /\
    seg_text qs args = Some (SegModel.fmt (rbf_render ts) xs) /\ seg_prec_pos qs args.
Proof.
induction ts as [|t ts IH]; intros xs Hok Hck Hx.
- destruct xs as [|x xs]; [|discriminate Hck].
  exists [], []. split; [reflexivity|]. split; [constructor|]. split; [reflexivity|exact I].
- cbn [forallb] in Hok. apply andb_prop in Hok as [Ht0 Hok].
  destruct t as [b| | | |]; cbn [rbf_tokb] in Ht0; cbn [rbf_render] in Hck |- *.
  + (* a literal byte *)
    apply andb_prop in Ht0 as [Hb1 Hb2]. apply negb_true_iff in Hb1.
    destruct (rbf_eq_L b (rbf_render ts) Hb1 Hb2) as (Ep & Ec & Ef).
    rewrite Ec in Hck. destruct (IH xs Hok Hck Hx) as (qs & args & Hp & Hr & Ht & Hpp).
    exists (PRel (PLit b) :: qs), args. rewrite Ep, Hp, Ef.
    split; [reflexivity|]. split; [exact Hr|]. split; [|exact Hpp].
    cbn [seg_text seg_step]. rewrite Ht. reflexivity.
  + (* %s *)
    destruct (rbf_eq_S (rbf_render ts)) as (Ep & Ec & Ef). rewrite Ec in Hck.
    destruct xs as [|x xs]; [discriminate Hck|]. cbn [map] in Hck. injection Hck as Hk Hck.
    destruct x as [s|z]; [|discriminate Hk].
    inversion_clear Hx as [|? ? Hs Hx']. cbn [rbf_xok] in Hs.
    destruct (IH xs Hok Hck Hx') as (qs & args & Hp & Hr & Ht & Hpp).
    exists (PRel Ps :: qs), (APtr s :: args). rewrite Ep, Hp, Ef, (rbf_cut s Hs).
    split; [reflexivity|]. split; [constructor; [exact eq_refl|exact Hr]|]. split; [|exact Hpp].
    cbn [seg_text seg_step]. rewrite Ht. reflexivity.
  + (* %d *)
    destruct (rbf_eq_D (rbf_render ts)) as (Ep & Ec & Ef). rewrite Ec in Hck.
    destruct xs as [|x xs]; [discriminate Hck|]. cbn [map] in Hck. injection Hck as Hk Hck.
    destruct x as [s|z]; [discriminate Hk|].
    inversion_clear Hx as [|? ? Hz Hx']. cbn [rbf_xok] in Hz.
    destruct (IH xs Hok Hck Hx') as (qs & args & Hp & Hr & Ht & Hpp).
    exists (PRel Pd :: qs), (AInt z :: args). rewrite Ep, Hp, Ef, <- (rbf_dec z Hz).
    split; [reflexivity|]. split; [constructor; [exact eq_refl|exact Hr]|]. split; [|exact Hpp].
    cbn [seg_text seg_step]. rewrite Ht. reflexivity.
  + (* %zu *)
    destruct (rbf_eq_ZU (rbf_render ts)) as (Ep & Ec & Ef). rewrite Ec in Hck.
    destruct xs as [|x xs]; [discriminate Hck|]. cbn [map] in Hck. injection Hck as Hk Hck.
    destruct x as [s|z]; [discriminate Hk|].
    inversion_clear Hx as [|? ? Hz Hx']. cbn [rbf_xok] in Hz.
    destruct (IH xs Hok Hck Hx') as (qs & args & Hp & Hr & Ht & Hpp).
    exists (Pzu :: qs), (AU64 z :: args). rewrite Ep, Hp, Ef, <- (rbf_udec z (proj1 Hz)).
    split; [reflexivity|]. split; [constructor; [exact eq_refl|exact Hr]|]. split; [|exact Hpp].
    cbn [seg_text seg_step]. rewrite Ht. reflexivity.
  + (* %.24s *)
    destruct (rbf_eq_24S (rbf_render ts)) as (Ep & Ec & Ef). rewrite Ec in Hck.
    destruct xs as [|x xs]; [discriminate Hck|]. cbn [map] in Hck. injection Hck as Hk Hck.
    destruct x as [s|z]; [|discriminate Hk].
    inversion_clear Hx as [|? ? Hs Hx']. cbn [rbf_xok] in Hs.
    destruct (IH xs Hok Hck Hx') as (qs & args & Hp & Hr & Ht & Hpp).
    exists (P24s :: qs), (APtr s :: args). rewrite Ep, Hp, Ef, (rbf_cut s Hs).
    split; [reflexivity|]. split; [constructor; [exact eq_refl|exact Hr]|]. split; [|exact Hpp].
    cbn [seg_text seg_step]. rewrite Ht. reflexivity.
Qed.

(* ======== the reader facts ======== *)
(* the read span of a text is str_end's: both are |s| + 8 - (w + |s|) mod 8 *)
Lemma rbf_span : forall w s, str_end w s - w = seg_spec.cstr_span w s.
Proof.
intros w s. unfold str_end, seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (w + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
pose proof (Z.div_mod (w + Z.of_nat (length s)) 8 ltac:(lia)).
pose proof (Z.div_mod (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)).
lia.
Qed.

Lemma rbf_cs_bnd : forall w s,
  Z.of_nat (length s) + 1 <= seg_spec.cstr_span w s <= Z.of_nat (length s) + 8.
Proof.
intros w s. unfold seg_spec.cstr_span.
pose proof (Z.mod_pos_bound (- (w + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia.
Qed.

Lemma rbf_bytes : forall (rd : reader) p s, sa_zs rd p (s ++ [0]) ->
  forall i, 0 <= i <= Z.of_nat (length s) -> rd (p + i) = Some (nth (Z.to_nat i) (s ++ [0]) 0).
Proof.
intros rd p s H i Hi. specialize (H (Z.to_nat i)). rewrite Z2Nat.id in H by lia.
apply H. rewrite length_app. cbn [length]. lia.
Qed.

(* a string argument: pf_arg_asan's facts and the two slack facts *)
Lemma rbf_ptr : forall rd rs w s, ffr_arg rd rs w (SegModel.AS s) ->
  pf_arg_asan rd rs w (APtr s) /\ amem_range w (str_end w s - w) /\ amem_range w (Z.of_nat (length s) + 8).
Proof.
intros rd rs w s (Hw & ((Hz & _) & Htl) & Hc & Hlen & (_ & _ & Ham1 & Hra & Hhv) & Ham & Hdis).
assert (Hl : Z.of_nat (length s) <= 65535) by (apply Nat2Z.inj_le in Hlen; exact Hlen). clear Hlen.
pose proof (rbf_span w s) as Hsp. pose proof (rbf_cs_bnd w s) as Hcs.
unfold sa_tail in Htl.
split; [|split; [|exact Ham]].
- unfold pf_arg_asan. split; [exact Hc|]. split; [exact Hw|]. split; [lia|].
  split; [exact (rbf_bytes rd w s Hz)|].
  split; [intros x Hx; apply Htl; unfold str_end in Hx; exact Hx|].
  split; [rewrite Hsp; exact Hdis|].
  split; [exact Ham1|]. split; [exact Hra|]. apply Hhv; lia.
- rewrite Hsp. unfold amem_range in *. lia.
Qed.

Lemma rbf_xs : forall rd rs ws xs, ffr_args rd rs ws xs -> Forall rbf_xok xs.
Proof.
intros rd rs ws xs. revert ws. induction xs as [|x xs IH]; intros ws H; [constructor|].
destruct ws as [|w ws]; [destruct H|]. destruct H as [Hx H]. constructor; [|exact (IH ws H)].
destruct x as [s|z].
- destruct Hx as (_ & _ & Hc & _). exact Hc.
- destruct Hx as (Hz & _). exact Hz.
Qed.

Lemma rbf_args : forall rd rs xs args, Forall2 rbf_rel xs args -> forall ws, ffr_args rd rs ws xs ->
  pf_args_asan rd rs ws args /\ cmd_args_slack ws args /\ cmd_args_amem ws args.
Proof.
intros rd rs xs args H. induction H as [|x a xs args Hxa Hr IH]; intros ws Hw.
- destruct ws; (split; [exact I|split; exact I]).
- destruct ws as [|w ws]; [destruct Hw|]. destruct Hw as [Hx Hw].
  destruct (IH ws Hw) as (Ha & Hs & Hm).
  destruct x as [s|z], a as [v|u|s']; cbn [rbf_rel] in Hxa; try contradiction.
  + subst s'. destruct (rbf_ptr rd rs w s Hx) as (Hp & Hsl & Ham).
    cbn [pf_args_asan cmd_args_slack cmd_args_amem]. tauto.
  + subst v. destruct Hx as [Hz Hwz]. subst w.
    cbn [pf_args_asan cmd_args_slack cmd_args_amem].
    split; [split; [|exact Ha]|split; [exact Hs|exact Hm]].
    unfold pf_arg_asan. split; [lia|reflexivity].
  + subst u. destruct Hx as [Hz Hwz]. subst w.
    cbn [pf_args_asan cmd_args_slack cmd_args_amem].
    split; [split; [|exact Ha]|split; [exact Hs|exact Hm]].
    unfold pf_arg_asan. reflexivity.
Qed.

(* the format: fmt_at from ffr_fmt *)
Lemma rbf_fmt_at : forall segs B gotw rd rs f fmt, ffr_fmt segs B gotw rd rs f fmt -> fmt_at rd rs f fmt.
Proof.
intros segs B gotw rd rs f fmt (Hlo & _ & ((Hz & _) & _) & (_ & _ & Ham1 & Hra & Hhv) & _ & _ & Hdis).
pose proof (rbf_cs_bnd f fmt) as Hcs.
unfold fmt_at. split; [lia|]. split; [exact (rbf_bytes rd f fmt Hz)|].
split.
{ revert Hdis. apply Forall_impl. intros [a b]. unfold zdisjoint. cbn [fst snd]. lia. }
split; [exact Ham1|]. split; [exact Hra|]. apply Hhv; lia.
Qed.

(* ======== FFR at segconf's family ======== *)
Theorem rb_ffr : forall (segs : list Segment) (B : asyms) (gotw : Z),
  ffr_family segs B gotw (FR_seg 0x10000 gotw).
Proof.
intros segs B gotw rd rs f fmt ws xs Hin Hck Hf Hargs.
destruct (rbf_lex_ok fmt Hin) as (ts & Hts & Htok & Hne).
rewrite <- Hts in Hck.
destruct (rbf_text ts xs Htok Hck (rbf_xs rd rs ws xs Hargs)) as (qs & args & Hp & Hr & Ht & Hpp).
rewrite Hts in Hp, Ht.
destruct (rbf_args rd rs xs args Hr ws Hargs) as (Ha & Hsl & Ham).
pose proof (rbf_fmt_at segs B gotw rd rs f fmt Hf) as Hat.
destruct Hf as (Hlo & Hhi & _).
unfold FR_seg, seg_fam. exists fmt, qs, args.
split; [exact Hat|]. split; [exact Hp|].
split; [apply Forall_forall; intros q _; destruct q; exact I|].
split; [exact Ha|]. split; [exact Ht|]. split; [exact Hpp|].
split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hsl|]. split; [exact Hne|exact Ham].
Qed.
