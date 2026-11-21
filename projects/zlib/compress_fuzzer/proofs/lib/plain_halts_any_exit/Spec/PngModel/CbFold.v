(** * Spec.PngModel.CbFold — the [compress_block] LOOP emits the symbol
      sequence: CbEmit's per-step seam, folded over the whole [sym_buf].

    OWNER: q5-emitter (zlib z-repro campaign, 2026-08-19).  P1 of the Q5 plan
    (PLAN.md §4).

    TRUST BOUNDARY: pure Gallina, image-INDEPENDENT.

    WHAT THIS FILE ADDS.  [CbEmit.v] proves ONE [cb_step] emits one symbol
    ([cb_step_emits_lit] / [cb_step_emits_ref]); nothing in the tree runs
    that seam around the loop (measured: zero consumers of [cb_loop] /
    [compress_block] outside Trees.v before this file).  Here:

      1. [tok_at] / [BufToks]: the token one buffer index carries, and the
         fuel-free EXACT-EDGE relation "indices [sx..symnext) carry [toks]".
         Exact edges ([bt_nil] only at [symnext = sx]) are what a real
         [sym_buf] satisfies ([symnext] steps by 3 from 0) and they make the
         extent an EQUATION ([buftoks_extent]), which is what the fold's
         CbCont/CbDone timing and [compress_block]'s fuel bound reduce to.
         [buftoks_snoc]/[buftoks_stable] are the two facts the walk layer
         needs to maintain the relation across [tr_tally].
      2. [cb_loop_emits]: the fold.
      3. [send_code_emits_end]: the END_BLOCK emission (CbEmit's per-symbol
         lemmas stop at literal 255; the terminator is symbol 256).
      4. [compress_block_emits] and the consumable [compress_block_decodes]:
         the appended block body decodes back — via
         [EmitSym.emit_decode_resolves] — to the resolution of the buffered
         tokens against any history.

    WHY THE FINAL CONCLUSION IS [emit_decode_resolves]' EXISTENTIAL form and
    not a pinned symbol list: the downstream consumer is [dec_blk]'s arm,
    which destructs [decode_symbols] and resolves WHATEVER list came out —
    the existential is exactly consumable there.  The pinned form would need
    [resolve_lz_app_end], whose only home ([DeflateSpecSyms.v]) imports the
    Codec/Inflate cone; an emit-side file must not couple its rebuild cone
    to the inflate tree other lanes are actively editing. *)

From Stdlib Require Import ZArith List Lia Bool Arith.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Bits Chunk Huff DeflateSpec ZBitsOut Trees BwStream EmitSym CbEmit
  TokLzBridge.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Local Open Scope Z_scope.

(** ** 1. The token at a buffer index, and the buffer-to-tokens relation

    [tok_at] is [sym_toks]'s body at one index, spelled with [CbEmit]'s
    named reads so the seam lemmas apply without arithmetic unfolding. *)
Definition tok_at (sym : zarr) (sx : Z) : Tok :=
  if Z.eqb (cb_dist sym sx) 0
  then TLit (cb_lc sym sx)
  else TMatch (cb_lc sym sx + 3) (cb_dist sym sx).

Inductive BufToks (sym : zarr) : Z -> Z -> list Tok -> Prop :=
| bt_nil : forall sx, BufToks sym sx sx []
| bt_cons : forall sx symnext toks,
    BufToks sym (sx + 3) symnext toks ->
    BufToks sym sx symnext (tok_at sym sx :: toks).

Lemma buftoks_extent : forall sym sx symnext toks,
  BufToks sym sx symnext toks ->
  symnext = sx + 3 * Z.of_nat (length toks).
Proof.
  intros sym sx symnext toks H; induction H; cbn [length]; lia.
Qed.

Lemma buftoks_cons_inv : forall sym sx symnext t toks,
  BufToks sym sx symnext (t :: toks) ->
  t = tok_at sym sx /\ BufToks sym (sx + 3) symnext toks.
Proof.
  intros sym sx symnext t toks H.
  inversion H; subst. split; reflexivity + assumption.
Qed.

(** Tie to Trees.v's fuelled reading, so [sym_tokens] facts interoperate.
    The exactness premise ([symnext] a 3-multiple past [sx]) is the shape
    every real buffer has. *)
Lemma sym_toks_buftoks : forall k f sym sx symnext,
  (k <= f)%nat ->
  symnext = sx + 3 * Z.of_nat k ->
  BufToks sym sx symnext (sym_toks f sym sx symnext).
Proof.
  induction k as [|k IH]; intros f sym sx symnext Hkf Hext.
  - assert (E : symnext = sx) by lia. rewrite E.
    destruct f as [|f]; cbn [sym_toks].
    + constructor.
    + replace (Z.leb sx sx) with true by (symmetry; apply Z.leb_le; lia).
      constructor.
  - destruct f as [|f]; [lia|].
    cbn [sym_toks].
    replace (Z.leb symnext sx) with false
      by (symmetry; apply Z.leb_gt; lia).
    cbv beta iota zeta.
    match goal with
    | |- BufToks _ _ _ (?tm :: _) =>
        replace tm with (tok_at sym sx) by reflexivity
    end.
    apply bt_cons.
    apply IH; lia.
Qed.

Lemma sym_tokens_buftoks : forall s k,
  ts_symnext s = 3 * Z.of_nat k ->
  BufToks (ts_symbuf s) 0 (ts_symnext s) (sym_tokens s).
Proof.
  intros s k Hk. unfold sym_tokens.
  apply (sym_toks_buftoks k); lia.
Qed.

(** The two facts the WALK needs to maintain [BufToks] across [tr_tally]:
    the relation reads only indices in [sx, symnext), and appending one
    symbol at the edge appends its token. *)
Lemma buftoks_stable : forall sym sym' sx symnext toks,
  BufToks sym sx symnext toks ->
  (forall i, sx <= i < symnext -> sym' i = sym i) ->
  BufToks sym' sx symnext toks.
Proof.
  intros sym sym' sx symnext toks H;
    induction H as [sx|sx symnext toks H IH]; intros Hagree.
  - constructor.
  - pose proof (buftoks_extent _ _ _ _ H) as Hext.
    assert (Htok : tok_at sym' sx = tok_at sym sx).
    { unfold tok_at, cb_dist, cb_lc. rewrite !Hagree by lia. reflexivity. }
    rewrite <- Htok.
    apply bt_cons.
    apply IH. intros i Hi. apply Hagree. lia.
Qed.

Lemma buftoks_snoc : forall sym sx symnext toks,
  BufToks sym sx symnext toks ->
  BufToks sym sx (symnext + 3) (toks ++ [tok_at sym symnext]).
Proof.
  intros sym sx symnext toks H;
    induction H as [sx|sx symnext toks H IH]; cbn [app].
  - apply bt_cons. constructor.
  - apply bt_cons. exact IH.
Qed.

(** ** 2. [cb_step] / [cb_loop] surface facts *)

Lemma cb_step_sx : forall sym symnext lt dt st,
  c_sx (cb_out (cb_step sym symnext lt dt st)) = c_sx st + 3.
Proof.
  intros sym symnext lt dt st. unfold cb_step, cb_out. cbv zeta.
  destruct (Z.ltb (c_sx st + 3) symnext); reflexivity.
Qed.

Lemma cb_step_split : forall sym symnext lt dt st,
  cb_step sym symnext lt dt st
  = if Z.ltb (c_sx st + 3) symnext
    then CbCont (cb_out (cb_step sym symnext lt dt st))
    else CbDone (cb_out (cb_step sym symnext lt dt st)).
Proof.
  intros sym symnext lt dt st. unfold cb_step, cb_out. cbv zeta.
  destruct (Z.ltb (c_sx st + 3) symnext); reflexivity.
Qed.

Lemma cb_loop_one : forall sym symnext lt dt st0,
  symnext <= c_sx st0 + 3 ->
  cb_loop 1 sym symnext lt dt st0
  = Some (cb_out (cb_step sym symnext lt dt st0)).
Proof.
  intros sym symnext lt dt st0 Hle.
  cbn [cb_loop].
  pose proof (cb_step_split sym symnext lt dt st0) as Hsp.
  replace (Z.ltb (c_sx st0 + 3) symnext) with false in Hsp
    by (symmetry; apply Z.ltb_ge; lia).
  rewrite Hsp. reflexivity.
Qed.

Lemma cb_loop_step_cont : forall f sym symnext lt dt st0,
  c_sx st0 + 3 < symnext ->
  cb_loop (S f) sym symnext lt dt st0
  = cb_loop f sym symnext lt dt (cb_out (cb_step sym symnext lt dt st0)).
Proof.
  intros f sym symnext lt dt st0 Hlt.
  cbn [cb_loop].
  pose proof (cb_step_split sym symnext lt dt st0) as Hsp.
  replace (Z.ltb (c_sx st0 + 3) symnext) with true in Hsp
    by (symmetry; apply Z.ltb_lt; lia).
  rewrite Hsp. reflexivity.
Qed.

Lemma cb_loop_fuel_mono : forall f g sym symnext lt dt st st',
  (f <= g)%nat ->
  cb_loop f sym symnext lt dt st = Some st' ->
  cb_loop g sym symnext lt dt st = Some st'.
Proof.
  induction f as [|f IH]; intros g sym symnext lt dt st st' Hle H;
    [discriminate H|].
  destruct g as [|g]; [lia|].
  cbn [cb_loop] in H |- *.
  destruct (cb_step sym symnext lt dt st) as [st1|st1].
  - apply IH; [lia | exact H].
  - exact H.
Qed.

(** ** 3. Per-token side conditions — [cb_step_emits_*]'s premises, bundled
    on the TOKEN so the walk and the build_tree lane can supply them without
    seeing the buffer.  [len] is the UNbiased match length (token form). *)
Definition tok_ok (ll dl : list nat) (nl nd : nat) (t : Tok) : Prop :=
  match t with
  | TLit b =>
      0 <= b < 256
      /\ (exists cw, code_for ll 15%nat (Z.to_nat b) = Some cw)
  | TMatch len dist =>
      0 <= len - 3 < 256
      /\ 1 <= dist <= 32768
      /\ DcodeRange (dist - 1)
      /\ (Z.to_nat ((length_code (len - 3) + LITERALS + 1)%Z) < nl)%nat
      /\ (Z.to_nat ((d_code (dist - 1))%Z) < nd)%nat
      /\ (exists cw,
            code_for ll 15%nat
              (Z.to_nat (length_code (len - 3) + LITERALS + 1)) = Some cw)
      /\ (exists dw,
            code_for dl 15%nat (Z.to_nat (d_code (dist - 1))) = Some dw)
  end.

(** ** 4. One trip, in token vocabulary *)

Lemma cb_step_emits_tok : forall sym symnext lt dt ll dl nl nd st0,
  tree_codes_upto lt ll nl -> tree_codes_upto dt dl nd ->
  (256 <= nl)%nat ->
  bw_wf (c_bw st0) ->
  tok_ok ll dl nl nd (tok_at sym (c_sx st0)) ->
  exists bs,
    bw_stream (c_bw (cb_out (cb_step sym symnext lt dt st0)))
      = bw_stream (c_bw st0) ++ bs
    /\ EmitsTo ll dl (tok_to_lz (tok_at sym (c_sx st0))) bs
    /\ bw_wf (c_bw (cb_out (cb_step sym symnext lt dt st0))).
Proof.
  intros sym symnext lt dt ll dl nl nd st0 Hlt Hdt Hnl Hwf Hok.
  unfold tok_at in Hok |- *.
  destruct (Z.eqb (cb_dist sym (c_sx st0)) 0) eqn:Ed.
  - cbn [tok_ok] in Hok. destruct Hok as [Hrange Hcode].
    destruct (cb_step_emits_lit sym symnext lt dt ll dl nl st0 Hlt Hnl Hwf
                (proj1 (Z.eqb_eq _ _) Ed) Hrange Hcode)
      as [bs [Hs [He Hw]]].
    exists bs. split; [exact Hs|]. split; [|exact Hw].
    unfold cb_sym_of in He. rewrite Ed in He.
    cbn [tok_to_lz]. exact He.
  - cbn [tok_ok] in Hok.
    replace (cb_lc sym (c_sx st0) + 3 - 3) with (cb_lc sym (c_sx st0))
      in Hok by lia.
    destruct Hok as (Hlc & Hdist & HD & Hinl & Hind & Hcl & Hcd).
    destruct (cb_step_emits_ref sym symnext lt dt ll dl nl nd st0 Hlt Hdt
                Hwf (proj1 (Z.eqb_neq _ _) Ed) Hlc Hdist HD Hinl Hind
                Hcl Hcd)
      as [bs [Hs [He Hw]]].
    exists bs. split; [exact Hs|]. split; [|exact Hw].
    unfold cb_sym_of in He. rewrite Ed in He.
    cbn [tok_to_lz]. exact He.
Qed.

(** ** 5. The END_BLOCK emission — the lit seam at symbol 256 *)

Lemma send_code_emits_end : forall lt ll dl n b,
  tree_codes_upto lt ll n -> (256 < n)%nat -> bw_wf b ->
  (exists cw, code_for ll 15%nat 256%nat = Some cw) ->
  exists bend,
    bw_stream (send_code END_BLOCK lt b) = bw_stream b ++ bend
    /\ EmitsTo ll dl LzEnd bend
    /\ bw_wf (send_code END_BLOCK lt b).
Proof.
  intros lt ll dl n b Htc Hn Hwf [cw Hcw].
  destruct (Htc 256%nat cw Hn Hcw) as [Hlen [Hcode Hbits]].
  replace (Z.of_nat 256) with 256 in Hlen, Hcode, Hbits
    by (vm_compute; reflexivity).
  destruct (bw_send_bits_stream (t_code lt 256) (t_len lt 256) b Hwf
              ltac:(unfold Buf_size; lia) Hcode) as [Hs Hw].
  exists cw. split; [|split].
  - unfold send_code, END_BLOCK. rewrite Hs, Hbits. reflexivity.
  - exists 0%nat, 0%nat. cbn [emit_sym]. exact Hcw.
  - unfold send_code, END_BLOCK. exact Hw.
Qed.

(** ** 6. THE FOLD *)

Theorem cb_loop_emits : forall toks t sym symnext lt dt ll dl nl nd st0,
  tree_codes_upto lt ll nl -> tree_codes_upto dt dl nd ->
  (256 <= nl)%nat ->
  bw_wf (c_bw st0) ->
  BufToks sym (c_sx st0) symnext (t :: toks) ->
  Forall (tok_ok ll dl nl nd) (t :: toks) ->
  exists bss st',
    cb_loop (S (length toks)) sym symnext lt dt st0 = Some st'
    /\ bw_stream (c_bw st') = bw_stream (c_bw st0) ++ concat bss
    /\ Forall2 (EmitsTo ll dl) (map tok_to_lz (t :: toks)) bss
    /\ bw_wf (c_bw st').
Proof.
  induction toks as [|t2 toks IH];
    intros t sym symnext lt dt ll dl nl nd st0 Hlt Hdt Hnl Hwf Hbuf Hok;
    destruct (buftoks_cons_inv _ _ _ _ _ Hbuf) as [-> Htail];
    pose proof (buftoks_extent _ _ _ _ Htail) as Hext;
    pose proof (Forall_inv Hok) as Hok1;
    pose proof (Forall_inv_tail Hok) as Hoktail;
    destruct (cb_step_emits_tok sym symnext lt dt ll dl nl nd st0
                Hlt Hdt Hnl Hwf Hok1) as [bs [Hs [He Hw]]].
  - (* the single symbol: this trip is the CbDone one *)
    cbn [length] in Hext.
    exists [bs], (cb_out (cb_step sym symnext lt dt st0)).
    split.
    { apply cb_loop_one. lia. }
    split.
    { rewrite Hs. cbn [concat]. rewrite app_nil_r. reflexivity. }
    split; [|exact Hw].
    cbn [map]. constructor; [exact He | constructor].
  - (* interior symbol: CbCont, then the induction *)
    cbn [length] in Hext.
    assert (Hlt3 : c_sx st0 + 3 < symnext) by lia.
    destruct (IH t2 sym symnext lt dt ll dl nl nd
                (cb_out (cb_step sym symnext lt dt st0)) Hlt Hdt Hnl Hw
                ltac:(rewrite cb_step_sx; exact Htail) Hoktail)
      as [bss [st' [Hloop [Hstream [Hf2 Hw']]]]].
    exists (bs :: bss), st'.
    split.
    { rewrite (cb_loop_step_cont _ sym symnext lt dt st0 Hlt3).
      exact Hloop. }
    split.
    { rewrite Hstream, Hs, <- app_assoc. cbn [concat]. reflexivity. }
    split; [|exact Hw'].
    cbn [map]. constructor; [exact He | exact Hf2].
Qed.

(** ** 7. [compress_block] *)

Theorem compress_block_emits : forall sym symnext lt dt ll dl nl nd b toks,
  tree_codes_upto lt ll nl -> tree_codes_upto dt dl nd ->
  (256 < nl)%nat -> bw_wf b ->
  BufToks sym 0 symnext toks ->
  Forall (tok_ok ll dl nl nd) toks ->
  (exists cw, code_for ll 15%nat 256%nat = Some cw) ->
  exists bss bend,
    bw_stream (compress_block sym symnext lt dt b)
      = bw_stream b ++ concat bss ++ bend
    /\ Forall2 (EmitsTo ll dl) (map tok_to_lz toks) bss
    /\ EmitsTo ll dl LzEnd bend
    /\ bw_wf (compress_block sym symnext lt dt b).
Proof.
  intros sym symnext lt dt ll dl nl nd b toks Hlt Hdt Hnl Hwf Hbuf Hok Heob.
  pose proof (buftoks_extent _ _ _ _ Hbuf) as Hext.
  unfold compress_block. cbv zeta.
  destruct toks as [|t toks].
  - (* empty buffer: [symnext = 0], only the terminator is sent *)
    cbn [length] in Hext.
    replace (Z.eqb symnext 0) with true
      by (symmetry; apply Z.eqb_eq; lia).
    cbv beta iota.
    destruct (send_code_emits_end lt ll dl nl b Hlt Hnl Hwf Heob)
      as [bend [Hsend [He Hw]]].
    exists [], bend.
    split; [cbn [concat map app]; exact Hsend|].
    split; [constructor|].
    split; [exact He | exact Hw].
  - cbn [length] in Hext.
    replace (Z.eqb symnext 0) with false
      by (symmetry; apply Z.eqb_neq; lia).
    cbv beta iota.
    destruct (cb_loop_emits toks t sym symnext lt dt ll dl nl nd
                {| c_sx := 0; c_bw := b |} Hlt Hdt ltac:(lia) Hwf Hbuf Hok)
      as [bss [st' [Hloop [Hstream [Hf2 Hw']]]]].
    rewrite (cb_loop_fuel_mono (S (length toks)) (Z.to_nat symnext + 1)
               sym symnext lt dt _ st' ltac:(lia) Hloop).
    cbv beta iota.
    destruct (send_code_emits_end lt ll dl nl (c_bw st') Hlt Hnl Hw' Heob)
      as [bend [Hsend [He Hw2]]].
    exists bss, bend.
    split; [rewrite Hsend, Hstream, app_assoc; reflexivity|].
    split; [exact Hf2|].
    split; [exact He | exact Hw2].
Qed.

(** The consumable per-block statement: what [compress_block] appended
    decodes back to the buffered tokens' resolution against ANY history —
    the exact shape [dec_blk]'s Huffman arms consume. *)
Theorem compress_block_decodes :
  forall sym symnext lt dt ll dl nl nd b toks acc out,
  tree_codes_upto lt ll nl -> tree_codes_upto dt dl nd ->
  (256 < nl)%nat -> bw_wf b ->
  BufToks sym 0 symnext toks ->
  Forall (tok_ok ll dl nl nd) toks ->
  (exists cw, code_for ll 15%nat 256%nat = Some cw) ->
  ValidLengths ll 15%nat -> ValidLengths dl 15%nat ->
  cEnc toks ->
  resolve acc toks = Some out ->
  exists delta,
    bw_stream (compress_block sym symnext lt dt b) = bw_stream b ++ delta
    /\ bw_wf (compress_block sym symnext lt dt b)
    /\ forall suffix, exists syms,
         decode_symbols ll dl (delta ++ suffix) = Some (syms, suffix)
         /\ resolve_lz syms acc = Some out.
Proof.
  intros sym symnext lt dt ll dl nl nd b toks acc out
         Hlt Hdt Hnl Hwf Hbuf Hok Heob HVl HVd Henc Hres.
  destruct (compress_block_emits sym symnext lt dt ll dl nl nd b toks
              Hlt Hdt Hnl Hwf Hbuf Hok Heob)
    as (bss & bend & Hs & Hf2 & Hend & Hw).
  exists (concat bss ++ bend).
  split; [exact Hs|].
  split; [exact Hw|].
  intro suffix.
  destruct (emit_decode_resolves ll dl (map tok_to_lz toks) bss bend suffix
              acc out HVl HVd Hf2 (tok_to_lz_not_end toks) Hend
              (resolve_lz_of_resolve toks acc out Henc Hres))
    as (syms & rem & Hdec & Hres2 & ->).
  exists syms.
  split; [|exact Hres2].
  rewrite <- app_assoc. exact Hdec.
Qed.

(** ** 8. Value witnesses

    A concrete three-symbol buffer (two literals and an overlapping match),
    read via the [sym_toks] tie, compressed with the STATIC trees, and
    decoded back by the spec decoder — the fold, the terminator and the
    [emit_decode_*] plumbing all exercised end-to-end as a value. *)
Definition cbfold_ctl_buf : zarr :=
  zset (zset (zset (zset (zset (zset (zset (zset (zset zzero
    0 0) 1 0) 2 72) 3 0) 4 0) 5 73) 6 2) 7 0) 8 1.

Example cbfold_control_read :
  sym_toks 3%nat cbfold_ctl_buf 0 9 = [TLit 72; TLit 73; TMatch 4 2].
Proof. vm_compute. reflexivity. Qed.

Example cbfold_control_decode :
  match decode_symbols fixed_lit_lengths fixed_dist_lengths
          (bw_stream (compress_block cbfold_ctl_buf 9
                        static_ltree static_dtree bw_init)) with
  | Some (syms, rem) => resolve_lz syms [] = Some [72; 73; 72; 73; 72; 73]
                        /\ rem = []
  | None => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

Print Assumptions compress_block_decodes.
