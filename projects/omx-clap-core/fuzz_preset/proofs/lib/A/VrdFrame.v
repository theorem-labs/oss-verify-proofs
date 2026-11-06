(* fuzz_preset, slice S5b, lane IelemA: the FRAME lemmas of the reader's representation predicates
   (lib/A/PRH_Reader.v), which every segment lemma of parse_items' element loop needs and which no file of the tree
   carries yet.
   WHAT THEY SAY: a node's representation reads only the node's own 56 bytes and the bytes of the blocks its subtree
   owns (the list D), so a memory change that keeps those bytes keeps the representation; the block predicate may be
   widened at the same time (a later ledger list still has the blocks D names). The same holds for pj_itemsR /
   pj_memsR (an array's or an object's slots), for pj_fshapeR / pj_fdR (a partly built tree) and for the cursor
   pj_in_okR.
   WHY: parse_items' loop calls parse_value, parse_string and grow between two loop-head states. Each of those
   writes bytes outside the node's subtree (its own frame, a new block, the cursor), and grow MOVES the kids array;
   the loop invariant's representation of the elements read so far has to survive each of them. A journal gives
   exactly a byte-agreement fact, which is what rd_keep takes.
   FORM: every lemma takes rd_keep at the EXACT set it reads, and a caller narrows its own agreement fact with
   rd_keep_mono. (A set-valued parameter inferred from the rd_keep premise is not inferable at an `apply`.)
   No machine state, no image, no engine: this file does not import a PAImg instance, so it type-checks with
   the cb build tool as well as in the warm workspace.
   Numerals: 56 (LENGTH: the node struct, PRH_Reader.v:98), 8 / 4 / 24 (LENGTH: the fields' widths, the cursor),
   0 (DERIVED). No ADDRESS.
   The kit's CUT (lane RBase, a working branch 7cdbb61b5fa0; PRH_Reader.v 4266e709561a, PRH_PjOrder.v
   e5917626b82b): tparse_items_specX's post gained pj_ncapR (Some arm) and pj_free's order list (both arms), so the loop
   carries the members' caps and the completed slots' order list (VrdIElem.v's vrd_incaps / vrd_iforder). Their frame
   lemmas are here, in this file's form: pj_ncapR_keep (a tree's caps read only its node and its blocks' bytes) with
   the list forms vrd_ncaps_items_gen / vrd_ncaps_mems_gen, the moves vrd_ncap_move / vrd_ncaps_items_move /
   vrd_ncaps_mems_move (grow's realloc copies the members' headers), the order list's keep through PRH_PjOrder's
   pf_oitemsR_frame (vrd_agree_of_keep bridges rd_keep to its pj_agreeR) and its moves vrd_fo_node_move /
   vrd_fo_items_move (after a Theorem Labs lane's B' pis_fo_node_xfer / pis_fo_items_xfer, a working branch
   34d46afa0965 lib/B/Prog/PItems_forder.v), the u64 read's determinism vrd_rd_u64_det, and the slot-list forms
   vrd_kids_snd / vrd_kids_let. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f YG0f YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_PjOrder.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section F.
Variable segs : list Segment.

(* ---- what a frame step gives: the bytes P names read the same, and what was writable stays writable ---- *)
Definition rd_keep (m m' : word -> option byte) (P : Z -> Prop) : Prop :=
  (forall a, P a -> mbyte segs m' a = mbyte segs m a) /\
  (forall a, P a -> writable_at segs m a -> writable_at segs m' a).

(* the bytes a block list covers *)
Definition rd_blk (D : list (Z * Z)) (a : Z) : Prop := Exists (fun b => pj_holdsR b a) D.

Lemma rd_keep_mono : forall m m' (P Q : Z -> Prop),
  rd_keep m m' Q -> (forall a, P a -> Q a) -> rd_keep m m' P.
Proof.
  intros m m' P Q [H1 H2] HPQ. split; intros a Ha; [apply H1 | apply H2]; apply HPQ; exact Ha.
Qed.

Lemma rd_blk_sub : forall (D D' : list (Z * Z)) a,
  (forall b, In b D -> In b D') -> rd_blk D a -> rd_blk D' a.
Proof.
  intros D D' a Hsub H. apply Exists_exists in H as (b & Hin & Hb).
  apply Exists_exists. exists b. split; [apply Hsub; exact Hin | exact Hb].
Qed.

Lemma rd_blk_in : forall D b a, In b D -> fst b <= a < fst b + snd b -> rd_blk D a.
Proof. intros D b a Hin Ha. apply Exists_exists. exists b. split; [exact Hin | exact Ha]. Qed.

Lemma rd_blk_app_l : forall D1 D2 a, rd_blk D1 a -> rd_blk (D1 ++ D2) a.
Proof. intros D1 D2 a H. apply (rd_blk_sub D1); [intros b Hb; apply in_or_app; left; exact Hb | exact H]. Qed.

Lemma rd_blk_app_r : forall D1 D2 a, rd_blk D2 a -> rd_blk (D1 ++ D2) a.
Proof. intros D1 D2 a H. apply (rd_blk_sub D2); [intros b Hb; apply in_or_app; right; exact Hb | exact H]. Qed.

Lemma rd_blk_cons : forall b D a, rd_blk D a -> rd_blk (b :: D) a.
Proof. intros b D a H. apply (rd_blk_sub D); [intros c Hc; right; exact Hc | exact H]. Qed.

(* ---- the byte-level predicates ---- *)

Lemma val_mem_keep : forall m m' a n v,
  val_mem segs m a n v -> rd_keep m m' (fun x => a <= x < a + Z.of_nat n) -> val_mem segs m' a n v.
Proof.
  intros m m' a n v H [Hb _] k Hk. rewrite (Hb (a + Z.of_nat k)) by lia. exact (H k Hk).
Qed.

Lemma garr8_keep : forall m m' a l,
  garr8 segs m a l -> rd_keep m m' (fun x => a <= x < a + Z.of_nat (length l)) -> garr8 segs m' a l.
Proof.
  intros m m' a l H [Hb _]. apply (garr8_frame segs m m' a l H). intros x Hx. apply Hb. exact Hx.
Qed.

Lemma rd_u64_keep : forall m m' a v,
  rd_u64 segs m a v -> rd_keep m m' (fun x => a <= x < a + 8) -> rd_u64 segs m' a v.
Proof.
  intros m m' a v [Hv H] HK. split; [exact Hv|]. apply (val_mem_keep m m' a 8 v H).
  eapply rd_keep_mono; [exact HK|]. intros z Hz. cbv beta in Hz |- *. cbn in Hz. lia.
Qed.

Lemma rd_u32_keep : forall m m' a v,
  rd_u32 segs m a v -> rd_keep m m' (fun x => a <= x < a + 4) -> rd_u32 segs m' a v.
Proof.
  intros m m' a v [Hv H] HK. split; [exact Hv|]. apply (val_mem_keep m m' a 4 v H).
  eapply rd_keep_mono; [exact HK|]. intros z Hz. cbv beta in Hz |- *. cbn in Hz. lia.
Qed.

Lemma rd_rw_keep : forall m m' a n,
  rd_rw segs m a n -> rd_keep m m' (fun x => a <= x < a + n) -> rd_rw segs m' a n.
Proof.
  intros m m' a n H [_ Hw] x Hx. apply Hw; [exact Hx | exact (H x Hx)].
Qed.

Lemma pj_rwR_keep : forall m m' p,
  pj_rwR segs m p -> rd_keep m m' (fun x => p <= x < p + 56) -> pj_rwR segs m' p.
Proof.
  intros m m' p [Hal H] HK. split; [exact Hal|]. exact (rd_rw_keep m m' p 56 H HK).
Qed.

Lemma pj_hdrR_keep : forall m m' p ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap ->
  rd_keep m m' (fun x => p <= x < p + 56) ->
  pj_hdrR segs m' p ty num str kids keys n cap.
Proof.
  intros m m' p ty num str kids keys n cap (Hrw & Hty & Hnum & Hstr & Hk & Hy & Hn & Hc) HK.
  split; [exact (pj_rwR_keep m m' p Hrw HK)|].
  split; [apply (rd_u32_keep m m' p ty Hty); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  split; [apply (rd_u64_keep m m' (p + 8) num Hnum); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  split; [apply (rd_u64_keep m m' (p + 16) str Hstr); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  split; [apply (rd_u64_keep m m' (p + 24) kids Hk); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  split; [apply (rd_u64_keep m m' (p + 32) keys Hy); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  split; [apply (rd_u64_keep m m' (p + 40) n Hn); eapply rd_keep_mono; [exact HK|];
          intros z Hz; cbv beta in Hz |- *; lia|].
  apply (rd_u64_keep m m' (p + 48) cap Hc). eapply rd_keep_mono; [exact HK|].
  intros z Hz. cbv beta in Hz |- *. lia.
Qed.

Lemma pj_cbytesR_keep : forall m m' a s,
  pj_cbytesR segs m a s -> rd_keep m m' (fun x => a <= x <= a + Z.of_nat (length s)) ->
  pj_cbytesR segs m' a s.
Proof.
  intros m m' a s [Hf Hg] HK. split; [exact Hf|].
  apply (garr8_keep m m' a (s ++ [0]) Hg). eapply rd_keep_mono; [exact HK|].
  intros z Hz. cbv beta in Hz |- *. rewrite length_app in Hz. cbn [length] in Hz. lia.
Qed.

Lemma pj_cstrR_keep : forall m m' lblk lblk' a k s,
  pj_cstrR segs m lblk a k s -> (lblk a k -> lblk' a k) ->
  rd_keep m m' (fun x => a <= x < a + k) ->
  pj_cstrR segs m' lblk' a k s.
Proof.
  intros m m' lblk lblk' a k s (Hb & Hlen & Hsz & Hc) Himp HK.
  split; [exact (Himp Hb)|]. split; [exact Hlen|]. split; [exact Hsz|].
  apply (pj_cbytesR_keep m m' a s Hc). eapply rd_keep_mono; [exact HK|].
  intros z Hz. cbv beta in Hz |- *. lia.
Qed.

Lemma pj_zeroR_keep : forall m m' v,
  pj_zeroR segs m v -> rd_keep m m' (fun x => v <= x < v + 56) -> pj_zeroR segs m' v.
Proof.
  intros m m' v H HK. apply (garr8_keep m m' v (repeat 0 56) H).
  eapply rd_keep_mono; [exact HK|]. intros z Hz. cbv beta in Hz |- *.
  rewrite repeat_length in Hz. cbn in Hz. lia.
Qed.

(* ---- the cursor ---- *)

Lemma pj_in_okR_keep : forall m m' q text len p d tb,
  pj_in_okR segs m q text len p d tb ->
  rd_keep m m' (fun x => q <= x < q + 24 \/ text <= x < text + len) ->
  pj_in_okR segs m' q text len p d tb.
Proof.
  intros m m' q text len p d tb
    (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) HK.
  split; [apply (val_mem_keep m m' q 8 p H1); eapply rd_keep_mono; [exact HK|];
          intros z Hz; left; cbn in Hz; lia|].
  split; [apply (val_mem_keep m m' (q + 8) 8 (text + len) H2); eapply rd_keep_mono; [exact HK|];
          intros z Hz; left; cbn in Hz; lia|].
  split; [apply (val_mem_keep m m' (q + 16) 4 d H3); eapply rd_keep_mono; [exact HK|];
          intros z Hz; left; cbn in Hz; lia|].
  split; [apply (rd_rw_keep m m' q 24 H4); eapply rd_keep_mono; [exact HK|]; intros z Hz; left; lia|].
  split; [exact H5|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8|]. split; [exact H9|].
  split; [|split; [exact H11 | exact H12]].
  apply (garr8_keep m m' text tb H10). eapply rd_keep_mono; [exact HK|]. intros z Hz. right. lia.
Qed.

(* ---- the tree ---- *)

(* the frame property of ONE node, as a predicate of the model value, so the list cases can carry it as a Forall *)
Definition rd_nodeframe (t : jv) : Prop :=
  forall m m' lblk lblk' p D,
    pj_nodeR segs m lblk p t D ->
    (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
    rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a) ->
    pj_nodeR segs m' lblk' p t D.

Lemma pj_itemsR_keep_gen : forall l, Forall rd_nodeframe l ->
  forall m m' lblk lblk' a D,
  pj_itemsR (pj_nodeR segs m lblk) a l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_itemsR (pj_nodeR segs m' lblk') a l D.
Proof.
  intros l. induction l as [|u r IH]; intros HF m m' lblk lblk' a D Hit Himp HK.
  - cbn in Hit. cbn. exact Hit.
  - cbn in Hit. destruct Hit as (D1 & D2 & HD & Hu & Hr).
    pose proof (Forall_inv HF) as HFu. pose proof (Forall_inv_tail HF) as HFr.
    cbn. exists D1, D2. split; [exact HD|]. split.
    + apply (HFu m m' lblk lblk' a D1 Hu).
      * intros x k Hin. apply Himp. rewrite HD. apply in_or_app. left. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
        { left. cbn [length]. lia. }
        { right. rewrite HD. apply rd_blk_app_l. exact Hz. }
    + apply (IH HFr m m' lblk lblk' (a + 56) D2 Hr).
      * intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
        { left. cbn [length]. lia. }
        { right. rewrite HD. apply rd_blk_app_r. exact Hz. }
Qed.

Lemma pj_memsR_keep_gen : forall l, Forall (fun mm => rd_nodeframe (snd mm)) l ->
  forall m m' lblk lblk' a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m'
    (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ ka <= z < ka + 8 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_memsR segs m' lblk' (pj_nodeR segs m' lblk') a ka l D.
Proof.
  intros l. induction l as [|[nm u] r IH]; intros HF m m' lblk lblk' a ka D Hms Himp HK.
  - cbn in Hms. cbn. exact Hms.
  - cbn in Hms. destruct Hms as (x & k & D1 & D2 & HD & Hx & Hnm & Hu & Hr).
    pose proof (Forall_inv HF) as HFu. pose proof (Forall_inv_tail HF) as HFr. cbn [snd] in HFu.
    cbn. exists x, k, D1, D2. split; [exact HD|].
    split.
    { apply (rd_u64_keep m m' ka x Hx). eapply rd_keep_mono; [exact HK|].
      intros z Hz. right. left. cbn [length]. lia. }
    split.
    { apply (pj_cstrR_keep m m' lblk lblk' x k nm Hnm).
      - intros Hb. apply (Himp x k); [rewrite HD; left; reflexivity | exact Hb].
      - eapply rd_keep_mono; [exact HK|]. intros z Hz. right. right.
        apply (rd_blk_in D (x, k)); [rewrite HD; left; reflexivity | cbn [fst snd]; lia]. }
    split.
    { apply (HFu m m' lblk lblk' a D1 Hu).
      - intros z kk Hin. apply Himp. rewrite HD. right. apply in_or_app. left. exact Hin.
      - eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
        + left. cbn [length]. lia.
        + right. right. rewrite HD. apply rd_blk_cons. apply rd_blk_app_l. exact Hz. }
    { apply (IH HFr m m' lblk lblk' (a + 56) (ka + 8) D2 Hr).
      - intros z kk Hin. apply Himp. rewrite HD. right. apply in_or_app. right. exact Hin.
      - eapply rd_keep_mono; [exact HK|]. intros z [Hz | [Hz | Hz]].
        + left. cbn [length]. lia.
        + right. left. cbn [length]. lia.
        + right. right. rewrite HD. apply rd_blk_cons. apply rd_blk_app_r. exact Hz. }
Qed.

Lemma pj_nodeR_keep : forall t, rd_nodeframe t.
Proof.
  intros t. induction t using jv_ind'; unfold rd_nodeframe;
    intros m m' lblk lblk' p D (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest) Himp HK;
    (split; [exact HND|]); (split; [exact HAP|]);
    exists num, str, kids, keys, n, cap;
    (split; [apply (pj_hdrR_keep m m' p _ num str kids keys n cap Hhdr);
             eapply rd_keep_mono; [exact HK|]; intros z Hz; left; exact Hz |]).
  - exact Hrest.
  - exact Hrest.
  - exact Hrest.
  - (* JNum: the token's block is D = [(str, k)] *)
    destruct Hrest as (Hnum & Hk0 & Hy0 & Hn0 & Hc0 & kk & Hstr & HD).
    split; [exact Hnum|]. split; [exact Hk0|]. split; [exact Hy0|]. split; [exact Hn0|]. split; [exact Hc0|].
    exists kk. split; [|exact HD].
    apply (pj_cstrR_keep m m' lblk lblk' str kk txt Hstr).
    + intros Hb. apply (Himp str kk); [rewrite HD; left; reflexivity | exact Hb].
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. right.
      apply (rd_blk_in D (str, kk)); [rewrite HD; left; reflexivity | cbn [fst snd]; lia].
  - (* JStr *)
    destruct Hrest as (Hk0 & Hy0 & Hn0 & Hc0 & kk & Hstr & HD).
    split; [exact Hk0|]. split; [exact Hy0|]. split; [exact Hn0|]. split; [exact Hc0|].
    exists kk. split; [|exact HD].
    apply (pj_cstrR_keep m m' lblk lblk' str kk s Hstr).
    + intros Hb. apply (Himp str kk); [rewrite HD; left; reflexivity | exact Hb].
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. right.
      apply (rd_blk_in D (str, kk)); [rewrite HD; left; reflexivity | cbn [fst snd]; lia].
  - (* JArr *)
    destruct Hrest as (Hstr0 & Hy0 & Hn & Hnc & Hcap & Di & HD & Hit).
    split; [exact Hstr0|]. split; [exact Hy0|]. split; [exact Hn|]. split; [exact Hnc|].
    split.
    { destruct Hcap as [Hc | (Hc & Hb)]; [left; exact Hc|]. right. split; [exact Hc|].
      apply (Himp kids (56 * cap)); [|exact Hb].
      rewrite HD. apply in_or_app. left.
      destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity]. }
    exists Di. split; [exact HD|].
    apply (pj_itemsR_keep_gen items H m m' lblk lblk' kids Di Hit).
    + intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
      * right. destruct Hcap as [(Hc & Hk0) | (Hc & Hb)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (kids, 56 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * right. rewrite HD. apply rd_blk_app_r. exact Hz.
  - (* JObj *)
    destruct Hrest as (Hstr0 & Hn & Hnc & Hcap & Di & HD & Hms).
    split; [exact Hstr0|]. split; [exact Hn|]. split; [exact Hnc|].
    split.
    { destruct Hcap as [Hc | (Hc & Hbk & Hby)]; [left; exact Hc|]. right. split; [exact Hc|].
      split.
      - apply (Himp kids (56 * cap)); [|exact Hbk].
        rewrite HD. apply in_or_app. left.
        destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
      - apply (Himp keys (8 * cap)); [|exact Hby].
        rewrite HD. apply in_or_app. left.
        destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | right; left; reflexivity]. }
    exists Di. split; [exact HD|].
    apply (pj_memsR_keep_gen members H m m' lblk lblk' kids keys Di Hms).
    + intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z [Hz | [Hz | Hz]].
      * right. destruct Hcap as [(Hc & Hk0 & Hy0) | (Hc & Hbk & Hby)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (kids, 56 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * right. destruct Hcap as [(Hc & Hk0 & Hy0) | (Hc & Hbk & Hby)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (keys, 8 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | right; left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * right. rewrite HD. apply rd_blk_app_r. exact Hz.
Qed.

Lemma pj_itemsR_keep : forall l m m' lblk lblk' a D,
  pj_itemsR (pj_nodeR segs m lblk) a l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_itemsR (pj_nodeR segs m' lblk') a l D.
Proof.
  intros l. apply pj_itemsR_keep_gen. apply Forall_forall. intros u _. apply pj_nodeR_keep.
Qed.

Lemma pj_memsR_keep : forall l m m' lblk lblk' a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m'
    (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ ka <= z < ka + 8 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_memsR segs m' lblk' (pj_nodeR segs m' lblk') a ka l D.
Proof.
  intros l. apply pj_memsR_keep_gen. apply Forall_forall. intros mm _. apply pj_nodeR_keep.
Qed.

(* ---- the partly built tree a refusal leaves ---- *)

Lemma pj_keyR_keep : forall m m' lblk lblk' ks ka Dk,
  pj_keyR segs m lblk ks ka Dk ->
  (forall x k, In (x, k) Dk -> lblk x k -> lblk' x k) ->
  rd_keep m m' (fun x => ks = true /\ ka <= x < ka + 8) ->
  pj_keyR segs m' lblk' ks ka Dk.
Proof.
  intros m m' lblk lblk' ks ka Dk H Himp HK. unfold pj_keyR in *.
  destruct ks; [|exact H].
  destruct H as (x & Hx & Hcase). exists x.
  split; [apply (rd_u64_keep m m' ka x Hx); eapply rd_keep_mono; [exact HK|];
          intros z Hz; split; [reflexivity | lia]|].
  destruct Hcase as [Hz | (k & Hb & HD)]; [left; exact Hz|].
  right. exists k. split; [|exact HD].
  apply (Himp x k); [rewrite HD; left; reflexivity | exact Hb].
Qed.

Lemma pf_itemsR_keep : forall n m m' lblk lblk' (P Q : Z -> list (Z * Z) -> Prop) ks a ka D,
  pf_itemsR segs m lblk P ks a ka n D ->
  (forall p D1, (forall x k, In (x, k) D1 -> lblk x k -> lblk' x k) ->
     rd_keep m m' (fun z => p <= z < p + 56 \/ rd_blk D1 z) -> P p D1 -> Q p D1) ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m'
    (fun z => a <= z < a + 56 * Z.of_nat n \/ (ks = true /\ ka <= z < ka + 8 * Z.of_nat n) \/ rd_blk D z) ->
  pf_itemsR segs m' lblk' Q ks a ka n D.
Proof.
  intros n. induction n as [|n IH]; intros m m' lblk lblk' P Q ks a ka D H Hstep Himp HK.
  - cbn in H. cbn. exact H.
  - cbn in H. destruct H as (Dk & D1 & D2 & HD & Hk & Hp & Hr).
    cbn. exists Dk, D1, D2. split; [exact HD|].
    split.
    { apply (pj_keyR_keep m m' lblk lblk' ks ka Dk Hk).
      - intros x k Hin. apply Himp. rewrite HD. apply in_or_app. left. exact Hin.
      - eapply rd_keep_mono; [exact HK|]. intros z [Hks Hz]. right. left. split; [exact Hks | lia]. }
    split.
    { apply (Hstep a D1).
      - intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. apply in_or_app. left. exact Hin.
      - eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
        + left. lia.
        + right. right. rewrite HD. apply rd_blk_app_r. apply rd_blk_app_l. exact Hz.
      - exact Hp. }
    { apply (IH m m' lblk lblk' P Q ks (a + 56) (ka + 8) D2 Hr Hstep).
      - intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. apply in_or_app. right. exact Hin.
      - eapply rd_keep_mono; [exact HK|]. intros z [Hz | [[Hks Hz] | Hz]].
        + left. lia.
        + right. left. split; [exact Hks | lia].
        + right. right. rewrite HD. apply rd_blk_app_r. apply rd_blk_app_r. exact Hz. }
Qed.

(* the shape of a refused tree, with the slot predicate transferred by the caller: the caller gets the block facts
   it needs (the kids / keys arrays are in D, and Di's blocks are in D) *)
Lemma pj_fshapeR_keep : forall m m' lblk lblk' Pi Pi' p D,
  pj_fshapeR segs m lblk Pi p D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a) ->
  (forall ks kids keys n Di,
     (kids = 0 /\ n = 0) \/ (exists k, In (kids, k) D /\ 56 * n <= k) ->
     (ks = false) \/ (ks = true /\ exists k, In (keys, k) D /\ 8 * n <= k) ->
     (forall b, In b Di -> In b D) ->
     Pi ks kids keys n Di -> Pi' ks kids keys n Di) ->
  pj_fshapeR segs m' lblk' Pi' p D.
Proof.
  intros m m' lblk lblk' Pi Pi' p D
    (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di &
     Hhdr & Hs & Hk & Hy & Hperm & Hpi) Himp HK Hstep.
  assert (Hin : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
    by (intros b Hb; apply (Permutation_in _ (Permutation_sym Hperm)); exact Hb).
  split; [exact HND|]. split; [exact HAP|].
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
  split; [apply (pj_hdrR_keep m m' p ty num str kids keys n cap Hhdr);
          eapply rd_keep_mono; [exact HK|]; intros z Hz; left; exact Hz|].
  split.
  { destruct Hs as [Hs | (k & Hb & HDs)]; [left; exact Hs|].
    right. exists k. split; [|exact HDs].
    apply (Himp str k); [apply Hin; apply in_or_app; left; rewrite HDs; left; reflexivity | exact Hb]. }
  split.
  { destruct Hk as [Hk | (k & Hb & Hle & HDk)]; [left; exact Hk|].
    right. exists k. split; [|split; [exact Hle | exact HDk]].
    apply (Himp kids k);
      [apply Hin; apply in_or_app; right; apply in_or_app; left; rewrite HDk; left; reflexivity | exact Hb]. }
  split.
  { destruct Hy as [Hy | (Hks & k & Hb & Hle & HDy)]; [left; exact Hy|].
    right. split; [exact Hks|]. exists k. split; [|split; [exact Hle | exact HDy]].
    apply (Himp keys k);
      [apply Hin; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left;
       rewrite HDy; left; reflexivity | exact Hb]. }
  split; [exact Hperm|].
  apply (Hstep ks kids keys n Di).
  - destruct Hk as [(Hk0 & Hn0 & HDk) | (k & Hb & Hle & HDk)]; [left; split; assumption|].
    right. exists k. split; [|exact Hle].
    apply Hin. apply in_or_app. right. apply in_or_app. left. rewrite HDk. left. reflexivity.
  - destruct Hy as [(Hy0 & Hks & HDy) | (Hks & k & Hb & Hle & HDy)]; [left; exact Hks|].
    right. split; [exact Hks|]. exists k. split; [|exact Hle].
    apply Hin. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
    rewrite HDy. left. reflexivity.
  - intros b Hb. apply Hin. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb.
  - exact Hpi.
Qed.

Lemma pj_fdR_keep : forall d m m' lblk lblk' p D,
  pj_fdR segs m lblk d p D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a) ->
  pj_fdR segs m' lblk' d p D.
Proof.
  intros d. induction d as [|d IH]; intros m m' lblk lblk' p D H Himp HK; cbn [pj_fdR] in H |- *.
  - apply (pj_fshapeR_keep m m' lblk lblk' _ _ p D H Himp HK).
    intros ks kids keys n Di _ _ _ Hpi. exact Hpi.
  - apply (pj_fshapeR_keep m m' lblk lblk' _ _ p D H Himp HK).
    intros ks kids keys n Di Hkb Hyb Hsub Hpi.
    apply (pf_itemsR_keep (Z.to_nat n) m m' lblk lblk'
             (pj_fdR segs m lblk d) (pj_fdR segs m' lblk' d) ks kids keys Di Hpi).
    + intros q D1 Himp1 HK1 Hq. exact (IH m m' lblk lblk' q D1 Hq Himp1 HK1).
    + intros x k Hb. apply Himp. apply Hsub. exact Hb.
    + eapply rd_keep_mono; [exact HK|]. intros z [Hz | [[Hks Hz] | Hz]].
      * right. destruct Hkb as [(Hk0 & Hn0) | (k & Hb & Hle)].
        { exfalso. subst n. cbn in Hz. lia. }
        { apply (rd_blk_in D (kids, k)); [exact Hb | cbn [fst snd]; lia]. }
      * right. destruct Hyb as [Hks0 | (Hks0 & k & Hb & Hle)].
        { exfalso. rewrite Hks in Hks0. discriminate Hks0. }
        { apply (rd_blk_in D (keys, k)); [exact Hb | cbn [fst snd]; lia]. }
      * right. apply (rd_blk_sub Di D); [exact Hsub | exact Hz].
Qed.

(* the kit's name for the set every tree lemma above reads (PRH_Reader.v:203, added by the kit's walkkit after this file
   was written): a caller that has rd_keep at pj_footR hands it to the lemmas through this bridge *)
Lemma rd_foot_keep : forall m m' p D,
  rd_keep m m' (pj_footR p D) -> rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a).
Proof.
  intros m m' p D HK. eapply rd_keep_mono; [exact HK|]. intros a [Ha | Ha]; [left; exact Ha|].
  right. apply Exists_exists in Ha as (b & Hin & Hb). exists b. split; [exact Hin | exact Hb].
Qed.

Lemma rd_keep_foot : forall m m' p D,
  rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a) -> rd_keep m m' (pj_footR p D).
Proof.
  intros m m' p D HK. eapply rd_keep_mono; [exact HK|]. intros a [Ha | Ha]; [left; exact Ha|].
  right. destruct Ha as (b & Hin & Hb). apply Exists_exists. exists b. split; [exact Hin | exact Hb].
Qed.

(* ---- a COMPLETE tree is freeable to its depth (IelemD, at a Theorem Labs lane's request, 2026-10-29). A refusal inside
   parse_items' loop leaves through the exit boundary, which hands pj_free the partly built node as pj_fdR; the
   elements read so far are carried as pj_nodeR, with the depth bound vrd_imodel now holds. pj_fdR k reads the
   same header and blocks as pj_nodeR; a slot of an array has no key (ks = false), a member of an object has its
   name's block as the key (ks = true). ---- *)
Definition rd_nodefd (t : jv) : Prop :=
  forall k m lblk p D, pj_nodeR segs m lblk p t D -> (PjTree.depth t <= k)%nat -> pj_fdR segs m lblk k p D.

Lemma vrd_fd_items : forall l, Forall rd_nodefd l ->
  forall k m lblk a ka D, pj_itemsR (pj_nodeR segs m lblk) a l D ->
  Forall (fun u => (PjTree.depth u <= k)%nat) l ->
  pf_itemsR segs m lblk (pj_fdR segs m lblk k) false a ka (length l) D.
Proof.
  induction l as [|u l IH]; intros HF k m lblk a ka D Hit Hd; cbn [pj_itemsR length pf_itemsR] in *.
  - exact Hit.
  - destruct Hit as (D1 & D2 & -> & Hu & Hr).
    apply Forall_cons_iff in HF as [Hfu HFl]. apply Forall_cons_iff in Hd as [Hdu Hdl].
    exists [], D1, D2. split; [reflexivity|]. split; [reflexivity|].
    split; [exact (Hfu k m lblk a D1 Hu Hdu)|]. exact (IH HFl k m lblk (a + 56) (ka + 8) D2 Hr Hdl).
Qed.

Lemma vrd_fd_mems : forall l, Forall (fun mm => rd_nodefd (snd mm)) l ->
  forall k m lblk a ka D, pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  Forall (fun mm => (PjTree.depth (snd mm) <= k)%nat) l ->
  pf_itemsR segs m lblk (pj_fdR segs m lblk k) true a ka (length l) D.
Proof.
  induction l as [|[nm u] l IH]; intros HF k m lblk a ka D Hms Hd; cbn [pj_memsR length pf_itemsR] in *.
  - exact Hms.
  - destruct Hms as (x & kk & D1 & D2 & -> & Hx & Hc & Hu & Hr).
    apply Forall_cons_iff in HF as [Hfu HFl]. apply Forall_cons_iff in Hd as [Hdu Hdl]. cbn [snd] in Hfu, Hdu.
    exists [(x, kk)], D1, D2. split; [reflexivity|].
    split; [exists x; split; [exact Hx | right; exists kk; split; [exact (proj1 Hc) | reflexivity]]|].
    split; [exact (Hfu k m lblk a D1 Hu Hdu)|]. exact (IH HFl k m lblk (a + 56) (ka + 8) D2 Hr Hdl).
Qed.

(* a node with no slots (a literal, a number, a string) is freeable at every depth *)
Lemma vrd_fd_leaf : forall k m lblk p D ty num str,
  NoDup D -> pj_apartR D p -> pj_hdrR segs m p ty num str 0 0 0 0 ->
  (str = 0 /\ D = [] \/ exists kk, lblk str kk /\ D = [(str, kk)]) ->
  pj_fdR segs m lblk k p D.
Proof.
  intros k m lblk p D ty num str HND HAP Hhdr Hs.
  assert (G : forall Pi : bool -> Z -> Z -> Z -> list (Z * Z) -> Prop, Pi false 0 0 0 [] ->
                pj_fshapeR segs m lblk Pi p D).
  { intros Pi HPi. split; [exact HND|]. split; [exact HAP|].
    exists ty, num, str, 0, 0, 0, 0, false, D, [], [], [].
    split; [exact Hhdr|].
    split; [destruct Hs as [(-> & ->) | (kk & Hk & ->)];
            [left; split; reflexivity | right; exists kk; split; [exact Hk | reflexivity]]|].
    split; [left; split; [reflexivity | split; reflexivity]|].
    split; [left; split; [reflexivity | split; reflexivity]|].
    split; [cbn [app]; rewrite app_nil_r; apply Permutation_refl | exact HPi]. }
  destruct k as [|k]; cbn [pj_fdR]; apply G; [split; reflexivity | reflexivity].
Qed.

Lemma vrd_nodefd_all : forall t, rd_nodefd t.
Proof.
  intros t. induction t using jv_ind'; unfold rd_nodefd;
    intros k m lblk p D (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest) Hdep.
  - destruct Hrest as (-> & -> & -> & -> & -> & ->).
    apply (vrd_fd_leaf k m lblk p [] _ num 0 HND HAP Hhdr). left. split; reflexivity.
  - destruct Hrest as (-> & -> & -> & -> & -> & ->).
    apply (vrd_fd_leaf k m lblk p [] _ num 0 HND HAP Hhdr). left. split; reflexivity.
  - destruct Hrest as (-> & -> & -> & -> & -> & ->).
    apply (vrd_fd_leaf k m lblk p [] _ num 0 HND HAP Hhdr). left. split; reflexivity.
  - destruct Hrest as (_ & -> & -> & -> & -> & kk & Hstr & HD).
    apply (vrd_fd_leaf k m lblk p D _ num str HND HAP Hhdr). right. exists kk. exact (conj (proj1 Hstr) HD).
  - destruct Hrest as (-> & -> & -> & -> & kk & Hstr & HD).
    apply (vrd_fd_leaf k m lblk p D _ num str HND HAP Hhdr). right. exists kk. exact (conj (proj1 Hstr) HD).
  - (* JArr: the kids array, no keys *)
    destruct Hrest as (Hs0 & Hy0 & Hn & Hnc & Hcap & Di & HD & Hit).
    destruct k as [|k]; [cbn [PjTree.depth] in Hdep; lia|].
    assert (Hd : Forall (fun u => (PjTree.depth u <= k)%nat) items).
    { apply Forall_forall. intros u Hu. pose proof (depth_item items u Hu). lia. }
    cbn [pj_fdR]. split; [exact HND|]. split; [exact HAP|].
    exists (tag (JArr items)), num, str, kids, keys, n, cap, false, [],
      (if cap =? 0 then [] else [(kids, 56 * cap)]), [], Di.
    split; [exact Hhdr|]. split; [left; split; [exact Hs0 | reflexivity]|].
    split.
    { destruct Hcap as [(Hc & Hk) | (Hc & Hb)].
      - left. split; [exact Hk|]. split; [lia|]. rewrite Hc. reflexivity.
      - right. exists (56 * cap). split; [exact Hb|]. split; [lia|].
        destruct (Z.eqb_spec cap 0); [lia | reflexivity]. }
    split; [left; split; [exact Hy0 | split; reflexivity]|].
    split; [rewrite HD; cbn [app]; apply Permutation_refl|].
    rewrite Hn, Nat2Z.id. exact (vrd_fd_items items H k m lblk kids keys Di Hit Hd).
  - (* JObj: the kids array and the keys array, each member's name block as its key *)
    destruct Hrest as (Hs0 & Hn & Hnc & Hcap & Di & HD & Hms).
    destruct k as [|k]; [cbn [PjTree.depth] in Hdep; lia|].
    assert (Hd : Forall (fun mm => (PjTree.depth (snd mm) <= k)%nat) members).
    { apply Forall_forall. intros [nm u] Hu. cbn [snd]. pose proof (depth_member members nm u Hu). lia. }
    cbn [pj_fdR]. split; [exact HND|]. split; [exact HAP|].
    destruct Hcap as [(Hc & Hk & Hy) | (Hc & Hbk & Hby)].
    + assert (Hn0 : n = 0) by lia.
      assert (Hm0 : members = []) by (destruct members; [reflexivity | cbn [length] in Hn; lia]).
      subst members. cbn [pj_memsR] in Hms. subst Di.
      exists (tag (JObj [])), num, str, kids, keys, n, cap, false, [], [], [], [].
      split; [exact Hhdr|]. split; [left; split; [exact Hs0 | reflexivity]|].
      split; [left; split; [exact Hk | split; [exact Hn0 | reflexivity]]|].
      split; [left; split; [exact Hy | split; reflexivity]|].
      split; [rewrite HD, Hc; cbn [app Z.eqb]; apply Permutation_refl|].
      rewrite Hn0. reflexivity.
    + exists (tag (JObj members)), num, str, kids, keys, n, cap, true, [], [(kids, 56 * cap)],
        [(keys, 8 * cap)], Di.
      split; [exact Hhdr|]. split; [left; split; [exact Hs0 | reflexivity]|].
      split; [right; exists (56 * cap); split; [exact Hbk | split; [lia | reflexivity]]|].
      split; [right; split; [reflexivity|]; exists (8 * cap); split; [exact Hby | split; [lia | reflexivity]]|].
      split; [rewrite HD; destruct (Z.eqb_spec cap 0); [lia|]; cbn [app]; apply Permutation_refl|].
      rewrite Hn, Nat2Z.id. exact (vrd_fd_mems members H k m lblk kids keys Di Hms Hd).
Qed.

Lemma vrd_node_fd : forall t k m lblk p D,
  pj_nodeR segs m lblk p t D -> (PjTree.depth t <= k)%nat -> pj_fdR segs m lblk k p D.
Proof. intros t. exact (vrd_nodefd_all t). Qed.

(* ---- RELOCATION: grow MOVES the kids (and keys) array, and with it the headers of the elements read so far. A
   header whose 56 bytes were copied to p' (byte for byte, writable there) is the same header at p'; the subtree
   below it is in D and moves nowhere (IelemD, 2026-10-29, for the grow step's success arms). ---- *)
Lemma vrd_hdr_move : forall m m' p p' ty num str kids keys n cap,
  pj_hdrR segs m p ty num str kids keys n cap ->
  (forall x, 0 <= x < 56 -> mbyte segs m' (p' + x) = mbyte segs m (p + x)) ->
  (forall x, 0 <= x < 56 -> writable_at segs m' (p' + x)) -> p' mod 8 = 0 ->
  pj_hdrR segs m' p' ty num str kids keys n cap.
Proof.
  intros m m' p p' ty num str kids keys n cap (_ & (Tr & Tv) & (Nr & Nv) & (Sr & Sv) & (Kr & Kv) & (Yr & Yv)
    & (Mr & Mv) & (Cr & Cv)) Hb Hw Hal.
  assert (F : forall off w v, 0 <= off -> off + Z.of_nat w <= 56 -> val_mem segs m (p + off) w v ->
                val_mem segs m' (p' + off) w v).
  { intros off w v H1 H2 Hv k Hk. replace (p' + off + Z.of_nat k) with (p' + (off + Z.of_nat k)) by lia.
    rewrite Hb by lia. replace (p + (off + Z.of_nat k)) with (p + off + Z.of_nat k) by lia. exact (Hv k Hk). }
  split; [split; [exact Hal | intros x Hx; replace x with (p' + (x - p')) by lia; apply Hw; lia]|].
  split; [split; [exact Tr|]; rewrite <- (Z.add_0_r p'); apply (F 0 4%nat ty); [lia | cbn; lia | rewrite Z.add_0_r; exact Tv]|].
  split; [split; [exact Nr | apply (F 8 8%nat num); [lia | cbn; lia | exact Nv]]|].
  split; [split; [exact Sr | apply (F 16 8%nat str); [lia | cbn; lia | exact Sv]]|].
  split; [split; [exact Kr | apply (F 24 8%nat kids); [lia | cbn; lia | exact Kv]]|].
  split; [split; [exact Yr | apply (F 32 8%nat keys); [lia | cbn; lia | exact Yv]]|].
  split; [split; [exact Mr | apply (F 40 8%nat n); [lia | cbn; lia | exact Mv]]|].
  split; [exact Cr | apply (F 48 8%nat cap); [lia | cbn; lia | exact Cv]].
Qed.

Lemma vrd_node_move : forall t m m' lblk lblk' p p' D,
  pj_nodeR segs m lblk p t D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 -> mbyte segs m' (p' + x) = mbyte segs m (p + x)) ->
  (forall x, 0 <= x < 56 -> writable_at segs m' (p' + x)) -> p' mod 8 = 0 ->
  pj_apartR D p' ->
  pj_nodeR segs m' lblk' p' t D.
Proof.
  intros t m m' lblk lblk' p p' D HN Himp HK Hb Hw Hal HAP.
  destruct t as [ | | | txt bits | s | items | members ];
    destruct HN as (HND & _ & num & str & kids & keys & n & cap & Hhdr & Hrest);
    (split; [exact HND|]); (split; [exact HAP|]); exists num, str, kids, keys, n, cap;
    (split; [exact (vrd_hdr_move m m' p p' _ num str kids keys n cap Hhdr Hb Hw Hal)|]).
  - exact Hrest.
  - exact Hrest.
  - exact Hrest.
  - destruct Hrest as (Hnum & Hk0 & Hy0 & Hn0 & Hc0 & kk & Hstr & HD).
    split; [exact Hnum|]. split; [exact Hk0|]. split; [exact Hy0|]. split; [exact Hn0|]. split; [exact Hc0|].
    exists kk. split; [|exact HD].
    apply (pj_cstrR_keep m m' lblk lblk' str kk txt Hstr).
    + intros Hbk. apply (Himp str kk); [rewrite HD; left; reflexivity | exact Hbk].
    + eapply rd_keep_mono; [exact HK|]. intros z Hz.
      apply (rd_blk_in D (str, kk)); [rewrite HD; left; reflexivity | cbn [fst snd]; lia].
  - destruct Hrest as (Hk0 & Hy0 & Hn0 & Hc0 & kk & Hstr & HD).
    split; [exact Hk0|]. split; [exact Hy0|]. split; [exact Hn0|]. split; [exact Hc0|].
    exists kk. split; [|exact HD].
    apply (pj_cstrR_keep m m' lblk lblk' str kk s Hstr).
    + intros Hbk. apply (Himp str kk); [rewrite HD; left; reflexivity | exact Hbk].
    + eapply rd_keep_mono; [exact HK|]. intros z Hz.
      apply (rd_blk_in D (str, kk)); [rewrite HD; left; reflexivity | cbn [fst snd]; lia].
  - destruct Hrest as (Hstr0 & Hy0 & Hn & Hnc & Hcap & Di & HD & Hit).
    split; [exact Hstr0|]. split; [exact Hy0|]. split; [exact Hn|]. split; [exact Hnc|].
    split.
    { destruct Hcap as [Hc | (Hc & Hbk)]; [left; exact Hc|]. right. split; [exact Hc|].
      apply (Himp kids (56 * cap)); [|exact Hbk].
      rewrite HD. apply in_or_app. left.
      destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity]. }
    exists Di. split; [exact HD|].
    apply (pj_itemsR_keep items m m' lblk lblk' kids Di Hit).
    + intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
      * destruct Hcap as [(Hc & Hk0) | (Hc & Hbk)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (kids, 56 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * rewrite HD. apply rd_blk_app_r. exact Hz.
  - destruct Hrest as (Hstr0 & Hn & Hnc & Hcap & Di & HD & Hms).
    split; [exact Hstr0|]. split; [exact Hn|]. split; [exact Hnc|].
    split.
    { destruct Hcap as [Hc | (Hc & Hbk & Hby)]; [left; exact Hc|]. right. split; [exact Hc|].
      split.
      - apply (Himp kids (56 * cap)); [|exact Hbk].
        rewrite HD. apply in_or_app. left.
        destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
      - apply (Himp keys (8 * cap)); [|exact Hby].
        rewrite HD. apply in_or_app. left.
        destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | right; left; reflexivity]. }
    exists Di. split; [exact HD|].
    apply (pj_memsR_keep members m m' lblk lblk' kids keys Di Hms).
    + intros x k Hin. apply Himp. rewrite HD. apply in_or_app. right. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z [Hz | [Hz | Hz]].
      * destruct Hcap as [(Hc & Hk0 & Hy0) | (Hc & Hbk & Hby)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (kids, 56 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * destruct Hcap as [(Hc & Hk0 & Hy0) | (Hc & Hbk & Hby)].
        { exfalso. rewrite Hn in Hnc. lia. }
        { apply (rd_blk_in D (keys, 8 * cap)).
          - rewrite HD. apply in_or_app. left.
            destruct (Z.eqb_spec cap 0) as [Hc0 | Hc0]; [lia | right; left; reflexivity].
          - cbn [fst snd]. rewrite Hn in Hnc. lia. }
      * rewrite HD. apply rd_blk_app_r. exact Hz.
Qed.

Lemma vrd_items_move : forall l m m' lblk lblk' a a' D,
  pj_itemsR (pj_nodeR segs m lblk) a l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> mbyte segs m' (a' + x) = mbyte segs m (a + x)) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> writable_at segs m' (a' + x)) -> a' mod 8 = 0 ->
  (forall b x, In b D -> pj_holdsR b x -> ~ (a' <= x < a' + 56 * Z.of_nat (length l))) ->
  pj_itemsR (pj_nodeR segs m' lblk') a' l D.
Proof.
  induction l as [|u l IH]; intros m m' lblk lblk' a a' D Hit Himp HK Hb Hw Hal HAP; cbn [pj_itemsR length] in *.
  - exact Hit.
  - destruct Hit as (D1 & D2 & -> & Hu & Hr). exists D1, D2. split; [reflexivity|]. split.
    + apply (vrd_node_move u m m' lblk lblk' a a' D1 Hu).
      * intros x k Hin. apply Himp. apply in_or_app. left. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_l. exact Hz.
      * intros x Hx. apply Hb. lia.
      * intros x Hx. apply Hw. lia.
      * exact Hal.
      * intros b x Hin Hx Hc. apply (HAP b x); [apply in_or_app; left; exact Hin | exact Hx | lia].
    + apply (IH m m' lblk lblk' (a + 56) (a' + 56) D2 Hr).
      * intros x k Hin. apply Himp. apply in_or_app. right. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_r. exact Hz.
      * intros x Hx. replace (a' + 56 + x) with (a' + (56 + x)) by lia.
        replace (a + 56 + x) with (a + (56 + x)) by lia. apply Hb. lia.
      * intros x Hx. replace (a' + 56 + x) with (a' + (56 + x)) by lia. apply Hw. lia.
      * replace (a' + 56) with (a' + 7 * 8) by lia. rewrite Z_mod_plus_full. exact Hal.
      * intros b x Hin Hx Hc. apply (HAP b x); [apply in_or_app; right; exact Hin | exact Hx | lia].
Qed.

Lemma vrd_mems_move : forall l m m' lblk lblk' a a' ka ka' D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  (forall x k, In (x, k) D -> lblk x k -> lblk' x k) ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> mbyte segs m' (a' + x) = mbyte segs m (a + x)) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> writable_at segs m' (a' + x)) -> a' mod 8 = 0 ->
  (forall x, 0 <= x < 8 * Z.of_nat (length l) -> mbyte segs m' (ka' + x) = mbyte segs m (ka + x)) ->
  (forall b x, In b D -> pj_holdsR b x -> ~ (a' <= x < a' + 56 * Z.of_nat (length l))) ->
  pj_memsR segs m' lblk' (pj_nodeR segs m' lblk') a' ka' l D.
Proof.
  induction l as [|[nm u] l IH]; intros m m' lblk lblk' a a' ka ka' D Hms Himp HK Hb Hw Hal Hkb HAP;
    cbn [pj_memsR length] in *.
  - exact Hms.
  - destruct Hms as (x & kk & D1 & D2 & -> & (Hxr & Hxv) & Hc & Hu & Hr).
    exists x, kk, D1, D2. split; [reflexivity|].
    split; [split; [exact Hxr|]; intros k Hk; rewrite Hkb by lia; exact (Hxv k Hk)|].
    split.
    { apply (pj_cstrR_keep m m' lblk lblk' x kk nm Hc).
      - intros Hbk. exact (Himp x kk (or_introl eq_refl) Hbk).
      - eapply rd_keep_mono; [exact HK|]. intros z Hz.
        apply (rd_blk_in _ (x, kk)); [left; reflexivity | cbn [fst snd]; lia]. }
    split.
    + apply (vrd_node_move u m m' lblk lblk' a a' D1 Hu).
      * intros x' k Hin. apply Himp. right. apply in_or_app. left. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_cons. apply rd_blk_app_l. exact Hz.
      * intros x' Hx. apply Hb. lia.
      * intros x' Hx. apply Hw. lia.
      * exact Hal.
      * intros b x' Hin Hx Hcc. apply (HAP b x'); [right; apply in_or_app; left; exact Hin | exact Hx | lia].
    + apply (IH m m' lblk lblk' (a + 56) (a' + 56) (ka + 8) (ka' + 8) D2 Hr).
      * intros x' k Hin. apply Himp. right. apply in_or_app. right. exact Hin.
      * eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_cons. apply rd_blk_app_r. exact Hz.
      * intros x' Hx. replace (a' + 56 + x') with (a' + (56 + x')) by lia.
        replace (a + 56 + x') with (a + (56 + x')) by lia. apply Hb. lia.
      * intros x' Hx. replace (a' + 56 + x') with (a' + (56 + x')) by lia. apply Hw. lia.
      * replace (a' + 56) with (a' + 7 * 8) by lia. rewrite Z_mod_plus_full. exact Hal.
      * intros x' Hx. replace (ka' + 8 + x') with (ka' + (8 + x')) by lia.
        replace (ka + 8 + x') with (ka + (8 + x')) by lia. apply Hkb. lia.
      * intros b x' Hin Hx Hcc. apply (HAP b x'); [right; apply in_or_app; right; exact Hin | exact Hx | lia].
Qed.

(* ---- THE KIT'S CUT: THE BATCH-KIT LAYER's FRAME LEMMAS (the members' caps and the completed slots' order list) ---- *)

(* a u64 read names one value *)
Lemma vrd_rd_u64_det : forall m a v1 v2, rd_u64 segs m a v1 -> rd_u64 segs m a v2 -> v1 = v2.
Proof.
  intros m a v1 v2 (R1 & H1) (R2 & H2).
  assert (Hb : forall z (w k : nat), 0 <= YO0f.le_byte z w k < 256)
    by (intros z w k; unfold YO0f.le_byte; apply Z.mod_pos_bound; lia).
  assert (E : forall k, (k < 8)%nat -> YO0f.le_byte v1 8 k = YO0f.le_byte v2 8 k).
  { intros k Hk. pose proof (H1 k Hk) as E1. rewrite (H2 k Hk) in E1.
    assert (E2 : bv_unsigned (Z_to_bv 8 (YO0f.le_byte v2 8 k)) = bv_unsigned (Z_to_bv 8 (YO0f.le_byte v1 8 k)))
      by (injection E1 as E1; exact E1).
    rewrite !Z_to_bv_unsigned in E2. unfold bv_wrap in E2.
    change (bv_modulus 8) with 256 in E2.
    rewrite !Z.mod_small in E2 by (apply Hb). symmetry. exact E2. }
  pose proof (YG0s.le_bytes8 v1 R1) as S1. pose proof (YG0s.le_bytes8 v2 R2) as S2.
  change YG0f.le_byte with YO0f.le_byte in S1, S2.
  rewrite <- S1, <- S2, !E by lia. reflexivity.
Qed.

(* rd_keep is PRH_Reader's pj_agreeR (the kit's frame lemmas take that spelling) *)
Lemma vrd_agree_of_keep : forall m m' (X : Z -> Prop), rd_keep m m' X -> pj_agreeR segs m m' X.
Proof. intros m m' X [H1 H2] x Hx. split; [exact (H1 x Hx) | exact (H2 x Hx)]. Qed.

(* the slot lists of the batch kit's layer: over a member list's values, and the object form pj_ncapR states *)
Lemma vrd_kids_snd : forall (P : Z -> jv -> Prop) a (l : list (list Z * jv)),
  pj_kidsR (fun a mb => P a (snd mb)) a l <-> pj_kidsR P a (map snd l).
Proof.
  intros P a l. revert a. induction l as [|[nm u] r IH]; intros a; cbn [pj_kidsR map snd]; [tauto|].
  rewrite IH. tauto.
Qed.

Lemma vrd_kids_let : forall (P : Z -> jv -> Prop) a (l : list (list Z * jv)),
  pj_kidsR (fun a mb => P a (snd mb)) a l <-> pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in P a u) a l.
Proof.
  intros P a l. revert a. induction l as [|[nm u] r IH]; intros a; cbn [pj_kidsR snd]; [tauto|].
  rewrite IH. tauto.
Qed.

(* the frame property of ONE tree's caps *)
Definition rd_ncapframe (t : jv) : Prop :=
  forall m m' lblk p D,
    pj_nodeR segs m lblk p t D -> pj_ncapR segs m p t ->
    rd_keep m m' (fun a => p <= a < p + 56 \/ rd_blk D a) ->
    pj_ncapR segs m' p t.

Lemma vrd_ncaps_items_gen : forall l, Forall rd_ncapframe l ->
  forall m m' lblk a D,
  pj_itemsR (pj_nodeR segs m lblk) a l D -> pj_kidsR (pj_ncapR segs m) a l ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_kidsR (pj_ncapR segs m') a l.
Proof.
  intros l. induction l as [|u r IH]; intros HF m m' lblk a D Hit Hk HK;
    cbn [pj_itemsR pj_kidsR] in Hit, Hk |- *; [exact I|].
  destruct Hit as (D1 & D2 & HD & Hu & Hr). destruct Hk as (Hku & Hkr).
  pose proof (Forall_inv HF) as HFu. pose proof (Forall_inv_tail HF) as HFr.
  split.
  - apply (HFu m m' lblk a D1 Hu Hku). eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + left. cbn [length]. lia.
    + right. rewrite HD. apply rd_blk_app_l. exact Hz.
  - apply (IH HFr m m' lblk (a + 56) D2 Hr Hkr). eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + left. cbn [length]. lia.
    + right. rewrite HD. apply rd_blk_app_r. exact Hz.
Qed.

Lemma vrd_ncaps_mems_gen : forall l, Forall (fun mm => rd_ncapframe (snd mm)) l ->
  forall m m' lblk a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in pj_ncapR segs m a u) a l ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_kidsR (fun a (mb : list Z * jv) => let (_, u) := mb in pj_ncapR segs m' a u) a l.
Proof.
  intros l. induction l as [|[nm u] r IH]; intros HF m m' lblk a ka D Hms Hk HK;
    cbn [pj_memsR pj_kidsR] in Hms, Hk |- *; [exact I|].
  destruct Hms as (x & k & D1 & D2 & HD & Hx & Hnm & Hu & Hr). destruct Hk as (Hku & Hkr).
  pose proof (Forall_inv HF) as HFu. pose proof (Forall_inv_tail HF) as HFr. cbn [snd] in HFu.
  split.
  - apply (HFu m m' lblk a D1 Hu Hku). eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + left. cbn [length]. lia.
    + right. rewrite HD. apply rd_blk_cons. apply rd_blk_app_l. exact Hz.
  - apply (IH HFr m m' lblk (a + 56) (ka + 8) D2 Hr Hkr). eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + left. cbn [length]. lia.
    + right. rewrite HD. apply rd_blk_cons. apply rd_blk_app_r. exact Hz.
Qed.

Lemma pj_ncapR_keep : forall t, rd_ncapframe t.
Proof.
  intros t. induction t using jv_ind'; unfold rd_ncapframe; intros m m' lblk p D HN Hc HK;
    cbn [pj_ncapR] in Hc |- *; try exact I.
  - (* JArr *)
    destruct HN as (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest).
    destruct Hrest as (Hstr0 & Hy0 & Hn & Hnc & Hcap & Di & HD & Hit).
    destruct Hc as (H48 & kids' & H24 & Hks).
    assert (Ek : kids' = kids)
      by (destruct Hhdr as (_ & _ & _ & _ & Hk24 & _); exact (vrd_rd_u64_det m (p + 24) kids' kids H24 Hk24)).
    subst kids'.
    split; [apply (rd_u64_keep m m' (p + 48) _ H48); eapply rd_keep_mono; [exact HK|]; intros z Hz; left; lia|].
    exists kids. split; [apply (rd_u64_keep m m' (p + 24) _ H24); eapply rd_keep_mono; [exact HK|]; intros z Hz; left; lia|].
    apply (vrd_ncaps_items_gen items H m m' lblk kids Di Hit Hks).
    eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + right. destruct Hcap as [(Hc0 & Hk0) | (Hc0 & Hb)].
      { exfalso. rewrite Hn in Hnc. lia. }
      { apply (rd_blk_in D (kids, 56 * cap)).
        - rewrite HD. apply in_or_app. left.
          destruct (Z.eqb_spec cap 0) as [Hz0 | Hz0]; [lia | left; reflexivity].
        - cbn [fst snd]. rewrite Hn in Hnc. lia. }
    + right. rewrite HD. apply rd_blk_app_r. exact Hz.
  - (* JObj *)
    destruct HN as (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest).
    destruct Hrest as (Hstr0 & Hn & Hnc & Hcap & Di & HD & Hms).
    destruct Hc as (H48 & kids' & H24 & Hks).
    assert (Ek : kids' = kids)
      by (destruct Hhdr as (_ & _ & _ & _ & Hk24 & _); exact (vrd_rd_u64_det m (p + 24) kids' kids H24 Hk24)).
    subst kids'.
    split; [apply (rd_u64_keep m m' (p + 48) _ H48); eapply rd_keep_mono; [exact HK|]; intros z Hz; left; lia|].
    exists kids. split; [apply (rd_u64_keep m m' (p + 24) _ H24); eapply rd_keep_mono; [exact HK|]; intros z Hz; left; lia|].
    apply (vrd_ncaps_mems_gen members H m m' lblk kids keys Di Hms Hks).
    eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + right. destruct Hcap as [(Hc0 & Hk0 & Hy0) | (Hc0 & Hbk & Hby)].
      { exfalso. rewrite Hn in Hnc. lia. }
      { apply (rd_blk_in D (kids, 56 * cap)).
        - rewrite HD. apply in_or_app. left.
          destruct (Z.eqb_spec cap 0) as [Hz0 | Hz0]; [lia | left; reflexivity].
        - cbn [fst snd]. rewrite Hn in Hnc. lia. }
    + right. rewrite HD. apply rd_blk_app_r. exact Hz.
Qed.

(* the batch kit slot-list form (VrdIElem.vrd_incaps) over an array's items / an object's members *)
Lemma vrd_ncaps_keep_items : forall (l : list (list Z * jv)) m m' lblk a D,
  pj_itemsR (pj_nodeR segs m lblk) a (map snd l) D ->
  pj_kidsR (fun a mb => pj_ncapR segs m a (snd mb)) a l ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_kidsR (fun a mb => pj_ncapR segs m' a (snd mb)) a l.
Proof.
  intros l m m' lblk a D Hit Hk HK. apply vrd_kids_snd. apply vrd_kids_snd in Hk.
  refine (vrd_ncaps_items_gen (map snd l) _ m m' lblk a D Hit Hk _).
  - apply Forall_forall. intros u _. apply pj_ncapR_keep.
  - rewrite length_map. exact HK.
Qed.

Lemma vrd_ncaps_keep_mems : forall (l : list (list Z * jv)) m m' lblk a ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  pj_kidsR (fun a mb => pj_ncapR segs m a (snd mb)) a l ->
  rd_keep m m' (fun z => a <= z < a + 56 * Z.of_nat (length l) \/ rd_blk D z) ->
  pj_kidsR (fun a mb => pj_ncapR segs m' a (snd mb)) a l.
Proof.
  intros l m m' lblk a ka D Hms Hk HK. apply vrd_kids_let. apply vrd_kids_let in Hk.
  refine (vrd_ncaps_mems_gen l _ m m' lblk a ka D Hms Hk HK).
  apply Forall_forall. intros mm _. apply pj_ncapR_keep.
Qed.

(* a tree whose node's 56 bytes were copied to p' (grow's realloc) keeps its caps at p' *)
Lemma vrd_ncap_move : forall t m m' lblk p p' D,
  pj_nodeR segs m lblk p t D -> pj_ncapR segs m p t ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 -> mbyte segs m' (p' + x) = mbyte segs m (p + x)) ->
  pj_ncapR segs m' p' t.
Proof.
  intros t m m' lblk p p' D HN Hc HK Hb.
  assert (Hmv : forall off v, 0 <= off -> off + 8 <= 56 -> rd_u64 segs m (p + off) v -> rd_u64 segs m' (p' + off) v).
  { intros off v H1 H2 (Hr & Hv). split; [exact Hr|]. intros k Hk.
    replace (p' + off + Z.of_nat k) with (p' + (off + Z.of_nat k)) by lia.
    rewrite Hb by lia. replace (p + (off + Z.of_nat k)) with (p + off + Z.of_nat k) by lia. exact (Hv k Hk). }
  destruct t as [ | | | txt bits | s | items | members ]; cbn [pj_ncapR] in Hc |- *; try exact I.
  - destruct HN as (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest).
    destruct Hrest as (Hstr0 & Hy0 & Hn & Hnc & Hcap & Di & HD & Hit).
    destruct Hc as (H48 & kids' & H24 & Hks).
    assert (Ek : kids' = kids)
      by (destruct Hhdr as (_ & _ & _ & _ & Hk24 & _); exact (vrd_rd_u64_det m (p + 24) kids' kids H24 Hk24)).
    subst kids'.
    split; [exact (Hmv 48 _ ltac:(lia) ltac:(lia) H48)|].
    exists kids. split; [exact (Hmv 24 _ ltac:(lia) ltac:(lia) H24)|].
    apply (vrd_ncaps_items_gen items (proj2 (Forall_forall _ _) (fun u _ => pj_ncapR_keep u))
             m m' lblk kids Di Hit Hks).
    eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + destruct Hcap as [(Hc0 & Hk0) | (Hc0 & Hbk)].
      { exfalso. rewrite Hn in Hnc. lia. }
      { apply (rd_blk_in D (kids, 56 * cap)).
        - rewrite HD. apply in_or_app. left.
          destruct (Z.eqb_spec cap 0) as [Hz0 | Hz0]; [lia | left; reflexivity].
        - cbn [fst snd]. rewrite Hn in Hnc. lia. }
    + rewrite HD. apply rd_blk_app_r. exact Hz.
  - destruct HN as (HND & HAP & num & str & kids & keys & n & cap & Hhdr & Hrest).
    destruct Hrest as (Hstr0 & Hn & Hnc & Hcap & Di & HD & Hms).
    destruct Hc as (H48 & kids' & H24 & Hks).
    assert (Ek : kids' = kids)
      by (destruct Hhdr as (_ & _ & _ & _ & Hk24 & _); exact (vrd_rd_u64_det m (p + 24) kids' kids H24 Hk24)).
    subst kids'.
    split; [exact (Hmv 48 _ ltac:(lia) ltac:(lia) H48)|].
    exists kids. split; [exact (Hmv 24 _ ltac:(lia) ltac:(lia) H24)|].
    apply (vrd_ncaps_mems_gen members (proj2 (Forall_forall _ _) (fun mm _ => pj_ncapR_keep (snd mm)))
             m m' lblk kids keys Di Hms Hks).
    eapply rd_keep_mono; [exact HK|]. intros z [Hz | Hz].
    + destruct Hcap as [(Hc0 & Hk0 & Hy0) | (Hc0 & Hbk & Hby)].
      { exfalso. rewrite Hn in Hnc. lia. }
      { apply (rd_blk_in D (kids, 56 * cap)).
        - rewrite HD. apply in_or_app. left.
          destruct (Z.eqb_spec cap 0) as [Hz0 | Hz0]; [lia | left; reflexivity].
        - cbn [fst snd]. rewrite Hn in Hnc. lia. }
    + rewrite HD. apply rd_blk_app_r. exact Hz.
Qed.

(* the members' caps after grow copied the slot array from a to a' (the trees below stay where they are) *)
Lemma vrd_ncaps_items_move : forall (l : list (list Z * jv)) m m' lblk a a' D,
  pj_itemsR (pj_nodeR segs m lblk) a (map snd l) D ->
  pj_kidsR (fun a mb => pj_ncapR segs m a (snd mb)) a l ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> mbyte segs m' (a' + x) = mbyte segs m (a + x)) ->
  pj_kidsR (fun a mb => pj_ncapR segs m' a (snd mb)) a' l.
Proof.
  induction l as [|[nm u] l IH]; intros m m' lblk a a' D Hit Hk HK Hb;
    cbn [pj_itemsR pj_kidsR map snd length] in Hit, Hk, Hb |- *; [exact I|].
  destruct Hit as (D1 & D2 & -> & Hu & Hr). destruct Hk as (Hku & Hkr). split.
  - apply (vrd_ncap_move u m m' lblk a a' D1 Hu Hku).
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_l. exact Hz.
    + intros x Hx. apply Hb. lia.
  - apply (IH m m' lblk (a + 56) (a' + 56) D2 Hr Hkr).
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_r. exact Hz.
    + intros x Hx. replace (a' + 56 + x) with (a' + (56 + x)) by lia.
      replace (a + 56 + x) with (a + (56 + x)) by lia. apply Hb. lia.
Qed.

Lemma vrd_ncaps_mems_move : forall (l : list (list Z * jv)) m m' lblk a a' ka D,
  pj_memsR segs m lblk (pj_nodeR segs m lblk) a ka l D ->
  pj_kidsR (fun a mb => pj_ncapR segs m a (snd mb)) a l ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 * Z.of_nat (length l) -> mbyte segs m' (a' + x) = mbyte segs m (a + x)) ->
  pj_kidsR (fun a mb => pj_ncapR segs m' a (snd mb)) a' l.
Proof.
  induction l as [|[nm u] l IH]; intros m m' lblk a a' ka D Hms Hk HK Hb;
    cbn [pj_memsR pj_kidsR snd length] in Hms, Hk, Hb |- *; [exact I|].
  destruct Hms as (x & kk & D1 & D2 & -> & Hx & Hc & Hu & Hr). destruct Hk as (Hku & Hkr). split.
  - apply (vrd_ncap_move u m m' lblk a a' D1 Hu Hku).
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_cons. apply rd_blk_app_l. exact Hz.
    + intros x' Hx'. apply Hb. lia.
  - apply (IH m m' lblk (a + 56) (a' + 56) (ka + 8) D2 Hr Hkr).
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_cons. apply rd_blk_app_r. exact Hz.
    + intros x' Hx'. replace (a' + 56 + x') with (a' + (56 + x')) by lia.
      replace (a + 56 + x') with (a + (56 + x')) by lia. apply Hb. lia.
Qed.

(* THE ORDER LIST MOVED: a pj_foR node whose 56 bytes were copied to p', its blocks unchanged (the twin of
   vrd_node_move; a Theorem Labs lane's B' pis_fo_node_xfer) *)
Lemma vrd_fo_node_move : forall d m m' lblk lblk' p p' D F,
  pj_foR segs m lblk d p D F ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 -> mbyte segs m' (p' + x) = mbyte segs m (p + x)) ->
  (forall x, 0 <= x < 56 -> writable_at segs m' (p' + x)) -> p' mod 8 = 0 ->
  pj_apartR D p' ->
  pj_foR segs m' lblk' d p' D F.
Proof.
  intros d m m' lblk lblk' p p' D F H HL HK Hb Hw Hal Hap.
  destruct d as [|d]; cbn [pj_foR] in H |- *; unfold pj_oshapeR in H |- *;
    destruct H as (Hnd & _ & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Fi &
      Hh & Hs & Hk & Hy & Hp & HPi & ->);
    (assert (HinD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
       by (intros b Hb0; eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hb0]));
    (split; [exact Hnd|]); (split; [exact Hap|]);
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di, Fi;
    (split; [exact (vrd_hdr_move m m' p p' ty num str kids keys n cap Hh Hb Hw Hal)|]);
    (split; [destruct Hs as [Hs|(k & _ & ->)]; [left; exact Hs|];
             right; exists k; split; [|reflexivity];
             apply HL; apply HinD; apply in_or_app; left; apply in_eq|]);
    (split; [destruct Hk as [Hk'|(k & _ & Hnk & ->)]; [left; exact Hk'|];
             right; exists k; split; [|split; [exact Hnk | reflexivity]];
             apply HL; apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|]);
    (split; [destruct Hy as [Hy'|(Hks & k & _ & Hnk & ->)]; [left; exact Hy'|];
             right; split; [exact Hks|]; exists k; split; [|split; [exact Hnk | reflexivity]];
             apply HL; apply HinD; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left;
             apply in_eq|]);
    (split; [exact Hp|]); (split; [|reflexivity]).
  - exact HPi.
  - cbv beta in HPi |- *.
    apply (pf_oitemsR_frame segs d m m' lblk lblk' ks kids keys (Z.to_nat n) Di Fi HPi).
    + intros x k Hin. apply HL. apply HinD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      exact Hin.
    + apply vrd_agree_of_keep. eapply rd_keep_mono; [exact HK|].
      intros y Hy'. unfold pf_ofoot in Hy'. destruct Hy' as [Hy'|[(Hks & Hy')|(b & Hb0 & Hy')]].
      * destruct Hk as [(-> & -> & ->)|(k & _ & Hnk & ->)]; [cbn in Hy'; lia|].
        apply (rd_blk_in D (kids, k)); [apply HinD; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
        cbn [fst snd]. lia.
      * destruct Hy as [(-> & -> & ->)|(_ & k & _ & Hnk & ->)]; [discriminate Hks|].
        apply (rd_blk_in D (keys, k));
          [apply HinD; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_eq|].
        cbn [fst snd]. lia.
      * apply (rd_blk_in D b); [|exact Hy'].
        apply HinD. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact Hb0.
Qed.

(* an order list moved with its slot array a -> a' (and key slots ka -> ka'), the slot blocks unchanged (the twin of
   vrd_items_move / vrd_mems_move; a Theorem Labs lane's B' pis_fo_items_xfer) *)
Lemma vrd_fo_items_move : forall d m m' lblk lblk' ks a ka a' ka' n D F,
  pf_oitemsR segs m lblk (pj_foR segs m lblk d) ks a ka n D F ->
  (forall x k, In (x, k) D -> lblk' x k) ->
  rd_keep m m' (rd_blk D) ->
  (forall x, 0 <= x < 56 * Z.of_nat n -> mbyte segs m' (a' + x) = mbyte segs m (a + x)) ->
  (forall x, 0 <= x < 56 * Z.of_nat n -> writable_at segs m' (a' + x)) -> a' mod 8 = 0 ->
  (forall b x, In b D -> pj_holdsR b x -> ~ (a' <= x < a' + 56 * Z.of_nat n)) ->
  (ks = true -> forall x, 0 <= x < 8 * Z.of_nat n -> mbyte segs m' (ka' + x) = mbyte segs m (ka + x)) ->
  pf_oitemsR segs m' lblk' (pj_foR segs m' lblk' d) ks a' ka' n D F.
Proof.
  intros d m m' lblk lblk' ks a ka a' ka' n. revert a ka a' ka'.
  induction n as [|n IH]; intros a ka a' ka' D F H HL HK Hb Hw Hal Hap Hy;
    cbn [pf_oitemsR] in H |- *; [exact H|].
  destruct H as (Dk & D1 & F1 & D2 & F2 & -> & -> & Hk & H1 & H2).
  exists Dk, D1, F1, D2, F2. split; [reflexivity|]. split; [reflexivity|]. split; [|split].
  - unfold pj_keyR in Hk |- *. destruct ks; cbv beta iota in Hk |- *; [|exact Hk].
    destruct Hk as (x & (Hxr & Hxv) & Hc). exists x. split.
    + split; [exact Hxr|]. intros k Hk'. rewrite (Hy eq_refl) by lia. exact (Hxv k Hk').
    + destruct Hc as [Hc|(k & Hl & ->)]; [left; exact Hc|]. right. exists k. split; [|reflexivity].
      apply HL. apply in_or_app. left. apply in_eq.
  - apply (vrd_fo_node_move d m m' lblk lblk' a a' D1 F1 H1).
    + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. left. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_r. apply rd_blk_app_l. exact Hz.
    + intros x Hx. apply Hb. lia.
    + intros x Hx. apply Hw. lia.
    + exact Hal.
    + intros b x Hin Hx Hx'. apply (Hap b x); [apply in_or_app; right; apply in_or_app; left; exact Hin | exact Hx | lia].
  - apply (IH (a + 56) (ka + 8) (a' + 56) (ka' + 8) D2 F2 H2).
    + intros x k Hin. apply HL. apply in_or_app. right. apply in_or_app. right. exact Hin.
    + eapply rd_keep_mono; [exact HK|]. intros z Hz. apply rd_blk_app_r. apply rd_blk_app_r. exact Hz.
    + intros x Hx. replace (a' + 56 + x) with (a' + (56 + x)) by lia.
      replace (a + 56 + x) with (a + (56 + x)) by lia. apply Hb. lia.
    + intros x Hx. replace (a' + 56 + x) with (a' + (56 + x)) by lia. apply Hw. lia.
    + replace (a' + 56) with (a' + 7 * 8) by lia. rewrite Z_mod_plus_full. exact Hal.
    + intros b x Hin Hx Hx'. apply (Hap b x); [apply in_or_app; right; apply in_or_app; right; exact Hin | exact Hx | lia].
    + intros Eks x Hx. replace (ka' + 8 + x) with (ka' + (8 + x)) by lia.
      replace (ka + 8 + x) with (ka + (8 + x)) by lia. apply (Hy Eks). lia.
Qed.

End F.

Print Assumptions pj_nodeR_keep.
Print Assumptions pj_itemsR_keep.
Print Assumptions pj_memsR_keep.
Print Assumptions pj_fdR_keep.
Print Assumptions pj_in_okR_keep.
Print Assumptions vrd_node_fd.
Print Assumptions vrd_items_move.
Print Assumptions vrd_mems_move.
Print Assumptions pj_ncapR_keep.
Print Assumptions vrd_ncap_move.
Print Assumptions vrd_ncaps_items_move.
Print Assumptions vrd_ncaps_mems_move.
Print Assumptions vrd_fo_node_move.
Print Assumptions vrd_fo_items_move.
