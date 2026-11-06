(* fuzz_preset, parse_value's image-B walk (lane PValueB), EXIT segment: the FRAME lemmas of PRH_Reader.v's REFUSED
   tree (pj_fdR) and of its cursor (pj_in_okR / pj_in_afterR) - the twins of lib/A/Prog/PRW_PjExt.v's pj_nodeR_frame,
   which that file does not carry. Same footprint (PRW_PjExt.pjx_foot p D) and same agreement (pjx_agree): a memory
   that keeps the node's 56 header bytes and the bytes of its blocks D, and keeps a writable byte writable, holds the
   same refused tree. The exit segment needs them because its three writes (the retired magic in the fake frame's
   word 0, the frame's 8 shadow bytes, the runtime's flag byte) land outside every footprint of the post.
   Image-free, allocator-free: no address, no image constant; numerals are the node layout (LENGTH: 56 node bytes,
   8 key-pointer stride, 24 cursor bytes). Rule 24: no released or live-head frame lemma of pj_fdR / pj_in_okR
   exists (the released plain twin is lib/Prog/CrsNode.v over plain PjStruct.pj_fd, a different vocabulary). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YI00 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_PjExt.
Import ListNotations.
Local Open Scope Z_scope.

Section e.
Variable segs : list Segment.

(* the key pointer of one member: read only when the shape has keys *)
Lemma pjx_key_frame : forall m m' lblk ks ka Dk,
  pj_keyR segs m lblk ks ka Dk ->
  (ks = true -> forall x, ka <= x < ka + 8 -> mbyte segs m' x = mbyte segs m x) ->
  pj_keyR segs m' lblk ks ka Dk.
Proof.
intros m m' lblk ks ka Dk H E. destruct ks; cbn [pj_keyR] in H |- *; [|exact H].
destruct H as (x & Hx & Hd). exists x. split; [|exact Hd].
apply (pjx_u64 segs m m' ka x Hx). exact (E eq_refl).
Qed.

(* the members of a refused node: item i at a + 56 i, its key pointer at ka + 8 i *)
Lemma pjx_fitems_frame : forall n (P P' : Z -> list (Z * Z) -> Prop) m m' lblk ks a ka D,
  pf_itemsR segs m lblk P ks a ka n D ->
  (ks = true -> forall i x, (i < n)%nat ->
     ka + 8 * Z.of_nat i <= x < ka + 8 * Z.of_nat i + 8 -> mbyte segs m' x = mbyte segs m x) ->
  (forall i D1, (i < n)%nat -> incl D1 D -> P (a + 56 * Z.of_nat i) D1 -> P' (a + 56 * Z.of_nat i) D1) ->
  pf_itemsR segs m' lblk P' ks a ka n D.
Proof.
induction n as [|n IH]; intros P P' m m' lblk ks a ka D H HK HP; cbn [pf_itemsR] in H |- *; [exact H|].
destruct H as (Dk & D1 & D2 & -> & Hk & H1 & H2).
exists Dk, D1, D2. split; [reflexivity|].
split.
{ apply (pjx_key_frame m m' lblk ks ka Dk Hk). intros Hks x Hx.
  apply (HK Hks 0%nat x ltac:(lia)). cbn [Z.of_nat]. lia. }
split.
{ pose proof (HP 0%nat D1 ltac:(lia)
    (fun y Hy => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hy))))) as HP0.
  replace (a + 56 * Z.of_nat 0) with a in HP0 by lia. exact (HP0 H1). }
apply (IH P P' m m' lblk ks (a + 56) (ka + 8) D2 H2).
- intros Hks i x Hi Hx. apply (HK Hks (S i) x ltac:(lia)). lia.
- intros i D1' Hi Hinc HPi.
  pose proof (HP (S i) D1' ltac:(lia)
    (fun y Hy => in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror (Hinc y Hy)))))) as HPi'.
  replace (a + 56 * Z.of_nat (S i)) with (a + 56 + 56 * Z.of_nat i) in HPi' by lia.
  exact (HPi' HPi).
Qed.

(* THE FRAME LEMMA of the refused tree *)
Lemma pjx_fd_frame : forall d m m' lblk p D,
  pj_fdR segs m lblk d p D -> pjx_agree segs m m' (pjx_foot p D) -> pj_fdR segs m' lblk d p D.
Proof.
induction d as [|d IH]; intros m m' lblk p D H HM; cbn [pj_fdR] in H |- *; unfold pj_fshapeR in H |- *;
  destruct H as (Hn & Ha & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & Hh & HDs & HDk & HDy & HPerm & HPi);
  assert (HM1 : forall x, pjx_foot p D x -> mbyte segs m' x = mbyte segs m x)
    by (intros x Hx; exact (proj1 (HM x Hx)));
  (split; [exact Hn|]); (split; [exact Ha|]);
  exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
  (split; [apply (pjx_hdr segs m m'); [exact Hh | intros x Hx; apply HM; left; exact Hx]|]);
  (split; [exact HDs|]); (split; [exact HDk|]); (split; [exact HDy|]); (split; [exact HPerm|]).
- exact HPi.
- assert (HDin : forall b, In b Di -> In b D).
  { intros b Hb. apply (Permutation_in _ (Permutation_sym HPerm)).
    apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hb. }
  apply (pjx_fitems_frame (Z.to_nat n) (pj_fdR segs m lblk d) (pj_fdR segs m' lblk d) m m' lblk ks kids keys Di HPi).
  + intros Hks i x Hi Hx.
    destruct HDy as [(_ & Hks' & _) | (_ & k & Hl & Hle & EDy)]; [rewrite Hks in Hks'; discriminate Hks'|].
    apply HM1. right. exists (keys, k). split.
    * apply (Permutation_in _ (Permutation_sym HPerm)).
      apply in_or_app; right; apply in_or_app; right; apply in_or_app; left. rewrite EDy. left. reflexivity.
    * unfold pj_holdsR. cbn [fst snd]. assert (Z.of_nat i + 1 <= n) by lia. lia.
  + intros i D1 Hi Hinc HPi'.
    destruct HDk as [(Hk0 & Hn0 & _) | (k & Hl & Hle & EDk)]; [lia|].
    assert (HinK : In (kids, k) D).
    { apply (Permutation_in _ (Permutation_sym HPerm)).
      apply in_or_app; right; apply in_or_app; left. rewrite EDk. left. reflexivity. }
    apply (IH m m' lblk (kids + 56 * Z.of_nat i) D1 HPi').
    intros x Hx. apply HM. destruct Hx as [Hx | (b & Hb & Hx)].
    * right. exists (kids, k). split; [exact HinK|].
      unfold pj_holdsR. cbn [fst snd]. assert (Z.of_nat i + 1 <= n) by lia. lia.
    * right. exists b. split; [exact (HDin b (Hinc b Hb)) | exact Hx].
Qed.

(* the cursor: the 24 bytes at q and the text *)
Lemma pjx_in_ok_frame : forall m m' q text len p d tb,
  pj_in_okR segs m q text len p d tb ->
  (forall x, q <= x < q + 24 -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, q <= x < q + 24 -> writable_at segs m x -> writable_at segs m' x) ->
  (forall x, text <= x < text + Z.of_nat (length tb) -> mbyte segs m' x = mbyte segs m x) ->
  pj_in_okR segs m' q text len p d tb.
Proof.
intros m m' q text len p d tb (V1 & V2 & V3 & Hrw & Hal & Ht0 & Htl & Hp & Hlen & GT & Hdq & Hd) EQ EW ET.
split; [apply (pjx_val segs m m' q 8 p V1); intros x Hx; apply EQ; cbn in Hx; lia|].
split; [apply (pjx_val segs m m' (q + 8) 8 (text + len) V2); intros x Hx; apply EQ; cbn in Hx; lia|].
split; [apply (pjx_val segs m m' (q + 16) 4 d V3); intros x Hx; apply EQ; cbn in Hx; lia|].
split; [intros x Hx; apply (EW x Hx); exact (Hrw x Hx)|].
split; [exact Hal|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hp|]. split; [exact Hlen|].
split; [|split; [exact Hdq | exact Hd]].
apply (pjx_garr8 segs m m' text tb GT). intros x Hx. apply ET. exact Hx.
Qed.

Lemma pjx_in_after_frame : forall m m' q text len lo hi,
  pj_in_afterR segs m q text len lo hi ->
  (forall x, q <= x < q + 24 -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, q <= x < q + 24 -> writable_at segs m x -> writable_at segs m' x) ->
  pj_in_afterR segs m' q text len lo hi.
Proof.
intros m m' q text len lo hi (p' & d' & Hp & Hd & V1 & V2 & V3 & Hrw) EQ EW.
exists p', d'. split; [exact Hp|]. split; [exact Hd|].
split; [apply (pjx_val segs m m' q 8 p' V1); intros x Hx; apply EQ; cbn in Hx; lia|].
split; [apply (pjx_val segs m m' (q + 8) 8 (text + len) V2); intros x Hx; apply EQ; cbn in Hx; lia|].
split; [apply (pjx_val segs m m' (q + 16) 4 d' V3); intros x Hx; apply EQ; cbn in Hx; lia|].
intros x Hx. apply (EW x Hx). exact (Hrw x Hx).
Qed.

(* a node's footprint, read off the two post shapes: the header and the blocks *)
Lemma pjx_agree_of_bytes : forall (m m' : word -> option byte) (X : Z -> Prop),
  (forall x, X x -> mbyte segs m' x = mbyte segs m x) ->
  (forall x, writable_at segs m x -> writable_at segs m' x) ->
  pjx_agree segs m m' X.
Proof. intros m m' X HB HW x Hx. split; [exact (HB x Hx) | intros H; exact (HW x H)]. Qed.

End e.
