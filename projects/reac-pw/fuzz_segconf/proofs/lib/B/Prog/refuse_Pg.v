(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan): the reader-keep kit of refuse's image-B prefix walk
   (lib/B/Prog/refuse_P.v, RB_PRE 0x894ac .. RB_REL 0x89544). A sub-lane (under a sub-lane, the image-B refuse walk lane) of
   the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: invariant lemma - the reader-keep transport of refuse's image-B walk; it walks no
   machine code and proves no whole function). Rule 24: the walk's record is ref-common.md "Rule 24" (no released
   proof of refuse); this file is ADAPTED from the image-A kit p10_k_* of lib/A/Prog/pf_a10b_s.v (a B10b sub-lane of
   the image-A G3 walk owner), with the write set a parameter Wl in place of that piece's fixed p10_W.

   refuse's walk calls snprintf and then vsnprintf; each call keeps every byte outside the part it writes and its
   stack window. rbp_K Wl rd rd' says: rd' reads as rd outside the ranges Wl, and every byte rd sees rd' sees. The
   lemmas carry the reader facts of refuse_pre (lib/B/Prog/refuse_c.v), of FFR's argument text
   (lib/B/Prog/refuse_pft.v ffr_arg / ffr_args) and of rt_rom_view (lib/B/Rt/RtDefs.v) across such a step.
   rbp_nout proves `~ rbp_out <list literal> x` by lia from the context. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK0i YK15 YK0j YK18 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFPf RtPFShared RtPFCmd RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require refuse_pft.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
(* a is inside one of the ranges Wl *)
Definition rbp_out (Wl : list (Z * Z)) (a : Z) : Prop := Exists (fun r => fst r <= a < fst r + snd r) Wl.
(* rd' is rd apart from Wl, and every byte rd sees rd' sees *)
Definition rbp_K (Wl : list (Z * Z)) (rd rd' : reader) : Prop :=
(forall a, 0 <= a < 2 ^ 64 -> ~ rbp_out Wl a -> rd' a = rd a) /\
(forall a, rd a <> None -> rd' a <> None).

(* 1 *)
Lemma rbp_out_nil : forall a, ~ rbp_out [] a.
Proof. intros a H. unfold rbp_out in H. apply Exists_nil in H. exact H. Qed.

(* 2 *)
Lemma rbp_out_cons : forall x Wl a, rbp_out (x :: Wl) a <-> (fst x <= a < fst x + snd x) \/ rbp_out Wl a.
Proof. intros x Wl a. unfold rbp_out. apply Exists_cons. Qed.

(* 3 *)
Lemma rbp_K_incl : forall Wl Wl' rd rd', (forall a, ~ rbp_out Wl' a -> ~ rbp_out Wl a) -> rbp_K Wl rd rd' ->
  rbp_K Wl' rd rd'.
Proof.
intros Wl Wl' rd rd' Hi (K1 & K2). split; [|exact K2].
intros a Ha Hn. exact (K1 a Ha (Hi a Hn)).
Qed.

(* 4 *)
Lemma rbp_K_trans : forall Wl rd rd' rd'', rbp_K Wl rd rd' -> rbp_K Wl rd' rd'' -> rbp_K Wl rd rd''.
Proof.
intros Wl rd rd' rd'' (K1 & K2) (L1 & L2). split.
- intros a Ha Hn. rewrite (L1 a Ha Hn). exact (K1 a Ha Hn).
- intros a Ha. exact (L2 a (K2 a Ha)).
Qed.

(* 5 *)
Lemma rbp_k_zs : forall Wl rd rd' p l, rbp_K Wl rd rd' -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall x, p <= x < p + Z.of_nat (length l) -> ~ rbp_out Wl x) -> sa_zs rd p l -> sa_zs rd' p l.
Proof.
intros Wl rd rd' p l (K1 & K2) Hp Hl Hn H. unfold sa_zs in *. intros i Hi.
assert (Hr : 0 <= p + Z.of_nat i < 2 ^ 64) by lia.
rewrite (K1 (p + Z.of_nat i) Hr) by (apply Hn; lia). exact (H i Hi).
Qed.

(* 6 *)
Lemma rbp_k_tail : forall Wl rd rd' e, rbp_K Wl rd rd' -> sa_tail rd e -> sa_tail rd' e.
Proof. intros Wl rd rd' e (K1 & K2) H. unfold sa_tail in *. intros x Hx. exact (K2 x (H x Hx)). Qed.

(* 7 *)
Lemma rbp_k_str : forall Wl rd rd' p s, rbp_K Wl rd rd' -> 0 <= p -> p + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  (forall x, p <= x <= p + Z.of_nat (length s) -> ~ rbp_out Wl x) -> sa_str rd p s -> sa_str rd' p s.
Proof.
intros Wl rd rd' p s K Hp Hb Hn H. unfold sa_str, sa_strz in *. destruct H as ((Hz & H0) & Ht).
split; [split; [|exact H0] | exact (rbp_k_tail Wl rd rd' _ K Ht)].
apply (rbp_k_zs Wl rd rd' p (s ++ [0]) K Hp); [ | | exact Hz].
- rewrite length_app. cbn [length]. lia.
- intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply Hn. lia.
Qed.

(* 8 *)
Lemma rbp_k_hull : forall Wl rd rd' q n, rbp_K Wl rd rd' -> shadow_hull_vis rd q n -> shadow_hull_vis rd' q n.
Proof.
intros Wl rd rd' q n (K1 & K2) H. unfold shadow_hull_vis in *. intros s Hs. exact (K2 s (H s Hs)).
Qed.

(* 9 *)
Lemma rbp_k_addr : forall Wl rd rd' q n, rbp_K Wl rd rd' ->
  (forall x, q <= x < q + n -> ~ rbp_out Wl (shadow_of_addr SHADOW_OFF x)) ->
  (forall x, q <= x < q + n -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64) ->
  sa_addr rd q n -> sa_addr rd' q n.
Proof.
intros Wl rd rd' q n K Hn Hs H. pose proof K as (K1 & K2).
unfold sa_addr in *. destruct H as (A0 & A1 & A2 & A3 & A4).
split; [exact A0|]. split; [exact A1|]. split; [exact A2|]. split.
- unfold range_addressable in *. intros x Hx. destruct (A3 x Hx) as (s & Hs1 & Hok). exists s.
  split; [|exact Hok]. rewrite (K1 _ (Hs x Hx) (Hn x Hx)). exact Hs1.
- intros H0. exact (rbp_k_hull Wl rd rd' q n K (A4 H0)).
Qed.

(* 10 *)
Lemma rbp_k_val : forall Wl rd rd' a n v, rbp_K Wl rd rd' -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> ~ rbp_out Wl x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof.
intros Wl rd rd' a n v (K1 & K2) Ha Hb Hn H. unfold sa_val in *. intros k Hk.
assert (Hr : 0 <= a + Z.of_nat k < 2 ^ 64) by lia.
rewrite (K1 (a + Z.of_nat k) Hr) by (apply Hn; lia). exact (H k Hk).
Qed.

(* 11 *)
Lemma rbp_k_rd32 : forall Wl rd rd' a v, rbp_K Wl rd rd' -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  (forall x, a <= x < a + 4 -> ~ rbp_out Wl x) -> rd32 rd a v -> rd32 rd' a v.
Proof.
intros Wl rd rd' a v (K1 & K2) Ha Hb Hn H. unfold rd32 in *. intros k Hk.
assert (Hr : 0 <= a + Z.of_nat k < 2 ^ 64) by lia.
rewrite (K1 (a + Z.of_nat k) Hr) by (apply Hn; lia). exact (H k Hk).
Qed.

(* 12 *)
Lemma rbp_k_word : forall Wl rd rd' a v, rbp_K Wl rd rd' -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> ~ rbp_out Wl x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof.
intros Wl rd rd' a v (K1 & K2) Ha Hb Hn H.
rewrite (rdword_ext rd rd' a); [exact H|].
intros k Hk. assert (Hr : 0 <= a + k < 2 ^ 64) by lia.
apply (K1 (a + k) Hr). apply Hn. lia.
Qed.

(* 13 *)
Lemma rbp_k_ssp : forall Wl rd rd' gotw guard, rbp_K Wl rd rd' -> 0 <= gotw -> gotw + 8 <= 2 ^ 64 ->
  0 <= guard -> guard + 8 <= 2 ^ 64 ->
  (forall x, gotw <= x < gotw + 8 -> ~ rbp_out Wl x) -> (forall x, guard <= x < guard + 8 -> ~ rbp_out Wl x) ->
  sa_ssp rd gotw guard -> sa_ssp rd' gotw guard.
Proof.
intros Wl rd rd' gotw guard K Hg0 Hg1 Hd0 Hd1 Hng Hnd H. unfold sa_ssp in *. destruct H as (G1 & g & G2).
split.
- exact (rbp_k_word Wl rd rd' gotw guard K Hg0 Hg1 Hng G1).
- exists g. exact (rbp_k_word Wl rd rd' guard g K Hd0 Hd1 Hnd G2).
Qed.

(* 14 *)
Lemma rbp_k_lit : forall Wl rd rd' a s, rbp_K Wl rd rd' -> 0 <= a -> a + Z.of_nat (length s) + 1 <= 2 ^ 64 ->
  (forall x, a <= x <= a + Z.of_nat (length s) -> ~ rbp_out Wl x) ->
  sa_lit segs B rd a s -> sa_lit segs B rd' a s.
Proof.
intros Wl rd rd' a s K Ha Hb Hn H. unfold sa_lit in *. destruct H as (H0 & Hs & Hp & Hr & Hi).
split; [exact H0|]. split; [exact (rbp_k_str Wl rd rd' a s K Ha Hb Hn Hs)|].
exact (conj Hp (conj Hr Hi)).
Qed.

(* 15 *)
Lemma rbp_k_words_at : forall Wl rd rd' ap ws, rbp_K Wl rd rd' -> 0 <= ap ->
  ap + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  (forall x, ap <= x < ap + 8 * Z.of_nat (length ws) -> ~ rbp_out Wl x) ->
  words_at rd ap ws -> words_at rd' ap ws.
Proof.
intros Wl rd rd' ap ws K H0 H1 Hn H. unfold words_at in *. intros i Hi.
apply (rbp_k_word Wl rd rd' (ap + 8 * Z.of_nat i) _ K); [lia | lia | | exact (H i Hi)].
intros x Hx. apply Hn. lia.
Qed.

(* 16. The per-argument side conditions of rbp_k_ffr_args: an %s argument's bytes and NUL, and the shadow bytes of
   its sa_addr range, lie outside Wl; an integer argument is no memory. The bounds on w come from ffr_arg itself
   (0 < w, and sa_addr's w + |s| + 1 <= 2 ^ 63). *)
Definition rbp_arg_apart (Wl : list (Z * Z)) (w : Z) (x : SegModel.arg) : Prop :=
match x with
| SegModel.AS s =>
    (forall y, w <= y <= w + Z.of_nat (length s) -> ~ rbp_out Wl y) /\
    (forall y, w <= y < w + Z.of_nat (length s) + 1 -> ~ rbp_out Wl (shadow_of_addr SHADOW_OFF y))
| SegModel.AI _ => True
end.
Lemma rbp_k_ffr_arg_ap : forall Wl rd rd' rs w x, rbp_K Wl rd rd' -> rbp_arg_apart Wl w x ->
  refuse_pft.ffr_arg rd rs w x -> refuse_pft.ffr_arg rd' rs w x.
Proof.
intros Wl rd rd' rs w x K Ha Hx. destruct x as [s | z]; [|exact Hx].
unfold rbp_arg_apart in Ha. destruct Ha as (H1 & H2).
unfold refuse_pft.ffr_arg in Hx |- *. destruct Hx as (X0 & X1 & X2 & X3 & X4 & X5 & X6).
pose proof X4 as (A0 & A1 & _).
split; [exact X0|]. split.
{ apply (rbp_k_str Wl rd rd' w s K); [lia | lia | | exact X1]. intros y Hy. apply H1. lia. }
split; [exact X2|]. split; [exact X3|]. split.
{ apply (rbp_k_addr Wl rd rd' w _ K); [ | | exact X4].
  - intros y Hy. apply H2. lia.
  - intros y Hy. unfold shadow_of_addr, SHADOW_OFF.
    assert (Q0 : 0 <= y / 8) by (apply Z.div_pos; lia).
    assert (Q1 : y / 8 <= y) by (apply Z.div_le_upper_bound; lia).
    lia. }
split; [exact X5 | exact X6].
Qed.
Lemma rbp_k_ffr_arg : forall Wl rd rd' rs w x, rbp_K Wl rd rd' ->
  (forall y, w <= y <= w + 8 + Z.of_nat (length (SegModel.arg_s x)) -> ~ rbp_out Wl y) ->
  (forall y, w <= y < w + Z.of_nat (length (SegModel.arg_s x)) + 1 -> ~ rbp_out Wl (shadow_of_addr SHADOW_OFF y)) ->
  0 <= w -> w + Z.of_nat (length (SegModel.arg_s x)) + 8 <= 2 ^ 63 ->
  refuse_pft.ffr_arg rd rs w x -> refuse_pft.ffr_arg rd' rs w x.
Proof.
intros Wl rd rd' rs w x K H1 H2 H3 H4 Hx. apply (rbp_k_ffr_arg_ap Wl rd rd' rs w x K); [|exact Hx].
destruct x as [s | z]; [|exact I].
pose proof Hx as Hx'. unfold refuse_pft.ffr_arg, sa_str, sa_strz in Hx'.
destruct Hx' as (_ & ((_ & Hnz) & _) & _).
assert (E : SegModel.arg_s (SegModel.AS s) = s) by (unfold SegModel.arg_s; apply SegModel.cut_nul_id; exact Hnz).
rewrite E in H1, H2. unfold rbp_arg_apart. split.
- intros y Hy. apply H1. lia.
- intros y Hy. apply H2. lia.
Qed.

(* 17 *)
Fixpoint rbp_args_apart (Wl : list (Z * Z)) (ws : list Z) (xs : list SegModel.arg) : Prop :=
match xs, ws with
| [], _ => True
| x :: xs', w :: ws' => rbp_arg_apart Wl w x /\ rbp_args_apart Wl ws' xs'
| _ :: _, [] => True
end.
Lemma rbp_k_ffr_args : forall Wl rd rd' rs ws xs, rbp_K Wl rd rd' -> rbp_args_apart Wl ws xs ->
  refuse_pft.ffr_args rd rs ws xs -> refuse_pft.ffr_args rd' rs ws xs.
Proof.
intros Wl rd rd' rs ws xs K. revert ws. induction xs as [|x xs IH]; intros ws Ha H;
  destruct ws as [|w ws]; [exact I | exact I | exact H |].
cbn [rbp_args_apart refuse_pft.ffr_args] in Ha, H |- *.
destruct Ha as (Ha1 & Ha2). destruct H as (H1 & H2).
split; [exact (rbp_k_ffr_arg_ap Wl rd rd' rs w x K Ha1 H1) | exact (IH ws Ha2 H2)].
Qed.

(* 18 *)
Lemma rbp_k_rom : forall Wl (W : world segs) mem mem',
  rbp_K Wl (aview segs (w_H W) mem) (aview segs (w_H W) mem') ->
  (forall a, in_rom segs a -> 0 <= a < 2 ^ 64 /\ ~ rbp_out Wl a) ->
  RtDefs.rt_rom_view segs B W mem -> RtDefs.rt_rom_view segs B W mem'.
Proof.
intros Wl W mem mem' (K1 & K2) Hr Hv. eapply RtDefs.rt_rom_view_keep; [exact Hv|].
intros a H1 _ _. destruct (Hr a H1) as (Ha & Hn). exact (K1 a Ha Hn).
Qed.
End d.

(* 19: `~ rbp_out <list literal> x` from the context: each range of the literal is refuted by lia *)
Ltac rbp_nout :=
  let HX := fresh "HX" in
  intros HX;
  repeat (apply rbp_out_cons in HX; destruct HX as [HX | HX]; [cbn [fst snd] in HX; lia |]);
  exact (rbp_out_nil _ HX).
Lemma rbp_nout_test : forall p q x, p + 16 <= x -> x < q ->
  ~ rbp_out [(p, 8)] x /\
  ~ rbp_out [(p, 8); (q, 8)] x /\
  ~ rbp_out [(p, 8); (q, 8); (p + 8, 8)] x /\
  ~ rbp_out [(p, 8); (q, 8); (p + 8, 8); (q + 8, 4)] x /\
  ~ rbp_out [(p, 8); (q, 8); (p + 8, 8); (q + 8, 4); (p - 64, 64)] x /\
  ~ rbp_out [(p, 8); (q, 8); (p + 8, 8); (q + 8, 4); (p - 64, 64); (q + 12, 100)] x.
Proof. intros p q x H1 H2. repeat split; rbp_nout. Qed.
