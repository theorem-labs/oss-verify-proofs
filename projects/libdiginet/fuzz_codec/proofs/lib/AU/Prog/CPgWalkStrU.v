(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/CPgWalkStr.v and moved to image B (the ASan-UBSan build):
   the image-A core modules are image B's (lib/AU), YImgTop is YImgTopU, the CA_ constants are CB_ ones with
   image B's values; lemma and tactic names unchanged. *)
(* Modified by Theorem Labs, 2026-10: cw_strcmp_at is the text of proofs/libreac/fuzz_identity/lib/A/Prog/
   reac_box_catalogue_defect.v:180-245 (aj_strcmp_at, origin/ossv/recipes 4b6f0df50aa7) in the form of
   lib/Reusable/YCbq.v's aj_bcmp_at, with the result stated as the wrapper's value and moved to libdiginet/fuzz_codec's
   ASan build (image B); cw_cs_k / cw_cs_k_spec are that file's catd_k / catd_k_spec over list Z. *)
(* The call of the strcmp wrapper (image B: the 4-byte jump at 0x422d4) from a walk of codec's own code.
   - cw_strcmp_at: the wrapper's contract (lib/A/Rt/StrcmpDef.v astrcmp_realizes) at the walk's journal, with sp at
     offset o of the journal's sp0: the premises the wrapper asks for (the k + 1 compared bytes of both strings
     readable, marked usable, their shadow window readable, off the 2 * ESTACK window below sp) and the post: the
     caller's journal kept, callee-saved registers kept, the model the same but for materialized pages, a0 = the
     wrapper's value strcmp_res c1 c2, every byte outside the window kept.
   - The C strings: cw_cstr_at W m x s (the bytes of s, then a 0, at x; no 0 in s), from a byte array
     (cw_cstr_of_garr8), from the image (cw_cstr_img; cw_cstr_row for a row lib/A/Prog/CPgWalkRoU.v's
     cpw_rows_free names) or across a run that keeps them (cw_cstr_kept).
   - cw_strcmp_cstr_at: the same call on two C strings sx and sy, each read with a crd_ok premise over its
     length + 1 bytes at the call's sp and window 2 * ESTACK; a0 = w64 (cw_strcmpZ sx sy), the sign of C strcmp,
     which is 0 exactly when sx = sy (cw_strcmpZ_0, cw_strcmpZ_unsigned): the plain model's strcmp contract.
   - crd_ok across a narrower range (cw_crd_sub), a deeper window (cw_crd_win) and a run (cw_crd_kept), and of an
     image range a contract's cimg_rd names, in any state (cw_crd_img, readable bytes by cw_cstr_rd). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Rt Require Import StrcmpDef.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkImgU CPgWalkRoU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================================ C strings over list Z ================================ *)
(* the index where the C strings x and y (no 0 in either) first differ, or where both end *)
Fixpoint cw_cs_k (x y : list Z) : nat :=
match x, y with
| a :: x', b :: y' => if a =? b then S (cw_cs_k x' y') else O
| _, _ => O
end.
Lemma cw_cs_k_le : forall x y, (cw_cs_k x y <= length x)%nat /\ (cw_cs_k x y <= length y)%nat.
Proof.
induction x as [|a x IH]; intros [|b y]; cbn [cw_cs_k length]; try lia.
destruct (a =? b); [destruct (IH y); lia | lia].
Qed.
Lemma cw_cs_k_spec : forall x y, ~ In 0 x -> ~ In 0 y ->
(forall j, (j < cw_cs_k x y)%nat -> nth j (x ++ [0]) 0 = nth j (y ++ [0]) 0 /\ nth j (x ++ [0]) 0 <> 0) /\
(nth (cw_cs_k x y) (x ++ [0]) 0 <> nth (cw_cs_k x y) (y ++ [0]) 0 \/ nth (cw_cs_k x y) (x ++ [0]) 0 = 0) /\
(nth (cw_cs_k x y) (x ++ [0]) 0 = nth (cw_cs_k x y) (y ++ [0]) 0 <-> x = y).
Proof.
induction x as [|a x IH]; intros [|b y] Nx Ny; cbn [cw_cs_k app nth].
- split; [intros j Hj; lia|]. split; [right; reflexivity|]. split; intros; reflexivity.
- split; [intros j Hj; lia|]. split; [right; reflexivity|].
  split; [intros H; exfalso; apply Ny; left; symmetry; exact H | discriminate].
- split; [intros j Hj; lia|]. split; [left; intros H; apply Nx; left; exact H|].
  split; [intros H; exfalso; apply Nx; left; exact H | discriminate].
- destruct (Z.eqb_spec a b) as [Eab|Nab]; cbv beta iota.
  + subst b. destruct (IH y) as (P1 & P2 & P3); [intros H; apply Nx; right; exact H | intros H; apply Ny; right; exact H |].
    split; [intros [|j] Hj; cbn [nth]; [split; [reflexivity | intros H; apply Nx; left; exact H] | apply P1; lia]|].
    cbn [nth]. split; [exact P2|].
    rewrite P3. split; [intros ->; reflexivity | intros H; injection H; auto].
  + split; [intros j Hj; lia|]. cbn [nth]. split; [left; exact Nab|].
    split; [intros H; exfalso; exact (Nab H) | intros H; injection H as H _; exfalso; exact (Nab H)].
Qed.
(* the wrapper's value at that index: the sign of C strcmp(x, y) *)
Definition cw_strcmpZ (x y : list Z) : Z :=
AStrcmpDef.strcmp_res (nth (cw_cs_k x y) (x ++ [0]) 0) (nth (cw_cs_k x y) (y ++ [0]) 0).
Lemma cw_strcmp_res_cases : forall c1 c2,
AStrcmpDef.strcmp_res c1 c2 = 0 \/ AStrcmpDef.strcmp_res c1 c2 = -1 \/ AStrcmpDef.strcmp_res c1 c2 = 1.
Proof. intros c1 c2. unfold AStrcmpDef.strcmp_res. destruct (c1 =? c2); [auto|]. destruct (c1 <? c2); auto. Qed.
Lemma cw_strcmpZ_0 : forall x y, ~ In 0 x -> ~ In 0 y -> (cw_strcmpZ x y = 0 <-> x = y).
Proof.
intros x y Nx Ny. destruct (cw_cs_k_spec x y Nx Ny) as (_ & _ & P3). rewrite <- P3. unfold cw_strcmpZ, AStrcmpDef.strcmp_res.
destruct (Z.eqb_spec (nth (cw_cs_k x y) (x ++ [0]) 0) (nth (cw_cs_k x y) (y ++ [0]) 0)) as [E|E]; [tauto|].
destruct (_ <? _); split; intros H; first [discriminate H | contradiction].
Qed.
(* a0 after the call reads 0 exactly when the strings are equal *)
Lemma cw_strcmpZ_unsigned : forall x y, ~ In 0 x -> ~ In 0 y ->
(bv_unsigned (w64 (cw_strcmpZ x y)) = 0 <-> x = y).
Proof.
intros x y Nx Ny. rewrite <- (cw_strcmpZ_0 x y Nx Ny).
destruct (cw_strcmp_res_cases (nth (cw_cs_k x y) (x ++ [0]) 0) (nth (cw_cs_k x y) (y ++ [0]) 0)) as [E|[E|E]];
unfold cw_strcmpZ; rewrite E; split; intros H; first [reflexivity | vm_compute in H; discriminate H | discriminate H].
Qed.
(* a byte list holding a 0 is a C string, its 0 and the rest *)
Lemma cw_cstr_split : forall tb : list Z, In 0 tb -> exists s rest, tb = s ++ 0 :: rest /\ ~ In 0 s.
Proof.
induction tb as [|b tb IH]; intros H; [destruct H|].
destruct (Z.eq_dec b 0) as [->|E].
- exists [], tb. split; [reflexivity | intros []].
- destruct H as [H|H]; [exfalso; exact (E H)|].
  destruct (IH H) as (s & rest & -> & N). exists (b :: s), rest. split; [reflexivity|].
  intros [H'|H']; [exact (E H') | exact (N H')].
Qed.
Lemma cw_cstringZ_app : forall s rest, ~ In 0 s -> cstringZ (s ++ 0 :: rest) = s.
Proof.
induction s as [|a s IH]; intros rest N; cbn [app cstringZ]; [reflexivity|].
destruct (Z.eqb_spec a 0) as [E|E]; [exfalso; apply N; left; exact E|].
f_equal. apply IH. intros H. apply N. right. exact H.
Qed.

(* ================================ crd_ok, narrower, deeper, kept ================================ *)
Lemma cw_hull_sub : forall (rd : reader) x n x' n',
shadow_hull_vis rd x n -> x <= x' -> x' + n' <= x + n -> 0 < n' -> shadow_hull_vis rd x' n'.
Proof.
intros rd x n x' n' H H1 H2 H3 s Hs. apply H. unfold shadow_addr in *.
pose proof (Z.div_le_mono x x' 8 ltac:(lia) H1).
pose proof (Z.div_le_mono (x' + n' - 1) (x + n - 1) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + x / 8) (SHADOW_OFF + x' / 8) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono (SHADOW_OFF + (x' + n' - 1) / 8) (SHADOW_OFF + (x + n - 1) / 8) 8 ltac:(lia) ltac:(lia)).
lia.
Qed.
Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cw_crd_sub : forall (W : world tfibsegs) m sp T q n q' n',
crd_ok tfibsegs W m sp T q n -> q <= q' -> q' + n' <= q + n -> 0 <= n' -> crd_ok tfibsegs W m sp T q' n'.
Proof.
intros W m sp T q n q' n' (Hq & Hqn & Hrd & Hra & Hhv & Ham & Hcw) H1 H2 H3.
split; [lia|]. split; [lia|]. split; [intros a Ha; apply Hrd; lia|].
split; [eapply range_addressable_sub; [exact Hra | lia | lia]|].
split; [intros Hn'; apply (cw_hull_sub _ q n); [apply Hhv; lia | lia | lia | lia]|].
split; [unfold amem_range in *; lia|]. unfold coff_win in *; lia.
Qed.
Lemma cw_crd_win : forall (W : world tfibsegs) m sp T q n sp' T',
crd_ok tfibsegs W m sp T q n -> sp' <= sp -> sp - T <= sp' - T' -> crd_ok tfibsegs W m sp' T' q n.
Proof.
intros W m sp T q n sp' T' (Hq & Hqn & Hrd & Hra & Hhv & Ham & Hcw) H1 H2.
split; [exact Hq|]. split; [exact Hqn|]. split; [exact Hrd|]. split; [exact Hra|]. split; [exact Hhv|].
split; [exact Ham|]. unfold coff_win in *; lia.
Qed.
(* across a run that keeps every byte outside [lo, hi), a window above the shadow map *)
Lemma cw_crd_kept : forall (W : world tfibsegs) m m' sp T q n lo hi,
crd_ok tfibsegs W m sp T q n ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
kHighShadowEnd <= lo -> (q + n <= lo \/ hi <= q) -> crd_ok tfibsegs W m' sp T q n.
Proof.
intros W m m' sp T q n lo hi (Hq & Hqn & Hrd & Hra & Hhv & Ham & Hcw) HK Hlo Hd.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (H47 : q + n <= 2 ^ 47) by (unfold amem_range in Ham; rewrite C3, C4, C5 in Ham; lia).
split; [exact Hq|]. split; [exact Hqn|].
split; [intros a Ha; rewrite HK; [apply Hrd; exact Ha | lia | lia]|].
split; [exact (range_addressable_kept_win _ _ lo hi q n HK Hlo Hq H47 Hra)|].
split; [intros Hn; exact (shadow_hull_vis_kept_win _ _ lo hi q n HK Hlo Hq H47 Hn (Hhv Hn))|].
split; [exact Ham | exact Hcw].
Qed.

(* ================================ a C string in memory ================================ *)
Definition cw_cstr_at (W : world tfibsegs) (m : word -> option byte) (x : Z) (s : list Z) : Prop :=
~ In 0 s /\
forall j, (j <= length s)%nat -> aview tfibsegs (w_H W) m (x + Z.of_nat j) = Some (nth j (s ++ [0]) 0).
(* from the byte array of a C string: its bytes, a 0 and anything after *)
Lemma cw_cstr_of_garr8 : forall (W : world tfibsegs) m x s rest,
garr8 tfibsegs (mrestrict (w_H W) m) x (s ++ 0 :: rest) -> ~ In 0 s -> cw_cstr_at W m x s.
Proof.
intros W m x s rest Hg N. split; [exact N|]. intros j Hj.
replace (s ++ 0 :: rest) with ((s ++ [0]) ++ rest) in Hg by (rewrite <- app_assoc; reflexivity).
assert (Hj' : (j < length ((s ++ [0%Z]) ++ rest))%nat) by (rewrite !length_app; cbn [length]; lia).
destruct (Hg j Hj') as [Hv Hr].
rewrite app_nth1 in Hv, Hr by (rewrite length_app; cbn [length]; lia).
specialize (Hv 0%nat ltac:(lia)). change (Z.of_nat 0) with 0 in Hv. rewrite Z.add_0_r in Hv.
assert (Hb : mbyte tfibsegs (mrestrict (w_H W) m) (x + Z.of_nat j) = Some (Z_to_bv 8 (nth j (s ++ [0]) 0))).
{ rewrite Hv. f_equal. f_equal. apply cpg_le_byte1. exact Hr. }
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. exact Hr.
Qed.
(* across a run that keeps every byte outside [lo, hi) *)
Lemma cw_cstr_kept : forall (W : world tfibsegs) m m' x s lo hi,
cw_cstr_at W m x s ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
0 <= x -> x + Z.of_nat (length s) + 1 <= 2 ^ 64 -> (x + Z.of_nat (length s) + 1 <= lo \/ hi <= x) ->
cw_cstr_at W m' x s.
Proof.
intros W m m' x s lo hi (N & A) HK Hx Hxs Hd. split; [exact N|]. intros j Hj.
rewrite HK; [apply A; exact Hj | lia | lia].
Qed.
(* from the image: the image file holds the string and its 0 (cw_img_cstr, by computation), and the bytes are
   read-only data that is neither the runtime's own nor errno *)
Definition cw_img_cstr (x : Z) (s : list Z) : bool :=
forallb (fun v => negb (v =? 0)) s &&
forallb (fun j => match img_byte tfibsegs (x + Z.of_nat j) with
                  | Some b => bv_unsigned b =? nth j (s ++ [0]) 0
                  | None => false end) (seq 0 (S (length s))).
Lemma cw_cstr_img : forall B rlo rhi (W : world tfibsegs) m x s,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) m) ->
(forall a, x <= a <= x + Z.of_nat (length s) ->
  in_roP tfibsegs rlo rhi a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
cw_img_cstr x s = true -> cw_cstr_at W m x s.
Proof.
intros B rlo rhi W m x s HRO Hin Hc. unfold cw_img_cstr in Hc. apply andb_prop in Hc as [Hz Hb].
split.
- intros H0. pose proof (proj1 (forallb_forall _ _) Hz 0 H0) as H. discriminate H.
- intros j Hj. destruct (Hin (x + Z.of_nat j) ltac:(lia)) as (H1 & H2 & H3).
  rewrite (HRO _ H1 H2 H3).
  assert (Hk : In j (seq 0 (S (length s)))) by (apply in_seq; lia).
  pose proof (proj1 (forallb_forall _ _) Hb j Hk) as H. cbv beta in H. unfold img_byte in H.
  destruct (seg_rom tfibsegs (Z_to_bv 64 (x + Z.of_nat j))) as [b|]; [|discriminate H].
  apply Z.eqb_eq in H. rewrite <- H. reflexivity.
Qed.
(* the same for a string at the start of a row of a list of free rows (lib/A/Prog/CPgWalkRoU.v cpw_rows_free) *)
Lemma cw_cstr_row : forall B rlo rhi (W : world tfibsegs) m l x n s,
arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) m) -> cpw_rows_free B l -> In (x, n) l ->
(forall j, 0 <= j < n -> in_roP tfibsegs rlo rhi (x + j)) -> Z.of_nat (length s) + 1 <= n ->
cw_img_cstr x s = true -> cw_cstr_at W m x s.
Proof.
intros B rlo rhi W m l x n s HRO HF Hin Hro Hn Hc. apply (cw_cstr_img B rlo rhi W m x s HRO); [|exact Hc].
intros a Ha. destruct (cpw_rows_free_In B l x n (a - x) HF Hin ltac:(lia)) as (Ho & He).
replace (x + (a - x)) with a in Ho, He by lia.
split; [replace a with (x + (a - x)) by lia; apply Hro; lia|]. split; [exact Ho | exact He].
Qed.
(* the bytes of a C string in memory are readable *)
Lemma cw_cstr_rd : forall (W : world tfibsegs) m x s, cw_cstr_at W m x s ->
forall a, x <= a < x + Z.of_nat (length s) + 1 -> aview tfibsegs (w_H W) m a <> None.
Proof.
intros W m x s (_ & A) a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
rewrite A by lia. discriminate.
Qed.
(* an image range of a contract's cimg_rd (CPgBase.cimg_range), read in any state AR holds of, at a deeper window *)
Lemma cw_crd_img : forall B ly S (W : world tfibsegs) m md sp T q n sp' T',
cimg_range tfibsegs B sp T q n -> AR tfibsegs B ly S W m md ->
(forall a, q <= a < q + n -> aview tfibsegs (w_H W) m a <> None) ->
sp' <= sp -> sp - T <= sp' - T' ->
crd_ok tfibsegs W m sp' T' q n.
Proof.
intros B ly S W m md sp T q n sp' T' (Hq & Hn & Hqn & Ham & Hcw & _ & HU) HAR Hrd H1 H2.
destruct (HU ly S W m md HAR) as [Hra Hhv].
split; [exact Hq|]. split; [exact Hqn|]. split; [exact Hrd|]. split; [exact Hra|]. split; [exact Hhv|].
split; [exact Ham|]. unfold coff_win in *; lia.
Qed.
End r.

(* ================================ the call of the wrapper ================================ *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Lemma cw_strcmp_at : forall pc, astrcmp_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k c1 c2 (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
AStrcmpDef.str_meet tfibsegs W memT x y k c1 c2 ->
src_ok tfibsegs W regsT memT x (k + 1) -> src_ok tfibsegs W regsT memT y (k + 1) ->
(forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
(forall a, y <= a <= y + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
amem_range x (k + 1) -> amem_range y (k + 1) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x (k + 1) ->
range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y (k + 1) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
cf = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = w64 (AStrcmpDef.strcmp_res c1 c2) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k c1 c2 o raw
HJ Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hmeet Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
unfold astrcmp_realizes, AStrcmpDef.astrcmp_realizes in AM.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPRE : ecall_pre tfibsegs B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (AM lyc Sc W regsT memT mdc x y k c1 c2 HPRE Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hmeet Hsx Hsy
  ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hsame|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.
(* The same on two C strings, each read under crd_ok at the call's sp with the wrapper's window 2 * ESTACK.
   One of them is shorter than 2 ^ 32 - 1 bytes. *)
Lemma cw_strcmp_cstr_at : forall pc, astrcmp_realizes tfibsegs B pc ->
forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y sx sy (o : Z) raw,
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
(Z.of_nat (length sx) + 1 < 2 ^ 32 \/ Z.of_nat (length sy) + 1 < 2 ^ 32) ->
cw_cstr_at W memT x sx -> cw_cstr_at W memT y sy ->
crd_ok tfibsegs W memT (sp0 + o) (2 * ESTACK) x (Z.of_nat (length sx) + 1) ->
crd_ok tfibsegs W memT (sp0 + o) (2 * ESTACK) y (Z.of_nat (length sy) + 1) ->
SRr tfibsegs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom tfibsegs)) mdc)
(fun W2 cf => W2 = W /\ exists regs2 mem2 md2,
cf = mkCfg (mkst regs2 raw mem2 (seg_rom tfibsegs)) md2 /\
ajournal tfibsegs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
aregs_preserved regsT regs2 /\ same_but_materialized mdc md2 /\ getr regs2 10 = w64 (cw_strcmpZ sx sy) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
  aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
(forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y sx sy o raw
HJ Ha0 Ha1 Hx0 Hy0 Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hlen [Nx AX] [Ny AY] Cx Cy.
assert (ESTACK = 4096) as Hes by reflexivity.
destruct (cw_cs_k_le sx sy) as [Kx Ky].
destruct (cw_cs_k_spec sx sy Nx Ny) as (P1 & P2 & _).
set (kk := cw_cs_k sx sy) in *.
pose proof (cw_crd_sub W memT (sp0 + o) (2 * ESTACK) x _ x (Z.of_nat kk + 1) Cx ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hxq & Hxn & Hxr & Hxa & Hxh & Hxm & Hxw).
pose proof (cw_crd_sub W memT (sp0 + o) (2 * ESTACK) y _ y (Z.of_nat kk + 1) Cy ltac:(lia) ltac:(lia) ltac:(lia))
  as (Hyq & Hyn & Hyr & Hya & Hyh & Hym & Hyw).
unfold coff_win in Hxw, Hyw.
eapply SRr_mono.
{ apply (cw_strcmp_at pc AM W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y (Z.of_nat kk)
    (nth kk (sx ++ [0]) 0) (nth kk (sy ++ [0]) 0) o raw HJ Ha0 Ha1 Hx0 Hy0 ltac:(lia) ltac:(lia) ltac:(lia)
    Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw).
  - split; [lia|]. split.
    + intros i Hi. destruct (P1 (Z.to_nat i) ltac:(lia)) as [Eq Nz].
      exists (nth (Z.to_nat i) (sx ++ [0]) 0).
      replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia. replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
      split; [apply AX; lia|]. split; [rewrite Eq; apply AY; lia | exact Nz].
    + split; [apply AX; lia|]. split; [apply AY; lia | exact P2].
  - intros a Ha. split; [apply Hxr; exact Ha | rewrite Hsp'; lia].
  - intros a Ha. split; [apply Hyr; exact Ha | rewrite Hsp'; lia].
  - intros a Ha. lia.
  - intros a Ha. lia.
  - exact Hxm.
  - exact Hym.
  - exact Hxa.
  - apply Hxh. lia.
  - exact Hya.
  - apply Hyh. lia. }
cbv beta. intros W2 cf _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & Hsame & Hv & Hfr & Hpres).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|]. split; [exact Hsame|]. split; [exact Hv|].
split; [exact Hfr | exact Hpres].
Qed.
End s.
