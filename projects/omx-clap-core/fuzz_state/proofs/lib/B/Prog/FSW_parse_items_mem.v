(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) helpers of the parse_items walk: memory transport along
   the walk's journal, the frame chain at s0 = q + 16, and where the result object v lies.
   B-LOCAL COPIES (renamed pv_ -> pim_, statements and proofs otherwise verbatim) of the B parse_value walk's helpers,
   copied from a working branch a40df3dd279
   proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value_holds.v (a Theorem Labs lane; no B kit twin):
   pim_eqon (pv_eqon) and its lemmas pim_eqon_sub / _trans / _refl / _keep / _val / _bytes / _wrat / _wr / _in / _zero /
   _RA, pim_aview_low, pim_pstat_img, pim_glob_eqon, pim_glob_aview, pim_inFP_nil, pim_ot16, pim_bad_next_le,
   pim_aview_eq2, pim_aview_nonneg, pim_skipn_map, pim_skipn_skipn, pim_skipn_app_len, pim_rest_skip, pim_mb_of_mr,
   pim_val_mb, pim_rdword_U, pim_val1, pim_byte_tb, pim_ro_keep, pim_v_place, pim_v_awr, pim_ush_frame, pim_ra_v;
   and from the same commit's proofs/omx-clap-core/fuzz_state/lib/B/Prog/FSW_parse_value.v: pim_wr_keep (pv_wr_keep).
   NEW here: pim_chain_q16 (the chain every parse_items callee's fpreU reads: B keeps q + 16 in s0 from 0x84ef0 on, so
   the chain is [] or the one record (q + 16, in->end, in->p), which in->p < q + 16 stops) and pim_pobj_mk (v's pobj at
   any point of the walk from the entry's, its placement and shadow along the journal, its writability given).
   rule 24: proves no function (kind: helper lemmas). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSPstat FSH_Fn_reader FSW_rd FSW_pj FSW_K3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require ReaderRes PjStruct PjIn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YI14.
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= list facts of the text (copied, see the header) ================= *)
Lemma pim_skipn_map : forall (f : byte -> Z) n (l : list byte), skipn n (map f l) = map f (skipn n l).
Proof. intros f n. induction n as [|n IH]; intros [|x l]; cbn; try reflexivity. apply IH. Qed.
Lemma pim_skipn_skipn : forall {A} n m (l : list A), skipn n (skipn m l) = skipn (n + m) l.
Proof.
intros A n m. revert n. induction m as [|m IH]; intros n l; [rewrite Nat.add_0_r; reflexivity|].
destruct l as [|x l]; cbn [skipn]; [rewrite !skipn_nil; reflexivity|].
rewrite IH. replace (n + S m)%nat with (S (n + m)) by lia. reflexivity.
Qed.
Lemma pim_skipn_app_len : forall {A} (s l : list A), skipn (length s) (s ++ l) = l.
Proof. intros A s. induction s as [|x s IH]; intros l; [reflexivity|]. cbn. apply IH. Qed.
(* in->p moved past the white space *)
Lemma pim_rest_skip : forall tb text p (ws r : list Z), text <= p ->
  ReaderRes.rest_at tb text p = ws ++ r -> ReaderRes.rest_at tb text (p + Z.of_nat (length ws)) = r.
Proof.
intros tb text p ws r Hp E. unfold ReaderRes.rest_at, ReaderRes.zb in *.
replace (Z.to_nat (p + Z.of_nat (length ws) - text)) with (length ws + Z.to_nat (p - text))%nat by lia.
rewrite <- pim_skipn_skipn, <- pim_skipn_map, E. apply pim_skipn_app_len.
Qed.

(* ================= memory transport: pointwise agreement of the restricted memory (copied) ================= *)
Definition pim_eqon (M M' : word -> option byte) (lo hi : Z) : Prop :=
  forall a, lo <= a < hi -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).

Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* writability reads one byte of the view (skip_ws walk's skw_wr_eq) *)
Lemma pim_wr_keep : forall (m m' : word -> option byte) a, m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a E. unfold writable_at, wview. rewrite E. reflexivity. Qed.
Lemma pim_eqon_sub : forall M M' lo hi lo' hi', pim_eqon M M' lo hi -> lo <= lo' -> hi' <= hi -> pim_eqon M M' lo' hi'.
Proof. intros M M' lo hi lo' hi' E H1 H2 a Ha. apply E. lia. Qed.
Lemma pim_eqon_trans : forall M1 M2 M3 lo hi, pim_eqon M1 M2 lo hi -> pim_eqon M2 M3 lo hi -> pim_eqon M1 M3 lo hi.
Proof. intros M1 M2 M3 lo hi E1 E2 a Ha. rewrite (E2 a Ha). exact (E1 a Ha). Qed.
Lemma pim_eqon_refl : forall M lo hi, pim_eqon M M lo hi.
Proof. intros M lo hi a _. reflexivity. Qed.
Lemma pim_eqon_keep : forall M M' (P : Z -> Prop) lo hi,
  (forall x : word, ~ P (bv_unsigned x) -> M' x = M x) -> 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> ~ P a) -> pim_eqon M M' lo hi.
Proof. intros M M' P lo hi K H0 H1 HP a Ha. apply K. rewrite wz by lia. apply HP. exact Ha. Qed.
Lemma pim_eqon_val : forall M M' a (n : nat) v, pim_eqon M M' a (a + Z.of_nat n) ->
  val_mem tfibsegs M a n v -> val_mem tfibsegs M' a n v.
Proof. intros M M' a n v E V k Hk. pose proof (V k Hk) as Vk. unfold mbyte in *. rewrite E by lia. exact Vk. Qed.
Lemma pim_eqon_bytes : forall M M' a bs, pim_eqon M M' a (a + Z.of_nat (length bs)) ->
  Mem.bytes_at tfibsegs M a bs -> Mem.bytes_at tfibsegs M' a bs.
Proof.
intros M M' a bs E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
pose proof (H i Hi) as Hh. unfold Mem.mrd, Mem.wa in *. rewrite E by lia. exact Hh.
Qed.
Lemma pim_eqon_wrat : forall M M' a, pim_eqon M M' a (a + 1) -> writable_at tfibsegs M a -> writable_at tfibsegs M' a.
Proof. intros M M' a E H. apply (proj1 (pim_wr_keep M M' a (E a ltac:(lia)))). exact H. Qed.
Lemma pim_eqon_wr : forall M M' a n, pim_eqon M M' a (a + n) -> Mem.wr_at tfibsegs M a n -> Mem.wr_at tfibsegs M' a n.
Proof.
intros M M' a n E (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
pose proof (H i Hi) as Hh. change (writable_at tfibsegs M' (a + i)). change (writable_at tfibsegs M (a + i)) in Hh.
exact (pim_eqon_wrat M M' (a + i) ltac:(eapply pim_eqon_sub; [exact E | lia | lia]) Hh).
Qed.
Lemma pim_eqon_in : forall M M' q text len p d tb, pim_eqon M M' q (q + 24) -> pim_eqon M M' text (text + len) ->
  PjIn.pj_in_ok tfibsegs M q text len p d tb -> PjIn.pj_in_ok tfibsegs M' q text len p d tb.
Proof.
intros M M' q text len p d tb Eq Et (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12).
refine (conj _ (conj _ (conj _ (conj _ (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj _ (conj H11 H12))))))))))).
- apply (pim_eqon_bytes M M' q); [|exact H1]. rewrite Mem.length_le8. eapply pim_eqon_sub; [exact Eq | lia | lia].
- apply (pim_eqon_bytes M M' (q + 8)); [|exact H2]. rewrite Mem.length_le8. eapply pim_eqon_sub; [exact Eq | lia | lia].
- apply (pim_eqon_bytes M M' (q + 16)); [|exact H3]. rewrite Mem.length_le4. eapply pim_eqon_sub; [exact Eq | lia | lia].
- exact (pim_eqon_wr M M' q 24 Eq H4).
- apply (pim_eqon_bytes M M' text); [|exact H10]. rewrite H9. exact Et.
Qed.
Lemma pim_eqon_zero : forall M M' v, pim_eqon M M' v (v + 56) -> PjStruct.pj_zero tfibsegs M v -> PjStruct.pj_zero tfibsegs M' v.
Proof.
intros M M' v E ((H8 & (S0 & S1 & S2)) & Hb). split; [split; [exact H8|]|].
- split; [exact S0|]. split; [exact S1|]. intros a Ha. destruct (S2 a Ha) as (Hw & b & Hr).
  split.
  + change (writable_at tfibsegs M' a). change (writable_at tfibsegs M a) in Hw.
    exact (pim_eqon_wrat M M' a ltac:(eapply pim_eqon_sub; [exact E | lia | lia]) Hw).
  + exists b. change (mbyte tfibsegs M' a = Some b). change (mbyte tfibsegs M a = Some b) in Hr.
    unfold mbyte in *. rewrite E by lia. exact Hr.
- apply (pim_eqon_bytes M M' v); [|exact Hb]. rewrite repeat_length. exact E.
Qed.
Lemma pim_eqon_RA : forall H H' m m' x n,
  (forall a, x <= a < x + n ->
     mrestrict H' m' (Z_to_bv 64 (shadow_of_addr SHADOW_OFF a)) = mrestrict H m (Z_to_bv 64 (shadow_of_addr SHADOW_OFF a))) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF x n -> range_addressable (aview tfibsegs H' m') SHADOW_OFF x n.
Proof.
intros H H' m m' x n E R y Hy. destruct (R y Hy) as (s & Es & Ok). exists s. split; [|exact Ok].
rewrite <- Es. unfold aview, mbyte. rewrite (E y Hy). reflexivity.
Qed.
(* fuzz/alloc.c's statics are image bytes (grow walk's fs_pstat_img) *)
Lemma pim_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a ((lo & hi) & Hin & Ha). cbn [fst snd] in Ha.
assert (HB : forall lo hi, In (lo, hi) FS_PSTAT_FP ->
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true).
{ intros lo' hi' H. unfold FS_PSTAT_FP in H. cbn [In] in H.
  repeat (destruct H as [H|H]; [injection H as <- <-; vm_compute; reflexivity|]); destruct H. }
apply HB in Hin. apply existsb_exists in Hin as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.
(* fs_glob reads only the four statics *)
Lemma pim_glob_eqon : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> mrestrict (w_H W') m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv. apply (pim_eqon_val (mrestrict (w_H W) m) (mrestrict (w_H W') m') g 8 v); [|exact Hv].
  intros a Ha. apply Hk. exists (g, g + 8). split; [exact Hg | cbn [fst snd]; lia]. }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [right; left; reflexivity | exact G1]|]. split; [apply VB; [right; right; left; reflexivity | exact G2]|].
split; [apply VB; [right; right; right; left; reflexivity | exact G3]|]. split; [apply VB; [left; reflexivity | exact G4]|].
exact R.
Qed.
(* ... through any change that keeps the four cells' views (a Theorem Labs lane's crcs_glob_aview) *)
Lemma pim_glob_aview : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hkk.
  assert (Hin : inFP FS_PSTAT_FP (g + Z.of_nat k)) by (exists (g, g + 8); split; [exact Hg | cbn [fst snd]; lia]).
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m' (g + Z.of_nat k) (Hk _ Hin)).
  exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [right; left; reflexivity | exact G1]|]. split; [apply VB; [right; right; left; reflexivity | exact G2]|].
split; [apply VB; [right; right; right; left; reflexivity | exact G3]|]. split; [apply VB; [left; reflexivity | exact G4]|].
exact R.
Qed.
Lemma pim_inFP_nil : forall a, ~ inFP [] a.
Proof. intros a (r & Hr & _). destruct Hr. Qed.
Lemma pim_bad_next_le : forall fp top nfp, nfp <= fp -> bad_next fp top nfp = true.
Proof. intros fp top nfp H. unfold bad_next. replace (nfp <=? fp) with true by (symmetry; apply Z.leb_le; lia). reflexivity. Qed.
(* a restricted-memory agreement is a view agreement, across worlds *)
Lemma pim_aview_eq2 : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H' m' a = aview tfibsegs H m a.
Proof. intros H H' m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma pim_aview_nonneg : forall H m a z, aview tfibsegs H m a = Some z -> 0 <= z.
Proof.
intros H m a z E. unfold aview in E. destruct (mbyte tfibsegs (mrestrict H m) a) as [b|]; [|discriminate].
cbn in E. injection E as <-. pose proof (bv_unsigned_in_range 8 b). lia.
Qed.
(* ---- small transports ---- *)
Lemma pim_mb_of_mr : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof. intros H H' m m' a E. unfold mbyte. rewrite E. reflexivity. Qed.
Lemma pim_val_mb : forall (M M' : word -> option byte) a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> mbyte tfibsegs M' (a + i) = mbyte tfibsegs M (a + i)) ->
  val_mem tfibsegs M a n v -> val_mem tfibsegs M' a n v.
Proof. intros M M' a n v E V j Hj. rewrite (E (Z.of_nat j) ltac:(lia)). exact (V j Hj). Qed.
(* one byte read off a memory as a val_mem of width 1 (image A's walk, a working branch 00c6d1886e6
   lib/A/FSH_parse_value.v pv_val1) *)
Lemma pim_val1 : forall (m : word -> option byte) a (b : byte), mbyte tfibsegs m a = Some b ->
  val_mem tfibsegs m a 1 (bv_unsigned b).
Proof.
intros m a b H k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
unfold YO0f.le_byte. cbn -[Z.modulo Z.shiftr Z.pow]. rewrite ?Z.shiftr_0_r, ?Z.mod_small by lia.
symmetry. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hr.
Qed.
(* the text byte at x, read off pj_in_ok's `bytes_at text tb` *)
Lemma pim_byte_tb : forall (m : word -> option byte) q text len p0 d (tb : list byte) x b,
  PjIn.pj_in_ok tfibsegs m q text len p0 d tb -> text <= x -> nth_error tb (Z.to_nat (x - text)) = Some b ->
  val_mem tfibsegs m x 1 (bv_unsigned b).
Proof.
intros m q text len p0 d tb x b HIN Hx Hb.
destruct HIN as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (H0 & H1 & HB) & _).
assert (Hlt : (Z.to_nat (x - text) < length tb)%nat) by (apply nth_error_Some; rewrite Hb; discriminate).
pose proof (HB _ Hlt) as E. rewrite Hb in E.
replace (text + Z.of_nat (Z.to_nat (x - text))) with x in E by lia.
apply pim_val1. exact E.
Qed.
(* the read-only view is a property of the image bytes only *)
Lemma pim_ro_keep : forall B (rd rd' : reader), arodata_okP tfibsegs FS_RLO FS_RHI B rd ->
  (forall a, in_roP tfibsegs FS_RLO FS_RHI a -> rd' a = rd a) -> arodata_okP tfibsegs FS_RLO FS_RHI B rd'.
Proof. intros B rd rd' H E a Ha Ho He. rewrite (E a Ha). exact (H a Ha Ho He). Qed.

(* ---- NEW: the chain every callee's fpreU reads at a parse_items call. s0 = q + 16 (0x84ef0, never written again), so
   the record at q + 16 is (q + 16, the word at q + 8 = in->end, the word at q = in->p); in->p is a text pointer below
   q + 16, so bad_next stops the chain there; if q + 16 is too near the stack top the chain is empty. ---- *)
Lemma pim_chain_q16 : forall ly (rd : reader) sp q e p,
  rdword rd (q + 8) = Some e -> rdword rd q = Some p -> 4096 <= e -> p <= q + 16 -> q mod 8 = 0 -> sp <= q ->
  exists ch, achain ly rd sp (q + 16) ch.
Proof.
intros ly rd sp q e p H8 H0 He Hp Hq8 Hsp.
assert (Hm : (q + 16) mod 8 = 0) by (replace (q + 16) with (q + 2 * 8) by lia; rewrite Z_mod_plus_full; exact Hq8).
destruct (Z_lt_le_dec (q + 16) (ly_top ly - 16)) as [Ht|Ht].
- exists [(q + 16, e, p)]. right. split; [lia|]. split; [exact Ht|]. split; [exact Hm|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact Hm|].
    split; [replace (q + 16 - 8) with (q + 8) by lia; exact H8|].
    split; [replace (q + 16 - 16) with q by lia; exact H0|]. split; [exact He|].
    rewrite (pim_bad_next_le (q + 16) (ly_top ly) p Hp). reflexivity.
  + constructor; [cbn [fst]; lia | constructor].
- exists []. left. split; [right; left; lia | reflexivity].
Qed.
End M.

(* ================= image-B facts along the walk's journal (copied, see the header) ================= *)
Section C. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* image bytes are no user-poisoned shadow bytes (a Theorem Labs lane's crcs_aview_low) *)
Lemma pim_aview_low : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha. apply (aview_at tfibsegs). apply unpoison_out.
rewrite (wz a ltac:(unfold SHADOW_OFF in Ha; lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption). lia.
Qed.
Lemma pim_ot16 : forall STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k,
  ajournal tfibsegs B STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k -> ot mod 16 = 0.
Proof.
intros STK ot FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _). exact (proj1 Hstk).
Qed.
Lemma pim_rdword_U : forall ly S U (W : world tfibsegs) m md a, ARU tfibsegs B ly S U W m md ->
  kHighMemBeg <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs (w_H W) (unpoison U m)) a = rdword (aview tfibsegs (w_H W) m) a.
Proof.
intros ly S U W m md a HU H1 H2. apply rdword_ext. intros i Hi.
apply (fsw_aview_unpoison_high B ly S U W m md (a + i) HU). lia.
Qed.
(* ---- where v lies at any point of the walk: in a live block that stays live (its head is off the footprint, which
   holds v's 56 bytes and the statics only) or in a frame of the entry frames; its shadow is addressable ---- *)
Lemma pim_v_place : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Wc memc mdc kk v,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc memc mdc kk ->
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v ->
  (exists b m, In (b, m) (ablocks B ly S) /\ In (b, m) (ablocks B lyc Sc) /\ b + HEAD <= v /\ v + 56 <= b + req_size m) \/
  (exists cid pos', In (cid, pos') (frames S) /\ 0 <= cid /\ frame_addr lyc cid pos' = frame_addr ly cid pos' /\
     frame_addr ly cid pos' mod 8 = 0 /\ frame_addr ly cid pos' <= v /\ v + 56 <= frame_addr ly cid pos' + fs_frame_bytes cid).
Proof.
intros STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v HJ HU HPO.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hgone & _).
destruct (al_layout tfibsegs B LAWS ly S W (unpoison U mem) md lyc HAR Hly) as (_ & HFA & _).
destruct HPO as [[((cid & pos' & Hf & Hc & H8 & H1 & H2) & _)|((b & m & Hb & H1 & H2) & _)] _].
- right. exists cid, pos'. split; [exact Hf|]. split; [exact Hc|]. split; [apply HFA|]. split; [exact H8|]. lia.
- left. exists b, m. split; [exact Hb|]. split; [|lia].
  assert (DEC : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  destruct (in_dec DEC (b, m) (ablocks B lyc Sc)) as [Hin|Hnin]; [exact Hin|exfalso].
  pose proof (Hgone b m 0 Hb Hnin ltac:(unfold HEAD in H1; lia)) as (r & Hr & Ha). rewrite Z.add_0_r in Ha.
  apply in_app_or in Hr as [Hr|Hr].
  + cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. unfold HEAD in H1. lia.
  + exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m b HAR Hb ltac:(unfold HEAD in H1; lia)
      (pim_pstat_img b (ex_intro _ r (conj Hr Ha)))).
Qed.
Lemma pim_v_awr : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Wc memc mdc kk v STKx sp0 a,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc memc mdc kk ->
  ARU tfibsegs B ly S U W mem md -> pobj tfibsegs B ly S W mem v -> in_zr a (v, 56) ->
  awr_byte tfibsegs B STKx sp0 ([(v, v + 56)] ++ FS_PSTAT_FP) (ablocks B ly S) (ablocks B lyc Sc) lyc own (frames S) a.
Proof.
intros STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v STKx sp0 a HJ HU HPO Ha. unfold in_zr in Ha. cbn [fst snd] in Ha.
assert (HFP : inFP ([(v, v + 56)] ++ FS_PSTAT_FP) a) by (exists (v, v + 56); split; [left; reflexivity | cbn [fst snd]; lia]).
destruct (pim_v_place STK ot ly S U W mem md own lyc Sc Wc memc mdc kk v HJ HU HPO)
  as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
- left. right. left. split; [exact HFP|]. exists b, m. split; [exact Hbc | unfold HEAD in H1; lia].
- right. right. split; [exact HFP|]. exists cid, pos'. split; [exact Hf|]. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite EF. lia.
Qed.
(* the heads of U are no shadow byte's granule of a byte of a frame *)
Lemma pim_ush_frame : forall ly S U (W : world tfibsegs) mem md cid pos x,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros ly S U W mem md cid pos x HU FH Hf Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hf) as (F1 & _).
apply fsw_head_ush_out; [lia|]. intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & M16).
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m HAR Hm) as (Q16 & _).
split; [exact E16|].
split; [apply Z.mod_divide in Q16 as [z Hz]; [|lia]; rewrite Hz; replace (z * 16) with ((z * 2) * 8) by lia; apply Z_mod_mult|].
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md (fst r) m cid pos HAR Hm Hf) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma pim_ra_v : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Uc Wc memc mdc kk v,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc
    (unpoison Uc memc) mdc kk ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B lyc Sc Uc ->
  pobj tfibsegs B ly S W mem v -> range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF v 56.
Proof.
intros STK ot ly S U W mem md own lyc Sc Uc Wc memc mdc kk v HJ HU HUc FH FHc HPO.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof (ARU_AR tfibsegs B ly S U W mem md HU) as HAR.
pose proof (ARU_AR tfibsegs B lyc Sc Uc Wc memc mdc HUc) as HARc.
pose proof asan_consts as (C1 & _).
assert (HRA0 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56)
  by (destruct HPO as [[(_ & _ & R)|(_ & _ & R)] _]; exact R).
destruct (pim_v_place STK ot ly S U W mem md own lyc Sc Wc (unpoison Uc memc) mdc kk v HJ HU HPO)
  as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
- exact (fsw_block_body_addressable B lyc Sc Uc Wc memc mdc b m v 56 HUc FHc Hbc ltac:(unfold HEAD in H1; lia) ltac:(lia) H2).
- pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & Hfrm & _).
  assert (Hfc : In (cid, pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hf).
  destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR Hf) as (Fb1 & Fb2 & Fapp).
  destruct (al_frames tfibsegs B LAWS ly S W (unpoison U mem) md cid pos' HAR Hf) as (F32 & _).
  pose proof (YG0s.frame_facts B ly S _ cid pos' (proj1 HAR) Hf) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & B64 & _).
  intros x Hx. destruct (HRA0 x Hx) as (s & Es & Hok). exists s. split; [|exact Hok]. rewrite <- Es.
  assert (SR : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 2 ^ 44)
    by (unfold shadow_of_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
  assert (S64 : 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64) by (unfold SHADOW_OFF in SR |- *; lia).
  assert (E1 : aview tfibsegs (w_H Wc) (unpoison Uc memc) (shadow_of_addr SHADOW_OFF x) =
               aview tfibsegs (w_H W) (unpoison U mem) (shadow_of_addr SHADOW_OFF x)).
  { apply (Hfrm cid pos' _ Hf).
    - right. assert (Hxf : frame_addr ly cid pos' <= x < frame_addr ly cid pos' + fs_frame_bytes cid) by lia.
      unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
      apply Z.mod_divide in F32 as [a8 Ha8]; [|lia]. apply Z.mod_divide in B64 as [b8 Hb8]; [|lia].
      rewrite Ha8, Hb8 in Hxf |- *. Z.div_mod_to_equations. lia.
    - intros (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr].
      + cbn [In] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
        unfold in_app, kLowShadowBeg, ASAN_CEIL, kHighMemBeg in Fapp. unfold SHADOW_OFF in *. lia.
      + pose proof (fs_segs_img _ (pim_pstat_img _ (ex_intro _ r (conj Hr Ha)))) as Hi.
        unfold FS_IMG_END, SHADOW_OFF in *. lia. }
  rewrite <- (aview_unpoison_out tfibsegs (w_H Wc) Uc memc (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ S64); rewrite <- EF in H1, H2;
        exact (pim_ush_frame lyc Sc Uc Wc memc mdc cid pos' x HUc FHc Hfc ltac:(lia))).
  rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem (shadow_of_addr SHADOW_OFF x))
    by (rewrite (wz _ S64); exact (pim_ush_frame ly S U W mem md cid pos' x HU FH Hf ltac:(lia))).
  exact E1.
Qed.
(* ---- NEW: v's pobj at any point of the walk: the placement and the shadow along the journal (pim_v_place, pim_ra_v),
   the alignment from the entry's, the writability given ---- *)
Lemma pim_pobj_mk : forall STK ot ly S U (W : world tfibsegs) mem md own lyc Sc Uc Wc memc mdc kk v,
  ajournal tfibsegs B STK ot ([(v, v + 56)] ++ FS_PSTAT_FP) ly S W (unpoison U mem) md own lyc Sc Wc
    (unpoison Uc memc) mdc kk ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  FSupoisonU.fs_heads B ly S U -> FSupoisonU.fs_heads B lyc Sc Uc ->
  pobj tfibsegs B ly S W mem v ->
  (forall i, 0 <= i < 56 -> writable_at tfibsegs (mrestrict (w_H Wc) memc) (v + i)) ->
  pobj tfibsegs B lyc Sc Wc memc v.
Proof.
intros STK ot ly S U W mem md own lyc Sc Uc Wc memc mdc kk v HJ HU HUc FH FHc HPO HWR.
assert (Hv8 : v mod 8 = 0) by (destruct HPO as [[(_ & Hm & _)|(_ & Hm & _)] _]; exact Hm).
pose proof (pim_ra_v STK ot ly S U W mem md own lyc Sc Uc Wc memc mdc kk v HJ HU HUc FH FHc HPO) as RA.
split; [|exact HWR].
destruct (pim_v_place STK ot ly S U W mem md own lyc Sc Wc (unpoison Uc memc) mdc kk v HJ HU HPO)
  as [(b & m & Hb & Hbc & H1 & H2)|(cid & pos' & Hf & Hc & EF & H8 & H1 & H2)].
- right. split; [exists b, m; split; [exact Hbc | split; [exact H1 | exact H2]]|]. split; [exact Hv8 | exact RA].
- left. pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
  split; [|split; [exact Hv8 | exact RA]].
  exists cid, pos'. split; [rewrite Hfrs; apply in_or_app; right; exact Hf|]. split; [exact Hc|].
  rewrite EF. split; [exact H8|]. split; [exact H1 | exact H2].
Qed.
End C.
