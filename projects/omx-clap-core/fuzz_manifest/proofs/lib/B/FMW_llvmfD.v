(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMW_llvmfD.v at a working branch 79d8c0f1b8f, relocated A->B:
   imports per a Theorem Labs lane's core rule (a working branch 305d8b1527f: lib.A AXxx -> lib.ReusableB YXxx when listed in its
   ReusableB list, other lib.A -> lib.B, FMupoison stays lib.A); every image numeral re-derived from B's listing
   (fuzz_manifest.objdump.txt / nm.txt of the asan-ubsan pin). *)
(* LLVMFuzzerTestOneInput walk: facts about the input's windows (FMW_llvmfP.v lx_uw, lx_tw, lx_ub, lx_tb) at any state
   whose AR keeps the input block and its bytes: what memchr, check_no_overread and the two memcpy calls ask. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC5d YCbp YC20.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0l YCej.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YE2k YCfn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMW_kit FMW_K FMW_kitS FMW_seg FMW_llvmf0 FMW_llvmfP.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- pure facts ---- *)
Lemma lf_find0_none : forall l, ManifestModel.find_idx (fun c => c =? 0) l = None -> Forall (fun c => c <> 0) l.
Proof.
induction l as [|x l IH]; cbn [ManifestModel.find_idx]; intros H; [constructor|].
revert H. destruct (Z.eqb_spec x 0) as [Hx|Hx]; intros H; [discriminate H|].
constructor; [exact Hx|]. apply IH. revert H.
destruct (ManifestModel.find_idx (fun c => c =? 0) l); intros H; [discriminate H | reflexivity].
Qed.
Lemma lf_find0_some : forall l j, ManifestModel.find_idx (fun c => c =? 0) l = Some j ->
  (j < length l)%nat /\ Forall (fun c => c <> 0) (firstn j l).
Proof.
induction l as [|x l IH]; cbn [ManifestModel.find_idx]; intros j H; [discriminate H|].
revert H. destruct (Z.eqb_spec x 0) as [Hx|Hx]; intros H.
- injection H as <-. cbn [length firstn]. split; [lia | constructor].
- revert H. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [j'|]; intros H; [|discriminate H].
  cbn in H. injection H as <-. destruct (IH j' eq_refl) as [H1 H2]. cbn [length firstn].
  split; [lia | constructor; assumption].
Qed.
Lemma lf_cut_nz : forall l, Forall (fun c => c <> 0) (lf_cut l).
Proof.
intros l. unfold lf_cut. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [j|] eqn:E.
- exact (proj2 (lf_find0_some l j E)).
- exact (lf_find0_none l E).
Qed.
Lemma lf_cut_prefix : forall l, lf_cut l = firstn (length (lf_cut l)) l.
Proof.
intros l. unfold lf_cut. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [j|] eqn:E.
- destruct (lf_find0_some l j E) as [H1 _]. rewrite length_firstn. replace (Nat.min j (length l)) with j by lia. reflexivity.
- symmetry. apply firstn_all.
Qed.
Lemma lf_cut_len : forall l, (length (lf_cut l) <= length l)%nat.
Proof.
intros l. unfold lf_cut. destruct (ManifestModel.find_idx (fun c => c =? 0) l); [rewrite length_firstn|]; lia.
Qed.
(* memchr (x, 0, len l)'s answer v (FMH_Rt.v amemchr_realizes) gives fuzz_strnlen: v = 0 -> len l, else v - x *)
Lemma lf_memchr_len : forall (l : list Z) x v, 4096 <= x ->
  match ManifestModel.find_idx (fun c => c =? 0) l with None => v = 0 | Some j => v = x + Z.of_nat j end ->
  (v = 0 /\ lf_cut l = l) \/ (v <> 0 /\ Z.of_nat (length (lf_cut l)) = v - x).
Proof.
intros l x v Hx H. unfold lf_cut. revert H. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [j|] eqn:E; intros H.
- right. destruct (lf_find0_some l j E) as [H1 _]. rewrite length_firstn. split; lia.
- left. split; [exact H | reflexivity].
Qed.
Lemma lf_mchr_len_bounds : forall l, 0 <= mchr_len l <= Z.of_nat (length l) /\ (0 < Z.of_nat (length l) -> 0 < mchr_len l).
Proof.
intros l. unfold mchr_len. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [j|] eqn:E.
- destruct (lf_find0_some l j E) as [H1 _]. lia.
- lia.
Qed.
Lemma lf_rounded_ge : forall n, n <= rounded_size n.
Proof.
intros n. unfold rounded_size, round_up.
pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : asyms.

(* a window of a live block, with the 8 bytes after it (a string's word reads; cstr_ok, src_rd, memchr): the chunk's
   extent covers the block and its right part, and lies below alloc_ceiling in one memory band *)
Lemma lf_blk_end8 : forall ly S (W : world tfibsegs) mem md b m a len,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= a -> 0 <= len -> a + len <= b + m ->
  a + len + 8 <= alloc_ceiling /\ amem_range a (len + 8).
Proof.
intros ly S W mem md b m a len HAR Hin H1 H2 H3.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HAR as (M & _).
apply In_ablocks in Hin as (k & Hk & Hst & Hu & Hn).
pose proof (chunk_facts B ly S _ k M Hk) as CF. unfold cfacts in CF.
destruct CF as (Happ & Hce & Hb16 & Huser & Hrz & Hrz16 & Hreq & Hrzx & Hbeg).
pose proof (am_layout B ly S _ M) as LO.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite Hu in Huser. rewrite Hn in Hrzx, Hreq.
unfold ASAN_CEIL in Hce. unfold in_app, ASAN_CEIL in Happ.
unfold amem_range. unfold kLowMemEnd, kHighMemBeg, kHighMemEnd, kLowShadowBeg in *.
revert Hbeg. destruct (ck_beg k) as [|off|r o|c p]; intros Hbeg; try (destruct Hbeg; fail).
- cbv zeta in Hbeg. destruct Hbeg as (Hc & Hfp & Hcc & Hext & Hbase & Hx0 & Hxm & Hxs & Hal).
  pose proof (region_in_prim ly (prim_class off) LO ltac:(lia)) as (R1 & R2 & R3 & R4 & R5).
  unfold ASAN_CEIL, kHighMemBeg in R4, R5. unfold kFreeArrayOffset in Hal.
  rewrite Hext in Hrzx. rewrite Hbase in Huser. lia.
- destruct Hbeg as (Ho & Hfp & Hbase & Hext & _).
  rewrite Hn in Hfp, Hext.
  pose proof (secondary_geometry m ltac:(lia) Hfp) as (S1 & S2 & S3 & S4 & S5 & S6).
  unfold needed_primary in S2. pose proof (lf_rounded_ge m) as Hr.
  pose proof (rz_size_bounds m) as [Z1 Z2]. unfold ck_rz in Huser. rewrite Hn in Huser.
  rewrite Hext in Happ, Hce. unfold kPage in *. lia.
Qed.

(* k, the windows and their lengths *)
Lemma lx_ranges : forall cx, lf_base B cx ->
  0 <= lx_k cx <= 255 /\ 0 <= lx_s6 cx <= 1 /\ lx_s6 cx + lx_k cx <= lx_n cx /\ lx_n cx < 2 ^ 26 /\
  (lx_n cx = 0 -> lx_s6 cx = 0 /\ lx_k cx = 0 /\ lx_p cx = A_EMPTY) /\
  (0 < lx_n cx -> lx_s6 cx = 1 /\ lx_k cx = Z.min (nth 0 (lx_dl cx) 0) (lx_n cx - 1)) /\
  Z.of_nat (length (lx_uw cx)) = lx_k cx /\ Z.of_nat (length (lx_tw cx)) = lx_n cx - lx_s6 cx - lx_k cx /\
  0 <= lx_un cx <= lx_k cx /\ 0 <= lx_tn cx <= lx_n cx - lx_s6 cx - lx_k cx /\ (length (lx_ub cx) <= 255)%nat.
Proof.
intros cx HB. pose proof HB as (HAP & Hra & H10 & H11 & Hpn & Hg & _).
assert (Hdl : Z.of_nat (length (lx_dl cx)) = lx_n cx) by (unfold lx_dl, lx_n; rewrite length_map; reflexivity).
assert (Hks : (lx_n cx = 0 /\ lx_s6 cx = 0 /\ lx_k cx = 0 /\ lx_p cx = A_EMPTY) \/
  (0 < lx_n cx < 2 ^ 26 /\ lx_s6 cx = 1 /\ lx_k cx = Z.min (nth 0 (lx_dl cx) 0) (lx_n cx - 1) /\
   0 <= nth 0 (lx_dl cx) 0 < 256)).
{ unfold lx_s6, lx_k. destruct Hpn as [[Hn Hp] | [Hn Hin]].
  - left. rewrite Hn. cbn [Z.eqb]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | exact Hp].
  - right. replace (lx_n cx =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    split; [exact Hn|]. split; [reflexivity|]. split; [reflexivity|].
    destruct (Hg 0%nat ltac:(lia)) as [_ R]. exact R. }
assert (Lu : Z.of_nat (length (lx_uw cx)) = lx_k cx).
{ unfold lx_uw. rewrite length_firstn, length_skipn. destruct Hks as [(E1 & E2 & E3 & _) | (E1 & E2 & E3 & E4)]; lia. }
assert (Lt : Z.of_nat (length (lx_tw cx)) = lx_n cx - lx_s6 cx - lx_k cx).
{ unfold lx_tw. rewrite length_skipn. destruct Hks as [(E1 & E2 & E3 & _) | (E1 & E2 & E3 & E4)]; lia. }
pose proof (lf_cut_len (lx_uw cx)) as Cu. pose proof (lf_cut_len (lx_tw cx)) as Ct.
fold (lx_ub cx) in Cu. fold (lx_tb cx) in Ct. unfold lx_un, lx_tn.
destruct Hks as [(E1 & E2 & E3 & E4) | (E1 & E2 & E3 & E4)].
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros _; split; [exact E2 | split; [exact E3 | exact E4]]|]. split; [intros; lia|].
  split; [exact Lu|]. split; [exact Lt|]. split; [lia|]. split; lia.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [intros; lia|]. split; [intros _; split; [exact E2 | exact E3]|].
  split; [exact Lu|]. split; [exact Lt|]. split; [lia|]. split; lia.
Qed.

(* a window of the input at a state whose AR keeps the input block (n > 0) and the input bytes *)
Lemma lf_window : forall cx ly' S' (W' : world tfibsegs) mem' md' o len,
  lf_base B cx -> AR tfibsegs B ly' S' W' mem' md' -> lf_inkept cx W' mem' ->
  (0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly' S')) ->
  0 <= o -> 0 <= len -> o + len <= lx_n cx ->
  bytes_at tfibsegs W' mem' (lx_p cx + o) (firstn (Z.to_nat len) (skipn (Z.to_nat o) (lx_dl cx))) /\
  4096 <= lx_p cx + o /\ lx_p cx + o + len + 8 <= alloc_ceiling /\ amem_range (lx_p cx + o) (len + 8) /\
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF (lx_p cx + o) len /\
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W') mem') (lx_p cx + o) len).
Proof.
intros cx ly' S' W' mem' md' o len HB HAR Hk Hin Ho Hl Hol.
pose proof HB as (HAP & Hra & H10 & H11 & Hpn & Hg & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hdl : Z.of_nat (length (lx_dl cx)) = lx_n cx) by (unfold lx_dl, lx_n; rewrite length_map; reflexivity).
split.
{ unfold bytes_at.
  pose proof Hg as Hg0. rewrite <- (firstn_skipn (Z.to_nat o) (lx_dl cx)) in Hg0.
  apply (proj1 (garr8_app tfibsegs _ _ _ _)) in Hg0 as [_ Hg1].
  rewrite <- (firstn_skipn (Z.to_nat len) (skipn (Z.to_nat o) (lx_dl cx))) in Hg1.
  apply (proj1 (garr8_app tfibsegs _ _ _ _)) in Hg1 as [Hg2 _].
  rewrite length_firstn in Hg2.
  replace (lx_p cx + Z.of_nat (Nat.min (Z.to_nat o) (length (lx_dl cx)))) with (lx_p cx + o) in Hg2 by lia.
  apply (garr8_frame tfibsegs _ _ _ _ Hg2). intros a Ha.
  rewrite length_firstn, length_skipn in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (lx_p cx + (a - lx_p cx)) by lia. apply Hk. lia. }
destruct (Z.eq_dec (lx_n cx) 0) as [E0 | E0].
- destruct Hpn as [[_ Hp] | [Hn _]]; [|lia].
  assert (o = 0) by lia. assert (len = 0) by lia. subst o len. rewrite Hp. unfold A_EMPTY, amem_range, kLowMemEnd.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [unfold range_addressable; intros x Hx; lia | intros H; lia].
- assert (Hin' : In (lx_p cx, lx_n cx) (ablocks B ly' S')) by (apply Hin; lia).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin') as (_ & H4096 & _).
  destruct (lf_blk_end8 ly' S' W' mem' md' (lx_p cx) (lx_n cx) (lx_p cx + o) len HAR Hin' ltac:(lia) Hl ltac:(lia))
    as [E8 Am].
  assert (Hrq : req_size (lx_n cx) = lx_n cx) by (unfold req_size; destruct (Z.eqb_spec (lx_n cx) 0); lia).
  split; [lia|]. split; [exact E8|]. split; [exact Am|]. split.
  + apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' (lx_p cx) (lx_n cx));
      [exact HAR | exact Hin' | lia | rewrite Hrq; lia].
  + intros Hlen. apply (shadow_hull_vis_of_block tfibsegs B LAWS ly' S' W' mem' md' (lx_p cx) (lx_n cx));
      [exact HAR | exact Hin' | lia | rewrite Hrq; lia | exact Hlen].
Qed.

(* memchr's premises over the two windows (FMH_Rt.v amemchr_realizes) *)
Lemma lf_memchr_pre : forall cx ly' S' (W' : world tfibsegs) mem' md' x l,
  lf_base B cx -> AR tfibsegs B ly' S' W' mem' md' -> lf_inkept cx W' mem' ->
  (0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly' S')) ->
  (x = lx_uri cx /\ l = lx_uw cx) \/ (x = lx_text cx /\ l = lx_tw cx) ->
  bytes_at tfibsegs W' mem' x l /\ 4096 <= x /\ x + Z.of_nat (length l) + 8 <= alloc_ceiling /\
  amem_range x (Z.of_nat (length l) + 8) /\ 0 <= Z.of_nat (length l) < 2 ^ 32 /\
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF x (mchr_len l) /\
  (0 < Z.of_nat (length l) -> shadow_hull_vis (aview tfibsegs (w_H W') mem') x (mchr_len l)).
Proof.
intros cx ly' S' W' mem' md' x l HB HAR Hk Hin Hxl.
pose proof (lx_ranges cx HB) as (Hk0 & Hs6 & Hsk & Hn26 & Hn0 & Hnp & Lu & Lt & Hun & Htn & Hub).
assert (Hw : exists o len, x = lx_p cx + o /\ l = firstn (Z.to_nat len) (skipn (Z.to_nat o) (lx_dl cx)) /\
  0 <= o /\ 0 <= len /\ o + len <= lx_n cx /\ Z.of_nat (length l) = len).
{ destruct Hxl as [[-> ->] | [-> ->]].
  - exists (lx_s6 cx), (lx_k cx). split; [reflexivity|]. split; [reflexivity|]. lia.
  - exists (lx_s6 cx + lx_k cx), (lx_n cx - lx_s6 cx - lx_k cx). unfold lx_text, lx_uri.
    split; [lia|]. split; [|lia].
    symmetry. apply firstn_all2. change (skipn (Z.to_nat (lx_s6 cx + lx_k cx)) (lx_dl cx)) with (lx_tw cx). lia. }
destruct Hw as (o & len & -> & El & Ho & Hl & Hol & Hlen).
destruct (lf_window cx ly' S' W' mem' md' o len HB HAR Hk Hin Ho Hl Hol) as (Hby & H4 & H8 & Am & Ra & Sh).
pose proof (lf_mchr_len_bounds l) as [Mb Mp].
rewrite Hlen in Mb, Mp |- *. rewrite <- El in Hby.
split; [exact Hby|]. split; [exact H4|]. split; [exact H8|]. split; [exact Am|]. split; [lia|]. split.
- unfold range_addressable. intros y Hy. apply Ra. lia.
- intros Hpos. specialize (Mp Hpos).
  apply (shadow_hull_vis_sub _ (lx_p cx + o) len); [apply Sh; lia | lia | lia | lia].
Qed.

(* check_no_overread's window premises (FMH_Fn.v check_no_overread_spec), and the memcpy sources *)
Lemma lf_src_rd : forall cx ly' S' (W' : world tfibsegs) mem' md',
  lf_base B cx -> AR tfibsegs B ly' S' W' mem' md' -> lf_inkept cx W' mem' ->
  (0 < lx_n cx -> In (lx_p cx, lx_n cx) (ablocks B ly' S')) ->
  src_rd tfibsegs W' mem' (lx_uri cx) (lx_ub cx) /\ src_rd tfibsegs W' mem' (lx_text cx) (lx_tb cx) /\
  Forall (fun c => c <> 0) (lx_ub cx) /\ Forall (fun c => c <> 0) (lx_tb cx) /\
  (lx_ub cx = [] \/ exists b m, In (b, m) (ablocks B ly' S') /\ b <= lx_uri cx /\
     lx_uri cx + Z.of_nat (length (lx_ub cx)) <= b + m) /\
  (lx_tb cx = [] \/ exists b m, In (b, m) (ablocks B ly' S') /\ b <= lx_text cx /\
     lx_text cx + Z.of_nat (length (lx_tb cx)) <= b + m) /\
  (0 < lx_un cx -> lx_p cx <= lx_uri cx /\ lx_uri cx + lx_un cx <= lx_p cx + lx_n cx) /\
  (0 < lx_tn cx -> lx_p cx <= lx_text cx /\ lx_text cx + lx_tn cx <= lx_p cx + lx_n cx).
Proof.
intros cx ly' S' W' mem' md' HB HAR Hk Hin.
pose proof (lx_ranges cx HB) as (Hk0 & Hs6 & Hsk & Hn26 & Hn0 & Hnp & Lu & Lt & Hun & Htn & Hub).
assert (Eub : lx_ub cx = firstn (length (lx_ub cx)) (skipn (Z.to_nat (lx_s6 cx)) (lx_dl cx))).
{ pose proof (lf_cut_prefix (lx_uw cx)) as E. fold (lx_ub cx) in E.
  pose proof (lf_cut_len (lx_uw cx)) as L. fold (lx_ub cx) in L.
  set (m := length (lx_ub cx)) in *. rewrite E at 1. unfold lx_uw. rewrite firstn_firstn. f_equal. lia. }
assert (Etb : lx_tb cx = firstn (length (lx_tb cx)) (skipn (Z.to_nat (lx_s6 cx + lx_k cx)) (lx_dl cx))).
{ pose proof (lf_cut_prefix (lx_tw cx)) as E. fold (lx_tb cx) in E. exact E. }
unfold lx_un, lx_tn in *.
pose proof (lf_window cx ly' S' W' mem' md' (lx_s6 cx) (Z.of_nat (length (lx_ub cx))) HB HAR Hk Hin
  ltac:(lia) ltac:(lia) ltac:(lia)) as (Uby & U4 & U8 & Uam & Ura & Ush).
pose proof (lf_window cx ly' S' W' mem' md' (lx_s6 cx + lx_k cx) (Z.of_nat (length (lx_tb cx))) HB HAR Hk Hin
  ltac:(lia) ltac:(lia) ltac:(lia)) as (Tby & T4 & T8 & Tam & Tra & Tsh).
rewrite Nat2Z.id, <- Eub in Uby. rewrite Nat2Z.id, <- Etb in Tby.
replace (lx_p cx + lx_s6 cx) with (lx_uri cx) in Uby, U4, U8, Uam, Ura, Ush by reflexivity.
replace (lx_p cx + (lx_s6 cx + lx_k cx)) with (lx_text cx) in Tby, T4, T8, Tam, Tra, Tsh
  by (unfold lx_text, lx_uri; lia).
assert (AM : forall a n, amem_range a (n + 8) -> 0 <= n -> amem_range a n) by (intros a n0 H H0; unfold amem_range in *; lia).
split.
{ unfold src_rd. split; [exact Uby|]. split; [exact U4|]. split; [exact U8|]. split; [apply AM; [exact Uam | lia]|].
  split; [exact Ura | exact Ush]. }
split.
{ unfold src_rd. split; [exact Tby|]. split; [exact T4|]. split; [exact T8|]. split; [apply AM; [exact Tam | lia]|].
  split; [exact Tra | exact Tsh]. }
split; [exact (lf_cut_nz (lx_uw cx))|]. split; [exact (lf_cut_nz (lx_tw cx))|].
split.
{ destruct (Nat.eq_dec (length (lx_ub cx)) 0) as [Z0 | Z0]; [left; apply length_zero_iff_nil; exact Z0 | right].
  exists (lx_p cx), (lx_n cx). split; [apply Hin; lia | unfold lx_uri; lia]. }
split.
{ destruct (Nat.eq_dec (length (lx_tb cx)) 0) as [Z0 | Z0]; [left; apply length_zero_iff_nil; exact Z0 | right].
  exists (lx_p cx), (lx_n cx). split; [apply Hin; lia | unfold lx_text, lx_uri; lia]. }
split; intros; unfold lx_text, lx_uri; lia.
Qed.

(* ---- strings in live blocks (the copies u and t, FMW_llvmfS3.v / FMW_llvmfS4.v) ---- *)
(* a C string inside a live block is a cstr_ok string *)
Lemma lf_cstr_ok_of_blk : forall ly S (W : world tfibsegs) mem md b m p l,
  AR tfibsegs B ly S W mem md -> In (b, m) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  cstr tfibsegs W mem p l -> cstr_ok tfibsegs W mem p l.
Proof.
intros ly S W mem md b m p l HAR Hin Hb Hbm Hc.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hm).
assert (Hm0 : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
pose proof (lf_blk_end8 ly S W mem md b m p (Z.of_nat (length l) + 1) HAR Hin Hb ltac:(lia) ltac:(lia)) as (Hc8 & Ham).
unfold MALLOC_MAX in Hm.
split; [exact Hc|].
split; [lia|]. split; [lia|]. split; [lia|].
split; [unfold amem_range in *; lia|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly S W mem md b m p _ HAR Hin Hb). rewrite Hrq. lia. }
split.
{ apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W mem md b m p _ HAR Hin Hb); [rewrite Hrq; lia | lia]. }
intros a Ha. apply (block_word_tail_vis B LAWS ly S W mem md b m HAR Hin Hm0).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
(* cstr_ok carried to a state whose AR holds the string's block and whose view agrees on the string and its NUL *)
Lemma lf_cstr_ok_view : forall ly S (W W' : world tfibsegs) mem mem' md b m p l,
  AR tfibsegs B ly S W' mem' md -> In (b, m) (ablocks B ly S) -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  cstr_ok tfibsegs W mem p l -> cstr_ok tfibsegs W' mem' p l.
Proof.
intros ly S W W' mem mem' md b m p l HAR Hin Hb Hbm HV ((Hg & Hnz) & _).
apply (lf_cstr_ok_of_blk ly S W' mem' md b m p l HAR Hin Hb Hbm).
split; [|exact Hnz].
apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
apply (mbyte_of_aview tfibsegs). apply HV. lia.
Qed.
End d.
