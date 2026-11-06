(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:133-134, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_name_seg7.v, with its module paths, module names and numbers changed; 758 of its 873 lines of code are new or changed and 976 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC8i YC1f YC8g YC44.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i YCbf YCj1 YCjr YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import ConstsViewDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
SbCh SbDec ReacBoxName ReacBoxNameCut ReacBoxNameSeg3D.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_box_name_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Definition RBN_U3PC : Z := 14700.
Definition RBN_U3RET : Z := 14768.
Definition RBN_P4PC : Z := 14804.
Definition rbn3u_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 152 208 152 168 [YP09.mkChunk 200 (CVal 8 (SLit 4))];
    YP09.mkRegion (Some 20%nat) 4 5 4 5 [];
    YP09.mkRegion (Some 18%nat) 8 11 8 11 [] ].
Definition rbn3u_facts : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
            (18%nat, mkAF 0 (2 ^ 47) 0); (20%nat, mkAF 0 (2 ^ 47) 0);
            (22%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
            (25%nat, mkAF 0 (2 ^ 47 - 2) 0); (32%nat, mkAF 1 255 0) ] [] [].
Definition ss_rbn3u : sstate := mkSS RBN_U3PC sr_atoms rbn3u_regions None rbn3u_facts.
Definition rbn3u_R25 : YP09.region :=
  YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition rbn3u_SB : Z := 0x7fff8000.
Definition rbn3u_Bx : sv := SOff 22 0.
Definition rbn3u_Bspan : Z * Z := (rbn3u_SB, rbn3u_SB + 2 ^ 44 - 1).
Definition rbn3u_SH : list shent := [mkSHE 25 0 1].

Lemma rbn3u_sh_len : forall a b c d, length (rbn_sh a b c d) = 64%nat.
Proof. intros a b c d. destruct a, b, c, d; reflexivity. Qed.
Lemma rbn3u_sh_eq : forall k, (k < 64)%nat -> ((k < 8)%nat \/ (10 < k)%nat) ->
  nth k (rbn_sh true true false false) 0 = nth k (rbn_sh true false false false) 0.
Proof.
intros k Hk Hr.
assert (Hb : forallb (fun j => implb ((j <? 8)%nat || (10 <? j)%nat)
    (nth j (rbn_sh true true false false) 0 =? nth j (rbn_sh true false false false) 0)) (seq 0 64) = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb k ltac:(apply in_seq; lia)) as Hk0.
cbv beta in Hk0.
assert (Hor : ((k <? 8)%nat || (10 <? k)%nat) = true)
  by (apply orb_true_iff; destruct Hr as [H | H]; [left | right]; apply Nat.ltb_lt; lia).
rewrite Hor in Hk0. cbn [implb] in Hk0. apply Z.eqb_eq. exact Hk0.
Qed.
Lemma rbn3u_nth0 : forall l : list Z, nth 0 (l ++ [0]) 0 = hd 0 l.
Proof. intros l. destruct l; reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma rbn3u_stem_ne : forall X, rbm_stem X <> [].
Proof.
intros X. unfold rbm_stem, bn_stem. destruct (ri_sd X) as [|c l]; [|discriminate].
unfold bn_STEM. destruct (ri_f X =? 1); [discriminate|]. destruct (ri_f X =? 2); [discriminate|].
destruct (ri_f X =? 3); discriminate.
Qed.
Definition ERB3U (regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs [Z_to_bv 64 c]).
Lemma regs_ok_ERB3U : forall regs c, regs_ok (ERB3U regs c) sr_atoms regs.
Proof.
intros regs c. unfold ERB3U. apply (regs_ok_agree 32 (Ereg regs [Z_to_bv 64 c])).
- split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity].
- vm_compute. reflexivity.
- apply regs_ok_Ereg.
Qed.
Lemma rbn3u_kept_frame : forall E rs (H : word -> bool) (m m' : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' P HF Hw a Ha Hn. apply aview_eq_of. apply HF. rewrite unsigned_lit_small by lia.
intros Hi. apply Hn. apply Hw. exact Hi.
Qed.
Lemma rbn3u_nowrange : forall E a, ~ in_wrange E [rbn3u_R25] a.
Proof.
intros E a (r & Hr & Hw). unfold rbn3u_R25 in Hr. cbn [In] in Hr.
destruct Hr as [<- | []]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; lia.
Qed.
Lemma rbn3u_aview_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. apply aview_eq_of. apply Hm. Qed.
Lemma rbn3u_apresent_mr : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, mrestrict H m' x = mrestrict H m x) -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a Hm (Ha & b & Hb). split; [exact Ha|]. exists b.
pose proof (Hm (Z_to_bv 64 a)) as Hx. unfold mrestrict in Hx. rewrite Ha in Hx. rewrite Hx. exact Hb.
Qed.
Lemma rbn3u_val_mem_mr : forall (H : word -> bool) (m m' : word -> option byte) a n v,
  (forall x, mrestrict H m' x = mrestrict H m x) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hm Hv k Hk. unfold mbyte. rewrite Hm. exact (Hv k Hk).
Qed.
Lemma rbn3u_cells_kept : forall H H' (m m' : word -> option byte) l,
  (forall a n v k, In (a, n, v) l -> 0 <= k < Z.of_nat n -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  rbn_cells (mrestrict H m) l -> rbn_cells (mrestrict H' m') l.
Proof.
intros H H' m m' l. induction l as [|[[a n] v] t IH]; cbn [rbn_cells]; intros HE HC; [exact I|].
destruct HC as [H1 H2]. split.
- apply (val_mem_kept SEGS H H' m m'); [|exact H1]. intros k Hk. exact (HE a n v k (or_introl eq_refl) Hk).
- apply IH; [|exact H2]. intros a' n' v' k Hin Hk. exact (HE a' n' v' k (or_intror Hin) Hk).
Qed.
Lemma rbn3u_cells_app : forall (m : word -> option byte) l1 l2,
  rbn_cells m (l1 ++ l2) <-> rbn_cells m l1 /\ rbn_cells m l2.
Proof.
intros m l1 l2. induction l1 as [|[[a n] v] t IH]; cbn [app rbn_cells]; [tauto|]. rewrite IH. tauto.
Qed.
Lemma rbn3u_argc_rng : forall X a n v, In (a, n, v) (rbn_argc X) ->
  rbn_A X <= a /\ a + Z.of_nat n <= rbn_A X + 64.
Proof.
intros X a n v H. unfold rbn_argc in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn3u_rw_rng : forall X pos n0 ov0 a n v, In (a, n, v) (rbn_rw X pos n0 ov0) ->
  rbn_A X + 184 <= a /\ a + Z.of_nat n <= rbn_A X + 212.
Proof.
intros X pos n0 ov0 a n v H. unfold rbn_rw in H. cbn [In] in H.
repeat (destruct H as [H | H]; [injection H as <- <- <-; lia|]). destruct H.
Qed.
Lemma rbn3u_w4_len : forall X, rbm_args X -> length (rbm_w4 X) = 4%nat.
Proof.
intros X HA. unfold rbm_args, reac_box_name_c.bn_args_ok in HA.
apply andb_prop in HA as [HA _]. apply andb_prop in HA as [HA Ho]. apply andb_prop in HA as [_ Hi].
exact (bn_w4_length _ _ Hi Ho).
Qed.
Lemma rbn3u_sh_band : forall x n j, 4096 <= x -> 0 <= n -> x + n <= alloc_ceiling -> 0 <= j < n / 8 ->
  kLowShadowBeg <= shadow_addr x + j < kHighMemBeg.
Proof.
intros x n j H1 H2 H3 H4.
pose proof (shadow_range_end x n H2) as E1.
pose proof (shadow_mono (x + n) alloc_ceiling H3) as E2.
pose proof (shadow_mono 4096 x H1) as E3.
pose proof asan_consts as (C1 & _).
assert (E4 : alloc_ceiling / 8 <= 0xfffffff0000) by (apply Z.div_le_upper_bound; lia).
assert (E5 : shadow_addr 4096 = SHADOW_OFF + 512) by reflexivity.
assert (E6 : shadow_addr alloc_ceiling = SHADOW_OFF + alloc_ceiling / 8) by reflexivity.
unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
Qed.
Lemma rbn3u_val_mem_zero4 : forall H (m : word -> option byte) a,
  (forall i, 0 <= i < 4 -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a 4 0.
Proof.
intros H m a Hz j Hj.
destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l ||
  rewrite Z.mod_0_l by (first [lazymatch goal with |- _ <> @nil _ => discriminate end
                              | vm_compute; discriminate])). lia.
Qed.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis AMEMSET : forall fq : YK11.FPState, aintrin_realizes (fx := fq) SEGS B OSet (SIGMA AS___asan_memset).
Hypothesis STP : rbn3_stp_stmt B.

Definition rbn3u_wz (X : rbn_in) (pos : Z) (a : Z) : Prop :=
  (rbn_A X - ESTACK <= a < rbn_A X) \/ (rbn_A X + 152 <= a < rbn_A X + 184) \/
  (rbn_F X pos + 36 <= a < rbn_F X pos + 37) \/ (rbn_SH X pos + 8 <= a < rbn_SH X pos + 11).

Lemma rbn3u_geom : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  (forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p) /\
  4096 <= rbn_F X pos /\ rbn_F X pos + 512 <= alloc_ceiling /\
  (rbn_F X pos + 512 <= kLowShadowBeg \/ kHighMemBeg <= rbn_F X pos) /\
  kLowMemEnd <= rbn_SH X pos /\ rbn_SH X pos + 64 <= kHighShadowEnd /\
  rbn_SP X - 336 <= rbn_A X <= rbn_SP X - 320 /\
  alloc_ceiling <= rbn_SP X - REAC_BOX_NAME_STK /\ rbn_SP X <= 2 ^ 47 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> ~ in_img SEGS a) /\
  (forall b m, In (b, m) (ablocks B (ri_lyc X) (ri_Sc X)) ->
     4096 <= b /\ b + req_size m <= alloc_ceiling /\
     (b + req_size m <= kLowShadowBeg \/ kHighMemBeg <= b) /\
     (b + req_size m <= rbn_F X pos \/ rbn_F X pos + 512 <= b)) /\
  (forall c p, In (c, p) (frames (ri_Sc X)) ->
     4096 <= frame_addr (ri_lyc X) c p /\
     frame_addr (ri_lyc X) c p + fs_frame_bytes c <= alloc_ceiling /\
     (frame_addr (ri_lyc X) c p + fs_frame_bytes c <= kLowShadowBeg \/
      kHighMemBeg <= frame_addr (ri_lyc X) c p) /\ 0 <= fs_frame_bytes c /\
     kLowMemEnd <= shadow_addr (frame_addr (ri_lyc X) c p) /\
     shadow_addr (frame_addr (ri_lyc X) c p) + fs_frame_bytes c / 8 <= kHighShadowEnd /\
     (frame_addr (ri_lyc X) c p + fs_frame_bytes c <= rbn_F X pos \/
      rbn_F X pos + 512 <= frame_addr (ri_lyc X) c p) /\
     (shadow_addr (frame_addr (ri_lyc X) c p) + fs_frame_bytes c / 8 <= rbn_SH X pos \/
      rbn_SH X pos + 64 <= shadow_addr (frame_addr (ri_lyc X) c p))).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (CAC : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (HSPdef : rbn_SP X = spZ (ri_regs X)) by reflexivity.
assert (HAdef : rbn_A X = 32 * ((rbn_SP X - 320) / 32)) by reflexivity.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
destruct HM as (HJ1 & Hfrs1 & Hperm & _ & HK & _).
pose proof HJ as (HARc & HlyX & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstkX & _).
pose proof HJ1 as (HAR1 & Hly1 & _).
assert (HFeq : forall c p, frame_addr lyc1 c p = frame_addr (ri_lyc X) c p).
{ intros c p. unfold frame_addr.
  destruct HlyX as (_ & _ & _ & _ & _ & HFX & _). destruct Hly1 as (_ & _ & _ & _ & _ & HF1 & _).
  rewrite HFX, HF1. reflexivity. }
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HFlo & HFhi & HFapp).
rewrite HFeq in HFlo, HFhi, HFapp. rewrite Hfb3 in HFhi, HFapp.
fold (rbn_F X pos) in HFlo, HFhi, HFapp.
assert (HSH : rbn_SH X pos = shadow_addr (rbn_F X pos)) by reflexivity.
pose proof (shadow_addr_bounds (rbn_F X pos) ltac:(lia)) as HSHb.
assert (HSHhi : rbn_SH X pos + 64 <= kHighShadowEnd).
{ pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1. change (512 / 8) with 64 in H1.
  pose proof (shadow_addr_bounds (rbn_F X pos + 512) ltac:(lia)) as H2. unfold rbn_SH. lia. }
destruct HstkX as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
destruct (sp1_facts (rbn_SP X - 320) ltac:(lia)
  ltac:(rewrite HSPdef, <- Zminus_mod_idemp_l, Hal; reflexivity)) as (HAr & _ & _).
split; [exact HFeq|]. split; [lia|]. split; [lia|].
split; [destruct HFapp as (_ & HFd); lia|].
split; [unfold rbn_SH; lia|]. split; [exact HSHhi|].
split; [lia|].
split; [lia|]. split; [lia|].
split.
{ intros a Ha.
  assert (Hdisj : (exists q n, In (q, n) (ablocks B lyc1 Sc1) /\ q <= a < q + req_size n) \/
    (exists cid p, In (cid, p) (frames Sc1) /\
       frame_addr lyc1 cid p <= a < frame_addr lyc1 cid p + fs_frame_bytes cid) \/
    (exists cid p, In (cid, p) (frames Sc1) /\ a = flag_addr lyc1 cid p)).
  { right. left. exists 3, pos. split; [exact Hin3|]. rewrite HFeq, Hfb3. exact Ha. }
  exact (proj2 (al_client_img SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 a HAR1 Hdisj)). }
split.
{ intros b m Hb.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARc Hb) as (_ & Hb4 & Hbc & Hbapp & _).
  destruct Hbapp as (_ & Hbd).
  split; [exact Hb4|]. split; [exact Hbc|]. split; [lia|].
  pose proof (sep_block_frame SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 b m 3 pos HAR1
    (Permutation_in _ (Permutation_sym Hperm) Hb) Hin3) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq, Hfb3 in Hd. fold (rbn_F X pos) in Hd. lia. }
intros c p Hc.
assert (Hin' : In (c, p) (frames Sc1)) by (rewrite Hfrs1; right; exact Hc).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR1 Hin') as (Hclo & Hchi & Hcapp).
rewrite HFeq in Hclo, Hchi, Hcapp.
destruct (in_split _ _ Hc) as (l2 & l3 & Hsplit).
pose proof (sep_frames_pos SEGS B LAWS lyc1 Sc1 W1 memc1 mdc1 (3, pos) (c, p) [] l2 l3 HAR1
  ltac:(rewrite Hfrs1, Hsplit; reflexivity)) as Hd.
unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite !HFeq, Hfb3 in Hd.
fold (rbn_F X pos) in Hd.
pose proof (fs_frame_bytes_nonneg c) as Hcnn.
pose proof (shadow_addr_bounds (frame_addr (ri_lyc X) c p) ltac:(lia)) as HG1.
pose proof (shadow_range_end (frame_addr (ri_lyc X) c p) (fs_frame_bytes c) ltac:(lia)) as HG2.
pose proof (shadow_addr_bounds (frame_addr (ri_lyc X) c p + fs_frame_bytes c) ltac:(lia)) as HG3.
destruct Hcapp as (_ & Hcd).
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hcnn|]. split; [lia|]. split; [lia|].
split; [lia|].
destruct Hd as [Hd | Hd].
- right. unfold rbn_SH.
  pose proof (shadow_range_end (rbn_F X pos) 512 ltac:(lia)) as H1.
  pose proof (shadow_mono (rbn_F X pos + 512) (frame_addr (ri_lyc X) c p) ltac:(lia)) as H2.
  change (512 / 8) with 64 in H1. lia.
- left. unfold rbn_SH.
  pose proof (shadow_mono (frame_addr (ri_lyc X) c p + fs_frame_bytes c) (rbn_F X pos) ltac:(lia)) as H2.
  lia.
Qed.

Lemma rbn3u_A_rng : forall X, rbn_cx B X ->
  alloc_ceiling + 8816 <= rbn_SP X /\ rbn_SP X - 351 <= rbn_A X /\ rbn_A X + 320 <= rbn_SP X /\
  rbn_A X mod 32 = 0 /\ rbn_SP X + 16 <= 2 ^ 47 /\
  ri_sp0 X - ri_STK X <= rbn_SP X - 8816 /\ rbn_SP X + 16 <= ri_sp0 X /\
  ly_stk_lo (ri_ly X) + ri_STK X <= ri_sp0 X /\ ri_sp0 X <= ly_stk_hi (ri_ly X) /\ rbn_SP X mod 16 = 0 /\
  ri_sp0 X mod 16 = 0 /\ rbn_A X mod 16 = 0.
Proof.
intros X HX. destruct HX as (HJ & _ & _ & _ & _ & _ & _ & _ & Hal & Hstk & Hsp & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
rewrite WS in Hstk. unfold rbn_A, rbn_SP.
pose proof (Z.div_mod (spZ (ri_regs X) - 320) 32 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (spZ (ri_regs X) - 320) 32 ltac:(lia)) as M1.
assert (HA32 : 32 * ((spZ (ri_regs X) - 320) / 32) mod 32 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
assert (HA16 : 32 * ((spZ (ri_regs X) - 320) / 32) mod 16 = 0).
{ replace (32 * ((spZ (ri_regs X) - 320) / 32)) with ((2 * ((spZ (ri_regs X) - 320) / 32)) * 16) by lia.
  apply Z_mod_mult. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HA32|].
repeat split; try lia; assumption.
Qed.

Lemma rbn3u_F_facts : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  rbn_F X pos mod 32 = 0 /\ in_app (rbn_F X pos) 512 /\
  (forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> apresent (w_H W1) memc1 a).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM.
destruct (rbn3u_geom X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HX HM) as (HFeq & _).
destruct HM as (HJ1 & Hfrs & _). pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (Hal & Happ & Hpr & _).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
unfold rbn_F. rewrite <- (HFeq 3 pos). rewrite Hfb3 in *.
split; [exact Hal|]. split; [exact Happ|]. intros a Ha. exact (proj1 (Hpr a Ha)).
Qed.

Lemma rbn3u_stk_eq : forall X pos lyc1 Sc1 W1 memc1 mdc1 Er sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 Er sh ->
  ly_stk_lo lyc1 = ly_stk_lo (ri_ly X) /\ ly_stk_hi lyc1 = ly_stk_hi (ri_ly X).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 Er sh HM.
destruct HM as ((_ & L1 & _) & _).
destruct L1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _). split; assumption.
Qed.

Lemma rbn3u_stk_shadow : forall lyc Sc W mem md a n,
  AR SEGS B lyc Sc W mem md ->
  ly_stk_lo lyc + 64 <= a -> a + n + 64 <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros lyc Sc W mem md a n HAR H1 H2 Hn.
pose proof (al_zshadow _ _ LAWS lyc Sc W mem md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HAR
  (or_introl eq_refl)) as HZ.
cbn [fst snd] in HZ.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & HPlo & HPhi & _).
unfold page_aligned in HPlo, HPhi.
assert (Hz : forall x, ly_stk_lo lyc <= x < ly_stk_hi lyc -> aview SEGS (w_H W) mem (shadow_addr x) = Some 0).
{ intros x Hx.
  pose proof (HZ (x / 8 - ly_stk_lo lyc / 8) ltac:(lia)) as E.
  unfold shadow_of_addr in E. unfold shadow_addr.
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + ly_stk_lo lyc / 8 + (x / 8 - ly_stk_lo lyc / 8)) by lia.
  exact E. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). apply Hz. lia.
- intros s Hs.
  assert (Hx : shadow_addr (8 * (s - SHADOW_OFF)) = s) by (unfold shadow_addr; lia).
  rewrite <- Hx. rewrite Hz; [discriminate|]. unfold shadow_addr in Hs. lia.
Qed.

Lemma rbn3u_mid_fw : forall X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2,
  rbn_cx B X -> rbn_mid B X pos lyc1 Sc1 W1 memc1 mdc1 (fun _ => False) (rbn_sh true false false false) ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 mem2 md2 (ri_k X) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ rbn3u_wz X pos a -> aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a) ->
  (forall a, apresent (w_H W1) memc1 a -> apresent (w_H W1) mem2 a) ->
  (forall j, 0 <= j < 3 -> aview SEGS (w_H W1) mem2 (rbn_SH X pos + 8 + j) = Some 0) ->
  rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh true true false false).
Proof.
intros X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 HX HM HJ2 HEQ HPR HSH3.
destruct (rbn3u_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
destruct (rbn3u_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10 & AR11 & AR12).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Happ : forall a, rbn_F X pos <= a < rbn_F X pos + 512 -> a < kLowShadowBeg \/ kHighMemBeg <= a)
  by (intros a Ha; unfold kLowShadowBeg, kHighMemBeg in *; lia).
unfold rbn_mid. split; [exact HJ2|]. split; [exact Hfrs1|]. split; [exact Hperm|].
split.
{ intros a Hroa Ho He.
  assert (Hia : in_img SEGS a)
    by (destruct Hroa as [(sg & Hsg & _ & Hr) | Hr];
        [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (pa_segs_low a Hia) as Hlow.
  rewrite (HEQ a ltac:(lia)
    ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]];
          [lia | lia | exact (HFimg a ltac:(lia) Hia) | lia])).
  exact (Hro1 a Hroa Ho He). }
split.
{ split.
  { intros a Ha Hn _.
    rewrite (HEQ a ltac:(lia) ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia)).
    exact (K1 a Ha Hn ltac:(intros [])). }
  split.
  { intros b m j Hb Hj _. destruct (HBlk b m Hb) as (Hb4 & Hbc & Hbz & Hbd).
    rewrite (HEQ (b + j) ltac:(lia) ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia)).
    exact (K2 b m j Hb Hj ltac:(intros [])). }
  split.
  { intros a Hia Ho He. pose proof (pa_segs_low a Hia) as Hlow.
    rewrite (HEQ a ltac:(lia)
      ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]];
            [lia | lia | exact (HFimg a ltac:(lia) Hia) | lia])).
    exact (K3 a Hia Ho He). }
  split.
  { intros cid p a Hcp Ha _.
    destruct (HFrm cid p Hcp) as (Hg4 & Hgc & Hgz & Hgn & Hgs1 & Hgs2 & Hgd & Hsd).
    unfold in_zr, frame_rng in Ha. cbn [fst snd] in Ha.
    rewrite (HEQ a ltac:(destruct Ha as [Ha | Ha]; lia)
      ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; destruct Ha as [Ha | Ha]; lia)).
    exact (K4 cid p a Hcp ltac:(unfold in_zr, frame_rng; cbn [fst snd]; exact Ha) ltac:(intros [])). }
  split.
  { intros a Ha Hn Hp. apply HPR. exact (K5 a Ha Hn Hp). }
  intros a Ha. apply Hpres2. lia. }
split.
{ intros j r Hj.
  assert (Hjr : (j < 13)%nat)
    by (apply (proj1 (nth_error_Some rbn_saved_regs j)); rewrite Hj; discriminate).
  apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [| exact (HFr1 j r Hj)].
  intros k Hk. apply HEQ; [lia | unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia]. }
split.
{ apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 mem2); [| exact HFL1].
  intros k Hk. apply HEQ; [lia | unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia]. }
intros j Hj. rewrite rbn3u_sh_len in Hj.
destruct (Z_lt_le_dec j 8) as [Hlt | Hge].
- rewrite (HEQ (rbn_SH X pos + j) ltac:(lia) ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia)).
  rewrite (HSh1 j ltac:(rewrite rbn3u_sh_len; lia)).
  f_equal. symmetry. apply rbn3u_sh_eq; [lia | left; lia].
- destruct (Z_lt_le_dec j 11) as [Hlt2 | Hge2].
  + replace (rbn_SH X pos + j) with (rbn_SH X pos + 8 + (j - 8)) by lia.
    rewrite (HSH3 (j - 8) ltac:(lia)). f_equal.
    assert (Hj3 : j = 8 \/ j = 9 \/ j = 10) by lia.
    destruct Hj3 as [-> | [-> | ->]]; reflexivity.
  + rewrite (HEQ (rbn_SH X pos + j) ltac:(lia) ltac:(unfold rbn3u_wz; intros [Hw | [Hw | [Hw | Hw]]]; lia)).
    rewrite (HSh1 j ltac:(rewrite rbn3u_sh_len; lia)).
    f_equal. symmetry. apply rbn3u_sh_eq; [lia | right; lia].
Qed.

Lemma rbn3u_mid_same : forall X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh,
  rbn_mid B X pos lyc1 Sc1 W1 memc2 mdc2 (fun _ => False) sh ->
  ajournal SEGS B (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 W1 memc3 mdc3 (ri_k X) ->
  (forall x, mrestrict (w_H W1) memc3 x = mrestrict (w_H W1) memc2 x) ->
  rbn_mid B X pos lyc1 Sc1 W1 memc3 mdc3 (fun _ => False) sh.
Proof.
intros X pos lyc1 Sc1 W1 memc2 mdc2 memc3 mdc3 sh
  (HJ & Hfr & Hp & Hro & (K1 & K2 & K3 & K4 & K5 & K6) & HFr & HFL & HSh) HJ3 Hm.
assert (Hv : forall a, aview SEGS (w_H W1) memc3 a = aview SEGS (w_H W1) memc2 a)
  by (intros a; apply rbn3u_aview_mr; exact Hm).
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hp|].
split; [intros a H1 H2 H3; rewrite Hv; exact (Hro a H1 H2 H3)|].
split.
{ split; [intros a H1 H2 H3; rewrite Hv; exact (K1 a H1 H2 H3)|].
  split; [intros b m j H1 H2 H3; rewrite Hv; exact (K2 b m j H1 H2 H3)|].
  split; [intros a H1 H2 H3; rewrite Hv; exact (K3 a H1 H2 H3)|].
  split; [intros cid p a H1 H2 H3; rewrite Hv; exact (K4 cid p a H1 H2 H3)|].
  split; [intros a H1 H2 H3; apply (rbn3u_apresent_mr _ memc2 memc3 a Hm); exact (K5 a H1 H2 H3)|].
  intros a H1. apply (rbn3u_apresent_mr _ memc2 memc3 a Hm). exact (K6 a H1). }
split; [intros j r Hj; apply (rbn3u_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact (HFr j r Hj)|].
split; [apply (rbn3u_val_mem_mr _ memc2 memc3 _ _ _ Hm); exact HFL|].
intros j Hj. rewrite Hv. exact (HSh j Hj).
Qed.

Lemma rbn3u_entry : forall (fq : YK11.FPState) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P,
  rbn_cx B X -> rbn3_stU B X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P ->
  rbn_stp X pos W1 memc1 P ->
  st_ok_pi SEGS VAL (ERB3U regs1 (hd 0 (rbm_stem X))) ss_rbn3u
    (restrict (w_H W1) (mkst (fx := fq) regs1 (Z_to_bv 64 (BASE + RBN_U3PC)) memc1 (seg_rom SEGS))).
Proof.
intros fq X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX HU HSTP.
pose proof HU as (HM & HRB & R18 & R20 & R21 & R25r & HC & HW4 & HPok & HA).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
destruct (rbn3u_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
destruct (rbn3u_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10 & AR11 & AR12).
destruct (rbn3u_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF32 & HFapp & HFpres).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
pose proof HSTP as (Hstr & Hsep).
destruct Hstr as (Hfs & Hgs & HP0 & HP1 & HPl & Ham & HPra & HPhv & HPtl).
assert (Hcb : 0 < hd 0 (rbm_stem X) < 256).
{ pose proof (rbn3u_stem_ne X) as Hne. destruct (rbm_stem X) as [|c0 l0]; [contradiction|].
  cbn [hd]. inversion Hfs. assumption. }
assert (HPhi : P <= 2 ^ 47 - 2).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
pose proof (proj1 HJ1) as HAR1.
assert (Hin3 : In (3, pos) (frames Sc1)) by (rewrite Hfrs1; left; reflexivity).
destruct (al_frames _ _ LAWS _ _ _ _ _ 3 pos HAR1 Hin3) as (_ & _ & HFpres2 & HSHpres).
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
rewrite (HFeq 3 pos) in HSHpres. rewrite Hfb3 in HSHpres.
fold (rbn_F X pos) in HSHpres. fold (rbn_SH X pos) in HSHpres.
change (512 / 8) with 64 in HSHpres.
rewrite restrict_mkst_fx.
set (E := ERB3U regs1 (hd 0 (rbm_stem X))).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB3U; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2%nat = w64 (rbn_A X)) by (rewrite (EE 2%nat 2%bv eq_refl); exact B2).
assert (E9 : ew E 9%nat = w64 (rbn_A X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact B9).
assert (E18 : ew E 18%nat = w64 (rbn_SH X pos)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E20 : ew E 20%nat = w64 (rbn_F X pos + 32)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22%nat = w64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact B22).
assert (E25 : ew E 25%nat = w64 P) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25r).
assert (E32 : ew E 32%nat = Z_to_bv 64 (hd 0 (rbm_stem X)))
  by (subst E; unfold ERB3U; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (U2 : bv_unsigned (ew E 2%nat) = rbn_A X) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9%nat) = rbn_A X) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18%nat) = rbn_SH X pos) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20%nat) = rbn_F X pos + 32)
  by (rewrite E20; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22%nat) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25%nat) = P) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32%nat) = hd 0 (rbm_stem X))
  by (rewrite E32; apply unsigned_lit_small; lia).
apply rbn3u_cells_app in HC as [HCa HCw].
unfold rbn_rw in HCw. cbn [rbn_cells] in HCw. destruct HCw as (Wa & Wb & Wc & Wd & _).
unfold ss_rbn3u, rbn3u_regions. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_ERB3U.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  + rewrite U9. split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply K6; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (rbn_A X) 200 8 _ 4); [reflexivity | zside | zside |].
    change (N.to_nat 8) with 8%nat. exact Wc.
  + rewrite U20. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply HFpres. lia.
  + rewrite U18. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HSHpres o ltac:(lia))).
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U18, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [rbn3u_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U18, U20, U22, U25, U32.
  change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Theorem rbn3u_u : rbn3_u_stmt B.
Proof.
intros X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX HU.
pose proof HU as (HM & HRB & R18 & R20 & R21 & R25r & HC & HW4 & HPok & HA).
pose proof HRB as (B2 & B3 & B4 & B8 & B9 & B19 & B22 & B23).
destruct (rbn3u_geom X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as
  (HFeq & HFlo & HFhi & HFz & HSlo & HShi & HAb & HCeil & H47 & HFimg & HBlk & HFrm).
destruct (rbn3u_A_rng X HX) as (AR1 & AR2 & AR3 & AR4 & AR5 & AR6 & AR7 & AR8 & AR9 & AR10 & AR11 & AR12).
destruct (rbn3u_F_facts X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HX HM) as (HF32 & HFapp & HFpres).
destruct (rbn3u_stk_eq X pos lyc1 Sc1 W1 memc1 mdc1 _ _ HM) as (Elo & Ehi).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
assert (WS : REAC_BOX_NAME_STK = 8816) by reflexivity.
assert (CLSB : kLowShadowBeg = 0x7fff7000) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hfb3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof (STP X pos P lyc1 Sc1 W1 memc1 mdc1 HX HA HPok
  (rbn3_rel_of_mid B X pos lyc1 Sc1 W1 memc1 mdc1 _ HM)) as HSTP.
pose proof HSTP as (Hstr & Hsep).
destruct Hstr as (Hfs & Hgs & HP0 & HP1 & HPl & Ham & HPra & HPhv & HPtl).
assert (Hcb : 0 < hd 0 (rbm_stem X) < 256).
{ pose proof (rbn3u_stem_ne X) as Hne. destruct (rbm_stem X) as [|c0 l0]; [contradiction|].
  cbn [hd]. inversion Hfs. assumption. }
assert (HPhi : P <= 2 ^ 47 - 2).
{ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
pose proof HM as (HJ1 & Hfrs1 & Hperm & Hro1 & (K1 & K2 & K3 & K4 & K5 & K6) & HFr1 & HFL1 & HSh1).
pose proof (proj1 HJ1) as HAR1.
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPst & _).
pose proof (rbn3u_entry (ri_fq X) X pos regs1 lyc1 Sc1 W1 memc1 mdc1 P HX HU HSTP) as HS0.
pose proof (@SRr_run_pi_AJ (ri_fq X) _ _ _ _ _ B LAWS) as RUNP.
pose proof (@SRr_run_pi_AJ_call (ri_fq X) _ _ _ _ _ B LAWS) as RUNC.
pose proof (@paj_run_to (ri_fq X) _ _ _ _ _ B LAWS) as RUNTO.
pose proof (paj_branch (fx := ri_fq X) (L := lib_both3_0_listing) (PI := PI)) as BR.
set (E := ERB3U regs1 (hd 0 (rbm_stem X))) in HS0.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold ERB3U; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold ERB3U; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2 : ew E 2%nat = w64 (rbn_A X)) by (rewrite (EE 2%nat 2%bv eq_refl); exact B2).
assert (E9 : ew E 9%nat = w64 (rbn_A X)) by (rewrite (EE 9%nat 9%bv eq_refl); exact B9).
assert (E19 : ew E 19%nat = w64 (rbn_F X pos)) by (rewrite (EE 19%nat 19%bv eq_refl); exact B19).
assert (E18 : ew E 18%nat = w64 (rbn_SH X pos)) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E20 : ew E 20%nat = w64 (rbn_F X pos + 32)) by (rewrite (EE 20%nat 20%bv eq_refl); exact R20).
assert (E22 : ew E 22%nat = w64 SHADOW_OFF) by (rewrite (EE 22%nat 22%bv eq_refl); exact B22).
assert (E25 : ew E 25%nat = w64 P) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25r).
assert (E32 : ew E 32%nat = Z_to_bv 64 (hd 0 (rbm_stem X)))
  by (subst E; unfold ERB3U; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (U2 : bv_unsigned (ew E 2%nat) = rbn_A X) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9%nat) = rbn_A X) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18%nat) = rbn_SH X pos) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20%nat) = rbn_F X pos + 32)
  by (rewrite E20; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25%nat) = P) by (rewrite E25; apply unsigned_lit_small; lia).
unfold rbn_cfg, cfg_at.
replace (BASE + AF_both3_reac_box_name + RBN_U3) with (BASE + RBN_U3PC)
  by (unfold AF_both3_reac_box_name, RBN_U3, RBN_U3PC; lia).
change (w64 (BASE + RBN_U3PC)) with (Z_to_bv 64 (BASE + RBN_U3PC)).
pose proof (st_ok_pi_pin_reg' E ss_rbn3u _ (21%bv : bv 5) 5 HS0
  ltac:(cbn [ms_regs mkst restrict]; exact R21) eq_refl) as HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
clear HS0.
paj_run_shc RUNP RUNC HS HJ1.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | cbn [base_val]; rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (rbn_F X pos + 32)); [reflexivity | exact U20 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFeq, Hfb3.
    fold (rbn_F X pos). lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos));
    [reflexivity | exact U18 | | apply awr_ok_nil].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFeq, Hfb3.
    fold (rbn_F X pos). fold (rbn_SH X pos). change (512 / 8) with 64. lia. } }
rename HG into G1. rename HFr into F1. clear HF.
psrr_branch_pi RUNP BR HS.
{ exfalso. rewrite branch_ltu_U, (U_not E 20%nat (rbn_F X pos + 32) E20 ltac:(lia)) in Hc.
  rewrite (U_lit E 4 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. lia. }
paj_run_shc RUNP RUNC HS HJ1.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (rbn_A X - ri_sp0 X));
    [reflexivity | cbn [base_val]; rewrite U9; lia | cbn; lia | cbn; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (rbn_F X pos + 32)); [reflexivity | exact U20 | |].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFeq, Hfb3.
    fold (rbn_F X pos). lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (rbn_SH X pos));
    [reflexivity | exact U18 | | apply awr_ok_nil].
  { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. right. right. right. exists 3, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite HFeq, Hfb3.
    fold (rbn_F X pos). fold (rbn_SH X pos). change (512 / 8) with 64. lia. } }
rename HG into G2. rename HFr into F2. clear HF.
pose proof (st_ok_region_nth E _ _ 0%nat _ HS eq_refl) as HR9. cbn [ms_mem restrict] in HR9.
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HR20. cbn [ms_mem restrict] in HR20.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HR18. cbn [ms_mem restrict] in HR18.
assert (KW : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((rbn_A X + 152 <= a < rbn_A X + 184) \/ (rbn_F X pos + 36 <= a < rbn_F X pos + 37) \/
     (rbn_SH X pos + 8 <= a < rbn_SH X pos + 11)) ->
  aview SEGS (w_H W1) (ms_mem ms0) a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha Hn.
  rewrite (rbn3u_kept_frame E _ (w_H W1) (ms_mem ms) (ms_mem ms0)
    (fun a => (rbn_A X + 152 <= a < rbn_A X + 184) \/ (rbn_F X pos + 36 <= a < rbn_F X pos + 37) \/
       (rbn_SH X pos + 8 <= a < rbn_SH X pos + 11)) F2
    ltac:(intros x (r & Hr & Hw); cbn [ss_mem In add_cond] in Hr;
          repeat (destruct Hr as [<- | Hr]); try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?U9, ?U18, ?U20 in Hw; lia) a Ha Hn).
  rewrite (rbn3u_kept_frame E _ (w_H W1) memc1 (ms_mem ms)
    (fun a => (rbn_A X + 152 <= a < rbn_A X + 184) \/ (rbn_F X pos + 36 <= a < rbn_F X pos + 37) \/
       (rbn_SH X pos + 8 <= a < rbn_SH X pos + 11)) F1
    ltac:(intros x (r & Hr & Hw); cbn [ss_mem In] in Hr;
          repeat (destruct Hr as [<- | Hr]); try destruct Hr;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
          rewrite ?U9, ?U18, ?U20 in Hw; lia) a Ha Hn).
  reflexivity. }
assert (V152 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms0)) (rbn_A X + 152) 8 (rbn_F X pos + 64)).
{ apply (field_of_region E _ 9%nat (rbn_A X) _ 152 208 152 168 152 8%N (SOff 19 64) (rbn_F X pos + 64)
    HR9 U9 ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E19; unfold w64;
      rewrite unsigned_lit_small by lia; reflexivity) ltac:(zside) ltac:(zside)). }
assert (V160 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms0)) (rbn_A X + 160) 8 24).
{ apply (field_of_region E _ 9%nat (rbn_A X) _ 152 208 152 168 160 8%N (SLit 24) 24
    HR9 U9 ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(zside) ltac:(zside)). }
assert (VF36 : val_mem SEGS (mrestrict (w_H W1) (ms_mem ms0)) (rbn_F X pos + 32 + 4) 1 0).
{ apply (field_of_region E _ 20%nat (rbn_F X pos + 32) _ 4 5 4 5 4 1%N (SLit 0) 0
    HR20 U20 ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(zside) ltac:(zside)). }
assert (VSH : forall j, 0 <= j < 3 ->
  val_mem SEGS (mrestrict (w_H W1) (ms_mem ms0)) (rbn_SH X pos + (8 + j)) 1 0).
{ intros j Hj.
  assert (Hj3 : j = 0 \/ j = 1 \/ j = 2) by lia.
  destruct Hj3 as [-> | [-> | ->]].
  - apply (field_of_region E _ 18%nat (rbn_SH X pos) _ 8 11 8 11 8 1%N (SLit 0) 0
      HR18 U18 ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(zside) ltac:(zside)).
  - apply (field_of_region E _ 18%nat (rbn_SH X pos) _ 8 11 8 11 9 1%N (SLit 0) 0
      HR18 U18 ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(zside) ltac:(zside)).
  - apply (field_of_region E _ 18%nat (rbn_SH X pos) _ 8 11 8 11 10 1%N (SLit 0) 0
      HR18 U18 ltac:(cbn [In]; tauto) ltac:(reflexivity) ltac:(zside) ltac:(zside)). }
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp.
prreg HS (4%bv : bv 5) Rtp.
rewrite U9 in Ra0.
rewrite (EE 2%nat 2%bv eq_refl), B2 in Rsp.
rewrite (EE 3%nat 3%bv eq_refl), B3 in Rgp. rewrite (EE 4%nat 4%bv eq_refl), B4 in Rtp.
assert (Hsp : spZ (ms_regs ms0) = ri_sp0 X + (rbn_A X - ri_sp0 X))
  by (unfold spZ at 1; rewrite Rsp; unfold w64; rewrite unsigned_lit_small by lia; lia).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rT _ ?mT _) ?dT) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA AS___asan_memset) (AMEMSET (ri_fq X)) W1 rT mT
    (ri_STK X) (ri_sp0 X) (ri_FP X) (ri_ly X) (ri_S X) (ri_W0 X) (ri_mem0 X) (ri_md0 X)
    ((3, pos) :: ri_own X) lyc1 Sc1 dT (ri_k X) (rbn_A X + 168) 0 16 (rbn_A X - ri_sp0 X) _ HJ1) end.
  - rewrite Ra0. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - exact Hsp.
  - rewrite Zminus_mod, AR12, AR11. reflexivity.
  - lia.
  - rewrite Hes. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [left; lia | lia].
  - unfold amem_range, kHighMemBeg, kHighMemEnd. right. lia.
  - exact (proj1 (rbn3u_stk_shadow lyc1 Sc1 W1 (ms_mem ms0) _ (rbn_A X + 168) 16
      (proj1 HJ1) ltac:(lia) ltac:(lia) ltac:(lia))).
  - intros _. exact (proj2 (rbn3u_stk_shadow lyc1 Sc1 W1 (ms_mem ms0) _ (rbn_A X + 168) 16
      (proj1 HJ1) ltac:(lia) ltac:(lia) ltac:(lia))).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hkeep & Hpres2).
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres2 & _).
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ rbn3u_wz X pos a ->
  aview SEGS (w_H W1) mem2 a = aview SEGS (w_H W1) memc1 a).
{ intros a Ha Hn. unfold rbn3u_wz in Hn.
  rewrite (Hkeep a Ha ltac:(lia) ltac:(rewrite Hes; lia)).
  apply KW; [lia | lia]. }
assert (HM2 : rbn_mid B X pos lyc1 Sc1 W1 mem2 md2 (fun _ => False) (rbn_sh true true false false)).
{ apply (rbn3u_mid_fw X pos lyc1 Sc1 W1 memc1 mdc1 mem2 md2 HX HM HJ2 KM).
  - intros a Hp. apply Hpres2. apply (apresent_grows _ _ _ _ G2). apply (apresent_grows _ _ _ _ G1). exact Hp.
  - intros j Hj.
    rewrite (Hkeep (rbn_SH X pos + 8 + j) ltac:(lia) ltac:(lia) ltac:(rewrite Hes; lia)).
    pose proof (VSH j Hj 0%nat ltac:(lia)) as Hv. cbn [Z.of_nat] in Hv.
    rewrite Z.add_0_r in Hv. replace (rbn_SH X pos + 8 + j) with (rbn_SH X pos + (8 + j)) by lia.
    unfold aview. rewrite Hv. reflexivity. }
pose proof (STP X pos P lyc1 Sc1 W1 mem2 md2 HX HA HPok
  (rbn3_rel_of_mid B X pos lyc1 Sc1 W1 mem2 md2 _ HM2)) as HSTP2.
pose proof HSTP2 as (Hstr2 & Hsep2).
destruct Hstr2 as (Hfs2 & Hgs2 & HP02 & HP12 & HPl2 & Ham2 & HPra2 & HPhv2 & HPtl2).
jafter_call_keep_pi HS 33%nat regs2 (mrestrict (w_H W1) mem2) HP2 (@nil nat) HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ apply Forall_nil. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 33 (map (getr regs2) CLOB)) as Ev eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM Ev) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD : forall n, (n < 33)%nat -> ew Ev n = ew E n)
  by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
clear HE2.
assert (W22 : U Ev rbn3u_Bx = SHADOW_OFF).
{ unfold U, rbn3u_Bx. cbn [sv_denot]. rewrite OLD by lia. rewrite E22, Z.add_0_r.
  unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. unfold SHADOW_OFF. lia. }
assert (W25 : U Ev (SOff 25 0) = P).
{ unfold U. cbn [sv_denot]. rewrite OLD by lia. rewrite E25, Z.add_0_r.
  unfold w64. rewrite Z_to_bv_bv_unsigned. apply unsigned_lit_small. lia. }
assert (U25b : bv_unsigned (ew Ev 25%nat) = P) by (rewrite OLD by lia; exact U25).
assert (E32b : ew Ev 32%nat = Z_to_bv 64 (hd 0 (rbm_stem X))) by (rewrite OLD by lia; exact E32).
assert (VP : val_mem SEGS (mrestrict (w_H W1) mem2) (P + 0) 1 (hd 0 (rbm_stem X))).
{ pose proof (proj1 (Hgs2 0%nat ltac:(rewrite length_app; cbn [length]; lia))) as Hv.
  rewrite rbn3u_nth0 in Hv. cbn [Z.of_nat] in Hv. exact Hv. }
pose proof (st_ok_pi_add_region Ev _ _ rbn3u_R25 HS eq_refl) as HS3.
match type of HS3 with ?a -> ?b -> _ => assert (HRO : a); [|assert (HAD : b); [|specialize (HS3 HRO HAD)]] end.
{ unfold rbn3u_R25, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst].
  rewrite U25b. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS Ev _ P 0 1 _ (hd 0 (rbm_stem X)));
    [cbn [sv_denot]; rewrite E32b, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  change (N.to_nat 1) with 1%nat. exact VP. }
{ cbn [all_disjoint ss_mem]. exact I. }
clear HS HRO HAD. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : sh_ok SEGS rbn3u_Bx rbn3u_SH Ev (mrestrict (w_H W1) mem2)).
{ unfold sh_ok, rbn3u_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W1) mem2 Ev rbn3u_Bx 25 P (Z.of_nat (length (rbm_stem X)) + 1) P 0 1
    HPra2 W22 W25 ltac:(lia) ltac:(lia)).
  intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham2. unfold SHADOW_OFF. lia. }
paj_run_to_tok RUNTO HS HJ2 SHOK rbn3u_Bspan RBN_P4PC.
{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?s0 ?fp ?b0 ?bc ?ly0 ?own0 =>
  let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk s0 fp b0 bc ly0 own0) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
assert (Hmm : forall x, mrestrict (w_H W1) (ms_mem ms1) x = mrestrict (w_H W1) mem2 x)
  by (intros x; apply HFr; apply rbn3u_nowrange).
assert (HM3 : rbn_mid B X pos lyc1 Sc1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2)
  (fun _ => False) (rbn_sh true true false false))
  by (apply (rbn3u_mid_same X pos lyc1 Sc1 W1 mem2 md2 _ _ _ HM2 HJ2 Hmm)).
apply SRr_ret.
pmkst HS.
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19. prreg HS (20%bv : bv 5) Q20.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23.
prreg HS (24%bv : bv 5) Q24. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
prreg HS (27%bv : bv 5) Q27.
rewrite OLD, (EE 2%nat 2%bv eq_refl) in Q2 by lia.
rewrite OLD, (EE 3%nat 3%bv eq_refl) in Q3 by lia.
rewrite OLD, (EE 4%nat 4%bv eq_refl) in Q4 by lia.
rewrite OLD, (EE 8%nat 8%bv eq_refl) in Q8 by lia.
rewrite OLD, (EE 9%nat 9%bv eq_refl) in Q9 by lia.
rewrite OLD, E32 in Q10 by lia.
rewrite OLD, E18 in Q18 by lia.
rewrite OLD, E19 in Q19 by lia.
rewrite OLD, E20 in Q20 by lia.
rewrite OLD, E25 in Q21 by lia.
rewrite OLD, (EE 22%nat 22%bv eq_refl) in Q22 by lia.
rewrite OLD, (EE 23%nat 23%bv eq_refl) in Q23 by lia.
rewrite OLD, E25 in Q25 by lia.
rewrite OLD, E25 in Q26 by lia.
rewrite OLD, E19 in Q27 by lia.
exists pos, (ms_regs ms1), lyc1, Sc1, (ms_mem ms1), (with_vm_backing (m_vm_lazy md2) mat1 md2), P.
split.
{ unfold rbn_cfg, cfg_at, w64.
  replace (BASE + AF_both3_reac_box_name + RBN_P4) with (BASE + RBN_P4PC)
    by (unfold AF_both3_reac_box_name, RBN_P4, RBN_P4PC; lia).
  reflexivity. }
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ rbn3u_wz X pos a ->
  aview SEGS (w_H W1) (ms_mem ms1) a = aview SEGS (w_H W1) memc1 a)
  by (intros a Ha Hn; rewrite (rbn3u_aview_mr (w_H W1) mem2 (ms_mem ms1) a Hmm); apply KM; [lia | exact Hn]).
unfold rbn_st4. split; [exact HM3|].
split.
{ split; [rewrite Q2; exact B2|]. split; [rewrite Q3; exact B3|]. split; [rewrite Q4; exact B4|].
  split; [rewrite Q8; exact B8|]. split; [rewrite Q9; exact B9|].
  split; [rewrite Q19; reflexivity|]. split; [rewrite Q22; exact B22 | rewrite Q23; exact B23]. }
split; [rewrite Q18; reflexivity|].
split; [rewrite Q20; reflexivity|].
split; [rewrite Q27; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite Q25; reflexivity|].
split; [rewrite Q21; reflexivity|].
split; [rewrite Q26; unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
split; [rewrite Q24; apply bv_eq; vm_compute; reflexivity|].
split; [rewrite Q10; reflexivity|].
split.
{ apply rbn3u_cells_app in HC as [HCa HCw].
  apply rbn3u_cells_app. split.
  { apply (rbn3u_cells_kept (w_H W1) (w_H W1) memc1 (ms_mem ms1)); [|exact HCa].
    intros a n v k Hin Hk. pose proof (rbn3u_argc_rng X a n v Hin) as Hr.
    apply KF; [lia | unfold rbn3u_wz; lia]. }
  apply rbn3u_cells_app. split.
  { apply (rbn3u_cells_kept (w_H W1) (w_H W1) memc1 (ms_mem ms1)); [|exact HCw].
    intros a n v k Hin Hk. pose proof (rbn3u_rw_rng X pos 4 0 a n v Hin) as Hr.
    apply KF; [lia | unfold rbn3u_wz; lia]. }
  unfold rbn_rn. cbn [rbn_cells].
  split.
  { apply (rbn3u_val_mem_mr (w_H W1) mem2 (ms_mem ms1) _ _ _ Hmm).
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms0) mem2); [|exact V152].
    intros k Hk. rewrite (Hkeep (rbn_A X + 152 + k) ltac:(lia) ltac:(lia) ltac:(rewrite Hes; lia)).
    reflexivity. }
  split.
  { apply (rbn3u_val_mem_mr (w_H W1) mem2 (ms_mem ms1) _ _ _ Hmm).
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms0) mem2); [|exact V160].
    intros k Hk. rewrite (Hkeep (rbn_A X + 160 + k) ltac:(lia) ltac:(lia) ltac:(rewrite Hes; lia)).
    reflexivity. }
  split.
  { apply (rbn3u_val_mem_mr (w_H W1) mem2 (ms_mem ms1) _ _ _ Hmm).
    apply val_mem_zero8. intros i Hi.
    replace (rbn_A X + 168 + i) with (rbn_A X + 168 + i) by lia. rewrite (Heff i ltac:(lia)). reflexivity. }
  split; [|exact I].
  apply (rbn3u_val_mem_mr (w_H W1) mem2 (ms_mem ms1) _ _ _ Hmm).
  apply rbn3u_val_mem_zero4. intros i Hi.
  replace (rbn_A X + 176 + i) with (rbn_A X + 168 + (8 + i)) by lia. rewrite (Heff (8 + i) ltac:(lia)).
  reflexivity. }
split.
{ intros j Hj. rewrite length_app, (rbn3u_w4_len X HA) in Hj. cbn [length] in Hj.
  destruct (Nat.lt_ge_cases j 4) as [Hj4 | Hj4].
  - rewrite app_nth1 by (rewrite (rbn3u_w4_len X HA); lia).
    destruct (HW4 j ltac:(rewrite (rbn3u_w4_len X HA); lia)) as (Hv & Hr).
    split; [|exact Hr].
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) memc1 (ms_mem ms1)); [|exact Hv].
    intros k Hk. apply KF; [lia | unfold rbn3u_wz; lia].
  - assert (Hje : j = 4%nat) by lia. subst j.
    rewrite app_nth2 by (rewrite (rbn3u_w4_len X HA); lia).
    rewrite (rbn3u_w4_len X HA). cbn [Nat.sub nth].
    split; [|lia].
    apply (rbn3u_val_mem_mr (w_H W1) mem2 (ms_mem ms1) _ _ _ Hmm).
    apply (val_mem_kept SEGS (w_H W1) (w_H W1) (ms_mem ms0) mem2);
      [|replace (rbn_F X pos + 32 + Z.of_nat 4) with (rbn_F X pos + 32 + 4) by (cbn [Z.of_nat]; lia);
        exact VF36].
    intros k Hk. rewrite (Hkeep (rbn_F X pos + 32 + Z.of_nat 4 + k) ltac:(cbn [Z.of_nat]; lia)
      ltac:(cbn [Z.of_nat]; lia) ltac:(rewrite Hes; cbn [Z.of_nat]; lia)).
    reflexivity. }
split; [|exact HA].
exact (STP X pos P lyc1 Sc1 W1 (ms_mem ms1) (with_vm_backing (m_vm_lazy md2) mat1 md2) HX HA HPok
  (rbn3_rel_of_mid B X pos lyc1 Sc1 W1 (ms_mem ms1) _ _ HM3)).
Qed.
End h.
End f.
End d.
