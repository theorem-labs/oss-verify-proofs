(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-278
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:1570-1572, 1593-1598, 1605-1613 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The
   same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACh9.v:106-109. *)
(* The shared lemmas of seg_K of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), over the statements of
   lib/B/Prog/LLVMFuzzerTestOneInput_seg_K_hand_stmt.v (KPRE, KH, kwin, kkeep, KC, KR): the contract hypotheses
   unpacked from KPRE, the plain-model lemmas the checks read (KModel), the four callees in the journal form
   (strlen and strcmp wrappers, check_str, reac_box_catalogue_defect), the geometry of the start state (k_geom),
   what a piece keeps (k_vm_kept, k_vm_hi, k_garr8_moved), the read-only image at a piece's state (k_aro), the
   call chain at sp = mf (k_achain), and the last piece's step to inv_K_end (k_finish). A piece of the segment
   proves `k_<part>_stmt` using these; lib/B/Prog/LLVMFuzzerTestOneInput_seg_K.v chains the pieces. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81 IdentBlkTail.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require
check_str reac_box_catalogue reac_box_catalogue_defect.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require AStrcmpDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_K_hand_stmt.
(* ---- the plain model facts the checks read (address-free; the lemmas of the released plain walk's
   lib/Prog/Seg/Tac_si.v:20-221, restated here with the k_ prefix, since that file is not a dependency of this
   build) ---------------------------------------------------------------------------------------------------- *)
Module KModel.
Import SlotModel RcIdentModel IdentSpec.
Definition nzb (l : list byte) : bool := forallb (fun b => negb (bz b =? 0)) l.
Lemma nzb_app : forall l1 l2, nzb (l1 ++ l2) = nzb l1 && nzb l2.
Proof. intros. unfold nzb. apply forallb_app. Qed.
Lemma nzb_nth : forall l i, nzb l = true -> (i < length l)%nat -> bz (nthb l i) <> 0.
Proof.
  intros l i H Hi E. unfold nzb in H. rewrite forallb_forall in H.
  specialize (H (nthb l i) (nth_In l (zb 0) Hi)). rewrite E in H. discriminate H.
Qed.
Lemma nzb_notin : forall l, nzb l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. unfold nzb in H. rewrite forallb_forall in H. specialize (H _ Hin).
  vm_compute in H. discriminate H.
Qed.
Lemma nzb_first_zero : forall l, nzb (firstn (first_zero l) l) = true.
Proof.
  induction l as [|b r IH]; cbn [first_zero]; [reflexivity|].
  destruct (bz b =? 0) eqn:E; [reflexivity|].
  unfold nzb in *. cbn [firstn forallb]. rewrite E, IH. reflexivity.
Qed.
Lemma nzb_stem_img : forall f, nzb (stem_img f) = true.
Proof.
  intro f. unfold stem_img.
  destruct (f =? 1); [vm_compute; reflexivity|].
  destruct (f =? 2); [vm_compute; reflexivity|].
  destruct (f =? 3); vm_compute; reflexivity.
Qed.
Lemma nzb_stem : forall inp, nzb (n_stem inp) = true.
Proof.
  intro inp. unfold n_stem. destruct (n_use_said inp); [apply nzb_first_zero | apply nzb_stem_img].
Qed.
Lemma nzb_dec_all : forall x, 0 <= x <= 40 -> nzb (DEC x 1) = true /\ nzb (DEC x 2) = true.
Proof.
  intros x Hx.
  pose proof (z_all_spec (fun x => nzb (DEC x 1) && nzb (DEC x 2)) (Z.to_nat 41) 0
    ltac:(vm_compute; reflexivity) x ltac:(lia)) as H.
  apply andb_true_iff in H. exact H.
Qed.
Lemma n_r0 : forall inp, n_r inp = 0 -> n_wok inp = true /\ n_fits inp = true.
Proof.
  intros inp H. unfold n_r in H. destruct (n_wok inp && n_fits inp) eqn:E; [|discriminate].
  apply andb_true_iff in E. exact E.
Qed.
Lemma n_r_cases : forall inp, n_r inp = 0 \/ n_r inp = -1.
Proof. intro inp. unfold n_r. destruct (n_wok inp && n_fits inp); [left | right]; reflexivity. Qed.
Lemma fits_unfold : forall inp, n_fits inp = true ->
  n_ln inp < t_cap_name inp /\ n_lt inp < t_cap_tok inp /\ n_ld inp < t_cap_disp inp.
Proof.
  intros inp H. unfold n_fits in H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1, H2, H3. auto.
Qed.
Lemma nzb_EXP_NM : forall inp, n_wok inp = true -> nzb (n_EXP_NM inp) = true.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  destruct (nzb_dec_all _ Hi) as [_ Ni]. destruct (nzb_dec_all _ Ho) as [_ No].
  unfold n_EXP_NM. destruct (n_ends_w4 inp); [apply nzb_stem|].
  rewrite !nzb_app, nzb_stem. unfold n_W4. rewrite nzb_app, Ni, No. reflexivity.
Qed.
Lemma nzb_EXP_DP : forall inp, n_wok inp = true -> nzb (n_EXP_DP inp) = true.
Proof.
  intros inp H. destruct (wok_chans inp H) as [Hi Ho].
  destruct (nzb_dec_all _ Hi) as [Ni _]. destruct (nzb_dec_all _ Ho) as [No _].
  unfold n_EXP_DP. rewrite !nzb_app, (nzb_EXP_NM inp H), Ni, No. vm_compute. reflexivity.
Qed.
Lemma lower_bz : forall b, bz (lower b) = if (65 <=? bz b) && (bz b <=? 90) then bz b + 32 else bz b.
Proof.
  intro b. unfold lower. destruct ((65 <=? bz b) && (bz b <=? 90)) eqn:E; [|reflexivity].
  apply andb_true_iff in E as [E1 E2]. apply Z.leb_le in E1, E2.
  unfold zb, bz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. unfold bz in *. lia.
Qed.
Lemma nzb_tok : forall l d, nzb l = true -> nzb (tok_go d l) = true.
Proof.
  induction l as [|b r IH]; intros d H; [reflexivity|].
  unfold nzb in H. cbn [forallb] in H. apply andb_true_iff in H as [Hb Hr].
  cbn [tok_go]. destruct (negb d && (bz b =? 45)); [apply IH; exact Hr|].
  unfold nzb. cbn [forallb]. apply andb_true_iff. split; [|apply IH; exact Hr].
  rewrite lower_bz. apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. apply negb_true_iff. apply Z.eqb_neq.
  pose proof (bz_range b). destruct ((65 <=? bz b) && (bz b <=? 90)); lia.
Qed.
Lemma has_dash_cons : forall b r, has_dash (b :: r) = (bz b =? 45) || has_dash r.
Proof. reflexivity. Qed.
Lemma has_dash_len : forall l, has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.
Lemma tok_len : forall l d,
  length (tok_go d l) = (length l - (if negb d && has_dash l then 1 else 0))%nat.
Proof.
  induction l as [|b r IH]; intros d; [reflexivity|].
  rewrite has_dash_cons. destruct d.
  - cbn [tok_go negb andb length]. rewrite IH. cbn [negb andb]. lia.
  - destruct (bz b =? 45) eqn:E; cbn [tok_go negb andb orb length]; rewrite E; cbn [andb orb].
    + rewrite IH. cbn [negb andb]. lia.
    + cbn [length]. rewrite IH. cbn [negb andb]. destruct (has_dash r) eqn:D; [|lia].
      pose proof (has_dash_len r D). lia.
Qed.
Lemma tk_len : forall inp, Z.of_nat (length (n_TK inp)) = n_lt inp.
Proof.
  intro inp. unfold n_TK, TOK, n_lt, n_ln. rewrite tok_len. cbn [negb andb].
  destruct (has_dash (n_EXP_NM inp)) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.
Lemma tok_app : forall l1 l2 d, tok_go d (l1 ++ l2) = tok_go d l1 ++ tok_go (d || has_dash l1) l2.
Proof.
  induction l1 as [|b r IH]; intros l2 d.
  - cbn. rewrite orb_false_r. reflexivity.
  - cbn [app tok_go]. rewrite has_dash_cons. destruct d; cbn [negb andb orb].
    + rewrite IH. reflexivity.
    + destruct (bz b =? 45) eqn:E; cbn [orb]; rewrite IH; reflexivity.
Qed.
Lemma firstn_snoc : forall (l : list byte) q, (q < length l)%nat ->
  firstn (S q) l = firstn q l ++ [nthb l q].
Proof.
  induction l as [|b r IH]; intros q H; [cbn in H; lia|].
  destruct q as [|q]; [reflexivity|]. cbn [firstn]. unfold nthb. cbn [nth]. cbn in H.
  rewrite (IH q ltac:(lia)). reflexivity.
Qed.
Lemma skipn_nth : forall (l : list byte) q, (q < length l)%nat -> skipn q l = nthb l q :: skipn (S q) l.
Proof.
  induction l as [|b r IH]; intros q H; [cbn in H; lia|].
  destruct q as [|q]; [reflexivity|]. cbn [skipn]. unfold nthb. cbn [nth]. cbn in H.
  rewrite (IH q ltac:(lia)). reflexivity.
Qed.
Lemma has_dash_app : forall l1 l2, has_dash (l1 ++ l2) = has_dash l1 || has_dash l2.
Proof. intros. unfold has_dash. apply existsb_app. Qed.
Definition dropped (l : list byte) (q : nat) : Z := if has_dash (firstn q l) then 1 else 0.
Lemma dropped_S : forall l q, (q < length l)%nat ->
  dropped l (S q) = if (bz (nthb l q) =? 45) || has_dash (firstn q l) then 1 else 0.
Proof.
  intros l q H. unfold dropped. rewrite (firstn_snoc l q H), has_dash_app. cbn [has_dash existsb].
  rewrite orb_false_r, orb_comm. reflexivity.
Qed.
Lemma dropped_range : forall l q, 0 <= dropped l q <= 1.
Proof. intros. unfold dropped. destruct (has_dash _); lia. Qed.
Lemma dropped_0 : forall l, dropped l 0 = 0.
Proof. intros. reflexivity. Qed.
Lemma dropped_le : forall l q, dropped l q <= Z.of_nat q.
Proof.
  intros l q. unfold dropped. destruct (has_dash (firstn q l)) eqn:D; [|lia].
  pose proof (has_dash_len _ D). rewrite length_firstn in H. lia.
Qed.
Lemma tok_at : forall l q, (q < length l)%nat ->
  ~ (bz (nthb l q) = 45 /\ dropped l q = 0) ->
  (Z.to_nat (Z.of_nat q - dropped l q) < length (TOK l))%nat /\
  nthb (TOK l) (Z.to_nat (Z.of_nat q - dropped l q)) = lower (nthb l q).
Proof.
  intros l q Hq Hn.
  assert (ET : TOK l = tok_go false (firstn q l) ++ tok_go (has_dash (firstn q l)) (nthb l q :: skipn (S q) l)).
  { unfold TOK. rewrite <- (firstn_skipn q l) at 1. rewrite tok_app. cbn [orb].
    rewrite (skipn_nth l q Hq). reflexivity. }
  assert (Hl : length (tok_go false (firstn q l)) = Z.to_nat (Z.of_nat q - dropped l q)).
  { rewrite tok_len, length_firstn. unfold dropped. cbn [negb andb].
    destruct (has_dash (firstn q l)) eqn:D; [|lia]. pose proof (has_dash_len _ D) as D1.
    rewrite length_firstn in D1. lia. }
  rewrite ET. cbn [tok_go]. destruct (negb (has_dash (firstn q l)) && (bz (nthb l q) =? 45)) eqn:E.
  - exfalso. apply Hn. apply andb_true_iff in E as [E1 E2]. apply negb_true_iff in E1. apply Z.eqb_eq in E2.
    unfold dropped. rewrite E1. auto.
  - rewrite length_app. cbn [length]. split; [lia|]. unfold nthb.
    rewrite app_nth2 by lia. rewrite Hl, Nat.sub_diag. reflexivity.
Qed.
Lemma tok_dash_drop : forall l q, (q < length l)%nat -> bz (nthb l q) = 45 -> dropped l q = 0 ->
  dropped l (S q) = 1.
Proof. intros l q Hq E D. rewrite (dropped_S l q Hq), E. reflexivity. Qed.
Lemma tok_other_keep : forall l q, (q < length l)%nat -> ~ (bz (nthb l q) = 45 /\ dropped l q = 0) ->
  dropped l (S q) = dropped l q.
Proof.
  intros l q Hq Hn. rewrite (dropped_S l q Hq). unfold dropped in *.
  destruct (has_dash (firstn q l)); [rewrite orb_true_r; reflexivity|].
  rewrite orb_false_r. destruct (Z.eqb_spec (bz (nthb l q)) 45); [exfalso; apply Hn; auto | reflexivity].
Qed.
Lemma tok_len_full : forall l, Z.of_nat (length (TOK l)) = Z.of_nat (length l) - dropped l (length l).
Proof.
  intro l. unfold TOK, dropped. rewrite tok_len, firstn_all. cbn [negb andb].
  destruct (has_dash l) eqn:D; [|lia]. pose proof (has_dash_len _ D). lia.
Qed.
Definition lw (c : Z) : Z := if (65 <=? c) && (c <=? 90) then c + 32 else c.
Lemma lower_lw : forall b, bz (lower b) = lw (bz b).
Proof. intro b. rewrite lower_bz. reflexivity. Qed.
End KModel.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
#[local] Notation KPREn := (KPRE B RLO RHI LLVMF_STK arodata_okS G).
#[local] Notation KHn := (KH B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation KCn := (KC B LLVMF_STK).
#[local] Notation KENDn := (inv_K_end B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
  asink_syms_T KS asink_none ameta_inv arodata_okS).
Hypothesis HPRE : KPREn.

(* ---- the contract hypotheses, unpacked once --------------------------------------------------------------- *)
Lemma k_laws : AR_laws SEGS B. Proof. exact (proj1 (proj2 HPRE)). Qed.
Lemma k_stk : STK_LLVMF <= LLVMF_STK. Proof. exact (proj1 HPRE). Qed.
Lemma k_tl : PALib B. Proof. exact (proj1 (proj2 (proj2 HPRE))). Qed.
Lemma k_psig : identb_prog_sig_ok (PI := PI). Proof. exact (proj1 (proj2 (proj2 (proj2 HPRE)))). Qed.
Lemma k_ro : ro_below_ofl SEGS pa_relro_lo pa_relro_hi. Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 HPRE))))). Qed.
Lemma k_hro : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE)))))). Qed.
Lemma k_gm : globs_marked SEGS B G.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))). Qed.
Lemma k_iv : img_shadow_vis SEGS B.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE)))))))). Qed.
Lemma k_gcat : In (VAL (A_OBJ 28), 3256) G.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))))). Qed.
Lemma k_himg : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE)))))))))). Qed.
Lemma k_astrlen : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))))))). Qed.
Lemma k_astrcmp : astrcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_strcmp).
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE)))))))))))). Qed.
Lemma k_ajio : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))))))))). Qed.
Lemma k_hchk : check_str.tcheck_str_spec B.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE)))))))))))))). Qed.
Lemma k_hcat : reac_box_catalogue.tcat_spec B.
Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))))))))))). Qed.
Lemma k_hcatd : reac_box_catalogue_defect.treac_box_catalogue_defect_spec B G.
Proof. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HPRE))))))))))))))). Qed.

(* ---- the wrappers and the program callees in the journal form ------------------------------------------------- *)
(* The strlen wrapper on a journal (as reac_box_catalogue_defect.v's aj_strcmp_at for strcmp). *)
Lemma k_strlen_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  first_byte SEGS W memT x (k + 1) 0 k ->
  src_ok SEGS W regsT memT x (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x (k + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (k + 1) ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
  (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
  HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hsx Hbx Hmx Hrx Hhx Hsl Hrom.
pose proof k_laws as LAWS.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPREc : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (k_astrlen lyc Sc W regsT memT mdc x k HPREc Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsx
    ltac:(rewrite Hsp'; exact Hbx) Hmx Hrx Hhx Hsl Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* The strcmp wrapper on a journal (AStrcmpDef's str_meet / strcmp_res form). *)
Lemma k_strcmp_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k c1 c2 (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> 0 < x -> 0 < y ->
  k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 -> y + k + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  AStrcmpDef.str_meet SEGS W memT x y k c1 c2 ->
  src_ok SEGS W regsT memT x (k + 1) -> src_ok SEGS W regsT memT y (k + 1) ->
  (forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a <= y + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x (k + 1) -> amem_range y (k + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (k + 1) -> shadow_hull_vis (aview SEGS (w_H W) memT) x (k + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF y (k + 1) -> shadow_hull_vis (aview SEGS (w_H W) memT) y (k + 1) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strcmp)) memT (seg_rom SEGS)) mdc)
  (fun W2 c3 => W2 = W /\ exists regs2 mem2 md2,
    c3 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
    aregs_preserved regsT regs2 /\ getr regs2 10 = w64 (AStrcmpDef.strcmp_res c1 c2) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
      aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
    (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x y k c1 c2 o raw
  HJ Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hmeet Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
pose proof k_laws as LAWS.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (ESTACK = 4096) as Hes by reflexivity. assert (ASTACK = 16384) as Has by reflexivity.
assert (HPREc : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try zlia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; zlia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; zlia).
eapply SRr_mono.
{ exact (k_astrcmp lyc Sc W regsT memT mdc x y k c1 c2 HPREc Hlo2 Hpres2E Ha0 Ha1 Hx0 Hy0 Hk1 Hxk Hyk Hmeet Hsx Hsy
    ltac:(rewrite Hsp'; exact Hbx) ltac:(rewrite Hsp'; exact Hby) Hmx Hmy Hrx Hhx Hry Hhy). }
cbv beta. intros W2 c3 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
  (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; zlia.
  - exact HAR2.
  - reflexivity. - reflexivity. - zlia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. split; [exact Hfr | exact Hpres2].
Qed.

(* check_str (afn_pre form) called from a journal: YC85.cl_callS with the callee's own post. *)
Lemma k_check_str_at : forall W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch1 r x c,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> check_str.CHECK_STR_STK - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  aro_unowned SEGS B (aview SEGS (w_H W) memc) ->
  getr regsc 10 = w64 r -> getr regsc 11 = w64 x -> getr regsc 12 = w64 c ->
  - 2 ^ 31 <= r < 2 ^ 31 -> 0 <= c < 2 ^ 64 ->
  (0 <= r -> check_str.tcheck_str_ok W regsc memc r x c) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_check_str)) memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 0) /\
    ajournal SEGS B check_str.CHECK_STR_STK (sp0 + o) [] lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 0 /\
    aregs_preserved regsc regs2 /\ (ly2 = lyc /\ S2 = Sc /\ W2 = W)).
Proof.
intros W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch1 r x c
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hch Hrom H10 H11 H12 Hr Hc HOK.
apply (cl_callS B k_laws W regsc memc _ STK sp0 FP ly S W0 mem md own lyc Sc mdc k check_str.CHECK_STR_STK [] 0 o raw ch1
  (fun ly' S' W' _ _ _ => ly' = lyc /\ S' = Sc /\ W' = W)); try assumption.
- unfold check_str.CHECK_STR_STK, ESTACK. lia.
- intros HPREc.
  pose proof (k_hchk lyc Sc W regsc memc mdc ch1 r x c HPREc Hrom H10 H11 H12 Hr Hc HOK) as H.
  eapply SRr_mono; [exact H|]. cbv beta.
  intros W2 c2 _ (ly' & S' & regs' & mem' & md' & Ec & HJ' & HP' & HK').
  exists ly', S', regs', mem', md'. rewrite Hra in Ec. split; [exact Ec|]. split; [exact HJ'|].
  split; [exact HP' | exact HK'].
- intros a (r' & [] & _).
Qed.

(* reac_box_catalogue_defect (afn_pre form) called from a journal. *)
Lemma k_defect_at : forall W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw ch1
  (e i o' d I O P : Z) (sP sd : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  getr regsc 10 = w64 e -> getr regsc 11 = w64 i -> getr regsc 12 = w64 o' -> getr regsc 13 = w64 d ->
  0 <= e < 2 ^ 64 -> -2 ^ 31 <= i < 2 ^ 31 -> -2 ^ 31 <= o' < 2 ^ 31 -> 0 <= d < 2 ^ 64 ->
  -2 ^ 31 <= I < 2 ^ 31 -> -2 ^ 31 <= O < 2 ^ 31 -> 0 <= P < 2 ^ 64 ->
  (e <> 0 ->
   IMG_LO <= e + 8 /\ e + 24 <= IMG_TOP /\ reac_box_catalogue_defect.catd_glob G (e + 8) 16 /\
   e mod 8 = 0 /\
   (e + 24 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= e + 8) /\
   (e + 24 <= VAL (A_OBJ 31) \/ VAL (A_OBJ 31) + 8 <= e + 8) /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 8) 8 P /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 16) 4 I /\
   val_mem SEGS (mrestrict (w_H W) memc) (e + 20) 4 O) ->
  (e <> 0 -> d <> 0 -> P <> 0 ->
   reac_box_catalogue_defect.catd_rostr G W memc P sP /\ reac_box_catalogue_defect.catd_hpstr B lyc Sc W memc d sd) ->
  SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_reac_box_catalogue_defect)) memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + 0) /\
    ajournal SEGS B reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK (sp0 + o) [] lyc Sc W memc mdc []
      ly2 S2 W2 mem2 md2 0 /\
    aregs_preserved regsc regs2 /\
    (getr regs2 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o' d I O P sP sd) /\
     ly2 = lyc /\ S2 = Sc /\ W2 = W /\
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (sp0 + o - reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= a < sp0 + o) ->
        aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a))).
Proof.
intros W regsc memc STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw ch1 e i o' d I O P sP sd
  HJ Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hra4 Hch H10 H11 H12 H13 Re Ri Ro Rd RI ROO RP HROW HSTR.
apply (cl_callS B k_laws W regsc memc _ STK sp0 FP ly S W0 mem md own lyc Sc mdc k
  reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK [] 0 o raw ch1
  (fun ly' S' W' regs' mem' _ =>
     getr regs' 10 = w64 (reac_box_catalogue_defect_c.CATALOGUE_DEFECT_MASK e i o' d I O P sP sd) /\
     ly' = lyc /\ S' = Sc /\ W' = W /\
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (sp0 + o - reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK <= a < sp0 + o) ->
        aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a))); try assumption.
- unfold reac_box_catalogue_defect.REAC_BOX_CATALOGUE_DEFECT_STK, ESTACK. lia.
- intros HPREc.
  pose proof (k_hcatd lyc Sc W regsc memc mdc ch1 e i o' d I O P sP sd HPREc H10 H11 H12 H13 Re Ri Ro Rd RI ROO RP HROW HSTR) as H.
  eapply SRr_mono; [exact H|]. cbv beta.
  intros W2 c2 _ (ly' & S' & regs' & mem' & md' & Ec & HJ' & HP' & (HK1 & HK2 & HK3 & HK4 & _ & HKEEP)).
  rewrite Hsp in HKEEP.
  exists ly', S', regs', mem', md'. rewrite Hra in Ec. split; [exact Ec|]. split; [exact HJ'|].
  split; [exact HP' | exact (conj HK1 (conj HK2 (conj HK3 (conj HK4 HKEEP))))].
- intros a (r' & [] & _).
Qed.

(* ---- the geometry of the start state, and what the pieces keep ------------------------------------------------ *)
Section run.
Variables (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
  (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model).
Hypothesis HKH : KHn g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2.

Lemma k_geom :
  alloc_ceiling + 8192 <= mf - 8208 /\ mf + 320 <= e_sp0 g /\ e_sp0 g <= 2 ^ 47 /\
  e_sp0 g mod 16 = 0 /\ e_sp0 g - 336 <= mf /\ mf mod 32 = 0 /\ e_sp0 g - LLVMF_STK <= mf - 8208 /\
  4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ in_app (SFa g pos) 1024 /\ SFa g pos mod 64 = 0 /\
  frame_addr ly2 4 pos = SFa g pos /\
  shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8 /\ 0 <= shadow_addr (SFa g pos) /\
  shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\ In (4, pos) (frames S2).
Proof.
pose proof HKH as (HJ2 & HFR & _ & _ & _ & HEC & _).
pose proof k_laws as LAWS. pose proof k_stk as HSTK.
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
pose proof HEC as (_ & _ & _ & Hmfb & Hmf32 & _).
pose proof asan_consts as (C1 & _).
assert (Has : ASTACK = 16384) by reflexivity.
unfold STK_LLVMF in HSTK.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. change (fs_frame_bytes 4) with 1024 in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
assert (D8 : 0 <= SFa g pos / 8 <= alloc_ceiling / 8) by (split; [apply Z.div_pos | apply Z.div_le_mono]; lia).
assert (D8' : 8 * (alloc_ceiling / 8) <= alloc_ceiling) by (apply Z.mul_div_le; lia).
assert (SH1 : 0 <= shadow_addr (SFa g pos)) by (rewrite Esh; unfold SHADOW_OFF; lia).
assert (SH2 : shadow_addr (SFa g pos) + 128 <= alloc_ceiling) by (rewrite Esh; unfold SHADOW_OFF; lia).
unfold e_sp0 in *. unfold ESTACK in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Hsp0al|]. split; [lia|]. split; [exact Hmf32|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HSFapp|]. split; [exact HSF64|].
split; [exact EFa|]. split; [exact Esh|]. split; [exact SH1|]. split; [exact SH2 | exact Hin4].
Qed.

Lemma k_vm_hi : forall mem a n v, kkeep B g pos mf ly2 S2 W2 mem2 mem -> mf <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem) a n v.
Proof.
intros mem a n v HKP H0 H1 Hv.
pose proof k_geom as (G1 & _ & _ & _ & _ & _ & _ & G8 & G9 & _ & _ & _ & _ & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 mem a n v); [|exact Hv].
intros k Hk. apply (proj1 HKP); [clear - H0 H1 Hk G1 C1; lia | clear - H0 Hk G1 C1; lia].
Qed.
(* A range of the entry's own frame, outside `count`. *)
Lemma k_vm_frame : forall mem off n v, kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  0 <= off -> off + Z.of_nat n <= 1024 -> (off + Z.of_nat n <= 720 \/ 728 <= off) ->
  val_mem SEGS (rd W2 mem2) (SFa g pos + off) n v -> val_mem SEGS (rd W2 mem) (SFa g pos + off) n v.
Proof.
intros mem off n v HKP H0 H1 H2 Hv.
pose proof k_geom as (G1 & _ & _ & _ & _ & _ & _ & G8 & G9 & G10 & _ & G12 & G13 & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 mem (SFa g pos + off) n v); [|exact Hv].
intros k Hk. apply (proj2 (proj2 HKP)).
- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite G12. change (fs_frame_bytes 4) with 1024.
  clear - H0 H1 Hk. lia.
- unfold V_cnt. clear - H0 H1 H2 Hk. lia.
- intros Hw. apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024 (SFa g pos + off + k));
    [exact G8 | clear - G9 C1; lia | exact G10 | | clear - H0 H1 Hk; lia].
  rewrite Hw, G13. unfold SHADOW_OFF. clear. lia.
Qed.
(* A range of a live heap block. *)
Lemma k_vm_blk : forall mem b n0 off n v, kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  In (b, n0) (ablocks B ly2 S2) -> 0 <= off -> off + Z.of_nat n <= req_size n0 ->
  val_mem SEGS (rd W2 mem2) (b + off) n v -> val_mem SEGS (rd W2 mem) (b + off) n v.
Proof.
intros mem b n0 off n v HKP Hin H0 H1 Hv.
apply (val_mem_kept SEGS (w_H W2) (w_H W2) mem2 mem (b + off) n v); [|exact Hv].
intros k Hk. replace (b + off + k) with (b + (off + k)) by lia.
apply (proj1 (proj2 HKP) b n0 (off + k) Hin). clear - H0 H1 Hk. lia.
Qed.
Lemma k_garr8_moved : forall H H' (m m' : word -> option byte) a l,
  (forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS H' m' (a + k) = aview SEGS H m (a + k)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (val_mem_moved SEGS H H' m m' (a + Z.of_nat j) (a + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros k Hk1. replace (a + Z.of_nat j + k) with (a + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.
(* The read-only image at the state of a piece: what the wrappers and HIMG ask. *)
Lemma k_aro : forall mem md,
  ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
    ly2 S2 W2 mem md (4 * Z.of_nat (m_nrec g) + 7) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem) /\
  aro_unowned SEGS B (aview SEGS (w_H W2) mem).
Proof.
intros mem md HJ.
pose proof HKH as (_ & _ & _ & _ & _ & HEC & _).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HPREe & _).
unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPREe.
destruct HPREe as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HAROS & _).
pose proof k_ro as RO.
pose proof (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  HJ (k_hro _ HAROS)) as HAP.
split; [exact HAP | exact (aro_unowned_of_arodata SEGS pa_relro_lo pa_relro_hi B _ HAP)].
Qed.

(* The call chain at sp = mf: the entry's own frame record, or none. *)
Lemma k_achain : forall mem, kkeep B g pos mf ly2 S2 W2 mem2 mem ->
  exists ch, achain ly2 (aview SEGS (w_H W2) mem) mf (e_sp0 g) ch.
Proof.
intros mem HKP.
pose proof HKH as (HJ2 & HFR & _ & _ & _ & HEC & _).
pose proof k_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & _).
pose proof asan_consts as (C1 & _).
destruct HEC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vra & Vs0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HPREe & _).
pose proof HPREe as HPRE'. unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPRE'.
destruct HPRE' as (HFN & Hraz & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & Hstk0 & _ & Hch0 & _).
pose proof HJ2 as (_ & Hly2 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
assert (Hach : achain ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) (e_sp0 g) (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop|]. change (spZ (e_regs g)) with (e_sp0 g) in Hch0. exact Hch0. }
assert (KEEPhi : forall a, e_sp0 g <= a < 2 ^ 64 -> aview SEGS (w_H W2) mem a = aview SEGS (w_H (e_W g)) (e_mem g) a).
{ intros a Ha. rewrite (proj1 HKP a ltac:(clear - C1 G1 G15 G2 G3 G9 Ha; lia) ltac:(clear - C1 G1 G15 G2 G3 G9 Ha; lia)).
  apply F1; [clear - C1 G1 G15 G2 G3 G9 Ha; lia | clear - C1 G1 G15 G2 G3 G9 Ha; lia]. }
pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra. change (bv_modulus 64) with (2 ^ 64) in Rra.
pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r. change (bv_modulus 64) with (2 ^ 64) in Rs0r.
destruct (Z_lt_le_dec (e_sp0 g) (ly_top ly2 - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))].
  apply (achain_push ly2 (aview SEGS (w_H (e_W g)) (e_mem g)) (aview SEGS (w_H W2) mem)
    (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
  + rewrite ETop. clear - C1 G1 G15 G2 G3 G9 H47 Hshi Htop1 Htop2. lia.
  + intros a Ha. apply KEEPhi. clear - C1 G1 G15 G2 G3 G9 Ha; lia.
  + apply rdword_of_val_mem; [|unfold raZ in Hraz; clear - C1 G1 G15 G2 G3 G9 Hraz Rra; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem (e_sp0 g - 8) (e_sp0 g - 8) 8 RA_LLVMF); [|exact Vra].
    intros kk Hkk. apply (proj1 HKP (e_sp0 g - 8 + kk)); [clear - C1 G1 G15 G2 G3 G9 Hkk; lia|].
    unfold kwin, V_cnt. clear - C1 G1 G15 G2 G3 G9 Hkk. lia.
  + apply rdword_of_val_mem; [|unfold s0Z; clear - C1 G1 G15 G2 G3 G9 Rs0r; lia].
    apply (val_mem_moved SEGS (w_H W2) (w_H W2) mem2 mem (e_sp0 g - 16) (e_sp0 g - 16) 8 (s0Z (e_regs g))); [|exact Vs0].
    intros kk Hkk. apply (proj1 HKP (e_sp0 g - 16 + kk)); [clear - C1 G1 G15 G2 G3 G9 Hkk; lia|].
    unfold kwin, V_cnt. clear - C1 G1 G15 G2 G3 G9 Hkk. lia.
  + rewrite <- Hraz. exact Hra4.
  + clear - C1 G1 G15 G2 G3 G9. lia.
  + pose proof (Z.div_mod (e_sp0 g) 16 ltac:(lia)) as D. rewrite G4, Z.add_0_r in D.
    replace (e_sp0 g) with ((2 * (e_sp0 g / 16)) * 8) by lia. apply Z_mod_mult.
  + exact Hlt.
  + clear - C1 G1 G15 G2 G3 G9. lia.
- exists []. left. split; [right; left; exact Hge | reflexivity].
Qed.

(* The end of the walk: inv_K_end from the state of the last piece. *)
Lemma k_finish : forall regs mem md, KCn g pos mf tk ly2 S2 W2 mem2 regs mem md ->
  KENDn g pos mf nm tk dp W2 (cfg_at SEGS (BASE + 0x1bec) regs mem md).
Proof.
intros regs mem md (HJ & HKP & Rsp & Rs1 & Rs0 & Rgp & Rtp & Rtk & Rsh).
pose proof HKH as (HJ2 & HFR & HK & HMLE & HMOK & HEC & HHB & HSR & _ & _ & _ & _ & _ & V152 & V184 & _).
pose proof k_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & Hin4).
pose proof k_laws as LAWS. pose proof asan_consts as (C1 & _).
unfold inv_K_end, acut.
exists ly2, S2, regs, mem, md.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HFR|]. split; [exact HK|].
split; [exact HMLE|]. split; [exact HMOK|].
split.
- destruct HEC as (_ & _ & _ & Hmfb & Hmf32 & _ & _ & V16 & V64 & V192 & V168 & Vra & Vs0 & W9 & W18 & W19 & W20 &
    W21 & W22 & W23 & W24 & W25 & W26 & W27 & Vflag & HPREe & Hfds & Hfs & Hinb).
  destruct (k_ajio _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as [Efd Efs].
  unfold ecommon.
  split; [exact Rsp|]. split; [exact Rs1|]. split; [exact Rs0|]. split; [exact Hmfb|]. split; [exact Hmf32|].
  split; [exact Rgp|]. split; [exact Rtp|].
  do 17 (split; [apply (k_vm_hi mem _ 8); [exact HKP | clear - Hmfb G2 G3; unfold e_sp0 in *; lia
                                          | clear - G3 Hmfb; unfold e_sp0 in *; lia | assumption]|]).
  split.
  { apply (k_vm_frame mem 1016 8 _ HKP); [clear; lia | clear; cbn; lia | clear; cbn; lia | exact Vflag]. }
  split; [exact HPREe|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|].
  unfold e_pre, tLLVMFuzzerTestOneInput_pre in HPREe.
  destruct HPREe as (_ & _ & _ & _ & Hinp & Hlen & _).
  unfold bytes_at8 in *. apply (k_garr8_moved (w_H W2) (w_H W2) mem2 mem _ _); [|exact Hinb].
  intros j Hj. rewrite length_map, <- Hlen in Hj.
  destruct Hinp as [[Hn0 _] | [[Hn0 Hn26] Hine]]; [clear - Hj Hn0; lia|].
  pose proof HJ2 as (HAR2 & _).
  assert (Hine2 : In (e_p g, e_n g) (ablocks B ly2 S2)).
  { destruct HHB as [Hperm _]. apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. right. exact Hine. }
  destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) HAR2 Hine2) as (_ & Hp4096 & Hpce & Hpapp & _).
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 (e_p g) (e_n g) 4 pos HAR2 Hine2 Hin4) as Hdf.
  unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite G12 in Hdf. change (fs_frame_bytes 4) with 1024 in Hdf.
  pose proof (req_size_pos (e_n g) ltac:(lia)) as Hrq.
  assert (Hrn : req_size (e_n g) = e_n g) by (unfold req_size; destruct (Z.eqb_spec (e_n g) 0); lia).
  apply (proj1 (proj2 HKP) (e_p g) (e_n g) j Hine2). clear - Hj Hrn Hrq. lia.
- split; [exact HHB|]. split; [unfold sh_reg; exact Rsh|]. split; [exact Rtk|].
  split; apply (k_vm_hi mem _ 8); first [exact HKP | clear - G2 G3; unfold e_sp0 in *; lia | assumption].
Qed.

End run.
End c.
End b.
End a.
