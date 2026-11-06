(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 527 of its 583 lines of code are new or changed and 458 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): row T5's boundaries at the re-hiding
   contract: the journals (AJ / AJW) at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   stretch statements CT5_ATL3 / CT5_ATC / CT5_AT_L1 / CT5_AT_L2 / CT5_L0_STMT at YA0nH.SRr' SEGS RZ_cf. Names and
   binders unchanged. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T5 (CRT-B-L012): the ROW'S BOUNDARIES. L0 (+0x478)
   -> L1 (+0x4f8, the at-search head, index i) -> L2 (+0x56c, at found) -> L3 (+0x5b4) / C (+0x6f8); the stretches are
   Crt102B_T5_L0.v / _L1.v / _L2.v, the row theorem
   Crt102B_T5.v.

   proves no function (kind: segment lemma support).

   THE B' CODE (fuzz_preset.c new:740-748): L0 `sd s8, 0(s1)` (saved); `bnez s5` -> abort (new:740, not taken:
   ct5_granted); &doc->n's shadow; a3 = doc->n, a1 = 0x48(s1) (U's copy of doc->n), a2 = (a1 == a3); 0x30(s1) =
   &doc->keys, 8(s1) = doc->n; `beqz a3` -> L2; `bne a1, a3` -> L2 (not taken); &doc->keys's shadow; s10 = doc->keys,
   s5 = 1, 0x28(s1) = (keys <> 0), 0x18(s1) = (keys <> 0 && keys aligned), 0x10(s1) = MOD_AT, s8 = s10, 0x20(s1) = keys.
   L1 (index i: s5 = i + 1, s8 = s10 = keys + 8 i): UBSan checks of keys + 8 i (-> +0x810, not taken), 0x40(s1) = i,
   keys[i]'s shadow, `__wrap_strcmp (keys[i], MOD_AT)` +0x53c; a1 = (hit ? i : n), a2 = (a1 == n); `bgeu s5, n` -> L2;
   s5 += 1, s10 += 8, s8 += 8; `beq a1, n` -> L1. L2: 0x40(s1) = a1 (at); back.n vs n + a2 (`bne` -> abort, new:748, not
   taken: Crt102Model.cm_members_crt); `beqz n` -> C; s8 = s10 = s5 = 0, s6 = shadow (&doc->keys), 0x48(s1) =
   &doc->kids, 0x28(s1) = shadow (&doc->kids); L3.

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): every cut of the row (L0_B, L1, L2, L3_B, C_B) carries crt_live
   at kb = prh_wk F_check_round_trip (the notation liveB, so crt5_pre / crt5_core and the stretch statements carry it)
   and its journal at a budget WS with wbudget [] (prh_wk F_check_round_trip) WS. ct5_live_run / ct5_pre_run /
   ct5_core_run read the run's journal at a budget WS with that bound (the A' twin's convention,
   Crt102Loops.cl_live_keep).
*)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp WriterSpec PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_Supply PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree Crt102B_T6.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* The re-hiding move's world relation and step relation (YA0nH), the zone (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.

(* the last of a writer's grow calls is its final capacity (WriterSpec.grow_calls / grow_cap) *)
Lemma ct5_last_cons : forall (L : list Z) a d, last (a :: L) d = last L a.
Proof.
intros L. induction L as [|b L IH]; intros a d; [reflexivity|].
change (last (a :: b :: L) d) with (last (b :: L) d). rewrite (IH b d), (IH b a). reflexivity.
Qed.
Lemma ct5_last_grow : forall ls x c, last (WriterSpec.grow_calls x c ls) c = WriterSpec.grow_cap x c ls.
Proof.
induction ls as [|l ls IH]; intros x c; cbn [WriterSpec.grow_calls WriterSpec.grow_cap]; [reflexivity|].
destruct (c <? x + l + 1); [|apply IH]. rewrite ct5_last_cons. apply IH.
Qed.

(* ---- EVERY REQUEST OF ONE pj_write IS AT MOST ITS LAST BUFFER (RQW, PRH_FnCheck.v): a grow's request is the
   doubling chain from 4096 up to the text it needs, and the text never passes the whole document. With the text's
   RQA_crt t <= most, a refused request of the rewrite's pj_write sets g_ran_out (prh_oks), so at L0 (ran' = 0) the
   write was not refused. ---- *)
Definition ct5_pw (c : Z) : Prop := exists k, 0 <= k /\ c = 4096 * 2 ^ k.
Lemma ct5_pw_dbl : forall f c need, ct5_pw c -> ct5_pw (WriterSpec.dbl f c need).
Proof.
induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [exact Hc|].
destruct (need <=? c); [exact Hc|]. apply IH. destruct Hc as (k & Hk & ->). exists (k + 1). split; [lia|].
rewrite Z.pow_add_r by lia. lia.
Qed.
Lemma ct5_pw_step : forall c M, ct5_pw c -> ct5_pw M -> c < M -> 2 * c <= M.
Proof.
intros c M (k & Hk & ->) (j & Hj & ->) Hlt.
destruct (Z.le_gt_cases j k) as [Hjk | Hkj].
- exfalso. pose proof (Z.pow_le_mono_r 2 j k ltac:(lia) Hjk). lia.
- pose proof (Z.pow_le_mono_r 2 (k + 1) j ltac:(lia) ltac:(lia)). rewrite Z.pow_add_r in H by lia. lia.
Qed.
Lemma ct5_dbl_le : forall f c need M, ct5_pw c -> ct5_pw M -> c <= M -> need <= M -> WriterSpec.dbl f c need <= M.
Proof.
induction f as [|f IH]; intros c need M Hc HM HcM HnM; cbn [WriterSpec.dbl]; [exact HcM|].
destruct (Z.leb_spec need c); [exact HcM|].
apply IH; [| exact HM | apply ct5_pw_step; [exact Hc | exact HM | lia] | exact HnM].
destruct Hc as (k & Hk & ->). exists (k + 1). split; [lia|]. rewrite Z.pow_add_r by lia. lia.
Qed.
Lemma ct5_dbl_ge : forall f c need, ct5_pw c -> need <= c * 2 ^ Z.of_nat f -> need <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc Hn; cbn [WriterSpec.dbl]; [cbn in Hn; lia|].
destruct (Z.leb_spec need c); [lia|]. apply IH.
- destruct Hc as (k & Hk & ->). exists (k + 1). split; [lia|]. rewrite Z.pow_add_r by lia. lia.
- rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia.
Qed.
Lemma ct5_newcap0 : forall N, 0 < N <= 2 ^ 64 -> ct5_pw (WriterSpec.newcap 0 N) /\ N <= WriterSpec.newcap 0 N.
Proof.
intros N HN. unfold WriterSpec.newcap. change (0 =? 0) with true. cbv iota.
split; [apply ct5_pw_dbl; exists 0; split; [lia | reflexivity]|].
apply ct5_dbl_ge; [exists 0; split; [lia | reflexivity]|]. change (Z.of_nat 64) with 64. lia.
Qed.
Lemma ct5_newcap_le : forall c need N, (c = 0 \/ ct5_pw c) -> c <= WriterSpec.newcap 0 N -> need <= N ->
  0 < N <= 2 ^ 64 -> WriterSpec.newcap c need <= WriterSpec.newcap 0 N /\ ct5_pw (WriterSpec.newcap c need).
Proof.
intros c need N Hc HcM Hn HN. destruct (ct5_newcap0 N HN) as (HM & HNM).
assert (H4 : 4096 <= WriterSpec.newcap 0 N).
{ destruct HM as (j & Hj & E). rewrite E. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj). lia. }
unfold WriterSpec.newcap at 1 3. destruct Hc as [-> | Hc].
- change (0 =? 0) with true. cbv iota.
  split; [apply ct5_dbl_le; [exists 0; split; [lia | reflexivity] | exact HM | exact H4 | lia]|].
  apply ct5_pw_dbl. exists 0. split; [lia | reflexivity].
- assert (Hc0 : c <> 0) by (destruct Hc as (k & Hk & ->); pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk); lia).
  rewrite (proj2 (Z.eqb_neq c 0) Hc0).
  split; [apply ct5_dbl_le; [exact Hc | exact HM | exact HcM | lia] | apply ct5_pw_dbl; exact Hc].
Qed.
Lemma ct5_skipn_app : forall {A} (l r : list A), skipn (length l) (l ++ r) = r.
Proof. intros A l. induction l as [|a l IH]; intros r; [reflexivity|]. cbn [length app skipn]. apply IH. Qed.
Lemma ct5_putN_reqs : forall P ok st N, 0 < N <= 2 ^ 64 ->
  (WriterApp.w_cap st = 0 \/ ct5_pw (WriterApp.w_cap st)) -> WriterApp.w_cap st <= WriterSpec.newcap 0 N ->
  Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length (concat P)) + 1 <= N ->
  Forall (fun c => c <= WriterSpec.newcap 0 N)
    (skipn (length (WriterApp.w_calls st)) (WriterApp.w_calls (PRH_FnWriter.prhWriter_putN ok st P))).
Proof.
induction P as [|b P IH]; intros ok st N HN Hc HcM Hlen.
- cbn [PRH_FnWriter.prhWriter_putN]. rewrite <- (app_nil_r (WriterApp.w_calls st)) at 2. rewrite ct5_skipn_app.
  apply Forall_nil.
- cbn [concat] in Hlen. rewrite length_app in Hlen. cbn [PRH_FnWriter.prhWriter_putN].
  destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G.
  + set (st' := PRH_FnWriter.prhWriter_put1 (hd true ok) st b).
    set (c' := WriterSpec.newcap (WriterApp.w_cap st) (PRH_FnWriter.prhWriter_need st b)).
    assert (Hneed : PRH_FnWriter.prhWriter_need st b <= N) by (unfold PRH_FnWriter.prhWriter_need; lia).
    destruct (ct5_newcap_le (WriterApp.w_cap st) _ N Hc HcM Hneed HN) as (Hc'M & Hc'pw). fold c' in Hc'M, Hc'pw.
    assert (Ecalls : WriterApp.w_calls st' = WriterApp.w_calls st ++ [c']) by exact (PRH_Supply.sup_put1_calls _ st b G).
    assert (Hst' : (WriterApp.w_cap st' = WriterApp.w_cap st \/ WriterApp.w_cap st' = c') /\
      Z.of_nat (length (WriterApp.w_text st')) <= Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b)).
    { unfold st', PRH_FnWriter.prhWriter_put1. rewrite G. fold c'.
      destruct (WriterApp.w_cnt st =? WriterApp.w_fail st); [cbn; split; [left; reflexivity | lia]|].
      destruct (hd true ok); cbn [WriterApp.w_cap WriterApp.w_text]; [|split; [left; reflexivity | lia]].
      split; [right; reflexivity|]. rewrite length_app. lia. }
    destruct (PRH_Supply.sup_putN_calls P (tl ok) st') as [L E].
    pose proof (IH (tl ok) st' N HN) as IH'. rewrite E, ct5_skipn_app in IH'. rewrite E, Ecalls, <- app_assoc.
    rewrite ct5_skipn_app. cbn [app]. apply Forall_cons; [exact Hc'M|].
    destruct Hst' as ([Ecap | Ecap] & Htx).
    * apply IH'; [rewrite Ecap; exact Hc | rewrite Ecap; exact HcM | lia].
    * apply IH'; [rewrite Ecap; right; exact Hc'pw | rewrite Ecap; exact Hc'M | lia].
  + destruct (PRH_Supply.sup_put1_keep st b G) as (Ec & _ & _).
    assert (Hst' : WriterApp.w_cap (WriterApp.put1 st b) = WriterApp.w_cap st /\
      Z.of_nat (length (WriterApp.w_text (WriterApp.put1 st b))) <=
        Z.of_nat (length (WriterApp.w_text st)) + Z.of_nat (length b)).
    { unfold PRH_FnWriter.prhWriter_grows, PRH_FnWriter.prhWriter_need in G. unfold WriterApp.put1.
      destruct (WriterApp.w_failed st =? 0) eqn:F; cbn [negb andb] in *; [|split; [reflexivity | lia]].
      apply Z.ltb_ge in G. rewrite (proj2 (Z.leb_le _ _) G). cbn [WriterApp.w_cap WriterApp.w_text].
      split; [reflexivity|]. rewrite length_app. lia. }
    rewrite <- Ec. destruct Hst' as (Ecap & Htx).
    apply IH; [exact HN | rewrite Ecap; exact Hc | rewrite Ecap; exact HcM | lia].
Qed.
Lemma ct5_wreq_le : forall ok cnt fail t p i, Z.of_nat (length (WriterValue.wdoc t p)) + 1 <= 2 ^ 64 ->
  nth i (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 cnt fail) (WriterValue.wdpieces t p)) 0 <= RQW t p.
Proof.
intros ok cnt fail t p i Hl. unfold PRH_FnWriter.prhWriter_reqs, RQW.
set (N := Z.of_nat (length (WriterValue.wdoc t p)) + 1).
assert (HN : 0 < N <= 2 ^ 64) by (unfold N; lia).
destruct (ct5_newcap0 N HN) as ((j & Hj & EM) & _).
assert (HF := ct5_putN_reqs (WriterValue.wdpieces t p) ok (WriterApp.w0 cnt fail) N HN (or_introl eq_refl)
  ltac:(cbn [WriterApp.w0 WriterApp.w_cap]; rewrite EM; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); lia)
  ltac:(cbn [WriterApp.w0 WriterApp.w_text length]; unfold N, WriterValue.wdoc; lia)).
set (l := skipn _ _) in HF |- *.
destruct (Nat.lt_ge_cases i (length l)) as [Hi | Hi].
- exact (proj1 (Forall_forall _ _) HF _ (nth_In l 0 Hi)).
- rewrite nth_overflow by exact Hi. rewrite EM. pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj). lia.
Qed.

Section t5w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).



Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: every journal below at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf, the
   relation of the glue's crt_live_journal and of QF *)
#[local] Notation RZW := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx RZW).
(* the journal at a wild-trace budget WS (YCbqG.v ajournal_xwR at RZW) *)
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARx RZW).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry this row reads (PRH_FnCheck.v, the text's own; Crt102Top
   discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HLED0 : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
(* the text's own request bound (PRH_FnCheck.v tcheck_round_trip_specX): every ledger request is within g_most *)
Hypothesis HRQA : RQA_crt t <= most.
(* the read-only string "modifiedAt" the at-search compares with: the text's own `kept_img B a_mod_at 11` at the
   instance's a_mod_at := CRT_MOD_AT_B (Crt102Img.v:1024) *)
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
(* NAMED HYPOTHESES BOK (asyms_ok B; owner image B's start-up record) and IMGVIS (the image's shadow is
   visible in every ARx state; owner the instance owner, img_shadow_vis_cf), as row T7's Crt102B_T7_tree.v takes them for its
   read-only strcmp operands (cb7t_rom_prem_mod_at) *)
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE CALLEE TEXTS, each at ANY float state.
   NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row): the __wrap_strcmp row in its read-only-premise form WITH the memnorm
   keep (YGcallMxmn.v:898 astrcmp_realizes_xrom). The _xro form (:849) is not enough here: crt_live's last field
   (Crt102Glue.v crt_live_memnorm, `memnorm mem -> memnorm memc`) must hold again after the call, and astrcmp_realizes_xro's post
   (YGcallMxmn.v:866-873) keeps no memnorm.
   *)
Hypothesis ASTRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

#[local] Notation ENT := (ct6_entry B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam
  peak cnt most HPRE HTREE).
#[local] Notation L0B := (crt_at_L0_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).

(* ---- L0's granted arm is the only one: the rewrite's pj_write is not refused and does not reach SIZE_MAXZ (prh_oks
   with g_ran_out 0 -> 0, the count below 2 ^ 62), so saved <> 0; its read-back reads the rewrite back (the count
   condition holds), so rc = 0 and back holds crt_tc. The new:740 abort at +0x47c is not taken. ---- *)
Lemma ct5_granted : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  L0B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  saved <> 0 /\ rcd = 0 /\ crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
    (t := t) Sc (crt_evs_L0 ms) /\
  cntc = cnt + ck_crt_count t cset /\
  exists Dback kw, Dx = Dback ++ (saved, kw) :: Dc /\
    pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK)
      (crt_tc (t := t)) Dback /\
    Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk (crt_tc (t := t))) /\
    (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
       (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
     map (fun b => snd b + cf_head) Fb = PresetReqAt.fo (crt_tc (t := t))) /\
    kw = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd HL0.
pose proof (crt_at_L0_B_obj HL0) as Ht. pose proof (crt_at_L0_B_cset_range HL0) as Hcs1.
pose proof (crt_at_L0_B_cset_mod HL0) as Hcs2. destruct (crt_at_L0_B_outcome HL0) as (ok & HOKS & Harm). clear HL0.
cbv zeta in HOKS, Harm.
set (st' := PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ) (crt_wP (t := t))) in *.
pose proof (cm_in_intro x t HREAD HLENX HWL0 HWL1) as Hin.
pose proof HLED0 as HB0. apply prh_ledger_bounds in HB0. destruct HB0 as (_ & _ & Hc0 & _).
assert (Hcnt0 : 0 <= cnt < 2 ^ 62 - 2 ^ 30) by lia.
destruct (cm_cnt_write x t ms cset cnt Hin Ht Hcs1 Hcnt0) as (Hw0 & Hw1).
assert (Ecw : crt_cw (t := t) (cnt := cnt) cset = ck_cnt2 cnt t + 1 + cset)
  by (unfold crt_cw; rewrite cm_cnt2_eq; lia).
assert (EwP : crt_wP (t := t) = WriterValue.wdpieces (ck_crt_tree t) true) by reflexivity.
pose proof (cm_wcalls_nonneg (ck_crt_tree t) true) as Hwn.
pose proof (cm_tcalls_nonneg (ck_crt_tree t)) as Htn.
pose proof (cm_pjw_k_le ok (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia)) as Hk.
rewrite <- EwP in Hk.
pose proof (cm_in_count x t cset Hin Hcs1) as Hcount.
pose proof (cm_cnt_obj cnt t ms cset Ht) as Ecnt.
(* the writer did not fail *)
assert (Hnf : WriterApp.w_failed st' = 0).
{ destruct (Z.eq_dec (WriterApp.w_failed st') 0) as [E|E]; [exact E|exfalso].
  destruct (cm_pjw_fail ok (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) ltac:(lia) E)
    as (i & Hi & [Hf | Hr]).
  - rewrite <- EwP in Hi. unfold SIZE_MAXZ in Hf. lia.
  - rewrite <- EwP in Hi. destruct HOKS as (_ & _ & H3).
    assert (Hrf : prh_refused ok (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ i = true).
    { unfold prh_refused. rewrite Hr. cbn [negb andb]. apply negb_true_iff, Z.eqb_neq. unfold SIZE_MAXZ. lia. }
    assert (Hrq : nth i (PRH_FnWriter.prhWriter_reqs ok (WriterApp.w0 (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ)
      (crt_wP (t := t))) 0 <= most).
    { rewrite EwP. pose proof (cm_rqa_write t most HRQA).
      pose proof (proj1 (proj2 (cm_in_wlen_crt x t Hin))) as Hwl. unfold PRH_FnWriter.prhWriter_WMAX in Hwl.
      pose proof (ct5_wreq_le ok (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ (ck_crt_tree t) true i ltac:(lia)).
      lia. }
    specialize (H3 i Hi Hrf Hrq). lia. }
destruct Harm as [(_ & Hf & _) | (Hsv & _ & okr & res & tr & Hrun & _ & Hcntc & Hres & Hmatch)]; [contradiction|].
destruct (cm_pjw_succ ok (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ (ck_crt_tree t) true ltac:(lia) ltac:(lia) Hnf)
  as (_ & Hwc). rewrite <- EwP in Hwc. fold st' in Hwc.
pose proof (cm_ncalls_crt x t true Hin) as Hnc. pose proof (cm_read_crt x t true Hin) as Hrd.
assert (Hcond : WriterApp.w_cnt st' + ck_ncalls (crt_tb (t := t)) <= SIZE_MAXZ)
  by (unfold crt_tb, crt_tc; rewrite Hwc, Hnc; unfold SIZE_MAXZ; lia).
destruct (Hres (or_intror Hcond)) as (Er & Ec).
unfold crt_tb, crt_tc in Er, Ec. rewrite Hrd in Er. subst res.
destruct Hmatch as (Hrc & Hpos & Dback & EDx & Hback & HbP & HFo).
split; [exact Hsv|]. split; [exact Hrc|]. split; [exact Hpos|].
split; [rewrite Hcntc, Hwc, Ec, Hnc, Ecw; lia|].
exists Dback, (WriterApp.w_cap st'). split; [exact EDx|]. split; [exact Hback|]. split; [exact HbP|].
split; [exact HFo|].
(* pj_write's buffer: the capacity of the unfailed writer run is the last of its grow calls *)
unfold st'. rewrite (cm_wput_cap (crt_wP (t := t)) ok (WriterApp.w0 (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ) eq_refl Hnf).
change (Z.of_nat (length (WriterApp.w_text (WriterApp.w0 (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ)))) with 0.
change (WriterApp.w_cap (WriterApp.w0 (crt_cw (t := t) (cnt := cnt) cset) SIZE_MAXZ)) with 0.
rewrite <- ct5_last_grow. unfold PresetReqAt.wcaps. rewrite Ht. reflexivity.
Qed.

(* ======================================================================================================== *)
(* THE ROW'S BOUNDARIES (internal to row T5) *)
#[local] Notation spillB := (crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs)).
#[local] Notation dregsB := (crt_dregs_B (regs := regs) (doc := doc)).

(* the facts every cut after L0 carries: L0's granted arm resolved (ct5_granted), saved at 0(s1), doc->n at 8(s1),
   &doc->keys at 0x30(s1); the walk holds Dback ++ (saved, kw) :: Dc beyond the entry's blocks *)
Definition crt5_core (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved kw : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (saved, kw) :: Dc) Lamc peakc cntc 0 0 /\
  dregsB rg (frame_addr lyc CRT_CID pos) /\
  spillB Wc memc CRT_SP_SAVED_B saved /\
  spillB Wc memc 8 (Z.of_nat (length ms)) /\
  spillB Wc memc CRT_SP_KEYS_B (doc + PJ_OFF_KEYS) /\
  spillB Wc memc CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) /\
  spillB Wc memc CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) /\
  spillB Wc memc CRT_SP_PN_B (doc + PJ_OFF_N) /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  cntc = cnt + ck_crt_count t cset /\
  saved <> 0 /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) (crt_tc (t := t))
    Dc /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) (crt_tc (t := t))
    Dback /\
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) Sc (crt_evs_L0 ms) /\
  kw = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0 /\
  Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk (crt_tc (t := t))) /\
  (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo (crt_tc (t := t))) /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (* copy's free order (crt_at_L0_B_copy_fo .. crt_at_C_B_copy_fo): the loops write none of copy's blocks *)
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat.

(* L1 (+0x4f8), the at-search head at index i (s5 = i + 1, s8 = s10 = keys + 8 i): the keys pointer kd, the loop's
   slots 0x10 (MOD_AT), 0x18 (keys aligned and non-null), 0x20 (kd), 0x28 (kd non-null) and U's copy of doc->n at
   0x48, no key before i is "modifiedAt" *)
Definition crt5_L1 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved kw kd : Z) (i : nat) : Prop :=
  crt5_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw /\
  getr rg 21 = w64 (Z.of_nat i + 1) /\ getr rg 24 = w64 (kd + 8 * Z.of_nat i) /\ getr rg 26 = w64 (kd + 8 * Z.of_nat i) /\
  spillB Wc memc 16 (@CRT_MOD_AT_B _ PA) /\ spillB Wc memc 24 1 /\ spillB Wc memc 32 kd /\ spillB Wc memc 40 1 /\
  spillB Wc memc CRT_SP_N_B (Z.of_nat (length ms)) /\
  rd_u64 SEGS (mrestrict (w_H Wc) memc) (doc + PJ_OFF_KEYS) kd /\
  (i < length ms)%nat /\
  (forall j nm u, (j < i)%nat -> nth_error ms j = Some (nm, u) -> nm <> ck_MOD_AT).

(* L2 (+0x56c), at found: a1 = at = cm_at ms, a2 = (at == doc->n) *)
Definition crt5_L2 (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (rg : bvmap 5 word) (ms : list (list Z * PjTree.jv)) (cset saved kw : Z) (atn : nat) : Prop :=
  crt5_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw /\
  getr rg 11 = w64 (Z.of_nat atn) /\ getr rg 12 = w64 (if Nat.eqb atn (length ms) then 1 else 0) /\
  atn = cm_at ms.

(* the facts of crt5_core that are not registers or the three spills L0 writes (0, 8, 0x30): what L0 already has *)
Definition crt5_pre (fxk : YK11.FPState) (lyc : alayout) (Sc : astate) (Hpc : list Z) (Wc : world SEGS)
  (memc : word -> option byte) (mdc : Model) (kj pos : Z) (Dc Dback Lamc : list (Z * Z)) (peakc cntc : Z)
  (ms : list (list Z * PjTree.jv)) (cset saved kw : Z) : Prop :=
  t = PjTree.JObj ms /\
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  liveB lyc Sc Hpc Wc memc mdc kj pos (Dback ++ (saved, kw) :: Dc) Lamc peakc cntc 0 0 /\
  doc mod 8 = 0 /\ range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF doc 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) 56 /\
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (frame_addr lyc CRT_CID pos + CRT_OFF_V) 56 /\
  0 <= cset <= 3 /\ (In ck_MOD_AT (map fst ms) -> cset = 0) /\
  cntc = cnt + ck_crt_count t cset /\
  saved <> 0 /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) (crt_tc (t := t))
    Dc /\
  pj_fdR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc /\
  pj_nodeR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) (crt_tc (t := t))
    Dback /\
  crt_pos (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0) (t := t) Sc (crt_evs_L0 ms) /\
  kw = last (PresetReqAt.wcaps (PresetReqAt.copy_set ms) true) 0 /\
  Permutation (map (fun b => snd b + cf_head) Dback) (PresetReqAtNoMiss.tblk (crt_tc (t := t))) /\
  (exists Fb, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) Dback Fb /\
   map (fun b => snd b + cf_head) Fb = PresetReqAt.fo (crt_tc (t := t))) /\
  Permutation (map (fun b => snd b + cf_head) Dc) (PresetReqAtNoMiss.tblk (crt_tree_J (t := t))) /\
  (exists Fc, PRH_PjOrder.pj_foR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) DOC_D
     (frame_addr lyc CRT_CID pos + CRT_OFF_COPY) Dc Fc /\
   map (fun b => snd b + cf_head) Fc = PresetReqAt.fo (crt_tree_J (t := t))) /\
  (PjTree.depth (crt_tree_J (t := t)) <= DOC_D)%nat.

(* ---- THE LIVE STATE ACROSS ONE OF THE ROW'S OWN RUNS OR CALLS: they write only below sp1 + 80 and above
   alloc_ceiling (the loop's and L2's spills, strcmp's window), so everything the live state reads (the saved words at sp0 - 8 .. sp0 - 104, F's spill at sp1 + 0x70,
   the ledger, statics, frames and blocks below alloc_ceiling) is kept ---- *)
Lemma ct5_live_run : forall lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dx Lamc peakc cntc mem2 md2 (X : Z -> Prop)
    {WS : list (list Z)},
  liveB lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc 0 0 ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  (forall a, X a -> YM05.alloc_ceiling <= a < sp1 + 80) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  liveB lyc Sc Hpc Wc mem2 md2 kj pos Dx Lamc peakc cntc 0 0 /\
  (forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
Proof.
intros lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc mem2 md2 X WS HL HJ2 HB_HJ2 HX Hag HMN2.
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL. pose proof (crt_live_blocks_perm HL) as HPB.
pose proof (crt_live_dx_apart HL) as HAP. pose proof (crt_live_saved HL) as HSV.
pose proof (crt_live_frame HL) as HFRM. pose proof (crt_live_fspill HL) as HSPF.
pose proof (crt_live_copy_open HL) as HCR. pose proof (crt_live_copy_hull HL) as HCH.
pose proof (crt_live_memnorm HL) as HMNc.
pose proof (proj1 HJ) as HAR.
pose proof (crt_side_ledger HSD) as HLED.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc mem2 md2 kj pos HJ2) as (_ & _ & _ & _ & _ & Ffr2 & _).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia|]. intros Hx. pose proof (HX a Hx). lia. }
assert (KST : forall a, sp1 + 80 <= a < 2 ^ 64 -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. apply Hag; [lia|]. intros Hx. pose proof (HX a Hx). lia. }
assert (KFR : forall cid pos' a, In (cid, pos') (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros cid pos' a Hin' Ha. destruct (frames_bounds_x _ _ _ LAWS lyc Sc Hpc Wc memc mdc cid pos' HAR Hin') as (G1 & G2 & G3).
  apply KL. unfold in_zr, frame_rng, shadow_addr in Ha. cbn [fst snd] in Ha.
  assert (0 <= fs_frame_bytes cid / 8) by (apply Z.div_pos; lia).
  assert (fs_frame_bytes cid / 8 <= fs_frame_bytes cid) by (apply Z.div_le_upper_bound; lia).
  assert (0 <= frame_addr lyc cid pos' / 8 <= frame_addr lyc cid pos') by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold SHADOW_OFF in *. lia. }
assert (KBL : forall p n j, In (p, n) (ablocks B lyc Sc) -> 0 <= j < req_size n ->
  aview SEGS (w_H Wc) mem2 (p + j) = aview SEGS (w_H Wc) memc (p + j)).
{ intros p n j Hab Hj. destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc Wc memc mdc _ _ HAR Hab) as (_ & H4096 & Hce & _).
  apply KL. lia. }
assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
  ~ Exists (in_zr a) PST -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha _ _ _. pose proof (@pa_segs_low _ _ PA a Ha) as Hl. apply KL. unfold kLowMemEnd in Hl. lia. }
assert (KPST : forall a, Exists (in_zr a) PST -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a).
{ intros a Ha. pose proof (@pa_segs_low _ _ PA a (pst_in_img_B a Ha)) as Hl. apply KL. unfold kLowMemEnd in Hl. lia. }
assert (HLED2 : prh_ledger B lyc Sc Hpc Wc mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0).
{ apply (prh_ledger_kept_aview B lyc Sc Hpc Wc memc lyc Sc Hpc Wc mem2 Lamc peakc cntc SIZE_MAXZ 0 most 0 HLED).
  - exact KPST.
  - intros a k j Hk Hj.
    destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 a k HAR HLED Hk) as (Hk0 & _ & H4 & Hc & _).
    apply KL. change (@cf_head CfParams_preset) with 16. lia.
  - intros a k _ Hab. exact Hab.
  - apply Permutation_refl. }
pose proof (ct6_side_after B ARx LAWS ly S Hp W regs mem md ch doc t D Lam peak most
  HPRE HTREE lyc Sc Hpc Wc memc mdc kj pos Dx Lamc peakc cntc lyc Hpc Wc mem2 md2 kj HL HJ2 HLED2
  KFR KBL KIMG) as HSD2.
set (F := frame_addr lyc CRT_CID pos) in *.
split; [|exact KL].
refine {| crt_live_journal := ex_intro _ WS (conj HJ2 HB_HJ2); crt_live_side := HSD2; crt_live_lam_perm := HPL;
          crt_live_blocks_perm := HPB;
          crt_live_dx_apart := HAP; crt_live_saved := _; crt_live_frame := _; crt_live_fspill := _;
          crt_live_copy_open := _; crt_live_copy_hull := _; crt_live_memnorm := _ |}.
{ intros j Hj. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact (HSV j Hj)]. intros k Hk. apply KST. lia. }
{ pose proof (crt_frame_listed HFRM) as Hinf. pose proof (crt_frame_flag_word HFRM) as Hfl.
  pose proof (crt_frame_present HFRM) as Hpr.
  refine {| crt_frame_listed := Hinf; crt_frame_flag_word := _; crt_frame_present := _ |}.
  - rewrite <- Hfl. apply ts_rdword_keep. intros j Hj. rewrite cb4_fb. apply KL. lia.
  - intros a Ha. rewrite cb4_fb in Ha. exact (proj1 (Ffr2 a Ha)). }
{ unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc mem2 _ 8 _); [|exact HSPF]. intros k Hk. apply KST.
  unfold CRT_SP_F. lia. }
{ apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HCR].
  intros y Hy. unfold CRT_OFF_COPY in Hy. unfold shadow_of_addr. apply KL.
  assert (0 <= y / 8) by (apply Z.div_pos; lia). assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF. lia. }
{ intros s0 Hs0. rewrite KL; [exact (HCH s0 Hs0)|].
  unfold CRT_OFF_COPY, shadow_addr, SHADOW_OFF in *.
  assert (0 <= (F + 224) / 8) by (apply Z.div_pos; lia).
  assert ((F + 224 + 56 - 1) / 8 <= F + 224 + 56 - 1) by (apply Z.div_le_upper_bound; lia). lia. }
exact HMN2.
Qed.

(* ---- the core across one of the row's own runs: the live state by ct5_live_run, the spills and the registers the
   caller reads off the run's final state, the trees and the shadow below alloc_ceiling kept ---- *)
Lemma ct5_pre_run : forall fxk lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dc Dback Lamc peakc cntc ms cset saved kw
    mem2 md2 rg2 (X : Z -> Prop) {WS : list (list Z)},
  crt5_pre fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc ms cset saved kw ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  (forall a, X a -> YM05.alloc_ceiling <= a < sp1 + 80) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  dregsB rg2 (frame_addr lyc CRT_CID pos) ->
  spillB Wc mem2 CRT_SP_SAVED_B saved -> spillB Wc mem2 8 (Z.of_nat (length ms)) ->
  spillB Wc mem2 CRT_SP_KEYS_B (doc + PJ_OFF_KEYS) ->
  spillB Wc mem2 CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) ->
  spillB Wc mem2 CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) -> spillB Wc mem2 CRT_SP_PN_B (doc + PJ_OFF_N) ->
  crt5_core fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc rg2 ms cset saved kw.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc ms cset saved kw mem2 md2 rg2 X WS HC HJ2 HB_HJ2 HX
  Hag HMN2 HDR S0 S8 S48 S56 S80 S88.
destruct HC as (Ht & HFZ & HFK & HL & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 & Hcnt & Hsv & HTC & HFD & HBK & HPOS0 &
  Hkw & HbP & (Fb & HFo & HFm) & HcP & (Fc & HFoc & HFmc) & Hdep).
destruct (ct5_live_run lyc Sc Hpc Wc memc mdc kj pos _ Lamc peakc cntc mem2 md2 X HL HJ2 HB_HJ2 HX Hag HMN2)
  as (HL2 & KL).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_side HL) as HSD.
pose proof (crt_live_lam_perm HL) as HPL.
pose proof (crt_side_ledger HSD) as HLED. pose proof (crt_side_doc HSD) as HDOC.
pose proof (crt_side_doc_blocks HSD) as HDL.
pose proof (proj1 HJ) as HAR.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc mem2 md2 kj pos HJ2) as (_ & _ & _ & _ & _ & Ffr2 & _).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hd1 & Hd2 & Hd3 & Hd4).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr lyc CRT_CID pos) in *.
assert (HDc : forall bk, In bk Dc -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. right.
  right. exact Hbk. }
assert (HDb : forall bk, In bk Dback -> In bk Lamc).
{ intros bk Hbk. apply (Permutation_in _ (Permutation_sym HPL)). apply in_or_app. left. apply in_or_app. left. exact Hbk. }
assert (KLam : forall a k y, In (a, k) Lamc -> a <= y < a + k -> aview SEGS (w_H Wc) mem2 y = aview SEGS (w_H Wc) memc y).
{ intros a k y Hak Hy. destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 a k HAR HLED Hak)
    as (Hk0 & _ & H4 & Hc & _). apply KL. lia. }
assert (AG : forall p Dp, F <= p -> p + 56 <= F + 512 -> (forall bk, In bk Dp -> In bk Lamc) ->
  pj_agreeR SEGS (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) mem2) (pj_footR p Dp)).
{ intros p Dp Hp1 Hp2 HD. destruct (crt_live_journal HL2) as (WS_HJ2' & HJ2' & _).
  pose proof (crt_side_ledger (crt_live_side HL2)) as HLED2.
  apply (ct6_agree B ARx LAWS Wc memc lyc Sc Hpc Wc mem2 md2 Lamc peakc cntc 0 p Dp (proj1 HJ2') HLED2 HD); [|exact KLam].
  intros y Hy. split; [exact (proj1 (Ffr2 y ltac:(lia)))|]. apply KL. lia. }
assert (RA : forall a, 4096 <= a -> a + 56 <= YM05.alloc_ceiling ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF a 56 ->
  range_addressable (aview SEGS (w_H Wc) mem2) SHADOW_OFF a 56).
{ intros a Ha1 Ha2 HR. apply (range_addressable_agree (aview SEGS (w_H Wc) memc)); [|exact HR].
  intros y Hy. unfold shadow_of_addr. apply KL.
  assert (0 <= y / 8) by (apply Z.div_pos; lia). assert (y / 8 <= y) by (apply Z.div_le_upper_bound; lia).
  unfold SHADOW_OFF. lia. }
refine (conj Ht (conj HFZ (conj HFK (conj HL2 (conj HDR (conj S0 (conj S8 (conj S48 (conj S56 (conj S80 (conj S88
  (conj Hd8 (conj _ (conj _ (conj _ (conj Hcs1 (conj Hcs2 (conj Hcnt (conj Hsv
  (conj _ (conj _ (conj _ (conj HPOS0 (conj Hkw (conj HbP (conj _ (conj HcP (conj _ Hdep)))))))))))))))))))))))))))).
- apply (RA doc); [lia | lia | exact RAd].
- apply (RA (F + CRT_OFF_BACK)); [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact RAb].
- apply (RA (F + CRT_OFF_V)); [unfold CRT_OFF_V; lia | unfold CRT_OFF_V; lia | exact RAv].
- apply (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Dc HTC). apply (AG (F + CRT_OFF_COPY) Dc); [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HDc].
- apply (crt102rw_fdR_frame SEGS DOC_D _ _ (prh_lin Lamc) _ Dc HFD). apply (AG (F + CRT_OFF_COPY) Dc); [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HDc].
- apply (pj_nodeR_frame SEGS _ _ _ (prh_lin Lamc) _ Dback HBK). apply (AG (F + CRT_OFF_BACK) Dback); [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact HDb].
- exists Fb. split; [|exact HFm].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dback Fb HFo).
  + exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFo).
  + apply (AG (F + CRT_OFF_BACK) Dback); [unfold CRT_OFF_BACK; lia | unfold CRT_OFF_BACK; lia | exact HDb].
- (* copy's free order: copy's blocks are not written *)
  exists Fc. split; [|exact HFmc].
  apply (PRH_PjOrder.pj_foR_frame SEGS DOC_D _ _ (prh_lin Lamc) (prh_lin Lamc) _ Dc Fc HFoc).
  + exact (PRH_PjOrder.pj_foR_lblk SEGS _ _ _ _ _ _ HFoc).
  + apply (AG (F + CRT_OFF_COPY) Dc); [unfold CRT_OFF_COPY; lia | unfold CRT_OFF_COPY; lia | exact HDc].
Qed.

Lemma ct5_pre_of_core : forall fxk lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved
    kw,
  crt5_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw ->
  crt5_pre fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc ms cset saved kw.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw
  (Ht & HFZ & HFK & HL & _ & _ & _ & _ & _ & _ & _ & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 & Hcnt & Hsv & HTC & HFD & HBK &
   HPOS).
exact (conj Ht (conj HFZ (conj HFK (conj HL (conj Hd8 (conj RAd (conj RAb (conj RAv (conj Hcs1 (conj Hcs2 (conj Hcnt
  (conj Hsv (conj HTC (conj HFD (conj HBK HPOS))))))))))))))).
Qed.

Lemma ct5_core_run : forall fxk lyc Sc Hpc (Wc : world SEGS) memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw
    mem2 md2 rg2 (X : Z -> Prop) {WS : list (list Z)},
  crt5_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw ->
  AJW STKC sp0 [] ly S Hp W mem md [(CRT_CID, pos)] lyc Sc Hpc Wc mem2 md2 kj WS ->
  YCbqGwild.wbudget [] (prh_wk F_check_round_trip) WS ->
  (forall a, X a -> YM05.alloc_ceiling <= a < sp1 + 80) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) memc a) ->
  (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  dregsB rg2 (frame_addr lyc CRT_CID pos) ->
  spillB Wc mem2 CRT_SP_SAVED_B saved -> spillB Wc mem2 8 (Z.of_nat (length ms)) ->
  spillB Wc mem2 CRT_SP_KEYS_B (doc + PJ_OFF_KEYS) ->
  spillB Wc mem2 CRT_SP_BACK (frame_addr lyc CRT_CID pos + CRT_OFF_BACK) ->
  spillB Wc mem2 CRT_SP_SHN_B (shadow_addr (doc + PJ_OFF_N)) -> spillB Wc mem2 CRT_SP_PN_B (doc + PJ_OFF_N) ->
  crt5_core fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc rg2 ms cset saved kw.
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw mem2 md2 rg2 X WS HC.
exact (ct5_pre_run fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc ms cset saved kw mem2 md2 rg2 X
  (ct5_pre_of_core fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw HC)).
Qed.

(* ---- the stretch statements, over any fact Pd of the pass's fixed data (Dc, Dback, kw, ms) the boundaries carry
   (True for the frozen text) ---- *)
Section p.
Variable Pd : list (Z * Z) -> list (Z * Z) -> Z -> list (list Z * PjTree.jv) -> Prop.
Definition CT5_ATL3 : Prop := forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i,
  L3B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw i -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L3_OFF_B rg memc mdc) QFb.
Definition CT5_ATC : Prop := forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw,
  CB fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_C_OFF_B rg memc mdc) QFb.
Definition CT5_AT_L1 (i : nat) (ms : list (list Z * PjTree.jv)) : Prop :=
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw kd,
  crt5_L1 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw kd i -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L1_OFF_B rg memc mdc) QFb.
Definition CT5_AT_L2 : Prop := forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw atn,
  crt5_L2 fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg ms cset saved kw atn -> Pd Dc Dback kw ms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L2_OFF_B rg memc mdc) QFb.
(* the three stretch lemmas the row's files prove *)
Definition CT5_L2_STMT : Prop := CT5_ATL3 -> CT5_ATC -> CT5_AT_L2.
Definition CT5_L1_STMT : Prop :=
  CT5_AT_L2 -> forall i ms, (forall j, (i < j)%nat -> CT5_AT_L1 j ms) -> CT5_AT_L1 i ms.
Definition CT5_L0_STMT : Prop :=
  (forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd Dback kw,
     L0B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
     Dx = Dback ++ (saved, kw) :: Dc -> Pd Dc Dback kw ms) ->
  (forall ms, CT5_AT_L1 0 ms) -> CT5_AT_L2 ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd,
  L0B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dx Lamc peakc cntc rg ms cset saved rcd ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_L0_OFF_B rg memc mdc) QFb.
End p.

End g.
End f.
End t5w.
