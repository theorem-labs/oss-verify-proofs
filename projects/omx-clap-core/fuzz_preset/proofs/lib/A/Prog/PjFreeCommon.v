(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the IMAGE-FREE pieces of pj_free's walks (fuzz_preset), ONE copy for image A (lib/A/Prog,
   slice S6) and image B (lib/B/Prog/pj_free_*.v): what a call keeps of the harness blocks. Generic over the program
   listing {L} and its image facts {PA : PAImg L}, the image's ledger parameters {PI : PrhImg} and the allocator
   parameters {cp : CfParams}; no lib/B import. proves no function (kind: walk glue).
   MOVED, statements and proofs unchanged, from h-rw-man-5's image-B lane, lib/B/Prog/pj_free_keep.v (blob
   02337852b3d6 at origin/cold/h-rw-man-5-b-pjfree-rb 85f034f446fd; byte-identical, for these two lemmas, to blob
   7011cf3f2c68 at b8478281ae9):
     pfk_hblk     pj_free_keep.v:81-103 (with its comment line)
     pfk_nohead   pj_free_keep.v:105-138 (with its comment lines)
   The only change for the generic form: image B's `PA := PI_prog_B`, `SEGS := @pa_segs _ B_prog_listing PA` and
   `PST := prh_pst (PI := prh_img_B)` become the Section's {L} {PA} / pa_segs and {PI}'s prh_pst. THE RE-HIDING MOVE:
   pfk_hblk's body is now pfk_hblkR, over any world relation R (a callee journal after a free is at wle'), and
   pfk_hblk is its instance at wle.
   Section hypothesis: AR_laws_x pa_segs B ARx cf_head (the kit's laws). No ADDRESS.
   ALSO MOVED, statements and proofs unchanged, from h-rw-man-5's image-B lane (h-rw-man-5's YES 2026-10-29, relayed by
   h-rw-pre-5): lib/B/Prog/pj_free_defs.v blob bd4c58302fde at origin/cold/h-rw-man-5-b-pjfree-rb ab365ca51d3, lines
   76-190, byte-identical: the observer (pf_obs, pf_reach, pf_safe), Section t (tfuzz_free_specO, pf_K0post,
   tpj_free_specO: the instrumented texts, generic over {L} {PA} {PI} {cp}). The image-B cuts of pj_free_defs.v (its
   Section d) stay in lib/B. Its Section ord (pf_oitemsR, pj_oshapeR, pj_foR) was here too until the kit took it
   (lib/A/PRH_PjOrder.v e5917626b82b, kit-oldpin bd0d3c3a486b, announced 17:42Z); it is cited from there. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep YG0dcf YGcfRoomPre.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_PjOrder.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetRoomPosKeep PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PA).
#[local] Notation PST := (@prh_pst PI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).

(* ---- a harness-block byte, live before and after, outside the callee's footprint ---- *)
(* over any world relation R (the callee journal's conjunct 4 is not read): after a free the callee journal is at
   wle' (YA0nH); pfk_hblk is its instance at wle *)
Lemma pfk_hblkR : forall (R : world SEGS -> world SEGS -> Prop)
    ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran most own
    peak2 cnt2 fail2 ran2 most2 own2 a k x,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  ajournal_xR (SK := SK) SEGS B PST ARx R STK1 sp1 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  In (a, k) Lam -> In (a, k) Lam2 -> a <= x < a + k -> ~ inFP FP1 x ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x /\ apresent (w_H W2) mem2 x.
Proof.
intros R ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran most own
  peak2 cnt2 fail2 ran2 most2 own2 a k x HAR HL HJ HL2 Hin Hin2 Hx Hfp.
destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HL Hin) as (Hk & Hab & _).
destruct (prh_ledger_hblock B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 a k most2 own2 HL2 Hin2)
  as (_ & Hab2 & _).
pose proof (ajxR_ar HJ) as HAR2. pose proof (ajxR_blk HJ) as J2.
pose proof (@cf_head_nonneg cp) as Hc0.
pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [_ Rk].
destruct (alx_blocks SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab2) as (_ & _ & _ & _ & Hby & _).
split.
- pose proof (J2 (a - @cf_head cp) (k + @cf_head cp) (x - (a - @cf_head cp)) Hab Hab2 ltac:(lia)) as E.
  replace (a - cf_head + (x - (a - cf_head))) with x in E by lia. exact (E Hfp).
- exact (proj1 (Hby x ltac:(lia))).
Qed.
Lemma pfk_hblk : forall ly S Hp W mem md Lam ly2 S2 Hp2 W2 mem2 md2 Lam2 STK1 sp1 FP1 k1 peak cnt fail ran most own
    peak2 cnt2 fail2 ran2 most2 own2 a k x,
  ARx ly S Hp W mem md ->
  prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  AJ STK1 sp1 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  prh_ledger (PA := PA) B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most2 own2 ->
  In (a, k) Lam -> In (a, k) Lam2 -> a <= x < a + k -> ~ inFP FP1 x ->
  aview SEGS (w_H W2) mem2 x = aview SEGS (w_H W) mem x /\ apresent (w_H W2) mem2 x.
Proof. exact (pfk_hblkR (@wle SEGS)). Qed.

(* a block that is not a harness block holds no hidden head (pj_parse_seg_c2ok.v pjp2_nohead's proof): every head of
   Hp is the base of a harness block, and blocks are pairwise apart (alx_blocks) *)
Lemma pfk_nohead : forall ly S Hp W mem md Lam peak cnt fail ran most own b m,
  ARx ly S Hp W mem md -> prh_ledger (PA := PA) B ly S Hp W mem Lam peak cnt fail ran most own ->
  In (b, m) (ablocks B ly S) -> ~ In (b + cf_head, m - cf_head) Lam ->
  forall h, In h Hp -> ~ (b <= h < b + req_size m).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hb Hn h Hh Hr.
destruct HLED as (_ & _ & HF & HP).
apply (Permutation_in _ HP) in Hh. apply in_map_iff in Hh as ([a k] & Eh & Hin). cbn [fst] in Eh. subst h.
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk0 & Hab & _). cbn [fst snd] in Hk0, Hab.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hb) as (_ & _ & _ & _ & _ & Hpw).
pose proof cf_head_nonneg as Hc0.
destruct (Z.eq_dec b (a - cf_head)) as [E1|N1]; [destruct (Z.eq_dec m (k + cf_head)) as [E2|N2]|].
- apply Hn. replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact Hin.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as _ E; exact (N2 E)).
  destruct (in_split_2 (b, m) (a - cf_head, k + cf_head) (ablocks B ly S) Hb Hab Hne) as (l1 & l2 & l3 & El).
  assert (HZ : zdisjoint (b, req_size m) (a - cf_head, req_size (k + cf_head))).
  { apply (pairwise_zdisjoint_split _ _ _ Hpw).
    exists (map (fun b0 => (fst b0, req_size (snd b0))) l1), (map (fun b0 => (fst b0, req_size (snd b0))) l2),
      (map (fun b0 => (fst b0, req_size (snd b0))) l3).
    destruct El as [El | El]; rewrite El; rewrite map_app; cbn [map fst snd]; rewrite map_app; cbn [map fst snd];
      [left | right]; reflexivity. }
  pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [R1 _]. unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
- assert (Hne : (b, m) <> (a - cf_head, k + cf_head)) by (intros E; injection E as E _; exact (N1 E)).
  destruct (in_split_2 (b, m) (a - cf_head, k + cf_head) (ablocks B ly S) Hb Hab Hne) as (l1 & l2 & l3 & El).
  assert (HZ : zdisjoint (b, req_size m) (a - cf_head, req_size (k + cf_head))).
  { apply (pairwise_zdisjoint_split _ _ _ Hpw).
    exists (map (fun b0 => (fst b0, req_size (snd b0))) l1), (map (fun b0 => (fst b0, req_size (snd b0))) l2),
      (map (fun b0 => (fst b0, req_size (snd b0))) l3).
    destruct El as [El | El]; rewrite El; rewrite map_app; cbn [map fst snd]; rewrite map_app; cbn [map fst snd];
      [left | right]; reflexivity. }
  pose proof (req_size_pos (k + @cf_head cp) ltac:(lia)) as [R1 _]. unfold zdisjoint in HZ. cbn [fst snd] in HZ. lia.
Qed.

End k.

(* ================================================================ moved from lib/B/Prog/pj_free_defs.v :76-190 *)
(* Section ord (pf_oitemsR, pj_oshapeR, pj_foR) is the KIT's now: lib/A/PRH_PjOrder.v e5917626b82b (kit-oldpin
   bd0d3c3a486b, h-hpreset-7 took it from h-rw-man-5's ab365ca51d33 unchanged); it is cited, not copied. *)

(* ================================================================ the observer *)
(* one fuzz_free call's allocator step: from (ly, S) to (ly', S'), freeing Some (p, n) (user address, user size) or
   nothing (None: fuzz_free (NULL)) *)
Definition pf_obs : Type := alayout -> astate -> alayout -> astate -> option (Z * Z) -> Prop.

(* from (ly, S), FX steps took the blocks of L off its front in order and left L' at (ly', S') *)
Inductive pf_reach (FX : pf_obs) : list (Z * Z) -> alayout -> astate -> list (Z * Z) -> alayout -> astate -> Prop :=
| pfr_refl : forall L ly S, pf_reach FX L ly S L ly S
| pfr_null : forall L ly S ly1 S1 L' ly' S',
    FX ly S ly1 S1 None -> pf_reach FX L ly1 S1 L' ly' S' -> pf_reach FX L ly S L' ly' S'
| pfr_free : forall b L ly S ly1 S1 L' ly' S',
    FX ly S ly1 S1 (Some b) -> pf_reach FX L ly1 S1 L' ly' S' -> pf_reach FX (b :: L) ly S L' ly' S'.

(* PB holds at every state the run can reach along F (fuzz_free's premise at each of its calls) *)
Definition pf_safe (FX : pf_obs) (PB : astate -> Prop) (F : list (Z * Z)) (ly : alayout) (S : astate) : Prop :=
  forall F' ly' S', pf_reach FX F ly S F' ly' S' -> PB S'.

(* ================================================================ the instrumented texts *)
Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* the fixed re-hideable zone of the cf layer (YGcfRehidePost.v) at this section's run ceiling *)
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* The kit's tfuzz_free_specX (PRH_FnAlloc.v, the kit's tip d607d12e4b0f) with its live-set premise abstracted to PB S and the
   call's FX added to the post. Its trace premise is the FIXED form `In (call_trace ..) (u_fix (as_universe B))`, the
   fact pj_free's four fuzz_free calls have (prh_univ_closure's clauses 1-2, PRH_Base.prh_univ_closure_lit); the kit's
   `admits (as_universe B) (call_trace ..) S` follows from it (YCbqG.admits_ct_fix), and with it the kit's BUDGETED post
   (fpostbm .. (YCbqGwild.wbudget [call_trace ..] 0) ..) reads back as the plain fpostm stated here
   (PRH_Base.fpost_of_fpostb_fix): pf_ff_of_kit. Every other premise and both post arms verbatim. THE HULL: the kit's
   premise `p <> 0 -> PresetHullBudget.hull_budget S []` and post conjunct `PresetHullBudget.hull_used S S' []` are
   carried by PB and FX, so this text keeps its shape: pf_ff_of_kit's PB is pf_PBk (it holds hull_budget S []) and
   its FX is pf_FXk (it holds hull_used S S' []). THE RE-HIDING MOVE: a free can hide shadow again, so the text
   concludes SRr' segs RZ_cf (YA0nH) and its post is fpostm's R form at wle' segs RZ_cf (PRH_Base fpostmR), the
   journal's world conjunct at wle' *)
Definition tfuzz_free_specO (PB : astate -> Prop) (FX : pf_obs) : Prop :=
  forall most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran,
  fpre B ARx STK_fuzz_free ly S Hp W regs mem md ch -> room_live_cf S ->
  PB S ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs ch) (u_fix (as_universe B)) ->
  getr regs 10 = w64 p -> (p = 0 \/ In (p, n) Lam) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' segs RZ_cf W (cfg_at segs (pa_sigma AS_fuzz_free) regs mem md)
    (fpostmR B ARx SK (wle' segs RZ_cf) STK_fuzz_free
       (if p =? 0 then [] else ablocks_fp [(p - cf_head, n + cf_head)])
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       FX ly S ly' S' (if p =? 0 then None else Some (p, n)) /\
       room_live_cf S' /\
       ((p = 0 /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S /\
        prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own)
       \/
       (p <> 0 /\ Hp' = remove Z.eq_dec (p - cf_head) Hp /\
        (exists b1 b2, ablocks B ly S = b1 ++ (p - cf_head, n + cf_head) :: b2 /\ ablocks B ly' S' = b1 ++ b2) /\
        exists l1 l2, Lam = l1 ++ (p, n) :: l2 /\
        prh_ledger B ly' S' Hp' W' mem' (l1 ++ l2) peak cnt fail ran most own)))).

(* The post body of tpj_free_specX (PRH_FnPj.v:1142, 1163-1167) verbatim, without its hull_used, position-transfer and ccnt24 conjuncts *)
Definition pf_K0post (D : list (Z * Z)) (v : Z) (ly : alayout) (S : astate) (Hp : list Z) (Lam : list (Z * Z))
  (peak cnt fail ran most own : Z) : alayout -> astate -> list Z -> world segs -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
       room_live_cf S' /\
       exists Lam', Permutation Lam (D ++ Lam') /\
       Permutation (ablocks B ly S) (prhPj_hbl D ++ ablocks B ly' S') /\
       prh_ledger B ly' S' Hp' W' mem' Lam' peak cnt fail ran most own /\
       (v = 0 -> Lam' = Lam /\ Hp' = Hp /\ ablocks B ly' S' = ablocks B ly S) /\
       (v <> 0 -> pj_zeroR segs (rdW W' mem') v).

(* The kit's tpj_free_specX (PRH_FnPj.v in the batch tree recorded as preset-tree-at-2026-10-29T23-27-23Z.tsv (sha256 1f0ae5f9ecde; internal record): no run words) with the ordered shape pj_foR
   (F), the live-set premise carried along F, and the order in the post. The live-set premise is asked only when
   v <> 0, as the kit's own class-24 premise (pj_free (NULL) returns before any call). The kit's head-width premise
   prh_head_wide is not here: the image walk takes it as a Section hypothesis, and pf_specX_of_walk passes the kit's
   premise to it. THE HULL: the kit's premise `v <> 0 -> PresetHullBudget.hull_budget S []` is carried by
   `v <> 0 -> pf_safe FX PB F ly S` (at pf_PBk / pf_FXk, pfk_safe), and the kit's post conjunct
   `PresetHullBudget.hull_used S S' []` follows from `pf_reach FX F ly S [] ly' S'` (at pf_FXk, pfk_reach_hull).
   THE RE-HIDING MOVE: the run crosses fuzz_free, so the text concludes SRr' segs RZ_cf and its post is fpostWm's R
   form at wle' segs RZ_cf (PRH_Base fpostWmR) *)
Definition tpj_free_specO (PB : astate -> Prop) (FX : pf_obs) (CTX0 : list (list Z)) (n : nat) : Prop :=
  forall most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran,
  fpre B ARx (STK_pj_free n) ly S Hp W regs mem md ch ->
  prh_univ_closure B CTX0 -> room_live_cf S ->
  getr regs 10 = w64 v ->
  fwin ly W regs mem d ->
  (v = 0 /\ D = [] /\ F = [] \/
   v <> 0 /\ v < YM05.alloc_ceiling /\ pj_foR segs (rdW W mem) (prh_lin Lam) n v D F /\
   prhPj_slot B (STK_pj_free n) d ly S Lam W regs mem v) ->
  (v <> 0 -> pf_safe FX PB F ly S) ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr' segs RZ_cf W (cfg_at segs (pa_sigma AS_pj_free) regs mem md)
    (fpostWmR B ARx SK (wle' segs RZ_cf) (STK_pj_free n) d
       (if v =? 0 then [] else (v, v + 56) :: ablocks_fp (prhPj_hbl D))
       regs ly S Hp W mem md (fun ly' S' Hp' W' regs' mem' md' =>
       pf_K0post D v ly S Hp Lam peak cnt fail ran most own ly' S' Hp' W' regs' mem' md' /\
       pf_reach FX F ly S [] ly' S')).
End t.


(* ================================================================ THE BULK FORM OF THE FUZZ_FREE CALLS (shared) *)
(* One copy for images A and B. The list facts and the observer glue were moved from a Theorem Labs image-B lane
   (lib/B/Prog/pj_free_top.v blob 9ff6ee23b621 at commit ec90d1af41fe) and stated generic
   over {L} {PA}. REBOUND to the #102 kit (owner 18:5xZ): the kit's tfuzz_free_specX
   (PRH_FnAlloc.v 740f4d11d144) is in the POST-IMPLICATION form - no position at entry, and its post moves a bulk
   sub-position for every model run - so the old FIX text (an entry widened to a bulk sub-position, the open text
   tfuzz_free_specX_FIX) and its derived forms (tfuzz_free_FIX_kit, tpj_free_specX_bulkF, pf_bulkF_of_walk,
   pf_FXe / pf_PBe / pf_ff_of_fix) are GONE: pf_ff_of_kit derives the walk's fuzz_free text from the kit's text itself, and
   pf_specX_of_walk derives the post-implication tpj_free_specX from any image's walk.
   RESTATED to the batch tree recorded as preset-tree-at-2026-10-29T23-27-23Z.tsv (sha256 1f0ae5f9ecde; internal record): tpj_free_specX CTX0 n (no run words DW) with the premise
   prh_head_wide, which pf_specX_of_walk passes to the walk. FITTED to the kit's tip d607d12e4b0f: tfuzz_free_specX's post
   is BUDGETED at its own trace (fpostbm .. (YCbqGwild.wbudget [call_trace ..] 0) ..); pj_free's fuzz_free traces are
   FIXED, so tfuzz_free_specO takes the trace in u_fix (the walk's prh_univ_closure_lit fact), and pf_ff_of_kit gives
   the kit's `admits` premise by YCbqG.admits_ct_fix and reads the post back by PRH_Base.fpost_of_fpostb_fix.
   pf_ff_of_kit reads the kit's fuzz_free post BY NAME through the kit's projection layer (PRH_FnAlloc.v tffP_R_of, the record
   tffP_R and the arm records tffP_R1 / tffP_R2), never by position; pf_specX_of_walk builds the kit's pj_free post BY NAME
   (PRH_FnPj.v tpfP_Q_of_R from the record tpfP_R).
   ONE COPY for images A' and B' on the kit's cut 7cdbb61b5fa0 (owner 06:38Z; writer a Theorem Labs lane): this file is a Theorem Labs lane's
   df66e85d3123 (the form above, which its B' pj_free walk needs: the walk exists only under the kit's prh_head_wide, so
   pf_specX_of_walk hands the kit's premise to it) plus pf_admits_fix from a Theorem Labs lane's b81eeb4e6e61 (the S6 A' walk's
   measurement: admission at EVERY fuzz_free call of pj_free holds whatever the earlier frees stored, because each
   call is made with an EMPTY chain - pj_free is no frame-pointer function - so its trace is [pc0; its return site] or
   [pc0], in u_fix by prh_univ_closure's clauses 1-2, and admits' u_fix disjunct never reads the depot). The S6 A' walk,
   which does not need prh_head_wide, gives pf_specX_of_walk its walk as `fun _ => ..`. The texts on the cut:
   PRH_FnAlloc.v 4d8aeba047e5 (tfuzz_free_specX), PRH_FnPj.v 5aca5cbe2cfb (tpj_free_specX). *)
(* ---- list facts for the bulk order ---- *)
Lemma pf_firstn_skipn_cons : forall (l : list Z) k m x r,
  firstn (Datatypes.S m) (skipn k l) = x :: r -> nth_error l k = Some x /\ firstn m (skipn (Datatypes.S k) l) = r.
Proof.
induction l as [|a l IH]; intros k m x r E.
- destruct k; cbn in E; discriminate E.
- destruct k as [|k].
  + cbn in E. injection E as E1 E2. subst. split; reflexivity.
  + cbn [skipn nth_error] in E |- *. exact (IH k m x r E).
Qed.

Lemma pf_firstn_length_map : forall (f : Z * Z -> Z) (l : list (Z * Z)), firstn (length l) (map f l) = map f l.
Proof. intros f l. induction l as [|a l IH]; [reflexivity|]. cbn [length map firstn]. rewrite IH. reflexivity. Qed.

Section obs. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation RZ_cf := (@YGcfRehidePost.RZ_cf rc).

(* the observer the fuzz_free text gives (PRH_FnAlloc.tfuzz_free_specX, post-implication form): a call never raises ccnt24;
   a call keeps both hull meters (its post's hull_used S S' []); a NULL free keeps the state; a non-NULL free of
   (p, n), for EVERY model run whose event at i is a bulk HBulk L with entry k = n + cf_head, moves the bulk
   sub-position k at S to k + 1 at S' *)
Definition pf_FXk : pf_obs :=
  fun _ S _ S' b => YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S /\
    PresetHullBudget.hull_used S S' [] /\
    match b with
    | None => S' = S
    | Some b => forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (Lb : list Z) (k : nat) (hb : list YG00.chunk),
        nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HBulk Lb) ->
        nth_error Lb k = Some (snd b + cf_head) ->
        PresetRoomPosKeep.iface_room_pos_bulk sm x os i Lb k H0 hb S ->
        exists hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i Lb (Datatypes.S k) H0 hb' S'
    end.

(* what the fuzz_free text asks at a non-NULL call: the class-24 bound, carried as the entry count c0 within the bound,
   and the hull budget for no event (a free makes no secondary entry) *)
Definition pf_PBk (c0 : Z) (S : astate) : Prop :=
  YGcfRoomLive.ccnt24 S <= c0 /\ c0 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  PresetHullBudget.hull_budget S [].

(* a FIXED trace is admitted at EVERY state (no room spent): admits' second disjunct is membership in u_fix, and inU's
   length bound is call_trace_len. YG01.admits_fix without its universe_ok premise, which it uses only for the length,
   and call_trace's own bound gives that. (The same fact as YCbqG.admits_ct_fix, which pf_ff_of_kit cites; kept under
   its own name because the S6 walk's measurement of admission at every free cites it.) *)
Lemma pf_admits_fix : forall ly pc0 regs ch S,
  In (call_trace ly pc0 regs ch) (u_fix (as_universe B)) -> admits (as_universe B) (call_trace ly pc0 regs ch) S.
Proof.
intros ly pc0 regs ch S H. split; [split; [apply call_trace_len | left; exact H]|].
right. left. apply mem_trace_In. exact H.
Qed.

(* The kit's fuzz_free text gives the walk's tfuzz_free_specO at pf_PBk / pf_FXk. Both conclude SRr' segs RZ_cf; the kit's post
   is the after-free fpostbm (its journal at wle') *)
Lemma pf_ff_of_kit : forall c0, PRH_FnAlloc.tfuzz_free_specX B ARx SK ->
  tfuzz_free_specO (PA := PA) B ARx SK (pf_PBk c0) pf_FXk.
Proof.
intros c0 X most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran HFP HR (Hc & Hc0 & Hh) Hfix H10 Hpin HL.
pose proof (YCbqG.admits_ct_fix (as_universe B) ly (pc_free_ra0 (as_code B)) regs ch S Hfix) as Htr.
eapply (SRr'_mono segs RZ_cf); [exact (X most own ly S Hp W regs mem md ch p n Lam peak cnt fail ran HFP (fun _ => HR)
  (fun _ => ltac:(lia)) (fun _ => Hh) Htr H10 Hpin HL)|].
(* The kit's budgeted post at the call's own FIXED trace is the plain post's R form at wle' *)
cbv beta. intros W' c' _ Hb. eapply fpost_of_fpostb_fix in Hb; [|exact Hfix].
destruct Hb as (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & Hpr & HQ).
exists ly', S', Hp', regs', mem', md', k. split; [exact Ec|]. split; [exact HJ|]. split; [exact Hpr|].
cbv beta delta [fQmn] in HQ. destruct HQ as [HK HMN].
(* The kit's post BY NAME (PRH_FnAlloc.v's projection layer): tffP_R_of reads it into the record tffP_R, whose fields and
   the arm records tffP_R1 / tffP_R2 name each conjunct; regs' and md' are the post's arguments its body does not
   mention, so they are given by name *)
pose proof (PRH_FnAlloc.tffP_R_of (regs' := regs') (md' := md') HK) as HRK. clear HK.
split; [|exact HMN].
split.
{ unfold pf_FXk. split.
  - destruct (PRH_FnAlloc.tffP_arm HRK) as [HA1 | HA2].
    + rewrite (PRH_FnAlloc.tffP1_state (PRH_FnAlloc.tffP_R1_of HA1)). lia.
    + destruct (PRH_FnAlloc.tffP_R2_of HA2) as (l1 & l2 & HR2).
      pose proof (PRH_FnAlloc.tffP2_ccnt24 HR2) as Heq. lia.
  - split; [exact (PRH_FnAlloc.tffP_hull HRK)|]. destruct (Z.eqb_spec p 0) as [E|E].
    + destruct (PRH_FnAlloc.tffP_arm HRK) as [HA1 | HA2];
        [exact (PRH_FnAlloc.tffP1_state (PRH_FnAlloc.tffP_R1_of HA1))|].
      destruct (PRH_FnAlloc.tffP_R2_of HA2) as (l1 & l2 & HR2). exfalso. exact (PRH_FnAlloc.tffP2_nonnull HR2 E).
    + intros sm x os i H0 L0 k1 hb1 HB Hk Hb. cbn [snd] in Hk.
      (* the field's run binders are implicit (the kit's layer is under Implicit Arguments): Hb determines them *)
      exact (PRH_FnAlloc.tffP_pos_bulk HRK E Hb (proj2 (prh_run_at_one sm x os i _) HB) Hk). }
split.
{ destruct (Z.eqb_spec p 0) as [E|E]; [|exact (PRH_FnAlloc.tffP_room HRK E)].
  destruct (PRH_FnAlloc.tffP_arm HRK) as [HA1 | HA2].
  - rewrite (PRH_FnAlloc.tffP1_state (PRH_FnAlloc.tffP_R1_of HA1)). exact HR.
  - destruct (PRH_FnAlloc.tffP_R2_of HA2) as (l1 & l2 & HR2). exfalso. exact (PRH_FnAlloc.tffP2_nonnull HR2 E). }
destruct (PRH_FnAlloc.tffP_arm HRK) as [HA1 | HA2].
- pose proof (PRH_FnAlloc.tffP_R1_of HA1) as HR1. left.
  split; [exact (PRH_FnAlloc.tffP1_null HR1)|]. split; [exact (PRH_FnAlloc.tffP1_hp HR1)|].
  split; [exact (PRH_FnAlloc.tffP1_ablocks HR1) | exact (PRH_FnAlloc.tffP1_ledger HR1)].
- destruct (PRH_FnAlloc.tffP_R2_of HA2) as (l1 & l2 & HR2). right.
  split; [exact (PRH_FnAlloc.tffP2_nonnull HR2)|]. split; [exact (PRH_FnAlloc.tffP2_hp HR2)|].
  split; [exact (PRH_FnAlloc.tffP2_ablocks HR2)|].
  exists l1, l2. split; [exact (PRH_FnAlloc.tffP2_lam HR2) | exact (PRH_FnAlloc.tffP2_ledger HR2)].
Qed.

Lemma pfk_reach_ccnt : forall F ly S F' ly' S',
  pf_reach pf_FXk F ly S F' ly' S' -> YGcfRoomLive.ccnt24 S' <= YGcfRoomLive.ccnt24 S.
Proof.
intros F ly S F' ly' S' HR.
induction HR as [L0 ly0 S0 | L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH | b L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH].
- lia.
- destruct HX as [HX _]. lia.
- destruct HX as [HX _]. lia.
Qed.

(* the hull meters never rise along the frees: each call keeps both (pf_FXk's hull_used at []) *)
Lemma pfk_reach_hull : forall F ly S F' ly' S',
  pf_reach pf_FXk F ly S F' ly' S' -> PresetHullBudget.hull_used S S' [].
Proof.
intros F ly S F' ly' S' HR.
induction HR as [L0 ly0 S0 | L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH | b L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH].
- exact (PresetHullBudget.hull_used_refl S0 []).
- destruct HX as [_ [HX _]]. exact (PresetHullBudget.hull_used_app S0 S1 S2 [] [] HX IH).
- destruct HX as [_ [HX _]]. exact (PresetHullBudget.hull_used_app S0 S1 S2 [] [] HX IH).
Qed.

(* from an empty list only NULL frees run, and they keep the state *)
Lemma pfk_reach_nil : forall F ly S F' ly' S', pf_reach pf_FXk F ly S F' ly' S' -> F = [] -> S' = S.
Proof.
intros F ly S F' ly' S' HR.
induction HR as [L0 ly0 S0 | L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH | b L0 ly0 S0 ly1 S1 L' ly2 S2 HX HR IH];
  intros E.
- reflexivity.
- destruct HX as [_ [_ HX]]. rewrite (IH E). exact HX.
- discriminate E.
Qed.

(* THE BULK ORDER CARRIED, for every model run: along F, the k-th free is L's k-th entry, so each non-NULL free moves
   the sub-position by one and the remaining list is L's next entries *)
Lemma pfk_reach_bulk : forall sm x os i H0 Lb F ly S F' ly' S',
  pf_reach pf_FXk F ly S F' ly' S' ->
  nth_error (PresetRun.hruns sm x os) i = Some (PresetReqAt.HBulk Lb) ->
  forall k hb, PresetRoomPosKeep.iface_room_pos_bulk sm x os i Lb k H0 hb S ->
  firstn (length F) (skipn k Lb) = map (fun b => snd b + cf_head) F ->
  exists k' hb', PresetRoomPosKeep.iface_room_pos_bulk sm x os i Lb k' H0 hb' S' /\
    firstn (length F') (skipn k' Lb) = map (fun b => snd b + cf_head) F' /\ (k' + length F' = k + length F)%nat.
Proof.
intros sm x os i H0 Lb F ly S F' ly' S' HR HB.
induction HR as [L0 ly0 S0 | L0 ly0 S0 ly1 S1 Lb' ly2 S2 HX HR IH | b L0 ly0 S0 ly1 S1 Lb' ly2 S2 HX HR IH];
  intros k hb Hb HO.
- exists k, hb. split; [exact Hb|]. split; [exact HO | reflexivity].
- destruct HX as [_ [_ HX]]. subst S1. exact (IH k hb Hb HO).
- destruct HX as [_ [_ HX]]. cbn [length map] in HO.
  destruct (pf_firstn_skipn_cons Lb k (length L0) _ _ HO) as (Hk & HO').
  destruct (HX sm x os i H0 Lb k hb HB Hk Hb) as (hb1 & Hb1).
  destruct (IH (Datatypes.S k) hb1 Hb1 HO') as (k' & hb' & Hb' & HO'' & Ek).
  exists k', hb'. split; [exact Hb'|]. split; [exact HO''|]. cbn [length]. lia.
Qed.

(* the bound and the hull budget along every reachable state, from the entry count within the bound and the entry
   budget (the budget for no event is kept: every step's hull use is at [], hull_budget_app) *)
Lemma pfk_safe : forall c0 F ly S,
  YGcfRoomLive.ccnt24 S <= c0 -> c0 <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S [] ->
  pf_safe pf_FXk (pf_PBk c0) F ly S.
Proof.
intros c0 F ly S Hc Hc0 Hh F' ly' S' HR. pose proof (pfk_reach_ccnt F ly S F' ly' S' HR) as Hc'.
unfold pf_PBk. split; [lia|]. split; [exact Hc0|].
exact (PresetHullBudget.hull_budget_app S S' [] [] Hh (pfk_reach_hull F ly S F' ly' S' HR)).
Qed.

(* THE KIT'S TEXT (PRH_FnPj.tpj_free_specX in the batch tree recorded as preset-tree-at-2026-10-29T23-27-23Z.tsv (sha256 1f0ae5f9ecde; internal record): post-implication form, no run words, the
   premise prh_head_wide) from the instrumented walk text, with the image walk a premise WALK under the kit's head-width
   premise (any image's instrumented walk gives the text; image B's walk cites the same lemma). The walk runs at
   pf_PBk (ccnt24 S) / pf_FXk; pf_safe by pfk_safe from the entry bound and entry hull budget (each needed only when
   v <> 0); the kit's hull use from the frees' reach (pfk_reach_hull). The
   position transfer, for every model run and position at S with the run's next events E = prhPj_free_evs F:
   F = [], E = []: every fuzz_free is NULL, the state is kept (pfk_reach_nil), the position is i + 0; F <> []:
   E = [HBulk (map (snd + cf_head) F)] at i (PRH_Base.prh_run_at_one), entered at sub-position 0
   (PresetRoomPosKeep.room_pos_bulk_enter), left at |F| = |map ..| (pfk_reach_bulk), and that is i + 1
   (room_pos_bulk_exit). The kit's text and the walk's both conclude SRr' segs RZ_cf with the post fpostWmR .. (wle' segs
   RZ_cf) ..; the journal passes through *)
Theorem pf_specX_of_walk : forall CTX0 n,
  (prh_head_wide -> forall PB FX, tfuzz_free_specO (PA := PA) B ARx SK PB FX ->
     tpj_free_specO (PA := PA) B ARx SK PB FX CTX0 n) ->
  PRH_FnAlloc.tfuzz_free_specX B ARx SK -> tpj_free_specX (PA := PA) B ARx SK CTX0 n.
Proof.
intros CTX0 n WALK XFF most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran
  HFP HU HR Hc Hh H10 HW HC HHW HL.
set (c0 := YGcfRoomLive.ccnt24 S).
assert (TXT : tfuzz_free_specO (PA := PA) B ARx SK (pf_PBk c0) pf_FXk) by exact (pf_ff_of_kit c0 XFF).
assert (HSF : v <> 0 -> pf_safe pf_FXk (pf_PBk c0) F ly S)
  by (intros Hv; exact (pfk_safe c0 F ly S ltac:(unfold c0; lia) ltac:(unfold c0; exact (Hc Hv)) (Hh Hv))).
pose proof (WALK HHW (pf_PBk c0) pf_FXk TXT most own ly S Hp W regs mem md ch d v D F Lam peak cnt fail ran
  HFP HU HR H10 HW HC HSF HL) as G.
eapply (SRr'_mono segs RZ_cf); [exact G|]. cbv beta.
intros W' c' _ (ly' & S' & Hp' & regs' & mem' & md' & k & Ec & HJ & HWIN & HP & [(HK0 & HRC) HMN]).
exists ly', S', Hp', regs', mem', md', k. split; [exact Ec|]. split; [exact HJ|]. split; [exact HWIN|].
split; [exact HP|]. split; [|exact HMN].
pose proof (pfk_reach_ccnt _ _ _ _ _ _ HRC) as Hc'.
destruct HK0 as (HR' & Lam' & HP1 & HP2 & HL' & H0 & HZ).
(* The kit's post BUILT BY NAME (PRH_FnPj.v's projection layer): the record tpfP_R field by field, then tpfP_Q_of_R; regs'
   is the post's argument its body does not mention, given by name, and md' is tpfP_Q_of_R's one explicit argument *)
refine (tpfP_Q_of_R (regs' := regs') (Lam' := Lam') md'
  {| tpfP_room := HR'; tpfP_hull := pfk_reach_hull _ _ _ _ _ _ HRC; tpfP_pos := _; tpfP_lam := HP1;
     tpfP_ablocks := HP2; tpfP_ledger := HL'; tpfP_null := H0; tpfP_zero := HZ; tpfP_ccnt24 := Hc' |}).
intros sm x os i H0' hist Hpos HRA.
destruct F as [|b F'].
- pose proof (pfk_reach_nil _ _ _ _ _ _ HRC eq_refl) as ES.
  exists hist. cbn [prhPj_free_evs length]. rewrite Nat.add_0_r, ES. exact Hpos.
- assert (HE : prhPj_free_evs (b :: F') = [PresetReqAt.HBulk (map (fun b => snd b + cf_head) (b :: F'))])
    by reflexivity.
  rewrite HE in HRA |- *. pose proof (proj1 (prh_run_at_one sm x os i _) HRA) as HB.
  pose proof (PresetRoomPosKeep.room_pos_bulk_enter sm x os i
    (map (fun b => snd b + cf_head) (b :: F')) H0' hist S Hpos) as Hb0.
  destruct (pfk_reach_bulk sm x os i H0' _ _ _ _ _ _ _ HRC HB 0%nat hist Hb0
    (pf_firstn_length_map _ (b :: F'))) as (k' & hb' & Hb' & _ & Ek).
  exists hb'. cbn [length]. replace (i + 1)%nat with (Datatypes.S i) by lia.
  apply (PresetRoomPosKeep.room_pos_bulk_exit sm x os i _ H0' hb' S' HB).
  rewrite length_map. cbn [length] in Ek |- *. replace (Datatypes.S (length F')) with k' by lia. exact Hb'.
Qed.
End obs.
