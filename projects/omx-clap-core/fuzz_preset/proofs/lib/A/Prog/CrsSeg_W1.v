(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Entry_r1.v, with its module paths and module names changed; 1673 of its 1709 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/CrsSeg_X1.v, with its module paths and module names changed; 1281 of its 1466 lines of code are new or changed and 1524 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 pins): segment W1 of the walk of check_reject_clean_starved, A' 0x82324 (+452)
   to 0x82358 (+504, H2) or 0x82410 (+688, R). Row CR-W1 of the crcs A' rows (the internal file PART7-ROWS.md);
   the closing lemma crs_seg_W1 : crs_from_R -> crs_from_H2 -> crs_from_W1.
   rule 24: proves function check_reject_clean_starved (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that
   lookup; CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its
   released rows were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). Written new; this file proves one segment lemma of it.
   INPUTS.
   - Pin A' asan sha256 1be0f53d96cb9d6c (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/A/Listing_prog.v blob 7ed1529926bd + lib/A/PAImg_prog.v blob 505a51ff7d08 (h-verbs-1 listings v3);
     entry 0x82160 = slot 736 (A_entry_check_reject_clean_starved); W1 = slots 849-861.
   - The kit lib/A/Prog/CrsKitAp.v blob cd00cafa2dbc (its crs_from_* at the re-hiding relation wle' SEGS RZ_cf) over
     the text tcheck_reject_clean_starved_specX (lib/A/PRH_FnCheck.v blob e3989e16a938); the
     ledger .. ran most own and fpre (with frm_zero at entry, FRM0-ENTRY: supplied at each call from crs_base's
     frm_zero) of lib/A/PRH_Base.v blob 39b170b3656d; the callee texts lib/A/PRH_FnAlloc.v blob bf282cf2f794
     (fuzz_free: no entry position, the class-24 bound and the hull budget only for p <> 0; its trace premise
     `admits ..`, given by YCbqG.admits_ct_fix from the fixed trace of w1_free_trace; its post budgeted at its own
     trace, read back by PRH_Base.fpost_of_fpostb_fix); pj_write through the interim crs_wexact (lib/A/Prog/CrsWexAp.v
     blob 8b5e3d0e730f: its `cnt < 2 ^ 62` from the boundary's crs_core, its consumer window prh_cons_from by
     CrsKitAp.crs_cons_sub), its entry events supplied by crs_run_split and PRH_Supply.v's prhWriter_pjw_evs_w_evs
     (blob e9069249fade); its post's prh_granted gives ran' = ran = 0 (PRW_CrsModel.crs_ran_of_granted, blob
     4d1e0e7dbb38) and, g_fail_at being SIZE_MAX, no failed allocation. The free's run event is the kit's
     crs_room_evs_of_run (from crs_pre's prh_run_at), so no event premise is taken.
   THE SEGMENT (A' 0x82324 .. 0x82354, 13 instructions; one lemma per stretch, backwards):
     0x82324 auipc s8              s8 = CRS_RO (crs_ro_atoms)                                   w1_at_A
     0x82328 lbu a0, 540(s8)       the g_own_ran_out byte: 0 (the boundary ledger's own cell, prh_ledger_own)
     0x8232c bnez a0 -> R          THE OWN ARM: not taken in the symbolic run (a0 = the literal 0)
     0x82330 jal fuzz_alloc_ran_out
     0x82334 bnez a0 -> R          THE RAN ARM: a0 = ran1 (the ledger's g_ran_out); refuted: ran1 = c_ran C = 0
                                   (crs_core, crs_pre), so W1 never exits to R
     0x82338 jal fuzz_alloc_count  a0 = cnt1 = crs_cnt1 C (crs_cnt_R with ran1 = 0)                  w1_at_P1
     0x8233c mv s7, a0 / addi a1, zero, 1 / mv a0, s3 / jal pj_write (doc, 1), FLOAT post          w1_at_P2
     0x8234c jal fuzz_free         the text q (a0) <> 0: pj_write's post states prh_granted, so no allocation
                                   failed (the NULL arm is refuted) and the free's event is the HFr of the model's
                                   last capacity (crs_room_evs_of_run, w1_wcap_full)                   w1_at_P3
     0x82350 jal fuzz_alloc_count  a0 = crs_cnt1 C + k1, k1 the pretty write's calls (crs_wfull)     w1_at_P4
     0x82354 beq a0, s7 -> R       refuted: 1 <= k1 (crs_kfull), both counts below 2 ^ 62           w1_at_P5
     0x82358 = H2                  crs_from_H2 with k1 and g_ran_out = c_ran C = 0
   PREMISES (the rows' order): HI_head (instance fact, witness crs_W1_HI_head at CfParams_preset), HI_hull (instance
   fact: the run's two meter caps within cp's caps, witness crs_W1_HI_hull; fuzz_free's hull budget), the callee texts
   HT_fuzz_alloc_count / HT_fuzz_alloc_ran_out / HT_fuzz_free (the texts, forall fx'), HT_fuzz_free0 (crs_free0),
   HW_exact (pj_write), HK : CrsKeep, HB_took : c_took C <= 2 ^ 28, crs_cnt24_W1 (the free's class-24 bound, its own
   premise), the continuations crs_from_R / crs_from_H2. No own-cell premise (kit v3: the ledger holds it at 0).
   On the batch kit's cut HT_fuzz_free0 and crs_from_R are not used (the RAN arm and the NULL free are refuted); they stay so
   that the row's statement is unchanged.
   Numerals: 452 .. 504, 688 (LENGTH: byte offsets of the listing's slots from the entry, 4 * slot); 540 (LENGTH, the
   lbu's offset, CrsKitAp's CRS_OFF_OWN); 33 (DERIVED: DOC_D); 24, 28, 62, 64 as powers of 2 (DERIVED / WORD bounds);
   42, 51, 298 (DERIVED: the symbolic engine's atom numbers of a0, s3 and the hi atom 18). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp WriterSpec WriterApp WriterAppFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRun PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetDrvHullA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_WalkEnv PRW_CrsModel CrsKitAp CrsWexAp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import CrsFree0Ap.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1ImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require CfParamsPreset.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* the import closure leaves lia's division / modulo conversion off (the flag below: ZifyNat sets it true, and project modules imported after it, such as lib/Reusable/YA09.v and YF0v.v, set it back to false); this file's
   arithmetic over x / 8 and x mod 2 ^ 64 needs it, so it is on for this file only *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================================================================================== *)
(* ---- the writer's model (pure): a run that did not fail is the all-granted run, whose last capacity is the last
   of its grow calls (PresetReqAt.wcaps) ---- *)
Lemma w1_pw_ok : forall P ok st, WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok st P) = 0 ->
  PRH_FnWriter.prhWriter_putN ok st P = WriterApp.putN st P.
Proof.
induction P as [|b P IH]; intros ok st H; cbn [PRH_FnWriter.prhWriter_putN] in H |- *;
  [rewrite WriterApp.putN_nil; reflexivity|].
rewrite WriterApp.putN_cons. destruct (PRH_FnWriter.prhWriter_grows st b) eqn:G.
- destruct (hd true ok) eqn:Eh.
  + rewrite crs_put1_true in H |- *. exact (IH _ _ H).
  + exfalso. unfold PRH_FnWriter.prhWriter_put1 in H. rewrite G in H. cbv zeta in H.
    destruct (WriterApp.w_cnt st =? WriterApp.w_fail st);
      (rewrite crs_pw_failed in H; [cbn in H; discriminate | cbn; discriminate]).
- exact (IH ok (WriterApp.put1 st b) H).
Qed.

Lemma w1_last_default : forall (A : Type) (l : list A) (z d1 d2 : A), last (z :: l) d1 = last (z :: l) d2.
Proof. intros A l. induction l as [|a l IH]; intros z d1 d2; [reflexivity | exact (IH a d1 d2)]. Qed.

Lemma w1_grow_cap_last : forall ls x c, WriterSpec.grow_cap x c ls = last (WriterSpec.grow_calls x c ls) c.
Proof.
induction ls as [|l ls IH]; intros x c; [reflexivity|].
rewrite WriterAppFacts.grow_cap_cons, WriterAppFacts.grow_calls_cons.
destruct (c <? x + l + 1).
- rewrite IH. destruct (WriterSpec.grow_calls (x + l) (WriterSpec.newcap c (x + l + 1)) ls) as [|z l0]; [reflexivity|].
  cbn [last]. apply w1_last_default.
- apply IH.
Qed.

(* the whole write with no injected failure that did not fail: its buffer's capacity is the model's last *)
Lemma w1_wcap_full : forall t p ok cnt,
  0 <= cnt -> cnt + Z.of_nat (PresetReqAt.wcalls t p) + 1 < 2 ^ 64 ->
  WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces t p)) = 0 ->
  WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 cnt SIZE_MAXZ) (WriterValue.wdpieces t p)) =
  last (PresetReqAt.wcaps t p) 0.
Proof.
intros t p ok cnt H0 H1 Hf. rewrite (w1_pw_ok _ _ _ Hf).
unfold PresetReqAt.wcalls, PresetReqAt.wcaps in H1. unfold PresetReqAt.wcaps.
rewrite (WriterAppFacts.putN_ok (WriterValue.wdpieces t p) (WriterApp.w0 cnt SIZE_MAXZ)).
- cbn [WriterApp.w_text WriterApp.w_cap WriterApp.w0 length]. change (Z.of_nat 0) with 0. apply w1_grow_cap_last.
- reflexivity.
- cbn [WriterApp.w_cnt WriterApp.w0]. exact H0.
- cbn [WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w0 length]. change (Z.of_nat 0) with 0. lia.
- right. cbn [WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w0 length].
  change (Z.of_nat 0) with 0. unfold SIZE_MAXZ. lia.
Qed.


(* ======================================================================================================== *)
(* ---- a tree's block predicate matters only on its own blocks (CrsSeg_X1.v x_*_lblk, ported under the w1_ prefix: the
   tree at the moved Lam is the same tree, with no proposition extensionality) ---- *)
Section pjl.
Variable segs : list Segment.
Lemma w1_cstrR_lblk : forall m lblk lblk' a k s, pj_cstrR segs m lblk a k s -> (lblk a k -> lblk' a k) ->
  pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma w1_itemsR_lblk : forall (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall a0 u D1, In u l -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_itemsR P a l D -> pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & H1 & H2). exists D1, D2. split; [exact E|].
split; [apply (H a u D1); [left; reflexivity | rewrite E; apply incl_appl, incl_refl | exact H1]|].
apply (IH (a + 56) D2); [|exact H2].
intros a0 v D3 Hv Hinc HP. apply (H a0 v D3); [right; exact Hv | rewrite E; apply incl_appr; exact Hinc | exact HP].
Qed.

Lemma w1_memsR_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  (forall a0 u D1, (exists nm, In (nm, u) l) -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D HL H Hl; cbn [pj_memsR] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & H1 & H2). exists x, k, D1, D2.
split; [exact E|]. split; [exact Hx|].
split; [apply (w1_cstrR_lblk m lblk lblk'); [exact Hc | apply HL; rewrite E; left; reflexivity]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | rewrite E; intros y Hy; right; apply in_or_app; left; exact Hy
  | exact H1]|].
apply (IH (a + 56) (ka + 8) D2); [| |exact H2].
- intros b k' Hin. apply HL. rewrite E. right. apply in_or_app. right. exact Hin.
- intros a0 v D3 (nm' & Hv) Hinc HP. apply (H a0 v D3); [exists nm'; right; exact Hv | | exact HP].
  rewrite E. intros y Hy. right. apply in_or_app. right. exact (Hinc y Hy).
Qed.

Lemma w1_nodeR_lblk : forall t m lblk lblk' p D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  pj_nodeR segs m lblk p t D -> pj_nodeR segs m lblk' p t D.
Proof.
intros t. induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; intros m lblk lblk' p D HL H;
  cbn [pj_nodeR] in H |- *;
  destruct H as (Hn & Ha & num & str & kids & keys & n & cap & Hh & Hb);
  (split; [exact Hn|]); (split; [exact Ha|]); exists num, str, kids, keys, n, cap; (split; [exact Hh|]).
- exact Hb.
- exact Hb.
- exact Hb.
- destruct Hb as (E1 & E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E1|]. split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (w1_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (w1_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & Hl)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hl]. rewrite ED, (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (w1_itemsR_lblk (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di); [|exact Hi].
  intros a0 u D1 Hu Hinc HP. rewrite Forall_forall in IH. apply (IH u Hu m lblk lblk' a0 D1); [|exact HP].
  intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & L0 & L1)]; [left; exact Hz | right; split; [exact Hp|]].
    rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    split; apply HL; [rewrite ED; left; reflexivity | exact L0 | rewrite ED; right; left; reflexivity | exact L1]. }
  exists Di. split; [exact ED|].
  apply (w1_memsR_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di); [| |exact Hi].
  + intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact Hin.
  + intros a0 u D1 (nm & Hu) Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m lblk lblk' a0 D1); [|exact HP].
    intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
Qed.
End pjl.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
#[local] Notation PA := (PI_prog_A).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ A_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ A_prog_listing PA).
#[local] Notation PST := (prh_pst (PI := prh_img_A)).

(* the pcs inside W1 (byte offsets from the listing base, as CrsKitAp's CRS_PC_<SEG>) *)
Definition W1_P1 : Z := CRS_PC0 + 468.   (* after fuzz_alloc_ran_out: bnez a0 *)
Definition W1_P2 : Z := CRS_PC0 + 476.   (* after the first fuzz_alloc_count: mv s7, a0 *)
Definition W1_P3 : Z := CRS_PC0 + 492.   (* after pj_write: jal fuzz_free *)
Definition W1_P4 : Z := CRS_PC0 + 496.   (* after fuzz_free: jal fuzz_alloc_count *)
Definition W1_P5 : Z := CRS_PC0 + 500.   (* after the second fuzz_alloc_count: beq a0, s7 *)

Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARx).
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B PST ARx).
(* the re-hiding relation of the cuts after pj_parse (the kit's crs_from_W1 / H2 / R) *)
#[local] Notation WR := (wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRr := (wle'_refl SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRt := (wle'_trans SEGS YGcfRehidePost.RZ_cf).
#[local] Notation WRw := (wle_wle' SEGS YGcfRehidePost.RZ_cf).
#[local] Notation LEDGER := (prh_ledger (PI := prh_img_A) (PA := PA) B).
#[local] Notation STK := (STK_check_reject_clean_starved (PI := prh_img_A)).
#[local] Notation cbase := (@crs_baseR fx rc ci cp RL SK B ARx).
#[local] Notation cpre := (@crs_pre fx rc ci cp RL B ARx).
#[local] Notation cpost := (@crs_post fx rc cp RL SK B ARx).
#[local] Notation cJ := (@crs_JR rc SK B ARx).
#[local] Notation clive := (@crs_live rc cp RL B).
#[local] Notation ccore := (@crs_core rc cp RL B).
#[local] Notation cperm := (@crs_perm rc B).
#[local] Notation cdat := (@crs_dat rc B).
#[local] Notation cfromR := (@crs_from_R fx rc ci cp RL SK B ARx).
#[local] Notation cfromH2 := (@crs_from_H2 fx rc ci cp RL SK B ARx).
#[local] Notation cfromW1 := (@crs_from_W1 fx rc ci cp RL SK B ARx).

(* ======================================================================================================== *)
(* ---- THE NAMED PREMISES OF THIS SEGMENT ---- *)

(* the class-24 live-set bound fuzz_free's text asks at its entry, in h-pre-b1's PresetCfnA.counts_of_room_pos_rl
   shape (every position of the model run that matches the state bounds it) *)
Definition crs_cnt24_W1 (C : crsC) : Prop :=
  forall (i : nat) (hist : list YG00.chunk) (S : astate),
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) i (c_rp_H0 C) hist S ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.

(* ======================================================================================================== *)
(* ---- THE STATE BETWEEN W1's CALLS: what crs_from_W1 carries, with s8 = CRS_RO from the auipc on, over a world
   relation R (its boundary is crs_baseR R); w1_st is w1_stR at wle ---- *)
Definition w1_stR (R : world SEGS -> world SEGS -> Prop) (CTX0 : list (list Z)) (C : crsC) (fxk : YK11.FPState)
  (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) (k sp2 : Z) (Lam : list (Z * Z)) (peak cnt ran : Z) (evs : list PresetReqAt.hev) : Prop :=
  cbase R CTX0 C fxk ly S Hp W regs mem md k sp2 /\
  crs_regsat regs (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) /\
  clive C ly S Hp W mem Lam peak cnt ran evs /\ cdat C ly S Hp W mem Lam /\ crs_tree C ly S Lam W mem.
Definition w1_st (CTX0 : list (list Z)) (C : crsC) (fxk : YK11.FPState) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k sp2 : Z)
  (Lam : list (Z * Z)) (peak cnt ran : Z) (evs : list PresetReqAt.hev) : Prop :=
  w1_stR (@wle SEGS) CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs.
Lemma w1_st_R_wle : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs,
  w1_st CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs =
  w1_stR (@wle SEGS) CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs.
Proof. reflexivity. Qed.

(* ======================================================================================================== *)
(* ---- STRETCH A: W1's entry to `jal fuzz_alloc_ran_out` (the auipc, the lbu of the own cell, the OWN arm) ---- *)
Definition w1_own_rg : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition ss_W1a : sstate := mkSS CRS_PC_W1 cur_atoms [w1_own_rg] None (mkFacts [] [] []).

Lemma w1_obj13 : forall regs0 regsc more, bv_unsigned (ew (TE regs0 regsc more) (A_OBJ 13)) = @pi_g_own_ran_out prh_img_A.
Proof.
intros regs0 regsc more. unfold TE. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite unsigned_lit_small by (apply pa_val_range). exact (proj2 crs_ro_atoms).
Qed.

Lemma w1a_seat : forall (fxk : YK11.FPState) (W : world SEGS) regs mem,
  prh_own W mem 0 ->
  st_ok_pi (fx := fxk) SEGS VAL (TE regs regs []) ss_W1a
    (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + CRS_PC_W1)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxk W regs mem [Hown _].
apply ts_st_ok.
- apply te_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor].
  pose proof (@pa_val_range _ _ PA (A_OBJ 13)) as R13. rewrite (proj2 crs_ro_atoms) in R13.
  apply (ts_rok _ _ (A_OBJ 13) (@pi_g_own_ran_out prh_img_A)); [apply w1_obj13 | lia | lia | intros o Ho; lia |].
  constructor; [|constructor].
  apply (ts_chunk _ _ _ 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Hown.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; exact I].
Qed.

(* ======================================================================================================== *)
(* ---- THE FRAME-POINTER CHAIN AT W1's CALLS: s0 is the entry sp, its record is the prologue's two saves (ra at
   sp0 - 8, the entry s0 at sp0 - 16), then the entry chain (crs_pre's fpre), read through the journal's clause for
   bytes at or above alloc_ceiling outside the function's window (all of the caller's stack) ---- *)
Lemma w1_fpchain_agree : forall (rd rd' : reader) lo top ch bp,
  (forall a, lo <= a < top -> rd' a = rd a) -> lo + 16 <= bp -> bp <= top ->
  Forall (fun r => lo + 16 <= fst (fst r)) ch ->
  fpchain (rdword rd) bp top ch -> fpchain (rdword rd') bp top ch.
Proof.
intros rd rd' lo top ch. induction ch as [|[[fp ra] nfp] rest IH]; intros bp Hrd Hbp Hbt HF Hch; cbn [fpchain] in Hch |- *.
- destruct Hch as (r & Hr & Hr1). exists r. split; [|exact Hr1].
  rewrite (rdword_ext rd rd' (bp - 8)); [exact Hr | intros k0 Hk0; apply Hrd; lia].
- destruct Hch as (E & Hal & Hra & Hnfp & H4 & Hrest). subst fp.
  inversion HF as [|x l Hx HF']; subst. cbn [fst] in Hx.
  split; [reflexivity|]. split; [exact Hal|].
  split; [rewrite (rdword_ext rd rd' (bp - 8)); [exact Hra | intros k0 Hk0; apply Hrd; lia]|].
  split; [rewrite (rdword_ext rd rd' (bp - 16)); [exact Hnfp | intros k0 Hk0; apply Hrd; lia]|].
  split; [exact H4|].
  destruct (bad_next bp top nfp) eqn:Eb; [exact Hrest|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb _]. apply orb_false_iff in Eb as [Eb Eb2].
  apply Z.leb_gt in Eb. apply Z.leb_gt in Eb2.
  apply (IH nfp Hrd ltac:(lia) ltac:(lia) HF' Hrest).
Qed.

(* the unwinder's trace of a call whose first record is (sp, r, s0) is the prh_trace of r and the chain's spine *)
Lemma w1_unwind_prh : forall pc0 a r b ch, unwind_of_chain pc0 ((a, r, b) :: ch) = prh_trace pc0 r (spine ch).
Proof.
intros pc0 a r b ch. unfold unwind_of_chain, prh_trace, spine. f_equal. f_equal. cbn [flat_map app].
f_equal. induction ch as [|[[x y] z] t IH]; [reflexivity|]. cbn [flat_map map fst snd]. rewrite IH. reflexivity.
Qed.

(* the chain at a call of W1: the prologue's record over the entry chain, or none when sp0 is at the stack top *)
Definition w1_ch (C : crsC) (ly : alayout) : list (Z * Z * Z) :=
  if spZ (c_regs C) <? ly_top ly - 16 then (spZ (c_regs C), raZ (c_regs C), s0Z (c_regs C)) :: c_ch C else [].

Lemma w1_achain : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2,
  cpre CTX0 C -> cJ R C ly3 S3 Hp3 W3 mem3 md3 k -> crs_saved C W3 mem3 ->
  spZ (c_regs C) - CRS_FRAME <= sp2 -> sp2 <= spZ (c_regs C) - 128 ->
  achain ly3 (aview SEGS (w_H W3) mem3) sp2 (spZ (c_regs C)) (w1_ch C ly3).
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2 HP HJ HSV Hs1 Hs2.
destruct HP as ((HAF & _ & Hsp64 & _) & _).
destruct HAF as (_ & _ & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
destruct HJ as (_ & Hle & _ & _ & _ & _ & _ & _ & HK1 & _).
destruct Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
inversion HSV as [|p1 l1 Hra Hsv1]; subst. inversion Hsv1 as [|p2 l2 Hs0 _]; subst.
cbn [fst snd] in Hra, Hs0. fold (raZ (c_regs C)) in Hra. fold (s0Z (c_regs C)) in Hs0.
set (sp0 := spZ (c_regs C)) in *.
replace (sp0 - 128 + 120) with (sp0 - 8) in Hra by lia. replace (sp0 - 128 + 112) with (sp0 - 16) in Hs0 by lia.
assert (Hc144 : CRS_FRAME = 144) by (rewrite crs_frame_is_pi; reflexivity).
assert (Hal8 : sp0 mod 8 = 0).
{ apply Z.mod_divide in Hal16; [|lia]. destruct Hal16 as [q Hq]. rewrite Hq. replace (q * 16) with ((2 * q) * 8) by lia.
  apply Z.mod_mul. lia. }
assert (Hrd : forall a, sp0 <= a < ly_top ly3 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W C)) (c_mem C) a).
{ intros a Ha. rewrite Etop in Ha. apply HK1; lia. }
unfold w1_ch. fold sp0. destruct (Z.ltb_spec sp0 (ly_top ly3 - 16)) as [Hlt|Hge].
- right. split; [lia|]. split; [exact Hlt|]. split; [exact Hal8|].
  destruct Hch as [(Hbad & Ech) | (Hv1 & Hv2 & Hv3 & Hfc & HF)].
  + rewrite Ech. split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal8|]. split; [exact Hra|]. split; [exact Hs0|].
      split; [exact Hra4|].
      destruct (bad_next sp0 (ly_top ly3) (s0Z (c_regs C))) eqn:Eb; [reflexivity|].
      exfalso. unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb Eb3]. apply orb_false_iff in Eb as [Eb1 Eb2].
      apply Z.leb_gt in Eb1. apply Z.leb_gt in Eb2. apply negb_false_iff, Z.eqb_eq in Eb3.
      rewrite Etop in Eb2. lia.
    * constructor; [cbn; lia | constructor].
  + split.
    * cbn [fpchain]. split; [reflexivity|]. split; [exact Hal8|]. split; [exact Hra|]. split; [exact Hs0|].
      split; [exact Hra4|].
      assert (Eb : bad_next sp0 (ly_top ly3) (s0Z (c_regs C)) = false).
      { unfold bad_next. rewrite Etop. apply orb_false_iff. split; [apply orb_false_iff; split; apply Z.leb_gt; lia|].
        apply negb_false_iff, Z.eqb_eq. exact Hv3. }
      rewrite Eb. rewrite Etop.
      apply (w1_fpchain_agree (aview SEGS (w_H (c_W C)) (c_mem C)) (aview SEGS (w_H W3) mem3) sp0 _ (c_ch C)
        (s0Z (c_regs C))); [| lia | lia | exact HF | exact Hfc].
      intros a Ha. apply Hrd. rewrite Etop. exact Ha.
    * constructor; [cbn; lia|]. eapply Forall_impl; [|exact HF]. intros r Hr. cbn beta in Hr. lia.
- left. split; [right; left; lia | reflexivity].
Qed.

(* the trace of W1's fuzz_free (return site BASE + W1_P4), in the universe by the universe closure *)
Lemma w1_free_trace : forall CTX0 C ly regs,
  cpre CTX0 C -> getr regs 1 = w64 (BASE + W1_P4) -> getr regs 8 = w64 (spZ (c_regs C)) ->
  In (call_trace ly (pc_free_ra0 (as_code B)) regs (w1_ch C ly)) (as_universe B).
Proof.
intros CTX0 C ly regs HP Hr1 Hr8.
pose proof HP as (_ & _ & HU & HCTX & _).
assert (Hr : In (BASE + W1_P4) (@pi_ret_sites prh_img_A F_check_reject_clean_starved RT_fuzz_free))
  by (vm_compute; left; reflexivity).
assert (Hfp : @pi_fp prh_img_A F_check_reject_clean_starved = true) by reflexivity.
assert (EraZ : raZ regs = BASE + W1_P4).
{ unfold raZ. rewrite Hr1. unfold w64. apply unsigned_lit_small. vm_compute. split; congruence. }
unfold call_trace. destruct (frame0_ok ly regs).
- unfold w1_ch. destruct (spZ (c_regs C) <? ly_top ly - 16).
  + rewrite w1_unwind_prh, EraZ. cbn [spine map fst snd].
    exact (prh_univ_closure_site B CTX0 F_check_reject_clean_starved _ RT_fuzz_free _ HU HCTX Hfp Hr).
  + rewrite w1_unwind_prh, EraZ. cbn [spine map].
    exact (prh_univ_closure_lit B CTX0 F_check_reject_clean_starved RT_fuzz_free _ HU Hr).
- destruct HU as (HU1 & _). exact (HU1 RT_fuzz_free).
Qed.

(* ======================================================================================================== *)
(* ---- A CALL OF W1 (YCbqGcall.v aj_call_x_spR) at a world relation R (reflexive, transitive): at the callee's
   entry the runner left the state ms (pc = the callee, ra = BASE + retk); the caller's sp is sp2, its s0 the entry
   sp. The callee's pre is the fpre at the chain w1_ch, its post the engine's apost_base_xR at R; the post composes
   the callee's journal with crs_JR ---- *)
Lemma w1_call : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
  (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) CTX0 C fxk W E ss ms mdc ly S Hp k sp2 STK1 FP1 retk
  (QQ : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  st_ok (fx := fxk) SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  cbase R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 ->
  getr (ms_regs ms) 2 = w64 sp2 -> getr (ms_regs ms) 8 = w64 (spZ (c_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  4096 <= BASE + retk < 2 ^ 40 ->
  0 <= STK1 -> STK1 + 144 <= STK ->
  fp_sub_x B STK (spZ (c_regs C)) [] FP1 (c_ly C) (c_S C) [(CRS_CID, c_fpos C)] ly S ->
  (fpre (fx := fxk) B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc (w1_ch C ly) ->
   SRrG SEGS R W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (apost_base_xR (fx := fxk) (SK := SK) SEGS B PST ARx R STK1 FP1 (ms_regs ms) ly S Hp W (ms_mem ms) mdc QQ)) ->
  (forall W2 ly2 S2 Hp2 regs2 mem2 md2 k1, R W W2 ->
   AJR R STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C)
     [(CRS_CID, c_fpos C)]
     ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
   AJR R STK1 sp2 FP1 ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
   aregs_preserved (ms_regs ms) regs2 -> QQ ly2 S2 Hp2 W2 regs2 mem2 md2 ->
   SRrG SEGS R W2 (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + retk)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt CTX0 C fxk W E ss ms mdc ly S Hp k sp2 STK1 FP1 retk QQ Q HS Hrv HB R2 R8 R1 Hrk Hrk2 Hbr Hstk1 Hbud HFP
  Hcallee Hcont.
pose proof HB as (HP & Hfz & _ & HJ & _ & HSV & _ & HROD & _ & Hgp & Htp & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HP as ((HAF & _ & Hsp64 & _) & _).
pose proof HAF as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof (proj1 HJ) as HAR. pose proof (proj1 (proj2 HJ)) as Hle.
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
pose proof asan_consts as (C1 & _).
assert (Hc144 : CRS_FRAME = 144) by (rewrite crs_frame_is_pi; reflexivity).
set (sp0 := spZ (c_regs C)) in *.
assert (Hsp2 : spZ (ms_regs ms) = sp2).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
assert (Hs0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hraw : bv_unsigned (Z_to_bv 64 (BASE + retk)) = BASE + retk) by (apply unsigned_lit_small; lia).
eapply (SRrG_bind SEGS R Rt).
{ eapply (@aj_call_x_spR fxk rc SK SEGS B PST ARx _ LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK sp0 []
    (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly S Hp mdc
    k STK1 FP1
    (sp2 - sp0) (Z_to_bv 64 (BASE + retk)) (w1_ch C ly) QQ HS Hrv HJ).
  - rewrite Hsp2. lia.
  - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hs3; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hs3 as [q2 Hq2].
    replace (sp2 - sp0) with ((2 * q2 - q1) * 16) by lia. apply Z.mod_mul. lia.
  - lia.
  - exact Hstk1.
  - lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [exact Hrk | exact Hrk2].
  - rewrite Hraw. lia.
  - rewrite Hs0. replace (sp0 + (sp2 - sp0)) with sp2 by lia.
    exact (w1_achain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 HP HJ HSV ltac:(lia) Hs2).
  - intros HPRE. apply Hcallee. split; [exact HPRE|]. split; [exact HROD|]. split.
    + rewrite Hsp2, Ehi. lia.
    + split; [unfold raZ; rewrite R1, Hraw; lia | exact Hfz].
  - exact HFP. }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJc & HP2 & HQ).
replace (sp0 + (sp2 - sp0)) with sp2 in HJc by lia.
exact (Hcont W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hwle HJ2 HJc HP2 HQ).
Qed.

(* the same call for a callee that posts in the FLOAT form (pj_write: decff's fpostFm, its puts reach snprintf):
   YCbqGcall.v aj_call_xF_spR; the continuation runs at the callee's float state fx' (frm 0, fs0-fs11 kept) *)
Lemma w1_callF : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
  (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) CTX0 C fxk W E ss ms mdc ly S Hp k sp2 STK1 FP1 retk
  (QQ : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world SEGS -> config -> Prop),
  st_ok (fx := fxk) SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  cbase R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 ->
  getr (ms_regs ms) 2 = w64 sp2 -> getr (ms_regs ms) 8 = w64 (spZ (c_regs C)) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  4096 <= BASE + retk < 2 ^ 40 ->
  0 <= STK1 -> STK1 + 144 <= STK ->
  fp_sub_x B STK (spZ (c_regs C)) [] FP1 (c_ly C) (c_S C) [(CRS_CID, c_fpos C)] ly S ->
  (fpre (fx := fxk) B ARx STK1 ly S Hp W (ms_regs ms) (ms_mem ms) mdc (w1_ch C ly) ->
   SRrG SEGS R W (mkCfg (@YK11.mkst fxk (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (ms_mem ms) (YK11.seg_rom SEGS)) mdc)
     (apost_base_xFR (fx := fxk) (SK := SK) SEGS B PST ARx R STK1 FP1 (ms_regs ms) ly S Hp W (ms_mem ms) mdc QQ)) ->
  (forall (fx' : YK11.FPState) W2 ly2 S2 Hp2 regs2 mem2 md2 k1, R W W2 ->
   frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
   AJR R STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C)
     [(CRS_CID, c_fpos C)]
     ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
   AJR R STK1 sp2 FP1 ly S Hp W (ms_mem ms) mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
   aregs_preserved (ms_regs ms) regs2 -> QQ ly2 S2 Hp2 W2 regs2 mem2 md2 ->
   SRrG SEGS R W2 (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + retk)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt CTX0 C fxk W E ss ms mdc ly S Hp k sp2 STK1 FP1 retk QQ Q HS Hrv HB R2 R8 R1 Hrk Hrk2 Hbr Hstk1 Hbud HFP
  Hcallee Hcont.
pose proof HB as (HP & Hfz & _ & HJ & _ & HSV & _ & HROD & _ & Hgp & Htp & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HP as ((HAF & _ & Hsp64 & _) & _).
pose proof HAF as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof (proj1 HJ) as HAR. pose proof (proj1 (proj2 HJ)) as Hle.
pose proof Hle as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _ & Ehi & _).
pose proof asan_consts as (C1 & _).
assert (Hc144 : CRS_FRAME = 144) by (rewrite crs_frame_is_pi; reflexivity).
set (sp0 := spZ (c_regs C)) in *.
assert (Hsp2 : spZ (ms_regs ms) = sp2).
{ unfold spZ. rewrite R2. unfold w64. apply unsigned_lit_small. lia. }
assert (Hs0 : s0Z (ms_regs ms) = sp0).
{ unfold s0Z. rewrite R8. unfold w64. apply unsigned_lit_small. lia. }
assert (Hraw : bv_unsigned (Z_to_bv 64 (BASE + retk)) = BASE + retk) by (apply unsigned_lit_small; lia).
eapply (SRrG_bind SEGS R Rt).
{ eapply (@aj_call_xF_spR fxk rc SK SEGS B PST ARx _ LAWS (@pa_segs_low _ _ PA) R Rr Rt W E ss ms STK sp0 []
    (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C) [(CRS_CID, c_fpos C)] ly S Hp mdc
    k STK1 FP1
    (sp2 - sp0) (Z_to_bv 64 (BASE + retk)) (w1_ch C ly) QQ HS Hrv HJ).
  - rewrite Hsp2. lia.
  - apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hs3; [|lia].
    destruct Hal16 as [q1 Hq1]. destruct Hs3 as [q2 Hq2].
    replace (sp2 - sp0) with ((2 * q2 - q1) * 16) by lia. apply Z.mod_mul. lia.
  - lia.
  - exact Hstk1.
  - lia.
  - rewrite Hgp. exact Hgp0.
  - rewrite Htp. exact Htp0.
  - exact R1.
  - apply (ret_ok_codeptr_v (PI := PA)); [exact Hrk | exact Hrk2].
  - rewrite Hraw. lia.
  - rewrite Hs0. replace (sp0 + (sp2 - sp0)) with sp2 by lia.
    exact (w1_achain R CTX0 C ly S Hp W (ms_mem ms) mdc k sp2 HP HJ HSV ltac:(lia) Hs2).
  - intros HPRE. apply Hcallee. split; [exact HPRE|]. split; [exact HROD|]. split.
    + rewrite Hsp2, Ehi. lia.
    + split; [unfold raZ; rewrite R1, Hraw; lia | exact Hfz].
  - exact HFP. }
cbv beta. intros W2 c2 Hwle (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HFZ & HFK & HJ2 & HJc & HP2 & HQ).
replace (sp0 + (sp2 - sp0)) with sp2 in HJc by lia.
exact (Hcont fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hwle HFZ HFK HJ2 HJc HP2 HQ).
Qed.

(* crs_base at the callee's float state: frm 0 and the entry's fs0-fs11 kept through both *)
Lemma w1_base_fx : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk fx' ly S Hp W regs mem md k sp2,
  cbase R CTX0 C fxk ly S Hp W regs mem md k sp2 -> frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fxk fx' ->
  cbase R CTX0 C fx' ly S Hp W regs mem md k sp2.
Proof.
intros R CTX0 C fxk fx' ly S Hp W regs mem md k sp2 (HP & _ & Hfk & Hrest) HFZ HFK.
split; [exact HP|]. split; [exact HFZ|]. split; [|exact Hrest].
intros r Hr. rewrite (HFK r Hr). exact (Hfk r Hr).
Qed.

(* ======================================================================================================== *)
(* ---- WHAT A CALL KEEPS OF crs_base: the own frame (its flag word, its bytes, the local's shadow) and the saved
   words by the callee's journal; the read-only view by its image clause; the registers by aregs_preserved ---- *)
Lemma w1_pairwise_cross : forall {X : Type} (R : X -> X -> Prop) l1 l2 x y,
  pairwise R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
Proof.
intros X R l1. induction l1 as [|z t IH]; intros l2 x y H Hx Hy; [destruct Hx|].
cbn [app pairwise] in H. destruct H as [HF Hp]. destruct Hx as [<-|Hx].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hy.
- exact (IH l2 x y Hp Hx Hy).
Qed.

Lemma w1_blk_frame : forall ly S Hp W mem md p n cid pos a, ARx ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> p <= a < p + req_size n ->
  frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid -> False.
Proof.
intros ly S Hp W mem md p n cid pos a HAR Hb Hf Ha1 Ha2.
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [Hpw _].
pose proof (w1_pairwise_cross _ _ _ (p, req_size n) (frame_addr ly cid pos, fs_frame_bytes cid) Hpw
  (in_map (fun b => (fst b, req_size (snd b))) _ (p, n) Hb)
  (in_map (fun f => (frame_addr ly (fst f) (snd f), fs_frame_bytes (fst f))) _ (cid, pos) Hf)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma w1_blk_shadow : forall ly S Hp W mem md p n cid pos a, ARx ly S Hp W mem md ->
  In (p, n) (ablocks B ly S) -> In (cid, pos) (frames S) -> p <= a < p + req_size n ->
  shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 -> False.
Proof.
intros ly S Hp W mem md p n cid pos a HAR Hb Hf Ha1 Ha2.
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md p n HAR Hb) as (_ & _ & _ & Happ & _).
destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as [_ HF].
rewrite Forall_forall in HF. specialize (HF (cid, pos) Hf). cbn [fst snd] in HF.
pose proof asan_consts as (C1 & _).
pose proof (fs_frame_bytes_nonneg cid) as Hb0.
unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia.
Qed.

Lemma w1_aregs : forall regs regs2 (r : bv 5), aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) ->
  getr regs2 r = getr regs r.
Proof. intros regs regs2 r H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma w1_regsat_kept : forall regs regs2 l, aregs_preserved regs regs2 ->
  Forall (fun p => acallee_saved (bv_unsigned (fst p))) l -> crs_regsat regs l -> crs_regsat regs2 l.
Proof.
intros regs regs2 l H Hl Hs. unfold crs_regsat in *. rewrite Forall_forall in *. intros p Hp.
rewrite (w1_aregs regs regs2 (fst p) H (Hl p Hp)). exact (Hs p Hp).
Qed.

(* the local's shadow and its hull lie in the frame's 16 shadow bytes (the frame is 32-aligned) *)
Lemma w1_slot_in_frame : forall F, F mod 32 = 0 ->
  (forall y, F + 32 <= y < F + 32 + 56 ->
     shadow_addr F <= shadow_of_addr SHADOW_OFF y < shadow_addr F + fs_frame_bytes CRS_CID / 8) /\
  (forall s, shadow_addr (F + 32) / 8 * 8 <= s < shadow_addr (F + 32 + 56 - 1) / 8 * 8 + 8 ->
     shadow_addr F <= s < shadow_addr F + fs_frame_bytes CRS_CID / 8).
Proof.
intros F HF. assert (E : fs_frame_bytes CRS_CID / 8 = 16) by reflexivity. rewrite E.
unfold shadow_addr, shadow_of_addr, SHADOW_OFF. split; intros; lia.
Qed.

Lemma w1_base_carry : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs mem md k sp2 STK1 FP1
  ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
  cbase R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  AJR R STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C)
    [(CRS_CID, c_fpos C)]
    ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  AJR R STK1 sp2 FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) ->
  ~ YI16.sink_open_fp FP1 ->
  aregs_preserved regs regs2 -> (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  cbase R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2.
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 STK1 FP1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB HJ2 HJc HFP Hsink HPR HMN.
destruct HB as (HP & Hfz & Hfk & HJ & HFR & HSV & HSL & HROD & HMN0 & Hgp & Htp & Hs1 & Hs2 & Hs3 & HDPk).
pose proof HP as ((HAF & _ & _ & _) & _).
pose proof HAF as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof (proj1 HJ) as HAR.
pose proof HJc as (HAR2 & Hle & _ & _ & _ & _ & _ & _ & HK1 & _ & HKimg & HKfr & _).
pose proof HJ2 as (HAR2' & _ & _ & _ & _ & Hfr2 & _).
destruct HFR as (Hfr & Hflag & Hpres).
destruct (crs_cF_keepR B ARx LAWS R CTX0 C ly S Hp W mem md k HP HJ) as [EF EFl].
destruct (crs_cF_keepR B ARx LAWS R CTX0 C ly2 S2 Hp2 W2 mem2 md2 (k + k1) HP HJ2) as [EF2 EFl2].
assert (Hin : In (CRS_CID, c_fpos C) (frames S)) by (rewrite Hfr; left; reflexivity).
assert (Hin2 : In (CRS_CID, c_fpos C) (frames S2)) by (rewrite Hfr2; left; reflexivity).
pose proof (alx_frames SEGS B ARx LAWS ly S Hp W mem md CRS_CID (c_fpos C) HAR Hin) as (HF32 & _ & _ & _).
rewrite EF in HF32.
assert (Hc144 : CRS_FRAME = 144) by (rewrite crs_frame_is_pi; reflexivity).
assert (Hfb : fs_frame_bytes CRS_CID = 128) by reflexivity.
(* a byte of the own frame or of its shadow is outside the callee's footprint *)
assert (HnFP : forall a, (cF C <= a < cF C + fs_frame_bytes CRS_CID \/
    shadow_addr (cF C) <= a < shadow_addr (cF C) + fs_frame_bytes CRS_CID / 8) -> ~ inFP FP1 a).
{ intros a Ha Hfp. destruct (HFP a Hfp) as (p & n & Hpn & Hpa). rewrite <- EF in Ha. destruct Ha as [Ha|Ha].
  - exact (w1_blk_frame ly S Hp W mem md p n CRS_CID (c_fpos C) a HAR Hpn Hin Hpa Ha).
  - exact (w1_blk_shadow ly S Hp W mem md p n CRS_CID (c_fpos C) a HAR Hpn Hin Hpa Ha). }
assert (Hkfr : forall a, (cF C <= a < cF C + fs_frame_bytes CRS_CID \/
    shadow_addr (cF C) <= a < shadow_addr (cF C) + fs_frame_bytes CRS_CID / 8) ->
    aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha. apply (HKfr CRS_CID (c_fpos C) a Hin); [| exact (HnFP a Ha)].
  unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. exact Ha. }
set (sp0 := spZ (c_regs C)) in *.
split; [exact HP|]. split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ2|].
split.
{ (* crs_frame *)
  split; [exact Hfr2|]. split.
  - rewrite (rdword_ext (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) mem2)).
    + rewrite Hflag. f_equal. rewrite EFl2. exact EFl.
    + intros k0 Hk0. apply Hkfr. left. rewrite Hfb in *. lia.
  - intros a Ha. rewrite <- EF2 in Ha.
    pose proof (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRS_CID (c_fpos C) HAR2' Hin2) as (_ & _ & Hp3 & _).
    exact (proj1 (Hp3 a Ha)). }
split.
{ (* crs_saved *)
  unfold crs_saved in *. rewrite Forall_forall in *. intros pr Hpr.
  assert (Hoff : 24 <= fst pr <= 120)
    by (unfold CRS_SAVED in Hpr; repeat (destruct Hpr as [<-|Hpr]; [cbn; lia|]); destruct Hpr).
  assert (HS0 : 27312 <= STK) by (vm_compute; discriminate).
  rewrite <- (HSV pr Hpr). apply rdword_ext. intros k0 Hk0. apply HK1; lia. }
split.
{ (* crs_slot *)
  destruct HSL as [HRA HHULL]. destruct (w1_slot_in_frame (cF C) HF32) as [Sy Sh].
  unfold cOut, CRS_OFF_DOC in *. split.
  - intros y Hy. destruct (HRA y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite Hkfr; [exact Hs | right; exact (Sy y Hy)].
  - intros s Hs. rewrite Hkfr; [exact (HHULL s Hs) | right; exact (Sh s Hs)]. }
split.
{ (* the read-only view *)
  intros a Hro Hown Herr. rewrite <- (HROD a Hro Hown Herr). apply HKimg.
  - destruct Hro as [(sg & Hsg & _ & Hr)|Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
    exact (@pa_relro_img _ _ PA a Hr).
  - exact Hown.
  - exact Herr.
  - intros Hpst. exact (pst_not_ro_A a Hpst Hro).
  - intros Ho. exfalso. exact (Hsink Ho). }
split; [exact (HMN HMN0)|].
split; [rewrite (w1_aregs regs regs2 3%bv HPR ltac:(cbv; lia)); exact Hgp|].
split; [rewrite (w1_aregs regs regs2 4%bv HPR ltac:(cbv; lia)); exact Htp|].
split; [exact Hs1|]. split; [exact Hs2 | split; [exact Hs3 | exact HDPk]].
Qed.

(* ======================================================================================================== *)
(* ---- THE INPUT AND THE TREE AT A BOUNDARY, from the entry's facts through crs_J (FP = []: every block of the
   entry that is still live, every frame of the entry and the read-only image keep their bytes) ---- *)
Lemma w1_garr8_move : forall (W W' : world SEGS) m m' p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall j, (j < length l)%nat -> aview SEGS (w_H W') m' (p + Z.of_nat j) = aview SEGS (w_H W) m (p + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W') m') p l.
Proof.
intros W W' m m' p l H E j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros kk Hkk. assert (kk = 0%nat) by lia. subst kk. rewrite <- (Hv 0%nat Hkk). cbn [Z.of_nat]. rewrite !Z.add_0_r.
apply mbyte_of_aview. exact (E j Hj).
Qed.

Lemma w1_not_sink_nil : ~ YI16.sink_open_fp [].
Proof. intros (r & Hr & _). destruct Hr. Qed.

(* a byte of the entry's read-only image (in_roP, not runtime-owned, not errno) keeps its view across crs_J *)
Lemma w1_ro_kept : forall (R : world SEGS -> world SEGS -> Prop) C ly3 S3 Hp3 W3 mem3 md3 k a,
  cJ R C ly3 S3 Hp3 W3 mem3 md3 k -> in_roP SEGS RLO RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W C)) (c_mem C) a.
Proof.
intros R C ly3 S3 Hp3 W3 mem3 md3 k a HJ Hro Hown Herr.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HKi & _). apply HKi.
- destruct Hro as [(sg & Hsg & _ & Hr)|Hr]; [exists sg; split; [exact Hsg | exact Hr]|].
  exact (@pa_relro_img _ _ PA a Hr).
- exact Hown.
- exact Herr.
- intros Hpst. exact (pst_not_ro_A a Hpst Hro).
- intros Ho. exfalso. exact (w1_not_sink_nil Ho).
Qed.

(* a byte of an entry block that is still live keeps its view across crs_J *)
Lemma w1_blk_kept : forall (R : world SEGS -> world SEGS -> Prop) C ly3 S3 Hp3 W3 mem3 md3 k p n a,
  cJ R C ly3 S3 Hp3 W3 mem3 md3 k -> In (p, n) (ablocks B (c_ly C) (c_S C)) -> In (p, n) (ablocks B ly3 S3) ->
  p <= a < p + req_size n -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W C)) (c_mem C) a.
Proof.
intros R C ly3 S3 Hp3 W3 mem3 md3 k p n a HJ H1 H2 Ha.
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HKb & _).
replace a with (p + (a - p)) by lia. apply (HKb p n (a - p) H1 H2); [lia | apply inFP_nil].
Qed.

Lemma w1_dat_tree : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3
  ran3,
  @CrsKeep rc cp SK B ARx -> cpre CTX0 C -> cJ R C ly3 S3 Hp3 W3 mem3 md3 k ->
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 ->
  Permutation Lam3 (c_Lam C) -> Permutation (ablocks B ly3 S3) (ablocks B (c_ly C) (c_S C)) ->
  cdat C ly3 S3 Hp3 W3 mem3 Lam3 /\ crs_tree C ly3 S3 Lam3 W3 mem3.
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 ran3 HK HP HJ HL HPL HPB.
destruct HP as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & Hdpos & _ & HSRC & HHOME & _ & Hdoc & HLED0 & _).
pose proof HFP as ((HAR0 & _) & _).
pose proof HJ as (HAR3 & Hle & _ & _ & _ & Hfr3 & _ & _ & _ & _ & _ & HKf & _).
pose proof HSRC as (Hby & H4096 & Hceil & _ & _ & _).
pose proof (@cf_head_nonneg cp) as Hc0.
assert (Hpers : forall x, In x (ablocks B (c_ly C) (c_S C)) -> In x (ablocks B ly3 S3))
  by (intros x Hx; exact (Permutation_in _ (Permutation_sym HPB) Hx)).
(* the Lam block of an entry Lam pair *)
assert (Hhb : forall b m, In (b, m) (c_Lam C) -> 0 <= m /\ In (b - cf_head, m + cf_head) (ablocks B (c_ly C) (c_S C))).
{ intros b m Hin. destruct HLED0 as (_ & _ & HF & _). rewrite Forall_forall in HF.
  destruct (HF (b, m) Hin) as (Hm & Hb & _). cbn [fst snd] in *. split; [exact Hm | exact Hb]. }
assert (Hlam_kept : forall b m a, In (b, m) (c_Lam C) -> b <= a < b + m ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W C)) (c_mem C) a).
{ intros b m a Hin Ha. destruct (Hhb b m Hin) as [Hm Hb].
  pose proof (req_size_pos (m + @cf_head cp) ltac:(lia)) as [_ Hrq].
  apply (w1_blk_kept R C ly3 S3 Hp3 W3 mem3 md3 k _ _ a HJ Hb (Hpers _ Hb)). lia. }
set (data := c_data C) in *. set (n := cSize C) in *.
assert (Hn0 : 0 <= n) by (unfold n, cSize; lia).
(* the input's bytes keep their views *)
assert (Hdat : forall a, data <= a < data + n ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W C)) (c_mem C) a).
{ intros a Ha. destruct HHOME as [[(b & m & Hin & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] |
    (b & m & Hin & _ & Hb1 & Hb2)].
  - apply (Hlam_kept b m a Hin). lia.
  - destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3). exact (w1_ro_kept R C ly3 S3 Hp3 W3 mem3 md3 k a HJ Hr1 Hr2 Hr3).
  - destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3 & _). exact (w1_ro_kept R C ly3 S3 Hp3 W3 mem3 md3 k a HJ Hr1 Hr2 Hr3).
  - assert (Hm0 : 0 <= m) by lia. pose proof (req_size_pos m Hm0) as [_ Hrq].
    apply (w1_blk_kept R C ly3 S3 Hp3 W3 mem3 md3 k b m a HJ Hin (Hpers _ Hin)). lia. }
assert (Hhome3 : PRH_FnReader.prhReader_home B ly3 S3 Hp3 Lam3 data n).
{ exact (kp_home_move B ARx HK (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_Lam C) (c_peak C) (c_cnt C) SIZE_MAXZ
    (c_ran C) (c_most C) 0 ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 data n HLED0 HL HPL HPB
    HHOME). }
split.
{ split.
  - unfold bytes_at in *. apply (w1_garr8_move (c_W C) W3 (c_mem C) mem3 data (c_tb C) Hby).
    intros j Hj. apply Hdat. unfold n, cSize. lia.
  - split; [exact Hhome3|].
    destruct (Z_lt_le_dec 0 n) as [Hpos|Hz].
    + assert (Hd0' : 0 <= data) by lia.
      assert (Hdn : data + n <= YM05.alloc_ceiling) by (unfold n, cSize in *; lia).
      destruct (kp_home_sh B ARx HK ly3 S3 Hp3 W3 mem3 md3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 data n HAR3 HL
        Hhome3
        Hpos Hd0' Hdn) as [HRA HHU].
      split; [exact HRA | intros _; exact HHU].
    + split; [intros x Hx; lia | intros Hp0; lia]. }
(* the tree *)
intros Hd. destruct Hdoc as [Hd0 | (_ & HT0 & _)]; [exfalso; exact (Hd Hd0)|].
destruct HT0 as (HN0 & HD0 & _ & HOH0).
assert (HDL : forall bk, In bk (c_D C) -> In bk Lam3) by (intros bk Hbk; exact (Permutation_in _ (Permutation_sym HPL) (HD0 bk Hbk))).
split; [|split; [exact HDL|]].
- (* the tree at Lam3 is the tree at c_Lam C: Lam3 holds every block c_Lam C holds (a permutation) *)
  apply (w1_nodeR_lblk SEGS (c_t C) _ (prh_lin (c_Lam C)) (prh_lin Lam3) (c_doc C) (c_D C)
    (fun b kk _ Hin => Permutation_in _ (Permutation_sym HPL) Hin)).
  apply (pj_nodeR_frame SEGS (c_t C) _ _ _ (c_doc C) (c_D C) HN0).
  intros x Hx. destruct Hx as [Hx | (bk & Hbk & Hx)].
  + destruct HOH0 as (_ & (cid & pos & Hcp & Hf1 & Hf2) & _).
    assert (Hcp3 : In (cid, pos) (frames S3)) by (rewrite Hfr3; apply in_or_app; right; exact Hcp).
    destruct (alx_layout SEGS B ARx LAWS (c_ly C) (c_S C) (c_Hp C) (c_W C) (c_mem C) (c_md C) ly3 HAR0 Hle)
      as (_ & Hfa & _).
    assert (Hkx : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x).
    { apply (HKf cid pos x Hcp); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | apply inFP_nil]. }
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Hkx)|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_frames SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 cid pos HAR3 Hcp3) as (_ & _ & Hpr & _).
    apply (proj1 (Hpr x ltac:(rewrite Hfa; lia))).
  + destruct bk as [b m]. unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
    destruct (Hhb b m (HD0 (b, m) Hbk)) as [Hm Hb].
    pose proof (req_size_pos (m + @cf_head cp) ltac:(lia)) as [_ Hrq].
    assert (Hkx : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (c_W C)) (c_mem C) x)
      by (apply (Hlam_kept b m x (HD0 (b, m) Hbk)); lia).
    split; [exact (mbyte_of_aview SEGS _ _ _ _ x Hkx)|].
    intros _. apply (apresent_writable SEGS).
    destruct (alx_blocks SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 _ _ HAR3 (Hpers _ Hb)) as (_ & _ & _ & _ & Hpr & _).
    apply (proj1 (Hpr x ltac:(lia))).
- split.
  + exact (kp_tree_vis B ARx HK ly3 S3 Hp3 W3 mem3 md3 Lam3 peak3 cnt3 SIZE_MAXZ ran3 (c_most C) 0 (c_D C) HAR3 HL
      HDL).
  + exact (crs_obj_keep_dpR B ARx LAWS R STK (spZ (c_regs C)) (c_ly C) (c_S C) (c_dp C) (c_Hp C) (c_W C) (c_mem C)
      (c_md C) [(CRS_CID, c_fpos C)] ly3 S3 Hp3 W3 mem3 md3 k (c_doc C) HAR0 HJ HOH0).
Qed.

(* ======================================================================================================== *)
(* ---- registers a stretch does not write keep their values (the symbolic state still holds their atoms) ---- *)
Lemma w1_regs_kept : forall (fxk : YK11.FPState) regs more ss (H : word -> bool) ms (l : list (bv 5 * Z)),
  st_ok (fx := fxk) SEGS (TE regs regs more) ss (restrict H ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (SOff (32 + Z.to_nat (bv_unsigned (fst p))) 0)) l = true ->
  crs_regsat regs l -> crs_regsat (ms_regs ms) l.
Proof.
intros fxk regs more ss H ms l HS Hb Hs. unfold crs_regsat in *. rewrite Forall_forall in *.
rewrite forallb_forall in Hb. intros p Hp.
rewrite (ts_reg_kept_c regs regs more ss H ms (fst p) (fst p) HS (sv_eqb_eq _ _ (Hb p Hp))). exact (Hs p Hp).
Qed.

Lemma w1_regsat_app : forall regs l1 l2, crs_regsat regs (l1 ++ l2) <-> crs_regsat regs l1 /\ crs_regsat regs l2.
Proof. intros regs l1 l2. unfold crs_regsat. rewrite Forall_app. tauto. Qed.

(* the registers of w1_st are callee-saved *)
Lemma w1_regs_saved : forall C sp2,
  Forall (fun p => acallee_saved (bv_unsigned (fst p))) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro).
Proof.
assert (Hb : forall r, ((r =? 2) || (r =? 3) || (r =? 4) || (r =? 8) || (r =? 9) || ((18 <=? r) && (r <=? 27)))%bool = true ->
  acallee_saved r).
{ intros r H. unfold acallee_saved.
  repeat (apply orb_true_iff in H as [H|H]); try (apply Z.eqb_eq in H; lia).
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1, H2. lia. }
intros C sp2. apply Forall_forall. intros p Hp. apply Hb. unfold crs_rbase, crs_rsh, crs_rargs, crs_rlive, crs_rro in Hp.
cbn [app] in Hp.
repeat (destruct Hp as [<-|Hp]; [vm_compute; reflexivity|]). destruct Hp.
Qed.

(* ---- AN ACCESSOR CALL (fuzz_alloc_ran_out, fuzz_alloc_count): nothing of the walk's state moves but the
   callee's frame and the statics it may rewrite with their own values ---- *)
Lemma w1_acc_carry : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak
  cnt ran evs STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1,
  @CrsKeep rc cp SK B ARx ->
  w1_stR R CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs ->
  AJR R STK (spZ (c_regs C)) [] (c_ly C) (YG00.set_depot (c_dp C) (c_S C)) (c_Hp C) (c_W C) (c_mem C) (c_md C)
    [(CRS_CID, c_fpos C)]
    ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  AJR R STK1 sp2 [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  aregs_preserved regs regs2 -> (YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS mem2) ->
  (room_live_cf S -> room_live_cf S2) -> S2 = S -> ablocks B ly2 S2 = ablocks B ly S ->
  LEDGER ly2 S2 Hp2 W2 mem2 Lam peak cnt SIZE_MAXZ ran (c_most C) 0 ->
  w1_stR R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak cnt ran evs.
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs STK1 ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HK
  (HB & HR & HL & _ & _) HJ2 HJc HPR HMN HRL ES EB HL2.
pose proof (w1_base_carry R CTX0 C fxk ly S Hp W regs mem md k sp2 STK1 [] ly2 S2 Hp2 W2 regs2 mem2 md2 k1 HB HJ2
  HJc (fun a Ha => False_ind _ (inFP_nil a Ha)) w1_not_sink_nil HPR HMN) as HB2.
destruct HL as ((_ & Hpk & Hrn & Hc1 & Hc2 & Hroom & Hpos) & (HPL & HPB)).
assert (HPB2 : Permutation (ablocks B ly2 S2) (ablocks B (c_ly C) (c_S C))) by (rewrite EB; exact HPB).
pose proof (w1_dat_tree R CTX0 C ly2 S2 Hp2 W2 mem2 md2 (k + k1) Lam peak cnt ran HK (proj1 HB2)
  (proj1 (proj2 (proj2 (proj2 HB2)))) HL2 HPL HPB2) as [HD2 HT2].
split; [exact HB2|]. split; [exact (w1_regsat_kept regs regs2 _ HPR (w1_regs_saved C sp2) HR)|].
split; [|split; [exact HD2 | exact HT2]].
split; [|split; [exact HPL | exact HPB2]].
split; [exact HL2|]. split; [exact Hpk|]. split; [exact Hrn|]. split; [exact Hc1|]. split; [exact Hc2|].
split; [exact (HRL Hroom)|]. subst S2. exact Hpos.
Qed.

(* ======================================================================================================== *)
(* ---- the segment's premises, bundled for the stretch lemmas (crs_seg_W1 states them one by one) ---- *)
Definition w1_ctx (CTX0 : list (list Z)) (C : crsC) : Prop :=
  @cf_head cp = PresetReqAt.HEAD /\
  (forall fx' : YK11.FPState, tfuzz_alloc_count_specX (fx := fx') (rc := rc) (cp := cp) (PI := prh_img_A) (RL := RL)
     (PA := PA) B ARx SK) /\
  (forall fx' : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fx') (rc := rc) (cp := cp) (PI := prh_img_A) (RL := RL)
     (PA := PA) B ARx SK) /\
  (forall fx' : YK11.FPState, tfuzz_free_specX (fx := fx') (rc := rc) (cp := cp) (PI := prh_img_A) (RL := RL)
     (PA := PA) B ARx SK) /\
  (forall fx' : YK11.FPState, crs_free0 (fx := fx') (rc := rc) (cp := cp) (RL := RL) (SK := SK) B ARx) /\
  @CrsKeep rc cp SK B ARx /\
  c_took C <= 2 ^ 28 /\
  (forall fx' : YK11.FPState, crs_wexact (fx := fx') (rc := rc) (ci := ci) (cp := cp) (RL := RL) (SK := SK) B ARx
     CTX0 C) /\
  crs_cnt24_W1 C /\
  cfromR CTX0 C /\ cfromH2 CTX0 C /\
  (PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\ PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp).

(* ---- after a stretch that writes no byte (no region has a write window) the memory is the stretch's start ---- *)
Lemma w1_mem_same : forall E rs (m m' : word -> option byte), (forall a, ~ in_wrange E rs a) -> frame_of E rs m m' ->
  m' = m.
Proof. intros E rs m m' Hn HF. apply functional_extensionality. intros x. apply HF. apply Hn. Qed.

Lemma w1_no_wr_nil : forall E a, ~ in_wrange E [] a.
Proof. intros E a (r & Hr & _). destruct Hr. Qed.

Lemma w1_no_wr_own : forall E a, ~ in_wrange E [w1_own_rg] a.
Proof. intros E a (r & Hr & Ha). destruct Hr as [<-|[]]. cbn in Ha. lia. Qed.

(* registers a stretch does not write, at a symbolic state of the runner *)
Lemma w1_regs_kept_pi : forall (fxk : YK11.FPState) regs more ss (H : word -> bool) ms (l : list (bv 5 * Z)),
  st_ok_pi (fx := fxk) SEGS VAL (TE regs regs more) ss (restrict H ms) ->
  forallb (fun p => sv_eqb (sr_get (ss_regs ss) (fst p)) (SOff (32 + Z.to_nat (bv_unsigned (fst p))) 0)) l = true ->
  crs_regsat regs l -> crs_regsat (ms_regs ms) l.
Proof.
intros fxk regs more ss H ms l HS Hb Hs. unfold crs_regsat in *. rewrite Forall_forall in *.
rewrite forallb_forall in Hb. intros p Hp.
rewrite (ts_reg_kept regs regs more ss H ms (fst p) (fst p) HS (sv_eqb_eq _ _ (Hb p Hp))). exact (Hs p Hp).
Qed.

(* crs_base over new registers (gp, tp kept) and the runner's model *)
Lemma w1_base_regs : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2,
  cbase R CTX0 C fxk ly S Hp W regs mem md k sp2 -> cJ R C ly S Hp W mem md' k ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  cbase R CTX0 C fxk ly S Hp W regs' mem md' k sp2.
Proof.
intros R CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2
  (HP & Hfz & Hfk & _ & HFR & HSV & HSL & HROD & HMN & Hgp & Htp & Hs) HJ E3 E4.
split; [exact HP|]. split; [exact Hfz|]. split; [exact Hfk|]. split; [exact HJ|]. split; [exact HFR|].
split; [exact HSV|]. split; [exact HSL|]. split; [exact HROD|]. split; [exact HMN|].
split; [rewrite E3; exact Hgp|]. split; [rewrite E4; exact Htp | exact Hs].
Qed.

Lemma w1_st_regs : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2 Lam
  peak cnt ran evs,
  w1_stR R CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt ran evs -> cJ R C ly S Hp W mem md' k ->
  getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  crs_regsat regs' (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) ->
  w1_stR R CTX0 C fxk ly S Hp W regs' mem md' k sp2 Lam peak cnt ran evs.
Proof.
intros R CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2 Lam peak cnt ran evs (HB & _ & HL & HD & HT) HJ E3 E4 HR.
split; [exact (w1_base_regs R CTX0 C fxk ly S Hp W regs regs' mem md md' k sp2 HB HJ E3 E4)|].
split; [exact HR|]. split; [exact HL|]. split; [exact HD | exact HT].
Qed.

Lemma w1_seat_nil : forall (fxk : YK11.FPState) (W : world SEGS) regs mem pc,
  st_ok_pi (fx := fxk) SEGS VAL (TE regs regs []) (mkSS pc cur_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxk W regs mem pc. apply ts_st_ok; [apply te_regs_ok | reflexivity | constructor | exact I |].
split; [exact I | split; exact I].
Qed.

(* ======================================================================================================== *)
(* ---- STRETCH P5 (A' 0x82354): `beq a0, s7` after the second count: a0 = crs_cnt1 C + k1, s7 = crs_cnt1 C, k1 >= 1,
   so the arm to R is refuted; fall through to H2 (0x82358) ---- *)
Lemma w1_at_P5 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  w1_stR WR CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak (crs_cnt1 C + k1) ran3 (crs_evs_at_H2 C) ->
  getr regs 10 = w64 (crs_cnt1 C + k1) -> getr regs 23 = w64 (crs_cnt1 C) ->
  crs_kfull C true k1 ran3 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + W1_P5) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1 Hctx Hdoc Hst R10 R23 Hkf.
pose proof Hctx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HH2 & _).
pose proof Hkf as [Hk1 _].
assert (HN1 : PjWriteHyp.wcalls (c_t C) true < 2 ^ 28).
{ pose proof (proj1 Hst) as (HP & _). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hd & _).
  destruct Hd as [Hd0 | (_ & _ & _ & Hw1 & _)]; [exfalso; exact (Hdoc Hd0)|].
  assert (Hw62 : PjWriteHyp.wlen (c_t C) true + 1 <= 2 ^ 62) by lia.
  pose proof (crs_wN_le (c_t C) true Hw62) as Hle. unfold PjWriteHyp.wcalls. lia. }
unfold crs_cfg. pose proof (w1_seat_nil fxk W regs mem W1_P5) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 (proj1 Hst))))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (RUNTO := @paj_run_to_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR (wle'_refl SEGS YGcfRehidePost.RZ_cf)
  (wle'_trans SEGS YGcfRehidePost.RZ_cf)).
pose (BR := paj_branchR (fx := fxk) (L := A_prog_listing) (PI := PA) WR).
psrr_branch_tokR RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- (* a0 = s7: refuted, the write made k1 >= 1 calls *)
  exfalso. rewrite branch_eq_U in Hc.
  change 42%nat with (32 + 10)%nat in Hc. change 55%nat with (32 + 23)%nat in Hc.
  rewrite !U_SOff, (te_cur regs regs [] 10%bv 10 eq_refl), (te_cur regs regs [] 23%bv 23 eq_refl), R10, R23 in Hc.
  rewrite !Z.add_0_r in Hc. unfold w64, zcanon, M64 in Hc. rewrite !Z_to_bv_unsigned in Hc.
  unfold bv_wrap in Hc. change (bv_modulus 64) with (2 ^ 64) in Hc. rewrite !Z.mod_mod in Hc by lia.
  apply Z.eqb_eq in Hc. lia.
- (* fall through to H2 *)
  paj_run_to_tok_x RUNTO HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) CRS_PC_H2.
  + intros a Ha. exfalso. exact (w1_no_wr_nil _ a Ha).
  + assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_nil _) HF).
    pmkst HS. rewrite Hm in HJ |- *.
    assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
    assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
    pose proof Hst as (_ & HR & _).
    assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
      by (apply (w1_regs_kept_pi fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
    assert (R23' : getr (ms_regs ms) 23 = w64 (crs_cnt1 C))
      by (rewrite (ts_reg_kept regs regs [] _ _ ms 23%bv 23%bv HS eq_refl); exact R23).
    pose proof (w1_st_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) mem md _ k sp2 Lam peak _ ran3 _ Hst HJ E3 E4
      HR2) as (HB2 & _ & HL2 & HD2 & HT2).
    match goal with |- context [{| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?p)) _ _; cfg_model := _ |}] =>
      replace p with CRS_PC_H2 by (vm_compute; reflexivity) end.
    apply (HH2 fxk ly S Hp W (ms_regs ms) mem _ k sp2 Lam peak ran3 k1 Hdoc HB2); [| exact HL2 | exact HD2 | exact HT2 | exact Hkf].
    replace (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro ++ [(23%bv, crs_cnt1 C)]) with
      ((crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) ++ [(23%bv, crs_cnt1 C)])
      by (rewrite <- !app_assoc; reflexivity).
    apply w1_regsat_app. split; [exact HR2 | constructor; [exact R23' | constructor]].
Qed.

(* ======================================================================================================== *)
(* ---- AN ACCESSOR TEXT (tfuzz_alloc_count_specX, tfuzz_alloc_ran_out_specX) in one generic shape: the value it
   returns is vf cnt ran ---- *)
Definition w1_acc_text (fxk : YK11.FPState) (sym : asym) (STKa : Z) (vf : Z -> Z -> Z) : Prop :=
  forall ly S Hp W regs mem md ch Lam peak cnt fail ran most own,
  fpre (fx := fxk) B ARx STKa ly S Hp W regs mem md ch -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own ->
  SRr SEGS W (cfg_at (fx := fxk) SEGS (SIGMA sym) regs mem md)
    (fpostm (fx := fxk) (PI := prh_img_A) (PA := PA) B ARx SK STKa [] regs ly S Hp W mem md
      (fun ly' S' Hp' W' regs' mem' md' =>
       (room_live_cf S -> room_live_cf S') /\ getr regs' 10 = w64 (vf cnt ran) /\ Hp' = Hp /\ S' = S /\
       ablocks B ly' S' = ablocks B ly S /\ LEDGER ly' S' Hp' W' mem' Lam peak cnt fail ran most own)).

(* the call of such a text at a world relation R (reflexive, transitive, containing wle): the plain text lifts to R
   (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift) *)
Lemma w1_acc_call : forall (R : world SEGS -> world SEGS -> Prop) (Rr : forall W, R W W)
  (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) (Rw : forall W W', @wle SEGS W W' -> R W W')
  CTX0 C fxk W E ss ms mdc ly S Hp k sp2 Lam peak cnt ran evs retk (sym : asym) STKa
  (vf : Z -> Z -> Z) (Q : world SEGS -> config -> Prop),
  @CrsKeep rc cp SK B ARx -> w1_acc_text fxk sym STKa vf -> 0 <= STKa -> STKa + 144 <= STK ->
  st_ok (fx := fxk) SEGS E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = SIGMA sym ->
  w1_stR R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 Lam peak cnt ran evs ->
  getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  4096 <= BASE + retk < 2 ^ 40 ->
  (forall W2 ly2 S2 Hp2 regs2 mem2 md2 k1,
   w1_stR R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k1) sp2 Lam peak cnt ran evs ->
   getr regs2 10 = w64 (vf cnt ran) -> aregs_preserved (ms_regs ms) regs2 ->
   SRrG SEGS R W2 (mkCfg (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + retk)) mem2 (YK11.seg_rom SEGS)) md2) Q) ->
  SRrG SEGS R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt Rw CTX0 C fxk W E ss ms mdc ly S Hp k sp2 Lam peak cnt ran evs retk sym STKa vf Q HK HTX HS0 HSb HS Hrv Hpc
  Hst R1 Hrk Hrk2 Hbr Hcont.
pose proof Hst as (HB & HR & HL & _ & _).
pose proof HL as ((HLED & _) & _).
rewrite !w1_regsat_app in HR. destruct HR as (HR1 & _).
unfold crs_regsat, crs_rbase in HR1. inversion HR1 as [|p1 l1 R2 HR1']; subst. inversion HR1' as [|p2 l2 R8 _]; subst.
cbn [fst snd] in R2, R8.
apply (w1_call R Rr Rt CTX0 C fxk W E ss ms mdc ly S Hp k sp2 STKa [] retk
  (fQmn (ms_mem ms) (fun ly' S' Hp' W' regs' mem' md' =>
     (room_live_cf S -> room_live_cf S') /\ getr regs' 10 = w64 (vf cnt ran) /\ Hp' = Hp /\ S' = S /\
     ablocks B ly' S' = ablocks B ly S /\ LEDGER ly' S' Hp' W' mem' Lam peak cnt SIZE_MAXZ ran (c_most C) 0)) Q HS Hrv
  HB R2 R8 R1
  Hrk Hrk2 Hbr HS0 HSb).
- intros a Ha. exfalso. exact (inFP_nil a Ha).
- intros HPRE. rewrite Hpc.
  refine (SRrG_mono SEGS R _ _ _ _ (SRr_SRrG SEGS R Rw _ _ _ (HTX ly S Hp W (ms_regs ms) (ms_mem ms) mdc (w1_ch C ly)
    Lam peak cnt SIZE_MAXZ ran (c_most C) 0 HPRE HLED)) _).
  intros W' c' _ HPm. exact (apost_base_x_R_lift (SK := SK) SEGS B PST ARx R Rw _ _ _ _ _ _ _ _ _ _ _ _ HPm).
- intros W2 ly2 S2 Hp2 regs2 mem2 md2 k1 Hwle HJ2 HJc HPR ((HRL & R10 & EHp & ES & EB & HL2) & HMN).
  apply (Hcont W2 ly2 S2 Hp2 regs2 mem2 md2 k1); [| exact R10 | exact HPR].
  exact (w1_acc_carry R CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) mdc k sp2 Lam peak cnt ran evs STKa ly2 S2 Hp2
    W2 regs2 mem2 md2 k1 HK Hst HJ2 HJc HPR HMN HRL ES EB HL2).
Qed.

(* ======================================================================================================== *)
(* ---- STRETCH P4 (A' 0x82350): `jal fuzz_alloc_count` after the free; a0 = crs_cnt1 C + k1 at P5 ---- *)
Lemma w1_at_P4 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  w1_stR WR CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak (crs_cnt1 C + k1) ran3 (crs_evs_at_H2 C) ->
  getr regs 23 = w64 (crs_cnt1 C) -> crs_kfull C true k1 ran3 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + W1_P4) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1 Hctx Hdoc Hst R23 Hkf.
pose proof Hctx as (_ & HTc & _ & _ & _ & HK & _).
unfold crs_cfg. pose proof (w1_seat_nil fxk W regs mem W1_P4) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 (proj1 Hst))))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- intros a Ha. exfalso. exact (w1_no_wr_nil _ a Ha).
- assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_nil _) HF).
  prreg HS (1%bv : bv 5) P1.
  assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept_c regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
  assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept_c regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
  pose proof Hst as (_ & HR & _).
  assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
    by (apply (w1_regs_kept fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
  assert (R23' : getr (ms_regs ms) 23 = w64 (crs_cnt1 C))
    by (rewrite (ts_reg_kept_c regs regs [] _ _ ms 23%bv 23%bv HS eq_refl); exact R23).
  rewrite <- Hm in HJ.
  pose proof (w1_st_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) (ms_mem ms) md _ k sp2 Lam peak _ ran3 _
    ltac:(rewrite Hm; exact Hst) HJ E3 E4 HR2) as Hst2.
  refine (w1_acc_call WR WRr WRt WRw CTX0 C fxk W (TE regs regs []) _ ms _ ly S Hp k sp2 Lam peak (crs_cnt1 C + k1) ran3
    (crs_evs_at_H2 C) W1_P5 AS_fuzz_alloc_count (@STK_fuzz_alloc_count prh_img_A) (fun c _ => c) (cpost C) HK
    _ _ _ HS eq_refl eq_refl Hst2 _ _ _ _ _).
  + intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0.
    exact (HTc fxk ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0).
  + vm_compute. discriminate.
  + vm_compute. discriminate.
  + rewrite P1. f_equal.
  + vm_compute. split; congruence.
  + reflexivity.
  + vm_compute. split; congruence.
  + intros W2 ly2 S2 Hp2 regs2 mem2 md2 k2 Hst3 R10 HPR.
    assert (R23b : getr regs2 23 = w64 (crs_cnt1 C))
      by (rewrite (w1_aregs _ _ 23%bv HPR ltac:(unfold acallee_saved; right; right; right; right; right; vm_compute;
            split; discriminate)); exact R23').
    exact (w1_at_P5 CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 Lam peak ran3 k1 Hctx Hdoc Hst3 R10 R23b Hkf).
Qed.

(* ======================================================================================================== *)
(* ---- a boundary state of W1 from its parts: the data and the tree come from the entry through crs_J ---- *)
Lemma w1_mk_st : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2 Lam2
  peak cnt ran3 evs,
  @CrsKeep rc cp SK B ARx -> cbase R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2 ->
  crs_regsat regs2 (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) ->
  LEDGER ly2 S2 Hp2 W2 mem2 Lam2 peak cnt SIZE_MAXZ ran3 (c_most C) 0 ->
  c_peak C <= peak -> ran3 = c_ran C -> c_cnt C <= cnt -> cnt < 2 ^ 62 -> room_live_cf S2 ->
  crs_pos C evs ran3 S2 ->
  Permutation Lam2 (c_Lam C) -> Permutation (ablocks B ly2 S2) (ablocks B (c_ly C) (c_S C)) ->
  w1_stR R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2 Lam2 peak cnt ran3 evs.
Proof.
intros R CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2 Lam2 peak cnt ran3 evs HK HB HR HL Hpk Hrn Hc1 Hc2 Hroom
  Hpos HPL HPB.
pose proof (w1_dat_tree R CTX0 C ly2 S2 Hp2 W2 mem2 md2 k2 Lam2 peak cnt ran3 HK (proj1 HB)
  (proj1 (proj2 (proj2 (proj2 HB)))) HL HPL HPB) as [HD HT].
split; [exact HB|]. split; [exact HR|]. split; [|split; [exact HD | exact HT]].
split; [|split; [exact HPL | exact HPB]].
split; [exact HL|]. split; [exact Hpk|]. split; [exact Hrn|]. split; [exact Hc1|]. split; [exact Hc2|].
split; [exact Hroom | exact Hpos].
Qed.

(* the block of a text the free removes is not among the entry's, so the free's footprint is a temporary block *)
Lemma w1_perm_drop : forall {X : Type} (x : X) (l0 l1 l2 E : list X),
  x :: l0 = l1 ++ x :: l2 -> Permutation l0 E -> Permutation (l1 ++ l2) E.
Proof.
intros X x l0 l1 l2 E Eq HP. apply (Permutation_trans (l' := l0)); [|exact HP].
apply Permutation_sym. apply Permutation_cons_app_inv with (a := x). rewrite <- Eq. reflexivity.
Qed.

Lemma w1_perm_drop2 : forall {X : Type} (x : X) (l1 l2 E bl : list X),
  bl = l1 ++ x :: l2 -> Permutation bl (x :: E) -> Permutation (l1 ++ l2) E.
Proof.
intros X x l1 l2 E bl Eq HP. subst bl. apply Permutation_sym.
apply Permutation_cons_app_inv with (a := x). apply Permutation_sym. exact HP.
Qed.

(* the text block at the free: NULL after a refusal (ran3 = 1; refuted in w1_at_P3 on the batch kit's cut: pj_write's post
   states prh_granted, so g_ran_out stays c_ran C = 0), else the pretty text (nothing refused: ran3 = 0), the head of
   Lam, not an entry block, with the model's last capacity *)
Definition w1_text (C : crsC) (ly : alayout) (S : astate) (Lam : list (Z * Z)) (q ran3 : Z) : Prop :=
  (q = 0 /\ ran3 = 1 /\ cperm C ly S Lam) \/
  (q <> 0 /\ ran3 = 0 /\ exists cap Lam0, Lam = (q, cap) :: Lam0 /\ Permutation Lam0 (c_Lam C) /\
     Permutation (ablocks B ly S) ((q - cf_head, cap + cf_head) :: ablocks B (c_ly C) (c_S C)) /\
     ~ In (q - cf_head, cap + cf_head) (ablocks B (c_ly C) (c_S C)) /\
     cap = last (PresetReqAt.wcaps (c_t C) true) 0).

Lemma w1_len_H2 : forall C, length (crs_evs_at_H2 C) = S (length (crs_evs_at_W1 C ++ crs_ev_w C true)).
Proof.
intros C. unfold crs_evs_at_H2, crs_ev_wf, PresetReqAt.w_free. rewrite app_assoc, length_app. cbn [length]. lia.
Qed.

(* the run has at most 4 calls (crs_pre, the text's premise for a callee's hull budget paid from the run's position) *)
Lemma w1_pre_los : forall CTX0 C, cpre CTX0 C -> (length (c_rp_os C) <= 4)%nat.
Proof.
intros CTX0 C HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & HL & _).
exact HL.
Qed.

(* ======================================================================================================== *)
(* ---- STRETCH P3 (A' 0x8234c): `jal fuzz_free` of the text q (a0); then P4. The free re-hides: the kit's text runs at
   wle' SEGS RZ_cf, and its hull budget comes from the run's position (PresetDrvHullA.drv_cf_hull_ok_at_call_A) ---- *)
Lemma w1_at_P3 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1 q,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  cbase WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat regs (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) ->
  getr regs 23 = w64 (crs_cnt1 C) -> getr regs 10 = w64 q ->
  LEDGER ly S Hp W mem Lam peak (crs_cnt1 C + k1) SIZE_MAXZ ran3 (c_most C) 0 ->
  c_peak C <= peak -> ran3 = c_ran C -> c_cnt C <= crs_cnt1 C + k1 -> crs_cnt1 C + k1 < 2 ^ 62 ->
  room_live_cf S ->
  (ran3 = 0 -> exists hist, PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
     (c_rp_i C + length (crs_evs_at_W1 C ++ crs_ev_w C true))%nat (c_rp_H0 C) hist S) ->
  w1_text C ly S Lam q ran3 -> crs_kfull C true k1 ran3 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + W1_P3) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak ran3 k1 q Hctx Hdoc HB HR R23 R10 HL Hpk Hrn Hc1 Hc2
  Hroom Hex Htx Hkf.
pose proof Hctx as (HIh & _ & _ & HTf & _ & HK & _ & _ & H24 & _ & _ & HIhull).
pose proof (proj1 HB) as HP.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRUN & Hran0 & _).
rewrite Hran0 in Hrn. subst ran3.
unfold crs_cfg. pose proof (w1_seat_nil fxk W regs mem W1_P3) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 HB)))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- intros a Ha. exfalso. exact (w1_no_wr_nil _ a Ha).
- assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_nil _) HF).
  prreg HS (1%bv : bv 5) P1.
  assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept_c regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
  assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept_c regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
  assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
    by (apply (w1_regs_kept fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
  assert (R23' : getr (ms_regs ms) 23 = w64 (crs_cnt1 C))
    by (rewrite (ts_reg_kept_c regs regs [] _ _ ms 23%bv 23%bv HS eq_refl); exact R23).
  assert (R10' : getr (ms_regs ms) 10 = w64 q)
    by (rewrite (ts_reg_kept_c regs regs [] _ _ ms 10%bv 10%bv HS eq_refl); exact R10).
  rewrite <- Hm in HJ.
  pose proof (w1_base_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) (ms_mem ms) md _ k sp2
    ltac:(rewrite Hm; exact HB) HJ E3 E4) as HB2.
  rewrite <- Hm in HL.
  pose proof HR2 as HR3. rewrite !w1_regsat_app in HR3. destruct HR3 as (HR1 & _).
  unfold crs_regsat, crs_rbase in HR1. inversion HR1 as [|p1 l1 R2 HR1']; subst.
  inversion HR1' as [|p2 l2 R8 _]; subst. cbn [fst snd] in R2, R8.
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + W1_P4)) by (rewrite P1; f_equal).
  pose proof (w1_free_trace CTX0 C ly (ms_regs ms) HP R1 R8) as Htr.
  destruct Htx as [(_ & Er & _) | (Hq & Er & cap & Lam0 & ELam & HPL0 & HPB0 & HnIn & Hcap)].
  + (* a refused write (q = 0, ran3 = 1): refuted, g_ran_out is c_ran C = 0 *)
    exfalso. lia.
  + (* the pretty text q <> 0 (nothing refused), freed at the exact position *)
    destruct (Hex eq_refl) as (hist0 & Hpos0).
    set (i0 := (c_rp_i C + length (crs_evs_at_W1 C ++ crs_ev_w C true))%nat) in Hpos0.
    pose proof (H24 i0 hist0 S Hpos0) as H24S.
    (* THE HULL BUDGET at the free: the run's position and its at most 4 calls bound both meters (A18's
       drv_cf_hull_ok_at_call_A), within the instance's caps (HI_hull) *)
    assert (HHULL : @PresetHullBudget.hull_budget cp S []).
    { destruct (PresetDrvHullA.drv_cf_hull_ok_at_call_A ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) i0 (c_rp_H0 C) hist0 S
        (w1_pre_los CTX0 C HP) Hpos0) as [HN HT].
      destruct HIhull as [HCN HCT]. rewrite PresetRoomPos.rp_nsec_layer in HN.
      unfold PresetHullBudget.hull_budget. cbv [PresetSecTotal.nsec PresetRun.nprodR]. cbn [PresetSecTotal.tsec].
      lia. }
    assert (Eq0 : (q =? 0) = false) by (apply Z.eqb_neq; exact Hq).
    assert (HinS : In (q - cf_head, cap + cf_head) (ablocks B ly S))
      by exact (Permutation_in _ (Permutation_sym HPB0) (in_eq _ _)).
    pose proof (proj1 HJ) as HARS.
    pose proof (alx_blocks SEGS B ARx LAWS ly S Hp W (ms_mem ms) _ _ _ HARS HinS) as (_ & Hq4096 & _).
    refine (w1_call WR WRr WRt CTX0 C fxk W (TE regs regs []) _ ms _ ly S Hp k sp2 (@STK_fuzz_free prh_img_A)
      (ablocks_fp [(q - cf_head, cap + cf_head)]) W1_P4 _ (cpost C) HS eq_refl HB2 R2 R8 R1 _ _ _ _ _ _ _ _).
    * vm_compute. split; congruence.
    * reflexivity.
    * vm_compute. split; congruence.
    * vm_compute. discriminate.
    * vm_compute. discriminate.
    * intros a (r & Hr & Ha). destruct Hr as [<-|[]]. cbn [fst snd] in Ha. right. left.
      exists (q - cf_head), (cap + cf_head). split; [exact HinS|]. split; [exact HnIn | lia].
    * intros HPRE.
      assert (Hin : q = 0 \/ In (q, cap) Lam) by (right; rewrite ELam; left; reflexivity).
      pose proof (HTf fxk (c_most C) 0 ly S Hp W (ms_regs ms) (ms_mem ms) _ (w1_ch C ly) q cap Lam peak
        (crs_cnt1 C + k1) SIZE_MAXZ 0 HPRE (fun _ => Hroom) (fun _ => H24S) (fun _ => HHULL)
        (admits_ct_fix _ _ _ _ _ _ Htr) R10' Hin HL) as Hfree.
      rewrite Eq0 in Hfree.
      (* the budgeted post at the free's own FIXED trace is the wle' form of the old post (PRH_Base.fpost_of_fpostb_fix) *)
      refine (SRrG_mono SEGS WR _ _ _ _ Hfree _).
      intros W' c' _ HPb. unfold fpostbm in HPb. eapply fpost_of_fpostb_fix in HPb; [|exact Htr]. exact HPb.
    * intros W2 ly2 S2 Hp2 regs2 mem2 md2 k2 _ HJ2 HJc HPR ((Hroom2' & _ & _ & Hpn & _ & _ & Harms) & HMN).
      pose proof (Hroom2' Hq) as Hroom2.
      destruct Harms as [(Hz & _) | (_ & _ & _ & (b1 & b2 & Eb1 & Eb2) & (l1 & l2 & El & HL2))];
        [exfalso; exact (Hq Hz)|].
      assert (HFPb : forall a, inFP (ablocks_fp [(q - cf_head, cap + cf_head)]) a ->
        exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n).
      { intros a (r & Hr & Ha). destruct Hr as [<-|[]]. cbn [fst snd] in Ha.
        exists (q - cf_head), (cap + cf_head). split; [exact HinS | lia]. }
      assert (Hsink : ~ YI16.sink_open_fp (ablocks_fp [(q - cf_head, cap + cf_head)]))
        by (apply sink_closed_ablocks_fp; constructor; [cbn; lia | constructor]).
      pose proof (w1_base_carry WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ k sp2 (@STK_fuzz_free prh_img_A)
        _ ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HB2 HJ2 HJc HFPb Hsink HPR HMN) as HB3.
      pose proof (w1_regsat_kept _ _ _ HPR (w1_regs_saved C sp2) HR2) as HR4.
      assert (R23b : getr regs2 23 = w64 (crs_cnt1 C))
        by (rewrite (w1_aregs _ _ 23%bv HPR ltac:(unfold acallee_saved; right; right; right; right; right; vm_compute;
              split; discriminate)); exact R23').
      assert (HPL2 : Permutation (l1 ++ l2) (c_Lam C))
        by (apply (w1_perm_drop (q, cap) Lam0 l1 l2 (c_Lam C)); [rewrite <- ELam; exact El | exact HPL0]).
      assert (HPB2 : Permutation (ablocks B ly2 S2) (ablocks B (c_ly C) (c_S C)))
        by (rewrite Eb2; exact (w1_perm_drop2 _ b1 b2 _ _ Eb1 HPB0)).
      assert (Hpos2 : crs_pos C (crs_evs_at_H2 C) 0 S2).
      { intros _.
        pose proof (proj1 (crs_room_evs_of_run C Hdoc HRUN)) as Hev.
        rewrite <- Hcap, <- HIh in Hev.
        destruct (Hpn Hq ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) i0 (c_rp_H0 C) hist0 Hpos0
          (proj2 (prh_run_at_one _ _ _ _ _) Hev)) as (hist' & Hh).
        exists hist'. rewrite w1_len_H2. cbn [length] in Hh.
        replace (c_rp_i C + Datatypes.S (length (crs_evs_at_W1 C ++ crs_ev_w C true)))%nat
          with (i0 + 1)%nat by (unfold i0; lia).
        exact Hh. }
      pose proof (w1_mk_st WR CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 (l1 ++ l2) peak (crs_cnt1 C + k1)
        0 (crs_evs_at_H2 C) HK HB3 HR4 HL2 Hpk ltac:(rewrite Hran0; lia) Hc1 Hc2 Hroom2 Hpos2 HPL2 HPB2) as Hst3.
      exact (w1_at_P4 CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 (l1 ++ l2) peak 0 k1 Hctx Hdoc Hst3
        R23b Hkf).
Qed.

(* a register of a crs_regsat list *)
Lemma w1_regsat_in : forall regs l p, crs_regsat regs l -> In p l -> getr regs (fst p) = w64 (snd p).
Proof. intros regs l p H Hin. unfold crs_regsat in H. rewrite Forall_forall in H. exact (H p Hin). Qed.
Ltac w1_in_tac := cbn [crs_rbase crs_rsh crs_rargs crs_rlive crs_rro app]; repeat (first [left; reflexivity | right]).

(* ======================================================================================================== *)
(* ---- the pretty write's premises from crs_pre and the boundary (pure parts) ---- *)
Lemma w1_dbl_ge : forall f c need, 0 <= c -> c <= WriterSpec.dbl f c need.
Proof.
induction f as [|f IH]; intros c need Hc; cbn [WriterSpec.dbl]; [lia|].
destruct (need <=? c); [lia|]. specialize (IH (2 * c) need ltac:(lia)). lia.
Qed.

Lemma w1_live_w_nonneg : forall t p, 0 <= PRH_FnWriter.LIVE_pj_write t p.
Proof.
intros t p. unfold PRH_FnWriter.LIVE_pj_write, WriterSpec.newcap. rewrite Z.eqb_refl.
pose proof (w1_dbl_ge 64 4096 (Z.of_nat (length (WriterValue.wdoc t p)) + 1) ltac:(lia)).
pose proof (@cf_head_nonneg cp). lia.
Qed.

Lemma w1_hpeak_nonneg : forall tr, 0 <= hpeakR tr.
Proof. intros [|e r]; cbn [hpeakR]; lia. Qed.

Lemma w1_live_crcs : forall tb t,
  PRH_FnWriter.LIVE_pj_write t true <= LIVE_check_reject_clean_starved tb t.
Proof.
intros tb t. unfold LIVE_check_reject_clean_starved, PRH_FnPj.LIVE_pj_parse.
pose proof (w1_live_w_nonneg t false). pose proof (w1_hpeak_nonneg (PRH_FnPj.prhPj_ptrace tb)).
pose proof (@cf_head_nonneg cp). pose proof (Zle_0_nat (PjGrammar.calls (PRH_FnPj.prhPj_ptrace tb))). nia.
Qed.

Lemma w1_wmax_rq : forall tb, PRH_FnWriter.prhWriter_WMAX <= RQ_crcs tb.
Proof. intros tb. unfold RQ_crcs, zmaxl. cbn [fold_right]. lia. Qed.

(* ======================================================================================================== *)
(* ---- STRETCH P2 (A' 0x8233c): `mv s7, a0`, `addi a1, zero, 1`, `mv a0, s3`, `jal pj_write` (doc, 1), the whole
   pretty write (crs_wexact's W1 call); then P3 ---- *)
Lemma w1_at_P2 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  w1_stR WR CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak (crs_cnt1 C) 0 (crs_evs_at_W1 C) ->
  getr regs 10 = w64 (crs_cnt1 C) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + W1_P2) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak Hctx Hdoc Hst R10.
pose proof Hctx as (HIh & _ & _ & _ & _ & HK & HBt & HWx & _).
pose proof Hst as (HB & HR & ((HLED & Hpk & Hrn & Hc1 & Hc2 & Hroom & Hpos) & (HPL & HPB)) & _ & HT).
pose proof (proj1 HB) as HP.
pose proof HP as (_ & _ & Huniv & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htook & Hd & _ & Hcnt0 & HRUN & _ & _ & _ &
  Hlive & Hrq & Hfr0 & _).
destruct Hd as [Hd0 | (_ & _ & Hw0 & Hw1 & Hdep)]; [exfalso; exact (Hdoc Hd0)|].
pose proof (HT Hdoc) as (Hnode & HDL & Hvis & (_ & Hinf & Hra)).
pose proof HB as (_ & _ & _ & _ & (Hfr & _) & _).
destruct (Hpos eq_refl) as (hist & Hpos0).
(* the counts *)
assert (Hfirst : 0 <= crs_first C <= c_took C).
{ unfold crs_first. destruct (Z.eqb_spec (c_took C) 0) as [E|E]; [lia|].
  pose proof (crs_pick_lt (c_tb C) (c_took C) ltac:(lia)). lia. }
assert (HN1 : (Z.of_nat (length (WriterSpec.grow_calls 0 0 (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) true))))
  <= PjWriteHyp.wlen (c_t C) true + 1)).
{ apply crs_wN_le. lia. }
unfold crs_cfg. pose proof (w1_seat_nil fxk W regs mem W1_P2) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 HB)))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- intros a Ha. exfalso. exact (w1_no_wr_nil _ a Ha).
- assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_nil _) HF).
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
  prreg HS (23%bv : bv 5) P23.
  change 51%nat with (32 + 19)%nat in P10. rewrite (te_cur regs regs [] 19%bv 19 eq_refl) in P10.
  change 42%nat with (32 + 10)%nat in P23. rewrite (te_cur regs regs [] 10%bv 10 eq_refl), R10 in P23.
  pose proof (w1_regsat_in regs _ (19%bv, c_doc C) HR ltac:(w1_in_tac)) as R19. cbn [fst snd] in R19.
  rewrite R19 in P10.
  assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept_c regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
  assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept_c regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
  assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
    by (apply (w1_regs_kept fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
  rewrite <- Hm in HJ.
  pose proof (w1_base_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) (ms_mem ms) md _ k sp2
    ltac:(rewrite Hm; exact HB) HJ E3 E4) as HB2.
  rewrite <- Hm in HLED.
  pose proof HR2 as HR3. rewrite !w1_regsat_app in HR3. destruct HR3 as (HR1 & _).
  unfold crs_regsat, crs_rbase in HR1. inversion HR1 as [|p1 l1 R2 HR1']; subst.
  inversion HR1' as [|p2 l2 R8 _]; subst. cbn [fst snd] in R2, R8.
  assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + W1_P3)) by (rewrite P1; f_equal).
  pose proof (crs_cap_callee (c_S C) S (c_fpos C) Hfr Hfr0) as (_ & _ & Hfrw).
  assert (Hbb : blocks_bytes S = blocks_bytes (c_S C)).
  { rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B (c_ly C) (c_S C)). apply bsum_perm. exact HPB. }
  pose proof (w1_live_crcs (c_tb C) (c_t C)) as Hlw.
  pose proof (w1_wmax_rq (c_tb C)) as Hwm.
  (* the call's events: the whole pretty write's (PRH_Supply), after the starved reading's (crs_run_split) *)
  assert (Ew : PRH_FnWriter.prhWriter_pjw_evs [] (crs_cnt1 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) true) =
    crs_ev_w C true).
  { pose proof HLED as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _) & _).
    unfold crs_ev_w. apply (prhWriter_pjw_evs_w_evs (c_t C) true (crs_cnt1 C) SIZE_MAXZ HIh Hc64).
    intros j Hj. unfold PresetReqAt.wcalls, PresetReqAt.wcaps in Hj. unfold SIZE_MAXZ, crs_cnt1 in *.
    rewrite Z.mod_small by lia. lia. }
  assert (E1 : crs_evs C = crs_evs_at_W1 C ++ (crs_ev_w C true ++ (crs_ev_wf C true ++ crs_ev_ws C true ++
    crs_ev_w C false ++ crs_ev_wf C false ++ crs_ev_ws C false))).
  { rewrite (crs_evs_doc C Hdoc). unfold crs_evs_at_X3, crs_evs_at_H3, crs_evs_at_Z, crs_evs_at_X2, crs_evs_at_H2.
    repeat rewrite <- app_assoc. reflexivity. }
  assert (Hrun1 : prh_run_at ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C) (c_rp_i C + length (crs_evs_at_W1 C))%nat
    (PRH_FnWriter.prhWriter_pjw_evs [] (crs_cnt1 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) true))).
  { rewrite Ew. destruct (crs_run_split C _ _ E1 HRUN) as [_ H2].
    exact (proj1 (proj1 (prh_run_at_app_iff _ _ _ _ _ _) H2)). }
  (* the call's consumer window, inside the text's (crs_cons_sub) *)
  assert (Hcons : PRH_Base.prh_cons_from ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
    (c_rp_i C + length (crs_evs_at_W1 C))%nat
    (length (PRH_FnWriter.prhWriter_pjw_evs [] (crs_cnt1 C) SIZE_MAXZ (WriterValue.wdpieces (c_t C) true)))).
  { refine (crs_cons_sub B ARx CTX0 C _ _ _ HP).
    rewrite Ew, E1, !length_app. lia. }
  refine (w1_callF WR WRr WRt CTX0 C fxk W (TE regs regs []) _ ms _ ly S Hp k sp2 (@STK_pj_write prh_img_A DOC_D) [] W1_P3
    _ (cpost C) HS eq_refl HB2 R2 R8 R1 _ _ _ _ _ _ _ _).
  + vm_compute. split; congruence.
  + reflexivity.
  + vm_compute. split; congruence.
  + vm_compute. discriminate.
  + vm_compute. discriminate.
  + intros a Ha. exfalso. exact (inFP_nil a Ha).
  + intros HPRE.
    (* crs_wexact's text concludes at the re-hiding relation (SRr' SEGS RZ_cf) with the kit's fpostFm *)
    apply (proj1 (HWx fxk) hist ly S Hp W (ms_regs ms) (ms_mem ms) _ (w1_ch C ly) Lam peak (crs_cnt1 C) SIZE_MAXZ 0).
    * reflexivity.
    * reflexivity.
    * exact Hc2.
    * exact HPRE.
    * exact Huniv.
    * exact Hroom.
    * exact Hpos0.
    * exact Hcons.
    * exact P10.
    * exact P11.
    * lia.
    * exact HLED.
    * exact Hrun1.
    * exact Hnode.
    * right. right. exact Hinf.
    * exact Hra.
    * exact Hvis.
    * intros a k0 Hin. exact (HDL (a, k0) Hin).
    * assert (EDD : DOC_D = 33%nat) by reflexivity. rewrite EDD. lia.
    * lia.
    * exact Hfrw.
    * cbn [negb Z.eqb]. unfold PjWriteHyp.wlen in Hw1. unfold PRH_FnWriter.prhWriter_WMAX. lia.
    * lia.
    * cbn [negb Z.eqb]. rewrite Hbb. lia.
  + intros fx' W2 ly2 S2 Hp2 regs2 mem2 md2 k2 _ HFZ HFK HJ2 HJc HPR ((ok & ran' & q & Lam' & peak' & HQw) & HMN).
    cbv zeta in HQw. cbn [negb Z.eqb] in HQw.
    destruct HQw as (Hoks & R10q & Hroom2 & Hgr & _ & _ & _ & HL2 & Harms & Hex).
    assert (Hcb : 0 <= crs_cnt1 C /\ crs_cnt1 C + Z.of_nat (length (WriterSpec.grow_calls 0 0
      (WriterSpec.piece_lens (WriterValue.wdpieces (c_t C) true)))) + 1 < 2 ^ 62).
    { pose proof HLED as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _) & _). unfold crs_cnt1 in *. lia. }
    pose proof (crs_wfull (WriterValue.wdpieces (c_t C) true) (crs_cnt1 C) ok (crs_wdpieces_ne (c_t C) true)
      ltac:(lia) ltac:(lia)) as Hwf.
    cbv zeta in Hwf. destruct Hwf as (Hk & Ecnt & Efail & Hfk & Hall & _).
    rewrite Ecnt, Efail in HL2.
    (* the post's prh_granted: g_ran_out is kept (ran' = ran = 0), and since g_fail_at = SIZE_MAX lies past every
       call, no call failed *)
    pose proof (crs_ran_of_granted _ _ _ _ _ _ _ _ Hoks Hgr) as Hran'.
    assert (Hnf : forall i, (i < PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (crs_cnt1 C) SIZE_MAXZ)
        (WriterValue.wdpieces (c_t C) true))%nat -> crs_cnt1 C + Z.of_nat i <> SIZE_MAXZ)
      by (intros i Hi; unfold SIZE_MAXZ, crs_cnt1 in *; lia).
    assert (Hok : WriterApp.w_failed (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (crs_cnt1 C) SIZE_MAXZ)
        (WriterValue.wdpieces (c_t C) true)) = 0).
    { apply Hall. intros i Hi. destruct (nth i ok true) eqn:En; [reflexivity|].
      exfalso. exact (Hnf i Hi (Hgr i Hi En)). }
    assert (Hkf : crs_kfull C true (Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (crs_cnt1 C) SIZE_MAXZ)
        (WriterValue.wdpieces (c_t C) true))) ran').
    { unfold crs_kfull, PjWriteHyp.wcalls. split; [lia|]. intros _. rewrite (Hfk Hok). reflexivity. }
    pose proof (w1_base_fx WR CTX0 C fxk fx' ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2
      (w1_base_carry WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) _ k sp2
        (@STK_pj_write prh_img_A DOC_D) [] ly2 S2 Hp2 W2 regs2 mem2 md2 k2 HB2 HJ2 HJc
        (fun a Ha => False_ind _ (inFP_nil a Ha)) w1_not_sink_nil HPR HMN) HFZ HFK) as HB3.
    pose proof (w1_regsat_kept _ _ _ HPR (w1_regs_saved C sp2) HR2) as HR4.
    assert (R23b : getr regs2 23 = w64 (crs_cnt1 C))
      by (rewrite (w1_aregs _ _ 23%bv HPR ltac:(unfold acallee_saved; right; right; right; right; right; vm_compute;
            split; discriminate)); exact P23).
    assert (Htx : w1_text C ly2 S2 Lam' q ran' /\ c_peak C <= peak').
    { destruct Harms as [(Hf0 & Hq & HnIn & ELam & Epk & HPB' & _ & _) | (Hf1 & _)]; [|exfalso; exact (Hf1 Hok)].
      split; [|rewrite Epk; lia].
      right. split; [exact Hq|]. split; [exact Hran'|].
      exists (WriterApp.w_cap (PRH_FnWriter.prhWriter_putN ok (WriterApp.w0 (crs_cnt1 C) SIZE_MAXZ)
        (WriterValue.wdpieces (c_t C) true))), Lam.
      split; [exact ELam|]. split; [exact HPL|].
      split; [exact (Permutation_trans HPB' (perm_skip _ HPB))|].
      split; [intros Hin; apply HnIn; exact (Permutation_in _ (Permutation_sym HPB) Hin)|].
      apply (w1_wcap_full (c_t C) true ok (crs_cnt1 C)).
      + lia.
      + unfold PresetReqAt.wcalls, PresetReqAt.wcaps. lia.
      + exact Hf0. }
    destruct Htx as [Htx Hpk2].
    assert (Hex' : ran' = 0 -> exists hist', PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (c_rp_x C) (c_rp_os C)
      (c_rp_i C + length (crs_evs_at_W1 C ++ crs_ev_w C true))%nat (c_rp_H0 C) hist' S2).
    { intros E0. destruct (Hex E0) as (h & Hh). exists h. rewrite length_app, Nat.add_assoc. exact Hh. }
    exact (w1_at_P3 CTX0 C fx' ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 Lam' peak' ran'
      (Z.of_nat (PRH_FnWriter.prhWriter_k ok (WriterApp.w0 (crs_cnt1 C) SIZE_MAXZ) (WriterValue.wdpieces (c_t C) true))) q
      Hctx Hdoc HB3 HR4 R23b R10q HL2 Hpk2 ltac:(rewrite Hran'; exact Hrn) ltac:(unfold crs_cnt1 in *; lia)
      ltac:(unfold crs_cnt1 in *; lia)
      Hroom2 Hex' Htx Hkf).
Qed.

(* `bnez a0` at a boundary seat: the condition is a0's value <> 0 *)
Lemma w1_bne_a0 : forall regs x, getr regs 10 = w64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot (TE regs regs []) (SOff 42 0)) (sv_denot (TE regs regs []) (SLit 0)) = negb (x =? 0).
Proof.
intros regs x R Hx. rewrite branch_ne_U, U_SLit, U_SOff. change 42%nat with (32 + 10)%nat.
rewrite (te_cur regs regs [] 10%bv 10 eq_refl), R. unfold w64, zcanon, M64. rewrite Z_to_bv_unsigned.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.add_0_r, Z.mod_mod by lia. rewrite Z.mod_small by lia. rewrite Zmod_0_l. reflexivity.
Qed.

(* ======================================================================================================== *)
(* ---- the count after the starved reading when nothing was refused ---- *)
Lemma w1_cnt_R_0 : forall C cnt1, crs_cnt_R C cnt1 0 -> cnt1 = crs_cnt1 C.
Proof.
intros C cnt1 [H0 H1]. unfold crs_cnt1, crs_first.
destruct (Z.eqb_spec (c_took C) 0) as [E|E]; [rewrite (H0 E); lia|].
destruct (H1 E) as [_ H2]. rewrite (H2 eq_refl). lia.
Qed.

(* ======================================================================================================== *)
(* ---- STRETCH P1 (A' 0x82334): `bnez a0` on fuzz_alloc_ran_out's value ran1. The RAN arm is refuted: ran1 =
   c_ran C = 0 (crs_core, crs_pre). Then `jal fuzz_alloc_count` -> P2 with a0 = crs_cnt1 C ---- *)
Lemma w1_at_P1 : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt1 ran1,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  w1_stR WR CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt1 ran1 (crs_evs_at_W1 C) ->
  getr regs 10 = w64 ran1 -> crs_cnt_R C cnt1 ran1 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + W1_P1) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt1 ran1 Hctx Hdoc Hst R10 HcR.
pose proof Hctx as (_ & HTc & _ & _ & _ & HK & _).
pose proof Hst as (HB & HR & ((_ & _ & Hrn & _) & _) & _).
pose proof (proj1 HB) as HP.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hran0 & _).
assert (E0 : ran1 = 0) by lia.
rewrite E0 in R10, HcR, Hst.
rewrite (w1_cnt_R_0 C cnt1 HcR) in Hst.
unfold crs_cfg. pose proof (w1_seat_nil fxk W regs mem W1_P1) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 HB)))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR WRr WRt).
pose (BR := paj_branchR (fx := fxk) (L := A_prog_listing) (PI := PA) WR).
psrr_branch_tokR RUN BR HS SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1);
  rewrite (w1_bne_a0 regs 0 R10 ltac:(lia)) in Hc.
- (* the RAN arm: refuted, a0 = ran1 = 0 *)
  exfalso. cbn in Hc. discriminate Hc.
- (* `jal fuzz_alloc_count` *)
  paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
  + intros a Ha. exfalso. exact (w1_no_wr_nil _ a Ha).
  + assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_nil _) HF).
    prreg HS (1%bv : bv 5) P1.
    assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept_c regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
    assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept_c regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
    assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro))
      by (apply (w1_regs_kept fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
    rewrite <- Hm in HJ.
    pose proof (w1_st_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) (ms_mem ms) md _ k sp2 Lam peak _ 0 _
      ltac:(rewrite Hm; exact Hst) HJ E3 E4 HR2) as Hst2.
    refine (w1_acc_call WR WRr WRt WRw CTX0 C fxk W (TE regs regs []) _ ms _ ly S Hp k sp2 Lam peak (crs_cnt1 C) 0
      (crs_evs_at_W1 C) W1_P2 AS_fuzz_alloc_count (@STK_fuzz_alloc_count prh_img_A) (fun c _ => c) (cpost C) HK
      _ _ _ HS eq_refl eq_refl Hst2 _ _ _ _ _).
    * intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0.
      exact (HTc fxk ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0).
    * vm_compute. discriminate.
    * vm_compute. discriminate.
    * rewrite P1. f_equal.
    * vm_compute. split; congruence.
    * reflexivity.
    * vm_compute. split; congruence.
    * intros W2 ly2 S2 Hp2 regs2 mem2 md2 k2 Hst3 R10' _.
      exact (w1_at_P2 CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 Lam peak Hctx Hdoc Hst3 R10').
Qed.

(* s8 after W1's auipc: the hi atom 18, g_own_ran_out - 540 *)
Lemma w1_hi18 : forall regs0 regsc more, ew (TE regs0 regsc more) (A_HI 18) = Z_to_bv 64 CRS_RO.
Proof.
intros regs0 regsc more. unfold TE. rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
rewrite (proj1 crs_ro_atoms). reflexivity.
Qed.

(* ======================================================================================================== *)
(* ---- STRETCH A (A' 0x82324): `auipc s8`, `lbu a0, 0(s8)` of g_own_ran_out (0: the boundary ledger's own cell,
   prh_ledger_own, so the OWN arm's `bnez a0` falls through in the symbolic run), `jal fuzz_alloc_ran_out`; then P1 *)
Lemma w1_at_A : forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt1 ran1,
  w1_ctx CTX0 C -> c_doc C <> 0 ->
  cbase WR CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat regs (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C) ->
  clive C ly S Hp W mem Lam peak cnt1 ran1 (crs_evs_at_W1 C) ->
  cdat C ly S Hp W mem Lam -> crs_tree C ly S Lam W mem ->
  crs_cnt_R C cnt1 ran1 ->
  SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg fxk (BASE + CRS_PC_W1) regs mem md) (cpost C).
Proof.
intros CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt1 ran1 Hctx Hdoc HB HR HL HD HT HcR.
pose proof Hctx as (_ & _ & HTr & _ & _ & HK & _).
assert (Hown : prh_own W mem 0) by (destruct HL as ((HLED & _) & _); eapply prh_ledger_own; exact HLED).
unfold crs_cfg. pose proof (w1a_seat fxk W regs mem Hown) as HS.
pose proof (proj1 (proj2 (proj2 (proj2 HB)))) as HJ.
assert (SHOK : sh_ok SEGS (SLit 0) [] (TE regs regs []) (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
assert (HEI : img_env VAL A_LIM (TE regs regs [])) by apply te_env.
pose (RUN := @paj_run_xR fxk rc SK _ PL PA B PST ARx _ LAWS WR WRr WRt).
paj_run_tok_x RUN HS HJ SHOK (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
- intros a Ha. exfalso. exact (w1_no_wr_own _ a Ha).
- assert (Hm : ms_mem ms = mem) by exact (w1_mem_same _ _ _ _ (w1_no_wr_own _) HF).
  prreg HS (1%bv : bv 5) P1. prreg HS (24%bv : bv 5) P24.
  change 298%nat with (A_HI 18) in P24. rewrite w1_hi18 in P24.
  assert (E3 : getr (ms_regs ms) 3 = getr regs 3) by exact (ts_reg_kept_c regs regs [] _ _ ms 3%bv 3%bv HS eq_refl).
  assert (E4 : getr (ms_regs ms) 4 = getr regs 4) by exact (ts_reg_kept_c regs regs [] _ _ ms 4%bv 4%bv HS eq_refl).
  assert (HR2 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C))
    by (apply (w1_regs_kept fxk regs [] _ _ ms _ HS); [vm_compute; reflexivity | exact HR]).
  assert (HR3 : crs_regsat (ms_regs ms) (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro)).
  { replace (crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C ++ crs_rro) with
      ((crs_rbase C sp2 ++ crs_rsh C ++ crs_rargs C ++ crs_rlive C) ++ crs_rro) by (rewrite <- !app_assoc; reflexivity).
    apply w1_regsat_app. split; [exact HR2 | constructor; [exact P24 | constructor]]. }
  rewrite <- Hm in HJ.
  pose proof (w1_base_regs WR CTX0 C fxk ly S Hp W regs (ms_regs ms) (ms_mem ms) md _ k sp2
    ltac:(rewrite Hm; exact HB) HJ E3 E4) as HB2.
  assert (Hst1 : w1_stR WR CTX0 C fxk ly S Hp W (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) k sp2
    Lam peak cnt1 ran1 (crs_evs_at_W1 C)).
  { split; [exact HB2|]. split; [exact HR3|]. rewrite Hm. split; [exact HL|]. split; [exact HD | exact HT]. }
  refine (w1_acc_call WR WRr WRt WRw CTX0 C fxk W (TE regs regs []) _ ms _ ly S Hp k sp2 Lam peak cnt1 ran1
    (crs_evs_at_W1 C) W1_P1 AS_fuzz_alloc_ran_out (@STK_fuzz_alloc_ran_out prh_img_A) (fun _ r => r) (cpost C) HK
    _ _ _ HS eq_refl eq_refl Hst1 _ _ _ _ _).
  + intros ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0.
    exact (HTr fxk ly0 S0 Hp0 W0 regs0 mem0 md0 ch0 Lam0 peak0 cnt0 fail0 ran0 most0 own0 HP0 HL0).
  + vm_compute. discriminate.
  + vm_compute. discriminate.
  + rewrite P1. f_equal.
  + vm_compute. split; congruence.
  + reflexivity.
  + vm_compute. split; congruence.
  + intros W2 ly2 S2 Hp2 regs2 mem2 md2 k2 Hst3 R10' _.
    exact (w1_at_P1 CTX0 C fxk ly2 S2 Hp2 W2 regs2 mem2 md2 (k + k2) sp2 Lam peak cnt1 ran1 Hctx Hdoc Hst3 R10'
      HcR).
Qed.

(* ======================================================================================================== *)
(* ---- THE CLOSING LEMMA of row CR-W1 (the internal file PART7-ROWS.md): crs_from_R -> crs_from_H2 -> crs_from_W1, with the
   premises in the rows' order: HI_*, HT_* (alphabetical, the p = 0 free interim right after fuzz_free's text;
   pj_write's is crs_wexact), HK, HB_took, the named hole crs_cnt24_W1, the continuations. Kit v3: the OWN arm is
   refuted by the boundary ledger's own cell (no crs_own_keep_W1). The batch kit's cut: the RAN arm and the NULL free are refuted
   too (g_ran_out stays c_ran C = 0), so crs_from_R and HT_fuzz_free0 are not used. The free / realloc re-hiding move:
   the kit's crs_from_W1 / H2 / R carry crs_baseR at wle' SEGS RZ_cf and conclude SRr', so every stretch of W1 runs at
   wle'; fuzz_free's text asks its hull budget, paid from the run's position within the instance's caps HI_hull
   (witness crs_W1_HI_hull below) ---- *)
Lemma crs_seg_W1 : forall (CTX0 : list (list Z)) (C : crsC),
  forall (HI_head : @cf_head cp = PresetReqAt.HEAD),
  forall (HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\
    PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp),
  forall (HT_fuzz_alloc_count : forall fx' : YK11.FPState, tfuzz_alloc_count_specX (fx := fx') (rc := rc) (cp := cp)
    (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK),
  forall (HT_fuzz_alloc_ran_out : forall fx' : YK11.FPState, tfuzz_alloc_ran_out_specX (fx := fx') (rc := rc)
    (cp := cp) (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK),
  forall (HT_fuzz_free : forall fx' : YK11.FPState, tfuzz_free_specX (fx := fx') (rc := rc) (cp := cp)
    (PI := prh_img_A) (RL := RL) (PA := PA) B ARx SK),
  forall (HT_fuzz_free0 : forall fx' : YK11.FPState, crs_free0 (fx := fx') (rc := rc) (cp := cp) (RL := RL)
    (SK := SK) B ARx),
  forall (HW_exact : forall fx' : YK11.FPState, crs_wexact (fx := fx') (rc := rc) (ci := ci) (cp := cp) (RL := RL)
    (SK := SK) B ARx CTX0 C),
  forall (HK : @CrsKeep rc cp SK B ARx),
  forall (HB_took : c_took C <= 2 ^ 28),
  forall (H24 : crs_cnt24_W1 C),
  cfromR CTX0 C -> cfromH2 CTX0 C -> cfromW1 CTX0 C.
Proof.
intros CTX0 C HI_head HI_hull HT_count HT_ranout HT_free HT_free0 HW_exact HK HB_took H24 HR HH2.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt1 ran1 Hdoc HB HRr HL HD HT HcR.
assert (Hctx : w1_ctx CTX0 C)
  by exact (conj HI_head (conj HT_count (conj HT_ranout (conj HT_free (conj HT_free0 (conj HK (conj HB_took
    (conj HW_exact (conj H24 (conj HR (conj HH2 HI_hull))))))))))).
exact (w1_at_A CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Lam3 peak3 cnt1 ran1 Hctx Hdoc HB HRr HL HD HT HcR).
Qed.

End f.
End d.

(* INSTANCE WITNESS of HI_head at the real A' instance (CfParams_preset's head field, alloc.c:28's HEAD) *)
Lemma crs_W1_HI_head : @cf_head CfParamsPreset.CfParams_preset = PresetReqAt.HEAD.
Proof. reflexivity. Qed.
(* INSTANCE WITNESS of HI_hull: CfParams_preset's caps are the caps of the run's two meters (2 ^ 17 entries,
   2 ^ 36 mapped bytes) *)
Lemma crs_W1_HI_hull : PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax CfParamsPreset.CfParams_preset /\
  PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max CfParamsPreset.CfParams_preset.
Proof. vm_compute. split; discriminate. Qed.

Print Assumptions crs_seg_W1.
Print Assumptions crs_W1_HI_head.
Print Assumptions crs_W1_HI_hull.
