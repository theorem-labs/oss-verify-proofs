(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/ExvB_Entry_r1.v, with its module paths and module names changed; 1686 of its 1727 lines of code are new or changed and 256 lines of the source are left out. *)
(* fuzz_preset, image B' (the #102 pins, asan-ubsan): segment X1 of the walk of check_reject_clean_starved against the kit's
   text tcheck_reject_clean_starved_specX, row X1_B (a Theorem Labs lane's internal file BRIEF-crcs-Bprime-seg.md; lane CrsX1H1,
   a working branch; ported to the batch kit's cut 7cdbb61b5fa0 on a working branch). It proves the row's
   closing lemma over the B' kit lib/B/Prog/CrsKitBp.v, at the kit's own crs_from_X1_B (no FIX twin since the cut):
     crs_seg_X1_B : HT_fuzz_alloc_fail -> HT_check_reject_clean -> HT_pj_parse (the text PRH_FnPj.tpj_parse_specX, with
                    its guarded THE OUTCOME OF AN INJECTED READING, at every CW) -> HI_hull -> HK -> crs_from_R_B .. ->
                    crs_from_W1_B .. -> crs_from_X1_B ..
   rule 24: proves function check_reject_clean_starved on image B' (reuse search: `proof-index
   check_reject_clean_starved 0x82160`, the internal file index-crcs-Aprime.out, and an internal record of that lookup;
   CONFIRM by checker LookupCheckCrcsAp. At that search origin/ossv/recipes had no lib/A or lib/B, its released rows
   were lib/Prog (plain) and lib/U/Prog (ubsan) only, and no released asan Proof.v existed for
   check_reject_clean_starved). This file is one SEGMENT of that walk (kind: segment lemma); it is new.
   DONOR (rule 24, reuse): this lane's A' file lib/A/Prog/CrsSeg_X1.v (a working branch 5a39b8409c94): the
   same call rules, transport lemmas, grant-list agreement and closing proof, with the kit's `_B` names, every class
   instance passed by name (prh_img_B / PI_prog_B; image A's instances are also loaded here, through S1ImgB) and every
   number re-read at B'.
   INPUTS.
   - Pin B' asan-ubsan sha256 d663f82d7f488d30 (harness.yaml of release/fuzz-preset-ran-out-pins 8f3e7e1a07f1).
   - Listing lib/B/Listing_prog.v blob c97cc46b3e13 + lib/B/PAImg_prog.v blob 15fab93fe702 (a Theorem Labs lane's listings v3).
     Entry 0x820e0 = slot 645 (B_entry_check_reject_clean_starved). X1 is slots 749 .. 763.
   - The kit texts at the batch kit's cut 7cdbb61b5fa0 (a working branch): tfuzz_alloc_fail_specX
     (lib/A/PRH_FnAlloc.v blob 4d8aeba047e5), tcheck_reject_clean_specX and tcheck_reject_clean_starved_specX
     (PRH_FnCheck.v blob c40cf3fdcd2a), tpj_parse_specX (PRH_FnPj.v blob 5aca5cbe2cfb), PRH_Base.v blob ef7c8ca98529
     (fpre ends with frm_zero of the callee's float state, FRM0-ENTRY: x_callee_fpre takes it from crs_base_B), all
     at prh_img_B / PI_prog_B. lib/B/Prog/S1ImgB.v blob daf4603f76f1 (pst_not_ro_B).
   THE SEGMENT (offsets from the entry, each read off the B' listing by vm_compute in the step that uses it):
     +416 addi s8, s10, 32 (s8 = the struct pj local, cOut_B); +420 remu a0, a1, s7 (h % took); +424 jal
     fuzz_alloc_fail; +428 .. +436 a0 = data, a1 = size, a2 = s8; +440 jal pj_parse; +444 mv s7, a0; +448 li a0, -1;
     +452 jal fuzz_alloc_fail; +456 .. +464 a0 = rc, a1 = s8, a2 = s6; +468 jal check_reject_clean;
     +472 beqz s3: doc = 0 -> R (+736), else W1 (+476).
   Instructions are stepped by hand on the concrete state (CrsSeg_H1_B.v's step kit); each call goes through the kit's text of
   the callee (at its float state fx': pj_parse's strtod may change it) by x_call / x_callR / x_callWFbR below, which
   are YCbqGcall.v's aj_call_x (a Theorem Labs lane) and YCbqGwild.v's aj_call_xWFbR restated over the concrete configuration
   (no symbolic state), the footprint side condition
   being YCbqG.v's fp_sub_x; the call-site helpers x_chain / x_callee_fpre / x_ap* are lane CrsX2H2's CrsSeg_X2.v
   crs_chain / crs_callee_fpre / cx_ap* (a working branch d381430f890) restated. crs_base_B after each
   call is x_base_call (the callee journal keeps the frame, its flag and shadow, the saved words and the read-only view:
   its footprint is inside the struct pj local), after pj_parse x_base_call_rbR at the rebased context; the input and
   the tree at the exit are x_dat_entry / x_tree_entry, from
   the ENTRY's own facts through the journal from entry (FP = []), the kit's CrsKeep_B and its crs_frame_keep_dpR_B /
   crs_obj_keep_dpR_B (the journal's entry depot moved).
   THE RE-HIDING RELATION. pj_parse's text posts at WR (YA0nH.wle' at RZ_cf), so from that call on the walk is at WR:
   the stretch before it is stepped plainly under YGcfRhLift.ra_rh_of_SRr, and after it every straight stretch is
   stepped the same way and every call is bound by YSRrG.SRr'_bind; the plain texts of fuzz_alloc_fail and
   check_reject_clean are lifted to WR by x_callR (YA0nH.SRr_SRrG, YCbqG.apost_base_x_R_lift); the base, call-site
   and exit lemmas are stated at any world relation R (the _R forms; the plain names are their instances at wle).
   THE HULL BUDGET of pj_parse (HHULL in crs_seg_X1_B, at the call): the run's position at the call and its at most 4
   calls (the kit's crs_pre_los_B) bound both meters (PresetSecTotalRun's prefix bounds), a reading of at most MAXB
   bytes is one call's counts (PresetHullPay.hull_nt_parse), and HI_hull puts the run's caps within cp's.
   THE INJECTED FAILURE. fuzz_alloc_fail (h % took) sets g_fail_at = cnt + pick (pick = ck_pick tb took < took <=
   the reading's call count), so pj_parse's reading is refused: PRW_CrsModel.crs_read_inj gives res = None and its
   call count (1 <= calls <= pick + 1, = pick + 1 when nothing else was refused), which is crs_cnt_R_B; rc = -1, the 56
   bytes at s8 zero, Lam and the allocator blocks back. fuzz_alloc_fail (-1) puts g_fail_at back to SIZE_MAX;
   check_reject_clean (rc, s8, s6) meets its text (rc <> 0, the zeroed struct, s6 = lsum Lam) and changes nothing.
   Every ledger is `.. (cb_most C) 0` (no callee here touches g_most or g_own_ran_out).
   THE EXACT POSITION AT W1 / R is pj_parse's own advance, its post-implication form (tpj_parse_specX's POSITION
   TRANSFER at the cut): for the kit's run at cb_rp_i C (crs_pos_B at the boundary) and the run premise over
   E = parse_evs ReaderRes.jr_strtod tb ok at the outcomes ok the post binds, S' is at cb_rp_i C + length E. The run
   premise is the prefix of crs_pre_B's and PRH_FnPj.prhPj_parse_evs_supply at the model's grant list
   okk (PresetReqAt.pick tb took), and E at ok IS E at that list because nothing was refused: prh_granted comes from the
   text's GUARDED conjunct THE OUTCOME OF AN INJECTED READING, whose guard x_guard_B discharges from crs_pre_B;
   the two lists then agree on the positions the reading consumed (x_agree, from prh_oks's first conjunct; PresetReqAt.pick
   is ck_pick, x_pick), and x_parse_evs_agree (section agr below) proves item (d) of PRH_FnPj.v's OPEN CORRESPONDENCE:
   lists agreeing on the consumed positions give PjGrammar.jr_run the same (res, tr) (PjGrammar.agrees, G7's
   decomposition) and PresetReqAt.pj_frees the same list (jfv / jfl follow jrv / jrl, by fuel induction).
   GONE WITH THE CUT: the FIX twin crs_from_X1_FIX_B and its premises HD_pjp_end / HD_pjp_frame (pj_parse's DW memberships,
   replaced by prh_cw_pj, met by x_cw_pj) and HP_sm (the keyed ReaderRes.jr_strtod model closes crs_sm_sp_B).
   NAMED PREMISES: LAWS (the engine's Section hypothesis); HT_fuzz_alloc_fail, HT_check_reject_clean (the kit's texts
   exactly, at prh_img_B / PI_prog_B and any float state fx'); HT_pj_parse (the text PRH_FnPj.tpj_parse_specX, with its
   guarded conjunct, at every CW and any float state fx'); HI_hull (the run's meter caps SEC_N_CAP / SEC_T_CAP within
   cp's, an instance fact); HK : CrsKeep_B B ARx (the kit's transport record, proved once in the composition); the
   continuations crs_from_R_B, crs_from_W1_B at every rebased context. No own / most premise: the ledger carries both
   cells.
   Numerals: offsets +416 .. +736 (LENGTH: 4 * slot); 32 / 56 / 128 / 144 / 120 (LENGTH: the struct pj's offset and
   size, the class-1 frame, the realigned frame, its flag word); 27312 / 27168 / 8208 / 0 / 48 (LENGTH: the STK budgets
   and pi_frame F_pj_parse, by vm_compute of the kit's own names at prh_img_B); 530124 (ADDRESS: the B' text base, by
   vm_compute of pa_val A_TEXT, never typed in a statement); 33 / 5381 (WORD: djb2's multiplier and seed, in x_pick);
   2 ^ 20 .. 2 ^ 64 (LENGTH / WORD bounds); -1 and 2 ^ 64 - 1 (WORD: fuzz_alloc_fail's SIZE_MAX argument). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require WriterValue PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Reader PRH_FnCheck PRH_FnAlloc PRH_FnPj.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CrsModel PRW_CrcGen.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import CrsKitBp CrsSeg_H1_B S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost YGcfRhLift.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetSecTotal PresetSecTotalRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PresetHullPay.
(* the two Requires above load a module that leaves zify's euclidean-division flag off; this file divides by
   constants, so the flag is set back on, for this file only *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* CrsSeg_H1_B.v's section-local step tactics hfd / hpost, restated (a section's Ltac ends with it) *)
Local Ltac hfd k Hl Hd :=
  let r := eval vm_compute in (HSLOT k) in
  lazymatch r with
  | Some (PW ?w) =>
      assert (Hl : HSLOT k = Some (PW w)) by (vm_compute; reflexivity);
      let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
      assert (Hd : decode_any (Z_to_bv 32 w) = d) by (vm_compute; reflexivity)
  end.
Local Ltac hpost := intros; hcanon; hsig; rewrite ?h_vaddi0; hgetr.

(* ======================================================================================================== *)

(* ======================================================================================================== *)
(* ---- a tree's block predicate matters only on its own blocks (Cno102_FKit.v pjf_*_lblk, lane CnoA102f,
   origin/cold/h-rw-pre-5-cno102a-f 574c27759c8, moved here by path under the x_ prefix: the kit is not on this base) *)
Section pjl.
Variable segs : list Segment.
Lemma x_cstrR_lblk : forall m lblk lblk' a k s, pj_cstrR segs m lblk a k s -> (lblk a k -> lblk' a k) ->
  pj_cstrR segs m lblk' a k s.
Proof. intros m lblk lblk' a k s (Hl & Hr) H. exact (conj (H Hl) Hr). Qed.

Lemma x_itemsR_lblk : forall (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a D,
  (forall a0 u D1, In u l -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_itemsR P a l D -> pj_itemsR P' a l D.
Proof.
intros P P' l. induction l as [|u r IH]; intros a D H Hl; cbn [pj_itemsR] in *; [exact Hl|].
destruct Hl as (D1 & D2 & E & H1 & H2). exists D1, D2. split; [exact E|].
split; [apply (H a u D1); [left; reflexivity | rewrite E; apply incl_appl, incl_refl | exact H1]|].
apply (IH (a + 56) D2); [|exact H2].
intros a0 v D3 Hv Hinc HP. apply (H a0 v D3); [right; exact Hv | rewrite E; apply incl_appr; exact Hinc | exact HP].
Qed.

Lemma x_memsR_lblk : forall m lblk lblk' (P P' : Z -> PjTree.jv -> list (Z * Z) -> Prop) l a ka D,
  (forall b k, In (b, k) D -> lblk b k -> lblk' b k) ->
  (forall a0 u D1, (exists nm, In (nm, u) l) -> incl D1 D -> P a0 u D1 -> P' a0 u D1) ->
  pj_memsR segs m lblk P a ka l D -> pj_memsR segs m lblk' P' a ka l D.
Proof.
intros m lblk lblk' P P' l. induction l as [|[nm u] r IH]; intros a ka D HL H Hl; cbn [pj_memsR] in *; [exact Hl|].
destruct Hl as (x & k & D1 & D2 & E & Hx & Hc & H1 & H2). exists x, k, D1, D2.
split; [exact E|]. split; [exact Hx|].
split; [apply (x_cstrR_lblk m lblk lblk'); [exact Hc | apply HL; rewrite E; left; reflexivity]|].
split; [apply (H a u D1); [exists nm; left; reflexivity | rewrite E; intros y Hy; right; apply in_or_app; left; exact Hy
  | exact H1]|].
apply (IH (a + 56) (ka + 8) D2); [| |exact H2].
- intros b k' Hin. apply HL. rewrite E. right. apply in_or_app. right. exact Hin.
- intros a0 v D3 (nm' & Hv) Hinc HP. apply (H a0 v D3); [exists nm'; right; exact Hv | | exact HP].
  rewrite E. intros y Hy. right. apply in_or_app. right. exact (Hinc y Hy).
Qed.

Lemma x_nodeR_lblk : forall t m lblk lblk' p D,
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
  exists k. split; [|exact ED]. apply (x_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (E2 & E3 & E4 & E5 & k & Hc & ED).
  split; [exact E2|]. split; [exact E3|]. split; [exact E4|]. split; [exact E5|].
  exists k. split; [|exact ED]. apply (x_cstrR_lblk m lblk lblk'); [exact Hc|]. apply HL. rewrite ED. left. reflexivity.
- destruct Hb as (Es & Ek & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact Ek|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & Hl)]; [left; exact Hz | right; split; [exact Hp|]].
    apply HL; [|exact Hl]. rewrite ED, (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity. }
  exists Di. split; [exact ED|].
  apply (x_itemsR_lblk (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') items kids Di); [|exact Hi].
  intros a0 u D1 Hu Hinc HP. rewrite Forall_forall in IH. apply (IH u Hu m lblk lblk' a0 D1); [|exact HP].
  intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
- destruct Hb as (Es & En & Hc & Hcap & Di & ED & Hi).
  split; [exact Es|]. split; [exact En|]. split; [exact Hc|].
  split.
  { destruct Hcap as [Hz | (Hp & L0 & L1)]; [left; exact Hz | right; split; [exact Hp|]].
    rewrite (proj2 (Z.eqb_neq cap 0)) in ED by lia.
    split; apply HL; [rewrite ED; left; reflexivity | exact L0 | rewrite ED; right; left; reflexivity | exact L1]. }
  exists Di. split; [exact ED|].
  apply (x_memsR_lblk m lblk lblk' (pj_nodeR segs m lblk) (pj_nodeR segs m lblk') members kids keys Di); [| |exact Hi].
  + intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact Hin.
  + intros a0 u D1 (nm & Hu) Hinc HP. rewrite Forall_forall in IH. specialize (IH (nm, u) Hu). cbn [snd] in IH.
    apply (IH m lblk lblk' a0 D1); [|exact HP].
    intros b k Hin. apply HL. rewrite ED. apply in_or_app. right. exact (Hinc _ Hin).
Qed.
End pjl.

(* ======================================================================================================== *)
(* ---- THE GRANT-LIST AGREEMENT (PRH_FnPj.v blob 908f34f0beaa :405-413, item (d), OWED there and proved here): two
   outcome lists that agree on the positions a reading consumes give PjGrammar.jr_run the same (res, tr) and
   PresetReqAt.pj_frees the same list, hence the same PresetReqAt.parse_evs. The monad half is PjGrammar's `agrees`
   (every reader computation has it, agrees_fuel); pj_frees' jfv / jfl follow jrv / jrl call for call, so a fuel
   induction carries the agreement through them. ---- *)
Section agr.
Import PjGrammar.
Definition xagree (k : nat) (ok1 ok2 : list bool) : Prop := forall i, (i < k)%nat -> nth i ok1 true = nth i ok2 true.

Lemma xagree_le : forall k k' ok1 ok2, xagree k ok1 ok2 -> (k' <= k)%nat -> xagree k' ok1 ok2.
Proof. intros k k' ok1 ok2 H Hk i Hi. apply H. lia. Qed.

Lemma x_split_unique : forall (P1 P2 r1 r2 : list ev) (E1 E2 : ev),
  P1 ++ E1 :: r1 = P2 ++ E2 :: r2 -> calls P1 = calls P2 -> is_call E1 = true -> is_call E2 = true ->
  P1 = P2 /\ E1 = E2.
Proof.
induction P1 as [|e1 P1 IH]; intros P2 r1 r2 E1 E2 Eq Hc H1 H2; destruct P2 as [|e2 P2]; cbn [app calls] in *.
- injection Eq as -> _. split; reflexivity.
- injection Eq as <- Eq. rewrite H1 in Hc. lia.
- injection Eq as -> Eq. rewrite H2 in Hc. lia.
- injection Eq as <- Eq. assert (Hc' : calls P1 = calls P2) by (destruct (is_call e1); lia).
  destruct (IH P2 r1 r2 E1 E2 Eq Hc' H1 H2) as (-> & ->). split; reflexivity.
Qed.

(* the monad half: an `agrees` computation run on two lists that agree on what it consumes from the first *)
Lemma x_ag : forall A (m : M A), agrees m -> forall k ok1 ok2 r t q1,
  xagree k ok1 ok2 -> m ok1 = (r, t, q1) -> (calls t <= k)%nat ->
  exists q2, m ok2 = (r, t, q2) /\ xagree (k - calls t) q1 q2.
Proof.
intros A m Hm k ok1 ok2 r t q1 HA E1 Hk.
set (c := calls (snd (fst (m [])))).
destruct (ok_upto_dec ok1 c) as [Hu | (j & Hj & Hf & Hu)].
- pose proof (proj1 (Hm ok1) Hu) as M1. rewrite E1 in M1. injection M1 as -> -> ->.
  assert (Hu2 : ok_upto ok2 c).
  { intros i Hi. rewrite <- (HA i ltac:(lia)). exact (Hu i Hi). }
  rewrite (proj1 (Hm ok2) Hu2). exists (skipn c ok2). split; [reflexivity|].
  intros i Hi. rewrite !nth_skipn_b. apply HA. lia.
- destruct (proj2 (Hm ok1) j Hj Hf Hu) as (P & Ev & rest & M1 & Hs & Hcp & Hic).
  rewrite E1 in M1. injection M1 as -> -> ->.
  assert (Hct : calls (P ++ [EFail (esize Ev)]) = S j) by (rewrite calls_app; cbn [calls is_call]; lia).
  rewrite Hct in Hk |- *.
  assert (Hf2 : nth j ok2 true = false) by (rewrite <- (HA j ltac:(lia)); exact Hf).
  assert (Hu2 : ok_upto ok2 j) by (intros i Hi; rewrite <- (HA i ltac:(lia)); exact (Hu i Hi)).
  destruct (proj2 (Hm ok2) j Hj Hf2 Hu2) as (P2 & Ev2 & rest2 & M2 & Hs2 & Hcp2 & Hic2).
  rewrite Hs in Hs2. destruct (x_split_unique P P2 rest rest2 Ev Ev2 Hs2 ltac:(lia) Hic Hic2) as (<- & <-).
  exists (skipn (S j) ok2). split; [exact M2|].
  intros i Hi. rewrite !nth_skipn_b. apply HA. lia.
Qed.

Section rd. Variable sm : list Z -> Z * Z.

(* a jbind whose first computation consumed within the bound *)
Lemma x_bind_some : forall A B (m : M A) (kf : A -> M B) ok a t q,
  m ok = (Some a, t, q) -> jbind m kf ok = (fst (fst (kf a q)), t ++ snd (fst (kf a q)), snd (kf a q)).
Proof.
intros A B m kf ok a t q E. unfold jbind. rewrite E. destruct (kf a q) as [[r t'] q']. reflexivity.
Qed.
Lemma x_bind_none : forall A B (m : M A) (kf : A -> M B) ok t q,
  m ok = (None, t, q) -> jbind m kf ok = (None, t, q).
Proof. intros A B m kf ok t q E. unfold jbind. rewrite E. reflexivity. Qed.

Lemma x_ag_fst : forall A (m : M A), agrees m -> forall k ok1 ok2,
  xagree k ok1 ok2 -> (calls (snd (fst (m ok1))) <= k)%nat ->
  fst (fst (m ok1)) = fst (fst (m ok2)) /\ snd (fst (m ok1)) = snd (fst (m ok2)) /\
  xagree (k - calls (snd (fst (m ok1)))) (snd (m ok1)) (snd (m ok2)).
Proof.
intros A m Hm k ok1 ok2 HA Hk. destruct (m ok1) as [[r t] q1] eqn:E1. cbn [fst snd] in *.
destruct (x_ag A m Hm k ok1 ok2 r t q1 HA E1 Hk) as (q2 & E2 & HA2). rewrite E2. cbn [fst snd].
split; [reflexivity|]. split; [reflexivity | exact HA2].
Qed.

Lemma xag_shift : forall a k ok1 ok2, xagree (a + k - a) ok1 ok2 -> xagree k ok1 ok2.
Proof. intros a k ok1 ok2 H. replace (a + k - a)%nat with k in H by lia. exact H. Qed.

(* pj_frees' recursion respects the agreement on the positions jrv / jrl consume *)
Lemma x_jf_fuel : forall f,
  (forall d x ok1 ok2, xagree (calls (snd (fst (jrv sm f d x ok1)))) ok1 ok2 ->
     PresetReqAt.jfv sm f d x ok1 = PresetReqAt.jfv sm f d x ok2) /\
  (forall d o n cap acc af y ok1 ok2, xagree (calls (snd (fst (jrl sm f d o n cap acc y ok1)))) ok1 ok2 ->
     PresetReqAt.jfl sm f d o n cap af y ok1 = PresetReqAt.jfl sm f d o n cap af y ok2).
Proof.
pose proof (agrees_fuel sm) as AF.
pose proof agrees_grow as AGg. pose proof agrees_jr_name as AGn.
induction f as [|f IH]; [split; intros; reflexivity|].
destruct IH as (IHv & IHl). split.
- intros d x ok1 ok2 HA. pose proof HA as HA0. cbn [PresetReqAt.jfv]. cbn [jrv] in HA.
  destruct (skip x) as [|b y] eqn:Ex; [reflexivity|].
  destruct (b =? 123) eqn:E1; [|destruct (b =? 91) eqn:E2].
  + unfold PresetReqAt.jf_cont. unfold jr_cont in HA. cbv iota in HA.
    destruct (Nat.ltb MAXD (S d)) eqn:Em; [reflexivity|]. cbv zeta in HA |- *.
    destruct (skip (tl (b :: y))) as [|c r] eqn:Ey.
    * exact (IHl (S d) true 0%nat 0%nat [] [] [] ok1 ok2 HA).
    * destruct (c =? closer true) eqn:Ec; [reflexivity|].
      exact (IHl (S d) true 0%nat 0%nat [] [] (c :: r) ok1 ok2 HA).
  + unfold PresetReqAt.jf_cont. unfold jr_cont in HA. cbv iota in HA.
    destruct (Nat.ltb MAXD (S d)) eqn:Em; [reflexivity|]. cbv zeta in HA |- *.
    destruct (skip (tl (b :: y))) as [|c r] eqn:Ey.
    * exact (IHl (S d) false 0%nat 0%nat [] [] [] ok1 ok2 HA).
    * destruct (c =? closer false) eqn:Ec; [reflexivity|].
      exact (IHl (S d) false 0%nat 0%nat [] [] (c :: r) ok1 ok2 HA).
  + (* a leaf: the same jrv (S f) trace on both lists *)
    f_equal. exact (proj1 (proj2 (x_ag_fst _ _ (proj1 (AF (S f)) d x) _ ok1 ok2 HA0 (Nat.le_refl _)))).
- intros d o n cap acc af y ok1 ok2 HA. cbn [PresetReqAt.jfl]. cbn [jrl] in HA.
  (* grow *)
  destruct (grow o n cap ok1) as [[g tg] q1] eqn:G1.
  destruct g as [cap1|].
  2: { rewrite (x_bind_none _ _ _ _ _ _ _ G1) in HA. cbn [fst snd] in HA.
       destruct (x_ag _ _ (AGg o n cap) _ ok1 ok2 _ _ _ HA G1 (Nat.le_refl _)) as (q2 & G2 & _).
       rewrite G2. reflexivity. }
  rewrite (x_bind_some _ _ _ _ _ _ _ _ G1) in HA. cbv beta in HA. cbn [fst snd] in HA. rewrite calls_app in HA.
  destruct (x_ag _ _ (AGg o n cap) _ ok1 ok2 _ _ _ HA G1 ltac:(lia)) as (q2 & G2 & HA1). rewrite G2.
  apply xag_shift in HA1. clear HA.
  (* jr_name *)
  destruct (jr_name o y q1) as [[nmr tn] q3] eqn:N1.
  destruct nmr as [[nm y1]|].
  2: { rewrite (x_bind_none _ _ _ _ _ _ _ N1) in HA1. cbn [fst snd] in HA1.
       destruct (x_ag _ _ (AGn o y) _ q1 q2 _ _ _ HA1 N1 (Nat.le_refl _)) as (q4 & N2 & _).
       rewrite N2. reflexivity. }
  rewrite (x_bind_some _ _ _ _ _ _ _ _ N1) in HA1. cbv beta iota in HA1. cbn [fst snd] in HA1.
  rewrite calls_app in HA1.
  destruct (x_ag _ _ (AGn o y) _ q1 q2 _ _ _ HA1 N1 ltac:(lia)) as (q4 & N2 & HA2). rewrite N2.
  apply xag_shift in HA2. clear HA1. cbv zeta.
  (* the value: the nested jfv and its trace *)
  destruct (jrv sm f d y1 q3) as [[vr tv] q5] eqn:V1.
  destruct vr as [[v r]|].
  2: { rewrite (x_bind_none _ _ _ _ _ _ _ V1) in HA2. cbn [fst snd] in HA2.
       destruct (x_ag _ _ (proj1 (AF f) d y1) _ q3 q4 _ _ _ HA2 V1 (Nat.le_refl _)) as (q6 & V2 & _).
       rewrite V2. rewrite (IHv d y1 q3 q4 ltac:(rewrite V1; exact HA2)). reflexivity. }
  rewrite (x_bind_some _ _ _ _ _ _ _ _ V1) in HA2. cbv beta iota in HA2. cbn [fst snd] in HA2.
  rewrite calls_app in HA2.
  rewrite (IHv d y1 q3 q4 ltac:(rewrite V1; cbn [fst snd]; eapply xagree_le; [exact HA2 | lia])).
  destruct (x_ag _ _ (proj1 (AF f) d y1) _ q3 q4 _ _ _ HA2 V1 ltac:(lia)) as (q6 & V2 & HA3). rewrite V2.
  apply xag_shift in HA3. clear HA2.
  destruct (skip r) as [|c r1] eqn:Er; [reflexivity|].
  destruct (c =? 44) eqn:Ec; [|reflexivity].
  try rewrite Er in HA3. try rewrite Ec in HA3. cbv iota in HA3.
  exact (IHl d o (S n) cap1 ((nm, v) :: acc) _ r1 q5 q6 HA3).
Qed.

Lemma x_jr_run_agree : forall x ok1 ok2, xagree (calls (snd (jr_run sm x ok1))) ok1 ok2 ->
  jr_run sm x ok1 = jr_run sm x ok2.
Proof.
intros x ok1 ok2 HA. rewrite !jr_run_eq in *. cbn [snd] in HA.
destruct (x_ag_fst _ _ (agrees_jr_value sm 0 x) _ ok1 ok2 HA (Nat.le_refl _)) as (E1 & E2 & _).
rewrite E1, E2. reflexivity.
Qed.

Lemma x_parse_evs_agree : forall x ok1 ok2, xagree (calls (snd (jr_run sm x ok1))) ok1 ok2 ->
  PresetReqAt.parse_evs sm x ok1 = PresetReqAt.parse_evs sm x ok2.
Proof.
intros x ok1 ok2 HA. unfold PresetReqAt.parse_evs, PresetReqAt.rtr, PresetReqAt.pj_frees.
rewrite (x_jr_run_agree x ok1 ok2 HA). f_equal. destruct (fst (jr_run sm x ok2)); [reflexivity|].
do 2 f_equal. apply (proj1 (x_jf_fuel (S (2 * length x)))).
rewrite jr_run_eq in HA. cbn [snd] in HA. exact HA.
Qed.
End rd.
End agr.

(* ======================================================================================================== *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PI_prog_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).

(* the `jal` of a PCall slot: pc = SIGMA s, ra = the next offset (Cno102A_FA.v cfa_hs_call over HSLOT) *)
Lemma x_hs_call : forall (W : world SEGS) fxk regs mem md Q k k' s,
  HSLOT k = Some (PCall s 1%bv) -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (SIGMA s) (regupd regs 1%bv (w64 (BASE + k'))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' s Hpl Ho -> HK.
pose proof h_base as (HB0 & HB1).
pose proof (cert_slot asym (clookup pa_tbl) VAL SIGMA B_prog_listing pa_cert k (PCall s 1%bv) Hpl) as (Hck & _ & _).
unfold pi_slot_check in Hck. cbv zeta in Hck.
destruct (clookup pa_tbl (VAL A_TEXT + k)) as [wz|] eqn:Hf; [|discriminate Hck].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hdec; [|discriminate Hck].
apply andb_prop in Hck as (Hsz & Hck). apply Z.eqb_eq in Hsz. subst isz.
destruct i; try (cbn in Hck; discriminate Hck).
apply andb_prop in Hck as (Hck & Hsig). apply andb_prop in Hck as (Hrd & _). apply Z.eqb_eq in Hsig.
assert (Erd : rd = 1%bv).
{ unfold bv_eqb in Hrd. apply Z.eqb_eq in Hrd. apply bv_eq. symmetry. exact Hrd. }
subst rd.
pose proof (pa_fetch_ok _ _ Hf) as Hfw.
apply (h_step W fxk regs mem md (regupd regs 1%bv (w64 (BASE + (k + 4)))) (BASE + k) (SIGMA s) Q); [|exact HK].
rewrite (@step_jal_link fxk SEGS regs _ (mrestrict (w_H W) mem) (YK11.seg_rom SEGS) _ 1%bv imm Hfw
           (not_ecall_of_decode _ _ _ Hdec ltac:(discriminate)) Hdec).
change (bv_eqb (1%bv : bv 5) 0%bv) with false. cbv iota.
rewrite (h_pcn k 4) by lia.
replace (btgt (Z_to_bv 64 (BASE + k)) (bv_signed imm)) with (Z_to_bv 64 (SIGMA s)); [reflexivity|].
unfold btgt, v_addi. rewrite unsigned_lit_small by lia. rewrite <- Hsig.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma x_remu : forall (W : world SEGS) fxk regs mem md Q k k' w rd rs1 rs2,
  HSLOT k = Some (PW w) -> decode_any (Z_to_bv 32 w) = Some (Mul M_REMU rd rs1 rs2, 4%Z) ->
  bv_eqb rd 0%bv = false -> 0 <= k < 2 ^ 29 -> k' = k + 4 ->
  (forall X, SRr SEGS W (crs_cfg_B fxk (BASE + k') (regupd regs rd (mul_div M_REMU (getr regs rs1) (getr regs rs2))) mem
     (with_vm_backing (m_vm_lazy md) X md)) Q) ->
  SRr SEGS W (crs_cfg_B fxk (BASE + k) regs mem md) Q.
Proof.
intros W fxk regs mem md Q k k' w rd rs1 rs2 Hl Hd Hrd Hk -> HK.
apply (h_step W fxk regs mem md (regupd regs rd (mul_div M_REMU (getr regs rs1) (getr regs rs2))) (BASE + k) (BASE + (k + 4)) Q); [|exact HK].
rewrite (@step_mul_gen fxk SEGS regs _ _ _ _ M_REMU rd rs1 rs2 (h_fetch k w Hl) (not_ecall_of_decode _ _ _ Hd ltac:(discriminate)) Hd).
rewrite Hrd, (h_pcn k 4) by lia. reflexivity.
Qed.


(* ---- the struct pj local's shadow facts are kept when the frame's 16 shadow bytes are (Cno102A_FA.v
   cfa_open_keep0 at the class-1 frame: 128 bytes, the local at + 32) ---- *)
Lemma x_div8 : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof.
intros a. pose proof (Z.div_mod a 8 ltac:(lia)) as H1. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as H2.
revert H1 H2. generalize (a / 8) (a mod 8). intros q r H1 H2. lia.
Qed.
Lemma x_open_keep : forall (rd rd' : reader) F, F mod 32 = 0 -> 0 <= F ->
  (forall a, shadow_addr F <= a < shadow_addr F + 16 -> rd' a = rd a) ->
  range_addressable rd SHADOW_OFF (F + 32) 56 /\ shadow_hull_vis rd (F + 32) 56 ->
  range_addressable rd' SHADOW_OFF (F + 32) 56 /\ shadow_hull_vis rd' (F + 32) 56.
Proof.
intros rd rd' F HF HF0 Hk (Hra & Hhv).
assert (Ef : F = 32 * (F / 32)) by (pose proof (Z.div_mod F 32 ltac:(lia)); lia).
set (f := F / 32) in *. clearbody f. subst F.
split.
- apply (range_addressable_agree rd rd' SHADOW_OFF (32 * f + 32) 56); [|exact Hra].
  intros x Hx. apply Hk. unfold shadow_of_addr, shadow_addr, SHADOW_OFF. lia.
- intros s Hs. rewrite Hk; [apply Hhv; exact Hs|].
  assert (E0 : 32 * f / 8 = 4 * f) by (replace (32 * f) with ((4 * f) * 8) by lia; apply Z.div_mul; lia).
  assert (E1 : (32 * f + 32) / 8 = 4 * f + 4)
    by (replace (32 * f + 32) with ((4 * f + 4) * 8) by lia; apply Z.div_mul; lia).
  assert (E2 : (32 * f + 32 + 56 - 1) / 8 = 4 * f + 10).
  { replace (32 * f + 32 + 56 - 1) with (7 + (4 * f + 10) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  unfold shadow_addr, SHADOW_OFF in *. rewrite E1, E2 in Hs. rewrite E0.
  pose proof (x_div8 (2147450880 + (4 * f + 4))) as D1. pose proof (x_div8 (2147450880 + (4 * f + 10))) as D2.
  revert Hs D1 D2. generalize ((2147450880 + (4 * f + 4)) / 8) ((2147450880 + (4 * f + 10)) / 8).
  intros q1 q2 Hs D1 D2. clear - Hs D1 D2. lia.
Qed.

(* an application range and its shadow bytes are apart *)
Lemma x_app_shadow : forall F n, in_app F n -> 0 <= n -> F + n <= YM05.alloc_ceiling ->
  forall a, shadow_addr F <= a < shadow_addr F + (n + 7) / 8 -> ~ (F <= a < F + n).
Proof.
intros F n Happ Hn Hc a Ha Hb. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ. unfold shadow_addr, SHADOW_OFF in Ha.
pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)).
assert (F / 8 * 8 <= F) by (pose proof (Z.mul_div_le F 8 ltac:(lia)); lia).
assert ((n + 7) / 8 <= n + 7) by (apply Z.div_le_upper_bound; lia). lia.
Qed.

(* the read-only image bytes are image bytes *)
Lemma x_ro_img : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.

(* the float registers kept twice are kept *)
Lemma x_fregs_trans : forall f1 f2 f3, fregs_kept_x f1 f2 -> fregs_kept_x f2 f3 -> fregs_kept_x f1 f3.
Proof. intros f1 f2 f3 H1 H2 r Hr. rewrite (H2 r Hr). exact (H1 r Hr). Qed.

(* a sum of user sizes under a permutation *)
Lemma x_bsum_perm : forall l l', Permutation l l' -> bsum l = bsum l'.
Proof.
intros l l' H. induction H as [|x l1 l2 H IH|x y l|l1 l2 l3 H1 IH1 H2 IH2]; cbn [bsum fold_right] in *; try lia.
unfold bsum in *. lia.
Qed.

(* ======================================================================================================== *)
Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

End f.
End d.

(* ======================================================================================================== *)
(* the segment's lemmas *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
#[local] Existing Instance PI_prog_B.
#[local] Notation PA := (PI_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
Section f2.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARx).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

#[local] Notation BASEp CTX0 C := (@crs_base_B fx rc ci cp RL SK B ARx CTX0 C).
#[local] Notation PREp CTX0 C := (crs_pre_B (fx := fx) (rc := rc) B ARx CTX0 C).
#[local] Notation JJ C := (crs_J_B (rc := rc) (SK := SK) B ARx C).
(* the same at a world relation R: the walk after pj_parse runs at the re-hiding relation WR *)
#[local] Notation AJR := (ajournal_xR (SK := SK) SEGS B prh_pst ARx).
#[local] Notation BASER R CTX0 C := (@crs_baseR_B fx rc ci cp RL SK B ARx R CTX0 C).
#[local] Notation JJR R C := (crs_JR_B (rc := rc) (SK := SK) B ARx R C).
#[local] Notation WR := (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf).

(* the facts of crs_pre_B the segment uses, by name *)
Lemma x_pre_facts : forall CTX0 C, PREp CTX0 C ->
  afn_pre_x SEGS B ARx (STK_check_reject_clean_starved (PI := prh_img_B)) (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_regs C) (cb_mem C) (cb_md C) (cb_ch C) /\
  spZ (cb_regs C) + 64 <= ly_stk_hi (cb_ly C) /\
  prh_univ_closure (PI := prh_img_B) B CTX0 /\
  cSize_B C <= 3 * 2 ^ 20 /\ 0 < cb_data C /\ cb_data C + cSize_B C < 2 ^ 62 /\
  src_rd (PA := PA) (cb_W C) (cb_mem C) (cb_data C) (cb_tb C) /\
  PRH_FnReader.prhReader_home (PA := PA) B (cb_ly C) (cb_S C) (cb_Hp C) (cb_Lam C) (cb_data C) (cSize_B C) /\
  0 <= cb_took C <= ck_ncalls (cb_tb C) /\
  prh_ledger B (cb_ly C) (cb_S C) (cb_Hp C) (cb_W C) (cb_mem C) (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ (cb_ran C)
    (cb_most C) 0 /\
  cb_cnt C < 2 ^ 62 - 2 ^ 30 /\ cb_ran C = 0 /\
  blocks_bytes (cb_S C) + LIVE_check_reject_clean_starved (cb_tb C) (cb_t C) <= LIVE_MAX /\
  RQ_crcs (cb_tb C) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (cb_S C))) <= ck_FRAMES_CAP - FR_check_reject_clean_starved.
Proof.
intros CTX0 C H. unfold crs_pre_B in H.
destruct H as (HF & _ & HU & _ & _ & _ & _ & _ & H9 & H10 & H11 & H12 & H13 & H14 & _ & H16 & H17 & _ & H19 & _ & _ &
  H22 & H23 & H24 & _).
destruct HF as (HA & _ & Hhi & _).
split; [exact HA|]. split; [exact Hhi|]. split; [exact HU|]. split; [exact H9|]. split; [exact H10|].
split; [exact H11|]. split; [exact H12|]. split; [exact H13|]. split; [exact H14|]. split; [exact H16|].
split; [exact H17|]. split; [exact H19|]. split; [exact H22|]. split; [exact H23 | exact H24].
Qed.


(* the walk's own frame at a boundary: its address, alignment, range and bytes (alx_frames at the current state) *)
Lemma x_frame_factsR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  frame_addr ly3 CRS_CID_B (cb_fpos C) = cF_B C /\ In (CRS_CID_B, cb_fpos C) (frames S3) /\
  cF_B C mod 32 = 0 /\ in_app (cF_B C) 128 /\ 4096 <= cF_B C /\ cF_B C + 128 <= YM05.alloc_ceiling /\
  (forall a, cF_B C <= a < cF_B C + 128 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  ARx ly3 S3 Hp3 W3 mem3 md3.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 HB. destruct HB as (HP & _ & _ & HJ & HF & _).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ) as (EF & _).
pose proof HJ as (HAR & _).
destruct HF as (Hfrs & _ & _).
assert (Hin : In (CRS_CID_B, cb_fpos C) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (alx_frames SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR Hin) as (H32 & Happ & Hb & _).
destruct (frames_bounds_x SEGS B ARx LAWS ly3 S3 Hp3 W3 mem3 md3 CRS_CID_B (cb_fpos C) HAR Hin) as (H4096 & Hc & _).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
rewrite EF, E128 in *.
split; [reflexivity|]. split; [exact Hin|]. split; [exact H32|]. split; [exact Happ|]. split; [exact H4096|].
split; [exact Hc|]. split; [exact Hb | exact HAR].
Qed.
Lemma x_frame_facts : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  frame_addr ly3 CRS_CID_B (cb_fpos C) = cF_B C /\ In (CRS_CID_B, cb_fpos C) (frames S3) /\
  cF_B C mod 32 = 0 /\ in_app (cF_B C) 128 /\ 4096 <= cF_B C /\ cF_B C + 128 <= YM05.alloc_ceiling /\
  (forall a, cF_B C <= a < cF_B C + 128 -> apresent (w_H W3) mem3 a /\ ~ aowned B ly3 S3 a) /\
  ARx ly3 S3 Hp3 W3 mem3 md3.
Proof. exact (x_frame_factsR (@wle SEGS)). Qed.

(* crs_base_B across one call made at the boundary state (the callee's journal HJ1 from it, the walk's journal HJ2 at the
   post state): the frame, its flag word and shadow, the saved words and the read-only view are the callee journal's
   keeps (its footprint inside the struct pj local); memnorm and gp / tp from the callee's post *)
Lemma x_base_callR : forall (R : world SEGS -> world SEGS -> Prop)
  CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 STK1 FP1 k1,
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  JJR R C ly2 S2 Hp2 W2 mem2 md2 k2 ->
  AJR R STK1 sp2 FP1 ly3 S3 Hp3 W3 mem3 md3 [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> cOut_B C <= a < cOut_B C + 56) ->
  ~ YI16.sink_open_fp FP1 ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem2) ->
  getr regs2 3%bv = getr regs3 3%bv -> getr regs2 4%bv = getr regs3 4%bv ->
  frm_zero (@YK11.fp_csr fx2) -> fregs_kept_x fxk fx2 ->
  BASER R CTX0 C fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 STK1 FP1 k1
  HB HJ2 HJ1 HFP HSK HMN2 E3 E4 Hz2 Hk2.
pose proof (x_frame_factsR R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 HB)
  as (EF3 & Hin3 & H32 & Happ & H4096 & Hceil & Hpr3 & HAR3).
pose proof HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp1 & Hsp2 & Hsp3 & HDPk).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly2 S2 Hp2 W2 mem2 md2 k2 HP HJ2) as (EF2 & EFl2).
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ) as (_ & EFl3).
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
pose proof (x_pre_facts CTX0 C HP) as (HA0 & _).
destruct HA0 as (_ & _ & _ & _ & _ & Hstk0 & _).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTK : @STK_check_reject_clean_starved prh_img_B = 27312) by (vm_compute; reflexivity).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
assert (EFR : CRS_FRAME_B = 144) by (rewrite crs_frame_is_pi_B; reflexivity).
rewrite ESTK in *. rewrite EFR in Hsp1.
assert (KFR : forall a, cF_B C <= a < cF_B C + 128 -> ~ (cOut_B C <= a < cOut_B C + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. apply (G4 CRS_CID_B (cb_fpos C) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, E128. lia.
  - intros Hf. exact (Hna (HFP a Hf)). }
assert (KSH : forall a, shadow_addr (cF_B C) <= a < shadow_addr (cF_B C) + 16 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (G4 CRS_CID_B (cb_fpos C) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF3, E128. change (128 / 8) with 16. lia.
  - intros Hf. pose proof (HFP a Hf) as Hw. unfold cOut_B, CRS_OFF_DOC_B in Hw.
    apply (x_app_shadow (cF_B C) 128 Happ ltac:(lia) Hceil a); [change ((128 + 7) / 8) with 16; lia | lia]. }
assert (KST : forall a, spZ (cb_regs C) - 128 <= a < spZ (cb_regs C) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply G1; lia. }
split; [exact HP|]. split; [exact Hz2|]. split; [exact (x_fregs_trans _ _ _ Hk Hk2)|]. split; [exact HJ2|].
split.
{ pose proof HF as (Hfrs & Hflag & _).
  split; [rewrite Hfrs2; reflexivity|].
  split.
  - rewrite EFl2, <- EFl3, <- Hflag, E128. apply rdword_ext. intros kk Hkk. apply KFR; unfold cOut_B, CRS_OFF_DOC_B; lia.
  - intros a Ha. rewrite E128 in Ha.
    assert (Hin2 : In (CRS_CID_B, cb_fpos C) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRS_CID_B (cb_fpos C) HAR2 Hin2) as (_ & _ & Hb2 & _).
    rewrite EF2, E128 in Hb2. exact (proj1 (Hb2 a Ha)). }
split.
{ unfold crs_saved_B in *. apply Forall_forall. intros [o rr] Hin.
  pose proof (proj1 (Forall_forall _ _) HSV (o, rr) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 24 <= o <= 120)
    by (unfold CRS_SAVED_B in Hin; cbn [In] in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply rdword_ext. intros kk Hkk. apply KST. lia. }
split.
{ unfold crs_slot_B in *. unfold cOut_B, CRS_OFF_DOC_B in *.
  exact (x_open_keep _ _ (cF_B C) H32 ltac:(lia) KSH HSL). }
split.
{ intros a Hro Hown Herr. rewrite <- (HRO a Hro Hown Herr). apply G3.
  - exact (x_ro_img a Hro).
  - exact Hown.
  - exact Herr.
  - intros Hpst. exact (pst_not_ro_B a Hpst Hro).
  - apply fp_spares_closed. exact HSK. }
split; [exact (HMN2 HMN)|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [exact Hsp1|]. split; [exact Hsp2 | split; [exact Hsp3 | exact HDPk]].
Qed.
Lemma x_base_call : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 STK1 FP1 k1,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  JJ C ly2 S2 Hp2 W2 mem2 md2 k2 ->
  AJ STK1 sp2 FP1 ly3 S3 Hp3 W3 mem3 md3 [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> cOut_B C <= a < cOut_B C + 56) ->
  ~ YI16.sink_open_fp FP1 ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem2) ->
  getr regs2 3%bv = getr regs3 3%bv -> getr regs2 4%bv = getr regs3 4%bv ->
  frm_zero (@YK11.fp_csr fx2) -> fregs_kept_x fxk fx2 ->
  BASEp CTX0 C fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2.
Proof. exact (x_base_callR (@wle SEGS)). Qed.

(* the same across the pj_parse call, whose post is BUDGETED (wild cursor traces, the kit's cut) and at the re-hiding
   relation: the walk goes on at the REBASED context (the kit's record comment), whose journal is from the entry with
   its depot moved to d, at any world relation R *)
Lemma x_base_call_rbR : forall (R : world SEGS -> world SEGS -> Prop)
    CTX0 C d ws fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 STK1 FP1 k1 WS1,
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  JJR R (crs_with_dp_B C d ws) ly2 S2 Hp2 W2 mem2 md2 k2 -> crs_dpok_B B (crs_with_dp_B C d ws) ->
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK1 sp2 FP1 ly3 S3 Hp3 W3 mem3 md3 [] ly2 S2 Hp2 W2 mem2 md2 k1 WS1 ->
  (forall a, inFP FP1 a -> cOut_B C <= a < cOut_B C + 56) ->
  ~ YI16.sink_open_fp FP1 ->
  (YAkMemnorm.memnorm SEGS mem3 -> YAkMemnorm.memnorm SEGS mem2) ->
  getr regs2 3%bv = getr regs3 3%bv -> getr regs2 4%bv = getr regs3 4%bv ->
  frm_zero (@YK11.fp_csr fx2) -> fregs_kept_x fxk fx2 ->
  BASER R CTX0 (crs_with_dp_B C d ws) fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 sp2.
Proof.
intros R CTX0 C d ws fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 fx2 ly2 S2 Hp2 W2 regs2 mem2 md2 k2 STK1 FP1 k1 WS1
  HB HJ2 HDP2 HJ1 HFP HSK HMN2 E3 E4 Hz2 Hk2.
(* the rebased context's base is C's but for the journal and the depot fact (crs_with_dp_B moves only cb_dp / cb_ws):
   every other conjunct is C's by conversion *)
unfold crs_baseR_B.
pose proof HJ2 as HJ2'. unfold crs_JR_B in HJ2'.
cbn [crs_with_dp_B cb_regs cb_ly cb_S cb_Hp cb_W cb_mem cb_md cb_fpos cb_dp] in HJ2'.
pose proof (x_frame_factsR R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 HB)
  as (EF3 & Hin3 & H32 & Happ & H4096 & Hceil & Hpr3 & HAR3).
pose proof HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp1 & Hsp2 & Hsp3 & HDPk).
pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _).
pose proof HP as ((HFP0 & _) & _). pose proof HFP0 as (HAR0 & _).
pose proof HJ2' as (_ & Hle2 & _).
destruct (crs_ly_keep_B B ARx LAWS _ _ _ _ _ _ ly2 CRS_CID_B (cb_fpos C) HAR0 Hle2) as (EF2' & EFl2).
assert (EF2 : frame_addr ly2 CRS_CID_B (cb_fpos C) = cF_B C) by exact EF2'.
destruct (crs_cF_keepR_B B ARx LAWS R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k HP HJ) as (_ & EFl3).
pose proof HJ2' as (HAR2 & _ & _ & _ & _ & Hfrs2 & _).
pose proof (x_pre_facts CTX0 C HP) as (HA0 & _).
destruct HA0 as (_ & _ & _ & _ & _ & Hstk0 & _).
destruct Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTK : @STK_check_reject_clean_starved prh_img_B = 27312) by (vm_compute; reflexivity).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
assert (EFR : CRS_FRAME_B = 144) by (rewrite crs_frame_is_pi_B; reflexivity).
rewrite ESTK in *. rewrite EFR in Hsp1.
assert (KFR : forall a, cF_B C <= a < cF_B C + 128 -> ~ (cOut_B C <= a < cOut_B C + 56) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha Hna. apply (G4 CRS_CID_B (cb_fpos C) a Hin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF3, E128. lia.
  - intros Hf. exact (Hna (HFP a Hf)). }
assert (KSH : forall a, shadow_addr (cF_B C) <= a < shadow_addr (cF_B C) + 16 ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (G4 CRS_CID_B (cb_fpos C) a Hin3).
  - right. unfold in_zr. cbn [fst snd]. rewrite EF3, E128. change (128 / 8) with 16. lia.
  - intros Hf. pose proof (HFP a Hf) as Hw. unfold cOut_B, CRS_OFF_DOC_B in Hw.
    apply (x_app_shadow (cF_B C) 128 Happ ltac:(lia) Hceil a); [change ((128 + 7) / 8) with 16; lia | lia]. }
assert (KST : forall a, spZ (cb_regs C) - 128 <= a < spZ (cb_regs C) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply G1; lia. }
split; [exact HP|]. split; [exact Hz2|]. split; [exact (x_fregs_trans _ _ _ Hk Hk2)|]. split; [exact HJ2|].
split.
{ change (crs_frame_B C ly2 S2 W2 mem2). pose proof HF as (Hfrs & Hflag & _).
  split; [rewrite Hfrs2; reflexivity|].
  split.
  - rewrite EFl2, <- EFl3, <- Hflag, E128. apply rdword_ext. intros kk Hkk. apply KFR; unfold cOut_B, CRS_OFF_DOC_B; lia.
  - intros a Ha. rewrite E128 in Ha.
    assert (Hin2 : In (CRS_CID_B, cb_fpos C) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
    destruct (alx_frames SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 CRS_CID_B (cb_fpos C) HAR2 Hin2) as (_ & _ & Hb2 & _).
    rewrite EF2, E128 in Hb2. exact (proj1 (Hb2 a Ha)). }
split.
{ change (crs_saved_B C W2 mem2). unfold crs_saved_B in *. apply Forall_forall. intros [o rr] Hin.
  pose proof (proj1 (Forall_forall _ _) HSV (o, rr) Hin) as Hv. cbn [fst snd] in Hv |- *.
  assert (Ho : 24 <= o <= 120)
    by (unfold CRS_SAVED_B in Hin; cbn [In] in Hin; repeat destruct Hin as [Hin|Hin]; try (injection Hin as <- _; lia); destruct Hin).
  rewrite <- Hv. apply rdword_ext. intros kk Hkk. apply KST. lia. }
split.
{ change (crs_slot_B C W2 mem2). unfold crs_slot_B in *. unfold cOut_B, CRS_OFF_DOC_B in *.
  exact (x_open_keep _ _ (cF_B C) H32 ltac:(lia) KSH HSL). }
split.
{ intros a Hro Hown Herr. rewrite <- (HRO a Hro Hown Herr). apply G3.
  - exact (x_ro_img a Hro).
  - exact Hown.
  - exact Herr.
  - intros Hpst. exact (pst_not_ro_B a Hpst Hro).
  - apply fp_spares_closed. exact HSK. }
split; [exact (HMN2 HMN)|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|].
split; [exact Hsp1|]. split; [exact Hsp2 | split; [exact Hsp3 | exact HDP2]].
Qed.

(* ---- the program call at a concrete configuration (YCbqGcall.v aj_call_x_sp without the symbolic state): the
   callee's text at the caller's float state fxk, its post apost_base_x, the journals composed by ajournal_x_sub ---- *)
Lemma x_call : forall fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (apost_base_x (fx := fxk) (SK := SK) SEGS B prh_pst ARx STK1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  SRr SEGS W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fxk regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       AJ STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJ STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_x_at (SK := SK) SEGS B prh_pst ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k
    regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own). eapply (ajournal_x_sub SEGS B prh_pst ARx LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

(* x_call at a world relation R containing wle: the callee's text is the plain one (its post at wle), lifted by
   YA0nH.SRr_SRrG and YCbqG.apost_base_x_R_lift; the journals are composed by ajournal_x_subR *)
Lemma x_callR : forall (R : world SEGS -> world SEGS -> Prop) (Rw : forall W W', @wle SEGS W W' -> R W W')
  (Rt : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3)
  fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw ch1
  (K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (apost_base_x (fx := fxk) (SK := SK) SEGS B prh_pst ARx STK1 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  YA0nH.SRrG SEGS R W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2 k1,
       c2 = mkCfg (@YK11.mkst fxk regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       AJR R STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1) /\
       AJR R STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 k1 /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros R Rw Rt fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 K
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply (YA0nH.SRrG_mono SEGS R).
{ apply (YA0nH.SRr_SRrG SEGS R Rw). apply Hcallee.
  eapply (afn_pre_x_atR (SK := SK) SEGS B prh_pst ARx R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k
    regsc STK1 o ch1); try eassumption.
  - rewrite Hra. exact Hraw.
  - unfold raZ. rewrite Hra. exact Hra4.
  - rewrite Hsp. exact Hch. }
cbv beta. intros W2 c2 _ HA.
apply (apost_base_x_R_lift (SK := SK) SEGS B prh_pst ARx R Rw) in HA.
destruct HA as (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ1 & HP & HQ).
exists ly2, S2, Hp2, regs2, mem2, md2, k1. rewrite Hra. split; [reflexivity|]. rewrite Hsp in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HQ]]].
change own with ([] ++ own).
eapply (ajournal_x_subR SEGS B prh_pst ARx LAWS pa_segs_low R Rt); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.

#[local] Notation LEDGER := (prh_ledger (PI := prh_img_B) (PA := PA) B).

(* ---- THE CALL SITE'S ENTRY FACTS (lane CrsX2H2's lib/A/Prog/CrsSeg_X2.v cx_keep_above / cx_fpchain_keep /
   crs_chain / crs_callee_fpre, origin/cold/h-w6u-rep-p102-CR-X2 d381430f890, restated here under the x_ prefix:
   check_reject_clean_starved keeps s0 = its entry sp, ra at s0 - 8 and the caller's s0 at s0 - 16) ---- *)
Lemma x_keep_above : forall (R : world SEGS -> world SEGS -> Prop) C ly3 S3 Hp3 W3 mem3 md3 k,
  JJR R C ly3 S3 Hp3 W3 mem3 md3 k ->
  forall a, spZ (cb_regs C) <= a < 2 ^ 64 ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (cb_W C)) (cb_mem C) a.
Proof.
intros R C ly3 S3 Hp3 W3 mem3 md3 k HJ a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _ & _).
pose proof Hstatic as (_ & Hstk0 & Hceil & Hslo & _).
apply F1; lia.
Qed.

Lemma x_fpchain_keep : forall (r1 r2 : reader) lo top ch bp,
  (forall a, lo <= a -> a < top -> rdword r2 a = rdword r1 a) ->
  lo + 16 <= bp -> bp <= top ->
  fpchain (rdword r1) bp top ch -> fpchain (rdword r2) bp top ch.
Proof.
intros r1 r2 lo top ch. induction ch as [|[[fp ra] nfp] ch IH]; intros bp Hkeep Hbp Hbt H.
- cbn [fpchain] in *. destruct H as (r & Hr & Hb). exists r.
  rewrite (Hkeep (bp - 8)) by lia. auto.
- cbn [fpchain] in *. destruct H as (E1 & E2 & E3 & E4 & E5 & E6).
  split; [exact E1|]. split; [exact E2|].
  split; [rewrite (Hkeep (fp - 8)) by lia; exact E3|].
  split; [rewrite (Hkeep (fp - 16)) by lia; exact E4|].
  split; [exact E5|].
  destruct (bad_next fp top nfp) eqn:Eb; [exact E6|].
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb1 _].
  apply orb_false_iff in Eb1 as [Eb11 Eb12].
  apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12.
  apply (IH nfp Hkeep); [lia | lia | exact E6].
Qed.

Lemma x_chain : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2,
  PREp CTX0 C -> JJR R C ly3 S3 Hp3 W3 mem3 md3 k -> crs_saved_B C W3 mem3 ->
  spZ (cb_regs C) - CRS_FRAME_B <= sp2 <= spZ (cb_regs C) - 128 ->
  exists ch1, achain ly3 (aview SEGS (w_H W3) mem3) sp2 (spZ (cb_regs C)) ch1.
Proof.
intros R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k sp2 HPRE HJ HSV Hsp2.
pose proof HPRE as ((HAFN & _) & _).
pose proof HAFN as (HAR0 & Hra & Hra4 & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
assert (HFR : CRS_FRAME_B = 144) by (vm_compute; reflexivity).
assert (H8 : spZ (cb_regs C) mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia].
  destruct Hal16 as [q Hq]. exists (2 * q). lia. }
pose proof (proj1 (Forall_forall _ _) HSV (120, 1%bv) ltac:(cbn; tauto)) as Hw1.
pose proof (proj1 (Forall_forall _ _) HSV (112, 8%bv) ltac:(cbn; tauto)) as Hw8.
cbn [fst snd] in Hw1, Hw8.
replace (spZ (cb_regs C) - 128 + 120) with (spZ (cb_regs C) - 8) in Hw1 by lia.
replace (spZ (cb_regs C) - 128 + 112) with (spZ (cb_regs C) - 16) in Hw8 by lia.
destruct (Z_le_gt_dec (ly_top ly3 - 16) (spZ (cb_regs C))) as [Hbad|Hgood].
- exists []. left. split; [right; left; exact Hbad | reflexivity].
- exists ((spZ (cb_regs C), raZ (cb_regs C), s0Z (cb_regs C)) :: cb_ch C). right.
  split; [lia|]. split; [lia|]. split; [exact H8|].
  assert (Hkeep : forall a, spZ (cb_regs C) <= a -> a < ly_top (cb_ly C) ->
            rdword (aview SEGS (w_H W3) mem3) a = rdword (aview SEGS (w_H (cb_W C)) (cb_mem C)) a).
  { intros a Ha Hat. apply rdword_ext. intros j Hj.
    apply (x_keep_above R C ly3 S3 Hp3 W3 mem3 md3 k HJ). lia. }
  split.
  + cbn [fpchain]. split; [reflexivity|]. split; [exact H8|].
    split; [exact Hw1|]. split; [exact Hw8|]. split; [exact Hra4|].
    destruct (bad_next (spZ (cb_regs C)) (ly_top ly3) (s0Z (cb_regs C))) eqn:Eb.
    * destruct Hch as [[_ Hnil] | (Hge & Hlt & Hm8 & _ & _)]; [exact Hnil|].
      exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
      apply orb_true_iff in Eb as [Eb1 | Eb2].
      { apply orb_true_iff in Eb1 as [Eb11 | Eb12].
        - apply Z.leb_le in Eb11. lia.
        - apply Z.leb_le in Eb12. lia. }
      { apply negb_true_iff, Z.eqb_neq in Eb2. exact (Eb2 Hm8). }
    * destruct Hch as [[Hb _] | (Hge & Hlt & Hm8 & Hfp & _)].
      { exfalso. unfold bad_next in Eb. rewrite Etop in Eb.
        apply orb_false_iff in Eb as [Eb1 Eb2]. apply orb_false_iff in Eb1 as [Eb11 Eb12].
        apply Z.leb_gt in Eb11. apply Z.leb_gt in Eb12. apply negb_false_iff, Z.eqb_eq in Eb2.
        destruct Hb as [Hb | [Hb | Hb]]; lia. }
      rewrite Etop. apply (x_fpchain_keep (aview SEGS (w_H (cb_W C)) (cb_mem C))
               (aview SEGS (w_H W3) mem3) (spZ (cb_regs C))); [exact Hkeep | lia | lia | exact Hfp].
  + apply Forall_cons; [cbn [fst snd]; lia|].
    destruct Hch as [[_ Hnil] | (_ & _ & _ & _ & HFa)]; [rewrite Hnil; apply Forall_nil|].
    eapply Forall_impl; [|exact HFa]. cbv beta. intros x Hx. lia.
Qed.

Lemma x_callee_fpreR : forall (R : world SEGS -> world SEGS -> Prop)
  CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 (rg : bvmap 5 word) md ch1,
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  spZ rg = sp2 -> raZ rg < YM05.alloc_ceiling ->
  afn_pre_x SEGS B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1 ->
  fpre (fx := fxk) (PA := PA) B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 rg md ch1 HB Hsp Hra HA.
pose proof HB as (HPRE & Hfz & _ & HJ & _ & _ & _ & HROD & _ & _ & _ & _ & Hs2 & _).
pose proof HPRE as ((_ & _ & Hhi & _) & _).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehi & _).
split; [exact HA|]. split; [exact HROD|]. split; [rewrite Hsp, Ehi; lia|]. split; [exact Hra | exact Hfz].
Qed.
Lemma x_callee_fpre : forall CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 STK1 (rg : bvmap 5 word) md ch1,
  BASEp CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  spZ rg = sp2 -> raZ rg < YM05.alloc_ceiling ->
  afn_pre_x SEGS B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1 ->
  fpre (fx := fxk) (PA := PA) B ARx STK1 ly3 S3 Hp3 W3 rg mem3 md ch1.
Proof. exact (x_callee_fpreR (@wle SEGS)). Qed.

(* ---- callee-saved registers across a call (CrsSeg_X2.v cx_ap / cx_regsat_ap, S10Env.v ts_ap) ---- *)
Lemma x_ap : forall rg rg' (r : bv 5), aregs_preserved rg rg' -> acallee_saved (bv_unsigned r) -> getr rg' r = getr rg r.
Proof. intros rg rg' r HP Hr. pose proof (HP _ Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. Qed.
Lemma x_ap3 : forall rg rg', aregs_preserved rg rg' -> getr rg' 3 = getr rg 3.
Proof. intros rg rg' HP. apply x_ap; [exact HP|]. change (bv_unsigned (3%bv : bv 5)) with 3. unfold acallee_saved. lia. Qed.
Lemma x_ap4 : forall rg rg', aregs_preserved rg rg' -> getr rg' 4 = getr rg 4.
Proof. intros rg rg' HP. apply x_ap; [exact HP|]. change (bv_unsigned (4%bv : bv 5)) with 4. unfold acallee_saved. lia. Qed.
Lemma x_regsat_ap : forall rg rg' l, aregs_preserved rg rg' ->
  Forall (fun p => acallee_saved (bv_unsigned (fst p))) l -> crs_regsat_B rg l -> crs_regsat_B rg' l.
Proof.
intros rg rg' l HP Hcs H. unfold crs_regsat_B in *. rewrite Forall_forall in *. intros x Hx.
rewrite (x_ap rg rg' (fst x) HP (Hcs x Hx)). exact (H x Hx).
Qed.

(* the registers X1 carries to W1 / R, and s8 = the struct pj local: every one callee-saved *)
Definition XK (C : crsC_B) (sp2 : Z) : list (bv 5 * Z) :=
  crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C ++ [(24%bv, cOut_B C)].
Lemma x_XK_cs : forall C sp2, Forall (fun p => acallee_saved (bv_unsigned (fst p))) (XK C sp2).
Proof.
intros C sp2. unfold XK, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B. cbn [app].
repeat (apply Forall_cons; [cbn [fst]; lazymatch goal with |- acallee_saved (bv_unsigned ?x) =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; unfold acallee_saved; lia|]).
apply Forall_nil.
Qed.

(* the REMU word (CrsSeg_X2.v cx_remu_word) *)
Lemma x_remu_word : forall x n, 0 <= x < 2 ^ 64 -> 0 < n < 2 ^ 64 ->
  mul_div M_REMU (w64 x) (w64 n) = w64 (x mod n).
Proof.
intros x n Hx Hn. assert (Hm : 0 <= x mod n < n) by (apply Z.mod_pos_bound; lia).
unfold w64. rewrite m_remu by (rewrite unsigned_lit_small; lia). apply bv_eq.
rewrite v_remu_small by (rewrite unsigned_lit_small; lia). rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

(* ---- the model's pick is the harness's: PresetReqAt.pick_h is ck_djb2 at 5381 (both djb2 over the bytes, mod 2^64) ---- *)
Lemma x_pick_h : forall (x : list Z) h, fold_left (fun h b => (h * 33 + b) mod 2 ^ 64) x h = ck_djb2 h x.
Proof.
intros x. induction x as [|b r IH]; intros h; [reflexivity|]. cbn [fold_left ck_djb2].
rewrite IH. f_equal. f_equal. lia.
Qed.
Lemma x_pick : forall (x : list Z) took, 0 < took ->
  PresetReqAt.pick x (Z.to_nat took) = Z.to_nat (ck_pick x took).
Proof.
intros x took Ht. unfold PresetReqAt.pick, ck_pick, PresetReqAt.pick_h.
destruct (Z.to_nat took) as [|n] eqn:En; [lia|].
rewrite (proj2 (Z.eqb_neq took 0)) by lia. rewrite x_pick_h.
rewrite <- En, Z2Nat.id by lia. reflexivity.
Qed.

(* the instance's outcomes agree with the model's grant list okk pick when nothing was refused (DEAD-PJPARSE: every
   failed outcome is the chosen one, prh_oks's first conjunct: the chosen one fails) and the reading made pick + 1
   calls *)
Lemma x_agree : forall ok cnt (p : nat) k ns most ran ran',
  prh_oks ok cnt (cnt + Z.of_nat p) k ns most ran ran' -> prh_granted ok cnt (cnt + Z.of_nat p) k -> (k = S p)%nat ->
  PRH_FnReader.prhReader_agree ok (PresetReqAt.okk p) k.
Proof.
intros ok cnt p k ns most ran ran' (Ha & _ & _) Hg -> j Hj. unfold PresetReqAt.okk.
destruct (Nat.lt_ge_cases j p) as [Hjp|Hjp].
- rewrite app_nth1 by (rewrite repeat_length; lia). rewrite nth_repeat.
  destruct (nth j ok true) eqn:E; [reflexivity|].
  exfalso. pose proof (Hg j Hj E). lia.
- assert (Ej : j = p) by lia. subst j.
  rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. cbn [nth].
  exact (Ha p Hj eq_refl).
Qed.

(* ---- THE INPUT AND THE TREE AT ANY STATE OF THE JOURNAL FROM ENTRY, from the entry's own facts (crs_pre_B): the
   journal crs_J_B (FP = []) keeps every byte of an entry block still live, of the read-only image and of an entry
   frame, and the kit's CrsKeep_B moves the reader's home, the shadow, the tree's visibility and the doc's home.
   Stated over the journal from entry, it needs no fact about the callees in between. ---- *)
Lemma x_hblock_present : forall ly S Hp W mem md Lam peak cnt fail ran most own a k x,
  ARx ly S Hp W mem md -> LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> In (a, k) Lam -> a <= x < a + k ->
  apresent (w_H W) mem x /\ In (a - cf_head, k + cf_head) (ablocks B ly S) /\
  a - cf_head <= x < a - cf_head + req_size (k + cf_head).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a k x HAR HL Hin Hx.
pose proof (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) as HF.
destruct (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in Hk, Hb.
pose proof (@cf_head_nonneg cp) as Hc0. assert (Hkc : 0 <= k + cf_head) by lia.
pose proof (YCbq.req_size_pos (k + cf_head) Hkc) as (_ & Hrq).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hb) as (_ & _ & _ & _ & Hpr & _).
split; [apply (Hpr x); lia|]. split; [exact Hb | lia].
Qed.

Lemma x_garr_av : forall (H H' : word -> bool) m m' a l,
  (forall j, (j < length l)%nat -> aview SEGS H' m' (a + Z.of_nat j) = aview SEGS H m (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hag HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [Z.of_nat]. rewrite Z.add_0_r in *.
rewrite (mbyte_of_aview SEGS H H' m m' _ (Hag j Hj)). pose proof (V 0%nat Hi) as V0. cbn [Z.of_nat] in V0.
rewrite Z.add_0_r in V0. exact V0.
Qed.

Lemma x_dat_entry : CrsKeep_B B ARx ->
  forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 fail3 ran3 most3 own3,
  PREp CTX0 C -> JJR R C ly3 S3 Hp3 W3 mem3 md3 k ->
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 -> crs_perm_B B C ly3 S3 Lam3 ->
  crs_dat_B B C ly3 S3 Hp3 W3 mem3 Lam3.
Proof.
intros HK R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 fail3 ran3 most3 own3 HP HJ HL3 (HpL & Hpb).
pose proof HP as (HF & _ & _ & _ & _ & _ & _ & _ & _ & Hd0 & _ & HSRC & Hhm & _ & _ & HL0 & _).
pose proof HF as ((HAR0 & _) & _).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & G2 & G3 & _).
pose proof HSRC as (Hby & H4096 & Hdc & _).
assert (Hbl : forall p n, In (p, n) (ablocks B (cb_ly C) (cb_S C)) -> In (p, n) (ablocks B ly3 S3))
  by (intros p n H; exact (Permutation_in _ (Permutation_sym Hpb) H)).
assert (Kdt : forall a, cb_data C <= a < cb_data C + cSize_B C ->
  aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (cb_W C)) (cb_mem C) a).
{ intros a Ha.
  destruct Hhm as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
  - destruct (x_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ b m a HAR0 HL0 Hbm ltac:(lia)) as (_ & Hblk & Hrg).
    replace a with ((b - cf_head) + (a - (b - cf_head))) by lia.
    apply (G2 _ _ _ Hblk (Hbl _ _ Hblk)); [lia | intros (r & Hr & _); destruct Hr].
  - destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3').
    exact (G3 a (x_ro_img a Hr1) Hr2 Hr3' (fun Hp => pst_not_ro_B a Hp Hr1) (fp_spares_closed [] a sink_closed_nil)).
  - destruct (Hro a Ha) as (Hr1 & Hr2 & Hr3' & _).
    exact (G3 a (x_ro_img a Hr1) Hr2 Hr3' (fun Hp => pst_not_ro_B a Hp Hr1) (fp_spares_closed [] a sink_closed_nil)).
  - assert (Hm0 : 0 <= m) by lia. pose proof (YCbq.req_size_pos m Hm0) as (_ & Hrq).
    replace a with (b + (a - b)) by lia.
    apply (G2 _ _ _ Hbm (Hbl _ _ Hbm)); [lia | intros (r & Hr & _); destruct Hr]. }
assert (Hhm3 : PRH_FnReader.prhReader_home (PA := PA) B ly3 S3 Hp3 Lam3 (cb_data C) (cSize_B C))
  by (eapply (kpb_home_move B ARx HK); [exact HL0 | exact HL3 | exact HpL | exact Hpb | exact Hhm]).
split; [|split; [exact Hhm3|]].
- unfold PRH_Base.bytes_at in *. apply (x_garr_av (w_H (cb_W C)) (w_H W3) (cb_mem C) mem3 _ _); [|exact Hby].
  intros j Hj. apply Kdt. unfold cSize_B. lia.
- destruct (Z_lt_le_dec 0 (cSize_B C)) as [Hn|Hn].
  + destruct (kpb_home_sh B ARx HK ly3 S3 Hp3 W3 mem3 md3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 (cb_data C) (cSize_B C)
      HAR3 HL3 Hhm3 Hn ltac:(lia) ltac:(unfold cSize_B in *; lia)) as (Hra & Hhv).
    split; [exact Hra | intros _; exact Hhv].
  + split; [intros x Hx; lia | intros Hn'; lia].
Qed.

Lemma x_tree_entry : CrsKeep_B B ARx ->
  forall (R : world SEGS -> world SEGS -> Prop) CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 fail3 ran3 most3 own3,
  PREp CTX0 C -> JJR R C ly3 S3 Hp3 W3 mem3 md3 k ->
  LEDGER ly3 S3 Hp3 W3 mem3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 -> crs_perm_B B C ly3 S3 Lam3 ->
  crs_tree_B C ly3 S3 Lam3 W3 mem3.
Proof.
intros HK R CTX0 C ly3 S3 Hp3 W3 mem3 md3 k Lam3 peak3 cnt3 fail3 ran3 most3 own3 HP HJ HL3 (HpL & Hpb) Hd.
pose proof HP as (HF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDOC & HL0 & _).
destruct HDOC as [Hd0 | (_ & HTOK & _)]; [exfalso; exact (Hd Hd0)|].
destruct HTOK as (Hn & HD & _ & Hobj).
pose proof HF as ((HAR0 & _) & _).
pose proof HJ as (HAR3 & Hly & _ & _ & _ & Hfrs & _ & _ & _ & G2 & _).
assert (HD3 : forall bk, In bk (cb_D C) -> In bk Lam3)
  by (intros bk Hb; exact (Permutation_in _ (Permutation_sym HpL) (HD bk Hb))).
assert (Hbl : forall p n, In (p, n) (ablocks B (cb_ly C) (cb_S C)) -> In (p, n) (ablocks B ly3 S3))
  by (intros p n H; exact (Permutation_in _ (Permutation_sym Hpb) H)).
split; [|split; [exact HD3 | split]].
- apply (pj_nodeR_frame SEGS (cb_t C) _ _ _ _ _
    (x_nodeR_lblk SEGS (cb_t C) _ (prh_lin (cb_Lam C)) (prh_lin Lam3) _ _
       (fun b kk _ H => Permutation_in _ (Permutation_sym HpL) H) Hn)).
  intros x Hx.
  assert (Kx : aview SEGS (w_H W3) mem3 x = aview SEGS (w_H (cb_W C)) (cb_mem C) x /\ apresent (w_H W3) mem3 x).
  { destruct Hx as [Hx | ((a, kk) & Hb & Hx)].
    - destruct Hobj as (_ & (cid & pos & Hin & Hlo & Hhi) & _).
      split.
      + unfold crs_JR_B in HJ.
        eapply (crs_frame_keep_dpR_B B ARx R); [exact HJ | exact Hin |].
        left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
      + assert (Hin3 : In (cid, pos) (frames S3)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
        destruct (crs_ly_keep_B B ARx LAWS _ _ _ _ _ _ ly3 cid pos HAR0 Hly) as (Efa & _).
        destruct (alx_frames _ _ _ LAWS ly3 S3 Hp3 W3 mem3 md3 cid pos HAR3 Hin3) as (_ & _ & Fb & _).
        rewrite Efa in Fb. exact (proj1 (Fb x ltac:(lia))).
    - unfold pj_holdsR in Hx. cbn [fst snd] in Hx.
      destruct (x_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ a kk x HAR0 HL0 (HD _ Hb) Hx) as (_ & Hblk & Hrg).
      split.
      + replace x with ((a - cf_head) + (x - (a - cf_head))) by lia.
        apply (G2 _ _ _ Hblk (Hbl _ _ Hblk)); [lia | intros (r & Hr & _); destruct Hr].
      + exact (proj1 (x_hblock_present _ _ _ _ _ _ _ _ _ _ _ _ _ a kk x HAR3 HL3 (HD3 _ Hb) Hx)). }
  destruct Kx as (Kv & Kp). split.
  + apply (mbyte_of_aview SEGS). exact Kv.
  + intros _. apply (apresent_writable SEGS). exact Kp.
- exact (kpb_tree_vis B ARx HK ly3 S3 Hp3 W3 mem3 md3 Lam3 peak3 cnt3 fail3 ran3 most3 own3 (cb_D C) HAR3 HL3 HD3).
- unfold crs_JR_B in HJ. eapply (crs_obj_keep_dpR_B B ARx LAWS R); [exact HAR0 | exact HJ | exact Hobj].
Qed.

(* CrsSeg_H1_B.v's h_base_step at a world relation R: one instruction moves only the registers and the model's
   backing (ajournal_x_materializeR) *)
Lemma x_base_stepR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X,
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 ->
  getr regs' 3%bv = getr regs3 3%bv -> getr regs' 4%bv = getr regs3 4%bv ->
  BASER R CTX0 C fxk ly3 S3 Hp3 W3 regs' mem3 (with_vm_backing (m_vm_lazy md3) X md3) k sp2.
Proof.
intros R CTX0 C fxk ly3 S3 Hp3 W3 regs3 regs' mem3 md3 k sp2 X HB E3 E4.
destruct HB as (HP & Hz & Hk & HJ & HF & HSV & HSL & HRO & HMN & R3 & R4 & Hsp).
split; [exact HP|]. split; [exact Hz|]. split; [exact Hk|].
split; [unfold crs_JR_B in *;
  exact (ajournal_x_materializeR (SK := SK) SEGS B prh_pst ARx LAWS pa_segs_low R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X HJ)|].
split; [exact HF|]. split; [exact HSV|]. split; [exact HSL|]. split; [exact HRO|]. split; [exact HMN|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. exact Hsp.
Qed.

(* ---- the step tactics of this segment (CrsSeg_H1_B.v hb_upd / hrs_upd at this section's B ARx LAWS) ---- *)
Ltac xb HB :=
  lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ (with_vm_backing (m_vm_lazy ?m) ?X ?m)) _ =>
    let H' := fresh "HB'" in
    first
      [ pose proof (h_base_step B ARx LAWS _ _ _ _ _ _ _ _ r _ _ _ _ X HB ltac:(hgetr; reflexivity)
          ltac:(hgetr; reflexivity)) as H'
      | pose proof (x_base_stepR _ _ _ _ _ _ _ _ _ r _ _ _ _ X HB ltac:(hgetr; reflexivity)
          ltac:(hgetr; reflexivity)) as H' ];
    clear HB; rename H' into HB end.
Ltac xr HR :=
  lazymatch goal with
  | |- SRr _ _ (crs_cfg_B _ _ (regupd ?rg ?rr ?v) _ _) _ =>
    let l := lazymatch type of HR with crs_regsat_B _ ?l => l end in
    let H' := fresh "HR'" in
    pose proof (h_regsat_upd rg l rr v ltac:(unfold XK, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hnot) HR) as H';
    clear HR; rename H' into HR
  | _ => idtac end.
Ltac xg HR := apply (h_regsat_get _ _ _ _ HR); unfold XK, crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hin.

(* ---- a call site of the segment: the stack pointer, s0, gp / tp, the return address (a listing slot) and the
   frame-pointer chain ---- *)
Lemma x_callsiteR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs mem md k sp2 ret,
  BASER R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (XK C sp2) -> getr regs 1%bv = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 29 -> ret mod 2 = 0 ->
  spZ regs = sp2 /\ s0Z regs = spZ (cb_regs C) /\
  getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
  YK0s.ret_ok (w64 (BASE + ret)) /\ 4096 <= bv_unsigned (w64 (BASE + ret)) /\ raZ regs < YM05.alloc_ceiling /\
  (sp2 - spZ (cb_regs C)) mod 16 = 0 /\ - 144 <= sp2 - spZ (cb_regs C) <= - 128 /\
  exists ch1, achain ly (aview SEGS (w_H W) mem) (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) (s0Z regs) ch1.
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 ret HB HR R1 Hret Hev.
pose proof HB as (HPRE & _ & _ & HJ & _ & HSV & _ & _ & _ & R3 & R4 & Hs1 & Hs2 & Hs3 & HDPk).
pose proof (x_pre_facts CTX0 C HPRE) as (HAFN0 & _).
pose proof HAFN0 as (_ & _ & _ & Hgp0 & Htp0 & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof h_base as (HB0 & HB1).
assert (EFR : CRS_FRAME_B = 144) by (rewrite crs_frame_is_pi_B; reflexivity).
rewrite EFR in Hs1.
assert (G2 : getr regs 2%bv = w64 sp2) by xg HR.
assert (G8 : getr regs 8%bv = w64 (spZ (cb_regs C))) by xg HR.
assert (EBASE : BASE = 530124) by (vm_compute; reflexivity).
assert (Hlt : BASE + ret < YM05.alloc_ceiling) by lia.
assert (Es0 : s0Z regs = spZ (cb_regs C)) by (unfold s0Z; rewrite G8; unfold w64; apply unsigned_lit_small; lia).
split; [unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia|].
split; [exact Es0|].
split; [rewrite R3; exact Hgp0|]. split; [rewrite R4; exact Htp0|].
split; [unfold w64; apply (ret_ok_codeptr_v (PI := PA)); [lia | exact Hev]|].
split; [unfold w64; rewrite unsigned_lit_small by lia; lia|].
split; [unfold raZ; rewrite R1; unfold w64; rewrite unsigned_lit_small by lia; exact Hlt|].
split.
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide in Hs3; [|lia].
  destruct Hal16 as [q1 Hq1]. destruct Hs3 as [q2 Hq2]. exists (2 * q2 - q1). lia. }
split; [lia|].
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 by lia. rewrite Es0.
exact (x_chain R CTX0 C ly S Hp W mem md k sp2 HPRE HJ HSV ltac:(rewrite EFR; lia)).
Qed.
Lemma x_callsite : forall CTX0 C fxk ly S Hp W regs mem md k sp2 ret,
  BASEp CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (XK C sp2) -> getr regs 1%bv = w64 (BASE + ret) ->
  0 <= ret < 2 ^ 29 -> ret mod 2 = 0 ->
  spZ regs = sp2 /\ s0Z regs = spZ (cb_regs C) /\
  getr regs 3%bv = w64 (as_gp B) /\ getr regs 4%bv = w64 (as_tp B) /\
  YK0s.ret_ok (w64 (BASE + ret)) /\ 4096 <= bv_unsigned (w64 (BASE + ret)) /\ raZ regs < YM05.alloc_ceiling /\
  (sp2 - spZ (cb_regs C)) mod 16 = 0 /\ - 144 <= sp2 - spZ (cb_regs C) <= - 128 /\
  exists ch1, achain ly (aview SEGS (w_H W) mem) (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) (s0Z regs) ch1.
Proof. exact (x_callsiteR (@wle SEGS)). Qed.

(* ---- the pj_parse call's slot, window and separation premises (tpj_parse_specX :460-464), at s8 = cOut_B ---- *)
Lemma x_pjp_site : CrsKeep_B B ARx ->
  forall CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran most own,
  BASEp CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  LEDGER ly S Hp W mem Lam peak cnt fail ran most own -> crs_perm_B B C ly S Lam -> spZ regs = sp2 ->
  fwin (PA := PA) ly W regs mem 0 /\
  prhPj_slot (PA := PA) B (STK_pj_parse (PI := prh_img_B)) 0 ly S Lam W regs mem (cOut_B C) /\ cOut_B C < YM05.alloc_ceiling /\
  (forall a kk, In (a, kk) Lam -> cOut_B C + 56 <= a \/ a + kk <= cOut_B C) /\
  (0 < cSize_B C -> cb_data C + cSize_B C <= cOut_B C \/ cOut_B C + 56 <= cb_data C) /\
  src_rd (PA := PA) W mem (cb_data C) (cb_tb C) /\ PRH_FnReader.prhReader_home (PA := PA) B ly S Hp Lam (cb_data C) (cSize_B C).
Proof.
intros HK CTX0 C fxk ly S Hp W regs mem md k sp2 Lam peak cnt fail ran most own HB HL Hperm Hsp.
pose proof (x_frame_facts CTX0 C fxk ly S Hp W regs mem md k sp2 HB)
  as (EF & Hin & H32 & Happ & H4096 & Hceil & Hpr & HAR).
pose proof HB as (HPRE & _ & _ & HJ & _ & _ & HSL & _ & _ & _ & _ & Hs1 & Hs2 & Hs3 & HDPk).
pose proof (x_dat_entry HK (@wle SEGS) CTX0 C ly S Hp W mem md k Lam peak cnt fail ran most own HPRE HJ HL Hperm)
  as (Hby & Hhm & Hra & Hhv).
pose proof (x_pre_facts CTX0 C HPRE) as (HAFN0 & _ & _ & Hsz & Hd0 & Hd62 & HSRC & _).
pose proof HAFN0 as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
pose proof HJ as (_ & Hly & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (ESTK : @STK_check_reject_clean_starved prh_img_B = 27312) by (vm_compute; reflexivity).
assert (ESTKp : @STK_pj_parse prh_img_B = 27168) by (vm_compute; reflexivity).
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
assert (EFR : CRS_FRAME_B = 144) by (rewrite crs_frame_is_pi_B; reflexivity).
rewrite ESTK in Hslo. rewrite EFR in Hs1.
pose proof (@cf_head_nonneg cp) as Hh0.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof HSRC as (_ & Hs4096 & Hsc & Hsam & _).
assert (H8 : (cF_B C + 32) mod 8 = 0).
{ pose proof H32 as H32'. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H32'; [|lia].
  destruct H32' as [q Hq]. exists (4 * q + 4). lia. }
assert (HFB : forall b m, In (b, m) (ablocks B ly S) -> b + req_size m <= cF_B C \/ cF_B C + 128 <= b).
{ intros b m Hb. pose proof (sep_block_frame_x SEGS B ARx LAWS ly S Hp W mem md b m CRS_CID_B (cb_fpos C) HAR Hb Hin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite EF, E128 in Hz. exact Hz. }
unfold cOut_B, CRS_OFF_DOC_B in *.
split.
{ split; [lia|]. split; [reflexivity|]. split; [rewrite Hsp, Etop; lia | intros a Ha; lia]. }
split.
{ split; [lia|].
  split; [right; right; left; exists CRS_CID_B, (cb_fpos C); split; [exact Hin|]; rewrite EF, E128; lia|].
  split; [split; [exact H8 | intros x Hx; apply (apresent_writable SEGS); exact (proj1 (Hpr x ltac:(lia)))]|].
  split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
  split; [intros a Ha; split; [exact (proj2 (Hpr a ltac:(lia))) | rewrite Hsp, ESTKp; lia]|].
  unfold crs_slot_B, cOut_B, CRS_OFF_DOC_B in HSL. exact HSL. }
split; [lia|].
split.
{ intros a kk Hak.
  pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) (a, kk) Hak) as (Hk & Hb & _).
  cbn [fst snd] in Hk, Hb.
  assert (Hkc : 0 <= kk + cf_head) by lia. pose proof (YCbq.req_size_pos (kk + cf_head) Hkc) as (_ & Hrq).
  destruct (HFB _ _ Hb); lia. }
split.
{ intros Hn.
  destruct Hhm as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & _ & Hro) | (_ & _ & Hro)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
  - pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL) (b, m) Hbm) as (Hk & Hb & _).
    cbn [fst snd] in Hk, Hb.
    assert (Hkc : 0 <= m + cf_head) by lia. pose proof (YCbq.req_size_pos (m + cf_head) Hkc) as (_ & Hrq).
    destruct (HFB _ _ Hb); lia.
  - destruct (Z_le_gt_dec (cb_data C + cSize_B C) (cF_B C + 32)) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (cF_B C + 32 + 56) (cb_data C)) as [H2|H2]; [right; exact H2|].
    exfalso. set (x := Z.max (cb_data C) (cF_B C + 32)).
    destruct (Hro x ltac:(unfold x; lia)) as (Hr1 & _).
    apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CRS_CID_B (cb_fpos C) x HAR Hin); [rewrite EF, E128; unfold x; lia|].
    exact (x_ro_img x Hr1).
  - destruct (Z_le_gt_dec (cb_data C + cSize_B C) (cF_B C + 32)) as [H1|H1]; [left; exact H1|].
    destruct (Z_le_gt_dec (cF_B C + 32 + 56) (cb_data C)) as [H2|H2]; [right; exact H2|].
    exfalso. set (x := Z.max (cb_data C) (cF_B C + 32)).
    destruct (Hro x ltac:(unfold x; lia)) as (Hr1 & _).
    apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md CRS_CID_B (cb_fpos C) x HAR Hin); [rewrite EF, E128; unfold x; lia|].
    exact (x_ro_img x Hr1).
  - assert (Hkc : 0 <= m) by lia. pose proof (YCbq.req_size_pos m Hkc) as (_ & Hrq).
    destruct (HFB _ _ Hbm); lia. }
split; [|exact Hhm].
split; [exact Hby|]. split; [lia|]. split; [lia|]. split; [exact Hsam|]. split; [exact Hra | exact Hhv].
Qed.

(* ---- check_reject_clean's doc: the zeroed struct pj local (tcheck_reject_clean_specX's src_rd) ---- *)
Lemma x_zero_srcR : forall (R : world SEGS -> world SEGS -> Prop) CTX0 C fxk ly S Hp W regs mem md k sp2,
  BASER R CTX0 C fxk ly S Hp W regs mem md k sp2 ->
  pj_zeroR SEGS (rdW W mem) (cOut_B C) -> src_rd (PA := PA) W mem (cOut_B C) (repeat 0 56).
Proof.
intros R CTX0 C fxk ly S Hp W regs mem md k sp2 HB HZ.
pose proof (x_frame_factsR R CTX0 C fxk ly S Hp W regs mem md k sp2 HB) as (_ & _ & _ & Happ & H4096 & Hceil & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & HSL & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
unfold crs_slot_B in HSL. destruct HSL as (Hra & Hhv).
unfold src_rd. rewrite repeat_length. change (Z.of_nat 56) with 56.
split; [exact HZ|]. unfold cOut_B, CRS_OFF_DOC_B in *. split; [lia|]. split; [lia|].
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
split; [exact Hra | intros _; exact Hhv].
Qed.

(* ---- THE EXIT (+472 beqz s3): doc = 0 -> R (+736), else W1 (+476). After pj_parse the walk is at the re-hiding
   relation WR; the branch is stepped plainly (YGcfRhLift.ra_rh_of_SRr) and each arm enters its continuation, which
   concludes at WR ---- *)
Lemma x_exit : CrsKeep_B B ARx ->
  forall CTX0 C fx5 ly S Hp W regs mem md k sp2 Lam peak cnt ran,
  @crs_from_R_B fx rc ci cp RL SK B ARx CTX0 C ->
  @crs_from_W1_B fx rc ci cp RL SK B ARx CTX0 C ->
  cb_took C <> 0 ->
  BASER WR CTX0 C fx5 ly S Hp W regs mem md k sp2 ->
  crs_regsat_B regs (XK C sp2) ->
  LEDGER ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (cb_most C) 0 -> crs_perm_B B C ly S Lam ->
  cb_peak C <= peak -> ran = cb_ran C -> cb_cnt C <= cnt < 2 ^ 62 -> room_live_cf S ->
  crs_pos_B C (crs_evs_at_W1_B C) ran S -> crs_cnt_R_B C cnt ran ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (crs_cfg_B fx5 (BASE + (CRS_PC0_B + 472)) regs mem md)
    (crs_post_B (fx := fx) (rc := rc) B ARx C).
Proof.
intros HK CTX0 C fx5 ly S Hp W regs mem md k sp2 Lam peak cnt ran KcR KcW1 Htk HB HR HL Hperm Hpk Hran Hc
  Hroom Hpos Hcnt.
apply YGcfRhLift.ra_rh_of_SRr.
pose proof h_pc0 as HPC.
pose proof HB as (HPRE & _ & _ & HJ & _).
pose proof (h_doc_range B ARx LAWS CTX0 C HPRE) as Hdoc.
assert (G19 : getr regs 19%bv = w64 (cb_doc C)) by xg HR.
assert (HLV : forall evs, evs = crs_evs_at_W1_B C -> crs_live_B B C ly S Hp W mem Lam peak cnt ran evs).
{ intros evs ->. split; [|exact Hperm]. split; [exact HL|]. split; [exact Hpk|]. split; [exact Hran|].
  split; [lia|]. split; [lia|]. split; [exact Hroom | exact Hpos]. }
pose proof (x_dat_entry HK WR CTX0 C ly S Hp W mem md k Lam peak cnt SIZE_MAXZ ran (cb_most C) 0 HPRE HJ HL Hperm)
  as HDt.
pose proof (x_tree_entry HK WR CTX0 C ly S Hp W mem md k Lam peak cnt SIZE_MAXZ ran (cb_most C) 0 HPRE HJ HL Hperm)
  as HTr.
hfd (CRS_PC0_B + 472) Hl Hd.
eapply (h_br W fx5 regs mem md _ (CRS_PC0_B + 472) (CRS_PC0_B + 736) (CRS_PC0_B + 476) _ _ _ _ _ Hl Hd);
  [lia | reflexivity | lia | reflexivity | |].
- intros Hb ?. revert Hb. hcanon. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0). rewrite G19.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply Z.eqb_eq in Hb.
  xb HB. apply SRr_ret. change (BASE + (CRS_PC0_B + 736)) with (BASE + CRS_PC_R_B).
  refine (KcR fx5 ly S Hp W regs mem _ k sp2 Lam peak cnt ran HB _ (HLV _ _) (proj1 HDt) HTr _).
  + apply (h_regsat_incl regs (XK C sp2)); [exact HR|]. intros p Hp'. unfold XK. rewrite !in_app_iff in *. tauto.
  + unfold crs_evs_at_R_B. exact (crs_evs_doc0_B C Hb).
  + unfold crs_cnt_end_B. destruct Hcnt as (_ & Hcnt). destruct (Hcnt Htk) as (Hc1 & Hc2).
    rewrite (crs_growth_doc0_B C Hb). unfold ck_crcs_max, crs_cnt1_B, crs_first_B.
    rewrite (proj2 (Z.eqb_neq (cb_took C) 0) Htk), (proj2 (Z.eqb_eq (cb_doc C) 0) Hb). cbv iota.
    split; [lia | intros Hr0; rewrite (Hc2 Hr0); lia].
- intros Hb ?. revert Hb. hcanon. rewrite ?getr_zero. change (Z_to_bv 64 0) with (w64 0). rewrite G19.
  cbn [branch_taken]. rewrite hw_eqb by lia. intros Hb. apply Z.eqb_neq in Hb.
  xb HB. apply SRr_ret. change (BASE + (CRS_PC0_B + 476)) with (BASE + CRS_PC_W1_B).
  refine (KcW1 fx5 ly S Hp W regs mem _ k sp2 Lam peak cnt ran Hb HB _ (HLV _ eq_refl) HDt HTr Hcnt).
  apply (h_regsat_incl regs (XK C sp2)); [exact HR|]. intros p Hp'. unfold XK. rewrite !in_app_iff in *. tauto.
Qed.

(* ==== THE pj_parse CALL AT THE KIT'S CUT: its two new entry facts, its cursor set and room, its budgeted call rule ==== *)
(* the live set (PresetRoom.rs_live of the cf room) is the allocator blocks' sizes: a permutation of the blocks
   permutes it (A' x_live_perm, lib/A/Prog/CrsSeg_X1.v:1164 at a working branch 7f61536759ab, the instance
   swapped) *)
Lemma x_live_perm : forall ly S ly' S', Permutation (ablocks B ly S) (ablocks B ly' S') ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S)) (PresetRoom.rs_live (YGcfRoom.room_of_cf S')).
Proof.
intros ly S ly' S' H. unfold YGcfRoom.room_of_cf. cbn [PresetRoom.rs_live].
apply (Permutation_map snd) in H. unfold ablocks in H. rewrite !map_map in H. exact H.
Qed.

(* the input's home ends strictly below alloc_ceiling (tpj_parse_specX's `t0 + len < YM05.alloc_ceiling`): a live
   allocator block ends at least 8 bytes below it (alx_blocks_ceil8), a harness block lies inside one, an image home
   ends below the image top (A' x_text_ceil, CrsSeg_X1.v:1174 at 7f61536759ab, the instance swapped) *)
Lemma x_text_ceil : forall CTX0 C, PREp CTX0 C -> cb_data C + cSize_B C < YM05.alloc_ceiling.
Proof.
intros CTX0 C HP.
pose proof (x_pre_facts CTX0 C HP) as (HAFN0 & _ & _ & _ & Hd0 & _ & HSRC & Hhm & _ & HL0 & _).
pose proof HAFN0 as (HAR0 & _).
pose proof HSRC as (_ & _ & Hsc & _).
pose proof asan_consts as (AC1 & _).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (Hhi : @pa_hi _ B_prog_listing PA < 0x7fff7f800000) by (vm_compute; reflexivity).
unfold cSize_B in *.
destruct Hhm as [[(b & m & Hbm & Hb1 & Hb2) | [(_ & _ & Hi & _) | (_ & Hi & _)]] | (b & m & Hbm & _ & Hb1 & Hb2)].
- pose proof (proj1 (Forall_forall _ _) (prh_ledger_blocks B _ _ _ _ _ _ _ _ _ _ _ _ HL0) (b, m) Hbm) as (Hk & Hb & _).
  cbn [fst snd] in Hk, Hb.
  assert (Hkc : 0 <= m + cf_head) by lia. pose proof (YCbq.req_size_pos (m + cf_head) Hkc) as (_ & Hrq).
  pose proof (alx_blocks_ceil8 _ _ _ LAWS _ _ _ _ _ _ _ _ HAR0 Hb) as Hc8. lia.
- lia.
- lia.
- assert (Hkc : 0 <= m) by lia. pose proof (YCbq.req_size_pos m Hkc) as (_ & Hrq).
  pose proof (alx_blocks_ceil8 _ _ _ LAWS _ _ _ _ _ _ _ _ HAR0 Hbm) as Hc8. lia.
Qed.

(* THE CURSOR SET of this call, in a Theorem Labs lane's pn_cw form (a working branch d8d35af5457c
   lib/B/Prog/PN102BCuts.v:276-293), at crcs's arguments: parse_items' trace at the cursor end data + size,
   parse_string's at the slot word memory holds at pj_parse's sp - pi_frame F_pj_parse (B' reads that word; it is
   not chosen). Its two traces are WILD on B' (a data word), so the post's budget is carried, not dropped. *)
Definition x_slotw (W : world SEGS) (mem : word -> option byte) (sp : Z) : Z :=
  match rdword (aview SEGS (w_H W) mem) (sp - pi_frame (PrhImg := prh_img_B) F_pj_parse) with
  | Some w => w | None => 0 end.
Definition x_cw (C : crsC_B) (W : world SEGS) (mem : word -> option byte) (sp : Z) : list (list Z) :=
  map (fun r => prh_trace (pc_free_ra0 (as_code B)) r [cb_data C + cSize_B C])
    (prh_free_sites (PI := prh_img_B) F_parse_items) ++
  map (fun r => prh_trace (pc_free_ra0 (as_code B)) r [x_slotw W mem sp])
    (prh_free_sites (PI := prh_img_B) F_parse_string).

(* it meets the text's pinned cursor premise at the call (pn_cw_pj's route; the kit's repaired prh_cw_pj: one pinned arm
   per cursor function, no code-word disjunct) *)
Lemma x_cw_pj : forall C (W : world SEGS) mem (regs : bvmap 5 word),
  prh_cw_pj (PI := prh_img_B) (PA := PA) B (x_cw C W mem (spZ regs)) W mem regs (cb_data C) (cSize_B C).
Proof.
intros C W mem regs. split.
- intros r Hr. apply in_or_app. left. apply in_map_iff. exists r. split; [reflexivity | exact Hr].
- intros r Hr w0 Hw. apply in_or_app. right. apply in_map_iff. exists r. split; [|exact Hr].
  unfold x_slotw. rewrite Hw. reflexivity.
Qed.

(* one trace per cursor function: |CW| = prh_wk F_check_reject_clean_starved = 2 *)
Lemma x_cw_len : forall C W mem sp, length (x_cw C W mem sp) = prh_wk F_check_reject_clean_starved.
Proof. intros C W mem sp. unfold x_cw. rewrite length_app, !length_map. vm_compute. reflexivity. Qed.

(* THE ROOM AT THE CALL (the text's `wild_room U CW 0 (st_depot S)`): the text's own room at entry
   (wild_room U [] (prh_wk F) at the entry depot), carried to the call over a journal that stored no wild trace
   (no budget spent before X1: cb_ws C = []), then paid out to CW (YCbqGwild.wild_room_set) *)
Lemma x_room_at_call : forall CTX0 C ly3 S3 Hp3 W3 mem3 md3 k (W : world SEGS) mem sp,
  PREp CTX0 C -> cb_ws C = [] -> crs_dpok_B B C -> JJ C ly3 S3 Hp3 W3 mem3 md3 k ->
  YCbqGwild.wild_room (as_universe B) (x_cw C W mem sp) 0 (st_depot S3).
Proof.
intros CTX0 C ly3 S3 Hp3 W3 mem3 md3 k W mem sp HP Hws (_ & Hdp) HJ.
destruct (crs_pre_room_B B ARx CTX0 C HP) as (HR & _).
unfold crs_J_B in HJ. pose proof HJ as Hw. apply ajx_wild in Hw.
cbn [st_depot YG00.set_depot] in Hw.
rewrite Hws, app_nil_r in Hdp. rewrite app_nil_r in Hw.
apply YCbqGwild.wild_room_set. rewrite x_cw_len, Nat.add_0_r.
pose proof (YCbqGwild.wild_room_step _ _ _ _ (st_depot S3) [] HR ltac:(rewrite app_nil_r; exact (incl_tran Hw Hdp))
  ltac:(unfold YCbqGwild.wfresh; cbn; lia)) as Hst.
unfold YCbqGwild.wfresh in Hst. cbn [YCbqGwild.wild_fresh List.filter length] in Hst. rewrite Nat.sub_0_r in Hst.
exact Hst.
Qed.

(* the BUDGETED call rule at window 0 at the re-hiding relation WR (YCbqGwild.aj_call_xWFbR): pj_parse's text posts
   fpostWFb P, which is at WR, so the walk's journal comes back at WR, at the callee's budget WS1 *)
Lemma x_callWFbR : forall fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 (o : Z) raw
  ch1 (P : list (list Z) -> Prop)
  (K : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  AJR WR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre_x SEGS B ARx STK1 lyc Sc Hpc W regsc memc mdc ch1 ->
   YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
     (fpostWFb (fx := fxk) (PI := prh_img_B) (PA := PA) B ARx SK P STK1 0 FP1 regsc lyc Sc Hpc W memc mdc K)) ->
  fp_sub_x B STK sp0 FP FP1 ly S own lyc Sc ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W (mkCfg (@YK11.mkst fxk regsc (Z_to_bv 64 pc) memc (YK11.seg_rom SEGS)) mdc)
    (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 Hp2 regs2 mem2 md2 k1 WS1,
       c2 = mkCfg (@YK11.mkst fx' regs2 raw mem2 (YK11.seg_rom SEGS)) md2 /\
       frm_zero (@YK11.fp_csr fx') /\ fregs_kept_x fxk fx' /\ P WS1 /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx WR STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + k1)
         WS1 /\
       ajournal_xwR (SK := SK) SEGS B prh_pst ARx WR STK1 (sp0 + o) FP1 lyc Sc Hpc W memc mdc [] ly2 S2 Hp2 W2 mem2
         md2 k1 WS1 /\
       aregs_preserved regsc regs2 /\ K ly2 S2 Hp2 W2 regs2 mem2 md2).
Proof.
intros fxk W regsc memc pc STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k STK1 FP1 o raw ch1 P K
  HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply (YA0nH.SRrG_mono SEGS WR).
{ eapply (YCbqGwild.aj_call_xWFbR (fx := fxk) (SK := SK) SEGS B prh_pst ARx LAWS pa_segs_low WR
    (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf) W regsc memc pc STK sp0
    FP ly S Hp W0 mem md own lyc Sc Hpc mdc k [] STK1 0 FP1 o raw ch1 P K HJ Hsp Hal Hneg Hstk1 Hbud
    ltac:(lia) ltac:(reflexivity) ltac:(lia) Hgp Htp Hra Hraw Hra4 Hch); [|exact HF].
  intros HA _. exact (Hcallee HA). }
cbv beta. intros W2 c2 _ (fx' & ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & WS1 & Hc & HFZ & HFK & HPW & HJ1 & HJ2 & _ &
  HP & HK).
exists fx', ly2, S2, Hp2, regs2, mem2, md2, k1, WS1. split; [exact Hc|]. split; [exact HFZ|]. split; [exact HFK|].
split; [exact HPW|]. split; [exact HJ1|]. split; [rewrite !Z.add_0_r in HJ2; exact HJ2|].
split; [exact HP | exact HK].
Qed.

(* the rebased context reads C's fields: turn its projections in a lemma's outputs and goals back into C's *)
Local Ltac xrbn Cr C :=
  try change (cb_regs Cr) with (cb_regs C) in *; try change (cb_fpos Cr) with (cb_fpos C) in *;
  try change (cb_ly Cr) with (cb_ly C) in *; try change (cb_S Cr) with (cb_S C) in *;
  try change (cF_B Cr) with (cF_B C) in *; try change (cOut_B Cr) with (cOut_B C) in *;
  try change (cSize_B Cr) with (cSize_B C) in *; try change (cb_Lam Cr) with (cb_Lam C) in *;
  try change (cb_peak Cr) with (cb_peak C) in *; try change (cb_cnt Cr) with (cb_cnt C) in *;
  try change (cb_ran Cr) with (cb_ran C) in *; try change (cb_most Cr) with (cb_most C) in *;
  try change (cb_data Cr) with (cb_data C) in *; try change (cb_tb Cr) with (cb_tb C) in *;
  try change (cb_took Cr) with (cb_took C) in *; try change (cb_doc Cr) with (cb_doc C) in *;
  try change (cb_t Cr) with (cb_t C) in *; try change (cb_D Cr) with (cb_D C) in *;
  try change (cb_rp_x Cr) with (cb_rp_x C) in *; try change (cb_rp_os Cr) with (cb_rp_os C) in *;
  try change (cb_rp_i Cr) with (cb_rp_i C) in *; try change (cb_rp_H0 Cr) with (cb_rp_H0 C) in *;
  try change (crs_evs_at_W1_B Cr) with (crs_evs_at_W1_B C) in *;
  try change (crs_cnt_R_B Cr) with (crs_cnt_R_B C) in *; try change (crs_pos_B Cr) with (crs_pos_B C) in *;
  try change (crs_perm_B B Cr) with (crs_perm_B B C) in *; try change (XK Cr) with (XK C) in *.

(* THE GUARDED CONJUNCT OF tpj_parse_specX's POST AT X1 (the A' twin crs_guard_x1, written against its blob 20030bb17091,
   the instance swapped): the conjunct's run, consumer window and window premises at the starved
   reading's call come from crs_pre_B and X1's boundary position alone (crs_evs_at_X1_B = []), so X1 gets
   prh_granted without x_agree: no circularity *)
Lemma x_guard_B : forall CTX0 (C : crsC_B) (S : astate) (hist0 : list YG00.chunk) (ok : list bool)
  (tr : list PjGrammar.ev),
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
     PRH_Base.prh_run_at sm x os i
       (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C)
          (PresetReqAt.okk (Z.to_nat ((cb_cnt C + ck_pick (cb_tb C) (cb_took C)) - cb_cnt C)))) ->
     PRH_Base.prh_cons_from sm x os i
       (length (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C)
          (PresetReqAt.okk (Z.to_nat ((cb_cnt C + ck_pick (cb_tb C) (cb_took C)) - cb_cnt C))))) ->
     cb_cnt C <= cb_cnt C + ck_pick (cb_tb C) (cb_took C) <
       cb_cnt C + Z.of_nat (PjGrammar.ncalls ReaderRes.jr_strtod (cb_tb C)) ->
     PRH_Base.prh_granted ok (cb_cnt C) (cb_cnt C + ck_pick (cb_tb C) (cb_took C)) (PjGrammar.calls tr)) ->
  PREp CTX0 C -> cb_took C <> 0 ->
  PresetRoomPos.iface_room_pos ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) hist0 S ->
  PRH_Base.prh_granted ok (cb_cnt C) (cb_cnt C + ck_pick (cb_tb C) (cb_took C)) (PjGrammar.calls tr).
Proof.
intros CTX0 C S hist0 ok tr G HP Htk Hpos.
pose proof HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Htk0 & _).
set (kp := ck_pick (cb_tb C) (cb_took C)) in *.
assert (Hkp : 0 <= kp < cb_took C) by (apply crs_pick_lt; lia).
assert (Ekp : Z.to_nat (cb_cnt C + kp - cb_cnt C) = PresetReqAt.pick (cb_tb C) (Z.to_nat (cb_took C))).
{ replace (cb_cnt C + kp - cb_cnt C) with kp by lia. unfold kp.
  rewrite <- (Z2Nat.id (cb_took C)) at 1 by lia.
  rewrite (crs_pick_bridge_B (cb_tb C) (Z.to_nat (cb_took C))) by lia. apply Nat2Z.id. }
rewrite Ekp in G.
(* the model's starved reading, split off the text's run list (crs_evs_B = ck_crcs_evs) *)
assert (Es : crs_evs_B C =
  PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) (PresetReqAt.okk (PresetReqAt.pick (cb_tb C) (Z.to_nat (cb_took C))))
  ++ (if cb_doc C =? 0 then [] else PresetReqAt.starved_writes (cb_tb C) (cb_t C))).
{ unfold crs_evs_B, ck_crcs_evs, PresetReqAt.starved_parse.
  destruct (Z.to_nat (cb_took C)) eqn:En; [lia | reflexivity]. }
apply (G ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) hist0 Hpos).
- (* the run premise: crs_pre_B's prh_run_at, its first part *)
  pose proof (crs_run_of_pre_B B ARx CTX0 C HP) as Hr. rewrite Es in Hr.
  exact (PRH_FnPj.prhPj_parse_evs_supply _ _ _ _ _ _ _ Hr).
- (* the consumer window: crs_pre_B's prh_cons_from, its first part (crs_cons_split_B at an empty prefix) *)
  assert (E3 : crs_evs_B C = [] ++ PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C)
    (PresetReqAt.okk (PresetReqAt.pick (cb_tb C) (Z.to_nat (cb_took C)))) ++
    (if cb_doc C =? 0 then [] else PresetReqAt.starved_writes (cb_tb C) (cb_t C))) by exact Es.
  pose proof (crs_cons_split_B B ARx CTX0 C _ _ _ E3 HP) as Hc. cbn [length] in Hc. rewrite Nat.add_0_r in Hc.
  exact Hc.
- (* the injected index lies inside the reading's window: pick < took <= ck_ncalls *)
  unfold ck_ncalls in Htk0. lia.
Qed.

(* ==== CR-X1: the closing lemma, at the kit's crs_from_X1_B. HT_pj_parse is the text PRH_FnPj.tpj_parse_specX itself,
   with its guarded THE OUTCOME OF AN INJECTED READING, whose guard X1 discharges from crs_pre_B (x_guard_B), at every
   cursor set; X1 takes it at this call's x_cw. Its post is BUDGETED at x_cw and at the re-hiding relation WR, so the
   walk goes on at the REBASED context and at WR: the continuations are asked at crs_with_dp_B C d ws for every d ws.
   The stretch before the call is stepped plainly (YGcfRhLift.ra_rh_of_SRr at entry); every call after it is bound at
   WR (YSRrG.SRr'_bind). HI_hull: the run's two meter caps within cp's, so the run's position pays pj_parse's hull
   budget (HHULL) ==== *)
Lemma crs_seg_X1_B : forall CTX0 C,
  (forall fx' : YK11.FPState, tfuzz_alloc_fail_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall fx' : YK11.FPState, tcheck_reject_clean_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK) ->
  (forall (fx' : YK11.FPState) (CW : list (list Z)),
     PRH_FnPj.tpj_parse_specX (fx := fx') (PI := prh_img_B) (RL := RL) (PA := PA) B ARx SK CTX0 CW) ->
  (PresetSecTotal.SEC_N_CAP <= @YGcfNames.cf_kmax cp /\ PresetSecTotal.SEC_T_CAP <= @YGcfNames.cf_T_max cp) ->
  CrsKeep_B B ARx ->
  (forall d ws, @crs_from_R_B fx rc ci cp RL SK B ARx CTX0 (crs_with_dp_B C d ws)) ->
  (forall d ws, @crs_from_W1_B fx rc ci cp RL SK B ARx CTX0 (crs_with_dp_B C d ws)) ->
  crs_from_X1_B (fx := fx) (rc := rc) B ARx CTX0 C.
Proof.
intros CTX0 C HT_fuzz_alloc_fail HT_check_reject_clean HT_pj_parse HI_hull HK KcR KcW1.
unfold crs_from_X1_B.
intros fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 Htk Hws HB HR HL _ _.
apply YGcfRhLift.ra_rh_of_SRr.
pose proof h_pc0 as HPC.
pose proof h_base as (HB0 & HB1).
assert (EBASE : BASE = 530124) by (vm_compute; reflexivity).
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (@cf_head_nonneg cp) as Hh0.
assert (E128 : fs_frame_bytes CRS_CID_B = 128) by (vm_compute; reflexivity).
assert (ESTK : @STK_check_reject_clean_starved prh_img_B = 27312) by (vm_compute; reflexivity).
assert (ESTf : @STK_fuzz_alloc_fail prh_img_B = 0) by (vm_compute; reflexivity).
assert (ESTp : @STK_pj_parse prh_img_B = 27168) by (vm_compute; reflexivity).
assert (ESTc : @STK_check_reject_clean prh_img_B = 8208) by (vm_compute; reflexivity).
pose proof HB as (HPRE & Hfz & _ & _ & HFR3 & _ & _ & _ & _ & _ & _ & Hsp2a & Hsp2b & Hsp2c & HDPk).
pose proof (h_pre_facts B ARx CTX0 C HPRE) as (Hsz & Hd0 & Hd62 & Htk2 & Hran0).
pose proof (x_pre_facts CTX0 C HPRE)
  as (_ & _ & HU & _ & _ & _ & _ & _ & Htk0 & _ & Hcnt0 & _ & HLIVE0 & HRQ0 & HFRS0).
unfold cSize_B in Hsz, Hd62, Htk2.
assert (EFR : CRS_FRAME_B = 144) by (rewrite crs_frame_is_pi_B; reflexivity). rewrite EFR in Hsp2a.
destruct HL as ((HL3 & _ & _ & _ & _ & Hroom3 & Hpos3) & HpL3 & Hpb3).
rewrite Hran0 in HL3, Hpos3.
destruct (Hpos3 eq_refl) as (hist0 & Hpos0).
unfold crs_evs_at_X1_B in Hpos0. cbn [length] in Hpos0. rewrite Nat.add_0_r in Hpos0.
set (kp := ck_pick (cb_tb C) (cb_took C)).
assert (Hkp : 0 <= kp < cb_took C) by (apply crs_pick_lt; lia).
(* the reading's grant list in the model, and its events: the kit's starved_parse is parse_evs at that list (took <> 0),
   at the strtod oracle pj_parse's text is stated at (convertible: the text's keyed model) *)
set (g_sp := PresetReqAt.okk (PresetReqAt.pick (cb_tb C) (Z.to_nat (cb_took C)))).
assert (Eg : g_sp = PresetReqAt.okk (Z.to_nat kp)) by (unfold g_sp, kp; rewrite x_pick by lia; reflexivity).
assert (Es : crs_ev_sp_B C = PresetReqAt.parse_evs prh_jr_strtod (cb_tb C) g_sp).
{ unfold g_sp. change prh_jr_strtod with ReaderRes.jr_strtod. unfold crs_ev_sp_B, PresetReqAt.starved_parse.
  destruct (Z.to_nat (cb_took C)) as [|n] eqn:En; [lia | reflexivity]. }
assert (HRUN : prh_run_at ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C)
                 (PresetReqAt.parse_evs prh_jr_strtod (cb_tb C) g_sp)).
{ pose proof (crs_run_of_pre_B B ARx CTX0 C HPRE) as Hr. unfold crs_evs_B, ck_crcs_evs in Hr.
  change (PresetReqAt.starved_parse ReaderRes.jr_strtod (cb_tb C) (Z.to_nat (cb_took C))) with (crs_ev_sp_B C) in Hr.
  rewrite Es in Hr. eapply PRH_FnPj.prhPj_parse_evs_supply. exact Hr. }
pose proof (djb_hash_range (cb_tb C)) as Hh. fold (cHash_B C) in Hh.
pose proof (x_frame_facts CTX0 C fxk ly3 S3 Hp3 W3 regs3 mem3 md3 k sp2 HB)
  as (_ & _ & H32 & Happ & H4096 & Hceil & _ & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
(* the registers at the boundary *)
assert (HK0 : crs_regsat_B regs3 (crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C)).
{ apply (h_regsat_incl regs3 _ _ HR). intros p Hp'. rewrite !in_app_iff in *. tauto. }
assert (G26 : getr regs3 26%bv = w64 (cF_B C))
  by (apply (h_regsat_get _ _ _ _ HR); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hin).
assert (G23 : getr regs3 23%bv = w64 (cb_took C))
  by (apply (h_regsat_get _ _ _ _ HR); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hin).
assert (G11 : getr regs3 11%bv = w64 (cHash_B C))
  by (apply (h_regsat_get _ _ _ _ HR); unfold crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hin).
(* ---- +416 addi s8, s10, 32 ---- *)
change (BASE + CRS_PC_X1_B) with (BASE + (CRS_PC0_B + 416)).
hfd (CRS_PC0_B + 416) Hl Hd.
eapply (h_addi W3 fxk regs3 mem3 md3 _ (CRS_PC0_B + 416) (CRS_PC0_B + 420) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G26, hw_addi by lia. xb HB.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ _) _ => assert (HRk : crs_regsat_B r (XK C sp2)) end.
{ replace (XK C sp2) with ((crs_rbase_B C sp2 ++ crs_rsh_B C ++ crs_rargs_B C ++ crs_rlive_B C) ++ [(24%bv, cOut_B C)])
    by (unfold XK; rewrite <- !app_assoc; reflexivity).
  apply h_regsat_app.
  - apply h_regsat_upd; [unfold crs_rbase_B, crs_rsh_B, crs_rargs_B, crs_rlive_B; hnot | exact HK0].
  - apply Forall_cons; [cbn [fst snd]; hgetr; unfold cOut_B, CRS_OFF_DOC_B; reflexivity | apply Forall_nil]. }
(* ---- +420 remu a0, a1, s7: a0 = h % took = pick ---- *)
clear Hl Hd. hfd (CRS_PC0_B + 420) Hl Hd.
eapply (x_remu W3 fxk _ mem3 _ _ (CRS_PC0_B + 420) (CRS_PC0_B + 424) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G11, G23, x_remu_word by lia.
replace (cHash_B C mod cb_took C) with kp by (unfold kp, cHash_B; rewrite crs_pick_eq by lia; reflexivity).
xb HB. xr HRk.
(* ---- +424 jal fuzz_alloc_fail (pick) ---- *)
clear Hl Hd.
assert (Hl : HSLOT (CRS_PC0_B + 424) = Some (PCall YPsym.AS_fuzz_alloc_fail 1%bv)) by (vm_compute; reflexivity).
eapply (x_hs_call W3 fxk _ mem3 _ _ (CRS_PC0_B + 424) (CRS_PC0_B + 428) YPsym.AS_fuzz_alloc_fail Hl); [lia | reflexivity |].
intros ?. xb HB. xr HRk. clear Hl.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ ?m) _ => set (rC1 := r) in *; set (mC1 := m) in * end.
assert (Q1 : getr rC1 1%bv = w64 (BASE + (CRS_PC0_B + 428))) by (unfold rC1; hgetr; reflexivity).
assert (Q10 : getr rC1 10%bv = w64 kp) by (unfold rC1; hgetr; reflexivity).
destruct (x_callsite CTX0 C fxk ly3 S3 Hp3 W3 rC1 mem3 mC1 k sp2 (CRS_PC0_B + 428) HB HRk Q1 ltac:(lia)
  ltac:(vm_compute; reflexivity)) as (Hsp & Hs0 & Q3 & Q4 & Hrok & Hra4 & Hraz & Hal & Ho & ch1 & Hch).
pose proof HB as (_ & _ & _ & HJc & _). unfold crs_J_B in HJc.
unfold crs_cfg_B, w64.
eapply SRr_bind.
{ eapply (x_call fxk W3 rC1 mem3 (SIGMA YPsym.AS_fuzz_alloc_fail) STK_check_reject_clean_starved (spZ (cb_regs C)) []
    (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly3 S3 Hp3 mC1 k
    (STK_fuzz_alloc_fail (PI := prh_img_B)) [] (sp2 - spZ (cb_regs C)) (w64 (BASE + (CRS_PC0_B + 428))) ch1 _ HJc).
  - rewrite Hsp. lia.
  - exact Hal.
  - lia.
  - rewrite ESTf. lia.
  - rewrite ESTf, ESTK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - exact Hrok.
  - exact Hra4.
  - exact Hch.
  - intros HAFN1.
    exact (HT_fuzz_alloc_fail fxk ly3 S3 Hp3 W3 rC1 mem3 mC1 ch1 (cb_Lam C) (cb_peak C) (cb_cnt C) SIZE_MAXZ 0 kp
      (cb_most C) 0 (x_callee_fpre CTX0 C fxk ly3 S3 Hp3 W3 rC1 mem3 mC1 k sp2 _ rC1 mC1 ch1 HB Hsp Hraz HAFN1) HL3 Q10
      ltac:(lia)).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W4 c4 _ (ly4 & S4 & Hp4 & regs4 & mem4 & md4 & k1 & -> & HJc4 & HJ1 & HP1 & HQ1).
cbv beta delta [fQmn] in HQ1.
destruct HQ1 as ((Hrm1 & -> & -> & Eab1 & HL4) & HMN4).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ1 by lia.
assert (Efa : (if kp <? SIZE_MAXZ - cb_cnt C then cb_cnt C + kp else SIZE_MAXZ) = cb_cnt C + kp)
  by (rewrite (proj2 (Z.ltb_lt _ _)) by (unfold SIZE_MAXZ; lia); reflexivity).
rewrite Efa in HL4.
pose proof (x_base_call CTX0 C fxk ly3 S3 Hp3 W3 rC1 mem3 mC1 k sp2 fxk ly4 S3 Hp3 W4 regs4 mem4 md4 (k + k1)
  (STK_fuzz_alloc_fail (PI := prh_img_B)) [] k1 HB HJc4 HJ1 ltac:(intros a (r & Hr & _); destruct Hr) sink_closed_nil
  HMN4 (x_ap3 _ _ HP1) (x_ap4 _ _ HP1) Hfz ltac:(intros r _; reflexivity)) as HB4.
pose proof (x_regsat_ap rC1 regs4 _ HP1 (x_XK_cs C sp2) HRk) as HRk4.
clear HB HJc HJc4 HJ1 HRk Hch Hsp Hs0 Q1 Q3 Q4 Q10 Hrok Hra4 Hraz Hal Ho.
change (SRr SEGS W4 (crs_cfg_B fxk (BASE + (CRS_PC0_B + 428)) regs4 mem4 md4) (fun W' c' =>
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W' c' (crs_post_B (fx := fx) (rc := rc) B ARx C))).
(* ---- +428 .. +436: a0 = data, a1 = size, a2 = s8 ---- *)
assert (G21 : getr regs4 21%bv = w64 (cb_data C)) by xg HRk4.
assert (G20 : getr regs4 20%bv = w64 (cSize_B C)) by xg HRk4.
assert (G24 : getr regs4 24%bv = w64 (cOut_B C)) by xg HRk4.
hfd (CRS_PC0_B + 428) Hl Hd.
eapply (h_addi W4 fxk regs4 mem4 md4 _ (CRS_PC0_B + 428) (CRS_PC0_B + 432) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G21. xb HB4. xr HRk4.
clear Hl Hd. hfd (CRS_PC0_B + 432) Hl Hd.
eapply (h_addi W4 fxk _ mem4 _ _ (CRS_PC0_B + 432) (CRS_PC0_B + 436) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G20. xb HB4. xr HRk4.
clear Hl Hd. hfd (CRS_PC0_B + 436) Hl Hd.
eapply (h_addi W4 fxk _ mem4 _ _ (CRS_PC0_B + 436) (CRS_PC0_B + 440) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite G24. xb HB4. xr HRk4.
(* ---- +440 jal pj_parse (data, size, s8): the reading, refused at its pick-th call ---- *)
clear Hl Hd.
assert (Hl : HSLOT (CRS_PC0_B + 440) = Some (PCall YPsym.AS_pj_parse 1%bv)) by (vm_compute; reflexivity).
eapply (x_hs_call W4 fxk _ mem4 _ _ (CRS_PC0_B + 440) (CRS_PC0_B + 444) YPsym.AS_pj_parse Hl); [lia | reflexivity |].
intros ?. xb HB4. xr HRk4. clear Hl.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ ?m) _ => set (rC2 := r) in *; set (mC2 := m) in * end.
assert (P1 : getr rC2 1%bv = w64 (BASE + (CRS_PC0_B + 444))) by (unfold rC2; hgetr; reflexivity).
assert (P10 : getr rC2 10%bv = w64 (cb_data C)) by (unfold rC2; hgetr; reflexivity).
assert (P11 : getr rC2 11%bv = w64 (cSize_B C)) by (unfold rC2; hgetr; reflexivity).
assert (P12 : getr rC2 12%bv = w64 (cOut_B C)) by (unfold rC2; hgetr; reflexivity).
destruct (x_callsite CTX0 C fxk ly4 S3 Hp3 W4 rC2 mem4 mC2 (k + k1) sp2 (CRS_PC0_B + 444) HB4 HRk4 P1 ltac:(lia)
  ltac:(vm_compute; reflexivity)) as (Hsp & Hs0 & P3 & P4 & Hrok & Hra4 & Hraz & Hal & Ho & ch2 & Hch).
assert (Hperm4 : crs_perm_B B C ly4 S3 (cb_Lam C)) by (split; [apply Permutation_refl | rewrite Eab1; exact Hpb3]).
destruct (x_pjp_site HK CTX0 C fxk ly4 S3 Hp3 W4 rC2 mem4 mC2 (k + k1) sp2 (cb_Lam C) (cb_peak C) (cb_cnt C)
  (cb_cnt C + kp) 0 (cb_most C) 0 HB4 HL4 Hperm4 Hsp) as (Hwin & Hslot & Hout & HLamd & Hapart & HSRC4 & Hhome4).
pose proof HB4 as (_ & _ & _ & HJc & HFR4 & _ & _ & _ & HMN & _ & _ & _ & _ & _ & HDP4).
unfold crs_J_B in HJc.
pose proof (x_frame_facts CTX0 C fxk ly4 S3 Hp3 W4 rC2 mem4 mC2 (k + k1) sp2 HB4) as (EF4 & _).
assert (Hmr : Z.of_nat (PjRoundTrip.maxrun (cb_tb C)) < 2 ^ 30).
{ pose proof (PjRoundTrip.G12_1 (cb_tb C)) as Gm. lia. }
assert (HRQ : PRH_FnPj.RQ_pj_parse (cb_tb C) + cf_head < cf_malloc_max).
{ unfold RQ_crcs, zmaxl in HRQ0. cbn [fold_right] in HRQ0. lia. }
assert (HLV : blocks_bytes S3 + PRH_FnPj.LIVE_pj_parse (cb_tb C) <= LIVE_MAX).
{ rewrite (blocks_bytes_bsum B ly3 S3), (x_bsum_perm _ _ Hpb3), <- (blocks_bytes_bsum B (cb_ly C) (cb_S C)).
  unfold LIVE_check_reject_clean_starved, PRH_FnWriter.LIVE_pj_write in HLIVE0.
  pose proof (WriterRet.newcap_ge 0 (Z.of_nat (length (WriterValue.wdoc (cb_t C) true)) + 1) ltac:(lia)) as N1.
  pose proof (WriterRet.newcap_ge 0 (Z.of_nat (length (WriterValue.wdoc (cb_t C) false)) + 1) ltac:(lia)) as N2.
  lia. }
assert (HFRm : Z.of_nat (length (frames S3)) + Z.of_nat DOC_D <= fs_frames 0).
{ destruct HFR3 as (Hfr3 & _). rewrite Hfr3. cbn [length]. rewrite Nat2Z.inj_succ.
  unfold ck_FRAMES_CAP, FR_check_reject_clean_starved, FR_pj_parse in HFRS0.
  assert (ED : Z.of_nat DOC_D <= 64) by (unfold Z.le; vm_compute; discriminate).
  assert (EF0 : fs_frames 0 = 16384) by (vm_compute; reflexivity). lia. }
(* ---- THE ENTRY FACTS THE KIT'S CUT ADDS TO pj_parse's TEXT (PRH_FnPj.v:592-656): the cursor set and its room (B'
   CW wild, x_cw), the strict ceiling of the text (x_text_ceil), the requests within g_most (crs_pre_B), the two room
   counts at the CALL state (crs_pre_B's at entry, the live set a permutation of the entry's: x_live_perm and
   PresetRun.pkR_mono, A' CrsSeg_X1.v:1404-1415's route) ---- *)
set (CWx := x_cw C W4 mem4 (spZ rC2)).
assert (HCW : prh_cw_pj (PI := prh_img_B) (PA := PA) B CWx W4 mem4 rC2 (cb_data C) (cSize_B C)) by exact (x_cw_pj C W4 mem4 rC2).
assert (Hwr : YCbqGwild.wild_room (as_universe B) CWx 0 (st_depot S3))
  by exact (x_room_at_call CTX0 C ly4 S3 Hp3 W4 mem4 mC2 (k + k1) W4 mem4 (spZ rC2) HPRE Hws HDP4 HJc).
pose proof (x_text_ceil CTX0 C HPRE) as Hcl.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRQm & _).
destruct (crs_pre_room_B B ARx CTX0 C HPRE) as (_ & Hsec0 & Hc240).
assert (Hlp : PresetReqAt.subm (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
                (PresetRoom.rs_live (YGcfRoom.room_of_cf (cb_S C))))
  by (apply PresetReqAt.subm_perm; apply Permutation_sym; exact (x_live_perm _ _ _ _ Hpb3)).
assert (Hsec : Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ pose proof (PresetRun.pkR_mono YGcfRoomLive.rl_sec_req (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])
    _ _ Hlp). lia. }
assert (Hc24 : Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass)
    (PresetRoom.rs_live (YGcfRoom.room_of_cf S3))
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ pose proof (PresetRun.pkR_mono (PresetRoom.in_cls YG00.kBatchClass)
    (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) []) _ _ Hlp). lia. }
(* THE HULL BUDGET of the reading (the text's last premise): the run's position at S3 and its at most 4 calls (the
   kit's crs_pre_los_B) bound both meters, a reading of at most MAXB bytes is at most one call's counts
   (PresetHullPay.hull_nt_parse), and the run's caps are within cp's (HI_hull) *)
assert (HHULL : @PresetHullBudget.hull_budget cp S3 (PresetReqAt.parse_evs ReaderRes.jr_strtod (cb_tb C) [])).
{ pose proof (crs_pre_los_B B ARx CTX0 C HPRE) as Hlos.
  destruct (PresetHullPay.hull_nt_parse ReaderRes.jr_strtod (cb_tb C) []
    ltac:(unfold PresetReqAt.MAXB; lia)) as [Hn Ht].
  pose proof Hpos0 as (_ & _ & _ & _ & _ & HC).
  destruct (HC YGcfSecsStep.secs_steps_cf_holds) as [N T]. rewrite PresetRoomPos.rp_nsec_layer in N.
  pose proof (PresetSecTotalRun.nsec_run_prefix ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) Hlos) as Np.
  pose proof (PresetSecTotalRun.tsec_run_prefix ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) Hlos) as Tp.
  rewrite PresetSecTotal.NCALL_value in Hn, Np. rewrite PresetSecTotal.TCALL_value in Ht, Tp.
  unfold PresetRoomPos.rp_NB in N. unfold PresetRoomPos.rp_TB in T. change (2 ^ 30) with 1073741824 in T.
  destruct HI_hull as [HCN HCT]. unfold PresetSecTotal.SEC_N_CAP, PresetSecTotal.SEC_T_CAP in HCN, HCT.
  change (2 ^ 17) with 131072 in HCN. change (2 ^ 36) with 68719476736 in HCT.
  unfold PresetHullBudget.hull_budget. split; lia. }
(* the call is bound at WR: the walk's base and journal there (wle is inside WR) *)
pose proof (crs_baseR_B_mono B ARx (@wle SEGS) WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) CTX0 C fxk ly4 S3 Hp3
  W4 rC2 mem4 mC2 (k + k1) sp2 HB4) as HB4R.
pose proof HB4R as (_ & _ & _ & HJcR & _). unfold crs_JR_B in HJcR.
apply SRr_ret. cbv beta.
unfold crs_cfg_B, w64.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (x_callWFbR fxk W4 rC2 mem4 (SIGMA YPsym.AS_pj_parse) STK_check_reject_clean_starved (spZ (cb_regs C)) []
    (cb_ly C) (YG00.set_depot (cb_dp C) (cb_S C)) (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly4 S3 Hp3 mC2 (k + k1)
    (STK_pj_parse (PI := prh_img_B)) [(cOut_B C, cOut_B C + 56)] (sp2 - spZ (cb_regs C)) (w64 (BASE + (CRS_PC0_B + 444)))
    ch2 (YCbqGwild.wbudget CWx 0) _ HJcR).
  - rewrite Hsp. lia.
  - exact Hal.
  - lia.
  - rewrite ESTp. lia.
  - rewrite ESTp, ESTK. lia.
  - exact P3.
  - exact P4.
  - exact P1.
  - exact Hrok.
  - exact Hra4.
  - exact Hch.
  - intros HAFN2.
    exact (HT_pj_parse fxk CWx (cb_most C) 0
      ly4 S3 Hp3 W4 rC2 mem4 mC2 ch2 0 (cb_data C) (cSize_B C) (cOut_B C) (cb_tb C) (cb_Lam C) (cb_peak C) (cb_cnt C)
      (cb_cnt C + kp) 0
      (x_callee_fpre CTX0 C fxk ly4 S3 Hp3 W4 rC2 mem4 mC2 (k + k1) sp2 _ rC2 mC2 ch2 HB4 Hsp Hraz HAFN2)
      HMN HU HCW Hwr Hroom3 Hfz P10 P11 P12 eq_refl HSRC4 Hhome4 Hcl Hmr Hwin Hslot Hout HLamd Hapart HL4
      ltac:(unfold cSize_B; lia) HRQ HRQm HLV HFRm Hsec Hc24 HHULL).
  - intros a (r & Hr & Ha). destruct Hr as [<- | []]. cbn [fst snd] in Ha.
    right; right; left. exists (CRS_CID_B, cb_fpos C). split; [left; reflexivity|].
    unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF4, E128. unfold cOut_B, CRS_OFF_DOC_B in Ha. lia. }
cbv beta. intros W5 c5 _ (fx5 & ly5 & S5 & Hp5 & regs5 & mem5 & md5 & k2 & WS1 & -> & Hfz5 & Hfk5 & HPW & HJc5w & HJ2
  & HP2 & HQ2).
cbv beta delta [fQmn] in HQ2.
destruct HQ2 as ((Hroom5 & _ & ok & res & tr & Lam5 & peak5 & cnt5 & fail5 & ran5 & Hrun & Hoks & Ecnt & _ & Epeak &
  _ & _ & _ & HL5 & Hex5 & _ & HG & Hres) & HMN5).
(* THE GUARD (the text's guarded THE OUTCOME OF AN INJECTED READING): discharged at X1's boundary position from
   crs_pre_B *)
pose proof (x_guard_B CTX0 C S3 hist0 ok tr HG HPRE Htk Hpos0) as Hgr.
change (ck_pick (cb_tb C) (cb_took C)) with kp in Hgr.
assert (Hj : (Z.to_nat kp < PjGrammar.ncalls prh_jr_strtod (cb_tb C))%nat).
{ unfold ck_ncalls in Htk0. change prh_jr_strtod with ReaderRes.jr_strtod. lia. }
pose proof (Z2Nat.id kp ltac:(lia)) as EZ.
rewrite <- EZ in Hoks, Hgr.
(* the reading refused nothing but the injected failure: the shared model's crs_read_inj_granted *)
destruct (crs_read_inj_granted (cb_tb C) ok res tr (cb_cnt C) (Z.to_nat kp) _ _ _ _ Hrun Hoks Hgr Hj)
  as (-> & Hcs & Hran5e).
assert (Hc1 : (1 <= PjGrammar.calls tr <= S (Z.to_nat kp))%nat) by lia.
assert (Hc2 : ran5 = 0 -> PjGrammar.calls tr = S (Z.to_nat kp)) by (intros _; exact Hcs).
pose proof Hoks as Hoks0. pose proof Hgr as Hgr0.
rewrite EZ in Hoks, Hgr.
destruct Hres as (R10 & HpL5 & Hpb5 & HZ5).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ2 by lia.
assert (HposO : 0 < fst (cOut_B C, cOut_B C + 56)) by (cbn [fst]; unfold cOut_B, CRS_OFF_DOC_B; lia).
(* ---- THE REBASE (the kit's record comment): the walk's journal at budget WS1 is one at the EMPTY budget from the
   entry with its depot moved to st_depot S5 (YCbqGwild.ajournal_xw_rebaseR, at WR); WS1 is inside CWx (wbudget CWx 0),
   so the moved depot's wild part is covered from the entry's by CWx, whose |CWx| = 2 is the text's wild budget ---- *)
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARx WR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc5w)
  as HJc5.
assert (HJc5' : JJR WR (crs_with_dp_B C (st_depot S5) CWx) ly5 S5 Hp5 W5 mem5 md5 (k + k1 + k2)) by exact HJc5.
assert (HDP5 : crs_dpok_B B (crs_with_dp_B C (st_depot S5) CWx)).
{ assert (Ewf : forall l : list (list Z), YCbqGwild.wfresh [] l = length l).
  { intros l. unfold YCbqGwild.wfresh, YCbqGwild.wild_fresh. induction l as [|t l IH]; [reflexivity|].
    cbn [List.filter]. cbn. rewrite <- IH. reflexivity. }
  unfold crs_dpok_B. cbn [crs_with_dp_B cb_ws cb_dp cb_S]. split.
  - unfold YCbqGwild.wbudget. rewrite Ewf. unfold CWx. rewrite x_cw_len. lia.
  - pose proof HDP4 as (_ & Hd4). rewrite Hws, app_nil_r in Hd4.
    pose proof HJc5w as Hw5. apply ajxR_wild in Hw5. cbn [st_depot YG00.set_depot app] in Hw5.
    assert (Hn : YCbqGwild.wild_fresh CWx WS1 = []).
    { apply length_zero_iff_nil. unfold YCbqGwild.wbudget, YCbqGwild.wfresh in HPW. lia. }
    intros t Ht. apply Hw5 in Ht. apply in_app_or in Ht as [Ht | Ht].
    + apply in_or_app. left. exact (Hd4 t Ht).
    + apply in_or_app. right. pose proof (YCbqGwild.wild_fresh_cover CWx WS1 t Ht) as Hc.
      rewrite Hn, app_nil_r in Hc. exact Hc. }
pose proof (x_base_call_rbR WR CTX0 C (st_depot S5) CWx fxk ly4 S3 Hp3 W4 rC2 mem4 mC2 (k + k1) sp2 fx5 ly5 S5 Hp5 W5
  regs5 mem5 md5 (k + k1 + k2) (STK_pj_parse (PI := prh_img_B)) [(cOut_B C, cOut_B C + 56)] k2 WS1 HB4R HJc5' HDP5 HJ2
  ltac:(intros a (r & Hr & Ha); destruct Hr as [<- | []]; exact Ha)
  (sink_closed_cons (cOut_B C, cOut_B C + 56) [] HposO sink_closed_nil)
  HMN5 (x_ap3 _ _ HP2) (x_ap4 _ _ HP2) Hfz5 Hfk5) as HB5.
pose proof (x_regsat_ap rC2 regs5 _ HP2 (x_XK_cs C sp2) HRk4) as HRk5.
pose proof (prh_ledger_bounds B _ _ _ _ _ _ _ _ _ _ _ _ HL5) as (_ & _ & Hcr5 & _).
clear HB4 HB4R HJc HJcR HJc5 HJc5' HJc5w HJ2 HRk4 Hch Hsp Hs0 P1 P3 P4 P10 P11 P12 Hrok Hra4 Hraz Hal Ho Hwin Hslot
  HSRC4 Hhome4.
(* from here the walk's base is the REBASED context's, at WR; its straight stretches are stepped plainly *)
set (Cr := crs_with_dp_B C (st_depot S5) CWx) in HB5.
change (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W5 (crs_cfg_B fx5 (BASE + (CRS_PC0_B + 444)) regs5 mem5 md5)
  (crs_post_B (fx := fx) (rc := rc) B ARx C)).
apply YGcfRhLift.ra_rh_of_SRr.
(* ---- +444 mv s7, a0 (rc = -1); +448 li a0, -1 ---- *)
hfd (CRS_PC0_B + 444) Hl Hd.
eapply (h_addi W5 fx5 regs5 mem5 md5 _ (CRS_PC0_B + 444) (CRS_PC0_B + 448) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite R10. xb HB5. xr HRk5.
clear Hl Hd. hfd (CRS_PC0_B + 448) Hl Hd.
eapply (h_addi W5 fx5 _ mem5 _ _ (CRS_PC0_B + 448) (CRS_PC0_B + 452) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite ?getr_zero.
lazymatch goal with |- context [v_addi ?z (-1)] =>
  replace (v_addi z (-1)) with (w64 (2 ^ 64 - 1)) by (apply bv_eq; vm_compute; reflexivity) end.
xb HB5. xr HRk5.
(* ---- +452 jal fuzz_alloc_fail (SIZE_MAX) ---- *)
clear Hl Hd.
assert (Hl : HSLOT (CRS_PC0_B + 452) = Some (PCall YPsym.AS_fuzz_alloc_fail 1%bv)) by (vm_compute; reflexivity).
eapply (x_hs_call W5 fx5 _ mem5 _ _ (CRS_PC0_B + 452) (CRS_PC0_B + 456) YPsym.AS_fuzz_alloc_fail Hl); [lia | reflexivity |].
intros ?. xb HB5. xr HRk5. clear Hl.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ ?m) _ => set (rC3 := r) in *; set (mC3 := m) in * end.
assert (T1 : getr rC3 1%bv = w64 (BASE + (CRS_PC0_B + 456))) by (unfold rC3; hgetr; reflexivity).
assert (T10 : getr rC3 10%bv = w64 (2 ^ 64 - 1)) by (unfold rC3; hgetr; reflexivity).
assert (T23 : getr rC3 23%bv = w64 (-1)) by (unfold rC3; hgetr; reflexivity).
destruct (x_callsiteR WR CTX0 Cr fx5 ly5 S5 Hp5 W5 rC3 mem5 mC3 (k + k1 + k2) sp2 (CRS_PC0_B + 456) HB5 HRk5 T1
  ltac:(lia) ltac:(vm_compute; reflexivity)) as (Hsp & Hs0 & T3 & T4 & Hrok & Hra4 & Hraz & Hal & Ho & ch3 & Hch).
xrbn Cr C.
pose proof HB5 as (_ & _ & _ & HJc & _). unfold crs_JR_B in HJc.
pose proof (x_frame_factsR WR CTX0 Cr fx5 ly5 S5 Hp5 W5 rC3 mem5 mC3 (k + k1 + k2) sp2 HB5) as (EF5 & Hin5 & _).
xrbn Cr C.
apply SRr_ret. cbv beta.
unfold crs_cfg_B, w64.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (x_callR WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    fx5 W5 rC3 mem5 (SIGMA YPsym.AS_fuzz_alloc_fail) STK_check_reject_clean_starved (spZ (cb_regs C)) []
    (cb_ly C) _ (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly5 S5 Hp5 mC3 (k + k1 + k2)
    (STK_fuzz_alloc_fail (PI := prh_img_B)) [] (sp2 - spZ (cb_regs C)) (w64 (BASE + (CRS_PC0_B + 456))) ch3 _ HJc).
  - rewrite Hsp. lia.
  - exact Hal.
  - lia.
  - rewrite ESTf. lia.
  - rewrite ESTf, ESTK. lia.
  - exact T3.
  - exact T4.
  - exact T1.
  - exact Hrok.
  - exact Hra4.
  - exact Hch.
  - intros HAFN3.
    exact (HT_fuzz_alloc_fail fx5 ly5 S5 Hp5 W5 rC3 mem5 mC3 ch3 Lam5 peak5 cnt5 fail5 ran5 (2 ^ 64 - 1)
      (cb_most C) 0 (x_callee_fpreR WR CTX0 Cr fx5 ly5 S5 Hp5 W5 rC3 mem5 mC3 (k + k1 + k2) sp2 _ rC3 mC3 ch3 HB5 Hsp Hraz
        HAFN3)
      HL5 T10 ltac:(lia)).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W6 c6 _ (ly6 & S6 & Hp6 & regs6 & mem6 & md6 & k3 & -> & HJc6 & HJ3 & HP3 & HQ3).
cbv beta delta [fQmn] in HQ3.
destruct HQ3 as ((Hrm3 & -> & -> & Eab3 & HL6) & HMN6).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ3 by lia.
assert (Efa3 : (if 2 ^ 64 - 1 <? SIZE_MAXZ - cnt5 then cnt5 + (2 ^ 64 - 1) else SIZE_MAXZ) = SIZE_MAXZ)
  by (rewrite (proj2 (Z.ltb_ge _ _)) by (unfold SIZE_MAXZ; lia); reflexivity).
rewrite Efa3 in HL6.
assert (HZ6 : pj_zeroR SEGS (rdW W6 mem6) (cOut_B C)).
{ pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G4 & _).
  unfold pj_zeroR in *. apply (x_garr_av (w_H W5) (w_H W6) mem5 mem6 _ _); [|exact HZ5].
  intros j Hjj. rewrite repeat_length in Hjj. apply (G4 CRS_CID_B (cb_fpos C) _ Hin5).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF5, E128. unfold cOut_B, CRS_OFF_DOC_B. lia.
  - intros (r & Hr & _). destruct Hr. }
pose proof (x_base_callR WR CTX0 Cr fx5 ly5 S5 Hp5 W5 rC3 mem5 mC3 (k + k1 + k2) sp2 fx5 ly6 S5 Hp5 W6 regs6 mem6 md6
  (k + k1 + k2 + k3) (STK_fuzz_alloc_fail (PI := prh_img_B)) [] k3 HB5 HJc6 HJ3
  ltac:(intros a (r & Hr & _); destruct Hr) sink_closed_nil
  HMN6 (x_ap3 _ _ HP3) (x_ap4 _ _ HP3) Hfz5 ltac:(intros r _; reflexivity)) as HB6.
pose proof (x_regsat_ap rC3 regs6 _ HP3 (x_XK_cs C sp2) HRk5) as HRk6.
assert (U23 : getr regs6 23%bv = w64 (-1)).
{ rewrite (x_ap rC3 regs6 23%bv HP3); [exact T23|]. change (bv_unsigned (23%bv : bv 5)) with 23. unfold acallee_saved. lia. }
clear HB5 HJc HJc6 HJ3 HRk5 Hch Hsp Hs0 T1 T3 T4 T10 T23 Hrok Hra4 Hraz Hal Ho.
change (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W6 (crs_cfg_B fx5 (BASE + (CRS_PC0_B + 456)) regs6 mem6 md6)
  (crs_post_B (fx := fx) (rc := rc) B ARx C)).
apply YGcfRhLift.ra_rh_of_SRr.
(* ---- +456 .. +464: a0 = s7 (rc), a1 = s8, a2 = s6 ---- *)
assert (V24 : getr regs6 24%bv = w64 (cOut_B C)) by xg HRk6.
assert (V22 : getr regs6 22%bv = w64 (Ledger.lsum (cb_Lam C))) by xg HRk6.
hfd (CRS_PC0_B + 456) Hl Hd.
eapply (h_addi W6 fx5 regs6 mem6 md6 _ (CRS_PC0_B + 456) (CRS_PC0_B + 460) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite U23. xb HB6. xr HRk6.
clear Hl Hd. hfd (CRS_PC0_B + 460) Hl Hd.
eapply (h_addi W6 fx5 _ mem6 _ _ (CRS_PC0_B + 460) (CRS_PC0_B + 464) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite V24. xb HB6. xr HRk6.
clear Hl Hd. hfd (CRS_PC0_B + 464) Hl Hd.
eapply (h_addi W6 fx5 _ mem6 _ _ (CRS_PC0_B + 464) (CRS_PC0_B + 468) _ _ _ _ Hl Hd); [reflexivity | lia | lia |].
hpost. rewrite V22. xb HB6. xr HRk6.
(* ---- +468 jal check_reject_clean (rc, s8, s6) ---- *)
clear Hl Hd.
assert (Hl : HSLOT (CRS_PC0_B + 468) = Some (PCall YPsym.AS_check_reject_clean 1%bv)) by (vm_compute; reflexivity).
eapply (x_hs_call W6 fx5 _ mem6 _ _ (CRS_PC0_B + 468) (CRS_PC0_B + 472) YPsym.AS_check_reject_clean Hl);
  [lia | reflexivity |].
intros ?. xb HB6. xr HRk6. clear Hl.
lazymatch goal with |- SRr _ _ (crs_cfg_B _ _ ?r _ ?m) _ => set (rC4 := r) in *; set (mC4 := m) in * end.
assert (D1 : getr rC4 1%bv = w64 (BASE + (CRS_PC0_B + 472))) by (unfold rC4; hgetr; reflexivity).
assert (D10 : getr rC4 10%bv = w64 (-1)) by (unfold rC4; hgetr; reflexivity).
assert (D11 : getr rC4 11%bv = w64 (cOut_B C)) by (unfold rC4; hgetr; reflexivity).
assert (D12 : getr rC4 12%bv = w64 (Ledger.lsum (cb_Lam C))) by (unfold rC4; hgetr; reflexivity).
destruct (x_callsiteR WR CTX0 Cr fx5 ly6 S5 Hp5 W6 rC4 mem6 mC4 (k + k1 + k2 + k3) sp2 (CRS_PC0_B + 472) HB6 HRk6 D1
  ltac:(lia) ltac:(vm_compute; reflexivity)) as (Hsp & Hs0 & D3 & D4 & Hrok & Hra4 & Hraz & Hal & Ho & ch4 & Hch).
xrbn Cr C.
pose proof HB6 as (_ & _ & _ & HJc & _). unfold crs_JR_B in HJc.
pose proof (x_zero_srcR WR CTX0 Cr fx5 ly6 S5 Hp5 W6 rC4 mem6 mC4 (k + k1 + k2 + k3) sp2 HB6 HZ6) as HZS.
apply SRr_ret. cbv beta.
unfold crs_cfg_B, w64.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ eapply (x_callR WR (YA0nH.wle_wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    fx5 W6 rC4 mem6 (SIGMA YPsym.AS_check_reject_clean) STK_check_reject_clean_starved (spZ (cb_regs C)) []
    (cb_ly C) _ (cb_Hp C) (cb_W C) (cb_mem C) (cb_md C) [(CRS_CID_B, cb_fpos C)] ly6 S5 Hp5 mC4 (k + k1 + k2 + k3)
    (STK_check_reject_clean (PI := prh_img_B)) [] (sp2 - spZ (cb_regs C)) (w64 (BASE + (CRS_PC0_B + 472))) ch4 _ HJc).
  - rewrite Hsp. lia.
  - exact Hal.
  - lia.
  - rewrite ESTc. lia.
  - rewrite ESTc, ESTK. lia.
  - exact D3.
  - exact D4.
  - exact D1.
  - exact Hrok.
  - exact Hra4.
  - exact Hch.
  - intros HAFN4.
    exact (HT_check_reject_clean fx5 ly6 S5 Hp5 W6 rC4 mem6 mC4 ch4 (-1) (cOut_B C) (Ledger.lsum (cb_Lam C)) Lam5 peak5
      cnt5 SIZE_MAXZ ran5 (cb_most C) 0
      (x_callee_fpreR WR CTX0 Cr fx5 ly6 S5 Hp5 W6 rC4 mem6 mC4 (k + k1 + k2 + k3) sp2 _ rC4 mC4 ch4 HB6 Hsp Hraz HAFN4)
      D10 ltac:(lia) ltac:(lia) D11 HZS D12 (crs_lsum_perm_B _ _ (Permutation_sym HpL5)) HL6).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W7 c7 _ (ly7 & S7 & Hp7 & regs7 & mem7 & md7 & k4 & -> & HJc7 & HJ4 & HP4 & HQ4).
cbv beta delta [fQmn] in HQ4.
destruct HQ4 as ((-> & -> & Eab4 & Hrm4 & HL7) & HMN7).
replace (spZ (cb_regs C) + (sp2 - spZ (cb_regs C))) with sp2 in HJ4 by lia.
pose proof (x_base_callR WR CTX0 Cr fx5 ly6 S5 Hp5 W6 rC4 mem6 mC4 (k + k1 + k2 + k3) sp2 fx5 ly7 S5 Hp5 W7 regs7 mem7 md7
  (k + k1 + k2 + k3 + k4) (STK_check_reject_clean (PI := prh_img_B)) [] k4 HB6 HJc7 HJ4
  ltac:(intros a (r & Hr & _); destruct Hr) sink_closed_nil
  HMN7 (x_ap3 _ _ HP4) (x_ap4 _ _ HP4) Hfz5 ltac:(intros r _; reflexivity)) as HB7.
pose proof (x_regsat_ap rC4 regs7 _ HP4 (x_XK_cs C sp2) HRk6) as HRk7.
change (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf W7 (crs_cfg_B fx5 (BASE + (CRS_PC0_B + 472)) regs7 mem7 md7)
  (crs_post_B (fx := fx) (rc := rc) B ARx C)).
(* ---- THE EXIT ---- *)
refine (x_exit HK CTX0 Cr fx5 ly7 S5 Hp5 W7 regs7 mem7 md7 (k + k1 + k2 + k3 + k4) sp2 Lam5 peak5 cnt5 ran5
  (KcR (st_depot S5) CWx) (KcW1 (st_depot S5) CWx) Htk HB7 HRk7 HL7 _ _ _ _ Hroom5 _ _).
all: xrbn Cr C.
- split; [exact HpL5|]. rewrite Eab4, Eab3. apply (Permutation_trans Hpb5). rewrite Eab1. exact Hpb3.
- rewrite Epeak. lia.
- rewrite Hran0. exact Hran5e.
- rewrite Ecnt. lia.
- intros Hr0. unfold crs_evs_at_W1_B. rewrite Es.
  assert (Eev : PresetReqAt.parse_evs prh_jr_strtod (cb_tb C) ok = PresetReqAt.parse_evs prh_jr_strtod (cb_tb C) g_sp).
  { apply x_parse_evs_agree. change prh_jr_strtod with ReaderRes.jr_strtod. rewrite Hrun. cbn [snd]. rewrite Eg.
    exact (x_agree ok (cb_cnt C) (Z.to_nat kp) (PjGrammar.calls tr) _ _ _ _ Hoks0 Hgr0 (Hc2 Hr0)). }
  rewrite <- Eev. apply (Hex5 ReaderRes.jr_strtod (cb_rp_x C) (cb_rp_os C) (cb_rp_i C) (cb_rp_H0 C) hist0 Hpos0).
  change prh_jr_strtod with ReaderRes.jr_strtod in *. rewrite Eev. exact HRUN.
- split; [intros H0; exfalso; exact (Htk H0)|]. intros _. rewrite Ecnt.
  split; [lia|]. intros Hr0. rewrite (Hc2 Hr0). lia.
Qed.


End f2.
End d2.

Print Assumptions crs_seg_X1_B.
Set Printing Implicit.
About crs_seg_X1_B.
Unset Printing Notations.
Print crs_from_X1_B.
Set Printing Notations.
Unset Printing Implicit.
