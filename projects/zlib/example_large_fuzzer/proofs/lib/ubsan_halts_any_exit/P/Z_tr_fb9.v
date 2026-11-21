(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_fbpure Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees FlushBlockModel RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition tfb_detect_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b3bc) fc None m' (seg_rom psegs)
    /\ munch [(dl_S L + 88, dl_S L + 92)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ dzs m' L (ds_strm (tfb_X0 s)).

Lemma tfb_X0_strm : forall s, 0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ds_strm (tfb_X0 s) = cset_data_type (ds_strm s) (detect_data_type s).
Proof.
  intros s Hl Hd. unfold tfb_X0. rewrite (proj2 (Z.ltb_lt _ _) Hl), Hd. reflexivity.
Qed.

Lemma tfb_dd_store : forall (L : dlay) (s : deflate_state) (v : Z) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = v ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) (wz v) a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b3b8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  lay_open LAY. destruct DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold tfR. zs2.
  apply evt_done. unfold tfb_detect_post, tfR. do 5 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite (tfb_X0_strm s Hl Hd), Ev. exists p1, p2, p3, resv. unfold zs_call_cells, zs_priv_cells. cbn [app].
  close_cells ZS.
Qed.

Lemma tfb_dd_bin : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_BINARY ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b3b4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold tfR. zs2.
  eapply (tfb_dd_store L s 0 sp last len bufp); eassumption.
Qed.
Lemma tfb_dd_text : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_TEXT ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bc28) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold tfR. zs2. zs2.
  eapply (tfb_dd_store L s 1 sp last len bufp); eassumption.
Qed.

Lemma tfb_dd_loop : forall (j : nat) (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  (Z.of_nat (S j) <= 224) ->
  ((exists k, 256 - Z.of_nat (S j) <= k < 256 /\ Freq s TL k <> 0) -> detect_data_type s = Z_TEXT) ->
  ((forall k, 256 - Z.of_nat (S j) <= k < 256 -> Freq s TL k = 0) -> detect_data_type s = Z_BINARY) ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 (wz (dl_As L + 212 + 4 * (256 - Z.of_nat (S j)))) (wz (Z.of_nat (S j))) a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1bc38) fc None m (seg_rom psegs)).
Proof.
  induction j as [|j IH]; intros until m; intros DZ MI LAY Hl Hd RDT RF Rj HT HB.
  all: pose proof (dlay_ranges _ LAY) as (Rs & _).
  all: match goal with |- evt _ _ (MS (tfR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?jj) _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (256 - jj) ltac:(lia)) as [RDf _]; pose proof (RF (256 - jj) ltac:(lia)) as Rf end.
  all: unfold tfR; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat 1). split; [lia| exact K].
  - rewrite K. zs2. zs2. zstep. br_false. zs2.
    eapply (tfb_dd_store L s 0 sp last len bufp); try eassumption. apply HB. intros k Hk. replace k with (256 - Z.of_nat 1) by lia. exact K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat (S (S j))). split; [lia| exact K].
  - rewrite K. zs2. zs2. zstep. br_true.
    replace (Z.of_nat (S (S j)) + -1) with (Z.of_nat (S j)) by lia.
    replace (dl_As L + 212 + 4 * (256 - Z.of_nat (S (S j))) + 4) with (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))) by lia.
    eapply (IH L s sp last len bufp); try eassumption; try lia.
    + intros (k & Hk & Hf). apply HT. exists k. split; [lia| exact Hf].
    + intros H. apply HB. intros k Hk. destruct (Z.eq_dec k (256 - Z.of_nat (S (S j)))) as [->|NE]; [exact K| apply H; lia].
Qed.

Lemma tfb_detect : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L s -> dzs m L (ds_strm s) -> mem_inv psegs m -> dlay_ok L ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  evt psegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (tfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1b2ec) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros GA DZ MI LAY Hl Rdt RDT RF.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & _ & RS).
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  pose proof DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold tfR. zs2. zs2. zs2. clear GA ZS.
  zstep. br_cases_s KDT.
  {
    apply evt_done. unfold tfb_detect_post, tfR. do 5 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold tfb_X0. unfold Z_UNKNOWN. rewrite (proj2 (Z.eqb_neq _ _) KDT), Bool.andb_false_r. exact DZ. }
  assert (Hd : cs_data_type (ds_strm s) = Z_UNKNOWN) by exact KDT.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 0 ltac:(lia)) as [RDb0 _]. replace (dl_As L + 212 + 4 * 0) with (dl_As L + 212) in RDb0 by lia.
  pose proof (RF 0 ltac:(lia)) as Rb0.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K0.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 0); [lia| reflexivity| exact K0]. }
  clear RDb0 Rb0.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 1 ltac:(lia)) as [RDb1 _]. replace (dl_As L + 212 + 4 * 1) with (dl_As L + 216) in RDb1 by lia.
  pose proof (RF 1 ltac:(lia)) as Rb1.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K1.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 1); [lia| reflexivity| exact K1]. }
  clear RDb1 Rb1.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 2 ltac:(lia)) as [RDb2 _]. replace (dl_As L + 212 + 4 * 2) with (dl_As L + 220) in RDb2 by lia.
  pose proof (RF 2 ltac:(lia)) as Rb2.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K2.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 2); [lia| reflexivity| exact K2]. }
  clear RDb2 Rb2.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 3 ltac:(lia)) as [RDb3 _]. replace (dl_As L + 212 + 4 * 3) with (dl_As L + 224) in RDb3 by lia.
  pose proof (RF 3 ltac:(lia)) as Rb3.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K3.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 3); [lia| reflexivity| exact K3]. }
  clear RDb3 Rb3.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 4 ltac:(lia)) as [RDb4 _]. replace (dl_As L + 212 + 4 * 4) with (dl_As L + 228) in RDb4 by lia.
  pose proof (RF 4 ltac:(lia)) as Rb4.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K4.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 4); [lia| reflexivity| exact K4]. }
  clear RDb4 Rb4.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 5 ltac:(lia)) as [RDb5 _]. replace (dl_As L + 212 + 4 * 5) with (dl_As L + 232) in RDb5 by lia.
  pose proof (RF 5 ltac:(lia)) as Rb5.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K5.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 5); [lia| reflexivity| exact K5]. }
  clear RDb5 Rb5.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 6 ltac:(lia)) as [RDb6 _]. replace (dl_As L + 212 + 4 * 6) with (dl_As L + 236) in RDb6 by lia.
  pose proof (RF 6 ltac:(lia)) as Rb6.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K6.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 6); [lia| reflexivity| exact K6]. }
  clear RDb6 Rb6.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 14 ltac:(lia)) as [RDb14 _]. replace (dl_As L + 212 + 4 * 14) with (dl_As L + 268) in RDb14 by lia.
  pose proof (RF 14 ltac:(lia)) as Rb14.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K14.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 14); [lia| reflexivity| exact K14]. }
  clear RDb14 Rb14.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 15 ltac:(lia)) as [RDb15 _]. replace (dl_As L + 212 + 4 * 15) with (dl_As L + 272) in RDb15 by lia.
  pose proof (RF 15 ltac:(lia)) as Rb15.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K15.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 15); [lia| reflexivity| exact K15]. }
  clear RDb15 Rb15.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 16 ltac:(lia)) as [RDb16 _]. replace (dl_As L + 212 + 4 * 16) with (dl_As L + 276) in RDb16 by lia.
  pose proof (RF 16 ltac:(lia)) as Rb16.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K16.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 16); [lia| reflexivity| exact K16]. }
  clear RDb16 Rb16.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 17 ltac:(lia)) as [RDb17 _]. replace (dl_As L + 212 + 4 * 17) with (dl_As L + 280) in RDb17 by lia.
  pose proof (RF 17 ltac:(lia)) as Rb17.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K17.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 17); [lia| reflexivity| exact K17]. }
  clear RDb17 Rb17.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 18 ltac:(lia)) as [RDb18 _]. replace (dl_As L + 212 + 4 * 18) with (dl_As L + 284) in RDb18 by lia.
  pose proof (RF 18 ltac:(lia)) as Rb18.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K18.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 18); [lia| reflexivity| exact K18]. }
  clear RDb18 Rb18.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 19 ltac:(lia)) as [RDb19 _]. replace (dl_As L + 212 + 4 * 19) with (dl_As L + 288) in RDb19 by lia.
  pose proof (RF 19 ltac:(lia)) as Rb19.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K19.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 19); [lia| reflexivity| exact K19]. }
  clear RDb19 Rb19.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 20 ltac:(lia)) as [RDb20 _]. replace (dl_As L + 212 + 4 * 20) with (dl_As L + 292) in RDb20 by lia.
  pose proof (RF 20 ltac:(lia)) as Rb20.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K20.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 20); [lia| reflexivity| exact K20]. }
  clear RDb20 Rb20.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 21 ltac:(lia)) as [RDb21 _]. replace (dl_As L + 212 + 4 * 21) with (dl_As L + 296) in RDb21 by lia.
  pose proof (RF 21 ltac:(lia)) as Rb21.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K21.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 21); [lia| reflexivity| exact K21]. }
  clear RDb21 Rb21.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 22 ltac:(lia)) as [RDb22 _]. replace (dl_As L + 212 + 4 * 22) with (dl_As L + 300) in RDb22 by lia.
  pose proof (RF 22 ltac:(lia)) as Rb22.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K22.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 22); [lia| reflexivity| exact K22]. }
  clear RDb22 Rb22.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 23 ltac:(lia)) as [RDb23 _]. replace (dl_As L + 212 + 4 * 23) with (dl_As L + 304) in RDb23 by lia.
  pose proof (RF 23 ltac:(lia)) as Rb23.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K23.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 23); [lia| reflexivity| exact K23]. }
  clear RDb23 Rb23.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 24 ltac:(lia)) as [RDb24 _]. replace (dl_As L + 212 + 4 * 24) with (dl_As L + 308) in RDb24 by lia.
  pose proof (RF 24 ltac:(lia)) as Rb24.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K24.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 24); [lia| reflexivity| exact K24]. }
  clear RDb24 Rb24.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 25 ltac:(lia)) as [RDb25 _]. replace (dl_As L + 212 + 4 * 25) with (dl_As L + 312) in RDb25 by lia.
  pose proof (RF 25 ltac:(lia)) as Rb25.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K25.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 25); [lia| reflexivity| exact K25]. }
  clear RDb25 Rb25.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 28 ltac:(lia)) as [RDb28 _]. replace (dl_As L + 212 + 4 * 28) with (dl_As L + 324) in RDb28 by lia.
  pose proof (RF 28 ltac:(lia)) as Rb28.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K28.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 28); [lia| reflexivity| exact K28]. }
  clear RDb28 Rb28.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 29 ltac:(lia)) as [RDb29 _]. replace (dl_As L + 212 + 4 * 29) with (dl_As L + 328) in RDb29 by lia.
  pose proof (RF 29 ltac:(lia)) as Rb29.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K29.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 29); [lia| reflexivity| exact K29]. }
  clear RDb29 Rb29.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 30 ltac:(lia)) as [RDb30 _]. replace (dl_As L + 212 + 4 * 30) with (dl_As L + 332) in RDb30 by lia.
  pose proof (RF 30 ltac:(lia)) as Rb30.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K30.
  { eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 30); [lia| reflexivity| exact K30]. }
  clear RDb30 Rb30.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 31 ltac:(lia)) as [RDb31 _]. replace (dl_As L + 212 + 4 * 31) with (dl_As L + 336) in RDb31 by lia.
  pose proof (RF 31 ltac:(lia)) as Rb31.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s K31.
  2:{ eapply (tfb_dd_bin L s sp last len bufp); try eassumption. apply (ddt_binary s 31); [lia| reflexivity| exact K31]. }
  clear RDb31 Rb31.
  assert (H0 : forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0).
  { intros k Hk Hb. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    repeat (destruct C as [C|C]; [subst k; first [assumption | discriminate Hb]|]). subst k. first [assumption | discriminate Hb]. }
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 9 ltac:(lia)) as [RDw9 _]. replace (dl_As L + 212 + 4 * 9) with (dl_As L + 248) in RDw9 by lia.
  pose proof (RF 9 ltac:(lia)) as Rw9.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W9.
  { eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). left. exact W9. }
  clear RDw9 Rw9.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 10 ltac:(lia)) as [RDw10 _]. replace (dl_As L + 212 + 4 * 10) with (dl_As L + 252) in RDw10 by lia.
  pose proof (RF 10 ltac:(lia)) as Rw10.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W10.
  { eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). right; left. exact W10. }
  clear RDw10 Rw10.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI 13 ltac:(lia)) as [RDw13 _]. replace (dl_As L + 212 + 4 * 13) with (dl_As L + 264) in RDw13 by lia.
  pose proof (RF 13 ltac:(lia)) as Rw13.
  zs2. rewrite zx16_small by lia. zstep. br_cases_s W13.
  2:{ eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply (ddt_text1 s H0). right; right. exact W13. }
  clear RDw13 Rw13.
  pose proof (ddt_rest s H0 W9 W10 W13) as ER.
  zs2. zs2.
  replace (wz (dl_As L + 340)) with (wz (dl_As L + 212 + 4 * (256 - Z.of_nat 224))) by (f_equal; lia).
  change (wz 224) with (wz (Z.of_nat 224)).
  eapply (tfb_dd_loop 223 L s sp last len bufp); try eassumption; try lia.
  - intros HE. rewrite ER, (dl2_some 224 s 32); [reflexivity| | lia]. destruct HE as (k & Hk & Hf). exists k. split; [lia| exact Hf].
  - intros HZ. rewrite ER, (dl2_none 224 s 32); [reflexivity|]. intros k Hk. apply HZ. lia.
Qed.
