(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_bt1 Z_tr_bt3.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition pqR2 (L : dlay) (T k x6v x7v hlv v n : Z) (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz (dl_As L + 5308 + v)) (wz (T + v * 4)) (wz k) s0 (wz (dl_As L)) a0 a1 (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) s5 (wz v)
      (wz T) s3 (wz (dl_As L + 5300)) t5 (wz (dl_As L + 3008)) t6 s8 s9 s10 s11 (wz x6v) (wz x7v) (wz hlv) t4.

Lemma pq2_sel : forall (L : dlay) (T N k j q HL v n : Z) (FC DL HP DP : arr) (x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv',
               ms' = MS (pqR2 L T k (sel3 FC HL DP HP j) (sel3 FC HL DP HP j) hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4' t5' t6') F (wz 0x1bd28) fc None m (seg_rom psegs))
      (MS (pqR2 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bcbc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold pqR2.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    zs2. apply evt_done. unfold sel3. rewrite (proj2 (Z.ltb_ge j HL)) by lia. cbn [andb]. do 4 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read psegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read psegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. replace (Z.lor j 1) with (j + 1) by (rewrite Ej, lor1_even by lia; lia).
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2.
    zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    +
      zstep. br_cases_s K2.
      *
        zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
        cbn [andb orb]. do 4 eexists. reflexivity.
      *
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        zs2. zs2. zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
    +
      zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb orb]. do 4 eexists. reflexivity.
Qed.

Lemma pq2_cmp : forall (L : dlay) (T N k j' HL v n : Z) (FC DL HP DP : arr) (hlv : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= j' <= HL -> HL < 573 -> 0 <= v < N ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv' pcx,
               ms' = MS (pqR2 L T k (arr_get HP j') j' hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4' t5' t6') F (wz pcx) fc None m (seg_rom psegs)
               /\ ((pcx = 0x1bd5c /\ smal FC DP v (arr_get HP j') = true) \/ (pcx = 0x1bca0 /\ smal FC DP v (arr_get HP j') = false)))
      (MS (pqR2 L T k j' j' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bd28) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Rj RHL Rv. lay_open LAY. unfold pqR2.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ j' Rj) as Rhj.
  pose proof (u32arr_read psegs m _ (av32 HP 573) j' _ (wa (dl_As L + 3008 + j' * 4)) HPA (av32_nth HP 573 j' ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j') ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP j') with (T + arr_get HP j' * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  zs2. shl_norm. zs2. zs2. zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. shl_norm. zs2. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j'))) by lia.
  zstep. br_cases K1.
  - apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
  - zstep. br_cases_s K2.
    + apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia. reflexivity.
    + pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j') _ (wa (dl_As L + 5308 + arr_get HP j')) DPA (av8_nth DP 573 (arr_get HP j') ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read psegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP j') ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      zs2. zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j'))) by lia.
      zstep. br_cases K3.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_gt _ _)) by lia. reflexivity.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. apply orb_true_r.
Qed.

Definition pq2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists k0 x6v hlv t4 t5 t6 HP' k' m',
    ms' = MS (pqR2 L T k0 x6v k' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bd60) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma pq2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt psegs (pq2_post L s t T N HL HM v n FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 F fc m0)
      (MS (pqR2 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bcbc) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (pq2_sel L T N k j q HL v n FC DL HP DP x7v); try eassumption; lia|]. intros ms' (t4' & t5' & t6' & hlv' & ->).
    eapply evt_cut; [eapply (pq2_cmp L T N k (sel3 FC HL DP HP j) HL v n FC DL HP DP hlv'); try eassumption; lia|].
    intros ms' (t4'' & t5'' & t6'' & hlv'' & pcx & -> & [[-> SM]|[-> SM]]); rewrite SM in ER.
    +
      unfold pqR2. zs2.
      apply evt_done. unfold pq2_post, pqR2. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    +
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold pqR2. zs2. shl_norm. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. zstep. br_cases K.
      *
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        apply evt_done. unfold pq2_post, pqR2. do 9 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * eapply (IH L s t T N HL HM v n FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j' j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.
