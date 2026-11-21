(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_fb1 Z_tr_fbpure.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees FillWinModel FlushBlockModel TreesTab. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefFlushBlk13.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

Definition tfb_detect_post (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 a6 m',
    ms' = MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c480) fc None m' (seg_rom usegs)
    /\ munch [(dl_S L + 88, dl_S L + 92)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ dzs m' L (ds_strm (tfb_X0 s)).

Lemma tfb_X0_strm : forall s, 0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ds_strm (tfb_X0 s) = cset_data_type (ds_strm s) (detect_data_type s).
Proof.
  intros s Hl Hd. unfold tfb_X0. rewrite (proj2 (Z.ltb_lt _ _) Hl), Hd. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tfb_dd_store : forall (L : dlay) (s : deflate_state) (v : Z) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = v ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 (wz v) a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c47c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. destruct DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold utfR. zs2.
  apply evt_done. unfold tfb_detect_post, utfR. do 8 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  rewrite (tfb_X0_strm s Hl Hd), Ev. exists p1, p2, p3, resv. unfold zs_call_cells, zs_priv_cells. cbn [app].
  close_cells ZS.
Qed.

(* [comment removed for export] *)
Lemma tfb_dd_text : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN -> detect_data_type s = Z_TEXT ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c478) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros DZ MI LAY Hl Hd Ev. unfold utfR. zs2.
  eapply (tfb_dd_store L s 1 sp last len bufp); eassumption.
Qed.

(* [comment removed for export] *)
Lemma tfb_dd_loop : forall (j : nat) (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> cs_data_type (ds_strm s) = Z_UNKNOWN ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  (Z.of_nat (S j) <= 224) ->
  ((exists k, 256 - Z.of_nat (S j) <= k < 256 /\ Freq s TL k <> 0) -> detect_data_type s = Z_TEXT) ->
  ((forall k, 256 - Z.of_nat (S j) <= k < 256 -> Freq s TL k = 0) -> detect_data_type s = Z_BINARY) ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz (dl_S L)) (wz (18446744073709551615 - (dl_As L + 212))) (wz (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))))
               (wz (Z.of_nat (S j))) (wz (4 * (256 - Z.of_nat (S j)))) a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1c54c) fc None m (seg_rom usegs)).
Proof.
  induction j as [|j IH]; intros until m; intros DZ MI LAY Hl Hd RDT RF Rj HT HB.
  all: pose proof (dlay_ranges _ LAY) as (Rs & _).
  all: match goal with |- evt _ _ (MS (utfR _ _ _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?jj) _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
         destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (256 - jj) ltac:(lia)) as [RDf _]; pose proof (RF (256 - jj) ltac:(lia)) as Rf end.
  all: unfold utfR; ustep TF_TRAP; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat 1). split; [lia| exact K].
  - rewrite K. zs2. zs2. zs2. zstep. br_false. zs2.
    eapply (tfb_dd_store L s 0 sp last len bufp); try eassumption. apply HB. intros k Hk. replace k with (256 - Z.of_nat 1) by lia. exact K.
  - eapply (tfb_dd_text L s sp last len bufp); try eassumption. apply HT. exists (256 - Z.of_nat (S (S j))). split; [lia| exact K].
  - rewrite K. zs2. zs2. zs2. zstep. br_true.
    replace (Z.of_nat (S (S j)) + -1) with (Z.of_nat (S j)) by lia.
    replace (dl_As L + 212 + 4 * (256 - Z.of_nat (S (S j))) + 4) with (dl_As L + 212 + 4 * (256 - Z.of_nat (S j))) by lia.
    replace (4 * (256 - Z.of_nat (S (S j))) + 4) with (4 * (256 - Z.of_nat (S j))) by lia.
    eapply (IH L s sp last len bufp); try eassumption; try lia.
    + intros (k & Hk & Hf). apply HT. exists k. split; [lia| exact Hf].
    + intros H. apply HB. intros k Hk. destruct (Z.eq_dec k (256 - Z.of_nat (S (S j)))) as [->|NE]; [exact K| apply H; lia].
Qed.

(* [comment removed for export] *)
Ltac dd_bits n RDT RF :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 115784) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ (Z_to_bv 64 115740) _ _ _ _) =>
      zs2; zstep; first [br_true | br_false];
      lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 115728) _ _ _ _) => zs2; zs2; zstep; first [br_true | br_false]; let n' := eval vm_compute in (n + 1) in dd_bits n' RDT RF
      | |- evt _ _ (MS _ _ (Z_to_bv 64 115748) _ _ ?mc _) =>
          ustep TF_TRAP; zs2;
          let RD := fresh "RDb" in let Rb := fresh "Rb" in let K := fresh "Kb" in
          (lazymatch goal with MI : mem_inv usegs ?mc' |- evt _ _ (MS _ _ _ _ _ ?mc' _) =>
             destruct (RDT mc' (munch_refl _ _) (wmono_refl _ _) MI n ltac:(lia)) as [RD _] end);
          pose proof (RF n ltac:(lia)) as Rb;
          zs2; rewrite (zx16_small (arr_get _ n)) by lia; zstep; br_cases_s K;
          [ rewrite ?K; zs2; zs2; zstep; first [br_true | br_false]; clear RD Rb; let n' := eval vm_compute in (n + 1) in dd_bits n' RDT RF
          | zs2; zstep; eapply tfb_dd_store; try eassumption; apply (ddt_binary _ n); [lia| reflexivity| exact K] ]
      end
  end.

(* [comment removed for export] *)
Lemma tfb_detect : forall (L : dlay) (s : deflate_state) (sp : word) (last len bufp : Z)
    (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  dsA m L s -> dzs m L (ds_strm s) -> mem_inv usegs m -> dlay_ok L ->
  0 < ds_level s -> - 2^31 <= cs_data_type (ds_strm s) < 2^31 ->
  ct_readable [(dl_S L + 88, dl_S L + 92)] m (dl_As L + 212) (ds_dyn_ltree_fc s) (ds_dyn_ltree_dl s) 573 ->
  (forall i, 0 <= i < 573 -> 0 <= arr_get (ds_dyn_ltree_fc s) i < 65536) ->
  evt usegs (tfb_detect_post L s sp last len bufp ra gp tp t0 t1 t2 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c3d4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros GA DZ MI LAY Hl Rdt RDT RF.
  pose proof (munch_refl [(dl_S L + 88, dl_S L + 92)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & _ & RS). pose proof (lo_S _ LAY) as (_ & ALS & _).
  destruct GA as (hA1 & hA2 & hA3 & hA4 & hA5 & GA). unfold dsA_cells in GA.
  pose proof DZ as (p1 & p2 & p3 & resv & ZS). unfold zs_call_cells, zs_priv_cells in ZS. cbn [app] in ZS.
  unfold utfR. zs2. ustep TF_TRAP. ustep TF_TRAP. ustep TF_TRAP. zs2. zs2. clear GA ZS.
  zstep. br_cases_s KDT.
  { (* [comment removed for export] *)
    apply evt_done. unfold tfb_detect_post, utfR. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    unfold tfb_X0. unfold Z_UNKNOWN. rewrite (proj2 (Z.eqb_neq _ _) KDT), Bool.andb_false_r. exact DZ. }
  assert (Hd : cs_data_type (ds_strm s) = Z_UNKNOWN) by exact KDT.
  do 4 zs2. rewrite zb_lxor_ones by lia. do 3 zs2. zstep.
  dd_bits 0 RDT RF.
 
  assert (H0 : forall k, 0 <= k <= 31 -> Z.testbit DD_MASK k = true -> Freq s TL k = 0).
  { intros k Hk Hb. assert (C : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    repeat (destruct C as [C|C]; [subst k; first [assumption | discriminate Hb]|]). subst k. first [assumption | discriminate Hb]. }
  (* [comment removed for export] *)
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 9 ltac:(lia)) as [RDw9 _]. pose proof (RF 9 ltac:(lia)) as Rw9.
  zs2. rewrite (zx16_small (arr_get _ 9)) by lia. zstep. br_cases_s W9.
  { eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). left. exact W9. }
  clear RDw9 Rw9.
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 10 ltac:(lia)) as [RDw10 _]. pose proof (RF 10 ltac:(lia)) as Rw10.
  zs2. rewrite (zx16_small (arr_get _ 10)) by lia. zstep. br_cases_s W10.
  { eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). right; left. exact W10. }
  clear RDw10 Rw10.
  zs2. ustep TF_TRAP.
  destruct (RDT _ (munch_refl _ _) (wmono_refl _ _) ltac:(eassumption) 13 ltac:(lia)) as [RDw13 _]. pose proof (RF 13 ltac:(lia)) as Rw13.
  zs2. rewrite (zx16_small (arr_get _ 13)) by lia. zstep. br_cases_s W13.
  2:{ eapply tfb_dd_text; try eassumption. apply (ddt_text1 s H0). right; right. exact W13. }
  clear RDw13 Rw13.
  pose proof (ddt_rest s H0 W9 W10 W13) as ER.
  zs2. zs2. zs2.
  replace (wz (dl_As L + 340)) with (wz (dl_As L + 212 + 4 * (256 - Z.of_nat 224))) by (f_equal; lia).
  change (wz 224) with (wz (Z.of_nat 224)). change (wz 128) with (wz (4 * (256 - Z.of_nat 224))).
  eapply (tfb_dd_loop 223 L s sp last len bufp); try eassumption; try lia.
  - intros HE. rewrite ER, (dl2_some 224 s 32); [reflexivity| | lia]. destruct HE as (k & Hk & Hf). exists k. split; [lia| exact Hf].
  - intros HZ. rewrite ER, (dl2_none 224 s 32); [reflexivity|]. intros k Hk. apply HZ. lia.
Qed.
