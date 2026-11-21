(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition pqR1 (L : dlay) (T k x6v x7v hlv v n : Z) (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz k) (wz x6v) (wz x7v) s0 (wz (dl_As L)) a0 a1 (wz (dl_As L + 5308)) (wz 1) (wz n) (wz v) (wz (dl_As L + 5308 + v)) (wz (T + v * 4))
      (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz hlv) t4 t5 t6.

Lemma lor1_even : forall q, 0 <= q -> Z.lor (2 * q) 1 = 2 * q + 1.
Proof.
  intros q Hq. pose proof (Z.add_lor_land (2 * q) 1) as H.
  assert (E : Z.land (2 * q) 1 = 0).
  { change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1) with 2. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma pq1_sel : forall (L : dlay) (T N k j q HL v n : Z) (FC DL HP DP : arr) (x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv',
               ms' = MS (pqR1 L T k (sel3 FC HL DP HP j) (sel3 FC HL DP HP j) hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz 0x1be34) fc None m (seg_rom psegs))
      (MS (pqR1 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bdc8) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold pqR1.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  - (* [comment removed for export] *)
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
    + (* [comment removed for export] *)
      zstep. br_cases_s K2.
      * (* [comment removed for export] *)
        zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_neq _ _)) by lia.
        cbn [andb orb]. do 4 eexists. reflexivity.
      * (* [comment removed for export] *)
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read psegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        zs2. zs2. zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_le _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
           rewrite (proj2 (Z.leb_gt _ _)) by lia. cbn [andb orb]. do 4 eexists. reflexivity.
    + (* [comment removed for export] *)
      zs2. zs2. zs2. apply evt_done. unfold sel3, smal. rewrite (proj2 (Z.ltb_lt j HL)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      cbn [andb orb]. do 4 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma pq1_cmp : forall (L : dlay) (T N k j' HL v n : Z) (FC DL HP DP : arr) (hlv : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= j' <= HL -> HL < 573 -> 0 <= v < N ->
  evt psegs (fun ms' => exists t4' t5' t6' hlv' pcx,
               ms' = MS (pqR1 L T k (arr_get HP j') j' hlv' v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4' t5' t6') F (wz pcx) fc None m (seg_rom psegs)
               /\ ((pcx = 0x1bd58 /\ smal FC DP v (arr_get HP j') = true) \/ (pcx = 0x1bda8 /\ smal FC DP v (arr_get HP j') = false)))
      (MS (pqR1 L T k j' j' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1be34) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY RT1 RT2 RN PQ RFC RDP Rj RHL Rv. lay_open LAY. unfold pqR1.
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
      * zs2. apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. unfold smal. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.eqb_eq _ _)) by lia.
        rewrite (proj2 (Z.leb_le _ _)) by lia. apply orb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fuel_ok (f : nat) (j HL : Z) : Prop := HL < j * 2 ^ Z.of_nat f.
Lemma fuel_ok_0 : forall j HL, fuel_ok 0 j HL -> HL < j.
Proof. unfold fuel_ok. intros j HL H. change (2 ^ Z.of_nat 0) with 1 in H. lia. Qed.
Lemma fuel_ok_S : forall f j j' HL, fuel_ok (S f) j HL -> 2 * j <= j' -> 0 < j -> fuel_ok f j' HL.
Proof.
  unfold fuel_ok. intros f j j' HL H Hj Hp. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  assert (0 < 2 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma pq_out : forall f X t v k j, ds_heap_len X < j -> pqdownheap_loop f X t v k j = (X, k).
Proof. intros [|f] X t v k j H; [reflexivity|]. cbn [pqdownheap_loop]. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.

Notation Wpq L := [(dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition pq1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists k0 x6v hlv t4 t5 t6 HP' k' m',
    ms' = MS (pqR1 L T k0 x6v k' hlv v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bd5c) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma pq1_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v n : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q x7v : Z)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt psegs (pq1_post L s t T N HL HM v n FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (pqR1 L T k j x7v HL v n ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 t4 t5 t6) F (wz 0x1bdc8) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (pq1_sel L T N k j q HL v n FC DL HP DP x7v); try eassumption; lia|]. intros ms' (t4' & t5' & t6' & hlv' & ->).
    eapply evt_cut; [eapply (pq1_cmp L T N k (sel3 FC HL DP HP j) HL v n FC DL HP DP hlv'); try eassumption; lia|].
    intros ms' (t4'' & t5'' & t6'' & hlv'' & pcx & -> & [[-> SM]|[-> SM]]); rewrite SM in ER.
    + (* [comment removed for export] *)
      unfold pqR1. zs2.
      apply evt_done. unfold pq1_post, pqR1. do 9 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    + (* [comment removed for export] *)
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold pqR1. zs2. zs2. shl_norm. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. zstep. br_cases K.
      * (* [comment removed for export] *)
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        apply evt_done. unfold pq1_post, pqR1. do 9 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * eapply (IH L s t T N HL HM v n FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j' j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition l3R (L : dlay) (T n : Z) (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 (wz (dl_As L)) a0 a1 (wz (dl_As L + 5308)) (wz 1) a4 (wz n) a6 a7
      (wz T) s3 (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Lemma pqdownheap_flat : forall s t FC DL HP HL HM DP BC OL SL MC k,
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k
  = heap_set (fst (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)))
             (snd (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2))) (arr_get HP k).
Proof.
  intros. unfold pqdownheap. rewrite bt_heap_get. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (pqdownheap_loop 32 _ t (arr_get HP k) k (k * 2)); reflexivity.
Qed.
Lemma loop3_S : forall f X t n, 1 <= n -> build_tree_loop3 (S f) X t n = build_tree_loop3 f (pqdownheap X t n) t (n - 1).
Proof. intros. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_le 1 n)) by lia. reflexivity. Qed.

Definition l3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n1 : Z) (FC DL DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 HP' pcx m',
    ms' = MS (l3R L T n1 ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = build_tree_loop3 f (bt_upd s t FC DL HP' HL HM DP BC OL SL MC) t n1
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N)
    /\ ((pcx = 0x1bd74 /\ 1 <= n1) \/ (pcx = 0x1be6c /\ n1 = 0)).

Ltac l3_close MU WM HPA DPA GC ER LHP PQ Rv SIDE :=
  apply evt_done; unfold l3_post, l3R; do 13 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPA|]; split; [eassumption|]; split; [eassumption|];
  split; [exact ER|]; split; [rewrite arr_len_set; exact LHP|]; split;
  [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
    match goal with |- 0 <= arr_get (arr_set _ ?k _) i < _ => destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi] end
  | SIDE; split; [reflexivity| lia] ].

Lemma l3_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= n <= HL -> HL < 573 ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt psegs (l3_post L s t T N HL HM (n - 1) FC DL DP BC OL SL MC f R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (l3R L T n ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd74) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Rn RHL ER.
  rewrite loop3_S, pqdownheap_flat in ER by lia.
  pose proof (PQ n ltac:(lia)) as Rv. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (u32arr_read psegs m _ (av32 HP 573) n _ (wa (dl_As L + 3008 + n * 4)) HPA (av32_nth HP 573 n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  unfold l3R. zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. shl_norm. strip32. zs2.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    rewrite pq_out in ER by (rewrite bt_heap_len; lia). cbn [fst snd] in ER. rewrite bt_heap_set in ER.
    zs2. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) n (arr_get HP n) ltac:(reflexivity).
    zs2. reg_as (n + -1) (n - 1). zstep. br_cases K2.
    + l3_close MU WM HPA DPA GC ER LHP PQ Rv ltac:(right).
    + l3_close MU WM HPA DPA GC ER LHP PQ Rv ltac:(left).
  - (* [comment removed for export] *)
    zs2. zs2. shl_norm. zs2. zs2. zs2.
    call (pq1_loop 32 L s t T N HL HM (arr_get HP n) n FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP n) n (n * 2)) m HP n (n * 2) n n).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      rewrite E in ER; cbn [fst snd] in ER; rewrite bt_heap_set in ER;
      rename H into HPB; rename HD into DPB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR1; zs2; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk (arr_get HP n) ltac:(reflexivity);
      zs2; reg_as (n + -1) (n - 1); zstep; br_cases K2;
      [ l3_close MU WM HPB DPB GC ER HL' HQ Rv ltac:(right) | l3_close MU WM HPB DPB GC ER HL' HQ Rv ltac:(left) ] end.
Qed.

Definition bt_loop3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (l3R L T 0 ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1be6c) fc None m' (seg_rom psegs)
    /\ munch (Wpq L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

Lemma bt_loop3 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq L) m0 T FC DL N -> mem_inv psegs m -> dlay_ok L -> munch (Wpq L) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  Z.of_nat (S f) = n -> n <= HL -> HL < 573 ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt psegs (bt_loop3_post L s t T N HL HM FC DL DP BC OL SL MC R ra sp gp tp s0 a0 a1 s3 s5 s7 s8 s9 s10 s11 F fc m0)
      (MS (l3R L T n ra sp gp tp t0 t1 t2 s0 a0 a1 a4 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd74) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM RT1 RT2 RN LHP PQ RFC RDP Ef Rn RHL ER.
  - call (l3_body L s t T N HL HM n FC DL HP DP BC OL SL MC 0%nat R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = build_tree_loop3 0 _ _ _ |- _ => cbn [build_tree_loop3] in E; rename E into ER' end.
    replace (n - 1) with 0 by lia.
    apply evt_done. unfold bt_loop3_post. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; assumption.
  - call (l3_body L s t T N HL HM n FC DL HP DP BC OL SL MC (S f) R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with E : R = build_tree_loop3 (S f) _ _ _, HA : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ _, HG : rw_cells psegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N HL HM (n - 1) FC DL hp DP BC OL SL MC R m0);
        [exact HA| exact HD| exact HG| exact RDT| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| assumption| assumption| exact RFC| exact RDP
        | lia| lia| exact RHL| exact E] end.
Qed.
