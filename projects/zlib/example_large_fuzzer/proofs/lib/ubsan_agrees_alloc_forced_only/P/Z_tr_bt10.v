(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_bt1 Z_tr_bt3 Z_tr_bt6 Z_tr_bt7 Z_tr_bt8 Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Ltac name_term X EX t :=
  let H := fresh in
  assert (H : exists X0, X0 = t) by (eexists; reflexivity);
  destruct H as [X EX]; rewrite <- ?EX in *.

(* [comment removed for export] *)
Definition l4_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 FC' DL' HP' DP' pcx m',
    ms' = MS (l4R L T (HL - 1) (node + 1) dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz (HM - 2))]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP' i < N) /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ ((pcx = 0x1beac /\ 2 <= HL - 1 /\ R = build_tree_loop4 f (bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC) t (node + 1))
        \/ (pcx = 0x1c118 /\ HL - 1 < 2 /\ R = bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC)).

Lemma l4_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> 0 <= node < N -> 3 <= HM <= 573 ->
  R = build_tree_loop4 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt psegs (l4_iter_post L s t T N HL HM node dsc mc BC OL SL MC f R ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1beac) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Rnode RHM ER.
  pose proof (munch_refl (W5 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _).
  assert (RDT : ct_readable (W4 L) m T FC DL N) by (eapply ct_readable_rw; [exact ARR| lia| lia| cbn [disjoint_from]; lia]).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  call (l4_remove L s t T N HL HM node dsc mc FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact RDT. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
  1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact RHL. }
  clear RDT.
  match goal with H : u32arr psegs _ _ (av32 ?hp2 573) |- _ => name_term HP2 EHP2 hp2 end.
  pose proof (PQ 1 ltac:(lia)) as Rn.
  match goal with HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N |- _ => pose proof (HQ 1 ltac:(lia)) as Rm; rename HQ into PQ2 end.
  match goal with H : u32arr psegs ?mm _ (av32 HP2 573), HD : u8arr psegs ?mm (dl_As L + 5308) _, HG : rw_cells psegs ?mm (dl_As L + 5300) _,
                   HLn : arr_len HP2 = 573 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    rename HLn into LHP2;
    call (l4_node L T N (HL - 1) HM node dsc mc (arr_get HP 1) (arr_get HP2 1) FC DL HP2 DP);
    [exact ARR| exact H| exact HD| exact HG| eassumption| exact LAY| exact RT1| exact RT2| exact RN| exact LFC| exact LDL| exact LHP2| exact LDP| exact RFC| exact RDP
    | reflexivity| exact Rn| exact Rm| exact Rnode| lia| exact RHM|] end.
  match goal with H : u8arr psegs _ T (u16s (avct ?fc' ?dl' N)) |- _ => name_term FC' EFC fc'; name_term DL' EDL dl'; rename H into ARR' end.
  match goal with H : u32arr psegs _ _ (av32 ?hp3 573) |- _ => name_term HP3 EHP3 hp3; rename H into HPA3 end.
  match goal with H : u8arr psegs _ (dl_As L + 5308) (av8 ?dp' 573) |- _ => name_term DP' EDP dp'; rename H into DPA' end.
  assert (LFC' : arr_len FC' = N) by (rewrite EFC, arr_len_set; exact LFC).
  assert (LDL' : arr_len DL' = N) by (rewrite EDL, !arr_len_set; exact LDL).
  assert (LHP3 : arr_len HP3 = 573) by (rewrite EHP3, !arr_len_set; exact LHP2).
  assert (LDP' : arr_len DP' = 573) by (rewrite EDP, arr_len_set; exact LDP).
  assert (RFC' : forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536).
  { intros i Hi. rewrite EFC. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RFC; exact Hi]. }
  assert (RDP' : forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256).
  { intros i Hi. rewrite EDP. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply Z_tr_cb3.wrap8_range| rewrite arr_get_set_other by exact NE; apply RDP; exact Hi]. }
  assert (E31 : arr_get HP3 1 = node) by (rewrite EHP3; apply arr_get_set_same; rewrite !arr_len_set; lia).
  assert (PQ3 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP3 i < N).
  { intros i Hi. rewrite EHP3. destruct (Z.eq_dec 1 i) as [<-|NE1]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rnode|].
    rewrite arr_get_set_other by exact NE1. destruct (Z.eq_dec (HM - 2) i) as [<-|NE2]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rm|].
    rewrite arr_get_set_other by exact NE2. destruct (Z.eq_dec (HM - 1) i) as [<-|NE3]; [rewrite arr_get_set_same by lia; exact Rn|].
    rewrite arr_get_set_other by exact NE3. apply PQ2. exact Hi. }
  pose proof (avct_zlength FC' DL' N ltac:(lia)) as LCT'.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT' : ct_readable (W4 L) mm T FC' DL' N) by (eapply ct_readable_rw; [exact ARR'| lia| lia| cbn [disjoint_from]; lia]) end.
  call (l4_down L s t T N (HL - 1) (HM - 2) node dsc mc FC' DL' HP3 DP' BC OL SL MC).
  1:{ exact HPA3. } 1:{ exact DPA'. } 1:{ eassumption. } 1:{ exact RDT'. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP3. }
  1:{ exact PQ3. } 1:{ exact RFC'. } 1:{ exact RDP'. } 1:{ lia. } 1:{ exact Rnode. } 1:{ exact E31. } 1:{ lia. }
  match goal with H : u32arr psegs _ _ (av32 ?hpf 573) |- _ => name_term HPf EHPf hpf; rename H into HPAf end.
  pose proof (l4_model s t BC OL SL MC FC DL HP HL HM DP node f R HP2 (arr_get HP2 1) FC' DL' HP3 DP' HPf ER EHP2 eq_refl EFC EDL EHP3 EDP EHPf) as EM.
  apply evt_done. unfold l4_iter_post. do 10 eexists. exists FC', DL', HPf, DP'. do 2 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR'|]. split; [exact HPAf|]. split; [eassumption|]. split; [eassumption|].
  split; [exact LFC'|]. split; [exact LDL'|]. split; [eassumption|]. split; [exact LDP'|]. split; [eassumption|]. split; [exact RFC'|]. split; [exact RDP'|].
  match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - left. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_le 2 (HL - 1)) K) in EM. exact EM.
  - right. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_gt 2 (HL - 1)) K) in EM. exact EM.
Qed.

(* [comment removed for export] *)
Definition bt_loop4_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc mc : Z) (BC : arr) (OL SL MC : Z) (R : deflate_state)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 FC' DL' HP' DP' HM' node' m',
    ms' = MS (l4R L T 1 node' dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c118) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz HM')]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ 0 <= arr_get HP' 1 < N /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ 1 <= HM' <= 571
    /\ R = bt_upd s t FC' DL' HP' 1 HM' DP' BC OL SL MC.

Lemma bt_loop4 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L -> munch (W5 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL -> HL <= Z.of_nat f -> 0 <= node -> node + HL <= N -> 2 * HL <= HM + 1 -> HM <= 573 ->
  R = build_tree_loop4 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt psegs (bt_loop4_post L s t T N dsc mc BC OL SL MC R ra sp gp tp s8 s9 s10 s11 F fc m0)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1beac) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC MI LAY MU WM RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Hf Rnode RC RK RHM ER.
  { exfalso. lia. }
  call (l4_iter L s t T N HL HM node dsc mc FC DL HP DP BC OL SL MC f R).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & ER')|(-> & K & ER')] end.
  - match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr psegs ?mm _ (av32 ?hp' 573), HD : u8arr psegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HG : rw_cells psegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (HL - 1) (HM - 2) (node + 1) dsc mc fc' dl' hp' dp' BC OL SL MC R m0);
        [exact HT| exact HA| exact HD| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| assumption| assumption| assumption| assumption
        | assumption| assumption| assumption| exact K| lia| lia| lia| lia| lia| exact ER'] end.
  - replace (HL - 1) with 1 in * by lia.
    apply evt_done. unfold bt_loop4_post. do 10 eexists.
    match goal with HT : u8arr psegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr psegs ?mm _ (av32 ?hp' 573), HD : u8arr psegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HQ : forall i, 1 <= i <= 1 -> _ |- _ =>
      exists fc', dl', hp', dp', (HM - 2), (node + 1); eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HA|]; split; [exact HD|]; split; [eassumption|];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [apply HQ; lia|]; split; [assumption|]; split; [assumption|];
      split; [lia| exact ER'] end.
Qed.
