(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_bt1 Z_tr_bt3 Z_tr_bt4.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree1 RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition l4R (L : dlay) (T HL node dsc mc : Z) (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz HL) t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma pqdownheap_heap : forall s t FC DL HP HL HM DP BC OL SL MC HP' k',
  pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP 1) 1 2 = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k') ->
  ds_heap (pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t 1) = arr_set HP' k' (arr_get HP 1).
Proof.
  intros until k'. intros E. rewrite pqdownheap_flat. change (1 * 2) with 2. rewrite E. cbn [fst snd]. rewrite bt_heap_set, bt_heap. reflexivity.
Qed.

Ltac name_mem1 id := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => is_var mm; rename mm into id end.
Notation W4 L := [(dl_As L + 3008, dl_As L + 5308)] (only parsing).

(* [comment removed for export] *)
Definition l4_remove_post (L : dlay) (T N HL HM node dsc mc n : Z) (HP2 DP : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a7 s5 s7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz n) a7
                  (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb4) fc None m' (seg_rom psegs)
    /\ munch (W4 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HP2 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz HM)]
    /\ arr_len HP2 = 573 /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N).

Lemma l4_remove : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (W4 L) m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 ->
  evt psegs (l4_remove_post L T N HL HM node dsc mc (arr_get HP 1)
               (ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) DP ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (l4R L T HL node dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1beac) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY RT1 RT2 RN LHP PQ RFC RDP RHL.
  pose proof (munch_refl (W4 L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (PQ HL ltac:(lia)) as Rv. pose proof (PQ 1 ltac:(lia)) as Rn1. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold l4R. zs2. zs2. shl_norm. zs2. zs2.
  match goal with H : u32arr psegs ?mm _ (av32 HP 573) |- _ =>
    pose proof (u32arr_read psegs mm _ (av32 HP 573) HL _ (wa (dl_As L + 3008 + HL * 4)) H (av32_nth HP 573 HL ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDv;
    pose proof (u32arr_read psegs mm _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) H (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn end.
  zs2. zs2.
  h32_store HPA HP 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
  zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
    assert (E1 : arr_get HP1 1 = arr_get HP HL) by (subst HP1; apply arr_get_set_same; lia).
    assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t 1) = arr_set HP1 1 (arr_get HP HL)).
    { rewrite <- E1. apply pqdownheap_heap. apply pq_out. rewrite bt_heap_len. lia. }
    zs2. zs2.
    h32_store HPA HP1 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
    apply evt_done. unfold l4_remove_post. rewrite EH. do 11 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [subst HP1; rewrite !arr_len_set; exact LHP|].
    intros i Hi. replace i with 1 by lia. rewrite arr_get_set_same by (subst HP1; rewrite arr_len_set; lia). exact Rv.
  - (* [comment removed for export] *)
    set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
    assert (E1 : arr_get HP1 1 = arr_get HP HL) by (subst HP1; apply arr_get_set_same; lia).
    assert (PQ1 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP1 i < N).
    { intros i Hi. subst HP1. destruct (Z.eq_dec 1 i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; lia]. }
    zs2. zs2. shl_norm. zs2. zs2. zs2. zs2. name_mem1 m2.
    call (pq2_loop 32 L s t T N (HL - 1) HM (arr_get HP HL) 0 FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t (arr_get HP HL) 1 2) m2 HP1 1 2 1 1).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ subst HP1. rewrite arr_len_set. exact LHP. } 1:{ exact PQ1. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HG : rw_cells psegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP1 (HL - 1) HM DP BC OL SL MC) t 1) = arr_set hp kk (arr_get HP HL))
        by (rewrite <- E1; apply pqdownheap_heap; rewrite E1; exact E);
      rename H into HPB; rename HD into DPB; rename HG into GCB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR2; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk (arr_get HP HL) ltac:(reflexivity);
      apply evt_done; unfold l4_remove_post; rewrite EH; do 11 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPB|]; split; [exact DPB|]; split; [exact GCB|];
      split; [rewrite arr_len_set; exact HL'|];
      intros i Hi; destruct (Z.eq_dec kk i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply HQ; exact Hi] end.
Qed.
