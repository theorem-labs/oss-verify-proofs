(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_bt1 Z_tr_bt3 Z_tr_bt5 Z_tr_bt6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition l4_down_post (L : dlay) (T N HL HM node1 dsc mc : Z) (HPf DP : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 a6 a7 s5 s7 t3 t4 t5 t6 pcx m',
    ms' = MS (l4R L T HL node1 dsc mc ra sp gp tp t1 t2 a6 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (W4 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u32arr psegs m' (dl_As L + 3008) (av32 HPf 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ arr_len HPf = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HPf i < N)
    /\ ((pcx = 0x1bc64 /\ 2 <= HL) \/ (pcx = 0x1bed0 /\ HL < 2)).

Lemma l4_down : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc mc : Z) (FC DL HP3 DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t0 t1 t2 s5 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr psegs m (dl_As L + 3008) (av32 HP3 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (W4 L) m T FC DL N -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP3 = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP3 i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= HL < 573 -> 0 <= node < N -> arr_get HP3 1 = node -> node + 1 < 2^31 ->
  evt psegs (l4_down_post L T N HL HM (node + 1) dsc mc
               (ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1)) DP ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz (T + node * 4)) (wz (dl_As L + 5308 + node))
               (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz HL) t4 t5 t6) F (wz 0x1bdfc) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY RT1 RT2 RN LHP PQ RFC RDP RHL Rnode E1 Rn1.
  pose proof (munch_refl (W4 L) m) as MU. pose proof (wmono_refl psegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  pose proof (av32_zlength HP3 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep. br_cases K.
  -
    assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1) = arr_set HP3 1 node).
    { rewrite <- E1. apply pqdownheap_heap. apply pq_out. rewrite bt_heap_len. lia. }
    zs2. zs2. zs2.
    h32_store HPA HP3 573 (dl_As L + 3008) 1 node ltac:(reflexivity).
    zs2. zs2. zstep. br_cases K2; [|exfalso; lia].
    apply evt_done. unfold l4_down_post, l4R. rewrite EH. do 12 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [rewrite arr_len_set; exact LHP|]. split; [|right; split; [reflexivity| lia]].
    intros i Hi. replace i with 1 by lia. rewrite arr_get_set_same by lia. exact Rnode.
  -
    zs2. zs2. zs2.
    assert (Et2 : t2 = wz (bv_unsigned t2)) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite Et2. clear Et2.
    call (pq3_loop 32 L s t T N HL HM node 0 FC DL DP BC OL SL MC
            (pqdownheap_loop 32 (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t node 1 2) m HP3 1 2 1).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| apply munch_refl| apply wmono_refl| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rnode. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr psegs ?mm _ (av32 ?hp 573), HD : u8arr psegs ?mm _ (av8 DP 573),
                     HG : rw_cells psegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (EH : ds_heap (pqdownheap (bt_upd s t FC DL HP3 HL HM DP BC OL SL MC) t 1) = arr_set hp kk node)
        by (rewrite <- E1; apply pqdownheap_heap; rewrite E1; exact E);
      rename H into HPB; rename HD into DPB; rename HG into GCB; pose proof (av32_zlength hp 573 ltac:(lia)) as L32b;
      unfold pqR3; zs2; shl_norm; zs2;
      h32_store HPB hp 573 (dl_As L + 3008) kk node ltac:(reflexivity);
      zs2; zs2; zstep; br_cases K2; [exfalso; lia|];
      apply evt_done; unfold l4_down_post, l4R; rewrite EH; do 12 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HPB|]; split; [exact DPB|]; split; [exact GCB|];
      split; [rewrite arr_len_set; exact HL'|]; split; [|left; split; [reflexivity| lia]];
      intros i Hi; destruct (Z.eq_dec kk i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rnode| rewrite arr_get_set_other by exact NE; apply HQ; exact Hi] end.
Qed.
