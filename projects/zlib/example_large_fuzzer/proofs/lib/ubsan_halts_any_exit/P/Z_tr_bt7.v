(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_bt1 Z_tr_bt3 Z_tr_bt6.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Lemma le2_add_sx16_2 : forall a b, le2 (wz (bv_unsigned (sx16 (wz b)) + bv_unsigned (sx16 (wz a)))) = le2 (wz (wrap16 (a + b))).
Proof.
  intros a b. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite Z.add_mod by lia. rewrite !lo16_sx16, !lo16_unsigned_wz. rewrite <- Z.add_mod by lia. f_equal. lia.
Qed.

Notation W5 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition l4_node_post (L : dlay) (T N HL HM node dsc mc : Z) (FC' DL' HP3 DP' : arr)
    (ra sp gp tp s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s5 s7 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz (T + node * 4)) (wz (dl_As L + 5308 + node))
                  (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 (wz HL) t4 t5 t6) F (wz 0x1c044) fc None m' (seg_rom psegs)
    /\ munch (W5 L T N) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP3 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz (HM - 2))].

Ltac l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC :=
  zs2; zs2;
  match goal with |- context [wz (?d + 1)] => pb_store DPA DP 573 (dl_As L + 5308) node (wrap8 (d + 1)) ltac:(apply lo8_wz_wrap8; lia) end;
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) DL N T m_ (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) (arr_set DL m_ (wrap16 node)) N T n (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  zs2;
  h32_store HPA (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 573 (dl_As L + 3008) 1 node ltac:(reflexivity);
  apply evt_done; unfold l4_node_post; do 9 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA| exact GC].

Lemma l4_node : forall (L : dlay) (T N HL HM node dsc mc n m_ : Z) (FC DL HP2 DP : arr)
    (ra sp gp tp t0 t1 t2 a7 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP2 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv psegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP2 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  m_ = arr_get HP2 1 -> 0 <= n < N -> 0 <= m_ < N -> 0 <= node < N -> 1 <= HL < 573 -> 3 <= HM <= 573 ->
  evt psegs (l4_node_post L T N HL HM node dsc mc (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
               (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node)) (arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node)
               (arr_set DP node (wrap8 (dmax DP n m_ + 1))) ra sp gp tp s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L)) (wz node) (wz dsc) (wz 3) (wz (dl_As L + 5308)) (wz 2) (wz 1) (wz n) a7
               (wz T) (wz mc) (wz (dl_As L + 5300)) s5 (wz (dl_As L + 3008)) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bfb4) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY RT1 RT2 RN LFC LDL LHP LDP RFC RDP Em Rn Rm Rnode RHL RHM.
  pose proof (munch_refl (W5 L T N) m) as MU. pose proof (wmono_refl psegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP2 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (u32arr_read psegs m _ (av32 HP2 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP2 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  zs2. zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. zs2.
  h32_store HPA HP2 573 (dl_As L + 3008) (HM - 1) n ltac:(reflexivity).
  zs2. zs2. zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. zs2.
  h32_store HPA (arr_set HP2 (HM - 1) n) 573 (dl_As L + 3008) (HM - 2) m_ ltac:(reflexivity).
  match goal with H : u8arr psegs ?mm T _ |- _ =>
    pose proof (u16arr_read psegs mm T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) H (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfn;
    pose proof (u16arr_read psegs mm T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) H (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfm end.
  zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zs2.
  ct_store_fc ARR FC DL N T node (wrap16 (arr_get FC n + arr_get FC m_)) ltac:(apply le2_add_sx16_2).
  pose proof (RDP n ltac:(lia)) as Rdn. pose proof (RDP m_ ltac:(lia)) as Rdm.
  match goal with H : u8arr psegs ?mm (dl_As L + 5308) _ |- _ =>
    pose proof (u8arr_read psegs mm _ (av8 DP 573) n _ (wa (dl_As L + 5308 + n)) H (av8_nth DP 573 n ltac:(lia)) ltac:(lia) eq_refl) as RDdn;
    pose proof (u8arr_read psegs mm _ (av8 DP 573) m_ _ (wa (dl_As L + 5308 + m_)) H (av8_nth DP 573 m_ ltac:(lia)) ltac:(lia) eq_refl) as RDdm end.
  zsb. rewrite (bv8_small (arr_get DP n)) by lia. zsb. rewrite (bv8_small (arr_get DP m_)) by lia.
  zstep. br_cases K.
  -
    assert (ED : dmax DP n m_ = arr_get DP n) by (unfold dmax; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity). rewrite ED.
    l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
  - assert (ED : dmax DP n m_ = arr_get DP m_) by (unfold dmax; destruct (Z.leb_spec (arr_get DP m_) (arr_get DP n)); lia). rewrite ED.
    zs2. l4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
Qed.
