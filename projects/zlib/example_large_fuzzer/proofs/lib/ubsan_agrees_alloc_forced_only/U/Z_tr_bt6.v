(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_tr_bt9.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3 RefBuildTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

Lemma le2_add_sx16_2 : forall a b, le2 (wz (bv_unsigned (sx16 (wz b)) + bv_unsigned (sx16 (wz a)))) = le2 (wz (wrap16 (a + b))).
Proof.
  intros a b. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem.
  rewrite Z.add_mod by lia. rewrite !lo16_sx16, !lo16_unsigned_wz. rewrite <- Z.add_mod by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Definition ul4R (L : dlay) (T node : Z) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) :=
  mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) a0 a1 a2 a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
      (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz node) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6.

Notation Wpq lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).
Notation ubt_f64 L := ([C8 (wz (ONES - (dl_As L + 3008)))])%list (only parsing).
Notation W5m L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).
Notation W4 lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5308)] (only parsing).
Notation W5 lo sp L T N := [(lo%Z, bv_unsigned sp); (T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

(* [comment removed for export] *)
Definition ul4_remove_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP2 m',
    ms' = MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (arr_get HP 1)) t3 t4 t5 t6 sp gp tp) F (wz 0x1d008) fc None m' (seg_rom usegs)
    /\ munch (W4 lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP2 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1 = bt_upd s t FC DL HP2 (HL - 1) HM DP BC OL SL MC
    /\ arr_len HP2 = 573 /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP2 i < N).

Lemma ul4_remove : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> a0 = wz HL ->
  evt usegs (ul4_remove_post L s t T N HL HM node lo FC DL HP DP BC OL SL MC sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY STK LO BEL Rsp AL4 RT1 RT2 RN LFC LHP PQ RFC RDP RHL ->.
  pose proof (munch_refl (W4 lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (PQ HL ltac:(lia)) as Rv. pose proof (PQ 1 ltac:(lia)) as Rn1. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul4R, BT_L4. zs2. ustep BT_TRAP.
  pose proof (u32arr_read usegs m _ (av32 HP 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  zs2. zstep. reg_as (HL + -1) (HL - 1). ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP. zs2.
  lazymatch goal with H : u32arr usegs ?mm _ (av32 HP 573) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP 573) HL _ (wa (dl_As L + 3008 + HL * 4)) H (av32_nth HP 573 HL ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDv end.
  zs2.
  h32_store HPA HP 573 (dl_As L + 3008) 1 (arr_get HP HL) ltac:(reflexivity).
  zs2. zs2. zs2. try reg_as (T + 0) T. zstep.
  set (HP1 := arr_set HP 1 (arr_get HP HL)) in *.
  assert (PQ1 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP1 i < N).
  { intros i Hi. subst HP1. destruct (Z.eq_dec 1 i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; lia]. }
  lazymatch goal with H : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (RDT : ct_readable (Wpq lo sp L) mm T FC DL N) by (eapply ct_readable_rw; [exact H| lia| lia| cbn [disjoint_from]; lia]) end.
  call (pqdownheap_spec L s t T N (HL - 1) HM 1 lo FC DL HP1 DP BC OL SL MC).
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact RDT. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ eassumption. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ subst HP1; rewrite arr_len_set; exact LHP. } 1:{ exact PQ1. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                   HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    apply evt_done; unfold ul4_remove_post, ul4R; do 18 eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HS|];
    split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact E|]; split; [exact HL'| exact HQ] end.
Qed.


(* [comment removed for export] *)
Definition ul4_node_post (L : dlay) (T N HL HM node : Z) (FC' DL' HP3 DP' : arr)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) (wz (dl_As L)) (wz T) (wz 1) a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
                  (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (node + 1)) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6) F (wz 0x1d13c) fc None m' (seg_rom usegs)
    /\ munch (W5m L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP3 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz (HM - 2))].

(* [comment removed for export] *)
Ltac ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC :=
  ustep BT_TRAP; ustep BT_TRAP; zs2; zs2;
  match goal with |- context [wz (?d + 1)] => pb_store DPA DP 573 (dl_As L + 5308) node (wrap8 (d + 1)) ltac:(apply lo8_wz_wrap8; lia) end;
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) DL N T m_ (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  ct_store_dl ARR (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_))) (arr_set DL m_ (wrap16 node)) N T n (wrap16 node) ltac:(rewrite (wrap16_id node) by lia; reflexivity);
  zs2;
  h32_store HPA (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 573 (dl_As L + 3008) 1 node ltac:(reflexivity);
  zs2; zs2; zs2; try reg_as (T + 0) T;
  apply evt_done; unfold ul4_node_post; do 15 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA| exact GC].

Lemma ul4_node : forall (L : dlay) (t : tree_id) (T N HL HM node dsc n m_ : Z) (FC DL HP2 DP : arr)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP2 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP2 = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  m_ = arr_get HP2 1 -> 0 <= n < N -> 0 <= m_ < N -> 0 <= node < N -> 1 <= HL < 573 -> 3 <= HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 ->
  evt usegs (ul4_node_post L T N HL HM node (arr_set FC node (wrap16 (arr_get FC n + arr_get FC m_)))
               (arr_set (arr_set DL m_ (wrap16 node)) n (wrap16 node)) (arr_set (arr_set (arr_set HP2 (HM - 1) n) (HM - 2) m_) 1 node)
               (arr_set DP node (wrap8 (dmax DP n m_ + 1))) sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz n) t3 t4 t5 t6 sp gp tp) F (wz 0x1d008) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP RFC RDP Em Rn Rm Rnode RHL RHM RE.
  pose proof (munch_refl (W5m L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP2 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul4R.
  zs2. zs2. reg_as (HM + -1) (HM - 1). ustep BT_TRAP.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP2 573) 1 _ (wa (dl_As L + 2976 + 36)) HPA (av32_nth HP2 573 1 ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm; rewrite <- Em in RDm end.
  zs2. zstep. ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP. zs2. shl_norm. zs2.
  h32_store HPA HP2 573 (dl_As L + 3008) (HM - 1) n ltac:(reflexivity).
  zs2. zs2. reg_as (HM - 1 + -1) (HM - 2). ustep BT_TRAP. zstep. ustep BT_TRAP. zs2. shl_norm. zs2. ustep BT_TRAP.
  zs2. zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2.
  h32_store HPA (arr_set HP2 (HM - 1) n) 573 (dl_As L + 3008) (HM - 2) m_ ltac:(reflexivity).
  do 4 ustep BT_TRAP. do 4 ustep BT_TRAP. ustep BT_TRAP.
  zs2. shl_norm. zs2. do 4 ustep BT_TRAP. do 2 ustep BT_TRAP.
  ustep BT_TRAP. zs2. zs2. zs2. zs2. ustep BT_TRAP. ustep BT_TRAP.
  match goal with H : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u16arr_read usegs mm T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) H (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfn;
    pose proof (u16arr_read usegs mm T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) H (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDfm end.
  zs2. zs2. zs2.
  ct_store_fc ARR FC DL N T node (wrap16 (arr_get FC n + arr_get FC m_)) ltac:(apply le2_add_sx16_2).
  pose proof (RDP n ltac:(lia)) as Rdn. pose proof (RDP m_ ltac:(lia)) as Rdm.
  do 4 ustep BT_TRAP. zs2. zs2.
  match goal with H : u8arr usegs ?mm (dl_As L + 5308) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8arr_read usegs mm _ (av8 DP 573) n _ (wa (dl_As L + 5308 + n)) H (av8_nth DP 573 n ltac:(lia)) ltac:(lia) eq_refl) as RDdn;
    pose proof (u8arr_read usegs mm _ (av8 DP 573) m_ _ (wa (dl_As L + 5308 + m_)) H (av8_nth DP 573 m_ ltac:(lia)) ltac:(lia) eq_refl) as RDdm end.
  zsb. rewrite (bv8_small (arr_get DP n)) by lia. zsb. rewrite (bv8_small (arr_get DP m_)) by lia.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    assert (ED : dmax DP n m_ = arr_get DP n) by (unfold dmax; rewrite (proj2 (Z.leb_le _ _)) by lia; reflexivity). rewrite ED.
    ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
  - assert (ED : dmax DP n m_ = arr_get DP m_) by (unfold dmax; destruct (Z.leb_spec (arr_get DP m_) (arr_get DP n)); lia). rewrite ED.
    zs2. try reg_as (arr_get DP m_ + 0) (arr_get DP m_). ul4_node_tail L T N node n m_ FC DL HP2 DP HM MU WM ARR HPA DPA GC.
Qed.


(* [comment removed for export] *)
Definition ul4_down_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 HPf pcx m',
    ms' = MS (ul4R L T (node + 1) x1 t0 t1 t2 (wz HL) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (W4 lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HPf 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t 1 = bt_upd s t FC DL HPf HL HM DP BC OL SL MC
    /\ arr_len HPf = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HPf i < N)
    /\ ((pcx = BT_L4 /\ 2 <= HL) \/ (pcx = BT_PARTB /\ HL < 2)).

Lemma ul4_down : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (x1 t0 t1 t2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= HL < 573 -> 0 <= node ->
  evt usegs (ul4_down_post L s t T N HL HM node lo FC DL HP DP BC OL SL MC sp gp tp F fc m)
      (MS (mkR x1 sp gp tp t0 t1 t2 (wz (T + node * 4)) (wz 572) (wz (dl_As L)) (wz T) (wz 1) a3 a4 a5 a6 a7 (wz (dl_As L + 5308)) (wz (dl_As L + 3008)) (wz node) (wz (T + node * 4)) (wz T) x23
               (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (node + 1)) (wz (ONES - (dl_As L + 5308))) t3 t4 t5 t6) F (wz 0x1d13c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC MI LAY STK LO BEL AL4 RT1 RT2 RN LFC LHP PQ RFC RDP RHL Rnode.
  pose proof (munch_refl (W4 lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO. pose proof (PQ 1 ltac:(lia)) as R1.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zstep.
  assert (RDT : ct_readable (Wpq lo sp L) m T FC DL N) by (eapply ct_readable_rw; [exact ARR| lia| lia| cbn [disjoint_from]; lia]).
  call (pqdownheap_spec L s t T N HL HM 1 lo FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact RDT. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  zs2. zs2. zs2. zs2. zs2. reg_as (T + node * 4 + 4) (T + (node + 1) * 4).
  zstep. br_cases K;
    match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evt_done; unfold ul4_down_post, ul4R; do 19 eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HS|];
      split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact E|]; split; [exact HL'|]; split; [exact HQ|] end;
    [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ul4_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node lo : Z) (BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 FC' DL' HP' DP' pcx m',
    ms' = MS (ul4R L T (node + 1) x1 t0 t1 t2 (wz (HL - 1)) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (W5 lo sp L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz (HL - 1)); C4 (wz (HM - 2))]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ (forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP' i < N) /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ ((pcx = BT_L4 /\ 2 <= HL - 1 /\ R = build_tree_loop4 f (bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC) t (node + 1))
        \/ (pcx = BT_PARTB /\ HL - 1 < 2 /\ R = bt_upd s t FC' DL' HP' (HL - 1) (HM - 2) DP' BC OL SL MC)).

Lemma ul4_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL < 573 -> 0 <= node < N -> 3 <= HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 -> a0 = wz HL ->
  R = build_tree_loop4 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt usegs (ul4_iter_post L s t T N HL HM node lo BC OL SL MC f R sp gp tp F fc m)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC F16 F64 MI LAY STK LO BEL Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Rnode RHM RE Ea0 ER.
  pose proof (munch_refl (W5 lo sp L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (dlay_ranges _ LAY) as (Rs & _). pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  call (ul4_remove L s t T N HL HM node dsc lo FC DL HP DP BC OL SL MC).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact Rsp. } 1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact RHL. } 1:{ exact Ea0. }
  pose proof (PQ 1 ltac:(lia)) as Rn.
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp2 _ _ _ _ _ _ _, H : u32arr usegs ?mm _ (av32 ?hp2 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                   HLn : arr_len ?hp2 = 573, HQ : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get ?hp2 i < N,
                   HF16 : rw_cells usegs ?mm (bv_unsigned sp + 16) _, HF64 : rw_cells usegs ?mm (bv_unsigned sp + 64) _, HT : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    rename hp2 into HP2; rename E into E2; rename HLn into LHP2; rename HQ into PQ2; pose proof (PQ2 1 ltac:(lia)) as Rm;
    assert (EHP2 : HP2 = ds_heap (pqdownheap (bt_upd s t FC DL (arr_set HP 1 (arr_get HP HL)) (HL - 1) HM DP BC OL SL MC) t 1)) by (rewrite E2, bt_heap; reflexivity);
    call (ul4_node L t T N (HL - 1) HM node dsc (arr_get HP 1) (arr_get HP2 1) FC DL HP2 DP);
    [exact HT| exact H| exact HD| exact HG| exact HF16| exact HF64| eassumption| exact LAY| lia| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN| exact LFC| exact LDL| exact LHP2| exact LDP| exact RFC| exact RDP
    | reflexivity| exact Rn| exact Rm| exact Rnode| lia| exact RHM| exact RE|] end.
  match goal with H : u8arr usegs _ T (u16s (avct ?fc' ?dl' N)) |- _ => name_term FC' EFC fc'; name_term DL' EDL dl'; rename H into ARR' end.
  match goal with H : u32arr usegs _ _ (av32 ?hp3 573) |- _ => name_term HP3 EHP3 hp3; rename H into HPA3 end.
  match goal with H : u8arr usegs _ (dl_As L + 5308) (av8 ?dp' 573) |- _ => name_term DP' EDP dp'; rename H into DPA' end.
  assert (LFC' : arr_len FC' = N) by (rewrite EFC, arr_len_set; exact LFC).
  assert (LDL' : arr_len DL' = N) by (rewrite EDL, !arr_len_set; exact LDL).
  assert (LHP3 : arr_len HP3 = 573) by (rewrite EHP3, !arr_len_set; exact LHP2).
  assert (LDP' : arr_len DP' = 573) by (rewrite EDP, arr_len_set; exact LDP).
  assert (RFC' : forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536).
  { intros i Hi. rewrite EFC. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RFC; exact Hi]. }
  assert (RDP' : forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256).
  { intros i Hi. rewrite EDP. destruct (Z.eq_dec node i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply wrap8_range| rewrite arr_get_set_other by exact NE; apply RDP; exact Hi]. }
  assert (E31 : arr_get HP3 1 = node) by (rewrite EHP3; apply arr_get_set_same; rewrite !arr_len_set; lia).
  assert (PQ3 : forall i, 1 <= i <= HL - 1 -> 0 <= arr_get HP3 i < N).
  { intros i Hi. rewrite EHP3. destruct (Z.eq_dec 1 i) as [<-|NE1]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rnode|].
    rewrite arr_get_set_other by exact NE1. destruct (Z.eq_dec (HM - 2) i) as [<-|NE2]; [rewrite arr_get_set_same by (rewrite !arr_len_set; lia); exact Rm|].
    rewrite arr_get_set_other by exact NE2. destruct (Z.eq_dec (HM - 1) i) as [<-|NE3]; [rewrite arr_get_set_same by lia; exact Rn|].
    rewrite arr_get_set_other by exact NE3. apply PQ2. exact Hi. }
  pose proof (avct_zlength FC' DL' N ltac:(lia)) as LCT'. pose proof (av8_zlength DP' 573 ltac:(lia)) as L8'.
  match goal with HG : rw_cells usegs ?mm (dl_As L + 5300) _, HS : stk usegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ul4_down L s t T N (HL - 1) (HM - 2) node lo FC' DL' HP3 DP' BC OL SL MC);
    [exact ARR'| exact HPA3| exact DPA'| exact HG| eassumption| exact LAY| exact HS| unfold Z_PQ_STACK; lia| exact BEL| exact AL4| exact RT1| exact RT2| exact RN| exact LFC'| exact LHP3
    | exact PQ3| exact RFC'| exact RDP'| lia| lia|] end.
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hpf _ _ _ _ _ _ _, H : u32arr usegs _ _ (av32 ?hpf 573) |- _ =>
    rename hpf into HPf; rename E into Ef; rename H into HPAf;
    assert (EHPf : HPf = ds_heap (pqdownheap (bt_upd s t FC' DL' HP3 (HL - 1) (HM - 2) DP' BC OL SL MC) t 1)) by (rewrite Ef, bt_heap; reflexivity) end.
  pose proof (l4_model s t BC OL SL MC FC DL HP HL HM DP node f R HP2 (arr_get HP2 1) FC' DL' HP3 DP' HPf ER EHP2 eq_refl EFC EDL EHP3 EDP EHPf) as EM.
  apply evt_done. unfold ul4_iter_post. do 16 eexists. exists FC', DL', HPf, DP'. do 2 eexists.
  split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ARR'|]. split; [exact HPAf|]. split; [eassumption|]. split; [eassumption|].
  split; [exact LFC'|]. split; [exact LDL'|]. split; [assumption|]. split; [exact LDP'|]. split; [assumption|]. split; [exact RFC'|]. split; [exact RDP'|].
  match goal with H : _ /\ _ \/ _ /\ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - left. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_le 2 (HL - 1)) K) in EM. exact EM.
  - right. split; [reflexivity|]. split; [exact K|]. rewrite (proj2 (Z.leb_gt 2 (HL - 1)) K) in EM. exact EM.
Qed.


(* [comment removed for export] *)
Definition ubt_loop4_post (L : dlay) (s : deflate_state) (t : tree_id) (T N lo : Z) (BC : arr) (OL SL MC : Z) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 FC' DL' HP' DP' HM' node' m',
    ms' = MS (ul4R L T node' x1 t0 t1 t2 (wz 1) a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_PARTB) fc None m' (seg_rom usegs)
    /\ munch (W5 lo sp L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz HM')]
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573
    /\ 0 <= arr_get HP' 1 < N /\ (forall i, 0 <= i < N -> 0 <= arr_get FC' i < 65536) /\ (forall i, 0 <= i < 573 -> 0 <= arr_get DP' i < 256)
    /\ 1 <= HM' <= 571 /\ 0 <= node'
    /\ R = bt_upd s t FC' DL' HP' 1 HM' DP' BC OL SL MC.

Lemma ubt_loop4 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM node dsc lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) -> rw_cells usegs m (bv_unsigned sp + 64) (ubt_f64 L) ->
  mem_inv usegs m -> dlay_ok L -> munch (W5 lo sp L T N) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  2 <= HL -> HL <= Z.of_nat f -> 0 <= node -> node + HL <= N -> 2 * HL <= HM + 1 -> HM <= 573 -> 0 <= sd_elems t < 2 ^ 32 -> a0 = wz HL ->
  R = build_tree_loop4 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t node ->
  evt usegs (ubt_loop4_post L s t T N lo BC OL SL MC R sp gp tp F fc m0)
      (MS (ul4R L T node x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 sp gp tp) F (wz BT_L4) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC F16 F64 MI LAY MU WM STK LO BEL Rsp AL4 RT1 RT2 RN LFC LDL LHP LDP PQ RFC RDP RHL Hf Rnode RC RK RHM RE Ea0 ER.
  { exfalso. lia. }
  pose proof (dlay_ranges _ LAY) as (Rs & _). pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  call (ul4_iter L s t T N HL HM node dsc lo FC DL HP DP BC OL SL MC f R).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. } 1:{ exact Rsp. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RE. } 1:{ exact Ea0. } 1:{ exact ER. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K & ER')|(-> & K & ER')] end.
  - match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr usegs ?mm _ (av32 ?hp' 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HG : rw_cells usegs ?mm (dl_As L + 5300) _, HS : stk usegs ?mm _ _, HF16 : rw_cells usegs ?mm (bv_unsigned sp + 16) _, HF64 : rw_cells usegs ?mm (bv_unsigned sp + 64) _
                     |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (HL - 1) (HM - 2) (node + 1) dsc lo fc' dl' hp' dp' BC OL SL MC R m0);
        [exact HT| exact HA| exact HD| exact HG| exact HF16| exact HF64| eassumption| exact LAY| eassumption| eassumption| exact HS| unfold Z_PQ_STACK; exact LO| exact BEL| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN
        | assumption| assumption| assumption| assumption| assumption| assumption| assumption| exact K| lia| lia| lia| lia| lia| exact RE| reflexivity| exact ER'] end.
  - replace (HL - 1) with 1 in * by lia.
    apply evt_done. unfold ubt_loop4_post. do 16 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HA : u32arr usegs ?mm _ (av32 ?hp' 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp' 573),
                     HQ : forall i, 1 <= i <= 1 -> _, HS : stk usegs ?mm _ _ |- _ =>
      exists fc', dl', hp', dp', (HM - 2), (node + 1); eexists;
      split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HS|]; split; [exact HT|]; split; [exact HA|]; split; [exact HD|]; split; [eassumption|];
      split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [apply HQ; lia|]; split; [assumption|]; split; [assumption|];
      split; [lia|]; split; [lia| exact ER'] end.
Qed.
