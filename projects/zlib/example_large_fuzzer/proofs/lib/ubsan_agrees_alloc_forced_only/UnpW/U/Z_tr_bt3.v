(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree1 RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

Lemma loop3_S : forall f X t n, 1 <= n -> build_tree_loop3 (S f) X t n = build_tree_loop3 f (pqdownheap X t n) t (n - 1).
Proof. intros. cbn [build_tree_loop3]. rewrite (proj2 (Z.leb_le 1 n)) by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition ul3R (L : dlay) (T n : Z) (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) :=
  mkR x1 sp gp tp t0 t1 t2 (wz 1) x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 (wz (dl_As L)) x21 (wz T) x23 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) x27
      t3 t4 t5 t6.

Notation Wl3 lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition ul3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n1 lo : Z) (FC DL DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state)
    (x9 x18 x21 x23 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' pcx m',
    ms' = MS (ul3R L T (n1 + 1) x1 t0 t1 t2 x9 (wz n1) a1 a2 a3 a4 a5 a6 a7 x18 (wz (n1 + 1)) x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wl3 lo sp L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = build_tree_loop3 f (bt_upd s t FC DL HP' HL HM DP BC OL SL MC) t n1
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N)
    /\ ((pcx = BT_L3 /\ 1 <= n1) \/ (pcx = 0x1cf94 /\ n1 = 0)).

Lemma ubt_l3_trip : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (f : nat) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wl3 lo sp L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wl3 lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= n <= HL -> HL < 573 -> x10 = wz n ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt usegs (ul3_post L s t T N HL HM (n - 1) lo FC DL DP BC OL SL MC f R x9 x18 x21 x23 x27 sp gp tp F fc m0)
      (MS (ul3R L T n x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz BT_L3) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY MU WM STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Rn RHL -> ER.
  rewrite loop3_S in ER by lia.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. unfold Z_PQ_STACK in LO.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  unfold ul3R, BT_L3. zs2. try reg_as (n + 0) n. zs2. try reg_as (dl_As L + 0) (dl_As L). zs2. try reg_as (T + 0) T. zs2. try reg_as (n + 0) n.
  zstep.
  call (pqdownheap_spec L s t T N HL HM n lo FC DL HP DP BC OL SL MC).
  1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_PQ_STACK; lia. } 1:{ exact BEL. }
  1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ exact Rn. } 1:{ exact RHL. }
  1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
  match goal with E : pqdownheap _ _ _ = bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _ |- _ => rewrite E in ER end.
  zs2. reg_as (n + -1) (n - 1). zstep. br_cases K;
    replace (wz n) with (wz (n - 1 + 1)) by (f_equal; lia);
    match goal with HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      apply evt_done; unfold ul3_post, ul3R; do 18 eexists;
      split; [reflexivity|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HS|];
      split; [exact HA|]; split; [exact HD|]; split; [exact HG|]; split; [exact ER|]; split; [exact HL'|]; split; [exact HQ|] end;
    [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

Definition ubt_loop3_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM lo : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state)
    (x9 x18 x21 x23 x27 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (ul3R L T 1 x1 t0 t1 t2 x9 (wz 0) a1 a2 a3 a4 a5 a6 a7 x18 (wz 1) x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz 0x1cf94) fc None m' (seg_rom usegs)
    /\ munch (Wl3 lo sp L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

Lemma ubt_loop3 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM n lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wl3 lo sp L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wl3 lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  Z.of_nat (S f) = n -> n <= HL -> HL < 573 -> x10 = wz n ->
  R = build_tree_loop3 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t n ->
  evt usegs (ubt_loop3_post L s t T N HL HM lo FC DL DP BC OL SL MC R x9 x18 x21 x23 x27 sp gp tp F fc m0)
      (MS (ul3R L T n x1 t0 t1 t2 x9 x10 a1 a2 a3 a4 a5 a6 a7 x18 x19 x21 x23 x27 t3 t4 t5 t6 sp gp tp) F (wz BT_L3) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Ef Rn RHL Ex ER.
  - call (ubt_l3_trip L s t T N HL HM n lo FC DL HP DP BC OL SL MC 0%nat R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Ex. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = build_tree_loop3 0 _ _ _ |- _ => cbn [build_tree_loop3] in E; rename E into ER' end.
    replace (n - 1) with 0 by lia. unfold ul3R. replace (0 + 1) with 1 by lia.
    apply evt_done. unfold ubt_loop3_post, ul3R. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; assumption.
  - call (ubt_l3_trip L s t T N HL HM n lo FC DL HP DP BC OL SL MC (S f) R m).
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; exact Hxx]. }
    1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact BEL. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. } 1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Ex. } 1:{ exact ER. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    unfold ul3R.
    match goal with E : R = build_tree_loop3 (S f) _ _ _, HA : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                     HS : stk usegs ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N HL HM (n - 1) lo FC DL hp DP BC OL SL MC R m0);
        [exact HA| exact HD| exact HG| exact RDT| eassumption| exact LAY| exact MU| exact WM| exact HS| exact LO| exact BEL| exact AL4| exact RT1| exact RT2| exact RN
        | assumption| assumption| exact RFC| exact RDP| lia| lia| exact RHL| reflexivity| exact E] end.
Qed.
