(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_scan1 Z_tr_bt_mid Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

Definition GL2_HEAD : Z := 0x1d4b8.
Definition GL2_FIND : Z := 0x1d4bc.
Definition GL2_FOUND : Z := 0x1d4e4.
Definition GL2_EXIT : Z := 0x1d524.

(* [comment removed for export] *)
Definition ugl2R (L : dlay) (T ovf mc ML : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz ML) (wz ML) (wz (dl_As L + 2976 + ML * 2)) (wz 16) (wz (ONES - (dl_As L + 2976))) (wz ovf)
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 (wz 16) t6.

(* [comment removed for export] *)
Lemma ugl2_find : forall (d : nat) (P : machine_state -> Prop) (L : dlay) (T ovf mc ML b B1 r : Z) (BC : arr)
    (sp ra gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L ->
  Z.of_nat d = b - r -> 0 <= r -> b < 15 -> (forall j, r < j <= b -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 -> B1 = b + 1 ->
  evt usegs P (MS (ugl2R L T ovf mc ML sp ra gp tp (wz (r + 1)) (wz r) (wz (dl_As L + 2976 + r * 2)) s0 s1 s2 s4 s5 s6 s7 s9 s11 (wz (arr_get BC r)) t4 t6) F (wz 0x1d4e4) fc None m (seg_rom usegs)) ->
  evt usegs P (MS (ugl2R L T ovf mc ML sp ra gp tp (wz B1) t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d4bc) fc None m (seg_rom usegs)).
Proof.
  induction d as [|d IH]; intros until m; intros BLC MI LAY Ed Rr Rb Z0 NZ RV EB1 K; subst B1.
  - assert (b = r) by lia. subst b.
    pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read usegs m _ (av16 BC 16) r _ (wa (dl_As L + 2976 + r * 2)) BLC (av16_nth BC 16 r ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    unfold ugl2R. zs2. try rewrite (bv_swrap32_id (r + 1 + -1)) by lia. reg_as (r + 1 + -1) r. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
    zstep. br_cases K2; [|exfalso; lia].
    exact K.
  - pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read usegs m _ (av16 BC 16) b _ (wa (dl_As L + 2976 + b * 2)) BLC (av16_nth BC 16 b ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    rewrite (Z0 b ltac:(lia)) in RDb.
    unfold ugl2R. zs2. try rewrite (bv_swrap32_id (b + 1 + -1)) by lia. reg_as (b + 1 + -1) b. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
    zstep. br_cases K2; [exfalso; lia|].
    zs2. try rewrite (bv_swrap32_id (b + 1 + -2)) by lia. zs2. zstep. br_true.
    eapply (IH P L T ovf mc ML (b - 1) b r BC); [exact BLC| exact MI| exact LAY| lia| exact Rr| lia| intros j Hj; apply Z0; lia| exact NZ| exact RV| lia| exact K].
Qed.

Notation uWg2 L := [(dl_As L + 2976, dl_As L + 3008)] (only parsing).

(* [comment removed for export] *)
Definition ugl2_iter_post (L : dlay) (T ovf mc ML : Z) (BC' : arr)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3 pcx m',
    ms' = MS (ugl2R L T (ovf - 2) mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWg2 L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ ((pcx = 0x1d4b8 /\ 0 < ovf - 2) \/ (pcx = 0x1d524 /\ ovf - 2 <= 0)).

Lemma ugl2_iter : forall (L : dlay) (T ovf mc ML r : Z) (BC : arr)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> arr_len BC = 16 ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> 0 <= r <= ML - 1 -> (forall j, r < j <= ML - 1 -> arr_get BC j = 0) -> arr_get BC r <> 0 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  evt usegs (ugl2_iter_post L T ovf mc ML (bl_adj ML BC r) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 F fc m)
      (MS (ugl2R L T ovf mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d4b8) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC MI LAY LBC RML Ro Rr Z0 NZ RBC.
  pose proof (munch_refl (uWg2 L) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof (RBC r ltac:(lia)) as RV.
  unfold ugl2R. zs2.
  eapply (ugl2_find (Z.to_nat (ML - 1 - r)) _ L T ovf mc ML (ML - 1) ML r BC); [exact BLC| exact MI| exact LAY| lia| lia| lia| exact Z0| exact NZ| exact RV| lia|].
  pose proof LAY as LAY0. lay_open LAY0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold ugl2R. zs2.
  ua16_store BLC BC 16 (dl_As L + 2976) r (wrap16 (arr_get BC r - 1)) ltac:(apply le2_wrap16; lia).
  set (BC1 := arr_set BC r (wrap16 (arr_get BC r - 1))) in *.
  assert (RBC1 : forall i, 0 <= i < 16 -> 0 <= arr_get BC1 i < 65536) by (subst BC1; apply arr_set_range16; exact RBC).
  match goal with H : u8arr usegs ?mm _ (u16s (av16 BC1 16)) |- _ =>
    pose proof (u16arr_read usegs mm _ (av16 BC1 16) (r + 1) _ (wa (dl_As L + 2976 + (r + 1) * 2)) H (av16_nth BC1 16 (r + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
  ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2.
  ua16_store BLC BC1 16 (dl_As L + 2976) (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2)) ltac:(apply le2_add_sx16).
  set (BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2))) in *.
  assert (RBC2 : forall i, 0 <= i < 16 -> 0 <= arr_get BC2 i < 65536) by (subst BC2; apply arr_set_range16; exact RBC1).
  match goal with H : u8arr usegs ?mm _ (u16s (av16 BC2 16)) |- _ =>
    pose proof (u16arr_read usegs mm _ (av16 BC2 16) ML _ (wa (dl_As L + 2976 + ML * 2)) H (av16_nth BC2 16 ML ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
  zs2. zs2. zs2. try rewrite (bv_swrap32_id (ovf + -2)) by lia.
  ua16_store BLC BC2 16 (dl_As L + 2976) ML (wrap16 (arr_get BC2 ML - 1)) ltac:(replace (arr_get BC2 ML - 1) with (arr_get BC2 ML + -1) by lia; apply le2_add_sx16).
  ustep BT_TRAP. zs2. zstep.
  assert (EBA : bl_adj ML BC r = arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1))) by reflexivity.
  br_cases K; reg_as (ovf + -2) (ovf - 2).
  - apply evt_done. unfold ugl2_iter_post, ugl2R. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
  - apply evt_done. unfold ugl2_iter_post, ugl2R. do 6 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].
Qed.

(* [comment removed for export] *)
Definition ugl2_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL : Z) (R : deflate_state)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 t3 BC' ovf' m',
    ms' = MS (ugl2R L T ovf' mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d524) fc None m' (seg_rom usegs)
    /\ munch (uWg2 L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ R = bt_upd s t FC DL HP HL HM DP BC' OL SL mc
    /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536).

Lemma ugl2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T ovf mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL : Z) (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> munch (uWg2 L) m0 m -> wmono usegs m0 m -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> ovf <= 2 * Z.of_nat f ->
  R = gen_bitlen_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ML ovf ->
  gb2_ok ML f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ovf ->
  evt usegs (ugl2_loop_post L s t T mc ML FC DL HP HL HM DP OL SL R sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t4 t6 F fc m0)
      (MS (ugl2R L T ovf mc ML sp ra gp tp t0 t1 t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t6) F (wz 0x1d4b8) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros BLC MI LAY MU WM LBC RBC RML Ro Hf ER OK.
  { exfalso. lia. }
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (GL2_step t ML) in ER. destruct (gb2_ok_step t ML f s FC DL HP HL HM DP BC OL SL mc ovf OK) as [Hr OK'].
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) (ML - 1)) in *.
  destruct (find_char t s FC DL HP HL HM DP BC OL SL mc ML r eq_refl Hr ltac:(lia)) as (Hr1 & Z0 & NZ).
  call (ugl2_iter L T ovf mc ML r BC sp).
  1:{ exact BLC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RML. } 1:{ exact Ro. } 1:{ lia. } 1:{ exact Z0. } 1:{ exact NZ. } 1:{ exact RBC. }
  pose proof (av16_zlength (bl_adj ML BC r) 16 ltac:(lia)) as L16'.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - rewrite (proj2 (Z.ltb_lt 0 (ovf - 2)) K) in ER.
    eapply (IH L s t T (ovf - 2) mc ML FC DL HP HL HM DP (bl_adj ML BC r) OL SL R m0);
      [eassumption| eassumption| exact LAY| exact MU| exact WM| rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC| exact RML| lia| lia| exact ER| apply OK'; exact K].
  - rewrite (proj2 (Z.ltb_ge 0 (ovf - 2))) in ER by lia.
    apply evt_done. unfold ugl2_loop_post. do 4 eexists. exists (bl_adj ML BC r), (ovf - 2). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
    split; [rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC].
Qed.
