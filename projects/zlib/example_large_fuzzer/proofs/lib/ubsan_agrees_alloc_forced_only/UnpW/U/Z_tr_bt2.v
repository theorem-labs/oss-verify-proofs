(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid Z_tr_bt1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefBuildTree1 RefBuildTree2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lxor_sign : forall a, 0 <= a < 2^63 -> Z.lxor a (2^63) = a + 2^63.
Proof.
  intros a H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 63 n) as [<-|]; [|apply andb_false_r].
  rewrite andb_true_r. rewrite Z.testbit_false by lia. rewrite Z.div_small by lia. reflexivity.
Qed.
Lemma l2node_mask : forall mc, -1 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor (mc mod 18446744073709551616) 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1)
  = (if mc <? 2 then mc + 1 else 0).
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|N1]; [reflexivity|]. destruct (Z.eq_dec mc 0) as [->|N0]; [reflexivity|]. destruct (Z.eq_dec mc 1) as [->|N2]; [reflexivity|].
  rewrite (Z.mod_small mc) by lia. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia.
  rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_ge mc 2)) by lia. reflexivity.
Qed.
Lemma l2node_mask_ge : forall mc, 2 <= mc < 2^31 - 1 ->
  Z.land ((0 - Z.b2z (Z.lxor mc 9223372036854775808 <? 9223372036854775810)) mod 18446744073709551616) (mc + 1) = 0.
Proof.
  intros mc H. change 9223372036854775808 with (2^63). rewrite lxor_sign by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.
Lemma swrap32_succ_m1 : forall mc, -1 <= mc < 2^31 - 1 -> bv_swrap 32 (mc mod 18446744073709551616 + 1) = mc + 1.
Proof.
  intros mc H. destruct (Z.eq_dec mc (-1)) as [->|NE]; [reflexivity|].
  rewrite Z.mod_small by lia. apply Z_dkit.bv_swrap32_id. lia.
Qed.

(* [comment removed for export] *)
Definition ubt2R (L : dlay) (T HL mc stp : Z) (x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) :=
  mkR ra sp gp tp (wz 1) (wz HL) (wz mc) s0 s1 (wz stp) (wz (dl_As L + 3008)) (wz (ONES - (dl_As L + 3008))) (wz (ONES - stp))
      (wz 2) (wz 572) (wz (dl_As L + 5308)) (wz (ONES - (dl_As L + 5308))) s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11
      x28 (wz mc) x30 x31.

Notation Wbt2 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5968)] (only parsing).

Definition ubt_l2_post (L : dlay) (s : deflate_state) (T N stp : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL mc : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x28 x30 x31 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (ubt2R L T HL mc stp x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4)
    /\ ((pcx = BT_L2 /\ HL < 2) \/ (pcx = BT_L2X /\ 2 <= HL)).

(* [comment removed for export] *)
Ltac ul2_close MU WM ARR HPA DPA GC GD :=
  let K3 := fresh "K3" in
  zs2; zs2; zs2;
  try (lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ (Z_to_bv 64 (?a + 0)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => reg_as (a + 0) a end);
  zstep; br_cases K3;
  (apply evt_done; unfold ubt_l2_post, ubt2R, bD_cells, BT_L2, BT_L2X; do 10 eexists;
   split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact ARR|]; split; [exact HPA|]; split; [exact DPA|];
   split; [exact GC|]; split; [close_cells GD|];
   first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]]).

Lemma ubt_l2_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc stp dsc HM OL SL node mc' : Z) (FC DL HP DP : arr) (h0 h1 h2 h3 h4 : list byte)
    (x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> stp mod 4 = 0 -> 0 <= HL < 2 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  (node, mc') = l2node mc ->
  evt usegs (ubt_l2_post L s T N stp (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (HL + 1) HM (arr_set DP node (wrap8 0))
               (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) mc'
               ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m)
      (MS (ubt2R L T HL mc stp x28 x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L2) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD F16 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LHP LDP SV ALS RHL Rmc ROL RSL ENODE.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  lay_open LAY. unfold ubt2R, BT_L2, bD_cells in *.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  assert (En : node = (if mc <? 2 then mc + 1 else 0) /\ mc' = (if mc <? 2 then mc + 1 else mc)).
  { unfold l2node in ENODE. destruct (mc <? 2); inversion ENODE; auto. }
  destruct En as [En Emc']. assert (Rnode : 0 <= node < 3) by (rewrite En; destruct (Z.ltb_spec mc 2); lia).
  assert (Rstp : 0 <= stp < 2^32) by (destruct SV as [[-> _]|(R & _)]; lia).
  zs2. rewrite swrap32_succ_m1 by lia. zs2. try reg_as (mc + 1 + 0) (mc + 1). zstep.
  br_cases K.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_lt _ _) K) in En, Emc'. subst node mc'.
    zs2. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. try reg_as (mc + 1 + 0) (mc + 1). zs2. zs2. zs2.
    rewrite l2node_mask by lia. rewrite (proj2 (Z.ltb_lt _ _) K).
    zs2. zs2. shl_norm. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) (mc + 1) ltac:(reflexivity).
    do 4 ustep BT_TRAP. do 4 ustep BT_TRAP.
    ct_store_fc ARR FC DL N T (mc + 1) (wrap16 1) ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) (mc + 1) (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zstep.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. ul2_close MU WM ARR HPA DPA GC GD.
    + br_false. lazymatch goal with H : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm (mc + 1) H ltac:(lia)) as [RDl Rsl] end.
      ustep BT_TRAP. zs2. ustep BT_TRAP. ustep BT_TRAP.
      zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zstep. zs2. ul2_close MU WM ARR HPA DPA GC GD.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge _ _)) in En, Emc' by lia. subst node mc'.
    zs2. try reg_as (mc + 0) mc.
    zs2. zstep. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. try reg_as (mc + 0) mc. zs2. zs2. zs2.
    rewrite l2node_mask_ge by lia.
    zs2. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) 0 ltac:(reflexivity).
    do 4 ustep BT_TRAP. do 4 ustep BT_TRAP.
    ct_store_fc ARR FC DL N T 0 (wrap16 1) ltac:(reflexivity).
    ustep BT_TRAP. ustep BT_TRAP. zs2.
    pb_store DPA DP 573 (dl_As L + 5308) 0 (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zstep.
    zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
    + subst stp. br_true. ul2_close MU WM ARR HPA DPA GC GD.
    + br_false. lazymatch goal with H : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm 0 H ltac:(lia)) as [RDl Rsl] end.
      change (0 * 4) with 0 in RDl. replace (stp + 0 + 2) with (stp + 2) in RDl by lia.
      ustep BT_TRAP. zs2. ustep BT_TRAP. ustep BT_TRAP.
      zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zstep. zs2. ul2_close MU WM ARR HPA DPA GC GD.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ubt_loop2_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc : Z) (DL BC : arr) (HM MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t5 t6 h0 h1 h2 h3 h4 FC' HP' HL' DP' OL' SL' mc' m',
    ms' = MS (mkR ra sp gp tp t0 (wz HL') t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (wz T) s7 s8 (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s11 t3 (wz mc') t5 t6)
             F (wz BT_L2X) fc None m' (seg_rom usegs)
    /\ munch (Wbt2 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC' DL HP' HL' HM DP' BC OL' SL' MC, mc')
    /\ arr_len FC' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ HL' = Z.max HL 2 /\ -1 <= mc' <= Z.max mc 2 /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.

Lemma ubt_loop2 : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL mc stp dsc HM OL SL MC : Z) (FC DL HP DP BC : arr) (h0 h1 h2 h3 h4 : list byte) (R : deflate_state * Z)
    (x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2 ^ 63 ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 3 <= N -> arr_len FC = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  stree_view t stp -> stp mod 4 = 0 -> 0 <= HL < 2^31 -> -1 <= mc < 286 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = build_tree_loop2 2 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t mc ->
  evt usegs (ubt_loop2_post L s t T N HL mc DL BC HM MC R ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11 F fc m)
      (MS (ubt1R L T (sd_elems t) (sd_elems t) mc stp x30 x31 ra sp gp tp s0 s1 s2 s3 s4 s5 s7 s8 s11) F (wz BT_L1X) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA GC GD F16 MI LAY Bsp Rsp AL4 RT1 RT2 RN LFC LHP LDP SV ALS RHL Rmc ROL RSL ER.
  pose proof (munch_refl (Wbt2 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. unfold ubt1R, BT_L1X.
  assert (Rstp : 0 <= stp < 2^32) by (destruct SV as [[-> _]|(R0 & _)]; lia).
  zs2. zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    rewrite RefBuildTree2.L2_step in ER by lia. destruct (RefBuildTree2.l2node mc) as [node mc1] eqn:E1. symmetry in E1.
    zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. rewrite (zb_lxor_ones (dl_As L + 3008)) by lia.
    zstep. br_false.
    zs2. zs2. rewrite (zb_lxor_ones stp) by lia. zs2. zs2. zs2. zs2. zs2. zs2. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia. zs2. zs2. try reg_as (mc + 0) mc. zs2.
    assert (Rn1 : -1 <= mc1 <= Z.max mc 2) by (unfold RefBuildTree2.l2node in E1; destruct (Z.ltb_spec mc 2); inversion E1; lia).
    assert (ROL1 : 0 <= wrap64 (OL - 1) < 2^64) by apply wrap64_range.
    assert (RSL1 : 0 <= (if stree_has t then wrap64 (SL - stree_Len t node) else SL) < 2^64) by (destruct (stree_has t); [apply wrap64_range| exact RSL]).
    call (ubt_l2_iter L s t T N HL mc stp dsc HM OL SL node mc1 FC DL HP DP h0 h1 h2 h3 h4).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact F16. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Bsp. } 1:{ exact Rsp. }
    1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact SV. } 1:{ exact ALS. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact E1. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> K1]|[-> K1]] end.
    + (* [comment removed for export] *)
      rewrite RefBuildTree2.L2_step in ER by lia. destruct (RefBuildTree2.l2node mc1) as [node2 mc2] eqn:E2. symmetry in E2.
      assert (Rn2 : -1 <= mc2 <= Z.max mc 2) by (unfold RefBuildTree2.l2node in E2; destruct (Z.ltb_spec mc1 2); inversion E2; lia).
      unfold ubt2R.
      match goal with HT : u8arr usegs ?mm T _, HA : u32arr usegs ?mm _ _, HD : u8arr usegs ?mm (dl_As L + 5308) _, HG : rw_cells usegs ?mm (dl_As L + 5300) _,
                       HGD : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells _ _ _ _ ?g0 ?g1 ?g2 ?g3 ?g4), HF : rw_cells usegs ?mm (bv_unsigned sp + 16) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (ubt_l2_iter L s t T N (HL + 1) mc1 stp dsc HM (wrap64 (OL - 1)) (if stree_has t then wrap64 (SL - stree_Len t node) else SL) node2 mc2
                (arr_set FC node (wrap16 1)) DL (arr_set HP (HL + 1) node) (arr_set DP node (wrap8 0)) g0 g1 g2 g3 g4);
        [exact HT| exact HA| exact HD| exact HG| exact HGD| exact HF| eassumption| exact LAY| exact Bsp| exact Rsp| exact AL4| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LFC| rewrite arr_len_set; exact LHP
        | rewrite arr_len_set; exact LDP| exact SV| exact ALS| lia| lia| exact ROL1| exact RSL1| exact E2|] end.
      match goal with H : _ \/ _ |- _ => destruct H as [[-> K2]|[-> K2]] end; [exfalso; lia|].
      cbn [build_tree_loop2] in ER.
      apply evt_done. unfold ubt_loop2_post, ubt2R. do 26 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [apply wrap64_range|]. destruct (stree_has t); [apply wrap64_range| exact RSL].
    + rewrite RefBuildTree2.L2_out in ER by lia.
      apply evt_done. unfold ubt_loop2_post, ubt2R. do 26 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
      split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
      split; [rewrite !arr_len_set; exact LFC|]. split; [rewrite !arr_len_set; exact LHP|]. split; [rewrite !arr_len_set; exact LDP|].
      split; [lia|]. split; [lia|]. split; [exact ROL1| exact RSL1].
  - rewrite RefBuildTree2.L2_out in ER by lia.
    apply evt_done. unfold ubt_loop2_post. do 26 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|].
    split; [exact GC|]. split; [exact GD|]. split; [exact ER|].
    split; [exact LFC|]. split; [exact LHP|]. split; [exact LDP|]. split; [lia|]. split; [lia|]. split; [exact ROL| exact RSL].
Qed.
