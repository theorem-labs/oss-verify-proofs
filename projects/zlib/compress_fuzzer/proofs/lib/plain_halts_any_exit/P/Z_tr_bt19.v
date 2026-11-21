(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3
     Z_tr_bt1 Z_tr_bt2 Z_tr_bt3 Z_tr_bt6 Z_tr_bt7 Z_tr_bt10 Z_tr_bt11 Z_tr_bt13 Z_tr_bt16 Z_tr_bt17 Z_tr_bt18.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel RefBuildTree1.

From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_tr_bt19p.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Notation WBT L T N dsc lo sp := [(lo%Z, bv_unsigned sp); (T%Z, (T + 4 * N)%Z); ((dsc + 8)%Z, (dsc + 12)%Z); (dl_As L + 2976, dl_As L + 5968)] (only parsing).

Definition body_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh : list byte) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FC' DL' HP' DP' BC' : arr) (OL' SL' hm mc : Z) (g0 g1 g2 g3 g4 : list byte) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (WBT L T N dsc lo sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m' /\ stk psegs m' lo (bv_unsigned sp)
    /\ u8arr psegs m' T (u16s (avct FC' DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells psegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells psegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))]
    /\ R = bt_upd s t FC' DL' HP' 1 hm DP' BC' OL' SL' mc
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16.

Lemma build_tree_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr psegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr psegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr psegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells psegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells psegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (SDA t))] ->
  mem_inv psegs m -> relro_clean m -> dlay_ok L ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 144 -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  R = build_tree s t ->
  evt psegs (body_post L s t T N dsc lo hh R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC -> -> ER0.
  unfold Z_BUILD_TREE.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5c000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  pose proof (toff_tsize t) as Rtt. pose proof (RefBuildTree1.elems_range t) as RE. pose proof (RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (RML : 7 <= sd_max_length t <= 15 /\ 0 <= sd_extra_base t <= 257) by (destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS, LITERALS; lia).
  pose proof (Z_tr_bt19p.SDA_range t) as RSDA. pose proof (Z_tr_bt19p.STP_range t) as RSTP. pose proof (XP_range t) as RXP.
  destruct (safe_s0 s t SAFE) as (RFC0 & ROL0 & RSL0). rewrite <- EN in RFC0.
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.

  unfold bD_cells in GD.

  carve_frame 144%nat STK.
  zstep.
  do 13 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  zs2. zs2. zs2. zs2. zs2. zs2.
  pose proof (sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold sd_cells in Gsd.
  zs2. zs2. clear Gsd.
  zs2. zs2. zstep. zstep. zs2. zstep. br_false.
  zs2. zs2. zs2. zs2. shl_norm. zs2. zs2. zstep.
  reg_as (T + 2 + sd_elems t * 4) (T + 4 * sd_elems t + 2). reg_as (dl_As L + 5308) (dl_As L + 5308 + 0). reg_as (T + 2) (T + 4 * 0 + 2).

  name_term R1 ER1 (L1 t (btX0 s t) 0 (-1)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (bt_loop1 (Z.to_nat (sd_elems t) - 1) L s t T N dsc (STP t) (tree_fc s t) (ds_bl_count s) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) R1 mm
                   (tree_dl s t) (ds_heap s) 0 (ds_depth s) 0 (-1)) end.
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact RFC0. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ unfold btX0 in ER1. exact ER1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) |- _ =>
    rename H into ER1';
    assert (E1 : build_tree_loop1 (Z.to_nat (sd_elems t)) (btX0 s t) t (sd_elems t) 0 (-1) = (bt_upd s t (tree_fc s t) dl1 hp1 hl1 573 dp1 (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t), mc1))
      by (rewrite <- ER1', ER1; unfold L1; rewrite Z.sub_0_r; reflexivity);
    clear ER1 ER1';
    pose proof (avct_zlength (tree_fc s t) dl1 N ltac:(lia)) as LCT1; pose proof (av32_zlength hp1 573 ltac:(lia)) as L32_1; pose proof (av8_zlength dp1 573 ltac:(lia)) as L8_1 end.

  lazymatch type of E1 with _ = (?X1, ?mc1) => name_term R2 ER2 (build_tree_loop2 2 X1 t mc1) end.
  unfold bt1R.
  lazymatch type of E1 with _ = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) =>
    call (bt_loop2 L s t T N hl1 mc1 dsc (STP t) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) (tree_fc s t) dl1 hp1 dp1 (ds_bl_count s) g0 g1 g2 g3 g4 R2) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. } 1:{ apply stree_view_of. } 1:{ lia. } 1:{ lia. } 1:{ exact ROL0. } 1:{ exact RSL0. }
  1:{ exact ER2. }
  match goal with H : R2 = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) |- _ =>
    rename H into ER2'; pose proof ER2' as E2; rewrite ER2 in E2; clear ER2 ER2' R2;
    pose proof (avct_zlength fc2 dl1 N ltac:(lia)) as LCT2; pose proof (av32_zlength hp2 573 ltac:(lia)) as L32_2; pose proof (av8_zlength dp2 573 ltac:(lia)) as L8_2 end.
  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG; rename HG into GD2 end.
  destruct (safe_s3 s t SAFE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2) as (PQ2 & RDP2 & RFC2 & S7). rewrite <- EN in PQ2, RFC2.

  zs2. zstep. zs2. zs2. zs2.
  lazymatch type of E2 with _ = (bt_upd _ _ _ _ _ ?hl2 _ _ _ _ _ _, _) => rewrite (srliw1 hl2) by lia; change (hl2 / 2 ^ 1) with (hl2 / 2) end.
  zs2. zs2. zs2. zstep.

  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    name_term R3 ER3 (build_tree_loop3 (Z.to_nat (hl2 / 2)) (bt_upd s t fc2 dl1 hp2 hl2 573 dp2 (ds_bl_count s) ol2 sl2 mc2) t (hl2 / 2));
    pose proof ER3 as ER3S; replace (Z.to_nat (hl2 / 2)) with (S (Z.to_nat (hl2 / 2) - 1)) in ER3S by lia end.
  lazymatch goal with HT : u8arr psegs ?mm T (u16s (avct ?fc2 ?dl1 N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E2 with _ = (bt_upd _ _ _ _ ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    call (bt_loop3 (Z.to_nat (hl2 / 2) - 1) L s t T N hl2 573 (hl2 / 2) fc2 dl1 hp2 dp2 (ds_bl_count s) ol2 sl2 mc2 R3 mm) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. }
  1:{ eapply ct_readable_rw; [eassumption| lia| lia| cbn [disjoint_from]; lia]. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
  1:{ exact PQ2. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. } 1:{ lia. } 1:{ exact ER3S. }
  match goal with H : R3 = bt_upd _ _ _ _ ?hp3 _ _ _ _ _ _ _ |- _ =>
    rename H into E3; clear ER3S; pose proof (av32_zlength hp3 573 ltac:(lia)) as L32_3 end.

  unfold l3R. zstep. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zstep.

  lazymatch type of E3 with R3 = ?X3 => name_term R4 ER4 (build_tree_loop4 573 X3 t (sd_elems t)) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E3 with R3 = bt_upd _ _ ?fc2 ?dl1 ?hp3 ?hl2 _ ?dp2 _ ?ol2 ?sl2 ?mc2 =>
    call (bt_loop4 573 L s t T N hl2 573 (sd_elems t) dsc mc2 fc2 dl1 hp3 dp2 (ds_bl_count s) ol2 sl2 mc2 R4 mm) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER4. }
  match goal with H : R4 = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ _ _ _ |- _ =>
    rename H into ER4'; pose proof ER4' as E4; rewrite ER4 in E4; clear ER4 ER4';
    pose proof (avct_zlength fc4 dl4 N ltac:(lia)) as LCT4; pose proof (av32_zlength hp4 573 ltac:(lia)) as L32_4; pose proof (av8_zlength dp4 573 ltac:(lia)) as L8_4 end.

  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    destruct (S7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 E4 ltac:(assumption) ltac:(lia)) as (RHP7 & RDL7 & OK1 & OK23 & LEN15) end.
  rewrite <- EN in RHP7, RDL7. clear S7.

  pose proof (sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold sd_cells in Gsd.
  lazymatch type of E4 with _ = bt_upd _ _ _ _ _ 1 ?hm4 _ _ _ _ _ =>
    match goal with HG : rw_cells psegs _ (dl_As L + 5300) [C4 (wz 1); C4 (wz hm4)] |- _ =>
      replace (wz hm4) with (wz (hm4 - 1 + 1)) in HG by (f_equal; lia) end end.
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?rest) =>
    destruct (proj1 (rw_cells_app_iff mm A [c0] (c1 :: rest)) FR) as [F0 FR1]; clear FR;
    destruct (proj1 (rw_cells_app_iff mm _ [c1] rest) FR1) as [F1 F2]; clear FR1;
    cbn [cells_size csize Nat.add] in F1, F2 end.
  change (Z.of_nat 8) with 8 in F1. change (Z.of_nat 8) with 8 in F2. change (Z.of_nat 32) with 32 in F2.
  replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) in F1 by lia.
  replace (bv_unsigned sp + -144 + 8 + 32) with (bv_unsigned sp + -104) in F2 by lia.

  pose proof E3 as E3x. rewrite ER3 in E3x.
  rewrite (build_tree_flat s t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2 E3x E4) in ER0.
  unfold l4R.
  lazymatch goal with HB : rw_cells psegs ?mm (bv_unsigned sp + -136) [CB 32 ?jk] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of GD2 with rw_cells _ _ _ [CB 7 ?k0; _; _; _; _; CB 4 ?k1; _; _; _; _; _; CB 2 ?k2; _; CB 4 ?k3; _; _; CB 4 ?k4; _] =>
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
  lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (wz ?nd) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    call (partB L s t T N (hm4 - 1) nd dsc (SDA t) mc2 (STP t) (XP t) ol2 sl2 fc4 dl4 hp4 dp4 (ds_bl_count s) hh k0 k1 k2 k3 k4 jk R) end end end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD2. } 1:{ exact Gdsc. } 1:{ exact Gsd. }
  1:{ rewrite ESP. exact F0. } 1:{ rewrite ESP. replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) by lia. exact F1. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ lia. } 1:{ lia. } 1:{ exact EN. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact LBC. }
  1:{ apply xbits_view_of. } 1:{ apply stree_view_n_of. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Edsc. }
  1:{ lia. } 1:{ assumption. } 1:{ lia. } 1:{ exact RHP7. } 1:{ exact RDL7. } 1:{ assumption. } 1:{ lia. } 1:{ lia. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact LEN15. } 1:{ exact ER0. }
  rewrite ESP in *.

  do 13 zs2. zstep. zstep.

  release_frame F0 STK (bv_unsigned sp + -136).
  match goal with HF : rw_cells psegs _ (bv_unsigned sp + -144 + 8) [CB 32 _] |- _ =>
    replace (bv_unsigned sp + -144 + 8) with (bv_unsigned sp + -136) in HF by lia; release_frame HF STK (bv_unsigned sp + -104) end.
  release_frame F2 STK (bv_unsigned sp).
  match goal with HG : rw_cells psegs _ (dl_As L + 5881) (bD_cells _ _ ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HR : R = bt_upd s t ?fc ?dl ?hp 1 ?hm ?dp ?bc _ _ ?mc |- _ =>
    apply evt_done; unfold body_post; do 15 eexists; exists fc, dl, hp, dp, bc, ol, sl, hm, mc, k0, k1, k2, k3, k4; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact STK|];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [exact HG|];
    split; [eassumption|]; split; [exact HR|] end.
  repeat (split; [first [assumption | rewrite arr_len_set; assumption] |]). first [assumption | rewrite arr_len_set; assumption].
Qed.

Ltac bt_tree_lens LENS t :=
  lazymatch t with
  | TL => constr:(conj (ln_ltf _ LENS) (ln_ltd _ LENS))
  | TD => constr:(conj (ln_dtf _ LENS) (ln_dtd _ LENS))
  | TB => constr:(conj (ln_btf _ LENS) (ln_btd _ LENS))
  end.

Lemma dsB_cells_split : forall L s h1 h2 h3,
  dsB_cells L s h1 h2 h3
  = [C8 (wz (dl_As L + 212)); C4 (wz (ds_l_max_code s)); CB 4 h1; C8 (wz Z_SL_DESC)]
    ++ [C8 (wz (dl_As L + 2504)); C4 (wz (ds_d_max_code s)); CB 4 h2; C8 (wz Z_SD_DESC)]
    ++ [C8 (wz (dl_As L + 2748)); C4 (wz (ds_bl_max_code s)); CB 4 h3; C8 (wz Z_SBL_DESC)].
Proof. intros. reflexivity. Qed.

Lemma build_tree_spec : build_tree_stmt.
Proof.
  unfold build_tree_stmt. intros until m. intros ST MI RC STK LO AL BEL SAFE Ea0 Ea1.
  open_DST ST. pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  destruct GB as (h1 & h2 & h3 & GB). destruct GD as (g0 & g1 & g2 & g3 & g4 & GD).
  rewrite dsB_cells_split in GB.
  destruct (proj1 (rw_cells_app_iff _ _ _ _) GB) as [GBl GB23]. destruct (proj1 (rw_cells_app_iff _ _ _ _) GB23) as [GBd GBb]. clear GB GB23.
  cbn [cells_size csize Nat.add] in GBd, GBb. change (Z.of_nat 24) with 24 in GBd, GBb.
  replace (dl_As L + 2904 + 24 + 24) with (dl_As L + 2952) in GBb by lia. replace (dl_As L + 2904 + 24) with (dl_As L + 2928) in GBd by lia.
  unfold dsC, dsC_cells in GC. change (dsD_cells L s g0 g1 g2 g3 g4) with (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) in GD.
  unfold dblc, u16arr in Gblc. unfold dheap in Gheap. unfold ddep in Gdep.
  destruct t.
  -
    unfold dlt, u16arr in Glt.
    eapply evt_mono.
    { eapply (build_tree_body L s TL (dl_As L + 212) 573 (dl_As L + 2904) lo h1 g0 g1 g2 g3 g4 (build_tree s TL)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Glt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBl. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_ltf _ LENS). } 1:{ exact (ln_ltd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBl' & ER & LFC' & LDL' & LHP' & LDP' & LBC').

    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl'| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact ARR'.
    + exact Gdt.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold ddt, u16arr in Gdt.
    eapply evt_mono.
    { eapply (build_tree_body L s TD (dl_As L + 2504) 61 (dl_As L + 2928) lo h2 g0 g1 g2 g3 g4 (build_tree s TD)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gdt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBd. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_dtf _ LENS). } 1:{ exact (ln_dtd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBd' & ER & LFC' & LDL' & LHP' & LDP' & LBC').

    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd'| exact GBb| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact ARR'.
    + exact Gbt.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
  -
    unfold dbt, u16arr in Gbt.
    eapply evt_mono.
    { eapply (build_tree_body L s TB (dl_As L + 2748) 39 (dl_As L + 2952) lo h3 g0 g1 g2 g3 g4 (build_tree s TB)
                ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
      1:{ exact Gbt. } 1:{ exact Gheap. } 1:{ exact Gdep. } 1:{ exact Gblc. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact GBb. }
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ unfold Z_BT_STACK in LO. exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_btf _ LENS). } 1:{ exact (ln_btd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBb' & ER & LFC' & LDL' & LHP' & LDP' & LBC').

    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport psegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport psegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
    unfold build_tree_post. do 16 eexists. split; [reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; unfold sub_fp; cbn [outside]; intros; lia|].
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    rewrite ER. constructor.
    + exact GA.
    + exists h1, h2, h3. rewrite dsB_cells_split.
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2928)); [exact GBl| | cbn; lia].
      apply (rw_cells_join2 _ _ _ _ (dl_As L + 2952)); [exact GBd| exact GBb'| cbn; lia].
    + exact GC'.
    + exists k0, k1, k2, k3, k4. exact GD'.
    + exact Glt.
    + exact Gdt.
    + exact ARR'.
    + exact BLC'.
    + exact HPA'.
    + exact DPA'.
    + exact Gwin.
    + exact Gprev.
    + exact Ghead.
    + exact Gpend.
    + destruct LENS; constructor; cbn -[arr_len Z.add]; assumption.
    + exact LAY.
Qed.
