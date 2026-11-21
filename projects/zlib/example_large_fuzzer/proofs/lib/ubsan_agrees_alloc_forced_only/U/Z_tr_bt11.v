(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_tr_bt19p.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel RefBuildTree1 RefBuildTree2.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid Z_tr_bt1 Z_tr_bt2 Z_tr_bt3 Z_tr_bt6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)

Lemma toff_mod4 : forall t, toff t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Lemma bt_desc_mod8 : forall t, bt_desc t mod 8 = 0. Proof. destruct t; reflexivity. Qed.

Lemma dlay_below_lower : forall L lo hi hi', dlay_below L lo hi -> hi' <= hi -> dlay_below L lo hi'.
Proof. unfold dlay_below. intros. lia. Qed.
Lemma STP_mod4 : forall t, Z_tr_bt_mid.STP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
(* [comment removed for export] *)
Lemma srliw1 : forall c, 0 <= c < 65536 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 c) 1) = c / 2 ^ 1.
Proof.
  intros c Hc. unfold bv_wrap, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. rewrite Z.mod_small by lia.
  rewrite Z.shiftr_div_pow2 by lia. apply Z_dkit.bv_swrap32_id. change (2 ^ 1) with 2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma frame_split4 : forall m A j16 v1 v2 v3 v4 v5 v6 j40 rest,
  rw_cells usegs m A (CB 16 j16 :: C8 v1 :: C8 v2 :: C8 v3 :: C8 v4 :: C8 v5 :: C8 v6 :: CB 40 j40 :: rest) ->
  exists j8 j32, rw_cells usegs m A [CB 16 j16] /\ rw_cells usegs m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6]
                 /\ rw_cells usegs m (A + 64) [CB 8 j8] /\ rw_cells usegs m (A + 72) (CB 32 j32 :: rest).
Proof.
  intros m A j16 v1 v2 v3 v4 v5 v6 j40 rest H.
  apply (rw_cells_split_CB usegs m A [CB 16 j16; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] 40 j40 rest [8; 32]%nat) in H; [|reflexivity].
  cbn [mk_CB_cells app] in H.
  exists (firstn 8 j40), (firstn 32 (skipn 8 j40)).
  destruct (Z_tr_bt_mid.rw_cells_split2 m A [CB 16 j16] _ (A + 16) H ltac:(reflexivity)) as [H0 H1].
  destruct (Z_tr_bt_mid.rw_cells_split2 m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] _ (A + 64) H1 ltac:(cbn; lia)) as [H1' H2].
  destruct (Z_tr_bt_mid.rw_cells_split2 m (A + 64) [CB 8 (firstn 8 j40)] _ (A + 72) H2 ltac:(cbn; lia)) as [H2' H3].
  split; [exact H0|]. split; [exact H1'|]. split; [exact H2'| exact H3].
Qed.

(* [comment removed for export] *)
Lemma frame_join4 : forall m A j0 mc v1 v2 v3 v4 v5 v6 h nc c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13,
  rw_cells usegs m A [CB 8 j0; C8 mc] -> rw_cells usegs m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] ->
  rw_cells usegs m (A + 64) [C8 h] ->
  rw_cells usegs m (A + 72) [CB 32 nc; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13] ->
  rw_cells usegs m A [CB 8 j0; C8 mc; C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6; C8 h;
                      CB 32 nc; C8 c1; C8 c2; C8 c3; C8 c4; C8 c5; C8 c6; C8 c7; C8 c8; C8 c9; C8 c10; C8 c11; C8 c12; C8 c13].
Proof.
  intros until c13. intros H0 H1 H2 H3.
  pose proof (Z_tr_bt_mid.rw_cells_join2 m (A + 64) [C8 h] _ (A + 72) H2 H3 ltac:(cbn; lia)) as H23.
  pose proof (Z_tr_bt_mid.rw_cells_join2 m (A + 16) [C8 v1; C8 v2; C8 v3; C8 v4; C8 v5; C8 v6] _ (A + 64) H1 H23 ltac:(cbn; lia)) as H123.
  exact (Z_tr_bt_mid.rw_cells_join2 m A [CB 8 j0; C8 mc] _ (A + 16) H0 H123 ltac:(cbn; lia)).
Qed.

(* [comment removed for export] *)
Tactic Notation "callx" uconstr(SPEC) "drop" ne_hyp_list(HS) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | clear HS; post_call segs m ]
  end.
(* [comment removed for export] *)
Ltac name_groups A Hh D G :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with H : u8arr usegs mm _ (u16s (avct _ _ _)) |- _ => rename H into A end;
    match goal with H : u32arr usegs mm _ _ |- _ => rename H into Hh end;
    match goal with H : u8arr usegs mm _ (av8 _ _) |- _ => rename H into D end;
    match goal with H : rw_cells usegs mm (dl_As _ + 5300) _ |- _ => rename H into G end
  end.

Lemma bt_front : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr usegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr usegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (Z_tr_bt_mid.SDA t))] ->
  mem_inv usegs m -> relro_clean m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  evt usegs (bt_mid_post L s t T N dsc lo hh ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC -> ->.
  unfold Z_BUILD_TREE. unfold Z_BT_STACK in LO.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. clear Rw Rp Rh Rb Bw Bp Bh Bb.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5f000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  assert (ALs : dl_As L mod 16 = 0) by (destruct (lo_s _ LAY) as (_ & X & _); exact X).
  pose proof (toff_tsize t) as Rtt. pose proof (toff_mod4 t) as Rt4. pose proof (bt_desc_mod8 t) as Rd8.
  pose proof (RefBuildTree1.elems_range t) as RE. pose proof (RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (RML : 7 <= sd_max_length t <= 15 /\ 0 <= sd_extra_base t <= 257) by (destruct t; cbn; unfold MAX_BITS, MAX_BL_BITS, LITERALS; lia).
  pose proof (Z_tr_bt_mid.SDA_range t) as RSDA. pose proof (Z_tr_bt_mid.SDA_al8 t) as ASDA. pose proof (Z_tr_bt_mid.STP_range t) as RSTP. pose proof (Z_tr_bt_mid.XP_range t) as RXP.
  destruct (Z_tr_bt19p.safe_s0 s t SAFE) as (RFC0 & ROL0 & RSL0). rewrite <- EN in RFC0.
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.
  (* [comment removed for export] *)
  unfold bD_cells in GD.
  (* [comment removed for export] *)
  pose proof (conj ARR (conj HPA (conj DPA (conj BLC GD)))) as BIG. clear ARR HPA DPA BLC GD.
  pose proof (munch_refl [(bv_unsigned sp + -208, bv_unsigned sp); (dl_As L + 5300, dl_As L + 5308)] m) as MUp.
  (* [comment removed for export] *)
  carve_frame 208%nat STK.
  zstep.
  do 13 zstep.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  uwalk 0x1ce40 BT_TRAP. at_pc 0x1ce40.

  pose proof (Z_tr_bt_mid.sdesc_relro t _ (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia))) as Gsd. unfold Z_tr_bt_mid.sd_cells in Gsd.
  zs2. zs2. clear Gsd.
  uwalk 0x1ce80 BT_TRAP. at_pc 0x1ce80.

  zstep. br_false.
  uwalk 0x1cec0 BT_TRAP. at_pc 0x1cec0. zstep.

  destruct BIG as (ARR & HPA & DPA & BLC & GD).
  lazymatch type of MUp with munch ?W ?ma ?mb =>
    apply (u8arr_transport usegs W ma mb) in ARR; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u32arr_transport usegs W ma mb) in HPA; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u8arr_transport usegs W ma mb) in DPA; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (u8arr_transport usegs W ma mb) in BLC; [| exact MUp| exact WM| cbn [disjoint_from]; lia];
    apply (rw_cells_transport usegs W ma mb) in GD; [| exact MUp| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
  clear MUp.
  (* [comment removed for export] *)
  rewrite (zb_lxor_ones (dl_As L + 3008)) by lia. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
  rewrite (zb_lxor_ones T) in FR by lia.
  assert (ALT : T mod 4 = 0) by (rewrite ET; Z.div_mod_to_equations; lia).
  rewrite (land1_mod2 T) in FR by (Z.div_mod_to_equations; lia).
  reg_as (T + 2) (T + 4 * 0 + 2). reg_as 2 (4 * 0 + 2).
  lazymatch type of FR with rw_cells _ ?mm ?A _ => destruct (frame_split4 _ _ _ _ _ _ _ _ _ _ _ FR) as (j8 & j32 & F0 & F1 & F2 & F3); clear FR end.
  replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) in F1 by lia.
  replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) in F2 by lia.
  replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) in F3 by lia.

  (* [comment removed for export] *)
  name_term R1 ER1 (L1 t (Z_tr_bt19p.btX0 s t) 0 (-1)).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    callx (ubt_loop1 (Z.to_nat (sd_elems t) - 1) L s t T N (Z_tr_bt_mid.STP t) dsc (tree_fc s t) (ds_bl_count s) 573 (ds_opt_len s) (ds_static_len s) (max_code s t) R1 mm
                    (tree_dl s t) (ds_heap s) 0 (ds_depth s) 0 (-1)) drop ARR HPA DPA GC LCT L32 L8 end.
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. } 1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia. exact F1. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact RFC0. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ unfold Z_tr_bt19p.btX0 in ER1. exact ER1. }

  match goal with H : R1 = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) |- _ =>
    rename H into ER1';
    assert (E1 : build_tree_loop1 (Z.to_nat (sd_elems t)) (Z_tr_bt19p.btX0 s t) t (sd_elems t) 0 (-1) = (bt_upd s t (tree_fc s t) dl1 hp1 hl1 573 dp1 (ds_bl_count s) (ds_opt_len s) (ds_static_len s) (max_code s t), mc1))
      by (rewrite <- ER1', ER1; unfold L1; rewrite Z.sub_0_r; reflexivity);
    clear ER1 ER1';
    pose proof (avct_zlength (tree_fc s t) dl1 N ltac:(lia)) as LCT1; pose proof (av32_zlength hp1 573 ltac:(lia)) as L32_1; pose proof (av8_zlength dp1 573 ltac:(lia)) as L8_1 end.
  (* [comment removed for export] *)
  name_groups ARR1 HPA1 DPA1 GC1.
  lazymatch type of E1 with _ = (?X1, ?mc1) => name_term R2 ER2 (build_tree_loop2 2 X1 t mc1) end.
  lazymatch type of E1 with _ = (bt_upd _ _ _ ?dl1 ?hp1 ?hl1 _ ?dp1 _ _ _ _, ?mc1) =>
    callx (ubt_loop2 L s t T N hl1 mc1 (Z_tr_bt_mid.STP t) dsc 573 (ds_opt_len s) (ds_static_len s) (max_code s t) (tree_fc s t) dl1 hp1 dp1 (ds_bl_count s) g0 g1 g2 g3 g4 R2)
      drop ARR1 HPA1 DPA1 GC1 GD LCT1 L32_1 L8_1 end.
  1:{ exact ARR1. } 1:{ exact HPA1. } 1:{ exact DPA1. } 1:{ exact GC1. } 1:{ exact GD. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -192) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia; exact HF end. }
  1:{ eassumption. } 1:{ exact LAY. }
  1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. } 1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. }
  1:{ apply Z_tr_bt_mid.stree_view_of. } 1:{ apply STP_mod4. } 1:{ lia. } 1:{ lia. } 1:{ exact ROL0. } 1:{ exact RSL0. }
  1:{ exact ER2. }

  match goal with H : R2 = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) |- _ =>
    rename H into ER2'; pose proof ER2' as E2; rewrite ER2 in E2; clear ER2 ER2' R2;
    pose proof (avct_zlength fc2 dl1 N ltac:(lia)) as LCT2; pose proof (av32_zlength hp2 573 ltac:(lia)) as L32_2; pose proof (av8_zlength dp2 573 ltac:(lia)) as L8_2 end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG; rename HG into GD2 end.
  destruct (Z_tr_bt19p.safe_s3 s t SAFE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2) as (PQ2 & RDP2 & RFC2 & S7). rewrite <- EN in PQ2, RFC2.
  (* [comment removed for export] *)
  unfold BT_L2X. zs2. reg_as (dl_As L + 2047 + 929) (dl_As L + 2976). zs2. zs2. zs2.

  zs2. lazymatch type of E2 with _ = (bt_upd _ _ _ _ _ ?hl2 _ _ _ _ _ _, _) => rewrite (srliw1 hl2) by lia; change (hl2 / 2 ^ 1) with (hl2 / 2) end.
  zs2. zs2.

  (* [comment removed for export] *)
  name_groups ARR2 HPA2 DPA2 GC2.
  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    name_term R3 ER3 (build_tree_loop3 (Z.to_nat (hl2 / 2)) (bt_upd s t fc2 dl1 hp2 hl2 573 dp2 (ds_bl_count s) ol2 sl2 mc2) t (hl2 / 2));
    pose proof ER3 as ER3S; replace (Z.to_nat (hl2 / 2)) with (S (Z.to_nat (hl2 / 2) - 1)) in ER3S by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E2 with _ = (bt_upd _ _ ?fc2 ?dl1 ?hp2 ?hl2 _ ?dp2 _ ?ol2 ?sl2 _, ?mc2) =>
    callx (ubt_loop3 (Z.to_nat (hl2 / 2) - 1) L s t T N hl2 573 (hl2 / 2) lo fc2 dl1 hp2 dp2 (ds_bl_count s) ol2 sl2 mc2 R3 mm) drop HPA2 DPA2 GC2 L32_2 end end.
  1:{ exact HPA2. } 1:{ exact DPA2. } 1:{ exact GC2. }
  1:{ eapply ct_readable_rw; [exact ARR2| lia| lia| cbn [disjoint_from]; lia]. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. exact STK. } 1:{ rewrite ESP. unfold Z_PQ_STACK. lia. } 1:{ apply (dlay_below_lower L lo (bv_unsigned sp)); [exact BEL| rewrite ESP; lia]. }
  1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. }
  1:{ exact PQ2. } 1:{ exact RFC2. } 1:{ exact RDP2. } 1:{ lia. } 1:{ Z.div_mod_to_equations; lia. } 1:{ lia. } 1:{ reflexivity. } 1:{ exact ER3S. }
  rewrite ESP in *.

  match goal with H : R3 = bt_upd _ _ _ _ ?hp3 _ _ _ _ _ _ _ |- _ =>
    rename H into E3; clear ER3S; pose proof (av32_zlength hp3 573 ltac:(lia)) as L32_3 end.
  (* [comment removed for export] *)
  unfold ul3R. zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. zs2. zs2. zs2. shl_norm. zs2.
  zs2. rewrite (zb_lxor_ones (dl_As L + 3008)) by lia. zs2.
  zs2. zs2. zs2. zs2. rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
  zs2. try reg_as (T + sd_elems t * 4 + 0) (T + sd_elems t * 4). zs2. try reg_as (sd_elems t + 0) (sd_elems t).

  (* [comment removed for export] *)
  name_groups ARR3 HPA3 DPA3 GC3.
  lazymatch type of E3 with R3 = ?X3 => name_term R4 ER4 (build_tree_loop4 573 X3 t (sd_elems t)) end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of E3 with R3 = bt_upd _ _ ?fc2 ?dl1 ?hp3 ?hl2 _ ?dp2 _ ?ol2 ?sl2 ?mc2 =>
    callx (ubt_loop4 573 L s t T N hl2 573 (sd_elems t) dsc lo fc2 dl1 hp3 dp2 (ds_bl_count s) ol2 sl2 mc2 R4 mm) drop ARR3 HPA3 DPA3 GC3 LCT2 L8_2 L32_3 end end.
  1:{ exact ARR3. } 1:{ exact HPA3. } 1:{ exact DPA3. } 1:{ exact GC3. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -192) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia; exact HF end. }
  1:{ match goal with HF : rw_cells usegs ?mm (bv_unsigned sp + -144) _ |- rw_cells usegs ?mm _ _ => rewrite ESP; replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) by lia; exact HF end. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ rewrite ESP. assumption. } 1:{ rewrite ESP. unfold Z_PQ_STACK. lia. } 1:{ apply (dlay_below_lower L lo (bv_unsigned sp)); [exact BEL| rewrite ESP; lia]. } 1:{ rewrite ESP. lia. }
  1:{ exact ALT. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ exact RFC2. } 1:{ exact RDP2. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. } 1:{ exact ER4. }
  rewrite ESP in *.

  match goal with H : R4 = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ _ _ _ |- _ =>
    rename H into ER4'; pose proof ER4' as E4; rewrite ER4 in E4; clear ER4 ER4';
    pose proof (avct_zlength fc4 dl4 N ltac:(lia)) as LCT4; pose proof (av32_zlength hp4 573 ltac:(lia)) as L32_4; pose proof (av8_zlength dp4 573 ltac:(lia)) as L8_4 end.
  (* [comment removed for export] *)
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    destruct (S7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E3 E4 ltac:(assumption) ltac:(lia)) as (RHP7 & RDL7 & OK1 & OK23 & LEN15) end.
  rewrite <- EN in RHP7, RDL7. clear S7.
  pose proof E3 as E3x. rewrite ER3 in E3x.
  pose proof (Z_tr_bt19p.build_tree_flat s t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ E1 E2 E3x E4) as EBT.
  pose proof (relro_clean_munch _ _ _ RC MU ltac:(cbn [disjoint_from]; unfold RELRO_LO, RELRO_HI; lia)) as RC'.

  (* [comment removed for export] *)
  match goal with HF0 : rw_cells usegs ?mm (bv_unsigned sp + -208) _, HF1 : rw_cells usegs ?mm (bv_unsigned sp + -192) _,
                   HF2 : rw_cells usegs ?mm (bv_unsigned sp + -144) _, HF3 : rw_cells usegs ?mm (bv_unsigned sp + -136) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    replace (bv_unsigned sp + -192) with (bv_unsigned sp + -208 + 16) in HF1 by lia;
    replace (bv_unsigned sp + -144) with (bv_unsigned sp + -208 + 64) in HF2 by lia;
    replace (bv_unsigned sp + -136) with (bv_unsigned sp + -208 + 72) in HF3 by lia;
    pose proof (frame_join4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HF0 HF1 HF2 HF3) as FRJ; clear HF0 HF1 HF2 HF3 end.

  unfold ul4R.
  apply evt_done. unfold bt_mid_post.
  lazymatch type of FRJ with rw_cells _ ?mm _ (CB 8 ?j0 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: CB 32 ?nc :: _) =>
  lazymatch type of GD2 with rw_cells _ _ _ [CB 7 ?k0; _; _; _; _; CB 4 ?k1; _; _; _; _; _; CB 2 ?k2; _; CB 4 ?k3; _; _; CB 4 ?k4; _] =>
  lazymatch type of E4 with _ = bt_upd _ _ ?fc4 ?dl4 ?hp4 1 ?hm4 ?dp4 _ ?ol2 ?sl2 ?mc2 =>
    do 24 eexists; exists fc4, dl4, hp4, dp4, hm4, mc2, ol2, sl2, k0, k1, k2, k3, k4, j0, nc; exists mm end end end.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact RC'|].
  split; [assumption|]. split; [exact FRJ|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact BLC|]. split; [eassumption|]. split; [exact GD2|]. split; [eassumption|].
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [lia|]. split; [assumption|]. split; [lia|].
  split; [exact RHP7|]. split; [exact RDL7|]. split; [assumption|]. split; [lia|]. split; [lia|].
  split; [exact OK1|]. split; [exact OK23|]. split; [exact LEN15| exact EBT].


Qed.
