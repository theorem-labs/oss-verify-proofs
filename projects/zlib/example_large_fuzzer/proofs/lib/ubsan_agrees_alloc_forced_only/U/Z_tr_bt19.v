From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit InitMem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel RefBuildTree1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt1
     Z_tr_bt11 Z_tr_bt13 Z_tr_bt17 Z_tr_bt18 Z_tr_bt18b Z_tr_bt_mid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.
Definition body_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh : list byte) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (FC' DL' HP' DP' BC' : arr) (OL' SL' hm mc : Z) (g0 g1 g2 g3 g4 : list byte) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (WBT L T N dsc lo sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells usegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))]
    /\ R = bt_upd s t FC' DL' HP' 1 hm DP' BC' OL' SL' mc
    /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ arr_len BC' = 16.
Lemma build_tree_body : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc lo : Z) (hh g0 g1 g2 g3 g4 : list byte) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct (tree_fc s t) (tree_dl s t) N)) -> u32arr usegs m (dl_As L + 3008) (av32 (ds_heap s) 573) ->
  u8arr usegs m (dl_As L + 5308) (av8 (ds_depth s) 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 (ds_bl_count s) 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz (ds_heap_len s)); C4 (wz (ds_heap_max s))] ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s (ds_opt_len s) (ds_static_len s) g0 g1 g2 g3 g4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz (max_code s t)); CB 4 hh; C8 (wz (SDA t))] ->
  mem_inv usegs m -> relro_clean m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_BT_STACK -> bv_unsigned sp mod 16 = 0 -> dlay_below L lo (bv_unsigned sp) ->
  bt_safe s t -> T = dl_As L + toff t -> N = tsize t -> dsc = dl_As L + bt_desc t ->
  arr_len (tree_fc s t) = N -> arr_len (tree_dl s t) = N -> arr_len (ds_heap s) = 573 -> arr_len (ds_depth s) = 573 -> arr_len (ds_bl_count s) = 16 ->
  a0 = wz (dl_As L) -> a1 = wz dsc ->
  R = build_tree s t ->
  evt usegs (body_post L s t T N dsc lo hh R ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_BUILD_TREE) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA DPA BLC GC GD Gdsc MI RC LAY STK LO AL BEL SAFE ET EN Edsc LFC LDL LHP LDP LBC Ea0 Ea1 ER0.
  pose proof (munch_refl (WBT L T N dsc lo sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof LO as LO0. unfold Z_BT_STACK in LO0.
  assert (BsK : dl_As L + 5968 <= 0x10000 \/ 0x5f000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & X); exact X).
  assert (ALs : dl_As L mod 16 = 0) by (destruct (lo_s _ LAY) as (_ & X & _); exact X).
  pose proof (RefBuildTree1.elems_range t) as RE. pose proof (RefBuildTree1.tsize_elems t) as EN2.
  assert (Rdsc : 2904 <= bt_desc t <= 2952) by (destruct t; cbn; lia).
  assert (Rtf : 212 <= toff t /\ toff t + 4 * tsize t <= 2904 /\ toff t mod 4 = 0) by (destruct t; cbn; lia).
  pose proof (SDA_range t) as RSDA.
  assert (AT4 : T mod 4 = 0) by (rewrite ET; clear - ALs Rtf; Z.div_mod_to_equations; lia).
  pose proof (avct_zlength (tree_fc s t) (tree_dl s t) N ltac:(lia)) as LCT. pose proof (av32_zlength (ds_heap s) 573 ltac:(lia)) as L32.
  pose proof (av8_zlength (ds_depth s) 573 ltac:(lia)) as L8. pose proof (av16_zlength (ds_bl_count s) 16 ltac:(lia)) as L16.
  call (bt_front L s t T N dsc lo hh g0 g1 g2 g3 g4).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact BLC. } 1:{ exact GC. } 1:{ exact GD. } 1:{ exact Gdsc. } 1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. }
  1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. } 1:{ exact SAFE. } 1:{ exact ET. } 1:{ exact EN. } 1:{ exact Edsc. }
  1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LDP. } 1:{ exact LBC. } 1:{ exact Ea0. } 1:{ exact Ea1. }
  lazymatch goal with H : build_tree s t = _ |- _ => rewrite <- ER0 in H; rename H into ER end.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -208)) = bv_unsigned sp + -208) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  reg_as (bv_unsigned sp - 208) (bv_unsigned sp + -208).
  match goal with HS : stk usegs ?mm lo (bv_unsigned sp - 208), HF : rw_cells usegs ?mm (bv_unsigned sp - 208) _ |- _ =>
    replace (bv_unsigned sp - 208) with (bv_unsigned sp + -208) in HS by lia; replace (bv_unsigned sp - 208) with (bv_unsigned sp + -208) in HF by lia;
    rename HS into STK; rename HF into FR end.
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
    destruct (proj1 (rw_cells_app_iff mm A [c0] (c1 :: c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest)) FR) as [F0 FR1]; clear FR;
    destruct (proj1 (rw_cells_app_iff mm _ [c1] (c2 :: c3 :: c4 :: c5 :: c6 :: c7 :: c8 :: c9 :: rest)) FR1) as [F8 FR2]; clear FR1;
    destruct (proj1 (rw_cells_app_iff mm _ [c2; c3; c4; c5; c6; c7] (c8 :: c9 :: rest)) FR2) as [F16 FR3]; clear FR2;
    destruct (proj1 (rw_cells_app_iff mm _ [c8] (c9 :: rest)) FR3) as [F64 FR4]; clear FR3;
    destruct (proj1 (rw_cells_app_iff mm _ [c9] rest) FR4) as [F72 FS]; clear FR4;
    cbn [cells_size csize Nat.add] in F8, F16, F64, F72, FS end.
  lazymatch type of F8 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -200) in F8 by lia end.
  lazymatch type of F16 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -192) in F16 by lia end.
  lazymatch type of F64 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -144) in F64 by lia end.
  lazymatch type of F72 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -136) in F72 by lia end.
  lazymatch type of FS with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -104) in FS by lia end.
  match goal with HR : relro_clean ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (sdesc_relro t _ HR) as Gsd end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5300) [C4 (wz 1); C4 (wz ?hm4)] |- _ =>
    replace (wz hm4) with (wz (hm4 - 1 + 1)) in HG by (f_equal; lia) end.
  lazymatch goal with HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp 573), HL : arr_len ?dp = 573 |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (av8_zlength dp 573 ltac:(lia)) as L8' end.
  lazymatch goal with HT : u8arr usegs ?mm T (u16s (avct ?fc ?dl N)), HH : u32arr usegs ?mm (dl_As L + 3008) (av32 ?hp 573), HD : u8arr usegs ?mm (dl_As L + 5308) (av8 ?dp 573),
                      HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HC : rw_cells usegs ?mm (dl_As L + 5300) [C4 (wz 1); C4 (wz (?hm - 1 + 1))],
                      Hd : rw_cells usegs ?mm dsc [C8 (wz T); C4 (wz ?mc); CB 4 hh; C8 (wz (SDA t))], HN : rw_cells usegs ?mm (bv_unsigned sp + -136) [CB 32 ?nc]
    |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (upartB L s t T N (hm - 1) dsc mc ol sl fc dl hp dp (ds_bl_count s) hh k0 k1 k2 k3 k4 nc R) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact Gsd. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 8) with (bv_unsigned sp + -200) by lia. exact F8. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 16) with (bv_unsigned sp + -192) by lia. exact F16. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 64) with (bv_unsigned sp + -144) by lia. exact F64. }
  1:{ rewrite ESP. replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) by lia. exact F72. }
  1:{ eassumption. } 1:{ exact LAY. } 1:{ lia. } 1:{ lia. } 1:{ exact EN. } 1:{ exact AT4. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact LBC. } 1:{ exact Edsc. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ rewrite ESP. lia. } 1:{ rewrite ESP. lia. }
  1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact ER. }
  rewrite ESP in *. unfold BT_EPI.
  match goal with HN : rw_cells usegs _ (bv_unsigned sp + -208 + 72) [CB 32 _] |- _ => replace (bv_unsigned sp + -208 + 72) with (bv_unsigned sp + -136) in HN by lia; rename HN into F72' end.
  do 13 zs2. zstep. zstep.
  release_frame F0 STK (bv_unsigned sp + -200). release_frame F8 STK (bv_unsigned sp + -192). release_frame F16 STK (bv_unsigned sp + -144).
  release_frame F64 STK (bv_unsigned sp + -136). release_frame F72' STK (bv_unsigned sp + -104). release_frame FS STK (bv_unsigned sp).
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ ?ol ?sl ?k0 ?k1 ?k2 ?k3 ?k4), HR : R = bt_upd s t ?fc ?dl ?hp 1 ?hm ?dp ?bc _ _ ?mc |- _ =>
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
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_ltf _ LENS). } 1:{ exact (ln_ltd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBl' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
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
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_dtf _ LENS). } 1:{ exact (ln_dtd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBd' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBb; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
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
      1:{ exact MI. } 1:{ exact RC. } 1:{ exact LAY. } 1:{ exact STK. } 1:{ exact LO. } 1:{ exact AL. } 1:{ exact BEL. }
      1:{ exact SAFE. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ reflexivity. }
      1:{ exact (ln_btf _ LENS). } 1:{ exact (ln_btd _ LENS). } 1:{ exact (ln_heap _ LENS). } 1:{ exact (ln_dep _ LENS). } 1:{ exact (ln_blc _ LENS). }
      1:{ exact Ea0. } 1:{ exact Ea1. } reflexivity. }
    intros ms' P. unfold body_post in P.
    destruct P as (x0 & x1 & x2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & FC' & DL' & HP' & DP' & BC' & OL' & SL' & hm & mc & k0 & k1 & k2 & k3 & k4 & m' &
                   -> & MU & WM & MI' & STK' & ARR' & HPA' & DPA' & BLC' & GC' & GD' & GBb' & ER & LFC' & LDL' & LHP' & LDP' & LBC').
    tr_groups MU WM.
    lazymatch type of MU with munch ?W _ _ =>
      apply (rw_cells_transport usegs W m m') in GBl; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport usegs W m m') in GBd; [| exact MU| exact WM| cbn [disjoint_from cells_size csize Nat.add]; lia] end.
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
