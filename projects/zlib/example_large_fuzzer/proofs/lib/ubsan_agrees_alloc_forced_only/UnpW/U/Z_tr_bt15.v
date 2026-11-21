(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13 Z_tr_bt14 Z_tr_bt15.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_scan1 Z_tr_bt_mid Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.
Definition G3_OHEAD : Z := 0x1d544.
Definition G3_OLATCH : Z := 0x1d53c.
Definition G3_IHEAD : Z := 0x1d560.
Definition G3_ILATCH : Z := 0x1d558.
Definition G3_EXIT : Z := 0x1d5c8.
Definition ug3R (L : dlay) (T bits n h mc : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz 572) (wz bits) (wz h) (wz n) a6 a7
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6.
Notation uWg3 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 5881, dl_As L + 5968)] (only parsing).
Definition ug3_trip_post (L : dlay) (s : deflate_state) (T N bits n' h mc : Z) (FC DL' : arr) (OL' SL : Z)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a6 a7 h0 h1 h2 h3 h4 pcx m',
    ms' = MS (ug3R L T bits n' (h - 1) mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ ((pcx = 0x1d560 /\ n' <> 0) \/ (pcx = 0x1d53c /\ n' = 0)).
Ltac ug3_latch n MU WM ARR GD :=
  let K3 := fresh "K3" in
  zs2; try (rewrite (bv_swrap32_id (n + -1)) by lia); reg_as (n + -1) (n - 1); zstep; br_cases K3;
  apply evt_done; unfold ug3_trip_post, ug3R, bD_cells; do 11 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [eassumption|]);
  (split; [exact ARR|]); (split; [close_cells GD|]); first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].
Lemma ug3_trip : forall (L : dlay) (s : deflate_state) (T N bits n h mc m_ OL SL : Z) (FC DL HP : arr) (h0 h1 h2 h3 h4 : list byte)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  1 <= n < 65536 -> 1 <= h <= 573 -> m_ = arr_get HP (h - 1) -> 0 <= m_ < 573 -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  evt usegs (ug3_trip_post L s T N bits (g3_n mc m_ n) h mc FC (g3_DL DL mc m_ bits) (g3_OL FC DL OL mc m_ bits) SL
               sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m)
      (MS (ug3R L T bits n h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d560) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA GD MI LAY RT1 RT2 RN LFC LDL LHP Rn Rh Em Rm Rmc Rb RDL RFC ROL.
  pose proof (munch_refl (uWg3 L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) (h - 1) _ (wa (dl_As L + 3008 + (h - 1) * 4)) HPA (av32_nth HP 573 (h - 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDm. rewrite <- Em in RDm.
  unfold ug3R. zs2. zs2. try rewrite (bv_swrap32_id (h + -1)) by lia. reg_as (h + -1) (h - 1). ustep BT_TRAP. ustep BT_TRAP. zs2. shl_norm. zs2. zs2.
  zstep. br_cases K.
  -
    assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    assert (En' : g3_n mc m_ n = n) by (unfold g3_n; rewrite (proj2 (Z.ltb_lt mc m_)) by lia; reflexivity).
    rewrite EDL, EOL, En'.
    apply evt_done. unfold ug3_trip_post, ug3R, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split; [exact ARR|]. split; [exact GD|]. left. split; [reflexivity| lia].
  - assert (En' : g3_n mc m_ n = n - 1) by (unfold g3_n; rewrite (proj2 (Z.ltb_ge mc m_)) by lia; reflexivity). rewrite En'.
    pose proof (u16arr_read usegs m T (avct FC DL N) (2 * m_ + 1) _ (wa (T + m_ * 4 + 2)) ARR (avct_nth_dl FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
    pose proof (u16arr_read usegs m T (avct FC DL N) (2 * m_) _ (wa (T + m_ * 4)) ARR (avct_nth_fc FC DL N m_ ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
    pose proof (RDL m_ ltac:(lia)) as Rl. pose proof (RFC m_ ltac:(lia)) as Rf.
    zs2. shl_norm. zs2. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2. rewrite zx16_small by lia. zstep. br_cases K2.
    +
      assert (EDL : g3_DL DL mc m_ bits = DL) by (unfold g3_DL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = OL) by (unfold g3_OL; rewrite (proj2 (Z.eqb_eq (arr_get DL m_) bits)) by lia; rewrite orb_true_r; reflexivity).
      rewrite EDL, EOL.
      ug3_latch n MU WM ARR GD.
    + zs2. rewrite zx16_small by lia. zs2. zs2. zs2. zs2.
      rewrite wz_mulmod. zstep.
      ct_store_dl ARR FC DL N T m_ (wrap16 bits) ltac:(apply le2_wrap16; reflexivity).
      zs2.
      assert (NEb : (arr_get DL m_ =? bits) = false) by (apply Z.eqb_neq; lia).
      assert (EDL : g3_DL DL mc m_ bits = arr_set DL m_ (wrap16 bits)) by (unfold g3_DL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      assert (EOL : g3_OL FC DL OL mc m_ bits = wrap64 (OL + (bits - arr_get DL m_) * arr_get FC m_)) by (unfold g3_OL; rewrite (proj2 (Z.ltb_ge mc m_)), NEb by lia; reflexivity).
      rewrite EDL, EOL.
      ug3_latch n MU WM ARR GD.
Qed.
Definition ug3i_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N bits mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state * Z)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a6 a7 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (ug3R L T bits 0 h' mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d53c) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc, h')
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= h' <= 573.
Lemma ug3i_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits n h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> munch (uWg3 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  1 <= n < 65536 -> 0 <= h -> h < Z.of_nat f -> -1 <= mc < N -> 1 <= bits <= 15 ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3i f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits n h ->
  gb3i_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits n h ->
  evt usegs (ug3i_loop_post L s t T N bits mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3R L T bits n h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d560) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP Rn Rh0 Hf Rmc Rb RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  destruct (g3i_ok_step' s t FC DL HP HL HM DP BC OL SL mc f bits n h (arr_get HP (h - 1)) OK ltac:(lia) eq_refl) as (Rh & Rm & OK').
  pose proof (g3i_model' s t FC DL HP HL HM DP BC OL SL mc f bits n h R (arr_get HP (h - 1)) ER ltac:(lia) eq_refl) as ER'. clear ER OK.
  set (m_ := arr_get HP (h - 1)) in *.
  pose proof (avct_zlength FC (g3_DL DL mc m_ bits) N ltac:(lia)) as LCT'.
  call (ug3_trip L s T N bits n h mc m_ OL SL FC DL HP h0 h1 h2 h3 h4 sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact Rn. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rm. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. }
  match goal with H : _ \/ _ |- _ => destruct H as [(-> & K)|(-> & K)] end.
  - assert (Rn' : 1 <= g3_n mc m_ n < 65536) by (revert K; unfold g3_n; destruct (mc <? m_); lia).
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N bits (g3_n mc m_ n) (h - 1) mc ol' SL FC (g3_DL DL mc m_ bits) HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HG| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact RN| exact LFC| rewrite g3_DL_len; exact LDL| exact LHP
        | exact Rn'| lia| lia| exact Rmc| exact Rb| apply g3_DL_range; exact RDL| exact RFC| apply g3_OL_range; exact ROL| exact ER'| exact OK'] end.
  - rewrite K in ER'. rewrite GL3i_done in ER'.
    rewrite K.
    apply evt_done. unfold ug3i_loop_post. do 9 eexists. exists (g3_DL DL mc m_ bits), (g3_OL FC DL OL mc m_ bits), (h - 1). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'|].
    split; [rewrite g3_DL_len; exact LDL|]. split; [apply g3_DL_range; exact RDL|]. split; [apply g3_OL_range; exact ROL|]. lia.
Qed.
Definition ug3oR (L : dlay) (T bits h mc : Z) (sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) (wz 572) (wz bits) (wz h) a5 a6 a7
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6.
Definition ug3_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc : Z) (FC HP : arr) (HL HM : Z) (DP BC : arr) (SL : Z) (R : deflate_state)
    (sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a5 a6 a7 h0 h1 h2 h3 h4 DL' OL' h' m',
    ms' = MS (ug3oR L T 0 h' mc sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d5c8) fc None m' (seg_rom usegs)
    /\ munch (uWg3 L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL h0 h1 h2 h3 h4)
    /\ R = bt_upd s t FC DL' HP HL HM DP BC OL' SL mc
    /\ arr_len DL' = N /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64.
Lemma ug3_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N bits h mc OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  mem_inv usegs m -> dlay_ok L -> munch (uWg3 L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> 0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  Z.of_nat f = bits -> 1 <= bits <= 15 -> 0 <= h <= 573 -> -1 <= mc < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 ->
  R = gen_bitlen_loop3 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits h ->
  gb3_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) bits h ->
  evt usegs (ug3_loop_post L s t T N mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3oR L T bits h mc sp ra gp tp t0 t1 t2 s0 s1 s2 a5 a6 a7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d544) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD MI LAY MU WM RT1 RT2 RN LFC LDL LHP LBC Ef Rb Rh Rmc RBC RDL RFC ROL ER OK.
  { exfalso. lia. }
  pose proof (g3_model s t FC DL HP HL HM DP BC OL SL mc f bits h R ER ltac:(lia)) as ER'.
  destruct (g3_ok_step s t FC DL HP HL HM DP BC OL SL mc f bits h OK ltac:(lia)) as [OKi OKo]. clear ER OK.
  assert (TAIL : forall (DL' : arr) (OL' h' : Z) (g0 g1 g2 g3 g4 : list byte) (b0 b1 b5 b6 b7 : word) (m' : mem),
    u8arr usegs m' T (u16s (avct FC DL' N)) -> u32arr usegs m' (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC 16)) ->
    rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL g0 g1 g2 g3 g4) -> mem_inv usegs m' -> munch (uWg3 L T N) m0 m' -> wmono usegs m0 m' ->
    arr_len DL' = N -> (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) -> 0 <= OL' < 2^64 -> 0 <= h' <= 573 ->
    R = gen_bitlen_loop3 f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) t mc (bits - 1) h' ->
    gb3_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC OL' SL mc) (bits - 1) h' ->
    evt usegs (ug3_loop_post L s t T N mc FC HP HL HM DP BC SL R sp ra gp tp t2 s0 s1 s2 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6 F fc m0)
      (MS (ug3oR L T bits h' mc sp ra gp tp b0 b1 t2 s0 s1 s2 b5 b6 b7 s4 s5 s6 s7 s9 s11 t3 t4 t5 t6) F (wz 0x1d53c) fc None m' (seg_rom usegs))).
  { intros DL' OL' h' g0 g1 g2 g3 g4 b0 b1 b5 b6 b7 m' ARR' HPA' BLC' GD' MI' MU' WM' LDL' RDL' ROL' Rh' ER2 OK2.
    unfold ug3oR. zs2. zstep. br_cases K; reg_as (bits + -1) (bits - 1).
    - replace (bits - 1) with 0 in * by lia. rewrite GL3_done in ER2.
      apply evt_done. unfold ug3_loop_post, ug3oR. do 10 eexists. exists DL', OL', h'. eexists.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ARR'|]. split; [exact GD'|]. split; [exact ER2|].
      split; [exact LDL'|]. split; [exact RDL'| exact ROL'].
    - eapply (IH L s t T N (bits - 1) h' mc OL' SL FC DL' HP HL HM DP BC g0 g1 g2 g3 g4 R m0);
        [exact ARR'| exact HPA'| exact BLC'| exact GD'| exact MI'| exact LAY| exact MU'| exact WM'| exact RT1| exact RT2| exact RN| exact LFC| exact LDL'| exact LHP| exact LBC
        | lia| lia| exact Rh'| exact Rmc| exact RBC| exact RDL'| exact RFC| exact ROL'| exact ER2| exact OK2]. }
  pose proof LAY as LAY0. lay_open LAY0.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (u16arr_read usegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn.
  pose proof (RBC bits ltac:(lia)) as Rn.
  unfold ug3oR. zs2. shl_norm. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  - call (ug3i_loop 574 L s t T N bits (arr_get BC bits) h mc OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4
            (gen_bitlen_loop3i 574 (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc bits (arr_get BC bits) h) m sp).
    1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact GD. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. }
    1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ lia. } 1:{ lia. } 1:{ change (Z.of_nat 574) with 574. lia. } 1:{ exact Rmc. } 1:{ exact Rb. } 1:{ exact RDL. } 1:{ exact RFC. }
    1:{ exact ROL. } 1:{ reflexivity. } 1:{ exact OKi. }
    match goal with E : gen_bitlen_loop3i 574 _ _ _ _ _ _ = (_, _) |- _ => rewrite E in ER', OKo end.
    unfold ug3R.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' SL ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ (wz ?hh) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ ?mm _) =>
      eapply (TAIL dl' ol' hh g0 g1 g2 g3 g4); [exact HT| eassumption| eassumption| exact HG| eassumption| exact MU| exact WM| assumption| assumption| assumption| lia| exact ER'| exact OKo] end.
  -
    rewrite K in ER', OKo. rewrite GL3i_done in ER', OKo.
    zs2.
    eapply (TAIL DL OL h h0 h1 h2 h3 h4); [exact ARR| exact HPA| exact BLC| exact GD| exact MI| exact MU| exact WM| exact LDL| exact RDL| exact ROL| exact Rh| exact ER'| exact OKo].
Qed.
