(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_tr_bt12 Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_scan1 Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.
Definition GB1_HEAD : Z := 0x1d33c.
Definition GB1_LATCH : Z := 0x1d330.
Definition GB1_LEAF : Z := 0x1d3b4.
Definition GB1_EXIT : Z := 0x1d484.
Definition ugbR (L : dlay) (T h ovf mc ML stp xp base : Z) (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) :=
  mkR ra sp gp tp (wz 573) (wz 573) (wz (ONES - T)) s0 s1 (wz T) (wz mc) (wz ML) (wz stp) (wz xp) (wz base) (wz (ONES - (dl_As L + 2976))) (wz ovf)
      s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 (wz (573 - h)) (wz (4 * h)) (wz 16) t6.
Definition ugb1_head_post (L : dlay) (T N h ovf base mc ML stp xp n bits ovf' : Z) (FC DL' : arr)
    (sp ra gp tp s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s5 m',
    ms' = MS (ugbR L T h ovf' mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz n) s5 s6 s7 s9 s11 (wz (n * 4))) F
             (wz (if mc <? n then GB1_LATCH else GB1_LEAF)) fc None m' (seg_rom usegs)
    /\ munch [(T, T + 4 * N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)).
Lemma ugb1_head : forall (L : dlay) (T N h ovf base mc ML stp xp n dlen bits : Z) (FC DL HP : arr)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] -> mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> n = arr_get HP h -> 0 <= n < N -> 0 <= arr_get DL n < N -> dlen = arr_get DL (arr_get DL n) -> 0 <= dlen < 65536 -> 1 <= ML <= 15 ->
  0 <= ovf < 2^30 -> -1 <= mc < 2^31 ->
  bits = (if ML <=? dlen then ML else dlen + 1) ->
  evt usegs (ugb1_head_post L T N h ovf base mc ML stp xp n bits (if ML <=? dlen then ovf + 1 else ovf) FC (arr_set DL n (wrap16 bits)) sp ra gp tp s6 s7 s9 s11 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d33c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA F64 MI LAY RT1 RT2 RN LFC LDL LHP SEP RSP Rh En Rn Rd Ed Rdl RML Ro Rmc Eb.
  pose proof (munch_refl [(T, T + 4 * N)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32.
  pose proof (u32arr_read usegs m _ (av32 HP 573) h _ (wa (dl_As L + 3008 + 4 * h)) HPA (av32_nth HP 573 h ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDn. rewrite <- En in RDn.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDd.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * arr_get DL n + 1) _ (wa (T + arr_get DL n * 4 + 2)) ARR (avct_nth_dl FC DL N (arr_get DL n) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  rewrite <- Ed in RDl.
  unfold ugbR. zs2. ustep BT_TRAP. zs2. ustep BT_TRAP. zs2. zs2. zs2. shl_norm. zs2.
  ustep BT_TRAP. zs2. zs2. zs2. zs2. ustep BT_TRAP.
  zs2. rewrite zx16_small by lia. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia.
  zstep. br_cases K.
  -
    rewrite (proj2 (Z.leb_le ML dlen)) in Eb |- * by lia. subst bits.
    zs2. ustep BT_TRAP. zs2. zs2.
    ct_store_dl ARR FC DL N T n (wrap16 ML) ltac:(rewrite (wrap16_id ML) by lia; reflexivity).
    zstep. br_cases K2.
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_lt mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_ge mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
  - rewrite (proj2 (Z.leb_gt ML dlen)) in Eb |- * by lia. subst bits.
    zs2.
    ct_store_dl ARR FC DL N T n (wrap16 (dlen + 1)) ltac:(rewrite (wrap16_id (dlen + 1)) by lia; reflexivity).
    zstep. br_cases K2.
    + apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_lt mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
    + zs2. apply evt_done. unfold ugb1_head_post, ugbR, GB1_LATCH, GB1_LEAF. rewrite (proj2 (Z.ltb_ge mc n)) by lia.
      do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ARR].
Qed.
Ltac ua16_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (av16 a n) idx (wa (A + 2 * idx)) ARR ltac:(rewrite av16_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av16_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      unfold u16arr in ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "L16" in pose proof (av16_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.
Definition ugb1_cnt_post (L : dlay) (T h ovf base mc ML stp xp n bits xb : Z) (BC' : arr)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s5 s7 s9 m',
    ms' = MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz xb) s5 s6 s7 s9 s11 (wz (n * 4))) F (wz 0x1d424) fc None m' (seg_rom usegs)
    /\ munch [(dl_As L + 2976, dl_As L + 3008)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16)).
Lemma ugb1_cnt : forall (L : dlay) (t : tree_id) (T h ovf mc stp xp n bits : Z) (BC : arr)
    (sp ra gp tp s5 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv usegs m -> dlay_ok L -> arr_len BC = 16 ->
  xbits_view t xp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> 0 <= n -> n <= mc -> mc < sd_elems t -> 1 <= bits <= 15 -> 0 <= sd_extra_base t < 2^31 -> sd_elems t < 2^31 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  evt usegs (ugb1_cnt_post L T h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n bits (xbits t n) (arr_set BC bits (wrap16 (arr_get BC bits + 1)))
               sp ra gp tp s6 s11 F fc m)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz n) s5 s6 s7 s9 s11 (wz (n * 4)))
          F (wz 0x1d3b4) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros BLC MI LAY LBC XV Rxp Axp Rn0 Rn Rmc Rb Rbase RE RBC.
  pose proof (munch_refl [(dl_As L + 2976, dl_As L + 3008)] m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY.
  pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16. pose proof (RBC bits ltac:(lia)) as Rcb.
  pose proof (u16arr_read usegs m _ (av16 BC 16) bits _ (wa (dl_As L + 2976 + bits * 2)) BLC (av16_nth BC 16 bits ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
  unfold ugbR. ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2.
  ua16_store BLC BC 16 (dl_As L + 2976) bits (wrap16 (arr_get BC bits + 1)) ltac:(apply le2_add_sx16).
  zstep. br_cases K.
  - assert (EX : xbits t n = arr_get (sd_extra_bits t) (n - sd_extra_base t)) by (unfold xbits; rewrite (proj2 (Z.leb_le _ _) K); reflexivity).
    match goal with MI' : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (XV mm n MI' ltac:(lia)) as [RDx Rx] end.
    rewrite <- EX in RDx, Rx.
    zs2. zs2. try rewrite (bv_swrap32_id (n - sd_extra_base t)) by lia. try rewrite (bv_swrap32_id (n + - sd_extra_base t)) by lia.
    ustep BT_TRAP. zs2. zs2. try rewrite (bv_swrap32_id (n - sd_extra_base t)) by lia. try rewrite (bv_swrap32_id (n + - sd_extra_base t)) by lia.
    zs2. shl_norm. zs2. zs2.
    ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2.
    apply evt_done. unfold ugb1_cnt_post, ugbR. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
  - assert (EX : xbits t n = 0) by (unfold xbits; rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity). rewrite EX.
    zs2. zs2.
    apply evt_done. unfold ugb1_cnt_post, ugbR. do 4 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact BLC].
Qed.
Notation uWgl L := [(dl_As L + 5881, dl_As L + 5968)] (only parsing).
Definition ugb1_len_post (L : dlay) (s : deflate_state) (T h ovf base mc ML stp xp xb : Z) (OL' SL' : Z)
    (sp ra gp tp s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s5 t6 h0 h1 h2 h3 h4 m',
    ms' = MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 (wz xb) s5 s6 s7 s9 s11 t6) F (wz 0x1d330) fc None m' (seg_rom usegs)
    /\ munch (uWgl L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4).
Lemma ugb1_len : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf base mc ML stp xp n bits xb OL SL : Z) (FC DL : arr) (h0 h1 h2 h3 h4 : list byte)
    (sp ra gp tp s5 s6 s7 s9 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  stree_view_n t stp -> stp mod 4 = 0 -> 0 <= n < N -> n < sd_elems t -> 0 <= arr_get FC n < 65536 -> 1 <= bits <= 15 -> 0 <= xb < 16 -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  evt usegs (ugb1_len_post L s T h ovf base mc ML stp xp xb (wrap64 (OL + arr_get FC n * (bits + xb)))
               (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xb)) else SL) sp ra gp tp s6 s7 s9 s11 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp (wz 0) (wz (T + n * 4)) (wz bits) (wz xb) s5 s6 s7 s9 s11 (wz (n * 4)))
          F (wz 0x1d424) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR GD MI LAY RT1 RT2 RN SV Astp Rn RnE Rf Rb Rx ROL RSL.
  pose proof (munch_refl (uWgl L) m) as MU. pose proof (wmono_refl usegs m) as WM. lay_open LAY. unfold bD_cells in GD.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT.
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n) _ (wa (T + n * 4)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  unfold ugbR. zs2. zs2. try rewrite (bv_swrap32_id (bits + xb)) by lia. ustep BT_TRAP.
  zs2. rewrite zx16_small by lia. zs2. zs2. zs2.
  try rewrite (Z.mod_small (bits + xb) 4294967296) by lia. try rewrite (Z.mod_small ((bits + xb) * 4294967296) 18446744073709551616) by lia.
  zs2. zs2. zstep.
  zstep. destruct SV as [[Es Eh]|(Rs0 & Eh & RDS)]; rewrite Eh.
  - subst stp. br_true.
    apply evt_done. unfold ugb1_len_post, ugbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite wz_wrap64. replace (OL + arr_get FC n * (bits + xb)) with (OL + (bits + xb) * arr_get FC n) by lia. eassumption.
  - br_false. match goal with MI' : mem_inv usegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => destruct (RDS mm n MI' ltac:(lia)) as [RDl Rsl] end.
    zs2. replace (wz (n * 4 + stp)) with (wz (stp + n * 4)) by (f_equal; lia).
    ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP. ustep BT_TRAP.
    zs2. rewrite zx16_small by lia. zs2. zs2. try rewrite (bv_swrap32_id (stree_Len t n + xb)) by lia. ustep BT_TRAP.
    zs2. zs2. zs2. try rewrite (Z.mod_small (stree_Len t n + xb) 4294967296) by lia. try rewrite (Z.mod_small ((stree_Len t n + xb) * 4294967296) 18446744073709551616) by lia.
    zs2. zs2. zstep.
    apply evt_done. unfold ugb1_len_post, ugbR, bD_cells. do 11 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    rewrite !wz_wrap64.
    replace (OL + arr_get FC n * (bits + xb)) with (OL + (bits + xb) * arr_get FC n) by lia.
    replace (SL + arr_get FC n * (stree_Len t n + xb)) with (SL + (stree_Len t n + xb) * arr_get FC n) by lia. eassumption.
Qed.
Definition ugb1_latch_post (L : dlay) (T h ovf base mc ML stp xp : Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists pcx m',
    ms' = MS (ugbR L T (h + 1) ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ ((pcx = 0x1d33c /\ h + 1 < 573) \/ (pcx = 0x1d484 /\ h + 1 = 573)).
Lemma ugb1_latch : forall (L : dlay) (T h ovf base mc ML stp xp : Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> 0 <= h < 573 ->
  evt usegs (ugb1_latch_post L T h ovf base mc ML stp xp sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 F fc m)
      (MS (ugbR L T h ovf mc ML stp xp base sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d330) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI Rh.
  unfold ugbR. zs2. zs2. zstep. br_cases K; reg_as (573 - h - 1) (573 - (h + 1)); reg_as (573 - h + -1) (573 - (h + 1)); reg_as (4 * h + 4) (4 * (h + 1)).
  - apply evt_done. unfold ugb1_latch_post, ugbR. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].
  - apply evt_done. unfold ugb1_latch_post, ugbR. do 2 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|].
    first [right; split; [reflexivity| lia] | left; split; [reflexivity| lia]].
Qed.
Notation uWgb L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 3008); (dl_As L + 5881, dl_As L + 5968)] (only parsing).
Definition ugb1_iter_post (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (f : nat) (R : deflate_state * Z)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s4 s5 s7 s9 t6 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' pcx m',
    ms' = MS (ugbR L T (h + 1) ovf' mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = gen_bitlen_loop1 f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) t mc (sd_extra_base t) (sd_max_length t) (h + 1) ovf'
    /\ gb1_ok t mc f (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc) (h + 1) ovf'
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ ovf <= ovf' <= ovf + 1
    /\ ((pcx = 0x1d33c /\ h + 1 < 573) \/ (pcx = 0x1d484 /\ h + 1 = 573)).
Lemma ugb1_iter : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (f : nat) (R : deflate_state * Z)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> 0 <= arr_get HP h < N ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc (S f) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt usegs (ugb1_iter_post L s t T N h ovf mc stp xp FC HP HL HM DP f R sp ra gp tp s6 s11 F fc m)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d33c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F64 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rh Ro Rmc Rn RBC RDL RFC ROL RSL ER OK.
  pose proof (munch_refl (uWgb L T N) m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (RML : 7 <= sd_max_length t <= 15) by (destruct t; cbv; split; discriminate).
  assert (RBASE : 0 <= sd_extra_base t < 300) by (destruct t; cbv; split; congruence).
  assert (RE : 19 <= sd_elems t <= 286 /\ tsize t = 2 * sd_elems t + 1) by (destruct t; cbv; repeat split; congruence).
  set (n := arr_get HP h) in *. set (dlen := arr_get DL (arr_get DL n)).
  set (bits := if sd_max_length t <=? dlen then sd_max_length t else dlen + 1). set (ovf' := if sd_max_length t <=? dlen then ovf + 1 else ovf).
  destruct (gb1_ok_step s t FC DL HP HL HM DP BC OL SL mc f h ovf n dlen bits ovf' OK ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as [RD OK'].
  pose proof (gb1_model s t FC DL HP HL HM DP BC OL SL mc f h ovf R n dlen bits ovf' ER ltac:(lia) eq_refl eq_refl eq_refl eq_refl) as ER'.
  clear ER OK. rewrite <- EN in RD.
  assert (Rdl : 0 <= dlen < 65536) by (apply RDL; exact RD).
  assert (Rb : 1 <= bits <= 15) by (subst bits; destruct (Z.leb_spec (sd_max_length t) dlen); lia).
  assert (Ro' : ovf <= ovf' <= ovf + 1) by (subst ovf'; destruct (sd_max_length t <=? dlen); lia).
  assert (Rx0 : n <= mc -> 0 <= xbits t n < 16).
  { intros Hn. unfold xbits. destruct (Z.leb_spec (sd_extra_base t) n); [|lia]. destruct (XV m n MI ltac:(lia)) as [_ X]. exact X. }
  call (ugb1_head L T N h ovf (sd_extra_base t) mc (sd_max_length t) stp xp n dlen bits FC DL HP sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. }
  1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact Rh. } 1:{ reflexivity. } 1:{ exact Rn. } 1:{ exact RD. } 1:{ reflexivity. } 1:{ exact Rdl. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ reflexivity. }
  fold ovf'.
  pose proof (avct_zlength FC (arr_set DL n (wrap16 bits)) N ltac:(lia)) as LCT'. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  pose proof (av16_zlength (arr_set BC bits (wrap16 (arr_get BC bits + 1))) 16 ltac:(lia)) as L16'.
  unfold ugbR. destruct (Z.ltb_spec mc n) as [K|K].
  - try rewrite (proj2 (Z.ltb_lt mc n) K) in ER', OK'. unfold GB1_LATCH.
    call (ugb1_latch L T h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp sp).
    1:{ eassumption. } 1:{ exact Rh. }
    apply evt_done. unfold ugb1_iter_post. do 13 eexists. exists (arr_set DL n (wrap16 bits)), BC, OL, SL, ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact BLC|]. split; [exact GD|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [exact LBC|]. split; [exact RBC|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [exact ROL|]. split; [exact RSL|]. split; [exact Ro'|]. assumption.
  - try rewrite (proj2 (Z.ltb_ge mc n)) in ER', OK' by lia. unfold GB1_LEAF.
    pose proof (Rx0 ltac:(lia)) as Rx.
    call (ugb1_cnt L t T h ovf' mc stp xp n bits BC sp).
    1:{ exact BLC. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact Rxp. } 1:{ exact Axp. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rb. } 1:{ lia. } 1:{ lia. } 1:{ exact RBC. }
    match goal with HT : u8arr usegs ?mm T _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugb1_len L s t T N h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp n bits (xbits t n) OL SL FC (arr_set DL n (wrap16 bits)) h0 h1 h2 h3 h4 sp);
      [exact HT| exact GD| eassumption| exact LAY| exact RT1| exact RT2| lia| exact SV| exact Astp| exact Rn| lia| apply RFC; exact Rn| exact Rb| exact Rx| exact ROL| exact RSL|] end.
    call (ugb1_latch L T h ovf' (sd_extra_base t) mc (sd_max_length t) stp xp sp).
    1:{ eassumption. } 1:{ exact Rh. }
    apply evt_done. unfold ugb1_iter_post. do 13 eexists. exists (arr_set DL n (wrap16 bits)), (arr_set BC bits (wrap16 (arr_get BC bits + 1))).
    exists (wrap64 (OL + arr_get FC n * (bits + xbits t n))), (if stree_has t then wrap64 (SL + arr_get FC n * (stree_Len t n + xbits t n)) else SL), ovf'. do 2 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER'|]. split; [exact OK'|]. split; [rewrite arr_len_set; exact LDL|]. split; [rewrite arr_len_set; exact LBC|].
    split; [intros i Hi; destruct (Z.eq_dec bits i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RBC; exact Hi]|].
    split; [intros i Hi; destruct (Z.eq_dec n i) as [<-|NE]; [rewrite arr_get_set_same by lia; apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RDL; exact Hi]|].
    split; [apply wrap64_range|]. split; [destruct (stree_has t); [apply wrap64_range| exact RSL]|]. split; [exact Ro'|]. assumption.
Qed.
Definition ugb1_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N mc stp xp : Z) (FC HP : arr) (HL HM : Z) (DP : arr) (R : deflate_state * Z)
    (sp ra gp tp s6 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists s0 s1 s2 s4 s5 s7 s9 t6 h0 h1 h2 h3 h4 DL' BC' OL' SL' ovf' m',
    ms' = MS (ugbR L T 573 ovf' mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d484) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' h0 h1 h2 h3 h4)
    /\ R = (bt_upd s t FC DL' HP HL HM DP BC' OL' SL' mc, ovf')
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536) /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64 /\ 0 <= ovf' <= 573.
Lemma ugb1_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N h ovf mc stp xp OL SL : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R : deflate_state * Z) (m0 : mem)
    (sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L -> munch (uWgb L T N) m0 m -> wmono usegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= h < 573 -> 573 - h <= Z.of_nat f -> 0 <= ovf <= h -> -1 <= mc < sd_elems t -> (forall k, h <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R = gen_bitlen_loop1 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) h ovf ->
  gb1_ok t mc f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) h ovf ->
  evt usegs (ugb1_loop_post L s t T N mc stp xp FC HP HL HM DP R sp ra gp tp s6 s11 F fc m0)
      (MS (ugbR L T h ovf mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz 0x1d33c) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA BLC GD F64 MI LAY MU WM RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rh Hf Ro Rmc RHP RBC RDL RFC ROL RSL ER OK.
  { exfalso. lia. }
  pose proof (avct_zlength FC DL N ltac:(destruct t; subst N; cbv; discriminate)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  call (ugb1_iter L s t T N h ovf mc stp xp OL SL FC DL HP HL HM DP BC h0 h1 h2 h3 h4 f R sp).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. }
  1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. } 1:{ exact Rxp. } 1:{ exact Axp. } 1:{ exact Astp. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact Rh. } 1:{ exact Ro. } 1:{ exact Rmc. } 1:{ apply RHP; lia. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. }
  1:{ exact ROL. } 1:{ exact RSL. } 1:{ exact ER. } 1:{ exact OK. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4), HC : rw_cells usegs ?mm (bv_unsigned sp + 64) _,
                     ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ ?o', OK' : gb1_ok t mc f _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s t T N (h + 1) o' mc stp xp ol' sl' FC dl' HP HL HM DP bc' g0 g1 g2 g3 g4 R m0);
        [exact HT| exact HPA| exact HB| exact HG| exact HC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact EN| exact LFC| assumption| exact LHP| assumption
        | exact XV| exact SV| exact Rxp| exact Axp| exact Astp| exact SEP| exact RSP| lia| lia| lia| exact Rmc| intros k Hk; apply RHP; lia| assumption| assumption| exact RFC| assumption| assumption| exact ER'| exact OK'] end.
  - match goal with ER' : R = gen_bitlen_loop1 f _ _ _ _ _ _ _ |- _ => rewrite gb1_done in ER' by lia end.
    replace (h + 1) with 573 by lia.
    apply evt_done. unfold ugb1_loop_post. do 13 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4), ER' : R = (_, ?o') |- _ =>
      exists dl', bc', ol', sl', o'; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER'|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; lia end.
Qed.
