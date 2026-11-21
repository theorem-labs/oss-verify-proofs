(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13 Z_tr_bt14.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_pq Z_tr_bt_mid Z_tr_bt1 Z_tr_bt13 Z_tr_bt14 Z_tr_bt15 Z_tr_bt16 Z_tr_bt17 Z_tr_bt18.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Notation ONES := 18446744073709551615.
Notation uWgb L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 3008); (dl_As L + 5881, dl_As L + 5968)] (only parsing).
Definition ugb_main_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc : Z) (FC HP : arr) (HL : Z) (DP : arr) (R : deflate_state)
    (ra sp gp tp s6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s9 s11 t3 t4 t5 t6 DL' BC' OL' SL' g0 g1 g2 g3 g4 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz T) (wz mc) a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 s6 s7 (wz (dl_As L + 2976)) s9 (wz (dl_As L + 5912)) s11 t3 t4 t5 t6)
             F (wz 0x1d5c8) fc None m' (seg_rom usegs)
    /\ munch (uWgb L T N) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC DL' N)) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ R = bt_upd s t FC DL' HP HL hm DP BC' OL' SL' mc
    /\ arr_len DL' = N /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536) /\ (forall i, 0 <= i < N -> 0 <= arr_get DL' i < 65536)
    /\ 0 <= OL' < 2^64 /\ 0 <= SL' < 2^64.
Lemma ugb_main : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm mc stp xp OL SL : Z) (FC DL HP : arr) (HL : Z) (DP BC : arr) (h0 h1 h2 h3 h4 : list byte)
    (R1 : deflate_state * Z) (R : deflate_state)
    (ra sp gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) -> rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  xbits_view t xp -> stree_view_n t stp -> 0 < xp < 2^32 -> xp mod 4 = 0 -> stp mod 4 = 0 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= hm <= 570 -> -1 <= mc < sd_elems t -> (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP k < N) ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  R1 = gen_bitlen_loop1 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 ->
  gb1_ok t mc 573 (bt_upd s t FC DL HP HL hm DP BC OL SL mc) (hm + 1) 0 ->
  (forall X10 ovf, R1 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  R = gb_tail t mc R1 ->
  evt usegs (ugb_main_post L s t T N hm mc FC HP HL DP R ra sp gp tp s6 F fc m)
      (MS (ugbR L T (hm + 1) 0 mc (sd_max_length t) stp xp (sd_extra_base t) sp ra gp tp s0 s1 s2 s4 s5 s6 s7 s9 s11 t6) F (wz GB1_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR HPA BLC GD F64 MI LAY RT1 RT2 EN LFC LDL LHP LBC XV SV Rxp Axp Astp SEP RSP Rhm Rmc RHP RBC RDL RFC ROL RSL ER1 OK1 OK23 ER.
  pose proof (munch_refl (uWgb L T N) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (RE : sd_extra_base t <= 257 /\ 0 <= sd_extra_base t /\ 19 <= sd_elems t <= 286 /\ 7 <= sd_max_length t <= 15 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_extra_base sd_elems sd_max_length tsize]; unfold LITERALS, L_CODES, D_CODES, BL_CODES, MAX_BITS, MAX_BL_BITS; lia).
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold GB1_HEAD.
  call (ugb1_loop 573 L s t T N (hm + 1) 0 mc stp xp OL SL FC DL HP HL hm DP BC h0 h1 h2 h3 h4 R1 m).
  1:{ exact ARR. } 1:{ exact HPA. } 1:{ exact BLC. } 1:{ exact GD. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LHP. } 1:{ exact LBC. } 1:{ exact XV. } 1:{ exact SV. }
  1:{ exact Rxp. } 1:{ exact Axp. } 1:{ exact Astp. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ exact RBC. } 1:{ exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. }
  match goal with H : R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?ovf') |- _ => rename H into ER1'; clear ER1 end.
  unfold ugbR. zstep. br_cases K.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => rewrite ER1' in ER; replace o with 0 in ER by lia; rewrite gb_tail_0 in ER end.
    apply evt_done. unfold ugb_main_post. do 21 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol' ?sl' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl', bc', ol', sl', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [exact ER|] end.
    repeat (split; [assumption|]). assumption.
  -
    lazymatch type of ER1' with R1 = (?X, ?o) => destruct (OK23 X o ER1' ltac:(lia)) as [OK2 OK3]; rewrite ER1' in ER; rewrite (gb_tail_nz t mc X o) in ER by lia end.
    zs2. ustep BT_TRAP. zs2. ustep BT_TRAP. zs2. zstep. br_false.
    zs2. zs2. rewrite shl32_shr31 by lia. zstep. br_false. zs2. try rewrite shl32_shr32 by lia. try rewrite (Z.mod_small (sd_max_length t) 4294967296) by lia. zs2. zs2.
    lazymatch type of ER1' with R1 = (?X, ?o) => name_term R2 ER2 (gen_bitlen_loop2 573 X (sd_max_length t) o) end.
    match goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HT : u8arr usegs ?mm T (u16s (avct FC ?dl' N)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'; pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ ?bc' ?ol' ?sl' _, ?o) =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugl2_loop 573 L s t T o mc (sd_max_length t) FC dl' HP HL hm DP bc' ol' sl' R2 mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ assumption. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact ER2. } 1:{ exact OK2. }
    match goal with H : R2 = bt_upd _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite H in ER, OK3; clear H ER2 end.
    unfold ugl2R. zstep. br_false. zs2. ustep BT_TRAP. zs2. zs2. zstep.
    match goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
    lazymatch type of ER1' with R1 = (bt_upd _ _ _ ?dl' _ _ _ _ _ ?ol' ?sl' _, _) =>
    lazymatch goal with HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)), HG : rw_cells usegs ?mm' (dl_As L + 5881) (bD_cells L s _ _ ?g0 ?g1 ?g2 ?g3 ?g4)
      |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ug3_loop (Z.to_nat (sd_max_length t)) L s t T N (sd_max_length t) 573 mc ol' sl' FC dl' HP HL hm DP bc' g0 g1 g2 g3 g4 R mm) end end.
    1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ exact LHP. } 1:{ assumption. }
    1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ assumption. } 1:{ assumption. } 1:{ exact RFC. } 1:{ assumption. } 1:{ exact ER. } 1:{ exact OK3. }
    unfold ug3oR. apply evt_done. unfold ugb_main_post. do 21 eexists.
    match goal with HT : u8arr usegs ?mm T (u16s (avct FC ?dl'' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc'' 16)),
                     HG : rw_cells usegs ?mm (dl_As L + 5881) (bD_cells L s ?ol'' ?sl'' ?g0 ?g1 ?g2 ?g3 ?g4) |- _ =>
      exists dl'', bc'', ol'', sl'', g0, g1, g2, g3, g4; eexists;
      split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [exact HB|]; split; [exact HG|];
      split; [assumption|] end.
    repeat (split; [assumption|]). all: lia.
Qed.
Lemma XP_pos : forall t, 0 < XP t < 2 ^ 32. Proof. destruct t; cbn; lia. Qed.
Lemma XP_al4 : forall t, XP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Lemma STP_al4 : forall t, STP t mod 4 = 0. Proof. destruct t; reflexivity. Qed.
Notation uWpB L T N sp := [(T%Z, (T + 4 * N)%Z); (dl_As L + 2976, dl_As L + 5308); (dl_As L + 5881, dl_As L + 5968); (bv_unsigned sp + 72, bv_unsigned sp + 104)] (only parsing).
Definition upartB_post (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc mc : Z) (HP7 DP : arr) (hh : list byte) (R : deflate_state)
    (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) FC' DL' BC' OL' SL' g0 g1 g2 g3 g4 junk' m',
    ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz BT_EPI) fc None m' (seg_rom usegs)
    /\ munch (uWpB L T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL' N)) /\ u32arr usegs m' (dl_As L + 3008) (av32 HP7 573) /\ u8arr usegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz 1); C4 (wz hm)] /\ rw_cells usegs m' (dl_As L + 5881) (bD_cells L s OL' SL' g0 g1 g2 g3 g4)
    /\ rw_cells usegs m' dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] /\ rw_cells usegs m' (bv_unsigned sp + 72) [CB 32 junk']
    /\ R = bt_upd s t FC' DL' HP7 1 hm DP BC' OL' SL' mc /\ arr_len FC' = N /\ arr_len DL' = N /\ arr_len BC' = 16.
Lemma upartB : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N hm dsc mc OL SL : Z) (FC DL HP DP BC : arr) (hh h0 h1 h2 h3 h4 nc : list byte)
    (R : deflate_state)
    (x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  let HP7 := arr_set HP hm (arr_get HP 1) in
  let X7 := bt_upd s t FC DL HP7 1 hm DP BC OL SL mc in
  let X9 := bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) HP7 1 hm DP (arr_fill BC 0 16 0) OL SL mc in
  u8arr usegs m T (u16s (avct FC DL N)) -> u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 2976) (u16s (av16 BC 16)) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz 1); C4 (wz (hm + 1))] -> rw_cells usegs m (dl_As L + 5881) (bD_cells L s OL SL h0 h1 h2 h3 h4) ->
  rw_cells usegs m dsc [C8 (wz T); C4 (wz mc); CB 4 hh; C8 (wz (SDA t))] -> rw_cells usegs m (SDA t) (sd_cells t) ->
  rw_cells usegs m (bv_unsigned sp + 8) [C8 (wz mc)] -> rw_cells usegs m (bv_unsigned sp + 16) (ubt_f16 dsc t L T) ->
  rw_cells usegs m (bv_unsigned sp + 64) [C8 (wz (ONES - (dl_As L + 3008)))] -> rw_cells usegs m (bv_unsigned sp + 72) [CB 32 nc] ->
  mem_inv usegs m -> dlay_ok L ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N = tsize t -> T mod 4 = 0 -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len BC = 16 ->
  dsc = dl_As L + bt_desc t -> 0 <= hm <= 570 -> 0 <= arr_get HP 1 < N -> -1 <= mc < sd_elems t ->
  (forall k, hm + 1 <= k < 573 -> 0 <= arr_get HP7 k < N) ->
  (forall i, 0 <= i < N -> 0 <= arr_get DL i < 65536) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> 0 <= OL < 2^64 -> 0 <= SL < 2^64 ->
  dl_As L + 5968 <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  gb1_ok t mc 573 X9 (hm + 1) 0 ->
  (forall X10 ovf, gen_bitlen_loop1 573 X9 t mc (sd_extra_base t) (sd_max_length t) (hm + 1) 0 = (X10, ovf) -> ovf <> 0 ->
     gb2_ok (sd_max_length t) 573 X10 ovf /\ gb3_ok t mc (Z.to_nat (sd_max_length t)) (gen_bitlen_loop2 573 X10 (sd_max_length t) ovf) (sd_max_length t) 573) ->
  (forall i, 0 <= i <= mc -> 0 <= Len (gen_bitlen X7 t) t i <= 15) ->
  R = gen_codes (gen_bitlen X7 t) t mc ->
  evt usegs (upartB_post L s t T N hm dsc mc HP7 DP hh R sp gp tp F fc m)
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (wz (dl_As L + 3008)) s4 s5 (wz T) s7 (wz (dl_As L + 2976)) (wz (dl_As L + 5300)) s10 s11 t3 t4 t5 t6)
          F (wz BT_PARTB) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HP7 X7 X9 ARR HPA BLC GC GD Gdsc Gsd F8 F16 F64 F72 MI LAY RT1 RT2 EN AT LFC LDL LHP LBC Edsc Rhm Rh1 Rmc RHP RDL RFC ROL RSL SEP RSP
    OK1 OK23 LEN ER. subst HP7 X7 X9.
  pose proof (munch_refl (uWpB L T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM. pose proof LAY as LAY0. lay_open LAY0.
  assert (Bs : dl_As L + 5968 <= 0x10000 \/ 0x5f000 <= dl_As L) by (destruct (lo_s _ LAY) as (_ & _ & _ & Bs); exact Bs).
  assert (RE : 19 <= sd_elems t <= 286 /\ N = 2 * sd_elems t + 1)
    by (subst N; destruct t; cbn [sd_elems tsize]; unfold L_CODES, D_CODES, BL_CODES; lia).
  pose proof (bt_desc_range t) as Rdsc. pose proof (SDA_range t) as RSDA.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (av32_zlength HP 573 ltac:(lia)) as L32. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (gen_bitlen_flat s t FC DL (arr_set HP hm (arr_get HP 1)) 1 hm DP BC OL SL mc) in ER, LEN.
  rewrite (arr_get_set_same HP hm (arr_get HP 1)) in ER, LEN by lia.
  name_term R1 ER1 (gen_bitlen_loop1 573 (bt_upd s t FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 hm DP (arr_fill BC 0 16 0) OL SL mc) t mc
                       (sd_extra_base t) (sd_max_length t) (hm + 1) 0).
  name_term RB ERB (gb_tail t mc R1).
  unfold sd_cells in Gsd.
  call (ugb_pre1 L t T hm dsc mc HP hh).
  1:{ exact HPA. } 1:{ exact GC. } 1:{ exact Gdsc. } 1:{ exact Gsd. } 1:{ exact F16. } 1:{ exact F64. } 1:{ exact MI. } 1:{ exact LAY. }
  1:{ exact LHP. } 1:{ exact Rhm. } 1:{ lia. } 1:{ lia. } 1:{ exact Edsc. } 1:{ exact SEP. } 1:{ exact RSP. }
  pose proof (av32_zlength (arr_set HP hm (arr_get HP 1)) 573 ltac:(lia)) as L32'.
  unfold UGB_PRE2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ugb_pre2 L t T N hm mc FC DL (arr_set HP hm (arr_get HP 1)) BC (arr_get HP 1)) end.
  1:{ exact ARR. } 1:{ eassumption. } 1:{ exact BLC. } 1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact AT. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ exact LBC. }
  1:{ exact Rhm. } 1:{ rewrite arr_get_set_same by lia. reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact SEP. } 1:{ exact RSP. }
  pose proof (avct_zlength FC (arr_set DL (arr_get HP 1) (wrap16 0)) N ltac:(lia)) as LCT'. pose proof (av16_zlength (arr_fill BC 0 16 0) 16 ltac:(lia)) as L16'.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (ugb_main L s t T N hm mc (STP t) (XP t) OL SL FC (arr_set DL (arr_get HP 1) (wrap16 0)) (arr_set HP hm (arr_get HP 1)) 1 DP (arr_fill BC 0 16 0) h0 h1 h2 h3 h4 R1 RB) end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact GD. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact EN. } 1:{ exact LFC. } 1:{ rewrite arr_len_set. exact LDL. } 1:{ rewrite arr_len_set. exact LHP. } 1:{ rewrite arr_len_fill. exact LBC. }
  1:{ apply xbits_view_of. } 1:{ apply stree_view_n_of. } 1:{ apply XP_pos. } 1:{ apply XP_al4. } 1:{ apply STP_al4. } 1:{ exact SEP. } 1:{ exact RSP. }
  1:{ exact Rhm. } 1:{ exact Rmc. } 1:{ exact RHP. } 1:{ intros i Hi. apply blc_zero_range; [exact LBC| exact Hi]. }
  1:{ apply arr_set_range16. exact RDL. } 1:{ exact RFC. } 1:{ exact ROL. } 1:{ exact RSL. }
  1:{ exact ER1. } 1:{ exact OK1. } 1:{ exact OK23. } 1:{ exact ERB. }
  match goal with H : RB = bt_upd _ _ _ ?dl' _ _ _ _ ?bc' _ _ _ |- _ => rewrite H in ER, LEN; clear H ERB;
    pose proof (avct_zlength FC dl' N ltac:(lia)) as LCT''; pose proof (av16_zlength bc' 16 ltac:(lia)) as L16'' end.
  match goal with HG : rw_cells usegs _ (dl_As L + 5881) (bD_cells _ _ _ _ _ _ _ _ _) |- _ => unfold bD_cells in HG end.
  lazymatch goal with HF : rw_cells usegs ?mm (bv_unsigned sp + 16) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) |- _ =>
    destruct (proj1 (rw_cells_app_iff mm _ [c0] (c1 :: c2 :: c3 :: c4 :: rest)) HF) as [_ HF1];
    destruct (proj1 (rw_cells_app_iff mm _ [c1] (c2 :: c3 :: c4 :: rest)) HF1) as [F24 HF2]; clear HF1;
    destruct (proj1 (rw_cells_app_iff mm _ [c2; c3] (c4 :: rest)) HF2) as [_ HF3]; clear HF2;
    destruct (proj1 (rw_cells_app_iff mm _ [c4] rest) HF3) as [F48 _]; clear HF3;
    cbn [cells_size csize Nat.add] in F24, F48 end.
  change (Z.of_nat 8) with 8 in F24. change (Z.of_nat 8) with 8 in F48. change (Z.of_nat 16) with 16 in F48.
  lazymatch type of F24 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + 24) in F24 by lia end.
  lazymatch type of F48 with rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + 48) in F48 by lia end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch type of ER with R = gen_codes (bt_upd s t FC ?dl' ?hp' 1 hm DP ?bc' ?ol' ?sl' mc) t mc =>
    call (ugcs_phase s t L T N mc FC dl' hp' 1 hm DP bc' ol' sl' mc R nc) end end.
  1:{ eassumption. } 1:{ eassumption. } 1:{ eassumption. } 1:{ exact F8. } 1:{ exact F24. } 1:{ exact F48. } 1:{ eassumption. } 1:{ exact LAY. }
  1:{ exact RT1. } 1:{ exact RT2. } 1:{ lia. } 1:{ exact LFC. } 1:{ assumption. } 1:{ assumption. } 1:{ assumption. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ lia. }
  1:{ intros i Hi. pose proof (LEN i Hi) as Li. rewrite bt_Len in Li. exact Li. } 1:{ exact ER. }
  apply evt_done. unfold upartB_post. do 28 eexists.
  match goal with HT : u8arr usegs ?mm T (u16s (avct ?fc' ?dl' N)), HB : u8arr usegs ?mm (dl_As L + 2976) (u16s (av16 ?bc' 16)),
                   HG : rw_cells usegs ?mm (dl_As L + 5881) [CB 7 ?g0; _; _; _; _; CB 4 ?g1; C8 (wz ?ol'); C8 (wz ?sl'); _; _; _; CB 2 ?g2; _; CB 4 ?g3; _; _; CB 4 ?g4; _],
                   HF : rw_cells usegs ?mm (bv_unsigned sp + 72) [CB 32 ?j] |- _ =>
    exists fc', dl', bc', ol', sl', g0, g1, g2, g3, g4, j; eexists;
    split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [exact HT|]; split; [eassumption|]; split; [exact HB|];
    split; [eassumption|]; split; [exact HG|]; split; [eassumption|]; split; [exact HF|] end.
  repeat (split; [assumption|]). assumption.
Qed.
