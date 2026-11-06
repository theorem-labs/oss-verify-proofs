(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RF_memcpy RY_buf_append.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac slia := Zify.zify; xlia zchecker.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ens_first (b : ybuf) : yprog (ybuf + ybuf) :=
  match yb_data b with
  | None =>
      r <- ymalloc YAJL_BUF_INIT_SIZE ;;
      match r with
      | None => b' <- ybuf_set_error (mkBuf BS_ok YAJL_BUF_INIT_SIZE (yb_used b) None (yb_bytes b)) BS_overflow ;; YRet (inr b')
      | Some d => YRet (inl (mkBuf BS_ok YAJL_BUF_INIT_SIZE (yb_used b) (Some d) (yb_bytes b)))
      end
  | Some _ => YRet (inl b)
  end.
Definition ens_tail (want : Z) (b1 : ybuf) : yprog ybuf :=
  if want =? 0 then YRet b1 else
  let need := ens_need_loop ENS_FUEL want (yb_len b1) (yb_used b1) in
  if (need <? yb_used b1) || (need =? 0) then ybuf_set_error b1 BS_overflow
  else if negb (need =? yb_len b1) then
    r <- yrealloc (yb_data b1) need ;;
    match r with
    | None => ybuf_set_error (mkBuf BS_ok (yb_len b1) (yb_used b1) None (yb_bytes b1)) BS_overflow
    | Some d => YRet (mkBuf BS_ok need (yb_used b1) (Some d) (yb_bytes b1))
    end
  else YRet b1.
Definition app_tail (src : list Z) (b1 : ybuf) : yprog ybuf :=
  match yb_state b1 with
  | BS_ok => if 0 <? zlength src
             then YRet (mkBuf BS_ok (yb_len b1) (yb_used b1 + zlength src) (yb_data b1) (yb_bytes b1 ++ src))
             else YRet b1
  | _ => YRet b1
  end.

Lemma ybuf_append_ok_eq : forall b src, yb_state b = BS_ok ->
  ybuf_append b src =
  (b1 <- (first <- ens_first b ;; match first with inr b' => YRet b' | inl b1 => ens_tail (zlength src) b1 end) ;;
   app_tail src b1).
Proof. intros b src Hs. unfold ybuf_append, ybuf_ensure_available. rewrite Hs. reflexivity. Qed.

(* [comment removed for export] *)
Lemma app_leaf_inl : forall b src b1 bf,
  yb_state b = BS_ok -> yleaf (ens_first b) (inl b1) ->
  yleaf (b2 <- ens_tail (zlength src) b1 ;; app_tail src b2) bf ->
  yleaf (ybuf_append b src) bf.
Proof.
  intros b src b1 bf Hs H1 H2. rewrite (ybuf_append_ok_eq b src Hs).
  apply yleaf_bind_inv in H2. destruct H2 as (b2 & H2 & H3).
  eapply yleaf_bind; [| exact H3]. eapply yleaf_bind; [exact H1|]. cbn. exact H2.
Qed.
Lemma app_leaf_inr : forall b src b',
  yb_state b = BS_ok -> yleaf (ens_first b) (inr b') -> yb_state b' <> BS_ok ->
  yleaf (ybuf_append b src) b'.
Proof.
  intros b src b' Hs H1 Hs'. rewrite (ybuf_append_ok_eq b src Hs).
  eapply yleaf_bind. { eapply yleaf_bind; [exact H1|]. cbn. apply yl_ret. }
  unfold app_tail. destruct (yb_state b'); [congruence| apply yl_ret| apply yl_ret].
Qed.
Lemma app_leaf_notok : forall b src, yb_state b <> BS_ok -> yleaf (ybuf_append b src) b.
Proof.
  intros b src Hs. unfold ybuf_append, ybuf_ensure_available.
  destruct (yb_state b) eqn:E; [congruence| |]; cbn; rewrite E; apply yl_ret.
Qed.

(* [comment removed for export] *)
Lemma src_pres : forall (REST : list block) (sp : word) (SA : Z) (src : list Z) LBx m1 m2,
  ysrc_range REST sp SA (zlength src) ->
  rheap_pres LBx (bv_unsigned sp + -48) m1 m2 -> (forall bt, In bt REST -> In bt LBx) ->
  mem_inv rsegs m1 -> mem_inv rsegs m2 -> bytes_at rsegs m1 SA (zbytes src) -> bytes_at rsegs m2 SA (zbytes src).
Proof.
  intros REST sp SA src LBx m1 m2 YSR HP HI MI1 MI2 TB. pose proof (zbytes_length src) as ZL.
  destruct YSR as [(bt & HBT & T1 & T2)|[R2|[R3|R4]]].
  - eapply rheap_pres_bytes_at; [exact HP| exact TB|]. right; right. exists bt. split; [apply HI; exact HBT|]. rewrite ZL. unfold zlength in *. lia.
  - eapply rodata_bytes_persist; [exact TB| exact MI1| exact MI2| lia|]. rewrite ZL. unfold zlength in *. lia.
  - eapply rheap_pres_bytes_at; [exact HP| exact TB|]. left. lia.
  - destruct src; [| unfold zlength in R4; cbn in R4; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_at_nil_any : forall m1 m2 A, bytes_at rsegs m1 A [] -> bytes_at rsegs m2 A [].
Proof. intros m1 m2 A (B0 & B1 & _). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia. Qed.
Lemma bytes_at_transport' : forall W m m' A bs,
  bytes_at rsegs m A bs -> munch W m m' -> ((0 < length bs)%nat -> disjoint_from W A (Z.of_nat (length bs))) ->
  bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs TB MU D. destruct bs as [|c bs'].
  - eapply bytes_at_nil_any. exact TB.
  - eapply (bytes_at_transport rsegs); [exact TB| exact MU| apply D; cbn; lia].
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWM : ywrap_malloc_stmt HK.
Hypothesis YWR : ywrap_realloc_stmt HK.

Section Fn.
Variables (REST : list block) (mb : mbuf) (b : ybuf) (AF SA : Z) (src : list Z) (lo B : Z) (errv : word) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
Let n := zlength src.
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (s' : PState)
    (b' : ybuf) (mb' : mbuf) (LK : list block),
  ybuf_append_rpost HK sp tp m REST mb b AF SA src lo B errv a0' m' mo' s' b' mb' LK ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                           F (ret_pc ra) fc None m' (seg_rom rsegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = wz RATP.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - RY_BUF_APPEND_STACK.
Hypothesis SPB : bv_unsigned sp <= B.
Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
Hypothesis LO0 : 0 <= lo.
Hypothesis HBIN : exists hb, In hb REST /\ blk_addr hb <= AF /\ AF + 32 <= blk_addr hb + blk_size hb.
Hypothesis SRCF : Forall (fun c => 0 <= c < 256) src.
Hypothesis SNZ : 0 < n -> SA <> 0.
Hypothesis SBND : SA + n <= 2^64.
Hypothesis YSR : ysrc_range REST sp SA n.
Hypothesis FB : Forall (fun c => 0 <= c < 256) (yb_bytes b).
Hypothesis YR : yroom REST 3.

Let J_ret := app_ret HK HKS REST mb b AF SA src lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m CONT TP LO.
Let J_copy := app_copy HK HKS HKF HKB REST mb b AF SA src lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m CONT TP CEIL LO SPB HBIN SRCF SNZ YSR FB.


(* [comment removed for export] *)
Lemma app_size : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (LK : list block) (junkf junk : list byte) (errv1 : word)
    (len1 used1 : Z) (d1 : yptr) (did1 : bptr) (D1 : Z),
  let b1 := mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b) in
  let mb1 := mkMB (mb_id mb) (mb_addr mb) did1 D1 in
  HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  app_frame ra sp s0 s1 s2 s3 m1 junkf -> stk rsegs m1 lo (bv_unsigned sp + -48) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 AF (alloc_cells ryc) ->
  rw_cells rsegs m1 (mb_addr mb) [C4 (wz 0); C4 (wz len1); C4 (wz used1); C4 (wz 0); C8 (wz D1); C8 (wz AF)] ->
  rw_cells rsegs m1 D1 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (len1 - used1 - 1)) junk] ->
  bytes_at rsegs m1 SA (zbytes src) ->
  0 <= used1 -> used1 = zlength (yb_bytes b) -> used1 < len1 -> len1 < 2^31 -> 0 < n -> used1 + n < 2^26 ->
  LK = [] ->
  (forall bf, yleaf (b2 <- ens_tail n b1 ;; app_tail src b2) bf -> yleaf (ybuf_append b src) bf) ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz (mb_addr mb)) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 (wz SA) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz 0x15108) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros until D1. cbv zeta. intros HK1 YS1 FR STK MI AX ERR PRES YAF BC DC TB U0 UB UL L31 NPOS N30 LKN HL.
  unfold app_frame, wz in *. pose proof LO as LO'. unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  destruct HBIN as (hb & HBI & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK1) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK1) as ND.
  cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app] in RNG, SEP, HK1, ND.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as BR. unfold rblock_range, alloc_ceiling in BR. cbn [blk_addr blk_size fst snd] in BR.
  destruct BR as (BR0 & _ & _ & BR3 & BR4).
  pose proof (all_range_In _ _ RNG (or_intror (or_introl eq_refl))) as DR. unfold rblock_range, alloc_ceiling in DR. cbn [blk_addr blk_size fst snd] in DR.
  destruct DR as (DR0 & _ & _ & DR3 & DR4).
  assert (HBI' : In hb ((mb_id mb, mb_addr mb, SIZEOF_BUF) :: (did1, D1, len1) :: LK ++ REST)) by (right; right; apply in_or_app; right; exact HBI).
  pose proof (all_range_In _ _ RNG HBI') as HBR. unfold rblock_range, alloc_ceiling in HBR. destruct HBR as (_ & _ & _ & HBR3 & _).
  cbn [all_sep] in SEP. destruct SEP as (SEPB & SEPD & _). cbn [sep_from] in SEPB. destruct SEPB as [SBD SEPB].
  unfold bsep in SBD. cbn [blk_addr blk_size fst snd] in SBD.
  pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBI)) as SBH. unfold bsep in SBH. cbn [blk_addr blk_size fst snd] in SBH.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, SIZEOF_BUF in *.
  unfold wz in YAF. unfold RERRNO in ERR.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB. pose proof (zbytes_length src) as ZL. pose proof (zbytes_length (yb_bytes b)) as ZLB.
  unfold n, zlength in *.
  set (nz := Z.of_nat (length src)) in *.
  destruct (proj1 (proj1 DC)) as (LZB & _ & LJ & _). cbn [cell_wf] in LZB, LJ.
  assert (SSEPB : SA + nz <= mb_addr mb \/ mb_addr mb + 32 <= SA).
  { destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[Y3|Y4]]]; [| clear -Y2 BR4 TBB ZL; slia| clear -Y3 LO' BR3 CEIL'; slia| lia].
    pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBT)) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X.
    clear -X T1 T2 ZL. lia. }
  (* [comment removed for export] *)
  pose proof (ens_need_loop_bounds nz len1 used1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as NB. cbv zeta in NB.
  set (r := ens_need_loop ENS_FUEL nz len1 used1) in *.
  assert (R31 : r < 2^31) by (clear -NB N30 L31; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear -SPR LO' LO0; lia).
  (* [comment removed for export] *)
  yhide BR4. yhide DR4. yhide SBD. yhide SBH. yhide SSEPB. yhide SEPB. yhide SEPD. clear RNG. yhide YSR.
  yhide FR. yhide ERR. yhide TB. yhide DC.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  rz_seg HKS HK1.
  zstep. rewrite ysx32_small by lia. zstep. rewrite ysx32_small by lia. zstep.
  eapply evt_cut.
  { eapply (size_loop ENS_FUEL len1); try lia. change (2 ^ Z.of_nat ENS_FUEL) with (2^64). clear -UL U0 N30 L31 NPOS. nia. }
  cbv beta. intros ms1 (a2s & a3s & ->). fold r. unfold wz.
  zstep. if_cases K1; zify_cond K1. 1:{ kill K1. }
  zstep. if_cases K2; zify_cond K2. 1:{ kill K2. }
  clear K1 K2.
  zstep. if_cases K3; zify_cond K3.
  - (* [comment removed for export] *)
    apply evt_done. yreveal FR MU WM. yreveal ERR MU WM. yreveal TB MU WM. yreveal DC MU WM.
    assert (RL : r = len1) by (revert K3; rewrite ?unsigned_lit by lia; lia). clear K3.
    eapply (J_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo1 s1' LK junkf junk errv1 len1 used1 d1 did1 D1);
      [ exact HK1 | exact YS1 | exact FR | exact STK | exact MI | exact AX | exact ERR | exact PRES | | exact BC | exact DC | exact TB
      | lia | lia | lia | lia | lia | | exact LKN ].
    { unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz. exact YAF. }
    apply HL. apply (yleaf_bind _ _ (mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b))).
    + unfold ens_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
      replace (nz =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold r.
      replace ((r <? used1) || (r =? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.eqb_neq]; clear -NB U0; lia).
      replace (negb (r =? len1)) with false by (symmetry; rewrite RL, Z.eqb_refl; reflexivity).
      apply yl_ret.
    + unfold app_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
      replace (0 <? nz) with true by (symmetry; apply Z.ltb_lt; lia). apply yl_ret.
  - (* [comment removed for export] *)
    assert (RNE : r <> len1) by (revert K3; rewrite ?unsigned_lit by lia; lia). clear K3.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. yshow ERR. yshow DC. yshow TB. yshow FR.
    pose proof (rw_cells_bytes_at _ _ _ _ DC) as OLD. cbn [cells_bytes cbytes] in OLD. rewrite app_nil_r in OLD.
    eapply YWR with (p := did1) (A := D1) (sz := len1) (n := r) (lo := lo) (B := B);
      [exact K0 | exact HK1 | right; left; reflexivity | exact OLD
      | rewrite !length_app, LZB, LJ; cbn [length]; clear -U0 UL; lia
      | exact AX | rewrite ESP; clear -SPB; lia | rewrite ESP; exact STK | exact CEIL
      | rewrite ESP; unfold RY_WRAP_STACK; clear -LO'; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR
      | exact MI | exact TP | reflexivity | reflexivity | unfold NUSERc; clear -RNE NB U0 N30 NPOS; lia
      | subst LK; cbn [length app]; clear -YR; unfold yroom in YR; lia | ].
    cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' errv2 p2 D2 MI2 STK2 ERR2 AX2 A0' R2 HK2 HP NEW0.
    replace (ret_pc (Z_to_bv 64 86348)) with (Z_to_bv 64 86348) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ESP in STK2. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
    clear MU WM.
    + (* [comment removed for export] *)
      destruct NEW0 as [junk2 NEW]. subst a0'. rewrite ESP in HP. unfold wz.
      unfold rblock_range, alloc_ceiling in R2. destruct R2 as (R20 & _ & _ & R23 & R24). yhide R24.
      rewrite (lb_remove_second did1 (mb_id mb, mb_addr mb, 32) (did1, D1, len1) (LK ++ REST) eq_refl ND) in HK2, HP.
      pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2.
      pose proof (ypres_frame _ _ _ _ _ _ HP FR ltac:(clear; lia)) as FR2. clear FR.
      pose proof (ypres_block _ _ _ _ _ _ HP YAF ltac:(exists hb; split; [right; apply in_or_app; right; exact HBI| cbn; clear -HB1 HB2; lia])) as YAF2. clear YAF.
      pose proof (ypres_block _ _ _ _ _ _ HP BC ltac:(eexists; split; [left; reflexivity| cbn; clear; lia])) as BC2. clear BC.
      pose proof (src_pres REST sp SA src _ _ _ YSR HP ltac:(intros bt Hbt; right; apply in_or_app; right; exact Hbt) MI MI2 TB) as TB2. clear TB DC OLD.
      assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
      { eapply ry_pres_trans; [exact PRES|]. apply ry_pres_of_rheap_pres.
        eapply rheap_pres_weaken; [exact HP| clear; lia| intros b0 Hb0; right; apply in_or_app; right; exact Hb0]. }
      clear HP MI AX ERR STK HK1 YS1.
      replace (Z.min r len1) with len1 in NEW by (clear -NB; lia).
      rewrite firstn_all2 in NEW by (rewrite !length_app, LZB, LJ; cbn [length]; clear -U0 UL; lia).
      (* [comment removed for export] *)
      assert (HK2' : HK s2' ((mb_id mb, mb_addr mb, 32) :: (p2, D2, r) :: LK ++ REST) m2 mo2).
      { eapply HKP; [exact HK2|]. apply Permutation.perm_swap. }
      clear HK2.
      assert (UD2 : bv_unsigned (Z_to_bv 64 D2) = D2) by (apply unsigned_lit; clear -R20 R23 NB U0; lia).
      destruct (HK_blocks HK HKB _ _ _ _ HK2') as [_ SEP2]. cbn [all_sep sep_from app] in SEP2.
      destruct SEP2 as ((SBD2 & _) & _). unfold bsep in SBD2. cbn [blk_addr blk_size fst snd] in SBD2. yhide SBD2.
      pose proof (munch_refl [(mb_addr mb, mb_addr mb + 32)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
      yhide FR2. yhide TB2. yhide YAF2. yhide ERR2. yhide NEW.
      rz_seg HKS HK2'.
      step. step. if_cases K4; zify_cond K4. 1:{ kill K4. } clear K4.
      step.
      apply evt_done.
      yreveal FR2 MU WM. yshow SSEPB. yreveal TB2 MU WM. yhide SSEPB. yshow SBH. yreveal YAF2 MU WM. yhide SBH.
      yshow BR4. yreveal ERR2 MU WM. yhide BR4. yshow SBD2. yreveal NEW MU WM. yhide SBD2.
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m3 end.
      lazymatch goal with H : rw_cells _ m3 (mb_addr mb) _ |- _ => rename H into BC3 end.
      lazymatch goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
      destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2' AX2 MU WM) as [HK3 AX3].
      { constructor; [| constructor]. right; right. eexists. split; [left; reflexivity| cbn; clear; lia]. }
      { constructor; [| constructor]. cbn. unfold RAUXV_CELL. yshow BR4. clear -BR4 BR3 CEIL' LO' SPB. lia. }
      yshow BR4. pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -BR4; lia| constructor])) as YS3. yhide BR4.
      (* [comment removed for export] *)
      assert (DC3 : rw_cells rsegs m3 D2 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (r - used1 - 1)) (junk ++ junk2)]).
      { pose proof (proj1 (proj1 NEW)) as WF2. cbn [cells_wf cell_wf] in WF2. destruct WF2 as (_ & LJ2 & _).
        eapply rw_cells_recast; [exact NEW| | |].
        - cbn [cells_wf cell_wf]. rewrite length_app, LJ, LJ2. clear -U0 UL NB LZB. repeat split; lia.
        - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity.
        - cbn [cells_size csize]. clear -U0 UL NB. lia. }
      clear NEW.
      eapply (J_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo2 s2' LK junkf (junk ++ junk2) errv2 r used1 d1 p2 D2);
        [ exact HK3 | exact YS3 | exact FR2 | exact STK2 | exact MI3 | exact AX3 | exact ERR2 | | | exact BC3 | exact DC3 | exact TB2
        | exact U0 | exact UB | clear -NB; lia | exact R31 | exact NPOS | | exact LKN ].
      * eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
        yshow SEPB. yshow BR4.
        intros a Ha Hc _. cbn. split; [| exact I].
        destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' BR3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc BR4; lia|].
        pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact Hb)) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. clear -Hs Hr. lia.
      * unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz. exact YAF2.
      * apply HL. apply (yleaf_bind _ _ (mkBuf BS_ok r used1 (Some d1) (yb_bytes b))).
        -- unfold ens_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
           replace (nz =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold r.
           replace ((r <? used1) || (r =? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.eqb_neq]; clear -NB U0; lia).
           replace (negb (r =? len1)) with true by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) RNE); reflexivity).
           apply (yleaf_bind _ _ (Some d1)); [apply yleaf_yrealloc| apply yl_ret].
        -- unfold app_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
           replace (0 <? nz) with true by (symmetry; apply Z.ltb_lt; lia). apply yl_ret.
Qed.
End Fn.

(* [comment removed for export] *)
Lemma ybuf_append_spec : ybuf_append_stmt HK.
Proof.
  unfold ybuf_append_stmt. intros REST mb b AF SA src lo B errv K. intros until s. intros K0 RY BR BI YAF AFIN TB SRCF SNZ SBND N30 YSR YR FP A0 A1 A2 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct BR as ((BC & DZ & RL & RU) & BD & FB).
  pose proof LO as LO'. unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO'.
  pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
  pose proof AFIN as AFIN0. destruct AFIN as (hb & HBI & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP]. pose proof (HK_nodup HK HKB _ _ _ _ HK0) as ND.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as BRG. unfold rblock_range, alloc_ceiling in BRG. cbn [blk_addr blk_size fst snd] in BRG.
  destruct BRG as (BR0 & _ & _ & BR3 & BR4).
  assert (HBI' : In hb (buf_blocks mb b ++ REST)) by (apply in_or_app; right; exact HBI).
  pose proof (all_range_In _ _ RNG HBI') as HBR. unfold rblock_range, alloc_ceiling in HBR. destruct HBR as (_ & _ & _ & HBR3 & _).
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  (* [comment removed for export] *)
  pose proof (app_ret HK HKS REST mb b AF SA src lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m CONT TP LO) as J_ret.
  pose proof (app_size REST mb b AF SA src lo B errv K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m CONT K0 TP CEIL LO SPB SPR LO0 AFIN0 SRCF SNZ YSR FB YR) as J_size.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold buf_cells in BC.
  unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, SIZEOF_BUF, RY_BUF_APPEND, wz in *.
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (zbytes_length src) as ZL. pose proof (zbytes_length (yb_bytes b)) as ZLB.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB.
  subst a0 a1 a2.
  set (nz := zlength src) in *.
  assert (NZE : nz = Z.of_nat (length src)) by reflexivity.
  assert (NZ0 : 0 <= nz) by (unfold nz, zlength; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear -SPR LO' LO0; lia).
  destruct BI as (I1 & I2 & I3 & I4 & I5 & I6).
  cbn [all_sep] in SEP. destruct SEP as [SEPB SEP'].
  pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBI)) as SBH. unfold bsep, SIZEOF_BUF in SBH. cbn [blk_addr blk_size fst snd] in SBH. yhide SBH.
  yhide BR4. yhide SEPB. yhide RNG.
  (* [comment removed for export] *)
  assert (PRESW : forall m1, munch [(bv_unsigned sp + -48, bv_unsigned sp); (mb_addr mb, mb_addr mb + 32)] m m1 -> wmono rsegs m m1 ->
                  ry_pres REST (bv_unsigned sp) [] m m1).
  { intros m1 MU1 WM1. eapply ryajl_pres_of_munch; [exact MU1| exact WM1|]. yshow SEPB. yshow BR4.
    intros a Ha Hc _. cbn. split; [| split; [| exact I]].
    - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc LO' CEIL'; lia|].
      pose proof (all_range_In _ _ ltac:(exact (proj1 (HK_blocks HK HKB _ _ _ _ HK0))) (ltac:(apply in_or_app; right; exact Hb))) as Hbr.
      unfold rblock_range, alloc_ceiling in Hbr. clear -Hbr Hr LO' CEIL'. lia.
    - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' BR3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc BR4; lia|].
      pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact Hb)) as Hs. clear -Hs Hr. unfold bsep, blk_addr, blk_size, SIZEOF_BUF in *. cbn [fst snd] in *. lia. }
  (* [comment removed for export] *)
  assert (SFACTS : 0 < nz -> (SA + nz <= bv_unsigned sp + -48 \/ bv_unsigned sp <= SA) /\ (SA + nz <= mb_addr mb \/ mb_addr mb + 32 <= SA)).
  { intros NP. yshow SEPB. yshow BR4. destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[Y3|Y4]]]; [| clear -Y2 BR4 LO' CEIL'; lia| clear -Y3 LO' BR3 CEIL'; lia| exfalso; clear -NP Y4; lia].
    pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBT)) as X.
    pose proof (all_range_In _ _ ltac:(exact (proj1 (HK_blocks HK HKB _ _ _ _ HK0))) (ltac:(apply in_or_app; right; exact HBT))) as Y.
    clear -X Y T1 T2 LO' CEIL'. unfold bsep, rblock_range, blk_addr, blk_size, SIZEOF_BUF, alloc_ceiling in *. cbn [fst snd] in *. lia. }
  (* [comment removed for export] *)
  yhide TB. yhide YAF. yhide ERR.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp); (mb_addr mb, mb_addr mb + 32)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  assert (OWN : forall m1, munch [(bv_unsigned sp + -48, bv_unsigned sp); (mb_addr mb, mb_addr mb + 32)] m m1 -> wmono rsegs m m1 ->
            (HK s (buf_blocks mb b ++ REST) m1 mo /\ rauxv_ok m1 B) /\ ystatics m1).
  { intros m1 MU1 WM1. split.
    - eapply (yown_writes HK HKF); [exact HK0| exact AX| exact MU1| exact WM1| |].
      + apply Forall_cons; [left; cbn [fst snd]; unfold alloc_ceiling; clear -LO' CEIL'; lia|].
        apply Forall_cons; [right; right; eexists; split; [left; reflexivity| cbn [fst snd blk_addr blk_size]; unfold SIZEOF_BUF; clear; lia]|]. apply Forall_nil.
      + apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; clear -SPB LO' CEIL'; lia|].
        apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; yshow BR4; clear -BR4 BR3 CEIL' LO' SPB; lia|]. apply Forall_nil.
    - yshow BR4. eapply ystatics_munch; [exact YS| exact MU1| exact WM1|].
      apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -LO' CEIL'; lia|].
      apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -BR4; lia|]. apply Forall_nil. }
  destruct (yb_state b) eqn:HS.
  2,3: (* [comment removed for export] *)
    cbn [buf_state_code] in BC;
    rz_seg HKS HK0;
    step; carve_frame 48%nat STK; step; step; step; step; step;
    (step; if_cases K1; zify_cond K1; [kill K1|]);
    step; step; rewrite ysx32_small by (clear; lia);
    (step; if_cases K2; zify_cond K2; [| kill K2]);
    apply evt_done; yshow SBH; yreveal YAF MU WM; yhide SBH; yshow BR4; yreveal ERR MU WM; yhide BR4;
    destruct (OWN _ MU WM) as [[HK1 AX1] YS1];
    (eapply (J_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mo s b mb []);
     [ change ([] ++ REST) with REST; exact HK1 | exact YS1 | eassumption | eassumption | eassumption | exact AX1 | eassumption
     | apply PRESW; assumption
     | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]; unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz; exact YAF
     | apply app_leaf_notok; first [rewrite HS; discriminate | discriminate]
     | split; [split; [unfold buf_cells; rewrite HS; cbn [buf_state_code]; unfold wz; eassumption| split; [exact DZ| lia]]| split; [| exact FB]]
     | split; reflexivity | reflexivity ]).
  2,3: unfold buf_data in BD |- *; specialize (I6 ltac:(first [discriminate | rewrite HS; discriminate])); rewrite I6 in *; exact I.
  - (* [comment removed for export] *)
    cbn [buf_state_code] in BC.
    destruct (yb_data b) as [d0|] eqn:HD.
    + (* [comment removed for export] *)
      specialize (I5 ltac:(discriminate)).
      assert (D0 : mb_data mb <> 0) by (intros E; apply DZ in E; discriminate).
      unfold buf_data in BD. rewrite HD in BD. destruct BD as (_ & junk0 & DC).
      pose proof (rw_cells_bound _ _ _ _ DC) as DCB. cbn [cells_size csize Nat.add] in DCB. yhide DC.
      yshow RNG. unfold buf_blocks in RNG. try rewrite HD in RNG. cbn [all_range app] in RNG. destruct RNG as (_ & DRG & _).
      unfold rblock_range, alloc_ceiling in DRG. cbn [blk_addr blk_size fst snd] in DRG. destruct DRG as (DR0 & _ & _ & DR3 & DR4). yhide DR4.
      yshow SEPB. unfold buf_blocks in SEPB. try rewrite HD in SEPB. cbn [sep_from app] in SEPB. destruct SEPB as [SBD SEPB]. yhide SEPB.
      unfold bsep, SIZEOF_BUF in SBD. cbn [blk_addr blk_size fst snd] in SBD. yhide SBD.
      rz_seg HKS HK0.
      step. carve_frame 48%nat STK. step. step. step. step. step.
      step. if_cases K1; zify_cond K1. 1:{ kill K1. }
      step. step. rewrite ysx32_small by (clear; lia).
      step. if_cases K2; zify_cond K2. 1:{ kill K2. }
      step. step. step.
      step. if_cases K3; zify_cond K3. 1:{ kill K3. }
      step. if_cases K4; zify_cond K4.
      * (* [comment removed for export] *)
        assert (NPOS : 0 < nz) by (revert K4; unfold nz, zlength; rewrite ?unsigned_lit by lia; clear; lia). clear K1 K2 K3 K4.
        destruct (SFACTS NPOS) as [SSF SSB].
        apply evt_done. yshow SBH. yreveal YAF MU WM. yhide SBH. yreveal TB MU WM. yshow SBD. yreveal DC MU WM. yhide SBD. yshow BR4. yreveal ERR MU WM. yhide BR4.
        destruct (OWN _ MU WM) as [[HK1 AX1] YS1].
        lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
        lazymatch goal with H : rw_cells _ m1 (mb_addr mb) _ |- _ => rename H into BC1 end.
        lazymatch goal with H : rw_cells _ m1 (bv_unsigned sp + -48) _ |- _ => rename H into FR1 end.
        rename ERR into ERR1.
        lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
        lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
        eapply (J_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 mo s [] (take 8 (take 16 (take 24 (take 32 (take 40 junk))))) junk0 errv
                  (yb_len b) (yb_used b) d0 (mb_did mb) (mb_data mb));
          [ cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app]; unfold buf_blocks in HK1; rewrite HD in HK1; exact HK1
          | exact YS1 | exact FR1 | exact STK1 | exact MI1 | exact AX1 | exact ERR1 | apply PRESW; assumption
          | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]; unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz; exact YAF
          | exact BC1 | exact DC | exact TB | exact I1 | exact I2 | exact I5 | clear -RL; lia | exact NPOS | exact N30 | reflexivity | ].
        intros bf HL. eapply app_leaf_inl; [exact HS| | exact HL]. unfold ens_first. rewrite HD. destruct b; cbn in *; subst; apply yl_ret.
      * (* [comment removed for export] *)
        assert (NZ : nz = 0) by (revert K4; unfold nz, zlength; rewrite ?unsigned_lit by lia; clear; lia). clear K1 K2 K3 K4.
        step. apply evt_done. yshow SBH. yreveal YAF MU WM. yhide SBH. yshow SBD. yreveal DC MU WM. yhide SBD. yshow BR4. yreveal ERR MU WM. yhide BR4.
        destruct (OWN _ MU WM) as [[HK1 AX1] YS1].
        eapply (J_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mo s b mb []);
         [ change ([] ++ REST) with REST; exact HK1 | exact YS1 | eassumption | eassumption | eassumption | exact AX1 | eassumption
         | apply PRESW; assumption
         | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]; unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz; exact YAF
         | | split; [split; [unfold buf_cells; rewrite HS; cbn [buf_state_code]; unfold wz; eassumption| split; [rewrite HD; exact DZ| lia]]| split; [unfold buf_data; rewrite HD; split; [split; [exact I1| exact I5]| exists junk0; exact DC]| exact FB]]
         | split; reflexivity | reflexivity ].
        eapply app_leaf_inl; [exact HS| unfold ens_first; rewrite HD; apply yl_ret|].
        apply (yleaf_bind _ _ b); [unfold ens_tail; fold nz; rewrite NZ; cbn; apply yl_ret|].
        unfold app_tail. rewrite HS. fold nz. rewrite NZ. cbn. apply yl_ret.
    + (* [comment removed for export] *)
      destruct (I4 eq_refl) as [L0 U00]. assert (D00 : mb_data mb = 0) by (apply DZ; reflexivity).
      assert (BY0 : yb_bytes b = []) by (destruct (yb_bytes b); [reflexivity| unfold zlength in I2; cbn in I2; lia]).
      clear BD. unfold buf_blocks in HK0, ND, OWN, HBI'. rewrite HD in HK0, ND, OWN, HBI'. cbn [app] in HK0, ND, OWN, HBI'.
      yshow SEPB. clear SEPB. destruct (HK_blocks HK HKB _ _ _ _ HK0) as [_ SEPX]. cbn [all_sep] in SEPX. destruct SEPX as [SEPB _]. yhide SEPB.
      rz_seg HKS HK0.
      step. carve_frame 48%nat STK. step. step. step. step. step.
      step. if_cases K1; zify_cond K1. 1:{ kill K1. }
      step. step. rewrite ysx32_small by (clear; lia).
      step. if_cases K2; zify_cond K2. 1:{ kill K2. }
      step. step. step.
      step. if_cases K3; zify_cond K3. 2:{ kill K3. }
      clear K1 K2 K3.
      pose proof YAF as YAFw. yshow SBH. yreveal YAFw MU WM. yhide SBH. step. step. step. clear YAFw. step. step. step. step.
      apply evt_done.
      yshow SBH. yreveal YAF MU WM. yhide SBH. yshow BR4. yreveal ERR MU WM. yhide BR4.
      (* [comment removed for export] *)
      destruct (OWN _ MU WM) as [[HK1 AX1] YS1].
      lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m1 end.
      lazymatch goal with H : rw_cells _ m1 (mb_addr mb) _ |- _ => rename H into BC1 end.
      lazymatch goal with H : rw_cells _ m1 (bv_unsigned sp + -48) _ |- _ => rename H into FR1 end.
      rename ERR into ERR1.
      lazymatch goal with H : mem_inv _ m1 |- _ => rename H into MI1 end.
      lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
      pose proof (PRESW _ MU WM) as PRES1.
      eapply YWM; [exact K0 | exact HK1 | exact AX1 | rewrite ESP; clear -SPB; lia | rewrite ESP; exact STK1 | exact CEIL
                  | rewrite ESP; unfold RY_WRAP_STACK; clear -LO'; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR1
                  | exact MI1 | exact TP | reflexivity | unfold NUSERc; clear; lia | eapply (yroom_lt _ 1); [apply yroom_cons; eapply yroom_le; [exact YR| clear; lia]| clear; lia] | ].
      cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' errv2 pn Dn MI2 STK2 ERR2 AX2 HP A0' RNB HK2 NEW0.
      replace (ret_pc (Z_to_bv 64 86264)) with (Z_to_bv 64 86264) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
      pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2.
      pose proof (ypres_frame _ _ _ _ _ _ HP FR1 ltac:(clear; lia)) as FR2. clear FR1.
      pose proof (ypres_block _ _ _ _ _ _ HP YAF ltac:(exists hb; split; [exact HBI'| cbn; clear -HB1 HB2; lia])) as YAF2. clear YAF.
      pose proof (ypres_block _ _ _ _ _ _ HP BC1 ltac:(eexists; split; [left; reflexivity| cbn [blk_addr blk_size fst snd cells_size csize Nat.add]; unfold SIZEOF_BUF; clear; lia])) as BC2. clear BC1.
      yshow TB.
      assert (TB2 : bytes_at rsegs m2 SA (zbytes src)).
      { eapply (bytes_at_transport' _ m) in TB; [| exact MU|].
        2:{ intros LP. rewrite ZL in LP. destruct (SFACTS ltac:(rewrite NZE; clear -LP; lia)) as [SSF SSB]. cbv [disjoint_from fst snd]. rewrite ZL. clear -SSF SSB NZE. lia. }
        eapply (src_pres REST sp SA src _ m1 m2 YSR HP); [intros bt Hbt; right; exact Hbt| exact MI1| exact MI2| exact TB]. }
      clear TB.
      assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
      { eapply ry_pres_trans; [exact PRES1|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP| clear; lia| intros b0 Hb0; right; exact Hb0]. }
      clear HP MU WM MI1 AX1 ERR1 STK1 HK1 YS1.
      * (* [comment removed for export] *)
        destruct NEW0 as [junkn NEW]. subst a0'. unfold rblock_range, alloc_ceiling in RNB. destruct RNB as (RN0 & _ & _ & RN3 & RN4). yhide RN4.
        unfold wz.
        assert (HK2' : HK s2' ((mb_id mb, mb_addr mb, 32) :: (pn, Dn, 2048) :: REST) m2 mo2).
        { eapply HKP; [exact HK2|]. apply Permutation.perm_swap. }
        clear HK2.
        assert (UDn : bv_unsigned (Z_to_bv 64 Dn) = Dn) by (apply unsigned_lit; clear -RN0 RN3 CEIL' LO' SPR; lia).
        destruct (HK_blocks HK HKB _ _ _ _ HK2') as [_ SEP2]. cbn [all_sep sep_from app] in SEP2.
        destruct SEP2 as ((SBD2 & _) & SEPN & _). unfold bsep in SBD2. cbn [blk_addr blk_size fst snd] in SBD2. yhide SBD2.
        pose proof (sep_from_In _ _ _ SEPN HBI) as SDH. unfold bsep in SDH. cbn [blk_addr blk_size fst snd] in SDH. yhide SDH.
        (* [comment removed for export] *)
        assert (SFN : 0 < nz -> SA + nz <= Dn \/ Dn + 2048 <= SA).
        { intros NP. destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[Y3|Y4]]]; [| yshow RN4; clear -Y2 RN4; lia| clear -Y3 LO' RN3 CEIL'; lia| exfalso; clear -NP Y4; lia].
          pose proof (sep_from_In _ _ _ SEPN HBT) as X. clear -X T1 T2. unfold bsep, blk_addr, blk_size in *. cbn [fst snd] in *. lia. }
        pose proof (munch_refl [(mb_addr mb, mb_addr mb + 32); (Dn, Dn + 2048)] m2) as MU. pose proof (wmono_refl rsegs m2) as WM.
        yhide FR2. yhide YAF2. yhide ERR2. yhide TB2.
        rz_seg HKS HK2'.
        yshow SBD2. step. yhide SBD2.
        step. if_cases K5; zify_cond K5. 1:{ kill K5. } clear K5.
        (* [comment removed for export] *)
        lazymatch goal with H : rw_cells _ _ Dn _ |- _ => rename H into NEW1 end.
        match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
          pose proof (rw_cells_CB_store_ok rsegs mx Dn _ _ 1%nat NEW1 ltac:(clear; lia)) as SOK end.
        step.
        match type of NEW1 with rw_cells _ ?mx _ _ =>
          pose proof (rw_cells_CB_prefix_write rsegs mx Dn _ _ (le1 (Z_to_bv 64 0)) NEW1 ltac:(cbn; clear; lia)) as DCN end.
        clear NEW1. yshow SBD2. store_done. yhide SBD2.
        (* [comment removed for export] *)
        lazymatch type of DCN with rw_cells _ ?mx _ _ =>
          assert (DC3 : rw_cells rsegs mx Dn [CB (Z.to_nat (yb_used b)) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (2048 - yb_used b - 1)) (drop 1 junkn)]) end.
        { rewrite U00, BY0. revert DCN. rewrite !length_le1. replace (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0] by reflexivity. intros DCN.
          pose proof (proj1 (proj1 DCN)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LJn & _).
          eapply rw_cells_recast; [exact DCN| | |].
          - cbn [cells_wf cell_wf zbytes map length]. split; [reflexivity|]. split; [exact I|]. split; [| exact I]. rewrite LJn. clear; lia.
          - cbn [cells_bytes cbytes zbytes map app]. reflexivity.
          - cbn [cells_size csize]. clear; lia. }
        clear DCN.
        step. if_cases K6; zify_cond K6.
        -- (* [comment removed for export] *)
          apply evt_done.
          yreveal FR2 MU WM. yshow SBH. yshow SDH. yreveal YAF2 MU WM. yhide SBH. yhide SDH. yshow BR4. yshow RN4. yreveal ERR2 MU WM. yhide BR4. yhide RN4.
          lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m4 end.
          lazymatch goal with H : rw_cells _ m4 (mb_addr mb) _ |- _ => rename H into BC4 end.
          lazymatch goal with H : rw_cells _ m4 Dn _ |- _ => rename H into DC4 end.
          lazymatch goal with H : mem_inv _ m4 |- _ => rename H into MI4 end.
          lazymatch goal with H : stk _ m4 _ _ |- _ => rename H into STK4 end.
          destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2' AX2 MU WM) as [HK3 AX3].
          { apply Forall_cons; [right; right; eexists; split; [left; reflexivity| cbn [fst snd blk_addr blk_size]; clear; lia]|].
            apply Forall_cons; [right; right; eexists; split; [right; left; reflexivity| cbn [fst snd blk_addr blk_size]; clear; lia]| apply Forall_nil]. }
          { apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; yshow BR4; clear -BR4 BR3 CEIL' LO' SPB; lia|].
            apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; yshow RN4; clear -RN3 RN4 CEIL' LO' SPB; lia| apply Forall_nil]. }
          yshow BR4. yshow RN4.
          pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -BR4; lia| apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -RN4; lia| apply Forall_nil]])) as YS3.
          yhide BR4. yhide RN4.
          assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m4).
          { eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
            yshow SEPB. yshow BR4. yshow RN4.
            intros a Ha Hc _. cbn. split; [| split; [| exact I]].
            - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' BR3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc BR4; lia|].
              pose proof (sep_from_In _ _ _ SEPB Hb) as Hs. clear -Hs Hr. unfold bsep, blk_addr, blk_size, SIZEOF_BUF in *. cbn [fst snd] in *. lia.
            - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' RN3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc RN4; lia|].
              pose proof (sep_from_In _ _ _ SEPN Hb) as Hs. clear -Hs Hr. unfold bsep, blk_addr, blk_size in *. cbn [fst snd] in *. lia. }
          eapply (J_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mo2 s2' (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b)) (mkMB (mb_id mb) (mb_addr mb) pn Dn) []);
           [ cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app]; exact HK3 | exact YS3 | exact FR2 | exact STK4 | exact MI4 | exact AX3 | exact ERR2
           | exact PRES3
           | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]; unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz; exact YAF2
           | | | split; reflexivity | reflexivity ].
          ++ eapply app_leaf_inl; [exact HS| unfold ens_first; rewrite HD; apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc| apply yl_ret]|].
             apply (yleaf_bind _ _ (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b))); [unfold ens_tail; fold nz; rewrite K6; cbn; apply yl_ret|].
             unfold app_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes]. fold nz. rewrite K6. cbn. apply yl_ret.
          ++ split; [split; [unfold buf_cells; cbn [buf_state_code yb_state yb_len yb_used mb_addr mb_data]; unfold wz; exact BC4
                            | split; [cbn [yb_data mb_data]; split; [discriminate| intros E; exfalso; clear -E RN0; lia]| cbn [yb_len yb_used]; clear -I1 U00; lia]]
                    | split; [unfold buf_data; cbn [yb_data yb_used yb_len yb_bytes mb_data]; split; [clear -I1 U00; lia| eexists; exact DC4]| cbn [yb_bytes]; exact FB]].
        -- (* [comment removed for export] *)
          assert (NPOS : 0 < nz) by (clear -K6 NZ0; lia).
          apply evt_done.
          yreveal FR2 MU WM. yshow SBH. yshow SDH. yreveal YAF2 MU WM. yhide SBH. yhide SDH. yshow BR4. yshow RN4. yreveal ERR2 MU WM. yhide BR4. yhide RN4.
          yshow TB2. eapply (bytes_at_transport' _ m2) in TB2; [| exact MU|].
          2:{ intros LP. destruct (SFACTS NPOS) as [_ SSB]. pose proof (SFN NPOS) as SSN. cbv [disjoint_from fst snd]. rewrite ZL, <- NZE. clear -SSB SSN. lia. }
          lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m4 end.
          lazymatch goal with H : rw_cells _ m4 (mb_addr mb) _ |- _ => rename H into BC4 end.
          lazymatch goal with H : rw_cells _ m4 Dn _ |- _ => rename H into DC4 end.
          lazymatch goal with H : mem_inv _ m4 |- _ => rename H into MI4 end.
          lazymatch goal with H : stk _ m4 _ _ |- _ => rename H into STK4 end.
          destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2' AX2 MU WM) as [HK3 AX3].
          { apply Forall_cons; [right; right; eexists; split; [left; reflexivity| cbn [fst snd blk_addr blk_size]; clear; lia]|].
            apply Forall_cons; [right; right; eexists; split; [right; left; reflexivity| cbn [fst snd blk_addr blk_size]; clear; lia]| apply Forall_nil]. }
          { apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; yshow BR4; clear -BR4 BR3 CEIL' LO' SPB; lia|].
            apply Forall_cons; [cbn [fst snd]; unfold RAUXV_CELL; yshow RN4; clear -RN3 RN4 CEIL' LO' SPB; lia| apply Forall_nil]. }
          yshow BR4. yshow RN4.
          pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -BR4; lia| apply Forall_cons; [cbn [fst snd]; unfold RY_CALLBACKS; clear -RN4; lia| apply Forall_nil]])) as YS3.
          yhide BR4. yhide RN4.
          assert (PRES3 : ry_pres REST (bv_unsigned sp) [] m m4).
          { eapply ry_pres_trans; [exact PRES2|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
            yshow SEPB. yshow BR4. yshow RN4.
            intros a Ha Hc _. cbn. split; [| split; [| exact I]].
            - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' BR3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc BR4; lia|].
              pose proof (sep_from_In _ _ _ SEPB Hb) as Hs. clear -Hs Hr. unfold bsep, blk_addr, blk_size, SIZEOF_BUF in *. cbn [fst snd] in *. lia.
            - destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [clear -Hc LO' CEIL' RN3; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc RN4; lia|].
              pose proof (sep_from_In _ _ _ SEPN Hb) as Hs. clear -Hs Hr. unfold bsep, blk_addr, blk_size in *. cbn [fst snd] in *. lia. }
          eapply (J_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 mo2 s2' [] (take 8 (take 16 (take 24 (take 32 (take 40 junk))))) (drop 1 junkn) errv2
                    2048 (yb_used b) 0%nat pn Dn);
            [ cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app]; exact HK3
            | exact YS3 | exact FR2 | exact STK4 | exact MI4 | exact AX3 | exact ERR2 | exact PRES3
            | unfold alloc_cells; cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]; unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz; exact YAF2
            | exact BC4 | exact DC4 | exact TB2 | exact I1 | exact I2 | clear -U00; lia | clear; lia | exact NPOS | exact N30 | reflexivity | ].
          intros bf HL. eapply app_leaf_inl; [exact HS| | exact HL]. unfold ens_first. rewrite HD.
          apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc| apply yl_ret].
Qed.
End S.
End RC__1.
