(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib RY_buf_append2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_region_is_poisoned AI_asan_memcpy1 AI_asan_memcpy AYajlRep AYajl_iface AY_rz AY_buf_append1 AY_buf_append2 AY_buf_append2g AY_buf_append3 AY_buf_append3g AY_buf_append4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma asrc_pres : forall Y (REST : list ablock) (LF : list fblock) (SP S : Z) (src : list Z) s (LBx : list ablock) m0 mo m1 m2,
  AHK_y_layout_stmt Y -> y_AHK Y s LBx LF m0 mo ->
  ysrc_range REST LF S (zlength src) -> ay_pres REST LF SP [] m1 m2 ->
  mem_inv asegs m1 -> mem_inv asegs m2 -> bytes_at asegs m1 S (zbytes src) -> bytes_at asegs m2 S (zbytes src).
Proof. aceil.
  intros Y REST LF SP S src s LBx m0 mo m1 m2 LAYY AHK YSR HP MI1 MI2 TB. pose proof (zbytes_length src) as ZL.
  destruct YSR as [(bt & HBT & T1 & T2)|[R2|[(f & Hf & F1 & F2)|R4]]].
  - eapply aypres_block_bytes; [exact HP| exact TB|]. exists bt. split; [exact HBT|]. rewrite ZL. unfold zlength in *. lia.
  - eapply arodata_bytes_persist; [exact TB| exact MI1| exact MI2| lia|]. rewrite ZL. unfold zlength in *. lia.
  - eapply aypres_bytes; [exact HP| exact TB|]. intros a Ha. split; [| intros F0; exact F0]. right; right; left.
    exists f. split; [exact Hf|]. left. rewrite ZL in Ha. unfold zlength in *. lia.
  - destruct src; [| unfold zlength in R4; cbn in R4; lia]. destruct TB as (B0 & B1 & _).
    split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. lia.
Qed.

(* [comment removed for export] *)
Lemma yleaf_ymalloc : forall n r, yleaf (ymalloc n) r.
Proof. aceil. intros. unfold ymalloc. apply (yl_malloc _ _ r). apply yl_ret. Qed.
Lemma yleaf_yrealloc : forall p n r, yleaf (yrealloc p n) r.
Proof. aceil. intros. unfold yrealloc. apply (yl_realloc _ _ _ r). apply yl_ret. Qed.
Lemma yleaf_yfree : forall p, yleaf (yfree p) tt.
Proof. aceil. intros. unfold yfree. apply yl_free. apply yl_ret. Qed.

Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis WFREEN : aywrap_free_null_stmt Y.
Hypothesis WREA : aywrap_realloc_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_rea : In 0x86ba4 URA.
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals asegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
(* [comment removed for export] *)
Hypothesis YPHI_shape : forall st len u1 u2 d bs1 bs2, y_phi_buf Y (mkBuf st len u1 d bs1) = y_phi_buf Y (mkBuf st len u2 d bs2).
Hypothesis YPHI_grow : forall len used want (d : yptr) bs,
    0 <= used < len -> len < 2^31 -> 0 < want -> used + want < 2^28 -> ens_need_loop ENS_FUEL want len used <> len ->
    y_acharge Y (ens_need_loop ENS_FUEL want len used) + y_free_cost Y + y_phi_buf Y (mkBuf BS_ok (ens_need_loop ENS_FUEL want len used) used (Some d) bs)
      <= y_phi_buf Y (mkBuf BS_ok len used (Some d) bs).
Hypothesis YPHI_err : forall len u (d : yptr) bs, y_phi_buf Y (mkBuf BS_overflow 0 0 None []) <= y_phi_buf Y (mkBuf BS_ok len u (Some d) bs).

Section Fn.
Variables (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : mem) (mo' : Model) (s' : y_APS Y) (b' : ybuf) (mb' : mbuf) (LK : list ablock),
  aybuf_append_rpost Y sp m mo s LF REST mb b AF S src lo RR a0' fc' m' mo' s' b' mb' LK ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis RR0 : 0 <= RR.
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AY_BUF_APPEND_STACK.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis TP : tp = wz (c_tp ACONSTS).
Hypothesis HBIN : exists hb, In hb REST /\ ab_addr hb <= AF /\ AF + 32 <= ab_addr hb + 8 * (ab_size hb / 8) /\ AF mod 8 = 0 /\ oshw_hi 0 (2^47) <= ab_addr hb.   (* [comment removed for export] *)
Hypothesis NBIG : nbig REST <= AY_NBIG_REST + 3.
Let n := zlength src.
Hypothesis SRCF : Forall (fun c => 0 <= c < 256) src.
Hypothesis SNZ : 0 < n -> S <> 0.
Hypothesis YSR : ysrc_range REST LF S n.
Hypothesis YWIN : ysrc_win Y REST LF (bv_unsigned sp) m S n.
Hypothesis FB : Forall (fun c => 0 <= c < 256) (yb_bytes b).

Lemma HBIN_weak : exists hb, In hb REST /\ ab_addr hb <= AF /\ AF + 32 <= ab_addr hb + ab_size hb /\ oshw_hi 0 (2^47) <= ab_addr hb.
Proof. aceil. destruct HBIN as (hb & H1 & H2 & H3 & H4 & H5). exists hb. split; [exact H1|]. split; [exact H2|]. split; [clear -CEILB H3; Z.div_mod_to_equations; lia| exact H5]. Qed.


(* [comment removed for export] *)
Lemma aapp_size : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2v s5v s6v s7v s10v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (junkf junk : list byte)
    (len1 used1 : Z) (d1 : yptr) (did1 : bptr) (D1 : Z) (sh9 sh11 : Z),
  let b1 := mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b) in
  let mb1 := mkMB (mb_id mb) (mb_addr mb) did1 D1 in
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ REST) LF m1 mo1 -> aystatics m1 ->
  aapp_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 junkf -> stk asegs m1 lo (bv_unsigned sp + -128) -> mem_inv asegs m1 -> frm0 fc1 ->
  True -> ay_pres REST LF (bv_unsigned sp) [] m m1 ->   (* [comment removed for export] *)
  rw_cells asegs m1 AF (alloc_cells ayc) ->
  rw_cells asegs m1 (mb_addr mb) [C4 (wz 0); C4 (wz len1); C4 (wz used1); C4 (wz 0); C8 (wz D1); C8 (wz AF)] ->
  rw_cells asegs m1 D1 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (len1 - used1 - 1)) junk] ->
  bytes_at asegs m1 S (zbytes src) ->
  y_SO Y s1' = y_SO Y s -> y_ayR Y s mo s1' mo1 -> y_phi_buf Y b1 + RR <= y_acredit Y s1' ->
  0 <= used1 -> used1 = zlength (yb_bytes b) -> used1 < len1 -> len1 < 2^31 -> 0 < n -> used1 + n < 2^26 ->
  (forall bf, yleaf (b2 <- ens_tail n b1 ;; app_tail src b2) bf -> yleaf (ybuf_append b src) bf) ->
  sh9 = A_SB + (mb_addr mb + 16) / 8 -> sh11 = A_SB + mb_addr mb / 8 -> yb_state b = BS_ok ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz (mb_addr mb + 16)) (wz (mb_addr mb)) a0 a1 a2 a3 a4 a5 a6 a7
                                   s2v (wz n) (wz S) s5v s6v s7v (wz A_SB) (wz sh9) s10v (wz sh11) t3 t4 t5 t6)
                          F1 (wz AAPP_SIZE) fc1 None m1 (seg_rom asegs)) mo1) K.
Proof. aceil.
  intros until sh11. cbv zeta. intros AHK1 YS1 FR ST MI FRM WM0 PRES YAF BC DC TB SO1 R1 CRED U0 UB UL L31 NPOS N30 HL E9 E11 BOK.
  pose proof (aapp_copy Y KIPY FRAMEY BLKY BSHY BSMALL LAYY RRT ICPG ICPB ICPR LF REST mb b AF S src lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s
                CONT CEIL LO SPH SRCF SNZ YSR YWIN HBIN_weak FB) as J_copy.
  cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app] in AHK1.
  unfold aapp_frame, A_SB, SIZEOF_BUF, wz in *. pose proof LO as LO'. unfold AY_BUF_APPEND_STACK, AMALLOC_STACK in LO'.
  pose proof CEIL as CEIL'. aceil.
  destruct HBIN as (hb & HBI & HB1 & HB2 & AF8 & HBHI).
  assert (HBIN' : In hb ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: REST)) by (right; right; exact HBI).
  destruct (BLKY _ _ _ _ _ AHK1) as (RNG & SEP & ND).
  pose proof (RNG _ (or_introl eq_refl)) as BR. pose proof (RNG _ (or_intror (or_introl eq_refl))) as DR. pose proof (RNG _ HBIN') as HBR.
  unfold ablock_range, ACONSTS in BR, DR, HBR. cbn [c_img_hi ab_addr ab_size] in BR, DR, HBR. aceil.
  pose proof (SEP _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND (or_introl eq_refl))) as SBD. cbn [ab_addr ab_size] in SBD.
  pose proof (SEP _ _ (or_introl eq_refl) HBIN' (nd_head_ne _ _ _ ND (or_intror HBI))) as SBH. cbn [ab_addr ab_size] in SBH.
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK1 (or_introl eq_refl) ltac:(cbn; lia))) as BSH. pose proof (BSMALL _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK1 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as BSHI.
  pose proof (proj1 (BSHY _ _ _ _ _ hb AHK1 HBIN' ltac:(lia))) as HBS. pose proof HBHI as HBSI.
  cbn [ab_addr ab_size] in BSH, BSHI. unfold oshw_hi, A_SB, amem in BSHI, HBSI.
  assert (BSH2 : 17594333495296 <= mb_addr mb) by (revert BSHI CEILB; clear; intros H CEILB; cbn in H; lia). clear BSHI.
  assert (HBS2 : 17594333495296 <= ab_addr hb) by (revert HBSI CEILB; clear; intros H CEILB; cbn in H; lia). clear HBSI.
  destruct BSH as (B8 & _ & BSHu). destruct HBS as (HB8 & HBn & HBSu). unfold A_SB in BSHu, HBSu.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold wz in YAF.
  pose proof (zbytes_length src) as ZL. pose proof (zbytes_length (yb_bytes b)) as ZLB.
  pose proof (ens_need_loop_bounds (zlength src) len1 used1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as NB. cbv zeta in NB.
  unfold n in *. set (r := ens_need_loop ENS_FUEL (zlength src) len1 used1) in *.
  destruct (proj1 (proj1 DC)) as (LZB & _ & LJ & _). cbn [cell_wf] in LZB, LJ.
  (* [comment removed for export] *)
  destruct (proj1 (ycells_app asegs m1 (bv_unsigned sp + -128) [CB 24 junkf] _) FR) as [FRL FRH]. cbn [cells_size csize Nat.add] in FRH.
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PB PBS].
  pose proof (aypol_opol_sub Y _ LF _ _ LINK hb AF 32 HBIN' HB1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [PHB _].
  pose proof (aypol_opol_block Y _ LF _ _ LINK hb HBIN' ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [_ PHBS].
  cbn [ab_addr ab_size] in PB, PBS. unfold oshw_lo, oshw_hi, A_SB, amem in PB, PBS, PHB, PHBS.
  eapply evtA_cut.
  { eapply (asizeA_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mb_addr mb) D1 S (zlength src) AF len1 used1 lo (bv_unsigned sp + -128) sh9 sh11 junkf _ _ (ab_addr hb) (ab_size hb));
      [ exact MI | lia | lia | lia | exact BC | exact BSHu | reflexivity | exact FRL | exact YAF | exact HBSu | reflexivity
      | lia | lia | exact AF8 | lia | lia | lia | lia | clear -CEILB SBH; lia | lia | lia | lia | lia
      | lia | lia | lia | lia | lia | lia
      | eapply pol_sub; [exact PSTK| lia| lia] | exact PB | exact PBS | exact PHB | exact PHBS ]. }
  cbv beta. fold r. intros ms2 [(RL & a2s & a3s & ->)|(RNE & m2 & -> & MU & WM & MI2 & FRL2)].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2.
    destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2].
    eapply (J_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc1 m1 mo2 s1' [] junkf junk len1 used1 d1 did1 D1 sh9 ((mb_addr mb + 8) / 8 + 2147450880)).
    + cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app]. exact AHK2.
    + exact YS1.
    + exact FR.
    + exact ST.
    + exact MI.
    + exact FRM.
    + exact WM0.
    + exact PRES.
    + unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF.
    + exact BC.
    + exact DC.
    + exact TB.
    + exact SO1.
    + eapply RRT; [exact R1| exact R2].
    + rewrite (YPHI_shape BS_ok len1 (used1 + zlength src) used1 (Some d1) (yb_bytes b ++ src) (yb_bytes b)). exact CRED.
    + exact U0.
    + exact UB.
    + clear -CEILB NB RL NPOS; lia.
    + exact L31.
    + exact NPOS.
    + apply HL. apply (yleaf_bind _ _ (mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b))).
      * unfold ens_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
        replace (zlength src =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold r.
        replace ((r <? used1) || (r =? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.eqb_neq]; clear -CEILB NB U0 NPOS; lia).
        replace (negb (r =? len1)) with false by (symmetry; rewrite RL, Z.eqb_refl; reflexivity).
        apply yl_ret.
      * unfold app_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
        replace (0 <? zlength src) with true by (symmetry; apply Z.ltb_lt; lia). apply yl_ret.
    + unfold A_SB. lia.
    + unfold A_SB. lia.
    + reflexivity.
  - (* [comment removed for export] *)
    apply evtA_done. intros mo2 Hag2 HLI2 Hh2.
    eapply (rw_cells_transport asegs) in FRH; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
    eapply (rw_cells_transport asegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
    eapply (rw_cells_transport asegs) in BC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
    eapply (rw_cells_transport asegs) in DC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
    eapply (stk_transport_disjoint asegs) in ST; [| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
    assert (TB2 : bytes_at asegs m2 S (zbytes src)).
    { eapply (bytes_at_transport asegs); [exact TB| exact MU|]. cbv [disjoint_from fst snd]. rewrite ZL.
      destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & F1' & F2)|Y4]]]; [| unfold zlength in *; lia| | unfold zlength in *; lia].
      - pose proof (RNG bt (or_intror (or_intror HBT))) as TR. unfold ablock_range in TR. unfold zlength in *. lia.
      - destruct (proj1 (LAYY _ _ _ _ _ AHK1) f Hf) as (Lf1 & Lf2 & _). unfold zlength in *. lia. }
    clear TB FRL BSHu HBSu.
    destruct (BACK mo2 Hag2 HLI2) as [AHK2m R2].
    assert (AHK2 : y_AHK Y s1' ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: REST) LF m2 mo2).
    { eapply FRAMEY; [exact AHK2m| exact MU| exact WM|]. constructor; [left; cbn; aceil; lia| constructor]. }
    clear AHK2m.
    pose proof (aystatics_munch _ _ _ YS1 MU WM ltac:(constructor; [cbn; lia| constructor])) as YS2.
    assert (PRES2 : ay_pres REST LF (bv_unsigned sp) [] m m2).
    { eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
      intros a Ha Hc _. eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp));
        [exact AHK1| intros b0 Hb0; right; right; exact Hb0| aceil; lia| lia| exact Hc]. }
    pose proof (rw_cells_bytes_at _ _ _ _ DC) as OLD. cbn [cells_bytes cbytes] in OLD. rewrite app_nil_r in OLD.
    clear PRES LINK BACK PSTK PB PBS PHB PHBS MU. rename WM into WMA.
    (* [comment removed for export] *)
    name_sp sp (-128)%Z. rewrite <- Hsp in ST.
    eapply (WREA D1 len1 r _ _ LF lo (y_phi_buf Y (mkBuf BS_ok r used1 (Some d1) (yb_bytes b)) + RR));
      [ exact K0
      | apply AYST_split; split; [exact AHK2| exact YS2]
      | right; left; reflexivity
      | exact OLD
      | rewrite !length_app, LZB, LJ; cbn [length]; clear -CEILB U0 UL; lia
      | reflexivity
      | reflexivity
      | clear -CEILB NB N30 L31 U0 UL NPOS RNE; lia
      | let YG := fresh in pose proof (YPHI_grow len1 used1 (zlength src) d1 (yb_bytes b) ltac:(lia) L31 NPOS ltac:(clear -CEILB N30; lia) RNE) as YG; fold r in YG; lia
      | destruct NONNEG as (_ & NB0 & _); pose proof (NB0 (mkBuf BS_ok r used1 (Some d1) (yb_bytes b))); lia
      | pose proof (nbig_cons_le {| ab_addr := mb_addr mb; ab_size := 32 |} ({| ab_addr := D1; ab_size := len1 |} :: REST));
        pose proof (nbig_cons_le {| ab_addr := D1; ab_size := len1 |} REST); unfold AY_NBIG_REST in NBIG; lia
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [exact ST|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
        split; [exact MI2|]; split; [exact TP| exact FRM]
      | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold AAPP_REA_RET; rewrite unsigned_lit by lia; exact URA_rea]
      | ].
    cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 m3 mo3 s3' D2 (MI3 & ST3 & FRM3 & WM3 & PRES3) SO3 R3 CRED3 RES.
    unname_sp.
    assert (NE_BD : mb_addr mb <> D1) by (clear -CEILB SBD UL U0; lia).
    rewrite (ab_remove_skip _ _ _ _ NE_BD), ab_remove_head in PRES3, RES.
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRH ltac:(lia)) as FRH3. clear FRH.
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES3 FRL2 ltac:(lia)) as FRL3. clear FRL2.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES3 YAF ltac:(exists hb; split; [right; exact HBI| cbn; lia])) as YAF3. clear YAF.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES3 BC ltac:(eexists; split; [left; reflexivity| cbn; lia])) as BC3. clear BC.
    assert (PRES3w : ay_pres REST LF (bv_unsigned sp) [] m m3).
    { eapply ay_pres_trans; [exact PRES2|]. eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
    (* [comment removed for export] *)
    assert (FR3 : rw_cells asegs m3 (bv_unsigned sp + -128)
              [CB 24 (firstn 8 junkf ++ le8 (Z_to_bv 64 ((mb_addr mb + 24) / 8 + 2147450880)) ++ le8 (Z_to_bv 64 (mb_addr mb + 24)));
               C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (proj2 (ycells_app asegs m3 (bv_unsigned sp + -128) [CB 24 _] _)). cbn [cells_size csize Nat.add]. split; [| exact FRH3].
      eapply rw_cells_recast; [exact FRL3| | | reflexivity].
      - pose proof (proj1 (proj1 FRL3)) as WF. cbn [cells_wf cell_wf] in WF |- *. rewrite !length_app, !length_le8. intuition lia.
      - cbn [cells_bytes cbytes]. rewrite <- !app_assoc. reflexivity. }
    clear FRH3 FRL3.
    (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct RES as (EA0 & D2R & D2SH & _ & D2S & (junk2 & NEW) & AY3 & REF3). subst a0''. unfold wz. unfold AAPP_REA_RET.
      unfold ablock_range, ACONSTS in D2R. cbn [c_img_hi] in D2R. aceil.
      apply AYST_split in AY3. destruct AY3 as [AHK3 YS3].
      assert (AHK3' : y_AHK Y s3' ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D2; ab_size := r |} :: REST) LF m3 mo3).
      { eapply PERMY; [exact AHK3| apply Permutation.perm_swap| apply Permutation.Permutation_refl]. }
      clear AHK3.
      pose proof (BSHY _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK3' (or_introl eq_refl) ltac:(cbn; lia)) as [BSH3 _]. cbn [ab_addr ab_size] in BSH3.
      destruct BSH3 as (_ & _ & BSHu). unfold A_SB in BSHu.
      replace (Z.min r len1) with len1 in NEW by (clear -CEILB NB RNE; lia).
      (* [comment removed for export] *)
      arz_seg KIPY AHK3'. ret_pc_lit.
      pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PB PBS].
      cbn [ab_addr ab_size] in PB, PBS. unfold oshw_lo, oshw_hi, A_SB, amem in PB, PBS.
      eapply evtA_cut.
      { eapply (asizeB_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mb_addr mb) D1 D2 AF len1 used1 r (bv_unsigned sp + -128));
          [ exact MI3 | exact BC3 | exact BSHu | reflexivity | lia | lia | lia | lia | lia | clear -CEILB NB L31 N30 U0 UL; lia | lia | lia | lia | lia | exact PB | exact PBS ]. }
      cbv beta. intros ms4 (a0x & a1x & m4 & -> & MU & WM & MI4 & BC4).
      apply evtA_done. intros mo4 Hag4 HLI4 Hh4.
      eapply (rw_cells_transport asegs) in FR3; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
      eapply (rw_cells_transport asegs) in YAF3; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
      eapply (stk_transport_disjoint asegs) in ST3; [| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
      pose proof (proj1 (proj1 NEW)) as WF2. cbn [cells_wf cell_wf] in WF2. destruct WF2 as (_ & LJ2 & _).
      eapply (rw_cells_transport asegs) in NEW; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]].
      2:{ destruct (BLKY _ _ _ _ _ AHK3') as (_ & SEP3 & ND3).
          pose proof (SEP3 _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND3 (or_introl eq_refl))) as X. cbn [ab_addr ab_size] in X.
          clear -CEILB X NB U0 UL. lia. }
      assert (TB4 : bytes_at asegs m4 S (zbytes src)).
      { eapply (bytes_at_transport asegs); [| exact MU|].
        - eapply (asrc_pres Y REST LF (bv_unsigned sp + -128) S src); [exact LAYY| exact AHK2| exact YSR| | exact MI2| exact MI3| exact TB2].
          eapply (ay_pres_weaken Y); [exact PRES3| lia| intros b0 Hb0; right; exact Hb0| auto| auto].
        - cbv [disjoint_from fst snd]. rewrite ZL.
          destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & F1' & F2)|Y4]]]; [| unfold zlength in *; lia| | unfold zlength in *; lia].
          + pose proof (SEP bt _ (or_intror (or_intror HBT)) (or_introl eq_refl) ltac:(intros E; exact (nd_head_ne _ _ _ ND (or_intror HBT) (eq_sym E)))) as X.
            cbn [ab_addr ab_size] in X. unfold zlength in *. lia.
          + destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK1)) f _ Hf (or_introl eq_refl)) as [X _]. cbn [ab_addr ab_size] in X. unfold zlength in *. lia. }
      clear TB2.
      destruct (BACK mo4 Hag4 HLI4) as [AHK4m R4].
      assert (AHK4 : y_AHK Y s3' ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D2; ab_size := r |} :: REST) LF m4 mo4).
      { eapply FRAMEY; [exact AHK4m| exact MU| exact WM|]. constructor; [right; left; eexists; split; [left; reflexivity| cbn; lia]| constructor]. }
      clear AHK4m.
      pose proof (aystatics_munch _ _ _ YS3 MU WM ltac:(constructor; [cbn; lia| constructor])) as YS4.
      (* [comment removed for export] *)
      assert (DC4 : rw_cells asegs m4 D2 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (r - used1 - 1)) (junk ++ junk2)]).
      { eapply rw_cells_recast; [exact NEW| | |].
        - cbn [cells_wf cell_wf]. rewrite length_app, LJ, LJ2. clear -CEILB U0 UL NB LZB. repeat split; lia.
        - cbn [cells_bytes cbytes]. rewrite firstn_all2 by (rewrite !length_app, LZB, LJ; cbn [length]; clear -CEILB U0 UL; lia). rewrite <- !app_assoc. reflexivity.
        - cbn [cells_size csize]. clear -CEILB U0 UL NB. lia. }
      clear NEW.
      eapply (J_copy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F3 fc3 m4 mo4 s3' [] _ (junk ++ junk2) r used1 d1 did1 D2 sh9 ((mb_addr mb + 8) / 8 + 2147450880)).
      * cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app]. exact AHK4.
      * exact YS4.
      * exact FR3.
      * exact ST3.
      * exact MI4.
      * exact FRM3.
      * exact I.
      * eapply ay_pres_trans; [exact PRES3w|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
        intros a Ha Hc _. eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mb_addr mb) 32));
          [exact AHK3'| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
        intros b0 Hb0. split; [right; right; exact Hb0|]. cbn. intros E.
        destruct (BLKY _ _ _ _ _ AHK3') as (_ & _ & ND3). exact (nd_head_ne _ _ _ ND3 (or_intror Hb0) (eq_sym E)).
      * unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF3.
      * exact BC4.
      * exact DC4.
      * exact TB4.
      * rewrite SO3. exact SO1.
      * eapply RRT; [exact R1|]. eapply RRT; [exact R2|]. eapply RRT; [exact R3| exact R4].
      * rewrite (YPHI_shape BS_ok r (used1 + zlength src) used1 (Some d1) (yb_bytes b ++ src) (yb_bytes b)). exact CRED3.
      * exact U0.
      * exact UB.
      * clear -CEILB NB NPOS; lia.
      * clear -CEILB NB N30 L31 U0 UL; lia.
      * exact NPOS.
      * apply HL. apply (yleaf_bind _ _ (mkBuf BS_ok r used1 (Some d1) (yb_bytes b))).
        -- unfold ens_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
           replace (zlength src =? 0) with false by (symmetry; apply Z.eqb_neq; lia). fold r.
           replace ((r <? used1) || (r =? 0)) with false by (symmetry; apply orb_false_intro; [apply Z.ltb_ge| apply Z.eqb_neq]; clear -CEILB NB U0 NPOS; lia).
           replace (negb (r =? len1)) with true by (symmetry; rewrite (proj2 (Z.eqb_neq _ _) RNE); reflexivity).
           apply (yleaf_bind _ _ (Some d1)); [apply yleaf_yrealloc| apply yl_ret].
        -- unfold app_tail. cbn [yb_state yb_len yb_used yb_data yb_bytes].
           replace (0 <? zlength src) with true by (symmetry; apply Z.ltb_lt; lia). apply yl_ret.
      * unfold A_SB. lia.
      * unfold A_SB. lia.
      * reflexivity.
Qed.
End Fn.
End W.
End RC__1.
