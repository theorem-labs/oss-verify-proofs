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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_region_is_poisoned AI_asan_memcpy1 AI_asan_memcpy AYajlRep AYajl_iface AY_rz AY_buf_append1 AY_buf_append2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis MIY : AHK_y_mem_inv_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
(* [comment removed for export] *)
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals asegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).

Section Fn.
Variables (LF : list fblock) (REST : list ablock) (mb : mbuf) (b : ybuf) (AF S : Z) (src : list Z) (lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (mo : Model) (s : y_APS Y).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32)
    (m' : mem) (mo' : Model) (s' : y_APS Y) (b' : ybuf) (mb' : mbuf) (LK : list ablock),
  aybuf_append_rpost Y sp m mo s LF REST mb b AF S src lo RR a0' fc' m' mo' s' b' mb' LK ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                             F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AY_BUF_APPEND_STACK.
Hypothesis SPH : bv_unsigned sp <= 2^47.
Let n := zlength src.
Hypothesis SRCF : Forall (fun c => 0 <= c < 256) src.
Hypothesis SNZ : 0 < n -> S <> 0.
Hypothesis SBND : S + n <= 2^47.
Hypothesis YSR : ysrc_range REST LF S n.
Hypothesis YWIN : ysrc_win Y REST LF (bv_unsigned sp) m S n.
Hypothesis HBIN : exists hb, In hb REST /\ ab_addr hb <= AF /\ AF + 32 <= ab_addr hb + ab_size hb /\ oshw_hi 0 (2^47) <= ab_addr hb.   (* [comment removed for export] *)
Hypothesis FB : Forall (fun c => 0 <= c < 256) (yb_bytes b).

Let J_ret := aapp_ret Y KIPY FRAMEY RRT LF REST mb b AF S src lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s CONT CEIL LO SPH.

(* [comment removed for export] *)
Lemma aapp_copy : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5v s6v s7v s11v t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (LK : list ablock) (junkf junk : list byte)
    (len1 used1 : Z) (d1 : yptr) (did1 : bptr) (D1 : Z) (sh9 sh10 : Z),
  let b1 := mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b) in
  let b' := mkBuf BS_ok len1 (used1 + n) (Some d1) (yb_bytes b ++ src) in
  let mb1 := mkMB (mb_id mb) (mb_addr mb) did1 D1 in
  y_AHK Y s1' (abl (buf_blocks mb1 b1) ++ LK ++ REST) LF m1 mo1 -> aystatics m1 ->
  aapp_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 junkf -> stk asegs m1 lo (bv_unsigned sp + -128) -> mem_inv asegs m1 -> frm0 fc1 ->
  True -> ay_pres REST LF (bv_unsigned sp) [] m m1 ->   (* [comment removed for export] *)
  rw_cells asegs m1 AF (alloc_cells ayc) ->
  rw_cells asegs m1 (mb_addr mb) [C4 (wz 0); C4 (wz len1); C4 (wz used1); C4 (wz 0); C8 (wz D1); C8 (wz AF)] ->
  rw_cells asegs m1 D1 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (len1 - used1 - 1)) junk] ->
  bytes_at asegs m1 S (zbytes src) ->
  y_SO Y s1' = y_SO Y s -> y_ayR Y s mo s1' mo1 -> y_phi_buf Y b' + RR <= y_acredit Y s1' ->
  0 <= used1 -> used1 = zlength (yb_bytes b) -> used1 + n < len1 -> len1 < 2^31 -> 0 < n ->
  yleaf (ybuf_append b src) b' ->
  sh9 = A_SB + (mb_addr mb + 16) / 8 -> sh10 = A_SB + (mb_addr mb + 8) / 8 -> LK = [] ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz (mb_addr mb + 16)) (wz (mb_addr mb)) a0 a1 a2 a3 a4 a5 a6 a7
                                   (wz (mb_addr mb + 8)) (wz n) (wz S) s5v s6v s7v (wz A_SB) (wz sh9) (wz sh10) s11v t3 t4 t5 t6)
                          F1 (wz AAPP_COPY) fc1 None m1 (seg_rom asegs)) mo1) K.
Proof. aceil.
  intros until sh10. cbv zeta. intros AHK1 YS1 FR ST MI FRM WM0 PRES YAF BC DC TB SO1 R1 CRED U0 UB ROOM L31 NPOS HL E9 E10 LK0.
  cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app] in AHK1.
  unfold aapp_frame, A_SB, SIZEOF_BUF, wz in *. pose proof LO as LO'. unfold AY_BUF_APPEND_STACK, AMALLOC_STACK in LO'.
  pose proof CEIL as CEIL'. aceil.
  (* [comment removed for export] *)
  destruct (BLKY _ _ _ _ _ AHK1) as (RNG & SEP & ND).
  pose proof (RNG _ (or_introl eq_refl)) as BR. pose proof (RNG _ (or_intror (or_introl eq_refl))) as DR.
  unfold ablock_range, ACONSTS in BR, DR. cbn [c_img_hi ab_addr ab_size] in BR, DR. aceil.
  pose proof (SEP _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND (or_introl eq_refl))) as SBD. cbn [ab_addr ab_size] in SBD.
  (* [comment removed for export] *)
  pose proof (proj1 (BSHY _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK1 (or_introl eq_refl) ltac:(cbn; lia))) as BSH. pose proof (BSMALL _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK1 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as BSHI.
  pose proof (BSHY _ _ _ _ _ (mkABlock D1 len1) AHK1 (or_intror (or_introl eq_refl)) ltac:(cbn; lia)) as [DSH DSHI].
  cbn [ab_addr ab_size] in BSH, BSHI, DSH, DSHI. unfold oshw_hi, A_SB, amem in BSHI, DSHI.
  assert (BSH2 : 17594333495296 <= mb_addr mb) by (revert BSHI CEILB; clear; intros H CEILB; cbn in H; lia). clear BSHI.
  rename DSHI into DSH2.   (* [comment removed for export] *)
  pose proof DSH as DSH0. destruct BSH as (B8 & _ & BSHu). destruct DSH as (D8 & _ & DSHu). unfold A_SB in BSHu, DSHu.
  pose proof YS1 as (_ & _ & _ & STA). destruct STA as (G1 & G2 & G3 & G4). unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.
  pose proof (zbytes_length src) as ZL. pose proof (zbytes_length (yb_bytes b)) as ZLB.
  unfold n, zlength in *. set (nz := Z.of_nat (length src)) in *.
  (* [comment removed for export] *)
  assert (SFACTS : (S + nz <= alloc_ceiling \/ S + nz <= 0x31000)
                   /\ ((0 < S /\ S + nz < 2147450880) \/ (17594333495296 <= S))
                   /\ (S + nz <= D1 \/ D1 + len1 <= S) /\ (S + nz <= mb_addr mb \/ mb_addr mb + 32 <= S)).
  { destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & F1' & F2)|Y4]]]; [| clear -CEILB Y2 NPOS BR DR; lia| | lia].
    - assert (HBT' : In bt ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: LK ++ REST)) by (right; right; apply in_or_app; right; exact HBT).
      pose proof (RNG _ HBT') as TR. unfold ablock_range, ACONSTS in TR. cbn [c_img_hi] in TR. aceil.
      pose proof (BSHY _ _ _ _ _ _ AHK1 HBT' ltac:(lia)) as [_ TSI]. unfold oshw_hi, A_SB, amem in TSI.
      pose proof (SEP _ _ (or_introl eq_refl) HBT' (nd_head_ne _ _ _ ND (or_intror (in_or_app _ _ _ (or_intror HBT))))) as X1.
      pose proof (SEP _ _ (or_intror (or_introl eq_refl)) HBT' (nd_head_ne _ _ _ (nd_tail _ _ ND) (in_or_app _ _ _ (or_intror HBT)))) as X2.
      cbn [ab_addr ab_size] in X1, X2. clear -CEILB TR TSI X1 X2 T1 T2. lia.
    - destruct (proj1 (LAYY _ _ _ _ _ AHK1) f Hf) as (L1 & L2 & L3 & L4 & L5). unfold oshw_hi, A_SB, amem in L1, L2; aceil.
      destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK1)) f _ Hf (or_introl eq_refl)) as [X1 _].
      destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK1)) f _ Hf (or_intror (or_introl eq_refl))) as [X2 _].
      cbn [ab_addr ab_size] in X1, X2.
      clear -CEILB L2 L1 X1 X2 F1' F2. lia. }
  destruct SFACTS as (SLO & SRIM & SSEP & SSEPB).
  (* [comment removed for export] *)
  destruct (YWIN NPOS s1' (mkABlock (mb_addr mb) 32 :: mkABlock D1 len1 :: LK) m1 mo1 AHK1 PRES) as (wsS & SWS & RCS & PSHS). unfold A_SB in SWS, RCS, PSHS.
  destruct (ICPB _ _ _ _ _ (mkABlock D1 len1) (D1 + used1) nz AHK1 (or_intror (or_introl eq_refl)) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as (wsD & SWD & RCD & _ & _).
  pose proof (ICPR _ _ _ _ _ (mkABlock D1 len1) (D1 + used1) nz AHK1 (or_intror (or_introl eq_refl)) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia)) as PGD.
  pose proof (ICPG _ _ _ _ _ AHK1) as IG1. unfold A_SB in SWD, RCD, PGD, IG1.
  pose proof (shw_geom 2147450880 (D1 + used1) nz ltac:(lia) ltac:(lia) ltac:(lia)) as GEOD. cbv zeta in GEOD.
  (* [comment removed for export] *)
  destruct (proj1 (proj1 DC)) as (LZB & _ & LJ & _). cbn [cell_wf] in LZB, LJ.
  destruct (u8arr_of_CB3 _ _ _ _ _ _ _ _ DC) as (ARR & L1 & L2). clear DC.
  apply u8arr_app in ARR. destruct ARR as [ARR1 ARR23]. rewrite L1, Z2Nat.id in ARR23 by lia.
  rewrite <- (firstn_skipn (Z.to_nat nz) ([Z_to_bv 8 0] ++ junk)) in ARR23.
  apply u8arr_app in ARR23. destruct ARR23 as [ARR2 ARR3].
  rewrite length_firstn in ARR3. replace (Z.of_nat (Nat.min (Z.to_nat nz) (length ([Z_to_bv 8 0] ++ junk)))) with nz in ARR3 by (cbn [length app]; rewrite ?length_app; cbn [length]; lia).
  pose proof (CB_of_u8arr _ _ _ _ (Z.to_nat nz) ARR2 ltac:(rewrite length_firstn; cbn [length app]; lia)) as DST. clear ARR2.
  remember (skipn (Z.to_nat nz) ([Z_to_bv 8 0] ++ junk)) as tail3 eqn:ET.
  assert (LEN3 : length tail3 = Z.to_nat (len1 - used1 - nz)) by (subst tail3; rewrite length_skipn; cbn [length app]; lia).
  destruct tail3 as [|j0 jrest]; [exfalso; cbn [length] in LEN3; lia|]. clear ET. cbn [length] in LEN3.
  (* [comment removed for export] *)
  arz_seg KIPY AHK1.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG.
  pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PB PBS].
  pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_intror (or_introl eq_refl)) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PD PDS].
  pose proof (aypol_pages (m_vm_lazy mo1) _ _ _ PGD ltac:(unfold shw_lo, al8 in *; Z.div_mod_to_equations; lia) ltac:(lia)) as PWD.
  assert (PSRC : pol (acc_ok (m_vm_lazy mo1) (y_aS Y s1')) S (S + nz)).
  { destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & F1' & F2)|Y4]]]; [| eapply pol_sub; [exact PIMG| unfold AY_IMG_LO; lia| unfold AY_IMG_HI; lia]| | lia].
    - assert (HBT' : In bt ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: LK ++ REST)) by (right; right; apply in_or_app; right; exact HBT).
      pose proof (RNG _ HBT') as TR. unfold ablock_range in TR.
      eapply (aypol_block Y _ LF _ _ LINK bt); [exact HBT'| lia| lia| lia| lia].
    - destruct (proj1 (LAYY _ _ _ _ _ AHK1) f Hf) as (Lf1 & Lf2 & _). unfold oshw_hi in Lf1.
      eapply (aypol_fframe Y _ LF _ _ LINK f); [exact Hf| lia| lia| lia| lia]. }
  cbn [ab_addr ab_size] in PB, PBS, PD, PDS. unfold oshw_lo, oshw_hi, A_SB, amem in PB, PBS, PD, PDS.
  eapply evtA_cut.
  { eapply (aapp_copy_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mb_addr mb) D1 S nz used1 len1 AF lo (bv_unsigned sp + -128) sh9 sh10
              (zbytes src) _ wsS wsD j0 jrest _ _);
      [ exact ST | exact MI | lia | lia | lia | exact BC | exact BSHu | reflexivity | exact DSHu | reflexivity | exact DST | exact ARR3 | exact TB
      | lia | lia | exact IG1 | exact SWS | exact RCS | exact SWD | exact RCD
      | lia | lia | lia | lia | lia | lia | lia | lia | exact SBD | lia | lia | lia | lia | exact (SNZ NPOS) | exact SLO | exact SRIM | exact SSEP | exact SSEPB
      | subst sh9; unfold A_SB; lia | subst sh10; unfold A_SB; lia
      | eapply pol_sub; [exact PSTK| lia| lia] | eapply pol_sub; [exact PIMG| unfold AY_IMG_LO; lia| unfold AY_IMG_HI; lia]
      | exact PB | exact PBS | exact PD | exact PDS | exact PWD | exact PSRC | exact PSHS ]. }
  cbv beta. intros ms2 (x1 & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU & WM & MI3 & ST3 & BC3 & DST3 & ARR3').
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3.
  (* [comment removed for export] *)
  eapply (rw_cells_transport asegs) in FR; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  destruct HBIN as (hb & HBI & HB1 & HB2 & HBHI).
  assert (HBIN' : In hb ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: LK ++ REST)) by (right; right; apply in_or_app; right; exact HBI).
  pose proof (RNG _ HBIN') as HBR. unfold ablock_range, ACONSTS in HBR. cbn [c_img_hi] in HBR. aceil.
  pose proof (SEP _ _ (or_introl eq_refl) HBIN' (nd_head_ne _ _ _ ND (or_intror (in_or_app _ _ _ (or_intror HBI))))) as XB1.
  pose proof (SEP _ _ (or_intror (or_introl eq_refl)) HBIN' (nd_head_ne _ _ _ (nd_tail _ _ ND) (in_or_app _ _ _ (or_intror HBI)))) as XB2.
  cbn [ab_addr ab_size] in XB1, XB2.
  eapply (rw_cells_transport asegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add alloc_cells length];
    clear - HB1 HB2 HBR CEIL' LO' XB1 XB2 U0 ROOM NPOS; lia].   (* [comment removed for export] *)
  eapply (u8arr_transport asegs) in ARR1; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite ZLB; lia].
  eapply (u8arr_transport asegs) in BSHu; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; lia].
  eapply (u8arr_transport asegs) in DSHu; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length len1) by lia; lia].
  (* [comment removed for export] *)
  destruct (u8arr_of_CB _ _ _ _ _ DST3) as [ARR2 _].
  assert (ARR123 : u8arr asegs m3 D1 (zbytes (yb_bytes b ++ src) ++ [Z_to_bv 8 0] ++ jrest)).
  { rewrite zbytes_app. apply u8arr_app. split.
    - apply u8arr_app. split; [exact ARR1|]. rewrite ZLB. replace (D1 + Z.of_nat (length (yb_bytes b))) with (D1 + used1) by lia. exact ARR2.
    - rewrite length_app, ZLB, ZL. replace (D1 + Z.of_nat (length (yb_bytes b) + length src)) with (D1 + used1 + nz) by lia. cbn [app]. exact ARR3'. }
  pose proof (CB3_of_u8arr _ _ _ _ _ _ (Z.to_nat (used1 + nz)) (Z.to_nat (len1 - (used1 + nz) - 1)) ARR123
                ltac:(rewrite zbytes_length, length_app; lia) ltac:(lia)) as DC3.
  clear ARR1 ARR2 ARR123 ARR3' DST3.
  (* [comment removed for export] *)
  destruct (BACK mo3 Hag3 HLI3) as [AHK3m R3].
  assert (AHK3 : y_AHK Y s1' ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := D1; ab_size := len1 |} :: LK ++ REST) LF m3 mo3).
  { eapply FRAMEY; [exact AHK3m| exact MU| exact WM|].
    constructor; [left; cbn; aceil; lia|].
    constructor; [right; left; eexists; split; [right; left; reflexivity| cbn; lia]|].
    constructor; [right; left; eexists; split; [left; reflexivity| cbn; lia]| constructor]. }
  clear AHK3m.
  pose proof (aystatics_munch _ _ _ YS1 MU WM ltac:(constructor; [cbn; lia| constructor; [cbn; lia| constructor; [cbn; lia| constructor]]])) as YS3.
  eapply J_ret with (sv := []) (b' := mkBuf BS_ok len1 (used1 + nz) (Some d1) (yb_bytes b ++ src)) (mb' := mkMB (mb_id mb) (mb_addr mb) did1 D1) (LK := LK) (junk := junkf).
  - cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app]. exact AHK3.
  - exact YS3.
  - exact FR.
  - exact ST3.
  - exact MI3.
  - exact FRM.
  - exact I.
  - eapply ay_pres_trans; [exact PRES|]. eapply ay_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. apply outside_cons; [| apply outside_cons; [| apply outside_cons; [| exact I]]].
    + eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK1| intros b0 Hb0; right; right; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc].
    + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock D1 len1)); [exact AHK1| right; left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
      intros b0 Hb0. split; [right; right; apply in_or_app; right; exact Hb0|]. cbn. intros E.
      exact (nd_head_ne _ _ _ (nd_tail _ _ ND) (in_or_app _ _ _ (or_intror Hb0)) (eq_sym E)).
    + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mb_addr mb) 32)); [exact AHK1| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
      intros b0 Hb0. split; [right; right; apply in_or_app; right; exact Hb0|]. cbn. intros E.
      exact (nd_head_ne _ _ _ ND (or_intror (in_or_app _ _ _ (or_intror Hb0))) (eq_sym E)).
  - exact YAF.
  - exact SO1.
  - eapply RRT; [exact R1| exact R3].
  - exact CRED.
  - exact HL.
  - split; [| split].
    + split; [| split; [cbn; split; [intros; discriminate| intros; exfalso; lia]| cbn; lia]]. unfold buf_cells. cbn. exact BC3.
    + unfold buf_data. cbn [yb_data yb_used yb_len yb_bytes mb_data]. split; [lia|]. exists jrest. exact DC3.
    + cbn [yb_bytes]. apply Forall_app. split; [exact FB| exact SRCF].
  - split; reflexivity.
  - unfold oshadow, block_shadow, A_SB. split; [exact B8|]. split; [lia|]. exact BSHu.
  - cbn [yb_data yb_len mb_data]. intros _. split; [| unfold oshw_hi, A_SB, amem; cbn; lia].
    unfold oshadow, block_shadow, A_SB. split; [exact D8|]. split; [lia|]. exact DSHu.
  - intros X. exfalso. exact (X LK0).
  - intros X. exfalso. exact (X LK0).
  - exact LK0.   (* [comment removed for export] *)
Qed.
End Fn.
End W.
End RC__1.
