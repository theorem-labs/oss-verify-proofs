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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RMallocRep RMallocTree RMalloc_iface RYajlRep RYajl_iface RY_lib RY_rz RF_memcpy.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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
Lemma ens_need_loop_ge : forall f want need used, 0 < need -> need <= ens_need_loop f want need used.
Proof.
  induction f as [|f IH]; intros want need used Hn; cbn [ens_need_loop]; [lia|].
  destruct ((need - used <=? want) && (0 <? need)); [| lia].
  specialize (IH want (need * 2) used ltac:(lia)). lia.
Qed.

Lemma size_loop : forall (fuel : nat) (need : Z)
    (ra sp gp tp t0 t1 t2 s0 a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (len1 used want : Z),
  0 < need < 2^31 -> 0 <= used < need -> 0 <= want < 2^31 -> 0 <= len1 < 2^31 ->
  want + used < need * 2 ^ (Z.of_nat fuel) ->
  ens_need_loop fuel want need used < 2^31 ->
  evt rsegs (fun ms' => exists a2' a3',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (wz want) (wz len1) (wz used) a2' a3' a4 a5 a6 a7 s2
                     (wz (ens_need_loop fuel want need used)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (wz 0x15128) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (wz want) (wz len1) (wz used) (wz need) a3 a4 a5 a6 a7 s2 s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x15114) fc None m (seg_rom rsegs)).
Proof.
  induction fuel as [|fuel IH]; intros until want; intros NB UB WB LB FB RB; unfold wz.
  - cbn [ens_need_loop] in *. change (2 ^ Z.of_nat 0) with 1 in FB.
    zstep. zstep. if_cases K0; zify_cond K0. 1:{ kill K0. }
    zstep. zstep.
    replace (bv_swrap 32 (need - used)) with (need - used) by (rewrite ybv_swrap32_eq; rewrite Z.mod_small; lia).
    zstep. if_cases K1; zify_cond K1. 1:{ kill K1. }
    apply evt_done. eexists _, _. reflexivity.
  - cbn [ens_need_loop] in RB |- *.
    zstep. zstep. if_cases K0; zify_cond K0. 1:{ kill K0. }
    zstep. zstep.
    replace (bv_swrap 32 (need - used)) with (need - used) by (rewrite ybv_swrap32_eq; rewrite Z.mod_small; lia).
    destruct (Z.leb_spec (need - used) want); destruct (Z.ltb_spec 0 need); try lia; cbn [andb] in RB |- *.
    + (* [comment removed for export] *)
      pose proof (ens_need_loop_ge fuel want (need * 2) used ltac:(lia)) as GE.
      replace (bv_swrap 32 (Z.shiftl need 1)) with (need * 2)
        by (rewrite Z.shiftl_mul_pow2, ybv_swrap32_eq by lia; rewrite Z.mod_small; lia).
      zstep. if_cases K1; zify_cond K1. 2:{ kill K1. }
      rewrite Nat2Z.inj_succ, Z.pow_succ_r in FB by lia.
      apply IH; try lia. all: replace (need * 2 * 2 ^ Z.of_nat fuel) with (need * (2 * 2 ^ Z.of_nat fuel)) by ring; exact FB.
    + zstep. if_cases K1; zify_cond K1. 1:{ kill K1. }
      apply evt_done. eexists _, _. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma yleaf_ymalloc : forall n r, yleaf (ymalloc n) r.
Proof. intros. unfold ymalloc. apply (yl_malloc _ _ r). apply yl_ret. Qed.
Lemma yleaf_yrealloc : forall p n r, yleaf (yrealloc p n) r.
Proof. intros. unfold yrealloc. apply (yl_realloc _ _ _ r). apply yl_ret. Qed.
Lemma yleaf_yfree : forall p, yleaf (yfree p) tt.
Proof. intros. unfold yfree. apply yl_free. apply yl_ret. Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWM : ywrap_malloc_stmt HK.
Hypothesis YWR : ywrap_realloc_stmt HK.

Section Fn.
(* [comment removed for export] *)
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

Definition app_frame (m1 : mem) (junk : list byte) : Prop :=
  rw_cells rsegs m1 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma app_ret : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0v s1v s2v s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (b' : ybuf) (mb' : mbuf) (LK : list block) (junk : list byte) (errv1 : word),
  HK s1' (buf_blocks mb' b' ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  app_frame m1 junk -> stk rsegs m1 lo (bv_unsigned sp + -48) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 AF (alloc_cells ryc) ->
  yleaf (ybuf_append b src) b' -> buf_rep rsegs m1 mb' b' AF -> mb_same mb mb' -> LK = [] ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz 0x151e0) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros until errv1. intros HK1 YS1 FR STK MI AX ERR PRES YAF HL BR MBS LKN.
  unfold app_frame, wz in *. pose proof LO as LO'. unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK in LO'.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  rz_seg HKS HK1.
  step. step. step. step. step. step. step.
  apply evt_done. release_frame FR STK (bv_unsigned sp).
  eapply CONT. unfold ybuf_append_rpost.
  split; [| split; [exact YAF| split; [exact HL| split; [exact BR| split; [exact MBS| split; [exact LKN| apply RYST_split; split; [exact HK1| exact YS1]]]]]]].
  split; [exact MI|]. split; [exact STK|]. split; [exists errv1; rewrite (ry_errno_lit tp TP); exact ERR|].
  split; [exact AX| exact PRES].
Qed.

Hypothesis SRCF : Forall (fun c => 0 <= c < 256) src.
Hypothesis SNZ : 0 < n -> SA <> 0.
Hypothesis SBND : SA + n <= 2^64.
Hypothesis YSR : ysrc_range REST sp SA n.
Hypothesis FB : Forall (fun c => 0 <= c < 256) (yb_bytes b).

(* [comment removed for export] *)
Lemma app_copy : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3v t3 t4 t5 t6 : word)
    (m1 : mem) (mo1 : Model) (s1' : PState) (LK : list block) (junkf junk : list byte) (errv1 : word)
    (len1 used1 : Z) (d1 : yptr) (did1 : bptr) (D1 : Z),
  let b1 := mkBuf BS_ok len1 used1 (Some d1) (yb_bytes b) in
  let mb1 := mkMB (mb_id mb) (mb_addr mb) did1 D1 in
  HK s1' (buf_blocks mb1 b1 ++ LK ++ REST) m1 mo1 -> ystatics m1 ->
  app_frame m1 junkf -> stk rsegs m1 lo (bv_unsigned sp + -48) -> mem_inv rsegs m1 -> rauxv_ok m1 B ->
  rw_cells rsegs m1 RERRNO [C4 errv1] ->
  ry_pres REST (bv_unsigned sp) [] m m1 ->
  rw_cells rsegs m1 AF (alloc_cells ryc) ->
  rw_cells rsegs m1 (mb_addr mb) [C4 (wz 0); C4 (wz len1); C4 (wz used1); C4 (wz 0); C8 (wz D1); C8 (wz AF)] ->
  rw_cells rsegs m1 D1 [CB (Z.to_nat used1) (zbytes (yb_bytes b)); C1 (Z_to_bv 8 0); CB (Z.to_nat (len1 - used1 - 1)) junk] ->
  bytes_at rsegs m1 SA (zbytes src) ->
  0 <= used1 -> used1 = zlength (yb_bytes b) -> used1 + n < len1 -> len1 < 2^31 -> 0 < n ->
  yleaf (ybuf_append b src) (mkBuf BS_ok len1 (used1 + n) (Some d1) (yb_bytes b ++ src)) -> LK = [] ->
  realizes_cfg acfg rsegs (mkCfg (MS (mkR rav (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 (wz (mb_addr mb)) (wz n) a0 a1 a2 a3 a4 a5 a6 a7 (wz SA) s3v s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                           F (wz 0x15158) fc None m1 (seg_rom rsegs)) mo1) K.
Proof.
  intros until D1. cbv zeta. intros HK1 YS1 FR STK MI AX ERR PRES YAF BC DC TB U0 UB ROOM L31 NPOS HL LKN.
  unfold app_frame, wz in *. pose proof LO as LO'. unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK, alloc_ceiling in LO', CEIL.
  destruct HBIN as (hb & HBI & HB1 & HB2).
  destruct (HK_blocks HK HKB _ _ _ _ HK1) as [RNG SEP].
  cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app] in RNG, SEP, HK1.
  pose proof (all_range_In _ _ RNG (or_introl eq_refl)) as BR. unfold rblock_range, alloc_ceiling in BR. cbn [blk_addr blk_size fst snd] in BR.
  pose proof (all_range_In _ _ RNG (or_intror (or_introl eq_refl))) as DR. unfold rblock_range, alloc_ceiling in DR. cbn [blk_addr blk_size fst snd] in DR.
  assert (HBI' : In hb ((mb_id mb, mb_addr mb, SIZEOF_BUF) :: (did1, D1, len1) :: LK ++ REST)) by (right; right; apply in_or_app; right; exact HBI).
  pose proof (all_range_In _ _ RNG HBI') as HBR. unfold rblock_range, alloc_ceiling in HBR.
  cbn [all_sep] in SEP. destruct SEP as (SEPB & SEPD & _). cbn [sep_from] in SEPB. destruct SEPB as [SBD SEPB].
  unfold bsep in SBD. cbn [blk_addr blk_size fst snd] in SBD.
  pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBI)) as SBH. unfold bsep in SBH. cbn [blk_addr blk_size fst snd] in SBH.
  pose proof (sep_from_In _ _ _ SEPD ltac:(apply in_or_app; right; exact HBI)) as SDH. unfold bsep in SDH. cbn [blk_addr blk_size fst snd] in SDH.
  pose proof (rw_cells_bound _ _ _ _ YAF) as YAFB. cbn [cells_size csize Nat.add alloc_cells length] in YAFB.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in YAF. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, SIZEOF_BUF in *.
  unfold wz in YAF. unfold RERRNO in ERR.
  pose proof (bytes_at_bound _ _ _ _ TB) as TBB. pose proof (zbytes_length src) as ZL. unfold zlength in *.
  (* [comment removed for export] *)
  assert (SSEP : SA + n <= D1 \/ D1 + len1 <= SA).
  { destruct YSR as [(bt & HBT & T1 & T2)|[R2|[R3|R4]]]; [| lia| lia| lia].
    pose proof (sep_from_In _ _ _ SEPD ltac:(apply in_or_app; right; exact HBT)) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. lia. }
  assert (SSEPB : SA + n <= mb_addr mb \/ mb_addr mb + 32 <= SA).
  { destruct YSR as [(bt & HBT & T1 & T2)|[R2|[R3|R4]]]; [| lia| lia| lia].
    pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact HBT)) as X. unfold bsep in X. cbn [blk_addr blk_size fst snd] in X. lia. }
  (* [comment removed for export] *)
  destruct (u8arr_of_CB3 _ _ _ _ _ _ _ _ DC) as (ARR & L1 & L2). clear DC.
  apply u8arr_app in ARR. destruct ARR as [ARR1 ARR23]. rewrite L1, Z2Nat.id in ARR23 by lia.
  rewrite <- (firstn_skipn (Z.to_nat n) ([Z_to_bv 8 0] ++ junk)) in ARR23.
  apply u8arr_app in ARR23. destruct ARR23 as [ARR2 ARR3].
  rewrite length_firstn in ARR3. replace (Z.of_nat (Nat.min (Z.to_nat n) (length ([Z_to_bv 8 0] ++ junk)))) with n in ARR3 by (cbn [length app]; rewrite ?length_app; cbn [length]; lia).
  pose proof (CB_of_u8arr _ _ _ _ (Z.to_nat n) ARR2 ltac:(rewrite length_firstn; cbn [length app]; lia)) as DST. clear ARR2.
  remember (skipn (Z.to_nat n) ([Z_to_bv 8 0] ++ junk)) as tail3 eqn:ET.
  assert (LEN3 : length tail3 = Z.to_nat (len1 - used1 - n)) by (subst tail3; rewrite length_skipn; cbn [length app]; lia).
  destruct tail3 as [|j0 jrest]; [exfalso; cbn [length] in LEN3; lia|]. clear ET. cbn [length] in LEN3.
  pose proof (zbytes_length (yb_bytes b)) as ZLB.
  assert (USA : bv_unsigned (Z_to_bv 64 SA) = SA) by (apply unsigned_lit; lia).
  assert (UDU : bv_unsigned (Z_to_bv 64 (D1 + used1)) = D1 + used1) by (apply unsigned_lit; clear - DR U0 ROOM NPOS; lia).
  assert (UN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  destruct BR as (BR0 & _ & _ & BR3 & BR4). destruct DR as (DR0 & _ & _ & DR3 & DR4).
  clear RNG YSR HBI' HBR L1 L2 TBB. yhide SBH. yhide SDH. yhide SEPB. yhide SEPD. yhide YAFB.
  remember (Z.to_nat used1) as nu eqn:Enu. assert (Hnu : Z.of_nat nu = used1) by lia. clear Enu.
  remember (Z.to_nat n) as nn eqn:Enn. assert (Hnn : Z.of_nat nn = n) by lia. clear Enn.
  remember (Z.to_nat (len1 - used1 - n - 1)) as nr eqn:Enr. assert (Hnr : Z.of_nat nr = len1 - used1 - n - 1) by lia.
  assert (LJ : length jrest = nr) by lia. clear Enr LEN3.
  yhide FR. yhide ERR. yhide YAF. yhide ARR1. yhide BR4. yhide DR4.
  pose proof (munch_refl [(mb_addr mb, mb_addr mb + 32); (D1 + used1, D1 + used1 + n + 1)] m1) as MU. pose proof (wmono_refl rsegs m1) as WM.
  rz_seg HKS HK1.
  step. if_cases KA; zify_cond KA. 1:{ exfalso. specialize (SNZ NPOS). kill KA. }
  zstep. rewrite yzx32_small by lia. zstep. zstep. zstep. zstep. rewrite (land_M32_small n) by lia. zstep.
  zstep. call memcpy_spec.
  1:{ rewrite USA. exact TB. }
  1:{ rewrite UN, ZL. lia. }
  1:{ rewrite UDU, UN. replace (Z.to_nat n) with nn by lia. exact DST. }
  1:{ rewrite USA, UDU, UN. lia. }
  1:{ assumption. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  lazymatch goal with H : rw_cells _ m2 (bv_unsigned (Z_to_bv 64 (D1 + used1))) _ |- _ => rename H into DST2; rewrite UDU, UN in DST2; replace (Z.to_nat n) with nn in DST2 by lia end.
  lazymatch goal with H : bytes_at _ m2 (bv_unsigned (Z_to_bv 64 SA)) _ |- _ => clear H end.
  clear SSEP SSEPB.
  zstep. rewrite ysx32_small by lia. zstep. zstep. zstep.
  zstep. zstep. rewrite (land_M32_small (used1 + n)) by lia. zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (u8arr_store_ok_at rsegs mx (D1 + used1 + n) _ 0 ARR3 ltac:(cbn [length]; lia)) as SOK end.
  step.
  lazymatch type of ARR3 with Arr.u8arr _ ?mx _ _ =>
    pose proof (u8arr_write rsegs mx (D1 + used1 + n) _ 0 (Z_to_bv 8 0) ARR3 ltac:(cbn [length]; lia)) as ARR3' end.
  cbn [upd Z.to_nat] in ARR3'. rewrite le1_wz by lia. clear ARR3. store_done.
  step. apply evt_done.
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m3 end.
  yreveal ARR1 MU WM. yreveal FR MU WM.
  yshow BR4. yshow DR4. yreveal ERR MU WM.
  yshow SBH. yshow SDH. yshow YAFB. yreveal YAF MU WM.
  yshow SEPB. yshow SEPD.
  lazymatch goal with H : mem_inv _ m3 |- _ => rename H into MI3 end.
  (* [comment removed for export] *)
  change (Z.to_nat 0) with 0%nat in ARR3'. cbn [upd] in ARR3'.
  destruct (u8arr_of_CB _ _ _ _ _ DST2) as [ARR2 _].
  assert (ARR12 : Arr.u8arr rsegs m3 D1 (zbytes (yb_bytes b) ++ zbytes src)).
  { apply u8arr_app. split; [exact ARR1|]. rewrite ZLB. replace (D1 + Z.of_nat (length (yb_bytes b))) with (D1 + used1) by lia. exact ARR2. }
  assert (ARR123 : Arr.u8arr rsegs m3 D1 (zbytes (yb_bytes b ++ src) ++ [Z_to_bv 8 0] ++ jrest)).
  { rewrite zbytes_app. apply u8arr_app. split; [exact ARR12|].
    rewrite length_app, ZLB, ZL. replace (D1 + Z.of_nat (length (yb_bytes b) + length src)) with (D1 + used1 + n) by lia.
    cbn [app]. exact ARR3'. }
  pose proof (CB3_of_u8arr _ _ _ _ _ _ (Z.to_nat (used1 + n)) nr ARR123
                ltac:(rewrite zbytes_length, length_app; lia) LJ) as DC3.
  clear ARR1 ARR2 ARR12 ARR123 ARR3' DST2.
  (* [comment removed for export] *)
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK1 AX MU WM) as [HK3 AX3].
  { constructor; [| constructor; [| constructor]].
    - right; right. eexists. split; [left; reflexivity| cbn; lia].
    - right; right. eexists. split; [right; left; reflexivity| cbn; lia]. }
  { clear - BR3 BR4 DR3 DR4 U0 ROOM NPOS SPB LO' CEIL; constructor; [| constructor; [| constructor]]; cbn; unfold RAUXV_CELL; lia. }
  pose proof (ystatics_munch _ _ _ YS1 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor; [cbn; unfold RY_CALLBACKS; lia| constructor]])) as YS3.
  eapply (app_ret _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo1 s1'
            (mkBuf BS_ok len1 (used1 + n) (Some d1) (yb_bytes b ++ src)) (mkMB (mb_id mb) (mb_addr mb) did1 D1) LK junkf errv1).
  - cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data app]. exact HK3.
  - exact YS3.
  - exact FR.
  - exact STK.
  - exact MI3.
  - exact AX3.
  - exact ERR.
  - eapply ry_pres_trans; [exact PRES|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    clear - BR0 BR3 BR4 DR0 DR3 DR4 SEPB SEPD LO' CEIL U0 ROOM NPOS.
    intros a Ha Hc _. cbn. split; [| split; [| exact I]].
    + destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (sep_from_In _ _ _ SEPB ltac:(apply in_or_app; right; exact Hb)) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. lia.
    + destruct Hc as [Hc|[Hc|(b0 & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
      pose proof (sep_from_In _ _ _ SEPD ltac:(apply in_or_app; right; exact Hb)) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. lia.
  - unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc]. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz. exact YAF.
  - exact HL.
  - split; [| split].
    + split; [| split; [cbn; split; [intros; discriminate| intros; exfalso; lia]| cbn; lia]]. unfold buf_cells. cbn. exact BC.
    + unfold buf_data. cbn [yb_data yb_used yb_len yb_bytes]. split; [lia|]. exists jrest.
      replace (Z.to_nat (len1 - (used1 + n) - 1)) with nr by lia. exact DC3.
    + cbn [yb_bytes]. apply Forall_app. split; [exact FB| exact SRCF].
  - split; reflexivity.
  - exact LKN.
Qed.
End Fn.
End S.
End RC__1.
