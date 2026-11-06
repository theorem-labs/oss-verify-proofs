(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UF_memcpy.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLex YajlParser YajlLeaf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma yleaf_ymalloc : forall n r, yleaf (ymalloc n) r.
Proof. intros n r. unfold ymalloc. apply (yl_malloc _ _ r). apply yl_ret. Qed.
Lemma yleaf_yrealloc : forall p n r, yleaf (yrealloc p n) r.
Proof. intros p n r. unfold yrealloc. apply (yl_realloc _ _ _ r). apply yl_ret. Qed.
Lemma yleaf_yfree : forall p, yleaf (yfree p) tt.
Proof. intros p. unfold yfree. apply yl_free. apply yl_ret. Qed.

Lemma ylex_alloc_leaf_some : forall aC v8 blk lx,
  yleaf (ylex_alloc aC v8) (Some (blk, lx)) -> exists bb, lx = mkLexer 0 0 LE_ok ybuf_zero bb 0 0 aC v8.
Proof.
  intros aC v8 blk lx HL. unfold ylex_alloc in HL. apply yleaf_bind_inv in HL. destruct HL as (r & _ & HL).
  destruct r as [b0|]; [| apply yleaf_ret_inv in HL; discriminate].
  apply yleaf_bind_inv in HL. destruct HL as (rb & _ & HL).
  destruct rb as [bb|].
  - apply yleaf_ret_inv in HL. exists bb. congruence.
  - apply yleaf_bind_inv in HL. destruct HL as (u & _ & HL). apply yleaf_ret_inv in HL. discriminate.
Qed.

(* [comment removed for export] *)
Lemma yleaf_ybuf_free : forall blk b, yleaf (ybuf_free blk b) tt.
Proof. intros blk b. unfold ybuf_free. destruct (yb_data b); [apply (yleaf_bind _ _ tt); apply yleaf_yfree| apply yleaf_yfree]. Qed.
Lemma yleaf_ylex_free : forall blk lx, yleaf (ylex_free blk lx) tt.
Proof. intros blk lx. unfold ylex_free. apply (yleaf_bind _ _ tt); [apply yleaf_ybuf_free| apply yleaf_yfree]. Qed.

(* [comment removed for export] *)
Lemma yalloc_leaf_ok : forall aC v8 (hb lb : yptr) lx (db sb : yptr), yleaf (ylex_alloc aC v8) (Some (lb, lx)) ->
  yleaf (yajl_alloc aC v8) (Some (mkHandle hb lb lx None 0 db ybuf_zero [ST_start] 128 (Some sb))).
Proof.
  intros aC v8 hb lb lx db sb HL. unfold yajl_alloc. apply (yleaf_bind _ _ (Some hb)); [apply yleaf_ymalloc|]. cbn beta iota.
  apply (yleaf_bind _ _ (Some (lb, lx))); [exact HL|]. cbn beta iota.
  apply (yleaf_bind _ _ (Some db)); [unfold ybuf_alloc; apply yleaf_ymalloc|]. cbn beta iota zeta.
  apply (yleaf_bind _ _ (true, h_set_stack3 (mkHandle hb lb lx None 0 db ybuf_zero [] 0 None) [ST_start] 128 (Some sb))).
  { unfold ybs_push, h_used. cbn [h_stack_size h_stack h_stack_blk].
    replace (0 - zlength [] =? 0) with true by reflexivity. replace (UINT_MAX - YAJL_BS_INC <? 0) with false by reflexivity. cbv beta iota zeta.
    apply (yleaf_bind _ _ (Some sb)); [apply yleaf_yrealloc| apply yl_ret]. }
  cbn beta iota. apply yl_ret.
Qed.

Lemma perm_yalloc : forall (A : Type) (sb db lb bb hb : A) (R : list A),
  Permutation (sb :: db :: lb :: bb :: hb :: R) (hb :: lb :: bb :: db :: sb :: R).
Proof.
  intros.
  change (hb :: lb :: bb :: db :: sb :: R) with ([hb; lb; bb; db] ++ sb :: R). apply Permutation_cons_app. cbn [app].
  change (hb :: lb :: bb :: db :: R) with ([hb; lb; bb] ++ db :: R). apply Permutation_cons_app. cbn [app].
  change (hb :: lb :: bb :: R) with ([hb] ++ lb :: bb :: R). apply Permutation_cons_app. cbn [app].
  apply perm_swap.
Qed.

Section S.
Variable HK : RawAlloc.PState -> list block -> (word -> option byte) -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YWM : ywrap_malloc_stmt HK.
Hypothesis YWRN : ywrap_realloc_null_stmt HK.
Hypothesis YSD : yset_default_stmt.
Hypothesis YBA : ybuf_alloc_stmt HK.
Hypothesis YLA : ylex_alloc_stmt HK.

Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.
Ltac lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       end).
Lemma land7_of_mod8 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.
Lemma land3_of_mod4 : forall x, x mod 4 = 0 -> Z.land x 3 = 0.
Proof. intros x H. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. exact H. Qed.
Lemma mod8_of_mod16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. rewrite <- (Z.mod_mod_divide x 16 8) by (try lia; exists 2; reflexivity). rewrite H. reflexivity. Qed.
Lemma mod8_off : forall x k, x mod 16 = 0 -> k mod 8 = 0 -> (x + k) mod 8 = 0.
Proof. intros x k H Hk. rewrite Z.add_mod, (mod8_of_mod16 _ H), Hk by lia. reflexivity. Qed.



Lemma yalloc_spec : yalloc_stmt HK.
Proof.
  unfold yalloc_stmt. intros REST CFGP CX lo B errv K. intros until s. intros K0 [SPA CFGA] RY CFG CFG1 CFG2 YR FP A0 A1 A2 A3 CONT.
  pose proof (land7_of_mod8 _ (mod8_off _ (-72) SPA eq_refl)) as L7S1. pose proof (land3_of_mod4 _ CFGA) as L3C.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  pose proof (proj1 STK) as LO0.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  rewrite (ry_errno_lit tp TP) in ERR. unfold RERRNO in ERR.
  pose proof (rw_cells_bound _ _ _ _ CFG) as CFGB. cbn [cells_size csize Nat.add length] in CFGB.
  subst a0 a1 a2 a3. unfold RY_ALLOC, RY_ALLOC_STACK, RY_LEX_ALLOC_STACK, RY_BUF_ALLOC_STACK, RY_WRAP_STACK, alloc_ceiling, wz in *.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  rz_seg HKS HK0.
  step. carve_frame 96%nat STK. step. step. step. step. step. step. step. step.
  step. step. step.
  step. if_cases K1; zify_cond K1. 2:{ kill K1. } clear K1.
  step. step. step. step.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96) (CB 32 ?j :: ?rest) |- _ =>
    destruct (proj1 (ycells_app usegs _ _ [CB 32 j] rest) H) as [AFS FRS]; clear H end.
  cbn [cells_size csize Nat.add] in FRS.
  step. call (YSD (bv_unsigned sp + -96)).
  all: try (unfold UA_yset_default; split; [lia | apply (mod8_off _ (-96)); [exact SPA | reflexivity]]).
  1:{ exact AFS. } 1:{ assumption. } 1:{ reflexivity. }
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96) _ |- _ => rename H into AFS' end.
  unfold alloc_cells in AFS'. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in AFS'. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in AFS'.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96 + Z.of_nat 32) _ |- _ => rename H into FRS' end.
  pose proof (proj2 (ycells_app usegs _ _ _ _) (conj AFS' FRS')) as FR. clear AFS' FRS'. cbn [app] in FR.
  zstep. step. if_cases GA; zify_cond GA. 1:{ kill GA. }
  step. step. step. step.
  apply evt_done.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MU WM) as [HK1 AX1].
  { constructor; [| constructor]. left. cbn. unfold alloc_ceiling. lia. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
  pose proof (ystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; lia| constructor])) as YS1.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI1; rename my into m1 end.
  lazymatch goal with H : stk _ m1 _ _ |- _ => rename H into STK1 end.
  lazymatch goal with H : rw_cells _ m1 CFGP _ |- _ => rename H into CFGc end.
  lazymatch goal with H : rw_cells _ m1 218620 _ |- _ => rename H into ERR1 end.
  assert (PRES1 : ry_pres REST (bv_unsigned sp) [] m m1).
  { eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; lia|].
    pose proof (all_range_In _ _ RNG Hb) as Hbr. unfold rblock_range, alloc_ceiling in Hbr. lia. }
  clear MU WM AX HK0 YS. try clear MI; try clear ERR; try clear STK.
  eapply YWM; [exact K0 | exact HK1 | exact AX1 | rewrite ESP; lia | rewrite ESP; exact STK1 | exact CEIL
               | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR1
               | exact MI1 | exact TP | reflexivity | unfold NUSERc; lia | eapply yroom_lt; [exact YR| lia] | ].
  cbv beta. intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 mo2 s2' errv2 ph Hd MI2 STK2 ERR2 AX2 HP A0' HR HK2 NEW.
  replace (ret_pc (Z_to_bv 64 80976)) with (Z_to_bv 64 80976) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK2, HP. rewrite (ry_errno_lit tp TP) in ERR2. unfold RERRNO in ERR2.
  pose proof (ystatics_pres _ _ _ _ YS1 HP) as YS2.
  pose proof (ypres_frame _ _ _ _ _ _ HP FR ltac:(lia)) as FR2. clear FR.
  pose proof (ypres_frame _ _ _ _ _ _ HP CFGc ltac:(lia)) as CFG2c. clear CFGc.
  assert (PRES2 : ry_pres REST (bv_unsigned sp) [] m m2).
  { eapply ry_pres_trans; [exact PRES1|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP| lia| auto]. }
  clear HP MI1 AX1 ERR1 STK1 HK1 YS1 PRES1.
  (* [comment removed for export] *)
  subst a0'. unfold rblock_range, alloc_ceiling in HR. unfold wz. destruct NEW as [junkh NEW].
  destruct HR as (HR0 & HRA & _ & HR3 & HR4). yhide HR4. pose proof (land7_of_mod8 _ (mod8_of_mod16 _ HRA)) as L7H.
  destruct (HK_blocks HK HKB _ _ _ _ HK2) as [_ SEP2]. cbn [all_sep] in SEP2. destruct SEP2 as [SEPH _].
  assert (UH : bv_unsigned (Z_to_bv 64 Hd) = Hd) by (apply unsigned_lit; lia).
  assert (UH72 : bv_unsigned (Z_to_bv 64 (Hd + 72)) = Hd + 72) by (apply unsigned_lit; lia).
  assert (U32 : bv_unsigned (Z_to_bv 64 32) = 32) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  assert (PRESH : forall ma mb, munch [(Hd, Hd + 104)] ma mb -> wmono usegs ma mb -> ry_pres REST (bv_unsigned sp) [] ma mb).
  { intros ma mb MU1 WM1. eapply ryajl_pres_of_munch; [exact MU1| exact WM1|]. yshow HR4.
    intros a Ha Hc _. cbn. split; [| exact I].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [clear -Hc HR3 CEIL LO; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc HR4; lia|].
    pose proof (sep_from_In _ _ _ SEPH Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. clear -Hs Hr. lia. }
  assert (ERRV : forall ma mb (ev : word), munch [(Hd, Hd + 104)] ma mb -> wmono usegs ma mb ->
            rw_cells usegs ma 218620 [C4 ev] -> rw_cells usegs mb 218620 [C4 ev]).
  { intros ma mb ev MU1 WM1 E1. yshow HR4. eapply (rw_cells_transport usegs); [exact E1| exact MU1| exact WM1| cbv [disjoint_from fst snd]; cbn; clear -HR4; lia]. }
  (* [comment removed for export] *)
  pose proof (rw_cells_split_CB usegs m2 Hd [] 104 junkh [] [72%nat; 32%nat] NEW eq_refl) as NEW'. clear NEW.
  cbn [app mk_CB_cells] in NEW'.
  destruct (proj1 (ycells_app usegs m2 Hd [CB 72 (take 72 junkh)] [CB 32 (take 32 (drop 72 junkh))]) NEW') as [HH HA]. clear NEW'.
  cbn [cells_size csize Nat.add] in HA. change (Z.of_nat 72) with 72 in HA.
  lazymatch type of FR2 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    destruct (proj1 (ycells_app usegs _ _ [c0; c1; c2; c3] rest) FR2) as [AFS2 FRS2] end. clear FR2.
  cbn [cells_size csize Nat.add] in FRS2.
  pose proof (rw_cells_bytes_at _ _ _ _ AFS2) as SRC. cbn [cells_bytes cbytes app] in SRC.
  pose proof (munch_refl [(Hd, Hd + 104)] m2) as MU. pose proof (wmono_refl usegs m2) as WM.
  yhide ERR2.
  rz_seg HKS HK2.
  step. if_cases K1; zify_cond K1. 1:{ kill K1. } clear K1.
  step. zstep. step. if_cases GB; zify_cond GB. 1:{ kill GB. }
  step. step. step. step.
  step. call memcpy_spec.
  1:{ rewrite ESP. exact SRC. } 1:{ rewrite U32. reflexivity. } 1:{ rewrite UH72, U32. exact HA. } 1:{ rewrite ESP, UH72, U32. lia. } 1:{ assumption. }
  clear SRC.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned (Z_to_bv 64 (Hd + 72))) _ |- _ => rename H into DST; rewrite UH72, U32 in DST end.
  lazymatch goal with H : bytes_at _ _ (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96))) _ |- _ => clear H | _ => idtac end.
  lazymatch type of DST with rw_cells _ ?mx _ _ =>
    assert (HA3 : rw_cells usegs mx (Hd + 72) [C8 (Z_to_bv 64 81588); C8 (Z_to_bv 64 81608); C8 (Z_to_bv 64 81600); C8 (Z_to_bv 64 0)])
      by (eapply rw_cells_recast; [exact DST| cbn; repeat split; exact I| reflexivity| reflexivity]) end.
  clear DST.
  lazymatch goal with H1 : rw_cells _ _ (bv_unsigned sp + -96) _, H2 : rw_cells _ _ (bv_unsigned sp + -96 + Z.of_nat 32) _ |- _ =>
    pose proof (proj2 (ycells_app usegs _ _ _ _) (conj H1 H2)) as FR; clear H1 H2; cbn [app] in FR end.
  step. if_cases K2; zify_cond K2. 1:{ kill K2. } clear K2.
  zstep. step. if_cases GC; zify_cond GC. 1:{ kill GC. }
  step. step. step.
  step. step. step. step.
  apply evt_done.
  (* [comment removed for export] *)
  yshow ERR2. pose proof (ERRV _ _ _ MU WM ERR2) as ERR3. clear ERR2.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK2 AX2 MU WM) as [HK3 AX3].
  { constructor; [| constructor]. right; right. exists (ph, Hd, 104). split; [left; reflexivity| cbn; lia]. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. yshow HR4. clear -HR3 HR4 CEIL LO SPB. lia. }
  yshow HR4. pose proof (ystatics_munch _ _ _ YS2 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -HR4; lia| constructor])) as YS3. yhide HR4.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI3; rename my into m3 end.
  lazymatch goal with H : stk _ m3 _ _ |- _ => rename H into STK3 end.
  lazymatch goal with H : rw_cells _ m3 CFGP _ |- _ => rename H into CFG3 end.
  lazymatch goal with H : rw_cells _ m3 Hd _ |- _ => rename H into HH3 end.
  lazymatch goal with H : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => rename H into FR3 end.
  pose proof (ry_pres_trans _ _ _ _ _ _ PRES2 (PRESH _ _ MU WM)) as PRES3.
  clear MU WM AX2 HK2 YS2 PRES2. try clear MI2; try clear STK2; try clear CFG2c.
  eapply (YLA ((ph, Hd, 104) :: REST) (Hd + 72) 1 1 lo B errv2 K);
    [ exact K0 | split; [lia | apply (mod8_off _ 72); [exact HRA | reflexivity]] | apply RYST_split; split; [exact HK3| exact YS3] | exact HA3
    | exists (ph, Hd, 104); split; [left; reflexivity| cbn; lia]
    | lia | lia
    | apply yroom_cons; eapply yroom_le; [exact YR| lia]
    | split; [exact AX3|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK3|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_LEX_ALLOC_STACK, RY_BUF_ALLOC_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR3|]; split; [exact MI3| exact TP]
    | reflexivity | reflexivity | reflexivity | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' m4 mo4 s4' L lid mbl lx POST.
  destruct POST as ((MI4 & STK4 & (errv4 & ERR4) & AX4 & HP4) & HA4 & RES2).
  replace (ret_pc (Z_to_bv 64 81060)) with (Z_to_bv 64 81060) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK4, HP4. rewrite (ry_errno_lit tp TP) in ERR4. unfold RERRNO in ERR4. apply ry_pres_nil in HP4.
  pose proof (ystatics_pres _ _ _ _ YS3 HP4) as YS4.
  pose proof (ypres_frame _ _ _ _ _ _ HP4 FR3 ltac:(lia)) as FR4. clear FR3.
  pose proof (ypres_frame _ _ _ _ _ _ HP4 CFG3 ltac:(lia)) as CFG4. clear CFG3.
  pose proof (ypres_block _ _ _ _ _ _ HP4 HH3 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as HH4. clear HH3.
  assert (PRES4 : ry_pres REST (bv_unsigned sp) [] m m4).
  { eapply ry_pres_trans; [exact PRES3|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP4| lia| intros b0 Hb0; right; exact Hb0]. }
  unfold alloc_cells in HA4. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in HA4. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in HA4.
  clear HP4 MI3 STK3 ERR3 AX3 HK3 YS3 PRES3 HA3.
  (* [comment removed for export] *)
  destruct RES2 as (A0' & LNZ & (blk0 & HLX) & LR4 & MBD & RY4). subst a0''. unfold wz. apply RYST_split in RY4. destruct RY4 as [HK4 _].
  destruct (ylex_alloc_leaf_some _ _ _ _ HLX) as [bb ELX]. subst lx.
  cbn [lexer_blocks buf_blocks lx_buf yb_data yb_len ybuf_zero app] in HK4. unfold SIZEOF_LEXER, SIZEOF_BUF in HK4.
  destruct (HK_blocks HK HKB _ _ _ _ HK4) as [RNG4 SEP4].
  pose proof (all_range_In _ _ RNG4 (or_introl eq_refl)) as LRG. unfold rblock_range, alloc_ceiling in LRG. cbn [blk_addr blk_size fst snd] in LRG.
  destruct LRG as (LRG0 & _ & _ & LRG3 & _).
  cbn [all_sep sep_from] in SEP4. destruct SEP4 as ((_ & SLH & SLR) & (SBH & SBR) & _). clear RNG4.
  unfold bsep in SLH, SBH. cbn [blk_addr blk_size fst snd] in SLH, SBH.
  assert (UL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (LRT : forall ma mb, munch [(Hd, Hd + 104)] ma mb -> wmono usegs ma mb ->
            lexer_rep usegs ma L (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) mbl (Hd + 72) -> lexer_rep usegs mb L (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) mbl (Hd + 72)).
  { intros ma mb MU1 WM1 LR1. eapply lexer_rep_transport; [exact LR1| exact MU1| exact WM1| cbv [disjoint_from fst snd]; clear -SLH; lia| cbv [disjoint_from fst snd]; clear -SBH; lia|].
    cbn [lx_buf yb_data ybuf_zero]. intros X; exfalso; apply X; reflexivity. }
  yhide SLH. yhide SBH.
  pose proof (munch_refl [(Hd, Hd + 104)] m4) as MU. pose proof (wmono_refl usegs m4) as WM.
  yhide ERR4.
  rz_seg HKS HK4.
  step. step. if_cases K3; zify_cond K3. 1:{ kill K3. } clear K3.
  step. lit_store. step. step.
  apply evt_done.
  (* [comment removed for export] *)
  yshow ERR4. pose proof (ERRV _ _ _ MU WM ERR4) as ERR5. clear ERR4.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK4 AX4 MU WM) as [HK5 AX5].
  { constructor; [| constructor]. right; right. exists (ph, Hd, 104). split; [right; right; left; reflexivity| cbn; lia]. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. yshow HR4. clear -HR3 HR4 CEIL LO SPB. lia. }
  yshow HR4. pose proof (ystatics_munch _ _ _ YS4 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -HR4; lia| constructor])) as YS5. yhide HR4.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI5; rename my into m5 end.
  lazymatch goal with H : stk _ m5 _ _ |- _ => rename H into STK5 end.
  lazymatch goal with H : rw_cells _ m5 CFGP _ |- _ => rename H into CFG5 end.
  lazymatch goal with H : rw_cells _ m5 Hd _ |- _ => rename H into HH5 end.
  lazymatch goal with H : rw_cells _ m5 (Hd + 72) _ |- _ => rename H into HA5 end.
  lazymatch goal with H : rw_cells _ m5 (bv_unsigned sp + -96) _ |- _ => rename H into FR5 end.
  pose proof (LRT _ _ MU WM LR4) as LR5.
  pose proof (ry_pres_trans _ _ _ _ _ _ PRES4 (PRESH _ _ MU WM)) as PRES5.
  clear MU WM AX4 HK4 YS4 PRES4 LR4. try clear MI4; try clear STK4; try clear CFG4.
  eapply (YBA ((lid, L, 48) :: (mb_id mbl, mb_addr mbl, 32) :: (ph, Hd, 104) :: REST) (Hd + 72) lo B errv4 K);
    [ exact K0 | split; [lia | apply (mod8_off _ 72); [exact HRA | reflexivity]] | apply RYST_split; split; [exact HK5| exact YS5] | exact HA5
    | exists (ph, Hd, 104); split; [right; right; left; reflexivity| cbn; lia]
    | apply yroom_cons; apply yroom_cons; apply yroom_cons; eapply yroom_le; [exact YR| lia]
    | split; [exact AX5|]; split; [rewrite ESP; lia|]; split; [rewrite ESP; exact STK5|]; split; [exact CEIL|];
      split; [rewrite ESP; unfold RY_BUF_ALLOC_STACK, RY_WRAP_STACK; lia|]; split; [rewrite (ry_errno_lit tp TP); exact ERR5|]; split; [exact MI5| exact TP]
    | reflexivity | ].
  cbv beta. intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x m6 mo6 s6' pb B0 POST.
  destruct POST as ((MI6 & STK6 & (errv6 & ERR6) & AX6 & HP6) & HA6 & RES3).
  replace (ret_pc (Z_to_bv 64 81080)) with (Z_to_bv 64 81080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK6, HP6. rewrite (ry_errno_lit tp TP) in ERR6. unfold RERRNO in ERR6. apply ry_pres_nil in HP6.
  pose proof (ystatics_pres _ _ _ _ YS5 HP6) as YS6.
  pose proof (ypres_frame _ _ _ _ _ _ HP6 FR5 ltac:(lia)) as FR6. clear FR5.
  pose proof (ypres_frame _ _ _ _ _ _ HP6 CFG5 ltac:(lia)) as CFG6. clear CFG5.
  pose proof (ypres_block _ _ _ _ _ _ HP6 HH5 ltac:(eexists; split; [right; right; left; reflexivity| cbn; lia])) as HH6. clear HH5.
  pose proof (lexer_rep_pres_sub _ _ _ _ _ _ _ _ lid LR5 HP6 ltac:(intros bq Hbq; cbn [lexer_blocks buf_blocks lx_buf yb_data ybuf_zero] in Hbq;
                destruct Hbq as [Hbq|[Hbq|[]]]; [left; exact Hbq| right; left; exact Hbq])) as LR6. clear LR5.
  assert (PRES6 : ry_pres REST (bv_unsigned sp) [] m m6).
  { eapply ry_pres_trans; [exact PRES5|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP6| lia| intros b0 Hb0; right; right; right; exact Hb0]. }
  unfold alloc_cells in HA6. cbn [yc_malloc_w yc_realloc_w yc_free_w ryc] in HA6. unfold RY_MALLOC_W, RY_REALLOC_W, RY_FREE_W, wz in HA6.
  clear HP6 MI5 STK5 ERR5 AX5 HK5 YS5 PRES5 HA5.
  (* [comment removed for export] *)
  destruct RES3 as (A0' & B0NZ & BS6 & RY6). subst a0x. unfold wz. apply RYST_split in RY6. destruct RY6 as [HK6 _].
  destruct BS6 as (BC6 & _ & _ & _). unfold buf_cells, ybuf_zero in BC6. cbn [buf_state_code yb_state yb_len yb_used] in BC6. unfold wz in BC6.
  unfold SIZEOF_BUF in HK6.
  destruct (HK_blocks HK HKB _ _ _ _ HK6) as [RNG6 SEP6].
  pose proof (all_range_In _ _ RNG6 (or_introl eq_refl)) as DRG. unfold rblock_range, alloc_ceiling in DRG. cbn [blk_addr blk_size fst snd] in DRG.
  destruct DRG as (DRG0 & _ & _ & DRG3 & _). clear RNG6.
  cbn [all_sep sep_from] in SEP6. destruct SEP6 as ((_ & _ & SDH & SDR) & _). unfold bsep in SDH. cbn [blk_addr blk_size fst snd] in SDH.
  assert (UB0 : bv_unsigned (Z_to_bv 64 B0) = B0) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(Hd, Hd + 104)] m6) as MU. pose proof (wmono_refl usegs m6) as WM.
  yhide ERR6.
  rz_seg HKS HK6.
  step. step. step. step. step. lit_store. step. lit_store. step.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells _ ?mx Hd [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; C8 (Z_to_bv 64 128); ?c9] |- _ =>
    assert (HH7 : rw_cells usegs mx Hd [c0; c1; c2; c3; c4; c5; c6; c7; C4 (Z_to_bv 64 128); C4 (Z_to_bv 64 0); c9])
      by (pose proof (proj1 (proj1 H)) as WF; cbn [cells_wf cell_wf] in WF;
          eapply rw_cells_recast; [exact H| cbn [cells_wf cell_wf]; tauto| reflexivity| reflexivity]);
    clear H end.
  step. step. step. step.
  apply evt_done.
  (* [comment removed for export] *)
  yshow ERR6. pose proof (ERRV _ _ _ MU WM ERR6) as ERR7. clear ERR6.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK6 AX6 MU WM) as [HK7 AX7].
  { constructor; [| constructor]. right; right. exists (ph, Hd, 104). split; [right; right; right; left; reflexivity| cbn; lia]. }
  { constructor; [| constructor]. cbn. unfold RAUXV_CELL. yshow HR4. clear -HR3 HR4 CEIL LO SPB. lia. }
  yshow HR4. pose proof (ystatics_munch _ _ _ YS6 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -HR4; lia| constructor])) as YS7. yhide HR4.
  lazymatch goal with H : mem_inv _ ?mx |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?my _) _) _ => rename H into MI7; rename my into m7 end.
  lazymatch goal with H : stk _ m7 _ _ |- _ => rename H into STK7 end.
  lazymatch goal with H : rw_cells _ m7 CFGP _ |- _ => rename H into CFG7 end.
  lazymatch goal with H : rw_cells _ m7 (Hd + 72) _ |- _ => rename H into HA7 end.
  lazymatch goal with H : rw_cells _ m7 B0 _ |- _ => rename H into BC7 end.
  lazymatch goal with H : rw_cells _ m7 (bv_unsigned sp + -96) _ |- _ => rename H into FR7 end.
  pose proof (LRT _ _ MU WM LR6) as LR7.
  pose proof (ry_pres_trans _ _ _ _ _ _ PRES6 (PRESH _ _ MU WM)) as PRES7.
  clear MU WM AX6 HK6 YS6 PRES6 LR6. try clear MI6; try clear STK6; try clear CFG6.
  eapply YWRN; [exact K0 | exact HK7 | exact AX7 | rewrite ESP; lia | rewrite ESP; exact STK7 | exact CEIL
               | rewrite ESP; unfold RY_WRAP_STACK; lia | rewrite (ry_errno_lit tp TP); unfold RERRNO; exact ERR7
               | exact MI7 | exact TP | reflexivity | reflexivity | unfold NUSERc; clear; lia
               | cbn [length]; clear -YR; unfold yroom in YR; lia | ].
  cbv beta. intros t0y t1y t2y a0y a1y a2y a3y a4y a5y a6y a7y t3y t4y t5y t6y m8 mo8 s8' errv8 ps SB MI8 STK8 ERR8 AX8 HP8 A0' SRG HK8 NEWS.
  replace (ret_pc (Z_to_bv 64 81124)) with (Z_to_bv 64 81124) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  rewrite ESP in STK8, HP8. rewrite (ry_errno_lit tp TP) in ERR8. unfold RERRNO in ERR8.
  pose proof (ystatics_pres _ _ _ _ YS7 HP8) as YS8.
  pose proof (ypres_frame _ _ _ _ _ _ HP8 FR7 ltac:(lia)) as FR8. clear FR7.
  pose proof (ypres_frame _ _ _ _ _ _ HP8 CFG7 ltac:(lia)) as CFG8. clear CFG7.
  pose proof (ypres_block _ _ _ _ _ _ HP8 HH7 ltac:(eexists; split; [right; right; right; left; reflexivity| cbn; lia])) as HH8. clear HH7.
  pose proof (ypres_block _ _ _ _ _ _ HP8 HA7 ltac:(eexists; split; [right; right; right; left; reflexivity| cbn; lia])) as HA8. clear HA7.
  pose proof (ypres_block _ _ _ _ _ _ HP8 BC7 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as BC8. clear BC7.
  pose proof (lexer_rep_pres_sub _ _ _ _ _ _ _ _ lid LR7 HP8 ltac:(intros bq Hbq; cbn [lexer_blocks buf_blocks lx_buf yb_data ybuf_zero] in Hbq;
                destruct Hbq as [Hbq|[Hbq|[]]]; [right; left; exact Hbq| right; right; left; exact Hbq])) as LR8. clear LR7.
  assert (PRES8 : ry_pres REST (bv_unsigned sp) [] m m8).
  { eapply ry_pres_trans; [exact PRES7|]. apply ry_pres_of_rheap_pres. eapply rheap_pres_weaken; [exact HP8| lia| intros b0 Hb0; right; right; right; right; exact Hb0]. }
  clear HP8 MI7 STK7 ERR7 AX7 HK7 YS7 PRES7.
  (* [comment removed for export] *)
  subst a0y. unfold rblock_range, alloc_ceiling in SRG. unfold wz. destruct NEWS as [junks NEWS].
  destruct SRG as (SRG0 & _ & _ & SRG3 & SRG4). yhide SRG4.
  destruct (HK_blocks HK HKB _ _ _ _ HK8) as [_ SEP8]. cbn [all_sep sep_from] in SEP8.
  destruct SEP8 as ((SSD & SSL & SSB & SSH & SSR) & _). unfold bsep in SSD, SSL, SSB, SSH. cbn [blk_addr blk_size fst snd] in SSD, SSL, SSB, SSH.
  yhide SSL. yhide SSB.
  assert (USB : bv_unsigned (Z_to_bv 64 SB) = SB) by (apply unsigned_lit; lia).
  change (Z.to_nat 128) with 128%nat in NEWS.
  pose proof (munch_refl [(Hd, Hd + 104); (SB, SB + 128)] m8) as MU. pose proof (wmono_refl usegs m8) as WM.
  yhide ERR8.
  rz_seg HKS HK8.
  step. step. if_cases K5; zify_cond K5. 1:{ kill K5. } clear K5.
  step. rewrite (yzx32_small 0) by (clear; lia).
  step. zstep.
  step. lit_store.
  step. if_cases GF; zify_cond GF. 1:{ exfalso. pose proof (proj2 (Z.lxor_nonneg SB 18446744073709551615) ltac:(clear -SRG0; lia)). clear -GF H. lia. }
  step. try (replace (Z_to_bv 64 (SB + 0)) with (Z_to_bv 64 SB) by (f_equal; clear; lia)).
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells _ _ SB _ |- _ => rename H into NEWS1 end.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (rw_cells_CB_store_ok usegs mx SB _ _ 1%nat NEWS1 ltac:(clear; lia)) as SOK end.
  step.
  replace (wa (SB + Z.of_nat 0)) with (wa SB) by (f_equal; clear; lia).
  match type of NEWS1 with rw_cells _ ?mx _ _ =>
    pose proof (rw_cells_CB_prefix_write usegs mx SB _ _ (le1 (Z_to_bv 64 0)) NEWS1 ltac:(cbn; clear; lia)) as DCN end.
  clear NEWS1. store_done.
  step. step. step. step. step. step. step. step. step. step. step. step.
  apply evt_done.
  lazymatch goal with H : stk _ _ lo _ |- _ => rename H into STKf end.
  lazymatch goal with H : rw_cells _ _ (bv_unsigned sp + -96) _ |- _ => rename H into FRf end.
  release_frame FRf STKf (bv_unsigned sp).
  lazymatch goal with |- realizes_cfg _ _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into mf end.
  lazymatch goal with H : rw_cells _ mf Hd _ |- _ => rename H into HHf end.
  lazymatch goal with H : rw_cells _ mf (Hd + 72) _ |- _ => rename H into HAf end.
  lazymatch goal with H : rw_cells _ mf B0 _ |- _ => rename H into BCf end.
  lazymatch goal with H : rw_cells _ mf SB _ |- _ => rename H into SCf end.
  lazymatch goal with H : rw_cells _ mf CFGP _ |- _ => rename H into CFGf end.
  lazymatch goal with H : mem_inv _ mf |- _ => rename H into MIf end.
  yshow ERR8. yshow HR4. yshow SRG4.
  assert (ERRf : rw_cells usegs mf 218620 [C4 errv8]).
  { eapply (rw_cells_transport usegs); [exact ERR8| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn; clear -HR4 SRG4; lia]. }
  clear ERR8.
  destruct (yown_writes HK HKF _ _ _ _ _ _ B HK8 AX8 MU WM) as [HKf AXf].
  { constructor; [| constructor; [| constructor]].
    - right; right. exists (ph, Hd, 104). split; [right; right; right; right; left; reflexivity| cbn; clear; lia].
    - right; right. exists (ps, SB, 128). split; [left; reflexivity| cbn; clear; lia]. }
  { constructor; [| constructor; [| constructor]]; cbn; unfold RAUXV_CELL; [clear -HR3 HR4 CEIL LO SPB| clear -SRG3 SRG4 CEIL LO SPB]; lia. }
  pose proof (ystatics_munch _ _ _ YS8 MU WM ltac:(constructor; [cbn; unfold RY_CALLBACKS; clear -HR4; lia| constructor; [cbn; unfold RY_CALLBACKS; clear -SRG4; lia| constructor]])) as YSf.
  assert (PRESf : ry_pres REST (bv_unsigned sp) [] m mf).
  { eapply ry_pres_trans; [exact PRES8|]. eapply ryajl_pres_of_munch; [exact MU| exact WM|].
    intros a Ha Hc _. cbn. split; [| split; [| exact I]].
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [clear -Hc HR3 CEIL LO; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc HR4; lia|].
      pose proof (sep_from_In _ _ _ SEPH Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. clear -Hs Hr. lia.
    - destruct Hc as [Hc|[Hc|(b & Hb & Hr)]]; [clear -Hc SRG3 CEIL LO; lia| unfold ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in Hc; clear -Hc SRG4; lia|].
      pose proof (sep_from_In _ _ _ SSR Hb) as Hs. unfold bsep in Hs. cbn [blk_addr blk_size fst snd] in Hs. clear -Hs Hr. lia. }
  yhide HR4. yhide SRG4.
  yshow SLH. yshow SBH. yshow SSL. yshow SSB.
  assert (LRf : lexer_rep usegs mf L (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) mbl (Hd + 72)).
  { eapply lexer_rep_transport; [exact LR8| exact MU| exact WM| cbv [disjoint_from fst snd]; clear -SLH SSL; lia| cbv [disjoint_from fst snd]; clear -SBH SSB; lia|].
    cbn [lx_buf yb_data ybuf_zero]. intros X; exfalso; apply X; reflexivity. }
  clear SLH SBH SSL SSB MU WM LR8.
  (* [comment removed for export] *)
  eapply (ycb8_c8_in _ _ [_; _; _]) in HHf. cbn [app] in HHf.
  eapply (ycb4_c4_in _ _ [_; _; _; _; _]) in HHf. cbn [app] in HHf.
  eapply CONT with (h := mkHandle 0%nat blk0 (mkLexer 0 0 LE_ok ybuf_zero bb 0 0 1 1) None 0 0%nat ybuf_zero [ST_start] 128 (Some 0%nat))
                   (mh := mkMH ph Hd lid L mbl (mkMB pb B0 pb 0) ps SB CX).
  unfold yalloc_rpost. cbn [mh_addr mh_ctx].
  split; [| split; [exact CFGf| split; [reflexivity| split; [clear -HR0; lia| split; [reflexivity| split; [apply (yalloc_leaf_ok 1 1); exact HLX| split]]]]]].
  - split; [exact MIf|]. split; [exact STKf|]. split; [exists errv8; rewrite (ry_errno_lit tp TP); exact ERRf|]. split; [exact AXf| exact PRESf].
  - (* [comment removed for export] *)
    split; [| split; [exact LRf| split]].
    + split.
      * eexists _, _. split; [| exact I]. apply hand_cells_app. split; [| exact HAf].
        unfold hand_head_cells. cbn [yc_callbacks ryc mh_ctx mh_lexer mh_decbuf mh_stack mh_addr mb_addr h_bytesConsumed h_stack_size h_parseError]. unfold wz.
        exact HHf.
      * cbn [h_bytesConsumed h_stack_size h_stack_blk mh_stack]. replace (h_used _) with 1 by reflexivity.
        split; [clear; lia|]. split; [clear; lia|]. split; [clear; lia|]. split; [intros X; discriminate| intros X; exfalso; clear -X SRG0; lia].
    + split; [split; [unfold buf_cells, ybuf_zero; cbn [buf_state_code yb_state yb_len yb_used mb_addr mb_data]; unfold wz; exact BCf| split; [cbn; tauto| cbn; clear; lia]]
             | split; [cbn; exact I| cbn; constructor]].
    + unfold bs_rep. cbn [h_stack_blk h_stack h_stack_size mh_stack]. split; [clear -SRG0; lia|].
      replace (h_used _) with 1 by reflexivity. change (Z.to_nat 1) with 1%nat. change (Z.to_nat (128 - 1)) with 127%nat.
      change (zbytes (stack_bytes [ST_start])) with [Z_to_bv 8 0].
      exists (drop 1 junks). revert SCf. rewrite length_le1. change (le1 (Z_to_bv 64 0)) with [Z_to_bv 8 0]. change (128 - 1)%nat with 127%nat. intros SCf. exact SCf.
  - apply RYST_split. split; [| exact YSf]. eapply HKP; [exact HKf|].
    cbn [yblocks lexer_blocks buf_blocks bs_blocks lx_buf yb_data yb_len ybuf_zero h_stack_blk h_stack_size mh_id mh_addr mh_lid mh_lexer mh_lexbuf mh_decbuf mh_sid mh_stack mb_id mb_addr app].
    unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF. apply perm_yalloc.
Qed.
End S.
End RC__1.
