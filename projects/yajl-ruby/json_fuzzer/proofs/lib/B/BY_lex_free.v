(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BYajlRep BYajl_iface BY_rz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ALEXF_RET : Z := 0x82f14.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma alexf1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (L B lo : Z) (lc : list cell) (shbL : list byte),
  stk bsegs m1 lo (bv_unsigned sp) -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  rw_cells bsegs m1 L lc -> cells_size lc = 48%nat -> cell_at lc 16 = Some (C8 (Z_to_bv 64 B)) ->
  u8arr bsegs m1 (2147450880 + L / 8) shbL -> shbL = blk_shadow 48 ->
  rw_cells bsegs m1 677280 [C8 (Z_to_bv 64 714168)] -> rw_cells bsegs m1 714168 [C8 (Z_to_bv 64 2147450880)] ->
  0 < L -> L mod 16 = 0 -> L + 48 <= alloc_ceiling -> 17594333495296 <= L -> 0 <= B < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 -> pol P L (L + 48) -> pol P (2147450880 + L / 8) (2147450880 + L / 8 + 6) ->
  evtA bsegs P (fun ms' => exists (a1' : word) (junk : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 ALEXF_RET) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 L) (Z_to_bv 64 2147450880) (Z_to_bv 64 B) a1' a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_BUF_FREE) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -32, bv_unsigned sp)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -32) /\ rw_cells bsegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_LEX_FREE) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shbL. intros ST MI CEIL' LOQ SPH LC LCS LC4 LS LSeq G1 G2 L0 L16 LHI LSH BR PSTK PIMG PL PLS.
  unfold AY_LEX_FREE, AY_BUF_FREE, ALEXF_RET, pol in *.
  pose proof (blk_shadow_length 48 ltac:(lia)) as LSlen. rewrite <- LSeq in LSlen.
  assert (L8 : L mod 8 = 0) by lia.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  carve_frame 32%nat ST.
  stepA. apply (rw_cells_split_CB bsegs _ _ [] 32 _ [] [8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  stepA. stepA. stepA.                                (* [comment removed for export] *)
  ugd. stepA. zstepA. ugd.                            (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast LS (L + 16) 8.                          (* [comment removed for export] *)
  pose proof (rw_cells_read_at bsegs _ L lc 16%nat _ 8%nat (wa (L + 16)) LC LC4 eq_refl eq_refl) as RD.
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. eexists _, _, _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| exact FR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma alexf2_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0o s1o : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (L AF lo SQ HB HN : Z) (lc : list cell) (junk shbL shbH : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo <= SQ -> SQ + 32 <= 2^47 ->
  rw_cells bsegs m1 L lc -> cells_size lc = 48%nat -> cell_at lc 40 = Some (C8 (Z_to_bv 64 AF)) ->
  u8arr bsegs m1 (2147450880 + L / 8) shbL -> shbL = blk_shadow 48 ->
  rw_cells bsegs m1 SQ [CB 8 junk; C8 s1o; C8 s0o; C8 rav] ->
  rw_cells bsegs m1 AF [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + HB / 8) shbH -> shbH = blk_shadow HN -> HB <= AF -> AF + 32 <= HB + 8 * (HN / 8) -> AF mod 8 = 0 ->
  0 < HB -> HB mod 16 = 0 -> HB + HN <= alloc_ceiling -> 17594333495296 <= HB ->
  0 < L -> L mod 16 = 0 -> L + 48 <= alloc_ceiling -> 17594333495296 <= L ->
  pol P lo (SQ + 32) -> pol P L (L + 48) -> pol P (2147450880 + L / 8) (2147450880 + L / 8 + 6) ->
  pol P AF (AF + 32) -> pol P (2147450880 + HB / 8) (2147450880 + HB / 8 + (HN + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (a2' : word),
      ms' = MS (mkR rav (Z_to_bv 64 (SQ + 32)) gp tp t0 (Z_to_bv 64 AY_FREE_W) t2 s0o s1o (Z_to_bv 64 0) (Z_to_bv 64 L) a2' a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FREE_W) fc None m1 (seg_rom bsegs)
      /\ stk bsegs m1 lo (SQ + 32))
    (MS (mkR (Z_to_bv 64 ALEXF_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 L) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ALEXF_RET) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shbH. intros ST MI CEIL' LOQ SQH LC LCS LC9 LS LSeq FR YAF HBS HBSeq HB1 HB2 AF8 HB0 HB16 HBHI HBS2 L0 L16 LHI LSH PSTK PL PLS PHB PHBS.
  unfold ALEXF_RET, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, pol in *.
  pose proof (blk_shadow_length 48 ltac:(lia)) as LSlen. rewrite <- LSeq in LSlen.
  pose proof (blk_shadow_length HN ltac:(lia)) as HBSlen. rewrite <- HBSeq in HBSlen.
  assert (L8 : L mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  zstepA. shadow_fast LS (L + 40) 8.                  (* [comment removed for export] *)
  pose proof (rw_cells_read_at bsegs _ L lc 40%nat _ 8%nat (wa (L + 40)) LC LC9 eq_refl eq_refl) as RD.
  zstepA.                                             (* [comment removed for export] *)
  ugd. zstepA. ugd.                                   (* [comment removed for export] *)
  zstepA. shadow_fast HBS (AF + 16) 8.                (* [comment removed for export] *)
  zstepA. shadow_fast HBS (AF + 24) 8.                (* [comment removed for export] *)
  zstepA. zstepA. stepA. stepA.                       (* [comment removed for export] *)
  do 4 stepA.                                         (* [comment removed for export] *)
  release_frame FR ST (SQ + 32).
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. eexists _. split; [| assumption].
  reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma agree_below : forall W m m' lo, munch W m m' -> wmono bsegs m m' -> Forall (fun iv => lo <= fst iv) W ->
  agree_on bsegs (fun a => a < lo) m m'.
Proof. aceil.
  intros W m m' lo MU WM FW a Ha Hlo. split; [| apply WM]. apply MU. rewrite wa_unsigned by lia.
  clear -CEILB FW Hlo. induction W as [|[u v] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *. split; [lia| apply IH; assumption].
Qed.

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
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis BFREE : aybuf_free_stmt Y.
Hypothesis WFREE : aywrap_free_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_bf : In 0x82f14 URA.                                            (* [comment removed for export] *)
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Theorem aylex_free_proof : aylex_free_stmt Y.
Proof. aceil.
  unfold aylex_free_stmt. intros LF REST L AF mbl lx lo RR K. intros until s. intros (LP & LA8 & AFP & AFA8 & MBP & MBA8) K0 AY LR YAF AFOK LS BS FP EA CRED RR0 NBIG UA CONT. subst a0.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA). ay_statics_open STA.
  destruct AFOK as (hb & HBI & HB1 & HB2 & AF8 & HBS & HBHI).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  assert (HBIN' : In hb (mkABlock L SIZEOF_LEXER :: abl (buf_blocks mbl (lx_buf lx)) ++ REST)) by (right; apply in_or_app; right; exact HBI).
  pose proof (RNG _ (or_introl eq_refl)) as LRG. pose proof (RNG _ HBIN') as HBR.
  unfold ablock_range, ACONSTS in LRG, HBR. cbn [c_img_hi ab_addr ab_size] in LRG, HBR.
  pose proof HBHI as HBSI. unfold oshw_hi, A_SB in HBSI.
  assert (HBS2 : 17594333495296 <= ab_addr hb) by (revert HBSI CEILB; clear; intros H CEILB; cbn in H; lia). clear HBSI.
  pose proof (BSMALL _ _ _ _ _ _ AHK0 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as LSHI. cbn [ab_addr] in LSHI. unfold oshw_hi, A_SB, amem in LSHI.
  assert (LSH2 : 17594333495296 <= L) by (revert LSHI CEILB; clear; intros H CEILB; cbn in H; lia). clear LSHI.
  assert (DBND : forall b, In b (abl (buf_blocks mbl (lx_buf lx))) -> ab_addr b + ab_size b <= alloc_ceiling).
  { intros b Hb. pose proof (RNG b (or_intror (in_or_app _ _ _ (or_introl Hb)))) as X. unfold ablock_range in X. lia. }
  pose proof LR as LR0. destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & BR). unfold lexer_cells in LC.
  unfold AY_LEX_FREE_STACK, AY_BUF_FREE_STACK, AMALLOC_STACK, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  aceil.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold wz in YAF.
  pose proof LS as LS0. destruct LS as (L8 & _ & LSu). destruct HBS as (HB8 & HBn & HBSu). unfold A_SB in LSu, HBSu.
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  assert (Q1 : 0 <= ab_addr (mkABlock L 48)) by (cbn [ab_addr]; lia).
  assert (Q2 : 0 <= oshw_lo (ab_addr (mkABlock L 48))) by (cbn [ab_addr]; unfold oshw_lo, A_SB; lia).
  assert (Q3 : oshw_hi (ab_addr (mkABlock L 48)) (ab_size (mkABlock L 48)) < 2^64) by (cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem; lia).
  assert (Q4 : ab_addr (mkABlock L 48) + ab_size (mkABlock L 48) < 2^64) by (cbn [ab_addr ab_size]; lia).
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock L 48) (or_introl eq_refl) Q1 Q2 Q3 Q4) as [PL PLS]. clear Q1 Q2 Q3 Q4.
  cbn [ab_addr ab_size] in PL, PLS. unfold oshw_lo, oshw_hi, A_SB, amem in PL, PLS.
  eapply evtA_cut.
  { eapply (alexf1_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L (mb_addr mbl) lo _ _);
      [ exact ST | exact MI | lia | lia | lia | exact LC | reflexivity | reflexivity | exact LSu | reflexivity | exact G1 | exact G2
      | lia | lia | lia | lia | | exact PSTK | exact PIMG | exact PL | intros a k Ha Hk; apply PLS; lia ].
    destruct BR as ((BC & _) & _). pose proof (rw_cells_bound _ _ _ _ BC) as X. unfold buf_cells in X. cbn [cells_size csize Nat.add length] in X. lia. }
  cbv beta. intros ms1 (a1' & junk & m1 & -> & MU & WM & MI1 & ST1 & FR1).
  apply evtA_done. intros mo1 Hag1 HLI1 Hh1.
  destruct (BACK mo1 Hag1 HLI1) as [AHKb R1].
  assert (AHK1 : y_AHK Y s (mkABlock L 48 :: abl (buf_blocks mbl (lx_buf lx)) ++ REST) LF m1 mo1).
  { eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  clear AHKb.
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (AG1 : agree_on bsegs (fun a => a < lo) m m1) by (eapply agree_below; [exact MU| exact WM| constructor; [cbn [fst]; lia| constructor]]).
  pose proof (DBND (mkABlock (mb_addr mbl) 32) ltac:(unfold buf_blocks, abl; left; reflexivity)) as BRG. cbn [ab_addr ab_size] in BRG.
  assert (BR1 : abuf_rep m1 mbl (lx_buf lx) AF).
  { eapply buf_rep_agree; [exact AG1| exact BR| cbn; intros a Ha; unfold SIZEOF_BUF in Ha; lia|].
    intros HD a Ha. cbn. unfold buf_blocks, abl in DBND. destruct (yb_data (lx_buf lx)); [| exfalso; apply HD; reflexivity].
    pose proof (DBND (mkABlock (mb_data mbl) (yb_len (lx_buf lx))) ltac:(right; left; reflexivity)) as X. cbn [ab_addr ab_size] in X. lia. }
  eapply (rw_cells_transport bsegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (rw_cells_transport bsegs) in LC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; right; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc]. }
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)) by (intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia).
  clear LINK BACK PSTK PIMG PL PLS LSu.
  (* [comment removed for export] *)
  assert (AHK1' : y_AHK Y s (abl (buf_blocks mbl (lx_buf lx)) ++ (mkABlock L 48 :: REST)) LF m1 mo1).
  { eapply PERMY; [exact AHK1| apply Permutation_middle| apply Permutation_refl]. }
  name_sp sp (-32)%Z. rewrite <- Hsp in ST1.
  eapply (BFREE LF (mkABlock L 48 :: REST) mbl (lx_buf lx) AF lo (y_free_cost Y + RR));
    [ split; [exact MBP|]; split; [exact MBA8|]; split; [exact AFP| exact AFA8]     (* [comment removed for export] *)
    | exact K0
    | apply AYST_split; split; [exact AHK1'| exact YS1]
    | exact BR1
    | exact YAF
    | exists hb; split; [right; exact HBI|]; split; [exact HB1|]; split; [exact HB2|]; split; [exact AF8|]; split; [| exact HBHI];
      split; [exact HB8|]; split; [exact HBn|]; eapply (u8arr_transport bsegs); [exact HBSu| exact MU| exact WM| cbv [disjoint_from fst snd]; unfold A_SB; rewrite (blk_shadow_length (ab_size hb)) by lia; lia]
    | destruct BS as (X1 & X2 & X3); split; [exact X1|]; split; [exact X2|]; eapply (u8arr_transport bsegs); [exact X3| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; unfold A_SB; pose proof (rw_cells_bound _ _ _ _ (proj1 (proj1 BR1))); lia]
    | unfold ayframe_pre, AY_BUF_FREE_STACK, AMALLOC_STACK; aceil;
      split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
      split; [exact MI1|]; split; [exact TP| exact FRM]
    | reflexivity
    | lia
    | pose proof YFREE as YF0; unfold yacct_free_stmt in YF0; lia
    | change (nbig ({| ab_addr := L; ab_size := 48 |} :: REST)) with (nbig REST); exact NBIG
    | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold ALEXF_RET; rewrite unsigned_lit by lia; exact URA_bf]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1'' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 (SO2 & R2 & CRED2 & (MI2 & ST2 & FRM2 & WM2 & PRES2) & YAF2 & AY2).
  unname_sp.
  apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. clear FR1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES2 LC ltac:(eexists; split; [left; reflexivity| cbn; lia])) as LC2. clear LC.
  pose proof (BSHY _ _ _ _ _ (mkABlock L 48) AHK2 (or_introl eq_refl) ltac:(cbn; lia)) as [LS2 _]. cbn [ab_addr ab_size] in LS2. destruct LS2 as (_ & _ & LSu2). unfold A_SB in LSu2.
  pose proof (BSHY _ _ _ _ _ hb AHK2 (or_intror HBI) ltac:(lia)) as [HBS2' _]. destruct HBS2' as (_ & _ & HBSu2). unfold A_SB in HBSu2.
  assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
  assert (AGREE2 : forall a, bv_unsigned sp <= a < 2^47 -> m2 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE1 a Ha). destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  (* [comment removed for export] *)
  unfold ALEXF_RET. arz_seg KIPY AHK2. ret_pc_lit.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock L 48) (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PL PLS].
  pose proof (aypol_opol_sub Y _ LF _ _ LINK hb AF 32 (or_intror HBI) HB1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [PHB _].
  pose proof (aypol_opol_block Y _ LF _ _ LINK hb (or_intror HBI) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [_ PHBS].
  cbn [ab_addr ab_size] in PL, PLS. unfold oshw_lo, oshw_hi, A_SB, amem in PL, PLS, PHB, PHBS.
  pose proof (SEP _ _ (or_introl eq_refl) HBIN' (nd_head_ne _ _ _ ND (or_intror (in_or_app _ _ _ (or_intror HBI))))) as SLH. cbn [ab_addr ab_size] in SLH.
  eapply evtA_cut.
  { eapply (alexf2_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L AF lo (bv_unsigned sp + -32) (ab_addr hb) (ab_size hb) _ junk _ _);
      [ exact ST2 | exact MI2 | lia | lia | lia | exact LC2 | reflexivity | reflexivity | exact LSu2 | reflexivity | exact FR2 | exact YAF2 | exact HBSu2 | reflexivity
      | lia | lia | exact AF8 | lia | lia | lia | lia | lia | lia | lia | lia
      | intros a k Ha Hk; apply PSTK; lia | exact PL | intros a k Ha Hk; apply PLS; lia | exact PHB | exact PHBS ]. }
  cbv beta. intros ms3 (a2x & -> & ST3).
  apply evtA_done. intros mo3 Hag3 HLI3 Hh3.
  destruct (BACK mo3 Hag3 HLI3) as [AHK3 R3].
  replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
  clear LINK BACK PSTK PL PLS PHB PHBS.
  (* [comment removed for export] *)
  eapply (WFREE L 48 _ LF lo RR);
    [ exact K0
    | apply AYST_split; split; [exact AHK3| exact YS2]
    | left; reflexivity
    | reflexivity
    | exact CRED2
    | exact RR0
    | change (nbig ({| ab_addr := L; ab_size := 48 |} :: REST)) with (nbig REST); unfold AY_NBIG_REST in NBIG; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
      split; [exact ST3|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact MI2|]; split; [exact TP| exact FRM2]
    | eapply UFRAME; [exact AGREE2| exact UA]
    | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1x a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F3 fc3 m3 mo4 sa3 (MI3 & ST4 & FRM3 & WM3 & PRES3) SO3 R4 CRED3 AY3.
  rewrite ab_remove_head in PRES3, AY3.
  eapply CONT. unfold aylex_free_rpost.
  split; [rewrite SO3; exact SO2|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3| exact R4]|].
  split; [lia|].
  split.
  { split; [exact MI3|]. split; [exact ST4|]. split; [exact FRM3|]. split.
    - exact I.
    - eapply ay_pres_trans; [exact PRES2w| exact PRES3]. }
  split; [eapply aypres_block; [exact PRES3| exact YAF2| exists hb; split; [exact HBI| cbn; lia]]|].
  exact AY3.
Qed.
End W.
End RC__1.
