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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_region_is_poisoned AI_asan_memcpy1 AI_asan_memcpy AYajlRep AYajl_iface AY_rz AY_buf_append1 AY_buf_append2 AY_buf_append2g AY_buf_append3 AY_buf_append3g AY_buf_append4 AY_buf_append4g AY_buf_append5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
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
Hypothesis WMAL : aywrap_malloc_stmt Y.
Hypothesis WFREEN : aywrap_free_null_stmt Y.
Hypothesis WREA : aywrap_realloc_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_mal : In 0x86ac4 URA.
Hypothesis URA_rea : In 0x86ba4 URA.
Hypothesis URA_err2 : In 0x86d08 URA.
Hypothesis URA_err3 : In 0x86d98 URA.
Hypothesis ICPG : forall s LB LF m mo, y_AHK Y s LB LF m mo -> icp_globals asegs m A_SB.
Hypothesis ICPB : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB ->
    ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    exists ws, shadow_window asegs m A_SB A n ws /\ range_clean A_SB A n ws
               /\ shw_hi A_SB A n <= 0x10007fff8000 /\ amem (ab_addr b) (ab_size b).   (* [comment removed for export] *)
Hypothesis ICPR : forall s LB LF m mo b A n, y_AHK Y s LB LF m mo -> In b LB -> ab_addr b <= A -> 1 <= n -> A + n <= ab_addr b + ab_size b ->
    pages_budgeted (y_aS Y s) (shw_lo A_SB A) (shw_hi A_SB A n).
Hypothesis YPHI_shape : forall st len u1 u2 d bs1 bs2, y_phi_buf Y (mkBuf st len u1 d bs1) = y_phi_buf Y (mkBuf st len u2 d bs2).
Hypothesis YPHI_grow : forall len used want (d : yptr) bs,
    0 <= used < len -> len < 2^31 -> 0 < want -> used + want < 2^28 -> ens_need_loop ENS_FUEL want len used <> len ->
    y_acharge Y (ens_need_loop ENS_FUEL want len used) + y_free_cost Y + y_phi_buf Y (mkBuf BS_ok (ens_need_loop ENS_FUEL want len used) used (Some d) bs)
      <= y_phi_buf Y (mkBuf BS_ok len used (Some d) bs).
Hypothesis YPHI_err : forall len u (d : yptr) bs, y_phi_buf Y (mkBuf BS_overflow 0 0 None []) <= y_phi_buf Y (mkBuf BS_ok len u (Some d) bs).
Hypothesis YPHI_first : forall (d : yptr) used bs, y_acharge Y YAJL_BUF_INIT_SIZE + y_phi_buf Y (mkBuf BS_ok YAJL_BUF_INIT_SIZE used (Some d) bs) <= y_phi_buf Y (mkBuf BS_ok 0 used None bs).

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

Theorem aybuf_append_proof : aybuf_append_stmt Y.
Proof. aceil.
  unfold aybuf_append_stmt. intros LF REST mb b AF S src lo RR K. intros until s.
  intros K0 AY BR BI YAF AFOK BSH DSH TB SRCF SNZ SBND U30 YSR YWIN FP EA0 EA1 EA2 CRED RR0 NBIG UA CONT. subst a0 a1 a2.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  pose proof (aapp_ret Y KIPY FRAMEY RRT LF REST mb b AF S src lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s CONT CEIL LO (Z.lt_le_incl _ _ SPH)) as J_ret.
  assert (HBIN8 : exists hb, In hb REST /\ ab_addr hb <= AF /\ AF + 32 <= ab_addr hb + 8 * (ab_size hb / 8) /\ AF mod 8 = 0 /\ oshw_hi 0 (2^47) <= ab_addr hb).
  { destruct AFOK as (hb & H1 & H2 & H3 & H4 & _ & H6). exists hb. auto 10. }
  destruct BR as ((BC & DZ & RL & RU) & BD & FB).
  pose proof (aapp_size Y KIPY FRAMEY BLKY BSHY BSMALL LAYY PERMY RRT NONNEG WREA URA UTRIV URA_rea ICPG ICPB ICPR YPHI_shape YPHI_grow
                LF REST mb b AF S src lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s CONT K0 RR0 CEIL LO (Z.lt_le_incl _ _ SPH) SP16 TP HBIN8 NBIG SRCF SNZ YSR YWIN FB) as J_size.
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA). ay_statics_open STA.
  destruct AFOK as (hb & HBI & HB1 & HB2 & AF8 & HBS & HBHI).
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  assert (HBIN' : In hb (abl (buf_blocks mb b) ++ REST)) by (apply in_or_app; right; exact HBI).
  pose proof (RNG _ (or_introl eq_refl)) as BRNG. pose proof (RNG _ HBIN') as HBR.
  unfold ablock_range, ACONSTS in BRNG, HBR. cbn [c_img_hi ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in BRNG, HBR. unfold SIZEOF_BUF in BRNG, HBR.
  pose proof HBHI as HBSI. unfold oshw_hi, A_SB in HBSI.
  assert (HBS2 : 17594333495296 <= ab_addr hb) by (revert HBSI CEILB; clear; intros H CEILB; cbn in H; lia). clear HBSI.
  pose proof (BSMALL _ _ _ _ _ _ AHK0 (or_introl eq_refl) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as BSHI. cbn [ab_addr abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in BSHI. unfold SIZEOF_BUF in BSHI. unfold oshw_hi, A_SB, amem in BSHI.
  assert (BSH2 : 17594333495296 <= mb_addr mb) by (revert BSHI CEILB; clear; intros H CEILB; cbn in H; lia). clear BSHI.
  pose proof (SEP _ _ (or_introl eq_refl) HBIN' (nd_head_ne _ _ _ ND (in_or_app _ _ _ (or_intror HBI)))) as SBH. cbn [ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in SBH. unfold SIZEOF_BUF in SBH.
  unfold buf_cells in BC. unfold AY_BUF_APPEND_STACK, AMALLOC_STACK, SIZEOF_BUF, wz in *.
  aceil.
  unfold alloc_cells in YAF. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc] in YAF. unfold wz in YAF.
  destruct BSH as (B8 & _ & BSHu). destruct HBS as (HB8 & HBn & HBSu). unfold A_SB in BSHu, HBSu.
  pose proof (zbytes_length src) as ZL. pose proof (zbytes_length (yb_bytes b)) as ZLB. pose proof (bytes_at_bound _ _ _ _ TB) as TBB.
  destruct BI as (I1 & I2 & I3 & I4 & I5 & I6).
  assert (NZ0 : 0 <= zlength src) by (unfold zlength; lia).
  assert (STR : 0 <= buf_state_code (yb_state b) < 2^31) by (destruct (yb_state b); cbn; lia).
  assert (DR64 : 0 <= mb_data mb < 2^64).
  { destruct (yb_data b) eqn:HD.
    - unfold buf_blocks, abl in RNG. rewrite HD in RNG. pose proof (RNG _ (or_intror (or_introl eq_refl))) as X. unfold ablock_range in X; aceil. cbn in X. lia.
    - assert (mb_data mb = 0) by (apply DZ; reflexivity). lia. }
  (* [comment removed for export] *)
  assert (SSEP : 0 < zlength src -> (S + zlength src <= lo \/ S + zlength src <= 0x31000) /\ (S + zlength src <= mb_addr mb \/ mb_addr mb + 32 <= S)).
  { intros NPOS. destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & F1' & F2)|Y4]]]; [| lia| | lia].
    - assert (HBT' : In bt (abl (buf_blocks mb b) ++ REST)) by (apply in_or_app; right; exact HBT).
      pose proof (RNG _ HBT') as TR. unfold ablock_range in TR; aceil.
      pose proof (SEP _ _ (or_introl eq_refl) HBT' (nd_head_ne _ _ _ ND (in_or_app _ _ _ (or_intror HBT)))) as X.
      cbn [ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in X. unfold SIZEOF_BUF in X. clear -CEILB TR X T1 T2 CEIL. lia.
    - destruct (proj1 (LAYY _ _ _ _ _ AHK0) f Hf) as (L1 & L2 & L3 & L4 & L5). aceil.
      destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK0)) f _ Hf (or_introl eq_refl)) as [X1 _].
      cbn [ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in X1. unfold SIZEOF_BUF in X1. clear -CEILB L2 X1 F1' F2 CEIL. lia. }
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  assert (Q1 : 0 <= ab_addr (mkABlock (mb_addr mb) 32)) by (cbn [ab_addr]; lia).
  assert (Q2 : 0 <= oshw_lo (ab_addr (mkABlock (mb_addr mb) 32))) by (cbn [ab_addr]; unfold oshw_lo, A_SB; lia).
  assert (Q3 : oshw_hi (ab_addr (mkABlock (mb_addr mb) 32)) (ab_size (mkABlock (mb_addr mb) 32)) < 2^64) by (cbn [ab_addr ab_size]; unfold oshw_hi, A_SB, amem; lia).
  assert (Q4 : ab_addr (mkABlock (mb_addr mb) 32) + ab_size (mkABlock (mb_addr mb) 32) < 2^64) by (cbn [ab_addr ab_size]; lia).
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock (mb_addr mb) 32) ltac:(left; unfold buf_blocks, abl; cbn [map blk_addr blk_size fst snd]; unfold SIZEOF_BUF; reflexivity) Q1 Q2 Q3 Q4) as [PB PBS]. clear Q1 Q2 Q3 Q4.
  pose proof (aypol_opol_sub Y _ LF _ _ LINK hb AF 32 HBIN' HB1 ltac:(Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [PHB _].
  pose proof (aypol_opol_block Y _ LF _ _ LINK hb HBIN' ltac:(lia) ltac:(unfold oshw_lo, A_SB; lia) ltac:(unfold oshw_hi, A_SB, amem; lia) ltac:(lia)) as [_ PHBS].
  cbn [ab_addr ab_size abl buf_blocks map blk_addr blk_size fst snd SIZEOF_BUF] in PB, PBS. unfold SIZEOF_BUF in PB, PBS. unfold oshw_lo, oshw_hi, A_SB, amem in PB, PBS, PHB, PHBS.
  eapply evtA_cut.
  { eapply (amain1_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              (mb_addr mb) (mb_data mb) S (zlength src) AF (buf_state_code (yb_state b)) (yb_len b) (yb_used b) lo _ _ (ab_addr hb) (ab_size hb));
      [ exact ST | exact MI | lia | lia | lia | exact BC | exact BSHu | reflexivity | exact G1 | exact G2 | exact YAF | exact HBSu | reflexivity
      | lia | lia | exact AF8 | lia | lia | lia | lia | clear -CEILB SBH; lia | lia | lia | lia | lia
      | exact STR | lia | lia | exact DR64 | lia | lia
      | exact PSTK | exact PIMG | exact PB | exact PBS | exact PHB | exact PHBS ]. }
  cbv beta. intros ms1 (junk & m1 & FR1 & ST1 & MU & WM & MI1 & CASES). unfold aframe13 in FR1.
  (* [comment removed for export] *)
  assert (COMMON : forall mo1, magree mo mo1 -> LI (y_aS Y s) (y_aN Y s) (y_aEB Y s) mo1 ->
            y_AHK Y s (abl (buf_blocks mb b) ++ REST) LF m1 mo1 /\ y_ayR Y s mo s mo1 /\ aystatics m1 /\ ay_pres REST LF (bv_unsigned sp) [] m m1).
  { intros mo1 Hag1 HLI1. destruct (BACK mo1 Hag1 HLI1) as [AHKb Rb]. split; [| split; [exact Rb| split]].
    - eapply FRAMEY; [exact AHKb| exact MU| exact WM|].
      constructor; [left; cbn [fst snd]; aceil; lia|].
      constructor; [| constructor]. right; left. exists (mkABlock (mb_addr mb) 32).
      split; [left; unfold buf_blocks, abl; cbn [map blk_addr blk_size fst snd]; unfold SIZEOF_BUF; reflexivity| cbn [ab_addr ab_size fst snd]; lia].
    - eapply aystatics_munch; [exact YS| exact MU| exact WM|]. constructor; [cbn [fst snd]; lia| constructor; [cbn [fst snd]; lia| constructor]].
    - eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _. apply outside_cons; [| apply outside_cons; [| exact I]].
      + eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc].
      + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mb_addr mb) 32));
          [exact AHK0| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
        intros b0 Hb0. split; [apply in_or_app; right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ ND (in_or_app _ _ _ (or_intror Hb0)) (eq_sym E)). }
  eapply (rw_cells_transport asegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  eapply (u8arr_transport asegs) in BSHu; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; lia].
  assert (TB1 : bytes_at asegs m1 S (zbytes src)).
  { destruct src as [|c src']. { destruct TB as (X0 & X1 & _). split; [exact X0|]. split; [exact X1|]. intros i Hi. cbn in Hi. lia. }
    destruct (SSEP ltac:(unfold zlength; cbn [length]; lia)) as [SSLO SSEPB].
    eapply (bytes_at_transport asegs); [exact TB| exact MU|]. cbv [disjoint_from fst snd]. rewrite ZL. unfold zlength in *. cbn [length] in *. lia. }
  clear TB LINK BACK PSTK PIMG PB PBS PHB PHBS.
  destruct CASES as [(STNZ & BC1 & x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->)
                    |[(STZ & DNZ & NZ & BC1 & x1 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x18 & x19 & x20 & x21 & x22 & x23 & x24 & x25 & x26 & x27 & x28 & x29 & x30 & x31 & ->)
                    |[(STZ & DNZ & NZ & BC1 & x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->)
                    |(STZ & DZ0 & BC1 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & ->)]]].
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (COMMON mo1 Hag1 HLI1) as (AHK1 & R1 & YS1 & PRES1).
    assert (HS : yb_state b <> BS_ok) by (intros E; rewrite E in STNZ; apply STNZ; reflexivity).
    pose proof (I6 HS) as HD.
    eapply J_ret with (sv := []) (b' := b) (mb' := mb) (LK := []) (junk := junk).
    + rewrite app_nil_l. exact AHK1.
    + exact YS1.
    + exact FR1.
    + exact ST1.
    + exact MI1.
    + exact FRM.
    + exact I.
    + exact PRES1.
    + unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF.
    + reflexivity.
    + exact R1.
    + exact CRED.
    + apply app_leaf_notok. exact HS.
    + split; [| split; [unfold buf_data; rewrite HD; exact I| exact FB]]. split; [unfold buf_cells, wz; exact BC1| split; [exact DZ| lia]].
    + split; reflexivity.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [exact B8|]. split; [lia|]. exact BSHu.
    + rewrite HD. intros X. exfalso. apply X. reflexivity.
    + intros X. exfalso. exact (X eq_refl).
    + intros X. exfalso. exact (X eq_refl).
    + reflexivity.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (COMMON mo1 Hag1 HLI1) as (AHK1 & R1 & YS1 & PRES1).
    assert (HS : yb_state b = BS_ok) by (destruct (yb_state b); [reflexivity| cbn in STZ; lia| cbn in STZ; lia]).
    destruct (yb_data b) as [d1|] eqn:HD. 2:{ exfalso. apply DNZ, DZ. reflexivity. }
    assert (SRC0 : src = []) by (destruct src; [reflexivity| unfold zlength in NZ; cbn in NZ; lia]).
    unfold buf_blocks, abl in AHK1, RNG, SEP, ND. rewrite HD in AHK1, RNG, SEP, ND. cbn [map app blk_addr blk_size fst snd] in AHK1, RNG, SEP. cbn [app blk_addr blk_size fst snd] in ND. unfold SIZEOF_BUF in AHK1, RNG, SEP, ND.
    pose proof (SEP _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND (or_introl eq_refl))) as SBD. cbn [ab_addr ab_size] in SBD. unfold SIZEOF_BUF in SBD.
    pose proof (RNG _ (or_intror (or_introl eq_refl))) as DR. unfold ablock_range in DR; aceil. cbn [ab_addr ab_size] in DR.
    unfold buf_data in BD. rewrite HD in BD. destruct BD as (UL & junkd & DC).
    eapply (rw_cells_transport asegs) in DC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
    pose proof (BSHY _ _ _ _ _ (mkABlock (mb_data mb) (yb_len b)) AHK1 (or_intror (or_introl eq_refl)) ltac:(cbn; lia)) as [DSH1 DSHI]. cbn [ab_addr ab_size] in DSH1, DSHI.
    eapply J_ret with (sv := []) (b' := b) (mb' := mb) (LK := []) (junk := junk).
    + unfold buf_blocks, abl. rewrite HD. cbn [map app blk_addr blk_size fst snd]. exact AHK1.
    + exact YS1.
    + exact FR1.
    + exact ST1.
    + exact MI1.
    + exact FRM.
    + exact I.
    + exact PRES1.
    + unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF.
    + reflexivity.
    + exact R1.
    + exact CRED.
    + rewrite SRC0. eapply app_leaf_inl; [exact HS| unfold ens_first; rewrite HD; apply yl_ret|].
      apply (yleaf_bind _ _ b); [unfold ens_tail; cbn; apply yl_ret|]. unfold app_tail. rewrite HS. cbn. apply yl_ret.
    + split; [| split; [unfold buf_data; rewrite HD; split; [exact UL| exists junkd; exact DC]| exact FB]].
      split; [unfold buf_cells, wz; exact BC1| split; [rewrite HD; exact DZ| lia]].
    + split; reflexivity.
    + unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. split; [exact B8|]. split; [lia|]. exact BSHu.
    + intros _. split; [exact DSH1| exact DSHI].
    + intros X. exfalso. exact (X eq_refl).
    + intros X. exfalso. exact (X eq_refl).
    + reflexivity.   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (COMMON mo1 Hag1 HLI1) as (AHK1 & R1 & YS1 & PRES1).
    assert (HS : yb_state b = BS_ok) by (destruct (yb_state b); [reflexivity| cbn in STZ; lia| cbn in STZ; lia]).
    destruct (yb_data b) as [d1|] eqn:HD. 2:{ exfalso. apply DNZ, DZ. reflexivity. }
    unfold buf_data in BD. rewrite HD in BD. destruct BD as (UL & junkd & DC).
    eapply (rw_cells_transport asegs) in DC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]].
    2:{ unfold buf_blocks, abl in RNG, SEP, ND. rewrite HD in RNG, SEP, ND. cbn [map app blk_addr blk_size fst snd] in RNG, SEP. cbn [app blk_addr blk_size fst snd] in ND.
        pose proof (SEP _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND (or_introl eq_refl))) as SBD. cbn [ab_addr ab_size] in SBD. unfold SIZEOF_BUF in SBD.
        pose proof (RNG _ (or_intror (or_introl eq_refl))) as X. unfold ablock_range in X; aceil. cbn [ab_addr ab_size] in X. lia. }
    eapply (J_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo1 s junk junkd (yb_len b) (yb_used b) d1 (mb_did mb) (mb_data mb)
              ((mb_addr mb + 16) / 8 + 2147450880) (mb_addr mb / 8 + 2147450880)).
    + unfold buf_blocks, abl in AHK1 |- *. rewrite HD in AHK1. cbn [map app blk_addr blk_size fst snd yb_data yb_len mb_id mb_addr mb_did mb_data] in AHK1 |- *. exact AHK1.
    + exact YS1.
    + exact FR1.
    + exact ST1.
    + exact MI1.
    + exact FRM.
    + exact I.
    + exact PRES1.
    + unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF.
    + rewrite STZ in BC1. exact BC1.
    + exact DC.
    + exact TB1.
    + reflexivity.
    + exact R1.
    + replace (mkBuf BS_ok (yb_len b) (yb_used b) (Some d1) (yb_bytes b)) with b by (destruct b; cbn in *; subst; reflexivity). exact CRED.
    + exact I1.
    + exact I2.
    + apply I5. discriminate.
    + lia.
    + lia.
    + lia.
    + intros bf HL. eapply app_leaf_inl; [exact HS| | exact HL]. unfold ens_first. rewrite HD. destruct b; cbn in *; subst; apply yl_ret.
    + unfold A_SB. lia.
    + unfold A_SB. lia.
    + exact HS.
  - (* [comment removed for export] *)
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (COMMON mo1 Hag1 HLI1) as (AHK1 & R1 & YS1 & PRES1).
    assert (HS : yb_state b = BS_ok) by (destruct (yb_state b); [reflexivity| cbn in STZ; lia| cbn in STZ; lia]).
    assert (HD : yb_data b = None) by (apply DZ; exact DZ0).
    destruct (I4 HD) as [L0 U00].
    unfold buf_blocks, abl in AHK1, RNG, SEP, ND, HBIN'. rewrite HD in AHK1, RNG, SEP, ND, HBIN'. cbn [map app blk_addr blk_size fst snd] in AHK1, RNG, SEP, HBIN'. cbn [app blk_addr blk_size fst snd] in ND. unfold SIZEOF_BUF in AHK1, RNG, SEP, HBIN', ND.
    rewrite DZ0 in BC1. rewrite STZ in BC1.
    clear MU. rename WM into WM1.
    assert (PHI1 : y_acharge Y 2048 + y_phi_buf Y (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b)) <= y_phi_buf Y b).
    { pose proof (YPHI_first 0%nat (yb_used b) (yb_bytes b)) as X. unfold YAJL_BUF_INIT_SIZE in X.
      destruct b as [bst blen bused bdata bbytes]. cbn in HS, HD, L0, X |- *. subst bst. subst bdata. subst blen. exact X. }
    (* [comment removed for export] *)
    name_sp sp (-128)%Z. rewrite <- Hsp in ST1.
    eapply (WMAL 2048 _ LF lo (y_phi_buf Y (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b)) + RR));
      [ exact K0
      | apply AYST_split; split; [exact AHK1| exact YS1]
      | reflexivity
      | lia
      | clear -CEILB PHI1 CRED; lia
      | destruct NONNEG as (_ & NB0 & _); pose proof (NB0 (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b))); lia
      | pose proof (nbig_cons_le {| ab_addr := mb_addr mb; ab_size := 32 |} REST); unfold AY_NBIG_REST in NBIG; lia
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [Z.div_mod_to_equations; lia|];
        split; [exact MI1|]; split; [exact TP| exact FRM]
      | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold AAPP_MAL_RET; rewrite unsigned_lit by lia; exact URA_mal]
      | ].
    cbv beta. intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F2 fc2 m2 mo2 sa2 B0 (MI2 & ST2 & FRM2 & WM2 & PRES2) SO2 R2 CRED2 RES.
    unname_sp.
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2. clear FR1.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES2 YAF ltac:(exists hb; split; [right; exact HBI| cbn; lia])) as YAF2. clear YAF.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES2 BC1 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as BC2. clear BC1.
    assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
    { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
    assert (TB2 : bytes_at asegs m2 S (zbytes src)).
    { eapply (asrc_pres Y REST LF (bv_unsigned sp + -128) S src); [exact LAYY| exact AHK1| exact YSR| | exact MI1| exact MI2| exact TB1].
      eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
    clear TB1 BSHu.
    (* [comment removed for export] *)
    + (* [comment removed for export] *)
      destruct RES as (EA0 & B0R & B0AM & B0HI & B0S & (junk0 & NEW) & AY2). subst a0''. unfold wz. unfold AAPP_MAL_RET.
      unfold ablock_range, ACONSTS in B0R. cbn [c_img_hi] in B0R. aceil.
      pose proof (B0HI ltac:(clear; lia)) as B0SH. unfold oshw_hi, A_SB in B0SH.   (* [comment removed for export] *)
      assert (B0SH2 : 17594333495296 <= B0) by (revert B0SH CEILB; clear; intros H CEILB; cbn in H; lia). clear B0SH B0HI.
      apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
      assert (AHK2' : y_AHK Y sa2 ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := B0; ab_size := 2048 |} :: REST) LF m2 mo2).
      { eapply PERMY; [exact AHK2| apply Permutation.perm_swap| apply Permutation.Permutation_refl]. }
      clear AHK2.
      destruct (BLKY _ _ _ _ _ AHK2') as (RNG2 & SEP2 & ND2).
      pose proof (SEP2 _ _ (or_introl eq_refl) (or_intror (or_introl eq_refl)) (nd_head_ne _ _ _ ND2 (or_introl eq_refl))) as SB0. cbn [ab_addr ab_size] in SB0.
      pose proof (BSHY _ _ _ _ _ (mkABlock (mb_addr mb) 32) AHK2' (or_introl eq_refl) ltac:(cbn; lia)) as [BSHm2 _]. cbn [ab_addr ab_size] in BSHm2.
      destruct BSHm2 as (_ & _ & BSHu). unfold A_SB in BSHu.
      pose proof B0S as B0S'. destruct B0S as (B08 & _ & B0Su). unfold A_SB in B0Su.
      (* [comment removed for export] *)
      arz_seg KIPY AHK2'. ret_pc_lit.
      pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_introl eq_refl) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PB PBS].
      pose proof (aypol_opol_block Y _ LF _ _ LINK _ (or_intror (or_introl eq_refl)) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PD PDS].
      cbn [ab_addr ab_size] in PB, PBS, PD, PDS. unfold oshw_lo, oshw_hi, A_SB, amem in PB, PBS, PD, PDS.
      eapply evtA_cut.
      { eapply (amain2_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mb_addr mb) B0 S (zlength src) AF (yb_used b) (bv_unsigned sp + -128) _ _ _ _ _ _ junk0);
          [ exact MI2 | exact BC2 | exact BSHu | reflexivity | exact NEW | exact B0Su | reflexivity
          | lia | lia | lia | lia | lia | lia | lia | lia | clear -CEILB SB0; lia | lia | lia
          | lia | lia | lia | lia | exact PB | exact PBS | exact PD | intros a k Ha Hk; apply PDS; lia ]. }
      cbv beta. intros ms3 (m3 & MU & WM & MI3 & BC3 & DC3 & CASES2).
      assert (COMMON2 : forall mo3, magree mo2 mo3 -> LI (y_aS Y sa2) (y_aN Y sa2) (y_aEB Y sa2) mo3 ->
                y_AHK Y sa2 ({| ab_addr := mb_addr mb; ab_size := 32 |} :: {| ab_addr := B0; ab_size := 2048 |} :: REST) LF m3 mo3 /\ y_ayR Y sa2 mo2 sa2 mo3
                /\ aystatics m3 /\ ay_pres REST LF (bv_unsigned sp) [] m m3).
      { intros mo3 Hag3 HLI3. destruct (BACK mo3 Hag3 HLI3) as [AHKb Rb]. split; [| split; [exact Rb| split]].
        - eapply FRAMEY; [exact AHKb| exact MU| exact WM|].
          constructor; [right; left; eexists; split; [left; reflexivity| cbn; lia]|].
          constructor; [right; left; eexists; split; [right; left; reflexivity| cbn; lia]| constructor].
        - eapply aystatics_munch; [exact YS2| exact MU| exact WM|]. constructor; [cbn; lia| constructor; [cbn; lia| constructor]].
        - eapply ay_pres_trans; [exact PRES2w|]. eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _. apply outside_cons; [| apply outside_cons; [| exact I]].
          + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock (mb_addr mb) 32));
              [exact AHK2'| left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
            intros b0 Hb0. split; [right; right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ ND2 (or_intror Hb0) (eq_sym E)).
          + eapply (ay_client_outside_block Y BLKY BSHY LAYY _ _ _ _ _ REST (bv_unsigned sp) (mkABlock B0 2048));
              [exact AHK2'| right; left; reflexivity| | cbn; lia| cbn; lia| lia| aceil; lia| exact Hc].
            intros b0 Hb0. split; [right; right; exact Hb0|]. cbn. intros E. exact (nd_head_ne _ _ _ (nd_tail _ _ ND2) Hb0 (eq_sym E)). }
      pose proof (SEP2 _ _ (or_intror (or_introl eq_refl)) (or_intror (or_intror HBI)) (nd_head_ne _ _ _ (nd_tail _ _ ND2) HBI)) as SB0H. cbn [ab_addr ab_size] in SB0H.
      eapply (rw_cells_transport asegs) in FR2; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
      eapply (rw_cells_transport asegs) in YAF2; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; clear -CEILB SB0H SBH HB1 HB2 HBR; lia].
      eapply (stk_transport_disjoint asegs) in ST2; [| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
      eapply (u8arr_transport asegs) in BSHu; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 32) by lia; lia].
      eapply (u8arr_transport asegs) in B0Su; [| exact MU| exact WM| cbv [disjoint_from fst snd]; rewrite (blk_shadow_length 2048) by lia; lia].
      assert (TB3 : bytes_at asegs m3 S (zbytes src)).
      { destruct src as [|c src']. { destruct TB2 as (X0 & X1 & _). split; [exact X0|]. split; [exact X1|]. intros i Hi. cbn in Hi. lia. }
        eapply (bytes_at_transport asegs); [exact TB2| exact MU|]. cbv [disjoint_from fst snd]. rewrite ZL.
        assert (SB0S : S + zlength (c :: src') <= B0 \/ B0 + 2048 <= S).
        { destruct YSR as [(bt & HBT & T1 & T2)|[Y2|[(f & Hf & Ff1 & Ff2)|Y4]]]; [| lia| | unfold zlength in Y4; cbn in Y4; lia].
          - pose proof (SEP2 _ _ (or_intror (or_introl eq_refl)) (or_intror (or_intror HBT)) (nd_head_ne _ _ _ (nd_tail _ _ ND2) HBT)) as X. cbn [ab_addr ab_size] in X. lia.
          - destruct (proj1 (proj2 (LAYY _ _ _ _ _ AHK2')) f _ Hf (or_intror (or_introl eq_refl))) as [X _]. cbn [ab_addr ab_size] in X. lia. }
        unfold zlength in *. cbn [length] in *. lia. }
      clear TB2.
      destruct CASES2 as [(NZ & x1 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & ->)
                          |(NZ & y10 & y11 & ->)].
      * (* [comment removed for export] *)
        apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (COMMON2 mo3 Hag3 HLI3) as (AHK3 & R3 & YS3 & PRES3).
        assert (SRC0 : src = []) by (destruct src; [reflexivity| unfold zlength in NZ; cbn in NZ; lia]).
        pose proof (BSHY _ _ _ _ _ (mkABlock B0 2048) AHK3 (or_intror (or_introl eq_refl)) ltac:(cbn; lia)) as [DSH3 DSHI3]. cbn [ab_addr ab_size] in DSH3, DSHI3.
        eapply J_ret with (sv := []) (b' := mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b)) (mb' := mkMB (mb_id mb) (mb_addr mb) (mb_did mb) B0) (LK := []) (junk := junk).
        -- cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app]. exact AHK3.
        -- exact YS3.
        -- exact FR2.
        -- exact ST2.
        -- exact MI3.
        -- exact FRM2.
        -- exact I.
        -- exact PRES3.
        -- unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF2.
        -- exact SO2.
        -- eapply RRT; [exact R1|]. eapply RRT; [exact R2| exact R3].
        -- exact CRED2.
        -- rewrite SRC0. eapply app_leaf_inl; [exact HS| unfold ens_first; rewrite HD; apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc| apply yl_ret]|].
           apply (yleaf_bind _ _ (mkBuf BS_ok 2048 (yb_used b) (Some 0%nat) (yb_bytes b))); [unfold ens_tail; cbn; apply yl_ret|].
           unfold app_tail. cbn. apply yl_ret.
        -- split; [| split; [| exact FB]].
           ++ split; [unfold buf_cells, wz; cbn [yb_state yb_len yb_used buf_state_code]; exact BC3| split; [cbn; split; [discriminate| lia]| cbn; unfold YAJL_BUF_INIT_SIZE in *; lia]].
           ++ unfold buf_data. cbn [yb_data yb_used yb_len yb_bytes mb_data]. rewrite U00. split; [lia|]. exists (skipn 1 junk0).
              replace (yb_bytes b) with ([] : list Z) by (destruct (yb_bytes b); [reflexivity| unfold zlength in I2; cbn in I2; lia]).
              change (Z.to_nat 0) with 0%nat. change (Z.to_nat (2048 - 0 - 1)) with 2047%nat. cbn [zbytes map]. exact DC3.
        -- split; reflexivity.
        -- unfold oshadow, block_shadow, A_SB, SIZEOF_BUF. cbn [mb_addr]. split; [exact B8|]. split; [lia|]. exact BSHu.
        -- cbn [yb_data yb_len mb_data]. intros _. split; [exact DSH3| exact DSHI3].
        -- intros X. exfalso. exact (X eq_refl).
        -- intros X. exfalso. exact (X eq_refl).
        -- reflexivity.   (* [comment removed for export] *)
      * (* [comment removed for export] *)
        apply evtA_done. intros mo3 Hag3 HLI3 Hh3. destruct (COMMON2 mo3 Hag3 HLI3) as (AHK3 & R3 & YS3 & PRES3).
        unfold AAPP_SIZE.
        eapply (J_size _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m3 mo3 sa2 junk (skipn 1 junk0) 2048 (yb_used b) 0%nat (mb_did mb) B0
                  ((mb_addr mb + 16) / 8 + 2147450880) (mb_addr mb / 8 + 2147450880)).
        -- cbn [buf_blocks yb_data yb_len mb_id mb_addr mb_did mb_data abl map blk_addr blk_size fst snd app]. exact AHK3.
        -- exact YS3.
        -- exact FR2.
        -- exact ST2.
        -- exact MI3.
        -- exact FRM2.
        -- exact I.
        -- exact PRES3.
        -- unfold alloc_cells. cbn [yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. exact YAF2.
        -- exact BC3.
        -- rewrite U00. replace (yb_bytes b) with ([] : list Z) by (destruct (yb_bytes b); [reflexivity| unfold zlength in I2; cbn in I2; lia]).
           change (Z.to_nat 0) with 0%nat. change (Z.to_nat (2048 - 0 - 1)) with 2047%nat. cbn [zbytes map]. exact DC3.
        -- exact TB3.
        -- exact SO2.
        -- eapply RRT; [exact R1|]. eapply RRT; [exact R2| exact R3].
        -- exact CRED2.
        -- exact I1.
        -- exact I2.
        -- lia.
        -- lia.
        -- lia.
        -- lia.
        -- intros bf HL. eapply app_leaf_inl; [exact HS| | exact HL]. unfold ens_first. rewrite HD.
           apply (yleaf_bind _ _ (Some 0%nat)); [apply yleaf_ymalloc| apply yl_ret].
        -- unfold A_SB. lia.
        -- unfold A_SB. lia.
        -- exact HS.
Qed.
End W.
End RC__1.
