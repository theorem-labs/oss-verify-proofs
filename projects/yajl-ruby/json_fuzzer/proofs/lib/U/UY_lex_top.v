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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel SFW1_lemmas InitMem Arr Frame.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMalloc_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UYajlAlign UYajl_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UY_rz UY_kit2 UY_lex_kit UY_lex_main.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Export UY_lex_top2.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlBuf YajlLeaf YajlLex YajlParser YajlFactsLex YajlFactsBuf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Open Scope yprog_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section T.
Variable HK : RawAlloc.PState -> list block -> mem -> Model -> Prop.
Hypothesis HKS : HK_silent_stmt HK.
Hypothesis HKP : HK_perm_stmt HK.
Hypothesis HKF : HK_frame_stmt HK.
Hypothesis HKB : HK_blocks_stmt HK.
Hypothesis YBA : ybuf_append_stmt HK.
Hypothesis YBE : ybuf_err_stmt.
Lemma ylex_lex_spec : ylex_lex_stmt HK.
Proof.
  unfold ylex_lex_stmt. intros REST h mh T txt off OBP OLP obw olw lo B errv KT.
  intros until s. intros K0 UA RY HS LR LI HOFF OFFB LEN TX TXR OB OL SPL OLB OBB YR FP A0 A1 A2 A3 A4 A5 CONT.
  destruct FP as (AX & SPB & STK & CEIL & LO & ERR & MI & TP).
  apply RYST_split in RY. destruct RY as [HK0 YS].
  rewrite (ry_errno_lit tp TP) in ERR.
  pose proof LI as (IU & IO & IL & ICH & IA & IV & IB).
  (* [comment removed for export] *)
  unfold lexer_blocks, buf_blocks in HK0. rewrite IB in HK0. cbn [yb_data ybuf_zero app] in HK0.
  destruct (HK_blocks HK HKB _ _ _ _ HK0) as [RNG SEP].
  cbn [all_range all_sep sep_from] in RNG, SEP. cbn [blk_addr blk_size fst snd] in RNG, SEP.
  destruct RNG as (RH & RL & RLB & RREST). destruct SEP as ((SHL & SHB & SHR) & (SLB & SLR) & SBR & _).
  unfold SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF in *.
  (* [comment removed for export] *)
  destruct HS as ((pew & pad & HC & PW) & HB1 & HB2 & HB3 & HB4).
  destruct LR as ((LC & L1 & L2 & L3 & L4 & L5 & L6) & ((BC & BI & BL1 & BL2) & BD & BF)). clear L1 L2 L3 L4 L5 L6 BL1 BL2.
  rewrite IB in BC, BI, BD, BF.
  assert (D0 : mb_data (mh_lexbuf mh) = 0) by (apply BI; reflexivity). rewrite D0 in BC.
  rewrite (lxcells_of_lexer _ _ _ LI) in LC.
  apply hand_split in HC. destruct HC as (HC0 & OFF0 & HC2 & YAF). rewrite HOFF in OFF0.
  pose proof (rw_cells_bound _ _ _ _ OB) as OBR. cbn [cells_size csize Nat.add] in OBR.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  unfold RY_LEX_LEX_STACK, RY_BUF_APPEND_STACK, RY_WRAP_STACK in LO.
  (* [comment removed for export] *)
  assert (A8LB : al8 (mb_addr (mh_lexbuf mh))) by (clear - RLB; unfold rblock_range in RLB; apply al8_of_mod16; lia).
  assert (A8AF : al8 (mh_addr mh + 72)) by (clear - RH; unfold rblock_range in RH; apply al8_of_mod16_off; [lia| reflexivity]).
  assert (AH : Z.land (mh_addr mh + 32) 3 = 0) by (clear - RH; unfold rblock_range in RH; apply land3_al4; apply al4_of_mod16_off; [lia| reflexivity]).
  assert (AL : Z.land (mh_lexer mh) 7 = 0) by (clear - RL; unfold rblock_range in RL; apply land7_al8; apply al8_of_mod16; lia).
  pose proof (land7_al8 _ (proj1 UA)) as AOB. pose proof (land3_al4 _ (proj2 UA)) as AOL.
  assert (UAB : forall R1 b src lo1 B1 ev spx S1, 0 < S1 -> 0 < mb_addr (mh_lexbuf mh) -> 0 < mh_addr mh + 72 ->
            UA_ybuf_append R1 (mh_lexbuf mh) b (mh_addr mh + 72) S1 src lo1 B1 ev spx).
  { intros. unfold UA_ybuf_append. repeat split; try assumption. }
  clear UA.
  pose proof TX as (_ & TF & TP0 & TL).
  assert (LENV : lexenv (bv_unsigned sp) lo T (zlength txt) (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh))).
  { eapply (lexenv_intro _ _ _ _ _ _ _ REST _ _ _ CEIL); [unfold alloc_ceiling in *; lia| lia| exact RH| exact RL| exact RLB| exact SHL| exact SHB| exact SLB| lia| exact TP0| exact TL| exact TXR| exact RREST| exact SHR| exact SLR| exact SBR]. }
  assert (LOSP : lo <= bv_unsigned sp) by lia.
  assert (NUMS : mh_addr mh + 104 <= lo /\ mh_lexer mh + 48 <= lo /\ mb_addr (mh_lexbuf mh) + 32 <= lo /\ 0 < mh_addr mh /\ 0 < mh_lexer mh
                 /\ 0 < mb_addr (mh_lexbuf mh) /\ lo <= bv_unsigned sp - 8464 /\ 356352 <= lo
                 /\ (mh_addr mh + 104 <= mh_lexer mh \/ mh_lexer mh + 48 <= mh_addr mh)
                 /\ (mh_addr mh + 104 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= mh_addr mh)
                 /\ (mh_lexer mh + 48 <= mb_addr (mh_lexbuf mh) \/ mb_addr (mh_lexbuf mh) + 32 <= mh_lexer mh)
                 /\ (mh_addr mh + 104 <= 65536 \/ 356352 <= mh_addr mh) /\ (mh_lexer mh + 48 <= 65536 \/ 356352 <= mh_lexer mh)
                 /\ (mb_addr (mh_lexbuf mh) + 32 <= 65536 \/ 356352 <= mb_addr (mh_lexbuf mh)))
    by (clear - RH RL RLB CEIL LO SHL SHB SLB; unfold rblock_range, bsep, alloc_ceiling in *; cbn [blk_addr blk_size fst snd] in *; lia).
  destruct NUMS as (NH & NL & NLB & NH0 & NL0 & NLB0 & NLO & NCE & NSHL & NSHB & NSLB & NIH & NIL & NILB).
  pose proof (fun a => lexW_client_outside (bv_unsigned sp) lo (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OLP OBP REST (mh_id mh) (mh_lid mh) (mb_id (mh_lexbuf mh)) a CEIL LOSP SPL OLB RH RL RLB RREST SHR SLR SBR) as WOUT.
  pose proof (fun a => lexL_client_outside (bv_unsigned sp) lo _ REST _ a CEIL ltac:(lia) RL SLR RREST) as LOUT.
  destruct (lexW_facts (bv_unsigned sp) lo (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OLP OBP B
              ((mh_id mh, mh_addr mh, 104) :: (mh_lid mh, mh_lexer mh, 48) :: (mb_id (mh_lexbuf mh), mb_addr (mh_lexbuf mh), 32) :: REST)
              (mh_id mh) (mh_lid mh) (mb_id (mh_lexbuf mh))
              CEIL SPL OLB OBB ltac:(lia)
              ltac:(left; reflexivity) ltac:(right; left; reflexivity) ltac:(right; right; left; reflexivity) RH RL RLB)
    as (WOK & WAX & WST).
  subst a0 a1 a2 a3 a4 a5.
  (* [comment removed for export] *)
  rz_seg HKS HK0.
  eapply evt_cut.
  { eapply (lex_prologue sp gp tp F fc lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP);
      [exact STK| exact MI| exact OFF0| exact OB| exact OL| exact LC| exact BC| exact LENV| exact SPL| exact OLB| lia| exact OFFB| exact AH| exact AOB| exact AOL| exact AL]. }
  cbv beta. intros ms1 (a1' & a2' & a3' & junk & m1 & -> & MU & WM & MI1 & STK1 & FR1 & OFF1 & OB1 & OL1 & LC1 & BC1).
  clear STK MI OFF0 OB OL LC BC.
  set (K := mkLK sp gp tp F fc lo T txt (mh_addr mh) (mh_lexer mh) (mb_addr (mh_lexbuf mh)) OBP OLP junk
                  ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  assert (ENV : kenv K) by exact LENV.
  Ltac kk X := cbv delta [X]; cbv delta [kSP kAF]; cbn [k_sp k_gp k_tp k_F k_fc k_lo k_T k_txt k_H k_L k_LB k_OBP k_OLP k_junk k_ra k_s0 k_s1 k_s2 k_s3 k_s4 k_s5 k_s6 k_s7 k_s8 k_s9 k_s10 k_s11].
  Ltac kkh X H := cbv delta [X] in H; cbv delta [kSP kAF] in H; cbn [k_sp k_gp k_tp k_F k_fc k_lo k_T k_txt k_H k_L k_LB k_OBP k_OLP k_junk k_ra k_s0 k_s1 k_s2 k_s3 k_s4 k_s5 k_s6 k_s7 k_s8 k_s9 k_s10 k_s11] in H.
  assert (TX1 : text_at usegs m1 T txt).
  { eapply text_at_transport; [exact TX| exact MU|]. intros Hl0. clear - Hl0 LENV SPL OLB CEIL LOSP. destruct LENV. cbn. unfold alloc_ceiling in *. lia. }
  eapply evt_cut.
  { eapply (lex_loop_walk K ENV (lex_fuel (zlength txt) off) (h_lexer h)) with (m0 := m1) (start := off);
      [exact TX1| exact LI| | kk K; lia| kk K; lia| kk K; unfold lex_fuel; lia].
    unfold lexmem, kW, kframe, lexW. kk K.
    split; [apply munch_refl|]. split; [apply wmono_refl|].
    repeat match goal with |- _ /\ _ => split end; assumption. }
  cbv beta. intros ms' POST. destruct POST as (lx1 & tok & off1 & start1 & YL & LI1 & TPost).
  pose proof (ypost_yleaf _ _ _ (ylex_loop_post (lex_fuel (zlength txt) off) (h_lexer h) txt (zlength txt) off LI ltac:(lia) ltac:(unfold lex_fuel; lia)) YL) as LP.
  unfold YajlFactsLex.loop_post in LP. cbv beta iota zeta in LP. destruct LP as (_ & SB1 & SB2 & TK).
  pose proof LI1 as (IU1 & IO1 & IL1 & ICH1 & IA1 & IV1 & IB1).
  apply tok_post_cases in TPost. destruct TPost as [[-> AT] | [NE AT]].
  + (* [comment removed for export] *)
    destruct AT as (rav' & s0' & s1' & s6' & s7' & s8' & t0' & t1' & t2' & a0' & a1'' & a2'' & a3'' & a4' & a5' & a6'' & a7'' & t3' & t4' & t5' & t6' & m2 & -> & LM2).
    pose proof LM2 as (MU2 & WM2 & _). unfold kW, lexW in MU2. kkh K MU2.
    assert (OB2 : rw_cells usegs m2 OBP [C8 (wz 0)]) by (eapply rw_cells_transport; [exact OB1| exact MU2| exact WM2| cbn; lia]).
    assert (OL2 : rw_cells usegs m2 OLP [C4 (wz 0)]) by (eapply rw_cells_transport; [exact OL1| exact MU2| exact WM2| cbn; lia]).
    eapply evt_mono; [eapply (lex_eof_head K ENV) with (m1 := m1); [exact LM2| lia| kk K; lia]|].
    cbv beta. intros ms3 (t0e & t1e & t2e & a3e & a4e & a5e & a6e & a7e & t3e & t4e & t5e & t6e & m4 & -> & MU4 & WM4 & MI4 & STK4 & FR4 & OFF4 & LX4 & BC4).
    unfold kW, lexW in MU4. kkh K MU4. kkh K STK4. kkh K FR4. kkh K OFF4. kkh K LX4. kkh K BC4. kk K.
    assert (OB4 : rw_cells usegs m4 OBP [C8 (wz 0)]) by (eapply rw_cells_transport; [exact OB1| exact MU4| exact WM4| cbn; lia]).
    assert (OL4 : rw_cells usegs m4 OLP [C4 (wz 0)]) by (eapply rw_cells_transport; [exact OL1| exact MU4| exact WM4| cbn; lia]).
    clear OB2 OL2 MU2 WM2 LM2.
    (* [comment removed for export] *)
    assert (MUT : munch [(lo, bv_unsigned sp); (mh_addr mh + 32, mh_addr mh + 36); (mh_lexer mh, mh_lexer mh + 48);
                         (mb_addr (mh_lexbuf mh) + 8, mb_addr (mh_lexbuf mh) + 12); (OLP, OLP + 4); (OBP, OBP + 8)] m m4).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU4]. unfold sub_fp. cbn [outside].
      intros x (X1 & X2 & X3 & X4 & X5 & X6 & _). repeat split; assumption. }
    pose proof (wmono_trans _ _ _ _ WM WM4) as WMT.
    destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MUT WMT WOK WAX) as [HK4 AX4].
    pose proof (ystatics_munch _ _ _ YS MUT WMT WST) as YS4.
    assert (TX4 : text_at usegs m4 T txt).
    { eapply text_at_transport; [exact TX| exact MUT|]. intros Hl0. clear - Hl0 LENV SPL OLB CEIL LOSP. destruct LENV. cbn. unfold alloc_ceiling in *. lia. }
    assert (SRCL : zlength (zslice txt start1 (off1 - start1)) = off1 - start1) by (apply zslice_length; lia).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 160)) = bv_unsigned sp - 160) by (apply unsigned_lit; lia).
    eapply (YBA ((mh_id mh, mh_addr mh, 104) :: (mh_lid mh, mh_lexer mh, 48) :: REST) (mh_lexbuf mh) ybuf_zero (mh_addr mh + 72)
                (T + start1) (zslice txt start1 (off1 - start1)) lo B errv KT).
    { exact K0. }
    { apply UAB; lia. }
    { unfold buf_blocks. cbn [yb_data ybuf_zero app]. apply RYST_split. split; [| exact YS4].
      eapply HKP; [exact HK4|]. apply Permutation.Permutation_sym.
      apply (Permutation.Permutation_cons_app [_; _] REST). apply Permutation.Permutation_refl. }
    { split; [split; [rewrite D0; exact BC4| split; [exact BI| cbn; lia]]|]. split; [exact BD| exact BF]. }
    { apply buf_inv_zero. }
    { eapply rw_cells_transport; [exact YAF| exact MUT| exact WMT| unfold alloc_cells; cbn; lia]. }
    { eexists. split; [left; reflexivity|]. cbn. lia. }
    { apply lbytes_at_zslice; [exact (proj1 TX4)| lia]. }
    { apply lForall_zslice. exact TF. }
    { intros _. lia. }
    { rewrite SRCL. lia. }
    { rewrite SRCL. cbn. lia. }
    { unfold ysrc_range. rewrite SRCL. destruct TXR as [(bt & IN & B1 & B2)|Z0].
      - left. exists bt. split; [right; right; exact IN| lia].
      - right; right; right. lia. }
    { apply yroom_cons. apply yroom_cons. eapply yroom_le; [exact YR| lia]. }
    { split; [exact AX4|]. split; [rewrite ESP; lia|]. split; [rewrite ESP; exact STK4|]. split; [exact CEIL|].
      split; [rewrite ESP; unfold RY_BUF_APPEND_STACK, RY_WRAP_STACK; lia|].
      split; [rewrite (ry_errno_lit tp TP); eapply rw_cells_transport; [exact ERR| exact MUT| exact WMT| cbn; unfold RERRNO; lia]|].
      split; [exact MI4| exact TP]. }
    { reflexivity. }
    { reflexivity. }
    { unfold wz. rewrite SRCL. reflexivity. }
    cbv beta. intros t0c t1c t2c a0c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c m5 mo5 pst5 b' mb' LK POST5.
    destruct POST5 as ((MI5 & STK5 & (errv5 & ERR5) & AX5 & HP5) & YAF5 & YLA & BR5 & MBS & LKE & RY5).
    replace (ret_pc (Z_to_bv 64 86680)) with (Z_to_bv 64 86680) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ESP in STK5, HP5. rewrite (ry_errno_lit tp TP) in ERR5.
    apply ry_pres_nil in HP5.
    apply RYST_split in RY5. destruct RY5 as [HK5 YS5].
    destruct MBS as [MBI MBA].
    pose proof BR5 as BR5c.
    destruct BR5 as ((BC5 & BI5 & BL5 & BL5') & BD5 & BF5). rewrite MBA in BC5. unfold buf_cells in BC5.
    (* [comment removed for export] *)
    pose proof (ypres_frame _ _ _ _ _ _ HP5 FR4 ltac:(lia)) as FR5.
    pose proof (ypres_block _ _ _ _ _ _ HP5 LX4 ltac:(eexists; split; [right; left; reflexivity| cbn; lia])) as LX5.
    pose proof (ypres_block _ _ _ _ _ _ HP5 OFF4 ltac:(eexists; split; [left; reflexivity| cbn; lia])) as OFF5.
    assert (HC05 : rw_cells usegs m5 (mh_addr mh) [C8 (wz (yc_callbacks ryc)); C8 (wz (mh_ctx mh)); C8 (wz (mh_lexer mh)); C8 pew]).
    { eapply ypres_block; [exact HP5| | eexists; split; [left; reflexivity| cbn; lia]].
      eapply rw_cells_transport; [exact HC0| exact MUT| exact WMT| cbn; lia]. }
    assert (HC25 : rw_cells usegs m5 (mh_addr mh + 36) [C4 pad; C8 (wz (mb_addr (mh_decbuf mh))); C8 (wz (mh_stack mh)); C4 (wz (h_stack_size h)); C4 (wz (h_used h)); C8 (wz (mh_addr mh + 72))]).
    { eapply ypres_block; [exact HP5| | eexists; split; [left; reflexivity| cbn; lia]].
      eapply rw_cells_transport; [exact HC2| exact MUT| exact WMT| cbn; lia]. }
    pose proof (ypres_frame _ _ _ _ _ _ HP5 OB4 ltac:(lia)) as OB5.
    pose proof (ypres_frame _ _ _ _ _ _ HP5 OL4 ltac:(lia)) as OL5.
    assert (TX5 : text_at usegs m5 T txt).
    { eapply ypres_text; [exact HP5| exact TX4|]. destruct TXR as [(bt & IN & B1 & B2)|Z0]; [left; exists bt; split; [right; right; exact IN| lia]| right; exact Z0]. }
    (* [comment removed for export] *)
    destruct (HK_blocks HK HKB _ _ _ _ HK5) as [RNG5 SEP5].
    assert (DSEP : yb_data b' <> None -> mb_data mb' + yb_len b' <= lo /\ (mb_data mb' + yb_len b' <= mh_lexer mh \/ mh_lexer mh + 48 <= mb_data mb')).
    { intros HD. unfold buf_blocks in SEP5, RNG5. destruct (yb_data b'); [| congruence].
      cbn [all_sep sep_from app] in SEP5. destruct SEP5 as (_ & S2 & _).
      apply sep_from_app in S2. destruct S2 as [_ S2]. cbn [sep_from] in S2. destruct S2 as (_ & S2 & _).
      unfold bsep in S2. cbn [blk_addr blk_size fst snd] in S2.
      cbn [all_range app] in RNG5. destruct RNG5 as (_ & RD & _). unfold rblock_range in RD. cbn [blk_addr blk_size fst snd] in RD.
      clear - S2 RD CEIL. unfold alloc_ceiling in *. lia. }
    assert (BSR : 0 <= buf_state_code (yb_state b') <= 2) by (destruct (yb_state b'); cbn; lia).
    (* [comment removed for export] *)
    rz_seg HKS HK5.
    eapply evt_mono.
    { eapply (lex_eof_tail K ENV YBE) with (e1 := lex_error_code (lx_error lx1)) (st := buf_state_code (yb_state b'))
        (LB := mb_addr (mh_lexbuf mh)) (bl := yb_len b') (bu := yb_used b') (bd := mb_data mb') (ba := mh_addr mh + 72) (off1 := off1);
        kk K; [exact FR5| exact LX5| exact BC5| exact BSR| lia| clear - RLB; unfold rblock_range, alloc_ceiling in *; lia| exact A8LB| lia| exact STK5| exact MI5]. }
    cbv beta. intros ms6 (t0f & t1f & t2f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m6 & -> & MU6 & WM6 & MI6 & STK6 & LX6 & BC6).
    kkh K MU6. kkh K STK6. kkh K LX6. kk K.
    assert (WOK6 : Forall (rclient_write_ok (buf_blocks mb' b' ++ LK ++ (mh_id mh, mh_addr mh, 104) :: (mh_lid mh, mh_lexer mh, 48) :: REST)) [(lo, bv_unsigned sp - 160); (mh_lexer mh, mh_lexer mh + 48)]).
    { constructor; [left; exact CEIL|]. constructor; [| constructor]. right; right. exists (mh_lid mh, mh_lexer mh, 48). split; [| cbn; lia].
      apply in_or_app. right. apply in_or_app. right. right. left. reflexivity. }
    pose proof (HKF _ _ _ _ _ _ HK5 MU6 WM6 WOK6) as HK6.
    (* [comment removed for export] *)
    set (lx2 := lx_set_buf lx1 b' 0 1).
    set (lxr := if buf_state_code (yb_state b') =? 0 then lx2 else lx_set_error lx2 LE_alloc_failed).
    set (tokr := if buf_state_code (yb_state b') =? 0 then TK_eof else TK_error).
    assert (RES : eof_ret (buf_state_code (yb_state b')) = tok_code tokr /\ eof_err (buf_state_code (yb_state b')) (lex_error_code (lx_error lx1)) = lex_error_code (lx_error lxr)
                  /\ lx_buf lxr = b' /\ lx_bufOff lxr = 0 /\ lx_bufInUse lxr = 1 /\ lx_lineOff lxr = 0 /\ lx_charOff lxr = 0
                  /\ lx_allowComments lxr = 1 /\ lx_validateUTF8 lxr = 1
                  /\ yleaf (ylex_finish lx1 txt TK_eof off1 start1) (lxr, tokr, off1, OB_null, 0)).
    { unfold eof_ret, eof_err, lxr, tokr, lx2. unfold ylex_finish. rewrite IU1, IB1.
      cbn [tok_eqb tok_code Z.eqb Pos.eqb orb negb andb ybuf_clear yb_state ybuf_zero ybind yb_len yb_data].
      destruct (yb_state b') eqn:BS;
        cbn [buf_state_code Z.eqb Pos.eqb tok_code lx_buf lx_bufOff lx_bufInUse lx_lineOff lx_charOff lx_allowComments lx_validateUTF8 lx_set_buf lx_set_error lx_error lex_error_code];
        repeat split; try reflexivity; try assumption.
      all: eapply yleaf_bind; [exact YLA|]; cbv beta iota; unfold ybuf_err; rewrite BS; cbn [buf_state_ok negb]; apply yl_ret. }
    destruct RES as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RLEAF). rewrite R1. rewrite R2 in LX6.
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m6 mo5 pst5 lxr tokr off1 OB_null 0 mb' LK).
    unfold ylex_lex_rpost.
    split.
    { split; [exact MI6|]. split; [exact STK6|].
      split; [exists errv5; rewrite (ry_errno_lit tp TP); eapply rw_cells_transport; [exact ERR5| exact MU6| exact WM6| cbn; unfold RERRNO; lia]|].
      split; [eapply rauxv_ok_frame; [exact AX5| exact MU6| exact WM6| constructor; [cbn; unfold RAUXV_CELL; lia|]; constructor; [cbn; unfold RAUXV_CELL; lia| constructor]]|].
      eapply ry_pres_trans; [| eapply ry_pres_trans; [eapply ry_pres_of_rheap_pres; eapply rheap_pres_weaken; [exact HP5| lia| intros bb Hbb; right; right; exact Hbb]|]].
      - eapply ryajl_pres_of_munch; [exact MUT| exact WMT| exact WOUT].
      - eapply ryajl_pres_of_munch; [exact MU6| exact WM6|]. intros a Ha Hc _. exact (LOUT a Ha Hc). }
    split.
    { unfold ylex_lex. eapply yleaf_bind; [exact YL|]. cbv beta iota. exact RLEAF. }
    split; [reflexivity|].
    split.
    { split. 2:{ change (h_used (h_set_lex_off h lxr off1)) with (h_used h). cbn. split; [lia| split; [lia| split; [lia| exact HB4]]]. }
      exists pew, pad. split; [| exact PW]. apply hand_split. cbn [h_bytesConsumed h_set_lex_off h_stack_size h_parseError mh_decbuf].
      change (h_used (h_set_lex_off h lxr off1)) with (h_used h).
      split; [| split; [| split]]; (eapply rw_cells_transport; [| exact MU6| exact WM6| unfold alloc_cells; cbn; lia]);
        [exact HC05| exact OFF5| exact HC25| exact YAF5]. }
    split.
    { split.
      - split; [| rewrite ?R4, ?R5, ?R6, ?R7, ?R8, ?R9; lia].
        unfold lexer_cells. rewrite ?R3, ?R4, ?R5, ?R6, ?R7, ?R8, ?R9, ?MBA. exact LX6.
      - rewrite R3. eapply buf_rep_transport; [exact BR5c| exact MU6| exact WM6| rewrite MBA; cbn; lia|].
        intros HD. specialize (DSEP HD). cbn. clear - DSEP. lia. }
    split; [split; assumption|].
    split; [eapply rw_cells_transport; [exact OB5| exact MU6| exact WM6| cbn; lia]|].
    split; [eapply rw_cells_transport; [exact OL5| exact MU6| exact WM6| cbn; lia]|].
    split; [eapply text_at_transport; [exact TX5| exact MU6|]; intros Hl1; clear - Hl1 LENV; destruct LENV; cbn; unfold alloc_ceiling in *; lia|].
    split; [exact LKE|].
    unfold lexer_blocks. rewrite R3.
    apply RYST_split. split.
    - eapply HKP; [exact HK6|]. rewrite !app_assoc. apply Permutation.Permutation_sym.
      apply (Permutation.Permutation_cons_app (buf_blocks mb' b' ++ LK) ((mh_lid mh, mh_lexer mh, 48) :: REST)).
      apply Permutation.Permutation_middle.
    - eapply ystatics_munch; [exact YS5| exact MU6| exact WM6|]. constructor; [cbn [fst snd]; unfold RY_CALLBACKS; lia|]. constructor; [cbn [fst snd]; unfold RY_CALLBACKS; lia| constructor].
  + (* [comment removed for export] *)
    destruct AT as (rav' & s0' & s1' & s6' & s7' & s8' & t0' & t1' & t2' & a0' & a1'' & a2'' & a3'' & a4' & a5' & a6'' & a7'' & t3' & t4' & t5' & t6' & m2 & -> & LM2).
    pose proof LM2 as (MU2 & WM2 & _). unfold kW, lexW in MU2. kkh K MU2.
    assert (OB2 : rw_cells usegs m2 OBP [C8 (wz 0)]) by (eapply rw_cells_transport; [exact OB1| exact MU2| exact WM2| cbn; lia]).
    assert (OL2 : rw_cells usegs m2 OLP [C4 (wz 0)]) by (eapply rw_cells_transport; [exact OL1| exact MU2| exact WM2| cbn; lia]).
    eapply evt_mono.
    { eapply (lex_fin_walk K ENV tok) with (m1 := m1); [exact NE| exact LM2| kk K; exact OB2| kk K; exact OL2| kk K; lia| kk K; lia| kk K; lia| lia| kk K; lia|].
      intros IS. destruct tok; try discriminate IS; lia. }
    cbv beta. intros ms'' (t0x & t1x & t2x & a1x & a2x & a3x & a4x & a5x & a6x & a7x & t3x & t4x & t5x & t6x & m3 & -> & MU3 & WM3 & MI3 & STK3 & OFF3 & LX3 & BC3 & OB3 & OL3).
    unfold topW, kW, lexW in MU3. kkh K MU3. kkh K STK3. kkh K OFF3. kkh K LX3. kkh K BC3. kkh K OB3. kkh K OL3. kk K. cbn [app] in MU3.
    pose proof (munch_trans _ _ _ _ MU MU3) as MUT. pose proof (wmono_trans _ _ _ _ WM WM3) as WMT.
    destruct (yown_writes HK HKF _ _ _ _ _ _ B HK0 AX MUT WMT WOK WAX) as [HK3 AX3].
    eapply (CONT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m3 mo s lx1 tok off1 (fst (fin_ob tok start1 off1)) (snd (fin_ob tok start1 off1)) (mh_lexbuf mh) []).
    unfold ylex_lex_rpost.
    split.
    { split; [exact MI3|]. split; [exact STK3|].
      split; [exists errv; rewrite (ry_errno_lit tp TP); eapply rw_cells_transport; [exact ERR| exact MUT| exact WMT| cbn; unfold RERRNO; lia]|].
      split; [exact AX3|].
      eapply ryajl_pres_of_munch; [exact MUT| exact WMT| exact WOUT]. }
    split.
    { unfold ylex_lex. eapply yleaf_bind; [exact YL|]. cbv beta iota.
      unfold ylex_finish. rewrite (tok_eqb_eof_false tok NE), IU1. cbn [orb negb Z.eqb].
      unfold fin_ob. destruct (tok_eqb tok TK_error) eqn:TE; cbn [negb fst snd].
      - apply yl_ret.
      - destruct (is_string_tok tok) eqn:IS.
        + unfold yassert. replace (2 <=? off1 - start1) with true by (symmetry; apply Z.leb_le; destruct tok; try discriminate IS; lia).
          cbn [ybind]. apply yl_ret.
        + apply yl_ret. }
    split; [reflexivity|].
    split.
    { split. 2:{ change (h_used (h_set_lex_off h lx1 off1)) with (h_used h). cbn. split; [lia| split; [lia| split; [lia| exact HB4]]]. }
      exists pew, pad. split; [| exact PW]. apply hand_split. cbn [h_bytesConsumed h_set_lex_off h_stack_size h_parseError mh_decbuf].
      change (h_used (h_set_lex_off h lx1 off1)) with (h_used h).
      split; [| split; [exact OFF3| split]]; (eapply rw_cells_transport; [| exact MUT| exact WMT| unfold alloc_cells; cbn; lia]);
        [exact HC0| exact HC2| exact YAF]. }
    split.
    { split.
      - split; [| rewrite IL1, ICH1, IO1, IU1, IA1, IV1; lia]. rewrite (lxcells_of_lexer _ _ _ LI1). exact LX3.
      - rewrite IB1. split; [split; [rewrite D0; exact BC3| split; [exact BI| cbn; lia]]|]. split; [exact BD| exact BF]. }
    split; [split; reflexivity|].
    split; [rewrite D0; exact OB3|]. split; [exact OL3|].
    split; [eapply text_at_transport; [exact TX| exact MUT|]; intros Hl1; clear - Hl1 LENV SPL OLB CEIL LOSP; destruct LENV; cbn; unfold alloc_ceiling in *; lia|].
    split; [reflexivity|].
    unfold lexer_blocks, buf_blocks. rewrite IB1. cbn [yb_data ybuf_zero app].
    apply RYST_split. split; [exact HK3| exact (ystatics_munch _ _ _ YS MUT WMT WST)].
Qed.
End T.

End RC__1.
