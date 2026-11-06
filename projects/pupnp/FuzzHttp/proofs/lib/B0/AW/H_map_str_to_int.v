(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Import HttpRepA AWKit AWAuto FakeKit HObjK H_memptr_cmp AWUb.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.AW Require Export H_map_str_to_int_seg.
Import ListNotations.
Open Scope Z_scope.

Section W.
Context {HC : HasCeiling}.
Hypothesis IC : icpt_contracts.
Variable FI : fs_if.
Hypothesis STACK_MALLOC_0 : stack_malloc_stmt FI 0.

Local Notation FSIV W := ((FSB FI, FSB FI + A0_FS_SIZE) :: (sh (FSB FI), sh (FSB FI) + A0_FS_SHSIZE) :: W)%Z.

Local Notation map_str_to_int_post_A := (H_map_str_to_int_seg.map_str_to_int_post_A FI).
Local Notation map_str_to_int_stmt_A := (H_map_str_to_int_seg.map_str_to_int_stmt_A FI).

Section WALK.
  Variables (T n TAB ne lo : Z) (tok : list byte) (ws : list word) (st : fsstate FI).
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis TL : Z.of_nat (length tok) >= n.
  Hypothesis N1 : 1 <= n <= 2^43.
  Hypothesis TLO : 0x609000 <= T.
  Hypothesis THI : T + Z.of_nat (length tok) <= alloc_ceiling.
  Hypothesis SHWT : shw m0 T n.
  Hypothesis TFS : T + Z.of_nat (length tok) <= FSB FI \/ FSB FI + A0_FS_SIZE <= T.
  Hypothesis TBAND : T + Z.of_nat (length tok) <= 0x7fff7000 \/ 0x10007fff8000 <= T.
  Hypothesis LEN : Z.of_nat (length ws) = 2 * ne.
  Hypothesis NE : 1 <= ne <= 33.
  Hypothesis TABLO : 0x10000 <= TAB.
  Hypothesis TABHI : TAB + 16 * ne <= 0x609000.
  Hypothesis TABAL : TAB mod 8 = 0.
  Hypothesis SHWTAB : shw m0 TAB (16 * ne).
  Hypothesis TS : table_strings_A m0 ws ne.
  Hypothesis CLO : alloc_ceiling <= lo.
  Hypothesis LO : lo <= q - 128 - 16 - 32 - 4096.
  Hypothesis AL16 : q mod 16 = 0.
  Hypothesis QHI : q < 2^64.
  Hypothesis RF0 : RFAKE FI st m0.
  Hypothesis FCO : fs_call_ok FI st tp 1.
  Hypothesis FE0 : FSENV FI m0.

  Local Notation F := (fs_F FI st 0).  Local Notation FL := (fs_FL FI st 0).  Local Notation st1 := (fs_next FI st 0).  Local Notation SF := (sh (fs_F FI st 0)).
  Notation POST := (map_str_to_int_post_A ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st lo ne m0).
  Notation W0 := ((lo, q) :: FSIV [])%Z.

  Local Notation minvM := (H_map_str_to_int_seg.minvM FI T n TAB lo tok ws st ra q s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0).
  Local Notation prologueM := (H_map_str_to_int_seg.prologueM FI STACK_MALLOC_0 T n TAB ne lo tok ws st ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc m0 TL N1 THI TFS TBAND LEN NE TABLO TABHI CLO LO AL16 QHI RF0 FCO FE0).

  #[using="TL N1 THI TFS TBAND LEN TABLO TABHI CLO LO AL16 RF0"] Lemma exitM : forall (r q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x27 x28 x29 x30 x31 m,
    minvM q' m -> (r = -1 \/ 0 <= r < ne) ->
    evt asegs POST
      (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
               (wz F) x19 (wz r) x21 x22 x23 (wz SF) (wz 0x7fff8000) (wz F) x27 x28 x29 x30 x31)
          F_ (wz 0x8ea3c) fc None m (seg_rom asegs)).
  Proof.
    intros r q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x27 x28 x29 x30 x31 m.
    intros (Hq & ST & (jq & QC) & GAP & FRhi & FH & MPC & (j8 & FT) & SH1 & SH2 & SH3 & FLG & TOK & ARR & MI & MU & WM & FK & RF & AE & LIVE1) HR.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & FSB3 & FSB4). unfold app_mem in FSB3.
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI, APART.
    pose proof (new_frame_fk FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as NFK.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (lb_new _ _ _ LIVE1) as LVF. pose proof (ls_new _ _ _ LIVE1) as LVS. pose proof (lf_new _ _ _ LIVE1) as LVL.
    unfold ff_size, ff_shsize in LVF, LVS. rewrite FCLS in LVF, LVS. cbn [FB_of SB_of] in LVF, LVS.
    change (ff_addr (fs_newff FI st 0)) with F in LVF, LVS. change (ff_flag (fs_newff FI st 0)) with FL in LVL. change (sh F) with SF in LVS.
    unfold memptr_cells, shadow_zero_cells, shadow_cells in *. cbn [map repeat] in SH2.
    pose proof (munch_refl [(lo, q); (F, F + 64); (SF, SF + 8)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    step.
    sstep. sstep.
    step. step. step; fix_lit_store.
    step.   if_cases K0; zify_cond K0. { exfalso. lia. } clear K0.
    step.
    do 8 sstep.
    step.

    env_sync AE MU0 WM0. fs_sync FI RF MU0 WM0 FK LSUB.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(FL, FL + 1)]%Z mm) as MU0; pose proof (wmono_refl asegs mm) as WM0 end.
    sstep.
    env_sync AE MU0 WM0. fk_sync FI RF MU0 FK LSUB.

    join_chunks SH2 SH3 SHt. join_chunks SH1 SHt SHF.
    join_chunks MPC FT FRt. join_chunks FH FRt FRF.
    lazymatch type of RF with RFAKE _ ?st2 ?mb =>
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (SHF' : rw_cells asegs mc (sh (ff_addr (fs_newff FI st 0))) (shadow_cells (repeat 245 (Z.to_nat (ff_shsize (fs_newff FI st 0))))))
        by (change (ff_addr (fs_newff FI st 0)) with F; change (sh F) with SF; unfold ff_shsize; rewrite FCLS; exact SHF);
      destruct (release FI st2 (fs_newff FI st 0) (fs_live FI st) mb mc _ RF LIVE1 MU0 WM0 FLG SHF' FRF
                  ltac:(unfold ff_size; rewrite FCLS; reflexivity)) as [RF3 LIVE3]
    end end.
    clear RF MU0 WM0 SHF'.

    step.   step.   step.
    do 13 step.
    step.   step.

    match goal with P : stk asegs _ lo q' |- _ => release_frame QC P (q' + 24)%Z end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with A : stk asegs mm lo (q' + 24)%Z, B : stk asegs mm (q' + 24)%Z _ |- _ =>
        pose proof (stk_merge asegs mm _ _ _ A B ltac:(lia)) as STm; clear A B end end.
    release_frame FRhi STm q.
    unfold map_str_to_int_post_A. finish.
    { rewrite LIVE3. reflexivity. }
    { exact RF3. }
  Qed.

  #[using="TAB tok ws CLO"] Lemma W0_fsw : Forall (fsw_iv FI) W0.
  Proof.
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    constructor; [left; apply app_iv_stack; lia|]. constructor; [left; exact (fsb_app_iv FI)|]. constructor; [right; cbn [fst snd]; lia| constructor].
  Qed.

  #[using="HC T n TAB lo tok ws q TL N1 THI TABLO CLO LO AL16"] Lemma srliw_halfA : forall x, 0 <= x < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 1) = x / 2.
  Proof.
    intros x Hx. unfold bv_swrap, bv_wrap.
    change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
    rewrite (Z.mod_small x) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
    rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="HC T n TAB lo tok ws q TL N1 THI TABLO CLO LO AL16"] Lemma sdiv2_halfB : forall x, 0 <= x < 2^31 ->
    bv_swrap 32 (Z.shiftr (bv_swrap 32 ((x + bv_swrap 32 (Z.shiftr (bv_wrap 32 x) 31)) mod 18446744073709551616)) 1) = x / 2.
  Proof.
    intros x Hx. unfold bv_swrap, bv_wrap.
    change (bv_modulus 32) with (2^32). change (bv_half_modulus 32) with (2^31).
    rewrite (Z.mod_small x (2^32)) by lia. rewrite (Z.shiftr_div_pow2 x 31) by lia. rewrite (Z.div_small x (2^31)) by lia.
    change ((0 + 2 ^ 31) mod 2 ^ 32 - 2 ^ 31) with 0. rewrite Z.add_0_r. rewrite (Z.mod_small x) by lia.
    rewrite (Z.mod_small (x + 2^31)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
    rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
    rewrite Z.mod_small by lia. lia.
  Qed.

  #[using="TAB tok ws q"] Lemma slti_neg0B : forall x, 0 <= x < 2^31 ->
    (Z.lxor (bv_swrap 32 (x + 0) mod 18446744073709551616) 9223372036854775808 <? 9223372036854775807) = false.
  Proof.
    intros x Hx. rewrite Z.add_0_r, swrap32_id by lia. rewrite Z.mod_small by lia.
    change 9223372036854775808 with (2^63). rewrite zb_lxor_pow2_small by lia. apply Z.ltb_ge. lia.
  Qed.

  Notation LSTM pc q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 top bot x23 x28 x29 x30 x31 mm :=
    (MS (mkR x1 (wz q') gp tp x5 x6 x7 (wz q) (wz q') x10 x11 x12 x13 x14 x15 x16 x17
             (wz F) (wz TAB) (wz (-1)) (wz (F + 32)) (wz top) x23 (wz SF) (wz 0x7fff8000) (wz F) (wz bot) x28 x29 x30 x31)
        F_ (wz pc) fc None mm (seg_rom asegs)).

  #[using="TL N1 THI SHWT TFS LEN TABLO TABHI TABAL SHWTAB TS CLO LO AL16 QHI RF0"] Lemma probeM : forall (entry pc0 pcr : Z) (top bot q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m
      (Q : machine_state -> Prop),
    memptr_cmp_stmt_A_at entry ->
    (pc0 = 0x8e93c /\ pcr = 0x8e99c /\ entry = memptr_cmp_entryA) \/ (pc0 = 0x8e9c4 /\ pcr = 0x8ea24 /\ entry = memptr_cmp_nocase_entryA) ->
    0 <= top <= bot -> bot < ne -> minvM q' m ->
    (forall (r mid : Z) y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m', minvM q' m' -> -255 <= r <= 255 -> top <= mid <= bot ->
       evt asegs Q (MS (mkR y1 (wz q') gp tp y5 y6 y7 (wz q) (wz q') (wz r) y11 y12 y13 y14 y15 y16 y17
                            (wz F) (wz TAB) (wz (-1)) (wz (F + 32)) (wz top) (wz mid) (wz SF) (wz 0x7fff8000) (wz F) (wz bot) y28 y29 y30 y31)
                        F_ (wz pcr) fc None m' (seg_rom asegs))) ->
    evt asegs Q (LSTM pc0 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 top bot x23 x28 x29 x30 x31 m).
  Proof.
    intros entry pc0 pcr top bot q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m Q CMP SITE TB BN INV K.
    destruct INV as (Hq & ST & (jq & QC) & GAP & FRhi & FH & MPC & (j8 & FT) & SH1 & SH2 & SH3 & FLG & TOK & ARR & MI & MU & WM & FK & RF & AE & LIVE1).
    pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
    pose proof (fsb_ok FI) as (FSB1 & FSB2 & FSB3 & FSB4). unfold app_mem in FSB3.
    assert (ESF : SF = F / 8 + 2147450880) by reflexivity.
    assert (ESHB : sh (FSB FI) = FSB FI / 8 + 2147450880) by reflexivity.
    destruct (new_frame_facts FI st 0 m0 F SF FL RF0 ltac:(lia) eq_refl eq_refl eq_refl) as (FCLS & FLO & FHI & FAL & FLLO & FLHI & APART).
    cbn [FB_of SB_of] in FHI. clear APART.
    assert (LSUB : forall g, In g (fs_live FI st) -> In g (fs_live FI st1)) by (intros g Hg; rewrite LIVE1; right; exact Hg).
    pose proof (proj1 (bytes_at_bound _ _ _ _ (proj1 ARR))) as TB0. pose proof (bytes_at_bound _ _ _ _ TOK) as TKB.
    pose proof (shw_frame_fs FI W0 m0 m TAB (16 * ne) SHWTAB MU W0_fsw ltac:(left; lia)) as SHWTABm.
    pose proof (shw_frame_fs FI W0 m0 m T n SHWT MU W0_fsw ltac:(clear - TFS TL; lia)) as SHWTm.
    pose proof (munch_refl [(lo, q)]%Z m) as MU0. pose proof (wmono_refl asegs m) as WM0.
    destruct SITE as [(-> & -> & ->)|(-> & -> & ->)].
    - zstep. zstep.
      rewrite swrap32_id by lia. step. ubr.
      zstep. zstep. zstep.
      rewrite sdiv2_halfB by lia. set (mid := (top + bot) / 2).
      assert (MR : top <= mid <= bot) by (subst mid; split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
      clearbody mid.
      zstep. zstep.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
      ub_null.
      zstep. zstep. zstep. zstep. zstep.
      rewrite slti_neg0B by lia.
      replace (TAB + mid * 16 <? mid * 16) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
      step. lit_branch_safe.
      zstep. step. ubr_by ltac:(clear - KU TABAL; Z.div_mod_to_equations; lia).
      destruct (TS mid ltac:(lia)) as (S & str & slack & HN & STRm & NONUL & PAD & SLO & SHI & SHWS).
      pose proof (STRm m MI) as STR. pose proof (bytes_at_bound _ _ _ _ STR) as STB. rewrite length_app in STB. cbn [length] in STB.
      pose proof (u64arr_read asegs m TAB ws (2 * mid) (Z_to_bv 64 S) (Z_to_bv 64 (TAB + mid * 16)) ARR HN ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD.
      cstep. cstep. cstep. cstep.

      step. step. step.
      pose proof (shw_frame_fs FI W0 m0 m S (Z.of_nat (length str) + 1) SHWS MU W0_fsw ltac:(left; lia)) as SHWSm.
      assert (ESH : sh (F + 32) = SF + 4) by (unfold SF, sh, SHADOW_OFF; clear; Z.div_mod_to_equations; lia).
      eapply evt_cut.
      { eapply (CMP (F + 32) T n S lo tok str slack q');
          first [ exact MPC | exact TOK | exact STR | exact NONUL | exact PAD | exact AE | exact SHWTm | exact SHWSm | exact ST | exact MI | reflexivity
                | (rewrite ESH; exact SH2) | (unfold app_mem; lia) | (unfold A0_RT_STACK; lia) | (clear - FAL; Z.div_mod_to_equations; lia) | lia ]. }
      intros ms' PO. unfold memptr_cmp_post_A in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & -> & MUc & WMc & MI' & ST' & AE' & RR).

      pose proof MUc as MUt. pose proof WMc as WMt.
      fs_sync FI RF MUc WMc FK LSUB.
      clear ST STR RD SHWTABm SHWTm SHWSm AE MI.
      unfold memptr_cells in MPC. unfold shadow_zero_cells, shadow_cells in SH2. cbn [map repeat] in SH2.
      transport_after_call asegs m m' MUt WMt. clear MUt WMt.
      replace (ret_pc (Z_to_bv 64 584092)) with (Z_to_bv 64 584092) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply (K r mid); [| exact RR| exact MR].
      unfold H_map_str_to_int_seg.minvM, memptr_cells, shadow_zero_cells, shadow_cells. cbn [map repeat]. split; [exact Hq|].
      repeat (split; [first [eassumption | (eexists; eassumption)] |]). assumption.

    - zstep. zstep.
      rewrite swrap32_id by lia. step. ubr.
      zstep. zstep. zstep.
      rewrite sdiv2_halfB by lia. set (mid := (top + bot) / 2).
      assert (MR : top <= mid <= bot) by (subst mid; split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia).
      clearbody mid.
      zstep. zstep.
      rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
      ub_null.
      zstep. zstep. zstep. zstep. zstep.
      rewrite slti_neg0B by lia.
      replace (TAB + mid * 16 <? mid * 16) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [Z.b2z]. change (Z.lxor (Z.lxor 0 0) 1) with 1.
      step. lit_branch_safe.
      zstep. step. ubr_by ltac:(clear - KU TABAL; Z.div_mod_to_equations; lia).
      destruct (TS mid ltac:(lia)) as (S & str & slack & HN & STRm & NONUL & PAD & SLO & SHI & SHWS).
      pose proof (STRm m MI) as STR. pose proof (bytes_at_bound _ _ _ _ STR) as STB. rewrite length_app in STB. cbn [length] in STB.
      pose proof (u64arr_read asegs m TAB ws (2 * mid) (Z_to_bv 64 S) (Z_to_bv 64 (TAB + mid * 16)) ARR HN ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RD.
      cstep. cstep. cstep. cstep.
      step. step. step.
      pose proof (shw_frame_fs FI W0 m0 m S (Z.of_nat (length str) + 1) SHWS MU W0_fsw ltac:(left; lia)) as SHWSm.
      assert (ESH : sh (F + 32) = SF + 4) by (unfold SF, sh, SHADOW_OFF; clear; Z.div_mod_to_equations; lia).
      eapply evt_cut.
      { eapply (CMP (F + 32) T n S lo tok str slack q');
          first [ exact MPC | exact TOK | exact STR | exact NONUL | exact PAD | exact AE | exact SHWTm | exact SHWSm | exact ST | exact MI | reflexivity
                | (rewrite ESH; exact SH2) | (unfold app_mem; lia) | (unfold A0_RT_STACK; lia) | (clear - FAL; Z.div_mod_to_equations; lia) | lia ]. }
      intros ms' PO. unfold memptr_cmp_post_A in PO.
      destruct PO as (y5 & y6 & y7 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m' & r & -> & MUc & WMc & MI' & ST' & AE' & RR).
      pose proof MUc as MUt. pose proof WMc as WMt.
      fs_sync FI RF MUc WMc FK LSUB.
      clear ST STR RD SHWTABm SHWTm SHWSm AE MI.
      unfold memptr_cells in MPC. unfold shadow_zero_cells, shadow_cells in SH2. cbn [map repeat] in SH2.
      transport_after_call asegs m m' MUt WMt. clear MUt WMt.
      replace (ret_pc (Z_to_bv 64 584228)) with (Z_to_bv 64 584228) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      apply (K r mid); [| exact RR| exact MR].
      unfold H_map_str_to_int_seg.minvM, memptr_cells, shadow_zero_cells, shadow_cells. cbn [map repeat]. split; [exact Hq|].
      repeat (split; [first [eassumption | (eexists; eassumption)] |]). assumption.
  Qed.

  #[using="IC TL N1 TLO THI SHWT TFS TBAND LEN TABLO TABHI TABAL SHWTAB TS CLO LO AL16 QHI RF0"] Lemma loopMA : forall (k : nat) (top bot q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m,
    bot - top < Z.of_nat k -> 0 <= top <= bot -> bot < ne -> minvM q' m ->
    evt asegs POST (LSTM 0x8e93c q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 top bot x23 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros top bot q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m HK TB BN INV; [lia|].
    eapply (probeM memptr_cmp_entryA 0x8e93c 0x8e99c top bot q'); [exact (memptr_cmp_spec_A IC)| left; repeat split| exact TB| exact BN| exact INV|].
    intros r mid y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' INV' RR MR.
    pose proof (munch_refl [] m') as MUx.
    zstep. if_cases K1; zify_cond K1.
    -
      zstep. rewrite swrap32_id by lia. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia.
      +   apply (exitM (-1) q'); [exact INV'| left; reflexivity].
      + eapply (IH (mid + 1) bot q'); [lia| lia| lia| exact INV'].
    - zstep. if_cases K4; zify_cond K4.
      +
        zstep. apply (exitM mid q'); [exact INV'| right; lia].
      +
        zstep. rewrite swrap32_id by lia. zstep. if_cases K5; zify_cond K5; rewrite ?signed_lit in K5 by lia.
        * eapply (IH top (mid + -1) q'); [lia| lia| lia| exact INV'].
        * zstep. apply (exitM (-1) q'); [exact INV'| left; reflexivity].
  Qed.

  #[using="IC TL N1 TLO THI SHWT TFS TBAND LEN TABLO TABHI TABAL SHWTAB TS CLO LO AL16 QHI RF0"] Lemma loopMB : forall (k : nat) (top bot q' : Z) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m,
    bot - top < Z.of_nat k -> 0 <= top <= bot -> bot < ne -> minvM q' m ->
    evt asegs POST (LSTM 0x8e9c4 q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 top bot x23 x28 x29 x30 x31 m).
  Proof.
    induction k as [|k IH]; intros top bot q' x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 m HK TB BN INV; [lia|].
    eapply (probeM memptr_cmp_nocase_entryA 0x8e9c4 0x8ea24 top bot q'); [exact (memptr_cmp_nocase_spec_A IC)| right; repeat split| exact TB| exact BN| exact INV|].
    intros r mid y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 m' INV' RR MR.
    pose proof (munch_refl [] m') as MUx.
    zstep. if_cases K1; zify_cond K1.
    -
      zstep. rewrite swrap32_id by lia. zstep. if_cases K3; zify_cond K3; rewrite ?signed_lit in K3 by lia.
      +   apply (exitM (-1) q'); [exact INV'| left; reflexivity].
      + eapply (IH (mid + 1) bot q'); [lia| lia| lia| exact INV'].
    - zstep. if_cases K4; zify_cond K4.
      +
        zstep. apply (exitM mid q'); [exact INV'| right; lia].
      +
        zstep. rewrite swrap32_id by lia. zstep. if_cases K5; zify_cond K5; rewrite ?signed_lit in K5 by lia.
        * eapply (IH top (mid + -1) q'); [lia| lia| lia| exact INV'].
        * zstep. apply (exitM (-1) q'); [exact INV'| left; reflexivity].
  Qed.

  #[using="IC STACK_MALLOC_0 TL N1 TLO THI SHWT TFS TBAND LEN NE TABLO TABHI TABAL SHWTAB TS CLO LO AL16 QHI RF0 FCO FE0"] Lemma bodyM : forall (cs : Z) t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
    bytes_at asegs m0 T tok -> u64arr asegs m0 TAB ws ->
    stk asegs m0 lo q -> mem_inv asegs m0 -> asan_env asegs m0 -> 0 <= cs < 2^64 ->
    evt asegs POST
      (MS (mkR ra (wz q) gp tp t0 t1 t2 s0 s1 (wz T) (wz n) (wz TAB) (wz ne) (wz cs) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz map_str_to_int_entryA) fc None m0 (seg_rom asegs)).
  Proof.
    intros cs t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 TOK ARR ST MI AE CS.
    eapply (prologueM cs); try eassumption.
    intros q' m x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 INV.
    pose proof (munch_refl [] m) as MUx.
    zstep. if_cases Kb; zify_cond Kb. { exfalso. rewrite ?signed_lit in Kb by lia. lia. }
    zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - assert (cs = 0) by lia. subst cs.
      step. ubr.
      zstep. zstep.
      eapply (loopMB (Datatypes.S (Z.to_nat ne)) 0 (ne + -1) q'); [lia| lia| lia| exact INV].
    - step. ubr.
      zstep. zstep. eapply (loopMA (Datatypes.S (Z.to_nat ne)) 0 (ne + -1) q'); [lia| lia| lia| exact INV].
  Qed.
End WALK.

#[using="IC STACK_MALLOC_0"] Lemma map_str_to_int_spec_A : map_str_to_int_stmt_A.
Proof.
  unfold map_str_to_int_stmt_A. intros T n TAB ne cs lo tok ws st ra q gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m.
  intros TOK TL N1 TLO THI SHWT TFS TBAND ARR LEN NE TABLO TABHI TABAL SHWTAB TS ST CLO LO AL16 QHI MI AE RF FCO FE CS -> -> -> -> ->.
  unfold A0_RT_STACK in LO.
  eapply (bodyM T n TAB ne lo tok ws st); eauto.
Qed.

End W.
