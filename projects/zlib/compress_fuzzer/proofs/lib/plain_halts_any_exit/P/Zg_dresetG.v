(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Zlib_iface Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_adler32 F_memset Z_dinit_kit Z_dreset Zg_cfgtab.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees DeflateLz Deflate RefDeflateInitLib FillWinModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Section RESETG.
  Hypothesis HTRI : tr_init_stmt.

  Lemma deflateResetG_spec : forall (L : dlay) (s : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word) (lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    DSTi m L s ->
    rw_cells psegs m (dl_S L) (zs_raw (dl_As L) ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    relro_clean m ->
    deflateStateCheck s = false -> 0 <= ds_wrap s <= 1 ->
    0 <= ds_level s <= 9 -> ds_w_size s = 32768 -> ds_hash_size s = 32768 -> ds_matches s = 0 -> ds_gzhead s = 0 ->
    stk psegs m lo (bv_unsigned sp) -> dlay_below L lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_DRESET_STACK ->
    mem_inv psegs m ->
    a0 = wz (dl_S L) ->
    evt psegs (dreset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s ni ai no ao p1 p2 opq p3 resv lo m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz Z_DRESET) fc None m (seg_rom psegs)).
  Proof.
    intros until m. intros ST ZS RC CHK WR HLV HW HH HM0 HGZ STK BEL LOSP MI ->.
    pose proof (st_lay _ _ _ _ ST) as LAY. lay_open LAY. pose proof BEL as BEL'. below_open BEL'.
    unfold Z_DRESET_STACK in LOSP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUh : bv_unsigned (wz (dl_Ah L)) = dl_Ah L) by (apply unsigned_lit; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] m) as MU.
    pose proof (wmono_refl psegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUf.
    unfold Z_DRESET.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* 1.4: + sd s2,0(sp) *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (ST0 : DSTi mm L s) end.
    { lazymatch goal with |- DSTi ?mm _ _ => apply (DSTi_agree m mm) end; [exact ST|].
      eapply ag_blocks_munch; [exact LAY| exact MUf| exact WM| | | | |]; cbn [disjoint_from]; slia. }
    clear MUf ST.
    call (deflateResetKeep_spec HTRI L s ni ai ti no ao to p1 p2 msg opq dt p3 adl resv lo).
    1:{ exact ST0. } 1:{ exact ZS. } 1:{ exact CHK. } 1:{ exact WR. } 1:{ exact HM0. } 1:{ exact HGZ. } 1:{ rewrite E32. exact STK. }
    1:{ rewrite E32. unfold dlay_below in *. lia. } 1:{ rewrite E32. lia. } 1:{ exact MI. } 1:{ reflexivity. }
    subst x2. rewrite E32 in PC. rename PC into STK. rename PC1 into ZS. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. clear ST0.
    remember (RK1 s) as X eqn:EX.
    assert (EWX : ds_w_size X = 32768) by (subst X; exact HW).
    assert (EHX : ds_hash_size X = 32768) by (subst X; exact HH).
    assert (RLX : 0 <= ds_level X <= 9) by (subst X; exact HLV).
    assert (RLX' : - 2^31 <= ds_level X < 2^31) by lia.
    pose proof (cfg_ranges (ds_level X)) as (Rg & Rl & Rn & Rc).
    open_DST POST. open_A GA. open_D GD. rewrite EWX, EHX in GA.

    unfold dhead, u16arr in Ghead.
    pose proof (av16_zlength (ds_head X) 32768 ltac:(lia)) as LH.
    destruct (u8arr_split3 _ (dl_Ah L) _ (Z.to_nat 65534) 2 Ghead ltac:(lia)) as (H1 & H2 & _). clear Ghead.
    replace (dl_Ah L + Z.of_nat (Z.to_nat 65534)) with (dl_Ah L + 65534) in H2 by lia.
    apply rw_cells_of_u8arr in H1. rewrite length_firstn, Nat.min_l in H1 by lia.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968); (dl_Ah L, dl_Ah L + 65536)] x14) as MUf.
    pose proof (wmono_refl psegs x14) as WMf.
    zstep. if_true.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4: + lui / addw / add s2 = s + 5928 *)
    zs.
    zs. zs. zs. zs.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [eapply memset_callZ with (D := dl_Ah L) (C := 0) (N := 65534); [exact H1| eassumption| lia| lia| lia| lia] | post_call segs mm] end.
    lazymatch type of POST with rw_cells _ ?mm _ _ => rename mm into mhd end.
    pose proof (dhead_LM_cleared mhd L X EHX LENS POST H2) as Ghead.
    clear POST H2.
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112); (dl_As L, dl_As L + 212); (dl_As L + 5881, dl_As L + 5968)] mhd) as MUg.
    pose proof (wmono_refl psegs mhd) as WMg.
    zs. zs.
    (* 1.4 lm_init: sd zero,0(s2) clears matches and insert (5928..5936); sw zero,32(s2) clears slid (5960, a junk cell) *)
    merge44 GD 8%nat. zs. split8 GD 8%nat.
    zs.
    zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (RC' : relro_clean mm) end.
    { eapply relro_clean_munch; [exact RC| exact MU|]. unfold RELRO_LO, RELRO_HI. cbn [disjoint_from].
      destruct (lo_s L LAY) as (_ & _ & _ & Ds). destruct (lo_h L LAY) as (_ & _ & _ & Dh). lia. }

    pose proof (configG_relro _ (ds_level X) RC' RLX) as CFG.

    replace (Z_CFG_TABLEG + 16 * ds_level X) with (ds_level X * 16 + Z_CFG_TABLEG) in CFG by lia. unfold Z_CFG_TABLEG in CFG.
    zs.
    rewrite (Z.shiftl_mul_pow2 (ds_level X) 4) by lia. change (2^4) with 16.
    zs.

    let b := eval cbv in Z_CFG_TABLEG in replace (wz (b + ds_level X * 16)) with (wz (ds_level X * 16 + b)) by (f_equal; lia).
    zs. zs. zs. zs. zs.
    rewrite !zx16_small by lia.
    zs. zs. zs. zs. zs. zs. zs. zs. zs.
    merge44 GA 31%nat.
    zs.
    split8 GA 31%nat.
    zs. zs. zs. zs. zs. zs. (* 1.4: + ld s2 *)
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold dreset_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [lazymatch goal with H : mem_inv psegs ?mm |- mem_inv psegs ?mm => exact H end|].
    split; [exact STK|]. split; [reflexivity|].
    split; [unfold zs_raw, zs_pub; cbn [app]; exact ZS|].
    rewrite <- LM_RK1, <- EX. tr_groups MUf WMf. tr_groups MUg WMg.

    constructor.
    - abstract (do 5 eexists; unfold dsA_cells, LM, clear_hash; dsred; rewrite EWX, EHX; unfold MIN_MATCH;
      change (3 - 1) with 2; change (2 * 32768) with 65536; close_cells GA).
    - abstract (exact GB).
    - abstract (exact GC).
    - assert (EMX : ds_matches X = 0) by (rewrite EX; reflexivity).
      abstract (do 5 eexists; unfold dsD_cells, LM, clear_hash; dsred; close_cells GD; rewrite EMX; reflexivity).
    - abstract (exact Glt).
    - abstract (exact Gdt).
    - abstract (exact Gbt).
    - abstract (exact Gblc).
    - abstract (exact Gheap).
    - abstract (exact Gdep).
    - abstract (exact Gwin).
    - abstract (exact Gprev).
    - abstract (exact Ghead).
    - abstract (exact Gpend).
    - destruct LENS as [l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13].
      abstract (constructor; unfold LM, clear_hash; dsred; rewrite ?arr_len_fill, ?arr_len_set; [exact l1|exact l2|exact l3|exact l4|exact l5|exact l6|exact l7|exact l8|exact l9|exact l10|exact l11|exact l12|exact l13]).
    - exact LAY.
  Qed.
End RESETG.
