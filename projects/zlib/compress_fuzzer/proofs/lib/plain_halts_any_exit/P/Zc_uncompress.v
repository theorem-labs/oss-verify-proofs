(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiC ZHarnessC ZInstC ZTargetC Target Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue F_stdio_exit Drv_kit Zlib_iface Zh_kit Zc_kit Zc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section UNC.
  Hypothesis U2 : runcompress2_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.

  Theorem uncompress_proof : runcompress_stmt.
  Proof.
    unfold runcompress_stmt. intros until canary.
    intros ENV INU UC UCL PLC PLLO PLHI PL8 INC CC CCL CF SL SRC NEQ DL CLB LOSP SP16 FRM -> -> -> ->.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof ENV as (HP0 & LXS0 & ZLS0 & SEW0 & SSP0 & AUX0 & SPB & B63 & ST0 & LOC & LOG & ERR0 & TP & MI0).
    pose proof LOSP as LOSP0. unfold ZC_UNC_STACK, ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK, GLOBALS_TOP in LOSP, LOG.

    pose proof (HBR _ _ _ _ HP0 INU) as (U0 & _ & _ & UCEIL & UIMG).
    pose proof (HBR _ _ _ _ HP0 INC) as (C0 & _ & _ & CCEIL & CIMG). cbn [blk_addr blk_size fst snd] in U0, UCEIL, UIMG, C0, CCEIL, CIMG.
    assert (LU : Z.of_nat (length (to_bytes uc)) = dlen) by (rewrite to_bytes_len; unfold zlength in UCL; lia).
    assert (LC : Z.of_nat (length (to_bytes comprc)) = cl) by (rewrite to_bytes_len; unfold zlength in CCL; lia).
    apply box in UC. apply box in CC.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold ZC_UNCOMPRESS. cbv beta delta [MallocRep.wz].
    (* 1.4 (zl14-cmp): uncompress keeps a 32-byte frame: sp+0 = sourceLen (used), sp+8 = *destLen (got), s0 = destLen
       pointer, ra; it calls uncompress2_z (ZC_UNCOMPRESS2) with &got / &used and stores got back through s0. *)
    zstep. carve_frame 32%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 32 junk [] [8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 9 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (E32 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv canary).
    { eapply (lx_env_munch _ m m1); [exact HFRAME| exact ENV| exact MU| exact WM| assumption| rewrite E32; assumption| rewrite E32; lia| |].
      - constructor; [| constructor]. left. cbn [fst]. lia.
      - intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (UC1 : u8arr psegs m1 U (to_bytes uc)).
    { eapply u8arr_agree; [exact AG1| exact (unbox _ UC)|]. intros a Ha. cbn [outside]. lia. }
    assert (CC1 : u8arr psegs m1 C (to_bytes comprc)).
    { eapply u8arr_agree; [exact AG1| exact (unbox _ CC)|]. intros a Ha. cbn [outside]. lia. }
    rename PLC into PLC1.
    assert (PRES1 : lx_pres LB (bv_unsigned sp) [(U, U + dlen); (PL, PL + 8)] m m1).
    { eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
      - lia.
      - pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _). lia.
      - lia. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s (runcompress_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB U dlen PL uc lo B canary m) msx) end.
    lazymatch goal with FRx : rw_cells psegs m1 (bv_unsigned sp + -32) [C8 ?vslen; C8 ?vdl; C8 ?vs0; C8 ?vra] |- _ =>
      apply (rw_cells_app psegs m1 (bv_unsigned sp + -32) [C8 vslen] [C8 vdl; C8 vs0; C8 vra]) in FRx; destruct FRx as [FS1 FRx];
      cbn [cells_size csize Nat.add] in FRx;
      apply (rw_cells_app psegs m1 (bv_unsigned sp + -32 + 8) [C8 vdl] [C8 vs0; C8 vra]) in FRx; destruct FRx as [FL1 FRA1];
      cbn [cells_size csize Nat.add] in FRA1 end.
    eapply implM_post_evt'.
    { eapply (U2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 s LB up cpS U dlen (bv_unsigned sp + -32 + 8) C cl slen (bv_unsigned sp + -32) uc comprc src lo B errv canary);
        rewrite ?E32;
        [ exact ENV1 | exact INU | exact UC1 | exact UCL | exact FL1 | lia | lia | clear - SP16 RSP; Z.div_mod_to_equations; lia
        | exact INC | exact CC1 | exact CCL | exact CF | exact SL | exact SRC
        | exact FS1 | lia | lia | clear - SP16 RSP; Z.div_mod_to_equations; lia
        | lia | exact NEQ | exact DL | exact CLB
        | unfold ZC_WRAP_STACK, Z_INFLATE_STACK, RMALLOC_STACK; lia | clear - SP16 RSP; Z.div_mod_to_equations; lia | exact FRM
        | reflexivity | first [reflexivity | f_equal; rewrite ?E32; lia] | reflexivity | first [reflexivity | f_equal; rewrite ?E32; lia] ]. }
    cbv beta. intros r s' ms' PO. unfold runcompress2_post in PO.
    destruct PO as (x0 & x1 & x2 & e0 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & x3 & x4 & x5 & x6 & F' & fc' & m' & rc & slen' & -> & LPE & HA0 & HRC & HRR & UC' & LEN' & LEN2 & PLC' & PSC').
    replace (ret_pc (Z_to_bv 64 0x1ced8)) with (Z_to_bv 64 0x1ced8) by (symmetry; rpc).
    destruct LPE as ((errv' & ENV') & FRM' & PRES' & ESO' & EFA').
    pose proof ENV' as (HP' & _ & _ & _ & _ & _ & _ & _ & ST' & _ & _ & _ & _ & MI').
    rewrite E32 in ST', PRES'.

    assert (FRA' : rw_cells psegs m' (bv_unsigned sp + -32 + 8 + 8) [C8 s0; C8 ra]).
    { eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES')| exact FRA1|].
      intros a Ha. cbn in Ha. split; [| left; lia]. cbn [rin_ivs fst snd]. lia. }
    assert (PLC2 : rw_cells psegs m' PL [C8 (Z_to_bv 64 dlen)]).
    { eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PRES')| exact PLC1|].
      pose proof (HBR _ _ _ _ HP0 INU) as (_ & _ & _ & UCB & _). cbn [blk_addr blk_size fst snd] in UCB.
      intros a Ha. cbn in Ha. split; [| left; lia]. cbn [rin_ivs fst snd]. lia. }
    assert (FR2 : rw_cells psegs m' (bv_unsigned sp + -32) [C8 (Z_to_bv 64 slen'); C8 (Z_to_bv 64 (snd (fst r))); C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app psegs m' (bv_unsigned sp + -32) [C8 (Z_to_bv 64 slen')] [C8 (Z_to_bv 64 (snd (fst r))); C8 s0; C8 ra])).
      split; [exact PSC'|]. cbn [cells_size csize Nat.add].
      apply (proj2 (rw_cells_app psegs m' (bv_unsigned sp + -32 + 8) [C8 (Z_to_bv 64 (snd (fst r)))] [C8 s0; C8 ra])).
      split; [exact PLC'| cbn [cells_size csize Nat.add]; exact FRA']. }
    clear FRA' PSC' PLC'.
    pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp); (PL, PL + 8)] m') as MU'. pose proof (wmono_refl psegs m') as WM'.
    apply box in UC'.
    (* ld a1,8(sp); sd a1,0(s0): destLen's target := got *)
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (ENV2 : lx_env m2 s' [] LB (Z_to_bv 64 (bv_unsigned sp + -32)) tp B lo errv' canary).
    { eapply (lx_env_munch _ m' m2); [exact HFRAME| exact ENV'| exact MU'| exact WM'| assumption| rewrite E32; assumption| rewrite E32; lia| |].
      - constructor; [| constructor; [| constructor]]; left; cbn [fst]; lia.
      - intros a Ha. cbn [outside]. lia. }
    assert (UC2 : u8arr psegs m2 U (to_bytes (zstore uc 0 (fst (fst r))))).
    { eapply u8arr_agree; [exact (agree_on_of_munch _ _ _ MU' WM')| exact (unbox _ UC')|]. intros a Ha. cbn [outside].
      pose proof (HBR _ _ _ _ HP0 INU) as (_ & _ & _ & UCB & _). cbn [blk_addr blk_size fst snd] in UCB.
      rewrite to_bytes_len in Ha. pose proof (zstore_length (fst (fst r)) uc 0) as ZL. unfold zlength in ZL, UCL. lia. }
    assert (PRESst : lx_pres LB (bv_unsigned sp) [(U, U + dlen); (PL, PL + 8)] m' m2).
    { eapply lx_pres_of_munch; [exact MU'| exact WM'|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; cbn [outside].
      - cbn [rin_ivs fst snd] in HX. lia.
      - pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _). cbn [rin_ivs fst snd] in HX. lia.
      - cbn [rin_ivs fst snd] in HX. lia. }
    (* ld ra,24(sp); ld s0,16(sp); add sp,sp,32 *)
    zstep. zstep. zstep.
    release_frame FR2 ST' (bv_unsigned sp).
    zstep.
    apply evt_done. unfold runcompress_post.
    do 15 eexists. exists F', fc', m2, rc. split; [reflexivity|].
    split.
    { unfold lx_post_env. split; [exists errv'; eapply lx_env_sp; [exact ENV2| exact ST'| exact SPB]|].
      split; [exact FRM'|]. split; [| split; [exact ESO'| exact EFA']].
      eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_trans; [| exact PRESst].
      eapply lx_pres_sub; [exact PRES'|]. intros a [HX Hc]. split.
      - cbn [rin_ivs fst snd] in HX |- *. intros [H1|[H2|[H3|[]]]]; [apply HX; left; exact H1| |].
        all: destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| | lia].
        all: pose proof (HBR _ _ _ _ HP0 Hb) as (_ & _ & _ & BC & _); lia.
      - destruct Hc as [Hc|Hc]; [left; lia| right; exact Hc]. }
    split; [exact HA0|]. split; [exact HRC|]. split; [exact HRR|].
    split; [exact UC2|]. split; [exact LEN'|]. split; [exact LEN2| exact PLC2].
  Qed.
End UNC.
End WithCeiling0.
