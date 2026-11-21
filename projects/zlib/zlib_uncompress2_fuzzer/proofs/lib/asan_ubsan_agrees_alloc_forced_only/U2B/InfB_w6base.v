(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2B Require Import U2BObj U2BClient U2BIface U2BGlue InfBBase InfBKit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition st_cin (st : ist) (c : Z) : ist :=
  IST (t_mode st) (t_last st) (t_flags st) c (t_cout st) (t_hold st) (t_bits st) (t_out st) (t_ret st) (t_length st) (t_offset st) (t_extra st)
      (t_lc st) (t_dc st) (t_lb st) (t_db st) (t_ncode st) (t_nlen st) (t_ndist st) (t_shave st) (t_nx st) (t_whave st) (t_wnext st).
Lemma st_cin_id : forall st, st_cin st (t_cin st) = st.
Proof. intros []; reflexivity. Qed.

Ltac inf_arm_open_sn :=
  lazymatch goal with
  | CTX : inf_ctx ?cx ?ly ?AI ?RNG ?LB, HID : inf_hid ?cx ?ly ?AI ?L ?RNG ?stA ?LB _ _ _ _ _ _ ?m,
    VIS : inf_vis ?cx ?ly (st_cin ?st ?cs) _ _ _ _ ?payload _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m,
    RNH : IDefs.RNG ?cx ?st _ _, PLEN : Z.of_nat (length ?payload) = _ |- _ =>
      pose proof CTX as CTX0;
      let AH := fresh "AH" in
      pose proof HID as (AH & SHZ & SHS & SHO & _ & UNP & _ & _ & _ & _ & _ & _ & _ & _ & SHLF & SHDF & SHOR & SHO6 & _);
      pose proof (inf_facts AI L RNG stA LB cx ly m AH CTX) as LIN0;
      pose proof (inf_dj AI RNG LB cx ly CTX LIN0) as (DJZ & DJS & DJO & DJP & DJLF & DJDF & DJOR & DJO6 & DJIT);
      let LIN := fresh "LIN" in
      pose proof LIN0 as LIN;
      destruct LIN as (Fu & ZSE & FU256 & HFU & (S1 & S2 & bS & BS0 & BS1 & BS2) & (U1 & U2 & bU & BU0 & BU1 & BU2) & (F1 & F2 & bF & BF0 & BF1 & BF2)
                       & DL1 & DL2 & (bD & BD0 & BD1 & BD2) & (cSU & CSU0 & CSU1 & CSU2) & (cSF & CSF0 & CSF1 & CSF2) & (cUF & CUF0 & CUF1 & CUF2)
                       & (cSD & CSD0 & CSD1 & CSD2) & (cUD & CUD0 & CUD1 & CUD2) & (cFD & CFD0 & CFD1 & CFD2));
      destruct CTX as (S16 & SB & _ & _ & RZ & RSZ & HF0 & F064 & F0B & RS & RSS & OBE & OSZ & OCI & ROB & ROBS & WDC
                       & D1 & NR & D16 & RD & RSD & LOC & LOS & SPAR & SPA32 & SP16 & SPT & RSTK & RI & RISH & RSFU & TABC1 & TABC2 & LBABLK);
      let VF := fresh "VISf" in pose proof VIS as VF;
      destruct VIS as (FRM & STRM & SSC & LENS & WORK & CODES & TAIL & OUT & PAYB & STK & MI & MNE & BKOK);
      destruct cx as [u S D n OB osz Wd cin0 cout0 W0 K0 zc]; destruct ly as [SP SPA Zs F0 lo];
      destruct st as [mode last flags cin cout hold bits out ret len offset extra lc dc lb db ncode nlen ndist shave nx whave wnext];
      unfold st_cin in *;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
           t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
           t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext l_SP l_SPA l_Zs l_F0 l_lo] in *;
      let RN := fresh "RN" in
      pose proof RNH as RN; unfold IDefs.RNG in RN;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc
           t_mode t_last t_flags t_cin t_cout t_hold t_bits t_out t_ret t_length t_offset t_extra
           t_lc t_dc t_lb t_db t_ncode t_nlen t_ndist t_shave t_nx t_whave t_wnext] in RN;
      repeat (let F := fresh "R" in destruct RN as [F RN]);
      unfold inf_locals, strm_cells, istate_cells, itail_cells, inf_W in *;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w c_cin0 c_cout0 c_W0 c_K c_zc l_SP l_SPA l_Zs l_F0 l_lo] in *;
      atop_facts; unfold KEND in SPT; subst OB; unfold A_OUTBUF in *;
      assert (Z8 : Zs mod 8 = 0) by (clear - ZSE FU256; Z.div_mod_to_equations; lia);
      assert (S8 : S mod 8 = 0) by (clear - S16; Z.div_mod_to_equations; lia);
      assert (PL : Z.of_nat (length (map (Z_to_bv 8) payload)) = n) by (rewrite length_map; exact PLEN);
      assert (RFRM : rng RNG SPA 568) by (eapply rng_sub'; [exact RSTK| lia]);
      pose proof (munch_refl [(lo, SPA + 568); (Zs, Zs + 112); (S, S + 7176); (6341696, 6341696 + osz)] m) as MU;
      pose proof (wmono_refl bsegs m) as WM;
      hide_or WDC;
      try (match goal with HF : _ = 0 \/ _ = -1 |- _ => hide_or HF end)
  end.

Ltac inf_arm_open_s :=
  lazymatch goal with
  | VIS : inf_vis ?cx _ (st_cin ?st _) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SI : sinv ?cx ?st _ _ |- _ =>
      let RN0 := fresh "RN0" in
      pose proof (proj1 SI) as RN0; inf_arm_open_sn; clear RN0
  end.
Ltac inf_vis_close_sn := unfold st_cin; inf_vis_close.
