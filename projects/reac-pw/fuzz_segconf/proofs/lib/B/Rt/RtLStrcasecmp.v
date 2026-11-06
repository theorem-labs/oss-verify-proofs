(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_ubjson_encoder/lib/S8/AsanAcct.v, with its module paths and module names changed; 403 of its 523 lines of code are new or changed and 1138 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/FMbz_clean.v, with its module paths and module names changed; 344 of its 386 lines of code are new or changed and 481 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/A/HPgWrapNcmp.v's hd_strncmp_core (itself reac-pw/fuzz_pin's
   lib/A/PPgWrapNcmp.v pin_strncmp_core at 90722657971) re-run with the caller's frame hole of lib/A/HPgHole.v
   (ecall_preH in, the hole post out), as lib/A/Rt/FMrt_lift.v rt_post_roU_win re-runs rt_post_ro_win with
   lib/A/Rt/FMupoison.v ARU_frame: hd_rt_post_roH_win is rt_post_roU_win with HPgHole.ARH_frame in place of
   ARU_frame; the walk's premises that AR gives (the stack window, the runtime cells, the read-only views) are read
   off AR of the unpoisoned memory and carried to the memory itself, which agrees with it off the hole; the rest
   is pin's proof. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgWrapNcmpH.v, with its module paths and module names changed; 210 of its 305 lines of code are new or changed and 291 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Rt/RtLStrncmp.v; 263 of its 353 lines of code are new or changed and 215 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Rt/RtLStrncasecmp.v, with its module paths and module names changed; 67 of its 137 lines of code are new or changed and 283 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLStrcasecmp.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* reac-pw/fuzz_segconf image B, interface row 10: the strcasecmp contract RtSeg.astrcasecmp_realizes (lib/A/Rt/RtSeg.v,
   accepted by the contracts' owner of record 2026-10-30T17:27Z, 80d098bd1905) at SegRtPC.PC_strcasecmp = 0x43aa8, from the wrapper walk
   lib/A/Bz/A/I_strcasecmp.v istrcasecmp_spec (its range check's Section hypothesis discharged by the kit's
   A/Bz/A/R_isPoisoned.v rip_proof), through fuzz_command's relocated bridge (RtBz*.v), the way fuzz_command's
   lib/A/Rt/RtLStrncmpR.v proves RtString.astrncmp_realizes:
   - the strings: the walk reads scc_sz <= len + 1 bytes of each (RtLStrcasecmpM.scc_ok_cstr), inside the
     contract's aread_ok over len + 1 bytes, so its byte lists are the whole strings with their NULs;
   - the answer: the walk returns scc_res, 0 exactly when the strings with their NULs agree under RtSeg.lc
     (RtLStrcasecmpM.scc_res_zero_iff);
   - the path: TryAsanInitFromRtl answers 1 (the asan-inited byte, from the frame's cells), so the arm through
     real_strcasecmp to musl strcasecmp 0x9b0cc is not taken (I_strcasecmp.v).
   The closing seg_strcasecmp_closed leaves only SegBSyms B (the kit's AR laws by YG0q.AR_laws_ok), as
   fuzz_command's lib/A/Rt/RtClosed.v:81-82 does for strncmp. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import
RtDefs RtBzHBase RtBzHStr RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP RtLStrncmp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg SegRtPC RtLStrcasecmpM.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strcasecmpm.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strcasecmp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module SCP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Module CM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strcasecmpm.
Module CW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strcasecmp.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module CB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtLStrcasecmpM.

(* ---- the contract, under the kit's AR laws ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

Theorem seg_strcasecmp : RtSeg.astrcasecmp_realizes tfibsegs B SegRtPC.PC_strcasecmp.
Proof.
  unfold RtSeg.astrcasecmp_realizes, SegRtPC.PC_strcasecmp.
  intros ly S W regs mem md x y sx sy HPRE G10 G11 Hx Hy SX SY RDX AMX RDY AMY TX TY HROM.
  pose proof HPRE as (HEP & HSLO & HPRS).
  pose proof HEP as (HAR & _).
  pose proof RDX as (RX0 & RX1 & RX2 & _).
  pose proof RDY as (RY0 & RY1 & RY2 & _).
  pose proof AMX as AMX'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMX'.
  pose proof AMY as AMY'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMY'.
  unfold astr_len in *.
  (* ---- the answer ---- *)
  destruct (CB.scc_ok_cstr sx sy (proj2 SX)) as (OK & SZ1 & SZ2).
  pose proof (CB.scc_res_zero_iff sx sy (proj2 SX) (proj2 SY)) as ANS.
  pose proof (CB.scc_res_range (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) as RNG.
  (* ---- the cleaned store ---- *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (RtBzClean.mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  destruct (stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (RtBzClean.stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END, ESTACK in *; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_sc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  (* ---- the run ---- *)
  apply (RtBzClean.bz_run_clean B TB W 0x43aa8 regs mem md
           (fun ms1 => SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
              (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
              (CM.scc_res (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
              (spZ regs - 2 * ESTACK) (clean (mrestrict (w_H W) mem)) ms1
            /\ YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem ms1)) _
           (romN_of_rt B W mem HROM) (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply RtBzAdaptP.evt_grows. apply RtBzPre.bz_canon. apply CW.tramp_strcasecmp.
    apply (CW.istrcasecmp_spec RIP.rip_proof (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
             (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9)
             (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14)
             (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
             (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
             (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
             (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr (clean (mrestrict (w_H W) mem)) x y
             (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) (spZ regs - 2 * ESTACK));
      [exact G10 | exact G11 | exact ST
       | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold ESTACK in *; lia
       | unfold BR.kHighShadowEnd; lia
       | change (bv_unsigned (reg_get regs 2)) with (spZ regs); lia
       | | | exact OK | lia | lia | | | | | exact M2S | exact IC | exact MI].
    + (* the first string with its NUL, on the cleaned store *)
      apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) x _ RE);
        [rewrite length_app; cbn [length]; unfold BM.UTOP; lia|].
      apply bz_bytes_of_abytes; [exact (proj1 SX) | lia | rewrite length_app; cbn [length]; lia].
    + apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) y _ RE);
        [rewrite length_app; cbn [length]; unfold BM.UTOP; lia|].
      apply bz_bytes_of_abytes; [exact (proj1 SY) | lia | rewrite length_app; cbn [length]; lia].
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs).
      destruct (sep_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length sx) + 1)
                  ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as [HL|HR];
        [left; unfold ESTACK in *; lia | right; lia].
    + change (bv_unsigned (reg_get regs 2)) with (spZ regs).
      destruct (sep_of_read (2 * ESTACK) W regs mem y (Z.of_nat (length sy) + 1)
                  ltac:(unfold ESTACK; lia) ltac:(lia) RDY) as [HL|HR];
        [left; unfold ESTACK in *; lia | right; lia].
    + apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) x
               (CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
      exact (chk_of_read (2 * ESTACK) W regs mem x (Z.of_nat (length sx) + 1)
               (CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
               (Z.of_nat (length sx)) RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)).
    + apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) y
               (CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
      exact (chk_of_read (2 * ESTACK) W regs mem y (Z.of_nat (length sy) + 1)
               (CM.scc_sz (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
               (Z.of_nat (length sy)) RDY AMY ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* ---- the post ---- *)
    intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM
                    & MI' & ST').
    destruct (RtBzPre.bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2256
                (spZ regs - 2 * ESTACK) MU ST') as (MO & MN);
      [unfold ESTACK; lia | unfold TFIB_IMG_END, ESTACK in *; lia |].
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 2256 ly S W regs mem md _ _ ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(keep_regs) MO MN GROW).
    intros regs' mem' HR _.
    assert (A10 : getr regs' 10%bv = Z_to_bv 64 (CM.scc_res (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
      by (rewrite (HR 10%bv); reflexivity).
    rewrite A10.
    split.
    + intros E. apply ANS.
      apply (f_equal (fun w : word => bv_unsigned w)) in E. unfold w64 in E.
      rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 64) with (2 ^ 64) in E.
      rewrite (Z.mod_small 0 (2 ^ 64) ltac:(lia)) in E.
      revert E. Z.div_mod_to_equations. lia.
    + intros E. apply ANS in E. rewrite E. reflexivity.
Qed.

End s.

(* ---- the closing: only the unit's B-symbols record left ---- *)
Section closed. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis HB : SegBSyms B.

Theorem seg_strcasecmp_closed : RtSeg.astrcasecmp_realizes tfibsegs B SegRtPC.PC_strcasecmp.
Proof. exact (seg_strcasecmp B (YG0q.AR_laws_ok tfibsegs B) HB). Qed.

End closed.

Print Assumptions seg_strcasecmp_closed.
