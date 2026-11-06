(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module names changed; 615 of its 727 lines of code are new or changed and 899 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/F35.v, with its module paths, module names and numbers changed; 139 of its 234 lines of code are new or changed and 632 lines of the source are left out. *)
(* lib/A/Prog/Seg/F19F_on.v -- route (C), a Theorem Labs lane (owner a Theorem Labs lane): the `_on` twins of Seg/F19F.v's (not in this delivery) two footprint
   runs (F19F.v (an earlier version, blob badcc8f71c7, not in this delivery) from a working branch 9e63d6e1607). This file edits no line of F19F.v (not in this delivery), whose later versions differ from the twin's base only in module qualification; this file adds
   lemmas only. Proves no function (kind: segment run). rule 24: no function proved.

     f19_evt_F_on    <- F19F.f19_evt_F    (F19F.v:72)
     f19_evt_ro_F_on <- F19F.f19_evt_ro_F (F19F.v:241)

   Each statement is the original's text with ONLY these edits:
   - PRE: `shadow_rw m` -> `shadow_rw_on (bcmp_wrap_shadow_R L (R + 6) 6) m` (A.ShadowRwOn.shadow_rw_on,
     A.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R).
   - POST (f19_evt_F_on only): `shadow_rw m'` -> `(forall P, shadow_rw_on P m -> shadow_rw_on P m')`.
     f19_evt_ro_F's post states no shadow fact, so f19_evt_ro_F_on's post is the original's, unchanged.

   R = bcmp_wrap_shadow_R L (R + 6) 6, i.e. fun a => sh_word_on L 6 a \/ sh_word_on (R + 6) 6 a (bcmp_wrap_c_on.v:20).
   Where it comes from: the run (0x82400 ld s4,200(s1); bnez a0; addi a1,s7,6; li a2,6; ld a0,64(s1);
   jal wrapper_bcmp) loads only the spills A+200 and A+64, no shadow byte. The original proofs use the shadow
   premise HSW once each:
   - f19_evt_F: `exact HSW` (F19F.v:161), the shadow premise of the wrapper call, at the call's registers
     a0 = [A+64] = Z_to_bv 64 L, a1 = s7 + 6 = Z_to_bv 64 (R + 6), a2 = Z_to_bv 64 6 (EL / ER6 / E6, F19F.v:137-139).
     Here that premise is bcmp_wrap_contract_F_on's (bcmp_wrap_c_on.v:73)
     `shadow_rw_on (bcmp_wrap_shadow_R L R N) m` at L := L, R := R + 6, N := 6. Its disjuncts:
       sh_word_on L 6        : the aligned shadow words of [L, L+6), the ASan range check of the first string
                               (bcmp_wrap_on.v:133, or_introl);
       sh_word_on (R + 6) 6  : the aligned shadow words of [R+6, R+12), the range check of the second string
                               (bcmp_wrap_on.v:136, or_intror).
     The contract is discharged by bcmp_wrap_on.bcmp_wrap_holds_F_on (bcmp_wrap_on.v:168) in place of
     bcmp_wrap_F.bcmp_wrap_holds_F; its post bcmp_wrap_post_on (bcmp_wrap_c_on.v:31) already carries the
     forall-P shadow conjunct, over the call's memory, which is m (the run before the call only loads).
   - f19_evt_ro_F: `F18.shadow_rw_rel m _ REL HSW` (F19F.v:298), the premise of f19_evt_F on normalize rsegs m.
     Here it is A.ShadowRwOnT.shadow_rw_on_rel (ShadowRwOnT.v:27) into f19_evt_F_on's premise, same R
     (normalizing changes no shadow byte).
   Template: the plain-form twins F19.f19_evt_on / f19_evt_ro_on (a Theorem Labs lane, Seg/F19.v (not in this delivery; from a working branch aef5855f4dd)),
   same R. The scripts are F19F's, with these three changes: the contract lemma, the transport, and f19_evt_F_on
   in place of f19_evt_F. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
(* DecodeC.decode_any / DecodeC.is_defined_illegal, named by MemNormF's decode case (already loaded: RiscvSemantics
   decodes with them). *)
From LinuxProcessSemantics.Riscv Require DecodeC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require memcmp_c bcmp_wrap_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require F18.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
(* Last: StepF's step (evtF goals) shadows Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* As in F19F.v, YK11 last among the term-level names (its seg_rom). *)
Import YK11.
(* The statement leaves: shadow_rw_on and bcmp_wrap_shadow_R / bcmp_wrap_contract_F_on, by their short names. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require A.ShadowRwOnT.
(* bcmp_wrap_on after Import YK11, Required (not imported), as F19F.v does with bcmp_wrap_F: its closure carries
   bcmp_wrap_F's. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require bcmp_wrap_on.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module BW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_c.
Module BWFO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.bcmp_wrap_on.
Module MC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.memcmp_c.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec.StrFun.
Module SRT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* ctrl's YK11 (the copy `Import YK11` above binds; the .glob of the first build records seg_rom there), by an
   alias, so ctrlgate's DUP check (lib/Reusable/YK11.v is also in the closure) sees one copy. *)
Module AK11 := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.

(* F19F.v's local names (local there, so restated here), so that the twins state F19F's constants. *)
Local Abbreviation BCMP_WRAP_K := BW.BCMP_WRAP_K.
Local Abbreviation BCMP := BW.BCMP.
Local Abbreviation REAL_BCMP := BW.REAL_BCMP.
Local Abbreviation REAL_MEMCMP := BW.REAL_MEMCMP.
Local Abbreviation GOT_CF := BW.GOT_CF.
Local Abbreviation CF := BW.CF.
Local Abbreviation MEMCMP := MC.MEMCMP.
Local Abbreviation memcmp_model := SF.memcmp_model.

(* ---- F19F.f19_evt_F over the wrapper's narrowed footprint contract: bcmp_wrap_on.bcmp_wrap_holds_F_on, applied
   below, at a0 = L, a1 = R + 6, a2 = 6. ---- *)
Lemma f19_evt_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s7v = Z_to_bv 64 R -> a0 = Z_to_bv 64 0 ->
    0 <= L < 2 ^ 64 -> 0 <= R -> R + 18 < 2 ^ 64 ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 (R + 18))) ->
    bytes_at rsegs m (A + 64) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m (R + 6) rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    mem_inv rsegs m -> addressable m L 6 -> addressable m (R + 6) 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 12) -> app_mem (R + 13) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 12 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R + 6) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L (R + 6) 6) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 200) 8 -> ExecF.rng RNG (A + 64) 8 ->
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    ExecF.rng RNG L 6 ->
    ExecF.rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 6 - 1) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    ExecF.rng RNG (R + 6) 6 ->
    ExecF.rng RNG (8 * (shadow_addr (R + 6) / 8))
      (8 * (shadow_addr (R + 6 + 6 - 1) / 8) + 8 - 8 * (shadow_addr (R + 6) / 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (R + 18)) s5 s6
                       (Z_to_bv 64 R) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82418) fc None m' (AK11.seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp)
         /\ asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m'))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82400) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs vcmp lo -> -> -> HLb HR0 HR18 H200 H64 HBL HLls HBR HLrs Hmm HMI HADL HADR
    HaL6 HaL7 HaR12 HaR13 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    G200 G64 Gby Gimg Gstk GL GsL GR GsR.
  assert (HL200 : ov_read_bytes rsegs m (wa (A + 200)) 8 = Some (le8 (Z_to_bv 64 (R + 18)))).
  { pose proof (bytes_at_ov_read rsegs m (A + 200) (le8 (Z_to_bv 64 (R + 18))) 0 8 H200
      ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  assert (HL64 : ov_read_bytes rsegs m (wa (A + 64)) 8 = Some (le8 (Z_to_bv 64 L))).
  { pose proof (bytes_at_ov_read rsegs m (A + 64) (le8 (Z_to_bv 64 L)) 0 8 H64 ltac:(rewrite length_le8; lia)) as HH.
    cbn [Z.of_nat] in HH. rewrite Z.add_0_r, skipn_O in HH.
    rewrite firstn_all2 in HH by (rewrite length_le8; lia). exact HH. }
  step.
  step.
  lazymatch goal with
  | |- ExecF.evtF _ _ _ (MS _ _ (if ?cnd then _ else _) _ _ _ _) =>
      let v := eval vm_compute in cnd in replace cnd with v by (vm_compute; reflexivity); cbv iota
  | _ => idtac
  end.
  step. step. step. step.
  pose proof BWFO.bcmp_wrap_holds_F_on as HB. unfold bcmp_wrap_contract_F_on, BW.BCMP_WRAP_K in HB. cbv zeta in HB.
  assert (EL : bv_unsigned (Z_to_bv 64 L) = L) by (apply unsigned_lit; lia).
  assert (ER6 : bv_unsigned (Z_to_bv 64 (R + 6)) = R + 6) by (apply unsigned_lit; lia).
  assert (E6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
  eapply ExecF.evtF_cut.
  { eapply HB with (ls := ls) (rs := rs) (v := vcmp) (lo := lo).
    all: rewrite ?EL, ?ER6, ?E6.
    - exact HBL.
    - exact HBR.
    - change (Z.to_nat 6) with 6%nat; exact Hmm.
    - exact HMI.
    - clear; lia.
    - exact HADL.
    - exact HADR.
    - right; exact HaL6.
    - right; replace (R + 6 + 6) with (R + 12) by lia; exact HaR12.
    - right; exact HaL7.
    - right; replace (R + 6 + 7) with (R + 13) by lia; exact HaR13.
    - exact HdjL.
    - replace (R + 6 + 6) with (R + 12) by lia; exact HdjR.
    - exact HST.
    - exact Hlo1.
    - exact Hlo2.
    - exact Hspa.
    - exact HAC.
    - exact HSW.
    - exact HRB.
    - exact HRM.
    - exact HGC.
    - exact HC254.
    - exact HC255.
    - exact Gby.
    - exact Gimg.
    - exact Gstk.
    - exact GL.
    - right; exact GsL.
    - exact GR.
    - right; exact GsR. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m'
              & E & MU & WM & MI' & ST' & AC' & SW' & HBpl & HBpr).
  subst ms'.
  replace (ret_pc (Z_to_bv 64 0x82418)) with (Z_to_bv 64 0x82418)
    by (symmetry; apply ret_pc_even; [clear; lia | reflexivity]).
  apply ExecF.evtF_done.
  exists (Z_to_bv 64 0x82418), a1'', a2'', a3'', a4'', a5'', a6'', a7'', t0'', t1'', t2'', t3'', t4'', t5'', t6'', m'.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split; [exact AC' | exact SW'].
Qed.

(* ---- F19F.f19_evt_ro_F over the narrowed premise: f19_evt_F_on's run on the normalized memory, moved onto m by
   evtF_normalize_ro; the premise crosses mem_rel by ShadowRwOnT.shadow_rw_on_rel (in place of F18.shadow_rw_rel);
   the post (no shadow fact) comes back across mem_rel / ro_same exactly as in F19F.f19_evt_ro_F. ---- *)
Lemma f19_evt_ro_F_on :
  forall (RNG : ExecF.footprint)
         (ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (Fr : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A L R : Z) (ls rs : list byte) (vcmp lo : Z),
    s1v = Z_to_bv 64 A -> s7v = Z_to_bv 64 R -> a0 = Z_to_bv 64 0 ->
    0 <= L < 2 ^ 64 -> 0 <= R -> R + 18 < 2 ^ 64 ->
    bytes_at rsegs m (A + 200) (le8 (Z_to_bv 64 (R + 18))) ->
    bytes_at rsegs m (A + 64) (le8 (Z_to_bv 64 L)) ->
    bytes_at rsegs m L ls -> (6 <= length ls)%nat ->
    bytes_at rsegs m (R + 6) rs -> (6 <= length rs)%nat ->
    memcmp_model ls rs 6 = Some vcmp ->
    ro_agree rsegs m -> addressable m L 6 -> addressable m (R + 6) 6 ->
    app_mem (L + 6) -> app_mem (L + 7) -> app_mem (R + 12) -> app_mem (R + 13) ->
    (L + 6 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= L) ->
    (R + 12 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= R + 6) ->
    stk rsegs m lo (bv_unsigned sp) -> lo + BCMP_WRAP_K <= bv_unsigned sp ->
    HIGHMEM_BEG <= lo -> bv_unsigned sp <= APPMEM_END ->
    asan_cells m -> shadow_rw_on (bcmp_wrap_shadow_R L (R + 6) 6) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    ExecF.rng RNG (A + 200) 8 -> ExecF.rng RNG (A + 64) 8 ->
    RngBytes.rng_bytes RNG ->
    ExecF.rng RNG 0x10000 0x5ee000 ->
    ExecF.rng RNG (bv_unsigned sp - BCMP_WRAP_K) BCMP_WRAP_K ->
    ExecF.rng RNG L 6 ->
    ExecF.rng RNG (8 * (shadow_addr L / 8)) (8 * (shadow_addr (L + 6 - 1) / 8) + 8 - 8 * (shadow_addr L / 8)) ->
    ExecF.rng RNG (R + 6) 6 ->
    ExecF.rng RNG (8 * (shadow_addr (R + 6) / 8))
      (8 * (shadow_addr (R + 6 + 6 - 1) / 8) + 8 - 8 * (shadow_addr (R + 6) / 8)) ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (ra' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 (Z_to_bv 64 A)
                       (Z_to_bv 64 vcmp) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (R + 18)) s5 s6
                       (Z_to_bv 64 R) s8 s9 s10 s11 t3' t4' t5' t6')
                  Fr (Z_to_bv 64 0x82418) fc None m' (AK11.seg_rom rsegs)
         /\ munch [(bv_unsigned sp - BCMP_WRAP_K, bv_unsigned sp)] m m'
         /\ wmono rsegs m m' /\ ro_agree rsegs m' /\ ro_same rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6)
          Fr (Z_to_bv 64 0x82400) fc None m (AK11.seg_rom rsegs)).
Proof.
  intros RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc m A L R ls rs vcmp lo E1 E7 E0 HLb HR0 HR18 H200 H64 HBL HLls HBR HLrs Hmm HRO HADL HADR
    HaL6 HaL7 HaR12 HaR13 HdjL HdjR HST Hlo1 Hlo2 Hspa HAC HSW HRB HRM HGC HC254 HC255
    G200 G64 Gby Gimg Gstk GL GsL GR GsR.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  (* F18.stk_rel_hi / stk_rel_hi_back take the image top AC.GT, as in F19F.f19_evt_ro_F. *)
  assert (Hlo0 : AC.GT <= lo) by (unfold AC.GT, HIGHMEM_BEG in *; lia).
  assert (Hsp64 : bv_unsigned sp <= 2 ^ 64) by (unfold APPMEM_END in Hspa; lia).
  pose proof (f19_evt_F_on RNG ra0 sp gp tp t0 t1 t2 s0 s1v a0 a1 a2 a3 a4 a5 a6 a7
    s2 s3 s4 s5 s6 s7v s8 s9 s10 s11 t3 t4 t5 t6
    Fr fc (normalize rsegs m) A L R ls rs vcmp lo E1 E7 E0 HLb HR0 HR18
    (F18.ba_rel1 m _ _ _ REL H200) (F18.ba_rel1 m _ _ _ REL H64) (F18.ba_rel1 m _ _ _ REL HBL) HLls
    (F18.ba_rel1 m _ _ _ REL HBR) HLrs Hmm (mem_inv_normalize rsegs m)
    (F18.addressable_rel m _ _ _ REL HADL) (F18.addressable_rel m _ _ _ REL HADR)
    HaL6 HaL7 HaR12 HaR13 HdjL HdjR (F18.stk_rel_hi m _ lo _ REL Hlo0 Hsp64 HST) Hlo1 Hlo2 Hspa
    (F18.asan_cells_rel m _ REL HAC) (SRT.shadow_rw_on_rel _ m _ REL HSW)
    (F18.ba_rel1 m _ _ _ REL HRB) (F18.ba_rel1 m _ _ _ REL HRM) (F18.ba_rel1 m _ _ _ REL HGC)
    (F18.ba_rel1 m _ _ _ REL HC254) (F18.ba_rel1 m _ _ _ REL HC255)
    G200 G64 Gby Gimg Gstk GL GsL GR GsR) as HC.
  pose proof (evtF_normalize_ro RNG _ _ _ _ _ _ m (AK11.seg_rom rsegs) HRO HC) as HN.
  eapply ExecF.evtF_mono; [exact HN|].
  intros ms (s0' & (ra' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t0' & t1' & t2' & t3' & t4' & t5' & t6' & m0'
              & E & MU & WM & MI' & ST' & AC' & SW') & Hrel & Hros).
  subst s0'.
  destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
  destruct Hrel as (HR & HF & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
    in HR, HF, Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
  subst regsX frX pcX svcX rvX fcX romX.
  exists ra', a1', a2', a3', a4', a5', a6', a7', t0', t1', t2', t3', t4', t5', t6', memX.
  split; [reflexivity|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) memX m0' REL Hmr Hros MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) memX m0' REL Hmr Hros WM)|].
  split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
  split; [exact Hros|].
  exact (F18.stk_rel_hi_back memX m0' lo _ Hmr Hlo0 Hsp64 ST').
Qed.

Print Assumptions f19_evt_F_on.
Print Assumptions f19_evt_ro_F_on.
