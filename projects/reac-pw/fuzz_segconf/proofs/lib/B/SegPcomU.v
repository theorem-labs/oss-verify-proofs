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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgWrapNcmpH.v, with its module paths and module names changed; 180 of its 234 lines of code are new or changed and 332 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/FMrt_lift.v at origin/ossv/recipes f26f9fbd8777; module paths changed (boxreg's lib.Lib modules as pin's lib.Lib modules); moved from lib/A/FMrt_lift.v to lib/A/Rt/FMrt_lift.v, and the Requires of the moved files follow; the comments are boxreg's, verbatim, and name fuzz_boxreg.asan's addresses. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_pin/lib/AU/Rt/FMrt_lift.v, with its module paths changed; 344 of its 393 lines of code are new or changed and 185 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/RT_pf_shU.v, with its module paths and module names changed; 67 of its 219 lines of code are new or changed and 241 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/SegPcomU.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* ASan's printf_common (RT_pf_Tbl.v PF_PRINTF_COMMON) in the shared contracts' form sh_apcommon_realizesUz (RtPFSx.v)
   for segconf's format family: RT_pf_shU.v pcom_shzK over seg_piece.
   - every seg_piece has its pcx arm (seg_pcx_arms): the released pieces by the released arms (RT_pf_sh.v lit / ps / pps,
     RT_pf_d.v, RT_pf_c.v, RT_pf_x04.v, RT_pf_02x.v, RT_pf_llu.v) carried to PRel p, the three new pieces by
     SegPcxGram.v;
   - FF_pcomS is RT_pf_sh.v FF_pcomK over seg_parse / seg_text (no piece predicate: every piece has its arm);
   - pcom_shzS is pcom_shzK's proof, the relocated Bz walk (RT_pf_bz.v pcom_call) at the same cleaned store, with the
     grammar facts taken from SegPcxGram.seg_pcomx_K and SegPfStep.seg_parse_bytes. The helper lemmas are
     RT_pf_shU.v's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFupoison RtPFH RtBzLift.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YE2y YFl3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtBzStr RtBzBridge RtBzClean RtBzPre.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require RT_pf_Tbl RT_pf_bz RT_pf_sh RT_pf_shU.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require RT_pf_d RT_pf_c RT_pf_x04 RT_pf_02x RT_pf_llu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require FMpfStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import SegPfStep SegPcxGram.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.D_kit.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.F_achk.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pck.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcbits.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcrr.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pchead.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxgram.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxlist.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.K.I_vprintfw.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib.Regs6ss.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BzI := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.ImageA.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Frame.
Module BzC := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Cells.
Module BzS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Step.
Module BzSh := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.Shadow.
Module BzR := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_m2s.
Module BzK := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_consts.
Module BzQ := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_qck.
Module BzB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcbits.
Module BzG := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxgram.
Module BzX := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_pcxlist.
Module BzV := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.K.I_vprintfw.
Module CL := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzClean.
Module BZS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzStr.
Module PRE := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt.RtBzPre.
Module RTB := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_bz.
Module RTT := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_Tbl.
Module RTS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_sh.
Module RTU := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.RT_pf_shU.
Module PFS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.FMpfStep.

(* ---- every seg_piece has its pcx arm ---- *)
Lemma seg_pa_of_eq : forall a, seg_pa_of a = RTS.pa_of a.
Proof. intros [v|u|s]; reflexivity. Qed.
Lemma seg_map_pa_of : forall args, map seg_pa_of args = map RTS.pa_of args.
Proof. intros args. apply map_ext. exact seg_pa_of_eq. Qed.

Lemma seg_pcx_arm_PRel : forall p, RTS.pcom_pcx_arm p -> seg_pcx_arm (PRel p).
Proof.
intros p A fuel rest args c a' C Hok H.
rewrite seg_step_PRel in H. rewrite !seg_map_pa_of.
assert (E1 : seg_cin1 (PRel p) = RTS.pc_cin1 p) by (destruct p; reflexivity).
change (seg_code (PRel p)) with (PFS.pf_code p). rewrite E1.
exact (A fuel rest args c a' C Hok H).
Qed.

Lemma seg_pcx_arms : forall q, seg_pcx_arm q.
Proof.
intros [[b| | | | | | |]| | |].
- apply seg_pcx_arm_PRel. apply RTS.pcom_pcx_arm_lit.
- apply seg_pcx_arm_PRel. exact RT_pf_d.pcom_pcx_arm_Pd.
- apply seg_pcx_arm_PRel. exact RT_pf_c.pcom_pcx_arm_Pc.
- apply seg_pcx_arm_PRel. exact RT_pf_x04.pcom_pcx_arm_Px04.
- apply seg_pcx_arm_PRel. exact RT_pf_02x.pcom_pcx_arm_px02.
- apply seg_pcx_arm_PRel. exact RT_pf_llu.pcom_pcx_arm_llu.
- apply seg_pcx_arm_PRel. exact RTS.pcom_pcx_arm_ps.
- apply seg_pcx_arm_PRel. exact RTS.pcom_pcx_arm_pps.
- exact seg_pcx_arm_u.
- exact seg_pcx_arm_zu.
- exact seg_pcx_arm_24s.
Qed.

Lemma seg_all_true : forall qs : list seg_piece, Forall (fun _ => True) qs.
Proof. induction qs as [|q qs IH]; constructor; [exact I | exact IH]. Qed.

(* the scan accepts every segconf format, at the released argument map *)
Lemma seg_pcomx : forall fmt qs args T,
  seg_parse fmt = Some qs -> seg_text qs args = Some T ->
  BzG.pcomx_ok (fmt ++ [0]) (map RTS.pa_of args) = true /\
  BzG.pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map RTS.pa_of args) (seg_cinK qs) = seg_cinK qs.
Proof.
intros fmt qs args T Hp Ht.
destruct (seg_pcomx_K (fun _ => True) (fun q _ => seg_pcx_arms q) fmt qs args T Hp (seg_all_true qs) Ht) as (OK & COV).
rewrite seg_map_pa_of in OK, COV. split; [exact OK | exact COV].
Qed.

(* ---- printf_common's family over segconf's grammar (RT_pf_sh.v FF_pcomK) ---- *)
Definition FF_pcomS : fmt_fam := fun rd rs f ws T =>
  exists (fmt : list Z) (qs : list seg_piece) (args : list pf_arg),
  fmt_at rd rs f fmt /\ fmt <> [] /\ f + Z.of_nat (length fmt) + 1 <= TFIB_IMG_END /\
  seg_parse fmt = Some qs /\ pf_args_asan rd rs ws args /\ RTS.pf_args_amem ws args /\
  seg_text qs args = Some T /\ seg_prec_pos qs args.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

(* ---- the contract (RT_pf_shU.v pcom_shzK, over seg_piece) ---- *)
Theorem pcom_shzS : forall K, 2320 <= K ->
  sh_apcommon_realizesUz tfibsegs B FF_pcomS K RTU.PCM_CR RTT.PF_PRINTF_COMMON.
Proof.
  intros K HK ly S U W regs mem md f ap ws T HPRE Hlo HWIN R11 R12 HCV _ _ HWS HZD HAP0 HAP47 HFF.
  destruct HFF as (fmt & qs & args & HFA & HNE & HIMG & HP & HAA & HAM & HT & _).
  pose proof HPRE as ((HAR & Hra & H16 & _ & HSH & _ & _ & _) & HOK & HPO).
  assert (HARU : ARU tfibsegs B ly S U W mem md) by (split; [exact HAR | split; assumption]).
  pose proof (stk_kHighMemBeg B ly S _ (proj1 HAR)) as (LB & LH).
  pose proof (lo_stk_ceil ly (am_layout B ly S _ (proj1 HAR))) as LC.
  pose proof ASAN_CEIL_range as ((LC1 & _) & _). unfold ASAN_CEIL in LC, LC1.
  lazymatch type of LB with ?k <= _ => let v := eval vm_compute in k in change k with v in LB end.
  lazymatch type of LH with _ <= ?k => let v := eval vm_compute in k in change k with v in LH end.
  set (sp := spZ regs) in *. set (H := w_H W) in *.
  set (m0 := mrestrict H mem). set (m := CL.clean m0).
  pose proof (RTU.pcm_rom_eq B TB W mem HCV) as RE. fold H m0 in RE.
  destruct HFA as (Hf0 & HFB & HFD & HFAM & HFRA & HFHV).
  destruct (seg_pcomx fmt qs args T HP HT) as (OK & COV).
  pose proof (seg_parse_bytes fmt qs HP) as FB.
  assert (L1 : (1 <= length fmt)%nat) by (destruct fmt; [exfalso; exact (HNE eq_refl) | cbn; lia]).
  set (n := Z.of_nat (length fmt) + 1).
  assert (Hn : Z.of_nat (length (fmt ++ [0])) = n) by (unfold n; rewrite length_app; cbn [length]; lia).
  unfold TFIB_IMG_END in HIMG.
  (* the format *)
  assert (BYf : BzM.bytes_at BzI.asegs m f (BzB.zb8 (fmt ++ [0]))).
  { apply (CL.bytes_at_clean m0 f _ RE); [unfold BzB.zb8; rewrite length_map, Hn; unfold BzM.UTOP; lia|].
    apply (RTU.bytes_of_view H mem f (fmt ++ [0])); [lia | rewrite Hn; lia|].
    intros i Hi. rewrite Hn in Hi. apply HFB. unfold n in Hi. lia. }
  assert (CHK : BzQ.chk_ok m f n).
  { apply (CL.chk_ok_clean m0 f n RE); [lia | unfold n; lia|].
    apply BZS.chk_ok_of_view; [lia | unfold n; lia | unfold n; lia | unfold n; lia | | exact HFRA |].
    - unfold BzK.region_in_mem, BzR.kLowMemEnd. left. unfold n. lia.
    - apply BZS.hull_of_shadow_hull_vis. exact HFHV. }
  (* the stack *)
  assert (ST : BzF.stk BzI.asegs m (sp - K) sp).
  { apply (CL.stk_clean m0 (sp - K) sp); [unfold YF0x.TFIB_IMG_END; lia | unfold BzM.UTOP; lia|].
    apply RtBzBridge.stk_of_apresent; [lia | lia | exact HWIN]. }
  (* the slots *)
  assert (VS : forall i w a, nth_error (map (Z_to_bv 64) ws) i = Some w -> nth_error (map RTS.pa_of args) i = Some a ->
               BzX.sarg a ->
               BzS.ro_cells BzI.asegs m (ap + 8 * Z.of_nat i) [BzC.C8 w]
               /\ (ap + 8 * Z.of_nat i + 8 <= sp - 2320 \/ sp <= ap + 8 * Z.of_nat i)).
  { intros i w a Ew _ _. rewrite nth_error_map in Ew.
    destruct (nth_error ws i) as [wz|] eqn:Ez; [|discriminate Ew]. cbn in Ew. injection Ew as <-.
    assert (Hi : (i < length ws)%nat) by (apply nth_error_Some; rewrite Ez; discriminate).
    pose proof (HWS i Hi) as Hrw. rewrite (nth_error_nth ws i 0 Ez) in Hrw.
    pose proof (YFl3.rdword_range H mem _ _ Hrw) as Hwr.
    pose proof (YE2y.val_mem_of_rdword H mem _ _ Hrw) as VM.
    unfold zdisjoint in HZD. cbn [fst snd] in HZD.
    split.
    - apply (CL.ro_cells_clean m0 _ _ RE); [change (BzC.cells_size [BzC.C8 (Z_to_bv 64 wz)]) with 8%nat; unfold BzM.UTOP; lia|].
      apply (PRE.c8_of_val_mem m0 _ wz); [lia | lia | exact Hwr | exact VM].
    - lia. }
  (* the strings *)
  assert (STR : forall i w s, nth_error ws i = Some w -> nth_error args i = Some (APtr s) ->
                BzX.ck_arg m (sp - 2320) sp (Z_to_bv 64 w) (BzG.PA_s s) None).
  { intros i w s Ew Ea.
    pose proof (RTU.args_asan_nth _ _ ws args i w (APtr s) HAA Ew Ea) as (FS & Hw0 & Hlen & HB & _ & HD & _ & HRA & HHV).
    pose proof (RTU.args_amem_nth ws args i w s HAM Ew Ea) as HAMs.
    unfold amem_range, YG0f.kLowMemEnd, YG0f.kHighMemBeg, YG0f.kHighMemEnd in HAMs.
    set (l := Z.of_nat (length s)) in *.
    assert (Ew64 : bv_unsigned (Z_to_bv 64 w) = w) by (apply wz; lia).
    unfold BzX.ck_arg. rewrite Ew64. exists (map (Z_to_bv 8) s).
    rewrite length_map. fold l.
    split; [|split; [exact Hw0|split; [|split]]].
    - split.
      + replace (map (Z_to_bv 8) s ++ [BzSh.z8]) with (map (Z_to_bv 8) (s ++ [0])) by (rewrite map_app; reflexivity).
        apply (CL.bytes_at_clean m0 w _ RE); [rewrite length_map, length_app; cbn [length]; unfold BzM.UTOP; fold l; lia|].
        apply (RTU.bytes_of_view H mem w (s ++ [0])); [lia | rewrite length_app; cbn [length]; fold l; lia|].
        intros i0 Hi0. rewrite length_app in Hi0. cbn [length] in Hi0. apply HB. fold l in Hi0. lia.
      + intros Hin. apply in_map_iff in Hin as (c & Ec & Hc).
        pose proof (proj1 (Forall_forall _ _) FS c Hc) as Rc. cbv beta in Rc.
        apply (f_equal (@bv_unsigned 8)) in Ec. unfold BzSh.z8 in Ec.
        rewrite (PRE.u8z c) in Ec by lia. rewrite (PRE.u8z 0) in Ec by lia. lia.
    - rewrite Forall_forall in HD. specialize (HD _ (or_introl eq_refl)). unfold zdisjoint, str_end in HD. cbn [fst snd] in HD.
      fold l in HD. pose proof (Z.mod_pos_bound (w + l) 8 ltac:(lia)). lia.
    - lia.
    - apply (RTU.chkr_clean m0 w (l + 1) RE); [lia | lia|].
      apply RTU.chkr_of_view; [lia | lia | lia | lia | | exact HRA | apply BZS.hull_of_shadow_hull_vis; exact HHV].
      unfold BzK.region_in_mem, BzR.kLowMemEnd, BzR.kHighShadowEnd, BzR.kHighMemEnd. lia. }
  assert (CKA : BzX.ck_args m (sp - 2320) sp (map (Z_to_bv 64) ws) (map RTS.pa_of args)
                  (BzG.pcx_covs (length (fmt ++ [0])) (fmt ++ [0]) (map RTS.pa_of args) (seg_cinK qs))).
  { rewrite COV. apply (RTU.ck_args_any m _ _ args ws _ (RTU.args_asan_len _ _ ws args HAA) STR). }
  (* the run *)
  eapply (CL.srr_of_clean_bz_eq W RTT.PF_PRINTF_COMMON regs mem md _ _ RE).
  - apply PRE.bz_canon.
    apply (RTB.pcom_call f ap (sp - K)).
    + exact R11.
    + exact R12.
    + exact ST.
    + change (bv_unsigned (reg_get regs 2)) with sp. lia.
    + lazymatch goal with |- ?k + 8 <= _ => let v := eval vm_compute in k in change k with v end. lia.
    + change (bv_unsigned (reg_get regs 2)) with sp. lia.
    + exact H16.
    + change (bv_unsigned (reg_get regs 2)) with sp.
      exists fmt, (map RTS.pa_of args), (seg_cinK qs), (map (Z_to_bv 64) ws).
      split; [exact OK|]. split; [exact FB|]. split; [exact L1|]. split; [exact BYf|].
      split; [lia|]. split; [lia|]. split; [exact VS|]. split; [exact HAP0|].
      split; [rewrite length_map; lia|]. split; [exact CKA|]. split; [exact CHK|].
      exact (RTU.pctx_of_ARU B TB ly S U W mem md HARU RE).
    + exact (CL.mem_inv_clean m0).
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    unfold BzV.pcom_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & _ & _ & ST').
    change (bv_unsigned (reg_get regs 2)) with sp in MU, ST'.
    destruct (PRE.bz_window m m' sp 2320 (sp - K) MU ST' ltac:(lia) ltac:(unfold YF0x.TFIB_IMG_END; lia)) as (MO & MN).
    apply (RTU.pcm_post B LAWS K ly S U W regs mem md _ ms' model' HPRE HK Hlo HWIN Hcl Heqv Hsbm);
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | keep_regs | exact MO | exact MN].
Qed.
End s.
