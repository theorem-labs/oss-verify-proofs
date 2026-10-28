(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface D_auxv I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA Pj_cpsA El_defsA El_lf1A El_lf2A El_lf2bA El_phasesA El_frontA El_costA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section LibIfaceE.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.

Definition fuzz_one_cpsE : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x6a7e68 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) ->
  LIB m -> io_ssp m -> libc_nl m -> el_xdataA m -> el_auxvA (bv_unsigned sp) m -> rt_sp0 RT Σ <= bv_unsigned sp + FUZZ_SP0GAP ->
  ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ -> frm0 fc ->
  cps asegs (fun c => ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_fuzz m)) c /\ frm0 (ms_fcsr (cfg_ms c)))
    (fun c => (exists (Σ' : rts RT),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) EL_LIB_FP m m' /\ LIB m') c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = [] /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ') /\ frm0 (ms_fcsr (cfg_ms c))).
End LibIfaceE.

Section Top.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.

Variable W : Z -> rts RT -> mem -> Prop.
Hypothesis WEXIT : forall c Σ m, W c Σ m -> rt_frames RT Σ = [] -> ART RT Σ m /\ rt_credit RT Σ = c.

Hypothesis VEC : forall PMc, el_vec_cps RT PMc.
Hypothesis PARSE : forall PMc, el_parse_cps RT PMc.
Hypothesis DISP : forall PMc, el_disp_cps RT PMc W (fun c => cutX (rt_sigW RT (W c)) PMc (W c)).
Hypothesis TAILP : forall PMc, el_tailP_cps RT PMc.
Hypothesis TAIL2 : forall PMc, el_tail2_cps RT PMc.
Hypothesis TAILPW : forall c PMc, el_tailP_cps (rt_sigW RT (W c)) PMc.
Hypothesis TAIL2W : forall c PMc, el_tail2_cps (rt_sigW RT (W c)) PMc.

Hypothesis ARMS : forall PMc a, el_liveA a = true -> arm_cpsA RT PMc W a.

Local Ltac ul := unfold FUZZ_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem fuzz_one_elA : fuzz_one_cpsE RT el_libA.
Proof using AF RC W WEXIT VEC PARSE DISP TAILP TAIL2 TAILPW TAIL2W ARMS.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS NL0 XD0 AUX0 SPB0 ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  match goal with |- cps asegs _ ?K0 => set (K := K0) end.

  assert (KFIN : forall (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' lo usp -> frm0 fc' ->
        el_libA m' -> rt_pres_fp (rt_live RT Σ) [] usp EL_LIB_FP m m' ->
        rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - FUZZ_COST <= rt_credit RT Σ' ->
        aevt RT PMc Σ' K (MS (mkR ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TPV_A) t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F' (ret_pc ra) fc' None m' (seg_rom asegs))).
  { intros Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'.
      split; [rewrite ESP, ETP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| exact LIB'].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (cps_of_aevt RT PMc).

  eapply (el_front RT AF RC PMc FDO MST Σ K); try eassumption.
  intros X EU EL LK. assert (LOWX : rt_sp0 RT Σ - STACK_WIN <= lf_lo X) by (rewrite EL; exact LOW).

  apply (VEC PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOWX D0 BSL INLV LVPOS LVB CR0).

  assert (KX : cutX RT PMc (ART RT) Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_credit RT Σ - FUZZ_COST) K).
  { apply (TAILP PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ K FDO MST LK LOWX LVPOS).
    apply (TAIL2 PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ K FDO MST LK LOWX LVPOS).
    intros Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP' CR'.
    rewrite EU, EL in *. exact (KFIN Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP' CR'). }

  apply (PARSE PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOWX D0 BSL INLV LVPOS LVB CR0).
  -
    apply (DISP PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K FDO MST LK LOWX D0 BSL INLV LVPOS LVB CR0 NL0 IOS XD0
             ltac:(rewrite EU; exact AUX0) ltac:(rewrite EU; split; [exact SPLE| exact SPB0]) (ARMS PMc)).
    +   exact KX.
    +
      intros c crd HC.
      apply (TAILPW c PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K FDO MST LK LOWX LVPOS).
      apply (TAIL2W c PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K FDO MST LK LOWX LVPOS).
      intros Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP' CR'.
      cbn [rt_sigW ART rt_live rt_frames rt_sp0 rt_credit rts] in ART', LV', FRS', SP', CR', PR'.
      destruct (WEXIT c Σ' m' ART' FRS') as [ARTx CRx].
      rewrite EU, EL in *. apply (KFIN Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ARTx MI' ST' FRM' LIB' PR' LV' FRS' SP'). lia.
  -   exact KX.
  -
    apply (TAIL2 PMc Σ m X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ K FDO MST LK LOWX LVPOS).
    intros Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP' CR'.
    rewrite EU, EL in *. apply (KFIN Σ' m' fc' F' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ART' MI' ST' FRM' LIB' PR' LV' FRS' SP').
    pose proof (el_vcost_bound bs BSL). unfold FUZZ_COST. lia.
Qed.
End Top.
