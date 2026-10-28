(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_ContStmt LbB_ContV4 LbB_ContVot.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablOS LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT5 LbB_TablPT6.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT14 LbB_TablPT15.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section PT16.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.

  Definition pt_epost (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (pspan p v b cap : Z) (l xs : list Z) (pid : bptr)
      (lo B shi : Z) : machine_state -> Prop :=
    fun ms => exists ff fp R M k errv',
      let e := PTEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp in
      ms = MS R F (Z_to_bv 64 (if Zlen l =? 0 then PT_EXIT else PT_H2)) fc None M (seg_rom asegs) /\ rfull R
      /\ getr R 3 = gp /\ getr R 4 = tp
      /\ (Zlen l <> 0 -> PTH R (pSP e) (pS1 e) ff pspan v (Zlen l) 0 /\ k = 4)
      /\ (Zlen l = 0 -> getr R 8 = Z_to_bv 64 (pSP e) /\ getr R 9 = Z_to_bv 64 (pS1 e) /\ getr R 26 = Z_to_bv 64 (sh ff))
      /\ fresh_frame H LF 0 ff fp
      /\ pmem H e xs k M s LB b cap pid errv'.

  Lemma pt_ppre_of : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (pspan p v b cap : Z) (l xs : list Z)
      (pid : bptr) (lo B shi ff fp : Z),
    let SP := bv_unsigned sp in
    fresh_frame H LF 0 ff fp ->
    (length LF < AFS_MAXLIVE_BP)%nat -> as_RFS H LF m ->
    SP mod 16 = 0 -> SP <= 2 ^ 47 -> SP <= B -> SP <= shi -> aceil <= lo -> lo <= SP - PT_STACK ->
    tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    span_keep H LB LF SP ((v, v + 24) :: v4_oldx b (4 * cap)) m pspan p (Zlen l) -> pspan mod 8 = 0 ->
    (pspan + 16 <= v \/ v + 24 <= pspan) -> spanA p l -> Zlen l <= 48 -> Forall (fun t => 0 <= t < 2 ^ 31) l ->
    v mod 8 = 0 -> ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    obj_win H LB LF SP lo v 24 -> v4_oldblk LB b cap pid -> vec32A LB m v b xs cap -> as_RHEAP H s LB m ->
    (4 * capmax (Zlen xs) cap (Zlen l) <= 2 ^ 26 /\ closs cap (capmax (Zlen xs) cap (Zlen l)) <= as_AL H s) ->
    lb_small LB + 3 * 64512 <= RT_SMALL_MAX ->
    Z.of_nat (length LB) + 2 <= RT_CNT_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> 0 <= as_AL H s ->
    ppre H (PTEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp).
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp SP
      FF LFL RF SP16 SPH SPB SPS CE LO TP RA SK PS8 PSD SPN N48 LR V8 VB OBJ OLD VEC RH BU1 BU2 BU3 BU4 TRO AL0.
    pose proof (rt_bp_base H HH) as HB.
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    unfold ppre. cbn [p_LF p_LB p_v p_b p_cap p_pid p_ps p_p p_l p_xs p_m p_s p_lo p_B p_shi p_tp p_ra p_sp p_ff p_fp].
    split; [exact FF|]. split; [exact LFL|].
    split; [intros f Hf; exact (proj2 (ah_RFS_range H HB _ _ RF) f Hf)|].
    split; [exact SP16|]. split; [exact SPH|]. split; [exact SPB|]. split; [exact SPS|]. split; [exact CE|]. split; [exact LO|].
    split; [exact TP|]. split; [exact RA|]. split; [exact SK|]. split; [exact PS8|]. split; [exact PSD|]. split; [exact SPN|].
    split; [exact N48|]. split; [exact LR|]. split; [exact V8|]. split; [exact VB|]. split; [exact OBJ|]. split; [exact OLD|].
    split; [exact (ah_nodup H HB _ _ _ RH)|]. split; [exact RH|].
    split; [exact BU1|]. split; [exact BU2|]. split; [exact BU3|]. split; [exact BU4|]. split; [exact TRO|]. split; [exact AL0|].
    split; [exact LEN|].
    destruct BK as [(B0 & C0)|(B0 & B16 & C0 & BC & HIn & DJ)].
    - split; [intros _; exact C0|]. split; [left; lia|]. intros X; contradiction.
    - split; [intros X; lia|].
      destruct OLD as [(X & _)|(_ & HIn')]; [lia|].
      pose proof (ah_blocks H HB _ _ _ _ RH HIn') as (_ & _ & _ & AI & ACe & _ & AP). cbn [blk_addr blk_size fst snd] in AI, ACe, AP.
      pose proof aceil_facts as ((ACF1 & ACF2) & _).
      split; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in AP; destruct AP; [left | right]; lia|].
      intros _; exact DJ.
  Qed.

  Lemma pt_after_entry : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe) (pspan p v b cap : Z) (l xs : list Z)
      (pid : bptr) (lo B shi : Z) (msF' : machine_state) (mo' : Model),
    let SP := bv_unsigned sp in
    (length LF < AFS_MAXLIVE_BP)%nat -> as_RFS H LF m ->
    SP mod 16 = 0 -> SP <= 2 ^ 47 -> SP <= B -> SP <= shi -> aceil <= lo -> lo <= SP - PT_STACK ->
    tp = Z_to_bv 64 ATP -> bv_unsigned ra mod 2 = 0 ->
    span_keep H LB LF SP ((v, v + 24) :: v4_oldx b (4 * cap)) m pspan p (Zlen l) -> pspan mod 8 = 0 ->
    (pspan + 16 <= v \/ v + 24 <= pspan) -> spanA p l -> Zlen l <= 48 -> Forall (fun t => 0 <= t < 2 ^ 31) l ->
    v mod 8 = 0 -> ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47)) ->
    obj_win H LB LF SP lo v 24 -> v4_oldblk LB b cap pid -> vec32A LB m v b xs cap -> as_RHEAP H s LB m ->
    (4 * capmax (Zlen xs) cap (Zlen l) <= 2 ^ 26 /\ closs cap (capmax (Zlen xs) cap (Zlen l)) <= as_AL H s) ->
    lb_small LB + 3 * 64512 <= RT_SMALL_MAX ->
    Z.of_nat (length LB) + 2 <= RT_CNT_MAX -> nlarge LB + 2 <= RT_LARGE_MAX ->
    trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] -> 0 <= as_AL H s ->
    as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
    pt_epost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi (as_VIS H s msF') ->
    as_SR H (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap (capmax (Zlen xs) cap (Zlen l))
                       (PrsGrammar.push_types l xs) pid lo B shi m mo (fun _ => True)) (mkCfg msF' mo').
  Proof.
    intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi msF' mo' SP
      LFL RF SP16 SPH SPB SPS CE LO TP RA SK PS8 PSD SPN N48 LR V8 VB OBJ OLD VEC RH BU1 BU2 BU3 BU4 TRO AL0 KR MP POST.
    pose proof (rt_bp_base H HH) as HB.
    destruct POST as (ff & fp & R & M & k & errv' & POST).
    set (e := PTEnt H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp) in POST.
    cbv zeta in POST.
    destruct POST as (VIS & HF & G3 & G4 & HN & HZ & FF & PM).
    pose proof VEC as (_ & _ & _ & LEN & BK & _).
    assert (P : ppre H e)
      by exact (pt_ppre_of ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m mo s LB LF pspan p v b cap l xs pid lo B shi ff fp
                  FF LFL RF SP16 SPH SPB SPS CE LO TP RA SK PS8 PSD SPN N48 LR V8 VB OBJ OLD VEC RH BU1 BU2 BU3 BU4 TRO AL0).
    change (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap (capmax (Zlen xs) cap (Zlen l))
                     (PrsGrammar.push_types l xs) pid lo B shi m mo (fun _ => True)) with (pQ H e).
    destruct (Z.eqb_spec (Zlen l) 0) as [N0|N0].
    - apply (pt_exit_step H HB e msF' mo' P). exists k.
      exists R, M, s, LB, b, cap, pid, errv'.
      split; [exact VIS|]. split; [exact HF|]. split; [exact G3|]. split; [exact G4|].
      split; [exact (HZ N0)|]. split; [exact KR|]. split; [exact MP|].
      replace (pys e (pn e)) with xs; [exact PM|]. unfold pys, pn. cbn [p_l p_xs e]. rewrite N0. cbn. rewrite app_nil_r. reflexivity.
    - destruct (HN N0) as [PH0 K4]. subst k.
      eapply (pt_loop H HH e (pQ H e) P (fun cf EX => match cf with mkCfg a b => fun EX' => pt_exit_step H HB e a b P EX' end EX)
                (Z.to_nat (pn e - 0)) 0 msF' mo' eq_refl).
      + unfold pn. cbn [p_l e]. pose proof (Zlen_nonneg l) as ZN. lia.
      + exists R, M, s, LB, b, cap, pid, errv'.
        split; [exact VIS|]. split; [exact HF|]. split; [exact G3|]. split; [exact G4|].
        split; [exact PH0|]. split; [exact KR|]. split; [exact MP|].
        rewrite pys_0. exact PM.
  Qed.
End PT16.
