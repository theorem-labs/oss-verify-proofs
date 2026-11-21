(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateState.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateFast.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateArms.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Inflate.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarbBase.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateGarb.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvLoop.
From Stdlib Require Import NArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Import RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.Riscv Require Import Instr.
From LinuxProcessSemantics.Riscv Require Import Decode.
From LinuxProcessSemantics.Riscv Require Import DecodeC.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import CatSim.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import SeqExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StoreOk.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import Hoare.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Tac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymAux.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvApi.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateInvCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import HarnessKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflRod6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflCtx6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6b.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflNeed6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6c.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflArmLib6d.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import UpdWin6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateRc.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import InflateCall.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import AdlerModel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import ZChecksum.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflLoop6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import Callee6i.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import InflA_Check2.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import Infl6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import Infl6B.
Import InflLv Infl6A.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent iadler32_upd UPDATE_CHECK_bytes.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache.
Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section UwEnter.
  Variable v : icv.
  Hypothesis C : ictx v.

  Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 2 ^ 3 = 0.
  Proof.
    intros a H. change (2 ^ 3) with 8. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. subst a.
    replace (k * 16) with ((k * 2) * 8) by lia. apply Z.mod_mul. lia.
  Qed.
  Ltac ub_align_side :=
    lazymatch goal with
    | |- ?a mod 2 ^ 3 = 0 => first [change (2 ^ 3) with 8; lia | apply mod16_mod8; lia]
    end.

  Lemma uw_enter6 : forall s c r R M pend copy,
    LMEM v (mkW s c r) M -> 0 <= ir_put r <= cv_NO v -> cv_WN v <> 0 ->
    getr R 10 = zw (cv_ZP v) -> getr R 11 = zw pend -> getr R 12 = zw copy -> getr R 1 = zw pc6_uw_ret -> getr R 2 = zw (cv_sp v - INF_FRAME) ->
    0 <= pend < 2 ^ 63 -> 0 <= copy < 2 ^ 31 ->
    exists R1 M1,
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uw) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_uwj) M1 s6u_rom)
      /\ JUW v R1 M1 pend copy (bv_unsigned (getr R 8)) (bv_unsigned (getr R 9)) (bv_unsigned (getr R 18)) (bv_unsigned (getr R 19))
             (bv_unsigned (getr R 20)) (bv_unsigned (getr R 21))
      /\ (forall rg, reg_in rg [2; 8; 9; 10; 12; 19]%bv = false -> getr R1 rg = getr R rg)
      /\ LMEM v (mkW s c r) M1 /\ agree_out (SCR v) M M1 /\ (forall x, M x <> None -> M1 x <> None).
  Proof.
    intros s c r R M pend copy HM Hput HWN G10 G11 G12 G1 G2 Bpend Bcopy. unfold INF_FRAME in G2. unfold pc6_uw_ret in G1.
    open_ictx C. pose proof HM as HM0. open_lmem HM. open_zs Mzs. unfold mapped in *.
    assert (HWB : 0 < cv_WB v /\ cv_WN v = 32768) by (clear - CWB HWN; lia).
    pose proof (is6_window _ _ _ _ Msc) as C72. cbn [q_window] in C72.
    symex s6u_segs (CFG [] [] [] [pc6_uwj] []) 30%nat [false; false; false; true]
      [RVal (EVar 33%nat); RVal (EVar 37%nat)]
      [(2, EVar 32%nat); (10, EVar 34%nat); (11, EVar 35%nat); (12, EVar 39%nat); (1, EVar 36%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 64); (37%nat, 2 ^ 63); (38%nat, 2 ^ 64); (39%nat, 2 ^ 31)]
      NoRegions [cv_sp v - 256; cv_S v; cv_ZP v; pend; 0x2163c; cv_WB v; cv_opq v; copy] NoVals F0 F0'
      (mkst R (Z_to_bv 64 pc6_uw) M s6u_rom) R' HR' Hfr Hms.
    all: try (unfold INF_FRAME in *; arm_side).
    all: try ub_align_side.
    all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFTUE" G end.
    match type of Hms with msteps _ _ (mkst _ _ ?Mx _) => exists R', Mx end.
    split; [by_run Hms|].
    symex_reg HR' (8%bv : reg) as Q8. symex_reg HR' (9%bv : reg) as Q9. symex_reg HR' (19%bv : reg) as Q19. symex_reg HR' (2%bv : reg) as Q2. symex_reg HR' (10%bv : reg) as Q10.
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?Mx _) =>
      assert (AG : agree_out (SCR v) M Mx)
        by (unfold INF_FRAME in *; do 7 (apply (agree_scratch_store v C); [| unfold INF_FRAME, INF_SCRATCH; cbn; lia | unfold INF_FRAME, INF_SCRATCH; cbn; lia]); apply agree_out_refl)
    end.
    split.
    { unfold JUW, uw_regs, UWF, INF_FRAME. split; [| split; [exact Q10 | repeat match goal with |- _ /\ _ => split end; tower_cell]].
      rewrite Q8, Q9, Q19, Q2. repeat split; try reflexivity; f_equal; lia. }
    split; [fr_weak Hfr|].
    split; [| split; [exact AG | intros x Hx; repeat apply wbytes_grows; exact Hx]].
    apply (LMEM_agree_scratch v C s c r M _ HM0 Hput AG). intros x Hx; repeat apply wbytes_grows; exact Hx.
  Qed.
End UwEnter.


Section Call.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis MEMCPY : memcpy_run6u.
  Variable ROM : (word -> option byte) -> Prop.
  Hypothesis ROMok : forall M, rod6_clear M -> ROM M.
  Hypothesis ADLER : adler32_run6u ROM.
  Hypothesis LOOP : loop_stmt.

  Local Abbreviation NI := (cv_NI v). Local Abbreviation NO := (cv_NO v).
  Local Abbreviation WN := (cv_WN v). Local Abbreviation TOT0 := (cv_TOT0 v).

  Lemma call_loop : forall s (c : icall) M,
    CMEM v s c M ->
    HEAD <= is_mode s <= MEM -> 0 <= is_bits s < 64 -> 0 <= is_hold s < 2 ^ 64 ->
    ic_avail_in c = NI -> ic_avail_out c = NO -> ic_next_in c = 0 -> ic_next_out c = 0 ->
    0 < cv_fa v -> 0 < cv_ff v ->
    getr (cv_R0 v) 2 = zw (cv_sp v) -> getr (cv_R0 v) 10 = zw (cv_ZP v) -> getr (cv_R0 v) 11 = zw (cv_flush v) ->
    LX v (W1M s c) -> pinv NI NO WN TOT0 (W1M s c) ->
    let '(stop, w') := inf_loop ivar_ref (cv_flush v) (W1M s c) in
    exists R2 M2,
      msteps s6u_segs (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) (mkst R2 (Z_to_bv 64 (stop_pc stop)) M2 s6u_rom)
      /\ loop_post v (W1M s c) stop w' R2 M2
      /\ (forall x, M x <> None -> M2 x <> None)
      /\ (forall x : word,
            ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) -> ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
            ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) -> ~ (cv_P0 v <= bv_unsigned x < cv_P0 v + ir_put (w_r w')) ->
            M2 x = M x).
  Proof.
    intros s c M HM Hmode Hbits Hhold Hai Hao Hni Hno HFA HFF G2 G10 G11 HX HP.
    destruct (pro_run v C s c M HM Hmode Hbits Hhold Hai Hao Hni Hno HFA HFF G2 G10 G11) as (R1 & M1 & Hms1 & HM1 & HRC1 & HF1 & HV1 & G26 & AG1 & Gr1).
    assert (HE1 : ENTRY v (W1M s c) R1 M1).
    { split; [exact HM1|]. split; [exact HRC1|]. split; [exact HX|]. split; [exact HF1|]. split; [exact HV1|]. intros _; exact G26. }
    pose proof (LOOP v (W1M s c) R1 M1 C HE1 HP) as L.
    destruct (inf_loop ivar_ref (cv_flush v) (W1M s c)) as [stop w'].
    destruct L as (R2 & M2 & Hms2 & HLP & HMF).
    exists R2, M2. split.
    { eapply msteps_trans; [exact Hms1|]. unfold W1M in Hms2 at 1. cbn [w_s] in Hms2. exact Hms2. }
    split; [exact HLP|].
    destruct HMF as (_ & Hg2 & HE2). split; [intros x Hx; apply Hg2, Gr1, Hx|].
    intros x N1 N2 N3 N4. pose proof (ic_sp _ C) as Csp. pose proof (ic_S _ C) as CS. unfold INF_FRAME, INF_SCRATCH in *.
    rewrite (HE2 x); [| lia | exact N2 | exact N3 | unfold W1M; cbn [w_r ir_put]; rewrite Hno; lia].
    apply AG1. intros [Hin|[Hin|Hin]]; [cbn in Hin; lia | cbn in Hin; lia | exact Hin].
  Qed.


  Definition ckA (s : inflate_state) (c : icall) (r : iregs) : Z :=
    iadler32_upd (is_check s) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r)).
  Definition sL (s : inflate_state) (c : icall) (r : iregs) : inflate_state :=
    if noupd s r then sT s r else iset_check (sT s r) (ckA s c r).
  Definition cL (s : inflate_state) (c : icall) (r : iregs) : icall :=
    icset_data_type (if noupd s r then cT v c r else icset_adler (cT v c r) (ckA s c r)) (dtv (sL s c r)).

  Lemma sL_fields : forall s c r,
    is_bits (sL s c r) = is_bits s /\ is_last (sL s c r) = is_last s /\ is_mode (sL s c r) = is_mode s
    /\ is_wrap (sL s c r) = is_wrap s /\ is_wbits (sL s c r) = is_wbits s /\ is_flags (sL s c r) = is_flags s
    /\ is_havedict (sL s c r) = is_havedict s /\ is_window (sL s c r) = is_window s /\ is_window_blk (sL s c r) = is_window_blk s
    /\ is_wsize (sL s c r) = is_wsize s.
  Proof. intros s c r. unfold sL, sT. destruct (noupd s r); destruct s; repeat split; reflexivity. Qed.
  Lemma sL_fields2 : forall s c r,
    is_whave (sL s c r) = is_whave s /\ is_wnext (sL s c r) = is_wnext s /\ is_lens (sL s c r) = is_lens s
    /\ is_work (sL s c r) = is_work s /\ is_codes (sL s c r) = is_codes s /\ is_hold (sL s c r) = is_hold s.
  Proof. intros s c r. unfold sL, sT. destruct (noupd s r); destruct s; repeat split; reflexivity. Qed.

  Lemma cL_fields : forall s c r,
    ic_next_out (cL s c r) = ic_next_out c /\ ic_input (cL s c r) = ic_input c /\ ic_msg (cL s c r) = ic_msg c
    /\ ic_next_in (cL s c r) = ic_next_in c /\ ic_avail_in (cL s c r) = ic_avail_in c /\ ic_avail_out (cL s c r) = ic_avail_out c
    /\ ic_outbuf (cL s c r) = ic_outbuf c.
  Proof. intros s c r. unfold cL, cT. destruct (noupd s r); destruct c; repeat split; reflexivity. Qed.

  Lemma CMEM_of_LMEM' : forall s c r M, LMEM v (mkW s c r) M -> ir_put r = ic_next_out c -> CMEM v s c M.
  Proof. intros s c r M HM Hp. destruct HM. cbn [w_s w_c w_r] in *. rewrite Hp in *. constructor; assumption. Qed.

  Lemma uw_s1_iset_total : forall s m, uw_s1 (iset_total s m) = iset_total (uw_s1 s) m.
  Proof. intros s m. unfold uw_s1. destruct s. cbn. destruct (_ =? 0); reflexivity. Qed.
  Lemma uw_s1_iset_check : forall s m, uw_s1 (iset_check s m) = iset_check (uw_s1 s) m.
  Proof. intros s m. unfold uw_s1. destruct s. cbn. destruct (_ =? 0); reflexivity. Qed.
  Lemma uwc_big_total : forall s1 (wb : arr) m,
    iset_whave (iset_wnext (iset_window (iset_total s1 m) wb) 0) 32768 = iset_total (iset_whave (iset_wnext (iset_window s1 wb) 0) 32768) m.
  Proof. intros s1 wb m. destruct s1; reflexivity. Qed.
  Lemma uwc_big_check : forall s1 (wb : arr) m,
    iset_whave (iset_wnext (iset_window (iset_check s1 m) wb) 0) 32768 = iset_check (iset_whave (iset_wnext (iset_window s1 wb) 0) 32768) m.
  Proof. intros s1 wb m. destruct s1; reflexivity. Qed.
  Lemma uwc_big_fields : forall s1 (wb : arr),
    let s2 := iset_whave (iset_wnext (iset_window s1 wb) 0) 32768 in
    is_bits s2 = is_bits s1 /\ is_hold s2 = is_hold s1 /\ is_mode s2 = is_mode s1 /\ is_last s2 = is_last s1
    /\ is_wrap s2 = is_wrap s1 /\ is_wbits s2 = is_wbits s1 /\ is_flags s2 = is_flags s1 /\ is_havedict s2 = is_havedict s1
    /\ is_total s2 = is_total s1 /\ is_check s2 = is_check s1 /\ is_window_blk s2 = is_window_blk s1.
  Proof. intros s1 wb. destruct s1; repeat split; reflexivity. Qed.
  Lemma uw_s1_fields : forall s,
    let s2 := uw_s1 s in
    is_bits s2 = is_bits s /\ is_hold s2 = is_hold s /\ is_mode s2 = is_mode s /\ is_last s2 = is_last s
    /\ is_wrap s2 = is_wrap s /\ is_wbits s2 = is_wbits s /\ is_flags s2 = is_flags s /\ is_havedict s2 = is_havedict s
    /\ is_total s2 = is_total s /\ is_check s2 = is_check s /\ is_window_blk s2 = is_window_blk s.
  Proof. intros s. unfold uw_s1. destruct (is_wsize s =? 0); destruct s; repeat split; reflexivity. Qed.
  Lemma uwc_iset_total : forall s src e copy m, uwc (iset_total s m) src e copy = iset_total (uwc s src e copy) m.
  Proof.
    intros s src e copy m. unfold uwc, uw_dist. rewrite uw_s1_iset_total. generalize (uw_s1 s); intros s1.
    replace (is_wnext (iset_total s1 m)) with (is_wnext s1) by (destruct s1; reflexivity).
    replace (is_whave (iset_total s1 m)) with (is_whave s1) by (destruct s1; reflexivity).
    replace (is_window (iset_total s1 m)) with (is_window s1) by (destruct s1; reflexivity).
    destruct (32768 <=? copy); [apply uwc_big_total|].
    set (dist := if copy <? 32768 - is_wnext s1 then copy else 32768 - is_wnext s1).
    replace (is_window (iset_window (iset_total s1 m) (arr_blit (is_window s1) (is_wnext s1) src (e - copy) dist)))
      with (is_window (iset_window s1 (arr_blit (is_window s1) (is_wnext s1) src (e - copy) dist))) by (destruct s1; reflexivity).
    destruct (negb _); [destruct s1; reflexivity|].
    destruct (is_whave s1 <? 32768); destruct s1; reflexivity.
  Qed.
  Lemma uwc_iset_check : forall s src e copy m, uwc (iset_check s m) src e copy = iset_check (uwc s src e copy) m.
  Proof.
    intros s src e copy m. unfold uwc, uw_dist. rewrite uw_s1_iset_check. generalize (uw_s1 s); intros s1.
    replace (is_wnext (iset_check s1 m)) with (is_wnext s1) by (destruct s1; reflexivity).
    replace (is_whave (iset_check s1 m)) with (is_whave s1) by (destruct s1; reflexivity).
    replace (is_window (iset_check s1 m)) with (is_window s1) by (destruct s1; reflexivity).
    destruct (32768 <=? copy); [apply uwc_big_check|].
    set (dist := if copy <? 32768 - is_wnext s1 then copy else 32768 - is_wnext s1).
    replace (is_window (iset_window (iset_check s1 m) (arr_blit (is_window s1) (is_wnext s1) src (e - copy) dist)))
      with (is_window (iset_window s1 (arr_blit (is_window s1) (is_wnext s1) src (e - copy) dist))) by (destruct s1; reflexivity).
    destruct (negb _); [destruct s1; reflexivity|].
    destruct (is_whave s1 <? 32768); destruct s1; reflexivity.
  Qed.
  Lemma uwc_fields : forall s src e copy,
    let s2 := uwc s src e copy in
    is_bits s2 = is_bits s /\ is_hold s2 = is_hold s /\ is_mode s2 = is_mode s /\ is_last s2 = is_last s
    /\ is_wrap s2 = is_wrap s /\ is_wbits s2 = is_wbits s /\ is_flags s2 = is_flags s /\ is_havedict s2 = is_havedict s
    /\ is_total s2 = is_total s /\ is_check s2 = is_check s /\ is_window_blk s2 = is_window_blk s.
  Proof.
    intros s src e copy. cbv zeta. unfold uwc.
    destruct (32768 <=? copy).
    { pose proof (uwc_big_fields (uw_s1 s) (arr_blit (is_window (uw_s1 s)) 0 src (e - 32768) 32768)) as B. cbv zeta in B.
      pose proof (uw_s1_fields s) as A. cbv zeta in A.
      destruct B as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11).
      destruct A as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11).
      rewrite B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11. repeat split; assumption. }
    destruct (negb _); [| destruct (is_whave (uw_s1 s) <? 32768)]; unfold uw_s1; destruct (is_wsize s =? 0); destruct s; repeat split; reflexivity.
  Qed.
  Lemma sL_uwc : forall s c r src e copy,
    sL (uwc s src e copy) c r = uwc (sL s c r) src e copy /\ cL (uwc s src e copy) c r = cL s c r.
  Proof.
    intros s c r src e copy.
    pose proof (uwc_fields s src e copy) as U. cbv zeta in U. destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
    assert (EsT : sT (uwc s src e copy) r = uwc (sT s r) src e copy) by (unfold sT; rewrite U9, uwc_iset_total; reflexivity).
    assert (Eck : ckA (uwc s src e copy) c r = ckA s c r) by (unfold ckA; rewrite U10; reflexivity).
    assert (Enu : noupd (uwc s src e copy) r = noupd s r) by (unfold noupd; rewrite U5; reflexivity).
    assert (EsL : sL (uwc s src e copy) c r = uwc (sL s c r) src e copy).
    { unfold sL. rewrite EsT, Eck, Enu. destruct (noupd s r); [reflexivity | symmetry; apply uwc_iset_check]. }
    split; [exact EsL|].
    unfold cL. rewrite EsL, Eck, Enu.
    pose proof (uwc_fields (sL s c r) src e copy) as W. cbv zeta in W. destruct W as (W1 & W2 & W3 & W4 & _).
    unfold dtv. rewrite W1, W3, W4. reflexivity.
  Qed.

  Definition CCUR (cf : icall) : Prop :=
    0 <= ic_next_in cf /\ 0 <= ic_avail_in cf /\ ic_next_in cf + ic_avail_in cf = NI
    /\ 0 <= ic_next_out cf /\ 0 <= ic_avail_out cf /\ ic_next_out cf + ic_avail_out cf = NO
    /\ (forall i, 0 <= i < ic_next_out cf -> 0 <= arr_get (ic_outbuf cf) i < 256).
  Lemma CCUR_cLR : forall s c r, CINV NI NO c -> RINV NI NO r -> CCUR (cL (sR s r) (cR c r) r).
  Proof.
    intros s c r HC HR. pose proof (cL_fields (sR s r) (cR c r) r) as (L1 & L2 & L3 & L4 & L5 & L6 & L7).
    pose proof (cR_fields c r) as (F1 & F2 & F3 & F4 & F5 & F6 & _).
    unfold CCUR. rewrite L1, L4, L5, L6, L7, F1, F2, F3, F4, F6. unfold CINV, RINV in *.
    destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Cob & _).
    repeat match goal with |- _ /\ _ => split end; try lia. intros i Hi. apply Cob. lia.
  Qed.


  Lemma iset_total_facts : forall s m,
    is_wrap (iset_total s m) = is_wrap s /\ is_flags (iset_total s m) = is_flags s /\ is_check (iset_total s m) = is_check s
    /\ is_bits (iset_total s m) = is_bits s /\ is_last (iset_total s m) = is_last s /\ is_mode (iset_total s m) = is_mode s.
  Proof. intros s m. destruct s; repeat split; reflexivity. Qed.

  Lemma leave_tail_eq : forall flush s (c : icall) r,
    ic_avail_in c = ir_have r -> ic_avail_out c = ir_left r -> ic_next_out c = ir_put r -> ir_in r = NI -> (is_wrap s = 5 \/ is_wrap s = 1) ->
    (is_flags s = 0 \/ ir_out r = ir_left r) ->
    0 <= NI - ir_have r < 2 ^ 32 -> 0 <= ir_out r - ir_left r < 2 ^ 32 ->
    leave_tail flush s c r = (sL s c r, zret_of_icall (cL s c r) (retv v flush r)).
  Proof.
    intros flush s c r Hai Hao Hno Hin Hw Hf Bin Bout.
    pose proof (iset_total_facts s (wrap64 (is_total s + (ir_out r - ir_left r)))) as (T1 & T2 & T3 & T4 & T5 & T6).
    pose proof (icset_total_in_facts c (wrap64 (ic_total_in c + (cv_NI v - ir_have r)))) as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
    pose proof (icset_total_out_facts (icset_total_in c (wrap64 (ic_total_in c + (cv_NI v - ir_have r)))) (wrap64 (ic_total_out c + (ir_out r - ir_left r)))) as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9 & O10 & O11).
    unfold leave_tail. rewrite Hai, Hao, Hin. rewrite !wrap32_id by lia. cbv zeta. rewrite I7. rewrite T1.
    unfold cL; unfold sL; unfold noupd, sT, cT, ckA, retv, dtv.
    destruct Hw as [Hw|Hw]; rewrite Hw.
    2:{
      change (negb (Z.land 1 4 =? 0)) with false. change (1 =? 1) with true. rewrite orb_true_r. cbn [andb]. reflexivity. }
    change (negb (Z.land 5 4 =? 0)) with true. change (5 =? 1) with false. rewrite orb_false_r. cbn [andb].
    destruct (Z.eqb_spec (ir_out r - ir_left r) 0) as [E0|E0]; cbn [negb].
    - reflexivity.
    - destruct Hf as [Hf|Hf]; [| exfalso; lia].
      unfold UPDATE_CHECK_bytes. rewrite T2, Hf. cbn [Z.eqb negb]. rewrite T3, O6, I6, O3, I3, Hno. reflexivity.
  Qed.

  Lemma srng_win : forall s, SRNGq s ->
    0 <= is_wsize s < 2 ^ 32 /\ 0 <= is_whave s < 2 ^ 32 /\ 0 <= is_wnext s < 2 ^ 32
    /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s /\ is_whave s <= is_wsize s)
    /\ (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s).
  Proof.
    intros s H. unfold SRNGq in H.
    destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hws & Hwh & Hwn & H).
    do 14 (destruct H as [_ H]). destruct H as (_ & A & B).
    repeat split; try lia; intros; try apply A; try apply B; assumption.
  Qed.



  Lemma LVCK : forall w w',
    pinv NI NO WN TOT0 w -> inf_loop ivar_ref (cv_flush v) w = (SLeave, w') ->
    ir_out (w_r w') <> ir_left (w_r w') -> Z.land (is_wrap (w_s w')) 4 <> 0 -> is_flags (w_s w') = 0 ->
    ck_adl (is_check (w_s w')).
  Proof.
    intros w w' PI E. pose proof PI as ((NI32 & NO32) & _).
    exact (inf_loop_leave ivar_ref (cv_flush v) NI NO WN TOT0 NI32 NO32 w w' PI E).
  Qed.

  Lemma needv_tail : forall s c r, needv v (sL (sR s r) (cR c r) r) r = needv v s r.
  Proof.
    intros s c r. pose proof (sL_fields (sR s r) (cR c r) r) as (_ & _ & Fm & _ & _ & _ & _ & _ & _ & Fws).
    pose proof (sR_fields s r) as (_ & _ & Y3 & _ & _ & _ & _ & _ & _ & _ & Y11 & _).
    unfold needv. rewrite Fm, Fws, Y3, Y11. reflexivity.
  Qed.

  Lemma lv_tail : forall s c r R M,
    LMEM v (mkW s c r) M -> LREG_leave v (mkW s c r) R -> RINV NI NO r -> CINV NI NO c ->
    ir_in r = NI -> (is_wrap s = 5 \/ is_wrap s = 1) -> (is_flags s = 0 \/ ir_out r = ir_left r) ->
    HEAD <= is_mode s <= MEM -> 0 <= ir_bits r < 64 -> - 2 ^ 31 <= is_last s < 2 ^ 31 ->
    0 <= is_total s < 2 ^ 64 -> 0 <= is_check s < 2 ^ 64 -> - 2 ^ 31 <= ir_ret r < 2 ^ 31 ->
    (is_wsize s = 0 \/ is_wsize s = 32768) ->
    (noupd s r = false -> adler_canon (is_check s)) ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_leave) M s6u_rom)
                     (mkst R' (Z_to_bv 64 (if needv v s r then pc6_uw else pc6_ret)) M' s6u_rom)
      /\ LMEM v (mkW (sL (sR s r) (cR c r) r) (cL (sR s r) (cR c r) r) r) M'
      /\ getr R' 2 = zw (cv_sp v - 256) /\ getr R' 3 = getr (cv_R0 v) 3 /\ getr R' 4 = getr (cv_R0 v) 4 /\ getr R' 8 = zw (cv_S v)
      /\ getr R' 23 = zw (ir_have r) /\ getr R' 18 = zw (cv_ZP v) /\ getr R' 9 = zw (cv_P0 v + ir_put r) /\ getr R' 19 = zw (ir_bits r)
      /\ (needv v s r = true ->
            getr R' 10 = zw (cv_ZP v) /\ getr R' 11 = zw (cv_P0 v + ir_put r) /\ getr R' 12 = zw (ir_out r - ir_left r)
            /\ getr R' 1 = zw pc6_uw_ret /\ getr R' 20 = zw (ir_out r - ir_left r) /\ getr R' 27 = zw (ir_ret r))
      /\ (needv v s r = false -> getr R' 10 = zw (retv v (cv_flush v) r))
      /\ (forall x, M x <> None -> M' x <> None)
      /\ (forall x : word,
            ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) -> ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
            ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) -> M' x = M x).
  Proof.
    intros s c r R M HM HR RI CI Hin Hw Hf Hmode Hbits Hlast Htot Hck Hret Hws Hcan.
    pose proof (pins_of_leave _ _ _ _ _ HR) as (P2 & P27 & P13 & P8 & P11 & P24 & P9 & P22 & P18 & P25 & P26 & P3 & P4).
    pose proof (ic_sp _ C) as Csp. pose proof (ic_S _ C) as CS. pose proof (ic_ZP _ C) as CZP. pose proof (ic_P0 _ C) as CP0.
    pose proof RI as RI0. open_rinv RI. pose proof CI as CI0. open_cinv CI.
    assert (Hput : 0 <= ir_put r <= NO) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (Hout : 0 <= ir_out r - ir_left r <= ir_put r /\ ir_out r - ir_left r < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    pose proof (sR_fields s r) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
    pose proof (cR_fields c r) as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11).
    pose proof (sT_fields (sR s r) r) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
    pose proof (cT_fields v (cR c r) r) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    rewrite <- (needv_tail s c r).
    destruct (lv_T1 v C s c r R M HM HR RI0 CI0 Hin Hw Hf Htot Hck Hret)
      as (R1 & Hms1 & HM1 & Hfr1 & Q19 & Q2 & Q26 & Q24 & Q9 & Q27 & Q8 & Q18 & Q3 & Q4 & Qz & Qnz).
    set (s1 := sT (sR s r) r) in *. set (c1 := cT v (cR c r) r) in *.
    assert (Enu : noupd (sR s r) r = noupd s r) by (unfold noupd; rewrite Y5; reflexivity).
    destruct (Bool.bool_dec (noupd s r) true) as [E0|E0]; [| apply not_true_is_false in E0]; rewrite E0 in Hms1.
    -
      destruct (Qz E0) as (Q13 & Q11).
      assert (Esl : sL (sR s r) (cR c r) r = s1) by (unfold sL; rewrite Enu, E0; reflexivity).
      assert (Ecl : cL (sR s r) (cR c r) r = icset_data_type c1 (dtv s1)) by (unfold cL; rewrite Enu, E0, Esl; reflexivity).
      rewrite Esl, Ecl.
      destruct (lv_T3 v C s1 c1 r R1 (MT1 v s c r M) HM1 RI0 ltac:(subst c1; rewrite K1; exact X3)
                  ltac:(subst s1; rewrite T1, Y1; exact Hbits) ltac:(subst s1; rewrite T4, Y4; exact Hlast) ltac:(subst s1; rewrite T3, Y3; exact Hmode)
                  ltac:(subst s1; rewrite T9, Y11; exact Hws)
                  Q2 Q27 Q13 Q8 Q11 Q19)
        as (R2 & bs & Hms2 & Hbl & Ebs & Q2' & Hfr2 & QT & QF).
      pose proof (LMEM_store_dt v C s1 c1 r (MT1 v s c r M) (dtv s1) bs HM1 Hput Hbl) as HM2.
      assert (FT : forall x : word, ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) -> ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) ->
                   wbytes (MT1 v s c r M) (zw (cv_ZP v + 88)) bs x = M x).
      { intros x N2 N3. pose proof (u64_range x). rewrite wbytes_inside; [apply (MT1_other v C); assumption | lia | rewrite Hbl; cbn; lia | rewrite Hbl; cbn; lia]. }
      destruct (needv v s1 r) eqn:EN.
      +
        destruct (QT eq_refl) as (C10 & C11 & C12 & C1).
        exists R2, (wbytes (MT1 v s c r M) (zw (cv_ZP v + 88)) bs).
        split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        split; [exact HM2|].
        split; [exact Q2'|]. split; [rewrite (Hfr2 (3%bv : reg) eq_refl); exact Q3|]. split; [rewrite (Hfr2 (4%bv : reg) eq_refl); exact Q4|].
        split; [rewrite (Hfr2 (8%bv : reg) eq_refl); exact Q27|].
        split; [rewrite (Hfr2 (23%bv : reg) eq_refl); exact Q24|].
        split; [rewrite (Hfr2 (18%bv : reg) eq_refl); exact Q8|]. split; [rewrite (Hfr2 (9%bv : reg) eq_refl); exact Q9|]. split; [rewrite (Hfr2 (19%bv : reg) eq_refl); exact Q18|].
        split; [intros _; split; [exact C10 | split; [exact C11 | split; [exact C12 | split; [exact C1 | split; [rewrite (Hfr2 (20%bv : reg) eq_refl); exact Q19 | rewrite (Hfr2 (27%bv : reg) eq_refl); exact Q26]]]]]|].
        split; [intros X; discriminate X|].
        split; [intros x Hx; apply wbytes_grows; apply (MT1_grows v); exact Hx|].
        intros x N1 N2 N3. apply FT; assumption.
      +
        pose proof (QF eq_refl) as C11.
        destruct (lv_ret v C _ _ r R2 (wbytes (MT1 v s c r M) (zw (cv_ZP v + 88)) bs) HM2 RI0 Hret Q2' C11
                    ltac:(rewrite (Hfr2 (23%bv : reg) eq_refl); exact Q24) ltac:(rewrite (Hfr2 (27%bv : reg) eq_refl); exact Q26))
          as (R3 & Hms3 & A10 & A2 & Hfr3).
        exists R3, (wbytes (MT1 v s c r M) (zw (cv_ZP v + 88)) bs).
        split; [eapply msteps_trans; [exact Hms1 | eapply msteps_trans; [exact Hms2 | exact Hms3]]|].
        split; [exact HM2|].
        split; [exact A2|]. split; [rewrite (Hfr3 (3%bv : reg) eq_refl), (Hfr2 (3%bv : reg) eq_refl); exact Q3|].
        split; [rewrite (Hfr3 (4%bv : reg) eq_refl), (Hfr2 (4%bv : reg) eq_refl); exact Q4|].
        split; [rewrite (Hfr3 (8%bv : reg) eq_refl), (Hfr2 (8%bv : reg) eq_refl); exact Q27|].
        split; [rewrite (Hfr3 (23%bv : reg) eq_refl), (Hfr2 (23%bv : reg) eq_refl); exact Q24|].
        split; [rewrite (Hfr3 (18%bv : reg) eq_refl), (Hfr2 (18%bv : reg) eq_refl); exact Q8|].
        split; [rewrite (Hfr3 (9%bv : reg) eq_refl), (Hfr2 (9%bv : reg) eq_refl); exact Q9|].
        split; [rewrite (Hfr3 (19%bv : reg) eq_refl), (Hfr2 (19%bv : reg) eq_refl); exact Q18|].
        split; [intros X; discriminate X|].
        split; [intros _; exact A10|].
        split; [intros x Hx; apply wbytes_grows; apply (MT1_grows v); exact Hx|].
        intros x N1 N2 N3. apply FT; assumption.
    -
      assert (Eo0 : ir_out r - ir_left r <> 0).
      { unfold noupd in E0. apply Bool.orb_false_iff in E0. destruct E0 as [E0a _]. apply Z.eqb_neq in E0a. exact E0a. }
      destruct Hf as [Hf|Hf]; [| exfalso; clear - Eo0 Hf; lia].
      destruct (Qnz E0) as (Q10 & Q11 & Q12 & Q1).
      specialize (Hcan E0).
      assert (Esl : sL (sR s r) (cR c r) r = iset_check s1 (ckA (sR s r) (cR c r) r)) by (unfold sL; rewrite Enu, E0; reflexivity).
      assert (Ecl : cL (sR s r) (cR c r) r = icset_data_type (icset_adler c1 (ckA (sR s r) (cR c r) r)) (dtv (sL (sR s r) (cR c r) r)))
        by (unfold cL; rewrite Enu, E0; reflexivity).
      assert (EckA : ckA (sR s r) (cR c r) r = iadler32_upd (is_check s) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r)))
        by (unfold ckA; rewrite Y10, X6; reflexivity).
      set (A := ckA (sR s r) (cR c r) r) in *.
      set (n := Z.to_nat (ir_out r - ir_left r)).
      assert (Hn : Z.of_nat n = ir_out r - ir_left r) by (subst n; apply Z2Nat.id; clear - Hout; lia).
      set (d := cbytes (arr_get (ic_outbuf c)) (ir_put r - (ir_out r - ir_left r)) n).
      assert (Hlen : length d = n) by (subst d; apply cbytes_length).
      pose proof HM1 as HM1'. open_lmem HM1'. unfold mapped in *.
      assert (Eob : ic_outbuf c1 = ic_outbuf c) by (subst c1; rewrite K7; exact X6).
      rewrite Eob in Mout.
      pose proof (cells_rdn_bytes s6u_segs (MT1 v s c r M) (cv_P0 v) (ir_put r) (arr_get (ic_outbuf c)) (ir_put r - (ir_out r - ir_left r)) n Mout
                    ltac:(clear - Hout; lia) ltac:(rewrite Hn; clear - Hout; lia) ltac:(clear - CP0; lia) ltac:(clear - CP0 Hput; lia)) as Hrdn.
      fold d in Hrdn. rewrite <- Hlen in Hrdn.
      assert (HNO : 0 < NO) by (clear - Eo0 Hout Hput; lia).
      pose proof (ic_d_fP _ C HNO) as CfP.
      destruct (ADLER (MT1 v s c r M) R1 (is_check s) (cv_P0 v + (ir_put r - (ir_out r - ir_left r))) d (cv_sp v - 256) (zw 0x2159c) Hrdn
                  ltac:(clear - Hck; lia) Hcan ltac:(clear - CP0 Hout Hput; lia)
                  ltac:(rewrite Hlen, Hn; clear - CP0 Hout Hput; lia) ltac:(rewrite Hlen, Hn; clear - Hout; lia)
                  ltac:(unfold ADLER_FR6U, IMG6_TOP, INF_FRAME, INF_SCRATCH in *; clear - Csp; lia) ltac:(clear - Csp; lia))
        as (R2 & M2 & Hms2 & B10 & B2 & Hfr2 & AG & Hg2).
      { intros x Hx. apply Mmap_f. unfold ADLER_FR6U in Hx. clear - Hx. lia. }
      { rewrite Hlen, Hn. intros _. unfold sep, ADLER_FR6U, INF_FRAME, INF_SCRATCH in *. clear - CfP Hout Hput Rpl CP0. lia. }
      { apply ROMok. exact Mrod. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { exact Q1. }
      { exact Q2. }
      { exact Q10. }
      { change (reg_get R1 11) with (getr R1 11). rewrite Q11. reflexivity. }
      { change (reg_get R1 12) with (getr R1 12). rewrite Q12, Hlen, Hn. reflexivity. }
      assert (EA : adler32_z_spec (is_check s) (cv_P0 v + (ir_put r - (ir_out r - ir_left r))) d = A).
      { rewrite (adler32_z_spec_canon _ _ _ Hcan) by (clear - CP0 Hout Hput; lia). subst A. rewrite EckA. unfold iadler32_upd. subst d.
        rewrite bZ_cbytes; [rewrite Hn; reflexivity|]. intros i Hi. apply Coutb. rewrite Hn in Hi. clear - Hi Hout Hput. lia. }
      rewrite EA in B10. change (reg_get R2 10) with (getr R2 10) in B10. change (reg_get R2 2) with (getr R2 2) in B2.
      assert (HA32 : 0 <= A < 2 ^ 32).
      { pose proof (adler32_model_canon (is_check s) (arr_slice (ic_outbuf c) (ir_put r - (ir_out r - ir_left r)) (ir_out r - ir_left r))) as HAc.
        subst A. rewrite EckA. unfold iadler32_upd. destruct HAc as (HA & _ & _). exact HA. }
      assert (AG' : agree_out (SCR v) (MT1 v s c r M) M2).
      { eapply agree_out_weaken; [exact AG|]. intros x Hx. unfold SCR, INF_FRAME, INF_SCRATCH, ADLER_FR6U in *. cbn in Hx |- *. clear - Hx. lia. }
      clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mleftc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      pose proof (LMEM_agree_scratch v C s1 c1 r (MT1 v s c r M) M2 HM1 Hput AG' Hg2) as HM2.
      destruct (lv_T2 v C s1 c1 r R2 M2 A HM2 Hput ltac:(clear - HA32; lia) B2
                  ltac:(rewrite (Hfr2 (8%bv : reg) eq_refl); exact Q27) ltac:(rewrite (Hfr2 (18%bv : reg) eq_refl); exact Q8) B10)
        as (R3 & Hms3 & HM3 & C13 & C11 & Hfr3).
      set (M3 := wbytes (wbytes M2 (zw (cv_S v + 40)) (Z_to_le_bytes 8 A)) (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 A)) in *.
      set (s2 := iset_check s1 A) in *. set (c2 := icset_adler c1 A) in *.
      pose proof (icset_adler_facts c1 A) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
      assert (Fb2 : is_bits s2 = ir_bits r) by (subst s2 s1; transitivity (is_bits (sT (sR s r) r)); [destruct (sT (sR s r) r); reflexivity | rewrite T1; exact Y1]).
      assert (Fl2 : is_last s2 = is_last s) by (subst s2 s1; transitivity (is_last (sT (sR s r) r)); [destruct (sT (sR s r) r); reflexivity | rewrite T4; exact Y4]).
      assert (Fm2 : is_mode s2 = is_mode s) by (subst s2 s1; transitivity (is_mode (sT (sR s r) r)); [destruct (sT (sR s r) r); reflexivity | rewrite T3; exact Y3]).
      assert (Fws2 : is_wsize s2 = is_wsize s) by (subst s2 s1; transitivity (is_wsize (sT (sR s r) r)); [destruct (sT (sR s r) r); reflexivity | rewrite T9; exact Y11]).
      assert (En2 : needv v s2 r = needv v s1 r) by (unfold needv; rewrite Fm2, Fws2; subst s1; rewrite T3, T9, Y3, Y11; reflexivity).
      destruct (lv_T3 v C s2 c2 r R3 M3 HM3 RI0 ltac:(subst c2 c1; rewrite U3, K1; exact X3)
                  ltac:(rewrite Fb2; exact Hbits) ltac:(rewrite Fl2; exact Hlast) ltac:(rewrite Fm2; exact Hmode) ltac:(rewrite Fws2; exact Hws)
                  ltac:(rewrite (Hfr3 (2%bv : reg) eq_refl); exact B2)
                  ltac:(rewrite (Hfr3 (8%bv : reg) eq_refl), (Hfr2 (8%bv : reg) eq_refl); exact Q27) C13
                  ltac:(rewrite (Hfr3 (18%bv : reg) eq_refl), (Hfr2 (18%bv : reg) eq_refl); exact Q8) C11
                  ltac:(rewrite (Hfr3 (20%bv : reg) eq_refl), (Hfr2 (20%bv : reg) eq_refl); exact Q19))
        as (R4 & bs & Hms4 & Hbl & Ebs & Q2' & Hfr4 & QT & QF).
      rewrite En2 in Hms4, QT, QF.
      pose proof (LMEM_store_dt v C s2 c2 r M3 (dtv s2) bs HM3 Hput Hbl) as HM4.
      assert (EsL2 : sL (sR s r) (cR c r) r = s2) by (rewrite Esl; reflexivity).
      assert (EcL2 : cL (sR s r) (cR c r) r = icset_data_type c2 (dtv s2)) by (rewrite Ecl, EsL2; reflexivity).
      rewrite EsL2, EcL2, En2.
      assert (FT : forall x : word, ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) ->
                   ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) -> ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) ->
                   wbytes M3 (zw (cv_ZP v + 88)) bs x = M x).
      { intros x N1 N2 N3. pose proof (u64_range x). unfold INF_FRAME, INF_SCRATCH in N1.
        rewrite wbytes_inside; [| lia | rewrite Hbl; cbn; lia | rewrite Hbl; cbn; lia].
        subst M3. rewrite !wbytes_inside; [| lia | cbn; lia | cbn; lia | lia | cbn; lia | cbn; lia].
        rewrite (AG x); [apply (MT1_other v C); assumption|].
        unfold ADLER_FR6U. intros [Hfr|Hfr]; [cbn in Hfr; lia | exact Hfr]. }
      assert (GR : forall x, M x <> None -> wbytes M3 (zw (cv_ZP v + 88)) bs x <> None).
      { intros x Hx. apply wbytes_grows. subst M3. apply wbytes_grows, wbytes_grows. apply Hg2. apply (MT1_grows v). exact Hx. }
      assert (Q24'' : getr R4 23 = zw (ir_have r)) by (rewrite (Hfr4 (23%bv : reg) eq_refl), (Hfr3 (23%bv : reg) eq_refl), (Hfr2 (23%bv : reg) eq_refl); exact Q24).
      assert (Q26'' : getr R4 27 = zw (ir_ret r)) by (rewrite (Hfr4 (27%bv : reg) eq_refl), (Hfr3 (27%bv : reg) eq_refl), (Hfr2 (27%bv : reg) eq_refl); exact Q26).
      assert (Q27'' : getr R4 8 = zw (cv_S v)) by (rewrite (Hfr4 (8%bv : reg) eq_refl), (Hfr3 (8%bv : reg) eq_refl), (Hfr2 (8%bv : reg) eq_refl); exact Q27).
      assert (Q8'' : getr R4 18 = zw (cv_ZP v)) by (rewrite (Hfr4 (18%bv : reg) eq_refl), (Hfr3 (18%bv : reg) eq_refl), (Hfr2 (18%bv : reg) eq_refl); exact Q8).
      assert (Q9'' : getr R4 9 = zw (cv_P0 v + ir_put r)) by (rewrite (Hfr4 (9%bv : reg) eq_refl), (Hfr3 (9%bv : reg) eq_refl), (Hfr2 (9%bv : reg) eq_refl); exact Q9).
      assert (Q18'' : getr R4 19 = zw (ir_bits r)) by (rewrite (Hfr4 (19%bv : reg) eq_refl), (Hfr3 (19%bv : reg) eq_refl), (Hfr2 (19%bv : reg) eq_refl); exact Q18).
      assert (Q3'' : getr R4 3 = getr (cv_R0 v) 3) by (rewrite (Hfr4 (3%bv : reg) eq_refl), (Hfr3 (3%bv : reg) eq_refl), (Hfr2 (3%bv : reg) eq_refl); exact Q3).
      assert (Q4'' : getr R4 4 = getr (cv_R0 v) 4) by (rewrite (Hfr4 (4%bv : reg) eq_refl), (Hfr3 (4%bv : reg) eq_refl), (Hfr2 (4%bv : reg) eq_refl); exact Q4).
      destruct (needv v s1 r) eqn:EN.
      + destruct (QT eq_refl) as (D10 & D11 & D12 & D1).
        exists R4, (wbytes M3 (zw (cv_ZP v + 88)) bs).
        split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2|]; eapply msteps_trans; [exact Hms3 | subst M3; exact Hms4]|].
        split; [exact HM4|].
        split; [exact Q2'|]. split; [exact Q3''|]. split; [exact Q4''|]. split; [exact Q27''|]. split; [exact Q24''|].
        split; [exact Q8''|]. split; [exact Q9''|]. split; [exact Q18''|].
        split; [intros _; split; [exact D10 | split; [exact D11 | split; [exact D12 | split; [exact D1 | split; [rewrite (Hfr4 (20%bv : reg) eq_refl), (Hfr3 (20%bv : reg) eq_refl), (Hfr2 (20%bv : reg) eq_refl); exact Q19 | exact Q26'']]]]]|].
        split; [intros X; discriminate X|].
        split; [exact GR | exact FT].
      + pose proof (QF eq_refl) as D11.
        destruct (lv_ret v C _ _ r R4 (wbytes M3 (zw (cv_ZP v + 88)) bs) HM4 RI0 Hret Q2' D11 Q24'' Q26'')
          as (R5 & Hms5 & A10 & A2 & Hfr5).
        exists R5, (wbytes M3 (zw (cv_ZP v + 88)) bs).
        split.
        { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
          eapply msteps_trans; [subst M3; exact Hms4 | exact Hms5]. }
        split; [exact HM4|].
        split; [exact A2|].
        split; [rewrite (Hfr5 (3%bv : reg) eq_refl); exact Q3''|]. split; [rewrite (Hfr5 (4%bv : reg) eq_refl); exact Q4''|].
        split; [rewrite (Hfr5 (8%bv : reg) eq_refl); exact Q27''|]. split; [rewrite (Hfr5 (23%bv : reg) eq_refl); exact Q24''|].
        split; [rewrite (Hfr5 (18%bv : reg) eq_refl); exact Q8''|]. split; [rewrite (Hfr5 (9%bv : reg) eq_refl); exact Q9''|]. split; [rewrite (Hfr5 (19%bv : reg) eq_refl); exact Q18''|].
        split; [intros X; discriminate X|].
        split; [intros _; exact A10|].
        split; [exact GR | exact FT].
  Qed.
  Lemma sL_back : forall s c r, is_back (sL s c r) = is_back s.
  Proof. intros s c r. unfold sL, sT. destruct (noupd s r); destruct s; reflexivity. Qed.
  Lemma sR_back : forall s r, is_back (sR s r) = is_back s.
  Proof. intros s r. destruct s; reflexivity. Qed.
  Lemma uwc_back : forall s src e copy, is_back (uwc s src e copy) = is_back s.
  Proof.
    intros s src e copy. unfold uwc.
    set (wb := arr_blit _ 0 _ _ 32768). clearbody wb.
    destruct (32768 <=? copy); [unfold uw_s1; destruct (is_wsize s =? 0); destruct s; reflexivity|].
    destruct (negb _); [| destruct (is_whave (uw_s1 s) <? 32768)]; unfold uw_s1; destruct (is_wsize s =? 0); destruct s; reflexivity.
  Qed.

  Theorem inflate_call6 : forall s zc M (ans : option (blk * (Z -> Z))),
    NI = zlength (zc_input zc) -> NO = zc_avail_out zc -> TOT0 = zs_total_out (zc_strm zc) -> WN = arr_len (is_window s) ->
    UI s -> zcall_ok zc -> LXS s -> - 1 <= zs_msg (zc_strm zc) <= 27 -> 0 < cv_fa v -> 0 < cv_ff v ->
    CMEM v s (icall_of_zcall zc) M ->
    getr (cv_R0 v) 2 = zw (cv_sp v) -> getr (cv_R0 v) 10 = zw (cv_ZP v) -> getr (cv_R0 v) 11 = zw (cv_flush v) ->
    snd (inflate_p ivar_ref ans s zc (cv_flush v)) = None ->
    let sf := fst (fst (inflate_p ivar_ref ans s zc (cv_flush v))) in
    let zf := snd (fst (inflate_p ivar_ref ans s zc (cv_flush v))) in
    exists R' M' (put' : Z),
      msteps s6u_segs (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) (mkst R' (getr (cv_R0 v) 1) M' s6u_rom)
      /\ getr R' 10 = zw (zr_rc zf) /\ getr R' 2 = zw (cv_sp v)
      /\ (forall rg : reg, In rg [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' rg = getr (cv_R0 v) rg)
      /\ getr R' 3 = getr (cv_R0 v) 3 /\ getr R' 4 = getr (cv_R0 v) 4
      /\ 0 <= put' <= NO
      /\ (forall x, M x <> None -> M' x <> None)
      /\ (forall x : word,
            ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) -> ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
            ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) -> ~ (cv_P0 v <= bv_unsigned x < cv_P0 v + put') ->
            ~ (WN <> 0 /\ cv_WB v <= bv_unsigned x < cv_WB v + WN) ->
            M' x = M x)
      /\ (~ RR (zr_rc zf) ->
          exists cf, zf = zret_of_icall cf (zr_rc zf) /\ ic_next_out cf = put'
                     /\ CMEM v sf cf M' /\ LXS sf /\ - 1 <= ic_msg cf <= 27 /\ CCUR cf).
  Proof.
    intros s zc M ans ENI ENO ETOT EWN HUI ZC HXS Hmsg HFA HFF HM G2 G10 G11 Hask. cbv zeta.
    pose proof HUI as (UR0 & SI0 & BS0 & CK0). pose proof UR0 as (SR0 & (Bb & Bh) & WS0).
    pose proof SR0 as SRx. unfold SRNGq in SRx. destruct SRx as (Smode & _).
    destruct HXS as (Lw & Lwb & Llv & Lfl & Lhd & Lbk).
    assert (Hmode : HEAD <= is_mode s <= MEM).
    { unfold live_mode in Llv. unfold HEAD, MEM, SYNC, FLAGS, HCRC in *. clear - Smode Llv. lia. }
    assert (Hchk : inflateStateCheck s = false).
    { unfold inflateStateCheck. unfold HEAD, MEM, SYNC in *. apply Bool.orb_false_intro; apply Z.ltb_ge; clear - Hmode; lia. }
    rewrite (inflate_p_W1M ivar_ref ans s zc (cv_flush v) Hchk) in Hask |- *.
    set (c := icall_of_zcall zc) in *.
    assert (Ec : ic_avail_in c = NI /\ ic_avail_out c = NO /\ ic_next_in c = 0 /\ ic_next_out c = 0 /\ ic_input c = arr_of_list (zc_input zc)
                 /\ ic_msg c = zs_msg (zc_strm zc)).
    { subst c. unfold icall_of_zcall. cbn. rewrite ENI, ENO. unfold zlength. repeat split; reflexivity. }
    destruct Ec as (Eai & Eao & Eni & Eno & Einp & Emsg).
    pose proof (s_entryM_fields s) as (Eh & Eb & Ew & Ewb & Ewbits & Ews).
    assert (HX1 : LX v (W1M s c)).
    { unfold LX, W1M. cbn [w_s w_c w_r ir_in ir_ret ir_out ir_left].
      assert (Em : is_mode (s_entryM s) = (if is_mode s =? TYPE then TYPEDO else is_mode s)) by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; reflexivity).
      assert (Ef : is_flags (s_entryM s) = is_flags s /\ is_wrap (s_entryM s) = is_wrap s /\ is_havedict (s_entryM s) = is_havedict s)
        by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; repeat split; reflexivity).
      destruct Ef as (Ef & Ewr & Ehd). rewrite Ewr, Ewbits, Em, Ef, Ehd, Emsg.
      split; [exact Lw|]. split; [exact Lwb|]. split.
      { destruct (Z.eqb_spec (is_mode s) TYPE); [unfold live_mode, TYPEDO, FLAGS, HCRC, SYNC; lia | exact Llv]. }
      split.
      { destruct Lfl as [F0 | (F1 & FM)]; [left; exact F0 | right]. split; [exact F1|]. split; [| reflexivity].
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|NT]; [exfalso; rewrite ET in FM; unfold TYPE, HEAD, BAD in FM; lia | exact FM]. }
      split; [exact Eai|]. split; [unfold Z_OK; lia|]. split; [exact Hmsg|]. split; [exact Lhd|].
      assert (Ebk : is_back (s_entryM s) = is_back s) by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; reflexivity).
      rewrite Ebk. destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|NT]; [unfold bk_ok, TYPEDO, LENEXT, DIST; split; intros; exfalso; lia | exact Lbk]. }
    pose proof (ui_entry s zc HUI ZC) as PI. rewrite <- ENI, <- ENO, <- ETOT, <- EWN in PI. change (icall_of_zcall zc) with c in PI.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    pose proof (inf_loop_exit ivar_ref (cv_flush v) NI NO WN TOT0 ltac:(lia) ltac:(lia) _ PI) as X.
    pose proof (inf_loop_rc ivar_ref (cv_flush v) NI NO WN TOT0 ltac:(lia) ltac:(lia) _ PI ltac:(left; reflexivity)) as RC.
    pose proof (fun w' => LVCK _ w' PI) as CKL.
    pose proof (call_loop s c M HM Hmode Bb ltac:(clear - Bb Bh; pose proof (Z.pow_lt_mono_r 2 (is_bits s) 64); lia) Eai Eao Eni Eno HFA HFF G2 G10 G11 HX1 PI) as L.
    cbv zeta in X, RC. destruct (inf_loop ivar_ref (cv_flush v) (W1M s c)) as [stop [s' c' r']] eqn:EQL.
    cbn [fst snd w_s w_c w_r] in X, RC, L |- *.
    destruct L as (R2 & M2 & Hms2 & HLP & Hg2 & HE2).
    destruct X as (LR & SI & BI & CK & EQ).
    pose proof LR as LR'. apply LRNGq_iff in LR'. destruct LR' as (SR & CIv & RIv & WI & CR).
    pose proof RIv as RIx. open_rinv RIx.
    destruct stop as [|rc].
    -
      destruct HLP as (HM2 & HX2 & SB2 & HRL2).
      pose proof HX2 as HX2'. open_lx HX2'.
      pose proof SR as SRy. unfold SRNGq in SRy.
      destruct SRy as (Smode' & Slast' & Swrap' & Shd' & Sflags' & Sdmax' & Scheck' & Stotal' & Swbits' & Swsize' & _).
      assert (Hmode' : HEAD <= is_mode s' <= MEM).
      { unfold live_mode in Xlive. unfold HEAD, MEM, SYNC, FLAGS, HCRC in *. clear - Smode' Xlive. lia. }
      unfold WINV in WI. destruct WI as (WL & WP & WNiff & Wsz).
      pose proof (ic_WB _ C) as CWB.
      assert (Hws : is_wsize s' = 0 \/ is_wsize s' = 32768) by (clear - Wsz CWB; lia).
      assert (Hput : 0 <= ir_put r' <= NO) by (clear - Rpt0 Rpl Rlf0; lia).
      pose proof (cR_fields c' r') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
      pose proof (sR_fields s' r') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
      assert (Hfl : is_flags s' = 0 \/ ir_out r' = ir_left r').
      { destruct Xflags as [F0 | (F1 & FM & FO)]; [left; exact F0 | right; exact FO]. }
      assert (Hcan : noupd s' r' = false -> adler_canon (is_check s')).
      { intros Hnu. unfold noupd in Hnu. apply Bool.orb_false_iff in Hnu. destruct Hnu as [Ho Hw1]. apply Z.eqb_neq in Ho.
        assert (Ho' : ir_out r' <> ir_left r') by (clear - Ho; lia).
        apply ck_adl_canon. apply (CKL (mkW s' c' r') eq_refl); cbn [w_s w_r].
        - exact Ho'.
        - destruct Xwrap as [X5 | X1]; [rewrite X5; cbv; discriminate | rewrite X1 in Hw1; discriminate Hw1].
        - destruct Xflags as [F0 | (F1 & FM & FO)]; [exact F0 | exfalso; exact (Ho' FO)]. }
      assert (Bin : 0 <= NI - ir_have r' < 2 ^ 32) by (clear - Rnx0 Rhv0 Rnh CI0; lia).
      assert (Bout : 0 <= ir_out r' - ir_left r' < 2 ^ 32) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
      assert (Hout : 0 <= ir_out r' - ir_left r' <= ir_put r' /\ ir_out r' - ir_left r' < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
      destruct (lv_tail s' c' r' R2 M2 HM2 HRL2 RIv CIv Xin Xwrap Hfl Hmode' Rbits Slast' Stotal' Scheck' Xret Hws Hcan)
        as (R3 & M3 & Hms3 & HM3 & A2 & A3 & A4 & A27 & A24 & A8 & A9 & A18 & QT & QF & Hg3 & HE3).
      unfold inf_leave_p in Hask |- *. rewrite RESTORE_eq in Hask |- *. cbn [w_s w_c w_r] in Hask |- *.
      rewrite (needv_leave_need v (sR s' r') (cR c' r') r' Q4) in Hask |- *.
      assert (EN0 : needv v (sR s' r') r' = needv v s' r') by (unfold needv; rewrite Y3, Y11; reflexivity).
      rewrite EN0 in Hask |- *.
      pose proof (sL_fields (sR s' r') (cR c' r') r') as (Fb & Fl & Fm & Fw & Fwb & Ff & Fhd & Fwin & Fblk & Fws).
      pose proof (sL_fields2 (sR s' r') (cR c' r') r') as (Fwh & Fwn & Flens & Fwork & Fcodes & Fhold).
      pose proof (cL_fields (sR s' r') (cR c' r') r') as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
      set (sX := sL (sR s' r') (cR c' r') r') in *. set (cX := cL (sR s' r') (cR c' r') r') in *.
      destruct (needv v s' r') eqn:EN.
      +
        rewrite Y15 in Hask |- *.
        destruct (is_window_blk s') as [wb|] eqn:EWB; [| exfalso; discriminate Hask].
        cbn [fst snd].
        assert (HWN : WN <> 0) by (intros E; pose proof (proj1 WNiff E) as X; rewrite ?EWB in X; discriminate X).
        assert (HWN2 : WN = 32768) by (clear - CWB HWN; lia).
        destruct (QT eq_refl) as (T10 & T11 & T12 & T1 & T19 & T26).
        pose proof (ic_nofast _ C) as Cnofast.
        destruct (uw_enter6 v C sX cX r' R3 M3 (cv_P0 v + ir_put r') (ir_out r' - ir_left r') HM3 Hput HWN
                    T10 T11 T12 T1 ltac:(unfold INF_FRAME; exact A2)
                    ltac:(clear - CP0 Hput; lia) ltac:(clear - Hout; lia))
          as (R4 & M4 & Hms4 & JUW4 & Hfr4 & HM4 & AG4 & Hg4).
        assert (HX3 : LX v (mkW sX cX r')).
        { unfold LX. cbn [w_s w_c w_r]. rewrite Fm, Fw, Fwb, Ff, Fhd, K3, Y3, Y5, Y6, Y7, Y8, Q10. subst sX. rewrite sL_back, sR_back. exact HX2. }
        pose proof (srng_win s' SR) as (Wsz2 & Wwh & Wwn & Wle & Weq).
        pose proof CIv as CIx. unfold CINV in CIx. destruct CIx as (_ & Col' & _ & _ & _ & _ & _ & _ & _ & Coutb & _).
        destruct (uw_all6 v C MEMCPY sX cX r' R4 M4 (cv_P0 v + ir_put r') (ir_out r' - ir_left r') _ _ _ _ _ _ HWN2 HM4 HX3 Hput
                    ltac:(rewrite Fwin, Y14, WL; exact HWN2) ltac:(rewrite Fws, Y11; exact Hws)
                    ltac:(rewrite Fwn, Fws, Y13, Y11; clear - Wwn Wle; split; [lia | intros E; apply (Wle E)])
                    ltac:(rewrite Fwh, Fws, Y12, Y11; clear - Wwh Wle; split; [lia | intros E; apply (Wle E)])
                    ltac:(rewrite Fws, Fwh, Fwn, Y11, Y12, Y13; exact Weq) ltac:(clear - Hout; lia) ltac:(clear - Hout; lia)
                    ltac:(rewrite K7, Q6; exact Coutb) eq_refl JUW4)
          as (R5 & M5 & Hms5 & HM5 & B10 & B8 & B9 & B18 & B19 & B20 & B21 & B2 & Hfr5 & UWFR5).
        rewrite K7, Q6 in HM5.
        set (s5 := uwc sX (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r')) in *.
        destruct (lv_R0 v C R5 M5 (lm_fr _ _ _ HM5) ltac:(unfold INF_FRAME in B2; exact B2) B10)
          as (R6 & Hms6 & C11 & C12 & Hfr6).
        destruct (lv_ret v C _ _ r' R6 M5 HM5 RIv Xret ltac:(rewrite (Hfr6 (2%bv : reg) eq_refl); unfold INF_FRAME in B2; exact B2) C11
                    ltac:(rewrite (Hfr6 (23%bv : reg) eq_refl), (Hfr5 (23%bv : reg) eq_refl), (Hfr4 (23%bv : reg) eq_refl); exact A24)
                    ltac:(rewrite (Hfr6 (27%bv : reg) eq_refl), (Hfr5 (27%bv : reg) eq_refl), (Hfr4 (27%bv : reg) eq_refl); exact T26))
          as (R7 & Hms7 & D10 & D2 & Hfr7).
        destruct (epi_run v C R7 M5 (retv v (cv_flush v) r') (lm_fr _ _ _ HM5) ltac:(unfold INF_FRAME; exact D2) D10) as (R' & Hms8 & A10 & A2' & Asv & A3' & A4').
        rewrite Q6, Q3, Q4 in |- *. rewrite (wrap32_id (ir_out r' - ir_left r')) by (clear - Bout; lia).
        rewrite (uw_core_eq (sR s' r') (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r') ltac:(rewrite Y6; exact Xwbits) ltac:(rewrite Y11; exact Hws)
                   ltac:(rewrite Y13, Y11; clear - Wwn Wle; split; [lia | intros E; apply (Wle E)])
                   ltac:(rewrite Y12, Y11; clear - Wwh Wle; split; [lia | intros E; apply (Wle E)])
                   ltac:(clear - Hout; lia)).
        pose proof (uwc_fields (sR s' r') (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r')) as U. cbv zeta in U.
        destruct U as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
        rewrite (leave_tail_eq (cv_flush v) (uwc (sR s' r') (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r')) (cR c' r') r' Q1 Q4 Q3 Xin
                   ltac:(rewrite U5, Y5; exact Xwrap) ltac:(rewrite U7, Y7; exact Hfl) Bin Bout).
        destruct (sL_uwc (sR s' r') (cR c' r') r' (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r')) as [EsU EcU].
        rewrite EsU, EcU. fold sX cX. fold s5.
        cbn [fst snd zret_of_icall zr_rc].
        exists R', M5, (ir_put r').
        split.
        { eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4|].
          eapply msteps_trans; [exact Hms5|]. eapply msteps_trans; [exact Hms6|]. eapply msteps_trans; [exact Hms7 | exact Hms8]. }
        split; [exact A10|]. split; [exact A2'|]. split; [exact Asv|].
        split; [rewrite A3', (Hfr7 (3%bv : reg) eq_refl), (Hfr6 (3%bv : reg) eq_refl), (Hfr5 (3%bv : reg) eq_refl), (Hfr4 (3%bv : reg) eq_refl); exact A3|].
        split; [rewrite A4', (Hfr7 (4%bv : reg) eq_refl), (Hfr6 (4%bv : reg) eq_refl), (Hfr5 (4%bv : reg) eq_refl), (Hfr4 (4%bv : reg) eq_refl); exact A4|].
        split; [exact Hput|].
        destruct UWFR5 as [Ug5 UE5].
        split; [intros x Hx; apply Ug5, Hg4, Hg3, Hg2; exact Hx|].
        split.
        { intros x N1 N2 N3 N4 N5.
          pose proof (ic_S _ C) as CS. pose proof (ic_ZP _ C) as CZP. pose proof (ic_sp _ C) as Csp. pose proof (u64_range x).
          unfold INF_FRAME, INF_SCRATCH in *.
          rewrite (UE5 x); [| clear - N1; lia | exact N2 | clear - N5 HWN; intros X; apply N5; split; [exact HWN | exact X]].
          rewrite (AG4 x); [| unfold SCR, INF_FRAME, INF_SCRATCH; intros [Hin|Hin]; [cbn in Hin; clear - N1 Hin; lia | exact Hin]].
          rewrite (HE3 x N1 N2 N3). apply HE2; assumption. }
        intros _. exists cX.
        split; [reflexivity|]. split; [subst cX; rewrite K1; exact Q3|].
        split; [apply (CMEM_of_LMEM' _ _ r' _ HM5); subst cX; rewrite K1, Q3; reflexivity|].
        pose proof (uwc_fields sX (ic_outbuf c') (ir_put r') (ir_out r' - ir_left r')) as W. cbv zeta in W. fold s5 in W.
        destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
        split; [| split; [subst cX; rewrite K3, Q10; exact Xmsg | subst cX; apply CCUR_cLR; [exact CIv | exact RIv]]].
        unfold LXS. rewrite W3, W5, W6, W7, W8. subst sX. rewrite Fm, Fw, Fwb, Ff, Fhd, Y3, Y5, Y6, Y7, Y8.
        split; [exact Xwrap|]. split; [exact Xwbits|]. split; [exact Xlive|].
        split; [destruct Xflags as [F0 | (F1 & FM & FO)]; [left; exact F0 | right; split; [exact F1 | exact FM]]|].
        split; [exact Xhd|]. try subst s5. rewrite ?uwc_back, ?sL_back, ?sR_back. exact Xbk.
      +
        cbn [fst snd].
        destruct (epi_run v C R3 M3 (retv v (cv_flush v) r') (lm_fr _ _ _ HM3) ltac:(unfold INF_FRAME; exact A2) (QF eq_refl)) as (R' & Hms4 & A10 & A2' & Asv & A3' & A4').
        rewrite (leave_tail_eq (cv_flush v) (sR s' r') (cR c' r') r' Q1 Q4 Q3 Xin ltac:(rewrite Y5; exact Xwrap) ltac:(rewrite Y7; exact Hfl) Bin Bout).
        fold sX cX. cbn [fst snd zret_of_icall zr_rc].
        exists R', M3, (ir_put r').
        split; [eapply msteps_trans; [exact Hms2 | eapply msteps_trans; [exact Hms3 | exact Hms4]]|].
        split; [exact A10|]. split; [exact A2'|]. split; [exact Asv|].
        split; [rewrite A3'; exact A3|]. split; [rewrite A4'; exact A4|].
        split; [exact Hput|].
        split; [intros x Hx; apply Hg3, Hg2; exact Hx|].
        split.
        { intros x N1 N2 N3 N4 N5. rewrite (HE3 x N1 N2 N3). apply HE2; assumption. }
        intros _. exists cX.
        split; [reflexivity|]. split; [subst cX; rewrite K1; exact Q3|].
        split; [apply (CMEM_of_LMEM' _ _ r' _ HM3); subst cX; rewrite K1, Q3; reflexivity|].
        split; [| split; [subst cX; rewrite K3, Q10; exact Xmsg | subst cX; apply CCUR_cLR; [exact CIv | exact RIv]]].
        unfold LXS. subst sX. rewrite Fw, Fwb, Fm, Ff, Fhd, Y3, Y5, Y6, Y7, Y8.
        split; [exact Xwrap|]. split; [exact Xwbits|]. split; [exact Xlive|].
        split; [destruct Xflags as [F0 | (F1 & FM & FO)]; [left; exact F0 | right; split; [exact F1 | exact FM]]|].
        split; [exact Xhd|]. try subst s5. rewrite ?uwc_back, ?sL_back, ?sR_back. exact Xbk.
    -
      destruct HLP as (HM2 & HX2 & SB2 & (HRR & Hrc & Hrcr)). destruct HRR as (P2 & P20 & P3 & P4). unfold INF_FRAME in P2.
      cbn [fst snd].
      destruct (epi_run v C R2 M2 rc (lm_fr _ _ _ HM2) ltac:(unfold INF_FRAME; exact P2) P20) as (R' & Hms3 & A10 & A2 & Asv & A3 & A4).
      exists R', M2, (ir_put r').
      split; [eapply msteps_trans; [exact Hms2 | exact Hms3]|].
      split; [exact A10|]. split; [exact A2|]. split; [exact Asv|]. split; [rewrite A3; exact P3|]. split; [rewrite A4; exact P4|].
      split; [clear - Rpt0 Rpl Rlf0; lia|].
      split; [exact Hg2|].
      split; [intros x N1 N2 N3 N4 N5; apply HE2; assumption|].
      intros NRR. exfalso. exact (NRR RC).
  Qed.


  Definition WST (s' : inflate_state) (c' : icall) (r' : iregs) (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
    let spi := cv_sp v - INF_FRAME in
    (* zlib 1.4: x8 / x9 / x18 / x19 are updatewindow's registers (its code is unchanged); inflate's have and ret are
       s7 / s11 (rotated), and inflate's S, now in s0, is in updatewindow's s0 save slot (spi - 16), not a register.
       The save slots are by register number: s0 S, s1 P0 + put, s2 ZP, s3 bits, s4 out - left, s5 preserved *)
    getr R' 13 = zw (cv_fa v) /\ getr R' 10 = zw (cv_opq v) /\ getr R' 11 = zw 32768 /\ getr R' 12 = zw 1
    /\ getr R' 2 = zw (spi - 64) /\ getr R' 8 = zw (cv_P0 v + ir_put r') /\ getr R' 9 = zw (ir_out r' - ir_left r')
    /\ getr R' 18 = zw 1 /\ getr R' 19 = zw (cv_S v) /\ getr R' 23 = zw (ir_have r') /\ getr R' 27 = zw (ir_ret r')
    /\ getr R' 3 = getr (cv_R0 v) 3 /\ getr R' 4 = getr (cv_R0 v) 4
    /\ LMEM v (mkW (sL (sR s' r') (cR c' r') r') (cL (sR s' r') (cR c' r') r') r') M'
    /\ cell s6u_segs M' (spi - 8) 8 pc6_uw_ret
    /\ cell s6u_segs M' (spi - 16) 8 (cv_S v)
    /\ cell s6u_segs M' (spi - 24) 8 (cv_P0 v + ir_put r') /\ cell s6u_segs M' (spi - 32) 8 (cv_ZP v)
    /\ cell s6u_segs M' (spi - 40) 8 (ir_bits r')
    /\ cell s6u_segs M' (spi - 48) 8 (ir_out r' - ir_left r') /\ cell s6u_segs M' (spi - 56) 8 (bv_unsigned (getr R' 21)).

  Theorem inflate_callW6 : forall s zc M (ans : option (blk * (Z -> Z))),
    NI = zlength (zc_input zc) -> NO = zc_avail_out zc -> TOT0 = zs_total_out (zc_strm zc) -> WN = arr_len (is_window s) ->
    UI s -> zcall_ok zc -> LXS s -> - 1 <= zs_msg (zc_strm zc) <= 27 -> 0 < cv_fa v -> 0 < cv_ff v ->
    CMEM v s (icall_of_zcall zc) M ->
    getr (cv_R0 v) 2 = zw (cv_sp v) -> getr (cv_R0 v) 10 = zw (cv_ZP v) -> getr (cv_R0 v) 11 = zw (cv_flush v) ->
    snd (inflate_p ivar_ref ans s zc (cv_flush v)) <> None ->
    exists R' M' s' c' r',
      inf_loop ivar_ref (cv_flush v) (W1M s (icall_of_zcall zc)) = (SLeave, mkW s' c' r')
      /\ leave_need (cv_flush v) (sR s' r') (cR c' r') r' = true /\ is_window_blk s' = None /\ WN = 0
      /\ pinv NI NO WN TOT0 (W1M s (icall_of_zcall zc)) /\ LX v (mkW s' c' r')
      /\ (SRNGq s' /\ RINV NI NO r' /\ CINV NI NO c' /\ is_wsize s' = 0)
      /\ msteps s6u_segs (mkst (cv_R0 v) (Z_to_bv 64 pc6_inflate) M s6u_rom) (mkst R' (Z_to_bv 64 pc6_tzw) M' s6u_rom)
      /\ WST s' c' r' R' M'
      /\ (forall x, M x <> None -> M' x <> None)
      /\ (forall x : word,
            ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) -> ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
            ~ (cv_ZP v <= bv_unsigned x < cv_ZP v + 112) -> ~ (cv_P0 v <= bv_unsigned x < cv_P0 v + ir_put r') ->
            M' x = M x).
  Proof.
    intros s zc M ans ENI ENO ETOT EWN HUI ZC HXS Hmsg HFA HFF HM G2 G10 G11 Hask.
    pose proof HUI as (UR0 & SI0 & BS0 & CK0). pose proof UR0 as (SR0 & (Bb & Bh) & WS0).
    pose proof SR0 as SRx. unfold SRNGq in SRx. destruct SRx as (Smode & _).
    destruct HXS as (Lw & Lwb & Llv & Lfl & Lhd & Lbk).
    assert (Hmode : HEAD <= is_mode s <= MEM).
    { unfold live_mode in Llv. unfold HEAD, MEM, SYNC, FLAGS, HCRC in *. clear - Smode Llv. lia. }
    assert (Hchk : inflateStateCheck s = false).
    { unfold inflateStateCheck. unfold HEAD, MEM, SYNC in *. apply Bool.orb_false_intro; apply Z.ltb_ge; clear - Hmode; lia. }
    rewrite (inflate_p_W1M ivar_ref ans s zc (cv_flush v) Hchk) in Hask.
    set (c := icall_of_zcall zc) in *.
    assert (Ec : ic_avail_in c = NI /\ ic_avail_out c = NO /\ ic_next_in c = 0 /\ ic_next_out c = 0 /\ ic_input c = arr_of_list (zc_input zc)
                 /\ ic_msg c = zs_msg (zc_strm zc)).
    { subst c. unfold icall_of_zcall. cbn. rewrite ENI, ENO. unfold zlength. repeat split; reflexivity. }
    destruct Ec as (Eai & Eao & Eni & Eno & Einp & Emsg).
    pose proof (s_entryM_fields s) as (Eh & Eb & Ew & Ewb & Ewbits & Ews).
    assert (HX1 : LX v (W1M s c)).
    { unfold LX, W1M. cbn [w_s w_c w_r ir_in ir_ret ir_out ir_left].
      assert (Em : is_mode (s_entryM s) = (if is_mode s =? TYPE then TYPEDO else is_mode s)) by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; reflexivity).
      assert (Ef : is_flags (s_entryM s) = is_flags s /\ is_wrap (s_entryM s) = is_wrap s /\ is_havedict (s_entryM s) = is_havedict s)
        by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; repeat split; reflexivity).
      destruct Ef as (Ef & Ewr & Ehd). rewrite Ewr, Ewbits, Em, Ef, Ehd, Emsg.
      split; [exact Lw|]. split; [exact Lwb|]. split.
      { destruct (Z.eqb_spec (is_mode s) TYPE); [unfold live_mode, TYPEDO, FLAGS, HCRC, SYNC; lia | exact Llv]. }
      split.
      { destruct Lfl as [F0 | (F1 & FM)]; [left; exact F0 | right]. split; [exact F1|]. split; [| reflexivity].
        destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|NT]; [exfalso; rewrite ET in FM; unfold TYPE, HEAD, BAD in FM; lia | exact FM]. }
      split; [exact Eai|]. split; [unfold Z_OK; lia|]. split; [exact Hmsg|]. split; [exact Lhd|].
      assert (Ebk : is_back (s_entryM s) = is_back s) by (unfold s_entryM; destruct (is_mode s =? TYPE); [destruct s|]; reflexivity).
      rewrite Ebk. destruct (Z.eqb_spec (is_mode s) TYPE) as [ET|NT]; [unfold bk_ok, TYPEDO, LENEXT, DIST; split; intros; exfalso; lia | exact Lbk]. }
    pose proof (ui_entry s zc HUI ZC) as PI. rewrite <- ENI, <- ENO, <- ETOT, <- EWN in PI. change (icall_of_zcall zc) with c in PI.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0.
    pose proof (inf_loop_exit ivar_ref (cv_flush v) NI NO WN TOT0 ltac:(lia) ltac:(lia) _ PI) as X.
    pose proof (call_loop s c M HM Hmode Bb ltac:(clear - Bb Bh; pose proof (Z.pow_lt_mono_r 2 (is_bits s) 64); lia) Eai Eao Eni Eno HFA HFF G2 G10 G11 HX1 PI) as L.
    cbv zeta in X. destruct (inf_loop ivar_ref (cv_flush v) (W1M s c)) as [stop [s' c' r']] eqn:EQL.
    cbn [fst snd w_s w_c w_r] in X, L, Hask |- *.
    destruct L as (R2 & M2 & Hms2 & HLP & Hg2 & HE2).
    destruct X as (LR & SI & BI & CK & EQ).
    pose proof LR as LR'. apply LRNGq_iff in LR'. destruct LR' as (SR & CIv & RIv & WI & CR).
    pose proof RIv as RIx. open_rinv RIx.
    destruct stop as [|rc]; [| exfalso; apply Hask; reflexivity].
    destruct HLP as (HM2 & HX2 & SB2 & HRL2).
    pose proof HX2 as HX2'. open_lx HX2'.
    pose proof SR as SRy. unfold SRNGq in SRy.
    destruct SRy as (Smode' & Slast' & Swrap' & Shd' & Sflags' & Sdmax' & Scheck' & Stotal' & Swbits' & Swsize' & _).
    assert (Hmode' : HEAD <= is_mode s' <= MEM).
    { unfold live_mode in Xlive. unfold HEAD, MEM, SYNC, FLAGS, HCRC in *. clear - Smode' Xlive. lia. }
    unfold WINV in WI. destruct WI as (WL & WP & WNiff & Wsz).
    pose proof (ic_WB _ C) as CWB.
    assert (Hws : is_wsize s' = 0 \/ is_wsize s' = 32768) by (clear - Wsz CWB; lia).
    assert (Hput : 0 <= ir_put r' <= NO) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (cR_fields c' r') as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    pose proof (sR_fields s' r') as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
    assert (Hfl : is_flags s' = 0 \/ ir_out r' = ir_left r').
    { destruct Xflags as [F0 | (F1 & FM & FO)]; [left; exact F0 | right; exact FO]. }
    pose proof (inf_loop_rc ivar_ref (cv_flush v) NI NO WN TOT0 ltac:(lia) ltac:(lia) _ PI ltac:(left; reflexivity)) as RC0.
    pose proof (fun w' => LVCK _ w' PI) as CKL.
    assert (Hcan : noupd s' r' = false -> adler_canon (is_check s')).
    { intros Hnu. unfold noupd in Hnu. apply Bool.orb_false_iff in Hnu. destruct Hnu as [Ho Hw1]. apply Z.eqb_neq in Ho.
      assert (Ho' : ir_out r' <> ir_left r') by (clear - Ho; lia).
      apply ck_adl_canon. rewrite EQL in CKL. apply (CKL (mkW s' c' r') eq_refl); cbn [w_s w_r].
      - exact Ho'.
      - destruct Xwrap as [X5 | X1]; [rewrite X5; cbv; discriminate | rewrite X1 in Hw1; discriminate Hw1].
      - destruct Xflags as [F0 | (F1 & FM & FO)]; [exact F0 | exfalso; exact (Ho' FO)]. }
    unfold inf_leave_p in Hask. rewrite RESTORE_eq in Hask. cbn [w_s w_c w_r] in Hask.
    rewrite (needv_leave_need v (sR s' r') (cR c' r') r' Q4) in Hask.
    assert (EN0 : needv v (sR s' r') r' = needv v s' r') by (unfold needv; rewrite Y3, Y11; reflexivity).
    rewrite EN0 in Hask.
    destruct (needv v s' r') eqn:EN; [| exfalso; apply Hask; reflexivity].
    rewrite Y15 in Hask.
    destruct (is_window_blk s') as [wb|] eqn:EWB; [exfalso; apply Hask; reflexivity|].
    assert (HWN : WN = 0) by (apply (proj2 WNiff); reflexivity).
    assert (Hout : 0 <= ir_out r' - ir_left r' <= ir_put r' /\ ir_out r' - ir_left r' < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    destruct (lv_tail s' c' r' R2 M2 HM2 HRL2 RIv CIv Xin Xwrap Hfl Hmode' Rbits Slast' Stotal' Scheck' Xret Hws Hcan)
      as (R3 & M3 & Hms3 & HM3 & A2 & A3 & A4 & A27 & A24 & A8 & A9 & A18 & QT & QF & Hg3 & HE3).
    rewrite EN in Hms3, QT. destruct (QT eq_refl) as (T10 & T11 & T12 & T1 & T19 & T26).
    pose proof (sL_fields (sR s' r') (cR c' r') r') as (Fb & Fl & Fm & Fw & Fwb & Ff & Fhd & Fwin & Fblk & Fws).
    pose proof (cL_fields (sR s' r') (cR c' r') r') as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    set (sX := sL (sR s' r') (cR c' r') r') in *. set (cX := cL (sR s' r') (cR c' r') r') in *.
    assert (HX3 : LX v (mkW sX cX r')).
    { unfold LX. cbn [w_s w_c w_r]. rewrite Fm, Fw, Fwb, Ff, Fhd, K3, Y3, Y5, Y6, Y7, Y8, Q10. subst sX. rewrite sL_back, sR_back. exact HX2. }
    destruct (uw_stop6 v C sX cX r' R3 M3 pc6_uw_ret (cv_P0 v + ir_put r') (ir_out r' - ir_left r')
                HWN HM3 HX3 Hput T10 T11 T12 T1 ltac:(unfold INF_FRAME; exact A2)
                ltac:(clear - CP0 Hput; lia) ltac:(clear - Hout; lia) ltac:(unfold pc6_uw_ret; lia))
      as (R4 & M4 & Hms4 & A13 & A10 & A11 & A12 & UR4 & A18u & Hfr4 & UF4 & HM4 & AG4 & Hg4).
    exists R4, M4, s', c', r'.
    split; [reflexivity|].
    split; [unfold leave_need; rewrite Q4; unfold needv in EN; rewrite Y3, Y11;
            replace (ir_out r' =? ir_left r') with (ir_out r' - ir_left r' =? 0) by (destruct (Z.eqb_spec (ir_out r') (ir_left r')); destruct (Z.eqb_spec (ir_out r' - ir_left r') 0); try reflexivity; lia);
            exact EN|].
    split; [exact EWB|]. split; [exact HWN|]. split; [exact PI|]. split; [exact HX2|].
    split; [split; [exact SR | split; [exact RIv | split; [exact CIv | clear - Wsz HWN; lia]]]|].
    split; [eapply msteps_trans; [exact Hms2 | eapply msteps_trans; [exact Hms3 | exact Hms4]]|].
    split.
    { unfold WST. cbv zeta. destruct UR4 as (U8 & U9 & U19 & U2). destruct UF4 as (F8c & F16 & F24 & F32 & F40 & F48 & F56). unfold INF_FRAME in *.
      pose proof (ic_ZP _ C) as CZP. pose proof (ic_S _ C) as CSs.
      split; [exact A13|]. split; [exact A10|]. split; [exact A11|]. split; [exact A12|].
      split; [exact U2|]. split; [exact U8|]. split; [exact U9|]. split; [exact A18u|]. split; [exact U19|].
      split; [rewrite (Hfr4 (23%bv : reg) eq_refl); exact A24|].
      split; [rewrite (Hfr4 (27%bv : reg) eq_refl); exact T26|].
      split; [rewrite (Hfr4 (3%bv : reg) eq_refl); exact A3|].
      split; [rewrite (Hfr4 (4%bv : reg) eq_refl); exact A4|].
      split; [exact HM4|]. split; [exact F8c|].
      split; [rewrite A27, u_zw, Z.mod_small in F16 by (clear - CSs; lia); exact F16|].
      split; [rewrite A9, u_zw, Z.mod_small in F24 by (clear - Rlf0 Rpl Rpt0 CP0; lia); exact F24|].
      split; [rewrite A8, u_zw, Z.mod_small in F32 by (clear - CZP; lia); exact F32|].
      split; [rewrite A18, u_zw, Z.mod_small in F40 by (clear - Rbits; lia); exact F40|].
      split; [rewrite T19, u_zw, Z.mod_small in F48 by (clear - Hout; lia); exact F48 | rewrite <- (Hfr4 (21%bv : reg) eq_refl) in F56; exact F56]. }
    split; [intros x Hx; apply Hg4, Hg3, Hg2; exact Hx|].
    intros x N1 N2 N3 N4.
    pose proof (ic_sp _ C) as Csp. pose proof (u64_range x). unfold INF_FRAME, INF_SCRATCH in *.
    rewrite (AG4 x); [| unfold SCR, INF_FRAME, INF_SCRATCH; intros [Hin|Hin]; [cbn in Hin; clear - N1 Hin; lia | exact Hin]].
    rewrite (HE3 x N1 N2 N3). apply HE2; assumption.
  Qed.

  Theorem inflate_resume6 : forall sx cx rx sF R M pend copy f21,
    cv_WN v = 32768 ->
    SRNGq sx -> RINV NI NO rx -> CINV NI NO cx -> LX v (mkW sx cx rx) -> is_wsize sx = 0 ->
    (forall f, In f [is_mode; is_last; is_wrap; is_havedict; is_flags; is_total; is_check; is_wbits; is_wsize; is_whave; is_wnext; is_bits; is_hold; is_back] ->
               f sF = f (sL (sR sx rx) (cR cx rx) rx)) ->
    arr_len (is_window sF) = 32768 ->
    LMEM v (mkW sF (cL (sR sx rx) (cR cx rx) rx) rx) M ->
    pend = cv_P0 v + ir_put rx -> copy = ir_out rx - ir_left rx ->
    (* zlib 1.4: updatewindow's save slots s0..s5 hold inflate's S, P0 + put, ZP, bits, out - left and a preserved s5 *)
    JUW v R M pend copy (cv_S v) (cv_P0 v + ir_put rx) (cv_ZP v) (ir_bits rx) (ir_out rx - ir_left rx) f21 ->
    getr R 23 = zw (ir_have rx) -> getr R 27 = zw (ir_ret rx) ->
    getr R 3 = getr (cv_R0 v) 3 -> getr R 4 = getr (cv_R0 v) 4 ->
    let s5 := uwc sF (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx) in
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R' (getr (cv_R0 v) 1) M' s6u_rom)
      /\ getr R' 10 = zw (retv v (cv_flush v) rx) /\ getr R' 2 = zw (cv_sp v)
      /\ (forall rg : reg, In rg [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R' rg = getr (cv_R0 v) rg)
      /\ getr R' 3 = getr (cv_R0 v) 3 /\ getr R' 4 = getr (cv_R0 v) 4
      /\ (forall x, M x <> None -> M' x <> None)
      /\ (forall x : word,
            ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v) -> ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
            ~ (cv_WB v <= bv_unsigned x < cv_WB v + WN) ->
            M' x = M x)
      /\ CMEM v s5 (cL (sR sx rx) (cR cx rx) rx) M' /\ LXS s5
      /\ - 1 <= ic_msg (cL (sR sx rx) (cR cx rx) rx) <= 27 /\ ic_next_out (cL (sR sx rx) (cR cx rx) rx) = ir_put rx
      /\ CCUR (cL (sR sx rx) (cR cx rx) rx).
  Proof.
    intros sx cx rx sF R M pend copy f21 HWN2 SR RIv CIv HX2 Hws0 Ef Hwl HM4 Epend Ecopy JUW4 P24 P26 P3 P4.
    cbv zeta.
    pose proof (Ef is_mode ltac:(cbn; tauto)) as Fm. pose proof (Ef is_last ltac:(cbn; tauto)) as Fl. pose proof (Ef is_wrap ltac:(cbn; tauto)) as Fw.
    pose proof (Ef is_havedict ltac:(cbn; tauto)) as Fhd. pose proof (Ef is_flags ltac:(cbn; tauto)) as Ff. pose proof (Ef is_total ltac:(cbn; tauto)) as Ft.
    pose proof (Ef is_check ltac:(cbn; tauto)) as Fck. pose proof (Ef is_wbits ltac:(cbn; tauto)) as Fwb. pose proof (Ef is_wsize ltac:(cbn; tauto)) as Fws.
    pose proof (Ef is_whave ltac:(cbn; tauto)) as Fwh. pose proof (Ef is_wnext ltac:(cbn; tauto)) as Fwn. pose proof (Ef is_bits ltac:(cbn; tauto)) as Fb.
    pose proof (Ef is_hold ltac:(cbn; tauto)) as Fho. pose proof (Ef is_back ltac:(cbn; tauto)) as Fbk. clear Ef.
    cbn beta in Fm, Fl, Fw, Fhd, Ff, Ft, Fck, Fwb, Fws, Fwh, Fwn, Fb, Fho, Fbk.
    pose proof (sL_fields (sR sx rx) (cR cx rx) rx) as (Gb & Gl & Gm & Gw & Gwb & Gf & Ghd & Gwin & Gblk & Gws).
    pose proof (sL_fields2 (sR sx rx) (cR cx rx) rx) as (Gwh & Gwn & Glens & Gwork & Gcodes & Ghold).
    pose proof (cL_fields (sR sx rx) (cR cx rx) rx) as (K1 & K2 & K3 & K4 & K5 & K6 & K7).
    pose proof HX2 as HX2'. open_lx HX2'.
    pose proof SR as SRy. unfold SRNGq in SRy.
    destruct SRy as (Smode' & Slast' & Swrap' & Shd' & Sflags' & Sdmax' & Scheck' & Stotal' & Swbits' & Swsize' & _).
    assert (Hmode' : HEAD <= is_mode sx <= MEM).
    { unfold live_mode in Xlive. unfold HEAD, MEM, SYNC, FLAGS, HCRC in *. clear - Smode' Xlive. lia. }
    pose proof RIv as RIx. open_rinv RIx.
    pose proof (ic_I0 _ C) as CI0. pose proof (ic_P0 _ C) as CP0. pose proof (ic_nofast _ C) as Cnofast.
    assert (Hput : 0 <= ir_put rx <= NO) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (cR_fields cx rx) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
    pose proof (sR_fields sx rx) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15).
    assert (Hout : 0 <= ir_out rx - ir_left rx <= ir_put rx /\ ir_out rx - ir_left rx < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    set (cX := cL (sR sx rx) (cR cx rx) rx) in *.
    assert (HX3 : LX v (mkW sF cX rx)).
    { unfold LX. cbn [w_s w_c w_r]. rewrite Fm, Fw, Fwb, Ff, Fhd, Fbk, Gm, Gw, Gwb, Gf, Ghd, Y3, Y5, Y6, Y7, Y8, sL_back, sR_back. subst cX. rewrite K3, Q10. exact HX2. }
    pose proof (srng_win sx SR) as (Wsz2 & Wwh & Wwn & Wle & Weq).
    pose proof CIv as CIx. unfold CINV in CIx. destruct CIx as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Coutb & _).
    subst pend copy.
    destruct (uw_all6 v C MEMCPY sF cX rx R M (cv_P0 v + ir_put rx) (ir_out rx - ir_left rx) _ _ _ _ _ _ HWN2 HM4 HX3 Hput
                Hwl ltac:(rewrite Fws, Gws, Y11, Hws0; left; reflexivity)
                ltac:(rewrite Fwn, Fws, Gwn, Gws, Y13, Y11; clear - Wwn Wle; split; [lia | intros E; apply (Wle E)])
                ltac:(rewrite Fwh, Fws, Gwh, Gws, Y12, Y11; clear - Wwh Wle; split; [lia | intros E; apply (Wle E)])
                ltac:(rewrite Fws, Fwh, Fwn, Gws, Gwh, Gwn, Y11, Y12, Y13; exact Weq) ltac:(clear - Hout; lia) ltac:(clear - Hout; lia)
                ltac:(subst cX; rewrite K7, Q6; exact Coutb) eq_refl JUW4)
      as (R5 & M5 & Hms5 & HM5 & B10 & B8 & B9 & B18 & B19 & B20 & B21 & B2 & Hfr5 & UWFR5).
    replace (ic_outbuf cX) with (ic_outbuf cx) in HM5 by (subst cX; rewrite K7, Q6; reflexivity).
    set (s5 := uwc sF (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) in *.
    destruct (lv_R0 v C R5 M5 (lm_fr _ _ _ HM5) ltac:(unfold INF_FRAME in B2; exact B2) B10)
      as (R6 & Hms6 & C11 & C12 & Hfr6).
    destruct (lv_ret v C _ _ rx R6 M5 HM5 RIv Xret ltac:(rewrite (Hfr6 (2%bv : reg) eq_refl); unfold INF_FRAME in B2; exact B2) C11
                ltac:(rewrite (Hfr6 (23%bv : reg) eq_refl), (Hfr5 (23%bv : reg) eq_refl); exact P24)
                ltac:(rewrite (Hfr6 (27%bv : reg) eq_refl), (Hfr5 (27%bv : reg) eq_refl); exact P26))
      as (R7 & Hms7 & D10 & D2 & Hfr7).
    destruct (epi_run v C R7 M5 (retv v (cv_flush v) rx) (lm_fr _ _ _ HM5) ltac:(unfold INF_FRAME; exact D2) D10) as (R' & Hms8 & A10 & A2' & Asv & A3' & A4').
    exists R', M5.
    split; [eapply msteps_trans; [exact Hms5 | eapply msteps_trans; [exact Hms6 | eapply msteps_trans; [exact Hms7 | exact Hms8]]]|].
    split; [exact A10|]. split; [exact A2'|]. split; [exact Asv|].
    split; [rewrite A3', (Hfr7 (3%bv : reg) eq_refl), (Hfr6 (3%bv : reg) eq_refl), (Hfr5 (3%bv : reg) eq_refl); exact P3|].
    split; [rewrite A4', (Hfr7 (4%bv : reg) eq_refl), (Hfr6 (4%bv : reg) eq_refl), (Hfr5 (4%bv : reg) eq_refl); exact P4|].
    destruct UWFR5 as [Ug5 UE5].
    split; [exact Ug5|].
    split.
    { intros x N1 N2 N5. pose proof (ic_sp _ C) as Csp. pose proof (u64_range x). unfold INF_FRAME, INF_SCRATCH in *.
      apply (UE5 x); [clear - N1; lia | exact N2 | exact N5]. }
    split; [apply (CMEM_of_LMEM' _ _ rx _ HM5); subst cX; rewrite K1, Q3; reflexivity|].
    pose proof (uwc_fields sF (ic_outbuf cx) (ir_put rx) (ir_out rx - ir_left rx)) as W. cbv zeta in W. fold s5 in W.
    destruct W as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10 & W11).
    split.
    { unfold LXS. rewrite W3, W5, W6, W7, W8, Fm, Fw, Fwb, Ff, Fhd, Gm, Gw, Gwb, Gf, Ghd, Y3, Y5, Y6, Y7, Y8.
      split; [exact Xwrap|]. split; [exact Xwbits|]. split; [exact Xlive|].
      split; [destruct Xflags as [F0 | (F1 & FM & FO)]; [left; exact F0 | right; split; [exact F1 | exact FM]]|].
      split; [exact Xhd|]. try subst s5. rewrite ?uwc_back, ?Fbk, ?sL_back, ?sR_back. exact Xbk. }
    pose proof (CCUR_cLR sx cx rx CIv RIv) as HCC. subst cX. rewrite K3, K1, Q10, Q3. split; [exact Xmsg | split; [reflexivity | exact HCC]].
  Qed.

End Call.
End FXG.
