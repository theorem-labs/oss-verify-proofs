(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_aensure F_apopulate AMalloc_iface AEmbRep AFrameD AEmbFrame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.
Notation POPULATE_STACK_X := 1344 (only parsing).

Lemma munch_focus : forall (W : list ivl) (m m' : amem) A n, munch W m m' -> 0 <= A ->
  (forall x, A <= x < A + n -> outside W x) -> munch [(0, A); (A + n, 2 ^ 64)]%Z m m'.
Proof.
  intros W m m' A n MU A0 O x Hx. apply MU. apply O. cbn [outside] in Hx. pose proof (bv_unsigned_in_range _ x) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma cells_frame_focus : forall (W : list ivl) (m m' : amem) A cs, rw_cells asegs m A cs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells asegs m' A cs.
Proof.
  intros W m m' A cs RC MU O. pose proof (rw_cells_bound asegs _ _ _ RC) as [B0 B1].
  eapply AFrameD.cells_frameD; [exact RC| exact (munch_focus W m m' A _ MU B0 O)|]. cbn [disjoint_from]. lia.
Qed.

Lemma emb_cells_top : forall st m d cap sz, emb_cells st m -> a_emb st = (d, cap, sz) -> cap = 0 \/ (0 < cap /\ AIMG_HI <= d /\ d + cap <= ATOP).
Proof.
  intros st m d cap sz EC EA. unfold emb_cells in EC. rewrite EA in EC. destruct EC as [_ EC].
  destruct (cap =? 0) eqn:C0; [left; apply Z.eqb_eq; exact C0| right]. apply Z.eqb_neq in C0.
  destruct EC as (_ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2. split; [lia|]. split; assumption.
Qed.

Definition populate_ret_false (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ ((exh_mem c st = true /\ st2 = st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c st)))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells asegs m' (RI + 68) [C1 (Z_to_bv 8 1)]
  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - POPULATE_STACK_X, bv_unsigned sp); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2
        /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma pop_exh_spec : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax s1x a0x a1x a3x a4x a5x s2x s3x s4x s5x s6x : word)
    (F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st : astate) (c lo : Z),
  let RI := aregion_info L c in
  exh_first_stmt -> aresv_ok L RESV ->
  stk asegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK_X ->
  bv_unsigned sp < 2 ^ 63 ->
  mem_inv asegs m1 -> tp = Z_to_bv 64 ATP -> arelro m1 -> bv_unsigned fc < 32 ->
  rw_cells asegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m1 (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  exh_cells m1 -> emb_cells st m1 -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  AIMG_HI <= RI -> RI + 128 <= ATOP -> pcov RESV RI (RI + 128) ->
  (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) ->
  1 <= c < K_NUM_CLASSES ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> emb_rng st RNG ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_false L RESV RNG sp st c lo m1 st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (exh_report ATOP RESV c st (fun st' => k st' false))) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x (Z_to_bv 64 c) a3x a4x a5x a6 a7
                 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42200) fc None m1 (seg_rom asegs)).
Proof.
  intros until lo. cbv zeta.
  intros EXHW ROK ST CEIL LO SP63 MI TP RELRO FC FR FLG XC EC CAPB RILO RIHI RIRES RIOLD HC RIMG RSTK RRI ERNG KF.
  word_range sp SPR. pose proof atop_range as ATR.
  pose proof (rw_cells_bound asegs _ _ _ FLG) as [RIB0 RIB1]. cbn [cells_size csize Nat.add] in RIB1.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64) : word) = bv_unsigned sp + -64) by (apply unsigned_lit; clear -SPR LO CEIL ATR; lia).
  unfold exh_report. destruct (exh_mem c st) eqn:EM.
  -
    iprefix.
    lstep.
    step. if_lit.
    step. step.
    step.
    do 10 step.
    lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -64) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    apply evtF_done. eapply KF.
    unfold populate_ret_false. cbv zeta. destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE.
    split; [apply fp_le_refl|]. split; [left; split; [exact EM| reflexivity]|].
    split; [exact EC|]. split; [exact ERNG|]. split; [exact XC|]. split; [exact FLG|].
    split. { exists d0, cap0. split; [apply munch_refl|]. split; [left; split; reflexivity|]. split; [left; split; reflexivity|].
             destruct (emb_cells_top st m1 d0 cap0 sz0 EC EE) as [Z0|(_ & _ & X)]; [left; exact Z0| right; exact X]. }
    split; [exact MI| assumption].
  -
    iprefix.
    lstep.
    step. if_lit.
    apply evtF_done.
    eapply (EXHW RNG R RESV (fun st' => k st' false) Q) with (lo := lo) (L := L) (c := c) (st := st); rewrite ?SPU; try eassumption.
    + unfold EXH_STACK. clear -LO. lia.
    + clear -SP63. lia.
    + eapply rng_sub'; [exact RSTK|]. clear -LO. lia.
    + intros st2 RNG' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
      unfold exh_first_ret in ER. cbv zeta in ER. destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
      destruct ER as (FPLE & (e2 & EST2) & EC2 & ERNG2 & XC2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI2 & ST2).
      rewrite SPU in MU2, ST2.
      assert (FR2 : rw_cells asegs m' (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
      { eapply cells_frame_focus; [exact FR| exact MU2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros x Hx. cbn [outside].
        assert (B0 : cap0 = 0 \/ d0 + cap0 <= ATOP) by (destruct (emb_cells_top st m1 d0 cap0 sz0 EC EE) as [Z0|(_ & _ & T0)]; [left| right]; assumption).
        assert (B2 : cap2 = 0 \/ d2 + cap2 <= ATOP) by (destruct (emb_cells_top st2 m' d2 cap2 sz2 EC2 EE2) as [Z2|(_ & _ & T2)]; [left| right]; assumption).
        unfold EXH_STACK, AEMB; repeat split; try exact I; clear -Hx LO CEIL RIHI ATR B0 B2 TOP1; lia. }
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. clear FR.
      iprefix.
      step. step.
      step.
      do 10 step.
      lazymatch goal with FRM : rw_cells asegs ?mm (bv_unsigned sp + -64) _, STK : stk asegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
      apply evtF_done. eapply KF.
      unfold populate_ret_false. cbv zeta. rewrite EE, EE2.
      split; [exact FPLE|]. split; [right; split; [exact EM| exists e2; exact EST2]|].
      split; [exact EC2|]. split; [exact ERNG2|]. split; [exact XC2|]. split; [exact FLG2|].
      split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
               eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; unfold EXH_STACK; clear; intros x Hx; lia. }
      split; [exact MI2| assumption].
Qed.

Lemma populate_spec_x : forall RNG {R} (RESV : list (Z * Z))
    (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK_X ->
  mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 RI -> a4 = Z_to_bv 64 req ->
  m3_cells L m ->
  rw_cells asegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  u64arr asegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells asegs m (al_t L + 2792) [C8 stm] ->
  rw_cells asegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0 <= req < 2^31 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_false L RESV RNG sp st c lo m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_g (exh_clear c) L RNG sp st c req lo sj m st2 RNG' m' ->
      implS asegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (populate_free_array_g (exh_report ATOP RESV c) (exh_clear c) st c req k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 populate_entry) fc None m (seg_rom asegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP EA0 EA1 EA2 EA3 EA4 MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KT.
  pose proof atop_range as ATR. word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RIB : AIMG_HI <= aregion_info L c /\ aregion_info L c + 128 <= ATOP).
  { rewrite RIE. unfold AIMG_HI, K_SPACE_SIZE, K_SPACE_EXTRA, K_NUM_CLASSES in *. change (2^37) with 137438953472 in *. clear -SP1 SP2 HC. lia. }
  destruct RIB as [RILO RIHI].
  eapply (populate_spec_g RNG (exh_report ATOP RESV c) (exh_clear c) k Q) with (lo := lo) (sj := sj) (stm := stm) (fj := fj)
         (flg := Z_to_bv 8 (if exh_mem c st then 1 else 0)); try eassumption.
  - clear -LO. lia.
  -
    intros m1 a1e a3e a4e a5e a6e s2e s3e s4e s5e MU1 WM1 MI1 ST1 FR1.
    assert (WHI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 512, bv_unsigned sp)]%Z).
    { constructor; [| constructor]. cbn [fst]. unfold AIMG_HI. clear -LO CEIL ATR. lia. }
    eapply pop_exh_spec with (lo := lo) (L := L) (st := st) (c := c) (RESV := RESV); try eassumption.
    + exact (arelro_frameD m m1 _ RELRO MU1 WHI).
    + eapply AFrameD.cells_frameD; [exact EXH| exact MU1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear -LO CEIL RIHI. lia.
    + exact (exh_cells_frameD m m1 _ XC MU1 WHI).
    + apply (emb_cells_frameD st m m1 _ EC MU1).
      * cbn [disjoint_from]. unfold AEMB. clear -LO CEIL ATR. lia.
      * destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (emb_cells_top st m d0 cap0 sz0 EC EE) as [Z0|(_ & _ & TB0)]; [left; exact Z0| right].
        cbn [disjoint_from]. clear -LO CEIL TB0. lia.
    + intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PRF. eapply KF.
      unfold populate_ret_false in *. cbv zeta in *. destruct (a_emb st) as [[d0 cap0] sz0]. destruct (a_emb st2) as [[d2 cap2] sz2].
      destruct PRF as (P1 & P2 & P3 & P4 & P5 & P6 & (d1 & cap1 & MU2 & V1 & V2 & TP1) & P8 & P9).
      repeat (split; [assumption|]). split; [| split; assumption].
      exists d1, cap1. split; [| split; [exact V1| split; [exact V2| exact TP1]]].
      eapply munch_trans; [eapply munch_weaken; [| exact MU1]| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia.
Qed.

End CANSECX.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AKit.TwinB AKit2.TwinB ARep.TwinB ARepKit.TwinB ARepFrame.TwinB ARefill_iface.TwinB RT_stubs.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import F_aensure.TwinB F_apopulate.TwinB AMalloc_iface.TwinB AEmbRep.TwinB AFrameD.TwinB AEmbFrame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSECX. Context {rc : runConstT} {ov : annOV}.
Notation POPULATE_STACK_X := 1344 (only parsing).

Lemma munch_focus : forall (W : list ivl) (m m' : amem) A n, munch W m m' -> 0 <= A ->
  (forall x, A <= x < A + n -> outside W x) -> munch [(0, A); (A + n, 2 ^ 64)]%Z m m'.
Proof.
  intros W m m' A n MU A0 O x Hx. apply MU. apply O. cbn [outside] in Hx. pose proof (bv_unsigned_in_range _ x) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.
Lemma cells_frame_focus : forall (W : list ivl) (m m' : amem) A cs, rw_cells bsegs m A cs -> munch W m m' ->
  (forall x, A <= x < A + Z.of_nat (cells_size cs) -> outside W x) -> rw_cells bsegs m' A cs.
Proof.
  intros W m m' A cs RC MU O. pose proof (rw_cells_bound bsegs _ _ _ RC) as [B0 B1].
  eapply AFrameD.TwinB.cells_frameD; [exact RC| exact (munch_focus W m m' A _ MU B0 O)|]. cbn [disjoint_from]. lia.
Qed.

Lemma emb_cells_top : forall st m d cap sz, emb_cells st m -> a_emb st = (d, cap, sz) -> cap = 0 \/ (0 < cap /\ AIMG_HI <= d /\ d + cap <= ATOP).
Proof.
  intros st m d cap sz EC EA. unfold emb_cells in EC. rewrite EA in EC. destruct EC as [_ EC].
  destruct (cap =? 0) eqn:C0; [left; apply Z.eqb_eq; exact C0| right]. apply Z.eqb_neq in C0.
  destruct EC as (_ & _ & _ & P2 & _ & _ & P5 & P6 & _). unfold EMB_INIT in P2. split; [lia|]. split; assumption.
Qed.

Definition populate_ret_false (L : alayout) (RESV : list (Z * Z)) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let RI := aregion_info L c in
  let '(d0, cap0, _) := a_emb st in let '(d2, cap2, _) := a_emb st2 in
  fp_le RNG RNG'
  /\ ((exh_mem c st = true /\ st2 = st) \/ (exh_mem c st = false /\ exists e2, st2 = set_emb e2 (exh_set c st)))
  /\ emb_cells st2 m' /\ emb_rng st2 RNG' /\ exh_cells m'
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 1)]
  /\ (exists d1 cap1,
        munch [(bv_unsigned sp - POPULATE_STACK_X, bv_unsigned sp); (RI + 68, RI + 69); (AEMB, AEMB + 56);
               (d0, d0 + cap0); (d1, d1 + cap1); (d2, d2 + cap2)]%Z m m'
        /\ emb_prov RESV st d0 cap0 d1 cap1 /\ emb_prov RESV st d0 cap0 d2 cap2
        /\ (cap1 = 0 \/ d1 + cap1 <= ATOP))
  /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp).

Lemma pop_exh_spec : forall RNG {R} (RESV : list (Z * Z)) (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a6 a7 s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (rax s1x a0x a1x a3x a4x a5x s2x s3x s4x s5x s6x : word)
    (F : bvmap 5 word) fc (m1 : amem) (L : alayout) (st : astate) (c lo : Z),
  let RI := aregion_info L c in
  exh_first_stmt -> aresv_ok L RESV ->
  stk bsegs m1 lo (bv_unsigned sp + -64) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK_X ->
  bv_unsigned sp < 2 ^ 63 ->
  mem_inv bsegs m1 -> tp = Z_to_bv 64 ATP -> arelro m1 -> bv_unsigned fc < 32 ->
  rw_cells bsegs m1 (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m1 (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  exh_cells m1 -> emb_cells st m1 -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  AIMG_HI <= RI -> RI + 128 <= ATOP -> pcov RESV RI (RI + 128) ->
  (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) ->
  1 <= c < K_NUM_CLASSES ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG RI 128 -> emb_rng st RNG ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_false L RESV RNG sp st c lo m1 st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (exh_report ATOP RESV c st (fun st' => k st' false))) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 RI) s1x a0x a1x (Z_to_bv 64 c) a3x a4x a5x a6 a7
                 s2x s3x s4x s5x s6x s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42b90) fc None m1 (seg_rom bsegs)).
Proof.
  intros until lo. cbv zeta.
  intros EXHW ROK ST CEIL LO SP63 MI TP RELRO FC FR FLG XC EC CAPB RILO RIHI RIRES RIOLD HC RIMG RSTK RRI ERNG KF.
  word_range sp SPR. pose proof atop_range as ATR.
  pose proof (rw_cells_bound bsegs _ _ _ FLG) as [RIB0 RIB1]. cbn [cells_size csize Nat.add] in RIB1.
  assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64) : word) = bv_unsigned sp + -64) by (apply unsigned_lit; clear -SPR LO CEIL ATR; lia).
  unfold exh_report. destruct (exh_mem c st) eqn:EM.
  -
    iprefix.
    lstep.
    step. if_lit.
    step. step.
    step.
    do 10 step.
    lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -64) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
    apply evtF_done. eapply KF.
    unfold populate_ret_false. cbv zeta. destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE.
    split; [apply fp_le_refl|]. split; [left; split; [exact EM| reflexivity]|].
    split; [exact EC|]. split; [exact ERNG|]. split; [exact XC|]. split; [exact FLG|].
    split. { exists d0, cap0. split; [apply munch_refl|]. split; [left; split; reflexivity|]. split; [left; split; reflexivity|].
             destruct (emb_cells_top st m1 d0 cap0 sz0 EC EE) as [Z0|(_ & _ & X)]; [left; exact Z0| right; exact X]. }
    split; [exact MI| assumption].
  -
    iprefix.
    lstep.
    step. if_lit.
    apply evtF_done.
    eapply (EXHW RNG R RESV (fun st' => k st' false) Q) with (lo := lo) (L := L) (c := c) (st := st); rewrite ?SPU; try eassumption.
    + unfold EXH_STACK. clear -LO. lia.
    + clear -SP63. lia.
    + eapply rng_sub'; [exact RSTK|]. clear -LO. lia.
    + intros st2 RNG' m' ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ER.
      unfold exh_first_ret in ER. cbv zeta in ER. destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (a_emb st2) as [[d2 cap2] sz2] eqn:EE2.
      destruct ER as (FPLE & (e2 & EST2) & EC2 & ERNG2 & XC2 & FLG2 & (d1 & cap1 & MU2 & PV1 & PV2 & TOP1) & MI2 & ST2).
      rewrite SPU in MU2, ST2.
      assert (FR2 : rw_cells bsegs m' (bv_unsigned sp + -64) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]).
      { eapply cells_frame_focus; [exact FR| exact MU2|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. intros x Hx. cbn [outside].
        assert (B0 : cap0 = 0 \/ d0 + cap0 <= ATOP) by (destruct (emb_cells_top st m1 d0 cap0 sz0 EC EE) as [Z0|(_ & _ & T0)]; [left| right]; assumption).
        assert (B2 : cap2 = 0 \/ d2 + cap2 <= ATOP) by (destruct (emb_cells_top st2 m' d2 cap2 sz2 EC2 EE2) as [Z2|(_ & _ & T2)]; [left| right]; assumption).
        unfold EXH_STACK, AEMB; repeat split; try exact I; clear -Hx LO CEIL RIHI ATR B0 B2 TOP1; lia. }
      apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. clear FR.
      iprefix.
      step. step.
      step.
      do 10 step.
      lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -64) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
      apply evtF_done. eapply KF.
      unfold populate_ret_false. cbv zeta. rewrite EE, EE2.
      split; [exact FPLE|]. split; [right; split; [exact EM| exists e2; exact EST2]|].
      split; [exact EC2|]. split; [exact ERNG2|]. split; [exact XC2|]. split; [exact FLG2|].
      split. { exists d1, cap1. split; [| split; [exact PV1| split; [exact PV2| exact TOP1]]].
               eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; unfold EXH_STACK; clear; intros x Hx; lia. }
      split; [exact MI2| assumption].
Qed.

Lemma populate_spec_x : forall RNG {R} (RESV : list (Z * Z))
    (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c req lo : Z) (sj : list word) (stm : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - POPULATE_STACK_X ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (al_t L + 2768) -> a2 = Z_to_bv 64 c -> a3 = Z_to_bv 64 RI -> a4 = Z_to_bv 64 req ->
  m3_cells L m ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 (if exh_mem c st then 1 else 0))] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->

  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0 <= req < 2^31 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->

  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG (FA + 4 * nf) (mfa - 4 * nf) ->
  AIMG_HI <= al_ctx L ->
  iclr (al_t L) 4096 ->

  exh_first_stmt -> aresv_ok L RESV -> bv_unsigned sp < 2 ^ 63 -> arelro m -> bv_unsigned fc < 32 ->
  exh_cells m -> emb_cells st m -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  pcov RESV RI (RI + 128) -> (let '(d0, cap0, _) := a_emb st in cap0 = 0 \/ RI + 128 <= d0 \/ d0 + cap0 <= RI) -> emb_rng st RNG ->

  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_false L RESV RNG sp st c lo m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 false)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      populate_ret_g (exh_clear c) L RNG sp st c req lo sj m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k st2 true)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (populate_free_array_g (exh_report ATOP RESV c) (exh_clear c) st c req k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 populate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP EA0 EA1 EA2 EA3 EA4 MC REG EXH STATS LSJ STM FJ AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM REQ
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFJ CXI TIC
         EXHW ROK SP63 RELRO FC XC EC CAPB RIRES RIOLD ERNG KF KT.
  pose proof atop_range as ATR. word_range sp SPR.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (RIB : AIMG_HI <= aregion_info L c /\ aregion_info L c + 128 <= ATOP).
  { rewrite RIE. unfold AIMG_HI, K_SPACE_SIZE, K_SPACE_EXTRA, K_NUM_CLASSES in *. change (2^37) with 137438953472 in *. clear -SP1 SP2 HC. lia. }
  destruct RIB as [RILO RIHI].
  eapply (populate_spec_g RNG (exh_report ATOP RESV c) (exh_clear c) k Q) with (lo := lo) (sj := sj) (stm := stm) (fj := fj)
         (flg := Z_to_bv 8 (if exh_mem c st then 1 else 0)); try eassumption.
  - clear -LO. lia.
  -
    intros m1 a1e a3e a4e a5e a6e s2e s3e s4e s5e MU1 WM1 MI1 ST1 FR1.
    assert (WHI : Forall (fun iv : Z * Z => AIMG_HI <= fst iv) [(bv_unsigned sp - 512, bv_unsigned sp)]%Z).
    { constructor; [| constructor]. cbn [fst]. unfold AIMG_HI. clear -LO CEIL ATR. lia. }
    eapply pop_exh_spec with (lo := lo) (L := L) (st := st) (c := c) (RESV := RESV); try eassumption.
    + exact (arelro_frameD m m1 _ RELRO MU1 WHI).
    + eapply AFrameD.TwinB.cells_frameD; [exact EXH| exact MU1|]. cbn [disjoint_from cells_size csize Nat.add Z.of_nat Pos.of_succ_nat]. clear -LO CEIL RIHI. lia.
    + exact (exh_cells_frameD m m1 _ XC MU1 WHI).
    + apply (emb_cells_frameD st m m1 _ EC MU1).
      * cbn [disjoint_from]. unfold AEMB. clear -LO CEIL ATR. lia.
      * destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE. destruct (emb_cells_top st m d0 cap0 sz0 EC EE) as [Z0|(_ & _ & TB0)]; [left; exact Z0| right].
        cbn [disjoint_from]. clear -LO CEIL TB0. lia.
    + intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PRF. eapply KF.
      unfold populate_ret_false in *. cbv zeta in *. destruct (a_emb st) as [[d0 cap0] sz0]. destruct (a_emb st2) as [[d2 cap2] sz2].
      destruct PRF as (P1 & P2 & P3 & P4 & P5 & P6 & (d1 & cap1 & MU2 & V1 & V2 & TP1) & P8 & P9).
      repeat (split; [assumption|]). split; [| split; assumption].
      exists d1, cap1. split; [| split; [exact V1| split; [exact V2| exact TP1]]].
      eapply munch_trans; [eapply munch_weaken; [| exact MU1]| exact MU2]. unfold sub_fp; cbn [outside]; clear; intros x Hx; lia.
Qed.

End CANSECX.
End TwinB.
