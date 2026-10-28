(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep ApFrame W_item_d2i_imgA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA EncKitA Fr_i2o_SCT W_sct_completeA W_i2o_sigA W_i2o_sctA W_asn1_flagsA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Definition I2O_SCT_W_STACK_A : Z := IOS_FRAME + I2O_SIG_STACK_A.

(* [comment removed for export] *)
Lemma cell_bytes_readA : forall (m : mem) A k pre c post i n,
  rw_cells ctasegs m A (pre ++ c :: post) -> Z.of_nat (cells_size pre) = k -> 0 <= i -> (Z.to_nat i + n <= length (cbytes c))%nat ->
  ov_read_bytes ctasegs m (wa (A + k + i)) n = Some (firstn n (skipn (Z.to_nat i) (cbytes c))).
Proof.
  intros m A k pre c post i n H Hk Hi Hn.
  pose proof (rw_cells_skip m A pre (c :: post) k H Hk) as R1. change (c :: post) with ([c] ++ post) in R1.
  assert (R : rw_cells ctasegs m (A + k) [c]) by exact (rw_cells_app_l m (A + k) [c] post R1).
  pose proof (rw_cells_bytes_at _ _ _ _ R) as B. cbn [cells_bytes] in B. rewrite app_nil_r in B.
  apply (bytes_at_read _ _ _ _ i n B Hi Hn).
Qed.
Ltac ts_read HX k idx i n RD :=
  lazymatch type of HX with rw_cells _ ?mm ?A ?cs =>
    let pre := eval cbv [firstn] in (firstn idx cs) in
    let c := eval cbv [nth] in (nth idx cs (C8 (Z_to_bv 64 0))) in
    let post := eval cbv [skipn] in (skipn (S idx) cs) in
    pose proof (cell_bytes_readA mm A k pre c post i n HX eq_refl ltac:(lia) ltac:(cbn; lia)) as RD;
    cbn [cbytes firstn skipn le8 Z_to_le_bytes Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD
  end.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma ios_open_p : forall Σ1 OW LB m f q,
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB m -> (forall b, In b LB -> off_fr f 0 b) -> @fr_geo (push AR f 0) f 0 ->
  rw_cells ctasegs m (shad f) ios_shadow_pro -> ~ In q (map blk_id (OW ++ LB)) ->
  @BnHeapA.AHEAP (push AR f 0) Σ1 OW ((q, f + 32, 8) :: LB) m.
Proof.
  intros Σ1 OW LB m f q HEAP FRESH GEO FRS Hq.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 0) Σ1 OW LB m f 0%nat q (f + 32) 8 (or_introl eq_refl) HEAP); [clear; lia| change (fs_size 0) with 64; clear; lia| clear; lia| | exact Hq|].
  - apply (acc_of_shadow_cells m (shad f) ios_shadow_pro 4%nat (f + 32) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
      [rewrite (shad_aligned_add f 32 F8) by (clear; lia); clear; cbn; lia| clear; cbn; lia| reflexivity].
  - intros b Hb. pose proof (FRESH b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 0) with 64 in O.
    cbn [blk_addr blk_size fst snd]. clear - O. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma i2o_sct_write_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo STK : Z)
    (adr : bptr -> Z) (sc : sctr bptr) (PP P : Z) (jo : list byte) (bPP bP : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + STK <= bv_unsigned sp -> I2O_SCT_W_STACK_A <= STK ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FRM < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  sct_repA m LB adr sc -> sct_complete sc = true ->
  In bPP (OW ++ LB) -> blk_addr bPP <= PP -> PP + 8 <= blk_addr bPP + blk_size bPP -> PP mod 8 = 0 -> rw_cells ctasegs m PP [C8 (wz P)] ->
  In bP (OW ++ LB) -> blk_addr bP <= P -> P + i2o_sct_len sc <= blk_addr bP + blk_size bP -> rw_cells ctasegs m P [CB (Z.to_nat (i2o_sct_len sc)) jo] ->
  (forall b, In b (sct_blocks adr sc) -> blk_addr b + blk_size b <= P \/ P + i2o_sct_len sc <= blk_addr b) ->
  (forall b, In b (sct_blocks adr sc) -> blk_addr b + blk_size b <= PP \/ PP + 8 <= blk_addr b) ->
  (PP + 8 <= P \/ P + i2o_sct_len sc <= PP) ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) -> a1 = Z_to_bv 64 PP ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(PP, PP + 8); (P, P + i2o_sct_len sc)]%Z a) m m' ->
     rw_cells ctasegs m' PP [C8 (wz (P + i2o_sct_len sc))] ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (i2o_sct_len sc)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2O_SCT_A) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until bP. intros HEAP ST CEIL LO STKB TOP AL16 MI TP FLEN CRED REP CPL PPIN PPL PPH PP8 HPP PIN PL PH HO APO APQ SEPQ A0 -> K.
  pose proof STKB as STKu. unfold I2O_SCT_W_STACK_A, I2O_SIG_STACK_A, IOS_FRAME, RT_STACK in STKu.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (sct_ok_of_repA _ _ _ _ _ _ HEAP REP) as OK.
  pose proof REP as (HINL & AL16S & HX & ARL & ARE & ARS & ARB & ND & VR & VN & HR & GR & TS & EXL & OE & OS & OB).
  assert (HIN : In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB)) by (apply in_or_app; right; exact HINL).
  pose proof OK as (_ & _ & _ & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL).
  assert (LENR : 0 <= i2o_sct_len sc <= 3 * 65536).
  { unfold i2o_sct_len, sc_siglen. destruct (sc_version sc =? 0); [| clear - BLR; lia].
    destruct (sc_sig sc) as [[q n]|] eqn:ES; [pose proof (SIGP q n eq_refl) as SB; clear - ELR SB; lia| clear - ELR; lia]. }
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (XB0 & _ & _ & XBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PPIN) as (QB0 & _ & _ & QBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP PIN) as (PB0 & _ & _ & PBC & _). cbn [blk_addr blk_size fst snd] in *. nrm. unfold MallocRep.wz in *.
  fz SEPQ.
  eapply (ios_head_cps Q) with (lo := lo) (STK := STK) (OW := OW) (LB := LB) (adr := adr) (sc := sc) (vs := 0);
    [exact HEAP| exact ST| exact CEIL| exact LO| unfold I2O_SCT_LEN_STACK_A, IOS_FRAME, RT_STACK; clear - STKu; lia| exact TOP| exact AL16| exact MI| exact TP| exact FLEN
    | exact CRED| exact HIN| exact AL16S| exact HX| exact OK| exact A0|].
  intros Σ1 m4 f spa g junk gj x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F1 fc1 j0 j8 j16 j24 j32 j40
         HEAP4 FRESH GEO CR1 EL1 ST4 MI4 AG4 FRL FRH HP FRS HX4 SPA32 SPAL SPAH GSZ SAVJ.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G4, G5.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP4) as (CF1 & CF2 & CF3). nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO STKu SPAL SPAH SPR; lia).
  pose proof (FRESH _ HIN) as OFX. pose proof (FRESH _ PPIN) as OFQ. pose proof (FRESH _ PIN) as OFP.
  unfold off_fr in OFX, OFQ, OFP. change (fs_size 0) with 64 in OFX, OFQ, OFP. cbn [blk_addr blk_size fst snd] in OFX.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG4) in HPP; [| intros xa Hxa; right; right; exists bPP; split; [exact PPIN| cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG4) in HO; [| intros xa Hxa; right; right; exists bP; split; [exact PIN| cbn [cells_size csize] in Hxa; rewrite Nat.add_0_r, Z2Nat.id in Hxa by lia; lia]].
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qp Hqp].
  pose proof (ios_open_p Σ1 OW LB m4 f qp HEAP4 ltac:(intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))) GEO FRS Hqp) as HEAPp.
  set (LB' := (qp, f + 32, 8) :: LB) in HEAPp.
  assert (INC : forall b, In b (OW ++ LB) -> In b (OW ++ LB')) by (intros b Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; exact Hb]).
  assert (QPIN : In (qp, f + 32, 8) (OW ++ LB')) by (apply in_or_app; right; left; reflexivity).
  pose proof (INC _ HIN) as HIN'. pose proof (INC _ PPIN) as PPIN'. pose proof (INC _ PIN) as PIN'.
  ablock HEAPp HIN' ACCX OFFX. ablock HEAPp PPIN' ACCQ OFFQ. ablock HEAPp PIN' ACCP OFFP. unfold SHLO, SHHI in OFFX, OFFQ, OFFP. fz OFFX. fz OFFQ. fz OFFP.
  unfold SCT_SIZE in *.
  assert (AWO : forall W, Forall (fun iv => (spa <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv = (f + 32, f + 40) \/ iv = (PP, PP + 8) \/ (P <= fst iv /\ snd iv <= P + i2o_sct_len sc)) W ->
                Forall (@aclient_write_ok (push AR f 0) (OW ++ LB')) W).
  { intros W HW. induction W as [|[l' h'] W IH]; [constructor|]. apply Forall_cons_iff in HW as [H1 HW]. constructor; [| exact (IH HW)]. cbn [fst snd] in H1.
    destruct H1 as [H1|[H1|[H1|H1]]].
    - left. cbn [fst snd]. clear - H1 CEIL LO STKu SPAL TOP. plia.
    - injection H1 as -> ->. right; right. exists (qp, f + 32, 8). split; [exact QPIN| cbn; clear; lia].
    - injection H1 as -> ->. right; right. exists bPP. split; [exact PPIN'| cbn; clear - PPL PPH; lia].
    - right; right. exists bP. split; [exact PIN'| cbn; clear - H1 PL PH; lia]. }
  fz G5.
  (* [comment removed for export] *)
  assert (XO : adr (sc_blk sc) + 104 <= P \/ P + i2o_sct_len sc <= adr (sc_blk sc)).
  { exact (APO _ ltac:(unfold sct_blocks; repeat (apply in_or_app; right); left; reflexivity)). }
  assert (XQ : adr (sc_blk sc) + 104 <= PP \/ PP + 8 <= adr (sc_blk sc)).
  { exact (APQ _ ltac:(unfold sct_blocks; repeat (apply in_or_app; right); left; reflexivity)). }
  fz XQ.
  (* [comment removed for export] *)
  unfold sct_cells, MallocRep.wz, u32 in HX4.
  rewrite CPL. cbn [bret].
  pose proof (munch_refl [(spa, spa + 48); (f + 32, f + 40); (PP, PP + 8)]%Z m4) as MU. pose proof (wmono_refl ctasegs m4) as WM.
  assert (OFFW : offshW [(spa, spa + 48); (f + 32, f + 40); (PP, PP + 8)]%Z).
  { pose proof OFFQ as X0. thaw X0. thaw G5. cbn [offshW]. unfold SHLO, SHHI. clear - CF1 CF2 CEIL LO STKu SPAL G4 G5 X0 PPL PPH. lia. }
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. bnot. zstep. rewrite sx32_mod32 by (clear - VR; lia). zstep. if_cases KV; zify_cond KV.
  - (* [comment removed for export] *)
    assert (V0 : sc_version sc = 0) by (destruct VR as [E0|VR']; [exfalso; revert KV; rewrite E0; vm_compute; congruence| revert KV; rewrite land64_small by lia; intros KV; lia]).
    pose proof CPL as CPL'. unfold sct_complete in CPL'. rewrite V0 in CPL'. cbn [Z.eqb] in CPL'.
    destruct (sc_logid sc) as [lq|] eqn:EL; [| discriminate].
    assert (SGC : sct_sig_complete sc = true) by (cbn [andb] in CPL'; exact CPL').
    destruct (sc_sig sc) as [[sq sn]|] eqn:ES; [| unfold sct_sig_complete in SGC; rewrite ES in SGC; rewrite andb_false_r in SGC; discriminate].
    pose proof (SIGP sq sn eq_refl) as [SQ0 SN]. set (en := sc_extlen sc) in *.
    assert (SNE : sc_siglen sc = sn) by (unfold sc_siglen; rewrite ES; reflexivity).
    assert (LEN : i2o_sct_len sc = 47 + en + sn) by (unfold i2o_sct_len; rewrite V0; cbn [Z.eqb]; rewrite SNE; clear; lia).
    rewrite LEN in *. rewrite V0 in HX4. cbn [optr W_sct_list_free.osz32 option_map SctRep.logid_len] in HX4. change (0 mod 2 ^ 32) with 0 in HX4.
    (* [comment removed for export] *)
    destruct (arr_bytes _ _ _ _ _ ARL) as (lid & LID & LIDL & LQIN & _).
    destruct (arr_bytes _ _ _ _ _ ARS) as (sig & SIG & SLEN & SQIN & _).
    assert (LQINB : In (lq, adr lq, 32) (sct_blocks adr sc)) by (unfold sct_blocks; rewrite EL; apply in_or_app; left; left; reflexivity).
    assert (SQINB : In (sq, adr sq, sn) (sct_blocks adr sc)) by (unfold sct_blocks; rewrite ES; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
    pose proof (APO _ LQINB) as SEPL. pose proof (APQ _ LQINB) as SEPLQ. pose proof (APO _ SQINB) as SEPS. pose proof (APQ _ SQINB) as SEPSQ.
    cbn [blk_addr blk_size fst snd] in SEPL, SEPLQ, SEPS, SEPSQ. pose proof (LOGP lq eq_refl) as LQ0.
    pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror LQIN))) as (_ & _ & _ & LQC & _).
    pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror SQIN))) as (_ & _ & _ & SQC & _). cbn [blk_addr blk_size fst snd] in LQC, SQC.
    pose proof (FRESH _ (in_or_app _ _ _ (or_intror LQIN))) as OFL. pose proof (FRESH _ (in_or_app _ _ _ (or_intror SQIN))) as OFS.
    unfold off_fr in OFL, OFS. change (fs_size 0) with 64 in OFL, OFS. cbn [blk_addr blk_size fst snd] in OFL, OFS. nrm.
    apply (bytes_at_agree _ m m4 _ _ AG4) in LID; [| intros xa Hxa; rewrite LIDL in Hxa; right; right; exists (lq, adr lq, 32); split; [exact (in_or_app _ _ _ (or_intror LQIN))| cbn; clear - Hxa; lia]].
    apply (bytes_at_agree _ m m4 _ _ AG4) in SIG; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists (sq, adr sq, sn); split; [exact (in_or_app _ _ _ (or_intror SQIN))| cbn; clear - Hxa; lia]].
    assert (LIDF : frozen (bytes_at ctasegs m4 (adr lq) lid)) by exact LID. assert (SIGF : frozen (bytes_at ctasegs m4 (adr sq) sig)) by exact SIG. clear LID SIG.
    fz SEPL. fz SEPLQ. fz SEPS. fz SEPSQ. fz OFL. fz OFS. fz OFX. fz OFQ. fz OFP.
    (* [comment removed for export] *)
    set (KP := fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(P, P + (47 + en + sn))]%Z a).
    assert (KMU : forall mA mB W, munch W mA mB ->
              Forall (fun iv => (spa - 96 <= fst iv /\ snd iv <= bv_unsigned sp) \/ iv = (f + 32, f + 40) \/ (P <= fst iv /\ snd iv <= P + (47 + en + sn))) W ->
              agree_on KP mA mB).
    { intros mA mB W MUx HW. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MUx)|]. intros a [Ha Ho]. cbn [outside fst snd] in Ho.
      thaw G5. clear - HW Ha Ho G3 G4 G5 FRESH CEIL CE1 LO STKu SPAL SPAH HEAP. induction W as [|[l' h'] W IH]; [exact I|].
      apply Forall_cons_iff in HW as [H1 HW]. cbn [outside fst snd]. split; [| exact (IH HW)]. cbn [fst snd] in H1.
      destruct H1 as [H1|[H1|H1]]; [| injection H1 as -> ->| lia].
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3'. unfold BnHeapA.ACEIL, STACK_WIN in B3'. lia.
      - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
        + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
        + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O. destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O. lia. }
    assert (KAG : forall mA mB (L : list block) (X : Z -> Prop), (forall b, In b OW -> In b L) -> agree_on (fun a => aclient_addr (L ++ LB') spa a /\ X a) mA mB ->
              (forall a, KP a -> X a) -> agree_on KP mA mB).
    { intros mA mB L X HL AGx HX0. eapply agree_on_mono; [exact AGx|]. intros a Hk. split; [| exact (HX0 a Hk)]. destruct Hk as [Ha _].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
      apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact (HL b Hb)| right; right; exact Hb]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    rewrite SNE. zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by (clear - ELR SN; lia). zstep. btaken.
    zstep. sfalse.
    (* [comment removed for export] *)
    zstep. zstep. zstep. sfalse. zstep. thaw OFX. thaw OFQ. thaw OFP. thaw G5. zstep. fz OFX. fz OFQ. fz OFP. fz G5. zstep. zstep.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    thaw XQ. thaw SEPQ. thaw OFQ. zstep. fz XQ. fz OFQ. fz SEPQ. zstep. zstep. zstep. btaken.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
    match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
    match goal with H : rw_cells ctasegs m5 PP _ |- _ => rename H into HPP5 end.
    pose proof (agree_on_refl KP m5) as AGK.
    assert (ST5 : stk ctasegs m5 lo spa) by (first [assumption| eapply stk_transport; [exact ST4| exact MU5| exact WM5| cbn; clear; lia]]).
    assert (HEAP5 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m5).
    { eapply (@AH_frame (push AR f 0)); [exact HEAPp| exact MU5| exact WM5|]. apply AWO. constructor; [cbn [fst snd]; left; clear - SPAH; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; left; reflexivity| constructor]]]. }
    assert (AGK45 : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(PP, PP + 8); (P, P + (47 + en + sn))]%Z a) m4 m5).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)|]. intros a [Ha Ho]. cbn [outside fst snd] in Ho |- *. thaw G5.
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha Ho SPAH G3 CEIL LO STKu; repeat split; try exact I; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr Ho CEIL CE1 LO STKu SPAL G4; repeat split; try exact I; lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
        destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3', O. unfold BnHeapA.ACEIL, STACK_WIN in B3'. clear - Hr Ho B3' O CEIL LO STKu SPAL. repeat split; try exact I; lia. }
    fz G5.
    (* [comment removed for export] *)
    destruct (cb_split2A m5 P 1 (46 + en + sn) jo ltac:(replace (1 + (46 + en + sn)) with (47 + en + sn) by (clear; lia); exact HO) ltac:(clear; lia) ltac:(clear - ELR SN; lia)) as [R0 Hr1].
    destruct (cb_split2A m5 (P + 1) 32 (14 + en + sn) _ ltac:(replace (32 + (14 + en + sn)) with (46 + en + sn) by (clear; lia); exact Hr1) ltac:(clear; lia) ltac:(clear - ELR SN; lia)) as [R1 Hr2]. clear Hr1.
    destruct (cb_split2A m5 (P + 1 + 32) 10 (4 + en + sn) _ ltac:(replace (10 + (4 + en + sn)) with (14 + en + sn) by (clear; lia); exact Hr2) ltac:(clear; lia) ltac:(clear - ELR SN; lia)) as [R2 Hr3]. clear Hr2.
    destruct (cb_split2A m5 (P + 1 + 32 + 10) en (4 + sn) _ ltac:(replace (en + (4 + sn)) with (4 + en + sn) by (clear; lia); exact Hr3) ltac:(clear - ELR; lia) ltac:(clear - SN; lia)) as [R3 Hr4]. clear Hr3.
    destruct (cb_split2A m5 (P + 1 + 32 + 10 + en) 4 sn _ Hr4 ltac:(clear; lia) ltac:(clear - SN; lia)) as [R4 R5]. clear Hr4 HO.
    replace (P + 1 + 32) with (P + 33) in R2 by (clear; lia). replace (P + 1 + 32 + 10) with (P + 43) in R3 by (clear; lia).
    replace (P + 1 + 32 + 10 + en) with (P + 43 + en) in R4 by (clear; lia). replace (P + 1 + 32 + 10 + en + 4) with (P + 47 + en) in R5 by (clear; lia).
    change (Z.to_nat 1) with 1%nat in R0. change (Z.to_nat 32) with 32%nat in R1. change (Z.to_nat 10) with 10%nat in R2. change (Z.to_nat 4) with 4%nat in R4.
    fz MU5. clear WM5. try clear MU WM. clear ACCX ACCQ ACCP.
    ablock HEAP5 HIN' ACCX OFFX5. ablock HEAP5 PIN' ACCP OFFP5. clear OFFX5 OFFP5.
    pose proof (munch_refl [(spa + 24, spa + 32); (f + 32, f + 40); (P, P + 1)]%Z m5) as MU. pose proof (wmono_refl ctasegs m5) as WM.
    assert (OFFW5 : offshW [(spa + 24, spa + 32); (f + 32, f + 40); (P, P + 1)]%Z) by (pose proof OFFP as X0; thaw X0; thaw G5; cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO STKu SPAL SPAH G3 G4 G5 X0 PL PH ELR SN; lia).
    (* [comment removed for export] *)
    zstep. thaw OFX. thaw OFQ. thaw OFP. thaw G5. thaw XO. thaw SEPQ. zstep. fz OFX. fz OFQ. fz OFP. fz G5. fz XO. fz SEPQ.
    thaw XO. thaw OFP. thaw SEPQ. zstep. fz OFP. fz SEPQ. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    match goal with H : munch _ m5 m6 |- _ => rename H into MU6 end. match goal with H : wmono ctasegs m5 m6 |- _ => rename H into WM6 end.
    match goal with H : mem_inv ctasegs m6 |- _ => rename H into MI6 end.
    assert (ST6 : stk ctasegs m6 lo spa) by (first [assumption| eapply stk_transport; [exact ST5| exact MU6| exact WM6| cbn; clear; lia]]).
    assert (HEAP6 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m6).
    { eapply (@AH_frame (push AR f 0)); [exact HEAP5| exact MU6| exact WM6|]. apply AWO. constructor; [cbn [fst snd]; left; clear - SPAH; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; right; clear - ELR SN; lia| constructor]]]. }
    pose proof (agree_on_trans _ _ _ _ AGK (KMU m5 m6 _ MU6 ltac:(constructor; [cbn [fst snd]; left; clear - SPAH; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; clear - ELR SN; lia| constructor]]]))) as AGK6. clear AGK.
    assert (LID6 : bytes_at ctasegs m6 (adr lq) lid).
    { pose proof LIDF as X0. thaw X0. thaw SEPL. thaw SEPLQ. pose proof MU5 as MU5'. thaw MU5'.
      apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU5') in X0; [| rewrite LIDL; cbn; thaw OFL; clear - SEPLQ OFL LQC CEIL LO STKu SPAL; lia].
      eapply (bytes_at_agree KP m5 m6 _ _ AGK6 X0). intros xa Hxa. rewrite LIDL in Hxa. subst KP. cbv beta. split.
      - right; right. exists (lq, adr lq, 32). split; [exact (in_or_app _ _ _ (or_intror LQIN))| cbn; clear - Hxa; lia].
      - cbn [outside fst snd]. clear - Hxa SEPL. lia. }
    fz OFL.
    fz SEPL. thaw SEPL.
    apply evt_done. eapply cps_step_same.
    { eapply (@asan_memcpy_cpsA (push AR f 0)) with (d := P + 1) (s := adr lq) (bs := lid) (bd := bP) (bsrc := (lq, adr lq, 32)) (lo := lo) (OW := OW) (LB := LB');
        rewrite ?LIDL, ?ESPA; change (Z.of_nat (Z.to_nat 32)) with 32; try reflexivity.
      - exact HEAP6.
      - exact ST6.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      - unfold RT_STACK. clear - LO STKu SPAL. lia.
      - unfold USTACK_TOP. clear - TOP SPAH. lia.
      - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
      - exact MI6.
      - exact PIN'.
      - clear - PL. lia.
      - clear - PH ELR SN. lia.
      - exact (INC _ (in_or_app _ _ _ (or_intror LQIN))).
      - exact LID6.
      - clear - SEPL ELR SN. lia. }
    fz SEPL.
    intros msM PO. unfold icall_post in PO. rewrite ?ESPA in PO.
    destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & FM & fcM & m7 & -> & MI7 & ST7 & HEAP7 & WM7 & AG7 & _ & _).
    rewrite (ret_pc_even 0x336444) by (clear; lia). unfold MallocRep.wz. rewrite LIDL in AG7. change (Z.of_nat (Z.to_nat 32)) with 32 in AG7.
    pose proof (agree_on_trans _ _ _ _ AGK6 (KAG m6 m7 OW _ (fun b H => H) AG7 ltac:(intros a [_ Ho]; cbn [outside fst snd] in Ho; clear - Ho ELR SN; lia))) as AGK7. clear AGK6.
    (* [comment removed for export] *)
    assert (XP7 : forall A' cs, rw_cells ctasegs m6 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ LB') spa a /\ ~ (P + 1 <= a < P + 1 + 32)) -> rw_cells ctasegs m7 A' cs).
    { intros A' cs H HA. eapply rw_cells_agree; [exact AG7| exact H| exact HA]. }
    apply XP7 in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH GSZ; lia| clear - Ha PBC PL PH ELR SN CEIL LO STKu SPAL; lia]].
    apply XP7 in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH; lia| clear - Ha PBC PL PH ELR SN CEIL LO STKu SPAL SPAH; lia]].
    apply XP7 in HX4; [| intros a Ha; cbn in Ha; split; [right; right; exists (sc_blk sc, adr (sc_blk sc), 104); split; [exact HIN'| cbn; clear - Ha; lia]| clear - Ha XO ELR SN; lia]].
    apply XP7 in R2; [| intros a Ha; cbn in Ha; split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha; lia]].
    apply XP7 in R3; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - ELR; lia); split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha; lia]].
    apply XP7 in R4; [| intros a Ha; cbn in Ha; split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha ELR; lia]].
    apply XP7 in R5; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - SN; lia); split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha ELR; lia]].
    thaw OFP. apply XP7 in HP; [| intros a Ha; cbn in Ha; split; [right; right; exists (qp, f + 32, 8); split; [exact QPIN| cbn; clear - Ha; lia]| clear - Ha OFP PL PH ELR SN; lia]]. fz OFP.
    thaw SEPQ. apply XP7 in HPP5; [| intros a Ha; cbn in Ha; split; [right; right; exists bPP; split; [exact PPIN'| cbn; clear - Ha PPL PPH; lia]| clear - Ha SEPQ ELR SN; lia]]. fz SEPQ.
    fz HPP5.
    clear XP7 LID6. try clear ST5. try clear ST6. try clear MI5. try clear MI6. try clear HEAP5. try clear HEAP6. try clear MU WM. try clear MU6 WM6.
    ablock HEAP7 HIN' ACCX7 OFFX7. ablock HEAP7 PIN' ACCP7 OFFP7. clear OFFX7 OFFP7. try clear ACCX. try clear ACCP. try clear ACCQ.
    pose proof (munch_refl [(P + 33, P + 43); (f + 32, f + 40)]%Z m7) as MU. pose proof (wmono_refl ctasegs m7) as WM.
    assert (OFFW7 : offshW [(P + 33, P + 43); (f + 32, f + 40)]%Z) by (pose proof OFFP as X0; thaw X0; thaw G5; cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO STKu SPAL SPAH G3 G4 G5 X0 PL PH ELR SN; lia).
    thaw OFP.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    zstep. zstep. ab_shload 1. ts_read HX4 40 6%nat 7 1%nat RD7. zstep. clear RD7. ab_ichk 13%Z 14%Z 0x336470.
    zstep. zstep.
    zstep. zstep. ab_shload 1. ts_read HX4 40 6%nat 6 2%nat RD6. zstep. clear RD6. ab_ichk 13%Z 14%Z 0x33648c.
    zstep. zstep.
    zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x3364a8.
    zstep. zstep. zstep.
    zstep. zstep. ab_shload 1. ts_read HX4 40 6%nat 4 4%nat RD4. zstep. clear RD4. ab_ichk 13%Z 14%Z 0x3364c8.
    zstep. zstep.
    zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x3364e4.
    zstep. zstep. zstep.
    zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x336504.
    zstep. zstep. zstep.
    zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x336524.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. ab_shload 1. zstep. ab_ichk 12%Z 13%Z 0x336544. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ab_shload 1. zstep. ab_ichk 12%Z 13%Z 0x336574. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. ab_shload 1. zstep. ab_ichk 12%Z 13%Z 0x336594. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. thaw OFX. thaw OFQ. thaw G5. zstep. fz OFX. fz OFQ. fz G5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
    match goal with H : munch _ m7 m8 |- _ => rename H into MU8 end. match goal with H : wmono ctasegs m7 m8 |- _ => rename H into WM8 end.
    match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI8 end.
    pose proof (agree_on_trans _ _ _ _ AGK7 (KMU m7 m8 _ MU8 ltac:(constructor; [cbn [fst snd]; right; right; clear - ELR SN; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor]]))) as AGK8. clear AGK7.
    assert (ST8 : stk ctasegs m8 lo spa) by (first [assumption| eapply stk_transport; [exact ST7| exact MU8| exact WM8| cbn; clear; lia]]).
    assert (HEAP8 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m8).
    { eapply (@AH_frame (push AR f 0)); [exact HEAP7| exact MU8| exact WM8|]. apply AWO. constructor; [cbn [fst snd]; right; right; right; clear - ELR SN; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor]]. }
    (* [comment removed for export] *)
    thaw HPP5. thaw SEPQ. thaw OFQ. apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HPP5; [| cbn; clear - SEPQ OFQ PPL PPH ELR SN; lia]. fz SEPQ. fz OFQ.
    fz OFP.
    (* [comment removed for export] *)
    assert (JOIN : forall mj (y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word) Fj fcj (hb3 hb4 hb5 : list byte),
      mem_inv ctasegs mj -> stk ctasegs mj lo spa -> @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' mj -> agree_on KP m5 mj ->
      rw_cells ctasegs mj spa [CB 8 j0; CB 8 j8; CB 8 j16; C8 (Z_to_bv 64 (f + 32)); CB 8 j32; CB 8 j40; C8 (Z_to_bv 64 f); CB g junk] ->
      rw_cells ctasegs mj (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells ctasegs mj (adr (sc_blk sc)) (sct_cells adr sc (-1) 0) ->
      rw_cells ctasegs mj (f + 32) [C8 (Z_to_bv 64 (P + 43 + en))] ->
      rw_cells ctasegs mj PP [C8 (Z_to_bv 64 (P + (47 + en + sn)))] ->
      rw_cells ctasegs mj (P + 43) [CB (Z.to_nat en) hb3] -> rw_cells ctasegs mj (P + 43 + en) [CB 4%nat hb4] -> rw_cells ctasegs mj (P + 47 + en) [CB (Z.to_nat sn) hb5] ->
      cps ctasegs (ASTA RT Σ1 PMc (eq
        (MS (mkR y1 (Z_to_bv 64 spa) gp (Z_to_bv 64 TP_A) y5 y6 y7 sp (Z_to_bv 64 spa) y10 (Z_to_bv 64 (f + 32)) y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 f) (Z_to_bv 64 (adr (sc_blk sc))) (Z_to_bv 64 (en + 47 + sn)) (Z_to_bv 64 0) (Z_to_bv 64 (Z.shiftr (adr (sc_blk sc) + 56) 3 + SHB)) (Z_to_bv 64 (P + 43))
                 (Z_to_bv 64 (adr (sc_blk sc) + 56)) (Z_to_bv 64 (shad f)) (Z_to_bv 64 f) (Z_to_bv 64 SHB) y28 y29 y30 y31)
            Fj (Z_to_bv 64 0x3365e8) fcj None mj (seg_rom ctasegs)))) Q).
    { clear - AWO INC QPIN HIN' PPIN' PIN' KAG KMU K STKu SPR OK HINL AL16S LENR CE1 CE2 CE3 XB0 XBC QB0 QBC PB0 PBC CEIL LO TOP AL16 TP FLEN CRED CPL PPL PPH PP8 PL PH APO APQ SEPQ
                FRESH GEO CR1 EL1 SPA32 SPAL SPAH GSZ SAVJ G1 G2 G3 G4 G5 CF1 CF2 CF3 LO0 F8 ESPA OFX OFQ OFP XO XQ V0 EL SGC ES SQ0 SN SNE LEN ELR HR GR VR SIGF SQIN SQINB SEPS SEPSQ SQC OFS AGK45 MU5 AG4 PPIN SLEN.
      intros mj y1 y5 y6 y7 y10 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 Fj fcj hb3 hb4 hb5 MIj STj HEAPj AGKj FRLj FRHj HXj HPj HPPj R3j R4j R5j.
      assert (SIGj : bytes_at ctasegs mj (adr sq) sig).
      { pose proof SIGF as X0. thaw X0. thaw SEPS. thaw SEPSQ. thaw OFS. pose proof MU5 as MU5'. thaw MU5'.
        apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU5') in X0; [| rewrite SLEN, Z2Nat.id by (clear - SN; lia); cbn; clear - SEPSQ OFS SQC SN CEIL LO STKu SPAL; lia].
        eapply (bytes_at_agree KP m5 mj _ _ AGKj X0). intros xa Hxa. rewrite SLEN, Z2Nat.id in Hxa by (clear - SN; lia). subst KP. cbv beta. split.
        - right; right. exists (sq, adr sq, sn). split; [exact (in_or_app _ _ _ (or_intror SQIN))| cbn; clear - Hxa; lia].
        - cbn [outside fst snd]. clear - Hxa SEPS. lia. }
      pose proof (munch_refl (@nil (Z * Z)) mj) as MU. pose proof (wmono_refl ctasegs mj) as WM.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. zstep.
      thaw SEPS. thaw OFP. thaw OFX. thaw XO.
      apply evt_done. eapply cps_step_same.
      { eapply (@i2o_sct_sig_write_specA (push AR f 0)) with (lo := lo) (OW := OW) (LB := LB') (adr := adr) (sc := sc) (vs := 0) (PP := f + 32) (P := P + 43 + en)
            (sq := sq) (sn := sn) (sig := sig) (j3 := hb4) (j4 := hb5) (bP := bP); rewrite ?ESPA; try reflexivity.
        - exact HEAPj.
        - exact STj.
        - exact MIj.
        - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
        - unfold I2O_SIG_STACK_A, RT_STACK. clear - LO STKu SPAL. lia.
        - unfold USTACK_TOP. clear - TOP SPAH. lia.
        - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
        - exact HIN'.
        - clear - AL16S. uchk_open. exact AL16S.
        - exact HXj.
        - exact OK.
        - exact V0.
        - exact SGC.
        - exact ES.
        - exists (qp, f + 32, 8). split; [exact QPIN| cbn; clear; lia].
        - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
        - exact HPj.
        - exact PIN'.
        - clear - PL ELR. lia.
        - clear - PH. lia.
        - clear - OFP PL PH ELR SN. lia.
        - unfold SCT_SIZE. clear - XO ELR SN. lia.
        - unfold SCT_SIZE. clear - OFX. lia.
        - exists (sq, adr sq, sn). split; [exact (INC _ (in_or_app _ _ _ (or_intror SQIN)))| cbn; clear; lia].
        - clear - SEPS ELR SN. lia.
        - thaw OFS. clear - OFS. lia.
        - exact R4j.
        - replace (P + 43 + en + 4) with (P + 47 + en) by (clear; lia). exact R5j.
        - exact SIGj.
        - exact SLEN. }
      fz SEPS. fz OFP. fz OFX.
      intros msS POs. unfold i2o_sig_postA in POs. rewrite ?ESPA in POs.
      destruct POs as (o0 & o1 & o2 & e1 & e2 & e3 & e4 & e5 & e6 & e7 & o3 & o4 & o5 & o6 & Fs & fcs & mk & hb4' & -> & MIk & STk & HEAPk & WMk & AGs & HPk & R4k & R5k).
      rewrite (ret_pc_even 0x3365f0) by (clear; lia).
      pose proof (agree_on_trans _ _ _ _ AGKj (KAG mj mk OW _ (fun b H => H) AGs ltac:(intros a [Ha Ho]; cbn [outside fst snd] in Ho |- *; thaw G5;
         destruct Ha as [Ha|[Ha|(b & Hb & Hr)]];
         [ clear - Ha Ho G3 CEIL LO STKu ELR SN; repeat split; try exact I; lia
         | destruct Ha as [(l & h & Hin & Hr) _]; unfold CLIENT_STATIC in Hin; cbn [In] in Hin; destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr Ho G4 ELR SN; repeat split; try exact I; lia
         | pose proof (FRESH b Hb) as O; unfold off_fr in O; change (fs_size 0) with 64 in O; destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O; clear - Hr Ho O ELR SN; repeat split; try exact I; lia ]))) as AGKk.
      apply (rw_cells_agree _ _ _ _ _ AGs) in FRLj; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH GSZ; lia| cbn [outside fst snd]; clear - Ha G3 PBC PH CEIL LO STKu SPAL; lia]].
      apply (rw_cells_agree _ _ _ _ _ AGs) in FRHj; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH; lia| cbn [outside fst snd]; clear - Ha G3 PBC PH CEIL LO STKu SPAL SPAH; lia]].
      thaw SEPQ. thaw OFQ.
      apply (rw_cells_agree _ _ _ _ _ AGs) in HPPj; [| intros a Ha; cbn in Ha; split; [right; right; exists bPP; split; [exact PPIN'| clear - Ha PPL PPH; lia]| cbn [outside fst snd]; clear - Ha OFQ SEPQ PPL PPH ELR SN; lia]].
      fz SEPQ. fz OFQ.
      pose proof (munch_refl (@nil (Z * Z)) mk) as MU2. pose proof (wmono_refl ctasegs mk) as WM2.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. sfalse. zstep.
      apply evt_done. change (Z_to_bv 64 3367600) with (wz IOS_EXIT).
      eapply (@frame_obj_close (push AR f 0)) in HEAPk; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
      eapply (@ios_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
        [exact HEAPk| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STk| exact CEIL| clear - LO STKu SPAL; lia
        | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIk| first [exact FRLj| exact (rw_cells_cb_first mk spa _ 6 FRLj)]| exact FRHj| reflexivity|].
      intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
      rewrite (v_addiw0_int (en + 47 + sn)) by (clear - ELR SN; lia). replace (en + 47 + sn) with (47 + en + sn) by (clear; lia).
      eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'| |].
      + eapply agree_on_trans; [eapply agree_on_mono; [exact AG4| intros a [Ha _]; exact Ha]|].
        eapply agree_on_trans; [exact AGK45|].
        eapply agree_on_trans; [eapply agree_on_mono; [exact AGKk| intros a [Ha Ho]; split; [exact Ha| cbn [outside fst snd] in Ho |- *; clear - Ho; lia]]|].
        eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [exact Hb| exact Hr]].
      + eapply rw_cells_agree; [exact AG'| exact HPPj|]. intros xa Hxa. cbn in Hxa. right; right. exists bPP. split; [exact PPIN| clear - Hxa PPL PPH; lia]. }
    (* [comment removed for export] *)
    clear LIDF.
    destruct (Z.eq_dec en 0) as [EN0|ENP].
    + zstep. rewrite EN0 in *. btaken. rewrite ?Z.add_0_r in *.
      assert (HXf : rw_cells ctasegs m8 (adr (sc_blk sc)) (sct_cells adr sc (-1) 0)).
      { unfold sct_cells, MallocRep.wz. rewrite V0, EL, ES. cbn [optr W_sct_list_free.osz32 option_map SctRep.logid_len]. change (sc_extlen sc) with en. rewrite ?EN0. exact HX4. }
      apply evt_done.
      eapply (JOIN m8); [exact MI8| exact ST8| exact HEAP8| exact AGK8| exact FRL| exact FRH| exact HXf| exact HP| exact HPP5| exact R3| exact R4| exact R5].
    + (* [comment removed for export] *)
      zstep. sfalse.
      pose proof EXTL as EXTL'. destruct (sc_ext sc) as [[xq en']|] eqn:EE; [| exfalso; clear - EXTL' ENP; lia]. subst en'.
      destruct (arr_bytes _ _ _ _ _ ARE) as (ext & EXT & EXTLN & XQIN & _).
      assert (XQINB : In (xq, adr xq, en) (sct_blocks adr sc)) by (unfold sct_blocks; rewrite EE; apply in_or_app; right; apply in_or_app; left; left; reflexivity).
      pose proof (APO _ XQINB) as SEPE. cbn [blk_addr blk_size fst snd] in SEPE. pose proof (EXTP xq en eq_refl) as XQ0.
      pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror XQIN))) as (_ & _ & _ & EQC & _). cbn [blk_addr blk_size fst snd] in EQC.
      pose proof (FRESH _ (in_or_app _ _ _ (or_intror XQIN))) as OFE. unfold off_fr in OFE. change (fs_size 0) with 64 in OFE. cbn [blk_addr blk_size fst snd] in OFE. nrm.
      apply (bytes_at_agree _ m m4 _ _ AG4) in EXT; [| intros xa Hxa; rewrite EXTLN, Z2Nat.id in Hxa by (clear - ELR; lia); right; right; exists (xq, adr xq, en); split; [exact (in_or_app _ _ _ (or_intror XQIN))| cbn; clear - Hxa; lia]].
      assert (EXT9 : bytes_at ctasegs m8 (adr xq) ext).
      { pose proof MU5 as MU5'. thaw MU5'. pose proof SEPQ as SEPQ'. thaw SEPQ'.
        pose proof (APQ _ XQINB) as SEPEQ. cbn [blk_addr blk_size fst snd] in SEPEQ.
        apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU5') in EXT; [| rewrite EXTLN, Z2Nat.id by (clear - ELR; lia); cbn; clear - SEPEQ OFE EQC ELR ENP CEIL LO STKu SPAL; lia].
        eapply (bytes_at_agree KP m5 m8 _ _ AGK8 EXT). intros xa Hxa. rewrite EXTLN, Z2Nat.id in Hxa by (clear - ELR; lia). subst KP. cbv beta. split.
        - right; right. exists (xq, adr xq, en). split; [exact (in_or_app _ _ _ (or_intror XQIN))| cbn; clear - Hxa; lia].
        - cbn [outside fst snd]. clear - Hxa SEPE. lia. }
      clear EXT OFE. cbn [optr] in HX4.
      clear ACCX7 ACCP7. clear MU8 WM8. try clear MU WM.
      ablock HEAP8 HIN' ACCX9 OFFX9. clear OFFX9.
      pose proof (munch_refl (@nil (Z * Z)) m8) as MU. pose proof (wmono_refl ctasegs m8) as WM.
      zstep. zstep. zstep.
      fz SEPE. thaw SEPE.
      apply evt_done. eapply cps_step_same.
      { eapply (@asan_memcpy_cpsA (push AR f 0)) with (d := P + 43) (s := adr xq) (bs := ext) (bd := bP) (bsrc := (xq, adr xq, en)) (lo := lo) (OW := OW) (LB := LB');
          rewrite ?EXTLN, ?ESPA; rewrite ?Z2Nat.id by (clear - ELR; lia); try reflexivity.
        - exact HEAP8.
        - exact ST8.
        - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
        - unfold RT_STACK. clear - LO STKu SPAL. lia.
        - unfold USTACK_TOP. clear - TOP SPAH. lia.
        - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
        - exact MI8.
        - exact PIN'.
        - clear - PL. lia.
        - clear - PH ELR SN. lia.
        - exact (INC _ (in_or_app _ _ _ (or_intror XQIN))).
        - exact EXT9.
        - clear - SEPE ELR SN. lia.
        - clear - ELR. lia. }
      fz SEPE.
      intros msE POE. unfold icall_post in POE. rewrite ?ESPA in POE.
      destruct POE as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & FE & fcE & mA & -> & MIA & STA & HEAPA & WMA & AGA & BZA & WRA).
      rewrite (ret_pc_even 0x3365d0) by (clear; lia). unfold MallocRep.wz. rewrite EXTLN in AGA, WRA. rewrite Z2Nat.id in AGA, WRA by (clear - ELR; lia).
      pose proof (agree_on_trans _ _ _ _ AGK8 (KAG m8 mA OW _ (fun b H => H) AGA ltac:(intros a [_ Ho]; cbn [outside fst snd] in Ho; clear - Ho ELR SN; lia))) as AGKA.
      assert (XPA : forall A' cs, rw_cells ctasegs m8 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ LB') spa a /\ ~ (P + 43 <= a < P + 43 + en)) -> rw_cells ctasegs mA A' cs).
      { intros A' cs H HA. eapply rw_cells_agree; [exact AGA| exact H| exact HA]. }
      apply XPA in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH GSZ; lia| clear - Ha PBC PL PH ELR SN CEIL LO STKu SPAL; lia]].
      apply XPA in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH; lia| clear - Ha PBC PL PH ELR SN CEIL LO STKu SPAL SPAH; lia]].
      apply XPA in HX4; [| intros a Ha; cbn in Ha; split; [right; right; exists (sc_blk sc, adr (sc_blk sc), 104); split; [exact HIN'| cbn; clear - Ha; lia]| clear - Ha XO ELR SN; lia]].
      apply XPA in R4; [| intros a Ha; cbn in Ha; split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha ELR; lia]].
      apply XPA in R5; [| intros a Ha; cbn [cells_size csize] in Ha; rewrite Nat.add_0_r, Z2Nat.id in Ha by (clear - SN; lia); split; [right; right; exists bP; split; [exact PIN'| cbn; clear - Ha PL PH ELR SN; lia]| clear - Ha ELR; lia]].
      thaw OFP. apply XPA in HP; [| intros a Ha; cbn in Ha; split; [right; right; exists (qp, f + 32, 8); split; [exact QPIN| cbn; clear - Ha; lia]| clear - Ha OFP PL PH ELR SN; lia]]. fz OFP.
      thaw SEPQ. apply XPA in HPP5; [| intros a Ha; cbn in Ha; split; [right; right; exists bPP; split; [exact PPIN'| cbn; clear - Ha PPL PPH; lia]| clear - Ha SEPQ ELR SN; lia]]. fz SEPQ.
      assert (R3A : rw_cells ctasegs mA (P + 43) [CB (Z.to_nat en) ext]).
      { split; [split; [cbn; split; [exact EXTLN| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BZA]|].
        cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - ELR; lia). exact WRA. }
      clear XPA EXT9 R3 BZA WRA. clear MU WM ACCX9. try clear ST8. clear HEAP8 MI8.
      ablock HEAPA HIN' ACCXA OFFXA. clear OFFXA.
      pose proof (munch_refl [(f + 32, f + 40)]%Z mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
      assert (OFFWA : offshW [(f + 32, f + 40)]%Z) by (thaw G5; cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO STKu SPAL SPAH G3 G4 G5; lia).
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. zstep. zstep. thaw OFX. thaw OFP. thaw OFQ. thaw G5. zstep. fz OFX. fz OFP. fz OFQ. fz G5.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mB end.
      match goal with H : munch _ mA mB |- _ => rename H into MUb end. match goal with H : wmono ctasegs mA mB |- _ => rename H into WMb end.
      match goal with H : mem_inv ctasegs mB |- _ => rename H into MIB end.
      pose proof (agree_on_trans _ _ _ _ AGKA (KMU mA mB _ MUb ltac:(constructor; [cbn [fst snd]; right; left; reflexivity| constructor]))) as AGKB.
      assert (STB : stk ctasegs mB lo spa) by (first [assumption| eapply stk_transport; [exact STA| exact MUb| exact WMb| cbn; clear; lia]]).
      assert (HEAPB : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' mB).
      { eapply (@AH_frame (push AR f 0)); [exact HEAPA| exact MUb| exact WMb|]. apply AWO. constructor; [cbn [fst snd]; right; left; reflexivity| constructor]. }
      assert (HXf : rw_cells ctasegs mB (adr (sc_blk sc)) (sct_cells adr sc (-1) 0)).
      { unfold sct_cells, MallocRep.wz. rewrite V0, EL, ES, EE. cbn [optr W_sct_list_free.osz32 option_map SctRep.logid_len]. change (sc_extlen sc) with en. exact HX4. }
      replace (en + 47 + sn) with (47 + en + sn) in HPP5 by (clear; lia).
      replace (en + (P + 43)) with (P + 43 + en) in HP by (clear; lia).
      apply evt_done.
      eapply (JOIN mB); [exact MIB| exact STB| exact HEAPB| exact AGKB| exact FRL| exact FRH| exact HXf| exact HP| exact HPP5| exact R3A| exact R4| exact R5].
  - (* [comment removed for export] *)
    assert (VNZ : sc_version sc <> 0) by (intros E0; apply KV; rewrite E0; reflexivity).
    assert (V8 : 0 < sc_version sc < 256).
    { destruct VR as [E0|VR']; [exfalso; pose proof CPL as X0; unfold sct_complete in X0; rewrite E0 in X0; cbn in X0; discriminate| clear - VR' VNZ; lia]. }
    clear VR KV.
    pose proof CPL as CPL'. unfold sct_complete in CPL'.
    replace (sc_version sc =? -1) with false in CPL' by (symmetry; apply Z.eqb_neq; clear - V8; lia).
    replace (sc_version sc =? 0) with false in CPL' by (symmetry; apply Z.eqb_neq; exact VNZ).
    destruct (sc_blob sc) as [[bq bn]|] eqn:EB; [| discriminate]. clear CPL'.
    pose proof (BLOBP bq bn eq_refl) as BQ0.
    assert (LEN : i2o_sct_len sc = bn) by (unfold i2o_sct_len; replace (sc_version sc =? 0) with false by (symmetry; apply Z.eqb_neq; exact VNZ); exact BLBL).
    destruct (arr_bytes _ _ _ _ _ ARB) as (blob & BLOB & BLEN & BQIN & BNP).
    assert (BN : 0 < bn <= 65535) by (pose proof BLR as X0; rewrite BLBL in X0; clear - X0 BNP; lia).
    rewrite LEN in *. rewrite BLBL in HX4. cbn [optr] in HX4.
    assert (BQINB : In (bq, adr bq, bn) (sct_blocks adr sc)).
    { unfold sct_blocks. rewrite EB. apply in_or_app; right. apply in_or_app; right. apply in_or_app; right. apply in_or_app; left. left. reflexivity. }
    pose proof (APO _ BQINB) as SEPB. pose proof (APQ _ BQINB) as SEPBQ. cbn [blk_addr blk_size fst snd] in SEPB, SEPBQ.
    pose proof (AH_range_gen _ _ _ _ _ HEAP (in_or_app _ _ _ (or_intror BQIN))) as (_ & _ & _ & BQC & _). cbn [blk_addr blk_size fst snd] in BQC.
    pose proof (FRESH _ (in_or_app _ _ _ (or_intror BQIN))) as OFB. unfold off_fr in OFB. change (fs_size 0) with 64 in OFB. cbn [blk_addr blk_size fst snd] in OFB. nrm.
    apply (bytes_at_agree _ m m4 _ _ AG4) in BLOB; [| intros xa Hxa; rewrite BLEN, Z2Nat.id in Hxa by (clear - BN; lia); right; right; exists (bq, adr bq, bn); split; [exact (in_or_app _ _ _ (or_intror BQIN))| cbn; clear - Hxa; lia]].
    assert (BLOBF : frozen (bytes_at ctasegs m4 (adr bq) blob)) by exact BLOB. clear BLOB.
    fz SEPB. fz SEPBQ. fz OFB. fz OFX. fz OFQ. fz OFP.
    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (Z.shiftr_div_pow2 _ 31), Z.div_small by (clear - BN; lia). zstep. btaken.
    zstep. sfalse.
    (* [comment removed for export] *)
    zstep. zstep. zstep. sfalse. zstep. thaw OFX. thaw OFQ. thaw OFP. thaw G5. zstep. fz OFX. fz OFQ. fz OFP. fz G5. zstep. zstep.
    (* [comment removed for export] *)
    thaw XQ. thaw SEPQ. thaw OFQ. zstep. fz XQ. fz OFQ. fz SEPQ. zstep. rewrite sx32_mod32 by (clear - V8; lia). zstep. zstep. sfalse.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m5 end.
    match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
    match goal with H : mem_inv ctasegs m5 |- _ => rename H into MI5 end.
    match goal with H : rw_cells ctasegs m5 PP _ |- _ => rename H into HPP5 end.
    assert (ST5 : stk ctasegs m5 lo spa) by (first [assumption| eapply stk_transport; [exact ST4| exact MU5| exact WM5| cbn; clear; lia]]).
    assert (HEAP5 : @BnHeapA.AHEAP (push AR f 0) Σ1 OW LB' m5).
    { eapply (@AH_frame (push AR f 0)); [exact HEAPp| exact MU5| exact WM5|]. apply AWO. constructor; [cbn [fst snd]; left; clear - SPAH; lia| constructor; [cbn [fst snd]; right; left; reflexivity| constructor; [cbn [fst snd]; right; right; left; reflexivity| constructor]]]. }
    assert (AGK45 : agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(PP, PP + 8); (P, P + bn)]%Z a) m4 m5).
    { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)|]. intros a [Ha Ho]. cbn [outside fst snd] in Ho |- *. thaw G5.
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha Ho SPAH G3 CEIL LO STKu; repeat split; try exact I; lia| |].
      - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr Ho CEIL CE1 LO STKu SPAL G4; repeat split; try exact I; lia.
      - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 0) with 64 in O.
        destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, B3', O. unfold BnHeapA.ACEIL, STACK_WIN in B3'. clear - Hr Ho B3' O CEIL LO STKu SPAL. repeat split; try exact I; lia. }
    fz G5.
    assert (BLOB5 : bytes_at ctasegs m5 (adr bq) blob).
    { pose proof BLOBF as X0. thaw X0. thaw SEPBQ. thaw OFB.
      apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU5) in X0; [exact X0|]. rewrite BLEN, Z2Nat.id by (clear - BN; lia). cbn. clear - SEPBQ OFB BQC BN CEIL LO STKu SPAL. lia. }
    clear BLOBF WM5. try clear MU WM. clear ACCX ACCQ ACCP. fz MU5.
    ablock HEAP5 HIN' ACCX5 OFFX5. clear OFFX5.
    pose proof (munch_refl (@nil (Z * Z)) m5) as MU. pose proof (wmono_refl ctasegs m5) as WM.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    thaw SEPB.
    apply evt_done. eapply cps_step_same.
    { eapply (@asan_memcpy_cpsA (push AR f 0)) with (d := P) (s := adr bq) (bs := blob) (bd := bP) (bsrc := (bq, adr bq, bn)) (lo := lo) (OW := OW) (LB := LB');
        rewrite ?BLEN, ?ESPA; rewrite ?Z2Nat.id by (clear - BN; lia); try reflexivity.
      - exact HEAP5.
      - exact ST5.
      - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      - unfold RT_STACK. clear - LO STKu SPAL. lia.
      - unfold USTACK_TOP. clear - TOP SPAH. lia.
      - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
      - exact MI5.
      - exact PIN'.
      - exact PL.
      - exact PH.
      - exact (INC _ (in_or_app _ _ _ (or_intror BQIN))).
      - exact BLOB5.
      - clear - SEPB BN. lia.
      - clear - BN. lia. }
    fz SEPB.
    intros msE POE. unfold icall_post in POE. rewrite ?ESPA in POE.
    destruct POE as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & FE & fcE & mA & -> & MIA & STA & HEAPA & WMA & AGA & _ & _).
    rewrite (ret_pc_even 0x336400) by (clear; lia). unfold MallocRep.wz. rewrite BLEN in AGA. rewrite Z2Nat.id in AGA by (clear - BN; lia).
    assert (XPA : forall A' cs, rw_cells ctasegs m5 A' cs -> (forall a, A' <= a < A' + Z.of_nat (cells_size cs) -> aclient_addr (OW ++ LB') spa a /\ ~ (P <= a < P + bn)) -> rw_cells ctasegs mA A' cs).
    { intros A' cs H HA. eapply rw_cells_agree; [exact AGA| exact H| exact HA]. }
    apply XPA in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH GSZ; lia| clear - Ha PBC PL PH BN CEIL LO STKu SPAL; lia]].
    apply XPA in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [left; unfold USTACK_TOP; clear - Ha TOP SPAH; lia| clear - Ha PBC PL PH BN CEIL LO STKu SPAL SPAH; lia]].
    thaw SEPQ. apply XPA in HPP5; [| intros a Ha; cbn in Ha; split; [right; right; exists bPP; split; [exact PPIN'| cbn; clear - Ha PPL PPH; lia]| clear - Ha SEPQ BN; lia]]. fz SEPQ.
    clear XPA MU WM ACCX5.
    pose proof (munch_refl (@nil (Z * Z)) mA) as MU. pose proof (wmono_refl ctasegs mA) as WM.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep.
    apply evt_done. change (Z_to_bv 64 3367600) with (wz IOS_EXIT).
    eapply (@frame_obj_close (push AR f 0)) in HEAPA; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 0) with 64; clear; lia].
    eapply (@ios_epi_cps AR Q) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
      [exact HEAPA| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact STA| exact CEIL| clear - LO STKu SPAL; lia
      | exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MIA| exact FRL| exact FRH| reflexivity|].
    intros Σ' m' HEAP' CR' LIVE' ST' MI' AG'.
    rewrite (v_addiw0_int bn) by (clear - BN; lia).
    eapply K; [exact HEAP'| rewrite CR'; exact CR1| rewrite LIVE'; exact EL1| exact ST'| exact MI'| |].
    + eapply agree_on_trans; [eapply agree_on_mono; [exact AG4| intros a [Ha _]; exact Ha]|].
      eapply agree_on_trans; [exact AGK45|].
      eapply agree_on_trans.
      { eapply agree_on_mono; [exact AGA|]. intros a [Ha Ho]. split; [| cbn [outside fst snd] in Ho; clear - Ho; lia].
        destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [exact (INC b Hb)| exact Hr]]. }
      eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [exact Hb| exact Hr]].
    + eapply rw_cells_agree; [exact AG'| exact HPP5|]. intros xa Hxa. cbn in Hxa. right; right. exists bPP. split; [exact PPIN| clear - Hxa PPL PPH; lia].
Qed.
End WithRT.
