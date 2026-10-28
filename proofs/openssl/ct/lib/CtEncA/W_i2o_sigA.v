(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApState ApOwner.
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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA W_sct_completeA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
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

(* [comment removed for export] *)
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.

(* [comment removed for export] *)
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].

(* [comment removed for export] *)
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

Definition I2O_SIG_STACK_A : Z := 80 + RT_STACK.     (* [comment removed for export] *)
Definition I2O_SIG_MEMCPY_RA : Z := 0x336004.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition i2o_sig_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo PP P sn : Z) (sig : list byte)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m' hb,
       ms' = MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (Z_to_bv 64 (4 + sn)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
       /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp) /\ AHEAP Σ OW LB m' /\ wmono ctasegs m m'
       /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside [(PP, PP + 8); (P, P + 4 + sn)]%Z a) m m'
       /\ rw_cells ctasegs m' PP [C8 (Z_to_bv 64 (P + 4 + sn))]
       /\ rw_cells ctasegs m' P [CB 4%nat hb] /\ rw_cells ctasegs m' (P + 4) [CB (Z.to_nat sn) sig].

Lemma i2o_sct_sig_write_specA : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (adr : bptr -> Z) (sc : sctr bptr) (vs : Z)
    (PP P : Z) (sq : bptr) (sn : Z) (sig j3 j4 : list byte) (bP : block),
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> mem_inv ctasegs m -> ACEIL <= lo -> lo + I2O_SIG_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> tp = wz TP_A ->
  In (sc_blk sc, adr (sc_blk sc), SCT_SIZE) (OW ++ LB) -> adr (sc_blk sc) mod 16 = 0 ->
  rw_cells ctasegs m (adr (sc_blk sc)) (sct_cells adr sc (-1) vs) -> sct_ok adr sc ->
  sc_version sc = 0 -> sct_sig_complete sc = true -> sc_sig sc = Some (sq, sn) ->
  cellA_in (OW ++ LB) PP 8 -> PP mod 8 = 0 -> rw_cells ctasegs m PP [C8 (Z_to_bv 64 P)] ->
  In bP (OW ++ LB) -> blk_addr bP <= P -> P + 4 + sn <= blk_addr bP + blk_size bP ->
  (PP + 8 <= P \/ P + 4 + sn <= PP) -> (adr (sc_blk sc) + SCT_SIZE <= P \/ P + 4 + sn <= adr (sc_blk sc)) ->
  (PP + 8 <= adr (sc_blk sc) \/ adr (sc_blk sc) + SCT_SIZE <= PP) ->
  cellA_in (OW ++ LB) (adr sq) sn -> (adr sq + sn <= P \/ P + 4 + sn <= adr sq) -> (PP + 8 <= adr sq \/ adr sq + sn <= PP) ->
  rw_cells ctasegs m P [CB 4%nat j3] -> rw_cells ctasegs m (P + 4) [CB (Z.to_nat sn) j4] ->
  bytes_at ctasegs m (adr sq) sig -> length sig = Z.to_nat sn ->
  a0 = Z_to_bv 64 (adr (sc_blk sc)) -> a1 = Z_to_bv 64 PP ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (Z_to_bv 64 I2O_SCT_SIGNATURE_A) fc None m (seg_rom ctasegs))))
              (ASTA RT Σ PMc (i2o_sig_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo PP P sn sig m)).
Proof.
  intros until bP. intros HEAP ST MI CEIL LO SPT SP16 -> HIN AL16 HX OK V0 SC ES ([[bq bQ] bqn] & QIN & QL & QH) AL8 HPP PIN PL PH SEPA SEPX SEPQX
         ([[bs bS] bsn] & SIN & SL & SH) SEPS SEPQS H3 H4 SIG SLEN -> ->.
  cbn [blk_addr blk_size fst snd] in QL, QH, SL, SH.
  change (frozen (adr sq + sn <= P \/ P + 4 + sn <= adr sq)) in SEPS.
  change (frozen (PP + 8 <= adr sq \/ adr sq + sn <= PP)) in SEPQS.
  assert (SIGF : frozen (bytes_at ctasegs m (adr sq) sig)) by exact SIG. clear SIG.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CE1, CE2, CE3.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HIN) as (XB0 & _ & _ & XBC & XBI). cbn [blk_addr blk_size fst snd] in XB0, XBC, XBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP QIN) as (QB0 & _ & _ & QBC & QBI). cbn [blk_addr blk_size fst snd] in QB0, QBC, QBI.
  pose proof (AH_range_gen _ _ _ _ _ HEAP PIN) as (PB0 & _ & _ & PBC & PBI).
  pose proof (AH_range_gen _ _ _ _ _ HEAP SIN) as (SB0 & _ & _ & SBC & SBI). cbn [blk_addr blk_size fst snd] in SB0, SBC, SBI.
  ablock HEAP HIN ACCX OFFX. ablock HEAP QIN ACCQ OFFQ. ablock HEAP PIN ACCP OFFP.
  unfold I2O_SCT_SIGNATURE_A, I2O_SIG_STACK_A, RT_STACK, SCT_SIZE, USTACK_TOP, SEGTOP_A, MallocRep.wz in *.
  pose proof OK as (VR & HR & GR & SIGP & BLOBP & LOGP & ELR & BLR & EXTP & EXTL & BLBL). pose proof (SIGP sq sn ES) as [SQ0 SN].
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (stk_below ctasegs m lo _ MI ST ltac:(lia)) as SPTT. unfold UTOP in SPTT.
  assert (SNE : sc_siglen sc = sn) by (unfold sc_siglen; rewrite ES; reflexivity).
  unfold sct_cells, MallocRep.wz, u32 in HX. rewrite SNE, ES in HX. cbn [optr] in HX.
  pose proof (munch_refl [(lo, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFFW : offshW [(lo, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z) by (cbn [offshW]; alia).
  assert (SEPQ : bQ + bqn <= bv_unsigned sp - 80) by alia.
  assert (SEPP : blk_addr bP + blk_size bP <= bv_unsigned sp - 80) by alia.
  assert (SEPB : adr (sc_blk sc) + 104 <= bv_unsigned sp - 80) by alia.
  assert (SEPSG : bS + bsn <= lo) by alia.
  (* [comment removed for export] *)
  clear VR SIGP BLOBP LOGP ELR BLR EXTP EXTL BLBL.
  fz XBI. fz QBI. fz PBI. fz SBI. fz OFFX. fz OFFQ. fz OFFP. fz SEPA. fz SEPX. fz SEPQX.
  apply cps_from_evt'.
  carve_frame 80%nat ST. do 11 zstep.
  (* [comment removed for export] *)
  zstep. thaw QBI. thaw PBI. zstep. fz QBI. fz PBI. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [left; cbn; alia|]. constructor; [right; right; exists (bq, bQ, bqn); cbn; split; [exact QIN| lia]|].
    constructor; [right; right; exists bP; cbn; split; [exact PIN| lia]| constructor]. }
  eapply evt_cut.
  { eapply SCT_signature_is_complete_specA with (lo := lo) (adr := adr) (sc := sc) (vs := vs); rewrite ?ESP;
      [exact HEAP1| exact ST| exact MI| exact CEIL| lia| exact HIN| exact AL16| | exact OK| reflexivity].
    unfold sct_cells, MallocRep.wz, u32. rewrite SNE, ES. cbn [optr]. exact HX. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  rewrite (ret_pc_even 0x335e1c) by (clear; lia).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HX; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HPP; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in H3; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in H4; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  assert (MU' : munch [(lo, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctasegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI ST HEAP1. rename MU' into MU. rename WM' into WM. rename MI2 into MI. try clear SHB1_ SHB2_. clear m1.
  rewrite SC. cbn [bret].
  (* [comment removed for export] *)
  zstep. bnot. zstep. rewrite sx32_mod32, V0 by lia. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. sfalse. zstep. zstep. sfalse. zstep. zstep. thaw SEPA. thaw SEPQX. zstep. fz SEPQX. thaw SEPX. zstep. zstep.
  (* [comment removed for export] *)
  ab_shload 1. zstep. ab_ichk 12%Z 13%Z 0x335f64. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x335f94. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x335fb8. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. ab_shload 1. zstep. ab_ichk 13%Z 14%Z 0x335fd8. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  name_mem m3.
  match goal with H : munch _ m m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m m3 |- _ => rename H into WM3 end.
  match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end. match goal with H : stk ctasegs m3 lo _ |- _ => rename H into ST3 end.
  thaw SEPS. thaw SEPQS.
  assert (AWO : Forall (aclient_write_ok (OW ++ LB)) [(lo, bv_unsigned sp); (PP, PP + 8); (P, P + 4 + sn)]%Z).
  { constructor; [left; cbn; alia|]. constructor; [right; right; exists (bq, bQ, bqn); cbn; split; [exact QIN| lia]|].
    constructor; [right; right; exists bP; cbn; split; [exact PIN| lia]| constructor]. }
  assert (HEAP3 : AHEAP Σ OW LB m3) by (eapply AH_frame; [exact HEAP| exact MU3| exact WM3| exact AWO]).
  assert (SIG3 : bytes_at ctasegs m3 (adr sq) sig).
  { pose proof SIGF as X. unfold frozen in X. eapply bytes_at_transport; [exact X| exact MU3|]. rewrite SLEN, Z2Nat.id by lia. cbn. lia. }
  apply evt_done. eapply cps_step_same.
  { eapply asan_memcpy_cpsA with (d := P + 4) (s := adr sq) (bs := sig) (bd := bP) (bsrc := (bs, bS, bsn)) (lo := lo) (OW := OW) (LB := LB);
      rewrite ?SLEN, ?Z2Nat.id by lia; try reflexivity.
    - exact HEAP3.
    - rewrite ESP. exact ST3.
    - exact CEIL.
    - rewrite ESP. unfold RT_STACK. lia.
    - rewrite ESP. unfold USTACK_TOP. lia.
    - rewrite ESP. uchk_open. clear - SP16 SPR. Z.div_mod_to_equations. lia.
    - exact MI3.
    - exact PIN.
    - lia.
    - lia.
    - exact SIN.
    - cbn. lia.
    - cbn. lia.
    - exact SIG3.
    - lia.
    - lia. }
  intros msM PO. unfold icall_post in PO. rewrite ?ESP in PO.
  destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & FM & fcM & mM & -> & MIM & STM & HEAPM & WMM & AGM & BZ & WRM).
  rewrite (ret_pc_even 0x336004) by (clear; lia). unfold MallocRep.wz.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AGM) in FR; [| intros xa Hxa; cbn in Hxa; split; [left; unfold USTACK_TOP; lia| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in HPP; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists (bq, bQ, bqn); cbn; split; [exact QIN| lia]| lia]].
  apply (rw_cells_agree _ _ _ _ _ AGM) in H3; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bP; cbn; split; [exact PIN| lia]| lia]].
  clear MI3 ST3 SIG3 HX H4. try clear SHB1_ SHB2_.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. zstep. rewrite Z.add_0_r, (swrap32_small (sn + 4)) by lia. do 9 zstep. zstep. release_frame FR STM (bv_unsigned sp). zstep.
  apply evt_done. apply cps_post. intros c Hc. eapply ASTA_conseq; [exact Hc|]. intros ms0 <-.
  unfold i2o_sig_postA. lazymatch type of H3 with rw_cells _ _ _ ?cs => do 16 eexists; exists mM, (cells_bytes cs) end.
  split; [replace (4 + sn) with (sn + 4) by lia; reflexivity|].
  split; [exact MIM|]. split; [exact STM|]. split; [exact HEAPM|]. split; [eapply wmono_trans; [exact WM3| exact WMM]|].
  split.
  { eapply agree_on_trans; [| eapply agree_on_mono; [exact AGM| intros a [Ha Hn]; cbn [outside fst snd] in Hn; split; [| lia]]].
    - eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)|]. intros a [Ha Hn]. cbn [outside fst snd] in Hn. cbn [outside fst snd].
      split; [| split; [lia| split; [lia| exact I]]].
      destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia| |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; alia.
      + pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3' & _). alia.
    - destruct Ha as [Ha|[Ha|Ha]]; [left; lia| right; left; exact Ha| right; right; exact Ha]. }
  split; [replace (P + 4 + sn) with (P + (sn + 4)) by lia; exact HPP|].
  split; [eapply (rw_cells_recast _ _ _ _ H3); [cbn; repeat split; reflexivity| cbn; reflexivity| reflexivity]|].
  split; [split; [cbn; split; [exact SLEN| exact I]| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact BZ]|].
  cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. rewrite SLEN, Z2Nat.id in WRM by lia. exact WRM.
Qed.
End WithRT.
