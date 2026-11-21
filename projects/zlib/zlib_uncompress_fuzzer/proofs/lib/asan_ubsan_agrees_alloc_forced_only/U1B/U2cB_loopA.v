(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* [U14B] A2 2026-11-12: the 1.4 uncompress chain.  This text is a 3-way merge (tools/merge3.sh run loopA1): the view's
   text, the 1.3.1 ASan twin as base, and G's 1.4 ASan twin U1A/U2cA_loopA (cure C36) moved to the combined image by
   tools/g2b.py; conflicts take G's side except the depot-chain hypothesis, which stays the combined one (UINB:
   [AMALLOC_PC; RA_UW_ZALLOC]); then the combined registers of LOOP by hand (marked [U14B]). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2BObj U2BClient U2BIface U2BGlue U2BIfaceS InfBBase InfBIface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U1B Require Import U2cB_pre U2cB_loop U2cB_inv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section Loop.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB1 F := (mkABlock (ABFake 0) F 64).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis INF_W : inflate_stmtA AI rng_fs true.
Hypothesis INF_N : inflate_stmtA AI rng_fs false.
Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variables (L : alayout) (SPA Fu F1 FLG lo : Z).
Variables (S D n : Z) (payload : list Z) (ps : AsanCtrl.aptr) (LB0 : list ablock).
Variables (j8 j16 : list byte) (n0 : Z) (trc : list Z) (m0 : amem) (RNG0 : footprint) (sR : APS).
Notation SP := (bv_unsigned sp).
Variable SL : Z.
Hypothesis ESL : SL = SP + 8.
Notation DL := (SP + 16).
Notation Zs := (Fu + 32).
Notation SHF := (Z.shiftr Fu 3 + 2147450880).
Notation OB := A_OUTBUF.

Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - UC_STACK.
Hypothesis SPAB : SP - 176 <= SPA <= SP - 160.
Hypothesis SPA32 : SPA mod 32 = 0.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis SPTOP : SP + 48 < al_top L.
Hypothesis FU256 : Fu mod 256 = 0.
Hypothesis FUB : ablk Fu (Fu + 256).
Hypothesis F1128 : F1 mod 64 = 0.
Hypothesis F1B : ablk F1 (F1 + 64).
Hypothesis F1IN : In (FB1 F1) LB0.
Hypothesis LBH : forall b, In b LB0 -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis SBK : ablk S (S + 7176).
Hypothesis S0SP : bv_unsigned s0 <= SP.
Hypothesis TPE : tp = Z_to_bv 64 ATP.
Hypothesis RAOK : 4096 <= bv_unsigned ra /\ bv_unsigned ra <> AMALLOC_PC.
Hypothesis TRL : (length trc <= 26)%nat.
Hypothesis UINB : In [AMALLOC_PC; RA_UW_ZALLOC] (al_U L).
Hypothesis RFU0 : rng RNG0 Fu 256.
Hypothesis RSFU0 : rng RNG0 SHF 32.
Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
Hypothesis RIMG0 : rng_aimg RNG0.
Hypothesis RISH0 : rng_aimg_sh RNG0.
Hypothesis RFS0 : rng_fs L RNG0.
Hypothesis N26 : 0 <= n < 67108864.

Notation UINV := (uc_inv AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL).
Notation LBN := (LBn Fu S ps LB0).

Notation LOOP pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 len v10 left x28 x29 x30 x31 mm :=
  (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) x10 x11 x12 x13 x14 x15 x16 x17
           (* [U14B] A2 2026-11-12: the COMBINED 1.4 image: s3 = destLen, s5 = left (as LOOP in U2cB_loop) *)
           (Z_to_bv 64 Fu) (Z_to_bv 64 DL) (Z_to_bv 64 SL) (Z_to_bv 64 left) v10 (Z_to_bv 64 Zs)
           (Z_to_bv 64 (Z.shiftr Fu 3 + 2147450880)) (Z_to_bv 64 Fu) (Z_to_bv 64 2147450880) (Z_to_bv 64 len) x28 x29 x30 x31)
      FR (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

Definition uc_end (Wd : Z) (RNG : footprint) (s : APS) (LB : list ablock) : machine_state -> Prop :=
  fun ms' => exists (site rcode : Z) (st : ist) (v : uvw) (m : amem) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    ms' = LOOP 0x8cf5c (Z_to_bv 64 site) x5 x6 x7 (Z_to_bv 64 rcode) x11 x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m
    /\ 0 <= rcode < 2^64 /\ UINV Wd RNG s LB st v m.

Lemma uspa : bv_unsigned (Z_to_bv 64 SPA) = SPA.
Proof. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. cbn in R. atop_facts. apply unsigned_lit. unfold UC_STACK in LOS. lia. Qed.

Lemma site_ret : forall site, site = 0x8cf08 \/ site = 0x8cf4c -> ret_pc (Z_to_bv 64 site) = Z_to_bv 64 site.
Proof. intros site [->| ->]; apply ret_pc_even; try lia; reflexivity. Qed.

Lemma uc_loopW : forall (k : nat) Wd RNG s LB st v m site (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  Wd <> 0 -> umu n st < Z.of_nat k -> site = 0x8cf08 \/ site = 0x8cf4c ->
  UINV Wd RNG s LB st v m ->
  evtF bsegs RNG (uc_end Wd RNG s LB)
    (LOOP A_INFLATE (Z_to_bv 64 site) x5 x6 x7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros Wd RNG s LB st v m site x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 WNZ MU SITE INV.
  { exfalso. destruct INV as (_ & _ & AV & _). pose proof (M2_nonneg _ _ _ _ AV) as X. unfold umu in MU. cbn [ucx icx_of c_n c_osz Wm] in X. unfold Wm in X. cbn in X. lia. }
  pose proof INV as (AH & IO & AV & MD & EM & ST & MI & FRM & PFA & OK & RS & FP & SH).
  pose proof uspa as USPA.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  assert (RFU : rng RNG Fu 256) by (eapply rng_fp_le; [exact FP| exact RFU0]).
  assert (RSFU : rng RNG SHF 32) by (eapply rng_fp_le; [exact FP| exact RSFU0]).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  eapply evtF_cut.
  { eapply (INF_W L RNG (Z_to_bv 64 site) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Zs) (Z_to_bv 64 0)
                  x12 x13 x14 x15 x16 x17 _ _ _ _ _ _ _ _ _ _ x28 x29 x30 x31 FR fc m s LB (ucx S D n Wd st) Fu Zs lo payload st
                  (v_lf v) (v_cf v) (v_wf v) (v_fo v) (bv_unsigned ra :: trc));
      [exact AH| exact IO| exact WNZ| exact AV| exact MD| reflexivity| reflexivity| reflexivity| exact EM
      | exact (u2_img_of_aheap AI _ _ _ _ _ AH)| rewrite USPA; exact ST| exact LOC| rewrite USPA; unfold INF_STACK, UC_STACK in *; lia
      | rewrite USPA; Z.div_mod_to_equations; lia| rewrite USPA; lia| exact MI| exact TPE| reflexivity| reflexivity
      | destruct SITE as [->| ->]; rewrite unsigned_lit by lia; lia
      | destruct SITE as [->| ->]; rewrite unsigned_lit by lia; unfold AMALLOC_PC; lia
      | intros X; discriminate X
      | eapply rng_fp_le; [exact FP| exact RSTK0]| eapply rng_fp_le; [exact FP| exact RIMG0]| eapply rng_fp_le; [exact FP| exact RISH0]| eapply rng_fs_mono; [exact FP| exact RFS0]| exact OK]. }
  cbv beta. intros ms1 [RET|(X & _)]; [| discriminate X].
  unfold inf_ret in RET. rewrite USPA in RET.
  destruct RET as (rcode & st' & lf' & cf' & wf' & fo' & zti & zto & zmsg & zopq & zdt & zadl & zres & zp1 & zp2 & zp3 & havedict & dmax & check & total & back & was & pad
                   & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & RC & MI' & ST' & AH' & CA & IO' & AV' & MD' & EM' & DEC & WLE).
  set (v' := UVW lf' cf' wf' fo' zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad).
  assert (INV' : UINV Wd RNG s LB st' v' m').
  { eapply (uc_inv_ret AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL ESL
                       LOC ltac:(unfold UC_STACK in LOS; lia) SPAB ltac:(lia) FU256 FUB F1128 F1B F1IN SBK S0SP Wd Wd RNG RNG s s LB LB st v m st' v' m');
      [exact INV| apply fp_le_refl| reflexivity| exact SH| exact MI'| exact ST'| exact AH'| exact CA| exact IO'| exact AV'| exact MD'| exact EM']. }
  rewrite (site_ret site SITE).
  destruct (Z.eq_dec rcode 0) as [->|RNZ].
  -
    specialize (DEC eq_refl).
    eapply evtF_cut; [eapply (uc_ret0 gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU site); exact SITE|].
    cbv beta. intros ms2 ->.
    pose proof INV' as (_ & _ & AV2 & _ & EM2 & _).
    unfold uc_emem, inf_emem in EM2. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w] in EM2. destruct EM2 as (STRM2 & _).
    destruct AV2 as (RG2 & _). unfold IDefs.RNG in RG2. cbn [ucx icx_of c_n c_osz] in RG2. destruct RG2 as (G1 & G2 & G3 & G4 & _).
    eapply evtF_cut.
    { eapply (uc_next gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU); [exact MI'| exact STRM2| lia| lia]. }
    cbv beta. intros ms3 (m3 & site' & y10 & SITE' & -> & MU3 & WM3 & MI3 & STRM3).
    eapply (IH Wd RNG s LB st' v' m3 site'); [exact WNZ| | exact SITE'|].
    + unfold M2, M2e in DEC. cbn [ucx icx_of c_n c_osz c_W0 c_cin0 Wm] in DEC. unfold Wm in DEC. cbn [ucx icx_of c_n c_osz] in DEC. unfold umu in *. lia.
    + eapply (uc_inv_strm AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL ESL
                          LOC ltac:(unfold UC_STACK in LOS; lia) SPAB ltac:(lia) FU256 FUB F1128 F1B F1IN SBK S0SP);
        [exact INV'| exact MU3| exact WM3| exact MI3| exact STRM3].
  -
    eapply evtF_mono; [eapply (uc_retN gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU site rcode); [exact SITE| exact RNZ| lia]|].
    cbv beta. intros ms2 ->. unfold uc_end. exists site, rcode, st', v', m'. do 14 eexists.
    split; [reflexivity|]. split; [lia| exact INV'].
Qed.

Definition uc_postW (RNG : footprint) (s : APS) (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ aps_rest s' = aps_rest s /\
    match r with None => False | Some pw => exists Wd, Wd <> 0 /\ uc_end Wd RNG' s' (HB pw Wd 32768 :: LBN) ms' end.

Lemma uc_after_ret : forall Wd RNG s LB st' v' m' site rcode (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (P : machine_state -> Prop),
  site = 0x8cf08 \/ site = 0x8cf4c -> 0 <= rcode < 18446744073709551616 ->
  UINV Wd RNG s LB st' v' m' ->
  (forall ms, uc_end Wd RNG s LB ms -> P ms) ->
  (rcode = 0 -> forall m3 site' (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
     site' = 0x8cf08 \/ site' = 0x8cf4c -> UINV Wd RNG s LB st' v' m3 ->
     evtF bsegs RNG P (LOOP A_INFLATE (Z_to_bv 64 site') x5 x6 x7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m3)) ->
  evtF bsegs RNG P
    (LOOP site (Z_to_bv 64 site) t0 t1 t2 (Z_to_bv 64 rcode) a1 a2 a3 a4 a5 a6 a7 0 (Z_to_bv 64 4294967295) 0 t3 t4 t5 t6 m').
Proof.
  intros Wd RNG s LB st' v' m' site rcode t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 P SITE RC INV' KE KNEXT.
  pose proof INV' as (AH & IO & AV & MD & EM & ST & MI & FRM & PFA & OK & RS & FP & SH).
  assert (RFU : rng RNG Fu 256) by (eapply rng_fp_le; [exact FP| exact RFU0]).
  assert (RSFU : rng RNG SHF 32) by (eapply rng_fp_le; [exact FP| exact RSFU0]).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  destruct (Z.eq_dec rcode 0) as [->|RNZ].
  - eapply evtF_cut; [eapply (uc_ret0 gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU site); exact SITE|].
    cbv beta. intros ms2 ->.
    unfold uc_emem, inf_emem in EM. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w] in EM. destruct EM as (STRM2 & _).
    destruct AV as (RG2 & _). unfold IDefs.RNG in RG2. cbn [ucx icx_of c_n c_osz] in RG2. destruct RG2 as (G1 & G2 & G3 & G4 & _).
    eapply evtF_cut.
    { eapply (uc_next gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU); [exact MI| exact STRM2| lia| lia]. }
    cbv beta. intros ms3 (m3 & site' & y10 & SITE' & -> & MU3 & WM3 & MI3 & STRM3).
    eapply (KNEXT eq_refl m3 site'); [exact SITE'|].
    eapply (uc_inv_strm AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL ESL
                        LOC ltac:(unfold UC_STACK in LOS; lia) SPAB ltac:(lia)
                        FU256 FUB F1128 F1B F1IN SBK S0SP);
      [exact INV'| exact MU3| exact WM3| exact MI3| exact STRM3].
  - eapply evtF_mono; [eapply (uc_retN gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU site rcode); [exact SITE| exact RNZ| lia]|].
    cbv beta. intros ms2 ->. apply KE. unfold uc_end. exists site, rcode, st', v', m'. do 14 eexists.
    split; [reflexivity|]. split; [lia| exact INV'].
Qed.

Lemma uc_loopN : forall (k : nat) RNG s st v m site (x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
  umu n st < Z.of_nat k -> site = 0x8cf08 \/ site = 0x8cf4c ->
  UINV 0 RNG s LBN st v m ->
  evtF bsegs RNG (fun ms1 => uc_end 0 RNG s LBN ms1 \/ implMA RNG (amalloc_M 32768) s (uc_postW RNG s) ms1)
    (LOOP A_INFLATE (Z_to_bv 64 site) x5 x6 x7 (Z_to_bv 64 Zs) (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 0 (Z_to_bv 64 4294967295) 0 x28 x29 x30 x31 m).
Proof.
  induction k as [|k IH]; intros RNG s st v m site x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 MU SITE INV.
  { exfalso. destruct INV as (_ & _ & AV & _). pose proof (M2_nonneg _ _ _ _ AV) as X. unfold umu in MU. cbn [ucx icx_of c_n c_osz Wm] in X. unfold Wm in X. cbn in X. lia. }
  pose proof INV as (AH & IO & AV & MD & EM & ST & MI & FRM & PFA & OK & RS & FP & SH).
  pose proof uspa as USPA.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  destruct RAOK as [RA4 RANE].
  eapply evtF_cut.
  { eapply (INF_N L RNG (Z_to_bv 64 site) (Z_to_bv 64 SPA) gp tp x5 x6 x7 sp (Z_to_bv 64 SPA) (Z_to_bv 64 Zs) (Z_to_bv 64 0)
                  x12 x13 x14 x15 x16 x17 _ _ _ _ _ _ _ _ _ _ x28 x29 x30 x31 FR fc m s LBN (ucx S D n 0 st) Fu Zs lo payload st
                  (v_lf v) (v_cf v) (v_wf v) (v_fo v) (bv_unsigned ra :: trc));
      [exact AH| exact IO| reflexivity| exact AV| exact MD| reflexivity| reflexivity| reflexivity| exact EM
      | exact (u2_img_of_aheap AI _ _ _ _ _ AH)| rewrite USPA; exact ST| exact LOC| rewrite USPA; unfold INF_STACK, UC_STACK in *; lia
      | rewrite USPA; Z.div_mod_to_equations; lia| rewrite USPA; lia| exact MI| exact TPE| reflexivity| reflexivity
      | destruct SITE as [->| ->]; rewrite unsigned_lit by lia; lia
      | destruct SITE as [->| ->]; rewrite unsigned_lit by lia; unfold AMALLOC_PC; lia
      |
      | eapply rng_fp_le; [exact FP| exact RSTK0]| eapply rng_fp_le; [exact FP| exact RIMG0]| eapply rng_fp_le; [exact FP| exact RISH0]| eapply rng_fs_mono; [exact FP| exact RFS0]| exact OK].
    intros _. exact UINB. }
  cbv beta. intros ms1 [RET|(_ & IMPL)].
  -
    unfold inf_ret in RET. rewrite USPA in RET.
    destruct RET as (rcode & st' & lf' & cf' & wf' & fo' & zti & zto & zmsg & zopq & zdt & zadl & zres & zp1 & zp2 & zp3 & havedict & dmax & check & total & back & was & pad
                     & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & RC & MI' & ST' & AH' & CA & IO' & AV' & MD' & EM' & DEC & WLE).
    set (v' := UVW lf' cf' wf' fo' zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad).
    assert (INV' : UINV 0 RNG s LBN st' v' m').
    { eapply (uc_inv_ret AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL ESL
                         LOC ltac:(unfold UC_STACK in LOS; lia) SPAB ltac:(lia) FU256 FUB F1128 F1B F1IN SBK S0SP 0 0 RNG RNG s s LBN LBN st v m st' v' m');
        [exact INV| apply fp_le_refl| reflexivity| exact SH| exact MI'| exact ST'| exact AH'| exact CA| exact IO'| exact AV'| exact MD'| exact EM']. }
    rewrite (site_ret site SITE).
    eapply (uc_after_ret 0 RNG s LBN st' v' m' site rcode); [exact SITE| exact RC| exact INV'| intros ms HE; left; exact HE|].
    intros R0 m3 site' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SITE' INV3.
    eapply (IH RNG s st' v' m3 site'); [| exact SITE'| exact INV3].
    specialize (DEC R0). unfold M2, M2e in DEC. cbn [ucx icx_of c_n c_osz c_W0 c_cin0 Wm] in DEC. unfold Wm in DEC. cbn [ucx icx_of c_n c_osz] in DEC. unfold umu in *. lia.
  -
    apply evtF_done. right.
    eapply implMA_post_evtF; [exact IMPL|].
    intros r s' RNG' ms' PW. unfold inf_retW in PW. destruct PW as (FPL & RS' & PW).
    destruct r as [pw|]; [| contradiction]. destruct PW as (Wd & W16 & WBK & RET).
    pose proof (ablk_lin _ _ WBK) as (WL1 & _). unfold AIMG_HI in WL1.
    unfold inf_ret in RET. rewrite USPA in RET.
    destruct RET as (rcode & st' & lf' & cf' & wf' & fo' & zti & zto & zmsg & zopq & zdt & zadl & zres & zp1 & zp2 & zp3 & havedict & dmax & check & total & back & was & pad
                     & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & RC & MI' & ST' & AH' & CA & IO' & AV' & MD' & EM' & DEC & WLE).
    set (v' := UVW lf' cf' wf' fo' zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad).
    assert (INV' : UINV Wd RNG' s' (HB pw Wd 32768 :: LBN) st' v' m').
    { eapply (uc_inv_ret AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu F1 FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL ESL
                         LOC ltac:(unfold UC_STACK in LOS; lia) SPAB ltac:(lia) FU256 FUB F1128 F1B F1IN SBK S0SP 0 Wd RNG RNG' s s' LBN (HB pw Wd 32768 :: LBN) st v m st' v' m');
        [exact INV| exact FPL| exact RS'| right; exists pw; split; [reflexivity| split; [exact W16| exact WBK]]
        | exact MI'| exact ST'| exact AH'| exact CA| exact IO'| exact AV'| exact MD'| exact EM']. }
    rewrite (site_ret site SITE).
    eapply (uc_after_ret Wd RNG' s' (HB pw Wd 32768 :: LBN) st' v' m' site rcode); [exact SITE| exact RC| exact INV'| |].
    + intros ms HE. unfold uc_postW. split; [exact FPL|]. split; [exact RS'|]. exists Wd. split; [lia| exact HE].
    + intros R0 m3 site' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 SITE' INV3.
      eapply evtF_mono; [eapply (uc_loopW (Datatypes.S (Z.to_nat (umu n st'))) Wd RNG' s' (HB pw Wd 32768 :: LBN) st' v' m3 site'); [lia| lia| exact SITE'| exact INV3]|].
      cbv beta. intros ms HE. unfold uc_postW. split; [exact FPL|]. split; [exact RS'|]. exists Wd. split; [lia| exact HE].
Qed.
End Loop.
End CANSEC1.
