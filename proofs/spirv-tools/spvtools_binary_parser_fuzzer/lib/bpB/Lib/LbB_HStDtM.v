(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_VecT LbB_VecD1 LbB_Own
  LbB_HKit LbB_HStKit LbB_StateStmt LbB_HStDtL LbB_HStDtK LbB_HStDtV.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition hdq (ns : list (Z * list byte)) : Z := match ns with [] => 0 | (q, _) :: _ => q end.

Definition DM3 : Z := 0xed62c.  Definition DM3_B : Z := 0xed674.  Definition DM3_N : Z := 0xed6b4.

Section DtM3h.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

#[local] Definition HTbAHStDtM_0 : list (reg * expr) := [(8%bv, EVar 32); (2%bv, EVar 33); (9%bv, ELit 2147450880)].
  Lemma dtm3h : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB LBr LBn : list block)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (ns : list (Z * list byte)),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM3) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 144) [C8 (wz (hdq ns))] -> SHAD m (st + 144) (repeat (b8 0) 1) -> st mod 8 = 0 ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    nodes_okG 24 LBn m ns -> Permutation LB (LBr ++ LBn) ->
    (ns <> [] -> st + ST_SIZE <= aceil) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> stack0 m lo shi -> spf <= shi ->
    (ns <> [] -> trace_ok (as_TR H) APC0_FREE [DTL3_DRET]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18 x19
                                 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DM3_B) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LBr LBn st spf lo B shi errv mo ns VIS CF SF V8 HLOC NO PERM STC RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC S0 SHI TRK K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    assert (GZF : gz m (st + 144) 8) by (intros i Hi; eapply sh0_of_SHAD0; [exact SF | cbn; Z.div_mod_to_equations; lia]).
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct ns as [|[q tl] ns'].
    -
      destruct LBn as [|b0 LBn]; [|cbn [nodes_okG] in NO; contradiction].
      rewrite app_nil_r in PERM.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM3_B] (SCR [] [] []) DM3 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 144) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CF 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM3 m (seg_rom asegs) HR HK 200%nat [DM3_B] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact PERM
                | apply apres_refl | exact RH | lia].
    -
      pose proof NO as NO0. cbn [nodes_okG] in NO0. destruct LBn as [|[[id q0] n0] LBn']; [contradiction|].
      destruct NO0 as (BA & BS & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS. subst q0 n0.
      assert (INQ : In (id, q, 24) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity).
      pose proof (ah_blocks H HH _ _ _ _ RH INQ) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Q0, Q16, Qn, QI, QC, QF, QAPP. unfold AIMG_TOP in QI.
      pose proof (STC ltac:(discriminate)) as STC'.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 q]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DTL3_LOOP] (SCR [] [] []) DM3 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 144) 8 (EVar 34);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { cbn [hdq] in CF. kword_cell CF 0%nat (C8 (wz q)). }
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM3 m (seg_rom asegs) HR HK 200%nat [DTL3_LOOP] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G10, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (dtl3_loop H HH HCF Q ns' q tl ((id, q, 24) :: LBn') LB LBr);
        [exact VIS1 | exact NO | exact PERM | exact RH | exact KR1 | exact AL0 | exact RA | exact SPB | exact ST | exact CE
        | unfold AFREE_STACK; lia | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC
        | left; rewrite u64_of_Z by lia; lia | exact (TRK ltac:(discriminate)) |].
      intros msF' mo' m' s' LBr' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' PL AP' RH' AC' AL'.
      eapply K; [exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP'] | exact MI' | exact ST' | exact ERR'
                | exact RA' | exact AC' | exact PL | exact AP' | exact RH' | lia].
  Qed.
End DtM3h.

Section DtM3b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma dtm3b : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (bl bc : Z) (qb : bptr),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM3_B) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 128) [C8 (wz bl); C8 (wz bc)] -> SHAD m (st + 128) (repeat (b8 0) 2) -> st mod 8 = 0 ->
    (st_live_frame LF st \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (bl <> 0 -> In (qb, bl, 8 * bc) LB /\ addressable m bl (8 * bc) /\ st + ST_SIZE <= aceil) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf <= shi ->
    (bl <> 0 -> trace_ok (as_TR H) APC0_FREE [DM3_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H)
            (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18 x19
                                 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DM3_N) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB qb bl) m' -> lb_own (dv_LB H LB qb bl) m' ->
       xpres H (dv_LB H LB qb bl) spf [(st + 128, st + 136)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 128) 8 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LF st spf lo B shi errv mo bl bc qb VIS CV SV V8 HLOC B1P OWN RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK in *.

    assert (LOCW : (aapp st ST_SIZE /\ (forall LB0, aclient_write_ok H LB0 (st + 128, st + 136)) /\ afs_write_ok H LF (st + 128, st + 136))
                   \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)).
    { destruct HLOC as [(fv & INV & FV1 & FV2)|HR]; [left|right; exact HR].
      unfold ST_SIZE in FV2. pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      split; [eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE, ST_SIZE; lia]|].
      split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
      right; exists fv; split; [exact INV | cbn; lia]. }
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | unfold ST_SIZE in *; lia]. }
    assert (STP : st + 240 <= 0x7fff7000 \/ 0x10007fff8000 <= st).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, ST_SIZE in HA; lia | lia]. }
    assert (WV1 : wr_at asegs m (st + 128) 8).
    { pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. cbn. lia. }
    assert (GZV : gz m (st + 128) 16) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; Z.div_mod_to_equations; lia]).

    assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) [(st + 128, st + 136)]).
    { apply Forall_cons; [| apply Forall_nil].
      destruct LOCW as [(HA & HC & HF)|[HS1 HS2]].
      - split; [exact (HC LB)|]. split; [exact HF|].
        split; [eapply (aconst_ok_app st 240); [exact HA | cbn; lia | cbn; lia]|].
        eapply (stack0_ok_aapp st 240); [exact HA | cbn; lia | cbn; lia].
      - unfold ST_SIZE in HS2.
        split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
        split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn; lia | right; left; cbn; lia]|].
        apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 K) W1) as W1C.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 K)) W1) as W1F.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 (proj2 K))) W1) as W1A.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj2 (proj2 (proj2 K))) W1) as W1S.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct (Z.eq_dec bl 0) as [Bz | Bnz].
    -
      subst bl.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM3_N] (SCR [] [] []) DM3_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 128) 8 (ELit 0); KWr (SA (EVar 32) 128) (ELit 8);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM3_B m (seg_rom asegs) HR HK 200%nat [DM3_N] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 128, st + 136)] m M1).
      { subst M1. clear - Hlf STB SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI1 | exact ST1
                | subst tp; unfold errno_addr in ERR |- *; rewrite u64_of_Z in ERR |- * by (unfold ATP; lia);
                  eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]
                | eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]
                | eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]
                | eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]
                | eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]
                | unfold dv_LB; rewrite Z.eqb_refl; exact (lb_own_wmono _ _ _ OWN WM1)
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (xpres_of_munch H s LB spf _ _ m m M1); [exact HH | exact RH | exact MU1 | exact WM1 |];
                  apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]
                | lia | exact (wr_at_wmono _ _ _ _ WV1 WM1)].
    -
      destruct (B1P Bnz) as (INB & ADB & STC).
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 bl; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [AOPDEL2] (SCR [] [] []) DM3_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 128) 8 (EVar 34); KWord (SA (EVar 32) 136) 8 (EVar 35); KWr (SA (EVar 32) 128) (ELit 8);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47);
           KRange (EVar 35) 0 (2 ^ 44) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz bl)). }
        apply Forall_cons. { kword_cell CV 8%nat (C8 (wz bc)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM3_B m (seg_rom asegs) HR HK 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 128, st + 136)] m M1).
      { subst M1. clear - Hlf STB SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 9%bv G9.
      rewrite ?G1, ?G2, ?G8, ?G10, ?G11, ?G9 in HRe.
      assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H M1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF M1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]).
      assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]).
      assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB M1 (qb, bl, 8 * bc) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.
      assert (SB1 : SHAD M1 bl (shadow_of (8 * bc))).
      { eapply SHAD_transport; [exact (proj2 ADB) | exact MU1 | exact WM1 |]. rewrite shadow_of_length by lia. cbn.
        pose proof (sh_nsh_high bl (8 * bc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X. unfold AHI_LO in X.
        unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := qb) (A := bl) (n := 8 * bc) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (8 * bc)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SB1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; exact SP16 | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; unfold ST_SIZE in STC; lia
          | rewrite u64_of_Z by (unfold DM3_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even 972468 ltac:(lia) eq_refl) in VIS2.
      set (LB' := as_lb_remove H qb LB) in *.
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = M1 (wa a) /\ (wview asegs M1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ M1 (L3 qb LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (XP : xpres H LB' spf [(st + 128, st + 136)] m m2).
      { eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spf _ _ m2 m M1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]. }
        exact (xpres_of_apres H _ _ _ _ _ AP2). }
      assert (WO : wr_at asegs m2 (st + 128) 8).
      { eapply (apres_wr_at H); [exact AP2 | exact (wr_at_wmono _ _ _ _ WV1 WM1) |].
        destruct HLOC as [(fv & INV & FV1 & FV2)|(HS1 & HS2)]; [|left; lia].
        unfold ST_SIZE in FV2. pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
        pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
        right; right; right; right; left. unfold AFS_SIZE in *. lia. }
      eapply K; [exact VIS2 | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MI2 | exact ST2
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtM3b.

Definition DM2 : Z := 0xed6b4.  Definition DM2_B : Z := 0xed6fc.  Definition DM2_N : Z := 0xed73c.

Section DtM2h.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma dtm2h : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB LBr LBn : list block)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (ns : list (Z * list byte)),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM2) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 104) [C8 (wz (hdq ns))] -> SHAD m (st + 104) (repeat (b8 0) 1) -> st mod 8 = 0 ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    nodes_okG 32 LBn m ns -> Permutation LB (LBr ++ LBn) ->
    (ns <> [] -> st + ST_SIZE <= aceil) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> stack0 m lo shi -> spf <= shi ->
    (ns <> [] -> trace_ok (as_TR H) APC0_FREE [DTL2_DRET]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18 x19
                                 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DM2_B) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LBr LBn st spf lo B shi errv mo ns VIS CF SF V8 HLOC NO PERM STC RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC S0 SHI TRK K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    assert (GZF : gz m (st + 104) 8) by (intros i Hi; eapply sh0_of_SHAD0; [exact SF | cbn; Z.div_mod_to_equations; lia]).
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct ns as [|[q tl] ns'].
    -
      destruct LBn as [|b0 LBn]; [|cbn [nodes_okG] in NO; contradiction].
      rewrite app_nil_r in PERM.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM2_B] (SCR [] [] []) DM2 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 104) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CF 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM2 m (seg_rom asegs) HR HK 200%nat [DM2_B] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact PERM
                | apply apres_refl | exact RH | lia].
    -
      pose proof NO as NO0. cbn [nodes_okG] in NO0. destruct LBn as [|[[id q0] n0] LBn']; [contradiction|].
      destruct NO0 as (BA & BS & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS. subst q0 n0.
      assert (INQ : In (id, q, 32) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity).
      pose proof (ah_blocks H HH _ _ _ _ RH INQ) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Q0, Q16, Qn, QI, QC, QF, QAPP. unfold AIMG_TOP in QI.
      pose proof (STC ltac:(discriminate)) as STC'.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 q]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DTL2_LOOP] (SCR [] [] []) DM2 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 104) 8 (EVar 34);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { cbn [hdq] in CF. kword_cell CF 0%nat (C8 (wz q)). }
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM2 m (seg_rom asegs) HR HK 200%nat [DTL2_LOOP] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G10, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (dtl2_loop H HH HCF Q ns' q tl ((id, q, 32) :: LBn') LB LBr);
        [exact VIS1 | exact NO | exact PERM | exact RH | exact KR1 | exact AL0 | exact RA | exact SPB | exact ST | exact CE
        | unfold AFREE_STACK; lia | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC
        | left; rewrite u64_of_Z by lia; lia | exact (TRK ltac:(discriminate)) |].
      intros msF' mo' m' s' LBr' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' PL AP' RH' AC' AL'.
      eapply K; [exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP'] | exact MI' | exact ST' | exact ERR'
                | exact RA' | exact AC' | exact PL | exact AP' | exact RH' | lia].
  Qed.
End DtM2h.

Section DtM2b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma dtm2b : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (bl bc : Z) (qb : bptr),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM2_B) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 88) [C8 (wz bl); C8 (wz bc)] -> SHAD m (st + 88) (repeat (b8 0) 2) -> st mod 8 = 0 ->
    (st_live_frame LF st \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (bl <> 0 -> In (qb, bl, 8 * bc) LB /\ addressable m bl (8 * bc) /\ st + ST_SIZE <= aceil) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf <= shi ->
    (bl <> 0 -> trace_ok (as_TR H) APC0_FREE [DM2_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H)
            (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18 x19
                                 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DM2_N) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB qb bl) m' -> lb_own (dv_LB H LB qb bl) m' ->
       xpres H (dv_LB H LB qb bl) spf [(st + 88, st + 96)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 88) 8 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LF st spf lo B shi errv mo bl bc qb VIS CV SV V8 HLOC B1P OWN RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK in *.

    assert (LOCW : (aapp st ST_SIZE /\ (forall LB0, aclient_write_ok H LB0 (st + 88, st + 96)) /\ afs_write_ok H LF (st + 88, st + 96))
                   \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)).
    { destruct HLOC as [(fv & INV & FV1 & FV2)|HR]; [left|right; exact HR].
      unfold ST_SIZE in FV2. pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      split; [eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE, ST_SIZE; lia]|].
      split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
      right; exists fv; split; [exact INV | cbn; lia]. }
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | unfold ST_SIZE in *; lia]. }
    assert (STP : st + 240 <= 0x7fff7000 \/ 0x10007fff8000 <= st).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, ST_SIZE in HA; lia | lia]. }
    assert (WV1 : wr_at asegs m (st + 88) 8).
    { pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. cbn. lia. }
    assert (GZV : gz m (st + 88) 16) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; Z.div_mod_to_equations; lia]).

    assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) [(st + 88, st + 96)]).
    { apply Forall_cons; [| apply Forall_nil].
      destruct LOCW as [(HA & HC & HF)|[HS1 HS2]].
      - split; [exact (HC LB)|]. split; [exact HF|].
        split; [eapply (aconst_ok_app st 240); [exact HA | cbn; lia | cbn; lia]|].
        eapply (stack0_ok_aapp st 240); [exact HA | cbn; lia | cbn; lia].
      - unfold ST_SIZE in HS2.
        split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
        split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn; lia | right; left; cbn; lia]|].
        apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 K) W1) as W1C.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 K)) W1) as W1F.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 (proj2 K))) W1) as W1A.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj2 (proj2 (proj2 K))) W1) as W1S.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct (Z.eq_dec bl 0) as [Bz | Bnz].
    -
      subst bl.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM2_N] (SCR [] [] []) DM2_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 88) 8 (ELit 0); KWr (SA (EVar 32) 88) (ELit 8);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM2_B m (seg_rom asegs) HR HK 200%nat [DM2_N] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 88, st + 96)] m M1).
      { subst M1. clear - Hlf STB SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI1 | exact ST1
                | subst tp; unfold errno_addr in ERR |- *; rewrite u64_of_Z in ERR |- * by (unfold ATP; lia);
                  eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]
                | eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]
                | eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]
                | eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]
                | eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]
                | unfold dv_LB; rewrite Z.eqb_refl; exact (lb_own_wmono _ _ _ OWN WM1)
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (xpres_of_munch H s LB spf _ _ m m M1); [exact HH | exact RH | exact MU1 | exact WM1 |];
                  apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]
                | lia | exact (wr_at_wmono _ _ _ _ WV1 WM1)].
    -
      destruct (B1P Bnz) as (INB & ADB & STC).
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 bl; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [AOPDEL2] (SCR [] [] []) DM2_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 88) 8 (EVar 34); KWord (SA (EVar 32) 96) 8 (EVar 35); KWr (SA (EVar 32) 88) (ELit 8);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47);
           KRange (EVar 35) 0 (2 ^ 44) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz bl)). }
        apply Forall_cons. { kword_cell CV 8%nat (C8 (wz bc)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM2_B m (seg_rom asegs) HR HK 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 88, st + 96)] m M1).
      { subst M1. clear - Hlf STB SPR LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo spf) by (subst M1; apply stk_mem_denot; exact ST).
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 9%bv G9.
      rewrite ?G1, ?G2, ?G8, ?G10, ?G11, ?G9 in HRe.
      assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H M1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF M1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]).
      assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]).
      assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB M1 (qb, bl, 8 * bc) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.
      assert (SB1 : SHAD M1 bl (shadow_of (8 * bc))).
      { eapply SHAD_transport; [exact (proj2 ADB) | exact MU1 | exact WM1 |]. rewrite shadow_of_length by lia. cbn.
        pose proof (sh_nsh_high bl (8 * bc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X. unfold AHI_LO in X.
        unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := qb) (A := bl) (n := 8 * bc) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (8 * bc)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SB1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; exact SP16 | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; unfold ST_SIZE in STC; lia
          | rewrite u64_of_Z by (unfold DM2_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite (ret_pc_even 972604 ltac:(lia) eq_refl) in VIS2.
      set (LB' := as_lb_remove H qb LB) in *.
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = M1 (wa a) /\ (wview asegs M1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ M1 (L3 qb LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (XP : xpres H LB' spf [(st + 88, st + 96)] m m2).
      { eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' spf _ _ m2 m M1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]. }
        exact (xpres_of_apres H _ _ _ _ _ AP2). }
      assert (WO : wr_at asegs m2 (st + 88) 8).
      { eapply (apres_wr_at H); [exact AP2 | exact (wr_at_wmono _ _ _ _ WV1 WM1) |].
        destruct HLOC as [(fv & INV & FV1 & FV2)|(HS1 & HS2)]; [|left; lia].
        unfold ST_SIZE in FV2. pose proof (FR fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
        pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
        right; right; right; right; left. unfold AFS_SIZE in *. lia. }
      eapply K; [exact VIS2 | exact KR2 | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP2] | exact MI2 | exact ST2
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtM2b.

Definition DM1 : Z := 0xed73c.  Definition DM1_B : Z := 0xed784.

Section DtM1h.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma dtm1h : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB LBr LBn : list block)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (ns : list (Z * list byte)),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM1) fc None m (seg_rom asegs) ->
    rw_cells asegs m (st + 64) [C8 (wz (hdq ns))] -> SHAD m (st + 64) (repeat (b8 0) 1) -> st mod 8 = 0 ->
    (aapp st ST_SIZE \/ (spf <= st /\ st + ST_SIZE + 64 <= shi)) ->
    nodes_okG 24 LBn m ns -> Permutation LB (LBr ++ LBn) ->
    (ns <> [] -> st + ST_SIZE <= aceil) ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m -> stack0 m lo shi -> spf <= shi ->
    (ns <> [] -> trace_ok (as_TR H) APC0_FREE [DTL1_DRET]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (LBr' : list block)
            (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y28 y29 y30 y31 : word),
       as_VIS H s' msF' = MS (mkR y1 (Z_to_bv 64 spf) gp tp y5 y6 y7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) y10 y11 y12 y13 y14 y15 y16 y17 y18 x19
                                 x20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                             F (Z_to_bv 64 DM1_B) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> Permutation LBr' LBr -> apres H LBr' spf m m' -> as_RHEAP H s' LBr' m' -> as_AL H s' >= as_AL H s ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      F fc msF m s LB LBr LBn st spf lo B shi errv mo ns VIS CF SF V8 HLOC NO PERM STC RH KR AL0 RA SPB ST CE LO ERR MI TP SP16 SPR
      AC S0 SHI TRK K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    unfold AFREE_STACK, ST_SIZE in *.
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct HLOC as [HA|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | lia]. }
    assert (GZF : gz m (st + 64) 8) by (intros i Hi; eapply sh0_of_SHAD0; [exact SF | cbn; Z.div_mod_to_equations; lia]).
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct ns as [|[q tl] ns'].
    -
      destruct LBn as [|b0 LBn]; [|cbn [nodes_okG] in NO; contradiction].
      rewrite app_nil_r in PERM.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM1_B] (SCR [] [] []) DM1 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 64) 8 (ELit 0);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CF 0%nat (C8 (wz 0)). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM1 m (seg_rom asegs) HR HK 200%nat [DM1_B] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply K; [exact VIS1 | exact KR1 | exact MP1 | exact MI | exact ST | exact ERR | exact RA | exact AC | exact PERM
                | apply apres_refl | exact RH | lia].
    -
      pose proof NO as NO0. cbn [nodes_okG] in NO0. destruct LBn as [|[[id q0] n0] LBn']; [contradiction|].
      destruct NO0 as (BA & BS & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in BA, BS. subst q0 n0.
      assert (INQ : In (id, q, 24) LB) by (apply (Permutation_in _ (Permutation_sym PERM)); apply in_or_app; right; left; reflexivity).
      pose proof (ah_blocks H HH _ _ _ _ RH INQ) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
      cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Q0, Q16, Qn, QI, QC, QF, QAPP. unfold AIMG_TOP in QI.
      pose proof (STC ltac:(discriminate)) as STC'.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 q]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DTL1_LOOP] (SCR [] [] []) DM1 (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 64) 8 (EVar 34);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { cbn [hdq] in CF. kword_cell CF 0%nat (C8 (wz q)). }
        do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM1 m (seg_rom asegs) HR HK 200%nat [DTL1_LOOP] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB SPR LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10. rreg HR' 9%bv G9.
      rewrite ?G2, ?G8, ?G10, ?G9 in HRe.
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      eapply (dtl1_loop H HH HCF Q ns' q tl ((id, q, 24) :: LBn') LB LBr);
        [exact VIS1 | exact NO | exact PERM | exact RH | exact KR1 | exact AL0 | exact RA | exact SPB | exact ST | exact CE
        | unfold AFREE_STACK; lia | exact ERR | exact MI | exact TP | exact SP16 | exact SPR | exact AC
        | left; rewrite u64_of_Z by lia; lia | exact (TRK ltac:(discriminate)) |].
      intros msF' mo' m' s' LBr' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 VIS' KR' MP' MI' ST' ERR' RA' PL AP' RH' AC' AL'.
      eapply K; [exact VIS' | exact KR' | eapply (ah_mpres_trans H HH); [exact MP1 | exact MP'] | exact MI' | exact ST' | exact ERR'
                | exact RA' | exact AC' | exact PL | exact AP' | exact RH' | lia].
  Qed.
End DtM1h.

Definition DM1_RET : Z := 0xed7d8.

Definition DM1_N : Z := 0xed7c4.

Section DtM1e.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis HCF : forall n, as_Cf H n = 0.

  Lemma dtm1e : forall (Q : config -> Prop)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp : word)
      (ra s0 s1 s2 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (LF : list fframe)
      (st spf lo B shi : Z) (errv : word) (mo : Model) (bl bc : Z) (qb : bptr),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
                             x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 DM1_B) fc None m (seg_rom asegs) ->
    rw_cells asegs m (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs m (st + 48) [C8 (wz bl); C8 (wz bc)] -> SHAD m (st + 48) (repeat (b8 0) 2) -> st mod 8 = 0 ->
    (st_live_frame LF st \/ (spf + 48 <= st /\ st + ST_SIZE + 64 <= shi)) ->
    (bl <> 0 -> In (qb, bl, 8 * bc) LB /\ addressable m bl (8 * bc) /\ st + ST_SIZE <= aceil) ->
    lb_own LB m ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
    as_rauxv_ok H m B -> spf + 48 <= B ->
    stk asegs m lo (spf + 48) -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf -> spf + 48 <= 2 ^ 47 -> ACONST m -> as_RFS H LF m -> stack0 m lo shi -> spf + 48 <= shi ->
    (bl <> 0 -> trace_ok (as_TR H) APC0_FREE [DM1_N]) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       as_VIS H s' msF' = MS (mkR ra (Z_to_bv 64 (spf + 48)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 x20 x21 x22 x23
                                 x24 x25 x26 x27 t3 t4 t5 t6)
                             F (ret_pc ra) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo (spf + 48) -> rw_cells asegs m' (errno_addr tp) [C4 errv] -> as_rauxv_ok H m' B ->
       ACONST m' -> as_RFS H LF m' -> stack0 m' lo shi ->
       as_RHEAP H s' (dv_LB H LB qb bl) m' -> lb_own (dv_LB H LB qb bl) m' ->
       xpres H (dv_LB H LB qb bl) (spf + 48) [(st + 48, st + 56)] m m' -> as_AL H s' >= as_AL H s ->
       wr_at asegs m' (st + 48) 8 ->
       Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 gp tp
      ra s0 s1 s2 F fc msF m s LB LF st spf lo B shi errv mo bl bc qb VIS FR CV SV V8 HLOC B1P OWN RH KR AL0 RA SPB
      ST CE LO ERR MI TP SP16 SPL SPH AC RF S0 SHI TRC K.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (stack0_bounds m lo shi S0) as SB0. unfold AAPP_HI in SB0.
    pose proof (ah_RFS_range H HH _ _ RF) as [FSBOK FR0]. pose proof FSBOK as (FS1 & FS2 & FS3 & FS4). unfold AIMG_TOP in FS1.
    unfold AFREE_STACK in *.
    assert (LOCW : (aapp st ST_SIZE /\ (forall LB0, aclient_write_ok H LB0 (st + 48, st + 56)) /\ afs_write_ok H LF (st + 48, st + 56))
                   \/ (spf + 48 <= st /\ st + ST_SIZE + 64 <= shi)).
    { destruct HLOC as [(fv & INV & FV1 & FV2)|HR]; [left|right; exact HR].
      unfold ST_SIZE in FV2. pose proof (FR0 fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
      pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
      split; [eapply aapp_sub; [exact FS4 | unfold AFS_SIZE; lia | unfold AFS_SIZE, ST_SIZE; lia]|].
      split; [intros LB0; right; right; right; right; left; cbn; unfold AFS_SIZE in *; lia|].
      right; exists fv; split; [exact INV | cbn; lia]. }
    assert (STB : 0x6e8000 <= st /\ st + 240 <= 2 ^ 47).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold AIMG_TOP, AAPP_HI in *; lia | unfold ST_SIZE in *; lia]. }
    assert (STP : st + 240 <= 0x7fff7000 \/ 0x10007fff8000 <= st).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, ST_SIZE in HA; lia | lia]. }
    assert (STF : st + 240 <= spf \/ spf + 48 <= st).
    { destruct LOCW as [(HA & _)|[HS1 HS2]]; [pose proof (aapp_bounds st 240 HA ltac:(lia)) as (X1 & X2 & X3 & _); unfold ST_SIZE in *; lia | lia]. }
    assert (WV1 : wr_at asegs m (st + 48) 8).
    { pose proof (proj2 CV) as W. destruct W as (W1 & W2 & W). cbn [cells_size csize Z.of_nat] in W.
      split; [lia|]. split; [lia|]. intros i Hi. apply W. cbn. lia. }
    assert (GZV : gz m (st + 48) 16) by (intros i Hi; eapply sh0_of_SHAD0; [exact SV | cbn; Z.div_mod_to_equations; lia]).
    assert (W1 : Forall (fun iv : Z * Z => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) [(st + 48, st + 56)]).
    { apply Forall_cons; [| apply Forall_nil].
      destruct LOCW as [(HA & HC & HF)|[HS1 HS2]].
      - split; [exact (HC LB)|]. split; [exact HF|].
        split; [eapply (aconst_ok_app st 240); [exact HA | cbn; lia | cbn; lia]|].
        eapply (stack0_ok_aapp st 240); [exact HA | cbn; lia | cbn; lia].
      - unfold ST_SIZE in HS2.
        split; [left; cbn; lia|]. split; [left; cbn; unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AFS_SIZE in *; split; lia|].
        split; [apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; cbn; lia | right; left; cbn; lia]|].
        apply stack0_ok_app; cbn; unfold AHI_LO; lia. }
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 K) W1) as W1C.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 K)) W1) as W1F.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj1 (proj2 (proj2 K))) W1) as W1A.
    pose proof (Forall_impl _ (fun iv (K : aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) => proj2 (proj2 (proj2 K))) W1) as W1S.
    remember (mkR x1 (Z_to_bv 64 spf) gp tp x5 x6 x7 (Z_to_bv 64 st) (Z_to_bv 64 0x7fff8000) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
               x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    destruct (Z.eq_dec bl 0) as [Bz | Bnz].
    -
      subst bl.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; s2; s1; s0; ra]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [DM1_RET] (SCR [] [] []) DM1_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 48) 8 (ELit 0); KWr (SA (EVar 32) 48) (ELit 8);
           KWord (SA (EVar 33) 16) 8 (EVar 34); KWord (SA (EVar 33) 24) 8 (EVar 35); KWord (SA (EVar 33) 32) 8 (EVar 36);
           KWord (SA (EVar 33) 40) 8 (EVar 37);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 48); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz 0)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        apply Forall_cons. { kword_cell FR 0%nat (C8 s2). }
        apply Forall_cons. { kword_cell FR 8%nat (C8 s1). }
        apply Forall_cons. { kword_cell FR 16%nat (C8 s0). }
        apply Forall_cons. { kword_cell FR 24%nat (C8 ra). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM1_B m (seg_rom asegs) HR HK 200%nat [DM1_RET] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP STF SPL SPH LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 48, st + 56)] m M1).
      { subst M1. clear - Hlf STB SPL SPH LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo (spf + 48)) by (subst M1; apply stk_mem_denot; exact ST).
      assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
      pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
      readback HR' HF1 HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18.
      assert (G2' : getr R' 2 = Z_to_bv 64 (spf + 48)) by (rewrite G2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
      rewrite ?G1, G2', ?G8, ?G9, ?G18 in HRe.
      eapply (sr_evt H HH) with
        (P := fun ms => exists u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6,
                ms = MS (mkR ra (Z_to_bv 64 (spf + 48)) gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 x19 x20 x21 x22 x23
                             x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None M1 (seg_rom asegs));
        [exact KR | exact VIS | |].
      { eapply evt_of_msteps; [exact Hms|].
        rewrite mkst_MS, HRe. step. apply evt_done. do 15 eexists. reflexivity. }
      intros msF' mo' KR' MP' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & HP).
      eapply K; [exact HP | exact KR' | exact MP' | exact MI1 | exact ST1
                | subst tp; unfold errno_addr in ERR |- *; rewrite u64_of_Z in ERR |- * by (unfold ATP; lia);
                  eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]
                | eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]
                | eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]
                | eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]
                | eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]
                | unfold dv_LB; rewrite Z.eqb_refl; exact (lb_own_wmono _ _ _ OWN WM1)
                | unfold dv_LB; rewrite Z.eqb_refl; eapply (xpres_of_munch H s LB (spf + 48) _ _ m m M1); [exact HH | exact RH | exact MU1 | exact WM1 |];
                  apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]
                | lia | exact (wr_at_wmono _ _ _ _ WV1 WM1)].
    -
      destruct (B1P Bnz) as (INB & ADB & STC).
      pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
      pose proof ABR as (BB0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP in BI.
      pose (E := Eseed R [Z_to_bv 64 st; Z_to_bv 64 spf; Z_to_bv 64 bl; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id HTbAHStDtM_0) R).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
      assert (HK : know_ok asegs E m
         (kn_fix 20 [AOPDEL2] (SCR [] [] []) DM1_B (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 32) 48) 8 (EVar 34); KWord (SA (EVar 32) 56) 8 (EVar 35); KWr (SA (EVar 32) 48) (ELit 8);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 48); KRange (EVar 32) 0x6e8000 (2 ^ 47); KRange (EVar 34) 0x6e8000 (2 ^ 47);
           KRange (EVar 35) 0 (2 ^ 44) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell CV 0%nat (C8 (wz bl)). }
        apply Forall_cons. { kword_cell CV 8%nat (C8 (wz bc)). }
        apply Forall_cons.
        { eapply kwr_of_wr_at; [exact WV1 | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia
                               | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off]; cbn; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; cbn; lia]. }
        do 4 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R DM1_B m (seg_rom asegs) HR HK 200%nat [AOPDEL2] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E STB STP STF SPL SPH LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK.
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
      assert (MU1 : munch [(st + 48, st + 56)] m M1).
      { subst M1. clear - Hlf STB SPL SPH LO CE ACF1 ACF2. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
      assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
      assert (ST1 : stk asegs M1 lo (spf + 48)) by (subst M1; apply stk_mem_denot; exact ST).
      readback HR' (msteps_full asegs _ _ Hms ltac:(rewrite HR0; apply rfull_mkR)) HR0 HRe.
      rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
      rewrite ?G1, ?G2, ?G8, ?G9, ?G10, ?G11 in HRe.
      assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | exact W1C]).
      assert (RA1 : as_rauxv_ok H M1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | exact W1C]).
      assert (RF1 : as_RFS H LF M1) by (eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 | exact W1F]).
      assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | exact W1A]).
      assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact W1S]).
      assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
      { subst tp. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
        eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
      assert (FR1 : rw_cells asegs M1 (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FR | exact MU1 | exact WM1 | cbn; lia]).
      pose proof (lb_own_wmono _ _ _ OWN WM1) as OWN1.
      destruct (rw_cells_of_own LB M1 (qb, bl, 8 * bc) OWN1 INB ltac:(cbn; unfold AIMG_TOP; lia) ltac:(cbn; lia)) as (bs & CB1).
      cbn [blk_addr blk_size fst snd] in CB1.
      assert (SB1 : SHAD M1 bl (shadow_of (8 * bc))).
      { eapply SHAD_transport; [exact (proj2 ADB) | exact MU1 | exact WM1 |]. rewrite shadow_of_length by lia. cbn.
        pose proof (sh_nsh_high bl (8 * bc) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI; lia)) as X. unfold AHI_LO in X.
        unfold sh, ASHADOW_BASE in *. Z.div_mod_to_equations. lia. }
      pose proof (stk_split asegs M1 lo spf (spf + 48) ST1 ltac:(lia)) as [ST1a ST1b].
      eapply (sr_blk_eq H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms | exact HRe |].
      intros msF1 mo1 KR1 MP1 VIS1.
      clear HRe HR' G1 G2 G8 G9 G10 G11 Hms Hlf. try clear R'.
      eapply (ah_seq H HH).
      { eapply (ah_opdel2 H HH) with (LB := LB) (p := qb) (A := bl) (n := 8 * bc) (lo := lo) (B := B) (errv := errv) (CH := [])
                                     (sbs := shadow_of (8 * bc)) (bs := bs);
          [exact VIS1 | exact RH1 | exact KR1 | exact INB | rewrite HCF; exact AL0 | exact CB1 | exact SB1 | rewrite shadow_of_length by lia; reflexivity
          | exact RA1 | rewrite u64_of_Z by lia; lia | rewrite u64_of_Z by lia; exact ST1a
          | exact CE | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP
          | rewrite u64_of_Z by lia; clear - SP16; Z.div_mod_to_equations; lia | exact AC1
          | rewrite u64_of_Z by lia; apply (ah_chain_nil H HH); left; unfold ST_SIZE in STC; lia
          | rewrite u64_of_Z by (unfold DM1_N; lia); exact (TRC Bnz) | reflexivity ]. }
      intros [msF2 mo2] POST2.
      destruct POST2 as (t0'' & t1'' & t2'' & a0'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m2 & sA
                         & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
      cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
      rewrite u64_of_Z in ST2, AP2 by lia.
      rewrite ret_pc_even in VIS2 by (try unfold DM1_N; first [reflexivity | lia]).
      set (LB' := as_lb_remove H qb LB) in *.
      assert (FRM : forall a, 0 <= a < 2 ^ 64 -> (as_FSB H <= a < as_FSB H + AFS_SIZE \/ ATLS_PRIV_LO <= a < ATLS_PRIV_HI
                               \/ sh (as_FSB H) <= a < sh (as_FSB H + AFS_SIZE)) ->
                     m2 (wa a) = M1 (wa a) /\ (wview asegs M1 (wa a) <> None -> wview asegs m2 (wa a) <> None)).
      { intros a Ha Hr. apply (AP2 a Ha). unfold aclient_addr. destruct Hr as [Hr|[Hr|Hr]].
        - right; right; right; right; left; exact Hr.
        - right; left. unfold aimg_client, ATLS_PRIV_LO, ATLS_PRIV_HI, ATP in *. right; right; right; lia.
        - right; right; right; right; right; left; exact Hr. }
      assert (RF2 : as_RFS H LF m2) by (eapply (ah_RFS_ext H HH); [exact RF1 | exact FRM]).
      assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact S01 | apply Forall_nil]).
      assert (OWN2 : lb_own LB' m2).
      { pose proof (ah_lb_remove H HH) as (_ & _ & L3).
        eapply (lb_own_apres H); [exact (lb_own_incl LB _ M1 (L3 qb LB) OWN1) | exact AP2 | intros bb Hb; exact Hb]. }
      assert (ST2' : stk asegs m2 lo (spf + 48)).
      { eapply (stk_merge asegs m2 lo spf (spf + 48)); [exact ST2 | | lia].
        eapply (xpres_stk H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact ST1b | lia | apply Forall_nil]. }
      assert (FR2 : rw_cells asegs m2 (spf + 16) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (xpres_rw_cells H); [exact (xpres_of_apres H _ _ [] _ _ AP2) | exact FR1 |]. split; [left; lia | apply Forall_nil]. }
      assert (XP : xpres H LB' (spf + 48) [(st + 48, st + 56)] m m2).
      { eapply xpres_trans.
        { eapply (xpres_of_munch H sA LB' (spf + 48) _ _ m2 m M1); [exact HH | exact RH2 | exact MU1 | exact WM1 |].
          apply Forall_cons; [right; intros a Ha; cbn; left; cbn in Ha; lia | apply Forall_nil]. }
        eapply (xpres_weaken H); [exact (xpres_of_apres H _ _ _ _ _ AP2) | lia | intros bb Hb; exact Hb | intros a Ha; exact Ha]. }
      assert (WO : wr_at asegs m2 (st + 48) 8).
      { eapply (apres_wr_at H); [exact AP2 | exact (wr_at_wmono _ _ _ _ WV1 WM1) |].
        destruct HLOC as [(fv & INV & FV1 & FV2)|(HS1 & HS2)]; [|left; lia].
        unfold ST_SIZE in FV2. pose proof (FR0 fv INV) as (FK & FA1 & FA2 & _ & _). unfold AFS_HDR, AFS_SIZE in FA1, FA2.
        pose proof (fsz_pos (ff_class fv) ltac:(lia)) as FSZ.
        right; right; right; right; left. unfold AFS_SIZE in *. lia. }
      lazymatch type of VIS2 with _ = MS ?T _ _ _ _ _ _ => remember T as R2 eqn:HR2 end.
      pose (E2 := Eseed R2 [Z_to_bv 64 st; Z_to_bv 64 spf; s2; s1; s0; ra]).
      assert (HR2s : regs_ok E2 (srs sr_id HTbAHStDtM_0) R2).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; reflexivity. }
      assert (HK2 : know_ok asegs E2 m2
         (kn_fix 20 [DM1_RET] (SCR [] [] []) DM1_N (srs sr_id HTbAHStDtM_0)
         [ KWord (SA (EVar 33) 16) 8 (EVar 34); KWord (SA (EVar 33) 24) 8 (EVar 35); KWord (SA (EVar 33) 32) 8 (EVar 36);
           KWord (SA (EVar 33) 40) 8 (EVar 37);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47 - 48); KRange (EVar 32) 0x6e8000 (2 ^ 47) ] 40)).
      { kn_eval. unfold know_ok.
        apply Forall_cons. { kword_cell FR2 0%nat (C8 s2). }
        apply Forall_cons. { kword_cell FR2 8%nat (C8 s1). }
        apply Forall_cons. { kword_cell FR2 16%nat (C8 s0). }
        apply Forall_cons. { kword_cell FR2 24%nat (C8 ra). }
        do 2 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
        know_tac. }
      xrun_at (PropExec.mkFP F fc) asegs R2 DM1_N m2 (seg_rom asegs) HR2s HK2 200%nat [DM1_RET] (SCR [] [] []) 40%N.
      { split_scs. all: clear - E2 STB STP STF SPL SPH LO CE ACF1 ACF2 SB0. all: first [ sc_shdj | sc_dj ]. }
      clear HK2.
      assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      pose proof (msteps_full asegs _ _ Hms HF2) as HF2'. cbn [ms_regs] in HF2'.
      readback HR' HF2' HR2 HRe2.
      rreg HR' 1%bv J1. rreg HR' 2%bv J2. rreg HR' 8%bv J8. rreg HR' 9%bv J9. rreg HR' 18%bv J18.
      lazymatch type of J2 with getr ?RR 2 = _ =>
        assert (J2' : getr RR 2 = Z_to_bv 64 (spf + 48)) by (rewrite J2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia) end.
      rewrite ?J1, J2', ?J8, ?J9, ?J18 in HRe2.
      eapply (sr_evt H HH) with
        (P := fun ms => exists u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6,
                ms = MS (mkR ra (Z_to_bv 64 (spf + 48)) gp tp u0 u1 u2 s0 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 x19 x20 x21 x22 x23
                             x24 x25 x26 x27 u3 u4 u5 u6) F (ret_pc ra) fc None m2 (seg_rom asegs));
        [exact KR2 | exact VIS2 | |].
      { eapply evt_of_msteps; [exact Hms|].
        rewrite mkst_MS, HRe2. step. apply evt_done. do 15 eexists. reflexivity. }
      intros msF' mo' KR' MP' (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & HP).
      eapply K; [exact HP | exact KR' | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP']]
                | exact MI2 | exact ST2'
                | exact ERR2 | exact RA2 | exact AC2 | exact RF2 | exact S02
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact RH2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact OWN2
                | unfold dv_LB; rewrite (proj2 (Z.eqb_neq bl 0) Bnz); exact XP
                | rewrite HCF in AL2; lia | exact WO].
  Qed.
End DtM1e.
