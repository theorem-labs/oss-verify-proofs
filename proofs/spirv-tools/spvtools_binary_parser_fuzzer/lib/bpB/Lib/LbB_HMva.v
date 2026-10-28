(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition MVA : Z := 0xed828.
Definition MVA_LOOP : Z := 0xed8ac.
Definition MVA_DRET1 : Z := 0xed8d0.
Definition MVA_L2 : Z := 0xed8d8.

Section MvaLoop.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Fixpoint nodes_ok (LB : list block) (m : mem) (ns : list (Z * list byte)) : Prop :=
    match ns with
    | [] => True
    | (q, tl) :: ns' =>
        (exists id, In (id, q, 24) LB) /\ rw_cells asegs m q [C8 (Z_to_bv 64 (match ns' with [] => 0 | (q', _) :: _ => q' end)); CB 16 tl]
        /\ addressable m q 24 /\ nodes_ok LB m ns'
    end.

  Lemma mva_loop_step : forall (Q : config -> Prop)
      (x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block)
      (q : Z) (tl : list byte) (ns : list (Z * list byte)) (spf lo B : Z) (errv : word) (mo : Model) (id : bptr),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                             (Z_to_bv 64 0x7fff8000) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 MVA_LOOP) fc None m (seg_rom asegs) ->
    In (id, q, 24) LB ->
    rw_cells asegs m q [C8 (Z_to_bv 64 (match ns with [] => 0 | (q', _) :: _ => q' end)); CB 16 tl] ->
    addressable m q 24 ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_Cf H 24 <= as_AL H s ->
    as_rauxv_ok H m B -> spf <= B ->
    stk asegs m lo spf -> aceil <= lo -> lo <= spf - AFREE_STACK ->
    rw_cells asegs m (errno_addr x4) [C4 errv] -> mem_inv asegs m -> x4 = Z_to_bv 64 ATP ->
    spf mod 16 = 0 -> 2 ^ 45 <= spf <= 2 ^ 47 -> ACONST m ->
    (bv_unsigned x8 <= aceil \/ bv_unsigned x8 mod 8 <> 0) ->
    trace_ok (as_TR H) APC0_FREE [MVA_DRET1] ->
    (match ns with [] => True | (q', _) :: _ => 0x6e8000 <= q' < 2 ^ 47 end) ->
    (forall (msF' : machine_state) (mo' : Model) (m' : mem) (s' : as_St H) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       as_VIS H s' msF' = MS (mkR (Z_to_bv 64 MVA_DRET1) (Z_to_bv 64 spf) x3 x4 t0 t1 t2 x8 x9
                                 (Z_to_bv 64 (match ns with [] => 0 | (q', _) :: _ => q' end)) a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
                                 (Z_to_bv 64 0x7fff8000) x22 x23 x24
                                 (Z_to_bv 64 (match ns with [] => 0 | (q', _) :: _ => q' end)) x26 x27 t3 t4 t5 t6)
                             F (Z_to_bv 64 (match ns with [] => MVA_L2 | _ => MVA_LOOP end)) fc None m' (seg_rom asegs) ->
       as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       mem_inv asegs m' -> stk asegs m' lo spf -> rw_cells asegs m' (errno_addr x4) [C4 errv] -> as_rauxv_ok H m' B ->
       apres H (as_lb_remove H id LB) spf m m' -> as_RHEAP H s' (as_lb_remove H id LB) m' -> ACONST m' ->
       as_AL H s' >= as_AL H s - as_Cf H 24 ->
       as_SR H Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x3 x4 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      F fc msF m s LB q tl ns spf lo B errv mo id VIS HIN CQ ADQ RH KR CF RA SPB ST CE LO ERR MI TP SP16 SPR AC S0LOW TRK NXR K.
    set (nxt := match ns with [] => 0 | (q', _) :: _ => q' end) in *.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (ah_blocks H HH _ _ _ (id, q, 24) RH HIN) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP).
    unfold blk_addr, blk_size in Q0, Q16, Qn, QI, QC, QF, QAPP. cbn [fst snd] in Q0, Q16, Qn, QI, QC, QF, QAPP.
    assert (GZQ : gz m q 24) by (intros i Hi; eapply sh0_of_addressable; [exact ADQ | change (8 * (24 / 8)) with 24; lia]).
    remember (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 x9 (Z_to_bv 64 q) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                  (Z_to_bv 64 0x7fff8000) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.

    pose (E := Eseed R [Z_to_bv 64 q; Z_to_bv 64 spf; Z_to_bv 64 nxt]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (21%bv, ELit 0x7fff8000)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AOPDEL2] (SCR [] [] []) MVA_LOOP (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (21%bv, ELit 0x7fff8000)])
         [ KWord (SA (EVar 32) 0) 8 (EVar 34);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KAlign (EVar 32) 8 ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m q _ 0%nat (C8 (Z_to_bv 64 nxt))); [exact CQ | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off Z.of_nat]; lia | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. unfold AIMG_TOP in QI. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. split; [lia|]. destruct (proj1 (Z.mod_divide q 16 ltac:(discriminate)) Q16) as [k8 Hk8]. apply (proj2 (Z.mod_divide q 8 ltac:(discriminate))). exists (2 * k8). rewrite Hk8. ring. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R MVA_LOOP m (seg_rom asegs) HR HK 40%nat [AOPDEL2] (SCR [] [] []) 40%N.
    { split_scs; try sc_auto1; try sc_shdj; try sc_dj. }
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 21%bv G21. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 25%bv G25.
    assert (GK : forall r x, In r [3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 26; 27]%bv -> getr R r = x -> getr R' r = x).
    { intros r x Hr Hx. rewrite <- Hx.
      eapply (syms_id_sound R _ _ R' [3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 26; 27]%bv HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]. }
    assert (G4 : getr R' 4 = x4) by (apply GK; [inb | subst R; reflexivity]).
    assert (G8 : getr R' 8 = x8) by (apply GK; [inb | subst R; reflexivity]).
    eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.

    eapply (ah_seq H HH).
    { eapply (ah_opdel2 H HH) with (p := id) (A := q) (n := 24) (LB := LB) (lo := lo) (B := B) (errv := errv) (CH := [])
        (sbs := shadow_of 24);
        [ exact VIS1 | exact RH | exact KR1 | exact HIN | exact CF | exact (rw_cells_to_CB m q _ CQ) | exact (proj2 ADQ) | reflexivity
        | exact RA | rewrite G2, u64_of_Z by lia; lia | rewrite G2, u64_of_Z by lia; exact ST | exact CE | rewrite G2, u64_of_Z by lia; exact LO
        | rewrite G4; exact ERR | exact MI | rewrite G4; exact TP | rewrite G2, u64_of_Z by lia; exact SP16 | exact AC
        | rewrite G8; apply (ah_chain_nil H HH); exact S0LOW
        | rewrite G1; cbn [map]; rewrite u64_of_Z by (unfold MVA_DRET1; lia); exact TRK
        | exact G10 ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1, (ret_pc_even 973008 ltac:(lia) eq_refl) in VIS2.
    rewrite G2, u64_of_Z in ST2, AP2 by lia. rewrite G4 in ERR2.

    lazymatch type of VIS2 with _ = MS ?T _ _ _ _ _ _ => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 nxt]).
    assert (HRb : regs_ok E2 (srs sr_id [(25%bv, EVar 32)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; exact G25. }
    destruct ns as [|[q' tl'] ns'].
    -
      assert (HKb : know_ok asegs E2 m2 [KRange (EVar 32) 0 0]).
      { unfold know_ok. apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. evs. subst nxt. rewrite u64_of_Z by lia. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R2 973008 m2 (seg_rom asegs) HRb HKb 10%nat [MVA_LOOP; MVA_L2] (SCR [] [] []) 40%N.
      { split_scs; try sc_auto1. }
      assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      pose proof (msteps_full asegs _ _ Hms0 HF2) as HF3. cbn [ms_regs] in HF3.
      readback HR'0 HF3 HR2 HRe3.
      rreg HR'0 10%bv J10. rreg HR'0 25%bv J25.
      rewrite ?J10, ?J25, ?G1, ?G2, ?G4, ?G8, ?G25,
        ?(GK 3%bv x3 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 9%bv x9 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 18%bv x18 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 19%bv x19 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 20%bv x20 ltac:(inb) ltac:(subst R; reflexivity)), ?G21,
        ?(GK 22%bv x22 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 23%bv x23 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 24%bv x24 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 26%bv x26 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 27%bv x27 ltac:(inb) ltac:(subst R; reflexivity)) in HRe3.
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | rewrite HR2; apply rfull_mkR | exact Hms0 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      apply (K msF3 mo3 m2 s' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'); try assumption.
      + rewrite VIS3, HRe3. reflexivity.
      + eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
    -
      assert (HKb : know_ok asegs E2 m2 [KRange (EVar 32) 0x6e8000 (2 ^ 47)]).
      { unfold know_ok. apply Forall_cons; [|apply Forall_nil]. cbn [kentry_ok]. evs. subst nxt. rewrite u64_of_Z by lia. lia. }
      xrun_at (PropExec.mkFP F fc) asegs R2 973008 m2 (seg_rom asegs) HRb HKb 10%nat [MVA_LOOP; MVA_L2] (SCR [] [] []) 40%N.
      { split_scs; try sc_auto1. }
      assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
      pose proof (msteps_full asegs _ _ Hms0 HF2) as HF3. cbn [ms_regs] in HF3.
      readback HR'0 HF3 HR2 HRe3.
      rreg HR'0 10%bv J10. rreg HR'0 25%bv J25.
      rewrite ?J10, ?J25, ?G1, ?G2, ?G4, ?G8, ?G25,
        ?(GK 3%bv x3 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 9%bv x9 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 18%bv x18 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 19%bv x19 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 20%bv x20 ltac:(inb) ltac:(subst R; reflexivity)), ?G21,
        ?(GK 22%bv x22 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 23%bv x23 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 24%bv x24 ltac:(inb) ltac:(subst R; reflexivity)), ?(GK 26%bv x26 ltac:(inb) ltac:(subst R; reflexivity)),
        ?(GK 27%bv x27 ltac:(inb) ltac:(subst R; reflexivity)) in HRe3.
      eapply (sr_blk H HH); [exact KR2 | exact VIS2 | rewrite HR2; apply rfull_mkR | exact Hms0 |].
      intros msF3 mo3 KR3 MP3 VIS3.
      apply (K msF3 mo3 m2 s' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'); try assumption.
      + rewrite VIS3, HRe3. reflexivity.
      + eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]].
  Qed.
End MvaLoop.

Definition MVA_END : Z := 0xedb10.
Definition MVA_RET : Z := 0xedb40.

Definition mva_frame (m : mem) (spf : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) : Prop :=
  rw_cells asegs m (spf + 8) [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Ltac kframe FR k :=
  eapply (kword_of_rw_cells asegs _ _ _ _ k); [exact FR | reflexivity | reflexivity | lia
    | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | reflexivity].

Section MvaEnd.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma mva_end : forall (Q : config -> Prop)
      (x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (mo : Model) (spf : Z)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word),
    as_VIS H s msF = MS (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                             x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 MVA_END) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) ->
    mva_frame m spf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ->
    2 ^ 45 <= spf -> spf + 96 <= 2 ^ 47 ->
    (forall (msF' : machine_state) (mo' : Model),
       as_AKREL H s (mkCfg msF' mo') -> as_MPRES H mo mo' ->
       as_VIS H s msF' = MS (mkR ra (Z_to_bv 64 (spf + 96)) x3 x4 x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                                 s6 s7 s8 s9 x26 x27 x28 x29 x30 x31)
                            F (ret_pc ra) fc None m (seg_rom asegs) ->
       Q (mkCfg msF' mo')) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros Q x1 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      F fc msF m s mo spf ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 VIS KR FR SPL SPH K.
    unfold mva_frame in FR.
    remember (mkR x1 (Z_to_bv 64 spf) x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                  x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 spf; ra; s0; s1; s2; s3; s4; s5; s6; s7; s8; s9]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HK : know_ok asegs E m
       [ KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 96);
         KWord (SA (EVar 32) 88) 8 (EVar 33); KWord (SA (EVar 32) 80) 8 (EVar 34); KWord (SA (EVar 32) 72) 8 (EVar 35);
         KWord (SA (EVar 32) 64) 8 (EVar 36); KWord (SA (EVar 32) 56) 8 (EVar 37); KWord (SA (EVar 32) 48) 8 (EVar 38);
         KWord (SA (EVar 32) 40) 8 (EVar 39); KWord (SA (EVar 32) 32) 8 (EVar 40); KWord (SA (EVar 32) 24) 8 (EVar 41);
         KWord (SA (EVar 32) 16) 8 (EVar 42); KWord (SA (EVar 32) 8) 8 (EVar 43) ]).
    { unfold know_ok.
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons; [kframe FR 80%nat|]. apply Forall_cons; [kframe FR 72%nat|]. apply Forall_cons; [kframe FR 64%nat|].
      apply Forall_cons; [kframe FR 56%nat|]. apply Forall_cons; [kframe FR 48%nat|]. apply Forall_cons; [kframe FR 40%nat|].
      apply Forall_cons; [kframe FR 32%nat|]. apply Forall_cons; [kframe FR 24%nat|]. apply Forall_cons; [kframe FR 16%nat|].
      apply Forall_cons; [kframe FR 8%nat|]. apply Forall_cons; [kframe FR 0%nat|]. apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R MVA_END m (seg_rom asegs) HR HK 20%nat [MVA_RET] (SCR [] [] []) 40%N.
    { split_scs; try sc_auto1. }
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 18%bv G18. rreg HR' 19%bv G19.
    rreg HR' 20%bv G20. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 23%bv G23. rreg HR' 24%bv G24. rreg HR' 25%bv G25.
    assert (G2' : getr R' 2 = Z_to_bv 64 (spf + 96)) by (rewrite G2; rewrite ?w_addm, ?w_add, ?v_addi_Z by lia; try reflexivity; f_equal; lia).
    rewrite G1, G2', G8, G9, G18, G19, G20, G21, G22, G23, G24, G25 in HRe.
    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra (Z_to_bv 64 (spf + 96)) x3 x4 x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5
                                   s6 s7 s8 s9 x26 x27 x28 x29 x30 x31) F (ret_pc ra) fc None m (seg_rom asegs));
      [exact KR | exact VIS | |].
    { eapply evt_of_msteps; [exact Hms|].
      rewrite mkst_MS, HRe. step. apply evt_done. reflexivity. }
    intros msF' mo' KR' MP' HP. cbv beta in HP. apply K; assumption.
  Qed.
End MvaEnd.
