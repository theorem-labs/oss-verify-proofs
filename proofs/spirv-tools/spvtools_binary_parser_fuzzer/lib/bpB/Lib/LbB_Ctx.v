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

Definition CTX_CREATE : Z := 0xe9f48.
Definition CTX_NEW_RET : Z := 0xe9f8c.
Definition CTX_RET : Z := 0xe9fd0.
Definition CTX_DESTROY : Z := 0xea008.
Definition CTX_SZ : Z := 64.

Section Ctx.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Definition ctx_create_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (evz lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (A : Z) j1 j2 (p : bptr) (s' : as_St H),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ apres H LB (bv_unsigned sp) m m'
      /\ ablock_range H A CTX_SZ /\ as_RHEAP H s' ((p, A, CTX_SZ) :: LB) m'
      /\ rw_cells asegs m' A [C4 (wz evz); CB 44 j1; C8 (wz 0); CB 8 j2]
      /\ addressable m' A CTX_SZ
      /\ ACONST m'
      /\ as_AL H s' >= as_AL H s - as_Cm H CTX_SZ.

  Lemma ctx_create_sr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (evz lo B : Z) (errv : word) (mo : Model),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 CTX_CREATE) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 evz -> 0 <= evz < 19 ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_alloc_ok H s LB CTX_SZ -> as_Cm H CTX_SZ <= as_AL H s ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32 - AOPNEW_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 -> bv_unsigned ra mod 2 = 0 -> ACONST m ->
    as_SR H (ctx_create_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB evz lo B m mo) (mkCfg msF mo).
  Proof.
    intros until mo. intros VIS Ha0 Henv RH KR AOK CM RA SPB ST CE LO ERR MI TP SP16 SP47 RA2 AC.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AOPNEW_STACK, AMALLOC_STACK in LO.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.

    pose (E := Eseed R [Z_to_bv 64 evz; Z_to_bv 64 spz; ra]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (HK : know_ok asegs E m
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWr (SA (EVar 33) (-32)) (ELit 32);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47);
         KRange (EVar 32) 0 18 ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R CTX_CREATE m (seg_rom asegs) HR HK 40%nat [AOPNEW] (SCR [] [] []) 40%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(spz - 32, spz)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WOK : aclient_write_ok H LB (spz - 32, spz) /\ aconst_ok (spz - 32, spz)).
    { split; [left; cbn; lia|].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj1 WOK) | apply Forall_nil]]).
    assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj2 WOK) | apply Forall_nil]]).
    assert (RA1 : as_rauxv_ok H M1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj1 WOK) | apply Forall_nil]]).
    assert (ERR1 : rw_cells asegs M1 (bv_unsigned tp + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. lia. }
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 4%bv G4. rreg HR' 10%bv G10.
    eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    assert (G2' : getr R' 2 = Z_to_bv 64 (spz - 32)).
    { rewrite G2. apply w_addm; lia. }
    assert (G4' : getr R' 4 = tp) by (rewrite G4; subst R; reflexivity).

    eapply (ah_seq H HH).
    { eapply (ah_opnew H HH) with (n := CTX_SZ) (LB := LB) (lo := lo) (B := B) (errv := errv); [exact VIS1 | exact RH1 | exact KR1 | exact AOK | exact CM | exact RA1
      | rewrite G2', u64_of_Z by lia; lia
      | rewrite G2', u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo (spz - 32) spz ST1 ltac:(lia)))
      | exact CE | rewrite G2', u64_of_Z by lia; unfold AOPNEW_STACK, AMALLOC_STACK; lia
      | rewrite G4'; exact ERR1 | exact MI1 | rewrite G4'; exact TP | rewrite G2', u64_of_Z by lia; Z.div_mod_to_equations; lia
      | exact AC1 | exact G10 | unfold CTX_SZ; lia ]. }
    intros c2 POST. destruct c2 as [msF2 mo2].
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & errv2 & A & junk & p & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2' & AP2 & ABR & RH2 & CB2 & ADDR & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite G1 in VIS2. rewrite (ret_pc_even 958348 ltac:(lia) eq_refl) in VIS2.

    rreg HR' 8%bv G8. rreg HR' 9%bv G9.

    assert (GK : forall r x, In r [3; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = x -> getr R' r = x).
    { intros r x Hr Hx. rewrite <- Hx. eapply (syms_id_sound R _ _ R' [3; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]. }

    assert (WS : forall k, 8 <= k <= 32 -> wr_at asegs m (spz - k) 8).
    { intros k Hk. pose proof (wr_at_of_stk asegs m lo spz ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (spz - k + i) with (lo + (spz - k - lo + i)) by lia. apply W. lia. }
    assert (CRA : rw_cells asegs M1 (spz - 8) [C8 ra]).
    { subst M1. eapply (rw_cells_mem_denot_w _ m [_; _] _ 8 (EVar 34) []); [exact Hlf | | | exact (WS 8 ltac:(lia)) | reflexivity | exact I | reflexivity].
      - repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia|]). apply Forall_nil.
      - unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia. }
    assert (CS0 : rw_cells asegs M1 (spz - 16) [C8 s0]).
    { subst M1. eapply (rw_cells_mem_denot_w _ m [_] _ 8 (EVar 8) [_]); [exact Hlf | | | exact (WS 16 ltac:(lia)) | reflexivity | exact I | subst R; reflexivity].
      - repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [a_off]; lia|]). apply Forall_nil.
      - unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia. }
    assert (CS1 : rw_cells asegs M1 (spz - 24) [C8 s1]).
    { subst M1. eapply (rw_cells_mem_denot_w _ m [] _ 8 (EVar 9) [_; _]); [exact Hlf | apply Forall_nil | | exact (WS 24 ltac:(lia)) | reflexivity | exact I | subst R; reflexivity].
      unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia. }
    rewrite G2', u64_of_Z in AP2, ST2 by lia. rewrite G4' in ERR2.
    assert (CRA2 : rw_cells asegs m2 (spz - 8) [C8 ra]) by (eapply apres_rw_cells; [exact AP2 | exact CRA | left; lia]).
    assert (CS02 : rw_cells asegs m2 (spz - 16) [C8 s0]) by (eapply apres_rw_cells; [exact AP2 | exact CS0 | left; lia]).
    assert (CS12 : rw_cells asegs m2 (spz - 24) [C8 s1]) by (eapply apres_rw_cells; [exact AP2 | exact CS1 | left; lia]).
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP, CTX_SZ in BI, BC, BF, BAPP, Bn.

    lazymatch type of VIS2 with _ = MS ?T _ _ _ _ _ _ => remember T as R2 eqn:HR2 end.
    pose (E2 := Eseed R2 [Z_to_bv 64 A; Z_to_bv 64 (spz - 32); ra; s0; s1; Z_to_bv 64 evz; Z_to_bv 64 2147450880]).
    assert (HRb : regs_ok E2 (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 37); (9%bv, ELit 2147450880)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R2; evs; try reflexivity; [exact G2' | exact G8 | exact G9]. }
    assert (GZA : gz m2 A 64) by (intros i Hi; eapply sh0_of_addressable; [exact ADDR | change (8 * (CTX_SZ / 8)) with 64; lia]).
    assert (WA : wr_at asegs m2 A 64) by exact (proj2 CB2).
    assert (HKb : know_ok asegs E2 m2
       (kn_fix 20 [CTX_RET] (SCR [] [] []) CTX_NEW_RET (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (8%bv, EVar 37); (9%bv, ELit 2147450880)])
         [ KWord (SA (EVar 33) 24) 8 (EVar 34); KWord (SA (EVar 33) 16) 8 (EVar 35); KWord (SA (EVar 33) 8) 8 (EVar 36);
           KWr (SA (EVar 32) 0) (ELit 64);
           KRange (EVar 33) (2 ^ 45) (2 ^ 47); KRange (EVar 32) 0x6e8000 (2 ^ 47); KAlign (EVar 32) 16;
           KDisj (SA (EVar 32) 0) (ELit 64) (SA (EVar 33) 0) (ELit 32) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E2 m2 (spz - 8) _ 0%nat (C8 ra)); [exact CRA2 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off Z.of_nat]; lia | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E2 m2 (spz - 16) _ 0%nat (C8 s0)); [exact CS02 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off Z.of_nat]; lia | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs E2 m2 (spz - 24) _ 0%nat (C8 s1)); [exact CS12 | reflexivity | reflexivity | lia | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off Z.of_nat]; lia | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons. { eapply kwr_of_wr_at; [exact WA | unfold estart; evs; rewrite u64_of_Z by lia; lia
                             | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. unfold CTX_SZ in *. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. split; [lia | exact B16]. }
      apply Forall_cons. { cbn [kentry_ok]. unfold estart, elenZ. evs. rewrite !u64_of_Z by lia. cbn [a_off]. unfold CTX_SZ in *. lia. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 CTX_NEW_RET m2 (seg_rom asegs) HRb HKb 40%nat [CTX_RET] (SCR [] [] []) 40%N.
    { unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in BAPP. split_scs; sc_shdj. }
    lazymatch type of Hlf0 with log_flat _ ?lg =>
      lazymatch type of Hms0 with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E2 m2 lg) in Hms0; set (M3 := mem_denot E2 m2 lg) in Hms0 end end.

    assert (MU3 : munch [(A, A + 4); (A + 48, A + 56)] m2 M3).
    { subst M3. apply munch_mem_denot; [exact Hlf0|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|].
      apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ a_off]; lia|].
      apply Forall_nil. }
    assert (WM3 : wmono asegs m2 M3) by (subst M3; apply wmono_mem_denot).
    assert (MI3 : mem_inv asegs M3) by exact (msteps_mem_inv asegs _ _ Hms0 MI2).
    assert (W3OK : Forall (aclient_write_ok H ((p, A, CTX_SZ) :: LB)) [(A, A + 4); (A + 48, A + 56)]).
    { do 2 (apply Forall_cons; [right; right; left; exists (p, A, CTX_SZ); (split; [left; reflexivity|]); cbn; unfold CTX_SZ; lia|]). apply Forall_nil. }
    assert (W3C : Forall aconst_ok [(A, A + 4); (A + 48, A + 56)]).
    { do 2 (apply Forall_cons; [eapply (aconst_ok_app A 64); [exact BAPP | cbn; lia | cbn; lia]|]). apply Forall_nil. }
    assert (RH3 : as_RHEAP H s' ((p, A, CTX_SZ) :: LB) M3) by (eapply (ah_RHEAP_frame H HH); [exact RH2 | exact MU3 | exact WM3 | exact W3OK]).
    assert (AC3 : ACONST M3) by (eapply ACONST_frame; [exact AC2 | exact MU3 | exact WM3 | exact W3C]).
    assert (RA3 : as_rauxv_ok H M3 B) by (eapply (ah_rauxv_frame H HH); [exact RA2' | exact MU3 | exact WM3 | exact W3OK]).
    assert (ERR3 : rw_cells asegs M3 (bv_unsigned tp + -164) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR2 | exact MU3 | exact WM3 |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. lia. }
    assert (WH3 : wins_hi [(A, A + 4); (A + 48, A + 56)]).
    { unfold wins_hi. pose proof BAPP as BAPP'. unfold aapp, aapp_lo, aapp_hi in BAPP'.
      do 2 (apply Forall_cons; [cbn [fst snd]; destruct BAPP' as [[X Y]|[X Y]]; [left | right]; unfold AIMG_TOP, ALOWSH_LO, AHI_LO in *; lia|]). apply Forall_nil. }
    assert (ADDR3 : addressable M3 A CTX_SZ) by (eapply addressable_transport_hi; [exact ADDR | exact MU3 | exact WM3 | unfold AAPP_HI, CTX_SZ; lia | exact WH3]).
    assert (ST3 : stk asegs M3 lo spz).
    { apply (stk_merge asegs M3 lo (spz - 32) spz); [subst M3; apply stk_mem_denot; exact ST2 | | lia].
      subst M3. apply stk_mem_denot. eapply apres_stk; [exact AP2 | exact (proj2 (stk_split asegs M1 lo (spz - 32) spz ST1 ltac:(lia))) | lia]. }

    change (Z.to_nat CTX_SZ) with 64%nat in CB2.
    pose proof (rw_cells_CB_split asegs m2 A 64 4 junk CB2 ltac:(lia)) as [C0 C1r].
    pose proof (rw_cells_CB_split asegs m2 (A + 4) 60 44 _ C1r ltac:(lia)) as [C1 C2r].
    pose proof (rw_cells_CB_split asegs m2 (A + 4 + Z.of_nat 44) 16 8 _ C2r ltac:(lia)) as [C2 C3].
    change (Z.of_nat 44) with 44 in C2, C3. change (Z.of_nat 8) with 8 in C3.
    assert (CE4 : rw_cells asegs M3 A [C4 (wz evz)]).
    { subst M3. eapply (rw_cells_mem_denot_w _ m2 [_] _ 4 (EVar 37) [] A (C4 (wz evz))); [exact Hlf0 | | | | reflexivity | exact I | reflexivity].
      - apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite !u64_of_Z by lia; cbn [a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]. apply Forall_nil.
      - unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia.
      - exact (proj2 C0). }
    assert (C48 : rw_cells asegs M3 (A + 48) [C8 (wz 0)]).
    { subst M3. eapply (rw_cells_mem_denot_w _ m2 [] _ 8 (ELit 0) [_] (A + 48) (C8 (wz 0))); [exact Hlf0 | apply Forall_nil | | | reflexivity | exact I | reflexivity].
      - unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; lia.
      - replace (A + 48) with (A + 4 + 44) by lia. exact (proj2 C2). }
    assert (C1' : rw_cells asegs M3 (A + 4) [CB 44 (firstn 44 (skipn 4 junk))]).
    { eapply rw_cells_transport; [exact C1 | exact MU3 | exact WM3 | cbn; lia]. }
    assert (C3' : rw_cells asegs M3 (A + 56) [CB 8 (skipn 8 (skipn 44 (skipn 4 junk)))]).
    { replace (A + 56) with (A + 4 + 44 + 8) by lia. eapply rw_cells_transport; [exact C3 | exact MU3 | exact WM3 | cbn; lia]. }
    assert (CALL : rw_cells asegs M3 A [C4 (wz evz); CB 44 (firstn 44 (skipn 4 junk)); C8 (wz 0); CB 8 (skipn 8 (skipn 44 (skipn 4 junk)))]).
    { change [C4 (wz evz); CB 44 (firstn 44 (skipn 4 junk)); C8 (wz 0); CB 8 (skipn 8 (skipn 44 (skipn 4 junk)))]
        with ([C4 (wz evz)] ++ ([CB 44 (firstn 44 (skipn 4 junk))] ++ ([C8 (wz 0)] ++ [CB 8 (skipn 8 (skipn 44 (skipn 4 junk)))]))).
      apply rw_cells_app. split; [exact CE4|]. cbn [cells_size csize]. change (Z.of_nat (4 + 0)) with 4.
      apply rw_cells_app. split; [exact C1'|]. cbn [cells_size csize]. change (Z.of_nat (44 + 0)) with 44.
      apply rw_cells_app. split; [replace (A + 4 + 44) with (A + 48) by lia; exact C48|]. cbn [cells_size csize]. change (Z.of_nat (8 + 0)) with 8.
      replace (A + 4 + 44 + 8) with (A + 56) by lia. exact C3'. }

    assert (NI : ~ In p (map blk_id LB)).
    { pose proof (ah_nodup H HH _ _ _ RH3) as ND. cbn [map] in ND. apply NoDup_cons_iff in ND. exact (proj1 ND). }
    assert (APall : apres H LB spz m M3).
    { eapply (apres_trans H); [eapply (apres_trans H) |].
      - eapply (apres_of_munch H HH s LB spz [(spz - 32, spz)] m m M1); [exact RH | exact MU1 | exact WM1 |].
        apply Forall_cons; [cbn; lia | apply Forall_nil].
      - eapply (apres_weaken H); [exact AP2 | lia | intros b Hb; exact Hb].
      - eapply (apres_new_block H HH s' LB p A CTX_SZ spz m2 M3); [exact RH2 | exact NI | exact MU3 | exact WM3 | | unfold CTX_SZ; lia].
        do 2 (apply Forall_cons; [cbn; unfold CTX_SZ; lia|]). apply Forall_nil. }

    rreg HR'0 1%bv H1. rreg HR'0 2%bv H2. rreg HR'0 8%bv H8. rreg HR'0 9%bv H9. rreg HR'0 10%bv H10.
    assert (H2' : getr R'0 2 = sp) by (rewrite H2, Hsp, w_add by lia; f_equal; lia).
    assert (GG3 : getr R' 3 = gp) by (apply GK; [inb | subst R; reflexivity]).
    assert (HF2 : rfull R2) by (rewrite HR2; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms0 HF2) as HF3. cbn [ms_regs] in HF3.
    readback HR'0 HF3 HR2 HRe3.
    rewrite H1, H2', H8, H9, H10, G4', GG3 in HRe3.
    rewrite (GK 18%bv s2 ltac:(inb) ltac:(subst R; reflexivity)), (GK 19%bv s3 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 20%bv s4 ltac:(inb) ltac:(subst R; reflexivity)), (GK 21%bv s5 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 22%bv s6 ltac:(inb) ltac:(subst R; reflexivity)), (GK 23%bv s7 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 24%bv s8 ltac:(inb) ltac:(subst R; reflexivity)), (GK 25%bv s9 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 26%bv s10 ltac:(inb) ltac:(subst R; reflexivity)), (GK 27%bv s11 ltac:(inb) ltac:(subst R; reflexivity)) in HRe3.

    eapply (sr_evt H HH) with
      (P := fun ms => ms = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A) (getr R'0 11) (getr R'0 12) a3' a4' a5' a6' a7'
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None M3 (seg_rom asegs));
      [exact KR2 | exact VIS2 | |].
    { eapply evt_of_msteps; [exact Hms0|]. change (PropExec.mkst R'0 (Z_to_bv 64 958416) M3 (seg_rom asegs)) with (MS R'0 F (Z_to_bv 64 958416) fc None M3 (seg_rom asegs)).
      rewrite HRe3. step. apply evt_done. reflexivity. }
    intros msF3 mo3 KR3 MP3 HP. cbv beta in HP.
    exists t0', t1', t2', (getr R'0 11), (getr R'0 12), a3', a4', a5', a6', a7', t3', t4', t5', t6', M3, errv2, A,
      (firstn 44 (skipn 4 junk)), (skipn 8 (skipn 44 (skipn 4 junk))), p, s'.
    cbn [cfg_ms cfg_model].
    split; [exact HP|]. split; [exact KR3|].
    split; [eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]]|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact RA3|]. split; [exact APall|].
    split; [exact ABR|]. split; [exact RH3|]. split; [exact CALL|]. split; [exact ADDR3|]. split; [exact AC3|].
    exact AL2.
  Qed.

  Lemma ctx_destroy_sr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (s : as_St H) (LB : list block) (p : bptr)
      (A evz lo B : Z) (errv : word) (mo : Model) (CH : list (Z * Z)) (j1 j2 : list byte),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 CTX_DESTROY) fc None m (seg_rom asegs) ->
    a0 = Z_to_bv 64 A ->
    as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> In (p, A, CTX_SZ) LB -> as_Cf H CTX_SZ <= as_AL H s ->
    rw_cells asegs m A [C4 (wz evz); CB 44 j1; C8 (wz 0); CB 8 j2] -> addressable m A CTX_SZ ->
    as_rauxv_ok H m B -> bv_unsigned sp <= B ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 - AFREE_STACK ->
    rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 -> ACONST m ->
    as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (bv_unsigned ra :: map snd CH) ->
    (forall fp ra', In (fp, ra') CH -> bv_unsigned sp + 16 <= fp) ->
    as_SR H (free_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p CTX_SZ lo B errv m mo) (mkCfg msF mo).
  Proof.
    intros until j2. intros VIS Ha0 RH KR INB CF CELLS ADDR RA SPB ST CE LO ERR MI TP SP16 SP47 AC CHN TRC CHUP.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    pose proof (aceil_facts) as ACF. destruct ACF as ((ACF1 & ACF2) & ACF3 & ACF4).
    unfold AFREE_STACK in LO.
    pose proof (ah_blocks H HH _ _ _ _ RH INB) as ABR. unfold blk_addr, blk_size in ABR. cbn [fst snd] in ABR.
    pose proof ABR as (B0 & B16 & Bn & BI & BC & BF & BAPP). unfold AIMG_TOP, CTX_SZ in BI, BC, BF, BAPP, Bn.
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 A; Z_to_bv 64 spz; ra; s0]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34); (8%bv, EVar 35)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp]. }
    pose proof (ACONST_shbase m AC) as [CG CS].
    assert (GZA : gz m A 64) by (intros i Hi; eapply sh0_of_addressable; [exact ADDR | change (8 * (CTX_SZ / 8)) with 64; lia]).
    assert (HK : know_ok asegs E m
       (kn_fix 20 [AOPDEL2] (SCR [] [] []) CTX_DESTROY (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34); (8%bv, EVar 35)])
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (EVar 32) 48) 8 (ELit 0);
         KWr (SA (EVar 33) (-16)) (ELit 16);
         KRange (EVar 33) (2 ^ 45) (2 ^ 47);
         KRange (EVar 32) 0x6e8000 (2 ^ 47); KAlign (EVar 32) 16;
         KDisj (SA (EVar 32) 0) (ELit 64) (SA (EVar 33) (-16)) (ELit 16) ] 40)).
    { kn_eval. unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x1850a0 _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m 0x191038 _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; lia | cbn; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m A _ 48%nat (C8 (wz 0))); [exact CELLS | reflexivity | reflexivity | lia
          | unfold estart; evs; rewrite u64_of_Z by lia; cbn [a_off]; change (Z.of_nat 48) with 48; lia
          | change (Z.of_nat 48) with 48; lia | change (Z.of_nat 48) with 48; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; lia
                           | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; lia | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. split; [lia | exact B16]. }
      apply Forall_cons. { cbn [kentry_ok]. unfold estart, elenZ. evs. rewrite !u64_of_Z by lia. cbn [a_off]. lia. }
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R CTX_DESTROY m (seg_rom asegs) HR HK 60%nat [AOPDEL2] (SCR [] [] []) 40%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(spz - 16, spz)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WOK : aclient_write_ok H LB (spz - 16, spz) /\ aconst_ok (spz - 16, spz)).
    { split; [left; cbn; lia|].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj1 WOK) | apply Forall_nil]]).
    assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj2 WOK) | apply Forall_nil]]).
    assert (RA1 : as_rauxv_ok H M1 B) by (eapply (ah_rauxv_frame H HH); [exact RA | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj1 WOK) | apply Forall_nil]]).
    assert (ERR1 : rw_cells asegs M1 (bv_unsigned tp + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. subst tp. rewrite u64_of_Z by (unfold ATP; lia).
      cbn. unfold ATP. lia. }
    assert (CELLS1 : rw_cells asegs M1 A [C4 (wz evz); CB 44 j1; C8 (wz 0); CB 8 j2]).
    { eapply rw_cells_transport; [exact CELLS | exact MU1 | exact WM1 | cbn; lia]. }
    assert (WH1 : wins_hi [(spz - 16, spz)]).
    { unfold wins_hi. apply Forall_cons; [cbn [fst snd]; right; unfold AHI_LO; lia | apply Forall_nil]. }
    assert (ADDR1 : addressable M1 A CTX_SZ) by (eapply addressable_transport_hi; [exact ADDR | exact MU1 | exact WM1 | unfold AAPP_HI, CTX_SZ; lia | exact WH1]).
    assert (CHN1 : as_chain H M1 (bv_unsigned s0) CH).
    { eapply (chain_via_munch H HH); [exact CHN | exact MU1 |]. intros fp ra' IN. pose proof (CHUP fp ra' IN) as U. cbn. lia. }
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 10%bv G10.
    assert (GK : forall r x, In r [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R r = x -> getr R' r = x).
    { intros r x Hr Hx. rewrite <- Hx. eapply (syms_id_sound R _ _ R' [3; 4; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HR'); [vm_cast_no_check (@eq_refl bool true) | exact Hr]. }
    eapply (sr_blk H HH); [exact KR | exact VIS | rewrite HR0; apply rfull_mkR | exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    rewrite G1, G2, G8, G10, <- Hsp in VIS1.
    rewrite (GK 3%bv gp ltac:(inb) ltac:(subst R; reflexivity)), (GK 4%bv tp ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 9%bv s1 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 18%bv s2 ltac:(inb) ltac:(subst R; reflexivity)), (GK 19%bv s3 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 20%bv s4 ltac:(inb) ltac:(subst R; reflexivity)), (GK 21%bv s5 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 22%bv s6 ltac:(inb) ltac:(subst R; reflexivity)), (GK 23%bv s7 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 24%bv s8 ltac:(inb) ltac:(subst R; reflexivity)), (GK 25%bv s9 ltac:(inb) ltac:(subst R; reflexivity)),
            (GK 26%bv s10 ltac:(inb) ltac:(subst R; reflexivity)), (GK 27%bv s11 ltac:(inb) ltac:(subst R; reflexivity)) in VIS1.
    pose proof (rw_cells_to_CB _ _ _ CELLS1) as CB1.
    eapply (ah_mono H HH).
    { eapply (ah_opdel2 H HH) with (LB := LB) (p := p) (A := A) (n := CTX_SZ) (lo := lo) (B := B) (errv := errv) (CH := CH) (sbs := shadow_of CTX_SZ);
        [exact VIS1 | exact RH1 | exact KR1 | exact INB | exact CF | exact CB1 | exact (proj2 ADDR1) | rewrite shadow_of_length by (unfold CTX_SZ; lia); reflexivity
        | exact RA1 | exact SPB | exact ST1 | exact CE | unfold AFREE_STACK; lia | exact ERR1 | exact MI1 | exact TP | exact SP16 | exact AC1
        | exact CHN1 | exact TRC | reflexivity ]. }
    intros c POST. destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & s' & V' & K' & MP' & MI' & ST' & ERR' & RA' & AP' & RH' & AC' & AL').
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', s'.
    split; [exact V'|]. split; [exact K'|]. split; [eapply (ah_mpres_trans H HH); [exact MP1 | exact MP']|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact RA'|].
    split; [| split; [exact RH'| split; [exact AC'| exact AL']]].
    eapply (apres_trans H); [| exact AP'].
    eapply (apres_weaken H); [eapply (apres_of_munch H HH s LB spz [(spz - 16, spz)] m m M1); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [cbn; lia | apply Forall_nil]] | lia |].
    intros b Hb. exact (proj2 (proj2 (ah_lb_remove H HH)) p LB b Hb).
  Qed.
End Ctx.
