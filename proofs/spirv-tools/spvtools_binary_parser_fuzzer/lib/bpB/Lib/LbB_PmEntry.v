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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_PmBase LbB_FSlots LbB_Regs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition PM_ENTRY : Z := 0xeeefc.
Definition PM_SM8_RA : Z := 0xeef70.

Lemma mul32_srl5 : forall x, 0 <= x < 2 ^ 64 ->
  mul_div M_MUL (Z_to_bv 64 32) (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 5)) = Z_to_bv 64 (x - x mod 32).
Proof.
  intros x Hx. apply bv_eq. cbn [mul_div alu64 alu].
  rewrite bv_mul_unsigned, bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small x), (Z.mod_small 32), (Z.mod_small 5), (Z.mod_small 63) by lia. change (Z.land 5 63) with 5.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
  pose proof (Z.div_mod x 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as B.
  assert (0 <= x / 32 < 2 ^ 59) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite !Z.mod_small by lia. lia.
Qed.

Lemma outside_app_l : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [exact I|]. destruct H as [H1 H2]. split; [exact H1 | exact (IH _ _ H2)]. Qed.
Lemma outside_app_r : forall W1 W2 x, outside (W1 ++ W2) x -> outside W2 x.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x H; cbn in *; [exact H|]. destruct H as [H1 H2]. exact (IH _ _ H2). Qed.
Lemma munch_app : forall W1 W2 m1 m2 m3, munch W1 m1 m2 -> munch W2 m2 m3 -> munch (W1 ++ W2) m1 m3.
Proof.
  intros W1 W2 m1 m2 m3 H1 H2 x Hx. rewrite (H2 x (outside_app_r _ _ _ Hx)). apply H1. exact (outside_app_l _ _ _ Hx).
Qed.
Lemma omiss_same : forall E b y n log, forallb (fun e => expr_eqb (a_base (e_addr e)) b) log = true -> Forall (omiss E b y n) log.
Proof.
  intros E b y n log Hb. apply Forall_forall. intros e He Hne. exfalso.
  pose proof (proj1 (forallb_forall _ _) Hb e He) as K. cbn in K. rewrite K in Hne. discriminate.
Qed.

Section Entry.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Lemma HH : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.
  Lemma HSM8 : stack_malloc_sz_stmt H 8 AFS_MALLOC_8.
  Proof. pose proof HHbp as (_ & X & _). destruct X as (_ & _ & _ & _ & _ & X & _). exact X. Qed.

  Definition pmS1 (sp0 : Z) : Z := sp0 - 832 - (sp0 - 832) mod 32.

  Lemma pm_e1 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
      (LF : list fframe) (p lo : Z) (Q : config -> Prop),
    as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 PM_ENTRY) fc None m (seg_rom asegs) ->
    as_AKREL H s (mkCfg msF mo) ->
    a0 = Z_to_bv 64 p ->
    stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 32768 ->
    bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= 2 ^ 47 ->
    mem_inv asegs m -> ACONST m -> as_RHEAP H s LB m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> tp = Z_to_bv 64 ATP ->
    (forall msF1 mo1 m1 (ff fp : Z) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       as_AKREL H s (mkCfg msF1 mo1) -> as_MPRES H mo mo1 ->
       as_VIS H s msF1 = MS (mkR (Z_to_bv 64 PM_SM8_RA) (Z_to_bv 64 (pmS1 (bv_unsigned sp))) gp tp t0' t1' t2' sp
                                 (Z_to_bv 64 (pmS1 (bv_unsigned sp))) (Z_to_bv 64 ff)
                                 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 (Z_to_bv 64 p) s8 (Z_to_bv 64 SHBASE) s10 s11 t3' t4' t5' t6')
                            F (Z_to_bv 64 PM_SM8_RA) fc None m1 (seg_rom asegs) ->
       munch [(bv_unsigned sp - 832, bv_unsigned sp); (pmS1 (bv_unsigned sp) - AFS_STACK, pmS1 (bv_unsigned sp));
              (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)] m m1 ->
       wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 lo (bv_unsigned sp) ->
       rw_cells asegs m1 (bv_unsigned sp - 104) (map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra]) ->
       as_RFS H ((8, ff, fp) :: LF) m1 ->
       (exists j1 j2, rw_cells asegs m1 ff [CB 24 j1; C8 (Z_to_bv 64 (pmS1 (bv_unsigned sp))); CB 16344 j2; C8 (Z_to_bv 64 fp)]) ->
       SHAD m1 ff (poison_bytes 1448 0) -> rw_cells asegs m1 fp [C1 (b8 1)] -> ACONST m1 -> as_RHEAP H s LB m1 ->
       as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros until Q. intros VIS KR Ha0 ST CE LO SP16 SP47 MI AC RH RF LFB TP K.
    set (spz := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 spz) by (subst spz; symmetry; apply Z_to_bv_bv_unsigned).
    pose proof (bv_unsigned_in_range 64 sp) as Hspr. change (bv_modulus 64) with (2 ^ 64) in Hspr. fold spz in Hspr.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    remember (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 spz; Z_to_bv 64 0; ra]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 34); (1%bv, EVar 36)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; try reflexivity; [exact Ha0 | exact Hsp]. }
    pose proof (ACONST_shbase m AC) as [CG CS]. pose proof (ACONST_uar m AC) as [UG UC].
    assert (HK : know_ok asegs E m
       [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
         KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
         KWord (SA (ELit 0) AGOT_UAR) 8 (ELit AUAR_CELL);
         KWord (SA (ELit 0) AUAR_CELL) 4 (ELit 1);
         KWr (SA (EVar 34) (-832)) (ELit 832);
         KRange (EVar 34) 0x7fff7f800000 (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_SHBASE _ 0%nat (C8 (wz ASHBASE_CELL))); [exact CG | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m ASHBASE_CELL _ 0%nat (C8 (wz ASHADOW_BASE))); [exact CS | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AGOT_UAR _ 0%nat (C8 (wz AUAR_CELL))); [exact UG | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells asegs E m AUAR_CELL _ 0%nat (C4 (wz 1))); [exact UC | reflexivity | reflexivity | lia | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL, AGOT_UAR, AUAR_CELL; lia | reflexivity]. }
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | | | ].
        - unfold estart. cbn [a_base a_off]. evs. rewrite u64_of_Z by lia. lia.
        - unfold estart, elenZ. cbn [a_base a_off]. evs. rewrite !u64_of_Z by lia. lia.
        - unfold elenZ. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_cons. { cbn [kentry_ok]. evs. rewrite u64_of_Z by lia. lia. }
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R PM_ENTRY m (seg_rom asegs) HR HK 60%nat [AFS_MALLOC_8] (SCR [] [] []) 40%N.
    { split_scs. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms; set (LOG1 := lg) in Hlf, M1 end end.

    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 8%bv G8. rreg HR' 9%bv G9. rreg HR' 10%bv G10.
    rreg HR' 23%bv G23. rreg HR' 25%bv G25.
    set (S1 := pmS1 spz).
    assert (HS1 : mul_div M_MUL (Z_to_bv 64 32) (alu64 ALU_SRL (alu64 ALU_ADD (Z_to_bv 64 spz) (Z_to_bv 64 (-832))) (Z_to_bv 64 5))
                  = Z_to_bv 64 S1).
    { rewrite w_addm by lia. rewrite mul32_srl5 by lia. reflexivity. }
    rewrite HS1 in G2, G9.
    assert (S1r : spz - 864 <= S1 <= spz - 832 /\ S1 mod 32 = 0).
    { subst S1. unfold pmS1. pose proof (Z.mod_pos_bound (spz - 832) 32 ltac:(lia)). split; [lia|].
      pose proof (Z.div_mod (spz - 832) 32 ltac:(lia)). Z.div_mod_to_equations. lia. }

    assert (MU1 : munch [(spz - 832, spz)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|]. subst LOG1.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite u64_of_Z by lia; cbn [inside Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo spz) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WOK : aclient_write_ok H LB (spz - 832, spz) /\ aconst_ok (spz - 832, spz)).
    { split; [left; cbn; lia|]. apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    assert (RH1 : as_RHEAP H s LB M1) by (eapply (ah_RHEAP_frame H HH); [exact RH | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj1 WOK) | apply Forall_nil]]).
    assert (AC1 : ACONST M1) by (eapply ACONST_frame; [exact AC | exact MU1 | exact WM1 | apply Forall_cons; [exact (proj2 WOK) | apply Forall_nil]]).
    assert (RF1 : as_RFS H LF M1).
    { eapply (ah_RFS_frame H HH); [exact RF | exact MU1 | exact WM1 |]. apply Forall_cons; [| apply Forall_nil].
      left. cbn [fst snd]. destruct (proj1 (ah_RFS_range H HH _ _ RF)) as (F1 & F2 & F3 & F4). unfold ATLS_PRIV_HI, ATP. split; right; lia. }
    assert (THR1 : athr_cells M1) by exact (ah_thr H HH _ _ _ RH1).

    assert (SAME1 : forallb (fun e => expr_eqb (a_base (e_addr e)) (EVar 34)) LOG1 = true) by (subst LOG1; vm_cast_no_check (@eq_refl bool true)).
    assert (SV1 : rw_cells asegs M1 (spz - 104) (map C8 [s11; s10; s9; s8; s7; s6; s5; s4; s3; s2; s1; s0; ra])).
    { apply rw_cells_C8s; [lia | cbn; lia |]. intros i x Hx.
      lazymatch type of Hlf with log_flat ?E0 _ => set (EE := E0) in Hlf, M1 end.
      assert (OM : forall y n, Forall (omiss EE (EVar 34) y n) LOG1) by (intros y n; exact (omiss_same EE (EVar 34) y n LOG1 SAME1)).
      assert (E34 : bv_unsigned (edenot EE (EVar 34)) = spz) by (subst EE; cbn [edenot]; unfold Eseed, reg_ev; cbn [ev]; apply u64_of_Z; lia).
      do 13 (destruct i as [|i]; [ cbn in Hx; injection Hx as <-;
        apply rw_C8_of_rdn; [lia | lia | |
          destruct ST1 as (W1 & W2 & W3); split; [lia|]; split; [lia|]; intros j Hj; apply (W3 (_ + j)); lia ];
        match goal with |- PropExec.rdn _ _ (Z_to_bv 64 (spz - 104 + 8 * Z.of_nat ?k)) _ = _ =>
          let kk := constr:(-104 + 8 * Z.of_nat k) in
          let v := eval vm_compute in (lword LOG1 (EVar 34) kk) in
          lazymatch v with Some (Some ?ve) =>
            replace (spz - 104 + 8 * Z.of_nat k) with (bv_unsigned (edenot EE (EVar 34)) + kk) by (rewrite E34; cbn; lia);
            unfold M1; rewrite (rdn_slot_some asegs EE m LOG1 (EVar 34) kk ve Hlf (OM _ _) ltac:(vm_cast_no_check (@eq_refl _ v)) ltac:(rewrite E34; cbn; lia) ltac:(rewrite E34; cbn; lia));
            f_equal; subst EE R; cbn [edenot]; unfold Eseed, reg_ev; cbn [ev]; reflexivity
          end
        end | ]).
      destruct i; cbn in Hx; discriminate. }

    assert (GK : forall r, In r [3; 4; 18; 19; 20; 21; 22; 24; 26; 27]%bv -> getr R' r = getr R r).
    { intros r Hr. lazymatch type of HR' with regs_ok (Eseed R ?vals) ?sr' R' =>
        exact (syms_id_sound R vals sr' R' [3; 4; 18; 19; 20; 21; 22; 24; 26; 27]%bv HR' ltac:(vm_cast_no_check (@eq_refl bool true)) r Hr) end. }
    rewrite !mkst_MS in Hms. rewrite HR0 in VIS.
    eapply (sr_blk H HH); [exact KR | exact VIS | apply rfull_mkR | rewrite <- HR0; exact Hms |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (ahh_evt_then H HH); [exact KR1 | exact VIS1 | |].
    { eapply HSM8 with (LF := LF) (lo := lo) (sz := 11584); [exact G10 | change (fsz 8) with 16384; lia | reflexivity | exact RF1 | lia | | exact CE | | exact MI1 | | exact AC1 | exact THR1].
      - rewrite G2, u64_of_Z by lia. exact (proj1 (stk_split asegs M1 lo S1 spz ST1 ltac:(lia))).
      - rewrite G2, u64_of_Z by lia. unfold AFS_STACK. lia.
      - rewrite (GK 4%bv ltac:(inb)). subst R. exact TP. }
    intros msF2 mo2 KR2 MP2 POST.
    destruct POST as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & ff & fp & junk1 & junk2
                      & EQ & MU2 & WM2 & MI2 & ST2 & RF2 & CL2 & SH2 & FL2 & AC2).
    rewrite G1 in EQ. rewrite (ret_pc_even 978800 ltac:(lia) eq_refl) in EQ.
    rewrite G2, u64_of_Z in MU2, ST2 by lia.
    pose proof (fresh_frame_facts H _ _ _ _ (fresh_of_RFS H HH _ _ _ _ _ RF2)) as FA.
    destruct FA as (FK & FR1 & FR2 & FM64 & FM8 & FP1 & FP2 & FP3 & FP4 & FP5 & FP6 & FP7 & FP8 & FP9).
    change (fsz 8) with 16384 in *. change (fshn 8) with 2048 in *.
    assert (DJ2 : forall a n, S1 <= a -> a + n <= spz -> 0 <= n ->
               disjoint_from [(S1 - AFS_STACK, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 16384); (sh ff, sh ff + 2048)] a n).
    { intros a n Ha Hn Hn0. cbn. unfold AFS_STACK, AFS_FLAGS, AFS_HDR, AFS_SIZE in *.
      assert (sh ff + 2048 <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
      repeat split; lia. }
    apply (K msF2 mo2 m2 ff fp t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6').
    - exact KR2.
    - exact (ah_mpres_trans H HH _ _ _ MP1 MP2).
    - rewrite EQ. rewrite G2, G8, G9, G23, G25.
      rewrite (GK 3%bv ltac:(inb)), (GK 4%bv ltac:(inb)), (GK 18%bv ltac:(inb)), (GK 20%bv ltac:(inb)),
              (GK 21%bv ltac:(inb)), (GK 19%bv ltac:(inb)), (GK 22%bv ltac:(inb)), (GK 24%bv ltac:(inb)),
              (GK 26%bv ltac:(inb)), (GK 27%bv ltac:(inb)).
      subst R. rewrite Hsp. reflexivity.
    - change ([(spz - 832, spz); (pmS1 spz - AFS_STACK, pmS1 spz); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 8); (sh ff, sh ff + fshn 8)])
        with ([(spz - 832, spz)] ++ [(S1 - AFS_STACK, S1); (as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + 16384); (sh ff, sh ff + 2048)]).
      exact (munch_app _ _ _ _ _ MU1 MU2).
    - exact (wmono_trans asegs _ _ _ WM1 WM2).
    - exact MI2.
    - apply (stk_merge asegs m2 lo S1 spz); [exact ST2 | | lia].
      eapply stk_transport_disjoint; [exact (proj2 (stk_split asegs M1 lo S1 spz ST1 ltac:(lia))) | exact MU2 | exact WM2 |].
      apply DJ2; lia.
    - eapply rw_cells_transport; [exact SV1 | exact MU2 | exact WM2 |]. cbn [map cells_size csize]. apply DJ2; cbn; lia.
    - exact RF2.
    - exists junk1, junk2. rewrite G2 in CL2. exact CL2.
    - exact SH2.
    - exact FL2.
    - exact AC2.
    - eapply (ah_RHEAP_frame H HH); [exact RH1 | exact MU2 | exact WM2 |].
      repeat apply Forall_cons; try apply Forall_nil.
      + left. cbn. unfold AFS_STACK. lia.
      + right; right; right; right; left. cbn. unfold AFS_FLAGS, AFS_SIZE. lia.
      + right; right; right; right; left. cbn. unfold AFS_FLAGS, AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; left. cbn. unfold AFS_HDR, AFS_SIZE in *. lia.
      + right; right; right; right; right; left. cbn. split.
        * apply sh_mono. unfold AFS_HDR in *. lia.
        * assert (sh (ff + 16384) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
          assert (sh ff + 2048 = sh (ff + 16384)) by (unfold sh; Z.div_mod_to_equations; lia). lia.
  Qed.
End Entry.
