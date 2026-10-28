(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim StoreOk SymExec3 SymExec3Sound SymRun3 Hoare RefMemcpyLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel HFpu HCommon.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_HStKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD LbB_NtI LbB_NtI4
  LbB_NtRL LbB_NtRE LbB_NtRB LbB_NtF LbB_NtG LbB_NtNd LbB_NtS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpNd LbB_RGl.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition E_DSP : Z := 0xf516c.

Definition srEN : list expr := srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (21%bv, EVar 34); (23%bv, EVar 33)].
Definition KN_EN : list kentry :=
  [KWord (SA (EVar 32) 616) 8 (ELit SHBASE);
   KWr (SA (EVar 32) 584) (ELit 32); KWr (SA (EVar 32) 632) (ELit 16); KWr (SA (EVar 32) 656) (ELit 16);
   KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672); KRange (EVar 33) (7241728 - 136) (2 ^ 47 - 176); KRange (EVar 34) 0 (2 ^ 47 - 8)].
Definition SCR_EN := SCR [] [EVar 35; EVar 36] [].

Definition srD : list expr := srs sr_id [(27%bv, EVar 34); (18%bv, EVar 33); (2%bv, EVar 35); (9%bv, EVar 35)].
Definition KN_D : list kentry := [].

Definition popcD : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec ASEGS 100 true [0xf51e4] (SCR [false] [] []) (SS E_DSP srD [] KN_D 50) [] in
     sr_get (s_regs ss) 11%bv).
Definition popcwD (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popcD.
Lemma popcD_env : forall E, edenot E popcD = popcwD (ev E 34).
Proof. intros E. unfold popcwD, popcD. cbn [edenot ev]. reflexivity. Qed.
Ltac vm_popcD :=
  match goal with |- context [bv_unsigned (popcwD ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcwD w)) in
    replace (bv_unsigned (popcwD w)) with v by (vm_compute; reflexivity) end.
Lemma popcwD_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcwD (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcwD (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popcD; reflexivity]
            | right; split; [lia | vm_popcD; lia] ] |]).
  destruct Hin.
Qed.

Definition non_dsp : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition aonlyD (R R' : bvmap 5 word) : Prop := forall r, In r non_dsp -> getr R' r = getr R r.
Definition SCR_D0 := SCR [true] [] [].
Definition SCR_D2 := SCR [false; false] [] [].
Definition SCR_Dlt := SCR [false; true; true] [] [].
Definition SCR_Dge := SCR [false; true; false] [] [].

Section Dsp.
  Context {fx : PropExec.FPState}.
  Context {AC : AllocCeiling}.
  Variable rom : word -> option byte.
  Variables (M : mem) (S1 key bc : Z).
  #[local] Abbreviation st R pc := (@PropExec.mkst fx R (Z_to_bv 64 pc) M rom).

  Ltac runD R scr :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in let Hpc := fresh "Hpc" in
    pose (E := Eseed R [Z_to_bv 64 0; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 S1]);
    assert (HR : regs_ok E srD R) by
      (apply regs_ok_srs; [apply regs_ok_seed|];
       repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; assumption] |]); apply Forall_nil);
    assert (HK : know_ok ASEGS E M KN_D) by (unfold know_ok; apply Forall_nil);
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popcD) = b ->
                  sc_denot ASEGS M E (SCBr b BC_LTU (ELit 1) popcD)) by (intros b Hb; exact Hb);
    xrun HR HK 60%nat [E_BB; E_NF] scr 50%N;
    [ split_scs; try sc_auto1;
      try (apply Hpc; rewrite popcD_env; evs; rewrite branch_ltu_lit_l by lia; bool_lia);
      try (cbn [sc_denot]; evs; rewrite ?br_ne, ?br_eq, ?br_ltu, ?br_geu by lia; bool_lia)
    | ].

  Lemma dsp_z : forall R, getr R 27%bv = Z_to_bv 64 bc -> getr R 18%bv = Z_to_bv 64 key -> getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 ->
    bc = 0 ->
    exists R', CatSim.msteps ASEGS (st R E_DSP) (st R' E_NF) /\ aonlyD R R'.
  Proof.
    intros R H27 H18 H2 H9 Hbc. runD R SCR_D0.
    exists R'. split; [exact Hms|]. intros r Hr. refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr). vm_cast_no_check (@eq_refl bool true).
  Qed.

  Lemma dsp_nz : forall R, In bc BSEQ -> bc <> 0 -> 0 <= key < 2 ^ 32 ->
    getr R 27%bv = Z_to_bv 64 bc -> getr R 18%bv = Z_to_bv 64 key -> getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 ->
    exists R' pw, CatSim.msteps ASEGS (st R E_DSP) (st R' E_BB) /\ aonlyD R R' /\ getr R' 22%bv = Z_to_bv 64 (hmod key bc)
      /\ getr R' 11%bv = Z_to_bv 64 pw /\ 0 <= pw < 2 ^ 64 /\ (bc <> 2 -> 2 <= pw) /\ (bc = 2 -> pw < 2).
  Proof.
    intros R Hin Hbc Hk H27 H18 H2 H9. pose proof (LbB_HFind.BSEQ_boundA bc Hin) as Hbcr.
    pose proof (bv_unsigned_in_range 64 (popcwD (Z_to_bv 64 bc))) as PWR. change (bv_modulus 64) with (2 ^ 64) in PWR.
    destruct (popcwD_cases bc Hin Hbc) as [[Hbc2 Hp1]|[Hbc2 Hp2]].
    - runD R SCR_D2.
      assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
      rreg HR' 22%bv G22.
      exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
      split; [intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
      split; [rewrite G22; rewrite w_addm, w_and by lia; subst bc; unfold hmod; change (2 + -1) with (Z.ones 1);
              first [rewrite Z.land_ones by lia | rewrite Z.land_comm, Z.land_ones by lia]; reflexivity|].
      split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
    - destruct (Z.lt_ge_cases key bc) as [Hlt|Hge].
      + runD R SCR_Dlt.
        assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
        rreg HR' 22%bv G22.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G22; unfold hmod; rewrite Z.mod_small by lia; reflexivity|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
      + runD R SCR_Dge.
        assert (P11 : getr R' 11%bv = popcwD (Z_to_bv 64 bc)) by exact (eq_trans (HR' 11%bv) (popcD_env E)).
        rreg HR' 22%bv G22.
        exists R', (bv_unsigned (popcwD (Z_to_bv 64 bc))). split; [exact Hms|].
        split; [intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ non_dsp HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true)|].
        split; [rewrite G22; unfold hmod; apply LbB_HFind.remuw_valA; lia|].
        split; [rewrite P11; symmetry; apply Z_to_bv_bv_unsigned|]. lia.
  Qed.
End Dsp.

Section NtE.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Tactic Notation "rq" constr(AO) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO (r : reg) ltac:(inb)) as Q; rewrite HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.
  Tactic Notation "rq2" constr(AO3) constr(AO2) constr(HRe) uconstr(r) ident(Q) :=
    pose proof (AO3 (r : reg) ltac:(inb)) as Q; rewrite (AO2 (r : reg) ltac:(inb)), HRe in Q; cbn [getr mkR PropExec.getr Vector.nth] in Q.
  Ltac npre_tac := unfold NPRE; repeat match goal with |- _ /\ _ => split end;
    first [eassumption | (apply Z.le_ge; apply Z.le_refl) | lia].

  Theorem nt_specA : nt_stmt H.
  Proof.
    intros ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 F fc msF m mo s LB LB0 LBm LF CH
      S1 obj bl bc keyp key v408 v576 v624 ents lo B shi errv j584 j592 j600 j608 j632 j640 j656 j664
      VIS FRZ U SH PE PM ADH WRH LFO OCE OBL FK EK K0 KCE K4 KR32 RS V408 V576 V624 W584 W632 W656 ZLEN BCL RH KR AL0 RSM RCN RLG RICM
      CHN TRK CHH RA SPB BR SP16 ST ACL LOR ERR MI TPV AC RF S0 SHI OWN.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    assert (LOS : lo <= S1) by (clear - LOR'; lia).
    assert (SPH : S1 + 672 <= 2 ^ 47) by (destruct S0 as (g & _ & Hg & _); unfold AAPP_HI in Hg; clear - Hg SHI; lia).
    assert (SPL : 2 ^ 45 <= S1) by (clear - ACF1 ACL LOR'; lia).
    pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_al U) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U)) as BCR.
    destruct (u_hdr U) as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    assert (GZO : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof RS as RS0. destruct RS0 as (R408 & R576 & R616 & R624 & R648).
    remember (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                  (Z_to_bv 64 keyp) s6 (Z_to_bv 64 (obj - 136)) s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).

    assert (CK : cellw ASEGS m keyp 4 key) by (split; [cbn; lia | exact FK]).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 (obj - 136); Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E srEN R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_b : sc_denot asegs m E (SCReadBase (SA (EVar 33) 144) 8 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (Hrd_k : sc_denot asegs m E (SCReadBase (SA (EVar 34) 0) 4 false (EVar 36))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ CK); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [E_DSP] SCR_EN NT_ENTRY srEN KN_EN 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell R616 0%nat (C8 (Z_to_bv 64 SHBASE))|].
      do 3 (apply Forall_cons;
        [ eapply kwr_of_stk; [exact ST | unfold estart; evs; rewrite u64_of_Z by lia; clear - ACL LOS; cbn [a_off a_base]; lia
                                       | unfold estart, elenZ; evs; rewrite !u64_of_Z by lia; cbn [a_off a_base]; lia
                                       | unfold elenZ; evs; rewrite u64_of_Z by lia; lia] |]).
      apply Forall_cons; [(cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia)|].
      apply Forall_cons; [(cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho0 Ho1; lia)|].
      apply Forall_cons; [(cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - K0 KCE ACF2; lia)|].
      clear - GZO Ho0 Ho1 OB3; know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R NT_ENTRY m (seg_rom asegs) HR HK 30%nat [E_DSP] SCR_EN 50%N.
    { clear - E Hrd_b Hrd_k K0 KCE ACL LOS OCE Ho0 Ho1 SPL SPH OB1 OB2 OB3 ACF1 ACF2.
      split_scs.
      all: first [exact Hrd_b | exact Hrd_k | sc_dj]. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    set (W1 := [(S1 + 600, S1 + 616); (S1 + 632, S1 + 648); (S1 + 656, S1 + 672)]).
    assert (MU1 : munch W1 m M1).
    { subst M1 W1. apply munch_mem_denot; [exact Hlf|]. clear - E SPL SPH Ho0 Ho1 OB3.
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia;
                                          cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]);
               apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (WROK : forall l h, S1 <= l -> h <= S1 + 672 -> l <= h ->
                   aclient_write_ok H LB (l, h) /\ afs_write_ok H LF (l, h) /\ aconst_ok (l, h) /\ stack0_ok (l, h)).
    { intros l h Hl Hh Hlh. assert (Xl : aceil <= l) by (clear - ACL LOS Hl; lia).
      destruct (stack_window_ok H LB LF l h Xl FB2) as (X1 & X2 & X3).
      split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. left. cbn. unfold AHI_LO. clear - SPL Hl. lia. }
    assert (FW : Forall (fun iv => aclient_write_ok H LB iv /\ afs_write_ok H LF iv /\ aconst_ok iv /\ stack0_ok iv) W1).
    { subst W1. apply Forall_cons; [apply WROK; lia|]. apply Forall_cons; [apply WROK; lia|]. apply Forall_cons; [apply WROK; lia | apply Forall_nil]. }
    assert (F1 : Forall (aclient_write_ok H LB) W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 X)).
    assert (F2 : Forall (afs_write_ok H LF) W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 (proj2 X))).
    assert (F3 : Forall aconst_ok W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj1 (proj2 (proj2 X)))).
    assert (F4 : Forall stack0_ok W1) by (eapply Forall_impl; [|exact FW]; intros iv X; exact (proj2 (proj2 (proj2 X)))).
    destruct (client_frame H HH s LB LF B W1 m M1 RH RF AC RA MU1 WM1 F1 F2 F3) as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact F4]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m M1).
    { eapply (xpres_munch_mixed H HH s LB LB0 LBm S1 (nt_X S1 obj) W1 m m M1); [apply xpres_refl | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      subst W1; repeat (apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs nt_X Datatypes.fst Datatypes.snd] in *; lia|]); apply Forall_nil. }
    assert (AG1 : forall a k, 0 <= a -> 0 <= k -> a + k <= S1 + 600 -> agree_on m M1 a k).
    { intros a k Ha Hk Hak. eapply agree_of_munch; [exact MU1 | | lia | clear - Hak SPH; lia]. intros z Hz. subst W1. cbn. clear - Hz Hak. lia. }
    assert (DSH1 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from W1 (sh A) (nsh k)).
    { intros A k HA Hk HAk. subst W1. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      pose proof (sh_nsh_high A k HA Hk ltac:(unfold AAPP_HI; lia)) as SN. unfold AHI_LO in SN.
      unfold ALOWSH_LO, AHI_LO. repeat (apply Forall_cons; [cbn [fst snd]; clear - SPL; lia |]). apply Forall_nil. }

    assert (WRS : forall o k, 0 <= o -> o + k <= 672 -> 0 <= k -> wr_at asegs m (S1 + o) k).
    { intros o k Ho Hk Hk0. eapply LbB_HEmpD.wr_at_subE; [exact (wr_at_of_stk _ _ _ _ ST) | clear - LOS Ho; lia | clear - Hk; lia | exact Hk0]. }
    assert (X584 : rw_cells asegs m (S1 + 584) ([C8 j584; C8 j592] ++ [C8 j600; C8 j608])) by exact W584.
    apply rw_cells_app in X584 as [X584a _].
    assert (W584a : rw_cells asegs M1 (S1 + 584) [C8 j584; C8 j592]) by (eapply rw_cells_transport; [exact X584a | exact MU1 | exact WM1 | subst W1; cbn; lia]).
    assert (W600a : rw_cells asegs M1 (S1 + 600) [C8 a5]).
    { subst M1; rwc_newT Hlf (WRS 600 8 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; rewrite HR0; reflexivity). }
    assert (W608a : rw_cells asegs M1 (S1 + 608) [C8 s10]).
    { subst M1; rwc_newT Hlf (WRS 608 8 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(evs; rewrite HR0; reflexivity). }
    assert (W632a : rw_cells asegs M1 (S1 + 632) [C8 (Z_to_bv 64 (obj + 8))]).
    { subst M1; rwc_newT Hlf (WRS 632 8 ltac:(lia) ltac:(lia) ltac:(lia))
                 ltac:(evs; rewrite (w_add (obj - 136) 144) by lia; replace (obj - 136 + 144) with (obj + 8) by lia; reflexivity). }
    assert (W640a : rw_cells asegs M1 (S1 + 640) [C8 (Z_to_bv 64 (obj / 8))]).
    { subst M1; rwc_newT Hlf (WRS 640 8 ltac:(lia) ltac:(lia) ltac:(lia))
                 ltac:(evs; rewrite (w_add (obj - 136) 136) by lia; replace (obj - 136 + 136) with obj by lia;
                       rewrite (HWord.w_srl obj 3) by lia; reflexivity). }
    assert (W656a : rw_cells asegs M1 (S1 + 656) [C8 (Z_to_bv 64 obj)]).
    { subst M1; rwc_newT Hlf (WRS 656 8 ltac:(lia) ltac:(lia) ltac:(lia))
                 ltac:(evs; rewrite (w_add (obj - 136) 136) by lia; replace (obj - 136 + 136) with obj by lia; reflexivity). }
    assert (W664a' : rw_cells asegs M1 (S1 + 664) [C8 (Z_to_bv 64 ((obj + 8) / 8 + SHBASE))]).
    { subst M1; rwc_newT Hlf (WRS 664 8 ltac:(lia) ltac:(lia) ltac:(lia))
                 ltac:(evs; rewrite (w_add (obj - 136) 144) by lia; replace (obj - 136 + 144) with (obj + 8) by lia;
                       rewrite (LbB_NtD.sh_word (obj + 8)) by lia; reflexivity). }
    assert (W664a : rw_cells asegs M1 (S1 + 664) [C8 (Z_to_bv 64 (sh (obj + 8)))]).
    { replace (sh (obj + 8)) with ((obj + 8) / 8 + SHBASE) by (unfold sh; rewrite ASHADOW_BASE_val; unfold SHBASE; lia). exact W664a'. }
    assert (WS1 : WSLOTS s10 a5 S1 obj M1 j584 j592).
    { unfold WSLOTS, nt_wslots; split; [exact W584a|]; split; [|split];
               [ change [C8 a5; C8 s10] with ([C8 a5] ++ [C8 s10]); apply rw_cells_app; split; [exact W600a|];
                 cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; eapply rw_cells_addr; [exact W608a | lia]
               | change [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))] with ([C8 (Z_to_bv 64 (obj + 8))] ++ [C8 (Z_to_bv 64 (obj / 8))]);
                 apply rw_cells_app; split; [exact W632a|];
                 cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; eapply rw_cells_addr; [exact W640a | lia]
               | change [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))] with ([C8 (Z_to_bv 64 obj)] ++ [C8 (Z_to_bv 64 (sh (obj + 8)))]);
                 apply rw_cells_app; split; [exact W656a|];
                 cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add]; eapply rw_cells_addr; [exact W664a | lia]]. }
    assert (RS1 : nt_slots M1 S1 obj v408 v576 v624).
    { unfold nt_slots. repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | subst W1; cbn; lia]). }
    pose proof RS1 as RS1'. destruct RS1' as (R408a & R576a & R616a & R624a & R648a).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { assert (EA : errno_addr tp = ATP - 164) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); vm_compute; reflexivity).
      rewrite EA in ERR |- *. eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | subst W1; cbn; unfold ATP; clear - SPL; lia]. }
    assert (U1 : umapx MI_A 32 (nval32 ASEGS) (lbl LB) M1 obj bl bc ents).
    { eapply (umapx_agree ASEGS LY_A MI_A 32 _ (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) (lbl LB) (lbl LB) m M1); [exact U | | intros; assumption].
      intros a Ha.
      assert (AGa : 0 <= aceil) by (clear - ACF1; lia). assert (AGb : 0 + aceil <= S1 + 600) by (clear - ACL LOS; lia).
      pose proof (AG1 0 aceil (Z.le_refl 0) AGa AGb) as AG.
      assert (Ha' : 0 <= a < aceil).
      { destruct Ha as [Ha | [[Hbc Ha] | (q & Hq & Hqa)]]; [lia | |].
        - pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
          destruct (lbl_in_inv LBm bl (8 * bc) (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; left; destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (_ & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC. lia.
        - apply in_map_iff in Hq. destruct Hq as ([z [k v]] & Hz & Hin). cbn in Hz. subst z.
          destruct (lbl_in_inv LBm q 32 (Permutation_in _ (Permutation_sym PM) ltac:(unfold umap_blocks; apply in_or_app; right; apply in_map_iff; exists (q, (k, v)); split; [reflexivity | exact Hin]))) as (qi & Qi).
          pose proof (ah_blocks H HH _ _ _ _ RH (Permutation_in _ (Permutation_sym PE) (in_or_app _ _ _ (or_intror Qi)))) as (Q0 & _ & _ & _ & QC & _).
          cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC, Q0. cbn in Hqa. clear - QC Q0 Hqa. lia. }
      pose proof (AG a ltac:(lia)) as X. rewrite Z.add_0_l in X. exact X. }
    assert (SH1 : umap_sh M1 32 (bl, bc, ents)).
    { destruct SH as [SHb SHn]. unfold umap_sh, HStmts.t3a, HStmts.t3b, HStmts.t3c in *. cbn [Datatypes.fst Datatypes.snd] in *. split.
      - intros Hbc. pose proof (u_bl_hi U). pose proof (u_bl_lo U Hbc).
        eapply addressable_transport; [exact (SHb Hbc) | exact MU1 | exact WM1 | apply DSH1; lia].
      - intros q k v Hin. destruct (ent_facts _ _ _ _ _ _ _ U Hin) as (E0 & E1 & _). cbn in E0, E1.
        eapply addressable_transport; [exact (SHn q k v Hin) | exact MU1 | exact WM1 | apply DSH1; lia]. }
    assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH1; lia]).
    assert (WRH1 : wr_at asegs M1 obj 40) by exact (wr_at_wmono _ _ _ _ WRH WM1).
    assert (FK1 : fldA M1 keyp 4 key).
    { unfold fldA in FK |- *. eapply (CRep.fld_agree ASEGS); [lia | cbn; lia | exact FK |].
      intros a Ha. unfold zwin in Ha. cbn [Z.of_nat] in Ha. pose proof (AG1 keyp 4 ltac:(lia) ltac:(lia) ltac:(clear - KCE ACL LOS; lia) (a - keyp) ltac:(lia)) as X.
      replace (keyp + (a - keyp)) with a in X by lia. exact X. }
    assert (OWN1 : lb_own LBm M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    assert (CHN1 : as_chain H M1 (bv_unsigned s0) CH).
    { eapply (chain_keep H HH m M1 _ CH S1); [exact CHN | exact CHH |];
               intros a Ha; apply MU1; rewrite u64_of_Z by lia; subst W1; cbn; lia. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 16%bv G16. rreg HR' 17%bv G17. rreg HR' 18%bv G18.
    rreg HR' 21%bv G21. rreg HR' 23%bv G23. rreg HR' 27%bv G27.
    rewrite (w_add (obj - 136) 136) in G16, G17 by lia. replace (obj - 136 + 136) with obj in G16, G17 by lia.
    rewrite (HWord.w_srl obj 3) in G17 by lia. change (obj / 2 ^ 3) with (obj / 8) in G17.
    rewrite G2, G9, G16, G17, G18, G21, G23, G27 in HRe. clear G2 G9 G16 G17 G18 G21 G23 G27.

    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbcn].
    - destruct (@dsp_z (PropExec.mkFP F fc) (seg_rom asegs) M1 S1 key bc R' ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity)
                  ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) Hbc0) as (R2 & Hms2 & AO2).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.
      eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms12 |].
      intros msF1 mo1 KR1 MP1 VIS1.
      rq AO2 HRe 2%bv Q2. rq AO2 HRe 3%bv Q3. rq AO2 HRe 4%bv Q4. rq AO2 HRe 8%bv Q8. rq AO2 HRe 9%bv Q9. rq AO2 HRe 18%bv Q18.
      rq AO2 HRe 20%bv Q20. rq AO2 HRe 21%bv Q21. rq AO2 HRe 24%bv Q24. rq AO2 HRe 27%bv Q27.
      rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q20, Q21, Q24, Q27 in VIS1.
      eapply stage_node.
      all: try (exact VIS1).
      all: first [exact FRZ | exact KR1 | (intros X; exfalso; exact (X Hbc0)) | apply (u_bseq U) | eassumption | npre_tac].
    - destruct (@dsp_nz (PropExec.mkFP F fc) (seg_rom asegs) M1 S1 key bc R' (u_bseq U) Hbcn KR32
                  ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity) ltac:(rewrite HRe; reflexivity))
          as (R2 & pw & Hms2 & AO2 & G22 & G11 & PWR & PW2 & PW1).
      pose proof (CatSim.msteps_trans _ _ _ _ Hms Hms2) as Hms12.
      pose proof SH1 as SH1'. destruct SH1' as [SHb SHn]. unfold HStmts.t3a, HStmts.t3b, HStmts.t3c in SHb, SHn. cbn [Datatypes.fst Datatypes.snd] in SHb, SHn.
      assert (SE : @LbB_NtS.SENV _ LY_A MI_A (lbl LB) M1 S1 obj bl bc key v408 v624 ents).
      { split; [exact U1|]; split; [exact KR32|];
                 split; [intros i Hi; eapply sh0_of_addressable; [exact ADH1 | change (8 * (40 / 8)) with 40; clear - Hi; lia]|];
                 split; [intros Hb i Hi; eapply sh0_of_addressable; [exact (SHb Hb) |]; replace (8 * bc / 8) with bc by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity); clear - Hi; lia|];
                 split; [intros q k v Hq i Hi; eapply sh0_of_addressable; [exact (SHn q k v Hq) | change (8 * (32 / 8)) with 32; clear - Hi; lia]|];
                 split; [exact R616a|]; split; [exact R408a|]; split; [exact R624a|]; split; [exact V408|]; split; [exact V624|]; split; [exact SPL | exact SPH]. }
      rq AO2 HRe 2%bv A2. rq AO2 HRe 9%bv A9. rq AO2 HRe 18%bv A18. rq AO2 HRe 17%bv A17. rq AO2 HRe 16%bv A16. rq AO2 HRe 27%bv A27.
      destruct (@LbB_NtS.emp_from_bb (PropExec.mkFP F fc) _ LY_A MI_A (seg_rom asegs) (lbl LB) M1 S1 obj bl bc key v408 v624 ents R2 pw SE Hbcn
                  A2 A9 A18 A17 A16 A27 G22 G11 PWR PW2 PW1) as [R3 [(r & EF & Hms3 & AO3 & G23 & G19 & G26) | (Hms3 & AO3)]].
      + destruct EF as [v Hin]. destruct (in_split _ _ Hin) as (l1 & l2 & He).
        pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 8%bv B8. rq2 AO3 AO2 HRe 9%bv B9.
        rq2 AO3 AO2 HRe 20%bv B20. rq2 AO3 AO2 HRe 24%bv B24.
        rewrite B2, B3, B4, B8, B9, B20, B24, G19, G23, G26 in VIS1.
        eapply stage_found with (p := r) (v0 := v) (l1 := l1) (l2 := l2) (LB' := LB) (LBm' := LBm) (j584 := j584) (j592 := j592).
        all: try (exact VIS1).
        all: first [exact FRZ | exact KR1 | exact He | exact WS1 | (apply Z.le_ge; apply Z.le_refl) | eassumption].
      + pose proof (CatSim.msteps_trans _ _ _ _ Hms12 Hms3) as Hms13.
        eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms13 |].
        intros msF1 mo1 KR1 MP1 VIS1.
        rq2 AO3 AO2 HRe 2%bv B2. rq2 AO3 AO2 HRe 3%bv B3. rq2 AO3 AO2 HRe 4%bv B4. rq2 AO3 AO2 HRe 8%bv B8. rq2 AO3 AO2 HRe 9%bv B9.
        rq2 AO3 AO2 HRe 18%bv B18. rq2 AO3 AO2 HRe 20%bv B20. rq2 AO3 AO2 HRe 21%bv B21. rq2 AO3 AO2 HRe 24%bv B24. rq2 AO3 AO2 HRe 27%bv B27.
        pose proof (AO3 (22%bv : reg) ltac:(inb)) as B22. rewrite G22 in B22.
        rewrite B2, B3, B4, B8, B9, B18, B20, B21, B24, B27, B22 in VIS1.
        eapply stage_node.
        all: try (exact VIS1).
        all: first [exact FRZ | exact KR1 | (intros _; reflexivity) | apply (u_bseq U) | eassumption | npre_tac].
Qed.
End NtE.
