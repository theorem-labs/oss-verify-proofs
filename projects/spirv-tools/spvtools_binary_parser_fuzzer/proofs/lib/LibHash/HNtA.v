(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Plain.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommon OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFpu OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtCtx.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_67e94_68324.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module HNtS.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Plain.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsS1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.S1_code_67e94_68324.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition NSRCH     : Z := 0x67ed4.
Definition B5_PC     : Z := 0x67f64.
Definition LM5_PC    : Z := 0x67fa4.
Definition LP5_PC    : Z := 0x67fcc.
Definition NFOUND_PC : Z := 0x68354.
Definition NNF_PC    : Z := 0x67fdc.
Definition STOPS5 : list Z := [B5_PC; LM5_PC; LP5_PC; NFOUND_PC; NNF_PC].

Definition KN5 : list kentry :=
  [KWord (SA (EVar 34) 64) (N.to_nat 8) (ELit 0x55555555); KWord (SA (EVar 34) 56) (N.to_nat 8) (ELit 0x33333333);
   KWord (SA (EVar 34) 48) (N.to_nat 8) (ELit 0x0f0f0f0f); KWord (SA (EVar 34) 40) (N.to_nat 8) (ELit 0x01010101)].

Definition popc5 : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS5 (SCR [false; false] [EVar 35; EVar 36] [])
                          (SS NSRCH (srs sr_id [(8%bv, EVar 32); (2%bv, EVar 34); (24%bv, ELit 1)]) [] KN5 50) [] in
     sr_get (s_regs ss) 11%bv).
Definition popcw5 (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc5.

Lemma popc5_env : forall E, edenot E popc5 = popcw5 (ev E 35).
Proof. intros E. unfold popcw5, popc5. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc5 :=
  match goal with |- context [bv_unsigned (popcw5 ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw5 w)) in
    replace (bv_unsigned (popcw5 w)) with v by (vm_compute; reflexivity) end.

Lemma popcw5_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw5 (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw5 (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc5; reflexivity]
            | right; split; [lia | vm_popc5; lia] ] |]).
  destruct Hin.
Qed.

Definition nkeep_regs : list reg := [1; 3; 4; 9; 18; 19; 20; 21; 27]%bv.
Definition nkeep (R R' : bvmap 5 word) : Prop := forall r, In r nkeep_regs -> getr R' r = getr R r.

Lemma nkeep_trans : forall R1 R2 R3, nkeep R1 R2 -> nkeep R2 R3 -> nkeep R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Lemma nkeep_of_syms : forall R vals sr R',
  regs_ok (Eseed R vals) sr R' -> syms_id sr nkeep_regs = true -> nkeep R R'.
Proof. intros R vals sr R' HR Hk r Hr. exact (syms_id_sound R vals sr R' _ HR Hk r Hr). Qed.

Section SearchProof.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (parser sp bl bc key : Z) (ents : list (Z * (Z * (Z * Z * Z)))).
  Hypothesis U : umapx MI 32 (nval32 SEGS) A M (parser + 136) bl bc ents.
  Hypothesis Hkey : cell4 SEGS M (sp + 244) key.
  Hypothesis C40 : cell8 SEGS M (sp + 40) 0x01010101.
  Hypothesis C48 : cell8 SEGS M (sp + 48) 0x0f0f0f0f.
  Hypothesis C56 : cell8 SEGS M (sp + 56) 0x33333333.
  Hypothesis C64 : cell8 SEGS M (sp + 64) 0x55555555.
  Hypothesis Hsp0 : 0 < sp.
  Hypothesis Hsp1 : sp + 248 <= 2 ^ 47.
  Hypothesis Hpar : 0 <= parser.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hbc_in : In bc BSEQ := u_bseq U.
  Let Hkey_rng : 0 <= key < 2 ^ 32 := proj1 Hkey.

  Lemma bc_rng5 : 0 <= bc <= 26339969.
  Proof using AC L MI A M parser bl bc ents U. exact (BSEQ_bound bc Hbc_in). Qed.

  Lemma node_facts5 : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + 32 <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI A M parser bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at _ M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma hdaddr_cases5 : forall (l2 : list (Z * (Z * (Z * Z * Z)))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Definition sregs5 (R' : bvmap 5 word) : Prop :=
    getr R' 8%bv = Z_to_bv 64 parser /\ getr R' 2%bv = Z_to_bv 64 sp /\ getr R' 24%bv = Z_to_bv 64 1
    /\ getr R' 22%bv = Z_to_bv 64 bc /\ getr R' 23%bv = Z_to_bv 64 key.

  Lemma blkA5 : forall R,
    getr R 8%bv = Z_to_bv 64 parser -> getr R 2%bv = Z_to_bv 64 sp -> getr R 24%bv = Z_to_bv 64 1 ->
    exists R', nkeep R R' /\ sregs5 R' /\
      ( (bc = 0 /\ msteps SEGS (st R NSRCH) (st R' NNF_PC))
      \/ (bc <> 0 /\ msteps SEGS (st R NSRCH) (st R' B5_PC)
          /\ getr R' 26%bv = Z_to_bv 64 (hmod key bc) /\ getr R' 11%bv = popcw5 (Z_to_bv 64 bc)) ).
  Proof using fx AC L MI rom A M parser sp bl bc key ents U Hkey C40 C48 C56 C64 Hsp0 Hsp1 Hpar.
    intros R H8 H2 H24.
    pose proof bc_rng5 as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (h_bc (u_hdr U)) as Cbc. unfold cell8 in Cbc. replace (parser + 136 + 8) with (parser + 144) in Cbc by lia.
    pose proof Hkey as Ck. unfold cell4 in Ck.
    pose (E := Eseed R [Z_to_bv 64 parser; Z_to_bv 64 0; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (2%bv, EVar 34); (24%bv, ELit 1)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M KN5).
    { unfold KN5. repeat apply Forall_cons; try apply Forall_nil;
        (eapply (kword_var _ _ _ _ sp); [ | apply N.le_refl | evs; reflexivity | lia | lia | cbn; lia | reflexivity]);
        [exact C64 | exact C56 | exact C48 | exact C40]. }
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc5) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc5)).
    { intros b Hb. exact Hb. }
    Ltac finA HR' := eexists; split; [eapply nkeep_of_syms; [exact HR'| reflexivity]|];
      split; [unfold sregs5; repeat split;
              [ let G := fresh in rreg HR' 8%bv G; exact G | let G := fresh in rreg HR' 2%bv G; exact G
              | let G := fresh in rreg HR' 24%bv G; exact G | let G := fresh in rreg HR' 22%bv G; exact G
              | let G := fresh in rreg HR' 23%bv G; exact G ] |].
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc].
    - xrun HR HK 100%nat STOPS5 (SCR [true] [EVar 35; EVar 36] []) 50%N.
      { split_scs; try sc_auto1. }
      finA HR'. left. split; [exact Hbc0 | exact Hms].
    - destruct (popcw5_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
      +
        xrun HR HK 100%nat STOPS5 (SCR [false; false] [EVar 35; EVar 36] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc5_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        finA HR'. right. split; [exact Hbc|]. split; [exact Hms|].
        rreg HR' 26%bv H26'. split.
        * rewrite H26'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
          change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc5_env E')) end.
      + destruct (Z.ltb_spec key bc) as [Hlt|Hge].
        *
          xrun HR HK 100%nat STOPS5 (SCR [false; true; true] [EVar 35; EVar 36] []) 50%N.
          { split_scs; try sc_auto1.
            apply Hpc. rewrite popc5_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          finA HR'. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 26%bv H26'. split.
          -- rewrite H26'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc5_env E')) end.
        *
          xrun HR HK 100%nat STOPS5 (SCR [false; true; false] [EVar 35; EVar 36] []) 50%N.
          { split_scs; try sc_auto1.
            apply Hpc. rewrite popc5_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          finA HR'. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 26%bv H26'. split.
          -- rewrite H26'. unfold hmod. apply remuw_val; lia.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 11%bv) (popc5_env E')) end.
  Qed.

  Lemma blkB5 : forall R idx b q0 (w4 : word),
    getr R 8%bv = Z_to_bv 64 parser -> getr R 2%bv = Z_to_bv 64 sp -> getr R 24%bv = Z_to_bv 64 1 ->
    getr R 22%bv = Z_to_bv 64 bc -> getr R 23%bv = Z_to_bv 64 key ->
    getr R 26%bv = Z_to_bv 64 idx -> getr R 11%bv = w4 ->
    0 <= idx < bc -> bc <> 0 ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) ->
    exists R', nkeep R R' /\ sregs5 R' /\ getr R' 26%bv = Z_to_bv 64 idx /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B5_PC) (st R' NNF_PC))
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B5_PC) (st R' LM5_PC)
          /\ getr R' 25%bv = Z_to_bv 64 q0 /\ getr R' 10%bv = sxw key)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B5_PC) (st R' LP5_PC)
          /\ getr R' 25%bv = Z_to_bv 64 q0 /\ getr R' 10%bv = sxw key /\ getr R' 11%bv = Z_to_bv 64 (bc - 1)) ).
  Proof using fx AC L MI rom A M parser sp bl bc key ents U Hkey Hpar.
    intros R idx b q0 w4 H8 H2 H24 H22 H23 H26 H11 Hidx Hbc Hb Hb0 Hb1 Hq0.
    pose proof bc_rng5 as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1.
    pose proof (proj1 Hb) as Hbr. pose proof (h_bl (u_hdr U)) as Cbl. unfold cell8 in Cbl.
    pose (E := Eseed R [Z_to_bv 64 parser; w4; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 idx; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(8%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (26%bv, EVar 37); (24%bv, ELit 1)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hrd_b : forall (e ba : expr), edenot E e = Z_to_bv 64 b -> edenot E ba = Z_to_bv 64 (bl + 8 * idx) ->
      sc_denot SEGS M E (SCReadBase (SA ba 0) 8 false e)).
    { intros e ba He Hba. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      unfold adenot. cbn [a_base a_off]. rewrite Hba, v_addi_Z by lia. f_equal. lia. }
    Ltac scB Hrd_b := split_scs; try sc_auto1;
      first [ apply Hrd_b; evs; rewrite ?w_mul, ?w_add by lia; first [reflexivity | f_equal; lia]
            | eapply sc_flat; [evs; rewrite ?w_mul, ?w_add by lia; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
            | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia
            | idtac ].
    Ltac finB HR' := eexists; split; [eapply nkeep_of_syms; [exact HR'| reflexivity]|];
      split; [unfold sregs5; repeat split;
              [ let G := fresh in rreg HR' 8%bv G; exact G | let G := fresh in rreg HR' 2%bv G; exact G
              | let G := fresh in rreg HR' 24%bv G; exact G | let G := fresh in rreg HR' 22%bv G; exact G
              | let G := fresh in rreg HR' 23%bv G; exact G ] |];
      split; [let G := fresh in rreg HR' 26%bv G; exact G|].
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    - xrun HR HK 100%nat STOPS5 (SCR [true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB Hrd_b|].
      finB HR'. left. split; [left; exact Hbz | exact Hms].
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS5 (SCR [false; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB Hrd_b|].
        finB HR'. left. split; [right; exact Hqz | exact Hms].
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        * xrun HR HK 100%nat STOPS5 (SCR [false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB Hrd_b|].
          finB HR'. right; left.
          rreg HR' 25%bv G25. rreg HR' 10%bv G10.
          repeat split; try assumption. rewrite G10. apply sextw_val. lia.
        * xrun HR HK 100%nat STOPS5 (SCR [false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB Hrd_b|].
          finB HR'. right; right.
          rreg HR' 25%bv G25. rreg HR' 10%bv G10. rreg HR' 11%bv G11.
          repeat split; try assumption.
          -- rewrite G10. apply sextw_val. lia.
          -- rewrite G11. apply w_addm; lia.
  Qed.

  Definition walk5 (R : bvmap 5 word) (pc0 : Z) (R' : bvmap 5 word) : Prop :=
    nkeep R R' /\ sregs5 R' /\ getr R' 26%bv = getr R 26%bv /\
    ( (exists p v, In (p, (key, v)) ents /\ msteps SEGS (st R pc0) (st R' NFOUND_PC) /\ getr R' 25%bv = Z_to_bv 64 p)
      \/ msteps SEGS (st R pc0) (st R' NNF_PC) ).

  Ltac seed5 R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (10%bv, EVar 33); (22%bv, EVar 34); (23%bv, EVar 35); (11%bv, EVar 36); (26%bv, EVar 37);
                                        (8%bv, EVar 38); (2%bv, EVar 39); (24%bv, ELit 1)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_common HR' :=
    split; [eapply nkeep_of_syms; [exact HR'| reflexivity]|];
    split; [unfold sregs5; repeat split;
            [ let G := fresh in rreg HR' 8%bv G; exact G | let G := fresh in rreg HR' 2%bv G; exact G
            | let G := fresh in rreg HR' 24%bv G; exact G | let G := fresh in rreg HR' 22%bv G; exact G
            | let G := fresh in rreg HR' 23%bv G; exact G ] |];
    split; [let G := fresh in rreg HR' 26%bv G; rewrite G; symmetry; assumption|].
  Ltac fin_found5 HR' Hms p v He :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; fin_common HR';
      left; exists p, v; split; [rewrite He; apply in_app_iff; right; left; reflexivity|];
      split; [exact Hms | let G := fresh in rreg HR' 25%bv G; exact G]
    end.
  Ltac fin_nf5 HR' Hms :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; fin_common HR'; right; exact Hms
    end.

  Lemma loopM5 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 8%bv = Z_to_bv 64 parser -> getr R 2%bv = Z_to_bv 64 sp -> getr R 24%bv = Z_to_bv 64 1 ->
    getr R 25%bv = Z_to_bv 64 p -> getr R 10%bv = sxw key -> getr R 22%bv = Z_to_bv 64 bc ->
    getr R 23%bv = Z_to_bv 64 key -> getr R 26%bv = Z_to_bv 64 (key mod bc) -> bc <> 0 ->
    exists R', walk5 R LM5_PC R'.
  Proof using fx AC L MI rom A M parser sp bl bc key ents U Hkey.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H8 H2 H24 H25 H10 H22 H23 H26 Hbc;
      pose proof bc_rng5 as Hbcr;
      destruct (node_facts5 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      assert (H11 : getr R 11%bv = getr R 11%bv) by reflexivity;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk5.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS5 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found5 HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS5 (SCR [false; true; true; true] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1|].
             fin_nf5 HR' Hms.
          -- xrun HR HK 100%nat STOPS5 (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf5 HR' Hms.
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS5 (SCR [false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1|].
             fin_nf5 HR' Hms.
          -- xrun HR HK 100%nat STOPS5 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf5 HR' Hms.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts5 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS5 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found5 HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM5_PC) (st R1 LM5_PC) /\ nkeep R R1 /\ getr R1 26%bv = getr R 26%bv
                    /\ getr R1 8%bv = Z_to_bv 64 parser /\ getr R1 2%bv = Z_to_bv 64 sp /\ getr R1 24%bv = Z_to_bv 64 1
                    /\ getr R1 25%bv = Z_to_bv 64 p' /\ getr R1 10%bv = sxw key /\ getr R1 22%bv = Z_to_bv 64 bc
                    /\ getr R1 23%bv = Z_to_bv 64 key /\ getr R1 26%bv = Z_to_bv 64 (key mod bc)).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS5 (SCR [false; true; true; false] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1|].
               exists R'. split; [exact Hms|]. split; [eapply nkeep_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 26%bv G26. rreg HR' 8%bv G8. rreg HR' 2%bv G2. rreg HR' 24%bv G24. rreg HR' 25%bv G25. rreg HR' 10%bv G10.
               rreg HR' 22%bv G22. rreg HR' 23%bv G23.
               repeat split; try assumption. rewrite G26. symmetry. exact H26.
            -- xrun HR HK 100%nat STOPS5 (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [eapply nkeep_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 26%bv G26. rreg HR' 8%bv G8. rreg HR' 2%bv G2. rreg HR' 24%bv G24. rreg HR' 25%bv G25. rreg HR' 10%bv G10.
               rreg HR' 22%bv G22. rreg HR' 23%bv G23.
               repeat split; try assumption. rewrite G26. symmetry. exact H26. }
          destruct STEP as (R1 & Hms1 & Hk1 & Hs1 & G8 & G2 & G24 & G25 & G10 & G22 & G23 & G26).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G8 G2 G24 G25 G10 G22 G23 G26 Hbc) as (R' & Hk2 & Hsr & Hs2 & Hw).
          exists R'. split; [eapply nkeep_trans; eassumption|]. split; [exact Hsr|]. split; [rewrite Hs2; exact Hs1|].
          destruct Hw as [(q & vq & Hin & Hms2 & F25) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact F25].
          -- right. eapply msteps_trans; [exact Hms1 | exact Hms2].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; getr R 11%bv; Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS5 (SCR [false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1|].
             fin_nf5 HR' Hms.
          -- xrun HR HK 100%nat STOPS5 (SCR [false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_nf5 HR' Hms.
  Qed.

  Lemma loopP5 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 8%bv = Z_to_bv 64 parser -> getr R 2%bv = Z_to_bv 64 sp -> getr R 24%bv = Z_to_bv 64 1 ->
    getr R 25%bv = Z_to_bv 64 p -> getr R 10%bv = sxw key -> getr R 22%bv = Z_to_bv 64 bc ->
    getr R 23%bv = Z_to_bv 64 key -> getr R 26%bv = Z_to_bv 64 (key mod bc) -> getr R 11%bv = Z_to_bv 64 (bc - 1) ->
    exists R', walk5 R LP5_PC R'.
  Proof using fx AC L MI rom A M parser sp bl bc key ents U Hkey.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H8 H2 H24 H25 H10 H22 H23 H26 H11;
      destruct (node_facts5 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound key 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1 k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk5.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS5 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found5 HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS5 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf5 HR' Hms.
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS5 (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf5 HR' Hms.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts5 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS5 (SCR [true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1. sc_rd_sx Hk. }
        fin_found5 HR' Hms p v He.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS5 (SCR [false; true; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 26%bv G26. rreg HR' 8%bv G8. rreg HR' 2%bv G2. rreg HR' 24%bv G24. rreg HR' 25%bv G25. rreg HR' 10%bv G10.
          rreg HR' 22%bv G22. rreg HR' 23%bv G23. rreg HR' 11%bv G11.
          pose proof (nkeep_of_syms _ _ _ _ HR' eq_refl) as Hk1.
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G8 G2 G24 G25 G10 G22 G23 G26 G11) as (R'' & Hk2 & Hsr & Hs2 & Hw).
          exists R''. split; [eapply nkeep_trans; eassumption|]. split; [exact Hsr|]. split; [rewrite Hs2, G26; symmetry; exact H26|].
          destruct Hw as [(q & vq & Hin & Hms2 & F25) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms | exact Hms2] | exact F25].
          -- right. eapply msteps_trans; [exact Hms | exact Hms2].
        * seed5 R [Z_to_bv 64 p; sxw key; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); Z_to_bv 64 parser; Z_to_bv 64 sp;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS5 (SCR [false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1. cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_nf5 HR' Hms.
  Qed.

  Theorem nsearch_correct : forall R,
    getr R 8%bv = Z_to_bv 64 parser -> getr R 2%bv = Z_to_bv 64 sp -> getr R 24%bv = Z_to_bv 64 1 ->
    exists R', nkeep R R' /\ sregs5 R' /\ (bc <> 0 -> getr R' 26%bv = Z_to_bv 64 (hmod key bc)) /\
      ( (exists p v, In (p, (key, v)) ents /\ msteps SEGS (st R NSRCH) (st R' NFOUND_PC) /\ getr R' 25%bv = Z_to_bv 64 p)
        \/ msteps SEGS (st R NSRCH) (st R' NNF_PC) ).
  Proof using fx AC L MI rom A M parser sp bl bc key ents U Hkey C40 C48 C56 C64 Hsp0 Hsp1 Hpar.
    intros R H8 H2 H24.
    pose proof bc_rng5 as Hbcr. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_lo U) as Ho0.
    destruct (blkA5 R H8 H2 H24) as (R1 & Hk1 & SR1 & [[Hbc0 Hms1] | (Hbc & Hms1 & G26 & G11)]).
    { exists R1. split; [exact Hk1|]. split; [exact SR1|]. split; [intros Hne; exfalso; exact (Hne Hbc0)|]. right. exact Hms1. }
    pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod key bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).
    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents _ b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts5 l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. intros _. split; reflexivity. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql).
    destruct SR1 as (S8 & S2 & S24 & S22 & S23).
    destruct (blkB5 R1 (hmod key bc) b q0 (popcw5 (Z_to_bv 64 bc)) S8 S2 S24 S22 S23 G26 G11 ltac:(unfold hmod; lia) Hbc Hb Hb0 Hb1 Hbq)
      as (R2 & Hk2 & SR2 & G226 & [ (Hz & Hms2) | [ (Hbn & Hqn & Hw & Hms2 & F25 & F10)
                                          | (Hbn & Hqn & Hw & Hms2 & F25 & F10 & F11) ] ]).
    - exists R2. split; [eapply nkeep_trans; eassumption|]. split; [exact SR2|]. split; [intros _; exact G226|].
      right. eapply msteps_trans; [exact Hms1 | exact Hms2].
    - destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases5 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0. destruct SR2 as (T8 & T2 & T24 & T22 & T23).
      destruct (loopM5 l2 pre p k v R2 He T8 T2 T24 F25 F10 T22 T23 G226 Hbc) as (R3 & Hk3 & SR3 & Hs3 & Hw3).
      exists R3. split; [eapply nkeep_trans; [eapply nkeep_trans|]; eassumption|]. split; [exact SR3|]. split; [intros _; rewrite Hs3; exact G226|].
      destruct Hw3 as [(q & vq & Hin & Hms3 & T25) | Hms3].
      + left. exists q, vq. split; [exact Hin|]. split; [| exact T25].
        eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
      + right. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
    - assert (Hbc2 : bc = 2).
      { destruct (popcw5_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases5 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0. destruct SR2 as (T8 & T2 & T24 & T22 & T23).
      destruct (loopP5 l2 pre p k v R2 He Hbc2 T8 T2 T24 F25 F10 T22 T23 G226 F11) as (R3 & Hk3 & SR3 & Hs3 & Hw3).
      exists R3. split; [eapply nkeep_trans; [eapply nkeep_trans|]; eassumption|]. split; [exact SR3|]. split; [intros _; rewrite Hs3; exact G226|].
      destruct Hw3 as [(q & vq & Hin & Hms3 & T25) | Hms3].
      + left. exists q, vq. split; [exact Hin|]. split; [| exact T25].
        eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
      + right. eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3.
  Qed.

End SearchProof.
End HNtS.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibBudget FPSteps SumMemsetLib SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HConstsS1 HCommon HFpu HFind HBlk HNtCtx.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtA.HNtS. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import S1_code_67e94_68324.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.

Definition STOPSA : list Z := [NT_NF; NT_NEWE; NT_NEWR; NT_FLW; NT_FCVT1; NT_FCVT2; NT_GROW; NT_INS; NT_EMPTY; NT_SIZE; NT_VAL; NT_EXIT].

#[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

Section NtA.
Context {AC : AllocCeiling}.

  Variables (L : Layout) (MI : MallocIface SEGS L) (ST : StaticsIface SEGS L) (NEW_STACK DEL_STACK : Z).
  Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
  Variables (sp parser key bl bc : Z) (val : Z * Z * Z) (v2 : Z) (ents : list (Z * (Z * (Z * Z * Z)))) (K : TSet).
  Variable C : @ntctx AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K.
  #[local] Abbreviation NTS := (NT_STACK NEW_STACK DEL_STACK).
  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation live_facts' := (live_facts L MI).
  #[local] Abbreviation live_offimg' := (live_offimg L MI).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI (c_HLimg_lo C) (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST (c_HLimg_lo C) (c_HLrw_img C) (c_HLrelro_img C) (c_HLrw_relro C) (c_HLerr_rw C)).
  #[local] Abbreviation ro_clear_via_eff' := (ro_clear_via_eff L MI (c_HLimg_lo C) (c_HLerr_rw C)).
  #[local] Abbreviation agree_block_via_eff' := (agree_block_via_eff L MI (c_HLrw_img C) (c_HLerr_rw C)).
  #[local] Abbreviation own_sx_via_eff' := (own_sx_via_eff L MI ST (c_HLrw_img C)).
  #[local] Abbreviation hi_unowned' := (hi_unowned L MI (c_HLimg_lo C) (c_HLrw_img C)).
  #[local] Abbreviation obj := (parser + 136).
  #[local] Abbreviation sent := (parser + 152).
  #[local] Abbreviation W := (Wnt NEW_STACK DEL_STACK sp).
  #[local] Abbreviation base_ok := (nt_base_ok L R0 sp parser val v2).
  #[local] Abbreviation pframe := (nt_pframe sp parser key).
  #[local] Abbreviation SPF := (sp_facts C).
  #[local] Abbreviation BCF := (bc_facts C).
  #[local] Ltac ctx := ntctx_pose C.

  Lemma phaseV : forall R (p : Z) (v0 : Z * Z * Z) (l1 l2 : list ent),
    base_ok R -> getr R 27%bv = Z_to_bv 64 (t3c val) -> getr R 25%bv = Z_to_bv 64 p ->
    ents = l1 ++ (p, (key, v0)) :: l2 ->
    srealizes SEGS (cfg fx R NT_VAL M0 model0) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros R p v0 l1 l2 B Q27 Q25 HE.
    destruct SPF as (_ & Hsplo & Hsphi & Hn16 & _ & _ & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    assert (Hin : In (p, (key, v0)) ents) by (rewrite HE; apply in_app_iff; right; left; reflexivity).
    destruct (u_node U0 p key v0 Hin) as (Hlv & Hp0 & Hp1 & Hpal & Ch & Ck & Hkr & Hnv & Hpo & Hpb).
    destruct (live_facts' A0 M0 model0 p 32 AI0 Hlv) as (_ & _ & Hpc & Hall).
    assert (DEFp : defined M0 p 32) by (intros i Hi; exact (proj2 (Hall (p + i) ltac:(lia)))).
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 (t3a val); Z_to_bv 64 v2; Z_to_bv 64 (t3c val); Z_to_bv 64 sp]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (21%bv, EVar 33); (18%bv, EVar 34); (27%bv, EVar 35); (2%bv, EVar 36)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M0 []) by constructor.
    xruns HR HK 100%nat STOPSA (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; sc_so; eapply (defined_sub _ _ _ _ _ DEFp); lia. }
    postrun. rewrite (w2lb4_low v2), Hv2m.
    set (M1 := wbytes (wbytes (wbytes M0 _ _) _ _) _ _).
    assert (HM1w : forall a : word, ~ (p + 20 <= bv_unsigned a < p + 32) -> M1 a = M0 a).
    { intros a Ha. pose proof (u64_range a). unfold M1.
      rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 4) with 4; lia. }
    assert (HM1g : forall a : word, M0 a <> None -> M1 a <> None) by (intros a Ha; unfold M1; repeat apply wbytes_grows; exact Ha).
    assert (AI1 : ainv MI A0 M1 model0).
    { eapply (ai_frame MI); [exact AI0 | | exact HM1g | reflexivity | reflexivity].
      intros x Ho. pose proof (u64_range x). apply HM1w; intros Hx. exact (proj1 (Hall (bv_unsigned x) ltac:(lia)) Ho). }
    assert (EF1 : eff MI A0 A0 M0 M1 W (fun a => p + 20 <= a < p + 32)).
    { apply eff_store; [| exact HM1g]. intros x HF _. apply HM1w. exact HF. }
    assert (FOFF : forall a, p + 20 <= a < p + 32 -> ~ in_ranges (ly_img L) a) by (intros a Ha; exact (live_offimg' A0 M0 model0 p 32 a AI0 Hlv ltac:(lia))).
    apply (CONT fx A0 R' M1 model0 p bl bc (l1 ++ (p, (key, val)) :: l2) false false AI1 MS0 eq_refl eq_refl).
    - eapply (sx_inv_via_eff' s A0 A0 M0 M1 model0 W _ SX0 AI0 EF1 Hown_sx Herr_sx FOFF). unfold Wnt. cbn. lia.
    - exact FRM.
    - apply (kept_of_base C).
      + unfold nt_base_ok. rreg HR' 2%bv Q2. rreg HR' 21%bv Q21. rreg HR' 18%bv Q18. rewrite Q2, Q21, Q18.
        rewrite !(syms_id_sound _ _ _ _ [3; 4; 8; 24]%bv HR' eq_refl) by inl.
        repeat split; try assumption; try reflexivity.
        intros r Hr. rewrite (syms_id_sound _ _ _ _ [9; 19; 20]%bv HR' eq_refl r Hr). apply Bs. exact Hr.
      + rreg HR' 27%bv Q. exact Q.
    - rreg HR' 25%bv Q. exact Q.
    -
      assert (HM1n : forall q kq vq, In (q, (kq, vq)) ents -> q <> p -> agree_on M0 M1 q 32).
      { intros q kq vq Hq Hne i Hi. apply HM1w. rewrite u64_of_Z by (destruct (u_node U0 q kq vq Hq) as (_ & ? & ? & _); lia).
        pose proof (u_napart U0 q p ltac:(apply in_map_iff; exists (q, (kq, vq)); split; [reflexivity | exact Hq]) ltac:(apply in_map_iff; exists (p, (key, v0)); split; [reflexivity | exact Hin]) Hne) as Hap.
        unfold apart in Hap. lia. }
      pose proof (u_nodup U0) as ND. apply base.NoDup_ListNoDup in ND. rewrite HE, map_app in ND. cbn in ND.
      destruct U0 as [HD Hoal Holo Hohi Hbseq Hload Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
      assert (Hfst : map fst (l1 ++ (p, (key, val)) :: l2) = map fst (l1 ++ (p, (key, v0)) :: l2)) by (rewrite !map_app; reflexivity).
      assert (Hlen : Zlength (l1 ++ (p, (key, val)) :: l2) = Zlength (l1 ++ (p, (key, v0)) :: l2)) by (unfold Zlength; rewrite !length_app; reflexivity).
      assert (AGh : agree_on M0 M1 obj 40) by (intros i Hi; apply HM1w; rewrite u64_of_Z by lia; unfold apart in Hpo; lia).
      constructor.
      + destruct HD as [C1 C2 C3 C4 C5 C6]. constructor.
        * eapply cellw_agree; [exact C1 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
        * eapply cellw_agree; [exact C2 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
        * replace (hdaddr (l1 ++ (p, (key, val)) :: l2)) with (hdaddr ents) by (rewrite HE; destruct l1 as [|[? ?] ?]; reflexivity).
          eapply cellw_agree; [exact C3 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
        * rewrite Hlen, <- HE. eapply cellw_agree; [exact C4 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
        * eapply cellw_agree; [exact C5 | eapply agree_on_sub; [exact AGh | lia | cbn; lia] | lia | cbn; lia].
        * intros i Hi. apply HM1g. apply C6. exact Hi.
      + exact Hoal. + exact Holo. + exact Hohi. + exact Hbseq.
      + rewrite Hlen, <- HE. exact Hload.
      + exact Hblive. + exact Hblal. + exact Hbllo. + exact Hblhi. + exact Hblobj.
      + intros i Hi. destruct (Hbkt i Hi) as (b' & Cb' & Hok'). exists b'. split.
        * eapply cellw_agree; [exact Cb' | | pose proof (Hbllo ltac:(lia)); lia | cbn; lia]. intros j Hj. apply HM1w. rewrite u64_of_Z by (pose proof (Hbllo ltac:(lia)); lia).
          pose proof (Hpb ltac:(lia)) as Hap. unfold apart in Hap. lia.
        * destruct Hok' as [H0 | [Hn | (Hs & Hne & Hi')]]; [left; exact H0 | right; left; rewrite Hfst, <- HE; exact Hn | right; right].
          split; [exact Hs|]. split; [destruct l1; discriminate|]. rewrite Hi', HE. destruct l1 as [|[? [? ?]] ?]; reflexivity.
      + rewrite Hfst, <- HE. exact Hndup.
      + rewrite HE in Hch. apply (chain_agree SEGS _ M0 M1) with (ents := l1 ++ (p, (key, v0)) :: l2) in Hch.
        2:{ intros q kq vq Hq. rewrite <- HE in Hq. destruct (Hnode q kq vq Hq) as (_ & Hq0 & Hq1 & _). split; [|lia].
            destruct (Z.eq_dec q p) as [->|Hne]; [intros i Hi; apply HM1w; rewrite u64_of_Z by lia; lia | eapply agree_on_sub; [exact (HM1n q kq vq Hq Hne) | lia | lia]]. }
        revert Hch. clear. generalize l1. intros l0. induction l0 as [|[q [kq vq]] l0 IH]; intros Hc; cbn in *.
        * destruct l2 as [|[? [? ?]] ?]; exact Hc.
        * destruct Hc as [Hc1 Hc2]. split; [| exact (IH Hc2)]. destruct l0 as [|[? [? ?]] ?]; exact Hc1.
      + intros q kq vq Hq. apply in_app_iff in Hq.
        assert (Hq' : In (q, (kq, vq)) ents /\ q <> p \/ (q = p /\ kq = key /\ vq = val)).
        { destruct Hq as [Hq | [Hq | Hq]].
          - left. split; [rewrite HE; apply in_app_iff; left; exact Hq|]. intros ->. eapply (nodup_app_ne_z _ _ p p ND); [apply in_map_iff; exists (p, (kq, vq)); split; [reflexivity| exact Hq] | left; reflexivity | reflexivity].
          - injection Hq as <- <- <-. right. repeat split; reflexivity.
          - left. split; [rewrite HE; apply in_app_iff; right; right; exact Hq|]. intros ->.
            apply NoDup_app_remove_l in ND. inversion ND as [|x l Hni Hnd]. subst. apply Hni. apply in_map_iff. exists (p, (kq, vq)). split; [reflexivity | exact Hq]. }
        clear Hq. destruct Hq' as [[Hq Hne] | (-> & -> & ->)].
        * destruct (Hnode q kq vq Hq) as (Hlv' & Hq0 & Hq1 & Hqal & Hh & Hk & Hkr' & Hv & Hqo & Hqb). pose proof (HM1n q kq vq Hq Hne) as AG.
          split; [exact Hlv'|]. split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqal|].
          split; [eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
          split; [eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
          split; [exact Hkr'|]. split; [eapply nval32_agree; [exact Hv | eapply agree_on_sub; [exact AG | lia | lia] | lia | lia]|].
          split; [exact Hqo | exact Hqb].
        * split; [exact Hlv|]. split; [exact Hp0|]. split; [exact Hp1|]. split; [exact Hpal|].
          split; [eapply cellw_agree; [exact Ch | intros i Hi; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia]|].
          split; [eapply cellw_agree; [exact Ck | intros i Hi; apply HM1w; rewrite u64_of_Z by lia; lia | lia | cbn; lia]|].
          split; [exact Hkr|]. split; [| split; [exact Hpo | exact Hpb]].
          generalize Hv1 Hv2 Hv3. destruct val as [[va vb] vc]. unfold nval32, cell4, M1. cbn [t3a t3b t3c fst snd]. intros Hva Hvb Hvc.
          split; [|split]; cellpeel.
      + rewrite Hfst, <- HE. exact Hapart.
    - apply in_app_iff. right. left. reflexivity.
    - intros _. exists v0, l1, l2. split; [exact HE|]. split; reflexivity.
    - intros HT. discriminate HT.
    - intros _. split; reflexivity.
    - intros HT. discriminate HT.
    - cbn. reflexivity.
    - unfold Wnt in EF1. eapply eff_weaken; [exact EF1|]. intros a Ha. cbv beta in Ha. left. right. right. exists p. split; [apply in_map_iff; exists (p, (key, v0)); split; [reflexivity | exact Hin] | lia].
    - intros i Hi. apply HM1g. exact (so8_defined C i Hi).
  Qed.

  Record nst (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := NST {
    n_ai : ainv MI A M model;
    n_ms : mstd model;
    n_fs : m_fs model = m_fs model0;
    n_fds : m_fds model = m_fds model0;
    n_sx : sx_inv ST s M;
    n_regs : base_ok R;
    n_s6 : getr R 22%bv = Z_to_bv 64 bc;
    n_s7 : getr R 23%bv = Z_to_bv 64 key;
    n_s10 : bc <> 0 -> getr R 26%bv = Z_to_bv 64 (hmod key bc);
    n_s11 : getr R 27%bv = Z_to_bv 64 (t3c val);
    n_a0 : getr R 10%bv = Z_to_bv 64 p;
    n_frame : pframe M;
    n_def8 : defined M (sp + 8) 8;
    n_defw : defined M (sp - NTS) NTS;
    n_eff : eff MI A0 A M0 M W (fun a => p <= a < p + 32);
    n_ladd : live_add p 32 (live MI A0) (live MI A);
    n_p0 : 0 < p; n_pc : p + 32 <= alloc_ceiling; n_pal : p mod 16 = 0;
    n_U : umapx MI 32 (nval32 SEGS) A M obj bl bc ents;
    n_roc : ro_clear L M
  }.

  Lemma phaseN : forall R,
    base_ok R -> getr R 22%bv = Z_to_bv 64 bc -> getr R 23%bv = Z_to_bv 64 key ->
    (bc <> 0 -> getr R 26%bv = Z_to_bv 64 (hmod key bc)) -> getr R 27%bv = Z_to_bv 64 (t3c val) ->
    (forall p A2 M2 model2 R2, nst p A2 M2 model2 R2 -> srealizes SEGS (cfg fx R2 NT_NEWR M2 model2) K) ->
    srealizes SEGS (cfg fx R NT_NF M0 model0) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros R B Q22 Q23 Q26 Q27 POST.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    pose proof (iroc0 C) as IROC0. pose proof (so8_defined C) as DEF8. pose proof (win_defined C) as DEFW.
    destruct ASPT as (_ & _ & Ho1). destruct ASP8 as (_ & _ & Ho8). destruct ASP24 as (_ & _ & Ho24). destruct ASP244 as (_ & _ & Ho244).
    pose (E := Eseed R [Z_to_bv 64 sp]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M0 []) by constructor.
    xruns HR HK 100%nat STOPSA (SCR [] [] []) 50%N; [split_scs; try sc_auto1|].
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
    rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 10%bv G10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
    replace (Z_to_bv 64 941532) with (Z_to_bv 64 (ly_new L) : word) by (rewrite HLnew; reflexivity).
    eapply (NEW fx A0 s Rc M0 model0 32 sp NT_NEWR K AI0 MS0 IROC0 SX0 SXH).
    - constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold NT_NEWR; lia | rewrite G2; reflexivity
                   | exact Hsp16' | lia | rewrite Gs by inl; exact B3 | rewrite Gs by inl; exact B4].
    - exact G10.
    - unfold LIB_NMAX in HNMAX. lia.
    - lia.
    - apply stack_room_of_defined; [lia | lia | lia |]. eapply defined_sub; [exact DEFW | lia | lia].
    - intros a Ha. apply Hwin. unfold zwin in Ha |- *. lia.
    - exact Hown_sx.
    - exact Herr_sx.
    - replace (new_size 32) with 32 by reflexivity.
      eapply roomL_room_for; [exact AI0 | unfold LIB_NMAX in HNMAX; lia | exact ROOM1].
    -
      intros A1 R2 M2 model1 p AI2 MS1 Hfs1 Hfds1 SX2 KEPT R1a0 Hp LADD CAPS BIGC NEWT FR2 DEF2.
      replace (new_size 32) with 32 in LADD, FR2 by reflexivity.
      assert (EFF : eff MI A0 A1 M0 M2 (sp - NEW_STACK, sp) (fun a => p <= a < p + 32)).
      { eapply (eff_of_new MI A0 A1 M0 M2 model1); [exact AI2 | exact CAPS | exact BIGC | exact NEWT | exact FR2 | exact DEF2 | intros a Ha; exact Ha | intros a Ha; exact Ha]. }
      assert (HinP : In (p, 32) (live MI A1)) by (rewrite (proj1 LADD); left; reflexivity).
      destruct (ai_live_block MI A1 M2 model1 p 32 AI2 HinP) as (_ & Hpal & Hp0 & Hpc & Hpown).
      assert (EFF2 : eff MI A0 A1 M0 M2 W (fun a => p <= a < p + 32)).
      { eapply eff_widen; [exact EFF|]. intros a Ha. unfold W_of, Wnt in Ha |- *. cbn [fst snd] in Ha |- *. lia. }

      assert (AGa : forall a n, sp <= a -> a + n <= 2 ^ 47 -> 0 <= n -> (forall i, 0 <= i < n -> ~ owned MI A0 (a + i)) -> defined M0 a n -> agree_on M0 M2 a n).
      { intros a n Ha Han Hn Hown Hdef. eapply (agree_above_via_eff' A0 A1 M0 M2 _ _ a n sp EFF); [lia | cbn; lia | lia | lia | lia | exact Hown | exact Hdef |].
        intros i Hi Hf. cbn beta in Hf. lia. }
      apply (POST p A1 M2 model1 R2). constructor;
        [ exact AI2 | exact MS1 | exact Hfs1 | exact Hfds1 | exact SX2 | | | | | | exact R1a0 | | | | exact EFF2 | exact LADD | exact Hp | exact Hpc | exact Hpal | | ].
      + unfold nt_base_ok. rewrite !(KEPT _) by inl. rewrite G2, !Gs by inl.
        split; [reflexivity|]. split; [exact B3|]. split; [exact B4|]. split; [exact B8|]. split; [exact B24|]. split; [exact B21|]. split; [exact B18|].
        intros r Hr. rewrite (KEPT r); [rewrite Gs; [apply Bs; exact Hr|]|]; cbn in Hr; unfold callee_saved; cbn; clear - Hr; intuition congruence.
      + rewrite (KEPT 22%bv) by inl. rewrite Gs by inl. exact Q22.
      + rewrite (KEPT 23%bv) by inl. rewrite Gs by inl. exact Q23.
      + intros Hbc. rewrite (KEPT 26%bv) by inl. rewrite Gs by inl. exact (Q26 Hbc).
      + rewrite (KEPT 27%bv) by inl. rewrite Gs by inl. exact Q27.
      + destruct (pframe0 C) as (F1 & F2 & F3 & F4 & F5 & F6). unfold nt_pframe.
        assert (AG244 : agree_on M0 M2 (sp + 244) 4) by (apply AGa; [lia | lia | lia | exact Ho244 | exact (cellw_high_defined M0 (sp + 244) 4 _ F1 ltac:(lia) ltac:(cbn; lia))]).
        assert (AGc : forall a v, cell8 SEGS M0 a v -> sp + 24 <= a -> a + 8 <= sp + 72 -> cell8 SEGS M2 a v).
        { intros a v F Ha1 Ha2. eapply cellw_agree; [exact F | | lia | cbn; lia].
          apply AGa; [lia | lia | lia | | exact (cellw_high_defined M0 a 8 _ F ltac:(lia) ltac:(cbn; lia))].
          intros i Hi. replace (a + i) with (sp + 24 + (a - sp - 24 + i)) by lia. apply Ho24. lia. }
        split; [eapply cellw_agree; [exact F1 | exact AG244 | lia | cbn; lia] |].
        split; [|split; [|split; [|split]]]; (apply AGc; [assumption | lia | lia]).
      + intros i Hi. rewrite (AGa (sp + 8) 8 ltac:(lia) ltac:(lia) ltac:(lia) Ho8 DEF8 i Hi). apply DEF8. exact Hi.
      + eapply (defined_via_eff L MI HLimg_lo HLrw_img HLerr_rw A0 A1 M0 M2 _ _ (sp - NTS) NTS EFF ltac:(lia) ltac:(cbn; lia)).
        * intros i Hi. eapply hi_unowned'; [exact AI0 | lia].
        * intros i Hi Hf. cbn beta in Hf. lia.
        * exact DEFW.
      +
        eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 32 (Z * Z * Z)%type (nval32 SEGS) ltac:(lia) (nval32_agree SEGS) A0 A1 M0 M2 model0 obj bl bc ents W _ sp U0 AI0 EFF2).
        * lia. * unfold Wnt; cbn; lia. * lia.
        * exact Ho1.
        * intros a Ha Hpa. exact (foot_apart_new C A1 M2 model1 p 32 a AI2 LADD Ha Hpa).
        * unfold Wnt; cbn; lia.
        * intros q m Hb Hl. rewrite (proj1 LADD). right. exact Hl.
      + eapply (ro_clear_via_eff' A0 A1 M0 M2 model0 W _ ROC AI0 EFF2); [| unfold Wnt; cbn; lia].
        intros a Ha. exact (live_offimg' A1 M2 model1 p 32 a AI2 HinP Ha).
  Qed.

  Record core (p : Z) (A : AS MI) (M : mem) (model : Model) (R : bvmap 5 word) : Prop := CORE {
    k_ai : ainv MI A M model;
    k_ms : mstd model;
    k_fs : m_fs model = m_fs model0;
    k_fds : m_fds model = m_fds model0;
    k_sx : sx_inv ST s M;
    k_regs : base_ok R;
    k_s7 : getr R 23%bv = Z_to_bv 64 key;
    k_s9 : getr R 25%bv = Z_to_bv 64 p;
    k_frame : pframe M;
    k_def8 : defined M (sp + 8) 8;
    k_defw : defined M (sp - NTS) NTS;
    k_p0 : 0 < p; k_pc : p + 32 <= alloc_ceiling; k_pal : p mod 16 = 0;
    k_plive : In (p, 32) (live MI A);
    k_pnew : ~ In p (map fst (live MI A0));
    k_nh : cell8 SEGS M (p + 8) key;
    k_nk : cell4 SEGS M (p + 16) key;
    k_pdef : defined M p 32
  }.

#[local] Definition HTHNtA_0 : list (reg * expr) := [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37); (10%bv, EVar 38)].
  Lemma phaseI : forall p A M model R,
    nst p A M model R ->
    (forall (fx1 : FPState) M' R',
        core p A M' model R' -> getr R' 22%bv = Z_to_bv 64 bc -> (bc <> 0 -> getr R' 26%bv = Z_to_bv 64 (hmod key bc)) ->
        getr R' 27%bv = Z_to_bv 64 (t3c val) ->
        frm_zero (@fp_csr fx1) -> fholds fx1 14%bv (ieee (Zlength ents + 1)) -> fholds fx1 15%bv one32 ->
        (bc = 0 \/ Zlength ents = bc) ->
        eff MI A0 A M0 M' W (fun a => p <= a < p + 32) -> live_add p 32 (live MI A0) (live MI A) ->
        umapx MI 32 (nval32 SEGS) A M' obj bl bc ents -> ro_clear L M' ->
        srealizes SEGS (cfg fx1 R' NT_GROW M' model) K) ->
    (forall (fx1 : FPState) M' R',
        core p A M' model R' -> frm_zero (@fp_csr fx1) -> bc <> 0 -> Zlength ents + 1 <= bc ->
        getr R' 22%bv = Z_to_bv 64 bc -> getr R' 26%bv = Z_to_bv 64 (hmod key bc) -> getr R' 27%bv = Z_to_bv 64 (t3c val) ->
        eff MI A0 A M0 M' W (fun a => p <= a < p + 32) -> live_add p 32 (live MI A0) (live MI A) ->
        umapx MI 32 (nval32 SEGS) A M' obj bl bc ents -> ro_clear L M' ->
        srealizes SEGS (cfg fx1 R' NT_INS M' model) K) ->
    srealizes SEGS (cfg fx R NT_NEWR M model) K.
  Proof using AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K C.
    ctx. intros p A M model R NS PRH PINS.
    destruct SPF as (Hsp16' & Hsplo & Hsphi & Hn16 & HnN & HnD & Hs1 & Hpar). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
    destruct BCF as (HbB & Hbcr & Hload & Hsz0).
    destruct NS as [AI MS Hfs Hfds SX B Q22 Q23 Q26 Q27 Q10 FR DEF8 DEFW EFF LADD Hp0 Hpc Hpal U RC].
    pose proof B as B'. destruct B' as (B2 & B3 & B4 & B8 & B24 & B21 & B18 & Bs).
    pose proof (proj1 (nf_key _ _ _ _ _ _ _ _ _ NF)) as Hkr. cbn in Hkr.
    pose proof (u_obj_lo U) as Hobjlo. pose proof (u_obj_hi U) as Hobjhi.
    assert (HinP : In (p, 32) (live MI A)) by (rewrite (proj1 LADD); left; reflexivity).
    destruct (live_facts' A M model p 32 AI HinP) as (_ & _ & _ & Hpall).
    assert (DEFp : defined M p 32) by (intros i Hi; exact (proj2 (Hpall (p + i) ltac:(lia)))).
    pose proof (u_hdr U) as HD. destruct HD as [Cbl Cbc Cp1 Csz Cmlf Cdef].
    unfold cell8 in Csz. unfold cell4 in Cmlf.

    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 (Zlength ents)]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KDisj (SA (EVar 32) 0) (ELit 32) (SA (EVar 33) 136) (ELit 40)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }
    xruns HR HK 100%nat STOPSA (SCR [] [EVar 38] []) 50%N.
    { split_scs; try sc_auto1; sc_so; eapply (defined_sub _ _ _ _ _ DEFp); lia. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRa; rename Rx into Ra end.
    set (M3 := wbytes _ _ _).
    rreg HRa 8%bv Qa8. rreg HRa 2%bv Qa2. rreg HRa 10%bv Qa10. rreg HRa 25%bv Qa25. rreg HRa 22%bv Qa22. rreg HRa 23%bv Qa23. rreg HRa 27%bv Qa27.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 24; 26]%bv HRa eq_refl) as Pa.
    assert (Ba : base_ok Ra) by (nt_base_from HRa B). clear HRa HR HK.

    assert (HM3w : forall a : word, ~ (p <= bv_unsigned a < p + 24) -> M3 a = M a).
    { intros a Ha. pose proof (u64_range a). unfold M3.
      rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia. }
    assert (HM3g : forall a : word, M a <> None -> M3 a <> None) by (intros a Ha; unfold M3; repeat apply wbytes_grows; exact Ha).
    assert (Cmlf3 : cellw SEGS M3 (parser + 168) 4 0x3f800000).
    { replace (parser + 168) with (obj + 32) by lia. eapply cellw_agree; [exact Cmlf | | lia | cbn; lia]. intros i Hi. apply HM3w. rewrite u64_of_Z by lia. lia. }
    pose proof Cmlf3 as Cmlf3'. destruct Cmlf3' as [_ Rmlf3].

    fp_flw MS F_67fbc D_67fbc Qa8 Rmlf3 168 0x68000.

    pose (E := Eseed Ra [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 (Zlength ents)]).
    assert (HR : regs_ok E (srs sr_id HTHNtA_0) Ra).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M3 []) by constructor.
    assert (DEFp3 : defined M3 p 32) by (intros j Hj; apply HM3g; apply DEFp; exact Hj).
    xruns HR HK 100%nat STOPSA (SCR [] [] []) 50%N.
    { split_scs; try sc_auto1; sc_so; eapply (defined_sub _ _ _ _ _ DEFp3); lia. }
    postrun.
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRb; rename Rx into Rb end.
    set (M5 := wbytes _ _ _).
    rreg HRb 8%bv Qb8. rreg HRb 2%bv Qb2. rreg HRb 10%bv Qb10. rreg HRb 25%bv Qb25. rreg HRb 22%bv Qb22. rreg HRb 23%bv Qb23. rreg HRb 27%bv Qb27.
    rewrite w_add in Qb10 by lia.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 24; 26]%bv HRb eq_refl) as Pb.
    assert (Bb : base_ok Rb) by (nt_base_from HRb Ba). clear HRb HR HK.

    assert (HM5w : forall a : word, ~ (p <= bv_unsigned a < p + 32) -> M5 a = M a).
    { intros a Ha. pose proof (u64_range a). unfold M5.
      rewrite 2!wbytes_outside; [apply HM3w; lia| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; try (change (Z.of_nat 8) with 8); try (change (Z.of_nat 4) with 4); lia. }
    assert (HM5g : forall a : word, M a <> None -> M5 a <> None) by (intros a Ha; unfold M5, M3; repeat apply wbytes_grows; exact Ha).
    assert (HM5a : forall a k, 0 <= a -> a + k <= 2 ^ 47 -> apart a k p 32 -> agree_on M M5 a k).
    { intros a k Ha Hak H1 i Hi. apply HM5w; rewrite u64_of_Z by lia; clear - H1 Hi; unfold apart in *; lia. }
    assert (AI5 : ainv MI A M5 model).
    { eapply (ai_frame MI); [exact AI | | exact HM5g | reflexivity | reflexivity].
      intros x Ho. pose proof (u64_range x). apply HM5w; intros Hx. exact (proj1 (Hpall (bv_unsigned x) Hx) Ho). }
    assert (EFF5 : eff MI A0 A M0 M5 W (fun a => p <= a < p + 32)).
    { eapply eff_weaken; [eapply eff_trans; [exact EFF | | intros a Ha; eapply hi_unowned'; [exact AI5 | unfold W_of, Wnt in Ha; cbn in Ha; lia]]|].
      - eapply eff_store with (F := fun a : Z => p <= a < p + 32); [| exact HM5g]. intros x HF _. apply HM5w. exact HF.
      - intros a [Ha|Ha]; exact Ha. }
    assert (U5 : umapx MI 32 (nval32 SEGS) A M5 obj bl bc ents).
    { eapply (umapx_agree SEGS L MI 32 _ (nval32 SEGS) (nval32_agree SEGS) ltac:(lia) A A M M5); [exact U | | intros; assumption].
      intros a Ha. pose proof (foot_low_or_high_gen C A M model bl bc ents a AI U Ha). apply HM5w. rewrite u64_of_Z by lia. exact (foot_apart_new C A M model p 32 a AI LADD Ha). }
    assert (RC5 : ro_clear L M5).
    { eapply (ro_clear_frame L (fun a => p <= a < p + 32) M M5 RC).
      - intros x Hn. apply HM5w. exact Hn.
      - intros a Hro Ha. exact (live_offimg' A M model p 32 a AI HinP Ha (proj1 Hro)). }
    assert (SX5 : sx_inv ST s M5).
    { eapply (sx_inv_via_eff' s A A M M5 model W (fun a => p <= a < p + 32) SX AI); [| | exact Herr_sx | | unfold Wnt; cbn; lia].
      - apply eff_store; [| exact HM5g]. intros x HF _. apply HM5w. exact HF.
      - exact (own_sx_via_eff' A0 A M0 M W _ EFF Hown_sx (fun a Ha => live_offimg' A M model p 32 a AI HinP Ha)).
      - intros a Ha. exact (live_offimg' A M model p 32 a AI HinP Ha). }
    assert (C5 : forall (Rx : bvmap 5 word), base_ok Rx -> getr Rx 23%bv = Z_to_bv 64 key -> getr Rx 25%bv = Z_to_bv 64 p -> core p A M5 model Rx).
    { intros Rx HB Q23' Q25'. constructor;
        [ exact AI5 | exact MS | exact Hfs | exact Hfds | exact SX5 | exact HB | exact Q23' | exact Q25' | | | | exact Hp0 | exact Hpc | exact Hpal | exact HinP | exact (proj2 LADD) | | | ].
      - destruct FR as (F1 & F2 & F3 & F4 & F5 & F6). unfold nt_pframe.
        split; [|split; [|split; [|split; [|split]]]]; (eapply cellw_agree; [| apply HM5a; [lia | lia | unfold apart; lia] | lia | cbn; lia]); assumption.
      - intros i Hi. apply HM5g. apply DEF8. exact Hi.
      - intros i Hi. apply HM5g. apply DEFW. exact Hi.
      - unfold M5, M3, cell8. cellpeel. - unfold M5, M3, cell4. cellpeel.
      - intros i Hi. apply HM5g. apply DEFp. exact Hi. }

    fp_fcvt_s_lu MS F_67fcc D_67fcc FRM Qb10 (Zlength ents + 1) 0x68010.
    pose proof (ieee_range (Zlength ents + 1) ltac:(lia)) as Hie1.
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
      assert (Hf14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_same; lia);
      assert (Hf15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | apply fholds_set_same; unfold one32; lia]) end.

    pose (E := Eseed Rb [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 (Zlength ents + 1)]).
    assert (HR : regs_ok E (srs sr_id HTHNtA_0) Rb).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M5 []) by constructor.
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc1].
    { xruns HR HK 100%nat STOPSA (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
      apply (PRH _ M5 R');
        [ apply C5; [nt_base_from HR' Bb | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q]
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | intros Hne; exfalso; exact (Hne Hbc0)
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | exact FRM | exact Hf14 | exact Hf15 | left; exact Hbc0 | exact EFF5 | exact LADD | exact U5 | exact RC5 ]. }
    xruns HR HK 100%nat STOPSA (SCR [false] [] []) 50%N; [split_scs; try sc_auto1|].
    lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRc; rename Rx into Rc end.
    rreg HRc 22%bv Qc22. rreg HRc 8%bv Qc8. rreg HRc 23%bv Qc23. rreg HRc 25%bv Qc25. rreg HRc 2%bv Qc2. rreg HRc 27%bv Qc27. rreg HRc 10%bv Qc10.
    pose proof (syms_id_sound _ _ _ _ [3; 4; 9; 18; 19; 20; 21; 24; 26]%bv HRc eq_refl) as Pc.
    assert (Bc : base_ok Rc) by (nt_base_from HRc Bb). clear HRc HR HK.

    fp_fcvt_s_lu MS F_67fd4 D_67fd4 FRM Qc22 bc 0x68018.
    pose proof (ieee_range bc ltac:(lia)) as Hie2.
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
      assert (Hg13 : fholds fxc 13%bv (ieee bc)) by (apply fholds_set_same; lia);
      assert (Hg15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | exact Hf15]);
      assert (Hg14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact Hf14]) end.
    fp_fari MS F_67fd8 D_67fd8 FRM Hg15 Hg13 (fun md => mul_one_val md bc) 0x6801c.
    lazymatch goal with |- srealizes _ (mkCfg (@mkst ?fxc _ _ _ _) _) _ =>
      assert (Hh13 : fholds fxc 13%bv (ieee bc)) by (apply fholds_set_same; lia);
      assert (Hh14 : fholds fxc 14%bv (ieee (Zlength ents + 1))) by (apply fholds_set_other; [intros X; discriminate X | exact Hg14]);
      assert (Hh15 : fholds fxc 15%bv one32) by (apply fholds_set_other; [intros X; discriminate X | exact Hg15]) end.
    fp_flt MS F_67fdc D_67fdc Hh13 Hh14 bc (Zlength ents + 1) 0x68020.
    set (Rd := regupd Rc 10%bv _).
    assert (Qd : forall r, r <> 10%bv -> getr Rd r = getr Rc r) by (intros r Hr; unfold Rd; apply getr_other; exact Hr).
    assert (Qd10 : getr Rd 10%bv = Z_to_bv 64 (if bc <? Zlength ents + 1 then 1 else 0)) by (unfold Rd; apply getr_same; intros X; discriminate X).
    pose proof (Qd 22%bv ltac:(intros X; discriminate X)) as Qd22. rewrite Qc22 in Qd22.
    pose proof (Qd 8%bv ltac:(intros X; discriminate X)) as Qd8. rewrite Qc8 in Qd8.
    pose proof (Qd 23%bv ltac:(intros X; discriminate X)) as Qd23. rewrite Qc23 in Qd23.
    pose proof (Qd 25%bv ltac:(intros X; discriminate X)) as Qd25. rewrite Qc25 in Qd25.
    pose proof (Qd 27%bv ltac:(intros X; discriminate X)) as Qd27. rewrite Qc27 in Qd27.
    pose proof (Qd 2%bv ltac:(intros X; discriminate X)) as Qd2. rewrite Qc2 in Qd2.
    pose proof (Qd 26%bv ltac:(intros X; discriminate X)) as Qd26. rewrite Pc, Pb, Pa, (Q26 Hbc1) in Qd26 by inl.
    assert (Bd : base_ok Rd).
    { unfold nt_base_ok. rewrite !Qd by (intros X; discriminate X). destruct Bc as (? & ? & ? & ? & ? & ? & ? & Bcs). repeat split; try assumption.
      intros r Hr. rewrite Qd; [apply Bcs; exact Hr|]. clear - Hr. cbn in Hr. intros ->. intuition discriminate. }

    pose (E := Eseed Rd [Z_to_bv 64 p; Z_to_bv 64 parser; Z_to_bv 64 sp; Z_to_bv 64 bc; Z_to_bv 64 key; Z_to_bv 64 (t3c val); Z_to_bv 64 (if bc <? Zlength ents + 1 then 1 else 0); Z_to_bv 64 (hmod key bc)]).
    assert (HR : regs_ok E (srs sr_id [(25%bv, EVar 32); (8%bv, EVar 33); (2%bv, EVar 34); (22%bv, EVar 35); (23%bv, EVar 36); (27%bv, EVar 37); (10%bv, EVar 38); (26%bv, EVar 39)]) Rd).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M5 []) by constructor.
    destruct (Z.ltb_spec bc (Zlength ents + 1)) as [Hlt | Hge].
    -
      xruns HR HK 100%nat STOPSA (SCR [false] [] []) 50%N; [split_scs; try sc_auto1|].
      apply (PRH _ M5 R');
        [ apply C5; [nt_base_from HR' Bd | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q]
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | intros _; let Q := fresh in rreg HR' 26%bv Q; exact Q
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | exact FRM | exact Hh14 | exact Hh15 | right; lia | exact EFF5 | exact LADD | exact U5 | exact RC5 ].
    -
      xruns HR HK 100%nat STOPSA (SCR [true] [] []) 50%N; [split_scs; try sc_auto1|].
      apply (PINS _ M5 R');
        [ apply C5; [nt_base_from HR' Bd | let Q := fresh in rreg HR' 23%bv Q; exact Q | let Q := fresh in rreg HR' 25%bv Q; exact Q]
        | exact FRM | exact Hbc1 | lia
        | let Q := fresh in rreg HR' 22%bv Q; exact Q
        | let Q := fresh in rreg HR' 26%bv Q; exact Q
        | let Q := fresh in rreg HR' 27%bv Q; exact Q
        | exact EFF5 | exact LADD | exact U5 | exact RC5 ].
  Qed.

End NtA.

Arguments phaseV {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C R p v0 l1 l2 _ _ _ _.
Arguments phaseN {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C R _ _ _ _ _ _.
Arguments phaseI {AC L MI ST NEW_STACK DEL_STACK fx A0 s R0 M0 model0 sp parser key bl bc val v2 ents K} C p A M model R _ _ _.
