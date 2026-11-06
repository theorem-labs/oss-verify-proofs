(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.U1Layout OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Lib_Cxx_OperatorNewU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocIfaceStmt OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.MallocInstU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv.U1Statics.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.ContStmts2 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Facts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow_6a1b8 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow_6d794 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Vec32_PbSlow_6b2e0 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_VecOty_PushBack OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_VecOpnd_PbSlow OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Str_PushBack OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_MakeString OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.U1Lib_Cxx_OperatorDelete.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFindU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFind2U1.
From Stdlib Require NArith.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module HFindNTU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFindU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmSetNumU1.U1_code_6a5c4_6a81c.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition NTF_ENTRY : Z := 0x6a604.
Definition B3_PC     : Z := 0x6a6b0.
Definition LM3_PC    : Z := 0x6a714.
Definition LP3_PC    : Z := 0x6a744.
Definition NTF_MISS  : Z := 0x6a75c.
Definition NTF_HIT   : Z := 0x6a7c0.
Definition STOPS3 : list Z := [B3_PC; LM3_PC; LP3_PC; NTF_MISS; NTF_HIT].

Definition popc3 : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS3 (SCR [false; false] [EVar 34] [])
                          (SS NTF_ENTRY (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33)]) [] [] 50) [] in
     sr_get (s_regs ss) 16%bv).
Definition popcw3 (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc3.

Lemma popc3_env : forall E, edenot E popc3 = popcw3 (ev E 34).
Proof. intros E. unfold popcw3, popc3. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc3 :=
  match goal with |- context [bv_unsigned (popcw3 ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw3 w)) in
    replace (bv_unsigned (popcw3 w)) with v by (vm_compute; reflexivity) end.

Lemma popcw3_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw3 (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw3 (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc3; reflexivity]
            | right; split; [lia | vm_popc3; lia] ] |]).
  destruct Hin.
Qed.

Lemma sx32_sxw : forall k, 0 <= k < 2 ^ 32 -> Z_to_bv 64 (HStmts.sx32 k) = sxw k.
Proof.
  intros k Hk. unfold HStmts.sx32, sxw. rewrite bv_swrap32_cases by lia.
  apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  destruct (Z.ltb_spec k (2 ^ 31)); [reflexivity|].
  replace (k + 2 ^ 64 - 2 ^ 32) with ((k - 2 ^ 32) + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma low32_sxw : forall k, 0 <= k < 2 ^ 32 -> low32 (sxw k) = low32 (Z_to_bv 64 k).
Proof.
  intros k Hk. unfold low32, sxw. apply bv_eq. rewrite !bv_extract_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, !Z.shiftr_0_r.
  unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec k (2 ^ 31)); [reflexivity|].
  replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64).
  2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
  replace (k - 2 ^ 32 + 2 ^ 64) with (k + (2 ^ 32 - 1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. rewrite (Z.mod_small k (2 ^ 64)) by lia. reflexivity.
Qed.

Lemma zext_sxw : forall k, 0 <= k < 2 ^ 32 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296) (sxw k)) (Z_to_bv 64 32) = Z_to_bv 64 k.
Proof.
  intros k Hk. unfold sxw. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_shiftr_unsigned, bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 4294967296), (Z.mod_small 32), (Z.mod_small 63), (Z.mod_small k) by lia.
  change (Z.land 32 63) with 32. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite bv_swrap32_cases by lia. destruct (Z.ltb_spec k (2 ^ 31)).
  - rewrite (Z.mod_small k), Z.mod_small by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  - replace ((k - 2 ^ 32) mod 2 ^ 64) with (k - 2 ^ 32 + 2 ^ 64).
    2:{ rewrite <- (Z.mod_add _ 1) by lia. symmetry. apply Z.mod_small. lia. }
    replace (4294967296 * (k - 2 ^ 32 + 2 ^ 64)) with (k * 4294967296 + (4294967296 - 1) * 2 ^ 64) by lia.
    rewrite Z.mod_add, Z.mod_small by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Ltac in_bv := cbn [In]; first [left; apply bv_eq; vm_compute; reflexivity | right; in_bv].

Section NTFind.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (this bl bc tid : Z) (ents : list (Z * (Z * (Z * Z * Z)))).
  Hypothesis U : umapx MI 32 (nval32 SEGS) A M (this + 136) bl bc ents.
  Hypothesis Htid : 0 <= tid < 2 ^ 32.
  Hypothesis Hthis0 : 0 < this.
  Hypothesis Hthis1 : this + 288 <= 2 ^ 47.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hbc_in : In bc BSEQ := u_bseq U.

  Lemma bc_rng3 : 0 <= bc <= 26339969.
  Proof using AC L MI A M this bl bc ents U. exact (BSEQ_bound bc Hbc_in). Qed.

  Lemma node_facts3 : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + 32 <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI A M this bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at _ M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma node_al3 : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 -> p mod 16 = 0.
  Proof using AC L MI A M this bl bc ents U.
    intros l1 p k v l2 He. destruct (u_node U p k v) as (_ & _ & _ & Hal & _); [| exact Hal].
    rewrite He. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma hdaddr_cases3 : forall (l2 : list (Z * (Z * (Z * Z * Z)))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Definition keep3 : list reg := [1; 2; 3; 4; 7; 9; 11; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
  Definition kept3 (R R' : bvmap 5 word) : Prop :=
    (forall r, In r keep3 -> getr R' r = getr R r) /\ getr R' 13%bv = Z_to_bv 64 this /\ getr R' 8%bv = getr R 8%bv.
  Lemma kept3_trans : forall R1 R2 R3, kept3 R1 R2 -> kept3 R2 R3 -> kept3 R1 R3.
  Proof using this.
    intros R1 R2 R3 (A1 & B1 & C1) (A2 & B2 & C2). split; [| split; congruence].
    intros r Hr. rewrite (A2 r Hr). apply A1, Hr.
  Qed.
  Lemma kept3_all : forall R R', kept3 R R' -> forall r, ~ In r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r.
  Proof using this.
    intros R R' (HA & HB & HC) r Hr.
    pose proof (bv_unsigned_in_range _ r) as Hrr. change (bv_modulus 5) with 32 in Hrr.
    assert (E : r = Z_to_bv 5 (bv_unsigned r)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (Hn : exists n, (n < 32)%nat /\ bv_unsigned r = Z.of_nat n) by (exists (Z.to_nat (bv_unsigned r)); split; lia).
    destruct Hn as (n & Hn & Hzn). rewrite Hzn in E. clear Hzn Hrr. subst r.
    do 32 (destruct n as [|n];
      [ first [ apply HA; in_bv
              | etransitivity; [| exact HB]; f_equal; apply bv_eq; vm_compute; reflexivity
              | etransitivity; [| exact HC]; f_equal; apply bv_eq; vm_compute; reflexivity
              | exfalso; apply Hr; in_bv
              | unfold getr; vm_compute; reflexivity ] |]).
    lia.
  Qed.
  Ltac kept3_of HR' H10 H8 :=
    split; [exact (syms_id_sound _ _ _ _ keep3 HR' eq_refl)
          | split; [let Q := fresh in rreg HR' 13%bv Q; first [exact Q | rewrite Q; exact H10]
                   | let Q := fresh in rreg HR' 8%bv Q; rewrite Q; symmetry; exact H8]].

  Lemma blkA3 : forall R,
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    exists R', kept3 R R' /\
      ( (bc = 0 /\ msteps SEGS (st R NTF_ENTRY) (st R' NTF_MISS))
      \/ (bc <> 0 /\ msteps SEGS (st R NTF_ENTRY) (st R' B3_PC)
          /\ getr R' 10%bv = Z_to_bv 64 bc /\ getr R' 12%bv = Z_to_bv 64 tid
          /\ getr R' 14%bv = Z_to_bv 64 (hmod tid bc) /\ getr R' 16%bv = popcw3 (Z_to_bv 64 bc)) ).
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid Hthis0 Hthis1.
    intros R H10 H8. pose proof (u_hdr U) as HD. destruct HD as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng3 as Hbcr. pose proof (u_bl_hi U) as Hbl1.
    unfold cell8 in Hbl, Hbc8. pose proof (proj1 Hbl) as Hblr.
    replace (this + 136 + 8) with (this + 144) in Hbc8 by lia.
    pose (E := Eseed R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 bl]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (8%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc3) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc3)).
    { intros b Hb. exact Hb. }
    pose proof (zext_sxw tid Htid) as Hz.
    destruct (Z.eq_dec bc 0) as [Hbc0 | Hbc].
    - xrun HR HK 100%nat STOPS3 (SCR [true] [EVar 34] []) 50%N.
      { split_scs; try sc_auto1. }
      exists R'. split; [kept3_of HR' H10 H8|]. left. split; [exact Hbc0 | exact Hms].
    - destruct (popcw3_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
      +
        xrun HR HK 100%nat STOPS3 (SCR [false; false] [EVar 34] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
        rreg HR' 10%bv H12'. rreg HR' 12%bv H13'. rreg HR' 14%bv H15'.
        rewrite Hz in H13', H15'.
        repeat split; try assumption.
        * rewrite H15'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
          change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
      + destruct (Z.ltb_spec tid bc) as [Hlt|Hge].
        *
          xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 34] []) 50%N.
          { split_scs; try sc_auto1.
            - cbn [sc_denot]. evs. rewrite Hz. rewrite br_ltu by lia. bool_lia.
            - apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 10%bv H12'. rreg HR' 12%bv H13'. rreg HR' 14%bv H15'.
          rewrite Hz in H13', H15'.
          repeat split; try assumption.
          -- rewrite H15'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
        *
          xrun HR HK 100%nat STOPS3 (SCR [false; true; false] [EVar 34] []) 50%N.
          { split_scs; try sc_auto1.
            - cbn [sc_denot]. evs. rewrite Hz. rewrite br_ltu by lia. bool_lia.
            - apply Hpc. rewrite popc3_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
          exists R'. split; [kept3_of HR' H10 H8|]. right. split; [exact Hbc|]. split; [exact Hms|].
          rreg HR' 10%bv H12'. rreg HR' 12%bv H13'. rreg HR' 14%bv H15'.
          rewrite Hz in H13'.
          repeat split; try assumption.
          -- rewrite H15'. rewrite low32_sxw by lia. unfold hmod. apply remuw_val; lia.
          -- lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 16%bv) (popc3_env E')) end.
  Qed.

  Lemma blkB3 : forall R idx b q0 (w4 : word),
    getr R 13%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 10%bv = Z_to_bv 64 bc -> getr R 12%bv = Z_to_bv 64 tid ->
    getr R 14%bv = Z_to_bv 64 idx -> getr R 16%bv = w4 ->
    0 <= idx < bc -> bc <> 0 ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) -> (b <> 0 -> b mod 8 = 0) ->
    exists R', kept3 R R' /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B3_PC) (st R' NTF_MISS))
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B3_PC) (st R' LM3_PC)
          /\ getr R' 15%bv = Z_to_bv 64 q0 /\ getr R' 10%bv = Z_to_bv 64 bc /\ getr R' 12%bv = Z_to_bv 64 tid
          /\ getr R' 14%bv = Z_to_bv 64 idx)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B3_PC) (st R' LP3_PC)
          /\ getr R' 15%bv = Z_to_bv 64 q0 /\ getr R' 10%bv = Z_to_bv 64 (bc - 1) /\ getr R' 12%bv = Z_to_bv 64 tid
          /\ getr R' 14%bv = Z_to_bv 64 idx) ).
  Proof using fx AC L MI rom A M this bl bc tid ents U Hthis0 Hthis1.
    intros R idx b q0 w4 H10 H8 H12 H13 H15 H16 Hidx Hbc Hb Hb0 Hb1 Hq0 Hbal.
    pose proof (u_hdr U) as HD. destruct HD as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef]. unfold cell8 in Hbl.
    pose proof bc_rng3 as Hbcr. pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1. pose proof (u_bl_al U) as Hblal.
    pose proof (proj1 Hb) as Hbr.
    pose (E := Eseed R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 0; Z_to_bv 64 idx; w4; Z_to_bv 64 0;
                        Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 34); (12%bv, EVar 35); (14%bv, EVar 37); (16%bv, EVar 38)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.

    assert (Hrd_b : forall e, edenot E e = Z_to_bv 64 b ->
      sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) 0) 8 false e)).
    { intros e He. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      evs. rewrite w_mul, w_add, v_addi_Z by lia. f_equal. lia. }
    assert (Hfl_b : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) 0) (ELit 8))).
    { eapply (sc_flat _ _ _ _ (bl + 8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }

    assert (UB1 : sc_denot SEGS M E (SCBr false BC_LTU (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) (EVar 40))).
    { eapply (sc_trap_wrap _ _ _ _ _ bl (8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | evs; reflexivity | lia | lia | lia]. }
    assert (UB2 : sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) (EVar 40))
                     (EAlu ALU_SLTU (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) (ELit 1))) (ELit 0))).
    { eapply (sc_trap_nullxor _ _ _ _ _ bl (8 * idx)); [evs; reflexivity | evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | lia | lia]. }
    assert (UB3 : sc_denot SEGS M E (SCBr false BC_EQ (EVar 40) (ELit 0))).
    { eapply (sc_trap_null _ _ _ _ bl); [evs; reflexivity | lia]. }
    assert (UB4 : sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 37)) (EVar 40)) (ELit 7)) (ELit 0))).
    { eapply (sc_trap_align _ _ _ _ (8 * idx + bl)); [evs; rewrite w_mul, w_add by lia; reflexivity | lia | apply align8_add; apply align16_8; exact Hblal]. }
    assert (UB5 : b <> 0 -> sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND (EVar 41) (ELit 7)) (ELit 0))).
    { intros Hbnz. eapply (sc_trap_align _ _ _ _ b); [evs; reflexivity | lia | exact (Hbal Hbnz)]. }
    Ltac scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b :=
      split_scs; try sc_auto1; first [exact UB1 | exact UB2 | exact UB3 | exact UB4 | apply UB5; assumption | exact Hfl_b | apply Hrd_b; evs; reflexivity
                                      | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia ].
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    - xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b|].
      exists R'. split; [kept3_of HR' H10 H8|]. left. split; [left; exact Hbz | exact Hms].
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b|].
        exists R'. split; [kept3_of HR' H10 H8|]. left. split; [right; exact Hqz | exact Hms].
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        * xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b|].
          exists R'. split; [kept3_of HR' H10 H8|]. right; left.
          rreg HR' 15%bv G14. rreg HR' 10%bv G12. rreg HR' 12%bv G13. rreg HR' 14%bv G15.
          repeat split; assumption.
        * xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false; false; false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N; [scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b|].
          exists R'. split; [kept3_of HR' H10 H8|]. right; right.
          rreg HR' 15%bv G14. rreg HR' 10%bv G12. rreg HR' 12%bv G13. rreg HR' 14%bv G15.
          repeat split; try assumption. rewrite G12. apply w_addm; lia.
  Qed.

  Definition walk3 (R : bvmap 5 word) (pc0 : Z) (R' : bvmap 5 word) : Prop :=
    kept3 R R' /\
    ( (exists p v, In (p, (tid, v)) ents /\ msteps SEGS (st R pc0) (st R' NTF_HIT) /\ getr R' 15%bv = Z_to_bv 64 p)
      \/ msteps SEGS (st R pc0) (st R' NTF_MISS) ).

  Ltac seed3 R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(13%bv, EVar 32); (8%bv, EVar 33); (10%bv, EVar 34); (12%bv, EVar 35); (15%bv, EVar 36); (14%bv, EVar 37)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_hit HR' Hms p v He H10 H8 :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [kept3_of HR' H10 H8|];
      left; exists p, v; split; [rewrite He; apply in_app_iff; right; left; reflexivity|];
      split; [exact Hms | let G := fresh in rreg HR' 15%bv G; exact G]
    end.
  Ltac fin_miss HR' Hms H10 H8 :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1; split; [kept3_of HR' H10 H8|]; right; exact Hms
    end.

  Lemma loopM3 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 13%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 15%bv = Z_to_bv 64 p -> getr R 10%bv = Z_to_bv 64 bc -> getr R 12%bv = Z_to_bv 64 tid ->
    getr R 14%bv = Z_to_bv 64 (tid mod bc) -> bc <> 0 ->
    exists R', walk3 R LM3_PC R'.
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H10 H8 H14 H12 H13 H15 Hbc;
      pose proof bc_rng3 as Hbcr;
      destruct (node_facts3 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (node_al3 l1 p k v _ He) as Hpal;
      pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk3.
    - destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; false; true; true; true] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal])|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal])|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts3 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM3_PC) (st R1 LM3_PC) /\ kept3 R R1
                    /\ getr R1 15%bv = Z_to_bv 64 p' /\ getr R1 10%bv = Z_to_bv 64 bc /\ getr R1 12%bv = Z_to_bv 64 tid
                    /\ getr R1 14%bv = Z_to_bv 64 (tid mod bc) /\ getr R1 13%bv = Z_to_bv 64 this /\ getr R1 8%bv = sxw tid).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS3 (SCR [false; false; true; true; false] [EVar 40; EVar 41] []) 50%N; [split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal])|].
               exists R'. split; [exact Hms|]. split; [kept3_of HR' H10 H8|].
               rreg HR' 15%bv G14. rreg HR' 10%bv G12. rreg HR' 12%bv G13. rreg HR' 14%bv G15. rreg HR' 13%bv G10. rreg HR' 8%bv G8.
               repeat split; assumption.
            -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [kept3_of HR' H10 H8|].
               rreg HR' 15%bv G14. rreg HR' 10%bv G12. rreg HR' 12%bv G13. rreg HR' 14%bv G15. rreg HR' 13%bv G10. rreg HR' 8%bv G8.
               repeat split; assumption. }
          destruct STEP as (R1 & Hms1 & Hk1 & G14 & G12 & G13 & G15 & G10 & G8).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G10 G8 G14 G12 G13 G15 Hbc) as (R' & Hk2 & Hw).
          exists R'. split; [eapply kept3_trans; eassumption|].
          destruct Hw as [(q & vq & Hin & Hms2 & F14) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2] | exact F14].
          -- right. eapply msteps_trans; [exact Hms1 | exact Hms2].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 bc; Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS3 (SCR [false; false; true; false] [EVar 40] []) 50%N; [split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal])|].
             fin_miss HR' Hms H10 H8.
          -- xrun HR HK 100%nat STOPS3 (SCR [false; false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_miss HR' Hms H10 H8.
  Qed.

  Lemma loopP3 : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 13%bv = Z_to_bv 64 this -> getr R 8%bv = sxw tid ->
    getr R 15%bv = Z_to_bv 64 p -> getr R 10%bv = Z_to_bv 64 (bc - 1) -> getr R 12%bv = Z_to_bv 64 tid ->
    getr R 14%bv = Z_to_bv 64 (tid mod bc) ->
    exists R', walk3 R LP3_PC R'.
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H8 H14 H12 H13 H15;
      destruct (node_facts3 l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (node_al3 l1 p k v _ He) as Hpal;
      pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound tid 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1 k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk; unfold walk3.
    - destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS3 (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS3 (SCR [false; false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts3 _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k tid) as [->|Hne].
      + seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 tid; sxw tid].
        xrun HR HK 100%nat STOPS3 (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_hit HR' Hms p v He H10 H8.
      + destruct (Z.eq_dec (k mod bc) (tid mod bc)) as [Hc|Hc].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS3 (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 15%bv G14. rreg HR' 10%bv G12. rreg HR' 12%bv G13. rreg HR' 14%bv G15. rreg HR' 13%bv G10. rreg HR' 8%bv G8.
          assert (Hk1 : kept3 R R') by (kept3_of HR' H10 H8).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G10 G8 G14 G12 G13 G15) as (R'' & Hk2 & Hw).
          exists R''. split; [eapply kept3_trans; eassumption|].
          destruct Hw as [(q & vq & Hin & Hms2 & F14) | Hms2].
          -- left. exists q, vq. split; [exact Hin|]. split; [eapply msteps_trans; [exact Hms | exact Hms2] | exact F14].
          -- right. eapply msteps_trans; [exact Hms | exact Hms2].
        * seed3 R [Z_to_bv 64 this; sxw tid; Z_to_bv 64 (bc - 1); Z_to_bv 64 tid; Z_to_bv 64 p; Z_to_bv 64 (tid mod bc); Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS3 (SCR [false; false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_miss HR' Hms H10 H8.
  Qed.

  Theorem ntfind_correct : forall R,
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = Z_to_bv 64 (HStmts.sx32 tid) ->
    exists R' (pc' : Z),
      msteps SEGS (st R NTF_ENTRY) (st R' pc')
      /\ (forall r, ~ In r [5; 6; 10; 12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r) /\ getr R' 13%bv = Z_to_bv 64 this
      /\ ( pc' = NTF_MISS \/ (pc' = NTF_HIT /\ exists p v, In (p, (tid, v)) ents /\ getr R' 15%bv = Z_to_bv 64 p)).
  Proof using fx AC L MI rom A M this bl bc tid ents U Htid Hthis0 Hthis1.
    intros R H10 H8. rewrite sx32_sxw in H8 by exact Htid.
    pose proof bc_rng3 as Hbcr.
    destruct (blkA3 R H10 H8) as (R1 & K1 & [[Hbc0 Hms1] | (Hbc & Hms1 & G12 & G13 & G15 & G16)]).
    { exists R1, NTF_MISS. split; [exact Hms1|]. split; [exact (kept3_all _ _ K1) |]. split; [exact (proj1 (proj2 K1)) | left; reflexivity]. }
    pose proof (Z.mod_pos_bound tid bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod tid bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).
    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l) /\ (b <> 0 -> b mod 8 = 0)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; [|split]; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents _ b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts3 l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        split; [| intros _; apply align16_8; exact (node_al3 l1 b k v l2 He)].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. pose proof (u_obj_hi U). split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. split; [intros _; split; reflexivity|].
        intros _. pose proof (u_obj_al U) as Hoal. replace (this + 136 + 16) with (8 * 19 + this) by lia. apply align8_add.
        replace this with (this + 136 - 8 * 17) by lia. rewrite <- Z.add_opp_r. replace (- (8 * 17)) with (8 * (-17)) by lia. rewrite Z.add_comm. apply align8_add. exact Hoal. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql & Hbal).
    assert (K110 : getr R1 13%bv = Z_to_bv 64 this) by (exact (proj1 (proj2 K1))).
    assert (K18 : getr R1 8%bv = sxw tid) by (rewrite (proj2 (proj2 K1)); exact H8).
    destruct (blkB3 R1 (hmod tid bc) b q0 (popcw3 (Z_to_bv 64 bc)) K110 K18 G12 G13 G15 G16 ltac:(unfold hmod; lia) Hbc Hb Hb0 Hb1 Hbq Hbal)
      as (R2 & K2 & [ (Hz & Hms2) | [ (Hbn & Hqn & Hw & Hms2 & F14 & F12 & F13 & F15)
                                      | (Hbn & Hqn & Hw & Hms2 & F14 & F12 & F13 & F15) ] ]).
    - exists R2, NTF_MISS. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [apply kept3_all; eapply kept3_trans; [exact K1 | exact K2] |]. split; [exact (proj1 (proj2 K2)) | left; reflexivity].
    - destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases3 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      assert (K210 : getr R2 13%bv = Z_to_bv 64 this) by (exact (proj1 (proj2 K2))).
      assert (K28 : getr R2 8%bv = sxw tid) by (rewrite (proj2 (proj2 K2)); exact K18).
      destruct (loopM3 l2 pre p k v R2 He K210 K28 F14 F12 F13 ltac:(exact F15) Hbc) as (R3 & K3 & Hw3).
      assert (KK : kept3 R R3) by (eapply kept3_trans; [eapply kept3_trans; [exact K1 | exact K2] | exact K3]).
      destruct Hw3 as [(q & vq & Hin & Hms3 & T14) | Hms3].
      + exists R3, NTF_HIT. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK)|]. split; [exact (proj1 (proj2 KK))|]. right. split; [reflexivity|]. exists q, vq. split; assumption.
      + exists R3, NTF_MISS. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK) |]. split; [exact (proj1 (proj2 KK)) | left; reflexivity].
    - assert (Hbc2 : bc = 2).
      { destruct (popcw3_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases3 l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      assert (K210 : getr R2 13%bv = Z_to_bv 64 this) by (exact (proj1 (proj2 K2))).
      assert (K28 : getr R2 8%bv = sxw tid) by (rewrite (proj2 (proj2 K2)); exact K18).
      destruct (loopP3 l2 pre p k v R2 He Hbc2 K210 K28 F14 F12 F13 ltac:(exact F15)) as (R3 & K3 & Hw3).
      assert (KK : kept3 R R3) by (eapply kept3_trans; [eapply kept3_trans; [exact K1 | exact K2] | exact K3]).
      destruct Hw3 as [(q & vq & Hin & Hms3 & T14) | Hms3].
      + exists R3, NTF_HIT. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK)|]. split; [exact (proj1 (proj2 KK))|]. right. split; [reflexivity|]. exists q, vq. split; assumption.
      + exists R3, NTF_MISS. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        split; [exact (kept3_all _ _ KK) |]. split; [exact (proj1 (proj2 KK)) | left; reflexivity].
  Qed.
End NTFind.

Theorem nt_find_block_u1_spec {AC : AllocCeiling} : forall (L : Layout) (MI : MallocIface SEGS L),
  nt_find_block_u1_stmt SEGS L MI NTF_ENTRY NTF_MISS NTF_HIT.
Proof.
  intros L MI fx A R M this bl bc tid ents U H10 H8 Htid Hthis0 Hthis1.
  exact (ntfind_correct L MI (seg_rom SEGS) A M this bl bc tid ents U Htid Hthis0 Hthis1 R H10 H8).
Qed.
End HFindNTU1.
From Stdlib Require Permutation.
From LinuxProcessSemantics.Riscv Require Fpu.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6a4fc_6a53c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6a534 : bv 32 := 0x00008067.
Lemma F_6a534 : fetch_word Ubsan.M.loaded_segments (0x6a574 : word) = Some W_6a534.
Proof. vm_refl. Qed.
Lemma D_6a534 : decode_any W_6a534 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6a4fc_6a53c.

Module HIndexU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.U1_code_6a4fc_6a53c.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition IDX      : Z := 0x6a53c.
Definition EMPF     : Z := 0x6aa04.
Definition EMPR     : Z := 0x6a55c.
Definition RET_PC   : Z := 0x6a574.
Definition TRAP_PC  : Z := 0x6a578.
Definition GOT_PC   : Z := 0xeec78.

Definition STOPS : list Z := [EMPF; EMPR; RET_PC; TRAP_PC].

Section IX.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis EMPL : emplace24u_stmt SEGS L MI ST NEW_STACK DEL_STACK EMPF.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation live_facts' := (live_facts L MI).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC L MI.
    intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
  Qed.

  Lemma sc_disjZ : forall M E (sa1 sa2 : saddr) (b1 b2 n1 n2 : Z),
    edenot E (a_base sa1) = Z_to_bv 64 b1 -> edenot E (a_base sa2) = Z_to_bv 64 b2 ->
    0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 -> 0 < n1 < 2 ^ 64 -> 0 < n2 < 2 ^ 64 ->
    0 <= b1 + a_off sa1 -> b1 + a_off sa1 + n1 <= 2 ^ 64 -> 0 <= b2 + a_off sa2 -> b2 + a_off sa2 + n2 <= 2 ^ 64 ->
    (b1 + a_off sa1 + n1 <= b2 + a_off sa2 \/ b2 + a_off sa2 + n2 <= b1 + a_off sa1) ->
    sc_denot SEGS M E (SCDisj sa1 (ELit n1) sa2 (ELit n2)).
  Proof using.
    intros M E sa1 sa2 b1 b2 n1 n2 H1 H2 Hb1 Hb2 Hn1 Hn2 Ho1 Ho1' Ho2 Ho2' Hd.
    cbn [sc_denot]. unfold flat, estart, elenZ. cbn [edenot]. rewrite H1, H2, !u64_of_Z by lia. lia.
  Qed.

  Lemma rdn_some_rom : forall M n (a : Z), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall j, 0 <= j < Z.of_nat n -> seg_rom SEGS (Z_to_bv 64 (a + j)) <> None) ->
    exists bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
  Proof using.
    intros M n. induction n as [|n IH]; intros a Ha Han Hrom.
    - exists []. split; reflexivity.
    - cbn [rdn].
      assert (Hb : exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom SEGS (Z_to_bv 64 a) end = Some b).
      { destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
        pose proof (Hrom 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; exact (H0 eq_refl)]. }
      destruct Hb as [b ->].
      destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr & Hl).
      { intros j Hj. replace (a + 1 + j) with (a + (1 + j)) by lia. apply Hrom. lia. }
      rewrite SymExec3Sound.SX2S.w_add_1, u64_of_Z by lia. rewrite Hr. exists (b :: bs). split; [reflexivity | cbn; lia].
  Qed.

  Lemma got_readable : forall M, exists bs, rdn SEGS M (Z_to_bv 64 GOT_PC) 8 = Some bs /\ length bs = 8%nat.
  Proof using.
    intros M. apply (rdn_some_rom M 8 GOT_PC); [unfold GOT_PC; lia | unfold GOT_PC; cbn; lia |].
    intros j Hj.
    assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
  Qed.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (INDEX_STACK NEW_STACK DEL_STACK).
    Hypothesis FRM : frm_zero (@fp_csr fx).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 keyp.
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
    Hypothesis ASK : above_sp MI A0 sp keyp 4.
    Hypothesis CK : cell4 SEGS M0 keyp key.
    Hypothesis KAL : keyp mod 4 = 0.
    Hypothesis ROC : ro_clear L M0.
    Hypothesis HSZ : Zlength ents + 1 < 2 ^ 24.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis ROOM1 : roomL MI A0 (live MI A0) 24.
    Hypothesis ROOM2 : (bc = 0 \/ Zlength ents = bc) -> roomL MI A0 ((0, 24) :: live MI A0) (8 * bseq_next bc).
    Hypothesis CONT : forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
            (inserted rehashed : bool),
        retB MI ST A' s R0 R' M' model0 model' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
        getr R' 10%bv = Z_to_bv 64 (p + 20) ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' bc' ents' ->
        In (p, (key, v)) ents' ->
        (inserted = false -> ents' = ents /\ rehashed = false) ->
        (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A0)
               ((if inserted then [LAdd p 24] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A0 A' M0 M' (sp - INDEX_STACK NEW_STACK DEL_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K.

    Definition SS : Z := 32 + (96 + Z.max NEW_STACK DEL_STACK).
    Definition W : Z * Z := (sp - SS, sp).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 128 <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret keyp CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold INDEX_STACK, EMPLACE_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Theorem index_correct : srealizes SEGS (cfg fx R0 IDX M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn EMPL HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc keyp key ents K CB FRM H10 H11 U0 ASP ASK CK KAL ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1). destruct ASK as (Ks1 & Kh1 & Ko1).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold INDEX_STACK, EMPLACE_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold INDEX_STACK, EMPLACE_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      destruct (got_readable M0) as (gbs & Hgot & Hglen).
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 sp; getr R0 1%bv; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                           Z_to_bv 64 (bytes_le_to_Z gbs)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34); (1%bv, EVar 35)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-32)) (ELit 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom]. }
      xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1;
        first [ eapply (sc_disjZ _ _ _ _ 0 sp); [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | cbn [a_off]; unfold SS in Hsplo; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia
                                             | cbn [a_off]; unfold SS in Hsplo; lia ]
              | cbn [sc_denot]; exists gbs; split; [evs; exact Hgot | evs; rewrite extz_false; reflexivity] ]. }
      postrun. rewrite Hra.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
      rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 10%bv G10. rreg HRc 11%bv G11. rreg HRc 13%bv G13.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
      assert (HMcw : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> Mc x = M0 x).
      { intros x Hx. pose proof (u64_range x). unfold Mc.
        rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
      assert (AIc : ainv MI A0 Mc model0).
      { eapply (ai_frame MI); [exact AI0 | | exact HMcg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMcw; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(unfold SS in Hsplo; lia) Ho). }
      assert (EFc : eff MI A0 A0 M0 Mc W (fun _ => False)).
      { apply eff_store; [|exact HMcg]. intros x HF HW. pose proof (u64_range x). apply HMcw; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROCc : img_ro_clear L Mc).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 Mc model0 W _ ROC0 AI0 EFc); [intros a [] | unfold W; cbn; lia]. }
      assert (SXc : sx_inv ST s Mc).
      { eapply (sx_inv_via_eff' s A0 A0 M0 Mc model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EFc
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      assert (RCc : ro_clear L Mc).
      { intros w Hw. pose proof (u64_range w). rewrite HMcw; [exact (ROC w Hw)|]. intros Hx. destruct Hw as (Himg & _). pose proof (HLimg_lo _ Himg). unfold SS in Hsplo. lia. }
      assert (F1 : cell8 SEGS Mc (sp - 8) ret) by (unfold Mc, cell8; cellpeel).
      assert (F2 : cell8 SEGS Mc (sp - 16) keyp) by (unfold Mc, cell8; cellpeel).
      assert (CKc : cell4 SEGS Mc keyp key).
      { eapply cellw_agree; [exact CK | | lia | cbn; lia]. intros i Hi. first [apply HMcw | symmetry; apply HMcw]. rewrite u64_of_Z by lia. lia. }
      eapply (EMPL fx A0 s Rc Mc model0 (sp - 32) EMPR obj bl bc keyp (sp - 16) keyp key ents K).
      -   constructor.
        + exact AIc. + exact MS0. + exact ROCc. + exact SXc. + exact (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB).
        + constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold EMPR; lia | rewrite G2; rewrite ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
                       | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia | rewrite Gs by inl; exact Hgp | rewrite Gs by inl; exact Htp].
        + unfold EMPLACE_STACK. unfold SS in Hsplo. lia.
        + unfold EMPLACE_STACK. apply stack_room_of_defined; [unfold SS in Hsplo; lia | lia | lia |]. unfold Mc. repeat apply defined_wbytes.
          eapply defined_sub; [exact Hdef0 | unfold SS; lia | unfold SS; lia].
        + unfold EMPLACE_STACK. intros a Ha. split; [eapply hi_unowned; [exact AI0 | unfold zwin, SS in *; lia]|].
          apply (proj2 (Hwin0 a ltac:(unfold zwin, SS in *; lia))).
        + exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
        + exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - exact FRM.
      - exact G10. - exact G11.
      - rewrite G13. rewrite ?w_addm, ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
      - eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 _ (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A0 M0 Mc model0 obj bl bc ents W _ sp U0 AI0 EFc);
          [exact Hs1 | unfold W; cbn; lia | lia | intros i Hi; eapply hi_unowned; [exact AI0 | lia] | intros a _ [] | unfold W, SS in *; cbn; lia | intros q m Hb Hl; exact Hl].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | unfold SS in Hsplo; lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - exact CKc. - exact F2. - exact CKc. - exact KAL. - exact RCc. - exact HSZ. - exact HNMAX. - exact Hlast.
      - exact ROOM1. - exact ROOM2.
      -
        intros fx' A' R' M' model' p v bl' bc' ents' inserted rehashed RB FZ' FK' Q10 Q11 U' Hin Hf Ht Hrf Hrt LAP EFF.
        destruct RB as [AI' MS' Hfs Hfds SX' KEPT]. unfold EMPLACE_STACK in EFF.
        destruct (u_node U' p key v Hin) as (Hplv & Hp0 & Hp1 & Hpal & _).

        assert (Hfr_own : forall i, 0 <= i < 32 -> ~ owned MI A0 (sp - 32 + i)) by (intros i Hi; eapply hi_unowned; [exact AI0 | unfold SS in Hsplo; lia]).
        assert (AGf : agree_on Mc M' (sp - 32) 32).
        { eapply (agree_above_via_eff' A0 A' Mc M' _ _ (sp - 32) 32 (sp - 32) EFF); [lia | cbn; lia | unfold SS in Hsplo; lia | lia | lia | exact Hfr_own | |].
          - intros i Hi. unfold Mc. repeat apply wbytes_grows. eapply (defined_pt _ _ _ _ Hdef0). unfold SS. lia.
          - intros i Hi [Hfo|Hfo].
            + destruct Hfo as [Hh|[[_ Hb]|(q & Hq & Hqa)]]; [lia | | ].
              * destruct (u_blive U0) as [[? ?]|[_ Hbin]]; [lia|]. destruct (live_facts' A0 M0 model0 bl (8 * bc) AI0 Hbin) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
              * apply in_map_iff in Hq. destruct Hq as ([q' [k' v']] & Hq' & Hqin). cbn in Hq'. subst q'.
                destruct (live_facts' A0 M0 model0 q 24 AI0 (proj1 (u_node U0 q k' v' Hqin))) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
            + destruct Hfo as [Hh|[[_ Hb]|(q & Hq & Hqa)]]; [lia | | ].
              * destruct (u_blive U') as [[? ?]|[_ Hbin]]; [lia|]. destruct (live_facts' A' M' model' bl' (8 * bc') AI' Hbin) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
              * apply in_map_iff in Hq. destruct Hq as ([q' [k' v']] & Hq' & Hqin). cbn in Hq'. subst q'.
                destruct (live_facts' A' M' model' q 24 AI' (proj1 (u_node U' q k' v' Hqin))) as (_ & _ & Hc & _). unfold SS in Hsplo. lia. }
        assert (F1' : cell8 SEGS M' (sp - 8) ret) by (eapply cellw_agree; [exact F1 | eapply agree_on_sub; [exact AGf | lia | cbn; lia] | lia | cbn; lia]).
        unfold cell8 in F1'. unfold ret_ok in Hret.
        pose proof (KEPT 2%bv ltac:(unfold callee_saved; inl)) as K2. rewrite G2 in K2. rewrite ?w_addm, ?v_addi_Z in K2 by lia.
        pose (E2 := Eseed R' [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 (sp - 32); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 ret]).
        assert (HR2 : regs_ok E2 (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 34)]) R').
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | rewrite K2; first [reflexivity | f_equal; lia]]. }
        assert (HK2 : know_ok SEGS E2 M' []) by constructor.
        xruns HR2 HK2 100%nat STOPS (SCR [false; false] [EVar 40] []) 50%N.
        { split_scs;
          first [ eapply (sc_trap_null _ _ _ _ p); [evs; reflexivity | lia]
                | eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F1'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | eapply sc_flat; [evs; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
        rreg HRr 1%bv T1. rreg HRr 2%bv T2. rreg HRr 10%bv T10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Ts.

        eapply srz_msteps; [eapply ms_halt; exact MS' | eapply ms_lazy; exact MS' | | ].
        { unfold RET_PC. norm_pc. stepjr F_6a534 D_6a534 (Z_to_bv 64 ret) ltac:(exact T1).
          change (bv_signed (0%bv : bv 12)) with 0%Z. rewrite Hret. apply mst_refl. }
        apply (CONT fx' A' Rr M' model' p v bl' bc' ents' inserted rehashed).
        + constructor; [exact AI' | exact MS' | exact Hfs | exact Hfds | exact SX' |].
          intros r Hr. unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite T1; symmetry; exact Hra
                  | rewrite T2; rewrite ?w_add, ?v_addi_Z by lia; replace (sp - 32 + 32) with sp by lia; symmetry; exact Hsp2
                  | rewrite Ts by inl; rewrite KEPT by (unfold callee_saved; inl); first [rewrite Gs by inl; reflexivity | apply Gs; inl] ].
        + exact FZ'.
        + exact FK'.
        + rewrite T10. rewrite ?w_add, ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + exact U'. + exact Hin. + exact Hf. + exact Ht. + exact Hrf. + exact Hrt. + exact LAP.
        + unfold INDEX_STACK, EMPLACE_STACK. fold SS. change (sp - SS, sp) with W.
          eapply eff_weaken; [eapply eff_trans; [exact EFc | eapply eff_widen; [exact EFF|] |]|].
          * intros a Ha. unfold W, W_of, SS in *. cbn in *. lia.
          * intros a Ha. eapply hi_unowned; [exact AI' | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha.
    Qed.
  End Main.

  Theorem index24_u1_spec : index24_u1_stmt SEGS L MI ST NEW_STACK DEL_STACK IDX.
  Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn EMPL HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros fx A s R M model sp ret obj bl bc keyp key ents K CB FRM H10 H11 U0 ASP ASK CK KAL ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
    eapply index_correct; eassumption.
  Qed.
End IX.
End HIndexU1.

Module U1_code_6a81c_6a85c.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6a838 : bv 32 := 0x4b1000ef.

Definition W_6a854 : bv 32 := 0x00008067.
Lemma F_6a854 : fetch_word Ubsan.M.loaded_segments (0x6a894 : word) = Some W_6a854.
Proof. vm_refl. Qed.
Lemma D_6a854 : decode_any W_6a854 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6a81c_6a85c.

Module HIndex2U1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.U1_code_6a81c_6a85c.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition IDX      : Z := 0x6a85c.
Definition EMPF     : Z := 0x6b528.
Definition EMPR     : Z := 0x6a87c.
Definition RET_PC   : Z := 0x6a894.
Definition TRAP_PC  : Z := 0x6a898.
Definition GOT_PC   : Z := 0xeec78.

Definition STOPS : list Z := [EMPF; EMPR; RET_PC; TRAP_PC].

Section IX.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis EMPL : emplace24u_stmt SEGS L MI ST NEW_STACK DEL_STACK EMPF.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).
  #[local] Abbreviation agree_above_via_eff' := (agree_above_via_eff L MI HLimg_lo HLrw_img HLerr_rw).
  #[local] Abbreviation live_facts' := (live_facts L MI).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Lemma eff_widen : forall (A A' : AS MI) M M' (W W' : Z * Z) F,
    eff MI A A' M M' W F -> (forall a, W_of W a -> W_of W' a) -> eff MI A A' M M' W' F.
  Proof using AC L MI.
    intros A A' M M' W0 W' F E HW. destruct E as [C B O FR D OI]. constructor; try assumption.
    intros a Hn. apply FR. intros [H|[H|[H|[H|[H|H]]]]]; apply Hn; try tauto. right; right; right; right; left. apply HW, H.
  Qed.

  Lemma sc_disjZ : forall M E (sa1 sa2 : saddr) (b1 b2 n1 n2 : Z),
    edenot E (a_base sa1) = Z_to_bv 64 b1 -> edenot E (a_base sa2) = Z_to_bv 64 b2 ->
    0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 -> 0 < n1 < 2 ^ 64 -> 0 < n2 < 2 ^ 64 ->
    0 <= b1 + a_off sa1 -> b1 + a_off sa1 + n1 <= 2 ^ 64 -> 0 <= b2 + a_off sa2 -> b2 + a_off sa2 + n2 <= 2 ^ 64 ->
    (b1 + a_off sa1 + n1 <= b2 + a_off sa2 \/ b2 + a_off sa2 + n2 <= b1 + a_off sa1) ->
    sc_denot SEGS M E (SCDisj sa1 (ELit n1) sa2 (ELit n2)).
  Proof using.
    intros M E sa1 sa2 b1 b2 n1 n2 H1 H2 Hb1 Hb2 Hn1 Hn2 Ho1 Ho1' Ho2 Ho2' Hd.
    cbn [sc_denot]. unfold flat, estart, elenZ. cbn [edenot]. rewrite H1, H2, !u64_of_Z by lia. lia.
  Qed.

  Lemma rdn_some_rom : forall M n (a : Z), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall j, 0 <= j < Z.of_nat n -> seg_rom SEGS (Z_to_bv 64 (a + j)) <> None) ->
    exists bs, rdn SEGS M (Z_to_bv 64 a) n = Some bs /\ length bs = n.
  Proof using.
    intros M n. induction n as [|n IH]; intros a Ha Han Hrom.
    - exists []. split; reflexivity.
    - cbn [rdn].
      assert (Hb : exists b, match M (Z_to_bv 64 a) with Some b => Some b | None => seg_rom SEGS (Z_to_bv 64 a) end = Some b).
      { destruct (M (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
        pose proof (Hrom 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. destruct (seg_rom SEGS (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; exact (H0 eq_refl)]. }
      destruct Hb as [b ->].
      destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hr & Hl).
      { intros j Hj. replace (a + 1 + j) with (a + (1 + j)) by lia. apply Hrom. lia. }
      rewrite SymExec3Sound.SX2S.w_add_1, u64_of_Z by lia. rewrite Hr. exists (b :: bs). split; [reflexivity | cbn; lia].
  Qed.

  Lemma got_readable : forall M, exists bs, rdn SEGS M (Z_to_bv 64 GOT_PC) 8 = Some bs /\ length bs = 8%nat.
  Proof using.
    intros M. apply (rdn_some_rom M 8 GOT_PC); [unfold GOT_PC; lia | unfold GOT_PC; cbn; lia |].
    intros j Hj.
    assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
    destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; discriminate.
  Qed.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (INDEX_STACK NEW_STACK DEL_STACK).
    Hypothesis FRM : frm_zero (@fp_csr fx).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 keyp.
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
    Hypothesis ASK : above_sp MI A0 sp keyp 4.
    Hypothesis CK : cell4 SEGS M0 keyp key.
    Hypothesis KAL : keyp mod 4 = 0.
    Hypothesis ROC : ro_clear L M0.
    Hypothesis HSZ : Zlength ents + 1 < 2 ^ 24.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis ROOM1 : roomL MI A0 (live MI A0) 24.
    Hypothesis ROOM2 : (bc = 0 \/ Zlength ents = bc) -> roomL MI A0 ((0, 24) :: live MI A0) (8 * bseq_next bc).
    Hypothesis CONT : forall (fx' : FPState) A' R' M' model' (p v bl' bc' : Z) (ents' : list (Z * (Z * Z)))
            (inserted rehashed : bool),
        retB MI ST A' s R0 R' M' model0 model' -> frm_zero (@fp_csr fx') -> fkept_u1 fx fx' ->
        getr R' 10%bv = Z_to_bv 64 (p + 20) ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' bc' ents' ->
        In (p, (key, v)) ents' ->
        (inserted = false -> ents' = ents /\ rehashed = false) ->
        (inserted = true -> v = 0 /\ Permutation ents' ((p, (key, 0)) :: ents)) ->
        (rehashed = false -> bl' = bl /\ bc' = bc) ->
        (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc) ->
        lapply (live MI A0)
               ((if inserted then [LAdd p 24] else [])
                ++ (if rehashed then LAdd bl' (8 * bc') :: (if bc =? 0 then [] else [LDel bl]) else []))
               (live MI A') ->
        eff MI A0 A' M0 M' (sp - INDEX_STACK NEW_STACK DEL_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' bc' ents' a) ->
        srealizes SEGS (cfg fx' R' ret M' model') K.

    Definition SS : Z := 32 + (96 + Z.max NEW_STACK DEL_STACK).
    Definition W : Z * Z := (sp - SS, sp).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 128 <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret keyp CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold INDEX_STACK, EMPLACE_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Theorem index_correct : srealizes SEGS (cfg fx R0 IDX M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn EMPL HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc keyp key ents K CB FRM H10 H11 U0 ASP ASK CK KAL ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1). destruct ASK as (Ks1 & Kh1 & Ko1).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold INDEX_STACK, EMPLACE_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold INDEX_STACK, EMPLACE_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      destruct (got_readable M0) as (gbs & Hgot & Hglen).
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 sp; getr R0 1%bv; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                           Z_to_bv 64 (bytes_le_to_Z gbs)]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34); (1%bv, EVar 35)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-32)) (ELit 32)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom]. }
      xruns HR HK 100%nat STOPS (SCR [] [EVar 40] []) 50%N.
      { split_scs; try sc_auto1;
        first [ eapply (sc_disjZ _ _ _ _ 0 sp); [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | cbn [a_off]; unfold SS in Hsplo; lia | cbn [a_off]; lia | cbn [a_off]; lia | cbn [a_off]; lia
                                             | cbn [a_off]; unfold SS in Hsplo; lia ]
              | cbn [sc_denot]; exists gbs; split; [evs; exact Hgot | evs; rewrite extz_false; reflexivity] ]. }
      postrun. rewrite Hra.
      lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
      rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 10%bv G10. rreg HRc 11%bv G11. rreg HRc 13%bv G13.
      pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
      assert (HMcw : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> Mc x = M0 x).
      { intros x Hx. pose proof (u64_range x). unfold Mc.
        rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
      assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
      assert (AIc : ainv MI A0 Mc model0).
      { eapply (ai_frame MI); [exact AI0 | | exact HMcg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMcw; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(unfold SS in Hsplo; lia) Ho). }
      assert (EFc : eff MI A0 A0 M0 Mc W (fun _ => False)).
      { apply eff_store; [|exact HMcg]. intros x HF HW. pose proof (u64_range x). apply HMcw; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROCc : img_ro_clear L Mc).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 Mc model0 W _ ROC0 AI0 EFc); [intros a [] | unfold W; cbn; lia]. }
      assert (SXc : sx_inv ST s Mc).
      { eapply (sx_inv_via_eff' s A0 A0 M0 Mc model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EFc
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      assert (RCc : ro_clear L Mc).
      { intros w Hw. pose proof (u64_range w). rewrite HMcw; [exact (ROC w Hw)|]. intros Hx. destruct Hw as (Himg & _). pose proof (HLimg_lo _ Himg). unfold SS in Hsplo. lia. }
      assert (F1 : cell8 SEGS Mc (sp - 8) ret) by (unfold Mc, cell8; cellpeel).
      assert (F2 : cell8 SEGS Mc (sp - 16) keyp) by (unfold Mc, cell8; cellpeel).
      assert (CKc : cell4 SEGS Mc keyp key).
      { eapply cellw_agree; [exact CK | | lia | cbn; lia]. intros i Hi. first [apply HMcw | symmetry; apply HMcw]. rewrite u64_of_Z by lia. lia. }
      eapply (EMPL fx A0 s Rc Mc model0 (sp - 32) EMPR obj bl bc keyp (sp - 16) keyp key ents K).
      -   constructor.
        + exact AIc. + exact MS0. + exact ROCc. + exact SXc. + exact (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB).
        + constructor; [exact G1 | apply bv_eq; vm_compute; reflexivity | unfold EMPR; lia | rewrite G2; rewrite ?w_addm, ?v_addi_Z by lia; first [reflexivity | f_equal; lia]
                       | replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16 | lia | rewrite Gs by inl; exact Hgp | rewrite Gs by inl; exact Htp].
        + unfold EMPLACE_STACK. unfold SS in Hsplo. lia.
        + unfold EMPLACE_STACK. apply stack_room_of_defined; [unfold SS in Hsplo; lia | lia | lia |]. unfold Mc. repeat apply defined_wbytes.
          eapply defined_sub; [exact Hdef0 | unfold SS; lia | unfold SS; lia].
        + unfold EMPLACE_STACK. intros a Ha. split; [eapply hi_unowned; [exact AI0 | unfold zwin, SS in *; lia]|].
          apply (proj2 (Hwin0 a ltac:(unfold zwin, SS in *; lia))).
        + exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
        + exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB).
      - exact FRM.
      - exact G10. - exact G11.
      - rewrite G13. rewrite ?w_addm, ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
      - eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 _ (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A0 M0 Mc model0 obj bl bc ents W _ sp U0 AI0 EFc);
          [exact Hs1 | unfold W; cbn; lia | lia | intros i Hi; eapply hi_unowned; [exact AI0 | lia] | intros a _ [] | unfold W, SS in *; cbn; lia | intros q m Hb Hl; exact Hl].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | unfold SS in Hsplo; lia].
      - split; [lia|]. split; [lia|]. intros i Hi. eapply hi_unowned; [exact AI0 | lia].
      - exact CKc. - exact F2. - exact CKc. - exact KAL. - exact RCc. - exact HSZ. - exact HNMAX. - exact Hlast.
      - exact ROOM1. - exact ROOM2.
      -
        intros fx' A' R' M' model' p v bl' bc' ents' inserted rehashed RB FZ' FK' Q10 Q11 U' Hin Hf Ht Hrf Hrt LAP EFF.
        destruct RB as [AI' MS' Hfs Hfds SX' KEPT]. unfold EMPLACE_STACK in EFF.
        destruct (u_node U' p key v Hin) as (Hplv & Hp0 & Hp1 & Hpal & _).

        assert (Hfr_own : forall i, 0 <= i < 32 -> ~ owned MI A0 (sp - 32 + i)) by (intros i Hi; eapply hi_unowned; [exact AI0 | unfold SS in Hsplo; lia]).
        assert (AGf : agree_on Mc M' (sp - 32) 32).
        { eapply (agree_above_via_eff' A0 A' Mc M' _ _ (sp - 32) 32 (sp - 32) EFF); [lia | cbn; lia | unfold SS in Hsplo; lia | lia | lia | exact Hfr_own | |].
          - intros i Hi. unfold Mc. repeat apply wbytes_grows. eapply (defined_pt _ _ _ _ Hdef0). unfold SS. lia.
          - intros i Hi [Hfo|Hfo].
            + destruct Hfo as [Hh|[[_ Hb]|(q & Hq & Hqa)]]; [lia | | ].
              * destruct (u_blive U0) as [[? ?]|[_ Hbin]]; [lia|]. destruct (live_facts' A0 M0 model0 bl (8 * bc) AI0 Hbin) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
              * apply in_map_iff in Hq. destruct Hq as ([q' [k' v']] & Hq' & Hqin). cbn in Hq'. subst q'.
                destruct (live_facts' A0 M0 model0 q 24 AI0 (proj1 (u_node U0 q k' v' Hqin))) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
            + destruct Hfo as [Hh|[[_ Hb]|(q & Hq & Hqa)]]; [lia | | ].
              * destruct (u_blive U') as [[? ?]|[_ Hbin]]; [lia|]. destruct (live_facts' A' M' model' bl' (8 * bc') AI' Hbin) as (_ & _ & Hc & _). unfold SS in Hsplo. lia.
              * apply in_map_iff in Hq. destruct Hq as ([q' [k' v']] & Hq' & Hqin). cbn in Hq'. subst q'.
                destruct (live_facts' A' M' model' q 24 AI' (proj1 (u_node U' q k' v' Hqin))) as (_ & _ & Hc & _). unfold SS in Hsplo. lia. }
        assert (F1' : cell8 SEGS M' (sp - 8) ret) by (eapply cellw_agree; [exact F1 | eapply agree_on_sub; [exact AGf | lia | cbn; lia] | lia | cbn; lia]).
        unfold cell8 in F1'. unfold ret_ok in Hret.
        pose proof (KEPT 2%bv ltac:(unfold callee_saved; inl)) as K2. rewrite G2 in K2. rewrite ?w_addm, ?v_addi_Z in K2 by lia.
        pose (E2 := Eseed R' [Z_to_bv 64 p; Z_to_bv 64 0; Z_to_bv 64 (sp - 32); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 ret]).
        assert (HR2 : regs_ok E2 (srs sr_id [(10%bv, EVar 32); (2%bv, EVar 34)]) R').
        { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | rewrite K2; first [reflexivity | f_equal; lia]]. }
        assert (HK2 : know_ok SEGS E2 M' []) by constructor.
        xruns HR2 HK2 100%nat STOPS (SCR [false; false] [EVar 40] []) 50%N.
        { split_scs;
          first [ eapply (sc_trap_null _ _ _ _ p); [evs; reflexivity | lia]
                | eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F1'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | eapply sc_flat; [evs; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
        rreg HRr 1%bv T1. rreg HRr 2%bv T2. rreg HRr 10%bv T10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Ts.

        eapply srz_msteps; [eapply ms_halt; exact MS' | eapply ms_lazy; exact MS' | | ].
        { unfold RET_PC. norm_pc. stepjr F_6a854 D_6a854 (Z_to_bv 64 ret) ltac:(exact T1).
          change (bv_signed (0%bv : bv 12)) with 0%Z. rewrite Hret. apply mst_refl. }
        apply (CONT fx' A' Rr M' model' p v bl' bc' ents' inserted rehashed).
        + constructor; [exact AI' | exact MS' | exact Hfs | exact Hfds | exact SX' |].
          intros r Hr. unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite T1; symmetry; exact Hra
                  | rewrite T2; rewrite ?w_add, ?v_addi_Z by lia; replace (sp - 32 + 32) with sp by lia; symmetry; exact Hsp2
                  | rewrite Ts by inl; rewrite KEPT by (unfold callee_saved; inl); first [rewrite Gs by inl; reflexivity | apply Gs; inl] ].
        + exact FZ'.
        + exact FK'.
        + rewrite T10. rewrite ?w_add, ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + exact U'. + exact Hin. + exact Hf. + exact Ht. + exact Hrf. + exact Hrt. + exact LAP.
        + unfold INDEX_STACK, EMPLACE_STACK. fold SS. change (sp - SS, sp) with W.
          eapply eff_weaken; [eapply eff_trans; [exact EFc | eapply eff_widen; [exact EFF|] |]|].
          * intros a Ha. unfold W, W_of, SS in *. cbn in *. lia.
          * intros a Ha. eapply hi_unowned; [exact AI' | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha.
    Qed.
  End Main.

  Theorem index24_u1_spec : index24_u1_stmt SEGS L MI ST NEW_STACK DEL_STACK IDX.
  Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn EMPL HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros fx A s R M model sp ret obj bl bc keyp key ents K CB FRM H10 H11 U0 ASP ASK CK KAL ROC HSZ HNMAX Hlast ROOM1 ROOM2 CONT.
    eapply index_correct; eassumption.
  Qed.
End IX.
End HIndex2U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplaceU1A OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplaceU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplace2U1A OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HEmplace2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehash2U1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6ad6c_6afb8.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.
End U1_code_6ad6c_6afb8.

Module HRehashWU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MemSplit OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibBudget OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.FPSteps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SumMemsetLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRepFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmtsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HCommonU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HBlkU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.U1_code_6ad6c_6afb8.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition RW       : Z := 0x6adac.
Definition NP_PC    : Z := 0x8c1fc.
Definition NPR      : Z := 0x6ade8.
Definition REH      : Z := 0x6aff8.
Definition SHRINK   : Z := 0x6ae10.

Definition STOPS : list Z := [NP_PC; NPR; REH; SHRINK].

Section RW.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variable ST : StaticsIface SEGS L.
  Variables NEW_STACK DEL_STACK : Z.
  Hypothesis NEW_STACK_nn : 0 <= NEW_STACK.
  Hypothesis DEL_STACK_nn : 0 <= DEL_STACK.
  Hypothesis NP : next_prime_stmt SEGS L hc.
  Hypothesis REHASH : rehash24_stmt SEGS L MI ST NEW_STACK DEL_STACK REH.

  Hypothesis HLimg_lo : forall a, in_ranges (ly_img L) a -> a < alloc_ceiling.
  Hypothesis HLrw_img : forall a, in_ranges (ly_rw L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrelro_img : forall a, in_ranges (ly_relro L) a -> in_ranges (ly_img L) a.
  Hypothesis HLrw_relro : forall a, in_ranges (ly_rw L) a -> ~ in_ranges (ly_relro L) a.
  Hypothesis HLerr_rw : forall a, errno_win L a -> in_ranges (ly_rw L) a.

  #[local] Abbreviation cfg fx R pc M model := (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
  #[local] Abbreviation img_ro_clear_via_eff' := (img_ro_clear_via_eff L MI HLimg_lo HLerr_rw).
  #[local] Abbreviation sx_inv_via_eff' := (sx_inv_via_eff L MI ST HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw).

  Lemma hi_unowned : forall A M model a, ainv MI A M model -> alloc_ceiling <= a -> ~ owned MI A a.
  Proof using AC L MI HLimg_lo HLrw_img.
    intros A M model a AI Ha Ho.
    destruct (ai_owned_not_img_ro MI A M model a AI Ho) as [Hrw | Hni].
    - pose proof (HLimg_lo _ (HLrw_img _ Hrw)). lia.
    - pose proof (ai_owned_below_ceiling MI A M model a AI Ho Hni). lia.
  Qed.

  Section Main.
    Variables (fx : FPState) (A0 : AS MI) (s : LibIface.SX ST) (R0 : bvmap 5 word) (M0 : mem) (model0 : Model).
    Variables (sp ret obj bl bc : Z) (ents : list (Z * (Z * Z))) (K : TSet).
    #[local] Notation n := (bseq_next bc).
    Hypothesis CB : callB MI ST A0 s R0 M0 model0 sp ret (REHASH_STACK NEW_STACK DEL_STACK).
    Hypothesis H10 : getr R0 10%bv = Z_to_bv 64 obj.
    Hypothesis H11 : getr R0 11%bv = Z_to_bv 64 (rw_arg bc).
    Hypothesis U0 : umapx MI 24 (nval24 SEGS) A0 M0 obj bl bc ents.
    Hypothesis Hlast : bc <> BSEQ_LAST.
    Hypothesis HNMAX : LIB_NMAX <= NMAX MI.
    Hypothesis ASP : above_sp MI A0 sp obj 40.
    Hypothesis RC0 : ro_clear L M0.
    Hypothesis ROOM : roomL MI A0 (live MI A0) (8 * n).
    Hypothesis CONT : forall A' R' M' model' (bl' : Z) (ents' : list (Z * (Z * Z))),
        retB MI ST A' s R0 R' M' model0 model' ->
        umapx MI 24 (nval24 SEGS) A' M' obj bl' n ents' ->
        Permutation ents' ents ->
        lapply (live MI A0) (LAdd bl' (8 * n) :: (if bc =? 0 then [] else [LDel bl])) (live MI A') ->
        eff MI A0 A' M0 M' (sp - REHASH_STACK NEW_STACK DEL_STACK, sp)
            (fun a => umap_foot 24 obj bl bc ents a \/ umap_foot 24 obj bl' n ents' a) ->
        srealizes SEGS (cfg fx R' ret M' model') K.

    Definition SS : Z := 48 + Z.max NEW_STACK DEL_STACK.
    Definition W : Z * Z := (sp - SS, sp).

    Let AI0 := cb_ainv _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let MS0 := cb_mstd _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let CR0 := cb_regs _ _ _ _ _ _ _ _ _ _ _ _ CB.
    Let ROC0 := cb_roc _ _ _ _ _ _ _ _ _ _ _ _ CB.

    Lemma sp_facts : sp mod 16 = 0 /\ alloc_ceiling + SS <= sp /\ sp < 2 ^ 47 /\ 0x124000 <= sp - SS /\ 48 <= SS.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn A0 s R0 M0 model0 sp ret CB.
      destruct CR0. pose proof (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hc. unfold REHASH_STACK in Hc. unfold SS.
      pose proof ac_bounds_lit. repeat split; try assumption; lia.
    Qed.

    Lemma n_facts : In n BSEQ /\ bc < n /\ 8 * n <= 2 ^ 28 /\ ((bc = 0 /\ n = 2) \/ (3 <= n /\ Z.land n (n - 1) <> 0)).
    Proof using AC L MI A0 M0 obj bl bc ents U0 Hlast. exact (bseq_next_facts bc (u_bseq U0) Hlast). Qed.
    #[local] Opaque bseq_next.

    Ltac zpc z := lazymatch goal with |- srealizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
                    replace pc with (Z_to_bv 64 z : word) by (apply bv_eq; vm_compute; reflexivity) end.

    Lemma tailcall : forall Rr Mr,
        ainv MI A0 Mr model0 ->
        (forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mr x = M0 x) -> (forall x : word, M0 x <> None -> Mr x <> None) ->
        getr Rr 1%bv = Z_to_bv 64 ret -> getr Rr 2%bv = Z_to_bv 64 sp ->
        (forall r, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr Rr r = getr R0 r) ->
        getr Rr 10%bv = Z_to_bv 64 obj -> getr Rr 11%bv = Z_to_bv 64 n ->
        srealizes SEGS (cfg fx Rr REH Mr model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB U0 Hlast HNMAX ASP ROOM CONT.
      intros Rr Mr AIr HMw HMg G1 G2 Gs G10 G11.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold REHASH_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold REHASH_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      assert (EFc : eff MI A0 A0 M0 Mr W (fun _ => False)).
      { apply eff_store; [|exact HMg]. intros x HF HW. pose proof (u64_range x). apply HMw; intros Hx. apply HW. unfold W, W_of, SS. cbn. lia. }
      assert (ROCc : img_ro_clear L Mr).
      { eapply (img_ro_clear_via_eff' A0 A0 M0 Mr model0 W _ ROC0 AI0 EFc); [intros a [] | unfold W; cbn; lia]. }
      assert (SXc : sx_inv ST s Mr).
      { eapply (sx_inv_via_eff' s A0 A0 M0 Mr model0 W _ (cb_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) AI0 EFc
                 (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)); [intros a [] | unfold W; cbn; lia]. }
      eapply (REHASH fx A0 s Rr Mr model0 sp ret obj bl bc ents K).
      - constructor; [exact AIr | exact MS0 | exact ROCc | exact SXc | exact (cb_sxh _ _ _ _ _ _ _ _ _ _ _ _ CB) | | exact (cb_ceil _ _ _ _ _ _ _ _ _ _ _ _ CB) | | exact (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_own_sx _ _ _ _ _ _ _ _ _ _ _ _ CB) | exact (cb_err_sx _ _ _ _ _ _ _ _ _ _ _ _ CB)].
        + constructor; [exact G1 | exact Hret | exact Hretr | exact G2 | exact Hsp16 | exact Hsphi | rewrite Gs by inl; exact Hgp | rewrite Gs by inl; exact Htp].
        + unfold REHASH_STACK. fold SS. apply stack_room_of_defined; [lia | lia | lia |]. intros i Hi; apply HMg; exact (Hdef0 i Hi).
      - exact G10.
      - exact G11.
      - destruct ASP as (Hs1 & Hh1 & Ho1).
        eapply (umapx_via_eff L MI HLimg_lo HLrw_img HLerr_rw 24 _ (nval24 SEGS) ltac:(lia) (nval24_agree SEGS) A0 A0 M0 Mr model0 obj bl bc ents W _ sp U0 AI0 EFc);
          [exact Hs1 | unfold W; cbn; lia | lia | intros i Hi; eapply hi_unowned; [exact AI0 | lia] | intros a _ [] | unfold W, SS in *; cbn; lia | intros q m Hb Hl; exact Hl].
      - exact Hlast.
      - exact HNMAX.
      - exact ASP.
      - exact ROOM.
      - intros A' R' M' model' bl' ents' RB U' PERM LAP EFF.
        destruct RB as [AI' MS' Hfs Hfds SX' KEPT].
        apply (CONT A' R' M' model' bl' ents'); [| exact U' | exact PERM | exact LAP |].
        + constructor; try assumption.
          intros r Hr. rewrite (KEPT r Hr). unfold callee_saved in Hr. cbn in Hr.
          repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [ rewrite G1; symmetry; exact Hra | rewrite G2; symmetry; exact Hsp2 | apply Gs; inl ].
        + unfold REHASH_STACK in EFF |- *. fold SS in EFF |- *. change (sp - SS, sp) with W in EFF |- *.
          eapply eff_weaken; [eapply eff_trans; [exact EFc | exact EFF |]|].
          * intros a Ha. eapply hi_unowned; [exact AI' | unfold W, W_of in Ha; cbn in Ha; lia].
          * intros a [[]|Ha]. exact Ha.
    Qed.

    Theorem rehashw_correct : srealizes SEGS (cfg fx R0 RW M0 model0) K.
    Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NP REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw fx A0 s R0 M0 model0 sp ret obj bl bc ents K CB H10 H11 U0 Hlast HNMAX ASP RC0 ROOM CONT.
      destruct sp_facts as (Hsp16 & Hsplo & Hsphi & Hspimg & Hss). pose proof ceiling_lt as Hcl. pose proof ac_bounds_lit as Hcv.
      pose proof CR0 as CR. destruct CR as [Hra Hret Hretr Hsp2 _ _ Hgp Htp].
      destruct ASP as (Hs1 & Hh1 & Ho1).
      destruct n_facts as (HnB & Hbcn & Hn28 & Hncase).
      pose proof (cb_room _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hroom. unfold REHASH_STACK in Hroom. fold SS in Hroom.
      pose proof (cb_win _ _ _ _ _ _ _ _ _ _ _ _ CB) as Hwin0. unfold REHASH_STACK in Hwin0. fold SS in Hwin0.
      pose proof (defined_of_stack_room M0 sp SS ltac:(lia) ltac:(unfold SS; lia) ltac:(lia) Hroom) as Hdef0.
      assert (Hbc0 : 0 <= bc) by (pose proof (u_bseq U0) as HB; unfold BSEQ in HB; cbn in HB; lia).
      pose proof (u_obj_lo U0) as Hobjlo. pose proof (u_obj_hi U0) as Hobjhi.
      pose proof (h_bc (u_hdr U0)) as Cbc. unfold cell8 in Cbc.
      pose proof (u64_range (getr R0 8)) as Hr8. pose proof (u64_range (getr R0 9)) as Hr9. pose proof (u64_range (getr R0 18)) as Hr18.
      pose (E := Eseed R0 [Z_to_bv 64 obj; Z_to_bv 64 (rw_arg bc); Z_to_bv 64 sp; getr R0 1%bv; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv; Z_to_bv 64 bc]).
      assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 34);
                                          (1%bv, EVar 35); (8%bv, EVar 36); (9%bv, EVar 37); (18%bv, EVar 38)]) R0).
      { apply regs_ok_srs; [apply regs_ok_seed|].
        repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; first [assumption | reflexivity]. }
      assert (HK : know_ok SEGS E M0 [KWr (SA (EVar 34) (-32)) (ELit 32); KDisj (SA (EVar 32) 0) (ELit 40) (SA (EVar 34) (-48)) (ELit 48)]).
      { repeat apply Forall_cons; try apply Forall_nil.
        - eapply (kwr_stack_sub _ _ _ _ sp SS); [evs; reflexivity | reflexivity | lia | lia | lia | exact Hroom].
        - eapply kdisj_vars; [evs; reflexivity | evs; reflexivity | lia | lia | lia | lia | lia]. }

      assert (FRM : forall Mc, (forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mc x = M0 x) -> (forall x : word, M0 x <> None -> Mc x <> None) ->
                    ainv MI A0 Mc model0).
      { intros Mc HMcw HMcg. eapply (ai_frame MI); [exact AI0 | | exact HMcg | reflexivity | reflexivity].
        intros x Ho. pose proof (u64_range x). apply HMcw; intros Hx. exact (hi_unowned A0 M0 model0 (bv_unsigned x) AI0 ltac:(lia) Ho). }
      destruct (Z.eq_dec bc 0) as [Hbc | Hbc].
      -
        assert (Hn2 : n = 2) by (rewrite Hbc; reflexivity). clear Hncase.
        assert (Harg : rw_arg bc = 1) by (unfold rw_arg; rewrite Hbc; reflexivity).
        xruns HR HK 100%nat STOPS (SCR [false; false] [EVar 39] []) 50%N.
        { split_scs; try sc_auto1;
          first [ cbn [sc_denot]; evs; rewrite ?Harg, ?Hbc, ?Hn2; rewrite ?br_ne, ?br_geu by lia; bool_lia
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
        assert (HMcw : forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mc x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mc.
          rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 18%bv G18. rreg HRc 10%bv G10. rreg HRc 11%bv G11.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.
        apply (tailcall Rc Mc (FRM Mc HMcw HMcg) HMcw HMcg).
        + rewrite G1. exact Hra.
        + rewrite G2. nadd. rewrite ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]); try contradiction; first [exact G8 | exact G9 | exact G18 | apply Gs; inl].
        + exact G10.
        + rewrite G11. rewrite Hn2. reflexivity.
      -
        destruct Hncase as [[? _] | [Hn3 Hland]]; [lia|].
        assert (Harg : rw_arg bc = 2 * bc + 1) by (unfold rw_arg, np_arg; destruct (Z.eqb_spec bc 0); [lia | reflexivity]).
        pose proof (nparg_not_pow2 bc (u_bseq U0) Hbc) as Hnp2.
        assert (Hl2 : 0 <= Z.land (2 * bc + 1) (2 * bc + 1 - 1) <= 2 * (2 * bc + 1)).
        { pose proof (Z.add_lor_land (2 * bc + 1) (2 * bc + 1 - 1)). pose proof (Z.land_nonneg (2 * bc + 1) (2 * bc + 1 - 1)). pose proof (Z.lor_nonneg (2 * bc + 1) (2 * bc + 1 - 1)). lia. }
        pose proof (u_bseq U0) as HbB. unfold BSEQ in HbB. cbn in HbB.
        assert (Hbc28 : bc < 2 ^ 25) by lia. clear HbB.
        xruns HR HK 100%nat STOPS (SCR [true; false] [] []) 50%N.
        { split_scs; try sc_auto1; cbn [sc_denot]; evs; rewrite Harg; nadd; repeat match goal with |- context [?x + -1] => change (x + -1) with (x - 1) end;
          rewrite ?w_and by lia; rewrite ?br_eq, ?br_ne by lia; bool_lia. }
        postrun.
        rewrite <- (Z_to_bv_bv_unsigned 64 (getr R0 8)), <- (Z_to_bv_bv_unsigned 64 (getr R0 9)), <- (Z_to_bv_bv_unsigned 64 (getr R0 18)). rewrite Hra.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ ?Mx _) _) _ => rename H into HRc; rename Rx into Rc; set (Mc := Mx) end.
        assert (HMcw : forall x : word, ~ (sp - 32 <= bv_unsigned x < sp) -> Mc x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mc.
          rewrite !wbytes_outside; [reflexivity| ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMcg : forall x : word, M0 x <> None -> Mc x <> None) by (intros x Hx; unfold Mc; repeat apply wbytes_grows; exact Hx).
        rreg HRc 1%bv G1. rreg HRc 2%bv G2. rreg HRc 8%bv G8. rreg HRc 9%bv G9. rreg HRc 18%bv G18. rreg HRc 10%bv G10.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRc eq_refl) as Gs.

        assert (F1 : cell8 SEGS Mc (sp - 8) ret) by (unfold Mc, cell8; cellpeel).
        assert (F2 : cell8 SEGS Mc (sp - 16) (bv_unsigned (getr R0 8%bv))) by (unfold Mc, cell8; cellpeel).
        assert (F3 : cell8 SEGS Mc (sp - 24) (bv_unsigned (getr R0 9%bv))) by (unfold Mc, cell8; cellpeel).
        assert (F4 : cell8 SEGS Mc (sp - 32) (bv_unsigned (getr R0 18%bv))) by (unfold Mc, cell8; cellpeel).
        assert (RCc : ro_clear L Mc).
        { intros w Hw. pose proof (u64_range w). rewrite HMcw; [exact (RC0 w Hw)|]. intros Hx. destruct Hw as (Himg & _). pose proof (HLimg_lo _ Himg). unfold SS in Hsplo. lia. }

        destruct (NP fx Rc Mc bc (sp - 32) (Z_to_bv 64 NPR) (u_bseq U0) Hbc Hlast ltac:(rewrite G10; rewrite Harg; reflexivity) G1
                     ltac:(apply bv_eq; vm_compute; reflexivity) ltac:(rewrite G2; nadd; f_equal; lia)
                     ltac:(replace (sp - 32) with (sp + (-2) * 16) by lia; rewrite Z.mod_add by lia; exact Hsp16) ltac:(lia) ltac:(lia)
                     ltac:(apply stack_room_of_defined; [lia | lia | lia |]; unfold Mc; repeat apply defined_wbytes; eapply defined_sub; [exact Hdef0 | unfold SS; lia | lia]) RCc)
          as (Rn & Hms & KEPT & Qa0).
        eapply srz_msteps; [eapply ms_halt; exact MS0 | eapply ms_lazy; exact MS0 | exact Hms |].
        replace (sp - 32 - 8) with (sp - 40) by lia. zpc NPR.
        set (Mn := wbytes Mc _ _).
        assert (HMnw : forall x : word, ~ (sp - 48 <= bv_unsigned x < sp) -> Mn x = M0 x).
        { intros x Hx. pose proof (u64_range x). unfold Mn. rewrite wbytes_outside; [apply HMcw; lia | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        assert (HMng : forall x : word, M0 x <> None -> Mn x <> None) by (intros x Hx; unfold Mn; apply wbytes_grows; apply HMcg; exact Hx).
        assert (HMa : agree_on Mc Mn (sp - 32) 32).
        { intros i Hi. unfold Mn. pose proof (u64_range (Z_to_bv 64 (sp - 32 + i))). rewrite wbytes_outside; [reflexivity | ..]; rewrite ?length_N_to_le_bytes, ?u64_of_Z by lia; change (Z.of_nat 8) with 8; lia. }
        Ltac frc F HMa := eapply cellw_agree; [exact F | eapply agree_on_sub; [exact HMa | lia | cbn; lia] | lia | cbn; lia].
        assert (F1' : cell8 SEGS Mn (sp - 8) ret) by frc F1 HMa.
        assert (F2' : cell8 SEGS Mn (sp - 16) (bv_unsigned (getr R0 8%bv))) by frc F2 HMa.
        assert (F3' : cell8 SEGS Mn (sp - 24) (bv_unsigned (getr R0 9%bv))) by frc F3 HMa.
        assert (F4' : cell8 SEGS Mn (sp - 32) (bv_unsigned (getr R0 18%bv))) by frc F4 HMa.
        unfold cell8 in F1', F2', F3', F4'.
        assert (Cbc' : cellw SEGS Mn (obj + 8) 8 bc).
        { eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. symmetry. first [apply HMnw | symmetry; apply HMnw]. rewrite u64_of_Z by lia. unfold SS in Hsplo. lia. }
        unfold ret_ok in Hret.
        pose (E2 := Eseed Rn [Z_to_bv 64 obj; Z_to_bv 64 n; Z_to_bv 64 (sp - 32); Z_to_bv 64 bc; Z_to_bv 64 ret; getr R0 8%bv; getr R0 9%bv; getr R0 18%bv]).
        assert (HR2 : regs_ok E2 (srs sr_id [(8%bv, EVar 32); (10%bv, EVar 33); (2%bv, EVar 34)]) Rn).
        { assert (G2' : getr Rc 2%bv = Z_to_bv 64 (sp - 32)) by (rewrite G2; nadd; rewrite ?v_addi_Z by lia; first [reflexivity | f_equal; lia]).
          apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs;
            first [exact Qa0 | rewrite (KEPT 8%bv ltac:(unfold callee_saved; inl)); exact G8 | rewrite (KEPT 2%bv ltac:(unfold callee_saved; inl)); exact G2']. }
        assert (HK2 : know_ok SEGS E2 Mn []) by constructor.
        xruns HR2 HK2 100%nat STOPS (SCR [false] [EVar 35; EVar 36; EVar 37; EVar 38; EVar 39] []) 50%N.
        { split_scs;
          first [ eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | cbn [sc_denot]; evs; rewrite br_geu by lia; bool_lia
                | eapply sc_flat; [evs; reflexivity | lia | cbn [a_off]; lia | lia | cbn [a_off]; lia]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F1'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F2'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F3'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity]
                | eapply (sc_read_cellw _ _ _ _ _ _ _ _ F4'); [cbn; lia | evs; rewrite ?v_addi_Z by lia; f_equal; lia | evs; rewrite Z_to_bv_bv_unsigned; reflexivity] ]. }
        postrun.
        lazymatch goal with H : regs_ok _ _ ?Rx |- srealizes _ (mkCfg (mkst ?Rx _ _ _) _) _ => rename H into HRr; rename Rx into Rr end.
        rreg HRr 1%bv T1. rreg HRr 2%bv T2. rreg HRr 8%bv T8. rreg HRr 9%bv T9. rreg HRr 18%bv T18. rreg HRr 10%bv T10. rreg HRr 11%bv T11.
        rewrite ?Z_to_bv_bv_unsigned in T8, T9, T18.
        pose proof (syms_id_sound _ _ _ _ [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HRr eq_refl) as Ts.
        apply (tailcall Rr Mn (FRM Mn HMnw HMng) HMnw HMng).
        + exact T1.
        + rewrite T2. nadd. rewrite ?v_addi_Z by lia. first [reflexivity | f_equal; lia].
        + intros r Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]); try contradiction;
            first [exact T8 | exact T9 | exact T18 | rewrite Ts by inl; rewrite KEPT by (unfold callee_saved; inl); apply Gs; inl].
        + exact T10.
        + exact T11.
    Qed.
  End Main.

  Theorem rehashw_spec : rehashw_stmt SEGS L MI ST NEW_STACK DEL_STACK RW.
  Proof using AC L MI ST NEW_STACK DEL_STACK NEW_STACK_nn DEL_STACK_nn NP REHASH HLimg_lo HLrw_img HLrelro_img HLrw_relro HLerr_rw.
    intros fx A s R M model sp ret obj bl bc ents K CB H10 H11 U0 Hlast HNMAX ASP RC ROOM CONT.
    eapply rehashw_correct; eassumption.
  Qed.
End RW.
End HRehashWU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRehashW2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNextPrimeU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HMvaU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HMva2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HNtU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMvaU1A OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMvaNTU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateMvaU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStateDtorU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmtsHdr OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablImgU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablPtrFacts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SmallU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_JumpU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_AccessorsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_StrlenU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_SplitU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation tc := Img.tc.

Definition OS_RETS : list Z := [0x6c5dc].
Definition BE_RETS : list Z := [0x6bfd8; 0x6c008].

Section Split.
Context {AC : AllocCeiling}.

  Theorem opcode_split_spec : opcode_split_stmt SEGS tc.
  Proof using AC.
    intros fx R M w pwc pop ret Ha0 Ha1 Ha2 Hw Hc1 Hh1 Hc2 Hh2 Hal1 Hal2 Hd1 Hd2 Hra Hret.
    pose proof ac_bounds_lit as HAC.
    pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 w); Z_to_bv 64 pwc; Z_to_bv 64 pop]).
    pose proof (sx32_range w Hw) as Hsw.
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 33) 2; KAlign (EVar 34) 2]).
    { constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]];
      [eapply krange_var; [evs; reflexivity | lia | lia] | eapply krange_var; [evs; reflexivity | lia | lia]
      | eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal1] | eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal2] ]. }
    assert (D1 : defined M pwc 2) by (intros i Hi; apply Hd1; lia).
    assert (D2 : defined M pop 2) by (intros i Hi; apply Hd2; lia).
    xrun HR HK 60%nat OS_RETS (SCR [] [] []) 40%N.
    { split_scs; sc_so; rewrite Z.add_0_r; [exact D2 | exact D1]. }
    match type of Hms with msteps _ _ (mkst _ _ ?M1 _) =>
      match goal with |- exists R'', msteps _ _ (mkst _ _ ?M2 _) /\ _ => assert (EM : M1 = M2) end end.
    { evs. rewrite !v_addi_Z by lia. rewrite !Z.add_0_r.
      rewrite srl16_val by lia.
      rewrite (w2_eq (TablStmts.sx32 w / 2 ^ 16) (w / 2 ^ 16)) by (apply sx32_hi16; lia).
      rewrite (w2_eq (TablStmts.sx32 w) (w mod 2 ^ 16)) by (rewrite sx32_mod16 by lia; rewrite Z.mod_mod by lia; reflexivity).
      reflexivity. }
    rewrite EM in Hms.
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    exists R'. split; [| exact (kept_of_syms _ _ _ R' HR' eq_refl)].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ].
  Qed.

  Theorem binary_endianness_spec : binary_endianness_stmt SEGS L tc.
  Proof using AC.
    intros fx R M pb pe words n sp ret HRO Ha0 Ha1 Hsp Fw Fn Hn Hw0 Hwn Hdw Hce Hpe4 Hdpe Hcb Hpb16 Hal8 Hal4w Hal4e Hdisj Hroom Hcs Hsp47 Hra Hret.
    pose proof ac_bounds_lit as HAC.
    destruct (mdef4_fld SEGS M words Hdw ltac:(lia) ltac:(lia)) as (ew & Hew & Few).
    assert (Cew : cell4 SEGS M words ew) by (split; [cbn; lia | exact Few]).
    assert (Hn64 : n < 2 ^ 45) by lia.
    assert (Cw : cell8 SEGS M pb words) by (split; [cbn; lia | exact Fw]).
    assert (Cn : cell8 SEGS M (pb + 8) n) by (split; [cbn; lia | exact Fn]).
    assert (Dpe : defined M pe 4) by (intros i Hi; apply Hdpe; lia).
    pose (E := Eseed R [Z_to_bv 64 pb; Z_to_bv 64 pe; Z_to_bv 64 words; Z_to_bv 64 n;
                        Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 words; Z_to_bv 64 n; Z_to_bv 64 ew]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 33) 1 (2 ^ 47); KAlign (EVar 32) 8; KAlign (EVar 33) 4;
                                  KRange (EVar 40) 1 (2 ^ 47); KAlign (EVar 40) 4; KRange (EVar 41) 1 (2 ^ 45)]).
    { repeat (constructor; [first [ eapply krange_var; [evs; reflexivity | lia | lia]
                                   | eapply kalign_var; [evs; reflexivity | lia | lia | assumption] ] |]); constructor. }
    destruct (mdef4_fld SEGS M pe Hdpe ltac:(lia) ltac:(lia)) as (e0 & He0 & Fe0).
    xtree HR HK 80%nat BE_RETS 40%N (@nil bool) [EVar 40; EVar 41; EVar 42]
      ltac:(try sc_auto1; sc_so; rewrite Z.add_0_r; exact Dpe) ltac:(idtac) ltac:(br_kill_all).
    all: assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    all: rreg HR' 10%bv H10.
    all: lazymatch type of Hms with msteps _ _ (mkst ?R1 (Z_to_bv 64 _) ?MF _) =>
           lazymatch type of H10 with _ = Z_to_bv 64 ?rv =>
             let r := eval vm_compute in (if rv <? 2 ^ 63 then rv else rv - 2 ^ 64)%Z in
             exists R1, MF, r end end.

    all: lazymatch goal with
         | |- exists e, msteps _ _ (mkst _ _ (wbytes _ _ (word_to_le_bytes 4 (edenot _ (ELit ?v)))) _) /\ _ => exists v
         | |- _ => exists e0
         end.
    all: split; [eapply msteps_trans; [exact Hms | eapply ret_run; [ vm_compute; reflexivity | exact Hra1 | exact Hret ]] |].
    all: split; [exact (kept_of_syms _ _ _ R' HR' eq_refl) |].
    all: split; [rewrite H10; apply bv_eq; vm_compute; reflexivity |].
    all: split; [lia|]. all: split; [lia|].
    all: evs; rewrite ?v_addi_Z by lia; rewrite ?Z.add_0_r.
    all: lazymatch goal with
         | |- CRep.fld _ (wbytes _ _ _) _ _ _ /\ _ =>
             split; [apply fld_wbytes4; lia|]; split; [intros; lia|];
             split; [apply frame_wbytes4; [lia|lia|intros x Hx; left; unfold zwin; lia] |];
             intros a Ha; apply defined_wbytes4; [lia|lia|exact Ha]
         | |- _ =>
             split; [exact Fe0|]; split; [intros; lia|]; split; [intros a _; reflexivity | intros a Ha; exact Ha]
         end.
  Qed.
End Split.
End Tabl_SplitU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_LookupOpndU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablByValue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module Tabl_LookupExtU1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.MmapSim.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont.CRep.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsGrammar.
Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablData OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablGrammar OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.TablByValue.

Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module Img := TablImgU1.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Abbreviation L := Img.Ly.L.
Abbreviation ti := Img.ti.
Abbreviation tc := Img.tc.

Definition LE_ENTRY : Z := 0x6cecc.
Definition LE_LOOP  : Z := 0x6d040.
Definition LE_EXIT  : Z := 0x6d0ac.
Definition LE_RET   : Z := 0x6d0d4.
Definition LE_TRAP  : Z := 0x6d0a8.
Definition LE_STOPS : list Z := [LE_LOOP; LE_EXIT; LE_RET; LE_TRAP].
Definition NEXT : Z := 500.
Lemma NEXT_eq : Zlen EXT = NEXT. Proof. reflexivity. Qed.
Lemma ext_base_bounds : 0x10000 <= ti_ext ti /\ ti_ext ti + 28 * NEXT + 28 <= 2 ^ 40.
Proof. unfold NEXT. cbn [ti_ext Img.ti]. lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma half_bounds : forall len, 0 < len -> 0 <= len / 2 < len /\ 0 <= len - len / 2 - 1 < len.
Proof. intros len H. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation V := (VAL EXT).

Lemma addchk_false : forall a k, 0 <= a -> 0 <= k -> a + k < 2 ^ 63 ->
  branch_taken BC_EQ (alu64 ALU_XOR (alu64 ALU_XOR (alu64 ALU_SLTU (Z_to_bv 64 (a + k)) (Z_to_bv 64 a)) (Z_to_bv 64 0)) (Z_to_bv 64 1)) (Z_to_bv 64 0) = false.
Proof.
  intros a k Ha Hk Hak. rewrite w_sltu by lia. destruct (Z.ltb_spec (a + k) a); [lia|].
  replace (alu64 ALU_XOR (alu64 ALU_XOR (Z_to_bv 64 0) (Z_to_bv 64 0)) (Z_to_bv 64 1)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity).
  rewrite br_eq by lia. reflexivity.
Qed.

Section LE.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (M : mem) (y : Z) (f c : Z).
  Hypothesis HRO : ro_clear L M.
  Hypothesis Hy : 0 <= y < 2 ^ 32.
  Hypothesis Hf : 0 <= f.
  Hypothesis Hc : 0 <= c.
  Hypothesis Hfc : f + c <= NEXT.
  Hypothesis HS : sorted_adj (map v_value (zsub f c EXT)) = true.
  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)).
  Let base := ti_ext ti.

  Definition keptX (R R' : bvmap 5 word) : Prop :=
    kept R R' /\ getr R' 10%bv = getr R 10%bv /\ getr R' 11%bv = getr R 11%bv /\ getr R' 12%bv = getr R 12%bv
    /\ getr R' 13%bv = getr R 13%bv /\ getr R' 16%bv = getr R 16%bv.
  Lemma keptX_trans : forall R1 R2 R3, keptX R1 R2 -> keptX R2 R3 -> keptX R1 R3.
  Proof using y Hy. intros R1 R2 R3 (A & B) (D & E). split; [exact (keeps_cs_trans _ _ _ A D) | repeat split; intuition congruence]. Qed.
  Ltac keptX_of HR' :=
    split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)
          | repeat split;
            [ let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 11%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 12%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 13%bv H; first [exact H | rewrite H; symmetry; assumption]
            | let H := fresh in rreg HR' 16%bv H; first [exact H | rewrite H; symmetry; assumption] ] ].

  Definition split_at (i len : Z) : Prop :=
    (forall j, f <= j < i -> V j < y) /\ (forall j, i + len <= j < f + c -> y <= V j).

  Definition LREG (R : bvmap 5 word) (i len : Z) : Prop :=
    getr R 15%bv = Z_to_bv 64 (base + 28 * i) /\ getr R 14%bv = Z_to_bv 64 len /\ getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) /\
    getr R 17%bv = Z_to_bv 64 28 /\ getr R 5%bv = Z_to_bv 64 (-28).

  Lemma lb_step : forall R i len,
    f <= i -> 0 < len -> i + len <= f + c -> LREG R i len ->
    let half := len / 2 in
    let i' := (if y <=? V (i + half) then i else i + half + 1) in
    let len' := (if y <=? V (i + half) then half else len - half - 1) in
    exists R', keptX R R' /\
      msteps SEGS (st R LE_LOOP) (st R' (if len' =? 0 then LE_EXIT else LE_LOOP)) /\ LREG R' i' len'.
  Proof using fx M y f c HRO Hy Hf Hfc.
    intros R i len Hi Hlen Hil (H15 & H14 & H11 & H17 & H5) half i' len'.
    pose proof ext_base_bounds as [B0 B1]. pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    assert (Hbase : base = 0x4094c) by reflexivity.
    pose proof (VAL_row EXT_KIND EXT ext_cert (i + half)) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
    pose proof (ext_cell SEGS L ti Img.rodata Img.IFX M (i + half) HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
    pose (E := Eseed R [Z_to_bv 64 (base + 28 * i); Z_to_bv 64 len; Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        sxw (V (i + half))]).
    assert (HR : regs_ok E (srs sr_id [(15%bv, EVar 32); (14%bv, EVar 33); (11%bv, EVar 34); (17%bv, ELit 28); (5%bv, ELit (-28))]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 0x4094c (0x4094c + 28 * 500); KAlign (EVar 32) 4; KRange (EVar 33) 1 500]).
    { repeat apply Forall_cons; [ | | | apply Forall_nil].
      - eapply krange_var; [evs; reflexivity | unfold NEXT in *; lia | subst base; rewrite Hbase; unfold NEXT in *; lia].
      - eapply kalign_var; [evs; reflexivity | unfold NEXT in *; lia | lia | subst base; rewrite Hbase].
        replace (264524 + 28 * i) with ((66131 + 7 * i) * 4) by lia. apply Z_mod_mult.
      - eapply krange_var; [evs; reflexivity | unfold NEXT in *; lia | unfold NEXT in *; lia]. }
    assert (ADDR : alu64 ALU_ADD (Z_to_bv 64 (base + 28 * i)) (mul_div M_MUL (Z_to_bv 64 28) (alu64 ALU_SRL (Z_to_bv 64 len) (Z_to_bv 64 1)))
                   = Z_to_bv 64 (base + 28 * (i + half))).
    { rewrite w_srl by lia. change (2 ^ 1) with 2. rewrite zbv_mul, zbv_add. f_equal. subst half. lia. }
    assert (RD : sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 28) (EAlu ALU_SRL (EVar 33) (ELit 1)))) 0) 4 true (EVar 40))).
    { eapply (sc_read_cell4_sx _ _ _ _ _ _ _ CELL); [| evs; reflexivity].
      unfold adenot. cbn [a_base a_off]. evs. rewrite ADDR. rewrite v_addi_Z by (unfold NEXT in *; lia). f_equal. lia. }
    assert (HAC_ : sc_denot SEGS M E (SCBr false BC_EQ
              (EAlu ALU_XOR (EAlu ALU_XOR (EAlu ALU_SLTU
                 (EAlu ALU_ADD (EVar 32) (EMd M_MUL (ELit 28) (EAlu ALU_SRL (EVar 33) (ELit 1)))) (EVar 32)) (ELit 0)) (ELit 1)) (ELit 0))).
    { cbn [sc_denot]. evs. rewrite ADDR.
      replace (base + 28 * (i + half)) with (base + 28 * i + 28 * half) by lia. apply addchk_false; unfold NEXT in *; lia. }
    assert (BR : forall b : bool, (if b then y <= V (i + half) else V (i + half) < y) ->
                 sc_denot SEGS M E (SCBr b BC_GEU (EVar 40) (EVar 34))).
    { intros b Hb. cbn [sc_denot]. evs. rewrite sx32_sxw by lia. rewrite br_geu_sxw by lia. destruct b; bool_lia. }
    assert (LEN0 : forall b : bool, (if b then len' = 0 else len' <> 0) ->
      sc_denot SEGS M E (SCBr b BC_EQ
         (if y <=? V (i + half) then EAlu ALU_SRL (EVar 33) (ELit 1)
          else EAlu ALU_ADD (EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EAlu ALU_SRL (EVar 33) (ELit 1)))) (ELit (-1))) (ELit 0))).
    { intros b Hb. subst len'. cbn [sc_denot]. destruct (Z.leb_spec y (V (i + half))); cbn [sc_denot]; evs;
        rewrite w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite ?zbv_mul, ?zbv_add.
      - rewrite br_eq by lia. destruct b; bool_lia.
      - replace (len + -1 * half + -1) with (len - half - 1) by lia. rewrite br_eq by lia. destruct b; bool_lia. }
    assert (POST : forall R', regs_ok E [] R' -> True) by (intros; exact I).
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [false; true; true] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact GE | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 15%bv X; exact X | rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite Hz; reflexivity
                      | rreg HR' 11%bv X; exact X | rreg HR' 17%bv X; exact X | rreg HR' 5%bv X; exact X].
      + subst i' len'. replace (half =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [false; true; false] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact GE | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 15%bv X; exact X | rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; reflexivity
                      | rreg HR' 11%bv X; exact X | rreg HR' 17%bv X; exact X | rreg HR' 5%bv X; exact X].
    - destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + subst i' len'. rewrite Hz. cbn [Z.eqb].
        xrun HR HK 40%nat LE_STOPS (SCR [false; false; true] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact LT | apply (LEN0 true); exact Hz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 15%bv X; rewrite X, ADDR, zbv_add; f_equal; lia
                      | rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 11%bv X; exact X | rreg HR' 17%bv X; exact X | rreg HR' 5%bv X; exact X].
      + subst i' len'. replace (len - half - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz).
        xrun HR HK 40%nat LE_STOPS (SCR [false; false; false] [EVar 40] []) 41%N.
        { split_scs; first [exact HAC_ | exact RD | apply BR; exact LT | apply (LEN0 false); exact Hnz | sc_auto1]. }
        exists R'. split; [keptX_of HR'|]. split; [exact Hms|].
        repeat split; [rreg HR' 15%bv X; rewrite X, ADDR, zbv_add; f_equal; lia
                      | rreg HR' 14%bv X; rewrite X, w_srl by lia; change (2 ^ 1) with 2; fold half; rewrite !zbv_mul, !zbv_add; f_equal; lia
                      | rreg HR' 11%bv X; exact X | rreg HR' 17%bv X; exact X | rreg HR' 5%bv X; exact X].
  Qed.

  Lemma lb_loop : forall (m : nat) R i len,
    len <= Z.of_nat m -> f <= i -> 0 < len -> i + len <= f + c -> split_at i len -> LREG R i len ->
    exists R' i', keptX R R' /\ msteps SEGS (st R LE_LOOP) (st R' LE_EXIT) /\
      LREG R' i' 0 /\ f <= i' <= f + c /\ split_at i' 0.
  Proof using fx M y f c HRO Hy Hf Hfc HS.
    induction m as [|m IH]; intros R i len Hm Hi Hlen Hil [SL SR] HL; [lia|].
    pose proof (half_bounds len Hlen) as [Hh1 Hh2].
    destruct (lb_step R i len Hi Hlen Hil HL) as (R1 & K1 & MS1 & HL1).
    cbv zeta in MS1, HL1.
    set (half := len / 2) in *.
    destruct (Z.leb_spec y (V (i + half))) as [GE|LT].
    - assert (SPL : split_at i half).
      { split; [exact SL|]. intros j Hj. destruct (Z.lt_ge_cases j (i + len)); [|apply SR; lia].
        pose proof (VAL_mono EXT_KIND EXT ext_cert f c (i + half) j Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec half 0) as [Hz|Hnz].
      + exists R1, i. split; [exact K1|]. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct (IH R1 i half ltac:(lia) Hi ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
    - assert (SPL : split_at (i + half + 1) (len - half - 1)).
      { split; [|intros j Hj; apply SR; lia]. intros j Hj. destruct (Z.lt_ge_cases j i); [apply SL; lia|].
        pose proof (VAL_mono EXT_KIND EXT ext_cert f c j (i + half) Hf ltac:(rewrite NEXT_eq; lia) HS ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
      destruct (Z.eqb_spec (len - half - 1) 0) as [Hz|Hnz].
      + exists R1, (i + half + 1). split; [exact K1|]. split; [exact MS1|]. split; [rewrite Hz in HL1; exact HL1|]. split; [lia|]. rewrite Hz in SPL. exact SPL.
      + destruct (IH R1 (i + half + 1) (len - half - 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SPL HL1) as (R' & i' & K' & MS' & P).
        exists R', i'. split; [exact (keptX_trans _ _ _ K1 K')|]. split; [eapply msteps_trans; [exact MS1|exact MS']|]. exact P.
  Qed.

  Lemma tail_block : forall R i pd (ret : word),
    f <= i <= f + c -> split_at i 0 ->
    getr R 15%bv = Z_to_bv 64 (base + 28 * i) -> getr R 13%bv = Z_to_bv 64 (base + 28 * f) -> getr R 16%bv = Z_to_bv 64 (28 * c) ->
    getr R 11%bv = Z_to_bv 64 (TablStmts.sx32 y) -> getr R 12%bv = Z_to_bv 64 pd -> getr R 10%bv = Z_to_bv 64 (-9) ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> pd mod 8 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M',
      kept R R' /\ msteps SEGS (st R LE_EXIT) (@mkst fx R' ret M' (seg_rom SEGS)) /\
      ( (i < f + c /\ V i = y /\ getr R' 10%bv = Z_to_bv 64 0 /\ M' = wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (base + 28 * i))))
      \/ (~ (i < f + c /\ V i = y) /\ getr R' 10%bv = Z_to_bv 64 (-9) /\ M' = M) ).
  Proof using fx AC M y f c HRO Hy Hf Hc Hfc.
    intros R i pd ret Hi [SL SR] H15 H13 H16 H11 H12 H10 Hce Hpd Hdef Hal Hra Hret.
    pose proof ext_base_bounds as [B0 B1]. pose proof ac_bounds_lit as HAC. assert (Hbase : base = 0x4094c) by reflexivity.
    assert (Dpd : defined M pd 8) by (intros k Hk; apply Hdef; lia).
    assert (ENDEQ : alu64 ALU_ADD (Z_to_bv 64 (28 * c)) (Z_to_bv 64 (base + 28 * f)) = Z_to_bv 64 (base + 28 * (f + c))).
    { rewrite zbv_add. f_equal. lia. }
    pose (E := Eseed R [Z_to_bv 64 (base + 28 * i); Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd; Z_to_bv 64 (28 * c); Z_to_bv 64 (base + 28 * f); Z_to_bv 64 (-9); Z_to_bv 64 0; Z_to_bv 64 0; sxw (V i)]).
    assert (HR : regs_ok E (srs sr_id [(15%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (16%bv, EVar 35); (13%bv, EVar 36); (10%bv, EVar 37)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M [KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 8; KRange (EVar 32) 0x4094c (0x4094c + 28 * 500); KAlign (EVar 32) 4]).
    { repeat apply Forall_cons; [ | | | | apply Forall_nil].
      - eapply krange_var; [evs; reflexivity | lia | lia].
      - eapply kalign_var; [evs; reflexivity | lia | lia | exact Hal].
      - eapply krange_var; [evs; reflexivity | unfold NEXT in *; lia | subst base; rewrite Hbase; unfold NEXT in *; lia].
      - eapply kalign_var; [evs; reflexivity | unfold NEXT in *; lia | lia | subst base; rewrite Hbase].
        replace (264524 + 28 * i) with ((66131 + 7 * i) * 4) by lia. apply Z_mod_mult. }
    destruct (Z_lt_le_dec i (f + c)) as [Hlt|Hge].
    - pose proof (VAL_row EXT_KIND EXT ext_cert i) as VR0. rewrite NEXT_eq in VR0. destruct (VR0 ltac:(lia)) as (r & _ & _ & HV). clear VR0.
      pose proof (ext_cell SEGS L ti Img.rodata Img.IFX M i HRO) as CL. rewrite NEXT_eq in CL. destruct (CL ltac:(lia)) as (CELL & _ & _). clear CL.
      assert (BE : sc_denot SEGS M E (SCBr false BC_EQ (EVar 32) (EAlu ALU_ADD (EVar 35) (EVar 36)))).
      { cbn [sc_denot]. evs. rewrite ENDEQ. rewrite br_eq by lia. bool_lia. }
      destruct (Z.eq_dec (V i) y) as [EQ|NE].
      + xrun HR HK 30%nat LE_STOPS (SCR [false; false] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL | sc_so; rewrite Z.add_0_r; exact Dpd
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', _. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        left. split; [exact Hlt|]. split; [exact EQ|]. split; [rreg HR' 10%bv H10'; exact H10'|].
        evs. rewrite v_addi_Z by lia. rewrite Z.add_0_r. reflexivity.
      + xrun HR HK 30%nat LE_STOPS (SCR [false; true] [EVar 40] []) 41%N.
        { split_scs; try sc_auto1; first [exact BE | sc_rd_sx CELL
                                          | cbn [sc_denot]; evs; rewrite sx32_sxw by lia; rewrite br_ne_sxw by lia; bool_lia ]. }
        assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
        eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
        { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
        right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
    - assert (Hi' : i = f + c) by lia.
      xrun HR HK 30%nat LE_STOPS (SCR [true] [EVar 40] []) 41%N.
      { split_scs; try sc_auto1. all: cbn [sc_denot]; evs; rewrite ENDEQ; rewrite Hi'; rewrite br_eq by lia; bool_lia. }
      assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
      eexists R', M. split; [exact (kept_of_syms _ _ _ _ HR' eq_refl)|]. split.
      { eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret]. }
      right. split; [lia|]. split; [rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity | reflexivity].
  Qed.
End LE.

Section Post.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variables (R : bvmap 5 word) (M : mem) (x y pd sp : Z) (ret : word).

  #[local] Notation le_post R' M' r d :=
    (msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_ext TG x y = Some l)) /\ (r = 0 -> edesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None)) (only parsing).

  Lemma post_missed : forall R', find_ext x y = None -> mdef M pd 8 -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 (-9) ->
    exists R'' M' r d, le_post R'' M' r d.
  Proof using fx AC R M x y pd sp ret.
    intros R' Hnone Hdef Hce Hpd MS K A10. pose proof ac_bounds_lit.
    destruct (mdef8_fld SEGS M pd Hdef ltac:(lia) ltac:(lia)) as (d0 & _ & Fd0).
    exists R', M, (-9), d0. split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [exact Fd0|].
    split. { split; [intros C; lia|]. intros [l Hl]. cbn [g_ext TG] in Hl. unfold tg_ext in Hl. rewrite Hnone in Hl. discriminate. }
    split. { intros C; lia. }
    split; [intros a _; reflexivity | intros a Ha; exact Ha].
  Qed.

  Lemma post_found : forall R' i r, find_ext x y = Some (i, r) -> alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 ->
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS))
                (@mkst fx R' ret (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_ext ti + 28 * i)))) (seg_rom SEGS)) ->
    kept R R' -> getr R' 10%bv = Z_to_bv 64 0 ->
    exists R'' M' rr d, le_post R'' M' rr d.
  Proof using fx AC R M x y pd sp ret.
    intros R' i r Hf Hce Hpd MS K A10. pose proof ac_bounds_lit.
    exists R', (wbytes M (Z_to_bv 64 pd) (word_to_le_bytes 8 (Z_to_bv 64 (ti_ext ti + 28 * i)))), 0, (ti_ext ti + 28 * i).
    split; [exact MS|]. split; [exact K|]. split; [exact A10|]. split; [lia|]. split; [apply fld_wbytes8; lia|].
    split. { split; [|intros; reflexivity]. intros _. exists (v_span r). cbn [g_ext TG]. unfold tg_ext. rewrite Hf. reflexivity. }
    split. { intros _. exists i, r. split; [exact Hf | reflexivity]. }
    split. { apply frame_wbytes8; [lia|lia|]. intros a Ha. left. unfold zwin. lia. }
    intros a Ha. apply defined_wbytes8; [lia|lia|exact Ha].
  Qed.
End Post.

Lemma HKimg_ext : forall E M, ro_clear L M -> know_ok SEGS E M [KImg (ti_ro_lo ti) (ti_ro_hi ti)].
Proof. intros E M HRO. constructor; [|constructor]. apply (kimg_ro SEGS L E M _ _ HRO Img.rodata); cbn; lia. Qed.

Lemma kind_run {AC : AllocCeiling} : forall (fx : FPState) R M x y pd sp (ret : word) R1 f c,
  ro_clear L M -> 0 <= y < 2 ^ 32 -> kind_range EXT_KIND x = (f, c) -> 0 <= f -> 0 < c -> f + c <= NEXT ->
  sorted_adj (map v_value (zsub f c EXT)) = true ->
  alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> pd mod 8 = 0 -> getr R 1%bv = ret -> ret_ok ret ->
  msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R1 (Z_to_bv 64 LE_LOOP) M (seg_rom SEGS)) ->
  kept R R1 ->
  LREG y R1 f c ->
  getr R1 13%bv = Z_to_bv 64 (ti_ext ti + 28 * f) -> getr R1 16%bv = Z_to_bv 64 (28 * c) -> getr R1 12%bv = Z_to_bv 64 pd -> getr R1 10%bv = Z_to_bv 64 (-9) ->
  exists R' M' r d,
    msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
    /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
    /\ CRep.fld SEGS M' pd 8 d
    /\ (r = 0 <-> (exists l, g_ext TG x y = Some l)) /\ (r = 0 -> edesc ti d x y)
    /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
    /\ (forall a : word, M a <> None -> M' a <> None).
Proof.
  intros fx R M x y pd sp ret R1 f c HRO Hy Hk Hf Hc Hfc HS Hce Hpd Hdef Hal Hra Hret MS1 K1 HL1 A13 A16 A12 A10.
  assert (SP0 : split_at y f c f c) by (split; intros j Hj; lia).
  destruct (lb_loop M y f c HRO Hy Hf Hfc HS (Z.to_nat c) R1 f c ltac:(lia) ltac:(lia) Hc ltac:(lia) SP0 HL1)
    as (R2 & i & (K2 & K2a & K2b & K2c & K2d & K2e) & MS2 & (B15 & _ & B11 & _) & Hi & SPL).
  destruct (tail_block M y f c HRO Hy Hf ltac:(lia) Hfc R2 i pd ret Hi SPL B15
              ltac:(rewrite K2d; exact A13) ltac:(rewrite K2e; exact A16) B11 ltac:(rewrite K2c; exact A12) ltac:(rewrite K2a; exact A10)
              Hce Hpd Hdef Hal ltac:(rewrite K2, K1; [exact Hra | (first [solve [clear; cbn; tauto] | cbn; tauto]) | (first [solve [clear; cbn; tauto] | cbn; tauto])]) Hret) as (R3 & M' & K3 & MS3 & RES).
  assert (KK : kept R R3) by (exact (keeps_cs_trans _ _ _ (keeps_cs_trans _ _ _ K1 K2) K3)).
  assert (MS : msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_lookup_ext tc)) M (seg_rom SEGS)) (@mkst fx R3 ret M' (seg_rom SEGS))).
  { eapply msteps_trans; [exact MS1|]. eapply msteps_trans; [exact MS2|exact MS3]. }
  destruct SPL as [SL SR]. rewrite Z.add_0_r in SR.
  destruct RES as [(Hlt & HV & B10 & HM')|(Hno & B10 & HM')]; subst M'.
  - destruct (lbv_found EXT_KIND EXT ext_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HV SL) as (r & Hfd & Hr).
    eapply post_found; [exact Hfd | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
  - pose proof (lbv_missed EXT_KIND EXT ext_cert x f c y i Hk Hf ltac:(lia) ltac:(rewrite NEXT_eq; lia) HS Hi SL SR Hno) as Hnone.
    eapply post_missed; [exact Hnone | exact Hdef | exact Hce | exact Hpd | exact MS | exact KK | exact B10].
Qed.

Theorem lookup_ext_spec {AC : AllocCeiling} : lookup_ext_stmt SEGS L TG tc (edesc ti).
Proof.
  intros fx R M x y pd sp ret HRO Ha0 Hx _ H3 Hsp Hce Hpd8 Hdef Hal Hdisj Hroom Hcs Hsp47 Hsp16 Hra Hret.
  destruct (H3 eq_refl) as (H11 & Hy & H12). clear H3.
  pose proof ac_bounds_lit as HAC. pose proof ext_base_bounds as [B0 B1].

  assert (Hcases : x = 0 \/ 16 <= x \/ (1 <= x < 1 + Z.of_nat 15)) by lia.
  destruct Hcases as [X0 | [X16 | XR]].
  -
    subst x. pose (E := Eseed R (@nil word)).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 40%nat LE_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    eapply (post_missed R M 0 y pd sp ret R'); [apply (kind_empty EXT_KIND EXT); reflexivity | exact Hdef | exact Hce | exact Hpd8 | | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  -
    pose (E := Eseed R [Z_to_bv 64 x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; exact Ha0. }
    assert (HK : know_ok SEGS E M [KRange (EVar 32) 16 (2 ^ 32)]).
    { constructor; [|constructor]. eapply krange_var; [evs; reflexivity | lia | lia]. }
    xrun HR HK 40%nat LE_STOPS (SCR [] [] []) 41%N. { split_scs; try sc_auto1. }
    assert (Hra1 : getr R' 1%bv = ret) by (etransitivity; [apply (kept_of_syms _ _ _ R' HR' eq_refl); (first [solve [clear; cbn; tauto] | cbn; tauto]) | exact Hra]).
    assert (Hk0 : kind_range EXT_KIND x = (0, 0)).
    { unfold kind_range.
      destruct (find (fun k => v_value k =? x) EXT_KIND) as [k|] eqn:EF; [|reflexivity].
      apply find_some in EF as [Hin Eq]. apply Z.eqb_eq in Eq. exfalso.
      assert (HB : forallb (fun k => v_value k <? 16) EXT_KIND = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in HB. specialize (HB k Hin). apply Z.ltb_lt in HB. lia. }
    eapply (post_missed R M x y pd sp ret R'); [apply (kind_empty EXT_KIND EXT); exact Hk0 | exact Hdef | exact Hce | exact Hpd8 | | exact (kept_of_syms _ _ _ _ HR' eq_refl) | rreg HR' 10%bv H10'; rewrite H10'; apply bv_eq; vm_compute; reflexivity].
    eapply msteps_trans; [exact Hms|]. eapply ret_run; [vm_compute; reflexivity | exact Hra1 | exact Hret].
  -
    enum_range x 1 15%nat XR; lit_in Ha0;
    lazymatch type of Ha0 with getr _ _ = Z_to_bv 64 ?xv =>
      let fc := eval vm_compute in (kind_range EXT_KIND xv) in
      lazymatch fc with (?f, ?c) =>
        pose (E := Eseed R [Z_to_bv 64 (TablStmts.sx32 y); Z_to_bv 64 pd]);
        assert (HR : regs_ok E (srs sr_id [(10%bv, ELit xv); (11%bv, EVar 32); (12%bv, EVar 33)]) R)
          by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
        pose proof (HKimg_ext E M HRO) as HK;
        xrun HR HK 80%nat LE_STOPS (SCR [] [] []) 41%N; [split_scs; try sc_auto1|];
        rreg HR' 15%bv A15; rreg HR' 14%bv A14; rreg HR' 11%bv A11; rreg HR' 17%bv A17; rreg HR' 5%bv A5;
        rreg HR' 13%bv A13; rreg HR' 16%bv A16; rreg HR' 12%bv A12; rreg HR' 10%bv A10;
        eapply (kind_run fx R M xv y pd sp ret R' f c HRO Hy eq_refl);
        [ lia | lia | unfold NEXT; lia | vm_compute; reflexivity | exact Hce | exact Hpd8 | exact Hdef | exact Hal | exact Hra | exact Hret
        | exact Hms | exact (kept_of_syms _ _ _ _ HR' eq_refl)
        | repeat split; [rewrite A15; f_equal; reflexivity | exact A14 | exact A11 | exact A17 | rewrite A5; apply bv_eq; vm_compute; reflexivity]
        | rewrite A13; f_equal; reflexivity | rewrite A16; reflexivity | exact A12
        | rewrite A10; apply bv_eq; vm_compute; reflexivity ]
      end end.
Qed.
End Tabl_LookupExtU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_SpecU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_ImportU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_PushU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_TakeU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl.Tabl_HeaderU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DRepU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag.DiagStmtsExU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsNeeds OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsInv OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PrsStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHyps OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmHypsU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCoreU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrapU1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmWrap2U1 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmBodyU1.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RunRandom.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec SRealizes StepTac LibIface LibBudget LibEff U1Layout Lib_Cxx_OperatorNewU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ Require Import MallocIfaceStmt MallocInstU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import U1Statics.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts ContStmts2 U1Facts
  U1Lib_Vec32_PbSlow U1Lib_Vec32_PbSlow_6a1b8 U1Lib_Vec32_PbSlow_6d794 U1Lib_Vec32_PbSlow_6b2e0 U1Lib_VecOty_PushBack U1Lib_VecOpnd_PbSlow
  U1Lib_Str_PushBack U1Lib_MakeString U1Lib_Cxx_OperatorDelete.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts HStmtsU1 HConstsU1 HFindU1 HFind2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.HFindNTU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.HIndexU1. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.HIndex2U1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HEmplaceU1A HEmplaceU1 HEmplace2U1A HEmplace2U1 HRehashU1 HRehash2U1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.HRehashWU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRehashW2U1 HNextPrimeU1 HMvaU1 HMva2U1 HNtU1 HStateMvaU1A HStateMvaNTU1 HStateMvaU1 HStateDtorU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablStmts TablStmtsHdr TablRep TablData TablGrammar TablFacts TablImgU1 TablPtrFacts Tabl_SmallU1 Tabl_JumpU1 Tabl_AccessorsU1 Tabl_StrlenU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.Tabl_SplitU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import Tabl_LookupOpU1 Tabl_LookupOpndU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs.PmCLInstU1.Tabl_LookupExtU1. From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import Tabl_SpecU1 Tabl_ImportU1 Tabl_PushU1 Tabl_TakeU1 Tabl_HeaderU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRepU1 DiagStmtsExU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar PrsNeeds PrsInv PrsStmts PmHyps PmHypsU1 PmCoreU1 PmWrapU1 PmWrap2U1 PmBodyU1.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := U1Layout.
Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma ms_val {AC : AllocCeiling} {RRND : RunRandom} : MALLOC_STACK MI_U1 = 8192.
Proof. rewrite (mc_stack _ _ _ MI_U1_consts_ok). reflexivity. Qed.
Lemma ms_nonneg {AC : AllocCeiling} {RRND : RunRandom} : 0 <= MALLOC_STACK MI_U1.
Proof. rewrite ms_val. lia. Qed.
Lemma ns_nonneg {AC : AllocCeiling} {RRND : RunRandom} : 0 <= ContStmts.NEW_STACK SEGS Ly.L MI_U1.
Proof. unfold ContStmts.NEW_STACK. rewrite ms_val. lia. Qed.
Lemma ms_range {AC : AllocCeiling} {RRND : RunRandom} : 0 <= MALLOC_STACK MI_U1 <= 8192.
Proof. rewrite ms_val. lia. Qed.

Lemma round_up_pg_bounds : forall x, x <= mng_round_up_pg x < x + 4096.
Proof.
  intros x. unfold mng_round_up_pg, MNG_PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia.
  change 4096 with (2 ^ 12). pose proof (Z.mod_pos_bound (- x) (2 ^ 12) ltac:(lia)). lia.
Qed.
Lemma rb_U1 {AC : AllocCeiling} {RRND : RunRandom} : round_big_law MI_U1.
Proof.
  intros n Hn. rewrite (mc_round_big _ _ _ MI_U1_consts_ok n). unfold mng_round_big, MNG_IB, MNG_UNIT.
  pose proof (round_up_pg_bounds (n + 4 + 16)). lia.
Qed.
Lemma classes_U1 {AC : AllocCeiling} {RRND : RunRandom} : size_class MI_U1 24 <= 2 /\ (size_class MI_U1 32 <= 2 /\ size_class MI_U1 24 <> size_class MI_U1 32) /\ 4096 <= BIG MI_U1.
Proof.
  rewrite !(mc_size_class _ _ _ MI_U1_consts_ok), (mc_big _ _ _ MI_U1_consts_ok).
  vm_compute. repeat split; congruence.
Qed.

Lemma new_U1 {AC : AllocCeiling} {RRND : RunRandom} : new_rule_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1).
Proof. exact (Lib_Cxx_OperatorNewU1.operator_new_spec MI_U1 U1ST ms_nonneg). Qed.
Lemma delr_U1 {AC : AllocCeiling} {RRND : RunRandom} : delete_rule_stmt SEGS Ly.L MI_U1 (MALLOC_STACK MI_U1).
Proof. exact (U1Lib_Cxx_OperatorDelete.u1_operator_delete_spec MI_U1). Qed.
Lemma next_prime_U1 : HStmts.next_prime_stmt SEGS Ly.L HConstsU1.hc.
Proof. apply (HNextPrimeU1.next_prime_spec Ly.L); reflexivity. Qed.

Ltac inst := first [ reflexivity | exact ns_nonneg | exact ms_nonneg | exact new_U1 | exact delr_U1 | exact next_prime_U1
                   | exact ly_img_low | exact ly_rw_img | exact ly_relro_img | exact ly_rw_not_relro | exact ly_errno_rw
                   | exact (HRepFacts.nval24_agree SEGS) | assumption ].

Lemma rehash_u32_U1 {AC : AllocCeiling} {RRND : RunRandom} : rehash24_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HRehashU1.REH.
Proof. eapply (HRehashU1.rehash24_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma rehash_ext_U1 {AC : AllocCeiling} {RRND : RunRandom} : rehash24_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HRehash2U1.REH.
Proof. eapply (HRehash2U1.rehash24_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma rehashw_u32_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.rehashw_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HRehashWU1.RW.
Proof. pose proof rehash_u32_U1. eapply (HRehashWU1.rehashw_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma rehashw_ext_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.rehashw_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HRehashW2U1.RW.
Proof. pose proof rehash_ext_U1. eapply (HRehashW2U1.rehashw_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma emplace_u32_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.emplace24u_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HEmplaceU1A.EMP.
Proof. pose proof rehashw_u32_U1. eapply (HEmplaceU1.emplace24u_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma emplace_ext_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.emplace24u_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HEmplace2U1A.EMP.
Proof. pose proof rehashw_ext_U1. eapply (HEmplace2U1.emplace24u_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma index_u32_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.index24_u1_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HIndexU1.IDX.
Proof. pose proof emplace_u32_U1. eapply (HIndexU1.index24_u1_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma index_ext_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.index24_u1_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HIndex2U1.IDX.
Proof. pose proof emplace_ext_U1. eapply (HIndex2U1.index24_u1_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma nt_block_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.emplace_nt_block_u1_stmt SEGS Ly.L MI_U1 U1ST (ContStmts.NEW_STACK SEGS Ly.L MI_U1) (MALLOC_STACK MI_U1) HConstsU1.hc.
Proof. eapply (HNtU1.emplace_nt_block_u1_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma mva_u32_U1 {AC : AllocCeiling} {RRND : RunRandom} : mva_stmt SEGS Ly.L MI_U1 U1ST (MALLOC_STACK MI_U1) HStateMvaU1A.MVA1E 24 Z (nval24 SEGS).
Proof. eapply (HMva2U1.mva_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma mva_ext_U1 {AC : AllocCeiling} {RRND : RunRandom} : mva_stmt SEGS Ly.L MI_U1 U1ST (MALLOC_STACK MI_U1) HStateMvaU1A.MVA3E 24 Z (nval24 SEGS).
Proof. eapply (HMvaU1.mva_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma nt_inl_U1 {AC : AllocCeiling} {RRND : RunRandom} : nt_inl_stmt Ly.L MI_U1 (MALLOC_STACK MI_U1).
Proof. eapply (HStateMvaNTU1.nt_inl_spec Ly.L MI_U1); inst. Qed.
Lemma state_mva_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStmtsU1.state_mva_u1_stmt SEGS Ly.L MI_U1 U1ST (MALLOC_STACK MI_U1) HConstsU1.hc.
Proof. pose proof mva_u32_U1. pose proof mva_ext_U1. pose proof nt_inl_U1. eapply (HStateMvaU1.state_mva_u1_spec Ly.L MI_U1 U1ST); inst. Qed.
Lemma state_dtor'_U1 {AC : AllocCeiling} {RRND : RunRandom} : HStateDtorU1.state_dtor_u1_stmt' Ly.L MI_U1 U1ST (MALLOC_STACK MI_U1) HConstsU1.hc.
Proof. eapply (HStateDtorU1.state_dtor_u1_spec' Ly.L MI_U1 U1ST); inst. Qed.

Lemma idesc_ptr_U1 : forall d op, idesc ti d op -> 0x10000 <= d /\ d + 60 <= 2 ^ 40 /\ d mod 4 = 0.
Proof. intros d op H. exact (TablPtrFacts.U1.idesc_ptr d op H). Qed.
Lemma odesc_ptr_U1 : forall d t v, odesc ti d t v -> 0x10000 <= d /\ d + 16 <= 2 ^ 40 /\ d mod 4 = 0.
Proof. intros d t v H. destruct (TablPtrFacts.U1.odesc_ptr d t v H) as (A & B & C). lia. Qed.
Lemma edesc_ptr_U1 : forall d e v, edesc ti d e v -> 0x10000 <= d /\ d + 16 <= 2 ^ 40 /\ d mod 4 = 0.
Proof. intros d e v H. destruct (TablPtrFacts.U1.edesc_ptr d e v H) as (A & B & C). lia. Qed.

Definition spec_len_okb : bool :=
  forallb (fun op => match tg_op op with Some l => (3 <=? Zlen l) | None => true end) SPECOPS.
Lemma spec_len_okb_true : spec_len_okb = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tg_spec_len : forall op l, g_specop TG op = true -> g_op TG op = Some l -> 3 <= Zlen l.
Proof.
  intros op l Hs H. cbn [g_specop TG] in Hs. unfold tg_specop in Hs. apply existsb_exists in Hs. destruct Hs as (op' & Hin & Heq).
  apply Z.eqb_eq in Heq. subst op'.
  pose proof spec_len_okb_true as OK. unfold spec_len_okb in OK. rewrite forallb_forall in OK. specialize (OK op Hin).
  cbn [g_op TG] in H. rewrite H in OK. apply Z.leb_le. exact OK.
Qed.

Section Inst.
Context {AC : AllocCeiling}.
Context {RRND : RunRandom}.
  Hypothesis D : DiagStmtsExU1.diag_contract MI_U1 U1ST.
  Hypothesis DX : PmHypsU1.exhaustedU_stmt SEGS Ly.L MI_U1 U1ST dcU1.

  Definition CL_U1 : pm_calleesU1 SEGS Ly.L MI_U1 U1ST TG tcU1 dcU1 nfcU1 HConstsU1.hc ccU1 kcU1
                       (idesc ti) (odesc ti) (edesc ti) tg_generates_type (fun _ => false) (fun _ => false) (DRepU1.ds_rep MI_U1).
  Proof using AC RRND D DX.
    destruct D as (D0 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8).
    constructor.
    -   exact (TG_ok).
    -   exact (tg_maxlen).
    -   exact (tg_mask_len).
    -   exact (tg_spec_len).
    -   exact (eq_refl).
    -   exact (eq_refl).
    -   exact (tg_gt_rid).
    -   exact (tg_rid1).
    -   exact (tg_import).
    -   exact (tg_spec_rid).
    -   exact (rb_U1).
    -   exact (new_U1).
    -   exact (U1Lib_Cxx_OperatorDelete.u1_op_delete1_spec MI_U1).
    -   exact (ms_range).
    -   exact (classes_U1).
    -   exact (fixword_spec).
    -   exact (is_host_endian_spec).
    -   exact (generates_type_spec).
    -   exact (is_ext_inst_spec).
    -   exact (is_optional_spec).
    -   exact (is_nonsemantic_spec).
    -   exact (fpenc_spec).
    -   exact (fpenc16_spec).
    -   exact (operand_type_str_spec).
    -   exact (idesc_name_spec).
    -   exact (idesc_operands_spec).
    -   exact (odesc_operands_spec).
    -   exact (edesc_operands_spec).
    -   exact (odesc_value_spec).
    -   exact (idesc_ptr_U1).
    -   exact (odesc_ptr_U1).
    -   exact (edesc_ptr_U1).
    -   exact (strlen_ro_spec).
    -   exact (opcode_split_spec).
    -   exact (binary_endianness_spec).
    -   exact (lookup_opcode_spec).
    -   exact (lookup_operand_spec).
    -   exact (lookup_ext_spec).
    -   exact (spec_lookup_spec).
    -   exact (import_type_get_spec MI_U1).
    -
      assert (Hc1 : vc_entry (ku_oty_pbs ccU1) = PBS_ENTRY /\ 0 <= vc_stack (ku_oty_pbs ccU1)) by (split; [reflexivity | cbn [vc_stack ku_oty_pbs ccU1]; lia]).
      exact (push_types_spec MI_U1 U1ST (ku_oty_pbs ccU1) ms_nonneg Hc1 (vec32_pbslow_6d794_spec MI_U1 U1ST ms_nonneg new_U1)).
    -
      assert (Hc1 : vc_entry (ku_oty_pbs ccU1) = PBS_ENTRY /\ 0 <= vc_stack (ku_oty_pbs ccU1)) by (split; [reflexivity | cbn [vc_stack ku_oty_pbs ccU1]; lia]).
      assert (Hc2 : vc_entry u1c6b2e0 = PBS2_ENTRY /\ 0 <= vc_stack u1c6b2e0 <= vc_stack (ku_oty_pbs ccU1)) by (split; [reflexivity | cbn [vc_stack ku_oty_pbs ccU1 u1c6b2e0]; lia]).
      exact (take_first_spec MI_U1 U1ST (ku_oty_pbs ccU1) u1c6b2e0 ms_nonneg Hc1 Hc2
               (vec32_pbslow_6d794_spec MI_U1 U1ST ms_nonneg new_U1) (vec32_pbslow_6b2e0_spec MI_U1 U1ST ms_nonneg new_U1)).
    -   cbn [tc_lookup_stack tc_import_stack tc_pattern_stack tcU1]. lia.
    -   exact (header_get_spec).
    -   exact (peek_at_spec).
    -   exact (D0).
    -   exact (D1).
    -   exact (D2).
    -   exact (D3).
    -   exact (D4).
    -   exact (D5).
    -   exact (D6).
    -   exact (D7).
    -   exact (D8).
    -   exact (DX).
    -   cbn [dc_stack dcU1]. split; [lia | reflexivity].
    -   exact (HFindU1.find_spec Ly.L MI_U1 24 Z (nval24 SEGS)).
    -   exact (HFind2U1.find_spec Ly.L MI_U1 24 Z (nval24 SEGS)).
    -   exact (HFind2U1.find_spec Ly.L MI_U1 32 (Z * Z * Z)%type (nval32 SEGS)).
    -   exact (index_u32_U1).
    -   exact (index_ext_U1).
    -   exact (nt_block_U1).
    -   exact (HFindNTU1.nt_find_block_u1_spec Ly.L MI_U1).
    -   exact (vec32_pbslow_6a1b8_spec MI_U1 U1ST ms_nonneg new_U1).
    -   exact (vec32_pbslow_6a018_spec MI_U1 U1ST ms_nonneg new_U1).
    -   exact (vec32_push_backU_6a4d8_spec MI_U1 U1ST ms_nonneg new_U1).
    -   exact (vec_opnd_pbslow_6bc9c_spec MI_U1 U1ST ms_nonneg new_U1).
    -   exact (makestring_66788_spec MI_U1 U1ST ms_nonneg new_U1).
  Defined.

  Hypothesis PMH : parse_module_stmt SEGS Ly.L MI_U1 U1ST kcU1.

  Definition PO_U1 : @PmWrapU1.po_callees AC MI_U1 U1ST := {| PmWrapU1.po_mva := state_mva_U1; PmWrapU1.po_dtor := state_dtor'_U1 |}.

  Theorem binary_parse_U1_inst : binary_parse_stmt SEGS Ly.L MI_U1 U1ST kcU1.
  Proof using AC RRND D DX PMH. exact (PmWrap2U1.binary_parse_U1 CL_U1 PMH PO_U1). Qed.

End Inst.

Theorem binary_parse_U1_closed {AC : AllocCeiling} {RRND : RunRandom} :
  DiagStmtsExU1.diag_contract MI_U1 U1ST -> PmHypsU1.exhaustedU_stmt SEGS Ly.L MI_U1 U1ST dcU1 ->
  binary_parse_stmt SEGS Ly.L MI_U1 U1ST kcU1.
Proof. intros D DX. exact (binary_parse_U1_inst D DX (PmBodyU1.parse_module_U1 (CL_U1 D DX))). Qed.

