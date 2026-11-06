(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Ubsan.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.PropExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CatSim OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SeqExec OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StepTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.WalkTac OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.StoreOk OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Hoare OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.ShapeAlg OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SRealizes OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.RefMemcpyLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibIface OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibEff OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3 OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymExec3Sound OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.SymRun3.
Require OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HRep OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HLib OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HStmts OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HWord OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HUbsan OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HConstsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Module U1_code_6b1dc_6b344.

Import Stdlib.ZArith.ZArith.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images.Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_6b204 : bv 32 := 0x02069893.

Definition W_6b224 : bv 32 := 0x00165893.

Definition W_6b240 : bv 32 := 0x0046d713.

Definition W_6b25c : bv 32 := 0x00e6e863.

Definition W_6b274 : bv 32 := 0x02c5f6bb.

Definition W_6b290 : bv 32 := 0x00f03833.

Definition W_6b33c : bv 32 := 0x00008067.
Lemma F_6b33c : fetch_word Ubsan.M.loaded_segments (0x6b37c : word) = Some W_6b33c.
Proof. vm_refl. Qed.
Lemma D_6b33c : decode_any W_6b33c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End U1_code_6b1dc_6b344.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibEff
  SymExec3 SymExec3Sound SymRun3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HStmts HWord HUbsan HConstsU1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache. Import OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash.HFindU1.U1_code_6b1dc_6b344.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition FIND : Z := 0x6b21c.
Definition B_PC : Z := 0x6b2c0.
Definition LP_PC : Z := 0x6b328.
Definition LM_PC : Z := 0x6b35c.
Definition RET_PC : Z := 0x6b37c.
Definition TRAP_PC : Z := 0x6b380.
Definition STOPS : list Z := [B_PC; LP_PC; LM_PC; RET_PC].

Lemma BSEQ_bound : forall bc, In bc BSEQ -> 0 <= bc <= 26339969.
Proof.
  intros bc Hin. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin]; [lia|]). destruct Hin.
Qed.

Lemma chain_at : forall (V : Type) (M : mem) l1 (p k : Z) (v : V) l2,
  chain SEGS M (l1 ++ (p, (k, v)) :: l2) -> cell8 SEGS M p (hdaddr l2).
Proof.
  intros V M l1. induction l1 as [|[q kv] l1 IH]; intros p k v l2 H; cbn in H.
  - exact (proj1 H).
  - apply (IH p k v l2). exact (proj2 H).
Qed.

Lemma in_split_ents : forall (V : Type) (p : Z) (ents : list (Z * (Z * V))),
  In p (map fst ents) -> exists l1 k v l2, ents = l1 ++ (p, (k, v)) :: l2.
Proof.
  intros V p ents Hin. apply in_map_iff in Hin. destruct Hin as ([p' [k v]] & Hp & Hin). cbn in Hp. subst p'.
  apply in_split in Hin. destruct Hin as (l1 & l2 & ->). exists l1, k, v, l2. reflexivity.
Qed.

Definition popc : expr :=
  Eval vm_compute in
    (let '(ss, _, _) := sym_exec SEGS 100 true STOPS (SCR [false; false] [EVar 34; EVar 35] [])
                          (SS FIND sr_id [] [] 50) [] in
     sr_get (s_regs ss) 14%bv).
Definition popcw (w : word) : word := edenot (Env (fun _ => w) (fun _ => [])) popc.

Lemma popc_env : forall E, edenot E popc = popcw (ev E 34).
Proof. intros E. unfold popcw, popc. cbn [edenot ev]. reflexivity. Qed.

Ltac vm_popc :=
  match goal with |- context [bv_unsigned (popcw ?w)] =>
    let v := eval vm_compute in (bv_unsigned (popcw w)) in
    replace (bv_unsigned (popcw w)) with v by (vm_compute; reflexivity) end.

Lemma popcw_cases : forall bc, In bc BSEQ -> bc <> 0 ->
  (bc = 2 /\ bv_unsigned (popcw (Z_to_bv 64 bc)) = 1) \/ (bc <> 2 /\ 2 <= bv_unsigned (popcw (Z_to_bv 64 bc))).
Proof.
  intros bc Hin Hnz. unfold BSEQ in Hin.
  repeat (destruct Hin as [<-|Hin];
    [ first [ exfalso; lia
            | left; split; [reflexivity | vm_popc; reflexivity]
            | right; split; [lia | vm_popc; lia] ] |]).
  destruct Hin.
Qed.

Lemma remuw_val : forall k bc, 0 <= k < 2 ^ 32 -> 0 < bc < 2 ^ 31 ->
  alu64 ALU_SRL (mul_div M_MUL (Z_to_bv 64 4294967296)
                   (sext 64 (mul_div M_REMU (low32 (Z_to_bv 64 k)) (low32 (Z_to_bv 64 bc)))))
        (Z_to_bv 64 32)
  = Z_to_bv 64 (k mod bc).
Proof.
  intros k bc Hk Hbc.
  pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hm.
  assert (Hlk : low32 (Z_to_bv 64 k) = Z_to_bv 32 k).
  { apply bv_eq. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
    rewrite Z.mod_small by lia. reflexivity. }
  assert (Hlb : low32 (Z_to_bv 64 bc) = Z_to_bv 32 bc).
  { apply bv_eq. unfold low32. rewrite bv_extract_unsigned, !Z_to_bv_unsigned, bv_wrap64_mod, Z.shiftr_0_r.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite Hlk, Hlb.
  assert (Hr : mul_div M_REMU (Z_to_bv 32 k) (Z_to_bv 32 bc) = Z_to_bv 32 (k mod bc)).
  { cbn [mul_div]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.mod_small bc) by lia. destruct (Z.eqb_spec bc 0); [lia|].
    apply bv_eq. rewrite bv_modu_unsigned, !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
    rewrite (Z.mod_small k), (Z.mod_small bc), (Z.mod_small (k mod bc)) by lia. reflexivity. }
  rewrite Hr.
  assert (Hs : sext 64 (Z_to_bv 32 (k mod bc)) = Z_to_bv 64 (k mod bc)).
  { apply bv_eq. unfold sext. rewrite bv_sign_extend_unsigned, Z_to_bv_signed, !Z_to_bv_unsigned, bv_wrap64_mod.
    rewrite (bv_swrap_small 32) by (change (bv_half_modulus 32) with (2 ^ 31); lia). unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). reflexivity. }
  rewrite Hs. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_shiftr_unsigned, bv_mul_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small 4294967296), (Z.mod_small (k mod bc)), (Z.mod_small 32), (Z.mod_small 63) by lia.
  change (Z.land 32 63) with 32.
  rewrite (Z.mod_small (4294967296 * (k mod bc))) by lia.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 32) with 4294967296.
  rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
Qed.

Section FindProof.
  Context {fx : FPState}.
Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variables (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop).
  Variable rom : word -> option byte.

  Variables (A : AS MI) (M : mem) (obj bl bc keyp key : Z) (ents : list (Z * (Z * V))).
  Hypothesis U : umapx MI NS nval A M obj bl bc ents.
  Hypothesis Hkey : cell4 SEGS M keyp key.
  Hypothesis Hkp0 : 0 < keyp.
  Hypothesis Hkp1 : keyp + 4 <= 2 ^ 47.
  Hypothesis HNS : 24 <= NS.

  #[local] Abbreviation st R pc := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Let Hhdr : hdr SEGS M obj bl bc ents := u_hdr U.
  Let Hbc_in : In bc BSEQ := u_bseq U.
  Let Hkey_rng : 0 <= key < 2 ^ 32 := proj1 Hkey.

  Lemma bc_rng : 0 <= bc <= 26339969.
  Proof using AC L MI NS V nval A M obj bl bc ents U. apply BSEQ_bound. exact Hbc_in. Qed.

  Lemma node_facts : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + NS <= 2 ^ 47 /\ cell8 SEGS M (p + 8) k /\ cell4 SEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 SEGS M p (hdaddr l2).
  Proof using AC L MI NS V nval A M obj bl bc ents U.
    intros l1 p k v l2 He.
    destruct (u_node U p k v) as (_ & Hp0 & Hp1 & _ & Hh & Hk & Hkr & _).
    { rewrite He. apply in_app_iff. right. left. reflexivity. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|].
    apply (chain_at V M l1 p k v l2). rewrite <- He. exact (u_chain U).
  Qed.

  Lemma node_al : forall l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 -> p mod 16 = 0.
  Proof using AC L MI NS V nval A M obj bl bc ents U.
    intros l1 p k v l2 He. destruct (u_node U p k v) as (_ & _ & _ & Hal & _); [| exact Hal].
    rewrite He. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma hdaddr_cases : forall (l2 : list (Z * (Z * V))),
    hdaddr l2 = 0 /\ l2 = [] \/ exists p k v l2', l2 = (p, (k, v)) :: l2' /\ hdaddr l2 = p.
  Proof using V.
    intros [|[p [k v]] l2']; [left; split; reflexivity | right]. exists p, k, v, l2'. split; reflexivity.
  Qed.

  Lemma blkA0 : forall R,
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> bc = 0 ->
    exists R', msteps SEGS (st R FIND) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 0.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U.
    intros R H10 H11 Hbc0. destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    xrun HR HK 100%nat STOPS (SCR [true] [EVar 34; EVar 35] []) 50%N.
    { split_scs; sc_auto1. }
    exists R'. split; [exact Hms|]. split.
    - eapply aonly_of_syms; [exact HR'| reflexivity].
    - rreg HR' 10%bv H. exact H.
  Qed.

  Lemma blkA : forall R,
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp -> bc <> 0 ->
    exists R', msteps SEGS (st R FIND) (st R' B_PC) /\ aonly R R'
      /\ getr R' 10%bv = Z_to_bv 64 obj /\ getr R' 11%bv = Z_to_bv 64 key
      /\ getr R' 12%bv = Z_to_bv 64 bc /\ getr R' 13%bv = Z_to_bv 64 (hmod key bc)
      /\ getr R' 14%bv = popcw (Z_to_bv 64 bc).
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1.
    intros R H10 H11 Hbc. destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 keyp; Z_to_bv 64 bc; Z_to_bv 64 key]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.
    assert (Hpc : forall b : bool, branch_taken BC_LTU (edenot E (ELit 1)) (edenot E popc) = b ->
                  sc_denot SEGS M E (SCBr b BC_LTU (ELit 1) popc)).
    { intros b Hb. exact Hb. }
    destruct (popcw_cases bc Hbc_in Hbc) as [[Hbc2 Hp1] | [Hbc2 Hp2]].
    -
      xrun HR HK 100%nat STOPS (SCR [false; false] [EVar 34; EVar 35] []) 50%N.
      { split_scs; try sc_auto1.
        apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
      exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
      rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
      repeat split; try assumption.
      + rewrite H13'. rewrite w_addm, w_and by lia. subst bc. unfold hmod.
        change (2 + -1) with (Z.ones 1). rewrite Z.land_comm, Z.land_ones by lia. reflexivity.
      + lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
    - destruct (Z.ltb_spec key bc) as [Hlt|Hge].
      +
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 34; EVar 35] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
        repeat split; try assumption.
        * rewrite H13'. unfold hmod. rewrite Z.mod_small by lia. reflexivity.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
      +
        xrun HR HK 100%nat STOPS (SCR [false; true; false] [EVar 34; EVar 35] []) 50%N.
        { split_scs; try sc_auto1.
          apply Hpc. rewrite popc_env. evs. rewrite branch_ltu_lit_l by lia. bool_lia. }
        exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
        rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'.
        repeat split; try assumption.
        * rewrite H13'. unfold hmod. apply remuw_val; lia.
        * lazymatch type of HR' with regs_ok ?E' _ _ => exact (eq_trans (HR' 14%bv) (popc_env E')) end.
  Qed.

  Lemma blkB : forall R idx b q0 (w4 : word),
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 idx -> getr R 14%bv = w4 ->
    0 <= idx < bc -> bc <> 0 ->
    cell8 SEGS M (bl + 8 * idx) b -> 0 <= b -> b + 8 <= 2 ^ 47 ->
    (b <> 0 -> cell8 SEGS M b q0) -> (b <> 0 -> b mod 8 = 0) ->
    exists R', aonly R R' /\
      ( ((b = 0 \/ q0 = 0) /\ msteps SEGS (st R B_PC) (st R' RET_PC) /\ getr R' 10%bv = Z_to_bv 64 0)
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= bv_unsigned w4 /\ msteps SEGS (st R B_PC) (st R' LM_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = Z_to_bv 64 key /\ getr R' 12%bv = Z_to_bv 64 bc
          /\ getr R' 13%bv = Z_to_bv 64 idx /\ getr R' 14%bv = sxw key)
      \/ (b <> 0 /\ q0 <> 0 /\ bv_unsigned w4 < 2 /\ msteps SEGS (st R B_PC) (st R' LP_PC)
          /\ getr R' 10%bv = Z_to_bv 64 q0 /\ getr R' 11%bv = Z_to_bv 64 key /\ getr R' 12%bv = Z_to_bv 64 (bc - 1)
          /\ getr R' 13%bv = Z_to_bv 64 idx /\ getr R' 14%bv = sxw key) ).
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey.
    intros R idx b q0 w4 H10 H11 H12 H13 H14 Hidx Hbc Hb Hb0 Hb1 Hq0 Hbal.
    destruct Hhdr as [Hbl Hbc8 Hp1c Hsz Hmlf Hdef].
    pose proof bc_rng as Hbcr. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1. pose proof (u_bl_al U) as Hblal.
    pose proof (proj1 Hb) as Hbr.
    pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 idx; w4; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                        Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption. }
    assert (HK : know_ok SEGS E M []) by constructor.

    assert (Hrd_b : forall e, edenot E e = Z_to_bv 64 b ->
      sc_denot SEGS M E (SCReadBase (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) 8 false e)).
    { intros e He. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Hb); [cbn; lia| |exact He].
      evs. rewrite w_mul, w_add, v_addi_Z by lia. f_equal. lia. }
    assert (Hfl_b : sc_denot SEGS M E (SCFlat (SA (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) 0) (ELit 8))).
    { eapply (sc_flat _ _ _ _ (bl + 8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | cbn; lia | lia | cbn; lia]. }

    assert (UB1 : sc_denot SEGS M E (SCBr false BC_LTU (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) (EVar 40))).
    { eapply (sc_trap_wrap _ _ _ _ _ bl (8 * idx)); [evs; rewrite w_mul, w_add by lia; f_equal; lia | evs; reflexivity | lia | lia | lia]. }
    assert (UB2 : sc_denot SEGS M E (SCBr false BC_EQ (EAlu ALU_XOR (EAlu ALU_SLTU (ELit 0) (EVar 40))
                     (EAlu ALU_SLTU (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) (ELit 1))) (ELit 0))).
    { eapply (sc_trap_nullxor _ _ _ _ _ bl (8 * idx)); [evs; reflexivity | evs; rewrite w_mul, w_add by lia; f_equal; lia | lia | lia | lia]. }
    assert (UB3 : sc_denot SEGS M E (SCBr false BC_EQ (EVar 40) (ELit 0))).
    { eapply (sc_trap_null _ _ _ _ bl); [evs; reflexivity | lia]. }
    assert (UB4 : sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 35)) (EVar 40)) (ELit 7)) (ELit 0))).
    { eapply (sc_trap_align _ _ _ _ (8 * idx + bl)); [evs; rewrite w_mul, w_add by lia; reflexivity | lia | apply align8_add; apply align16_8; exact Hblal]. }
    assert (UB5 : b <> 0 -> sc_denot SEGS M E (SCBr false BC_NE (EAlu ALU_AND (EVar 41) (ELit 7)) (ELit 0))).
    { intros Hbnz. eapply (sc_trap_align _ _ _ _ b); [evs; reflexivity | lia | exact (Hbal Hbnz)]. }
    Ltac scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b :=
      split_scs; try sc_auto1; first [exact UB1 | exact UB2 | exact UB3 | exact UB4 | apply UB5; assumption | exact Hfl_b | apply Hrd_b; evs; reflexivity
                                      | cbn [sc_denot]; evs; rewrite branch_geu_lit_r by lia; bool_lia ].
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    -
      xrun HR HK 100%nat STOPS (SCR [false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
      { scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b. }
      exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. left.
      split; [left; exact Hbz|]. split; [exact Hms|]. rreg HR' 10%bv H. rewrite H, Hbz. reflexivity.
    - specialize (Hq0 Hbnz). pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + xrun HR HK 100%nat STOPS (SCR [false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
        { scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b. }
        exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. left.
        split; [right; exact Hqz|]. split; [exact Hms|]. rreg HR' 10%bv H. rewrite H, Hqz. reflexivity.
      + destruct (Z.le_gt_cases 2 (bv_unsigned w4)) as [Hw|Hw].
        *
          xrun HR HK 100%nat STOPS (SCR [false; false; false; false; false; false; false; true] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b. }
          exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. right; left.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
          repeat split; try assumption. rewrite H14'. apply sextw_val. lia.
        *
          xrun HR HK 100%nat STOPS (SCR [false; false; false; false; false; false; false; false] [EVar 40; EVar 41; EVar 42] []) 50%N.
          { scB UB1 UB2 UB3 UB4 UB5 Hfl_b Hrd_b. }
          exists R'. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|]. right; right.
          rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
          repeat split; try assumption.
          -- rewrite H12'. apply w_addm; lia.
          -- rewrite H14'. apply sextw_val. lia.
  Qed.

  Definition found (r : Z) : Prop := r = 0 \/ exists v, In (r, (key, v)) ents.

  Ltac seedL R vals :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32); (11%bv, EVar 33); (12%bv, EVar 34); (13%bv, EVar 35); (14%bv, EVar 36)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|];
          repeat constructor; cbn [fst snd]; try (intros X; discriminate X); evs; assumption);
    assert (HK : know_ok SEGS E M []) by constructor.

  Ltac fin_ret HR' Hms r :=
    lazymatch type of HR' with regs_ok _ _ ?R1 =>
      exists R1, r; split; [exact Hms|]; split; [eapply aonly_of_syms; [exact HR'| reflexivity]|];
      split; [let H := fresh in rreg HR' 10%bv H; first [exact H | rewrite H; reflexivity] |]
    end.

  Lemma loopM : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 bc ->
    getr R 13%bv = Z_to_bv 64 (key mod bc) -> getr R 14%bv = sxw key -> bc <> 0 ->
    exists R' r, msteps SEGS (st R LM_PC) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ found r.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey HNS.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He H10 H11 H12 H13 H14 Hbc;
      pose proof bc_rng as Hbcr;
      destruct (node_facts l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (node_al l1 p k v _ He) as Hpal;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk.
    -
      destruct (Z.eq_dec k key) as [->|Hne].
      +
        seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; false; true; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; false; true; true] [EVar 40; EVar 41] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
    -
      assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        *
          seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          assert (STEP : exists R1, msteps SEGS (st R LM_PC) (st R1 LM_PC) /\ aonly R R1
                    /\ getr R1 10%bv = Z_to_bv 64 p' /\ getr R1 11%bv = Z_to_bv 64 key /\ getr R1 12%bv = Z_to_bv 64 bc
                    /\ getr R1 13%bv = Z_to_bv 64 (key mod bc) /\ getr R1 14%bv = sxw key).
          { destruct (Z.ltb_spec k bc).
            -- rewrite (Z.mod_small k bc) in Hc by lia.
               xrun HR HK 100%nat STOPS (SCR [false; false; true; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). }
               exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
               repeat split; assumption.
            -- xrun HR HK 100%nat STOPS (SCR [false; false; false; true; false] [EVar 40; EVar 41] []) 50%N.
               { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
               exists R'. split; [exact Hms|]. split; [eapply aonly_of_syms; [exact HR'| reflexivity]|].
               rreg HR' 10%bv H10'. rreg HR' 11%bv H11'. rreg HR' 12%bv H12'. rreg HR' 13%bv H13'. rreg HR' 14%bv H14'.
               repeat split; assumption. }
          destruct STEP as (R1 & Hms1 & Ha1 & G10 & G11 & G12 & G13 & G14).
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R1 He' G10 G11 G12 G13 G14 Hbc) as (R' & r & Hms2 & Ha2 & Hr & Hf).
          exists R', r. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
          split; [eapply aonly_trans; eassumption|]. split; assumption.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          destruct (Z.ltb_spec k bc).
          -- rewrite (Z.mod_small k bc) in Hc by lia.
             xrun HR HK 100%nat STOPS (SCR [false; false; true; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). }
             fin_ret HR' Hms 0. left; reflexivity.
          -- xrun HR HK 100%nat STOPS (SCR [false; false; false; false] [EVar 40] []) 50%N.
             { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite w_remu, br_eq by lia. bool_lia. }
             fin_ret HR' Hms 0. left; reflexivity.
  Qed.

  Lemma land_1 : forall k, Z.land k 1 = k mod 2.
  Proof using. intros k. pose proof (Z.land_ones k 1 ltac:(lia)) as H. exact H. Qed.

  Lemma loopP : forall l2 l1 p k v R,
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 key -> getr R 12%bv = Z_to_bv 64 (bc - 1) ->
    getr R 13%bv = Z_to_bv 64 (key mod bc) -> getr R 14%bv = sxw key ->
    exists R' r, msteps SEGS (st R LP_PC) (st R' RET_PC) /\ aonly R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ found r.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey HNS.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R He Hbc2 H10 H11 H12 H13 H14;
      destruct (node_facts l1 p k v _ He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx); cbn [hdaddr] in Hnx;
      pose proof (node_al l1 p k v _ He) as Hpal;
      pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hmk;
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk';
      pose proof (Z.mod_pos_bound key 2 ltac:(lia)) as Hmk2;
      pose proof (Z.mod_pos_bound k 2 ltac:(lia)) as Hmk2';
      pose proof (land_1 k) as Hl1;
      unfold cell8 in Hh, Hnx; unfold cell4 in Hk.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 0].
          xrun HR HK 100%nat STOPS (SCR [false; false; true; true] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_facts _ p' k' v' _ He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                 Z_to_bv 64 key; sxw key].
        xrun HR HK 100%nat STOPS (SCR [false; true; true] [EVar 40; EVar 41] []) 50%N.
        { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). sc_rd_sx Hk. }
        fin_ret HR' Hms p. right. exists v. rewrite He. apply in_app_iff. right. left. reflexivity.
      + destruct (Z.eq_dec (k mod bc) (key mod bc)) as [Hc|Hc].
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k; Z_to_bv 64 p'].
          xrun HR HK 100%nat STOPS (SCR [false; false; true; false] [EVar 40; EVar 41] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 14%bv G14.
          pose proof (aonly_of_syms _ _ _ _ HR' eq_refl) as Ha1.
          destruct (IH (l1 ++ [(p, (k, v))]) p' k' v' R' He' Hbc2 G10 G11 G12 G13 G14) as (R'' & r & Hms2 & Ha2 & Hr & Hf).
          exists R'', r. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
          split; [eapply aonly_trans; eassumption|]. split; assumption.
        * seedL R [Z_to_bv 64 p; Z_to_bv 64 key; Z_to_bv 64 (bc - 1); Z_to_bv 64 (key mod bc); sxw key; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0;
                   Z_to_bv 64 k].
          xrun HR HK 100%nat STOPS (SCR [false; false; false] [EVar 40] []) 50%N.
          { split_scs; try sc_auto1; try (eapply (sc_trap_align _ _ _ _ p); [evs; reflexivity | lia | apply align16_8; exact Hpal]). cbn [sc_denot]. evs. rewrite Hbc2. change (2 - 1) with 1. rewrite w_and, land_1, br_eq by lia. rewrite Hbc2 in Hc. bool_lia. }
          fin_ret HR' Hms 0. left; reflexivity.
  Qed.

  Lemma ret_step : forall R1 (ret : word),
    getr R1 1%bv = ret -> ret_ok ret ->
    msteps SEGS (st R1 RET_PC) (@mkst fx R1 ret M rom).
  Proof using fx rom M.
    intros R1 ret Hra Hret. unfold RET_PC. norm_pc.
    stepjr F_6b33c D_6b33c ret ltac:(exact Hra).
    change (bv_signed (0%bv : bv 12)) with 0%Z. unfold ret_ok in Hret. rewrite Hret. apply mst_refl.
  Qed.

  Theorem find_correct : forall R (ret : word),
    getr R 10%bv = Z_to_bv 64 obj -> getr R 11%bv = Z_to_bv 64 keyp ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' (p : Z),
      msteps SEGS (st R FIND) (@mkst fx R' ret M rom)
      /\ keeps_cs R R' /\ getr R' 10%bv = Z_to_bv 64 p /\ found p.
  Proof using fx AC L MI NS V nval rom A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1 HNS.
    intros R ret H10 H11 Hra Hret.
    pose proof bc_rng as Hbcr. pose proof (u_obj_hi U) as Ho1. pose proof (u_obj_lo U) as Ho0.
    destruct (Z.eq_dec bc 0) as [Hbc0|Hbc].
    { destruct (blkA0 R H10 H11 Hbc0) as (R1 & Hms1 & Ha1 & G10).
      exists R1, 0. split; [eapply msteps_trans; [exact Hms1 | apply ret_step; [|exact Hret]]|].
      { rewrite (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; exact Ha1|]. split; [exact G10 | left; reflexivity]. }
    destruct (blkA R H10 H11 Hbc) as (R1 & Hms1 & Ha1 & G10 & G11 & G12 & G13 & G14).
    pose proof (Z.mod_pos_bound key bc ltac:(lia)) as Hidx.
    destruct (u_bkt U (hmod key bc) ltac:(unfold hmod; lia)) as (b & Hb & Hbok).

    assert (Hq : exists q0 pre l,
              0 <= b /\ b + 8 <= 2 ^ 47 /\ (b <> 0 -> cell8 SEGS M b q0)
              /\ (b <> 0 -> q0 = hdaddr l /\ ents = pre ++ l) /\ (b <> 0 -> b mod 8 = 0)).
    { destruct Hbok as [Hb0 | [Hbn | (Hbs & Hne & _)]].
      - exists 0, [], ents. subst b. split; [lia|]. split; [lia|]. split; [|split]; intros HH; exfalso; exact (HH eq_refl).
      - destruct (in_split_ents V b ents Hbn) as (l1 & k & v & l2 & He).
        destruct (node_facts l1 b k v l2 He) as (Hp0 & Hp1 & _ & _ & _ & Hnx).
        exists (hdaddr l2), (l1 ++ [(b, (k, v))]), l2. split; [lia|]. split; [lia|]. split; [intros _; exact Hnx|].
        split; [| intros _; apply align16_8; exact (node_al l1 b k v l2 He)].
        intros _. split; [reflexivity|]. rewrite He, <- app_assoc. reflexivity.
      - exists (hdaddr ents), [], ents. subst b. split; [lia|]. split; [lia|].
        split; [intros _; exact (h_p1 (u_hdr U))|]. split; [intros _; split; reflexivity|].
        intros _. pose proof (u_obj_al U) as Hoal. rewrite Z.add_comm. replace 16 with (8 * 2) by reflexivity. apply align8_add. exact Hoal. }
    destruct Hq as (q0 & pre & l & Hb0 & Hb1 & Hbq & Hql & Hbal).
    destruct (blkB R1 (hmod key bc) b q0 (popcw (Z_to_bv 64 bc)) G10 G11 G12 G13 G14 ltac:(unfold hmod; lia) Hbc Hb Hb0 Hb1 Hbq Hbal)
      as (R2 & Ha2 & [ (Hz & Hms2 & F10) | [ (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F12 & F13 & F14)
                                          | (Hbn & Hqn & Hw & Hms2 & F10 & F11 & F12 & F13 & F14) ] ]).
    -
      exists R2, 0. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. apply ret_step; [|exact Hret].
        rewrite (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; eassumption|]. split; [exact F10 | left; reflexivity].
    -
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopM l2 pre p k v R2 He F10 F11 F12 ltac:(exact F13) F14 Hbc) as (R3 & r & Hms3 & Ha3 & Hr & Hf).
      exists R3, r. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        apply ret_step; [|exact Hret]. rewrite (Ha3 1%bv), (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; [eapply aonly_trans|]; eassumption|]. split; assumption.
    -
      assert (Hbc2 : bc = 2).
      { destruct (popcw_cases bc Hbc_in Hbc) as [[E _]|[_ Hge]]; [exact E | exfalso; lia]. }
      destruct (Hql Hbn) as [Hq0 He]. destruct (hdaddr_cases l) as [[Hl0 _] | (p & k & v & l2 & Hl & Hlp)]; [exfalso; lia|].
      subst l. cbn [hdaddr] in Hq0. subst q0.
      destruct (loopP l2 pre p k v R2 He Hbc2 F10 F11 F12 ltac:(exact F13) F14) as (R3 & r & Hms3 & Ha3 & Hr & Hf).
      exists R3, r. split.
      { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. eapply msteps_trans; [exact Hms3|].
        apply ret_step; [|exact Hret]. rewrite (Ha3 1%bv), (Ha2 1%bv), (Ha1 1%bv) by (first [solve [clear; cbn; tauto] | cbn; tauto]). exact Hra. }
      split; [apply aonly_kept; eapply aonly_trans; [eapply aonly_trans|]; eassumption|]. split; assumption.
  Qed.

End FindProof.

Theorem find_spec {AC : AllocCeiling} : forall (L : Layout) (MI : MallocIface SEGS L) (NS : Z) (V : Type) (nval : mem -> Z -> V -> Prop),
  find_stmt SEGS L MI FIND NS V nval.
Proof.
  intros L MI NS V nval fx A R M obj bl bc keyp key ents ret U HNS Hkey Hkp0 Hkp1 H10 H11 Hra Hret.
  exact (find_correct L MI NS V nval (seg_rom SEGS) A M obj bl bc keyp key ents U Hkey Hkp0 Hkp1 HNS R ret H10 H11 Hra Hret).
Qed.
