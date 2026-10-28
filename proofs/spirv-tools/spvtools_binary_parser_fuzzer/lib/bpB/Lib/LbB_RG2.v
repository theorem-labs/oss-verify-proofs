(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsStack0.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition GTE_ENTRY : Z := 0x100a30.
Definition GTE_RET : Z := 0x100a98.
Definition RG_ENV : Z := 6.

Definition rg_words : list Z := ContStmts.mt_init ++ [0].
Definition rg_cells : list cell := map (fun z => C8 (wz z)) rg_words.

Definition X1 : Z := 13057201162865595358.
Definition X156 : Z := 2619718836853156863.

Definition SR0 : list expr := srs sr_id [(10%bv, EVar 32); (2%bv, EVar 33); (1%bv, EVar 34)].

Definition KN0 : list kentry :=
  [ KWord (SA (ELit 0) AGOT_SHBASE) 8 (ELit ASHBASE_CELL);
    KWord (SA (ELit 0) ASHBASE_CELL) 8 (ELit 0x7fff8000);
    KImg 0x10000 0x91000;
    KWord (SA (EVar 32) 0) 8 (ELit 5489);
    KWord (SA (EVar 32) 8) 8 (ELit X1);
    KWord (SA (EVar 32) 1248) 8 (ELit X156);
    KWord (SA (EVar 32) 2496) 8 (ELit 0);
    KWr (SA (EVar 32) 0) (ELit 2504);
    KWr (SA (EVar 33) (-176)) (ELit 176);
    KRange (EVar 33) (2 ^ 45) (2 ^ 47);
    KRange (EVar 32) 0x6e8000 (2 ^ 47);
    KDisj (SA (EVar 32) 0) (ELit 2504) (SA (EVar 33) (-176)) (ELit 176) ].

Definition SCR0 : scripts := SCR [] [] [].
Definition KN1 : list kentry := kn_fix 20 [GTE_RET] SCR0 GTE_ENTRY SR0 KN0 40.

Definition gte_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (obj lo : Z) (m ro : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 RG_ENV) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' ro
    /\ munch [(obj, obj + 2504); (bv_unsigned sp - 176, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Section GTE.
  Context {HCEIL : HeapCeil}.

  Lemma gte_evt : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) (fc : bv 32) (m ro : word -> option byte) (obj lo shi : Z),
    rw_cells asegs m obj rg_cells -> SHAD m obj (repeat (b8 0) 313) ->
    0 < obj -> obj mod 8 = 0 -> obj + 2504 <= 2 ^ 47 ->
    (obj + 2504 <= bv_unsigned sp - 176 \/ bv_unsigned sp <= obj) ->
    stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 176 ->
    stack0 m lo shi -> bv_unsigned sp <= shi -> 2 ^ 45 <= lo -> bv_unsigned sp <= 2 ^ 47 -> bv_unsigned sp mod 16 = 0 ->
    ((0x6e8000 <= obj /\ obj + 2504 <= 0x7fff7000) \/ (0x10007fff8000 <= obj /\ obj + 2504 <= 2 ^ 47)) -> ACONST m -> mem_inv asegs m ->
    evt asegs (gte_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc obj lo m ro)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 GTE_ENTRY) fc None m ro).
Proof.
  intros until shi. intros RC SH0 O0 O8 O47 OB ST LO S0 SPS L45 SP47 SP16 BAND AC MI.
  pose proof (ACONST_shbase m AC) as [CG CS].
  assert (HSP : sp = Z_to_bv 64 (bv_unsigned sp)) by (symmetry; apply Z_to_bv_bv_unsigned).
  remember (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 obj) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
  pose (E := Eseed R [Z_to_bv 64 obj; Z_to_bv 64 (bv_unsigned sp); ra]).
  assert (E32 : bv_unsigned (edenot E (EVar 32)) = obj) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (E33 : bv_unsigned (edenot E (EVar 33)) = bv_unsigned sp) by (evs; rewrite u64_of_Z by lia; reflexivity).
  assert (HR : regs_ok E SR0 R).
  { unfold SR0. apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X);
      subst R; evs; first [reflexivity | exact HSP]. }
  assert (HK : know_ok asegs E m (KN0 ++
     [ KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-44))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-48))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-152))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-144))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-128))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-136))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-112))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-120))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-104))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-96))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit (-88))) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EVar 32) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 8)) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 1248)) (ELit 3)) SHBASE) 1 (ELit 0);
     KWord (SA (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 2496)) (ELit 3)) SHBASE) 1 (ELit 0);
     KAlign (EVar 32) 8 ])).
  { unfold KN0, know_ok. cbn [app].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CG | reflexivity | reflexivity | lia
                        | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL; lia | reflexivity]|].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m _ _ 0%nat _); [exact CS | reflexivity | reflexivity | lia
                        | reflexivity | cbn; unfold AGOT_SHBASE, ASHBASE_CELL; lia | cbn; unfold AGOT_SHBASE, ASHBASE_CELL; lia | reflexivity]|].
    apply Forall_cons; [apply kimg_of_mem_inv; [exact MI | lia | lia]|].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m obj rg_cells 0%nat (C8 (wz 5489))); [exact RC | vm_cast_no_check (@eq_refl (option cell) (Some (C8 (wz 5489)))) | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite E32; cbn; lia | cbn; lia | cbn; lia | reflexivity]|].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m obj rg_cells 8%nat (C8 (wz X1))); [exact RC | vm_cast_no_check (@eq_refl (option cell) (Some (C8 (wz X1)))) | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite E32; cbn; lia | cbn; lia | cbn; lia | reflexivity]|].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m obj rg_cells 1248%nat (C8 (wz X156))); [exact RC | vm_cast_no_check (@eq_refl (option cell) (Some (C8 (wz X156)))) | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite E32; cbn; lia | cbn; lia | cbn; lia | reflexivity]|].
    apply Forall_cons; [eapply (kword_of_rw_cells asegs E m obj rg_cells 2496%nat (C8 (wz 0))); [exact RC | vm_cast_no_check (@eq_refl (option cell) (Some (C8 (wz 0)))) | reflexivity | lia | unfold estart; cbn [a_base a_off]; rewrite E32; cbn; lia | cbn; lia | cbn; lia | reflexivity]|].
    apply Forall_cons.
    { assert (WRO : wr_at asegs m obj 2504) by (pose proof (proj2 RC) as W; replace (Z.of_nat (cells_size rg_cells)) with 2504 in W by (vm_compute; reflexivity); exact W).
      eapply kwr_of_wr_at; [exact WRO
        | unfold estart; cbn [a_base a_off]; rewrite E32; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E32; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons.
    { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite E33; lia
        | unfold estart, elenZ; cbn [a_base a_off]; rewrite E33; evs; rewrite u64_of_Z by lia; lia
        | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]. }
    apply Forall_cons; [cbn [kentry_ok]; rewrite E33; lia|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite E32; lia|].
    apply Forall_cons; [cbn [kentry_ok]; unfold estart, elenZ; cbn [a_base a_off]; rewrite E32, E33; evs;
                        rewrite !u64_of_Z by lia; lia|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 44));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 48));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 152));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 144));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 128));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 136));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 112));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 120));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 104));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 96));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (bv_unsigned sp - 88));
      [evs; rewrite w_addm by lia; f_equal; lia | lia | eapply sh0_of_stack0; [exact S0 | lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ obj);
      [evs; reflexivity | lia | eapply sh0_of_SHAD0; [exact SH0 | cbn; lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (obj + 8));
      [evs; rewrite w_add by lia; reflexivity | lia | eapply sh0_of_SHAD0; [exact SH0 | cbn; lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (obj + 1248));
      [evs; rewrite w_add by lia; reflexivity | lia | eapply sh0_of_SHAD0; [exact SH0 | cbn; lia]]|].
    apply Forall_cons; [eapply (kshadow0 E m _ (obj + 2496));
      [evs; rewrite w_add by lia; reflexivity | lia | eapply sh0_of_SHAD0; [exact SH0 | cbn; lia]]|].
    apply Forall_cons; [cbn [kentry_ok]; rewrite E32; lia|].
    apply Forall_nil. }
  xrun_at (PropExec.mkFP F fc) asegs R GTE_ENTRY m ro HR HK 400%nat [GTE_RET] (SCR [] [] []) 40%N.
  { split_scs; sc_shdj. }
  clear HK.
  lazymatch type of Hlf with log_flat _ ?lg =>
    lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
      change mm with (mem_denot E m lg) in Hms; set (M := mem_denot E m lg) in Hms end end.
  assert (MU : munch [(obj, obj + 2504); (bv_unsigned sp - 176, bv_unsigned sp)] m M).
  { pose proof (munch_mem_denot_2b [(0, 2504)] [(-176, 0)] (EVar 32) (EVar 33) E m _ Hlf
                  ltac:(vm_cast_no_check (@eq_refl bool true))) as MU.
    rewrite E32, E33 in MU. cbn [map fst snd app] in MU. subst M. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
  assert (WM : wmono asegs m M) by (subst M; apply wmono_mem_denot).
  assert (MI1 : mem_inv asegs M) by exact (msteps_mem_inv asegs _ _ Hms MI).
  assert (ST1 : stk asegs M lo (bv_unsigned sp)) by (subst M; apply stk_mem_denot; exact ST).
  clearbody M.
  assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
  pose proof (msteps_full asegs _ _ Hms HF) as HF1. cbn [ms_regs] in HF1.
  readback HR' HF1 HR0 HRe.
  rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 10%bv L10.
  rewrite <- HSP in L2.
  rewrite L1, L2, L10 in HRe.
  eapply evt_of_msteps; [exact Hms|].
  change (PropExec.mkst R' (Z_to_bv 64 1051288) M ro) with (MS R' F (Z_to_bv 64 1051288) fc None M ro).
  rewrite HRe. step. apply evt_done.
  exists (getr R' 5), (getr R' 6), (getr R' 7), (getr R' 11), (getr R' 12), (getr R' 13), (getr R' 14), (getr R' 15),
    (getr R' 16), (getr R' 17), (getr R' 28), t4, t5, t6, M.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1 | exact ST1].
Qed.
End GTE.
