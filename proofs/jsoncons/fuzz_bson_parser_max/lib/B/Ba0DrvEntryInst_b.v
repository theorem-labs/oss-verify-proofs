(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import AsanAcct.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DefsK_b Ba0PlanImagesK_b.
  From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HandoffBridgeK HandoffBInvK. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0HandoffK_b Ba0HSK_0_b Ba0HSK_1_b Ba0MainTableK_b Ba0HandoffInstK_b Ba0DrvEntryK_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA HeapIfaceABx As0DrvKitA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0DrvEntry_b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma drv_chk_0 : drv_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma drv_chk_1 : drv_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma drv_chk_HSA : forall h, (h < 2)%nat -> drv_chk (HSA h) = true.
Proof. intros h Hh. destruct h as [|[|h]]; [exact drv_chk_0 | exact drv_chk_1 | lia]. Qed.
Lemma stk_chk_0 : stk_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma stk_chk_1 : stk_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma stk_chk_HSA : forall h, (h < 2)%nat -> stk_chk (HSA h) = true.
Proof. intros h Hh. destruct h as [|[|h]]; [exact stk_chk_0 | exact stk_chk_1 | lia]. Qed.

Lemma lib_chk_0 : lib_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma lib_chk_1 : lib_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma lib_chk_HSA : forall h, (h < 2)%nat -> lib_chk (HSA h) = true.
Proof. intros h Hh. destruct h as [|[|h]]; [exact lib_chk_0 | exact lib_chk_1 | lia]. Qed.

(* [comment removed for export] *)
Lemma xc_chk_0 : xc_chk HS_0 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma xc_chk_1 : xc_chk HS_1 = true.   Proof. vm_compute. reflexivity. Qed.
Lemma xc_chk_HSA : forall h, (h < 2)%nat -> xc_chk (HSA h) = true.
Proof. intros h Hh. destruct h as [|[|h]]; [exact xc_chk_0 | exact xc_chk_1 | lia]. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variables a0s path : list byte.
  Variable envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  #[local] Notation argv := [a0s; path].
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 argv envp uid hw).
  #[local] Notation argH := (argH0 APH0 sp rdraw argv envp uid hw).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461330432 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665200128 + BUDGET) + (21 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Theorem as0_main_entry : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    let A0 := as0_A0 EXTRA (HSA h) E in
    let MV := mrestrict (ahid A0 model) FULL in
    exists can tid : word,
      let ES := env_mainA sp (Z_to_bv 64 (usp + 8 * envc + 200)) (Z_to_bv 64 (usp + 8 * envc + L0 + 201)) can tid R in
      SX2S.regs_ok ES sr_mainA R
      /\ SX2S.know_ok ASEGS ES MV kn_mainA
      /\ lzinv ASEGS (ahid A0 model) A0 model
      /\ m_fds model = APSK.fds_std /\ m_fs model = fs
      /\ (forall k, (k < 2)%nat ->
            rdn ASEGS MV (cat_argv_ptr sp argv envp k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
            /\ bv_unsigned (cat_argv_ptr sp argv envp k) = usp + 8 * envc + 200 + Z.of_nat (total_arg_bytes_nat (firstn k argv))
            /\ bv_unsigned (cat_argv_ptr sp argv envp k) + Z.of_nat (length (nth k argv [])) + 1 + 16 <= 2 ^ 47).
  Proof.
    intros h Hh E R FULL model HC A0 MV.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (lib_chk_HSA h Hh) as CL. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x693d40) 8 = Some (word_to_le_bytes 8 can)
                                   /\ rdn ASEGS MV (Z_to_bv 64 0x673cf0) 8 = Some (word_to_le_bytes 8 can)).
    { edestruct (ent_guard sp brk0 rdraw argv envp uid hw fs) as (can & G1 & G2); [ .. | exists can; exact (conj G1 G2)]; eassumption. }
    destruct G as (can & G1 & G2). exists can.
    assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303
                 /\ rdn ASEGS MV (Z_to_bv 64 0x673c38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x673c38))
                 /\ rdn ASEGS MV (Z_to_bv 64 0x673c58) 4 = Some (word_to_le_bytes 4 tid)
                 /\ rdn ASEGS MV (Z_to_bv 64 0x673cd0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x693fc8))
                 /\ rdn ASEGS MV (Z_to_bv 64 0x693f98) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * envc + 40)))).
    { eapply (ent_libcells sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity. }
    destruct T as (tid & TR & T1 & T2 & T3 & T4). exists tid. cbv zeta.
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
    { destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
    assert (HB : 0 <= envc <= 256 /\ 0 <= L0 <= 131071).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply (main_regs_okA sp envc L0 R).
      eapply (ent_regs sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
    - apply (main_know_okA sp envc L0 R MV SR HB).
      + eapply (ent_stack_words sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
      + eapply (ent_window sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact G1.
      + eapply (ent_img sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact TR.
      + exact (conj T1 (conj T2 (conj G2 (conj T3 T4)))).
      + change XC9_CELLS with XC9K. eapply (ent_xcells sp brk0 rdraw argv envp uid hw fs); try eassumption; first [reflexivity | exact (xc_chk_HSA h Hh)].
    - unfold lzinv. eapply (ent_lz sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - intros k Hk. refine ((fun X Y => conj (proj1 X) (conj (proj2 X) Y)) _ _).
      + eapply (ent_str sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
      + eapply (ent_str_hi sp rdraw argv envp uid hw); try eassumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem as0_main_auxv : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    exists uidz rnd hwz : Z,
      (forall j, (j < 20)%nat ->
         rdn ASEGS FULL (Z_to_bv 64 (usp + 8 * envc + 40 + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (nth j (auxv_list uidz rnd hwz) 0))))
      /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
  Proof.
    intros h Hh E R FULL model HC.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (lib_chk_HSA h Hh) as CL. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    eapply (ent_auxv sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Theorem as0_main_stack_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    forall top, top mod 4096 = 0 -> top <= usp + 4096 -> defined FULL usp (top - usp).
  Proof.
    intros h Hh E R FULL model HC top Hm Hle i Hi.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    eapply (ent_stack_defined_top sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Theorem as0_main_str_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
    forall k, (k < 2)%nat -> forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 16 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp argv envp k) + i)) <> None.
  Proof.
    intros h Hh E R FULL model HC k Hk i Hi.
    pose proof (as0_chk_HSA h Hh) as C0. pose proof (drv_chk_HSA h Hh) as CD. pose proof (stk_chk_HSA h Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP h Hh) as GP.
    eapply (ent_str_defined sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
  Qed.
End Inst.
End FPX_1.
