(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the SIGPIPE disposition as a launch variable; the new launch (process input, auxv, group id, exec file name); the CONFIG_RSEQ flag; the string read-ahead slack of 9; start-up certificates and hand-off states computed in the build; addresses and numbers; new lemmas; unused lemmas removed; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/As0DrvEntryInst.v, 75 lines within its lines 11-200. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Ea0DefsK Ea0PlanImagesK
  HandoffBridgeK HandoffBInvK Ea0HandoffK Ea0CertK_202 Ea0HandoffInstK Ea0DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA HeapIfaceAEx As0DrvKitA Ea0DrvEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma drv_chk_HSA : forall r h, 0 <= r <= 1 -> (h < 2)%nat -> drv_chk r (HSA r h) = true.
Proof. intros r h Hr Hh. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct h as [|[|h]]; try lia; vm_compute; reflexivity. Qed.
Lemma stk_chk_HSA : forall r h, 0 <= r <= 1 -> (h < 2)%nat -> stk_chk r (HSA r h) = true.
Proof. intros r h Hr Hh. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct h as [|[|h]]; try lia; vm_compute; reflexivity. Qed.

Lemma lib_chk_HSA : forall r h, 0 <= r <= 1 -> (h < 2)%nat -> lib_chk r (HSA r h) = true.
Proof. intros r h Hr Hh. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct h as [|[|h]]; try lia; vm_compute; reflexivity. Qed.
Lemma aux_chk_HSA : forall r h, 0 <= r <= 1 -> (h < 2)%nat -> aux_chk r (HSA r h) = true.
Proof. intros r h Hr Hh. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct h as [|[|h]]; try lia; vm_compute; reflexivity. Qed.

Lemma xc_chk_HSA : forall r h, 0 <= r <= 1 -> (h < 2)%nat -> xc_chk (HSA r h) = true.
Proof. intros r h Hr Hh. assert (r = 0 \/ r = 1) as [-> | ->] by lia; destruct h as [|[|h]]; try lia; vm_compute; reflexivity. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section Inst.
  Variable sp brk0 : word.
  Variable rdraw : EntryDraw.
  Variables a0s path : list byte.
  Variable envp : list (list byte).
  Variables uid hw : word.
  Variable fs : Fs.Fs.
  Variable mbase : word.
  Variable stdin : InputStream.
  Variable gid : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Variable abrt : bool.
  Variable ur : InputStream.
  Variable kb : KernelBuild.
  Variable execfn : list byte.
  Variable sdf : bool.
  Variable apc : N.
  Variable r : Z.
  #[local] Notation argv := [a0s; path].
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
    (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis Hvl : valid_launch (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  Hypothesis HRZ : r = APK.rseq_z (kb_rseq (in_kernel (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf))).
  Remark r01 : 0 <= r <= 1.
  Proof. rewrite HRZ. apply APK.rseq_z_range. Qed.
  #[local] Notation INP := (AsanInitK.inp argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation top := (ed_top rdraw).
  #[local] Notation STR0 := (bv_unsigned sp + Z.of_nat (cat_string_off (kb_rseq (in_kernel INP)) sp top argv envp execfn)).
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt ur kb execfn sdf).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461339648 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665290240 + BUDGET) + (23 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation envc := (Z.of_nat (length envp)).
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Theorem as0_main_entry : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    let A0 := as0_A0 EXTRA (HSA r h) E in
    let MV := mrestrict (ahid A0 model) FULL in
    exists can tid : word,
      let ES := env_mainA sp (Z_to_bv 64 STR0) (Z_to_bv 64 (STR0 + L0 + 1)) can tid (Z_to_bv 64 (usp + 8 * envc + 40)) R in
      SX2S.regs_ok ES sr_mainA R
      /\ SX2S.know_ok ASEGS ES MV kn_mainA
      /\ lzinv ASEGS (ahid A0 model) A0 model
      /\ m_fds model = APSK.fds_std /\ m_fs model = fs
      /\ (forall k, (k < 2)%nat ->
            rdn ASEGS MV (cat_argv_ptr top argv envp execfn k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
            /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) = STR0 + Z.of_nat (total_arg_bytes_nat (firstn k argv))
            /\ bv_unsigned (cat_argv_ptr top argv envp execfn k) + Z.of_nat (length (nth k argv [])) + 1 + 9 <= 2 ^ 47).
  Proof using All.
    intros h Hh E R FULL model HC A0 MV.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (lib_chk_HSA r h r01 Hh) as CL. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x695ac0) 8 = Some (word_to_le_bytes 8 can)
                                   /\ rdn ASEGS MV (Z_to_bv 64 0x675a70) 8 = Some (word_to_le_bytes 8 can)).
    { edestruct (ent_guard sp brk0 rdraw argv envp uid hw fs) as (can & G1 & G2); [ .. | exists can; exact (conj G1 G2)]; eassumption. }
    destruct G as (can & G1 & G2). exists can.
    assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303
                 /\ rdn ASEGS MV (Z_to_bv 64 0x6759b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6759b8))
                 /\ rdn ASEGS MV (Z_to_bv 64 0x6759d8) 4 = Some (word_to_le_bytes 4 tid)
                 /\ rdn ASEGS MV (Z_to_bv 64 0x675a50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x695d48))
                 /\ rdn ASEGS MV (Z_to_bv 64 0x695d18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (usp + 8 * 2 + 8 * envc + 24)))).
    { eapply (ent_libcells sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity. }
    destruct T as (tid & TR & T1 & T2 & T3 & T4). exists tid. cbv zeta.
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
    { destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
    assert (HB : 0 <= envc <= 256 /\ 0 <= L0 <= 131071).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - apply (main_regs_okA sp envc L0 STR0 R).
      eapply (ent_regs sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
    - apply (main_know_okA sp envc L0 STR0 R MV SR HB).
      + eapply (ent_stack_words sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
      + eapply (ent_window sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact G1.
      + eapply (ent_img sp brk0 rdraw argv envp uid hw fs); eassumption.
      + exact TR.
      + exact (conj T1 (conj T2 (conj G2 (conj T3 T4)))).
      + change XC9_CELLS with XC9K. eapply (ent_xcells sp brk0 rdraw argv envp uid hw fs); try eassumption; first [reflexivity | exact (xc_chk_HSA r h r01 Hh)].
    - unfold lzinv. eapply (ent_lz sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - eapply (ent_model sp brk0 rdraw argv envp uid hw fs); eassumption.
    - intros k Hk. refine ((fun X Y => conj (proj1 X) (conj (proj2 X) Y)) _ _).
      + eapply (ent_str sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
      + eapply (ent_str_hi sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption; reflexivity.
  Qed.

  Theorem as0_main_auxv : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    auxv_atA sp (Z_to_bv 64 (usp + 8 * envc + 40)) FULL.
  Proof using All.
    intros h Hh E R FULL model HC.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (lib_chk_HSA r h r01 Hh) as CL. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (aux_chk_HSA r h r01 Hh) as CA.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    assert (AX : exists (uidz rnd hwz : Z) (la : LaunchAuxv) (entry gidw ae : word),
      (forall j, (j < 2 * auxv_count (la_rseq la))%nat ->
         rdn ASEGS FULL (Z_to_bv 64 (usp + 8 * 2 + 8 * envc + 24 + 8 * Z.of_nat j)) 8
         = Some (word_to_le_bytes 8 (nth j (RefLayout.auxv_words la APH0 entry (Z_to_bv 64 uidz) gidw (Z_to_bv 64 hwz) (Z_to_bv 64 rnd) ae)
                                          (Z_to_bv 64 0))))
      /\ usp + 8 * 2 + 8 * envc + 24 + 16 * Z.of_nat (auxv_count (la_rseq la)) <= 2 ^ 47
      /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64).
    { eapply (ent_auxv sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity. }
    destruct AX as (uidz & rnd & hwz & la & entry & gidw & ae & AW & AB & U1 & H1 & R1 & R2).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47 /\ usp mod 16 = 0).
    { destruct Hsp as (S1 & S2 & S3). unfold sp_window_lo, sp_window_hi in S1, S2. lia. }
    assert (UPA : bv_unsigned (Z_to_bv 64 (usp + 8 * envc + 40)) = usp + 8 * envc + 40).
    { rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. pose proof Hve as [Hle _]. lia. }
    assert (NM : forall (l : list word) n, nth n (map (fun w : word => bv_unsigned w) l) 0 = bv_unsigned (nth n l (Z_to_bv 64 0)))
      by (induction l as [|a l IH]; intros [|n]; cbn [map nth]; try reflexivity; apply IH).
    exists uidz, rnd, hwz, la, APH0, entry, gidw, ae. rewrite UPA.
    split; [exact aph0_addr|]. split; [exact aph0_ent|]. split; [exact aph0_num|]. split; [lia|].
    split.
    { intros j Hj. unfold LibIface.cellz, LibIface.auxv_vec. rewrite NM, Z_to_bv_bv_unsigned.
      replace (usp + 8 * envc + 40 + 8 * Z.of_nat j) with (usp + 8 * 2 + 8 * envc + 24 + 8 * Z.of_nat j) by lia.
      exact (AW j Hj). }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    pose proof (Z.div_mod usp 16 ltac:(lia)) as DM. destruct SR as [_ SA16]. rewrite SA16 in DM.
    replace (usp + 8 * envc + 40) with ((2 * (usp / 16) + envc + 5) * 8) by lia. apply Z.mod_mul. lia.
  Qed.

  Theorem as0_main_stack_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    forall tp, tp mod 4096 = 0 -> tp <= usp + 4096 -> defined FULL usp (tp - usp).
  Proof using All.
    intros h Hh E R FULL model HC tp Hm Hle i Hi.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    eapply (ent_stack_defined_top sp brk0 rdraw argv envp uid hw fs); try eassumption; reflexivity.
  Qed.
  Theorem as0_main_str_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA r h) R FULL model ->
    forall k, (k < 2)%nat -> forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned (cat_argv_ptr top argv envp execfn k) + i)) <> None.
  Proof using All.
    intros h Hh E R FULL model HC k Hk i Hi.
    pose proof (as0_chk_HSA r h Hh) as C0. pose proof (drv_chk_HSA r h r01 Hh) as CD. pose proof (stk_chk_HSA r h r01 Hh) as CS.
    pose proof (as0_inst_bud BUDGET EXTRA BUD_le r h Hh) as BL.
    pose proof (as0_inst_gap BUDGET LENMAX KMAX BUD GAP r h Hh) as GP.
    eapply (ent_str_defined sp brk0 rdraw argv envp uid hw fs mbase stdin gid groups net nofile sigmask abrt ur kb execfn sdf apc); try eassumption; reflexivity.
  Qed.
End Inst.
End FPX_1.
