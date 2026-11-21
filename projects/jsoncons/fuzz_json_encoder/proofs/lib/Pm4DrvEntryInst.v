(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the rseq-dependent auxv, the 6144513-byte zero-filled stack window, the nine-byte string read-ahead, the launch input's kernel build): changed GAP, SINV, a0s and 24 more; added B, Hapc, Hbrk and 28 more; removed as0_main_auxv, envc, usp; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8DrvEntryInst.v, lines 16-30, 35-83, 93-122, 128-211. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec AgentLib AxSymExec3K AxSymExec3SoundK AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4DefsK Pm4PlanImagesK
  HandoffBridgeK HandoffBInvK Pm4HandoffK Pm4HSK_0 Pm4HSK_1 Pm4MainTableK Pm4HandoffInstK Pm4DrvEntryK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive HeapIface HeapIfaceA As0DrvKitA Pm4DrvEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
(* STATEMENT CHANGED, old beside new, throughout this block: the hand-off states and the
   checks are indexed by the run's CONFIG_RSEQ flag [b].
     OLD  drv_chk HS_0 = true, stk_chk HS_0, lib_chk HS_0, xc_chk HS_0 (and HS_1, HSA h)
     NEW  drv_chk (rseq_z b) (HS_0 b) = true, .. (HSA b h), [forall b].
   [b] is destructed ABOVE every [vm_compute], so each closed check runs on a closed
   state (Pm4HandoffInstK's pattern). *)
Lemma drv_chk_0 : forall b, drv_chk (APCK.rseq_z b) (HS_0 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma drv_chk_1 : forall b, drv_chk (APCK.rseq_z b) (HS_1 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma drv_chk_HSA : forall b h, (h < 2)%nat -> drv_chk (APCK.rseq_z b) (HSA b h) = true.
Proof. intros b h Hh. destruct h as [|[|h]]; [exact (drv_chk_0 b) | exact (drv_chk_1 b) | lia]. Qed.
Lemma stk_chk_0 : forall b, stk_chk (APCK.rseq_z b) (HS_0 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma stk_chk_1 : forall b, stk_chk (APCK.rseq_z b) (HS_1 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma stk_chk_HSA : forall b h, (h < 2)%nat -> stk_chk (APCK.rseq_z b) (HSA b h) = true.
Proof. intros b h Hh. destruct h as [|[|h]]; [exact (stk_chk_0 b) | exact (stk_chk_1 b) | lia]. Qed.

Lemma lib_chk_0 : forall b, lib_chk (APCK.rseq_z b) (HS_0 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma lib_chk_1 : forall b, lib_chk (APCK.rseq_z b) (HS_1 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma lib_chk_HSA : forall b h, (h < 2)%nat -> lib_chk (APCK.rseq_z b) (HSA b h) = true.
Proof. intros b h Hh. destruct h as [|[|h]]; [exact (lib_chk_0 b) | exact (lib_chk_1 b) | lia]. Qed.

Lemma xc_chk_0 : forall b, xc_chk (HS_0 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma xc_chk_1 : forall b, xc_chk (HS_1 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma xc_chk_HSA : forall b h, (h < 2)%nat -> xc_chk (HSA b h) = true.
Proof. intros b h Hh. destruct h as [|[|h]]; [exact (xc_chk_0 b) | exact (xc_chk_1 b) | lia]. Qed.

(* NEW: the plan's [V_W]/[V_G] range entries in each hand-off state, which
   [Pm4DrvEntryK.ent_stack_words] takes as arguments ([wg_range]). *)
Lemma wk_HSA : forall b h, (h < 2)%nat -> existsb (APK.kentry_eqb (AX2K.KRange (AX2K.EVar APK.V_W) 0 4110)) (APK.kn (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vmc_refl]. Qed.
Lemma gk_HSA : forall b h, (h < 2)%nat -> existsb (APK.kentry_eqb (AX2K.KRange (AX2K.EVar APK.V_G) 0 1)) (APK.kn (HSA b h)) = true.
Proof. intros [|] [|[|h]] H; first [lia | vmc_refl]. Qed.

Section FPX_1. Context {fx : PropExec.FPState}.
Section Inst.
  (* THE SECTION'S PARAMETERS, old beside new.
       OLD  sp brk0 rdraw a0s path envp uid hw fs, with Hsp Hva Hve Hfit;
            SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw.
       NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order, with
            argv = [a0s; path] ([Pm4DrvEntryK]'s second Section's [Hargv], discharged
            by [reflexivity]); the hand-off states are those of the run's own flag
            [B := kb_rseq (in_kernel INP)] (Pm4StartupFinalK takes the certificate there).
     Every [Pm4DrvEntryK] lemma is reached by [eapply X; isec]: its arity is the set of
     Section variables its proof USES, which the text does not show. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (a0s path : list byte) (envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  #[local] Notation argv := [a0s; path].
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = APK.a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation B := (kb_rseq (in_kernel INP)).
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (APSK.cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  (* argv string [k]'s pointer, CatExec's at the revision *)
  #[local] Notation P k := (cat_argv_ptr (ed_top rdraw) argv envp execfn k).
  #[local] Notation STRLO := (bv_unsigned sp + Z.of_nat (cat_string_off B sp (ed_top rdraw) argv envp execfn)).
  #[local] Notation L0 := (Z.of_nat (length a0s)).

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.
  Hypothesis BUD_le : 16515072 + 2461523968 + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (17729665372160 + APCK.resx_bytes ASAN0 + BUDGET) + (23 + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Local Ltac isec := first [ eassumption | reflexivity | exact asan0_in_hull | exact asan0_hull_ok | exact asan0_img_facts
                           | (unfold DRV_WINDOW; eassumption) ].
  (* The four per-state facts every lemma below opens with.  [as0_inst_bud]/[as0_inst_gap]
     are Pm4HandoffInstK Section lemmas, so they too are reached by [eapply]. *)
  Local Ltac inst_facts h Hh :=
    pose proof (as0_chk_HSA B h Hh) as C0; pose proof (drv_chk_HSA B h Hh) as CD;
    pose proof (lib_chk_HSA B h Hh) as CL; pose proof (stk_chk_HSA B h Hh) as CS;
    assert (BL : APK.a_eager (HSA B h) + APK.a_abytes (HSA B h) + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT)
      by (eapply as0_inst_bud; eassumption);
    assert (GP : AsanCeil.bottomup_floor + LENMAX + (APK.a_totsz (HSA B h) + BUDGET)
                 + (Z.of_nat (length (segments_reserved ASEGS0) + APK.n_resx ASAN0 + length (APK.a_maps (HSA B h))) + KMAX) * (LENMAX + 4095)
                 <= AsanCeil.alloc_ceiling)
      by (eapply as0_inst_gap; eassumption).

  (* STATEMENT CHANGED, old beside new:
       OLD  forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
              exists can tid, let ES := env_mainA sp (Z_to_bv 64 (usp + 8*envc + 200))
                                                  (Z_to_bv 64 (usp + 8*envc + L0 + 201)) can tid R in ..
              /\ forall k < 2, rdn .. (cat_argv_ptr sp argv envp k) .. /\
                   bv_unsigned (cat_argv_ptr sp argv envp k) = usp + 8*envc + 200 + |firstn k argv|
                   /\ .. + |argv[k]| + 1 + 16 <= 2^47
       NEW  the hand-off state is [HSA B h]; argv[k]'s pointer is [P k] =
            [cat_argv_ptr (ed_top rdraw) argv envp execfn k] both in the driver's env and in
            the string facts; its value is [STRLO + |firstn k argv|]; the slack is 9
            (Main's ruling (a), Pm4DrvEntryK.ent_str_hi). *)
  Theorem as0_main_entry : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA B h) R FULL model ->
    let A0 := as0_A0 EXTRA (HSA B h) E in
    let MV := mrestrict (ahid A0 model) FULL in
    exists can tid : word,
      let ES := env_mainA sp (P 0) (P 1) can tid R in
      SX2S.regs_ok ES sr_mainA R
      /\ SX2S.know_ok ASEGS ES MV kn_mainA
      /\ lzinv ASEGS (ahid A0 model) A0 model
      /\ m_fds model = APSK.fds_std /\ m_fs model = fs
      /\ (forall k, (k < 2)%nat ->
            rdn ASEGS MV (P k) (length (nth k argv []) + 1) = Some (nth k argv [] ++ [Z_to_bv 8 0])
            /\ bv_unsigned (P k) = STRLO + Z.of_nat (total_arg_bytes_nat (firstn k argv))
            /\ bv_unsigned (P k) + Z.of_nat (length (nth k argv [])) + 1 + 9 <= 2 ^ 47).
  Proof.
    intros h Hh E R FULL model HC A0 MV.
    inst_facts h Hh.
    pose proof (wk_HSA B h Hh) as WK. pose proof (gk_HSA B h Hh) as GK.
    assert (G : exists can : word, rdn ASEGS MV (Z_to_bv 64 0x6be010) 8 = Some (word_to_le_bytes 8 can)
                                   /\ rdn ASEGS MV (Z_to_bv 64 0x69dfc0) 8 = Some (word_to_le_bytes 8 can))
      by (eapply ent_guard; isec).
    destruct G as (can & G1 & G2). exists can.
    (* [ent_libcells]' fifth conjunct, libc's __auxv cell, is true and unread since option D *)
    assert (T : exists tid : word, 1 <= bv_unsigned tid <= 4194303
                 /\ rdn ASEGS MV (Z_to_bv 64 0x69df08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x69df08))
                 /\ rdn ASEGS MV (Z_to_bv 64 0x69df28) 4 = Some (word_to_le_bytes 4 tid)
                 /\ rdn ASEGS MV (Z_to_bv 64 0x69dfa0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6be298))).
    { edestruct ent_libcells as (tid & TR & T1 & T2 & T3 & _); [isec .. |].
      exists tid. exact (conj TR (conj T1 (conj T2 T3))). }
    destruct T as (tid & TR & T1 & T2 & T3). exists tid. cbv zeta.
    assert (SR : 0x7fff80000000 <= bv_unsigned sp <= 2 ^ 47 /\ bv_unsigned sp mod 16 = 0).
    { destruct Hsp as (H1 & H2 & H3). unfold sp_window_lo, sp_window_hi in H1, H2. lia. }
    assert (HB : 0 <= Z.of_nat (length envp) <= 256 /\ 0 <= L0 <= 131071).
    { pose proof Hve as [Hle _]. pose proof Hva as (_ & _ & Hfa & _). inversion Hfa as [|x l Hx _]; subst. lia. }
    assert (WORDS : rdn ASEGS MV (Z_to_bv 64 (bv_unsigned sp)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 2))
                    /\ rdn ASEGS MV (Z_to_bv 64 (bv_unsigned sp + 8)) 8 = Some (word_to_le_bytes 8 (P 0))
                    /\ rdn ASEGS MV (Z_to_bv 64 (bv_unsigned sp + 16)) 8 = Some (word_to_le_bytes 8 (P 1))).
    { assert (E0 : P 0 = Z_to_bv 64 (bv_unsigned sp + 8 * Z.of_nat (length envp) + 488 + 32 * APCK.rseq_z B + 8 * VZ E 11 + VZ E 4))
        by (eapply ent_p0_eq; isec).
      assert (E1 : P 1 = Z_to_bv 64 (bv_unsigned sp + 8 * Z.of_nat (length envp) + 489 + 32 * APCK.rseq_z B + 8 * VZ E 11 + VZ E 4 + L0))
        by (eapply ent_p1_eq; isec).
      rewrite E0, E1. eapply ent_stack_words; isec. }
    assert (WIN : forall d (m : nat), 0 <= d -> d + Z.of_nat m <= DRV_ZWIN ->
                  store_ok ASEGS MV (Z_to_bv 64 (bv_unsigned sp - DRV_ZWIN + d)) m = true).
    { intros d m Hd Hm. eapply ent_window; isec. }
    assert (IMG : forall lo hi i, In (lo, hi) [(0x10000, 0x162c90); (0x162cac, 0x166840); (0x68c54a, 0x69df00); (0x6be298, 0x6be2c8); (0x6be340, 0x6be344)] ->
                  lo <= i < hi -> MV (Z_to_bv 64 i) = None).
    { intros lo hi i Hin Hi. eapply ent_img; isec. }
    assert (LIBW : rdn ASEGS MV (Z_to_bv 64 0x69df08) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x69df08))
                   /\ rdn ASEGS MV (Z_to_bv 64 0x69df28) 4 = Some (word_to_le_bytes 4 tid)
                   /\ rdn ASEGS MV (Z_to_bv 64 0x69dfc0) 8 = Some (word_to_le_bytes 8 can)
                   /\ rdn ASEGS MV (Z_to_bv 64 0x69dfa0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6be298)))
      by exact (conj T1 (conj T2 (conj G2 T3))).
    assert (XCW : Forall (fun c : Z * nat * Z => rdn ASEGS MV (Z_to_bv 64 (fst (fst c))) (snd (fst c)) = Some (word_to_le_bytes (snd (fst c)) (Z_to_bv 64 (snd c)))) XC9_CELLS).
    { change XC9_CELLS with XC9K. pose proof (xc_chk_HSA B h Hh) as XC. eapply ent_xcells; isec. }
    split; [|split; [|split; [|split; [|split]]]].
    - eapply main_regs_okA. intros r v Hin. eapply ent_regs; first [exact Hin | isec].
    - eapply main_know_okA; eassumption.
    - unfold lzinv. eapply ent_lz; isec.
    - eapply ent_model; isec.
    - eapply ent_model; isec.
    - intros k Hk. refine ((fun X Y => conj (proj1 X) (conj (proj2 X) Y)) _ _).
      + eapply ent_str; first [exact Hk | isec].
      + eapply ent_str_hi; first [exact Hk | isec].
  Qed.

  (* DROPPED, old beside new (Main's ruling, option D):
       OLD  Theorem as0_main_auxv : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA h) R FULL model ->
              exists uidz rnd hwz : Z, (forall j, (j < 20)%nat ->
                rdn ASEGS FULL (Z_to_bv 64 (usp + 8 * envc + 40 + 8 * Z.of_nat j)) 8 = Some (.. (nth j (auxv_list uidz rnd hwz) 0)))
              /\ 0 <= uidz < 2 ^ 32 /\ 0 <= hwz < 2 ^ 64 /\ usp <= rnd /\ rnd + 16 <= 2 ^ 64.
     The ten contiguous pairs at [e_auxv] are false at LPS 75d69e00 (27/29 pairs, the claimed
     ones at 16*{13,14,15,11,10,19,20,23,24,26+2r}); the fact's only consumer was
     [Pm4MainPhaseA]'s [auxv_atA] premise, whose chain ends at LibIface.lib_init_facts'
     auxv conjuncts, which no prover reads.  [Pm4DrvEntryK.ent_auxv] goes with it. *)

  (* STATEMENT UNCHANGED apart from the state's flag ([HSA B h]); proof by [eapply]. *)
  Theorem as0_main_stack_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA B h) R FULL model ->
    forall top, top mod 4096 = 0 -> top <= bv_unsigned sp + 4096 -> defined FULL (bv_unsigned sp) (top - bv_unsigned sp).
  Proof.
    intros h Hh E R FULL model HC top Hm Hle i Hi.
    inst_facts h Hh.
    eapply ent_stack_defined_top; first [exact Hm | exact Hle | exact Hi | isec].
  Qed.

  (* STATEMENT CHANGED, old beside new -- the pointer and the slack:
       OLD  .. 0 <= i < |argv[k]| + 1 + 16 -> FULL (.. (cat_argv_ptr sp argv envp k) + i) <> None
       NEW  .. 0 <= i < |argv[k]| + 1 + 8  -> FULL (.. (P k) + i) <> None
     (Main's ruling (a); Pm4DrvEntryK.ent_str_defined). *)
  Theorem as0_main_str_defined : forall h, (h < 2)%nat -> forall E R FULL model, CSOK E (HSA B h) R FULL model ->
    forall k, (k < 2)%nat -> forall i, 0 <= i < Z.of_nat (length (nth k argv [])) + 1 + 8 -> FULL (Z_to_bv 64 (bv_unsigned (P k) + i)) <> None.
  Proof.
    intros h Hh E R FULL model HC k Hk i Hi.
    inst_facts h Hh.
    eapply ent_str_defined; first [exact Hk | exact Hi | isec].
  Qed.
End Inst.
End FPX_1.
