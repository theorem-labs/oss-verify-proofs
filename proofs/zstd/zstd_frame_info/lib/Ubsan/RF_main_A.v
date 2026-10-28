(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP InitMem.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Common Require Import DrvAgree Startup_kit STRW_tac F_fmt_fp_lib Printf_fmts.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import UImg F_syscalls StdioFiles Startup Exit F_printf_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Malloc Require Import MallocBlocks MallocTree MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RMallocRep RMallocTree RMalloc_iface Harness_iface RDriver_iface RDriver_kit RDriver_ctx.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Prelim STree Malloc Monad Stdio Driver Prog.
From OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac rpc := apply ret_pc_even; [lia| reflexivity].

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma stderr_file0_wfile : forall m, stderr_file0 m -> stderr_wfile m.
Proof.
  intros m H. exists (Z_to_bv 64 5), (wz 0), 0, 0, (repeat (Z_to_bv 8 0) 80). split; [exact H|]. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Section A.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw) (TID : Z).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis HT : 0 < TID < 4194304.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).

  (* [comment removed for export] *)
  Definition BASE (mm : mem) : Prop :=
    stk usegs mm LO' (usp0 + -128) /\ mem_inv usegs mm /\ RSTAT TID mm /\ rauxv_ok mm usp0 /\ bytes_at usegs mm usp0 IMGB
    /\ stderr_file0 mm /\ stdout_file mm stdout_init /\ trun_cells0 mm.

  #[using="rc VSP VARGV VENVP"] Lemma IMGB_len : usp0 + Z.of_nat (length IMGB) <= 2^64.
  Proof.
    destruct VSP as ((A & B & C) & _ & _). unfold sp_window_lo, sp_window_hi in *.
    pose proof (build_stack_bytes_length pph sp0 argv envp uid hw draw). pose proof (raw_len_nonneg argv envp).
    destruct VARGV as (A1 & A2 & _). destruct VENVP as (E1 & E2 & _). unfold raw_len, struct_size, argc, envc in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010=4699407760.2100000FS1A1B1H2H02A12A22E12E2".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc VSP"] Lemma IMGB_top : usp0 + Z.of_nat (length IMGB) <= 2^47.
  Proof.
    destruct VSP as (_ & _ & FIT). unfold entry_stack_fits, entry_stack_span, sp_window_hi in FIT.
    change (Z.of_nat auxv_size) with 160 in FIT.
    pose proof (build_stack_bytes_length pph sp0 argv envp uid hw draw) as BL. pose proof (raw_len_nonneg argv envp).
    unfold raw_len, struct_size, argc, envc in *. Local Ltac2 Set LiaHints.tbl := fun () => "0010>42614262010.1500000:S3FIT2BL1H".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="Type"] Lemma BASE_heap_pres : forall LB m m', BASE m -> rheap_pres LB (usp0 + -128) m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> rauxv_ok m' usp0 -> BASE m'.
  Proof.
    intros LB m m' (ST & MI & RS & AUX & IMG & SE & SO & TR) HP MI' ST' AUX'.
    split; [exact ST'|]. split; [exact MI'|]. split; [eapply RSTAT_heap_pres; [exact HP| exact RS]|]. split; [exact AUX'|].
    Local Ltac2 Set LiaHints.tbl := fun () => "0010>11139824401.27000001S".
split; [eapply rheap_pres_bytes_at; [exact HP| exact IMG| left; lia]|].
    split; [eapply stderr_file0_heap_pres; [exact HP| exact SE]|].
    split; [eapply stdout_file_heap_pres; [exact HP| exact SO]| eapply trun_cells0_heap_pres; [exact HP| exact TR]].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition WOK (iv : Z * Z) : Prop :=
    (LO' <= fst iv /\ snd iv <= usp0 + -128) \/ (fst iv = RERRNO /\ snd iv = RERRNO + 4)
    \/ (snd iv <= ATOP /\ (snd iv <= 0x10000 \/ 0x4f000 <= fst iv))
    \/ (UREAD_STAGE <= fst iv /\ snd iv <= UREAD_STAGE + 65536).

  #[using="argv envp VSP"] Lemma WOK_outside : forall W a, Forall WOK W ->
    (usp0 + -128 <= a \/ (0x10000 <= a < 0x4f000 /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (UREAD_STAGE <= a < UREAD_STAGE + 65536))) -> outside W a.
  Proof.
    pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in *.
    induction W as [|[lo1 hi1] W IH]; intros a HW Ha; cbn; [exact I|].
    inversion HW as [|x l H1 H2]; subst. split; [| apply IH; assumption].
    unfold WOK, LO, RERRNO, UREAD_STAGE in H1. cbn [fst snd] in H1. unfold RERRNO, UREAD_STAGE in Ha. Local Ltac2 Set LiaHints.tbl := fun () => "0010>20527683581.2300000:S2SF2Ha2H1".
lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="VSP VARGV VENVP"] Lemma BASE_munch : forall W m m', BASE m -> Forall WOK W -> munch W m m' -> wmono usegs m m' ->
    mem_inv usegs m' -> stk usegs m' LO' (usp0 + -128) -> BASE m'.
  Proof.
    intros W m m' (ST & MI & RS & AUX & IMG & SE & SO & TR) HW MU WM MI' ST'. pose proof (sp_facts sp0 argv envp VSP) as SF. pose proof IMGB_len as IL. unfold LO in *.
    split; [exact ST'|]. split; [exact MI'|].
    Local Ltac2 Set LiaHints.tbl := fun () => "0030>15175843668.3324875532855.349602355480.33 00000400:00>S2HaS2SF1HS2Ha".
split; [eapply RSTAT_munch; [exact MU| exact WM| intros a Ha; apply WOK_outside; [exact HW| unfold rstat_addr, RERRNO, UREAD_STAGE in *; lia]| exact RS]|].
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|].
      eapply Forall_impl; [| exact HW]. intros [lo1 hi1] H. unfold WOK, RERRNO, RAUXV_CELL, RLIBC, LO, UREAD_STAGE in *. cbn [fst snd] in *. lia. }
    split.
    { eapply bytes_at_magree; [eapply magree_of_munch; [exact MU| exact WM]| exact IMG|]. intros a Ha. cbn. apply WOK_outside; [exact HW| left; lia]. }
    split.
    { eapply stderr_file0_munch; [exact MU| exact WM| | exact SE]. intros a Ha. apply WOK_outside; [exact HW| unfold stderr_addr, RERRNO, UREAD_STAGE in *; lia]. }
    split.
    { eapply stdout_file_munch; [exact MU| exact WM| | exact SO]. intros a Ha. apply WOK_outside; [exact HW| unfold stdout_addr, RERRNO, UREAD_STAGE in *; lia]. }
    eapply trun_cells0_munch; [exact MU| exact WM| | exact TR]. intros a Ha. apply WOK_outside; [exact HW|].
    unfold trun0_addr, PINIT_FLAG, PGOT_FUZZ_INIT, PGOT_STDERR, PSTDERR_PTR, RERRNO, UREAD_STAGE in *. lia.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  #[using="argv envp VSP"] Lemma RHEAP_munchW : forall s LB W m m', Forall WOK W -> munch W m m' -> wmono usegs m m' ->
    (forall iv, In iv W -> snd iv <= ATOP -> (snd iv <= 0x10000 \/ 0x4f000 <= fst iv) ->
                exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) ->
    RHEAP s LB m -> RHEAP s LB m'.
  Proof.
    intros s LB W m m' HW MU WM HB HP. pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in *.
    eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MU| exact WM|].
    apply Forall_forall. intros [lo1 hi1] Hin. pose proof (proj1 (Forall_forall _ _) HW _ Hin) as H.
    unfold WOK, rclient_write_ok, RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, LO, UREAD_STAGE in *. cbn [fst snd] in *.
    Local Ltac2 Set LiaHints.tbl := fun () => "0040>18527521756.2824447471371.2855437548248.2858391612977.2800000300900?00BS1HS2SF1HS2SF1HS1H".
destruct H as [H|[H|[H|H]]]; [left; lia| right; left; lia| right; right| right; left; lia]. apply (HB (lo1, hi1)); [exact Hin| cbn; atop_facts; lia| cbn; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="rc argv envp VSP"] Lemma main_prologue : forall (Q : machine_state -> Prop) (ra s0 s1 a0 a1 a2 s2 s3 t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    stk usegs m LO' (usp0 + -48) -> mem_inv usegs m ->
    (forall (j8 : list byte) m', rw_cells usegs m' (usp0 + -128) [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk usegs m' LO' (usp0 + -128) ->
        munch [(usp0 - 128, usp0 - 48)] m m' -> wmono usegs m m' -> mem_inv usegs m' ->
        evt usegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 (Z_to_bv 64 2) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x12818) fc None m' (seg_rom usegs))) ->
    evt usegs Q (MS (mkR ra (Z_to_bv 64 (usp0 + -48)) gpv tpv t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (Z_to_bv 64 0x127ec) fc None m (seg_rom usegs)).
  Proof.
    intros until m. intros ST MI K. pose proof (sp_facts sp0 argv envp VSP) as SF. unfold LO in *.
    pose proof (munch_refl [(usp0 - 128, usp0 - 48)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "00P0>10370078823.6111805467289.5811805467289.5911805467289.6011805467289.6116368629351.6019084113859.6127941168743.6131053909955.6033580666819.6134685236327.5938037297445.5248077244355.6148622319811.5949705053714.5849705053714.5949705053714.6049705053714.6151782096487.5854590468691.5056283539395.5857084014183.6158241529539.605859191911.60 66661700291.6167593320551.5967792789095.6168587509587.5868587509587.5968587509587.6068587509587.618895973571.59 00000100500900=00A00B00C00D00E00F00G00H00I00J00Q00X00_00f00g00h00i00j00k00l00m00n00o01601=01D01K01LSS2HBS2HBS2HBS2HBSSSSSSSSSS2SF2HBS2SF2HBS2SF2HBS2SF2HBSSSSSSSSSS2SF2HBS2SF2HBS2SF2HBS2SF2HBS".
carve_frame 80%nat ST.
    do 10 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => eapply (K _ mx) end; [exact FR| exact ST| exact MU| exact WM| assumption].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  Definition STG (mm : mem) : Prop := exists sj, rw_cells usegs mm UREAD_STAGE [CB PSTAGE_LEN sj].

  (* [comment removed for export] *)
  Definition P1 (ms : machine_state) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (fc : bv 32) (mm : mem) (j8 : list byte),
      ms = MS (mkR (Z_to_bv 64 PSTAGE2_RET) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 2) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 PMAIN) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              bvmap_empty (Z_to_bv 64 0x1281c) fc None mm (seg_rom usegs)
      /\ MFRAME sp0 argv mm j8 s7 s6 s5 s4 /\ BASE mm /\ RHEAP (ps_init (reservedZ usegs) ATOP) [] mm
      /\ rw_cells usegs mm RERRNO [C4 (Z_to_bv 64 0)] /\ frm0 fc /\ STG mm.
End A.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section A2.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (draw : EntryDraw).
  Hypothesis VSP : dvalid_sp sp0 argv envp.
  Hypothesis HSEC : SECRET = InitMem.draw_secret draw.
  Hypothesis VARGV : valid_argv argv.
  Hypothesis VENVP : valid_envp envp.
  Hypothesis FPR : @fprintf_diag_stmt PState.
  Hypothesis FWX : fwritex_stderr_stmt.
  Hypothesis SWF : stdio_write_flush_stmt.
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATP).
  Notation IMGB := (build_stack_bytes pph sp0 argv envp uid hw draw).
  Notation LO' := (LO sp0).

  (* [comment removed for export] *)
  #[using="VSP HSEC VARGV VENVP"] Lemma main_to_test : forall (ms : machine_state) (Q : machine_state -> Prop),
    pat_main sp0 argv envp uid hw draw CAN ms ->
    (forall (TID : Z) (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (mm : mem) (j8 : list byte),
        0 < TID < 4194304 ->
        MFRAME sp0 argv mm j8 s7 s6 s5 s4 -> BASE sp0 argv envp uid hw draw TID mm -> RHEAP (ps_init (reservedZ usegs) ATOP) [] mm ->
        rw_cells usegs mm RERRNO [C4 (Z_to_bv 64 0)] -> STG mm ->
        evt usegs Q (MS (mkR (Z_to_bv 64 PSTAGE2_RET) (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2
                          (Z_to_bv 64 2) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                          (Z_to_bv 64 PMAIN) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        bvmap_empty (Z_to_bv 64 0x12818) (Z_to_bv 32 0) None mm (seg_rom usegs))) ->
    evt usegs Q ms.
  Proof.
    intros ms Q AM K.
    destruct AM as (t0 & t1 & t2 & a3 & a4 & a5 & a6 & a7 & s4 & s5 & s6 & s7 & s8 & s9 & s10 & s11 & t3 & t4 & t5 & t6 & t & P0 & pg & m
                    & -> & MI & ST & TD & ERR & TLS & LIBC1 & LIBC2 & MTLS & SYSI & PROG & HWCAP & ENV & DSS & GUARD & GOT0 & GOTM & GCX & G28 & G38 & G50 & GOTG & GF & IA & FA & GD0 & INI & FIN & EXL & SOU & SEU & SIN & OFL & SOF & SEF & IMG & IMGW & HP0 & NONE & HT).
    pose proof (sp_facts sp0 argv envp VSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL. unfold LO in *.
    pose proof (bytes_at_bound _ _ _ _ IMG) as IMGBD.
    pose proof (heap_init sp0 argv envp m NONE LIBC1 LIBC2 GOTG GUARD MI) as [HP0i AUXC].
    pose proof (rauxv_ok_init sp0 argv envp uid hw draw m NONE LIBC1 LIBC2 GOTG GUARD MI IMG HSEC (proj1 (proj2 VSP))) as AI.
    pose proof (trun_cells0_init m NONE) as TR0.
    pose proof (rstatx0_init m NONE) as [DSO0 AXS0].
    pose proof (stderr_file0_init m NONE) as SE.
    pose proof (stage_init m NONE) as STG0.
    clear TLS MTLS SYSI PROG HWCAP ENV DSS GOT0 GOTM G38 G50 IA INI IMGW HP0 NONE.
    Local Ltac2 Set LiaHints.tbl := fun () => "0070>12526735165.8612530648637.8816800608486.7516800608486.8422708542307.8546849286404.8461256830327.8400000700F00G00H00L00P00TS2SF2HaS2SF2Ha7PSTAGERSSS2HaS2SFS2SF".
replace (usp0 - 8388608) with (usp0 + -8388608) in ST by lia.
    unfold PMAIN, PSTAGE2_RET in *.
    eapply (main_prologue sp0 argv envp VSP); [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST| exact MI|].
    intros j8 m1 FR ST1 MU WM MI1. unfold LO in ST1.
    pose proof (magree_of_munch usegs _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < usp0 - 128 \/ usp0 - 48 <= a) -> (fun a0 : Z => outside [(usp0 - 128, usp0 - 48)] a0) a) by (intros a Ha; cbn; lia).
    apply (K t t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 j8 HT).
    - exact FR.
    - split; [unfold LO; replace (usp0 - 8388608) with (usp0 + -8388608) by lia; exact ST1|]. split; [exact MI1|].
      split. { eapply (RSTAT_agree t _ _ _ AG); [intros a Ha; apply OUT; unfold rstat_addr in Ha; lia|].
               unfold RSTAT. split; [exact TD|]. split; [exact EXL|]. split; [exact GF|]. split; [exact FA|]. split; [exact FIN|]. split; [exact GCX|].
               split; [exact OFL|]. split; [exact SIN|]. split; [exact SOU|]. split; [exact SEU|]. split; [exact G28|]. split; [exact GD0|]. split; [exact DSO0| exact AXS0]. }
      split. { eapply rauxv_ok_frame; [exact AI| exact MU| exact WM|]. constructor; [| constructor]. unfold RAUXV_CELL, RLIBC. cbn [fst snd]. lia. }
      split. { eapply bytes_at_magree; [exact AG| exact IMG| intros a Ha; apply OUT; lia]. }
      split. { eapply (stderr_file0_agree _ _ _ AG); [intros a Ha; apply OUT; unfold stderr_addr in Ha; lia| exact SE]. }
      split. { eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT; unfold stdout_addr in Ha; lia| exact SOF]. }
      eapply (trun_cells0_agree _ _ _ AG); [intros a Ha; apply OUT| exact TR0].
      unfold trun0_addr, PINIT_FLAG, PGOT_FUZZ_INIT, PGOT_STDERR, PSTDERR_PTR in Ha. lia.
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP0i| exact MU| exact WM|]. constructor; [| constructor]. left. cbn [fst snd]. atop_facts. lia.
    - eapply rw_cells_magree; [exact AG| unfold RERRNO; exact ERR| intros a Ha; apply OUT; cbn in Ha; unfold RERRNO in Ha; lia].
    - destruct STG0 as [sj SJ]. exists sj. eapply rw_cells_magree; [exact AG| exact SJ| intros a Ha; apply OUT; cbn in Ha; unfold UREAD_STAGE in Ha; lia].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="VSP HSEC VARGV VENVP"] Lemma main_to_P1 : forall (arg0 arg1 : list byte) (ms : machine_state) (Q : machine_state -> Prop),
    argv = [arg0; arg1] -> pat_main sp0 argv envp uid hw draw CAN ms ->
    (forall TID ms', 0 < TID < 4194304 -> P1 sp0 argv envp uid hw draw TID ms' -> evt usegs Q ms') ->
    evt usegs Q ms.
  Proof.
    intros arg0 arg1 ms Q EARGV AM K.
    eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm j8 HT FR BA HP ERR SJ.
    unfold argc. rewrite EARGV. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]. rewrite <- EARGV.
    pose proof BA as (ST & MI & _).
    zstep. Local Ltac2 Set LiaHints.tbl := fun () => "0010>59323410545.54000004S2K0".
if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    apply (K TID); [exact HT|].
    unfold P1, PMAIN, PSTAGE2_RET. do 20 eexists. exists (Z_to_bv 32 0), mm, j8. split; [reflexivity|].
    split; [exact FR|]. split; [exact BA|]. split; [exact HP|]. split; [exact ERR|]. split; [vm_compute; reflexivity| exact SJ].
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".

  (* [comment removed for export] *)
  #[using="VSP HSEC VARGV VENVP FPR FWX SWF"] Lemma main_usage : forall ms, pat_main sp0 argv envp uid hw draw CAN ms -> Z.of_nat (length argv) <> 2 ->
    implM usegs (main_model Prog.io raw_malloc raw_free UREAD_STAGE Prog.alloc_init Prog.run Prog.alloc_count (argv_Z argv))
          (ps_init (reservedZ usegs) ATOP) (fun code s' ms' => pat_exit code s' ms') ms.
  Proof.
    intros ms AM HARGC.
    unfold main_model. unfold argv_Z at 1. rewrite length_map.
    replace (Z.of_nat (length argv) =? 2) with false by (symmetry; apply Z.eqb_neq; exact HARGC). cbn [negb].
    unfold implM. apply impl_evt with (P := fun ms' => impl usegs (at_node usegs)
        ((io_diag Prog.io (DUsage (nth 0 (argv_Z argv) []));;; mret 2) (ps_init (reservedZ usegs) ATOP))
        (epost (fun p : Z * PState => pat_exit (fst p) (snd p))) ms'); [| intros ms' H; exact H].
    eapply main_to_test; [exact AM|]. intros TID t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mm j8 HT FR BA HP ERR _.
    pose proof (sp_facts sp0 argv envp VSP) as SF. pose proof (IMGB_len sp0 argv envp uid hw draw VSP VARGV VENVP) as IL. unfold LO in *.
    pose proof BA as (ST & MI & RS & AUX & IMG & SE & SO & TR). unfold LO in ST.
    pose proof RS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G28 & GD0 & _).
    destruct VARGV as (ARGC & _ & ARGLEN & NONUL & _).
    Local Ltac2 Set LiaHints.tbl := fun () => "00J0?11410905828.74 15034496672.74 16075584458.74 16800608486.10317381815389.10324361825921.74 25546104465.74 25573673715.75 30709266035.74 31036321035.74 3834053667.3   49364486404.10352799084368.74 53712225440.74 54263845776.1005452366560.105 56323174152.74 57614170466.10357614170466.10459102833272.74 59323410545.75 59670567639.74 66026193812.10066026193812.74 6667549001.105 67209421747.62 00000400500;00<00=00A00B00M00T00Z00^00b01801F01G01N01R01V01]01^01k02902=02A02E02KS2SFSS4ARGCSSS2SFSS2SF4P0HI1HS5A0LENS4SLK0S2SFS2SFS2SF2IL4ARGC4P0LO4P0HIS2SF4ARGC4P0LOSS2SF2HaS2SFS2HaS2SF2HaSS5HARGC2SF2K0S2SF4ARGC4P0LOS2SFS2SFS2HaS4ARGC".
destruct argv as [|arg0 argv'] eqn:EARGV; [cbn in ARGC; lia|]. rewrite <- EARGV in *.
    (* [comment removed for export] *)
    destruct (argv_cstring sp0 argv envp uid hw draw mm IMG 0 arg0 ltac:(rewrite EARGV; reflexivity) ltac:(clear -SF; OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.Lib.LiaTuning.dmlia))
      as (p0 & slack0 & HP0 & P0LO & P0HI & STR0 & SLK0). unfold str_base, struct_size, argc, envc in P0LO.
    destruct (stack_pieces sp0 argv envp uid hw draw mm IMG) as (_ & ARGVP & _).
    assert (A0NN : ~ In (Z_to_bv 8 0) arg0) by (rewrite EARGV in NONUL; inversion NONUL; assumption).
    assert (A0LEN : Z.of_nat (length arg0) <= 131071) by (rewrite EARGV in ARGLEN; inversion ARGLEN; assumption).
    unfold argc, PMAIN, PSTAGE2_RET. zstep. if_cases K0; zify_cond K0; try (exfalso; lia). clear K0.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    pose proof (u64ro_read usegs mm (usp0 + 8) (argv_ptrs sp0 argv envp ++ [Z_to_bv 64 0]) 0 (Z_to_bv 64 p0) (Z_to_bv 64 (usp0 + 8))
                  ARGVP ltac:(rewrite nth_error_app1 by (rewrite argv_ptrs_length, EARGV; cbn; lia); exact HP0) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. zstep.
    (* [comment removed for export] *)
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM usegs tm (ps_init (reservedZ usegs) ATOP) (fun code s' ms' => pat_exit code s' ms') msx) end.
    eapply implM_bind.
    { eapply (FPR (DUsage (nth 0 (argv_Z argv) []))) with (lo := usp0 - 8388608) (canary := CAN);
        [exact FWX| exact SWF| apply stderr_file0_wfile; exact SE| reflexivity| | rewrite unsigned_lit by lia; exact ST
        | rewrite unsigned_lit by lia; unfold FPRINTF_DEPTH; lia| unfold GLOBALS_TOP; lia| rewrite unsigned_lit by lia; lia
        | apply (RHEAP_ssp _ _ _ HP)| exact MI| vm_compute; reflexivity].
      cbn [diag_args]. split; [reflexivity|]. exists slack0.
      rewrite EARGV. cbn [argv_Z map nth]. rewrite unsigned_lit by lia.
      unfold F_fmt_fp_lib.zb. rewrite zbytes_map_unsigned'. unfold zlength. rewrite !length_map.
      split; [exact STR0|]. split; [apply map_unsigned_pos; exact A0NN|]. split; [lia|].
      split; [unfold FmtFp.INT_MAX; lia|]. split; [right; rewrite unsigned_lit by lia; lia|]. split; [unfold GLOBALS_TOP; lia|].
      pose proof (IMGB_top sp0 argv envp uid hw draw VSP). lia. }
    cbv beta. intros [] st' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m2 & -> & MUc & WMc & MI2 & FRM2 & FEQ & ST2 & SEW & SSP2 & ->).
    rewrite !unsigned_lit in MUc by lia. rewrite !unsigned_lit in ST2 by lia.
    replace (ret_pc (Z_to_bv 64 0x129a0)) with (Z_to_bv 64 0x129a0) by (symmetry; rpc).
    pose proof (magree_of_munch usegs _ _ _ MUc WMc) as AG.
    assert (OUT : forall a, (usp0 - 128 <= a /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    assert (OUT2 : forall a, (0x10000 <= a < 0x4f000 /\ ~ (0x1dcf8 <= a < 0x1dcf8 + 232)) -> (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -128); (0x1dcf8, 0x1dcf8 + 232)] a0) a).
    { intros a Ha. cbn. lia. }
    apply implM_ret. unfold MFRAME, PMAIN, PSTAGE2_RET in FR.
    apply (rw_cells_magree usegs _ _ _ _ _ AG) in FR; [| intros a Ha; apply OUT; cbn in Ha; lia].
    zstep.
    eapply (main_return sp0 argv envp TID VSP HT 2 (ps_init (reservedZ usegs) ATOP) []).
    - unfold MFRAME, PMAIN, PSTAGE2_RET. exact FR.
    - unfold LO. replace (usp0 - 8388608) with (usp0 + -8388608) in ST2 by lia. exact ST2 || exact ST2.
    - eapply (RSTAT_agree TID _ _ _ AG); [intros a Ha; apply OUT2; unfold rstat_addr in Ha; lia| exact RS].
    - eapply RMalloc_ifaceP.RHEAP_frame_proof; [exact HP| exact MUc| exact WMc|].
      constructor; [left; cbn [fst snd]; atop_facts; lia|]. constructor; [| constructor].
      right; left. cbn [fst snd]. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP. lia.
    - cbn [ps_so ps_init]. eapply (stdout_file_agree _ _ _ _ AG); [intros a Ha; apply OUT2; unfold stdout_addr in Ha; lia| exact SO].
    - apply stderr_wfile_file. exact SEW.
    - exact MI2.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End A2.
End CANSEC1.
