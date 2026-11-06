(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages ITreeA NodesA SysStepA MonadA.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AM_monadx AM_syscalls AX_file AM_stdio_exit
     AI_shadow AX_unreg AX_unreg2 AX_unreg3 AX_atexit AX_fini2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Import ITree.Exc.

Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.

Notation A_EXIT := 0x91d10%Z (only parsing).
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AEXIT_DEPTH : Z := 320.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_statics (m : mem) (t : Z) : Prop :=
     rw_cells asegs m 0x5e0a68 [C4 (Z_to_bv 64 t)] /\ 0 < t < 2^31        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x600d80 [C4 (Z_to_bv 64 0)]                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13fa20 [C1 (Z_to_bv 8 0)]
  /\ fini_statics m /\ unreg_statics m /\ globals_tab m
  /\ rw_cells asegs m 0xaa510 [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0xaa4c0 [C8 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xab430 [C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
End RC__1.
Notation EXW q :=
  [(q - 320, q); (0x600d80, 0x600d84); (0x600b60, 0x600d80); (0xaa510, 0xaa511); (0xaa4c0, 0xaa4c8); (0xab430, 0xab438);
   (SHA_LO, SHA_HI); (SHB_LO, SHB_HI); (SHC_LO, SHC_HI)]%Z.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition aexit_prefix_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code : Z) (ra s0 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x91d7c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x97aa4) fc None m' (seg_rom asegs)
    /\ munch (EXW (bv_unsigned sp)) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra].

Lemma aexit_prefix_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo code t : Z) (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop)
    (reg : bool) (p3 p4 FJ AJ : list byte),
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000e048 -> P (Z_to_bv 64 a, k)) ->
  stk asegs m lo (bv_unsigned sp) -> (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo -> lo <= bv_unsigned sp - AEXIT_DEPTH ->
  mem_inv asegs m ->
  exit_statics m t ->
  rw_cells asegs m AATX (atx_cells reg p3 p4 FJ AJ) ->                              (* [comment removed for export] *)
  rw_cells asegs m 0x5e01d4 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells asegs m 0x600da0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
  tp = Z_to_bv 64 0x5e0b10 -> a0 = Z_to_bv 64 code -> 0 <= code < 2^32 ->
  evtA asegs P (aexit_prefix_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code ra s0 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 A_EXIT) fc None m (seg_rom asegs)).
Proof.
  intros until AJ. intros PSTK PIMG PSHA PSHB ST LOC LO MI ES ATX FLG LIBC SA SB SC Htp Ha0 CODE. subst tp a0.
  unfold AEXIT_DEPTH in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  destruct ES as (TID & Ht & EXL & COV & FS & G & TAB & CMPL & REGD & MUT).
  pose proof (munch_refl (EXW (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold atx_cells in ATX.
  carve_frame 16%nat ST.
  stepA. stepA. stepA. zstepA. zstepA. stepA.
  replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t : word)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  stepA. zstepA.
  (* [comment removed for export] *)
  stepA. replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0 : word) by (apply bv_eq; vm_compute; reflexivity).
  stepA. if_false. stepA. stepA. if_false.
  zstepA. stepA. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. }
  clear K. stepA. if_true.
  zstepA. stepA. (* [comment removed for export] *)
  call_spA (afoe_spec reg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo p3 p4 FJ AJ cdt thr sec tm1 P);
    [ intros a k H1 H2; apply PSTK; lia | exact PIMG | exact ST | lia | lia | exact MI | unfold atx_cells; exact ATX | exact FLG | exact COV | exact LIBC
    | vm_compute; reflexivity | ].
  stepA. (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
    pose proof (unreg_statics_transport _ _ _ G MUx WMx ltac:(unreg_statics_disjoint)) as Gx;
    pose proof (globals_tab_transport _ _ _ TAB MUx WMx ltac:(cbn [disjoint_from]; repeat split; lia)) as TABx;
    pose proof (fini_statics_transport _ _ _ FS MUx WMx ltac:(unfold fini_statics_cells; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; repeat split; lia|]); apply Forall_nil)) as FSx
    end end.
  call_spA (libc_exit_fini_spec P _ _ _ _ _ lo _);
    [ exact LOC | lia | intros a k H1 H2; apply PSTK; lia | exact PIMG | exact PSHA | exact PSHB
    | eassumption | eassumption | exact FSx | exact Gx | exact TABx | eassumption | eassumption | eassumption | eassumption | eassumption | eassumption
    | vm_compute; reflexivity | ].
  stepA. (* [comment removed for export] *)
  apply evtA_done. unfold aexit_prefix_post. do 16 eexists.
  split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

(* [comment removed for export] *)
Definition exit_regions : list (Z * Z) :=
  ([(0x5e0a68, 4); (0x600d80, 4); (0x13fa20, 1); (0xa9380, 4416); (0xaa510, 1); (0xaa4c0, 8); (0xab430, 8)]
   ++ fini_statics_cells ++ unreg_statics_cells)%Z.

Lemma exit_statics_transport : forall W m m' t,
  exit_statics m t -> munch W m m' -> wmono asegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) exit_regions -> exit_statics m' t.
Proof.
  intros W m m' t ES MU WM D. unfold exit_regions in D.
  rewrite !Forall_app in D. destruct D as [D [DF DU]].
  apply Forall_cons_iff in D; destruct D as [D1 D]. apply Forall_cons_iff in D; destruct D as [D2 D].
  apply Forall_cons_iff in D; destruct D as [D5 D]. apply Forall_cons_iff in D; destruct D as [D6 D].
  apply Forall_cons_iff in D; destruct D as [D7 D]. apply Forall_cons_iff in D; destruct D as [D8 D].
  apply Forall_cons_iff in D; destruct D as [D9 _]. cbn [fst snd] in *.
  destruct ES as (TID & Ht & EXL & COV & FS & G & TAB & CMPL & REGD & MUT).
  assert (T : forall lo n A cs, rw_cells asegs m A cs -> disjoint_from W lo n -> lo <= A -> A + Z.of_nat (cells_size cs) <= lo + n ->
              rw_cells asegs m' A cs).
  { intros lo n A cs X HD X1 X2. eapply rw_cells_transport; [exact X | exact MU | exact WM |]. eapply disjoint_from_sub; [exact HD | lia | lia]. }
  unfold exit_statics.
  split; [apply (T _ _ _ _ TID D1); cbn; lia|]. split; [exact Ht|]. split; [apply (T _ _ _ _ EXL D2); cbn; lia|].
  split; [apply (T _ _ _ _ COV D5); cbn; lia|].
  split; [exact (fini_statics_transport _ _ _ FS MU WM DF)|]. split; [exact (unreg_statics_transport _ _ _ G MU WM DU)|].
  split; [exact (globals_tab_transport _ _ _ TAB MU WM D6)|].
  split; [apply (T _ _ _ _ CMPL D7); cbn; lia|]. split; [apply (T _ _ _ _ REGD D8); cbn; lia| apply (T _ _ _ _ MUT D9); cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition stdio_state (m : mem) (so : stdout_st) (guard : word) (cdt thr sec : byte) (tm1 : word) : Prop :=
  stdio_statics m cdt thr sec tm1 /\ stdin_file m /\ stdout_file m so /\ stderr_wfile0 m /\ ssp_cells m guard.

Definition stdio_regions : list (Z * Z) :=
  [(0xa9088, 0xa9380 - 0xa9088); (0x601208, 0x601620 - 0x601208); (0x600da0, 8); (0xa5638, 8); (0x600b50, 8)]%Z.

Lemma stdio_state_transport : forall W m m' so guard cdt thr sec tm1,
  stdio_state m so guard cdt thr sec tm1 -> munch W m m' -> wmono asegs m m' ->
  Forall (fun c => disjoint_from W (fst c) (snd c)) stdio_regions -> stdio_state m' so guard cdt thr sec tm1.
Proof.
  intros W m m' so guard cdt thr sec tm1 (STAT & SIN & SOF & SEF & SSP) MU WM D. unfold stdio_regions in D.
  apply Forall_cons_iff in D; destruct D as [D1 D]. apply Forall_cons_iff in D; destruct D as [D2 D].
  apply Forall_cons_iff in D; destruct D as [D3 D]. apply Forall_cons_iff in D; destruct D as [D4 D].
  apply Forall_cons_iff in D; destruct D as [D5 _]. cbn [fst snd] in *.
  assert (T : forall lo n A cs, rw_cells asegs m A cs -> disjoint_from W lo n -> lo <= A -> A + Z.of_nat (cells_size cs) <= lo + n ->
              rw_cells asegs m' A cs).
  { intros lo n A cs X HD X1 X2. eapply rw_cells_transport; [exact X | exact MU | exact WM |]. eapply disjoint_from_sub; [exact HD | lia | lia]. }
  pose proof (fun A cs X => T _ _ A cs X D1) as T1. pose proof (fun A cs X => T _ _ A cs X D2) as T2.
  pose proof (fun A cs X => T _ _ A cs X D3) as T3. pose proof (fun A cs X => T _ _ A cs X D4) as T4.
  pose proof (fun A cs X => T _ _ A cs X D5) as T5. cbv beta in T1, T2, T3, T4, T5.
  split; [|split; [|split; [|split]]].
  - destruct STAT as (L & O & I & U & E). unfold stdio_statics.
    split; [apply (T3 _ _ L); cbn; lia|]. split; [apply (T2 _ _ O); cbn; lia|].
    split; [apply (T1 _ _ I); cbn; lia|]. split; [apply (T1 _ _ U); cbn; lia| apply (T1 _ _ E); cbn; lia].
  - unfold stdin_file, stdin_cells in *. apply (T1 _ _ SIN); cbn; lia.
  - destruct SOF as (flags & mode & tail & bufb & FC & FL & BUF & R). exists flags, mode, tail, bufb.
    split; [| split; [exact FL | split; [| exact R]]].
    + unfold file_cells in *. apply (T1 _ _ FC); cbn; lia.
    + apply (T2 _ _ BUF); cbn; lia.
  - destruct SEF as (flags & mode & e & wend & tail & FC & R). exists flags, mode, e, wend, tail. split; [| exact R].
    unfold file_cells in *. apply (T1 _ _ FC); cbn; lia.
  - destruct SSP as [G1 G2]. unfold ssp_cells, got_ssp, ssp_guard in *. split; [apply (T4 _ _ G1); cbn; lia | apply (T5 _ _ G2); cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Lemma exit_spec : forall (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : mem) (lo code t : Z) (guard : word) (cdt thr sec : byte) (tm1 : word) (P : acc -> Prop)
      (reg : bool) (p3 p4 FJ AJ : list byte),
    (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x7fffc000 <= a -> a + Z.of_nat k <= 0x7fffd000 -> P (Z_to_bv 64 a, k)) ->
    (forall a k, 0x8000d065 <= a -> a + Z.of_nat k <= 0x8000e048 -> P (Z_to_bv 64 a, k)) ->
    (forall a, P (Z_to_bv 64 a, 0%nat)) ->
    stk asegs m lo (bv_unsigned sp) -> (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608) <= lo -> lo <= bv_unsigned sp - AEXIT_DEPTH ->
    (bv_unsigned sp < 0x800000000000) (* [comment removed for export] *) ->
    mem_inv asegs m ->
    exit_statics m t -> stdio_state m (get_so s) guard cdt thr sec tm1 ->
    rw_cells asegs m AATX (atx_cells reg p3 p4 FJ AJ) -> rw_cells asegs m 0x5e01d4 [C1 (Z_to_bv 8 0)] ->
    stk asegs m SHA_LO SHA_HI -> stk asegs m SHB_LO SHB_HI -> stk asegs m SHC_LO SHC_HI ->
    tp = Z_to_bv 64 0x5e0b10 -> a0 = Z_to_bv 64 code -> 0 <= code < 2^32 ->
    implMA asegs P (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 A_EXIT) fc None m (seg_rom asegs)).
  Proof.
    intros until AJ; intros PSTK PIMG PSHA PSHB PNUL ST LOC LO SPTS MI ES SS ATX FLG SA SB SC Htp Ha0 CODE.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof LO as LO'. unfold AEXIT_DEPTH in LO'.
    pose proof (munch_refl (EXW (bv_unsigned sp)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof SS as SS0. destruct SS as (STAT & SIN & SOF & SEF & SSP). pose proof STAT as STAT0. destruct STAT as (LIBC & _).
    unfold Driver.exit_model.
    eapply (implMA_bind asegs P _ _ s
              (fun _ _ ms' => exists gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0x91d7c) (Z_to_bv 64 (bv_unsigned sp + -16)) gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0x91d7c) fc None m' (seg_rom asegs))).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implMA_from_evtA.
      callA (aexit_prefix_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo code t cdt thr sec tm1 P reg p3 p4 FJ AJ);
        [ exact PSTK | exact PIMG | exact PSHA | exact PSHB | exact ST | exact LOC | exact LO | exact MI | exact ES | exact ATX | exact FLG | exact LIBC
        | exact SA | exact SB | exact SC | exact Htp | exact Ha0 | exact CODE | ].
      apply evtA_done.
      lazymatch goal with |- implMA _ _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with MUx : munch _ m mx, WMx : wmono asegs m mx |- _ =>
          pose proof (stdio_state_transport _ _ _ _ _ _ _ _ _ SS0 MUx WMx
                        ltac:(unfold stdio_regions; repeat (apply Forall_cons; [cbn [fst snd disjoint_from]; repeat split; lia|]); apply Forall_nil)) as SS1
        end end.
      destruct SS1 as (STAT1 & SIN1 & SOF1 & SEF1 & SSP1).
      name_sp sp (-16).
      lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -16), E : bv_unsigned _ = bv_unsigned sp + -16 |- _ => rewrite <- E in H end.
      eapply implMA_mono.
      { eapply (stdio_exit_proof get_so set_so get_set set_set set_get) with (lo := lo) (P := P);
          [ intros a k H1 H2; apply PSTK; lia | exact PIMG | exact PNUL | | exact STAT1 | exact SIN1 | exact SOF1 | exact (stderr_wfile0_file _ SEF1) | exact SSP1 | | lia | lia | lia ];
          eassumption. }
      cbv beta. intros [] st' ms' PO. unfold stdio_exit_post in PO. destruct_exs PO. destruct PO as (E & _). subst ms'.
      unname_sp.
      replace (ret_pc (Z_to_bv 64 0x91d7c)) with (Z_to_bv 64 0x91d7c : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
      repeat eexists.
    - (* [comment removed for export] *)
      intros [] s' ms' PO. destruct_exs PO. subst ms'.
      apply implMA_sys. stepA. stepA. zstepA. zstepA. step_ecallA.
      split; [ at_nodeA_solve; right; reflexivity | intros rsp a H; cbn in H; discriminate H].
  Qed.
End ExitProof.
End RC__2.
