(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import AsanUbsan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS SeamA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface RDriverA_kit RDriverA_ctx.
Import ListNotations.
Open Scope Z_scope.

Section Statics.
  Variables (sp0 : word) (argv envp : list (list byte)) (t : Z).
  Notation usp0 := (bv_unsigned sp0).

  Definition EXITC (mm : mem) : Prop :=
    rw_cells asegs mm 0x5e7508 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs mm 0x607820 [C4 z64]

    /\ (exists (p3 p4 : list byte),
          rw_cells asegs mm 0x607600 [C1 (Z_to_bv 8 0); CB 3 p3; C4 z64; C4 (Z_to_bv 64 1); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 0x95694); C8 z64])
    /\ rw_cells asegs mm 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 z64]
    /\ rw_cells asegs mm 0x1463e0 [C1 (Z_to_bv 8 0)]
    /\ (exists (cdt thr sec : byte) (tm1 : word),
          rw_cells asegs mm 0x607840 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells asegs mm 0xab9f8 [C8 (Z_to_bv 64 0xaa750); C8 (Z_to_bv 64 0xaa740)]
    /\ rw_cells asegs mm 0xaa740 [C8 (Z_to_bv 64 0x8ba48); C8 (Z_to_bv 64 0x324b8)]
    /\ rw_cells asegs mm 0xaad00 [C8 (Z_to_bv 64 0x955cc); C8 z64]
    /\ (exists dso : bv 64, rw_cells asegs mm 0xaca40 [C8 dso])
    /\ rw_cells asegs mm 0x607ca8 [C8 z64]
    /\ rw_cells asegs mm 0xaf9f0 [C8 (Z_to_bv 64 0xaf908)]
    /\ rw_cells asegs mm 0xaf900 [C8 (Z_to_bv 64 0xaf818)]
    /\ rw_cells asegs mm 0xaf810 [C8 (Z_to_bv 64 0xaf728)].

  Definition exitc_addr (a : Z) : Prop :=
    (0x5e7508 <= a < 0x5e750c) \/ (0x607820 <= a < 0x607824) \/ (0x607600 <= a < 0x607630) \/ (0x607720 <= a < 0x607730)
    \/ (0x1463e0 <= a < 0x1463e1) \/ (0x607840 <= a < 0x607848)
    \/ (0xab9f8 <= a < 0xaba08) \/ (0xaa740 <= a < 0xaa750) \/ (0xaad00 <= a < 0xaad10)
    \/ (0xaca40 <= a < 0xaca48) \/ (0x607ca8 <= a < 0x607cb0) \/ (0xaf9f0 <= a < 0xafa20) \/ (0xaf900 <= a < 0xaf908)
    \/ (0xaf810 <= a < 0xaf818).

  Ltac tr AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold exitc_addr; cbn in Ha; lia].

  #[using="Type"] Lemma EXITC_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, exitc_addr a -> P a) -> EXITC m -> EXITC m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & (p3 & p4 & A3) & A3b & A3c & (cdt & thr & sec & tm1 & A4) & A5 & A6 & A8 & (dso & A9) & A10 & A11 & A12 & A13).
    unfold EXITC.
    split; [tr AG HP A1|]. split; [tr AG HP A2|]. split; [exists p3, p4; tr AG HP A3|]. split; [tr AG HP A3b|]. split; [tr AG HP A3c|].
    split; [exists cdt, thr, sec, tm1; tr AG HP A4|].
    split; [tr AG HP A5|]. split; [tr AG HP A6|]. split; [tr AG HP A8|].
    split; [exists dso; tr AG HP A9|]. split; [tr AG HP A10|]. split; [tr AG HP A11|]. split; [tr AG HP A12| tr AG HP A13].
  Qed.

  #[using="Type"] Lemma EXITC_munch : forall W m m', munch W m m' -> wmono asegs m m' -> (forall a, exitc_addr a -> outside W a) -> EXITC m -> EXITC m'.
  Proof.
    intros W m m' MU WM HW. apply (EXITC_agree _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.

  Definition EXITC2 (mm : mem) : Prop :=
    rw_cells asegs mm 0x5e7508 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs mm 0x607820 [C4 z64]
    /\ (exists (p3 p4 : list byte),
          rw_cells asegs mm 0x607600 [C1 (Z_to_bv 8 0); CB 3 p3; C4 z64; C4 (Z_to_bv 64 2); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 0x95694); C8 (Z_to_bv 64 0x95694)])
    /\ rw_cells asegs mm 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 (Z_to_bv 64 0x86484)]
    /\ rw_cells asegs mm 0x1463e0 [C1 (Z_to_bv 8 0)]
    /\ (exists (cdt thr sec : byte) (tm1 : word),
          rw_cells asegs mm 0x607840 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1])
    /\ rw_cells asegs mm 0xab9f8 [C8 (Z_to_bv 64 0xaa750); C8 (Z_to_bv 64 0xaa740)]
    /\ rw_cells asegs mm 0xaa740 [C8 (Z_to_bv 64 0x8ba48); C8 (Z_to_bv 64 0x324b8)]
    /\ rw_cells asegs mm 0xaad00 [C8 (Z_to_bv 64 0x955cc); C8 z64]
    /\ (exists dso : bv 64, rw_cells asegs mm 0xaca40 [C8 dso])
    /\ rw_cells asegs mm 0x607ca8 [C8 z64]
    /\ rw_cells asegs mm 0xaf9f0 [C8 (Z_to_bv 64 0xaf908)]
    /\ rw_cells asegs mm 0xaf900 [C8 (Z_to_bv 64 0xaf818)]
    /\ rw_cells asegs mm 0xaf810 [C8 (Z_to_bv 64 0xaf728)]
    /\ rw_cells asegs mm 0x5e6b94 [C1 (Z_to_bv 8 0)].

  Definition exitc2_addr (a : Z) : Prop :=
    exitc_addr a \/ (0x5e6b94 <= a < 0x5e6b95).

  Ltac tr2 AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold exitc2_addr, exitc_addr; cbn in Ha; lia].

  #[using="Type"] Lemma EXITC2_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, exitc2_addr a -> P a) -> EXITC2 m -> EXITC2 m'.
  Proof.
    intros P m m' AG HP (A1 & A2 & (p3 & p4 & A3) & A3b & A3c & (cdt & thr & sec & tm1 & A4) & A5 & A6 & A8 & (dso & A9) & A10 & A11 & A12 & A13 & A14).
    unfold EXITC2.
    split; [tr2 AG HP A1|]. split; [tr2 AG HP A2|]. split; [exists p3, p4; tr2 AG HP A3|]. split; [tr2 AG HP A3b|]. split; [tr2 AG HP A3c|].
    split; [exists cdt, thr, sec, tm1; tr2 AG HP A4|].
    split; [tr2 AG HP A5|]. split; [tr2 AG HP A6|]. split; [tr2 AG HP A8|].
    split; [exists dso; tr2 AG HP A9|]. split; [tr2 AG HP A10|]. split; [tr2 AG HP A11|]. split; [tr2 AG HP A12|]. split; [tr2 AG HP A13| tr2 AG HP A14].
  Qed.

  #[using="Type"] Lemma EXITC2_munch : forall W m m', munch W m m' -> wmono asegs m m' -> (forall a, exitc2_addr a -> outside W a) -> EXITC2 m -> EXITC2 m'.
  Proof.
    intros W m m' MU WM HW. apply (EXITC2_agree _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.

  #[using="Type"] Lemma crt_cell_any : forall mm, wr_at asegs mm 0xb0ed0 1 -> exists b, rw_cells asegs mm 0xb0ed0 [C1 b].
  Proof.
    intros mm W. exists (match mm (wa 0xb0ed0) with Some b => b | None => Z_to_bv 8 0 end).
    split; [| exact W]. split; [cbn; repeat split; exact I|].
    split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. destruct i; [| lia]. cbn [nth_error cells_bytes cbytes app le1].
    rewrite Z.add_0_r. unfold mrd. destruct (mm (wa 724688)) as [b|] eqn:E; [reflexivity|]. vm_compute. reflexivity.
  Qed.

  Definition MAINC (guard : word) (mm : mem) : Prop :=
    rw_cells asegs mm 0xab990 [C8 (Z_to_bv 64 0xaac28); C8 z64]
    /\ rw_cells asegs mm 0xaac28 [C8 (Z_to_bv 64 0xaf728)]
    /\ ssp_cells mm guard
    /\ rw_cells asegs mm 0x5e6b90 [C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3); C1 (Z_to_bv 8 0)]
    /\ rw_cells asegs mm 0x5e6ba0 [CB 16 (repeat (Z_to_bv 8 0) 16)].

  Definition mainc_addr (a : Z) : Prop :=
    (0xab990 <= a < 0xab9a0) \/ (0xaac28 <= a < 0xaac30) \/ (0xab9c8 <= a < 0xab9d0) \/ (0x6075f0 <= a < 0x6075f8)
    \/ (0x5e6b90 <= a < 0x5e6b95) \/ (0x5e6ba0 <= a < 0x5e6bb0).

  #[using="Type"] Lemma MAINC_agree : forall guard (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, mainc_addr a -> P a) -> MAINC guard m -> MAINC guard m'.
  Proof.
    intros guard P m m' AG HP (A1 & A2 & [G1 G2] & A4 & A5). unfold MAINC, ssp_cells, got_ssp, ssp_guard in *.
    Ltac trm AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold mainc_addr; cbn in Ha; lia].
    split; [trm AG HP A1|]. split; [trm AG HP A2|]. split; [split; [trm AG HP G1| trm AG HP G2]|]. split; [trm AG HP A4| trm AG HP A5].
  Qed.

  #[using="Type"] Lemma MAINC_munch : forall guard W m m', munch W m m' -> wmono asegs m m' -> (forall a, mainc_addr a -> outside W a) -> MAINC guard m -> MAINC guard m'.
  Proof.
    intros guard W m m' MU WM HW. apply (MAINC_agree guard _ _ _ (gagree_on_of_munch _ _ _ MU WM)). intros a Ha. cbn. apply HW. exact Ha.
  Qed.
End Statics.

Section Windows.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).

  Definition SHZ (mm : mem) : Prop :=
    (shz mm (sh 0x10000) (sh 0x213e0) /\ shr mm (sh 0x10000) (sh 0x213e0 + 8))
    /\ (shz mm (sh 0x5d6b80) (sh 0x5e6bc0) /\ shr mm (sh 0x5d6b80 - 8) (sh 0x5e6bc0 + 8))
    /\ (shz mm (sh 0x607c00) (sh 0x6080c0) /\ shr mm (sh 0x607c00 - 8) (sh 0x6080c0 + 8))
    /\ (shz mm (sh alloc_ceiling) (Z.min (sh (usp0 + Z.of_nat (length IMGB)) + 1) SH_HI)
        /\ shr mm (sh alloc_ceiling - sh alloc_ceiling mod 8) (Z.min (sh (usp0 + Z.of_nat (length IMGB)) + 8) SH_HI)).

  #[using="Type"] Lemma SHZ_frame : forall W m m', SHZ m -> munch W m m' -> app_ivs W -> SHZ m'.
  Proof.
    intros W m m' ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]) MU AW.
    pose proof alloc_ceiling_bounds as CR.
    split; [| split; [| split]]; split;
      first [ eapply shz_frame; [eassumption| | | exact MU| exact AW] | eapply shr_frame; [eassumption| | | exact MU| exact AW] ];
      unfold SH_LO, SH_HI, sh, SHADOW_OFF in *; try lia.
    all: try apply Z.le_min_r. all: Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma SHZ_ro : forall m, SHZ m -> shw m 0x10000 0x113e0.
  Proof.
    intros m ([Z1 R1] & _). eapply shw_of_shz_shr; [exact Z1 | exact R1 | split; [lia| left; lia] | lia | | |];
      unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
  Qed.
  #[using="Type"] Lemma SHZ_stdout_buf : forall m, SHZ m -> shw m 0x607cc0 1024.
  Proof.
    intros m (_ & _ & [Z3 R3] & _). eapply shw_of_shz_shr; [exact Z3 | exact R3 | split; [lia| left; lia] | | | |];
      unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
  Qed.
  #[using="Type"] Lemma SHZ_cli : forall m A n, SHZ m -> 0x5d6b80 <= A -> A + n <= 0x5e6bc0 -> 0 <= n -> shw m A n.
  Proof.
    intros m A n (_ & [Z2 R2] & _) H1 H2 H3. eapply shw_of_shz_shr; [exact Z2 | exact R2 | split; [lia| left; lia] | | | |];
      unfold sh, SHADOW_OFF; Z.div_mod_to_equations; lia.
  Qed.

  #[using="Type"] Lemma SHZ_stack : forall m A n, SHZ m -> alloc_ceiling <= A -> A + n <= usp0 + Z.of_nat (length IMGB) -> A + n <= 2^47 -> 0 <= n ->
    shw m A n.
  Proof.
    intros m A n (_ & _ & _ & [Z4 R4]) H1 H2 H3 H4. pose proof alloc_ceiling_bounds as CR.
    eapply shw_of_shz_shr; [exact Z4 | exact R4 | split; [lia| right; lia] | | | |];
      unfold sh, SHADOW_OFF, SH_HI in *.
    - Z.div_mod_to_equations; lia.
    - apply Z.min_glb; Z.div_mod_to_equations; lia.
    - Z.div_mod_to_equations; lia.
    - apply Z.min_glb; Z.div_mod_to_equations; lia.
  Qed.
End Windows.

Section AtMainA.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.

  Variable PZ : mem -> Prop.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw).
  Notation usp0 := (bv_unsigned sp0).
  Notation IMGB := (build_stack_bytes rph sp0 argv envp uid hw rnd).

  Definition rat_mainA (msr : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
           (t : Z) (e0 : word) (m : mem) (s : aps FI AI) (st : fsstate FI),
      msr = MS (mkR (Z_to_bv 64 0x94fe8) (Z_to_bv 64 (usp0 + -48)) (Z_to_bv 64 0x10800) (Z_to_bv 64 RATPA)
                   t0 t1 t2 (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (argc argv))
                   (Z_to_bv 64 (argc argv)) (Z_to_bv 64 (usp0 + 8)) (Z_to_bv 64 (envp_addr sp0 argv)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 0x8605c) (Z_to_bv 64 (envp_addr sp0 argv)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x8605c) fc None m (seg_rom asegs)
      /\ frm0 fc

      /\ mem_inv asegs m
      /\ stk asegs m (usp0 - 8388608) (usp0 + -48)
      /\ rw_cells asegs m 0x5e750c [C4 e0]
      /\ EXITC t m /\ 0 < t < 2^31 /\ wr_at asegs m 0xb0ed0 1
      /\ MAINC guard_word m
      /\ stdout_file m stdout_init /\ stderr_wfile0 m /\ stdin_file m
      /\ stk asegs m RSVA (RSVA + 65536)
      /\ IMGK sp0 argv envp uid hw rnd m

      /\ RHEAP_A FI AI s [] m /\ RFAKE FI st m /\ asan_env asegs m /\ g = gh FI AI s
      /\ fs_live FI st = [] /\ am_nsec FI AI s = 0

      /\ SHZ sp0 argv envp uid hw rnd m

      /\ globals_shadow m /\ PZ m.
End AtMainA.
