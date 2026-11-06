(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import ITree Nodes Decode SysStep.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import F_fmt_fp_lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg F_syscalls StdioFiles Stdio_kit MonadF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import StrwF SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import LiaTier0U.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RSTDIN : Z := 0x10bba0.
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xf4650); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0xf467c); C8 z64; C8 (Z_to_bv 64 0xf4794); C8 (Z_to_bv 64 0x663988); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

(* [comment removed for export] *)
Section StdioExitStatement2.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Definition stdio_exit_spec_stmt2 : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk asegs m lo (bv_unsigned sp) ->
      rw_cells asegs m 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells asegs m 0x663568 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells asegs m 0x10bc88 [C8 (Z_to_bv 64 RSTDIN)] ->                           (* [comment removed for export] *)
      rw_cells asegs m RSTDIN stdin_cells ->                                           (* [comment removed for export] *)
      rw_cells asegs m 0x10bb98 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells asegs m 0x10baa8 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->   (* [comment removed for export] *)
      mem_inv asegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
      (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
      implAM RNG (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xf4d7c) fc None m (seg_rom asegs)).
End StdioExitStatement2.

(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells asegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells asegs _ (Zpos ?p') _ |- _ =>
                     lazymatch eval vm_compute in (Z.ltb (Zpos p') (Zpos p)) with true => idtac | false => fail end end)
            then fail
            else (move H at bottom; lazymatch type of H with ?T => change T with (sf_hide T) in H end)
          end); sf_unhide.
Ltac hstep := sort_lits; zstep; fix_lit_store.
(* [comment removed for export] *)
Ltac hyp_by_addr :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- bytes_at _ _ ?A _ => match goal with H : bytes_at _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.
Ltac astep := hstep; try (first [if_true | if_false]).
Ltac at_pc p := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?q) _ _ _ _) => constr_eq q p end.
Ltac steps_to p := repeat (tryif at_pc p then fail else astep).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma a_Exit_specM : forall {St : Type} RNG (s : St) (code : Z) (Q : Empty_set -> St -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 code ->
  implAM RNG (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xeec24) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros MI ->.
  apply implAM_sys; [exact I|]. do 2 zstep. step_ecall.
  split; [ at_nodeA_solve | intros rsp a H; cbn in H; discriminate H ].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MDTOR_DEPTH : Z := 1024.
(* [comment removed for export] *)
Definition MDTOR_W : list (Z * Z) :=
  [(0x10c440, 0x10c448); (0x10d3b0, 0x10d3b8); (0x642320, 0x64232a);
   (0x7fffc5d8, 0x7fffd5fc); (0x800187d0, 0x80018800); (0x800c0430, 0x800c0464); (0x80019798, 0x80019888)]%Z.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0x10c440, 0x10c448); (0x10d3b0, 0x10d3b8); (0x642320, 0x64232a);
              (0x7fffc5d8, 0x7fffd5fc); (0x800187d0, 0x80018800); (0x800c0430, 0x800c0464); (0x80019798, 0x80019888)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv asegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF asegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x96608) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x6630e0, 0x6630e4); (0x662ec0, 0x662ec1); (0x662ec8, 0x662ecc); (0x662ed0, 0x662ed8); (0x10c490, 0x10c491)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.

(* [comment removed for export] *)
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0xeeec0) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xf4d7c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x6630e0, 0x6630e4); (0x662ec0, 0x662ec1); (0x662ec8, 0x662ecc);
              (0x662ed0, 0x662ed8); (0x10c490, 0x10c491);
              (0x10c440, 0x10c448); (0x10d3b0, 0x10d3b8); (0x642320, 0x64232a);
              (0x7fffc5d8, 0x7fffd5fc); (0x800187d0, 0x80018800); (0x800c0430, 0x800c0464); (0x80019798, 0x80019888)]%Z m m'
                                                                  (* [comment removed for export] *)
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells asegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells asegs m' 0x642dc8 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0x6630e0 [C4 (Z_to_bv 64 t)]
    /\ rw_cells asegs m' 0x10c490 [C1 (Z_to_bv 8 1)].

Section Prefix.
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.

  Lemma aexit_prefix_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x642dc8 [C4 (Z_to_bv 64 t)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x6630e0 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    rw_cells asegs m 0x662ec0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x662ec4 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x662ec8 [C4 (Z_to_bv 64 1)] ->                                  (* [comment removed for export] *)
    rw_cells asegs m 0x662ed0 [C8 (Z_to_bv 64 0x662ed8)] ->                           (* [comment removed for export] *)
    rw_cells asegs m 0x662ed8 [C8 z64] ->                                             (* [comment removed for export] *)
    rw_cells asegs m 0x662ee0 [C8 (Z_to_bv 64 0xeee00)] ->                           (* [comment removed for export] *)
    rw_cells asegs m 0x662fe0 [C8 (Z_to_bv 64 0x84e1c)] ->                            (* [comment removed for export] *)
    rw_cells asegs m 0x1a19a0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x108080 [C8 (Z_to_bv 64 0x103a98); C8 (Z_to_bv 64 0x103a88)] -> (* [comment removed for export] *)
    rw_cells asegs m 0x103a88 [C8 (Z_to_bv 64 0x96608); C8 (Z_to_bv 64 0x43cfc)] ->  (* [comment removed for export] *)
    rw_cells asegs m 0x10c490 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells asegs m 0x1072d0 [C8 (Z_to_bv 64 0xeed38); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells asegs m 0x1090c0 [C8 dso] ->                                             (* [comment removed for export] *)
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF asegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xeee54) fc None m (seg_rom asegs)).
  Proof.
    intros until dso. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 A0 COV GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. unfold KHIGH in KH.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    (* [comment removed for export] *)
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    astep. sort_lits. amo_step. astep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
    hstep. hstep.
    (* [comment removed for export] *)
    carve_frame 48%nat ST.
    steps_to 0xfdad0%Z.
    (* [comment removed for export] *)
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x43cfc%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0xeed38%Z. hstep.
    steps_to 0x43d88%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep.
    match goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH, KHIGH; lia) MU WM) as HPRE1;
      assert (MU2 : munch (AEXIT_W (bv_unsigned sp)) m mc)
        by (eapply munch_weaken; [| exact MU]; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH, sub_fp; cbn [outside app]; intros; lia);
      clear MU; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH in MU2; cbn [app] in MU2
    end.
    call_sp (MDTOR RNG); try first [ exact HPRE1 | eassumption | unfold MDTOR_DEPTH; lia | unfold KHIGH; lia | exact RW ].
    1:{ eapply rng_sub'; [exact RSTK | lia]. }
    (* [comment removed for export] *)
    astep. astep. hstep. hstep. hstep. hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
    hstep. hstep.
    hstep.
    unfold aexit_prefix_post. sys_finish.
  Qed.

  Lemma aexit_prefix_spec2 : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x642dc8 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x6630e0 [C4 z64] ->
    rw_cells asegs m 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0x662ec0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x662ec4 [C4 z64] ->
    rw_cells asegs m 0x662ec8 [C4 (Z_to_bv 64 2)] ->
    rw_cells asegs m 0x662ed0 [C8 (Z_to_bv 64 0x662ed8)] ->
    rw_cells asegs m 0x662ed8 [C8 z64] ->
    rw_cells asegs m 0x662ee0 [C8 (Z_to_bv 64 0xeee00)] ->
    rw_cells asegs m 0x662ee8 [C8 (Z_to_bv 64 0xeee00)] ->
    rw_cells asegs m 0x662fe0 [C8 (Z_to_bv 64 0x84e1c)] ->
    rw_cells asegs m 0x662fe8 [C8 (Z_to_bv 64 0x957e4)] ->
    rw_cells asegs m 0x642154 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x1a19a0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x108080 [C8 (Z_to_bv 64 0x103a98); C8 (Z_to_bv 64 0x103a88)] ->
    rw_cells asegs m 0x103a88 [C8 (Z_to_bv 64 0x96608); C8 (Z_to_bv 64 0x43cfc)] ->
    rw_cells asegs m 0x10c490 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x1072d0 [C8 (Z_to_bv 64 0xeed38); C8 z64] ->
    rw_cells asegs m 0x1090c0 [C8 dso] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF asegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xeee54) fc None m (seg_rom asegs)).
  Proof.
    intros until dso. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 F1 A0 A1 INH COV GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. unfold KHIGH in KH.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    do 6 hstep.
    replace (sx32 (Z_to_bv 64 t)) with (Z_to_bv 64 t)
      by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
    hstep. hstep.
    sort_lits. amo_step. replace (sx32 z64) with z64 by (vm_compute; reflexivity).
    astep. sort_lits. amo_step. astep.
    hstep. change (bv_swrap 32 (0 + 0)) with 0%Z.
    hstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K. astep.
    hstep. hstep.
    carve_frame 48%nat ST.
    steps_to 0xfdad0%Z.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_false. hstep.
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    hstep. hstep. hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (0 + -1)%Z with (-1)%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    release_frame FR0 ST (bv_unsigned sp + -16)%Z.
    hstep. carve_frame 32%nat ST.
    steps_to 0x43cfc%Z.
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0xeed38%Z. hstep.
    steps_to 0x43d88%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
    astep. astep. hstep. hstep. hstep.
    match goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mc _) =>
      pose proof (PRE_frame (bv_unsigned sp) m mc HPRE ltac:(unfold MDTOR_DEPTH, KHIGH; lia) MU WM) as HPRE1;
      assert (MU2 : munch (AEXIT_W (bv_unsigned sp)) m mc)
        by (eapply munch_weaken; [| exact MU]; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH, sub_fp; cbn [outside app]; intros; lia);
      clear MU; unfold AEXIT_W, AEXIT_W1, MDTOR_W, MDTOR_DEPTH in MU2; cbn [app] in MU2
    end.
    call_sp (MDTOR RNG); try first [ exact HPRE1 | eassumption | unfold MDTOR_DEPTH; lia | unfold KHIGH; lia | exact RW ].
    1:{ eapply rng_sub'; [exact RSTK | lia]. }
    astep. astep. hstep. hstep. hstep. hstep.
    match goal with H : rw_cells _ _ (bv_unsigned sp + -48)%Z _, S : stk _ _ lo _ |- _ => release_frame H S (bv_unsigned sp + -16)%Z end.
    hstep. hstep.
    hstep.
    unfold aexit_prefix_post. sys_finish.
  Qed.
End Prefix.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono asegs m m' -> PRE m'.
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.     (* [comment removed for export] *)

  Lemma aexit_spec : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x642dc8 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x6630e0 [C4 z64] ->
    rw_cells asegs m 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0x662ec0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x662ec4 [C4 z64] ->
    rw_cells asegs m 0x662ec8 [C4 (Z_to_bv 64 1)] ->
    rw_cells asegs m 0x662ed0 [C8 (Z_to_bv 64 0x662ed8)] ->
    rw_cells asegs m 0x662ed8 [C8 z64] ->
    rw_cells asegs m 0x662ee0 [C8 (Z_to_bv 64 0xeee00)] ->
    rw_cells asegs m 0x662fe0 [C8 (Z_to_bv 64 0x84e1c)] ->
    rw_cells asegs m 0x1a19a0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x108080 [C8 (Z_to_bv 64 0x103a98); C8 (Z_to_bv 64 0x103a88)] ->
    rw_cells asegs m 0x103a88 [C8 (Z_to_bv 64 0x96608); C8 (Z_to_bv 64 0x43cfc)] ->
    rw_cells asegs m 0x10c490 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x1072d0 [C8 (Z_to_bv 64 0xeed38); C8 z64] ->
    rw_cells asegs m 0x1090c0 [C8 dso] ->
    (* [comment removed for export] *)
    rw_cells asegs m 0x663568 [C8 z64] -> rw_cells asegs m 0x10bc88 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
    rw_cells asegs m 0x10bb98 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x10baa8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xeee54) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 A0 COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO KH RSTK RIMG RW RG0 SP47.
    pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    eapply (implAM_bind RNG _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0xeeec0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0xeeec0) fc None m' (seg_rom asegs) /\ mem_inv asegs m')).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implAM_from_evt.
      call (aexit_prefix_spec PRE MDTOR PRE_frame RNG);
        try first [ exact HPRE | eassumption | reflexivity | unfold MDTOR_DEPTH; lia | exact KH | exact RW ].
      all: try (lazymatch goal with |- rng _ _ _ => first [exact RSTK | exact RIMG] end).
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt2, got_ssp, ssp_guard, GLOBALS_TOP, RSTDIN, stdin_cells in SE.
      apply evtF_done. eapply implAM_mono; [eapply (SE RNG)|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [] s' ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0xeeec0)) with (Z_to_bv 64 0xeeec0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               do 30 eexists; split; [cbv delta [mkR]; reflexivity | destruct PO as (_ & _ & MIq & _); exact MIq]
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- rng _ _ _ => unname_sp; first [ eapply rng_sub'; [exact RSTK | lia] | exact RIMG ]
           | |- rng0 _ => exact RG0
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia | assumption ]
           end.
    - (* [comment removed for export] *)
      clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. destruct PO as [-> MI']. 
      apply implAM_from_evt. zstep. zstep. apply evtF_done.
      apply a_Exit_specM; [exact MI' | reflexivity].
  Qed.

  Lemma aexit_spec2 : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (cdt thr sec : byte) (tm1 dso guard : word),
    PRE m ->
    stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m 0x642dc8 [C4 (Z_to_bv 64 t)] ->
    rw_cells asegs m 0x6630e0 [C4 z64] ->
    rw_cells asegs m 0x663100 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells asegs m 0x662ec0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x662ec4 [C4 z64] ->
    rw_cells asegs m 0x662ec8 [C4 (Z_to_bv 64 2)] ->
    rw_cells asegs m 0x662ed0 [C8 (Z_to_bv 64 0x662ed8)] ->
    rw_cells asegs m 0x662ed8 [C8 z64] ->
    rw_cells asegs m 0x662ee0 [C8 (Z_to_bv 64 0xeee00)] ->
    rw_cells asegs m 0x662ee8 [C8 (Z_to_bv 64 0xeee00)] ->
    rw_cells asegs m 0x662fe0 [C8 (Z_to_bv 64 0x84e1c)] ->
    rw_cells asegs m 0x662fe8 [C8 (Z_to_bv 64 0x957e4)] ->
    rw_cells asegs m 0x642154 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x1a19a0 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x108080 [C8 (Z_to_bv 64 0x103a98); C8 (Z_to_bv 64 0x103a88)] ->
    rw_cells asegs m 0x103a88 [C8 (Z_to_bv 64 0x96608); C8 (Z_to_bv 64 0x43cfc)] ->
    rw_cells asegs m 0x10c490 [C1 (Z_to_bv 8 0)] ->
    rw_cells asegs m 0x1072d0 [C8 (Z_to_bv 64 0xeed38); C8 z64] ->
    rw_cells asegs m 0x1090c0 [C8 dso] ->
    rw_cells asegs m 0x663568 [C8 z64] -> rw_cells asegs m 0x10bc88 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells asegs m RSTDIN stdin_cells ->
    rw_cells asegs m 0x10bb98 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells asegs m 0x10baa8 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 guard] ->
    mem_inv asegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    (bv_unsigned sp < 2^47)%Z ->
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xeee54) fc None m (seg_rom asegs)).
  Proof.
    intros until guard. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 F1 A0 A1 INH COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO KH RSTK RIMG RW RG0 SP47.
    pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    eapply (implAM_bind RNG _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0xeeec0) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0xeeec0) fc None m' (seg_rom asegs) /\ mem_inv asegs m')).
    - change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implAM_from_evt.
      call (aexit_prefix_spec2 PRE MDTOR PRE_frame RNG);
        try first [ exact HPRE | eassumption | reflexivity | unfold MDTOR_DEPTH; lia | exact KH | exact RW ].
      all: try (lazymatch goal with |- rng _ _ _ => first [exact RSTK | exact RIMG] end).
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt2, got_ssp, ssp_guard, GLOBALS_TOP, RSTDIN, stdin_cells in SE.
      apply evtF_done. eapply implAM_mono; [eapply (SE RNG)|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [] s' ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0xeeec0)) with (Z_to_bv 64 0xeeec0) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
               do 30 eexists; split; [cbv delta [mkR]; reflexivity | destruct PO as (_ & _ & MIq & _); exact MIq]
           | |- stdout_file _ _ => exists flg, mode, tail, bufb; exact (conj SOF1 (conj SOF2 (conj SOF3 (conj SOF4 (conj SOF5 SOF6)))))
           | |- stderr_file _ => exists flg', mode', ee, wend', tail'; exact SEF1
           | |- rng _ _ _ => unname_sp; first [ eapply rng_sub'; [exact RSTK | lia] | exact RIMG ]
           | |- rng0 _ => exact RG0
           | |- _ => unname_sp; first [ hyp_by_addr | reflexivity | lia | assumption ]
           end.
    - clear SOF1 SOF2 SOF3 SOF4 SOF5 SOF6 SEF1.
      intros [] s' ms' PO. destruct_exs PO. destruct PO as [-> MI'].
      apply implAM_from_evt. zstep. zstep. apply evtF_done.
      apply a_Exit_specM; [exact MI' | reflexivity].
  Qed.
End ExitProof.
End CANSEC2.
