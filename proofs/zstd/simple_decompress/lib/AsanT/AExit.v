(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad Stdio Driver.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import Shadow ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import F_fmt_fp_lib.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg F_syscalls StdioFiles Stdio_kit MonadF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StrwF SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition RSTDIN : Z := 0xcbae8.
Definition stdin_cells : list cell :=
  [C4 (Z_to_bv 64 9); C4 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 0xbc1e8); C8 z64; C8 z64; C8 z64; C8 z64;
   C8 (Z_to_bv 64 0xbc214); C8 z64; C8 (Z_to_bv 64 0xbc32c); C8 (Z_to_bv 64 0x6237c8); C8 (Z_to_bv 64 1024); C8 z64; C8 z64;
   C4 z64; C4 z64; C8 z64; C4 z64; C4 (Z_to_bv 64 0xffffffff)].

(* [comment removed for export] *)
Section StdioExitStatement2.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Definition stdio_exit_spec_stmt2 : Prop :=
    forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (s : St) (guard : word)
           (cdt thr sec : byte) (tm1 : word),
      stk bsegs m lo (bv_unsigned sp) ->
      rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->   (* [comment removed for export] *)
      rw_cells bsegs m 0x6233a8 [C8 z64] ->                                            (* [comment removed for export] *)
      rw_cells bsegs m 0xcbbd0 [C8 (Z_to_bv 64 RSTDIN)] ->                           (* [comment removed for export] *)
      rw_cells bsegs m RSTDIN stdin_cells ->                                           (* [comment removed for export] *)
      rw_cells bsegs m 0xcbae0 [C8 (Z_to_bv 64 RSTDOUT)] ->                          (* [comment removed for export] *)
      rw_cells bsegs m 0xcb9f0 [C8 (Z_to_bv 64 RSTDERR)] ->                          (* [comment removed for export] *)
      stdout_file m (get_so s) -> stderr_file m ->
      rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->   (* [comment removed for export] *)
      mem_inv bsegs m ->
      tp = Z_to_bv 64 RTP ->
      (lo <= bv_unsigned sp - 160)%Z -> (GLOBALS_TOP <= lo)%Z ->
      rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> rng0 RNG ->
      (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
      implAM RNG (stdout_exit_flush get_so set_so) s
            (stdio_exit_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
            (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0xbc914) fc None m (seg_rom bsegs)).
End StdioExitStatement2.

(* [comment removed for export] *)
End CANSEC1.
Ltac sort_lits :=
  repeat (match goal with H : rw_cells bsegs _ (Zpos ?p) _ |- _ =>
            tryif (match goal with H' : rw_cells bsegs _ (Zpos ?p') _ |- _ =>
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
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 code ->
  implAM RNG (msys (NExit code) dec_exit) s Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0xb6bf4) fc None m (seg_rom bsegs)).
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
  [(0xcc640, 0xcc648); (0xcd5b0, 0xcd5b8); (0x7fffc220, 0x7fffc534); (0x800b8470, 0x800b8474); (0x80011780, 0x800118c8)]%Z.

Definition module_dtor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 1024, bv_unsigned sp); (0xcc640, 0xcc648); (0xcd5b0, 0xcd5b8);
              (0x7fffc220, 0x7fffc534); (0x800b8470, 0x800b8474); (0x80011780, 0x800118c8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition module_dtor_stmt (PRE : mem -> Prop) : Prop :=
  forall RNG (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - MDTOR_DEPTH) -> (KHIGH <= lo) ->
    mem_inv bsegs m ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF bsegs RNG (module_dtor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x82c6c) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AEXIT_W1 (sp : Z) : list (Z * Z) :=
  [(sp - 48 - MDTOR_DEPTH, sp); (0x622f20, 0x622f24); (0x622d00, 0x622d01); (0x622d08, 0x622d0c); (0x622d10, 0x622d18); (0xcc690, 0xcc691)]%Z.
Definition AEXIT_W (sp : Z) : list (Z * Z) := AEXIT_W1 sp ++ MDTOR_W.

(* [comment removed for export] *)
Definition aexit_prefix_post (sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo code t : Z) (ra : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0xb6e90) (Z_to_bv 64 (bv_unsigned sp + -16)) gp (Z_to_bv 64 RTP) t0 t1 t2 (Z_to_bv 64 code) s1
                 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xbc914) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48 - 1024, bv_unsigned sp); (0x622f20, 0x622f24); (0x622d00, 0x622d01); (0x622d08, 0x622d0c);
              (0x622d10, 0x622d18); (0xcc690, 0xcc691);
              (0xcc640, 0xcc648); (0xcd5b0, 0xcd5b8); (0x7fffc220, 0x7fffc534); (0x800b8470, 0x800b8474); (0x80011780, 0x800118c8)]%Z m m'
                                                                  (* [comment removed for export] *)
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -16)
    /\ rw_cells bsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra]
    /\ rw_cells bsegs m' 0x602c08 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m' 0x622f20 [C4 (Z_to_bv 64 t)]
    /\ rw_cells bsegs m' 0xcc690 [C1 (Z_to_bv 8 1)].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition foe_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (0x622d00, 0x622d01); (0x622d08, 0x622d0c); (0x622d10, 0x622d18)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x622d00 [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' 0x622d08 [C4 (Z_to_bv 64 32)]
    /\ rw_cells bsegs m' 0x622d10 [C8 z64].

Lemma funcs_on_exit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo : Z) (reg : bool) (cdt thr sec : byte) (tm1 : word),
  stk bsegs m lo (bv_unsigned sp) ->
  rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
  rw_cells bsegs m 0x622d00 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  rw_cells bsegs m 0x622d04 [C4 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x622d08 [C4 (Z_to_bv 64 (if reg then 2 else 1))] ->              (* [comment removed for export] *)
  rw_cells bsegs m 0x622d10 [C8 (Z_to_bv 64 0x622d18)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x622d18 [C8 z64] ->                                             (* [comment removed for export] *)
  rw_cells bsegs m 0x622d20 [C8 (Z_to_bv 64 0xb6dd0)] ->                           (* [comment removed for export] *)
  rw_cells bsegs m 0x622e20 [C8 (Z_to_bv 64 0x71fe8)] ->                            (* [comment removed for export] *)
  (reg = true -> rw_cells bsegs m 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)] /\ rw_cells bsegs m 0x622e28 [C8 (Z_to_bv 64 0x829b0)]
              /\ rw_cells bsegs m 0x602354 [C1 (Z_to_bv 8 0)]) ->
  rw_cells bsegs m 0x161ba0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
  mem_inv bsegs m ->
  (lo <= bv_unsigned sp - 48)%Z -> (KHIGH <= lo)%Z ->
  rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG ->
  evtF bsegs RNG (foe_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xb6c40) fc None m (seg_rom bsegs)).
Proof.
  intros until tm1. intros ST LIBC FIN ALK SLOT HEAD NEXT F0 A0 REG COV MI LO KH RSTK RIMG.
  pose proof KH as KH'. unfold KHIGH in KH'.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x622d00, 0x622d01); (0x622d08, 0x622d0c); (0x622d10, 0x622d18)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  Ltac nlit := try rewrite !sx32_lit by lia; try rewrite !swrap32_small by lia; try rewrite !Z.add_0_r.
  destruct reg; [destruct (REG eq_refl) as (F1 & A1 & INCB)|]; clear REG.
  all: carve_frame 48%nat ST.
  all: steps_to 0xc0f08%Z.
  (* [comment removed for export] *)
  all: hstep; hstep; hstep; change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word); if_true; hstep.
  1:{ (* [comment removed for export] *)
    change (if true then 2 else 1) with 2%Z in SLOT.
    astep. astep. hstep. nlit. hstep. hstep. nlit. change (2 + -1)%Z with 1%Z. hstep. astep.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. replace (sx32 z64) with z64 by (vm_compute; reflexivity). astep. hstep.
    hstep. hstep. hstep.
    (* [comment removed for export] *)
    hstep. hstep. change (zxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). astep. hstep.
    (* [comment removed for export] *)
    hstep. hstep.
    hstep. hstep. hstep. change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0 : word). if_true. hstep.
    hstep. nlit. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
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
    release_frame FR ST (bv_unsigned sp).
    unfold foe_post. finish. }
  (* [comment removed for export] *)
  change (if false then 2 else 1) with 1%Z in SLOT.
  astep. astep. hstep. nlit. hstep. hstep. nlit. change (1 + -1)%Z with 0%Z. hstep. astep.
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
  release_frame FR ST (bv_unsigned sp).
  unfold foe_post. finish.
Qed.

Section Prefix.
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  (* [comment removed for export] *)
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.

  Lemma aexit_prefix_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (reg : bool) (cdt thr sec : byte) (tm1 dso : word),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m 0x602c08 [C4 (Z_to_bv 64 t)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x622f20 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->       (* [comment removed for export] *)
    rw_cells bsegs m 0x622d00 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0x622d04 [C4 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x622d08 [C4 (Z_to_bv 64 (if reg then 2 else 1))] ->              (* [comment removed for export] *)
    rw_cells bsegs m 0x622d10 [C8 (Z_to_bv 64 0x622d18)] ->                           (* [comment removed for export] *)
    rw_cells bsegs m 0x622d18 [C8 z64] ->                                             (* [comment removed for export] *)
    rw_cells bsegs m 0x622d20 [C8 (Z_to_bv 64 0xb6dd0)] ->                           (* [comment removed for export] *)
    rw_cells bsegs m 0x622e20 [C8 (Z_to_bv 64 0x71fe8)] ->                            (* [comment removed for export] *)
    (reg = true -> rw_cells bsegs m 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)] /\ rw_cells bsegs m 0x622e28 [C8 (Z_to_bv 64 0x829b0)]
                /\ rw_cells bsegs m 0x602354 [C1 (Z_to_bv 8 0)]) ->     (* [comment removed for export] *)
    rw_cells bsegs m 0x161ba0 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0xc8010 [C8 (Z_to_bv 64 0xc6da0); C8 (Z_to_bv 64 0xc6d90)] -> (* [comment removed for export] *)
    rw_cells bsegs m 0xc6d90 [C8 (Z_to_bv 64 0x82c6c); C8 (Z_to_bv 64 0x32980)] ->  (* [comment removed for export] *)
    rw_cells bsegs m 0xcc690 [C1 (Z_to_bv 8 0)] ->                                   (* [comment removed for export] *)
    rw_cells bsegs m 0xc72d8 [C8 (Z_to_bv 64 0xb6d08); C8 z64] ->                   (* [comment removed for export] *)
    rw_cells bsegs m 0xc9050 [C8 dso] ->                                             (* [comment removed for export] *)
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W ->
    evtF bsegs RNG (aexit_prefix_post sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo code t ra m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xb6e24) fc None m (seg_rom bsegs)).
  Proof.
    intros until dso. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 A0 REG COV GF FA FINZ GCX DSO MI -> -> Ht LO KH RSTK RIMG RW.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold MDTOR_DEPTH in LO. unfold KHIGH in KH.
    pose proof (munch_refl (AEXIT_W1 (bv_unsigned sp)) m) as MU. unfold AEXIT_W1, MDTOR_DEPTH in MU.
    pose proof (wmono_refl bsegs m) as WM.
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
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (REG0 : reg = true -> rw_cells bsegs mc 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)] /\ rw_cells bsegs mc 0x622e28 [C8 (Z_to_bv 64 0x829b0)]
                                   /\ rw_cells bsegs mc 0x602354 [C1 (Z_to_bv 8 0)])
        by (intros E; destruct (REG E) as (F1 & A1 & INCB);
            split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn; lia]))
    end.
    clear REG.
    call_sp (funcs_on_exit_spec RNG); first [exact SLOT | exact REG0 | eassumption | reflexivity | unfold KHIGH; lia | lia | idtac].
    all: try (eapply rng_sub'; [exact RSTK| lia]).
    rename PC into ST.
    (* [comment removed for export] *)
    hstep. carve_frame 32%nat ST.
    steps_to 0x32980%Z.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    hstep. hstep. hstep. hstep. hstep. hstep. hstep. hstep. change (Z.land (bv_unsigned (zxb (Z_to_bv 8 0))) 1) with 0%Z. astep.
    steps_to 0xb6d08%Z. hstep.
    steps_to 0x32a0c%Z. release_frame FR1 ST (bv_unsigned sp + -48)%Z. hstep.
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
End Prefix.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ExitProof.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Variable PRE : mem -> Prop.
  Hypothesis MDTOR : module_dtor_stmt PRE.
  Hypothesis PRE_frame : forall sp m m', PRE m -> (KHIGH <= sp - 48 - MDTOR_DEPTH)%Z -> munch (AEXIT_W1 sp) m m' -> wmono bsegs m m' -> PRE m'.
  Hypothesis stdio_exit_spec : stdio_exit_spec_stmt2 get_so set_so.     (* [comment removed for export] *)

  Lemma aexit_spec : forall RNG (s : St) (Q : Empty_set -> St -> machine_state -> Prop)
      ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : mem) (lo : Z) (code t : Z) (reg : bool) (cdt thr sec : byte) (tm1 dso guard : word),
    PRE m ->
    stk bsegs m lo (bv_unsigned sp) ->
    rw_cells bsegs m 0x602c08 [C4 (Z_to_bv 64 t)] ->
    rw_cells bsegs m 0x622f20 [C4 z64] ->
    rw_cells bsegs m 0x622f40 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
    rw_cells bsegs m 0x622d00 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0x622d04 [C4 z64] ->
    rw_cells bsegs m 0x622d08 [C4 (Z_to_bv 64 (if reg then 2 else 1))] ->
    rw_cells bsegs m 0x622d10 [C8 (Z_to_bv 64 0x622d18)] ->
    rw_cells bsegs m 0x622d18 [C8 z64] ->
    rw_cells bsegs m 0x622d20 [C8 (Z_to_bv 64 0xb6dd0)] ->
    rw_cells bsegs m 0x622e20 [C8 (Z_to_bv 64 0x71fe8)] ->
    (reg = true -> rw_cells bsegs m 0x622d28 [C8 (Z_to_bv 64 0xb6dd0)] /\ rw_cells bsegs m 0x622e28 [C8 (Z_to_bv 64 0x829b0)]
                /\ rw_cells bsegs m 0x602354 [C1 (Z_to_bv 8 0)]) ->
    rw_cells bsegs m 0x161ba0 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0xc8010 [C8 (Z_to_bv 64 0xc6da0); C8 (Z_to_bv 64 0xc6d90)] ->
    rw_cells bsegs m 0xc6d90 [C8 (Z_to_bv 64 0x82c6c); C8 (Z_to_bv 64 0x32980)] ->
    rw_cells bsegs m 0xcc690 [C1 (Z_to_bv 8 0)] ->
    rw_cells bsegs m 0xc72d8 [C8 (Z_to_bv 64 0xb6d08); C8 z64] ->
    rw_cells bsegs m 0xc9050 [C8 dso] ->
    (* [comment removed for export] *)
    rw_cells bsegs m 0x6233a8 [C8 z64] -> rw_cells bsegs m 0xcbbd0 [C8 (Z_to_bv 64 RSTDIN)] -> rw_cells bsegs m RSTDIN stdin_cells ->
    rw_cells bsegs m 0xcbae0 [C8 (Z_to_bv 64 RSTDOUT)] -> rw_cells bsegs m 0xcb9f0 [C8 (Z_to_bv 64 RSTDERR)] ->
    stdout_file m (get_so s) -> stderr_file m ->
    rw_cells bsegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells bsegs m ssp_guard [C8 guard] ->
    mem_inv bsegs m ->
    tp = Z_to_bv 64 RTP -> a0 = Z_to_bv 64 code ->
    (0 < t < 4194304)%Z -> (lo <= bv_unsigned sp - 48 - MDTOR_DEPTH)%Z -> (KHIGH <= lo)%Z ->
    rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) MDTOR_W -> rng0 RNG ->
    (bv_unsigned sp < 2^47)%Z ->                      (* [comment removed for export] *)
    implAM RNG (Driver.exit_model (io_S get_so set_so) code) s Q
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xb6e24) fc None m (seg_rom bsegs)).
  Proof.
    intros until guard. intros HPRE ST TID EXL LIBC FIN ALK SLOT HEAD NEXT F0 A0 REG COV GF FA FINZ GCX DSO OFL SIN SINF SOU SEU SOF SEF GG GU MI -> -> Ht LO KH RSTK RIMG RW RG0 SP47.
    pose proof KH as KH'. unfold KHIGH in KH'. unfold MDTOR_DEPTH in LO.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
    destruct SOF as (flg & mode & tail & bufb & SOF1 & SOF2 & SOF3 & SOF4 & SOF5 & SOF6).
    destruct SEF as (flg' & mode' & ee & wend' & tail' & SEF1).
    unfold file_cells in SOF1, SEF1. unfold got_ssp, ssp_guard in GG, GU. unfold RSTDIN, stdin_cells in SIN, SINF.
    unfold Driver.exit_model.
    eapply (implAM_bind RNG _ _ s
              (fun _ _ ms' => exists sp' gp' tp' x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
                 ms' = MS (mkR (Z_to_bv 64 0xb6e90) sp' gp' tp' x5 x6 x7 (Z_to_bv 64 code) x9 x10 x11 x12 x13 x14 x15 x16 x17
                               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                          F (Z_to_bv 64 0xb6e90) fc None m' (seg_rom bsegs) /\ mem_inv bsegs m')).
    - (* [comment removed for export] *)
      change (io_exit (io_S get_so set_so)) with (stdout_exit_flush get_so set_so).
      apply implAM_from_evt.
      call (aexit_prefix_spec PRE MDTOR PRE_frame RNG);
        try first [ exact HPRE | exact SLOT | exact REG | eassumption | reflexivity | unfold MDTOR_DEPTH; lia | exact KH | exact RW ].
      all: try (lazymatch goal with |- rng _ _ _ => first [exact RSTK | exact RIMG] end).
      name_sp sp (-16)%Z.
      pose proof stdio_exit_spec as SE. unfold stdio_exit_spec_stmt2, got_ssp, ssp_guard, GLOBALS_TOP, RSTDIN, stdin_cells in SE.
      apply evtF_done. eapply implAM_mono; [eapply (SE RNG)|].
      all: lazymatch goal with
           | |- forall _, _ =>
               intros [] s' ms' PO; cbn [fst snd] in PO; unfold stdio_exit_post in PO;
               destruct_exs PO; destruct PO as (E & PO); subst ms'; cbn [fst snd];
               replace (ret_pc (Z_to_bv 64 0xb6e90)) with (Z_to_bv 64 0xb6e90) by (symmetry; apply ret_pc_even; [lia|reflexivity]);
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
End ExitProof.
End CANSEC2.
