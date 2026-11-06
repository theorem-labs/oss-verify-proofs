(* Modified by Theorem Labs, 2026-10: relocated by R4Printf.BzPrintfPort (a Theorem Labs lane) onto plugin-hostd/fuzz_reply.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/K/I_snprintfw.v: module paths and 7 address numerals, rewritten in one pass, each paired by object (the code functions are identical modulo pc-relative fields): 0x4268c->0x421d4 trampoline_vsnprintf+0x0; 0x42694->0x421dc trampoline_snprintf+0x0; 0x45b58->0x464e0 ___interceptor_vsnprintf+0x0; 0x45fa0->0x46928 ___interceptor_snprintf+0x58; 0x5a078->0x5adf0 TryAsanInitFromRtl+0x0; 0xa8c18->0xa6d98 asan_inited+0x0; 0x5f7000->0x5fb000 try_init_spec's stack bound (our I_ikit.v), fuzz_reply image end. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread X_atexit D_kit I_ikit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition snfr (usp : Z) (j0 j1 : list byte) (ra s0 s1 s2 : word) : list cell :=
  [CB 8 j0; C8 (Z_to_bv 64 (usp + -40)); C8 s2; C8 s1; C8 s0; C8 ra; CB 8 j1].

Definition snw_call (usp : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (m' : mem) (t0 t1 t2 a4' a5' a6' a7' t3 t4 t5 t6 : word) (j0 j1 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x46928) (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 a2 a1 a0 a1 a2
                  (Z_to_bv 64 (usp + -40)) a4' a5' a6' a7' a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x464e0) fc None m' (seg_rom asegs)
    /\ munch [(usp - 112, usp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (usp + -96)
    /\ rw_cells asegs m' (usp + -96) (snfr usp j0 j1 ra s0 s1 s2)
    /\ rw_cells asegs m' (usp + -40) [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7].

Lemma snprintf_walkA : forall (usp lo : Z)
    ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 112 -> 0x5fb000 <= lo -> usp <= 2^47 ->
  rw_cells asegs m 0xa6d98 [C1 (Z_to_bv 8 1)] -> mem_inv asegs m ->
  evt asegs (snw_call usp ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 a2 a3 a4 a5 a6 a7 F fc lo m)
    (MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x421dc) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO LOLO SPH AI MI.
  pose proof (munch_refl [(usp - 112, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
  carve_frame 40%nat ST. rename FR into FRva.
  apply (rw_cells_split_CB asegs _ _ [] 40 _ [] [8; 8; 8; 8; 8]%nat) in FRva; [| reflexivity].
  cbn [mk_CB_cells app] in FRva.
  carve_frame 56%nat ST. rename FR into FRp.
  apply (rw_cells_split_CB asegs _ _ [] 56 _ [] [8; 8; 8; 8; 8; 8; 8]%nat) in FRp; [| reflexivity].
  cbn [mk_CB_cells app] in FRp.
  xsteps_to 0x5adf0%Z.
  call try_init_spec; [exact AI | rewrite EU96; exact ST | rewrite EU96; lia | lia | assumption |].
  rename POST into ST. rewrite EU96 in ST.
  xsteps_to 0x464e0%Z.
  apply evt_done. unfold snw_call. do 14 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. split; [exact FRp | exact FRva].
Qed.

Lemma snprintf_walkB : forall (usp lo : Z) (j0 j1 : list byte) (ra s0 s1 s2 a3 a4 a5 a6 a7 : word)
    (ra' gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  stk asegs m lo (usp + -96) -> lo <= usp + -96 -> usp <= 2^47 ->
  rw_cells asegs m (usp + -96) (snfr usp j0 j1 ra s0 s1 s2) ->
  rw_cells asegs m (usp + -40) [C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] ->
  mem_inv asegs m ->
  evt asegs (fun ms' => (exists (t0' t1' t2' a1' a2'' a3'' a4'' a5'' a6'' a7'' t3' t4' t5' t6' : word),
                 ms' = MS (mkR ra (Z_to_bv 64 usp) gp tp t0' t1' t2' s0 s1 a0 a1' a2'' a3'' a4'' a5'' a6'' a7''
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m (seg_rom asegs))
                 /\ stk asegs m lo usp)
    (MS (mkR ra' (Z_to_bv 64 (usp + -96)) gp tp t0 t1 t2 s0' s1' a0 a1 a2' a3' a4' a5' a6' a7' s2' s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x46928) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO UT FRp FRva MI. unfold snfr in FRp.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU96 : bv_unsigned (Z_to_bv 64 (usp + -96)) = usp + -96) by (apply unsigned_lit; lia).
  do 6 lstep.
  release_frame FRp ST (usp + -40).
  release_frame FRva ST usp.
  apply evt_done. split; [| exact ST]. do 14 eexists. first [reflexivity | f_equal; f_equal; apply Z_to_bv_eqm; lia].
Qed.

Lemma vsn_tramp_mstep : forall (R F : bvmap 5 word) (fc : bv 32) (m : mem),
  mstep asegs (MS R F (Z_to_bv 64 0x421d4) fc None m (seg_rom asegs))
              (MS R F (Z_to_bv 64 0x464e0) fc None m (seg_rom asegs)).
Proof.
  intros R F fc m. split; [reflexivity|].
  change (MS R F (Z_to_bv 64 0x421d4) fc None m (seg_rom asegs))
    with (@mkst (mkFP F fc) R (Z_to_bv 64 0x421d4) m (seg_rom asegs)).
  let fw := eval vm_compute in (fetch_word asegs (Z_to_bv 64 0x421d4)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (Jal _ ?imm, _) =>
          assert (Hd : decode_any w = Some (Jal 0 imm, 4%Z))
            by (vm_compute;
                lazymatch goal with
                | |- Some (Jal ?r1 ?i1, _) = Some (Jal ?r2 ?i2, _) =>
                    replace r1 with r2 by (apply bv_eq; reflexivity);
                    replace i1 with i2 by (apply bv_eq; reflexivity); reflexivity
                end);
          rewrite (@step_jal_x0 (mkFP F fc) asegs R (Z_to_bv 64 0x421d4) m (seg_rom asegs) w imm
                     ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) Hd);
          assert (Et : btgt (Z_to_bv 64 0x421d4) (bv_signed imm) = Z_to_bv 64 0x464e0)
            by (apply bv_eq; vm_compute; reflexivity);
          rewrite Et; reflexivity
      end
  end.
Qed.
