(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the start-up chain takes the run's whole launch input and one certificate per CONFIG_RSEQ value (hand-off table, plan and result shape indexed by the flag); cs_ok_inp and init_cfg_gen are deleted; taken in part from projects/simdjson/fuzz_atpointer/proofs/lib/B/Z11e.v, lines 38-40, 49-55, 62-68, 77-88. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_ondemand.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import PropExec.
Local Instance topa_fx : PropExec.FPState := PropExec.fx0.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import
  ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctImages AxSymExec3 AxSymExec3Sound AxSymRun3
  AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanImagesB AsanInit AsanTablesB
  AsanNodesIface AsanNodesMmA AsanNodesMmB SumsAsanClose AsanNodesStartX AsanNodesStartXAsan AsanSmearA AsanHeapSortA AsanStartupB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Fixpoint holes_only (s : shape) : bool :=
  match s with
  | SHole _ => true
  | SCase _ _ a b => (holes_only a && holes_only b)%bool
  | SAlt2 a b => (holes_only a && holes_only b)%bool
  | _ => false
  end.

Lemma sd_holes_only : forall (HOLES : nat -> env -> Fs.Fs -> TSet) (D : TSet) (E : env) (fs : Fs.Fs) (T : TSet) (s : shape),
  (forall h, t_eq (HOLES h E fs) T) -> holes_only s = true -> t_eq (sd HOLES D E fs s) T.
Proof.
  intros HOLES D E fs T s HH. induction s as [| c | fd ps s' IH | a IHa b IHb | e mid a IHa b IHb | h | ];
    cbn [holes_only sd]; intros Hs; try discriminate.
  - apply andb_prop in Hs as [H1 H2]. intros tr. unfold t_alt2. rewrite (IHa H1 tr), (IHb H2 tr). tauto.
  - apply andb_prop in Hs as [H1 H2]. destruct (bv_unsigned (edenot E e) <=? mid); [exact (IHa H1) | exact (IHb H2)].
  - exact (HH h).
Qed.

(* LPS 727298f3: [cs_ok_inp] and [init_cfg_gen] are gone (image B's twin of
   A/TopA_start.v).  They moved [cs_ok] from the launch input AS/AsanInit.v used to fix
   to the run's input, and [wrap_mem] reads the exec name and the kernel now,
   so that move is false.  AS/AsanInit.v's Section Init takes the run's whole input
   instead, and [AsanStartupB.asan_startup] is stated at it. *)

Section StartupGen.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* ONE CHAIN PER CONFIG_RSEQ VALUE, as in A/TopA_start.v *)
  Variable HS_both : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : Z -> shape.
  Variables KC0 BFUEL FUEL : nat.
  (* ONE CERTIFICATE PER CLOSED [rseq_z b], joined by the [forall b] wrapper;
     the flag is NOT pinned ([recorded_kernel] preserves [kb_rseq]). *)
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_B NX0 AsanInit.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_both (rseq_z b)) KC0 BFUEL FUEL None
          (asan_b_init (rseq_z b)) (startup_plan (rseq_z b)) = COk (startup_shape (rseq_z b)).
  Hypothesis Hshape : forall b : bool, holes_only (startup_shape (rseq_z b)) = true.

  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    holes_stmt ASEGS ASAN_B NX0 AsanInit.LIMIT (HS_both (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 ASAN_B APH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).

  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS AsanUbsan.M.init_pc APH) en inp -> valid_input_either inp ->
    srealizes ASEGS (init_config ASEGS AsanUbsan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
                                 target_alloc_limit inp)
              (T (in_argv inp) (in_fs inp)).
  Proof using IT0_ok startup_cert Hshape T_nil T_holes.
    intros en inp Hve Hvi.
    destruct en as [sp brk0 mbase rdraw].
    (* [Run.valid_input_either]: argv, envp, fs, keys, image, creds, nofile,
       sigmask, hwcap, va size, urandom, launch, reader, sigpipe, kernel *)
    destruct Hvi as (Hva & Hvenv & _ & _ & _ & (Huid & _) & _ & _ & _ & Hsv & _ & Hlaunch & Hrdr & _ & Hkb).
    rewrite (valid_entry_sv48 _ _ _ Hsv) in Hve. destruct Hve as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    cbn [en_sp en_brk en_mmap_base en_draw] in *.
    set (HOLES := fun (_ : nat) (_ : env) (fs' : Fs.Fs) => T (in_argv inp) fs').
    pose proof (T_holes sp rdraw brk0 mbase inp Hsp Hva Hvenv Hfit Hlaunch Hlau) as HOLES_sound.
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 sp rdraw brk0 inp) (in_fs inp) (startup_shape (rseq_z (kb_rseq (in_kernel inp)))))).
    - eapply asan_startup.
      all: first [ exact (startup_cert (kb_rseq (in_kernel inp))) | exact IT0_ok | exact HOLES_sound
                 | (intros; reflexivity) | (intros; apply T_nil) | eassumption ].
    - apply sd_holes_only; [intros h tr; reflexivity | exact (Hshape (kb_rseq (in_kernel inp)))].
  Qed.
End StartupGen.
