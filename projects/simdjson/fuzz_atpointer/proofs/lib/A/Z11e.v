(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch stated over the run's whole input; the start-up per CONFIG_RSEQ value and the new auxv layout). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zg2.
Local Instance topa_fx : Zg2.FPState := Zg2.fx0.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import
  Zp7 Z10a Z14 Z1b Z1c Z78 Z7a Z7b
  Z2z Z2y Z33 Z34 Z30 Z1s Z3g
  Z2o Z2q Z2r Z110 Z2t Z2u Z3a Z1h Z3d.
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

(* LPS 727298f3: [cs_ok_inp] and [init_cfg_gen] are gone.  They moved [cs_ok]
   from the launch input AS/Z1s.v used to fix (exec name, [/tmp], descriptor
   limit, urandom, signal mask and flags all pinned) to the run's input, and
   [wrap_mem] reads the exec name and the kernel now, so that move is false.
   AS/Z1s.v's Section Init takes the run's whole input instead, and
   [Z3d.asan_startup] is stated at it. *)

Section StartupGen.

  Variable IT0 : itab.
  Hypothesis IT0_ok : itab_sound ASEGS IT0.
  (* ONE CHAIN PER CONFIG_RSEQ VALUE: the hand-off table and the plan are read
     at the run's own [rseq_z (kb_rseq (in_kernel inp))].  The plan's states
     move with [AUXSZ r = 432 + 32 * r], so one table cannot serve both. *)
  Variable HS_asan : Z -> nat -> option acs.
  Variable startup_plan : Z -> plan.
  Variable startup_shape : shape.
  Variables KC0 BFUEL FUEL : nat.
  (* ONE CERTIFICATE PER CLOSED [rseq_z b], joined by the [forall b] wrapper.
     A certificate is checked at one literal value of the flag
     (75d69e00:theories/Common/AsanPlan.v:35).  The flag is NOT pinned: this
     section is entered at whatever [kb_rseq] the run's kernel gives, and
     [recorded_kernel] preserves [kb_rseq]. *)
  Hypothesis startup_cert : forall b : bool,
    check ASEGS IT0 ASAN_A NX0 Z1s.LIMIT (rseq_z b) XN0 XE0 XB0 (HS_asan (rseq_z b)) KC0 BFUEL FUEL None
          (asan_a_init (rseq_z b)) (startup_plan (rseq_z b)) = COk startup_shape.
  Hypothesis Hshape : holes_only startup_shape = true.

  Variable T : list (list byte) -> Fs.Fs -> TSet.
  Hypothesis T_nil : forall argv fs, T argv fs [].
  Hypothesis T_holes : forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (inp : ProcInput),
    valid_sp sp -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) inp ->
    holes_stmt ASEGS ASAN_A NX0 Z1s.LIMIT (HS_asan (rseq_z (kb_rseq (in_kernel inp))))
               (SINV0 ASAN_A APH sp rdraw brk0 mbase inp) (argH0 sp rdraw inp)
               (fun _ _ fs' => T (in_argv inp) fs') (in_fs inp).

  Theorem asan_startup_gen : forall en inp,
    valid_entry (mkImage ASEGS Asan.M.init_pc APH) en inp -> valid_input_either inp ->
    srealizes ASEGS (init_config ASEGS Asan.M.init_pc APH (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en)
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
    apply (srz_conseq ASEGS _ (sd HOLES t_nil (E0 sp rdraw brk0 inp) (in_fs inp) startup_shape)).
    - eapply asan_startup.
      all: first [ exact (startup_cert (kb_rseq (in_kernel inp))) | exact IT0_ok | exact HOLES_sound
                 | (intros; reflexivity) | (intros; apply T_nil) | eassumption ].
    - apply sd_holes_only; [intros h tr; reflexivity | exact Hshape].
  Qed.
End StartupGen.
