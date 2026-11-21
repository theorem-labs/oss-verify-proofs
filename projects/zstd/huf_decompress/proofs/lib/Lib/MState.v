(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (15 recorded proofs replaced by written proofs (MS_eta, step_gen, step_ecall_gen and 12 more); adds kr_u_anchor, kr_u_anchor2, segs_vvar and 6 more; imports). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MState () := "C4ELinuxProcessSemantics5Riscv7PreludeBbvmap_get_set_sameC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics5Riscv7PreludeCbvmap_get_set_otherK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_regsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8ms_fregsC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics9ms_pc_valC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_resvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_memC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_romc59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state01K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8is_ecallI47Corelib4Init9Datatypes4prod00C4ELinuxProcessSemantics5Riscv7DecodeC:decode_anyK47Corelib4Init9Datatypes4prod01I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsDdecode_exec_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_word_ovC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>fetch_tail_anyC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=fetch_failureK47Corelib4Init9Datatypes4list01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result02K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result03C45stdpp9bitvector;definitions7Z_to_bvK4ELinuxProcessSemantics5Riscv3Sem4core01C4ELinuxProcessSemantics5Riscv3Sem4execC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:interp_effc59OSSVerify5KrLib3Lib6MState;lift_resultC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics6ms_regC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsCinterp_eff_accessesC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<access_valueC4ELinuxProcessSemantics5Riscv3Sem6c_regsC4ELinuxProcessSemantics5Riscv3Sem7c_fregsC4ELinuxProcessSemantics5Riscv3Sem4c_pcC4ELinuxProcessSemantics5Riscv3Sem6c_resvC4ELinuxProcessSemantics5Riscv3Sem6c_fcsrC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics?accessed_rangesC4ELinuxProcessSemantics5Riscv7DecodeCBis_defined_illegalC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemanticsBdrop_access_reportK4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>machine_result01K4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=access_report01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5ms_pcC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics4stepI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics5Riscv5Instr5instr00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=memory_accessK47Corelib4Init5Logic4True01I4ELinuxProcessSemantics5Riscv3Sem4core00C4ELinuxProcessSemantics5Riscv3Sem5is_x0C4ELinuxProcessSemantics5Riscv3Sem7reg_getc59OSSVerify5KrLib3Lib6MState5MSsvcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions4BvWfK47Corelib4Init9Datatypes4bool01C4ELinuxProcessSemantics5Riscv3Sem2w0C4ELinuxProcessSemantics5Riscv7Prelude9bvmap_setC4ELinuxProcessSemantics5Riscv7Prelude9bvmap_getC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums1Z01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions6bv_addC56Stdlib6ZArith6BinInt1Z3addC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions:bv_modulusC56Stdlib6ZArith6BinInt1Z6moduloC46Stdlib6ZArith4Zdiv9Zplus_modC47Corelib4Init5Logic6eq_indC45stdpp9bitvector;definitions@Z_to_bv_unsignedC45stdpp9bitvector;definitions?bv_add_unsignedI47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C46Stdlib6ZArith4ZdivAZplus_mod_idemp_lC59OSSVerify5KrLib3Lib8PropExec6v_addiC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC35stdpp7tactics<f_equal_helpI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01C45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallc59OSSVerify5KrLib3Lib6MStateCZ_to_bv_bv_unsignedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7add_0_rC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltc59OSSVerify5KrLib3Lib6MState6ret_pcC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions6bv_notC45stdpp9bitvector;definitions6bv_andC56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z4lnotC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z7testbitC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z3eqbK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr01C56Stdlib6ZArith6BinInt1Z8bit0_eqbC56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega7EnvRing5PExpr04C56Stdlib6ZArith6BinInt1Z=ones_spec_lowC56Stdlib6ZArith6BinInt1Z6shiftlC56Stdlib6ZArith6BinInt1Z;shiftl_specC47Corelib4Init5Logic6eq_symC46Stdlib4Bool4Bool;andb_true_rC56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z<log2_lt_pow2K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z;lt_le_transC56Stdlib6ZArith6BinInt1Z?bits_above_log2C56Stdlib6ZArith6BinInt1Z9land_specC56Stdlib6ZArith6BinInt1Z9bits_inj'C56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphC46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions?bv_not_unsignedC45stdpp9bitvector;definitions?bv_and_unsignedK46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula03C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00C46Stdlib9micromega8ZifyInst7Inj_Z_Z".
Import ListNotations.
Open Scope bv_scope.

(* UNIVERSE ANCHOR, and it is load-bearing rather than decoration.  The F_memchr replays rewrite
   under `@respectful machine_state Prop eq (flip impl)`, and the kernel checks that application
   against the universe graph it inherits instead of inferring a fresh constraint for it.  With
   the inequality absent the check fails with
     Type@{max(Set,bvmap.u0)} ... should be a subtype of Type@{Proper.u0}
   at a line holding nothing but a replay blob, which names neither the file nor the cause.
   Writing the application once here records `machine_state`'s universe below [respectful]'s in
   MState.vo, which every replay file already Requires.  Nothing is assumed and nothing is
   proved: this is a definition whose only job is the constraint it carries. *)
From Corelib Require Import Classes.Morphisms.
Definition kr_u_anchor (R : machine_state -> machine_state -> Prop) (S : Prop -> Prop -> Prop)
  : (machine_state -> Prop) -> (machine_state -> Prop) -> Prop :=
  @respectful machine_state Prop R S.

(* ANCHOR 2, UNVERIFIED BY A COMPILER -- it is the next link of the same chain, and it is a
   HYPOTHESIS until a build removes it.  With kr_u_anchor above in place the failure moved from
   respectful to
     @reflexive_eq_dom_reflexive : forall (A B : Type) (R' : relation B),
        Reflexive R' -> Reflexive (eq ==> R')%signature
     "Type@{max(Set,bvmap.u0)} ... should be a subtype of Type@{GenericInstances.u0}"
   (log-20261106T043815Z).  The signature below is transcribed from that error, not guessed.
   The chain is BOUNDED and its extent is measured, not estimated: decoding the four F_memchr
   constant tables lists exactly 26 Corelib.Classes constants, the same 26 in every lane, so at
   most that many universes can need recording and most take no Type argument at all. *)
Definition kr_u_anchor2 (R : Prop -> Prop -> Prop) (H : Reflexive R)
  : Reflexive (@respectful machine_state Prop eq R) :=
  @reflexive_eq_dom_reflexive machine_state Prop R H.

(* [comment removed for export] *)
Definition MS (R F : bvmap 5 word) (pc : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := None;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

Definition MSsvc (R F : bvmap 5 word) (pc : word) (x8 : word) (fc : bv 32) (rv : option word)
           (m ro : word -> option byte) : machine_state :=
  {| ms_regs := R; ms_fregs := F; ms_pc_val := pc; ms_svc_pending := Some x8;
     ms_resv := rv; ms_fcsr := fc; ms_mem := m; ms_rom := ro |}.

(* [comment removed for export] *)
Definition MS_of_core (c : core) (m ro : word -> option byte) : machine_state :=
  MS (c_regs c) (c_fregs c) (c_pc c) (c_fcsr c) (c_resv c) m ro.

Lemma MS_eta : forall ms, ms_svc_pending ms = None ->
  ms = MS (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H; cbn in *; subst; reflexivity. Qed.

(* [comment removed for export] *)

(* The vvar arm of a failed load (08b1429, unchanged at 75d69e00) is guarded by [segs_vvar segs]
   first: for a binary's own segment list (no vvar segment) that reduces to [false] by conversion,
   so the shim below keeps, on a concrete image, the pre-revision shape the recorded walk terms
   were built against.  [interp_eff_accesses_nv_shim_ok] stays unconditional, because a byte of the
   vvar pages lies in a vvar segment of [segs] ([range_meets_vvar_segs]). *)
Definition segs_vvar (segs : list Segment) : bool := existsb seg_vdso_vvar segs.

Lemma find_segment_in : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
  induction segs as [|s r IH]; intros a n seg H; cbn in H; [discriminate|].
  destruct (_ && _)%bool; [injection H as <-; left; reflexivity | right; exact (IH _ _ _ H)].
Qed.

Lemma range_meets_vvar_segs : forall segs a n, range_meets_vvar segs a n = true -> segs_vvar segs = true.
Proof.
  intros segs a n; revert a. induction n as [|n IH]; intros a H; cbn in H; [discriminate|].
  apply orb_prop in H as [H|H]; [|exact (IH _ H)].
  unfold vvar_byte_at in H. destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|discriminate].
  unfold segs_vvar. apply existsb_exists. exists seg. split; [exact (find_segment_in _ _ _ _ E) | exact H].
Qed.

Section InterpEffNV.
Variable segs : list Segment.

(* [RiscvSemantics.interp_eff_accesses] (RiscvSemantics.v:988-1033 at 75d69e00) copied
   STRUCTURALLY, with one change: the ELoad miss arm's vvar test is guarded by [segs_vvar segs].
   The access-report layer is reproduced exactly as the model builds it.  Its predecessor
   [interp_eff0] collapsed that layer into the bare [core * mem] result, so a recorded term --
   which carries the layer reduced but present (the [mkAccessReport ... ((a, n) :: ...)] node) --
   could never match it; that is measured, not argued, in the 87-vs-53 round. *)
Fixpoint interp_eff_accesses_nv_shim (t : eff) (m : word -> option byte)
    : machine_result (access_report (core * (word -> option byte))) :=
  match t with
  | EDone c => MachineOk (@mkAccessReport _ (c, m) [])
  | EEbreak _ | EFault _ | EDefinedIllegal _ => MachineFault
  | EIllegal _ | EEcall _ => MachineUnmodeled
  | ELoad n a k =>
      match ov_read_bytes segs m a (width_bytes n) with
      | Some bs =>
        match interp_eff_accesses_nv_shim (k (bv_extract 0 n (le_bytes_to_word bs))) m with
        | MachineOk report =>
          MachineOk
            (@mkAccessReport _ (@access_value _ report)
               ((a, width_bytes n) :: @accessed_ranges _ report))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
        end
      | None =>
        if (segs_vvar segs && range_meets_vvar segs a (width_bytes n))%bool
        then MachineUnmodeled else MachineFault
      end
  | EStore n a v k =>
      if store_ok segs m a (width_bytes n)
      then
        match interp_eff_accesses_nv_shim k
                (write_to_mem m a
                   (Z_to_le_bytes (width_bytes n) (bv_unsigned v))) with
        | MachineOk report =>
          MachineOk
            (@mkAccessReport _ (@access_value _ report)
               ((a, width_bytes n) :: @accessed_ranges _ report))
        | MachineFault => MachineFault
        | MachineUnmodeled => MachineUnmodeled
        end
      else MachineFault
  end.

Lemma interp_eff_accesses_nv_shim_ok :
  forall t m, interp_eff_accesses segs t m = interp_eff_accesses_nv_shim t m.
Proof.
  induction t as [c|c|c|c|c|c|n a k IH|n a v k IH]; intros m;
    cbn [interp_eff_accesses interp_eff_accesses_nv_shim]; try reflexivity.
  - destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|].
    + rewrite <- IH. reflexivity.
    + destruct (range_meets_vvar segs a (width_bytes n)) eqn:Ev.
      * rewrite (range_meets_vvar_segs _ _ _ Ev). reflexivity.
      * rewrite andb_false_r. reflexivity.
  - destruct (store_ok segs m a (width_bytes n)); [|reflexivity].
    rewrite <- IH. reflexivity.
Qed.
End InterpEffNV.

(* NAME LENGTHS HERE ARE LOAD-BEARING, and the two numbers are forced, not chosen.  A replay
   reaches these by one swapped entry in its own encoded constant table, and KReplay indexes
   that table by BYTE OFFSET (KReplay.v:594/:635), so a swapped entry must occupy exactly as
   many bytes as the model entry it replaces.  An entry is `C<nsegs>(<len><seg>)*`, each <len>
   written as chr(48+len), so with the path Lib.MState fixed at 48 bytes:
     RiscvSemantics.interp_eff           = 66 bytes  ->  name must be 18 chars
     RiscvSemantics.interp_eff_accesses  = 75 bytes  ->  name must be 27 chars
   [interp_eff_nv_shim] is 18 and [interp_eff_accesses_nv_shim] is 27.  Renaming either without
   re-padding makes the decoder read a shifted offset and die on `KReplay: bad identifier`;
   that is measured, in log-20261106T033929Z. *)
Definition interp_eff_nv_shim (segs : list Segment) (t : eff) (m : word -> option byte)
    : machine_result (core * (word -> option byte)) :=
  drop_access_report (interp_eff_accesses_nv_shim segs t m).

Definition lift_result (ro : word -> option byte) (r : machine_result (core * (word -> option byte)))
  : machine_result machine_state :=
  match r with
  | MachineOk (c, m') => MachineOk (MS_of_core c m' ro)
  | MachineFault => MachineFault
  | MachineUnmodeled => MachineUnmodeled
  end.

Lemma step_gen : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  lift_result ro (interp_eff segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  (* [comment removed for export] *)
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He, Hd. cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom MS].
  unfold interp_eff.
  destruct (interp_eff_accesses segs (exec (Z_to_bv 64 sz) i _) m) as [[[c m'] acc]| |]; reflexivity.
Qed.

(* [step_gen] with its right-hand side over the shim.  Two things about it are load-bearing and
   neither is cosmetic.
   (1) BINDERS AND ARITY ARE IDENTICAL to [step_gen]'s.  The recorded terms apply it
       positionally, so one premise or one argument more would break every one of them.
   (2) THE NAME IS EXACTLY AS LONG AS [step_gen], eight characters, and must stay so.  A replay
       reaches this lemma by one name swap inside its own encoded constant table, and KReplay
       indexes that table by BYTE OFFSET (KReplay.v:594/:635, `kr_global ... tab (kr_num4 ...)`),
       so a longer name shifts every later entry and the decoder dies on `bad identifier`.
       That is measured: `step_gen_nv` produced exactly that error before the rename. *)
Lemma step_gnv : forall segs R F pc fc rv m ro w i sz,
  fetch_word segs pc = Some w ->
  is_ecall w = false ->
  decode_any w = Some (i, sz) ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  lift_result ro (interp_eff_nv_shim segs (exec (Z_to_bv 64 sz) i (Core R F pc fc rv)) m).
Proof.
  intros segs R F pc fc rv m ro w i sz Hf He Hd.
  unfold interp_eff_nv_shim. rewrite <- (interp_eff_accesses_nv_shim_ok segs).
  exact (step_gen segs R F pc fc rv m ro w i sz Hf He Hd).
Qed.

(* [comment removed for export] *)
Lemma step_ecall_gen : forall segs R F pc fc rv m ro w,
  fetch_word segs pc = Some w ->
  is_ecall w = true ->
  RiscvSemantics.step segs (MS R F pc fc rv m ro) =
  MachineOk (MSsvc R F pc (if is_x0 17 then w0 else reg_get R 17) fc rv m ro).
Proof.
  intros segs R F pc fc rv m ro w Hf He.
  unfold RiscvSemantics.step, RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val MS]. rewrite Hf.
  unfold decode_exec_accesses. rewrite He. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma reg_get_set_same : forall (R : bvmap 5 word) (r : reg) v,
  reg_get (bvmap_set r v R) r = v.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_same. reflexivity. Qed.

Lemma reg_get_set_other : forall (R : bvmap 5 word) (r r' : reg) v,
  r <> r' -> reg_get (bvmap_set r v R) r' = reg_get R r'.
Proof. intros. unfold reg_get. rewrite bvmap_get_set_other by assumption. reflexivity. Qed.

(* [comment removed for export] *)

Lemma w0_lit : w0 = Z_to_bv 64 0.
Proof.
ltac2:(KReplay.run1 (kr_t_MState ()) [] "p;1p;2g002Aj10Tg002fj14Tg003Dj12Tg00Pej21Tg00@Oj23Tg00B0#0#0#0#0#0#0#4R0#2g00n?,10'3o"). Qed.
Lemma w1_lit : w1 = Z_to_bv 64 1.
Proof.
ltac2:(KReplay.run1 (kr_t_MState ()) [] "p;1p;2g002Aj10Tg002fj15Tg003Dj12Tg00TXj11Tg00Pej24Tg00@Oj23Tg00B0R0#0#0#0#0#0#0#5R1#2%10,41'3o"). Qed.

(* [comment removed for export] *)
Lemma lit_add_lit : forall a b, (Z_to_bv 64 a + Z_to_bv 64 b : word) = Z_to_bv 64 (a + b).
Proof.
  intros. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

Lemma v_addi_lit : forall p i, v_addi (Z_to_bv 64 p) i = Z_to_bv 64 (p + i).
Proof.
  intros p i. unfold v_addi. rewrite Z_to_bv_unsigned. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma v_addi_assoc : forall (x : word) a b,
  v_addi (Z_to_bv 64 (bv_unsigned x + a)) b = Z_to_bv 64 (bv_unsigned x + (a + b)).
Proof.
  intros. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma v_addi_var : forall (x : word) b, v_addi x b = Z_to_bv 64 (bv_unsigned x + b).
Proof. reflexivity. Qed.

Lemma Z_to_bv_bv_unsigned : forall (x : word), Z_to_bv 64 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma Z_to_bv_plus0 : forall (x : word), Z_to_bv 64 (bv_unsigned x + 0) = x.
Proof. intros. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)
Lemma unsigned_lit : forall z, (0 <= z < 2^64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact H. Qed.

Lemma unsigned_lit_wrap : forall z, bv_unsigned (Z_to_bv 64 z) = (z mod 2^64)%Z.
Proof. intros. rewrite Z_to_bv_unsigned. reflexivity. Qed.

(* [comment removed for export] *)
Definition ret_pc (ra : word) : word := bv_and ra (bv_not (Z_to_bv 64 1)).

Lemma ret_pc_fold : forall ra, bv_and ra (bv_not (Z_to_bv 64 1)) = ret_pc ra.
Proof. reflexivity. Qed.

Lemma ret_pc_even : forall z, (0 <= z < 2^64)%Z -> (z mod 2 = 0)%Z -> ret_pc (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz He. unfold ret_pc. apply bv_eq. rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  rewrite !(bv_wrap_small 64 z) by (unfold bv_modulus; lia).
  change (bv_wrap 64 (Z.lnot (bv_wrap 64 1))) with (Z.ones 64 - 1)%Z.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
  destruct (Z.eq_dec i 0).
  - subst i. rewrite (Z.bit0_eqb z). replace (z mod 2)%Z with 0%Z by lia. cbn. reflexivity.
  - destruct (Z.ltb_spec0 i 64).
    + replace (Z.testbit (Z.ones 64 - 1) i) with true. { apply andb_true_r. }
      symmetry. change (Z.ones 64 - 1)%Z with (Z.shiftl (Z.ones 63) 1). rewrite Z.shiftl_spec by lia. apply Z.ones_spec_low. lia.
    + rewrite (Z.bits_above_log2 z i); [reflexivity| lia |].
      destruct (Z.eq_dec z 0). { subst. cbn. lia. }
      apply Z.lt_le_trans with 64%Z; [|lia]. apply Z.log2_lt_pow2; lia.
Qed.
