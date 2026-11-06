(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/CmdObj.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; csym -> ssym, cmd_ -> seg_; the program functions a walk calls are fuzz_segconf.asan's 33 (every program function in 0x84d34..0x8a188 but LLVMFuzzerTestOneInput, in address order, the --call list of SegList); the read-only range 0xa5740..0xa7108 -> 0xa14a0..0xa3748 (fuzz_segconf.asan's .data.rel.ro start and .got end). *)
(* Modified by Theorem Labs, 2026-10: copied from lib/A/Prog/SegObj.v for fuzz_segconf.asan-ubsan: module paths; and the image-B values named in the commit message. *)
(* The bridge between a contract's absolute addresses and the listing's object atoms.

   A walk runs under `Context {PI : PAImg cmd_listing}`, where an auipc/addi pair denotes the atom `A_OBJ i`, so
   the symbolic state says `SOff (A_OBJ i) off` and the walk can only learn `pa_val (A_OBJ i)`. A contract, on the
   other hand, names the image's objects by their address (g_rec 0x5e3740, the literals, the GOT words), because
   the driver, the global invariant GI_cmdA and the plain proof's models do. `cmd_val_objs` is the one premise
   that ties the two together for every object of the listing at once; the instance discharges it by computation,
   so no walk carries a per-object hypothesis. cgif does the same thing per object (lib/A/AChc.v's VAL (A_OBJ 0)
   and (A_OBJ 12) facts, lib/YC1f.v:305-307). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable SegSyms SegList SegAddr SegPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* The program functions a walk calls (the image's function table, fn column, less LLVMFuzzerTestOneInput, which no
   function calls and which is the listing's first word, BASE + 0), and each one's offset from the listing's
   base, so that a walk can match a callee's `BASE + AF_<fn>` with the call target `pa_sigma CS_<fn>`. *)
Definition seg_prog_syms : list ssym := [
SS_m_file; SS_check_segments; SS_check_role; SS_check_model; SS_check_ignore; SS_check_provenance;
SS_check_refusals; SS_check_address; SS_check_knock_refused; SS_m_find; SS_check_absent; SS_check_declared;
SS_m_refuse; SS_strip; SS_ieq; SS_fold; SS_reac_segconf_init; SS_reac_segconf_parse_file; SS_refuse; SS_trim;
SS_reac_segconf_parse; SS_cross_check; SS_reac_segconf_find; SS_reac_segconf_ignored; SS_reac_segconf_role;
SS_reac_segconf_role_file; SS_reac_segconf_ignore_file; SS_reac_segconf_model; SS_reac_segconf_declared;
SS_reac_declared_vlan_split; SS_name_ok; SS_reac_declared_vlan_add; SS_fuzz_catalogue_row; SS_reac_box_catalogue;
SS_reac_box_catalogue_by_token].
Definition seg_af (s : ssym) : Z := seg_sigma s - seg_text.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Context {PI : PAImg seg_listing}.
Definition seg_val_objs : Prop :=
forall i, (i < length seg_objs)%nat -> pa_val (A_OBJ i) = nth i seg_objs 0.
Definition seg_val_his : Prop :=
forall j, (j < length seg_his)%nat -> pa_val (A_HI j) = nth j seg_his 0.
(* the call target of every program function, against the listing's base *)
Definition seg_sig_prog : Prop :=
forall s, In s seg_prog_syms -> pa_sigma s = pa_val A_TEXT + seg_af s.
(* the instance's read-only range is the image's relro range (CmdImg.v sets these values) *)
Definition seg_val_relro : Prop := pa_relro_lo = 0xa1c60 /\ pa_relro_hi = 0xa3f08.
End c.
End b.
