(* The bridge between a contract's absolute addresses and the listing's object atoms.

   A walk runs under `Context {PI : PAImg cmd_listing}`, where an auipc/addi pair denotes the atom `A_OBJ i`, so
   the symbolic state says `SOff (A_OBJ i) off` and the walk can only learn `pa_val (A_OBJ i)`. A contract, on the
   other hand, names the image's objects by their address (g_rec 0x5e32c0, the literals, the GOT words), because
   the driver, the global invariant GI_cmdA and the plain proof's models do. `cmd_val_objs` is the one premise
   that ties the two together for every object of the listing at once; the instance discharges it by computation,
   so no walk carries a per-object hypothesis. cgif does the same thing per object (lib/A/AChc.v's VAL (A_OBJ 0)
   and (A_OBJ 12) facts, lib/YC1f.v:305-307). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* The program functions a walk calls (fuzz_command.asan-ubsan's 64 program functions in its function table,
   less LLVMFuzzerTestOneInput, which no function calls and which is the listing's first word, BASE + 0), and each
   one's offset from the listing's base, so that a walk can match a callee's `BASE + AF_<fn>` with the call target
   `pa_sigma CS_<fn>`. B's set differs from A's: xmalloc, record and arg_s are functions here; arg_i and xstrdup
   are inlined. *)
Definition cmd_prog_syms : list csym := [
CS_send_message; CS_check_reply; CS_check_arity; CS_check_words; CS_check_refusal; CS_check_round_trip;
CS_check_reply_answer; CS_syntax_reply_matches; CS_joined; CS_check_words_add; CS_check_words_chain;
CS_check_words_pin_set; CS_rec_code_declared; CS_rec_shape_of; CS_rec_canonical; CS_xmalloc; CS_rec_clear;
CS_rec_calls_free; CS_rec_calls_copy; CS_rec_calls_equal; CS_sup_resp; CS_sup_reply_code; CS_sup_add; CS_record;
CS_arg_s; CS_hand_back; CS_answer; CS_mix_call; CS_sup_call; CS_arg_line; CS_sup_remove; CS_sup_remove_all;
CS_sup_connect; CS_sup_broadcast; CS_sup_host_setting; CS_sup_instance_verb; CS_sup_worker_list;
CS_sup_instance_info; CS_sup_reset; CS_sup_quarantine_clear; CS_sup_policy_set; CS_sup_pin_accept;
CS_sup_pool_config; CS_sup_lv2_worker_set; CS_sup_worker_env; CS_sup_chain; CS_sup_chain_clear; CS_sup_after_reply;
CS_pins_set; CS_answer_code; CS_pins_clear; CS_descriptors_add; CS_descriptors_get; CS_descriptors_panel_get;
CS_lv2_refusals_forget; CS_socket_send; CS_verbs_receive; CS_reply; CS_verb_is; CS_chain_words; CS_number;
CS_pin_set_words; CS_is_instance_verb].
Definition cmd_af (s : csym) : Z := cmd_sigma s - cmd_text.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section c.
Context {PI : PAImg cmd_listing}.
Definition cmd_val_objs : Prop :=
forall i, (i < length cmd_objs)%nat -> pa_val (A_OBJ i) = nth i cmd_objs 0.
Definition cmd_val_his : Prop :=
forall j, (j < length cmd_his)%nat -> pa_val (A_HI j) = nth j cmd_his 0.
(* the call target of every program function, against the listing's base *)
Definition cmd_sig_prog : Prop :=
forall s, In s cmd_prog_syms -> pa_sigma s = pa_val A_TEXT + cmd_af s.
(* the instance's read-only range is the image's relro range (CmdImg.v sets these values: fuzz_command.asan-ubsan's
   .data.rel.ro start and .got end) *)
Definition cmd_val_relro : Prop := pa_relro_lo = 0xa52a0 /\ pa_relro_hi = 0xa6c68.
End c.
End b.
