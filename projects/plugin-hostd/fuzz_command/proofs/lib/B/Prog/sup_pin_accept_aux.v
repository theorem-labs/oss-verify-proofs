(* sup_pin_accept on the ASan+UBSan build of plugin-hostd/fuzz_command (fuzz_command.asan-ubsan): the facts of its
   image-B walk that need no callee contract. The walk itself (tsup_pin_accept_spec of lib/B/Prog/sup_pin_accept_c.v)
   composes the contracts of record, arg_s, rec_shape_of and answer; this file holds only the constants of the B
   code and the facts about the verb literal and the call targets.

   B code (fuzz_command.asan-ubsan, sha256 658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401,
   .symtab sup_pin_accept = 0x8be78, size 88 = 22 instructions; listing lib/B/Prog/CmdList.v:5793-5814):
     0x8be78 addi sp,sp,-32 / sd ra,24(sp) / sd s0,16(sp) / sd s1,8(sp)   a 32-byte frame, no side-stack frame
     0x8be88 mv s0,a0                                                      s0 = uri
     0x8be8c li a0,13 ; 0x8be90 jal record (0x8a728)                       record(REC 13), slot in a0
     0x8be94 mv s1,a0 ; 0x8be98 mv a1,s0 ; 0x8be9c jal arg_s (0x8a820)     arg_s(slot, uri), slot in s1
     0x8bea0 auipc a0 / addi a0 (0x21ea0) ; 0x8bea8 li a1,10 ;
     0x8beac jal rec_shape_of (0x896d4)                                    rec_shape_of("pin_accept", 10)
     0x8beb0 li a2,1 ; mv a1,a0 ; mv a0,s1 ; ld ra / ld s0 / ld s1 ;
     0x8bec8 addi sp,sp,32 ; 0x8becc j answer (0x8aa10)                    answer(slot, shape, 1) at the entry sp
   No conditional branch, no `jal __asan_report_*`, no unimp: 0 report and 0 UBSan trap edges. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdAddr CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdObj CmdRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* the frame and the pcs of the B code, as offsets from the listing's base *)
Definition SPB_FRAME : Z := 32.
Definition SPB_RET_RECORD : Z := AF_sup_pin_accept + 0x1c.   (* mv s1,a0 after the call of record (0x8be94) *)
Definition SPB_RET_ARG_S : Z := AF_sup_pin_accept + 0x28.    (* auipc a0 after the call of arg_s (0x8bea0) *)
Definition SPB_RET_RSO : Z := AF_sup_pin_accept + 0x38.      (* li a2,1 after the call of rec_shape_of (0x8beb0) *)
Definition SPB_TAIL : Z := AF_sup_pin_accept + 0x54.         (* j answer (0x8becc) *)

Lemma spb_pcs : cmd_text + AF_sup_pin_accept = 0x8be78 /\ cmd_text + SPB_RET_RECORD = 0x8be94 /\
  cmd_text + SPB_RET_ARG_S = 0x8bea0 /\ cmd_text + SPB_RET_RSO = 0x8beb0 /\ cmd_text + SPB_TAIL = 0x8becc.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the verb rec_shape_of is asked for: the 10 bytes of "pin_accept" at 0x21ea0 (the listing's object 72) *)
Definition spb_verb : list byte := bstr "pin_accept"%string.
Lemma spb_verb_lit : spb_verb ++ [Z_to_bv 8 0] = RO_lit_21ea0.
Proof. vm_compute. reflexivity. Qed.
Lemma spb_verb_len : length spb_verb = 10%nat.
Proof. reflexivity. Qed.
Lemma spb_verb_shape : shape_of spb_verb = daemon_shape "pin_accept"%string.
Proof. reflexivity. Qed.
Lemma spb_verb_no0 : ~ In (Z_to_bv 8 0) spb_verb.
Proof.
intros Hin. apply (in_map bv_unsigned) in Hin. vm_compute in Hin.
repeat (destruct Hin as [Hin | Hin]; [discriminate Hin|]). exact Hin.
Qed.
Lemma spb_obj72 : nth 72 cmd_objs 0 = 0x21ea0.
Proof. reflexivity. Qed.

(* the callees' offsets from the listing's base, and the four callees are program functions of the listing *)
Lemma spb_af : cmd_af CS_record = AF_record /\ cmd_af CS_arg_s = AF_arg_s /\
  cmd_af CS_rec_shape_of = AF_rec_shape_of /\ cmd_af CS_answer = AF_answer.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma spb_prog_syms : In CS_record cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
  In CS_rec_shape_of cmd_prog_syms /\ In CS_answer cmd_prog_syms.
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {PI : PAImg cmd_listing}.
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).

(* the address the auipc/addi pair at 0x8bea0 denotes, from the statement's object bridge *)
Lemma spb_verb_val : cmd_val_objs -> VAL (A_OBJ 72) = 0x21ea0.
Proof. intros VOBJS. rewrite (VOBJS 72%nat ltac:(vm_compute; lia)). exact spb_obj72. Qed.

(* the call targets: each callee's entry is BASE + AF_<fn>, from the walk fact cmd_sig_prog (record's is the kit's
   CmdRecAns.rca_sig_record) *)
Section s.
Hypothesis SIGP : cmd_sig_prog.
Lemma spb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s (proj1 (proj2 spb_prog_syms))), (proj1 (proj2 spb_af)). reflexivity. Qed.
Lemma spb_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof.
rewrite (SIGP CS_rec_shape_of (proj1 (proj2 (proj2 spb_prog_syms)))), (proj1 (proj2 (proj2 spb_af))).
reflexivity.
Qed.
Lemma spb_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof.
rewrite (SIGP CS_answer (proj2 (proj2 (proj2 spb_prog_syms)))), (proj2 (proj2 (proj2 spb_af))).
reflexivity.
Qed.
End s.
End d.
