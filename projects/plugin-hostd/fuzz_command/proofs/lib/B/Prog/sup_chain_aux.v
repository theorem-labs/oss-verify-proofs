(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helper facts of sup_chain's walk on plugin-hostd/fuzz_command's ASan+UBSan
   build (fuzz_command.asan-ubsan), for a Theorem Labs lane's lib/B/Prog/sup_chain_c.v (`tsup_chain_spec`), that need none of the
   callee statements record_c / arg_s_c / answer_c. Re-walked at B's addresses from the ASan walk
   lib/A/Prog/sup_chain_s2.v (the text model of the loop: formats, pf_dec bridge, dec_list), from
   lib/B/Prog/answer_code_aux.v (the class-1 side-stack frame, the realigned frame, the entry state) and
   sup_pool_config_aux.v (snprintf's 16-byte buffer, the int argument).

   B code (capstone 5.0.7 over the pin's .symtab, sha256 658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401):
   sup_chain = 0x8c1c4 = BASE + AF_sup_chain (0x86530 + 0x5c94), 940 bytes, 235 instructions (all 4-byte); listing
   lib/B/Prog/CmdList.v:6004-6238. 192-byte frame (`addi sp,sp,-192`, `sd zero,0(sp)`, ra and s0 .. s11 to
   sp + 184 .. sp + 88), `addi s0,sp,192` (s0 = the entry sp), `andi sp,sp,-32` (0x8c204), s1 = the realigned sp.
   Calls: __asan_stack_malloc_1 0x3fac8 (0x8c23c, a0 = 96), record 0x8a728 (0x8c2f4, a0 = 17), xmalloc 0x899b4
   (0x8c30c, a0 = 12n + 1), the snprintf trampoline 0x451d0 (0x8c334 and 0x8c364, "%d" 0x21f40), arg_s 0x8a820
   (0x8c340, 0x8c374, 0x8c450), the sprintf trampoline 0x451cc (0x8c414, "%d" / " %d" 0x21f20), the free trampoline
   0x589cc (0x8c458), rec_shape_of 0x896d4 (0x8c468, "chain" 0x21f60, 5), answer 0x8aa10 (0x8c478, changes = 1).
   Report calls: __asan_report_load4 (0x8c440; guarded by `bnez` 0x8c408 and `blt` 0x8c438, the shadow of ids[k]) and
   __asan_report_store1 (0x8c56c; guarded by `bnez` 0x8c390 and `blt` 0x8c564, the shadow of list[0]): scb_ld4_ok,
   scb_ids_addr and scb_chk0 below are the facts that refute them at their branches. UBSan: four checks, all to the
   `unimp` at 0x8c55c: 0x8c3d0 `bltu s2,s5` (scb_trap_3d0 with scb_xor_m1), 0x8c3e4 `bltu s8,a0` (scb_trap_3e4),
   0x8c3f0 `beqz a0` (scb_trap_3f0), 0x8c3f4 `beqz s9` (scb_trap_3f4). Every auipc is a paired object slot of the
   listing (PLdHi for the two GOT words, PAddHi for the rest), so no plain-word access goes through an A_HI value
   and the walk needs no `cmd_val_his`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YM05 YG05 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdAddr CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSnText.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m YF0x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- program points, as listing offsets from BASE (B, measured with capstone from .symtab) ---------- *)
Definition SCB_FRAME : Z := 192.                          (* addi sp,sp,-192; the realignment adds up to 16 *)
Definition SCB_SIDE_REQ : Z := 96.                        (* __asan_stack_malloc_1's request: class 1, 128 bytes *)
Definition SCB_SMALLOC : Z := AF_sup_chain + 0x78.        (* 0x8c23c: jal __asan_stack_malloc_1, a0 = 96 *)
Definition SCB_FLAG0 : Z := AF_sup_chain + 0x80.          (* 0x8c244: the use-after-return flag is 0: a0 := 0 *)
Definition SCB_FJOIN : Z := AF_sup_chain + 0x84.          (* 0x8c248: the flag's two arms meet *)
Definition SCB_REAL : Z := AF_sup_chain + 0x8c.           (* 0x8c250: the real-stack fallback (frame = 0) *)
Definition SCB_SEAT : Z := AF_sup_chain + 0xa8.           (* 0x8c26c: the frame a4 is seated *)
Definition SCB_RECORD : Z := AF_sup_chain + 0x130.        (* 0x8c2f4: jal record, a0 = 17 *)
Definition SCB_XMALLOC : Z := AF_sup_chain + 0x148.       (* 0x8c30c: jal xmalloc, a0 = 12n + 1 *)
Definition SCB_SNPRINTF1 : Z := AF_sup_chain + 0x170.     (* 0x8c334: snprintf(frame + 64, 16, "%d", id) *)
Definition SCB_ARGS1 : Z := AF_sup_chain + 0x17c.         (* 0x8c340: arg_s(slot, frame + 64) *)
Definition SCB_SNPRINTF2 : Z := AF_sup_chain + 0x1a0.     (* 0x8c364: snprintf(frame + 32, 16, "%d", n) *)
Definition SCB_ARGS2 : Z := AF_sup_chain + 0x1b0.         (* 0x8c374: arg_s(slot, frame + 32) *)
Definition SCB_CHK0 : Z := AF_sup_chain + 0x1c8.          (* 0x8c38c: lb of list[0]'s shadow (store1 check) *)
Definition SCB_LOOP : Z := AF_sup_chain + 0x20c.          (* 0x8c3d0: loop head, UBSan check 1 *)
Definition SCB_LCHK : Z := AF_sup_chain + 0x240.          (* 0x8c404: lb of ids[k]'s shadow (load4 check) *)
Definition SCB_SPRINTF : Z := AF_sup_chain + 0x250.       (* 0x8c414: sprintf(list + o, fmt_k, ids[k]) *)
Definition SCB_BACK : Z := AF_sup_chain + 0x264.          (* 0x8c428: bne s11,s10 (back edge) *)
Definition SCB_REPLD4 : Z := AF_sup_chain + 0x27c.        (* 0x8c440: jal __asan_report_load4 *)
Definition SCB_LEXIT : Z := AF_sup_chain + 0x280.         (* 0x8c444: after the loop *)
Definition SCB_ARGS3 : Z := AF_sup_chain + 0x28c.         (* 0x8c450: arg_s(slot, list) *)
Definition SCB_FREE : Z := AF_sup_chain + 0x294.          (* 0x8c458: free(list) *)
Definition SCB_SHAPE : Z := AF_sup_chain + 0x2a4.         (* 0x8c468: rec_shape_of("chain", 5) *)
Definition SCB_ANSWER : Z := AF_sup_chain + 0x2b4.        (* 0x8c478: answer(slot, shape, 1) *)
Definition SCB_REL : Z := AF_sup_chain + 0x2b8.           (* 0x8c47c: the frame's release (magic 0x45e0360e) *)
Definition SCB_RREL : Z := AF_sup_chain + 0x324.          (* 0x8c4e8: the real-stack arm of the release *)
Definition SCB_EPI : Z := AF_sup_chain + 0x358.           (* 0x8c51c: the epilogue, sp := s0 - 192 *)
Definition SCB_RET : Z := AF_sup_chain + 0x394.           (* 0x8c558: ret *)
Definition SCB_TRAP : Z := AF_sup_chain + 0x398.          (* 0x8c55c: unimp, the four UBSan checks' target *)
Definition SCB_CHK0B : Z := AF_sup_chain + 0x39c.         (* 0x8c560: list[0]'s partial-granule test *)
Definition SCB_REPST1 : Z := AF_sup_chain + 0x3a8.        (* 0x8c56c: jal __asan_report_store1 *)

Lemma scb_pcs : cmd_text + AF_sup_chain = 0x8c1c4 /\ cmd_text + SCB_SMALLOC = 0x8c23c /\
  cmd_text + SCB_RECORD = 0x8c2f4 /\ cmd_text + SCB_XMALLOC = 0x8c30c /\ cmd_text + SCB_SNPRINTF1 = 0x8c334 /\
  cmd_text + SCB_ARGS1 = 0x8c340 /\ cmd_text + SCB_SNPRINTF2 = 0x8c364 /\ cmd_text + SCB_ARGS2 = 0x8c374 /\
  cmd_text + SCB_LOOP = 0x8c3d0 /\ cmd_text + SCB_SPRINTF = 0x8c414 /\ cmd_text + SCB_ARGS3 = 0x8c450 /\
  cmd_text + SCB_FREE = 0x8c458 /\ cmd_text + SCB_SHAPE = 0x8c468 /\ cmd_text + SCB_ANSWER = 0x8c478 /\
  cmd_text + SCB_REL = 0x8c47c /\ cmd_text + SCB_EPI = 0x8c51c /\ cmd_text + SCB_RET = 0x8c558 /\
  cmd_text + SCB_TRAP = 0x8c55c /\ cmd_text + SCB_REPLD4 = 0x8c440 /\ cmd_text + SCB_REPST1 = 0x8c56c.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the listing's objects the code names: the two GOT words, the shadow-base cell, "%d", the frame descriptor
   "2 32 16 9 b.i28:237 64 16 7 b.i:237", the function's own address, " %d", "chain" *)
Lemma scb_objs : nth 0 cmd_objs 0 = 0xa5f50 /\ nth 1 cmd_objs 0 = 0xa5fa8 /\ nth 12 cmd_objs 0 = 0xb0c38 /\
  nth 51 cmd_objs 0 = 0x21f40 /\ nth 77 cmd_objs 0 = 0x1dfad /\ nth 78 cmd_objs 0 = 0x8c1c4 /\
  nth 79 cmd_objs 0 = 0x21f20 /\ nth 80 cmd_objs 0 = 0x21f60.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the callees' offsets from the listing's base, and the five are program functions of the listing *)
Lemma scb_af : cmd_af CS_record = AF_record /\ cmd_af CS_xmalloc = AF_xmalloc /\ cmd_af CS_arg_s = AF_arg_s /\
  cmd_af CS_rec_shape_of = AF_rec_shape_of /\ cmd_af CS_answer = AF_answer.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma scb_prog_syms : In CS_record cmd_prog_syms /\ In CS_xmalloc cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
  In CS_rec_shape_of cmd_prog_syms /\ In CS_answer cmd_prog_syms.
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

(* the store values of the frame code: the header magic (0x8c27c/0x8c290), the release magic (0x8c47c/0x8c480),
   the shadow bytes of the class-1 frame after its set-up (0x8c2b8 .. 0x8c2ec: f1 x 4 | f8 f8 b.i28 | f2 f2 | f8 f8
   b.i | f3 f3) and the release's f5 *)
Definition scb_fr_shadow0 : list Z := [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf8; 0xf2; 0xf2; 0xf8; 0xf8; 0xf3; 0xf3].
Lemma scb_store_consts : 0x41b59 * 4096 + (-0x54d) = 0x41b58ab3 /\ 0x45e03 * 4096 + 0x60e = 0x45e0360e /\
  map (fun z => z mod 256) [-15; -15; -15; -15; -8; -8; -14; -14; -8; -8; -13; -13] = scb_fr_shadow0 /\
  (-11) mod 256 = 0xf5.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------- the model, in the order the walk's callees build it ---------- *)
Definition scb_verb : list byte := bstr "chain"%string.

Lemma scb_args : forall id n (l : list byte), (([] ++ [dec id]) ++ [dec n]) ++ [l] = [dec id; dec n; l].
Proof. reflexivity. Qed.

Lemma scb_model : forall R id ids,
sup_chain_m R id ids =
rec_answer (rec_record R REC_CHAIN [dec id; dec (Z.of_nat (length ids)); dec_list ids])
  (REC_CHAIN, [dec id; dec (Z.of_nat (length ids)); dec_list ids]) (shape_of scb_verb) true.
Proof. intros R id ids. unfold sup_chain_m, rec_stub, daemon_shape. reflexivity. Qed.

(* ---------- the read-only literals: "%d" (0x21f40), " %d" (0x21f20), "chain" (0x21f60) ---------- *)
Definition scb_fmt0 : list Z := [37; 100].
Definition scb_fmt1 : list Z := [32; 37; 100].

Lemma scb_fmt0_lit : RO_lit_21f40 = PF.pf_bytes scb_fmt0 ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma scb_fmt1_lit : RO_lit_21f20 = PF.pf_bytes scb_fmt1 ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma scb_verb_lit : RO_lit_21f60 = scb_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.
Lemma scb_verb_len : Z.of_nat (length scb_verb) = 5.
Proof. reflexivity. Qed.
Lemma scb_verb_shape : shape_of scb_verb = daemon_shape "chain"%string.
Proof. reflexivity. Qed.

Lemma scb_lit_21f40_at : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f40 RO_lit_21f40.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21f40 _ /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.
Lemma scb_lit_21f20_at : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f20 RO_lit_21f20.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21f20 _ /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.
Lemma scb_lit_21f60_at : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f60 RO_lit_21f60.
Proof.
intros rd [HRO _]. unfold cmd_ro_bytes in HRO.
repeat match type of HRO with
| abytes_atR _ 0x21f60 _ /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

Lemma scb_abytes_prefix : forall (rd : reader) a l1 l2, abytes_atR rd a (l1 ++ l2) -> abytes_atR rd a l1.
Proof. intros rd a l1 l2 H k Hk. rewrite (H k ltac:(rewrite length_app; lia)). rewrite app_nth1 by lia. reflexivity. Qed.

Lemma scb_fmt0_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21f40 (PF.pf_bytes scb_fmt0).
Proof.
intros rd H. pose proof (scb_lit_21f40_at rd H) as HL. rewrite scb_fmt0_lit in HL. split; [exact HL|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.
Lemma scb_fmt1_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21f20 (PF.pf_bytes scb_fmt1).
Proof.
intros rd H. pose proof (scb_lit_21f20_at rd H) as HL. rewrite scb_fmt1_lit in HL. split; [exact HL|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.
Lemma scb_verb_str : forall rd, cmd_ro_ok rd -> astr_atR rd 0x21f60 scb_verb.
Proof.
intros rd H. pose proof (scb_lit_21f60_at rd H) as HL. rewrite scb_verb_lit in HL. split; [exact HL|].
vm_compute. intros Hc. repeat (destruct Hc as [Hc | Hc]; [discriminate Hc|]). exact Hc.
Qed.
Lemma scb_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd 0x21f60 scb_verb.
Proof.
intros rd H. pose proof (scb_lit_21f60_at rd H) as HL. rewrite scb_verb_lit in HL.
exact (scb_abytes_prefix rd _ _ _ HL).
Qed.

Lemma scb_fmt0_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 3 -> ro (0x21f40 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 3 -> ro (0x21f40 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.
Lemma scb_fmt1_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 4 -> ro (0x21f20 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 4 -> ro (0x21f20 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.
Lemma scb_verb_ro : forall ro, cmd_ro_in ro -> forall i, 0 <= i < 6 -> ro (0x21f60 + i).
Proof.
intros ro HRO. unfold cmd_ro_in in HRO.
repeat match type of HRO with
| (forall i, 0 <= i < 6 -> ro (0x21f60 + i)) /\ _ => exact (proj1 HRO)
| _ /\ _ => apply proj2 in HRO
end.
Qed.

(* ---------- the formats, their pieces and the text they give (lib/A/Prog/sup_chain_s2.v at B's addresses) ---------- *)
Lemma scb_fmt0_parse : PF.pf_parse scb_fmt0 = Some [PF.Pd].
Proof. reflexivity. Qed.
Lemma scb_fmt1_parse : PF.pf_parse scb_fmt1 = Some [PF.PLit 32; PF.Pd].
Proof. reflexivity. Qed.
Lemma scb_fmt1_text : forall v, PF.pf_text [PF.PLit 32; PF.Pd] [PF.AInt v] = Some (32 :: PF.pf_dec v).
Proof.
intros v. change (Some (32 :: (PF.pf_dec v ++ [])) = Some (32 :: PF.pf_dec v)). rewrite app_nil_r. reflexivity.
Qed.

Lemma scb_pf_dec_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> (1 <= length (PF.pf_dec v) <= 11)%nat.
Proof.
intros v Hv. pose proof (dec_length v Hv) as H. rewrite <- (snt_pf_dec v Hv) in H.
unfold PF.pf_bytes in H. rewrite length_map in H. exact H.
Qed.

(* the inlined arg_i: snprintf(b, 16, "%d", v) writes dec v and its NUL into the 16-byte buffer *)
Lemma scb_snprintf_len : forall v, -2 ^ 31 <= v < 2 ^ 31 -> Z.of_nat (length (PF.pf_dec v)) < 2 ^ 31 - 1.
Proof. intros v Hv. pose proof (scb_pf_dec_len v Hv). lia. Qed.
Lemma scb_snprintf_out : forall v, -2 ^ 31 <= v < 2 ^ 31 ->
PF.pf_bytes (firstn (Z.to_nat (16 - 1)) (PF.pf_dec v) ++ [0]) = dec v ++ [Z_to_bv 8 0].
Proof.
intros v Hv. pose proof (scb_pf_dec_len v Hv) as HL.
change (Z.to_nat (16 - 1)) with 15%nat. rewrite firstn_all2 by lia.
unfold PF.pf_bytes. rewrite map_app. fold (PF.pf_bytes (PF.pf_dec v)). rewrite (snt_pf_dec v Hv). reflexivity.
Qed.

(* the member at index k: its format, pieces, text and the bytes sprintf writes *)
Lemma scb_fmt_text : forall (k : nat) v, -2 ^ 31 <= v < 2 ^ 31 ->
exists ps t, PF.pf_parse (if Nat.eqb k 0 then scb_fmt0 else scb_fmt1) = Some ps /\
  PF.pf_text ps [PF.AInt v] = Some t /\
  PF.pf_bytes t = (if Nat.eqb k 0 then dec v else SPACE :: dec v) /\
  Z.of_nat (length t) + 1 < 2 ^ 31.
Proof.
intros k v Hv. pose proof (scb_pf_dec_len v Hv) as HL. destruct (Nat.eqb k 0).
- exists [PF.Pd], (PF.pf_dec v). split; [exact scb_fmt0_parse|]. split; [apply snt_text_d|].
  split; [exact (snt_pf_dec v Hv) | lia].
- exists [PF.PLit 32; PF.Pd], (32 :: PF.pf_dec v). split; [exact scb_fmt1_parse|]. split; [apply scb_fmt1_text|].
  split; [|cbn [length]; lia].
  change (PF.pf_bytes (32 :: PF.pf_dec v)) with (Z_to_bv 8 32 :: PF.pf_bytes (PF.pf_dec v)).
  rewrite (snt_pf_dec v Hv). reflexivity.
Qed.
Lemma scb_sprintf_out : forall (t : list Z) (b : list byte), PF.pf_bytes t = b ->
PF.pf_bytes (t ++ [0]) = b ++ [Z_to_bv 8 0].
Proof. intros t b H. unfold PF.pf_bytes in *. rewrite map_app, H. reflexivity. Qed.

(* an int argument in a register as w64 v (the entry's a0 = id and a2 = n go to snprintf in a3) *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma scb_aint_arg : forall segs stk (W : world segs) regs mem D n rs v, -2 ^ 31 <= v < 2 ^ 31 ->
apf_args_ok segs stk W regs mem D n (w64 v :: rs) [PF.AInt v].
Proof.
intros segs stk W regs mem D n rs v Hv. cbn [apf_args_ok apf_arg_ok]. split; [|destruct rs; exact I].
split; [exact Hv|].
unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_eq v (2 ^ 64)) by lia.
replace (v - 2 ^ 64 * (v / 2 ^ 64)) with (v + (- (2 ^ 32) * (v / 2 ^ 64)) * 2 ^ 32) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.
End a.

(* ---------- the loop's text: dec_list over the prefixes of ids ---------- *)
Lemma scb_dec_list_snoc : forall l v,
dec_list (l ++ [v]) = dec_list l ++ (match l with [] => dec v | _ :: _ => SPACE :: dec v end).
Proof.
intros [|i r] v.
- exact (app_nil_r (dec v)).
- change (dec i ++ concat (map (fun j => SPACE :: dec j) (r ++ [v])) =
          (dec i ++ concat (map (fun j => SPACE :: dec j) r)) ++ SPACE :: dec v).
  rewrite <- (app_assoc (dec i)). f_equal.
  rewrite map_app, concat_app. f_equal.
  exact (app_nil_r (SPACE :: dec v)).
Qed.
Lemma scb_firstn_snoc : forall (A : Type) (l : list A) k v, nth_error l k = Some v ->
firstn (S k) l = firstn k l ++ [v].
Proof.
intros A l. induction l as [|a l IH]; intros k v H.
- destruct k; cbn [nth_error] in H; discriminate H.
- destruct k as [|k].
  + cbn [nth_error] in H. injection H as E. subst. reflexivity.
  + change (a :: firstn (S k) l = a :: (firstn k l ++ [v])). rewrite (IH k v H). reflexivity.
Qed.
Lemma scb_firstn_len : forall (A : Type) (l : list A) k, (k <= length l)%nat -> length (firstn k l) = k.
Proof.
intros A l. induction l as [|a l IH]; intros [|k] H; cbn [firstn length] in *; try reflexivity; try lia.
rewrite IH by lia. reflexivity.
Qed.
Lemma scb_Forall_firstn : forall (A : Type) (P : A -> Prop) (l : list A) k, Forall P l -> Forall P (firstn k l).
Proof.
intros A P l. induction l as [|a l IH]; intros [|k] H; cbn [firstn]; try constructor.
- exact (Forall_inv H).
- apply IH. exact (Forall_inv_tail H).
Qed.
Lemma scb_dec_list_step : forall ids k v, nth_error ids k = Some v ->
dec_list (firstn (S k) ids) = dec_list (firstn k ids) ++ (if Nat.eqb k 0 then dec v else SPACE :: dec v).
Proof.
intros ids k v H. rewrite (scb_firstn_snoc _ ids k v H), scb_dec_list_snoc.
destruct k as [|k]; [reflexivity|].
destruct ids as [|a ids']; [cbn [nth_error] in H; discriminate H | reflexivity].
Qed.
Lemma scb_dec_list_all : forall ids : list Z, firstn (length ids) ids = ids.
Proof. intros ids. apply firstn_all. Qed.

Lemma scb_space_dec_no0 : forall j, no0 (SPACE :: dec j).
Proof.
intros j. change (SPACE :: dec j) with ([SPACE] ++ dec j). apply no0_app; [|apply dec_no0].
apply no0_forall. apply Forall_cons; [|apply Forall_nil]. unfold SPACE. rewrite byte_unsigned by lia. lia.
Qed.
Lemma scb_concat_no0 : forall r, no0 (concat (map (fun j => SPACE :: dec j) r)).
Proof.
induction r as [|j r IH]; [intros H; exact H|].
change (no0 ((SPACE :: dec j) ++ concat (map (fun j => SPACE :: dec j) r))).
apply no0_app; [apply scb_space_dec_no0 | exact IH].
Qed.
Lemma scb_dec_list_nz : forall ids, ~ In (Z_to_bv 8 0) (dec_list ids).
Proof.
intros [|i r]; [intros H; exact H|].
change (no0 (dec i ++ concat (map (fun j => SPACE :: dec j) r))).
apply no0_app; [apply dec_no0 | apply scb_concat_no0].
Qed.

(* lengths: each member takes at most 11 bytes and one separator, so n members fit 12n - 1 bytes *)
Lemma scb_concat_len : forall r, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) r ->
Z.of_nat (length (concat (map (fun j => SPACE :: dec j) r))) <= 12 * Z.of_nat (length r).
Proof.
induction r as [|j r IH]; intros HF; [cbn [map concat length]; lia|].
change (concat (map (fun j => SPACE :: dec j) (j :: r)))
  with ((SPACE :: dec j) ++ concat (map (fun j => SPACE :: dec j) r)).
rewrite length_app. cbn [length].
pose proof (dec_length j (Forall_inv HF)). specialize (IH (Forall_inv_tail HF)). lia.
Qed.
Lemma scb_dec_list_len : forall ids, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> (1 <= length ids)%nat ->
Z.of_nat (length (dec_list ids)) <= 12 * Z.of_nat (length ids) - 1.
Proof.
intros [|i r] HF Hn; [cbn [length] in Hn; lia|].
change (dec_list (i :: r)) with (dec i ++ concat (map (fun j => SPACE :: dec j) r)).
rewrite length_app. cbn [length].
pose proof (dec_length i (Forall_inv HF)). pose proof (scb_concat_len r (Forall_inv_tail HF)). lia.
Qed.
Lemma scb_dec_list_prefix_len : forall ids k, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids ->
(k <= length ids)%nat -> Z.of_nat (length (dec_list (firstn k ids))) <= 12 * Z.of_nat k.
Proof.
intros ids [|k] HF Hk; [exact (Z.le_refl 0)|].
pose proof (scb_firstn_len _ ids (S k) Hk) as Hl.
pose proof (scb_dec_list_len (firstn (S k) ids) (scb_Forall_firstn _ _ ids (S k) HF) ltac:(lia)) as E.
lia.
Qed.
(* the text after member k and its NUL fit the block of 12n + 1 bytes xmalloc returned *)
Lemma scb_room : forall ids k, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> (k < length ids)%nat ->
Z.of_nat (length (dec_list (firstn (S k) ids))) + 1 <= 12 * Z.of_nat (length ids) + 1.
Proof. intros ids k HF Hk. pose proof (scb_dec_list_prefix_len ids (S k) HF ltac:(lia)). lia. Qed.
(* the finished text is a recorder argument: no NUL, at most 743 bytes (arg_s's LMAX) *)
Lemma scb_text_arg : forall ids, Forall (fun v => -2 ^ 31 <= v < 2 ^ 31) ids -> (1 <= length ids <= 62)%nat ->
~ In (Z_to_bv 8 0) (dec_list ids) /\ Z.of_nat (length (dec_list ids)) + 1 <= LMAX + 1.
Proof.
intros ids HF Hn. split; [apply scb_dec_list_nz|].
pose proof (scb_dec_list_len ids HF ltac:(lia)). unfold LMAX. lia.
Qed.

(* ---------- the arithmetic of the UBSan checks and of xmalloc's size ---------- *)
(* 0x8c2fc .. 0x8c308: a0 := (n << 4) - (n << 2) + 1 *)
Lemma scb_xm_size : forall n, 0 <= n <= 62 -> (Z.shiftl n 4 - Z.shiftl n 2 + 1) mod 2 ^ 64 = 12 * n + 1.
Proof.
intros n Hn. rewrite !Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. change (2 ^ 2) with 4.
replace (n * 16 - n * 4 + 1) with (12 * n + 1) by lia. apply Z.mod_small. lia.
Qed.
(* 0x8c3a8 `not s2,s6` (xori s2,s6,-1): s2 = 2^64 - 1 - list *)
Lemma scb_xor_m1 : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x (2 ^ 64 - 1) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. assert (Hones : Z.ones 64 = 2 ^ 64 - 1) by reflexivity. rewrite <- Hones.
assert (D : Z.land x (Z.lxor x (Z.ones 64)) = 0).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [H|H].
  - rewrite Z.testbit_ones by lia. replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia).
    replace (n <? 64) with true by (symmetry; apply Z.ltb_lt; lia). destruct (Z.testbit x n); reflexivity.
  - assert (H0 : Z.testbit x n = false).
    { rewrite <- (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_pow2_bits_high. lia. }
    rewrite H0. reflexivity. }
pose proof (Z.add_nocarry_lxor x (Z.lxor x (Z.ones 64)) D) as E.
rewrite <- (Z.lxor_assoc x x (Z.ones 64)), Z.lxor_nilpotent, Z.lxor_0_l in E. lia.
Qed.
(* 0x8c3d0 `bltu s2,s5`: ~list < o is false, since o <= 12k <= 12n and list + 12n + 1 <= 2^64 *)
Lemma scb_trap_3d0 : forall list n o, 0 <= list -> list + 12 * n + 1 <= 2 ^ 64 -> 0 <= o <= 12 * n ->
~ (2 ^ 64 - 1 - list < o).
Proof. intros list n o H1 H2 H3. lia. Qed.
(* 0x8c3e4 `bltu s8,a0`: s8 = ids + 4k does not wrap below ids *)
Lemma scb_trap_3e4 : forall pids n k, 0 <= pids -> pids + 4 * n < 2 ^ 64 -> 0 <= k < n ->
~ ((pids + 4 * k) mod 2 ^ 64 < pids).
Proof. intros pids n k H1 H2 H3. rewrite Z.mod_small by lia. lia. Qed.
(* 0x8c3f0 `beqz a0`, a0 = snez(ids) xor seqz(ids + 4k) *)
Lemma scb_trap_3f0 : forall pids n k, 0 < pids -> pids + 4 * n < 2 ^ 64 -> 0 <= k < n ->
Z.lxor (if pids =? 0 then 0 else 1) (if (pids + 4 * k) mod 2 ^ 64 =? 0 then 1 else 0) <> 0.
Proof.
intros pids n k H1 H2 H3. rewrite Z.mod_small by lia.
replace (pids =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
replace (pids + 4 * k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
change (Z.lxor 1 0 <> 0). intros Hc. discriminate Hc.
Qed.
(* 0x8c3f4 `beqz s9`, s9 = seqz(ids & 3) & snez(ids) *)
Lemma scb_trap_3f4 : forall pids, pids <> 0 -> pids mod 4 = 0 ->
Z.land (if Z.land pids 3 =? 0 then 1 else 0) (if pids =? 0 then 0 else 1) = 1.
Proof.
intros pids H1 H2.
assert (E : Z.land pids 3 = pids mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
rewrite E, H2. replace (pids =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.
(* the load4 check of ids[k] (0x8c404 .. 0x8c438): an addressable 4-aligned word has shadow 0 or a shadow above
   (x & 7) + 3, so `bnez` falls through or `blt a2,a0` jumps back to the load: the report 0x8c440 is not reached *)
Lemma scb_ld4_ok : forall (rd : reader) x, 0 <= x -> x mod 4 = 0 -> range_addressable rd SHADOW_OFF x 4 ->
exists s, rd (shadow_of_addr SHADOW_OFF x) = Some s /\ (s = 0 \/ x mod 8 + 3 < s).
Proof.
intros rd x H0 H4 HR. destruct (HR (x + 3) ltac:(lia)) as (s & Hs & Hok).
assert (G : 8 * (x / 8) <= x + 3 <= 8 * (x / 8) + 7).
{ pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
  assert (x mod 8 = 0 \/ x mod 8 = 4).
  { pose proof (Z.div_mod x 4 ltac:(lia)) as D4. rewrite H4 in D4. lia. }
  lia. }
rewrite (shadow_of_addr_same_granule SHADOW_OFF x (x + 3) G) in Hs.
exists s. split; [exact Hs|]. destruct Hok as [Hok|[Hok _]]; [left; exact Hok|right].
assert (E : (x + 3) mod 8 = x mod 8 + 3).
{ pose proof (Z.div_mod x 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M.
  assert (x mod 8 = 0 \/ x mod 8 = 4).
  { pose proof (Z.div_mod x 4 ltac:(lia)) as D4. rewrite H4 in D4. lia. }
  symmetry. apply Z.mod_unique with (q := x / 8); lia. }
lia.
Qed.

(* ---------- the realigned frame: sp1 = (sp - 192) & -32 ---------- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the symbolic value of sp after `addi sp,sp,-192; andi sp,sp,-32` (0x8c1c4, 0x8c204) *)
Lemma scb_denot_and32 : forall E n v, ew E n = Z_to_bv 64 v -> 192 <= v < 2 ^ 64 ->
sv_denot E (SAlu ALU_AND (SOff n (-192)) (SLit (-32))) = Z_to_bv 64 (32 * ((v - 192) / 32)).
Proof.
intros E n v Hn Hv.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_AND (SOff n (-192)) (SLit (-32))))). f_equal.
change (U E (SAlu ALU_AND (SOff n (-192)) (SLit (-32))) = 32 * ((v - 192) / 32)).
rewrite U_SAlu, U_SOff, U_SLit, Hn. cbn [zalu_raw]. rewrite unsigned_lit_small by lia.
unfold zcanon, M64. rewrite (Z.mod_small (v + -192)) by lia.
replace (-32 mod 2 ^ 64) with (2 ^ 64 - 32) by reflexivity.
rewrite snt_land_m32 by lia. replace (v + -192) with (v - 192) by lia.
pose proof (Z.div_pos (v - 192) 32 ltac:(lia) ltac:(lia)). pose proof (Z.mul_div_le (v - 192) 32 ltac:(lia)).
apply Z.mod_small. lia.
Qed.

(* `mv s1, sp` (0x8c208) is `addi s1, sp, 0` *)
Lemma scb_denot_add0 : forall E e, sv_denot E (SAlu ALU_ADD e (SLit 0)) = sv_denot E e.
Proof.
intros E e. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD e (SLit 0)))).
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E e)). f_equal.
change (U E (SAlu ALU_ADD e (SLit 0)) = U E e). rewrite U_SAlu, U_SLit. cbn [zalu_raw].
unfold zcanon, M64. rewrite (Z.mod_0_l (2 ^ 64)) by lia. rewrite Z.add_0_r.
apply Z.mod_small. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as H. unfold U. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma scb_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* sp1 lies 192 or 208 bytes below the entry sp, 32-aligned *)
Lemma scb_sp1_facts : forall sp, sp mod 16 = 0 -> 2 ^ 46 <= sp ->
sp - 208 <= 32 * ((sp - 192) / 32) <= sp - 192 /\ (32 * ((sp - 192) / 32)) mod 32 = 0 /\
(32 * ((sp - 192) / 32) - sp) mod 16 = 0.
Proof.
intros sp H16 Hlo.
pose proof (Z.div_mod (sp - 192) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (sp - 192) 32 ltac:(lia)) as M.
assert (Hm : (sp - 192) mod 32 = 0 \/ (sp - 192) mod 32 = 16).
{ pose proof (Z.div_mod sp 16 ltac:(lia)) as D2. rewrite H16 in D2. lia. }
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|].
destruct Hm as [Hm|Hm].
- replace (32 * ((sp - 192) / 32) - sp) with (-192) by lia. reflexivity.
- replace (32 * ((sp - 192) / 32) - sp) with (-208) by lia. reflexivity.
Qed.

Lemma scb_not_in_ranges : forall (L : list (Z * Z)) lo hi,
forallb (fun r => (hi <=? fst r) || (fst r + snd r <=? lo)) L = true ->
forall a, lo <= a < hi -> ~ Exists (in_zr a) L.
Proof.
intros L lo hi HL a Ha HE. apply Exists_exists in HE as (r & Hr & Hin).
pose proof (proj1 (forallb_forall _ _) HL r Hr) as Hb. cbn beta in Hb.
apply Bool.orb_true_iff in Hb. unfold in_zr in Hin.
destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* ---------- the symbolic state at the entry 0x8c1c4, up to the call of __asan_stack_malloc_1 ---------- *)
(* the regions the walk writes or reads before its first call: the word `sd zero,0(sp)` stores (entry sp - 192), the
   thirteen saved registers (entry sp - 104 .. entry sp), the two words `sd a1,48(s1)` (ids) and `sd a1,56(s1)` (the
   shadow base) store (atom 34 = sp1), the shadow base's GOT word and cell (atom 32 = SB), the use-after-return
   flag's GOT word and cell (atom 33 = the cell). sp1 + 48 >= entry sp - 160, so the four stack pieces are apart in
   both cases of the realignment. The words at sp1 + 8 .. sp1 + 40 and sp1 + 80 are stored after the call (the
   frame address at sp1 + 16 can be the word `sd zero` stored, when sp1 = entry sp - 208), so the walk seats them
   from the call's post. *)
Definition scb_regions0 : smem := [
 YP09.mkRegion (Some 2%nat) (-192) (-184) (-192) (-184) [];
 YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [];
 YP09.mkRegion (Some 34%nat) 48 64 48 64 [];
 got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition scb_facts0 : facts :=
mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5)] [] [].
Definition ss_scb0 : sstate := mkSS AF_sup_chain sr_atoms scb_regions0 None scb_facts0.

(* the class-1 side-stack frame (atom 1028 = its address F, 128 bytes; atom 1040 = its flag cell, the word at
   F + 120; atom 1041 = its shadow SB + F / 8, 16 bytes), as answer_code_aux's fr_hdr / fr_flg / fr_shd: the header
   F + 0 .. F + 24 (magic, descriptor 0x1dfad, pc 0x8c1c4) is written at 0x8c29c .. 0x8c2a8, the flag word read at
   0x8c4dc, the shadow bytes written at 0x8c2b8 .. 0x8c2ec, 0x8c314 / 0x8c318, 0x8c344 .. 0x8c350,
   0x8c378 / 0x8c380 and 0x8c49c .. 0x8c4d8 *)
Definition scb_fr_hdr : YP09.region := YP09.mkRegion (Some 1028%nat) 0 32 0 24 [].
Definition scb_fr_flg : YP09.region :=
YP09.mkRegion (Some 1028%nat) 120 128 120 120 [YP09.mkChunk 120 (CVal 8 (SOff 1040 0))].
Definition scb_fr_shd : YP09.region := YP09.mkRegion (Some 1041%nat) 0 16 0 16 [].
(* the shadow address of the frame as the walk computes it: (F >> 3) + SB (0x8c288, 0x8c2b4) *)
Definition scb_shx_F : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 1028 0) (SLit 3)) (SOff 32 0).

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the addresses the auipc/addi and auipc/ld pairs denote, from the statement's object bridge *)
Lemma scb_vals : cmd_val_objs ->
VAL (A_OBJ 0) = 0xa5f50 /\ VAL (A_OBJ 1) = 0xa5fa8 /\ VAL (A_OBJ 12) = 0xb0c38 /\ VAL (A_OBJ 51) = 0x21f40 /\
VAL (A_OBJ 77) = 0x1dfad /\ VAL (A_OBJ 78) = 0x8c1c4 /\ VAL (A_OBJ 79) = 0x21f20 /\ VAL (A_OBJ 80) = 0x21f60.
Proof.
intros VOBJS. pose proof scb_objs as (O0 & O1 & O12 & O51 & O77 & O78 & O79 & O80).
rewrite (VOBJS 0%nat ltac:(vm_compute; lia)), (VOBJS 1%nat ltac:(vm_compute; lia)),
  (VOBJS 12%nat ltac:(vm_compute; lia)), (VOBJS 51%nat ltac:(vm_compute; lia)),
  (VOBJS 77%nat ltac:(vm_compute; lia)), (VOBJS 78%nat ltac:(vm_compute; lia)),
  (VOBJS 79%nat ltac:(vm_compute; lia)), (VOBJS 80%nat ltac:(vm_compute; lia)).
repeat split; assumption.
Qed.

(* the call targets: each program callee's entry is BASE + AF_<fn>, from the walk fact cmd_sig_prog *)
Section s.
Hypothesis SIGP : cmd_sig_prog.
Lemma scb_sigs : SIG CS_record = BASE + AF_record /\ SIG CS_xmalloc = BASE + AF_xmalloc /\
  SIG CS_arg_s = BASE + AF_arg_s /\ SIG CS_rec_shape_of = BASE + AF_rec_shape_of /\
  SIG CS_answer = BASE + AF_answer.
Proof.
pose proof scb_prog_syms as (P1 & P2 & P3 & P4 & P5). pose proof scb_af as (A1 & A2 & A3 & A4 & A5).
rewrite (SIGP _ P1), (SIGP _ P2), (SIGP _ P3), (SIGP _ P4), (SIGP _ P5), A1, A2, A3, A4, A5.
repeat split; reflexivity.
Qed.
End s.

Section e.
Variable B : asyms.
(* the walk hypotheses (cgif's names, as answer_code_aux's): the entry lemma takes TL and TLF, the shadow facts take
   HB (CmdBSyms, lib/B/YF0m.v) *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis HB : YF0m.CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* ---------- shadow bytes of the record's const cells (Tfib_const_shadow, lib/B/YF0m.v:2318) ---------- *)
Definition scb_shval (a : Z) : option Z :=
match YF0x.cell_lookup YF0m.Tfib_const_shadow (ANum a) with
| Some (ACell (ANum a') w (AV (ANum v))) => if (a' =? a) && Nat.eqb w 1 then Some (v mod 256) else None
| _ => None
end.

Lemma scb_shval_rd : forall ly S (W : world SEGS) mem md a v, AR SEGS B ly S W mem md ->
scb_shval a = Some v -> rdW W mem a = Some v.
Proof.
intros ly S W mem md a v HAR Hv. unfold scb_shval in Hv. revert Hv.
destruct (YF0x.cell_lookup YF0m.Tfib_const_shadow (ANum a)) as [[e w av]|] eqn:L; [|intros H; discriminate H].
destruct e; try (cbn; intros H; discriminate H). rename z into a'.
destruct av as [e'|mk mv]; [|cbn; intros H; discriminate H].
destruct e'; try (cbn; intros H; discriminate H). rename z into vv.
cbn.
destruct (Z.eqb_spec a' a) as [Ea|Ha]; [subst a'|cbn; intros H; discriminate H].
destruct (Nat.eqb_spec w 1) as [Ew|Hw]; [subst w|cbn; intros H; discriminate H].
cbn. intros Hv. injection Hv as <-.
pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (YF0m.ts_const B HB ly) in HC.
assert (Hin : In (ACell (ANum a) 1 (AV (ANum vv))) (YF0m.Tfib_const ly)).
{ unfold YF0m.Tfib_const. apply in_app_iff. right. apply in_app_iff. right. exact (YF0x.cell_lookup_In _ _ _ L). }
pose proof (proj1 (Forall_forall _ _) HC _ Hin) as Hc. unfold cell_holds in Hc. cbn [c_at c_w c_val aeval] in Hc.
specialize (Hc 0%nat ltac:(lia)). replace (a + Z.of_nat 0) with a in Hc by lia. rewrite Hc. f_equal.
unfold le_byte. replace (8 * Z.of_nat 1) with 8 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. apply Z.mod_mod. lia.
Qed.

(* the stack-protector GOT word the musl bodies under the snprintf and sprintf wrappers read (aguard_ok's first
   half): a const cell of the record (lib/B/YF0m.v:231 `z8 (ANum 0xa6bf8) 0x604158`) *)
Lemma scb_guard_got : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
rdword (rdW W mem) 0xa6bf8 = Some 0x604158.
Proof.
intros ly S W mem md HAR. pose proof (am_const _ _ _ _ (proj1 HAR)) as HC. rewrite (YF0m.ts_const B HB ly) in HC.
assert (Hin : In (z8 (ANum 0xa6bf8) 0x604158) (YF0m.Tfib_const ly)).
{ apply (YF0x.cell_lookup_In _ (ANum 0xa6bf8)). vm_compute. reflexivity. }
eapply rdword_cell; [lia | exact (proj1 (Forall_forall _ _) HC _ Hin)].
Qed.

Lemma scb_visl : forall ly S (W : world SEGS) mem md lo offs, AR SEGS B ly S W mem md ->
forallb (fun i => match scb_shval (lo + i) with Some _ => true | None => false end) offs = true ->
forall i, In i offs -> rdW W mem (lo + i) <> None.
Proof.
intros ly S W mem md lo offs HAR Hb i Hi.
pose proof (proj1 (forallb_forall _ _) Hb i Hi) as Hv. cbv beta in Hv.
destruct (scb_shval (lo + i)) as [v|] eqn:E; [|discriminate Hv].
rewrite (scb_shval_rd ly S W mem md (lo + i) v HAR E). discriminate.
Qed.

(* a literal of n bytes inside one granule whose shadow byte is s, with n <= s < 8: range_addressable *)
Lemma scb_rng_lit : forall ly S (W : world SEGS) mem md a n s, AR SEGS B ly S W mem md ->
a mod 8 = 0 -> 0 < n <= s -> s < 8 -> scb_shval (SHADOW_OFF + a / 8) = Some s ->
range_addressable (rdW W mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n s HAR Ha Hn Hs Hv x Hx. exists s.
pose proof (Z.div_mod a 8 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
assert (E : x / 8 = a / 8) by (symmetry; apply Z.div_unique with (r := x - a); lia).
split.
- unfold shadow_of_addr. rewrite E. exact (scb_shval_rd ly S W mem md _ s HAR Hv).
- right. split; [|exact Hs]. rewrite <- (Z.mod_unique x 8 (a / 8) (x - a)) by lia. lia.
Qed.

Lemma scb_hull_of : forall (rd : reader) x n lo, (forall s, lo <= s < lo + 8 -> rd s <> None) ->
shadow_addr x / 8 * 8 = lo -> shadow_addr (x + n - 1) / 8 * 8 = lo -> shadow_hull_vis rd x n.
Proof. intros rd x n lo H E1 E2 s Hs. rewrite E1, E2 in Hs. apply H. lia. Qed.

(* the shadow octet 0x7fffc3e8 .. 0x7fffc3ef ("%d" 0x21f40 -> 03, "chain" 0x21f60 -> 06, the rest f9) *)
Lemma scb_vis_c3e8 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall s, 0x7fffc3e8 <= s < 0x7fffc3e8 + 8 -> rdW W mem s <> None.
Proof.
intros ly S W mem md HAR s Hs. replace s with (0x7fffc3e8 + (s - 0x7fffc3e8)) by lia.
apply (scb_visl ly S W mem md 0x7fffc3e8 [0; 1; 2; 3; 4; 5; 6; 7] HAR); [vm_compute; reflexivity|].
cbn [In]. lia.
Qed.
(* the shadow octet 0x7fffc3e0 .. 0x7fffc3e7: 0x7fffc3e0 is the zero shadow of "worker_env"'s first granule
   (Tfib_zero_shadow's (0x21f00, 8)), the others const cells (" %d" 0x21f20 -> 04) *)
Lemma scb_zsh_21f00_in : In (0x21f00, 8) YF0m.Tfib_zero_shadow.
Proof.
assert (H : existsb (fun r => (fst r =? 0x21f00) && (snd r =? 8)) YF0m.Tfib_zero_shadow = true) by (vm_compute; reflexivity).
apply existsb_exists in H as ([p n] & Hin & Hb). cbn [fst snd] in Hb.
apply andb_prop in Hb as [Hp Hn]. apply Z.eqb_eq in Hp, Hn. subst p n. exact Hin.
Qed.
Lemma scb_vis_c3e0 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
forall s, 0x7fffc3e0 <= s < 0x7fffc3e0 + 8 -> rdW W mem s <> None.
Proof.
intros ly S W mem md HAR s Hs. destruct (Z.eq_dec s 0x7fffc3e0) as [->|Hne].
- pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md (0x21f00, 8) HAR scb_zsh_21f00_in 0
    ltac:(cbn [snd]; change (8 / 8) with 1; lia)) as Z0.
  cbn [fst] in Z0. replace (shadow_of_addr SHADOW_OFF 0x21f00 + 0) with 0x7fffc3e0 in Z0 by reflexivity.
  rewrite Z0. discriminate.
- replace s with (0x7fffc3e0 + (s - 0x7fffc3e0)) by lia.
  apply (scb_visl ly S W mem md 0x7fffc3e0 [1; 2; 3; 4; 5; 6; 7] HAR); [vm_compute; reflexivity|].
  cbn [In]. lia.
Qed.

(* the formats and the verb: their shadow is usable, as the runtime entries' aread_ok and astr_argA's read-only arm
   ask (the A walk carries these as the named hypotheses ZSH_lit_* / HULL_lit_*; on B they follow from AR and HB) *)
Lemma scb_rng_21f40 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21f40 3.
Proof. intros ly S W mem md HAR. apply (scb_rng_lit ly S W mem md 0x21f40 3 3 HAR); [reflexivity | lia | lia | vm_compute; reflexivity]. Qed.
Lemma scb_rng_21f20 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21f20 4.
Proof. intros ly S W mem md HAR. apply (scb_rng_lit ly S W mem md 0x21f20 4 4 HAR); [reflexivity | lia | lia | vm_compute; reflexivity]. Qed.
Lemma scb_rng_21f60 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
range_addressable (rdW W mem) SHADOW_OFF 0x21f60 6.
Proof. intros ly S W mem md HAR. apply (scb_rng_lit ly S W mem md 0x21f60 6 6 HAR); [reflexivity | lia | lia | vm_compute; reflexivity]. Qed.
Lemma scb_hull_21f40 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21f40 3.
Proof. intros ly S W mem md HAR. apply (scb_hull_of _ _ _ 0x7fffc3e8 (scb_vis_c3e8 ly S W mem md HAR)); reflexivity. Qed.
Lemma scb_hull_21f20 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21f20 4.
Proof. intros ly S W mem md HAR. apply (scb_hull_of _ _ _ 0x7fffc3e0 (scb_vis_c3e0 ly S W mem md HAR)); reflexivity. Qed.
Lemma scb_hull_21f60 : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
shadow_hull_vis (rdW W mem) 0x21f60 6.
Proof. intros ly S W mem md HAR. apply (scb_hull_of _ _ _ 0x7fffc3e8 (scb_vis_c3e8 ly S W mem md HAR)); reflexivity. Qed.

(* the format the snprintf / sprintf wrappers read: aread_ok in the entry's window (a literal lies far below the
   stack) *)
Lemma scb_fmt0_aread : forall stk ly S (W : world SEGS) regs mem md, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
0x21f43 <= spZ regs - stk -> aread_ok SEGS stk W regs mem 0x21f40 (Z.of_nat (length scb_fmt0) + 1).
Proof.
intros stk ly S W regs mem md HAR HRO Hsp. change (Z.of_nat (length scb_fmt0) + 1) with 3.
pose proof (scb_lit_21f40_at _ HRO) as HL.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [|unfold ascratch_stk; lia].
  replace a with (0x21f40 + Z.of_nat (Z.to_nat (a - 0x21f40))) by lia.
  rewrite (HL (Z.to_nat (a - 0x21f40)) ltac:(change (length RO_lit_21f40) with 3%nat; lia)). discriminate. }
split; [left; unfold kLowMemEnd; lia|]. split; [exact (scb_rng_21f40 ly S W mem md HAR)|].
intros _. exact (scb_hull_21f40 ly S W mem md HAR).
Qed.
Lemma scb_fmt1_aread : forall stk ly S (W : world SEGS) regs mem md, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
0x21f24 <= spZ regs - stk -> aread_ok SEGS stk W regs mem 0x21f20 (Z.of_nat (length scb_fmt1) + 1).
Proof.
intros stk ly S W regs mem md HAR HRO Hsp. change (Z.of_nat (length scb_fmt1) + 1) with 4.
pose proof (scb_lit_21f20_at _ HRO) as HL.
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ intros a Ha. split; [|unfold ascratch_stk; lia].
  replace a with (0x21f20 + Z.of_nat (Z.to_nat (a - 0x21f20))) by lia.
  rewrite (HL (Z.to_nat (a - 0x21f20)) ltac:(change (length RO_lit_21f20) with 4%nat; lia)). discriminate. }
split; [left; unfold kLowMemEnd; lia|]. split; [exact (scb_rng_21f20 ly S W mem md HAR)|].
intros _. exact (scb_hull_21f20 ly S W mem md HAR).
Qed.

(* the record's checks over the three literals (lib/B/Prog/CmdChk.v), by computation: the form astr_argA's read-only
   arm states (lib/B/Prog/CmdRep.v:152), and the literals' ends among CmdRo's literal ends *)
Lemma scb_chk_lits : cmd_addr_b 0x21f40 3 = true /\ cmd_hull_b 0x21f40 3 = true /\
  cmd_addr_b 0x21f20 4 = true /\ cmd_hull_b 0x21f20 4 = true /\
  cmd_addr_b 0x21f60 6 = true /\ cmd_hull_b 0x21f60 6 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma scb_ends : In 0x21f42 cmd_ro_ends /\ In 0x21f23 cmd_ro_ends /\ In 0x21f65 cmd_ro_ends.
Proof.
assert (H : forall e, existsb (Z.eqb e) cmd_ro_ends = true -> In e cmd_ro_ends).
{ intros e He. apply existsb_exists in He as (x & Hx & Hb). apply Z.eqb_eq in Hb. subst x. exact Hx. }
split; [|split]; apply H; vm_compute; reflexivity.
Qed.
(* the word tails the musl format loops may read after each format's NUL (atail_vis), from cmd_ro_ok's tails *)
Lemma scb_tail_21f42 : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> atail_vis SEGS W mem 0x21f42.
Proof. intros W mem [_ HT] a Ha. exact (HT 0x21f42 (proj1 scb_ends) a Ha). Qed.
Lemma scb_tail_21f23 : forall (W : world SEGS) mem, cmd_ro_ok (rdW W mem) -> atail_vis SEGS W mem 0x21f23.
Proof. intros W mem [_ HT] a Ha. exact (HT 0x21f23 (proj1 (proj2 scb_ends)) a Ha). Qed.

(* rec_shape_of's verb "chain" (0x21f60, 5 bytes and its NUL): astr_argA's read-only arm, for any owned list; the
   read-only membership is the walk's record hypothesis cmd_ro_in (the A walk's CMD_RO_IN) *)
Lemma scb_verb_arg : forall ly S (W : world SEGS) mem md O, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
cmd_ro_in (in_roP SEGS RLO RHI) -> astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) O 0x21f60 (Some scb_verb).
Proof.
intros ly S W mem md O HAR HRO HIN. cbv beta iota zeta delta [astr_argA].
change (Z.of_nat (length scb_verb) + 1) with 6. change (Z.of_nat (length scb_verb)) with 5.
pose proof scb_chk_lits as (_ & _ & _ & _ & C5 & C6).
split; [lia|]. split; [exact (scb_verb_str _ HRO)|]. split; [unfold LMAX; lia|].
right. split; [|split; [exact C5 | split; [exact C6 | exact (proj2 (proj2 scb_ends))]]].
intros i Hi. split; [exact (scb_verb_ro _ HIN i Hi)|]. split.
- rewrite (YF0m.ts_owned B HB). apply (scb_not_in_ranges _ 0x21f60 0x21f66); [vm_compute; reflexivity | lia].
- rewrite (YF0m.ts_errno B HB). unfold YF0m.TFIB_ERRNO. lia.
Qed.
Lemma scb_verb_pre : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> cmd_ro_ok (rdW W mem) ->
cmd_ro_in (in_roP SEGS RLO RHI) -> (Z.of_nat (length scb_verb) <= 16 ->
abytes_atR (rdW W mem) 0x21f60 scb_verb /\
(in_blockA (ablocks B ly S) 0x21f60 (Z.of_nat (length scb_verb)) \/
 astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] 0x21f60 (Some scb_verb))).
Proof.
intros ly S W mem md HAR HRO HIN _. split; [exact (scb_verb_bytes _ HRO)|].
right. exact (scb_verb_arg ly S W mem md [] HAR HRO HIN).
Qed.

(* ---------- the two report edges: the shadow facts that refute them at their branches ---------- *)
(* list[0] (0x8c38c .. 0x8c390): the first granule of xmalloc's fresh block of at least 8 bytes is at zero shadow,
   so `bnez` falls through and the report 0x8c56c is not reached *)
Lemma scb_chk0 : forall ly S (W : world SEGS) mem md p m, AR SEGS B ly S W mem md ->
In (p, m) (ablocks B ly S) -> 8 <= m -> rdW W mem (shadow_of_addr SHADOW_OFF p) = Some 0.
Proof.
intros ly S W mem md p m HAR Hin Hm.
destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as [(Hp & Hn & Hc) _].
assert (Rq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); cbn; lia).
rewrite Rq in Hn, Hc. pose proof (Hc 0 ltac:(split; [lia|]; apply Z.div_str_pos; lia)) as H0.
rewrite Z.add_0_r in H0. rewrite H0.
replace (0 <? m / 8) with true by (symmetry; apply Z.ltb_lt; apply Z.div_str_pos; lia). reflexivity.
Qed.
(* ids[k] (0x8c3f8 .. 0x8c438): the member array premise of the statement makes every member's word addressable *)
Lemma scb_ids_addr : forall ly S (W : world SEGS) mem md pids n (O : list (Z * Z)) k, AR SEGS B ly S W mem md ->
(afobj SEGS B ly S W mem pids (4 * n) \/
 (in_blockA (ablocks B ly S) pids (4 * n) /\ Forall (fun qk => iv_apart pids (4 * n) (fst qk) (snd qk)) O)) ->
0 <= k < n -> range_addressable (rdW W mem) SHADOW_OFF (pids + 4 * k) 4.
Proof.
intros ly S W mem md pids n O k HAR Harr Hk. destruct Harr as [(_ & _ & HR) | ((p & m & Hin & Hlo & Hhi) & _)].
- apply (range_addressable_sub _ _ pids (4 * n)); [exact HR | lia | lia].
- destruct (al_shadow _ _ LAWS ly S W mem md p m HAR Hin) as [HBS _].
  assert (Rq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); cbn; lia).
  apply (block_shadow_range _ _ p (req_size m)); [exact HBS | lia | lia].
Qed.

(* the entry: any stack budget of at least the frame and its realignment (192 + 16) *)
Definition scb_extra (sp1 : Z) : list word := map (Z_to_bv 64) [SB; as_uar_cell B; sp1].

Lemma scb_entry : forall STK W ly S regs mem md ch, 208 <= STK ->
afn_pre SEGS B STK ly S W regs mem md ch ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (scb_extra (32 * ((spZ regs - 192) / 32))))) ss_scb0
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_sup_chain)) mem (seg_rom SEGS))).
Proof.
intros STK W ly S regs mem md ch HSTK HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
pose proof (pa_obj_img 0 ltac:(lia)) as HO0. pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 12 ltac:(lia)) as HO12.
rewrite restrict_mkst_fx.
set (sp1 := 32 * ((spZ regs - 192) / 32)).
destruct (scb_sp1_facts (spZ regs) Hal16 ltac:(lia)) as (Hsp1 & Hsp1a & Hsp1b). fold sp1 in Hsp1, Hsp1a, Hsp1b.
set (E := Eimg (Ereg regs (scb_extra sp1))).
assert (Usp : bv_unsigned (ew E 2) = spZ regs).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 sp1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (U34 : base_val E (Some 34%nat) = sp1) by (apply VB; [exact E34 | lia]).
assert (U0 : base_val E (Some (A_OBJ 0)) = VAL (A_OBJ 0)) by (apply VB; [exact E241 | lia]).
assert (U1 : base_val E (Some (A_OBJ 1)) = VAL (A_OBJ 1)) by (apply VB; [exact E242 | lia]).
assert (U12 : base_val E (Some (A_OBJ 12)) = VAL (A_OBJ 12)) by (apply VB; [exact E253 | lia]).
assert (U33 : base_val E (Some 33%nat) = as_uar_cell B) by (apply VB; [exact E33 | lia]).
assert (U2 : base_val E (Some 2%nat) = spZ regs) by (cbn [base_val]; exact Usp).
unfold ss_scb0. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold scb_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U2. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U34. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
+ rewrite U0. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
[rewrite scb_denot_off0; exact E253 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
+ rewrite U12. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
[rewrite scb_denot_off0; exact E32 | unfold SB; lia | lia |].
rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ rewrite U1. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 33 0) (as_uar_cell B));
[rewrite scb_denot_off0; exact E33 | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kguar).
+ rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | lia | lia |].
rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
- apply pairwise_disjoint_of_extents. unfold scb_regions0, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U2, U34, U0, U1, U12, U33.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [scb_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
rewrite Hal16, Hsp1a. unfold SB. repeat split; lia.
Qed.
End e.
End f.
End d.

Print Assumptions scb_entry.
Print Assumptions scb_verb_arg.
Print Assumptions scb_fmt0_aread.
Print Assumptions scb_fmt1_aread.
Print Assumptions scb_ids_addr.
Print Assumptions scb_chk0.
Print Assumptions scb_xor_m1.
