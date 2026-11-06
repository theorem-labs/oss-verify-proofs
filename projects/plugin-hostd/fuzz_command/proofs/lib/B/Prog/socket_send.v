(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of sup_lv2_worker_set (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan, entry BASE + AF_sup_lv2_worker_set = 0x8c0cc, 28 instructions, 112 bytes): it proves
   a Theorem Labs lane's `tsup_lv2_worker_set_spec` (lib/B/Prog/sup_lv2_worker_set_c.v; statement from a Theorem Labs lane f490061c104, over
   a Theorem Labs lane c022a2f6a88) in the form of cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic
   executor over the position-abstract listing up to each call (the plain runs of lib/B/Prog/PaCallRun.v, no shadow
   access in the function), the callee contracts of record, arg_s and rec_shape_of (taken at the entry's FP state,
   which these apost_base callees keep) through cl_callS_wide / cl_callS_na (lib/B/Prog/PaNoChain.v), and answer's
   FP-existential post (apost_baseF) through PaFx.callS_wideF at the tail jump, which is this function's
   apost_baseF. The frame chains (pass 5, no astack_pres): s0 = worker (a heap pointer) at the four program calls,
   achain_low; at the tail jump s0 and sp are the entry's, afn_pre's chain moved by achain_kept / achain_ly_top.
   It is the B re-walk of the A walk
   lib/A/Prog/sup_lv2_worker_set.v + _s0 .. _s3 (a working branch 5c647899d9f), whose rec_shape_of call,
   tail call of answer and post assembly (sup_lv2_worker_set_s2.v slw_D2 / slw_D3) it follows; B calls record and
   arg_s where A inlines them, so A's segments A, B and s3 become one contract step each. The Generation-N B walk
   lib/B/Prog/sup_lv2_worker_set.v on a working branch 543f2c3645b (template only, not ported) cuts the same
   code at the same return addresses.

   B code (MEASURED from the pinned fuzz_command.asan-ubsan with pyelftools and capstone, symbol-keyed; a Theorem Labs lane's
   gen/dis/sup_lv2_worker_set.s): a 32-byte frame (ra, s0, s1, s2), `mv s0,a1` (worker), `mv s1,a0` (uri);
   record(15) at 0x8c0ec (ret 0x8c0f0), `mv s2,a0` (the slot); arg_s(slot, uri) at 0x8c0f8; arg_s(slot, worker) at
   0x8c104; rec_shape_of(.str.13 = 0x21ee0, 14) at 0x8c114 (the listing's `PHi 10 176; PAddHi 10 10 176 (A_OBJ 75) 0`
   at 0x8c108: a0 = the literal's address, nothing is loaded or stored through the auipc base); the epilogue and the
   tail jump `j answer` (0x8c138) with a0 = slot, a1 = the shape, a2 = 1, at the entry sp.
   Report / trap edges: none. The function has no branch, no `unimp`/`ebreak`, no call to any of the 24
   __asan_report_* entries and 0 UBSan trap sites (a Theorem Labs lane's gen/traps.B.summary); its checks are its callees'
   (record 4, arg_s 5, answer 5 trap sites, rec_shape_of 2 inline checks), refuted in their own walks, whose
   contracts this walk uses. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_lv2_worker_set.v, with its module paths, module names and numbers changed; 671 of its 776 lines of code are new or changed and 999 lines of the source are left out. *)
(* The ASan+UBSan walk of socket_send (plugin-hostd/fuzz_command, image fuzz_command.asan-ubsan, entry
   BASE + AF_socket_send = 0x8cdb4): it proves `tsocket_send_spec` (lib/B/Prog/socket_send_c.v) in the form of
   cgif_file_fuzzer's per-function walks: afn_pre at the entry, the symbolic executor over the position-abstract
   listing up to each call, the runtime's rules at the runtime calls, the callee contract xmalloc_c at the call of
   xmalloc (through cl_callS), the return through `paj_ret_at`, and apost_base at the end.

   It is the B re-walk of the A walk lib/A/Prog/socket_send.v (a working branch 8fcc9317a00), at
   B's addresses (a Theorem Labs lane's gen/dis/socket_send.s, 38 instructions, 0x8cdb4 .. 0x8ce48):
   - prologue (48-byte frame, ra s0 s1 s2 s3 saved); `mv s0,a2`; g_rec by auipc/addi (listing object 44);
     `lw a0,920(s3)`, `addiw a2,a0,1`, then the UBSan trap branch `blt a2,a0` (0x8cde0 -> unimp 0x8ce48);
     `sw a2,920(s3)`; the free wrapper on g_rec.reply (0x8cdf4, __interceptor_trampoline_free 0x589cc);
     memset(&g_rec.reply, 0, 16) through the runtime's entry (0x8ce04, __asan_memset 0x57b18); `blez s0`;
   - size > 0: xmalloc(size) (0x8ce10, xmalloc 0x899b4; B keeps xmalloc as a function where A inlines its malloc
     call, so there is no null-check branch here: xmalloc's contract returns a block), `sd a0,928(s3)`,
     memcpy(reply, buf, size) (0x8ce20, __asan_memcpy 0x5767c), `sd s0,936(s3)`; return size.
   The UBSan trap site 0x8cde0 is refuted at its branch: the symbolic executor's step at 0x8cde0 decides `blt a2,a0`
   with a2 = atom 32 + 1 and a0 = atom 32 by decide_cond2 (lib/Reusable/YP0e.v) from ss_facts0's fact
   0 <= atom 32 <= 2 ^ 31 - 2, so it takes only the fall-through (ss_step_8cde0, ss_ubsan_8cde0 below); the fact is
   the premise `r_nreplies R < 2 ^ 31 - 1` with rec_repA's `0 <= r_nreplies R` (ss_entry_ok). There is no
   __asan_report call in the function.

   The recorder lemmas are a Theorem Labs lane's kit, lib/B/Prog/RecBLemmas.v, bound below under ss_ names: the Section w_full
   forms, and the minimal forms that take xmalloc_c's post as it is (the new block consed onto the old block list:
   recb_fresh_disj_perm_m, recb_not_new_perm_m, recb_awr_new_block_perm_m) and what a callee with an empty footprint
   keeps (recb_call_keeps_m).

   Statement: a Theorem Labs lane's lib/B/Prog/socket_send_c.v at a working branch fc8bcbd8b42 (pass 5: no astack_pres premise; the
   callee and runtime contracts taken at every FP state, the walk applies them at its fx). Facts a Theorem Labs lane states only
   at the pinned image are Section hypotheses under the names of a Theorem Labs lane's lemmas (cmd_palib, cmd_sig_prog_PB,
   cmd_img_facts_tfib) and PRW : prog_rw; the program statics' image facts come from CmdRecRest.cmd_prog_img;
   lib/B/Prog/SocketSendClosed.v discharges them at the pinned image. The frame chain at each call is achain's empty
   case for s0 = size (ss_achain), turned into the wrappers' chain_pre by achain_chain_pre (ss_chain_pre). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr xmalloc_c socket_send_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require CmdRecBase CmdRecRest.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program's statics list of lib/B/Prog/RecBLemmas.v (recb_PG) is the allocator record's TFIB_PROG_STATIC *)
Lemma ss_PG_tfib : recb_PG = TFIB_PROG_STATIC.
Proof. reflexivity. Qed.

(* the symbolic state at the entry: the 48-byte frame, and the two g_rec fields the code reads before the free
   (nreplies at +920, written; reply at +928). Atom 32 is nreplies, atom 33 the reply pointer. g_rec is the
   listing's object 44 (the auipc/addi pair at 0x8cdd0). *)
Definition SS_GR : nat := A_OBJ 44.
Definition ss_grec0 : YP09.region :=
YP09.mkRegion (Some SS_GR) 920 944 920 924 [YP09.mkChunk 920 (CVal 4 (SOff 32 0)); YP09.mkChunk 928 (CVal 8 (SOff 33 0))].
Definition ss_facts0 : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0 (2 ^ 31 - 2) 0)] [] [].
Definition ss_entry : sstate := mkSS AF_socket_send sr_atoms [stack_region 48; ss_grec0] None ss_facts0.
Definition ss_extra (nrep rp : Z) : list word := map (Z_to_bv 64) [nrep; rp].
Definition SS_FP (O : list (Z * Z)) : list (Z * Z) := (A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O.
(* g_rec after the memset: nreplies (atom 32 + 1), reply and reply_size zero; the code writes reply and
   reply_size from here on *)
Definition ss_grec1 : YP09.region :=
YP09.mkRegion (Some SS_GR) 920 944 928 944
[YP09.mkChunk 920 (CVal 4 (SOff 32 1)); YP09.mkChunk 928 (CVal 8 (SLit 0)); YP09.mkChunk 936 (CVal 8 (SLit 0))].
(* the bytes the recorder's representation reads that socket_send does not write: g_rec outside nreplies, reply
   and reply_size; record.spill; the recorder's blocks other than the reply; and the buffer the call copies *)
Definition ss_keep (Q : rlay) (buf size a : Z) : Prop :=
(A_G_REC <= a < A_G_REC + OFF_NREPLIES) \/ (A_G_REC + OFF_STATE <= a < A_G_REC + REC_SIZE) \/
(A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
(exists pn, In pn (lay_rest Q) /\ fst pn <= a < fst pn + snd pn) \/
(0 < size /\ buf <= a < buf + size).

(* UBSan trap site 0x8cde0 (`blt a2,a0` -> unimp 0x8ce48, the signed overflow check of `g_rec.nreplies++`,
   recorder.c:576, gen/trapsites.B.tsv). The executor reaches 0x8cde0 after 11 steps from the entry with
   a0 = SOff 32 0 (`lw a0,920(s3)`, atom 32 = r_nreplies R) and a2 = SOff 32 1 (`addiw a2,a0,1`), its facts still
   ss_facts0, and its step there is the fall-through to 0x8cde4 (ss_step_8cde0): the Branch case of sym_step_pi
   (PaSym.v) decides `decide_cond2 ss_facts0 BC_LT (SOff 32 1) (SOff 32 0) = Some false`. That decision is sound
   (decide_cond2_sound, YP0e.v) under the fact 0 <= atom 32 <= 2 ^ 31 - 2 (ss_ubsan_8cde0), which ss_entry_ok
   proves from the premise `r_nreplies R < 2 ^ 31 - 1` with rec_repA's `0 <= r_nreplies R`; the walk's first run
   (paj_run_shc in tsocket_send_holds) goes through this step by PaRun.sym_run_pi_sound. *)
Lemma ss_step_8cde0 :
ss_pc (fst (sym_run_pi cmd_tpi 11 ss_entry)) = AF_socket_send + 44 /\
ss_facts (fst (sym_run_pi cmd_tpi 11 ss_entry)) = ss_facts0 /\
sr_get (ss_regs (fst (sym_run_pi cmd_tpi 11 ss_entry))) 12%bv = SOff 32 1 /\
sr_get (ss_regs (fst (sym_run_pi cmd_tpi 11 ss_entry))) 10%bv = SOff 32 0 /\
sym_step_pi cmd_tpi (fst (sym_run_pi cmd_tpi 11 ss_entry)) =
PRun (setpc (fst (sym_run_pi cmd_tpi 11 ss_entry)) (AF_socket_send + 48)).
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma ss_ubsan_8cde0 : forall E, facts_ok E ss_facts0 ->
branch_taken BC_LT (sv_denot E (SOff 32 1)) (sv_denot E (SOff 32 0)) = false.
Proof. intros E HG. apply (decide_cond2_sound E ss_facts0 BC_LT _ _ false HG). vm_compute. reflexivity. Qed.

(* cgif's region_kept over aview for a region whose window bytes stay present (lib/A/Prog/answer_code.v
   region_kept_hi2): the call's world may grow *)
Lemma ss_region_kept_hi2 {fx : YK11.FPState} : forall (segs : list Segment) E H H2 (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview segs H2 m2 a = aview segs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept segs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros segs E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview segs). apply Hav. exact Ha.
- intros _. apply (apresent_writable segs). apply Hp. exact Ha.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the statement's Section hypotheses (socket_send_c.v, Section e): the callee and runtime contracts at every FP
   state; the walk takes them at this Section's fx *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis VOBJS : cmd_val_objs.
(* the walk's hypotheses: HB, the allocator record (lib/B/YF0m.v, Record CmdBSyms); MTL, the meter's laws; and the
   facts a Theorem Labs lane states only at the pinned image (PI := PB_cmd), here under the names of a Theorem Labs lane's lemmas, so that a
   closing file at PB_cmd discharges each by the lemma of that name:
   - cmd_palib (lib/B/Prog/CmdRecRest.v): the PALib record (the free trampoline's pc);
   - cmd_sig_prog_PB (lib/B/Prog/CmdRecRest.v): the call target of every program function, for the call of xmalloc;
   - cmd_img_facts_tfib (lib/B/Prog/CmdRecImg.v): the image facts, from which CmdRecRest.cmd_prog_img gives that the
     program's statics are image bytes;
   - PRW : prog_rw SEGS B (lib/Reusable/YCbq.v): the program's statics are writable (CmdRecCells.PROG_WRITABLE's
     premise), which the symbolic regions' write windows over g_rec and the memset of g_rec.reply ask for.
   LAWS is not a hypothesis: AR_laws_ok (lib/Reusable/YG0q.v) proves it. *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_palib : forall B0, CmdBSyms B0 -> PALib B0.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @CmdRecBase.cmd_img_facts SK SEGS B0.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let TL : PALib B := cmd_palib B HB.
Let IMG : @CmdRecBase.cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a :=
  fun a Ha => CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG a (eq_ind _ (fun l => Exists (in_zr a) l) Ha _ ss_PG_tfib).
Let cmd_prog_writable : forall ly S (W : world SEGS) mem md a, AR SEGS B ly S W mem md ->
Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a :=
  fun ly S W mem md a _ Ha => PRW (mrestrict (w_H W) mem) a
    (eq_ind _ (fun l => Exists (in_zr a) l) Ha _ (eq_trans ss_PG_tfib (eq_sym (ts_prog B HB)))).
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* the kit's walk lemmas (lib/B/Prog/RecBLemmas.v Section w_full) at this walk's hypotheses (the free rule at this
   fx), and the four facts of Section ssk above *)
Let ss_grec_awr := recb_grec_awr B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_grec_writable := recb_grec_writable B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_rep_addressable := recb_rep_addressable B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_rep_hull := recb_rep_hull B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_kept_prog := recb_kept_prog B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_free_any := recb_free_any B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_val_mem_frame := recb_val_mem_frame B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_ablocks_nodup := recb_ablocks_nodup B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_heap_noimg := recb_heap_noimg B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_heap_apart := recb_heap_apart B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_lay_rest_L2 := recb_lay_rest_L2 B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_run_keeps := recb_run_keeps B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_free_keeps := recb_free_keeps B MT (AFREE4 fx) HB cmd_prog_img cmd_prog_writable.
Let ss_fresh_disj := recb_fresh_disj_perm_m B.
Let ss_call_keeps := recb_call_keeps_m B HB cmd_prog_img.
Let ss_not_new := recb_not_new_perm_m B cmd_prog_img.
Let ss_awr_new_block := recb_awr_new_block_perm_m B.

Lemma ss_grec_val : VAL SS_GR = A_G_REC.
Proof. unfold SS_GR. rewrite (VOBJS 44%nat) by (vm_compute; lia). vm_compute. reflexivity. Qed.

Lemma ss_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (SS_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia]. Qed.

(* the call target of xmalloc (a Theorem Labs lane's gen/funcs.tsv: 0x899b4 = BASE + AF_xmalloc) *)
Lemma ss_sig_xmalloc : SIG CS_xmalloc = BASE + AF_xmalloc.
Proof. rewrite (cmd_sig_prog_PB CS_xmalloc ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.

(* s0 holds the size (a 32-bit int) at every call, never a frame pointer: the unwinder's chain is empty *)
Lemma ss_achain : forall lyc rd sp (regsT : bvmap 5 word) size,
-2 ^ 31 <= size < 2 ^ 31 -> (size < 0 -> ly_top lyc <= 2 ^ 47) ->
getr regsT 8 = w64 size -> achain lyc rd sp (s0Z regsT) [].
Proof.
intros lyc rd sp regsT size Hs Ht H8. pose proof asan_consts as (C1 & _).
left. split; [|reflexivity]. unfold s0Z. rewrite H8. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64).
destruct (Z_lt_le_dec size 0) as [Hn|Hn].
- right; left. assert (Hm : size mod 2 ^ 64 = size + 2 ^ 64).
  { rewrite <- (Z.mod_add size 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
  specialize (Ht Hn). rewrite Hm. lia.
- left. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ss_chain_pre : forall lyc rd (regsT : bvmap 5 word) size,
-2 ^ 31 <= size < 2 ^ 31 -> (size < 0 -> ly_top lyc <= 2 ^ 47) -> alloc_ceiling <= spZ regsT ->
getr regsT 8 = w64 size -> 4096 <= raZ regsT -> chain_pre lyc rd regsT [].
Proof.
intros lyc rd regsT size Hs Ht Hsp H8 Hra.
apply (achain_chain_pre lyc rd (spZ regsT) (s0Z regsT) [] regsT); [| lia | reflexivity | exact Hra].
exact (ss_achain lyc rd (spZ regsT) regsT size Hs Ht H8).
Qed.

Lemma ss_region_kept_grec : forall E (W W2 : world SEGS) memT mem2 lo hi wlo whi cs,
bv_unsigned (ew E SS_GR) = A_G_REC ->
(forall a, A_G_REC + lo <= a < A_G_REC + hi -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memT a) ->
(forall a, A_G_REC + wlo <= a < A_G_REC + whi -> writable_at SEGS (mrestrict (w_H W2) mem2) a) ->
region_kept SEGS E (mrestrict (w_H W) memT) (mrestrict (w_H W2) mem2) (YP09.mkRegion (Some SS_GR) lo hi wlo whi cs).
Proof.
intros E W W2 memT mem2 lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

Lemma ss_entry_ok : forall ly S W regs mem md ch nrep rp,
afn_pre SEGS B SOCKET_SEND_STK ly S W regs mem md ch ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 920) 4 nrep -> 0 <= nrep <= 2 ^ 31 - 2 ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 928) 8 rp -> 0 <= rp < 2 ^ 64 ->
(forall o, 920 <= o < 924 -> writable_at SEGS (mrestrict (w_H W) mem) (A_G_REC + o)) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ss_extra nrep rp))) ss_entry
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_socket_send)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch nrep rp HPRE V920 Rn V928 Rrp HW.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ss_extra nrep rp))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 nrep) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rp) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (UGR : bv_unsigned (ew E SS_GR) = A_G_REC).
{ subst E. rewrite Eimg_img by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia). rewrite ss_grec_val. apply unsigned_lit_small. unfold A_G_REC. lia. }
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, ss_grec0. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold SOCKET_SEND_STK, ASTACK in *. lia.
  + rewrite UGR. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [exact HW|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ A_G_REC 920 4 _ nrep); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V920].
    * apply (chunk_ok_val SEGS E _ A_G_REC 928 8 _ rp); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact V928].
- apply pairwise_disjoint_of_extents. unfold stack_region, ss_grec0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, UGR.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold A_G_REC, SOCKET_SEND_STK, ASTACK in *.
  repeat split; lia.
- split; [|split; [exact I | exact I]]. cbn [ss_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, unsigned_lit_small by lia. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SOCKET_SEND_STK, ASTACK in *. repeat split; lia.
Qed.

(* where a kept byte lies *)
Lemma ss_keep_info : forall ly S (W : world SEGS) mem md R Q O buf size L2,
AR SEGS B ly S W mem md ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
(0 < size -> in_blockA (ablocks B ly S) buf size /\ Forall (fun qk => iv_apart buf size (fst qk) (snd qk)) O) ->
Permutation (ablocks B ly S) (oblk (l_reply Q) ++ L2) ->
forall a, ss_keep Q buf size a ->
0 <= a < alloc_ceiling /\ ~ (A_G_REC + OFF_NREPLIES <= a < A_G_REC + OFF_STATE) /\
(Exists (in_zr a) recb_PG \/ exists b m, In (b, m) L2 /\ b <= a < b + req_size m /\ ~ in_img SEGS a).
Proof.
intros ly S W mem md R Q O buf size L2 HAR HA HO Hbuf HP a Hk.
pose proof asan_consts as (C1 & _).
assert (Hheap : forall b m, In (b, m) L2 -> b <= a < b + req_size m -> 0 <= a < alloc_ceiling /\ ~ in_img SEGS a).
{ intros b m Hbm Ha.
  assert (Hin : In (b, m) (ablocks B ly S)) by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hc & _).
  split; [lia | exact (ss_heap_noimg ly S W mem md b m a HAR Hin Ha)]. }
assert (Himg : Exists (in_zr a) recb_PG -> 0 <= a < alloc_ceiling).
{ intros HPG. pose proof (pa_img_range a (cmd_prog_img a HPG)) as Hr. lia. }
assert (Hgr : A_G_REC + OFF_NREPLIES <= a < A_G_REC + OFF_STATE -> in_img SEGS a).
{ intros Ha. apply cmd_prog_img. apply recb_grec_in. unfold OFF_NREPLIES, OFF_STATE, REC_SIZE in *. lia. }
destruct Hk as [Hg | [Hg | [Hs | [(pn & Hpn & Ha) | (Hsz & Hb)]]]].
- assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold OFF_NREPLIES, REC_SIZE in *; lia).
  split; [exact (Himg HPG)|]. split; [lia | left; exact HPG].
- assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_grec_in; unfold OFF_STATE, REC_SIZE in *; lia).
  split; [exact (Himg HPG)|]. split; [unfold OFF_STATE, OFF_NREPLIES in *; lia | left; exact HPG].
- assert (HPG : Exists (in_zr a) recb_PG) by (apply recb_spill_in; lia).
  split; [exact (Himg HPG)|]. split; [unfold A_REC_SPILL, A_G_REC, SC_SIZE, OFF_NREPLIES, OFF_STATE in *; lia | left; exact HPG].
- pose proof (ss_lay_rest_L2 ly S (rdW W mem) R Q L2 HA HP pn Hpn) as HL.
  destruct pn as [b m]. cbn [fst snd] in Ha.
  pose proof (req_size_pos m ltac:(lia)) as Hq.
  destruct (Hheap b m HL ltac:(lia)) as [Hr Hni].
  split; [exact Hr|]. split; [intros Hx; exact (Hni (Hgr Hx))|]. right. exists b, m. split; [exact HL|]. split; [lia | exact Hni].
- destruct (Hbuf Hsz) as [(p & k & Hin & H1 & H2) Hap].
  assert (Hpk : In (p, k) L2).
  { apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [Hr | H]; [|exact H]. exfalso.
    assert (HpO : In (p, k) O) by (apply HO; rewrite lay_blocks_rest; apply in_or_app; right; exact Hr).
    rewrite Forall_forall in Hap. pose proof (Hap (p, k) HpO) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
  pose proof (req_size_pos k ltac:(lia)) as Hq.
  destruct (Hheap p k Hpk ltac:(lia)) as [Hr Hni].
  split; [exact Hr|]. split; [intros Hx; exact (Hni (Hgr Hx))|]. right. exists p, k. split; [exact Hpk|]. split; [lia | exact Hni].
Qed.

(* the post-condition's recorder and block facts, from the final reader and the final block list (a permutation of
   the new reply block, if any, and the blocks after the free) *)
Lemma ss_post_Q : forall ly S (W : world SEGS) mem md R Q O buf size x L2 lyF SF (WF : world SEGS) memF mdF q',
AR SEGS B ly S W mem md -> AR SEGS B lyF SF WF memF mdF ->
arep_at (ablocks B ly S) (rdW W mem) A_G_REC A_REC_SPILL R Q ->
(forall pn, In pn O <-> In pn (lay_blocks Q)) ->
r_nreplies R < 2 ^ 31 - 1 ->
Permutation (ablocks B ly S) (oblk (l_reply Q) ++ L2) ->
Permutation (ablocks B lyF SF) (oblk q' ++ L2) ->
(forall a, ss_keep Q buf size a -> rdW WF memF a = rdW W mem a) ->
aval_mem (rdW WF memF) (A_G_REC + OFF_NREPLIES) 4 (r_nreplies R + 1) ->
areply_at (ablocks B lyF SF) (rdW WF memF) A_G_REC (match x with [] => None | _ :: _ => Some x end) q' ->
exists O', rec_repA B lyF SF (rdW WF memF) (fst (socket_send_m R x)) O' /\
(forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B lyF SF) -> (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O') /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyF SF)).
Proof.
intros ly S W mem md R Q O buf size x L2 lyF SF WF memF mdF q' HAR HARF HA HO Hnr HP EF HK Hn Hrep.
pose proof (ss_ablocks_nodup _ _ _ _ _ HAR) as ND0.
pose proof (Permutation_NoDup EF (ss_ablocks_nodup _ _ _ _ _ HARF)) as NDF.
pose proof (Permutation_NoDup HP ND0) as ND0'.
pose proof (ss_lay_rest_L2 ly S (rdW W mem) R Q L2 HA HP) as HL.
pose proof HA as (_ & _ & _ & _ & _ & _ & HSC & _). destruct HSC as (_ & _ & _ & _ & _ & _ & _ & Rn & _).
exists (lay_rest Q ++ oblk q'). split; [|split; [|split]].
- unfold socket_send_m, rec_socket_send. cbn [fst].
  apply (rec_repA_set_reply B ly S (rdW W mem) R Q lyF SF (rdW WF memF) (r_nreplies R + 1) _ q' HA).
  + intros i Hi. apply HK. left. lia.
  + intros i Hi. apply HK. right; left. unfold OFF_STATE, REC_SIZE in *. lia.
  + intros i Hi. apply HK. right; right; left. lia.
  + intros pn Hpn. split; [apply (Permutation_in _ (Permutation_sym EF)); apply in_or_app; right; exact (HL pn Hpn)|].
    intros i Hi. apply HK. right; right; right; left. exists pn. split; [exact Hpn | lia].
  + exact Hn.
  + lia.
  + exact Hrep.
  + intros [p n] Hq. cbn [fst snd].
    assert (Hpin : In (p, n) (ablocks B lyF SF)) by (apply (Permutation_in _ (Permutation_sym EF)); apply in_or_app; left; rewrite Hq; left; reflexivity).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HARF Hpin) as (_ & _ & _ & _ & _ & _ & Hn0).
    split; [apply (ss_heap_apart lyF SF WF memF mdF p n _ _ HARF Hpin ltac:(lia)); [unfold REC_SIZE; lia | intros a Ha; apply cmd_prog_img, recb_grec_in; exact Ha]|].
    split; [apply (ss_heap_apart lyF SF WF memF mdF p n _ _ HARF Hpin ltac:(lia)); [unfold SC_SIZE; lia | intros a Ha; apply cmd_prog_img, recb_spill_in; exact Ha]|].
    intros Hin. apply in_map_iff in Hin as ([b m] & Hb & Hbm). cbn [fst] in Hb. subst b.
    pose proof (HL (p, m) Hbm) as HL2.
    assert (EF' : Permutation (ablocks B lyF SF) ((p, n) :: L2)) by (rewrite Hq in EF; exact EF).
    pose proof (ss_fresh_disj lyF SF WF memF mdF L2 p n p m HARF EF' HL2) as Hd.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p m HARF ltac:(apply (Permutation_in _ (Permutation_sym EF)); apply in_or_app; right; exact HL2)) as (_ & _ & _ & _ & _ & _ & Hm0).
    pose proof (req_size_pos n ltac:(lia)). pose proof (req_size_pos m ltac:(lia)). unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
- intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn].
  + left. apply HO. rewrite lay_blocks_rest. apply in_or_app. left. exact Hpn.
  + destruct (in_dec recb_pair_dec pn (ablocks B ly S)) as [Hin | Hnin]; [|right; exact Hnin].
    apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [Hr | H2].
    * left. apply HO. rewrite lay_blocks_rest. apply in_or_app. right. exact Hr.
    * exfalso. exact (list_nodup_app_disj _ _ pn NDF Hpn H2).
- intros pn Hpn. apply (Permutation_in _ EF) in Hpn. apply in_app_or in Hpn as [Hq | H2].
  + right. apply in_or_app. right. exact Hq.
  + destruct (in_dec recb_pair_dec pn O) as [HinO | HnO].
    * right. apply in_or_app. left. apply HO in HinO. rewrite lay_blocks_rest in HinO. apply in_app_or in HinO as [Hr | Hr]; [exact Hr|].
      exfalso. exact (list_nodup_app_disj _ _ pn ND0' Hr H2).
    * left. split; [apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; right; exact H2 | exact HnO].
- intros pn Hin HnO. apply (Permutation_in _ HP) in Hin. apply in_app_or in Hin as [Hr | H2].
  + exfalso. apply HnO. apply HO. rewrite lay_blocks_rest. apply in_or_app. right. exact Hr.
  + apply (Permutation_in _ (Permutation_sym EF)). apply in_or_app. right. exact H2.
Qed.

Lemma ss_signed64 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z H. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap.
change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.

(* blez s0: bge x0, s0 *)
Lemma ss_bge_0 : forall size, - 2 ^ 31 <= size < 2 ^ 31 ->
branch_taken BC_GE (Z_to_bv 64 0) (Z_to_bv 64 size) = (size <=? 0).
Proof.
intros size Hs. cbn [branch_taken]. unfold bv_lts. rewrite !ss_signed64 by lia.
destruct (Z.ltb_spec 0 size), (Z.leb_spec size 0); cbn; first [reflexivity | lia].
Qed.

Theorem tsocket_send_holds : tsocket_send_spec B MT.
Proof.
unfold tsocket_send_spec.
intros ly S W regs mem md ch buf size x R O HPRE HROD H11 Hbuf H12 Hsz HREP Hnr Hpos Hneg Hev Hlive HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : SOCKET_SEND_STK = 16448) by (vm_compute; reflexivity).
assert (HXSv : XMALLOC_STK = 16400) by (vm_compute; reflexivity).
destruct HREP as (Q & HA & HO).
pose proof HA as (Hg8 & Hs8 & Hap & HC & HAns & HRep & HSC & HOWN).
pose proof HSC as (_ & _ & Vnr & _ & _ & _ & _ & Rnr & _).
destruct (areply_at_ptr _ _ _ _ _ HRep) as (Vrp & Hrpin & Hrpnone).
set (nrep := r_nreplies R) in *. set (rp := oaddr (l_reply Q)) in *.
assert (Rrp : 0 <= rp < 2 ^ 64).
{ subst rp. destruct (l_reply Q) as [[p n]|] eqn:Eq; cbn [oaddr fst]; [|lia].
  destruct (Hrpin (p, n) eq_refl) as [Hin _].
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hc & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as Hq. lia. }
pose proof (ajournal_init SEGS B SOCKET_SEND_STK (SS_FP O) ly S W regs mem md ch HPRE) as HJ.
pose proof (ss_entry_ok ly S W regs mem md ch nrep rp HPRE
(val_mem_view SEGS _ _ _ _ _ Vnr) ltac:(lia) (val_mem_view SEGS _ _ _ _ _ Vrp) Rrp
ltac:(intros o Ho; eapply ss_grec_writable; [exact HJ | unfold REC_SIZE; lia])) as HS.
unfold cfg_at. change (w64 (BASE + AF_socket_send)) with (Z_to_bv 64 (BASE + AF_socket_send)).
remember (Eimg (Ereg regs (ss_extra nrep rp))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ss_extra nrep rp)) E) by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. rewrite HE. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (E32 : ew E 32 = Z_to_bv 64 nrep) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 rp) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
clear HE.
assert (UGR : bv_unsigned (ew E SS_GR) = A_G_REC) by (rewrite (HEI SS_GR) by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia); exact ss_grec_val).
assert (UGR' : bv_unsigned (ew E 285) = A_G_REC) by exact UGR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
(* the run from the entry to the free call: through the UBSan trap branch at 0x8cde0, which the executor's step
   decides not taken (ss_step_8cde0 / ss_ubsan_8cde0) *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact UGR | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
clear HF HG. rename HFr into HFr1. rename ms into msA.
(* the call of the free wrapper at 0x8cdf4 *)
prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
lazymatch type of R2 with getr (ms_regs ?msx) _ = _ =>
assert (Esp1 : spZ (ms_regs msx) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; unfold SOCKET_SEND_STK, ASTACK in *; lia) end.
pmkst HS. rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (ss_free_any W _ _ SOCKET_SEND_STK (spZ regs) (SS_FP O) ly S W mem md [] ly S _ 0 (-48) _ [] (l_reply Q) (fun _ => AFREE_NULL4 fx) HJ).
  - intros [p n] Hq. destruct (Hrpin (p, n) Hq) as [Hin _]. split; [exact Hin|]. intros _ i Hi.
    assert (HpO : In (p, n) O) by (apply HO; unfold lay_blocks; rewrite Hq; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
    destruct (inFP_ablocks_fp O p n i HpO Hi) as (r & Hr & Hb). exists r. split; [right; exact Hr | exact Hb].
  - rewrite R10, E33. reflexivity.
  - exact Esp1.
  - reflexivity.
  - lia.
  - unfold SOCKET_SEND_STK. lia.
  - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold EV_SOCKET_SEND, EV_XMALLOC in Hev. lia.
  - apply (ss_chain_pre ly _ _ size Hsz); [intros _; lia | rewrite Esp1; unfold SOCKET_SEND_STK, ASTACK in *; lia | rewrite R8, (EE 12%nat 12%bv eq_refl); exact H12 |].
    unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - apply (mo_ok_le MT MTL S (mo_free MT) (XM_SOCKET_SEND MT size) HMOK). unfold XM_SOCKET_SEND, XM_XMALLOC, LIVE_XMALLOC.
    destruct (0 <? size) eqn:Hs; [pose proof (mo_malloc_nonneg MT MTL (Z.max size 1) ltac:(lia)); lia | lia]. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hperm2 & Hfr2 & HK2 & MLE2).
(* the free gives back the old reply's bytes, or nothing *)
assert (Hbb2 : blocks_bytes S2 <= blocks_bytes S).
{ rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), (bsum_perm _ _ Hperm2), bsum_app.
  destruct (l_reply Q) as [[p n]|] eqn:Eq; cbn [oblk].
  - destruct (Hrpin (p, n) eq_refl) as [Hin _]. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
    replace (bsum [(p, n)]) with n by (unfold bsum; cbn [fold_right snd]; lia). lia.
  - replace (bsum []) with 0 by reflexivity. lia. }
pose proof (ss_ablocks_nodup _ _ _ _ _ HAR) as ND0.
assert (KI : forall a, ss_keep Q buf size a ->
  0 <= a < alloc_ceiling /\ ~ (A_G_REC + OFF_NREPLIES <= a < A_G_REC + OFF_STATE) /\
  (Exists (in_zr a) recb_PG \/ exists b m, In (b, m) (ablocks B ly2 S2) /\ b <= a < b + req_size m /\ ~ in_img SEGS a)).
{ apply (ss_keep_info ly S W mem md R Q O buf size (ablocks B ly2 S2) HAR HA HO); [|exact Hperm2].
  intros Hs0. destruct (Hpos Hs0) as (_ & _ & _ & Hb & Ha). split; [exact Hb | exact Ha]. }
assert (K1 : forall a, ss_keep Q buf size a -> rdW W2 mem2 a = rdW W mem a).
{ intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl).
  rewrite (ss_free_keeps ly S W (ms_mem msA) _ W2 mem2 _ _ (l_reply Q) (ablocks B ly2 S2) a (proj1 HJ) ND0 Hperm2 HK2 Hcl).
  apply (ss_run_keeps E _ (w_H W) mem (ms_mem msA) a HFr1); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR', ?Usp in Hw;
    unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0; 1]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
  - eapply (region_kept_stack_aj SEGS B); [exact HK2 | exact HJ2 | exact Usp | | | | |]; unfold SOCKET_SEND_STK, ASTACK in *; lia.
  - apply ss_region_kept_grec; [exact UGR | |].
    + intros a Ha. apply (ss_kept_prog _ _ _ _ _ _ _ _ _ a HK2). apply recb_grec_in. unfold REC_SIZE. lia.
    + intros a Ha. eapply ss_grec_writable; [exact HJ2 | unfold REC_SIZE; lia]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS. clear R10 R2 R3 R4 R1 R8 Esp1.
remember (havoc E 34 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall n, (n < 34)%nat -> ew E2 n = ew E n) by (intros n Hn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE2 : env_agree 32 (Ereg regs (ss_extra nrep rp)) E2) by (rewrite HE2; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HE2.
assert (UGR2 : bv_unsigned (ew E2 SS_GR) = A_G_REC) by (rewrite (HEI2 SS_GR) by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia); exact ss_grec_val).
assert (UGR2' : bv_unsigned (ew E2 285) = A_G_REC) by exact UGR2.
assert (Usp2 : bv_unsigned (ew E2 2) = spZ regs) by (rewrite OLD2 by lia; exact Usp).
paj_run_shc RUNP RUNC HS HJ2.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack; [reflexivity | exact Usp2 | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact UGR2 | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
clear HF HG. rename HFr into HFr2. rename ms into msB.
(* the call of the memset entry at 0x8ce04: memset(&g_rec.reply, 0, 16) *)
prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12. prreg HS (2%bv : bv 5) R2.
prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
lazymatch type of R2 with getr (ms_regs ?msx) _ = _ =>
assert (Esp2 : spZ (ms_regs msx) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp2; apply unsigned_lit_small; unfold SOCKET_SEND_STK, ASTACK in *; lia) end.
pose proof (st_ok_region_nth E2 _ _ 1 _ HS eq_refl) as HRg2.
pose proof (field_of_region_any E2 _ SS_GR A_G_REC _ _ _ _ _ 920 4 (SOff 32 1) HRg2 UGR2 ltac:(cbn; tauto) ltac:(cbn; lia)) as V920.
assert (D920 : bv_unsigned (sv_denot E2 (SOff 32 1)) mod 2 ^ (8 * Z.of_N 4) = nrep + 1).
{ cbn [sv_denot]. rewrite OLD2 by lia. rewrite E32. rewrite (unsigned_lit_small nrep) by lia. rewrite unsigned_lit_small by lia.
  apply Z.mod_small. cbn. lia. }
rewrite D920 in V920. clear D920 HRg2.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG CS___asan_memset) (AMEMSET fx) W2 _ _ SOCKET_SEND_STK (spZ regs) (SS_FP O)
  ly S W mem md [] ly2 S2 _ _ (A_G_REC + OFF_REPLY) 0 16 (-48) (Z_to_bv 64 (BASE + 26840)) HJ2).
  - rewrite R10, UGR2'. reflexivity.
  - rewrite R11. reflexivity.
  - rewrite R12. reflexivity.
  - lia.
  - unfold A_G_REC, OFF_REPLY. lia.
  - unfold A_G_REC, OFF_REPLY. lia.
  - exact Esp2.
  - reflexivity.
  - lia.
  - unfold SOCKET_SEND_STK, ASTACK, ESTACK. lia.
  - rewrite R3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite R4, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact R1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [apply ss_grec_awr; [apply ss_inFP_grec|]; unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia|].
    unfold ESTACK, A_G_REC, OFF_REPLY, SOCKET_SEND_STK, ASTACK in *. lia.
  - intros a Ha _ _. eapply ss_grec_writable; [exact HJ2 | unfold A_G_REC, OFF_REPLY, REC_SIZE in *; lia].
  - apply amem_range_high; [lia | unfold A_G_REC, OFF_REPLY; lia | unfold A_G_REC, OFF_REPLY; lia].
  - exact (ss_rep_addressable _ _ _ _ _ (proj1 HJ2)).
  - intros _. exact (ss_rep_hull _ _ _ _ _ (proj1 HJ2)).
  - exact I. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hfr3 & Hpres3 & Hsame3).
assert (K2 : forall a, ss_keep Q buf size a -> rdW W2 mem3 a = rdW W mem a).
{ intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K1 a Hk).
  rewrite (Hfr3 a ltac:(lia) ltac:(unfold A_G_REC, OFF_REPLY, OFF_NREPLIES, OFF_STATE in *; lia) ltac:(unfold SOCKET_SEND_STK, ASTACK, ESTACK in *; lia)).
  apply (ss_run_keeps E2 _ (w_H W2) mem2 (ms_mem msB) a HFr2); [lia|].
  intros (r & Hr' & Hw). vm_compute in Hr'.
  repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR2', ?Usp2 in Hw;
    unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  eapply region_kept_aview; [exact Usp2 | | exact Hpres3].
  intros a Ha. apply Hfr3; unfold SOCKET_SEND_STK, ASTACK, ESTACK, A_G_REC, OFF_REPLY in *; lia. }
remember (havoc E2 50 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD3 : forall n, (n < 50)%nat -> ew E3 n = ew E2 n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (ss_extra nrep rp)) E3) by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE2]).
clear HE3.
assert (UGR3 : bv_unsigned (ew E3 SS_GR) = A_G_REC) by (rewrite (HEI3 SS_GR) by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia); exact ss_grec_val).
assert (UGR3' : bv_unsigned (ew E3 285) = A_G_REC) by exact UGR3.
assert (Usp3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact Usp2).
clear HS. pose proof (st_ok_pi_add_region E3 _ _ ss_grec1 HS3 eq_refl) as HS.
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ unfold region_ok, ss_grec1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst].
  rewrite UGR3. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|].
  split; [intros o Ho; eapply ss_grec_writable; [exact HJ3 | unfold REC_SIZE; lia]|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  - apply (chunk_ok_val SEGS E3 _ A_G_REC 920 4 _ (nrep + 1)); [| zside | zside |].
    + cbn [sv_denot]. rewrite OLD3, OLD2 by lia. rewrite E32, (unsigned_lit_small nrep) by lia. reflexivity.
    + apply (ss_val_mem_frame _ _ _ _ _ _ _ V920). intros k Hk. apply Hfr3; cbn in Hk; unfold SOCKET_SEND_STK, ASTACK, ESTACK, A_G_REC, OFF_REPLY in *; lia.
  - apply (chunk_ok_val SEGS E3 _ A_G_REC 928 8 _ 0); [reflexivity | zside | zside |].
    apply val_mem_zero8. intros i Hi. replace (A_G_REC + 928 + i) with (A_G_REC + OFF_REPLY + i) by (unfold OFF_REPLY; lia).
    rewrite Heff3 by lia. reflexivity.
  - apply (chunk_ok_val SEGS E3 _ A_G_REC 936 8 _ 0); [reflexivity | zside | zside |].
    apply val_mem_zero8. intros i Hi. replace (A_G_REC + 936 + i) with (A_G_REC + OFF_REPLY + (8 + i)) by (unfold OFF_REPLY; lia).
    rewrite Heff3 by lia. reflexivity. }
match type of HS with ?t -> _ => assert (HRK : t); [|specialize (HS HRK); clear HRK] end.
{ cbn [all_disjoint ss_mem]. split; [|exact I]. unfold extent_disjoint, ss_grec1, stack_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite UGR3, Usp3. unfold A_G_REC, SOCKET_SEND_STK, ASTACK in *. lia. }
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS end.
clear HS3 R10 R11 R12 R2 R3 R4 R1 Esp2.
rewrite <- restrict_mkst_fx in HS.
assert (E12 : sv_denot E3 (SOff 12 0) = Z_to_bv 64 size).
{ cbn [sv_denot]. rewrite OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl), H12, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned. }
psrr_branch_pi RUNP BR HS.
- (* size <= 0: the branch to 0x8ce28, then the return *)
  rewrite E12 in Hc. change (sv_denot E3 (SLit 0)) with (Z_to_bv 64 0) in Hc. rewrite ss_bge_0 in Hc by lia. apply Z.leb_le in Hc.
  paj_run_shc RUNP RUNC HS HJ3.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact UGR3 | |].
    { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
    eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr3. rename ms into msC.
  assert (K3 : forall a, ss_keep Q buf size a -> rdW W2 (ms_mem msC) a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K2 a Hk).
    apply (ss_run_keeps E3 _ (w_H W2) mem3 (ms_mem msC) a HFr3); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR3', ?Usp3 in Hw;
      unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
  eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (10%bv : bv 5) Rf10.
  pose proof (st_ok_pi_region_nth E3 _ _ 0 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region_any E3 _ SS_GR A_G_REC _ _ _ _ _ 920 4 (SOff 32 1) HRf UGR3 ltac:(cbn; tauto) ltac:(cbn; lia)) as F920.
  pose proof (field_of_region_any E3 _ SS_GR A_G_REC _ _ _ _ _ 928 8 (SLit 0) HRf UGR3 ltac:(cbn; tauto) ltac:(cbn; lia)) as F928.
  pose proof (field_of_region_any E3 _ SS_GR A_G_REC _ _ _ _ _ 936 8 (SLit 0) HRf UGR3 ltac:(cbn; tauto) ltac:(cbn; lia)) as F936.
  assert (D920 : bv_unsigned (sv_denot E3 (SOff 32 1)) mod 2 ^ (8 * Z.of_N 4) = nrep + 1).
  { cbn [sv_denot]. rewrite OLD3, OLD2 by lia. rewrite E32. rewrite (unsigned_lit_small nrep) by lia. rewrite unsigned_lit_small by lia.
    apply Z.mod_small. cbn. lia. }
  rewrite D920 in F920. change (bv_unsigned (sv_denot E3 (SLit 0)) mod 2 ^ (8 * Z.of_N 8)) with 0 in F928, F936.
  assert (Hra1' : getr (ms_regs msC) 1 = getr regs 1) by (rewrite Rf1, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  assert (Hrep' : areply_at (ablocks B ly2 S2) (rdW W2 (ms_mem msC)) A_G_REC (match x with [] => None | _ :: _ => Some x end) None).
  { rewrite (Hneg ltac:(lia)). change (areply_at (ablocks B ly2 S2) (rdW W2 (ms_mem msC)) A_G_REC None None).
    split; [exact (aval_mem_view SEGS _ _ _ _ _ F928) | exact (aval_mem_view SEGS _ _ _ _ _ F936)]. }
  assert (EF0 : Permutation (ablocks B ly2 S2) (oblk None ++ ablocks B ly2 S2)) by (cbn [oblk app]; apply Permutation_refl).
  destruct (ss_post_Q ly S W mem md R Q O buf size x (ablocks B ly2 S2) ly2 S2 W2 (ms_mem msC) _ None HAR (proj1 HJ3) HA HO Hnr
    Hperm2 EF0 K3 (aval_mem_view SEGS _ _ _ _ _ F920) Hrep') as (O' & HR' & HB1 & HB2 & HB3).
  unfold apost_base. eexists ly2, S2, (ms_regs msC), (ms_mem msC), _.
  split; [rewrite Hra1', Hra'; reflexivity|].
  split; [apply (ajournal_mono_k SEGS B) with (k := 0 + 1); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ3 | unfold EV_SOCKET_SEND, EV_XMALLOC; lia]|].
  split; [exact (aregs_preserved_of_st_ok SEGS (w_H W2) E3 _ msC regs (ss_extra nrep rp) HS HAE3 ltac:(vm_compute; reflexivity))|].
  exists O'. split; [rewrite Rf10, OLD3, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12|].
  split; [exact HR'|]. split; [exact HB1|]. split; [exact HB2|]. split; [exact HB3|].
  split; [unfold LIVE_SOCKET_SEND, LMAX in *; lia|].
  apply (mo_le_mono MT MTL S S2 (mo_free MT) (XM_SOCKET_SEND MT size) MLE2). unfold XM_SOCKET_SEND.
  replace (0 <? size) with false by (symmetry; apply Z.ltb_ge; lia). lia.
- (* size > 0 *)
  rewrite E12 in Hc. change (sv_denot E3 (SLit 0)) with (Z_to_bv 64 0) in Hc. rewrite ss_bge_0 in Hc by lia. apply Z.leb_gt in Hc.
  destruct (Hpos Hc) as (Hsz_l & Hlen & Hbytes & Hblk & Happ).
  pose proof Hblk as (pb & kb & Hpb & Hb1 & Hb2).
  assert (Hpb2 : In (pb, kb) (ablocks B ly2 S2)).
  { apply (Permutation_in _ Hperm2) in Hpb. apply in_app_or in Hpb as [Hr | H]; [|exact H]. exfalso.
    assert (HpO : In (pb, kb) O) by (apply HO; rewrite lay_blocks_rest; apply in_or_app; right; exact Hr).
    rewrite Forall_forall in Happ. pose proof (Happ (pb, kb) HpO) as Hd. unfold iv_apart in Hd. cbn [fst snd] in Hd. lia. }
  paj_run_shc RUNP RUNC HS HJ3.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact UGR3 | |].
    { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
    eapply awr_ok_cons_stack; [reflexivity | exact Usp3 | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr3. rename ms into msC.
  assert (K3 : forall a, ss_keep Q buf size a -> rdW W2 (ms_mem msC) a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K2 a Hk).
    apply (ss_run_keeps E3 _ (w_H W2) mem3 (ms_mem msC) a HFr3); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR3', ?Usp3 in Hw;
      unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
  (* the call of xmalloc at 0x8ce10, through its contract (xmalloc_c.v txmalloc_spec) and cl_callS *)
  prreg HS (10%bv : bv 5) R10. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  prreg HS (1%bv : bv 5) R1. prreg HS (8%bv : bv 5) R8.
  assert (Esp3 : spZ (ms_regs msC) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp3; apply unsigned_lit_small; unfold SOCKET_SEND_STK, ASTACK in *; lia).
  assert (Hnev3 : st_nev S2 + EV_XMALLOC <= EV_MAX).
  { pose proof HJ3 as (_ & _ & _ & _ & _ & _ & Hn3 & _). unfold EV_SOCKET_SEND, EV_XMALLOC in *. lia. }
  assert (LXs : LIVE_XMALLOC size = size) by (unfold LIVE_XMALLOC; lia).
  assert (HMOKx : mo_ok MT S2 (XM_XMALLOC MT size)).
  { apply (mo_ok_step MT MTL S S2 (mo_free MT) (XM_XMALLOC MT size)); [|exact MLE2].
    unfold XM_SOCKET_SEND in HMOK. replace (0 <? size) with true in HMOK by (symmetry; apply Z.ltb_lt; lia). exact HMOK. }
  pmkst HS. rewrite ss_sig_xmalloc.
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W2 (ms_regs msC) (ms_mem msC) _ SOCKET_SEND_STK (spZ regs) (SS_FP O) ly S W mem md [] ly2 S2 _ _
      XMALLOC_STK [] EV_XMALLOC (-48) (Z_to_bv 64 (BASE + 26852)) []
      (fun ly' S' W' regs' mem' md' => exists p : Z,
         getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
         Permutation (ablocks B ly' S') ((p, LIVE_XMALLOC size) :: ablocks B ly2 S2) /\
         Forall (fun qk => iv_apart p (LIVE_XMALLOC size) (fst qk) (snd qk)) (ablocks B ly2 S2) /\
         in_blockA (ablocks B ly' S') p (LIVE_XMALLOC size) /\
         blocks_bytes S' <= blocks_bytes S2 + LIVE_XMALLOC size /\
         mo_le MT S2 S' (XM_XMALLOC MT size)) HJ3 Esp3).
    - reflexivity.
    - lia.
    - unfold XMALLOC_STK, ASTACK. lia.
    - rewrite HSTKv, HXSv. lia.
    - rewrite R3, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite unsigned_lit_small by lia. lia.
    - apply (ss_achain ly2 _ _ _ size Hsz); [intros; lia|].
      rewrite R8, OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl). exact H12.
    - intros HPREx. eapply SRr_mono.
      + apply (TXMALLOC fx ly2 S2 W2 (ms_regs msC) (ms_mem msC) _ [] size HPREx).
        * rewrite R10, OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl). exact H12.
        * unfold MALLOC_MAX, LMAX in *. lia.
        * exact Hnev3.
        * rewrite LXs. unfold LIVE_SOCKET_SEND, LMAX in *. lia.
        * exact HMOKx.
      + cbv beta. unfold apost_base. intros W3' c3' _ (ly3 & S3 & regs3' & mem3' & md3' & -> & HJx & HPx & HKx).
        exists ly3, S3, regs3', mem3', md3'. split; [rewrite R1; reflexivity | split; [exact HJx | split; [exact HPx | exact HKx]]].
    - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJi & HP4 & (res & Ha04 & Hres & Hperm4 & Hap4 & Hblk4 & Hbb4 & MLE4)).
  rewrite LXs in Hperm4, Hap4, Hblk4, Hbb4.
  pose proof (proj1 HJ4) as HAR4.
  assert (Hres_in : In (res, size) (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym Hperm4)); left; reflexivity).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res size HAR4 Hres_in) as (_ & _ & Hrc & _).
  pose proof (req_size_pos size ltac:(lia)) as Hrq.
  assert (Hpb4 : In (pb, kb) (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hpb2).
  (* what xmalloc keeps: its journal has an empty footprint (xmalloc_c's apost_base XMALLOC_STK []) *)
  assert (K4 : forall a, ss_keep Q buf size a -> rdW W4 mem4 a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K3 a Hk).
    apply (ss_call_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi).
    destruct Hcl as [HPG | (b & m & Hbm & Hab & Hni)]; [left; exact HPG | right].
    exists b, m. split; [exact Hbm|]. split; [apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hbm | exact Hab]. }
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & FI1 & _).
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJ4pres & _).
  jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1]%nat HS4.
  match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
    - apply ss_region_kept_grec; [exact UGR3 | |].
      + intros a Ha. apply (ss_call_keeps _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi). left. apply recb_grec_in. unfold REC_SIZE. lia.
      + intros a Ha. eapply ss_grec_writable; [exact HJ4 | unfold REC_SIZE; lia].
    - eapply (ss_region_kept_hi2 SEGS E3 (w_H W2) (w_H W4) (ms_mem msC) mem4 2 (spZ regs)); [exact Usp3 | |].
      + intros a Ha. apply FI1; [lia | rewrite HXSv; lia | intros (r & Hr & _); destruct Hr].
      + intros a Ha. apply HJ4pres. lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS. clear R10 R2 R3 R4 R1 R8 Esp3.
  remember (havoc E3 66 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
  assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
  assert (OLD4 : forall n, (n < 66)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE4 : env_agree 32 (Ereg regs (ss_extra nrep rp)) E4) by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
  assert (E70 : ew E4 70 = Z_to_bv 64 res) by (rewrite HE4; cbn [havoc ew Nat.ltb Nat.leb Nat.sub nth map CLOB]; exact Ha04).
  clear HE4.
  assert (UGR4 : bv_unsigned (ew E4 SS_GR) = A_G_REC) by (rewrite (HEI4 SS_GR) by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia); exact ss_grec_val).
  assert (UGR4' : bv_unsigned (ew E4 285) = A_G_REC) by exact UGR4.
  assert (Usp4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact Usp3).
  (* xmalloc returns a block: no null check follows in B's code; `sd a0,928(s3)` and the memcpy call *)
  paj_run_shc RUNP RUNC HS HJ4.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact UGR4 | |].
    { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
    eapply awr_ok_cons_stack; [reflexivity | exact Usp4 | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr4. rename ms into msD.
  assert (K5 : forall a, ss_keep Q buf size a -> rdW W4 (ms_mem msD) a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K4 a Hk).
    apply (ss_run_keeps E4 _ (w_H W4) mem4 (ms_mem msD) a HFr4); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR4', ?Usp4 in Hw;
      unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
  (* the call of the memcpy entry at 0x8ce20: memcpy(reply, buf, size) *)
  prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11. prreg HS (12%bv : bv 5) R12. prreg HS (2%bv : bv 5) R2.
  prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4. prreg HS (1%bv : bv 5) R1.
  assert (Esp4 : spZ (ms_regs msD) = spZ regs + -48) by (unfold spZ at 1; rewrite R2, Usp4; apply unsigned_lit_small; unfold SOCKET_SEND_STK, ASTACK in *; lia).
  pmkst HS.
  pose proof (proj1 HJ4) as HAR4'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HAR4' Hpb4) as (_ & Hpb4096 & Hpbc & _ & Hpbpres & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ res size HAR4' Hres_in) as (_ & _ & _ & _ & Hrpres' & _).
  pose proof (ss_fresh_disj ly4 S4 W4 (ms_mem msD) _ (ablocks B ly2 S2) res size pb kb HAR4' Hperm4 Hpb2) as Hdisj.
  unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
  pose proof (req_size_pos kb ltac:(lia)) as Hkq.
  eapply SRr_bind.
  { eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W4 _ _ SOCKET_SEND_STK (spZ regs) (SS_FP O)
      ly S W mem md [] ly4 S4 _ _ res buf size (-48) (Z_to_bv 64 (BASE + 26868)) HJ4).
    - rewrite R10, E70. reflexivity.
    - rewrite R11, OLD4, OLD3, OLD2 by lia. rewrite (EE 11%nat 11%bv eq_refl). exact H11.
    - rewrite R12, OLD4, OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl). exact H12.
    - unfold LMAX in *. lia.
    - lia.
    - lia.
    - exact Esp4.
    - reflexivity.
    - lia.
    - unfold SOCKET_SEND_STK, ASTACK, ESTACK. lia.
    - rewrite R3, OLD4, OLD3, OLD2 by lia. rewrite (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, OLD4, OLD3, OLD2 by lia. rewrite (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - intros a Ha. split.
      + replace a with (res + (a - res)) by lia.
        eapply ss_awr_new_block; [exact HJ3 | exact HAR4' | exact Hperm4 | exact Hres_in | lia].
      + unfold SOCKET_SEND_STK, ASTACK, ESTACK in *. lia.
    - intros a Ha _ _. apply (apresent_writable SEGS). exact (proj1 (Hrpres' a ltac:(lia))).
    - exact (amem_range_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ res size res size HAR4' Hres_in ltac:(lia) ltac:(lia)).
    - exact (range_addressable_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ res size res size HAR4' Hres_in ltac:(lia) ltac:(lia)).
    - intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ res size res size HAR4' Hres_in ltac:(lia) ltac:(lia) ltac:(lia)).
    - hnf. split; [lia|]. split; [lia|]. split.
      { intros a Ha. split; [apply (aview_some_of_apresent SEGS); exact (proj1 (Hpbpres a ltac:(lia)))|].
        rewrite Esp4. unfold SOCKET_SEND_STK, ASTACK, ESTACK in *. lia. }
      split; [lia|].
      split; [exact (amem_range_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ pb kb buf size HAR4' Hpb4 ltac:(lia) ltac:(lia))|].
      split; [exact (range_addressable_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ pb kb buf size HAR4' Hpb4 ltac:(lia) ltac:(lia))|].
      intros _. exact (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 W4 (ms_mem msD) _ pb kb buf size HAR4' Hpb4 ltac:(lia) ltac:(lia) ltac:(lia)). }
  cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & Hsame5).
  assert (K6 : forall a, ss_keep Q buf size a -> rdW W4 mem5 a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K5 a Hk).
    apply Hfr5; [lia | | unfold SOCKET_SEND_STK, ASTACK, ESTACK in *; lia].
    exact (ss_not_new ly4 S4 W4 (ms_mem msD) _ (ablocks B ly2 S2) res size a HAR4' Hperm4 ltac:(lia) Hcl). }
  jafter_call_keep_pi HS 82%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0; 1]%nat HS5.
  match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | apply Forall_nil].
    - eapply region_kept_aview; [exact UGR4 | | exact Hpres5].
      intros a Ha. apply Hfr5; [unfold A_G_REC in *; lia | | unfold SOCKET_SEND_STK, ASTACK, ESTACK, A_G_REC in *; lia].
      exact (ss_not_new ly4 S4 W4 (ms_mem msD) _ (ablocks B ly2 S2) res size a HAR4' Hperm4 ltac:(lia)
        (or_introl (recb_grec_in a ltac:(unfold REC_SIZE in *; lia)))).
    - eapply region_kept_aview; [exact Usp4 | | exact Hpres5].
      intros a Ha. apply Hfr5; unfold SOCKET_SEND_STK, ASTACK, ESTACK in *; lia. }
  clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS. clear R10 R11 R12 R2 R3 R4 R1 Esp4.
  remember (havoc E4 82 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
  assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
  assert (OLD5 : forall n, (n < 82)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
  assert (HAE5 : env_agree 32 (Ereg regs (ss_extra nrep rp)) E5) by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
  clear HE5.
  assert (UGR5 : bv_unsigned (ew E5 SS_GR) = A_G_REC) by (rewrite (HEI5 SS_GR) by (unfold SS_GR, A_OBJ, A_TEXT, A_LIM; lia); exact ss_grec_val).
  assert (UGR5' : bv_unsigned (ew E5 285) = A_G_REC) by exact UGR5.
  assert (Usp5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact Usp4).
  paj_run_shc RUNP RUNC HS HJ5.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr lyx own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact UGR5 | |].
    { cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply ss_grec_awr; [apply ss_inFP_grec|]; unfold REC_SIZE; lia. }
    eapply awr_ok_cons_stack; [reflexivity | exact Usp5 | cbn; unfold SOCKET_SEND_STK, ASTACK; lia | cbn; lia | apply awr_ok_nil]. }
  clear HF HG. rename HFr into HFr5. rename ms into msE.
  assert (K7 : forall a, ss_keep Q buf size a -> rdW W4 (ms_mem msE) a = rdW W mem a).
  { intros a Hk. destruct (KI a Hk) as (Hr & Hng & Hcl). rewrite <- (K6 a Hk).
    apply (ss_run_keeps E5 _ (w_H W4) mem5 (ms_mem msE) a HFr5); [lia|].
    intros (r & Hr' & Hw). vm_compute in Hr'.
    repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR5', ?Usp5 in Hw;
      unfold A_G_REC, OFF_NREPLIES, OFF_STATE, SOCKET_SEND_STK, ASTACK in *; lia|]). destruct Hr'. }
  (* the bytes the memcpy wrote are there at the return *)
  assert (Hcopy : abytes_atR (rdW W4 (ms_mem msE)) res x).
  { intros i Hi.
    assert (Hni : ~ in_img SEGS (res + Z.of_nat i)) by (exact (ss_heap_noimg ly4 S4 W4 (ms_mem msD) _ res size (res + Z.of_nat i) HAR4' Hres_in ltac:(lia))).
    rewrite (ss_run_keeps E5 _ (w_H W4) mem5 (ms_mem msE) (res + Z.of_nat i) HFr5 ltac:(lia)).
    - rewrite (Heff5 (Z.of_nat i) ltac:(lia)). rewrite (K5 (buf + Z.of_nat i) ltac:(right; right; right; right; split; lia)).
      exact (Hbytes i Hi).
    - intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw; rewrite ?UGR5', ?Usp5 in Hw|]); [| | destruct Hr'].
      + apply Hni. apply cmd_prog_img. apply recb_grec_in. unfold REC_SIZE. lia.
      + unfold SOCKET_SEND_STK, ASTACK in *. lia. }
  eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  prreg HS (1%bv : bv 5) Rf1. prreg HS (10%bv : bv 5) Rf10.
  pose proof (st_ok_pi_region_nth E5 _ _ 0 _ HS eq_refl) as HRf. cbn [ms_mem restrict] in HRf.
  pose proof (field_of_region_any E5 _ SS_GR A_G_REC _ _ _ _ _ 920 4 (SOff 32 1) HRf UGR5 ltac:(cbn; tauto) ltac:(cbn; lia)) as F920.
  pose proof (field_of_region_any E5 _ SS_GR A_G_REC _ _ _ _ _ 928 8 (SOff 70 0) HRf UGR5 ltac:(cbn; tauto) ltac:(cbn; lia)) as F928.
  pose proof (field_of_region_any E5 _ SS_GR A_G_REC _ _ _ _ _ 936 8 (SOff 12 0) HRf UGR5 ltac:(cbn; tauto) ltac:(cbn; lia)) as F936.
  assert (D920 : bv_unsigned (sv_denot E5 (SOff 32 1)) mod 2 ^ (8 * Z.of_N 4) = nrep + 1).
  { cbn [sv_denot]. rewrite OLD5, OLD4, OLD3, OLD2 by lia. rewrite E32. rewrite (unsigned_lit_small nrep) by lia. rewrite unsigned_lit_small by lia.
    apply Z.mod_small. cbn. lia. }
  assert (D928 : bv_unsigned (sv_denot E5 (SOff 70 0)) mod 2 ^ (8 * Z.of_N 8) = res).
  { cbn [sv_denot]. rewrite OLD5 by lia. rewrite E70, Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia. apply Z.mod_small. cbn. lia. }
  assert (D936 : bv_unsigned (sv_denot E5 (SOff 12 0)) mod 2 ^ (8 * Z.of_N 8) = size).
  { cbn [sv_denot]. rewrite OLD5, OLD4, OLD3, OLD2 by lia. rewrite (EE 12%nat 12%bv eq_refl), H12, Z.add_0_r. unfold w64.
    rewrite Z_to_bv_bv_unsigned, unsigned_lit_small by lia. apply Z.mod_small. cbn. lia. }
  rewrite D920 in F920. rewrite D928 in F928. rewrite D936 in F936.
  assert (Hra1' : getr (ms_regs msE) 1 = getr regs 1) by (rewrite Rf1, OLD5, OLD4, OLD3, OLD2 by lia; exact (EE 1%nat 1%bv eq_refl)).
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  assert (Hrep' : areply_at (ablocks B ly4 S4) (rdW W4 (ms_mem msE)) A_G_REC (match x with [] => None | _ :: _ => Some x end) (Some (res, size))).
  { destruct x as [|b0 x']; [cbn [length] in Hlen; lia|].
    unfold areply_at. cbn [fst snd].
    split; [exact (aval_mem_view SEGS _ _ _ _ _ F928)|].
    split; [rewrite Hlen; exact (aval_mem_view SEGS _ _ _ _ _ F936)|].
    split; [lia|]. split; [discriminate|]. split; [exact Hres_in|]. split; [lia|]. split; [exact Hcopy|]. lia. }
  destruct (ss_post_Q ly S W mem md R Q O buf size x (ablocks B ly2 S2) ly4 S4 W4 (ms_mem msE) _ (Some (res, size)) HAR (proj1 HJ5) HA HO Hnr
    Hperm2 Hperm4 K7 (aval_mem_view SEGS _ _ _ _ _ F920) Hrep') as (O' & HR' & HB1 & HB2 & HB3).
  unfold apost_base. eexists ly4, S4, (ms_regs msE), (ms_mem msE), _.
  split; [rewrite Hra1', Hra'; reflexivity|].
  split; [apply (ajournal_mono_k SEGS B) with (k := 0 + 1 + EV_XMALLOC); [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ5 | unfold EV_SOCKET_SEND, EV_XMALLOC; lia]|].
  split; [exact (aregs_preserved_of_st_ok SEGS (w_H W4) E5 _ msE regs (ss_extra nrep rp) HS HAE5 ltac:(vm_compute; reflexivity))|].
  exists O'. split; [rewrite Rf10, OLD5, OLD4, OLD3, OLD2 by lia; rewrite (EE 12%nat 12%bv eq_refl); exact H12|].
  split; [exact HR'|]. split; [exact HB1|]. split; [exact HB2|]. split; [exact HB3|].
  split; [unfold LIVE_SOCKET_SEND in *; lia|].
  apply (mo_le_mono MT MTL S S4 (mo_free MT + XM_XMALLOC MT size) (XM_SOCKET_SEND MT size) (mo_le_trans MT MTL _ _ _ _ _ MLE2 MLE4)).
  unfold XM_SOCKET_SEND. replace (0 <? size) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End e.
End f.
End d.
