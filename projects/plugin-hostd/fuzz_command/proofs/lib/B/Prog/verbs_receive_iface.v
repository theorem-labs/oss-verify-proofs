(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the interface of the walk of verbs_receive on the ASan+UBSan build of
   plugin-hostd/fuzz_command (statement: lib/B/Prog/verbs_receive_c.v, entry 0x8ce4c). The B twin of
   lib/A/Prog/verbs_receive_iface.v: the same 32 segments, the same boundary predicates and the same names, over B's
   own code (gen/dis/verbs_receive.s, 734 instructions against A's 677).

   What differs from A, and why each boundary below carries other numbers (B-PREP.md section 2, "A-to-B address map"):
   - the register allocation rotates (A s2/s5/s6 roles go to B s4/s2/s3), so every register list is B's;
   - B keeps tok in the frame slot s1+40 and reloads it before each dispatch arm, where A keeps it in s6; B's spill
     map is s1+0 = 0, +8 = shadow_addr F, +16 = F, +24 = F, +32 = shadow_addr F + 4, +40 = F + 32 (tok), +48 = c,
     +56 = q, +72 = F (A: +16 = F + 32, +24 = q, +40 = F, +48 = F, +56 = c);
   - the dispatch arms are re-ordered and B merges 3 of A's 9 sup_resp refusal tails (A 8 `li a0,-902` sites, B 6);
   - 34 UBSan trap checks are inserted, each branching to the `unimp` at 0x8d938; none is taken on a path this
     statement allows (verbs_receive_c.v:55-67), so no boundary mentions them.

   The shadow of the side-stack frame, the saved-register layout, the frame class (4) and the flag word at F + 1016
   are A's, word for word; vr_sh1 / vr_sh2 / vr_saved_regs are therefore unchanged.

   Program counters are the pinned image's (0x8ce4c .. 0x8d9c0); `vr_pc pc` is the listing's address of the
   instruction at pc. Register numbers: a0 10, a1 11, s0 8, s1 9, s2..s11 18..27. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
chain_words_c descriptors_add_c descriptors_get_c descriptors_panel_get_c is_instance_verb_c lv2_refusals_forget_c
number_c pin_set_words_c pins_clear_c reply_c sup_add_c sup_after_reply_c sup_broadcast_c sup_call_c
sup_chain_c sup_chain_clear_c sup_connect_c sup_host_setting_c sup_instance_info_c sup_instance_verb_c sup_lv2_worker_set_c
sup_pin_accept_c sup_policy_set_c sup_pool_config_c sup_quarantine_clear_c sup_remove_c sup_remove_all_c
sup_reply_code_c sup_reset_c sup_resp_c sup_worker_env_c sup_worker_list_c verb_is_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import verbs_receive_c.
(* the FP relation of statement pass 4 (frm0, fxrel and their lemmas) and the F call rules: a Theorem Labs lane's kit *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Module VRR := OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog.verbs_receive_route.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---------------------------------------------------------------------------------------------------------------
   The model's view of one message (lib/Spec/VerbsRun.v:59-64 run_receive, at the ASan wrappers' values). B runs the
   same C on the same message, so the model side is A's unchanged. *)
Definition vr_l (n : Z) (D : list byte) : Z := StrFun.strnlen_res n D.
Definition vr_ntok (D : list byte) : Z := Z.of_nat (length (Verbs.toks D)).
Definition vr_st (D : list byte) : Verbs.step := fst (Verbs.receive atoi_a D).
Definition vr_aft (D : list byte) : option (Z * list byte) := snd (Verbs.receive atoi_a D).
Definition vr_h (R : rstate) (D : list byte) : rstate * list byte * bool := VerbsRun.run_step reply_code_a R (vr_st D).
Definition vr_R1 (R : rstate) (D : list byte) : rstate := fst (fst (vr_h R D)).
Definition vr_x (R : rstate) (D : list byte) : list byte := snd (fst (vr_h R D)).
Definition vr_quit (R : rstate) (D : list byte) : bool := snd (vr_h R D).
Definition vr_R2 (R : rstate) (D : list byte) : rstate := fst (socket_send_m (vr_R1 R D) (vr_x R D ++ [Z_to_bv 8 0])).
Definition vr_R3 (R : rstate) (D : list byte) : rstate :=
match vr_aft D with Some (i, v) => sup_after_reply_m (vr_R2 R D) i (Some v) | None => vr_R2 R D end.
Definition vr_k1 (R : rstate) (D : list byte) : Z := 2 + ev_route R (Verbs.line D) (Verbs.toks D) (vr_st D).
Definition vr_k2 (R : rstate) (D : list byte) : Z := vr_k1 R D + EV_REPLY.
Definition vr_k3 (R : rstate) (D : list byte) : Z := vr_k2 R D + ev_after (vr_R2 R D) (vr_aft D).

Lemma vr_runA_eq : forall R D, vr_runA R D = (vr_R3 R D, vr_x R D, vr_quit R D).
Proof.
intros R D. unfold vr_runA, VerbsRun.run_receive, vr_R3, vr_R2, vr_R1, vr_x, vr_quit, vr_h, vr_st, vr_aft.
destruct (Verbs.receive atoi_a D) as [st af]. cbn [fst snd].
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q]. cbn [fst snd].
destruct af as [[i v]|]; reflexivity.
Qed.

Lemma ev_vr_eq : forall R D, ev_vr R D = vr_k3 R D + 2.
Proof.
intros R D. unfold ev_vr, vr_k3, vr_k2, vr_k1, vr_R2, vr_R1, vr_x, vr_h, vr_st, vr_aft.
destruct (Verbs.receive atoi_a D) as [st af]. cbn [fst snd].
destruct (VerbsRun.run_step reply_code_a R st) as [[R1 x] q]. cbn [fst snd]. lia.
Qed.

(* the malloc caps of the meter account at each phase: the two duplications, the handler (at most 25 more, one of
   them sup_resp's at a refusal stub), the reply (socket_send's copy), the call after the reply (its two copies);
   the statement's budget is VERBS_RECEIVE_MALLOCS = 32. B allocates where A does (B-PREP: the allocator calls per
   route are A's). *)
Definition VR_NM_PRE : Z := 2.
Definition VR_NM_PR : Z := 26.
Definition VR_NM_HD : Z := 27.
Definition VR_NM_AR : Z := 28.
Definition VR_NM_AF : Z := 30.

(* the shadow of the side-stack frame (128 bytes) after the prologue (f1 x4 at 0x8cf20-0x8cf2c, tok f8 x64 by
   __asan_set_shadow_f8 at 0x8cf3c, f2 x8 at 0x8cf48-0x8cf64, save f8 at 0x8cf6c, f3 x3 at 0x8cf70-0x8cf78, the
   unused slot tail 00), and once strndup has returned (tok opened at 0x8cfcc, save at 0x8cfd0) *)
Definition vr_sh1 : list Z := repeat 0xf1 4 ++ repeat 0xf8 64 ++ repeat 0xf2 8 ++ [0xf8] ++ repeat 0xf3 3 ++ repeat 0 48.
Definition vr_sh2 : list Z := repeat 0xf1 4 ++ repeat 0 64 ++ repeat 0xf2 8 ++ [0] ++ repeat 0xf3 3 ++ repeat 0 48.

(* the callee-saved registers the prologue stores at sp0-8 .. sp0-104: ra, s0, s1, s2, .., s11 (0x8ce54-0x8ce84) *)
Definition vr_saved_regs : list Z := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* the routes of the dispatch (lib/Prog/verbs_receive_route.v:7-9) and the B instruction each one starts at; the
   four routes behind the scan of g_instance_info_verbs all leave the dispatch at 0x8d7e0 *)
Definition vr_route_pc (r : VRR.vroute) : Z :=
match r with
| VRR.RAdd => 0x8d2e8 | VRR.RDget => 0x8d308 | VRR.RPget => 0x8d328 | VRR.RRemove => 0x8d41c
| VRR.RWlist => 0x8d3a0 | VRR.RIinfo => 0x8d3f8 | VRR.RReset => 0x8d4b8 | VRR.RQclear => 0x8d4e8
| VRR.RPolicy => 0x8d51c | VRR.RLv2 => 0x8d56c | VRR.RPool => 0x8d598 | VRR.REnv => 0x8d5d0
| VRR.RChain => 0x8d608 | VRR.RChclear => 0x8d61c | VRR.RPinset => 0x8d654 | VRR.RPinacc => 0x8d66c
| VRR.RPinclr => 0x8d7b4 | VRR.RQuit => 0x8d2a0
| VRR.RLedger _ | VRR.RInst | VRR.RConn | VRR.RBroad => 0x8d7e0
end.
Definition vr_is_tail (r : VRR.vroute) : bool :=
match r with VRR.RLedger _ | VRR.RInst | VRR.RConn | VRR.RBroad => true | _ => false end.

(* the shadow-checked image objects verbs_receive passes to the wrappers or reads under an inline check: the
   literals (with their terminators) and g_instance_info_verbs (10 rows of 16 bytes, 0xa5c40). Every address is A's
   + 0x40 (B-PREP section 2, the data rows: A .str 0x224c0 -> B 0x22500 .. A .str.38 0x22a00 -> B 0x22a40). *)
Definition vr_lits : list (Z * list byte) :=
[(0x22500, RO_lit_22500); (0x22520, RO_lit_22520); (0x22560, RO_lit_22560); (0x225a0, RO_lit_225a0);
 (0x225c0, RO_lit_225c0); (0x225e0, RO_lit_225e0); (0x22600, RO_lit_22600); (0x22620, RO_lit_22620);
 (0x22640, RO_lit_22640); (0x22660, RO_lit_22660); (0x226a0, RO_lit_226a0); (0x226c0, RO_lit_226c0);
 (0x22700, RO_lit_22700); (0x22720, RO_lit_22720); (0x22740, RO_lit_22740); (0x22760, RO_lit_22760);
 (0x22780, RO_lit_22780); (0x227a0, RO_lit_227a0); (0x227c0, RO_lit_227c0); (0x227e0, RO_lit_227e0);
 (0x22800, RO_lit_22800); (0x22820, RO_lit_22820); (0x22840, RO_lit_22840); (0x22860, RO_lit_22860);
 (0x228a0, RO_lit_228a0); (0x228c0, RO_lit_228c0); (0x228e0, RO_lit_228e0); (0x22920, RO_lit_22920);
 (0x22940, RO_lit_22940); (0x22960, RO_lit_22960); (0x22980, RO_lit_22980); (0x229a0, RO_lit_229a0);
 (0x229c0, RO_lit_229c0); (0x229e0, RO_lit_229e0); (0x22a00, RO_lit_22a00); (0x22a20, RO_lit_22a20);
 (0x22a40, RO_lit_22a40)].
Definition vr_shr : list (Z * Z) :=
map (fun al => (fst al, Z.of_nat (length (snd al)))) vr_lits ++ [(0xa5c40, 160)].

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the listing's address of the instruction at pc of the pinned image (B entry 0x8ce4c = BASE + AF_verbs_receive) *)
Definition vr_pc (pc : Z) : Z := BASE + (AF_verbs_receive + (pc - 0x8ce4c)).
Lemma vr_pc_entry : vr_pc 0x8ce4c = BASE + AF_verbs_receive.
Proof. unfold vr_pc. lia. Qed.

(* the entry state and the values tverbs_receive_spec quantifies *)
Record vrE : Type := mkVrE {
  e_ly : alayout; e_S : astate; e_W : world SEGS; e_regs : bvmap 5 word; e_mem : word -> option byte; e_md : Model;
  e_ch : list (Z * Z * Z); e_msg : Z; e_fd : Z; e_data : Z; e_n : Z; e_q0 : Z; e_ev : Z; e_D : list byte;
  e_R : rstate; e_O : list (Z * Z); e_rest : list (Z * Z) }.

Definition vr_sp0 (e : vrE) : Z := spZ (e_regs e).
(* s1 and sp after `andi sp,sp,-32` (0x8ce8c) *)
Definition vr_s1 (e : vrE) : Z := vr_sp0 e - 192 - (vr_sp0 e - 192) mod 32.
Definition vr_lb (e : vrE) (q : Z) : Z * Z := (q, vr_l (e_n e) (e_D e) + 1).
Definition vr_cb (e : vrE) (c : Z) : Z * Z := (c, Z.of_nat (length (Verbs.line (e_D e))) + 1).
Definition vr_qv (e : vrE) : Z := if vr_quit (e_R e) (e_D e) then 1 else e_q0 e.
Definition vr_rv (regs : bvmap 5 word) (l : list (Z * Z)) : Prop :=
Forall (fun rv => getr regs (Z_to_bv 5 (fst rv)) = w64 (snd rv)) l.

(* the spill slots (offsets from s1): after the prologue (0x8ceec); on the no-word path (0x8d070, 0x8d084); after
   the tokenizer (0x8d098-0x8d0c4). B's map, not A's: tok lives at s1+40 and the line at s1+56. *)
Definition vr_sl1 (F : Z) : list (Z * Z) := [(72, F)].
Definition vr_sl2 (F q c : Z) : list (Z * Z) := [(48, c); (56, q); (72, F)].
Definition vr_sl3 (F q c : Z) : list (Z * Z) :=
[(0, 0); (8, shadow_addr F); (16, F); (24, F); (32, shadow_addr F + 4); (40, F + 32); (48, c); (56, q); (72, F)].

(* the registers at each boundary, besides sp, gp, tp, s0, s1 (vr_base). B's allocation: s2 = line, s3 = the shadow
   base and later tok, s4 and s6 = the side-stack frame, s5 = 0 and later the word count, s8 = msg and later the
   sender, s9 = shadow_addr F and later the reply text, s10 = tok[0], s11 = shadow_addr F + 4. *)
Definition vr_rl1 (e : vrE) (F : Z) : list (Z * Z) :=
[(10, e_msg e + 8); (19, SHADOW_OFF); (20, F); (21, 0); (22, F); (24, e_msg e); (25, shadow_addr F);
 (27, shadow_addr F + 4)].
Definition vr_rl2 (e : vrE) (F q : Z) : list (Z * Z) :=
[(18, q); (19, SHADOW_OFF); (20, F); (21, 0); (22, F); (24, e_msg e); (25, shadow_addr F); (26, F + 608);
 (27, shadow_addr F + 4)].
(* 0x8cffc: a1 holds the end of the line, a0 its last byte; the trim loop runs from there *)
Definition vr_rl2t (e : vrE) (F q : Z) : list (Z * Z) := (11, q + vr_l (e_n e) (e_D e)) :: vr_rl2 e F q.
Definition vr_rl4e (e : vrE) (F q : Z) : list (Z * Z) :=
[(18, e_msg e / 8); (19, SHADOW_OFF); (20, F); (21, 0); (22, F); (24, e_msg e); (25, shadow_addr F);
 (26, F + 608); (27, shadow_addr F + 4)].
Definition vr_rl4t (e : vrE) : list (Z * Z) :=
[(18, e_msg e / 8); (19, SHADOW_OFF); (21, vr_ntok (e_D e)); (24, e_msg e); (25, vr_ntok (e_D e))].
(* at a route: B has reloaded s2 = q, s6 = F and s11 = shadow_addr F + 4 (0x8d120-0x8d128) before the first arm, so
   one list serves every route (A needed three groups).
   s8 is NOT named from here on. The dispatch loads the sender with `lw s8,0(s8)` (0x8d100), which SIGN-EXTENDS the
   four bytes, and the statement bounds neither fd nor the word at msg, so `getr regs 24 = w64 (e_fd e)` does not
   hold in general. Nothing downstream needs the value: reply passes a0 on unread (reply_c.v:72 "a0 (the
   destination) is passed on unread"), S31 overwrites s8 with tok[0] at 0x8d6b8, and the epilogue does not read it. *)
Definition vr_rl_rt (e : vrE) (F q v : Z) : list (Z * Z) :=
let nt := vr_ntok (e_D e) in
[(18, q); (19, SHADOW_OFF); (21, nt); (22, F); (23, nt - 1); (25, nt); (26, v); (27, shadow_addr F + 4)].
(* the refusal stubs: B's six `li a0,-902` / sup_resp tails. 0x8d88c is entered with the code already in a0 (from
   pin_set_words at 0x8d668, from pins_clear at 0x8d7d0/0x8d7dc, and from the two feeders 0x8d64c and 0x8d884). *)
Definition vr_rl_pr (e : vrE) (F q c pc code : Z) : list (Z * Z) :=
let nt := vr_ntok (e_D e) in
let base := [(18, q); (21, nt); (22, F); (27, shadow_addr F + 4)] in
if pc =? 0x8d88c then (10, code) :: (19, F + 32) :: base
else if (pc =? 0x8d4c4) || (pc =? 0x8d64c) then (19, F + 32) :: base
else base.
(* the handler's text tq at the joins J1 0x8d3b0, JB 0x8d4cc / 0x8d4d0 and JA 0x8d55c / 0x8d6a0 / 0x8d6a4 *)
Definition vr_rl_hd (e : vrE) (F q c pc tq : Z) : list (Z * Z) :=
let nt := vr_ntok (e_D e) in
let base := [(18, q); (22, F); (27, shadow_addr F + 4)] in
if pc =? 0x8d3b0 then (10, tq) :: base
else if pc =? 0x8d4cc then (10, tq) :: (19, F + 32) :: base
else if pc =? 0x8d4d0 then (25, tq) :: (19, F + 32) :: base
else if pc =? 0x8d55c then (10, tq) :: (19, F + 32) :: (21, nt) :: base
else if pc =? 0x8d6a0 then (26, tq) :: (20, F) :: (21, nt) :: (25, shadow_addr F) :: base
else (26, tq) :: (19, F + 32) :: (20, F) :: (21, nt) :: (25, shadow_addr F) :: base.
(* the number of words the code has tested on the way to a join: J1 is reached with one word only (RQuit and
   RWlist each test `ntok = 1`), the JB entries with at least two *)
Definition vr_hd_ntok (pc : Z) (nt : nat) : Prop :=
if pc =? 0x8d3b0 then nt = 1%nat
else if (pc =? 0x8d4cc) || (pc =? 0x8d4d0) then (2 <= nt)%nat
else (1 <= nt)%nat.
(* the refusal stubs 0x8d4c4 and 0x8d870 lead into JB (0x8d4cc / 0x8d4d0), which needs at least two words, so their
   producers carry at least two: 0x8d4c4's (S07, S11, S13) each refuse past a word-count test, and 0x8d870's only
   producer is RQuit's `bne s5,a0` at 0x8d2a4, taken exactly when the count is not 1 (and it is at least 1) *)
Definition vr_pr_ntok (pc : Z) (nt : nat) : Prop :=
if (pc =? 0x8d4c4) || (pc =? 0x8d870) then (2 <= nt)%nat else (1 <= nt)%nat.
Definition vr_rl_ar (F q c : Z) : list (Z * Z) :=
[(18, q); (19, F + 32); (20, F); (22, F); (25, shadow_addr F); (27, shadow_addr F + 4)].
Definition vr_rl_af (F q c : Z) : list (Z * Z) :=
[(18, q); (20, F); (22, F); (25, shadow_addr F); (27, shadow_addr F + 4)].

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the read-only range is the image's RELRO, fixed by the statement pass (CmdGlob.v CMD_RLO / CMD_RHI) *)
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* ---------------------------------------------------------------------------------------------------------------
   The facts of the allocator record and of the image that the walk takes as named premises (a Theorem Labs lane's RULING-STMT.md
   §1-2). On B each is an `exact` from lib/B/Prog/CmdRecBase / Cells / Ro / Img / ImgChk / Cover / Rest; the
   assembly (lib/B/Prog/verbs_receive.v) discharges them there, so no segment proves one locally. *)
Definition vr_rtrom : Prop :=
forall (W : world SEGS) mem, arodata_okP SEGS RLO RHI B (rdW W mem) -> rt_rom_view SEGS B W mem.
Lemma vr_rtrom_ok : vr_rtrom.
Proof.
intros W mem HR a Hrom Hown Herr. apply (HR a); [left; exact Hrom | exact Hown | exact Herr].
Qed.
Definition vr_shadow_ok : Prop :=
forall ly S (W : world SEGS) mem md a n, AR SEGS B ly S W mem md -> In (a, n) vr_shr ->
range_addressable (rdW W mem) SHADOW_OFF a n /\ shadow_hull_vis (rdW W mem) a n.
Definition vr_blktail : Prop :=
forall ly S (W : world SEGS) mem md p n x, AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= x < p + n -> atail_vis SEGS W mem x.
Definition vr_ro_of_aro : Prop :=
forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Definition vr_relro_img : Prop := forall a, RLO <= a < RHI -> in_img SEGS a.
Definition vr_pg_not_ro : Prop := forall a, inFP cmd_PG a -> ~ in_roP SEGS RLO RHI a.
Definition vr_ro_in_img : Prop := cmd_ro_in (in_roP SEGS RLO RHI).
(* cmd_rec_cells (RECC) at B's cells: the replace_str flag byte 0xae455 and the guard pair 0xa6bf8 / 0x604158 *)
Definition vr_rec_cells : Prop :=
forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
rdW W mem 0xae455 = Some 1 /\ aguard_ok SEGS W mem 0xa6bf8 0x604158 /\ exists ev, rd32 (rdW W mem) (as_errno B) ev.
Definition vr_prog_unowned : Prop :=
forall a, inFP cmd_PG a -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).

(* the premises of tverbs_receive_spec at the entry, and the record facts that hold there, in the statement's own
   order (lib/B/Prog/verbs_receive_c.v:280-322); the assembly derives the added conjuncts from them *)
Definition vr_ent (e : vrE) : Prop :=
let ly := e_ly e in let S := e_S e in let W := e_W e in let regs := e_regs e in let mem := e_mem e in
let md := e_md e in let ch := e_ch e in let msg := e_msg e in let fd := e_fd e in let data := e_data e in
let n := e_n e in let q0 := e_q0 e in let ev := e_ev e in let D := e_D e in let R := e_R e in let O := e_O e in
let rest := e_rest e in
afn_pre SEGS B VERBS_RECEIVE_STK ly S W regs mem md ch /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
getr regs 10 = w64 msg /\
afobj SEGS B ly S W mem msg 24 /\
aval_mem (rdW W mem) msg 4 fd /\
aval_mem (rdW W mem) (msg + 8) 8 data /\
aval_mem (rdW W mem) (msg + 16) 8 n /\
(0 <= n <= 8192) /\ Z.of_nat (length D) = n /\
In (data, Z.max n 1) (ablocks B ly S) /\ ~ In (data, Z.max n 1) O /\
abytes_atR (rdW W mem) data D /\
(0 <= e_msg e < 2 ^ 64) /\
rec_repA B ly S (rdW W mem) R O /\
r_calls R = [] /\ r_answer R = None /\ r_reply R = None /\ r_nreplies R = 0 /\
(r_refuse R <> 0 -> declared (r_code R) = true) /\
Permutation (ablocks B ly S) (O ++ rest) /\
aval_mem (rdW W mem) A_G_QUITTING 4 q0 /\
cmd_got_ok (rdW W mem) /\ cmd_ro_ok (rdW W mem) /\ cmd_ro_in (in_roP SEGS RLO RHI) /\ cmd_val_objs /\
rd32 (rdW W mem) (as_errno B) ev /\
rdW W mem 0xae455 = Some 1 /\
aguard_ok SEGS W mem 0xa6bf8 0x604158 /\
Z.of_nat (length (frames S)) <= 4 /\
st_nev S + ev_vr R D <= EV_MAX /\ blocks_bytes S + LIVE_VERBS_RECEIVE <= LIVE_MAX /\
mo_ok MT S (XM_VERBS_RECEIVE MT R D) /\
(* rounding mode 0 at the entry FP state (the last conjunct, so earlier positions stay) *)
frm0 fx.

(* the conclusion of tverbs_receive_spec, at the return (its post, verbatim) *)
Definition vr_final (e : vrE) : world SEGS -> config -> Prop :=
let ly := e_ly e in let S := e_S e in let W := e_W e in let regs := e_regs e in let mem := e_mem e in
let md := e_md e in let msg := e_msg e in let fd := e_fd e in let data := e_data e in
let n := e_n e in let q0 := e_q0 e in let D := e_D e in let R := e_R e in let O := e_O e in
let rest := e_rest e in
apost_baseF SEGS B VERBS_RECEIVE_STK (VERBS_RECEIVE_PG ++ ablocks_fp O) regs ly S W mem md (ev_vr R D)
(fun ly' S' W' regs' mem' md' =>
 let '(R', _, quit) := vr_runA R D in
 exists O' : list (Z * Z),
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 aval_mem (rdW W' mem') A_G_QUITTING 4 (if quit then 1 else q0) /\
 Permutation (ablocks B ly' S') (O' ++ rest) /\
 ~ In (data, Z.max n 1) O' /\ abytes_atR (rdW W' mem') data D /\
 aval_mem (rdW W' mem') msg 4 fd /\
 aval_mem (rdW W' mem') (msg + 8) 8 data /\
 aval_mem (rdW W' mem') (msg + 16) 8 n /\
 blocks_bytes S' <= blocks_bytes S + LIVE_VERBS_RECEIVE /\
 mo_le MT S S' (XM_VERBS_RECEIVE MT R D)).

(* ---------------------------------------------------------------------------------------------------------------
   The parts of a boundary state *)
Definition vr_fp (e : vrE) : list (Z * Z) := VERBS_RECEIVE_PG ++ ablocks_fp (e_O e).
Definition vr_base (e : vrE) : list (Z * Z) :=
[(2, vr_s1 e); (3, as_gp B); (4, as_tp B); (8, vr_sp0 e); (9, vr_s1 e)].
Definition vr_saved (e : vrE) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
forall j r, nth_error vr_saved_regs j = Some r ->
aval_mem (rdW Wc memc) (vr_sp0 e - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr (e_regs e) (Z_to_bv 5 r))).
Definition vr_spill (e : vrE) (Wc : world SEGS) (memc : word -> option byte) (l : list (Z * Z)) : Prop :=
Forall (fun ov => aval_mem (rdW Wc memc) (vr_s1 e + fst ov) 8 (snd ov)) l.
Definition vr_env (Wc : world SEGS) (memc : word -> option byte) : Prop :=
arodata_okP SEGS RLO RHI B (rdW Wc memc) /\ cmd_got_ok (rdW Wc memc) /\ cmd_ro_ok (rdW Wc memc) /\
aguard_ok SEGS Wc memc 0xa6bf8 0x604158 /\ rdW Wc memc 0xae455 = Some 1 /\
(exists ev', rd32 (rdW Wc memc) (as_errno B) ev').
Definition vr_meter (e : vrE) (Sc : astate) (k nm : Z) : Prop :=
exists nf, 0 <= nm <= k /\ 0 <= nf /\ nf <= k /\
mo_le MT (e_S e) Sc (nm * mo_malloc MT VERBS_RECEIVE_REQ + nf * mo_free MT).
Lemma vri_meter_step : forall e Sc S2 k nm (X a b ev : Z),
ameter_laws MT -> vr_meter e Sc k nm -> mo_le MT Sc S2 X ->
X <= a * mo_malloc MT VERBS_RECEIVE_REQ + b * mo_free MT -> 0 <= a <= ev -> 0 <= b <= ev ->
vr_meter e S2 (k + ev) (nm + a).
Proof.
intros e Sc S2 k nm X a b ev ML (nf & Hnm & Hnf & Hnfk & Hle) H2 HX Ha Hb.
exists (nf + b). split; [lia|]. split; [lia|]. split; [lia|].
apply (mo_le_mono MT ML _ _ (nm * mo_malloc MT VERBS_RECEIVE_REQ + nf * mo_free MT + X)).
- exact (mo_le_trans MT ML _ _ _ _ _ Hle H2).
- lia.
Qed.
Lemma vri_meter_ok : forall e Sc k nm (X a b ev : Z),
ameter_laws MT -> vr_ent e -> vr_meter e Sc k nm ->
X <= a * mo_malloc MT VERBS_RECEIVE_REQ + b * mo_free MT -> 0 <= a <= ev -> 0 <= b <= ev ->
k + ev <= ev_vr (e_R e) (e_D e) -> mo_ok MT Sc X.
Proof.
intros e Sc k nm X a b ev ML He (nf & Hnm & Hnf & Hnfk & Hle) HX Ha Hb Hk.
assert (Hmok : mo_ok MT (e_S e) (XM_VERBS_RECEIVE MT (e_R e) (e_D e))).
{ unfold vr_ent in He. cbv zeta in He.
  repeat lazymatch type of He with _ /\ (_ /\ _) => apply proj2 in He end. exact (proj1 He). }
pose proof (mo_malloc_nonneg MT ML VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hm0.
pose proof (mo_free_nonneg MT ML) as Hf0.
apply (mo_ok_le MT ML Sc X (X + 0)); [|lia].
apply (mo_ok_step MT ML (e_S e) Sc (nm * mo_malloc MT VERBS_RECEIVE_REQ + nf * mo_free MT) (X + 0)); [|exact Hle].
apply (mo_ok_le MT ML _ _ (XM_VERBS_RECEIVE MT (e_R e) (e_D e)) Hmok). unfold XM_VERBS_RECEIVE.
assert (E1 : (nm + a) * mo_malloc MT VERBS_RECEIVE_REQ <= ev_vr (e_R e) (e_D e) * mo_malloc MT VERBS_RECEIVE_REQ)
  by (apply Z.mul_le_mono_nonneg_r; lia).
assert (E2 : (nf + b) * mo_free MT <= ev_vr (e_R e) (e_D e) * mo_free MT) by (apply Z.mul_le_mono_nonneg_r; lia).
rewrite Z.mul_add_distr_l. lia.
Qed.
Lemma vri_meter_final : forall e S2 k nm,
ameter_laws MT -> vr_meter e S2 k nm -> k <= ev_vr (e_R e) (e_D e) ->
mo_le MT (e_S e) S2 (XM_VERBS_RECEIVE MT (e_R e) (e_D e)).
Proof.
intros e S2 k nm ML (nf & Hnm & Hnf & Hnfk & Hle) Hk.
pose proof (mo_malloc_nonneg MT ML VERBS_RECEIVE_REQ ltac:(unfold VERBS_RECEIVE_REQ; lia)) as Hm0.
pose proof (mo_free_nonneg MT ML) as Hf0.
apply (mo_le_mono MT ML _ _ _ _ Hle). unfold XM_VERBS_RECEIVE.
assert (E1 : nm * mo_malloc MT VERBS_RECEIVE_REQ <= ev_vr (e_R e) (e_D e) * mo_malloc MT VERBS_RECEIVE_REQ)
  by (apply Z.mul_le_mono_nonneg_r; lia).
assert (E2 : nf * mo_free MT <= ev_vr (e_R e) (e_D e) * mo_free MT) by (apply Z.mul_le_mono_nonneg_r; lia).
rewrite Z.mul_add_distr_l. lia.
Qed.
(* the side-stack frame (class 4, slot pos at F): the flag pointer at F+1016 and the 128 shadow bytes *)
Definition vr_frame (lyc : alayout) (Wc : world SEGS) (memc : word -> option byte) (pos F : Z) (sh : list Z) : Prop :=
F = frame_addr lyc 4 pos /\
rdword (rdW Wc memc) (F + 1016) = Some (flag_addr lyc 4 pos) /\
(forall i, (i < 128)%nat -> rdW Wc memc (shadow_addr F + Z.of_nat i) = Some (nth i sh 0)).
Definition vr_fresh (e : vrE) (b : Z * Z) : Prop := 4096 <= fst b /\ ~ In b (ablocks B (e_ly e) (e_S e)).

Definition vr_core (e : vrE) (pos F : Z) (tmps : list (Z * Z)) (sh : list Z) (sl rl : list (Z * Z))
  (Rc : rstate) (Oc : list (Z * Z)) (qv k kmax nm nmax : Z)
  (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
  : Prop :=
ajournal SEGS B VERBS_RECEIVE_STK (vr_sp0 e) (vr_fp e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e)
  [(4, pos)] lyc Sc Wc memc mdc k /\
k <= kmax /\ vr_meter e Sc k nm /\ nm <= nmax /\
vr_frame lyc Wc memc pos F sh /\
vr_rv regsc (vr_base e ++ rl) /\ vr_saved e Wc memc /\ vr_spill e Wc memc sl /\
vr_env Wc memc /\
rec_repA B lyc Sc (rdW Wc memc) Rc Oc /\ ~ In (e_data e, Z.max (e_n e) 1) Oc /\
Permutation (ablocks B lyc Sc) (Oc ++ tmps ++ e_rest e) /\
aval_mem (rdW Wc memc) A_G_QUITTING 4 qv.

(* the line block: strndup's copy (q, l+1), then the trimmed line in it *)
Definition vr_line0 (e : vrE) (q : Z) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
vr_fresh e (vr_lb e q) /\
abytes_atR (rdW Wc memc) q (firstn (Z.to_nat (vr_l (e_n e) (e_D e))) (e_D e) ++ [Z_to_bv 8 0]).
Definition vr_line (e : vrE) (q : Z) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
vr_fresh e (vr_lb e q) /\ astr_atR (rdW Wc memc) q (Verbs.line (e_D e)).
(* the copy block (c, |line|+1) and tok[] at F+32: the words of the line, cut in place (CmdRep's atoks_atA) *)
Definition vr_copy (e : vrE) (F c : Z) (tp : list Z) (Wc : world SEGS) (memc : word -> option byte) : Prop :=
vr_fresh e (vr_cb e c) /\
atoks_atA (rdW Wc memc) (F + 32) tp (Verbs.toks (e_D e)) c (Z.of_nat (length (Verbs.line (e_D e))) + 1).

(* ---------------------------------------------------------------------------------------------------------------
   The boundary states *)
(* S01 -> S02, 0x8cf9c: the frame is taken and its shadow written, msg and msg+8 checked *)
Definition vr_b1 (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8cf9c) regsc memc mdc /\
vr_core e pos F [] vr_sh1 (vr_sl1 F) (vr_rl1 e F) (e_R e) (e_O e) (e_q0 e) k 0 nm 0 lyc Sc Wc regsc memc mdc.
(* S02 -> S03, 0x8cffc: line = strndup(data, n) holds l > 0 bytes, tok and save opened, save = NULL; a1 = line + l *)
Definition vr_b2 (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8cffc) regsc memc mdc /\ 0 < vr_l (e_n e) (e_D e) /\
vr_core e pos F [vr_lb e q] vr_sh2 (vr_sl1 F) (vr_rl2t e F q) (e_R e) (e_O e) (e_q0 e)
  k 1 nm 1 lyc Sc Wc regsc memc mdc /\
vr_line0 e q Wc memc /\ rdword (rdW Wc memc) (F + 608) = Some 0.
(* S02/S03 -> S04, 0x8d070: the line is trimmed (the spill of q at s1+56 is S04's first instruction) *)
Definition vr_b3 (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d070) regsc memc mdc /\
vr_core e pos F [vr_lb e q] vr_sh2 (vr_sl1 F) (vr_rl2 e F q) (e_R e) (e_O e) (e_q0 e) k 1 nm 1 lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ rdword (rdW Wc memc) (F + 608) = Some 0.
(* S04 -> S05, 0x8d2bc: the copy is made and holds no word; s2 = msg >> 3 *)
Definition vr_b4e (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d2bc) regsc memc mdc /\ Verbs.toks (e_D e) = [] /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl2 F q c) (vr_rl4e e F q) (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_fresh e (vr_cb e c).
(* S04 -> S06, 0x8d0f4: the words are cut and stored in tok[] *)
Definition vr_b4t (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d0f4) regsc memc mdc /\ Verbs.toks (e_D e) <> [] /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl4t e) (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* S06 -> the route r, at vr_route_pc r: the dispatch has decided the route; s8 holds msg->sender_id, s10 tok[0] *)
Definition vr_rt (e : vrE) (r : VRR.vroute) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc (vr_route_pc r)) regsc memc mdc /\
VRR.route (Verbs.toks (e_D e)) = r /\ Verbs.toks (e_D e) <> [] /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_rt e F q (hd 0 tp)) (e_R e) (e_O e) (e_q0 e)
  k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
Definition vr_rt_tail (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists r, vr_is_tail r = true /\ vr_rt e r Wc cf.
(* S25 -> S26, 0x8d894: the scan matched row j of g_instance_info_verbs; s11 = the row, s3 = the shadow of its
   ledger word (B keeps the row in s11 and the shadow in s3, where A used s7 and s3) *)
Definition vr_led (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists j nmj led pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d894) regsc memc mdc /\
nth_error Verbs.Lit.instance_info_verbs j = Some (nmj, led) /\
VRR.route (Verbs.toks (e_D e)) = VRR.RLedger led /\ Verbs.toks (e_D e) <> [] /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(19, SHADOW_OFF + (0xa5c48 + 16 * Z.of_nat j) / 8); (21, vr_ntok (e_D e));
   (26, hd 0 tp); (27, 0xa5c40 + 16 * Z.of_nat j)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* S25 -> S27, 0x8d830: no row matched (route RInst, RConn or RBroad). s9 still holds ntok: the broadcast arm
   passes it to sup_host_setting with `mv a2,s9` at 0x8d958, and sup_host_setting_c.v:140 asks
   `getr regs 12 = w64 (length toks)`. Nothing on the path 0x8d7e0 -> 0x8d958 writes s9 (the scan writes s2, s3,
   s4, s6, s7, s11; is_instance_verb, verb_is and sup_broadcast keep it as a callee-saved register). *)
Definition vr_s27in (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d830) regsc memc mdc /\
(match Verbs.toks (e_D e) with
 | v :: args => Verbs.ledger_of v Verbs.Lit.instance_info_verbs = None /\ VRR.route (v :: args) = VRR.route_conn v args
 | [] => False end) /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* S27 -> S28, 0x8d8c4: not an instance verb with an argument (route RConn or RBroad); s9 = ntok, as at 0x8d830 *)
Definition vr_s28in (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d8c4) regsc memc mdc /\
(match Verbs.toks (e_D e) with
 | v :: args => VRR.route (v :: args) = VRR.route_cd v args
 | [] => False end) /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  [(21, vr_ntok (e_D e)); (25, vr_ntok (e_D e)); (26, hd 0 tp)]
  (e_R e) (e_O e) (e_q0 e) k 2 nm VR_NM_PRE lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* a refusal stub (0x8d4c4, 0x8d64c, 0x8d68c, 0x8d870, 0x8d884: code -902; 0x8d88c: the code already in a0, from
   pin_set_words, from pins_clear or from one of the two feeders): the handler's result is sup_resp(code) on Rx *)
Definition vr_pr (e : vrE) (pc : Z) : world SEGS -> config -> Prop := fun Wc cf =>
exists code Rx Ox pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
(pc <> 0x8d88c -> code = -902) /\ -2 ^ 31 <= code < 2 ^ 31 /\
vr_h (e_R e) (e_D e) = (Rx, resp code, false) /\ Verbs.toks (e_D e) <> [] /\
vr_pr_ntok pc (length (Verbs.toks (e_D e))) /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_pr e F q c pc code) Rx Ox (e_q0 e)
  k (vr_k1 (e_R e) (e_D e) - EV_SUP_RESP) nm VR_NM_PR lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* the handler is done (at a join): its text tq is a live block of its own *)
Definition vr_hd (e : vrE) (pc : Z) : world SEGS -> config -> Prop := fun Wc cf =>
exists tq O1 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc pc) regsc memc mdc /\
vr_hd_ntok pc (length (Verbs.toks (e_D e))) /\
4096 <= tq /\ astr_atR (rdW Wc memc) tq (vr_x (e_R e) (e_D e)) /\
vr_core e pos F [(tq, Z.of_nat (length (vr_x (e_R e) (e_D e))) + 1); vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c)
  (vr_rl_hd e F q c pc tq) (vr_R1 (e_R e) (e_D e)) O1 (vr_qv e)
  k (vr_k1 (e_R e) (e_D e)) nm VR_NM_HD lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* after the reply, 0x8d6b8 (S31): the text is freed *)
Definition vr_ar (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists O2 pos F q c tp lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d6b8) regsc memc mdc /\
(2 <= length (Verbs.toks (e_D e)))%nat /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 (vr_sl3 F q c) (vr_rl_ar F q c) (vr_R2 (e_R e) (e_D e)) O2 (vr_qv e)
  k (vr_k2 (e_R e) (e_D e)) nm VR_NM_AR lyc Sc Wc regsc memc mdc /\
vr_line e q Wc memc /\ vr_copy e F c tp Wc memc.
(* after the call after the reply, 0x8d71c (S32): the copy and the line are still to be freed; B reads the copy
   back from the spill slot s1+48, so vr_af keeps that slot (A kept it in s3) *)
Definition vr_af (e : vrE) : world SEGS -> config -> Prop := fun Wc cf =>
exists O3 pos F q c lyc Sc regsc memc mdc k nm,
cf = cfg_at SEGS (vr_pc 0x8d71c) regsc memc mdc /\
vr_core e pos F [vr_lb e q; vr_cb e c] vr_sh2 [(48, c)] (vr_rl_af F q c) (vr_R3 (e_R e) (e_D e)) O3 (vr_qv e)
  k (vr_k3 (e_R e) (e_D e)) nm VR_NM_AF lyc Sc Wc regsc memc mdc /\
vr_fresh e (vr_lb e q) /\ vr_fresh e (vr_cb e c).

(* ---------------------------------------------------------------------------------------------------------------
   The segment statements. A segment runs from its entry state at the current FP state (the section's fx; the
   assembly instantiates each segment lemma at the FP state the walk has reached). A segment that calls no
   printf-reaching callee ends at the same FP state (vr_seg); one that does ends at some FP state related to it by
   fxrel (PaFx.v; vr_segF, below the section break). *)
Definition vr_seg (P Q : vrE -> world SEGS -> config -> Prop) : Prop :=
forall e W cf, vr_ent e -> P e W cf -> SRr SEGS W cf (Q e).
Definition vr_or (P Q : vrE -> world SEGS -> config -> Prop) : vrE -> world SEGS -> config -> Prop :=
fun e W cf => P e W cf \/ Q e W cf.
Definition vr_atr (r : VRR.vroute) : vrE -> world SEGS -> config -> Prop := fun e => vr_rt e r.
Definition vr_atpr (pc : Z) : vrE -> world SEGS -> config -> Prop := fun e => vr_pr e pc.
Definition vr_athd (pc : Z) : vrE -> world SEGS -> config -> Prop := fun e => vr_hd e pc.

(* S01 PRO 0x8ce4c-0x8cf98 *)
Definition vr_s01_stmt : Prop :=
forall e, vr_ent e ->
SRr SEGS (e_W e) (cfg_at SEGS (BASE + AF_verbs_receive) (e_regs e) (e_mem e) (e_md e)) (vr_b1 e).
(* S02 DUP 0x8cf9c-0x8cff8 *)
Definition vr_s02_stmt : Prop := vr_seg vr_b1 (vr_or vr_b2 vr_b3).
(* S03 TRIM 0x8cffc-0x8d06c *)
Definition vr_s03_stmt : Prop := vr_seg vr_b2 vr_b3.
(* S04 TOK 0x8d070-0x8d0f0 *)
Definition vr_s04_stmt : Prop := vr_seg vr_b3 (vr_or vr_b4e vr_b4t).
(* S06 DISP 0x8d0f4-0x8d2a4 and the two inline-check tails 0x8d974-0x8d984 (verb_is is frameless and reaches no
   printf wrapper) *)
Definition vr_s06_stmt : Prop := vr_seg vr_b4t (fun e => vr_rt e (VRR.route (Verbs.toks (e_D e)))).
(* S25 SCAN 0x8d7e0-0x8d82c *)
Definition vr_s25_stmt : Prop := vr_seg vr_rt_tail (vr_or vr_led vr_s27in).
(* S30 JOIN: reply(fd, text) at J1 0x8d3b0, JB 0x8d4cc / 0x8d4d0 and JA 0x8d55c / 0x8d6a0 / 0x8d6a4 (reply's post
   is apost_base). J1 answers a one-word message, so the model's `after` is None and it runs to the epilogue; the
   JA entries test `ntok = 1` at 0x8d6b4 themselves. *)
Definition vr_s30_stmt : Prop :=
vr_seg (vr_athd 0x8d3b0) vr_af /\
vr_seg (vr_athd 0x8d4cc) vr_ar /\ vr_seg (vr_athd 0x8d4d0) vr_ar /\
vr_seg (vr_athd 0x8d55c) (vr_or vr_ar vr_af) /\ vr_seg (vr_athd 0x8d6a0) (vr_or vr_ar vr_af) /\
vr_seg (vr_athd 0x8d6a4) (vr_or vr_ar vr_af).
(* S32 FIN 0x8d71c-0x8d7b0 *)
Definition vr_s32_stmt : Prop := vr_seg vr_af vr_final.

End e.
End f.
End d.

(* ---------------------------------------------------------------------------------------------------------------
   The segments that call a printf-reaching callee (its post is apost_baseF): they end at some FP state fq with
   fxrel fx fq, and their exit predicate is the boundary predicate at fq. *)
Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
(* a boundary predicate at every FP state *)
Definition vrF : Type := YK11.FPState -> vrE -> world SEGS -> config -> Prop.
Definition vr_segF (P : vrE -> world SEGS -> config -> Prop) (Q : vrF) : Prop :=
forall e W cf, vr_ent B MT e -> P e W cf ->
SRr SEGS W cf (fun W' cf' => exists fq : YK11.FPState, fxrel fx fq /\ Q fq e W' cf').
Definition vrF_or (P Q : vrF) : vrF := fun fq => vr_or (P fq) (Q fq).
Definition vrF_pr (pc : Z) : vrF := fun fq => vr_atpr (fx := fq) B MT pc.
Definition vrF_hd (pc : Z) : vrF := fun fq => vr_athd (fx := fq) B MT pc.
Definition vrF_ar : vrF := fun fq => vr_ar (fx := fq) B MT.
Definition vrF_af : vrF := fun fq => vr_af (fx := fq) B MT.
Definition vrF_s28in : vrF := fun fq => vr_s28in (fx := fq) B MT.
(* a segment that ends at its own FP state also ends at a related one *)
Lemma vr_segF_same : forall (P : vrE -> world SEGS -> config -> Prop) (Q : vrF),
(forall e W cf, vr_ent B MT e -> P e W cf -> SRr SEGS W cf (Q fx e)) -> vr_segF P Q.
Proof.
intros P Q H e W cf He HP. eapply SRr_mono; [exact (H e W cf He HP)|].
intros W' cf' _ HQ. exists fx. split; [apply fxrel_refl | exact HQ].
Qed.

(* S05 EMPTY 0x8d2bc-0x8d2e4 (sup_resp(-902), then reply, then the epilogue) *)
Definition vr_s05_stmt : Prop := vr_segF (vr_b4e B MT) vrF_af.
(* S07..S24: the routes of the dispatch. B merges A's refusal tails, so an arm that refuses leaves at 0x8d68c
   (the shared `li a0,-902` before sup_resp) unless it has already reloaded tok, when it leaves at 0x8d4c4. *)
Definition vr_s07_stmt : Prop :=
vr_segF (vr_atr B MT VRR.RAdd) (vrF_or (vrF_pr 0x8d68c) (vrF_or (vrF_pr 0x8d4c4) (vrF_hd 0x8d4d0))).
Definition vr_s08_stmt : Prop := vr_segF (vr_atr B MT VRR.RDget) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s09_stmt : Prop := vr_segF (vr_atr B MT VRR.RPget) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s10_stmt : Prop := vr_segF (vr_atr B MT VRR.RRemove) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s11_stmt : Prop := vr_segF (vr_atr B MT VRR.RWlist) (vrF_or (vrF_pr 0x8d4c4) (vrF_hd 0x8d3b0)).
Definition vr_s12_stmt : Prop := vr_segF (vr_atr B MT VRR.RIinfo) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s13_stmt : Prop := vr_segF (vr_atr B MT VRR.RReset) (vrF_or (vrF_pr 0x8d4c4) (vrF_hd 0x8d55c)).
Definition vr_s14_stmt : Prop := vr_segF (vr_atr B MT VRR.RQclear) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s15_stmt : Prop := vr_segF (vr_atr B MT VRR.RPolicy) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s16_stmt : Prop := vr_segF (vr_atr B MT VRR.RLv2) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s17_stmt : Prop := vr_segF (vr_atr B MT VRR.RPool) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s18_stmt : Prop := vr_segF (vr_atr B MT VRR.REnv) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s19_stmt : Prop := vr_segF (vr_atr B MT VRR.RChain) (vrF_hd 0x8d55c).
Definition vr_s20_stmt : Prop := vr_segF (vr_atr B MT VRR.RChclear) (vrF_or (vrF_pr 0x8d64c) (vrF_hd 0x8d55c)).
Definition vr_s21_stmt : Prop := vr_segF (vr_atr B MT VRR.RPinset) (vrF_pr 0x8d88c).
Definition vr_s22_stmt : Prop := vr_segF (vr_atr B MT VRR.RPinacc) (vrF_or (vrF_pr 0x8d68c) (vrF_hd 0x8d4cc)).
Definition vr_s23_stmt : Prop := vr_segF (vr_atr B MT VRR.RPinclr) (vrF_or (vrF_pr 0x8d884) (vrF_pr 0x8d88c)).
Definition vr_s24_stmt : Prop := vr_segF (vr_atr B MT VRR.RQuit) (vrF_or (vrF_pr 0x8d870) (vrF_hd 0x8d3b0)).
(* S26 LEDGER 0x8d894-0x8d8c0 *)
Definition vr_s26_stmt : Prop := vr_segF (vr_led B MT) (vrF_hd 0x8d6a0).
(* S27 INST 0x8d830-0x8d86c *)
Definition vr_s27_stmt : Prop := vr_segF (vr_s27in B MT) (vrF_or (vrF_hd 0x8d4cc) vrF_s28in).
(* S28 CONNBROAD 0x8d8c4-0x8d934 and 0x8d93c-0x8d970 *)
Definition vr_s28_stmt : Prop := vr_segF (vr_s28in B MT) (vrF_or (vrF_hd 0x8d4cc) (vrF_hd 0x8d6a4)).
(* S29 REJ: the six refusal stubs. 0x8d64c and 0x8d884 only set the code (and 0x8d884 reloads tok) and fall into
   the shared sup_resp at 0x8d88c, so they are plain segments. *)
Definition vr_s29_stmt : Prop :=
vr_segF (vr_atpr B MT 0x8d4c4) (vrF_hd 0x8d4cc) /\
vr_segF (vr_atpr B MT 0x8d68c) (vrF_hd 0x8d6a4) /\
vr_segF (vr_atpr B MT 0x8d870) (vrF_hd 0x8d4d0) /\
vr_segF (vr_atpr B MT 0x8d88c) (vrF_hd 0x8d55c) /\
vr_seg B MT (vr_atpr B MT 0x8d64c) (vr_atpr B MT 0x8d88c) /\
vr_seg B MT (vr_atpr B MT 0x8d884) (vr_atpr B MT 0x8d88c).
(* S31 AFTER 0x8d6b8-0x8d718 *)
Definition vr_s31_stmt : Prop := vr_segF (vr_ar B MT) vrF_af.

End e2.
End f2.
End d2.
