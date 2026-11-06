(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_drain of the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of
   fuzz_reply's LLVMFuzzerTestOneInput - the jump table's arm 2 (op_drain, fuzz_reply.c:596-609), from the arm's
   entry 0x8489c to the latch 0x84804.  THIS FILE IS THE INTERFACE the arm's two stage files and its closing file
   share: the addresses, the model notions, the register predicates, the state at the lock call (DLK), the bundle
   of what the other lanes owe (dr_env), and the pure lemmas over the model.  Proves no function (kind: segment
   walk): the callees are named contracts.

   Image: the pinned asan-ubsan objdump of fuzz_reply (fuzz_reply.objdump.txt (sha256 17f5c434bf57; internal record) beside the pinned ELF),
   sha256 17f5c434bf5755fb1ceaed0ac3e631e85a2eae980ed9983d0ee03955bf5307ac (the ELF beside it is the pin
   sha256 10ffb5f9202ae2bd..., lib/B/W_LLVMFuzzerTestOneInput_cut.v:18).

   ------------------------------------------------------------------ B's arm, read from B's own disassembly
   (0x8489c-0x84934; EVERY address, frame cell and shadow fact below is B's, not A's: B calls relay_source where
   A walks the inlined g_src scan, and B's arm has no join block of its own - all three paths jump straight to
   the latch 0x84804)
     0x8489c  beqz s5,850fc            TRAP NONNULL   s5 = the picked source g_s + 96 i  (runner, seat R1)
     0x848a0  andi a0,s5,7
     0x848a4  bnez a0,850fc            TRAP ALIGN8    same                                (runner, seat R1)
     0x848a8  sd t1,144(s1)            in.n left -> F+144   (t1 = c_n - k', lregs_D's reg 6)
     0x848ac  srli a1,s5,0x3 ; add a1,a1,s11 ; lb a1,0(a1)
     0x848b8  bnez a1,84dec            the ASan shadow check of s->fd: g_s lies in a zero-shadow range (HZS)
     0x848bc  lw a0,0(s5)              a0 = s->fd
     0x848c0  jal 85d28 <relay_source> CALL, contract RSRC (_cut.v:691)
     0x848c4  sd zero,192(s1)          at := 0  (F+192, the out-parameter of check_no_loss)
     0x848c8  beqz a0,84804            no entry with that fd -> the latch (a skip)
     0x848cc  mv s6,a0                 s6 = the entry g_src + 56 j
     0x848d0  andi a0,a0,7
     0x848d4  bnez a0,850fc            TRAP ALIGN8    8 | T + 56 j (RSRC's result, in the table's block)
     0x848d8  addi a0,s6,4 ; srli a1,a0,0x3 ; add a1,a1,s11 ; lb a1,0(a1)
     0x848e8  bnez a1,84e14            the shadow check of r->eof: inside the table's live 896-byte block
     0x848ec  lw a0,0(a0)              a0 = r->eof
     0x848f0  bnez a0,84804            end of file -> the latch (a skip)
     0x848f4  auipc a0,0x554 ; addi s7,a0,1868   s7 = &g_lock (0x5d9040)
     0x848fc  mv a0,s7 ; jal 98dbc <pthread_mutex_lock>        ra = 0x84904
     0x84904  mv a0,s6 ; jal 83278 <drain>                     ra = 0x8490c
     0x8490c  mv a0,s7 ; li s7,1 ; jal 992a8 <pthread_mutex_unlock>   ra = 0x84918
     0x84918  mv a0,s5 ; jal 85dd4 <check_no_loss_read>         ra = 0x84920
     0x84920  addi a1,s1,192 ; mv a0,s5 ; jal 85e3c <check_no_loss>   ra = 0x8492c
     0x8492c  ld a0,192(s1) ; jal 85a5c <check_shape_done>      ra = 0x84934
     0x84934  j 84804                  the latch
   The three trap branches are the cut header's ARM_drain rows (0x8489c NONNULL, 0x848a4 ALIGN8, 0x848d4 ALIGN8);
   each is decided by the runner from the seat's atom facts (lib/B/W_traps.v THE SEAT RECIPE R1/R2), so no
   trap_<shape> lemma is cited.  B keeps &g_lock in s7 (A keeps it in the frame cell F+40) and restores s7 = 1 at
   0x84910, so lregs_common's `getr regs 23 = w64 1` holds again at the latch; B keeps `t` in s9 and the cursor in
   s4, so B has no "reload s9 from F+104" tail (A's dr_jn_entry / dr_join_latch).

   ------------------------------------------------------------------ what this arm takes (all Section
   hypotheses, in dr_env below; the closing file declares them by name)
     RSRC            - the cut's own Section hypothesis (_cut.v:691), a Theorem Labs lane's agreed relay_source text;
     TL              - PALib B, the allocator instance (lib/B/W_kit.v);
     DRAIN           - the kit's dr_spec B MT MMAX fr_RG (BASE + AF_fr_drain) (lib/B/W_contract.v:1027);
     ALOCK / AUNLOCK - the kit's alock_realizes / aunlock_realizes at SIGMA WS_pthread_mutex_lock / _unlock
                       (lib/B/W_sites.v:90 / :105);
     CNLR            - the kit's cnlr_spec at BASE + AF_fr_check_no_loss_read (lib/B/W_contract.v:484);
     CSD             - the kit's csd_spec at BASE + AF_fr_check_shape_done (lib/B/W_contract.v:157);
     CNL             - the kit's cnl_spec, lib/B/W_contract.v:2054 (cnl_post :1967, CNL_STK :1966, Section w3n),
                       at the G the call site needs;
     the G-coverage facts, the instance facts, and the RINV / LS rule families, as on image A. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* local, so no file that Requires this one inherits it (the shared rule); each of the arm's files sets it *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the cut's own Local Notations, which do not leave its file (lib/B/W_LLVMFuzzerTestOneInput_cut.v:158-161) *)
Local Notation A_LLVMF := YCfn.A_LLVMF.
Local Notation RA_LLVMF := YCfn.RA_LLVMF.
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the arm's addresses (offsets from fr_B0) *)
Definition A_dr_arm : Z := AF_arm_drain.             (* 0x8489c the arm's entry *)
Definition A_dr_ret : Z := AF_arm_drain + 0x28.      (* 0x848c4 back from relay_source *)
Definition A_dr_r1 : Z := AF_arm_drain + 0x68.       (* 0x84904 back from pthread_mutex_lock *)
Definition A_dr_r2 : Z := AF_arm_drain + 0x70.       (* 0x8490c back from drain *)
Definition A_dr_r3 : Z := AF_arm_drain + 0x7c.       (* 0x84918 back from pthread_mutex_unlock *)
Definition A_dr_r4 : Z := AF_arm_drain + 0x84.       (* 0x84920 back from check_no_loss_read *)
Definition A_dr_r5 : Z := AF_arm_drain + 0x90.       (* 0x8492c back from check_no_loss *)
Definition A_dr_r6 : Z := AF_arm_drain + 0x98.       (* 0x84934 back from check_shape_done *)
(* the frame cells this arm uses: in.n left, `at` (check_no_loss's out-parameter) and the window that holds it *)
Definition DR_N : Z := 144.
Definition DR_AT : Z := 192.
Definition DR_XO : Z := 208.

(* ------------------------------------------------------------------ the model side (plain records only) *)
Definition dr_e0 : rentry := RE 0 0 0 [] 0 0 0 0 0 [] [] [] [].
Fixpoint set_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | O, _ :: l' => x :: l'
  | S n', y :: l' => y :: set_nth n' x l'
  | _, [] => []
  end.
Lemma set_nth_length : forall (A : Type) n (x : A) l, length (set_nth n x l) = length l.
Proof.
  intros A n x l. revert n. induction l as [|y l IH]; intros [|n]; cbn [set_nth length]; try reflexivity.
  rewrite IH. reflexivity.
Qed.
Lemma set_nth_same : forall (A : Type) n (x : A) l d, (n < length l)%nat -> nth n (set_nth n x l) d = x.
Proof.
  intros A n x l d. revert n. induction l as [|y l IH]; intros [|n] Hn; cbn [set_nth length nth] in *;
    try lia; [reflexivity | apply IH; lia].
Qed.
Lemma set_nth_other : forall (A : Type) n p (x : A) l d, n <> p -> nth p (set_nth n x l) d = nth p l d.
Proof.
  intros A n. induction n as [|n IH]; intros [|p] x l d Hnp; destruct l as [|y l];
    cbn [set_nth nth]; try reflexivity; try lia.
  apply IH. lia.
Qed.

Section dr_defs.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
(* ---- _cut's Section w, verbatim ---- *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable fr_live_post : astate -> astate -> Z -> Prop.
Variable fr_surv : alayout -> astate -> alayout -> astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
Variable MMAX : Z.                                   (* W7's request bound, dr_spec's parameter *)

(* ------------------------------------------------------------------ the arm's own model notions *)
(* the input cursor after the operation's two bytes (lregs_D's k'), and the byte pick() took *)
Definition dr_k' (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then lm_k m + 2 else lm_k m + 1.
Definition dr_kb (cx : lfcx) (m : lmod) : Z := if lm_k m + 1 <? c_n cx then in_byte cx (lm_k m + 1) else 0.
(* the operation this arm runs: op = 2 at the cursor, nothing read yet in it *)
Definition dr_at_op (cx : lfcx) (m : lmod) : Prop :=
  0 <= lm_k m < c_n cx /\ lm_O m = [] /\ in_byte cx (lm_k m) mod 10 = 2.
(* the source pick() returned: slot si, holding h *)
Definition dr_pick (cx : lfcx) (m : lmod) (si : nat) (h : hsrc) : Prop :=
  pick (lm_hs m) (dr_kb cx m) = Some si /\ (si < 4)%nat /\ nth si (lm_hs m) None = Some h.
(* no relay entry before index i has the source's fd *)
Definition dr_nomatch (m : lmod) (h : hsrc) (i : Z) : Prop :=
  forall q, 0 <= q < i -> re_fd (nth (Z.to_nat q) (lm_es m) dr_e0) <> hs_fd h.
(* the model after an operation that did nothing but consume its input bytes *)
Definition dr_skip (m : lmod) (k : Z) : lmod :=
  LM k (lm_hs m) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m) (lm_out m) (lm_gn m) (lm_nfd m).
(* the model after a drain of slot si / entry j *)
Definition dr_step (m : lmod) (k : Z) (si : nat) (h' : hsrc) (j : nat) (e' : rentry)
  (c' : ctl) (O' : list byte) (cap' out' : Z) : lmod :=
  LM k (set_nth si (Some h') (lm_hs m)) (lm_G m) (set_nth j e' (lm_es m)) c' O' (lm_mx m) cap' out'
     (lm_gn m) (lm_nfd m).

(* ------------------------------------------------------------------ the arm's register predicates (B's
   allocation, _cut.v difference (4): s2 = HI_G_SRC, s3 = FF + 32, s4 = the cursor, s5 = the picked source,
   s6 = the relay entry, s7 = 1 (and &g_lock between 0x848f8 and 0x84910), s8 = SB + FF / 8, s9 = t,
   s10 = HI_G_NOUT, s11 = SB) *)
(* the registers the six calls keep (every one callee-saved); s7 is NOT here: it holds &g_lock *)
Definition dr_regs_call (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 24 = w64 (SB + FF / 8) /\
  getr regs 26 = w64 HI_G_NOUT /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  getr regs 25 = w64 t /\ 0 <= t < OPS_MAX /\
  getr regs 20 = w64 (c_p cx + dr_k' cx m) /\
  getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat si) /\
  getr regs 22 = w64 (lm_G m + AENT * Z.of_nat j).

(* ---- the state at `jal pthread_mutex_lock` (0x84900): everything lcut says at the found entry with eof = 0,
   plus in.n at F+144, at = 0 at F+192, a0 = s7 = &g_lock and ra = 0x84904 ---- *)
Definition DLK (cx : lfcx) (t : Z) (m : lmod) (j si : nat) (h : hsrc) (fpos : Z) (ly3 : alayout) (S3 : astate)
  (k : Z) : world segs -> config -> Prop :=
  fun W c => exists regs mem md,
  c = mkCfg (mkst regs (Z_to_bv 64 (SIGMA WS_pthread_mutex_lock)) mem (seg_rom segs)) md /\
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k /\
  aframe_at cx (frame_addr ly3 1 fpos) W mem /\
  sv8 W mem (frame_addr ly3 1 fpos + 120) (flag_addr ly3 1 fpos) /\
  amodel_at B ly3 S3 W mem m /\ ainput_at B cx ly3 S3 W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  ablocks_sep B fr_FP cx m ly3 S3 /\ LS cx t m ly3 S3 /\ RINV cx t m /\
  dr_at_op cx m /\ dr_pick cx m si h /\ (j < length (lm_es m))%nat /\
  re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\ re_eof (nth j (lm_es m) dr_e0) = 0 /\
  sv8 W mem (lf_F cx + DR_N) (c_n cx - dr_k' cx m) /\ sv8 W mem (lf_F cx + DR_AT) 0 /\
  getr regs 1 = Z_to_bv 64 (BASE + A_dr_r1) /\ getr regs 10 = w64 (rg_lock fr_RG) /\
  getr regs 23 = w64 (rg_lock fr_RG) /\
  dr_regs_call cx t m j si (frame_addr ly3 1 fpos) regs.

(* ------------------------------------------------------------------ the functional half of one drained
   operation: W7's dr_post over the entry and the source, then k4's cnl_post over the drained source's two lists
   (image A's dr_step_ok, at B's contracts) *)
Definition dr_step_ok (cx : lfcx) (m : lmod) (si : nat) (h : hsrc) (j : nat)
  (e' : rentry) (h' : hsrc) (c' : ctl) (O' : list byte) (cap' out' : Z) (ev' : Z) (LB : list byte)
  (E' H' : hlist) : Prop :=
  let e := nth j (lm_es m) dr_e0 in
  let c := lm_c m in let mx := lm_mx m in let no := Z.of_nat (length (lm_O m)) in
  let cap := lm_cap m in let out := lm_out m in
  let fin := dr_fin c mx no cap e h in
  let live := dr_live c h in
  re_fd e' = re_fd e /\ re_eof e' = (if hs_closed h =? 1 then 1 else re_eof e) /\ 0 < re_cap e' /\
  re_cap e' = drain_b_c.ds_cap fin /\ bzs (re_U e') = drain_b_c.ds_u fin /\
  re_skip e' = (if drain_b_c.ds_skip fin then 1 else 0) /\
  drain_b_c.keys_texts (re_keys e') = drain_b_c.ds_H fin /\ drain_b_c.ent_ka e' = drain_b_c.ds_ka fin /\
  NoDup (drain_b_c.keys_texts (re_keys e')) /\
  same_set (drain_b_c.keys_texts (re_keys e')) (upds (drain_b_c.keys_texts (re_keys e)) (dr_lines h)) /\
  hs_fd h' = hs_fd h /\ hs_closed h' = hs_closed h /\ hs_eintr h' = 0 /\
  hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
  hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
  map snd (hl_recs (hs_expected h')) = map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) /\
  hs_held h' = hs_held h /\
  re_skip e' = hs_overlong h' /\ (re_skip e' = 0 -> bzs (re_U e') = bzs (hs_W h')) /\
  bzs LB = with_nul (dr_lines h) /\
  hl_cap (hs_expected h') = drain_b_c.ds_ecap fin /\
  c' = dr_ctl c h ev' /\ O' = (if live then lm_O m ++ LB else lm_O m) /\
  cap' = (if live then drain_b_c.ds_ocap fin else cap) /\
  hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h') /\ hl_cap E' = hl_cap (hs_expected h') /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h')) (texts (hs_expected h')).

(* ------------------------------------------------------------------ what the other lanes owe, as one bundle.
   Every field is the text its owner published; the closing file declares them as named Section hypotheses and
   builds this record from them. *)
Record dr_env : Prop := mk_dr_env {
  (* ---- the allocator instance and the callees ---- *)
  dre_TL : PALib (PI := PB_fr) B;
  dre_DRAIN : dr_spec (PI := PB_fr) B MT MMAX fr_RG (BASE + AF_fr_drain);
  dre_ALOCK : alock_realizes (PI := PB_fr) B (SIGMA WS_pthread_mutex_lock);
  dre_AUNLOCK : aunlock_realizes (PI := PB_fr) B (SIGMA WS_pthread_mutex_unlock);
  dre_CNLR : cnlr_spec (PI := PB_fr) B (BASE + AF_fr_check_no_loss_read);
  dre_CSD : csd_spec (PI := PB_fr) B (BASE + AF_fr_check_shape_done);
  (* the kit's check_no_loss (lib/B/W_contract.v:2054, Section w3n), at the G the call site takes: the slot's two
     list headers.  Its proof pb_check_no_loss takes gx_ok and (through its callees) rom_out at its own G. *)
  dre_CNL : forall G, gx_ok segs B G -> gx_rt (PI := PB_fr) B G -> rom_out segs B G ->
    cnl_spec (PI := PB_fr) B MT G MMAX (BASE + AF_fr_check_no_loss);
  (* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
  dre_HGs : forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a;
  dre_HG_DR : forall a, inG (G_DR B fr_RG) a -> inG G_fr a;
  dre_HGlock : forall a, rg_lock fr_RG <= a < rg_lock fr_RG + 12 -> inG G_fr a;
  (* the other cells of amodel_at are G_fr's too (so they are no allocator static: gx_ok) *)
  dre_HG_GK : forall a, inG [(rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
    (rg_send_max fr_RG, 8); (rg_client fr_RG, 4); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1);
    (rg_wake fr_RG, 8); (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] a -> inG G_fr a;
  (* errno's cell (0x5d994c on image B, lib/B/YF0m.v ts_errno) lies above every program global amodel_at names *)
  dre_HERR_HI : rg_out fr_RG + 8 <= as_errno B;
  (* _cut's errno_law / glob_wr_law at G_fr, verbatim *)
  dre_ERR : errno_law B;
  dre_GWR : glob_wr_law G_fr;
  (* W_journal.v's rom_out at G_fr *)
  dre_ROM_OUT : rom_out segs B G_fr;
  (* g_s lies in one of the instance's zero-shadow ranges (lib/B/W_LLVMFuzzerTestOneInput_G.v's measurement:
     Tfib_zero_shadow holds (0x5d8e60, 384)) *)
  dre_HZS : azs B (rg_s fr_RG) (4 * ASRC);
  (* the image objects this arm reads are apart from g_s; on image B the shadow GOT slot is A_OBJ 0 and
     __asan_shadow_memory_dynamic_address is A_OBJ 30 (lib/B/W_LLVMFuzzerTestOneInput_G.v c_HAP) *)
  dre_HAP : (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
            (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 30) \/ VAL (A_OBJ 30) + 8 <= rg_s fr_RG);
  (* ---- the arm's open model obligations (pure, over lmod and the plain records) ---- *)
  dre_RI_drain_skip : forall cx t m si h,
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (dr_nomatch m h (Z.of_nat (length (lm_es m))) \/
     (exists j, (j < length (lm_es m))%nat /\ re_fd (nth j (lm_es m) dr_e0) = hs_fd h /\
        re_eof (nth j (lm_es m) dr_e0) = 1)) ->
    RINV cx (t + 1) (dr_skip m (dr_k' cx m));
  dre_RI_drain_step : forall cx t m si h j e' h' c' O' cap' out' ev' LB E' H',
    RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    dr_step_ok cx m si h j e' h' c' O' cap' out' ev' LB E' H' ->
    RINV cx (t + 1) (dr_step m (dr_k' cx m) si (set_exp_held h' E' H') j e' c' O' cap' out');
  dre_RI_src : forall cx t m si h,
    RINV cx t m -> dr_pick cx m si h ->
    hl_recs (hs_expected h) = [] /\ NoDup (texts (hs_held h)) /\ 0 <= hs_fd h < 2 ^ 31;
  dre_RI_fds : forall cx t m i1 i2 h1 h2,
    RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
    nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2;
  dre_RI_pair : forall cx t m si h j,
    RINV cx t m -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    re_fd (nth j (lm_es m) dr_e0) = hs_fd h -> re_eof (nth j (lm_es m) dr_e0) = 0 ->
    re_skip (nth j (lm_es m) dr_e0) = hs_overlong h /\
    (re_skip (nth j (lm_es m) dr_e0) = 0 -> bzs (re_U (nth j (lm_es m) dr_e0)) = bzs (hs_W h)) /\
    length (re_pad1 (nth j (lm_es m) dr_e0)) = 4%nat /\ length (re_pad2 (nth j (lm_es m) dr_e0)) = 4%nat;
  dre_RI_gone : forall cx t m,
    RINV cx t m ->
    (lm_gn m = 0 -> ct_cl (lm_c m) = 3 /\ ct_br (lm_c m) = 0 /\ ct_dd (lm_c m) = 0) /\
    (lm_gn m = 1 -> ct_cl (lm_c m) = -1 \/ ct_br (lm_c m) = 1 \/ ct_dd (lm_c m) = 1);
  (* ---- the allocator-state facts the two calls take, read off LS ---- *)
  (* the peak form (a Theorem Labs lane's ROOM-ROUND row #19; dr_spec's byte premise is the drain trace's byte PEAK, C3), image A's
     text (W8's drain arm b5892edd1cb lib/A/W_LLVMFuzzerTestOneInput_drain.v): conjunct 5 is s5-r1d's
     fr_LS_drain_pre_c5p (lib/A/ReplyTrPeak.v:942 on image A), and the three premises after re_eof are the ones its
     rows take (fr_LS3_drain_pre_c4 lib/A/ReplyLS3Arms.v:790, fr_LS_drain_pre_c5p): dc_regs' Ht, aentry_ok's |re_U|
     bound and the drained blocks' sizes (dc_stB's HXP).  The sum form (tr_alloc) was FALSE at reachable states. *)
  dre_LS_drain_pre : forall cx t m ly S si h j,
    LS cx t m ly S -> RINV cx t m -> dr_at_op cx m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    0 <= t < OPS_MAX ->
    Z.of_nat (length (re_U (nth j (lm_es m) dr_e0))) <= APARTIAL ->
    (forall b, In b (aentry_blks (nth j (lm_es m) dr_e0) ++ asrc_blks h ++ aout_blks (lm_cap m) (lm_out m)) ->
       0 < snd b) ->
    Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    hl_cap (hs_expected h) < 2 ^ 26 /\
    re_nheld (nth j (lm_es m) dr_e0) + Z.of_nat (length (pending_stream h)) < 2 ^ 26 /\
    tr_max (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) < MMAX /\
    blocks_bytes S +
      tr_peak (dr_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h)
      <= LIVE_MAX /\
    mo_ok MT S (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h);
  dre_LS_cnl_pre : forall cx t m ly S (ly' : alayout) (S' : astate) si h j h'',
    LS cx t m ly S -> RINV cx t m -> dr_pick cx m si h ->
    (j < length (lm_es m))%nat -> re_fd (nth j (lm_es m) dr_e0) = hs_fd h ->
    re_eof (nth j (lm_es m) dr_e0) = 0 ->
    mo_le MT S S' (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
                     (nth j (lm_es m) dr_e0) h) ->
    hl_cap (hs_expected h'') = drain_b_c.ds_ecap
      (dr_fin (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    map snd (hl_recs (hs_expected h'')) =
      map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) (dr_lines h) ->
    hs_held h'' = hs_held h ->
    NoDup (texts (hs_held h'')) /\ hl_n (hs_expected h'') < 2 ^ 26 /\
    hl_n (hs_held h'') + Z.of_nat (count_begin (texts (hs_expected h''))) < 2 ^ 22 /\
    cnl_room MMAX (blocks_bytes S') (texts (hs_held h'')) (hl_cap (hs_held h''))
      (hl_recs (hs_expected h'')) /\
    mo_ok MT S' (cnl_cost MT (hs_expected h'') (hs_held h''));
  dre_LS_drain_skip : forall cx t m ly S,
    LS cx t m ly S -> LS cx (t + 1) (dr_skip m (dr_k' cx m)) ly S;
  dre_LS_drain_step : forall cx t m ly S (S1 : astate) (ly' : alayout) (S' : astate)
      si h j h'' e' c' O' cap' out' (E H : hlist),
    LS cx t m ly S -> dr_pick cx m si h -> (j < length (lm_es m))%nat ->
    mo_le MT S S1
      (dr_cost MT (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (nth j (lm_es m) dr_e0) h) ->
    mo_le MT S1 S' (cnl_cost MT E H) ->
    LS cx (t + 1) (dr_step m (dr_k' cx m) si h'' j e' c' O' cap' out') ly' S'
}.

(* ------------------------------------------------------------------ pure lemmas over the model *)
(* pick() returns an open slot *)
Lemma dr_pick_from : forall hs q kb i, pick_from hs q kb = Some i ->
  (q <= i < q + length hs)%nat /\ exists h, nth (i - q) hs None = Some h.
Proof.
  induction hs as [|o hs IH]; intros q kb i Hp; [discriminate Hp|].
  cbn [pick_from] in Hp. destruct o as [h|].
  - destruct (kb =? 0).
    + injection Hp as <-. cbn [length]. split; [lia|]. exists h. rewrite Nat.sub_diag. reflexivity.
    + destruct (IH (S q) (kb - 1) i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
      exists h'. replace (i - q)%nat with (S (i - S q)) by lia. exact Hh'.
  - destruct (IH (S q) kb i Hp) as [Hr [h' Hh']]. cbn [length]. split; [lia|].
    exists h'. replace (i - q)%nat with (S (i - S q)) by lia. exact Hh'.
Qed.
Lemma dr_pick_some : forall hs kb i, pick hs kb = Some i ->
  (i < length hs)%nat /\ exists h, nth i hs None = Some h.
Proof.
  intros hs kb i Hp. unfold pick in Hp. destruct (nopen hs =? 0); [discriminate Hp|].
  destruct (dr_pick_from hs 0 (kb mod nopen hs) i Hp) as [Hr [h Hh]].
  rewrite Nat.sub_0_r in Hh. split; [lia | exists h; exact Hh].
Qed.
(* no entry at all carries the fd, from `no entry of the list does` *)
Lemma dr_nomatch_all : forall m h,
  (forall e, In e (lm_es m) -> re_fd e <> hs_fd h) -> dr_nomatch m h (Z.of_nat (length (lm_es m))).
Proof.
  intros m h HF q Hq. apply HF. apply nth_In. lia.
Qed.
(* the cursor after the operation's bytes stays inside the input *)
Lemma dr_k'_rng : forall cx m, 0 <= lm_k m < c_n cx -> 0 <= dr_k' cx m <= c_n cx.
Proof. intros cx m Hk. unfold dr_k'. destruct (Z.ltb_spec (lm_k m + 1) (c_n cx)); lia. Qed.
(* the two models the arm can leave, at the latch's cursor *)
Lemma dr_skip_k : forall m k, lm_k (dr_skip m k) = k.
Proof. reflexivity. Qed.
Lemma dr_step_k : forall m k si h' j e' c' O' cap' out', lm_k (dr_step m k si h' j e' c' O' cap' out') = k.
Proof. reflexivity. Qed.
(* an entry holds re_nheld keys by definition (RelayRep.v re_nheld) *)
Lemma dr_keys_le : forall e, Z.of_nat (length (re_keys e)) <= re_nheld e.
Proof. intros e. unfold re_nheld. lia. Qed.
End dr_defs.
