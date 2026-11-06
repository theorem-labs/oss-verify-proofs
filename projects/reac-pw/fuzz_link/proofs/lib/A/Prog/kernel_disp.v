(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module names changed; 327 of its 364 lines of code are new or changed and 1268 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readDefs.v, with its module names changed; 1004 of its 1049 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/copy_attr.v, with its module names changed; 373 of its 423 lines of code are new or changed and 999 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/kernel_setup.v, with its numbers changed; 1383 of its 1444 lines of code are new or changed and 362 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's DISPATCH phase, kin_loop (+0x63c) -> the eight kind entries / kin_qmsg (+0x1e9c) (link-a/plan/kernel-plan.md
   (internal record, sha256 440bf3b40ab7) section 4; link-a/plan/kernel-lanes.md (internal record, sha256 18c8d69749d5)).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3)):
     +0x63c  ld a0, 0xc8(s1); lw a0, 0(a0)        w2.full (slot KS_W2F = &w2.full)
     +0x644  beqz a0 -> +0x64c, else j +0x1e9c    the reply buffer is full: the message loop is over (kin_qmsg)
     +0x64c  lbu a0, 0(s8); beqz a0               the check of the cursor's n word (s8 = shadow(a0 + 8))
     +0x658  ld s3, 0xb0(s1); ld a2, 0(s3)        s3 := a0 + 8, a2 := n
     +0x660  sd a4, 0xa0(s1)                      the slot KS_K := k
     +0x664  beqz a2 -> +0x6e0 `mv a6, zero` -> +0x6e4: the empty cursor's kind is 0 (kin_kind at kd = 0)
     +0x668  lbu a0, 0(s8); beqz a0               the check again, for the store of n - 1
     +0x674  addi a3, a2, -1; sd a3, 8(s2)        the cursor's n
     +0x67c  ld a0, 0xc0(s1); lbu a0, 0(a0); beqz a0   the check of the cursor's p word (slot KS_CSH)
     +0x68c  ld a1, 0(s2); addi a0, a1, 1; sd a0, 0(s2)   the cursor's p
     +0x694  srli a4, a1, 3; add a4, a4, s4; lb a4, 0(a4); beqz a4 -> +0x6ac, else j +0x1b90
             (+0x1b90 `andi a5, a1, 7; bge a5, a4` -> the error path, else j +0x6ac)
     +0x6ac  lbu a4, 0(a1)                        the kind byte at p
     +0x6b0  auipc a5, 0xfff9d; andi a6, a4, 7; slli a4, a6, 2; addi a5, a5, -0x468 (= 0x20f78, A_OBJ 16)
     +0x6c0  add a4, a4, a5; lw a4, 0(a4); add a4, a4, a5; jr a4   the jump table

   THE THREE ARMS, and why each is cheap. w2.full is 0 or 1 (nlw_fields) and the cursor's n is 0 or not, both fixed
   by the invariant, so this file CASES ON THEM IN Coq and gives the engine a literal: no symbolic branch is left at
   +0x644 or at +0x664. The arm w2.full = 1 writes nothing, the arm n = 0 writes only the spill slot 0xa0, and the
   arm n <> 0 writes that slot and the cursor's 16 bytes.

   THE ONE CHECK THE ENGINE CANNOT DO. The three cursor checks (+0x64c, +0x668, +0x680) pass by computation from the
   one shadow entry `mkSHE 18 0 16` over the cursor's atom (kernel_apre's `range_addressable .. (aarg regs 0) 16`,
   moved to the current memory by kkept: kernel_kit.v kn_cursor_ra). The INPUT BYTE's check at +0x6a0 cannot:
   `tok_branch_pi`'s `slow_block` does not match this layout (the nonzero arm at +0x6a8 is `j +0x1b90`, and the
   `andi a5, a1, 7` sits at the jump target, not at the branch's own fall-through), so the engine would ask for
   `range_addressable p 8`, which is false for a p in the last granule of the input. So this file walks that check
   as kernel_head.v walks its twin: the shadow byte of p is a one-byte read-only region reached through an alias,
   and the run splits UP FRONT on its value s (s = 0, or s <> 0 with (p & 7) < s, which `saddr_ok p s` gives), each
   case being one run whose branches the engine decides from the facts' conditions.

   THE JUMP TABLE. The run stops at +0x6b0 (`dp_tail`), where the state is rebuilt with the registers as atoms and
   ONE region: the jump table at A_OBJ 16 = 0x20f78, its eight 4-byte words from kernel_img.v `ki_jt_val_mem`
   (through kkept's arodata_okP). `andi a6, a4, 7` makes a6 = b mod 8, which the proof pins to each of the eight
   literals (`st_ok_pi_pin_reg'`); the table word is then read by computation, and before the `jr` the proof names
   a4 by the CODE POINTER `SOff A_TEXT (kpc (kind_pc kd))` (`ast_ok_pi_set_reg_fp`; the two denotations agree by
   `kind_pc_jt` and LinkVals, 0x20f78 + ki_jt_words[i] = link_text + kpc (kind_pc i)), so the engine itself takes
   the indirect jump and lands at the kind's entry.

   Section hypotheses: LAWS (the frame's AR_laws, for the run instances and the kit), LV (LinkVals, for the jump
   table's address), KI (KernImg, for its words), TB (PcapSyms, for kernel_kit.v's shadow transport).
   Released proofs (rule 24): this proves no function (kind: segment lemma of kernel's walk); the walk of kernel had
   its search (lookups/walk-lookups.md (internal record, sha256 98fff7967d93): disposition none, written new; confirmed by the rule-24 walk check at 14:56Z).
   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide LinkWalkShadow.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
PcapRelro kernel_c kernel_img kernel_defs kernel_kit kernel_head.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the private cut: +0x6b0, the kind byte in a4, before the jump table's address is formed ---- *)
Definition KP_MID : Z := 0x6b0.

(* ---- the symbolic state at +0x63c.  Atoms as in kernel_head.v: 32 = the cursor's p, 33 = its n, 34 = the input
   byte at p, 35 = shadow(p), 36 = the shadow byte there; s8 (24) carries the shadow address of a0 + 8, so the
   cursor's three checks resolve against the one shadow entry hd_SH.  s3 (19) is NOT set at this cut. ---- *)
Definition dp_regs : list sv := sr_set sr_atoms (Z_to_bv 5 24) (hd_sh 18 8).
(* the spill slots [s1 + 0xa0, s1 + 0xd0): KS_K is written, KS_CN / KS_CSH / KS_W2F are read *)
Definition dp_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) KS_K (KS_W2F + 8) KS_K (KS_K + 8)
    [YP09.mkChunk KS_CN (CVal 8 (SOff 18 8)); YP09.mkChunk KS_CSH (CVal 8 (hd_sh 18 0));
     YP09.mkChunk KS_W2F (CVal 8 (SOff 21 NW_FULL))].
(* w2.full, a literal of the invariant *)
Definition dp_w2f (f : Z) : YP09.region :=
  YP09.mkRegion (Some 21%nat) NW_FULL (NW_FULL + 4) 0 0 [YP09.mkChunk NW_FULL (CVal 4 (SLit f))].
(* the cursor is empty or w2 is full: no input byte, no write to the cursor *)
Definition dp_ss0 (f : Z) (cs : list acond) : sstate :=
  mkSS (kpc KP_LOOP) dp_regs [hd_cur 0 (SOff 33 0); dp_slots; dp_w2f f] None (mkFacts hd_atoms cs hd_alias).
(* a byte is read: the input byte and its shadow byte, and the cursor's 16 bytes are written *)
Definition dp_ss1 (cs : list acond) : sstate :=
  mkSS (kpc KP_LOOP) dp_regs [hd_cur 16 (SOff 33 0); dp_slots; dp_w2f 0; hd_in; hd_ish] None
    (mkFacts hd_atoms cs hd_alias).
Definition dp_c0 : list acond := [mkAC BC_EQ (SOff 33 0) (SLit 0)].
Definition dp_cs (fast : bool) : list acond :=
  if fast then [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_EQ (SOff 36 0) (SLit 0)]
  else [mkAC BC_NE (SOff 33 0) (SLit 0); mkAC BC_NE (SOff 36 0) (SLit 0);
        mkAC BC_LT (SAlu ALU_AND (SOff 32 0) (SLit 7)) (SOff 36 0)].

(* ---- the state at the private cut +0x6b0: the registers as atoms, the jump table the only region ---- *)
Definition dp_jtc (i : nat) : YP09.chunk :=
  YP09.mkChunk (4 * Z.of_nat i) (CVal 4 (SLit (nth i ki_jt_words 0))).
Definition dp_jt : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 16)) 0 32 0 0
    [dp_jtc 0; dp_jtc 1; dp_jtc 2; dp_jtc 3; dp_jtc 4; dp_jtc 5; dp_jtc 6; dp_jtc 7].
Definition dp_tss : sstate := mkSS (kpc KP_MID) sr_atoms [dp_jt] None (mkFacts [] [] []).

(* the registers no run of this phase writes: kregs0's, and s5, s6, s8, s9 of the message loop *)
Definition dp_keep0 : list Z := [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25].
(* the tail (+0x6b0 .. a kind's entry) writes only a4, a5, a6 *)
Definition dp_keept : list Z := [2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 24; 25].
(* the registers a cut of the tail may name *)
Definition dp_rl_ok (rl : list (nat * Z)) : bool :=
  forallb (fun rv => existsb (Nat.eqb (fst rv)) [10; 11; 12; 13; 19; 21; 22; 24; 25]%nat) rl.

Ltac dp_inl := cbn [In]; repeat (first [left; reflexivity | right]).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis KI : KernImg pa_segs B.
Hypothesis TB : PcapSyms B.                                  (* AF0m.v; AD2l.PcapB_syms at the frame's B *)

(* ---- reading a register off a symbolic state ---- *)

Lemma dp_getR : forall E (W : world SEGS) (ms : machine_state) ssx (r : bv 5) e,
  st_ok_pi SEGS pa_val E ssx (restrict (w_H W) ms) -> sr_get (ss_regs ssx) r = e ->
  getr (ms_regs ms) r = sv_denot E e.
Proof.
  intros E W ms ssx r e HS Hr. rewrite (st_ok_pi_restrict_reg (w_H W) E ssx ms r HS), Hr. reflexivity.
Qed.

Lemma dp_getOff : forall E (W : world SEGS) (ms : machine_state) ssx (r : bv 5) nn cc v,
  st_ok_pi SEGS pa_val E ssx (restrict (w_H W) ms) -> sr_get (ss_regs ssx) r = SOff nn cc ->
  ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + cc < 2 ^ 64 ->
  getr (ms_regs ms) r = Z_to_bv 64 (v + cc).
Proof.
  intros E W ms ssx r nn cc v HS Hr Hn Hv Hvc.
  rewrite (dp_getR E W ms ssx r (SOff nn cc) HS Hr), denot_lit_U, (U_atom_off E nn v cc Hn Hv Hvc).
  reflexivity.
Qed.

Lemma dp_getLit : forall E (W : world SEGS) (ms : machine_state) ssx (r : bv 5) z,
  st_ok_pi SEGS pa_val E ssx (restrict (w_H W) ms) -> sr_get (ss_regs ssx) r = SLit z ->
  0 <= z < 2 ^ 64 -> getr (ms_regs ms) r = Z_to_bv 64 z.
Proof.
  intros E W ms ssx r z HS Hr Hz.
  rewrite (dp_getR E W ms ssx r (SLit z) HS Hr), denot_lit_U, U_SLit.
  f_equal. apply zcanon_id. unfold M64. lia.
Qed.

(* the registers a run did not write, moved onto a cut's register list *)
Lemma dp_regs_move : forall (ms0 ms1 : machine_state) rl,
  (forall r, In r (map fst rl) ->
     getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat r)) = getr (ms_regs ms0) (Z_to_bv 5 (Z.of_nat r))) ->
  kregs_eq ms0 rl -> kregs_eq ms1 rl.
Proof.
  intros ms0 ms1 rl HR H. unfold kregs_eq in *. rewrite Forall_forall in H |- *.
  intros ov Hov. rewrite (HR (fst ov) (in_map fst rl ov Hov)). exact (H ov Hov).
Qed.

Lemma dp_regs_sub : forall (ms : machine_state) rl rl',
  kregs_eq ms rl -> (forall ov, In ov rl' -> In ov rl) -> kregs_eq ms rl'.
Proof.
  intros ms rl rl' H Hs. unfold kregs_eq in *. rewrite Forall_forall in H |- *.
  intros ov Hov. exact (H ov (Hs ov Hov)).
Qed.

Lemma dp_rl_ok_in : forall rl, dp_rl_ok rl = true ->
  forall r, In r (map fst rl) -> existsb (Nat.eqb r) [10; 11; 12; 13; 19; 21; 22; 24; 25]%nat = true.
Proof.
  intros rl H r Hr. unfold dp_rl_ok in H. rewrite forallb_forall in H.
  apply in_map_iff in Hr as (ov & <- & Hov). exact (H ov Hov).
Qed.

(* a register of that set is one the tail keeps *)
Lemma dp_keept_of : forall (ms0 ms1 : machine_state),
  (forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) dp_keept = true ->
     getr (ms_regs ms1) r = getr (ms_regs ms0) r) ->
  forall n, existsb (Nat.eqb n) [10; 11; 12; 13; 19; 21; 22; 24; 25]%nat = true ->
  getr (ms_regs ms1) (Z_to_bv 5 (Z.of_nat n)) = getr (ms_regs ms0) (Z_to_bv 5 (Z.of_nat n)).
Proof.
  intros ms0 ms1 H n Hn. apply H.
  cbn [existsb] in Hn.
  repeat (apply orb_true_iff in Hn as [Hn | Hn]; [apply Nat.eqb_eq in Hn; subst n; vm_compute; reflexivity|]).
  discriminate Hn.
Qed.

(* ---- the jump table as a read-only region ---- *)

Lemma dp_chunk4 : forall E (m : word -> option byte) base off v,
  0 <= v < 2 ^ 32 -> val_mem SEGS m (base + off) 4 v ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 4 (SLit v))).
Proof.
  intros E m base off v Hv HV.
  apply (chunk_ok_val SEGS E m base off 4 (SLit v) v).
  - rewrite denot_lit_U, U_SLit. f_equal. apply zcanon_id. unfold M64. lia.
  - change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). exact Hv.
  - cbn; lia.
  - exact HV.
Qed.

Lemma dp_jtw : forall (i : nat), (i < 8)%nat -> 0 <= nth i ki_jt_words 0 < 2 ^ 32.
Proof. intros i Hi. do 8 (destruct i as [|i]; [unfold ki_jt_words; cbn [nth]; lia|]). lia. Qed.

Lemma dp_jt_chunk : forall E (H : word -> bool) (m : word -> option byte) (i : nat), (i < 8)%nat ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS H m) ->
  YP09.chunk_ok SEGS E (mrestrict H m) KI_JT (dp_jtc i).
Proof.
  intros E H m i Hi HRO. unfold dp_jtc.
  apply dp_chunk4; [exact (dp_jtw i Hi) | exact (ki_jt_val_mem SEGS PCAP_RLO PCAP_RHI B KI H m HRO i Hi)].
Qed.

Lemma dp_jt_region : forall E (W : world SEGS) (ms : machine_state),
  base_val E (Some (A_OBJ 16)) = KI_JT ->
  arodata_okP SEGS PCAP_RLO PCAP_RHI B (aview SEGS (w_H W) (ms_mem ms)) ->
  region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) dp_jt.
Proof.
  intros E W ms HBV HRO. unfold dp_jt, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite HBV.
  split; [unfold KI_JT; lia|]. split; [unfold KI_JT; lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
    apply (dp_jt_chunk E (w_H W) (ms_mem ms)); solve [lia | exact HRO].
Qed.

(* a run whose regions have no writable window leaves every byte of memory as it was *)
Lemma dp_un_of : forall E (W : world SEGS) (m m' : word -> option byte) rs,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall (bb : option nat) (wlo whi : Z), In (bb, wlo, whi) (windows rs) -> whi <= wlo) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
  intros E W m m' rs HFr HWin a Ha.
  apply (kept_of_frame (segs := SEGS) E rs (w_H W) m m' (fun _ => False) HFr); [| exact Ha | intros []].
  intros bb wlo whi x Hin Hx. pose proof (HWin bb wlo whi Hin). lia.
Qed.

(* the address of the jump table, and the code pointer of a kind's entry *)
Lemma dp_obj16 : link_obj 16 = KI_JT.
Proof. vm_compute. reflexivity. Qed.

Lemma dp_jt_base : forall (E : env), base_val (Eimg E) (Some (A_OBJ 16)) = KI_JT.
Proof.
  intros E. cbn [base_val]. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_obj LV 16%nat) by (unfold link_nobj; lia). rewrite dp_obj16.
  apply unsigned_lit_small. unfold KI_JT. lia.
Qed.

Lemma dp_jt_tgt : forall (kd : Z), 0 <= kd < 8 ->
  link_obj 16 + nth (Z.to_nat kd) ki_jt_words 0 = link_text + kpc (kind_pc kd).
Proof.
  intros kd Hkd.
  assert (Hk : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3 \/ kd = 4 \/ kd = 5 \/ kd = 6 \/ kd = 7) by lia.
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma dp_tgt_facts : forall kd, 0 <= kd < 8 ->
  0 <= pa_val A_TEXT + kpc (kind_pc kd) < 2 ^ 64 /\ (pa_val A_TEXT + kpc (kind_pc kd)) mod 2 = 0.
Proof.
  intros kd Hkd. rewrite (lv_text LV).
  assert (Hk : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3 \/ kd = 4 \/ kd = 5 \/ kd = 6 \/ kd = 7) by lia.
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    match goal with
    | |- context [link_text + kpc (kind_pc ?k)] =>
        let v := eval vm_compute in (link_text + kpc (kind_pc k)) in
        replace (link_text + kpc (kind_pc k)) with v by (vm_compute; reflexivity)
    end; (split; [lia | reflexivity]).
Qed.

(* the target range of the kind entries, and link_text as a number *)
Lemma dp_toff : forall kd, 0 <= kd < 8 ->
  0 <= link_text < 2 ^ 64 /\ 0 <= link_text + kpc (kind_pc kd) < 2 ^ 64.
Proof.
  intros kd Hkd.
  assert (Ht : link_text = 532940) by (vm_compute; reflexivity).
  assert (Hk : kd = 0 \/ kd = 1 \/ kd = 2 \/ kd = 3 \/ kd = 4 \/ kd = 5 \/ kd = 6 \/ kd = 7) by lia.
  destruct Hk as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]];
    match goal with
    | |- context [kpc (kind_pc ?k)] =>
        let v := eval vm_compute in (kpc (kind_pc k)) in
        replace (kpc (kind_pc k)) with v by (vm_compute; reflexivity)
    end; rewrite Ht; split; lia.
Qed.

Lemma dp_objrng : 0 <= link_obj 16 < 2 ^ 64.
Proof. rewrite dp_obj16. unfold KI_JT. lia. Qed.

Lemma dp_objw : forall kd, 0 <= kd < 8 ->
  0 <= link_obj 16 + nth (Z.to_nat kd) ki_jt_words 0 < 2 ^ 64.
Proof.
  intros kd Hkd. pose proof (dp_jtw (Z.to_nat kd) ltac:(lia)). rewrite dp_obj16. unfold KI_JT. lia.
Qed.

(* the pc and the shape of a run's end state *)
Lemma dp_kms : forall E (W : world SEGS) ss (msF : machine_state) pcF,
  st_ok_pi SEGS pa_val E ss (restrict (w_H W) msF) -> ss_resv ss = None -> ss_pc ss = kpc pcF ->
  kms pcF msF.
Proof.
  intros E W ss msF pcF HS Hrv Hpc.
  pose proof (st_ok_pi_restrict_mkst (w_H W) E ss msF HS Hrv) as Hsh. rewrite Hpc in Hsh.
  unfold kms. rewrite Hsh. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst].
  repeat split; reflexivity.
Qed.

(* ==========================================================================
   THE TAIL: +0x6b0 (the kind byte b in a4) -> the kind's entry, through the jump table.
   The run +0x6b0..+0x6b8 is shared; then, for each of the eight values of b mod 8, a6 is pinned to that
   literal (st_ok_pi_pin_reg'), the table word is read by computation, and before the `jr` at +0x6cc the
   proof names a4 by the CODE POINTER SOff A_TEXT (kpc (kind_pc kd)) (ast_ok_pi_set_reg_fp; the two
   denotations agree by kind_pc_jt through dp_jt_tgt and LinkVals), so the engine itself takes the indirect
   jump.  The tail writes no byte of memory: its one region, the jump table, has an empty write window.
   ========================================================================== *)

Ltac dp_awr_jt :=
  cbv [dp_tss]; cbn [ss_mem];
  apply awr_ok_x_cons; [| apply awr_ok_x_nil];
  let xx := fresh "xx" in let Hxx := fresh "Hxx" in
  intros xx Hxx; cbv [dp_jt] in Hxx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hxx; lia.

Ltac dp_nowin :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let Hin := fresh "Hin" in
  intros bb wlo whi Hin; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; lia |]); destruct Hin.

(* accumulate "the memory did not change" and "presence grew" over one more run *)
Ltac dp_acc W0 base0 UNa HPa :=
  match goal with
  | HFr0 : frame_of ?E0 ?rs0 (mrestrict _ ?m0) (mrestrict _ ?m1), HG0 : mem_grows _ _ |- _ =>
      let U := fresh "Unew" in let P := fresh "Pnew" in
      assert (U : forall a, 0 <= a < 2 ^ 64 -> aview pa_segs (w_H W0) m1 a = aview pa_segs (w_H W0) base0 a)
        by (intros a Ha; rewrite (dp_un_of E0 W0 m0 m1 rs0 HFr0 ltac:(dp_nowin) a Ha); exact (UNa a Ha));
      assert (P : forall a, apresent (w_H W0) base0 a -> apresent (w_H W0) m1 a)
        by (intros a Hp; exact (kh_apres_grows (w_H W0) m0 m1 a HG0 (HPa a Hp)));
      clear HFr0 HG0 UNa HPa; rename U into UNa; rename P into HPa
  end.

Lemma dp_tail : forall (Q : world SEGS -> config -> Prop)
    (cx : kcx) (fpos k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model)
    (rl : list (nat * Z)) (sl : list (Z * Z)) (sh : list Z) (live : bool) (adv : Z) (g : option Z) (b : Z),
  kbase SK B cx ->
  ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
    (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  kat B cx fpos KP_MID ((14%nat, b) :: rl) sl sh live adv g k2 ly3 S3 W3 ms3 md3 ->
  0 <= b < 256 -> dp_rl_ok rl = true -> kslots_okb sl = true -> (length sh <= 2048)%nat ->
  (forall (ms' : machine_state) (md' : Model),
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
       (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     (forall a, 0 <= a < 2 ^ 64 ->
        aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
     kat B cx fpos (kind_pc (b mod 8)) ((16%nat, b mod 8) :: rl) sl sh live adv g k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros Q cx fpos k2 ly3 S3 W3 ms3 md3 rl sl sh live adv g b HB HJ3 HK Hb Hrlok Hslok Hshl CONT.
pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & _ & Hkjbk & Hkkept & _ & _ & _).
pose proof Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
pose proof Hkkept as (_ & HRO3).
pose proof HB as ((HJ0 & HGok & _) & _).
assert (Hb8 : 0 <= b mod 8 < 8) by (apply Z.mod_pos_bound; lia).
remember (hd_E ms3 0 0 0 0) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
assert (EA : ew E A_TEXT = Z_to_bv 64 link_text).
{ rewrite HEdef. unfold hd_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_text LV). reflexivity. }
assert (EO : ew E (A_OBJ 16) = Z_to_bv 64 (link_obj 16)).
{ rewrite HEdef. unfold hd_E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (lv_obj LV 16%nat) by (unfold link_nobj; lia). reflexivity. }
assert (E14 : ew E 14%nat = Z_to_bv 64 b).
{ rewrite HEdef. unfold hd_E.
  rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 14%nat (Z_to_bv 5 (Z.of_nat 14)) ltac:(vm_compute; reflexivity)).
  exact (kn_reg_of ms3 _ 14%nat b Hkre ltac:(dp_inl)). }
assert (HS0 : st_ok_pi SEGS pa_val E dp_tss (restrict (w_H W3) ms3)).
{ rewrite (kh_ms_shape ms3 (BASE + kpc KP_MID) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  unfold dp_tss. apply pa_entry_st_ok_full.
  - rewrite HEdef. unfold hd_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply dp_jt_region; [rewrite HEdef; unfold hd_E; apply dp_jt_base | exact HRO3].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. tauto. }
assert (SHOK : sh_ok SEGS hd_Bx (@nil shent) E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
assert (UNacc : forall a, 0 <= a < 2 ^ 64 ->
          aview SEGS (w_H W3) (ms_mem ms3) a = aview SEGS (w_H W3) (ms_mem ms3) a) by (intros; reflexivity).
assert (HPacc : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms3) a)
  by (intros a Hp; exact Hp).
pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
pose proof HS0 as HS. pose proof HJ3 as HJ.
(* +0x6b0 .. +0x6b8: the kind byte's low three bits *)
paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc 0x6b8).
{ dp_awr_jt. }
repeat rewrite wvb_collapse in HJ.
dp_acc W3 (ms_mem ms3) UNacc HPacc.
lazymatch type of HS with
| st_ok_pi _ _ _ _ (restrict _ ?msA) =>
  assert (R16 : getr (ms_regs msA) (Z_to_bv 5 16) = Z_to_bv 64 (b mod 8));
  [ pose proof (dp_getR E W3 msA _ (Z_to_bv 5 16) (SAlu ALU_AND (SOff 14 0) (SLit 7)) HS
                  ltac:(vm_compute; reflexivity)) as RR;
    rewrite RR, denot_lit_U; f_equal;
    rewrite U_SAlu; cbn [zalu_raw]; rewrite U_SLit;
    rewrite (U_atom_off E 14%nat b 0 E14 ltac:(lia) ltac:(lia)), Z.add_0_r;
    change (zcanon 7) with 7;
    replace (Z.land b 7) with (b mod 8)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
    apply zcanon_id; unfold M64; lia
  | ]
end.
assert (CASES : b mod 8 = 0 \/ b mod 8 = 1 \/ b mod 8 = 2 \/ b mod 8 = 3 \/ b mod 8 = 4 \/
                b mod 8 = 5 \/ b mod 8 = 6 \/ b mod 8 = 7) by lia.
destruct CASES as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]]]; rewrite Hc in R16, CONT; clear Hc Hb8.
all: lazymatch type of R16 with
| getr (ms_regs ?msA) _ = Z_to_bv 64 ?kd =>
  pose proof (st_ok_pi_pin_reg' E _ (restrict (w_H W3) msA) (Z_to_bv 5 16) kd HS R16
                ltac:(vm_compute; reflexivity)) as HPIN
end.
all: clear HS; rename HPIN into HS.
(* +0x6b8 .. +0x6cc: the table word *)
all: paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc 0x6cc); [ dp_awr_jt | ].
all: repeat rewrite wvb_collapse in HJ.
all: dp_acc W3 (ms_mem ms3) UNacc HPacc.
(* name a4 by the code pointer of the kind's entry, and take the jr *)
all: lazymatch type of CONT with
| forall _ _, _ -> _ -> _ -> kat _ _ _ (kind_pc ?kd) _ _ _ _ _ _ _ _ _ _ _ _ -> _ =>
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msA) =>
    assert (HC : sv_denot E (SOff A_TEXT (kpc (kind_pc kd))) = getr (ms_regs msA) (Z_to_bv 5 14));
    [ rewrite (dp_getOff E W3 msA _ (Z_to_bv 5 14) (A_OBJ 16) (nth (Z.to_nat kd) ki_jt_words 0)
                 (link_obj 16) HS ltac:(vm_compute; reflexivity) EO dp_objrng (dp_objw kd ltac:(lia)));
      rewrite denot_lit_U,
        (U_atom_off E A_TEXT link_text (kpc (kind_pc kd)) EA
           (proj1 (dp_toff kd ltac:(lia))) (proj2 (dp_toff kd ltac:(lia))));
      f_equal; symmetry; apply dp_jt_tgt; lia
    | ];
    pose proof (ast_ok_pi_set_reg_fp E _ (restrict (w_H W3) msA) (Z_to_bv 5 14)
                  (SOff A_TEXT (kpc (kind_pc kd))) HS ltac:(vm_compute; reflexivity) HC) as HPIN2
  end;
  clear HS; rename HPIN2 into HS;
  paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc (kind_pc kd)); [ dp_awr_jt | ];
  repeat rewrite wvb_collapse in HJ;
  dp_acc W3 (ms_mem ms3) UNacc HPacc;
  lazymatch type of HS with
  | st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    assert (RK : forall r : bv 5, existsb (Z.eqb (bv_unsigned r)) dp_keept = true ->
              getr (ms_regs msF) r = getr (ms_regs ms3) r)
      by (exact (kh_reg_same E dp_tss _ (w_H W3) ms3 msF dp_keept HS0 HS
                   ltac:(vm_compute; reflexivity)));
    apply CONT;
    [ exact HJ
    | exact UNacc
    | exact HPacc
    | apply (kat_frame SK B LAWS (fun _ : Z => False) cx fpos KP_MID ((14%nat, b) :: rl) sl sh live adv g
               k2 ly3 S3 W3 ms3 md3 (kind_pc kd) ((16%nat, kd) :: rl) sl W3 msF _ HB HK);
      [ exact (dp_kms E W3 _ msF (kind_pc kd) HS ltac:(vm_compute; reflexivity)
                 ltac:(vm_compute; reflexivity))
      | unfold kregs0 in Hkr0 |- *;
        refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
        rewrite RK by (vm_compute; reflexivity); tauto
      | apply Forall_cons;
        [ cbn [fst snd];
          exact (dp_getLit E W3 msF _ (Z_to_bv 5 (Z.of_nat 16)) kd HS
                   ltac:(vm_compute; reflexivity) ltac:(lia))
        | apply (dp_regs_move ms3 msF rl); [| exact (Forall_inv_tail Hkre)];
          intros r Hr; exact (dp_keept_of ms3 msF RK r (dp_rl_ok_in rl Hrlok r Hr)) ]
      | apply incl_refl
      | exact Hshl
      | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
      | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
      | intros a Ha _; exact (UNacc a Ha)
      | exact HPacc
      | intros a []
      | unfold kX_miss; repeat apply conj;
        [ intros a _ F; exact F
        | intros ov Hov; split;
          [ exact (kslots_okb_spec sl Hslok ov Hov) | intros a _ F; exact F ]
        | intros a _ F; exact F | intros a _ F; exact F | intros a _ F; exact F
        | intros a _ F; exact F | intros a _ F; exact F | intros a _ F; exact F ] ] ]
  end
end.
Qed.

(* a cut's register list, read down to a sub-list *)
Lemma dp_kat_rl : forall cx' fpos' pc rl rl' sl sh live adv' g k2' ly S (W : world SEGS) ms md,
  kat B cx' fpos' pc rl sl sh live adv' g k2' ly S W ms md ->
  (forall ov, In ov rl' -> In ov rl) ->
  kat B cx' fpos' pc rl' sl sh live adv' g k2' ly S W ms md.
Proof.
  intros cx' fpos' pc rl rl' sl sh live adv' g k2' ly S W ms md
    (H1 & H2 & HRL & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12) Hin.
  unfold kat. refine (conj H1 (conj H2 (conj _ (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9
    (conj H10 (conj H11 H12))))))))))).
  unfold kregs_eq in HRL |- *. rewrite Forall_forall in HRL |- *. intros ov Hov. exact (HRL ov (Hin ov Hov)).
Qed.

(* w2's two fields are no byte the phase writes *)
Lemma dp_w2_miss : forall cx fpos k2 ly3 S3 md3 a,
  kbase SK B cx -> kjbk B cx fpos k2 ly3 S3 md3 ->
  kW2 cx fpos + NW_N <= a < kW2 cx fpos + NW_FULL + 4 ->
  ~ (ka0 cx <= a < ka0 cx + 16 \/ ksp1 cx + KS_K <= a < ksp1 cx + KS_K + 8).
Proof.
  intros cx fpos k2 ly3 S3 md3 a HB HJB Ha.
  pose proof (kn_sp1 SK B cx HB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (kn_sp SK B cx HB) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB HJB) as (F1 & F2 & F3 & F4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  intros [Hx | Hx].
  - assert (Hrd : kernel_ard SEGS (k_regs cx) (km0 cx) a) by (apply kn_ard_cur; exact Hx).
    destruct (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 a HB HJB Hrd) as (_ & _ & HF & _).
    apply HF. unfold kW2, KN_W2, NW_N, NW_FULL in Ha. lia.
  - unfold kW2, KN_W2, NW_N, NW_FULL, KS_K in *. lia.
Qed.

(* ==========================================================================
   THE PHASE at one cut of kin_loop (+0x63c).
   ========================================================================== *)
Section h.
Variable cx : kcx.
Variables fpos k2 : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variable ms3 : machine_state.
Variable md3 : Model.
Variables c ci j m k n f adv : Z.

Definition dp_sl0 : list (Z * Z) :=
  kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m)].

Hypothesis Hkm : 0 <= k < m /\ 1 <= m <= 5.
Hypothesis HB : kbase SK B cx.
Hypothesis HJ3 : ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx)
  (k_S cx) (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2.
Hypothesis HW : kw_at W3 ms3 (kW2 cx fpos) n f.
Hypothesis HK : kat B cx fpos KP_LOOP
  [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N); (14%nat, k); (22%nat, m)]
  dp_sl0 (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms3 md3.

(* the bytes this phase may write: the cursor's 16 and the spill slot KS_K *)
Definition dp_X (a : Z) : Prop :=
  (ka0 cx <= a < ka0 cx + 16) \/ (ksp1 cx + KS_K <= a < ksp1 cx + KS_K + 8).

Lemma dp_jbk : kjbk B cx fpos k2 ly3 S3 md3.
Proof. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

Lemma dp_kept : kkept B cx fpos W3 ms3.
Proof. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.

(* where a byte of the cursor and a byte of the input are *)
Lemma dp_CA : forall x, ka0 cx <= x < ka0 cx + 16 ->
  0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x) /\
  ~ (kF cx fpos <= x < kF cx fpos + 16384) /\ ~ (ksp cx - KERNEL_AK <= x < ksp cx).
Proof.
  intros x Hx. apply (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 x HB dp_jbk).
  apply kn_ard_cur. exact Hx.
Qed.

Lemma dp_CI : forall x, k_wp cx <= x < k_wp cx + k_wn cx ->
  0 <= x < 2 ^ 47 /\ (x < kLowMemEnd \/ kHighMemBeg <= x) /\
  ~ (kF cx fpos <= x < kF cx fpos + 16384) /\ ~ (ksp cx - KERNEL_AK <= x < ksp cx).
Proof.
  intros x Hx. apply (kn_ard_loc SK B LAWS cx fpos k2 ly3 S3 md3 x HB dp_jbk).
  exact (kn_ard_inp SK B cx x Hx HB).
Qed.

(* THE LANDING: the run wrote only the cursor and the slot KS_K *)
Lemma dp_land : forall (ms' : machine_state) md' pc' rl' adv' nl sl',
  kms pc' ms' -> kregs0 cx ms' -> kregs_eq ms' rl' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  0 <= adv' <= k_wn cx ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx) (k_wp cx + adv') ->
  au64_at SEGS (rdW W3 (ms_mem ms')) (ka0 cx + 8) (k_wn cx - adv') ->
  kslots_eq cx W3 ms' nl -> (forall ov, In ov sl' -> In ov (dp_sl0 ++ nl)) ->
  kat B cx fpos pc' rl' sl' (kfsh 0xf8 0 0xf3) true adv' (Some j) k2 ly3 S3 W3 ms' md'.
Proof.
  intros ms' md' pc' rl' adv' nl sl' Hkms HR0 HRL UN HP Hfds Hfs Hadv Hp' Hn' Hnl Hsub.
  pose proof HK as (_ & _ & _ & _ & _ & Hksh & Hksl & _ & _ & Hkcur & _ & _).
  pose proof (kn_sp1 SK B cx HB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (kn_sp SK B cx HB) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB dp_jbk) as (F1 & F2 & F3 & F4).
  pose proof (kn_apre SK B cx HB) as (Agnl & Ala & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (Hfb : fs_frame_bytes KN_CID = 16384) by reflexivity.
  assert (HFSH : SHADOW_OFF + 512 <= kFSH cx fpos /\ kFSH cx fpos + 0x448 <= SHADOW_OFF + 2 ^ 44)
    by (unfold kFSH, shadow_of_addr, SHADOW_OFF in *; lia).
  assert (Hlen : Z.of_nat (length (kfsh 0xf8 0 0xf3)) = 0x448) by (rewrite kfsh_length; reflexivity).
  (* a slot of the cut avoids the one the phase writes *)
  pose proof (kslots_okb_spec dp_sl0 eq_refl) as SOK.
  pose proof (kslots_avoidb_spec KS_K (KS_K + 8) dp_sl0 eq_refl) as SAV.
  apply (kat_reframe SK B LAWS dp_X cx fpos KP_LOOP _ dp_sl0 (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3
           W3 ms3 md3 pc' rl' sl' (kfsh 0xf8 0 0xf3) adv' W3 ms' md' HB HK Hkms HR0 HRL Hfds Hfs UN HP).
  - (* every byte of dp_X is one kernel may write *)
    intros a [Ha | Ha].
    + left. unfold kE, inFP. exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
      split; [unfold kernel_awr; dp_inl | cbn [fst snd]; unfold ka0 in Ha; lia].
    + apply (kX_in_sl SK B cx fpos KS_K (KS_K + 8) a HB ltac:(unfold KS_K; lia) ltac:(unfold KS_K; lia));
      unfold KS_K in *; lia.
  - (* the thirteen saved words *)
    intros a Ha [Hx | Hx]; [destruct (dp_CA a Hx) as (_ & _ & _ & Hw); apply Hw; rewrite HKA; lia
                           | unfold KS_K in Hx; lia].
  - (* F's three header words *)
    intros a Ha [Hx | Hx]; [destruct (dp_CA a Hx) as (_ & _ & HF & _); apply HF; lia
                           | unfold KS_K in Hx; lia].
  - (* F's flag word *)
    rewrite Hfb. intros a Ha [Hx | Hx]; [destruct (dp_CA a Hx) as (_ & _ & HF & _); apply HF; lia
                                        | unfold KS_K in Hx; lia].
  - (* g_nl *)
    unfold apart_gnl in Agnl.
    intros a Ha [Hx | Hx]; unfold LA_G_NL, NK_SIZE, KS_K in *; lia.
  - (* long_alias *)
    unfold apart in Ala.
    intros a Ha [Hx | Hx]; unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE, KS_K in *; lia.
  - (* F's shadow bytes *)
    apply (kshadow_frame B LAWS dp_X cx fpos (kfsh 0xf8 0 0xf3) k2 ly3 S3 md3 W3 ms3 W3 ms' dp_jbk UN
             (kfsh_fits 0xf8 0 0xf3)); [| exact Hksh].
    intros a Ha [Hx | Hx]; rewrite Hlen in Ha.
    + destruct (dp_CA a Hx) as (_ & [Hq | Hq] & _); rewrite ?C3, ?C5 in Hq; unfold SHADOW_OFF in *; lia.
    + unfold KS_K, SHADOW_OFF in *; lia.
  - (* the slots *)
    apply (kn_kslots_sub cx W3 ms' (dp_sl0 ++ nl) sl'); [| exact Hsub].
    unfold kslots_eq. apply Forall_app. split; [| exact Hnl].
    change (kslots_eq cx W3 ms' dp_sl0).
    apply (kslots_frame SK B dp_X cx dp_sl0 dp_sl0 W3 ms3 W3 ms' HB UN (incl_refl _)); [| exact Hksl].
    intros ov Hov. pose proof (SOK ov Hov) as S1. pose proof (SAV ov Hov) as S2.
    split; [exact S1|].
    intros a Ha [Hx | Hx].
    + destruct (dp_CA a Hx) as (_ & _ & _ & Hw). apply Hw. rewrite HKA. lia.
    + unfold KS_K in *. lia.
  - (* the cursor *)
    destruct Hkcur as (_ & _ & _ & HCW).
    split; [exact Hadv|]. split; [exact Hp'|]. split; [exact Hn'|].
    intros i Hi. exact (writable_at_grows SEGS _ _ _ (kk_grows_of_apresent _ _ _ _ HP) (HCW i Hi)).
Qed.

(* ---- the environment at the cut ---- *)

Lemma dp_Ef : forall p nv d s,
  ew (hd_E ms3 p nv d s) 18%nat = w64 (ka0 cx) /\ ew (hd_E ms3 p nv d s) 9%nat = w64 (ksp1 cx) /\
  ew (hd_E ms3 p nv d s) 20%nat = w64 SHADOW_OFF /\ ew (hd_E ms3 p nv d s) 21%nat = w64 (kW2 cx fpos) /\
  ew (hd_E ms3 p nv d s) 24%nat = w64 (kS8 cx) /\
  ew (hd_E ms3 p nv d s) 32%nat = w64 p /\ ew (hd_E ms3 p nv d s) 33%nat = w64 nv /\
  ew (hd_E ms3 p nv d s) 34%nat = w64 d /\ ew (hd_E ms3 p nv d s) 35%nat = w64 (SHADOW_OFF + p / 8) /\
  ew (hd_E ms3 p nv d s) 36%nat = w64 s.
Proof.
  intros p nv d s. pose proof HK as (_ & Hkr0 & Hkre & _).
  destruct Hkr0 as (R2 & R9 & R8 & R3 & R4 & R18 & R20).
  pose proof (kn_reg_of ms3 _ 21%nat (kW2 cx fpos) Hkre ltac:(dp_inl)) as R21.
  pose proof (kn_reg_of ms3 _ 24%nat (kS8 cx) Hkre ltac:(dp_inl)) as R24.
  assert (ER : forall (q : nat) (r : bv 5), Z.of_nat q = bv_unsigned r ->
            ew (hd_E ms3 p nv d s) q = getr (ms_regs ms3) r)
    by (intros q r Hq; exact (ew_Eimg_Ereg_nat _ _ q r Hq)).
  assert (EXT : forall q, (q < 5)%nat -> ew (hd_E ms3 p nv d s) (32 + q) =
            nth q [w64 p; w64 nv; w64 d; w64 (SHADOW_OFF + p / 8); w64 s] (Z_to_bv 64 0))
    by (intros q Hq; unfold hd_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  split; [rewrite (ER 18%nat 18%bv eq_refl); exact R18|].
  split; [rewrite (ER 9%nat 9%bv eq_refl); exact R9|].
  split; [rewrite (ER 20%nat 20%bv eq_refl); exact R20|].
  split; [rewrite (ER 21%nat 21%bv eq_refl); exact R21|].
  split; [rewrite (ER 24%nat 24%bv eq_refl); exact R24|].
  split; [exact (EXT 0%nat ltac:(lia))|]. split; [exact (EXT 1%nat ltac:(lia))|].
  split; [exact (EXT 2%nat ltac:(lia))|]. split; [exact (EXT 3%nat ltac:(lia))|].
  exact (EXT 4%nat ltac:(lia)).
Qed.

(* the cursor's shadow entry *)
Lemma dp_shok : forall p nv d s,
  sh_ok SEGS hd_Bx hd_SH (hd_E ms3 p nv d s) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
  intros p nv d s. destruct (dp_Ef p nv d s) as (E18 & _ & E20 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (dp_CA (ka0 cx) ltac:(lia)) as (Ha0 & _). pose proof (dp_CA (ka0 cx + 15) ltac:(lia)) as (Ha15 & _).
  apply Forall_cons; [|apply Forall_nil].
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold hd_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom _ 18 (ka0 cx) E18) by lia.
  split.
  - rewrite <- (aview_rd_of SEGS). rewrite Z.add_0_r. replace (16 - 0) with 16 by lia.
    exact (kn_cursor_ra SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ3 dp_jbk dp_kept).
  - intros a Ha. change (Z.min 0 16) with 0 in Ha. change (Z.max 0 16) with 16 in Ha.
    destruct (dp_CA a ltac:(lia)) as (_ & [Hq | Hq] & _);
      unfold kLowMemEnd, kHighMemBeg, SHADOW_OFF in *; lia.
Qed.

(* ---- the numbers the regions' disjointness needs ---- *)
Lemma dp_geo :
  0 <= ka0 cx /\ ka0 cx + 16 <= 2 ^ 47 /\
  (ka0 cx + 16 <= kLowMemEnd \/ kHighMemBeg <= ka0 cx) /\
  4096 <= kW2 cx fpos /\ kW2 cx fpos + NW_SIZE <= alloc_ceiling /\
  ksp cx - 368 <= ksp1 cx <= ksp cx - 352 /\ ksp1 cx mod 32 = 0 /\ 2 ^ 46 <= ksp1 cx /\
  ksp1 cx + 0xf8 <= ksp cx - 104 /\ alloc_ceiling + KERNEL_AK <= ksp cx /\ ksp cx <= 2 ^ 47 /\
  0 <= k_wp cx /\ k_wp cx + k_wn cx <= 2 ^ 47 /\
  (k_wp cx + k_wn cx <= ka0 cx \/ ka0 cx + 16 <= k_wp cx).
Proof.
  pose proof (kn_sp1 SK B cx HB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (kn_sp SK B cx HB) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB dp_jbk) as (F1 & F2 & F3 & F4).
  pose proof (kn_apre SK B cx HB) as (_ & _ & _ & _ & HAMR & HKAP).
  destruct HKAP as (_ & _ & _ & HAPCi).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (dp_CA (ka0 cx) ltac:(lia)) as (Ha0 & Hb0 & _).
  pose proof (dp_CA (ka0 cx + 15) ltac:(lia)) as (Ha15 & Hb15 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HWPr & HWNr & _).
  assert (A1 : 0 <= ka0 cx) by lia.
  assert (A2 : ka0 cx + 16 <= 2 ^ 47) by lia.
  assert (A3 : ka0 cx + 16 <= kLowMemEnd \/ kHighMemBeg <= ka0 cx)
    by (destruct Hb0 as [H0 | H0]; destruct Hb15 as [H1 | H1];
        unfold kLowMemEnd, kHighMemBeg in *; lia).
  assert (A4 : 4096 <= kW2 cx fpos) by (unfold kW2, KN_W2; lia).
  assert (A5 : kW2 cx fpos + NW_SIZE <= alloc_ceiling) by (unfold kW2, KN_W2, NW_SIZE; lia).
  assert (A6 : 0 <= k_wp cx /\ k_wp cx + k_wn cx <= 2 ^ 47)
    by (unfold amem_range, kLowMemEnd, kHighMemEnd in HAMR; lia).
  assert (A7 : k_wp cx + k_wn cx <= ka0 cx \/ ka0 cx + 16 <= k_wp cx)
    by (unfold apart in HAPCi; change (aarg (k_regs cx) 0) with (ka0 cx) in HAPCi; lia).
  repeat split; try tauto; try lia.
Qed.

(* ---- the regions ---- *)
Lemma dp_rcur : forall d s w, 0 <= w <= 16 ->
  region_ok SEGS (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (mrestrict (w_H W3) (ms_mem ms3))
    (hd_cur w (SOff 33 0)).
Proof.
  intros d s w Hw.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & _ & _ & _ & _ & E32 & E33 & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hkcur & _). destruct Hkcur as (Hadv & HCP & HCN & HCW).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  assert (BV18 : base_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (Some 18%nat) = ka0 cx)
    by (cbn [base_val]; rewrite E18; unfold w64; apply unsigned_lit_small; lia).
  unfold hd_cur, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite BV18. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (HCW o ltac:(lia))|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS _ _ (ka0 cx) 0 8 (SOff 32 0) (k_wp cx + adv));
      [apply sv_off0; exact E32 | cbn; lia | cbn; lia | rewrite Z.add_0_r; exact HCP].
  - apply (chunk_ok_val SEGS _ _ (ka0 cx) 8 8 (SOff 33 0) (k_wn cx - adv));
      [apply sv_off0; exact E33 | cbn; lia | cbn; lia | exact HCN].
Qed.

Lemma dp_rslots : forall d s,
  region_ok SEGS (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (mrestrict (w_H W3) (ms_mem ms3)) dp_slots.
Proof.
  intros d s.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & E9 & E20 & E21 & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & Hksl & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HPRES.
  pose proof (kn_slot_of cx W3 ms3 dp_sl0 KS_CN (ka0 cx + 8) Hksl ltac:(unfold dp_sl0; dp_inl)) as SL_CN.
  pose proof (kn_slot_of cx W3 ms3 dp_sl0 KS_CSH (shadow_of_addr SHADOW_OFF (ka0 cx)) Hksl
                ltac:(unfold dp_sl0; dp_inl)) as SL_CSH.
  pose proof (kn_slot_of cx W3 ms3 dp_sl0 KS_W2F (kW2 cx fpos + NW_FULL) Hksl
                ltac:(unfold dp_sl0; dp_inl)) as SL_W2F.
  assert (BV9 : base_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (Some 9%nat) = ksp1 cx)
    by (cbn [base_val]; rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  pose proof (kn_sp1 SK B cx HB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold dp_slots, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite BV9. unfold KS_K, KS_W2F, KS_CN, KS_CSH.
  split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (kn_apresent_writable SEGS); apply HPRES; rewrite HKA in *; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (kh_chunk_rd _ (w_H W3) (ms_mem ms3) (ksp1 cx) 0xb0 (SOff 18 8) (ka0 cx + 8));
      [| exact SL_CN].
    cbn [sv_denot]. rewrite E18. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
  - apply (kh_chunk_rd _ (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc0 (hd_sh 18 0)
             (shadow_of_addr SHADOW_OFF (ka0 cx))); [| exact SL_CSH].
    rewrite (kh_denot_sh _ 18%nat (ka0 cx) 0 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold shadow_of_addr. rewrite Z.add_0_r. reflexivity.
  - apply (kh_chunk_rd _ (w_H W3) (ms_mem ms3) (ksp1 cx) 0xc8 (SOff 21 NW_FULL)
             (kW2 cx fpos + NW_FULL)); [| exact SL_W2F].
    cbn [sv_denot]. rewrite E21. unfold w64. rewrite unsigned_lit_small by (unfold NW_FULL, NW_SIZE in *; lia).
    reflexivity.
Qed.

Lemma dp_rw2f : forall d s,
  region_ok SEGS (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (mrestrict (w_H W3) (ms_mem ms3)) (dp_w2f f).
Proof.
  intros d s.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (_ & _ & _ & E21 & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof HW as (Hw0 & Hw64 & Hpres & Hn & Hf & Hnr & Hfr).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (BV21 : base_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (Some 21%nat) = kW2 cx fpos)
    by (cbn [base_val]; rewrite E21; unfold w64; apply unsigned_lit_small;
        unfold NW_FULL, NW_SIZE in *; lia).
  unfold dp_w2f, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite BV21. unfold NW_FULL, NW_SIZE in *.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil]. apply dp_chunk4; [lia | exact Hf].
Qed.

(* ---- the input byte at the cursor and its shadow byte ---- *)
Lemma dp_sb : adv < k_wn cx -> exists s,
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s /\
  saddr_ok (k_wp cx + adv) s.
Proof.
  intros Hadv.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  exact (proj1 (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) HB HJ3 dp_jbk
                  dp_kept ltac:(lia))).
Qed.

Lemma dp_db : adv < k_wn cx -> exists bb : byte, mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some bb.
Proof.
  intros Hadv.
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HD & HDL & _).
  destruct HD as (_ & _ & HD).
  assert (Hi : (Z.to_nat adv < length (k_d cx))%nat) by lia.
  destruct (nth_error (k_d cx) (Z.to_nat adv)) as [b0|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  exists b0. pose proof (HD (Z.to_nat adv) Hi) as Hm. rewrite Eb, Z2Nat.id in Hm by lia.
  rewrite <- Hm.
  apply (kn_mbyte_of_aview SEGS (w_H (k_W cx)) (w_H W3) (k_memc cx) (ms_mem ms3) (k_wp cx + adv)
           (k_wp cx + adv)).
  exact (proj2 (kn_input_at SK B LAWS TB cx fpos k2 ly3 S3 W3 ms3 md3 (k_wp cx + adv) HB HJ3 dp_jbk
                  dp_kept ltac:(lia))).
Qed.

(* ---- the facts' three parts, and the seat ---- *)
Lemma dp_atoms_ok : forall d s, 0 <= d < 256 -> 0 <= s < 8 ->
  atoms_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) hd_atoms.
Proof.
  intros d s Hd Hs.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & E9 & E20 & _ & _ & _ & _ & E34 & _ & E36).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  unfold hd_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E18, E9, E20, E34, E36. unfold w64.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; first [lia | exact G7 | exact I].
Qed.

Lemma dp_alias_ok : forall d s,
  alias_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) hd_alias.
Proof.
  intros d s.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (_ & _ & E20 & _ & _ & E32 & _ & _ & E35 & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  unfold hd_alias. cbn [alias_ok]. split; [|exact I].
  rewrite (kh_denot_sh _ 32%nat (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia) ltac:(lia) E20).
  rewrite (sv_off0 _ 35%nat _ E35). rewrite Z.add_0_r. reflexivity.
Qed.

Lemma dp_seat_core : forall d s (rs : smem) (cs : list acond),
  0 <= d < 256 -> 0 <= s < 8 ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
            (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  pairwise_disjoint (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) rs ->
  conds_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) cs ->
  st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
    (mkSS (kpc KP_LOOP) dp_regs rs None (mkFacts hd_atoms cs hd_alias)) (restrict (w_H W3) ms3).
Proof.
  intros d s rs cs Hd Hs Hwf Hrok Hdisj Hcs.
  pose proof HK as (Hkms & Hkr0 & Hkre & _).
  destruct Hkms as (Hpc & Hrv & Hsvc & Hrom & Hfrg & Hfcs).
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & _ & E20 & _ & _ & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  rewrite (kh_ms_shape ms3 (BASE + kpc KP_LOOP) Hpc Hrv Hsvc Hrom Hfrg Hfcs), restrict_mkst_fx.
  assert (HS0 : st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
            (mkSS (kpc KP_LOOP) sr_atoms rs None (mkFacts hd_atoms cs hd_alias))
            (mkst (ms_regs ms3) (w64 (BASE + kpc KP_LOOP)) (mrestrict (w_H W3) (ms_mem ms3))
               (seg_rom SEGS))).
  { apply pa_entry_st_ok_full.
    - unfold hd_E. apply regs_ok_Eimg_Ereg.
    - exact Hwf.
    - exact Hrok.
    - exact Hdisj.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias].
      split; [exact (dp_atoms_ok d s Hd Hs)|]. split; [exact Hcs | exact (dp_alias_ok d s)]. }
  assert (HD24 : sv_denot (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (hd_sh 18 8) =
            getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 24))).
  { rewrite (kn_reg_of ms3 _ 24%nat (kS8 cx) Hkre ltac:(dp_inl)),
            (kh_denot_sh _ 18%nat (ka0 cx) 8 E18 ltac:(lia) ltac:(lia) ltac:(lia) E20).
    unfold w64, kS8, shadow_of_addr. reflexivity. }
  exact (ast_ok_pi_set_reg_fp _ _ _ (Z_to_bv 5 (Z.of_nat 24)) (hd_sh 18 8) HS0 eq_refl HD24).
Qed.

(* ---- the three region lists are pairwise disjoint ---- *)
Lemma dp_disj0 : forall d s (fv : Z),
  pairwise_disjoint (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
    [hd_cur 0 (SOff 33 0); dp_slots; dp_w2f fv].
Proof.
  intros d s fv.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & E9 & _ & E21 & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof (dp_CA (ka0 cx) ltac:(lia)) as (_ & _ & CF0 & CW0).
  pose proof (dp_CA (ka0 cx + 15) ltac:(lia)) as (_ & _ & CF1 & CW1).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  apply pairwise_disjoint_of_extents.
  unfold hd_cur, dp_slots, dp_w2f, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  cbn [base_val]. rewrite E18, E9, E21. unfold w64.
  rewrite !unsigned_lit_small by (unfold NW_FULL, NW_SIZE in *; lia).
  unfold KS_K, KS_W2F, NW_FULL, NW_SIZE, kW2, KN_W2 in *. rewrite HKA in *.
  repeat split; lia.
Qed.

Lemma dp_disj1 : forall (d s : Z), adv < k_wn cx ->
  pairwise_disjoint (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
    [hd_cur 16 (SOff 33 0); dp_slots; dp_w2f 0; hd_in; hd_ish].
Proof.
  intros d s Hadv.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & E9 & _ & E21 & _ & E32 & _ & _ & E35 & _).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  pose proof (dp_CA (ka0 cx) ltac:(lia)) as (_ & _ & CF0 & CW0).
  pose proof (dp_CA (ka0 cx + 15) ltac:(lia)) as (_ & _ & CF1 & CW1).
  pose proof (dp_CI (k_wp cx + adv) ltac:(lia)) as (CP0 & CPB & CPF & CPW).
  pose proof (kn_F SK B LAWS cx fpos k2 ly3 S3 md3 HB dp_jbk) as (F1 & F2 & F3 & F4).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKA : KERNEL_AK = 4640) by reflexivity.
  assert (HQ : SHADOW_OFF <= SHADOW_OFF + (k_wp cx + adv) / 8 < SHADOW_OFF + 2 ^ 44).
  { split; [pose proof (Z.div_pos (k_wp cx + adv) 8 ltac:(lia) ltac:(lia)); lia
           | pose proof (Z.div_lt_upper_bound (k_wp cx + adv) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]. }
  apply pairwise_disjoint_of_extents.
  unfold hd_cur, dp_slots, dp_w2f, hd_in, hd_ish, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  cbn [base_val]. rewrite E18, E9, E21, E32, E35. unfold w64.
  rewrite !unsigned_lit_small by (unfold NW_FULL, NW_SIZE, SHADOW_OFF in *; lia).
  unfold KS_K, KS_W2F, NW_FULL, NW_SIZE, kW2, KN_W2 in *. rewrite HKA in *.
  unfold kLowMemEnd, kHighMemBeg, kLowShadowBeg, SHADOW_OFF in *.
  repeat split;
    first [ lia | destruct G14 as [H | H]; lia | destruct G3 as [H | H]; lia
          | destruct F4 as [H | H]; lia | destruct CPB as [H | H]; lia ].
Qed.

(* ---- the conditions of each arm ---- *)
Lemma dp_cond_empty : k_wn cx - adv = 0 ->
  conds_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) 0 0) dp_c0.
Proof.
  intros Hn0.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) 0 0) as (_ & _ & _ & _ & _ & _ & E33 & _).
  unfold dp_c0. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
  split; [|exact I].
  rewrite (sv_off0 _ 33%nat _ E33). rewrite Hn0.
  unfold branch_taken, bv_eqb. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma dp_cond_byte : forall (fast : bool) d s, adv < k_wn cx -> 0 <= s < 8 ->
  saddr_ok (k_wp cx + adv) s -> (if fast then s = 0 else s <> 0) ->
  conds_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (dp_cs fast).
Proof.
  intros fast d s Hadv Hs Hsok Hf.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (_ & _ & _ & _ & _ & E32 & E33 & _ & _ & E36).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  assert (D33 : sv_denot (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (SOff 33 0) =
            Z_to_bv 64 (k_wn cx - adv)) by (apply sv_off0; exact E33).
  assert (D36 : sv_denot (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (SOff 36 0) = Z_to_bv 64 s)
    by (apply sv_off0; exact E36).
  assert (Dand : sv_denot (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s)
            (SAlu ALU_AND (SOff 32 0) (SLit 7)) = Z_to_bv 64 ((k_wp cx + adv) mod 8)).
  { rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
    rewrite (U_atom_off _ 32%nat (k_wp cx + adv) 0 E32 ltac:(lia) ltac:(lia)), Z.add_0_r.
    change (zcanon 7) with 7.
    replace (Z.land (k_wp cx + adv) 7) with ((k_wp cx + adv) mod 8)
      by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
    apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound (k_wp cx + adv) 8). lia. }
  assert (BEQ : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
            branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y))
    by (intros x y Hx Hy; unfold branch_taken, bv_eqb; rewrite !unsigned_lit_small by lia; reflexivity).
  assert (BNE : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
            branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 y) = negb (x =? y))
    by (intros x y Hx Hy; change BC_NE with (neg_bc BC_EQ); rewrite branch_taken_neg, BEQ by assumption;
        reflexivity).
  assert (D0 : sv_denot (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (SLit 0) = Z_to_bv 64 0)
    by reflexivity.
  pose proof (Z.mod_pos_bound (k_wp cx + adv) 8 ltac:(lia)) as Hm8.
  destruct fast; cbv iota in Hf; unfold dp_cs; cbn [conds_ok]; unfold acond_ok; cbn [ac_c ac_a ac_b];
    repeat match goal with |- _ /\ _ => split end; try exact I;
    rewrite ?D33, ?D36, ?D0, ?Dand;
    first [ rewrite BNE by lia; apply negb_true_iff, Z.eqb_neq; lia
          | rewrite BEQ by lia; apply Z.eqb_eq; lia
          | apply kh_blt; unfold saddr_ok in Hsok; lia ].
Qed.

(* ---- the two seats ---- *)
Lemma dp_seat0 : forall fv cs d s, f = fv -> 0 <= d < 256 -> 0 <= s < 8 ->
  conds_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) cs ->
  st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (dp_ss0 fv cs)
    (restrict (w_H W3) ms3).
Proof.
  intros fv cs d s Hfv Hd Hs Hcs. subst fv. unfold dp_ss0.
  apply (dp_seat_core d s [hd_cur 0 (SOff 33 0); dp_slots; dp_w2f f] cs Hd Hs
           ltac:(vm_compute; reflexivity)); [| apply dp_disj0 | exact Hcs].
  apply Forall_cons; [apply (dp_rcur d s 0); lia|].
  apply Forall_cons; [apply dp_rslots|].
  apply Forall_cons; [apply dp_rw2f | apply Forall_nil].
Qed.

Lemma dp_seat1 : forall cs d s (bb : byte), adv < k_wn cx -> f = 0 ->
  0 <= s < 8 -> d = bv_unsigned bb ->
  mbyte SEGS (rdW W3 (ms_mem ms3)) (k_wp cx + adv) = Some bb ->
  aview SEGS (w_H W3) (ms_mem ms3) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)) = Some s ->
  conds_ok (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) cs ->
  st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (dp_ss1 cs)
    (restrict (w_H W3) ms3).
Proof.
  intros cs d s bb Hadv Hf0 Hs Hd Hb Hsb Hcs.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (_ & _ & _ & _ & _ & E32 & _ & E34 & E35 & E36).
  pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (Hadv0 & _) & _).
  pose proof (bv_unsigned_in_range 8 bb) as Hbr. change (bv_modulus 8) with 256 in Hbr.
  assert (Hd8 : 0 <= d < 256) by lia.
  assert (BV32 : base_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (Some 32%nat) = k_wp cx + adv)
    by (cbn [base_val]; rewrite E32; unfold w64; apply unsigned_lit_small; lia).
  assert (HQ : SHADOW_OFF <= SHADOW_OFF + (k_wp cx + adv) / 8 < SHADOW_OFF + 2 ^ 44).
  { split; [pose proof (Z.div_pos (k_wp cx + adv) 8 ltac:(lia) ltac:(lia)); lia
           | pose proof (Z.div_lt_upper_bound (k_wp cx + adv) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia]. }
  assert (BV35 : base_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) (Some 35%nat) =
            SHADOW_OFF + (k_wp cx + adv) / 8)
    by (cbn [base_val]; rewrite E35; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
  (* the shadow byte, as a byte of memory *)
  unfold aview in Hsb.
  destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3)) (shadow_of_addr SHADOW_OFF (k_wp cx + adv)))
    as [bs|] eqn:Ebs; [|discriminate Hsb].
  cbn [option_map] in Hsb. injection Hsb as Hsb.
  pose proof (dp_rw2f d s) as Rw. rewrite Hf0 in Rw.
  unfold dp_ss1.
  apply (dp_seat_core d s [hd_cur 16 (SOff 33 0); dp_slots; dp_w2f 0; hd_in; hd_ish] cs Hd8 Hs
           ltac:(vm_compute; reflexivity)); [| apply dp_disj1; exact Hadv | exact Hcs].
  apply Forall_cons; [apply (dp_rcur d s 16); lia|].
  apply Forall_cons; [apply dp_rslots|].
  apply Forall_cons; [exact Rw|].
  apply Forall_cons.
  - unfold hd_in, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (k_wp cx + adv) 0 1 (SOff 34 0) d);
      [apply sv_off0; exact E34 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, Hd. exact (kh_val1 _ _ _ Hb).
  - apply Forall_cons; [|apply Forall_nil].
    unfold hd_ish, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    rewrite BV35. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS _ _ (SHADOW_OFF + (k_wp cx + adv) / 8) 0 1 (SOff 36 0) s);
      [apply sv_off0; exact E36 | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r, <- Hsb. exact (kh_val1 _ _ _ Ebs).
Qed.

(* the frame addresses of the run's layout are the call's *)
Lemma dp_fa : forall cid pos, frame_addr ly3 cid pos = frame_addr (k_lyc cx) cid pos.
Proof.
  intros cid pos. pose proof HB as ((HJ0 & _) & _).
  pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (_ & Hly0 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  pose proof HJ3 as (_ & _ & (memS3 & HJi3 & _) & _). pose proof HJi3 as (_ & Hly3 & _).
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
  unfold frame_addr. rewrite EF0, EF3. reflexivity.
Qed.

(* the cursor's bytes may be written: the call's ajw, moved to the current journal *)
Lemma dp_awr_cur : forall a, ka0 cx <= a < ka0 cx + 16 ->
  (awr_byte (k_STK cx) (k_sp0 cx) (k_FP cx) (ablocks B (k_ly cx) (k_S cx)) (ablocks B ly3 S3) ly3
     ((KN_CID, fpos) :: k_own cx) a /\ ~ (k_sp0 cx <= a < k_sp0 cx + k_XO cx)) \/
  inG (k_G cx) a \/ (inFP (k_OUT cx) a /\ k_sp0 cx <= a < k_sp0 cx + k_XO cx).
Proof.
  intros a Ha.
  pose proof HB as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hajw & _) & _).
  pose proof HK as (_ & _ & _ & _ & _ & _ & _ & (_ & _ & Hperm & _) & _).
  assert (HE : inFP (kernel_awr (k_regs cx) (km0 cx)) a).
  { exists (aarg (k_regs cx) 0, aarg (k_regs cx) 0 + 16).
    split; [unfold kernel_awr; dp_inl |]. cbn [fst snd]. unfold ka0 in Ha. lia. }
  destruct (Hajw a HE) as [[Haw Hnout] | [HGa | Hout]];
    [left; split; [|exact Hnout] | right; left; exact HGa | right; right; exact Hout].
  destruct Haw as [Hw | [(Hfp & b0 & n0 & Hbn & Hr) | [(b0 & n0 & Hbn & Hnb & Hr) | (cid & pos & Hown & Hr)]]].
  - left. exact Hw.
  - right; left. split; [exact Hfp|]. exists b0, n0. split; [|exact Hr].
    exact (Permutation_in _ (Permutation_sym Hperm) Hbn).
  - right; right; left. exists b0, n0. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hbn)|].
    split; [exact Hnb | exact Hr].
  - right; right; right. exists cid, pos. split; [right; exact Hown|]. rewrite dp_fa. exact Hr.
Qed.

(* ---- the slot lists of the two exits ---- *)
Lemma dp_incl_qmsg : forall ov, In ov (kslots_setup cx fpos c ++ [(KS_CI, ci)]) -> In ov (dp_sl0 ++ []).
Proof.
  intros ov H. rewrite app_nil_r. unfold dp_sl0.
  apply in_app_or in H as [H | H]; apply in_or_app; [left; exact H | right; cbn [In] in H |- *; tauto].
Qed.

Lemma dp_incl_kind : forall ov,
  In ov (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)]) ->
  In ov (dp_sl0 ++ [(KS_K, k)]).
Proof.
  intros ov H. unfold dp_sl0. rewrite <- app_assoc.
  apply in_app_or in H as [H | H]; apply in_or_app;
    [left; exact H | right; cbn [app In] in H |- *; tauto].
Qed.

Ltac dp_awr_arm BV18 BV9 :=
  cbv [dp_ss0 dp_ss1]; cbn [ss_mem];
  repeat (apply awr_ok_x_cons;
    [ let x := fresh "x" in let Hx := fresh "Hx" in
      intros x Hx; cbv [hd_cur dp_slots dp_w2f hd_in hd_ish] in Hx;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx;
      first [ lia
            | rewrite BV9 in Hx; left;
              split; [left; unfold KS_K in *; lia | unfold KS_K in *; lia]
            | rewrite BV18 in Hx; apply dp_awr_cur; lia ]
    | ]);
  apply awr_ok_x_nil.

(* THE PHASE: the three arms *)
Lemma dp_go : forall (Q : world SEGS -> config -> Prop),
  (forall (ms' : machine_state) (md' : Model),
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
       (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
        aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
     kat B cx fpos KP_QMSG [(21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N)]
       (kslots_setup cx fpos c ++ [(KS_CI, ci)]) (kfsh 0xf8 0 0xf3) true adv (Some j) k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (forall (ms' : machine_state) (md' : Model) (kd adv' : Z),
     ajournal_gx SEGS B (k_G cx) (k_XO cx) (k_OUT cx) (k_STK cx) (k_sp0 cx) (k_FP cx) (k_ly cx) (k_S cx)
       (k_W0 cx) (k_mem0 cx) (k_md0 cx) ((KN_CID, fpos) :: k_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
        aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
     (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms') a) ->
     0 <= kd < 8 ->
     (kd = 0 \/ (1 <= adv' /\ kregs_eq ms' [(10%nat, k_wp cx + adv'); (11%nat, k_wp cx + adv' - 1);
                                            (12%nat, k_wn cx - adv' + 1); (13%nat, k_wn cx - adv')])) ->
     kat B cx fpos (kind_pc kd)
       [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx); (25%nat, kW2 cx fpos + NW_N);
        (22%nat, m); (16%nat, kd)]
       (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
       (kfsh 0xf8 0 0xf3) true adv' (Some j) k2 ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
intros Q CQ CK.
pose proof HB as ((HJ0 & HGok & _) & _).
pose proof HK as (Hkms & Hkr0 & Hkre & _ & _ & _ & Hksl & Hkjbk & Hkkept & Hkcur & _ & _).
pose proof HW as (_ & _ & _ & _ & _ & _ & Hfr).
pose proof Hkcur as (Hadv0 & HCP & HCN & HCW).
pose proof dp_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14).
pose proof (kn_sp1 SK B cx HB) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
assert (HKA : KERNEL_AK = 4640) by reflexivity.
assert (R14 : getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat 14)) = w64 k)
  by (exact (kn_reg_of ms3 _ 14%nat k Hkre ltac:(dp_inl))).
pose (RUNTO := paj_run_to_x SK B LAWS (k_G cx) HGok (k_XO cx) (k_OUT cx)).
assert (GO : forall (d s : Z) (cs : list acond) (ss : sstate),
          0 <= d < 256 -> 0 <= s < 8 ->
          st_ok_pi SEGS pa_val (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) ss (restrict (w_H W3) ms3) ->
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 18%nat = w64 (ka0 cx) /\
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 9%nat = w64 (ksp1 cx) /\
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 14%nat = w64 k /\
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 32%nat = w64 (k_wp cx + adv) /\
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 33%nat = w64 (k_wn cx - adv) /\
          ew (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) d s) 34%nat = w64 d).
{ intros d s cs ss Hd Hs HS.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) d s) as (E18 & E9 & _ & _ & _ & E32 & E33 & E34 & _).
  split; [exact E18|]. split; [exact E9|]. split; [|split; [exact E32|]; split; [exact E33 | exact E34]].
  unfold hd_E.
  rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 14%nat (Z_to_bv 5 (Z.of_nat 14)) ltac:(vm_compute; reflexivity)).
  exact R14. }
clear GO.
destruct (Z.eq_dec f 1) as [Hf1 | Hfn1].
- (* ARM A: w2 is full, the message loop is over *)
  remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) 0 0) as E eqn:HEdef.
  destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) 0 0) as (E18 & E9 & _ & _ & _ & E32 & E33 & _).
  rewrite <- HEdef in E18, E9, E32, E33.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
  assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx)
    by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
  assert (BV9u : bv_unsigned (ew E 9%nat) = ksp1 cx)
    by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by (cbn [base_val]; exact BV9u).
  assert (HS : st_ok_pi SEGS pa_val E (dp_ss0 1 []) (restrict (w_H W3) ms3))
    by (rewrite HEdef; apply (dp_seat0 1 [] 0 0 Hf1 ltac:(lia) ltac:(lia) I)).
  assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3)))
    by (rewrite HEdef; apply dp_shok).
  pose proof HS as HS0. pose proof HJ3 as HJ.
  paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_QMSG).
  { dp_awr_arm BV18 BV9. }
  repeat rewrite wvb_collapse in HJ.
  match goal with
  | HFr0 : frame_of ?E0 ?rs0 (mrestrict _ ?m0) (mrestrict _ ?m1), HG0 : mem_grows _ _ |- _ =>
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a -> aview SEGS (w_H W3) m1 a = aview SEGS (w_H W3) m0 a)
      by (apply (kept_of_frame (segs := SEGS) E0 rs0 (w_H W3) m0 m1 dp_X HFr0);
          intros bb wlo whi x Hin Hx; vm_compute in Hin;
          repeat (destruct Hin as [Hin | Hin];
                  [injection Hin as <- <- <-; rewrite ?BV18, ?BV9 in Hx; unfold dp_X, KS_K in *;
                   cbn [base_val] in Hx; rewrite ?BV18u, ?BV9u in Hx; lia |]);
          destruct Hin);
    assert (HP : forall a, apresent (w_H W3) m0 a -> apresent (w_H W3) m1 a)
      by (intros a Hp; exact (kh_apres_grows (w_H W3) m0 m1 a HG0 Hp))
  end.
  lazymatch type of HS with
  | st_ok_pi _ _ _ ?ssF (restrict _ ?msF) =>
    spregion HS 0%nat HR0;
    apply (CQ msF _ HJ UN HP);
    apply (dp_land msF _ KP_QMSG _ adv [] (kslots_setup cx fpos c ++ [(KS_CI, ci)]));
    [ exact (dp_kms E W3 ssF msF KP_QMSG HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
    | pose proof (kh_reg_same E (dp_ss0 1 []) ssF (w_H W3) ms3 msF dp_keep0 HS0 HS
                    ltac:(vm_compute; reflexivity)) as RK;
      unfold kregs0 in Hkr0 |- *;
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))));
      rewrite RK by (vm_compute; reflexivity); tauto
    | pose proof (kh_reg_same E (dp_ss0 1 []) ssF (w_H W3) ms3 msF dp_keep0 HS0 HS
                    ltac:(vm_compute; reflexivity)) as RK;
      apply (dp_regs_move ms3 msF);
      [ intros r Hr; cbn [map In] in Hr;
        repeat (destruct Hr as [Hr | Hr]; [subst r; rewrite RK by (vm_compute; reflexivity); reflexivity |]);
        destruct Hr
      | apply (dp_regs_sub ms3 _ _ Hkre);
        let ov := fresh in let Hov := fresh in intros ov Hov; cbn [In] in Hov |- *; tauto ]
    | exact UN | exact HP
    | repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity
    | repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity
    | lia
    | pose proof (kh_curw cx W3 E msF _ _ _ _ _ 0 (SOff 32 0) (k_wp cx + adv) HR0 BV18u ltac:(dp_inl)
                    (sv_off0 _ 32%nat _ E32) ltac:(lia)) as VP;
      rewrite Z.add_0_r in VP; exact VP
    | exact (kh_curw cx W3 E msF _ _ _ _ _ 8 (SOff 33 0) (k_wn cx - adv) HR0 BV18u ltac:(dp_inl)
               (sv_off0 _ 33%nat _ E33) ltac:(lia))
    | unfold kslots_eq; apply Forall_nil
    | exact dp_incl_qmsg ]
  end.
- assert (Hf0 : f = 0) by lia.
  destruct (Z.eq_dec (k_wn cx - adv) 0) as [Hn0 | Hn1].
  + (* ARM B: the cursor is empty, so the kind is 0 *)
    remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) 0 0) as E eqn:HEdef.
    destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) 0 0) as (E18 & E9 & _ & _ & _ & E32 & E33 & _).
    rewrite <- HEdef in E18, E9, E32, E33.
    assert (E14 : ew E 14%nat = w64 k).
    { rewrite HEdef. unfold hd_E.
      rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 14%nat (Z_to_bv 5 (Z.of_nat 14))
                 ltac:(vm_compute; reflexivity)).
      exact R14. }
    assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
    assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx)
      by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
    assert (BV9u : bv_unsigned (ew E 9%nat) = ksp1 cx)
      by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
    assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by (cbn [base_val]; exact BV9u).
    assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by (cbn [base_val]; exact BV18u).
    assert (HS : st_ok_pi SEGS pa_val E (dp_ss0 0 dp_c0) (restrict (w_H W3) ms3))
      by (rewrite HEdef; apply (dp_seat0 0 dp_c0 0 0 Hf0 ltac:(lia) ltac:(lia) (dp_cond_empty Hn0))).
    assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3)))
      by (rewrite HEdef; apply dp_shok).
    pose proof HS as HS0. pose proof HJ3 as HJ.
    paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_K07).
    { dp_awr_arm BV18 BV9. }
    repeat rewrite wvb_collapse in HJ.
    lazymatch type of HS with
    | st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msA
    end.
    assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
              aview SEGS (w_H W3) (ms_mem msA) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { eapply (kept_of_frame (segs := SEGS) _ _ (w_H W3) (ms_mem ms3) (ms_mem msA) dp_X);
        [ eassumption |].
      intros bb2 wlo whi x Hin Hx. vm_compute in Hin.
      repeat (destruct Hin as [Hin | Hin];
              [injection Hin as <- <- <-; unfold dp_X, KS_K in *;
               cbn [base_val] in Hx; rewrite ?BV18u, ?BV9u in Hx; lia |]).
      destruct Hin. }
    assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msA) a).
    { intros a Hp. eapply (kh_apres_grows (w_H W3) (ms_mem ms3) (ms_mem msA) a);
        [eassumption | exact Hp]. }
    spregion HS 0%nat HR0. spregion HS 1%nat HR1.
    pose proof (kh_reg_same E (dp_ss0 0 dp_c0) _ (w_H W3) ms3 msA dp_keep0 HS0 HS
                  ltac:(vm_compute; reflexivity)) as RK.
    apply (CK msA _ 0 adv HJ UN HP ltac:(lia) ltac:(left; reflexivity)).
    apply (dp_land msA _ (kind_pc 0) _ adv [(KS_K, k)]
             (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])).
    * exact (dp_kms E W3 _ msA (kind_pc 0) HS ltac:(vm_compute; reflexivity)
               ltac:(vm_compute; reflexivity)).
    * unfold kregs0 in Hkr0 |- *.
      refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
      all: rewrite RK by (vm_compute; reflexivity); tauto.
    * unfold kregs_eq.
      apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
        [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]; cbn [fst snd].
      -- exact (dp_getOff E W3 msA _ (Z_to_bv 5 (Z.of_nat 19)) 18%nat 8 (ka0 cx) HS
                  ltac:(vm_compute; reflexivity) E18 ltac:(lia) ltac:(lia)).
      -- rewrite RK by (vm_compute; reflexivity).
         exact (kn_reg_of ms3 _ 21%nat (kW2 cx fpos) Hkre ltac:(dp_inl)).
      -- rewrite RK by (vm_compute; reflexivity).
         exact (kn_reg_of ms3 _ 24%nat (kS8 cx) Hkre ltac:(dp_inl)).
      -- rewrite RK by (vm_compute; reflexivity).
         exact (kn_reg_of ms3 _ 25%nat (kW2 cx fpos + NW_N) Hkre ltac:(dp_inl)).
      -- rewrite RK by (vm_compute; reflexivity).
         exact (kn_reg_of ms3 _ 22%nat m Hkre ltac:(dp_inl)).
      -- exact (dp_getLit E W3 msA _ (Z_to_bv 5 (Z.of_nat 16)) 0 HS
                  ltac:(vm_compute; reflexivity) ltac:(lia)).
    * exact UN.
    * exact HP.
    * repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
    * repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
    * lia.
    * pose proof (kh_curw cx W3 E msA _ _ _ _ _ 0 (SOff 32 0) (k_wp cx + adv) HR0 BV18u ltac:(dp_inl)
                    (sv_off0 _ 32%nat _ E32) ltac:(lia)) as VP.
      rewrite Z.add_0_r in VP. exact VP.
    * exact (kh_curw cx W3 E msA _ _ _ _ _ 8 (SOff 33 0) (k_wn cx - adv) HR0 BV18u ltac:(dp_inl)
               (sv_off0 _ 33%nat _ E33) ltac:(lia)).
    * unfold kslots_eq. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
      exact (kh_rd_of_region E (w_H W3) (ms_mem msA) 9%nat (ksp1 cx) _ _ _ _ _ KS_K (SOff 14 0) k
               HR1 BV9u ltac:(dp_inl) (sv_off0 _ 14%nat _ E14) ltac:(lia)).
    * exact dp_incl_kind.
  + (* ARM C: the kind byte at the cursor *)
    assert (Hadv : adv < k_wn cx) by lia.
    destruct (dp_sb Hadv) as (s & Hsb & Hsok). destruct (dp_db Hadv) as (bb & Hbb).
    pose proof (bv_unsigned_in_range 8 bb) as Hbr. change (bv_modulus 8) with 256 in Hbr.
    assert (Hs8 : 0 <= s < 8).
    { unfold aview in Hsb.
      destruct (mbyte SEGS (mrestrict (w_H W3) (ms_mem ms3))
                  (shadow_of_addr SHADOW_OFF (k_wp cx + adv))) as [bs|] eqn:Ebs; [|discriminate Hsb].
      cbn [option_map] in Hsb. injection Hsb as Hsb.
      pose proof (bv_unsigned_in_range 8 bs) as Hbs2. change (bv_modulus 8) with 256 in Hbs2.
      unfold saddr_ok in Hsok. lia. }
    assert (GOCT : s = 0 -> SRr SEGS W3 (mkCfg ms3 md3) Q).
    { intros Hfast.
      remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned bb) s) as E eqn:HEdef.
      destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned bb) s)
        as (E18 & E9 & _ & _ & _ & E32 & E33 & E34 & _).
      rewrite <- HEdef in E18, E9, E32, E33, E34.
      assert (E14 : ew E 14%nat = w64 k).
      { rewrite HEdef. unfold hd_E.
        rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 14%nat (Z_to_bv 5 (Z.of_nat 14))
                   ltac:(vm_compute; reflexivity)).
        exact R14. }
      assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
      assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx)
        by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
      assert (BV9u : bv_unsigned (ew E 9%nat) = ksp1 cx)
        by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
      assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by (cbn [base_val]; exact BV9u).
      assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by (cbn [base_val]; exact BV18u).
      assert (HS : st_ok_pi SEGS pa_val E (dp_ss1 (dp_cs true)) (restrict (w_H W3) ms3)).
      { rewrite HEdef.
        apply (dp_seat1 (dp_cs true) (bv_unsigned bb) s bb Hadv Hf0 Hs8 eq_refl Hbb Hsb).
        exact (dp_cond_byte true (bv_unsigned bb) s Hadv Hs8 Hsok Hfast). }
      assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3)))
        by (rewrite HEdef; apply dp_shok).
      pose proof HS as HS0. pose proof HJ3 as HJ.
      paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_MID).
      { dp_awr_arm BV18 BV9. }
      repeat rewrite wvb_collapse in HJ.
      lazymatch type of HS with
      | st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msF
      end.
      assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
                aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
      { eapply (kept_of_frame (segs := SEGS) _ _ (w_H W3) (ms_mem ms3) (ms_mem msF) dp_X);
          [ eassumption |].
        intros bb2 wlo whi x Hin Hx. vm_compute in Hin.
        repeat (destruct Hin as [Hin | Hin];
                [injection Hin as <- <- <-; unfold dp_X, KS_K in *;
                 cbn [base_val] in Hx; rewrite ?BV18u, ?BV9u in Hx; lia |]).
        destruct Hin. }
      assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msF) a).
      { intros a Hp. eapply (kh_apres_grows (w_H W3) (ms_mem ms3) (ms_mem msF) a);
          [eassumption | exact Hp]. }
      spregion HS 0%nat HR0. spregion HS 1%nat HR1.
      pose proof (kh_reg_same E (dp_ss1 (dp_cs true)) _ (w_H W3) ms3 msF dp_keep0 HS0 HS
                    ltac:(vm_compute; reflexivity)) as RK.
        lazymatch goal with
        | |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdF |} _ =>
          assert (HMID : kat B cx fpos KP_MID
                    ((14%nat, bv_unsigned bb) ::
                     [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx);
                      (25%nat, kW2 cx fpos + NW_N); (22%nat, m);
                      (10%nat, k_wp cx + (adv + 1)); (11%nat, k_wp cx + (adv + 1) - 1);
                      (12%nat, k_wn cx - (adv + 1) + 1); (13%nat, k_wn cx - (adv + 1))])
                    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
                    (kfsh 0xf8 0 0xf3) true (adv + 1) (Some j) k2 ly3 S3 W3 msF mdF)
        end.
        { apply (dp_land msF _ KP_MID _ (adv + 1) [(KS_K, k)]
                   (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])).
          - exact (dp_kms E W3 _ msF KP_MID HS ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)).
          - unfold kregs0 in Hkr0 |- *.
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
            all: rewrite RK by (vm_compute; reflexivity); tauto.
          - unfold kregs_eq.
            apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
              [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
              [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]]]]];
              cbn [fst snd].
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 14)) 34%nat 0 (bv_unsigned bb) HS
                         ltac:(vm_compute; reflexivity) E34 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + exact (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 19)) 18%nat 8 (ka0 cx) HS
                       ltac:(vm_compute; reflexivity) E18 ltac:(lia) ltac:(lia)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 21%nat (kW2 cx fpos) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 24%nat (kS8 cx) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 25%nat (kW2 cx fpos + NW_N) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 22%nat m Hkre ltac:(dp_inl)).
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 10)) 32%nat 1 (k_wp cx + adv)
                         HS ltac:(vm_compute; reflexivity) E32 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 11)) 32%nat 0 (k_wp cx + adv)
                         HS ltac:(vm_compute; reflexivity) E32 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 12)) 33%nat 0 (k_wn cx - adv)
                         HS ltac:(vm_compute; reflexivity) E33 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 13)) 33%nat (-1) (k_wn cx - adv)
                         HS ltac:(vm_compute; reflexivity) E33 ltac:(lia) ltac:(lia)).
              f_equal. lia.
          - exact UN.
          - exact HP.
          - repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
          - repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
          - lia.
          - pose proof (kh_curw cx W3 E msF _ _ _ _ _ 0 (SOff 32 1) (k_wp cx + (adv + 1)) HR0 BV18u
                          ltac:(dp_inl) ltac:(cbn [sv_denot]; rewrite E32; unfold w64;
                             rewrite unsigned_lit_small by lia; f_equal; lia) ltac:(lia)) as VP.
            rewrite Z.add_0_r in VP. exact VP.
          - exact (kh_curw cx W3 E msF _ _ _ _ _ 8 (SOff 33 (-1)) (k_wn cx - (adv + 1)) HR0 BV18u
                     ltac:(dp_inl) ltac:(cbn [sv_denot]; rewrite E33; unfold w64;
                        rewrite unsigned_lit_small by lia; f_equal; lia) ltac:(lia)).
          - unfold kslots_eq. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
            exact (kh_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_K (SOff 14 0) k
                     HR1 BV9u ltac:(dp_inl) (sv_off0 _ 14%nat _ E14) ltac:(lia)).
          - exact dp_incl_kind. }
      apply (dp_tail Q cx fpos k2 ly3 S3 W3 msF _ _ _ _ _ _ _ (bv_unsigned bb) HB HJ HMID
               ltac:(lia) eq_refl eq_refl (kfsh_fits 0xf8 0 0xf3)).
      intros msG mdG HJG UNG HPG HKG.
      apply (CK msG mdG (bv_unsigned bb mod 8) (adv + 1) HJG
               ltac:(intros a Ha Hn; rewrite (UNG a Ha); exact (UN a Ha Hn))
               ltac:(intros a Hp; exact (HPG a (HP a Hp)))
               ltac:(apply Z.mod_pos_bound; lia)).
      + right. split; [lia|].
        apply (dp_regs_sub msG _ _ (proj1 (proj2 (proj2 HKG)))).
        let ov := fresh in let Hov := fresh in intros ov Hov; cbn [In] in Hov |- *; tauto.
      + apply (dp_kat_rl cx fpos (kind_pc (bv_unsigned bb mod 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ HKG).
        let ov := fresh in let Hov := fresh in intros ov Hov; cbn [In] in Hov |- *; tauto. }
    assert (GOCF : s <> 0 -> SRr SEGS W3 (mkCfg ms3 md3) Q).
    { intros Hfast.
      remember (hd_E ms3 (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned bb) s) as E eqn:HEdef.
      destruct (dp_Ef (k_wp cx + adv) (k_wn cx - adv) (bv_unsigned bb) s)
        as (E18 & E9 & _ & _ & _ & E32 & E33 & E34 & _).
      rewrite <- HEdef in E18, E9, E32, E33, E34.
      assert (E14 : ew E 14%nat = w64 k).
      { rewrite HEdef. unfold hd_E.
        rewrite (ew_Eimg_Ereg_nat (ms_regs ms3) _ 14%nat (Z_to_bv 5 (Z.of_nat 14))
                   ltac:(vm_compute; reflexivity)).
        exact R14. }
      assert (HEI : img_env pa_val A_LIM E) by (rewrite HEdef; unfold hd_E; apply Eimg_env).
      assert (BV18u : bv_unsigned (ew E 18%nat) = ka0 cx)
        by (rewrite E18; unfold w64; apply unsigned_lit_small; lia).
      assert (BV9u : bv_unsigned (ew E 9%nat) = ksp1 cx)
        by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
      assert (BV9 : base_val E (Some 9%nat) = ksp1 cx) by (cbn [base_val]; exact BV9u).
      assert (BV18 : base_val E (Some 18%nat) = ka0 cx) by (cbn [base_val]; exact BV18u).
      assert (HS : st_ok_pi SEGS pa_val E (dp_ss1 (dp_cs false)) (restrict (w_H W3) ms3)).
      { rewrite HEdef.
        apply (dp_seat1 (dp_cs false) (bv_unsigned bb) s bb Hadv Hf0 Hs8 eq_refl Hbb Hsb).
        exact (dp_cond_byte false (bv_unsigned bb) s Hadv Hs8 Hsok Hfast). }
      assert (SHOK : sh_ok SEGS hd_Bx hd_SH E (mrestrict (w_H W3) (ms_mem ms3)))
        by (rewrite HEdef; apply dp_shok).
      pose proof HS as HS0. pose proof HJ3 as HJ.
      paj_run_to_tok RUNTO HS HJ SHOK hd_span (kpc KP_MID).
      { dp_awr_arm BV18 BV9. }
      repeat rewrite wvb_collapse in HJ.
      lazymatch type of HS with
      | st_ok_pi _ _ _ _ (restrict _ ?mm) => rename mm into msF
      end.
      assert (UN : forall a, 0 <= a < 2 ^ 64 -> ~ dp_X a ->
                aview SEGS (w_H W3) (ms_mem msF) a = aview SEGS (w_H W3) (ms_mem ms3) a).
      { eapply (kept_of_frame (segs := SEGS) _ _ (w_H W3) (ms_mem ms3) (ms_mem msF) dp_X);
          [ eassumption |].
        intros bb2 wlo whi x Hin Hx. vm_compute in Hin.
        repeat (destruct Hin as [Hin | Hin];
                [injection Hin as <- <- <-; unfold dp_X, KS_K in *;
                 cbn [base_val] in Hx; rewrite ?BV18u, ?BV9u in Hx; lia |]).
        destruct Hin. }
      assert (HP : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem msF) a).
      { intros a Hp. eapply (kh_apres_grows (w_H W3) (ms_mem ms3) (ms_mem msF) a);
          [eassumption | exact Hp]. }
      spregion HS 0%nat HR0. spregion HS 1%nat HR1.
      pose proof (kh_reg_same E (dp_ss1 (dp_cs false)) _ (w_H W3) ms3 msF dp_keep0 HS0 HS
                    ltac:(vm_compute; reflexivity)) as RK.
        lazymatch goal with
        | |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdF |} _ =>
          assert (HMID : kat B cx fpos KP_MID
                    ((14%nat, bv_unsigned bb) ::
                     [(19%nat, ka0 cx + 8); (21%nat, kW2 cx fpos); (24%nat, kS8 cx);
                      (25%nat, kW2 cx fpos + NW_N); (22%nat, m);
                      (10%nat, k_wp cx + (adv + 1)); (11%nat, k_wp cx + (adv + 1) - 1);
                      (12%nat, k_wn cx - (adv + 1) + 1); (13%nat, k_wn cx - (adv + 1))])
                    (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])
                    (kfsh 0xf8 0 0xf3) true (adv + 1) (Some j) k2 ly3 S3 W3 msF mdF)
        end.
        { apply (dp_land msF _ KP_MID _ (adv + 1) [(KS_K, k)]
                   (kslots_setup cx fpos c ++ [(KS_ROOM, 4097); (KS_CI, ci); (KS_M, m); (KS_K, k)])).
          - exact (dp_kms E W3 _ msF KP_MID HS ltac:(vm_compute; reflexivity)
                     ltac:(vm_compute; reflexivity)).
          - unfold kregs0 in Hkr0 |- *.
            refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
            all: rewrite RK by (vm_compute; reflexivity); tauto.
          - unfold kregs_eq.
            apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
              [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons;
              [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]]]]]]]];
              cbn [fst snd].
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 14)) 34%nat 0 (bv_unsigned bb) HS
                         ltac:(vm_compute; reflexivity) E34 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + exact (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 19)) 18%nat 8 (ka0 cx) HS
                       ltac:(vm_compute; reflexivity) E18 ltac:(lia) ltac:(lia)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 21%nat (kW2 cx fpos) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 24%nat (kS8 cx) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 25%nat (kW2 cx fpos + NW_N) Hkre ltac:(dp_inl)).
            + rewrite RK by (vm_compute; reflexivity).
              exact (kn_reg_of ms3 _ 22%nat m Hkre ltac:(dp_inl)).
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 10)) 32%nat 1 (k_wp cx + adv)
                         HS ltac:(vm_compute; reflexivity) E32 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 11)) 32%nat 0 (k_wp cx + adv)
                         HS ltac:(vm_compute; reflexivity) E32 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 12)) 33%nat 0 (k_wn cx - adv)
                         HS ltac:(vm_compute; reflexivity) E33 ltac:(lia) ltac:(lia)).
              f_equal. lia.
            + rewrite (dp_getOff E W3 msF _ (Z_to_bv 5 (Z.of_nat 13)) 33%nat (-1) (k_wn cx - adv)
                         HS ltac:(vm_compute; reflexivity) E33 ltac:(lia) ltac:(lia)).
              f_equal. lia.
          - exact UN.
          - exact HP.
          - repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity.
          - repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity.
          - lia.
          - pose proof (kh_curw cx W3 E msF _ _ _ _ _ 0 (SOff 32 1) (k_wp cx + (adv + 1)) HR0 BV18u
                          ltac:(dp_inl) ltac:(cbn [sv_denot]; rewrite E32; unfold w64;
                             rewrite unsigned_lit_small by lia; f_equal; lia) ltac:(lia)) as VP.
            rewrite Z.add_0_r in VP. exact VP.
          - exact (kh_curw cx W3 E msF _ _ _ _ _ 8 (SOff 33 (-1)) (k_wn cx - (adv + 1)) HR0 BV18u
                     ltac:(dp_inl) ltac:(cbn [sv_denot]; rewrite E33; unfold w64;
                        rewrite unsigned_lit_small by lia; f_equal; lia) ltac:(lia)).
          - unfold kslots_eq. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
            exact (kh_rd_of_region E (w_H W3) (ms_mem msF) 9%nat (ksp1 cx) _ _ _ _ _ KS_K (SOff 14 0) k
                     HR1 BV9u ltac:(dp_inl) (sv_off0 _ 14%nat _ E14) ltac:(lia)).
          - exact dp_incl_kind. }
      apply (dp_tail Q cx fpos k2 ly3 S3 W3 msF _ _ _ _ _ _ _ (bv_unsigned bb) HB HJ HMID
               ltac:(lia) eq_refl eq_refl (kfsh_fits 0xf8 0 0xf3)).
      intros msG mdG HJG UNG HPG HKG.
      apply (CK msG mdG (bv_unsigned bb mod 8) (adv + 1) HJG
               ltac:(intros a Ha Hn; rewrite (UNG a Ha); exact (UN a Ha Hn))
               ltac:(intros a Hp; exact (HPG a (HP a Hp)))
               ltac:(apply Z.mod_pos_bound; lia)).
      + right. split; [lia|].
        apply (dp_regs_sub msG _ _ (proj1 (proj2 (proj2 HKG)))).
        let ov := fresh in let Hov := fresh in intros ov Hov; cbn [In] in Hov |- *; tauto.
      + apply (dp_kat_rl cx fpos (kind_pc (bv_unsigned bb mod 8)) _ _ _ _ _ _ _ _ _ _ _ _ _ HKG).
        let ov := fresh in let Hov := fresh in intros ov Hov; cbn [In] in Hov |- *; tauto. }
    destruct (Z.eq_dec s 0) as [Hs0 | Hs0]; [exact (GOCT Hs0) | exact (GOCF Hs0)].
Qed.

End h.

Theorem kn_disp : forall POST (Rc Rm : kcx -> Z -> Prop),
  (forall kd, 0 <= kd < 8 -> kfrom SK B POST (kin_kind B Rc Rm kd)) ->
  kfrom SK B POST (kin_qmsg B Rc) ->
  kfrom SK B POST (kin_loop B Rc Rm).
Proof.
  intros POST Rc Rm HKIND HQ cx fpos k2 ly3 S3 W3 ms3 md3 HB HJ Hfrm HI.
  destruct HI as (c & ci & j & m & k & n & f & adv & HRc & HRm & Hc & Hci & Hj & Hm & Hk & HWat & HK).
  apply (dp_go cx fpos k2 ly3 S3 W3 ms3 md3 c ci j m k n f adv (conj Hk Hm) HB HJ HWat HK (POST cx)).
  - intros ms' md' HJ' UN HP HK'.
    apply (HQ cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, n, f, adv.
    split; [exact HRc|]. split; [exact Hc|]. split; [exact Hci|]. split; [exact Hj|].
    split; [| exact HK'].
    apply (kw_frame (dp_X cx) W3 ms3 W3 ms' (kW2 cx fpos) n f);
      [ intros a Ha Hn; exact (UN a Ha Hn) | exact HP
      | intros a Ha; exact (dp_w2_miss cx fpos k2 ly3 S3 md3 a HB
          ltac:(pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _); exact HJB) Ha)
      | exact HWat ].
  - intros ms' md' kd adv' HJ' UN HP Hkd Hdisj HK'.
    apply (HKIND kd Hkd cx fpos k2 ly3 S3 W3 ms' md' HB HJ' Hfrm).
    exists c, ci, j, m, k, n, f, adv'.
    split; [exact HRc|]. split; [exact HRm|]. split; [exact Hc|]. split; [exact Hci|].
    split; [exact Hj|]. split; [exact Hm|]. split; [exact Hk|]. split; [exact Hkd|].
    split; [| split; [exact Hdisj | exact HK']].
    apply (kw_frame (dp_X cx) W3 ms3 W3 ms' (kW2 cx fpos) n f);
      [ intros a Ha Hn; exact (UN a Ha Hn) | exact HP
      | intros a Ha; exact (dp_w2_miss cx fpos k2 ly3 S3 md3 a HB
          ltac:(pose proof HK as (_ & _ & _ & _ & _ & _ & _ & HJB & _); exact HJB) Ha)
      | exact HWat ].
Qed.

End b.
End a.

Print Assumptions kn_disp.
