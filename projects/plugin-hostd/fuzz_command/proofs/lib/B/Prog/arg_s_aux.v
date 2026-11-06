(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the symbolic states, seeds and small lemmas of arg_s's ASan+UBSan walk
   (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan, entry 0x8a820), after lib/A/Prog/sup_pin_accept_s1.v and
   sup_pin_accept_s4.v (a working branch 3cc8391594b: the entry seed with the shadow-base GOT word and cell,
   the join seed rebuilt from concrete facts), at B's addresses.

   The code (capstone 5.0.7 over fuzz_command.asan-ubsan, .symtab LOCAL FUNC arg_s 0x8a820, 344 bytes, 86 instructions;
   offsets from the entry):
     +0x00 .. +0x20  the 64-byte frame: ra, s0 .. s6 at sp + 56 .. sp + 0
     +0x24 beqz a0 -> +0x114 (unimp)          UBSan: c = NULL                  (trap site 0x8a844)
     +0x28 mv s1,a0; +0x2c andi a0,a0,7
     +0x30 bnez a0 -> +0x114 (unimp)          UBSan: c mod 8 <> 0             (trap site 0x8a850)
     +0x34 mv s3,a1
     +0x38 auipc a0 / +0x3c ld a0 (PHi 119 / PLdHi (A_OBJ 0): the shadow-base GOT word 0xa5f50)
     +0x40 ld s5,0(a0) (the shadow base); +0x44 s0 := c + 4; +0x48, +0x4c s6 := (s0 >> 3) + s5
     +0x50 lb a0,0(s6); +0x54 bnez a0 -> +0x118: the load4 check of c->nargs (slow path +0x118 .. +0x120,
           report 0x8a948 `jal __asan_report_load4`)
     +0x58 lw a0,0(s0); +0x5c li a1,5; +0x60 blt a1,a0 -> +0xec (nargs >= 6: return)
     +0x64 bnez s3 -> +0x70; +0x68 auipc / +0x6c addi s3 (PHi 120 / PAddHi (A_OBJ 54): "(null)" 0x224c0)
     +0x70 mv a0,s3; +0x74 jal __interceptor_trampoline_strlen (0x4517c)
     +0x78 addi s4,a0,1; +0x7c mv a0,s4; +0x80 jal xmalloc (0x899b4)
     +0x84 mv s2,a0; +0x88 mv a1,s3; +0x8c mv a2,s4; +0x90 jal __asan_memcpy (0x5767c)
     +0x94 lb a0,0(s6); +0x98 bnez a0 -> +0x12c: the second load4 check (report 0x8a95c)
     +0x9c lw a1,0(s0); +0xa0 addiw a2,a1,1
     +0xa4 blt a2,a1 -> +0x114 (unimp)          UBSan: c->nargs++ overflows     (trap site 0x8a8c4)
     +0xa8 lb a0,0(s6); +0xac bnez a0 -> +0x140: the store4 check (report 0x8a970)
     +0xb0 s1 := c + 8; +0xb4, +0xb8 a0 := (a1 << 3) + s1; +0xbc sw a2,0(s0)
     +0xc0 beqz a0 -> +0x114 (unimp)            UBSan: c->args + m is NULL      (trap site 0x8a8e0)
     +0xc4 .. +0xd0 (a0 <u s1) xor (m < 0) xor 1
     +0xd4 beqz a1 -> +0x114 (unimp)            UBSan: c->args + m wraps        (trap site 0x8a8f4)
     +0xd8 .. +0xe0 lbu of the shadow byte of a0; +0xe4 bnez a1 -> +0x154: the store8 check (report 0x8a974)
     +0xe8 sd s2,0(a0); +0xec .. +0x10c the frame back, sp += 64; +0x110 ret
   No auipc forms a plain-word access through an A_HI base (the two auipc pairs load the GOT word through the
   object atom A_OBJ 0 and form "(null)" as the object atom A_OBJ 54), so the walk needs no cmd_val_his.

   The walk's symbolic states:
   - ss_E: the entry (atoms 0 .. 31 the registers, 32 the shadow base, 33 the slot's nargs field m); regions: the
     64-byte frame below the entry sp, the GOT word, the shadow-base cell, the slot's nargs field; shadow entry: the
     slot (atom 10 = c, 56 bytes).
   - ss_B0: the point both arms of `bnez s3` meet (+0x70), rebuilt from concrete facts (atom 32 the shadow base,
     33 the slot, 34 .. 41 the entry's ra, s0 .. s6, which the frame holds). The tail (+0x94) adds the slot's nargs
     field (as_slotA m) and args[m] (as_slotB m) to the state the calls leave. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecCells CmdRecRo CmdRecRest CmdRecImg RecBLemmas RecBridge CmdRecAns.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- the walk's points in the listing ---------- *)
Definition AS_FRAME : Z := 64.
Definition AS_B0 : Z := AF_arg_s + 0x70.   (* mv a0,s3 (0x8a890): both arms of `bnez s3` meet *)
Definition AS_RS : Z := AF_arg_s + 0x78.   (* after the call of the strlen wrapper (0x8a898) *)
Definition AS_RX : Z := AF_arg_s + 0x84.   (* after the call of xmalloc (0x8a8a4) *)
Definition AS_RM : Z := AF_arg_s + 0x94.   (* after the call of __asan_memcpy (0x8a8b4) *)

(* ---------- the entry state ---------- *)
Definition AS_C : nat := 10.
Definition AS_SB : nat := 32.
Definition AS_M : nat := 33.
(* the slot's nargs field c + 4 .. c + 8, read only in this segment *)
Definition as_slotE : YP09.region :=
YP09.mkRegion (Some AS_C) CALL_OFF_NARGS (CALL_OFF_NARGS + 4) CALL_OFF_NARGS CALL_OFF_NARGS
  [YP09.mkChunk CALL_OFF_NARGS (CVal 4 (SOff AS_M 0))].
Definition as_rsE : smem := [stack_region AS_FRAME; got_regionP; bcell_regionP AS_SB; as_slotE].
Definition as_factsE (mlo mhi : Z) : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (AS_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (AS_SB, mkAF SB SB 0);
         (AS_M, mkAF mlo mhi 0)] [] [].
Definition ss_E (mlo mhi : Z) : sstate := mkSS AF_arg_s sr_atoms as_rsE None (as_factsE mlo mhi).
Definition as_BxE : sv := SOff AS_SB 0.
Definition as_SHE : list shent := [mkSHE AS_C 0 CALL_SIZE].
Definition as_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition as_extraE (m : Z) : list word := [Z_to_bv 64 SB; Z_to_bv 64 m].

(* ---------- the state at B0 (+0x70) and after ---------- *)
Definition AB_SB : nat := 32.
Definition AB_C : nat := 33.
(* the registers the frame holds, at sp0 - 8 - 8 j: ra, s0, s1, s2, s3, s4, s5, s6 *)
Definition as_saved : list Z := [1; 8; 9; 18; 19; 20; 21; 22].
Definition as_extraB (regs : bvmap 5 word) (c : Z) : list word :=
map (Z_to_bv 64) [SB; c] ++ map (fun r => getr regs (Z_to_bv 5 r)) as_saved.
Definition as_BxB : sv := SOff AB_SB 0.
Definition as_shx (x : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) as_BxB.
(* the frame above the B0 sp (atom 2), read only from here on *)
Definition as_frameB : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 AS_FRAME 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0));
   YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0));
   YP09.mkChunk 8 (CVal 8 (SOff 40 0)); YP09.mkChunk 0 (CVal 8 (SOff 41 0))].
Definition as_factsB : facts :=
mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (AB_C, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3); (AB_SB, mkAF SB SB 0)] [] [].
Definition as_regsB : list sv := Eval vm_compute in
sr_set (sr_set (sr_set (sr_set sr_atoms 8 (SOff AB_C 4)) 9 (SOff AB_C 0)) 21 as_BxB) 22 (as_shx (SOff AB_C 4)).
Definition ss_B0 : sstate := mkSS AS_B0 as_regsB [as_frameB] None as_factsB.
(* the tail's regions over the slot: its nargs field (m arguments) and args[m] *)
Definition as_slotA (m : Z) : YP09.region :=
YP09.mkRegion (Some AB_C) CALL_OFF_NARGS (CALL_OFF_NARGS + 4) CALL_OFF_NARGS (CALL_OFF_NARGS + 4)
  [YP09.mkChunk CALL_OFF_NARGS (CVal 4 (SLit m))].
Definition as_slotB (m : Z) : YP09.region :=
YP09.mkRegion (Some AB_C) (CALL_OFF_ARGS + 8 * m) (CALL_OFF_ARGS + 8 * m + 8)
  (CALL_OFF_ARGS + 8 * m) (CALL_OFF_ARGS + 8 * m + 8) [].
Definition as_SHB : list shent := [mkSHE AB_C 0 CALL_SIZE].

(* ---------- the slot ---------- *)
(* the slot record() returned, in RecBridge.v rec_bridge_slot's form *)
Definition as_slot_ok (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.

Lemma as_slot_bounds : forall c, as_slot_ok c ->
A_G_REC + OFF_CALLS <= c <= A_REC_SPILL /\ c mod 8 = 0 /\
((A_G_REC + OFF_CALLS <= c /\ c + CALL_SIZE <= A_G_REC + REC_SIZE) \/ c = A_REC_SPILL).
Proof.
intros c [(i & Hi & ->) | ->]; unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE, REC_CALLS_MAX in *.
- split; [lia|]. split; [|left; lia].
  replace (6173376 + 16 + 56 * i) with ((771674 + 7 * i) * 8) by lia. apply Z_mod_mult.
- split; [lia|]. split; [reflexivity | right; reflexivity].
Qed.

Lemma as_slot_range : forall c, as_slot_ok c -> 0x5e32d0 <= c <= 0x5e3760 /\ c + 56 <= 0x5e3798.
Proof.
intros c Hc. destruct (as_slot_bounds c Hc) as (H1 & _ & [(H2 & H3) | ->]);
unfold A_G_REC, A_REC_SPILL, OFF_CALLS, REC_SIZE, CALL_SIZE in *; lia.
Qed.

(* every byte of the slot is a byte of g_rec or of record.spill, a program static *)
Lemma as_slot_PG : forall c a, as_slot_ok c -> c <= a < c + CALL_SIZE -> inFP cmd_PG a.
Proof.
intros c a Hc Ha. destruct (as_slot_bounds c Hc) as (_ & _ & [(H2 & H3) | ->]).
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]].
  unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]].
  unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

Lemma as_slot_static : forall c a, as_slot_ok c -> c <= a < c + CALL_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof.
intros c a Hc Ha. destruct (as_slot_bounds c Hc) as (_ & _ & [(H2 & H3) | ->]); unfold TFIB_PROG_STATIC.
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. unfold A_REC_SPILL, CALL_SIZE in *. lia.
Qed.

Lemma as_slot_rec : forall c a, as_slot_ok c -> c <= a < c + CALL_SIZE ->
A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE.
Proof.
intros c a Hc Ha. destruct (as_slot_bounds c Hc) as (_ & _ & [(H2 & H3) | ->]).
- left. unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- right. unfold A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
Qed.

(* the spill's 56 bytes pass the record's addressability check *)
Lemma as_spill_chk : cmd_addr_b A_REC_SPILL CALL_SIZE = true.
Proof. vm_compute. reflexivity. Qed.

(* the shadow of a byte below the image's end lies far above every byte of the image, the heap and the slot *)
Lemma as_shadow_above : forall x, 0 <= x < 2 ^ 47 -> 0x606000 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---------- the representation's readers (a working branch c79a9f2daf7, lib/B/Prog/sup_reset.v:64-195,
   srb_aval_keep .. srb_arep_at_ext, under this walk's names) ---------- *)

Lemma as_aval_keep : forall rd rd' a n v, aval_mem rd a n v ->
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H K k Hk. rewrite K by lia. exact (H k Hk). Qed.

Lemma as_bytes_keep : forall rd rd' a l, abytes_atR rd a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> rd' x = rd x) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H K i Hi. rewrite K by lia. exact (H i Hi). Qed.

Lemma as_str_keep : forall rd rd' p s, astr_atR rd p s ->
  (forall x, p <= x < p + Z.of_nat (length s) + 1 -> rd' x = rd x) -> astr_atR rd' p s.
Proof.
  intros rd rd' p s [H1 H2] K. split; [|exact H2].
  apply (as_bytes_keep rd); [exact H1|]. intros x Hx. apply K. rewrite length_app in Hx. cbn [length] in Hx. lia.
Qed.

Lemma as_call_keep : forall bl bl' rd rd' a c P, acall_at bl rd a c P ->
  (forall x, a <= x < a + CALL_SIZE -> rd' x = rd x) ->
  (forall pn, In pn P -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  acall_at bl' rd' a c P.
Proof.
  intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) KA KP.
  unfold acall_at, CALL_SIZE, CALL_OFF_FN, CALL_OFF_NARGS, CALL_OFF_ARGS in *.
  refine (conj H1 (conj H2 (conj H3 (conj _ (conj _ (conj H6 _)))))).
  - apply (as_aval_keep rd); [exact H4|]. intros x Hx. apply KA. lia.
  - apply (as_aval_keep rd); [exact H5|]. intros x Hx. apply KA. lia.
  - intros k s pn Es Ep. destruct (H7 k s pn Es Ep) as (G1 & G2 & G3 & G4 & G5).
    assert (Hk : (k < length (snd c))%nat) by (apply nth_error_Some; rewrite Es; discriminate).
    destruct (KP pn ltac:(eapply nth_error_In; exact Ep)) as [Kin Kx].
    refine (conj _ (conj G2 (conj Kin (conj G4 _)))).
    + apply (as_aval_keep rd); [exact G1|]. intros x Hx. apply KA. lia.
    + apply (as_str_keep rd); [exact G5|]. intros x Hx. apply Kx. lia.
Qed.

Lemma as_answer_keep : forall bl bl' rd rd' gr t q, aanswer_at bl rd gr t q ->
  (forall x, gr + OFF_ANSWER <= x < gr + OFF_ANSWER + 8 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  aanswer_at bl' rd' gr t q.
Proof.
  intros bl bl' rd rd' gr t q H KA KP.
  destruct t as [x|]; destruct q as [pn|]; cbn [aanswer_at] in H |- *; try contradiction.
  - destruct H as (N1 & N2 & N3 & N4 & N5 & N6).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj N2 (conj Kin (conj N4 (conj _ N6))))).
    + apply (as_aval_keep rd); [exact N1|]. intros y Hy. apply KA. lia.
    + apply (as_str_keep rd); [exact N5|]. intros y Hy. apply Kx. lia.
  - apply (as_aval_keep rd); [exact H|]. intros y Hy. apply KA. lia.
Qed.

Lemma as_reply_keep : forall bl bl' rd rd' gr y q, areply_at bl rd gr y q ->
  (forall x, gr + OFF_REPLY <= x < gr + OFF_REPLY + 16 -> rd' x = rd x) ->
  (forall pn, In pn (oblk q) -> In pn bl' /\ forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x) ->
  areply_at bl' rd' gr y q.
Proof.
  intros bl bl' rd rd' gr y q H KA KP.
  destruct y as [x|]; destruct q as [pn|]; cbn [areply_at] in H |- *; try contradiction;
    unfold OFF_REPLY, OFF_REPLY_SIZE in *.
  - destruct H as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
    destruct (KP pn ltac:(cbn; left; reflexivity)) as [Kin Kx].
    refine (conj _ (conj _ (conj P3 (conj P4 (conj Kin (conj P6 (conj _ P8))))))).
    + apply (as_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (as_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
    + apply (as_bytes_keep rd); [exact P7|]. intros z Hz. apply Kx. lia.
  - destruct H as [P1 P2]. split.
    + apply (as_aval_keep rd); [exact P1|]. intros z Hz. apply KA. lia.
    + apply (as_aval_keep rd); [exact P2|]. intros z Hz. apply KA. lia.
Qed.

Lemma as_scalars_keep : forall rd rd' gr R, ag1_scalars rd gr R ->
  (forall x, gr <= x < gr + 8 \/ gr + 920 <= x < gr + 924 \/ gr + 944 <= x < gr + 960 -> rd' x = rd x) ->
  ag1_scalars rd' gr R.
Proof.
  intros rd rd' gr R (X1 & X2 & X3 & X4 & X5 & X6) K.
  unfold ag1_scalars, OFF_REFUSE, OFF_CODE, OFF_NREPLIES, OFF_STATE, OFF_HOST in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ X6))))).
  all: apply (as_aval_keep rd); [eassumption|]; intros z Hz; apply K; lia.
Qed.

Lemma as_in_calls : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
  intros Q i P pn E H. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
  split; [eapply nth_error_In; exact E | exact H].
Qed.

Lemma as_in_spill : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.

Lemma as_in_reply : forall Q pn, In pn (oblk (l_reply Q)) -> In pn (lay_blocks Q).
Proof.
  intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right. exact H.
Qed.

(* arep_at reads the reader only at g_rec, record.spill and the bytes of the recorder's own blocks, and the block
   list only at those blocks *)
Lemma as_arep_at_ext : forall bl bl' rd rd' gr sc R Q,
  arep_at bl rd gr sc R Q ->
  (forall pn, In pn (lay_blocks Q) -> In pn bl') ->
  (forall a, (gr <= a < gr + REC_SIZE) \/ (sc <= a < sc + SC_SIZE) \/
             (exists pn, In pn (lay_blocks Q) /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  arep_at bl' rd' gr sc R Q.
Proof.
  intros bl bl' rd rd' gr sc R Q (G1 & G2 & G3 & (C1 & C2 & C3 & C4 & C5 & C6) & HA & HP & HX & HW) KL K.
  assert (KQ : forall pn, In pn (lay_blocks Q) -> In pn bl' /\
             forall x, fst pn <= x < fst pn + snd pn -> rd' x = rd x).
  { intros pn Hpn. split; [exact (KL pn Hpn)|]. intros x Hx. apply K. right. right. exists pn.
    split; [exact Hpn | exact Hx]. }
  assert (KR : forall x, gr <= x < gr + REC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; left; exact Hx).
  assert (KS : forall x, sc <= x < sc + SC_SIZE -> rd' x = rd x) by (intros x Hx; apply K; right; left; exact Hx).
  unfold REC_SIZE, SC_SIZE in KR, KS.
  refine (conj G1 (conj G2 (conj G3 (conj _ (conj _ (conj _ (conj _ HW))))))).
  - refine (conj C1 (conj C2 (conj _ (conj _ (conj _ C6))))).
    + apply (as_aval_keep rd); [exact C3|]. intros x Hx. apply KR. unfold OFF_NCALLS in Hx. lia.
    + intros i c P Ec EP. destruct (C4 i c P Ec EP) as [Hc HL]. split; [|exact HL].
      assert (Hi : (i < length (r_calls R))%nat) by (apply nth_error_Some; rewrite Ec; discriminate).
      apply (as_call_keep bl _ rd); [exact Hc | |].
      * intros x Hx. apply KR. unfold OFF_CALLS, CALL_SIZE in *. lia.
      * intros pn Hpn. apply KQ. exact (as_in_calls Q i P pn EP Hpn).
    + apply (as_call_keep bl _ rd); [exact C5 | |].
      * intros x Hx. apply KS. unfold CALL_SIZE in Hx. lia.
      * intros pn Hpn. apply KQ. apply as_in_spill. exact Hpn.
  - apply (as_answer_keep bl _ rd); [exact HA | |].
    + intros x Hx. apply KR. unfold OFF_ANSWER in Hx. lia.
    + intros pn Hpn. apply KQ. apply rca_in_answer. exact Hpn.
  - apply (as_reply_keep bl _ rd); [exact HP | |].
    + intros x Hx. apply KR. unfold OFF_REPLY in Hx. lia.
    + intros pn Hpn. apply KQ. apply as_in_reply. exact Hpn.
  - apply (as_scalars_keep rd); [exact HX|]. intros x Hx. apply KR. lia.
Qed.

(* the recorder at a later reader that agrees on g_rec, record.spill and the recorder's blocks, which stay live *)
Lemma as_rep_keep : forall B ly S ly' S' rd rd' R O, rec_repA B ly S rd R O ->
  (forall pn, In pn O -> In pn (ablocks B ly' S')) ->
  (forall a, (A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
             (exists pn, In pn O /\ fst pn <= a < fst pn + snd pn) -> rd' a = rd a) ->
  rec_repA B ly' S' rd' R O.
Proof.
  intros B ly S ly' S' rd rd' R O (Q & HA & HO) KL K. exists Q. split; [|exact HO].
  apply (as_arep_at_ext _ _ rd rd' _ _ R Q HA).
  - intros pn Hpn. apply KL. apply HO. exact Hpn.
  - intros a [Ha | [Ha | (pn & Hpn & Ha)]]; apply K; [left; exact Ha | right; left; exact Ha |].
    right; right. exists pn. split; [apply HO; exact Hpn | exact Ha].
Qed.

(* the recorder's blocks are live blocks *)
Lemma as_O_in : forall B ly S rd R O, rec_repA B ly S rd R O -> forall pn, In pn O -> In pn (ablocks B ly S).
Proof. intros B ly S rd R O (Q & HQ & HOQ) pn Hpn. exact (lay_blocks_in _ _ _ _ _ _ HQ pn (proj1 (HOQ pn) Hpn)). Qed.

(* the footprint of the statement when the slot has room (arg_s_c.v:119-122) *)
Definition as_FP (c m : Z) : list (Z * Z) :=
[(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)].

Lemma as_FP_slot : forall c m a, 0 <= m <= 5 -> inFP (as_FP c m) a -> c <= a < c + CALL_SIZE.
Proof.
intros c m a Hm (r & Hr & Ha). unfold as_FP in Hr.
destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha; unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition as_EE (regs : bvmap 5 word) (m : Z) : env := Eimg (Ereg regs (as_extraE m)).
Definition as_EB (regs1 regs : bvmap 5 word) (c : Z) : env := Eimg (Ereg regs1 (as_extraB regs c)).
(* the value each callee-saved register holds after the epilogue, over the B0 state's atoms: sp the B0 sp + 64,
   s0 .. s6 the frame's words (atoms 35 .. 41), gp, tp, s7 .. s11 their own atoms *)
Definition as_restore (r : Z) : sv :=
if r =? 2 then SOff 2 AS_FRAME else if r =? 8 then SOff 35 0 else if r =? 9 then SOff 36 0
else if (18 <=? r) && (r <=? 22) then SOff (Z.to_nat (r + 19)) 0 else SOff (Z.to_nat r) 0.

Lemma as_regs_restored : forall H E ss ms (regs : bvmap 5 word),
st_ok_pi SEGS VAL E ss (restrict H ms) ->
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (as_restore (bv_unsigned r))) CALLEE_SAVED = true ->
(forall r, acallee_saved r -> sv_denot E (as_restore r) = getr regs (Z_to_bv 5 r)) ->
aregs_preserved regs (ms_regs ms).
Proof.
intros H E ss ms regs HS Hcs Hden r Hr.
assert (Hin : In (Z_to_bv 5 r : bv 5) CALLEE_SAVED).
{ unfold acallee_saved in Hr. cbv [CALLEE_SAVED In].
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct Hc as [->|Hc]; [repeat (first [left; apply bv_eq; reflexivity | right])|]).
  subst. repeat (first [left; apply bv_eq; reflexivity | right]). }
pose proof (proj1 (forallb_forall _ _) Hcs _ Hin) as Hq. cbn beta in Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_pi_restrict_reg H E ss ms _ HS), Hq.
assert (Hr5 : bv_unsigned (Z_to_bv 5 r : bv 5) = r).
{ unfold acallee_saved in Hr. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
  apply Z.mod_small. lia. }
rewrite Hr5. exact (Hden r Hr).
Qed.
Section e.
Variable B : asyms.
#[local] Notation LAWS := (AR_laws_ok SEGS B).
Hypothesis VOBJS : cmd_val_objs.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : @cmd_img_facts SK SEGS B.
Hypothesis PRW : prog_rw SEGS B.

(* the slot's 56 bytes are addressable at every AR state *)
Lemma as_slot_addressable : forall ly S (W : world SEGS) mem md c, AR SEGS B ly S W mem md -> as_slot_ok c ->
range_addressable (rdW W mem) SHADOW_OFF c CALL_SIZE.
Proof.
intros ly S W mem md c HAR Hc. destruct (as_slot_bounds c Hc) as (_ & _ & [(H2 & H3) | ->]).
- intros x Hx. apply (cmd_cf_grec SEGS B LAWS HB ly S W mem md HAR). unfold A_G_REC, OFF_CALLS, REC_SIZE, CALL_SIZE in *. lia.
- exact (cmd_addressable_chk SEGS B LAWS HB ly S W mem md A_REC_SPILL CALL_SIZE HAR as_spill_chk).
Qed.

(* the slot's shadow entry, at any state over an environment that names the slot and the shadow base *)
Lemma as_shok : forall ly S (W : world SEGS) mem md E (nc nb : nat) c, AR SEGS B ly S W mem md -> as_slot_ok c ->
ew E nc = Z_to_bv 64 c -> ew E nb = Z_to_bv 64 SB ->
sh_ok SEGS (SOff nb 0) [mkSHE nc 0 CALL_SIZE] E (mrestrict (w_H W) mem).
Proof.
intros ly S W mem md E nc nb c HAR Hc Ec Eb. pose proof (as_slot_range c Hc) as Hr.
unfold sh_ok. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E (SOff nb 0) nc c CALL_SIZE c 0 CALL_SIZE).
- exact (as_slot_addressable ly S W mem md c HAR Hc).
- rewrite (U_atom E nb SB Eb) by (unfold SB; lia). reflexivity.
- apply (U_atom E nc c Ec). lia.
- lia.
- lia.
- intros x Hx. cbn [Z.min Z.max] in Hx. unfold CALL_SIZE, SHADOW_OFF in *. lia.
Qed.

(* a byte of the slot's nargs or args[m] field, in the footprint, is a byte the walk may write *)
Lemma as_awr_slot : forall c a STK sp0 FP bl0 blc fr0 ly own, as_slot_ok c -> c <= a < c + CALL_SIZE -> inFP FP a ->
awr_byte SEGS B STK sp0 FP bl0 blc fr0 ly own a.
Proof.
intros c a STK sp0 FP bl0 blc fr0 ly own Hc Ha Hf.
right; right; right; right. left. split; [exact Hf|].
split; [rewrite (ts_prog B HB); exact (as_slot_static c a Hc Ha)|].
exact (cif_prog_img _ _ IMG a (as_slot_PG c a Hc Ha)).
Qed.

(* every byte of the slot is writable *)
Lemma as_slot_writable : forall (m : word -> option byte) c a, as_slot_ok c -> c <= a < c + CALL_SIZE ->
writable_at SEGS m a.
Proof. intros m c a Hc Ha. exact (PROG_WRITABLE SEGS B LAWS HB PRW m a (as_slot_PG c a Hc Ha)). Qed.

(* ---------- the string arg_s copies ---------- *)

(* the string q arg_s hands to strlen and __asan_memcpy: the caller's s (in a live block, in the read-only image, or
   in an object of a live side-stack frame; arg_s_c.v:104-109) or the default "(null)" (RO_lit_224c0), with the
   word tail the strlen wrapper reads *)
Definition as_str_ok (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) (q : Z) (y : list byte)
  : Prop :=
q <> 0 /\ astr_atR (rdW W mem) q y /\ Z.of_nat (length y) + 1 <= LMAX + 1 /\
atail_vis SEGS W mem (q + Z.of_nat (length y)) /\
(in_blockA (ablocks B ly S) q (Z.of_nat (length y) + 1) \/
 ((forall i, 0 <= i < Z.of_nat (length y) + 1 -> in_roP SEGS CMD_RLO CMD_RHI (q + i) /\
     ~ Exists (in_zr (q + i)) (as_owned_static B) /\ ~ (as_errno B <= q + i < as_errno B + 4)) /\
  cmd_addr_b q (Z.of_nat (length y) + 1) = true /\ cmd_hull_b q (Z.of_nat (length y) + 1) = true) \/
 afobj SEGS B ly S W mem q (Z.of_nat (length y) + 1)).

Lemma as_str_bounds : forall ly S (W : world SEGS) mem md q y, AR SEGS B ly S W mem md -> as_str_ok ly S W mem q y ->
4096 <= q /\ q + Z.of_nat (length y) + 1 <= alloc_ceiling.
Proof.
intros ly S W mem md q y HAR (Hq0 & Hstr & Hn & Htl & Hk). pose proof asan_consts as (C1 & _).
destruct Hk as [(p & k & Hin & H1 & H2) | [(Hro & _ & _) | ((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hq8 & HRA)]].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hk).
  pose proof (crf_req_size_ge k). lia.
- pose proof (cmd_ro_low SEGS B LAWS HB IMG q ltac:(replace q with (q + 0) by lia; exact (proj1 (Hro 0 ltac:(lia))))).
  pose proof (cmd_ro_low SEGS B LAWS HB IMG (q + Z.of_nat (length y)) (proj1 (Hro (Z.of_nat (length y)) ltac:(lia)))).
  lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hb1 & Hb2 & _). lia.
Qed.

(* a range of the string is one a runtime entry may read *)
Lemma as_str_read : forall stk ly S (W : world SEGS) regs mem md q y, AR SEGS B ly S W mem md ->
as_str_ok ly S W mem q y -> alloc_ceiling <= spZ regs - stk ->
aread_ok SEGS stk W regs mem q (astr_len y + 1).
Proof.
intros stk ly S W regs mem md q y HAR Hs Hsp.
pose proof (as_str_bounds ly S W mem md q y HAR Hs) as [Hq1 Hq2]. pose proof asan_consts as (C1 & _).
destruct Hs as (Hq0 & Hstr & Hn & Htl & Hk). unfold aread_ok, astr_len.
split; [lia|]. split; [lia|]. split; [unfold LMAX in Hn; lia|].
split.
{ intros a Ha. split.
  - destruct Hstr as [HBy _]. replace a with (q + Z.of_nat (Z.to_nat (a - q))) by lia.
    rewrite (HBy (Z.to_nat (a - q)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
  - unfold ascratch_stk. lia. }
destruct Hk as [(p & k & Hin & H1 & H2) | [(Hro & Ha & Hh) | ((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hq8 & HRA)]].
- pose proof (crf_req_size_ge k).
  split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md p k q (Z.of_nat (length y) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
  split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md p k q (Z.of_nat (length y) + 1) HAR Hin ltac:(lia) ltac:(lia))|].
  intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md p k q (Z.of_nat (length y) + 1) HAR Hin ltac:(lia) ltac:(lia) Hn0).
- destruct (cmd_aread_ok_chk SEGS B LAWS HB ly S W mem md q (Z.of_nat (length y) + 1) HAR Ha Hh) as [HR HH].
  pose proof (cmd_ro_low SEGS B LAWS HB IMG (q + Z.of_nat (length y)) (proj1 (Hro (Z.of_nat (length y)) ltac:(lia)))).
  split; [apply amem_range_high; lia|]. split; [exact HR | intros _; exact HH].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hb1 & Hb2 & Happ).
  split; [exact (amem_range_sub_app _ _ q (Z.of_nat (length y) + 1) Happ Hb2 Hf1 Hf2 ltac:(lia))|].
  split; [exact HRA|].
  intros Hn0. exact (shadow_hull_vis_of_frame SEGS B LAWS ly S W mem md cid pos q _ HAR Hin Hf1 Hf2 Hn0).
Qed.

(* the shadow byte of a byte of a side-stack frame is one of the frame's shadow bytes *)
Lemma as_frame_shadow : forall fa fb x, fa mod 8 = 0 -> fb mod 8 = 0 -> fa <= x < fa + fb ->
shadow_addr fa <= shadow_addr x < shadow_addr fa + fb / 8.
Proof.
intros fa fb x Hal Hb8 Hx. split; [apply shadow_mono; lia|].
assert (Hlt : x / 8 < fa / 8 + fb / 8).
{ apply Z.div_lt_upper_bound; [lia|].
  pose proof (Z.div_mod fa 8 ltac:(lia)) as D1. pose proof (Z.div_mod fb 8 ltac:(lia)) as D2.
  rewrite Hal in D1. rewrite Hb8 in D2. lia. }
unfold shadow_addr. lia.
Qed.

(* the string's facts along a journal whose footprint is the slot's two fields: its bytes are a live block's,
   read-only image bytes or a live frame's, none of which the footprint names *)
Lemma as_str_journal : forall STK sp0 c m ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k q y,
AR SEGS B ly S W mem md -> as_slot_ok c -> 0 <= m <= 5 ->
ajournal SEGS B STK sp0 (as_FP c m) ly S W mem md own lyc Sc Wc memc mdc k ->
as_str_ok ly S W mem q y -> as_str_ok lyc Sc Wc memc q y.
Proof.
intros STK sp0 c m ly S W mem md own lyc Sc Wc memc mdc k q y HAR Hc Hm HJ Hs.
pose proof (as_str_bounds ly S W mem md q y HAR Hs) as [Hq1 Hq2]. pose proof asan_consts as (C1 & _).
pose proof HJ as (HARc & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
assert (HnI : forall a, ~ in_img SEGS a -> ~ inFP (as_FP c m) a).
{ intros a Hni Hf. apply Hni. exact (cif_prog_img _ _ IMG a (as_slot_PG c a Hc (as_FP_slot c m a Hm Hf))). }
destruct Hs as (Hq0 & Hstr & Hn & Htl & Hkind).
destruct Hkind as [(p & kk & Hin & H1 & H2) | [(Hro & Ha & Hh) | ((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hq8 & HRA)]].
- pose proof (crf_req_size_ge kk) as Hreq.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p kk HAR Hin) as (_ & H4096 & Hceil & _ & _ & _ & Hkk).
  pose proof (req_size_pos kk ltac:(lia)) as [Hr1 Hr2].
  assert (Hlive : In (p, kk) (ablocks B lyc Sc)).
  { destruct (in_dec recb_pair_dec (p, kk) (ablocks B lyc Sc)) as [H|H]; [exact H|]. exfalso.
    pose proof (Hgone p kk 0 Hin H ltac:(lia)) as Hf. rewrite Z.add_0_r in Hf.
    exact (HnI p (blk_img SEGS B LAWS ly S W mem md p kk p HAR Hin ltac:(lia)) Hf). }
  assert (K : forall i, 0 <= i < Z.of_nat (length y) + 1 -> rdW Wc memc (q + i) = rdW W mem (q + i)).
  { intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply (F2 p kk (q - p + i) Hin Hlive); [lia|].
    apply HnI. exact (blk_img SEGS B LAWS ly S W mem md p kk (p + (q - p + i)) HAR Hin ltac:(lia)). }
  split; [exact Hq0|]. split.
  { apply (as_str_keep (rdW W mem)); [exact Hstr|]. intros x Hx. replace x with (q + (x - q)) by lia. apply K. lia. }
  split; [exact Hn|]. split.
  { exact (cmd_heap_tail_vis SEGS B LAWS HB lyc Sc Wc memc mdc p kk (q + Z.of_nat (length y)) HARc Hlive ltac:(lia)). }
  left. exists p, kk. split; [exact Hlive | lia].
- assert (K : forall i, 0 <= i < Z.of_nat (length y) + 1 -> rdW Wc memc (q + i) = rdW W mem (q + i)).
  { intros i Hi. destruct (Hro i Hi) as (Hr & Ho & He).
    apply F3; [exact (proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG _ Hr)) | exact Ho | exact He |].
    apply fp_spares_below; [exact (cif_ro_below_ofl _ _ IMG _ Hr)|].
    intros Hf. exact (cif_prog_not_ro _ _ IMG _ (as_slot_PG c _ Hc (as_FP_slot c m _ Hm Hf)) Hr). }
  split; [exact Hq0|]. split.
  { apply (as_str_keep (rdW W mem)); [exact Hstr|]. intros x Hx. replace x with (q + (x - q)) by lia. apply K. lia. }
  split; [exact Hn|]. split.
  { destruct (Hro (Z.of_nat (length y)) ltac:(lia)) as (Hr & Ho & _).
    exact (cmd_atail_kept SEGS B LAWS HB IMG ly S W mem md lyc Sc Wc memc mdc 0 0 _ HAR HARc (or_intror (conj Hr Ho)) Htl). }
  right; left. split; [exact Hro | split; [exact Ha | exact Hh]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hb1 & Hb2 & Happ).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z.mod_mul. lia. }
  assert (EF : frame_addr lyc cid pos = frame_addr ly cid pos).
  { destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. }
  assert (Hinc : In (cid, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (K : forall i, 0 <= i < Z.of_nat (length y) + 1 -> rdW Wc memc (q + i) = rdW W mem (q + i)).
  { intros i Hi. apply (F4 cid pos (q + i) Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - apply HnI. exact (frm_img SEGS B LAWS ly S W mem md cid pos (q + i) HAR Hin ltac:(lia)). }
  assert (KS : forall x, q <= x < q + Z.of_nat (length y) + 1 ->
    rdW Wc memc (shadow_of_addr SHADOW_OFF x) = rdW W mem (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. pose proof (as_frame_shadow _ _ x Hal Hb8 ltac:(lia)) as Hsx.
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (F4 cid pos (shadow_addr x) Hin).
    - right. unfold in_zr. cbn [fst snd]. exact Hsx.
    - intros Hf. pose proof (as_FP_slot c m _ Hm Hf) as Hsl. pose proof (as_slot_range c Hc).
      unfold shadow_addr, SHADOW_OFF in Hsl. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). unfold CALL_SIZE in *. lia. }
  split; [exact Hq0|]. split.
  { apply (as_str_keep (rdW W mem)); [exact Hstr|]. intros x Hx. replace x with (q + (x - q)) by lia. apply K. lia. }
  assert (HSTRc : astr_atR (rdW Wc memc) q y).
  { apply (as_str_keep (rdW W mem)); [exact Hstr|]. intros x Hx. replace x with (q + (x - q)) by lia. apply K. lia. }
  assert (HOBJ : afobj SEGS B lyc Sc Wc memc q (Z.of_nat (length y) + 1)).
  { split; [exists cid, pos; rewrite EF; refine (conj Hinc (conj Hcid (conj Hal (conj Hf1 Hf2))))|].
    split; [exact Hq8|]. intros x Hx. destruct (HRA x Hx) as (sh & Hsh & Hok). exists sh. split; [|exact Hok].
    rewrite (KS x ltac:(lia)). exact Hsh. }
  split; [exact Hn|]. split; [exact (cmd_fobj_tail SEGS B LAWS HB lyc Sc Wc memc mdc q y HARc HOBJ HSTRc)|].
  right; right. exact HOBJ.
Qed.

(* ---------- the allocator's blocks: RecBLemmas.v's recb_ablocks_nodup_m, recb_heap_apart_m, and the cons-permutation
   forms recb_fresh_disj_perm_m / recb_awr_new_block_perm_m (a Theorem Labs lane fc8bcbd8b42) take xmalloc_c.v's post as it is ---------- *)

(* the block a callee handed out is apart from the string: a live block's string by the allocator's separation, an
   image string because the block's bytes are no image bytes, a side-stack frame's string by the separation of
   blocks and frames *)
Lemma as_str_apart : forall STK sp0 FP ly S (W : world SEGS) mem md own ly4 S4 (W4 : world SEGS) mem4 md4 k q y p n',
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly4 S4 W4 mem4 md4 k ->
Permutation (ablocks B ly4 S4) ((p, n') :: ablocks B ly S) ->
as_str_ok ly S W mem q y ->
p + n' <= q \/ q + Z.of_nat (length y) + 1 <= p.
Proof.
intros STK sp0 FP ly S W mem md own ly4 S4 W4 mem4 md4 k q y p n' HAR HJ HP Hs.
pose proof HJ as (HAR4 & Hly & _ & _ & _ & Hfrs & _).
assert (Hpin : In (p, n') (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym HP)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n' HAR4 Hpin) as (_ & Hp4096 & Hpc & _ & _ & _ & Hn').
pose proof (crf_req_size_ge n') as Hrq. pose proof (req_size_pos n' ltac:(lia)) as [Hr1 _].
destruct Hs as (Hq0 & Hstr & Hn & Htl & Hk).
destruct Hk as [(pb & kb & Hin & H1 & H2) | [(Hro & _ & _) | ((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hq8 & HRA)]].
- pose proof (crf_req_size_ge kb).
  pose proof (recb_fresh_disj_perm_m B ly4 S4 W4 mem4 md4 (ablocks B ly S) p n' pb kb HAR4 HP Hin) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. destruct D as [D | D]; lia.
- destruct (Z_le_gt_dec (p + n') q) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (q + Z.of_nat (length y) + 1) p) as [D'|D']; [right; exact D'|]. exfalso.
  destruct (Hro (Z.max p q - q) ltac:(lia)) as (Hr & _ & _).
  replace (q + (Z.max p q - q)) with (Z.max p q) in Hr by lia.
  apply (blk_img SEGS B LAWS ly4 S4 W4 mem4 md4 p n' (Z.max p q) HAR4 Hpin ltac:(lia)).
  exact (proj1 (cmd_ro_prog_apart SEGS B LAWS HB IMG _ Hr)).
- assert (Hin4 : In (cid, pos) (frames S4)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  assert (EF : frame_addr ly4 cid pos = frame_addr ly cid pos).
  { destruct Hly as (_ & _ & _ & _ & _ & EF & _). unfold frame_addr. rewrite EF. reflexivity. }
  pose proof (sep_block_frame SEGS B LAWS ly4 S4 W4 mem4 md4 p n' cid pos HAR4 Hpin Hin4) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite EF in D. lia.
Qed.

(* ---------- the seeds ---------- *)

Lemma as_seed_E : forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md c m mlo mhi STK,
AR SEGS B ly S W mem md ->
astk_ok STK ly (spZ regs) -> AS_FRAME <= STK ->
(forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 c -> as_slot_ok c ->
0 <= mlo -> mlo <= m <= mhi -> mhi < 2 ^ 31 ->
aval_mem (rdW W mem) (c + CALL_OFF_NARGS) 4 m ->
st_ok_pi SEGS VAL (as_EE regs m) (ss_E mlo mhi)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arg_s)) mem (seg_rom SEGS)))
/\ sh_ok SEGS as_BxE as_SHE (as_EE regs m) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md c m mlo mhi STK HAR Hstk HSTK Hpres H10 Hc Hm0 Hm Hm1 HNA.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (as_slot_range c Hc) as Hcr. pose proof (as_slot_bounds c Hc) as (_ & Hc8 & _).
destruct (al_const _ _ LAWS _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (cmd_cf_got B HB VOBJS), (cmd_cf_cell B HB VOBJS) in Kgot. rewrite (cmd_cf_cell B HB VOBJS) in Kcell.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hgot_r. pose proof (pa_obj_img 12%nat ltac:(lia)) as Hcell_r.
set (E := as_EE regs m).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : bv_unsigned (ew E 2) = spZ regs).
{ subst E. unfold as_EE. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (E10 : ew E 10 = Z_to_bv 64 c).
{ subst E. unfold as_EE. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl). exact H10. }
assert (E32 : ew E 32 = Z_to_bv 64 SB).
{ subst E. unfold as_EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
assert (E33 : ew E 33 = Z_to_bv 64 m).
{ subst E. unfold as_EE. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 1). }
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (exact (img_env_atomP E (A_OBJ 0) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (E253 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (exact (img_env_atomP E (A_OBJ 12) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia))).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Ugot : VAL (A_OBJ 0) = 0xa5f50) by (rewrite (VOBJS 0%nat ltac:(vm_compute; lia)); reflexivity).
assert (Ucell : VAL (A_OBJ 12) = 0xb0c38) by (rewrite (VOBJS 12%nat ltac:(vm_compute; lia)); reflexivity).
split.
2:{ subst E. unfold as_BxE, as_SHE.
    exact (as_shok ly S W mem md (as_EE regs m) AS_C AS_SB c HAR Hc E10 E32). }
unfold ss_E. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold as_EE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold as_rsE, stack_region, got_regionP, bcell_regionP, as_slotE, AS_C, AS_SB, AS_M.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite E2. unfold AS_FRAME. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres. unfold AS_FRAME in *. lia. }
    constructor.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E253, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); pose proof (pa_val_range (A_OBJ 12)); lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 (SOff 32 0) SB);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SB; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS _ _ _ _ Kcell).
  + rewrite (VB 10%nat c E10) by lia.
    split; [unfold CALL_OFF_NARGS; lia|]. split; [unfold CALL_OFF_NARGS; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ c CALL_OFF_NARGS 4 (SOff 33 0) m);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia |].
    exact (val_mem_of_aval SEGS (w_H W) mem (c + CALL_OFF_NARGS) 4%nat m HNA).
- apply pairwise_disjoint_of_extents.
  unfold as_rsE, stack_region, got_regionP, bcell_regionP, as_slotE, extent_of_region, AS_C, AS_SB, AS_M.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E253) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  rewrite (VB 10%nat c E10) by lia.
  cbn [base_val]. rewrite E2.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite Ugot, Ucell. unfold AS_FRAME, CALL_OFF_NARGS in *.
  repeat split; lia.
- split; [|split; exact I].
  cbn [as_factsE f_atoms atoms_ok]. unfold AS_C, AS_SB, AS_M, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E10, E32, E33, !unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, A_G_REC, A_REC_SPILL, OFF_CALLS.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.

(* the state at B0, rebuilt from concrete facts: the registers, the frame's eight words *)
Lemma as_seed_B0 : forall (W : world SEGS) mem (regs regs1 : bvmap 5 word) c sp0,
2 ^ 46 <= sp0 - AS_FRAME -> sp0 <= 2 ^ 47 -> sp0 mod 16 = 0 -> as_slot_ok c ->
spZ regs1 = sp0 - AS_FRAME ->
getr regs1 8 = w64 (c + CALL_OFF_NARGS) -> getr regs1 9 = w64 c -> getr regs1 21 = w64 SB ->
getr regs1 22 = w64 (SB + (c + CALL_OFF_NARGS) / 8) ->
(forall j r, nth_error as_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
st_ok_pi SEGS VAL (as_EB regs1 regs c) ss_B0
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AS_B0)) mem (seg_rom SEGS))).
Proof.
intros W mem regs regs1 c sp0 Hsp Hsp47 Hsp16 Hc Hsp1 R8 R9 R21 R22 HFR.
pose proof (as_slot_range c Hc) as Hcr. pose proof (as_slot_bounds c Hc) as (_ & Hc8 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := as_EB regs1 regs c).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold as_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (as_extraB regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold as_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0 - AS_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp1).
assert (UC : bv_unsigned (ew E 33) = c) by (rewrite EC; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite ESB; apply unsigned_lit_small; unfold SB; lia).
rewrite restrict_mkst_fx. unfold ss_B0. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [YP01.all_regs In] in Hr. clear HFR.
  repeat (destruct Hr as [<- | Hr];
    [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
        let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
      first [ unfold as_shx, as_BxB; rewrite (denot_shx E 33 32 4 c SB EC ESB) by (unfold SB; lia);
              rewrite R22; unfold CALL_OFF_NARGS; reflexivity
            | cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
              first [ apply getr_zero
                    | symmetry; apply EE; reflexivity
                    | rewrite ESB; exact R21
                    | rewrite EC; exact R9
                    | rewrite UC; rewrite R8; reflexivity ] ]
    | ]); try (destruct Hr; fail).
- vm_compute. reflexivity.
- unfold as_frameB. apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Usp. unfold AS_FRAME in *. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil;
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval compute in (n - 34)%nat in let r := eval compute in (nth j as_saved 0) in
    let jj := eval compute in (n - 32)%nat in
    apply (chunk_ok_val SEGS E _ (sp0 - 64) off 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 r))));
    [ cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
      change (ew E n) with (ew E (32 + jj)%nat); rewrite (EX jj ltac:(cbv; lia));
      cbn [as_extraB nth map app as_saved]; symmetry; apply Z_to_bv_bv_unsigned
    | let HR := fresh in pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HR;
      change (bv_modulus 64) with (2 ^ 64) in HR; exact HR
    | cbn; lia
    | replace (sp0 - 64 + off) with (sp0 - 8 - 8 * Z.of_nat j) by (cbn; lia); exact (HFR j r eq_refl) ] end.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [|split; exact I].
  cbn [as_factsB f_atoms atoms_ok]. unfold AB_C, AB_SB, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, UC, USB. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  assert (Hs16 : (sp0 - AS_FRAME) mod 16 = 0).
  { unfold AS_FRAME. replace (sp0 - 64) with (sp0 + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hsp16. }
  unfold AS_FRAME, SB, A_G_REC, A_REC_SPILL, OFF_CALLS in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | assumption].
Qed.

End e.
End f.
End d.
