(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a Theorem Labs lane of the walk of fuzz_pcap's entry function
   LLVMFuzzerTestOneInput on fuzz_pcap.asan-ubsan (libreac v1.9.0, pin sha256 9e66f771f22af67a..., 0x80818, listing
   offset AF_LLVMFuzzerTestOneInput = 0x90 of lib/B/Prog/PcapList.v): phase L5, the end of the walk (stage W of
   lib/B/Prog/PcapEntryDefs.v "The walks"), as cut lemmas in the pe_from form of lib/B/Prog/PcapEntryDefs.v at the
   waypoint invariants GI_* of lib/B/Prog/PcapEntryPhases.v.

   The stretches (pcs of the pin; capstone disassembly llvmf-au.dis (sha256 be945029c797; internal record)):
     K5  -> KW / KX  0x80e0c `mv s5,a0` (s5 := first), the abort test 0x80e18 `blt n,-1`, a0 := g_file_len
                     (0x80e1c), 0x80e20 `bne s10(=at),a0`: at <> |F| goes to 0x80fa8 (s3 := file <> 0, s7 := -9) and
                     on into PP_KW 0x80fb0; at = |F| sets want := 0 (0x80e24) and reaches PP_KX 0x80e28.
     KW  -> KWL / KX s6 := e + 16, want := -1 (0x80fb0, 0x80fb4); 0x80fb8 `bltu a0(=|F|),s6` leaves to PP_KX with
                     want = -1 when fewer than 16 bytes are left; else a0 := file + e (0x80fbc), the four UBSan guards
                     0x80fc0 `bltu a0,s2` (file + e <u file), 0x80fcc `beqz a1` ((file <> 0) = (file + e = 0)),
                     0x80fd0 `beqz s2` (file = NULL), 0x80fd4 `bltu s7(=-9),a0` (wrap(file + e + 8)), a1 :=
                     ps.swapped (0x80fd8 `lw a1,8(s4)`), a0 := file + e + 8, and the call of rd32 (0x80fe0) to its
                     return PP_KWL 0x80fe4.
     KWL -> KW / KX  0x80fe4 `beqz a0` (len = 0: an empty record, e := e + 16 at 0x81010); else len zero-extended
                     (0x80fe8, 0x80fec), 0x80ff4 `bgeu cap,len` (a record that fits: want := len, or -1 when it is cut,
                     0x8101c .. 0x8102c, to PP_KX); else 0x80ffc `beqz d` (cap = 0: want = -1, to PP_KX), 0x81008
                     `bltu |F|,e + 16 + len` (a cut record: want = -1, to PP_KX), else e := e + 16 + len (0x81010);
                     the back edge 0x81014 `bne s6,|F|` to PP_KW, else want := 0 (0x81018 `j` 0x80e24) and PP_KX.
     KX  -> K6       the harness's check 0x80e2c `bne n,want` to PP_abort, and pcap_source_close (0x80e34) to its
                     return PP_K6 0x80e38.
   The cut GI_KX (PP_KX = 0x6a0, 0x80e28: the join of the three ways out of the end-of-walk check, with want in s9) is
   local to this file. The end-of-walk loop (KW -> KWL -> KW) is closed here by induction on |F| - e: at PP_KW e is
   s10, at PP_KWL it is s6 - 16 (pe_measW, pe_measL).

   Rule 24 (task text of a Theorem Labs lane): a search of the proof index for LLVMFuzzerTestOneInput (index v5 built
   2026-10-28T21:58:24Z, rebuilt 23:22:17Z, recipes 566eb6ffa5d) rc=0; the 30 named files are all in other units, and no
   row names libreac/fuzz_pcap; the working-branch search found no Qed walk of it on any asan-ubsan image. CONFIRM (a Theorem Labs lane
   23:47Z): the released fuzz_pcap harness walks (lib/U/Prog/Slot/USegE.v etc.) are for the v1.8 UBSAN image (343
   instructions, 176-byte frame) against this pin's 530 instructions with a 256-byte frame and ASan instrumentation, so
   this is a new proof. The released end-loop lemma lib/U/Prog/Slot/USegW.v:61 ubs_W_loop (origin/ossv/recipes
   c8557374ad2e) is the template for the guard decisions (:98, :105-109). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81 PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PSourceMeter PFclose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases Rd32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalkDef PWalk.
(* The walk helpers whose single owner is a Theorem Labs lane's file (2026-10-29): ms_eta, pe_sp1_bounds, pb_HG, pb_ftr,
   pe_chain, and the entry-state pattern of ref_entry. They are imported, never copied. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryOpen.
(* The generic walk helpers, single home lib/B/Prog/PcapEntryKit.v (a Theorem Labs lane, 2026-10-29): bpaj_run_x /
   bpaj_run_to_x (the lib/B instances of W_journalG's run chain over ajournal_gx), mk / mk_mbyte and the keep
   lemmas, rd32_call; and the callee applications of lib/B/Prog/PcapEntryCalls.v (a Theorem Labs lane): close_call. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryKit PcapEntryCalls.
(* wvb_fds_fs: materialising the lazy VM backing keeps the descriptors and the file system. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lia must keep div / mod: lib/A/AE2f.v (cgif's text) turns the euclidean-division flag off globally (a Theorem Labs lane 00:36Z). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module PWD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalkDef.
Module PWK := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalk.

(* The local cut: 0x80e28, the join of the end-of-walk check (listing offset 0x6a0). *)
Definition PP_KX : Z := 0x6a0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).

(* The measure of the end-of-walk loop: |F| - e, with e = s10 at PP_KW and e = s6 - 16 at PP_KWL. *)
Definition pe_measW
  (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) (m : Z) :
  ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
    GI cx fp k acc ly3 S3 W3 ms3 md3 /\ p_nF cx - bv_unsigned (getr (ms_regs ms3) 26) <= m.
Definition pe_measL
  (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) (m : Z) :
  ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
    GI cx fp k acc ly3 S3 W3 ms3 md3 /\ p_nF cx + 16 - bv_unsigned (getr (ms_regs ms3) 22) <= m.

(* ==== the reader's model at the end of the walk ====
   The harness's loop (0x80fb0 .. 0x81030) decides `want` from the four bytes of the record header at e; these
   lemmas say what the reader's own model (lib/Prog/pcap_source_struct_next.v, lib/Prog/Slot/PWalkDef.v) answers
   for the same bytes, so the comparison 0x80e2c never aborts. They use no machine state. *)

(* The kind at a position with a whole header left, as the harness's three tests read it (0x80fe4 len = 0,
   0x80ff4 len <=u cap, 0x80ffc cap = 0, 0x81008 / 0x8101c e + 16 + len vs |F|). *)
Lemma pe5_kind : forall cx e, e + 16 <= p_nF cx ->
  p_kind cx e =
    (if PSN.incl (p_sw cx) (p_F cx) e =? 0 then PSN.KEmpty
     else if PSN.incl (p_sw cx) (p_F cx) e <=? p_cap cx
          then (if e + 16 + PSN.incl (p_sw cx) (p_F cx) e <=? p_nF cx then PSN.KFit else PSN.KCutFit)
          else if p_cap cx =? 0 then PSN.KBig0
          else if e + 16 + PSN.incl (p_sw cx) (p_F cx) e <=? p_nF cx then PSN.KBig else PSN.KCutBig).
Proof.
intros cx e He. unfold p_kind, PSN.kind.
change (PSN.flen (p_F cx)) with (p_nF cx).
destruct (Z.eqb_spec (p_nF cx - e) 0) as [H0|H0]; [lia|].
destruct (Z.ltb_spec (p_nF cx - e) 16) as [H1|H1]; [lia|]. reflexivity.
Qed.

(* The end of the file (0x80e20 / 0x81014 taken: e = |F|) and a header that does not fit (0x80fb8 taken). *)
Lemma pe5_kind_end : forall cx q, q = p_nF cx -> p_kind cx q = PSN.KEnd.
Proof.
intros cx q Hq. unfold p_kind, PSN.kind. change (PSN.flen (p_F cx)) with (p_nF cx).
destruct (Z.eqb_spec (p_nF cx - q) 0) as [H0|H0]; [reflexivity | lia].
Qed.

Lemma pe5_kind_cuth : forall cx q, q <> p_nF cx -> p_nF cx - q < 16 -> p_kind cx q = PSN.KCutH.
Proof.
intros cx q Hq Hlt. unfold p_kind, PSN.kind. change (PSN.flen (p_F cx)) with (p_nF cx).
destruct (Z.eqb_spec (p_nF cx - q) 0) as [H0|H0]; [lia|].
destruct (Z.ltb_spec (p_nF cx - q) 16) as [H1|H1]; [reflexivity | lia].
Qed.

(* A position whose kind is neither KEmpty nor KBig is where the reader's chain stops, so the walk's own e and the
   reader's answer position agree there (PWalk.skips_exit), and the answer is want_of (PWalk.kind_nfit). *)
Lemma pe5_stop : forall cx q Q, p_skips cx q Q ->
  p_kind cx q <> PSN.KEmpty -> p_kind cx q <> PSN.KBig -> Q = q.
Proof. intros cx q Q H H1 H2. exact (PWK.skips_exit (p_sw cx) (p_F cx) (p_cap cx) q Q H H1 H2). Qed.

Lemma pe5_res_of_kind : forall cx q, p_res cx q =
  match p_kind cx q with PSN.KEnd => 0 | PSN.KFit => PSN.rec_len (p_sw cx) (p_F cx) q | _ => -1 end.
Proof. intros cx q. reflexivity. Qed.

Lemma pe5_res_end : forall cx q, q = p_nF cx -> p_res cx q = 0.
Proof. intros cx q Hq. rewrite pe5_res_of_kind, (pe5_kind_end cx q Hq). reflexivity. Qed.

Lemma pe5_res_m1 : forall cx q,
  p_kind cx q = PSN.KCutH \/ p_kind cx q = PSN.KCutFit \/ p_kind cx q = PSN.KBig0 \/ p_kind cx q = PSN.KCutBig ->
  p_res cx q = -1.
Proof.
intros cx q H. rewrite pe5_res_of_kind.
destruct H as [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

(* The loop's two back edges: an empty record (0x81010 e := e + 16) and a skipped oversized one
   (0x81004 / 0x81010 e := e + 16 + len) keep the reader's chain from e. *)
Lemma pe5_step_empty : forall cx e Q, p_skips cx e Q -> p_kind cx e = PSN.KEmpty -> p_skips cx (e + 16) Q.
Proof. intros cx e Q H HK. exact (PWK.skips_empty_inv (p_sw cx) (p_F cx) (p_cap cx) e Q H HK). Qed.

Lemma pe5_step_big : forall cx e Q, p_skips cx e Q -> p_kind cx e = PSN.KBig ->
  p_skips cx (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) Q.
Proof. intros cx e Q H HK. exact (PWK.skips_big_inv (p_sw cx) (p_F cx) (p_cap cx) e Q H HK). Qed.

(* The reader's own answer position from p is reached by the chain (PWalk.psn_q_skips), and at a position whose
   kind stops the chain the position is its own answer. *)
Lemma pe5_q_self : forall cx q, 0 <= q ->
  p_kind cx q <> PSN.KEmpty -> p_kind cx q <> PSN.KBig -> p_q cx q = q.
Proof.
intros cx q Hq H1 H2.
exact (PWK.skips_exit (p_sw cx) (p_F cx) (p_cap cx) q (p_q cx q)
         (PWK.psn_q_skips (p_sw cx) (p_F cx) (p_cap cx) q Hq) H1 H2).
Qed.

(* 0 <= len < 2^32, so the harness's zero-extension of the 32-bit rd32 answer (0x80fe8, 0x80fec) is len itself, and
   its test against 0 (0x80fe4) is the model's `incl = 0`. *)
Lemma pe5_incl_range : forall cx e, 0 <= PSN.incl (p_sw cx) (p_F cx) e < 2 ^ 32.
Proof. intros cx e. unfold PSN.incl. apply PWK.pw_hw_range. Qed.

(* The capacity the harness keeps in PS_CAP is the model's cap, and it is small. *)
Lemma pe5_cap_range : forall cx, 0 <= p_cap cx <= 2040.
Proof. intros cx. pose proof (p_sizes cx) as (_ & H & _). exact H. Qed.

(* ---- the six exits of the end-of-walk check, each against the reader's answer ---- *)
(* Written with Q = p_q cx p, the reader's answer position from p, which GI_KW / GI_KWL reach from e by
   p_skips cx e Q. `want` is the value the loop leaves in s9. *)

(* 0x80fb8 taken (fewer than 16 bytes left, e < |F|): the header is cut, and the answer is -1. *)
Lemma pe5_exit_cuth : forall cx e Q, p_skips cx e Q -> e <> p_nF cx -> p_nF cx - e < 16 ->
  Q = e /\ p_res cx Q = -1.
Proof.
intros cx e Q Hsk Hne Hlt.
assert (HK : p_kind cx e = PSN.KCutH) by (apply pe5_kind_cuth; [exact Hne | exact Hlt]).
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
split; [exact HQ|]. rewrite HQ. apply pe5_res_m1. left. exact HK.
Qed.

(* 0x80e20 / 0x81014 not taken (e = |F|): the walk is at the end of the file, and the answer is 0. *)
Lemma pe5_exit_end : forall cx e Q, p_skips cx e Q -> e = p_nF cx -> Q = e /\ p_res cx Q = 0.
Proof.
intros cx e Q Hsk He.
assert (HK : p_kind cx e = PSN.KEnd) by (apply pe5_kind_end; exact He).
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
split; [exact HQ|]. rewrite HQ. apply pe5_res_end. exact He.
Qed.

(* 0x80fe4 taken (len = 0): an empty record; the loop goes on at e + 16. *)
Lemma pe5_exit_empty : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  PSN.incl (p_sw cx) (p_F cx) e = 0 -> p_skips cx (e + 16) Q.
Proof.
intros cx e Q Hsk He H0. apply (pe5_step_empty cx e Q Hsk).
rewrite (pe5_kind cx e He), H0. reflexivity.
Qed.

(* 0x80ff4 taken and 0x81024 (len <= cap, |F| < e + 16 + len): the record is cut, and the answer is -1. *)
Lemma pe5_exit_cutfit : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  PSN.incl (p_sw cx) (p_F cx) e <> 0 -> PSN.incl (p_sw cx) (p_F cx) e <= p_cap cx ->
  p_nF cx < e + 16 + PSN.incl (p_sw cx) (p_F cx) e ->
  Q = e /\ p_res cx Q = -1.
Proof.
intros cx e Q Hsk He Hne Hle Hcut.
assert (HK : p_kind cx e = PSN.KCutFit).
{ rewrite (pe5_kind cx e He).
  destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) e) 0) as [H|H]; [lia|].
  destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) e) (p_cap cx)) as [H1|H1]; [|lia].
  destruct (Z.leb_spec (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_nF cx)) as [H2|H2]; [lia | reflexivity]. }
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
split; [exact HQ|]. rewrite HQ. apply pe5_res_m1. right; left. exact HK.
Qed.

(* 0x80ff4 taken with the record whole (len <= cap, e + 16 + len <= |F|): the reader would stop here with a FIT
   record, which the cut's own fact p_kind cx Q <> KFit refutes. The arm is unreachable. *)
Lemma pe5_exit_fit_absurd : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  PSN.incl (p_sw cx) (p_F cx) e <> 0 -> PSN.incl (p_sw cx) (p_F cx) e <= p_cap cx ->
  e + 16 + PSN.incl (p_sw cx) (p_F cx) e <= p_nF cx ->
  p_kind cx Q <> PSN.KFit -> False.
Proof.
intros cx e Q Hsk He Hne Hle Hfit HnK.
assert (HK : p_kind cx e = PSN.KFit).
{ rewrite (pe5_kind cx e He).
  destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) e) 0) as [H|H]; [lia|].
  destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) e) (p_cap cx)) as [H1|H1]; [|lia].
  destruct (Z.leb_spec (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_nF cx)) as [H2|H2]; [reflexivity | lia]. }
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
apply HnK. rewrite HQ. exact HK.
Qed.

(* 0x80ffc taken (cap = 0, len > 0): the reader refuses every record, and the answer is -1. *)
Lemma pe5_exit_big0 : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  p_cap cx < PSN.incl (p_sw cx) (p_F cx) e -> p_cap cx = 0 ->
  Q = e /\ p_res cx Q = -1.
Proof.
intros cx e Q Hsk He Hgt Hcap0.
pose proof (pe5_incl_range cx e) as Hr.
assert (HK : p_kind cx e = PSN.KBig0).
{ rewrite (pe5_kind cx e He).
  destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) e) 0) as [H|H]; [lia|].
  destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) e) (p_cap cx)) as [H1|H1]; [lia|].
  destruct (Z.eqb_spec (p_cap cx) 0) as [H2|H2]; [reflexivity | lia]. }
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
split; [exact HQ|]. rewrite HQ. apply pe5_res_m1. right; right; left. exact HK.
Qed.

(* 0x81008 taken (cap > 0, len > cap, |F| < e + 16 + len): the oversized record is cut, and the answer is -1. *)
Lemma pe5_exit_cutbig : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  p_cap cx < PSN.incl (p_sw cx) (p_F cx) e -> p_cap cx <> 0 ->
  p_nF cx < e + 16 + PSN.incl (p_sw cx) (p_F cx) e ->
  Q = e /\ p_res cx Q = -1.
Proof.
intros cx e Q Hsk He Hgt Hcap Hcut.
assert (HK : p_kind cx e = PSN.KCutBig).
{ rewrite (pe5_kind cx e He).
  destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) e) 0) as [H|H]; [lia|].
  destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) e) (p_cap cx)) as [H1|H1]; [lia|].
  destruct (Z.eqb_spec (p_cap cx) 0) as [H2|H2]; [lia|].
  destruct (Z.leb_spec (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_nF cx)) as [H3|H3]; [lia | reflexivity]. }
assert (HQ : Q = e) by (apply (pe5_stop cx e Q Hsk); rewrite HK; discriminate).
split; [exact HQ|]. rewrite HQ. apply pe5_res_m1. right; right; right. exact HK.
Qed.

(* 0x81004 / 0x81010 (cap > 0, len > cap, e + 16 + len <= |F|): the record is skipped; the loop goes on. *)
Lemma pe5_exit_big : forall cx e Q, p_skips cx e Q -> e + 16 <= p_nF cx ->
  p_cap cx < PSN.incl (p_sw cx) (p_F cx) e -> p_cap cx <> 0 ->
  e + 16 + PSN.incl (p_sw cx) (p_F cx) e <= p_nF cx ->
  p_skips cx (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) Q.
Proof.
intros cx e Q Hsk He Hgt Hcap Hfit. pose proof (pe5_cap_range cx) as Hcr.
apply (pe5_step_big cx e Q Hsk).
rewrite (pe5_kind cx e He).
destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) e) 0) as [H|H]; [lia|].
destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) e) (p_cap cx)) as [H1|H1]; [lia|].
destruct (Z.eqb_spec (p_cap cx) 0) as [H2|H2]; [lia|].
destruct (Z.leb_spec (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_nF cx)) as [H3|H3]; [reflexivity | lia].
Qed.

(* The K5 join: when the record loop stopped at at = |F| the reader's answer from p is 0 (0x80e24 want := 0). *)
Lemma pe5_K5_end : forall cx p, 0 <= p -> p = p_nF cx -> p_q cx p = p /\ p_res cx (p_q cx p) = 0.
Proof.
intros cx p Hp He.
assert (HK : p_kind cx p = PSN.KEnd) by (apply pe5_kind_end; exact He).
assert (HQ : p_q cx p = p) by (apply pe5_q_self; [exact Hp | rewrite HK; discriminate | rewrite HK; discriminate]).
split; [exact HQ|]. rewrite HQ. apply pe5_res_end. exact He.
Qed.



Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.

(* PP_KX 0x80e28 (local): the end-of-walk check is over and want (s9) is the reader's answer from p, the answer n the
   record loop stored in PS_N; the walk's other facts are GI_KW's. *)
Definition GI_KX (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p : Z,
  p_cut B cx fp PP_KX PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= p_nF cx /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_first cx) /\ getr (ms_regs ms3) 25 = w64 (p_res cx (p_q cx p)) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader KS cx fp W3 ms3 b h buf p.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis FM : asrc_file_meter SK SEGS B MT.
(* pcap_source_close (0x80e34) is PROVED at this image (lib/B/Prog/PcapSourceClose.v pb_pcap_source_closeX); its walk
   takes the fclose wrapper's contract and the two trace facts of fclose's frees as Section hypotheses, so this file
   takes the same three. *)
Variable ra_fc1 ra_fc2 : Z.
Hypothesis AFCLOSE : afclose_source_spec SK SEGS B KS (pa_sigma PS___interceptor_trampoline_fclose) ra_fc1 ra_fc2
  pa_relro_lo pa_relro_hi.
Hypothesis HUfc1 : In [pc_free_ra0 (as_code B); ra_fc1] (as_universe B).
Hypothesis HUfc2 : In [pc_free_ra0 (as_code B); ra_fc2] (as_universe B).
(* The hi/lo pair of g_file_len the end-of-walk loop reads with raw `ld a1,0x498(s8)` words (0x81000, 0x8100c,
   0x8101c), which the listing keeps as PW: the engine resolves them at the atom A_HI 8, so the walk needs the
   listing's relocation equation to meet p_glob, which names the object. lib/B/Prog/PcapEntryEntry.v takes the same
   hypothesis (HHI8 there). pe_base now excludes musl's open-file-list head from pe_G itself
   (PcapEntryDefs.v, pe_G clause), so no hypothesis is needed for that. *)
Hypothesis HHI8 : pa_val (A_HI 8) + PE_GLEN_LO = pa_val (A_OBJ 4).

(* ---- the symbolic start states of this phase ---- *)
(* s8 holds the auipc value of g_file_len for the whole body (0x809a8 `auipc s8,0x553`, never spilled), so a start
   state of the phase pins it to the listing's atom A_HI 8: the PLdHi at 0x80e1c asks for exactly that (PaSym.is_hi),
   and the three raw `ld a1,0x498(s8)` words of the loop (0x81000, 0x8100c, 0x8101c) then resolve at that atom too. *)
Definition sr_hi8 : list sv := sr_set sr_atoms (24%bv : bv 5) (SOff (A_HI 8) 0).
(* No stretch of this phase reads shadow memory (no ASan check is instrumented between 0x80e0c and 0x80e38 or
   between 0x80fa8 and 0x81030), so the shadow-token machinery carries no entry. *)
Definition W5Bx : sv := SLit 0.
Definition W5span : Z * Z := (0, 0).

Lemma w5_sh_ok : forall (E : env) (m : word -> option byte), sh_ok SEGS W5Bx (@nil shent) E m.
Proof. intros E m. apply Forall_nil. Qed.

(* No region of this phase has a writable window, so the runs write nothing. *)
Ltac w5_awr :=
  let a := fresh "a" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros a (r & Hin & Hr); cbn [In] in Hin;
  repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hr; lia|]);
  destruct Hin.

(* The registers of a cut, as the engine's start list reads them: every register is its own atom but s8, which is
   the listing's A_HI 8. *)
Lemma w5_regs_ok : forall (ms3 : machine_state) (extra : list word),
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  regs_ok (Eimg (Ereg (ms_regs ms3) extra)) sr_hi8 (ms_regs ms3).
Proof.
intros ms3 extra R24. unfold sr_hi8.
apply (regs_ok_pin _ _ _ (24%bv : bv 5) (SOff (A_HI 8) 0)).
- apply regs_ok_Eimg_Ereg.
- intros HH. apply (f_equal bv_unsigned) in HH. vm_compute in HH. discriminate HH.
- rewrite R24. cbn [sv_denot].
  rewrite (Eimg_img (Ereg (ms_regs ms3) extra) (A_HI 8) ltac:(unfold A_HI, A_TEXT, A_LIM; lia)).
  rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia).
  rewrite Z.add_0_r. reflexivity.
Qed.


Variable POST : ecx -> world SEGS -> config -> Prop.
#[local] Abbreviation PF := (pe_from SK B MT KS POST).

(* ---- the cut lemmas, stated (each Definition X_stmt becomes Lemma X : X_stmt when proved) ---- *)

(* KX -> K6: the check n = want (0x80e2c) and pcap_source_close (0x80e34). *)
Definition pe_from_KX_stmt : Prop :=
  PF (GI_K6 B MT KS) -> PF GI_KX.

(* KWL -> KW (e grows by 16, or by 16 + len for a skipped record) / KX. *)
Definition pe_from_KWL_m_stmt : Prop :=
  forall m, PF (pe_measW (GI_KW B MT KS) (m - 16)) -> PF GI_KX -> PF (pe_measL (GI_KWL B MT KS) m).

(* KW -> KWL (the guards and the rd32 call of len) / KX (fewer than 16 bytes left). *)
Definition pe_from_KW_m_stmt : Prop :=
  forall m, PF (pe_measL (GI_KWL B MT KS) m) -> PF GI_KX -> PF (pe_measW (GI_KW B MT KS) m).

(* K5 -> KW (at <> |F|) / KX (at = |F|, want = 0). *)
Definition pe_from_K5_stmt : Prop :=
  PF (GI_KW B MT KS) -> PF GI_KX -> PF (GI_K5 B MT KS).

(* ---- the end-of-walk loop, closed ---- *)

Definition pe_from_endloop_stmt : Prop :=
  PF GI_KX -> PF (GI_KW B MT KS).

(* ---- the phase, composed: every cut of the stretch reaches PP_K6 ---- *)

Definition pe_from_KW_K6_stmt : Prop :=
  PF (GI_K6 B MT KS) -> PF (GI_KW B MT KS).

Definition pe_from_KWL_K6_stmt : Prop :=
  PF (GI_K6 B MT KS) -> PF (GI_KWL B MT KS).

Definition pe_from_K5_K6_stmt : Prop :=
  PF (GI_K6 B MT KS) -> PF (GI_K5 B MT KS).

(* A register of the engine's state, as its symbolic value (PcapPaLib.prreg without the env normalisation, so the
   atoms keep the names the start state's facts give them). *)
Ltac w5reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* The atoms of a start state's environment: a register atom is the register at the cut, an image atom its value. *)
Lemma w5_denot_reg : forall (regs : bvmap 5 word) (X : list word) (n : nat) (r : bv 5),
  (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  sv_denot (Eimg (Ereg regs X)) (SOff n 0) = getr regs r.
Proof.
intros regs X n r Hn Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr.
Qed.

Lemma w5_denot_img : forall (regs : bvmap 5 word) (X : list word) (a : nat),
  (A_TEXT <= a < A_LIM)%nat -> sv_denot (Eimg (Ereg regs X)) (SOff a 0) = Z_to_bv 64 (pa_val a).
Proof.
intros regs X a Ha. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply Eimg_img. exact Ha.
Qed.


(* s3 := (file <> 0) at 0x80fa8 (`sltu s3,zero,s2`), for a live block's address. *)
Lemma w5_snez : forall (regs : bvmap 5 word) (X : list word) b,
  getr regs 18 = w64 b -> 0 < b < 2 ^ 64 ->
  sv_denot (Eimg (Ereg regs X)) (SAlu ALU_SLTU (SLit 0) (SOff 18 0)) = w64 1.
Proof.
intros regs X b R18 Hb. rewrite denot_lit_U. unfold w64. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (U_atom (Eimg (Ereg regs X)) 18 b) by first
  [ rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs X 18 18%bv eq_refl); exact R18 | lia ].
change (zcanon 0) with 0. destruct (Z.ltb_spec 0 b) as [H|H]; [reflexivity | lia].
Qed.

(* A run whose regions have no writable window leaves memory as it found it. *)
Lemma w5_frame_eq : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> m' = m.
Proof.
intros E rs m m' HF Hw. apply functional_extensionality. intros x. apply HF.
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hw r Hin) as Hr2. apply Z.leb_le in Hr2. lia.
Qed.

(* A cut's common part (p_cut) at a later pc of the same stretch, when the run wrote no memory: only the pc, the
   kept registers of pregs and the model's VM backing changed. *)
Lemma w5_cut_move : forall cx fp pc pc' sh k kmax acc amax L ly3 S3 W3 (ms3 : machine_state)
  (regs1 : bvmap 5 word) md3 lz mat,
  p_cut B cx fp pc sh k kmax acc amax L ly3 S3 W3 ms3 md3 ->
  pregs cx (mkst regs1 (Z_to_bv 64 (BASE + pc')) (ms_mem ms3) (seg_rom SEGS)) ->
  p_cut B cx fp pc' sh k kmax acc amax L ly3 S3 W3 (mkst regs1 (Z_to_bv 64 (BASE + pc')) (ms_mem ms3) (seg_rom SEGS))
    (with_vm_backing lz mat md3).
Proof.
intros cx fp pc pc' sh k kmax acc amax L ly3 S3 W3 ms3 regs1 md3 lz mat (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) Hpr.
pose proof Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & _ & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
split; [| split; [exact Hk | split; [exact Hacc | split; [exact Hperm |
  split; [rewrite (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds
         | rewrite (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs]]]]].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [exact Hpr|].
split; [exact Hsaved|]. split; [exact Hhdr|]. split; [exact Hshd|]. split; [exact Hshlen | exact Hinp].
Qed.

(* pregs at the end of a run that did not touch sp, s0, s1, gp, tp. *)
Lemma w5_pregs_keep : forall cx (ms3 : machine_state) (regs1 : bvmap 5 word) pc m rom,
  pregs cx ms3 ->
  getr regs1 2 = getr (ms_regs ms3) 2 -> getr regs1 8 = getr (ms_regs ms3) 8 ->
  getr regs1 9 = getr (ms_regs ms3) 9 -> getr regs1 3 = getr (ms_regs ms3) 3 ->
  getr regs1 4 = getr (ms_regs ms3) 4 ->
  pregs cx (mkst regs1 pc m rom).
Proof.
intros cx ms3 regs1 pc m rom (Rsp & Rs0 & Rs1 & Rgp & Rtp) E2 E8 E9 E3 E4. unfold pregs. cbn [ms_regs mkst].
rewrite E2, E8, E9, E3, E4. repeat split; assumption.
Qed.

(* ---- the two finishers: GI_KX and GI_KW at the end of a run that wrote nothing ---- *)
Lemma w5_mk_KX : forall cx fp pc k acc ly3 S3 W3 (ms3 : machine_state) md3 (regs1 : bvmap 5 word) lz mat b h buf p,
  p_cut B cx fp pc PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 ->
  c_n cx < 2 ^ 26 -> p_good cx = true -> 24 <= p <= p_nF cx -> p_kind cx (p_q cx p) <> PSN.KFit ->
  pregs cx (mkst regs1 (Z_to_bv 64 (BASE + PP_KX)) (ms_mem ms3) (seg_rom SEGS)) ->
  getr regs1 18 = w64 b -> getr regs1 20 = w64 (pPS cx fp) -> getr regs1 21 = w64 (p_first cx) ->
  getr regs1 25 = w64 (p_res cx (p_q cx p)) ->
  pslots cx fp W3 ms3 -> pslot cx W3 ms3 PS_BUF buf -> pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) ->
  p_glob cx W3 ms3 b -> p_reader KS cx fp W3 ms3 b h buf p ->
  GI_KX cx fp k acc ly3 S3 W3 (mkst regs1 (Z_to_bv 64 (BASE + PP_KX)) (ms_mem ms3) (seg_rom SEGS))
    (with_vm_backing lz mat md3).
Proof.
intros cx fp pc k acc ly3 S3 W3 ms3 md3 regs1 lz mat b h buf p HC Hn26 Hgood Hp Hnfit Hpr R18 R20 R21 R25
  Hsl Hbuf HN Hglob Hrd.
exists b, h, buf, p. split; [eapply w5_cut_move; [exact HC | exact Hpr]|].
split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hp|]. split; [exact Hnfit|].
cbn [ms_regs mkst].
split; [exact R18|]. split; [exact R20|]. split; [exact R21|]. split; [exact R25|].
split; [exact Hsl|]. split; [exact Hbuf|]. split; [exact HN|]. split; [exact Hglob | exact Hrd].
Qed.

Lemma w5_mk_KW : forall m cx fp pc k acc ly3 S3 W3 (ms3 : machine_state) md3 (regs1 : bvmap 5 word) lz mat b h buf p e,
  p_cut B cx fp pc PSH_ts k 3 acc (PA_K3 MT cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 ->
  c_n cx < 2 ^ 26 -> p_good cx = true ->
  24 <= p <= e -> e <= p_nF cx -> e <> p_nF cx -> p_skips cx e (p_q cx p) -> p_kind cx (p_q cx p) <> PSN.KFit ->
  p_nF cx - e <= m ->
  pregs cx (mkst regs1 (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms3) (seg_rom SEGS)) ->
  getr regs1 10 = w64 (p_nF cx) -> getr regs1 18 = w64 b -> getr regs1 19 = w64 1 ->
  getr regs1 20 = w64 (pPS cx fp) -> getr regs1 21 = w64 (p_first cx) -> getr regs1 23 = w64 (-9) ->
  getr regs1 24 = w64 (pa_val (A_HI 8)) -> getr regs1 26 = w64 e ->
  pslots cx fp W3 ms3 -> pslot cx W3 ms3 PS_BUF buf -> pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) ->
  p_glob cx W3 ms3 b -> p_reader KS cx fp W3 ms3 b h buf p ->
  pe_measW (GI_KW B MT KS) m cx fp k acc ly3 S3 W3
    (mkst regs1 (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms3) (seg_rom SEGS)) (with_vm_backing lz mat md3).
Proof.
intros m cx fp pc k acc ly3 S3 W3 ms3 md3 regs1 lz mat b h buf p e HC Hn26 Hgood Hpe Hef Hne Hsk Hnfit Hm Hpr
  R10 R18 R19 R20 R21 R23 R24 R26 Hsl Hbuf HN Hglob Hrd.
pose proof (p_sizes cx) as (HnF & _ & _).
split.
- exists b, h, buf, p, e. split; [eapply w5_cut_move; [exact HC | exact Hpr]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hpe|]. split; [exact Hef|]. split; [exact Hne|].
  split; [exact Hsk|]. split; [exact Hnfit|].
  cbn [ms_regs mkst].
  split; [exact R10|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
  split; [exact R23|]. split; [exact R24|]. split; [exact R26|].
  split; [exact Hsl|]. split; [exact Hbuf|]. split; [exact HN|]. split; [exact Hglob | exact Hrd].
- cbn [ms_regs mkst]. rewrite R26. unfold w64. rewrite unsigned_lit_small by lia. exact Hm.
Qed.

(* ---- the arithmetic of the loop's tests on the rd32 answer ---- *)
(* rd32's answer for len is w64 (bv_swrap 32 len), 0 <= len < 2^32 (0x80fe4 `beqz a0`). *)
Lemma w5_swrap_eq0 : forall z, 0 <= z < 2 ^ 32 -> (bv_swrap 32 z mod 2 ^ 64 =? 0) = (z =? 0).
Proof.
intros z Hz. unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus.
change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ (Z.of_N 32 - 1)) with (2 ^ 31).
destruct (Z.eqb_spec z 0) as [H0|H0].
- subst z. reflexivity.
- apply Z.eqb_neq. lia.
Qed.

(* ... and its zero-extension (0x80fe8 `slli a0,a0,0x20`, 0x80fec `srli a0,a0,0x20`) is len. *)
Lemma w5_swrap32 : forall z, 0 <= z < 2 ^ 32 -> bv_swrap 32 z = if z <? 2 ^ 31 then z else z - 2 ^ 32.
Proof.
intros z Hz. unfold bv_swrap, bv_wrap.
assert (EM : bv_modulus 32 = 2 ^ 32) by reflexivity. assert (EH : bv_half_modulus 32 = 2 ^ 31) by reflexivity.
rewrite EM, EH.
destruct (Z.ltb_spec z (2 ^ 31)) as [H|H].
- rewrite Z.mod_small by lia. lia.
- replace ((z + 2 ^ 31) mod 2 ^ 32) with (z + 2 ^ 31 - 2 ^ 32) by (apply (Z.mod_unique _ _ 1); lia). lia.
Qed.

Lemma w5_zext32 : forall E v z, U E v = bv_swrap 32 z mod 2 ^ 64 -> 0 <= z < 2 ^ 32 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL v (SLit 32)) (SLit 32)) = z.
Proof.
intros E v z Hv Hz. rewrite !U_SAlu. cbn [zalu_raw]. rewrite !U_SLit, Hv.
change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (w5_swrap32 z Hz). unfold zcanon, M64.
destruct (Z.ltb_spec z (2 ^ 31)) as [H|H].
- rewrite (Z.mod_small z) by lia. rewrite (Z.mod_small (z * 2 ^ 32)) by lia.
  rewrite Z.div_mul by lia. rewrite Z.mod_small by lia. reflexivity.
- replace (z - 2 ^ 32) with ((z - 2 ^ 32 + 2 ^ 64) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (z - 2 ^ 32 + 2 ^ 64)) by lia.
  replace ((z - 2 ^ 32 + 2 ^ 64) * 2 ^ 32) with (z * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. rewrite (Z.mod_small (z * 2 ^ 32)) by lia.
  rewrite Z.div_mul by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* The all-ones mask OR any 64-bit value (0x8102c `or s9,a1,a0` with a1 = -1). *)
Lemma w5_lor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) x = 2 ^ 64 - 1.
Proof.
intros x Hx. change (2 ^ 64 - 1) with (Z.ones 64).
apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
destruct (Z.ltb_spec n 64) as [H|H].
- rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. cbn [orb].
  apply Z.bits_above_log2; [lia|].
  destruct (Z.eq_dec x 0) as [->|Hx0]; [cbn; lia|].
  assert (Hl : Z.log2 x < 64) by (apply Z.log2_lt_pow2; lia). lia.
Qed.

(* ---- the start state of the K5 stretch (0x80e0c .. 0x80e20) ----
   It reads two words: the loop's answer n in PS_N (0x80e14) and g_file_len (0x80e1c, a PLdHi at the object), and
   writes nothing. *)
Definition w5_K5_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_N (PS_N + 8) 0 0 [YP09.mkChunk PS_N (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]].
Definition ss_K5 : sstate := mkSS PP_K5 sr_hi8 w5_K5_regions None (mkFacts [] [] []).
(* The values the regions name: atom 32 = n (PS_N), atom 33 = |F| (g_file_len). *)
Definition w5_K5_extra (vN vF : Z) : list word := map (Z_to_bv 64) [vN; vF].

Lemma w5_entry_K5 : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 b p,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  c_n cx < 2 ^ 26 ->
  pregs cx ms3 ->
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) ->
  p_glob cx W3 ms3 b ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (w5_K5_extra (p_res cx (p_q cx p) mod 2 ^ 64) (p_nF cx))))
    ss_K5
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K5)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 b p HB HJ Hfrs Hn26 Hpregs R24 HN Hglob.
destruct (pe_sp1_bounds B MT KS LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & _ & _).
pose proof (pa_obj_img 4%nat ltac:(lia)) as Ho4.
unfold pcap_img_end, YImgTop.IMG_TOP in Ho4.
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (HvN : 0 <= p_res cx (p_q cx p) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
set (X := w5_K5_extra (p_res cx (p_q cx p) mod 2 ^ 64) (p_nF cx)).
set (E := Eimg (Ereg (ms_regs ms3) X)).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) X) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E32 : ew E 32 = Z_to_bv 64 (p_res cx (p_q cx p) mod 2 ^ 64))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (Us1 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; apply unsigned_lit_small; lia).
assert (Eo4 : ew E (A_OBJ 4) = Z_to_bv 64 (pa_val (A_OBJ 4)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Uo4 : bv_unsigned (ew E (A_OBJ 4)) = pa_val (A_OBJ 4))
  by (rewrite Eo4; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 4)); lia).
rewrite restrict_mkst_fx. unfold ss_K5. apply pa_entry_st_ok_full.
- apply w5_regs_ok. exact R24.
- vm_compute. reflexivity.
- unfold w5_K5_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Us1. unfold PS_N.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 32 0) (p_res cx (p_q cx p) mod 2 ^ 64));
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HN).
  + cbn [base_val]. fold E. rewrite Uo4.
    split; [lia|]. split; [pose proof (pa_val_range (A_OBJ 4)); lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 4)) 0 8 (SOff 33 0) (p_nF cx));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact (proj2 Hglob).
- apply pairwise_disjoint_of_extents.
  unfold w5_K5_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  fold E. rewrite Us1, Uo4. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PS_N. repeat split; lia.
- split; [exact I | split; [exact I | exact I]].
Qed.




(* The K5 stretch, walked. 0x80e0c s5 := first; 0x80e10 a0 := -1; 0x80e14 a1 := n (PS_N); 0x80e18 `blt a1,a0` to
   PP_abort, refuted because the record loop's answer n is 0 or -1 (PWalk.kind_nfit at the cut's p_kind <> KFit);
   0x80e1c a0 := g_file_len; 0x80e20 `bne s10(=at),a0` splits the phase: taken (at <> |F|) runs 0x80fa8 (s3 :=
   file <> 0, which the allocator's 4096 <= b makes 1) and 0x80fac (s7 := -9) into PP_KW with e := at; not taken
   (at = |F|) runs 0x80e24 (want := 0) into PP_KX, and the reader's answer from p is 0 (pe5_K5_end). *)
Lemma pe_from_K5 : pe_from_K5_stmt.
Proof.
unfold pe_from_K5_stmt. intros HKW HKX cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hacc HG.
destruct HG as (b & h & buf & p & HC & Hn26 & Hgood & Hprng & Hnfit & R10 & R18 & R20 & R24 & R26 &
  Hsl & Hbuf & HN & Hglob & Hsrc & Hpso & Hfit).
pose proof HC as (Hbody & Hk & Hacc' & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & Hpregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof (p_sizes cx) as (HnFle & _ & _).
(* the copy is a live block, so 4096 <= b (the snez at 0x80fa8 gives 1) *)
assert (HAR : AR SEGS B ly3 S3 W3 (ms_mem ms3) md3)
  by (pose proof HJ as HJc; destruct HJc as (_ & _ & (memS & HJi & _) & _); exact (proj1 HJi)).
assert (Hinb : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hinb) as (_ & Hb4096 & Hbceil & Hbia & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as (Hrq & _).
(* the record loop's answer is 0 or -1 *)
destruct (PWK.kind_nfit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) Hnfit) as (_ & Hres01).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbia.
pose proof (w5_entry_K5 cx fp k ly3 S3 W3 ms3 md3 b p HB HJ Hfrs Hn26 Hpregs R24 HN Hglob) as HS.
set (X := w5_K5_extra (p_res cx (p_q cx p) mod 2 ^ 64) (p_nF cx)) in HS.
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) X))) by apply Eimg_env.
pose proof (w5_sh_ok (Eimg (Ereg (ms_regs ms3) X)) (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K5)) (ms_mem ms3) (seg_rom SEGS)).
{ pose proof (ms_eta ms3 Hresv Hsvc Hfregs Hfcsr) as HE. rewrite Hpc, Hrom in HE. exact HE. }
rewrite Ems.
pose proof (bpaj_run_x B LAWS pe_G (pb_HG B MT KS cx HB) 0 (@nil (Z * Z))) as RUN.
pose proof (bpaj_run_to_x B LAWS pe_G (pb_HG B MT KS cx HB) 0 (@nil (Z * Z))) as RUNTO.
pose (BR := paj_branch (PI := PI)).
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm1. cbn [ms_mem mkst] in Hm1. clear HF HFr HG.
assert (EE : forall i, (i < A_TEXT)%nat -> ew (Eimg (Ereg (ms_regs ms3) X)) i = ew (Ereg (ms_regs ms3) X) i)
  by (intros i Hi; apply Eimg_low; exact Hi).
assert (EE32 : ew (Eimg (Ereg (ms_regs ms3) X)) 32 = Z_to_bv 64 (p_res cx (p_q cx p) mod 2 ^ 64))
  by (rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (EE33 : ew (Eimg (Ereg (ms_regs ms3) X)) 33 = Z_to_bv 64 (p_nF cx))
  by (rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (EE26 : ew (Eimg (Ereg (ms_regs ms3) X)) 26 = w64 p)
  by (rewrite EE by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ 26 26%bv eq_refl); exact R26).
change (pcap_source_struct_next.res_of (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)) with (p_res cx (p_q cx p)) in Hres01.
psrr_branch_tok RUN BR HS SHOK W5span.
- (* 0x80e18 taken: signed n < -1. n is 0 or -1 (as a word, 0 or 2^64 - 1): refuted. *)
  exfalso. cbn [branch_taken] in Hc. cbn [sv_denot] in Hc.
  rewrite EE32, Z.add_0_r in Hc. rewrite unsigned_lit_small in Hc by (apply Z.mod_pos_bound; lia).
  unfold bv_lts in Hc. rewrite !signed_lit in Hc.
  destruct Hres01 as [H0|H0]; rewrite H0 in Hc; vm_compute in Hc; discriminate Hc.
- (* 0x80e18 not taken; 0x80e1c a0 := g_file_len; stop at 0x80e20 `bne s10,a0` *)
  paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
  pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm2. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK W5span.
  + (* 0x80e20 taken: at <> |F|; 0x80fa8 s3 := (file <> 0), 0x80fac s7 := -9, to PP_KW *)
    rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 26 p EE26), (U_atom _ 33 (p_nF cx) EE33) in Hc0 by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KW; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm3. clear HF HFr HG.
    w5reg HS (10%bv : bv 5) Q10. w5reg HS (18%bv : bv 5) Q18. w5reg HS (19%bv : bv 5) Q19.
    w5reg HS (21%bv : bv 5) Q21. w5reg HS (23%bv : bv 5) Q23. w5reg HS (24%bv : bv 5) Q24.
    w5reg HS (26%bv : bv 5) Q26. w5reg HS (20%bv : bv 5) Q20.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    assert (Hmem : ms_mem ms1 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1; reflexivity).
    apply (HKW cx fp k acc ly3 S3 W3 ms1 _ HB HJ Hfrs Hacc).
    rewrite Ems1, Hmem.
    exists b, h, buf, p, p.
    split.
    { eapply w5_cut_move; [exact HC|]. apply (w5_pregs_keep cx ms3); [exact Hpregs | | | | |].
      - rewrite Q2. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q8. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q9. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q3. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q4. apply w5_denot_reg; [lia | reflexivity]. }
    split; [exact Hn26|]. split; [exact Hgood|]. split; [lia|]. split; [lia|]. split; [exact Hc0|].
    split; [exact (PWK.psn_q_skips (p_sw cx) (p_F cx) (p_cap cx) p ltac:(lia))|]. split; [exact Hnfit|].
    cbn [ms_regs mkst].
    split; [rewrite Q10; cbn [sv_denot]; rewrite EE33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q18, (w5_denot_reg _ _ 18 18%bv) by (lia || reflexivity); exact R18|].
    split; [rewrite Q19; apply (w5_snez _ _ b); [exact R18 | lia]|].
    split; [rewrite Q20, (w5_denot_reg _ _ 20 20%bv) by (lia || reflexivity); exact R20|].
    split; [rewrite Q21, (w5_denot_reg _ _ 10 10%bv) by (lia || reflexivity); exact R10|].
    split; [rewrite Q23; apply bv_eq; vm_compute; reflexivity|].
    split; [rewrite Q24, (w5_denot_img _ _ 288) by (unfold A_TEXT, A_LIM; lia); reflexivity|].
    split; [rewrite Q26, (w5_denot_reg _ _ 26 26%bv) by (lia || reflexivity); exact R26|].
    split; [exact Hsl|]. split; [exact Hbuf|]. split; [exact HN|]. split; [exact Hglob|].
    split; [exact Hsrc|]. split; [exact Hpso | exact Hfit].
  + (* 0x80e20 not taken: at = |F|; 0x80e24 want := 0, to PP_KX; the reader's answer from p is 0 *)
    rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 26 p EE26), (U_atom _ 33 (p_nF cx) EE33) in Hc0 by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    destruct (pe5_K5_end cx p ltac:(lia) Hc0) as (HQp & Hres0).
    paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm3. clear HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    assert (Hmem : ms_mem ms1 = ms_mem ms3) by (rewrite Hm3, Hm2, Hm1; reflexivity).
    apply (HKX cx fp k acc ly3 S3 W3 ms1 _ HB HJ Hfrs Hacc).
    rewrite Ems1, Hmem.
    exists b, h, buf, p.
    split.
    { eapply w5_cut_move; [exact HC|]. apply (w5_pregs_keep cx ms3); [exact Hpregs | | | | |].
      - rewrite Q2. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q8. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q9. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q3. apply w5_denot_reg; [lia | reflexivity].
      - rewrite Q4. apply w5_denot_reg; [lia | reflexivity]. }
    split; [exact Hn26|]. split; [exact Hgood|]. split; [lia|]. split; [exact Hnfit|].
    cbn [ms_regs mkst].
    split; [rewrite Q18, (w5_denot_reg _ _ 18 18%bv) by (lia || reflexivity); exact R18|].
    split; [rewrite Q20, (w5_denot_reg _ _ 20 20%bv) by (lia || reflexivity); exact R20|].
    split; [rewrite Q21, (w5_denot_reg _ _ 10 10%bv) by (lia || reflexivity); exact R10|].
    split; [rewrite Q25, Hres0; reflexivity|].
    split; [exact Hsl|]. split; [exact Hbuf|]. split; [exact HN|]. split; [exact Hglob|].
    split; [exact Hsrc|]. split; [exact Hpso | exact Hfit].
Qed.

(* ---- the start state of the KWL stretch (0x80fe4 .. 0x81030) ----
   It reads d (PS_D, 0x80ff8), cap (PS_CAP, 0x80ff0) and g_file_len three times through s8 (0x81000, 0x8100c,
   0x8101c, raw `ld a1,0x498(s8)`, so at the atom A_HI 8, offset 0x498), and writes nothing. *)
Definition w5_KWL_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_D (PS_CAP + 8) 0 0
     [YP09.mkChunk PS_D (CVal 8 (SOff 32 0)); YP09.mkChunk PS_CAP (CVal 8 (SOff 33 0))];
   YP09.mkRegion (Some (A_HI 8)) PE_GLEN_LO PE_GLEN_LO8 0 0 [YP09.mkChunk PE_GLEN_LO (CVal 8 (SOff 34 0))]].
Definition ss_KWL : sstate := mkSS PP_KWL sr_hi8 w5_KWL_regions None (mkFacts [] [] []).
(* The values the regions name: atom 32 = d, atom 33 = cap = 8 d, atom 34 = |F|. *)
Definition w5_KWL_extra (cx : ecx) : list word := map (Z_to_bv 64) [p_d cx; p_cap cx; p_nF cx].

Lemma w5_entry_KWL : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 b,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  c_n cx < 2 ^ 26 ->
  pregs cx ms3 ->
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  pslots cx fp W3 ms3 ->
  p_glob cx W3 ms3 b ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (w5_KWL_extra cx))) ss_KWL
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KWL)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 b HB HJ Hfrs Hn26 Hpregs R24 Hsl Hglob.
destruct (pe_sp1_bounds B MT KS LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & Hs1al & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (HnF & Hcap & _). pose proof (p_d_range cx) as Hd.
pose proof (pa_obj_img 4%nat ltac:(lia)) as Ho4.
unfold pcap_img_end, YImgTop.IMG_TOP in Ho4.
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hsl as (_ & HD & _ & _ & _ & _ & _ & HCAP).
pose proof (pa_val_range (A_HI 8)) as Rh8.
set (X := w5_KWL_extra cx).
set (E := Eimg (Ereg (ms_regs ms3) X)).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) X) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E32 : ew E 32 = Z_to_bv 64 (p_d cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (p_nF cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (Us1 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; apply unsigned_lit_small; lia).
assert (Eh8 : ew E (A_HI 8) = Z_to_bv 64 (pa_val (A_HI 8)))
  by (subst E; apply Eimg_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (Uh8 : bv_unsigned (ew E (A_HI 8)) = pa_val (A_HI 8)) by (rewrite Eh8; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_KWL. apply pa_entry_st_ok_full.
- apply w5_regs_ok. exact R24.
- vm_compute. reflexivity.
- unfold w5_KWL_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Us1. unfold PS_D, PS_CAP.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 24 8 (SOff 32 0) (p_d cx));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HD).
    * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 120 8 (SOff 33 0) (p_cap cx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HCAP).
  + cbn [base_val]. fold E. rewrite Uh8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pa_val (A_HI 8)) PE_GLEN_LO 8 (SOff 34 0) (p_nF cx));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite HHI8. exact (proj2 Hglob).
- apply pairwise_disjoint_of_extents.
  unfold w5_KWL_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  fold E. rewrite Us1, Uh8. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold PS_D, PS_CAP. repeat split; lia.
- split; [exact I | split; [exact I | exact I]].
Qed.

(* 0x8101c .. 0x8102c: want := -(|F| <u e + 16 + len) | len, which is -1 when the record is cut. *)
Lemma w5_U_cutfit : forall E s6 zx nF x l,
  U E s6 = x -> U E zx = l -> U E (SOff 34 0) = nF -> nF < x -> 0 <= l < 2 ^ 64 ->
  U E (SAlu ALU_OR (SAlu ALU_SUB (SLit 0) (SAlu ALU_SLTU (SOff 34 0) s6)) zx) = 2 ^ 64 - 1.
Proof.
intros E s6 zx nF x l Hs6 Hzx H34 Hlt Hl. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Hs6, Hzx, H34, U_SLit.
destruct (Z.ltb_spec nF x) as [_|H]; [|lia].
change (zcanon (zcanon 0 - zcanon 1)) with (2 ^ 64 - 1).
rewrite w5_lor_ones by exact Hl. reflexivity.
Qed.

(* The rd32 answer in a0 at PP_KWL, as the engine's atom 10 reads it. *)
Lemma w5_U_rd : forall (regs : bvmap 5 word) (X : list word) z,
  getr regs 10 = w64 (bv_swrap 32 z) -> U (Eimg (Ereg regs X)) (SOff 10 0) = bv_swrap 32 z mod 2 ^ 64.
Proof.
intros regs X z H. rewrite U_SOff. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs X 10 10%bv eq_refl), H. unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.

(* The KWL stretch, walked. 0x80fe4 `beqz a0` (len = 0, the model's KEmpty: e := e + 16 at 0x81010 after a0 :=
   g_file_len at 0x8100c, then 0x81014 `bne s6,a0` back to PP_KW, or want := 0 at 0x80e24 and PP_KX); else len
   zero-extended (0x80fe8, 0x80fec), a1 := cap (0x80ff0) and 0x80ff4 `bgeu a1,a0`: a record that fits by size goes to
   0x8101c .. 0x8102c (want := -1 when |F| < e + 16 + len, the model's KCutFit; a whole record would be the model's
   KFit, which GI_KWL's p_kind <> KFit refutes) and PP_KX; else a1 := d (0x80ff8) and 0x80ffc `beqz a1` (cap = 0, the
   model's KBig0: want = -1, PP_KX); else 0x81000 .. 0x81008 `bltu |F|,e + 16 + len` (KCutBig: want = -1, PP_KX), else
   e := e + 16 + len (KBig) and the same back edge 0x81014. No guard and no abort edge lies in this stretch. *)
Lemma pe_from_KWL_m : pe_from_KWL_m_stmt.
Proof.
unfold pe_from_KWL_m_stmt. intros m HKW HKX cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hacc (HG & Hmeas).
destruct HG as (b & h & buf & p & e & HC & Hn26 & Hgood & Hpe & Hef & Hsk & Hnfit & R10 & R18 & R19 & R20 & R21 &
  R22 & R23 & R24 & R25 & Hsl & Hbuf & HN & Hglob & Hsrc & Hpso & Hfit).
pose proof HC as (Hbody & Hk & Hacc' & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & Hpregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof (p_sizes cx) as (HnFle & Hcapr & _). pose proof (p_d_range cx) as Hdr.
change (p_hw cx e 8) with (PSN.incl (p_sw cx) (p_F cx) e) in R10.
set (L := PSN.incl (p_sw cx) (p_F cx) e) in *.
pose proof (pe5_incl_range cx e) as HL. fold L in HL.
rewrite R22 in Hmeas. unfold w64 in Hmeas. rewrite unsigned_lit_small in Hmeas by lia.
assert (Hcapd : p_cap cx = 8 * p_d cx) by reflexivity.
pose proof (w5_entry_KWL cx fp k ly3 S3 W3 ms3 md3 b HB HJ Hfrs Hn26 Hpregs R24 Hsl Hglob) as HS.
set (X := w5_KWL_extra cx) in HS.
set (E := Eimg (Ereg (ms_regs ms3) X)) in HS.
assert (HEI : img_env pa_val A_LIM E) by apply Eimg_env.
pose proof (w5_sh_ok E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
assert (EE : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) X) i)
  by (intros i Hi; apply Eimg_low; exact Hi).
assert (HU10 : U E (SOff 10 0) = bv_swrap 32 L mod 2 ^ 64) by (apply w5_U_rd; exact R10).
assert (HU22 : U E (SOff 22 0) = e + 16).
{ apply U_atom; [|lia]. rewrite EE by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ 22 22%bv eq_refl). exact R22. }
assert (HU32 : U E (SOff 32 0) = p_d cx) by (apply U_atom; [rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0) | lia]).
assert (HU33 : U E (SOff 33 0) = p_cap cx) by (apply U_atom; [rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1) | lia]).
assert (HU34 : U E (SOff 34 0) = p_nF cx) by (apply U_atom; [rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2) | lia]).
assert (EE34 : ew E 34 = Z_to_bv 64 (p_nF cx)) by (rewrite EE by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (HUz : U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32)) = L) by (apply w5_zext32; [exact HU10 | exact HL]).
assert (HU6 : U E (SAlu ALU_ADD (SOff 22 0) (SAlu ALU_SRL (SAlu ALU_SLL (SOff 10 0) (SLit 32)) (SLit 32)))
              = e + 16 + L).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HU22, HUz. unfold zcanon, M64. apply Z.mod_small. lia. }
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KWL)) (ms_mem ms3) (seg_rom SEGS)).
{ pose proof (ms_eta ms3 Hresv Hsvc Hfregs Hfcsr) as HE. rewrite Hpc, Hrom in HE. exact HE. }
rewrite Ems.
pose proof (bpaj_run_x B LAWS pe_G (pb_HG B MT KS cx HB) 0 (@nil (Z * Z))) as RUN.
pose proof (bpaj_run_to_x B LAWS pe_G (pb_HG B MT KS cx HB) 0 (@nil (Z * Z))) as RUNTO.
pose (BR := paj_branch (PI := PI)).
assert (Hatom : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
          sv_denot E (SOff n 0) = getr (ms_regs ms3) r)
  by (intros n r Hn Hr; apply w5_denot_reg; assumption).
assert (Hh8 : sv_denot E (SOff 288 0) = w64 (pa_val (A_HI 8)))
  by (apply w5_denot_img; unfold A_HI, A_TEXT, A_LIM; lia).
assert (H34 : sv_denot E (SOff 34 0) = w64 (p_nF cx))
  by (cbn [sv_denot]; rewrite EE34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_tok RUN BR HS SHOK W5span.
- (* 0x80fe4 taken: len = 0 *)
  rewrite branch_eq_U, HU10, U_lit in Hc by lia. apply Z.eqb_eq in Hc.
  assert (HL0 : L = 0) by (pose proof (w5_swrap_eq0 L HL) as H0; rewrite Hc in H0; symmetry in H0; apply Z.eqb_eq in H0; exact H0).
  pose proof (pe5_exit_empty cx e (p_q cx p) Hsk Hef HL0) as Hsk16.
  (* 0x8100c a0 := g_file_len; 0x81010 s10 := s6; stop at 0x81014 `bne s6,a0` *)
  paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
  pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm. cbn [ms_mem mkst] in Hm. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK W5span.
  + (* 0x81014 taken: e + 16 <> |F|, back to PP_KW with e := e + 16 *)
    rewrite branch_ne_U, HU22, HU34 in Hc0. apply Bool.negb_true_iff, Z.eqb_neq in Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KW; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (10%bv : bv 5) Q10. w5reg HS (18%bv : bv 5) Q18. w5reg HS (19%bv : bv 5) Q19.
    w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21. w5reg HS (23%bv : bv 5) Q23.
    w5reg HS (24%bv : bv 5) Q24. w5reg HS (26%bv : bv 5) Q26.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKW cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KW (m - 16) cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p (e + 16) HC Hn26 Hgood);
      [ lia | lia | lia | exact Hsk16 | exact Hnfit | lia
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q10; exact H34
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q19, (Hatom 19%nat 19%bv) by (lia || reflexivity); exact R19
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q23, (Hatom 23%nat 23%bv) by (lia || reflexivity); exact R23
      | rewrite Q24; exact Hh8
      | rewrite Q26, (Hatom 22%nat 22%bv) by (lia || reflexivity); exact R22
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
  + (* 0x81014 not taken: e + 16 = |F|; 0x81018 `j` 0x80e24 want := 0, to PP_KX *)
    rewrite branch_ne_U, HU22, HU34 in Hc0. apply Bool.negb_false_iff, Z.eqb_eq in Hc0.
    destruct (pe5_exit_end cx (e + 16) (p_q cx p) Hsk16 Hc0) as (_ & Hres0).
    paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKX cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KX cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p HC Hn26 Hgood);
      [ lia | exact Hnfit
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q25, Hres0; reflexivity
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
- (* 0x80fe4 not taken: len <> 0 *)
  rewrite branch_eq_U, HU10, U_lit in Hc by lia. apply Z.eqb_neq in Hc.
  assert (HLn0 : L <> 0) by (intros HL0; apply Hc; rewrite HL0; reflexivity).
  (* 0x80fe8 / 0x80fec zero-extension, 0x80ff0 a1 := cap; stop at 0x80ff4 `bgeu a1,a0` *)
  paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
  pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm. cbn [ms_mem mkst] in Hm. clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK W5span.
  + (* 0x80ff4 taken: len <= cap *)
    rewrite branch_geu_U, HU33, HUz in Hc0. apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
    destruct (Z_le_gt_dec (e + 16 + L) (p_nF cx)) as [Hwhole | Hcut].
    { exfalso. exact (pe5_exit_fit_absurd cx e (p_q cx p) Hsk Hef HLn0 Hc0 Hwhole Hnfit). }
    destruct (pe5_exit_cutfit cx e (p_q cx p) Hsk Hef HLn0 Hc0 ltac:(lia)) as (_ & Hres1).
    paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKX cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KX cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p HC Hn26 Hgood);
      [ lia | exact Hnfit
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q25, Hres1, denot_lit_U, (w5_U_cutfit E _ _ (p_nF cx) (e + 16 + L) L HU6 HUz HU34 ltac:(lia) ltac:(lia)); unfold w64; apply bv_eq; vm_compute; reflexivity
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
  + (* 0x80ff4 not taken: cap < len *)
    rewrite branch_geu_U, HU33, HUz in Hc0. apply Bool.negb_false_iff, Z.ltb_lt in Hc0.
    (* 0x80ff8 a1 := d; stop at 0x80ffc `beqz a1` *)
    paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
    pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG. rename Hm' into Hm.
    psrr_branch_tok RUN BR HS SHOK W5span.
    * (* 0x80ffc taken: d = 0, so cap = 0 (KBig0): want = -1, to PP_KX *)
      rewrite branch_eq_U, HU32, U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1.
      assert (Hcap0 : p_cap cx = 0) by lia.
      pose proof (pe5_exit_big0 cx e (p_q cx p) Hsk Hef Hc0 Hcap0) as (_ & Hres2).
      paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
      pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKX cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KX cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p HC Hn26 Hgood);
      [ lia | exact Hnfit
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q25, Hres2, (Hatom 25%nat 25%bv) by (lia || reflexivity); exact R25
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
    * (* 0x80ffc not taken: d <> 0, cap <> 0 *)
      rewrite branch_eq_U, HU32, U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1.
      assert (Hcapn0 : p_cap cx <> 0) by lia.
      (* 0x81000 a1 := g_file_len, 0x81004 s6 := e + 16 + len; stop at 0x81008 `bltu a1,s6` *)
      paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
      pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG. rename Hm' into Hm.
      psrr_branch_tok RUN BR HS SHOK W5span.
      -- (* 0x81008 taken: |F| < e + 16 + len (KCutBig): want = -1, to PP_KX *)
        rewrite branch_ltu_U, HU34, HU6 in Hc2. apply Z.ltb_lt in Hc2.
        pose proof (pe5_exit_cutbig cx e (p_q cx p) Hsk Hef Hc0 Hcapn0 Hc2) as (_ & Hres3).
        paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
        pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKX cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KX cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p HC Hn26 Hgood);
      [ lia | exact Hnfit
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q25, Hres3, (Hatom 25%nat 25%bv) by (lia || reflexivity); exact R25
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
      -- (* 0x81008 not taken: the oversized record is whole (KBig) and is skipped *)
        rewrite branch_ltu_U, HU34, HU6 in Hc2. apply Z.ltb_ge in Hc2.
        pose proof (pe5_exit_big cx e (p_q cx p) Hsk Hef Hc0 Hcapn0 Hc2) as HskB. fold L in HskB.
        (* 0x8100c a0 := g_file_len, 0x81010 s10 := s6; stop at 0x81014 `bne s6,a0` *)
        paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
        pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG. rename Hm' into Hm.
        psrr_branch_tok RUN BR HS SHOK W5span.
        ++ (* 0x81014 taken: back to PP_KW with e := e + 16 + len *)
          rewrite branch_ne_U, HU6, HU34 in Hc3. apply Bool.negb_true_iff, Z.eqb_neq in Hc3.
          paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KW; [ w5_awr | ].
          pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (10%bv : bv 5) Q10. w5reg HS (18%bv : bv 5) Q18. w5reg HS (19%bv : bv 5) Q19.
    w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21. w5reg HS (23%bv : bv 5) Q23.
    w5reg HS (24%bv : bv 5) Q24. w5reg HS (26%bv : bv 5) Q26.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKW cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KW (m - 16) cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p (e + 16 + L) HC Hn26 Hgood);
      [ lia | lia | lia | exact HskB | exact Hnfit | lia
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q10; exact H34
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q19, (Hatom 19%nat 19%bv) by (lia || reflexivity); exact R19
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q23, (Hatom 23%nat 23%bv) by (lia || reflexivity); exact R23
      | rewrite Q24; exact Hh8
      | rewrite Q26, denot_lit_U, U_SAlu; cbn [zalu_raw]; rewrite HU6, U_SLit; change (zcanon 0) with 0;
        rewrite Z.add_0_r; unfold zcanon, M64, w64; rewrite Z.mod_small by lia; reflexivity
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
        ++ (* 0x81014 not taken: e + 16 + len = |F|; 0x81018 `j` 0x80e24 want := 0, to PP_KX *)
          rewrite branch_ne_U, HU6, HU34 in Hc3. apply Bool.negb_false_iff, Z.eqb_eq in Hc3.
          destruct (pe5_exit_end cx (e + 16 + L) (p_q cx p) HskB Hc3) as (_ & Hres4).
          paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
          pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm'. rewrite Hm in Hm'. clear Hm HF HFr HG.
    w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
    w5reg HS (25%bv : bv 5) Q25.
    w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
    w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
    pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msN) =>
      apply (HKX cx fp k acc ly3 S3 W3 msN _ HB HJ Hfrs Hacc); rewrite Ems1, Hm' end.
    eapply (w5_mk_KX cx fp PP_KWL k acc ly3 S3 W3 ms3 md3 _ _ _ b h buf p HC Hn26 Hgood);
      [ lia | exact Hnfit
      | apply (w5_pregs_keep cx ms3); [exact Hpregs | rewrite Q2; apply Hatom; [lia | reflexivity]
          | rewrite Q8; apply Hatom; [lia | reflexivity] | rewrite Q9; apply Hatom; [lia | reflexivity]
          | rewrite Q3; apply Hatom; [lia | reflexivity] | rewrite Q4; apply Hatom; [lia | reflexivity]]
      | rewrite Q18, (Hatom 18%nat 18%bv) by (lia || reflexivity); exact R18
      | rewrite Q20, (Hatom 20%nat 20%bv) by (lia || reflexivity); exact R20
      | rewrite Q21, (Hatom 21%nat 21%bv) by (lia || reflexivity); exact R21
      | rewrite Q25, Hres4; reflexivity
      | exact Hsl | exact Hbuf | exact HN | exact Hglob | exact (conj Hsrc (conj Hpso Hfit)) ].
Qed.

(* ==== KW stretch ==== *)

(* The start state of the KW stretch (0x80fb0 .. 0x80fe0): it reads one word, ps.swapped (0x80fd8 `lw a1,8(s4)`, the
   field p_psopen states), and writes nothing. Atom 32 = p_swz (0 or 1). *)
Definition kw_regions : smem :=
  [YP09.mkRegion (Some 20%nat) 8 12 0 0 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))]].
Definition ss_KW : sstate := mkSS PP_KW sr_hi8 kw_regions None (mkFacts [(32%nat, mkAF 0 1 0)] [] []).
Definition kw_extra (sw : Z) : list word := map (Z_to_bv 64) [sw].

Lemma kw_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 h,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) ->
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) ->
  p_psopen cx fp W3 ms3 h ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (kw_extra (p_swz cx)))) ss_KW
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 h HB HJ Hfrs R20 R24 (_ & Hsw).
destruct (pe_sp1_bounds B MT KS LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs) as (_ & _ & _ & _ & Hf0 & Hf1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_swz_01 cx) as Hsz.
unfold PE_FRAME in Hf1.
set (E := Eimg (Ereg (ms_regs ms3) (kw_extra (p_swz cx)))).
assert (E32 : ew E 32 = Z_to_bv 64 (p_swz cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U20 : bv_unsigned (ew E 20) = pPS cx fp).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat _ _ 20 20%bv eq_refl), R20.
  apply unsigned_lit_small. unfold pPS, PO_PS. lia. }
rewrite restrict_mkst_fx. unfold ss_KW. apply pa_entry_st_ok_full.
- apply w5_regs_ok. exact R24.
- vm_compute. reflexivity.
- unfold kw_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. fold E. rewrite U20.
  split; [unfold pPS, PO_PS; lia|]. split; [unfold pPS, PO_PS; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (pPS cx fp) 8 4 (SOff 32 0) (p_swz cx));
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact Hsw].
- exact (conj I I).
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite E32, unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

(* The three blocks of the end-of-walk cuts, and their bounds. *)
Lemma kw_blocks3 : forall cx ly3 S3 W3 (ms3 : machine_state) md3 b h buf,
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 ->
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)]) ->
  In (b, p_nF cx) (ablocks B ly3 S3) /\
  4096 <= b /\ b + p_nF cx <= alloc_ceiling /\ 4096 <= h /\ h + SRC_FILE_BLOCK <= alloc_ceiling /\
  4096 <= buf /\ buf + p_bn cx <= alloc_ceiling.
Proof.
intros cx ly3 S3 W3 ms3 md3 b h buf HAR HP.
assert (HI : forall x, In x [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] -> In x (ablocks B ly3 S3)).
{ intros x Hx. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_or_app. right. exact Hx. }
pose proof (HI (b, p_nF cx) ltac:(cbn; tauto)) as I1.
pose proof (HI (h, SRC_FILE_BLOCK) ltac:(cbn; tauto)) as I2.
pose proof (HI (buf, p_bn cx) ltac:(cbn; tauto)) as I3.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR I1) as (_ & B1 & B2 & _ & _ & _ & B3).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR I2) as (_ & B4 & B5 & _ & _ & _ & B6).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR I3) as (_ & B7 & B8 & _ & _ & _ & B9).
pose proof (req_size_pos (p_nF cx) ltac:(pose proof (p_sizes cx); lia)) as R1.
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as R2.
pose proof (req_size_pos (p_bn cx) ltac:(pose proof (p_sizes cx); lia)) as R3.
split; [exact I1|]. lia.
Qed.

Lemma kw_den : forall (E : env) (n : nat), sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* A register of the state stopped at the rd32 call (an st_ok state, setpc to the callee), as its symbolic value. *)
Ltac kw_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

(* The KW stretch, walked. 0x80fb0 s6 := e + 16, 0x80fb4 s9 := -1; 0x80fb8 `bltu a0(=|F|),s6` taken (fewer than 16
   bytes left) goes to PP_KX with want = -1, which is the reader's answer (pe5_exit_cuth); not taken, 0x80fbc
   a0 := file + e, the four UBSan guards (0x80fc0, 0x80fcc, 0x80fd0, 0x80fd4, each into the trap 0x8103c) are refuted
   from the live block (b, |F|) (4096 <= b, b + |F| <= alloc_ceiling), e <= |F| and s3 = 1, s7 = -9; 0x80fd8 a1 :=
   ps.swapped (p_psopen), 0x80fdc a0 := file + e + 8, and the call of rd32 (0x80fe0) reads the four bytes of the copy
   at e + 8, which the reader's stream holds (asource_at_bytes), to its return PP_KWL with a0 = incl at e. *)
Lemma pe_from_KW_m : pe_from_KW_m_stmt.
Proof.
unfold pe_from_KW_m_stmt. intros m HKWL HKX cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hacc (HG & HM).
destruct HG as (b & h & buf & p & e & HC & Hn26 & Hgood & Hpe & HeF & Hne & Hsk & Hnfit & R10 & R18 & R19 & R20 &
  R21 & R23 & R24 & R26 & Hsl & Hbuf & HN & Hglob & Hrd).
pose proof HC as (Hbody & Hk & Hacc' & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & Hpregs & Hsaved & Hhdr & Hshd & Hshlen & Hgin).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof (p_sizes cx) as (HnFle & _ & _).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
unfold LLVMF_STK in Hspc.
destruct (kw_blocks3 cx ly3 S3 W3 ms3 md3 b h buf HAR Hperm) as (Hinb & Hb1 & Hb2 & Hh1 & Hh2 & Hu1 & Hu2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HMe : p_nF cx - e <= m)
  by (rewrite R26 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; exact HM).
pose proof Hrd as (Hsrc & Hpso & Hfit).
pose proof (kw_entry cx fp k ly3 S3 W3 ms3 md3 h HB HJ Hfrs R20 R24 Hpso) as HS.
remember (Eimg (Ereg (ms_regs ms3) (kw_extra (p_swz cx)))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_swz cx))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
clear HEdef.
(* the atoms of the start state: a register atom is the register at PP_KW *)
assert (KQ : forall (n : nat) (r : bv 5) (msx : machine_state), (n < A_TEXT)%nat -> Z.of_nat n = bv_unsigned r ->
          getr (ms_regs msx) r = sv_denot E (SOff n 0) -> getr (ms_regs msx) r = getr (ms_regs ms3) r)
  by (intros n r msx Hn Hr H; rewrite H, kw_den; apply EW; assumption).
assert (E10 : ew E 10 = Z_to_bv 64 (p_nF cx))
  by (rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R10).
assert (E18 : ew E 18 = Z_to_bv 64 b) by (rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 1) by (rewrite (EW 19%nat 19%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R19).
assert (E23 : ew E 23 = Z_to_bv 64 (2 ^ 64 - 9))
  by (rewrite (EW 23%nat 23%bv ltac:(unfold A_TEXT; lia) eq_refl), R23; apply bv_eq; vm_compute; reflexivity).
assert (E26 : ew E 26 = Z_to_bv 64 e) by (rewrite (EW 26%nat 26%bv ltac:(unfold A_TEXT; lia) eq_refl); exact R26).
(* file + e, as the guards read it: no wrap, since the copy is a live block and e <= |F| *)
assert (UA : U E (SAlu ALU_ADD (SOff 18 0) (SOff 26 0)) = b + e).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 18 b E18), (U_atom E 26 e E26) by lia.
  apply zcanon_id. unfold M64. lia. }
assert (US : U E (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 18 0) (SOff 26 0)) (SLit 1)) = 0).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite UA, U_SLit. change (zcanon 1) with 1.
  destruct (Z.ltb_spec (b + e) 1) as [H|H]; [lia | reflexivity]. }
assert (UX : U E (SAlu ALU_XOR (SOff 19 0) (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 18 0) (SOff 26 0)) (SLit 1))) = 1).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite US, (U_atom E 19 1 E19) by lia. reflexivity. }
pose proof (w5_sh_ok E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KW)) (ms_mem ms3) (seg_rom SEGS)).
{ pose proof (ms_eta ms3 Hresv Hsvc Hfregs Hfcsr) as HE. rewrite Hpc, Hrom in HE. exact HE. }
rewrite Ems.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 (@nil (Z * Z))) as RUN.
pose proof (bpaj_run_to_x B LAWS pe_G HGX 0 (@nil (Z * Z))) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* 0x80fb0 s6 := e + 16, 0x80fb4 s9 := -1; stop at 0x80fb8 `bltu a0,s6` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm1. cbn [ms_mem mkst] in Hm1. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK W5span.
{ (* 0x80fb8 taken: |F| < e + 16 (and e <> |F|): to PP_KX with want = -1, the reader's answer from p *)
  rewrite branch_ltu_U, (U_atom E 10 (p_nF cx) E10), (U_atom_off E 26 e 16 E26) in Hc by lia.
  apply Z.ltb_lt in Hc.
  destruct (pe5_exit_cuth cx e (p_q cx p) Hsk Hne ltac:(lia)) as (_ & Hres).
  paj_run_to_tok RUNTO HS HJ SHOK W5span PP_KX; [ w5_awr | ].
  pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm2. clear HF HFr HG.
  w5reg HS (18%bv : bv 5) Q18. w5reg HS (20%bv : bv 5) Q20. w5reg HS (21%bv : bv 5) Q21.
  w5reg HS (25%bv : bv 5) Q25.
  w5reg HS (2%bv : bv 5) Q2. w5reg HS (8%bv : bv 5) Q8. w5reg HS (9%bv : bv 5) Q9.
  w5reg HS (3%bv : bv 5) Q3. w5reg HS (4%bv : bv 5) Q4.
  pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as Ems1. cbn [ss_pc add_cond] in Ems1.
  assert (Hmem : ms_mem ms0 = ms_mem ms3) by (rewrite Hm2, Hm1; reflexivity).
  apply (HKX cx fp k acc ly3 S3 W3 ms0 _ HB HJ Hfrs Hacc).
  rewrite Ems1, Hmem.
  exists b, h, buf, p.
  split.
  { eapply w5_cut_move; [exact HC|]. apply (w5_pregs_keep cx ms3); [exact Hpregs | | | | |].
    - exact (KQ 2%nat 2%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q2).
    - exact (KQ 8%nat 8%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q8).
    - exact (KQ 9%nat 9%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q9).
    - exact (KQ 3%nat 3%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q3).
    - exact (KQ 4%nat 4%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q4). }
  split; [exact Hn26|]. split; [exact Hgood|]. split; [lia|]. split; [exact Hnfit|].
  cbn [ms_regs mkst].
  split; [rewrite (KQ 18%nat 18%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q18); exact R18|].
  split; [rewrite (KQ 20%nat 20%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q20); exact R20|].
  split; [rewrite (KQ 21%nat 21%bv ms0 ltac:(unfold A_TEXT; lia) eq_refl Q21); exact R21|].
  split; [rewrite Q25, Hres; apply bv_eq; vm_compute; reflexivity|].
  split; [exact Hsl|]. split; [exact Hbuf|]. split; [exact HN|]. split; [exact Hglob|]. exact Hrd. }
(* 0x80fb8 not taken: e + 16 <= |F| *)
rewrite branch_ltu_U, (U_atom E 10 (p_nF cx) E10), (U_atom_off E 26 e 16 E26) in Hc by lia.
apply Z.ltb_ge in Hc. rename Hc into He16.
(* 0x80fbc a0 := file + e; stop at 0x80fc0 `bltu a0,s2` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm2. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK W5span.
{ (* 0x80fc0 taken (file + e <u file, into the trap 0x8103c): refuted, b + e does not wrap *)
  exfalso. rewrite branch_ltu_U, UA, (U_atom E 18 b E18) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x80fc4 a1 := (a0 = 0), 0x80fc8 a1 := s3 xor a1; stop at 0x80fcc `beqz a1` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm3. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK W5span.
{ (* 0x80fcc taken ((file <> 0) = (file + e = 0), into the trap): refuted, s3 = 1 and b + e <> 0 *)
  exfalso. rewrite branch_eq_U, UX, U_SLit in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* stop at 0x80fd0 `beqz s2` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm4. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK W5span.
{ (* 0x80fd0 taken (file = NULL, into the trap): refuted, 4096 <= b *)
  exfalso. rewrite branch_eq_U, (U_atom E 18 b E18), U_SLit in Hc by lia. apply Z.eqb_eq in Hc.
  change (zcanon 0) with 0 in Hc. lia. }
clear Hc.
(* stop at 0x80fd4 `bltu s7(=-9),a0` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm5. clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK W5span.
{ (* 0x80fd4 taken (file + e + 8 wraps, into the trap): refuted, b + e <= alloc_ceiling < 2^64 - 9 *)
  exfalso. rewrite branch_ltu_U, (U_atom E 23 (2 ^ 64 - 9) E23), UA in Hc by lia. apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x80fd8 a1 := ps.swapped, 0x80fdc a0 := file + e + 8, 0x80fe0 the call of rd32 *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm6. clear HF HFr HG.
kw_reg HS (1%bv : bv 5) Q1. kw_reg HS (2%bv : bv 5) Q2. kw_reg HS (3%bv : bv 5) Q3. kw_reg HS (4%bv : bv 5) Q4.
kw_reg HS (8%bv : bv 5) Q8. kw_reg HS (9%bv : bv 5) Q9. kw_reg HS (10%bv : bv 5) Q10. kw_reg HS (11%bv : bv 5) Q11.
kw_reg HS (18%bv : bv 5) Q18. kw_reg HS (19%bv : bv 5) Q19. kw_reg HS (20%bv : bv 5) Q20.
kw_reg HS (21%bv : bv 5) Q21. kw_reg HS (22%bv : bv 5) Q22. kw_reg HS (23%bv : bv 5) Q23.
kw_reg HS (24%bv : bv 5) Q24. kw_reg HS (25%bv : bv 5) Q25.
assert (Hmem : ms_mem ms5 = ms_mem ms3) by (rewrite Hm6, Hm5, Hm4, Hm3, Hm2, Hm1; reflexivity).
pose proof (KQ 2%nat 2%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q2) as Q2'.
pose proof (KQ 3%nat 3%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q3) as Q3'.
pose proof (KQ 4%nat 4%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q4) as Q4'.
pose proof (KQ 8%nat 8%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q8) as Q8'.
pose proof (KQ 9%nat 9%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q9) as Q9'.
pose proof (KQ 18%nat 18%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q18) as Q18'.
pose proof (KQ 19%nat 19%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q19) as Q19'.
pose proof (KQ 20%nat 20%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q20) as Q20'.
pose proof (KQ 21%nat 21%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q21) as Q21'.
pose proof (KQ 23%nat 23%bv ms5 ltac:(unfold A_TEXT; lia) eq_refl Q23) as Q23'.
assert (Q1' : getr (ms_regs ms5) 1 = Z_to_bv 64 (BASE + 2140)) by (rewrite Q1; exact (codeptr_val E 2140 HEI)).
assert (Ha0c : getr (ms_regs ms5) 10 = Z_to_bv 64 (b + (e + 8))).
{ rewrite Q10, denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E 18 b 8 E18), (U_atom E 26 e E26) by lia.
  unfold zcanon, M64. rewrite Z.mod_small by lia. lia. }
assert (Hsw11 : bv_unsigned (getr (ms_regs ms5) 11) = p_swz cx).
{ rewrite Q11, kw_den, E32. apply unsigned_lit_small. destruct (p_swz_01 cx) as [H|H]; rewrite H; lia. }
assert (Q22' : getr (ms_regs ms5) 22 = Z_to_bv 64 (e + 16))
  by (rewrite Q22, denot_lit_U, (U_atom_off E 26 e 16 E26) by lia; reflexivity).
assert (Q24' : getr (ms_regs ms5) 24 = Z_to_bv 64 (pa_val (A_HI 8))).
{ rewrite Q24. cbn [sv_denot]. rewrite (HEI 288%nat ltac:(unfold A_TEXT, A_LIM; lia)), Z.add_0_r. reflexivity. }
assert (Q25' : getr (ms_regs ms5) 25 = Z_to_bv 64 (-1)) by (rewrite Q25; apply bv_eq; vm_compute; reflexivity).
assert (Usp : spZ (ms_regs ms5) = c_sp1 cx) by (unfold spZ; rewrite Q2', Rsp; apply unsigned_lit_small; lia).
(* the four bytes of the header's len, from the reader's own copy of the file *)
assert (HC4 : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms5)) (b + (e + 8))
                [nth (Z.to_nat (e + 8)) (p_C cx) 0; nth (Z.to_nat (e + 8 + 1)) (p_C cx) 0;
                 nth (Z.to_nat (e + 8 + 2)) (p_C cx) 0; nth (Z.to_nat (e + 8 + 3)) (p_C cx) 0]).
{ rewrite Hmem.
  exact (garr8_four _ b (p_C cx) (e + 8) (asource_at_bytes KS _ _ _ _ _ Hsrc) ltac:(lia) ltac:(rewrite p_lens; lia)). }
pmkst HS. rewrite pa_sigma_rd32.
eapply SRr_bind.
{ exact (rd32_call B LAWS TL LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms5) _ k (ms_regs ms5) (b + (e + 8)) b (p_nF cx)
    (nth (Z.to_nat (e + 8)) (p_C cx) 0) (nth (Z.to_nat (e + 8 + 1)) (p_C cx) 0)
    (nth (Z.to_nat (e + 8 + 2)) (p_C cx) 0) (nth (Z.to_nat (e + 8 + 3)) (p_C cx) 0) HJ
    ltac:(rewrite Q1'; apply ret_ok_codeptr_v; [lia | reflexivity])
    Ha0c
    ltac:(rewrite Usp; lia)
    ltac:(rewrite Usp; unfold Rd32.RD32_FRAME, LLVMF_STK; lia)
    ltac:(rewrite Usp; lia)
    Hinb ltac:(lia) ltac:(lia) HC4). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & Hsame & Hfr2).
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms5) (Z_to_bv 5 r))
  by exact HP2.
assert (UNa : mk W3 (ms_mem ms3) mem2 (c_sp1 cx - 16) (c_sp1 cx)).
{ intros a Ha Hn. rewrite <- Hmem. apply Hfr2; [exact Ha | unfold Rd32.RD32_FRAME; rewrite Usp; exact Hn]. }
destruct (same_but_materialized_fs _ _ Hsame) as (Hfd2 & Hfs2).
assert (G10 : getr regs2 10 = w64 (bv_swrap 32 (p_hw cx e 8)))
  by (rewrite Ha0, (trd32_hw cx e 8 _ Hsw11); reflexivity).
assert (G18 : getr regs2 18 = w64 b)
  by exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) (eq_trans Q18' R18)).
assert (G19 : getr regs2 19 = w64 1)
  by exact (eq_trans (P 19 ltac:(unfold acallee_saved; lia)) (eq_trans Q19' R19)).
assert (G20 : getr regs2 20 = w64 (pPS cx fp))
  by exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) (eq_trans Q20' R20)).
assert (G21 : getr regs2 21 = w64 (p_first cx))
  by exact (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) (eq_trans Q21' R21)).
assert (G22 : getr regs2 22 = w64 (e + 16)) by exact (eq_trans (P 22 ltac:(unfold acallee_saved; lia)) Q22').
assert (G23 : getr regs2 23 = w64 (-9))
  by exact (eq_trans (P 23 ltac:(unfold acallee_saved; lia)) (eq_trans Q23' R23)).
assert (G24 : getr regs2 24 = w64 (pa_val (A_HI 8)))
  by exact (eq_trans (P 24 ltac:(unfold acallee_saved; lia)) Q24').
assert (G25 : getr regs2 25 = w64 (-1)) by exact (eq_trans (P 25 ltac:(unfold acallee_saved; lia)) Q25').
set (msK := mkst regs2 (getr (ms_regs ms5) 1) mem2 (seg_rom SEGS)).
assert (UNaK : mk W3 (ms_mem ms3) (ms_mem msK) (c_sp1 cx - 16) (c_sp1 cx)) by exact UNa.
apply (HKWL cx fp k acc ly3 S3 W3 msK md2 HB HJ2 Hfrs Hacc).
split.
2: { change (getr (ms_regs msK) 22) with (getr regs2 22). rewrite G22. unfold w64.
     rewrite unsigned_lit_small by lia. lia. }
exists b, h, buf, p, e.
split.
{ split.
  { eapply (pe_body_keep cx fp PP_KW PP_KWL W3 ms3 msK PSH_ts (c_sp1 cx - 16) (c_sp1 cx) Hbody);
    try reflexivity;
    [ cbn [ms_pc_val msK mkst]; rewrite Q1'; reflexivity
    | exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2')
    | exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8')
    | exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9')
    | exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3')
    | exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4')
    | exact UNaK | lia | lia | unfold LLVMF_STK; lia | lia | exact Hf0 | exact Hf1 | exact Hinp ]. }
  split; [exact Hk|]. split; [exact Hacc'|]. split; [exact Hperm|].
  split; [rewrite Hfd2; repeat rewrite (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds
         | rewrite Hfs2; repeat rewrite (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs]. }
split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hpe|]. split; [exact He16|].
split; [exact Hsk|]. split; [exact Hnfit|].
split; [exact G10|]. split; [exact G18|]. split; [exact G19|]. split; [exact G20|]. split; [exact G21|].
split; [exact G22|]. split; [exact G23|]. split; [exact G24|]. split; [exact G25|].
split; [exact (pslots_keep cx fp W3 ms3 msK _ _ Hsl UNaK ltac:(unfold slots_apart; left; lia) ltac:(lia) ltac:(lia))|].
split; [exact (pslot_keep cx W3 ms3 msK _ _ PS_BUF buf Hbuf UNaK ltac:(unfold PS_BUF; lia)
                 ltac:(unfold PS_BUF; lia) ltac:(right; unfold PS_BUF; lia))|].
split; [exact (pslot_keep cx W3 ms3 msK _ _ PS_N _ HN UNaK ltac:(unfold PS_N; lia)
                 ltac:(unfold PS_N; lia) ltac:(right; unfold PS_N; lia))|].
split; [exact (p_glob_keep cx W3 ms3 msK _ _ b Hglob UNaK ltac:(lia))|].
exact (p_reader_keep B KS ASIL cx fp W3 ms3 msK _ _ b h buf p Hrd UNaK ltac:(lia) Hf0 Hf1 ltac:(lia) Hh2
         ltac:(lia) Hb2 ltac:(lia) Hu2).
Qed.

(* ==== end KW ==== *)

(* ==== KX stretch ==== *)
(* KX -> K6, listing offsets 0x6a0 .. 0x6ac (pcs 0x80e28 .. 0x80e34), from PP_KX:
     0x80e28 `ld a0,0x70(s1)`  a0 := n, the word in PS_N (GI_KX: p_res Q mod 2^64, Q = p_q cx p);
     0x80e2c `bne a0,s9`       to PP_abort 0x81034 when n <> want; REFUTED at the branch: s9 = w64 (p_res Q) (GI_KX), the
                               same word as n (PcapEntryKit.w64_mod64);
     0x80e30 `mv a0,s4`        a0 := &ps = pPS cx fp;
     0x80e34 `jal pcap_source_close`, the PROVED contract lib/B/Prog/PcapSourceClose.v pb_pcap_source_closeX through
                               lib/B/Prog/PcapEntryCalls.v close_call, back at PP_K6 0x80e38.
   No UBSan guard (PcapEntryDefs.PE_GUARDS) and no __asan_report_* call lies in the stretch.
   Two Section hypotheses of this stretch, the ones lib/A/Prog/PcapHarnessTail.v takes for the same call (MLAWS, HRO):
   the meter laws (mo_le_trans adds close's charge to the cut's meter), and PcapBase.ro_below_ofl, the read-only bytes
   below the open-file list head, which PcapBase.arodata_ok_journalP needs to carry pe_base's arodata_okP to the call
   state (close's premise). *)
Hypothesis KX_MTL : ameter_laws MT.
Hypothesis KX_HRO : @ro_below_ofl SEGS pa_relro_lo pa_relro_hi SK.

(* ---- list facts: the blocks of a state are distinct (lib/A/Prog/PcapHarnessTail.v nodup_of_split / notin_prefix) ---- *)
Lemma kx_nodup_of_split : forall {A} (l : list A),
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) -> List.NoDup l.
Proof.
intros A l. induction l as [|a t IH]; intros H; [apply List.NoDup_nil|]. apply List.NoDup_cons.
- intros Hin. apply List.in_split in Hin as (t1 & t2 & ->). apply (H [] a t1 t2). reflexivity.
- apply IH. intros l1 x l2 l3 E. apply (H (a :: l1) x l2 l3). rewrite E. reflexivity.
Qed.

Lemma kx_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply kx_nodup_of_split. intros l1 x l2 l3 E.
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md x x l1 l2 l3 HAR E) as D.
assert (Hin : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct x as [q n].
destruct (al_blocks _ _ LAWS ly S W mem md q n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R _].
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.

Lemma kx_notin_prefix : forall {A} (l L M : list A) x,
  List.NoDup l -> Permutation l (L ++ M) -> List.In x M -> ~ List.In x L.
Proof.
intros A l L M x Hnd Hp HxM. apply (Permutation_NoDup Hp) in Hnd. clear Hp l.
induction L as [|a L IH]; intros Hin; [destruct Hin|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hna Hnd].
destruct Hin as [-> | Hin]; [apply Hna; apply in_or_app; right; exact HxM | exact (IH Hnd Hin)].
Qed.

(* ---- the call state's view of pe_base's facts (lib/A/Prog/PcapHarnessTail.v aview_memS, meta_now, aro_now) ---- *)
Lemma kx_aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.

Lemma kx_meta_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly3 (mrestrict (w_H W3) mem3) (c_M cx).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ &
  _ & _ & _ & HGX & HGD & _).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
  rewrite <- (kx_aview_memS cx memS x Hag ltac:(lia)).
  + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
  + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  rewrite <- (kx_aview_memS cx memS a Hag ltac:(lia)).
  + apply F5.
    * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
  + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.

Lemma kx_aro_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS
    (c_md cx) own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
eapply (arodata_ok_journalP (SK := SK) (RO := KX_HRO) SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
intros a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
rewrite (kx_aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.

(* ---- what close keeps of the bytes GI_K6 reads (lib/A/Prog/PcapHarnessTail.v hfoot / tail_kept / foot_kept, at this
   image's frame: the saved registers [sp0 - 104, sp0), the spill slots [s1 + 16, s1 + 0x98), the frame's header and
   flag word, its shadow, and the input) ---- *)
Definition kx_hfoot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (PcapEntryDefs.c_regs cx) - 104 <= a < spZ (PcapEntryDefs.c_regs cx)) \/
  (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) \/
  (c_p cx <= a < c_p cx + c_n cx).

Lemma kx_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (specialize (H 0 ltac:(lia)); rewrite Z.add_0_r in H; exact H).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

Lemma kx_tail_kept : forall (cx : ecx) fp W (ms : machine_state) W' (ms' : machine_state) sh buf,
  (forall a, kx_hfoot cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms -> pshadow cx fp W ms sh -> length sh = PE_NSH ->
  garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  pslots cx fp W ms -> pslot cx W ms PS_BUF buf ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\ pshadow cx fp W' ms' sh /\
  garr8 SEGS (mrestrict (w_H W') (ms_mem ms')) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  pslots cx fp W' ms' /\ pslot cx W' ms' PS_BUF buf.
Proof.
intros cx fp W ms W' ms' sh buf HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hsh Hlen Hin
  (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8) PB.
assert (RW : forall a, (forall i, 0 <= i < 8 -> kx_hfoot cx fp (a + i)) ->
  rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
  by (intros a Ha; apply kx_rdword_ext; intros i Hi; apply HK, Ha, Hi).
split; [|split; [|split; [|split; [|split]]]].
- split.
  + rewrite RW; [exact Hs8|]. intros i Hi. unfold kx_hfoot. left. lia.
  + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold kx_hfoot. left. lia.
- unfold pheader, PE_FLAGPTR in *.
  split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold kx_hfoot; right; right; left;
  first [left; lia | right; lia].
- intros i Hi. rewrite HK; [exact (Hsh i Hi)|]. unfold kx_hfoot. right; right; right; left.
  rewrite Hlen in Hi. unfold PE_NSH in Hi. lia.
- apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
  unfold kx_hfoot. right; right; right; right. rewrite length_map in Ha. unfold c_n. lia.
- unfold pslots, pslot, PS_F0, PS_D, PS_SHB, PS_SH, PS_F, PS_FK, PS_TSP, PS_CAP in *.
  repeat split; (rewrite RW; [assumption|]); intros i Hi; unfold kx_hfoot; right; left; lia.
- unfold pslot, PS_BUF in *. rewrite RW; [exact PB|]. intros i Hi. unfold kx_hfoot. right; left. lia.
Qed.

Lemma kx_foot_kept : forall (cx : ecx) fp lyc Sc (W : world SEGS) (memc : word -> option byte) (W2 : world SEGS)
  (mem2 : word -> option byte) slo shi (E : Z -> Prop),
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  alloc_ceiling <= c_sp1 cx -> c_sp1 cx + 256 <= spZ (PcapEntryDefs.c_regs cx) ->
  spZ (PcapEntryDefs.c_regs cx) <= 2 ^ 47 -> shi <= c_sp1 cx + 16 ->
  In (PE_CID, fp) (frames Sc) -> frame_addr lyc PE_CID fp = pF cx fp ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B lyc Sc)) ->
  (forall a, kx_hfoot cx fp a -> ~ E a) ->
  forall a, kx_hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros cx fp lyc Sc W memc W2 mem2 slo shi E K1 K2 K4 Hs1c Hs1s Hsp47 Hshi Hfr Efa Hinb HE a Ha.
pose proof (HE a Ha) as HnE.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- apply K1; lia.
- apply K1; lia.
- apply (K4 PE_CID fp a Hfr); [|exact HnE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes PE_CID) with 128. lia.
- apply (K4 PE_CID fp a Hfr); [|exact HnE]. right. unfold in_zr. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold pSH, shadow_of_addr in Ha. unfold shadow_addr. lia.
- destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|lia].
  replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) (Hinb Hn)).
  + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
  + replace (c_p cx + (a - c_p cx)) with a by lia. exact HnE.
Qed.

(* A block the call allocated (not the input) misses every byte of kx_hfoot. *)
Lemma kx_block_off : forall cx fp ly3 S3 W3 mem3 md3 q n,
  AR SEGS B ly3 S3 W3 mem3 md3 ->
  alloc_ceiling <= c_sp1 cx -> c_sp1 cx + 256 <= spZ (PcapEntryDefs.c_regs cx) ->
  In (q, n) (ablocks B ly3 S3) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ (c_p cx, c_n cx) <> (q, n)) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  forall a, kx_hfoot cx fp a -> ~ (q <= a < q + req_size n).
Proof.
intros cx fp ly3 S3 W3 mem3 md3 q n HAR Hs1c Hs1s Hin Hinp Hfin Efa x Hx Hex.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ q n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q n PE_CID fp HAR Hin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
unfold kx_hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia; try (Z.div_mod_to_equations; lia).
assert (Hcn : 0 < c_n cx) by lia.
destruct (Hinp Hcn) as [Hpin Hne].
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.

(* Bytes of the frame past its 24-byte header and before its flag word (ps, ts) miss every byte of kx_hfoot. *)
Lemma kx_frame_off : forall cx fp ly3 S3 W3 mem3 md3 q m,
  AR SEGS B ly3 S3 W3 mem3 md3 ->
  alloc_ceiling <= c_sp1 cx -> c_sp1 cx + 256 <= spZ (PcapEntryDefs.c_regs cx) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  pF cx fp + 24 <= q -> q + m <= pF cx fp + 120 ->
  forall a, kx_hfoot cx fp a -> ~ (q <= a < q + m).
Proof.
intros cx fp ly3 S3 W3 mem3 md3 q m HAR Hs1c Hs1s Hinp Hfin Efa Hq1 Hq2 x Hx Hex.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
unfold kx_hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; try lia; try (Z.div_mod_to_equations; lia).
assert (Hcn : 0 < c_n cx) by lia.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR (Hinp Hcn) Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.

(* ---- the start state of the KX stretch (0x80e28 .. 0x80e34): one region, the slot PS_N, read only; atom 32 = n ---- *)
Definition kx_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_N (PS_N + 8) 0 0 [YP09.mkChunk PS_N (CVal 8 (SOff 32 0))]].
Definition ss_KX : sstate := mkSS PP_KX sr_atoms kx_regions None (mkFacts [] [] []).
Definition kx_extra (vN : Z) : list word := map (Z_to_bv 64) [vN].

Lemma kx_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 vN,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pregs cx ms3 -> 0 <= vN < 2 ^ 64 -> pslot cx W3 ms3 PS_N vN ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (kx_extra vN))) ss_KX
    (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KX)) (ms_mem ms3) (seg_rom SEGS))).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 vN HB HJ Hfrs Hpregs HvN HN.
destruct (pe_sp1_bounds B MT KS LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs) as (Hs1lo & Hs1al & Hsp1 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof HB as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
set (E := Eimg (Ereg (ms_regs ms3) (kx_extra vN))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (kx_extra vN)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E32 : ew E 32 = Z_to_bv 64 vN) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E9 : ew E 9 = getr (ms_regs ms3) 9)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 9 9%bv eq_refl)).
assert (Us1 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9, Rs1; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold ss_KX. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold kx_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. fold E. rewrite Us1. unfold PS_N.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (c_sp1 cx) 112 8 (SOff 32 0) vN);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ HN).
- apply pairwise_disjoint_of_extents.
  unfold kx_regions, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- split; [exact I | split; [exact I | exact I]].
Qed.

(* The KX stretch, walked: the check 0x80e2c (its abort arm refuted) and the call of pcap_source_close 0x80e34, whose
   post rebuilds GI_K6 at its return PP_K6 0x80e38. *)
Lemma pe_from_KX : pe_from_KX_stmt.
Proof.
unfold pe_from_KX_stmt. intros HK6 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hacc HG.
destruct HG as (b & h & buf & p & HC & Hn26 & Hgood & Hprng & Hnfit & R18 & R20 & R21 & R25 &
  Hsl & Hbuf & HN & Hglob & Hsrc).
pose proof HC as (Hbody & Hk & Hacc' & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & Hpregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof Hpregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof Hsrc as (Hsat & (Hpsf & Hpsw) & _).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1e & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinpb & Hs1b & Hal32).
destruct (pe_sp1_bounds B MT KS LAWS cx fp k ly3 S3 W3 (ms_mem ms3) md3 HB HJ Hfrs)
  as (Hs1lo & _ & _ & Efa & _ & _ & Hfapp).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & _ & _ & _ & _ & Hev0 & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HGD & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok _ _ PI) as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (HnFle & Hcap & Hbn).
unfold PE_FRAME in Hf1.
assert (Hs1c : alloc_ceiling <= c_sp1 cx) by lia.
assert (Hs1s : c_sp1 cx + 256 <= spZ (PcapEntryDefs.c_regs cx)) by lia.
(* the blocks: the FILE h is one the call allocated, distinct from the input *)
assert (Hhin : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hbin : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hhout : ~ In (h, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (kx_notin_prefix _ _ _ _ (kx_ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ h SRC_FILE_BLOCK HAR Hhin) as (_ & Hh4096 & Hhceil & _ & _ & _ & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (Hpin0 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hn. pose proof HB as (_ & _ & _ & _ & Hinput & _). destruct Hinput as [[H0 _] | [_ Hin0]]; [lia | exact Hin0]. }
assert (Hpin3 : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3))
  by (intros Hn; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact (Hpin0 Hn)).
assert (Hpinne : 0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ (c_p cx, c_n cx) <> (h, SRC_FILE_BLOCK)).
{ intros Hn. split; [exact (Hpin3 Hn)|]. intros Heq. apply Hhout. rewrite <- Heq. exact (Hpin0 Hn). }
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0) by (rewrite Hps; apply mod64_mod8; exact Hf64).
(* the symbolic state at PP_KX *)
assert (HvN : 0 <= p_res cx (p_q cx p) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
pose proof (kx_entry cx fp k ly3 S3 W3 ms3 md3 _ HB HJ Hfrs Hpregs HvN HN) as HS.
remember (Eimg (Ereg (ms_regs ms3) (kx_extra (p_res cx (p_q cx p) mod 2 ^ 64)))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat ->
  ew E i = ew (Ereg (ms_regs ms3) (kx_extra (p_res cx (p_q cx p) mod 2 ^ 64))) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 (p_res cx (p_q cx p) mod 2 ^ 64))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
clear EL HEdef.
pose proof (w5_sh_ok E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_KX)) (ms_mem ms3) (seg_rom SEGS)).
{ pose proof (ms_eta ms3 Hresv Hsvc Hfregs Hfcsr) as HE. rewrite Hpc, Hrom in HE. exact HE. }
rewrite Ems.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 (@nil (Z * Z))) as RUN.
pose (BR := paj_branch (PI := PI)).
(* 0x80e28 a0 := n; stop at 0x80e2c `bne a0,s9` *)
paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm1. cbn [ms_mem mkst] in Hm1. clear HF HFr HG.
rename ms into ms1. rename mat into mat1.
psrr_branch_tok RUN BR HS SHOK W5span.
- (* 0x80e2c taken (n <> want), to PP_abort 0x81034: refuted, n and want are the same word *)
  exfalso. rewrite branch_ne_U in Hc.
  rewrite (U_atom E 32 _ E32 HvN) in Hc.
  rewrite (U_atom E 25 (p_res cx (p_q cx p) mod 2 ^ 64)) in Hc;
    [ rewrite Z.eqb_refl in Hc; cbn in Hc; discriminate Hc
    | rewrite (EW 25%nat 25%bv ltac:(unfold A_TEXT; lia) eq_refl), R25; exact (eq_sym (w64_mod64 _))
    | exact HvN ].
- (* 0x80e2c not taken; 0x80e30 a0 := &ps; 0x80e34 jal pcap_source_close *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK W5span; [ w5_awr | ].
  pose proof (w5_frame_eq _ _ _ _ HF eq_refl) as Hm2. cbn [ms_mem mkst] in Hm2. clear HF HFr HG.
  assert (HFm : ms_mem ms = ms_mem ms3) by (rewrite Hm2, Hm1; reflexivity).
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q18.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q20.
  rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q21.
  assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
  destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnev & _).
  assert (HEV : EV_LIB = 10) by reflexivity.
  pmkst HS. rewrite pa_sigma_pcap_source_close.
  eapply SRr_bind.
  { eapply (close_call SK B MT KS
      (OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog.PcapSourceClose.pb_pcap_source_closeX SK B KS MT
         LAWS TL ra_fc1 ra_fc2 AFCLOSE HUfc1 HUfc2 ASIL FM)
      LLVMF_STK (spZ (PcapEntryDefs.c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pPS cx fp) h b (c_M cx) (p_pos cx (p_q cx p))
      (p_C cx) PE_CID fp HJ).
    - exact (kx_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    - rewrite Q3, Rgp. exact Hgp0.
    - rewrite Q4, Rtp. exact Htp0.
    - exact Q10.
    - rewrite Hsp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal32; [|lia]. destruct Hal32 as [q Hq].
      exists (2 * q). lia.
    - rewrite Hsp. assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity. rewrite HTS.
      unfold LLVMF_STK. lia.
    - rewrite Hsp. lia.
    - left. reflexivity.
    - rewrite Efa, Hps. lia.
    - rewrite Efa, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
    - split; [rewrite Hps; lia | exact Hps8].
    - rewrite HFm. exact Hpsf.
    - lia.
    - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
      intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r.
      rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hf64; [|lia];
        destruct Hf64 as [q Hq]; exists (8 * q); lia).
      change (32 / 8) with 4. exact (Hshd 4%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    - intros _. split; [exact Hhin|]. split; [rewrite p_lens; exact Hbin|].
      split; [rewrite HFm; exact Hsat|].
      split; [exact (kx_meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag)|].
      intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
      right. exists h, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|].
      change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. lia.
    - rewrite HEV in Hev0. unfold AC.EV_CLOSE. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hmle & Hfd2 & Hfs2 & HPm & Hnull &
    HK & Hsrc2).
  assert (Hh0 : h <> 0) by lia.
  assert (Hfb : AC.tclose_fblk h = [(h, SRC_FILE_BLOCK)])
    by (unfold AC.tclose_fblk; destruct (Z.eqb_spec h 0); [lia | reflexivity]).
  assert (Hif : (if h =? 0 then 0 else mo_free MT + mo_free MT) = mo_free MT + mo_free MT)
    by (destruct (Z.eqb_spec h 0); [lia | reflexivity]).
  rewrite Hfb in HPm. cbn [app] in HPm. rewrite Hif in Hmle.
  destruct (Hsrc2 Hh0) as [Hnone2 Hcopy2].
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by exact HP2.
  assert (Hshi0 : spZ (ms_regs ms) <= c_sp1 cx + 16) by (rewrite Hsp; lia).
  assert (Hfoot : forall a, kx_hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite <- HFm.
    refine (kx_foot_kept cx fp ly3 S3 W3 (ms_mem ms) W2 mem2 _ _
      (fun a => (pPS cx fp <= a < pPS cx fp + 8) \/ (h <> 0 /\ h <= a < h + req_size SRC_FILE_BLOCK))
      (fun a Ha Hn => K1 a Ha Hn) K2 K4 Hs1c Hs1s Hsp47 Hshi0 Hfin Efa Hpin3 _ a Ha).
    intros x Hx [Hx1 | [_ Hx2]].
    - exact (kx_frame_off cx fp ly3 S3 W3 (ms_mem ms3) md3 (pPS cx fp) 8 HAR Hs1c Hs1s Hpin3 Hfin Efa
        ltac:(rewrite Hps; lia) ltac:(rewrite Hps; lia) x Hx Hx1).
    - exact (kx_block_off cx fp ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hs1c Hs1s Hhin Hpinne Hfin Efa
        x Hx Hx2). }
  destruct (kx_tail_kept cx fp W3 ms3 W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) PSH_ts buf Hfoot
    Hsaved Hhdr Hshd Hshlen Hinp Hsl Hbuf) as (T1 & T2 & T3 & T4 & T5 & T6).
  assert (Hgk : forall a, inG pe_G a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha. rewrite <- HFm. destruct (HGX a Ha) as [Hi Hno]. destruct (HGD a Ha) as (_ & _ & Hne & Hna).
    exact (K3 a Hi Hno Hne Hna). }
  assert (Hglob2 : p_glob cx W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) b).
  { destruct Hglob as (G1 & G2). unfold p_glob, pval in G1, G2 |- *. cbn [ms_mem mkst]. split.
    - eapply val_mem_frame; [|exact G1]. intros x Hx. apply (mbyte_of_aview SEGS). apply Hgk.
      unfold pe_G. apply inG_cons. right. apply inG_cons. left. unfold in_zr. cbn [fst snd].
      change (Z.of_nat 8) with 8 in Hx. lia.
    - eapply val_mem_frame; [|exact G2]. intros x Hx. apply (mbyte_of_aview SEGS). apply Hgk.
      unfold pe_G. apply inG_cons. left. unfold in_zr. cbn [fst snd]. change (Z.of_nat 8) with 8 in Hx. lia. }
  apply (HK6 cx fp (k + AC.EV_CLOSE) (acc + (mo_free MT + mo_free MT)) ly2 S2 W2
    (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB HJ2).
  + rewrite Hfr2. exact Hfrs.
  + exact (mo_le_trans MT KX_MTL _ _ _ _ _ Hacc Hmle).
  + exists b, buf.
    split.
    { split.
      { split; [cbn [ms_pc_val mkst]; rewrite Q1; reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split.
        { unfold pregs. cbn [ms_regs mkst].
          split; [exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) (eq_trans Q2 Rsp))|].
          split; [exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) (eq_trans Q8 Rs0))|].
          split; [exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) (eq_trans Q9 Rs1))|].
          split; [exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) (eq_trans Q3 Rgp))|].
          exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) (eq_trans Q4 Rtp)). }
        split; [exact T1|]. split; [exact T2|]. split; [exact T3|]. split; [exact Hshlen | exact T4]. }
      split; [unfold AC.EV_CLOSE; lia|].
      split; [unfold PA_K6; lia|].
      split.
      { assert (HP' : Permutation ((h, SRC_FILE_BLOCK) :: ablocks B ly2 S2)
          ((h, SRC_FILE_BLOCK) :: (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (buf, p_bn cx)]))).
        { eapply Permutation_trans; [exact (Permutation_sym HPm)|]. eapply Permutation_trans; [exact Hperm|].
          replace (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)])
            with ((ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) ++ (h, SRC_FILE_BLOCK) :: [(buf, p_bn cx)])
            by (rewrite <- app_assoc; reflexivity).
          eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
          rewrite <- app_assoc. apply Permutation_refl. }
        exact (Permutation_cons_inv HP'). }
      split.
      { rewrite Hfd2. repeat rewrite (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)). exact Hfds. }
      { rewrite Hfs2. repeat rewrite (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)). exact Hfs. } }
    split; [exact Hn26|]. split; [exact Hgood|].
    cbn [ms_regs mkst].
    split; [exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) (eq_trans Q18 R18))|].
    split; [exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) (eq_trans Q20 R20))|].
    split; [exact (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) (eq_trans Q21 R21))|].
    split; [exact T5|]. split; [exact T6|]. split; [exact Hglob2|].
    split; [exact Hcopy2|]. split; [exact Hnull | exact Hnone2].
Qed.
(* ==== end KX ==== *)

(* ---- the loop and the composition, PROVED from the four stretch statements ---- *)

(* A cut at a bound on the measure is weaker than the cut itself, and monotone in the bound. *)
Lemma pe_measW_weak : forall GI m, PF GI -> PF (pe_measW GI m).
Proof.
intros GI m H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc (HG & _).
exact (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc HG).
Qed.

Lemma pe_measW_mono : forall GI m m', m <= m' -> PF (pe_measW GI m') -> PF (pe_measW GI m).
Proof.
intros GI m m' Hle H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc (HG & Hm).
apply (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc). split; [exact HG | lia].
Qed.

(* Every state of a cut meets its own measure, so the bounded family covers the plain cut. *)
Lemma pe_from_measW_all : forall GI, (forall m, PF (pe_measW GI m)) -> PF GI.
Proof.
intros GI H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc HG.
apply (H (p_nF cx - bv_unsigned (getr (ms_regs ms3) 26)) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc).
split; [exact HG | lia].
Qed.

Lemma pe_from_measL_all : forall GI, (forall m, PF (pe_measL GI m)) -> PF GI.
Proof.
intros GI H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc HG.
apply (H (p_nF cx + 16 - bv_unsigned (getr (ms_regs ms3) 22)) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc).
split; [exact HG | lia].
Qed.

(* At PP_KW the harness's e is s10 and e < |F| (GI_KW: e <= |F| and e <> |F|), so the measure is at least 1: a
   cut at a bound m <= 0 describes no state. *)
Lemma pe_measW_vac : forall m, m <= 0 -> PF (pe_measW (GI_KW B MT KS) m).
Proof.
intros m Hm cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hacc (HG & Hle).
exfalso. destruct HG as (b & h & buf & p & e & HG).
repeat match goal with Hx : _ /\ _ |- _ => destruct Hx end.
pose proof (p_sizes cx) as (Hs1 & _ & _).
match goal with H26 : getr (ms_regs ms3) 26 = w64 e |- _ => rewrite H26 in Hle end.
unfold w64 in Hle. rewrite unsigned_lit_small in Hle by lia. lia.
Qed.

(* The end-of-walk loop: KW -> KWL -> KW grows e by at least 16 (0x81004 / 0x81010 with len >= 0), so |F| - e
   falls by at least 16 on every turn, and the loop is closed by strong induction on it. *)
Lemma pe_endloop_n : pe_from_KW_m_stmt -> pe_from_KWL_m_stmt -> PF GI_KX ->
  forall n : nat, PF (pe_measW (GI_KW B MT KS) (Z.of_nat n)).
Proof.
intros HKW HKWL HKX n.
induction n as [n IH] using (well_founded_induction PeanoNat.Nat.lt_wf_0).
destruct (Z_le_gt_dec (Z.of_nat n) 0) as [Hle|Hgt]; [apply pe_measW_vac; lia|].
apply HKW; [|exact HKX]. apply HKWL; [|exact HKX].
destruct (Z_le_gt_dec (Z.of_nat n - 16) 0) as [Hle2|Hgt2]; [apply pe_measW_vac; lia|].
apply (pe_measW_mono _ (Z.of_nat n - 16) (Z.of_nat (n - 16))); [lia|].
apply IH. lia.
Qed.

Lemma pe_from_endloop_of : pe_from_KW_m_stmt -> pe_from_KWL_m_stmt -> pe_from_endloop_stmt.
Proof.
intros HKW HKWL HKX. apply pe_from_measW_all. intros m.
destruct (Z_le_gt_dec m 0) as [Hle|Hgt]; [apply pe_measW_vac; lia|].
apply (pe_measW_mono _ m (Z.of_nat (Z.to_nat m))); [lia|].
apply (pe_endloop_n HKW HKWL HKX).
Qed.

Lemma pe_from_KW_K6_of : pe_from_KX_stmt -> pe_from_endloop_stmt -> pe_from_KW_K6_stmt.
Proof. intros HKX HL H6. apply HL. apply HKX. exact H6. Qed.

Lemma pe_from_KWL_K6_of : pe_from_KX_stmt -> pe_from_KW_m_stmt -> pe_from_KWL_m_stmt -> pe_from_KWL_K6_stmt.
Proof.
intros HKX HKW HKWL H6.
assert (HX : PF GI_KX) by (apply HKX; exact H6).
assert (HW : PF (GI_KW B MT KS)) by (apply (pe_from_endloop_of HKW HKWL); exact HX).
apply pe_from_measL_all. intros m. apply HKWL; [apply pe_measW_weak; exact HW | exact HX].
Qed.

Lemma pe_from_K5_K6_of : pe_from_K5_stmt -> pe_from_KX_stmt -> pe_from_KW_m_stmt -> pe_from_KWL_m_stmt ->
  pe_from_K5_K6_stmt.
Proof.
intros H5 HKX HKW HKWL H6.
assert (HX : PF GI_KX) by (apply HKX; exact H6).
apply H5; [apply (pe_from_endloop_of HKW HKWL); exact HX | exact HX].
Qed.


(* The end-of-walk loop, closed: every state at PP_KW reaches the join PP_KX. *)
Lemma pe_from_endloop : pe_from_endloop_stmt.
Proof. exact (pe_from_endloop_of pe_from_KW_m pe_from_KWL_m). Qed.

(* ---- the phase, composed: every cut of this phase reaches PP_K6 ---- *)
Lemma pe_from_KW_K6 : pe_from_KW_K6_stmt.
Proof. exact (pe_from_KW_K6_of pe_from_KX pe_from_endloop). Qed.

Lemma pe_from_KWL_K6 : pe_from_KWL_K6_stmt.
Proof. exact (pe_from_KWL_K6_of pe_from_KX pe_from_KW_m pe_from_KWL_m). Qed.

Lemma pe_from_K5_K6 : pe_from_K5_K6_stmt.
Proof. exact (pe_from_K5_K6_of pe_from_K5 pe_from_KX pe_from_KW_m pe_from_KWL_m). Qed.

End c.
End b.
End a.

(* The sink head is EXPLICIT on every exported statement that depends on it (a Theorem Labs lane, 21:57Z; see PcapEntry.v): the only
   global sink_head instance in this closure is the plain build's, so it must never be inferred. *)
Arguments pe_from_KX_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_KWL_m_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_KW_m_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_K5_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_endloop_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_KW_K6_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_KWL_K6_stmt {fx rc} SK {PI} B MT KS POST.
Arguments pe_from_K5_K6_stmt {fx rc} SK {PI} B MT KS POST.
