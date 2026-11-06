(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file, written for libreac/fuzz_pcap -- a Theorem Labs lane of the walk of fuzz_pcap's entry function
   LLVMFuzzerTestOneInput on fuzz_pcap.asan-ubsan (libreac v1.9.0, 0x80818, listing offset AF_LLVMFuzzerTestOneInput
   = 0x90 of lib/B/Prog/PcapList.v): phase L3, the record loop's head and the harness's skip loop, as cut lemmas in the
   pe_from form of lib/B/Prog/PcapEntryDefs.v at the waypoint invariants GI_* of lib/B/Prog/PcapEntryPhases.v.

   The stretches (pcs of the pin; capstone disassembly llvmf-au.dis (sha256 be945029c797; internal record)):
     KD  -> K4 / K5  0x80b04 `blez a0` (n = first <= 0 to 0x80e04: s10 := 24, n spilled at 0x70(s1), PP_K5 0x80e0c);
                     else the loop's constants (0x80b08 .. 0x80b3c: a3 := 0, calls := 0 at 0x68(s1), buf + 12 at
                     0x38(s1), s7 := ~b, s10 := 24, s5 := -8, 0xf00 at 0x30(s1), 10^6 2^32 at 0x40(s1), n at
                     0x70(s1)) to PP_K4 0x80b40.
     K4  -> KR       0x80b40 .. 0x80b8c: the calls bound 0x80b50 (abort), first := (calls = 0 ? n : a3) at 0x50(s1)
                     (0x80b5c .. 0x80b64), n <= cap 0x80b70 (abort), at + 16 <= g_file_len 0x80b7c (abort), the UBSan
                     guard 0x80b80 `beqz s2` (file = NULL), calls := calls + 1 (0x80b84 .. 0x80b8c), to PP_KR 0x80b90.
     KR  -> KRI      the UBSan guards 0x80b90 `bltu s7,s10` (wrap(file + e)) and 0x80b98 `bgeu s3,s5` (wrap(file + e +
                     8)), s3 := file + e, a1 := ps.swapped (0x80b9c `lw a1,8(s4)`), a0 := s3 + 8, and the call of rd32
                     (0x80ba4) to its return PP_KRI 0x80ba8.
     KRI -> KR / KO  s11 := incl (sign-extended), s9 := incl (zero-extended); 0x80bb4 `beqz s11` (an empty record) and
                     0x80bbc `bgeu a0(=cap),s9` (a fit one) decide the arm. Skip: s9 := e + incl, s6 := e + incl + 32,
                     s10 := e + incl + 16, 0x80bd0 `bgeu len,s6` back to PP_KR, else 0x80bd4 `j` to PP_abort. Fit: the
                     UBSan guard 0x80bdc `bltu a0(=-17),s3` (wrap(file + e + 16)), at + 16 + incl <= len 0x80be8
                     (abort), a1 := ps.swapped, s6 := ps.last_orig_len (0x80bf0 `lw s6,0xc(s4)`), a0 := s3 + 12, and
                     the call of rd32 (0x80bf8) to its return PP_KO 0x80bfc.
   The skip loop (KR -> KRI -> KR) is closed here by induction on |F| - e (pe_from_skip_m); the record loop's measure
   is the same register (s10 = at <= e <= Q), so pe_meas states every cut lemma at a bound m on |F| - s10 for the lane
   that closes the record loop (K4 <= KL2 <= ... <= KO <= KRI <= KR <= K4).

   Rule 24 (task text of a Theorem Labs lane): a search of the proof index for LLVMFuzzerTestOneInput (index v5 built
   2026-10-28T21:58:24Z, rebuilt 23:22:17Z, recipes 566eb6ffa5d) rc=0; the 30 named files are all in other units, and no
   row names libreac/fuzz_pcap; the working-branch search found no Qed walk of it on any asan-ubsan image. CONFIRM
   (23:47Z): the released fuzz_pcap harness walks (lib/U/Prog/Slot/USegE.v etc.) are for the v1.8 UBSAN image (343
   instructions, 176-byte frame) against this pin's 530 instructions with a 256-byte frame and ASan instrumentation, so
   this is a new proof. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntrySkip.v, with its module paths and module names changed; 2326 of its 2461 lines of code are new or changed and 2297 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapEntryTail.v, with its module names changed; 335 of its 390 lines of code are new or changed and 2406 lines of the source are left out. *)
(* The PROGRAM-callee call sites of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput, 0x80818, asan-ubsan build of
   libreac v1.9.0), lifted once to the harness's journal, so that every phase file of the walk applies one lemma per
   call site instead of opening and repacking the journal itself (owner: a Theorem Labs lane; ruling of 02:5xZ: one text,
   one owner. The keep helpers live in a Theorem Labs lane's lib/B/Prog/PcapEntryKit.v).

   The harness's journal is W_journalG.v's `ajournal_gx SEGS B pe_G 0 []` (the two globals g_file / g_file_len are
   written by the harness itself, so they are the journal's program-global ranges). A PROGRAM callee of the harness
   states its contract in cgif_file's CALLER-JOURNAL form (lib/A/Prog/PcapSourceCloseSpec.v
   tpcap_source_close_specX, lib/A/Prog/PcapSourceOpenDefs.v tpcap_source_open_specX, lib/A/Prog/PcapSourceNextDefs.v
   tpcap_source_next_specX): it takes the caller's donor `ajournal` and gives it back extended. So the lift is
     gx_open   (the gx journal's inner donor journal, at the same start memory memS)
     the callee's contract at that donor journal
     gx_pack0  (the same gagree, XO = 0, no out cell)
   and nothing of the callee's post changes. `rd32` is the one program callee whose contract takes a FRESH journal
   from the call state; its lift is PaJournalFs.ajournal_gx_callee (a Theorem Labs lane's rd32_call).

   Each contract comes in as an argument, not as a Section hypothesis, so that a caller may pass either the proved
   instance (close: lib/B/Prog/PcapSourceClose.v pb_pcap_source_closeX) or its own Section hypothesis (open, next).

   TAKEN FROM: the journal lemmas of lib/A/W_journalG.v (a Theorem Labs lane) and the three contracts above; this file proves
   no callee. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapList PcapAddr PcapPa.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require YC85G.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec PcapSourceOpenDefs PcapSourceNextSpec PcapFuzzFopenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct_next.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceCloseSpec.
Module AO := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceOpenDefs.
Module AN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapSourceNextSpec.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module AF := OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog.PcapFuzzFopenDefs.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- the two halves of the lift ---- *)

(* The donor journal inside the harness's gx journal: the same window, the same owned frames, and a start memory
   that agrees with the harness's outside the globals. *)
Lemma gx_open : forall G STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
  ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
  exists memS, ajournal SEGS B STK sp0 FP ly S W memS md own lyc Sc Wc memc mdc k /\
               gagree G (w_H W) mem memS /\ 0 <= STK.
Proof.
intros G STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k (HSTK & _ & (memS & HJ & Hag) & _).
rewrite !Z.add_0_r in HJ. exists memS. split; [exact HJ | split; [exact Hag | exact HSTK]].
Qed.

(* The gx journal again, from a donor journal at the same start memory (XO = 0, so the out clause is empty). *)
Lemma gx_pack0 : forall G STK sp0 FP ly S (W : world SEGS) mem md own ly2 S2 (W2 : world SEGS) mem2 md2 k2 memS,
  0 <= STK -> ajournal SEGS B STK sp0 FP ly S W memS md own ly2 S2 W2 mem2 md2 k2 -> gagree G (w_H W) mem memS ->
  ajournal_gx SEGS B G 0 [] STK sp0 FP ly S W mem md own ly2 S2 W2 mem2 md2 k2.
Proof.
intros G STK sp0 FP ly S W mem md own ly2 S2 W2 mem2 md2 k2 memS HSTK HJ Hag.
eapply ajournal_gx_pack; [exact HSTK | lia | rewrite !Z.add_0_r; exact HJ | exact Hag |].
intros a Ha _. lia.
Qed.


(* ---- the next-call premise helpers (moved here from a Theorem Labs lane's PcapEntryOpen.v, text unchanged; nxF_pC and
   present_rdW are the lib/B twins of lib/A/Prog/PcapHarnessTail.v's lemmas of the same names) ---- *)

Lemma present_rdW : forall (H : word -> bool) mem a, apresent H mem a -> YO0d.present (mrestrict H mem) a.
Proof. intros H mem a (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.

(* The reader statement's view of the file (bytes from its Z list) is the harness's p_F. *)
Lemma nxF_pC : forall cx, AN.nxF (p_C cx) = p_F cx.
Proof.
  intros cx. unfold AN.nxF, bytesZ, p_C. rewrite map_map.
  rewrite (map_ext (fun x : byte => Z_to_bv 8 (bv_unsigned x)) (fun x => x)) by (intros x; apply Z_to_bv_bv_unsigned).
  apply map_id.
Qed.

(* The reader contract's view of the file (bytes from a list of Z) is the harness's p_F. *)
Lemma k3_nxF : forall cx, AN.nxF (p_C cx) = p_F cx.
Proof.
intros cx. unfold AN.nxF, bytesZ, p_C. rewrite map_map.
rewrite (map_ext (fun x : byte => Z_to_bv 8 (bv_unsigned x)) (fun x => x)) by (intros x; apply Z_to_bv_bv_unsigned).
apply map_id.
Qed.

(* The model's last-header slot: a `chain` that stops at a header that fits stopped BECAUSE of that header, so it
   left its position in lh. (With no fuel the chain stops anywhere, so the fuel bound is a premise.) *)
Lemma k3_chain_lh : forall sw F cap fuel q lh, 0 <= cap ->
  Z.of_nat (length F) - q < 16 * Z.of_nat fuel -> q <= Z.of_nat (length F) ->
  PSN.kind sw F cap (fst (fst (PSN.chain sw F cap fuel q lh))) = PSN.KFit ->
  snd (PSN.chain sw F cap fuel q lh) = Some (fst (fst (PSN.chain sw F cap fuel q lh))).
Proof.
intros sw F cap fuel. induction fuel as [|f IH]; intros q lh Hcap Hfuel Hq Hk; [cbn in Hfuel; lia|].
cbn [PSN.chain] in Hk |- *. destruct (PSN.kind sw F cap q) eqn:Ek.
- cbn [fst snd] in Hk. rewrite Ek in Hk. discriminate Hk.
- cbn [fst snd] in Hk. rewrite Ek in Hk. discriminate Hk.
- destruct (AN.nx_kind_empty sw F cap q Ek) as (_ & H16).
  apply (IH (q + 16) lh Hcap); [rewrite Nat2Z.inj_succ in Hfuel; lia | lia | exact Hk].
- reflexivity.
- reflexivity.
- reflexivity.
- destruct (AN.nx_kind_big sw F cap q Ek) as (Hi & _ & Hle & _).
  destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q o] l] eqn:EC.
  cbn [fst snd] in Hk |- *.
  pose proof (IH (q + 16 + PSN.incl sw F q) (Some q) Hcap
    ltac:(rewrite Nat2Z.inj_succ in Hfuel; lia) ltac:(lia)) as IH'.
  rewrite EC in IH'. cbn [fst snd] in IH'. exact (IH' Hk).
- reflexivity.
Qed.

Lemma k3_lh_fit : forall sw F cap p, 0 <= cap -> 0 <= p <= Z.of_nat (length F) ->
  PSN.kind sw F cap (PSN.psn_q sw F cap p) = PSN.KFit ->
  PSN.psn_lh sw F cap p = Some (PSN.psn_q sw F cap p).
Proof.
intros sw F cap p Hcap Hp Hk. unfold PSN.psn_q, PSN.psn_lh, PSN.psn_chain in *.
apply (k3_chain_lh sw F cap (S (length F)) p None Hcap); [rewrite Nat2Z.inj_succ; lia | lia | exact Hk].
Qed.

(* A byte the journal says is present reads back through the world's filter. *)
Lemma k3_present : forall (H : word -> bool) mem a, apresent H mem a -> YO0d.present (mrestrict H mem) a.
Proof. intros H mem a (Hh & b & Hb). exists b. unfold mrestrict. rewrite Hh. exact Hb. Qed.

(* Four present bytes hold SOME 32-bit value: the harness never states ps.last_orig_len and the two VLAN fields at
   its cuts, but pcap_source_next's contract needs a value for each. *)
Lemma k3_vm4 : forall (m : word -> option byte) a,
  YO0d.present m a -> YO0d.present m (a + 1) -> YO0d.present m (a + 2) -> YO0d.present m (a + 3) ->
  exists v, 0 <= v < 2 ^ 32 /\ val_mem SEGS m a 4 v.
Proof.
intros m a [b0 Hb0] [b1 Hb1] [b2 Hb2] [b3 Hb3].
pose proof (bv_unsigned_in_range _ b0) as Hr0. pose proof (bv_unsigned_in_range _ b1) as Hr1.
pose proof (bv_unsigned_in_range _ b2) as Hr2. pose proof (bv_unsigned_in_range _ b3) as Hr3.
change (bv_modulus 8) with 256 in Hr0, Hr1, Hr2, Hr3.
set (v := bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3).
exists v. split; [unfold v; change (2 ^ 32) with 4294967296; lia|].
assert (Hm : v mod 2 ^ (8 * Z.of_nat 4) = v)
  by (apply Z.mod_small; replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 by reflexivity; unfold v; lia).
intros kk Hk. unfold YO0f.le_byte. rewrite Hm. unfold mbyte.
destruct kk as [|[|[|[|kk]]]]; [| | | |lia].
- replace (a + Z.of_nat 0) with a by lia. rewrite Hb0. f_equal.
  replace (8 * Z.of_nat 0) with 0 by reflexivity. rewrite Z.shiftr_0_r.
  replace v with (bv_unsigned b0 + (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) * 256)
    by (unfold v; lia).
  rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
- replace (a + Z.of_nat 1) with (a + 1) by lia. rewrite Hb1. f_equal.
  replace (8 * Z.of_nat 1) with 8 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  replace v with (bv_unsigned b0 + (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3) * 256)
    by (unfold v; lia).
  rewrite Z.div_add, Z.div_small, Z.add_0_l by lia.
  replace (bv_unsigned b1 + 256 * bv_unsigned b2 + 65536 * bv_unsigned b3)
    with (bv_unsigned b1 + (bv_unsigned b2 + 256 * bv_unsigned b3) * 256) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
- replace (a + Z.of_nat 2) with (a + 2) by lia. rewrite Hb2. f_equal.
  replace (8 * Z.of_nat 2) with 16 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 16) with 65536.
  replace v with (bv_unsigned b0 + 256 * bv_unsigned b1 + (bv_unsigned b2 + 256 * bv_unsigned b3) * 65536)
    by (unfold v; lia).
  rewrite Z.div_add, Z.div_small, Z.add_0_l by lia.
  replace (bv_unsigned b2 + 256 * bv_unsigned b3) with (bv_unsigned b2 + bv_unsigned b3 * 256) by lia.
  rewrite Z_mod_plus_full, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
- replace (a + Z.of_nat 3) with (a + 3) by lia. rewrite Hb3. f_equal.
  replace (8 * Z.of_nat 3) with 24 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 24) with 16777216.
  replace v with (bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + bv_unsigned b3 * 16777216)
    by (unfold v; lia).
  rewrite Z.div_add, Z.div_small, Z.add_0_l, Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- pcap_source_close (0x80e34, 0x80e70) ---- *)
(* TAKEN FROM: lib/A/Prog/PcapSourceCloseSpec.v tpcap_source_close_specX (a Theorem Labs lane); its asan-ubsan instance is
   proved in lib/B/Prog/PcapSourceClose.v (pb_pcap_source_closeX, this branch). *)
Lemma close_call : forall (HCLOSE : AC.tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B KS MT
                                      (BASE + AF_pcap_source_close))
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (ps f b M p : Z) (C : list Z) (cid pos : Z),
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ps ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - AC.TPCAP_SOURCE_CLOSE_STK -> spZ regs <= sp0 ->
  In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + 8 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  ps <> 0 /\ ps mod 8 = 0 ->
  val_mem SEGS (rdW W memc) ps 8 f -> 0 <= f < 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 8 ->
  (f <> 0 ->
     In (f, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\ In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
     asource_at SEGS KS (rdW W memc) f b C p /\ asrc_meta_inv SEGS KS lyc (rdW W memc) M /\
     (forall x, inFP (asource_fp f) x -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x)) ->
  st_nev Sc + AC.EV_CLOSE <= EV_MAX ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_pcap_source_close) regs memc mdc)
    (fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + AC.EV_CLOSE) /\
       aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
       mo_le MT Sc S2 (if f =? 0 then 0 else mo_free MT + mo_free MT) /\
       m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
       Permutation (ablocks B lyc Sc) (AC.tclose_fblk f ++ ablocks B ly2 S2) /\
       val_mem SEGS (rdW W2 mem2) ps 8 0 /\
       AC.tclose_kept SK SEGS B lyc Sc W memc W2 mem2 (spZ regs - AC.TPCAP_SOURCE_CLOSE_STK) (spZ regs)
         (fun a => (ps <= a < ps + 8) \/ (f <> 0 /\ f <= a < f + req_size SRC_FILE_BLOCK)) /\
       (f <> 0 -> asource_none SEGS KS (rdW W2 mem2) /\ garr8 SEGS (rdW W2 mem2) b C)).
Proof.
intros HCLOSE STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps f b M p C cid pos
  HJ HROD Hraw Hra4 Hgp Htp H10 Hal16 Hwlo Hwhi Hown Hfa1 Hfa2 Hps Hfv Hf64 Hsh Hstream Hev.
destruct (gx_open pe_G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (HCLOSE STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k regs ps f b M p C cid pos
    HJi HROD Hraw Hra4 Hgp Htp H10 Hal16 Hwlo Hwhi Hown Hfa1 Hfa2 Hps Hfv Hf64 Hsh Hstream Hev). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP & Hfrs & HMO & HFD & HFS & HPm & HV & HK & HSN).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [exact (gx_pack0 pe_G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 _ memS HSTK HJ2 Hag)|].
split; [exact HP|]. split; [exact Hfrs|]. split; [exact HMO|]. split; [exact HFD|]. split; [exact HFS|].
split; [exact HPm|]. split; [exact HV|]. split; [exact HK | exact HSN].
Qed.


(* ---- pcap_source_open (0x80a0c, 0x80e4c) ---- *)
(* TAKEN FROM: lib/A/Prog/PcapSourceOpenDefs.v tpcap_source_open_specX (a Theorem Labs lane, the post with one journal bound per
   arm, a working branch da7eb5095c2); its asan-ubsan instance is a Theorem Labs lane's. The post is the
   contract's, with each arm's donor journal replaced by the harness's gx journal. *)
Definition open_post_gx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (ps b : Z) (C : list Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  AO.topen_kept SK SEGS B lyc Sc W memc W2 mem2 (spZ regs - AO.TPCAP_SOURCE_OPEN_STK) (spZ regs)
    (fun a => ps <= a < ps + 22) /\
  mo_le MT Sc S2 (AO.OPEN_METER MT) /\
  val_mem SEGS (rdW W2 mem2) (ps + 12) 4 0 /\ val_mem SEGS (rdW W2 mem2) (ps + 16) 4 0 /\
  val_mem SEGS (rdW W2 mem2) (ps + 20) 2 0 /\
  ((ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + AF.EV_FUZZ_FOPEN) /\
    getr regs2 10 = w64 0 /\ AO.pcap_goodZ C = true /\
    (exists f, 4096 <= f /\ f mod 16 = 0 /\
       ablocks B ly2 S2 = ablocks B lyc Sc ++ [(f, SRC_FILE_BLOCK)] /\
       val_mem SEGS (rdW W2 mem2) ps 8 f /\ val_mem SEGS (rdW W2 mem2) (ps + 8) 4 (AO.pcap_swZ C) /\
       asource_at SEGS KS (rdW W2 mem2) f b C 24 /\
       mo_le MT Sc S2 (mo_malloc MT SRC_FILE_BLOCK)))
   \/
   (ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + AO.EV_OPEN) /\
    getr regs2 10 = w64 (-1) /\ AO.pcap_goodZ C = false /\
    val_mem SEGS (rdW W2 mem2) ps 8 0 /\
    (forall i, 8 <= i < 12 -> aview SEGS (w_H W2) mem2 (ps + i) = aview SEGS (w_H W) memc (ps + i)) /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    asource_none SEGS KS (rdW W2 mem2))).

Lemma open_call : forall (apath alen afile : Z) (roimg : (word -> option byte) -> Prop) (FM_RA : Z) (CTX : list (list Z))
    (HOPEN : AO.tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi apath alen afile roimg B KS MT FM_RA CTX
               (BASE + AF_pcap_source_open))
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word) ch
    (ps n b M : Z) (C : list Z) (cid pos : Z),
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ps -> getr regs 11 = w64 apath ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - AO.TPCAP_SOURCE_OPEN_STK -> spZ regs <= sp0 ->
  spZ regs + 32 <= ly_top lyc -> Z.of_nat (length (frames Sc)) <= 7 ->
  In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  ps <> 0 -> ps mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 ->
  inFP FP 0 ->
  roimg (rdW W memc) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF apath 13 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) apath 13 ->
  val_mem SEGS (rdW W memc) alen 8 n -> val_mem SEGS (rdW W memc) afile 8 b ->
  0 <= b < 2 ^ 64 ->
  asource_none SEGS KS (rdW W memc) ->
  n = Z.of_nat (length C) -> n < 2 ^ 26 ->
  (1 <= n -> In (b, n) (ablocks B lyc Sc) /\ garr8 SEGS (rdW W memc) b C /\ bytes_ok C) ->
  asrc_meta_inv SEGS KS lyc (rdW W memc) M ->
  st_nev Sc + AO.EV_OPEN <= EV_MAX -> blocks_bytes Sc + SRC_FILE_BLOCK <= LIVE_MAX ->
  mo_ok MT Sc (mo_malloc MT SRC_FILE_BLOCK) ->
  In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_pcap_source_open) regs memc mdc)
    (open_post_gx STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps b C).
Proof.
intros apath alen afile roimg FM_RA CTX HOPEN STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch
  ps n b M C cid pos HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24
  H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37.
destruct (gx_open pe_G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (HOPEN STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k regs ch ps n b M C cid pos
    HJi H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24
    H25 H26 H27 H28 H29 H30 H31 H32 H33 H34 H35 H36 H37). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP & Hfrs & HFD & HFS & HK & HMO & V12 & V16 & V20 & Harms).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
do 9 (split; [assumption|]).
destruct Harms as [(HJ2 & Hrest) | (HJ2 & Hrest)]; [left | right];
  (split; [exact (gx_pack0 pe_G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 _ memS HSTK HJ2 Hag) | exact Hrest]).
Qed.

(* ---- pcap_source_next (0x80b00, 0x80db8, 0x80e64, 0x80e84) ---- *)
(* TAKEN FROM: lib/A/Prog/PcapSourceNextSpec.v tpcap_source_next_specX (a Theorem Labs lane, image-free, blob ca692a132f5e;
   the statement of a working branch cf12207f2a1); nstk is the image's stack datum (the caller passes this image's value). The post is the contract's
   with its donor journal replaced by the harness's gx journal. *)
Definition next_post_gx (nstk : Z) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (ps buf cap ts h b p sw lol lvt lvid tsv : Z)
  (C bj pad : list Z) : world SEGS -> config -> Prop :=
fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + AN.EV_NEXT) /\
  aregs_preserved regs regs2 /\
  ablocks B ly2 S2 = ablocks B lyc Sc /\ frames S2 = frames Sc /\
  mo_le MT Sc S2 0 /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  AN.nx_fin SEGS nstk B KS lyc Sc W memc (spZ regs) ps buf cap ts h b p sw lol lvt lvid tsv C bj pad W2 mem2
    (getr regs2 10).

Lemma next_call : forall (nstk : Z)
    (HNEXT : AN.tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi nstk B MT KS (BASE + AF_pcap_source_next))
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world SEGS) memc mdc k (regs : bvmap 5 word)
    (ps buf cap ts h b p sw lol lvt lvid tsv M cid pos : Z) (C bj pad : list Z) (ch : list (Z * Z * Z)),
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ps -> getr regs 11 = w64 buf -> getr regs 12 = w64 cap -> getr regs 13 = w64 ts ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - nstk -> spZ regs <= sp0 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  count_cid AN.NX_CID (frames Sc) < fs_frames AN.NX_CID ->
  val_mem SEGS (rdW W memc) (ps + AN.PS_F_OFF) 8 h -> 0 <= h < 2 ^ 64 ->
  ps mod 8 = 0 -> 4096 <= ps -> ps + AN.PS_LEN <= 2 ^ 47 -> amem_range ps AN.PS_LEN ->
  In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + AN.PS_LEN <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps AN.PS_LEN ->
  (h <> 0 -> AN.nx_ps_at SEGS (rdW W memc) ps h sw lol lvt lvid pad) ->
  (h <> 0 -> sw = 0 \/ sw = 1) ->
  (h <> 0 -> 0 <= lol < 2 ^ 32 /\ 0 <= lvt < 2 ^ 32 /\ 0 <= lvid < 2 ^ 16) ->
  (h <> 0 -> AN.nx_wr_ok nstk B STK sp0 FP ly S lyc Sc own (spZ regs) ps AN.PS_LEN) ->
  (h <> 0 ->
     In (buf, AN.nx_bufn cap) (ablocks B lyc Sc) /\
     4096 <= buf /\ buf + AN.nx_bufn cap < 2 ^ 63 /\
     garr8 SEGS (rdW W memc) buf bj /\ Z.of_nat (length bj) = AN.nx_bufn cap /\
     0 <= cap <= AN.NX_CAP_MAX /\
     AN.nx_wr_ok nstk B STK sp0 FP ly S lyc Sc own (spZ regs) buf (AN.nx_bufn cap) /\
     (buf + AN.nx_bufn cap <= ps \/ ps + AN.PS_LEN <= buf)) ->
  (h <> 0 -> ts <> 0 ->
     val_mem SEGS (rdW W memc) ts 8 tsv /\ ts mod 8 = 0 /\ 4096 <= ts /\ ts + 8 <= 2 ^ 47 /\
     amem_range ts 8 /\
     (exists tcid tpos, In (tcid, tpos) own /\ frame_addr lyc tcid tpos <= ts /\
        ts + 8 <= frame_addr lyc tcid tpos + fs_frame_bytes tcid) /\
     AN.nx_wr_ok nstk B STK sp0 FP ly S lyc Sc own (spZ regs) ts 8 /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ts 8 /\
     (ts + 8 <= ps \/ ps + AN.PS_LEN <= ts) /\ (buf + AN.nx_bufn cap <= ts \/ ts + 8 <= buf)) ->
  (h <> 0 ->
     In (h, SRC_FILE_BLOCK) (ablocks B lyc Sc) /\
     In (b, Z.of_nat (length C)) (ablocks B lyc Sc) /\
     asource_at SEGS KS (rdW W memc) h b C p /\
     Z.of_nat (length C) < 2 ^ 26 /\ 0 <= p <= Z.of_nat (length C) /\
     (buf + AN.nx_bufn cap <= h \/ h + SRC_FILE_BLOCK <= buf) /\
     (buf + AN.nx_bufn cap <= b \/ b + Z.of_nat (length C) <= buf) /\
     (ps + AN.PS_LEN <= h \/ h + SRC_FILE_BLOCK <= ps) /\
     (ps + AN.PS_LEN <= b \/ b + Z.of_nat (length C) <= ps) /\
     (ts <> 0 -> (ts + 8 <= h \/ h + SRC_FILE_BLOCK <= ts) /\ (ts + 8 <= b \/ b + Z.of_nat (length C) <= ts)) /\
     (forall x, inFP (asource_fp h) x -> inFP FP x \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) x)) ->
  (h <> 0 -> asrc_meta_inv SEGS KS lyc (rdW W memc) M) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_pcap_source_next) regs memc mdc)
    (next_post_gx nstk STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
       ps buf cap ts h b p sw lol lvt lvid tsv C bj pad).
Proof.
intros nstk HNEXT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
  ps buf cap ts h b p sw lol lvt lvid tsv M cid pos C bj pad ch
  HJ H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 H28 H29
  H30 H31 H32.
destruct (gx_open pe_G STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (HNEXT STK sp0 FP ly S W0 memS md0 own lyc Sc W memc mdc k regs ps buf cap ts h b p sw lol lvt lvid tsv
    M cid pos C bj pad ch HJi H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23
    H24 H25 H26 H27 H28 H29 H30 H31 H32). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Hrest).
exists ly2, S2, regs2, mem2, md2. split; [reflexivity|].
split; [exact (gx_pack0 pe_G STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 _ memS HSTK HJ2 Hag) | exact Hrest].
Qed.

(* ---- the harness's intrinsic calls: __asan_memcpy (0x809d8) and __asan_memset (0x809fc) ---- *)
(* TAKEN FROM: the runtime rule aintrin_realizes (Reusable/YG0d.v:318, cgif's) through lib/A/Prog/YC85G.v
   aj_intrin_atS, which is already in the caller-journal form; the lift is gx_open / gx_pack0. *)
Lemma intrin_call : forall op pc, aintrin_realizes SEGS B op pc ->
  forall (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n (o : Z) raw,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
  getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n -> 0 <= n < 2 ^ 32 -> 0 <= d -> d + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  (forall a, d <= a < d + n -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
                               ~ (sp0 + o - ESTACK <= a < sp0 + o)) ->
  amem_range d n ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF d n ->
  (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) d n) ->
  (match op with
   | OCpy => 0 <= x /\ x + n <= 2 ^ 63 /\ src_ok SEGS W regsT memT x n /\ (d + n <= x \/ x + n <= d) /\ amem_range x n /\
             range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x n /\ (0 < n -> shadow_hull_vis (aview SEGS (w_H W) memT) x n)
   | OSet => True end) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 d /\
       (forall i, 0 <= i < n -> aview SEGS (w_H W) mem2 (d + i) =
          match op with OCpy => aview SEGS (w_H W) memT (x + i) | OSet => Some (x mod 256) end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (sp0 + o - ESTACK <= a < sp0 + o) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a) /\
       (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) /\
       same_but_materialized mdc md2).
Proof.
intros op pc HAI W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k d x n o raw HJ
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19.
destruct (gx_open pe_G STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k HJ) as (memS & HJi & Hag & HSTK).
eapply SRr_mono.
{ exact (YC85G.aj_intrin_atS SEGS B LAWS pa_segs_low op pc HAI W regsT memT STK sp0 FP ly S W0 memS md own lyc Sc mdc
    k d x n o raw HJi H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & Hrest).
split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|].
split; [exact (gx_pack0 pe_G STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 _ memS HSTK HJ2 Hag) | exact Hrest].
Qed.

(* The two named sites (a Theorem Labs lane's 0x809d8 / 0x809fc). *)
Definition memcpy_call (pc : Z) (HI : aintrin_realizes SEGS B OCpy pc) := intrin_call OCpy pc HI.
Definition memset_call (pc : Z) (HI : aintrin_realizes SEGS B OSet pc) := intrin_call OSet pc HI.

End c.
End b.
End a.
(* The sink head is EXPLICIT on every exported lemma (a Theorem Labs lane 21:57Z). *)
Arguments gx_open {rc} SK {PI} B G.
Arguments gx_pack0 {rc} SK {PI} B G.
Arguments close_call {fx rc} SK {PI} B MT KS HCLOSE.
Arguments open_post_gx {fx rc} SK {PI} B MT KS.
Arguments open_call {fx rc} SK {PI} B MT KS apath alen afile roimg FM_RA CTX HOPEN.
Arguments next_post_gx {fx rc} SK {PI} B MT KS nstk.
Arguments next_call {fx rc} SK {PI} B MT KS nstk HNEXT.
Arguments intrin_call {fx rc} SK {PI} B LAWS op pc.
Arguments memcpy_call {fx rc} SK {PI} B LAWS pc HI.
Arguments memset_call {fx rc} SK {PI} B LAWS pc HI.
