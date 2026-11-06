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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases Rd32.
(* the walk kit shared by the lanes of this harness (a Theorem Labs lane): one home for the model and keep lemmas *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalkDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* lib/A/AE2f.v (in this closure) turns off zify's euclidean division; the bounds below need it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module PWD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalkDef.

(* ---- the symbolic state of a stretch: the spill slots as one region based at s1 (atom 9) ---- *)
Definition SB_W : Z := 0x7fff8000.
Definition WBx : sv := SOff 32 0.
Definition Wspan : Z * Z := (SB_W, SB_W + 2 ^ 44 - 1).
Definition slots_region (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 9%nat) 16 152 16 152 cs.
Definition w3_facts (l : list (nat * afact)) (cds : list acond) : facts :=
  mkFacts ((32%nat, mkAF SB_W SB_W 0) :: (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) :: l) cds [].
Definition glen_region (v : sv) : YP09.region := YP09.mkRegion (Some (A_OBJ 4)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 v)].

(* The atoms a stretch adds beyond the registers (32 + j): the shadow base, the three blocks, the sizes, the
   frame and its shadow, and the three loop words. *)
Definition w3_extra (b h buf cap len d F SH first calls n : Z) : list word :=
  map (Z_to_bv 64) [SB_W; b; h; buf; cap; len; d; F; SH; first; calls; n].
Definition cs_base : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
   YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 8 (SOff 40 0));
   YP09.mkChunk 72 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 88 (CVal 8 (SOff 39 96));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 120 (CVal 8 (SOff 36 0));
   YP09.mkChunk 144 (CVal 8 (SOff 39 0))].



(* PP_K4's slots: the record loop's constants are set, `first` is not yet stored. *)
Definition cs_K4 : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
   YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 8 (SOff 40 0));
   YP09.mkChunk 48 (CVal 8 (SLit 3840)); YP09.mkChunk 56 (CVal 8 (SOff 35 12));
   YP09.mkChunk 64 (CVal 8 (SLit 4294967296000000));
   YP09.mkChunk 72 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 88 (CVal 8 (SOff 39 96));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 104 (CVal 8 (SOff 42 0));
   YP09.mkChunk 112 (CVal 8 (SOff 43 0)); YP09.mkChunk 120 (CVal 8 (SOff 36 0));
   YP09.mkChunk 144 (CVal 8 (SOff 39 0))].
(* The ranges the three UBSan guards and the `beqz s2` of the stretch need. *)
Definition fl_K4 : list (nat * afact) :=
  [(18%nat, mkAF 4096 140737479966720 0); (23%nat, mkAF (2 ^ 26) (2 ^ 64 - 1) 0);
   (26%nat, mkAF 0 (2 ^ 26) 0); (36%nat, mkAF 0 2040 0); (37%nat, mkAF 24 (2 ^ 26) 0);
   (42%nat, mkAF 0 (2 ^ 26) 0); (43%nat, mkAF 1 2040 0)].
(* The three abort tests of the stretch, as conditions the walk proves once: the calls bound (0x80b50), n <= cap
   (0x80b70) and at + 16 <= g_file_len (0x80b7c); and the UBSan guard 0x80b80 (file <> NULL). *)
Definition cds_K4 : list acond :=
  [mkAC BC_LTU (SOff 42 0) (SAlu ALU_SRL (SOff 37 (-24)) (SLit 4));
   mkAC BC_GEU (SOff 36 0) (SOff 43 0);
   mkAC BC_GEU (SOff 37 0) (SOff 26 16);
   mkAC BC_NE (SOff 18 0) (SLit 0)].

Definition w3_extra2 (b h buf cap len d F SH first calls n swz orig : Z) : list word :=
  map (Z_to_bv 64) [SB_W; b; h; buf; cap; len; d; F; SH; first; calls; n; swz; orig].
Definition ps_region (v8 v12 : sv) : YP09.region :=
  YP09.mkRegion (Some 20%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 4 v8); YP09.mkChunk 12 (CVal 4 v12)].
Definition cs_KR : list YP09.chunk :=
  [YP09.mkChunk 16 (CVal 8 (SOff 39 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0));
   YP09.mkChunk 32 (CVal 8 (SOff 39 0)); YP09.mkChunk 40 (CVal 8 (SOff 40 0));
   YP09.mkChunk 48 (CVal 8 (SLit 3840)); YP09.mkChunk 56 (CVal 8 (SOff 35 12));
   YP09.mkChunk 64 (CVal 8 (SLit 4294967296000000));
   YP09.mkChunk 72 (CVal 8 (SLit SHADOW_OFF)); YP09.mkChunk 80 (CVal 8 (SOff 41 0));
   YP09.mkChunk 88 (CVal 8 (SOff 39 96));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 104 (CVal 8 (SOff 42 0));
   YP09.mkChunk 112 (CVal 8 (SOff 43 0)); YP09.mkChunk 120 (CVal 8 (SOff 36 0));
   YP09.mkChunk 144 (CVal 8 (SOff 39 0))].
Definition fl_KR : list (nat * afact) :=
  [(18%nat, mkAF 4096 140737479966720 0); (20%nat, mkAF 4096 140737479966720 0);
   (21%nat, mkAF (2 ^ 64 - 8) (2 ^ 64 - 8) 0); (23%nat, mkAF (2 ^ 26) (2 ^ 64 - 1) 0);
   (26%nat, mkAF 0 (2 ^ 26) 0); (44%nat, mkAF 0 1 0)].
Definition ss_KR : sstate := mkSS PP_KR (sr_set sr_atoms (24%bv : bv 5) (SOff (A_HI 8) 0))
  [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0)] None (w3_facts fl_KR []).

(* ---- KRI -> KR (a skipped record) / KO (the fit one) ---- *)
Definition fl_KRI : list (nat * afact) :=
  [(18%nat, mkAF 4096 140737479966720 0); (19%nat, mkAF 4096 140737479966720 0);
   (20%nat, mkAF 4096 140737479966720 0); (21%nat, mkAF (2 ^ 64 - 8) (2 ^ 64 - 8) 0);
   (23%nat, mkAF (2 ^ 26) (2 ^ 64 - 1) 0); (26%nat, mkAF 0 (2 ^ 26) 0);
   (36%nat, mkAF 0 2040 0); (37%nat, mkAF 24 (2 ^ 26) 0); (44%nat, mkAF 0 1 0)].
Definition W3ZX : sv := SAlu ALU_SRL (SAlu ALU_SLL (SOff 46 0) (SLit 32)) (SLit 32).
Definition cds_empty : list acond :=
  [mkAC BC_EQ (SOff 46 0) (SLit 0); mkAC BC_GEU (SOff 37 0) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 26 0) W3ZX) (SLit 32))].
Definition cds_big : list acond :=
  [mkAC BC_NE (SOff 46 0) (SLit 0); mkAC BC_LTU (SOff 36 0) W3ZX;
   mkAC BC_GEU (SOff 37 0) (SAlu ALU_ADD (SAlu ALU_ADD (SOff 26 0) W3ZX) (SLit 32))].
Definition cds_fit : list acond :=
  [mkAC BC_NE (SOff 46 0) (SLit 0); mkAC BC_GEU (SOff 36 0) W3ZX;
   mkAC BC_GEU (SOff 37 0) (SAlu ALU_ADD (SOff 22 0) W3ZX)].
Definition w3_extra3 (b h buf cap len d F SH first calls n swz orig rdv : Z) : list word :=
  map (Z_to_bv 64) [SB_W; b; h; buf; cap; len; d; F; SH; first; calls; n; swz; orig; rdv].
Definition sr_KRI : list sv := sr_set (sr_set sr_atoms (24%bv : bv 5) (SOff (A_HI 8) 0)) (10%bv : bv 5) (SOff 46 0).

(* The write obligation of a stretch whose regions are the spill slots (based at s1, atom 9) and read-only
   image cells: every written byte is a byte of the caller's own machine frame. *)
Ltac w3_awr Ebase :=
  apply awr_ok_x_of0;
  cbn [ss_mem]; try unfold slots_region; try unfold glen_region; try unfold ps_region;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply awr_ok_cons_gen;
    [reflexivity | exact Ebase | cbn [YP09.r_wlo YP09.r_whi]; intros ?a ?Ha; left;
     change LLVMF_STK with 32768; lia |] ].


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).

(* A cut predicate at a bound m on |F| - s10 (s10 = at, e or Q at every cut of the record loop). *)
Definition pe_meas
  (GI : ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) (m : Z) :
  ecx -> Z -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
  fun cx fp k acc ly3 S3 W3 ms3 md3 =>
    GI cx fp k acc ly3 S3 W3 ms3 md3 /\ p_nF cx - bv_unsigned (getr (ms_regs ms3) 26) <= m.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- what every stretch uses ---- *)

(* The realigned stack pointer: where it sits, from pe_base and the journal. *)
Lemma w3_sp1 : forall cx fp ly3 S3 W3 (ms3 : machine_state) md3 k,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  spZ (c_regs cx) - 272 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0 /\
  alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 /\
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a).
Proof.
intros cx fp ly3 S3 W3 ms3 md3 k HB HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
destruct HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
rewrite !Z.add_0_r in Hstk, Hpres.
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HF : LLVMF_STK = 32768) by reflexivity.
set (sp0 := spZ (c_regs cx)) in *.
assert (Hq : sp0 - 272 <= pe_sp1 sp0 <= sp0 - 256 /\ pe_sp1 sp0 mod 32 = 0).
{ unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (sp0 - 256) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (sp0 - 256) 32 ltac:(lia)) as Dm.
  split; [lia|]. replace (32 * ((sp0 - 256) / 32)) with (((sp0 - 256) / 32) * 32) by lia. apply Z_mod_mult. }
rewrite Hsp1. split; [tauto|]. split; [tauto|]. split; [lia|]. split; [lia|].
intros a Ha. apply Hpres. lia.
Qed.

Lemma w3_chunk_slot : forall E (W3 : world SEGS) (ms3 : machine_state) cx off e v,
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> pslot cx W3 ms3 off v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx) (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E W3 ms3 cx off e v He Hv Hs.
apply (chunk_ok_val SEGS E _ (c_sp1 cx) off 8 e v He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)).
exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ Hs).
Qed.

Lemma w3_slots_ok : forall E (W3 : world SEGS) (ms3 : machine_state) cx cs,
  bv_unsigned (ew E 9%nat) = c_sp1 cx ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 ->
  (forall a, c_sp1 cx + 16 <= a < c_sp1 cx + 152 -> apresent (w_H W3) (ms_mem ms3) a) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) cs ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (slots_region cs).
Proof.
intros E W3 ms3 cx cs H9 Hr Hp Hcs.
unfold slots_region, region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H9. split; [lia|]. split; [lia|]. split; [|exact Hcs].
intros o Ho. apply (apresent_writable SEGS). apply Hp. lia.
Qed.

Lemma w3_facts_ok : forall E cx l cds,
  ew E 32%nat = w64 SB_W -> bv_unsigned (ew E 9%nat) = c_sp1 cx ->
  2 ^ 46 <= c_sp1 cx <= 2 ^ 47 -> c_sp1 cx mod 32 = 0 ->
  atoms_ok E l -> conds_ok E cds -> facts_ok E (w3_facts l cds).
Proof.
intros E cx l cds H32 H9 Hr Hal Hl Hc.
unfold w3_facts, facts_ok. cbn [f_atoms f_conds f_alias alias_ok].
split; [|split; [exact Hc | exact I]].
cbn [atoms_ok].
split; [unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite H32, unsigned_lit_small by (unfold SB_W; lia);
        unfold SB_W; rewrite Z.pow_0_r, Z.mod_1_r; lia|].
split; [|exact Hl].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H9. change (2 ^ 5) with 32. lia.
Qed.

(* ---- what a stretch keeps: every byte outside [sp1 - 16, sp1 + 152) ---- *)
Definition w3_keep (sp1 : Z) (W3 : world SEGS) (m m' : word -> option byte) : Prop :=
  PcapEntryKit.mk W3 m m' (sp1 - 16) (sp1 + 152).

Lemma w3_rdword_fr : forall (H : word -> bool) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview SEGS H m' x = aview SEGS H m x) ->
  rdword (aview SEGS H m) a = Some v -> rdword (aview SEGS H m') a = Some v.
Proof.
intros H m m' a v Hk Hv. unfold rdword in *.
rewrite (Hk a ltac:(lia)), (Hk (a+1) ltac:(lia)), (Hk (a+2) ltac:(lia)), (Hk (a+3) ltac:(lia)),
        (Hk (a+4) ltac:(lia)), (Hk (a+5) ltac:(lia)), (Hk (a+6) ltac:(lia)), (Hk (a+7) ltac:(lia)).
exact Hv.
Qed.

(* The bounds every phase's objects satisfy: the frame, its shadow and the caller's input lie below the
   allocator ceiling, and the ceiling lies below the spill slots. *)
Lemma w3_bounds : forall cx fp ly3 S3 W3 (ms3 : machine_state) md3 k,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  4096 <= pF cx fp /\ pF cx fp + 128 <= alloc_ceiling /\
  0 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling /\
  0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling /\
  alloc_ceiling <= c_sp1 cx - 16 /\ spZ (c_regs cx) - 272 <= c_sp1 cx /\ c_sp1 cx + 152 <= spZ (c_regs cx) - 104 /\
  spZ (c_regs cx) <= 2 ^ 47 /\ 2 ^ 46 <= c_sp1 cx <= 2 ^ 47 /\ c_sp1 cx mod 32 = 0 /\
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> apresent (w_H W3) (ms_mem ms3) a) /\
  AR SEGS B ly3 S3 W3 (ms_mem ms3) md3 /\ In (PE_CID, fp) (frames S3) /\
  frame_addr ly3 PE_CID fp = pF cx fp /\ (pF cx fp + 128 <= 65536 \/ pcap_img_end <= pF cx fp).
Proof.
intros cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (w3_sp1 cx fp ly3 S3 W3 ms3 md3 k HB HJ) as (Hd & Hal32 & Hsp0 & Hsp1r & Hpres).
pose proof HB as (HPRE & _ & _ & _ & Hpn & Hgarr & Hfr0 & _).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (HAR3 & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HPRE as (HAR0 & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
assert (HEF : frame_addr ly3 PE_CID fp = pF cx fp).
{ unfold pF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hin) as (Hf1 & Hf2 & Hf3).
rewrite HEF in Hf1, Hf2, Hf3. change (fs_frame_bytes PE_CID) with 128 in Hf1, Hf2, Hf3.
assert (HSH : 0 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF.
  pose proof (Z.div_mod (pF cx fp) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (pF cx fp) 8 ltac:(lia)) as Dm. lia. }
assert (Hinp : 0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling).
{ destruct Hpn as [[Hn0 Hp0] | [Hn1 Hinb]].
  - rewrite Hn0, Hp0. unfold A_EMPTY. lia.
  - destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx) HAR0 Hinb)
      as (_ & Hb4096 & Hbceil & _ & _ & _ & Hn).
    pose proof (req_size_pos0 (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hpres|]. split; [exact HAR3|]. split; [exact Hin|]. split; [exact HEF|].
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR3 Hin) as Hoff.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff. rewrite HEF in Hoff.
change (fs_frame_bytes PE_CID) with 128 in Hoff. unfold pcap_img_end, YImgTop.IMG_TOP. lia.
Qed.

Lemma w3_keep_lo : forall sp1 (W3 : world SEGS) m m',
  w3_keep sp1 W3 m m' -> alloc_ceiling <= sp1 - 16 ->
  forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof. intros sp1 W3 m m' HK Hsp a Ha. pose proof asan_consts as (C1 & _). apply HK; lia. Qed.

Lemma w3_keep_trans : forall sp1 (W3 : world SEGS) m1 m2 m3,
  w3_keep sp1 W3 m1 m2 -> w3_keep sp1 W3 m2 m3 -> w3_keep sp1 W3 m1 m3.
Proof. intros sp1 W3 m1 m2 m3 H1 H2. exact (PcapEntryKit.mk_trans W3 m1 m2 m3 _ _ H1 H2). Qed.

Lemma w3_mbyte_lo : forall sp1 (W3 : world SEGS) m m',
  w3_keep sp1 W3 m m' -> alloc_ceiling <= sp1 - 16 ->
  forall a, 0 <= a < alloc_ceiling ->
    mbyte SEGS (mrestrict (w_H W3) m') a = mbyte SEGS (mrestrict (w_H W3) m) a.
Proof. intros sp1 W3 m m' HK Hsp a Ha. pose proof asan_consts as (C1 & _). exact (PcapEntryKit.mk_mbyte W3 m m' _ _ a HK ltac:(lia) ltac:(lia)). Qed.

Lemma w3_val_lo : forall sp1 (W3 : world SEGS) m m' a n v,
  w3_keep sp1 W3 m m' -> alloc_ceiling <= sp1 - 16 -> 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem SEGS (mrestrict (w_H W3) m) a n v -> val_mem SEGS (mrestrict (w_H W3) m') a n v.
Proof. intros sp1 W3 m m' a n v HK Hsp Ha Han Hv. pose proof asan_consts as (C1 & _). exact (PcapEntryKit.val_mem_keep W3 m m' (sp1 - 16) (sp1 + 152) a n v Hv HK ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma w3_garr_lo : forall sp1 (W3 : world SEGS) m m' a (l : list Z),
  w3_keep sp1 W3 m m' -> alloc_ceiling <= sp1 - 16 -> 0 <= a -> a + Z.of_nat (length l) <= alloc_ceiling ->
  garr8 SEGS (mrestrict (w_H W3) m) a l -> garr8 SEGS (mrestrict (w_H W3) m') a l.
Proof. intros sp1 W3 m m' a l HK Hsp Ha Hal Hg. pose proof asan_consts as (C1 & _). exact (PcapEntryKit.garr8_keep W3 m m' (sp1 - 16) (sp1 + 152) a l Hg HK ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma w3_rdword_lo : forall sp1 (W3 : world SEGS) m m' a v,
  w3_keep sp1 W3 m m' -> alloc_ceiling <= sp1 - 16 -> 0 <= a -> a + 8 <= alloc_ceiling ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof. intros sp1 W3 m m' a v HK Hsp Ha Han Hv. pose proof asan_consts as (C1 & _). exact (PcapEntryKit.rdword_keep W3 m m' (sp1 - 16) (sp1 + 152) a v Hv HK ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

(* The body facts carry across any stretch that writes only the spill slots (and a callee's 16-byte frame). *)
Lemma w3_body_keep : forall cx fp pc0 pc1 sh ly3 S3 W3 (ms3 : machine_state) md3 k (ms4 : machine_state),
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp pc0 W3 ms3 sh ->
  ms_pc_val ms4 = w64 (BASE + pc1) -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr -> pregs cx ms4 ->
  w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms4) ->
  pe_body cx fp pc1 W3 ms4 sh.
Proof.
intros cx fp pc0 pc1 sh ly3 S3 W3 ms3 md3 k ms4 HB HJ Hfrs HBody Hpc Hrv Hsvc Hrom Hfr Hfcsr Hregs HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
pose proof HBody as (_ & _ & _ & _ & _ & _ & (P2 & P8 & P9 & P3 & P4) & _).
destruct Hregs as (R2 & R8 & R9 & R3 & R4).
pose proof (w3_sp1 cx fp ly3 S3 W3 ms3 md3 k HB HJ) as (_ & _ & Hsp0 & _).
apply (PcapEntryKit.pe_body_keep cx fp pc0 pc1 W3 ms3 ms4 sh (c_sp1 cx - 16) (c_sp1 cx + 152) HBody
         Hpc Hrv Hsvc Hrom Hfr Hfcsr).
- rewrite R2, P2. reflexivity.
- rewrite R8, P8. reflexivity.
- rewrite R9, P9. reflexivity.
- rewrite R3, P3. reflexivity.
- rewrite R4, P4. reflexivity.
- exact HK.
- lia.
- lia.
- change LLVMF_STK with 32768. lia.
- lia.
- exact HF1.
- change PE_FRAME with 128. lia.
- right. split; lia.
Qed.

(* The record the reader hands back is never longer than its header's incl. *)
Lemma w3_rec_len : forall sw F q, 0 <= PSN.incl sw F q ->
  Z.of_nat (length (PSN.rec_bytes sw F q)) <= PSN.incl sw F q.
Proof. intros sw F q H. apply (PcapEntryKit.rec_bytes_len sw F q H). intros Ht. pose proof (PcapEntryKit.tagged_incl sw F q Ht). lia. Qed.

Lemma w3_C_len : forall cx, Z.of_nat (length (p_C cx)) = p_nF cx.
Proof. intros cx. exact (PcapEntryKit.p_lens cx). Qed.


Lemma w3_hw_range : forall sw F q j, 0 <= PSN.hw sw F q j < 2 ^ 32.
Proof. intros. apply PcapEntryKit.hw_range. Qed.


Lemma w3_fit : forall sw F cap q, PSN.kind sw F cap q = PSN.KFit ->
  0 < PSN.incl sw F q <= cap /\ q + 16 + PSN.incl sw F q <= PSN.flen F /\ 16 <= PSN.flen F - q.
Proof. intros sw F cap q HK. destruct (PcapEntryKit.kind_fit sw F cap q HK) as (H1 & H2 & H3 & H4). unfold PSN.flen. split; [lia | split; lia]. Qed.

(* The reader's state is kept by a stretch that writes only the spill slots. *)
Lemma w3_reader_keep : forall cx fp (W3 : world SEGS) (ms3 ms4 : machine_state) b h buf p,
  asource_img_laws SK SEGS B KS ->
  w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms4) -> alloc_ceiling <= c_sp1 cx - 16 ->
  0 <= b -> b + p_nF cx <= alloc_ceiling ->
  0 <= h -> h + SRC_FILE_BLOCK <= alloc_ceiling ->
  0 <= buf -> buf + p_bn cx <= alloc_ceiling ->
  4096 <= pF cx fp -> pF cx fp + 128 <= alloc_ceiling ->
  p_reader KS cx fp W3 ms3 b h buf p -> p_reader KS cx fp W3 ms4 b h buf p.
Proof. intros cx fp W3 ms3 ms4 b h buf p ASIL' HK Hac Hb0 Hb1 Hh0 Hh1 Hu0 Hu1 HF1 HF2 HR. exact (PcapEntryKit.p_reader_keep B KS ASIL' cx fp W3 ms3 ms4 (c_sp1 cx - 16) (c_sp1 cx + 152) b h buf p HR HK ltac:(lia) HF1 ltac:(change PE_FRAME with 128; lia) Hh0 Hh1 Hb0 Hb1 Hu0 Hu1). Qed.

(* The entry state of a stretch that starts at pc with the slot chunks cs. *)
Lemma w3_entry : forall cx fp pc sh rs l cds (ex : list word) ly3 S3 W3 (ms3 : machine_state) md3 k,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp pc W3 ms3 sh ->
  nth 0 ex (Z_to_bv 64 0) = Z_to_bv 64 SB_W ->
  regions_wf rs = true ->
  Forall (region_ok SEGS (Eimg (Ereg (ms_regs ms3) ex)) (mrestrict (w_H W3) (ms_mem ms3))) rs ->
  pairwise_disjoint (Eimg (Ereg (ms_regs ms3) ex)) rs ->
  atoms_ok (Eimg (Ereg (ms_regs ms3) ex)) l -> conds_ok (Eimg (Ereg (ms_regs ms3) ex)) cds ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) ex))
    (mkSS pc sr_atoms rs None (w3_facts l cds)) (restrict (w_H W3) ms3) /\
  sh_ok SEGS WBx [] (Eimg (Ereg (ms_regs ms3) ex)) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp pc sh rs l cds ex ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody H32 Hwf Hrs Hpd Hl Hcds.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
pose proof HBody as (Hpc & Hrv & Hsvc & Hrom & Hfreg & Hfcsr & Hregs & _).
pose proof Hregs as (_ & _ & R9 & _).
set (E := Eimg (Ereg (ms_regs ms3) ex)).
assert (E32 : ew E 32%nat = Z_to_bv 64 SB_W).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite <- H32. exact (ew_Ereg_extra (ms_regs ms3) ex 0). }
assert (E9 : bv_unsigned (ew E 9%nat) = c_sp1 cx).
{ subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat (ms_regs ms3) ex 9 (9%bv : bv 5) eq_refl), R9. apply unsigned_lit_small. lia. }
split; [|apply Forall_nil].
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (pa_val A_TEXT + pc)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in Hpc, Hrv, Hsvc, Hrom, Hfreg, Hfcsr |- *; subst; reflexivity. }
rewrite Hms at 1. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- exact Hwf.
- exact Hrs.
- exact Hpd.
- apply (w3_facts_ok E cx l cds); [exact E32 | exact E9 | lia | lia | exact Hl | exact Hcds].
Qed.

(* The run lemmas of W_journal's gx journal, at the lib/B kit (lib/A's paj_run_x is bound to lib/A's PAImg). *)
Definition w3_RUN (G : list (Z * Z)) (HG : gx_ok SEGS B G) (XO : Z) (OUT : list (Z * Z)) :=
  PcapEntryKit.bpaj_run_x B LAWS G HG XO OUT.
Definition w3_RUNTO (G : list (Z * Z)) (HG : gx_ok SEGS B G) (XO : Z) (OUT : list (Z * Z)) :=
  PcapEntryKit.bpaj_run_to_x B LAWS G HG XO OUT.

Lemma w3_good_len : forall cx, p_good cx = true -> 24 <= p_nF cx.
Proof.
intros cx HG. unfold p_good, PST.pcap_good in HG. apply andb_true_iff in HG as [HG _].
apply Z.leb_le in HG. unfold p_nF. exact HG.
Qed.

Lemma w3_res_pos : forall sw F cap q, PSN.kind sw F cap q = PSN.KFit -> 0 < PSN.res_of sw F cap q.
Proof. intros sw F cap q H. exact (PcapEntryKit.res_fit_pos sw F cap q H). Qed.

Lemma w3_res_range : forall sw F cap q, -1 <= PSN.res_of sw F cap q < 2 ^ 32.
Proof. intros sw F cap q. exact (PcapEntryKit.res_range sw F cap q). Qed.

Lemma w3_slot_of_region : forall E (W3 : world SEGS) (ms : machine_state) cx cs od e v,
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) (slots_region cs) ->
  bv_unsigned (ew E 9%nat) = c_sp1 cx ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  pslot cx W3 ms od v.
Proof.
intros E W3 ms cx cs od e v HR H9 Hin He Hv.
apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms) (c_sp1 cx + od) v); [|exact Hv].
exact (field_of_region E (mrestrict (w_H W3) (ms_mem ms)) 9%nat (c_sp1 cx) cs 16 152 16 152 od 8 e v
         HR H9 Hin He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv) ltac:(cbn; lia)).
Qed.

Lemma w3_region0 : forall E ss (ms : machine_state) (W3 : world SEGS) r,
  st_ok_pi SEGS pa_val E ss (restrict (w_H W3) ms) -> nth_error (ss_mem ss) 0 = Some r ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) r.
Proof.
intros E ss ms W3 r HS Hn.
pose proof (st_ok_region_nth E (abs_ss pa_val ss) (restrict (w_H W3) ms) 0 r HS Hn) as HR.
cbn [restrict ms_mem] in HR. exact HR.
Qed.

Lemma w3_shape : forall E ss (ms : machine_state) (W3 : world SEGS),
  st_ok_pi SEGS pa_val E ss (restrict (w_H W3) ms) -> ss_resv ss = None ->
  ms_pc_val ms = w64 (BASE + ss_pc ss) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof.
intros E ss ms W3 HS Hrv.
destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & _).
cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom abs_ss setpc ss_pc ss_resv] in A1, A2, A3, A4, A5, A6.
rewrite Hrv in A4. cbn [resv_denot] in A4.
repeat split; assumption.
Qed.

Lemma w3_signed_small : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z H. exact (PcapEntryKit.bsigned_w64 z H). Qed.

Lemma w3_bv_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
apply Zmod_mod.
Qed.

Lemma w3_lxor_ones : forall b, 0 <= b < 2 ^ 64 -> Z.lxor b (2 ^ 64 - 1) = 2 ^ 64 - 1 - b.
Proof.
intros b Hb. change (2 ^ 64 - 1) with (Z.ones 64).
assert (Hl : Z.ldiff b (Z.ones 64) = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.ldiff_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64) as [H|H].
  - rewrite Z.ones_spec_low by lia. apply andb_false_r.
  - rewrite <- (Z.mod_small b (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
rewrite (Z.sub_nocarry_ldiff (Z.ones 64) b Hl).
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.ldiff_spec.
destruct (Z.lt_ge_cases i 64) as [H|H].
- rewrite Z.ones_spec_low by lia. destruct (Z.testbit b i); reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small b (2 ^ 64)) by lia.
  rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

(* The value `not s2` (xori s2,-1 0x80b18) leaves when s2 = b. *)
Lemma w3_not_val : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = w64 (- b - 1).
Proof.
intros E n b Hn Hb. unfold w64. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SAlu ALU_XOR (SOff n 0) (SLit (-1))))) with (U E (SAlu ALU_XOR (SOff n 0) (SLit (-1)))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n b Hn Hb).
replace (U E (SLit (-1))) with (2 ^ 64 - 1) by (unfold U; cbn [sv_denot]; rewrite unsigned_lit; reflexivity).
rewrite w3_lxor_ones by exact Hb. unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (2 ^ 64 - 1 - b)) by lia. apply (Z.mod_unique _ _ (-1)); [left; lia | lia].
Qed.

Lemma w3_not_val' : forall E n b, ew E n = Z_to_bv 64 b -> 0 <= b < 2 ^ 64 ->
  alu64 ALU_XOR (ew E n) (Z_to_bv 64 (-1)) = w64 (- b - 1).
Proof.
intros E n b Hn Hb. rewrite <- (w3_not_val E n b Hn Hb). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
reflexivity.
Qed.

Lemma w3_res_fit_of_pos : forall sw F cap q, 0 < PSN.res_of sw F cap q -> PSN.kind sw F cap q = PSN.KFit.
Proof. intros sw F cap q H. exact (PcapEntryKit.res_pos_fit sw F cap q H). Qed.

Hypothesis TL : PALib B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Variable POST : ecx -> world SEGS -> config -> Prop.
#[local] Abbreviation PF := (pe_from SK B MT KS POST).

(* The three blocks every cut of the record loop holds, and their bounds. *)
Lemma w3_blocks3 : forall cx ly3 S3 W3 (ms3 : machine_state) md3 b h buf,
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
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as R1.
pose proof (req_size_pos SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as R2.
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as R3.
split; [exact I1|]. lia.
Qed.

Lemma w3_glob_keep : forall cx (W3 : world SEGS) (ms3 ms4 : machine_state) src,
  w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms4) -> alloc_ceiling <= c_sp1 cx - 16 ->
  p_glob cx W3 ms3 src -> p_glob cx W3 ms4 src.
Proof. intros cx W3 ms3 ms4 src HK Hac Hg. pose proof asan_consts as (C1 & _). exact (PcapEntryKit.p_glob_keep cx W3 ms3 ms4 (c_sp1 cx - 16) (c_sp1 cx + 152) src Hg HK ltac:(lia)). Qed.


(* The rd32 contract (lib/B/Prog/Rd32.v trd32_specX, proved there as pb_rd32X) at a call site of the harness: the
   caller's gx journal is opened, rd32's own journal is started inside it (ajournal_sub_init) and the result is
   lifted back by PaJournalFs.ajournal_gx_callee. *)
Lemma w3_rd32_call : forall STK sp0 FP ly S W0 mem md own lyc Sc (W3 : world SEGS) memc mdc k
    (regs : bvmap 5 word) p bb nn c0 c1 c2 c3,
  ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k ->
  YK0s.ret_ok (getr regs 1) ->
  getr regs 10 = w64 p ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - RD32_FRAME -> spZ regs <= sp0 ->
  In (bb, nn) (ablocks B lyc Sc) -> bb <= p -> p + 4 <= bb + nn ->
  garr8 SEGS (mrestrict (w_H W3) memc) p [c0; c1; c2; c3] ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_rd32)) memc (seg_rom SEGS)) mdc)
    (fun W2 c2' => W2 = W3 /\ exists regs2 mem2 md2,
       c2' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
       ajournal_gx SEGS B pe_G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W3 mem2 md2 k /\
       aregs_preserved regs regs2 /\
       getr regs2 10 = w64 (bv_swrap 32 (trd32_val (getr regs 11) c0 c1 c2 c3)) /\
       same_but_materialized mdc md2 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - RD32_FRAME <= a < spZ regs) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memc a)).
Proof. intros STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k regs p bb nn c0 c1 c2 c3 HJ Hraw H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb. exact (PcapEntryKit.rd32_call B LAWS TL STK sp0 FP ly S W0 mem md own lyc Sc W3 memc mdc k regs p bb nn c0 c1 c2 c3 HJ Hraw H10 Hal16 Hwlo Hwhi Hin Hbp Hpn Hgb). Qed.

Lemma w3_swz_range : forall cx, 0 <= p_swz cx <= 1.
Proof. intros cx. destruct (PcapEntryKit.p_swz_01 cx) as [H|H]; rewrite H; lia. Qed.

Lemma w3_fb_range : forall F q, 0 <= PSN.fb F q < 256.
Proof.
intros F q. unfold PSN.fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat q) F (Z_to_bv 8 0))) as H.
unfold bv_modulus in H. cbn in H. lia.
Qed.

Lemma w3_C_nth : forall cx j, 0 <= j -> nth (Z.to_nat j) (p_C cx) 0 = PSN.fb (p_F cx) j.
Proof. intros cx j _. exact (PcapEntryKit.p_C_fb cx j). Qed.

(* The four bytes a rd32 site reads, out of the copy's bytes. *)
Lemma w3_bytes4 : forall cx (m : word -> option byte) b q,
  garr8 SEGS m b (p_C cx) -> 0 <= q -> q + 4 <= p_nF cx ->
  garr8 SEGS m (b + q)
    [PSN.fb (p_F cx) q; PSN.fb (p_F cx) (q + 1); PSN.fb (p_F cx) (q + 2); PSN.fb (p_F cx) (q + 3)].
Proof. intros cx m b q Hg Hq Hq4. pose proof (PcapEntryKit.garr8_four m b (p_C cx) q Hg Hq ltac:(rewrite PcapEntryKit.p_lens; lia)) as H4. rewrite !PcapEntryKit.p_C_fb in H4. exact H4. Qed.

(* rd32's value at a site of the harness is the reader's hw. *)
Lemma w3_trd32_hw : forall cx q j,
  trd32_val (w64 (p_swz cx)) (PSN.fb (p_F cx) (q + j)) (PSN.fb (p_F cx) (q + j + 1))
    (PSN.fb (p_F cx) (q + j + 2)) (PSN.fb (p_F cx) (q + j + 3)) = p_hw cx q j.
Proof.
intros cx q j. unfold trd32_val, p_hw, PSN.hw, PSN.w32le, p_sw, w64.
pose proof (w3_swz_range cx) as Hr.
destruct (Z.eqb_spec (p_swz cx) 1) as [E1|E1].
- rewrite E1. replace (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false
    by (symmetry; apply Bool.not_true_is_false; rewrite bv_eqb_unsigned, Z.eqb_eq, !unsigned_lit_small; lia).
  lia.
- replace (p_swz cx) with 0 by lia.
  replace (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true
    by (symmetry; rewrite bv_eqb_unsigned, Z.eqb_eq; reflexivity).
  lia.
Qed.

Lemma w3_shape_call : forall E ss (ms : machine_state) (W3 : world SEGS) tgt,
  st_ok SEGS E (setpc ss tgt) (restrict (w_H W3) ms) -> ss_resv ss = None ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 tgt) (ms_mem ms) (seg_rom SEGS).
Proof.
intros E ss ms W3 tgt HS Hrv. destruct HS as (A1 & A2 & A3 & A4 & A5 & A6 & _).
cbn [restrict ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom setpc ss_pc ss_resv] in A1, A2, A3, A4, A5, A6.
rewrite Hrv in A4. cbn [resv_denot] in A4.
destruct ms. unfold mkst. cbn in A1, A2, A3, A4, A5, A6 |- *.
rewrite A1, A2, A3, A4, A5, A6. reflexivity.
Qed.

Lemma w3_alu_add : forall (x y : word) a c, bv_unsigned x = a -> bv_unsigned y = c ->
  alu64 ALU_ADD x y = w64 (a + c).
Proof.
intros x y a c Hx Hy. apply bv_eq. rewrite alu64_unsigned, Hx, Hy. cbn [zalu_raw].
unfold w64. rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma w3_preg : forall (regs regs2 : bvmap 5 word) (r : Z) (rr : bv 5),
  aregs_preserved regs regs2 -> acallee_saved r -> Z_to_bv 5 r = rr -> getr regs2 rr = getr regs rr.
Proof. intros regs regs2 r rr HP Hc Hr. subst rr. exact (HP r Hc). Qed.

(* A callee that writes only its own frame below sp keeps every spill slot. *)
Lemma w3_keepf_weak : forall sp1 (W3 : world SEGS) m m',
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 16 <= a < sp1) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  w3_keep sp1 W3 m m'.
Proof. intros sp1 W3 m m' H. exact (PcapEntryKit.mk_mono W3 m m' (sp1 - 16) sp1 (sp1 - 16) (sp1 + 152) ltac:(lia) ltac:(lia) H). Qed.

Lemma w3_slot_keepf : forall cx (W3 : world SEGS) (ms ms' : machine_state) off v,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 16 <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  0 <= c_sp1 cx -> c_sp1 cx + off + 8 <= 2 ^ 64 -> 16 <= off ->
  pslot cx W3 ms off v -> pslot cx W3 ms' off v.
Proof. intros cx W3 ms ms' off v HK H0 H1 H2 Hs. exact (PcapEntryKit.pslot_keep cx W3 ms ms' (c_sp1 cx - 16) (c_sp1 cx) off v Hs HK ltac:(lia) ltac:(lia) ltac:(lia)). Qed.

Lemma w3_region0_call : forall E ss (ms : machine_state) (W3 : world SEGS) r tgt,
  st_ok SEGS E (setpc ss tgt) (restrict (w_H W3) ms) -> nth_error (ss_mem ss) 0 = Some r ->
  region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms)) r.
Proof.
intros E ss ms W3 r tgt HS Hn.
pose proof (st_ok_region_nth E (setpc ss tgt) (restrict (w_H W3) ms) 0 r HS Hn) as HR.
cbn [restrict ms_mem] in HR. exact HR.
Qed.

Lemma w3_skips_inv : forall sw F cap q Q, PWD.skips sw F cap q Q ->
  (Q = q /\ PSN.kind sw F cap q <> PSN.KEmpty /\ PSN.kind sw F cap q <> PSN.KBig) \/
  (PSN.kind sw F cap q = PSN.KEmpty /\ PWD.skips sw F cap (q + 16) Q) \/
  (PSN.kind sw F cap q = PSN.KBig /\ PWD.skips sw F cap (q + 16 + PSN.incl sw F q) Q).
Proof.
intros sw F cap q Q HS. destruct HS as [q H1 H2 | q Q H1 H2 | q Q H1 H2].
- left. split; [reflexivity | split; [exact H1 | exact H2]].
- right; left. split; [exact H1 | exact H2].
- right; right. split; [exact H1 | exact H2].
Qed.

Lemma w3_skips_ge : forall sw F cap q Q, PWD.skips sw F cap q Q -> q <= Q.
Proof.
intros sw F cap q Q HS. induction HS as [q _ _ | q Q _ _ IH | q Q _ _ IH]; [lia | lia |].
pose proof (w3_hw_range sw F q 8) as Hr. unfold PSN.incl in *. lia.
Qed.

(* The skip chain's shape at a position whose record the reader did not skip. *)
Lemma w3_skips_fit : forall sw F cap q Q, PWD.skips sw F cap q Q ->
  PSN.kind sw F cap q <> PSN.KEmpty -> PSN.kind sw F cap q <> PSN.KBig -> Q = q.
Proof. intros sw F cap q Q HS H1 H2. destruct (w3_skips_inv sw F cap q Q HS) as [(-> & _ & _) | [(H & _) | (H & _)]];
       [reflexivity | exact (False_ind _ (H1 H)) | exact (False_ind _ (H2 H))]. Qed.

(* At a skipped position the kind is KEmpty or KBig, and the next position is still before the fit record. *)
Lemma w3_skip_step : forall cx q Q, p_skips cx q Q -> p_kind cx Q = PSN.KFit -> q <> Q ->
  (p_kind cx q = PSN.KEmpty \/ p_kind cx q = PSN.KBig) /\
  p_skips cx (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) Q /\ q + 16 + PSN.incl (p_sw cx) (p_F cx) q <= Q.
Proof.
intros cx q Q HS HK Hne. unfold p_skips, p_kind in *.
destruct (w3_skips_inv (p_sw cx) (p_F cx) (p_cap cx) q Q HS) as [(Hq & _ & _) | [(He & Hs) | (Hb & Hs)]].
- exfalso. exact (Hne (eq_sym Hq)).
- assert (Hi : PSN.incl (p_sw cx) (p_F cx) q = 0).
  { unfold PSN.kind in He.
    destruct (Z.eqb_spec (PSN.flen (p_F cx) - q) 0) as [E0|E0]; [discriminate He|].
    destruct (Z.ltb_spec (PSN.flen (p_F cx) - q) 16) as [E1|E1]; [discriminate He|].
    destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) q) 0) as [E2|E2]; [exact E2|].
    destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) q) (p_cap cx));
    [destruct (Z.leb_spec (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) (PSN.flen (p_F cx))); discriminate He|].
    destruct (Z.eqb_spec (p_cap cx) 0); [discriminate He|].
    destruct (Z.leb_spec (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) (PSN.flen (p_F cx))); discriminate He. }
  rewrite Hi, Z.add_0_r. split; [left; exact He|]. split; [exact Hs | exact (w3_skips_ge _ _ _ _ _ Hs)].
- split; [right; exact Hb|]. split; [exact Hs | exact (w3_skips_ge _ _ _ _ _ Hs)].
Qed.

(* `slli a0,a0,0x20; srli s9,a0,0x20` (0x80bac, 0x80bb0): the zero-extension of rd32's sign-extended answer. *)
Lemma w3_zext32 : forall E n v, ew E n = w64 (bv_swrap 32 v) -> 0 <= v < 2 ^ 32 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = v.
Proof.
intros E n v Hn Hv.
assert (Hu : U E (SOff n 0) = v + (if v <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)).
{ assert (Hid : forall z, zcanon (zcanon z) = zcanon z) by (intros z; unfold zcanon, M64; apply Zmod_mod).
  unfold U. rewrite denot_SOff, Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit, Hid.
  apply rd_sx32. exact Hv. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hu, !(U_lit E 32 ltac:(lia)).
change (Z.land 32 63) with 32. rewrite Z.shiftl_mul_pow2 by lia.
assert (Hm : zcanon ((v + (if v <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)) * 2 ^ 32) = v * 2 ^ 32).
{ unfold zcanon, M64. destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite Z.add_0_r. apply Z.mod_small. nia.
  - replace ((v + (2 ^ 64 - 2 ^ 32)) * 2 ^ 32) with (v * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. nia. }
rewrite Hm. rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma w3_swrap32_zero : forall v, 0 <= v < 2 ^ 32 -> bv_swrap 32 v = 0 -> v = 0.
Proof.
intros v Hv H0. pose proof (rd_sx32 v Hv) as Hc. rewrite H0 in Hc. unfold zcanon, M64 in Hc.
rewrite Z.mod_0_l in Hc by lia. destruct (Z.ltb_spec v (2 ^ 31)); lia.
Qed.

Lemma w3_kri_tri : forall cx e Q, p_skips cx e Q -> p_kind cx Q = PSN.KFit ->
  p_kind cx e = PSN.KEmpty \/ p_kind cx e = PSN.KBig \/ (e = Q /\ p_kind cx e = PSN.KFit).
Proof.
intros cx e Q HS HK. unfold p_skips, p_kind in *.
destruct (w3_skips_inv (p_sw cx) (p_F cx) (p_cap cx) e Q HS) as [(Hq & _ & _) | [(He & _) | (Hb & _)]].
- right; right. subst Q. split; [reflexivity | exact HK].
- left. exact He.
- right; left. exact Hb.
Qed.

(* The record at a skipped position: incl = 0 for KEmpty, cap < incl for KBig. *)
Lemma w3_kind_vals : forall cx q,
  (p_kind cx q = PSN.KEmpty -> PSN.incl (p_sw cx) (p_F cx) q = 0 /\ 16 <= p_nF cx - q) /\
  (p_kind cx q = PSN.KBig -> p_cap cx < PSN.incl (p_sw cx) (p_F cx) q /\
     q + 16 + PSN.incl (p_sw cx) (p_F cx) q <= p_nF cx /\ 16 <= p_nF cx - q).
Proof.
intros cx q. unfold p_kind, PSN.kind.
destruct (Z.eqb_spec (PSN.flen (p_F cx) - q) 0) as [E0|E0]; [split; discriminate|].
destruct (Z.ltb_spec (PSN.flen (p_F cx) - q) 16) as [E1|E1]; [split; discriminate|].
unfold PSN.flen, p_nF in *.
destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) q) 0) as [E2|E2].
- split; [intros _; split; [exact E2 | lia] | discriminate].
- destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) q) (p_cap cx)) as [E3|E3].
  + destruct (Z.leb_spec (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) (Z.of_nat (length (p_F cx))));
    split; discriminate.
  + destruct (Z.eqb_spec (p_cap cx) 0) as [E4|E4]; [split; discriminate|].
    destruct (Z.leb_spec (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) (Z.of_nat (length (p_F cx)))) as [E5|E5].
    * split; [discriminate | intros _; split; [lia | split; lia]].
    * split; discriminate.
Qed.

(* The fit record at e: the three tests of 0x80bb4 / 0x80bbc / 0x80be8 passed. *)
Lemma w3_kind_fit_of : forall cx q, 16 <= p_nF cx - q ->
  PSN.incl (p_sw cx) (p_F cx) q <> 0 -> PSN.incl (p_sw cx) (p_F cx) q <= p_cap cx ->
  q + 16 + PSN.incl (p_sw cx) (p_F cx) q <= p_nF cx -> p_kind cx q = PSN.KFit.
Proof.
intros cx q H16 Hnz Hcap Hfit. unfold p_kind, PSN.kind. unfold PSN.flen, p_nF in *.
destruct (Z.eqb_spec (Z.of_nat (length (p_F cx)) - q) 0) as [E0|E0]; [lia|].
destruct (Z.ltb_spec (Z.of_nat (length (p_F cx)) - q) 16) as [E1|E1]; [lia|].
destruct (Z.eqb_spec (PSN.incl (p_sw cx) (p_F cx) q) 0) as [E2|E2]; [lia|].
destruct (Z.leb_spec (PSN.incl (p_sw cx) (p_F cx) q) (p_cap cx)) as [E3|E3]; [|lia].
destruct (Z.leb_spec (q + 16 + PSN.incl (p_sw cx) (p_F cx) q) (Z.of_nat (length (p_F cx)))); [reflexivity | lia].
Qed.

(* `lw s6,0xc(s4)` (0x80bf0): ps.last_orig_len, sign-extended from bit 31. *)
Lemma w3_sext32 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff n 0)) = w64 (bv_swrap 32 v).
Proof.
intros E n v Hn Hv. rewrite denot_lit_U, U_SExt, (U_atom E n v Hn) by lia.
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold w64, zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Zmod_mod.
Qed.

Lemma w3_sext32' : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 ->
  sext 64 (bv_extract 0 32 (ew E n)) = w64 (bv_swrap 32 v).
Proof.
intros E n v Hn Hv. rewrite <- (w3_sext32 E n v Hn Hv). cbn [sv_denot].
rewrite Hn, unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.


Lemma w3_zx_alu : forall (x : word) v, bv_unsigned x = zcanon (bv_swrap 32 v) -> 0 <= v < 2 ^ 32 ->
  alu64 ALU_SRL (alu64 ALU_SLL x (Z_to_bv 64 32)) (Z_to_bv 64 32) = w64 v.
Proof.
intros x v Hx Hv. apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw]. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite !(unsigned_lit_small 32) by lia. change (Z.land 32 63) with 32.
rewrite Hx, (rd_sx32 v Hv). unfold w64. rewrite Z_to_bv_unsigned.
rewrite Z.shiftl_mul_pow2 by lia.
assert (Hm : bv_wrap 64 ((v + (if v <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32)) * 2 ^ 32) = v * 2 ^ 32).
{ unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). destruct (Z.ltb_spec v (2 ^ 31)).
  - rewrite Z.add_0_r. apply Z.mod_small. nia.
  - replace ((v + (2 ^ 64 - 2 ^ 32)) * 2 ^ 32) with (v * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64) by ring.
    rewrite Z_mod_plus_full. apply Z.mod_small. nia. }
rewrite Hm, Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small v) by lia. reflexivity.
Qed.

(* ---- the cut lemmas, stated (each Definition X_stmt becomes Lemma X : X_stmt when proved) ---- *)

(* KD -> K4 (n > 0) / K5 (n <= 0). *)
Definition pe_from_KD_stmt : Prop :=
  PF (GI_K4 B MT KS) -> PF (GI_K5 B MT KS) -> PF (GI_KD B MT KS).

(* K4 -> KR. *)
Definition pe_from_K4_m_stmt : Prop :=
  forall m, PF (pe_meas (GI_KR B MT KS) m) -> PF (pe_meas (GI_K4 B MT KS) m).

(* KR -> KRI (the rd32 call of incl). *)
Definition pe_from_KR_m_stmt : Prop :=
  forall m, PF (pe_meas (GI_KRI B MT KS) m) -> PF (pe_meas (GI_KR B MT KS) m).

(* KRI -> KR (a skipped record: the back edge, e grows by 16 + incl >= 16) / KO (the fit record; the rd32 call of
   orig_len). *)
Definition pe_from_KRI_m_stmt : Prop :=
  forall m,
  PF (pe_meas (GI_KR B MT KS) (m - 16)) -> PF (pe_meas (GI_KO B MT KS) m) -> PF (pe_meas (GI_KRI B MT KS) m).

(* ---- the skip loop, closed ---- *)

Definition pe_meas_KR_low_stmt : Prop :=
  forall m cx fp k acc ly3 S3 W3 ms3 md3,
  pe_meas (GI_KR B MT KS) m cx fp k acc ly3 S3 W3 ms3 md3 -> 16 <= m.

Definition pe_from_skip_m_stmt : Prop :=
  forall m, PF (pe_meas (GI_KO B MT KS) m) -> PF (pe_meas (GI_KR B MT KS) m).

(* ---- the plain forms ---- *)

Definition pe_from_meas_all_stmt : Prop :=
  forall GI, (forall m, PF (pe_meas GI m)) -> PF GI.

Definition pe_meas_of_stmt : Prop :=
  forall GI m, PF GI -> PF (pe_meas GI m).

Definition pe_from_K4_stmt : Prop :=
  PF (GI_KR B MT KS) -> PF (GI_K4 B MT KS).

Definition pe_from_KR_stmt : Prop :=
  PF (GI_KRI B MT KS) -> PF (GI_KR B MT KS).

Definition pe_from_KRI_stmt : Prop :=
  PF (GI_KR B MT KS) -> PF (GI_KO B MT KS) -> PF (GI_KRI B MT KS).

Definition pe_from_skip_stmt : Prop :=
  PF (GI_KO B MT KS) -> PF (GI_KR B MT KS).

(* KO closes K4's stretch through the skip loop. *)
Definition pe_from_K4_KO_stmt : Prop :=
  PF (GI_KO B MT KS) -> PF (GI_K4 B MT KS).


(* ---- KD -> K4 / K5 ---- *)
Lemma pe_from_KD : pe_from_KD_stmt.
Proof.
unfold pe_from_KD_stmt.
intros RK4 RK5 cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGI as (b & h & buf & HCUT & Hn26 & Hgood & Ra0 & Rs2 & Rs3 & Rs4 & Rs8 & Hslots & Hbuf & Hglob & Hrd).
destruct HCUT as (HBody & Hk & Hacc & HPerm & Hfds & Hfs).
pose proof HJ as HJ0.
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
destruct (w3_blocks3 cx ly3 S3 W3 ms3 md3 b h buf HAR3 HPerm) as (Hinb & Hb1 & Hb2 & Hh1 & Hh2 & Hu1 & Hu2).
pose proof HBody as (_ & _ & _ & _ & _ & _ & (P2 & P8 & P9 & P3 & P4) & _).
pose proof Hslots as (Q144 & Q24 & Q72 & Q40 & Q32 & Q16 & Q88 & Q120).
set (ex := w3_extra b h buf (p_cap cx) (p_nF cx) (p_d cx) (pF cx fp) (pSH cx fp) 0 0 0).
set (E := Eimg (Ereg (ms_regs ms3) ex)).
assert (EReg : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EXn : forall j, (j < 12)%nat ->
   ew E (32 + j)%nat = Z_to_bv 64
     (nth j [SB_W; b; h; buf; p_cap cx; p_nF cx; p_d cx; pF cx fp; pSH cx fp; 0; 0; 0] 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra (ms_regs ms3) ex j). subst ex. unfold w3_extra. apply map_nth. }
assert (E35 : ew E 35%nat = Z_to_bv 64 buf)
  by (pose proof (EXn 3%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E36 : ew E 36%nat = Z_to_bv 64 (p_cap cx))
  by (pose proof (EXn 4%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E38 : ew E 38%nat = Z_to_bv 64 (p_d cx))
  by (pose proof (EXn 6%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E39 : ew E 39%nat = Z_to_bv 64 (pF cx fp))
  by (pose proof (EXn 7%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E40 : ew E 40%nat = Z_to_bv 64 (pSH cx fp))
  by (pose proof (EXn 8%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E9 : bv_unsigned (ew E 9%nat) = c_sp1 cx)
  by (rewrite (EReg 9%nat (9%bv : bv 5) eq_refl), P9; apply unsigned_lit_small; lia).
pose proof (p_sizes cx) as (Z1 & Z2 & Z3). pose proof (p_d_range cx) as Zd.
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) cs_base).
{ unfold cs_base. repeat apply Forall_cons; try apply Forall_nil.
  - apply (w3_chunk_slot E W3 ms3 cx 16 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q16].
  - apply (w3_chunk_slot E W3 ms3 cx 24 (SOff 38 0) (p_d cx));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_d in *; lia | exact Q24].
  - apply (w3_chunk_slot E W3 ms3 cx 32 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q32].
  - apply (w3_chunk_slot E W3 ms3 cx 40 (SOff 40 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q40].
  - apply (w3_chunk_slot E W3 ms3 cx 72 (SLit SHADOW_OFF) SHADOW_OFF);
    [reflexivity | unfold SHADOW_OFF; lia | exact Q72].
  - apply (w3_chunk_slot E W3 ms3 cx 88 (SOff 39 96) (pF cx fp + PO_TS));
    [cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity | unfold PO_TS; lia
    | exact Q88].
  - apply (w3_chunk_slot E W3 ms3 cx 96 (SOff 35 0) buf);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hbuf].
  - apply (w3_chunk_slot E W3 ms3 cx 120 (SOff 36 0) (p_cap cx));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_cap, p_d in *; lia
    | unfold p_cap, p_d; exact Q120].
  - apply (w3_chunk_slot E W3 ms3 cx 144 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q144]. }
assert (HG : gx_ok SEGS B pe_G)
  by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hq&_); exact Hq).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
destruct (w3_entry cx fp PP_KD PSH_ts [slots_region cs_base] [] [] ex ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody
            ltac:(subst ex; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(apply Forall_cons; [|apply Forall_nil];
                  apply (w3_slots_ok E W3 ms3 cx cs_base E9 ltac:(lia)); [|exact HCS];
                  intros a Ha; apply Hpres; change LLVMF_STK with 32768; split; lia)
            ltac:(apply pairwise_disjoint_of_extents; cbn [map extent_of_region];
                  cbn [zpairwise_disjoint zall_disjoint]; tauto)
            I I) as [HS SHOK].
pose proof (w3_RUN pe_G HG 0 []) as RUN.
pose proof (w3_RUNTO pe_G HG 0 []) as RUNTO.
pose proof (paj_branch (PI:=PI)) as BR.
fold E in HS, SHOK.
assert (Hfirst : -1 <= p_first cx < 2 ^ 32) by (unfold p_first, p_res; apply w3_res_range).
assert (E10 : ew E 10%nat = w64 (p_first cx)) by (rewrite (EReg 10%nat (10%bv : bv 5) eq_refl); exact Ra0).
psrr_branch_tok RUN BR HS SHOK Wspan.
- (* n <= 0: the record loop is skipped, PP_K5 with at = 24 *)
  assert (Hn0 : p_first cx <= 0).
  { cbn [branch_taken sv_denot] in Hc. rewrite E10, Z.add_0_r in Hc. unfold w64 in Hc.
    rewrite Z_to_bv_bv_unsigned, bv_lts_signed, !w3_signed_small in Hc by lia.
    apply negb_true_iff, Z.ltb_ge in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_K5.
  { apply awr_ok_x_of0.
    eapply (awr_ok_cons_gen E (slots_region cs_base) [] LLVMF_STK (spZ (c_regs cx)) [sink_token]
              (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(PE_CID, fp)] 9%nat (c_sp1 cx));
    [reflexivity | exact E9 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi slots_region]. intros a Ha. left. change LLVMF_STK with 32768. lia. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9. prreg HS (10%bv : bv 5) T10.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (24%bv : bv 5) T24.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9. rewrite (EReg 10%nat (10%bv : bv 5) eq_refl) in T10.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 24%nat (24%bv : bv 5) eq_refl) in T24.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_KD PP_K5 PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBody5.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd5 & Hfs5).
  apply (RK5 cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB HJ Hfrs Hmo).
  exists b, h, buf, 24.
  split; [split; [exact HBody5|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite Hfd5; exact Hfds | rewrite Hfs5; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [pose proof (w3_good_len cx Hgood); lia|].
  split; [intros HKF; pose proof (w3_res_pos _ _ _ _ HKF); unfold p_first, p_res in Hn0; lia|].
  split; [rewrite T10; exact Ra0|]. split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|].
  split; [rewrite T24; exact Rs8|]. split; [rewrite T26; reflexivity|].
  split.
  { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                    ltac:(unfold p_d in *; lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                    eq_refl ltac:(unfold SHADOW_OFF; lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                    ltac:(unfold PO_TS; lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
             ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
             ltac:(unfold p_cap, p_d in *; lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 10 0) (p_res cx (p_q cx 24) mod 2 ^ 64) HRg E9
                  ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned, w3_bv_mod;
                        reflexivity)
                  ltac:(apply Z.mod_pos_bound; lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  exact (w3_reader_keep cx fp W3 ms3 ms b h buf 24 ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2 Hrd).
- (* n > 0: the record loop's constants, PP_K4 with i = 0, at = 24 *)
  assert (Hn0 : 0 < p_first cx).
  { cbn [branch_taken sv_denot] in Hc. rewrite E10, Z.add_0_r in Hc. unfold w64 in Hc.
    rewrite Z_to_bv_bv_unsigned, bv_lts_signed, !w3_signed_small in Hc by lia.
    apply negb_false_iff, Z.ltb_lt in Hc. lia. }
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_K4.
  { apply awr_ok_x_of0.
    eapply (awr_ok_cons_gen E (slots_region cs_base) [] LLVMF_STK (spZ (c_regs cx)) [sink_token]
              (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(PE_CID, fp)] 9%nat (c_sp1 cx));
    [reflexivity | exact E9 | | apply awr_ok_nil].
    cbn [YP09.r_wlo YP09.r_whi slots_region]. intros a Ha. left. change LLVMF_STK with 32768. lia. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 24%nat (24%bv : bv 5) eq_refl) in T24.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_KD PP_K4 PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBody4.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd4 & Hfs4).
  assert (E18 : ew E 18%nat = Z_to_bv 64 b) by (rewrite (EReg 18%nat (18%bv : bv 5) eq_refl); exact Rs2).
  assert (E19 : ew E 19%nat = Z_to_bv 64 buf) by (rewrite (EReg 19%nat (19%bv : bv 5) eq_refl); exact Rs3).
  apply (RK4 cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB HJ Hfrs Hmo).
  exists b, h, buf, 0, 24.
  split; [split; [exact HBody4|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite Hfd4; exact Hfds | rewrite Hfs4; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|].
  split; [lia|]. split; [lia|].
  split; [apply w3_res_fit_of_pos; exact Hn0|].
  split; [left; split; reflexivity|].
  split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|].
  split; [rewrite T21; unfold w64; rewrite <- (w3_bv_mod (-8)); reflexivity|].
  split; [rewrite T23; exact (w3_not_val' E 18 b E18 ltac:(lia))|].
  split; [rewrite T24; exact Rs8|]. split; [rewrite T26; reflexivity|].
  split.
  { split.
    { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 19 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 104 (SLit 0) 0 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 10 0) (p_res cx (p_q cx 24)) HRg E9
                  ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E10, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(unfold p_first in *; lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  exact (w3_reader_keep cx fp W3 ms3 ms b h buf 24 ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2 Hrd).
Qed.

(* The reader's chain only moves forward, and the harness's skip relation holds from any start to the chain's stop. *)
Lemma w3_chain_ge : forall sw F cap fuel q lh, q <= fst (fst (PSN.chain sw F cap fuel q lh)).
Proof.
intros sw F cap fuel. induction fuel as [|f IH]; intros q lh; [cbn; lia|].
cbn [PSN.chain]. assert (Hi : 0 <= PSN.incl sw F q < 2 ^ 32) by exact (w3_hw_range sw F q 8).
destruct (PSN.kind sw F cap q); try (cbn; lia).
- pose proof (IH (q + 16) lh). lia.
- pose proof (IH (q + 16 + PSN.incl sw F q) (Some q)) as Hq.
  destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q o] l]. cbn in Hq |- *. lia.
Qed.

Lemma w3_skips_chain : forall sw F cap fuel q lh,
  PSN.flen F - q <= 16 * Z.of_nat fuel -> PWD.skips sw F cap q (fst (fst (PSN.chain sw F cap fuel q lh))).
Proof.
intros sw F cap fuel. induction fuel as [|f IH]; intros q lh Hf.
- cbn [PSN.chain fst]. apply PWD.skips_stop; unfold PSN.kind;
  (destruct (Z.eqb_spec (PSN.flen F - q) 0) as [E0|E0]; [discriminate|]);
  (destruct (Z.ltb_spec (PSN.flen F - q) 16) as [E1|E1]; [discriminate|]); cbn [Z.of_nat] in Hf; lia.
- assert (Hi : 0 <= PSN.incl sw F q < 2 ^ 32) by exact (w3_hw_range sw F q 8).
  cbn [PSN.chain]. destruct (PSN.kind sw F cap q) eqn:HK; try (cbn [fst]; apply PWD.skips_stop; rewrite HK; discriminate).
  + apply (PWD.skips_empty sw F cap q _ HK). apply IH. lia.
  + pose proof (IH (q + 16 + PSN.incl sw F q) (Some q) ltac:(lia)) as Hq.
    destruct (PSN.chain sw F cap f (q + 16 + PSN.incl sw F q) (Some q)) as [[Q o] l]. cbn [fst] in Hq |- *.
    exact (PWD.skips_big sw F cap q Q HK Hq).
Qed.

Lemma w3_skips_self : forall cx p, 0 <= p -> p_skips cx p (p_q cx p).
Proof.
intros cx p Hp. unfold p_skips, p_q, PSN.psn_q, PSN.psn_chain.
apply w3_skips_chain. unfold PSN.flen. lia.
Qed.

Lemma w3_q_ge : forall cx p, p <= p_q cx p.
Proof. intros cx p. unfold p_q, PSN.psn_q, PSN.psn_chain. apply w3_chain_ge. Qed.

Lemma w3_res_le_incl : forall sw F cap q, PSN.kind sw F cap q = PSN.KFit ->
  PSN.res_of sw F cap q <= PSN.incl sw F q.
Proof.
intros sw F cap q HK. unfold PSN.res_of. rewrite HK. unfold PSN.rec_len.
destruct (PSN.tagged sw F q); lia.
Qed.

(* What the K4 cut gives about the record the reader found: the file is long enough for the header at `at`, and
   the answer n fits the record buffer. *)
Lemma w3_K4_facts : forall cx p,
  p_good cx = true -> 0 <= p -> p_kind cx (p_q cx p) = PSN.KFit ->
  p + 16 <= p_nF cx /\ 0 < p_res cx (p_q cx p) <= p_cap cx /\ p <= p_q cx p.
Proof.
intros cx p Hgood Hp HK.
pose proof (w3_q_ge cx p) as Hq.
destruct (w3_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HK) as (Hi & Hfit & _).
pose proof (w3_res_pos _ _ _ _ HK) as Hpos.
pose proof (w3_res_le_incl _ _ _ _ HK) as Hle.
unfold PSN.flen, p_nF, p_res, p_q in *. lia.
Qed.

(* ---- K4 -> KR: the loop head's three abort tests, `first`, and the calls counter ---- *)
Lemma pe_from_K4_m : pe_from_K4_m_stmt.
Proof.
unfold pe_from_K4_m_stmt. intros m RKR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo (HGI & HM).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGI as (b & h & buf & i & p & HCUT & Hn26 & Hgood & Hi0 & Hip & HKF & Hdisj &
                 Rs2 & Rs4 & Rs5 & Rs7 & Rs8 & Rs10 & Hlslots & Hcalls & Hnslot & Hglob & Hrd).
destruct HCUT as (HBody & Hk & Hacc & HPerm & Hfds & Hfs).
destruct Hlslots as (Hslots & Hbuf & Hvmask & Hbuf12 & Husec).
pose proof HJ as HJ0.
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
destruct (w3_blocks3 cx ly3 S3 W3 ms3 md3 b h buf HAR3 HPerm) as (Hinb & Hb1 & Hb2 & Hh1 & Hh2 & Hu1 & Hu2).
pose proof HBody as (_ & _ & _ & _ & _ & _ & (P2 & P8 & P9 & P3 & P4) & _).
pose proof Hslots as (Q144 & Q24 & Q72 & Q40 & Q32 & Q16 & Q88 & Q120).
pose proof (p_sizes cx) as (Z1 & Z2 & Z3). pose proof (p_d_range cx) as Zd.
destruct (w3_K4_facts cx p Hgood ltac:(lia) HKF) as (Hp16 & (Hn1 & Hn2) & Hpq).
pose proof (w3_good_len cx Hgood) as Hgl.
set (ex := w3_extra b h buf (p_cap cx) (p_nF cx) (p_d cx) (pF cx fp) (pSH cx fp) 0 i (p_res cx (p_q cx p))).
set (E := Eimg (Ereg (ms_regs ms3) ex)).
assert (EReg : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EXn : forall j, (j < 12)%nat ->
   ew E (32 + j)%nat = Z_to_bv 64
     (nth j [SB_W; b; h; buf; p_cap cx; p_nF cx; p_d cx; pF cx fp; pSH cx fp; 0; i; p_res cx (p_q cx p)] 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra (ms_regs ms3) ex j). subst ex. unfold w3_extra. apply map_nth. }
assert (E35 : ew E 35%nat = Z_to_bv 64 buf)
  by (pose proof (EXn 3%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E36 : ew E 36%nat = Z_to_bv 64 (p_cap cx))
  by (pose proof (EXn 4%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E37 : ew E 37%nat = Z_to_bv 64 (p_nF cx))
  by (pose proof (EXn 5%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E38 : ew E 38%nat = Z_to_bv 64 (p_d cx))
  by (pose proof (EXn 6%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E39 : ew E 39%nat = Z_to_bv 64 (pF cx fp))
  by (pose proof (EXn 7%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E40 : ew E 40%nat = Z_to_bv 64 (pSH cx fp))
  by (pose proof (EXn 8%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E42 : ew E 42%nat = Z_to_bv 64 i)
  by (pose proof (EXn 10%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E43 : ew E 43%nat = Z_to_bv 64 (p_res cx (p_q cx p)))
  by (pose proof (EXn 11%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E9 : bv_unsigned (ew E 9%nat) = c_sp1 cx)
  by (rewrite (EReg 9%nat (9%bv : bv 5) eq_refl), P9; apply unsigned_lit_small; lia).
assert (E18 : ew E 18%nat = Z_to_bv 64 b) by (rewrite (EReg 18%nat (18%bv : bv 5) eq_refl); exact Rs2).
assert (E23 : ew E 23%nat = Z_to_bv 64 (- b - 1)) by (rewrite (EReg 23%nat (23%bv : bv 5) eq_refl); exact Rs7).
assert (E26 : ew E 26%nat = Z_to_bv 64 p) by (rewrite (EReg 26%nat (26%bv : bv 5) eq_refl); exact Rs10).
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) cs_K4).
{ unfold cs_K4. repeat apply Forall_cons; try apply Forall_nil.
  - apply (w3_chunk_slot E W3 ms3 cx 16 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q16].
  - apply (w3_chunk_slot E W3 ms3 cx 24 (SOff 38 0) (p_d cx));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_d in *; lia | exact Q24].
  - apply (w3_chunk_slot E W3 ms3 cx 32 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q32].
  - apply (w3_chunk_slot E W3 ms3 cx 40 (SOff 40 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q40].
  - apply (w3_chunk_slot E W3 ms3 cx 48 (SLit 3840) 3840); [reflexivity | lia | exact Hvmask].
  - apply (w3_chunk_slot E W3 ms3 cx 56 (SOff 35 12) (buf + 12));
    [cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity | lia | exact Hbuf12].
  - apply (w3_chunk_slot E W3 ms3 cx 64 (SLit 4294967296000000) (1000000 * 2 ^ 32));
    [reflexivity | lia | exact Husec].
  - apply (w3_chunk_slot E W3 ms3 cx 72 (SLit SHADOW_OFF) SHADOW_OFF);
    [reflexivity | unfold SHADOW_OFF; lia | exact Q72].
  - apply (w3_chunk_slot E W3 ms3 cx 88 (SOff 39 96) (pF cx fp + PO_TS));
    [cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity | unfold PO_TS; lia
    | exact Q88].
  - apply (w3_chunk_slot E W3 ms3 cx 96 (SOff 35 0) buf);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hbuf].
  - apply (w3_chunk_slot E W3 ms3 cx 104 (SOff 42 0) i);
    [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hcalls].
  - apply (w3_chunk_slot E W3 ms3 cx 112 (SOff 43 0) (p_res cx (p_q cx p)));
    [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hnslot].
  - apply (w3_chunk_slot E W3 ms3 cx 120 (SOff 36 0) (p_cap cx));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_cap, p_d in *; lia
    | unfold p_cap, p_d; exact Q120].
  - apply (w3_chunk_slot E W3 ms3 cx 144 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q144]. }
assert (Eobj4 : bv_unsigned (ew E (A_OBJ 4)) = pa_val (A_OBJ 4)).
{ subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  apply unsigned_lit_small. pose proof (pa_val_range (A_OBJ 4)). lia. }
pose proof (pa_obj_img 4 ltac:(lia)) as O4. assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
assert (HGL : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (glen_region (SOff 37 0))).
{ unfold glen_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eobj4.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 4)) 0 8 (SOff 37 0) (p_nF cx));
  [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  rewrite Z.add_0_r. exact (proj2 Hglob). }
assert (HG : gx_ok SEGS B pe_G)
  by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hq&_); exact Hq).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HCDS : conds_ok E cds_K4).
{ unfold cds_K4. cbn [conds_ok].
  split; [|split; [|split; [|split; [|exact I]]]]; unfold acond_ok; cbn [ac_c ac_a ac_b branch_taken].
  - rewrite bv_ltu_unsigned. apply Z.ltb_lt.
    change (bv_unsigned (sv_denot E (SOff 42 0))) with (U E (SOff 42 0)).
    change (bv_unsigned (sv_denot E (SAlu ALU_SRL (SOff 37 (-24)) (SLit 4))))
      with (U E (SAlu ALU_SRL (SOff 37 (-24)) (SLit 4))).
    rewrite (U_atom E 42%nat i E42 ltac:(lia)), U_SAlu. cbn [zalu_raw].
    replace (U E (SOff 37 (-24))) with (p_nF cx - 24)
      by (unfold U; rewrite denot_SOff, E37, unsigned_lit_small by lia;
          rewrite zcanon_id by (unfold M64; lia); lia).
    rewrite (U_lit E 4 ltac:(lia)). change (Z.land 4 63) with 4. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 4) with 16.
    assert (Hdiv : i + 1 <= (p_nF cx - 24) / 16).
    { apply Z.div_le_lower_bound; lia. }
    rewrite zcanon_id; [lia|]. unfold M64.
    pose proof (Z.div_pos (p_nF cx - 24) 16 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (p_nF cx - 24) 16 (p_nF cx) ltac:(lia) ltac:(lia)). lia.
  - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge.
    rewrite (denot_SOff E 36 0), (denot_SOff E 43 0), E36, E43, !unsigned_lit_small by lia.
    rewrite !Z.add_0_r, !zcanon_id by (unfold M64; lia). lia.
  - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge.
    rewrite (denot_SOff E 37 0), (denot_SOff E 26 16), E37, E26, !unsigned_lit_small by lia.
    rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). lia.
  - rewrite negb_true_iff, bv_eqb_unsigned, Z.eqb_neq.
    rewrite (denot_SOff E 18 0), E18, unsigned_lit_small by lia. rewrite Z.add_0_r, zcanon_id by (unfold M64; lia).
    replace (bv_unsigned (sv_denot E (SLit 0))) with 0 by (cbn [sv_denot]; rewrite unsigned_lit_small; lia). lia. }
assert (U18 : bv_unsigned (ew E 18%nat) = b) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23%nat) = 2 ^ 64 - 1 - b)
  by (rewrite E23, unsigned_lit; unfold zcanon, M64; symmetry; apply (Z.mod_unique _ _ (-1)); lia).
assert (U26 : bv_unsigned (ew E 26%nat) = p) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36%nat) = p_cap cx) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37%nat) = p_nF cx) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U42 : bv_unsigned (ew E 42%nat) = i) by (rewrite E42; apply unsigned_lit_small; lia).
assert (U43 : bv_unsigned (ew E 43%nat) = p_res cx (p_q cx p))
  by (rewrite E43; apply unsigned_lit_small; lia).
assert (HATOMS : atoms_ok E fl_K4).
{ unfold fl_K4. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U23, U26, U36, U37, U42, U43. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
destruct (w3_entry cx fp PP_K4 PSH_ts [slots_region cs_K4; glen_region (SOff 37 0)] fl_K4 cds_K4 ex
            ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody ltac:(subst ex; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(apply Forall_cons; [|apply Forall_cons; [exact HGL | apply Forall_nil]];
                  apply (w3_slots_ok E W3 ms3 cx cs_K4 E9 ltac:(lia)); [|exact HCS];
                  intros a Ha; apply Hpres; change LLVMF_STK with 32768; split; lia)
            ltac:(apply pairwise_disjoint_of_extents;
                  unfold slots_region, glen_region, extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
                  cbn [base_val]; fold E; rewrite Eobj4, E9;
                  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
                  repeat split; lia)
            HATOMS HCDS) as [HS SHOK].
pose proof (w3_RUN pe_G HG 0 []) as RUN.
pose proof (w3_RUNTO pe_G HG 0 []) as RUNTO.
pose proof (paj_branch (PI:=PI)) as BR.
fold E in HS, SHOK.
(* pin s8 to the listing's hi atom, so the PLdHi of g_file_len runs *)
assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
{ cbn [restrict ms_regs]. rewrite Rs8. cbn [sv_denot]. subst E.
  rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia). rewrite Z.add_0_r. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS eq_refl HS8) as HSp.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSp. clear HS. rename HSp into HS.
(* the three abort tests and the UBSan guard 0x80b80, decided by cds_K4; stop at the `beqz calls` of 0x80b5c *)
paj_run_tok RUN HS HJ SHOK Wspan.
{ w3_awr E9. }
assert (HKEEP1 : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
{ intros a Ha Hn.
  refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
  intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
  destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
  destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
  destruct Hinw. }
clear HF HFr HG. rename ms into ms1. rename mat into mat1.
psrr_branch_tok RUN BR HS SHOK Wspan.
- (* calls = 0: `first` is the answer n itself (0x80b54, 0x80b64) *)
  assert (Hi00 : i = 0).
  { cbn [branch_taken] in Hc. rewrite bv_eqb_unsigned in Hc. apply Z.eqb_eq in Hc.
    rewrite (denot_SOff E 42 0), E42, unsigned_lit_small in Hc by lia.
    rewrite Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
    replace (bv_unsigned (sv_denot E (SLit 0))) with 0 in Hc
      by (cbn [sv_denot]; symmetry; apply unsigned_lit_small; lia). lia. }
  assert (Hp24 : p = 24) by (destruct Hdisj as [[_ Hq] | [Hq _]]; lia).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_KR.
  { w3_awr E9. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { apply (w3_keep_trans (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms1) (ms_mem ms) HKEEP1).
    intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_K4 PP_KR PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBodyR.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat1 md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
  destruct (same_but_materialized_fs (with_vm_backing (m_vm_lazy md3) mat1 md3)
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat1 md3)) mat
                 (with_vm_backing (m_vm_lazy md3) mat1 md3))
              ltac:(apply same_but_materialized_wvb_any)) as (HfdR & HfsR).
  apply (RKR cx fp k acc ly3 S3 W3 ms _ HB HJ Hfrs Hmo).
  split; [| rewrite T26, E26, unsigned_lit_small by lia;
            rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; exact HM].
  exists b, h, buf, i, p, p.
  split; [split; [exact HBodyR|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite HfdR, Hfd1; exact Hfds | rewrite HfsR, Hfs1; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HKF|].
  split; [lia|]. split; [exact (w3_skips_self cx p ltac:(lia))|]. split; [lia|].
  split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|]. split; [rewrite T21; exact Rs5|].
  split; [rewrite T22, E26, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite T23; exact Rs7|].
  split; [rewrite T24; subst E; change 288%nat with (A_HI 8);
          rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
  split; [rewrite T26; exact Rs10|].
  split.
  { split.
    { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 1) (i + 1) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E42, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 43 0) (p_first cx mod 2 ^ 64) HRg E9
                  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; rewrite Hp24; rewrite <- w3_bv_mod; reflexivity) ltac:(apply Z.mod_pos_bound; lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  exact (w3_reader_keep cx fp W3 ms3 ms b h buf p ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2 Hrd).
- (* calls <> 0: `first` is the loop's a3 (0x80b60) *)
  assert (Hi0n : i <> 0).
  { cbn [branch_taken] in Hc. rewrite bv_eqb_unsigned in Hc. apply Z.eqb_neq in Hc.
    rewrite (denot_SOff E 42 0), E42, unsigned_lit_small in Hc by lia.
    rewrite Z.add_0_r, zcanon_id in Hc by (unfold M64; lia).
    replace (bv_unsigned (sv_denot E (SLit 0))) with 0 in Hc
      by (cbn [sv_denot]; symmetry; apply unsigned_lit_small; lia). lia. }
  assert (E13 : ew E 13%nat = w64 (p_first cx))
    by (rewrite (EReg 13%nat (13%bv : bv 5) eq_refl); destruct Hdisj as [[Hq _] | [_ Hq]]; [lia | exact Hq]).
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_KR.
  { w3_awr E9. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { apply (w3_keep_trans (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms1) (ms_mem ms) HKEEP1).
    intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_K4 PP_KR PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBodyR.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat1 md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
  destruct (same_but_materialized_fs (with_vm_backing (m_vm_lazy md3) mat1 md3)
              (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat1 md3)) mat
                 (with_vm_backing (m_vm_lazy md3) mat1 md3))
              ltac:(apply same_but_materialized_wvb_any)) as (HfdR & HfsR).
  apply (RKR cx fp k acc ly3 S3 W3 ms _ HB HJ Hfrs Hmo).
  split; [| rewrite T26, E26, unsigned_lit_small by lia;
            rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; exact HM].
  exists b, h, buf, i, p, p.
  split; [split; [exact HBodyR|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite HfdR, Hfd1; exact Hfds | rewrite HfsR, Hfs1; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HKF|].
  split; [lia|]. split; [exact (w3_skips_self cx p ltac:(lia))|]. split; [lia|].
  split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|]. split; [rewrite T21; exact Rs5|].
  split; [rewrite T22, E26, unsigned_lit_small by lia; reflexivity|].
  split; [rewrite T23; exact Rs7|].
  split; [rewrite T24; subst E; change 288%nat with (A_HI 8);
          rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
  split; [rewrite T26; exact Rs10|].
  split.
  { split.
    { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 1) (i + 1) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E42, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 13 0) (p_first cx mod 2 ^ 64) HRg E9
                  ltac:(cbn; tauto) ltac:(cbn [sv_denot]; rewrite E13, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; rewrite <- w3_bv_mod; reflexivity) ltac:(apply Z.mod_pos_bound; lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  exact (w3_reader_keep cx fp W3 ms3 ms b h buf p ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2 Hrd).
Qed.


(* ---- KR -> KRI: the two UBSan guards of the header address and the rd32 of incl ---- *)
Lemma pe_from_KR_m : pe_from_KR_m_stmt.
Proof.
unfold pe_from_KR_m_stmt. intros m RKI cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo (HGI & HM).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGI as (b & h & buf & i & p & e & HCUT & Hn26 & Hgood & Hi0 & Hip & HKF & Hpe & Hskips & He16 &
                 Rs2 & Rs4 & Rs5 & Rs6 & Rs7 & Rs8 & Rs10 & Hlslots & Hcalls & Hnslot & Hfirst & Hglob & Hrd).
destruct HCUT as (HBody & Hk & Hacc & HPerm & Hfds & Hfs).
destruct Hlslots as (Hslots & Hbuf & Hvmask & Hbuf12 & Husec).
pose proof HJ as HJ0.
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
destruct (w3_blocks3 cx ly3 S3 W3 ms3 md3 b h buf HAR3 HPerm) as (Hinb & Hb1 & Hb2 & Hh1 & Hh2 & Hu1 & Hu2).
pose proof HBody as (_ & _ & _ & _ & _ & _ & (P2 & P8 & P9 & P3 & P4) & _).
pose proof Hslots as (Q144 & Q24 & Q72 & Q40 & Q32 & Q16 & Q88 & Q120).
pose proof (p_sizes cx) as (Z1 & Z2 & Z3). pose proof (p_d_range cx) as Zd.
pose proof (w3_good_len cx Hgood) as Hgl.
pose proof (w3_swz_range cx) as Hswz.
destruct Hrd as (Hsrc & Hpso & Hfit).
destruct (Hfit HKF) as (Vorig & Vtag & Vvid & Vts & Vbuf).
destruct Hpso as (Vf & Vsw).
assert (Hcopy : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) b (p_C cx)).
{ destruct Hsrc as (Wn & cpos & fl & md & Hq). cbv zeta in Hq. tauto. }
set (orig := PSN.orig (p_sw cx) (p_F cx) (p_q cx p)).
set (ex := w3_extra2 b h buf (p_cap cx) (p_nF cx) (p_d cx) (pF cx fp) (pSH cx fp)
             (p_first cx mod 2 ^ 64) (i + 1) (p_res cx (p_q cx p)) (p_swz cx) orig).
set (E := Eimg (Ereg (ms_regs ms3) ex)).
assert (EReg : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EXn : forall j, (j < 14)%nat ->
   ew E (32 + j)%nat = Z_to_bv 64
     (nth j [SB_W; b; h; buf; p_cap cx; p_nF cx; p_d cx; pF cx fp; pSH cx fp; p_first cx mod 2 ^ 64;
             i + 1; p_res cx (p_q cx p); p_swz cx; orig] 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra (ms_regs ms3) ex j). subst ex. unfold w3_extra2. apply map_nth. }
assert (E35 : ew E 35%nat = Z_to_bv 64 buf)
  by (pose proof (EXn 3%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E36 : ew E 36%nat = Z_to_bv 64 (p_cap cx))
  by (pose proof (EXn 4%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E38 : ew E 38%nat = Z_to_bv 64 (p_d cx))
  by (pose proof (EXn 6%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E39 : ew E 39%nat = Z_to_bv 64 (pF cx fp))
  by (pose proof (EXn 7%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E40 : ew E 40%nat = Z_to_bv 64 (pSH cx fp))
  by (pose proof (EXn 8%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E41 : ew E 41%nat = Z_to_bv 64 (p_first cx mod 2 ^ 64))
  by (pose proof (EXn 9%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E42 : ew E 42%nat = Z_to_bv 64 (i + 1))
  by (pose proof (EXn 10%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E43 : ew E 43%nat = Z_to_bv 64 (p_res cx (p_q cx p)))
  by (pose proof (EXn 11%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E44 : ew E 44%nat = Z_to_bv 64 (p_swz cx))
  by (pose proof (EXn 12%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E45 : ew E 45%nat = Z_to_bv 64 orig)
  by (pose proof (EXn 13%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E9 : bv_unsigned (ew E 9%nat) = c_sp1 cx)
  by (rewrite (EReg 9%nat (9%bv : bv 5) eq_refl), P9; apply unsigned_lit_small; lia).
assert (E18 : ew E 18%nat = Z_to_bv 64 b) by (rewrite (EReg 18%nat (18%bv : bv 5) eq_refl); exact Rs2).
assert (E20 : ew E 20%nat = Z_to_bv 64 (pPS cx fp)) by (rewrite (EReg 20%nat (20%bv : bv 5) eq_refl); exact Rs4).
assert (E21 : ew E 21%nat = Z_to_bv 64 (-8)) by (rewrite (EReg 21%nat (21%bv : bv 5) eq_refl); exact Rs5).
assert (E23 : ew E 23%nat = Z_to_bv 64 (- b - 1)) by (rewrite (EReg 23%nat (23%bv : bv 5) eq_refl); exact Rs7).
assert (E26 : ew E 26%nat = Z_to_bv 64 e) by (rewrite (EReg 26%nat (26%bv : bv 5) eq_refl); exact Rs10).
assert (Horig : 0 <= orig < 2 ^ 32) by (subst orig; exact (w3_hw_range (p_sw cx) (p_F cx) (p_q cx p) 12)).
assert (Hres : 0 < p_res cx (p_q cx p) <= p_cap cx)
  by (destruct (w3_K4_facts cx p Hgood ltac:(lia) HKF) as (_ & Hq & _); exact Hq).
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) cs_KR).
{ unfold cs_KR. repeat apply Forall_cons; try apply Forall_nil.
  - apply (w3_chunk_slot E W3 ms3 cx 16 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q16].
  - apply (w3_chunk_slot E W3 ms3 cx 24 (SOff 38 0) (p_d cx));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_d in *; lia | exact Q24].
  - apply (w3_chunk_slot E W3 ms3 cx 32 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q32].
  - apply (w3_chunk_slot E W3 ms3 cx 40 (SOff 40 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q40].
  - apply (w3_chunk_slot E W3 ms3 cx 48 (SLit 3840) 3840); [reflexivity | lia | exact Hvmask].
  - apply (w3_chunk_slot E W3 ms3 cx 56 (SOff 35 12) (buf + 12));
    [cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity | lia | exact Hbuf12].
  - apply (w3_chunk_slot E W3 ms3 cx 64 (SLit 4294967296000000) (1000000 * 2 ^ 32));
    [reflexivity | lia | exact Husec].
  - apply (w3_chunk_slot E W3 ms3 cx 72 (SLit SHADOW_OFF) SHADOW_OFF);
    [reflexivity | unfold SHADOW_OFF; lia | exact Q72].
  - apply (w3_chunk_slot E W3 ms3 cx 80 (SOff 41 0) (p_first cx mod 2 ^ 64));
    [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia | exact Hfirst].
  - apply (w3_chunk_slot E W3 ms3 cx 88 (SOff 39 96) (pF cx fp + PO_TS));
    [cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity | unfold PO_TS; lia
    | exact Q88].
  - apply (w3_chunk_slot E W3 ms3 cx 96 (SOff 35 0) buf);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hbuf].
  - apply (w3_chunk_slot E W3 ms3 cx 104 (SOff 42 0) (i + 1));
    [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hcalls].
  - apply (w3_chunk_slot E W3 ms3 cx 112 (SOff 43 0) (p_res cx (p_q cx p)));
    [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hnslot].
  - apply (w3_chunk_slot E W3 ms3 cx 120 (SOff 36 0) (p_cap cx));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_cap, p_d in *; lia
    | unfold p_cap, p_d; exact Q120].
  - apply (w3_chunk_slot E W3 ms3 cx 144 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q144]. }
assert (HPS : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (ps_region (SOff 44 0) (SOff 45 0))).
{ unfold ps_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E20, unsigned_lit_small by (unfold pPS, PO_PS; lia).
  split; [unfold pPS, PO_PS; lia|]. split; [unfold pPS, PO_PS; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS E _ (pPS cx fp) 8 4 (SOff 44 0) (p_swz cx));
    [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact Vsw].
  - apply (chunk_ok_val SEGS E _ (pPS cx fp) 12 4 (SOff 45 0) orig);
    [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact Vorig]. }
assert (HG : gx_ok SEGS B pe_G)
  by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hq&_); exact Hq).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (U18 : bv_unsigned (ew E 18%nat) = b) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20%nat) = pPS cx fp)
  by (rewrite E20; apply unsigned_lit_small; unfold pPS, PO_PS; lia).
assert (U21 : bv_unsigned (ew E 21%nat) = 2 ^ 64 - 8)
  by (rewrite E21, unsigned_lit; unfold zcanon, M64; symmetry; apply (Z.mod_unique _ _ (-1)); lia).
assert (U23 : bv_unsigned (ew E 23%nat) = 2 ^ 64 - 1 - b)
  by (rewrite E23, unsigned_lit; unfold zcanon, M64; symmetry; apply (Z.mod_unique _ _ (-1)); lia).
assert (U26 : bv_unsigned (ew E 26%nat) = e) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35%nat) = buf) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36%nat) = p_cap cx) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38%nat) = p_d cx) by (rewrite E38; apply unsigned_lit_small; unfold p_d in *; lia).
assert (U39 : bv_unsigned (ew E 39%nat) = pF cx fp) by (rewrite E39; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E 40%nat) = pSH cx fp) by (rewrite E40; apply unsigned_lit_small; lia).
assert (U41 : bv_unsigned (ew E 41%nat) = p_first cx mod 2 ^ 64)
  by (rewrite E41; apply unsigned_lit_small; pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia).
assert (U42 : bv_unsigned (ew E 42%nat) = i + 1) by (rewrite E42; apply unsigned_lit_small; lia).
assert (U43 : bv_unsigned (ew E 43%nat) = p_res cx (p_q cx p)) by (rewrite E43; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E 44%nat) = p_swz cx) by (rewrite E44; apply unsigned_lit_small; lia).
assert (HATOMS : atoms_ok E fl_KR).
{ unfold fl_KR. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U20, U21, U23, U26, U44. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold pPS, PO_PS in *; lia]. }
destruct (w3_entry cx fp PP_KR PSH_ts [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0)] fl_KR [] ex
            ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody ltac:(subst ex; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(apply Forall_cons; [|apply Forall_cons; [exact HPS | apply Forall_nil]];
                  apply (w3_slots_ok E W3 ms3 cx cs_KR E9 ltac:(lia)); [|exact HCS];
                  intros a Ha; apply Hpres; change LLVMF_STK with 32768; split; lia)
            ltac:(apply pairwise_disjoint_of_extents;
                  unfold slots_region, ps_region, extent_of_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi];
                  cbn [base_val]; fold E; rewrite E9, U20;
                  cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
                  repeat split; unfold pPS, PO_PS in *; lia)
            HATOMS I) as [HS SHOK].
pose proof (w3_RUN pe_G HG 0 []) as RUN.
pose proof (paj_branch (PI:=PI)) as BR.
fold E in HS, SHOK.
assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
{ cbn [restrict ms_regs]. rewrite Rs8. cbn [sv_denot]. subst E.
  rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
  rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia). rewrite Z.add_0_r. reflexivity. }
pose proof (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS eq_refl HS8) as HSp.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSp. clear HS. rename HSp into HS.
paj_run_tok RUN HS HJ SHOK Wspan.
{ w3_awr E9. }
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
prreg HS (24%bv : bv 5) T24. prreg HS (26%bv : bv 5) T26.
rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
assert (HKEEP1 : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
{ intros a Ha Hn.
  refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
  intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
  destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
  destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
  destruct Hinw. }
assert (Hms : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_rd32)) (ms_mem ms) (seg_rom SEGS)).
{ rewrite <- pa_sigma_rd32. exact (w3_shape_call E _ _ W3 _ HS eq_refl). }
assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite T2, P2; apply unsigned_lit_small; lia).
assert (Hbytes : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (b + (e + 8))
                   [PSN.fb (p_F cx) (e + 8); PSN.fb (p_F cx) (e + 8 + 1);
                    PSN.fb (p_F cx) (e + 8 + 2); PSN.fb (p_F cx) (e + 8 + 3)]).
{ apply (w3_bytes4 cx _ b (e + 8)); [|lia|lia].
  apply (w3_garr_lo (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms) b (p_C cx) HKEEP1 ltac:(lia) ltac:(lia)
           ltac:(rewrite w3_C_len; lia) Hcopy). }
assert (HJms : ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
                 (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms)
                 (with_vm_backing (m_vm_lazy md3) mat md3) k) by exact HJ.
assert (Ha0c : getr (ms_regs ms) 10 = w64 (b + (e + 8))).
{ rewrite T10. rewrite (w3_alu_add _ _ (b + 8) e); [f_equal; lia | | exact U26].
  rewrite U18. apply unsigned_lit_small. lia. }
rewrite Hms. eapply SRr_bind.
{ exact (w3_rd32_call LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
           [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k (ms_regs ms)
           (b + (e + 8)) b (p_nF cx) _ _ _ _ HJms
           ltac:(rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity])
           Ha0c
           ltac:(rewrite Hsp; pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)); lia)
           ltac:(rewrite Hsp; unfold RD32_FRAME, LLVMF_STK; lia)
           ltac:(rewrite Hsp; lia) Hinb ltac:(lia) ltac:(lia) Hbytes). }
cbv beta. intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPres2 & Ha0 & Hsame2 & UN2).
rewrite Hsp in UN2. unfold RD32_FRAME in UN2.
assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) mem2)
  by (apply (w3_keep_trans (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms) mem2 HKEEP1);
      apply (w3_keepf_weak (c_sp1 cx) W3 (ms_mem ms) mem2); exact UN2).
pose proof (w3_region0_call E _ _ _ _ _ HS eq_refl) as HRg.
destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
            ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
destruct (same_but_materialized_fs (with_vm_backing (m_vm_lazy md3) mat md3) md2 Hsame2) as (Hfd2 & Hfs2).
assert (K2 : getr regs2 2 = getr (ms_regs ms) 2) by (apply (HPres2 2); unfold acallee_saved; lia).
assert (K3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HPres2 3); unfold acallee_saved; lia).
assert (K4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HPres2 4); unfold acallee_saved; lia).
assert (K8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HPres2 8); unfold acallee_saved; lia).
assert (K9 : getr regs2 9 = getr (ms_regs ms) 9) by (apply (HPres2 9); unfold acallee_saved; lia).
assert (K18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HPres2 18); unfold acallee_saved; lia).
assert (K19 : getr regs2 19 = getr (ms_regs ms) 19) by (apply (HPres2 19); unfold acallee_saved; lia).
assert (K20 : getr regs2 20 = getr (ms_regs ms) 20) by (apply (HPres2 20); unfold acallee_saved; lia).
assert (K21 : getr regs2 21 = getr (ms_regs ms) 21) by (apply (HPres2 21); unfold acallee_saved; lia).
assert (K22 : getr regs2 22 = getr (ms_regs ms) 22) by (apply (HPres2 22); unfold acallee_saved; lia).
assert (K23 : getr regs2 23 = getr (ms_regs ms) 23) by (apply (HPres2 23); unfold acallee_saved; lia).
assert (K24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HPres2 24); unfold acallee_saved; lia).
assert (K26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HPres2 26); unfold acallee_saved; lia).
assert (Hregs2 : pregs cx (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS))).
{ unfold pregs, mkst; cbn [ms_regs]; split; [|split; [|split; [|split]]].
  - rewrite K2, T2.
    exact P2.
  - rewrite K8, T8.
    exact P8.
  - rewrite K9, T9.
    exact P9.
  - rewrite K3, T3.
    exact P3.
  - rewrite K4, T4.
    exact P4. }
pose proof (w3_body_keep cx fp PP_KR PP_KRI PSH_ts ly3 S3 W3 ms3 md3 k (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) HB HJ0 Hfrs HBody
              ltac:(unfold mkst; cbn [ms_pc_val]; rewrite T1; reflexivity)
              eq_refl eq_refl eq_refl eq_refl eq_refl Hregs2 HKEEP) as HBodyI.
apply (RKI cx fp k acc ly3 S3 W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrs Hmo).
assert (T26' : getr regs2 26 = w64 e)
  by (rewrite K26, T26,
      E26; reflexivity).
split; [|unfold mkst; cbn [ms_regs]; rewrite T26', unsigned_lit_small by lia;
         rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; exact HM].
exists b, h, buf, i, p, e.
split; [split; [exact HBodyI|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
        split; [rewrite Hfd2, Hfd1; exact Hfds | rewrite Hfs2, Hfs1; exact Hfs]|].
split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HKF|].
split; [exact Hpe|]. split; [exact Hskips|]. split; [exact He16|].
split.
{ unfold mkst; cbn [ms_regs]. rewrite Ha0, T11, E44. rewrite <- (w3_trd32_hw cx e 8). reflexivity. }
split; [unfold mkst; cbn [ms_regs];
        rewrite K18, T18;
        exact Rs2|].
split.
{ unfold mkst; cbn [ms_regs].
  rewrite K19, T19.
  exact (w3_alu_add _ _ b e U18 U26). }
split; [unfold mkst; cbn [ms_regs];
        rewrite K20, T20;
        exact Rs4|].
split; [unfold mkst; cbn [ms_regs];
        rewrite K21, T21;
        exact Rs5|].
split.
{ unfold mkst; cbn [ms_regs].
  rewrite K22, T22,
    (EReg 22%nat (22%bv : bv 5) eq_refl). exact Rs6. }
split; [unfold mkst; cbn [ms_regs];
        rewrite K23, T23;
        exact Rs7|].
split; [unfold mkst; cbn [ms_regs];
        rewrite K24, T24;
        subst E; change 288%nat with (A_HI 8);
        rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
split; [unfold mkst; cbn [ms_regs]; exact T26'|].
assert (SLOT : forall off v, 16 <= off -> off <= 152 -> pslot cx W3 ms off v -> pslot cx W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) off v).
{ intros off v Ho1 Ho2 Hs. apply (w3_slot_keepf cx W3 ms (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) off v); [|lia|lia|lia|exact Hs].
  intros a Ha Hn. unfold mkst; cbn [ms_mem]. apply UN2; [exact Ha | exact Hn]. }
split.
{ split.
  { split; [apply (SLOT 144 (pF cx fp)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (SLOT 24 (p_d cx)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                    ltac:(unfold p_d in *; lia))|].
    split; [apply (SLOT 72 SHADOW_OFF); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                    eq_refl ltac:(unfold SHADOW_OFF; lia))|].
    split; [apply (SLOT 40 (pSH cx fp)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (SLOT 32 (pF cx fp)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (SLOT 16 (pF cx fp)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (SLOT 88 (pF cx fp + PO_TS)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                    ltac:(unfold PO_TS; lia))|].
    apply (SLOT 120 (p_cap cx)); [lia|lia|].
    apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
             ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
             ltac:(unfold p_cap, p_d in *; lia)). }
  split; [apply (SLOT 96 buf); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (SLOT 48 3840); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
  split; [apply (SLOT 56 (buf + 12)); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
  apply (SLOT 64 (1000000 * 2 ^ 32)); [lia|lia|].
  apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
           eq_refl ltac:(lia)). }
split; [apply (SLOT 104 (i + 1)); [lia|lia|];
        apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 0) (i + 1) HRg E9 ltac:(cbn; tauto)
                ltac:(cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
split; [apply (SLOT 112 (p_res cx (p_q cx p))); [lia|lia|];
        apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
split; [apply (SLOT 80 (p_first cx mod 2 ^ 64)); [lia|lia|];
        apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 41 0) (p_first cx mod 2 ^ 64) HRg E9 ltac:(cbn; tauto)
                ltac:(cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                ltac:(pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia))|].
split; [exact (w3_glob_keep cx W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) b HKEEP ltac:(lia) Hglob)|].
apply (w3_reader_keep cx fp W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) b h buf p ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
         ltac:(lia) Hu2 HF1 HF2).
split; [exact Hsrc|]. split; [exact (conj Vf Vsw)|].
intros _. exact (conj Vorig (conj Vtag (conj Vvid (conj Vts Vbuf)))).
Qed.


Lemma pe_from_KRI_m : pe_from_KRI_m_stmt.
Proof.
unfold pe_from_KRI_m_stmt. intros m RKR RKO cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo (HGI & HM).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HGI as (b & h & buf & i & p & e & HCUT & Hn26 & Hgood & Hi0 & Hip & HKF & Hpe & Hskips & He16 &
                 Ra0 & Rs2 & Rs3 & Rs4 & Rs5 & Rs6 & Rs7 & Rs8 & Rs10 & Hlslots & Hcalls & Hnslot & Hfirst &
                 Hglob & Hrd).
destruct HCUT as (HBody & Hk & Hacc & HPerm & Hfds & Hfs).
destruct Hlslots as (Hslots & Hbuf & Hvmask & Hbuf12 & Husec).
pose proof HJ as HJ0.
destruct (w3_bounds cx fp ly3 S3 W3 ms3 md3 k HB HJ Hfrs)
  as (HF1 & HF2 & HS1 & HS2 & HP1 & HP2 & HAC & Hlo272 & Hhi & Hsp47 & (Hsp1a & Hsp1b) & Hal32 & Hpres & HAR3 & Hin & HEF & HOFF).
destruct (w3_blocks3 cx ly3 S3 W3 ms3 md3 b h buf HAR3 HPerm) as (Hinb & Hb1 & Hb2 & Hh1 & Hh2 & Hu1 & Hu2).
pose proof HBody as (_ & _ & _ & _ & _ & _ & (P2 & P8 & P9 & P3 & P4) & _).
pose proof Hslots as (Q144 & Q24 & Q72 & Q40 & Q32 & Q16 & Q88 & Q120).
pose proof (p_sizes cx) as (Z1 & Z2 & Z3). pose proof (p_d_range cx) as Zd.
pose proof (w3_good_len cx Hgood) as Hgl.
pose proof (w3_swz_range cx) as Hswz.
destruct Hrd as (Hsrc & Hpso & Hfitb).
destruct (Hfitb HKF) as (Vorig & Vtag & Vvid & Vts & Vbuf).
destruct Hpso as (Vf & Vsw).
assert (Hcopy : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms3)) b (p_C cx))
  by (destruct Hsrc as (Wn & cpos & fl & md & Hq); cbv zeta in Hq; tauto).
assert (Hres : 0 < p_res cx (p_q cx p) <= p_cap cx)
  by (destruct (w3_K4_facts cx p Hgood ltac:(lia) HKF) as (_ & Hq & _); exact Hq).
assert (Hincl : 0 <= PSN.incl (p_sw cx) (p_F cx) e < 2 ^ 32) by exact (w3_hw_range (p_sw cx) (p_F cx) e 8).
destruct (w3_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HKF) as (HQi & HQfit & HQ16).
pose proof (w3_skips_ge (p_sw cx) (p_F cx) (p_cap cx) e (p_q cx p) Hskips) as HeQ.
set (ex := w3_extra3 b h buf (p_cap cx) (p_nF cx) (p_d cx) (pF cx fp) (pSH cx fp)
             (p_first cx mod 2 ^ 64) (i + 1) (p_res cx (p_q cx p)) (p_swz cx) (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)) (bv_swrap 32 (p_hw cx e 8))).
set (E := Eimg (Ereg (ms_regs ms3) ex)).
assert (EReg : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. unfold bv_modulus in Hr5. cbn in Hr5.
  subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EXn : forall j, (j < 15)%nat ->
   ew E (32 + j)%nat = Z_to_bv 64
     (nth j [SB_W; b; h; buf; p_cap cx; p_nF cx; p_d cx; pF cx fp; pSH cx fp; p_first cx mod 2 ^ 64;
             i + 1; p_res cx (p_q cx p); p_swz cx; (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)); (bv_swrap 32 (p_hw cx e 8))] 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra (ms_regs ms3) ex j). subst ex. unfold w3_extra3. apply map_nth. }
assert (E35 : ew E 35%nat = Z_to_bv 64 buf)
  by (pose proof (EXn 3%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E36 : ew E 36%nat = Z_to_bv 64 (p_cap cx))
  by (pose proof (EXn 4%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E37 : ew E 37%nat = Z_to_bv 64 (p_nF cx))
  by (pose proof (EXn 5%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E38 : ew E 38%nat = Z_to_bv 64 (p_d cx))
  by (pose proof (EXn 6%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E39 : ew E 39%nat = Z_to_bv 64 (pF cx fp))
  by (pose proof (EXn 7%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E40 : ew E 40%nat = Z_to_bv 64 (pSH cx fp))
  by (pose proof (EXn 8%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E41 : ew E 41%nat = Z_to_bv 64 (p_first cx mod 2 ^ 64))
  by (pose proof (EXn 9%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E42 : ew E 42%nat = Z_to_bv 64 (i + 1))
  by (pose proof (EXn 10%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E43 : ew E 43%nat = Z_to_bv 64 (p_res cx (p_q cx p)))
  by (pose proof (EXn 11%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E44 : ew E 44%nat = Z_to_bv 64 (p_swz cx))
  by (pose proof (EXn 12%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E45 : ew E 45%nat = Z_to_bv 64 (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)))
  by (pose proof (EXn 13%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E46 : ew E 46%nat = Z_to_bv 64 (bv_swrap 32 (p_hw cx e 8)))
  by (pose proof (EXn 14%nat ltac:(lia)) as Hq; cbn [nth Nat.add] in Hq; exact Hq).
assert (E9 : bv_unsigned (ew E 9%nat) = c_sp1 cx)
  by (rewrite (EReg 9%nat (9%bv : bv 5) eq_refl), P9; apply unsigned_lit_small; lia).
assert (E18 : ew E 18%nat = Z_to_bv 64 b) by (rewrite (EReg 18%nat (18%bv : bv 5) eq_refl); exact Rs2).
assert (E19 : ew E 19%nat = Z_to_bv 64 (b + e)) by (rewrite (EReg 19%nat (19%bv : bv 5) eq_refl); exact Rs3).
assert (E20 : ew E 20%nat = Z_to_bv 64 (pPS cx fp)) by (rewrite (EReg 20%nat (20%bv : bv 5) eq_refl); exact Rs4).
assert (E21 : ew E 21%nat = Z_to_bv 64 (-8)) by (rewrite (EReg 21%nat (21%bv : bv 5) eq_refl); exact Rs5).
assert (E22 : ew E 22%nat = Z_to_bv 64 (e + 16)) by (rewrite (EReg 22%nat (22%bv : bv 5) eq_refl); exact Rs6).
assert (E23 : ew E 23%nat = Z_to_bv 64 (- b - 1)) by (rewrite (EReg 23%nat (23%bv : bv 5) eq_refl); exact Rs7).
assert (E26 : ew E 26%nat = Z_to_bv 64 e) by (rewrite (EReg 26%nat (26%bv : bv 5) eq_refl); exact Rs10).
assert (Horig : 0 <= (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)) < 2 ^ 32) by exact (w3_hw_range (p_sw cx) (p_F cx) (p_q cx p) 12).
assert (HZX : U E W3ZX = PSN.incl (p_sw cx) (p_F cx) e).
{ unfold W3ZX. apply (w3_zext32 E 46%nat); [rewrite E46; reflexivity | exact Hincl]. }
assert (U18 : bv_unsigned (ew E 18%nat) = b) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19%nat) = b + e) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20%nat) = pPS cx fp)
  by (rewrite E20; apply unsigned_lit_small; unfold pPS, PO_PS; lia).
assert (U21 : bv_unsigned (ew E 21%nat) = 2 ^ 64 - 8)
  by (rewrite E21, unsigned_lit; unfold zcanon, M64; symmetry; apply (Z.mod_unique _ _ (-1)); lia).
assert (U22 : bv_unsigned (ew E 22%nat) = e + 16) by (rewrite E22; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23%nat) = 2 ^ 64 - 1 - b)
  by (rewrite E23, unsigned_lit; unfold zcanon, M64; symmetry; apply (Z.mod_unique _ _ (-1)); lia).
assert (U26 : bv_unsigned (ew E 26%nat) = e) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36%nat) = p_cap cx) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37%nat) = p_nF cx) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E 44%nat) = p_swz cx) by (rewrite E44; apply unsigned_lit_small; lia).
assert (U46 : bv_unsigned (ew E 46%nat) = zcanon (bv_swrap 32 (p_hw cx e 8))) by (rewrite E46; apply unsigned_lit).
assert (HCS : Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (c_sp1 cx)) cs_KR).
{ unfold cs_KR. repeat apply Forall_cons; try apply Forall_nil.
  - apply (w3_chunk_slot E W3 ms3 cx 16 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q16].
  - apply (w3_chunk_slot E W3 ms3 cx 24 (SOff 38 0) (p_d cx));
    [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_d in *; lia | exact Q24].
  - apply (w3_chunk_slot E W3 ms3 cx 32 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q32].
  - apply (w3_chunk_slot E W3 ms3 cx 40 (SOff 40 0) (pSH cx fp));
    [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q40].
  - apply (w3_chunk_slot E W3 ms3 cx 48 (SLit 3840) 3840); [reflexivity | lia | exact Hvmask].
  - apply (w3_chunk_slot E W3 ms3 cx 56 (SOff 35 12) (buf + 12));
    [cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity | lia | exact Hbuf12].
  - apply (w3_chunk_slot E W3 ms3 cx 64 (SLit 4294967296000000) (1000000 * 2 ^ 32));
    [reflexivity | lia | exact Husec].
  - apply (w3_chunk_slot E W3 ms3 cx 72 (SLit SHADOW_OFF) SHADOW_OFF);
    [reflexivity | unfold SHADOW_OFF; lia | exact Q72].
  - apply (w3_chunk_slot E W3 ms3 cx 80 (SOff 41 0) (p_first cx mod 2 ^ 64));
    [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia | exact Hfirst].
  - apply (w3_chunk_slot E W3 ms3 cx 88 (SOff 39 96) (pF cx fp + PO_TS));
    [cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity | unfold PO_TS; lia
    | exact Q88].
  - apply (w3_chunk_slot E W3 ms3 cx 96 (SOff 35 0) buf);
    [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hbuf].
  - apply (w3_chunk_slot E W3 ms3 cx 104 (SOff 42 0) (i + 1));
    [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hcalls].
  - apply (w3_chunk_slot E W3 ms3 cx 112 (SOff 43 0) (p_res cx (p_q cx p)));
    [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Hnslot].
  - apply (w3_chunk_slot E W3 ms3 cx 120 (SOff 36 0) (p_cap cx));
    [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold p_cap, p_d in *; lia
    | unfold p_cap, p_d; exact Q120].
  - apply (w3_chunk_slot E W3 ms3 cx 144 (SOff 39 0) (pF cx fp));
    [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | exact Q144]. }
assert (HPS : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (ps_region (SOff 44 0) (SOff 45 0))).
{ unfold ps_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U20.
  split; [unfold pPS, PO_PS; lia|]. split; [unfold pPS, PO_PS; lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_ok_val SEGS E _ (pPS cx fp) 8 4 (SOff 44 0) (p_swz cx));
    [cbn [sv_denot]; rewrite E44, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact Vsw].
  - apply (chunk_ok_val SEGS E _ (pPS cx fp) 12 4 (SOff 45 0) (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)));
    [cbn [sv_denot]; rewrite E45, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | cbn; lia | exact Vorig]. }
assert (Eobj4 : bv_unsigned (ew E (A_OBJ 4)) = pa_val (A_OBJ 4)).
{ subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  apply unsigned_lit_small. pose proof (pa_val_range (A_OBJ 4)). lia. }
pose proof (pa_obj_img 4 ltac:(lia)) as O4. assert (HIE : pcap_img_end = (symaddr ImgPages.AsanUbsan.top)) by reflexivity.
assert (HGL : region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)) (glen_region (SOff 37 0))).
{ unfold glen_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Eobj4.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (pa_val (A_OBJ 4)) 0 8 (SOff 37 0) (p_nF cx));
  [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia |].
  rewrite Z.add_0_r. exact (proj2 Hglob). }
assert (HATOMS : atoms_ok E fl_KRI).
{ unfold fl_KRI. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U19, U20, U21, U23, U26, U36, U37, U44. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | unfold pPS, PO_PS in *; lia]. }
assert (HG : gx_ok SEGS B pe_G)
  by (destruct HB as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hq&_); exact Hq).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HREG : regions_wf [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0); glen_region (SOff 37 0)] = true)
  by (vm_compute; reflexivity).
assert (HRS : Forall (region_ok SEGS E (mrestrict (w_H W3) (ms_mem ms3)))
                [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0); glen_region (SOff 37 0)]).
{ apply Forall_cons; [|apply Forall_cons; [exact HPS | apply Forall_cons; [exact HGL | apply Forall_nil]]].
  apply (w3_slots_ok E W3 ms3 cx cs_KR E9 ltac:(lia)); [|exact HCS].
  intros a Ha. apply Hpres. change LLVMF_STK with 32768. split; lia. }
assert (HPD : pairwise_disjoint E [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0); glen_region (SOff 37 0)]).
{ apply pairwise_disjoint_of_extents.
  unfold slots_region, ps_region, glen_region, extent_of_region. cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  cbn [base_val]. rewrite E9, U20, Eobj4.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; unfold pPS, PO_PS, pcap_img_end, YImgTop.IMG_TOP in *; lia. }

assert (D46 : bv_unsigned (sv_denot E (SOff 46 0)) = zcanon (bv_swrap 32 (p_hw cx e 8)))
  by (rewrite denot_SOff, E46, Z.add_0_r, unsigned_lit; unfold zcanon, M64; apply Zmod_mod).
assert (D0 : bv_unsigned (sv_denot E (SLit 0)) = 0) by (cbn [sv_denot]; apply unsigned_lit_small; lia).
assert (DZX : bv_unsigned (sv_denot E W3ZX) = PSN.incl (p_sw cx) (p_F cx) e) by exact HZX.
assert (D37 : bv_unsigned (sv_denot E (SOff 37 0)) = p_nF cx)
  by (rewrite denot_SOff, Z.add_0_r, U37; apply zcanon_id; unfold M64; lia).
assert (D36 : bv_unsigned (sv_denot E (SOff 36 0)) = p_cap cx)
  by (rewrite denot_SOff, Z.add_0_r, U36; apply zcanon_id; unfold M64; lia).
assert (Dbk : bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 26 0) W3ZX) (SLit 32))) =
              e + PSN.incl (p_sw cx) (p_F cx) e + 32).
{ change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 26 0) W3ZX) (SLit 32))))
    with (U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 26 0) W3ZX) (SLit 32))).
  rewrite !U_SAlu. cbn [zalu_raw]. rewrite HZX, (U_atom E 26%nat e E26 ltac:(lia)), (U_lit E 32 ltac:(lia)).
  rewrite (zcanon_id (e + PSN.incl (p_sw cx) (p_F cx) e)) by (unfold M64; lia).
  apply zcanon_id. unfold M64. lia. }
assert (Dfa : bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 22 0) W3ZX)) =
              e + 16 + PSN.incl (p_sw cx) (p_F cx) e).
{ change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 22 0) W3ZX)))
    with (U E (SAlu ALU_ADD (SOff 22 0) W3ZX)).
  rewrite U_SAlu. cbn [zalu_raw]. rewrite HZX, (U_atom E 22%nat (e + 16) E22 ltac:(lia)).
  apply zcanon_id. unfold M64. lia. }
assert (Drdv : zcanon (bv_swrap 32 (p_hw cx e 8)) = PSN.incl (p_sw cx) (p_F cx) e +
                 (if PSN.incl (p_sw cx) (p_F cx) e <? 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32))
  by (apply rd_sx32; exact Hincl).

destruct (w3_kri_tri cx e (p_q cx p) Hskips HKF) as [HKe0 | [HKe0 | (HeQq & HKe0)]].
- (* KEmpty: incl = 0, the back edge to PP_KR at e + 16 *)
  destruct (proj1 (w3_kind_vals cx e) HKe0) as (Hi0z & H16e).
  assert (Hne : e <> p_q cx p) by (intros Hq; rewrite Hq, HKF in HKe0; discriminate).
  assert (HCDS : conds_ok E cds_empty).
  { unfold cds_empty. cbn [conds_ok].
    split; [|split; [|exact I]]; unfold acond_ok; cbn [ac_c ac_a ac_b branch_taken].
    - rewrite bv_eqb_unsigned, D46, D0, Drdv, Hi0z. reflexivity.
    - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge. rewrite D37, Dbk.
      pose proof (w3_skips_ge (p_sw cx) (p_F cx) (p_cap cx) (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_q cx p)
                    (proj1 (proj2 (w3_skip_step cx e (p_q cx p) Hskips HKF Hne)))).
      unfold PSN.flen, p_nF in *. lia. }

  destruct (w3_skip_step cx e (p_q cx p) Hskips HKF Hne) as (_ & Hskips2 & He2Q).
  destruct (w3_entry cx fp PP_KRI PSH_ts [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0);
              glen_region (SOff 37 0)] fl_KRI cds_empty ex ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody
              ltac:(subst ex; reflexivity) HREG HRS HPD HATOMS HCDS) as [HS SHOK].
  pose proof (w3_RUNTO pe_G HG 0 []) as RUNTO.
  fold E in HS, SHOK.
  assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
  { cbn [restrict ms_regs]. rewrite Rs8. cbn [sv_denot]. subst E.
    rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
    rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia). rewrite Z.add_0_r. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS eq_refl HS8) as HSp.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSp. clear HS. rename HSp into HS.
  assert (HS10 : sv_denot E (SOff 46 0) = getr (ms_regs (restrict (w_H W3) ms3)) 10).
  { cbn [restrict ms_regs]. rewrite Ra0. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 46 0) HS eq_refl HS10) as HSq.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. clear HS. rename HSq into HS.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_KR.
  { w3_awr E9. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_KRI PP_KR PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBodyR.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
  assert (HZXa : alu64 ALU_SRL (alu64 ALU_SLL (ew E 46%nat) (Z_to_bv 64 32)) (Z_to_bv 64 32)
                 = w64 (PSN.incl (p_sw cx) (p_F cx) e)).
  { apply (w3_zx_alu _ (PSN.incl (p_sw cx) (p_F cx) e)); [|exact Hincl].
    rewrite E46. rewrite unsigned_lit. reflexivity. }
  assert (HT26 : getr (ms_regs ms) 26 = w64 (e + 16 + PSN.incl (p_sw cx) (p_F cx) e)).
  { rewrite T26, HZXa,
      (w3_alu_add (ew E 26%nat) (w64 (PSN.incl (p_sw cx) (p_F cx) e)) e (PSN.incl (p_sw cx) (p_F cx) e) U26
         ltac:(unfold w64; apply unsigned_lit_small; lia)),
      (w3_alu_add (w64 (e + PSN.incl (p_sw cx) (p_F cx) e)) (Z_to_bv 64 16)
         (e + PSN.incl (p_sw cx) (p_F cx) e) 16
         ltac:(unfold w64; apply unsigned_lit_small; lia) ltac:(apply unsigned_lit_small; lia)).
    f_equal. lia. }
  apply (RKR cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB HJ Hfrs Hmo).
  split; [|rewrite HT26, unsigned_lit_small by lia;
           rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; lia].
  exists b, h, buf, i, p, (e + 16 + PSN.incl (p_sw cx) (p_F cx) e).
  split; [split; [exact HBodyR|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite Hfd1; exact Hfds | rewrite Hfs1; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HKF|].
  split; [lia|]. split; [exact Hskips2|]. split; [unfold PSN.flen, p_nF in *; lia|].
  split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|]. split; [rewrite T21; exact Rs5|].
  split.
  { rewrite T22, HZXa,
      (w3_alu_add (ew E 26%nat) (w64 (PSN.incl (p_sw cx) (p_F cx) e)) e (PSN.incl (p_sw cx) (p_F cx) e) U26
         ltac:(unfold w64; apply unsigned_lit_small; lia)),
      (w3_alu_add (w64 (e + PSN.incl (p_sw cx) (p_F cx) e)) (Z_to_bv 64 32)
         (e + PSN.incl (p_sw cx) (p_F cx) e) 32
         ltac:(unfold w64; apply unsigned_lit_small; lia) ltac:(apply unsigned_lit_small; lia)).
    f_equal. lia. }
  split; [rewrite T23; exact Rs7|].
  split; [rewrite T24; subst E; change 288%nat with (A_HI 8);
          rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
  split; [exact HT26|].
  split.
  { split.
    { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 0) (i + 1) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 41 0) (p_first cx mod 2 ^ 64) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  apply (w3_reader_keep cx fp W3 ms3 ms b h buf p ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2).
  split; [exact Hsrc|]. split; [exact (conj Vf Vsw)|].
  intros _. exact (conj Vorig (conj Vtag (conj Vvid (conj Vts Vbuf)))).
- (* KBig: cap < incl, the back edge to PP_KR at e + 16 + incl *)
  destruct (proj2 (w3_kind_vals cx e) HKe0) as (Hcapi & Hfite & H16e).
  assert (Hne : e <> p_q cx p) by (intros Hq; rewrite Hq, HKF in HKe0; discriminate).
  assert (HCDS : conds_ok E cds_big).
  { unfold cds_big. cbn [conds_ok].
    split; [|split; [|split; [|exact I]]]; unfold acond_ok; cbn [ac_c ac_a ac_b branch_taken].
    - rewrite negb_true_iff, bv_eqb_unsigned, D46, D0, Drdv.
      apply Z.eqb_neq. destruct (Z.ltb_spec (PSN.incl (p_sw cx) (p_F cx) e) (2 ^ 31)); lia.
    - rewrite bv_ltu_unsigned. apply Z.ltb_lt. rewrite D36, DZX. lia.
    - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge. rewrite D37, Dbk.
      pose proof (w3_skips_ge (p_sw cx) (p_F cx) (p_cap cx) (e + 16 + PSN.incl (p_sw cx) (p_F cx) e) (p_q cx p)
                    (proj1 (proj2 (w3_skip_step cx e (p_q cx p) Hskips HKF Hne)))).
      unfold PSN.flen, p_nF in *. lia. }

  destruct (w3_skip_step cx e (p_q cx p) Hskips HKF Hne) as (_ & Hskips2 & He2Q).
  destruct (w3_entry cx fp PP_KRI PSH_ts [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0);
              glen_region (SOff 37 0)] fl_KRI cds_big ex ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody
              ltac:(subst ex; reflexivity) HREG HRS HPD HATOMS HCDS) as [HS SHOK].
  pose proof (w3_RUNTO pe_G HG 0 []) as RUNTO.
  fold E in HS, SHOK.
  assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
  { cbn [restrict ms_regs]. rewrite Rs8. cbn [sv_denot]. subst E.
    rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
    rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia). rewrite Z.add_0_r. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS eq_refl HS8) as HSp.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSp. clear HS. rename HSp into HS.
  assert (HS10 : sv_denot E (SOff 46 0) = getr (ms_regs (restrict (w_H W3) ms3)) 10).
  { cbn [restrict ms_regs]. rewrite Ra0. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 46 0) HS eq_refl HS10) as HSq.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. clear HS. rename HSq into HS.
  paj_run_to_tok RUNTO HS HJ SHOK Wspan PP_KR.
  { w3_awr E9. }
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw. }
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
  prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (18%bv : bv 5) T18. prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21.
  prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
  destruct (w3_shape _ _ _ _ HS eq_refl) as (A2 & A4 & A3 & A6 & A1 & A5). cbn [ss_pc] in A2.
  pose proof (w3_region0 _ _ _ _ _ HS eq_refl) as HRg.
  assert (Hregs4 : pregs cx ms) by (split; [rewrite T2; exact P2|]; split; [rewrite T8; exact P8|];
                                    split; [rewrite T9; exact P9|]; split; [rewrite T3; exact P3 | rewrite T4; exact P4]).
  pose proof (w3_body_keep cx fp PP_KRI PP_KR PSH_ts ly3 S3 W3 ms3 md3 k ms HB HJ0 Hfrs HBody
                A2 A4 A3 A6 A1 A5 Hregs4 HKEEP) as HBodyR.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
  assert (HZXa : alu64 ALU_SRL (alu64 ALU_SLL (ew E 46%nat) (Z_to_bv 64 32)) (Z_to_bv 64 32)
                 = w64 (PSN.incl (p_sw cx) (p_F cx) e)).
  { apply (w3_zx_alu _ (PSN.incl (p_sw cx) (p_F cx) e)); [|exact Hincl].
    rewrite E46. rewrite unsigned_lit. reflexivity. }
  assert (HT26 : getr (ms_regs ms) 26 = w64 (e + 16 + PSN.incl (p_sw cx) (p_F cx) e)).
  { rewrite T26, HZXa,
      (w3_alu_add (ew E 26%nat) (w64 (PSN.incl (p_sw cx) (p_F cx) e)) e (PSN.incl (p_sw cx) (p_F cx) e) U26
         ltac:(unfold w64; apply unsigned_lit_small; lia)),
      (w3_alu_add (w64 (e + PSN.incl (p_sw cx) (p_F cx) e)) (Z_to_bv 64 16)
         (e + PSN.incl (p_sw cx) (p_F cx) e) 16
         ltac:(unfold w64; apply unsigned_lit_small; lia) ltac:(apply unsigned_lit_small; lia)).
    f_equal. lia. }
  apply (RKR cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB HJ Hfrs Hmo).
  split; [|rewrite HT26, unsigned_lit_small by lia;
           rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; lia].
  exists b, h, buf, i, p, (e + 16 + PSN.incl (p_sw cx) (p_F cx) e).
  split; [split; [exact HBodyR|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite Hfd1; exact Hfds | rewrite Hfs1; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|]. split; [exact HKF|].
  split; [lia|]. split; [exact Hskips2|]. split; [unfold PSN.flen, p_nF in *; lia|].
  split; [rewrite T18; exact Rs2|]. split; [rewrite T20; exact Rs4|]. split; [rewrite T21; exact Rs5|].
  split.
  { rewrite T22, HZXa,
      (w3_alu_add (ew E 26%nat) (w64 (PSN.incl (p_sw cx) (p_F cx) e)) e (PSN.incl (p_sw cx) (p_F cx) e) U26
         ltac:(unfold w64; apply unsigned_lit_small; lia)),
      (w3_alu_add (w64 (e + PSN.incl (p_sw cx) (p_F cx) e)) (Z_to_bv 64 32)
         (e + PSN.incl (p_sw cx) (p_F cx) e) 32
         ltac:(unfold w64; apply unsigned_lit_small; lia) ltac:(apply unsigned_lit_small; lia)).
    f_equal. lia. }
  split; [rewrite T23; exact Rs7|].
  split; [rewrite T24; subst E; change 288%nat with (A_HI 8);
          rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
  split; [exact HT26|].
  split.
  { split.
    { split; [apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 0) (i + 1) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 41 0) (p_first cx mod 2 ^ 64) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 ms b HKEEP ltac:(lia) Hglob)|].
  apply (w3_reader_keep cx fp W3 ms3 ms b h buf p ASIL HKEEP ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2
           ltac:(lia) Hu2 HF1 HF2).
  split; [exact Hsrc|]. split; [exact (conj Vf Vsw)|].
  intros _. exact (conj Vorig (conj Vtag (conj Vvid (conj Vts Vbuf)))).
- (* KFit: e is the fit record the reader found; the rd32 of its orig_len *)
  assert (HZXa : alu64 ALU_SRL (alu64 ALU_SLL (ew E 46%nat) (Z_to_bv 64 32)) (Z_to_bv 64 32)
                 = w64 (PSN.incl (p_sw cx) (p_F cx) e)).
  { apply (w3_zx_alu _ (PSN.incl (p_sw cx) (p_F cx) e)); [|exact Hincl].
    rewrite E46, unsigned_lit. reflexivity. }
  rewrite HeQq in Ra0, Rs3, Rs6, Rs10, E19, E22, E26, U19, U22, U26, HZX, Hincl, HZXa, Hskips, He16, Hpe, E46,
    D46, DZX, Dbk, Dfa, Drdv, HKe0.
  destruct (w3_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) HKe0) as (Hi1 & Hfitq & H16q).
  assert (HCDS : conds_ok E cds_fit).
  { unfold cds_fit. cbn [conds_ok].
    split; [|split; [|split; [|exact I]]]; unfold acond_ok; cbn [ac_c ac_a ac_b branch_taken].
    - rewrite negb_true_iff, bv_eqb_unsigned, D46, D0, Drdv.
      apply Z.eqb_neq. destruct (Z.ltb_spec (PSN.incl (p_sw cx) (p_F cx) (p_q cx p)) (2 ^ 31)); lia.
    - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge. rewrite D36, DZX. lia.
    - rewrite negb_true_iff, bv_ltu_unsigned. apply Z.ltb_ge. rewrite D37, Dfa.
      unfold PSN.flen, p_nF in *. lia. }
  destruct (w3_entry cx fp PP_KRI PSH_ts [slots_region cs_KR; ps_region (SOff 44 0) (SOff 45 0);
              glen_region (SOff 37 0)] fl_KRI cds_fit ex ly3 S3 W3 ms3 md3 k HB HJ Hfrs HBody
              ltac:(subst ex; reflexivity) HREG HRS HPD HATOMS HCDS) as [HS SHOK].
  pose proof (w3_RUN pe_G HG 0 []) as RUN.
  fold E in HS, SHOK.
  assert (HS8 : sv_denot E (SOff (A_HI 8) 0) = getr (ms_regs (restrict (w_H W3) ms3)) 24).
  { cbn [restrict ms_regs]. rewrite Rs8. cbn [sv_denot]. subst E.
    rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia).
    rewrite unsigned_lit_small by (pose proof (pa_val_range (A_HI 8)); lia). rewrite Z.add_0_r. reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff (A_HI 8) 0) HS eq_refl HS8) as HSp.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSp. clear HS. rename HSp into HS.
  assert (HS10 : sv_denot E (SOff 46 0) = getr (ms_regs (restrict (w_H W3) ms3)) 10).
  { cbn [restrict ms_regs]. rewrite Ra0. cbn [sv_denot]. rewrite E46, Z.add_0_r, Z_to_bv_bv_unsigned.
    reflexivity. }
  pose proof (ast_ok_pi_set_reg_fp E _ _ (10%bv : bv 5) (SOff 46 0) HS eq_refl HS10) as HSq.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSq. clear HS. rename HSq into HS.
  paj_run_tok RUN HS HJ SHOK Wspan.
  { w3_awr E9. }
  prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3.
  prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8. prreg HS (9%bv : bv 5) T9.
  prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11.
  prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19. prreg HS (20%bv : bv 5) T20.
  prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22. prreg HS (23%bv : bv 5) T23.
  prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25. prreg HS (26%bv : bv 5) T26.
  prreg HS (27%bv : bv 5) T27.
  rewrite (EReg 2%nat (2%bv : bv 5) eq_refl) in T2. rewrite (EReg 3%nat (3%bv : bv 5) eq_refl) in T3.
  rewrite (EReg 4%nat (4%bv : bv 5) eq_refl) in T4. rewrite (EReg 8%nat (8%bv : bv 5) eq_refl) in T8.
  rewrite (EReg 9%nat (9%bv : bv 5) eq_refl) in T9.
  rewrite (EReg 18%nat (18%bv : bv 5) eq_refl) in T18. rewrite (EReg 20%nat (20%bv : bv 5) eq_refl) in T20.
  rewrite (EReg 21%nat (21%bv : bv 5) eq_refl) in T21. rewrite (EReg 23%nat (23%bv : bv 5) eq_refl) in T23.
  assert (HKEEP1 : w3_keep (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms)).
  { intros a Ha Hn.
    refine (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun x => c_sp1 cx - 16 <= x < c_sp1 cx + 152) HFr _ a Ha Hn).
    intros bb wlo whi aa Hinw Hrr. vm_compute in Hinw.
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; fold E in Hrr; rewrite E9 in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw as [Hq|Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|].
    destruct Hinw. }
  assert (Hms : ms = mkst (ms_regs ms) (Z_to_bv 64 (BASE + AF_rd32)) (ms_mem ms) (seg_rom SEGS))
    by (rewrite <- pa_sigma_rd32; exact (w3_shape_call E _ _ W3 _ HS eq_refl)).
  assert (Hsp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite T2, P2; apply unsigned_lit_small; lia).
  assert (Hbytes : garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (b + (p_q cx p + 12))
                     [PSN.fb (p_F cx) (p_q cx p + 12); PSN.fb (p_F cx) (p_q cx p + 12 + 1);
                      PSN.fb (p_F cx) (p_q cx p + 12 + 2); PSN.fb (p_F cx) (p_q cx p + 12 + 3)]).
  { apply (w3_bytes4 cx _ b (p_q cx p + 12)); [|lia|unfold PSN.flen, p_nF in *; lia].
    apply (w3_garr_lo (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms) b (p_C cx) HKEEP1 ltac:(lia) ltac:(lia)
             ltac:(rewrite w3_C_len; lia) Hcopy). }
  assert (Ha0c : getr (ms_regs ms) 10 = w64 (b + (p_q cx p + 12))).
  { rewrite T10;
    first [ rewrite U19
          | rewrite (w3_alu_add (ew E 19%nat) (Z_to_bv 64 12) (b + p_q cx p) 12 U19
                      ltac:(apply unsigned_lit_small; lia)) ];
    unfold w64; f_equal; lia. }
  rewrite Hms. eapply SRr_bind.
  { exact (w3_rd32_call LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
             [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3) k (ms_regs ms)
             (b + (p_q cx p + 12)) b (p_nF cx) _ _ _ _ HJ
             ltac:(rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]) Ha0c
             ltac:(rewrite Hsp; pose proof (Z.div_mod (c_sp1 cx) 32 ltac:(lia)); lia)
             ltac:(rewrite Hsp; unfold RD32_FRAME, LLVMF_STK; lia)
             ltac:(rewrite Hsp; lia) Hinb ltac:(lia) ltac:(unfold PSN.flen, p_nF in *; lia) Hbytes). }
  cbv beta. intros W4 c4 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPres2 & Ha0 & Hsame2 & UN2).
  rewrite Hsp in UN2. unfold RD32_FRAME in UN2.
  assert (HKEEP : w3_keep (c_sp1 cx) W3 (ms_mem ms3) mem2)
    by (apply (w3_keep_trans (c_sp1 cx) W3 (ms_mem ms3) (ms_mem ms) mem2 HKEEP1);
        apply (w3_keepf_weak (c_sp1 cx) W3 (ms_mem ms) mem2); exact UN2).
  pose proof (w3_region0_call E _ _ _ _ _ HS eq_refl) as HRg.
  destruct (same_but_materialized_fs md3 (with_vm_backing (m_vm_lazy md3) mat md3)
              ltac:(apply same_but_materialized_wvb_any)) as (Hfd1 & Hfs1).
  destruct (same_but_materialized_fs (with_vm_backing (m_vm_lazy md3) mat md3) md2 Hsame2) as (Hfd2 & Hfs2).
  assert (K2 : getr regs2 2 = getr (ms_regs ms) 2) by (apply (HPres2 2); unfold acallee_saved; lia).
  assert (K3 : getr regs2 3 = getr (ms_regs ms) 3) by (apply (HPres2 3); unfold acallee_saved; lia).
  assert (K4 : getr regs2 4 = getr (ms_regs ms) 4) by (apply (HPres2 4); unfold acallee_saved; lia).
  assert (K8 : getr regs2 8 = getr (ms_regs ms) 8) by (apply (HPres2 8); unfold acallee_saved; lia).
  assert (K9 : getr regs2 9 = getr (ms_regs ms) 9) by (apply (HPres2 9); unfold acallee_saved; lia).
  assert (K18 : getr regs2 18 = getr (ms_regs ms) 18) by (apply (HPres2 18); unfold acallee_saved; lia).
  assert (K19 : getr regs2 19 = getr (ms_regs ms) 19) by (apply (HPres2 19); unfold acallee_saved; lia).
  assert (K20 : getr regs2 20 = getr (ms_regs ms) 20) by (apply (HPres2 20); unfold acallee_saved; lia).
  assert (K21 : getr regs2 21 = getr (ms_regs ms) 21) by (apply (HPres2 21); unfold acallee_saved; lia).
  assert (K22 : getr regs2 22 = getr (ms_regs ms) 22) by (apply (HPres2 22); unfold acallee_saved; lia).
  assert (K23 : getr regs2 23 = getr (ms_regs ms) 23) by (apply (HPres2 23); unfold acallee_saved; lia).
  assert (K24 : getr regs2 24 = getr (ms_regs ms) 24) by (apply (HPres2 24); unfold acallee_saved; lia).
  assert (K25 : getr regs2 25 = getr (ms_regs ms) 25) by (apply (HPres2 25); unfold acallee_saved; lia).
  assert (K26 : getr regs2 26 = getr (ms_regs ms) 26) by (apply (HPres2 26); unfold acallee_saved; lia).
  assert (K27 : getr regs2 27 = getr (ms_regs ms) 27) by (apply (HPres2 27); unfold acallee_saved; lia).
  assert (Hregs2 : pregs cx (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS))).
  { unfold pregs, mkst; cbn [ms_regs]; split; [|split; [|split; [|split]]].
    - rewrite K2, T2. exact P2.
    - rewrite K8, T8. exact P8.
    - rewrite K9, T9. exact P9.
    - rewrite K3, T3. exact P3.
    - rewrite K4, T4. exact P4. }
  pose proof (w3_body_keep cx fp PP_KRI PP_KO PSH_ts ly3 S3 W3 ms3 md3 k
                (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) HB HJ0 Hfrs HBody
                ltac:(unfold mkst; cbn [ms_pc_val]; rewrite T1; reflexivity)
                eq_refl eq_refl eq_refl eq_refl eq_refl Hregs2 HKEEP) as HBodyO.
  assert (SLOT : forall off v, 16 <= off -> off <= 152 -> pslot cx W3 ms off v ->
                   pslot cx W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) off v).
  { intros off v Ho1 Ho2 Hs.
    apply (w3_slot_keepf cx W3 ms (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) off v);
    [|lia|lia|lia|exact Hs]. intros a Ha Hn. unfold mkst; cbn [ms_mem]. apply UN2; [exact Ha | exact Hn]. }
  apply (RKO cx fp k acc ly3 S3 W3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB HJ2 Hfrs Hmo).
  assert (HT26 : getr regs2 26 = w64 (p_q cx p)) by (rewrite K26, T26; exact E26).
  split; [| unfold mkst; cbn [ms_regs]; rewrite HT26, unsigned_lit_small by lia;
            rewrite Rs10 in HM; unfold w64 in HM; rewrite unsigned_lit_small in HM by lia; exact HM].
  exists b, h, buf, i, p. cbv zeta.
  split; [split; [exact HBodyO|]; split; [exact Hk|]; split; [exact Hacc|]; split; [exact HPerm|];
          split; [rewrite Hfd2, Hfd1; exact Hfds | rewrite Hfs2, Hfs1; exact Hfs]|].
  split; [exact Hn26|]. split; [exact Hgood|]. split; [exact Hi0|]. split; [exact Hip|].
  split; [exact Hpe|]. split; [exact HKF|].
  split.
  { unfold mkst; cbn [ms_regs]. rewrite Ha0, T11, E44. rewrite <- (w3_trd32_hw cx (p_q cx p) 12). reflexivity. }
  split; [unfold mkst; cbn [ms_regs]; rewrite K18, T18; exact Rs2|].
  split; [unfold mkst; cbn [ms_regs]; rewrite K19, T19; exact Rs3|].
  split; [unfold mkst; cbn [ms_regs]; rewrite K20, T20; exact Rs4|].
  split; [unfold mkst; cbn [ms_regs]; rewrite K21, T21; exact Rs5|].
  split.
  { unfold mkst; cbn [ms_regs]. rewrite K22, T22.
    exact (w3_sext32' E 45%nat (PSN.orig (p_sw cx) (p_F cx) (p_q cx p)) E45 Horig). }
  split; [unfold mkst; cbn [ms_regs]; rewrite K23, T23; exact Rs7|].
  split; [unfold mkst; cbn [ms_regs]; rewrite K24, T24; subst E; change 288%nat with (A_HI 8);
          rewrite Eimg_img by (unfold A_HI, A_TEXT, A_LIM; lia); reflexivity|].
  split.
  { unfold mkst; cbn [ms_regs]. rewrite K25, T25. exact HZXa. }
  split; [unfold mkst; cbn [ms_regs]; exact HT26|].
  split.
  { unfold mkst; cbn [ms_regs]. rewrite K27, T27, E46. reflexivity. }
  split.
  { split.
    { split; [apply (SLOT 144 (pF cx fp)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 144 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (SLOT 24 (p_d cx)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 24 (SOff 38 0) (p_d cx) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                      ltac:(unfold p_d in *; lia))|].
      split; [apply (SLOT 72 SHADOW_OFF); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 72 (SLit SHADOW_OFF) SHADOW_OFF HRg E9 ltac:(cbn; tauto)
                      eq_refl ltac:(unfold SHADOW_OFF; lia))|].
      split; [apply (SLOT 40 (pSH cx fp)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 40 (SOff 40 0) (pSH cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (SLOT 32 (pF cx fp)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 32 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (SLOT 16 (pF cx fp)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 16 (SOff 39 0) (pF cx fp) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
      split; [apply (SLOT 88 (pF cx fp + PO_TS)); [lia|lia|];
              apply (w3_slot_of_region E W3 ms cx _ 88 (SOff 39 96) (pF cx fp + PO_TS) HRg E9 ltac:(cbn; tauto)
                      ltac:(cbn [sv_denot]; rewrite E39; unfold PO_TS; rewrite unsigned_lit_small by lia; reflexivity)
                      ltac:(unfold PO_TS; lia))|].
      apply (SLOT 120 (p_cap cx)); [lia|lia|].
      apply (w3_slot_of_region E W3 ms cx _ 120 (SOff 36 0) (p_cap cx) HRg E9 ltac:(cbn; tauto)
               ltac:(cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
               ltac:(unfold p_cap, p_d in *; lia)). }
    split; [apply (SLOT 96 buf); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 96 (SOff 35 0) buf HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
    split; [apply (SLOT 48 3840); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 48 (SLit 3840) 3840 HRg E9 ltac:(cbn; tauto) eq_refl ltac:(lia))|].
    split; [apply (SLOT 56 (buf + 12)); [lia|lia|];
            apply (w3_slot_of_region E W3 ms cx _ 56 (SOff 35 12) (buf + 12) HRg E9 ltac:(cbn; tauto)
                    ltac:(cbn [sv_denot]; rewrite E35, unsigned_lit_small by lia; reflexivity) ltac:(lia))|].
    apply (SLOT 64 (1000000 * 2 ^ 32)); [lia|lia|].
    apply (w3_slot_of_region E W3 ms cx _ 64 (SLit 4294967296000000) (1000000 * 2 ^ 32) HRg E9 ltac:(cbn; tauto)
             eq_refl ltac:(lia)). }
  split; [apply (SLOT 104 (i + 1)); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 104 (SOff 42 0) (i + 1) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (SLOT 112 (p_res cx (p_q cx p))); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 112 (SOff 43 0) (p_res cx (p_q cx p)) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(lia))|].
  split; [apply (SLOT 80 (p_first cx mod 2 ^ 64)); [lia|lia|];
          apply (w3_slot_of_region E W3 ms cx _ 80 (SOff 41 0) (p_first cx mod 2 ^ 64) HRg E9 ltac:(cbn; tauto)
                  ltac:(cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
                  ltac:(pose proof (Z.mod_pos_bound (p_first cx) (2 ^ 64) ltac:(lia)); lia))|].
  split; [exact (w3_glob_keep cx W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) b HKEEP
                   ltac:(lia) Hglob)|].
  apply (w3_reader_keep cx fp W3 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) b h buf p ASIL HKEEP
           ltac:(lia) ltac:(lia) Hb2 ltac:(lia) Hh2 ltac:(lia) Hu2 HF1 HF2).
  split; [exact Hsrc|]. split; [exact (conj Vf Vsw)|].
  intros _. exact (conj Vorig (conj Vtag (conj Vvid (conj Vts Vbuf)))).
Qed.

(* ---- the measured forms and the skip loop ---- *)

Lemma pe_meas_of : pe_meas_of_stmt.
Proof. unfold pe_meas_of_stmt. intros GI m H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo (HGI & _).
exact (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI). Qed.

Lemma pe_meas_mono : forall GI m m', m <= m' -> PF (pe_meas GI m') -> PF (pe_meas GI m).
Proof.
intros GI m m' Hle H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo (HGI & HM).
apply (H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo). split; [exact HGI | lia].
Qed.

Lemma pe_from_meas_all : pe_from_meas_all_stmt.
Proof.
unfold pe_from_meas_all_stmt. intros GI H cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI.
apply (H (p_nF cx - bv_unsigned (getr (ms_regs ms3) 26)) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo).
split; [exact HGI | lia].
Qed.

Lemma pe_meas_KR_low : pe_meas_KR_low_stmt.
Proof.
unfold pe_meas_KR_low_stmt. intros m cx fp k acc ly3 S3 W3 ms3 md3 (HGI & HM).
destruct HGI as (b & h & buf & i & p & e & _ & Hn26 & _ & Hi0 & Hip & _ & Hpe & _ & He16 &
                 _ & _ & _ & _ & _ & _ & Rs10 & _).
pose proof (p_sizes cx) as (Z1 & _).
rewrite Rs10 in HM. unfold w64 in HM. rewrite unsigned_lit_small in HM by lia. lia.
Qed.

(* The skip loop: e grows by at least 16 at every turn, so the chain from PP_KR ends at PP_KO. *)
Lemma pe_from_skip_fuel : forall (n : nat) m, m <= 16 * Z.of_nat n ->
  PF (pe_meas (GI_KO B MT KS) m) -> PF (pe_meas (GI_KR B MT KS) m).
Proof.
induction n as [|n IH]; intros m Hm HKO.
- intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HGI.
  exfalso. pose proof (pe_meas_KR_low m cx fp k acc ly3 S3 W3 ms3 md3 HGI). cbn [Z.of_nat] in Hm. lia.
- apply pe_from_KR_m. apply pe_from_KRI_m.
  + apply (IH (m - 16) ltac:(rewrite Nat2Z.inj_succ in Hm; lia)).
    apply (pe_meas_mono (GI_KO B MT KS) (m - 16) m ltac:(lia) HKO).
  + exact HKO.
Qed.

Lemma pe_from_skip_m : pe_from_skip_m_stmt.
Proof.
unfold pe_from_skip_m_stmt. intros m HKO.
apply (pe_from_skip_fuel (Z.to_nat (Z.max m 0)) m); [|exact HKO].
pose proof (Z2Nat.id (Z.max m 0) ltac:(lia)) as Hid. lia.
Qed.

Lemma pe_from_skip : pe_from_skip_stmt.
Proof.
unfold pe_from_skip_stmt. intros HKO. apply pe_from_meas_all. intros m.
apply pe_from_skip_m. apply pe_meas_of. exact HKO.
Qed.

Lemma pe_from_K4 : pe_from_K4_stmt.
Proof.
unfold pe_from_K4_stmt. intros HKR. apply pe_from_meas_all. intros m.
apply pe_from_K4_m. apply pe_meas_of. exact HKR.
Qed.

Lemma pe_from_KR : pe_from_KR_stmt.
Proof.
unfold pe_from_KR_stmt. intros HKI. apply pe_from_meas_all. intros m.
apply pe_from_KR_m. apply pe_meas_of. exact HKI.
Qed.

Lemma pe_from_KRI : pe_from_KRI_stmt.
Proof.
unfold pe_from_KRI_stmt. intros HKR HKO. apply pe_from_meas_all. intros m.
apply pe_from_KRI_m; apply pe_meas_of; [exact HKR | exact HKO].
Qed.

(* The record loop's head, closed through the skip loop: PP_KO is all the next lane must give. *)
Lemma pe_from_K4_KO : pe_from_K4_KO_stmt.
Proof. unfold pe_from_K4_KO_stmt. intros HKO. apply pe_from_K4. apply pe_from_skip. exact HKO. Qed.

End c.
End b.
End a.
