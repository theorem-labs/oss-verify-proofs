(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ge_achain adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v (rt_chain) for the call chain of libreac/fuzz_grant's entry function; the rest of the file is written for fuzz_grant's entry walk. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySeat.v, with its module paths and module names changed; 463 of its 516 lines of code are new or changed and 878 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNextFitB.v, with its module names changed; 1578 of its 1632 lines of code are new or changed and 462 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the ASan+UBSan
   build of libreac v1.9.0: the phase from the return of the header fread (NP_hd_ra, 0x81770) to the record loop's
   head (KEmpty), the skip test (NP_sk1), the fit path (NP_fit) or the exit (NP_exit). Its entry predicate is
   nx_hdra_inv (lib/B/Prog/PcapSourceNextHdrBDefs.v).

   THE CODE (0x81770 .. 0x81814, 0x81858..0x81864 and 0x81970..0x81984).
     0x81770 li a1,16; 0x81774 `bne a0,a1` -> 0x81970 (NP_eof): a6 := NS_FK, s3 := NS_F0, a1 := -1, `bnez a0`
       -> NP_exit (a short header, KCutH); else a1 := a0 = 0 (KEnd) and -> NP_exit.
     else (16 bytes read) four times: the shadow check of ps + 8 (`lb a0,0(s4)`; the slow compare 0x81868.. is not
       reached, the shadow byte is 0), `lw a1,0(s11)` = ps->swapped, and `jal rd_u32` with a0 = ph + 0, 4, 8, 12
       (0x81788, 0x817a8, 0x817c8, 0x817f0; the pointers 4, 8, 12 come from the slots NS_PH4 / NS_PH8 / NS_PH12).
       Between them the UBSan guards `bgeu s3,-4` 0x81794, `bltu -9,s3` 0x817b4 and `bltu -13,s3` 0x817d8 (the
       `unimp` at 0x81b64) are not taken: ph + 12 < 2 ^ 64.
     0x817cc `beqz a0` (the third word, incl) -> 0x81858 (NP_empty): the frame's shadow bytes 4, 5 := 0xf8 and
       `j` NP_loop (KEmpty).
     else s6 := incl (0x817d0), NS_SEC := s2 = ts_sec (0x817e4), the fourth rd_u32 (orig), the shadow check of
       ps + 12 (0x817f4..0x817fc, the slot NS_SH12), s2 := incl zero-extended (0x81800, 0x81804), `sw a0,0(a1)`
       0x8180c writes ps->orig through the slot NS_PS12, and `bgeu s7,s2` 0x81810 -> NP_fit (cap >= incl), else
       the fall-through NP_sk1 (0x81814).

   Every number is read from the pinned fuzz_pcap.asan-ubsan image
   (sha256 9e66f771f22af67a...; capstone 5 disassembly of its unstripped twin). *)
(* Modified by Theorem Labs, 2026-10: the Require of PcapSourceNextFitB.v, made only for its vm_frame / asource_at_frame
   copies (deleted; lib/A/Prog/PcapSourceCloseSpec.v holds them), is dropped: this file names none of them. *)
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI01 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import RdU32.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs PcapSourceNextHdrBDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextSkipDefs PcapSourceNextFitADefs.
(* hb_geo, hb_out, hb_kept_step, hb_body_keep, hb_mid_keep: what one segment of the run keeps. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrBKeep.
(* hdr_len / hdr_bytes / hw_of_bytes / incl_range / orig_range / the kind lemmas / chain_empty_at. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrWords.
(* hb_loop_at / hb_fit_at / hb_sk1_at: the three landings. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextHdrBLand.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic state of the run                                                                    *)
(* ---------------------------------------------------------------------------------------------- *)

(* The four places the run touches, one region each (atoms: 9 = s1 = the realigned sp, 19 = s3 = ph = F + 32,
   20 = s4 = the shadow address of ps + 8, 25 = s9 = the frame's shadow address, 27 = s11 = ps + 8, and the
   extra atom 32 = ps->swapped):
   - the spill slots [s1 + 56, s1 + 128): NS_SEC (written at 0x817e4), then the seven slots the run reads;
   - [ps + 8, ps + 16): ps->swapped (read at 0x81780, 0x817a0, 0x817c0, 0x817e8) and ps->orig (written at
     0x8180c through the slot NS_PS12 = s11 + 4);
   - the shadow byte of ps + 8, which is also the shadow byte of ps + 12 (ps is 8-aligned): read at 0x81778,
     0x81798, 0x817b8, 0x817dc and (through NS_SH12) 0x817f8;
   - the frame's shadow bytes 4 and 5, written by NP_empty (0x8185c, 0x81860). *)
Definition hb_slots : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 128 56 64
    [ YP09.mkChunk NS_F0 (CVal 8 (SOff 19 (- NO_PH)));
      YP09.mkChunk NS_SH12 (CVal 8 (SOff 20 0));
      YP09.mkChunk NS_PH12 (CVal 8 (SOff 19 12));
      YP09.mkChunk NS_PS12 (CVal 8 (SOff 27 4));
      YP09.mkChunk NS_FK (CVal 8 (SOff 19 (- NO_PH)));
      YP09.mkChunk NS_PH8 (CVal 8 (SOff 19 8));
      YP09.mkChunk NS_PH4 (CVal 8 (SOff 19 4)) ].
(* ps->swapped (atom 32) and ps->orig (atom 33, the value the turn starts with): both are chunks, so the
   state carries ps->orig's value whether or not 0x8180c has written it yet. *)
Definition hb_ps8 : YP09.region :=
  YP09.mkRegion (Some 27%nat) 0 8 4 8
    [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0))].
Definition hb_sh8 : YP09.region :=
  YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
(* The frame's shadow bytes 4 and 5: 0 while `ph` is in scope, 0xf8 after NP_empty writes them. They are
   chunks for the same reason. *)
Definition hb_fsh : YP09.region :=
  YP09.mkRegion (Some 25%nat) 4 6 4 6
    [YP09.mkChunk 4 (CVal 1 (SLit 0)); YP09.mkChunk 5 (CVal 1 (SLit 0))].
Definition hb_regions : smem := [hb_slots; hb_ps8; hb_sh8; hb_fsh].
(* ph = F + 32 is a pointer at least 4128, 32-aligned (F is 64-aligned): the three UBSan guards
   (0x81794, 0x817b4, 0x817d8) are decided by it. *)
Definition hb_facts : facts := mkFacts [(19%nat, mkAF 4128 140737479966720 5)] [] [].
Definition hb_ss (pc : Z) : sstate := mkSS pc sr_atoms hb_regions None hb_facts.

(* The first shadow byte of a range that is addressable and starts 8-aligned is 0 (the copy of
   PcapSourceNextEntry's nx_shadow0: an address with x mod 8 = 7 forces saddr_ok's second arm to be
   impossible, YG0v.v:29). *)
Lemma hb_shadow0 : forall (rd : Z -> option Z) p n,
  p mod 8 = 0 -> 8 <= n -> range_addressable rd SHADOW_OFF p n -> rd (SHADOW_OFF + p / 8) = Some 0.
Proof.
intros rd p n Hp Hn HR. destruct (HR (p + 7) ltac:(lia)) as (s & Hs & Hok).
assert (E : shadow_of_addr SHADOW_OFF (p + 7) = SHADOW_OFF + p / 8).
{ unfold shadow_of_addr. f_equal. symmetry. apply (Z.div_unique (p + 7) 8 (p / 8) 7); [left; lia|].
  pose proof (Z.div_mod p 8 ltac:(lia)) as D. rewrite Hp, Z.add_0_r in D. lia. }
rewrite E in Hs. unfold saddr_ok in Hok.
assert (Hm : (p + 7) mod 8 = 7) by (rewrite <- Zplus_mod_idemp_l, Hp; reflexivity).
rewrite Hm in Hok. destruct Hok as [-> | [H1 H2]]; [exact Hs | lia].
Qed.

(* The model at a turn whose header fread came up short (`bne a0,16` 0x81774 taken): fewer than 16 bytes are
   left, so the record's kind is KEnd (nothing left: the call returns 0) or KCutH (a short header: -1), the
   walk stops at this q, and the stream ends at |C|. *)
Lemma hb_eof_model : forall sw C cap p q lh,
  nx_chain_inv sw (nxF C) cap p q lh -> 0 <= q <= Z.of_nat (length C) ->
  Z.of_nat (length C) - q < 16 ->
  nx_q sw C cap p = q /\ nx_lh sw C cap p = lh /\ nx_fit sw C cap p = false /\
  nx_pos sw C cap p = Z.of_nat (length C) /\
  nx_res sw C cap p = (if Z.of_nat (length C) - q =? 0 then 0 else -1).
Proof.
intros sw C cap p q lh HC Hq Hlt.
assert (Hflen : PSN.flen (nxF C) = Z.of_nat (length C))
  by (unfold PSN.flen; rewrite nxF_length; reflexivity).
assert (Hk : PSN.kind sw (nxF C) cap q =
             if Z.of_nat (length C) - q =? 0 then PSN.KEnd else PSN.KCutH).
{ unfold PSN.kind. rewrite Hflen.
  destruct (Z.eqb_spec (Z.of_nat (length C) - q) 0) as [E|E]; [reflexivity|].
  destruct (Z.ltb_spec (Z.of_nat (length C) - q) 16); [reflexivity | lia]. }
destruct (nx_chain_stop sw (nxF C) cap p q lh HC ltac:(rewrite nxF_length; lia)
  ltac:(rewrite Hk; destruct (Z.of_nat (length C) - q =? 0); discriminate)
  ltac:(rewrite Hk; destruct (Z.of_nat (length C) - q =? 0); discriminate)) as (Hq' & Hlh').
split; [unfold nx_q; exact Hq'|].
split; [unfold nx_lh; rewrite Hlh', Hk; destruct (Z.of_nat (length C) - q =? 0); reflexivity|].
split; [unfold nx_fit, nx_kind, nx_q; rewrite Hq', Hk;
        destruct (Z.of_nat (length C) - q =? 0); reflexivity|].
split; [unfold nx_pos, nx_q; rewrite Hq'; unfold PSN.pos_of; rewrite Hk, Hflen;
        destruct (Z.of_nat (length C) - q =? 0); reflexivity|].
unfold nx_res, nx_q. rewrite Hq'. unfold PSN.res_of. rewrite Hk.
destruct (Z.of_nat (length C) - q =? 0); reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
(* rd_u32 (0x81c38), proved by a Theorem Labs lane's lib/B/Prog walk; this phase calls it four times. *)
Hypothesis H_rdu32 : trd_u32_specX SK SEGS B (BASE + AF_rd_u32).

Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* hb_* of PcapSourceNextHdrBKeep take this section's B, KS and LAWS (and ASIL) first. *)
(* The environment of the run: the registers at the cut, plus ps->swapped as atom 32 and ps->orig (the value
   the turn starts with) as atom 33. *)
Definition hb_E (cx : ncx) (ol : Z) (ms3 : machine_state) : env :=
  Eimg (Ereg (ms_regs ms3) [w64 (n_sw cx); w64 ol]).


(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic state at NP_hd_ra                                                                   *)
(* ---------------------------------------------------------------------------------------------- *)

(* The machine state's shape at a cut of the run. *)
Lemma hb_state_of : forall (E : env) ss (W : world SEGS) ms,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  ms_pc_val ms = w64 (BASE + ss_pc ss) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr.
Proof.
intros E ss W ms HS Hrv. pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
split; [rewrite Hms at 1; reflexivity|]. split; [rewrite Hms at 1; reflexivity|].
split; [rewrite Hms at 1; reflexivity|]. split; [rewrite Hms at 1; reflexivity|].
split; rewrite Hms at 1; reflexivity.
Qed.


(* The same at a call, where the state is st_ok (the pc is the callee's absolute address). *)
Lemma hb_chunk_byte_s : forall (E : env) ss (W : world SEGS) ms i (r : YP09.region) (c : YP09.chunk) v,
  st_ok SEGS E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
  YP09.c_len c = 1 -> YP09.c_val c = CVal 1 (SLit v) -> 0 <= v < 256 ->
  aview SEGS (w_H W) (ms_mem ms) (base_val E (YP09.r_base r) + YP09.c_off c) = Some v.
Proof.
intros E ss W ms i r c v HS Hi Hc Hlen Hval Hv.
assert (HR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ destruct (st_ok_mem_ok SEGS E ss (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs. exact (proj1 (Forall_forall _ _) Hrs r (nth_error_In _ _ Hi)). }
destruct HR as (_ & _ & _ & HC).
destruct (proj1 (Forall_forall _ _) HC c Hc 0 ltac:(rewrite Hlen; lia)) as (b & Hb & Hm).
rewrite Hval in Hb. cbn [cbyte] in Hb. injection Hb as <-.
unfold aview. rewrite Z.add_0_r in Hm. rewrite Hm. cbn [option_map]. f_equal.
cbn [sv_denot]. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite (unsigned_lit_small v ltac:(clear - Hv; lia) : bv_unsigned (Z_to_bv 64 v) = v).
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. clear - Hv. lia.
Qed.
(* A byte a region of the run state carries, read back out of the state: the two shadow bytes of `ph` are
   inside the frame-shadow region's write window, so the frame fact of a run says nothing about them; their
   value comes from the region's chunk. *)
Lemma hb_chunk_byte : forall (E : env) ss (W : world SEGS) ms i (r : YP09.region) (c : YP09.chunk) v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
  YP09.c_len c = 1 -> YP09.c_val c = CVal 1 (SLit v) -> 0 <= v < 256 ->
  aview SEGS (w_H W) (ms_mem ms) (base_val E (YP09.r_base r) + YP09.c_off c) = Some v.
Proof.
intros E ss W ms i r c v HS Hi Hc Hlen Hval Hv.
assert (HR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  refine (proj1 (Forall_forall _ _) Hrs r _).
  destruct ss; exact (nth_error_In _ _ Hi). }
destruct HR as (_ & _ & _ & HC).
destruct (proj1 (Forall_forall _ _) HC c Hc 0 ltac:(rewrite Hlen; lia)) as (b & Hb & Hm).
rewrite Hval in Hb. cbn [cbyte] in Hb. injection Hb as <-.
unfold aview. rewrite Z.add_0_r in Hm. rewrite Hm. cbn [option_map]. f_equal.
cbn [sv_denot]. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite (unsigned_lit_small v ltac:(clear - Hv; lia) : bv_unsigned (Z_to_bv 64 v) = v).
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. clear - Hv. lia.
Qed.

(* The same when the stored value is a 64-bit literal (0x81858 `sb` of -8: the chunk is SLit (2 ^ 64 - 8)):
   the byte is its low 8 bits. *)
Lemma hb_chunk_byte_w : forall (E : env) ss (W : world SEGS) ms i (r : YP09.region) (c : YP09.chunk) v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
  YP09.c_len c = 1 -> YP09.c_val c = CVal 1 (SLit v) -> 0 <= v < 2 ^ 64 ->
  aview SEGS (w_H W) (ms_mem ms) (base_val E (YP09.r_base r) + YP09.c_off c) = Some (v mod 256).
Proof.
intros E ss W ms i r c v HS Hi Hc Hlen Hval Hv.
assert (HR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  refine (proj1 (Forall_forall _ _) Hrs r _).
  destruct ss; exact (nth_error_In _ _ Hi). }
destruct HR as (_ & _ & _ & HC).
destruct (proj1 (Forall_forall _ _) HC c Hc 0 ltac:(rewrite Hlen; lia)) as (b & Hb & Hm).
rewrite Hval in Hb. cbn [cbyte] in Hb. injection Hb as <-.
unfold aview. rewrite Z.add_0_r in Hm. rewrite Hm. cbn [option_map]. f_equal.
cbn [sv_denot]. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
rewrite (unsigned_lit_small v Hv : bv_unsigned (Z_to_bv 64 v) = v).
rewrite Z_to_bv_unsigned. reflexivity.
Qed.

(* The same for a word-valued chunk: the struct's orig field is a chunk of the run state, so its value comes
   back out of the state whether or not 0x8180c has written it. *)
Lemma hb_chunk_val : forall (E : env) ss (W : world SEGS) ms i (r : YP09.region) (c : YP09.chunk) n sv v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
  YP09.c_len c = Z.of_N n -> YP09.c_val c = CVal n sv ->
  sv_denot E sv = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> (8 * Z.of_N n <= 64) ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms))
    (base_val E (YP09.r_base r) + YP09.c_off c) (N.to_nat n) v.
Proof.
intros E ss W ms i r c n sv v HS Hi Hc Hlen Hval Hsv Hv Hn.
assert (HR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  refine (proj1 (Forall_forall _ _) Hrs r _). destruct ss; exact (nth_error_In _ _ Hi). }
destruct HR as (_ & _ & _ & HC).
intros k Hk.
assert (Hk' : 0 <= Z.of_nat k < YP09.c_len c) by (rewrite Hlen; lia).
destruct (proj1 (Forall_forall _ _) HC c Hc (Z.of_nat k) Hk') as (b & Hb & Hm).
rewrite Hval in Hb. cbn [cbyte] in Hb. injection Hb as <-. rewrite Hm. f_equal.
rewrite (le_byte_small v (N.to_nat n) k ltac:(rewrite N_nat_Z; exact Hv) Hk).
unfold byte_of_word. rewrite Hsv.
rewrite (unsigned_lit_small v ltac:(clear - Hv Hn;
  pose proof (Z.pow_le_mono_r 2 (8 * Z.of_N n) 64 ltac:(lia) ltac:(lia)); lia)).
reflexivity.
Qed.

(* ---- the words rd_u32 returns, as the landings read them ---- *)

(* rd_u32 returns its 32-bit value sign-extended (a0 = w64 (bv_swrap 32 v)): the low 32 bits are v. *)
Lemma hb_swrap_low : forall x, 0 <= x < 2 ^ 32 -> bv_unsigned (w64 (bv_swrap 32 x)) mod 2 ^ 32 = x.
Proof.
intros x Hx. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64). change (bv_modulus 32) with (2 ^ 32).
change (bv_half_modulus 32) with (2 ^ 31).
destruct (Z.lt_ge_cases x (2 ^ 31)) as [Hl|Hh].
- rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. replace (x + 2 ^ 31 - 2 ^ 31) with x by lia.
  rewrite (Z.mod_small x (2 ^ 64)) by lia. apply Z.mod_small. lia.
- replace ((x + 2 ^ 31) mod 2 ^ 32) with (x - 2 ^ 31)
    by (apply (Z.mod_unique (x + 2 ^ 31) (2 ^ 32) 1 (x - 2 ^ 31)); [left; lia | lia]).
  replace ((x - 2 ^ 31 - 2 ^ 31) mod 2 ^ 64) with (x - 2 ^ 32 + 2 ^ 64)
    by (apply (Z.mod_unique (x - 2 ^ 31 - 2 ^ 31) (2 ^ 64) (-1) (x - 2 ^ 32 + 2 ^ 64));
        [left; lia | lia]).
  symmetry. apply (Z.mod_unique (x - 2 ^ 32 + 2 ^ 64) (2 ^ 32) (2 ^ 32 - 1) x); [left; lia | lia].
Qed.

(* ... and below 2 ^ 31 the sign extension is the value itself. *)
Lemma hb_swrap_small : forall x, 0 <= x < 2 ^ 31 -> w64 (bv_swrap 32 x) = w64 x.
Proof.
intros x Hx. f_equal. unfold bv_swrap, bv_wrap.
change (bv_modulus 32) with (2 ^ 32). change (bv_half_modulus 32) with (2 ^ 31).
rewrite (Z.mod_small (x + 2 ^ 31) (2 ^ 32)) by lia. lia.
Qed.

Lemma hb_wrap64 : forall z, bv_wrap 64 z = z mod 2 ^ 64.
Proof. intros z. reflexivity. Qed.
Lemma hb_wrap8 : forall z, bv_wrap 8 z = z mod 2 ^ 8.
Proof. intros z. reflexivity. Qed.

Lemma hb_sll_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SLL a (Z_to_bv 64 k)) = (bv_unsigned a * 2 ^ k) mod 2 ^ 64.
Proof.
intros a k Hk. unfold alu64, alu. rewrite bv_shiftl_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !hb_wrap64.
rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma hb_srl_u : forall (a : word) k, 0 <= k < 64 ->
  bv_unsigned (alu64 ALU_SRL a (Z_to_bv 64 k)) = bv_unsigned a / 2 ^ k.
Proof.
intros a k Hk. unfold alu64, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, !Z_to_bv_unsigned, !hb_wrap64.
rewrite (Z.mod_small k) by lia. change (63 mod 2 ^ 64) with (Z.ones 6).
rewrite Z.land_ones by lia. change (2 ^ 6) with 64. rewrite (Z.mod_small k 64) by lia.
rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* s2 := incl zero-extended (0x81800 `slli s2,a0,32`, 0x81804 `srli s2,s2,32`). *)
Lemma hb_zext32 : forall (a : word),
  alu64 ALU_SRL (alu64 ALU_SLL a (Z_to_bv 64 32)) (Z_to_bv 64 32) = w64 (bv_unsigned a mod 2 ^ 32).
Proof.
intros a. apply bv_eq. rewrite hb_srl_u, hb_sll_u by lia. unfold w64. rewrite Z_to_bv_unsigned, hb_wrap64.
replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
rewrite (Z.mod_small (bv_unsigned a mod 2 ^ 32)); [reflexivity|].
pose proof (Z.mod_pos_bound (bv_unsigned a) (2 ^ 32) ltac:(lia)). lia.
Qed.

(* A 4-byte store keeps the low 32 bits of a word: the two shifts and masks of a byte read below bit 32
   agree for two numbers that agree mod 2 ^ 32. *)
Lemma hb_byte_low32 : forall u v k, 0 <= k < 4 -> u mod 2 ^ 32 = v mod 2 ^ 32 ->
  Z.shiftr u (8 * k) mod 2 ^ 8 = Z.shiftr v (8 * k) mod 2 ^ 8.
Proof.
intros u v k Hk Huv. rewrite <- !Z.land_ones by lia. apply Z.bits_inj'. intros n Hn.
rewrite !Z.land_spec, !Z.shiftr_spec by lia.
destruct (Z.lt_ge_cases n 8) as [Hl|Hh].
- rewrite Z.ones_spec_low by lia. rewrite !andb_true_r.
  rewrite <- (Z.mod_pow2_bits_low u 32 (n + 8 * k)) by lia.
  rewrite <- (Z.mod_pow2_bits_low v 32 (n + 8 * k)) by lia.
  rewrite Huv. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite !andb_false_r. reflexivity.
Qed.

(* A 4-byte chunk of the run state holds v when its word agrees with v mod 2 ^ 32. *)
Lemma hb_chunk_val32 : forall (E : env) ss (W : world SEGS) ms i (r : YP09.region) (c : YP09.chunk) sv v,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> In c (YP09.r_chunks r) ->
  YP09.c_len c = 4 -> YP09.c_val c = CVal 4 sv ->
  bv_unsigned (sv_denot E sv) mod 2 ^ 32 = v -> 0 <= v < 2 ^ 32 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (base_val E (YP09.r_base r) + YP09.c_off c) 4 v.
Proof.
intros E ss W ms i r c sv v HS Hi Hc Hlen Hval Hsv Hv.
assert (HR : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ destruct (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hrs & _).
  cbn [ms_mem restrict] in Hrs.
  refine (proj1 (Forall_forall _ _) Hrs r _). destruct ss; exact (nth_error_In _ _ Hi). }
destruct HR as (_ & _ & _ & HC).
intros k Hk.
assert (Hk' : 0 <= Z.of_nat k < YP09.c_len c) by (rewrite Hlen; lia).
destruct (proj1 (Forall_forall _ _) HC c Hc (Z.of_nat k) Hk') as (b & Hb & Hm).
rewrite Hval in Hb. cbn [cbyte] in Hb. injection Hb as <-. rewrite Hm. f_equal.
apply bv_eq. unfold byte_of_word. rewrite !Z_to_bv_unsigned.
rewrite !hb_wrap8.
unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32. change 256 with (2 ^ 8). rewrite Z.mod_mod by lia.
apply hb_byte_low32; [lia|]. rewrite Hsv, Z.mod_mod by lia. symmetry. apply Z.mod_small. lia.
Qed.

(* After a call the run's state names the callee's a0 by the atom k + 4 (a0 is CLOB's fifth register). *)
Lemma hb_havoc_a0 : forall (E : env) k regs, ew (havoc E k (map (getr regs) CLOB)) (k + 4) = getr regs 10.
Proof. intros E k regs. rewrite (ew_havoc_new E k _ 4 (w64 0)) by (cbn; lia). reflexivity. Qed.

(* The runs only materialize the vm backing: the descriptors and the file system stay. *)
Lemma hb_fds_wvb : forall l X m, m_fds (with_vm_backing l X m) = m_fds m.
Proof. reflexivity. Qed.
Lemma hb_fs_wvb : forall l X m, m_fs (with_vm_backing l X m) = m_fs m.
Proof. reflexivity. Qed.

Lemma hb_U_atom0 : forall (E : env) n, U E (SOff n 0) = bv_unsigned (ew E n).
Proof.
intros E n. apply U_atom; [symmetry; apply Z_to_bv_bv_unsigned|].
pose proof (bv_unsigned_in_range 64 (ew E n)) as H. change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma hb_U_zext : forall (E : env) n,
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = bv_unsigned (ew E n) mod 2 ^ 32.
Proof.
intros E n. unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, hb_zext32. unfold w64.
apply unsigned_lit_small. pose proof (Z.mod_pos_bound (bv_unsigned (ew E n)) (2 ^ 32) ltac:(lia)). lia.
Qed.

(* What a call j of the header returns, read as the model's word: its low 32 bits are PSN.hw at 4 j. *)
Lemma hb_word_of_call : forall (a0 : word) sw C q j,
  (sw = 0 \/ sw = 1) -> 0 <= q -> 16 <= Z.of_nat (length C) - q -> 0 <= j <= 3 -> bytes_ok C ->
  a0 = w64 (bv_swrap 32 (rd_u32_val sw (nth (Z.to_nat (4 * j + 0)) (nx_hdr C q) 0)
         (nth (Z.to_nat (4 * j + 1)) (nx_hdr C q) 0) (nth (Z.to_nat (4 * j + 2)) (nx_hdr C q) 0)
         (nth (Z.to_nat (4 * j + 3)) (nx_hdr C q) 0))) ->
  bv_unsigned a0 mod 2 ^ 32 = PSN.hw (sw =? 1) (nxF C) q (4 * j) /\
  a0 = w64 (bv_swrap 32 (PSN.hw (sw =? 1) (nxF C) q (4 * j))).
Proof.
intros a0 sw C q j Hsw Hq HC Hj Hok Ha0.
rewrite (hw_of_bytes sw C q (4 * j) _ _ _ _ Hsw Hq HC ltac:(lia) ltac:(rewrite Z.mul_comm, Z_mod_mult; reflexivity)
  eq_refl eq_refl eq_refl eq_refl Hok) in Ha0.
split; [|exact Ha0]. rewrite Ha0. apply hb_swrap_low. apply nx_hw_range.
Qed.

(* `ph` is addressable while its two shadow bytes are 0: the 16 bytes [F + 32, F + 48) live in the two
   64-byte-frame granules 4 and 5 of this call's frame. rd_u32 asks for this at each of its four pointers. *)
Lemma hb_ph_ra : forall cx fp (W : world SEGS) (m : word -> option byte) d n,
  nF cx fp mod 64 = 0 -> 4096 <= nF cx fp -> nSH cx fp = SHADOW_OFF + nF cx fp / 8 ->
  aview SEGS (w_H W) m (nSH cx fp + 4) = Some 0 ->
  aview SEGS (w_H W) m (nSH cx fp + 5) = Some 0 ->
  0 <= d -> 0 <= n -> d + n <= 16 ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF (nF cx fp + NO_PH + d) n.
Proof.
intros cx fp W m d n H64 H4096 ESH H4 H5 Hd Hn Hdn x Hx.
exists 0. split; [|left; reflexivity].
assert (EFd : nF cx fp = 64 * (nF cx fp / 64))
  by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
assert (EF8 : nF cx fp / 8 = 8 * (nF cx fp / 64))
  by (rewrite EFd at 1; replace (64 * (nF cx fp / 64)) with (8 * (nF cx fp / 64) * 8) by lia;
      apply Z.div_mul; lia).
rewrite ESH, EF8 in H4, H5. unfold shadow_of_addr.
unfold NO_PH in Hx.
destruct (Z.le_gt_cases (nF cx fp + 40) x) as [Hhi|Hlo].
- assert (Hq : x / 8 = 8 * (nF cx fp / 64) + 5)
    by (symmetry; apply (Z.div_unique x 8 (8 * (nF cx fp / 64) + 5) (x - (nF cx fp + 40)));
        [clear - Hhi Hx Hd Hn Hdn; left; lia | clear - EFd; lia]).
  rewrite Hq.
  replace (SHADOW_OFF + (8 * (nF cx fp / 64) + 5)) with (SHADOW_OFF + 8 * (nF cx fp / 64) + 5)
    by (clear; lia).
  exact H5.
- assert (Hq : x / 8 = 8 * (nF cx fp / 64) + 4)
    by (symmetry; apply (Z.div_unique x 8 (8 * (nF cx fp / 64) + 4) (x - (nF cx fp + 32)));
        [clear - Hlo Hx Hd Hn Hdn; left; lia | clear - EFd; lia]).
  rewrite Hq.
  replace (SHADOW_OFF + (8 * (nF cx fp / 64) + 4)) with (SHADOW_OFF + 8 * (nF cx fp / 64) + 4)
    by (clear; lia).
  exact H4.
Qed.

(* One byte, read back from the shadow (PcapSourceNextEntry's nx_val_mem1). *)
Lemma hb_val_mem1 : forall (H : word -> bool) (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> 0 <= v < 256 -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv Hr k Hk. replace k with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hv. destruct (mbyte SEGS (mrestrict H m) a) as [b|] eqn:Hb; [|discriminate Hv].
cbn [option_map] in Hv. injection Hv as <-. f_equal.
rewrite (le_byte_small (bv_unsigned b) 1 0) by (cbn [Z.of_nat]; lia).
rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma hb_seat : forall cx fp k2 ly3 S3 W3 ms3 md3 q lh,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 19 = w64 (nF cx fp + NO_PH) ->
  getr (ms_regs ms3) 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) ->
  0 <= nx_ol cx lh < 2 ^ 32 ->
  st_ok_pi SEGS VAL (hb_E cx (nx_ol cx lh) ms3) (hb_ss NP_hd_ra) (restrict (w_H W3) ms3).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 q lh HB HJ3 Hfr3 HMID R19 R20 HOL.
destruct HMID as ((HBODY0 & HSLOTS) & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh0 & HPSAT &
  HRADDR & HSRC & Hqrange & HBJ & HTSV).
destruct HBODY0 as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW &
  HSHADOW & Hshlen & R25 & HFK).
destruct HSLOTS as (SFK & SF0 & SBUF & STS & SSB & SPS12 & SSH12 & SOFF8 & SOFF12 & SPH4 & SPH8 & SPH12).
destruct HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (hb_geo B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HFSpres & HPS4096 & HPSceil &
   HPSapp & HPSimg & HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hown & Hfa1 & Hfa2 & _ & _ & Hswz & _).
pose proof HJ3 as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* the constants as equations: `unfold ... in *` would rewrite inside the journals, which costs the
   kernel a tree the size of the whole premise set *)
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HSWO : PS_SW_OFF = 8) by reflexivity.
assert (HOLO : PS_OL_OFF = 12) by reflexivity.
assert (HNOP : NO_PH = 32) by reflexivity.
assert (HSHO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
assert (HKHM : kHighMemBeg = 17594333495296) by reflexivity.
assert (HASC : @ASAN_CEIL rc = alloc_ceiling) by reflexivity.
assert (HSW : n_sw cx = 0 \/ n_sw cx = 1) by (apply Hswz; exact Hh0).
(* the struct's bytes are present: the caller's journal lets this call write them *)
assert (HPSpres : forall a, n_ps cx <= a < n_ps cx + PS_LEN -> apresent (w_H W3) (ms_mem ms3) a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ3 _)).
  right. right. right. exists (n_cid cx), (n_pos cx). split; [right; exact Hown|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFA. lia. }
(* the shadow byte of ps + 8 (= that of ps + 12) is 0 *)
assert (Hsh8 : aview SEGS (w_H W3) (ms_mem ms3) (SHADOW_OFF + (n_ps cx + PS_SW_OFF) / 8) = Some 0).
{ apply (hb_shadow0 (aview SEGS (w_H W3) (ms_mem ms3)) (n_ps cx + PS_SW_OFF) 16);
  [ unfold PS_SW_OFF; rewrite <- Zplus_mod_idemp_l, HPS8; reflexivity | lia |].
  intros x Hx. apply HRADDR. lia. }
assert (ESH12 : shadow_of_addr SHADOW_OFF (n_ps cx + PS_OL_OFF) = SHADOW_OFF + (n_ps cx + PS_SW_OFF) / 8).
{ unfold shadow_of_addr, PS_OL_OFF, PS_SW_OFF. f_equal.
  pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)) as D. rewrite HPS8, Z.add_0_r in D.
  replace (n_ps cx + 12) with ((n_ps cx / 8 + 1) * 8 + 4) by lia.
  replace (n_ps cx + 8) with ((n_ps cx / 8 + 1) * 8 + 0) by lia.
  rewrite (Z.div_add_l (n_ps cx / 8 + 1) 8 4 ltac:(lia)),
          (Z.div_add_l (n_ps cx / 8 + 1) 8 0 ltac:(lia)).
  reflexivity. }
(* the environment *)
set (E := hb_E cx (nx_ol cx lh) ms3).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; unfold hb_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = w64 (n_sp1 cx))
  by (rewrite (EW 9%nat (9%bv : bv 5) ltac:(vm_compute; reflexivity)); exact Rs1).
assert (E19 : ew E 19 = w64 (nF cx fp + NO_PH))
  by (rewrite (EW 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R19).
assert (E20 : ew E 20 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)))
  by (rewrite (EW 20%nat (20%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R20).
assert (E25 : ew E 25 = w64 (nSH cx fp))
  by (rewrite (EW 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R25).
assert (E27 : ew E 27 = w64 (n_ps cx + PS_SW_OFF))
  by (rewrite (EW 27%nat (27%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R27).
assert (E32 : ew E 32 = w64 (n_sw cx)).
{ subst E. unfold hb_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra (ms_regs ms3) _ 0). }
assert (E33 : ew E 33 = w64 (nx_ol cx lh)).
{ subst E. unfold hb_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_extra (ms_regs ms3) _ 1). }
(* the numeric bounds of the atoms *)
assert (HFhi : nF cx fp + 64 <= 2 ^ 47) by lia.
assert (Hsh8v : SHADOW_OFF + (n_ps cx + PS_SW_OFF) / 8 = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF))
  by reflexivity.
assert (HdivPS : 0 <= (n_ps cx + PS_SW_OFF) / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
assert (HdivF : 0 <= nF cx fp / 8 < 2 ^ 44).
{ split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
assert (USP : bv_unsigned (ew E 9) = n_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = nF cx fp + NO_PH)
  by (rewrite E19; apply unsigned_lit_small; unfold NO_PH; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF + (n_ps cx + PS_SW_OFF) / 8)
  by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = nSH cx fp)
  by (rewrite E25; apply unsigned_lit_small; rewrite ESH; unfold SHADOW_OFF; lia).
assert (U27 : bv_unsigned (ew E 27) = n_ps cx + PS_SW_OFF)
  by (rewrite E27; apply unsigned_lit_small; lia).
(* the machine state's shape *)
assert (Hms : restrict (w_H W3) ms3 =
              mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_hd_ra)) (mrestrict (w_H W3) (ms_mem ms3))
                   (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem]
    in Hpc, Hresv, Hsvc, Hrom, Hfregs, Hfcsr. subst. reflexivity. }
(* the struct's byte-swap flag and its orig field, and the two shadow bytes of `ph` (0 while it is in scope) *)
assert (Vsw : val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ps cx + PS_SW_OFF) 4 (n_sw cx))
  by exact (proj1 (proj2 HPSAT)).
assert (Vol : val_mem SEGS (rdW W3 (ms_mem ms3)) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx lh))
  by exact (proj1 (proj2 (proj2 HPSAT))).
assert (Vsh4 : aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 4) = Some 0).
{ pose proof (HSHADOW 4%nat ltac:(vm_compute; lia)) as H4.
  replace (nth 4%nat NSH_ph 0) with 0 in H4 by (vm_compute; reflexivity).
  replace (Z.of_nat 4) with 4 in H4 by reflexivity. exact H4. }
assert (Vsh5 : aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 5) = Some 0).
{ pose proof (HSHADOW 5%nat ltac:(vm_compute; lia)) as H5.
  replace (nth 5%nat NSH_ph 0) with 0 in H5 by (vm_compute; reflexivity).
  replace (Z.of_nat 5) with 5 in H5 by reflexivity. exact H5. }
(* Keep only the small facts: the journals and the stream predicates below would make every `lia`
   of the rest scan a term the size of the whole premise set. *)
clear - E9 E19 E20 E25 E27 E32 E33 USP U19 U20 U25 U27 ESH ESH12 Hsh8 Hsh8v HdivPS HdivF
         Hpres3 HPSpres HFSpres SF0 SSH12 SPH12 SPS12 SFK SPH8 SPH4 Vsw Vol Vsh4 Vsh5 Hms HOL
         HF4096 HFceil HF64 HFapp HFimg HPS4096 HPSceil HPSapp HPSimg HPS8 HdPF
         Hsplo Hsphi Hsp1b Hsp1m Hwlo Hwhi Hac HSW
         HPL HSWO HOLO HNOP HSHO HNSB HKLS HKHM HASC C1 C2 C3 C4 C5.
rewrite Hms. unfold hb_ss. apply pa_entry_st_ok_full.
- subst E. unfold hb_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold hb_regions, hb_slots, hb_ps8, hb_sh8, hb_fsh.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite USP. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpres3. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_F0 8 (SOff 19 (- NO_PH)) (nF cx fp));
      [ cbn [sv_denot]; rewrite U19; f_equal; unfold NO_PH; lia | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SF0).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_SH12 8 (SOff 20 0)
               (shadow_of_addr SHADOW_OFF (n_ps cx + PS_OL_OFF)));
      [ cbn [sv_denot]; rewrite U20, Z.add_0_r, ESH12; reflexivity
      | rewrite ESH12; cbn; unfold SHADOW_OFF; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SSH12).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_PH12 8 (SOff 19 12) (nF cx fp + NO_PH + 12));
      [ cbn [sv_denot]; rewrite U19; reflexivity | cbn; unfold NO_PH; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SPH12).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_PS12 8 (SOff 27 4) (n_ps cx + PS_OL_OFF));
      [ cbn [sv_denot]; rewrite U27; f_equal; unfold PS_SW_OFF, PS_OL_OFF; lia
      | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SPS12).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_FK 8 (SOff 19 (- NO_PH)) (nF cx fp));
      [ cbn [sv_denot]; rewrite U19; f_equal; unfold NO_PH; lia | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SFK).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_PH8 8 (SOff 19 8) (nF cx fp + NO_PH + 8));
      [ cbn [sv_denot]; rewrite U19; reflexivity | cbn; unfold NO_PH; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SPH8).
    * apply (chunk_ok_val SEGS E _ (n_sp1 cx) NS_PH4 8 (SOff 19 4) (nF cx fp + NO_PH + 4));
      [ cbn [sv_denot]; rewrite U19; reflexivity | cbn; unfold NO_PH; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ SPH4).
  + rewrite U27. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply HPSpres. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (n_ps cx + PS_SW_OFF) 0 4 (SOff 32 0) (n_sw cx));
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact Vsw.
    * apply (chunk_ok_val SEGS E _ (n_ps cx + PS_SW_OFF) 4 4 (SOff 33 0) (nx_ol cx lh));
      [ cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | cbn; lia | cbn; lia |].
      replace (n_ps cx + PS_SW_OFF + 4) with (n_ps cx + PS_OL_OFF) by lia.
      exact Vol.
  + rewrite U20, Hsh8v. split; [unfold shadow_of_addr, SHADOW_OFF; lia|].
    split; [unfold shadow_of_addr, SHADOW_OFF; lia|].
    split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) 0 1 (SLit 0) 0);
    [ reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. apply (hb_val_mem1 (w_H W3) (ms_mem ms3)); [|lia]. exact Hsh8.
  + rewrite U25. split; [rewrite ESH; unfold SHADOW_OFF; lia|].
    split; [rewrite ESH; unfold SHADOW_OFF; lia|].
    split.
    { intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))). }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val SEGS E _ (nSH cx fp) 4 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply (hb_val_mem1 (w_H W3) (ms_mem ms3)); [|lia].
      exact (Vsh4).
    * apply (chunk_ok_val SEGS E _ (nSH cx fp) 5 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      apply (hb_val_mem1 (w_H W3) (ms_mem ms3)); [|lia].
      exact (Vsh5).
- apply pairwise_disjoint_of_extents.
  unfold hb_regions, hb_slots, hb_ps8, hb_sh8, hb_fsh, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite USP, U20, U25, U27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite ESH.
  assert (EPSd : n_ps cx = 8 * (n_ps cx / 8)) by (pose proof (Z.div_mod (n_ps cx) 8 ltac:(lia)); lia).
  assert (EFd : nF cx fp = 64 * (nF cx fp / 64)) by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
  assert (EF8 : nF cx fp / 8 = 8 * (nF cx fp / 64))
    by (rewrite EFd at 1; replace (64 * (nF cx fp / 64)) with (8 * (nF cx fp / 64) * 8) by lia;
        apply Z.div_mul; lia).
  assert (EPS8 : (n_ps cx + PS_SW_OFF) / 8 = n_ps cx / 8 + 1).
  { rewrite EPSd at 1. unfold PS_SW_OFF.
    replace (8 * (n_ps cx / 8) + 8) with ((n_ps cx / 8 + 1) * 8) by lia. apply Z.div_mul. lia. }
  unfold in_app in HPSapp, HFapp.
  rewrite EPS8, EF8.
  revert HPSapp HFapp HdPF HPS4096 HPSceil HF4096 HFceil Hsplo Hsphi Hsp1b Hac EPSd EFd
         HPL HSWO HOLO HNOP HSHO HNSB HKLS HKHM HASC.
  clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [hb_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U19.
  split; [unfold NO_PH; lia|]. split; [|lia]. change (2 ^ 5) with 32.
  assert (EFd : nF cx fp = 64 * (nF cx fp / 64)) by (pose proof (Z.div_mod (nF cx fp) 64 ltac:(lia)); lia).
  rewrite EFd. unfold NO_PH.
  replace (64 * (nF cx fp / 64) + 32) with ((2 * (nF cx fp / 64) + 1) * 32) by lia.
  apply Z.mod_mul. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* One call of rd_u32                                                                               *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma hb_sext_sw : forall sw, sw = 0 \/ sw = 1 ->
  sext 64 (bv_extract 0 32 (Z_to_bv 64 (bv_unsigned (w64 sw) + 0))) = w64 sw.
Proof. intros sw [-> | ->]; vm_compute; reflexivity. Qed.

(* At a call of rd_u32 (0x81788, 0x817a8, 0x817c8, 0x817f0) the run stands at the callee with a0 = ph + 4 j,
   a1 = ps->swapped and ra = the next slot. The callee's contract H_rdu32 takes this call's journal as its
   caller journal: the four bytes lie in this call's own class-0 frame (frames S3), and they are apart from the
   callee's 16-byte frame below sp1 because a frame lies under the heap ceiling, far below the machine stack.
   After the call the symbolic state is the same, with the caller-saved registers havocked from atom k on
   (st_ok_pi_after_call), provided every region of the run is kept (HRK: the callee writes only below sp1). *)
Lemma hb_call : forall cx fp k2 ly3 S3 W ms md (Q : world SEGS -> config -> Prop) E ssc (k : nat) retk j sw
    b0 b1 b2 b3,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  img_env VAL A_LIM E ->
  st_ok SEGS E ssc (restrict (w_H W) ms) ->
  ss_pc ssc = @pa_sigma _ pcap_listing PI PS_rd_u32 -> ss_resv ssc = None ->
  (k + 16 <= A_TEXT)%nat -> ss_atoms_p (pband k A_TEXT) ssc = true ->
  regions_wf (ss_mem ssc) = true -> no_cdata (ss_mem ssc) = true ->
  mem_atoms_p (pband k A_TEXT) (ss_mem ssc) = true ->
  sr_get (ss_regs ssc) 1 = SOff A_TEXT retk -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  sv_denot E (sr_get (ss_regs ssc) 10) = w64 (nF cx fp + NO_PH + 4 * j) -> 0 <= j < 4 ->
  sv_denot E (sr_get (ss_regs ssc) 11) = w64 sw -> (sw = 0 \/ sw = 1) ->
  sv_denot E (sr_get (ss_regs ssc) 2) = w64 (n_sp1 cx) ->
  garr8 SEGS (rdW W (ms_mem ms)) (nF cx fp + NO_PH + 4 * j) [b0; b1; b2; b3] ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (nF cx fp + NO_PH + 4 * j) 4 ->
  (forall mem2 md2,
     ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
       ((NX_CID, fp) :: n_own cx) ly3 S3 W mem2 md2 k2 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) ->
     Forall (region_kept SEGS E (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) mem2)) (ss_mem ssc)) ->
  (forall regs2 mem2 md2,
     st_ok_pi SEGS VAL (havoc E k (map (getr regs2) CLOB)) (ss_after_call ssc (ss_mem ssc) k retk)
       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS))) ->
     ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
       ((NX_CID, fp) :: n_own cx) ly3 S3 W mem2 md2 k2 ->
     aregs_preserved (ms_regs ms) regs2 ->
     getr regs2 10 = w64 (bv_swrap 32 (rd_u32_val sw b0 b1 b2 b3)) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) (ms_mem ms) a) ->
     m_fds md2 = m_fds md -> m_fs md2 = m_fs md ->
     SRr SEGS W (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros cx fp k2 ly3 S3 W ms md Q E ssc k retk j sw b0 b1 b2 b3 HB HJ Hfr3 HEI HS Hpc Hrv Hk Hat Hwf Hnc Hmat
  Hra Hrk Hrk2 Ha0 Hj Ha1 Hsw Hsp Hbytes Hsh HRK HK.
destruct (hb_geo B KS LAWS cx fp k2 ly3 S3 W (ms_mem ms) md HB HJ Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsplo & Hsphi & Hsp1b & Hsp1m &
   Hwlo & Hwhi & Hac).
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HNOP : NO_PH = 32) by reflexivity.
pose proof (st_ok_restrict_mkst SEGS (w_H W) E ssc ms HS Hrv) as Hms.
assert (RG : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ssc) r))
  by (intros r; exact (st_ok_restrict_reg SEGS (w_H W) E ssc ms r HS)).
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + retk)) by (rewrite RG, Hra; exact (codeptr_val E retk HEI)).
assert (R10 : getr (ms_regs ms) 10 = w64 (nF cx fp + NO_PH + 4 * j)) by (rewrite RG; exact Ha0).
assert (R11 : getr (ms_regs ms) 11 = w64 sw) by (rewrite RG; exact Ha1).
assert (R2 : getr (ms_regs ms) 2 = w64 (n_sp1 cx)) by (rewrite RG; exact Hsp).
assert (USP : spZ (ms_regs ms) = n_sp1 cx) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hfin : In (NX_CID, fp) (frames S3)) by (rewrite Hfr3; left; reflexivity).
rewrite Hms, Hpc, pa_sigma_rd_u32.
eapply SRr_bind.
{ refine (H_rdu32 (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md k2 (ms_regs ms) (nF cx fp + NO_PH + 4 * j)
    b0 b1 b2 b3 NX_CID fp HJ _ R10 _ _ _ Hfin _ _ _ Hbytes Hsh).
  - rewrite R1. apply ret_ok_codeptr_v; [exact Hrk | exact Hrk2].
  - rewrite USP.
    pose proof (Z.div_mod (n_sp1 cx) 32 ltac:(lia)) as D. rewrite Hsp1m, Z.add_0_r in D.
    rewrite D. replace (32 * (n_sp1 cx / 32)) with ((2 * (n_sp1 cx / 32)) * 16) by lia.
    apply Z.mod_mul. lia.
  - rewrite USP. unfold RDU32_FRAME. lia.
  - rewrite USP. lia.
  - rewrite EFA. change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp). lia.
  - rewrite EFA. change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp).
    change (fs_frame_bytes NX_CID) with 64. lia.
  - left. rewrite USP. unfold RDU32_FRAME. lia. }
cbv beta. intros W2 c2 _ (regs2 & mem2 & md2 & -> & -> & HJ2 & HP & Ha02 & Hfds & Hfs & Hb2 & Hun).
rewrite R11, unsigned_lit_small in Ha02 by (destruct Hsw as [-> | ->]; lia).
rewrite USP in Hun. unfold RDU32_FRAME in Hun. rewrite R1.
apply (HK regs2 mem2 md2); [| exact HJ2 | exact HP | exact Ha02 | exact Hun | exact Hfds | exact Hfs].
rewrite restrict_mkst_fx.
apply (st_ok_pi_after_call k E ssc (restrict (w_H W) ms) regs2 (mrestrict (w_H W) mem2) (ss_mem ssc) retk HEI Hrk
  HS Hrv Hk Hat Hwf Hnc Hmat (submem_refl _) Hra HP).
exact (HRK mem2 md2 HJ2 Hun).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* What the run may write, and what a callee keeps                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

(* The run's three write windows are the caller's: the slot NS_SEC of this call's machine frame (inside the
   stack window), ps->orig (a byte of the caller's struct, in the frame the caller owns), and the two shadow
   bytes of `ph` (in this call's own frame's shadow). *)
Lemma hb_awr : forall cx fp k2 ly3 S3 W3 mem3 md3 (E : env),
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mem3 md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  bv_unsigned (ew E 9) = n_sp1 cx -> bv_unsigned (ew E 27) = n_ps cx + PS_SW_OFF ->
  bv_unsigned (ew E 25) = nSH cx fp ->
  awr_ok E hb_regions (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B ly3 S3) ly3
    ((NX_CID, fp) :: n_own cx).
Proof.
intros cx fp k2 ly3 S3 W3 mem3 md3 E HB HJ3 Hfr3 U9 U27 U25.
destruct (hb_geo B KS LAWS cx fp k2 ly3 S3 W3 mem3 md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & _ & _ & ESH & _ & _ & _ & _ & _ & _ & HPS8 & _ & Hsplo & Hsphi & Hsp1b &
   Hsp1m & Hwlo & Hwhi & Hac).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hown & Hfa1 & Hfa2 & _).
assert (HNSB : NX_STK_B = 8464) by reflexivity.
unfold hb_regions, hb_slots, hb_ps8, hb_sh8, hb_fsh.
eapply awr_ok_cons_gen; [reflexivity | exact U9 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. lia. }
eapply awr_ok_cons_gen; [reflexivity | exact U27 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right. right. right. exists (n_cid cx), (n_pos cx). split; [right; exact Hown|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFA. unfold PS_SW_OFF, PS_LEN in *. lia. }
apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
eapply awr_ok_cons_gen; [reflexivity | exact U25 | | apply awr_ok_nil].
intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
right. right. right. exists NX_CID, fp. split; [left; reflexivity|].
right. unfold in_zr. cbn [fst snd]. rewrite EFA.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp).
change (fs_frame_bytes NX_CID / 8) with 8. unfold shadow_addr. rewrite <- ESH. lia.
Qed.

(* awr_ok and region_kept depend on a region's base and bounds, not on its chunks: so they hold of any state
   the run reaches, whose regions have the skeleton of hb_regions. *)
Lemma hb_awr_sk : forall (E : env) rs STK sp0 FP bl0 blc ly own,
  skeleton rs = skeleton hb_regions ->
  awr_ok E hb_regions STK sp0 FP bl0 blc ly own -> awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs STK sp0 FP bl0 blc ly own Hsk H a Hin. apply H.
apply (in_wrange_skeleton E rs hb_regions a Hsk Hin).
Qed.

Lemma hb_kept_sk : forall (E : env) (m m' : word -> option byte) rs rs0,
  skeleton rs = skeleton rs0 ->
  Forall (region_kept SEGS E m m') rs0 -> Forall (region_kept SEGS E m m') rs.
Proof.
intros E m m' rs rs0. revert rs. induction rs0 as [|r0 rs0 IH]; intros rs Hsk HF.
- destruct rs as [|r rs]; [constructor | cbn in Hsk; discriminate].
- destruct rs as [|r rs]; [cbn in Hsk; discriminate|].
  cbn [skeleton map] in Hsk. injection Hsk as Hb Hlo Hhi Hwlo Hwhi Hrest.
  pose proof (Forall_inv HF) as HR0. pose proof (Forall_inv_tail HF) as HF0.
  constructor; [|exact (IH rs Hrest HF0)].
  unfold region_kept in *. rewrite Hb, Hlo, Hhi, Hwlo, Hwhi. exact HR0.
Qed.

(* The four regions of the run are kept across a callee that writes only inside [wlo, whi), a window apart
   from all four, as long as their written bytes stay writable. *)
Lemma hb_kept : forall (E : env) (m m' : word -> option byte) (sp1 ps8 sh8 nsh wlo whi : Z),
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 27) = ps8 ->
  bv_unsigned (ew E 20) = sh8 -> bv_unsigned (ew E 25) = nsh ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> mbyte SEGS m' a = mbyte SEGS m a) ->
  0 <= sp1 -> sp1 + 128 <= 2 ^ 64 -> 0 <= ps8 -> ps8 + 8 <= 2 ^ 64 ->
  0 <= sh8 -> sh8 + 1 <= 2 ^ 64 -> 0 <= nsh -> nsh + 6 <= 2 ^ 64 ->
  (sp1 + 128 <= wlo \/ whi <= sp1 + 56) -> (ps8 + 8 <= wlo \/ whi <= ps8) ->
  (sh8 + 1 <= wlo \/ whi <= sh8) -> (nsh + 6 <= wlo \/ whi <= nsh + 4) ->
  (forall o, 56 <= o < 64 -> writable_at SEGS m' (sp1 + o)) ->
  (forall o, 4 <= o < 8 -> writable_at SEGS m' (ps8 + o)) ->
  (forall o, 4 <= o < 6 -> writable_at SEGS m' (nsh + o)) ->
  Forall (region_kept SEGS E m m') hb_regions.
Proof.
intros E m m' sp1 ps8 sh8 nsh wlo whi U9 U27 U20 U25 HM
  Hs0 Hs1 Hp0 Hp1 Hh0 Hh1 Hn0 Hn1 Ds Dp Dh Dn Ws Wp Wn.
unfold hb_regions, hb_slots, hb_ps8, hb_sh8, hb_fsh.
repeat apply Forall_cons; try apply Forall_nil; unfold region_kept;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val].
- rewrite U9. split; [intros a Ha; apply HM; lia|].
  intros a Ha _. replace a with (sp1 + (a - sp1)) by lia. apply Ws. lia.
- rewrite U27. split; [intros a Ha; apply HM; lia|].
  intros a Ha _. replace a with (ps8 + (a - ps8)) by lia. apply Wp. lia.
- rewrite U20. split; [intros a Ha; apply HM; lia|]. intros a Ha; lia.
- rewrite U25. split; [intros a Ha; apply HM; lia|].
  intros a Ha _. replace a with (nsh + (a - nsh)) by lia. apply Wn. lia.
Qed.

(* What a callee of this phase keeps: it writes only its own frame, below sp1, and the run's four regions
   are all above it (the spill slots) or far below the machine stack (the struct and the shadow). *)
Lemma hb_kept_call : forall cx fp k2 ly3 S3 (W : world SEGS) (E : env)
    (m mem2 : word -> option byte) md2 rs,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W mem2 md2 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  bv_unsigned (ew E 9) = n_sp1 cx -> bv_unsigned (ew E 27) = n_ps cx + PS_SW_OFF ->
  bv_unsigned (ew E 20) = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF) ->
  bv_unsigned (ew E 25) = nSH cx fp ->
  skeleton rs = skeleton hb_regions ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) m a) ->
  Forall (region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W) mem2)) rs.
Proof.
intros cx fp k2 ly3 S3 W E m mem2 md2 rs HB HJ Hfr3 U9 U27 U20 U25 Hsk HUN.
destruct (hb_geo B KS LAWS cx fp k2 ly3 S3 W mem2 md2 HB HJ Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HFSpres & HPS4096 & HPSceil &
   HPSapp & HPSimg & HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & Hown & Hfa1 & Hfa2 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HSWO : PS_SW_OFF = 8) by reflexivity.
assert (HSHO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HdivF : 0 <= nF cx fp / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HdivPS : 0 <= (n_ps cx + PS_SW_OFF) / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HPSpres : forall a, n_ps cx <= a < n_ps cx + PS_LEN -> apresent (w_H W) mem2 a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ _)).
  right. right. right. exists (n_cid cx), (n_pos cx). split; [right; exact Hown|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFA. lia. }
apply (hb_kept_sk E _ _ rs hb_regions Hsk).
apply (hb_kept E (mrestrict (w_H W) m) (mrestrict (w_H W) mem2) (n_sp1 cx) (n_ps cx + PS_SW_OFF)
         (shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)) (nSH cx fp) (n_sp1 cx - 16) (n_sp1 cx)
         U9 U27 U20 U25).
- intros a Ha Hw. apply (mbyte_of_aview SEGS). apply HUN; [exact Ha | exact Hw].
- clear - Hsp1b Hsplo Hac HNSB; lia.
- clear - Hsp1b Hsphi Hac HNSB; lia.
- clear - HPS4096 HSWO; lia.
- clear - HPSceil HPL HSWO Hac; lia.
- unfold shadow_of_addr; clear - HdivPS HSHO; lia.
- unfold shadow_of_addr; clear - HdivPS HSHO Hac Hsplo Hsp1b HNSB; lia.
- clear - ESH HdivF HSHO; lia.
- clear - ESH HdivF HSHO Hac Hsplo Hsp1b HNSB; lia.
- clear; lia.
- clear - HPSceil HPL HSWO Hac Hsplo Hsp1b HNSB; lia.
- unfold shadow_of_addr; clear - HdivPS HSHO Hac Hsplo Hsp1b HNSB; lia.
- clear - ESH HdivF HSHO Hac Hsplo Hsp1b HNSB; lia.
- intros o Ho. apply (apresent_writable SEGS). apply Hpres. clear - Ho Hsp1b Hwlo Hwhi HNSB; lia.
- intros o Ho. apply (apresent_writable SEGS). apply HPSpres. clear - Ho HPL HSWO; lia.
- intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(clear - Ho; lia))).
Qed.

(* What one segment of the run leaves alone: everything but the three windows. (The frame fact comes
   first, so that it fixes the region list before the skeleton check is computed.) *)
Lemma hb_unch : forall (E : env) rs (W : world SEGS) (m m' : word -> option byte) sp1 ps8 nsh,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  skeleton rs = skeleton hb_regions ->
  bv_unsigned (ew E 9) = sp1 -> bv_unsigned (ew E 27) = ps8 -> bv_unsigned (ew E 25) = nsh ->
  forall a, 0 <= a < 2 ^ 64 ->
  ~ (sp1 + 56 <= a < sp1 + 64) -> ~ (ps8 + 4 <= a < ps8 + 8) -> ~ (nsh + 4 <= a < nsh + 6) ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E rs W m m' sp1 ps8 nsh HF Hsk U9 U27 U25 a Ha N1 N2 N3.
apply (kept_of_frame E rs (w_H W) m m'
  (fun x => (sp1 + 56 <= x < sp1 + 64) \/ (ps8 + 4 <= x < ps8 + 8) \/ (nsh + 4 <= x < nsh + 6)) HF);
  [| exact Ha | tauto].
intros b wlo whi x Hin Hr.
assert (Hw : windows rs = windows hb_regions).
{ clear - Hsk. revert rs Hsk. induction hb_regions as [|r0 rs0 IH]; intros rs Hsk.
  - destruct rs as [|r rs]; [reflexivity | cbn in Hsk; discriminate].
  - destruct rs as [|r rs]; [cbn in Hsk; discriminate|].
    cbn [skeleton map] in Hsk. injection Hsk as Hb Hlo Hhi Hwlo Hwhi Hrest.
    unfold windows in *. cbn [map]. rewrite Hb, Hwlo, Hwhi. f_equal. apply IH. exact Hrest. }
rewrite Hw in Hin. unfold windows, hb_regions, hb_slots, hb_ps8, hb_sh8, hb_fsh in Hin.
cbn [map In YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
repeat (destruct Hin as [Hq|Hin];
  [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U9, ?U27, ?U25 in Hr;
   first [exfalso; lia | left; lia | right; left; lia | right; right; lia] |]).
destruct Hin.
Qed.



(* NP_exit from this phase: the run wrote nothing of the caller's but (possibly) ps->orig, and the model says
   the walk stopped at this turn's q. *)
Lemma hb_exit_at : forall cx fp k2 ly3 S3 (W : world SEGS) ms ms' md3 md' q lh rr,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md3 k2 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms') md' k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_hd_ra NSH_ph (nx_E cx) (q + nx_hk (n_C cx) q) (nx_ol cx lh)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W ms md3 ->
  nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = false ->
  nx_pos (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = q + nx_hk (n_C cx) q ->
  nx_lh (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = lh ->
  nx_res (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = rr ->
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
     ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
     aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  (forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
  ms_pc_val ms' = w64 (BASE + NP_exit) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  nregs cx ms' -> getr (ms_regs ms') 25 = w64 (nSH cx fp) ->
  getr (ms_regs ms') 19 = w64 (nF cx fp) -> getr (ms_regs ms') 16 = w64 (nF cx fp) ->
  getr (ms_regs ms') 11 = w64 rr ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 4) = Some 0 ->
  aview SEGS (w_H W) (ms_mem ms') (nSH cx fp + 5) = Some 0 ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx lh) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W ms' md'.
Proof.
intros cx fp k2 ly3 S3 W ms ms' md3 md' q lh rr HB HJ HJ' Hfr3 HMID Mfit Mpos Mlh Mres UNCH HPRES
  Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25 R19 R16 R11 Hsh4 Hsh5 Vol' Hfds Hfs.
pose proof HMID as (HBODY & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh0 & HPSAT &
  HRADDR & HSRC & Hqrange & HBJ & HTSV).
assert (HNSHph : forall i, (i < 8)%nat -> i <> 4%nat -> i <> 5%nat ->
  nth i NSH_ph 0 = nth i NSH_ph 0) by (intros; reflexivity).
assert (UNCH24 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + PS_LEN) ->
  ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
  aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a).
{ intros a Ha N1 N2 N3. apply UNCH;
  [exact Ha | exact N1 | clear - N2; unfold PS_LEN, PS_OL_OFF in *; lia | exact N3]. }
split.
{ apply (hb_body_keep B KS LAWS cx fp k2 ly3 S3 W ms ms' md3 NP_hd_ra NP_exit NSH_ph HB HJ Hfr3 HBODY UNCH24
    Hpc Hresv Hsvc Hrom Hfregs Hfcsr HREGS R25);
  [ replace (nth 4 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh4
  | replace (nth 5 NSH_ph 0) with 0 by (vm_compute; reflexivity); exact Hsh5
  | exact HNSHph
  | vm_compute; reflexivity ]. }
split; [exact R19|]. split; [exact R16|].
split.
{ pose proof HJBK as (K1 & K2 & K3 & K4 & K5). split; [exact K1|]. split; [exact K2|].
  split; [exact K3|]. split; [rewrite Hfds; exact K4 | rewrite Hfs; exact K5]. }
(* the post *)
unfold nx_fin_at, nx_fin. right.
rewrite R11, Mres.
split; [exact Hh0|]. split; [reflexivity|].
destruct (hb_mid_keep B KS LAWS ASIL cx fp k2 ly3 S3 W ms ms' md3 (nx_ol cx lh) (nx_ol cx lh)
  (q + nx_hk (n_C cx) q) HB HJ Hfr3 UNCH Hh0 HPSAT Vol' HRADDR HSRC HBJ HTSV)
  as (Qps & Qra & Qsrc & Qbj & Qts).
split.
{ (* nx_kept *)
  pose proof HJ' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres' & _).
  apply (hb_kept_step B KS LAWS cx fp k2 ly3 S3 W (ms_mem ms) md3 (ms_mem ms') HB HJ Hfr3);
  [ intros a Ha N1 N2 N3; apply UNCH; [exact Ha | exact N1 | clear - N2; unfold PS_LEN, PS_OL_OFF in *; lia
                                      | exact N3]
  | exact HPRES
  | intros a Ha; apply Hpres';
    pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _);
    clear - Ha Hwlo Hwhi; lia
  | exact HKEPT ]. }
split; [rewrite Mpos; exact Qsrc|].
split.
{ unfold nx_orig, nx_vtag, nx_vid. rewrite Mlh, Mfit.
  replace (match lh with Some q0 => PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q0 | None => n_lol cx end)
    with (nx_ol cx lh) by reflexivity.
  exact Qps. }
split.
{ destruct Qbj as (bj' & Hgb & Hlen). exists bj'. split; [exact Hgb|]. split; [exact Hlen|].
  intros Hq. rewrite Mfit in Hq. discriminate Hq. }
intros Hts0. unfold nx_tsv. rewrite Mfit. exact (proj1 (Qts Hts0)).
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The phase                                                                                        *)
(* ---------------------------------------------------------------------------------------------- *)

Theorem nx_hdrb_ph : forall (POST : ncx -> world SEGS -> config -> Prop) (R : ncx -> Z -> Prop),
  nx_from SK B KS POST (nx_loop_at B MT KS R) ->
  nx_from SK B KS POST (nx_sk1_inv B MT KS R) ->
  nx_from SK B KS POST (nx_fit_inv B MT KS) ->
  nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  nx_from SK B KS POST (nx_hdra_inv B MT KS R).
Proof.
intros POST R HLOOP HSK HFIT HEXIT cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 Hfr3 HGI.
pose proof HGI as (q & lh & Hnext & HMID & Ha0 & Hgarr & R19 & R20 & Hqr & Hchain).
(* the struct's orig field for the turn's lh is a 32-bit word *)
assert (HOL : 0 <= nx_ol cx lh < 2 ^ 32).
{ pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & Hrng & _).
  pose proof HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Hh & _).
  unfold nx_ol. destruct lh as [q0|]; [apply nx_hw_range | exact (proj1 (Hrng Hh))]. }
pose proof (hb_seat cx fp k2 ly3 S3 W3 ms3 md3 q lh HB HJ3 Hfr3 HMID R19 R20 HOL) as HS.
pose proof HMID as ((HBODY0 & HSLOTS) & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh0 & HPSAT &
  HRADDR & HSRC & Hqrange & HBJ & HTSV).
pose proof HBODY0 as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HREGS & HSAVED & HHDR & HFLW &
  HSHADOW & Hshlen & R25 & HFK).
pose proof HREGS as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (hb_geo B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 HB HJ3 Hfr3) as
  (EFA & HF4096 & HFceil & HF64 & HFapp & HFimg & ESH & HFpres & HFSpres & HPS4096 & HPSceil &
   HPSapp & HPSimg & HPS8 & HdPF & Hsplo & Hsphi & Hsp1b & Hsp1m & Hwlo & Hwhi & Hac).
assert (HPL : PS_LEN = 24) by reflexivity.
assert (HSWO : PS_SW_OFF = 8) by reflexivity.
assert (HOLO : PS_OL_OFF = 12) by reflexivity.
assert (HNOP : NO_PH = 32) by reflexivity.
assert (HSHO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HNSB : NX_STK_B = 8464) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
assert (HKHM : kHighMemBeg = 17594333495296) by reflexivity.
assert (HASC : @ASAN_CEIL rc = alloc_ceiling) by reflexivity.
set (E := hb_E cx (nx_ol cx lh) ms3) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold hb_E; apply Eimg_env).
assert (EW : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr (ms_regs ms3) r)
  by (intros n r Hn; subst E; unfold hb_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx)
  by (rewrite (EW 9%nat (9%bv : bv 5) ltac:(vm_compute; reflexivity)), Rs1;
      apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = n_ps cx + PS_SW_OFF)
  by (rewrite (EW 27%nat (27%bv : bv 5) ltac:(vm_compute; reflexivity)), R27;
      apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = nSH cx fp)
  by (rewrite (EW 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity)), R25;
      apply unsigned_lit_small; rewrite ESH; unfold SHADOW_OFF;
      pose proof (Z.div_pos (nF cx fp) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_lt_upper_bound (nF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)); lia).
assert (U20 : bv_unsigned (ew E 20) = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF)).
{ rewrite (EW 20%nat (20%bv : bv 5) ltac:(vm_compute; reflexivity)), R20.
  apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF, PS_SW_OFF.
  pose proof (Z.div_pos (n_ps cx + 8) 8 ltac:(clear - HPS4096; lia) ltac:(lia)).
  pose proof (Z.div_le_upper_bound (n_ps cx + 8) 8 17592184995840 ltac:(lia)
    ltac:(clear - HPSceil HPL Hac; lia)). lia. }
assert (U19 : bv_unsigned (ew E 19) = nF cx fp + NO_PH)
  by (rewrite (EW 19%nat (19%bv : bv 5) ltac:(vm_compute; reflexivity)), R19;
      apply unsigned_lit_small; clear - HF4096 HFceil Hac HNOP; lia).
(* the frame's shadow bytes 4 and 5 at the entry: 0, `ph` is in scope *)
assert (S4 : aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 4) = Some 0).
{ pose proof (HSHADOW 4%nat ltac:(rewrite Hshlen; vm_compute; lia)) as H4.
  replace (nth 4%nat NSH_ph 0) with 0 in H4 by (vm_compute; reflexivity).
  replace (Z.of_nat 4) with 4 in H4 by reflexivity. exact H4. }
assert (S5 : aview SEGS (w_H W3) (ms_mem ms3) (nSH cx fp + 5) = Some 0).
{ pose proof (HSHADOW 5%nat ltac:(rewrite Hshlen; vm_compute; lia)) as H5.
  replace (nth 5%nat NSH_ph 0) with 0 in H5 by (vm_compute; reflexivity).
  replace (Z.of_nat 5) with 5 in H5 by reflexivity. exact H5. }
assert (EE : E = hb_E cx (nx_ol cx lh) ms3) by reflexivity.
assert (E33 : ew E 33 = w64 (nx_ol cx lh))
  by (rewrite EE; unfold hb_E; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra (ms_regs ms3) _ 1)).
assert (E32 : ew E 32 = w64 (n_sw cx))
  by (rewrite EE; unfold hb_E; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra (ms_regs ms3) _ 0)).
assert (E25 : ew E 25 = w64 (nSH cx fp))
  by (rewrite (EW 25%nat (25%bv : bv 5) ltac:(vm_compute; reflexivity)); exact R25).
pose proof (hb_awr cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 E HB HJ3 Hfr3 U9 U27 U25) as HAWR.
assert (E10 : ew E 10 = w64 (nx_hk (n_C cx) q))
  by (rewrite (EW 10%nat (10%bv : bv 5) ltac:(vm_compute; reflexivity)); exact Ha0).
assert (Hk16 : 0 <= nx_hk (n_C cx) q <= 16) by (unfold nx_hk, NX_PH_LEN; lia).
(* the geometry the window arguments below use *)
assert (HdivF : 0 <= nF cx fp / 8 <= 17592184995840)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HSHb : 2147450880 <= nSH cx fp /\ nSH cx fp + 8 <= 17594333495296)
  by (rewrite ESH; unfold SHADOW_OFF; lia).
pose proof HB as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & _ & _ & _ & _ & Hbufb & Htsb & Hstream & _).
destruct (Hstream Hh0) as (Hinh & Hinb & _ & HlenC & Hp0C & _ & _ & Hdpsh & Hdpsb & Hdts & _).
destruct (Hbufb Hh0) as (Hinbuf & Hbuf4096 & Hbufhi & _ & HlenBJ & Hcap & _ & Hdpsbuf).
pose proof (proj1 HJ3) as HAR3'.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinh) as (_ & Hh4096 & Hhceil & Hhapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ (proj1 HJ0) Hinbuf) as (_ & _ & Hbufceil & Hbufapp & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hhapp, Hbapp, Hbufapp, HPSapp, HFapp.
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil, Hhapp.
pose proof (req_size_pos (Z.of_nat (length (n_C cx)))) as Hrqb.
pose proof (req_size_pos (nx_bufn (n_cap cx))) as Hrqbuf.
unfold hb_ss in HS.
(* the journal at the phase's entry, which the run tactics consume *)
pose proof HJ3 as HJE.
(* 0x81770, 0x81774: the test `a0 = 16` *)
paj_run_sh RUNP HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR]|].
pose proof (hb_unch E _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9 U27 U25) as UN1.
pose proof (fun a Hp => apresent_grows (w_H W3) _ _ a HG Hp) as PG1.
clear HF HFr HG.
psrr_branch_pi RUNP BR HS.
- (* a0 <> 16: the header fread came up short, the EOF arm 0x81970..0x81984 *)
  (* every `lia` of this arm runs in a cleared context: the premise set carries a dozen disjunctions
     (the block / frame placements), and lia splits on each of them *)
  rewrite branch_ne_U, (U_atom E 10 (nx_hk (n_C cx) q) E10 ltac:(clear - Hk16; lia)), U_lit in Hc
    by (clear; lia).
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hshort : Z.of_nat (length (n_C cx)) - q < 16)
    by (clear - Hc Hqr; unfold nx_hk, NX_PH_LEN in Hc; lia).
  assert (Hkv : nx_hk (n_C cx) q = Z.of_nat (length (n_C cx)) - q)
    by (clear - Hshort Hqr; unfold nx_hk, NX_PH_LEN; lia).
  destruct (hb_eof_model (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) q lh Hchain
    ltac:(clear - Hqr Hp0C; lia) Hshort) as (Mq & Mlh & Mfit & Mpos & Mres).
  (* 0x81970..0x8197c: a6 := NS_FK, s3 := NS_F0, a1 := -1, then `bnez a0` *)
  paj_run_sh RUNP HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR]|].
  pose proof (hb_unch E _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9 U27 U25) as UN2.
  pose proof (fun a Hp => apresent_grows (w_H W3) _ _ a HG Hp) as PG2.
  clear HF HFr HG.
  psrr_branch_pi RUNP BR HS.
  (* both arms reach NP_exit 0x818b4 with a1 the result: -1 for a short header, 0 at the file's end *)
  all: paj_run_to_sh RUNTOP HS HJ3 NP_exit;
    [ eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR] |].
  all: pose proof (hb_unch E _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9 U27 U25) as UN3.
  all: pose proof (fun a Hp => apresent_grows (w_H W3) _ _ a HG Hp) as PG3.
  all: destruct (hb_state_of E _ W3 _ HS eq_refl) as (Zpc & Zrv & Zsv & Zrom & Zfr & Zfc).
  all: cbn [ss_pc] in Zpc.
  all: prreg HS (2%bv : bv 5) Z2; prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9;
       prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4; prreg HS (25%bv : bv 5) Z25;
       prreg HS (19%bv : bv 5) Z19; prreg HS (16%bv : bv 5) Z16; prreg HS (11%bv : bv 5) Z11.
  (* the registers at NP_exit: s3 = a6 = F (NS_F0 / NS_FK), the result in a1 *)
  all: rewrite U19 in Z19, Z16. all: rewrite E25 in Z25.
  all: replace (nF cx fp + NO_PH + -32) with (nF cx fp) in Z19, Z16 by (clear; unfold NO_PH; lia).
  (* name the state the two runs reached *)
  all: match goal with | Hp : ms_pc_val ?M = _ |- _ => set (MSX := M) in * end.
  all: assert (UNA : forall a, 0 <= a < 2 ^ 64 ->
         ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) -> ~ (n_ps cx + PS_OL_OFF <= a < n_ps cx + 16) ->
         ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
         aview SEGS (w_H W3) (ms_mem MSX) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha N1 N2 N3;
        assert (N2' : ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8))
          by (clear - N2 HSWO HOLO; lia);
        rewrite (UN3 a Ha N1 N2' N3), (UN2 a Ha N1 N2' N3); exact (UN1 a Ha N1 N2' N3)).
  all: assert (PGA : forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem MSX) a)
    by (intros a Hp; exact (PG3 a (PG2 a (PG1 a Hp)))).
  all: assert (ZREGS : nregs cx MSX)
    by (split; [rewrite Z2; exact Rsp | split; [rewrite Z8; exact Rs0 |
        split; [rewrite Z9; exact Rs1 | split; [rewrite Z3; exact Rgp | rewrite Z4; exact Rtp]]]]).
  (* the two shadow bytes of `ph` are the frame-shadow region's chunks, untouched on this path *)
  all: assert (ASH : forall i, i = 4 \/ i = 5 ->
         aview SEGS (w_H W3) (ms_mem MSX) (nSH cx fp + i) = Some 0)
    by (intros i Hi;
        let HX := fresh "HX" in
        destruct Hi as [-> | ->];
        [ pose proof (hb_chunk_byte E _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
            ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX
        | pose proof (hb_chunk_byte E _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
            ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX ];
        cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX; rewrite U25 in HX; exact HX).
  (* ps->orig is the second chunk of the struct region; on this path the run has not written it *)
  all: assert (AOL : val_mem SEGS (rdW W3 (ms_mem MSX)) (n_ps cx + PS_OL_OFF) 4 (nx_ol cx lh))
    by (pose proof (hb_chunk_val E _ W3 MSX 1%nat hb_ps8 (YP09.mkChunk 4 (CVal 4 (SOff 33 0))) 4
          (SOff 33 0) (nx_ol cx lh) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl
          ltac:(cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
          ltac:(cbn; clear - HOL; lia) ltac:(cbn; lia)) as HX;
        cbn [YP09.r_base YP09.c_off hb_ps8 base_val N.to_nat] in HX; rewrite U27 in HX;
        replace (n_ps cx + PS_SW_OFF + 4) with (n_ps cx + PS_OL_OFF) in HX
          by (clear - HSWO HOLO; lia);
        exact HX).
  + (* a0 <> 0: a short header (KCutH), the call returns -1 *)
    rewrite branch_ne_U, (U_atom E 10 (nx_hk (n_C cx) q) E10 ltac:(clear - Hk16; lia)), U_lit in Hc0
      by (clear; lia).
    apply negb_true_iff, Z.eqb_neq in Hc0.
    apply (HEXIT cx fp k2 ly3 S3 W3 MSX _ HB HJ3 Hfr3).
    refine (hb_exit_at cx fp k2 ly3 S3 W3 ms3 MSX md3 _ q lh (-1) HB HJE HJ3 Hfr3 HMID Mfit
              ltac:(rewrite Mpos; clear - Hkv; lia) Mlh
              ltac:(rewrite Mres;
                    destruct (Z.eqb_spec (Z.of_nat (length (n_C cx)) - q) 0) as [Hz|Hz];
                    [clear - Hz Hc0 Hkv; lia | reflexivity])
              UNA PGA Zpc Zrv Zsv Zrom Zfr Zfc ZREGS Z25 Z19 Z16
              ltac:(rewrite Z11; apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity)
              (ASH 4 (or_introl eq_refl)) (ASH 5 (or_intror eq_refl)) AOL eq_refl eq_refl).
  + (* a0 = 0: the file is at its end (KEnd), the call returns 0 *)
    rewrite branch_ne_U, (U_atom E 10 (nx_hk (n_C cx) q) E10 ltac:(clear - Hk16; lia)), U_lit in Hc0
      by (clear; lia).
    apply negb_false_iff, Z.eqb_eq in Hc0.
    apply (HEXIT cx fp k2 ly3 S3 W3 MSX _ HB HJ3 Hfr3).
    refine (hb_exit_at cx fp k2 ly3 S3 W3 ms3 MSX md3 _ q lh 0 HB HJE HJ3 Hfr3 HMID Mfit
              ltac:(rewrite Mpos; clear - Hkv; lia) Mlh
              ltac:(rewrite Mres;
                    destruct (Z.eqb_spec (Z.of_nat (length (n_C cx)) - q) 0) as [Hz|Hz];
                    [reflexivity | clear - Hz Hc0 Hkv; lia])
              UNA PGA Zpc Zrv Zsv Zrom Zfr Zfc ZREGS Z25 Z19 Z16
              ltac:(rewrite Z11, E10, Hc0; reflexivity)
              (ASH 4 (or_introl eq_refl)) (ASH 5 (or_intror eq_refl)) AOL eq_refl eq_refl).
- (* a0 = 16: the whole header is in `ph`; four rd_u32 calls read it *)
  rewrite branch_ne_U, (U_atom E 10 (nx_hk (n_C cx) q) E10 ltac:(clear - Hk16; lia)), U_lit in Hc
    by (clear; lia).
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hfull : 16 <= Z.of_nat (length (n_C cx)) - q)
    by (clear - Hc Hqr; unfold nx_hk, NX_PH_LEN in Hc; lia).
  destruct (hdr_len (n_C cx) q ltac:(clear - Hqr Hp0C; lia) Hfull) as (Hkfull & Hhlen).
  assert (HbC : bytes_ok (n_C cx))
    by (destruct HSRC as (W' & cpos & fl & md' & _ & _ & _ & _ & _ & _ & _ & Hbo & _); exact Hbo).
  assert (HSW2 : n_sw cx = 0 \/ n_sw cx = 1)
    by (pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
        _ & _ & _ & _ & _ & _ & _ & Hswz & _); exact (Hswz Hh0)).
  assert (E2 : ew E 2 = w64 (n_sp1 cx))
    by (rewrite (EW 2%nat (2%bv : bv 5) ltac:(vm_compute; reflexivity)); exact Rsp).
  (* 0x81778..0x81788: the shadow check of ps + 8, a1 := ps->swapped, a0 := ph, `jal rd_u32` *)
  paj_run_shc RUNP RUNC HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR]|].
  pose proof (hb_unch E _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9 U27 U25) as UNc1.
  match goal with | HSx : st_ok _ _ _ (restrict _ ?M) |- _ => set (MS1 := M) in * end.
  assert (UNA1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) ->
    ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8) ->
    ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) ->
    aview SEGS (w_H W3) (ms_mem MS1) a = aview SEGS (w_H W3) (ms_mem ms3) a)
    by (intros a Ha N1 N2 N3; rewrite (UNc1 a Ha N1 N2 N3); exact (UN1 a Ha N1 N2 N3)).
  refine (hb_call cx fp k2 ly3 S3 W3 _ _ _ E _ 40%nat (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x1d4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) 0 (n_sw cx)
            (nth 0 (nx_hdr (n_C cx) q) 0) (nth 1 (nx_hdr (n_C cx) q) 0)
            (nth 2 (nx_hdr (n_C cx) q) 0) (nth 3 (nx_hdr (n_C cx) q) 0)
            HB HJ3 Hfr3 HEI HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(clear; cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(reflexivity)
            _ ltac:(clear; lia) _ HSW2 _ _ _ _ _).
  (* a0 = ph (0x81784), a1 = ps->swapped (0x81780, sign-extended), sp = s1 *)
  + match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
    cbn [sv_denot]. rewrite U19. f_equal.
  + match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
    cbn [sv_denot]. rewrite E32. apply hb_sext_sw. exact HSW2.
  + match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
    cbn [sv_denot]. rewrite E2, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  + (* the four bytes at ph: the header the fread wrote, kept by the run so far *)
    apply (hdr_bytes SEGS _ (nF cx fp + NO_PH) (n_C cx) q 0); [|exact Hhlen | clear; lia
      | reflexivity | reflexivity | reflexivity | reflexivity].
    apply (garr8_frame SEGS _ _ _ _ Hgarr). intros x Hx. rewrite Hhlen in Hx.
    apply (mbyte_of_aview SEGS). apply UNA1;
    [ clear - Hx HF4096 HFceil Hac HNOP; lia
    | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia
    | clear - Hx HdPF HPL HSWO HPSceil HPS4096 HF4096 HNOP; lia
    | clear - Hx HFapp HSHb HSHO HF4096 HFceil Hac HNOP; lia ].
  + (* `ph` is addressable: its shadow bytes are 0 *)
    apply (hb_ph_ra cx fp W3 _ 0 4 HF64 HF4096 ESH); [| | clear; lia | clear; lia | clear; lia].
    * pose proof (hb_chunk_byte_s E _ W3 _ 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
               ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
      cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25 in HX. exact HX.
    * pose proof (hb_chunk_byte_s E _ W3 _ 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
               ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
      cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25 in HX. exact HX.
  + (* the callee writes only below sp1, so every region of the run is kept *)
    intros mem2 md2 HJ2 Hun.
    eapply (hb_kept_call cx fp k2 ly3 S3 W3 E (ms_mem MS1) mem2 md2 _ HB HJ2 Hfr3 U9 U27 U20 U25);
    [vm_compute; reflexivity | exact Hun].
  + (* back from rd_u32 at 0x8178c: a0 = ts_sec; the env is E with the caller-saved registers havocked *)
    clear HS HJ3 HF HFr HG. intros regs2 mem2 md2 HS HJ3 HP2 Ha02 Hun2 Hfds2 Hfs2.
    set (E1 := havoc E 40 (map (getr regs2) CLOB)) in HS.
    assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEI | cbv; lia]).
    assert (V1 : forall n, (n < 40)%nat -> ew E1 n = ew E n) by (intros n Hn; apply ew_havoc_old; exact Hn).
    assert (U9a : bv_unsigned (ew E1 9) = n_sp1 cx) by (rewrite V1 by lia; exact U9).
    assert (U27a : bv_unsigned (ew E1 27) = n_ps cx + PS_SW_OFF) by (rewrite V1 by lia; exact U27).
    assert (U25a : bv_unsigned (ew E1 25) = nSH cx fp) by (rewrite V1 by lia; exact U25).
    assert (U20a : bv_unsigned (ew E1 20) = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF))
      by (rewrite V1 by lia; exact U20).
    assert (U19a : bv_unsigned (ew E1 19) = nF cx fp + NO_PH) by (rewrite V1 by lia; exact U19).
    assert (E2a : ew E1 2 = w64 (n_sp1 cx)) by (rewrite V1 by lia; exact E2).
    assert (E32a : ew E1 32 = w64 (n_sw cx)) by (rewrite V1 by lia; exact E32).
    pose proof (hb_awr cx fp k2 ly3 S3 W3 mem2 md2 E1 HB HJ3 Hfr3 U9a U27a U25a) as HAWR1.
    (* 0x8178c..0x817a8: the UBSan guard `bgeu s3,-4`, the shadow check of ps + 8, a1 := swapped,
       a0 := NS_PH4 = ph + 4, `jal rd_u32` *)
    paj_run_shc RUNP RUNC HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR1]|].
    pose proof (hb_unch E1 _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9a U27a U25a) as UNc2.
    match goal with | HSx : st_ok _ _ _ (restrict _ ?M) |- _ => set (MS2 := M) in * end.
    assert (UNA2 : forall a, 0 <= a < 2 ^ 64 ->
      ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) ->
      ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8) ->
      ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
      aview SEGS (w_H W3) (ms_mem MS2) a = aview SEGS (w_H W3) (ms_mem ms3) a)
      by (intros a Ha N1 N2 N3 N4; rewrite (UNc2 a Ha N1 N2 N3), (Hun2 a Ha N4);
          exact (UNA1 a Ha N1 N2 N3)).
    refine (hb_call cx fp k2 ly3 S3 W3 _ _ _ E1 _ 60%nat (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x1f4) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) 1 (n_sw cx)
              (nth 4 (nx_hdr (n_C cx) q) 0) (nth 5 (nx_hdr (n_C cx) q) 0)
              (nth 6 (nx_hdr (n_C cx) q) 0) (nth 7 (nx_hdr (n_C cx) q) 0)
              HB HJ3 Hfr3 HEI1 HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(clear; cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
              ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(reflexivity)
              _ ltac:(clear; lia) _ HSW2 _ _ _ _ _).
    * match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
      cbn [sv_denot]. rewrite U19a. f_equal.
    * match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
      cbn [sv_denot]. rewrite E32a. apply hb_sext_sw. exact HSW2.
    * match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
      cbn [sv_denot]. rewrite E2a, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    * apply (hdr_bytes SEGS _ (nF cx fp + NO_PH) (n_C cx) q 1); [|exact Hhlen | clear; lia
        | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (garr8_frame SEGS _ _ _ _ Hgarr). intros x Hx. rewrite Hhlen in Hx.
      apply (mbyte_of_aview SEGS). apply UNA2;
      [ clear - Hx HF4096 HFceil Hac HNOP; lia
      | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia
      | clear - Hx HdPF HPL HSWO HPSceil HPS4096 HF4096 HNOP; lia
      | clear - Hx HFapp HSHb HSHO HF4096 HFceil Hac HNOP; lia
      | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia ].
    * apply (hb_ph_ra cx fp W3 _ 4 4 HF64 HF4096 ESH); [| | clear; lia | clear; lia | clear; lia].
      -- pose proof (hb_chunk_byte_s E1 _ W3 _ 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
               ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
         cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25a in HX. exact HX.
      -- pose proof (hb_chunk_byte_s E1 _ W3 _ 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
               ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
         cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25a in HX. exact HX.
    * intros mem3' md3' HJ2 Hun.
      eapply (hb_kept_call cx fp k2 ly3 S3 W3 E1 (ms_mem MS2) mem3' md3' _ HB HJ2 Hfr3
                U9a U27a U20a U25a); [vm_compute; reflexivity | exact Hun].
    * (* back from rd_u32 at 0x817ac: a0 = ts_usec, kept in s8 *)
      clear HS HJ3 HF HFr HG. intros regs3 mem3 md3b HS HJ3 HP3 Ha03 Hun3 Hfds3 Hfs3.
      set (E2' := havoc E1 60 (map (getr regs3) CLOB)) in HS.
      assert (HEI2 : img_env VAL A_LIM E2') by (apply img_env_havoc; [exact HEI1 | cbv; lia]).
      assert (V2 : forall n, (n < 40)%nat -> ew E2' n = ew E n)
        by (intros n Hn; unfold E2'; rewrite ew_havoc_old by lia; apply V1; exact Hn).
      assert (U9b : bv_unsigned (ew E2' 9) = n_sp1 cx) by (rewrite V2 by lia; exact U9).
      assert (U27b : bv_unsigned (ew E2' 27) = n_ps cx + PS_SW_OFF) by (rewrite V2 by lia; exact U27).
      assert (U25b : bv_unsigned (ew E2' 25) = nSH cx fp) by (rewrite V2 by lia; exact U25).
      assert (U20b : bv_unsigned (ew E2' 20) = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF))
        by (rewrite V2 by lia; exact U20).
      assert (U19b : bv_unsigned (ew E2' 19) = nF cx fp + NO_PH) by (rewrite V2 by lia; exact U19).
      assert (E2b : ew E2' 2 = w64 (n_sp1 cx)) by (rewrite V2 by lia; exact E2).
      assert (E32b : ew E2' 32 = w64 (n_sw cx)) by (rewrite V2 by lia; exact E32).
      pose proof (hb_awr cx fp k2 ly3 S3 W3 mem3 md3b E2' HB HJ3 Hfr3 U9b U27b U25b) as HAWR2.
      (* 0x817ac..0x817c8: the guard `bltu -9,s3`, the shadow check, a0 := NS_PH8 = ph + 8, `jal` *)
      paj_run_shc RUNP RUNC HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR2]|].
      pose proof (hb_unch E2' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9b U27b U25b) as UNc3.
      match goal with | HSx : st_ok _ _ _ (restrict _ ?M) |- _ => set (MS3 := M) in * end.
      assert (UNA3 : forall a, 0 <= a < 2 ^ 64 ->
        ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) ->
        ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8) ->
        ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
        aview SEGS (w_H W3) (ms_mem MS3) a = aview SEGS (w_H W3) (ms_mem ms3) a)
        by (intros a Ha N1 N2 N3 N4; rewrite (UNc3 a Ha N1 N2 N3), (Hun3 a Ha N4);
            exact (UNA2 a Ha N1 N2 N3 N4)).
      refine (hb_call cx fp k2 ly3 S3 W3 _ _ _ E2' _ 80%nat (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x214) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) 2 (n_sw cx)
                (nth 8 (nx_hdr (n_C cx) q) 0) (nth 9 (nx_hdr (n_C cx) q) 0)
                (nth 10 (nx_hdr (n_C cx) q) 0) (nth 11 (nx_hdr (n_C cx) q) 0)
                HB HJ3 Hfr3 HEI2 HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(clear; cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(reflexivity)
                _ ltac:(clear; lia) _ HSW2 _ _ _ _ _).
      -- match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
         cbn [sv_denot]. rewrite U19b. f_equal.
      -- match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
         cbn [sv_denot]. rewrite E32b. apply hb_sext_sw. exact HSW2.
      -- match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
         cbn [sv_denot]. rewrite E2b, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      -- apply (hdr_bytes SEGS _ (nF cx fp + NO_PH) (n_C cx) q 2); [|exact Hhlen | clear; lia
           | reflexivity | reflexivity | reflexivity | reflexivity].
         apply (garr8_frame SEGS _ _ _ _ Hgarr). intros x Hx. rewrite Hhlen in Hx.
         apply (mbyte_of_aview SEGS). apply UNA3;
         [ clear - Hx HF4096 HFceil Hac HNOP; lia
         | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia
         | clear - Hx HdPF HPL HSWO HPSceil HPS4096 HF4096 HNOP; lia
         | clear - Hx HFapp HSHb HSHO HF4096 HFceil Hac HNOP; lia
         | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia ].
      -- apply (hb_ph_ra cx fp W3 _ 8 4 HF64 HF4096 ESH); [| | clear; lia | clear; lia | clear; lia].
         ++ pose proof (hb_chunk_byte_s E2' _ W3 _ 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
                  ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
            cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25b in HX. exact HX.
         ++ pose proof (hb_chunk_byte_s E2' _ W3 _ 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
                  ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
            cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25b in HX. exact HX.
      -- intros mem4 md4 HJ2 Hun.
         eapply (hb_kept_call cx fp k2 ly3 S3 W3 E2' (ms_mem MS3) mem4 md4 _ HB HJ2 Hfr3
                   U9b U27b U20b U25b); [vm_compute; reflexivity | exact Hun].
      -- (* back from rd_u32 at 0x817cc: a0 = incl *)
         clear HS HJ3 HF HFr HG. intros regs4 mem4 md4 HS HJ3 HP4 Ha04 Hun4 Hfds4 Hfs4.
         set (E3' := havoc E2' 80 (map (getr regs4) CLOB)) in HS.
         assert (HEI3 : img_env VAL A_LIM E3') by (apply img_env_havoc; [exact HEI2 | cbv; lia]).
         assert (V3 : forall n, (n < 40)%nat -> ew E3' n = ew E n)
           by (intros n Hn; unfold E3'; rewrite ew_havoc_old by lia; apply V2; exact Hn).
         assert (U9c : bv_unsigned (ew E3' 9) = n_sp1 cx) by (rewrite V3 by lia; exact U9).
         assert (U27c : bv_unsigned (ew E3' 27) = n_ps cx + PS_SW_OFF) by (rewrite V3 by lia; exact U27).
         assert (U25c : bv_unsigned (ew E3' 25) = nSH cx fp) by (rewrite V3 by lia; exact U25).
         pose proof (hb_awr cx fp k2 ly3 S3 W3 mem4 md4 E3' HB HJ3 Hfr3 U9c U27c U25c) as HAWR3.
         (* 0x817cc `beqz a0`: an empty record (incl = 0) goes to NP_empty *)
         psrr_branch_pi RUNP BR HS.
         ++ (* incl = 0: 0x81858..0x81864, shadow bytes 4, 5 := 0xf8, `j` NP_loop (KEmpty) *)
            paj_run_to_sh RUNTOP HS HJ3 NP_loop;
              [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR3] |].
            pose proof (hb_unch E3' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9c U27c U25c) as UNc5.
            match goal with | HSx : st_ok_pi _ _ _ _ (restrict _ ?M) |- _ => set (MSX := M) in * end.
            destruct (hb_state_of E3' _ W3 _ HS eq_refl) as (Zpc & Zrv & Zsv & Zrom & Zfr & Zfc).
            cbn [ss_pc] in Zpc.
            prreg HS (2%bv : bv 5) Z2; prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9;
            prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4; prreg HS (25%bv : bv 5) Z25;
            prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23; prreg HS (26%bv : bv 5) Z26;
            prreg HS (27%bv : bv 5) Z27; prreg HS (19%bv : bv 5) Z19; prreg HS (20%bv : bv 5) Z20.
            assert (KR : forall n (r : bv 5), (n < 40)%nat -> Z.of_nat n = bv_unsigned r ->
                      ew E3' n = getr (ms_regs ms3) r)
              by (intros n r Hn Hr; rewrite V3 by exact Hn; apply EW; exact Hr).
            (* incl = 0: 0x817cc `beqz a0` taken *)
            assert (Hq0 : 0 <= q) by (clear - Hqr Hp0C; lia).
            destruct (hb_word_of_call _ (n_sw cx) (n_C cx) q 2 HSW2 Hq0 Hfull ltac:(lia) HbC Ha04)
              as (Wincl & _).
            change (4 * 2) with 8 in Wincl.
            assert (A84 : ew E3' 84 = getr regs4 10)
              by (unfold E3'; change 84%nat with (80 + 4)%nat; apply hb_havoc_a0).
            match goal with H : branch_taken BC_EQ _ _ = true |- _ => rename H into Hbz end.
            rewrite branch_eq_U, U_lit, hb_U_atom0, A84 in Hbz by (clear; lia).
            apply Z.eqb_eq in Hbz.
            assert (HI0 : PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q = 0)
              by (unfold PSN.incl; rewrite <- Wincl, Hbz; reflexivity).
            apply (HLOOP cx fp k2 ly3 S3 W3 _ _ HB HJ3 Hfr3).
            eapply (hb_loop_at B MT KS LAWS ASIL R cx fp k2 ly3 S3 W3 ms3 _ md3 _ q lh
                      HB HJE HJ3 Hfr3 HMID Hnext Hchain).
            ** exact (proj1 Hqr).
            ** clear - Hfull. lia.
            ** intros a Ha N1 N2 N3 N4.
               assert (N2' : ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8))
                 by (clear - N2 HSWO HOLO; lia).
               etransitivity; [exact (UNc5 a Ha N1 N2' N3)|].
               etransitivity; [exact (Hun4 a Ha N4)|]. exact (UNA3 a Ha N1 N2' N3 N4).
            ** exact Zrv.
            ** exact Zsv.
            ** exact Zrom.
            ** exact Zfr.
            ** exact Zfc.
            ** split; [rewrite Z2, (KR 2%nat (2%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                         exact Rsp|].
               split; [rewrite Z8, (KR 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                         exact Rs0|].
               split; [rewrite Z9, (KR 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                         exact Rs1|].
               split; [rewrite Z3, (KR 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                         exact Rgp|].
               rewrite Z4, (KR 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact Rtp.
            ** rewrite Z25, (KR 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R25.
            ** rewrite Z21, (KR 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R21.
            ** rewrite Z23, (KR 23%nat (23%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R23.
            ** rewrite Z26, (KR 26%nat (26%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R26.
            ** rewrite Z27, (KR 27%nat (27%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R27.
            ** rewrite Z19, (KR 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R19.
            ** rewrite Z20, (KR 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R20.
            ** rewrite !hb_fds_wvb, Hfds4, !hb_fds_wvb, Hfds3, !hb_fds_wvb, Hfds2, !hb_fds_wvb. reflexivity.
            ** rewrite !hb_fs_wvb, Hfs4, !hb_fs_wvb, Hfs3, !hb_fs_wvb, Hfs2, !hb_fs_wvb. reflexivity.
            ** exact HI0.
            ** exact Zpc.
            ** (* the shadow bytes of `ph` := 0xf8 (0x81858, 0x8185c): `ph` goes out of scope *)
               match type of HS with st_ok_pi _ _ _ ?ss _ =>
                 let r := eval vm_compute in (nth_error (ss_mem ss) 3%nat) in
                 match r with Some ?RG =>
                   pose proof (hb_chunk_byte_w E3' ss W3 MSX 3%nat RG
                     (YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608))) 18446744073709551608 HS
                     ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX
                 end end.
               cbn [YP09.r_base YP09.c_off base_val] in HX. rewrite U25c in HX.
               rewrite HX. vm_compute. reflexivity.
            ** match type of HS with st_ok_pi _ _ _ ?ss _ =>
                 let r := eval vm_compute in (nth_error (ss_mem ss) 3%nat) in
                 match r with Some ?RG =>
                   pose proof (hb_chunk_byte_w E3' ss W3 MSX 3%nat RG
                     (YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608))) 18446744073709551608 HS
                     ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX
                 end end.
               cbn [YP09.r_base YP09.c_off base_val] in HX. rewrite U25c in HX.
               rewrite HX. vm_compute. reflexivity.
            ** (* ps->orig: untouched on this path, the turn's value *)
               match type of HS with st_ok_pi _ _ _ ?ss _ =>
                 let r := eval vm_compute in (nth_error (ss_mem ss) 1%nat) in
                 match r with Some ?RG =>
                   pose proof (hb_chunk_val E3' ss W3 MSX 1%nat RG (YP09.mkChunk 4 (CVal 4 (SOff 33 0))) 4
                     (SOff 33 0) (nx_ol cx lh) HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl
                     ltac:(cbn [sv_denot]; rewrite (V3 33%nat ltac:(lia)), E33, Z.add_0_r; unfold w64;
                           rewrite Z_to_bv_bv_unsigned; reflexivity)
                     ltac:(cbn; clear - HOL; lia) ltac:(cbn; lia)) as HX
                 end end.
               cbn [YP09.r_base YP09.c_off base_val N.to_nat] in HX. rewrite U27c in HX.
               replace (n_ps cx + PS_SW_OFF + 4) with (n_ps cx + PS_OL_OFF) in HX
                 by (clear - HSWO HOLO; lia).
               exact HX.
         ++ (* incl <> 0: 0x817d0..0x817f0, s6 := incl, NS_SEC := ts_sec, the guard `bltu -13,s3`,
               a0 := NS_PH12 = ph + 12, `jal rd_u32` (orig) *)
            assert (U20c : bv_unsigned (ew E3' 20) = shadow_of_addr SHADOW_OFF (n_ps cx + PS_SW_OFF))
              by (rewrite V3 by lia; exact U20).
            assert (U19c : bv_unsigned (ew E3' 19) = nF cx fp + NO_PH) by (rewrite V3 by lia; exact U19).
            assert (E2c : ew E3' 2 = w64 (n_sp1 cx)) by (rewrite V3 by lia; exact E2).
            assert (E32c : ew E3' 32 = w64 (n_sw cx)) by (rewrite V3 by lia; exact E32).
            paj_run_shc RUNP RUNC HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR3]|].
            pose proof (hb_unch E3' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9c U27c U25c) as UNc4.
            match goal with | HSx : st_ok _ _ _ (restrict _ ?M) |- _ => set (MS4 := M) in * end.
            assert (UNA4 : forall a, 0 <= a < 2 ^ 64 ->
              ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) ->
              ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8) ->
              ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
              aview SEGS (w_H W3) (ms_mem MS4) a = aview SEGS (w_H W3) (ms_mem ms3) a)
              by (intros a Ha N1 N2 N3 N4; rewrite (UNc4 a Ha N1 N2 N3), (Hun4 a Ha N4);
                  exact (UNA3 a Ha N1 N2 N3 N4)).
            refine (hb_call cx fp k2 ly3 S3 W3 _ _ _ E3' _ 100%nat (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x23c) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) 3 (n_sw cx)
                      (nth 12 (nx_hdr (n_C cx) q) 0) (nth 13 (nx_hdr (n_C cx) q) 0)
                      (nth 14 (nx_hdr (n_C cx) q) 0) (nth 15 (nx_hdr (n_C cx) q) 0)
                      HB HJ3 Hfr3 HEI3 HS ltac:(reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(clear; cbv; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                      ltac:(vm_compute; reflexivity) ltac:(clear; lia) ltac:(reflexivity)
                      _ ltac:(clear; lia) _ HSW2 _ _ _ _ _).
            ** match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
               cbn [sv_denot]. rewrite U19c. f_equal.
            ** match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
               cbn [sv_denot]. rewrite E32c. apply hb_sext_sw. exact HSW2.
            ** match goal with |- sv_denot _ ?t = _ => let e := eval vm_compute in t in change t with e end.
               cbn [sv_denot]. rewrite E2c, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
            ** apply (hdr_bytes SEGS _ (nF cx fp + NO_PH) (n_C cx) q 3); [|exact Hhlen | clear; lia
                 | reflexivity | reflexivity | reflexivity | reflexivity].
               apply (garr8_frame SEGS _ _ _ _ Hgarr). intros x Hx. rewrite Hhlen in Hx.
               apply (mbyte_of_aview SEGS). apply UNA4;
               [ clear - Hx HF4096 HFceil Hac HNOP; lia
               | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia
               | clear - Hx HdPF HPL HSWO HPSceil HPS4096 HF4096 HNOP; lia
               | clear - Hx HFapp HSHb HSHO HF4096 HFceil Hac HNOP; lia
               | clear - Hx HFceil Hac Hsplo Hsp1b HNSB HNOP; lia ].
            ** apply (hb_ph_ra cx fp W3 _ 12 4 HF64 HF4096 ESH); [| | clear; lia | clear; lia | clear; lia].
               --- pose proof (hb_chunk_byte_s E3' _ W3 _ 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0
                      HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia))
                      as HX.
                   cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25c in HX. exact HX.
               --- pose proof (hb_chunk_byte_s E3' _ W3 _ 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0
                      HS ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia))
                      as HX.
                   cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25c in HX. exact HX.
            ** intros mem5 md5 HJ2 Hun.
               eapply (hb_kept_call cx fp k2 ly3 S3 W3 E3' (ms_mem MS4) mem5 md5 _ HB HJ2 Hfr3
                         U9c U27c U20c U25c); [vm_compute; reflexivity | exact Hun].
            ** (* back from rd_u32 at 0x817f4: a0 = orig; the shadow check of ps + 12, s2 := incl,
                  ps->orig := orig (0x8180c), then `bgeu s7,s2` 0x81810 *)
               clear HS HJ3 HF HFr HG. intros regs5 mem5 md5 HS HJ3 HP5 Ha05 Hun5 Hfds5 Hfs5.
               set (E4' := havoc E3' 100 (map (getr regs5) CLOB)) in HS.
               assert (HEI4 : img_env VAL A_LIM E4') by (apply img_env_havoc; [exact HEI3 | cbv; lia]).
               assert (V4 : forall n, (n < 40)%nat -> ew E4' n = ew E n)
                 by (intros n Hn; unfold E4'; rewrite ew_havoc_old by lia; apply V3; exact Hn).
               assert (U9d : bv_unsigned (ew E4' 9) = n_sp1 cx) by (rewrite V4 by lia; exact U9).
               assert (U27d : bv_unsigned (ew E4' 27) = n_ps cx + PS_SW_OFF)
                 by (rewrite V4 by lia; exact U27).
               assert (U25d : bv_unsigned (ew E4' 25) = nSH cx fp) by (rewrite V4 by lia; exact U25).
               pose proof (hb_awr cx fp k2 ly3 S3 W3 mem5 md5 E4' HB HJ3 Hfr3 U9d U27d U25d) as HAWR4.
               paj_run_sh RUNP HS HJ3; [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR4]|].
               pose proof (hb_unch E4' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9d U27d U25d) as UNc5.
               clear HF HFr HG.
               (* the four words: the atoms 44, 64, 84, 104 are the four calls' a0 *)
               assert (A44 : ew E4' 44 = getr regs2 10)
                 by (unfold E4', E3', E2', E1; do 3 rewrite ew_havoc_old by lia;
                     change 44%nat with (40 + 4)%nat; apply hb_havoc_a0).
               assert (A64 : ew E4' 64 = getr regs3 10)
                 by (unfold E4', E3', E2'; do 2 rewrite ew_havoc_old by lia;
                     change 64%nat with (60 + 4)%nat; apply hb_havoc_a0).
               assert (A84 : ew E4' 84 = getr regs4 10)
                 by (unfold E4', E3'; rewrite ew_havoc_old by lia;
                     change 84%nat with (80 + 4)%nat; apply hb_havoc_a0).
               assert (A104 : ew E4' 104 = getr regs5 10)
                 by (unfold E4'; change 104%nat with (100 + 4)%nat; apply hb_havoc_a0).
               assert (Hq0 : 0 <= q) by (clear - Hqr Hp0C; lia).
               destruct (hb_word_of_call _ (n_sw cx) (n_C cx) q 0 HSW2 Hq0 Hfull ltac:(lia) HbC Ha02)
                 as (Wsec & _).
               destruct (hb_word_of_call _ (n_sw cx) (n_C cx) q 1 HSW2 Hq0 Hfull ltac:(lia) HbC Ha03)
                 as (Wusec & _).
               destruct (hb_word_of_call _ (n_sw cx) (n_C cx) q 2 HSW2 Hq0 Hfull ltac:(lia) HbC Ha04)
                 as (Wincl & Wincl2).
               destruct (hb_word_of_call _ (n_sw cx) (n_C cx) q 3 HSW2 Hq0 Hfull ltac:(lia) HbC Ha05)
                 as (Worig & _).
               change (4 * 0) with 0 in Wsec. change (4 * 1) with 4 in Wusec.
               change (4 * 2) with 8 in Wincl, Wincl2. change (4 * 3) with 12 in Worig.
               (* every caller-saved register below atom 40 is still the entry's *)
               assert (KR : forall n (r : bv 5), (n < 40)%nat -> Z.of_nat n = bv_unsigned r ->
                         ew E4' n = getr (ms_regs ms3) r)
                 by (intros n r Hn Hr; rewrite V4 by exact Hn; apply EW; exact Hr).
               (* the unchanged-memory fact of the landings, from the entry to the branch *)
               assert (UNB : forall a, 0 <= a < 2 ^ 64 ->
                 ~ (n_sp1 cx + 56 <= a < n_sp1 cx + 64) ->
                 ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8) ->
                 ~ (nSH cx fp + 4 <= a < nSH cx fp + 6) -> ~ (n_sp1 cx - 16 <= a < n_sp1 cx) ->
                 aview SEGS (w_H W3) mem5 a = aview SEGS (w_H W3) (ms_mem ms3) a)
                 by (intros a Ha N1 N2 N3 N4; rewrite (Hun5 a Ha N4); exact (UNA4 a Ha N1 N2 N3 N4)).
               psrr_branch_pi RUNP BR HS.
               --- (* cap >= incl: 0x81810 `bgeu s7,s2` taken, NP_fit (0x81988) *)
                   paj_run_to_sh RUNTOP HS HJ3 NP_fit;
                     [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR4] |].
                   pose proof (hb_unch E4' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9d U27d U25d)
                     as UNc6.
                   match goal with | HSx : st_ok_pi _ _ _ _ (restrict _ ?M) |- _ => set (MSX := M) in * end.
                   destruct (hb_state_of E4' _ W3 _ HS eq_refl) as (Zpc & Zrv & Zsv & Zrom & Zfr & Zfc).
                   cbn [ss_pc] in Zpc.
                   prreg HS (2%bv : bv 5) Z2; prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9;
                   prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4; prreg HS (25%bv : bv 5) Z25;
                   prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23; prreg HS (26%bv : bv 5) Z26;
                   prreg HS (27%bv : bv 5) Z27; prreg HS (19%bv : bv 5) Z19; prreg HS (20%bv : bv 5) Z20;
                   prreg HS (18%bv : bv 5) Z18; prreg HS (22%bv : bv 5) Z22; prreg HS (24%bv : bv 5) Z24.
                   (* 0 < incl (0x817cc `beqz a0` not taken) and incl <= cap (0x81810 `bgeu s7,s2` taken) *)
                   match goal with H : branch_taken BC_EQ _ _ = false |- _ => rename H into Hbz end.
                   match goal with H : branch_taken BC_GEU _ _ = true |- _ => rename H into Hge end.
                   assert (A84' : ew E3' 84 = getr regs4 10)
                     by (unfold E3'; change 84%nat with (80 + 4)%nat; apply hb_havoc_a0).
                   rewrite branch_eq_U, U_lit, hb_U_atom0, A84', Wincl2 in Hbz by (clear; lia).
                   rewrite branch_geu_U, hb_U_zext, hb_U_atom0, A84, Wincl in Hge.
                   rewrite (KR 23%nat (23%bv : bv 5) ltac:(clear; lia) ltac:(vm_compute; reflexivity)), R23
                     in Hge.
                   rewrite unsigned_lit_small in Hge by (clear - Hcap; unfold NX_CAP_MAX in Hcap; lia).
                   apply negb_true_iff, Z.ltb_ge in Hge. apply Z.eqb_neq in Hbz.
                   assert (HINC : 0 < PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= n_cap cx).
                   { unfold PSN.incl. pose proof (nx_hw_range (n_sw cx =? 1) (nxF (n_C cx)) q 8) as Hr.
                     split; [|exact Hge].
                     destruct (Z.eq_dec (PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 8) 0) as [H0|H0];
                       [exfalso; apply Hbz; rewrite H0; reflexivity | clear - Hr H0; lia]. }
                   apply (HFIT cx fp k2 ly3 S3 W3 _ _ HB HJ3 Hfr3).
                   eapply (hb_fit_at B MT KS LAWS ASIL R cx fp k2 ly3 S3 W3 ms3 _ md3 _ q lh
                             HB HJE HJ3 Hfr3 HMID Hnext Hchain).
                   +++ exact (proj1 Hqr).
                   +++ clear - Hfull. lia.
                   +++ intros a Ha N1 N2 N3 N4.
                       assert (N2' : ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8))
                         by (clear - N2 HSWO HOLO; lia).
                       rewrite (UNc6 a Ha N1 N2' N3), (UNc5 a Ha N1 N2' N3). exact (UNB a Ha N1 N2' N3 N4).
                   +++ exact Zrv.
                   +++ exact Zsv.
                   +++ exact Zrom.
                   +++ exact Zfr.
                   +++ exact Zfc.
                   +++ split; [rewrite Z2, (KR 2%nat (2%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rsp|].
                       split; [rewrite Z8, (KR 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rs0|].
                       split; [rewrite Z9, (KR 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rs1|].
                       split; [rewrite Z3, (KR 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rgp|].
                       rewrite Z4, (KR 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact Rtp.
                   +++ rewrite Z25, (KR 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R25.
                   +++ rewrite Z21, (KR 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R21.
                   +++ rewrite Z23, (KR 23%nat (23%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R23.
                   +++ rewrite Z26, (KR 26%nat (26%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R26.
                   +++ rewrite Z27, (KR 27%nat (27%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R27.
                   +++ rewrite Z19, (KR 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R19.
                   +++ rewrite Z20, (KR 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R20.
                   +++ (* the descriptors: the runs only materialize the vm backing, rd_u32 keeps them *)
                       rewrite !hb_fds_wvb, Hfds5, !hb_fds_wvb, Hfds4, !hb_fds_wvb, Hfds3, !hb_fds_wvb, Hfds2,
                         !hb_fds_wvb. reflexivity.
                   +++ rewrite !hb_fs_wvb, Hfs5, !hb_fs_wvb, Hfs4, !hb_fs_wvb, Hfs3, !hb_fs_wvb, Hfs2,
                         !hb_fs_wvb. reflexivity.
                   +++ exact HINC.
                   +++ exact Zpc.
                   +++ rewrite Z18, hb_zext32, A84, Wincl. reflexivity.
                   +++ rewrite Z22, A84, Wincl2, hb_swrap_small; [reflexivity|].
                       unfold PSN.incl in HINC. clear - HINC Hcap. unfold NX_CAP_MAX in Hcap. lia.
                   +++ rewrite Z24, A64. exact Wusec.
                   +++ (* NS_SEC holds ts_sec, the first call's a0 (0x817e4) *)
                       exists (bv_unsigned (ew E4' 44)). split; [|rewrite A44; exact Wsec].
                       pose proof (bv_unsigned_in_range 64 (ew E4' 44)) as Hr44.
                       change (bv_modulus 64) with (2 ^ 64) in Hr44.
                       match type of HS with st_ok_pi _ _ _ ?ss _ =>
                         let r := eval vm_compute in (nth_error (ss_mem ss) 0%nat) in
                         match r with Some ?RG =>
                           pose proof (hb_chunk_val E4' ss W3 MSX 0%nat RG (YP09.mkChunk 56 (CVal 8 (SOff 44 0))) 8
                             (SOff 44 0) (bv_unsigned (ew E4' 44)) HS ltac:(vm_compute; reflexivity)
                             ltac:(cbn; tauto) eq_refl eq_refl
                             ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity) Hr44 ltac:(cbn; lia)) as HX
                         end end.
                       cbn [YP09.r_base YP09.c_off base_val N.to_nat] in HX. rewrite U9d in HX.
                       unfold nslot, NS_SEC. exact (rdword_of_val_mem SEGS _ _ _ _ HX Hr44).
                   +++ pose proof (hb_chunk_byte E4' _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
                         ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
                       cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25d in HX. exact HX.
                   +++ pose proof (hb_chunk_byte E4' _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
                         ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
                       cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25d in HX. exact HX.
                   +++ (* ps->orig := the fourth call's a0 (0x8180c) *)
                       pose proof (orig_range (n_sw cx =? 1) (nxF (n_C cx)) q) as Hro.
                       match type of HS with st_ok_pi _ _ _ ?ss _ =>
                         let r := eval vm_compute in (nth_error (ss_mem ss) 1%nat) in
                         match r with Some ?RG =>
                           pose proof (hb_chunk_val32 E4' ss W3 MSX 1%nat RG (YP09.mkChunk 4 (CVal 4 (SOff 104 0)))
                             (SOff 104 0) (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) HS
                             ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl
                             ltac:(change (bv_unsigned (sv_denot E4' (SOff 104 0))) with (U E4' (SOff 104 0));
                                   rewrite hb_U_atom0, A104; exact Worig) Hro) as HX
                         end end.
                       cbn [YP09.r_base YP09.c_off base_val] in HX. rewrite U27d in HX.
                       replace (n_ps cx + PS_SW_OFF + 4) with (n_ps cx + PS_OL_OFF) in HX
                         by (clear - HSWO HOLO; lia).
                       exact HX.
               --- (* cap < incl: the fall-through NP_sk1 (0x81814) *)
                   paj_run_to_sh RUNTOP HS HJ3 NP_sk1;
                     [eapply hb_awr_sk; [vm_compute; reflexivity | exact HAWR4] |].
                   pose proof (hb_unch E4' _ W3 _ _ _ _ _ HFr ltac:(vm_compute; reflexivity) U9d U27d U25d)
                     as UNc6.
                   match goal with | HSx : st_ok_pi _ _ _ _ (restrict _ ?M) |- _ => set (MSX := M) in * end.
                   destruct (hb_state_of E4' _ W3 _ HS eq_refl) as (Zpc & Zrv & Zsv & Zrom & Zfr & Zfc).
                   cbn [ss_pc] in Zpc.
                   prreg HS (2%bv : bv 5) Z2; prreg HS (8%bv : bv 5) Z8; prreg HS (9%bv : bv 5) Z9;
                   prreg HS (3%bv : bv 5) Z3; prreg HS (4%bv : bv 5) Z4; prreg HS (25%bv : bv 5) Z25;
                   prreg HS (21%bv : bv 5) Z21; prreg HS (23%bv : bv 5) Z23; prreg HS (26%bv : bv 5) Z26;
                   prreg HS (27%bv : bv 5) Z27; prreg HS (19%bv : bv 5) Z19; prreg HS (20%bv : bv 5) Z20;
                   prreg HS (22%bv : bv 5) Z22.
                   (* incl <> 0 (0x817cc `beqz a0` not taken) and cap < incl (0x81810 `bgeu s7,s2` not taken) *)
                   match goal with H : branch_taken BC_EQ _ _ = false |- _ => rename H into Hbz end.
                   match goal with H : branch_taken BC_GEU _ _ = false |- _ => rename H into Hlt end.
                   assert (A84' : ew E3' 84 = getr regs4 10)
                     by (unfold E3'; change 84%nat with (80 + 4)%nat; apply hb_havoc_a0).
                   rewrite branch_eq_U, U_lit, hb_U_atom0, A84', Wincl2 in Hbz by (clear; lia).
                   rewrite branch_geu_U, hb_U_zext, hb_U_atom0, A84, Wincl in Hlt.
                   rewrite (KR 23%nat (23%bv : bv 5) ltac:(clear; lia) ltac:(vm_compute; reflexivity)), R23
                     in Hlt.
                   rewrite unsigned_lit_small in Hlt by (clear - Hcap; unfold NX_CAP_MAX in Hcap; lia).
                   apply negb_false_iff, Z.ltb_lt in Hlt. apply Z.eqb_neq in Hbz.
                   assert (HNZ : nx_incl cx q <> 0).
                   { unfold nx_incl, PSN.incl. intros H0. apply Hbz. rewrite H0. reflexivity. }
                   apply (HSK cx fp k2 ly3 S3 W3 _ _ HB HJ3 Hfr3).
                   eapply (hb_sk1_at B MT KS LAWS ASIL R cx fp k2 ly3 S3 W3 ms3 _ md3 _ q lh
                             HB HJE HJ3 Hfr3 HMID Hnext Hchain).
                   +++ exact (proj1 Hqr).
                   +++ clear - Hfull. lia.
                   +++ intros a Ha N1 N2 N3 N4.
                       assert (N2' : ~ (n_ps cx + PS_SW_OFF + 4 <= a < n_ps cx + PS_SW_OFF + 8))
                         by (clear - N2 HSWO HOLO; lia).
                       rewrite (UNc6 a Ha N1 N2' N3), (UNc5 a Ha N1 N2' N3). exact (UNB a Ha N1 N2' N3 N4).
                   +++ exact Zrv.
                   +++ exact Zsv.
                   +++ exact Zrom.
                   +++ exact Zfr.
                   +++ exact Zfc.
                   +++ split; [rewrite Z2, (KR 2%nat (2%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rsp|].
                       split; [rewrite Z8, (KR 8%nat (8%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rs0|].
                       split; [rewrite Z9, (KR 9%nat (9%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rs1|].
                       split; [rewrite Z3, (KR 3%nat (3%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity));
                                exact Rgp|].
                       rewrite Z4, (KR 4%nat (4%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact Rtp.
                   +++ rewrite Z25, (KR 25%nat (25%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R25.
                   +++ rewrite Z21, (KR 21%nat (21%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R21.
                   +++ rewrite Z23, (KR 23%nat (23%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R23.
                   +++ rewrite Z26, (KR 26%nat (26%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R26.
                   +++ rewrite Z27, (KR 27%nat (27%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R27.
                   +++ rewrite Z19, (KR 19%nat (19%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R19.
                   +++ rewrite Z20, (KR 20%nat (20%bv : bv 5) ltac:(lia) ltac:(vm_compute; reflexivity)). exact R20.
                   +++ rewrite !hb_fds_wvb, Hfds5, !hb_fds_wvb, Hfds4, !hb_fds_wvb, Hfds3, !hb_fds_wvb, Hfds2,
                         !hb_fds_wvb. reflexivity.
                   +++ rewrite !hb_fs_wvb, Hfs5, !hb_fs_wvb, Hfs4, !hb_fs_wvb, Hfs3, !hb_fs_wvb, Hfs2,
                         !hb_fs_wvb. reflexivity.
                   +++ exact HNZ.
                   +++ unfold nx_incl, PSN.incl. exact Hlt.
                   +++ exact Zpc.
                   +++ rewrite Z22, A84. exact Wincl.
                   +++ pose proof (hb_chunk_byte E4' _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 4 (CVal 1 (SLit 0))) 0 HS
                         ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
                       cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25d in HX. exact HX.
                   +++ pose proof (hb_chunk_byte E4' _ W3 MSX 3%nat hb_fsh (YP09.mkChunk 5 (CVal 1 (SLit 0))) 0 HS
                         ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl ltac:(clear; lia)) as HX.
                       cbn [YP09.r_base YP09.c_off hb_fsh base_val] in HX. rewrite U25d in HX. exact HX.
                   +++ pose proof (orig_range (n_sw cx =? 1) (nxF (n_C cx)) q) as Hro.
                       match type of HS with st_ok_pi _ _ _ ?ss _ =>
                         let r := eval vm_compute in (nth_error (ss_mem ss) 1%nat) in
                         match r with Some ?RG =>
                           pose proof (hb_chunk_val32 E4' ss W3 MSX 1%nat RG (YP09.mkChunk 4 (CVal 4 (SOff 104 0)))
                             (SOff 104 0) (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) HS
                             ltac:(vm_compute; reflexivity) ltac:(cbn; tauto) eq_refl eq_refl
                             ltac:(change (bv_unsigned (sv_denot E4' (SOff 104 0))) with (U E4' (SOff 104 0));
                                   rewrite hb_U_atom0, A104; exact Worig) Hro) as HX
                         end end.
                       cbn [YP09.r_base YP09.c_off base_val] in HX. rewrite U27d in HX.
                       replace (n_ps cx + PS_SW_OFF + 4) with (n_ps cx + PS_OL_OFF) in HX
                         by (clear - HSWO HOLO; lia).
                       exact HX.
Qed.

End c.
End b.
End a.

(* SK is explicit at every use, as in lib/B/Prog/PcapSourceNextDefs.v's nx_from / nx_post. *)
Arguments nx_hdrb_ph {fx rc} SK {PI}.

(* GUARD: SK is passed by position and fx rc PI by name; were SK implicit again, SK would be
   taken as B and this line would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing)
  (B : asyms) (MT : ameter_ops) (KS : asource_syms) =>
  nx_hdrb_ph (fx := fx) (rc := rc) SK (PI := PI) B MT KS).
