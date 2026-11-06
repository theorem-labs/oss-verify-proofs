(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of rec_clear on fuzz_command.asan-ubsan (image B): the B re-walk of
   lib/A/Prog/rec_clear.v (a working branch 9dd2d0c2ea2), in the shape of
   proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v .. ACh1.v (cgif_close): the seed of a symbolic state over the
   listing, paj_run_tok steps, cl_callS for the program callee and the 04 rules for the runtime entries. B's code
   has A's 26 instructions at other addresses (the image-B walk lib/B/Prog/rec_clear.v of a working branch
   543f2c3645b, read as the B-code template, has the same instructions, calls and trap sites). *)

(* The walk of rec_clear (BASE + AF_rec_clear = 0x899e4, 26 instructions, 104 bytes, one block, no instrumented
   check, no UBSan trap site, no call of an __asan_report_* entry: measured on fuzz_command.asan-ubsan
   (sha256 658cefbe...) with capstone, keyed by .symtab).

   Order (0x899e4 .. 0x89a48): frame of 32 bytes, ra/s0/s1 saved; s1 := g_rec (auipc/addi at 0x899f4, the
   listing's A_OBJ 44 = 0x5e32c0); a1 := g_rec.ncalls; a0 := g_rec + 16; rec_calls_free(a0, a1) (jal 0x89a04 to
   0x89a4c); a0 := g_rec.answer; g_rec.ncalls := 0; free(a0) (jal 0x89a10 to the free wrapper 0x589cc);
   a0 := g_rec.reply; g_rec.answer := 0; s0 := g_rec + 928; free(a0) (jal 0x89a20 to 0x589cc);
   g_rec.nreplies := 0; the memory-checking runtime's memset entry on [g_rec + 928, +16) with 0 (jal 0x89a34 to
   __asan_memset 0x57b18); return.

   The four writes land in the program's own writable static g_rec, which the ASan journal of
   lib/Reusable/YCbq.v admits through a Theorem Labs lane's journal change (awr_byte's `inFP FP a /\
   Exists (in_zr a) (as_prog_static B) /\ in_img segs a` disjunct and fp_spares' `~ inFP FP a`).

   Statement: trec_clear_spec of a Theorem Labs lane's lib/B/Prog/rec_clear_c.v (a working branch f490061c104, pass 5: no astack_pres
   premise): the callee rec_calls_free and the runtime entries (free, free(NULL), the memset entry) are taken at every
   FP state, and the walk applies each at the Section's fx. The frame chain at each free is achain_chain_pre's: at
   the first, of afn_pre's achain (s0 the caller's); at the second, of achain_low (s0 = g_rec + 928). Section
   hypotheses beyond the statement's: the per-binary record CmdBSyms
   (HB), PALib (TL), the meter's laws (MTL), the program functions' call targets (cmd_sig_prog_PB, CmdObj.v's
   cmd_sig_prog), the per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib, and
   the core's prog_rw (PRW, YCbq.v; CmdRecCells.v's PROG_WRITABLE takes the same), each under the name of the lemma
   that discharges it at the pinned image (PI := PB_cmd). The per-binary facts the walk uses are a Theorem Labs lane's
   CmdRecRest.v lemmas over them, by exact (cmd_prog_img, cmd_ro_prog_apart); the A walk's `ts_prog` is CmdBSyms'
   own field on B (lib/B/YF0m.v), so RecBLemmas' recb_ts_prog_m derives it from HB. Everything else comes from the kit:
   the call of rec_calls_free, whose own footprint holds the nargs field of each entry of g_rec's call table,
   composes through lib/B/Prog/PaNoChain.v's cl_callS_wide; AR_laws from AR_laws_ok; the record's zero shadow from
   CmdZsh; the recorder's lemmas from a Theorem Labs lane's lib/B/Prog/RecBLemmas.v; and the callee and the runtime entries from
   the statement's own hypotheses. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal PaCall PaCallRun PaDenot PaNoChain PaLibF PaLibG PaLibH PaSB CmdSyms CmdList CmdAddr CmdPa CmdPaLib CmdBase CmdRep CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdZsh RecBLemmas CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_calls_free_c rec_clear_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the listing atom of g_rec: cmd_objs' 44th object is 0x5e32c0 (lib/B/Prog/CmdAddr.v:164) *)
Definition A_GREC : nat := A_OBJ 44.
(* the five fields the walk touches, one symbolic region each, so that each one is rebuilt after a call from
   the callee's post and none of them has to be kept across a write of another *)
Definition rc_stk : YP09.region := YP09.mkRegion (Some 2%nat) (-32) 0 (-32) 0 [].
Definition rc_nc : YP09.region := YP09.mkRegion (Some A_GREC) 8 12 8 12 [YP09.mkChunk 8 (CVal 4 (SOff 32 0))].
Definition rc_an : YP09.region := YP09.mkRegion (Some A_GREC) 912 920 912 920 [YP09.mkChunk 912 (CVal 8 (SOff 33 0))].
Definition rc_nr : YP09.region := YP09.mkRegion (Some A_GREC) 920 924 920 924 [YP09.mkChunk 920 (CVal 4 (SOff 35 0))].
Definition rc_rp : YP09.region := YP09.mkRegion (Some A_GREC) 928 936 0 0 [YP09.mkChunk 928 (CVal 8 (SOff 34 0))].
Definition rc_regions : smem := [rc_stk; rc_nc; rc_an; rc_nr; rc_rp].
(* the caller's stack pointer is in the stack band and g_rec is at its image address: the two the symbolic
   executor needs to see that no write of this call lands in the shadow band *)
Definition rc_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (A_GREC, mkAF A_G_REC A_G_REC 3)] [] [].
Definition rc_SH : list shent := [].
Definition Bxr : sv := SOff (A_OBJ 12) 0.
Definition RBspanR : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition ss_rc (pc : Z) (sregs : list sv) (rs : smem) : sstate := mkSS pc sregs rs None rc_facts.
(* the atoms 32..35: the four field values the walk reads *)
Definition rc_extra (nc an nr rp : Z) : list word := map (Z_to_bv 64) [nc; an; rp; nr].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG c := (@pa_sigma _ cmd_listing PI c).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* lib/Reusable/YG0f.v:260 (the reader's byte, which aval_mem uses) and lib/Reusable/YO0f.v:536 (the memory's
   byte, which val_mem uses) are the same function under two names *)
Lemma le_byte_YG_YO : forall v n k, YG0f.le_byte v n k = YO0f.le_byte v n k.
Proof. reflexivity. Qed.
Lemma val_mem_of_aval : forall (W : world SEGS) mem a n v,
aval_mem (aview SEGS (w_H W) mem) a n v -> val_mem SEGS (mrestrict (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hv. unfold aview in Hv.
destruct (mbyte SEGS (mrestrict (w_H W) mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn [option_map] in Hv. injection Hv as Hv. rewrite le_byte_YG_YO in Hv. rewrite <- Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma aval_of_val_mem : forall (W : world SEGS) mem a n v,
val_mem SEGS (mrestrict (w_H W) mem) a n v -> aval_mem (aview SEGS (w_H W) mem) a n v.
Proof.
intros W mem a n v H k Hk. pose proof (H k Hk) as Hb. unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
repeat first [progress unfold YO0f.le_byte | progress unfold YG0f.le_byte]. apply Z.mod_mod. lia.
Qed.
Lemma region_kept_bytes : forall E (m m' : word -> option byte) nn base lo hi wlo whi cs,
bv_unsigned (ew E nn) = base ->
(forall a, base + lo <= a < base + hi -> mbyte SEGS m' a = mbyte SEGS m a) ->
(forall o, wlo <= o < whi -> writable_at SEGS m' (base + o)) ->
region_kept SEGS E m m' (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E m m' nn base lo hi wlo whi cs Hn HK HW.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- exact (HK a Ha).
- intros _. replace a with (base + (a - base)) by lia. apply HW. lia.
Qed.
Lemma region_kept_val_wr : forall E (m m' : word -> option byte) nn base lo (n : nat) v wlo whi cs,
bv_unsigned (ew E nn) = base ->
val_mem SEGS m (base + lo) n v -> val_mem SEGS m' (base + lo) n v ->
(forall o, wlo <= o < whi -> writable_at SEGS m' (base + o)) ->
region_kept SEGS E m m' (YP09.mkRegion (Some nn) lo (lo + Z.of_nat n) wlo whi cs).
Proof.
intros E m m' nn base lo n v wlo whi cs Hn H1 H2 Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- replace a with (base + lo + (a - (base + lo))) by lia.
apply (val_mem_agree SEGS m m' (base + lo) n v H1 H2). lia.
- intros _. replace a with (base + (a - base)) by lia. apply Hw. lia.
Qed.

Lemma sv_denot_off0 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by lia. f_equal. lia. Qed.
Lemma le_byte_zero : forall n k, YG0f.le_byte 0 n k = 0.
Proof.
intros n k. unfold YG0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
rewrite Z.shiftr_0_l. apply Z.mod_0_l. lia.
Qed.
Lemma acall_at_bl : forall bl bl' rd a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') -> acall_at bl' rd a c P.
Proof.
intros bl bl' rd a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) HB.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [exact H5|]. split; [exact H6|].
intros k sx pn Hs Hpn. destruct (H7 k sx pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
split; [exact G1|]. split; [exact G2|]. split; [exact (HB pn (nth_error_In _ _ Hpn))|].
split; [exact G4 | exact G5].
Qed.
(* a field keeps its value when the bytes it holds do (answer_code.v's name) *)
Lemma aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk i Hi. rewrite (Hk i Hi). exact (H i Hi). Qed.
(* the recorder's state survives a call that keeps g_rec, record.spill and the blocks it owns
   (lib/B/Prog/answer_code.v's rabytes_kept / rastr_kept / acall_at_kept, same kit) *)
Lemma rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma acall_at_kept : forall bl (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl rd' a c P.
Proof.
intros bl rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha;
  apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk;
  pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha;
  apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk;
  pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [exact G3|]. split; [exact G4|].
apply (rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma acall_blocks : forall bl rd a c P, acall_at bl rd a c P -> forall pn, In pn P -> In pn bl.
Proof.
intros bl rd a c P (_ & _ & HlenP & _ & _ & _ & Hargs) pn Hin.
apply In_nth_error in Hin as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs;
[|exfalso; apply nth_error_None in Hs;
  assert (Hk' : (k < length P)%nat) by (apply nth_error_Some; rewrite Hk; discriminate); lia].
exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
Qed.
(* the whole representation, when every byte of g_rec, of record.spill and of each live block is kept *)
Lemma rc_arep_kept : forall bl (rd rd' : reader) R' Q',
arep_at bl rd A_G_REC A_REC_SPILL R' Q' ->
(forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rd' a = rd a) ->
(forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rd' a = rd a) ->
(forall p n i, In (p, n) bl -> 0 <= i < n -> rd' (p + i) = rd (p + i)) ->
arep_at bl rd' A_G_REC A_REC_SPILL R' Q'.
Proof.
intros bl rd rd' R' Q' (Hg8 & Hs8 & Hap & (Hle16 & HlenQ & Vnc & HCA & HSP & HSPL) & HANS & HREPL & HSCAL & HOWN)
KG KS KB.
assert (KBpn : forall pn i, In pn bl -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i))
by (intros [p n] i Hin Hi; exact (KB p n i Hin Hi)).
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ split; [exact Hle16|]. split; [exact HlenQ|].
  split; [apply (aval_mem_kept rd); [exact Vnc | intros k Hk; apply KG; unfold OFF_NCALLS, A_G_REC, REC_SIZE; lia]|].
  split.
  - intros i c P Hc Hi. destruct (HCA i c P Hc Hi) as (HAC & HFA). split; [|exact HFA].
    assert (Hi2 : (i < length (l_calls Q'))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    pose proof (proj1 (proj2 (proj2 (proj2 HAC)))) as _.
    apply (acall_at_kept bl rd); [exact HAC | |
      intros pn ii Hin Hii; apply KBpn; [exact (acall_blocks bl rd _ c P HAC pn Hin) | exact Hii]].
    intros j Hj. rewrite <- Z.add_assoc. apply KG.
    destruct HAC as (_ & Hle6 & _). unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS, REC_SIZE in *. lia.
  - split; [|exact HSPL]. apply (acall_at_kept bl rd); [exact HSP | |
      intros pn ii Hin Hii; apply KBpn; [exact (acall_blocks bl rd _ _ _ HSP pn Hin) | exact Hii]].
    intros j Hj. apply KS. destruct HSP as (_ & Hle6 & _).
    unfold A_REC_SPILL, SC_SIZE, CALL_OFF_ARGS in *. lia. }
split.
{ destruct (r_answer R') as [x|], (l_answer Q') as [pn|]; cbn [aanswer_at] in HANS |- *; try exact HANS.
  - destruct HANS as (V & Hne & Hin & Hsz & Hstr & Hlm).
    split; [apply (aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_ANSWER, A_G_REC, REC_SIZE; lia]|].
    split; [exact Hne|]. split; [exact Hin|]. split; [exact Hsz|]. split; [|exact Hlm].
    apply (rastr_kept rd); [exact Hstr | intros i Hi; apply (KB (fst pn) (snd pn) i); [destruct pn; exact Hin | lia]].
  - apply (aval_mem_kept rd); [exact HANS | intros k Hk; apply KG; unfold OFF_ANSWER, A_G_REC, REC_SIZE; lia]. }
split.
{ destruct (r_reply R') as [x|], (l_reply Q') as [pn|]; cbn [areply_at] in HREPL |- *; try exact HREPL.
  - destruct HREPL as (V & Vs & Hne & Hx & Hin & Hsz & Hbs & Hlm).
    split; [apply (aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_REPLY, A_G_REC, REC_SIZE; lia]|].
    split; [apply (aval_mem_kept rd); [exact Vs | intros k Hk; apply KG; unfold OFF_REPLY_SIZE, A_G_REC, REC_SIZE; lia]|].
    split; [exact Hne|]. split; [exact Hx|]. split; [exact Hin|]. split; [exact Hsz|]. split; [|exact Hlm].
    apply (rabytes_kept rd); [exact Hbs | intros i Hi; apply (KB (fst pn) (snd pn) i); [destruct pn; exact Hin | lia]].
  - destruct HREPL as (V & Vs).
    split; [apply (aval_mem_kept rd); [exact V | intros k Hk; apply KG; unfold OFF_REPLY, A_G_REC, REC_SIZE; lia]|].
    apply (aval_mem_kept rd); [exact Vs | intros k Hk; apply KG; unfold OFF_REPLY_SIZE, A_G_REC, REC_SIZE; lia]. }
split; [|exact HOWN].
destruct HSCAL as (Vrf & Vcd & Vnr & Vst & Vho & Rs).
split; [apply (aval_mem_kept rd); [exact Vrf | intros k Hk; apply KG; unfold OFF_REFUSE, A_G_REC, REC_SIZE; lia]|].
split; [apply (aval_mem_kept rd); [exact Vcd | intros k Hk; apply KG; unfold OFF_CODE, A_G_REC, REC_SIZE; lia]|].
split; [apply (aval_mem_kept rd); [exact Vnr | intros k Hk; apply KG; unfold OFF_NREPLIES, A_G_REC, REC_SIZE; lia]|].
split; [apply (aval_mem_kept rd); [exact Vst | intros k Hk; apply KG; unfold OFF_STATE, A_G_REC, REC_SIZE; lia]|].
split; [apply (aval_mem_kept rd); [exact Vho | intros k Hk; apply KG; unfold OFF_HOST, A_G_REC, REC_SIZE; lia]|].
exact Rs.
Qed.
(* the argument blocks of the recorded calls: how many there are (the allocator events rec_calls_free spends)
   and that each is a live block *)
Lemma rc_concat_len : forall (cs : list rcall) (ps : list (list (Z * Z))),
length ps = length cs ->
(forall i c P, nth_error cs i = Some c -> nth_error ps i = Some P -> length P = length (snd c)) ->
Z.of_nat (length (concat ps)) = fold_right (fun c acc => Z.of_nat (length (snd c)) + acc) 0 cs.
Proof.
induction cs as [|c cs IH]; intros ps Hl Hn.
- destruct ps as [|P ps]; [reflexivity | cbn in Hl; discriminate].
- destruct ps as [|P ps]; [cbn in Hl; discriminate|].
  cbn [concat fold_right]. rewrite length_app, Nat2Z.inj_add.
  rewrite (Hn 0%nat c P eq_refl eq_refl). f_equal.
  apply IH; [cbn in Hl; lia | intros i c0 P0 H1 H2; exact (Hn (Datatypes.S i) c0 P0 H1 H2)].
Qed.
Lemma rc_in_concat_block : forall bl rd gr sc R' Q' pn,
ag1_calls bl rd gr sc R' Q' -> In pn (concat (l_calls Q')) -> In pn bl.
Proof.
intros bl rd gr sc R' Q' pn (Hle16 & Hlen & Vnc & HCA & _ & _) Hin.
apply in_concat in Hin as (P & HinP & HinPn).
apply In_nth_error in HinP as (i & Hi).
destruct (nth_error (r_calls R') i) as [c|] eqn:Hc.
2:{ exfalso. apply nth_error_None in Hc. assert (Hi' : (i < length (l_calls Q'))%nat)
    by (apply nth_error_Some; rewrite Hi; discriminate). lia. }
destruct (HCA i c P Hc Hi) as ((_ & _ & HlenP & _ & _ & _ & Hargs) & _).
apply In_nth_error in HinPn as (k & Hk).
destruct (nth_error (snd c) k) as [s|] eqn:Hs.
2:{ exfalso. apply nth_error_None in Hs. assert (Hk' : (k < length P)%nat)
    by (apply nth_error_Some; rewrite Hk; discriminate). lia. }
exact (proj1 (proj2 (proj2 (Hargs k s pn Hs Hk)))).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the per-binary facts, cgif's names (a Theorem Labs lane's RULING-STMT.md section 1) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
(* the callee and the runtime entries this call reaches, each at every FP state, with the statement's own names
   (rec_clear_c.v:62-66) *)
Hypothesis TRCF : forall fx0 : YK11.FPState, @trec_calls_free_spec fx0 rc SK PI B MT.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis AFREE_NULL4 : forall fx0 : YK11.FPState, @afree_null04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG CS___asan_memset).
Hypothesis VOBJS : cmd_val_objs.
(* the facts stated at the pinned image only (PI := PB_cmd), under the names of the lemmas that state them there:
   CmdRecImg.v cmd_img_facts_tfib (at tfibsegs; this walk is over an abstract PAImg, so at its segments),
   CmdRecRest.v cmd_sig_prog_PB, and the core's prog_rw (YCbq.v:1145; CmdRecCells.v's PROG_WRITABLE takes it) *)
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis PRW : prog_rw SEGS B.

(* AR_laws is not a hypothesis: lib/Reusable/YG0q.v's AR_laws_ok proves it (socket_send.v:92) *)
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
Let errno_low := pal_env B TL.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
(* a Theorem Labs lane's per-binary facts (CmdRecRest.v), by exact: TFIB_PROG_STATIC is recb_PG *)
Let cmd_prog_img : forall a, Exists (in_zr a) recb_PG -> in_img SEGS a :=
  CmdRecRest.cmd_prog_img (SK := SK) SEGS B LAWS HB IMG.
Let cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) recb_PG :=
  CmdRecRest.cmd_ro_prog_apart (SK := SK) SEGS B LAWS HB IMG.
(* the runtime free rule at this walk's FP state, for RecBLemmas' Section w *)
Let AF4 : afree04_rule SEGS B MT := AFREE4 fx.

(* every byte of the program's statics is writable: the core's prog_rw over the record's ts_prog (the form
   RecBLemmas' Section w takes) *)
Lemma cmd_prog_writable : forall ly S (W : world SEGS) mem md a,
AR SEGS B ly S W mem md -> Exists (in_zr a) recb_PG -> writable_at SEGS (mrestrict (w_H W) mem) a.
Proof. intros ly S W mem md a _ HP. apply (PRW (mrestrict (w_H W) mem) a). rewrite (recb_ts_prog_m B HB). exact HP. Qed.

(* every byte of g_rec is one the journal admits as a write of this call: it is in the footprint the contract
   names (RecBLemmas' recb_grec_awr_m gives the rest: a byte of the program's statics, in the loaded image) *)
Lemma rc_awr_grec : forall STK sp0 (O : list (Z * Z)) bl0 blc fr0 lyx own a,
A_G_REC <= a < A_G_REC + REC_SIZE ->
awr_byte SEGS B STK sp0 ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) bl0 blc fr0 lyx own a.
Proof.
intros STK sp0 O bl0 blc fr0 lyx own a Ha. apply (recb_grec_awr_m B HB cmd_prog_img); [|exact Ha].
exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
(* the read-only range the contract names is disjoint from g_rec and from every live block, so the journal of
   this call keeps it (lib/B/Prog/CmdBase.v's arodata_ok_journalP after a Theorem Labs lane's change) *)
Lemma rc_ro_off_fp : forall ly S (W : world SEGS) mem md (O : list (Z * Z)),
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
forall a, in_roP SEGS RLO RHI a -> ~ inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) a.
Proof.
intros ly S W mem md O HAR HO a Hro (r & [<- | Hr] & Ha).
- cbn [fst snd] in Ha. exact (proj2 (cmd_ro_prog_apart a Hro) (recb_grec_in a Ha)).
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (HO (p, n) Hin) Ha (proj1 (cmd_ro_prog_apart a Hro))).
Qed.
(* the value of g_rec's atom: the one premise that ties the listing's object to the contract's address *)
Lemma rc_val_grec : VAL A_GREC = A_G_REC.
Proof. unfold A_GREC. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
(* g_rec lies inside a range of the record's zero-shadow list (lib/B/YF0m.v's Tfib_zero_shadow: .bss from 0xad560
   up to g_rec's end 0x5e3680), so every byte range of it is addressable and the shadow bytes its checks read are
   visible (lib/B/Prog/CmdZsh.v over AR) *)
Lemma rc_zsh_in : In (0xad560, 0x5e3680 - 0xad560) Tfib_zero_shadow.
Proof. unfold Tfib_zero_shadow. repeat first [left; reflexivity | right]. Qed.
Lemma rc_addressable : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_G_REC <= a -> a + n <= A_G_REC + REC_SIZE ->
range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n.
Proof.
intros ly S W mem md a n HAR Hlo Hhi.
apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xad560, 0x5e3680 - 0xad560) a n HAR rc_zsh_in);
cbn; unfold A_G_REC, REC_SIZE in *; try reflexivity; lia.
Qed.
Lemma rc_hull_vis : forall ly S (W : world SEGS) mem md a n,
AR SEGS B ly S W mem md -> A_G_REC <= a -> 0 < n -> a + n <= A_G_REC + REC_SIZE ->
shadow_hull_vis (aview SEGS (w_H W) mem) a n.
Proof.
intros ly S W mem md a n HAR Hlo Hn Hhi s Hs.
pose proof (cmd_zshadow_rec SEGS B LAWS HB ly S W mem md _ HAR rc_zsh_in) as Z.
cbn in Z. unfold zero_shadow, shadow_of_addr in Z.
assert (Hi : 0 <= s - (SHADOW_OFF + 0xad560 / 8) < (0x5e3680 - 0xad560) / 8).
{ unfold shadow_addr, SHADOW_OFF, A_G_REC, REC_SIZE in *.
  assert (Ha8 : 0xad560 / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (Hb8 : (a + n - 1) / 8 <= 0x5e367f / 8) by (apply Z.div_le_mono; lia).
  revert Hs. Z.div_mod_to_equations. lia. }
specialize (Z _ Hi).
replace (SHADOW_OFF + 0xad560 / 8 + (s - (SHADOW_OFF + 0xad560 / 8))) with s in Z by lia.
rewrite Z. discriminate.
Qed.

(* no inline check in this function, so the shadow entry list is empty and sh_ok is immediate *)
Lemma rc_shok : forall E m, sh_ok SEGS Bxr rc_SH E m.
Proof. intros E m. constructor. Qed.

(* The symbolic state at the entry: the caller's registers as atoms, the 32-byte frame the prologue writes, and
   one region per g_rec field the body reads (ncalls, answer, nreplies, reply). *)
Lemma rc_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem ly S md nc an nr rp,
AR SEGS B ly S W mem md ->
astk_ok REC_CLEAR_STK ly (spZ regs) ->
(forall a, spZ regs - REC_CLEAR_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 8) 4 nc -> 0 <= nc < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 912) 8 an -> 0 <= an < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 920) 4 nr -> 0 <= nr < 2 ^ 32 ->
val_mem SEGS (mrestrict (w_H W) mem) (A_G_REC + 928) 8 rp -> 0 <= rp < 2 ^ 64 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (rc_extra nc an nr rp))) (ss_rc AF_rec_clear sr_atoms rc_regions)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_rec_clear)) mem (seg_rom SEGS))).
Proof.
intros W regs mem ly S md nc an nr rp HAR Hstk Hpres Vnc Rnc Van Ran Vnr Rnr Vrp Rrp.
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTS : REC_CLEAR_STK = 16560) by reflexivity.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (rc_extra nc an nr rp))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (EG : ew E A_GREC = Z_to_bv 64 A_G_REC)
by (subst E; rewrite Eimg_img by (unfold A_GREC, A_OBJ, A_TEXT, A_LIM; lia); rewrite rc_val_grec; reflexivity).
assert (EGu : bv_unsigned (ew E A_GREC) = A_G_REC)
by (rewrite EG; apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) = nth j (rc_extra nc an nr rp) (Z_to_bv 64 0))
by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E32 : ew E 32 = Z_to_bv 64 nc) by (change 32%nat with (32 + 0)%nat; rewrite EX by lia; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 an) by (change 33%nat with (32 + 1)%nat; rewrite EX by lia; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 rp) by (change 34%nat with (32 + 2)%nat; rewrite EX by lia; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 nr) by (change 35%nat with (32 + 3)%nat; rewrite EX by lia; reflexivity).
unfold ss_rc, rc_regions. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, rc_stk, rc_nc, rc_an, rc_nr, rc_rp;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E2. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite EGu. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply recb_grec_in. unfold REC_SIZE. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 8 4%N (SOff 32 0) nc);
    [exact (sv_denot_off0 E 32%nat nc E32 ltac:(lia)) | cbn; lia | cbn; lia | exact Vnc].
  + rewrite EGu. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply recb_grec_in. unfold REC_SIZE. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 912 8%N (SOff 33 0) an);
    [exact (sv_denot_off0 E 33%nat an E33 ltac:(lia)) | cbn; lia | cbn; lia | exact Van].
  + rewrite EGu. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split.
    { intros o Ho. apply (cmd_prog_writable ly S W mem md _ HAR). apply recb_grec_in. unfold REC_SIZE. lia. }
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 920 4%N (SOff 35 0) nr);
    [exact (sv_denot_off0 E 35%nat nr E35 ltac:(lia)) | cbn; lia | cbn; lia | exact Vnr].
  + rewrite EGu. split; [unfold A_G_REC; lia|]. split; [unfold A_G_REC; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ A_G_REC 928 8%N (SOff 34 0) rp);
    [exact (sv_denot_off0 E 34%nat rp E34 ltac:(lia)) | cbn; lia | cbn; lia | exact Vrp].
- apply pairwise_disjoint_of_extents. unfold rc_stk, rc_nc, rc_an, rc_nr, rc_rp, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite E2, EGu.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold A_G_REC in *. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms rc_facts atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, EGu. split; [|split; [|exact I]].
  + split; [lia|]. split; [|lia]. change (2 ^ 4) with 16. exact Hsp0al.
  + split; [lia|]. split; [|lia]. unfold A_G_REC. reflexivity.
Qed.

Theorem trec_clear_holds : trec_clear_spec B MT.
Proof.
unfold trec_clear_spec. intros ly S W regs mem md ch R O HPRE HROD HREP Hcalls HEV HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (WS : REC_CLEAR_STK = 16560) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Has : ASTACK = 16384) by reflexivity.
destruct HREP as (Q & HREP & HOQ).
pose proof HREP as (Hg8 & Hs8 & Hap & HCALLS & HANS & HREPL & HSCAL & HOWN).
pose proof HCALLS as (Hlen16 & HlenQ & Vnc & HCA & HSP & HSPL).
pose proof HSCAL as (Vrf & Vcd & Vnr & Vst & Vho & Rrf & Rcd & Rnr & Rst & Rho).
(* the answer and the reply pointers the body loads: 0 when the recorder holds none, the block's address
   otherwise, and then a live block of the allocator *)
assert (HAN : exists an, aval_mem (rdW W mem) (A_G_REC + OFF_ANSWER) 8 an /\ 0 <= an < 2 ^ 64 /\
(l_answer Q = None -> an = 0) /\ (forall pn, l_answer Q = Some pn -> an = fst pn /\ In pn (ablocks B ly S))).
{ destruct (r_answer R) as [x|] eqn:EX; destruct (l_answer Q) as [pn|] eqn:EA;
  cbn [aanswer_at] in HANS; try (exfalso; exact HANS).
  - destruct HANS as (V & Hne & Hin & Hsz & Hstr & Hlm). destruct pn as [pp pq].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hcl & _).
    pose proof (req_size_pos pq) as Hrq.
    exists pp. split; [exact V|]. split; [cbn [fst snd] in *; lia|]. split; [discriminate|].
    intros pn' E. injection E as <-. split; [reflexivity | exact Hin].
  - exists 0. split; [exact HANS|]. split; [lia|]. split; [reflexivity | discriminate]. }
destruct HAN as (an & Van & Ran & HanN & HanS).
assert (HRP : exists rp, aval_mem (rdW W mem) (A_G_REC + OFF_REPLY) 8 rp /\ 0 <= rp < 2 ^ 64 /\
(l_reply Q = None -> rp = 0) /\ (forall pn, l_reply Q = Some pn -> rp = fst pn /\ In pn (ablocks B ly S))).
{ destruct (r_reply R) as [x|] eqn:EX; destruct (l_reply Q) as [pn|] eqn:EA;
  cbn [areply_at] in HREPL; try (exfalso; exact HREPL).
  - destruct HREPL as (V & Vs & Hne & Hx & Hin & Hsz & Hbs & Hlm). destruct pn as [pp pq].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hcl & _).
    pose proof (req_size_pos pq) as Hrq.
    exists pp. split; [exact V|]. split; [cbn [fst snd] in *; lia|]. split; [discriminate|].
    intros pn' E. injection E as <-. split; [reflexivity | exact Hin].
  - destruct HREPL as (V & Vs). exists 0. split; [exact V|]. split; [lia|]. split; [reflexivity | discriminate]. }
destruct HRP as (rp & Vrp & Rrp & HrpN & HrpS).
pose proof (rc_seed W regs mem ly S md (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp HAR Hstk Hpres
(val_mem_of_aval W mem _ 4 _ Vnc) ltac:(lia)
(val_mem_of_aval W mem _ 8 _ Van) Ran
(val_mem_of_aval W mem _ 4 _ Vnr) ltac:(lia)
(val_mem_of_aval W mem _ 8 _ Vrp) Rrp) as HS.
pose proof (rc_shok (Eimg (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)))
(mrestrict (w_H W) mem)) as SHOK.
pose proof (ajournal_init SEGS B REC_CLEAR_STK ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O)
ly S W regs mem md ch HPRE) as HJ.
set (E := Eimg (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp))) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)) E)
by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E2u : bv_unsigned (ew E 2) = spZ regs)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (EGu : bv_unsigned (ew E A_GREC) = A_G_REC)
by (subst E; rewrite Eimg_img by (unfold A_GREC, A_OBJ, A_TEXT, A_LIM; lia); rewrite rc_val_grec;
apply unsigned_lit_small; unfold A_G_REC; lia).
assert (EGu' : bv_unsigned (ew E 285%nat) = A_G_REC) by exact EGu.
unfold cfg_at, w64.
paj_run_tok RUN HS HJ SHOK RBspanR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := A_GREC);
     [reflexivity | exact EGu
     | intros aa Haa; apply rc_awr_grec; cbn [YP09.r_wlo YP09.r_whi] in Haa; unfold REC_SIZE; lia |]) ]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
(* what the prologue changed: the frame, and nothing else outside the fields the body writes *)
assert (UN : forall a, 0 <= a < 2 ^ 64 ->
~ (spZ regs - 32 <= a < spZ regs) -> ~ (A_G_REC + 8 <= a < A_G_REC + 12) ->
~ (A_G_REC + 912 <= a < A_G_REC + 924) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (spZ regs - 32 <= a < spZ regs) \/ (A_G_REC + 8 <= a < A_G_REC + 12) \/
            (A_G_REC + 912 <= a < A_G_REC + 924)) HFr).
  - intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    repeat (destruct Hin as [Hq | Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?E2u, ?EGu' in Hrr; unfold A_G_REC in *; lia|]).
    destruct Hin.
  - exact Ha.
  - intros [H | [H | H]]; [exact (H1 H) | exact (H2 H) | exact (H3 H)]. }
assert (Hsp0 : 0x606000 < spZ regs - REC_CLEAR_STK) by (rewrite WS; lia).
assert (UNG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
~ (A_G_REC + 8 <= a < A_G_REC + 12) -> ~ (A_G_REC + 912 <= a < A_G_REC + 924) ->
rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha H2 H3. apply UN; [unfold A_G_REC, REC_SIZE in *; lia | unfold A_G_REC, REC_SIZE in *; lia | exact H2 | exact H3]. }
(* the read-only bytes of the image are kept: they are neither the frame nor a byte of g_rec *)
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms))).
{ intros a Hro Ho He. destruct (cmd_ro_prog_apart a Hro) as (Himg & Hpg).
  pose proof (pa_img_range a Himg) as Hr.
  rewrite UN; [exact (HROD a Hro Ho He) | lia | lia | intros Hc; apply Hpg; apply recb_grec_in; unfold REC_SIZE; lia
  | intros Hc; apply Hpg; apply recb_grec_in; unfold REC_SIZE; lia]. }
(* the register state at the call *)
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 (Z.of_nat (length (r_calls R))))
by (subst E; change 32%nat with (32 + 0)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_extra regs _ 0); reflexivity).
assert (Psp : spZ (ms_regs ms) = spZ regs + -32)
by (unfold spZ at 1; rewrite P2, E2u, unsigned_lit_small by lia; reflexivity).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 (A_G_REC + OFF_CALLS))
by (rewrite P10, EGu'; unfold w64, OFF_CALLS; reflexivity).
assert (P11' : getr (ms_regs ms) 11 = w64 (Z.of_nat (length (l_calls Q)))).
{ rewrite P11, E32, sext32_small by lia. rewrite HlenQ. reflexivity. }
assert (Hs0 : s0Z (ms_regs ms) = s0Z regs) by (unfold s0Z; rewrite P8, (EEo 8%nat 8%bv eq_refl); reflexivity).
assert (HCH : achain ly (rdW W (ms_mem ms)) (spZ regs + -32) (s0Z (ms_regs ms)) ch).
{ rewrite Hs0. apply (achain_lower ly _ (spZ regs)); [|lia].
  apply (achain_kept ly (rdW W mem) _ _ _ _ (spZ regs) Hch ltac:(lia) ltac:(lia)).
  intros a Ha. apply UN; [lia | lia | unfold A_G_REC in *; lia | unfold A_G_REC in *; lia]. }
(* the events and the meter rec_calls_free spends: one free per recorded argument *)
assert (HEVA : Z.of_nat (length (concat (l_calls Q))) = ev_args R).
{ unfold ev_args. apply (rc_concat_len (r_calls R) (l_calls Q) HlenQ).
  intros i c P Hc Hi. destruct (HCA i c P Hc Hi) as ((_ & _ & HlenP & _) & _). exact HlenP. }
assert (Hmf : 0 <= mo_free MT) by (exact (mo_free_nonneg MT MTL)).
assert (Hev0 : 0 <= ev_args R) by (rewrite <- HEVA; lia).
assert (Hlen2 : (length (l_calls Q) <= 2)%nat) by (rewrite HlenQ; exact Hcalls).
assert (HHOME : rcf_home B ly S W (ms_mem ms) (A_G_REC + OFF_CALLS) (CALL_SIZE * Z.of_nat (length (l_calls Q)))).
{ left. unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_SIZE. lia. }
(* the B contract's UBSan premise: the table g_rec + 16 = 0x5e32d0 is 8-aligned (rec_calls_free's trap site
   0x89afc, lib/B/Prog/rec_calls_free_c.v) *)
assert (HAL8 : (A_G_REC + OFF_CALLS) mod 8 = 0) by (unfold A_G_REC, OFF_CALLS; reflexivity).
assert (HNODUP : NoDup (map fst (concat (l_calls Q)))).
{ pose proof (proj1 HOWN) as HN. apply NoDup_ListNoDup in HN. apply NoDup_ListNoDup.
  unfold lay_blocks in HN. rewrite !map_app in HN. exact (List.NoDup_app_remove_r _ _ HN). }
assert (HEVB : st_nev S + EV_REC_CALLS_FREE (l_calls Q) <= EV_MAX).
{ unfold EV_REC_CALLS_FREE. rewrite HEVA. unfold EV_REC_CLEAR in HEV. lia. }
assert (HMOKB : mo_ok MT S (XM_REC_CALLS_FREE MT (l_calls Q))).
{ apply (mok_station MT S S (XM_REC_CLEAR MT R) 0 (XM_REC_CALLS_FREE MT (l_calls Q)) MTL HMOK (mle_start MT S MTL));
  unfold XM_REC_CALLS_FREE, XM_REC_CLEAR; rewrite HEVA; nia. }
assert (HENT : forall i P, nth_error (l_calls Q) i = Some P ->
(length P <= 6)%nat /\
aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_NARGS) 4 (Z.of_nat (length P)) /\
(forall a pn, nth_error P a = Some pn ->
 aval_mem (rdW W (ms_mem ms)) (A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat i + CALL_OFF_ARGS + 8 * Z.of_nat a) 8 (fst pn) /\
 In pn (ablocks B ly S))).
{ intros i P Hi.
  assert (Hi2 : (i < length (l_calls Q))%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Hc; [|exfalso; apply nth_error_None in Hc; lia].
  destruct (HCA i c P Hc Hi) as ((Hfn & Hle6 & HlenP & Vfn & Vna & Hnd & Hargs) & _).
  split; [lia|]. split.
  - apply (aval_mem_kept (rdW W mem)); [rewrite HlenP; exact Vna|].
    intros k Hk. apply UNG; unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, REC_SIZE; lia.
  - intros a pn Hpn.
    assert (Ha2 : (a < length P)%nat) by (apply nth_error_Some; rewrite Hpn; discriminate).
    destruct (nth_error (snd c) a) as [sx|] eqn:Hs; [|exfalso; apply nth_error_None in Hs; lia].
    destruct (Hargs a sx pn Hs Hpn) as (V & Hne & Hin & _).
    split; [|exact Hin]. apply (aval_mem_kept (rdW W mem)); [exact V|].
    intros k Hk. apply UNG; unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_ARGS, REC_SIZE; lia. }
assert (HnoOfl : ~ YI16.sink_open_fp (rcf_fp (A_G_REC + OFF_CALLS) (l_calls Q))).
{ apply sink_closed_pos. unfold rcf_fp. apply Forall_app. split.
  - apply Forall_map. apply Forall_forall. intros i _. cbn [fst].
    pose proof (Nat2Z.is_nonneg i). unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS. lia.
  - apply Forall_map. apply Forall_forall. intros [p n] Hin. cbn [fst].
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rc_in_concat_block _ _ _ _ _ _ _ HCALLS Hin)) as (_ & H4096 & _).
    lia. }
(* neither the frame nor the fields the body writes are in the callee's footprint *)
assert (NFP1 : forall a, in_img SEGS a -> (a < A_G_REC + 16 \/ A_G_REC + 128 <= a) ->
~ inFP (rcf_fp (A_G_REC + OFF_CALLS) (l_calls Q)) a).
{ intros a Ha Hout (r & Hr & Hin). unfold rcf_fp in Hr. apply in_app_iff in Hr as [Hr|Hr].
  - apply in_map_iff in Hr as (i & <- & Hi). apply in_seq in Hi. cbn [fst snd] in Hin.
    unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS in *. lia.
  - apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hin.
    exact (blk_img SEGS B LAWS ly S W mem md p n a HAR (rc_in_concat_block _ _ _ _ _ _ _ HCALLS Hb) Hin Ha). }
assert (NFP1s : forall a, alloc_ceiling <= a -> ~ inFP (rcf_fp (A_G_REC + OFF_CALLS) (l_calls Q)) a).
{ intros a Ha (r & Hr & Hin). unfold rcf_fp in Hr. apply in_app_iff in Hr as [Hr|Hr].
  - apply in_map_iff in Hr as (i & <- & Hi). apply in_seq in Hi. cbn [fst snd] in Hin.
    unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS in *. lia.
  - apply in_map_iff in Hr as ([p n] & <- & Hb). cbn [fst snd] in Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (rc_in_concat_block _ _ _ _ _ _ _ HCALLS Hb))
      as (_ & H4096 & Hceilb & _). lia. }
eapply SRr_bind;
[ eapply (cl_callS_wide B LAWS W (ms_regs ms) (ms_mem ms) _ REC_CLEAR_STK (spZ regs)
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) ly S W mem md [] ly S _ 0
    REC_CALLS_FREE_STK (rcf_fp (A_G_REC + OFF_CALLS) (l_calls Q)) (EV_REC_CALLS_FREE (l_calls Q))
    (-32) (Z_to_bv 64 (BASE + 13528)) ch _ HJ Psp);
  [ reflexivity | lia | unfold REC_CALLS_FREE_STK, ASTACK; lia
  | rewrite WS; unfold REC_CALLS_FREE_STK, ASTACK; lia
  | exact P3' | exact P4' | exact P1 | apply ret_ok_codeptr_v; [lia | reflexivity]
  | rewrite unsigned_lit_small by lia; lia
  | exact HCH
  | intros HPRE1; rewrite (cmd_sig_prog_PB CS_rec_calls_free ltac:(vm_compute; tauto)); eapply SRr_mono;
    [ exact (TRCF fx ly S W (ms_regs ms) (ms_mem ms) _ ch (A_G_REC + OFF_CALLS) (l_calls Q)
        HPRE1 HROD1 P10' P11' Hlen2 HHOME HAL8 HENT HNODUP HEVB HMOKB)
    | cbv beta; unfold apost_base; intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ1 & HP & HK);
      exists ly3, S3, regs3, mem3, md3;
      split; [rewrite P1; reflexivity | split; [exact HJ1 | split; [exact HP | exact HK]]] ]
  | intros aa (r & Hr & Ha); unfold rcf_fp in Hr; apply in_app_iff in Hr as [Hr | Hr]
  | intros ly2 S2 W2 regs2 mem2 md2 HK aa Hf Hst Hn; exfalso; exact (NFP1s aa ltac:(lia) Hf) ]
| ].
{ apply in_map_iff in Hr as (i & <- & Hi). apply in_seq in Hi. cbn [fst snd] in Ha.
  apply rc_awr_grec. unfold A_G_REC, OFF_CALLS, CALL_SIZE, CALL_OFF_NARGS, REC_SIZE in *. lia. }
{ right; left. apply in_map_iff in Hr as ([p n] & <- & Hin). cbn [fst snd] in Ha.
  assert (HinB : In (p, n) (ablocks B ly S)) by (exact (rc_in_concat_block _ _ _ _ _ _ _ HCALLS Hin)).
  assert (HinO : In (p, n) O) by (apply HOQ; unfold lay_blocks; apply in_or_app; left; exact Hin).
  split.
  - exists (p, p + req_size n). split;
    [right; apply in_map_iff; exists (p, n); split; [reflexivity | exact HinO] | cbn [fst snd]; exact Ha].
  - exists p, n. split; [exact HinB | exact Ha]. }
(* the three fields the body will write still hold the values of the entry: the symbolic regions say so *)
assert (KGW : forall a n v, val_mem SEGS (mrestrict (w_H W) mem) a n v ->
val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) a n v ->
forall k, 0 <= k < Z.of_nat n -> rdW W (ms_mem ms) (a + k) = rdW W mem (a + k)).
{ intros a n v V1 V2 k Hk. unfold aview. f_equal. exact (val_mem_agree SEGS _ _ a n v V1 V2 k Hk). }
assert (Vnc1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (A_G_REC + 8) 4 (Z.of_nat (length (r_calls R)))).
{ lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let r := eval vm_compute in (nth 1%nat (ss_mem ssx) rc_nc) in
  pose proof (st_ok_region_nth E ssx _ 1%nat r HS ltac:(vm_compute; reflexivity)) as HR end.
  cbn [ms_mem restrict mkst] in HR.
  pose proof (field_of_region_any E _ A_GREC A_G_REC _ 8 12 8 12 8 4%N (SOff 32 0) HR EGu
    ltac:(left; reflexivity) ltac:(cbn; lia)) as V.
  rewrite (sv_denot_off0 E 32%nat _ E32 ltac:(lia)) in V. rewrite unsigned_lit_small in V by lia.
  rewrite Z.mod_small in V by (cbn; lia). exact V. }
assert (Van1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (A_G_REC + 912) 8 an).
{ lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let r := eval vm_compute in (nth 2%nat (ss_mem ssx) rc_an) in
  pose proof (st_ok_region_nth E ssx _ 2%nat r HS ltac:(vm_compute; reflexivity)) as HR end.
  cbn [ms_mem restrict mkst] in HR.
  pose proof (field_of_region_any E _ A_GREC A_G_REC _ 912 920 912 920 912 8%N (SOff 33 0) HR EGu
    ltac:(left; reflexivity) ltac:(cbn; lia)) as V.
  assert (E33 : ew E 33 = Z_to_bv 64 an)
  by (subst E; change 33%nat with (32 + 1)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_extra regs _ 1); reflexivity).
  rewrite (sv_denot_off0 E 33%nat _ E33 ltac:(lia)) in V. rewrite unsigned_lit_small in V by lia.
  rewrite Z.mod_small in V by (cbn; lia). exact V. }
assert (Vnr1 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (A_G_REC + 920) 4 (r_nreplies R)).
{ lazymatch type of HS with st_ok _ _ ?ssx _ =>
  let r := eval vm_compute in (nth 3%nat (ss_mem ssx) rc_nr) in
  pose proof (st_ok_region_nth E ssx _ 3%nat r HS ltac:(vm_compute; reflexivity)) as HR end.
  cbn [ms_mem restrict mkst] in HR.
  pose proof (field_of_region_any E _ A_GREC A_G_REC _ 920 924 920 924 920 4%N (SOff 35 0) HR EGu
    ltac:(left; reflexivity) ltac:(cbn; lia)) as V.
  assert (E35 : ew E 35 = Z_to_bv 64 (r_nreplies R))
  by (subst E; change 35%nat with (32 + 3)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_extra regs _ 3); reflexivity).
  rewrite (sv_denot_off0 E 35%nat _ E35 ltac:(lia)) in V. rewrite unsigned_lit_small in V by lia.
  rewrite Z.mod_small in V by (cbn; lia). exact V. }
assert (KG : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha.
  destruct (Z_lt_le_dec a (A_G_REC + 8)) as [H1|H1];
  [apply UNG; unfold REC_SIZE in *; lia|].
  destruct (Z_lt_le_dec a (A_G_REC + 12)) as [H2|H2].
  { replace a with (A_G_REC + 8 + (a - (A_G_REC + 8))) by lia.
    apply (KGW (A_G_REC + 8) 4%nat (Z.of_nat (length (r_calls R)))); [exact (val_mem_of_aval W mem _ 4 _ Vnc) | exact Vnc1 | cbn; lia]. }
  destruct (Z_lt_le_dec a (A_G_REC + 912)) as [H3|H3];
  [apply UNG; unfold REC_SIZE in *; lia|].
  destruct (Z_lt_le_dec a (A_G_REC + 920)) as [H4|H4].
  { replace a with (A_G_REC + 912 + (a - (A_G_REC + 912))) by lia.
    apply (KGW (A_G_REC + 912) 8%nat an); [exact (val_mem_of_aval W mem _ 8 _ Van) | exact Van1 | cbn; lia]. }
  destruct (Z_lt_le_dec a (A_G_REC + 924)) as [H5|H5].
  { replace a with (A_G_REC + 920 + (a - (A_G_REC + 920))) by lia.
    apply (KGW (A_G_REC + 920) 4%nat (r_nreplies R)); [exact (val_mem_of_aval W mem _ 4 _ Vnr) | exact Vnr1 | cbn; lia]. }
  apply UNG; unfold REC_SIZE in *; lia. }
assert (KS : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply UN; unfold A_REC_SPILL, SC_SIZE, A_G_REC, REC_SIZE in *; lia. }
assert (KB : forall p n i, In (p, n) (ablocks B ly S) -> 0 <= i < n -> rdW W (ms_mem ms) (p + i) = rdW W mem (p + i)).
{ intros p n i Hin Hi.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hp4096 & Hpceil & _).
  pose proof (blk_off_imgP B ly S W mem md p n HAR Hin) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  apply UN; unfold A_G_REC, REC_SIZE in *; lia. }
assert (HREPc : arep_at (ablocks B ly S) (rdW W (ms_mem ms)) A_G_REC A_REC_SPILL R Q)
by (exact (rc_arep_kept _ _ _ R Q HREP KG KS KB)).
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc3 & HP3 & HK3).
destruct HK3 as (HPERM1 & HNARGS1 & HTAB1 & HBLK1 & HREP1 & _ & _ & _ & HMLE1).
pose proof (HREP1 R Q HREPc eq_refl eq_refl) as HREP2.
(* the bytes of g_rec outside the nargs fields the callee cleared are the bytes of the call state *)
assert (PGSEP : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. pose proof (recb_grec_in a Ha) as HP. split; [exact (cmd_prog_img a HP)|].
  destruct (prog_static_sep B a (ts_ok B HB) ltac:(rewrite (recb_ts_prog_m B HB); exact HP)) as (H1 & H2 & _).
  split; [exact H1 | exact H2]. }
assert (KEEP1 : forall a, A_G_REC <= a < A_G_REC + REC_SIZE ->
~ inFP (rcf_fp (A_G_REC + OFF_CALLS) (l_calls Q)) a -> rdW W3 mem3 a = rdW W (ms_mem ms) a).
{ intros a Ha Hnf. destruct (PGSEP a Ha) as (Himg & Ho & He).
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  exact (F3 a Himg Ho He (conj (fun Hopen => False_ind _ (HnoOfl Hopen)) Hnf)). }
pose proof (proj1 HJ3) as HAR3.
jafter_call_keep_pi HS 36%nat regs3 (mrestrict (w_H W3) mem3) HP3 [0;1;2;3;4]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - eapply (region_kept_stack_sub SEGS B); [exact HJc3 | exact HJ3 | exact E2u | lia | rewrite WS; lia | lia
    | cbn [YP09.r_lo YP09.r_wlo]; lia | cbn [YP09.r_hi YP09.r_whi]; lia
    | intros a Ha; apply NFP1s; cbn [YP09.r_lo YP09.r_hi] in Ha; lia ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 8 12 8 12); [exact EGu
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEP1;
      [unfold REC_SIZE; lia | apply NFP1; [exact (proj1 (PGSEP a ltac:(unfold REC_SIZE; lia))) | unfold REC_SIZE; lia]]
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ3 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 912 920 912 920); [exact EGu
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEP1;
      [unfold REC_SIZE; lia | apply NFP1; [exact (proj1 (PGSEP a ltac:(unfold REC_SIZE; lia))) | unfold REC_SIZE; lia]]
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ3 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 920 924 920 924); [exact EGu
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEP1;
      [unfold REC_SIZE; lia | apply NFP1; [exact (proj1 (PGSEP a ltac:(unfold REC_SIZE; lia))) | unfold REC_SIZE; lia]]
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ3 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 928 936 0 0); [exact EGu
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEP1;
      [unfold REC_SIZE; lia | apply NFP1; [exact (proj1 (PGSEP a ltac:(unfold REC_SIZE; lia))) | unfold REC_SIZE; lia]]
    | intros o Ho; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc E 36 (map (getr regs3) CLOB)) as E3 eqn:HE3 in HS.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD3 : forall n, (n < 36)%nat -> ew E3 n = ew E n) by (intros n Hn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE3 : env_agree 32 (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)) E3)
by (rewrite HE3; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
assert (EGu3 : bv_unsigned (ew E3 A_GREC) = A_G_REC)
by (rewrite HE3, ew_havoc_above by (cbv; lia); exact EGu).
clear HE3.
assert (E2u3 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite OLD3 by lia; exact E2u).
assert (EGu3' : bv_unsigned (ew E3 285%nat) = A_G_REC) by exact EGu3.
pose proof (rc_shok E3 (mrestrict (w_H W3) mem3)) as SHOK3.
(* 0x89a08 .. 0x89a10: a0 := g_rec.answer, g_rec.ncalls := 0, then the free wrapper *)
paj_run_tok RUN HS HJ3 SHOK3 RBspanR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u3 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := A_GREC);
     [reflexivity | exact EGu3
     | intros aa Haa; apply rc_awr_grec; cbn [YP09.r_wlo YP09.r_whi] in Haa; unfold REC_SIZE; lia |]) ]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv0 := mdq) in *; clearbody mdv0 end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
(* the chain of frames, at any later state that keeps the caller's stack *)
assert (CH : forall (W' : world SEGS) (mem' : word -> option byte) ly',
ly_top ly' = ly_top ly -> (forall a, spZ regs <= a < 2 ^ 64 -> rdW W' mem' a = rdW W mem a) ->
achain ly' (rdW W' mem') (spZ regs + -32) (s0Z regs) ch).
{ intros W' mem' ly' Etop HK. apply (achain_lower ly' _ (spZ regs)); [|lia].
  apply (achain_ly_top ly ly' _ _ _ _ Etop).
  exact (achain_kept ly (rdW W mem) _ _ _ _ (spZ regs) Hch ltac:(lia) ltac:(lia) HK). }
assert (KHI1 : forall a, spZ regs <= a < 2 ^ 64 -> rdW W3 (ms_mem ms0) a = rdW W mem a).
{ intros a Ha.
  assert (K2 : rdW W3 (ms_mem ms0) a = rdW W3 mem3 a).
  { lazymatch goal with Hfr : frame_of E3 _ (mrestrict _ mem3) (mrestrict _ (ms_mem ms0)) |- _ =>
    apply (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E3 _ _ _ _ a Hfr ltac:(lia)) end.
    intros (r & Hr & Hrr). vm_compute in Hr.
    repeat (destruct Hr as [Hq | Hr]; [subst r; cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hrr;
      rewrite ?E2u3, ?EGu3' in Hrr; unfold A_G_REC in *; lia|]). destruct Hr. }
  assert (K3 : rdW W3 mem3 a = rdW W (ms_mem ms) a).
  { pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply (F1 a); [lia | lia | apply NFP1s; lia]. }
  rewrite K2, K3. apply UN; unfold A_G_REC, REC_SIZE in *; lia. }
pose proof HJ3 as (HAR3b & HLY3 & _ & _ & _ & _ & HNEV3 & _).
pose proof HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop3 & _).
(* the answer block, if the recorder holds one, is still live and is in the footprint *)
assert (Hoth : forall pn, In pn (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)) ->
In pn (ablocks B ly3 S3)).
{ intros pn Hpn.
  assert (HinQ : In pn (lay_blocks Q)) by (unfold lay_blocks; apply in_or_app; right; exact Hpn).
  assert (HinS : In pn (ablocks B ly S)) by (exact (lay_blocks_in _ _ _ _ _ _ HREP pn HinQ)).
  destruct (in_app_or _ _ _ (Permutation_in _ HPERM1 HinS)) as [H | H]; [exact H|].
  exfalso. pose proof (proj1 HOWN) as HND. apply NoDup_ListNoDup in HND.
  unfold lay_blocks in HND. rewrite map_app in HND.
  exact (list_nodup_app_disj _ _ (fst pn) HND (in_map fst _ _ H) (in_map fst _ _ Hpn)). }
assert (Hans : forall pn, l_answer Q = Some pn -> In pn (ablocks B ly3 S3) /\
(In pn (ablocks B ly S) -> forall i, 0 <= i < req_size (snd pn) ->
 inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) (fst pn + i))).
{ intros pn Hpn.
  assert (Hin2 : In pn (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)))
  by (apply in_or_app; right; apply in_or_app; left; rewrite Hpn; left; reflexivity).
  split; [exact (Hoth pn Hin2)|].
  intros _ i Hi. exists (fst pn, fst pn + req_size (snd pn)). split; [|cbn [fst snd]; lia].
  right. apply in_map_iff. exists pn. split; [reflexivity|].
  apply HOQ. unfold lay_blocks. apply in_or_app. right. exact Hin2. }
assert (Hoa : oaddr (l_answer Q) = an)
by (destruct (l_answer Q) as [pn|]; [exact (eq_sym (proj1 (HanS pn eq_refl))) | exact (eq_sym (HanN eq_refl))]).
assert (E33 : ew E 33 = Z_to_bv 64 an)
by (subst E; change 33%nat with (32 + 1)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_extra regs _ 1); reflexivity).
assert (Qa0 : getr (ms_regs ms0) 10 = w64 (oaddr (l_answer Q)))
by (rewrite Q10, OLD3 by lia; rewrite E33, Hoa; reflexivity).
assert (Qsp : spZ (ms_regs ms0) = spZ regs + -32)
by (unfold spZ at 1; rewrite Q2, E2u3, unsigned_lit_small by lia; reflexivity).
assert (Qgp : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite Q3, OLD3 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (Qtp : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite Q4, OLD3 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (Qs0 : s0Z (ms_regs ms0) = s0Z regs)
by (unfold s0Z; rewrite Q8, OLD3 by lia; rewrite (EEo 8%nat 8%bv eq_refl); reflexivity).
assert (HNEVa : st_nev S3 < EV_MAX) by (unfold EV_REC_CALLS_FREE in HNEV3; rewrite HEVA in HNEV3; unfold EV_REC_CLEAR in HEV; lia).
assert (HCHa : chain_pre ly3 (rdW W3 (ms_mem ms0)) (ms_regs ms0) ch).
{ apply (achain_chain_pre ly3 _ (spZ regs + -32) (s0Z regs) ch (ms_regs ms0) (CH W3 (ms_mem ms0) ly3 Etop3 KHI1));
  [rewrite Qsp; lia | exact Qs0 | unfold raZ; rewrite Q1, unsigned_lit_small by lia; lia]. }
assert (HMOKa : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT S S3 (XM_REC_CLEAR MT R) (XM_REC_CALLS_FREE MT (l_calls Q)) (mo_free MT) MTL HMOK HMLE1);
  [lia | unfold XM_REC_CALLS_FREE, XM_REC_CLEAR; rewrite HEVA; nia]. }
rewrite (pal_free B TL).
eapply SRr_bind;
[ exact (recb_free_any B MT AF4 HB cmd_prog_img cmd_prog_writable
    W3 (ms_regs ms0) (ms_mem ms0) REC_CLEAR_STK (spZ regs)
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) ly S W mem md [] ly3 S3 _ (0 + EV_REC_CALLS_FREE (l_calls Q))
    (-32) (Z_to_bv 64 (BASE + 13540)) ch (l_answer Q) (fun _ => AFREE_NULL4 fx) HJ3 Hans Qa0 Qsp eq_refl ltac:(lia)
    ltac:(rewrite WS; unfold ASTACK; lia) Qgp Qtp Q1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) HNEVa HCHa HMOKa)
| ].
cbv beta. unfold recb_free_post. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HPERM4 & HFR4 & HK4 & HMLE4).
(* 0x89a14 .. 0x89a20: a0 := g_rec.reply, g_rec.answer := 0, s0 := g_rec + 928, then the free wrapper *)
pose proof (proj1 HJ4) as HAR4.
pose proof HJ4 as (_ & HLY4 & _ & _ & _ & _ & HNEV4 & _ & _ & _ & _ & _ & _ & HPRES4 & _).
pose proof HLY4 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop4 & _).
assert (KEEPB : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W4 mem4 a = rdW W3 (ms_mem ms0) a)
by (intros a Ha; exact (recb_kept_prog B MT AF4 HB cmd_prog_img cmd_prog_writable
  _ _ _ _ _ _ _ _ _ a HK4 (recb_grec_in a Ha))).
assert (KHIB : forall a, spZ regs - 32 <= a < 2 ^ 64 -> rdW W4 mem4 a = rdW W3 (ms_mem ms0) a).
{ intros a Ha. apply (proj1 HK4 a); [lia | lia]. }
jafter_call_keep_pi HS 56%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0;1;2;3;4]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_bytes _ _ _ 2%nat (spZ regs) (-32) 0 (-32) 0); [exact E2u3
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KHIB; lia
    | intros o Ho; apply (apresent_writable SEGS); apply HPRES4; rewrite WS; lia ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 8 12 8 12); [exact EGu3
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPB; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ4 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 912 920 912 920); [exact EGu3
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPB; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ4 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 920 924 920 924); [exact EGu3
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPB; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ4 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 928 936 0 0); [exact EGu3
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPB; unfold REC_SIZE; lia
    | intros o Ho; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS4. rename HS4 into HS.
remember (havoc E3 56 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall n, (n < 56)%nat -> ew E4 n = ew E3 n) by (intros n Hn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE4 : env_agree 32 (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)) E4)
by (rewrite HE4; apply env_agree_havoc_ge; [cbv; lia | exact HAE3]).
assert (EGu4 : bv_unsigned (ew E4 A_GREC) = A_G_REC)
by (rewrite HE4, ew_havoc_above by (cbv; lia); exact EGu3).
clear HE4.
assert (E2u4 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite OLD4 by lia; exact E2u3).
assert (EGu4' : bv_unsigned (ew E4 285%nat) = A_G_REC) by exact EGu4.
pose proof (rc_shok E4 (mrestrict (w_H W4) mem4)) as SHOK4.
paj_run_tok RUN HS HJ4 SHOK4 RBspanR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u4 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := A_GREC);
     [reflexivity | exact EGu4
     | intros aa Haa; apply rc_awr_grec; cbn [YP09.r_wlo YP09.r_whi] in Haa; unfold REC_SIZE; lia |]) ]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv1 := mdq) in *; clearbody mdv1 end.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (8%bv : bv 5) T8. prreg HS (10%bv : bv 5) T10.
(* the reply block, if the recorder holds one, is still live: the answer's free took only the answer *)
assert (Hrepb : forall pn, l_reply Q = Some pn -> In pn (ablocks B ly4 S4) /\
(In pn (ablocks B ly S) -> forall i, 0 <= i < req_size (snd pn) ->
 inFP ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) (fst pn + i))).
{ intros pn Hpn.
  assert (Hin2 : In pn (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)))
  by (apply in_or_app; right; apply in_or_app; right; rewrite Hpn; left; reflexivity).
  assert (Hin3 : In pn (ablocks B ly3 S3)) by (exact (Hoth pn Hin2)).
  split.
  - destruct (in_app_or _ _ _ (Permutation_in _ HPERM4 Hin3)) as [H | H]; [|exact H].
    exfalso. pose proof (proj1 HOWN) as HND. apply NoDup_ListNoDup in HND.
    unfold lay_blocks in HND. rewrite !map_app in HND.
    apply (List.NoDup_app_remove_l _ _) in HND. apply (List.NoDup_app_remove_l _ _) in HND.
    assert (Hinr : In pn (oblk (l_reply Q))) by (rewrite Hpn; left; reflexivity).
    exact (list_nodup_app_disj _ _ (fst pn) HND (in_map fst _ _ H) (in_map fst _ _ Hinr)).
  - intros _ i Hi. exists (fst pn, fst pn + req_size (snd pn)). split; [|cbn [fst snd]; lia].
    right. apply in_map_iff. exists pn. split; [reflexivity|].
    apply HOQ. unfold lay_blocks. apply in_or_app. right. exact Hin2. }
assert (E34 : ew E 34 = Z_to_bv 64 rp)
by (subst E; change 34%nat with (32 + 2)%nat; rewrite Eimg_low by (unfold A_TEXT; lia);
rewrite (ew_Ereg_extra regs _ 2); reflexivity).
assert (Hor : oaddr (l_reply Q) = rp)
by (destruct (l_reply Q) as [pn|]; [exact (eq_sym (proj1 (HrpS pn eq_refl))) | exact (eq_sym (HrpN eq_refl))]).
assert (Ta0 : getr (ms_regs ms1) 10 = w64 (oaddr (l_reply Q)))
by (rewrite T10, OLD4, OLD3 by lia; rewrite E34, Hor; reflexivity).
assert (Tsp : spZ (ms_regs ms1) = spZ regs + -32)
by (unfold spZ at 1; rewrite T2, E2u4, unsigned_lit_small by lia; reflexivity).
assert (Tgp : getr (ms_regs ms1) 3 = w64 (as_gp B))
by (rewrite T3, OLD4, OLD3 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (Ttp : getr (ms_regs ms1) 4 = w64 (as_tp B))
by (rewrite T4, OLD4, OLD3 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
assert (Ts0 : s0Z (ms_regs ms1) = A_G_REC + 928)
by (unfold s0Z; rewrite T8, EGu4', unsigned_lit_small by (unfold A_G_REC; lia); reflexivity).
assert (HNEVb : st_nev S4 < EV_MAX)
by (unfold EV_REC_CALLS_FREE in HNEV4; rewrite HEVA in HNEV4; unfold EV_REC_CLEAR in HEV; lia).
assert (HCHb : chain_pre ly4 (rdW W4 (ms_mem ms1)) (ms_regs ms1) []).
{ apply (achain_chain_pre ly4 _ (spZ regs + -32) (A_G_REC + 928) [] (ms_regs ms1));
  [apply achain_low; unfold A_G_REC; lia | rewrite Tsp; lia | exact Ts0
  | unfold raZ; rewrite T1, unsigned_lit_small by lia; lia]. }
assert (HMLE14 : mo_le MT S S4 (XM_REC_CALLS_FREE MT (l_calls Q) + mo_free MT))
by (exact (mle_station MT S S3 S4 _ _ MTL HMLE1 HMLE4)).
assert (HMOKb : mo_ok MT S4 (mo_free MT)).
{ apply (mok_station MT S S4 (XM_REC_CLEAR MT R) (XM_REC_CALLS_FREE MT (l_calls Q) + mo_free MT) (mo_free MT)
    MTL HMOK HMLE14); [lia | unfold XM_REC_CALLS_FREE, XM_REC_CLEAR; rewrite HEVA; nia]. }
rewrite (pal_free B TL).
eapply SRr_bind;
[ exact (recb_free_any B MT AF4 HB cmd_prog_img cmd_prog_writable
    W4 (ms_regs ms1) (ms_mem ms1) REC_CLEAR_STK (spZ regs)
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) ly S W mem md [] ly4 S4 _
    (0 + EV_REC_CALLS_FREE (l_calls Q) + 1) (-32) (Z_to_bv 64 (BASE + 13556)) [] (l_reply Q)
    (fun _ => AFREE_NULL4 fx) HJ4 Hrepb Ta0 Tsp eq_refl ltac:(lia) ltac:(rewrite WS; unfold ASTACK; lia) Tgp Ttp T1
    ltac:(apply ret_ok_codeptr_v; [lia | reflexivity]) HNEVb HCHb HMOKb)
| ].
cbv beta. unfold recb_free_post. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 & HPERM5 & HFR5 & HK5 & HMLE5).
(* 0x89a24 .. 0x89a34: g_rec.nreplies := 0, a0 := g_rec + 928, a1 := 0, a2 := 16, then the runtime's memset *)
pose proof (proj1 HJ5) as HAR5.
pose proof HJ5 as (_ & HLY5 & _ & _ & _ & _ & HNEV5 & _ & _ & _ & _ & _ & _ & HPRES5 & _).
pose proof HLY5 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop5 & _).
assert (KEEPC : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> rdW W5 mem5 a = rdW W4 (ms_mem ms1) a)
by (intros a Ha; exact (recb_kept_prog B MT AF4 HB cmd_prog_img cmd_prog_writable
  _ _ _ _ _ _ _ _ _ a HK5 (recb_grec_in a Ha))).
assert (KHIC : forall a, spZ regs - 32 <= a < 2 ^ 64 -> rdW W5 mem5 a = rdW W4 (ms_mem ms1) a).
{ intros a Ha. apply (proj1 HK5 a); [lia | lia]. }
jafter_call_keep_pi HS 76%nat regs5 (mrestrict (w_H W5) mem5) HP5 [0;1;2;3;4]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_bytes _ _ _ 2%nat (spZ regs) (-32) 0 (-32) 0); [exact E2u4
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KHIC; lia
    | intros o Ho; apply (apresent_writable SEGS); apply HPRES5; rewrite WS; lia ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 8 12 8 12); [exact EGu4
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPC; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ5 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 912 920 912 920); [exact EGu4
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPC; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ5 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 920 924 920 924); [exact EGu4
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPC; unfold REC_SIZE; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ5 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 928 936 0 0); [exact EGu4
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply KEEPC; unfold REC_SIZE; lia
    | intros o Ho; lia ]. }
clear HS. rewrite <- restrict_mkst_fx in HS5. rename HS5 into HS.
remember (havoc E4 76 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall n, (n < 76)%nat -> ew E5 n = ew E4 n) by (intros n Hn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hn).
assert (HAE5 : env_agree 32 (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)) E5)
by (rewrite HE5; apply env_agree_havoc_ge; [cbv; lia | exact HAE4]).
assert (EGu5 : bv_unsigned (ew E5 A_GREC) = A_G_REC)
by (rewrite HE5, ew_havoc_above by (cbv; lia); exact EGu4).
clear HE5.
assert (E2u5 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite OLD5 by lia; exact E2u4).
assert (EGu5' : bv_unsigned (ew E5 285%nat) = A_G_REC) by exact EGu5.
pose proof (rc_shok E5 (mrestrict (w_H W5) mem5)) as SHOK5.
paj_run_tok RUN HS HJ5 SHOK5 RBspanR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2u5 | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := A_GREC);
     [reflexivity | exact EGu5
     | intros aa Haa; apply rc_awr_grec; cbn [YP09.r_wlo YP09.r_whi] in Haa; unfold REC_SIZE; lia |]) ]. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdq) _ => set (mdv2 := mdq) in *; clearbody mdv2 end.
pmkst HS.
prreg HS (1%bv : bv 5) U1. prreg HS (2%bv : bv 5) U2. prreg HS (3%bv : bv 5) U3. prreg HS (4%bv : bv 5) U4.
prreg HS (10%bv : bv 5) U10. prreg HS (11%bv : bv 5) U11. prreg HS (12%bv : bv 5) U12.
(* the memory-checking runtime's memset entry on [g_rec + 928, +16) with 0: the reply pointer and its size *)
pose proof (proj1 HJ5) as HARm.
assert (Ud : getr (ms_regs ms2) 10 = w64 (A_G_REC + 928))
by (rewrite U10, EGu5'; unfold w64; reflexivity).
assert (Usp : spZ (ms_regs ms2) = spZ regs + -32)
by (unfold spZ at 1; rewrite U2, E2u5, unsigned_lit_small by lia; reflexivity).
assert (Ugp : getr (ms_regs ms2) 3 = w64 (as_gp B))
by (rewrite U3, OLD5, OLD4, OLD3 by lia; rewrite (EEo 3%nat 3%bv eq_refl); exact Hgp).
assert (Utp : getr (ms_regs ms2) 4 = w64 (as_tp B))
by (rewrite U4, OLD5, OLD4, OLD3 by lia; rewrite (EEo 4%nat 4%bv eq_refl); exact Htp).
eapply SRr_bind;
[ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIG CS___asan_memset) (AMEMSET fx)
    W5 (ms_regs ms2) (ms_mem ms2) REC_CLEAR_STK (spZ regs)
    ((A_G_REC, A_G_REC + REC_SIZE) :: ablocks_fp O) ly S W mem md [] ly5 S5 mdv2 _
    (A_G_REC + 928) 0 16 (-32) (Z_to_bv 64 (BASE + 13576)) HJ5 Ud U11 U12);
  [ lia | unfold A_G_REC; lia | unfold A_G_REC; lia | exact Usp | reflexivity | lia
  | rewrite WS; unfold ESTACK; lia | exact Ugp | exact Utp | exact U1
  | apply ret_ok_codeptr_v; [lia | reflexivity]
  | intros a Ha; split; [apply rc_awr_grec; unfold REC_SIZE; lia | unfold A_G_REC in *; lia]
  | intros a Ha _ _; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ5 | unfold REC_SIZE; lia]
  | unfold amem_range, A_G_REC, kLowMemEnd; lia
  | apply (rc_addressable ly5 S5 W5 (ms_mem ms2) mdv2 (A_G_REC + 928) 16 HARm);
    [unfold A_G_REC; lia | unfold REC_SIZE; lia]
  | intros _; apply (rc_hull_vis ly5 S5 W5 (ms_mem ms2) mdv2 (A_G_REC + 928) 16 HARm);
    [unfold A_G_REC; lia | lia | unfold REC_SIZE; lia]
  | exact I ]
| ].
cbv beta. intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & Hd6 & HSET6 & HKEEP6 & HPRES6 & HMAT6).
(* 0x89a38 .. 0x89a48: the epilogue restores ra, s0 and s1, drops the frame and returns *)
pose proof (proj1 HJ6) as HAR6.
pose proof HJ6 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRESj6 & _).
jafter_call_keep_pi HS 96%nat regs6 (mrestrict (w_H W5) mem6) HP6 [0;1;2;3]%nat HS6.
match type of HS6 with ?t -> _ => assert (HRK : t); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  - apply (region_kept_bytes _ _ _ 2%nat (spZ regs) (-32) 0 (-32) 0); [exact E2u5
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply HKEEP6;
      [lia | unfold A_G_REC; lia | lia]
    | intros o Ho; apply (apresent_writable SEGS); apply HPRESj6; rewrite WS; lia ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 8 12 8 12); [exact EGu5
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply HKEEP6; unfold A_G_REC in *; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ6 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 912 920 912 920); [exact EGu5
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply HKEEP6; unfold A_G_REC in *; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ6 | unfold REC_SIZE; lia] ].
  - apply (region_kept_bytes _ _ _ A_GREC A_G_REC 920 924 920 924); [exact EGu5
    | intros a Ha; cbn [YP09.r_lo YP09.r_hi] in Ha; apply (mbyte_of_aview SEGS); apply HKEEP6; unfold A_G_REC in *; lia
    | intros o Ho; eapply (recb_grec_writable_m B cmd_prog_writable); [exact HJ6 | unfold REC_SIZE; lia] ]. }
clear HS. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
remember (havoc E5 96 (map (getr regs6) CLOB)) as Ef eqn:HEf in HS.
assert (HEIf : img_env VAL A_LIM Ef) by (rewrite HEf; apply img_env_havoc; [exact HEI5 | cbv; lia]).
assert (OLDf : forall n, (n < 96)%nat -> ew Ef n = ew E5 n) by (intros n Hn; rewrite HEf; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEf : env_agree 32 (Ereg regs (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp)) Ef)
by (rewrite HEf; apply env_agree_havoc_ge; [cbv; lia | exact HAE5]).
assert (EGuf : bv_unsigned (ew Ef A_GREC) = A_G_REC)
by (rewrite HEf, ew_havoc_above by (cbv; lia); exact EGu5).
clear HEf.
assert (E2uf : bv_unsigned (ew Ef 2) = spZ regs) by (rewrite OLDf by lia; exact E2u5).
assert (EGuf' : bv_unsigned (ew Ef 285%nat) = A_G_REC) by exact EGuf.
pose proof (rc_shok Ef (mrestrict (w_H W5) mem6)) as SHOKf.
paj_run_tok RUN HS HJ6 SHOKf RBspanR.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  eapply awr_ok_cons_stack with (n := 2%nat);
  [reflexivity | exact E2uf | cbn [YP09.r_wlo]; rewrite WS; lia | cbn [YP09.r_whi]; lia |].
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | (eapply awr_ok_cons_gen with (n := A_GREC);
     [reflexivity | exact EGuf
     | intros aa Haa; apply rc_awr_grec; cbn [YP09.r_wlo YP09.r_whi] in Haa; unfold REC_SIZE; lia |]) ]. }
(* every byte of the program's statics outside the four fields this call wrote, and every byte of a block the
   recorder still owns, holds what it held at the entry *)
assert (PGB : forall a, Exists (in_zr a) recb_PG -> 0x5e32c0 <= a < 0x5e37e4).
{ intros a HP. apply Exists_exists in HP as (r & Hr & Hz). unfold recb_PG in Hr. cbn [In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; unfold in_zr in Hz; cbn [fst snd] in Hz;
  unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE, A_G_QUITTING in *; lia. }
assert (HSPB : 0x606100 < spZ regs - 32) by (rewrite WS in Hsp0; lia).
assert (KPG : forall a, Exists (in_zr a) recb_PG -> (a < A_G_REC + 16 \/ A_G_REC + 128 <= a) ->
~ (A_G_REC + 8 <= a < A_G_REC + 12) -> ~ (A_G_REC + 912 <= a < A_G_REC + 924) ->
~ (A_G_REC + 928 <= a < A_G_REC + 944) -> rdW W5 (ms_mem ms3) a = rdW W mem a).
{ intros a HP H0 H1 H2 H3. pose proof (PGB a HP) as Hb. pose proof (recb_prog_unowned B MT AF4 HB cmd_prog_img cmd_prog_writable a HP) as (Himg & Ho & He).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable Ef _ _ _ _ a HFr3 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2uf, ?EGuf' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  rewrite (HKEEP6 a ltac:(lia) ltac:(unfold A_G_REC in *; lia) ltac:(lia)).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E5 _ _ _ _ a HFr2 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u4, ?EGu4' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  rewrite (recb_free_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable ly4 S4 W4 (ms_mem ms1) _ W5 mem5 _ _ (l_reply Q) (ablocks B ly5 S5) a
    (proj1 HJ4) (recb_ablocks_nodup B MT AF4 HB cmd_prog_img cmd_prog_writable _ _ _ _ _ (proj1 HJ4)) HPERM5 HK5 (or_introl HP)).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E4 _ _ _ _ a HFr1 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u4, ?EGu4' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  rewrite (recb_free_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable ly3 S3 W3 (ms_mem ms0) _ W4 mem4 _ _ (l_answer Q) (ablocks B ly4 S4) a
    (proj1 HJ3) (recb_ablocks_nodup B MT AF4 HB cmd_prog_img cmd_prog_writable _ _ _ _ _ (proj1 HJ3)) HPERM4 HK4 (or_introl HP)).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E3 _ _ _ _ a HFr0 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u3, ?EGu3' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  pose proof HJc3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  rewrite (F3 a Himg Ho He (conj (fun Hopen => False_ind _ (HnoOfl Hopen))
    (NFP1 a Himg H0))).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E _ _ _ _ a HFr ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u, ?EGu' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  reflexivity. }
assert (KBL : forall b m i, In (b, m) (ablocks B ly5 S5) -> 0 <= i < m ->
rdW W5 (ms_mem ms3) (b + i) = rdW W mem (b + i)).
{ intros b m i Hin Hi.
  assert (Hin4 : In (b, m) (ablocks B ly4 S4))
  by (apply (Permutation_in _ (Permutation_sym HPERM5)); apply in_or_app; right; exact Hin).
  assert (Hin3 : In (b, m) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym HPERM4)); apply in_or_app; right; exact Hin4).
  pose proof (al_blocks _ _ LAWS _ _ _ _ _ b m (proj1 HJ3) Hin3) as (_ & Hb4096 & Hbceil & _).
  pose proof (req_size_pos m ltac:(lia)) as (Hrq1 & Hrq2).
  assert (Hni : ~ in_img SEGS (b + i))
  by (exact (recb_heap_noimg B MT AF4 HB cmd_prog_img cmd_prog_writable
       ly3 S3 W3 (ms_mem ms0) _ b m (b + i) (proj1 HJ3) Hin3 ltac:(lia))).
  assert (Hnpg : ~ Exists (in_zr (b + i)) recb_PG)
  by (intros HP; apply Hni; exact (cmd_prog_img _ HP)).
  assert (Hng : ~ (A_G_REC <= b + i < A_G_REC + REC_SIZE))
  by (intros Hc; apply Hnpg; exact (recb_grec_in _ Hc)).
  assert (Hdisj5 : Exists (in_zr (b + i)) recb_PG \/
    exists bb mm, In (bb, mm) (ablocks B ly5 S5) /\ bb <= b + i < bb + req_size mm /\ ~ in_img SEGS (b + i))
  by (right; exists b, m; split; [exact Hin | split; [lia | exact Hni]]).
  assert (Hdisj4 : Exists (in_zr (b + i)) recb_PG \/
    exists bb mm, In (bb, mm) (ablocks B ly4 S4) /\ bb <= b + i < bb + req_size mm /\ ~ in_img SEGS (b + i))
  by (right; exists b, m; split; [exact Hin4 | split; [lia | exact Hni]]).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable Ef _ _ _ _ (b + i) HFr3 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2uf, ?EGuf' in Hw; unfold A_G_REC, REC_SIZE in *; lia|]). destruct Hr'. }
  rewrite (HKEEP6 (b + i) ltac:(lia) ltac:(unfold A_G_REC, REC_SIZE in *; lia) ltac:(lia)).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E5 _ _ _ _ (b + i) HFr2 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u4, ?EGu4' in Hw; unfold A_G_REC, REC_SIZE in *; lia|]). destruct Hr'. }
  rewrite (recb_free_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable ly4 S4 W4 (ms_mem ms1) _ W5 mem5 _ _ (l_reply Q) (ablocks B ly5 S5) (b + i)
    (proj1 HJ4) (recb_ablocks_nodup B MT AF4 HB cmd_prog_img cmd_prog_writable _ _ _ _ _ (proj1 HJ4)) HPERM5 HK5 Hdisj5).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E4 _ _ _ _ (b + i) HFr1 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u4, ?EGu4' in Hw; unfold A_G_REC, REC_SIZE in *; lia|]). destruct Hr'. }
  rewrite (recb_free_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable ly3 S3 W3 (ms_mem ms0) _ W4 mem4 _ _ (l_answer Q) (ablocks B ly4 S4) (b + i)
    (proj1 HJ3) (recb_ablocks_nodup B MT AF4 HB cmd_prog_img cmd_prog_writable _ _ _ _ _ (proj1 HJ3)) HPERM4 HK4 Hdisj4).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E3 _ _ _ _ (b + i) HFr0 ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u3, ?EGu3' in Hw; unfold A_G_REC, REC_SIZE in *; lia|]). destruct Hr'. }
  rewrite (HBLK1 b m i Hin3 Hi).
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable E _ _ _ _ (b + i) HFr ltac:(lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2u, ?EGu' in Hw; unfold A_G_REC, REC_SIZE in *; lia|]). destruct Hr'. }
  reflexivity. }
(* the sixteen bytes the runtime's memset wrote are zero at the return *)
assert (KRP : forall i, 0 <= i < 16 -> rdW W5 (ms_mem ms3) (A_G_REC + 928 + i) = Some 0).
{ intros i Hi.
  rewrite (recb_run_keeps B MT AF4 HB cmd_prog_img cmd_prog_writable Ef _ _ _ _
    (A_G_REC + 928 + i) HFr3 ltac:(unfold A_G_REC; lia)).
  2:{ intros (r & Hr' & Hw). vm_compute in Hr'.
      repeat (destruct Hr' as [Hr' | Hr']; [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
        rewrite ?E2uf, ?EGuf' in Hw; unfold A_G_REC in *; lia|]). destruct Hr'. }
  rewrite (HSET6 i Hi). reflexivity. }
assert (VREP : aval_mem (rdW W5 (ms_mem ms3)) (A_G_REC + OFF_REPLY) 8 0).
{ intros k Hk. replace (A_G_REC + OFF_REPLY + Z.of_nat k) with (A_G_REC + 928 + Z.of_nat k)
  by (unfold OFF_REPLY; lia). rewrite (KRP (Z.of_nat k) ltac:(lia)). rewrite le_byte_zero. reflexivity. }
assert (VRPS : aval_mem (rdW W5 (ms_mem ms3)) (A_G_REC + OFF_REPLY_SIZE) 8 0).
{ intros k Hk. replace (A_G_REC + OFF_REPLY_SIZE + Z.of_nat k) with (A_G_REC + 928 + (8 + Z.of_nat k))
  by (unfold OFF_REPLY_SIZE; lia). rewrite (KRP (8 + Z.of_nat k) ltac:(lia)). rewrite le_byte_zero. reflexivity. }
(* the return *)
eapply (RET W5 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
prreg HS (1%bv : bv 5) Rf1.
pose proof (st_ok_pi_region_nth Ef _ _ 1%nat _ HS eq_refl) as HRnc. cbn [ms_mem restrict] in HRnc.
pose proof (st_ok_pi_region_nth Ef _ _ 2%nat _ HS eq_refl) as HRan. cbn [ms_mem restrict] in HRan.
pose proof (st_ok_pi_region_nth Ef _ _ 3%nat _ HS eq_refl) as HRnr. cbn [ms_mem restrict] in HRnr.
pose proof (field_of_region_any Ef _ A_GREC A_G_REC _ _ _ _ _ 8 4 (SLit 0) HRnc EGuf
  ltac:(cbn; tauto) ltac:(cbn; lia)) as F8.
pose proof (field_of_region_any Ef _ A_GREC A_G_REC _ _ _ _ _ 912 8 (SLit 0) HRan EGuf
  ltac:(cbn; tauto) ltac:(cbn; lia)) as F912.
pose proof (field_of_region_any Ef _ A_GREC A_G_REC _ _ _ _ _ 920 4 (SLit 0) HRnr EGuf
  ltac:(cbn; tauto) ltac:(cbn; lia)) as F920.
assert (DZ4 : bv_unsigned (sv_denot Ef (SLit 0)) mod 2 ^ (8 * Z.of_N 4) = 0)
by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity).
assert (DZ8 : bv_unsigned (sv_denot Ef (SLit 0)) mod 2 ^ (8 * Z.of_N 8) = 0)
by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; reflexivity).
rewrite DZ4 in F8. rewrite DZ8 in F912. rewrite DZ4 in F920.
assert (Hra1' : getr (ms_regs ms3) 1 = getr regs 1)
by (rewrite Rf1, OLDf, OLD5, OLD4, OLD3 by lia; exact (EEo 1%nat 1%bv eq_refl)).
pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
(* the recorder's state at the return: RecModel.rec_clear R over the spill's blocks *)
assert (HNDs : List.NoDup (map fst (l_spill Q) ++ map fst (oblk (l_answer Q) ++ oblk (l_reply Q)))).
{ pose proof (proj1 HOWN) as HND. apply NoDup_ListNoDup in HND. unfold lay_blocks in HND.
  rewrite map_app in HND. apply (List.NoDup_app_remove_l _ _) in HND. rewrite map_app in HND. exact HND. }
assert (Hspill5 : forall pn, In pn (l_spill Q) -> In pn (ablocks B ly5 S5)).
{ intros pn Hpn.
  assert (Hin3 : In pn (ablocks B ly3 S3)) by (apply Hoth; apply in_or_app; left; exact Hpn).
  destruct (in_app_or _ _ _ (Permutation_in _ HPERM4 Hin3)) as [H | H4].
  - exfalso. exact (list_nodup_app_disj _ _ (fst pn) HNDs (in_map fst _ _ Hpn)
      (in_map fst _ _ (in_or_app _ _ _ (or_introl H)))).
  - destruct (in_app_or _ _ _ (Permutation_in _ HPERM5 H4)) as [H | H5]; [|exact H5].
    exfalso. exact (list_nodup_app_disj _ _ (fst pn) HNDs (in_map fst _ _ Hpn)
      (in_map fst _ _ (in_or_app _ _ _ (or_intror H)))). }
assert (HSPILL : acall_at (ablocks B ly5 S5) (rdW W5 (ms_mem ms3)) A_REC_SPILL (r_spill R) (l_spill Q)).
{ apply (acall_at_bl (ablocks B ly S)).
  - apply (acall_at_kept (ablocks B ly S) (rdW W mem)); [exact HSP | |].
    + intros j Hj. apply KPG; [apply recb_spill_in; unfold A_REC_SPILL, SC_SIZE, CALL_OFF_ARGS in *;
        destruct HSP as (_ & Hle6 & _); lia
      | unfold A_G_REC, A_REC_SPILL, CALL_OFF_ARGS in *; destruct HSP as (_ & Hle6 & _); lia
      | unfold A_G_REC, A_REC_SPILL, CALL_OFF_ARGS in *; destruct HSP as (_ & Hle6 & _); lia
      | unfold A_G_REC, A_REC_SPILL, CALL_OFF_ARGS in *; destruct HSP as (_ & Hle6 & _); lia
      | unfold A_G_REC, A_REC_SPILL, CALL_OFF_ARGS in *; destruct HSP as (_ & Hle6 & _); lia].
    + intros [pp pq] ii Hpn Hii. apply (KBL pp pq ii); [exact (Hspill5 (pp, pq) Hpn) | exact Hii].
  - exact Hspill5. }
assert (HSC : ag1_scalars (rdW W5 (ms_mem ms3)) A_G_REC (RecModel.rec_clear R)).
{ destruct HSCAL as (Vrf2 & Vcd2 & Vnr2 & Vst2 & Vho2 & Rrf2 & Rcd2 & Rnr3 & Rst2 & Rho2).
  unfold RecModel.rec_clear, ag1_scalars. cbn [r_refuse r_code r_nreplies r_state r_host].
  split; [apply (aval_mem_kept (rdW W mem)); [exact Vrf2|]|].
  { intros k Hk. apply KPG; [apply recb_grec_in; unfold OFF_REFUSE, REC_SIZE; lia
    | unfold OFF_REFUSE; lia | unfold OFF_REFUSE; lia | unfold OFF_REFUSE; lia | unfold OFF_REFUSE; lia]. }
  split; [apply (aval_mem_kept (rdW W mem)); [exact Vcd2|]|].
  { intros k Hk. apply KPG; [apply recb_grec_in; unfold OFF_CODE, REC_SIZE; lia
    | unfold OFF_CODE; lia | unfold OFF_CODE; lia | unfold OFF_CODE; lia | unfold OFF_CODE; lia]. }
  split; [exact (aval_mem_view SEGS _ _ _ _ _ F920)|].
  split; [apply (aval_mem_kept (rdW W mem)); [exact Vst2|]|].
  { intros k Hk. apply KPG; [apply recb_grec_in; unfold OFF_STATE, REC_SIZE; lia
    | unfold OFF_STATE; lia | unfold OFF_STATE; lia | unfold OFF_STATE; lia | unfold OFF_STATE; lia]. }
  split; [apply (aval_mem_kept (rdW W mem)); [exact Vho2|]|].
  { intros k Hk. apply KPG; [apply recb_grec_in; unfold OFF_HOST, REC_SIZE; lia
    | unfold OFF_HOST; lia | unfold OFF_HOST; lia | unfold OFF_HOST; lia | unfold OFF_HOST; lia]. }
  repeat split; first [assumption | lia]. }
assert (HREPF : rec_repA B ly5 S5 (rdW W5 (ms_mem ms3)) (RecModel.rec_clear R) (l_spill Q)).
{ exists (RLay [] (l_spill Q) None None). split.
  - split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
    split.
    { unfold RecModel.rec_clear, ag1_calls. cbn [r_calls l_calls r_spill l_spill length].
      split; [lia|]. split; [reflexivity|].
      split; [cbn [length]; exact (aval_mem_view SEGS _ _ _ _ _ F8)|].
      split; [intros i c P Hc; cbn [nth_error] in Hc; destruct i; discriminate|].
      split; [exact HSPILL | exact HSPL]. }
    split; [unfold RecModel.rec_clear; cbn [r_answer l_answer aanswer_at];
      exact (aval_mem_view SEGS _ _ _ _ _ F912)|].
    split; [unfold RecModel.rec_clear; cbn [r_reply l_reply areply_at]; split; [exact VREP | exact VRPS]|].
    split; [exact HSC|].
    destruct HOWN as (HND & HAP). split.
    + unfold lay_blocks. cbn [concat l_calls l_spill l_answer l_reply oblk app].
      rewrite app_nil_r. apply NoDup_ListNoDup. apply NoDup_ListNoDup in HND.
      unfold lay_blocks in HND. rewrite !map_app in HND.
      apply (List.NoDup_app_remove_l _ _) in HND. exact (List.NoDup_app_remove_r _ _ HND).
    + intros pn Hpn. apply HAP. unfold lay_blocks in *.
      cbn [concat l_calls l_spill l_answer l_reply oblk app] in Hpn. rewrite app_nil_r in Hpn.
      apply in_or_app. right. apply in_or_app. left. exact Hpn.
  - intros pn. unfold lay_blocks. cbn [concat l_calls l_spill l_answer l_reply oblk app].
    rewrite app_nil_r. reflexivity. }
(* the post *)
unfold apost_base. eexists ly5, S5, (ms_regs ms3), (ms_mem ms3), _.
split; [rewrite Hra1', Hra'; reflexivity|].
split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_REC_CALLS_FREE (l_calls Q) + 1 + 1);
  [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ6
  | unfold EV_REC_CLEAR, EV_REC_CALLS_FREE; rewrite HEVA; lia]|].
split; [exact (aregs_preserved_of_st_ok SEGS (w_H W5) Ef _ ms3 regs
  (rc_extra (Z.of_nat (length (r_calls R))) an (r_nreplies R) rp) HS HAEf ltac:(vm_compute; reflexivity))|].
exists (l_spill Q), (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)).
split; [exact HREPF|].
split; [intros pn Hpn; apply HOQ; unfold lay_blocks; apply in_or_app; right; apply in_or_app; left; exact Hpn|].
split.
{ intros pn. split.
  - intros Hpn. assert (HinQ : In pn (lay_blocks Q)).
    { unfold lay_blocks. apply in_app_or in Hpn as [H | H]; [apply in_or_app; left; exact H|].
      apply in_or_app; right; apply in_or_app; right; exact H. }
    split; [apply HOQ; exact HinQ|]. intros Hsp.
    assert (HNDc : List.NoDup (map fst (concat (l_calls Q)) ++
      map fst (l_spill Q ++ oblk (l_answer Q) ++ oblk (l_reply Q)))).
    { pose proof (proj1 HOWN) as HND. apply NoDup_ListNoDup in HND. unfold lay_blocks in HND.
      rewrite map_app in HND. exact HND. }
    apply in_app_or in Hpn as [H | H].
    + exact (list_nodup_app_disj _ _ (fst pn) HNDc (in_map fst _ _ H)
        (in_map fst _ _ (in_or_app _ _ _ (or_introl Hsp)))).
    + exact (list_nodup_app_disj _ _ (fst pn) HNDs (in_map fst _ _ Hsp) (in_map fst _ _ H)).
  - intros (HpO & Hnsp). apply HOQ in HpO. unfold lay_blocks in HpO.
    apply in_app_or in HpO as [H | H]; [apply in_or_app; left; exact H|].
    apply in_app_or in H as [H | H]; [contradiction|]. apply in_or_app; right; exact H. }
assert (HPERMF : Permutation (ablocks B ly S) (ablocks B ly5 S5 ++
  (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q)))).
{ assert (Hp4 : forall (Pa1 Pr1 Pl1 Pc1 : list (Z * Z)), Permutation ((Pa1 ++ (Pr1 ++ Pl1)) ++ Pc1) (Pl1 ++ (Pc1 ++ Pa1 ++ Pr1))).
  { intros Pa1 Pr1 Pl1 Pc1. rewrite <- !app_assoc.
    apply (Permutation_trans (Permutation_app_comm Pa1 (Pr1 ++ Pl1 ++ Pc1))). rewrite <- !app_assoc.
    apply (Permutation_trans (Permutation_app_comm Pr1 (Pl1 ++ Pc1 ++ Pa1))). rewrite <- !app_assoc.
    apply Permutation_refl. }
  apply (Permutation_trans HPERM1).
  apply (Permutation_trans (Permutation_app_tail (concat (l_calls Q)) HPERM4)).
  apply (Permutation_trans (Permutation_app_tail (concat (l_calls Q))
    (Permutation_app_head (oblk (l_answer Q)) HPERM5))).
  apply Hp4. }
split; [exact HPERMF|].
split.
{ unfold LIVE_REC_CLEAR. rewrite (blocks_bytes_bsum B ly S), (blocks_bytes_bsum B ly5 S5).
  rewrite (bsum_perm _ _ HPERMF), bsum_app.
  assert (HD0 : forall l, (forall pn, In pn l -> In pn (ablocks B ly S)) -> 0 <= bsum l).
  { induction l as [|x l IH]; intros Hl; [cbn; lia|]. rewrite bsum_cons.
    destruct x as [p n]. destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR (Hl (p, n) (or_introl eq_refl)))
      as (_ & _ & _ & _ & _ & _ & Hn). cbn [snd].
    assert (0 <= bsum l) by (apply IH; intros pn Hpn; exact (Hl pn (or_intror Hpn))). lia. }
  assert (0 <= bsum (concat (l_calls Q) ++ oblk (l_answer Q) ++ oblk (l_reply Q))); [|lia].
  apply HD0. intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERMF)). apply in_or_app. right. exact Hpn. }
apply (mo_le_mono MT MTL S S5 (XM_REC_CALLS_FREE MT (l_calls Q) + mo_free MT + mo_free MT)
  (XM_REC_CLEAR MT R) (mle_station MT S S4 S5 _ _ MTL HMLE14 HMLE5)).
unfold XM_REC_CALLS_FREE, XM_REC_CLEAR. rewrite HEVA. nia.
Qed.

End e.
End f.
End d.
