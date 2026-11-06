(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACep.v, with its module paths and module names changed; 1031 of its 1086 lines of code are new or changed and 171 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_op4find.v, with its module paths and module names changed; 1761 of its 1872 lines of code are new or changed and 975 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4st: segment OP4ST of the image-B walk of fuzz_transport.asan-ubsan's
   LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_op4st_stmt): from the cut CMDW (+0x14cc, op 4
   after the calls of diginet_session_submit, check_refusal_submit and check_latest_submit) to the cut S4 (+0x1654,
   op 4's call of settle).

   The code (offsets from the entry 0x812a0; the listing lib/B/Prog/DgnTransportBList.v):
     +0x14cc          `bnez s6`: want <> 0 goes to +0x1634;
     +0x14d0 .. +0x1558  want = 0: serial (64(s1)) and its UBSan index test (`beq a1, a0` with a0 = 1024, trap edge
                      0x8277c), the pointer g_cmd + 40 serial (0(s1)) and its null test (`beqz a5`, trap edge 0x82780),
                      the four checked stores of g_cmd[serial]'s st (1), key (c + 28), display (c + 25) and len (c + 24,
                      one byte) with their slow paths +0x17cc .. +0x1804 and reports +0x1d08 .. +0x1d18, and the call of
                      __asan_memcpy (g_cmd[serial] + 12, c, len) at +0x1558;
     +0x155c .. +0x1560  `sext.w a0, s9; bltz a0`: at < 0 goes to the append;
     +0x1564 .. +0x15d8  the replace: g_q + 4 at (trap edge 0x82814 on its wrap), the checked load of g_q[at]
                      (slow path +0x182c .. +0x1838, report +0x1d2c), its index test (trap edge 0x82834), g_cmd + 40
                      g_q[at] (trap edge 0x82844), the checked store of 3 at its st (slow path +0x183c .. +0x1848, report
                      +0x1d34), the shadow test of the store g_q[at] (+0x15c4 .. +0x15d4, report +0x1c5c);
     +0x15e8 .. +0x1624  the append: g_nq + 1 (plain load and store), the index test of the old g_nq (trap edge
                      0x8289c), g_q + 4 g_nq (trap edge 0x828b0), the shadow test of the store g_q[g_nq] (slow path
                      +0x184c .. +0x1858, report +0x1d38);
     +0x1628 .. +0x1630  g_q[at or old g_nq] = serial, s4 = c (144(s1));
     +0x1634 .. +0x1650  g_ncmd + 1 (plain), s11 = the bytes left after the take (16(s1) - 8(s1)), s6 = 1.

   The walk is a G-form walk: the runs are lib/A/Prog/PaShadow.v's token runs over the caller's G journal
   (lib/B/Prog/TransportGRunB.v paj_run_x / paj_run_to_x), the call by lib/A/Prog/TransportGCg.v gx_intrin_at. The
   token engine decides every checked access from the shadow entries of the runs (g_cmd[serial], g_q[at or g_nq],
   g_cmd[g_q[at]]: zero-shadow payloads, lib/B/Prog/settle_cg.v trans_settle_cells), so none of the eight
   __asan_report_* calls (0x82efc, 0x82fac, 0x82fb0, 0x82fb4, 0x82fb8, 0x82fcc, 0x82fd4, 0x82fd8) is reached. Of the
   seven branches to the UBSan trap word 0x82de4, the engine decides 0x8277c (serial in [0, 1023]), 0x82780 (the
   pointer's range), 0x82834 (g_q[at] in [0, 1023]) and 0x8289c (g_nq in [0, 1023]) from the atoms' facts; the walk
   splits 0x82814, 0x82844 and 0x828b0 (the pointer wraps: ~g_q < 4 at, ~g_cmd < 40 g_q[at], ~g_q < 4 g_nq) and
   refutes each taken side (o4_trap_q, o4_trap_c).

   The model (TOps.v op_submit_m, tagged mode, after check_latest_submit): LLVMFuzzerTestOneInput_seg_op4st_m.v
   o4_model; the world after the stores is o4_b7 (o4_b6 B5 (o4_cmdw B5 ..) want at serial), related to the memory by
   o4_w_ncmd / o4_w_cmd / o4_w_rep / o4_w_app.

   The cuts' state facts (lc_lcore) carry over each stretch by o4_lcore_keep (every byte outside G and outside the
   callee's window below sp1 is kept). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB settle_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st LLVMFuzzerTestOneInput_seg_op4st_m.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TCb TSess0 TSess TOps TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require Agree QueueFacts LoopOk LinksProof.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module AG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.Agree.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module FCells := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The symbolic states                                              *)
(* ------------------------------------------------------------------ *)

(* The return of __asan_memcpy, and the two points where a computed address of G becomes an atom: g_q + 4 at (or
   g_q + 4 g_nq) in a0, g_cmd + 40 g_q[at] in a1. *)
Definition LO_RCPY : Z := 0x155c.
Definition LO_GQ : Z := 0x157c.
Definition LO_GC : Z := 0x15ac.
Definition LO_GQA : Z := 0x1618.

(* The pages of g_nq and g_ncmd the spill slots 32(s1) and 56(s1) hold (segs.v lf_spill_pages). *)
Definition O4_H14 : Z := 0x5df784.
Definition O4_H15 : Z := 0x5df788.

(* Atoms: 0 .. 31 the registers at the cut, then 32 g_cmd + 40 serial (0(s1)), 33 the take's length (8(s1)), 34 the
   bytes left before the take (16(s1)), 35 serial (64(s1)), 36 c.key, 37 c.display, 38 c.len, 39 g_ncmd, 40 g_nq,
   41 g_q + 4 at (or g_q + 4 g_nq), 42 g_q[at], 43 g_cmd + 40 g_q[at]. *)
Definition o4_extra (gc tn fin serial key disp len ncmd nq x41 q x43 : Z) : list word :=
  [w64 gc; w64 tn; w64 fin; w64 serial; w64 key; w64 disp; w64 len; w64 ncmd; w64 nq; w64 x41; w64 q; w64 x43].

(* CMDW: the spill slots the segment reloads (read only), c's len, display and key (read only). *)
Definition o4_rg_sp1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 152 0 0
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
   YP09.mkChunk 32 (CVal 8 (SLit O4_H14)); YP09.mkChunk 56 (CVal 8 (SLit O4_H15));
   YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 144 (CVal 8 (SOff 20 0))].
Definition o4_rg_c : YP09.region := YP09.mkRegion (Some 20%nat) 24 32 0 0
  [YP09.mkChunk 24 (CVal 1 (SOff 38 0)); YP09.mkChunk 25 (CVal 1 (SOff 37 0)); YP09.mkChunk 28 (CVal 4 (SOff 36 0))].
(* g_cmd[serial]'s st, key, display [0, 12) and len [36, 37) (written when want = 0); g_ncmd (written), g_nq. *)
Definition o4_rg_cmda : YP09.region := YP09.mkRegion (Some 32%nat) 0 12 0 12 [].
Definition o4_rg_cmdb : YP09.region := YP09.mkRegion (Some 32%nat) 36 37 36 37 [].
Definition o4_rg_ncmd : YP09.region := YP09.mkRegion None TB_g_ncmd (TB_g_ncmd + 4) TB_g_ncmd (TB_g_ncmd + 4)
  [YP09.mkChunk TB_g_ncmd (CVal 4 (SOff 39 0))].
Definition o4_rg_nq : YP09.region := YP09.mkRegion None TB_g_nq (TB_g_nq + 4) TB_g_nq (TB_g_nq + 4)
  [YP09.mkChunk TB_g_nq (CVal 4 (SOff 40 0))].
Definition O4_PSP : afact := mkAF (CEIL_MIN + 32432) (2 ^ 47) 5.
Definition o4_facts1 : facts :=
  mkFacts [(2%nat, O4_PSP); (9%nat, O4_PSP); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (20%nat, mkAF 4096 CEIL_MAX 5);
           (32%nat, mkAF TB_g_cmd (TB_g_cmd + 40 * 1023) 3); (35%nat, mkAF 0 1023 0);
           (36%nat, mkAF 0 (2 ^ 32 - 1) 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0)] [] [].
Definition o4_ss1 : sstate := mkSS LO_CMDW sr_atoms [o4_rg_sp1; o4_rg_c] None o4_facts1.
Definition O4_Bx : sv := SOff 26 0.
Definition O4_SH1 : list shent := [mkSHE 32 0 40].

(* RCPY: the spill slots, g_ncmd; s9 = at mod 2 ^ 32 in [alo, ahi]; g_nq in [nlo, nhi]. *)
Definition o4_rg_sp2 : YP09.region := YP09.mkRegion (Some 9%nat) 0 152 0 0
  [YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
   YP09.mkChunk 32 (CVal 8 (SLit O4_H14)); YP09.mkChunk 56 (CVal 8 (SLit O4_H15));
   YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 144 (CVal 8 (SOff 20 0))].
Definition o4_facts2 (alo ahi nlo nhi : Z) : facts :=
  mkFacts [(2%nat, O4_PSP); (9%nat, O4_PSP); (26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (20%nat, mkAF 4096 CEIL_MAX 5);
           (27%nat, mkAF TB_g_cmd TB_g_cmd 6); (25%nat, mkAF alo ahi 0); (A_OBJ 21, mkAF TB_g_q TB_g_q 6);
           (35%nat, mkAF 0 1023 0); (40%nat, mkAF nlo nhi 0)] [] [].
Definition o4_ss2 (alo ahi nlo nhi : Z) (rs : smem) : sstate :=
  mkSS LO_RCPY sr_atoms rs None (o4_facts2 alo ahi nlo nhi).
(* g_q's cell at atom 41 (holding atom 42 on the replace), g_cmd[g_q[at]].st at atom 43. *)
Definition o4_rg_q (cs : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 41%nat) 0 4 0 4 cs.
Definition o4_rg_k : YP09.region := YP09.mkRegion (Some 43%nat) 0 4 0 4 [].
Definition O4_SHQ : list shent := [mkSHE 41 0 4].
Definition O4_SHK : list shent := [mkSHE 41 0 4; mkSHE 43 0 4].

Section mach. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

Definition o4_E (regs : bvmap 5 word) (gc tn fin serial key disp len ncmd nq x41 q x43 : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs (o4_extra gc tn fin serial key disp len ncmd nq x41 q x43)).

Lemma o4_vals : VAL (A_OBJ 21) = TB_g_q /\ BASE = transportb_text /\ O4_H14 = transportb_hi 14 /\
  O4_H15 = transportb_hi 15 /\ O4_H14 - 0x1a4 = TB_g_nq /\ O4_H15 - 0x188 = TB_g_ncmd.
Proof. vm_compute. repeat split. Qed.

Lemma o4_ew_x : forall regs gc tn fin serial key disp len ncmd nq x41 q x43 j, (j < 12)%nat ->
  ew (o4_E regs gc tn fin serial key disp len ncmd nq x41 q x43) (32 + j) =
  nth j (o4_extra gc tn fin serial key disp len ncmd nq x41 q x43) (Z_to_bv 64 0).
Proof.
intros regs gc tn fin serial key disp len ncmd nq x41 q x43 j Hj. unfold o4_E.
rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.

Lemma o4_ew_r : forall regs gc tn fin serial key disp len ncmd nq x41 q x43 n (r : bv 5),
  Z.of_nat n = bv_unsigned r -> ew (o4_E regs gc tn fin serial key disp len ncmd nq x41 q x43) n = YK11.getr regs r.
Proof. intros. unfold o4_E. apply ew_Eimg_Ereg_nat. assumption. Qed.

Lemma o4_env_img : forall regs gc tn fin serial key disp len ncmd nq x41 q x43,
  img_env VAL A_LIM (o4_E regs gc tn fin serial key disp len ncmd nq x41 q x43).
Proof. intros. unfold o4_E. apply Eimg_env. Qed.

Lemma o4_ew_obj : forall regs gc tn fin serial key disp len ncmd nq x41 q x43 i, (i < 97)%nat ->
  ew (o4_E regs gc tn fin serial key disp len ncmd nq x41 q x43) (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)).
Proof. intros. unfold o4_E. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM. lia. Qed.

(* An atom holding w64 v, 0 <= v < 2 ^ 64. *)
Lemma o4_U : forall E n v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* A chunk of an 8-byte spill slot, from rdword. *)
Lemma o4_chunk8 : forall E (m : word -> option byte) H base off e v,
  sv_denot E e = w64 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H m) (base + off) = Some v ->
  YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E m H base off e v He Hv Hr.
apply (chunk_ok_val segs E _ base off 8 e v); [exact He | exact Hv | cbn; lia | exact (val_mem_of_rdword segs _ _ _ _ Hr)].
Qed.

(* A chunk of w <= 8 bytes from a val_mem fact. *)
Lemma o4_chunkv : forall E (m : word -> option byte) base off (w : N) e v,
  sv_denot E e = w64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> (w <= 8)%N ->
  YI04.val_mem segs m (base + off) (N.to_nat w) v ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v He Hv Hw V.
assert (Hv64 : 0 <= v < 2 ^ 64).
{ split; [lia|]. apply (Z.lt_le_trans _ (2 ^ (8 * Z.of_N w))); [lia|]. apply Z.pow_le_mono_r; lia. }
apply (chunk_ok_val segs E _ base off w e v); [exact He | exact Hv | lia | exact V].
Qed.

(* A word the view reads is below 2 ^ 64. *)
Lemma o4_rdword_range : forall H (m : word -> option byte) a v, rdword (aview segs H m) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H m a v Hr. unfold rdword in Hr.
assert (BY : forall x, match aview segs H m x with Some b => 0 <= b < 256 | None => True end).
{ intros x. change (aview segs H m x) with (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H m) x)).
  destruct (YP09.mbyte segs (mrestrict H m) x) as [b|]; cbn [option_map]; [|exact I].
  pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
pose proof (BY a) as B0. pose proof (BY (a + 1)) as B1. pose proof (BY (a + 2)) as B2. pose proof (BY (a + 3)) as B3.
pose proof (BY (a + 4)) as B4. pose proof (BY (a + 5)) as B5. pose proof (BY (a + 6)) as B6. pose proof (BY (a + 7)) as B7.
destruct (aview segs H m a); [|discriminate Hr]. destruct (aview segs H m (a + 1)); [|discriminate Hr].
destruct (aview segs H m (a + 2)); [|discriminate Hr]. destruct (aview segs H m (a + 3)); [|discriminate Hr].
destruct (aview segs H m (a + 4)); [|discriminate Hr]. destruct (aview segs H m (a + 5)); [|discriminate Hr].
destruct (aview segs H m (a + 6)); [|discriminate Hr]. destruct (aview segs H m (a + 7)); [|discriminate Hr].
injection Hr as <-. lia.
Qed.

(* The view of a byte val_mem fixes. *)
Lemma o4_aview_of_val : forall H (m : word -> option byte) a n v k,
  YI04.val_mem segs (mrestrict H m) a n v -> (k < n)%nat -> aview segs H m (a + Z.of_nat k) = Some (YO0f.le_byte v n k).
Proof.
intros H m a n v k V Hk.
change (aview segs H m (a + Z.of_nat k)) with
  (option_map (fun b : byte => bv_unsigned b) (YP09.mbyte segs (mrestrict H m) (a + Z.of_nat k))).
rewrite (V k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. change (2 ^ 8) with 256.
apply Z.mod_pos_bound. lia.
Qed.

Lemma o4_le_mod : forall x (n k : nat), YO0f.le_byte (x mod 2 ^ (8 * Z.of_nat n)) n k = YO0f.le_byte x n k.
Proof. intros x n k. unfold YO0f.le_byte. rewrite Zmod_mod. reflexivity. Qed.

Lemma o4_le_eqv : forall x y (n k : nat), x mod 2 ^ (8 * Z.of_nat n) = y mod 2 ^ (8 * Z.of_nat n) ->
  YO0f.le_byte x n k = YO0f.le_byte y n k.
Proof. intros x y n k H. unfold YO0f.le_byte. rewrite H. reflexivity. Qed.

(* The bytes of a chunk, through the view, as the bytes of a value x it agrees with. *)
Lemma o4_chunk_bytes : forall E H (m : word -> option byte) base od (w : N) (wn : nat) e x,
  YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk od (CVal w e)) -> Z.of_N w = Z.of_nat wn -> (wn <= 8)%nat ->
  bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_nat wn) = x mod 2 ^ (8 * Z.of_nat wn) ->
  forall k, (k < wn)%nat -> aview segs H m (base + od + Z.of_nat k) = Some (YO0f.le_byte x wn k).
Proof.
intros E H m base od w wn e x HC Hw Hwn Hx k Hk.
pose proof (val_of_chunk_any segs E (mrestrict H m) base od w e HC ltac:(lia)) as V.
assert (Ew : N.to_nat w = wn) by lia. rewrite Ew in V.
replace (8 * Z.of_N w) with (8 * Z.of_nat wn) in V by lia.
rewrite (o4_aview_of_val H m (base + od) wn _ k V Hk). f_equal.
rewrite o4_le_mod. apply o4_le_eqv. exact Hx.
Qed.

(* x mod (c * d) mod c, x mod 2 ^ 64 mod 2 ^ 32 and the 32-bit signed wrap. *)
Lemma o4_mod_mul : forall x c d, 0 < c -> 0 < d -> x mod (c * d) mod c = x mod c.
Proof.
intros x c d Hc Hd. rewrite (Z.mod_eq x (c * d)) by lia.
replace (x - c * d * (x / (c * d))) with (x + (- (d * (x / (c * d)))) * c) by ring. apply Z_mod_plus_full.
Qed.
Lemma o4_mod64_32 : forall x, x mod 2 ^ 64 mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity. apply o4_mod_mul; lia. Qed.
Lemma o4_swrap32 : forall x, bv_swrap 32 x mod 2 ^ 32 = x mod 2 ^ 32.
Proof. intros x. unfold bv_swrap, bv_wrap, bv_modulus, bv_half_modulus. rewrite Zminus_mod_idemp_l. f_equal. lia. Qed.
Lemma o4_mod64_w : forall x (w : nat), (w <= 8)%nat -> x mod 2 ^ 64 mod 2 ^ (8 * Z.of_nat w) = x mod 2 ^ (8 * Z.of_nat w).
Proof.
intros x w Hw. replace (2 ^ 64) with (2 ^ (8 * Z.of_nat w) * 2 ^ (64 - 8 * Z.of_nat w))
  by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
apply o4_mod_mul; apply Z.pow_pos_nonneg; lia.
Qed.

(* lw (sign-extended), + 1, sw: the 4 bytes of (v + 1). *)
Lemma o4_den_inc : forall E (n : nat) v, bv_unsigned (ew E n) = v ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))) mod 2 ^ (8 * Z.of_nat 4) =
  (v + 1) mod 2 ^ (8 * Z.of_nat 4).
Proof.
intros E n v Hv. change (8 * Z.of_nat 4) with 32.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))))
  with (U E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))).
rewrite U_SAlu, U_SExt, U_SOff, U_SLit. cbn [zalu_raw]. rewrite Hv. unfold zcanon, M64.
change (Z.of_N 32) with 32. rewrite !o4_mod64_32.
rewrite Zplus_mod, o4_mod64_32, o4_swrap32, o4_mod64_32, Z.add_0_r, Zmod_mod, <- Zplus_mod.
rewrite (Zplus_mod v 1), <- (Zplus_mod v 1). reflexivity.
Qed.

(* lw (sign-extended), sw: the 4 bytes of v. *)
Lemma o4_den_sext : forall E (n : nat) v, bv_unsigned (ew E n) = v ->
  bv_unsigned (sv_denot E (SExt true 32 (SOff n 0))) mod 2 ^ (8 * Z.of_nat 4) = v mod 2 ^ (8 * Z.of_nat 4).
Proof.
intros E n v Hv. change (8 * Z.of_nat 4) with 32.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite U_SExt, U_SOff. rewrite Hv. unfold zcanon, M64. change (Z.of_N 32) with 32.
rewrite o4_mod64_32, o4_swrap32, Zmod_mod, Z.add_0_r, o4_mod64_32. reflexivity.
Qed.

Lemma o4_den_off : forall E (n : nat) v (w : nat) z, bv_unsigned (ew E n) = v -> (w <= 8)%nat ->
  bv_unsigned (sv_denot E (SOff n z)) mod 2 ^ (8 * Z.of_nat w) = (v + z) mod 2 ^ (8 * Z.of_nat w).
Proof.
intros E n v w z Hv Hw. cbn [sv_denot]. rewrite Hv, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact (o4_mod64_w (v + z) w Hw).
Qed.
Lemma o4_den_lit : forall E z (w : nat), (w <= 8)%nat ->
  bv_unsigned (sv_denot E (SLit z)) mod 2 ^ (8 * Z.of_nat w) = z mod 2 ^ (8 * Z.of_nat w).
Proof.
intros E z w Hw. cbn [sv_denot]. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). exact (o4_mod64_w z w Hw).
Qed.

(* s11 = 16(s1) - 8(s1) at the end of the segment. *)
Lemma o4_den_sub : forall E (x y : nat) a b, ew E x = w64 a -> ew E y = w64 b ->
  sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0)) = w64 (a - b).
Proof.
intros E x y a b Ha Hb. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0))))
  with (U E (SAlu ALU_ADD (SMd M_MUL (SOff y 0) (SLit (-1))) (SOff x 0))).
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite Ha, Hb. unfold w64, zcanon, M64.
rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.add_0_r.
repeat rewrite ?Zmod_mod, ?Zplus_mod_idemp_l, ?Zplus_mod_idemp_r, ?Zmult_mod_idemp_l, ?Zmult_mod_idemp_r.
rewrite <- (Zplus_mod_idemp_l (b mod 2 ^ 64 * (-1 mod 2 ^ 64))), <- Zmult_mod, Zplus_mod_idemp_l.
f_equal. ring.
Qed.

(* `bnez s6` on want. *)
Lemma o4_br_want : forall E want, ew E 22 = w64 want -> (want = 0 \/ want = -10 \/ want = -5) ->
  branch_taken BC_NE (sv_denot E (SOff 22 0)) (sv_denot E (SLit 0)) = negb (want =? 0).
Proof.
intros E want H Hw. cbn [sv_denot]. rewrite H, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
destruct Hw as [-> | [-> | ->]]; vm_compute; reflexivity.
Qed.

(* The three pointer-wrap tests to the trap word: ~g_q < 4 i (i < 1024) and ~g_cmd < 40 q (q < 1024) never hold. *)
Lemma o4_trap_q : forall E (n : nat) i, ew E (A_OBJ 21) = Z_to_bv 64 TB_g_q -> ew E n = w64 i -> 0 <= i < 1024 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff (A_OBJ 21) 0) (SLit (-1))))
    (sv_denot E (SAlu ALU_SLL (SOff n 0) (SLit 2))) = false.
Proof.
intros E n i HQ Hn Hi. rewrite branch_ltu_U. apply Z.ltb_ge.
rewrite !U_SAlu, !U_SOff, !U_SLit. rewrite HQ, Hn. unfold w64.
rewrite !unsigned_lit_small by (unfold TB_g_q; lia). rewrite !Z.add_0_r.
cbn [zalu_raw]. change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
replace (zcanon (Z.lxor (zcanon TB_g_q) (zcanon (-1)))) with 18446744073703319423 by (vm_compute; reflexivity).
unfold zcanon, M64. rewrite (Z.mod_small i) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma o4_trap_c : forall E (n : nat) q, ew E 27 = w64 TB_g_cmd -> ew E n = w64 q -> 0 <= q < 1024 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 27 0) (SLit (-1))))
    (sv_denot E (SMd M_MUL (SOff n 0) (SLit 40))) = false.
Proof.
intros E n q HC Hn Hq. rewrite branch_ltu_U. apply Z.ltb_ge.
rewrite U_SAlu, U_SMd, !U_SOff, !U_SLit. rewrite HC, Hn. unfold w64.
rewrite !unsigned_lit_small by (unfold TB_g_cmd; lia). rewrite !Z.add_0_r.
cbn [zalu_raw zmd_raw].
replace (zcanon (Z.lxor (zcanon TB_g_cmd) (zcanon (-1)))) with 18446744073703370623 by (vm_compute; reflexivity).
unfold zcanon, M64. repeat (rewrite Z.mod_small by lia). lia.
Qed.

(* `sext.w a0, s9; bltz a0` with s9 = 0xffffffff (at = -1): taken. *)
Lemma o4_br_app : forall E, ew E 25 = w64 (2 ^ 32 - 1) ->
  branch_taken BC_LT (sv_denot E (SAluw ALU_ADD (SOff 25 0) (SLit 0))) (sv_denot E (SLit 0)) = true.
Proof. intros E H. cbn [sv_denot]. rewrite H. vm_compute. reflexivity. Qed.

(* The addresses g_q + 4 i (`slli; auipc/addi; add`) and g_cmd + 40 q (`mul; add` with s11 = g_cmd). *)
Lemma o4_den_gq : forall E (n : nat) i, ew E (A_OBJ 21) = Z_to_bv 64 TB_g_q -> ew E n = w64 i -> 0 <= i < 1024 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff (A_OBJ 21) 0)) = w64 (TB_g_q + 4 * i).
Proof.
intros E n i HQ Hn Hi. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff (A_OBJ 21) 0))))
  with (U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SOff (A_OBJ 21) 0))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, HQ. unfold w64.
rewrite !unsigned_lit_small by (unfold TB_g_q; lia).
change (Z.land (zcanon 2) 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64. rewrite ?Z.add_0_r.
repeat (rewrite Z.mod_small by (unfold TB_g_q; lia)). lia.
Qed.

Lemma o4_den_gc : forall E (n : nat) q, ew E 27 = w64 TB_g_cmd -> ew E n = w64 q -> 0 <= q < 1024 ->
  sv_denot E (SAlu ALU_ADD (SOff 27 0) (SMd M_MUL (SOff n 0) (SLit 40))) = w64 (TB_g_cmd + 40 * q).
Proof.
intros E n q HC Hn Hq. apply bv_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 27 0) (SMd M_MUL (SOff n 0) (SLit 40)))))
  with (U E (SAlu ALU_ADD (SOff 27 0) (SMd M_MUL (SOff n 0) (SLit 40)))).
rewrite U_SAlu, U_SMd, !U_SOff, U_SLit. cbn [zalu_raw zmd_raw]. rewrite HC, Hn. unfold w64.
rewrite !unsigned_lit_small by (unfold TB_g_cmd; lia).
unfold zcanon, M64. rewrite ?Z.add_0_r.
repeat (rewrite Z.mod_small by (unfold TB_g_cmd; lia)). unfold TB_g_cmd. lia.
Qed.

(* A register of a symbolic state becomes an atom holding its value. *)
Lemma o4_set_reg : forall E ss ms (r : bv 5) (n : nat),
  st_ok_pi segs VAL E ss ms -> YK11.getr (ms_regs ms) r = ew E n -> bv_eqb r 0 = false ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r n HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *.
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs segs E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r (SOff n 0)) HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. pose proof (st_ok_reg segs E _ ms r HS) as Hq.
  cbn [ss_regs] in Hq. rewrite <- Hq, Hr, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* c's len, display and key bytes from c's struct. *)
Lemma o4_c_vals : forall (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs m c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  0 <= len < 256 -> 0 <= disp < 256 ->
  YI04.val_mem segs m (c + 24) 1 len /\ YI04.val_mem segs m (c + 25) 1 disp /\ YI04.val_mem segs m (c + 28) 4 key.
Proof.
intros m c cb len disp key HG Hcb Hl Hd.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
assert (HN : forall i, (24 <= i < 32)%nat ->
  nth i (TW.zs (TOP.cmd_struct cb len disp key)) 0 =
  bv_unsigned (nth (i - 24) ([DSpec.b8 len; DSpec.b8 disp; DSpec.b8 0; DSpec.b8 0] ++ TW.put 4 key) (Z_to_bv 8 0))).
{ intros i Hi. unfold TW.zs, TOP.cmd_struct.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, !length_app, Hcb, TWL.length_put; cbn; lia).
  rewrite map_nth. rewrite app_nth2 by lia. rewrite Hcb. reflexivity. }
assert (V : forall i, (i < 32)%nat -> YI04.val_mem segs m (c + Z.of_nat i) 1 (nth i (TW.zs (TOP.cmd_struct cb len disp key)) 0))
  by (intros i Hi; exact (proj1 (HG i ltac:(rewrite HL; lia)))).
split; [|split].
- pose proof (V 24%nat ltac:(lia)) as H. rewrite HN in H by lia. cbn in H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H.
  rewrite Z.mod_small in H by lia. exact H.
- pose proof (V 25%nat ltac:(lia)) as H. rewrite HN in H by lia. cbn in H.
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap, bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H.
  rewrite Z.mod_small in H by lia. exact H.
- intros k Hk. pose proof (V (28 + k)%nat ltac:(lia)) as H. rewrite HN in H by lia.
  replace (28 + k - 24)%nat with (4 + k)%nat in H by lia.
  rewrite app_nth2 in H by (cbn; lia). cbn [length] in H. replace (4 + k - 4)%nat with k in H by lia.
  rewrite tw_le_byte_put in H by exact Hk.
  specialize (H 0%nat ltac:(lia)). cbn [Z.of_nat] in H. rewrite Z.add_0_r in H.
  replace (c + Z.of_nat (28 + k)) with (c + 28 + Z.of_nat k) in H by lia. rewrite H. do 2 f_equal.
  apply tw_le_byte1. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.

(* c's first 32 bytes are present. *)
Lemma o4_c_some : forall (H : word -> bool) (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs (mrestrict H m) c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  forall i, 0 <= i < 32 -> aview segs H m (c + i) <> None.
Proof.
intros H m c cb len disp key HG Hcb i Hi.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
pose proof (proj1 (HG (Z.to_nat i) ltac:(rewrite HL; lia))) as V.
rewrite Z2Nat.id in V by lia.
pose proof (o4_aview_of_val H m (c + i) 1 _ 0%nat V ltac:(lia)) as A.
cbn [Z.of_nat] in A. rewrite Z.add_0_r in A. rewrite A. discriminate.
Qed.

(* The byte i < 24 of c is byte i of its bytes. *)
Lemma o4_c_byte : forall (H : word -> bool) (m : word -> option byte) (c : Z) (cb : list byte) (len disp key : Z),
  garr8 segs (mrestrict H m) c (TW.zs (TOP.cmd_struct cb len disp key)) -> length cb = 24%nat ->
  forall i, 0 <= i < 24 -> aview segs H m (c + i) = Some (bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0))).
Proof.
intros H m c cb len disp key HG Hcb i Hi.
assert (HL : length (TW.zs (TOP.cmd_struct cb len disp key)) = 32%nat).
{ unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hcb, TWL.length_put. reflexivity. }
pose proof (proj1 (HG (Z.to_nat i) ltac:(rewrite HL; lia))) as V.
rewrite Z2Nat.id in V by lia.
pose proof (o4_aview_of_val H m (c + i) 1 _ 0%nat V ltac:(lia)) as A.
cbn [Z.of_nat] in A. rewrite Z.add_0_r in A. rewrite A. f_equal.
assert (E : nth (Z.to_nat i) (TW.zs (TOP.cmd_struct cb len disp key)) 0 = bv_unsigned (nth (Z.to_nat i) cb (Z_to_bv 8 0))).
{ unfold TW.zs, TOP.cmd_struct.
  rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map, !length_app, Hcb, TWL.length_put; cbn; lia).
  rewrite map_nth. rewrite app_nth1 by lia. reflexivity. }
rewrite E. apply tw_le_byte1. apply bv_unsigned_in_range.
Qed.

(* A G byte is below the shadow and the stack. *)
Lemma o4_GL : forall a, inG TG.G_HARNESS_B a -> 0 <= a < 2147450880.
Proof. intros a Ha. pose proof (transportb_segs_low a (trans_g_img a Ha)) as H. unfold kLowMemEnd in H. lia. Qed.

(* The shadow entry of a zero-shadow payload [glo, ghi) at atom mt, offsets [lo, hi). *)
Lemma o4_shent : forall ly S (W : world segs) mem md (E : env) (mt : nat) (p lo hi glo ghi : Z),
  @AR rc segs B ly S W mem md -> decode_zshadow_at B glo ghi ->
  ew E 26 = w64 SHADOW_OFF -> ew E mt = w64 p -> 0 <= lo < hi ->
  glo <= (p + lo) / 64 * 64 -> (p + hi - 1) / 64 * 64 + 64 <= ghi -> 0 <= p -> p + hi <= SHADOW_OFF ->
  shent_ok segs O4_Bx E (mrestrict (w_H W) mem) (mkSHE mt lo hi).
Proof.
intros ly S W mem md E mt p lo hi glo ghi HAR HZ HB Hp Hlh Hglo Hghi Hp0 HpS.
apply (shent_ok_of_range segs (w_H W) mem E O4_Bx mt (p + lo) (hi - lo) p lo hi).
- exact (proj1 (decode_zshadow_ra B ly S W mem md glo ghi (p + lo) (hi - lo) HAR HZ ltac:(lia) Hglo
    ltac:(replace (p + lo + (hi - lo) - 1) with (p + hi - 1) by lia; exact Hghi))).
- unfold U, O4_Bx. cbn [sv_denot]. rewrite HB, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
- unfold U. cbn [sv_denot]. rewrite Hp, Z.add_0_r. unfold w64. rewrite Z_to_bv_bv_unsigned.
  apply unsigned_lit_small. unfold SHADOW_OFF in HpS. lia.
- lia.
- lia.
- intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. unfold SHADOW_OFF in *. lia.
Qed.

(* The 64-byte blocks of g_cmd[s]'s bytes [lo, hi) and of g_q[i]'s 4 bytes inside their globals. *)
Lemma o4_cmd_blk : forall s lo hi, 0 <= s < 1024 -> 0 <= lo -> lo < hi <= 40 ->
  TB_g_cmd <= (TB_g_cmd + 40 * s + lo) / 64 * 64 /\ (TB_g_cmd + 40 * s + hi - 1) / 64 * 64 + 64 <= TB_g_cmd + 40960.
Proof.
intros s lo hi Hs Hl Hh. unfold TB_g_cmd. split.
- assert (H : 6180992 / 64 <= (6180992 + 40 * s + lo) / 64) by (apply Z.div_le_mono; lia).
  change (6180992 / 64) with 96578 in H. lia.
- assert (H : (6180992 + 40 * s + hi - 1) / 64 <= 6221951 / 64) by (apply Z.div_le_mono; lia).
  change (6221951 / 64) with 97217 in H. lia.
Qed.

Lemma o4_q_blk : forall i, 0 <= i < 1024 ->
  TB_g_q <= (TB_g_q + 4 * i + 0) / 64 * 64 /\ (TB_g_q + 4 * i + 4 - 1) / 64 * 64 + 64 <= TB_g_q + 4096.
Proof.
intros i Hi. unfold TB_g_q. split.
- assert (H : 6232192 / 64 <= (6232192 + 4 * i + 0) / 64) by (apply Z.div_le_mono; lia).
  change (6232192 / 64) with 97378 in H. lia.
- assert (H : (6232192 + 4 * i + 4 - 1) / 64 <= 6236287 / 64) by (apply Z.div_le_mono; lia).
  change (6236287 / 64) with 97441 in H. lia.
Qed.

(* A written region of G bytes at an atom's address, with no chunk. *)
Lemma o4_rgw_ok : forall E (m : word -> option byte) (n : nat) b lo hi,
  bv_unsigned (ew E n) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 -> lo <= hi ->
  (forall o, lo <= o < hi -> inG TG.G_HARNESS_B (b + o)) ->
  region_ok segs E m (YP09.mkRegion (Some n) lo hi lo hi []).
Proof.
intros E m n b lo hi Hn H0 H1 Hlh HG. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw). apply HG. lia.
Qed.

(* A written 4-byte G cell at an address, holding the value of atom a. *)
Lemma o4_rgabs_ok : forall E (m : word -> option byte) (a : nat) g v,
  bv_unsigned (ew E a) = v -> 0 <= v < 2 ^ 32 -> 0 <= g -> g + 4 <= 2 ^ 64 ->
  (forall o, g <= o < g + 4 -> inG TG.G_HARNESS_B o) ->
  YI04.val_mem segs m (0 + g) 4 v ->
  region_ok segs E m (YP09.mkRegion None g (g + 4) g (g + 4) [YP09.mkChunk g (CVal 4 (SOff a 0))]).
Proof.
intros E m a g v Ha Hv Hg0 Hg1 HG V. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|].
split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw); apply HG; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ 0 g 4 (SOff a 0) v);
  [cbn [sv_denot]; rewrite Ha, Z.add_0_r; reflexivity | lia | cbn; lia | exact V].
Qed.

(* A written 4-byte G cell at an atom, holding the value of atom a. *)
Lemma o4_rgq_ok : forall E (m : word -> option byte) (n a : nat) g v,
  bv_unsigned (ew E n) = g -> bv_unsigned (ew E a) = v -> 0 <= v < 2 ^ 32 -> 0 <= g -> g + 4 <= 2 ^ 64 ->
  (forall o, g <= o < g + 4 -> inG TG.G_HARNESS_B o) ->
  YI04.val_mem segs m (g + 0) 4 v ->
  region_ok segs E m (YP09.mkRegion (Some n) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff a 0))]).
Proof.
intros E m n a g v Hn Ha Hv Hg0 Hg1 HG V. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hn.
split; [lia|]. split; [lia|].
split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw); apply HG; lia|].
apply Forall_cons; [|apply Forall_nil].
apply (chunk_ok_val segs E _ g 0 4 (SOff a 0) v);
  [cbn [sv_denot]; rewrite Ha, Z.add_0_r; reflexivity | lia | cbn; lia | exact V].
Qed.

(* c's first n <= 24 bytes are addressable (shadow 4 .. 6 of the frame is 0 while c is in scope) and the shadow
   bytes of their hull are the frame's. *)
Lemma o4_c_src : forall cx (rd : reader) n,
  lc_fsh cx rd true false -> 4096 <= lc_F cx -> lc_F cx mod 64 = 0 -> 0 < n <= 24 ->
  range_addressable rd SHADOW_OFF (lc_F cx + 32) n /\ shadow_hull_vis rd (lc_F cx + 32) n.
Proof.
intros cx rd n HS HF0 HF64 Hn.
pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
remember (lc_F cx / 64) as k eqn:Ek. clear Ek.
assert (EF8 : lc_F cx / 8 = 8 * k) by (rewrite D; replace (64 * k) with ((8 * k) * 8) by ring; apply Z.div_mul; lia).
assert (ESH : lc_SH cx = SHADOW_OFF + 8 * k) by (unfold lc_SH; rewrite EF8; reflexivity).
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  unfold shadow_of_addr.
  assert (Hq : x / 8 = 8 * k + 4 \/ x / 8 = 8 * k + 5 \/ x / 8 = 8 * k + 6).
  { pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx. lia. }
  destruct Hq as [Hq|[Hq|Hq]]; rewrite Hq.
  + replace (SHADOW_OFF + (8 * k + 4)) with (lc_SH cx + 4) by (rewrite ESH; ring). exact (HS 4 ltac:(lia)).
  + replace (SHADOW_OFF + (8 * k + 5)) with (lc_SH cx + 5) by (rewrite ESH; ring). exact (HS 5 ltac:(lia)).
  + replace (SHADOW_OFF + (8 * k + 6)) with (lc_SH cx + 6) by (rewrite ESH; ring). exact (HS 6 ltac:(lia)).
- intros s Hs. unfold shadow_addr in Hs.
  assert (Hy1 : (lc_F cx + 32) / 8 = 8 * k + 4).
  { pose proof (Z.div_mod (lc_F cx + 32) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lc_F cx + 32) 8 ltac:(lia)). lia. }
  assert (Hy2 : 8 * k + 4 <= (lc_F cx + 32 + n - 1) / 8 <= 8 * k + 6).
  { pose proof (Z.div_mod (lc_F cx + 32 + n - 1) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (lc_F cx + 32 + n - 1) 8 ltac:(lia)). lia. }
  rewrite Hy1 in Hs. unfold SHADOW_OFF in *.
  assert (Hz1 : (2147450880 + (8 * k + 4)) / 8 = 268431360 + k).
  { pose proof (Z.div_mod (2147450880 + (8 * k + 4)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (8 * k + 4)) 8 ltac:(lia)). lia. }
  assert (Hz2 : (2147450880 + (lc_F cx + 32 + n - 1) / 8) / 8 = 268431360 + k).
  { pose proof (Z.div_mod (2147450880 + (lc_F cx + 32 + n - 1) / 8) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (lc_F cx + 32 + n - 1) / 8) 8 ltac:(lia)). lia. }
  rewrite Hz1, Hz2 in Hs.
  replace s with (lc_SH cx + (s - lc_SH cx)) by ring.
  rewrite (HS (s - lc_SH cx) ltac:(rewrite ESH; lia)). discriminate.
Qed.

(* An aview equality carries a val_mem fact. *)
Lemma o4_val_mem_xfer : forall H (m m' : word -> option byte) a n v,
  (forall k, (k < n)%nat -> aview segs H m' (a + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  YI04.val_mem segs (mrestrict H m) a n v -> YI04.val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v Hk V k Hkn. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat k) (Hk k Hkn)). exact (V k Hkn).
Qed.

(* A frame byte is no byte of G: the frame lies apart from a range of G. *)
Lemma o4_apart_G : forall F g n, (forall x, F <= x < F + 256 -> ~ inG TG.G_HARNESS_B x) ->
  (forall x, g <= x < g + n -> inG TG.G_HARNESS_B x) -> 0 < n -> F + 256 <= g \/ g + n <= F.
Proof.
intros F g n HF HG Hn. destruct (Z_le_gt_dec (F + 256) g) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (g + n) F) as [H'|H']; [right; exact H'|]. exfalso.
apply (HF (Z.max F g)); [lia|]. apply HG. lia.
Qed.

(* An atom's denotation. *)
Lemma o4_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

(* The state at CMDW holds of the machine state there. *)
Lemma o4_entry1 : forall (W : world segs) (regs : bvmap 5 word) mem (sp1 F serial tn fin key disp len ncmd : Z),
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 (F + 32) ->
  YM05.alloc_ceiling + 32432 <= sp1 <= 2 ^ 47 - 320 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= YM05.alloc_ceiling ->
  0 <= serial < 1024 -> 0 <= tn < 2 ^ 64 -> 0 <= fin < 2 ^ 64 -> 0 <= key < 2 ^ 32 -> 0 <= disp < 256 ->
  0 <= len < 256 -> 0 <= ncmd < 2 ^ 32 ->
  rdword (aview segs (w_H W) mem) (sp1 + 0) = Some (TB_g_cmd + 40 * serial) ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some tn ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some fin ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some O4_H14 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some O4_H15 ->
  rdword (aview segs (w_H W) mem) (sp1 + 64) = Some serial ->
  rdword (aview segs (w_H W) mem) (sp1 + 144) = Some (F + 32) ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 24) 1 len ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 25) 1 disp ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (F + 32 + 28) 4 key ->
  st_ok_pi segs VAL (o4_E regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0) o4_ss1
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_CMDW)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 F serial tn fin key disp len ncmd R2 R9 R26 R20 Hsp1 Hsp32 HF0 HF64 HFg Hs Htn Hfin Hkey
  Hdisp Hlen Hncmd S0 S8 S16 S32 S56 S64 S144 Vlen Vdisp Vkey.
pose proof YM05.alloc_ceiling_value as Hce.
set (E := o4_E regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply o4_ew_r; exact Hn).
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 0 ltac:(lia)) as E32.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 1 ltac:(lia)) as E33.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 2 ltac:(lia)) as E34.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 3 ltac:(lia)) as E35.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 4 ltac:(lia)) as E36.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 5 ltac:(lia)) as E37.
pose proof (o4_ew_x regs (TB_g_cmd + 40 * serial) tn fin serial key disp len ncmd 0 0 0 0 6 ltac:(lia)) as E38.
fold E in E32, E33, E34, E35, E36, E37, E38.
cbn [Nat.add nth o4_extra] in E32, E33, E34, E35, E36, E37, E38.
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = F + 32)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = TB_g_cmd + 40 * serial)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U35 : bv_unsigned (ew E 35) = serial) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = key) by (rewrite E36; unfold w64; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = disp) by (rewrite E37; unfold w64; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = len) by (rewrite E38; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ss1.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks o4_rg_sp1 o4_rg_c base_val];
    rewrite ?U9, ?U20.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (o4_chunk8 E mem (w_H W) sp1 0 (SOff 32 0) (TB_g_cmd + 40 * serial));
        [rewrite o4_den_atom; exact E32 | unfold TB_g_cmd; lia | exact S0].
    * apply (o4_chunk8 E mem (w_H W) sp1 8 (SOff 33 0) tn); [rewrite o4_den_atom; exact E33 | lia | exact S8].
    * apply (o4_chunk8 E mem (w_H W) sp1 16 (SOff 34 0) fin); [rewrite o4_den_atom; exact E34 | lia | exact S16].
    * apply (o4_chunk8 E mem (w_H W) sp1 32 (SLit O4_H14) O4_H14); [reflexivity | unfold O4_H14; lia | exact S32].
    * apply (o4_chunk8 E mem (w_H W) sp1 56 (SLit O4_H15) O4_H15); [reflexivity | unfold O4_H15; lia | exact S56].
    * apply (o4_chunk8 E mem (w_H W) sp1 64 (SOff 35 0) serial); [rewrite o4_den_atom; exact E35 | lia | exact S64].
    * apply (o4_chunk8 E mem (w_H W) sp1 144 (SOff 20 0) (F + 32));
        [rewrite o4_den_atom, (EE 20%nat 20%bv eq_refl); exact R20 | lia | exact S144].
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (o4_chunkv E _ (F + 32) 24 1 (SOff 38 0) len); [rewrite o4_den_atom; exact E38 | cbn; lia | lia | exact Vlen].
    * apply (o4_chunkv E _ (F + 32) 25 1 (SOff 37 0) disp); [rewrite o4_den_atom; exact E37 | cbn; lia | lia | exact Vdisp].
    * apply (o4_chunkv E _ (F + 32) 28 4 (SOff 36 0) key); [rewrite o4_den_atom; exact E36 | cbn; lia | lia | exact Vkey].
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, o4_rg_sp1, o4_rg_c.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U20.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; first [exact I | lia].
- unfold o4_facts1, O4_PSP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U26, U20, U32, U35, U36, U37, U38.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H8 : (TB_g_cmd + 40 * serial) mod 8 = 0).
  { unfold TB_g_cmd. replace (6180992 + 40 * serial) with ((772624 + 5 * serial) * 8) by lia. apply Z_mod_mult. }
  assert (H32 : (F + 32) mod 32 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
    replace (F + 32) with ((2 * (F / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I; first [lia | unfold SHADOW_OFF, TB_g_cmd in *; lia].
Qed.

(* The state at RCPY (the return of __asan_memcpy) holds of the machine state there: the spill slots and g_ncmd;
   s9 holds av in [alo, ahi]. *)
Lemma o4_entry2 : forall (W : world segs) (regs : bvmap 5 word) mem (sp1 F serial tn fin ncmd nq x41 q x43 alo ahi
    nlo nhi av : Z),
  YK11.getr regs 2 = w64 sp1 -> YK11.getr regs 9 = w64 sp1 -> YK11.getr regs 26 = w64 SHADOW_OFF ->
  YK11.getr regs 20 = w64 (F + 32) -> YK11.getr regs 27 = w64 TB_g_cmd -> YK11.getr regs 25 = w64 av ->
  YM05.alloc_ceiling + 32432 <= sp1 <= 2 ^ 47 - 320 -> sp1 mod 32 = 0 ->
  4096 <= F -> F mod 64 = 0 -> F + 256 <= YM05.alloc_ceiling ->
  0 <= serial < 1024 -> 0 <= tn < 2 ^ 64 -> 0 <= fin < 2 ^ 64 -> 0 <= ncmd < 2 ^ 32 -> nlo <= nq <= nhi ->
  0 <= nq < 2 ^ 32 -> alo <= av <= ahi -> 0 <= av < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 8) = Some tn ->
  rdword (aview segs (w_H W) mem) (sp1 + 16) = Some fin ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some O4_H14 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some O4_H15 ->
  rdword (aview segs (w_H W) mem) (sp1 + 64) = Some serial ->
  rdword (aview segs (w_H W) mem) (sp1 + 144) = Some (F + 32) ->
  YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TB_g_ncmd) 4 ncmd ->
  st_ok_pi segs VAL (o4_E regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43) (o4_ss2 alo ahi nlo nhi [o4_rg_sp2; o4_rg_ncmd])
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_RCPY)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem sp1 F serial tn fin ncmd nq x41 q x43 alo ahi nlo nhi av R2 R9 R26 R20 R27 R25 Hsp1 Hsp32 HF0
  HF64 HFg Hs Htn Hfin Hncmd Hnq Hnq' Hav Hav' S8 S16 S32 S56 S64 S144 Vncmd.
pose proof YM05.alloc_ceiling_value as Hce.
set (E := o4_E regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E; apply o4_ew_r; exact Hn).
pose proof (o4_ew_x regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 1 ltac:(lia)) as E33.
pose proof (o4_ew_x regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 2 ltac:(lia)) as E34.
pose proof (o4_ew_x regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 3 ltac:(lia)) as E35.
pose proof (o4_ew_x regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 7 ltac:(lia)) as E39.
pose proof (o4_ew_x regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 8 ltac:(lia)) as E40.
pose proof (o4_ew_obj regs 0 tn fin serial 0 0 0 ncmd nq x41 q x43 21 ltac:(lia)) as EQ21.
fold E in E33, E34, E35, E39, E40, EQ21.
cbn [Nat.add nth o4_extra] in E33, E34, E35, E39, E40.
assert (U2 : bv_unsigned (ew E 2) = sp1) by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = sp1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U20 : bv_unsigned (ew E 20) = F + 32)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = TB_g_cmd)
  by (rewrite (EE 27%nat 27%bv eq_refl), R27; unfold w64; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U25 : bv_unsigned (ew E 25) = av)
  by (rewrite (EE 25%nat 25%bv eq_refl), R25; unfold w64; apply unsigned_lit_small; lia).
assert (UQ : bv_unsigned (ew E (A_OBJ 21)) = TB_g_q)
  by (rewrite EQ21, (proj1 o4_vals); apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U35 : bv_unsigned (ew E 35) = serial) by (rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U39 : bv_unsigned (ew E 39) = ncmd) by (rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E 40) = nq) by (rewrite E40; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold o4_ss2.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks o4_rg_sp2 o4_rg_ncmd base_val];
    rewrite ?U9.
  + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (o4_chunk8 E mem (w_H W) sp1 8 (SOff 33 0) tn); [rewrite o4_den_atom; exact E33 | lia | exact S8].
    * apply (o4_chunk8 E mem (w_H W) sp1 16 (SOff 34 0) fin); [rewrite o4_den_atom; exact E34 | lia | exact S16].
    * apply (o4_chunk8 E mem (w_H W) sp1 32 (SLit O4_H14) O4_H14); [reflexivity | unfold O4_H14; lia | exact S32].
    * apply (o4_chunk8 E mem (w_H W) sp1 56 (SLit O4_H15) O4_H15); [reflexivity | unfold O4_H15; lia | exact S56].
    * apply (o4_chunk8 E mem (w_H W) sp1 64 (SOff 35 0) serial); [rewrite o4_den_atom; exact E35 | lia | exact S64].
    * apply (o4_chunk8 E mem (w_H W) sp1 144 (SOff 20 0) (F + 32));
        [rewrite o4_den_atom, (EE 20%nat 20%bv eq_refl); exact R20 | lia | exact S144].
  + split; [unfold TB_g_ncmd; lia|]. split; [unfold TB_g_ncmd; lia|].
    split; [intros o Ho; apply (gx_rw_writable segs TG.G_HARNESS_B _ G_HARNESS_B_rw); apply o4_inG_ncmd; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (o4_chunkv E _ 0 TB_g_ncmd 4 (SOff 39 0) ncmd); [rewrite o4_den_atom; exact E39 | cbn; lia | lia | exact Vncmd].
- apply pairwise_disjoint_of_extents.
  unfold extent_of_region, o4_rg_sp2, o4_rg_ncmd.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold TB_g_ncmd. repeat split; first [exact I | lia].
- unfold o4_facts2, O4_PSP, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U2, U9, U26, U20, U27, U25, UQ, U35, U40.
  change (2 ^ 5) with 32. change (2 ^ 6) with 64. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (H32 : (F + 32) mod 32 = 0).
  { pose proof (Z.div_mod F 64 ltac:(lia)) as D. rewrite HF64, Z.add_0_r in D.
    replace (F + 32) with ((2 * (F / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  repeat match goal with |- _ /\ _ => split end; try exact I;
    first [lia | unfold SHADOW_OFF, TB_g_cmd, TB_g_q in *; lia | vm_compute; reflexivity].
Qed.

End mach.

(* The windows a run wrote, each case closed by tac. *)
Ltac o4_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The value of register r in the machine state of a symbolic state HS, as v. *)
Ltac o4_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* The low atoms of a run's valuation are those of E0. *)
Ltac o4_low HS E0 HEX :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
      assert (HEX : forall n, (n < 1024)%nat -> ew Ex n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn;
            repeat rewrite ew_ewset_other by lia; repeat rewrite ew_havoc_old by lia; reflexivity)
  end.

(* The write right of a run: regions with an empty window, or G's (each address rewritten by the equations Us). *)
Ltac o4_awr Us :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (first
    [ apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?Us in Ha;
        first [ apply o4_inG_cmd; unfold TB_g_cmd in *; lia | apply o4_inG_q; unfold TB_g_q in *; lia
              | apply o4_inG_nq; unfold TB_g_nq in *; lia | apply o4_inG_ncmd; unfold TB_g_ncmd in *; lia ] |] ]);
  apply awr_ok_x_nil.

(* The same, with the address rewrites given as a tactic on the window hypothesis. *)
Ltac o4_awr2 rw :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (first
    [ apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; exfalso; lia |]
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rw Ha;
        first [ apply o4_inG_cmd; unfold TB_g_cmd in *; lia | apply o4_inG_q; unfold TB_g_q in *; lia
              | apply o4_inG_nq; unfold TB_g_nq in *; lia | apply o4_inG_ncmd; unfold TB_g_ncmd in *; lia ] |] ]);
  apply awr_ok_x_nil.

(* A spill slot of the loop holds its value. *)
Lemma o4_spill_get : forall {rc : YM05.RunCeil} cx (r : reader) o v,
  lc_spills cx (lf_spill_loop (lc_F cx)) r -> In (o, v) (lf_spill_loop (lc_F cx)) -> rdword r (lc_sp1 cx + o) = Some v.
Proof. intros rc cx r o v H Hin. unfold lc_spills in H. rewrite Forall_forall in H. exact (H (o, v) Hin). Qed.

Ltac o4_in := unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app];
  repeat (first [left; reflexivity | right]).

Lemma o4_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z.div_mod a 32 ltac:(lia)) as Da. rewrite Ha, Z.add_0_r in Da.
rewrite Zminus_mod, Hb. rewrite Da. replace (32 * (a / 32)) with ((2 * (a / 32)) * 16) by ring.
rewrite Z_mod_mult. reflexivity.
Qed.

Section seg. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The loop facts of a cut carry over a stretch that keeps every byte outside G and outside the callee's window below
   sp1 (X bytes), the presence of every byte, the registers lc_lcore reads, the journal's ly and S and the events. *)
Lemma o4_lcore_keep : forall cx op cin bin k ly S (W : world segs) regs mem md e regs2 mem2 md2 (X : Z),
  lc_base B MT XL RLO RHI cx -> AR_laws segs B ->
  lc_lcore B MT cx op cin bin k ly S W regs mem md e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S W mem2 md2 e ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)) ->
  0 <= X <= 4096 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - X <= a < lc_sp1 cx) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  lc_lcore B MT cx op cin bin k ly S W regs2 mem2 md2 e.
Proof.
intros cx op cin bin k ly S W regs mem md e regs2 mem2 md2 X HB LAWS HL HJ2 KR HX K GA.
destruct HL as (HC & HFR & HSP & HFSH & HOK & He & HMT & R19).
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & HFal & HFceil & _).
destruct Hstk as (Hs1 & Hs2 & Hs3 & Hs4). destruct Hsp1 as [Hsp1a Hsp1b].
pose proof YM05.alloc_ceiling_value as Hce.
unfold LF_FBYTES, LF_FRAME, LLVMF_STK in *.
assert (HSH : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= YM05.alloc_ceiling).
{ unfold lc_SH. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as D0.
  assert (D1 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
assert (KS : forall a, lc_sp1 cx <= a < lc_sp0 cx -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply K; [lia | intros HG; pose proof (o4_GL a HG); lia | lia]. }
assert (KFr : forall a, lc_F cx <= a < lc_F cx + 256 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha. apply K; [lia | | lia]. intros HG.
  apply (frm_img segs B LAWS ly S W mem md LF_CID (l_fpos cx) a HAR HFin); [|exact (trans_g_img _ HG)].
  rewrite HFaddr. change (fs_frame_bytes LF_CID) with 256. lia. }
assert (KSH : forall a, lc_SH cx <= a < lc_SH cx + 32 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ unfold SHADOW_OFF in HSH. intros a Ha. apply K; [lia | intros HG; pose proof (o4_GL a HG); lia | lia]. }
assert (KR' : forall r : Z, In r [2; 3; 4; 8; 9] -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- apply (lc_core_kept_run B MT XL RLO RHI cx ly S W regs mem md e ly S W regs2 mem2 md2 e HB HC HJ2 eq_refl
    (Permutation_refl _) KR').
  + intros a Ha. apply KS. lia.
  + intros i Hi. destruct Hnl as [Hn1 Hnl].
    pose proof (Hinb ltac:(lia)) as Hb.
    destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HAR Hb) as (_ & H4096 & Hbc & _).
    unfold req_size in Hbc. destruct (l_n cx =? 0) eqn:E0; [apply Z.eqb_eq in E0; lia|].
    apply K; [lia | | lia]. intros HG.
    apply (blk_img segs B LAWS ly S W mem md (l_p cx) (l_n cx) (l_p cx + i) HAR Hb); [|exact (trans_g_img _ HG)].
    unfold req_size. rewrite E0. lia.
  + intros a Ha. unfold LF_FBYTES in Ha. apply KFr. lia.
  + intros a _ Hp. exact (GA a Hp).
- destruct HFR as (R18 & R26). split.
  + change (YK11.getr regs2 18) with (YK11.getr regs2 (Z_to_bv 5 18)).
    rewrite (KR 18 ltac:(cbn; tauto)). exact R18.
  + change (YK11.getr regs2 26) with (YK11.getr regs2 (Z_to_bv 5 26)).
    rewrite (KR 26 ltac:(cbn; tauto)). exact R26.
- eapply lc_spills_kept; [| | exact HSP].
  + intros o Ho.
    pose proof (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) as V.
    rewrite Forall_forall in V. destruct (V o Ho) as (_ & _ & H8 & H192). lia.
  + intros a Ha. apply KS. lia.
- eapply lc_fsh_kept; [| exact HFSH]. exact KSH.
- exact HOK.
- exact He.
- exact HMT.
- change (YK11.getr regs2 19) with (YK11.getr regs2 (Z_to_bv 5 19)).
  rewrite (KR 19 ltac:(cbn; tauto)). exact R19.
Qed.

(* The S4 cut from its facts at the final registers and memory. *)
Lemma o4_close : forall (cx : lcx) (op : lop) ly S (W : world segs) regs mem md e Bw c5 (pcv : word),
  pcv = w64 (transportb_text + LO_S4) ->
  lc_lcore B MT cx op true false (lo_k op) ly S W regs mem md e ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  lc_tw W mem Bw -> TC.settle_m Bw 0 = Some (Bw, tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (Bw, (c5, lo_k op))) ->
  lc_cur cx regs 24 27 c5 -> lc_s46 cx regs ->
  lc_st_s4 B MT cx op W (mkCfg (@YK11.mkst (l_fx cx) regs pcv mem (YK11.seg_rom segs)) md).
Proof.
intros cx op ly S W regs mem md e Bw c5 pcv Hpc HL Hopc HTW HSET HOP HCUR H46. subst pcv.
exists ly, S, regs, mem, md, e, Bw, c5.
split; [reflexivity|]. split; [exact Hopc|]. split; [exact HL|]. split; [exact HTW|]. split; [exact HSET|].
split; [exact HOP|]. split; [exact HCUR | exact H46].
Qed.

(* After a run: the run's valuation Ek is named in HS and its img_env fact, with its low atoms those of the walk's
   entry valuation E2 (from the previous valuation's Eplo). *)
Ltac o4_env HS E0 Ek Eklo Eplo HEIk :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    lazymatch goal with Hi : img_env _ _ Ex |- _ =>
      set (Ek := Ex) in HS, Hi; rename Hi into HEIk;
      assert (Eklo : forall n, (n < 1024)%nat -> ew Ek n = ew E0 n)
        by (let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; unfold Ek;
            repeat rewrite ew_ewset_other by lia; exact (Eplo n Hn))
    end end.

(* The frame lies in the application's low or high memory. *)
Lemma o4_F_range : forall cx ly S W regs mem md e, AR_laws segs B -> lc_base B MT XL RLO RHI cx ->
  lc_core B cx ly S W regs mem md e -> lc_F cx + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= lc_F cx.
Proof.
intros cx ly S W regs mem md e LAWS HB HC.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVE].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds segs B LAWS ly S W mem md LF_CID (l_fpos cx) HAR HFin) as (F1 & F2 & F3).
rewrite HFaddr in F1, F2, F3. rewrite lf_fbytes in F2, F3. unfold LF_FBYTES in F2, F3.
unfold in_app, kLowShadowBeg, ASAN_CEIL in F3. rewrite C3 in F3.
lia.
Qed.

(* want = SPEC_OK: o4_b6 is the replace (at >= 0) or the append (at < 0). *)
Lemma o4_b6_rep : forall B5 Bw at_ s, 0 <= at_ ->
  o4_b6 B5 Bw 0 at_ s = TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ s.
Proof. intros B5 Bw at_ s H. unfold o4_b6, DSpec.SPEC_OK. rewrite Z.eqb_refl, (proj2 (Z.leb_le 0 at_) H). reflexivity. Qed.
Lemma o4_b6_app : forall B5 Bw at_ s, at_ < 0 ->
  o4_b6 B5 Bw 0 at_ s = TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) s) ((TW.g_nq Bw + 1) mod 2 ^ 32).
Proof. intros B5 Bw at_ s H. unfold o4_b6, DSpec.SPEC_OK. rewrite Z.eqb_refl, (proj2 (Z.leb_gt 0 at_) H). reflexivity. Qed.

(* The replace, from RCPY to S4. *)
Lemma o4_tail_rep : forall (cx : lcx) (op : lop) ly S (W : world segs) regs mem md e (Bw : list byte) (c5 : TOP.fuzz_in)
    (at_ serial tn fin : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op true false (lo_k op) ly S W regs mem md e ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  lc_tw W mem Bw -> 0 <= at_ < 1024 -> 0 <= TW.Q_at Bw at_ < 1024 -> 0 <= serial < 1024 ->
  TC.settle_m (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ serial)) 0 =
    Some (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ serial), tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ serial), (c5, lo_k op))) ->
  YK11.getr regs (Z_to_bv 5 25) = w64 (at_ mod 2 ^ 32) ->
  YK11.getr regs (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off c5) ->
  YK11.getr regs (Z_to_bv 5 27) = w64 TB_g_cmd -> YK11.getr regs (Z_to_bv 5 20) = w64 (lc_F cx + 32) ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 8) = Some tn ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 16) = Some fin ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 64) = Some serial ->
  TOP.fi_n c5 = fin - tn ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_RCPY)) mem (YK11.seg_rom segs)) md)
    (lc_st_s4 B MT cx op).
Proof.
intros cx op ly S W regs mem md e Bw c5 at_ serial tn fin HP HB HL Hopc HTW Hat Hq Hs HSET HOP R25 R24 R27 R20 S8
  S16 S64 Hfi5.
pose proof HL as (HC0 & HFR & HSP & HFSH & HOK & He & HMT & R19).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC0) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC0 as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof YM05.alloc_ceiling_value as Hce.
pose proof HSC as (_ & _ & HZq & HZc).
destruct o4_vals as (VQ & VB & VH14 & VH15 & VNQ & VNC).
pose proof (o4_spill_get cx _ 32 (transportb_hi 14) HSP ltac:(o4_in)) as S32.
pose proof (o4_spill_get cx _ 56 (transportb_hi 15) HSP ltac:(o4_in)) as S56.
pose proof (o4_spill_get cx _ 144 (lc_F cx + 32) HSP ltac:(o4_in)) as S144.
rewrite <- VH14 in S32. rewrite <- VH15 in S56.
pose proof (o4_rdword_range _ _ _ _ S16) as Hfin. pose proof (o4_rdword_range _ _ _ _ S8) as Htn.
unfold LF_FBYTES in HFceil.
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
assert (Hsp1b : YM05.alloc_ceiling + 32432 <= lc_sp1 cx <= 2 ^ 47 - 320)
  by (unfold LF_FRAME in Hsp1; destruct Hsp1 as [Hsp1a Hsp1b']; split; [exact Hsp1c | lia]).
pose proof (TWL.u_at_range Bw TW.OFF_g_ncmd 4) as Hncmd. change (8 * Z.of_nat 4) with 32 in Hncmd.
assert (V39 : YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TB_g_ncmd) 4 (TW.u_at Bw TW.OFF_g_ncmd 4)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bw TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 4
    TMAP_B_ok HTW TMAP_B_g_ncmd ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as V.
  rewrite !Z.add_0_r in V. rewrite Z.add_0_l. exact V. }
assert (Vq : YI04.val_mem segs (mrestrict (w_H W) mem) (TB_g_q + 4 * at_ + 0) 4 (TW.Q_at Bw at_)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bw TW.OFF_g_q TB_g_q TW.SZ_g_q (4 * at_) 4
    TMAP_B_ok HTW TMAP_B_g_q ltac:(lia) ltac:(unfold TW.SZ_g_q; lia)) as V.
  rewrite Z.add_0_r. exact V. }
rewrite (Z.mod_small at_ (2 ^ 32)) in R25 by lia.
change (YK11.getr regs (Z_to_bv 5 20)) with (YK11.getr regs 20) in R20.
change (YK11.getr regs (Z_to_bv 5 25)) with (YK11.getr regs 25) in R25.
change (YK11.getr regs (Z_to_bv 5 27)) with (YK11.getr regs 27) in R27.
pose proof (o4_entry2 (fx := l_fx cx) W regs mem (lc_sp1 cx) (lc_F cx) serial tn fin (TW.u_at Bw TW.OFF_g_ncmd 4) 0
  (TB_g_q + 4 * at_) (TW.Q_at Bw at_) (TB_g_cmd + 40 * TW.Q_at Bw at_) 0 1023 0 0 at_ R2 R9 R26 R20 R27 R25
  Hsp1b Hsp1al HF4096 HFal HFceil Hs Htn Hfin Hncmd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S8 S16 S32 S56 S64 S144
  V39) as HS.
set (E2 := o4_E regs 0 tn fin serial 0 0 0 (TW.u_at Bw TW.OFF_g_ncmd 4) 0 (TB_g_q + 4 * at_) (TW.Q_at Bw at_)
  (TB_g_cmd + 40 * TW.Q_at Bw at_)) in HS.
assert (HEI : img_env VAL A_LIM E2) by (unfold E2; apply o4_env_img).
assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E2 n) by (intros; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs r)
  by (intros n r Hn'; unfold E2; apply o4_ew_r; exact Hn').
assert (EX : forall j, (j < 12)%nat -> ew E2 (32 + j) =
  nth j (o4_extra 0 tn fin serial 0 0 0 (TW.u_at Bw TW.OFF_g_ncmd 4) 0 (TB_g_q + 4 * at_) (TW.Q_at Bw at_)
    (TB_g_cmd + 40 * TW.Q_at Bw at_)) (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply o4_ew_x; exact Hj).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 9%nat ltac:(lia)) as E41. pose proof (EX 10%nat ltac:(lia)) as E42.
pose proof (EX 11%nat ltac:(lia)) as E43.
cbn [Nat.add nth o4_extra] in E33, E34, E35, E39, E41, E42, E43. clear EX.
assert (EQ21 : ew E2 (A_OBJ 21) = Z_to_bv 64 TB_g_q) by (unfold E2; rewrite o4_ew_obj by lia; rewrite VQ; reflexivity).
assert (E25 : ew E2 25 = w64 at_) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E2 27 = w64 TB_g_cmd) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E26 : ew E2 26 = w64 SHADOW_OFF) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (SHOK : sh_ok segs O4_Bx [] E2 (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
clear HSAV HIN HFpres HFL.
(* run R1, +0x155c .. +0x1570: `bltz` (decided: at in [0, 1023]), g_q + 4 at, its wrap test *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ o4_awr2 ltac:(fun H => idtac). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EA EAlo E2lo HEIA.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn.
  apply (kept_of_frame E2 _ (w_H W) mem (ms_mem ms) (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4) HFr); [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; unfold TB_g_ncmd; lia). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1, md1 into mdA, K1 into KA1, GA1 into GAA.
(* +0x1574: the wrap test, refuted *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
{ exfalso.
  pose proof (o4_trap_q _ 25 at_ ltac:(rewrite EAlo by (unfold A_OBJ; lia); exact EQ21)
    ltac:(rewrite EAlo by lia; exact E25) Hat) as T.
  change (A_OBJ 21) with 262%nat in T. rewrite T in Hc. discriminate Hc. }
clear Hc.
(* run R2, to +0x157c: a0 = g_q + 4 at *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_GQ.
{ o4_awr2 ltac:(fun H => idtac). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EB EBlo EAlo HEIB.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn. rewrite <- (KA1 a Ha Hn).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms) (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4) HFr);
    [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; unfold TB_g_ncmd; lia). }
assert (GA2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAA a Ha))).
clear HF HFr HG KA1 GAA.
rename ms into ms2, md1 into mdB.
o4_reg HS (Z_to_bv 5 10) (w64 (TB_g_q + 4 * at_)) R10
  ltac:(exact (o4_den_gq EB 25 at_ ltac:(rewrite EBlo by (unfold A_OBJ; lia); exact EQ21)
                ltac:(rewrite EBlo by lia; exact E25) Hat)).
assert (E41x : ew EB 41 = w64 (TB_g_q + 4 * at_)) by (rewrite EBlo by lia; exact E41).
pose proof (o4_set_reg EB _ _ (Z_to_bv 5 10) 41 HS ltac:(rewrite E41x; exact R10) eq_refl) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (U41 : bv_unsigned (ew EB 41) = TB_g_q + 4 * at_)
  by (rewrite E41x; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U42 : bv_unsigned (ew EB 42) = TW.Q_at Bw at_)
  by (rewrite EBlo by lia; rewrite E42; unfold w64; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew EB 9) = lc_sp1 cx)
  by (rewrite EBlo by lia; rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
  assert (Hdis : all_disjoint EB (o4_rg_q [YP09.mkChunk 0 (CVal 4 (SOff 42 0))]) (ss_mem s)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_q, o4_rg_sp2, o4_rg_ncmd.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U41, U9.
  unfold TB_g_q, TB_g_ncmd in *. repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region (PI := PI_transportb) EB _ _ (o4_rg_q [YP09.mkChunk 0 (CVal 4 (SOff 42 0))]) HS
  ltac:(vm_compute; reflexivity)
  (o4_rgq_ok EB _ 41 42 (TB_g_q + 4 * at_) (TW.Q_at Bw at_) U41 U42 ltac:(lia) ltac:(unfold TB_g_q; lia)
     ltac:(unfold TB_g_q; lia) ltac:(intros o Ho; apply o4_inG_q; lia)
     ltac:(apply (o4_val_mem_xfer (w_H W) mem (ms_mem ms2)); [|exact Vq];
           intros kk Hkk; apply K2; unfold TB_g_q, TB_g_ncmd; lia)) Hdis) as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_fact (PI := PI_transportb) EB _ _ 41 (mkAF TB_g_q (TB_g_q + 4092) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U41; change (2 ^ 2) with 4;
        split; [lia|]; split; [unfold TB_g_q; replace (6232192 + 4 * at_) with ((1558048 + at_) * 4) by ring;
                               apply Z_mod_mult | lia]))
  as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_fact (PI := PI_transportb) EB _ _ 42 (mkAF 0 1023 0) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U42, Z.pow_0_r, Z.mod_1_r; lia)) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
assert (SHQ : sh_ok segs O4_Bx O4_SHQ EB (mrestrict (w_H W) (ms_mem ms2))).
{ unfold sh_ok, O4_SHQ. constructor; [|constructor].
  destruct (o4_q_blk at_ Hat) as [Hb1 Hb2].
  apply (o4_shent B ly S W (ms_mem ms2) mdB EB 41 (TB_g_q + 4 * at_) 0 4 TB_g_q (TB_g_q + TW.SZ_g_q) HAR2 HZq
    ltac:(rewrite EBlo by lia; exact E26) E41x).
  - lia.
  - exact Hb1.
  - unfold TW.SZ_g_q. exact Hb2.
  - unfold TB_g_q. lia.
  - unfold TB_g_q, SHADOW_OFF. lia. }
clear SHOK. rename SHQ into SHOK.
(* run R3, +0x157c .. +0x15a0: the checked load of g_q[at], its index test (decided), g_cmd + 40 g_q[at] *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ o4_awr2 ltac:(fun H => rewrite ?U41 in H). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EC EClo EBlo HEIC.
assert (U41c : bv_unsigned (ew EC 41) = TB_g_q + 4 * at_)
  by (rewrite EClo by lia; rewrite E41; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
  ~ (TB_g_q + 4 * at_ <= a < TB_g_q + 4 * at_ + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2. rewrite <- (K2 a Ha Hn).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms2) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_q + 4 * at_ <= x < TB_g_q + 4 * at_ + 4) HFr);
    [|exact Ha | intros [Hx|Hx]; [exact (Hn Hx) | exact (Hn2 Hx)]].
  intros b wlo whi x Hin Hx.
  o4_win Hin Hx ltac:(cbv beta; rewrite ?U41, ?U9 in Hx; unfold TB_g_ncmd; first [lia | left; lia | right; lia]). }
assert (GA3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
clear HF HFr HG K2 GA2.
rename ms into ms3, md1 into mdC.
(* +0x15a4: the wrap test of g_cmd + 40 g_q[at], refuted *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
{ exfalso.
  rewrite (o4_trap_c _ 42 (TW.Q_at Bw at_) ltac:(rewrite EClo by lia; exact E27)
    ltac:(rewrite EClo by lia; exact E42) Hq) in Hc. discriminate Hc. }
clear Hc.
(* run R4, to +0x15ac: a1 = g_cmd + 40 g_q[at] *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_GC.
{ o4_awr2 ltac:(fun H => rewrite ?U41c in H). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 ED EDlo EClo HEID.
assert (K4 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
  ~ (TB_g_q + 4 * at_ <= a < TB_g_q + 4 * at_ + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2. rewrite <- (K3 a Ha Hn Hn2).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms3) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_q + 4 * at_ <= x < TB_g_q + 4 * at_ + 4) HFr);
    [|exact Ha | intros [Hx|Hx]; [exact (Hn Hx) | exact (Hn2 Hx)]].
  intros b wlo whi x Hin Hx.
  o4_win Hin Hx ltac:(cbv beta; rewrite ?U41c in Hx; unfold TB_g_ncmd; first [lia | left; lia | right; lia]). }
assert (GA4 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
clear HF HFr HG K3 GA3.
rename ms into ms4, md1 into mdD.
o4_reg HS (Z_to_bv 5 11) (w64 (TB_g_cmd + 40 * TW.Q_at Bw at_)) R11
  ltac:(exact (o4_den_gc ED 42 (TW.Q_at Bw at_) ltac:(rewrite EDlo by lia; exact E27)
                ltac:(rewrite EDlo by lia; exact E42) Hq)).
assert (E43x : ew ED 43 = w64 (TB_g_cmd + 40 * TW.Q_at Bw at_)) by (rewrite EDlo by lia; exact E43).
pose proof (o4_set_reg ED _ _ (Z_to_bv 5 11) 43 HS ltac:(rewrite E43x; exact R11) eq_refl) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (U43 : bv_unsigned (ew ED 43) = TB_g_cmd + 40 * TW.Q_at Bw at_)
  by (rewrite E43x; unfold w64; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U41b : bv_unsigned (ew ED 41) = TB_g_q + 4 * at_)
  by (rewrite EDlo by lia; rewrite E41; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U9b : bv_unsigned (ew ED 9) = lc_sp1 cx)
  by (rewrite EDlo by lia; rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
  assert (Hdis2 : all_disjoint ED o4_rg_k (ss_mem s)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_k, o4_rg_q, o4_rg_sp2, o4_rg_ncmd.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U43, U41b, U9b.
  unfold TB_g_q, TB_g_ncmd, TB_g_cmd in *. repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region (PI := PI_transportb) ED _ _ o4_rg_k HS ltac:(vm_compute; reflexivity)
  (o4_rgw_ok ED _ 43 (TB_g_cmd + 40 * TW.Q_at Bw at_) 0 4 U43 ltac:(unfold TB_g_cmd; lia)
     ltac:(unfold TB_g_cmd; lia) ltac:(lia) ltac:(intros o Ho; apply o4_inG_cmd; unfold TB_g_cmd in *; lia)) Hdis2)
  as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_fact (PI := PI_transportb) ED _ _ 43 (mkAF TB_g_cmd (TB_g_cmd + 40 * 1023) 3) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U43; change (2 ^ 3) with 8;
        split; [lia|]; split; [unfold TB_g_cmd; replace (6180992 + 40 * TW.Q_at Bw at_)
                                 with ((772624 + 5 * TW.Q_at Bw at_) * 8) by ring; apply Z_mod_mult | lia]))
  as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR4.
assert (SHK : sh_ok segs O4_Bx O4_SHK ED (mrestrict (w_H W) (ms_mem ms4))).
{ unfold sh_ok, O4_SHK. constructor; [|constructor; [|constructor]].
  - destruct (o4_q_blk at_ Hat) as [Hb1 Hb2].
    apply (o4_shent B ly S W (ms_mem ms4) mdD ED 41 (TB_g_q + 4 * at_) 0 4 TB_g_q (TB_g_q + TW.SZ_g_q) HAR4 HZq
      ltac:(rewrite EDlo by lia; exact E26) ltac:(rewrite EDlo by lia; exact E41)).
    + lia.
    + exact Hb1.
    + unfold TW.SZ_g_q. exact Hb2.
    + unfold TB_g_q. lia.
    + unfold TB_g_q, SHADOW_OFF. lia.
  - destruct (o4_cmd_blk (TW.Q_at Bw at_) 0 4 Hq ltac:(lia) ltac:(lia)) as [Hb1 Hb2].
    apply (o4_shent B ly S W (ms_mem ms4) mdD ED 43 (TB_g_cmd + 40 * TW.Q_at Bw at_) 0 4 TB_g_cmd
      (TB_g_cmd + TW.SZ_g_cmd) HAR4 HZc ltac:(rewrite EDlo by lia; exact E26) E43x).
    + lia.
    + exact Hb1.
    + unfold TW.SZ_g_cmd. exact Hb2.
    + unfold TB_g_cmd. lia.
    + unfold TB_g_cmd, SHADOW_OFF. lia. }
clear SHOK. rename SHK into SHOK.
(* run R5, +0x15ac .. +0x1650: g_cmd[g_q[at]].st = 3, g_q[at] = serial, s4, g_ncmd + 1, s11, s6 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_S4.
{ o4_awr2 ltac:(fun H => rewrite ?U41b, ?U43 in H). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EF EFlo EDlo HEIF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
  ~ (TB_g_q + 4 * at_ <= a < TB_g_q + 4 * at_ + 4) ->
  ~ (TB_g_cmd + 40 * TW.Q_at Bw at_ <= a < TB_g_cmd + 40 * TW.Q_at Bw at_ + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2 Hn3. rewrite <- (K4 a Ha Hn Hn2).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms4) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_q + 4 * at_ <= x < TB_g_q + 4 * at_ + 4 \/
              TB_g_cmd + 40 * TW.Q_at Bw at_ <= x < TB_g_cmd + 40 * TW.Q_at Bw at_ + 4) HFr);
    [|exact Ha | intros [Hx|[Hx|Hx]]; [exact (Hn Hx) | exact (Hn2 Hx) | exact (Hn3 Hx)]].
  intros b wlo whi x Hin Hx.
  o4_win Hin Hx ltac:(cbv beta; rewrite ?U41b, ?U43, ?U9b in Hx; unfold TB_g_ncmd;
    first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (GAF : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA4 a Ha))).
clear HF HFr HG K4 GA4.
(* the stored bytes, from the final chunks *)
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 0 _ HS eq_refl) as RGk.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 1 _ HS eq_refl) as RGq.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 3 _ HS eq_refl) as RGn.
cbn [ms_mem restrict] in RGk, RGq, RGn.
destruct RGk as (_ & _ & _ & Ck). destruct RGq as (_ & _ & _ & Cq). destruct RGn as (_ & _ & _ & Cn).
cbn [YP09.r_chunks YP09.r_base base_val] in Ck, Cq, Cn.
apply Forall_inv in Ck. apply Forall_inv in Cq. apply Forall_inv in Cn.
assert (U43F : bv_unsigned (ew EF 43) = TB_g_cmd + 40 * TW.Q_at Bw at_)
  by (rewrite EFlo by lia; rewrite E43; unfold w64; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U41F : bv_unsigned (ew EF 41) = TB_g_q + 4 * at_)
  by (rewrite EFlo by lia; rewrite E41; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U35F : bv_unsigned (ew EF 35) = serial)
  by (rewrite EFlo by lia; rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U39F : bv_unsigned (ew EF 39) = TW.u_at Bw TW.OFF_g_ncmd 4)
  by (rewrite EFlo by lia; rewrite E39; unfold w64; apply unsigned_lit_small; lia).
rewrite U43F in Ck. rewrite U41F in Cq.
assert (Vst : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms) (TB_g_cmd + 40 * TW.Q_at Bw at_ + Z.of_nat j) = Some (YO0f.le_byte 3 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) _ 0 4 4 (SLit 3) 3 Ck eq_refl ltac:(lia)
    (o4_den_lit EF 3 4 ltac:(lia)) j Hj) as Hb. rewrite Z.add_0_r in Hb. exact Hb. }
assert (Vqs : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms) (TB_g_q + 4 * at_ + Z.of_nat j) = Some (YO0f.le_byte serial 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) _ 0 4 4 _ (serial + 0) Cq eq_refl ltac:(lia)
    (o4_den_off EF 35 _ 4 0 U35F ltac:(lia)) j Hj) as Hb. rewrite !Z.add_0_r in Hb. exact Hb. }
assert (VN : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_ncmd + Z.of_nat j) =
  Some (YO0f.le_byte (TW.u_at Bw TW.OFF_g_ncmd 4 + 1) 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) 0 TB_g_ncmd 4 4 _
    (TW.u_at Bw TW.OFF_g_ncmd 4 + 1) Cn eq_refl ltac:(lia) (o4_den_inc EF 39 _ U39F) j Hj) as Hb.
  rewrite Z.add_0_l in Hb. exact Hb. }
clear Ck Cq Cn.
assert (HTWF : lc_tw W (ms_mem ms) (o4_b7 (TW.set_Q_at (TW.set_Cmd_st Bw (TW.Q_at Bw at_) TC.REPLACED) at_ serial))).
{ apply (o4_w_rep Bw (aview segs (w_H W) mem) (aview segs (w_H W) (ms_mem ms)) at_ serial HTW Hat Hq Vst Vqs VN).
  intros x Hx Hn1 Hn2 Hn3. pose proof (o4_GL x (o4_tw_in_G x Hx)) as Hl. apply KF; [lia | exact Hn3 | exact Hn2 | exact Hn1]. }
(* the registers *)
assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS);
      lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
      rewrite o4_den_atom, EFlo by lia; apply EE; reflexivity |]).
  destruct Hr. }
assert (R24F : YK11.getr (ms_regs ms) (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off c5)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite o4_den_atom, EFlo by lia. rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl). exact R24. }
assert (R27F : YK11.getr (ms_regs ms) (Z_to_bv 5 27) = w64 (TOP.fi_n c5)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite (o4_den_sub _ 34 33 fin tn); [rewrite Hfi5; reflexivity | |]; rewrite EFlo by lia; assumption. }
assert (R20F : YK11.getr (ms_regs ms) 20 = w64 (lc_F cx + 32)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite o4_den_atom, EFlo by lia. rewrite (EE 20%nat 20%bv eq_refl). exact R20. }
assert (R22F : YK11.getr (ms_regs ms) 22 = w64 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  reflexivity. }
assert (HLF : lc_lcore B MT cx op true false (lo_k op) ly S W (ms_regs ms) (ms_mem ms) md1 e).
{ apply (o4_lcore_keep cx op true false (lo_k op) ly S W regs mem md e (ms_regs ms) (ms_mem ms) md1 0
    HB LAWS HL HJ KR ltac:(lia)).
  - intros a Ha HnG _. apply KF; [exact Ha | intros Hn; apply HnG; apply o4_inG_ncmd; exact Hn
      | intros Hn; apply HnG; apply o4_inG_q; unfold TB_g_q in *; lia
      | intros Hn; apply HnG; apply o4_inG_cmd; unfold TB_g_cmd in *; lia].
  - exact GAF. }
pmkst HS.
apply SRr_ret.
refine (o4_close cx op ly S W (ms_regs ms) (ms_mem ms) md1 e _ c5 _ _ HLF Hopc HTWF HSET HOP
  (conj R24F R27F) (conj R20F R22F)).
rewrite VB. reflexivity.
Qed.

(* The append, from RCPY to S4. *)
Lemma o4_tail_app : forall (cx : lcx) (op : lop) ly S (W : world segs) regs mem md e (Bw : list byte) (c5 : TOP.fuzz_in)
    (serial tn fin : Z),
  lp_prem B MT XL RLO RHI -> lc_base B MT XL RLO RHI cx ->
  lc_lcore B MT cx op true false (lo_k op) ly S W regs mem md e ->
  lc_opc (l_pl cx) (lo_c op) = 4 ->
  lc_tw W mem Bw -> 0 <= TW.g_nq Bw < 1024 -> 0 <= serial < 1024 ->
  TC.settle_m (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) serial) ((TW.g_nq Bw + 1) mod 2 ^ 32))) 0 =
    Some (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) serial) ((TW.g_nq Bw + 1) mod 2 ^ 32)), tt) ->
  (forall A, TOP.LLVMFuzzerTestOneInput_op_m timg_B (lo_B op) A (l_pl cx) (lo_c op) (lo_k op) =
     Some (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) serial) ((TW.g_nq Bw + 1) mod 2 ^ 32)), (c5, lo_k op))) ->
  YK11.getr regs (Z_to_bv 5 25) = w64 (2 ^ 32 - 1) ->
  YK11.getr regs (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off c5) ->
  YK11.getr regs (Z_to_bv 5 27) = w64 TB_g_cmd -> YK11.getr regs (Z_to_bv 5 20) = w64 (lc_F cx + 32) ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 8) = Some tn ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 16) = Some fin ->
  rdword (aview segs (w_H W) mem) (lc_sp1 cx + 64) = Some serial ->
  TOP.fi_n c5 = fin - tn ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_RCPY)) mem (YK11.seg_rom segs)) md)
    (lc_st_s4 B MT cx op).
Proof.
intros cx op ly S W regs mem md e Bw c5 serial tn fin HP HB HL Hopc HTW Hnq Hs HSET HOP R25 R24 R27 R20 S8
  S16 S64 Hfi5.
pose proof HL as (HC0 & HFR & HSP & HFSH & HOK & He & HMT & R19).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly S W regs mem md e HB HC0) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC0 as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof YM05.alloc_ceiling_value as Hce.
pose proof HSC as (_ & _ & HZq & HZc).
destruct o4_vals as (VQ & VB & VH14 & VH15 & VNQ & VNC).
pose proof (o4_spill_get cx _ 32 (transportb_hi 14) HSP ltac:(o4_in)) as S32.
pose proof (o4_spill_get cx _ 56 (transportb_hi 15) HSP ltac:(o4_in)) as S56.
pose proof (o4_spill_get cx _ 144 (lc_F cx + 32) HSP ltac:(o4_in)) as S144.
rewrite <- VH14 in S32. rewrite <- VH15 in S56.
pose proof (o4_rdword_range _ _ _ _ S16) as Hfin. pose proof (o4_rdword_range _ _ _ _ S8) as Htn.
unfold LF_FBYTES in HFceil.
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
assert (Hsp1b : YM05.alloc_ceiling + 32432 <= lc_sp1 cx <= 2 ^ 47 - 320)
  by (unfold LF_FRAME in Hsp1; destruct Hsp1 as [Hsp1a Hsp1b']; split; [exact Hsp1c | lia]).
pose proof (TWL.u_at_range Bw TW.OFF_g_ncmd 4) as Hncmd. change (8 * Z.of_nat 4) with 32 in Hncmd.
assert (V39 : YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TB_g_ncmd) 4 (TW.u_at Bw TW.OFF_g_ncmd 4)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bw TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 4
    TMAP_B_ok HTW TMAP_B_g_ncmd ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as V.
  rewrite !Z.add_0_r in V. rewrite Z.add_0_l. exact V. }
assert (V40 : YI04.val_mem segs (mrestrict (w_H W) mem) (0 + TB_g_nq) 4 (TW.g_nq Bw)).
{ pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B Bw TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 4
    TMAP_B_ok HTW TMAP_B_g_nq ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)) as V.
  rewrite !Z.add_0_r in V. rewrite Z.add_0_l. exact V. }
change (YK11.getr regs (Z_to_bv 5 20)) with (YK11.getr regs 20) in R20.
change (YK11.getr regs (Z_to_bv 5 25)) with (YK11.getr regs 25) in R25.
change (YK11.getr regs (Z_to_bv 5 27)) with (YK11.getr regs 27) in R27.
pose proof (o4_entry2 (fx := l_fx cx) W regs mem (lc_sp1 cx) (lc_F cx) serial tn fin (TW.u_at Bw TW.OFF_g_ncmd 4)
  (TW.g_nq Bw) (TB_g_q + 4 * TW.g_nq Bw) 0 0 (2 ^ 32 - 1) (2 ^ 32 - 1) 0 1023 (2 ^ 32 - 1) R2 R9 R26 R20 R27 R25
  Hsp1b Hsp1al HF4096 HFal HFceil Hs Htn Hfin Hncmd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S8 S16 S32 S56 S64 S144
  V39) as HS.
set (E2 := o4_E regs 0 tn fin serial 0 0 0 (TW.u_at Bw TW.OFF_g_ncmd 4) (TW.g_nq Bw) (TB_g_q + 4 * TW.g_nq Bw) 0 0)
  in HS.
assert (HEI : img_env VAL A_LIM E2) by (unfold E2; apply o4_env_img).
assert (E2lo : forall n, (n < 1024)%nat -> ew E2 n = ew E2 n) by (intros; reflexivity).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr regs r)
  by (intros n r Hn'; unfold E2; apply o4_ew_r; exact Hn').
assert (EX : forall j, (j < 12)%nat -> ew E2 (32 + j) =
  nth j (o4_extra 0 tn fin serial 0 0 0 (TW.u_at Bw TW.OFF_g_ncmd 4) (TW.g_nq Bw) (TB_g_q + 4 * TW.g_nq Bw) 0 0)
    (Z_to_bv 64 0))
  by (intros j Hj; unfold E2; apply o4_ew_x; exact Hj).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. pose proof (EX 7%nat ltac:(lia)) as E39.
pose proof (EX 8%nat ltac:(lia)) as E40. pose proof (EX 9%nat ltac:(lia)) as E41.
cbn [Nat.add nth o4_extra] in E33, E34, E35, E39, E40, E41. clear EX.
assert (EQ21 : ew E2 (A_OBJ 21) = Z_to_bv 64 TB_g_q) by (unfold E2; rewrite o4_ew_obj by lia; rewrite VQ; reflexivity).
assert (E25 : ew E2 25 = w64 (2 ^ 32 - 1)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E26 : ew E2 26 = w64 SHADOW_OFF) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (U9 : bv_unsigned (ew E2 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U40 : bv_unsigned (ew E2 40) = TW.g_nq Bw) by (rewrite E40; unfold w64; apply unsigned_lit_small; lia).
(* g_nq's cell joins the state *)
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
  assert (Hdis : all_disjoint E2 o4_rg_nq (ss_mem s)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_nq, o4_rg_sp2, o4_rg_ncmd.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
  unfold TB_g_nq, TB_g_ncmd in *. repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region (PI := PI_transportb) E2 _ _ o4_rg_nq HS ltac:(vm_compute; reflexivity)
  (o4_rgabs_ok E2 _ 40 TB_g_nq _ U40 ltac:(lia) ltac:(unfold TB_g_nq; lia) ltac:(unfold TB_g_nq; lia)
     o4_inG_nq V40) Hdis) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (SHOK : sh_ok segs O4_Bx [] E2 (mrestrict (w_H W) mem)) by apply Forall_nil.
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
clear HSAV HIN HFpres HFL.
(* run A1, +0x155c: `sext.w a0, s9` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ o4_awr2 ltac:(fun H => idtac). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EA EAlo E2lo HEIA.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) -> ~ (TB_g_nq <= a < TB_g_nq + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2.
  apply (kept_of_frame E2 _ (w_H W) mem (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_nq <= x < TB_g_nq + 4) HFr);
    [|exact Ha | intros [Hx|Hx]; [exact (Hn Hx) | exact (Hn2 Hx)]].
  intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; unfold TB_g_ncmd, TB_g_nq; first [lia | left; lia | right; lia]). }
assert (GA1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
rename ms into ms1, md1 into mdA, K1 into KA1, GA1 into GAA.
(* +0x1560: `bltz a0`, taken (at = -1) *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
2: { exfalso. rewrite (o4_br_app _ ltac:(rewrite EAlo by lia; exact E25)) in Hc. discriminate Hc. }
clear Hc.
(* run A2, +0x15e8 .. +0x160c: g_nq + 1, its index test (decided), g_q + 4 g_nq *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ o4_awr2 ltac:(fun H => idtac). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EB EBlo EAlo HEIB.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) -> ~ (TB_g_nq <= a < TB_g_nq + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2. rewrite <- (KA1 a Ha Hn Hn2).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms1) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_nq <= x < TB_g_nq + 4) HFr);
    [|exact Ha | intros [Hx|Hx]; [exact (Hn Hx) | exact (Hn2 Hx)]].
  intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; unfold TB_g_ncmd, TB_g_nq; first [lia | left; lia | right; lia]). }
assert (GA2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GAA a Ha))).
clear HF HFr HG KA1 GAA.
rename ms into ms2, md1 into mdB.
(* +0x1610: the wrap test of g_q + 4 g_nq, refuted *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
{ exfalso.
  pose proof (o4_trap_q _ 40 (TW.g_nq Bw) ltac:(rewrite EBlo by (unfold A_OBJ; lia); exact EQ21)
    ltac:(rewrite EBlo by lia; exact E40) Hnq) as T.
  change (A_OBJ 21) with 262%nat in T. rewrite T in Hc. discriminate Hc. }
clear Hc.
(* run A3, to +0x1618: a0 = g_q + 4 g_nq *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_GQA.
{ o4_awr2 ltac:(fun H => idtac). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EC EClo EBlo HEIC.
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) -> ~ (TB_g_nq <= a < TB_g_nq + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2. rewrite <- (K2 a Ha Hn Hn2).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms2) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_nq <= x < TB_g_nq + 4) HFr);
    [|exact Ha | intros [Hx|Hx]; [exact (Hn Hx) | exact (Hn2 Hx)]].
  intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; unfold TB_g_ncmd, TB_g_nq; first [lia | left; lia | right; lia]). }
assert (GA3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA2 a Ha))).
clear HF HFr HG K2 GA2.
rename ms into ms3, md1 into mdC.
o4_reg HS (Z_to_bv 5 10) (w64 (TB_g_q + 4 * TW.g_nq Bw)) R10
  ltac:(exact (o4_den_gq EC 40 (TW.g_nq Bw) ltac:(rewrite EClo by (unfold A_OBJ; lia); exact EQ21)
                ltac:(rewrite EClo by lia; exact E40) Hnq)).
assert (E41x : ew EC 41 = w64 (TB_g_q + 4 * TW.g_nq Bw)) by (rewrite EClo by lia; exact E41).
pose proof (o4_set_reg EC _ _ (Z_to_bv 5 10) 41 HS ltac:(rewrite E41x; exact R10) eq_refl) as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
assert (U41 : bv_unsigned (ew EC 41) = TB_g_q + 4 * TW.g_nq Bw)
  by (rewrite E41x; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U9b : bv_unsigned (ew EC 9) = lc_sp1 cx) by (rewrite EClo by lia; exact U9).
lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
  assert (Hdis2 : all_disjoint EC (o4_rg_q []) (ss_mem s)) end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_q, o4_rg_nq, o4_rg_sp2, o4_rg_ncmd.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U41, U9b.
  unfold TB_g_q, TB_g_nq, TB_g_ncmd in *. repeat split; first [exact I | lia]. }
pose proof (st_ok_pi_add_region (PI := PI_transportb) EC _ _ (o4_rg_q []) HS ltac:(vm_compute; reflexivity)
  (o4_rgw_ok EC _ 41 (TB_g_q + 4 * TW.g_nq Bw) 0 4 U41 ltac:(unfold TB_g_q; lia) ltac:(unfold TB_g_q; lia)
     ltac:(lia) ltac:(intros o Ho; apply o4_inG_q; lia)) Hdis2) as HS2.
clear HS. rename HS2 into HS.
pose proof (st_ok_pi_add_fact (PI := PI_transportb) EC _ _ 41 (mkAF TB_g_q (TB_g_q + 4092) 2) HS
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U41; change (2 ^ 2) with 4;
        split; [lia|]; split; [unfold TB_g_q; replace (6232192 + 4 * TW.g_nq Bw) with ((1558048 + TW.g_nq Bw) * 4)
                                 by ring; apply Z_mod_mult | lia]))
  as HS2.
clear HS. rename HS2 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR3.
assert (SHQ : sh_ok segs O4_Bx O4_SHQ EC (mrestrict (w_H W) (ms_mem ms3))).
{ unfold sh_ok, O4_SHQ. constructor; [|constructor].
  destruct (o4_q_blk (TW.g_nq Bw) Hnq) as [Hb1 Hb2].
  apply (o4_shent B ly S W (ms_mem ms3) mdC EC 41 (TB_g_q + 4 * TW.g_nq Bw) 0 4 TB_g_q (TB_g_q + TW.SZ_g_q) HAR3 HZq
    ltac:(rewrite EClo by lia; exact E26) E41x).
  - lia.
  - exact Hb1.
  - unfold TW.SZ_g_q. exact Hb2.
  - unfold TB_g_q. lia.
  - unfold TB_g_q, SHADOW_OFF. lia. }
clear SHOK. rename SHQ into SHOK.
(* run A4, +0x1618 .. +0x1650: the shadow test of g_q[g_nq], g_q[g_nq] = serial, s4, g_ncmd + 1, s11, s6 *)
paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_S4.
{ o4_awr2 ltac:(fun H => rewrite ?U41 in H). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
o4_env HS E2 EF EFlo EClo HEIF.
assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) -> ~ (TB_g_nq <= a < TB_g_nq + 4) ->
  ~ (TB_g_q + 4 * TW.g_nq Bw <= a < TB_g_q + 4 * TW.g_nq Bw + 4) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ intros a Ha Hn Hn2 Hn3. rewrite <- (K3 a Ha Hn Hn2).
  apply (kept_of_frame _ _ (w_H W) (ms_mem ms3) (ms_mem ms)
    (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4 \/ TB_g_nq <= x < TB_g_nq + 4 \/
              TB_g_q + 4 * TW.g_nq Bw <= x < TB_g_q + 4 * TW.g_nq Bw + 4) HFr);
    [|exact Ha | intros [Hx|[Hx|Hx]]; [exact (Hn Hx) | exact (Hn2 Hx) | exact (Hn3 Hx)]].
  intros b wlo whi x Hin Hx.
  o4_win Hin Hx ltac:(cbv beta; rewrite ?U41, ?U9b in Hx; unfold TB_g_ncmd, TB_g_nq;
    first [lia | left; lia | right; left; lia | right; right; lia]). }
assert (GAF : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG (GA3 a Ha))).
clear HF HFr HG K3 GA3.
(* the stored bytes, from the final chunks *)
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 0 _ HS eq_refl) as RGq.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 1 _ HS eq_refl) as RGa.
pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 3 _ HS eq_refl) as RGn.
cbn [ms_mem restrict] in RGq, RGa, RGn.
destruct RGq as (_ & _ & _ & Cq). destruct RGa as (_ & _ & _ & Ca). destruct RGn as (_ & _ & _ & Cn).
cbn [YP09.r_chunks YP09.r_base base_val] in Cq, Ca, Cn.
apply Forall_inv in Cq. apply Forall_inv in Ca. apply Forall_inv in Cn.
assert (U41F : bv_unsigned (ew EF 41) = TB_g_q + 4 * TW.g_nq Bw)
  by (rewrite EFlo by lia; rewrite E41; unfold w64; apply unsigned_lit_small; unfold TB_g_q; lia).
assert (U35F : bv_unsigned (ew EF 35) = serial)
  by (rewrite EFlo by lia; rewrite E35; unfold w64; apply unsigned_lit_small; lia).
assert (U39F : bv_unsigned (ew EF 39) = TW.u_at Bw TW.OFF_g_ncmd 4)
  by (rewrite EFlo by lia; rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (U40F : bv_unsigned (ew EF 40) = TW.g_nq Bw) by (rewrite EFlo by lia; exact U40).
rewrite U41F in Cq.
assert (Vqs : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms) (TB_g_q + 4 * TW.g_nq Bw + Z.of_nat j) = Some (YO0f.le_byte serial 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) _ 0 4 4 _ (serial + 0) Cq eq_refl ltac:(lia)
    (o4_den_off EF 35 _ 4 0 U35F ltac:(lia)) j Hj) as Hb. rewrite !Z.add_0_r in Hb. exact Hb. }
assert (Vnq : forall j, (j < 4)%nat ->
  aview segs (w_H W) (ms_mem ms) (TB_g_nq + Z.of_nat j) = Some (YO0f.le_byte (TW.g_nq Bw + 1) 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) 0 TB_g_nq 4 4 _ (TW.g_nq Bw + 1) Ca eq_refl ltac:(lia)
    (o4_den_off EF 40 _ 4 1 U40F ltac:(lia)) j Hj) as Hb. rewrite Z.add_0_l in Hb. exact Hb. }
assert (VN : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem ms) (TB_g_ncmd + Z.of_nat j) =
  Some (YO0f.le_byte (TW.u_at Bw TW.OFF_g_ncmd 4 + 1) 4 j)).
{ intros j Hj. pose proof (o4_chunk_bytes EF (w_H W) (ms_mem ms) 0 TB_g_ncmd 4 4 _
    (TW.u_at Bw TW.OFF_g_ncmd 4 + 1) Cn eq_refl ltac:(lia) (o4_den_inc EF 39 _ U39F) j Hj) as Hb.
  rewrite Z.add_0_l in Hb. exact Hb. }
clear Cq Ca Cn.
assert (HTWF : lc_tw W (ms_mem ms)
  (o4_b7 (TW.set_g_nq (TW.set_Q_at Bw (TW.g_nq Bw) serial) ((TW.g_nq Bw + 1) mod 2 ^ 32)))).
{ apply (o4_w_app Bw (aview segs (w_H W) mem) (aview segs (w_H W) (ms_mem ms)) serial HTW Hnq Vnq Vqs VN).
  intros x Hx Hn1 Hn2 Hn3. pose proof (o4_GL x (o4_tw_in_G x Hx)) as Hl.
  apply KF; [lia | exact Hn3 | exact Hn1 | exact Hn2]. }
(* the registers *)
assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
  YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS);
      lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
      rewrite o4_den_atom, EFlo by lia; apply EE; reflexivity |]).
  destruct Hr. }
assert (R24F : YK11.getr (ms_regs ms) (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off c5)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite o4_den_atom, EFlo by lia. rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl). exact R24. }
assert (R27F : YK11.getr (ms_regs ms) (Z_to_bv 5 27) = w64 (TOP.fi_n c5)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite (o4_den_sub _ 34 33 fin tn); [rewrite Hfi5; reflexivity | |]; rewrite EFlo by lia; assumption. }
assert (R20F : YK11.getr (ms_regs ms) 20 = w64 (lc_F cx + 32)).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  rewrite o4_den_atom, EFlo by lia. rewrite (EE 20%nat 20%bv eq_refl). exact R20. }
assert (R22F : YK11.getr (ms_regs ms) 22 = w64 1).
{ rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms _ HS).
  lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
  reflexivity. }
assert (HLF : lc_lcore B MT cx op true false (lo_k op) ly S W (ms_regs ms) (ms_mem ms) md1 e).
{ apply (o4_lcore_keep cx op true false (lo_k op) ly S W regs mem md e (ms_regs ms) (ms_mem ms) md1 0
    HB LAWS HL HJ KR ltac:(lia)).
  - intros a Ha HnG _. apply KF; [exact Ha | intros Hn; apply HnG; apply o4_inG_ncmd; exact Hn
      | intros Hn; apply HnG; apply o4_inG_nq; exact Hn
      | intros Hn; apply HnG; apply o4_inG_q; unfold TB_g_q in *; lia].
  - exact GAF. }
pmkst HS.
apply SRr_ret.
refine (o4_close cx op ly S W (ms_regs ms) (ms_mem ms) md1 e _ c5 _ _ HLF Hopc HTWF HSET HOP
  (conj R24F R27F) (conj R20F R22F)).
rewrite VB. reflexivity.
Qed.


Lemma lc_op4st_ok : lc_op4st_stmt B MT XL RLO RHI.
Proof.
intros HP cx op W' c' HB HCW.
destruct HCW as (ly' & S' & regs' & mem' & md' & e & B1 & at_ & B3 & rc0 & B4 & B5 & HCW).
cbv zeta in HCW.
destruct HCW as (-> & Hopc & HL & HOB & HRAW & Hser & HAT & HSUB & HREF & HLAT & HTW & HCS & S0 & S16 & S8 & S64 &
  R22 & R25 & R24 & R27 & R20).
pose proof HL as (HC0 & HFR & HSP & HFSH & HOK & He & HMT & R19).
pose proof HOK as (HAG & Hops & HFI & Hfin0 & Hk).
pose proof (o4_model (l_pl cx) (lo_B op) B1 B3 B4 B5 (lo_c op) (lo_k op) (lo_ops op) at_ rc0 HAG Hops HFI Hfin0 Hopc
  HOB HRAW Hser HAT HSUB HREF HLAT) as HM.
cbv zeta in HM.
pose proof (o4_tag_facts (l_pl cx) B1 (lo_c op) HFI) as HTF. cbv zeta in HTF.
pose proof (o4_kd_facts (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) as HKD.
pose proof (o4_at_range _ _ _ HAT) as HATR.
pose proof (o4_want_cases (lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))))) at_)
  as HWC.
set (kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) in *.
set (tv := lc_tag_vals (l_pl cx) B1 (sv_c kd)) in *.
set (want := lc_want tv at_) in *.
destruct HTF as (Hlen & Hcb & Hntk & Hoff4 & Hfi4 & Hn4 & Hoff5 & Hfi5).
destruct HKD as (Hkey & Hdisp).
destruct HM as (HMrep & HMapp & HSET & HOP).
pose proof (lp_laws B MT XL RLO RHI HP) as LAWS.
pose proof (lp_settle_cells B MT XL RLO RHI HP) as HSC.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned B MT XL RLO RHI HP)) as HGX.
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W' regs' mem' md' e HB HC0) as GEO.
destruct GEO as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hnl Hinb Hlive].
pose proof HC0 as (HJ & Hfrs & HlyF & HPERM & R2 & R8 & R9 & R3 & R4 & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
pose proof HFR as (R18 & R26).
pose proof YM05.alloc_ceiling_value as Hce.
assert (Hs : 0 <= tg_serial tv < 1024) by (unfold TC.CMDS_MAX in Hser; lia).
pose proof (o4_spill_get cx _ 32 (transportb_hi 14) HSP ltac:(o4_in)) as S32.
pose proof (o4_spill_get cx _ 56 (transportb_hi 15) HSP ltac:(o4_in)) as S56.
pose proof (o4_spill_get cx _ 144 (lc_F cx + 32) HSP ltac:(o4_in)) as S144.
destruct (o4_vals) as (VQ & VB & VH14 & VH15 & VNQ & VNC).
rewrite <- VH14 in S32. rewrite <- VH15 in S56.
pose proof (o4_c_vals _ (lc_F cx + 32) (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd) HCS Hcb
  ltac:(lia) ltac:(destruct Hdisp as [Hd|Hd]; rewrite Hd; lia)) as (Vlen & Vdisp & Vkey).
pose proof (o4_rdword_range _ _ _ _ S16) as Hfin.
pose proof (o4_rdword_range _ _ _ _ S8) as Htn.
pose proof (TWL.u_at_range B5 TW.OFF_g_ncmd 4) as Hncmd. change (8 * Z.of_nat 4) with 32 in Hncmd.
unfold LF_FBYTES in HFceil.
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
assert (Hsp1b : YM05.alloc_ceiling + 32432 <= lc_sp1 cx <= 2 ^ 47 - 320)
  by (unfold LF_FRAME in Hsp1; destruct Hsp1 as [Hsp1a Hsp1b']; split; [exact Hsp1c | lia]).
pose proof (o4_entry1 (fx := l_fx cx) W' regs' mem' (lc_sp1 cx) (lc_F cx) (tg_serial tv) (tg_n tv)
  (TOP.fi_n (tg_c4 tv)) (sv_key kd) (sv_display kd) (tg_len tv) (TW.u_at B5 TW.OFF_g_ncmd 4)
  R2 R9 R26 R20 Hsp1b Hsp1al HF4096 HFal HFceil Hs Htn Hfin Hkey
  ltac:(destruct Hdisp as [Hd|Hd]; rewrite Hd; lia) ltac:(lia) Hncmd ltac:(rewrite Z.add_0_r; exact S0) S8 S16 S32 S56
  S64 S144 Vlen Vdisp Vkey) as HS.
set (E1 := o4_E regs' (TB_g_cmd + 40 * tg_serial tv) (tg_n tv) (TOP.fi_n (tg_c4 tv)) (tg_serial tv) (sv_key kd)
  (sv_display kd) (tg_len tv) (TW.u_at B5 TW.OFF_g_ncmd 4) 0 0 0 0) in HS.
assert (HEI : img_env VAL A_LIM E1) by (unfold E1; apply o4_env_img).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = YK11.getr regs' r)
  by (intros n r Hn'; unfold E1; apply o4_ew_r; exact Hn').
assert (EX : forall j, (j < 12)%nat -> ew E1 (32 + j) =
  nth j (o4_extra (TB_g_cmd + 40 * tg_serial tv) (tg_n tv) (TOP.fi_n (tg_c4 tv)) (tg_serial tv) (sv_key kd)
    (sv_display kd) (tg_len tv) (TW.u_at B5 TW.OFF_g_ncmd 4) 0 0 0 0) (Z_to_bv 64 0))
  by (intros j Hj; unfold E1; apply o4_ew_x; exact Hj).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
pose proof (EX 6%nat ltac:(lia)) as E38. pose proof (EX 7%nat ltac:(lia)) as E39.
cbn [Nat.add nth o4_extra] in E32, E33, E34, E35, E36, E37, E38, E39. clear EX.
assert (U9 : bv_unsigned (ew E1 9) = lc_sp1 cx)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E1 20) = lc_F cx + 32)
  by (rewrite (EE 20%nat 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E1 32) = TB_g_cmd + 40 * tg_serial tv)
  by (rewrite E32; unfold w64; apply unsigned_lit_small; unfold TB_g_cmd; lia).
assert (U39 : bv_unsigned (ew E1 39) = TW.u_at B5 TW.OFF_g_ncmd 4)
  by (rewrite E39; unfold w64; apply unsigned_lit_small; lia).
assert (E22 : ew E1 22 = w64 want) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (HWC' : want = 0 \/ want = -10 \/ want = -5)
  by (unfold DSpec.SPEC_OK, DSpec.SPEC_E_REFUSED, DSpec.SPEC_E_SPACE in HWC; exact HWC).
(* the shadow entry of g_cmd[serial]'s 40 bytes *)
pose proof HSC as (_ & _ & HZq & HZc).
assert (SHOK : sh_ok segs O4_Bx O4_SH1 E1 (mrestrict (w_H W') mem')).
{ unfold sh_ok, O4_SH1. constructor; [|constructor].
  destruct (o4_cmd_blk (tg_serial tv) 0 40 Hs ltac:(lia) ltac:(lia)) as [Hb1 Hb2].
  apply (o4_shent B ly' S' W' mem' md' E1 32 (TB_g_cmd + 40 * tg_serial tv) 0 40 TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd)
    HAR HZc ltac:(rewrite (EE 26%nat 26%bv eq_refl); exact R26) E32).
  - lia.
  - exact Hb1.
  - unfold TW.SZ_g_cmd. exact Hb2.
  - unfold TB_g_cmd. lia.
  - unfold TB_g_cmd, SHADOW_OFF. lia. }
(* the frame is no byte of G *)
assert (HFG : forall x, lc_F cx <= x < lc_F cx + 256 -> ~ inG TG.G_HARNESS_B x).
{ intros x Hx HGx. apply (frm_img segs B LAWS ly' S' W' mem' md' LF_CID (l_fpos cx) x HAR HFin);
    [rewrite HFaddr; change (fs_frame_bytes LF_CID) with 256; lia | exact (trans_g_img _ HGx)]. }
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
unfold lc_cfg.
replace (w64 (transportb_text + LO_CMDW)) with (Z_to_bv 64 (BASE + LO_CMDW)) by (rewrite VB; reflexivity).
(* +0x14cc: `bnez s6` *)
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* want <> SPEC_OK: g_ncmd + 1 only *)
  rewrite (o4_br_want E1 want E22 HWC') in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rename Hc into Hw0.
  assert (V39 : YI04.val_mem segs (mrestrict (w_H W') mem') (0 + TB_g_ncmd) 4 (TW.u_at B5 TW.OFF_g_ncmd 4)).
  { pose proof (tw_read_val segs (mrestrict (w_H W') mem') TMAP_B B5 TW.OFF_g_ncmd TB_g_ncmd TW.SZ_g_ncmd 0 4
      TMAP_B_ok HTW TMAP_B_g_ncmd ltac:(lia) ltac:(unfold TW.SZ_g_ncmd; lia)) as V.
    rewrite !Z.add_0_r in V. rewrite Z.add_0_l. exact V. }
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (Hdis : all_disjoint E1 o4_rg_ncmd (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_ncmd.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U20.
    pose proof (o4_apart_G (lc_F cx) TB_g_ncmd 4 HFG o4_inG_ncmd ltac:(lia)) as Hap.
    unfold TB_g_ncmd in *. split; [lia | split; [lia | exact I]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transportb) E1 _ _ o4_rg_ncmd HS ltac:(vm_compute; reflexivity)
    (o4_rgabs_ok E1 _ 39 TB_g_ncmd _ U39 Hncmd ltac:(unfold TB_g_ncmd; lia) ltac:(unfold TB_g_ncmd; lia)
       o4_inG_ncmd V39) Hdis) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  (* run W, +0x1634 .. +0x1650: g_ncmd + 1, s11, s6 = 1 *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_S4.
  { o4_awr U39. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
  o4_low HS E1 HEX.
  assert (KW : forall a, 0 <= a < 2 ^ 64 -> ~ (TB_g_ncmd <= a < TB_g_ncmd + 4) ->
    aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
  { intros a Ha Hn.
    apply (kept_of_frame E1 _ (w_H W') mem' (ms_mem ms) (fun x => TB_g_ncmd <= x < TB_g_ncmd + 4) HFr);
      [|exact Ha | exact Hn].
    intros b wlo whi x Hin Hx. o4_win Hin Hx ltac:(cbv beta; rewrite ?U9, ?U20 in Hx; unfold TB_g_ncmd; lia). }
  pose proof (st_ok_pi_region_nth (PI := PI_transportb) _ _ _ 0 _ HS eq_refl) as RG.
  cbn [ms_mem restrict] in RG. destruct RG as (_ & _ & _ & RGc).
  cbn [YP09.r_chunks YP09.r_base base_val] in RGc. apply Forall_inv in RGc.
  assert (U39x : bv_unsigned (ew _ 39) = TW.u_at B5 TW.OFF_g_ncmd 4) by (try (rewrite HEX by lia); exact U39).
  assert (VN : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms) (TB_g_ncmd + Z.of_nat j) =
    Some (YO0f.le_byte (TW.u_at B5 TW.OFF_g_ncmd 4 + 1) 4 j)).
  { intros j Hj. pose proof (o4_chunk_bytes _ (w_H W') (ms_mem ms) 0 TB_g_ncmd 4 4 _
      (TW.u_at B5 TW.OFF_g_ncmd 4 + 1) RGc eq_refl ltac:(lia) (o4_den_inc _ 39 _ U39x) j Hj) as Hb.
    rewrite Z.add_0_l in Hb. exact Hb. }
  assert (HTWF : lc_tw W' (ms_mem ms) (o4_b7 B5)).
  { apply (o4_w_ncmd B5 (aview segs (w_H W') mem') (aview segs (w_H W') (ms_mem ms)) HTW VN).
    intros x Hx Hn. pose proof (o4_GL x (o4_tw_in_G x Hx)) as Hl. apply KW; [lia | exact Hn]. }
  rewrite (o4_b6_skip B5 _ want at_ (tg_serial tv) Hw0) in HSET, HOP.
  (* the registers *)
  assert (KR : forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ rewrite (st_ok_pi_restrict_reg (w_H W') _ _ ms _ HS);
        lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        rewrite o4_den_atom; try (rewrite HEX by lia); apply EE; reflexivity |]).
    destruct Hr. }
  assert (R24F : YK11.getr (ms_regs ms) (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off (tg_c tv))).
  { rewrite (st_ok_pi_restrict_reg (w_H W') _ _ ms _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    rewrite o4_den_atom; try (rewrite HEX by lia). rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl). exact R24. }
  assert (R27F : YK11.getr (ms_regs ms) (Z_to_bv 5 27) = w64 (TOP.fi_n (tg_c tv))).
  { rewrite (st_ok_pi_restrict_reg (w_H W') _ _ ms _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    rewrite (o4_den_sub _ 34 33 (TOP.fi_n (tg_c4 tv)) (tg_n tv)); [rewrite Hfi5; reflexivity | |];
      try (rewrite HEX by lia); assumption. }
  assert (R20F : YK11.getr (ms_regs ms) 20 = w64 (lc_F cx + 32)).
  { rewrite (st_ok_pi_restrict_reg (w_H W') _ _ ms _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    rewrite o4_den_atom; try (rewrite HEX by lia). rewrite (EE 20%nat 20%bv eq_refl). exact R20. }
  assert (R22F : YK11.getr (ms_regs ms) 22 = w64 1).
  { rewrite (st_ok_pi_restrict_reg (w_H W') _ _ ms _ HS).
    lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end.
    reflexivity. }
  (* the loop facts at the final memory *)
  assert (HLF : lc_lcore B MT cx op true false (lo_k op) ly' S' W' (ms_regs ms) (ms_mem ms) md1 e).
  { apply (o4_lcore_keep cx op true false (lo_k op) ly' S' W' regs' mem' md' e (ms_regs ms) (ms_mem ms) md1 0
      HB LAWS HL HJ KR ltac:(lia)).
    - intros a Ha HnG _. apply KW; [exact Ha | intros Hn; apply HnG; apply o4_inG_ncmd; exact Hn].
    - intros a Ha. exact (apresent_grows _ _ _ a HG Ha). }
  pmkst HS.
  apply SRr_ret.
  refine (o4_close cx op ly' S' W' (ms_regs ms) (ms_mem ms) md1 e (o4_b7 B5) (tg_c tv) _ _ HLF Hopc HTWF HSET HOP
    (conj R24F R27F) (conj R20F R22F)).
  rewrite VB. reflexivity.
- (* want = SPEC_OK: the stores of g_cmd[serial], the copy, then the replace or the append *)
  rewrite (o4_br_want E1 want E22 HWC') in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hw0.
  pose proof (o4_apart_G (lc_F cx) (TB_g_cmd + 40 * tg_serial tv) 40 HFG
    ltac:(intros x Hx; apply o4_inG_cmd; unfold TB_g_cmd in *; lia) ltac:(lia)) as HapC.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (HdisA : all_disjoint E1 o4_rg_cmda (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_cmda.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U20.
    unfold TB_g_cmd in *. split; [lia | split; [lia | exact I]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transportb) E1 _ _ o4_rg_cmda HS ltac:(vm_compute; reflexivity)
    (o4_rgw_ok E1 _ 32 (TB_g_cmd + 40 * tg_serial tv) 0 12 U32 ltac:(unfold TB_g_cmd; lia)
       ltac:(unfold TB_g_cmd; lia) ltac:(lia) ltac:(intros o Ho; apply o4_inG_cmd; unfold TB_g_cmd in *; lia))
    HdisA) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ =>
    assert (HdisB : all_disjoint E1 o4_rg_cmdb (ss_mem s)) end.
  { cbn [ss_mem all_disjoint]. unfold extent_disjoint, o4_rg_cmdb.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U20.
    unfold TB_g_cmd in *. split; [lia | split; [lia | split; [lia | exact I]]]. }
  pose proof (st_ok_pi_add_region (PI := PI_transportb) E1 _ _ o4_rg_cmdb HS ltac:(vm_compute; reflexivity)
    (o4_rgw_ok E1 _ 32 (TB_g_cmd + 40 * tg_serial tv) 36 37 U32 ltac:(unfold TB_g_cmd; lia)
       ltac:(unfold TB_g_cmd; lia) ltac:(lia) ltac:(intros o Ho; apply o4_inG_cmd; unfold TB_g_cmd in *; lia))
    HdisB) as HS2.
  clear HS. rename HS2 into HS.
  lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.
  (* run 0, +0x14d0 .. +0x1558: the index and pointer tests (decided), the four checked stores into g_cmd[serial],
     the copy's arguments, `jal __asan_memcpy` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { o4_awr U32. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md1 := mdx) in * end. clearbody md1.
  o4_low HS E1 HEX.
  (* run 0 changed g_cmd[serial]'s two stretches only *)
  assert (KB1 : forall a, 0 <= a < 2 ^ 64 ->
    ~ (TB_g_cmd + 40 * tg_serial tv <= a < TB_g_cmd + 40 * tg_serial tv + 12) ->
    a <> TB_g_cmd + 40 * tg_serial tv + 36 -> aview segs (w_H W') (ms_mem ms) a = aview segs (w_H W') mem' a).
  { intros a Ha Hn1 Hn2.
    apply (kept_of_frame E1 _ (w_H W') mem' (ms_mem ms)
      (fun x => TB_g_cmd + 40 * tg_serial tv <= x < TB_g_cmd + 40 * tg_serial tv + 12 \/
                x = TB_g_cmd + 40 * tg_serial tv + 36) HFr);
      [|exact Ha | intros [Hx|Hx]; [exact (Hn1 Hx) | exact (Hn2 Hx)]].
    intros b wlo whi x Hin Hx.
    o4_win Hin Hx ltac:(cbv beta; rewrite ?U9, ?U20, ?U32 in Hx; first [lia | left; lia | right; lia]). }
  lazymatch type of HS with OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ =>
    set (Eb := Ex) in * end.
  assert (U32b : bv_unsigned (ew Eb 32) = TB_g_cmd + 40 * tg_serial tv) by (try (rewrite HEX by lia); exact U32).
  assert (U20b : bv_unsigned (ew Eb 20) = lc_F cx + 32) by (try (rewrite HEX by lia); exact U20).
  assert (U36b : bv_unsigned (ew Eb 36) = sv_key kd)
    by (try (rewrite HEX by lia); rewrite E36; unfold w64; apply unsigned_lit_small; lia).
  assert (U37b : bv_unsigned (ew Eb 37) = sv_display kd)
    by (try (rewrite HEX by lia); rewrite E37; unfold w64; apply unsigned_lit_small; destruct Hdisp as [Hd|Hd]; rewrite Hd; lia).
  assert (U38b : bv_unsigned (ew Eb 38) = tg_len tv)
    by (try (rewrite HEX by lia); rewrite E38; unfold w64; apply unsigned_lit_small; lia).
  assert (HEIb : img_env VAL A_LIM Eb)
    by (intros n Hn; try (rewrite HEX by (unfold A_TEXT, A_LIM in *; lia)); exact (HEI n Hn)).
  (* the stored bytes, from the chunks of the run's last state *)
  pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as RGb. cbn [ms_mem restrict] in RGb.
  pose proof (st_ok_region_nth _ _ _ 1 _ HS eq_refl) as RGa. cbn [ms_mem restrict] in RGa.
  destruct RGb as (_ & _ & _ & HCb). destruct RGa as (_ & _ & _ & HCa).
  cbn [YP09.r_chunks YP09.r_base base_val] in HCa, HCb. rewrite U32b in HCa, HCb.
  pose proof (Forall_inv HCb) as Cl.
  pose proof (Forall_inv HCa) as Cd. pose proof (Forall_inv (Forall_inv_tail HCa)) as Ck.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCa))) as Cs.
  clear HCa HCb.
  assert (Vst0 : forall j, (j < 4)%nat -> aview segs (w_H W') (ms_mem ms) (TB_g_cmd + 40 * tg_serial tv + Z.of_nat j) =
    Some (YO0f.le_byte 1 4 j)).
  { intros j Hj. pose proof (o4_chunk_bytes Eb (w_H W') (ms_mem ms) _ 0 4 4 (SLit 1) 1 Cs eq_refl ltac:(lia)
      (o4_den_lit Eb 1 4 ltac:(lia)) j Hj) as Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (Vkey0 : forall j, (j < 4)%nat ->
    aview segs (w_H W') (ms_mem ms) (TB_g_cmd + 40 * tg_serial tv + 4 + Z.of_nat j) =
    Some (YO0f.le_byte (sv_key kd) 4 j)).
  { intros j Hj. exact (o4_chunk_bytes Eb (w_H W') (ms_mem ms) _ 4 4 4 _ (sv_key kd) Ck eq_refl ltac:(lia)
      (o4_den_sext Eb 36 _ U36b) j Hj). }
  assert (Vdisp0 : forall j, (j < 4)%nat ->
    aview segs (w_H W') (ms_mem ms) (TB_g_cmd + 40 * tg_serial tv + 8 + Z.of_nat j) =
    Some (YO0f.le_byte (sv_display kd) 4 j)).
  { intros j Hj. pose proof (o4_chunk_bytes Eb (w_H W') (ms_mem ms) _ 8 4 4 _ (sv_display kd + 0) Cd eq_refl
      ltac:(lia) (o4_den_off Eb 37 _ 4 0 U37b ltac:(lia)) j Hj) as Hb. rewrite Z.add_0_r in Hb. exact Hb. }
  assert (Vlen0 : aview segs (w_H W') (ms_mem ms) (TB_g_cmd + 40 * tg_serial tv + 36) =
    Some (YO0f.le_byte (tg_len tv) 1 0)).
  { pose proof (o4_chunk_bytes Eb (w_H W') (ms_mem ms) _ 36 1 1 _ (tg_len tv + 0) Cl eq_refl
      ltac:(lia) (o4_den_off Eb 38 _ 1 0 U38b ltac:(lia)) 0%nat ltac:(lia)) as Hb.
    cbn [Z.of_nat] in Hb. rewrite ?Z.add_0_r in Hb. exact Hb. }
  clear Cl Cd Ck Cs.
  (* the registers at the call of __asan_memcpy *)
  o4_reg HS (Z_to_bv 5 10) (w64 (TB_g_cmd + 40 * tg_serial tv + 12)) Ra0
    ltac:(cbn [sv_denot]; rewrite U32b; reflexivity).
  o4_reg HS (Z_to_bv 5 11) (w64 (lc_F cx + 32)) Ra1 ltac:(cbn [sv_denot]; rewrite U20b, Z.add_0_r; reflexivity).
  o4_reg HS (Z_to_bv 5 12) (w64 (tg_len tv)) Ra2 ltac:(cbn [sv_denot]; rewrite U38b, Z.add_0_r; reflexivity).
  o4_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + LO_RCPY)) Rra ltac:(apply codeptr_val; exact HEIb).
  o4_reg HS (2%bv : bv 5) (w64 (lc_sp1 cx)) Rsp
    ltac:(rewrite o4_den_atom; try (rewrite HEX by lia); rewrite (EE 2%nat 2%bv eq_refl); exact R2).
  o4_reg HS (3%bv : bv 5) (w64 (as_gp B)) Rgp
    ltac:(rewrite o4_den_atom; try (rewrite HEX by lia); rewrite (EE 3%nat 3%bv eq_refl); exact R3).
  o4_reg HS (4%bv : bv 5) (w64 (as_tp B)) Rtp
    ltac:(rewrite o4_den_atom; try (rewrite HEX by lia); rewrite (EE 4%nat 4%bv eq_refl); exact R4).
  assert (KRT : forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 24; 25; 26; 27] ->
    YK11.getr (ms_regs ms) (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ rewrite (st_ok_restrict_reg segs (w_H W') _ _ ms _ HS);
        lazymatch goal with |- sv_denot _ ?ee = _ => let e' := eval vm_compute in ee in change ee with e' end;
        rewrite o4_den_atom; try (rewrite HEX by lia); apply EE; reflexivity |]).
    destruct Hr. }
  assert (Usp : spZ (ms_regs ms) = lc_sp0 cx + (lc_sp1 cx - lc_sp0 cx)).
  { unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (EST : ESTACK = 4096) by reflexivity.
  (* the destination g_cmd[serial] + 12: its zero shadow *)
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARb.
  destruct (o4_cmd_blk (tg_serial tv) 12 (12 + tg_len tv) Hs ltac:(lia) ltac:(lia)) as [Hb1 Hb2].
  assert (Hb2' : (TB_g_cmd + 40 * tg_serial tv + 12 + tg_len tv - 1) / 64 * 64 + 64 <= TB_g_cmd + TW.SZ_g_cmd).
  { replace (TB_g_cmd + 40 * tg_serial tv + 12 + tg_len tv - 1)
      with (TB_g_cmd + 40 * tg_serial tv + (12 + tg_len tv) - 1) by lia.
    unfold TW.SZ_g_cmd. exact Hb2. }
  destruct (decode_zshadow_ra B ly' S' W' (ms_mem ms) md1 TB_g_cmd (TB_g_cmd + TW.SZ_g_cmd)
     (TB_g_cmd + 40 * tg_serial tv + 12) (tg_len tv) HARb HZc ltac:(lia) Hb1 Hb2') as (DRA & DHU).
  (* the source c: its shadow (c in scope) and its bytes *)
  assert (HSH : SHADOW_OFF <= lc_SH cx /\ lc_SH cx + 32 <= YM05.alloc_ceiling).
  { unfold lc_SH. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia) ltac:(lia)) as D0.
    assert (D1 : lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia). unfold SHADOW_OFF. lia. }
  assert (HFSHb : lc_fsh cx (aview segs (w_H W') (ms_mem ms)) true false).
  { apply (lc_fsh_kept cx (aview segs (w_H W') mem') _ true false); [|exact HFSH].
    intros a Ha. apply KB1; unfold SHADOW_OFF, TB_g_cmd in *; lia. }
  destruct (o4_c_src cx (aview segs (w_H W') (ms_mem ms)) (tg_len tv) HFSHb HF4096 HFal ltac:(lia)) as (SRA & SHU).
  pose proof (o4_F_range cx ly' S' W' regs' mem' md' e LAWS HB HC0) as FRg.
  assert (SRC : src_ok segs W' (ms_regs ms) (ms_mem ms) (lc_F cx + 32) (tg_len tv)).
  { intros a Ha. split.
    - rewrite (KB1 a ltac:(lia)) by (destruct HapC; lia).
      replace a with (lc_F cx + 32 + (a - (lc_F cx + 32))) by ring.
      exact (o4_c_some (w_H W') mem' (lc_F cx + 32) _ _ _ _ HCS Hcb (a - (lc_F cx + 32)) ltac:(lia)).
    - rewrite Usp. lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (mkCfg (@YK11.mkst (l_fx cx) rg (Z_to_bv 64 (transportb_sigma TB___asan_memcpy)) mm rom) mdx) Q)
  end.
  eapply SRr_bind.
  { apply (@gx_intrin_at (l_fx cx) rc tfib_sink_head segs B LAWS transportb_segs_low OCpy
      (transportb_sigma TB___asan_memcpy) (lp_memcpy B MT XL RLO RHI HP (l_fx cx)) TG.G_HARNESS_B W' (ms_regs ms)
      (ms_mem ms) _ _ _ _ _ _ _ _ _ ly' S' md1 e (TB_g_cmd + 40 * tg_serial tv + 12) (lc_F cx + 32) (tg_len tv)
      (lc_sp1 cx - lc_sp0 cx) (Z_to_bv 64 (BASE + LO_RCPY)) HGX G_HARNESS_B_rw HJ Ra0 Ra1 Ra2).
    - lia.
    - unfold TB_g_cmd; lia.
    - unfold TB_g_cmd; lia.
    - exact Usp.
    - exact (o4_mod16 _ _ Hsp1al Hsp0al).
    - unfold LF_FRAME in Hsp1. lia.
    - unfold LLVMF_STK, LF_FRAME in *. lia.
    - exact Rgp.
    - exact Rtp.
    - exact Rra.
    - apply (ret_ok_codeptr_v (PI := PI_transportb)); [unfold LO_RCPY; lia | reflexivity].
    - eapply (transport_twr_ok_g_intro segs B LAWS); [exact HJ|]. intros a Ha. right. apply o4_inG_cmd.
      unfold TB_g_cmd in *. lia.
    - unfold amem_range, kLowMemEnd, TB_g_cmd. left. lia.
    - exact DRA.
    - intros _. exact DHU.
    - cbv iota beta. split; [lia|]. split; [lia|]. split; [exact SRC|].
      split; [destruct HapC; lia|].
      split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd; destruct FRg; [left | right]; lia|].
      split; [exact SRA | intros _; exact SHU]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Hcopy & Heff & Hpres3).
  cbv iota in Hcopy.
  (* the call's side facts are spent: clear the divisions and disjunctions the kit's lia would split on *)
  clear Hb1 Hb2 Hb2' DRA DHU SRA SHU HSH HFSHb SRC FRg HWC' HARb.
  assert (Hdisp' : 0 <= sv_display kd <= 1) by (destruct Hdisp as [Hd|Hd]; rewrite Hd; lia). clear Hdisp.
  revert HATR.
  clear - HP HB LAWS HL HJ3 HP3 KRT Heff Hcopy Hpres3 HG KB1 EST Hsp1c Hsp1b Hce HF4096 HFceil Hs Hlen Hcb HTW Vst0 Vkey0 Vdisp0 Vlen0
    HapC HCS R25 R24 R27 R20 S8 S16 S64 Hw0 HSET HOP HMapp HMrep Hopc Hfi5 Hkey Hdisp'.
  (* what run 0 and the copy keep *)
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ inG TG.G_HARNESS_B a -> ~ (lc_sp1 cx - 4096 <= a < lc_sp1 cx) ->
    aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a).
  { intros a Ha HnG Hw.
    rewrite (Heff a Ha ltac:(intros Hx; apply HnG; apply o4_inG_cmd; unfold TB_g_cmd in *; lia)
      ltac:(rewrite EST; lia)).
    apply KB1; [exact Ha | intros Hx; apply HnG; apply o4_inG_cmd; unfold TB_g_cmd in *; lia
      | intros Hx; apply HnG; apply o4_inG_cmd; unfold TB_g_cmd in *; lia]. }
  assert (GA3 : forall a, apresent (w_H W') mem' a -> apresent (w_H W') mem3 a)
    by (intros a Ha; exact (Hpres3 a (apresent_grows _ _ _ a HG Ha))).
  assert (KR3 : forall r, In r [2; 3; 4; 8; 9; 18; 19; 26] ->
    YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HP3 r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KRT.
    cbn [In] in Hr |- *. tauto. }
  assert (HL3 : lc_lcore B MT cx op true false (lo_k op) ly' S' W' regs3 mem3 md3 e)
    by exact (o4_lcore_keep cx op true false (lo_k op) ly' S' W' regs' mem' md' e regs3 mem3 md3 4096 HB LAWS HL HJ3
      KR3 ltac:(lia) KC GA3).
  assert (RK : forall r, In r [20; 24; 25; 27] -> YK11.getr regs3 (Z_to_bv 5 r) = YK11.getr regs' (Z_to_bv 5 r)).
  { intros r Hr. rewrite (HP3 r ltac:(unfold acallee_saved; cbn [In] in Hr; lia)). apply KRT.
    cbn [In] in Hr |- *. tauto. }
  assert (R25' : YK11.getr regs3 (Z_to_bv 5 25) = w64 (at_ mod 2 ^ 32)) by (rewrite (RK 25 ltac:(cbn; tauto)); exact R25).
  assert (R24' : YK11.getr regs3 (Z_to_bv 5 24) = w64 (l_p cx + TOP.fi_off (tg_c tv)))
    by (rewrite (RK 24 ltac:(cbn; tauto)); exact R24).
  assert (R27' : YK11.getr regs3 (Z_to_bv 5 27) = w64 TB_g_cmd) by (rewrite (RK 27 ltac:(cbn; tauto)); exact R27).
  assert (R20' : YK11.getr regs3 (Z_to_bv 5 20) = w64 (lc_F cx + 32)) by (rewrite (RK 20 ltac:(cbn; tauto)); exact R20).
  assert (KS3 : forall a, lc_sp1 cx <= a < lc_sp1 cx + 216 -> aview segs (w_H W') mem3 a = aview segs (w_H W') mem' a).
  { intros a Ha. apply KC; [lia | intros HG3; pose proof (o4_GL a HG3); lia | lia]. }
  assert (S8' : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 8) = Some (tg_n tv)).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3)) by (intros j Hj; apply KS3; lia).
    exact S8. }
  assert (S16' : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 16) = Some (TOP.fi_n (tg_c4 tv))).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3)) by (intros j Hj; apply KS3; lia).
    exact S16. }
  assert (S64' : rdword (aview segs (w_H W') mem3) (lc_sp1 cx + 64) = Some (tg_serial tv)).
  { rewrite (rdword_ext (aview segs (w_H W') mem') (aview segs (w_H W') mem3)) by (intros j Hj; apply KS3; lia).
    exact S64. }
  (* the world after g_cmd[serial]'s stores and the copy *)
  set (Bw := o4_cmdw B5 (tg_serial tv) (sv_key kd) (sv_display kd) (tg_len tv) (tg_cbytes tv)) in *.
  assert (HTW3 : lc_tw W' mem3 Bw).
  { apply (o4_w_cmd B5 (aview segs (w_H W') mem') (aview segs (w_H W') mem3) (tg_serial tv) (sv_key kd)
      (sv_display kd) (tg_len tv) (tg_cbytes tv) HTW Hs ltac:(lia) Hcb).
    - intros j Hj. rewrite (Heff (TB_g_cmd + 40 * tg_serial tv + Z.of_nat j) ltac:(unfold TB_g_cmd; lia) ltac:(lia)
        ltac:(rewrite EST; unfold TB_g_cmd; lia)).
      exact (Vst0 j Hj).
    - intros j Hj. rewrite (Heff (TB_g_cmd + 40 * tg_serial tv + 4 + Z.of_nat j) ltac:(unfold TB_g_cmd; lia) ltac:(lia)
        ltac:(rewrite EST; unfold TB_g_cmd; lia)).
      exact (Vkey0 j Hj).
    - intros j Hj. rewrite (Heff (TB_g_cmd + 40 * tg_serial tv + 8 + Z.of_nat j) ltac:(unfold TB_g_cmd; lia) ltac:(lia)
        ltac:(rewrite EST; unfold TB_g_cmd; lia)).
      exact (Vdisp0 j Hj).
    - rewrite (Heff (TB_g_cmd + 40 * tg_serial tv + 36) ltac:(unfold TB_g_cmd; lia) ltac:(lia)
        ltac:(rewrite EST; unfold TB_g_cmd; lia)).
      exact Vlen0.
    - intros i Hi. rewrite (Hcopy i Hi).
      rewrite (KB1 (lc_F cx + 32 + i) ltac:(lia)) by (destruct HapC; lia).
      exact (o4_c_byte (w_H W') mem' (lc_F cx + 32) _ _ _ _ HCS Hcb i ltac:(lia)).
    - intros x Hx Hn1 Hn2. pose proof (o4_GL x (o4_tw_in_G x Hx)) as Hl.
      rewrite (Heff x ltac:(lia) ltac:(lia) ltac:(rewrite EST; lia)). apply KB1; [lia | lia | exact Hn2]. }
  clear HapC.
  assert (HOKw : lc_want tv at_ = DSpec.SPEC_OK) by exact Hw0.
  rewrite Hw0 in HSET, HOP.
  intros HATR. destruct HATR as [Ha1 | Ha1].
  + (* at = -1: the append *)
    pose proof (HMapp HOKw ltac:(lia)) as Hnq. unfold TC.CMDS_MAX in Hnq.
    rewrite (o4_b6_app B5 Bw at_ (tg_serial tv) ltac:(lia)) in HSET, HOP.
    rewrite Ha1 in R25'. replace ((-1) mod 2 ^ 32) with (2 ^ 32 - 1) in R25' by reflexivity.
    exact (o4_tail_app cx op ly' S' W' regs3 mem3 md3 e Bw (tg_c tv) (tg_serial tv) (tg_n tv) (TOP.fi_n (tg_c4 tv))
      HP HB HL3 Hopc HTW3 Hnq Hs HSET HOP R25' R24' R27' R20' S8' S16' S64' Hfi5).
  + (* 0 <= at < 1024: the replace *)
    pose proof (HMrep HOKw ltac:(lia)) as Hq. unfold TC.CMDS_MAX in Hq, Ha1.
    rewrite (o4_b6_rep B5 Bw at_ (tg_serial tv) ltac:(lia)) in HSET, HOP.
    exact (o4_tail_rep cx op ly' S' W' regs3 mem3 md3 e Bw (tg_c tv) at_ (tg_serial tv) (tg_n tv)
      (TOP.fi_n (tg_c4 tv)) HP HB HL3 Hopc HTW3 Ha1 Hq Hs HSET HOP R25' R24' R27' R20' S8' S16' S64' Hfi5).
Qed.

End seg.
