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
(* lib/B phase file of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput, 0x80818, asan-ubsan build of libreac v1.9.0):
   the TAIL, from the end of the end-of-walk check to the return (a Theorem Labs lane of entry-au-map.md
   (sha256 3f4d6f638159; internal record), the stretches R1 .. R7 and BT of lib/B/Prog/PcapEntryDefs.v). Every cut lemma has PcapEntryDefs.pe_from's form,
   at the waypoint invariants GI_* of lib/B/Prog/PcapEntryPhases.v:
     R1   PP_K6  0x80e38 -> PP_K7  0x80e50   ld a0,0(s4) (ps.f = NULL), bnez a0 to PP_abort (not taken), the second
                                            pcap_source_open (0x80e4c) of the good file
     R2   PP_K7  0x80e50 -> PP_K8  0x80e68   bnez a0 to PP_abort (a0 = 0), pcap_source_next (0x80e64, ts = NULL)
     R3   PP_K8  0x80e68 -> PP_K9  0x80e74   bne a0,s5 to PP_abort (a0 = s5 = first), pcap_source_close (0x80e70)
     R4   PP_K9  0x80e74 -> PP_K10 0x80e88   pcap_source_next of the closed reader (0x80e84)
     R5   PP_K10 0x80e88 -> PP_K11 0x80e98   bne a0,a1 to PP_abort (a0 = a1 = -1), free of the record buffer (0x80e94)
     R6   PP_K11 0x80e98 -> PP_K12 0x80ea0   free of the copy of the file (0x80e9c)
     R7   PP_K12 0x80ea0 -> PP_K12r 0x80eac  ts out of scope (sb 0xf8,0xc(s9), s9 reloaded from PS_SH)
     BT   PP_K12r 0x80eac -> PP_leave 0x80ec4  ps out of scope (sb 0xf8 at 4/5/6(s9)), s7 / s10 reloaded (PS_FK, PS_F)
     leave PP_leave 0x80ec4 -> PP_ret 0x80fa4  the retired magic at F (0x80ecc), beqz s7 to the machine-frame arm
                                            (not taken: s7 = F >= 4096), the 16 shadow bytes 0xf5 (0x80ed8..0x80f14),
                                            the flag byte through F + PE_FLAGPTR (0x80f18, 0x80f1c: astack_free_law), a0 := 0,
                                            the restores (0x80f68..0x80fa0); stated for pcap_source_ret (frames S3 = [])
     ret  PP_ret 0x80fa4: the `ret`, GI_ret gives pe_post.
   No UBSan guard and no __asan_report_* call lies in these stretches; the four branches to PP_abort (0x80e3c,
   0x80e50, 0x80e68, 0x80e8c) are refuted by the facts of the cut before them, as is the machine-frame arm 0x80ed0.

   The statements are stated first (pt_* below), and each lemma proves its statement: pe_from_K6 .. pe_from_K11 (R1 ..
   R6, the callee contracts as the Section hypotheses of Sections p / pn / po, lifted by PcapEntryCalls and
   PcapEntryKit), pe_from_K12 (R7), pe_from_K12r (BT), pe_from_leave, pe_from_ret_post; and the compositions
   pe_from_leave_post (GI_leave), pe_from_K12r_post (GI_K12r) and pe_from_K6_post (GI_K6), each to pe_post.
   Template: lib/A/Prog/PcapHarnessTail.v (the same tail on the ASan build); R1 .. R6 were proved by this lane's
   sub-lanes and are kept here as one text. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs PcapEntryPhases.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournalFs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceOpenDefs PcapSourceNextSpec PcapFuzzFopenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntryCalls PcapEntryKit.
(* lib/B's entry names last, over the kit's namesakes (c_regs, ...). *)
Import PcapEntryDefs PcapEntryPhases.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* lib/A/AE2f.v turns zify's euclidean-division equations OFF for every file that requires it; this file needs
   them (the realigned stack pointer and the shadow address are / and mod). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

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

(* ---- the statements ---- *)
(* R1: the second open. *)
Definition pt_K6 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K7 B MT KS) -> pe_from SK B MT KS POST (GI_K6 B MT KS).
(* R2: next from 24, ts = NULL. *)
Definition pt_K7 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K8 B MT KS) -> pe_from SK B MT KS POST (GI_K7 B MT KS).
(* R3: the second close. *)
Definition pt_K8 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K9 B MT KS) -> pe_from SK B MT KS POST (GI_K8 B MT KS).
(* R4: next of the closed reader. *)
Definition pt_K9 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K10 B MT KS) -> pe_from SK B MT KS POST (GI_K9 B MT KS).
(* R5: free of the record buffer. *)
Definition pt_K10 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K11 B MT KS) -> pe_from SK B MT KS POST (GI_K10 B MT KS).
(* R6: free of the copy. *)
Definition pt_K11 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K12 B MT KS) -> pe_from SK B MT KS POST (GI_K11 B MT KS).
(* R7: ts out of scope. *)
Definition pt_K12 : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_K12r B MT KS) -> pe_from SK B MT KS POST (GI_K12 B MT KS).
(* BT: ps out of scope, s7 / s10 reloaded. *)
Definition pt_K12r : Prop :=
  forall POST, pe_from SK B MT KS POST (GI_leave B MT KS) -> pe_from SK B MT KS POST (GI_K12r B MT KS).
(* The frame given back and the restores. *)
Definition pt_leave : Prop :=
  forall POST, pe_from_ret SK B MT KS POST (GI_ret B MT KS) -> pe_from SK B MT KS POST (GI_leave B MT KS).
(* The `ret`. *)
Definition pt_ret : Prop := pe_from_ret SK B MT KS (pe_post SK B MT KS) (GI_ret B MT KS).
(* The compositions the other lanes take: PP_leave (the early return, L1), PP_K12r (the refused open, L2) and
   PP_K6 (the end of the end-of-walk check, L5) each reach pe_post. *)
Definition pt_leave_post : Prop := pe_from SK B MT KS (pe_post SK B MT KS) (GI_leave B MT KS).
Definition pt_K12r_post : Prop := pe_from SK B MT KS (pe_post SK B MT KS) (GI_K12r B MT KS).
Definition pt_K6_post : Prop := pe_from SK B MT KS (pe_post SK B MT KS) (GI_K6 B MT KS).

End c.

(* ---- the proofs ---- *)
Section p.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
(* Section hypotheses, each of the exact type of the fact it stands for, discharged by the composer (lib/A
   PcapHarnessTail's set, at lib/B's numbers); the callee contracts of pcap_source_next and pcap_source_open are the
   hypotheses of the inner Sections pn and po below:
     LAWS, TL, MTL   the allocator laws, the listing's runtime symbols, the meter laws;
     ASIL            asource_img_laws SK SEGS B KS (the stream's environment lies in the image);
     AFREE           afree04_rule SEGS B MT (YC5d.v), through PcapEntryKit.afree_call;
     CLOSE           PcapSourceCloseSpec.tpcap_source_close_specX at pcap_source_close (lib/B/Prog/PcapSourceClose.v
                     pb_pcap_source_closeX is its instance), through PcapEntryCalls.close_call;
     HRO             ro_below_ofl (PcapBase.v: the read-only bytes lie below the open-file list head);
     ML, ASF, FFL, MTF  model_laws (as_universe B), astack_free_law SEGS B, frame_flag_lawP SEGS B, ameter_fs_laws MT:
                     the frame give-back (PcapFrame.aj_flag_store_pi) and the meter across it. *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Hypothesis AFREE : afree04_rule SEGS B MT.
Hypothesis CLOSE : AC.tpcap_source_close_specX SK SEGS pa_relro_lo pa_relro_hi B KS MT (BASE + AF_pcap_source_close).
Context {HRO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis MTF : ameter_fs_laws MT.

Lemma src_env_img : forall a, asrc_env_addr KS a -> 0x10000 <= a < pcap_img_end.
Proof. intros a Ha. exact (pa_img_range a (proj1 (asil_env _ _ _ _ ASIL a Ha))). Qed.

(* the same, in numbers, for lia *)
Lemma src_env_num : forall a, asrc_env_addr KS a -> 65536 <= a < (symaddr ImgPages.AsanUbsan.top).
Proof. intros a Ha. pose proof (src_env_img a Ha) as H. vm_compute pcap_img_end in H. exact H. Qed.

Lemma vm_frame : forall (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> mbyte SEGS m' x = mbyte SEGS m x) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v Hfr Hv kk Hk. rewrite Hfr by lia. exact (Hv kk Hk). Qed.

(* asource_none reads only its environment. *)
Lemma asource_none_frame : forall (m m' : word -> option byte),
  (forall a, asrc_env_addr KS a -> mbyte SEGS m' a = mbyte SEGS m a) ->
  asource_none SEGS KS m -> asource_none SEGS KS m'.
Proof.
intros m m' Hfr ((Hth & Hnl & Hlk & Hmode & Hms & (cv & Hcv & Hc)) & Hhead).
unfold asource_none, asrc_stdio_env, as_ofl_head in *.
split; [split; [|split; [|split; [|split; [|split]]]]|].
- eapply vm_frame; [|exact Hth]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hnl]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hlk]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hmode). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_mode_Z app] in Hx. cbn in Hx. lia.
- apply (garr8_frame SEGS m m' _ _ Hms). intros x Hx. apply Hfr. unfold asrc_env_addr.
  cbn [length src_modeset_Z app] in Hx. cbn in Hx. lia.
- exists cv. split; [exact Hcv|]. eapply vm_frame; [|exact Hc]. intros x Hx. apply Hfr.
  unfold asrc_env_addr. cbn in Hx. lia.
- eapply vm_frame; [|exact Hhead]. intros x Hx. apply Hfr. unfold asrc_env_addr. cbn in Hx. lia.
Qed.


(* A machine state at a slot, as mkst. *)
Lemma ms_mkst_at : forall (ms : machine_state) pc,
  ms_pc_val ms = w64 pc -> ms_resv ms = None -> ms_svc_pending ms = None ->
  ms_rom ms = seg_rom SEGS -> ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom SEGS).
Proof. intros ms pc H1 H2 H3 H4 H5 H6. destruct ms. cbn in *. subst. reflexivity. Qed.

(* The caller's bytes, read off two garr8 facts of the same list. *)
Lemma aview_of_garr8 : forall H H' (m m' : word -> option byte) p l i,
  garr8 SEGS (mrestrict H m) p l -> garr8 SEGS (mrestrict H' m') p l -> 0 <= i < Z.of_nat (length l) ->
  aview SEGS H' m' (p + i) = aview SEGS H m (p + i).
Proof.
intros H H' m m' p l i G1 G2 Hi. unfold aview.
pose proof (garr8_mbyte SEGS _ _ _ (Z.to_nat i) G1 ltac:(lia)) as E1.
pose proof (garr8_mbyte SEGS _ _ _ (Z.to_nat i) G2 ltac:(lia)) as E2.
rewrite Z2Nat.id in E1, E2 by lia. rewrite E1, E2. reflexivity.
Qed.

(* A one-byte val_mem is an aview. *)
Lemma aview_of_val_mem1 : forall H (m : word -> option byte) a v, 0 <= v < 256 ->
  val_mem SEGS (mrestrict H m) a 1 v -> aview SEGS H m a = Some v.
Proof.
intros H m a v Hv Hm. specialize (Hm 0%nat ltac:(lia)). cbn [Z.of_nat] in Hm. rewrite Z.add_0_r in Hm.
unfold aview. rewrite Hm. cbn [option_map]. f_equal.
replace (YO0f.le_byte v 1 0) with v;
  [rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; change (2 ^ 8) with 256; apply Z.mod_small; lia
  | unfold YO0f.le_byte; change (2 ^ (8 * Z.of_nat 1)) with 256;
    rewrite ?Z.shiftr_0_r; rewrite (Z.mod_small v 256) by lia; symmetry; apply Z.mod_small; lia].
Qed.

Lemma nth_firstn_lt : forall (l : list Z) k j, (j < k)%nat -> nth j (firstn k l) 0 = nth j l 0.
Proof.
induction l as [|x l IH]; intros k j Hj; [rewrite firstn_nil; destruct j; reflexivity|].
destruct k as [|k]; [lia|]. cbn [firstn]. destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.
Lemma nth_skipn_add : forall (l : list Z) i j, nth i (skipn j l) 0 = nth (j + i) l 0.
Proof.
induction l as [|x l IH]; intros i j; [rewrite skipn_nil; destruct i, j; reflexivity|].
destruct j as [|j]; [reflexivity|]. cbn [skipn nth]. rewrite IH. reflexivity.
Qed.

Lemma nth_repeat_lt : forall (v : Z) n j, (j < n)%nat -> nth j (repeat v n) 0 = v.
Proof.
intros v n. induction n as [|n IH]; intros j Hj; [lia|]. cbn [repeat].
destruct j as [|j]; [reflexivity|]. cbn [nth]. apply IH. lia.
Qed.

(* The nth of an n-byte update of a list. *)
Lemma nth_psh_set : forall sh i n v k, (i + n <= length sh)%nat -> (k < length sh)%nat ->
  nth k (psh_set sh i n v) 0 = if ((i <=? k) && (k <? i + n))%nat then v else nth k sh 0.
Proof.
intros sh i n v k Hi Hk. unfold psh_set.
destruct (Nat.lt_ge_cases k i) as [Hlt|Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia).
  rewrite (nth_firstn_lt sh i k) by lia.
  replace ((i <=? k)%nat) with false by (symmetry; apply Nat.leb_gt; lia). reflexivity.
- rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (Nat.min i (length sh)) with i by lia.
  replace ((i <=? k)%nat) with true by (symmetry; apply Nat.leb_le; lia). cbn [andb].
  destruct (Nat.lt_ge_cases k (i + n)) as [Hin|Hout].
  + replace ((k <? i + n)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite app_nth1 by (rewrite repeat_length; lia). apply nth_repeat_lt. lia.
  + replace ((k <? i + n)%nat) with false by (symmetry; apply Nat.ltb_ge; lia).
    rewrite app_nth2 by (rewrite repeat_length; lia). rewrite repeat_length.
    rewrite (nth_skipn_add sh (k - i - n) (i + n)). f_equal. lia.
Qed.

Lemma length_psh_set : forall sh i n v, (i + n <= length sh)%nat -> length (psh_set sh i n v) = length sh.
Proof.
intros sh i n v Hi. unfold psh_set.
rewrite !length_app, length_firstn, length_skipn, repeat_length. lia.
Qed.

(* A shadow list with n bytes written to the same value. *)
Lemma pshadow_upd : forall cx fp (W3 : world SEGS) ms3 (W4 : world SEGS) ms4 sh i n v,
  pshadow cx fp W3 ms3 sh -> (i + n <= length sh)%nat -> 0 <= v < 256 ->
  (forall j, (i <= j < i + n)%nat -> aview SEGS (w_H W4) (ms_mem ms4) (pSH cx fp + Z.of_nat j) = Some v) ->
  (forall j, (j < length sh)%nat -> ~ (i <= j < i + n)%nat ->
     aview SEGS (w_H W4) (ms_mem ms4) (pSH cx fp + Z.of_nat j) =
     aview SEGS (w_H W3) (ms_mem ms3) (pSH cx fp + Z.of_nat j)) ->
  pshadow cx fp W4 ms4 (psh_set sh i n v).
Proof.
intros cx fp W3 ms3 W4 ms4 sh i n v HS Hi Hv Hw Hk j Hj.
rewrite (length_psh_set sh i n v Hi) in Hj.
rewrite (nth_psh_set sh i n v j Hi Hj).
destruct ((i <=? j)%nat && (j <? i + n)%nat)%bool eqn:Ein.
- apply andb_prop in Ein as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. exact (Hw j (conj E1 E2)).
- rewrite (Hk j Hj ltac:(intros [X1 X2]; apply andb_false_iff in Ein as [E|E];
    [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia)).
  exact (HS j Hj).
Qed.

(* pt_ret: the `ret` at PP_ret, from GI_ret to pe_post. *)
Lemma pe_from_ret_post : pt_ret B MT KS.
Proof.
intros cx k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HGI.
destruct HGI as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hpres & Hra & Ha0 & Hk & Hacc & HPerm & Hfds & Hfs & Hsn & Hinp).
pose proof HB as (_ & HraB & _ & _ & _ & Hgarr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hneed & _).
pose proof (ms_mkst_at ms3 (BASE + PP_ret) Hpc Hrv Hsv Hrom Hfreg Hfcsr) as Ems.
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *. rewrite Ems.
set (E := Eimg (Ereg regs [])).
assert (HS : st_ok_pi SEGS pa_val E (mkSS PP_ret sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_ret)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
eapply (paj_ret_at (PL := PL_pcap) W3 E _ _ md3 _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbn [ms_regs ms_mem mkst].
assert (Era : getr (c_regs cx) 1 = Z_to_bv 64 RA_LLVMF) by (rewrite <- HraB; unfold raZ; symmetry; apply Z_to_bv_bv_unsigned).
exists ly3, S3, regs, mem, (with_vm_backing (m_vm_lazy md3) mat' md3), k.
split; [rewrite Hra, Era, (v_jalr_lit_even RA_LLVMF ltac:(unfold RA_LLVMF; lia) ltac:(reflexivity)); reflexivity|].
split; [eapply (ajournal_gx_materialize SEGS B LAWS pa_segs_low); exact HJ|].
split; [exact Hk|]. split; [exact Hpres|]. split; [exact Ha0|]. split; [exact HPerm|].
split; [rewrite (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds|].
split; [rewrite (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs|].
split; [exact Hsn|].
split; [apply (mo_le_mono MT MTL _ _ _ _ Hmo); pose proof (PA_K12_need MT MTL cx); lia|].
intros i Hi. apply (aview_of_garr8 _ _ _ _ _ _ i Hgarr Hinp). rewrite length_map. unfold c_n in Hi. exact Hi.
Qed.


(* pt_K12: R7, PP_K12 0x80ea0 -> PP_K12r 0x80eac (ts out of scope). *)
Lemma pe_from_K12 : pt_K12 B MT KS.
Proof.
intros POST IH cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HGI.
destruct HGI as ((Hbody & Hk & Hacc & HPerm & Hfds & Hfs) & Hn26 & Hslots & Hsn).
destruct Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hshlen & Hinp).
destruct Hslots as (HF0 & HD & HSHB & HSH & HFs & HFK & HTSP & HCAP).
destruct Hregs as (Hsp & Hs0 & Hs1 & Hgp & Htp).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & Hout).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (ms_mkst_at ms3 (BASE + PP_K12) Hpc Hrv Hsv Hrom Hfreg Hfcsr) as Ems.
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *.
set (E := Eimg (Ereg regs [w64 (pSH cx fp)])).
assert (Esp1 : c_sp1 cx = pe_sp1 (spZ (c_regs cx))) by (unfold pe_base in HB; tauto).
assert (Hs1v : spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0).
{ rewrite Esp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 256) 32) as D.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 256) 32 ltac:(lia)) as M.
  split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]. }
assert (HfF : pF cx fp = frame_addr ly3 PE_CID fp).
{ unfold pF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (HSHv : SHADOW_OFF <= pSH cx fp /\ pSH cx fp + 16 < 17594333495296).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. rewrite HfF.
  assert (H0 : 0 <= frame_addr ly3 PE_CID fp) by lia.
  assert (H1 : frame_addr ly3 PE_CID fp <= 140737479966720) by (pose proof (fs_frame_bytes_nonneg PE_CID); lia).
  assert (Hq : 0 <= frame_addr ly3 PE_CID fp / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  lia. }
assert (HpFb : 4096 <= pF cx fp /\ pF cx fp + 128 <= alloc_ceiling)
  by (rewrite HfF; change (fs_frame_bytes PE_CID) with 128 in Hfceil; lia).
assert (HSHc : pSH cx fp + 16 < alloc_ceiling) by (destruct HSHv; lia).
(* the two regions the stretch touches: the spill slot PS_SH and the shadow byte SH + 12 *)
assert (Hsp1A : pSH cx fp + 16 < c_sp1 cx /\ c_sp1 cx + 288 <= spZ (c_regs cx) + 288)
  by (unfold LLVMF_STK in Hslo; lia).
assert (HSHp : forall a, pSH cx fp <= a < pSH cx fp + 16 -> apresent (w_H W3) mem a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Ha. rewrite HfF in Ha.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia. }
assert (HSLp : forall a, c_sp1 cx <= a < c_sp1 cx + 128 -> apresent (w_H W3) mem a)
  by (intros a Ha; apply Hpres; unfold LLVMF_STK; lia).
pose (ss12 := mkSS PP_K12 sr_atoms
  [ YP09.mkRegion (Some 9%nat) 0 128 0 0 [YP09.mkChunk PS_SH (CVal 8 (SOff 32 0))]
  ; YP09.mkRegion (Some 32%nat) 0 16 12 13 [] ]
  None (mkFacts [(9%nat, mkAF 4096 140737488355328 5); (32%nat, mkAF SHADOW_OFF 17594333495296 0)] [] [])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (pSH cx fp)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact Hs1).
assert (E32 : ew E 32 = w64 (pSH cx fp))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Hsp1b : 4096 <= c_sp1 cx /\ c_sp1 cx + 128 < 2 ^ 47).
{ change (2 ^ 47) with 140737488355328 in *. unfold LLVMF_STK in *. lia. }
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite E9; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = pSH cx fp)
  by (rewrite E32; apply unsigned_lit_small; destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (HS : st_ok_pi SEGS pa_val E ss12 (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_K12)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss12. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_SH 8 (SOff 32 0) (pSH cx fp));
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL; lia
        | cbn [Z.of_N]; lia |].
      exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ HSH).
    + rewrite U32. destruct HSHv as [HL HR]. unfold SHADOW_OFF in HL.
      split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HSHp. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HSHv as [HL HR]. unfold SHADOW_OFF in HL. unfold LLVMF_STK in *.
    repeat split; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U32. unfold SHADOW_OFF in *.
    destruct HSHv as [HL HR]. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; try lia. }
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
rewrite Ems.
paj_run_to_sh (SRr_run_to_pi_AJ (L := pcap_listing) (PL := PL_pcap) B LAWS) HS HJi PP_K12r.
- (* the only writable byte is SH + 12, a byte of the frame's shadow *)
  intros a (r & Hinr & Hr). unfold ss12 in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr; lia|].
  rewrite U32 in Hr. right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Hr. rewrite HfF in Hr.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia.
- (* at PP_K12r: ts out of scope (PSH_tsout) and s9 = SH *)
  match goal with HSx : st_ok_pi _ _ _ ?ssx _ |- _ => let v := eval vm_compute in ssx in change ssx with v in HSx end.
  pose proof (kept_of_frame (segs := SEGS) E (ss_mem ss12) (w_H W3) mem (ms_mem ms)
    (fun a => pSH cx fp + 12 <= a < pSH cx fp + 13) HFr
    ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
          repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                  rewrite ?U9, ?U32 in Hrr; lia|]); destruct Hinw)) as UN.
  assert (HnotF : forall a, pF cx fp <= a < pF cx fp + 128 -> ~ (pSH cx fp + 12 <= a < pSH cx fp + 13)).
  { intros a Ha Hbad. unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad.
    refine (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia)
      ltac:(change (2 ^ 47) with 140737488355328; lia) _ _ _);
      [rewrite HfF; exact Hfapp | lia | lia]. }
  assert (HnotS : forall a, c_sp1 cx <= a < c_sp1 cx + 160 -> ~ (pSH cx fp + 12 <= a < pSH cx fp + 13)) by lia.
  apply (IH cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB).
  + eapply ajournal_gx_pack; [exact HSTK0 | exact HXO0 | rewrite !Z.add_0_r; exact HJi | exact Hag |].
    intros a Ha _. lia.
  + exact Hfr.
  + exact Hmo.
  + pose proof HS as (HSfr & HSpc & HSsv & HSrv & HSfc & HSrom & HSregs & HSmem & HSfacts).
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts abs_ss setpc resv_denot ms_regs ms_mem ms_pc_val ms_fregs ms_fcsr ms_rom ms_svc_pending restrict mkst] in
      HSfr, HSpc, HSsv, HSrv, HSfc, HSrom, HSregs, HSmem, HSfacts.
    split; [|split; [exact Hn26 | split]].
    * (* p_cut at PSH_tsout *)
      exists PSH_tsout. split; [left; reflexivity|].
      split; [|split; [change EV_LIB with 10; lia | split; [lia | split; [exact HPerm | split]]]].
      -- split; [exact HSpc|]. split; [exact HSrv|]. split; [exact HSsv|]. split; [exact HSrom|].
         split; [exact HSfr|]. split; [exact HSfc|].
         split.
         { split; [|split; [|split; [|split]]].
           - prreg HS (2%bv : bv 5) Q2; rewrite Q2; exact Hsp.
           - prreg HS (8%bv : bv 5) Q8; rewrite Q8; exact Hs0.
           - prreg HS (9%bv : bv 5) Q9; rewrite Q9; exact Hs1.
           - prreg HS (3%bv : bv 5) Q3; rewrite Q3; exact Hgp.
           - prreg HS (4%bv : bv 5) Q4; rewrite Q4; exact Htp. }
         split.
         { destruct Hsaved as [Hra8 Hrest]. unfold psaved in *. split.
           - rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact Hra8|].
             intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia].
           - intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact (Hrest j Hj)|].
             intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
         split.
         { destruct Hhdr as (H1 & H2 & H3 & H4).
           unfold pheader in *.
           assert (Hhd : forall off v, 0 <= off <= 120 ->
             rdword (aview SEGS (w_H W3) mem) (pF cx fp + off) = Some v ->
             rdword (aview SEGS (w_H W3) (ms_mem ms)) (pF cx fp + off) = Some v).
           { intros off v Hoff Hv.
             rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact Hv|].
             intros kk Hk2. apply UN; [change (2 ^ 64) with 18446744073709551616; lia | apply HnotF; lia]. }
           split; [|split; [|split]].
           - rewrite <- (Z.add_0_r (pF cx fp)). apply (Hhd 0); [lia | rewrite Z.add_0_r; exact H1].
           - apply (Hhd 8); [lia | exact H2].
           - apply (Hhd 16); [lia | exact H3].
           - apply (Hhd PE_FLAGPTR); [unfold PE_FLAGPTR; lia | exact H4]. }
         split.
         { change PSH_tsout with (psh_set PSH_ts 12 1 248).
           apply (pshadow_upd cx fp W3 ms3 W3 ms PSH_ts 12 1 248 Hsh ltac:(vm_compute; lia) ltac:(lia)).
           - intros j Hjr.
             apply (aview_of_val_mem1 (w_H W3) (ms_mem ms) _ 248 ltac:(lia)).
             lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
               let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
               pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
               cbn [ms_mem restrict mkst] in HR1 end.
             replace j with 12%nat by lia;
               pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 32%nat (pSH cx fp)
                   _ 0 16 12 13 12 1%N (SLit 18446744073709551608) HR1 U32
                   ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vsh;
               cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vsh;
               match type of Vsh with val_mem _ _ _ _ ?v => replace v with 248 in Vsh by (vm_compute; reflexivity) end;
               cbn [Z.of_nat]; exact Vsh.
           - intros j Hj Hne. vm_compute (length PSH_ts) in Hj.
             apply UN; [destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL;
                        change (2 ^ 64) with 18446744073709551616; lia | lia]. }
         split; [reflexivity | ].
         apply (garr8_frame SEGS _ _ _ _ Hinp). intros a Ha. apply (mbyte_of_aview SEGS).
         rewrite length_map in Ha. fold (c_n cx) in Ha.
         destruct HB as (HPRE & _ & _ & _ & Hinput & _).
         destruct Hinput as [[Hn0 Hpe] | [Hnpos Hinb]]; [unfold c_n in Ha, Hn0; lia|].
         destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx)
           (proj1 HPRE) Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
         pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hrq1 Hrq2].
         apply UN; [unfold in_app in Hbapp; unfold ASAN_CEIL in *; lia|].
         intros Hbad. unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad.
         refine (fshadow_not_app (pF cx fp) 16 (c_p cx) (req_size (c_n cx)) a ltac:(lia) ltac:(change (2 ^ 47) with 140737488355328; lia) Hbapp _ _); lia.
      -- etransitivity; [apply (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfds].
      -- etransitivity; [apply (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfs].
    * prreg HS (25%bv : bv 5) Q25; rewrite Q25; exact E32.
    * split; [|split].
      -- unfold pslot. rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact HFK|].
         intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia].
      -- unfold pslot. rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact HFs|].
         intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia].
      -- apply (asource_none_frame (mrestrict (w_H W3) mem)); [|exact Hsn].
         intros a Ha. apply (mbyte_of_aview SEGS). apply UN;
           [pose proof (src_env_num a Ha); change (2 ^ 64) with 18446744073709551616; lia
           | pose proof (src_env_num a Ha); destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL; lia].

Qed.


(* pt_K12r: BT, PP_K12r 0x80eac -> PP_leave 0x80ec4 (ps out of scope; s7 and s10 reloaded). *)
Lemma pe_from_K12r : pt_K12r B MT KS.
Proof.
intros POST IH cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HGI.
destruct HGI as ((sh & Hsheq & (Hbody & Hk & Hacc & HPerm & Hfds & Hfs)) & Hn26 & Hs9 & HFK & HFs & Hsn).
destruct Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hshw & Hshlen & Hinp).
destruct Hregs as (Hsp & Hs0 & Hs1 & Hgp & Htp).
pose proof HJ as (HSTK0 & HXO0 & (memS & HJi & Hag) & Hout).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hin) as (Hf4096 & Hfceil & Hfapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (ms_mkst_at ms3 (BASE + PP_K12r) Hpc Hrv Hsv Hrom Hfreg Hfcsr) as Ems.
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *.
set (E := Eimg (Ereg regs [w64 (pF cx fp)])).
assert (Esp1 : c_sp1 cx = pe_sp1 (spZ (c_regs cx))) by (unfold pe_base in HB; tauto).
assert (Hs1v : spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0).
{ rewrite Esp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z_div_mod_eq_full (spZ (c_regs cx) - 256) 32) as D.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 256) 32 ltac:(lia)) as M.
  split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]. }
assert (HfF : pF cx fp = frame_addr ly3 PE_CID fp).
{ unfold pF, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (HSHv : SHADOW_OFF <= pSH cx fp /\ pSH cx fp + 16 < 17594333495296).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. rewrite HfF.
  assert (H0 : 0 <= frame_addr ly3 PE_CID fp) by lia.
  assert (H1 : frame_addr ly3 PE_CID fp <= 140737479966720) by (pose proof (fs_frame_bytes_nonneg PE_CID); lia).
  assert (Hq : 0 <= frame_addr ly3 PE_CID fp / 8 <= 17592184995840)
    by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  lia. }
assert (HpFb : 4096 <= pF cx fp /\ pF cx fp + 128 <= alloc_ceiling)
  by (rewrite HfF; change (fs_frame_bytes PE_CID) with 128 in Hfceil; lia).
assert (HSHc : pSH cx fp + 16 < alloc_ceiling) by (destruct HSHv; lia).
assert (Hsp1A : pSH cx fp + 16 < c_sp1 cx /\ c_sp1 cx + 288 <= spZ (c_regs cx) + 288)
  by (unfold LLVMF_STK in Hslo; lia).
assert (HSHp : forall a, pSH cx fp <= a < pSH cx fp + 16 -> apresent (w_H W3) mem a).
{ intros a Ha. refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJi _)).
  right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Ha. rewrite HfF in Ha.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia. }
pose (ss12r := mkSS PP_K12r sr_atoms
  [ YP09.mkRegion (Some 9%nat) 0 128 0 0 [YP09.mkChunk PS_FK (CVal 8 (SOff 32 0)); YP09.mkChunk PS_F (CVal 8 (SOff 32 0))]
  ; YP09.mkRegion (Some 25%nat) 0 16 4 7 [] ]
  None (mkFacts [(9%nat, mkAF 4096 140737488355328 5); (25%nat, mkAF SHADOW_OFF 17594333495296 0);
                 (32%nat, mkAF 4096 140737488355328 0)] [] [])).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs [w64 (pF cx fp)]) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact Hs1).
assert (E25 : ew E 25 = w64 (pSH cx fp))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact Hs9).
assert (E32 : ew E 32 = w64 (pF cx fp))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Hsp1b : 4096 <= c_sp1 cx /\ c_sp1 cx + 128 < 2 ^ 47).
{ change (2 ^ 47) with 140737488355328 in *. unfold LLVMF_STK in *. lia. }
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp)
  by (rewrite E25; apply unsigned_lit_small; destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL;
      change (2 ^ 64) with 18446744073709551616; lia).
assert (U32 : bv_unsigned (ew E 32) = pF cx fp)
  by (rewrite E32; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616;
      pose proof (fs_frame_bytes_nonneg PE_CID); lia).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS pa_val E ss12r (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_K12r)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss12r. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_FK 8 (SOff 32 0) (pF cx fp));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; pose proof (fs_frame_bytes_nonneg PE_CID); lia
          | cbn [Z.of_N]; lia |].
        exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ HFK).
      * apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_F 8 (SOff 32 0) (pF cx fp));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; pose proof (fs_frame_bytes_nonneg PE_CID); lia
          | cbn [Z.of_N]; lia |].
        exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ HFs).
    + rewrite U25. destruct HSHv as [HL HR]. unfold SHADOW_OFF in HL.
      split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply HSHp. lia.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct HSHv as [HL HR]. unfold SHADOW_OFF in HL. unfold LLVMF_STK in *.
    repeat split; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U25, U32. unfold SHADOW_OFF in *.
    destruct HSHv as [HL HR]. change (2 ^ 5) with 32. change (2 ^ 0) with 1.
    pose proof (fs_frame_bytes_nonneg PE_CID).
    assert (HFal : pF cx fp mod 32 = 0)
      by (rewrite HfF; exact (proj1 (al_frames _ _ LAWS ly3 S3 W3 mem md3 PE_CID fp HAR Hin))).
    repeat match goal with |- _ /\ _ => split end; try exact I; try (rewrite Z.mod_1_r; reflexivity); try lia. }
rewrite Ems.
paj_run_to_sh (SRr_run_to_pi_AJ (L := pcap_listing) (PL := PL_pcap) B LAWS) HS HJi PP_leave.
- (* the writable bytes are SH + 4 .. SH + 6, bytes of the frame's shadow *)
  intros a (r & Hinr & Hr). unfold ss12r in Hinr. cbn [ss_mem In] in Hinr.
  destruct Hinr as [<- | [<- | []]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; [rewrite U9 in Hr; lia|].
  rewrite U25 in Hr. right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
  right. unfold in_zr, shadow_addr. cbn [fst snd]. unfold pSH, shadow_of_addr in Hr. rewrite HfF in Hr.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold SHADOW_OFF in *. lia.
- (* at PP_leave *)
  match goal with HSx : st_ok_pi _ _ _ ?ssx _ |- _ => let v := eval vm_compute in ssx in change ssx with v in HSx end.
  pose proof (kept_of_frame (segs := SEGS) E (ss_mem ss12r) (w_H W3) mem (ms_mem ms)
    (fun a => pSH cx fp + 4 <= a < pSH cx fp + 7) HFr
    ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
          repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                  rewrite ?U9, ?U25 in Hrr; lia|]); destruct Hinw)) as UN.
  assert (HnotF : forall a, pF cx fp <= a < pF cx fp + 128 -> ~ (pSH cx fp + 4 <= a < pSH cx fp + 7)).
  { intros a Ha Hbad. unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad.
    refine (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia)
      ltac:(change (2 ^ 47) with 140737488355328; lia) _ _ _);
      [rewrite HfF; exact Hfapp | lia | lia]. }
  assert (HnotS : forall a, c_sp1 cx <= a < c_sp1 cx + 160 -> ~ (pSH cx fp + 4 <= a < pSH cx fp + 7)) by lia.
  apply (IH cx fp k acc ly3 S3 W3 ms (with_vm_backing (m_vm_lazy md3) mat md3) HB).
  + eapply ajournal_gx_pack; [exact HSTK0 | exact HXO0 | rewrite !Z.add_0_r; exact HJi | exact Hag |].
    intros a Ha _. lia.
  + exact Hfr.
  + exact Hmo.
  + pose proof HS as (HSfr & HSpc & HSsv & HSrv & HSfc & HSrom & HSregs & HSmem & HSfacts).
    cbn [ss_pc ss_regs ss_mem ss_resv ss_facts abs_ss setpc resv_denot ms_regs ms_mem ms_pc_val ms_fregs ms_fcsr ms_rom ms_svc_pending restrict mkst] in
      HSfr, HSpc, HSsv, HSrv, HSfc, HSrom, HSregs, HSmem, HSfacts.
    split; [|split; [|split; [|split]]].
    * (* p_cut at PSH_entry *)
      split; [|split; [lia | split; [lia | split; [exact HPerm | split]]]].
      -- split; [exact HSpc|]. split; [exact HSrv|]. split; [exact HSsv|]. split; [exact HSrom|].
         split; [exact HSfr|]. split; [exact HSfc|].
         split.
         { split; [|split; [|split; [|split]]].
           - prreg HS (2%bv : bv 5) Q2; rewrite Q2; exact Hsp.
           - prreg HS (8%bv : bv 5) Q8; rewrite Q8; exact Hs0.
           - prreg HS (9%bv : bv 5) Q9; rewrite Q9; exact Hs1.
           - prreg HS (3%bv : bv 5) Q3; rewrite Q3; exact Hgp.
           - prreg HS (4%bv : bv 5) Q4; rewrite Q4; exact Htp. }
         split.
         { destruct Hsaved as [Hra8 Hrest]. unfold psaved in *. split.
           - rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact Hra8|].
             intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia].
           - intros j Hj. rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact (Hrest j Hj)|].
             intros kk Hk2. unfold PS_FK, PS_F.
         apply UN; [change (2 ^ 64) with 18446744073709551616; lia | lia]. }
         split.
         { destruct Hhdr as (H1 & H2 & H3 & H4).
           unfold pheader in *.
           assert (Hhd : forall off v, 0 <= off <= 120 ->
             rdword (aview SEGS (w_H W3) mem) (pF cx fp + off) = Some v ->
             rdword (aview SEGS (w_H W3) (ms_mem ms)) (pF cx fp + off) = Some v).
           { intros off v Hoff Hv.
             rewrite (rdword_ext (aview SEGS (w_H W3) mem) (aview SEGS (w_H W3) (ms_mem ms))); [exact Hv|].
             intros kk Hk2. apply UN; [change (2 ^ 64) with 18446744073709551616; lia | apply HnotF; lia]. }
           split; [|split; [|split]].
           - rewrite <- (Z.add_0_r (pF cx fp)). apply (Hhd 0); [lia | rewrite Z.add_0_r; exact H1].
           - apply (Hhd 8); [lia | exact H2].
           - apply (Hhd 16); [lia | exact H3].
           - apply (Hhd PE_FLAGPTR); [unfold PE_FLAGPTR; lia | exact H4]. }
         split.
         { replace PSH_entry with (psh_set sh 4 3 248)
             by (destruct Hsheq as [-> | ->]; [exact PSH_out_body | exact PSH_out_refused]).
           apply (pshadow_upd cx fp W3 ms3 W3 ms sh 4 3 248 Hshw ltac:(rewrite Hshlen; unfold PE_NSH; lia) ltac:(lia)).
           - intros j Hjr.
             apply (aview_of_val_mem1 (w_H W3) (ms_mem ms) _ 248 ltac:(lia)).
             lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
               let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
               pose proof (st_ok_pi_region_nth E ssx (restrict _ msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
               cbn [ms_mem restrict mkst] in HR1 end.
             assert (Hjc : (j = 4 \/ j = 5 \/ j = 6)%nat) by lia.
             destruct Hjc as [-> | [-> | ->]];
               [ pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
                   _ 0 16 4 7 4 1%N (SLit 18446744073709551608) HR1 U25
                   ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vsh
               | pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
                   _ 0 16 4 7 5 1%N (SLit 18446744073709551608) HR1 U25
                   ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vsh
               | pose proof (field_of_region_any (segs := SEGS) E (mrestrict (w_H W3) (ms_mem ms)) 25%nat (pSH cx fp)
                   _ 0 16 4 7 6 1%N (SLit 18446744073709551608) HR1 U25
                   ltac:(cbn [In]; tauto) ltac:(cbn; lia)) as Vsh ];
               cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Vsh;
               match type of Vsh with val_mem _ _ _ _ ?v => replace v with 248 in Vsh by (vm_compute; reflexivity) end;
               cbn [Z.of_nat]; exact Vsh.
           - intros j Hj Hne. rewrite Hshlen in Hj. unfold PE_NSH in Hj.
             apply UN; [destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL;
                        change (2 ^ 64) with 18446744073709551616; lia | lia]. }
         split; [reflexivity | ].
         apply (garr8_frame SEGS _ _ _ _ Hinp). intros a Ha. apply (mbyte_of_aview SEGS).
         rewrite length_map in Ha. fold (c_n cx) in Ha.
         destruct HB as (HPRE & _ & _ & _ & Hinput & _).
         destruct Hinput as [[Hn0 Hpe] | [Hnpos Hinb]]; [unfold c_n in Ha, Hn0; lia|].
         destruct (al_blocks _ _ LAWS (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) (c_p cx) (c_n cx)
           (proj1 HPRE) Hinb) as (_ & Hb4096 & Hbceil & Hbapp & _).
         pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hrq1 Hrq2].
         apply UN; [unfold in_app in Hbapp; unfold ASAN_CEIL in *; lia|].
         intros Hbad. unfold pSH, shadow_of_addr, SHADOW_OFF in Hbad.
         refine (fshadow_not_app (pF cx fp) 16 (c_p cx) (req_size (c_n cx)) a ltac:(lia) ltac:(change (2 ^ 47) with 140737488355328; lia) Hbapp _ _); lia.
      -- etransitivity; [apply (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfds].
      -- etransitivity; [apply (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfs].
    * prreg HS (23%bv : bv 5) Q23; rewrite Q23; exact E32.
    * prreg HS (25%bv : bv 5) Q25; rewrite Q25; exact E25.
    * prreg HS (26%bv : bv 5) Q26; rewrite Q26; exact E32.
    * apply (asource_none_frame (mrestrict (w_H W3) mem)); [|exact Hsn].
      intros a Ha. apply (mbyte_of_aview SEGS). apply UN;
        [pose proof (src_env_num a Ha); change (2 ^ 64) with 18446744073709551616; lia
        | pose proof (src_env_num a Ha); destruct HSHv as [HL HR]; unfold SHADOW_OFF in HL; lia].
Qed.



(* ---- leave: PP_leave 0x80ec4 -> PP_ret 0x80fa4, the frame given back (the port of lib/A PcapHarnessTail.tail_leave) ----
   lui/addiw a0 = 0x45e0360e, sd a0,0(s10) 0x80ecc (the retired-frame magic); beqz s7,0x80f24 at 0x80ed0, not taken:
   s7 = F, the side-stack frame (frames S3 = [(PE_CID, fp)]), F >= 4096 (frames_bounds, the atom fact on s7 below), so
   the machine-stack arm 0x80f24..0x80f60 is never run. a0 = -0xb, sb a0 to the 16 shadow bytes 0x80ed8..0x80f14;
   ld a0,0x78(s7) 0x80f18 (the frame's flag pointer, pheader's 4th conjunct); sb zero,0(a0) 0x80f1c (the flag: the
   frame is free, PcapFrame.aj_flag_store_pi, astack_free_law); j 0x80f64; a0 = 0; sp = s0 - 0x100; the 13 saved
   registers 0x80f6c..0x80f9c; sp += 0x100; at the ret. Regions: the 13 saved words (base s0, values the extra atoms
   32..44), the magic word (base s10), the flag-pointer word (base s7, value the extra atom 45 = the flag), the shadow
   (base s9), the flag byte (base atom 45). *)
Definition lv_rs : smem :=
  [ YP09.mkRegion (Some 8%nat) (-104) 0 0 0
      [YP09.mkChunk (-8) (CVal 8 (SOff 32 0)); YP09.mkChunk (-16) (CVal 8 (SOff 33 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 34 0)); YP09.mkChunk (-32) (CVal 8 (SOff 35 0));
       YP09.mkChunk (-40) (CVal 8 (SOff 36 0)); YP09.mkChunk (-48) (CVal 8 (SOff 37 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 38 0)); YP09.mkChunk (-64) (CVal 8 (SOff 39 0));
       YP09.mkChunk (-72) (CVal 8 (SOff 40 0)); YP09.mkChunk (-80) (CVal 8 (SOff 41 0));
       YP09.mkChunk (-88) (CVal 8 (SOff 42 0)); YP09.mkChunk (-96) (CVal 8 (SOff 43 0));
       YP09.mkChunk (-104) (CVal 8 (SOff 44 0))];
    YP09.mkRegion (Some 26%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 23%nat) 120 128 0 0 [YP09.mkChunk 120 (CVal 8 (SOff 45 0))];
    YP09.mkRegion (Some 25%nat) 0 16 0 16 [];
    YP09.mkRegion (Some 45%nat) 0 1 0 1 [] ].
Definition lv_facts : facts := mkFacts [(23%nat, mkAF 4096 (2 ^ 47) 6)] [] [].
Definition lv_ext (cx : ecx) (fp : Z) : list word :=
  [getr (c_regs cx) (Z_to_bv 5 1); getr (c_regs cx) (Z_to_bv 5 8); getr (c_regs cx) (Z_to_bv 5 9);
   getr (c_regs cx) (Z_to_bv 5 18); getr (c_regs cx) (Z_to_bv 5 19); getr (c_regs cx) (Z_to_bv 5 20);
   getr (c_regs cx) (Z_to_bv 5 21); getr (c_regs cx) (Z_to_bv 5 22); getr (c_regs cx) (Z_to_bv 5 23);
   getr (c_regs cx) (Z_to_bv 5 24); getr (c_regs cx) (Z_to_bv 5 25); getr (c_regs cx) (Z_to_bv 5 26);
   getr (c_regs cx) (Z_to_bv 5 27); Z_to_bv 64 (pFL cx fp)].

(* A saved word of the caller, read as a chunk whose value is an extra atom (lib/A PcapHarnessTail.chunk_saved). *)
Lemma b_chunk_saved : forall E (H : word -> bool) mem base off n (w : word) a v,
  ew E n = w -> v = bv_unsigned w -> base + off = a ->
  rdword (aview SEGS H mem) a = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem base off n w a v Hn -> Ha Hrd.
  apply (chunk_ok_val SEGS E _ base off 8 (SOff n 0) (bv_unsigned w)).
  - cbn [sv_denot]. rewrite Hn, Z.add_0_r.
    first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity | symmetry; apply Z_to_bv_bv_unsigned].
  - pose proof (bv_unsigned_in_range 64 w) as Hw. change (bv_modulus 64) with (2 ^ 64) in Hw.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn [Z.of_N]. lia.
  - rewrite Ha. exact (val_mem_of_rdword SEGS H mem a _ Hrd).
Qed.

Lemma pe_from_leave : pt_leave B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as ((Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & R23 & R25 & R26 & Hsrc).
destruct Hbody as (Hpc & Hresv & Hsvc & Hrom & Hfrg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hin).
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & HSTK). clear HJ. rename HJi into HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
unfold LLVMF_STK in Hslo, Hbot.
destruct Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct Hsaved as (Hs8 & Hsj). destruct Hhdr as (_ & _ & _ & Hh120). unfold PE_FLAGPTR in Hh120.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct Hly as (_ & _ & _ & _ & _ & EF & _).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite EF; reflexivity).
assert (EFL : flag_addr ly3 PE_CID fp = pFL cx fp) by (unfold pFL, flag_addr; rewrite EF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (frame_al64 SEGS B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (Hfa64 & _ & _). rewrite Efa in Hfa64.
destruct (al_frames _ _ LAWS _ _ _ _ _ PE_CID fp HAR Hfin) as (_ & _ & HFpres & HFSpres).
change (fs_frame_bytes PE_CID / 8) with 16 in HFSpres. change (fs_frame_bytes PE_CID) with 128 in HFpres.
rewrite Efa in HFpres, HFSpres. change (shadow_addr (pF cx fp)) with (pSH cx fp) in HFSpres.
destruct (FFL ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (HFLpres & HFLown & (HFLapp & HFLimg) & (HFL4096 & _ & HFLceil)).
rewrite EFL in HFLpres, HFLown, HFLapp, HFLimg, HFL4096, HFLceil.
assert (HSHb : 0x7fff8000 <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
assert (HSHF : pSH cx fp + 16 <= pF cx fp \/ pF cx fp + 128 <= pSH cx fp).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
  Z.div_mod_to_equations. lia. }
assert (HnF : ~ (pF cx fp <= pFL cx fp < pF cx fp + 128)) by (intros Hc; exact (proj2 (HFpres _ Hc) HFLown)).
assert (HnS : ~ (pSH cx fp <= pFL cx fp < pSH cx fp + 16)).
{ intros Hc. pose proof (proj2 (HFSpres (pFL cx fp - pSH cx fp) ltac:(lia))) as Hno.
  replace (pSH cx fp + (pFL cx fp - pSH cx fp)) with (pFL cx fp) in Hno by lia. exact (Hno HFLown). }
assert (Hsp64 : 0 <= spZ (c_regs cx) < 2 ^ 64) by (change (2 ^ 47) with 140737488355328 in H47; lia).
pose proof (ms_mkst_at ms3 (BASE + PP_leave) Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as Ems.
remember (Eimg (Ereg (ms_regs ms3) (lv_ext cx fp))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) (lv_ext cx fp)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E3 : ew E 3 = getr (ms_regs ms3) 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr (ms_regs ms3) 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 4 4%bv eq_refl)).
assert (E8 : ew E 8 = getr (ms_regs ms3) 8) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 8 8%bv eq_refl)).
assert (E23 : ew E 23 = getr (ms_regs ms3) 23) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 23 23%bv eq_refl)).
assert (E25 : ew E 25 = getr (ms_regs ms3) 25) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 25 25%bv eq_refl)).
assert (E26 : ew E 26 = getr (ms_regs ms3) 26) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat _ _ 26 26%bv eq_refl)).
assert (E32 : ew E 32 = getr (c_regs cx) (Z_to_bv 5 1)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = getr (c_regs cx) (Z_to_bv 5 8)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = getr (c_regs cx) (Z_to_bv 5 9)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = getr (c_regs cx) (Z_to_bv 5 18)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = getr (c_regs cx) (Z_to_bv 5 19)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (E37 : ew E 37 = getr (c_regs cx) (Z_to_bv 5 20)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
assert (E38 : ew E 38 = getr (c_regs cx) (Z_to_bv 5 21)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 6)).
assert (E39 : ew E 39 = getr (c_regs cx) (Z_to_bv 5 22)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 7)).
assert (E40 : ew E 40 = getr (c_regs cx) (Z_to_bv 5 23)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 8)).
assert (E41 : ew E 41 = getr (c_regs cx) (Z_to_bv 5 24)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 9)).
assert (E42 : ew E 42 = getr (c_regs cx) (Z_to_bv 5 25)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 10)).
assert (E43 : ew E 43 = getr (c_regs cx) (Z_to_bv 5 26)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 11)).
assert (E44 : ew E 44 = getr (c_regs cx) (Z_to_bv 5 27)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 12)).
assert (E45 : ew E 45 = Z_to_bv 64 (pFL cx fp)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 13)).
assert (U8 : bv_unsigned (ew E 8) = spZ (c_regs cx)) by (rewrite E8, Rs0; unfold w64; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = pF cx fp)
  by (rewrite E23, R23; unfold w64; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (U25 : bv_unsigned (ew E 25) = pSH cx fp)
  by (rewrite E25, R25; unfold w64; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (U26 : bv_unsigned (ew E 26) = pF cx fp)
  by (rewrite E26, R26; unfold w64; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (U45 : bv_unsigned (ew E 45) = pFL cx fp)
  by (rewrite E45; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).
assert (HS : st_ok_pi SEGS pa_val E (mkSS PP_leave sr_atoms lv_rs None lv_facts) (restrict (w_H W3) ms3)).
{ rewrite Ems. rewrite restrict_mkst_fx. rewrite HEdef.
  rewrite HEdef in U8, U23, U25, U26, U45, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42, E43, E44, E45.
  apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | | |].
  - unfold lv_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E32 eq_refl (Z.eq_refl _)).
        replace (spZ (c_regs cx) + -8) with (spZ (c_regs cx) - 8) by lia. exact Hs8.
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E33 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -16) with (spZ (c_regs cx) - 16 - 8 * 0) by lia. exact (Hsj 0 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E34 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -24) with (spZ (c_regs cx) - 16 - 8 * 1) by lia. exact (Hsj 1 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E35 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -32) with (spZ (c_regs cx) - 16 - 8 * 2) by lia. exact (Hsj 2 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E36 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -40) with (spZ (c_regs cx) - 16 - 8 * 3) by lia. exact (Hsj 3 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E37 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -48) with (spZ (c_regs cx) - 16 - 8 * 4) by lia. exact (Hsj 4 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E38 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -56) with (spZ (c_regs cx) - 16 - 8 * 5) by lia. exact (Hsj 5 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E39 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -64) with (spZ (c_regs cx) - 16 - 8 * 6) by lia. exact (Hsj 6 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E40 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -72) with (spZ (c_regs cx) - 16 - 8 * 7) by lia. exact (Hsj 7 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E41 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -80) with (spZ (c_regs cx) - 16 - 8 * 8) by lia. exact (Hsj 8 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E42 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -88) with (spZ (c_regs cx) - 16 - 8 * 9) by lia. exact (Hsj 9 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E43 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -96) with (spZ (c_regs cx) - 16 - 8 * 10) by lia. exact (Hsj 10 ltac:(lia)).
      * apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E44 eq_refl (Z.eq_refl _)). replace (spZ (c_regs cx) + -104) with (spZ (c_regs cx) - 16 - 8 * 11) by lia. exact (Hsj 11 ltac:(lia)).
    + rewrite U26. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (pF cx fp + o) ltac:(lia))).
    + rewrite U23. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (b_chunk_saved _ _ _ _ _ _ _ _ _ E45
        (eq_sym (unsigned_lit_small (pFL cx fp) ltac:(change (2 ^ 64) with 18446744073709551616; lia))) (Z.eq_refl _)).
      exact Hh120.
    + rewrite U25. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U45. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (pFL cx fp + o) with (pFL cx fp) by lia. exact HFLpres.
  - apply pairwise_disjoint_of_extents. unfold lv_rs, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U8, U26, U23, U25, U45.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; lia.
  - split; [|split; exact I]. cbn [lv_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U23. change (2 ^ 6) with 64. change (2 ^ 47) with 140737488355328.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
clear HEdef EL.
paj_run_flag_sh (aj_flag_store_pi B LAWS ML ASF FFL) HS HJ.
{ unfold PE_CID. lia. }
{ intros a (r & Hinr & Hr). cbn [ss_mem] in Hinr. unfold lv_rs in Hinr. cbn [In] in Hinr.
  destruct Hinr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  - rewrite U8 in Hr. lia.
  - rewrite U26 in Hr. left. right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite U23 in Hr. lia.
  - rewrite U25 in Hr. left. right. right. right. exists PE_CID, fp. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID / 8) with 16.
    change (shadow_addr (pF cx fp)) with (pSH cx fp). lia.
  - rewrite U45 in Hr. right. rewrite EFL. lia. }
{ intros msr HSr. rewrite EFL.
  pose proof (st_ok_pi_region_nth E _ msr 4 _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 45%nat (pFL cx fp) _ _ _ _ _ 0 1%N (SLit 0) 0 HR U45
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(cbv; lia)). cbn [Z.of_nat] in V. rewrite !Z.add_0_r in V. exact V. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10.
prreg HS (Z_to_bv 5 2) P2. prreg HS (Z_to_bv 5 3) P3. prreg HS (Z_to_bv 5 4) P4. prreg HS (Z_to_bv 5 8) P8.
prreg HS (Z_to_bv 5 9) P9. prreg HS (Z_to_bv 5 18) P18. prreg HS (Z_to_bv 5 19) P19. prreg HS (Z_to_bv 5 20) P20.
prreg HS (Z_to_bv 5 21) P21. prreg HS (Z_to_bv 5 22) P22. prreg HS (Z_to_bv 5 23) P23. prreg HS (Z_to_bv 5 24) P24.
prreg HS (Z_to_bv 5 25) P25. prreg HS (Z_to_bv 5 26) P26. prreg HS (Z_to_bv 5 27) P27.
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _
  (fun a => (pF cx fp <= a < pF cx fp + 8) \/ (pSH cx fp <= a < pSH cx fp + 16) \/ (pFL cx fp <= a < pFL cx fp + 1)) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
          rewrite ?U8, ?U23, ?U25, ?U26, ?U45 in HrrW; cbv beta; lia|]);
        destruct HinW)) as UN.
pose proof (frm_off_imgP B ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as Hfimg.
rewrite Efa in Hfimg. change (fs_frame_bytes PE_CID) with 128 in Hfimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hfimg.
eapply (NEXT cx k acc ly3 (stack_free_state PE_CID fp S3) W3
  (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PP_ret)) (ms_mem ms) (seg_rom SEGS)) _ HB).
- exact (gx_pack0 SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ memS HSTK HJ Hag).
- change (del_pos (frames S3) PE_CID fp = []). rewrite Hfrs. cbn [del_pos]. rewrite !Z.eqb_refl. reflexivity.
- apply (mo_le_set_fs_r MT MTF). exact Hmo.
- unfold GI_ret. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs ms_mem].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros r Hr. unfold acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]].
    - rewrite P2, E8, Rs0. unfold w64, spZ. apply Z_to_bv_bv_unsigned.
    - rewrite P3, E3. exact Rgp.
    - rewrite P4, E4. exact Rtp.
    - rewrite P8. exact E33.
    - rewrite P9. exact E34.
    - rewrite P18. exact E35.
    - rewrite P19. exact E36.
    - rewrite P20. exact E37.
    - rewrite P21. exact E38.
    - rewrite P22. exact E39.
    - rewrite P23. exact E40.
    - rewrite P24. exact E41.
    - rewrite P25. exact E42.
    - rewrite P26. exact E43.
    - rewrite P27. exact E44. }
  split; [rewrite Q1; exact E32|].
  split; [exact Q10|].
  split; [exact Hk|]. split; [exact Hacc|].
  split.
  { assert (EA : ablocks B ly3 (stack_free_state PE_CID fp S3) = ablocks B ly3 S3)
      by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
    rewrite EA. rewrite app_nil_r in Hperm. exact Hperm. }
  split; [etransitivity; [apply (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfds]|].
  split; [etransitivity; [apply (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfs]|].
  split.
  { apply (asource_none_frame (rdW W3 (ms_mem ms3))); [|exact Hsrc].
    intros a Ha. apply (mbyte_of_aview SEGS).
    destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & _).
    assert (HaF : a <> pFL cx fp) by (intros ->; exact (HFLimg Hi)).
    pose proof (src_env_num a Ha) as Ha2.
    apply UN; [change (2 ^ 64) with 18446744073709551616; lia | cbv beta; lia]. }
  { apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS).
    rewrite length_map in Ha. fold (c_n cx) in Ha.
    destruct HB as (HPRE & _ & _ & _ & Hinput & _).
    destruct Hinput as [[Hn0 Hpe] | [Hnpos Hinb]]; [unfold c_n in Ha, Hn0; lia|].
    assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hinb).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin) as (_ & _ & _ & Hpapp & Hpown & _).
    pose proof (req_size_pos (c_n cx) ltac:(unfold c_n in *; lia)) as Hrq.
    pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
    assert (HaF : a <> pFL cx fp) by (intros ->; exact (proj2 (Hpown (pFL cx fp) ltac:(lia)) HFLown)).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp.
    assert (HSHk : pSH cx fp + 16 <= 0x10007fff8000).
    { unfold pSH, shadow_of_addr, SHADOW_OFF. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
      Z.div_mod_to_equations. lia. }
    apply UN; [change (2 ^ 64) with 18446744073709551616; lia | cbv beta; lia]. }
Qed.



(* ---- the generic helpers of the call stretches: ports of lib/A/Prog/PcapHarnessTail.v's helpers, named b_<lib/A name>,
   with lib/A's statement shapes and lib/B's numbers (machine frame 0x100, s1 in [sp0 - 288, sp0 - 256], spill slots
   s1 + 0x10 .. s1 + 0x98). Written by this lane's sub-lanes for the stretches R1 .. R6 (one copy each, identical statements). ---- *)

(* ---- ports of lib/A/Prog/PcapHarnessTail.v's generic helpers: b_<lib/A name>, lib/A's statement shape with
   lib/B's numbers (machine frame 0x100, s1 in [sp0 - 288, sp0 - 256], spill slots s1 + 0x10 .. s1 + 0x98) ---- *)
Lemma b_nodup_of_split : forall {X} (l : list X),
  (forall l1 x l2 l3, l = l1 ++ x :: l2 ++ x :: l3 -> False) -> List.NoDup l.
Proof.
intros X l. induction l as [|a t IH]; intros H; [apply List.NoDup_nil|]. apply List.NoDup_cons.
- intros Hin. apply List.in_split in Hin as (t1 & t2 & ->). apply (H [] a t1 t2). reflexivity.
- apply IH. intros l1 x l2 l3 E. apply (H (a :: l1) x l2 l3). rewrite E. reflexivity.
Qed.


Lemma b_notin_prefix : forall {X} (l L M : list X) x,
  List.NoDup l -> Permutation l (L ++ M) -> List.In x M -> ~ List.In x L.
Proof.
intros X l L M x Hnd Hp HxM. apply (Permutation_NoDup Hp) in Hnd. clear Hp l.
induction L as [|a L IH]; intros Hin; [destruct Hin|].
cbn [app] in Hnd. apply List.NoDup_cons_iff in Hnd as [Hna Hnd].
destruct Hin as [-> | Hin]; [apply Hna; apply in_or_app; right; exact HxM | exact (IH Hnd Hin)].
Qed.


Lemma b_ablocks_nodup : forall ly S W mem md, AR SEGS B ly S W mem md -> List.NoDup (ablocks B ly S).
Proof.
intros ly S W mem md HAR. apply b_nodup_of_split. intros l1 x l2 l3 E.
pose proof (sep_blocks_pos SEGS B LAWS ly S W mem md x x l1 l2 l3 HAR E) as D.
assert (Hin : In x (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct x as [p n].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [R _].
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.


(* The stack facts of the body (lib/A tail_geo; a Theorem Labs lane's k3_geo is the same text without ly_bot). *)
Lemma b_tail_geo : forall cx, pe_base SK B MT KS cx ->
  spZ (c_regs cx) mod 16 = 0 /\ c_sp1 cx mod 32 = 0 /\
  spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\
  alloc_ceiling <= ly_stk_lo (c_ly cx) /\ ly_stk_lo (c_ly cx) + LLVMF_STK <= spZ (c_regs cx) /\
  spZ (c_regs cx) <= ly_stk_hi (c_ly cx) /\ ly_stk_hi (c_ly cx) <= 2 ^ 47 /\
  ly_bot (c_ly cx) + LLVMF_STK < spZ (c_regs cx) + ASTACK /\
  spZ (c_regs cx) <= ly_top (c_ly cx) /\ ly_top (c_ly cx) <= ly_stk_hi (c_ly cx).
Proof.
intros cx HB.
pose proof HB as ((_ & _ & _ & _ & _ & Hstk & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
pose proof Hstk as (Hal & Hs0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
assert (Hsp : spZ (c_regs cx) - 288 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0).
{ rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
  pose proof (Z.div_mod (spZ (c_regs cx) - 256) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 256) 32 ltac:(lia)) as M.
  split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]. }
repeat split; try assumption; try lia.
Qed.


(* A byte that is not in pe_G reads the same in the inner journal's start memory and in c_mem. *)
Lemma b_aview_memS : forall cx memS a, gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> 0 <= a < 2 ^ 64 ->
  ~ inG pe_G a -> aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a Hag Ha HnG. apply (aview_gagree SEGS pe_G _ _ _ a Hag).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.


Lemma b_gagree_high : forall cx memS a, pe_base SK B MT KS cx ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS -> alloc_ceiling <= a < 2 ^ 64 ->
  aview SEGS (w_H (c_W cx)) memS a = aview SEGS (w_H (c_W cx)) (c_mem cx) a.
Proof.
intros cx memS a _ Hag Ha. pose proof asan_consts as (C1 & _).
apply (b_aview_memS cx memS a Hag ltac:(lia)).
pose proof (pa_obj_img 4 ltac:(lia)) as O4. pose proof (pa_obj_img 2 ltac:(lia)) as O2.
unfold pcap_img_end, YImgTop.IMG_TOP in O4, O2.
unfold pe_G. intros HG.
apply inG_cons in HG as [HG|HG]; [|apply inG_cons in HG as [HG|HG]; [|exact (inG_nil a HG)]];
  unfold in_zr in HG; cbn [fst snd] in HG; lia.
Qed.


(* The chain the harness hands to a callee: its own frame record, when it lies below the stack top. *)
Lemma b_pch_achain : forall cx own memS ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  achain ly3 (aview SEGS (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)) (pch cx).
Proof.
intros cx own memS ly3 S3 W3 mem3 md3 k HB HJ Hag R8 R16.
pose proof (b_tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hlo.
pose proof HB as ((_ & _ & Hra4 & _ & _ & _ & _ & Hch & _) & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
apply (achain_ly_top (c_ly cx)); [exact Etop|].
assert (H8 : spZ (c_regs cx) mod 8 = 0).
{ pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
  apply Z.mod_divide; [lia|]. exists (2 * (spZ (c_regs cx) / 16)). lia. }
pose proof asan_consts as (C1 & _).
assert (Hc0 : alloc_ceiling <= spZ (c_regs cx)) by lia.
assert (Ht64 : ly_top (c_ly cx) <= 2 ^ 64) by (change (2 ^ 47) with 140737488355328 in H47;
  change (2 ^ 64) with 18446744073709551616; lia).
unfold pch. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
- assert (HK : forall a, spZ (c_regs cx) <= a < 2 ^ 64 ->
    aview SEGS (w_H W3) mem3 a = aview SEGS (w_H (c_W cx)) (c_mem cx) a)
    by (intros a Ha; rewrite <- (b_gagree_high cx memS a HB Hag ltac:(lia)); apply F1; lia).
  refine (achain_push _ _ _ _ _ _ _ _ Hch Ht64 HK R8 R16 Hra4 Hc0 H8 _ _); lia.
- left. split; [right; left; lia | reflexivity].
Qed.


(* The source's meta invariant at a state of the walk (PSourceMeta.asrc_meta_inv_kept through the inner journal). *)
Lemma b_meta_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  asrc_meta_inv SEGS KS ly3 (rdW W3 mem3) (c_M cx).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (HX & Himg & Hp & Hm & H0 & H47 & Hal & HZ) & _ & _ &
  _ & _ & _ & HGX & HGD & _).
pose proof HJ as (HAR' & Hly & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _ & _ & _ & _ & F5 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
split; [rewrite Eextra; exact HX|]. split; [exact Himg|].
split; [exact (asrc_meta_ptr_of_AR SK SEGS B KS ASIL _ _ _ _ _ HAR')|]. split.
- eapply val_mem_frame; [|exact Hm]. intros x Hx. cbn in Hx. apply (mbyte_of_aview SEGS).
  destruct (asil_meta _ _ _ _ ASIL x ltac:(lia)) as (Hi & Hns & He & Hlt).
  pose proof (pa_img_range x Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
  rewrite <- (b_aview_memS cx memS x Hag ltac:(lia)).
  + apply (F3 x Hi Hns He). apply fp_spares_below. exact Hlt.
  + intros HxG. destruct (HGD x HxG) as (_ & Hnm & _). apply Hnm. lia.
- split; [exact H0|]. split; [exact H47|]. split; [exact Hal|].
  intros a Ha. rewrite <- (HZ a Ha). apply (mbyte_of_aview SEGS).
  rewrite <- (b_aview_memS cx memS a Hag ltac:(lia)).
  + apply F5.
    * apply Exists_exists. exists (c_M cx, AMETA_SIZE). split; [exact HX | unfold in_zr; cbn [fst snd]; lia].
    * intros He. pose proof (asil_errno_img _ _ _ _ ASIL a He) as Hi. pose proof (Himg a Hi). lia.
  + intros HaG. pose proof (proj1 (HGX a HaG)) as Hi. pose proof (Himg a Hi). lia.
Qed.


(* The read-only data at a state of the walk (PcapBase.arodata_ok_journalP through the inner journal). *)
Lemma b_aro_now : forall cx memS own ly3 S3 W3 mem3 md3 k,
  pe_base SK B MT KS cx ->
  ajournal SEGS B LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
    own ly3 S3 W3 mem3 md3 k ->
  gagree pe_G (w_H (c_W cx)) (c_mem cx) memS ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W3) mem3).
Proof.
intros cx memS own ly3 S3 W3 mem3 md3 k HB HJ Hag.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _ & _ & _ & _ & _ & _ & _ & _ & HGX & HGD & _).
eapply (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img); [exact HJ|].
intros a Hro Ho He.
assert (Hi : in_img SEGS a)
  by (destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)]).
pose proof (pa_img_range a Hi) as Hxr. unfold pcap_img_end, YImgTop.IMG_TOP in Hxr.
rewrite (b_aview_memS cx memS a Hag ltac:(lia)); [exact (Hrod a Hro Ho He)|].
intros HaG. exact (proj1 (HGD a HaG) Hro).
Qed.


(* The bytes of the body every cut states and no callee may change: the saved registers, the spill slots
   s1 + 0x10 .. s1 + 0x98, the frame header and the frame's shadow, and the input. *)
Definition b_hfoot (cx : ecx) (fp a : Z) : Prop :=
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)) \/ (c_sp1 cx + 16 <= a < c_sp1 cx + 152) \/
  (pF cx fp <= a < pF cx fp + 24 \/ pF cx fp + 120 <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) \/
  (c_p cx <= a < c_p cx + c_n cx).


Lemma b_tail_kept : forall (cx : ecx) fp W ms W' ms' sh,
  (forall a, b_hfoot cx fp a -> aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  psaved cx W ms -> pheader cx fp W ms -> pshadow cx fp W ms sh -> length sh = PE_NSH ->
  garr8 SEGS (rdW W (ms_mem ms)) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) ->
  pslots cx fp W ms ->
  psaved cx W' ms' /\ pheader cx fp W' ms' /\ pshadow cx fp W' ms' sh /\
  garr8 SEGS (rdW W' (ms_mem ms')) (c_p cx) (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  pslots cx fp W' ms'.
Proof.
intros cx fp W ms W' ms' sh HK (Hs8 & Hsj) (Hh0 & Hh8 & Hh16 & Hh120) Hsh Hlen Hin (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
assert (RW : forall a, (forall i, 0 <= i < 8 -> b_hfoot cx fp (a + i)) ->
  rdword (aview SEGS (w_H W') (ms_mem ms')) a = rdword (aview SEGS (w_H W) (ms_mem ms)) a)
  by (intros a Ha; apply rdword_ext; intros i Hi; apply HK, Ha, Hi).
split; [|split; [|split; [|split]]].
- split.
  + rewrite RW; [exact Hs8|]. intros i Hi. unfold b_hfoot. left. lia.
  + intros j Hj. rewrite RW; [exact (Hsj j Hj)|]. intros i Hi. unfold b_hfoot. left. lia.
- unfold pheader, PE_FLAGPTR in *.
  split; [|split; [|split]]; (rewrite RW; [assumption|]); intros i Hi; unfold b_hfoot; right; right; left;
  first [left; lia | right; lia].
- intros i Hi. rewrite HK; [exact (Hsh i Hi)|]. unfold b_hfoot. right; right; right; left.
  rewrite Hlen in Hi. unfold PE_NSH in Hi. lia.
- apply (garr8_frame SEGS _ _ _ _ Hin). intros a Ha. apply (mbyte_of_aview SEGS). apply HK.
  unfold b_hfoot. right; right; right; right. rewrite length_map in Ha. unfold c_n. lia.
- unfold pslots, pslot, PS_F0, PS_D, PS_SHB, PS_SH, PS_F, PS_FK, PS_TSP, PS_CAP in *.
  repeat split; (rewrite RW; [assumption|]); intros i Hi; unfold b_hfoot; right; left; lia.
Qed.


(* The clauses a callee's post keeps (nx_kept / acall_kept / tclose_kept / topen_kept, clauses 1, 2 and 4), for the
   harness's body bytes, when its write set E misses them. *)
Lemma b_foot_kept : forall (cx : ecx) fp lyc Sc (W : world SEGS) (memc : word -> option byte) (W2 : world SEGS)
  (mem2 : word -> option byte) slo shi (E : Z -> Prop),
  pe_base SK B MT KS cx ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> ~ E a ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) ->
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) ->
  shi <= c_sp1 cx + 16 ->
  In (PE_CID, fp) (frames Sc) -> frame_addr lyc PE_CID fp = pF cx fp ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B lyc Sc)) ->
  (forall a, b_hfoot cx fp a -> ~ E a) ->
  forall a, b_hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros cx fp lyc Sc W memc W2 mem2 slo shi E HB K1 K2 K4 Hshi Hfr Efa Hinb HE a Ha.
pose proof (b_tail_geo cx HB) as (Hal & Hs1 & Hs1b & Hceil & Hlo & Hhi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hlo. change (2 ^ 47) with 140737488355328 in H47.
pose proof (HE a Ha) as HnE.
destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
- apply K1; [change (2 ^ 64) with 18446744073709551616; lia | lia | exact HnE].
- apply K1; [change (2 ^ 64) with 18446744073709551616; lia | lia | exact HnE].
- apply (K4 PE_CID fp a Hfr); [|exact HnE]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes PE_CID) with 128. lia.
- apply (K4 PE_CID fp a Hfr); [|exact HnE]. right. unfold in_zr. cbn [fst snd]. rewrite Efa.
  change (fs_frame_bytes PE_CID / 8) with 16. unfold pSH, shadow_of_addr in Ha. unfold shadow_addr. lia.
- destruct (Z_lt_le_dec 0 (c_n cx)) as [Hn|Hn]; [|lia].
  replace a with (c_p cx + (a - c_p cx)) by lia. apply (K2 (c_p cx) (c_n cx) (a - c_p cx) (Hinb Hn)).
  + pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
  + replace (c_p cx + (a - c_p cx)) with a by lia. exact HnE.
Qed.


(* The input block, when there is one, is one of the caller's blocks and stays a block at every cut. *)
Lemma b_input_block : forall cx ly3 S3 L,
  pe_base SK B MT KS cx -> Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3).
Proof.
intros cx ly3 S3 L HB HP Hn. pose proof HB as (_ & _ & _ & _ & Hinp & _).
destruct Hinp as [[H0 _] | [_ Hin]]; [lia|].
apply (Permutation_in _ (Permutation_sym HP)). apply in_or_app. left. exact Hin.
Qed.


(* A heap block the call allocated since its start (not one of its caller's) misses every body byte. *)
Lemma b_block_off_hfoot : forall cx fp ly3 S3 W3 mem3 md3 L p n,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (p, n) (ablocks B ly3 S3) -> ~ In (p, n) (ablocks B (c_ly cx) (c_S cx)) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  forall a, b_hfoot cx fp a -> ~ (p <= a < p + req_size n).
Proof.
intros cx fp ly3 S3 W3 mem3 md3 L p n HB HAR HP Hin Hout Hfin Efa x Hx Hex.
pose proof (b_tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ p n PE_CID fp HAR Hin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite Efa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
unfold b_hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp.
destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [lia | lia | lia | lia |].
assert (Hcn : 0 < c_n cx) by lia.
pose proof (b_input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
assert (Hne : (c_p cx, c_n cx) <> (p, n)).
{ intros Heq. apply Hout. rewrite <- Heq. pose proof HB as (_ & _ & _ & _ & [[H0 _] | [_ Hin0]] & _); [lia | exact Hin0]. }
pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D.
pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.


(* Bytes of the call's own frame past its 24-byte header (ps, ts) miss every body byte. *)
Lemma b_frame_off_hfoot : forall cx fp ly3 S3 W3 mem3 md3 L q m,
  pe_base SK B MT KS cx -> AR SEGS B ly3 S3 W3 mem3 md3 ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (PE_CID, fp) (frames S3) -> frame_addr ly3 PE_CID fp = pF cx fp ->
  pF cx fp + 24 <= q -> q + m <= pF cx fp + 120 ->
  forall a, b_hfoot cx fp a -> ~ (q <= a < q + m).
Proof.
intros cx fp ly3 S3 W3 mem3 md3 L q m HB HAR HP Hfin Efa Hq1 Hq2 x Hx Hex.
pose proof (b_tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 mem3 md3 PE_CID fp HAR Hfin) as (Hf4096 & Hfceil & Hfapp).
rewrite Efa in Hf4096, Hfceil, Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfceil, Hfapp.
unfold b_hfoot, pSH, shadow_of_addr, SHADOW_OFF in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]]; [lia | lia | lia | lia |].
assert (Hcn : 0 < c_n cx) by lia.
pose proof (b_input_block cx ly3 S3 _ HB HP Hcn) as Hpin.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ PE_CID fp HAR Hpin Hfin) as D.
unfold zdisjoint in D. cbn [fst snd] in D. rewrite Efa in D. change (fs_frame_bytes PE_CID) with 128 in D.
pose proof (req_size_pos (c_n cx) ltac:(lia)). lia.
Qed.



(* lib/A pC_nth / magicZ_magic / goodZ_good / swZ_sw over lib/B's p_C, p_F, p_good, p_swz. *)
Lemma b_pC_nth : forall cx j, nth j (p_C cx) 0 = bv_unsigned (nth j (p_F cx) (Z_to_bv 8 0)).
Proof.
  intros cx j. unfold p_C.
  rewrite <- (map_nth (fun x : byte => bv_unsigned x) (p_F cx) (Z_to_bv 8 0) j).
  reflexivity.
Qed.


Lemma b_magicZ_magic : forall cx, AO.pcap_magicZ (p_C cx) = PST.pcap_magic (p_F cx).
Proof.
  intros cx. unfold AO.pcap_magicZ, PST.pcap_magic, PST.pcap_byte. rewrite !b_pC_nth. reflexivity.
Qed.


Lemma b_goodZ_good : forall cx, AO.pcap_goodZ (p_C cx) = p_good cx.
Proof.
  intros cx. unfold AO.pcap_goodZ, p_good, PST.pcap_good. rewrite b_magicZ_magic.
  unfold p_C. rewrite length_map. reflexivity.
Qed.


Lemma b_swZ_sw : forall cx, AO.pcap_swZ (p_C cx) = p_swz cx.
Proof. intros cx. unfold AO.pcap_swZ, p_swz, PST.pcap_sw. rewrite b_magicZ_magic. reflexivity. Qed.



(* lib/A PcapHarnessTail.o_mod16 with lib/B's numbers: the call's stack offset s1 - sp0 is a multiple of 16. *)
Lemma b_o_mod16 : forall cx, pe_base SK B MT KS cx -> (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0.
Proof.
intros cx HB.
pose proof HB as ((_ & _ & _ & _ & _ & (Hal & _) & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
rewrite Hsp1. unfold pe_sp1, PE_MFRAME.
pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D. rewrite Hal, Z.add_0_r in D.
apply Z.mod_divide; [lia|]. exists (2 * ((spZ (c_regs cx) - 256) / 32) - spZ (c_regs cx) / 16). lia.
Qed.


(* ---- R3: PP_K8 0x80e68 -> PP_K9 0x80e74 (the second pcap_source_close) ----
   0x80e68 `bne a0,s5` to PP_abort (0x81034): refuted at the branch, a0 = s5 = p_first cx (GI_K8);
   0x80e6c `mv a0,s4` (ps); 0x80e70 `jal pcap_source_close` (the Section hypothesis CLOSE, lifted by
   PcapEntryCalls.close_call). Template: lib/A/Prog/PcapHarnessTail.v tail_R3 and its helpers (the b_* ports below
   have lib/A's statement shapes with lib/B's numbers: the machine frame is 256 bytes, s1 in [sp0 - 288, sp0 - 256],
   the spill slots are s1 + 16 .. s1 + 152). *)


(* pt_K8: R3, PP_K8 0x80e68 -> PP_K9 0x80e74. *)
Lemma pe_from_K8 : pt_K8 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HG.
destruct HG as (b & buf & h & HC & Hn26 & Hgood & R10 & R18 & R20 & R21 & Hsl & Hbuf & Hpso & Hsrc).
pose proof HC as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hev & _).
unfold LLVMF_STK in Hspc. unfold PE_FRAME in Hf1.
(* what pcap_source_close's premises read at the start memory, before the run (which writes nothing) *)
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & _).
pose proof (b_aro_now cx memS _ ly3 S3 W3 (ms_mem ms3) md3 k HB HJi Hag) as HROD.
pose proof (b_meta_now cx memS _ ly3 S3 W3 (ms_mem ms3) md3 k HB HJi Hag) as HMETA.
pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnev & _).
clear HJi Hag.
(* the blocks: the copy b and the FILE h, which the call allocated (not its caller's) *)
assert (Hb3 : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hh3 : In (h, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 h SRC_FILE_BLOCK HAR Hh3) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 b (p_nF cx) HAR Hb3) as (_ & Hb4096 & Hbceil & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (Hhout : ~ In (h, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx))).
{ intros Hin.
  refine (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (buf, p_bn cx)])
    h SRC_FILE_BLOCK HAR _ _).
  - rewrite <- app_assoc. exact Hperm.
  - apply in_or_app. left. exact Hin. }
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
(* the symbolic state at 0x80e68: no memory region (the stretch reads and writes no memory) *)
assert (Ems : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K8)) (ms_mem ms3) (seg_rom SEGS))
  by exact (ms_mkst_at ms3 (BASE + PP_K8) Hpc Hrv Hsv Hrom Hfreg Hfcsr).
assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (mkSS PP_K8 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K8)) (ms_mem ms3) (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
  [apply regs_ok_Eimg_Ereg | reflexivity | constructor | exact I | split; [exact I | split; exact I]]. }
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
clear HEdef.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
rewrite Ems.
psrr_branch_tok RUN BR HS SHOK Espan.
- (* 0x80e68 taken (to PP_abort 0x81034): a0 <> s5. Both are the reader's first answer (GI_K8 R10, R21): refuted. *)
  exfalso. rewrite branch_ne_U in Hc. unfold U in Hc. cbn [sv_denot] in Hc.
  rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl),
    R10, R21, Z.eqb_refl in Hc.
  discriminate Hc.
- (* 0x80e68 not taken; 0x80e6c mv a0,s4; 0x80e70 jal pcap_source_close *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Espan; [apply awr_ok_x_of0; apply awr_ok_nil |].
  pose proof (no_write_run_mem _ _ _ _ HF ltac:(intros r Hr; destruct Hr)) as Hm1.
  rewrite Hm1 in HJ.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
  prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20.
  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10, Q20.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
  assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
  assert (HTS : AC.TPCAP_SOURCE_CLOSE_STK = 16560) by reflexivity.
  pmkst HS. rewrite Hm1, pa_sigma_pcap_source_close.
  eapply SRr_bind.
  { eapply (close_call SK B MT KS CLOSE LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
      (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) _ k (ms_regs ms) (pPS cx fp) h b (c_M cx)
      (p_pos cx (p_q cx 24)) (p_C cx) PE_CID fp HJ).
    - exact HROD.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
    - rewrite Q3, Rgp. exact Hgp0.
    - rewrite Q4, Rtp. exact Htp0.
    - exact Q10.
    - rewrite Usp. lia.
    - rewrite Usp, HTS. unfold LLVMF_STK. lia.
    - rewrite Usp. lia.
    - left. reflexivity.
    - rewrite Efa. unfold pPS, PO_PS. lia.
    - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold pPS, PO_PS. lia.
    - unfold pPS, PO_PS. split; [lia | exact (mod64_mod8 _ Hf64)].
    - exact (proj1 Hpso).
    - lia.
    - apply zero_shadow_range; [unfold pPS, PO_PS; exact (mod64_mod8 _ Hf64) | reflexivity |].
      intros i Hi. change (8 / 8) with 1 in Hi. replace i with 0 by lia. rewrite Z.add_0_r.
      unfold pPS, PO_PS. rewrite shadow_of_addr_aligned_off by lia.
      change (32 / 8) with 4. exact (Hsh 4%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    - intros _. split; [exact Hh3|]. split; [rewrite p_lens; exact Hb3|].
      split; [exact Hsrc|]. split; [exact HMETA|].
      intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
      right. exists h, SRC_FILE_BLOCK. split; [exact Hh3|]. split; [exact Hhout|].
      change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. lia.
    - unfold AC.EV_CLOSE. change EV_LIB with 10 in Hev. lia. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfr2 & Hmle & Hfd2 & Hfs2 & HPm & Hnull
    & HK & Hsrc2).
  assert (Hh0 : h <> 0) by lia.
  destruct (Hsrc2 Hh0) as [Hnone2 Hcopy2].
  unfold AC.tclose_fblk in HPm. rewrite (proj2 (Z.eqb_neq h 0) Hh0) in HPm, Hmle. cbn [app] in HPm.
  destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
  assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
    by exact HP2.
  (* the body's bytes, kept by the callee (its write set: ps.f and the FILE block h) *)
  assert (Hfoot : forall a, b_hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { refine (b_foot_kept cx fp ly3 S3 W3 (ms_mem ms3) W2 mem2 _ _
      (fun a => (pPS cx fp <= a < pPS cx fp + 8) \/ (h <> 0 /\ h <= a < h + req_size SRC_FILE_BLOCK)) HB
      (fun a Ha Hn _ => K1 a Ha Hn) K2 K4 _ Hfin Efa (b_input_block cx ly3 S3 _ HB Hperm) _); [rewrite Usp; lia|].
    intros x Hx [Hx1 | [_ Hx2]].
    - exact (b_frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) 8 HB HAR Hperm Hfin Efa
        ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS; lia) x Hx Hx1).
    - exact (b_block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ h SRC_FILE_BLOCK HB HAR Hperm Hh3 Hhout Hfin Efa
        x Hx Hx2). }
  assert (MK : mkw W3 W2 (ms_mem ms3) (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + PP_K9)) mem2 (seg_rom SEGS)))
    (fun a => ~ b_hfoot cx fp a)).
  { intros a Ha HnR. cbn [ms_mem mkst]. apply Hfoot. unfold b_hfoot in *. lia. }
  rewrite Q1.
  apply (NEXT cx fp (k + AC.EV_CLOSE) (acc + (mo_free MT + mo_free MT)) ly2 S2 W2
    (mkst regs2 (Z_to_bv 64 (BASE + PP_K9)) mem2 (seg_rom SEGS)) md2 HB HJ2).
  + rewrite Hfr2. exact Hfr.
  + exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle).
  + exists b, buf.
    split.
    { split; [|split; [unfold AC.EV_CLOSE; lia | split; [unfold PA_K9; lia | split; [|split]]]].
      - apply (pe_body_keepw cx fp PP_K8 PP_K9 W3 W2 ms3 (mkst regs2 (Z_to_bv 64 (BASE + PP_K9)) mem2 (seg_rom SEGS))
          PSH_ts (fun a => ~ b_hfoot cx fp a) Hbody); try reflexivity.
        + cbn [ms_regs mkst]. exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2).
        + cbn [ms_regs mkst]. exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8).
        + cbn [ms_regs mkst]. exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9).
        + cbn [ms_regs mkst]. exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3).
        + cbn [ms_regs mkst]. exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4).
        + exact MK.
        + intros a Ha HR. apply HR. unfold b_hfoot. lia.
        + intros a Ha HR. apply HR. unfold b_hfoot. lia.
        + intros a Ha HR. apply HR. unfold b_hfoot. unfold PE_FLAGPTR in Ha. lia.
        + intros a Ha HR. apply HR. unfold b_hfoot. lia.
        + intros a Ha HR. apply HR. unfold b_hfoot. lia.
        + unfold LLVMF_STK. lia.
        + lia.
        + exact Hf0.
        + unfold PE_FRAME. lia.
        + exact Hinp.
      - assert (HP' : Permutation ((h, SRC_FILE_BLOCK) :: ablocks B ly2 S2)
          ((ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (buf, p_bn cx)]) ++ [(h, SRC_FILE_BLOCK)])).
        { rewrite <- app_assoc. cbn [app]. exact (Permutation_trans (Permutation_sym HPm) Hperm). }
        pose proof (Permutation_app_inv [] _ _ [] _ HP') as Hq. cbn [app] in Hq. rewrite app_nil_r in Hq. exact Hq.
      - rewrite Hfd2, (proj1 (AC.wvb_fds_fs _ _ _)). exact Hfds.
      - rewrite Hfs2, (proj2 (AC.wvb_fds_fs _ _ _)). exact Hfs. }
    split; [exact Hn26|].
    split; [cbn [ms_regs mkst]; exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18)|].
    split; [cbn [ms_regs mkst]; exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Q20)|].
    split.
    { apply (pslots_keepw cx fp W3 W2 ms3 _ (fun a => ~ b_hfoot cx fp a) Hsl MK); [|lia | lia].
      intros a Ha Hn HR. apply HR. unfold b_hfoot. lia. }
    split.
    { apply (pslot_keepw_apart cx W3 W2 ms3 _ _ PS_BUF buf Hbuf MK); [| lia | lia |].
      - intros a Ha Hn HR. apply HR. unfold b_hfoot. lia.
      - unfold PS_FK, PS_D, PS_F, PS_SH, PS_VMASK, PS_BUF12, PS_USEC, PS_SHB, PS_FIRST, PS_TSP, PS_BUF, PS_CALLS,
          PS_CAP, PS_F0. lia. }
    split; [exact Hcopy2|].
    split; [exact Hnull | exact Hnone2].
Qed.


(* ---- helpers (R5, R6) ---- *)


(* What a free of a block (pa, n) the call allocated keeps of a cut: free's kept clause (acall_kept, callee stack
   window [slo, shi) under s1 + 16) keeps the body bytes pe_body states, the spill slots and the stream's environment;
   R is the set of bytes that changed, so mkw holds by the decidable equality of bytes. *)
Lemma r56_free_keep : forall cx fp pc pc' k ly3 S3 W3 (ms3 ms4 : machine_state) md3 (W2 : world SEGS) sh L pa n
    slo shi,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) ->
  In (pa, n) (ablocks B ly3 S3) -> ~ In (pa, n) (ablocks B (c_ly cx) (c_S cx)) ->
  acall_kept SEGS B ly3 S3 W3 (ms_mem ms3) W2 (ms_mem ms4) slo shi (fun a => pa <= a < pa + req_size n) ->
  shi <= c_sp1 cx + 16 ->
  pe_body cx fp pc W3 ms3 sh ->
  ms_pc_val ms4 = w64 (BASE + pc') -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  getr (ms_regs ms4) 2 = getr (ms_regs ms3) 2 -> getr (ms_regs ms4) 8 = getr (ms_regs ms3) 8 ->
  getr (ms_regs ms4) 9 = getr (ms_regs ms3) 9 -> getr (ms_regs ms4) 3 = getr (ms_regs ms3) 3 ->
  getr (ms_regs ms4) 4 = getr (ms_regs ms3) 4 ->
  pslots cx fp W3 ms3 -> asource_none SEGS KS (mrestrict (w_H W3) (ms_mem ms3)) ->
  pe_body cx fp pc' W2 ms4 sh /\ pslots cx fp W2 ms4 /\ asource_none SEGS KS (mrestrict (w_H W2) (ms_mem ms4)).
Proof.
intros cx fp pc pc' k ly3 S3 W3 ms3 ms4 md3 W2 sh L pa n slo shi HB HJ Hfr HP Hin Hout HK Hshi Hbody
  Hpc Hrv Hsv Hrom Hfreg Hfcsr E2 E8 E9 E3 E4 Hslots Hsn.
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (_ & HAR & _ & Hspc & Hsp47 & _ & _ & Hf0 & Hf1 & _ & HEF & Hinp & Hs1lo & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HK as (K1 & K2 & K3 & K4 & _).
set (R := fun a => aview SEGS (w_H W2) (ms_mem ms4) a <> aview SEGS (w_H W3) (ms_mem ms3) a).
assert (HM : mkw W3 W2 (ms_mem ms3) (ms_mem ms4) R).
{ intros a _ HnR.
  destruct (decide (aview SEGS (w_H W2) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a)) as [e|ne];
    [exact e | exfalso; exact (HnR ne)]. }
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
assert (EFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 pa n HAR Hin) as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & Hbn).
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ pa n PE_CID fp HAR Hin Hfin) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EFa in Dbf. change (fs_frame_bytes PE_CID) with 128 in Dbf.
pose proof (req_size_pos n ltac:(lia)) as [Hrq1 Hrq2].
unfold PE_FRAME in Hf1. unfold LLVMF_STK in Hspc.
assert (Hframe : forall a, pF cx fp <= a < pF cx fp + 128 -> ~ R a).
{ intros a Ha HR. apply HR. apply (K4 PE_CID fp a Hfin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes PE_CID) with 128. lia.
  - cbv beta. lia. }
assert (Hshad : forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ R a).
{ intros a Ha HR. apply HR. apply (K4 PE_CID fp a Hfin).
  - right. unfold in_zr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes PE_CID / 8) with 16.
    unfold shadow_addr. unfold pSH, shadow_of_addr in Ha. lia.
  - cbv beta. intros Hx. unfold pSH, shadow_of_addr, SHADOW_OFF in Ha.
    exact (fshadow_not_app (pF cx fp) 16 pa (req_size n) a ltac:(lia)
             ltac:(change (2 ^ 47) with 140737488355328; lia) Hbapp ltac:(lia) Hx). }
assert (Hinput : forall a, c_p cx <= a < c_p cx + c_n cx -> ~ R a).
{ intros a Ha HR. apply HR.
  pose proof HB as (_ & _ & _ & _ & Hinb & _).
  destruct Hinb as [[Hn0 _] | [Hnpos Hinb]]; [lia|].
  assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HP)); apply in_or_app; left; exact Hinb).
  assert (Hne : (c_p cx, c_n cx) <> (pa, n)) by (intros Heq; apply Hout; rewrite <- Heq; exact Hinb).
  pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hpin Hin Hne) as D. unfold zdisjoint in D.
  cbn [fst snd] in D.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq3].
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin); [lia | cbv beta; lia]. }
assert (Hstack : forall a, c_sp1 cx + 16 <= a < spZ (c_regs cx) -> ~ R a).
{ intros a Ha HR. apply HR. apply K1; lia. }
split; [|split].
- apply (pe_body_keepw cx fp pc pc' W3 W2 ms3 ms4 sh R Hbody Hpc Hrv Hsv Hrom Hfreg Hfcsr E2 E8 E9 E3 E4 HM);
    [ intros a Ha; apply Hstack; lia
    | intros a Ha; apply Hframe; lia
    | intros a Ha; apply Hframe; unfold PE_FLAGPTR in Ha; lia
    | exact Hshad
    | exact Hinput
    | unfold LLVMF_STK; lia | exact Hsp47 | exact Hf0 | unfold PE_FRAME; lia | exact Hinp ].
- apply (pslots_keepw cx fp W3 W2 ms3 ms4 R Hslots HM); [intros a Ha _; apply Hstack; lia | lia | lia].
- apply (asource_none_keepw B KS ASIL W3 W2 (ms_mem ms3) (ms_mem ms4) R Hsn HM).
  intros a Ha HR. apply HR. destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
Qed.


(* ---- R5: PP_K10 0x80e88 `addi a1,zero,-1`, 0x80e8c `bne a0,a1` to PP_abort 0x81034 (refuted: a0 = -1, GI_K10),
   0x80e90 `ld a0,0x60(s1)` (PS_BUF: buf), 0x80e94 `jal __wrap_free` (the record buffer) -> PP_K11 0x80e98 ---- *)


(* The symbolic state at PP_K10: atom 32 = buf, the word of the spill slot PS_BUF, read only. *)
Definition r56_k10_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_BUF (PS_BUF + 8) 0 0 [YP09.mkChunk PS_BUF (CVal 8 (SOff 32 0))]].

Definition r56_k10_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].


Lemma pe_from_K10 : pt_K10 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HG.
destruct HG as (b & buf & HC & Hn26 & R10 & R18 & Hslots & SBUF & Hnull & Hsn).
pose proof HC as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
unfold LLVMF_STK in Hspc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (Rsp & Rs0 & Rs1 & Rgp & Rtp) & Hsav & _).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ & _ & _ &
  Hmok & Hneed & _ & _ & _ & Hftr).
assert (Hbin : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hperm' : Permutation (ablocks B ly3 S3) ((ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) ++ [(buf, p_bn cx)]))
  by (rewrite <- app_assoc; exact Hperm).
pose proof (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ buf (p_bn cx) HAR Hperm') as Hbout.
assert (Hbout0 : ~ In (buf, p_bn cx) (ablocks B (c_ly cx) (c_S cx)))
  by (intros Hc; apply Hbout; apply in_or_app; left; exact Hc).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hbin) as (_ & Hu4096 & Huceil & _).
pose proof (p_sizes cx) as (_ & _ & Hbn).
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [Hrq1 Hrq2].
pose proof HJ as HJ0.
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnev & Hk0 & _).
pose proof (ms_mkst_at ms3 (BASE + PP_K10) Hpc Hrv Hsv Hrom Hfreg Hfcsr) as Ems.
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *.
set (E := Eimg (Ereg regs [w64 buf])).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat regs _ i r Hr)).
assert (E32 : ew E 32 = w64 buf)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS pa_val E (mkSS PP_K10 sr_atoms r56_k10_regions None r56_k10_facts)
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_K10)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold r56_k10_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. unfold PS_BUF. split; [lia|]. split; [change (2 ^ 64) with 18446744073709551616; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 32 0) buf);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616; lia
      | cbn [Z.of_N]; lia |].
    exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ SBUF).
  - apply pairwise_disjoint_of_extents. unfold r56_k10_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint].
    repeat split; try exact I.
  - split; [|split; [exact I | exact I]].
    cbn [r56_k10_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
rewrite Ems.
paj_run_tok RUN HS HJ SHOK Espan;
  [apply awr_ok_x_of0; cbn [ss_mem r56_k10_regions]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
assert (Hm1 : ms_mem ms = mem)
  by (refine (no_write_run_mem _ _ _ _ HF _); intros r Hr; cbn [ss_mem r56_k10_regions In] in Hr;
      destruct Hr as [<- | []]; cbn; lia).
clear HF HFr HG. rename ms into ms1. rename mat into mat1.
psrr_branch_tok RUN BR HS SHOK Espan.
- (* 0x80e8c taken, to PP_abort 0x81034: refuted, a0 = -1 (GI_K10's conjunct on register 10) = a1 *)
  exfalso. cbn [branch_taken sv_denot] in Hc.
  rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10 in Hc. vm_compute in Hc. discriminate Hc.
- (* not taken: 0x80e90 ld a0,0x60(s1); 0x80e94 jal __wrap_free *)
  clear Hc.
  paj_run_tok RUN HS HJ SHOK Espan;
    [apply awr_ok_x_of0; cbn [ss_mem add_cond]; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
  assert (Hm : ms_mem ms = mem)
    by (rewrite <- Hm1; refine (no_write_run_mem _ _ _ _ HF _); intros r Hr; cbn [ss_mem add_cond In] in Hr;
        destruct Hr as [<- | []]; cbn; lia).
  pmkst HS. rewrite (pal_free B TL).
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.

  rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
  rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
  rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
  rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
  rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
  rewrite E32 in Q10.
  rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q18.
  pose proof (@pa_base_lo _ _ PL_pcap PI) as HBLO.
  assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
  assert (Ura : raZ (ms_regs ms) = BASE + PP_K11)
    by (unfold raZ; rewrite Q1; apply unsigned_lit_small; unfold PP_K11; lia).
  assert (Hch : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) (pch cx)).
  { rewrite Hm.
    assert (Hs16 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
    { pose proof (proj2 Hsav 0 ltac:(lia)) as H0.
      replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
    apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (pch cx) (ms_regs ms)
             (b_pch_achain cx _ memS ly3 S3 W3 mem md3 k HB HJi Hag (proj1 Hsav) Hs16)).
    - rewrite Usp. lia.
    - unfold s0Z. rewrite Q8, Rs0. apply unsigned_lit_small. lia.
    - rewrite Ura. unfold PP_K11. lia. }
  assert (Htr : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms) (pch cx)) (as_universe B)).
  { apply Hftr. rewrite Ura. replace (BASE + PP_K11 - BASE) with PP_K11 by lia.
    unfold PE_FREE_SITES, PP_K11. cbn [In]. right; left; reflexivity. }
  assert (Hmok' : mo_ok MT S3 (mo_free MT)).
  { apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL Hmok Hmo (mo_free_nonneg MT MTL)).
    pose proof (PA_K12_need MT MTL cx) as Hn. pose proof (mo_free_nonneg MT MTL).
    unfold PA_K12, PA_K11 in Hn. lia. }
  assert (Hnev' : st_nev S3 < EV_MAX) by (change EV_LIB with 10 in Hev; lia).
  assert (Hspo : spZ (ms_regs ms) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) by (rewrite Usp; lia).
  assert (Hgp' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Rgp; exact Hgp0).
  assert (Htp' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Rtp; exact Htp0).
  eapply SRr_bind.
  { exact (afree_call B MT LAWS AFREE W3 (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx)) [sink_token]
      (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 _ k buf (p_bn cx)
      (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + PP_K11)) (pch cx) HJ Hbin Q10 Hspo (b_o_mod16 cx HB)
      ltac:(lia) ltac:(unfold ASTACK, LLVMF_STK; lia) Hgp' Htp' Q1
      (ret_ok_codeptr_v PP_K11 ltac:(unfold PP_K11; lia) eq_refl) Hnev' Hch Htr
      (fun Hc => False_ind _ (Hbout0 Hc)) Hmok'). }
  cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfr2 & HK &
    Hmle & Hfd2 & Hfs2).
  assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
  rewrite Hm in HK.
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK by lia.
  destruct (r56_free_keep cx fp PP_K10 PP_K11 k ly3 S3 W3 ms3
    (mkst regs2 (Z_to_bv 64 (BASE + PP_K11)) mem2 (seg_rom SEGS))
    md3 W2 PSH_ts [(b, p_nF cx); (buf, p_bn cx)] buf (p_bn cx) _ (c_sp1 cx) HB HJ0 Hfr Hperm Hbin Hbout0 HK
    ltac:(lia) Hbody eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
    (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2) (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)
    (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9) (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)
    (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4) Hslots Hsn) as (T1 & T2 & T3).
  apply (NEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2
    (mkst regs2 (Z_to_bv 64 (BASE + PP_K11)) mem2 (seg_rom SEGS))
    md2 HB HJ2 ltac:(rewrite Hfr2; exact Hfr) (mle_station MT _ _ _ _ _ MTL Hmo Hmle)).
  exists b.
  split; [|split; [exact Hn26 | split; [|split; [exact T2 | exact T3]]]].
  + split; [exact T1|]. split; [lia|]. split; [unfold PA_K11; lia|].
    split; [rewrite El2; rewrite El1 in Hperm'; rewrite <- (app_nil_r (_ ++ [(b, p_nF cx)]));
            exact (Permutation_app_inv _ _ _ [] _ Hperm')|].
    split; [rewrite Hfd2, (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds
           | rewrite Hfs2, (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs].
  + cbn [ms_regs mkst]. rewrite <- R18. exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18).
Qed.


(* ---- R6: PP_K11 0x80e98 `mv a0,s2`, 0x80e9c `jal __wrap_free` (the copy b) -> PP_K12 0x80ea0 ---- *)
Lemma pe_from_K11 : pt_K11 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HG.
destruct HG as (b & HC & Hn26 & R18 & Hslots & Hsn).
pose proof HC as (Hbody & Hk & Hacc & Hperm & Hfds & Hfs).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
unfold LLVMF_STK in Hspc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (Rsp & Rs0 & Rs1 & Rgp & Rtp) & Hsav & _).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _ & _ & _ & _ & _ & _ & Hev & _ & _ & _ & _ & _ & _ & _ & _ &
  Hmok & Hneed & _ & _ & _ & Hftr).
assert (Hbin : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
pose proof (block_fresh B LAWS ly3 S3 W3 (ms_mem ms3) md3 _ b (p_nF cx) HAR Hperm) as Hbout.
pose proof HJ as HJ0.
pose proof HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & Hnev & Hk0 & _).
pose proof (ms_mkst_at ms3 (BASE + PP_K11) Hpc Hrv Hsv Hrom Hfreg Hfcsr) as Ems.
set (regs := ms_regs ms3) in *. set (mem := ms_mem ms3) in *.
set (E := Eimg (Ereg regs [])).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr regs r)
  by (intros i r Hi Hr; subst E; rewrite Eimg_low by exact Hi; exact (ew_Ereg_nat regs _ i r Hr)).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (HS : st_ok_pi SEGS pa_val E (mkSS PP_K11 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_K11)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; exact I | split; [exact I | split; exact I]]. }
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) mem)) by apply Forall_nil.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
rewrite Ems.
paj_run_tok RUN HS HJ SHOK Espan; [apply awr_ok_x_of0; apply awr_ok_nil |].

assert (Hm : ms_mem ms = mem) by exact (no_write_run_mem _ _ _ _ HF ltac:(intros r Hr; destruct Hr)).
pmkst HS. rewrite (pal_free B TL).
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q10.
pose proof (@pa_base_lo _ _ PL_pcap PI) as HBLO.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
assert (Ura : raZ (ms_regs ms) = BASE + PP_K12) by (unfold raZ; rewrite Q1; apply unsigned_lit_small; unfold PP_K12; lia).
assert (Hch : chain_pre ly3 (aview SEGS (w_H W3) (ms_mem ms)) (ms_regs ms) (pch cx)).
{ rewrite Hm.
  assert (Hs16 : rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (proj2 Hsav 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
  apply (achain_chain_pre ly3 _ (c_sp1 cx) (spZ (c_regs cx)) (pch cx) (ms_regs ms)
           (b_pch_achain cx _ memS ly3 S3 W3 mem md3 k HB HJi Hag (proj1 Hsav) Hs16)).
  - rewrite Usp. lia.
  - unfold s0Z. rewrite Q8, Rs0. apply unsigned_lit_small. lia.
  - rewrite Ura. unfold PP_K12. lia. }
assert (Htr : In (call_trace0 (pc_free_ra0 (as_code B)) (ms_regs ms) (pch cx)) (as_universe B)).
{ apply Hftr. rewrite Ura. replace (BASE + PP_K12 - BASE) with PP_K12 by lia.
  unfold PE_FREE_SITES, PP_K12. cbn [In]. right; right; left; reflexivity. }
assert (Hmok' : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_free MT) MTL Hmok Hmo (mo_free_nonneg MT MTL)).
  pose proof (PA_K12_need MT MTL cx) as Hn. unfold PA_K12 in Hn. lia. }
assert (Hnev' : st_nev S3 < EV_MAX) by (change EV_LIB with 10 in Hev; lia).
assert (Hspo : spZ (ms_regs ms) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) by (rewrite Usp; lia).
assert (Hgp' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite Q3, Rgp; exact Hgp0).
assert (Htp' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite Q4, Rtp; exact Htp0).
eapply SRr_bind.
{ exact (afree_call B MT LAWS AFREE W3 (ms_regs ms) (ms_mem ms) LLVMF_STK (spZ (c_regs cx)) [sink_token]
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 _ k b (p_nF cx)
    (c_sp1 cx - spZ (c_regs cx)) (Z_to_bv 64 (BASE + PP_K12)) (pch cx) HJ Hbin Q10 Hspo (b_o_mod16 cx HB)
    ltac:(lia) ltac:(unfold ASTACK, LLVMF_STK; lia) Hgp' Htp' Q1
    (ret_ok_codeptr_v PP_K12 ltac:(unfold PP_K12; lia) eq_refl) Hnev' Hch Htr
    (fun Hc => False_ind _ (Hbout Hc)) Hmok'). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (l1 & l2 & El1 & El2) & Hfr2 & HK &
  Hmle & Hfd2 & Hfs2).
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
rewrite Hm in HK.
replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HK by lia.
destruct (r56_free_keep cx fp PP_K11 PP_K12 k ly3 S3 W3 ms3 (mkst regs2 (Z_to_bv 64 (BASE + PP_K12)) mem2 (seg_rom SEGS))
  md3 W2 PSH_ts [(b, p_nF cx)] b (p_nF cx) _ (c_sp1 cx) HB HJ0 Hfr Hperm Hbin Hbout HK ltac:(lia) Hbody
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
  (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2) (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)
  (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9) (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)
  (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4) Hslots Hsn) as (T1 & T2 & T3).
apply (NEXT cx fp (k + 1) (acc + mo_free MT) ly2 S2 W2 (mkst regs2 (Z_to_bv 64 (BASE + PP_K12)) mem2 (seg_rom SEGS))
  md2 HB HJ2 ltac:(rewrite Hfr2; exact Hfr) (mle_station MT _ _ _ _ _ MTL Hmo Hmle)).
split; [|split; [exact Hn26 | split; [exact T2 | exact T3]]].
split; [exact T1|]. split; [lia|]. split; [unfold PA_K12; lia|].
split; [rewrite El2; rewrite El1 in Hperm; exact (Permutation_app_inv _ _ _ [] _ Hperm)|].
split; [rewrite Hfd2, (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds
       | rewrite Hfs2, (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs].
Qed.



(* ---- the compositions the other lanes take ---- *)
(* PP_leave reaches pe_post (phase L1's early return). *)
Lemma pe_from_leave_post : pt_leave_post B MT KS.
Proof. exact (pe_from_leave _ pe_from_ret_post). Qed.

(* PP_K12r reaches pe_post (phase L2's refused open). *)
Lemma pe_from_K12r_post : pt_K12r_post B MT KS.
Proof. exact (pe_from_K12r _ pe_from_leave_post). Qed.


(* The cuts around pcap_source_next (R2 at 0x80e64, R4 at 0x80e84): its contract for any stack window NSTK inside
   PcapEntryDefs' bound 32368 (a Theorem Labs lane's cut C states it the same way). *)
Section pn.
Variable NSTK : Z.
Hypothesis HNSTK : 0 <= NSTK <= 32368.
Hypothesis HNEXT : AN.tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NSTK B MT KS (BASE + AF_pcap_source_next).

(* ==== R2: PP_K7 0x80e50 -> PP_K8 0x80e68 ====================================
   0x80e50 bnez a0,0x81034 (PP_abort): refuted at the branch, a0 = 0 (GI_K7); 0x80e54 mv a0,s4 (ps); 0x80e58
   ld a1,0x60(s1) (buf, PS_BUF); 0x80e5c ld a2,0x78(s1) (cap, PS_CAP); 0x80e60 mv a3,zero (ts = NULL); 0x80e64
   jal pcap_source_next (PcapEntryCalls.next_call, the Section hypotheses NSTK / HNSTK / HNEXT), from position 24
   (GI_K7's stream): GI_K8 at the return 0x80e68, a0 = p_first cx and the stream at p_pos cx (p_q cx 24). *)


(* ---- R2 itself ---- *)


(* The symbolic start at PP_K7: one read-only region, the two spill slots the stretch loads (0x80e58 PS_BUF,
   0x80e5c PS_CAP), their words the extra atoms 32 = buf and 33 = cap. No shadow cell is read or written. *)
Definition r2_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_BUF (PS_CAP + 8) 0 0
     [YP09.mkChunk PS_BUF (CVal 8 (SOff 32 0)); YP09.mkChunk PS_CAP (CVal 8 (SOff 33 0))]].

Definition r2_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].

Definition ss_r2 : sstate := mkSS PP_K7 sr_atoms r2_regions None r2_facts.

Definition r2_extra (cx : ecx) (buf : Z) : list word := map (Z_to_bv 64) [buf; p_cap cx].


Lemma pe_from_K7 : pt_K7 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (bb & bf & hh & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hgood & R10 & R18 & R20 & R21 &
  Hslots & QBUF & Hps & Hsrc).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hshlen & Hinp).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinpb & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (b_tail_geo cx HB) as (Hal & Hs1m & Hs1b & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
unfold LLVMF_STK in Hslo, Hbot, Hspc. change (2 ^ 47) with 140737488355328 in H47, Hsp47.
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof pa_base_lo as HBLO.
pose proof (p_sizes cx) as (Hsz1 & Hsz2 & Hsz3).
assert (H24 : 24 <= p_nF cx).
{ pose proof Hgood as Hg. unfold p_good, PST.pcap_good in Hg. apply andb_true_iff in Hg as [Hg _].
  apply Z.leb_le in Hg. exact Hg. }
unfold PE_FRAME in Hf1.
(* the frame *)
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (_ & _ & Hfapp).
rewrite Efa in Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfapp.
destruct (al_frames _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (_ & _ & HFpres & _).
rewrite Efa in HFpres. change (fs_frame_bytes PE_CID) with 128 in HFpres.
assert (HFlo : pF cx fp + 128 <= 2147446784 \/ 17594333495296 <= pF cx fp).
{ destruct Hfapp as (_ & [HL | (HH & _)]); [left; unfold kLowShadowBeg in HL; lia | right; unfold kHighMemBeg in HH; lia]. }
assert (Hf8 : pF cx fp mod 8 = 0).
{ apply Z.mod_divide in Hf64; [|lia]. destruct Hf64 as [q Hq]. apply Z.mod_divide; [lia|]. exists (8 * q). lia. }
assert (Hps8 : pPS cx fp mod 8 = 0) by (unfold pPS, PO_PS; exact (mod64_mod8 _ Hf64)).
assert (HSH : pSH cx fp = 2147450880 + pF cx fp / 8) by reflexivity.
(* the three blocks of the cut: b (the copy), buf, h *)
assert (Hbin : In (bb, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hfbin : In (bf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
assert (Hhin : In (hh, SRC_FILE_BLOCK) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; right; left; reflexivity).
assert (Hfbout : ~ In (bf, p_bn cx) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (b_notin_prefix _ _ _ _ (b_ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; left; reflexivity).
assert (Hhout : ~ In (hh, SRC_FILE_BLOCK) (ablocks B (c_ly cx) (c_S cx)))
  by (refine (b_notin_prefix _ _ _ _ (b_ablocks_nodup _ _ _ _ _ HAR) Hperm _); right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 bb (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 hh SRC_FILE_BLOCK HAR Hhin) as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 bf (p_bn cx) HAR Hfbin) as (_ & Hu4096 & Hubceil & _ & Hupres & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
assert (ERS : req_size (p_bn cx) = p_bn cx)
  by (unfold req_size; destruct (Z.eqb_spec (p_bn cx) 0) as [E0|_]; [lia | reflexivity]).
rewrite ERS in Hubceil, Hupres.
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrqb1 Hrqb2].
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ hh SRC_FILE_BLOCK PE_CID fp HAR Hhin Hfin) as Dhf.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bb (p_nF cx) PE_CID fp HAR Hbin Hfin) as Dbf.
pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ bf (p_bn cx) PE_CID fp HAR Hfbin Hfin) as Duf.
unfold zdisjoint in Dhf, Dbf, Duf. cbn [fst snd] in Dhf, Dbf, Duf. rewrite Efa in Dhf, Dbf, Duf.
change (fs_frame_bytes PE_CID) with 128 in Dhf, Dbf, Duf. change (req_size SRC_FILE_BLOCK) with 1304 in Dhf.
rewrite ERS in Duf.
assert (HL3 : List.NoDup [(bb, p_nF cx); (bf, p_bn cx); (hh, SRC_FILE_BLOCK)])
  by exact (List.NoDup_app_remove_l _ _ (Permutation_NoDup Hperm (b_ablocks_nodup _ _ _ _ _ HAR))).
assert (Hne_uh : (bf, p_bn cx) <> (hh, SRC_FILE_BLOCK)).
{ intros Heq. inversion HL3 as [|x l _ HL2]. inversion HL2 as [|y l2 Hy _]. apply Hy. rewrite Heq. left. reflexivity. }
assert (Hne_ub : (bf, p_bn cx) <> (bb, p_nF cx)).
{ intros Heq. inversion HL3 as [|x l Hx _]. apply Hx. rewrite Heq. left. reflexivity. }
assert (Dfh : bf + p_bn cx <= hh \/ hh + 1304 <= bf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hfbin Hhin Hne_uh) as D. unfold zdisjoint in D.
  cbn [fst snd] in D. rewrite ERS in D. change (req_size SRC_FILE_BLOCK) with 1304 in D. exact D. }
assert (Dfb : bf + p_bn cx <= bb \/ bb + req_size (p_nF cx) <= bf).
{ pose proof (sep_blocks SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hfbin Hbin Hne_ub) as D. unfold zdisjoint in D.
  cbn [fst snd] in D. rewrite ERS in D. exact D. }
(* the symbolic state at 0x80e50 *)
remember (Eimg (Ereg (ms_regs ms3) (r2_extra cx bf))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (r2_extra cx bf)) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 bf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1; apply unsigned_lit_small;
      change (2 ^ 64) with 18446744073709551616; lia).
clear EL.
assert (HS : st_ok_pi SEGS pa_val E ss_r2 (restrict (w_H W3) ms3)).
{ rewrite (ms_mkst_at ms3 (BASE + PP_K7) Hpc Hrv Hsv Hrom Hfreg Hfcsr) at 1. rewrite restrict_mkst_fx.
  unfold ss_r2. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold r2_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [unfold PS_BUF; lia|]. split; [unfold PS_CAP; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_BUF 8 (SOff 32 0) bf);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ QBUF).
    + apply (chunk_ok_val SEGS E _ (c_sp1 cx) PS_CAP 8 (SOff 33 0) (p_cap cx));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hslots)))))))).
  - apply pairwise_disjoint_of_extents. unfold r2_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - split; [|split; [exact I | exact I]].
    cbn [r2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9. change (2 ^ 5) with 32. change (2 ^ 46) with 70368744177664.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
clear HEdef.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
pose proof (paj_branch (PI := PI)) as BR.
(* 0x80e50 bnez a0 to PP_abort 0x81034: refuted here, a0 = 0 (GI_K7) *)
psrr_branch_tok RUN BR HS SHOK Espan.
{ exfalso. cbn [branch_taken sv_denot] in Hc.
  rewrite (EW 10%nat 10%bv ltac:(unfold A_TEXT; lia) eq_refl), R10 in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc.
(* 0x80e54 mv a0,s4; ld a1,0x60(s1); ld a2,0x78(s1); mv a3,zero; 0x80e64 jal pcap_source_next *)
paj_run_tok RUN HS HJ SHOK Espan.
{ apply awr_ok_x_of0. cbn [ss_mem add_cond ss_r2 r2_regions].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }

assert (HFm : ms_mem ms = ms_mem ms3).
{ refine (no_write_run_mem E _ _ _ HF _). intros r Hr. vm_compute in Hr. destruct Hr as [<- | []]. cbn. lia. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (18%bv : bv 5) Q18.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl), Rsp in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl), Rgp in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl), Rtp in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs0 in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl), Rs1 in Q9.
rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10, Q20.
rewrite E32 in Q11. rewrite E33 in Q12.
rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in Q21.
pmkst HS. rewrite pa_sigma_pcap_source_next.
rewrite HFm in HJ |- *.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx)
  by (unfold spZ; rewrite Q2; apply unsigned_lit_small; change (2 ^ 64) with 18446744073709551616; lia).

(* ---- pcap_source_next (jal 0x80e64): ps, buf, cap, ts = NULL, from position 24 ---- *)
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS1 & HJi1 & Hag1 & HSTK1).
assert (Ppres : forall a, pF cx fp <= a < pF cx fp + 128 -> YO0d.present (rdW W3 (ms_mem ms3)) a)
  by (intros a Ha; apply k3_present; exact (proj1 (HFpres a Ha))).
assert (Pps : forall j, 12 <= j < 24 -> YO0d.present (rdW W3 (ms_mem ms3)) (pPS cx fp + j))
  by (intros j Hj; apply Ppres; unfold pPS, PO_PS; lia).
destruct (k3_vm4 (rdW W3 (ms_mem ms3)) (pPS cx fp + 12) (Pps 12 ltac:(lia))
  ltac:(replace (pPS cx fp + 12 + 1) with (pPS cx fp + 13) by lia; exact (Pps 13 ltac:(lia)))
  ltac:(replace (pPS cx fp + 12 + 2) with (pPS cx fp + 14) by lia; exact (Pps 14 ltac:(lia)))
  ltac:(replace (pPS cx fp + 12 + 3) with (pPS cx fp + 15) by lia; exact (Pps 15 ltac:(lia))))
  as (lol & Hlol & Vlol).
destruct (k3_vm4 (rdW W3 (ms_mem ms3)) (pPS cx fp + 16) (Pps 16 ltac:(lia))
  ltac:(replace (pPS cx fp + 16 + 1) with (pPS cx fp + 17) by lia; exact (Pps 17 ltac:(lia)))
  ltac:(replace (pPS cx fp + 16 + 2) with (pPS cx fp + 18) by lia; exact (Pps 18 ltac:(lia)))
  ltac:(replace (pPS cx fp + 16 + 3) with (pPS cx fp + 19) by lia; exact (Pps 19 ltac:(lia))))
  as (lvt & Hlvt & Vlvt).
destruct (val_mem2 SEGS (rdW W3 (ms_mem ms3)) (pPS cx fp + 20) (Pps 20 ltac:(lia))
  ltac:(replace (pPS cx fp + 20 + 1) with (pPS cx fp + 21) by lia; exact (Pps 21 ltac:(lia))))
  as (lvid & Hlvid & Vlvid).
destruct (garr8_of_present SEGS (rdW W3 (ms_mem ms3)) (pPS cx fp + 22) 2
  ltac:(intros a Ha; apply Ppres; unfold pPS, PO_PS in *; cbn [Z.of_nat] in Ha; lia)) as (pad & Hpadl & Hpad).
destruct (garr8_of_present SEGS (rdW W3 (ms_mem ms3)) bf (Z.to_nat (p_bn cx))
  ltac:(intros a Ha; rewrite Z2Nat.id in Ha by lia; apply k3_present; exact (proj1 (Hupres a Ha))))
  as (bj & Hbjl & Hbj).
assert (EBN : AN.nx_bufn (p_cap cx) = p_bn cx) by reflexivity.
assert (Hsh4 : forall i, (4 <= i <= 6)%nat -> aview SEGS (w_H W3) (ms_mem ms3) (pSH cx fp + Z.of_nat i) = Some 0).
{ intros i Hi. rewrite (Hsh i ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
  assert (Hc : (i = 4 \/ i = 5 \/ i = 6)%nat) by lia. destruct Hc as [-> | [-> | ->]]; reflexivity. }
eapply SRr_bind.
{ eapply (next_call SK B MT KS NSTK HNEXT LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx)
    (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) _ k (ms_regs ms)
    (pPS cx fp) bf (p_cap cx) 0 hh bb 24 (p_swz cx) lol lvt lvid 0 (c_M cx) PE_CID fp
    (p_C cx) bj pad (pch cx) HJ).
  - exact (b_aro_now cx memS1 _ ly3 S3 W3 (ms_mem ms3) _ k HB HJi1 Hag1).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small; [lia | change (2 ^ 64) with 18446744073709551616; lia].
  - rewrite Q3. exact Hgp0.
  - rewrite Q4. exact Htp0.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact Q13.
  - rewrite Usp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hs1m; [|lia]. destruct Hs1m as [q Hq].
    exists (2 * q). lia.
  - rewrite Usp. unfold LLVMF_STK. lia.
  - rewrite Usp. lia.
  - rewrite Usp. unfold s0Z at 1. rewrite Q8. unfold w64.
    rewrite unsigned_lit_small by (change (2 ^ 64) with 18446744073709551616; lia).
    destruct Hsaved as (S8 & Sj).
    pose proof (Sj 0 ltac:(lia)) as S16. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in S16 by lia.
    exact (b_pch_achain cx _ memS1 ly3 S3 W3 (ms_mem ms3) _ k HB HJi1 Hag1 S8 S16).
  - rewrite Hfrs. vm_compute. reflexivity.
  - unfold AN.PS_F_OFF. rewrite Z.add_0_r. exact (proj1 Hps).
  - change (2 ^ 64) with 18446744073709551616. lia.
  - exact Hps8.
  - unfold pPS, PO_PS. lia.
  - unfold AN.PS_LEN, pPS, PO_PS. change (2 ^ 47) with 140737488355328. lia.
  - unfold amem_range, AN.PS_LEN, pPS, PO_PS. destruct HFlo; [left | right]; lia.
  - left. reflexivity.
  - rewrite Efa. unfold pPS, PO_PS. lia.
  - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold AN.PS_LEN, pPS, PO_PS. lia.
  - apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. unfold AN.PS_LEN in Hi. change (24 / 8) with 3 in Hi.
    unfold pPS, PO_PS. rewrite shadow_of_addr_aligned_off by exact Hf8. change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]];
    [ replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia)
    | replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia)
    | replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia) ];
    apply Hsh4; lia.
  - intros _. unfold AN.nx_ps_at, AN.PS_F_OFF, AN.PS_SW_OFF, AN.PS_OL_OFF, AN.PS_VT_OFF, AN.PS_VID_OFF.
    rewrite Z.add_0_r. split; [exact (proj1 Hps)|]. split; [exact (proj2 Hps)|]. split; [exact Vlol|].
    split; [exact Vlvt|]. split; [exact Vlvid|]. split; [exact Hpad | exact Hpadl].
  - intros _. exact (p_swz_01 cx).
  - intros _. change (2 ^ 32) with 4294967296 in *. change (2 ^ 16) with 65536 in *. lia.
  - intros _ a Ha. unfold AN.PS_LEN, pPS, PO_PS in Ha. split.
    + right; right; right. exists PE_CID, fp. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes PE_CID) with 128. lia.
    + rewrite Usp. lia.
  - intros _. rewrite EBN. split; [exact Hfbin|]. split; [lia|].
    split; [change (2 ^ 63) with 9223372036854775808; lia|]. split; [exact Hbj|].
    split; [rewrite Hbjl, Z2Nat.id by lia; reflexivity|]. split; [unfold AN.NX_CAP_MAX; lia|].
    split; [|unfold AN.PS_LEN, pPS, PO_PS; lia].
    intros a Ha. split.
    + right; right; left. exists bf, (p_bn cx). split; [exact Hfbin|]. split; [exact Hfbout | rewrite ERS; lia].
    + rewrite Usp. lia.
  - intros _ Hts. exfalso. apply Hts. reflexivity.
  - intros _. rewrite p_lens. split; [exact Hhin|]. split; [exact Hbin|]. split; [exact Hsrc|].
    split; [lia|]. split; [lia|]. rewrite EBN. change SRC_FILE_BLOCK with 1304.
    split; [lia|]. split; [lia|]. split; [unfold AN.PS_LEN, pPS, PO_PS; lia|].
    split; [unfold AN.PS_LEN, pPS, PO_PS; lia|]. split; [intros Hts; exfalso; apply Hts; reflexivity|].
    intros x Hx. unfold asource_fp in Hx. apply inFP_cons in Hx as [Hx|Hx]; [|left; exact Hx].
    right. exists hh, SRC_FILE_BLOCK. split; [exact Hhin|]. split; [exact Hhout|].
    change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Hx. lia.
  - intros _. exact (b_meta_now cx memS1 _ ly3 S3 W3 (ms_mem ms3) _ k HB HJi1 Hag1). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl2 & Hfr2 & Hmle & Hfd2 & Hfs2 & Hfin2).
destruct Hfin2 as [(Hh00 & _) | (_ & Ha0 & HK & Hsrc2 & Hps2 & Hbj2 & Hts2)]; [lia|].

(* ---- at PP_K8 0x80e68: the bytes the body states, kept by the callee (nx_kept misses them) ---- *)
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
assert (Hfoot : forall a, b_hfoot cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ refine (b_foot_kept cx fp ly3 S3 W3 (ms_mem ms3) W2 mem2 _ _ (AN.nx_wrset (pPS cx fp) bf (p_cap cx) 0 hh) HB K1 K2 K4
    _ Hfin Efa (b_input_block cx ly3 S3 _ HB Hperm) _); [rewrite Usp; lia|].
  intros x Hx Hw. unfold AN.nx_wrset in Hw. rewrite EBN in Hw.
  destruct Hw as [Hw | [Hw | [[Hw _] | [_ Hw]]]].
  - exact (b_frame_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ (pPS cx fp) AN.PS_LEN HB HAR Hperm Hfin Efa
      ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS, AN.PS_LEN; lia) x Hx Hw).
  - exact (b_block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ bf (p_bn cx) HB HAR Hperm Hfbin Hfbout Hfin Efa x Hx
      ltac:(rewrite ERS; lia)).
  - exact (Hw eq_refl).
  - exact (b_block_off_hfoot cx fp ly3 S3 W3 (ms_mem ms3) md3 _ hh SRC_FILE_BLOCK HB HAR Hperm Hhin Hhout Hfin Efa x Hx
      ltac:(change (req_size SRC_FILE_BLOCK) with 1304; unfold SRC_FILE_BLOCK in Hw; lia)). }
destruct (b_tail_kept cx fp W3 ms3 W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) PSH_ts Hfoot
  Hsaved Hhdr Hsh Hshlen Hinp Hslots) as (T1 & T2 & T3 & T4 & T5).
assert (QBUF2 : pslot cx W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) PS_BUF bf).
{ unfold pslot. cbn [ms_mem mkst].
  rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W2) mem2)); [exact QBUF|].
  intros i Hi. apply Hfoot. unfold b_hfoot, PS_BUF. right; left. lia. }
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
apply (NEXT cx fp (k + AN.EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2
  HB HJ2).
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle).
- exists bb, bf, hh.
  split; [|split; [exact Hn26 | split; [exact Hgood | split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  + split; [|split; [unfold AN.EV_NEXT; lia | split; [lia | split; [|split]]]].
    * unfold pe_body. cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst ms_regs].
      split; [rewrite Q1; reflexivity|]. do 5 (split; [reflexivity|]).
      split; [|split; [exact T1 | split; [exact T2 | split; [exact T3 | split; [exact Hshlen | exact T4]]]]].
      unfold pregs. cbn [ms_regs mkst].
      split; [exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2)|].
      split; [exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)|].
      split; [exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9)|].
      split; [exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)|].
      exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4).
    * rewrite Hbl2. exact Hperm.
    * rewrite Hfd2, (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)). exact Hfds.
    * rewrite Hfs2, (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)). exact Hfs.
  + cbn [ms_regs mkst]. rewrite Ha0. unfold AN.nx_res, AN.nx_q. rewrite k3_nxF. reflexivity.
  + cbn [ms_regs mkst]. exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18).
  + cbn [ms_regs mkst]. exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Q20).
  + cbn [ms_regs mkst]. exact (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) Q21).
  + exact T5.
  + exact QBUF2.
  + destruct Hps2 as (Hf2 & Hsw2 & _). unfold AN.PS_F_OFF, AN.PS_SW_OFF in Hf2, Hsw2. rewrite Z.add_0_r in Hf2.
    unfold p_psopen, pval. cbn [ms_mem mkst]. split; [exact Hf2 | exact Hsw2].
  + cbn [ms_mem mkst]. unfold AN.nx_pos, AN.nx_q in Hsrc2. rewrite k3_nxF in Hsrc2. exact Hsrc2.
Qed.


(* ==== R4: PP_K9 0x80e74 -> pcap_source_next of the closed reader (0x80e84) -> PP_K10 0x80e88 ====
   0x80e74 mv a0,s4 (ps = F + 32); 0x80e78 ld a1,0x60(s1) (buf, PS_BUF); 0x80e7c ld a2,0x78(s1) (cap, PS_CAP);
   0x80e80 mv a3,zero (ts = NULL); 0x80e84 jal pcap_source_next. ps.f = 0 (p_psnull), so the contract's closed-reader
   arm (h = 0): a0 = -1 and nothing of the caller's is written (nx_kept at E = False). The stretch has no branch,
   so no edge into PP_abort (0x81034), 0x8103c or 0x81040 lies in it. (lib/A PcapHarnessTail.tail_R4, ported.) *)


(* The symbolic state at PP_K9: atom 32 = buf (PS_BUF's word, ld a1,0x60(s1) 0x80e78), atom 33 = cap (PS_CAP's word,
   ld a2,0x78(s1) 0x80e7c). One region, the two slots, read only. *)
Definition r4_regions : smem :=
  [YP09.mkRegion (Some 9%nat) PS_BUF (PS_CAP + 8) 0 0
     [YP09.mkChunk PS_BUF (CVal 8 (SOff 32 0)); YP09.mkChunk PS_CAP (CVal 8 (SOff 33 0))]].

Definition r4_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].

Definition ss_r4 : sstate := mkSS PP_K9 sr_atoms r4_regions None r4_facts.

Definition r4_extra (buf cap : Z) : list word := map (Z_to_bv 64) [buf; cap].


Lemma r4_entry : forall cx fp k ly3 S3 W3 (ms3 : machine_state) md3 buf,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(PE_CID, fp)] ->
  pe_body cx fp PP_K9 W3 ms3 PSH_ts ->
  pslot cx W3 ms3 PS_BUF buf -> 0 <= buf < 2 ^ 64 ->
  pslot cx W3 ms3 PS_CAP (p_cap cx) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx)))) ss_r4 (restrict (w_H W3) ms3) /\
  sh_ok SEGS EBx [] (Eimg (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx)))) (mrestrict (w_H W3) (ms_mem ms3)).
Proof.
intros cx fp k ly3 S3 W3 ms3 md3 buf HB HJ Hfrs HBody SBUF Hbuf SCAP.
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs)
  as (_ & _ & Hsp16 & Hspc & Hsp47 & Hsp1 & _ & Hf0 & Hf1 & Hf64 & _ & _ & Hs1lo & Hal32).
unfold LLVMF_STK in Hspc.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (p_sizes cx) as (_ & Hcap & _).
pose proof HBody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & (Rsp & Rs0 & Rs1 & Rgp & Rtp) & _).
set (E := Eimg (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx)))).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx))) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (E9 : ew E 9 = w64 (c_sp1 cx))
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms3) _ 9 9%bv eq_refl); exact Rs1).
assert (E32 : ew E 32 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; unfold LLVMF_STK in *; lia).
split; [|apply Forall_nil].
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K9)) (ms_mem ms3) (seg_rom SEGS)).
{ destruct ms3; cbn in Hpc, Hrv, Hsv, Hrom, Hfreg, Hfcsr |- *; subst; reflexivity. }
rewrite Hms at 1. rewrite restrict_mkst_fx. unfold ss_r4. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold r4_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
  rewrite U9. unfold PS_BUF, PS_CAP in *. split; [lia|]. split; [unfold LLVMF_STK in *; lia|].
  split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 96 8 (SOff 32 0) buf);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SBUF).
  + apply (chunk_ok_val SEGS E _ (c_sp1 cx) 120 8 (SOff 33 0) (p_cap cx));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | zside |].
    exact (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3) _ _ SCAP).
- apply pairwise_disjoint_of_extents. unfold r4_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [r4_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  fold E. rewrite U9. change (2 ^ 5) with 32. unfold LLVMF_STK in *.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.


Lemma pe_from_K9 : pt_K9 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr Hmo HI.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfr)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinp & Hs1lo & Hal32).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hspc' : alloc_ceiling + 32768 <= spZ (c_regs cx)) by exact Hspc.
assert (Hf1' : pF cx fp + 128 <= alloc_ceiling) by exact Hf1.
destruct HI as (b & buf & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & R18 & R20 & Hslots & SBUF & Hcopy &
  Hnull & Hsn).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsav & Hhd & Hsh & Hshlen & Hinb).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
pose proof Hslots as (SF0 & SD & SSHB & SSH & SF & SFK & STSP & SCAP).
pose proof HB as ((_ & _ & _ & Hgp0 & Htp0 & _) & _).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfr; left; reflexivity).
assert (Efa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (_ & _ & Hfapp).
rewrite Efa in Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfapp.
assert (Hbuf3 : In (buf, p_bn cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly3 S3 W3 (ms_mem ms3) md3 buf (p_bn cx) HAR Hbuf3) as (_ & Hbuf4096 & Hbufceil & _).
pose proof (p_sizes cx) as (_ & Hcap & Hbn).
pose proof (req_size_pos (p_bn cx) ltac:(lia)) as [_ Hrqb].
assert (HSHv : SHADOW_OFF <= pSH cx fp /\ pSH cx fp + 16 <= alloc_ceiling).
{ unfold pSH, shadow_of_addr, SHADOW_OFF. Z.div_mod_to_equations. lia. }
assert (Hf8 : pF cx fp mod 8 = 0).
{ apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hf64; [|lia]. destruct Hf64 as [q Hq]. exists (8 * q). lia. }
assert (Hps8 : pPS cx fp mod 8 = 0) by (unfold pPS, PO_PS; exact (mod64_mod8 _ Hf64)).
destruct (r4_entry cx fp k ly3 S3 W3 ms3 md3 buf HB HJ Hfr Hbody SBUF ltac:(lia) SCAP) as [HS SHOK].
remember (Eimg (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx)))) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) (r4_extra buf (p_cap cx))) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (E32 : ew E 32 = Z_to_bv 64 buf) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (p_cap cx)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
clear HEdef.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
(* 0x80e74 .. 0x80e80, the call 0x80e84: the run stops at pcap_source_next's entry *)
paj_run_tok RUN HS HJ SHOK Espan;
  [ apply awr_ok_x_of0; cbn [ss_mem ss_r4 r4_regions];
    apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil] |].
assert (HFm : ms_mem ms = ms_mem ms3).
{ apply (no_write_run_mem _ _ _ _ HF). intros r Hr. cbn [ss_mem ss_r4 r4_regions In] in Hr.
  destruct Hr as [<- | []]. cbn. lia. }
clear HF HFr HG.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10.
rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
rewrite E32 in Q11. rewrite E33 in Q12.
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
assert (Us0 : s0Z (ms_regs ms) = spZ (c_regs cx))
  by (unfold s0Z; rewrite Q8, Rs0; apply unsigned_lit_small; change (2 ^ 47) with 140737488355328 in Hsp47; lia).
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & HSTK).
pmkst HS. rewrite pa_sigma_pcap_source_next.
eapply SRr_bind.
{ eapply (next_call SK B MT KS NSTK HNEXT LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx)
    (c_mem cx) (c_md cx) [(PE_CID, fp)] ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms)
    (pPS cx fp) buf (p_cap cx) 0 0 0 0 0 0 0 0 0 (c_M cx) PE_CID fp [] [] [] (pch cx) HJ).
  - exact (b_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, Rgp. exact Hgp0.
  - rewrite Q4, Rtp. exact Htp0.
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - exact Q13.
  - rewrite Usp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hal32; [|lia].
    destruct Hal32 as [q Hq]. exists (2 * q). lia.
  - rewrite Usp. unfold LLVMF_STK. lia.
  - rewrite Usp. lia.
  - rewrite Usp, Us0. rewrite HFm in HJi |- *.
    apply (b_pch_achain cx _ memS ly3 S3 W3 (ms_mem ms3) _ k HB HJi Hag); [exact (proj1 Hsav)|].
    pose proof (proj2 Hsav 0 ltac:(lia)) as H0.
    replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0.
  - rewrite Hfr. vm_compute. reflexivity.
  - unfold AN.PS_F_OFF. rewrite Z.add_0_r, HFm. exact Hnull.
  - lia.
  - exact Hps8.
  - unfold pPS, PO_PS. lia.
  - unfold AN.PS_LEN, pPS, PO_PS. change (2 ^ 47) with 140737488355328. lia.
  - unfold amem_range, AN.PS_LEN, pPS, PO_PS. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. lia.
  - left. reflexivity.
  - rewrite Efa. unfold pPS, PO_PS. lia.
  - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold AN.PS_LEN, pPS, PO_PS. lia.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. unfold AN.PS_LEN in Hi. change (24 / 8) with 3 in Hi.
    unfold pPS, PO_PS. rewrite shadow_of_addr_aligned_off by exact Hf8.
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hshlen; unfold PE_NSH; lia)).
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity.
  - intros H0. exfalso. apply H0. reflexivity. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl2 & Hfr2 & Hmle & Hfd2 & Hfs2 & Hfin2).
destruct Hfin2 as [(_ & Ha0 & HK) | (Hh & _)]; [| exfalso; apply Hh; reflexivity].
destruct HK as (K1 & K2 & K3 & K4 & _ & _).
rewrite Usp in K1.
assert (P : forall r : Z, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r))
  by exact HP2.
(* What the call keeps of the harness's bytes: every byte outside the callee's window [s1 - NSTK, s1) that lies above
   the allocator's ceiling, in the frame, in its shadow or in the input block (nx_kept, clauses 1, 4 and 2). *)
set (R := fun a => (c_sp1 cx - NSTK <= a < c_sp1 cx) \/
  (a < alloc_ceiling /\ ~ (pF cx fp <= a < pF cx fp + 128) /\ ~ (pSH cx fp <= a < pSH cx fp + 16) /\
   ~ (c_p cx <= a < c_p cx + c_n cx))).
assert (HMK : mkw W3 W2 (ms_mem ms3) mem2 R).
{ intros a Ha HnR. rewrite <- HFm.
  destruct (Z_lt_le_dec a alloc_ceiling) as [Hlt | Hge].
  2: { apply K1; [lia | intros Hw; apply HnR; left; exact Hw | intros []]. }
  assert (Hc : (pF cx fp <= a < pF cx fp + 128) \/ (pSH cx fp <= a < pSH cx fp + 16) \/
               (c_p cx <= a < c_p cx + c_n cx)) by (unfold R in HnR; lia).
  destruct Hc as [Hc | [Hc | Hc]].
  - apply (K4 PE_CID fp a Hfin); [|intros []]. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID) with 128. lia.
  - apply (K4 PE_CID fp a Hfin); [|intros []]. right. unfold in_zr. cbn [fst snd]. rewrite Efa.
    change (fs_frame_bytes PE_CID / 8) with 16. change (shadow_addr (pF cx fp)) with (pSH cx fp). lia.
  - assert (Hn : 0 < c_n cx) by lia.
    assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3)).
    { pose proof HB as (_ & _ & _ & _ & Hinp0 & _). destruct Hinp0 as [[H0 _] | [_ Hin0]]; [lia|].
      apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. exact Hin0. }
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
    replace a with (c_p cx + (a - c_p cx)) by lia.
    apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin); [lia | intros []]. }
assert (Hap : slots_apartw cx R) by (intros a Ha _ [Hw | (Hlt & _)]; lia).
apply (NEXT cx fp (k + AN.EV_NEXT) (acc + 0) ly2 S2 W2 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2
  HB HJ2 ltac:(rewrite Hfr2; exact Hfr) (mle_station MT _ _ _ _ _ MTL Hmo Hmle)).
exists b, buf.
split.
{ split.
  { eapply (pe_body_keepw cx fp PP_K9 PP_K10 W3 W2 ms3 _ PSH_ts R Hbody);
    [ cbn [ms_pc_val mkst]; rewrite Q1; reflexivity
    | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | cbn [ms_regs mkst]; exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2)
    | cbn [ms_regs mkst]; exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)
    | cbn [ms_regs mkst]; exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9)
    | cbn [ms_regs mkst]; exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)
    | cbn [ms_regs mkst]; exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4)
    | exact HMK
    | intros a Ha [Hw | (Hlt & _)]; lia
    | intros a Ha [Hw | (_ & HnF & _)]; [lia | apply HnF; lia]
    | intros a Ha [Hw | (_ & HnF & _)]; unfold PE_FLAGPTR in Ha; [lia | apply HnF; lia]
    | intros a Ha [Hw | (_ & _ & HnS & _)]; [lia | apply HnS; lia]
    | intros a Ha [Hw | (_ & _ & _ & HnI)]; [lia | apply HnI; lia]
    | exact Hspc | exact Hsp47 | exact Hf0 | exact Hf1 | exact Hinp ]. }
  split; [unfold AN.EV_NEXT; lia|]. split; [lia|]. split; [rewrite Hbl2; exact Hperm|].
  split; [rewrite Hfd2, (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfds
         | rewrite Hfs2, (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)); exact Hfs]. }
split; [exact Hn26|].
split; [cbn [ms_regs mkst]; exact Ha0|].
split; [cbn [ms_regs mkst]; exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18)|].
split; [exact (pslots_keepw cx fp W3 W2 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) R Hslots HMK Hap ltac:(lia) ltac:(change (2 ^ 64) with 18446744073709551616; lia))|].
split; [apply (pslot_keepw_apart cx W3 W2 ms3 (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) R PS_BUF buf SBUF HMK Hap);
          [lia | change (2 ^ 64) with 18446744073709551616; lia | repeat (first [left; reflexivity | right])]|].
split.
{ unfold p_psnull, pval in Hnull |- *. cbn [ms_mem mkst].
  apply (val_mem_keepw W3 W2 (ms_mem ms3) mem2 R _ _ _ Hnull HMK);
    [unfold pPS, PO_PS; lia | unfold pPS, PO_PS; cbn [Z.of_nat]; change (2 ^ 64) with 18446744073709551616; lia |].
  intros j Hj [Hw | (_ & HnF & _)]; unfold pPS, PO_PS in *; cbn [Z.of_nat] in Hj; [lia | apply HnF; lia]. }
cbn [ms_mem mkst]. apply (asource_none_frame (mrestrict (w_H W3) (ms_mem ms3))); [|exact Hsn].
intros a Ha. apply (mbyte_of_aview SEGS). rewrite <- HFm.
destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He). exact (K3 a Hi Ho He).
Qed.

End pn.

(* The cut around the second pcap_source_open (R1 at 0x80e4c): its contract and the facts it needs, which are
   lib/A/Prog/PcapHarnessTail.v's Section hypotheses of the open call (HROI, HPATH, HCTX, HFMU), each of the exact type
   of the fact it stands for, at lib/B's numbers (PP_K7 = 0x6c8, the return address 0x80e50 of jal 0x80e4c). *)
Section po.
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis OPENS : AO.tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4))
  (pa_val (A_OBJ 2)) ROI B KS MT FM_RA CTX (BASE + AF_pcap_source_open).
Hypothesis HROI : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (pa_val (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (pa_val (A_OBJ 3)) 13.
Hypothesis HCTX : In [BASE + PP_K7; RA_LLVMF] CTX /\ In [BASE + PP_K7] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).

(* ==== R1: PP_K6 0x80e38 -> PP_K7 0x80e50 (the second pcap_source_open) ==== *)

(* The symbolic state at PP_K6 (0x80e38): one read-only region, ps.f at s4 = PS (GI_K6's p_psnull: the word 0). *)
Definition r1_rs : smem := [YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit 0))]].


(* What a call keeps, as Kit's mkw: every byte that reads the same in both states is outside the set of bytes that
   differ (option Z has decidable equality). *)
Lemma r1_mkw_diff : forall (W3 W4 : world SEGS) (m m' : word -> option byte),
  mkw W3 W4 m m' (fun a => aview SEGS (w_H W4) m' a <> aview SEGS (w_H W3) m a).
Proof.
intros W3 W4 m m' a _ Hn.
destruct (aview SEGS (w_H W4) m' a) as [x|], (aview SEGS (w_H W3) m a) as [y|];
  [destruct (Z.eq_dec x y) as [->|Hne]; [reflexivity|] | | | reflexivity]; exfalso; apply Hn; congruence.
Qed.


Lemma pe_from_K6 : pt_K6 B MT KS.
Proof.
intros POST NEXT cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
destruct HG as (b & buf & (Hbody & Hk & Hacc & Hperm & Hfds & Hfs) & Hn26 & Hgood & R18 & R20 & R21 &
  Hslots & Hsbuf & Hglob & Hcopy & Hnull & Hsrc).
pose proof Hbody as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hsh & Hlen & Hinp).
pose proof Hregs as (Rsp & Rs0 & Rs1 & Rgp & Rtp).
destruct (rec_ctx B MT KS LAWS cx fp k ly3 S3 W3 ms3 md3 HB HJ Hfrs)
  as (HGX & HAR & Hsp16 & Hspc & Hsp47 & Hsp1 & Hpres & Hf0 & Hf1 & Hf64 & HEF & Hinb & Hs1lo & Hal32).
pose proof (b_tail_geo cx HB) as (_ & _ & _ & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HB as ((HAR0 & Hrok & Hra4 & Hgp0 & Htp0 & _) & HraL & _ & _ & _ & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ &
  _ & _ & Hmok & Hneed & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
assert (EFa : frame_addr ly3 PE_CID fp = pF cx fp) by (unfold pF, frame_addr; rewrite HEF; reflexivity).
assert (Hfin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 PE_CID fp HAR Hfin) as (_ & _ & Hfapp).
rewrite EFa in Hfapp. change (fs_frame_bytes PE_CID) with 128 in Hfapp.
assert (Hps : pPS cx fp = pF cx fp + 32) by reflexivity.
assert (Hps8 : pPS cx fp mod 8 = 0) by (rewrite Hps; apply mod64_mod8; exact Hf64).
assert (Hbin : In (b, p_nF cx) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b (p_nF cx) HAR Hbin) as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
pose proof (req_size_pos (p_nF cx) ltac:(lia)) as [Hrqb1 Hrqb2].
assert (EBB : blocks_bytes S3 = blocks_bytes (c_S cx) + p_nF cx + p_bn cx).
{ rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)).
  rewrite (bsum_perm _ _ Hperm), bsum_app. cbn [bsum fold_right snd]. lia. }
unfold PE_FRAME, LLVMF_STK in *.
assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + PP_K6)) (ms_mem ms3) (seg_rom SEGS))
  by exact (ms_mkst_at ms3 (BASE + PP_K6) Hpc Hrv Hsv Hrom Hfreg Hfcsr).
set (E := Eimg (Ereg (ms_regs ms3) [])).
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg (ms_regs ms3) []) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (EW : forall i (r : bv 5), (i < A_TEXT)%nat -> Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r)
  by (intros i r Hi Hr; rewrite EL by exact Hi; exact (ew_Ereg_nat (ms_regs ms3) _ i r Hr)).
assert (EO3 : ew E 244%nat = Z_to_bv 64 (pa_val (A_OBJ 3)))
  by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (U20 : bv_unsigned (ew E 20) = pPS cx fp)
  by (rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS pa_val E (mkSS PP_K6 sr_atoms r1_rs None (mkFacts [] [] [])) (restrict (w_H W3) ms3)).
{ rewrite Hms at 1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold r1_rs. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; fold E.
    rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (pPS cx fp) 0 8 (SLit 0) 0); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. exact Hnull.
  - apply pairwise_disjoint_of_extents. unfold r1_rs, extent_of_region.
    cbn [map zpairwise_disjoint zall_disjoint]. repeat split; exact I.
  - split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS EBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by apply Forall_nil.
clear Hms.
pose proof (bpaj_run_x B LAWS pe_G HGX 0 []) as RUN.
(* 0x80e38 ld a0,0(s4): the region's chunk, the literal 0 (p_psnull); 0x80e3c bnez a0 to PP_abort 0x81034: the engine
   decides it on the literal (not taken), so no run state reaches the abort; 0x80e40 / 0x80e44 a1 := the path literal
   (object 3); 0x80e48 a0 := s4; the run stops at jal pcap_source_open 0x80e4c *)
paj_run_tok RUN HS HJ SHOK Espan;
  [apply awr_ok_x_of0; cbn [ss_mem]; unfold r1_rs; apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
assert (HFm : ms_mem ms = ms_mem ms3).
{ refine (no_write_run_mem E _ _ _ HF _). intros r Hr. cbn [ss_mem] in Hr. unfold r1_rs in Hr.
  destruct Hr as [<- | []]. cbn. lia. }
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (18%bv : bv 5) Q18. prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
rewrite (EW 2%nat 2%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q2.
rewrite (EW 3%nat 3%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q3.
rewrite (EW 4%nat 4%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q4.
rewrite (EW 8%nat 8%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q8.
rewrite (EW 9%nat 9%bv ltac:(unfold A_TEXT; lia) eq_refl) in Q9.
rewrite (EW 20%nat 20%bv ltac:(unfold A_TEXT; lia) eq_refl), R20 in Q10, Q20.
rewrite EO3 in Q11.
rewrite (EW 18%nat 18%bv ltac:(unfold A_TEXT; lia) eq_refl), R18 in Q18.
rewrite (EW 21%nat 21%bv ltac:(unfold A_TEXT; lia) eq_refl), R21 in Q21.
assert (Usp : spZ (ms_regs ms) = c_sp1 cx) by (unfold spZ; rewrite Q2, Rsp; apply unsigned_lit_small; lia).
destruct (gx_open SK B pe_G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (memS & HJi & Hag & _).
pose proof HJi as (_ & Hly & _ & _ & _ & _ & Hnev & _).
assert (Etop : ly_top ly3 = ly_top (c_ly cx))
  by (destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _); exact Etop).
assert (Hs8 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)))
  by (rewrite HFm; exact (proj1 Hsaved)).
assert (Hs16 : rdword (aview SEGS (w_H W3) (ms_mem ms)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
{ rewrite HFm. pose proof (proj2 Hsaved 0 ltac:(lia)) as H0.
  replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia. exact H0. }
pmkst HS. rewrite pa_sigma_pcap_source_open.
eapply SRr_bind.
{ eapply (open_call SK B MT KS (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4)) (pa_val (A_OBJ 2)) ROI FM_RA CTX OPENS
    _ (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(PE_CID, fp)]
    ly3 S3 W3 (ms_mem ms) _ k (ms_regs ms) (pch cx) (pPS cx fp) (p_nF cx) b (c_M cx) (p_C cx) PE_CID fp HJ).
  - exact (b_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia. lia.
  - rewrite Q3, Rgp. exact Hgp0.
  - rewrite Q4, Rtp. exact Htp0.
  - exact Q10.
  - exact Q11.
  - rewrite Usp. unfold s0Z at 1. rewrite Q8, Rs0. unfold w64. rewrite unsigned_lit_small by lia.
    exact (b_pch_achain cx _ memS ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag Hs8 Hs16).
  - unfold raZ. rewrite Q1, unsigned_lit_small by lia.
    unfold pch, spine. destruct (Z.ltb_spec (spZ (c_regs cx) + 16) (ly_top (c_ly cx))) as [Ht|Ht].
    + cbn [map]. rewrite HraL. exact (proj1 HCTX).
    + cbn [map]. exact (proj2 HCTX).
  - rewrite Usp. lia.
  - rewrite Usp, AO.TPCAP_SOURCE_OPEN_STK_val. lia.
  - rewrite Usp. lia.
  - rewrite Usp, Etop. lia.
  - rewrite Hfrs. cbn [length Z.of_nat]. lia.
  - left. reflexivity.
  - rewrite EFa, Hps. lia.
  - rewrite EFa, Hps. change (fs_frame_bytes PE_CID) with 128. lia.
  - rewrite Hps. lia.
  - exact Hps8.
  - rewrite HFm. apply zero_shadow_range; [exact Hps8 | reflexivity |].
    intros i Hi. change (24 / 8) with 3 in Hi.
    rewrite Hps, shadow_of_addr_aligned_off by (apply Z.mod_divide; [lia|]; apply Z.mod_divide in Hf64; [|lia];
      destruct Hf64 as [q Hq]; exists (8 * q); lia).
    change (32 / 8) with 4.
    assert (Hi3 : i = 0 \/ i = 1 \/ i = 2) by lia.
    destruct Hi3 as [-> | [-> | ->]].
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 0) with (pSH cx fp + Z.of_nat 4) by (unfold pSH; lia).
      exact (Hsh 4%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 1) with (pSH cx fp + Z.of_nat 5) by (unfold pSH; lia).
      exact (Hsh 5%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
    + replace (shadow_of_addr SHADOW_OFF (pF cx fp) + 4 + 2) with (pSH cx fp + Z.of_nat 6) by (unfold pSH; lia).
      exact (Hsh 6%nat ltac:(rewrite Hlen; unfold PE_NSH; lia)).
  - exists sink_token. split; [left; reflexivity|]. unfold sink_token. cbn [fst snd]. lia.
  - apply HROI. exact (b_aro_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - rewrite HFm. exact (proj1 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 (HPATH ly3 S3 W3 (ms_mem ms3) md3 HAR)).
  - rewrite HFm. exact (proj2 Hglob).
  - rewrite HFm. exact (proj1 Hglob).
  - lia.
  - rewrite HFm. exact Hsrc.
  - symmetry. exact (p_lens cx).
  - lia.
  - intros _. split; [exact Hbin|]. split; [rewrite HFm; exact Hcopy|].
    exact (garr8_bytes_ok SEGS _ _ _ Hcopy).
  - exact (b_meta_now cx memS _ ly3 S3 W3 (ms_mem ms) _ k HB HJi Hag).
  - change EV_LIB with 10 in Hev. unfold AO.EV_OPEN, AF.EV_FUZZ_FOPEN. lia.
  - rewrite EBB. change LIVE_LIB with (2 ^ 26 + 1304 + 2040) in Hlive. unfold SRC_FILE_BLOCK. lia.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc (mo_malloc MT SRC_FILE_BLOCK) MTL Hmok Hmo
      (mo_malloc_nonneg MT MTL SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia))).
    pose proof (PA_K12_need MT MTL cx) as Hn. pose proof (mo_free_nonneg MT MTL).
    unfold PA_K12, PA_K11, PA_K9, PA_K7 in *. lia.
  - exact (proj1 HFMU).
  - exact (proj2 HFMU). }

cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HP2 & Hfr2 & Hfd2 & Hfs2 & HK & Hmle & V12 & V16 & V20 &
  Harm).
(* the refused arm: AO.pcap_goodZ (p_C cx) = false against GI_K6's p_good cx = true *)
destruct Harm as [(HJ2 & Ha0 & _ & hh & Hh4096 & Hh16 & Hbl2 & Hpf2 & Hpsw2 & Hsrc2 & Hmle2) |
                  (_ & _ & Hbad & _)]; [| rewrite b_goodZ_good, Hgood in Hbad; discriminate Hbad].
destruct HK as (K1 & K2 & K3 & K4 & K5 & K6).
rewrite Usp, HFm in K1. rewrite HFm in K2, K4.
assert (P : forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr (ms_regs ms) (Z_to_bv 5 r)) by exact HP2.
(* the bytes the call kept, against GI_K6's state *)
assert (KH1 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (c_sp1 cx - AO.TPCAP_SOURCE_OPEN_STK <= a < c_sp1 cx) ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a) by exact K1.
assert (KH4 : forall a, (pF cx fp <= a < pF cx fp + 128 \/ pSH cx fp <= a < pSH cx fp + 16) ->
  ~ (pPS cx fp <= a < pPS cx fp + 22) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hne. apply (K4 PE_CID fp a Hfin); [|exact Hne].
  destruct Ha as [Ha|Ha]; [left | right]; unfold in_zr, frame_rng, shadow_addr; cbn [fst snd]; rewrite EFa;
    change (fs_frame_bytes PE_CID) with 128; change (128 / 8) with 16;
    [lia | unfold pSH, shadow_of_addr in Ha; unfold SHADOW_OFF in *; lia]. }
assert (Hshv : forall a, pSH cx fp <= a < pSH cx fp + 16 -> ~ (pPS cx fp <= a < pPS cx fp + 22)).
{ intros a Ha Hp. unfold pSH, shadow_of_addr, SHADOW_OFF in Ha.
  refine (fshadow_not_app (pF cx fp) 16 (pF cx fp) 128 a ltac:(lia)
    ltac:(change (2 ^ 47) with 140737488355328; lia) Hfapp ltac:(lia) ltac:(lia)). }
set (R := fun a => aview SEGS (w_H W2) mem2 a <> aview SEGS (w_H W3) (ms_mem ms3) a).
assert (MK : mkw W3 W2 (ms_mem ms3) (ms_mem (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS))) R)
  by exact (r1_mkw_diff W3 W2 (ms_mem ms3) mem2).
assert (NR : forall a, aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a -> ~ R a)
  by (intros a Ha Hr; exact (Hr Ha)).
assert (Hs1A : alloc_ceiling + 32368 <= c_sp1 cx) by lia.
assert (NS : forall a, c_sp1 cx <= a < 2 ^ 64 -> ~ R a)
  by (intros a Ha; apply NR, KH1; [lia | rewrite AO.TPCAP_SOURCE_OPEN_STK_val; lia]).
apply (NEXT cx fp (k + AF.EV_FUZZ_FOPEN) (acc + mo_malloc MT SRC_FILE_BLOCK) ly2 S2 W2
  (mkst regs2 (getr (ms_regs ms) 1) mem2 (seg_rom SEGS)) md2 HB).
- exact HJ2.
- rewrite Hfr2. exact Hfrs.
- exact (mle_station MT _ _ _ _ _ MTL Hmo Hmle2).
- exists b, buf, hh.
  split; [|split; [exact Hn26 | split; [exact Hgood | split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
  + split; [|split; [unfold AF.EV_FUZZ_FOPEN; lia | split; [unfold PA_K7; lia | split; [|split]]]].
    * eapply (pe_body_keepw cx fp PP_K6 PP_K7 W3 W2 ms3 _ PSH_ts R Hbody); try reflexivity;
        [ cbn [ms_pc_val mkst]; rewrite Q1; reflexivity
        | cbn [ms_regs mkst]; exact (eq_trans (P 2 ltac:(unfold acallee_saved; lia)) Q2)
        | cbn [ms_regs mkst]; exact (eq_trans (P 8 ltac:(unfold acallee_saved; lia)) Q8)
        | cbn [ms_regs mkst]; exact (eq_trans (P 9 ltac:(unfold acallee_saved; lia)) Q9)
        | cbn [ms_regs mkst]; exact (eq_trans (P 3 ltac:(unfold acallee_saved; lia)) Q3)
        | cbn [ms_regs mkst]; exact (eq_trans (P 4 ltac:(unfold acallee_saved; lia)) Q4)
        | exact MK
        | intros a Ha; apply NS; lia
        | intros a Ha; apply NR, KH4; [left; lia | rewrite Hps; lia]
        | intros a Ha; apply NR, KH4; [left; unfold PE_FLAGPTR in Ha; lia | rewrite Hps; unfold PE_FLAGPTR in Ha; lia]
        | intros a Ha; apply NR, KH4; [right; exact Ha | exact (Hshv a Ha)]
        |
        | unfold LLVMF_STK; lia | lia | lia | unfold PE_FRAME; lia | exact Hinb ].
      intros a Ha. apply NR.
      assert (Hn0 : 0 < c_n cx) by lia.
      pose proof HB as (_ & _ & _ & _ & [[Hc0 _] | [_ Hin0]] & _); [lia|].
      assert (Hpin : In (c_p cx, c_n cx) (ablocks B ly3 S3))
        by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hin0).
      pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) PE_CID fp HAR Hpin Hfin) as D.
      unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFa in D. change (fs_frame_bytes PE_CID) with 128 in D.
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [Hq1 Hq2].
      replace a with (c_p cx + (a - c_p cx)) by lia.
      apply (K2 (c_p cx) (c_n cx) (a - c_p cx) Hpin); [lia | rewrite Hps; lia].
    * rewrite Hbl2. eapply Permutation_trans; [apply (Permutation_app_tail [(hh, SRC_FILE_BLOCK)] Hperm)|].
      rewrite <- app_assoc. cbn [app]. apply Permutation_refl.
    * rewrite Hfd2. etransitivity; [apply (proj1 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfds].
    * rewrite Hfs2. etransitivity; [apply (proj2 (PcapSourceCloseSpec.wvb_fds_fs _ _ _)) | exact Hfs].
  + cbn [ms_regs mkst]. exact Ha0.
  + cbn [ms_regs mkst]. exact (eq_trans (P 18 ltac:(unfold acallee_saved; lia)) Q18).
  + cbn [ms_regs mkst]. exact (eq_trans (P 20 ltac:(unfold acallee_saved; lia)) Q20).
  + cbn [ms_regs mkst]. exact (eq_trans (P 21 ltac:(unfold acallee_saved; lia)) Q21).
  + apply (pslots_keepw cx fp W3 W2 ms3 _ R Hslots MK); [|lia | lia].
    intros a Ha _. apply NS. lia.
  + apply (pslot_keepw cx W3 W2 ms3 _ R PS_BUF buf Hsbuf MK); unfold PS_BUF; [lia | lia |].
    intros j Hj. apply NS. lia.
  + unfold p_psopen, pval. cbn [ms_mem mkst]. split; [exact Hpf2|]. rewrite <- b_swZ_sw. exact Hpsw2.
  + cbn [ms_mem mkst]. exact Hsrc2.
Qed.

End po.

(* The whole tail: GI_K6 (the end of the end-of-walk check, phase L5) reaches pe_post. *)
Section pall.
Variable NSTK : Z.
Hypothesis HNSTK : 0 <= NSTK <= 32368.
Hypothesis HNEXT : AN.tpcap_source_next_specX SK SEGS pa_relro_lo pa_relro_hi NSTK B MT KS (BASE + AF_pcap_source_next).
Variable FM_RA : Z.
Variable CTX : list (list Z).
Variable ROI : (word -> option byte) -> Prop.
Hypothesis OPENS : AO.tpcap_source_open_specX SK SEGS pa_relro_lo pa_relro_hi (pa_val (A_OBJ 3)) (pa_val (A_OBJ 4))
  (pa_val (A_OBJ 2)) ROI B KS MT FM_RA CTX (BASE + AF_pcap_source_open).
Hypothesis HROI : forall (W : world SEGS) mem,
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> ROI (mrestrict (w_H W) mem).
Hypothesis HPATH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (pa_val (A_OBJ 3)) 13 /\
  shadow_hull_vis (aview SEGS (w_H W) mem) (pa_val (A_OBJ 3)) 13.
Hypothesis HCTX : In [BASE + PP_K7; RA_LLVMF] CTX /\ In [BASE + PP_K7] CTX.
Hypothesis HFMU : In [pc_malloc_ra0 (as_code B)] (as_universe B) /\
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)).

Lemma pe_from_K6_post : pt_K6_post B MT KS.
Proof.
exact (pe_from_K6 FM_RA CTX ROI OPENS HROI HPATH HCTX HFMU _
  (pe_from_K7 NSTK HNSTK HNEXT _ (pe_from_K8 _ (pe_from_K9 NSTK HNSTK HNEXT _ (pe_from_K10 _ (pe_from_K11 _
    (pe_from_K12 _ pe_from_K12r_post))))))).
Qed.
End pall.

End p.
End b.
End a.
Arguments pt_K6 {fx rc} SK {PI} B MT KS.
Arguments pt_K7 {fx rc} SK {PI} B MT KS.
Arguments pt_K8 {fx rc} SK {PI} B MT KS.
Arguments pt_K9 {fx rc} SK {PI} B MT KS.
Arguments pt_K10 {fx rc} SK {PI} B MT KS.
Arguments pt_K11 {fx rc} SK {PI} B MT KS.
Arguments pt_K12 {fx rc} SK {PI} B MT KS.
Arguments pt_K12r {fx rc} SK {PI} B MT KS.
Arguments pt_leave {fx rc} SK {PI} B MT KS.
Arguments pt_ret {fx rc} SK {PI} B MT KS.
Arguments pt_leave_post {fx rc} SK {PI} B MT KS.
Arguments pt_K12r_post {fx rc} SK {PI} B MT KS.
Arguments pt_K6_post {fx rc} SK {PI} B MT KS.
(* The sink head is EXPLICIT on every exported lemma that depends on it (a Theorem Labs lane 21:57Z). *)
Arguments src_env_img {rc} SK {PI} B KS ASIL.
Arguments src_env_num {rc} SK {PI} B KS ASIL.
Arguments pe_from_ret_post {fx rc} SK {PI} B MT KS LAWS MTL.
Arguments pe_from_K12 {fx rc} SK {PI} B MT KS LAWS ASIL.
Arguments pe_from_K12r {fx rc} SK {PI} B MT KS LAWS ASIL.
Arguments pe_from_leave {fx rc} SK {PI} B MT KS LAWS ASIL ML ASF FFL MTF.
Arguments b_tail_geo {rc} SK {PI} B MT KS.
Arguments b_gagree_high {rc} SK {PI} B MT KS.
Arguments b_pch_achain {rc} SK {PI} B MT KS.
Arguments b_meta_now {rc} SK {PI} B MT KS ASIL.
Arguments b_aro_now {rc} SK {PI} B MT KS {HRO}.
Arguments b_foot_kept {rc} SK {PI} B MT KS.
Arguments b_input_block {rc} SK {PI} B MT KS.
Arguments b_block_off_hfoot {rc} SK {PI} B MT KS LAWS.
Arguments b_frame_off_hfoot {rc} SK {PI} B MT KS LAWS.
Arguments b_o_mod16 {rc} SK {PI} B MT KS.
Arguments pe_from_K8 {fx rc} SK {PI} B MT KS LAWS MTL ASIL CLOSE {HRO}.
Arguments r56_free_keep {fx rc} SK {PI} B MT KS LAWS ASIL.
Arguments pe_from_K10 {fx rc} SK {PI} B MT KS LAWS TL MTL ASIL AFREE.
Arguments pe_from_K11 {fx rc} SK {PI} B MT KS LAWS TL MTL ASIL AFREE.
Arguments pe_from_leave_post {fx rc} SK {PI} B MT KS LAWS MTL ASIL ML ASF FFL MTF.
Arguments pe_from_K12r_post {fx rc} SK {PI} B MT KS LAWS MTL ASIL ML ASF FFL MTF.
Arguments pe_from_K7 {fx rc} SK {PI} B MT KS LAWS MTL ASIL {HRO} NSTK HNSTK HNEXT.
Arguments r4_entry {fx rc} SK {PI} B MT KS LAWS.
Arguments pe_from_K9 {fx rc} SK {PI} B MT KS LAWS MTL ASIL {HRO} NSTK HNSTK HNEXT.
Arguments pe_from_K6 {fx rc} SK {PI} B MT KS LAWS MTL ASIL {HRO} FM_RA CTX ROI OPENS HROI HPATH HCTX HFMU.
Arguments pe_from_K6_post {fx rc} SK {PI} B MT KS LAWS TL MTL ASIL AFREE CLOSE {HRO} ML ASF FFL MTF NSTK HNSTK HNEXT FM_RA CTX ROI OPENS HROI HPATH HCTX HFMU.
