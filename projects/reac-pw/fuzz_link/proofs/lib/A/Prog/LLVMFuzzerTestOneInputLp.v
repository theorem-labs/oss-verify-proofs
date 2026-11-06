(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC85.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/YC85.v, ea5560a967b, carries it): the listing's names are bsym; module paths changed. No image numeral occurs in this file. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/YC85.v, with its module paths and module names changed; 313 of its 404 lines of code are new or changed and 320 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputFree.v, with its module names changed; 143 of its 198 lines of code are new or changed and 349 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): the small kit
   the control phases of the walk share (the two callocs, the loop head, the loop tail, the exit;
   lib/A/Prog/LLVMFuzzerTestOneInput{Blk,Head,Tail,Exit}.v): a cut's machine state as the symbolic runner's
   entry state, the registers a run leaves as they were, and the byte agreement a run with no write gives.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section a. Context {rc : YM05.RunCeil}.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

(* a cut's machine state is the runner's mkst at the cut's pc *)
Lemma lf_shape_eta : forall (fy : YK11.FPState) pc ms3, lf_shape fy pc ms3 ->
  ms3 = @mkst fy (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
  intros fy pc ms3 (H1 & H2 & H3 & H4 & H5 & H6). destruct ms3; cbn in *. unfold mkst. subst. reflexivity.
Qed.

(* the runner's state at a stop gives the cut's fixed fields *)
Lemma lf_shape_of_st_ok : forall (fy : YK11.FPState) (W : world SEGS) E ss ms,
  st_ok_pi (fx := fy) SEGS pa_val E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  lf_shape fy (ss_pc ss) ms.
Proof.
  intros fy W E ss ms HS Hrv. rewrite (st_ok_pi_restrict_mkst (fx := fy) (w_H W) E ss ms HS Hrv).
  unfold lf_shape, mkst. cbn. repeat split; reflexivity.
Qed.

(* the environment of a cut's entry state: its registers as atoms 0 .. 31 *)
Lemma lf_env_agree0 : forall regs0, env_agree 32 (Ereg regs0 []) (Eimg (Ereg regs0 [])).
Proof. intros regs0. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

(* a register the run left as the atom of its entry value holds that value *)
Lemma lf_reg_atom : forall (fy : YK11.FPState) (W : world SEGS) E ss ms regs0 (r : bv 5),
  st_ok_pi (fx := fy) SEGS pa_val E ss (restrict (w_H W) ms) -> env_agree 32 (Ereg regs0 []) E ->
  sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0 -> getr (ms_regs ms) r = getr regs0 r.
Proof.
  intros fy W E ss ms regs0 r HS HA Hr.
  rewrite (st_ok_pi_restrict_reg (fx := fy) (w_H W) E ss ms r HS), Hr.
  pose proof (bv_unsigned_in_range 5 r) as Rr. change (bv_modulus 5) with 32 in Rr.
  cbn [sv_denot]. destruct HA as [HA _]. rewrite (HA (Z.to_nat (bv_unsigned r))) by lia.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. apply ew_Ereg_nat. lia.
Qed.

(* a run whose regions write nothing changes no byte *)
Lemma kagree_frame_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> kagree SEGS (fun _ => False) m m'.
Proof.
  intros E m m' HF a _. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros (r & Hin & _). destruct Hin.
Qed.

Lemma kagree_false_trans : forall (m1 m2 m3 : word -> option byte),
  kagree SEGS (fun _ => False) m1 m2 -> kagree SEGS (fun _ => False) m2 m3 -> kagree SEGS (fun _ => False) m1 m3.
Proof. intros m1 m2 m3 H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* the materialised model keeps the descriptors and the file system *)
Lemma lf_wvb_fds : forall l X (m : Model), m_fds (with_vm_backing l X m) = m_fds m.
Proof. intros l X m. exact (proj1 (wvb_fds_fs l X m)). Qed.
Lemma lf_wvb_fs : forall l X (m : Model), m_fs (with_vm_backing l X m) = m_fs m.
Proof. intros l X m. exact (proj2 (wvb_fds_fs l X m)). Qed.

(* a register given as an atom plus a constant *)
Lemma lf_sv_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
  intros E n v c H Hv Hc. apply bv_eq. rewrite unsigned_lit_small by lia.
  change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)). exact (U_atom_off E n v c H Hv Hc).
Qed.

(* a run's frame_of as byte agreement: the run writes only inside its regions' writable ranges *)
Lemma lf_frame_kagree : forall E rs (m m' : word -> option byte) (Y : Z -> Prop),
  frame_of E rs m m' -> (forall a, 0 <= a < 2 ^ 64 -> in_wrange E rs a -> Y a) ->
  kagree SEGS (fun a => Y (a mod 2 ^ 64)) m m'.
Proof.
  intros E rs m m' Y HF HY a Ha. unfold mbyte. rewrite (HF (Z_to_bv 64 a)); [reflexivity|].
  intros Hin. apply Ha. rewrite Z_to_bv_unsigned in Hin. unfold bv_wrap, bv_modulus in Hin.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hin. apply HY; [apply Z.mod_pos_bound; lia | exact Hin].
Qed.
End a.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
Hypothesis LAWS : AR_laws pa_segs B.

#[local] Notation BASEF cx := (lf_base SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx).
#[local] Notation JRN cx fp ly S W mem mdl k :=
  (ajournal_gx SEGS B G_HARNESS 0 [] LLVMF_STK (spZ (c_regs cx)) (amf_harness_fp (c_T cx))
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(LF_CID, fp)] ly S W mem mdl k).

(* the journal's counters only get weaker as their bounds grow *)
Lemma lf_jbk_mono : forall cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ev' mo' wl' lv',
  ameter_laws MT -> ev <= ev' -> mo <= mo' -> (wl <= wl')%nat -> lv <= lv' ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ->
  lf_jbk B MT MS la_nul cx fp k2 ev' mo' wl' lv' ly3 S3 W3 ms3 md3 T3 own.
Proof.
  intros cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3 T3 own ev' mo' wl' lv' ML He Hm Hw Hl
    (J1 & JL & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15).
  split; [lia|]. split; [lia|]. split; [exact J2|]. split; [exact J3|]. split; [exact J4|]. split; [exact J5|].
  split; [exact (mle_weaken MT _ _ _ _ ML J6 Hm)|]. split; [lia|].
  exact (conj J8 (conj J9 (conj J10 (conj J11 (conj J12 (conj J13 (conj J14 J15))))))).
Qed.

(* the bytes the frame header, the frame's shadow, the journal's bookkeeping, the blocks' shadow and the data read
   lie below the allocator's ceiling *)
Lemma lf_cut_fp_low : forall cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a,
  BASEF cx -> JRN cx fp ly3 S3 W3 mem3 md3 k2 -> In (LF_CID, fp) (frames S3) ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3' T3 own ->
  In (md, MD_SIZE) (ablocks B ly3 S3) -> In (mk, MK_SIZE) (ablocks B ly3 S3) ->
  (lf_header_fp cx fp a \/ lf_fshadow_fp cx fp 112 a \/ lf_jbk_fp MS la_nul cx T3 a \/ lf_blocks_fp md mk a \/
   lf_data_fp md mk a) ->
  0 <= a < alloc_ceiling.
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a HB HJ HFR Hjbk B1 B2 Ha.
  destruct (lf_frame_facts SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END cx fp ly3 S3 W3
    mem3 md3 k2 HB HJ) as (_ & Hceil & _ & _ & _ & _ & HAR).
  pose proof (lf_sp1_le cx) as (P1 & P2).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof HB as (_ & _ & _ & Hla & HMS & _).
  pose proof Hjbk as (_ & _ & J2 & _ & _ & _ & _ & _ & J8 & _ & _ & J11 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR B1) as (_ & Md0 & Mdc & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR B2) as (_ & Mk0 & Mkc & _).
  change (req_size MD_SIZE) with MD_SIZE in Mdc. change (req_size MK_SIZE) with MK_SIZE in Mkc.
  destruct (frames_bounds _ _ LAWS _ _ _ _ _ _ _ HAR HFR) as (F0 & Fc & _).
  pose proof LF_frame_slot as (F1024 & _).
  assert (EF : lf_F cx fp = frame_addr ly3 LF_CID fp) by (unfold lf_F; symmetry; apply J2).
  rewrite F1024 in Fc.
  assert (SH : forall x, 0 <= x < alloc_ceiling -> 0 <= shadow_of_addr SHADOW_OFF x < alloc_ceiling).
  { intros x Hx. unfold shadow_of_addr, SHADOW_OFF. pose proof (Z.mul_div_le x 8 ltac:(lia)) as Q.
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as Q0. remember (x / 8) as y eqn:Ey. clear Ey. lia. }
  assert (LOW : forall a, in_roP SEGS PCAP_RLO PCAP_RHI a -> 0 <= a < alloc_ceiling).
  { intros a0 H0. pose proof (in_roP_low a0 H0) as L. unfold kLowMemEnd in L. lia. }
  assert (BLK : forall b n x, In (b, n) (ablocks B ly3 S3) -> b <= x < b + n -> 0 <= x < alloc_ceiling).
  { intros b n x Hin Hx. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H0 & Hc & _).
    unfold req_size in Hc. destruct (n =? 0) eqn:En; [apply Z.eqb_eq in En; subst n; lia | lia]. }
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - unfold lf_header_fp in Ha. rewrite F1024, EF in Ha. lia.
  - unfold lf_fshadow_fp, lf_SH in Ha. rewrite EF in Ha.
    pose proof (SH (frame_addr ly3 LF_CID fp) ltac:(lia)) as S0.
    pose proof (SH (frame_addr ly3 LF_CID fp + 1023) ltac:(lia)) as S1.
    unfold shadow_of_addr in S0, S1 |- *.
    assert (Hd : (frame_addr ly3 LF_CID fp + 1023) / 8 >= frame_addr ly3 LF_CID fp / 8 + 127) by
      (pose proof (Z.div_add_l 128 8 (frame_addr ly3 LF_CID fp)) as D;
       pose proof (Z.div_le_mono (frame_addr ly3 LF_CID fp + 1016) (frame_addr ly3 LF_CID fp + 1023) 8 ltac:(lia) ltac:(lia));
       replace (frame_addr ly3 LF_CID fp + 1016) with (127 * 8 + frame_addr ly3 LF_CID fp) in * by lia;
       rewrite Z.div_add_l in * by lia; lia).
    unfold shadow_of_addr in Ha. lia.
  - unfold lf_jbk_fp, amf_fp in Ha.
    destruct Ha as [[Ha | [Ha | (f & n & Hf & Ha)]] | [Ha | [Ha | Ha]]].
    + rewrite HMS in Ha. unfold amf_head_addr, amf_ofl_head in Ha.
      cbn [amf_sink_addr amf_say_addr amf_ofl_lock link_amf] in Ha. lia.
    + rewrite HMS in Ha. unfold amf_env_addr in Ha.
      cbn [amf_threaded amf_need_locks amf_ofl_lock link_amf] in Ha. lia.
    + destruct (amf_gi_shape SEGS MS T3 _ J8) as [Et | (f' & Et)]; rewrite Et in Hf; [destruct Hf|].
      destruct Hf as [Hf | []]. injection Hf as E1 E2. subst f' n.
      apply (BLK f AMF_BLOCK a); [apply J11; rewrite Et; left; reflexivity | exact Ha].
    + rewrite Hla in Ha. unfold LA_NUL, LA_LONG_ALIAS in Ha. lia.
    + exact (LOW a Ha).
    + apply (BLK (c_p cx) (c_n cx) a); [|exact Ha].
      apply (lf_input_block SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END LAWS cx fp ly3 S3
        W3 mem3 md3 k2 HB HJ). lia.
  - destruct Ha as [(x & Hx & ->) | (x & Hx & ->)]; apply SH; lia.
  - unfold lf_data_fp in Ha.
    destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]];
      try (unfold LA_G_NL, NK_SIZE, LA_G_NAMES, G_NAMES_SIZE, LA_LONG_ALIAS in Ha; lia); try lia.
    exact (LOW a Ha).
Qed.

(* every byte a cut's memory clauses read lies below the allocator's ceiling, in the spill slots under the
   cursor, or in the saved words: so a step that writes only the cursor or above the saved words keeps them *)
Lemma lf_cut_fp_place : forall cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a,
  BASEF cx -> JRN cx fp ly3 S3 W3 mem3 md3 k2 -> In (LF_CID, fp) (frames S3) ->
  lf_jbk B MT MS la_nul cx fp k2 ev mo wl lv ly3 S3 W3 ms3 md3' T3 own ->
  lf_blocks B cx md mk T3 ly3 S3 (rdW W3 (ms_mem ms3)) ->
  lf_cut_fp MS la_nul cx fp md mk T3 a ->
  (0 <= a < alloc_ceiling) \/ (lf_sp1 cx + 0x18 <= a < lf_sp1 cx + 0x118) \/
  (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)).
Proof.
  intros cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a HB HJ HFR Hjbk Hblk Ha.
  pose proof Hblk as (B1 & B2 & _).
  unfold lf_cut_fp in Ha.
  destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
  - right; right. exact Ha.
  - left. exact (lf_cut_fp_low cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a HB HJ HFR Hjbk B1 B2
      (or_introl Ha)).
  - left. exact (lf_cut_fp_low cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a HB HJ HFR Hjbk B1 B2
      (or_intror (or_introl Ha))).
  - right; left. unfold lf_slots_fp in Ha. lia.
  - left. exact (lf_cut_fp_low cx fp k2 ly3 S3 W3 mem3 md3 ev mo wl lv ms3 md3' md mk T3 own a HB HJ HFR Hjbk B1 B2
      (or_intror (or_intror Ha))).
Qed.
End b.
