(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B twin of lib/A/Prog/PcapSourceClose.v: pcap_source_close (fuzz_pcap.asan-ubsan
   0x81d4c, listing offset AF_pcap_source_close = 0x15c4, 31 instructions) on libreac v1.9.0's ASan+UBSan build, walked
   against lib/A's contract.

   The code is lib/A's ASan code (fuzz_pcap.asan 0x81e90, 27 instructions) with two UBSan guards and a register swap
   (measured: pcap-ubsan-inventory.md (sha256 5b607b62e337; internal record), row G6 and the pcap_source_close row of (c)). After
   the 32-byte frame and the saves of ra, s0 and s1, 0x81d5c `beqz a0` branches to the `unimp` at 0x81db4 when ps is
   null, 0x81d60 `mv s0,a0` (above the GOT load here), and 0x81d64 `andi a0,a0,7` / 0x81d68 `bnez a0` branch to the same
   `unimp` when ps is not 8-aligned. The shadow base is then loaded through the GOT word 0x996f8 (object 1; through a0,
   where the ASan code uses a1) from the cell 0xa17b8 (object 15). The rest is the ASan code at other pcs: the shadow
   check of ps's 8 bytes (0x81d80 `lbu`, 0x81d84 `bnez` to the error path at 0x81db8), f = ps->f (0x81d88), the test of
   f (0x81d8c `beqz` to 0x81da0), the call of the fclose wrapper's 4-byte jump (0x81d90 `jal
   __interceptor_trampoline_fclose`, 0x4161c), the second shadow check (0x81d94, 0x81d98 `bnez` to the error path at
   0x81dc0), ps->f = NULL (0x81d9c `sd zero,0(s0)`), the restores and the return (0x81db0).

   THE GUARDS. The walk's first symbolic run decides both, from the facts on a0 = ps that cl_entry proves (atom 10: ps
   >= 4096 and ps mod 2^3 = 0; ps >= 4096 because ps lies in a frame of the caller (frames_bounds), which gives the
   statement's ps <> 0; the alignment is the statement's ps mod 8 = 0):
     0x81d5c: decide_cond2 (Reusable/YP0e.v:932) through decide_eq (Reusable/YP0m.v:658-672), whose SOff / SLit arm
              (:665-666) tests ranges_disjoint (:653): ps's range [4096, ...] is disjoint from 0, so the branch is not
              taken;
     0x81d68: s_and_ptr (Reusable/YP0m.v:969-980) rewrites ps & 7 to 0 from the alignment fact, so `bnez` sees 0 and is
              not taken.
   These are the decisions of the released UBSan proof for the v1.8 image (proofs/libreac/fuzz_pcap/lib/U/Prog/
   pcap_source_close.v on origin/ossv/recipes c8557374ad2e): close_closed :43 (if_false, premise bv_unsigned a0 <> 0 at
   :23) and :45-46 (ub_align A8, premise bv_unsigned a0 mod 8 = 0 at :23), close_pro :82 and :84-85 (premises :58).

   The contract is lib/A's, not a copy (the shared-text rule): pb_pcap_source_closeX proves lib/A's image-generic
   AC.tpcap_source_close_specX (with AC.tpcap_source_close_post and AC.tclose_kept) at this image's segments SEGS and
   relro window pa_relro_lo / pa_relro_hi of the lib/B PAImg instance (on the pin PcapRelro.PCAP_RLO /
   PcapRelro.PCAP_RHI, lib/B/Prog/PcapRelro.v), at a = BASE + AF_pcap_source_close of the lib/B listing. The image-free constants
   (TPCAP_SOURCE_CLOSE_STK, EV_CLOSE, tclose_fblk) and lemmas are lib/A's too, through AC. The fclose wrapper's contract
   is the Section hypothesis AFCLOSE, of lib/A/Stdio/PFclose.v's image-generic afclose_source_spec type at this image.
   There is no lib/B/Stdio/PFclose.v (that statement takes the image as parameters). AFCLOSE is discharged by the
   asan-ubsan instance of a Theorem Labs lane's fclose walk lib/A/Stdio/WFclose.v, whose lib/B walk twin is
   lib/B/Stdio/WFclose.v (lib/B/Stdio/PFcloseInstB.v's inst_AFCLOSE_U composes it with lib/B/Stdio/WFcloseI.v).
   getr / mkst / seg_rom come from YK11; nothing from lib/Lib is imported. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceClose.v, with its module names changed; 3497 of its 3557 lines of code are new or changed and 570 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessTail.v, with its module paths and module names changed; 346 of its 396 lines of code are new or changed and 3507 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the DEC segment of its walk, from the DEC cut (+0x498, the read
   answered 0) through reac_served_decide to the four verdict cuts. Cut interface: lib/A/Prog/reac_served_markDefs.v;
   listing (internal path) (internal record, sha256 5943815fc488).

   The code of the segment:
     +0x498  mv a0, s8          a0 := kind (F + 0x20)
     +0x49c  mv a1, s7          a1 := alias (F + 0x60)
     +0x4a0  jal reac_served_decide (0x89510)      the verdict v in a0
     +0x4a4  addi a1, zero, 1
     +0x4a8  blt a1, a0 -> +0x508                  v in {2, 3}
     +0x4ac  bnez a0 -> +0x550                     v = 1: THE VOURS CUT
     +0x4b0                                        v = 0: THE VMARK CUT
     +0x508  addi a1, zero, 2
     +0x50c  bne a0, a1 -> +0x57c                  v = 3: THE VHOST CUT
     +0x510                                        v = 2: THE VVLAN CUT
   reac_served_decide is applied under SRr_bind at the walk's fx (its contract is `aleaf_rd`, model_decide_c.v), with
   its Pre from the DEC facts: the two buffers hold the read's strings (srm_bufs), each meets astr_rt_ok at the
   callee's window (reac_served_markBufs.v srm_bufs_rt), and the two literals are the Pre's policy strings (the
   Kit's srm_policy_at). Its read set is F's buffers (the Kit's srm_akb_frame), its write set is empty. After it the
   Kit's srm_call_back gives the cut base at the return, and reac_served_markXfer.v moves the kernel, the buffers, the
   marks block and the FILE across decide's akept (its exception set is empty). The verdict is one of 0 .. 3, so each
   arm pins a0 to its literal and the run reaches the arm's cut, which is that arm's obligation.

   Section hypotheses: LAWS (AR_laws), HV (LinkVals), TB (PcapSyms B, instance AD2l.PcapB_syms), RELRO_IMG (the relro
   window is image bytes; the top file discharges it from HSEGS and PcapRelroA.pcap_relro_in_image), HSEGS
   (pa_segs = tfibsegs), HDC (reac_served_decide_acontract at every fx; discharge reac_served_decide_aproof,
   model_decide.v).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk LinkWalkSide LinkWalkPi PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markUniq reac_served_markKit reac_served_markKitAt reac_served_markXfer reac_served_markBufs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the verdict is one of the four *)
Lemma srm_decide_cases : forall k a,
  decide k a = V_MARK \/ decide k a = V_OURS \/ decide k a = V_LEAVE_VLAN \/ decide k a = V_LEAVE_HOST.
Proof.
  intros k a. destruct a as [a|]; destruct k as [k|]; cbn [decide];
    repeat match goal with |- context [if ?b then _ else _] => destruct b end; auto.
Qed.

(* a callee-saved register of a symbolic state that maps it to its own atom, at an env read off regs0 *)
Ltac srm_reg_keep HS ER :=
  lazymatch goal with |- getr (ms_regs _) (Z_to_bv 5 ?c) = _ =>
    let Q := fresh "Q" in
    prreg HS (Z_to_bv 5 c) Q; rewrite Q; apply ER; [reflexivity | unfold A_TEXT; lia]
  end.
Ltac srm_keep_all HS ER :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hc := fresh "Hc" in
  intros r Hr; unfold acallee_saved in Hr;
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
               r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  clear Hr;
  repeat (destruct Hc as [Hc | Hc]; [subst r; srm_reg_keep HS ER |]);
  subst r; srm_reg_keep HS ER.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals.

Definition srm_dBx : sv := SLit SHADOW_OFF.
Definition srm_dspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma srm_ms_eta : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

(* the symbolic state at a cut: every register its own atom, no memory region (pcap PcapHarnessTail.v entry0) *)
Lemma srm_entry0 : forall pc (ms : machine_state) (W : world SEGS),
  ms_pc_val ms = w64 (BASE + pc) -> ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms) [])) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) ms).
Proof.
  intros pc ms W Hpc Hresv Hsvc Hrom Hfrg Hfcsr.
  pose proof (srm_ms_eta ms Hfrg Hsvc Hresv Hfcsr) as Hms. rewrite Hpc, Hrom in Hms.
  assert (Hms' : restrict (w_H W) ms =
    mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS))
    by (rewrite Hms at 1; reflexivity).
  rewrite Hms'.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. exact I.
  - split; [exact I | split; exact I].
Qed.

(* The base survives a run that writes no memory and keeps every callee-saved register. *)
Lemma srm_dec_base_move : forall cx fpos X ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_base fx SK B cx fpos X ly3 S3 W3 ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr -> ms_mem ms' = ms_mem ms ->
  aregs_preserved (ms_regs ms) (ms_regs ms') ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms) md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos X ly3 S3 W3 ms ms' md md' HB Hr Hs Hro Hf Hc Hm HP HJ Hfd Hfs.
  unfold srm_base in HB |- *. cbv zeta in HB |- *. rewrite Hm.
  destruct HB as (_ & _ & _ & _ & _ & _ & B7 & B8 & B9 & B10 & B11 & R2 & R9 & R8 & R18 & R19 & R25 & R26 & R20 &
    R22 & R3 & R4 & R27 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).
  do 11 (split; [assumption|]).
  split; [etransitivity; [exact (HP 2 ltac:(unfold acallee_saved; lia)) | exact R2]|].
  split; [etransitivity; [exact (HP 9 ltac:(unfold acallee_saved; lia)) | exact R9]|].
  split; [etransitivity; [exact (HP 8 ltac:(unfold acallee_saved; lia)) | exact R8]|].
  split; [etransitivity; [exact (HP 18 ltac:(unfold acallee_saved; lia)) | exact R18]|].
  split; [etransitivity; [exact (HP 19 ltac:(unfold acallee_saved; lia)) | exact R19]|].
  split; [etransitivity; [exact (HP 25 ltac:(unfold acallee_saved; lia)) | exact R25]|].
  split; [etransitivity; [exact (HP 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
  split; [etransitivity; [exact (HP 20 ltac:(unfold acallee_saved; lia)) | exact R20]|].
  split; [etransitivity; [exact (HP 22 ltac:(unfold acallee_saved; lia)) | exact R22]|].
  split; [etransitivity; [exact (HP 3 ltac:(unfold acallee_saved; lia)) | exact R3]|].
  split; [etransitivity; [exact (HP 4 ltac:(unfold acallee_saved; lia)) | exact R4]|].
  split; [etransitivity; [exact (HP 27 ltac:(unfold acallee_saved; lia)) | exact R27]|].
  rewrite Hfd, Hfs. repeat (split; [assumption|]). exact B33.
Qed.

(* +0x498 .. +0x4a0: the two moves and the call. The continuation runs at the callee's entry, with the memory
   unchanged, a0 = s8, a1 = s7, ra the return slot +0x4a4 and every callee-saved register kept. *)
Lemma srm_dec_call_run : forall (cx : srmcx) fpos ly3 S3 W3 (ms3 : machine_state) md3 (Q : world SEGS -> config -> Prop),
  srm_pre SK B cx -> srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_DEC) ->
  (forall (regs : bvmap 5 word) mat,
     getr regs 10 = getr (ms_regs ms3) 24 -> getr regs 11 = getr (ms_regs ms3) 23 ->
     getr regs 1 = w64 (BASE + (SRM_CUT_DEC + 12)) ->
     aregs_preserved (ms_regs ms3) regs ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 (mkst regs (w64 REAC_SERVED_DECIDE_A) (ms_mem ms3) (seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md3) mat md3) ->
     SRr SEGS W3 (mkCfg (mkst regs (w64 REAC_SERVED_DECIDE_A) (ms_mem ms3) (seg_rom SEGS))
       (with_vm_backing (m_vm_lazy md3) mat md3)) Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 Q HP HB Hpc K.
  pose proof HB as HB0. unfold srm_base in HB. cbv zeta in HB.
  destruct HB as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _).
  destruct HP as ((_ & HGok & _) & _ & _).
  pose proof (srm_entry0 SRM_CUT_DEC ms3 W3 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS.
  remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
            ew E n = getr (ms_regs ms3) r)
    by (intros n r Hr Hn; subst E; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  assert (SHOK : sh_ok SEGS srm_dBx [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
  clear HEdef.
  pose (RUN := paj_run_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  paj_run_tok RUN HS HJ SHOK srm_dspan; [apply awr_ok_x_nil |].
  assert (HFm : ms_mem ms = ms_mem ms3)
    by (apply functional_extensionality; intros x; exact (frame_of_nil _ _ _ x HF)).
  pmkst HS.
  assert (KEEP : aregs_preserved (ms_regs ms3) (ms_regs ms)) by srm_keep_all HS ER.
  prreg HS (Z_to_bv 5 1) Q1. prreg HS (Z_to_bv 5 10) Q10. prreg HS (Z_to_bv 5 11) Q11.
  rewrite (lv_sigma HV), HFm.
  change (Z_to_bv 64 (link_sigma LS_reac_served_decide)) with (w64 REAC_SERVED_DECIDE_A).
  apply K.
  - etransitivity; [exact Q10|]. apply ER; [reflexivity | unfold A_TEXT; lia].
  - etransitivity; [exact Q11|]. apply ER; [reflexivity | unfold A_TEXT; lia].
  - etransitivity; [exact Q1|]. unfold w64. f_equal; unfold SRM_CUT_DEC, AF_reac_served_mark; lia.
  - exact KEEP.
  - apply (srm_dec_base_move cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0); try reflexivity;
      first [exact KEEP | rewrite <- HFm; exact HJ | exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _))].
Qed.

(* the end of an arm's run: the state at the cut, handed to the continuation *)
Ltac srm_arm_close K HB0 HJ HS HF ER :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?m) =>
  lazymatch type of HF with frame_of _ _ (ms_mem ?m0) _ =>
  let HFm := fresh "HFm" in let KEEP := fresh "KEEP" in
  assert (HFm : ms_mem m = ms_mem m0)
    by (apply functional_extensionality; let x := fresh "x" in intros x; exact (frame_of_nil _ _ _ x HF));
  pmkst HS;
  assert (KEEP : aregs_preserved (ms_regs m0) (ms_regs m)) by srm_keep_all HS ER;
  apply K; cbn [ms_pc_val ms_mem ms_regs mkst];
  [ unfold w64; f_equal; unfold SRM_CUT_VMARK, SRM_CUT_VOURS, SRM_CUT_VVLAN, SRM_CUT_VHOST, AF_reac_served_mark; lia
  | exact HFm
  | exact KEEP
  | apply (srm_dec_base_move _ _ _ _ _ _ m0 _ _ _ HB0); try reflexivity;
    first [ exact HFm | exact KEEP | rewrite <- HFm; exact HJ
          | exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _)) ] ]
  end end.

(* +0x4a4 .. a verdict cut: with a0 = v, the run reaches the cut of v with the memory unchanged and every
   callee-saved register kept. *)
Lemma srm_dec_arm_run : forall c pcoff (cx : srmcx) fpos ly4 S4 W4 (ms4 : machine_state) md4
    (Q : world SEGS -> config -> Prop),
  (c = V_MARK /\ pcoff = SRM_CUT_VMARK) \/ (c = V_OURS /\ pcoff = SRM_CUT_VOURS) \/
  (c = V_LEAVE_VLAN /\ pcoff = SRM_CUT_VVLAN) \/ (c = V_LEAVE_HOST /\ pcoff = SRM_CUT_VHOST) ->
  srm_pre SK B cx -> srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 ms4 md4 ->
  ms_pc_val ms4 = w64 (BASE + (SRM_CUT_DEC + 12)) -> getr (ms_regs ms4) 10 = w64 c ->
  (forall (ms5 : machine_state) md5, ms_pc_val ms5 = w64 (BASE + pcoff) -> ms_mem ms5 = ms_mem ms4 ->
     aregs_preserved (ms_regs ms4) (ms_regs ms5) -> srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 ms5 md5 ->
     SRr SEGS W4 (mkCfg ms5 md5) Q) ->
  SRr SEGS W4 (mkCfg ms4 md4) Q.
Proof.
  intros c pcoff cx fpos ly4 S4 W4 ms4 md4 Q Hc HP HB Hpc R10 K.
  pose proof HB as HB0. unfold srm_base in HB. cbv zeta in HB.
  destruct HB as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _).
  destruct HP as ((_ & HGok & _) & _ & _).
  pose proof (srm_entry0 (SRM_CUT_DEC + 12) ms4 W4 Hpc Hresv Hsvc Hrom Hfrg Hfcsr) as HS0.
  destruct Hc as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]];
  pose proof (st_ok_pi_pin_reg' _ _ _ (Z_to_bv 5 10) _ HS0 R10 eq_refl) as HS; clear HS0; norm_pi HS;
  remember (Eimg (Ereg (ms_regs ms4) [])) as E eqn:HEdef;
  (assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env));
  (assert (ER : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
            ew E n = getr (ms_regs ms4) r)
    by (intros n r Hr Hn; subst E; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)));
  (assert (SHOK : sh_ok SEGS srm_dBx [] E (mrestrict (w_H W4) (ms_mem ms4))) by constructor);
  clear HEdef;
  pose (RUNTO := paj_run_to_x SK B LAWS (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  - paj_run_to_tok RUNTO HS HJ SHOK srm_dspan SRM_CUT_VMARK; [apply awr_ok_x_nil |].
    srm_arm_close K HB0 HJ HS HF ER.
  - paj_run_to_tok RUNTO HS HJ SHOK srm_dspan SRM_CUT_VOURS; [apply awr_ok_x_nil |].
    srm_arm_close K HB0 HJ HS HF ER.
  - paj_run_to_tok RUNTO HS HJ SHOK srm_dspan SRM_CUT_VVLAN; [apply awr_ok_x_nil |].
    srm_arm_close K HB0 HJ HS HF ER.
  - paj_run_to_tok RUNTO HS HJ SHOK srm_dspan SRM_CUT_VHOST; [apply awr_ok_x_nil |].
    srm_arm_close K HB0 HJ HS HF ER.
Qed.

(* ---- the segment ---- *)
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis HDC : forall fx' : YK11.FPState, @reac_served_decide_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

(* a section hypothesis a shared lemma takes, by assumption *)
Ltac srm_inst H := repeat match type of H with
  | forall _ : YI16.sink_head, _ => specialize (H SK)
  | forall _ : asyms, _ => specialize (H B)
  | ?A -> _ => let h := fresh "h" in assert (h : A) by assumption; specialize (H h); clear h end.

(* a verdict cut's state, from the DEC facts moved to it *)
Lemma srm_dec_arm_gi : forall pcoff v cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 (ms5 : machine_state) md5,
  ms_pc_val ms5 = w64 (BASE + pcoff) ->
  srm_ent cx s kbs tab gbs k0 -> r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = v ->
  getr (ms_regs ms5) 23 = w64 (srm_alias cx fpos) -> getr (ms_regs ms5) 24 = w64 (srm_kind cx fpos) ->
  srm_kern (rdW W4 (ms_mem ms5)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  srm_bufs cx fpos W4 (ms_mem ms5) (srm_R s kbs tab) ->
  amarks_at SEGS (rdW W4 (ms_mem ms5)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W4 (ms_mem ms5)) (sm_sink cx) k0 ->
  srm_base fx SK B cx fpos (srm_E cx) ly4 S4 W4 ms5 md5 ->
  @srm_gi_arm fx rc SK PI B pcoff v cx fpos ly4 S4 W4 ms5 md5.
Proof.
  intros pcoff v cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 ms5 md5 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
  exists s, kbs, tab, gbs, k0, kbs1.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 H11)))))))))).
Qed.

(* THE DEC SEGMENT *)
Lemma srm_dec : srm_vmark_obl fx SK B -> srm_vours_obl fx SK B -> srm_vvlan_obl fx SK B -> srm_vhost_obl fx SK B ->
  srm_dec_obl fx SK B.
Proof.
  intros OVM OVO OVV OVH cx fpos ly3 S3 W3 ms3 md3 HP HGS HG.
  unfold srm_gi_dec in HG. destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & HG). cbv zeta in HG.
  destruct HG as (Hpc & Hent & Hrc & R23 & R24 & Hkern & Hbufs & Hmarks & Hfile & HB).
  pose proof asan_consts as ((C1a & C1b) & _).
  pose proof pa_B_ok as (HB0 & HB1 & HB2). pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBLO.
  destruct (srm_R_lens s kbs tab) as (HLk & HLa).
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HP HB)
    as (HF4096 & HFceil & HF64 & HFapp & _ & HFin & EF & _ & EFa & _ & _).
  destruct (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HP) as (_ & Hspceil & _ & Hsp1 & _).
  rewrite REAC_SERVED_MARK_AK_val in Hspceil.
  pose proof Hent as (Hmk0 & _ & _ & HNLK & _).
  apply (srm_dec_call_run cx fpos ly3 S3 W3 ms3 md3 _ HP HB Hpc).
  intros regs mat Rg10 Rg11 Rg1 KEEP1 HBc.
  set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
  set (msc := mkst regs (w64 REAC_SERVED_DECIDE_A) (ms_mem ms3) (seg_rom SEGS)) in *.
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 msc mdc HP HBc) as Hspc.
  change (spZ (ms_regs msc)) with (spZ regs) in Hspc.
  set (R := srm_R s kbs tab) in *.
  (* the two arguments *)
  assert (A0 : aarg regs 0 = srm_kind cx fpos).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rg10, R24. unfold w64. apply unsigned_lit_small. unfold srm_kind, SRM_KIND, SRM_FB in *. lia. }
  assert (A1 : aarg regs 1 = srm_alias cx fpos).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Rg11, R23. unfold w64. apply unsigned_lit_small. unfold srm_alias, SRM_ALIAS, SRM_FB in *. lia. }
  pose proof Hbufs as (Hbk & Hba & _).
  assert (HAk : astr_arg SEGS (rdW W3 (ms_mem ms3)) (aarg regs 0) (Some (r_kind R))).
  { rewrite A0. split; [unfold srm_kind, SRM_KIND in *; lia | exact Hbk]. }
  assert (HAa : astr_arg SEGS (rdW W3 (ms_mem ms3)) (aarg regs 1) (Some (r_alias R))).
  { rewrite A1. split; [unfold srm_alias, SRM_ALIAS in *; lia | exact Hba]. }
  (* reac_served_decide's premises *)
  pose proof DECIDE_AK_val as EDK. pose proof REAC_CODE_EMIT_AK_val as EEK.
  assert (HK8 : 0 <= DECIDE_AK <= REAC_CODE_EMIT_AK) by lia.
  assert (HRET : YK0s.ret_ok (getr (ms_regs msc) 1)).
  { change (getr (ms_regs msc) 1) with (getr regs 1). rewrite Rg1. unfold w64.
    apply ret_ok_codeptr_v; [unfold SRM_CUT_DEC, AF_reac_served_mark; lia | reflexivity]. }
  assert (HRA : 4096 <= raZ (ms_regs msc)).
  { unfold raZ. change (getr (ms_regs msc) 1) with (getr regs 1). rewrite Rg1. unfold w64.
    rewrite unsigned_lit_small by (unfold SRM_CUT_DEC, AF_reac_served_mark; lia).
    unfold SRM_CUT_DEC, AF_reac_served_mark; lia. }
  pose proof (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc DECIDE_AK [] []
    HP HBc (fun a H => H) HK8 HRET HRA (fun cd H => match H with end)
    (fun a H => match H with ex_intro _ r (conj Hr _) => match Hr with end end)) as HAPRE.
  assert (HRD : forall a, decide_ard SEGS regs (rdW W3 (ms_mem ms3)) a ->
                  akb SEGS B ly3 S3 (spZ regs - DECIDE_AK) (spZ regs) a).
  { intros a Ha. apply (srm_akb_frame SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 msc mdc _ _ a HP HBc).
    unfold decide_ard, astr_rd in Ha. destruct Ha as [(_ & s' & Hs' & Ha) | (_ & s' & Hs' & Ha)].
    - rewrite A0 in Hs', Ha. rewrite (acstr_at_unique _ _ _ _ _ Hs' Hbk) in Ha.
      unfold srm_kind, SRM_KIND, KIND_CAP, SRM_FB in *. lia.
    - rewrite A1 in Hs', Ha. rewrite (acstr_at_unique _ _ _ _ _ Hs' Hba) in Ha.
      unfold srm_alias, SRM_ALIAS, ALIAS_MAX, SRM_FB in *. lia. }
  assert (HPRE : decide_apre SEGS LA_RSD_PREFIX LA_RSD_VLAN regs (rdW W3 (ms_mem ms3))).
  { pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 msc mdc DECIDE_AK HP HBc
      (fun a H => H) HK8) as (Pp & Ppr & Pv & Pvr & _).
    destruct (srm_bufs_rt SK B LAWS cx fpos _ ly3 S3 W3 ms3 md3 R regs DECIDE_AK HB HF64 HFceil HFapp HFin EF
      Hbufs HLk HLa ltac:(lia) ltac:(rewrite Hspc; lia))
      as (Rk & Ra).
    exists (Some (r_kind R)), (Some (r_alias R)).
    refine (conj HAk (conj HAa (conj Pp (conj Ppr (conj Pv (conj Pvr (conj _ _))))))).
    - intros t Ht. injection Ht as <-. rewrite A0. exact Rk.
    - intros t Ht. injection Ht as <-. rewrite A1. exact Ra. }
  (* the call *)
  eapply SRr_bind.
  { exact (HDC fx (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx)
      (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem ms3) mdc (sm_k cx) regs
      HAPRE HRD HPRE). }
  intros W4 c4 _ Hpost.
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc DECIDE_AK
    (fun a => inFP (decide_awr regs (rdW W3 (ms_mem ms3))) a) (decide_apost SEGS regs (rdW W3 (ms_mem ms3)))
    W4 c4 HP HBc (fun a H => H) (@BoxBase.fxr_refl fx) HK8
    (fun a H => match H with ex_intro _ r (conj Hr _) => match Hr with end end) Hpost)
    as (ly4 & S4 & regs4 & mem4 & md4 & -> & HB4 & KEEP2 & HK & HD).
  change (getr (ms_regs msc) 1) with (getr regs 1) in HB4 |- *.
  change (ms_mem msc) with (ms_mem ms3) in HK.
  change (spZ (ms_regs msc)) with (spZ regs) in HK.
  set (ms4 := mkst regs4 (getr regs 1) mem4 (seg_rom SEGS)) in *.
  (* the verdict *)
  assert (Hv : getr regs4 10 = w64 (decide (Some (r_kind R)) (Some (r_alias R)))) by exact (HD _ _ HAk HAa).
  (* the DEC facts at the return *)
  pose proof (ajournal_gx_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 HB4))))))) as HAR4.
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 ms4 md4 HP HB4)
    as (_ & _ & _ & _ & _ & HFin4 & _ & _ & EFa4 & _ & _).
  assert (HEc : forall a, ~ inFP (decide_awr regs (rdW W3 (ms_mem ms3))) a)
    by (intros a (r & Hr & _); destruct Hr).
  pose proof xfer_bufs as XB. srm_inst XB.
  pose proof (XB cx fpos ly3 S3 W3 (ms_mem ms3) W4 mem4 ly4 S4 md4 _ _ _ R HK HAR4 HFin HFin4 EFa EFa4
    (fun a _ => HEc a) (fun i _ => HEc _) HLk HLa Hbufs) as Hbufs4. clear XB.
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 DECIDE_AK HP HB
    (fun a H => H) HK8 Hmk0) as (_ & (Hmk3 & _) & _).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 ms4 md4 DECIDE_AK HP HB4
    (fun a H => H) HK8 Hmk0) as (_ & (Hmk4 & _) & _).
  pose proof xfer_amarks as XM. srm_inst XM.
  pose proof (XM ly3 S3 W3 (ms_mem ms3) W4 mem4 ly4 S4 md4 _ _ _ (srm_mk cx) gbs HK HAR4 Hmk3 Hmk4
    (fun a _ => HEc a) Hmarks) as Hmarks4. clear XM.
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 DECIDE_AK HP HB
    (fun a H => H) HK8) as (_ & Hf3).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 ms4 md4 DECIDE_AK HP HB4
    (fun a H => H) HK8) as (_ & Hf4).
  pose proof xfer_amemfile_k as XF. srm_inst XF.
  pose proof (XF ly3 S3 W3 (ms_mem ms3) W4 mem4 ly4 S4 md4 _ _ _ (sm_sink cx) k0 HK HAR4 Hf3 Hf4
    (fun a _ => HEc a) Hfile) as Hfile4. clear XF.
  (* the kernel: g_nl by decide's akept, the table strings are the entry's at both cuts *)
  assert (HTV : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall a, p <= a <= p + Z.of_nat (length n2) -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros i n2 ix p Hi Hp Hp64 a Ha. change mem4 with (ms_mem ms4).
    assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    assert (Htl : Z.of_nat (length tab) <= 80)
      by (destruct HNLK as (_ & _ & _ & _ & _ & (_ & Htl & _) & _); exact Htl).
    assert (Hp4 : au64_at SEGS (rdW W4 (ms_mem ms4)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { apply (srm_val_mem_move SEGS (w_H W3) (w_H W4) (ms_mem ms3) (ms_mem ms4)); [|exact Hp].
      intros x Hx.
      rewrite (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 ms4 md4 x HP HB4 (fun a H => H)
        ltac:(unfold NK_IF_NAME, NK_SIZE in *; lia)).
      rewrite (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 x HP HB (fun a H => H)
        ltac:(unfold NK_IF_NAME, NK_SIZE in *; lia)).
      reflexivity. }
    rewrite (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 ms4 md4 kbs tab i n2 ix p a
      HP HB4 (fun a H => H) HNLK Hi Hp4 Hp64 Ha).
    rewrite (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 kbs tab i n2 ix p a
      HP HB (fun a H => H) HNLK Hi Hp Hp64 Ha).
    reflexivity. }
  pose proof xfer_kern as XK. srm_inst XK.
  pose proof (XK ly3 S3 W3 (ms_mem ms3) W4 mem4 _ _ _ kbs kbs1 tab _ _ _ HK (fun a _ => HEc a) HTV Hkern)
    as Hkern4. clear XK.
  (* the registers the arms read *)
  assert (G23 : getr regs4 23 = w64 (srm_alias cx fpos)).
  { etransitivity; [exact (KEEP2 23 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (KEEP1 23 ltac:(unfold acallee_saved; lia))|]. exact R23. }
  assert (G24 : getr regs4 24 = w64 (srm_kind cx fpos)).
  { etransitivity; [exact (KEEP2 24 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact (KEEP1 24 ltac:(unfold acallee_saved; lia))|]. exact R24. }
  assert (Hpc4 : ms_pc_val ms4 = w64 (BASE + (SRM_CUT_DEC + 12))) by exact Rg1.
  (* the four arms *)
  destruct (srm_decide_cases (Some (r_kind R)) (Some (r_alias R))) as [Ev | [Ev | [Ev | Ev]]];
    rewrite Ev in Hv.
  - apply (srm_dec_arm_run V_MARK SRM_CUT_VMARK cx fpos ly4 S4 W4 ms4 md4 _
      (or_introl (conj eq_refl eq_refl)) HP HB4 Hpc4 Hv).
    intros ms5 md5 Hpc5 Hm5 KEEP3 HB5. apply (OVM cx fpos ly4 S4 W4 ms5 md5 HP HGS).
    apply (srm_dec_arm_gi _ _ cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 ms5 md5 Hpc5 Hent Hrc Ev);
      try rewrite Hm5; try assumption;
      [etransitivity; [exact (KEEP3 23 ltac:(unfold acallee_saved; lia)) | exact G23]
      |etransitivity; [exact (KEEP3 24 ltac:(unfold acallee_saved; lia)) | exact G24]].
  - apply (srm_dec_arm_run V_OURS SRM_CUT_VOURS cx fpos ly4 S4 W4 ms4 md4 _
      (or_intror (or_introl (conj eq_refl eq_refl))) HP HB4 Hpc4 Hv).
    intros ms5 md5 Hpc5 Hm5 KEEP3 HB5. apply (OVO cx fpos ly4 S4 W4 ms5 md5 HP HGS).
    apply (srm_dec_arm_gi _ _ cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 ms5 md5 Hpc5 Hent Hrc Ev);
      try rewrite Hm5; try assumption;
      [etransitivity; [exact (KEEP3 23 ltac:(unfold acallee_saved; lia)) | exact G23]
      |etransitivity; [exact (KEEP3 24 ltac:(unfold acallee_saved; lia)) | exact G24]].
  - apply (srm_dec_arm_run V_LEAVE_VLAN SRM_CUT_VVLAN cx fpos ly4 S4 W4 ms4 md4 _
      (or_intror (or_intror (or_introl (conj eq_refl eq_refl)))) HP HB4 Hpc4 Hv).
    intros ms5 md5 Hpc5 Hm5 KEEP3 HB5. apply (OVV cx fpos ly4 S4 W4 ms5 md5 HP HGS).
    apply (srm_dec_arm_gi _ _ cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 ms5 md5 Hpc5 Hent Hrc Ev);
      try rewrite Hm5; try assumption;
      [etransitivity; [exact (KEEP3 23 ltac:(unfold acallee_saved; lia)) | exact G23]
      |etransitivity; [exact (KEEP3 24 ltac:(unfold acallee_saved; lia)) | exact G24]].
  - apply (srm_dec_arm_run V_LEAVE_HOST SRM_CUT_VHOST cx fpos ly4 S4 W4 ms4 md4 _
      (or_intror (or_intror (or_intror (conj eq_refl eq_refl)))) HP HB4 Hpc4 Hv).
    intros ms5 md5 Hpc5 Hm5 KEEP3 HB5. apply (OVH cx fpos ly4 S4 W4 ms5 md5 HP HGS).
    apply (srm_dec_arm_gi _ _ cx fpos s kbs tab gbs k0 kbs1 ly4 S4 W4 ms5 md5 Hpc5 Hent Hrc Ev);
      try rewrite Hm5; try assumption;
      [etransitivity; [exact (KEEP3 23 ltac:(unfold acallee_saved; lia)) | exact G23]
      |etransitivity; [exact (KEEP3 24 ltac:(unfold acallee_saved; lia)) | exact G24]].
Qed.

End b.
End a.
About srm_dec.
Print Assumptions srm_dec.
