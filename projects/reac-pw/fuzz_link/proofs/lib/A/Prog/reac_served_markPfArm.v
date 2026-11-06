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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v, with its module paths and module names changed; 785 of its 844 lines of code are new or changed and 337 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markWret.v, with its module paths and module names changed; 307 of its 385 lines of code are new or changed and 766 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the head and the end of the two wrapper_fprintf arms
   (VVLAN +0x510 and VHOST +0x57c, against lib/A/Prog/reac_served_markDefs.v).

   Both arms start the same way (listing (internal path) (internal record, sha256 5943815fc488)):
     auipc a0; ld a0, g_say          a0 := the memory FILE (sink <> 0)
     bnez a0                         taken: the stderr fallback (+0x51c / +0x588) is not reached
     auipc a1; addi a1, .str.8/.9    a1 := the format
     mv a2, s4 (; mv a3, s7)         the name (and the alias)
     jal wrapper_fprintf (0x43084)
   and end the same way: `addi s5, zero, v; j +0x2cc` (v = V_LEAVE_VLAN = 2 or V_LEAVE_HOST = 3).

   - `srm_pfv_ok`: the symbolic state at an arm cut, with g_say's word as a region whose value is the env atom 32.
   - `srm_pf_head`: from the cut to the wrapper's entry, over the two engine runs (to `bnez`, then to the call) that
     the arm file computes: the wrapper's entry state with a0 = sink, a1 = the format, ra = the return address, the
     other registers as the run's end state names them, the memory and the journal unchanged.
   - `srm_pf_str_arg` / `srm_pf_alias_arg`: the name (srm_name_at) and the alias (srm_bufs) as reac_code_emit_c.v
     `apf_arg_ok` at the wrapper's window LFP_STK; `srm_pf_lit_apart`: a .rodata literal apart from the FILE block.
   - `srm_pf_after`: from the wrapper's return at fx' (the continuation of reac_served_markPfStep.v
     srm_fprintf_step) to the post at fx: the kernel and the marks carried across the wrapper (whose write set is the
     FILE block), the tail run to RESTORE (srm_leave_tail at fx'), lifted back to fx (link_amem.v srr_apostF_lift).

   Proves no function (kind: segment lemma of reac_served_mark's walk: the VVLAN and VHOST cuts to RESTORE). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkPrintf LinkWalkMkFile LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markDefs reac_served_markUniq reac_served_markKit reac_served_markKitAt reac_served_markXfer.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markPf reac_served_markPfStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkFmt reac_served_markEmitArgs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* g_say's word (object 47 of the listing, 0x6312e0): its value is the env's first extra atom *)
Definition srm_pf_gsay : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 47)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition srm_pfv_ss (pc : Z) : sstate := mkSS pc sr_atoms [srm_pf_gsay] None (mkFacts [] [] []).

Lemma srm_pf_add_cond_mem : forall ss c, ss_mem (add_cond ss c) = ss_mem ss.
Proof. intros [] c. reflexivity. Qed.
Lemma srm_pf_setpc_regs : forall ss pc, ss_regs (setpc ss pc) = ss_regs ss.
Proof. intros [] pc. reflexivity. Qed.
Lemma srm_pf_setpc_pc : forall ss pc, ss_pc (setpc ss pc) = pc.
Proof. intros [] pc. reflexivity. Qed.
Lemma srm_pf_setpc_resv : forall ss pc, ss_resv (setpc ss pc) = ss_resv ss.
Proof. intros [] pc. reflexivity. Qed.

Lemma srm_pf_u5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
  intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  apply Z.mod_small. lia.
Qed.

Lemma srm_pf_w64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

(* the bytes of a frame of the region list have an empty write window: a run over it stores nothing *)
Lemma srm_pf_frame_gsay : forall E (m m' : word -> option byte), frame_of E [srm_pf_gsay] m m' -> m' = m.
Proof.
  intros E m m' Hfr. apply functional_extensionality. intros x. apply Hfr.
  intros (r & Hr & Hx). destruct Hr as [<- | []]. unfold srm_pf_gsay in Hx. cbn [YP09.r_wlo YP09.r_whi] in Hx. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis TB : PcapSyms B.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.

(* ==========================================================================
   1. The symbolic state at an arm cut
   ========================================================================== *)

Lemma srm_pfv_ok : forall (W : world SEGS) regs mem pc sink,
  au64_at SEGS (rdW W mem) LA_G_SAY sink -> 0 <= sink < 2 ^ 64 ->
  st_ok_pi SEGS pa_val (Eimg (Ereg regs [w64 sink])) (srm_pfv_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
  intros W regs mem pc sink Hg Hs.
  pose proof (lv_obj HV 47%nat ltac:(unfold link_nobj; lia)) as V47. cbv [link_obj] in V47.
  set (E := Eimg (Ereg regs [w64 sink])).
  assert (E32 : ew E 32 = Z_to_bv 64 sink).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs [w64 sink] 0). }
  assert (VB : base_val E (Some (A_OBJ 47)) = pa_val (A_OBJ 47)).
  { cbn [base_val]. subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    apply unsigned_lit_small. pose proof (pa_val_range (A_OBJ 47)). lia. }
  rewrite restrict_mkst_fx. unfold srm_pfv_ss. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold srm_pf_gsay. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    fold E. rewrite VB.
    split; [rewrite V47; lia|]. split; [rewrite V47; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 47)) 0 8 (SOff 32 0) sink);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    rewrite Z.add_0_r, V47. cbn [ms_mem restrict mkst]. exact Hg.
  - exact (conj I I).
  - split; [exact I | split; exact I].
Qed.

(* ==========================================================================
   2. From the cut to the wrapper's entry
   ========================================================================== *)

Lemma srm_pf_head : forall (pcoff retoff : Z) (fi : nat) (ssA ssB : sstate) (cx : srmcx) fpos ly3 S3
    (W3 : world SEGS) (ms3 : machine_state) md3 (Q : world SEGS -> config -> Prop),
  sym_runN_pi pl_tpi FUEL (srm_pfv_ss pcoff) = (ssA, PRS_stopped (SR_branch BC_NE (SOff 32 0) (SLit 0))) ->
  sym_runN_pi pl_tpi FUEL (add_cond ssA (mkAC BC_NE (SOff 32 0) (SLit 0))) =
    (ssB, PRS_call LS___interceptor_trampoline_fprintf) ->
  ss_mem ssA = [srm_pf_gsay] -> ss_resv ssB = None -> ss_mem ssB = [srm_pf_gsay] ->
  sr_get (ss_regs ssB) 1%bv = SOff A_TEXT retoff ->
  sr_get (ss_regs ssB) 10%bv = SOff 32 0 ->
  sr_get (ss_regs ssB) 11%bv = SOff (A_OBJ fi) 0 -> (fi < link_nobj)%nat ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssB) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) SRM_PF_KEEP = true ->
  srm_pre SK B cx ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  ms_pc_val ms3 = w64 (BASE + pcoff) ->
  (forall (regsT : bvmap 5 word) md1,
     getr regsT 1 = Z_to_bv 64 (BASE + retoff) ->
     getr regsT 10 = w64 (sm_sink cx) ->
     getr regsT 11 = w64 (link_obj fi) ->
     srm_kregs regsT (ms_regs ms3) ->
     (forall (r : bv 5) n, sr_get (ss_regs ssB) r = SOff n 0 -> (n < 32)%nat ->
        getr regsT r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat n))) ->
     ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
       (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
       ly3 S3 W3 (ms_mem ms3) md1 (sm_k cx) ->
     m_fds md1 = m_fds md3 -> m_fs md1 = m_fs md3 ->
     SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 LA_W_FPRINTF) (ms_mem ms3) (seg_rom SEGS)) md1) Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros pcoff retoff fi ssA ssB cx fpos ly3 S3 W3 ms3 md3 Q HrA HrB HmA HrvB HmB R1 R10 R11 Hfi HKB HPRE HB Hpc HK.
  pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
  destruct HB0 as (Zrsv & Zsvc & Zrom & Zfrg & Zfcsr & HJ & _).
  pose proof HPRE as ((_ & HGX & _) & _).
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HB
    (fun a H => H)) as (Hg & Hs1 & Hs2 & Hs3).
  assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)])) (srm_pfv_ss pcoff)
    (restrict (w_H W3) ms3)).
  { rewrite (srm_pf_ms_eta ms3 Zfrg Zsvc Zrsv Zfcsr) at 2. rewrite Hpc, Zrom. apply srm_pfv_ok; [exact Hg | lia]. }
  assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)]))) by apply Eimg_env.
  assert (E32 : ew (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)])) 32 = w64 (sm_sink cx)).
  { rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra (ms_regs ms3) [w64 (sm_sink cx)] 0). }
  assert (EREG : forall n, (n < 32)%nat ->
    ew (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)])) n = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat n))).
  { intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. rewrite srm_pf_u5 by exact Hn.
    reflexivity. }
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [w64 (sm_sink cx)]) (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)])))
    by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  remember (Eimg (Ereg (ms_regs ms3) [w64 (sm_sink cx)])) as E eqn:HEdef.
  (* the cut to `bnez a0` *)
  eapply (paj_run_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx));
    [exact HEI | exact HS | exact HrA | exact I | exact HJ | |].
  { cbn [srm_pfv_ss ss_mem]. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold srm_pf_gsay in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  intros ms1 mat1 HS1 HJ1 HF1 _ _.
  cbn [srm_pfv_ss ss_mem] in HF1. pose proof (srm_pf_frame_gsay _ _ _ HF1) as Em1. clear HF1.
  (* `bnez a0`: g_say holds the FILE, sink <> 0 *)
  apply (paj_branch (PI := PI) W3 E ssA ms1 _ _ BC_NE (SOff 32 0) (SLit 0) HS1).
  2:{ intros Hc _. exfalso.
      rewrite branch_ne_U, (U_atom E 32%nat (sm_sink cx) ltac:(exact E32) ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc.
      apply negb_false_iff, Z.eqb_eq in Hc. lia. }
  intros _ HS1'.
  (* to `jal wrapper_fprintf` *)
  eapply (paj_run_call_plain_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx));
    [exact HEI | exact HS1' | exact HrB | exact HJ1 | |].
  { rewrite srm_pf_add_cond_mem, HmA. apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. unfold srm_pf_gsay in Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. lia. }
  intros ms2 mat2 HS2 HJ2 HF2 _ _.
  rewrite srm_pf_add_cond_mem, HmA in HF2. pose proof (srm_pf_frame_gsay _ _ _ HF2) as Em2. clear HF2.
  (* the wrapper's entry registers *)
  assert (Q1 : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + retoff)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms2 1%bv HS2), srm_pf_setpc_regs, R1.
    exact (codeptr_val E retoff HEI). }
  assert (Q10 : getr (ms_regs ms2) 10 = w64 (sm_sink cx)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms2 10%bv HS2), srm_pf_setpc_regs, R10.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32. }
  assert (Q11 : getr (ms_regs ms2) 11 = w64 (link_obj fi)).
  { rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms2 11%bv HS2), srm_pf_setpc_regs, R11.
    cbn [sv_denot]. rewrite Z.add_0_r, (HEI (A_OBJ fi) ltac:(unfold A_OBJ, A_TEXT, A_LIM, link_nobj in *; lia)).
    rewrite (lv_obj HV fi Hfi). reflexivity. }
  assert (QR : forall (r : bv 5) n, sr_get (ss_regs ssB) r = SOff n 0 -> (n < 32)%nat ->
    getr (ms_regs ms2) r = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat n))).
  { intros r n Hr Hn. rewrite (st_ok_restrict_reg SEGS (w_H W3) E _ ms2 r HS2), srm_pf_setpc_regs, Hr.
    cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (EREG n Hn). }
  assert (QK : forall r, In r SRM_PF_KEEP -> getr (ms_regs (restrict (w_H W3) ms2)) r = getr (ms_regs ms3) r).
  { intros r Hr. apply (regs_kept_of_st_ok SEGS E _ _ (ms_regs ms3) [w64 (sm_sink cx)] SRM_PF_KEEP HS2 HAE);
      [rewrite srm_pf_setpc_regs; exact HKB | exact Hr]. }
  cbn [ms_regs restrict] in QK.
  assert (QKR : srm_kregs (ms_regs ms2) (ms_regs ms3)).
  { unfold srm_kregs. repeat split; apply QK; cbn [In SRM_PF_KEEP]; repeat (first [left; reflexivity | right]). }
  rewrite (st_ok_restrict_mkst SEGS _ _ _ _ HS2 (eq_trans (srm_pf_setpc_resv ssB _) HrvB)), srm_pf_setpc_pc.
  rewrite (lv_sigma HV LS___interceptor_trampoline_fprintf).
  change (link_sigma LS___interceptor_trampoline_fprintf) with LA_W_FPRINTF.
  rewrite Em2, Em1. rewrite Em2, Em1 in HJ2.
  apply (HK (ms_regs ms2) _ Q1 Q10 Q11 QKR QR HJ2).
  - rewrite !(proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite !(proj2 (wvb_fds_fs _ _ _)). reflexivity.
Qed.

(* ==========================================================================
   3. The strings the two formats print
   ========================================================================== *)

(* the wrapper's window LFP_STK at s1 inside the caller's window LFP_STK at s1 *)
Lemma srm_pf_win : forall cx fpos X ly3 S3 W3 (ms3 : machine_state) md3,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  win_in (spZ (ms_regs ms3)) LFP_STK (srm_sp1 cx) LFP_STK.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HPRE HB.
  rewrite (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos X ly3 S3 W3 ms3 md3 HPRE HB).
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (_ & _ & _ & _ & Q5).
  assert (HL : LFP_STK = 5664) by reflexivity.
  unfold win_in. rewrite HL. lia.
Qed.

(* a .rodata literal [p, p + n) lies apart from the FILE block, a heap block of the state *)
Lemma srm_pf_lit_apart : forall ly S (W : world SEGS) m md f p n,
  AR SEGS B ly S W m md -> In (f, AMF_BLOCK) (ablocks B ly S) -> 0x10000 <= p -> p + n <= 0x654000 -> 0 < n ->
  apart p n f AMF_BLOCK.
Proof.
  intros ly S W m md f p n HAR Hin H1 H2 Hn.
  apply (blk_apart_img B LAWS ly S W m md f AMF_BLOCK p n HAR Hin ltac:(unfold AMF_BLOCK; lia)); [|exact Hn].
  intros a Ha. rewrite HSEGS. apply xf_tfib_hull. lia.
Qed.

(* the name, a %s argument of both formats *)
Lemma srm_pf_str_arg : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 s (r : word),
  srm_pre SK B cx -> srm_gspan_ok B cx ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) -> s <> [] ->
  r = w64 (srm_name cx) ->
  apf_arg_ok SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (sm_sink cx) r (APtr (map bv_unsigned s)) /\
  (length s <= 15)%nat.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 s r HPRE HSP HB HSA Hne ->.
  assert (Hkc : 0 <= LFP_STK <= REAC_CODE_EMIT_AK) by (rewrite REAC_CODE_EMIT_AK_val; vm_compute; split; discriminate).
  pose proof HSP as (HSPn & _).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK s
    HPRE HB (fun a H => H) Hkc HSA (fun a Ha => HSPn s a HSA Ha)) as (HNM & HNrt & HNlen & _ & HNf & _).
  pose proof (xf_acstr_range SEGS _ _ _ HNM) as Hnr.
  assert (Hun : bv_unsigned (w64 (srm_name cx)) = srm_name cx) by (apply srm_pf_w64; lia).
  split; [|exact HNlen].
  cbn [apf_arg_ok]. rewrite Hun, ea_map_rt, length_map.
  split; [|split; [exact HNM | split; [exact HNrt|]]].
  - apply ea_pos_of_nonul. exact (proj2 HNM).
  - unfold apart in *. lia.
Qed.

Lemma srm_pf_present_view : forall (H : word -> bool) mem a, apresent H mem a -> ard SEGS (mrestrict H mem) a <> None.
Proof. intros H mem a (Hh & b & Hb). unfold ard, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate. Qed.

(* the alias, the second %s of .str.9: the string the read left in F's buffer *)
Lemma srm_pf_alias_arg : forall cx fpos ly3 S3 W3 (ms3 : machine_state) md3 R (r : word),
  srm_pre SK B cx -> srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  srm_bufs cx fpos W3 (ms_mem ms3) R -> Z.of_nat (length (r_alias R)) < ALIAS_MAX ->
  r = w64 (srm_alias cx fpos) ->
  apf_arg_ok SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (sm_sink cx) r (APtr (map bv_unsigned (r_alias R))).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 R r HPRE HB HBUFS Hla ->.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HB)
    as (HF4 & HFc & HFal & HFapp & _ & HFin & HFa & _).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HB) as Hsp.
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Q1 & Q2 & Q3 & Q4 & Q5).
  pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & HSHp & _).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK HPRE HB
    (fun a H => H) ltac:(rewrite REAC_CODE_EMIT_AK_val; vm_compute; split; discriminate)) as (_ & Hin).
  pose proof (srm_jAR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx) AMF_BLOCK SRM_CID fpos HAR Hin HFin)
    as Hsep.
  rewrite HFa in Hsep. change (fs_frame_bytes SRM_CID) with 512 in Hsep.
  assert (Rq : req_size AMF_BLOCK = AMF_BLOCK) by reflexivity. rewrite Rq in Hsep.
  destruct HBUFS as (_ & HAL & _ & (junk & Ljunk & Hjunk) & Hsh).
  set (al := r_alias R) in *.
  assert (HSB : SRM_FB = 512) by exact SRM_FB_val.
  assert (Hal8 : srm_alias cx fpos = srm_F cx fpos + 96) by reflexivity.
  assert (Hal0 : 0 <= srm_alias cx fpos) by lia.
  assert (Hun : bv_unsigned (w64 (srm_alias cx fpos)) = srm_alias cx fpos) by (apply srm_pf_w64; lia).
  pose proof (Z.mod_pos_bound (srm_alias cx fpos + Z.of_nat (length al)) 8 ltac:(lia)) as Hm8.
  assert (Hal_mod : srm_alias cx fpos mod 8 = 0) by lia.
  (* a byte of the alias buffer is viewed *)
  assert (HV256 : forall b, srm_alias cx fpos <= b < srm_alias cx fpos + ALIAS_MAX ->
    ard SEGS (rdW W3 (ms_mem ms3)) b <> None).
  { intros b Hb. destruct Hjunk as ((_ & _ & Hjb) & _).
    unfold ard. replace b with (srm_alias cx fpos + Z.of_nat (Z.to_nat (b - srm_alias cx fpos))) by lia.
    rewrite (Hjb (Z.to_nat (b - srm_alias cx fpos)) ltac:(unfold ALIAS_MAX in *; lia)).
    destruct (nth_error junk (Z.to_nat (b - srm_alias cx fpos))) eqn:Ej; [discriminate|].
    apply nth_error_None in Ej. unfold ALIAS_MAX in *. lia. }
  cbn [apf_arg_ok]. rewrite Hun, ea_map_rt, length_map.
  split; [apply ea_pos_of_nonul; exact (proj2 HAL)|].
  split; [exact HAL|].
  split.
  - unfold astr_rt_ok. unfold ALIAS_MAX in Hla.
    split; [lia|]. split; [lia|].
    split; [unfold amem_range, in_app in *; unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|].
    split.
    { intros x Hx. exists 0. split; [|left; reflexivity].
      replace (shadow_of_addr SHADOW_OFF x) with (srm_SH cx fpos + (x / 8 - srm_F cx fpos / 8))
        by (unfold srm_SH, shadow_addr, shadow_of_addr; lia).
      apply Hsh. unfold srm_bufsh_off. right. lia. }
    split.
    { intros sa Hsa. apply srm_pf_present_view. apply HSHp.
      unfold shadow_addr in Hsa. unfold srm_SH, shadow_addr, SRM_SHN, SHADOW_OFF in *. lia. }
    split.
    { intros b Hb. apply HV256. unfold ALIAS_MAX. lia. }
    unfold apart_frame. left. rewrite Hsp. assert (HL : LFP_STK = 5664) by reflexivity. rewrite HL.
    rewrite REAC_SERVED_MARK_AK_val in Q2. lia.
  - unfold ALIAS_MAX in Hla. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold apart, AMF_BLOCK.
    clear - Hsep Hal8 Hla. unfold AMF_BLOCK in *. lia.
Qed.

(* ==========================================================================
   4. From the wrapper's return (at fx') to the post (at fx)
   ========================================================================== *)

(* a table string's bytes have the entry's view at both states (reac_served_markVours.v srm_xstr) *)
Lemma srm_pf_xstr {fxa fxb : YK11.FPState} : forall cx fpos XA XB lyA SA (WA : world SEGS) msA mdA
    lyB SB (WB : world SEGS) msB mdB s kbs tab gbs k0,
  srm_pre SK B cx ->
  srm_base fxa SK B cx fpos XA lyA SA WA msA mdA -> (forall a, XA a -> srm_E cx a) ->
  srm_base fxb SK B cx fpos XB lyB SB WB msB mdB -> (forall a, XB a -> srm_E cx a) ->
  srm_ent cx s kbs tab gbs k0 ->
  forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
  au64_at SEGS (rdW WA (ms_mem msA)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
  forall a, p <= a <= p + Z.of_nat (length n2) ->
  aview SEGS (w_H WB) (ms_mem msB) a = aview SEGS (w_H WA) (ms_mem msA) a.
Proof.
  intros cx fpos XA XB lyA SA WA msA mdA lyB SB WB msB mdB s kbs tab gbs k0 HPRE HBa HXa HBb HXb HENT
    i n2 ix p Hi Hp Hp64 a Ha.
  pose proof HENT as (_ & _ & _ & HNLK & _).
  pose proof HNLK as (_ & _ & _ & _ & _ & (Hnif & Hl80 & _) & _).
  assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  assert (HpB : au64_at SEGS (rdW WB (ms_mem msB)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { eapply srm_val_mem_move; [|exact Hp]. intros x Hx.
    rewrite (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fxb cx fpos XB lyB SB WB msB mdB _ HPRE HBb HXb)
      by (unfold NK_IF_NAME, NK_SIZE in *; lia).
    rewrite (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fxa cx fpos XA lyA SA WA msA mdA _ HPRE HBa HXa)
      by (unfold NK_IF_NAME, NK_SIZE in *; lia).
    reflexivity. }
  rewrite (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fxb cx fpos XB lyB SB WB msB mdB kbs tab i n2 ix p a
    HPRE HBb HXb HNLK Hi HpB Hp64 Ha).
  rewrite (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fxa cx fpos XA lyA SA WA msA mdA kbs tab i n2 ix p a
    HPRE HBa HXa HNLK Hi Hp Hp64 Ha).
  reflexivity.
Qed.

Lemma srm_pf_after : forall (retoff v : Z) (ssT : sstate) (stT : prun_status lsym)
    (cx : srmcx) fpos ly3 S3 (W3 : world SEGS) (ms3 : machine_state) md3 s kbs tab gbs k0 kbs1 (T : list Z)
    (fx' : YK11.FPState) ly4 S4 regs2 mem2 md2,
  sym_run_toN_pi pl_tpi FUEL SRM_CUT_RESTORE (srm_pf_ss retoff) = (ssT, stT) ->
  pi_plain_stop stT -> ss_pc ssT = SRM_CUT_RESTORE -> ss_resv ssT = None ->
  sr_get (ss_regs ssT) 21%bv = SLit v ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssT) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) SRM_PF_KEEP = true ->
  srm_restore_all SK B -> srm_pre SK B cx -> srm_gspan_ok B cx ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  srm_ent cx s kbs tab gbs k0 -> r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = v ->
  v = V_LEAVE_VLAN \/ v = V_LEAVE_HOST ->
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs ->
  Z.of_nat (length T) <= MARK_LINE_MAX ->
  @BoxBase.fxr fx fx' ->
  srm_base fx' SK B cx fpos (srm_E cx) ly4 S4 W3
    (@mkst fx' regs2 (Z_to_bv 64 (BASE + retoff)) mem2 (seg_rom SEGS)) md2 ->
  akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 mem2 (srm_sp1 cx - LFP_STK) (srm_sp1 cx)
    (fun a => sm_sink cx <= a < sm_sink cx + AMF_BLOCK) ->
  amemfile_k SEGS (rdW W3 mem2) (sm_sink cx) (k0 + Z.of_nat (length T)) ->
  SRr SEGS W3 (mkCfg (@mkst fx' regs2 (Z_to_bv 64 (BASE + retoff)) mem2 (seg_rom SEGS)) md2)
    (srm_post fx SK B cx).
Proof.
  intros retoff v ssT stT cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 kbs1 T fx' ly4 S4 regs2 mem2 md2
    HrT HstT HpcT HrvT H21T HKT HREST HPRE HSP HB HENT Hrc Hdec Hv HKERN HMK HTl Hfxr HB4 HAK HMF2.
  pose proof HENT as (Hmk0 & _).
  assert (Hkc : 0 <= LFP_STK <= REAC_CODE_EMIT_AK) by (rewrite REAC_CODE_EMIT_AK_val; vm_compute; split; discriminate).
  pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0. destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _).
  pose proof HB4 as HB5. unfold srm_base in HB5. cbv zeta in HB5. destruct HB5 as (_ & _ & _ & _ & _ & HJ4 & _).
  pose proof (srm_jAR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  pose proof (srm_jAR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
  cbn [ms_mem mkst] in HAR4.
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK HPRE HB
    (fun a H => H) Hkc Hmk0) as (_ & (Hin3 & _) & _ & _ & Hmf).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos (srm_E cx) ly4 S4 W3 _ md2 LFP_STK HPRE HB4
    (fun a H => H) Hkc Hmk0) as (_ & (Hin4 & _) & _).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK HPRE HB
    (fun a H => H) Hkc) as (_ & Hinf).
  (* the marks across the wrapper *)
  assert (HMK4 : amarks_at SEGS (rdW W3 mem2) (srm_mk cx) gbs).
  { eapply (xfer_amarks B LAWS ly3 S3 W3 (ms_mem ms3) W3 mem2 ly4 S4 md2 _ _ _ (srm_mk cx) gbs HAK HAR4 Hin3 Hin4);
      [|exact HMK].
    intros a Ha HF. unfold apart in Hmf. lia. }
  (* the kernel across the wrapper *)
  assert (HKERN4 : srm_kern (rdW W3 mem2) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1).
  { eapply (xfer_kern B HSEGS TB ly3 S3 W3 (ms_mem ms3) W3 mem2 _ _ _ kbs kbs1 tab _ _ 1 HAK).
    - intros a Ha HF.
      assert (Hg : apart LA_G_NL NK_SIZE (sm_sink cx) AMF_BLOCK).
      { apply (blk_apart_img B LAWS ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx) AMF_BLOCK LA_G_NL NK_SIZE
          HAR3 Hinf ltac:(unfold AMF_BLOCK; lia)); [|unfold NK_SIZE; lia].
        intros b Hb. exact (proj1 (xfer_gnl_img B HSEGS TB b Hb)). }
      unfold apart in Hg. lia.
    - pose proof (srm_pf_xstr (fxa := fx) (fxb := fx') cx fpos (srm_E cx) (srm_E cx) ly3 S3 W3 ms3 md3 ly4 S4 W3 _ md2
        s kbs tab gbs k0 HPRE HB (fun a H => H) HB4 (fun a H => H) HENT) as HX.
      cbn [ms_mem mkst] in HX. exact HX.
    - exact HKERN. }
  (* the tail at fx', lifted back to fx *)
  unfold srm_post. eapply (srr_apostF_lift SK SEGS B fx fx'); [exact Hfxr|].
  exact (srm_leave_tail (fx := fx') SK B LAWS retoff v ssT stT cx fpos ly4 S4 W3
    (@mkst fx' regs2 (Z_to_bv 64 (BASE + retoff)) mem2 (seg_rom SEGS)) md2 s kbs tab gbs k0 kbs1
    (k0 + Z.of_nat (length T)) HrT HstT HpcT HrvT H21T HKT (HREST fx') HPRE HSP eq_refl HB4 HENT Hrc Hdec Hv
    HKERN4 HMK4 HMF2 ltac:(lia)).
Qed.

End a.

About srm_pfv_ok. About srm_pf_head. About srm_pf_win. About srm_pf_lit_apart. About srm_pf_str_arg.
About srm_pf_alias_arg. About srm_pf_xstr. About srm_pf_after. About srm_leave_tail. About srm_fprintf_step.
About link_vf_FF_of_c. About afmt_at. About apf_args_asan. About apf_args_slack. About pf_text_of_fit.
About pf_text_length. About pc_lds_link. About pf_parse_bytes. About ea_map_rt. About ea_pos_of_nonul.
Print Assumptions srm_pf_head. Print Assumptions srm_pf_after. Print Assumptions srm_pf_alias_arg.
