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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v; 356 of its 403 lines of code are new or changed and 349 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markVmark.v, with its module names changed; 121 of its 160 lines of code are new or changed and 364 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the segment of its walk from the VVLAN cut (+0x510, the
   verdict V_LEAVE_VLAN) to the RESTORE cut (+0x2cc), against the cut interface lib/A/Prog/reac_served_markDefs.v.

   The code (listing (internal path) (internal record, sha256 5943815fc488)):
     +0x510..+0x518  a0 := g_say; bnez a0 (the FILE: sink <> 0, so the stderr fallback +0x51c is not reached)
     +0x538..+0x540  a1 := 0x21500 (.str.8), a2 := s4 (the name)
     +0x544          jal wrapper_fprintf (0x43084)
     +0x548          s5 := 2
     +0x54c          j +0x2cc
   That is link_spec.v's mark_core in its V_LEAVE_VLAN arm: the answer is 2, the marks and the kernel as the read
   left them, and the FILE holds the line `.str.8` with the name, at most 115 + 15 bytes more.

   srm_vvlan : srm_restore_all -> srm_vvlan_obl: the head (reac_served_markPfArm.v srm_pf_head over the two engine
   runs below), the call (reac_served_markPfStep.v srm_fprintf_step, the format family from LinkWalkMkFmt.v
   link_vf_FF_of_c), the tail (reac_served_markPfArm.v srm_pf_after over the run below).

   Proves no function (kind: segment lemma of reac_served_mark's walk: the VVLAN cut to RESTORE). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import reac_served_markPfArm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ---- .str.8: "reac-pw: [%s] is a VLAN the host made ..." ---- *)
Definition FMT_8 : list Z := map bv_unsigned S_STR8.
Definition PS_8 : list pf_piece := Eval vm_compute in match pf_parse FMT_8 with Some ps => ps | None => [] end.
Lemma PS_8_ok : pf_parse FMT_8 = Some PS_8. Proof. vm_compute. reflexivity. Qed.
Lemma PS_8_lds : forallb pc_lds PS_8 = true. Proof. vm_compute. reflexivity. Qed.
Lemma PS_8_convs : convs PS_8 = [1%nat]. Proof. vm_compute. reflexivity. Qed.
Lemma PS_8_lits : pf_lits PS_8 = 115. Proof. vm_compute. reflexivity. Qed.
Lemma FMT_8_len : length FMT_8 = 117%nat. Proof. vm_compute. reflexivity. Qed.
Lemma FMT_8_ne : FMT_8 <> []. Proof. vm_compute. discriminate. Qed.

(* ---- the engine runs: the cut to `bnez a0`, then to `jal wrapper_fprintf`; from the return to RESTORE ---- *)
Definition VV_ssA : sstate := Eval vm_compute in fst (sym_runN_pi link_tpi FUEL (srm_pfv_ss SRM_CUT_VVLAN)).
Lemma VV_A_ok : sym_runN_pi link_tpi FUEL (srm_pfv_ss SRM_CUT_VVLAN) =
  (VV_ssA, PRS_stopped (SR_branch BC_NE (SOff 32 0) (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition VV_ssB : sstate :=
  Eval vm_compute in fst (sym_runN_pi link_tpi FUEL (add_cond VV_ssA (mkAC BC_NE (SOff 32 0) (SLit 0)))).
Lemma VV_B_ok : sym_runN_pi link_tpi FUEL (add_cond VV_ssA (mkAC BC_NE (SOff 32 0) (SLit 0))) =
  (VV_ssB, PRS_call LS___interceptor_trampoline_fprintf).
Proof. vm_compute. reflexivity. Qed.
Definition VV_RET : Z := SRM_CUT_VVLAN + 0x38.
Definition VV_ssT : sstate := Eval vm_compute in fst (sym_run_toN_pi link_tpi FUEL SRM_CUT_RESTORE (srm_pf_ss VV_RET)).
Definition VV_stT : prun_status lsym :=
  Eval vm_compute in snd (sym_run_toN_pi link_tpi FUEL SRM_CUT_RESTORE (srm_pf_ss VV_RET)).
Lemma VV_T_ok : sym_run_toN_pi link_tpi FUEL SRM_CUT_RESTORE (srm_pf_ss VV_RET) = (VV_ssT, VV_stT).
Proof. vm_compute. reflexivity. Qed.

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
(* wrapper_fprintf 0x43084 on link's memory FILE, at every FP state (LinkVfInst.v link_afprintf_contract) *)
Hypothesis HFP : forall fx' : YK11.FPState,
  @afprintf_mf_realizes fx' rc SEGS B link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LA_GOT_GUARD LA_GUARD
    LA_W_FPRINTF.

Theorem srm_vvlan : srm_restore_all SK B -> srm_vvlan_obl fx SK B.
Proof.
  intros HREST cx fpos ly3 S3 W3 ms3 md3 HPRE HSP HG.
  unfold srm_gi_vvlan, srm_gi_arm in HG.
  destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & Hpc & HENT & Hrc & Hdec & R23 & R24 & HKERN & HBUFS & HMK & HMF
    & HB).
  pose proof HENT as (Hmk0 & HSA & Hsne & _ & _ & _ & _ & Hk0).
  pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
  pose proof (srm_jAR SK B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hkc : 0 <= LFP_STK <= REAC_CODE_EMIT_AK)
    by (rewrite REAC_CODE_EMIT_AK_val; vm_compute; split; discriminate).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK HPRE HB
    (fun a H => H) Hkc) as (_ & Hin).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 LFP_STK HPRE HB
    (fun a H => H) Hkc) as HPOL.
  destruct HPOL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H8c & H8rt & _).
  pose proof (srm_pf_win SK B LAWS TB RELRO_IMG HSEGS cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HB) as HW.
  destruct (srm_pf_str_arg SK B LAWS TB RELRO_IMG HSEGS cx fpos ly3 S3 W3 ms3 md3 s (w64 (srm_name cx))
    HPRE HSP HB HSA Hsne eq_refl) as (Harg & Hslen).
  (* the text the call prints *)
  set (sZ := map bv_unsigned s).
  assert (Hfit : args_fit (convs PS_8) [APtr sZ]) by (rewrite PS_8_convs; cbn; exact I).
  destruct (pf_text_of_fit PS_8 _ PS_8_lds Hfit) as (T & HT).
  pose proof (pf_text_length PS_8 _ T PS_8_lds HT) as HL. rewrite PS_8_lits in HL. cbn [pa_lens pa_len] in HL.
  unfold sZ in HL. rewrite length_map in HL.
  assert (HkT : k0 + Z.of_nat (length T) <= AMF_BUFSIZ) by (unfold MARK_LINE_MAX in Hk0; lia).
  assert (HT31 : Z.of_nat (length T) < 2 ^ 31 - 1) by lia.
  assert (HTl : Z.of_nat (length T) <= MARK_LINE_MAX) by (unfold MARK_LINE_MAX; lia).
  (* the format *)
  assert (H8c' : acstr_at SEGS (rdW W3 (ms_mem ms3)) (link_obj 52) (map (Z_to_bv 8) FMT_8))
    by (unfold FMT_8; rewrite ea_map_rt; exact H8c).
  assert (H8rt' : astr_rt_ok SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (link_obj 52) (map (Z_to_bv 8) FMT_8))
    by (unfold FMT_8; rewrite ea_map_rt; exact H8rt).
  assert (H8ap : apart (link_obj 52) (Z.of_nat (length FMT_8) + 8) (sm_sink cx) AMF_BLOCK).
  { rewrite FMT_8_len. apply (srm_pf_lit_apart B LAWS HSEGS ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx));
      [exact HAR | exact Hin | cbv [link_obj]; lia | cbv [link_obj]; lia | lia]. }
  pose proof (afmt_at SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (link_obj 52) FMT_8 LFP_STK (srm_sp1 cx)
    (sm_sink cx) HW (pf_parse_bytes FMT_8 PS_8 PS_8_ok) H8c' H8rt' H8ap) as HFMT.
  (* +0x510 .. +0x544 *)
  eapply (srm_pf_head SK B LAWS HV TB RELRO_IMG HSEGS SRM_CUT_VVLAN VV_RET 52%nat VV_ssA VV_ssB cx fpos ly3 S3 W3
    ms3 md3 _ VV_A_ok VV_B_ok eq_refl eq_refl eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold link_nobj; lia) ltac:(vm_compute; reflexivity) HPRE HB Hpc).
  intros regsT md1 Q1 Q10 Q11 QKR QR HJ1 Hfd1 Hfs1.
  assert (Q12 : getr regsT (Z_to_bv 5 12) = w64 (srm_name cx)).
  { rewrite (QR (Z_to_bv 5 12) 20%nat ltac:(vm_compute; reflexivity) ltac:(lia)).
    replace (Z_to_bv 5 (Z.of_nat 20)) with (20%bv : bv 5) by (apply bv_eq; reflexivity). exact R20. }
  (* the argument words a2 .. a7 and the family *)
  set (rsT := map (fun i => getr regsT (Z_to_bv 5 (10 + i))) [2; 3; 4; 5; 6; 7]).
  assert (Hargs : apf_args_ok SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (sm_sink cx) rsT [APtr sZ]).
  { unfold rsT. cbn [map apf_args_ok]. split; [|exact I].
    change (Z_to_bv 5 (10 + 2)) with (Z_to_bv 5 12). rewrite Q12. exact Harg. }
  destruct (apf_args_slack SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (sm_sink cx) rsT [APtr sZ] Hargs)
    as (Hsl & Ham).
  assert (HFF : link_vf_FF (aview SEGS (w_H W3) (ms_mem ms3)) (vmf_out LFP_STK (srm_sp1 cx) (sm_sink cx))
    (link_obj 52) (map (argZ regsT) [2; 3; 4; 5; 6; 7]) T).
  { replace (map (argZ regsT) [2; 3; 4; 5; 6; 7]) with (map (fun r : word => bv_unsigned r) rsT)
      by (unfold rsT; rewrite map_map; reflexivity).
    apply (link_vf_FF_of_c (aview SEGS (w_H W3) (ms_mem ms3)) (vmf_out LFP_STK (srm_sp1 cx) (sm_sink cx))
      (link_obj 52) FMT_8 PS_8 [APtr sZ] T (map (fun r : word => bv_unsigned r) rsT) HFMT PS_8_ok
      (pc_lds_link PS_8 PS_8_lds)
      (apf_args_asan SEGS (ms_regs ms3) LFP_STK (rdW W3 (ms_mem ms3)) (sm_sink cx) rsT [APtr sZ] LFP_STK
        (srm_sp1 cx) HW Hargs) HT).
    - cbv [link_obj]. lia.
    - rewrite FMT_8_len. cbv [link_obj]. lia.
    - exact Hsl.
    - exact FMT_8_ne.
    - exact Ham. }
  (* +0x544: the call *)
  apply (srm_fprintf_step SK B LAWS TB RELRO_IMG HSEGS HFP cx fpos ly3 S3 W3 ms3 md3 regsT md1 (link_obj 52) k0 T _
    HPRE HB HJ1 Hfd1 Hfs1 QKR Q10 Q11).
  - rewrite Q1. apply ret_ok_codeptr_v; [unfold VV_RET, SRM_CUT_VVLAN, AF_reac_served_mark; lia | reflexivity].
  - unfold raZ. rewrite Q1. pose proof pa_B_ok as (HB0' & HB1' & _). pose proof pa_base_lo as HBL.
    rewrite unsigned_lit_small by (unfold VV_RET, SRM_CUT_VVLAN, AF_reac_served_mark; lia).
    unfold VV_RET, SRM_CUT_VVLAN, AF_reac_served_mark. lia.
  - exact HMF.
  - exact HkT.
  - exact HFF.
  - exact HT31.
  - (* +0x548 .. RESTORE, at the fx' the wrapper returned *)
    intros fx' ly4 S4 regs2 mem2 md2 Hfxr HB4 _ HAK HMF2 _.
    rewrite Q1 in HB4 |- *.
    exact (srm_pf_after (fx := fx) SK B LAWS TB RELRO_IMG HSEGS VV_RET V_LEAVE_VLAN VV_ssT VV_stT cx fpos ly3 S3 W3 ms3 md3
      s kbs tab gbs k0 kbs1 T fx' ly4 S4 regs2 mem2 md2 VV_T_ok I eq_refl eq_refl ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) HREST HPRE HSP HB HENT Hrc Hdec (or_introl eq_refl) HKERN HMK HTl Hfxr HB4
      HAK HMF2).
Qed.

End a.

About srm_vvlan.
Print Assumptions srm_vvlan.
