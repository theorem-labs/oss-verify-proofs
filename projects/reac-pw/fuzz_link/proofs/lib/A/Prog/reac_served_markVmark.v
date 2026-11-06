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
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the segment of its walk from the VMARK cut (+0x4b0, the
   verdict V_MARK; reac_served_markDefs.v `srm_gi_vmark`) to the WRET cut (+0x4c0, `srm_gi_wret`), against the cut
   interface lib/A/Prog/reac_served_markDefs.v.

   The code (listing (internal path) (internal record, sha256 5943815fc488) lines 304-308):
     +0x4b0..+0x4b4  a1 := 0x213c0 (.str.4, "reac-pw:served")
     +0x4b8          a0 := s4 (the name)
     +0x4bc          jal reac_link_alias_write (0x88f54)      (aleaf_rd, at the entry's FP state)
     +0x4c0          beqz a0                                   = the WRET cut
   That is link_spec.v's mark_core in its V_MARK arm up to the write: `write_lib tab (Some s) (Some S_SERVED)
   (r_reqs R) (r_state R)` = `srm_Wr s tab R`, which the WRET cut names.

   No instruction of this segment reads or writes memory, so the plain engine (LinkWalkSide.v Section pe) runs it
   over no region at all.

   The pieces:
   - svm_call_pre: reac_link_alias_write's apre (srm_call_apre, K 8560, SIDE [(3,1); (9,1)], its write set the
     g_nl prefix, a part of this call's), its read set (the name, the literal, the live table strings: each is an
     `akb` byte of the entry, Defs' srm_gspan_ok) and its Pre at the cut's memory (the kernel kbs1 the read left,
     the interface table, g_nl's shadow, errno, the name, the literal and its strlen slack).
   - svm_kstate: the kernel the read left reads back as `r_state R` and `r_reqs R`, so the writer's Post is at
     `srm_Wr s tab R` (the plain lane's `kstate_of` pattern).
   - srm_vmark: the run to the call, `HWR` under SRr_bind, srm_call_back at the same FP state (the callee is
     `aleaf_rd`), and the WRET cut from the writer's Post.

   Proves no function (kind: segment lemma of reac_served_mark's walk: the VMARK cut to WRET). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c nl_talk_c reac_link_alias_write_c reac_served_mark_c
reac_served_markDefs reac_served_markUniq reac_served_markKit reac_served_markKitAt reac_served_markXfer
reac_served_markEmitArgs reac_served_markPf reac_served_markWret.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. link_spec: the kernel the read left, read back as the read's own kstate
   ========================================================================== *)

Lemma svm_read_chunks : forall tab nm kc ac reqs K,
  k_chunks (r_state (read_core tab nm kc ac reqs K)) = k_chunks K /\
  k_end (r_state (read_core tab nm kc ac reqs K)) = k_end K.
Proof.
  intros tab nm kc ac reqs K. unfold read_core.
  destruct nm as [s|]; [|cbn [r_state]; split; reflexivity].
  destruct (Nat.eqb (length s) 0); [cbn [r_state]; split; reflexivity|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [r_state]; split; reflexivity|].
  cbn [r_state]. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [snd fst k_chunks k_end]; split; reflexivity|].
  destruct (negb (k_send K =? 0)); [cbn [snd fst k_chunks k_end]; split; reflexivity|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; cbn [snd fst k_chunks k_end]; split; reflexivity.
Qed.

Lemma svm_kstate_of : forall kbs K, nk_chunks kbs = k_chunks K -> nk_next kbs = Z.of_nat (k_next K) ->
  nk_end_errno kbs = k_end K -> nk_socket_errno kbs = k_sock K -> nk_send_errno kbs = k_send K ->
  nk_kstate kbs = K.
Proof.
  intros kbs K H1 H2 H3 H4 H5. unfold nk_kstate. rewrite H1, H2, H3, H4, H5, Nat2Z.id.
  destruct K; reflexivity.
Qed.

(* ==========================================================================
   2. The engine at this segment's one cut
   ========================================================================== *)

Definition SVM_CALL_RA : Z := SRM_CUT_WRET.         (* the return address of reac_link_alias_write *)
Lemma SVM_CALL_RA_val : SVM_CALL_RA = 30876. Proof. reflexivity. Qed.

Section a. Context {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HV : LinkVals (L := link_listing).
Hypothesis TB : PcapSyms B.                        (* instance AD2l.PcapB_syms *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = tfibsegs.
(* the callee: reac_link_alias_write, at every FP state (it returns at the one it was called in) *)
Hypothesis HWR : forall fx' : YK11.FPState, @reac_link_alias_write_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

(* the kernel the read left is the read's own kstate and request list *)
Lemma svm_kstate : forall m s kbs tab kbs1,
  nlk_wf kbs ->
  srm_kern m kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  nk_kstate kbs1 = r_state (srm_R s kbs tab) /\ nk_sent kbs1 = r_reqs (srm_R s kbs tab).
Proof.
  intros m s kbs tab kbs1 HWF (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  destruct (svm_read_chunks tab (Some s) KIND_CAP ALIAS_MAX (nk_sent kbs) (nk_kstate kbs)) as (HC & HE).
  unfold srm_R, read_lib in *.
  split; [|exact K10].
  apply svm_kstate_of.
  - rewrite K3, HC. cbn [nk_kstate k_chunks]. reflexivity.
  - exact K7.
  - rewrite K4, HE. cbn [nk_kstate k_end]. reflexivity.
  - exact K8.
  - exact K9.
Qed.

(* ==========================================================================
   3. reac_link_alias_write's apre, read set and Pre at the call
   ========================================================================== *)

Lemma svm_call_pre {fx : YK11.FPState} : forall (cx : srmcx) fpos ly3 S3 W3 (ms : machine_state) md
    s kbs tab kbs1,
  srm_pre SK B cx -> srm_gspan_ok B cx -> srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms md ->
  srm_mk cx <> 0 -> astr_arg SEGS (srm_m0 cx) (srm_name cx) (Some s) ->
  amk_nlk_ok SEGS (srm_m0 cx) kbs tab 2 ->
  srm_kern (rdW W3 (ms_mem ms)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  getr (ms_regs ms) 10 = w64 (srm_name cx) -> getr (ms_regs ms) 11 = w64 LA_S_SERVED ->
  getr (ms_regs ms) 1 = w64 (BASE + SVM_CALL_RA) ->
  apre SK SEGS PCAP_RLO PCAP_RHI B REAC_LINK_ALIAS_WRITE_AK 0 REAC_LINK_ALIAS_WRITE_ASIDE
    (reac_link_alias_write_awr (ms_regs ms) (rdW W3 (ms_mem ms)))
    (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms) md (sm_k cx) (ms_regs ms) /\
  (forall a, reac_link_alias_write_ard SEGS (ms_regs ms) (rdW W3 (ms_mem ms)) a ->
     akb SEGS B ly3 S3 (spZ (ms_regs ms) - REAC_LINK_ALIAS_WRITE_AK) (spZ (ms_regs ms)) a) /\
  reac_link_alias_write_apre SEGS B (ms_regs ms) (rdW W3 (ms_mem ms)).
Proof.
  intros cx fpos ly3 S3 W3 ms md s kbs tab kbs1 HPRE HGSP HB Hmk0 HSA HNLK HKERN R10 R11 R1.
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  assert (HKc : 0 <= REAC_LINK_ALIAS_WRITE_AK <= REAC_CODE_EMIT_AK)
    by (rewrite REAC_LINK_ALIAS_WRITE_AK_val, REAC_CODE_EMIT_AK_val; lia).
  pose proof (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Hsp16 & Hspc & Hsp47 & Hsp1 & Hsp1m).
  pose proof (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md HPRE HB) as Hsp.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HKv : REAC_LINK_ALIAS_WRITE_AK = 8560) by exact REAC_LINK_ALIAS_WRITE_AK_val.
  assert (HKm : REAC_SERVED_MARK_AK = 9504) by exact REAC_SERVED_MARK_AK_val.
  (* the two arguments as aarg reads them *)
  assert (HA0 : aarg (ms_regs ms) 0 = srm_name cx)
    by (apply (smk_aarg _ 0 10); [apply bv_eq; reflexivity | exact R10 | unfold srm_name; apply smk_aarg_range]).
  assert (HA1 : aarg (ms_regs ms) 1 = LA_S_SERVED)
    by (apply (smk_aarg _ 1 11); [apply bv_eq; reflexivity | exact R11 | unfold LA_S_SERVED; lia]).
  (* the window of this callee sits inside the caller's *)
  assert (HFR : forall q n, apart_frame (sm_regs cx) REAC_SERVED_MARK_AK q n ->
            apart_frame (ms_regs ms) REAC_LINK_ALIAS_WRITE_AK q n).
  { intros q n H. unfold apart_frame, srm_sp in *. rewrite Hsp. unfold srm_sp1 in *. lia. }
  (* the name at the cut *)
  assert (HNAKB : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
    by (intros a Ha; exact (proj1 HGSP s a HSA Ha)).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md REAC_LINK_ALIAS_WRITE_AK s
              HPRE HB HXE HKc HSA HNAKB) as (NC & NRT & NL & NG & NF & NE & NM).
  pose proof NRT as (N0 & N31 & NAM & NRA & NHV & NTL & NFR).
  (* the literal .str.4 at the cut *)
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md REAC_LINK_ALIAS_WRITE_AK
                HPRE HB HXE HKc) as (_ & _ & _ & _ & PSV & PSVr & _).
  pose proof PSVr as (V0 & V31 & VAM & VRA & VHV & VTL & VFR).
  assert (HSL : length S_SERVED = 14%nat) by reflexivity.
  (* errno and g_nl's shadow at the cut *)
  destruct (srm_errno_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md REAC_LINK_ALIAS_WRITE_AK
              HPRE HB HKc) as (He1 & He2 & He3 & He4 & He5 & He6 & _).
  destruct (srm_gnl_sh_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md HB) as (Hg1 & Hg2).
  (* the kernel at the cut *)
  pose proof HKERN as (Hnlk1 & Hwf1 & Hch1 & Hend1 & Hnif1 & Hift1 & _ & _ & _ & _ & _ & Hopen1 & _ & Hoc1 & Hb1).
  pose proof HNLK as (Hnlk0 & Hwf0 & Hopen0 & Hop2 & Hcl2 & Hift0 & _ & _).
  (* a table entry at the cut is the entry's *)
  assert (HTE : forall i n2 ix, nth_error tab i = Some (n2, ix) ->
     exists p0, au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 /\
       au64_at SEGS (rdW W3 (ms_mem ms)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 /\
       acstr_at SEGS (srm_m0 cx) p0 n2 /\ p0 <> 0 /\ 0 <= p0 /\ p0 + Z.of_nat (length n2) + 1 <= 2 ^ 64).
  { intros i n2 ix Hi. pose proof Hift0 as (_ & Hl & Ht).
    destruct (Ht i n2 ix Hi) as (_ & p0 & Hp0 & Hp00 & Hc0 & _).
    assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    exists p0. split; [exact Hp0|]. split.
    - eapply srm_val_mem_move; [|exact Hp0]. intros x Hx.
      rewrite (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md x HPRE HB HXE)
        by (unfold NK_IF_NAME, NK_SIZE in *; lia).
      reflexivity.
    - split; [exact Hc0|]. split; [exact Hp00|].
      destruct Hc0 as ((H0 & H1 & _) & _). rewrite length_app in H1. cbn [length] in H1. lia. }
  (* the facts of an in-range table entry at the cut *)
  assert (HTF : forall i n2 ix p0, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (srm_m0 cx) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 ->
     au64_at SEGS (rdW W3 (ms_mem ms)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p0 ->
     acstr_at SEGS (srm_m0 cx) p0 n2 -> 0 <= p0 < 2 ^ 64 ->
     acstr_at SEGS (rdW W3 (ms_mem ms)) p0 n2 /\
     astr_rt_ok SEGS (ms_regs ms) REAC_LINK_ALIAS_WRITE_AK (rdW W3 (ms_mem ms)) p0 n2 /\
     achk SEGS (rdW W3 (ms_mem ms)) p0 (Z.of_nat (length n2) + 1) /\
     apart_gnl LA_G_NL p0 (Z.of_nat (length n2) + 1) /\
     apart (as_errno B) 4 p0 (Z.of_nat (length n2) + 1) /\ 0 < p0).
  { intros i n2 ix p0 Hi Hp0 Hp3 Hc0 Hpr.
    assert (Hspan2 : forall a, p0 <= a <= p0 + Z.of_nat (length n2) ->
              akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
      by (intros a Ha; exact (proj2 HGSP kbs tab i n2 ix p0 a Hnlk0 Hift0 Hi Hp0 Hc0 Ha)).
    destruct (srm_table_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md REAC_LINK_ALIAS_WRITE_AK
                kbs tab i n2 ix p0 HPRE HB HXE HKc HNLK Hi Hp3 Hpr Hspan2)
      as (Htc & Htrt & Htchk & _ & Htgnl & Hterr & _ & _).
    split; [exact Htc|]. split; [exact Htrt|]. split; [exact Htchk|]. split; [exact Htgnl|].
    split; [exact Hterr|]. exact (proj1 Htrt). }
  split; [|split].
  (* ---- apre ---- *)
  - apply (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md
             REAC_LINK_ALIAS_WRITE_AK REAC_LINK_ALIAS_WRITE_ASIDE _ HPRE HB HXE HKc).
    + rewrite R1. apply ret_ok_codeptr_v;
        unfold SVM_CALL_RA, SRM_CUT_WRET, AF_reac_served_mark; lia.
    + unfold raZ. rewrite R1. pose proof pa_base_lo as HBL. pose proof pa_B_ok as (HB1 & HB2 & _).
      rewrite unsigned_lit_small; unfold SVM_CALL_RA, SRM_CUT_WRET, AF_reac_served_mark in *; lia.
    + intros cd Hcd. unfold REAC_LINK_ALIAS_WRITE_ASIDE in Hcd. cbn [In] in Hcd.
      destruct Hcd as [<- | [<- | []]].
      * exists 2. split; [unfold REAC_SERVED_MARK_ASIDE; cbn [In]; tauto | cbn; lia].
      * exists 1. split; [unfold REAC_SERVED_MARK_ASIDE; cbn [In]; tauto | cbn; lia].
    + intros a (r & Hin & Hr). unfold reac_link_alias_write_awr in Hin. cbn [In] in Hin.
      destruct Hin as [<- | []]. left. unfold srm_E, srm_wr, reac_served_mark_awr.
      exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact Hr].
  (* ---- the read set ---- *)
  - intros a [(Hn0' & s' & Hc' & Ha) | [(Hl0 & s' & Hc' & Ha) |
      (bs & tab' & i & n2 & ix & p & Hbs & Ht' & Hi & Hp & Hc & Ha)]].
    + rewrite HA0 in Hc', Ha.
      pose proof (acstr_at_unique SEGS _ _ _ _ Hc' NC) as Es. subst s'.
      apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md
               REAC_LINK_ALIAS_WRITE_AK a HPRE HB HKc).
      apply HNAKB. unfold srm_gspan.
      pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)). lia.
    + rewrite HA1 in Hc', Ha.
      pose proof (acstr_at_unique SEGS _ _ _ _ Hc' PSV) as Es. subst s'. rewrite HSL in Ha.
      apply (srm_lit_akb B HSEGS TB ly3 S3 _ _ a). unfold srm_lit_byte. right. left.
      cbn [Z.of_nat] in Ha. lia.
    + pose proof (anlk_at_unique SEGS _ _ _ _ Hbs Hnlk1) as Eb. subst bs.
      pose proof (aiftab_at_unique SEGS _ _ _ _ Ht' Hift1) as Et. subst tab'.
      destruct (HTE i n2 ix Hi) as (p0 & Hp0 & Hp03 & Hc0 & Hp00 & Hp0lo & Hp0hi).
      assert (Hpr : 0 <= p < 2 ^ 64)
        by (destruct Hc as ((H0 & H1 & _) & _); rewrite length_app in H1; cbn [length] in H1; lia).
      pose proof (srm_au64_unique SEGS _ _ _ _ Hp Hp03) as Hmod.
      rewrite (Z.mod_small p) in Hmod by exact Hpr. rewrite (Z.mod_small p0) in Hmod by lia. subst p0.
      apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms md
               REAC_LINK_ALIAS_WRITE_AK a HPRE HB HKc).
      apply (proj2 HGSP kbs tab i n2 ix p a Hnlk0 Hift0 Hi Hp0 Hc0). unfold srm_gspan.
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length n2)) 8 ltac:(lia)). lia.
  (* ---- the Pre ---- *)
  - exists kbs1, tab, (Some s), (Some S_SERVED).
    rewrite HA0, HA1.
    split; [exact Hnlk1|]. split; [exact Hwf1|]. split; [exact Hopen1|].
    split; [lia|]. split; [lia|]. split; [exact Hift1|].
    split; [exact Hg1|]. split; [exact Hg2|].
    split; [split; [exact He1|]; split; [exact He2|]; split; [exact He3|]; split; [exact He5 | exact He6]|].
    split; [split; [exact (proj1 HSA) | exact NC]|].
    split; [split; [unfold LA_S_SERVED; lia | exact PSV]|].
    (* the table strings *)
    split.
    { intros i n2 ix p Hi Hp.
      destruct (HTE i n2 ix Hi) as (p0 & Hp0 & Hp03 & Hc0 & Hp00 & Hp0lo & Hp0hi).
      pose proof (srm_au64_unique SEGS _ _ _ _ Hp Hp03) as Hmod.
      rewrite (Z.mod_small p0) in Hmod by lia.
      destruct (Z.eq_dec (p mod 2 ^ 64) p) as [Hq0 | Hq0].
      - assert (Ep : p = p0) by lia. subst p.
        destruct (HTF i n2 ix p0 Hi Hp0 Hp03 Hc0 ltac:(lia)) as (_ & Htrt & Htchk & Htgnl & Hterr & Ht0).
        split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Htrt)))))) |].
        split; [exact Htgnl|]. split; [exact Hterr|].
        intros _. split; [exact Ht0|].
        split; [| split; [exact Htchk | exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Htrt))))))]].
        pose proof (proj1 (proj2 Htrt)) as Hn31. lia.
      - (* p is not in [0, 2 ^ 64): every clause is trivial or guarded *)
        pose proof (Z.mod_pos_bound p (2 ^ 64) ltac:(lia)) as Hmb.
        assert (Hfar : p < 0 \/ 2 ^ 64 <= p) by lia.
        assert (Hsp64 : spZ (ms_regs ms) < 2 ^ 64)
          by (unfold spZ; pose proof (bv_unsigned_in_range 64 (getr (ms_regs ms) 2)) as Hr;
              change (bv_modulus 64) with (2 ^ 64) in Hr; lia).
        assert (Hn2 : 0 <= Z.of_nat (length n2)) by lia.
        split; [unfold apart_frame; lia|]. split; [unfold apart_gnl, LA_G_NL, NK_SIZE; lia|].
        split; [unfold apart; pose proof (ts_errno B TB) as Her; unfold TFIB_ERRNO in Her; lia|].
        intros Hr. exfalso. lia. }
    (* the name's own facts *)
    split.
    { intros s0 Es0. injection Es0 as <-.
      split; [exact NFR|]. split; [unfold apart_gnl in NG |- *; lia|].
      split; [lia|].
      split; [split; [unfold amem_range in NAM |- *; lia | split; [exact NRA | exact NHV]] | exact NTL]. }
    (* the literal's own facts *)
    split.
    { intros s0 Es0. injection Es0 as <-. rewrite HSL.
      split; [rewrite HSL in VFR; cbn [Z.of_nat] in VFR; unfold apart_frame in VFR |- *; lia|].
      split; [unfold apart_gnl, LA_S_SERVED, LA_G_NL, NK_SIZE; lia|].
      split; [lia|]. split; [unfold amem_range, LA_S_SERVED, kLowMemEnd, kHighMemBeg, kHighMemEnd; lia|].
      rewrite HSL in VRA, VHV. cbn [Z.of_nat] in VRA, VHV |- *. split; [exact VRA | exact VHV]. }
    (* the literal's slack: the byte at 0x213cf, which the strlen wrapper reads *)
    { intros s0 Es0. injection Es0 as <-. rewrite HSL. cbn [Z.of_nat].
      assert (Hb : ard SEGS (rdW W3 (ms_mem ms)) (LA_S_SERVED + 15) <> None).
      { rewrite HSL in VTL. cbn [Z.of_nat] in VTL. apply VTL. unfold LA_S_SERVED. lia. }
      unfold ard in Hb.
      destruct (mbyte SEGS (rdW W3 (ms_mem ms)) (LA_S_SERVED + 15)) as [b0|] eqn:Eb; [|cbn in Hb; congruence].
      exists [b0]. split.
      - split; [unfold LA_S_SERVED; lia|]. split; [cbn [length]; unfold LA_S_SERVED; lia|].
        intros i Hi. destruct i as [|i]; [|cbn [length] in Hi; lia].
        cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
      - cbn [length Z.of_nat]. unfold LA_S_SERVED. lia. }
Qed.

(* ==========================================================================
   4. The segment: the run to the call, the callee, and the WRET cut
   ========================================================================== *)

Theorem srm_vmark {fx : YK11.FPState} : srm_wret_obl fx SK B -> srm_vmark_obl fx SK B.
Proof.
  intros HWRET cx fpos ly3 S3 W3 ms3 md3 HPRE HGSP HG.
  unfold srm_gi_vmark, srm_gi_arm in HG.
  destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & HG). cbv zeta in HG.
  destruct HG as (Hpc & HENT & Hrc & Hdec & R23 & R24 & HKERN & HBUFS & HMK & HMF & HB).
  pose proof HENT as (Hmk0 & HSA & Hsne & HNLK & HGBS & HGWF & HMF0 & HFIT).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  assert (HKc : 0 <= REAC_LINK_ALIAS_WRITE_AK <= REAC_CODE_EMIT_AK)
    by (rewrite REAC_LINK_ALIAS_WRITE_AK_val, REAC_CODE_EMIT_AK_val; lia).
  pose proof HB as HB0.
  destruct HB0 as (Hrv & Hsv & Hrom & Hfrg & Hfcs & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 &
    R22 & _).
  pose proof HPRE as ((HJc & HGok & _) & _ & _).
  (* the environment: the registers at VMARK *)
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) []) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E20 : ew E 20%nat = getr (ms_regs ms3) 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) [] 20 20%bv eq_refl)).
  assert (E291 : ew E 291%nat = Z_to_bv 64 LA_S_SERVED).
  { subst E. change 291%nat with (A_OBJ 50). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 50%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  (* the cut state as an mkst, and the symbolic state *)
  assert (HMS : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_VMARK)) (ms_mem ms3) (seg_rom SEGS)).
  { rewrite (smk_ms_shape ms3 (seg_rom SEGS) Hrv Hsv Hrom Hfrg Hfcs) at 1. rewrite Hpc. reflexivity. }
  assert (HS : st_ok_pi SEGS pa_val E (smk_ss SRM_CUT_VMARK [])
     (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_VMARK)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - cbv [facts_ok smk_nof f_atoms f_alias f_conds atoms_ok alias_ok conds_ok]. tauto. }
  rewrite HMS.
  set (ms3' := mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_VMARK)) (ms_mem ms3) (seg_rom SEGS)) in HS |- *.
  assert (Hm3 : ms_mem ms3' = ms_mem ms3) by reflexivity.
  assert (HJ3 : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3') md3 (sm_k cx)) by exact HJ.
  pose (RUNC := paj_run_call_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  (* +0x4b0 .. +0x4bc: the two arguments, then `jal reac_link_alias_write` *)
  smk_prun RUNC HS HJ3 HEI; [apply awr_ok_x_nil|].
  intros ms2 mat2 HS4 HJ2 HF2 HFr2 HG2.
  pose proof (smk_frame_nil E _ _ HF2) as Hm2. rewrite Hm3 in Hm2.
  rewrite (lv_sigma HV) in HS4. cbn [link_sigma] in HS4.
  pose proof (st_ok_restrict_mkst SEGS (w_H W3) E _ ms2 HS4 eq_refl) as Hsh2. cbn [ss_pc setpc] in Hsh2.
  smk_reg HS4 (10%bv : bv 5) H10. smk_reg HS4 (11%bv : bv 5) H11. smk_reg HS4 (1%bv : bv 5) H1.
  cbn [sv_denot] in H10, H11.
  rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned, R20 in H10.
  rewrite E291, Z.add_0_r, Z_to_bv_bv_unsigned in H11.
  change (SOff 240 30876) with (SOff A_TEXT 30876) in H1.
  rewrite (codeptr_val (PI := PI) E 30876 HEI) in H1.
  assert (HBR : forall r : bv 5, In r SMK_BASE_REGS -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
  { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms2) (ms_regs ms3) []
      SMK_BASE_REGS HS4 HAE ltac:(vm_compute; reflexivity) r Hr). }
  (* the cut base at the call state *)
  set (mdc' := with_vm_backing (m_vm_lazy md3) mat2 md3) in *.
  assert (HBc : srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms2 mdc').
  { rewrite Hsh2 in HJ2 |- *. cbn [ms_mem mkst] in HJ2.
    apply (smk_base_same SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB);
      cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
      first [exact Hm2 | exact HJ2 | exact HBR | reflexivity
             | (repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
             | (repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)]. }
  assert (Hmem2 : ms_mem ms2 = ms_mem ms3) by exact Hm2.
  rewrite <- Hmem2 in HKERN, HMK, HMF.
  (* reac_link_alias_write's premises at the call *)
  destruct (svm_call_pre (fx := fx) cx fpos ly3 S3 W3 ms2 mdc' s kbs tab kbs1 HPRE HGSP HBc Hmk0 HSA HNLK
              HKERN H10 H11 ltac:(rewrite H1; reflexivity)) as (HAP & HRD & HPC).
  (* the call *)
  rewrite Hsh2.
  eapply SRr_bind.
  { exact (HWR fx (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx)
      (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem ms2) mdc'
      (sm_k cx) (ms_regs ms2) HAP HRD HPC). }
  intros W4 c4 Hle HPOST.
  assert (HEsub : forall a, inFP (reac_link_alias_write_awr (ms_regs ms2) (rdW W3 (ms_mem ms2))) a ->
                    srm_E cx a \/ srm_bufb cx fpos a).
  { intros a (r & Hin & Hr). cbn [In reac_link_alias_write_awr] in Hin. destruct Hin as [<- | []].
    left. unfold srm_E, srm_wr, reac_served_mark_awr.
    exists (LA_G_NL, LA_G_NL + NK_N_SENT + 4). split; [left; reflexivity | exact Hr]. }
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx cx fpos (srm_E cx) ly3 S3 W3 ms2 mdc'
              REAC_LINK_ALIAS_WRITE_AK
              (fun a => inFP (reac_link_alias_write_awr (ms_regs ms2) (rdW W3 (ms_mem ms2))) a)
              (reac_link_alias_write_apost SEGS (ms_regs ms2) (rdW W3 (ms_mem ms2))) W4 c4
              HPRE HBc HXE (@BoxBase.fxr_refl fx) HKc HEsub HPOST)
    as (ly4 & S4 & regs4 & mem4 & md4 & -> & HB4 & HPR & HAK & HPO).
  (* the writer's Post at the entry's objects *)
  assert (HA0 : aarg (ms_regs ms2) 0 = srm_name cx)
    by (apply (smk_aarg _ 0 10); [apply bv_eq; reflexivity | exact H10 | unfold srm_name; apply smk_aarg_range]).
  assert (HA1 : aarg (ms_regs ms2) 1 = LA_S_SERVED)
    by (apply (smk_aarg _ 1 11); [apply bv_eq; reflexivity | exact H11 | unfold LA_S_SERVED; lia]).
  pose proof HKERN as (Hnlk1 & Hwf1 & Hch1 & Hend1 & Hnif1 & Hift1 & _ & _ & _ & Hsent1 & _ & Hopen1 & Hmis1 &
    Hoc1 & Hb1).
  pose proof HNLK as (Hnlk0 & Hwf0 & Hopen0 & Hop2 & Hcl2 & Hift0 & _ & _).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms2 mdc'
                REAC_LINK_ALIAS_WRITE_AK HPRE HBc HXE HKc) as (_ & _ & _ & _ & PSV & _).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms2 mdc'
              REAC_LINK_ALIAS_WRITE_AK s HPRE HBc HXE HKc HSA
              (fun a Ha => proj1 HGSP s a HSA Ha)) as (NC & _ & _ & _ & _ & _ & _).
  destruct (HPO kbs1 tab (Some s) (Some S_SERVED) Hnlk1 Hift1
              ltac:(rewrite HA0; split; [exact (proj1 HSA) | exact NC])
              ltac:(rewrite HA1; split; [unfold LA_S_SERVED; lia | exact PSV]))
    as (Hrc10 & (kbs2 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & _)).
  destruct (svm_kstate (rdW W3 (ms_mem ms2)) s kbs tab kbs1 Hwf0 HKERN) as (Hks & Hsnt).
  rewrite Hks, Hsnt in Hrc10, P7, P8, P9, P10, P11.
  fold (srm_Wr s tab (srm_R s kbs tab)) in Hrc10, P7, P8, P9, P10, P11.
  (* the transports across the writer: its write set is the g_nl prefix *)
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms2 mdc'
              REAC_LINK_ALIAS_WRITE_AK HPRE HBc HXE HKc Hmk0) as (_ & (HMK3 & _) & HMg & _ & _).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 _ md4
              REAC_LINK_ALIAS_WRITE_AK HPRE HB4 HXE HKc Hmk0) as (_ & (HMK4 & _) & _ & _ & _).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms2 mdc'
              REAC_LINK_ALIAS_WRITE_AK HPRE HBc HXE HKc) as (_ & HINF3).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly4 S4 W4 _ md4
              REAC_LINK_ALIAS_WRITE_AK HPRE HB4 HXE HKc) as (_ & HINF4).
  assert (HOFF : off_img (sm_sink cx) AMF_BLOCK)
    by exact (blk_off_imgP (PI := PI) B ly3 S3 W3 (ms_mem ms2) mdc' (sm_sink cx) AMF_BLOCK
                (smk_base_AR SK B cx fpos _ ly3 S3 W3 ms2 mdc' HBc) HINF3).
  assert (HEc : forall a, inFP (reac_link_alias_write_awr (ms_regs ms2) (rdW W3 (ms_mem ms2))) a ->
     LA_G_NL <= a < LA_G_NL + NK_N_SENT + 4).
  { intros a (r & Hin & Hr). cbn [In reac_link_alias_write_awr] in Hin. destruct Hin as [<- | []].
    cbn [fst snd] in Hr. exact Hr. }
  (* the WRET cut *)
  apply (HWRET cx fpos ly4 S4 W4 _ md4 HPRE HGSP).
  exists s, kbs, tab, gbs, k0, kbs2. cbv zeta.
  split; [cbn [ms_pc_val mkst]; rewrite H1; reflexivity|].
  split; [exact HENT|]. split; [exact Hrc|]. split; [exact Hdec|].
  split; [cbn [ms_regs mkst]; exact Hrc10|].
  split.
  { cbn [ms_mem mkst].
    split; [exact P1|]. split; [exact P2|]. split; [rewrite P3; exact Hch1|].
    split; [rewrite P4; exact Hend1|]. split; [rewrite P5; exact Hnif1|]. split; [exact P6|].
    split; [exact P7|]. split; [exact P8|]. split; [exact P9|]. split; [exact P10|]. split; [exact P11|].
    split; [exact P12|]. split; [rewrite P13; exact Hmis1|]. split; [lia | lia]. }
  split.
  { cbn [ms_mem mkst].
    eapply (xfer_amarks B LAWS ly3 S3 W3 (ms_mem ms2) W4 mem4 ly4 S4 md4 _ _ _ (srm_mk cx) gbs HAK
      (smk_base_AR SK B cx fpos _ ly4 S4 W4 _ md4 HB4) HMK3 HMK4).
    - intros a Ha HE. pose proof (HEc a HE). unfold apart_gnl in HMg. unfold NK_SIZE, NK_N_SENT, MK_SIZE in *. lia.
    - exact HMK. }
  split.
  { cbn [ms_mem mkst].
    eapply (xfer_amemfile_k B LAWS HSEGS ly3 S3 W3 (ms_mem ms2) W4 mem4 ly4 S4 md4 _ _ _ (sm_sink cx) k0 HAK
      (smk_base_AR SK B cx fpos _ ly4 S4 W4 _ md4 HB4) HINF3 HINF4).
    - intros a Ha HE. pose proof (HEc a HE).
      unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
      unfold LA_G_NL, NK_N_SENT, AMF_BLOCK in *. lia.
    - exact HMF. }
  exact HB4.
Qed.

End b.
End a.

About srm_vmark.
Print Assumptions srm_vmark.
