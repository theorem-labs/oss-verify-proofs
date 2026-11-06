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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v, with its module paths and module names changed; 725 of its 781 lines of code are new or changed and 340 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the segment of its walk from the VOURS cut (+0x550, the
   verdict V_OURS) to the RESTORE cut (+0x2cc), against the cut interface lib/A/Prog/reac_served_markDefs.v.

   The code (listing (internal path) (internal record, sha256 5943815fc488)):
     +0x550..+0x55c  a1 := 0x213c0 ("reac-pw:served", .str.4), a2 := 15, a0 := s7 (alias)
     +0x560          jal wrapper_bcmp (0x4305c)
     +0x564          s5 := 1
     +0x568          bnez a0 -> +0x2cc
     +0x56c..+0x570  a0 := s6 (the marks block), a1 := s4 (the name)
     +0x574          jal remember (0x89db4)
     +0x578          j +0x2cc
   That is link_spec.v's mark_core in its V_OURS arm: the answer is V_OURS = 1, and the name is remembered exactly
   when the alias is "reac-pw:served" (the 15-byte bcmp of the alias buffer against the literal and its NUL is the
   plain build's strcmp of the two strings).

   The two pieces:
   - srm_vo_call : srm_from srm_gi_vret -> srm_vours_obl. The symbolic run from VOURS to the bcmp call (no memory
     access), the wrapper over lib/A/Prog/LinkWalkBcmp.v `aj_gx_bcmp_at` (window 2 * ESTACK at s1), and the cut
     state at its return address +0x564 (srm_gi_vret below: the base again, the cut facts carried across the
     wrapper, and a0 = 0 exactly when the alias is S_SERVED).
   - srm_vo_ret : srm_restore_all -> srm_from srm_gi_vret. `bnez a0`: a0 <> 0 goes to RESTORE with the marks as
     they are; a0 = 0 calls remember (`HRM`, aleaf_fx, through link_amem.v apostF_continue) and goes to RESTORE at
     the fx' remember returned, with the marks `remember (mk_names gbs) s`.
   srm_vours composes them.

   Proves no function (kind: segment lemma of reac_served_mark's walk: the VOURS cut to RESTORE). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide LinkWalkBcmp PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markUniq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
reac_served_markKit reac_served_markKitAt reac_served_markXfer reac_served_markRemArgs reac_served_markPf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. The bcmp answer as link_spec.v reads it
   ========================================================================== *)

Lemma srm_served_nz : ~ In (zb 0) S_SERVED.
Proof.
unfold S_SERVED, zb. cbn [map In]. intros H.
repeat (destruct H as [H|H]; [apply (f_equal (fun x : bv 8 => bv_unsigned x)) in H; vm_compute in H; discriminate H|]).
exact H.
Qed.

Lemma srm_served_len : length S_SERVED = 14%nat.
Proof. reflexivity. Qed.

(* a C string whose first 15 bytes (as far as the string and its NUL go) are those of "reac-pw:served" and its
   NUL is "reac-pw:served" *)
Lemma srm_cstr_served : forall al : list byte, ~ In (zb 0) al ->
  (forall i, (i < 15)%nat -> (i <= length al)%nat ->
     nth_error (al ++ [zb 0]) i = nth_error (S_SERVED ++ [zb 0]) i) ->
  al = S_SERVED.
Proof.
intros al Hal H.
assert (HL : length al = 14%nat).
{ destruct (Nat.lt_trichotomy (length al) 14) as [Hl | [Hl | Hl]]; [exfalso | exact Hl | exfalso].
  - pose proof (H (length al) ltac:(lia) ltac:(lia)) as E.
    rewrite nth_error_app2 in E by lia. rewrite Nat.sub_diag in E. cbn [nth_error] in E.
    rewrite nth_error_app1 in E by (rewrite srm_served_len; lia).
    symmetry in E. apply nth_error_In in E. exact (srm_served_nz E).
  - pose proof (H 14%nat ltac:(lia) ltac:(lia)) as E.
    rewrite nth_error_app1 in E by lia.
    rewrite nth_error_app2 in E by (rewrite srm_served_len; lia).
    rewrite srm_served_len, Nat.sub_diag in E. change (nth_error [zb 0] 0) with (Some (zb 0)) in E.
    apply nth_error_In in E. exact (Hal E). }
apply lw_list_ext; [rewrite HL; reflexivity|]. intros k Hk.
pose proof (H k ltac:(lia) ltac:(lia)) as E.
rewrite nth_error_app1 in E by lia. rewrite nth_error_app1 in E by (rewrite srm_served_len; lia). exact E.
Qed.

Lemma srm_omap_bz_inj : forall o1 o2 : option byte,
  option_map (fun b : byte => bv_unsigned b) o1 = option_map (fun b : byte => bv_unsigned b) o2 -> o1 = o2.
Proof.
intros [b1|] [b2|] H; cbn in H; try discriminate H; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Section bc.
Variable segs : list Segment.

(* wrapper_bcmp's answer (the 15 viewed bytes at x and y agree) is "the alias is S_SERVED" *)
Lemma srm_bcmp_served : forall (H : word -> bool) (mem : word -> option byte) x y al,
  acstr_at segs (mrestrict H mem) x al -> acstr_at segs (mrestrict H mem) y S_SERVED ->
  ((forall i, 0 <= i < 15 -> aview segs H mem (x + i) = aview segs H mem (y + i)) <-> al = S_SERVED).
Proof.
intros H mem x y al ((_ & _ & Hx) & Hnz) ((_ & _ & Hy) & _). split.
- intros Heq. apply srm_cstr_served; [exact Hnz|]. intros i Hi Hil.
  pose proof (Heq (Z.of_nat i) ltac:(lia)) as E. unfold aview in E.
  rewrite (Hx i ltac:(rewrite length_app; cbn [length]; lia)) in E.
  rewrite (Hy i ltac:(rewrite length_app, srm_served_len; cbn [length]; lia)) in E.
  exact (srm_omap_bz_inj _ _ E).
- intros -> i Hi. unfold aview.
  replace (x + i) with (x + Z.of_nat (Z.to_nat i)) by lia.
  replace (y + i) with (y + Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hx (Z.to_nat i) ltac:(rewrite length_app, srm_served_len; cbn [length]; lia)).
  rewrite (Hy (Z.to_nat i) ltac:(rewrite length_app, srm_served_len; cbn [length]; lia)).
  reflexivity.
Qed.
End bc.

(* mark_core's V_OURS arm, at the read the body made *)
Lemma srm_mark_ours : forall s kbs tab marks,
  s <> [] -> r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = V_OURS ->
  mark_lib tab (Some s) marks (nk_sent kbs) (nk_kstate kbs) =
  (if bl_eqb (r_alias (srm_R s kbs tab)) S_SERVED
   then Mres V_OURS (remember marks s) (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab))
   else Mres V_OURS marks (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab))).
Proof.
intros s kbs tab marks Hs Hrc Hd. destruct s as [|x s']; [congruence|].
unfold mark_lib, mark_core. cbv beta iota zeta. cbn [length Nat.eqb].
change (read_core tab (Some (x :: s')) KIND_CAP ALIAS_MAX (nk_sent kbs) (nk_kstate kbs))
  with (srm_R (x :: s') kbs tab).
rewrite Hrc, Hd. change (negb (0 =? 0)) with false. change (V_OURS =? V_MARK) with false.
change (V_OURS =? V_OURS) with true. cbn [andb]. reflexivity.
Qed.

(* the frame of a run over an empty symbolic memory: nothing written *)
Lemma srm_frame_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof.
intros E m m' Hfr. apply functional_extensionality. intros x. apply Hfr. intros (r & Hr & _). destruct Hr.
Qed.

Lemma srm_ms_eta `{fx : YK11.FPState} : forall ms : machine_state,
  ms_fregs ms = fp_regs -> ms_svc_pending ms = None -> ms_resv ms = None -> ms_fcsr ms = fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

(* ==========================================================================
   2. The symbolic state at a cut: every register its own atom, no region, s10 pinned to the shadow base
   ========================================================================== *)

Definition SRB : Z := 0x7fff8000.
Definition srm_vBx : sv := SOff 26 0.
Definition srm_vspan : Z * Z := (SRB, SRB + 2 ^ 44 - 1).
Definition srm_vfacts : facts := mkFacts [(26%nat, mkAF SRB SRB 0)] [] [].
Definition srm_vss (pc : Z) : sstate := mkSS pc sr_atoms [] None srm_vfacts.

Definition SRM_KEEP : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 25%bv; 26%bv; 27%bv].
Ltac srm_inkeep := cbn [In SRM_KEEP]; repeat (first [left; reflexivity | right]).

Lemma srm_rdword_ext : forall (rd rd' : reader) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
rewrite <- (Z.add_0_r a) at 1 2. rewrite !H by lia. rewrite Z.add_0_r. reflexivity.
Qed.

(* The walk is stated at every FP state (remember returns at some fx' related to the entry's), so the Section
   fixes none: each lemma that needs one binds its own. *)
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
(* the Kit's and the transports' prefix (reac_served_markKit.v, reac_served_markXfer.v) *)
Hypothesis TB : AF0m.PcapSyms B.                 (* instance AD2l.PcapB_syms *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis HSEGS : SEGS = AB1v.tfibsegs.
(* the callees: the frame's bcmp wrapper, and remember at every FP state *)
Hypothesis ABCMP : forall fx' : YK11.FPState, @abcmp_realizes fx' rc SEGS B 0x4305c.
Hypothesis HRM : forall fx' : YK11.FPState, @remember_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

Lemma srm_vss_ok {fx : YK11.FPState} : forall (W : world SEGS) regs mem pc,
  getr regs 26 = Z_to_bv 64 SHADOW_OFF ->
  st_ok_pi SEGS pa_val (Eimg (Ereg regs [])) (srm_vss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem pc H26.
rewrite restrict_mkst_fx. unfold srm_vss, srm_vfacts. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- exact I.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs [] 26 26%bv eq_refl), H26.
  rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). unfold SRB, SHADOW_OFF.
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

Lemma srm_present_view : forall (H : word -> bool) mem a, apresent H mem a -> aview SEGS H mem a <> None.
Proof.
intros H mem a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. cbn. discriminate.
Qed.

(* the cut state again after a step that kept every register of SRM_KEEP and every byte outside a window
   [lo, hi) that lies inside [sp - K, sp - 96) (below the twelve saved words): a symbolic run of no store, or a
   wrapper call at s1 *)
Lemma srm_base_frame {fx : YK11.FPState} : forall (cx : srmcx) fpos (X : Z -> Prop) ly3 S3 (W3 : world SEGS)
    (ms ms' : machine_state) md md' lo hi,
  srm_pre SK B cx -> srm_base fx SK B cx fpos X ly3 S3 W3 ms md ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  (forall r, In r SRM_KEEP -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  srm_sp cx - REAC_SERVED_MARK_AK <= lo -> hi <= srm_sp cx - 96 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms) a -> apresent (w_H W3) (ms_mem ms') a) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X ly3 S3 W3 ms' md'.
Proof.
intros cx fpos X ly3 S3 W3 ms ms' md md' lo hi HPRE HB Hresv Hsvc Hrom Hfrg Hfcsr HJ' HR Hlo Hhi UN HPG Hfds Hfs.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct HPRE as ((HJc & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _) & _ & _).
pose proof HJc as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hceil & Hslo & _).
unfold srm_base in HB |- *. cbv zeta in HB |- *.
destruct HB as (_ & _ & _ & _ & _ & _ & Hfrs & Hnin & HS3 & Hperm & HS1 & R2 & R9 & R8 & R18 & R19 & R25 & R26 &
  R20 & R22 & R3 & R4 & R27 & Hra & Hsav & Hflag & HFp & HSHp & HK & Hfds0 & Hfs0 & HROD & Hfrm).
pose proof HS1 as (S1 & W1 & mem1 & md1 & HAR1 & Hfr1 & _).
destruct (frames_bounds SEGS B LAWS (sm_lyc cx) S1 W1 mem1 md1 SRM_CID fpos HAR1
  ltac:(rewrite Hfr1; left; reflexivity)) as (HF4 & HFc & _).
change (fs_frame_bytes SRM_CID) with 512 in HFc.
pose proof (bv_unsigned_in_range 64 (getr (sm_regs cx) 2)) as Hsp. change (bv_modulus 64) with (2 ^ 64) in Hsp.
unfold srm_sp, spZ in *. rewrite REAC_SERVED_MARK_AK_val in *.
assert (Hpv : forall a, 0 <= a < 2 ^ 64 -> (a < lo \/ hi <= a) ->
  aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
  by (intros a Ha Hn; apply UN; [exact Ha | lia]).
split; [exact Hresv|]. split; [exact Hsvc|]. split; [exact Hrom|]. split; [exact Hfrg|]. split; [exact Hfcsr|].
split; [exact HJ'|]. split; [exact Hfrs|]. split; [exact Hnin|]. split; [exact HS3|]. split; [exact Hperm|].
split; [exact HS1|].
split; [rewrite (HR 2%bv ltac:(srm_inkeep)); exact R2|].
split; [rewrite (HR 9%bv ltac:(srm_inkeep)); exact R9|].
split; [rewrite (HR 8%bv ltac:(srm_inkeep)); exact R8|].
split; [rewrite (HR 18%bv ltac:(srm_inkeep)); exact R18|].
split; [rewrite (HR 19%bv ltac:(srm_inkeep)); exact R19|].
split; [rewrite (HR 25%bv ltac:(srm_inkeep)); exact R25|].
split; [rewrite (HR 26%bv ltac:(srm_inkeep)); exact R26|].
split; [rewrite (HR 20%bv ltac:(srm_inkeep)); exact R20|].
split; [rewrite (HR 22%bv ltac:(srm_inkeep)); exact R22|].
split; [rewrite (HR 3%bv ltac:(srm_inkeep)); exact R3|].
split; [rewrite (HR 4%bv ltac:(srm_inkeep)); exact R4|].
split; [rewrite (HR 27%bv ltac:(srm_inkeep)); exact R27|].
split.
{ rewrite <- Hra. apply srm_rdword_ext. intros i Hi. apply Hpv; lia. }
split.
{ intros j Hj. rewrite <- (Hsav j Hj). apply srm_rdword_ext. intros i Hi. apply Hpv; lia. }
split.
{ rewrite <- Hflag. apply srm_rdword_ext. intros i Hi. unfold srm_F, SRM_FLAGPTR in *. apply Hpv; lia. }
split; [intros a Ha; exact (HPG a (HFp a Ha))|].
split; [intros a Ha; exact (HPG a (HSHp a Ha))|].
split.
{ eapply (akept_step SK SEGS B LAWS pa_segs_low (sm_lyc cx) (sm_Sc cx) (sm_W cx) (sm_memc cx) (sm_mdc cx)
    W3 (ms_mem ms) W3 (ms_mem ms') _ _ _ _ (fun a => lo <= a < hi) HARc); [lia | lia | exact HK | | | | ].
  - intros a Ha Hn. exact (UN a Ha Hn).
  - intros a Ha Hp. exact (HPG a Hp).
  - intros a Ha. exact Ha.
  - intros a Ha. right. lia. }
split; [rewrite Hfds; exact Hfds0|]. split; [rewrite Hfs; exact Hfs0|].
split; [|exact Hfrm].
intros a Hro Hno Herr. rewrite <- (HROD a Hro Hno Herr). apply Hpv.
- destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  + pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as Hl. lia.
  + unfold PCAP_RLO, PCAP_RHI in Hr. lia.
- left. destruct Hro as [(sg & Hsg & _ & Hr) | Hr].
  + pose proof (pa_segs_low a (ex_intro _ sg (conj Hsg Hr))) as Hl. lia.
  + unfold PCAP_RLO, PCAP_RHI in Hr. lia.
Qed.

(* the alias buffer's first 15 bytes: their shadow (0 by srm_bufs) and its hull (F's shadow is present) *)
Lemma srm_alias_ra : forall (cx : srmcx) fpos (W3 : world SEGS) m3 R,
  srm_F cx fpos mod 64 = 0 -> 0 <= srm_F cx fpos ->
  srm_bufs cx fpos W3 m3 R ->
  range_addressable (aview SEGS (w_H W3) m3) SHADOW_OFF (srm_alias cx fpos) 15.
Proof.
intros cx fpos W3 m3 R Hal H0 (_ & _ & _ & _ & Hsh) x Hx.
unfold srm_alias, SRM_ALIAS in Hx.
exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF x) with (srm_SH cx fpos + (x / 8 - srm_F cx fpos / 8))
  by (unfold srm_SH, shadow_addr, shadow_of_addr; lia).
apply Hsh. unfold srm_bufsh_off. right. lia.
Qed.

Lemma srm_alias_hull : forall (cx : srmcx) fpos (W3 : world SEGS) m3,
  srm_F cx fpos mod 64 = 0 -> 0 <= srm_F cx fpos ->
  (forall a, srm_SH cx fpos <= a < srm_SH cx fpos + SRM_SHN -> apresent (w_H W3) m3 a) ->
  shadow_hull_vis (aview SEGS (w_H W3) m3) (srm_alias cx fpos) 15.
Proof.
intros cx fpos W3 m3 Hal H0 Hp s Hs. apply srm_present_view. apply Hp.
unfold srm_alias, SRM_ALIAS, shadow_addr in Hs. unfold srm_SH, shadow_addr, SRM_SHN, SHADOW_OFF in *. lia.
Qed.

(* ==========================================================================
   3. Small facts the walk uses
   ========================================================================== *)

Lemma srm_ew_reg : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs [])) n = getr regs r.
Proof.
intros regs n r Hr. pose proof (bv_unsigned_in_range 5 r) as Hu. change (bv_modulus 5) with 32 in Hu.
rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs [] n r Hr).
Qed.

Lemma srm_ew_img : forall E n, img_env pa_val A_LIM E -> (A_TEXT <= n < A_LIM)%nat ->
  ew E n = Z_to_bv 64 (pa_val n).
Proof. intros E n HE Hn. rewrite <- (HE n Hn). symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma srm_env_agree : forall regs, env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])).
Proof. intros regs. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.

Lemma srm_aarg0 : forall regs, aarg regs 0 = bv_unsigned (getr regs 10).
Proof.
intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 0)) with (10%bv : bv 5) by (apply bv_eq; reflexivity).
reflexivity.
Qed.
Lemma srm_aarg1 : forall regs, aarg regs 1 = bv_unsigned (getr regs 11).
Proof.
intros regs. unfold aarg, argZ. replace (Z_to_bv 5 (10 + 1)) with (11%bv : bv 5) by (apply bv_eq; reflexivity).
reflexivity.
Qed.

Lemma srm_w64_unsigned : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma srm_word0 : forall w : word, w = w64 0 <-> bv_unsigned w = 0.
Proof.
intros w. split; [intros ->; reflexivity|]. intros H. apply bv_eq. rewrite H. reflexivity.
Qed.

(* the registers SRM_KEEP from aregs_preserved *)
Lemma srm_keep_pres : forall regs regs', aregs_preserved regs regs' ->
  forall r, In r SRM_KEEP -> getr regs' r = getr regs r.
Proof.
intros regs regs' HP r Hr. cbn [In SRM_KEEP] in Hr.
repeat (destruct Hr as [<- | Hr];
  [ match goal with |- getr _ ?b = _ =>
      let z := eval vm_compute in (bv_unsigned b) in
      replace b with (Z_to_bv 5 z) by (apply bv_eq; reflexivity); apply HP; unfold acallee_saved; lia end |]).
destruct Hr.
Qed.

(* ==========================================================================
   4. The intermediate cuts of this segment
   ========================================================================== *)

Definition SRM_VRET : Z := AF_reac_served_mark + 0x564.    (* the return address of wrapper_bcmp *)
Definition SRM_VREM : Z := AF_reac_served_mark + 0x578.    (* the return address of remember: `j +0x2cc` *)

(* +0x564: wrapper_bcmp returned; a0 = 0 exactly when the alias is "reac-pw:served" *)
Definition srm_gi_vret {fx : YK11.FPState} (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs1,
  let R := srm_R s kbs tab in
  ms_pc_val ms3 = w64 (BASE + SRM_VRET) /\
  srm_ent cx s kbs tab gbs k0 /\
  r_rc R = 0 /\ decide (Some (r_kind R)) (Some (r_alias R)) = V_OURS /\
  (getr (ms_regs ms3) 10 = w64 0 <-> r_alias R = S_SERVED) /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state R) (r_reqs R) 1 /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.

(* +0x578: remember returned (at its fx'); s5 = 1, the marks remember the name *)
Definition srm_gi_vrem {fx : YK11.FPState} (cx : srmcx) (fpos : Z) (ly3 : alayout) (S3 : astate)
    (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  exists s kbs tab gbs k0 kbs1 gbs',
  let R := srm_R s kbs tab in
  ms_pc_val ms3 = w64 (BASE + SRM_VREM) /\ getr (ms_regs ms3) 21 = w64 1 /\
  srm_ent cx s kbs tab gbs k0 /\
  r_rc R = 0 /\ decide (Some (r_kind R)) (Some (r_alias R)) = V_OURS /\ r_alias R = S_SERVED /\
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state R) (r_reqs R) 1 /\
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs' /\ marks_wf gbs' /\
  mk_names gbs' = remember (mk_names gbs) s /\
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 /\
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3.

(* the RESTORE cut from the facts of either arm *)
Lemma srm_vo_restore {fx : YK11.FPState} : forall cx fpos ly3 S3 (W3 : world SEGS) ms3 md3
    s kbs tab gbs k0 kbs1 gbs' (M : mres),
  srm_ent cx s kbs tab gbs k0 ->
  M = mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) -> m_rc M = 1 ->
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (m_state M) (m_reqs M) 1 ->
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs' -> marks_wf gbs' -> mk_names gbs' = m_marks M ->
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 ->
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_RESTORE) -> getr (ms_regs ms3) 21 = w64 1 ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  srm_gi_restore SK B cx fpos ly3 S3 W3 ms3 md3.
Proof.
intros cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 kbs1 gbs' M HENT HM Hrc HK HMK HWF HN HMF Hpc H21 HB.
exists 1. split; [exact Hpc|]. split; [exact H21|]. split; [|exact HB].
rewrite <- Hrc.
apply (srm_pf_of cx s kbs tab gbs k0 kbs1 gbs' k0 (rdW W3 (ms_mem ms3)) M HENT HM);
  [ | exact HMK | exact HWF | exact HN | exact HMF | unfold MARK_LINE_MAX; lia].
eapply srm_kern_mono; [|exact HK]. lia.
Qed.

(* the string premise of xfer_kern between two cuts: a table string's bytes have the entry's view at both *)
Lemma srm_xstr {fxa fxb : YK11.FPState} : forall cx fpos XA XB lyA SA (WA : world SEGS) msA mdA
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

(* ==========================================================================
   5. From +0x578 (remember returned) to RESTORE: `j +0x2cc`
   ========================================================================== *)

Lemma srm_vo_rem_tail {fx : YK11.FPState} : srm_restore_all SK B -> srm_from fx SK B (@srm_gi_vrem fx).
Proof.
intros HREST cx fpos ly3 S3 W3 ms3 md3 HPRE HSP HG.
destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & gbs' & Hpc & H21 & HENT & Hrc & Hdec & Hal & HKERN & HMK &
  HWF & HN & HMF & HB).
pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
destruct HB0 as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _).
pose proof HPRE as ((_ & HGX & _) & _ & _).
pose proof HENT as (Hmk0 & HSA & Hsne & _).
assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (srm_vss SRM_VREM) (restrict (w_H W3) ms3)).
{ rewrite (srm_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr) at 2. rewrite Hpc, Hrom. apply srm_vss_ok. exact R26. }
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS srm_vBx [] (Eimg (Ereg (ms_regs ms3) [])) (mrestrict (w_H W3) (ms_mem ms3)))
  by constructor.
pose proof (srm_env_agree (ms_regs ms3)) as HAE.
assert (E21 : ew (Eimg (Ereg (ms_regs ms3) [])) 21 = getr (ms_regs ms3) 21) by exact (srm_ew_reg _ 21 21%bv eq_refl).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
pose proof (paj_run_to_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUNTO.
paj_run_to_tok RUNTO HS HJ SHOK srm_vspan SRM_CUT_RESTORE; [apply awr_ok_x_nil|].
pose proof (srm_frame_nil _ _ _ HF) as Hm.
prreg HS (21%bv : bv 5) Q21.
pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ SRM_KEEP HS HAE ltac:(vm_compute; reflexivity)) as QK.
cbn [ms_regs restrict] in QK.
pmkst HS.
apply (HREST fx cx fpos ly3 S3 W3 _ _ HPRE HSP).
set (R := srm_R s kbs tab).
assert (HMv : mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)
  = Mres V_OURS (remember (mk_names gbs) s) (r_reqs R) (r_state R)).
{ rewrite (srm_mark_ours s kbs tab (mk_names gbs) Hsne Hrc Hdec). fold R.
  replace (bl_eqb (r_alias R) S_SERVED) with true by (symmetry; apply bl_eqb_iff; exact Hal). reflexivity. }
eapply (srm_vo_restore cx fpos ly3 S3 W3 _ _ s kbs tab gbs k0 kbs1 gbs' _ HENT eq_refl);
  rewrite ?HMv; cbn [m_rc m_state m_reqs m_marks ms_mem ms_regs ms_pc_val mkst].
- reflexivity.
- rewrite Hm. exact HKERN.
- rewrite Hm. exact HMK.
- exact HWF.
- exact HN.
- rewrite Hm. exact HMF.
- reflexivity.
- rewrite Q21, E21. exact H21.
- eapply (srm_base_frame cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ (srm_sp cx - 96) (srm_sp cx - 96) HPRE HB);
    [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ | | | | | | | ].
  + intros r Hr. cbn [ms_regs mkst]. exact (QK r Hr).
  + rewrite REAC_SERVED_MARK_AK_val. lia.
  + lia.
  + intros a _ _. cbn [ms_mem mkst]. rewrite Hm. reflexivity.
  + intros a Hp. cbn [ms_mem mkst]. rewrite Hm. exact Hp.
  + repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  + repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
Qed.

(* ==========================================================================
   6. From +0x564 (wrapper_bcmp returned) to RESTORE: s5 := 1, `bnez a0`, remember on a0 = 0
   ========================================================================== *)

(* after a run: name its end state, and its memory as the cut's (the run stored nothing) *)
Ltac srm_rename n :=
  lazymatch goal with
  | H : st_ok_pi _ _ _ _ (restrict _ ?x) |- _ => rename x into n
  | H : st_ok _ _ _ (restrict _ ?x) |- _ => rename x into n
  end.
Ltac srm_mem Hm :=
  lazymatch goal with HF : frame_of _ _ (ms_mem _) (ms_mem _) |- _ =>
    let Hm' := fresh "Hm'" in pose proof (srm_frame_nil _ _ _ HF) as Hm'; clear HF;
    first [ rewrite Hm in Hm'; clear Hm; rename Hm' into Hm | rename Hm' into Hm ] end;
  repeat lazymatch goal with HFr : frame_of _ _ _ _ |- _ => clear HFr end;
  repeat lazymatch goal with HG : mem_grows _ _ |- _ => clear HG end.

Lemma srm_base_AR {fx : YK11.FPState} : forall cx fpos X ly3 S3 (W3 : world SEGS) ms3 md3,
  srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof.
intros cx fpos X ly3 S3 W3 ms3 md3 HB. unfold srm_base in HB. cbv zeta in HB.
destruct HB as (_ & _ & _ & _ & _ & HJ & _). destruct HJ as (_ & _ & (memS & HJi & _) & _). exact (proj1 HJi).
Qed.

Lemma srm_pres21 : forall regs regs', aregs_preserved regs regs' -> getr regs' 21%bv = getr regs 21%bv.
Proof.
intros regs regs' HP. replace (21%bv : bv 5) with (Z_to_bv 5 21) by (apply bv_eq; reflexivity).
apply HP. unfold acallee_saved. lia.
Qed.

Lemma srm_aarg_range : forall regs i, 0 <= aarg regs i < 2 ^ 64.
Proof.
intros regs i. unfold aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (10 + i)))) as H.
change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma srm_base_codeptr : forall k, 0 <= k < 2 ^ 40 -> bv_unsigned (Z_to_bv 64 (BASE + k)) = BASE + k.
Proof.
intros k Hk. pose proof pa_B_ok as (HB0 & HB1 & _). apply unsigned_lit_small. lia.
Qed.

Lemma srm_vo_ret {fx : YK11.FPState} : srm_restore_all SK B -> srm_from fx SK B (@srm_gi_vret fx).
Proof.
intros HREST cx fpos ly3 S3 W3 ms3 md3 HPRE HSP HG.
destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & Hpc & HENT & Hrc & Hdec & Ha0 & HKERN & HMK & HMF & HB).
pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
destruct HB0 as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R26 & R20 &
  R22 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
pose proof HPRE as ((_ & HGX & _) & _ & _).
pose proof HSP as (HSPn & _).
pose proof HENT as (Hmk0 & HSA & Hsne & _ & _ & HWF0 & _).
assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (srm_vss SRM_VRET) (restrict (w_H W3) ms3)).
{ rewrite (srm_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr) at 2. rewrite Hpc, Hrom. apply srm_vss_ok. exact R26. }
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS srm_vBx [] (Eimg (Ereg (ms_regs ms3) [])) (mrestrict (w_H W3) (ms_mem ms3)))
  by constructor.
pose proof (srm_env_agree (ms_regs ms3)) as HAE.
assert (E10 : ew (Eimg (Ereg (ms_regs ms3) [])) 10 = getr (ms_regs ms3) 10) by exact (srm_ew_reg _ 10 10%bv eq_refl).
assert (E20 : ew (Eimg (Ereg (ms_regs ms3) [])) 20 = getr (ms_regs ms3) 20) by exact (srm_ew_reg _ 20 20%bv eq_refl).
assert (E22 : ew (Eimg (Ereg (ms_regs ms3) [])) 22 = getr (ms_regs ms3) 22) by exact (srm_ew_reg _ 22 22%bv eq_refl).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
pose proof (paj_run_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUN.
pose proof (paj_run_to_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUNTO.
pose proof (paj_branch (PI := PI)) as BR.
(* +0x564 `addi s5, zero, 1`, to `bnez a0` *)
paj_run_tok RUN HS HJ SHOK srm_vspan; [apply awr_ok_x_nil|].
srm_rename ms1. srm_mem Hm. rewrite ?wvb_collapse in HJ.
psrr_branch_tok RUN BR HS SHOK srm_vspan.
- (* a0 <> 0: the alias is not "reac-pw:served"; s5 = 1 to RESTORE, the marks as they are *)
  rewrite branch_ne_U, (U_atom E 10%nat (bv_unsigned (getr (ms_regs ms3) 10))
      ltac:(rewrite E10; symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(pose proof (bv_unsigned_in_range 64 (getr (ms_regs ms3) 10)) as Hu;
            change (bv_modulus 64) with (2 ^ 64) in Hu; lia)),
    (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hal : bl_eqb (r_alias (srm_R s kbs tab)) S_SERVED = false).
  { destruct (bl_eqb (r_alias (srm_R s kbs tab)) S_SERVED) eqn:Hb; [|reflexivity].
    exfalso. apply Hc. apply srm_word0. apply Ha0. apply bl_eqb_iff. exact Hb. }
  paj_run_to_tok RUNTO HS HJ SHOK srm_vspan SRM_CUT_RESTORE; [apply awr_ok_x_nil|].
  srm_rename ms2. srm_mem Hm. rewrite ?wvb_collapse in HJ.
  prreg HS (21%bv : bv 5) Q21.
  pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ SRM_KEEP HS HAE ltac:(vm_compute; reflexivity)) as QK.
  cbn [ms_regs restrict] in QK.
  pmkst HS.
  apply (HREST fx cx fpos ly3 S3 W3 _ _ HPRE HSP).
  assert (HMv : mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)
    = Mres V_OURS (mk_names gbs) (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab))).
  { rewrite (srm_mark_ours s kbs tab (mk_names gbs) Hsne Hrc Hdec), Hal. reflexivity. }
  eapply (srm_vo_restore cx fpos ly3 S3 W3 _ _ s kbs tab gbs k0 kbs1 gbs _ HENT eq_refl);
    rewrite ?HMv; cbn [m_rc m_state m_reqs m_marks ms_mem ms_regs ms_pc_val mkst].
  + reflexivity.
  + rewrite Hm. exact HKERN.
  + rewrite Hm. exact HMK.
  + exact HWF0.
  + reflexivity.
  + rewrite Hm. exact HMF.
  + reflexivity.
  + exact Q21.
  + eapply (srm_base_frame cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ (srm_sp cx - 96) (srm_sp cx - 96) HPRE HB);
      [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ | | | | | | | ].
    * intros r Hr. cbn [ms_regs mkst]. exact (QK r Hr).
    * rewrite REAC_SERVED_MARK_AK_val. lia.
    * lia.
    * intros a _ _. cbn [ms_mem mkst]. rewrite Hm. reflexivity.
    * intros a Hp. cbn [ms_mem mkst]. rewrite Hm. exact Hp.
    * repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    * repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity.
- (* a0 = 0: the alias is "reac-pw:served"; remember(m, name) *)
  rewrite branch_ne_U, (U_atom E 10%nat (bv_unsigned (getr (ms_regs ms3) 10))
      ltac:(rewrite E10; symmetry; apply Z_to_bv_bv_unsigned)
      ltac:(pose proof (bv_unsigned_in_range 64 (getr (ms_regs ms3) 10)) as Hu;
            change (bv_modulus 64) with (2 ^ 64) in Hu; lia)),
    (U_lit E 0 ltac:(lia)) in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hal : r_alias (srm_R s kbs tab) = S_SERVED) by (apply Ha0; apply srm_word0; exact Hc).
  paj_run_tok RUN HS HJ SHOK srm_vspan; [apply awr_ok_x_nil|].
  srm_rename ms2. srm_mem Hm. rewrite ?wvb_collapse in HJ.
  prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (21%bv : bv 5) Q21.
  assert (QK : forall r, In r SRM_KEEP -> getr (ms_regs (restrict (w_H W3) ms2)) r = getr (ms_regs ms3) r).
  { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ _ _ _ SRM_KEEP HS HAE ltac:(vm_compute; reflexivity) r Hr). }
  cbn [ms_regs restrict] in QK.
  pmkst HS.
  rewrite (lv_sigma HV LS_remember). change (link_sigma LS_remember) with REMEMBER_A.
  remember (mkst (ms_regs ms2) (Z_to_bv 64 REMEMBER_A) (ms_mem ms2) (seg_rom SEGS)) as msc eqn:Hmsc.
  assert (Rmsc : ms_regs msc = ms_regs ms2) by (rewrite Hmsc; reflexivity).
  assert (Mmsc : ms_mem msc = ms_mem ms2) by (rewrite Hmsc; reflexivity).
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdc' := mdx) end.
  (* the call's arguments *)
  assert (Hmk : aarg (ms_regs msc) 0 = srm_mk cx).
  { rewrite Rmsc, srm_aarg0, Q10, E22, R22. apply srm_w64_unsigned. apply srm_aarg_range. }
  assert (Hname : aarg (ms_regs msc) 1 = srm_name cx).
  { rewrite Rmsc, srm_aarg1, Q11, E20, R20. apply srm_w64_unsigned. apply srm_aarg_range. }
  assert (Hkc : 0 <= REMEMBER_AK <= REAC_CODE_EMIT_AK) by (rewrite REMEMBER_AK_val, REAC_CODE_EMIT_AK_val; lia).
  (* the cut base at the call *)
  assert (HBc : srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 msc mdc').
  { eapply (srm_base_frame cx fpos (srm_E cx) ly3 S3 W3 ms3 msc md3 mdc' (srm_sp cx - 96) (srm_sp cx - 96)
      HPRE HB); [rewrite Hmsc; reflexivity | rewrite Hmsc; reflexivity | rewrite Hmsc; reflexivity
                | rewrite Hmsc; reflexivity | rewrite Hmsc; reflexivity | rewrite Mmsc; exact HJ | | | | | | | ].
    - intros r Hr. rewrite Rmsc. exact (QK r Hr).
    - rewrite REAC_SERVED_MARK_AK_val. lia.
    - lia.
    - intros a _ _. rewrite Mmsc, Hm. reflexivity.
    - intros a Hp. rewrite Mmsc, Hm. exact Hp.
    - unfold mdc'. repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
    - unfold mdc'. repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
  (* the Kit's facts at the call, window REMEMBER_AK *)
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK s
    HPRE HBc (fun a H => H) Hkc HSA (fun a Ha => HSPn s a HSA Ha))
    as (HNM & HNrt & HNlen & _ & _ & _ & HNmk).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK
    HPRE HBc (fun a H => H) Hkc Hmk0) as (HMB & HLED & HMg & _ & HMf).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK
    HPRE HBc (fun a H => H) Hkc) as (_ & _ & _ & _ & _ & _ & HFMT & HFMTrt & _).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK
    HPRE HBc (fun a H => H) Hkc) as (_ & Hin3).
  assert (HMKc : amarks_at SEGS (rdW W3 (ms_mem msc)) (aarg (ms_regs msc) 0) gbs)
    by (rewrite Hmk, Mmsc, Hm; exact HMK).
  assert (HNMc : acstr_at SEGS (rdW W3 (ms_mem msc)) (aarg (ms_regs msc) 1) s) by (rewrite Hname; exact HNM).
  (* remember's premises *)
  pose proof (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK []
    (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) HPRE HBc (fun a H => H) Hkc) as HAPc.
  assert (Hra : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + 31060)) by (rewrite Rmsc; exact Q1).
  specialize (HAPc ltac:(rewrite Hra; apply ret_ok_codeptr_v; [lia | reflexivity])
    ltac:(unfold raZ; rewrite Hra, srm_base_codeptr by lia; pose proof pa_base_lo; lia)
    ltac:(intros cd [])
    ltac:(intros a Ha; left; exact (srm_rem_wr cx _ _ a Hmk Ha))).
  assert (HRDc : forall a, remember_ard SEGS (ms_regs msc) (rdW W3 (ms_mem msc)) a ->
    akb SEGS B ly3 S3 (spZ (ms_regs msc) - REMEMBER_AK) (spZ (ms_regs msc)) a).
  { intros a (_ & s' & Hs' & Ha). rewrite Hname in Hs', Ha.
    pose proof (acstr_at_unique SEGS _ _ _ _ Hs' HNM) as Es. subst s'.
    apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK a
      HPRE HBc Hkc).
    apply (HSPn s a HSA). unfold srm_gspan.
    pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)). lia. }
  assert (HPREc : remember_apre SEGS (ablocks B ly3 S3) (ms_regs msc) (rdW W3 (ms_mem msc))).
  { apply (srm_rem_pre (ablocks B ly3 S3) (ms_regs msc) (rdW W3 (ms_mem msc)) gbs s HMKc HWF0).
    - rewrite Hmk. exact HLED.
    - rewrite Hmk. exact HMB.
    - rewrite Hname. exact (proj1 HSA).
    - exact HNMc.
    - exact HNlen.
    - rewrite Hname. exact HNrt.
    - rewrite Hname, Hmk. exact (HNmk Hmk0).
    - exact HFMT.
    - exact HFMTrt. }
  (* remember, at every fx' it returns *)
  assert (HcfgE : msc = mkst (ms_regs msc) (w64 REMEMBER_A) (ms_mem msc) (seg_rom SEGS))
    by (rewrite Hmsc; reflexivity).
  rewrite HcfgE.
  eapply apostF_continue.
  { exact (HRM fx (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx)
      (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem msc) mdc' (sm_k cx)
      (ms_regs msc) HAPc HRDc Hfrm HPREc). }
  intros fx' W4 c4 _ Hfxr HPOST.
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx' cx fpos (srm_E cx) ly3 S3 W3 msc mdc' REMEMBER_AK
    (fun a => inFP (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) a)
    (fun r m => remember_apost SEGS (ms_regs msc) (rdW W3 (ms_mem msc)) r m) W4 c4
    HPRE HBc (fun a H => H) Hfxr Hkc (fun a Ha => or_introl (srm_rem_wr cx _ _ a Hmk Ha)) HPOST)
    as (ly4 & S4 & regs4 & mem4 & md4 & -> & HB4 & HP4 & HK4 & HPOST4).
  destruct (srm_rem_post (ms_regs msc) (rdW W3 (ms_mem msc)) regs4 (rdW W4 mem4) gbs s HPOST4 HMKc HNMc)
    as (gbs' & HMK4 & HWF4 & HN4 & _).
  rewrite Hmk in HMK4.
  (* the transports across remember: its write set is the marks block *)
  assert (HEc : forall a, inFP (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) a ->
    srm_mk cx <= a < srm_mk cx + MK_SIZE).
  { intros a Ha. rewrite <- Hmk. exact (srm_rem_wr_blk (ms_regs msc) _ a ltac:(rewrite Hmk; exact Hmk0) Ha). }
  pose proof (srm_xstr (fxa := fx) (fxb := fx') cx fpos (srm_E cx) (srm_E cx) ly3 S3 W3 msc mdc' ly4 S4 W4 _ md4
    s kbs tab gbs k0 HPRE HBc (fun a H => H) HB4 (fun a H => H) HENT) as HX.
  cbn [ms_mem mkst] in HX.
  assert (HKERN4 : srm_kern (rdW W4 mem4) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1).
  { eapply (xfer_kern B HSEGS TB ly3 S3 W3 (ms_mem msc) W4 mem4 _ _ _ kbs kbs1 tab _ _ 1 HK4).
    - intros a Ha HE. pose proof (HEc a HE). unfold apart_gnl in HMg. unfold NK_SIZE, MK_SIZE in *. lia.
    - exact HX.
    - rewrite Mmsc, Hm. exact HKERN. }
  assert (HMF4 : amemfile_k SEGS (rdW W4 mem4) (sm_sink cx) k0).
  { destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos (srm_E cx) ly4 S4 W4 _ md4 REMEMBER_AK
      HPRE HB4 (fun a H => H) Hkc) as (_ & Hin4).
    eapply (xfer_amemfile_k B LAWS HSEGS ly3 S3 W3 (ms_mem msc) W4 mem4 ly4 S4 md4 _ _ _ (sm_sink cx) k0 HK4
      (srm_base_AR (fx := fx') _ _ _ _ _ _ _ _ HB4) Hin3 Hin4).
    - intros a Ha HE. pose proof (HEc a HE). unfold apart in HMf. unfold AMF_BLOCK, MK_SIZE in *. lia.
    - rewrite Mmsc, Hm. exact HMF. }
  (* the rest of the walk at fx' (`j +0x2cc` to RESTORE), lifted back to fx *)
  unfold srm_post. eapply (srr_apostF_lift SK SEGS B fx fx'); [exact Hfxr|].
  apply (srm_vo_rem_tail (fx := fx') HREST cx fpos ly4 S4 W4 _ md4 HPRE HSP).
  exists s, kbs, tab, gbs, k0, kbs1, gbs'. cbv zeta.
  split; [cbn [ms_pc_val mkst]; rewrite Hra; reflexivity|].
  split; [cbn [ms_regs mkst]; rewrite (srm_pres21 _ _ HP4), Rmsc; exact Q21|].
  split; [exact HENT|]. split; [exact Hrc|]. split; [exact Hdec|]. split; [exact Hal|].
  split; [exact HKERN4|]. split; [exact HMK4|]. split; [exact HWF4|].
  split; [rewrite HN4; reflexivity|]. split; [exact HMF4|].
  exact HB4.
Qed.

(* ==========================================================================
   7. From VOURS to +0x564: the literal, 15, the alias; wrapper_bcmp
   ========================================================================== *)

Lemma srm_vo_call {fx : YK11.FPState} : srm_from fx SK B (@srm_gi_vret fx) -> srm_vours_obl fx SK B.
Proof.
intros HVRET cx fpos ly3 S3 W3 ms3 md3 HPRE HSP HG.
unfold srm_gi_vours, srm_gi_arm in HG.
destruct HG as (s & kbs & tab & gbs & k0 & kbs1 & Hpc & HENT & Hrc & Hdec & R23 & _ & HKERN & HBUFS & HMK & HMF & HB).
pose proof HB as HB0. unfold srm_base in HB0. cbv zeta in HB0.
destruct HB0 as (Hresv & Hsvc & Hrom & Hfrg & Hfcsr & HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R26 & _ & _ &
  R3 & R4 & _ & _ & _ & _ & _ & HSHp & _ & _ & _ & _ & _).
pose proof HPRE as ((HJc & HGX & _ & _ & _ & Hgp & Htp & _ & Hwlo & Hwhi & _) & _ & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
destruct (srm_sp_facts SK B LAWS TB RELRO_IMG HSEGS cx HPRE) as (Hsp16 & Hspc & Hsp47 & Hsp1 & Hsp1m).
destruct (srm_F_facts SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 HPRE HB)
  as (HF4 & HFc & HFal & HFapp & _).
assert (Hkc : 0 <= 2 * ESTACK <= REAC_CODE_EMIT_AK) by (rewrite REAC_CODE_EMIT_AK_val; unfold ESTACK; lia).
pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 (2 * ESTACK)
  HPRE HB (fun a H => H) Hkc) as (_ & _ & _ & _ & HSV & HSVrt & _).
destruct HSVrt as (_ & _ & _ & HSVra & HSVhv & _ & _).
rewrite srm_served_len in HSVra, HSVhv. change (Z.of_nat 14 + 1) with 15 in HSVra, HSVhv.
destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 (2 * ESTACK)
  HPRE HB (fun a H => H) Hkc) as (_ & Hin_f).
destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 (2 * ESTACK)
  HPRE HB (fun a H => H) Hkc (proj1 HENT)) as (_ & (Hin_m & _) & _).
pose proof HBUFS as (_ & HAL & _ & HALbuf & _).
(* the symbolic state at VOURS *)
assert (HS : st_ok_pi SEGS pa_val (Eimg (Ereg (ms_regs ms3) [])) (srm_vss SRM_CUT_VOURS) (restrict (w_H W3) ms3)).
{ rewrite (srm_ms_eta ms3 Hfrg Hsvc Hresv Hfcsr) at 2. rewrite Hpc, Hrom. apply srm_vss_ok. exact R26. }
assert (HEI : img_env pa_val A_LIM (Eimg (Ereg (ms_regs ms3) []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS srm_vBx [] (Eimg (Ereg (ms_regs ms3) [])) (mrestrict (w_H W3) (ms_mem ms3)))
  by constructor.
pose proof (srm_env_agree (ms_regs ms3)) as HAE.
assert (E2 : ew (Eimg (Ereg (ms_regs ms3) [])) 2 = getr (ms_regs ms3) 2) by exact (srm_ew_reg _ 2 2%bv eq_refl).
assert (E23 : ew (Eimg (Ereg (ms_regs ms3) [])) 23 = getr (ms_regs ms3) 23) by exact (srm_ew_reg _ 23 23%bv eq_refl).
remember (Eimg (Ereg (ms_regs ms3) [])) as E eqn:HEdef.
pose proof (paj_run_x SK B LAWS (sm_G cx) HGX (sm_XO cx) (sm_OUT cx)) as RUN.
(* +0x550 .. +0x560: the arguments, then `jal wrapper_bcmp` *)
paj_run_tok RUN HS HJ SHOK srm_vspan; [apply awr_ok_x_nil|].
srm_rename ms1. srm_mem Hm. rewrite ?wvb_collapse in HJ.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12.
assert (QK : forall r, In r SRM_KEEP -> getr (ms_regs (restrict (w_H W3) ms1)) r = getr (ms_regs ms3) r).
{ intros r Hr. exact (regs_kept_of_st_ok SEGS E _ _ _ _ SRM_KEEP HS HAE ltac:(vm_compute; reflexivity) r Hr). }
cbn [ms_regs restrict] in QK.
rewrite (srm_ew_img E 291 HEI ltac:(unfold A_TEXT, A_LIM; lia)) in Q11.
change 291%nat with (A_OBJ 50) in Q11. rewrite (lv_obj HV 50 ltac:(unfold link_nobj; lia)) in Q11.
pmkst HS.
rewrite (lv_sigma HV LS___interceptor_trampoline_bcmp).
change (link_sigma LS___interceptor_trampoline_bcmp) with 0x4305c.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdc' := mdx) end.
(* wrapper_bcmp's premises *)
assert (Tsp : spZ (ms_regs ms1) = srm_sp1 cx).
{ unfold spZ. rewrite Q2, E2. exact (srm_base_sp SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HPRE HB). }
assert (Hal0 : 0 <= srm_alias cx fpos) by (unfold srm_alias, SRM_ALIAS; lia).
unfold srm_sp, SRM_FB in *.
assert (HAKv : REAC_SERVED_MARK_AK = 9504) by exact REAC_SERVED_MARK_AK_val.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hbuf_some : forall a, srm_alias cx fpos <= a < srm_alias cx fpos + 15 ->
  aview SEGS (w_H W3) (ms_mem ms1) a <> None).
{ intros a Ha. rewrite Hm. destruct HALbuf as (junk & Hlen & (_ & _ & Hb) & _).
  unfold aview. replace a with (srm_alias cx fpos + Z.of_nat (Z.to_nat (a - srm_alias cx fpos))) by lia.
  rewrite (Hb (Z.to_nat (a - srm_alias cx fpos)) ltac:(unfold ALIAS_MAX in Hlen; lia)).
  destruct (nth_error junk (Z.to_nat (a - srm_alias cx fpos))) eqn:Ej; [discriminate|].
  apply nth_error_None in Ej. unfold ALIAS_MAX in Hlen. lia. }
assert (Hlit_some : forall a, LA_S_SERVED <= a < LA_S_SERVED + 15 -> aview SEGS (w_H W3) (ms_mem ms1) a <> None).
{ intros a Ha. rewrite Hm. destruct HSV as ((_ & _ & Hb) & _).
  unfold aview. replace a with (LA_S_SERVED + Z.of_nat (Z.to_nat (a - LA_S_SERVED))) by lia.
  rewrite (Hb (Z.to_nat (a - LA_S_SERVED)) ltac:(rewrite length_app, srm_served_len; cbn [length]; unfold LA_S_SERVED in *; lia)).
  destruct (nth_error (S_SERVED ++ [zb 0]) (Z.to_nat (a - LA_S_SERVED))) eqn:Ej; [discriminate|].
  apply nth_error_None in Ej. rewrite length_app, srm_served_len in Ej. cbn [length] in Ej.
  unfold LA_S_SERVED in *. lia. }
eapply SRr_bind.
{ apply (aj_gx_bcmp_at SK SEGS B LAWS pa_segs_low 0x4305c (ABCMP fx) (sm_G cx) (sm_XO cx) (sm_OUT cx) W3 (ms_regs ms1)
    (ms_mem ms1) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx)
    ((SRM_CID, fpos) :: sm_own cx) ly3 S3 mdc' (sm_k cx) (srm_alias cx fpos) LA_S_SERVED 15
    (Z_to_bv 64 (BASE + 31040)) HGX HJ).
  - rewrite Tsp. lia.
  - rewrite Tsp. lia.
  - rewrite Tsp. lia.
  - rewrite (QK 3%bv ltac:(srm_inkeep)), R3. exact Hgp.
  - rewrite (QK 4%bv ltac:(srm_inkeep)), R4. exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q10, E23. exact R23.
  - exact Q11.
  - exact Q12.
  - lia.
  - exact Hal0.
  - unfold srm_alias, SRM_ALIAS. lia.
  - unfold LA_S_SERVED. lia.
  - unfold LA_S_SERVED. lia.
  - intros a Ha. split; [exact (Hbuf_some a Ha)|]. rewrite Tsp. unfold srm_alias, SRM_ALIAS in Ha. lia.
  - intros a Ha. split; [exact (Hlit_some a Ha)|]. rewrite Tsp. unfold LA_S_SERVED in Ha. lia.
  - intros a Ha. rewrite Tsp. unfold srm_alias, SRM_ALIAS in Ha. lia.
  - intros a Ha. rewrite Tsp. unfold LA_S_SERVED in Ha. lia.
  - unfold amem_range, srm_alias, SRM_ALIAS. unfold in_app, kLowShadowBeg, kLowMemEnd, kHighMemBeg,
      kHighMemEnd, ASAN_CEIL in *. lia.
  - unfold amem_range, LA_S_SERVED, kLowMemEnd. lia.
  - rewrite Hm. exact (srm_alias_ra cx fpos W3 (ms_mem ms3) _ HFal ltac:(lia) HBUFS).
  - intros _. rewrite Hm. exact (srm_alias_hull cx fpos W3 (ms_mem ms3) HFal ltac:(lia) HSHp).
  - rewrite Hm. exact HSVra.
  - intros _. rewrite Hm. exact HSVhv. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hres & Hfr2 & Hpr2 & Hsbm).
(* the cut at +0x564 *)
assert (HB2 : srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 (mkst regs2 (Z_to_bv 64 (BASE + 31040)) mem2 (seg_rom SEGS)) md2).
{ eapply (srm_base_frame cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 md2 (srm_sp1 cx - 2 * ESTACK) (srm_sp1 cx) HPRE HB);
    [reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | exact HJ2 | | | | | | | ].
  - intros r Hr. cbn [ms_regs mkst]. rewrite (srm_keep_pres _ _ HP2 r Hr). exact (QK r Hr).
  - unfold srm_sp. lia.
  - unfold srm_sp. lia.
  - intros a Ha Hn. cbn [ms_mem mkst]. rewrite <- Hm. apply Hfr2; [exact Ha | rewrite Tsp; exact Hn].
  - intros a Hp. cbn [ms_mem mkst]. apply Hpr2. rewrite Hm. exact Hp.
  - rewrite (same_but_materialized_wvb _ _ Hsbm). unfold mdc'.
    repeat rewrite (proj1 (wvb_fds_fs _ _ _)). reflexivity.
  - rewrite (same_but_materialized_wvb _ _ Hsbm). unfold mdc'.
    repeat rewrite (proj2 (wvb_fds_fs _ _ _)). reflexivity. }
(* the callee-relative kept clause of the wrapper, for the transports *)
assert (HAKb : akept SEGS B ly3 S3 W3 (ms_mem ms3) W3 mem2 (srm_sp1 cx - 2 * ESTACK) (srm_sp1 cx) (fun _ => False)).
{ pose proof HJ as (_ & HXO & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwin & _).
  eapply (akept_step SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms3) md3 W3 (ms_mem ms3) W3 mem2 _ _ _ _
    (fun a => srm_sp1 cx - 2 * ESTACK <= a < srm_sp1 cx)
    (srm_base_AR _ _ _ _ _ _ _ _ HB)).
  - lia.
  - lia.
  - apply (akept_refl SK SEGS B LAWS pa_segs_low). intros a Ha. rewrite <- Hm. apply Hwin. lia.
  - intros a Ha Hn. rewrite <- Hm. exact (Hfr2 a Ha ltac:(rewrite Tsp; exact Hn)).
  - intros a _ Hp. apply Hpr2. rewrite Hm. exact Hp.
  - intros a Ha. exact Ha.
  - intros a Ha. right. exact Ha. }
apply (HVRET cx fpos ly3 S3 W3 _ md2 HPRE HSP).
exists s, kbs, tab, gbs, k0, kbs1. cbv zeta.
split; [reflexivity|].
split; [exact HENT|]. split; [exact Hrc|]. split; [exact Hdec|].
split.
{ cbn [ms_regs mkst].
  pose proof (srm_bcmp_served SEGS (w_H W3) (ms_mem ms3) (srm_alias cx fpos) LA_S_SERVED _ HAL HSV) as Hsv.
  rewrite Hm in Hres.
  split; intros H0; [apply Hsv; apply Hres; exact H0 | apply Hres; apply Hsv; exact H0]. }
split.
{ cbn [ms_mem mkst]. eapply (xfer_kern B HSEGS TB ly3 S3 W3 (ms_mem ms3) W3 mem2 _ _ _ kbs kbs1 tab _ _ 1 HAKb).
  - intros a _ HE. exact HE.
  - pose proof (srm_xstr (fxa := fx) (fxb := fx) cx fpos (srm_E cx) (srm_E cx) ly3 S3 W3 ms3 md3 ly3 S3 W3 _ md2
      s kbs tab gbs k0 HPRE HB (fun a H => H) HB2 (fun a H => H) HENT) as HX.
    cbn [ms_mem mkst] in HX. exact HX.
  - exact HKERN. }
split.
{ cbn [ms_mem mkst]. eapply (xfer_amarks B LAWS ly3 S3 W3 (ms_mem ms3) W3 mem2 ly3 S3 md2 _ _ _ (srm_mk cx) gbs HAKb
    (srm_base_AR _ _ _ _ _ _ _ _ HB2) Hin_m Hin_m); [intros a _ HE; exact HE | exact HMK]. }
split.
{ cbn [ms_mem mkst]. eapply (xfer_amemfile_k B LAWS HSEGS ly3 S3 W3 (ms_mem ms3) W3 mem2 ly3 S3 md2 _ _ _ (sm_sink cx) k0 HAKb
    (srm_base_AR _ _ _ _ _ _ _ _ HB2) Hin_f Hin_f); [intros a _ HE; exact HE | exact HMF]. }
exact HB2.
Qed.

(* ==========================================================================
   8. The segment
   ========================================================================== *)

Theorem srm_vours {fx : YK11.FPState} : srm_restore_all SK B -> srm_vours_obl fx SK B.
Proof. intros HREST. exact (srm_vo_call (srm_vo_ret HREST)). Qed.

End b.
End a.

About srm_vours.
Print Assumptions srm_vours.
