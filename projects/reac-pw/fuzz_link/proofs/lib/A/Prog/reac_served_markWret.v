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
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the segment of its walk from the WRET cut (+0x4c0, after
   reac_link_alias_write returned w_rc WR in a0; reac_served_markDefs.v `srm_gi_wret`) to the RESTORE cut (+0x2cc),
   against the cut interface lib/A/Prog/reac_served_markDefs.v.

   The code (listing (internal path) (internal record, sha256 5943815fc488) lines 308-386):
     +0x4c0  beqz a0, +0x5c0                  a0 = w_rc WR, the writer's answer
   the write succeeded:
     +0x5c0..+0x5c4  a0 := s6 (the marks block), a1 := s4 (the name)
     +0x5c8          jal remember (0x89db4)          (aleaf_fx: returns at some fx' with fxr fx fx')
     +0x5cc          s5 := 0;  +0x5d0 j +0x2cc
   the write failed:
     +0x4c4  s5 := a0;  +0x4c8..+0x4cc a0 := g_say   (the Pre's `au64_at m LA_G_SAY sink`)
     +0x4d0  bnez a0, +0x4f0                  sink <> 0, so the stderr arm +0x4d4..+0x4ec is not reached
     +0x4f0  a1 := -1;  +0x4f4 negw a6, s5;  +0x4f8 beq s5, a1, +0x5d4
     +0x4fc..+0x504  a7 := .str.7 (0x214e0), j +0x5dc     |  +0x5d4..+0x5d8 a7 := .str.6 (0x21480)
     +0x5dc..+0x5f0  a3 := .str.5 (0x213e0), a5 := .str.4 (0x213c0), a2 := 0, a4 := s4 (the name)
     +0x5f4          jal reac_code_emit (0x89be4)    (aleaf_fx)
     +0x5f8          j +0x2cc
   That is link_spec.v's mark_core in its V_MARK arm after the write (`smk_mark_vmark`): a write that answered 0
   remembers the name and answers V_MARK = 0; a write that failed answers its code, keeps the marks, and prints
   one line through reac_code_emit (which of .str.6 / .str.7 it takes does not reach the Post: only the line's
   length, at most MARK_LINE_MAX, does).

   No instruction of this segment stores, and only `ld a0, g_say` reads memory (g_say is at a constant offset into
   a global, uninstrumented), so the plain engine (LinkWalkSide.v Section pe) runs it over one read-only region,
   g_say's 8 bytes, as reac_served_markRret.v does.

   The pieces:
   - smk_wret_run: the run from WRET to remember's or to reac_code_emit's entry.
   - smk_tail: the run from a callee's return address (+0x5cc, +0x5f8) to RESTORE, at any fx.
   - smk_wret_rem: remember (HRM, through link_amem.v apostF_continue), then RESTORE at its fx' with rcv = 0.
   - smk_wret_emit: reac_code_emit (HEM, .str.5's Pre from reac_served_markEmitArgs.v), then RESTORE at its fx'
     with rcv = w_rc WR.
   srm_wret composes them.

   Proves no function (kind: segment lemma of reac_served_mark's walk: the WRET cut to RESTORE). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markUniq
reac_served_markKit reac_served_markKitAt reac_served_markXfer reac_served_markEmitArgs reac_served_markRemArgs
reac_served_markPf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* ==========================================================================
   1. link_spec facts of the V_MARK arm
   ========================================================================== *)

(* nl_talk's state after: the socket and send errnos cleared or kept, the end errno kept *)
Lemma smk_talk_after_bounds : forall K,
  0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  0 <= k_sock (talk_after K) < 2^31 /\ 0 <= k_send (talk_after K) < 2^31 /\ 0 <= k_end (talk_after K) < 2^31.
Proof.
  intros K H1 H2 H3. unfold talk_after, talk_core.
  destruct (negb (k_sock K =? 0)); [cbn [snd fst k_sock k_send k_end]; lia|].
  destruct (negb (k_send K =? 0)); [cbn [snd fst k_sock k_send k_end]; lia|].
  destruct (chunk_loop _ _ _) as [v j]. destruct v; cbn [snd fst k_sock k_send k_end]; lia.
Qed.

Lemma smk_read_state_bounds : forall tab nm kc ac reqs K,
  0 <= k_sock K < 2^31 -> 0 <= k_send K < 2^31 -> 0 <= k_end K < 2^31 ->
  0 <= k_sock (r_state (read_core tab nm kc ac reqs K)) < 2^31 /\
  0 <= k_send (r_state (read_core tab nm kc ac reqs K)) < 2^31 /\
  0 <= k_end (r_state (read_core tab nm kc ac reqs K)) < 2^31.
Proof.
  intros tab nm kc ac reqs K H1 H2 H3. unfold read_core.
  destruct nm as [s|]; [|cbn [r_state]; lia].
  destruct (Nat.eqb (length s) 0); [cbn [r_state]; lia|]. cbv zeta.
  destruct (index_of tab s =? 0); [cbn [r_state]; lia|].
  cbn [r_state]. apply smk_talk_after_bounds; assumption.
Qed.

(* the writer's code on the kstate the reader left is an int32, so `beqz a0` decides `w_rc = 0` *)
Lemma smk_wrc_range : forall s kbs tab, nlk_wf kbs ->
  -2^31 <= w_rc (srm_Wr s tab (srm_R s kbs tab)) < 2^31.
Proof.
  intros s kbs tab HW. destruct (srm_kstate_bounds kbs HW) as (H1 & H2 & H3).
  unfold srm_Wr, write_lib, srm_R, read_lib.
  destruct (smk_read_state_bounds tab (Some s) KIND_CAP ALIAS_MAX (nk_sent kbs) (nk_kstate kbs) H1 H2 H3)
    as (G1 & G2 & G3).
  apply srm_write_rc_range; assumption.
Qed.

(* mark_core's V_MARK arm: the write's answer decides between remembering the name and answering its code *)
Lemma smk_mark_vmark : forall s kbs tab gbs, s <> [] -> r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = V_MARK ->
  mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs) =
    if w_rc (srm_Wr s tab (srm_R s kbs tab)) =? 0
    then Mres V_MARK (remember (mk_names gbs) s) (w_reqs (srm_Wr s tab (srm_R s kbs tab)))
           (w_state (srm_Wr s tab (srm_R s kbs tab)))
    else Mres (w_rc (srm_Wr s tab (srm_R s kbs tab))) (mk_names gbs) (w_reqs (srm_Wr s tab (srm_R s kbs tab)))
           (w_state (srm_Wr s tab (srm_R s kbs tab))).
Proof.
  intros s kbs tab gbs Hs Hrc Hdec. unfold mark_lib, mark_core, srm_Wr, write_lib.
  destruct (Nat.eqb_spec (length s) 0) as [H0|H0]; [destruct s; [contradiction | discriminate] |].
  unfold srm_R, read_lib in Hrc, Hdec |- *. cbv zeta.
  rewrite Hrc, Z.eqb_refl, Hdec, Z.eqb_refl. cbv beta iota.
  destruct (w_rc (write_core tab (Some s) (Some S_SERVED) _ _) =? 0); reflexivity.
Qed.

(* ==========================================================================
   2. The engine at this segment's cuts
   ========================================================================== *)

Definition SRM_WREM : Z := AF_reac_served_mark + 0x5cc.    (* the return address of remember: `mv s5, zero` *)
Definition SRM_WEMR : Z := AF_reac_served_mark + 0x5f8.    (* the return address of reac_code_emit: `j +0x2cc` *)
Lemma SRM_WREM_val : SRM_WREM = 31144. Proof. reflexivity. Qed.
Lemma SRM_WEMR_val : SRM_WEMR = 31188. Proof. reflexivity. Qed.

(* every register its own atom, atom 32 the sink, and g_say's 8 bytes as the one region (read-only) *)
Definition smk_nof : facts := mkFacts [] [] [].
Definition smk_gsay : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 47)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition smk_ss (pc : Z) (rs : list YP09.region) : sstate := mkSS pc sr_atoms rs None smk_nof.

Lemma smk_ms_shape : forall {fx : YK11.FPState} (ms : machine_state) rom,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = rom ->
  ms_fregs ms = YK11.fp_regs -> ms_fcsr ms = YK11.fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) rom.
Proof. intros fx ms rom H1 H2 H3 H4 H5. destruct ms; cbn in *; subst; reflexivity. Qed.

Lemma smk_frame_ro : forall E (m m' : word -> option byte), frame_of E [smk_gsay] m m' -> m' = m.
Proof.
  intros E m m' HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [smk_gsay YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

Lemma smk_frame_nil : forall E (m m' : word -> option byte), frame_of E [] m m' -> m' = m.
Proof.
  intros E m m' HF. apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). destruct Hr.
Qed.

Lemma smk_w64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof.
  intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Lemma smk_aarg : forall (regs : bvmap 5 word) (i : Z) (r : bv 5) v,
  Z_to_bv 5 (10 + i) = r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> aarg regs i = v.
Proof. intros regs i r v Hr Hv Hb. unfold aarg, argZ. rewrite Hr, Hv. apply unsigned_lit_small. lia. Qed.

Lemma smk_aarg_range : forall regs i, 0 <= aarg regs i < 2 ^ 64.
Proof.
  intros regs i. unfold aarg, argZ. pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (10 + i)))) as H.
  change (bv_modulus 64) with (2 ^ 64) in H. exact H.
Qed.

Lemma smk_apart_sym : forall a n b k, apart a n b k -> apart b k a n.
Proof. unfold apart. intros. lia. Qed.

(* the plain engine on a state HS: the run lemma RUN instantiated with the computed end state *)
Ltac smk_tpi RUN :=
  lazymatch type of RUN with
  | context [sym_runN_pi ?tpi _ _] => constr:(tpi)
  | context [sym_run_toN_pi ?tpi _ _ _] => constr:(tpi)
  end.
Ltac smk_prun RUN HS HJ HEI :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := smk_tpi RUN in
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      eapply (RUN W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ); clear Hrun
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      eapply (RUN W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
    end
  end.
Ltac smk_prun_to RUN HS HJ HEI stop :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := smk_tpi RUN in
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      eapply (RUN W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
    end
  end.
(* a register at a callee entry state (st_ok), with the symbolic value computed *)
Ltac smk_reg HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict] in H
  end.
(* a register at a stopped run state (st_ok_pi), with the symbolic value computed *)
Ltac smk_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict] in H
  end.

(* the registers the base names: sp, s1, s0, s2, s3, s9, s10, s4, s6, gp, tp, s11 *)
Definition SMK_BASE_REGS : list (bv 5) := [2; 9; 8; 18; 19; 25; 26; 20; 22; 3; 4; 27]%bv.

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
(* the two callees, at every FP state *)
Hypothesis HRM : forall fx' : YK11.FPState, @remember_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.
Hypothesis HEM : forall fx' : YK11.FPState, @reac_code_emit_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

(* the cut base at a state with the same memory, the same base registers and the journal *)
Lemma smk_base_same {fx : YK11.FPState} : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_base fx SK B cx fpos X ly3 S3 W3 ms md ->
  ms_mem ms' = ms_mem ms ->
  (forall r, In r SMK_BASE_REGS -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = YK11.fp_regs -> ms_fcsr ms' = YK11.fp_csr ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos X ly3 S3 W3 ms ms' md md' HB Hm HR H1 H2 H3 H4 H5 HJ Hfd Hfs.
  assert (R : forall r, In r SMK_BASE_REGS -> getr (ms_regs ms') r = getr (ms_regs ms) r) by exact HR.
  unfold srm_base in HB |- *. cbv zeta in HB |- *.
  destruct HB as (_ & _ & _ & _ & _ & _ & B7 & B8 & B9 & B10 & B11 & G2 & G9 & G8 & G18 & G19 & G25 & G26 & G20 &
    G22 & G3 & G4 & G27 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).
  rewrite Hm in HJ |- *.
  rewrite (R 2%bv), (R 9%bv), (R 8%bv), (R 18%bv), (R 19%bv), (R 25%bv), (R 26%bv), (R 20%bv), (R 22%bv),
    (R 3%bv), (R 4%bv), (R 27%bv), Hfd, Hfs by (cbn [In SMK_BASE_REGS]; tauto).
  repeat (split; [eassumption|]). exact B33.
Qed.

Lemma smk_base_AR {fx : YK11.FPState} : forall cx fpos X ly3 S3 (W3 : world SEGS) ms3 md3,
  srm_base fx SK B cx fpos X ly3 S3 W3 ms3 md3 -> AR SEGS B ly3 S3 W3 (ms_mem ms3) md3.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 HB. unfold srm_base in HB. cbv zeta in HB.
  destruct HB as (_ & _ & _ & _ & _ & HJ & _). exact (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.

(* the string premise of xfer_kern between two cuts: a table string's bytes have the entry's view at both *)
Lemma smk_xstr {fxa fxb : YK11.FPState} : forall cx fpos XA XB lyA SA (WA : world SEGS) msA mdA
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
  assert (HpB : au64_at SEGS (rdW WB (ms_mem msB)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
  { pose proof HNLK as (_ & _ & _ & _ & _ & (Hnif & Hl80 & _) & _).
    assert (Hil : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    eapply srm_val_mem_move; [|exact Hp]. intros x Hx.
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
   3. The run from WRET to remember's or to reac_code_emit's entry
   ========================================================================== *)

Lemma smk_wret_run {fx : YK11.FPState} : forall (cx : srmcx) fpos ly3 S3 W3 ms3 md3 (rcw : Z)
    (Q : world SEGS -> config -> Prop),
  srm_pre SK B cx ->
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_WRET) ->
  getr (ms_regs ms3) 10 = w64 rcw -> -2^31 <= rcw < 2^31 ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) LA_G_SAY (sm_sink cx) -> 4096 <= sm_sink cx < 2 ^ 64 ->
  (* the write answered 0: remember's entry *)
  (forall ms' md', rcw = 0 ->
     ms' = mkst (ms_regs ms') (w64 REMEMBER_A) (ms_mem ms') (seg_rom SEGS) -> ms_mem ms' = ms_mem ms3 ->
     getr (ms_regs ms') 10 = getr (ms_regs ms3) 22 -> getr (ms_regs ms') 11 = getr (ms_regs ms3) 20 ->
     getr (ms_regs ms') 1 = w64 (BASE + SRM_WREM) ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (* the write failed: reac_code_emit's entry *)
  (forall ms' md' cap, rcw <> 0 -> (cap = LA_S_NOCAP \/ cap = LA_S_EMPTY) ->
     ms' = mkst (ms_regs ms') (w64 REAC_CODE_EMIT_A) (ms_mem ms') (seg_rom SEGS) -> ms_mem ms' = ms_mem ms3 ->
     getr (ms_regs ms') 10 = w64 (sm_sink cx) -> getr (ms_regs ms') 13 = w64 LA_S_WRITEERR ->
     getr (ms_regs ms') 14 = getr (ms_regs ms3) 20 -> getr (ms_regs ms') 15 = w64 LA_S_SERVED ->
     getr (ms_regs ms') 17 = w64 cap -> getr (ms_regs ms') 21 = w64 rcw ->
     getr (ms_regs ms') 1 = w64 (BASE + SRM_WEMR) ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 rcw Q HPRE Hpc Ha0 Hrr HBASE HSAY HSK KREM KEM.
  pose proof HBASE as HB0.
  destruct HBASE as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ & _).
  destruct HPRE as ((HJc & HGok & _) & _ & _).
  (* the environment: the registers at WRET, and the sink as atom 32 *)
  set (EXT := [w64 (sm_sink cx)]).
  set (E := Eimg (Ereg (ms_regs ms3) EXT)).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) EXT) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) EXT) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E10 : ew E 10%nat = getr (ms_regs ms3) 10)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) EXT 10 10%bv eq_refl)).
  assert (E20 : ew E 20%nat = getr (ms_regs ms3) 20)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) EXT 20 20%bv eq_refl)).
  assert (E22 : ew E 22%nat = getr (ms_regs ms3) 22)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) EXT 22 22%bv eq_refl)).
  assert (E32 : ew E 32%nat = w64 (sm_sink cx))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) EXT 0)).
  assert (EOBJ : ew E (A_OBJ 47) = Z_to_bv 64 LA_G_SAY).
  { subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 47%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (UOBJ : bv_unsigned (ew E (A_OBJ 47)) = LA_G_SAY)
    by (rewrite EOBJ; apply unsigned_lit_small; unfold LA_G_SAY; lia).
  (* the literals: .str.4 (A_OBJ 50), .str.7 (A_OBJ 51), .str.6 (A_OBJ 54), .str.5 (A_OBJ 55) *)
  assert (E291 : ew E 291%nat = Z_to_bv 64 LA_S_SERVED).
  { subst E. change 291%nat with (A_OBJ 50). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 50%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (E292 : ew E 292%nat = Z_to_bv 64 LA_S_EMPTY).
  { subst E. change 292%nat with (A_OBJ 51). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 51%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (E295 : ew E 295%nat = Z_to_bv 64 LA_S_NOCAP).
  { subst E. change 295%nat with (A_OBJ 54). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 54%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (E296 : ew E 296%nat = Z_to_bv 64 LA_S_WRITEERR).
  { subst E. change 296%nat with (A_OBJ 55). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 55%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  (* the cut state as an mkst *)
  assert (HMS : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_WRET)) (ms_mem ms3) (seg_rom SEGS)).
  { rewrite (smk_ms_shape ms3 (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc) at 1. rewrite Hpc. reflexivity. }
  assert (HS : st_ok_pi SEGS pa_val E (smk_ss SRM_CUT_WRET [smk_gsay])
     (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_WRET)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold smk_gsay, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UOBJ. split; [unfold LA_G_SAY; lia|]. split; [unfold LA_G_SAY; lia|]. split.
      + intros o Ho. lia.
      + apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ LA_G_SAY 0 8%N (SOff 32 0) (sm_sink cx));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbv; discriminate
           | rewrite Z.add_0_r; cbn [ms_mem restrict mkst]; exact HSAY].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - cbv [facts_ok smk_nof f_atoms f_alias f_conds atoms_ok alias_ok conds_ok]. tauto. }
  rewrite HMS.
  set (ms3' := mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_WRET)) (ms_mem ms3) (seg_rom SEGS)) in HS |- *.
  assert (Hm3 : ms_mem ms3' = ms_mem ms3) by reflexivity.
  assert (HJ3 : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3') md3 (sm_k cx)) by exact HJ.
  pose (RUNP := paj_run_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  pose (RUNC := paj_run_call_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  (* +0x4c0 beqz a0 *)
  apply (paj_branch (PI := PI) W3 E _ ms3' md3 Q BC_EQ (SOff 10 0) (SLit 0) HS).
  - (* a0 = 0: +0x5c0 .. +0x5c8, to remember *)
    intros Hc HS1.
    rewrite branch_eq_U, (U_atom E 10%nat (rcw mod 2 ^ 64)
      ltac:(rewrite E10, Ha0; apply smk_w64_mod) ltac:(apply Z.mod_pos_bound; lia)),
      (U_lit E 0 ltac:(lia)) in Hc.
    apply Z.eqb_eq in Hc.
    assert (HR0 : rcw = 0) by lia.
    smk_prun RUNC HS1 HJ3 HEI.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [smk_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
    intros ms2 mat2 HS4 HJ2 HF2 HFr2 HG2.
    pose proof (smk_frame_ro E _ _ HF2) as Hm2. rewrite Hm3 in Hm2.
    rewrite (lv_sigma HV) in HS4. cbn [link_sigma] in HS4.
    pose proof (st_ok_restrict_mkst SEGS (w_H W3) E _ ms2 HS4 eq_refl) as Hsh2. cbn [ss_pc setpc] in Hsh2.
    smk_reg HS4 (10%bv : bv 5) H10. smk_reg HS4 (11%bv : bv 5) H11. smk_reg HS4 (1%bv : bv 5) H1.
    cbn [sv_denot] in H10, H11.
    rewrite E22, Z.add_0_r, Z_to_bv_bv_unsigned in H10.
    rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned in H11.
    change (SOff 240 31144) with (SOff A_TEXT 31144) in H1.
    rewrite (codeptr_val (PI := PI) E 31144 HEI) in H1.
    assert (HBR : forall r : bv 5, In r SMK_BASE_REGS -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
    { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms2) (ms_regs ms3) EXT
        SMK_BASE_REGS HS4 HAE ltac:(vm_compute; reflexivity) r Hr). }
    apply KREM.
    + exact HR0.
    + exact Hsh2.
    + exact Hm2.
    + exact H10.
    + exact H11.
    + rewrite H1. reflexivity.
    + rewrite Hsh2 in HJ2 |- *. cbn [ms_mem mkst] in HJ2.
      apply (smk_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
        cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
        first [exact Hm2 | exact HJ2 | exact HBR | reflexivity
               | exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _))].
  - (* a0 <> 0: the write failed *)
    intros Hc HS1.
    rewrite branch_eq_U, (U_atom E 10%nat (rcw mod 2 ^ 64)
      ltac:(rewrite E10, Ha0; apply smk_w64_mod) ltac:(apply Z.mod_pos_bound; lia)),
      (U_lit E 0 ltac:(lia)) in Hc.
    apply Z.eqb_neq in Hc.
    assert (HRN : rcw <> 0) by (intros H0; apply Hc; rewrite H0; reflexivity).
    (* +0x4c4 .. +0x4cc: s5 := a0, a0 := g_say; the run stops at `bnez a0` *)
    smk_prun RUNP HS1 HJ3 HEI.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [smk_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
    intros ms1 mat1 HS2 HJ1 HF1 HFr1 HG1.
    pose proof (smk_frame_ro E _ _ HF1) as Hm1. rewrite Hm3 in Hm1.
    assert (HJ1' : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
      (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
      ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3) (sm_k cx)) by exact HJ1.
    apply (paj_branch (PI := PI) W3 E _ ms1 _ Q BC_NE (SOff 32 0) (SLit 0) HS2).
    + (* g_say <> 0: +0x4f0 .. +0x4f8, to `beq s5, a1` *)
      intros Hc2 HS3.
      smk_prun RUNP HS3 HJ1' HEI.
      { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [smk_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
      intros ms5 mat5 HS5 HJ5 HF5 HFr5 HG5.
      pose proof (smk_frame_ro E _ _ HF5) as Hm5. rewrite Hm1 in Hm5.
      assert (HJ5' : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
        (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
        ly3 S3 W3 (ms_mem ms5) (with_vm_backing (m_vm_lazy (with_vm_backing (m_vm_lazy md3) mat1 md3)) mat5
          (with_vm_backing (m_vm_lazy md3) mat1 md3)) (sm_k cx)) by exact HJ5.
      (* `beq s5, a1`: a7 := .str.6 (s5 = -1) or .str.7, then +0x5dc .. +0x5f4, to the call *)
      apply (paj_branch (PI := PI) W3 E _ ms5 _ Q BC_EQ (SOff 10 0) (SLit 18446744073709551615) HS5).
      * intros _ HS6.
        smk_prun RUNC HS6 HJ5' HEI.
        { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
          intros a Ha. cbn [smk_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
        intros ms2 mat2 HS4 HJ2 HF2 HFr2 HG2.
        pose proof (smk_frame_ro E _ _ HF2) as Hm2. rewrite Hm5 in Hm2.
        rewrite (lv_sigma HV) in HS4. cbn [link_sigma] in HS4.
        pose proof (st_ok_restrict_mkst SEGS (w_H W3) E _ ms2 HS4 eq_refl) as Hsh2. cbn [ss_pc setpc] in Hsh2.
        smk_reg HS4 (10%bv : bv 5) H10. smk_reg HS4 (13%bv : bv 5) H13. smk_reg HS4 (14%bv : bv 5) H14.
        smk_reg HS4 (15%bv : bv 5) H15. smk_reg HS4 (17%bv : bv 5) H17. smk_reg HS4 (21%bv : bv 5) H21.
        smk_reg HS4 (1%bv : bv 5) H1.
        cbn [sv_denot] in H10, H13, H14, H15, H17, H21.
        rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in H10.
        rewrite E296, Z.add_0_r, Z_to_bv_bv_unsigned in H13.
        rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned in H14.
        rewrite E291, Z.add_0_r, Z_to_bv_bv_unsigned in H15.
        rewrite E295, Z.add_0_r, Z_to_bv_bv_unsigned in H17.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned, Ha0 in H21.
        change (SOff 240 31188) with (SOff A_TEXT 31188) in H1.
        rewrite (codeptr_val (PI := PI) E 31188 HEI) in H1.
        assert (HBR : forall r : bv 5, In r SMK_BASE_REGS -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
        { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms2) (ms_regs ms3) EXT
            SMK_BASE_REGS HS4 HAE ltac:(vm_compute; reflexivity) r Hr). }
        apply (KEM _ _ LA_S_NOCAP HRN (or_introl eq_refl)).
        -- exact Hsh2.
        -- exact Hm2.
        -- exact H10.
        -- exact H13.
        -- exact H14.
        -- exact H15.
        -- exact H17.
        -- exact H21.
        -- rewrite H1. reflexivity.
        -- rewrite Hsh2 in HJ2 |- *. cbn [ms_mem mkst] in HJ2.
           apply (smk_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
             cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
             first [exact Hm2 | exact HJ2 | exact HBR | reflexivity
                    | (repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
                    | (repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)].
      * intros _ HS6.
        smk_prun RUNC HS6 HJ5' HEI.
        { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
          intros a Ha. cbn [smk_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
        intros ms2 mat2 HS4 HJ2 HF2 HFr2 HG2.
        pose proof (smk_frame_ro E _ _ HF2) as Hm2. rewrite Hm5 in Hm2.
        rewrite (lv_sigma HV) in HS4. cbn [link_sigma] in HS4.
        pose proof (st_ok_restrict_mkst SEGS (w_H W3) E _ ms2 HS4 eq_refl) as Hsh2. cbn [ss_pc setpc] in Hsh2.
        smk_reg HS4 (10%bv : bv 5) H10. smk_reg HS4 (13%bv : bv 5) H13. smk_reg HS4 (14%bv : bv 5) H14.
        smk_reg HS4 (15%bv : bv 5) H15. smk_reg HS4 (17%bv : bv 5) H17. smk_reg HS4 (21%bv : bv 5) H21.
        smk_reg HS4 (1%bv : bv 5) H1.
        cbn [sv_denot] in H10, H13, H14, H15, H17, H21.
        rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in H10.
        rewrite E296, Z.add_0_r, Z_to_bv_bv_unsigned in H13.
        rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned in H14.
        rewrite E291, Z.add_0_r, Z_to_bv_bv_unsigned in H15.
        rewrite E292, Z.add_0_r, Z_to_bv_bv_unsigned in H17.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned, Ha0 in H21.
        change (SOff 240 31188) with (SOff A_TEXT 31188) in H1.
        rewrite (codeptr_val (PI := PI) E 31188 HEI) in H1.
        assert (HBR : forall r : bv 5, In r SMK_BASE_REGS -> getr (ms_regs ms2) r = getr (ms_regs ms3) r).
        { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms2) (ms_regs ms3) EXT
            SMK_BASE_REGS HS4 HAE ltac:(vm_compute; reflexivity) r Hr). }
        apply (KEM _ _ LA_S_EMPTY HRN (or_intror eq_refl)).
        -- exact Hsh2.
        -- exact Hm2.
        -- exact H10.
        -- exact H13.
        -- exact H14.
        -- exact H15.
        -- exact H17.
        -- exact H21.
        -- rewrite H1. reflexivity.
        -- rewrite Hsh2 in HJ2 |- *. cbn [ms_mem mkst] in HJ2.
           apply (smk_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
             cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
             first [exact Hm2 | exact HJ2 | exact HBR | reflexivity
                    | (repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
                    | (repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)].
    + (* g_say = 0: the sink is not NULL *)
      intros Hc2 _. exfalso.
      rewrite branch_ne_U, (U_atom E 32%nat (sm_sink cx) E32 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc2.
      apply negb_false_iff, Z.eqb_eq in Hc2. lia.
Qed.

(* ==========================================================================
   4. From a callee's return address (+0x5cc, +0x5f8) to RESTORE, at any fx
   ========================================================================== *)

Lemma smk_tail {fx : YK11.FPState} : forall (cx : srmcx) fpos ly3 S3 W3 ms3 md3 p (v21 : word)
    (Q : world SEGS -> config -> Prop),
  ((p = SRM_WREM /\ v21 = w64 0) \/ (p = SRM_WEMR /\ v21 = getr (ms_regs ms3) 21)) ->
  srm_pre SK B cx -> ms_pc_val ms3 = w64 (BASE + p) ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  (forall ms' md', ms_pc_val ms' = w64 (BASE + SRM_CUT_RESTORE) -> ms_mem ms' = ms_mem ms3 ->
     getr (ms_regs ms') 21 = v21 ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md' -> SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 p v21 Q Hp HPRE Hpc HBASE K.
  pose proof HBASE as HB0.
  destruct HBASE as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ & _).
  destruct HPRE as ((HJc & HGok & _) & _ & _).
  set (E := Eimg (Ereg (ms_regs ms3) [])).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) []) E)
    by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (HMS : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + p)) (ms_mem ms3) (seg_rom SEGS)).
  { rewrite (smk_ms_shape ms3 (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc) at 1. rewrite Hpc. reflexivity. }
  assert (HS : st_ok_pi SEGS pa_val E (smk_ss p [])
     (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + p)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - exact I.
    - cbv [facts_ok smk_nof f_atoms f_alias f_conds atoms_ok alias_ok conds_ok]. tauto. }
  rewrite HMS.
  set (ms3' := mkst (ms_regs ms3) (Z_to_bv 64 (BASE + p)) (ms_mem ms3) (seg_rom SEGS)) in HS |- *.
  assert (Hm3 : ms_mem ms3' = ms_mem ms3) by reflexivity.
  assert (HJ3 : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3') md3 (sm_k cx)) by exact HJ.
  pose (RUNT := paj_run_to_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  destruct Hp as [(Ep & Ev) | (Ep & Ev)]; subst p v21; unfold SRM_WREM, SRM_WEMR, AF_reac_served_mark in HS.
  - (* +0x5cc s5 := 0; +0x5d0 j +0x2cc *)
    smk_prun_to RUNT HS HJ3 HEI SRM_CUT_RESTORE; [apply awr_ok_x_nil|].
    intros ms' mat' HS' HJ' HF HFr HG.
    pose proof (smk_frame_nil E _ _ HF) as Hm'. rewrite Hm3 in Hm'.
    pose proof (st_ok_pi_restrict_mkst (PI := PI) (w_H W3) E _ ms' HS' eq_refl) as Hsh'. cbn [ss_pc] in Hsh'.
    smk_preg HS' (21%bv : bv 5) H21. cbn [sv_denot] in H21.
    assert (HBR : forall r : bv 5, In r SMK_BASE_REGS -> getr (ms_regs ms') r = getr (ms_regs ms3) r).
    { intros r Hr. exact (regs_kept_of_st_ok_pi (PI := PI) E _ _ (ms_regs ms3) [] SMK_BASE_REGS HS' HAE
                            ltac:(vm_compute; reflexivity) r Hr). }
    apply K; [rewrite Hsh'; reflexivity | exact Hm' | rewrite H21; reflexivity |].
    rewrite Hsh' in HJ' |- *. cbn [ms_mem mkst] in HJ'.
    apply (smk_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
      cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
      first [exact Hm' | exact HJ' | exact HBR | reflexivity
             | (repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
             | (repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)].
  - (* +0x5f8 j +0x2cc *)
    smk_prun_to RUNT HS HJ3 HEI SRM_CUT_RESTORE; [apply awr_ok_x_nil|].
    intros ms' mat' HS' HJ' HF HFr HG.
    pose proof (smk_frame_nil E _ _ HF) as Hm'. rewrite Hm3 in Hm'.
    pose proof (st_ok_pi_restrict_mkst (PI := PI) (w_H W3) E _ ms' HS' eq_refl) as Hsh'. cbn [ss_pc] in Hsh'.
    assert (HBR : forall r : bv 5, In r (21%bv :: SMK_BASE_REGS) ->
                    getr (ms_regs ms') r = getr (ms_regs ms3) r).
    { intros r Hr. exact (regs_kept_of_st_ok_pi (PI := PI) E _ _ (ms_regs ms3) [] (21%bv :: SMK_BASE_REGS) HS'
                            HAE ltac:(vm_compute; reflexivity) r Hr). }
    apply K; [rewrite Hsh'; reflexivity | exact Hm' | apply HBR; left; reflexivity |].
    rewrite Hsh' in HJ' |- *. cbn [ms_mem mkst] in HJ'.
    apply (smk_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
      cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
      first [exact Hm' | exact HJ' | (intros r Hr; apply HBR; right; exact Hr) | reflexivity
             | (repeat rewrite (proj1 (wvb_fds_fs _ _ _)); reflexivity)
             | (repeat rewrite (proj2 (wvb_fds_fs _ _ _)); reflexivity)].
Qed.

(* ==========================================================================
   5. The write answered 0: remember (m, name), then RESTORE at its fx' with rcv = V_MARK = 0
   ========================================================================== *)

Lemma smk_wret_rem {fx : YK11.FPState} : forall (cx : srmcx) fpos ly3 S3 W3 (msc : machine_state) mdc
    s kbs tab gbs k0 kbs2,
  srm_restore_all SK B -> srm_pre SK B cx -> srm_gspan_ok B cx ->
  srm_ent cx s kbs tab gbs k0 ->
  r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = V_MARK ->
  w_rc (srm_Wr s tab (srm_R s kbs tab)) = 0 ->
  srm_kern (rdW W3 (ms_mem msc)) kbs kbs2 tab (w_state (srm_Wr s tab (srm_R s kbs tab)))
    (w_reqs (srm_Wr s tab (srm_R s kbs tab))) 2 ->
  amarks_at SEGS (rdW W3 (ms_mem msc)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W3 (ms_mem msc)) (sm_sink cx) k0 ->
  msc = mkst (ms_regs msc) (w64 REMEMBER_A) (ms_mem msc) (seg_rom SEGS) ->
  getr (ms_regs msc) 10 = w64 (srm_mk cx) -> getr (ms_regs msc) 11 = w64 (srm_name cx) ->
  getr (ms_regs msc) 1 = w64 (BASE + SRM_WREM) ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 msc mdc ->
  SRr SEGS W3 (mkCfg msc mdc) (srm_post fx SK B cx).
Proof.
  intros cx fpos ly3 S3 W3 msc mdc s kbs tab gbs k0 kbs2 HREST HPRE HSP HENT Hrc Hdec Hw0 HKERN HMK HMF Hmsc
    R10 R11 Hra HBc.
  pose proof HENT as (Hmk0 & HSA & Hsne & HNLK & _ & HWF0 & _ & HFIT).
  pose proof HBc as HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfrm).
  pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)) as Hm8.
  (* the call's arguments *)
  assert (Hmk : aarg (ms_regs msc) 0 = srm_mk cx).
  { apply (smk_aarg _ 0 10); [apply bv_eq; reflexivity | exact R10 | unfold srm_mk; apply smk_aarg_range]. }
  assert (Hname : aarg (ms_regs msc) 1 = srm_name cx).
  { apply (smk_aarg _ 1 11); [apply bv_eq; reflexivity | exact R11 | unfold srm_name; apply smk_aarg_range]. }
  assert (Hkc : 0 <= REMEMBER_AK <= REAC_CODE_EMIT_AK) by (rewrite REMEMBER_AK_val, REAC_CODE_EMIT_AK_val; lia).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  (* the Kit's facts at the call, window REMEMBER_AK *)
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK s
    HPRE HBc HXE Hkc HSA (fun a Ha => proj1 HSP s a HSA Ha))
    as (HNM & HNrt & HNlen & _ & _ & _ & HNmk).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK
    HPRE HBc HXE Hkc Hmk0) as (HMB & HLED & HMg & _ & HMf).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK
    HPRE HBc HXE Hkc) as (_ & _ & _ & _ & _ & _ & HFMT & HFMTrt & _).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK
    HPRE HBc HXE Hkc) as (_ & Hin3).
  assert (HMKc : amarks_at SEGS (rdW W3 (ms_mem msc)) (aarg (ms_regs msc) 0) gbs) by (rewrite Hmk; exact HMK).
  assert (HNMc : acstr_at SEGS (rdW W3 (ms_mem msc)) (aarg (ms_regs msc) 1) s) by (rewrite Hname; exact HNM).
  (* remember's apre, read set and Pre *)
  pose proof (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK []
    (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) HPRE HBc HXE Hkc) as HAPc.
  specialize (HAPc
    ltac:(rewrite Hra; apply ret_ok_codeptr_v; unfold SRM_WREM, AF_reac_served_mark; lia)
    ltac:(unfold raZ; rewrite Hra; pose proof pa_base_lo as HBL; pose proof pa_B_ok as (HB1 & HB2 & _);
          rewrite unsigned_lit_small; unfold SRM_WREM, AF_reac_served_mark in *; lia)
    ltac:(intros cd [])
    ltac:(intros a Ha; left; exact (srm_rem_wr cx _ _ a Hmk Ha))).
  assert (HRDc : forall a, remember_ard SEGS (ms_regs msc) (rdW W3 (ms_mem msc)) a ->
    akb SEGS B ly3 S3 (spZ (ms_regs msc) - REMEMBER_AK) (spZ (ms_regs msc)) a).
  { intros a (_ & s' & Hs' & Ha). rewrite Hname in Hs', Ha.
    pose proof (acstr_at_unique SEGS _ _ _ _ Hs' HNM) as Es. subst s'.
    apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK a
      HPRE HBc Hkc).
    apply (proj1 HSP s a HSA). unfold srm_gspan. lia. }
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
  rewrite Hmsc.
  eapply apostF_continue.
  { exact (HRM fx (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx)
      (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx) ly3 S3 W3 (ms_mem msc) mdc (sm_k cx)
      (ms_regs msc) HAPc HRDc Hfrm HPREc). }
  intros fx' W4 c4 _ Hfxr HPOST.
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx' cx fpos (srm_E cx) ly3 S3 W3 msc mdc REMEMBER_AK
    (fun a => inFP (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) a)
    (fun r m => remember_apost SEGS (ms_regs msc) (rdW W3 (ms_mem msc)) r m) W4 c4
    HPRE HBc HXE Hfxr Hkc (fun a Ha => or_introl (srm_rem_wr cx _ _ a Hmk Ha)) HPOST)
    as (ly4 & S4 & regs4 & mem4 & md4 & -> & HB4 & HP4 & HK4 & HPOST4).
  destruct (srm_rem_post (ms_regs msc) (rdW W3 (ms_mem msc)) regs4 (rdW W4 mem4) gbs s HPOST4 HMKc HNMc)
    as (gbs' & HMK4 & HWF4 & HN4 & _).
  rewrite Hmk in HMK4.
  (* the transports across remember: its write set is the marks block *)
  assert (HEc : forall a, inFP (remember_awr (ms_regs msc) (rdW W3 (ms_mem msc))) a ->
    srm_mk cx <= a < srm_mk cx + MK_SIZE).
  { intros a Ha. rewrite <- Hmk.
    apply (srm_rem_wr_blk (ms_regs msc) (rdW W3 (ms_mem msc)) a); [rewrite Hmk; exact Hmk0 | exact Ha]. }
  pose proof (smk_xstr (fxa := fx) (fxb := fx') cx fpos (srm_E cx) (srm_E cx) ly3 S3 W3 msc mdc ly4 S4 W4 _ md4
    s kbs tab gbs k0 HPRE HBc HXE HB4 HXE HENT) as HX.
  cbn [ms_mem mkst] in HX.
  assert (HKERN4 : srm_kern (rdW W4 mem4) kbs kbs2 tab (w_state (srm_Wr s tab (srm_R s kbs tab)))
    (w_reqs (srm_Wr s tab (srm_R s kbs tab))) 2).
  { eapply (xfer_kern B HSEGS TB ly3 S3 W3 (ms_mem msc) W4 mem4 _ _ _ kbs kbs2 tab _ _ 2 HK4).
    - intros a Ha HE. pose proof (HEc a HE). unfold apart_gnl in HMg. unfold NK_SIZE, MK_SIZE in *. lia.
    - exact HX.
    - exact HKERN. }
  assert (HMF4 : amemfile_k SEGS (rdW W4 mem4) (sm_sink cx) k0).
  { destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos (srm_E cx) ly4 S4 W4 _ md4 REMEMBER_AK
      HPRE HB4 HXE Hkc) as (_ & Hin4).
    eapply (xfer_amemfile_k B LAWS HSEGS ly3 S3 W3 (ms_mem msc) W4 mem4 ly4 S4 md4 _ _ _ (sm_sink cx) k0 HK4
      (smk_base_AR (fx := fx') _ _ _ _ _ _ _ _ HB4) Hin3 Hin4).
    - intros a Ha HE. pose proof (HEc a HE). unfold apart in HMf. unfold AMF_BLOCK, MK_SIZE in *. lia.
    - exact HMF. }
  (* mark_lib's answer: V_MARK, the name remembered *)
  pose proof (smk_mark_vmark s kbs tab gbs Hsne Hrc Hdec) as HMv.
  rewrite Hw0, Z.eqb_refl in HMv. cbv beta iota in HMv.
  assert (HPF : srm_pf cx (m_rc (mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)))
                  (rdW W4 mem4)).
  { eapply srm_pf_of; [exact HENT | reflexivity | | exact HMK4 | exact HWF4 | | exact HMF4 |].
    - rewrite HMv. cbn [m_state m_reqs]. exact HKERN4.
    - rewrite HMv. cbn [m_marks]. exact HN4.
    - unfold MARK_LINE_MAX. lia. }
  rewrite HMv in HPF. cbn [m_rc] in HPF.
  (* `mv s5, zero; j +0x2cc` at fx', and the walk lifted back to fx *)
  unfold srm_post. eapply (srr_apostF_lift SK SEGS B fx fx'); [exact Hfxr|].
  apply (smk_tail (fx := fx') cx fpos ly4 S4 W4 _ md4 SRM_WREM (w64 0) _ (or_introl (conj eq_refl eq_refl)) HPRE).
  - cbn [ms_pc_val mkst]. rewrite Hra. reflexivity.
  - exact HB4.
  - intros ms' md' Hpc' Hm' H21' HB'.
    apply (HREST fx' cx fpos ly4 S4 W4 ms' md' HPRE HSP).
    exists 0. split; [exact Hpc'|]. split; [exact H21'|]. split; [|exact HB'].
    rewrite Hm'. cbn [ms_mem mkst]. exact HPF.
Qed.

(* ==========================================================================
   6. The write failed: reac_code_emit(g_say, .., .str.5, name, .str.4, -rc, cap), then RESTORE at its fx' with
      rcv = w_rc WR
   ========================================================================== *)

Lemma smk_wret_emit {fx : YK11.FPState} : forall (cx : srmcx) fpos ly3 S3 W3 (ms3 : machine_state) md3
    s kbs tab gbs k0 kbs2 cap,
  srm_restore_all SK B -> srm_pre SK B cx -> srm_gspan_ok B cx ->
  srm_ent cx s kbs tab gbs k0 ->
  r_rc (srm_R s kbs tab) = 0 ->
  decide (Some (r_kind (srm_R s kbs tab))) (Some (r_alias (srm_R s kbs tab))) = V_MARK ->
  w_rc (srm_Wr s tab (srm_R s kbs tab)) <> 0 ->
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs2 tab (w_state (srm_Wr s tab (srm_R s kbs tab)))
    (w_reqs (srm_Wr s tab (srm_R s kbs tab))) 2 ->
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 ->
  (cap = LA_S_NOCAP \/ cap = LA_S_EMPTY) ->
  ms3 = mkst (ms_regs ms3) (w64 REAC_CODE_EMIT_A) (ms_mem ms3) (seg_rom SEGS) ->
  getr (ms_regs ms3) 10 = w64 (sm_sink cx) ->
  getr (ms_regs ms3) 13 = w64 LA_S_WRITEERR ->
  getr (ms_regs ms3) 14 = w64 (srm_name cx) ->
  getr (ms_regs ms3) 15 = w64 LA_S_SERVED ->
  getr (ms_regs ms3) 17 = w64 cap ->
  getr (ms_regs ms3) 21 = w64 (w_rc (srm_Wr s tab (srm_R s kbs tab))) ->
  getr (ms_regs ms3) 1 = w64 (BASE + SRM_WEMR) ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (srm_post fx SK B cx).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 kbs2 cap HRA HPRE HGSP HENT Hrc Hdec HWN HKERN HMK HMF Hcap
    Hsh Ha0 Ha3 Ha4 Ha5 Ha7 Hs5 Hra HB.
  set (R := srm_R s kbs tab) in *.
  set (WR := srm_Wr s tab R) in *.
  set (Kc := REAC_CODE_EMIT_AK).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  assert (HKc : 0 <= Kc <= REAC_CODE_EMIT_AK) by (unfold Kc; rewrite REAC_CODE_EMIT_AK_val; lia).
  pose proof HENT as (Hmk & (Hn0 & Hnc) & Hs & HNLK & HGBS & HGWF & HMF0 & HFIT).
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HPRE HB HXE)
    as (_ & HSK1 & HSK2 & HSK3).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc HPRE HB HXE HKc)
    as (HAMF & HINF).
  assert (HA0 : aarg (ms_regs ms3) 0 = sm_sink cx)
    by (apply (smk_aarg _ 0 10); [apply bv_eq; reflexivity | exact Ha0 | lia]).
  assert (HA3 : aarg (ms_regs ms3) 3 = LA_S_WRITEERR)
    by (apply (smk_aarg _ 3 13); [apply bv_eq; reflexivity | exact Ha3 | unfold LA_S_WRITEERR; lia]).
  (* the name at the cut, at the callee's window: the name and its NUL are akb at the entry (srm_gspan_ok) *)
  assert (HNAKB : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
    by (intros a Ha; exact (proj1 HGSP s a (conj Hn0 Hnc) Ha)).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc s HPRE HB HXE HKc
              (conj Hn0 Hnc) HNAKB) as (NC & NRT & NL & NG & NF & NE & NM).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc HPRE HB HXE HKc)
    as (_ & _ & _ & _ & PSV & PSVr & _ & _ & PL1 & PL2 & PL3 & PL4 & PL5 & PL6 & _ & _ & PR5a & PR5r & _ & _ &
        _ & _ & PR6a & PR6r & PR7a & PR7r).
  pose proof HB as HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & HROD & HFRM).
  (* the string the cap register names *)
  assert (HSC : exists sc, ((cap = LA_S_NOCAP /\ sc = S_STR6) \/ (cap = LA_S_EMPTY /\ sc = [])) /\
     acstr_at SEGS (rdW W3 (ms_mem ms3)) cap sc /\ astr_rt_ok SEGS (ms_regs ms3) Kc (rdW W3 (ms_mem ms3)) cap sc).
  { destruct Hcap as [-> | ->].
    - exists S_STR6. split; [left; split; reflexivity | split; [exact PR6a | exact PR6r]].
    - exists (@nil byte). split; [right; split; reflexivity | split; [exact PR7a | exact PR7r]]. }
  destruct HSC as (sc & Hsc & SCa & SCr).
  (* the facts every reac_code_emit call of this function has *)
  assert (HEF : srm_emit_facts SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (ablocks B ly3 S3) k0 (srm_name cx) s).
  { unfold srm_emit_facts. rewrite HA0.
    split; [lia|]. split; [exact HINF|]. split; [exact HMF|]. split; [exact HFIT|]. split; [exact HAMF|].
    split.
    { exact (blk_off_imgP (PI := PI) B ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx) AMF_BLOCK
               (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) HINF). }
    split; [exact Ha4|]. split; [exact Hn0|]. split; [exact NC|]. split; [exact NL|]. split; [exact NRT|].
    split; [apply smk_apart_sym; exact NF|].
    split; [exact PL1|]. split; [exact PL2|]. split; [exact PL3|]. split; [exact PL4|]. split; [exact PL5|].
    exact PL6. }
  (* the callee's Pre at .str.5, and the format its Post is instantiated with *)
  destruct (srm_emit_pre_mark SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (ablocks B ly3 S3) k0 (srm_name cx) s cap sc
              HEF HA3 PR5a PR5r Ha5 PSV PSVr Hsc Ha7 SCa SCr) as (fmt & ps & args & T & HFMT & HLEN & HPC).
  (* the callee's apre, read set, Pre *)
  assert (HAP : apre SK SEGS PCAP_RLO PCAP_RHI B Kc 0 [(0, 1)]
     (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx)
     (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
     ly3 S3 W3 (ms_mem ms3) md3 (sm_k cx) (ms_regs ms3)).
  { apply (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc [(0, 1)] _ HPRE HB HXE HKc).
    - rewrite Hra. apply ret_ok_codeptr_v; unfold SRM_WEMR, AF_reac_served_mark; lia.
    - unfold raZ. rewrite Hra. pose proof pa_base_lo as HBL. pose proof pa_B_ok as (HB1 & HB2 & _).
      rewrite unsigned_lit_small; unfold SRM_WEMR, AF_reac_served_mark in *; lia.
    - intros cd [<- | []]. exists 1. split; [right; right; right; left; reflexivity | cbn; lia].
    - intros a (r & [<- | []] & Hr). left. unfold srm_E, srm_wr, reac_served_mark_awr.
      exists (aivl (sm_sink cx) AMF_BLOCK). split; [right; right; left; reflexivity|].
      rewrite HA0 in Hr. exact Hr. }
  assert (HRD : forall a, reac_code_emit_ard SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) a ->
     akb SEGS B ly3 S3 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) a).
  { intros a Ha.
    pose proof (srm_acstr_range SEGS _ _ _ NC) as NCR.
    destruct (srm_emit_rd_mark SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (srm_name cx) cap sc a PR5a PSV Ha4
                ltac:(lia) HA3 Ha5 Hsc Ha7 SCa Ha) as [(s' & Hs' & Hn) | Hl].
    - pose proof (acstr_at_unique SEGS _ _ _ _ Hs' NC) as Es. subst s'.
      apply (srm_akb_entry SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc a HPRE HB HKc).
      apply HNAKB. unfold srm_gspan.
      pose proof (Z.mod_pos_bound (srm_name cx + Z.of_nat (length s)) 8 ltac:(lia)) as Hm8. lia.
    - exact (srm_lit_akb B HSEGS TB _ _ _ _ a Hl). }
  (* run the callee's contract and go on at the fx' it returns *)
  rewrite Hsh.
  eapply (apostF_continue SK SEGS B Kc 0); [apply (HEM fx); [exact HAP | exact HRD | exact HFRM | exact HPC] |].
  intros fx' W4 c4 Hle Hfx HPOST.
  assert (HEsub : forall a, inFP (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a ->
                    srm_E cx a \/ srm_bufb cx fpos a).
  { intros a (r & [<- | []] & Hr). left. unfold srm_E, srm_wr, reac_served_mark_awr.
    exists (aivl (sm_sink cx) AMF_BLOCK). split; [right; right; left; reflexivity|].
    rewrite HA0 in Hr. exact Hr. }
  destruct (srm_call_back SK B LAWS TB RELRO_IMG HSEGS fx fx' cx fpos _ ly3 S3 W3 ms3 md3 Kc
              (fun a => inFP (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a)
              (reac_code_emit_apost SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3))) W4 c4
              HPRE HB HXE Hfx HKc HEsub HPOST)
    as (ly4 & S4 & regs4 & mem4 & md4 & Hc4 & HB4 & HPR & HAK & HPO).
  subst c4.
  (* the Post at the RESTORE cut: the kernel and the marks as at WRET (the call writes only the FILE block),
     the FILE with EMIT_HEAD + |T| more bytes *)
  pose proof HB4 as HB4'.
  destruct HB4' as (_ & _ & _ & _ & _ & HJ4 & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
  assert (HOFF : off_img (sm_sink cx) AMF_BLOCK)
    by exact (blk_off_imgP (PI := PI) B ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx) AMF_BLOCK HAR3 HINF).
  assert (HEc : forall a, inFP (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a ->
     sm_sink cx <= a < sm_sink cx + AMF_BLOCK).
  { intros a (r & [<- | []] & Hr). rewrite HA0 in Hr. unfold aivl in Hr. cbn [fst snd] in Hr.
    replace (sm_sink cx =? 0) with false in Hr by (symmetry; apply Z.eqb_neq; lia). exact Hr. }
  (* g_nl is image bytes: the FILE block lies off the image *)
  assert (HGNE : forall a, LA_G_NL <= a < LA_G_NL + NK_SIZE ->
     ~ inFP (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a).
  { intros a Ha Hin. apply HEc in Hin. unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HOFF.
    unfold LA_G_NL, NK_SIZE, AMF_BLOCK in *. lia. }
  pose proof (smk_xstr (fxa := fx) (fxb := fx') cx fpos (srm_E cx) (srm_E cx) ly3 S3 W3 ms3 md3 ly4 S4 W4 _ md4
    s kbs tab gbs k0 HPRE HB HXE HB4 HXE HENT) as HTABV.
  cbn [ms_mem mkst] in HTABV.
  (* the marks block, a ledger block at both ends, apart from the FILE block *)
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc HPRE HB HXE HKc Hmk)
    as (_ & (HMK3 & _) & _ & _ & HMKF).
  destruct (srm_marks_blk_at SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos _ ly4 S4 W4 _ md4 Kc HPRE HB4 HXE HKc Hmk)
    as (_ & (HMK4 & _) & _ & _ & _).
  assert (HMKNE : forall a, srm_mk cx <= a < srm_mk cx + MK_SIZE ->
     ~ inFP (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) a).
  { intros a Ha Hin. apply HEc in Hin. unfold apart in HMKF. lia. }
  (* the FILE after the call, from the callee's Post at the format its Pre parses *)
  pose proof (HPO fmt ps args T k0 HFMT ltac:(rewrite HA0; exact HMF)) as HMF4.
  rewrite HA0 in HMF4.
  (* mark_lib's answer: the writer's code, the marks kept *)
  pose proof (smk_mark_vmark s kbs tab gbs Hs Hrc Hdec) as HMv. fold R WR in HMv.
  replace (w_rc WR =? 0) with false in HMv by (symmetry; apply Z.eqb_neq; exact HWN). cbv beta iota in HMv.
  assert (HPF : srm_pf cx (m_rc (mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)))
                  (rdW W4 mem4)).
  { eapply srm_pf_of; [exact HENT | reflexivity | | | exact HGWF | | exact HMF4
                       | unfold EMIT_HEAD, MARK_LINE_MAX in *; lia].
    - rewrite HMv. cbn [m_state m_reqs].
      eapply (xfer_kern B HSEGS TB ly3 S3 W3 (ms_mem ms3) W4 mem4 _ _ _ kbs kbs2 tab _ _ 2 HAK).
      + intros a Ha HE. exact (HGNE a Ha HE).
      + exact HTABV.
      + exact HKERN.
    - eapply (xfer_amarks B LAWS ly3 S3 W3 (ms_mem ms3) W4 mem4 ly4 S4 md4 _ _ _ (srm_mk cx) gbs HAK
        (smk_base_AR (fx := fx') _ _ _ _ _ _ _ _ HB4) HMK3 HMK4).
      + intros a Ha HE. exact (HMKNE a Ha HE).
      + exact HMK.
    - rewrite HMv. reflexivity. }
  rewrite HMv in HPF. cbn [m_rc] in HPF.
  (* `j +0x2cc` at fx', and the walk lifted back to fx *)
  unfold srm_post. eapply (srr_apostF_lift SK SEGS B fx fx'); [exact Hfx|].
  eapply (smk_tail (fx := fx') cx fpos ly4 S4 W4 _ md4 SRM_WEMR (getr regs4 21)).
  - right. split; reflexivity.
  - exact HPRE.
  - cbn [ms_pc_val mkst]. rewrite Hra. reflexivity.
  - exact HB4.
  - intros ms' md' Hpc' Hm' H21' HB'.
    apply (HRA fx' cx fpos ly4 S4 W4 ms' md' HPRE HGSP).
    exists (w_rc WR). split; [exact Hpc'|].
    split.
    { rewrite H21'. pose proof (HPR 21 ltac:(unfold acallee_saved; lia)) as H21.
      replace (Z_to_bv 5 21) with (21%bv : bv 5) in H21 by (apply bv_eq; reflexivity).
      rewrite H21. exact Hs5. }
    split; [|exact HB'].
    rewrite Hm'. cbn [ms_mem mkst]. exact HPF.
Qed.

(* ==========================================================================
   7. The segment
   ========================================================================== *)

Theorem srm_wret {fx : YK11.FPState} : srm_restore_all SK B -> srm_wret_obl fx SK B.
Proof.
  intros HREST cx fpos ly3 S3 W3 ms3 md3 HPRE HSP HG.
  destruct HG as (s & kbs & tab & gbs & k0 & kbs2 & HG). cbv zeta in HG.
  destruct HG as (Hpc & HENT & Hrc & Hdec & Ha0 & HKERN & HMK & HMF & HB).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HPRE HB HXE)
    as (HSAY & HSK1 & HSK2 & HSK3).
  pose proof HENT as (_ & _ & _ & (_ & HWF & _) & _).
  pose proof (smk_wrc_range s kbs tab HWF) as Hrr.
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & R22 & _).
  apply (smk_wret_run cx fpos ly3 S3 W3 ms3 md3 _ _ HPRE Hpc Ha0 Hrr HB HSAY ltac:(lia)).
  - intros ms' md' Hw0 Hsh Hm' R10' R11' Hra' HB'.
    rewrite R22 in R10'. rewrite R20 in R11'.
    rewrite <- Hm' in HKERN, HMK, HMF.
    exact (smk_wret_rem cx fpos ly3 S3 W3 ms' md' s kbs tab gbs k0 kbs2 HREST HPRE HSP HENT Hrc Hdec Hw0
             HKERN HMK HMF Hsh R10' R11' Hra' HB').
  - intros ms' md' cap HRN Hcap Hsh Hm' R10' R13' R14' R15' R17' R21' Hra' HB'.
    rewrite R20 in R14'. rewrite <- Hm' in HKERN, HMK, HMF.
    exact (smk_wret_emit cx fpos ly3 S3 W3 ms' md' s kbs tab gbs k0 kbs2 cap HREST HPRE HSP HENT Hrc Hdec HRN
             HKERN HMK HMF Hcap Hsh R10' R13' R14' R15' R17' R21' Hra' HB').
Qed.

End b.
End a.

About srm_wret.
Print Assumptions srm_wret.
