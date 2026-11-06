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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_served_markDec.v, with its module names changed; 430 of its 493 lines of code are new or changed and 333 lines of the source are left out. *)
(* reac_served_mark (fuzz_link.asan 0x895a8) on image A: the RRET segment of the walk, from the cut after
   reac_link_alias_read (+0x284 `beqz a0`, reac_served_markDefs.v `srm_gi_rret`) to the DEC cut (+0x498, the read
   answered 0) or, when the read failed, through reac_code_emit(g_say, 0, .str.3, name, -rc) to the RESTORE cut (+0x2cc).
   Listing (internal path) (internal record, sha256 5943815fc488) lines 165-183:
     +0x284  beqz a0, +0x498                  a0 = r_rc R (the reader's answer)
     +0x288  mv s5, a0                        the answer so far is the reader's code
     +0x28c  auipc a0; +0x290 ld a0, g_say    a0 = the sink FILE (the Pre's `au64_at m LA_G_SAY sink`)
     +0x294  bnez a0, +0x2b4                  sink <> 0, so the stderr arm +0x298..+0x2b0 is not reached
     +0x2b4  negw a5, s5; a3 := .str.3 (0x21300); a2 := 0; a4 := s4 (the name)
     +0x2c8  jal reac_code_emit               (aleaf_fx: returns at some fx' with fxr fx fx')
   No instruction of this segment stores, and none is instrumented (g_say is at a constant offset into a global),
   so the plain engine (LinkWalkSide.v Section pe) runs it over one read-only region, g_say's 8 bytes.
   The read-failure arm ends in the contract's Post with M = mark_lib ... = Mres (r_rc R) marks (r_reqs R)
   (r_state R) (link_spec.v mark_core's `negb (r_rc r =? 0)` branch): reac_served_markPf.v `srm_pf_of`.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkSide PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
model_decide_c remember_c reac_code_emit_c reac_served_mark_c reac_served_markDefs reac_served_markUniq
reac_served_markKit reac_served_markKitAt reac_served_markXfer reac_served_markEmitArgs reac_served_markPf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* the symbolic state at the RRET cut: every register its own atom, atom 32 the sink, and g_say's 8 bytes as the
   one region (read-only: no write window) *)
Definition srm_nof : facts := mkFacts [] [] [].
Definition rr_gsay : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 47)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition rr_ss : sstate := mkSS SRM_CUT_RRET sr_atoms [rr_gsay] None srm_nof.

(* a machine state of the shape the engine certifies is an mkst *)
Lemma srm_ms_shape : forall {fx : YK11.FPState} (ms : machine_state) rom,
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = rom ->
  ms_fregs ms = YK11.fp_regs -> ms_fcsr ms = YK11.fp_csr ->
  ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) rom.
Proof. intros fx ms rom H1 H2 H3 H4 H5. destruct ms; cbn in *; subst; reflexivity. Qed.

(* a run over regions with no write window leaves the memory as it was *)
Lemma srm_frame_ro : forall E (m m' : word -> option byte),
  frame_of E [rr_gsay] m m' -> m' = m.
Proof.
  intros E m m' HF. apply functional_extensionality. intros x. apply HF.
  intros (r & Hin & Hr). destruct Hin as [<- | []]. cbn [rr_gsay YP09.r_wlo YP09.r_whi] in Hr. lia.
Qed.

(* Z_to_bv reads its argument modulo 2 ^ 64 *)
Lemma srm_w64_mod : forall z, Z_to_bv 64 z = Z_to_bv 64 (z mod 2 ^ 64).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_mod by lia. reflexivity. Qed.

(* the registers the base and the DEC cut name: sp, s1, s0, s2, s3, s9, s10, s4, s6, gp, tp, s11, s7, s8 *)
Definition SRM_RRET_REGS : list (bv 5) := [2; 9; 8; 18; 19; 25; 26; 20; 22; 3; 4; 27; 23; 24]%bv.

(* the plain engine (LinkWalkSide.v Section pe) on a state HS: the run lemma RUN instantiated with the computed end
   state, leaving its awr_ok_x and run_post goals *)
Ltac srm_tpi RUN :=
  lazymatch type of RUN with
  | context [sym_runN_pi ?tpi _ _] => constr:(tpi)
  | context [sym_run_toN_pi ?tpi _ _ _] => constr:(tpi)
  end.
Ltac srm_prun RUN HS HJ HEI :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := srm_tpi RUN in
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
Ltac srm_prun_to RUN HS HJ HEI stop :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict (w_H ?W) ?ms) =>
    let tpi := srm_tpi RUN in
    let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
      eapply (RUN W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ); clear Hrun
    end
  end.
(* a register at a callee entry state (st_ok), with the symbolic value computed *)
Ltac srm_reg HS r H :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict] in H
  end.

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
Hypothesis TL : PALib B.
Hypothesis HSEGS : SEGS = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img SEGS a.
Hypothesis TB : PcapSyms B.
Hypothesis HEM : forall fx' : YK11.FPState, @reac_code_emit_acontract fx' rc SK SEGS PCAP_RLO PCAP_RHI B.

(* the cut base at a state with the same memory, the same base registers and the journal: nothing it states moved *)
Lemma srm_base_same : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms ms' : machine_state) md md',
  srm_base fx SK B cx fpos X ly3 S3 W3 ms md ->
  ms_mem ms' = ms_mem ms ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 9 = getr (ms_regs ms) 9 ->
  getr (ms_regs ms') 8 = getr (ms_regs ms) 8 -> getr (ms_regs ms') 18 = getr (ms_regs ms) 18 ->
  getr (ms_regs ms') 19 = getr (ms_regs ms) 19 -> getr (ms_regs ms') 25 = getr (ms_regs ms) 25 ->
  getr (ms_regs ms') 26 = getr (ms_regs ms) 26 -> getr (ms_regs ms') 20 = getr (ms_regs ms) 20 ->
  getr (ms_regs ms') 22 = getr (ms_regs ms) 22 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 -> getr (ms_regs ms') 27 = getr (ms_regs ms) 27 ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = YK11.fp_regs -> ms_fcsr ms' = YK11.fp_csr ->
  ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms') md' (sm_k cx) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  srm_base fx SK B cx fpos X ly3 S3 W3 ms' md'.
Proof.
  intros cx fpos X ly3 S3 W3 ms ms' md md' HB Hm R2 R9 R8 R18 R19 R25 R26 R20 R22 R3 R4 R27
    H1 H2 H3 H4 H5 HJ Hfd Hfs.
  unfold srm_base in HB |- *. cbv zeta in HB |- *.
  destruct HB as (_ & _ & _ & _ & _ & _ & B7 & B8 & B9 & B10 & B11 & G2 & G9 & G8 & G18 & G19 & G25 & G26 & G20 &
    G22 & G3 & G4 & G27 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33).
  rewrite Hm in HJ |- *.
  rewrite R2, R9, R8, R18, R19, R25, R26, R20, R22, R3, R4, R27, Hfd, Hfs.
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj HJ (conj B7 (conj B8 (conj B9 (conj B10 (conj B11
    (conj G2 (conj G9 (conj G8 (conj G18 (conj G19 (conj G25 (conj G26 (conj G20 (conj G22 (conj G3 (conj G4
    (conj G27 (conj B24 (conj B25 (conj B26 (conj B27 (conj B28 (conj B29 (conj B30 (conj B31 (conj B32
    B33)))))))))))))))))))))))))))))))).
Qed.

(* ---- the run: from the RRET cut to the DEC cut or to reac_code_emit's entry ---- *)
Lemma srm_rret_run : forall (cx : srmcx) fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0
    (Q : world SEGS -> config -> Prop),
  srm_pre SK B cx ->
  ms_pc_val ms3 = w64 (BASE + SRM_CUT_RRET) ->
  srm_ent cx s kbs tab gbs k0 ->
  getr (ms_regs ms3) 10 = w64 (r_rc (srm_R s kbs tab)) ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  au64_at SEGS (rdW W3 (ms_mem ms3)) LA_G_SAY (sm_sink cx) -> 4096 <= sm_sink cx < 2 ^ 64 ->
  (* the read answered 0: the DEC cut, every register and the memory as at RRET *)
  (forall ms' md',
     r_rc (srm_R s kbs tab) = 0 ->
     ms_pc_val ms' = w64 (BASE + SRM_CUT_DEC) -> ms_mem ms' = ms_mem ms3 ->
     (forall r : bv 5, In r SRM_RRET_REGS -> getr (ms_regs ms') r = getr (ms_regs ms3) r) ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  (* the read failed: reac_code_emit's entry *)
  (forall ms' md',
     r_rc (srm_R s kbs tab) <> 0 ->
     ms' = mkst (ms_regs ms') (w64 REAC_CODE_EMIT_A) (ms_mem ms') (seg_rom SEGS) ->
     ms_mem ms' = ms_mem ms3 ->
     getr (ms_regs ms') 10 = w64 (sm_sink cx) ->
     getr (ms_regs ms') 13 = w64 LA_S_READERR ->
     getr (ms_regs ms') 14 = getr (ms_regs ms3) 20 ->
     getr (ms_regs ms') 21 = w64 (r_rc (srm_R s kbs tab)) ->
     getr (ms_regs ms') 1 = w64 (BASE + SRM_CUT_RESTORE) ->
     srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms' md' ->
     SRr SEGS W3 (mkCfg ms' md') Q) ->
  SRr SEGS W3 (mkCfg ms3 md3) Q.
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 Q HPRE Hpc HENT Ha0 HBASE HSAY HSK KDEC KEMIT.
  set (R := srm_R s kbs tab) in *.
  pose proof HBASE as HB0.
  destruct HBASE as (Hrv & Hsv & Hrom & Hfr & Hfc & HJ & _).
  destruct HPRE as ((HJc & HGok & _) & _ & _).
  (* the reader's code is an int32 *)
  assert (HRR : -2^31 <= r_rc R < 2^31).
  { destruct HENT as (_ & _ & _ & (_ & HWF & _) & _). unfold R, srm_R, read_lib.
    exact (srm_read_rc_range tab (Some s) KIND_CAP ALIAS_MAX (nk_sent kbs) kbs HWF). }
  (* the environment: the registers at RRET, and the sink as atom 32 *)
  set (EXT := [w64 (sm_sink cx)]).
  set (E := Eimg (Ereg (ms_regs ms3) EXT)).
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg (ms_regs ms3) EXT) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms3) EXT) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (E10 : ew E 10%nat = getr (ms_regs ms3) 10)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) EXT 10 10%bv eq_refl)).
  assert (E32 : ew E 32%nat = w64 (sm_sink cx))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra (ms_regs ms3) EXT 0)).
  assert (EOBJ : ew E (A_OBJ 47) = Z_to_bv 64 LA_G_SAY).
  { subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    rewrite (lv_obj HV 47%nat ltac:(unfold link_nobj; lia)). reflexivity. }
  assert (UOBJ : bv_unsigned (ew E (A_OBJ 47)) = LA_G_SAY)
    by (rewrite EOBJ; apply unsigned_lit_small; unfold LA_G_SAY; lia).
  (* the cut state as an mkst *)
  assert (HMS : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_RRET)) (ms_mem ms3) (seg_rom SEGS)).
  { rewrite (srm_ms_shape ms3 (seg_rom SEGS) Hrv Hsv Hrom Hfr Hfc) at 1. rewrite Hpc. reflexivity. }
  assert (HS : st_ok_pi SEGS pa_val E rr_ss
     (restrict (w_H W3) (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_RRET)) (ms_mem ms3) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold rr_gsay, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite UOBJ. split; [unfold LA_G_SAY; lia|]. split; [unfold LA_G_SAY; lia|]. split.
      + intros o Ho. lia.
      + apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ LA_G_SAY 0 8%N (SOff 32 0) (sm_sink cx));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
           | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbv; discriminate
           | rewrite Z.add_0_r; cbn [ms_mem restrict mkst]; exact HSAY].
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - cbv [facts_ok srm_nof f_atoms f_alias f_conds atoms_ok alias_ok conds_ok]. tauto. }
  rewrite HMS.
  set (ms3' := mkst (ms_regs ms3) (Z_to_bv 64 (BASE + SRM_CUT_RRET)) (ms_mem ms3) (seg_rom SEGS)) in HS |- *.
  assert (Hm3 : ms_mem ms3' = ms_mem ms3) by reflexivity.
  assert (HJ3 : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
    (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
    ly3 S3 W3 (ms_mem ms3') md3 (sm_k cx)) by exact HJ.
  pose (RUNP := paj_run_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  pose (RUNT := paj_run_to_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  pose (RUNC := paj_run_call_plain_x SK B LAWS (PL := PL_link) (sm_G cx) HGok (sm_XO cx) (sm_OUT cx)).
  (* +0x284 beqz a0 *)
  apply (paj_branch (PI := PI) W3 E rr_ss ms3' md3 Q BC_EQ (SOff 10 0) (SLit 0) HS).
  - (* a0 = 0: to the DEC cut *)
    intros Hc HS1.
    rewrite branch_eq_U, (U_atom E 10%nat (r_rc R mod 2 ^ 64)
      ltac:(rewrite E10, Ha0; apply srm_w64_mod) ltac:(apply Z.mod_pos_bound; lia)),
      (U_lit E 0 ltac:(lia)) in Hc.
    apply Z.eqb_eq in Hc.
    assert (HR0 : r_rc R = 0) by lia.
    srm_prun_to RUNT HS1 HJ3 HEI SRM_CUT_DEC.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [rr_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
    intros ms' mat' HS' HJ' HF HFr HG.
    pose proof (srm_frame_ro E _ _ HF) as Hm'. rewrite Hm3 in Hm'.
    pose proof (st_ok_pi_restrict_mkst (PI := PI) (w_H W3) E _ ms' HS' eq_refl) as Hsh'. cbn [ss_pc] in Hsh'.
    assert (HRG : forall r : bv 5, In r SRM_RRET_REGS -> getr (ms_regs ms') r = getr (ms_regs ms3) r).
    { intros r Hr. exact (regs_kept_of_st_ok_pi (PI := PI) E _ _ (ms_regs ms3) EXT SRM_RRET_REGS HS' HAE
                            ltac:(vm_compute; reflexivity) r Hr). }
    apply KDEC; [exact HR0 | rewrite Hsh'; reflexivity | exact Hm' | exact HRG |].
    rewrite Hsh' in HJ' |- *. cbn [ms_mem mkst] in HJ'.
    apply (srm_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
      cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
      first [exact Hm' | exact HJ' | apply HRG; cbn; auto 20 | reflexivity
             | exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _))].
  - (* a0 <> 0: the read failed *)
    intros Hc HS1.
    rewrite branch_eq_U, (U_atom E 10%nat (r_rc R mod 2 ^ 64)
      ltac:(rewrite E10, Ha0; apply srm_w64_mod) ltac:(apply Z.mod_pos_bound; lia)),
      (U_lit E 0 ltac:(lia)) in Hc.
    apply Z.eqb_neq in Hc.
    assert (HRN : r_rc R <> 0) by (intros H0; apply Hc; rewrite H0; reflexivity).
    (* +0x288 .. +0x290: s5 := a0, a0 := g_say; the run stops at `bnez a0` *)
    srm_prun RUNP HS1 HJ3 HEI.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
      intros a Ha. cbn [rr_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
    intros ms1 mat1 HS2 HJ1 HF1 HFr1 HG1.
    pose proof (srm_frame_ro E _ _ HF1) as Hm1. rewrite Hm3 in Hm1.
    assert (HJ1' : ajournal_gx SEGS B (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx) (sm_sp0 cx) (sm_FP cx)
      (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
      ly3 S3 W3 (ms_mem ms1) (with_vm_backing (m_vm_lazy md3) mat1 md3) (sm_k cx)) by exact HJ1.
    apply (paj_branch (PI := PI) W3 E _ ms1 _ Q BC_NE (SOff 32 0) (SLit 0) HS2).
    + (* g_say <> 0: +0x2b4 .. +0x2c8, to the call *)
      intros Hc2 HS3.
      srm_prun RUNC HS3 HJ1' HEI.
      { apply awr_ok_x_cons; [|apply awr_ok_x_nil].
        intros a Ha. cbn [rr_gsay YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
      intros ms2 mat2 HS4 HJ2 HF2 HFr2 HG2.
      pose proof (srm_frame_ro E _ _ HF2) as Hm2. rewrite Hm1 in Hm2.
      rewrite (lv_sigma HV) in HS4. cbn [link_sigma] in HS4.
      pose proof (st_ok_restrict_mkst SEGS (w_H W3) E _ ms2 HS4 eq_refl) as Hsh2. cbn [ss_pc setpc] in Hsh2.
      srm_reg HS4 (10%bv : bv 5) H10. srm_reg HS4 (13%bv : bv 5) H13. srm_reg HS4 (14%bv : bv 5) H14.
      srm_reg HS4 (21%bv : bv 5) H21. srm_reg HS4 (1%bv : bv 5) H1.
      assert (E290 : ew E 290%nat = Z_to_bv 64 LA_S_READERR).
      { subst E. change 290%nat with (A_OBJ 49). rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
        rewrite (lv_obj HV 49%nat ltac:(unfold link_nobj; lia)). reflexivity. }
      assert (E20 : ew E 20%nat = getr (ms_regs ms3) 20)
        by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms3) EXT 20 20%bv eq_refl)).
      cbn [sv_denot] in H10, H13, H14, H21.
      rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned in H10.
      rewrite E290, Z.add_0_r, Z_to_bv_bv_unsigned in H13.
      rewrite E20, Z.add_0_r, Z_to_bv_bv_unsigned in H14.
      rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned, Ha0 in H21.
      change (SOff 240 30376) with (SOff A_TEXT 30376) in H1.
      rewrite (codeptr_val (PI := PI) E 30376 HEI) in H1.
      assert (HBR : forall r : bv 5, In r [2; 9; 8; 18; 19; 25; 26; 20; 22; 3; 4; 27]%bv ->
                      getr (ms_regs ms2) r = getr (ms_regs ms3) r).
      { intros r Hr. exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms2) (ms_regs ms3) EXT
          [2; 9; 8; 18; 19; 25; 26; 20; 22; 3; 4; 27]%bv HS4 HAE ltac:(vm_compute; reflexivity) r Hr). }
      apply KEMIT.
      * exact HRN.
      * exact Hsh2.
      * exact Hm2.
      * exact H10.
      * exact H13.
      * exact H14.
      * exact H21.
      * rewrite H1. reflexivity.
      * rewrite Hsh2 in HJ2 |- *. cbn [ms_mem mkst] in HJ2.
        apply (srm_base_same cx fpos (srm_E cx) ly3 S3 W3 ms3 _ md3 _ HB0);
          cbn [ms_regs ms_mem ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr mkst];
          first [exact Hm2 | exact HJ2 | apply HBR; cbn; auto 20 | reflexivity
                 | exact (proj1 (wvb_fds_fs _ _ _)) | exact (proj2 (wvb_fds_fs _ _ _))].
    + (* g_say = 0: the sink is not NULL *)
      intros Hc2 _. exfalso.
      rewrite branch_ne_U, (U_atom E 32%nat (sm_sink cx) E32 ltac:(lia)), (U_lit E 0 ltac:(lia)) in Hc2.
      apply negb_false_iff, Z.eqb_eq in Hc2. lia.
Qed.

(* a0..a7 as the contract reads them *)
Lemma srm_aarg : forall (regs : bvmap 5 word) (i : Z) (r : bv 5) v,
  Z_to_bv 5 (10 + i) = r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> aarg regs i = v.
Proof. intros regs i r v Hr Hv Hb. unfold aarg, argZ. rewrite Hr, Hv. apply unsigned_lit_small. lia. Qed.

Lemma srm_apart_sym : forall a n b k, apart a n b k -> apart b k a n.
Proof. unfold apart. intros. lia. Qed.

(* the read failed: mark_lib answers the reader's code, keeps the marks, and the kernel is the reader's *)
Lemma srm_mark_readfail : forall s kbs tab gbs, s <> [] -> r_rc (srm_R s kbs tab) <> 0 ->
  mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)
  = Mres (r_rc (srm_R s kbs tab)) (mk_names gbs) (r_reqs (srm_R s kbs tab)) (r_state (srm_R s kbs tab)).
Proof.
  intros s kbs tab gbs Hs Hrc. unfold mark_lib, mark_core.
  destruct (Nat.eqb_spec (length s) 0) as [H0|H0]; [destruct s; [contradiction | discriminate] |].
  cbv zeta. unfold srm_R, read_lib in Hrc |- *.
  destruct (Z.eqb_spec (r_rc (read_core tab (Some s) KIND_CAP ALIAS_MAX (nk_sent kbs) (nk_kstate kbs))) 0)
    as [E0|E0]; [contradiction | reflexivity].
Qed.

(* ---- the call: reac_code_emit(g_say, 0, .str.3, name, -rc) at +0x2c8, and the RESTORE cut at fx' ---- *)
Lemma srm_rret_emit : forall (cx : srmcx) fpos ly3 S3 W3 (ms3 : machine_state) md3 s kbs tab gbs k0 kbs1,
  srm_restore_all SK B ->
  srm_pre SK B cx -> srm_gspan_ok B cx ->
  srm_ent cx s kbs tab gbs k0 ->
  r_rc (srm_R s kbs tab) <> 0 ->
  srm_kern (rdW W3 (ms_mem ms3)) kbs kbs1 tab (r_state (srm_R s kbs tab)) (r_reqs (srm_R s kbs tab)) 1 ->
  amarks_at SEGS (rdW W3 (ms_mem ms3)) (srm_mk cx) gbs ->
  amemfile_k SEGS (rdW W3 (ms_mem ms3)) (sm_sink cx) k0 ->
  ms3 = mkst (ms_regs ms3) (w64 REAC_CODE_EMIT_A) (ms_mem ms3) (seg_rom SEGS) ->
  getr (ms_regs ms3) 10 = w64 (sm_sink cx) ->
  getr (ms_regs ms3) 13 = w64 LA_S_READERR ->
  getr (ms_regs ms3) 14 = w64 (srm_name cx) ->
  getr (ms_regs ms3) 21 = w64 (r_rc (srm_R s kbs tab)) ->
  getr (ms_regs ms3) 1 = w64 (BASE + SRM_CUT_RESTORE) ->
  srm_base fx SK B cx fpos (srm_E cx) ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (srm_post fx SK B cx).
Proof.
  intros cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 kbs1 HRA HPRE HGSP HENT HRN HKERN HMK HMF Hsh Ha0 Ha3 Ha4 Hs5
    Hra HB.
  set (R := srm_R s kbs tab) in *.
  set (Kc := REAC_CODE_EMIT_AK).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  assert (HKc : 0 <= Kc <= REAC_CODE_EMIT_AK) by (unfold Kc; rewrite REAC_CODE_EMIT_AK_val; lia).
  pose proof HENT as (Hmk & (Hn0 & Hnc) & Hs & HNLK & HGBS & HGWF & HMF0 & HFIT).
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HPRE HB HXE)
    as (_ & HSK1 & HSK2 & HSK3).
  destruct (srm_file_blk_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc HPRE HB HXE HKc)
    as (HAMF & HINF).
  assert (HA0 : aarg (ms_regs ms3) 0 = sm_sink cx)
    by (apply (srm_aarg _ 0 10); [apply bv_eq; reflexivity | exact Ha0 | lia]).
  assert (HA3 : aarg (ms_regs ms3) 3 = LA_S_READERR)
    by (apply (srm_aarg _ 3 13); [apply bv_eq; reflexivity | exact Ha3 | unfold LA_S_READERR; lia]).
  (* the name at the cut, at the callee's window: the name and its NUL are akb at the entry (srm_gspan_ok) *)
  assert (HNAKB : forall a, srm_name cx <= a <= srm_name cx + Z.of_nat (length s) ->
     akb SEGS B (sm_lyc cx) (sm_Sc cx) (srm_sp cx - REAC_SERVED_MARK_AK) (srm_sp cx) a)
    by (intros a Ha; exact (proj1 HGSP s a (conj Hn0 Hnc) Ha)).
  destruct (srm_name_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc s HPRE HB HXE HKc
              (conj Hn0 Hnc) HNAKB) as (NC & NRT & NL & NG & NF & NE & NM).
  pose proof (srm_policy_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc HPRE HB HXE HKc)
    as (_ & _ & _ & _ & _ & _ & _ & _ & PL1 & PL2 & PL3 & PL4 & PL5 & PL6 & PR3a & PR3r & _).
  pose proof HB as HB0.
  destruct HB0 as (_ & _ & _ & _ & _ & HJ3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & _ & _ & _ & HROD & HFRM).
  (* the facts every reac_code_emit call of this function has *)
  assert (HEF : srm_emit_facts SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (ablocks B ly3 S3) k0 (srm_name cx) s).
  { unfold srm_emit_facts. rewrite HA0.
    split; [lia|]. split; [exact HINF|]. split; [exact HMF|]. split; [exact HFIT|]. split; [exact HAMF|].
    split.
    { exact (blk_off_imgP (PI := PI) B ly3 S3 W3 (ms_mem ms3) md3 (sm_sink cx) AMF_BLOCK
               (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) HINF). }
    split; [exact Ha4|]. split; [exact Hn0|]. split; [exact NC|]. split; [exact NL|]. split; [exact NRT|].
    split; [apply srm_apart_sym; exact NF|].
    exact (conj PL1 (conj PL2 (conj PL3 (conj PL4 (conj PL5 PL6))))). }
  (* the callee's Pre at .str.3, and the format its Post is instantiated with *)
  destruct (srm_emit_pre_read SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (ablocks B ly3 S3) k0 (srm_name cx) s
              HEF HA3 PR3a PR3r) as (fmt & ps & args & T & HFMT & HLEN & HPC).
  (* the callee's apre, read set, Pre *)
  assert (HAP : apre SK SEGS PCAP_RLO PCAP_RHI B Kc 0 [(0, 1)]
     (reac_code_emit_awr (ms_regs ms3) (rdW W3 (ms_mem ms3))) (sm_G cx) (sm_XO cx) (sm_OUT cx) (sm_STK cx)
     (sm_sp0 cx) (sm_FP cx) (sm_ly cx) (sm_S cx) (sm_W0 cx) (sm_mem0 cx) (sm_md0 cx) ((SRM_CID, fpos) :: sm_own cx)
     ly3 S3 W3 (ms_mem ms3) md3 (sm_k cx) (ms_regs ms3)).
  { apply (srm_call_apre SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 Kc [(0, 1)] _ HPRE HB HXE HKc).
    - rewrite Hra. apply ret_ok_codeptr_v; unfold SRM_CUT_RESTORE, AF_reac_served_mark; lia.
    - unfold raZ. rewrite Hra. pose proof (pa_base_lo (PL := PL_link) (PI := PI)) as HBL.
      pose proof (pa_B_ok (PAImg := PI)) as (HB1 & HB2 & _).
      rewrite unsigned_lit_small; unfold SRM_CUT_RESTORE, AF_reac_served_mark in *; lia.
    - intros cd [<- | []]. exists 1. split; [right; right; right; left; reflexivity | cbn; lia].
    - intros a (r & [<- | []] & Hr). left. unfold srm_E, srm_wr, reac_served_mark_awr.
      exists (aivl (sm_sink cx) AMF_BLOCK). split; [right; right; left; reflexivity|].
      rewrite HA0 in Hr. exact Hr. }
  assert (HRD : forall a, reac_code_emit_ard SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) a ->
     akb SEGS B ly3 S3 (spZ (ms_regs ms3) - Kc) (spZ (ms_regs ms3)) a).
  { intros a Ha.
    pose proof (srm_acstr_range SEGS _ _ _ NC) as NCR.
    destruct (srm_emit_rd_read SEGS (ms_regs ms3) (rdW W3 (ms_mem ms3)) (srm_name cx) a PR3a Ha4
                ltac:(lia) HA3 Ha) as [(s' & Hs' & Hn) | Hl].
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
  unfold srm_post. eapply (srr_apostF_lift SK SEGS B fx fx'); [exact Hfx|].
  apply (HRA fx' cx fpos ly4 S4 W4 _ md4 HPRE HGSP).
  exists (r_rc R).
  split; [cbn [ms_pc_val mkst]; rewrite Hra; reflexivity|].
  split.
  { cbn [ms_regs mkst]. pose proof (HPR 21 ltac:(unfold acallee_saved; lia)) as H21.
    rewrite <- Hs5. exact H21. }
  split; [|exact HB4].
  (* the Post at the RESTORE cut: the kernel and the marks as at RRET (the call writes only the FILE block),
     the FILE with EMIT_HEAD + |T| more bytes *)
  pose proof HB4 as HB4'.
  destruct HB4' as (_ & _ & _ & _ & _ & HJ4 & _).
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4) as HAR4.
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
  (* the table strings: the entry's view at both ends *)
  assert (HTL : (length tab <= 80)%nat).
  { destruct HNLK as (_ & _ & _ & _ & _ & (_ & HTl & _) & _). lia. }
  assert (HTABV : forall i n2 ix p, nth_error tab i = Some (n2, ix) ->
     au64_at SEGS (rdW W3 (ms_mem ms3)) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p -> 0 <= p < 2 ^ 64 ->
     forall a, p <= a <= p + Z.of_nat (length n2) ->
       aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros i n2 ix p Hi Hp Hpr a Ha.
    assert (Hi80 : Z.of_nat i < 80).
    { assert (Hlt : (i < length tab)%nat) by (apply nth_error_Some; rewrite Hi; discriminate). lia. }
    assert (Hp4 : au64_at SEGS (rdW W4 mem4) (LA_G_NL + NK_IF_NAME + 8 * Z.of_nat i) p).
    { apply (srm_val_mem_move SEGS (w_H W3) (w_H W4) (ms_mem ms3) mem4 _ 8 p); [|exact Hp].
      intros x Hx.
      assert (Hx' : LA_G_NL + NK_IF_NAME <= x < LA_G_NL + NK_SIZE) by (unfold NK_IF_NAME, NK_SIZE in *; lia).
      pose proof (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos _ ly4 S4 W4 _ md4 _ HPRE HB4 HXE Hx') as G4.
      pose proof (srm_gtab_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 _ HPRE HB HXE Hx') as G3.
      cbn [ms_mem mkst] in G4. rewrite G4, G3. reflexivity. }
    pose proof (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fx' cx fpos _ ly4 S4 W4 _ md4 kbs tab i n2 ix p a
               HPRE HB4 HXE HNLK Hi Hp4 Hpr Ha) as T4.
    cbn [ms_mem mkst] in T4. rewrite T4.
    rewrite (srm_table_view SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 kbs tab i n2 ix p a
               HPRE HB HXE HNLK Hi Hp Hpr Ha).
    reflexivity. }
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
  replace (r_rc R) with (m_rc (mark_lib tab (Some s) (mk_names gbs) (nk_sent kbs) (nk_kstate kbs)))
    by (rewrite (srm_mark_readfail s kbs tab gbs Hs HRN); reflexivity).
  eapply srm_pf_of; [exact HENT | reflexivity | | | exact HGWF | | exact HMF4 | unfold EMIT_HEAD in *; lia].
  - rewrite (srm_mark_readfail s kbs tab gbs Hs HRN). cbn [m_state m_reqs].
    apply (srm_kern_mono _ _ _ _ _ _ 1 2); [lia|].
    eapply xfer_kern; solve [exact LAWS | exact HSEGS | exact TB | exact HAK | exact HGNE | exact HTABV
                             | exact HKERN].
  - eapply xfer_amarks; solve [exact LAWS | exact HSEGS | exact TB | exact HAK | exact HAR4 | exact HMK3
                               | exact HMK4 | exact HMKNE | exact HMK].
  - rewrite (srm_mark_readfail s kbs tab gbs Hs HRN). reflexivity.
Qed.

(* ---- the segment: srm_restore_all -> srm_dec_obl -> srm_rret_obl ---- *)
Theorem srm_rret : srm_restore_all SK B -> srm_dec_obl fx SK B -> srm_rret_obl fx SK B.
Proof.
  intros HRA HDEC cx fpos ly3 S3 W3 ms3 md3 HPRE HGSP HGI.
  destruct HGI as (s & kbs & tab & gbs & k0 & kbs1 & HGI). cbv zeta in HGI.
  destruct HGI as (Hpc & HENT & Ha0 & Hs5 & Hs7 & Hs8 & HKERN & HBUFS & HMK & HMF & HBASE).
  assert (HXE : forall a, srm_E cx a -> srm_E cx a) by (intros a Ha; exact Ha).
  destruct (srm_gsay_at SK B LAWS TB RELRO_IMG HSEGS fx cx fpos _ ly3 S3 W3 ms3 md3 HPRE HBASE HXE)
    as (HSAY & HSK1 & HSK2 & HSK3).
  apply (srm_rret_run cx fpos ly3 S3 W3 ms3 md3 s kbs tab gbs k0 _ HPRE Hpc HENT Ha0 HBASE HSAY
           ltac:(lia)).
  - intros ms' md' HR0 Hpc' Hm' HRG HB'.
    apply (HDEC cx fpos ly3 S3 W3 ms' md' HPRE HGSP).
    exists s, kbs, tab, gbs, k0, kbs1. cbv zeta. rewrite Hm'.
    split; [exact Hpc'|]. split; [exact HENT|]. split; [exact HR0|].
    split; [rewrite HRG by (cbn; auto 20); exact Hs7|]. split; [rewrite HRG by (cbn; auto 20); exact Hs8|].
    split; [exact HKERN|]. split; [exact HBUFS|]. split; [exact HMK|]. split; [exact HMF | exact HB'].
  - intros ms' md' HRN Hsh Hm' Ha0' Ha3' Ha4' Hs5' Hra' HB'.
    pose proof HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs4 & _).
    rewrite Hs4 in Ha4'.
    rewrite <- Hm' in HKERN, HMK, HMF.
    exact (srm_rret_emit cx fpos ly3 S3 W3 ms' md' s kbs tab gbs k0 kbs1 HRA HPRE HGSP HENT HRN HKERN HMK HMF
             Hsh Ha0' Ha3' Ha4' Hs5' Hra' HB').
Qed.

End b.
End a.

About srm_rret.
Print Assumptions srm_rret.
