(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/B/Prog/NextEntry.v, with its module paths and module names changed; 542 of its 591 lines of code are new or changed and 711 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_link_alias_readExit.v, with its module names changed; 424 of its 471 lines of code are new or changed and 544 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100) on image A, the SEND piece's second half: from the RQ cut (+0x1d8, the request
   built in the side frame, checked_memcpy returned) to the EXIT cut (+0x210) (cut interface lib/A/Prog/model_writeDefs.v;
   listing (internal path) (internal record, sha256 2152d78b142c)):
     +0x1d8..+0x1f4  a0 := s4 (m), a1 := s9 (the request), a2 := s10 (its length), a3..a6 := 0: a plain run to the
                     call of talk
     +0x1f4          talk: the own callee's contract (talk_c.v) at the empty relro window (model_writeCall.v), its
                     Pre from the entry Pre carried to the call and from the request the code built (the RQ cut)
     +0x1f8..+0x204  s8 := a0, a0 := s7 (the request's shadow), a1 := 64: a plain run to meta_fill_f8
     +0x204          meta_fill_f8: LinkWalkSide.v aj_gx_set_shadow_at (the request's shadow out of scope again)
     +0x208          `j` to the EXIT cut (a plain run)
   The EXIT cut's result clause is model_writeSendA.v mw_pf_talk from talk's Post.

   Section hypotheses: LAWS, TB, HSEGS, LV, MFF8 (meta_fill_f8's contract, lib/A/Rt/SetShadow.v link_set_shadow_f8),
   TALK (talk's contract at every rlo rhi; discharge: talk_aproof).

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC88 LinkWalk LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkShadow LinkWalkCall LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs model_writeKit model_writeStep model_writeArmsA model_writeCut
model_writeCall model_writeArmsB model_writeArmsC model_writeArmsD model_writeSendA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Definition MW_RQ : Z := AF_model_write + 0x1d8.    (* the return address of checked_memcpy *)
Definition MW_TK : Z := AF_model_write + 0x1f8.    (* the return address of talk *)
Definition MW_F8 : Z := AF_model_write + 0x208.    (* the return address of meta_fill_f8 *)

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : SEGS = tfibsegs.
Set Default Proof Using "All".

(* ---- the RQ cut: the request is built ---- *)
Definition mw_gi_rq (cx : mwcx) (fpos : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
    (ms3 : machine_state) (md3 : Model) : Prop :=
  exists sn sa tab kbs,
  ms_pc_val ms3 = w64 (BASE + MW_RQ) /\
  anlk_at SEGS (mw_m0 cx) LA_G_NL kbs /\ aiftab_at SEGS (mw_m0 cx) LA_G_NL kbs tab /\
  acstr_at SEGS (mw_m0 cx) (mw_name cx) sn /\ mw_name cx <> 0 /\ sn <> [] /\
  acstr_at SEGS (mw_m0 cx) (mw_alias cx) sa /\ mw_alias cx <> 0 /\
  Z.of_nat (length sa) < ALIAS_MAX /\ index_of tab sn <> 0 /\
  getr (ms_regs ms3) 25 = w64 (mw_F cx fpos + 32) /\
  getr (ms_regs ms3) 26 = w64 (32 + nl_align (RTA_HDR + Z.of_nat (length sa))) /\
  abytes SEGS (rdW W3 (ms_mem ms3)) (mw_F cx fpos + 32) (req_write (index_of tab sn) sa) /\
  (forall j, 4 <= j < 68 -> aview SEGS (w_H W3) (ms_mem ms3) (mw_SH cx fpos + j) = Some 0) /\
  mw_base SK B cx fpos NoX ly3 S3 W3 ms3 md3.

(* the base across a stretch that writes nothing, at any exception set *)
Lemma mw_base_nomemX : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 (ms : machine_state) md,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 ->
  ms_mem ms = ms_mem ms3 ->
  ms_resv ms = None -> ms_svc_pending ms = None -> ms_rom ms = seg_rom SEGS ->
  ms_fregs ms = fp_regs -> ms_fcsr ms = fp_csr ->
  ajournal_gx SEGS B (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
    (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx)
    ly3 S3 W3 (ms_mem ms) md (mw_k cx) ->
  m_fds md = m_fds md3 -> m_fs md = m_fs md3 ->
  mw_rsame (ms_regs ms3) (ms_regs ms) ->
  mw_base SK B cx fpos X ly3 S3 W3 ms md.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 ms md HPX HB Hmem H1 H2 H3 H4 H5 HJ Hfd Hfs HR.
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
  pose proof asan_consts as ((C1a & C1b) & _).
  apply (mw_base_step SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 ly3 S3 W3 ms md (mw_sp1 cx) (mw_sp1 cx) NoX
           HPX HB H1 H2 H3 H4 H5 HJ eq_refl).
  - unfold mw_base in HB. cbv zeta in HB. tauto.
  - unfold mw_base in HB. cbv zeta in HB. tauto.
  - rewrite Hmem. apply (akept_refl SK SEGS B LAWS pa_segs_low). intros a Ha. lia.
  - lia.
  - lia.
  - intros a [].
  - intros a _ [].
  - intros a _ [].
  - exact HR.
  - exact Hfd.
  - exact Hfs.
Qed.

(* a byte of the model block is writable at every cut *)
Lemma mw_base_blk_writable : forall cx fpos (X : Z -> Prop) ly3 S3 W3 (ms3 : machine_state) md3 a,
  mw_pre SK B cx -> mw_base SK B cx fpos X ly3 S3 W3 ms3 md3 -> mw_E cx a ->
  writable_at SEGS (rdW W3 (ms_mem ms3)) a.
Proof.
  intros cx fpos X ly3 S3 W3 ms3 md3 a HPX HB HE.
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos X ly3 S3 W3 ms3 md3 HPX HB) as (_ & _ & Hbl & _ & Hfa & _).
  eapply mw_blk_writable with (cx := cx) (own' := (MW_CID, fpos) :: mw_own cx) (ly' := ly3) (S' := S3) (W' := W3)
    (m' := ms_mem ms3) (k' := mw_k cx).
  all: first
    [ exact LAWS | exact HSEGS | exact HPX | exact (mw_base_jx SK B cx fpos X ly3 S3 W3 ms3 md3 HB) | exact Hfa
    | exact Hbl | intros y Hy; right; exact Hy | exact HE ].
Qed.

Lemma mw_blk_in : forall cx a, mw_m cx <= a < mw_m cx + MD_SIZE -> mw_E cx a.
Proof.
  intros cx a Ha. unfold mw_E, mw_wr, model_write_awr. exists (mw_m cx, mw_m cx + MD_SIZE).
  split; [left; reflexivity | exact Ha].
Qed.

(* an argument register's value *)
Lemma mw_aarg : forall (regs : bvmap 5 word) k (r : bv 5) v,
  Z_to_bv 5 (10 + k) = r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> aarg regs k = v.
Proof.
  intros regs k r v Hr Hg Hv. unfold aarg, argZ. rewrite Hr, Hg. unfold w64. apply unsigned_lit_small. exact Hv.
Qed.

Lemma mw_blk_akb' : forall cx a, mw_pre SK B cx -> mw_m cx <= a < mw_m cx + MD_SIZE ->
  akb SEGS B (mw_lyc cx) (mw_Sc cx) (mw_sp cx - MODEL_WRITE_AK) (mw_sp cx) a.
Proof. intros cx a HPX Ha. eapply mw_blk_akb; try eassumption; exact (mw_blk_in cx a Ha). Qed.

Lemma mw_blk_not_side' : forall cx fpos a, mw_pre SK B cx -> 0 <= fpos < fs_frames MW_CID ->
  ~ In (MW_CID, fpos) (frames (mw_Sc cx)) -> mw_m cx <= a < mw_m cx + MD_SIZE ->
  ~ aside_rng (mw_lyc cx) MW_CID fpos a.
Proof. intros cx fpos a HPX Hp Hn Ha. eapply mw_blk_not_side; try eassumption; exact (mw_blk_in cx a Ha). Qed.

Hypothesis LV : LinkVals.
(* meta_fill_f8 (0x55f94): lib/A/Rt/SetShadow.v link_set_shadow_f8 *)
Hypothesis MFF8 : aset_shadow_realizes SEGS B (pa_sigma LS___asan_set_shadow_f8) 0xf8.
(* talk (0x8763c): talk_c.v, at every rlo rhi *)
Hypothesis TALK : forall rlo rhi, talk_acontract SK SEGS rlo rhi B.

Lemma mw_rq : mw_exit_obl SK B -> mw_from SK B mw_gi_rq.
Proof.
  intros EXIT cx fpos ly3 S3 W3 ms3 md3 HPX HRQ.
  destruct HRQ as (sn & sa & tab & kbs & Hpc & HNK & HIT & HSN & Hn0 & Hsn & HSA & Ha0 & HAL & Hidx & R25 & R26
                   & HREQ & HSHZ & HB).
  pose proof (mw_base_shape SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HB) as (Hrv & Hsv & Hrom & Hfr & Hfc).
  pose proof (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms3 md3 HB) as HJ3.
  pose proof HPX as (HAPRE & HRD & HP).
  assert (HGx : gx_ok SEGS B (mw_G cx)) by (unfold apre in HAPRE; tauto).
  pose proof (mw_sp_facts SK B LAWS TB HSEGS cx HPX) as HSPF.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. assert (HKt : TALK_AK = 4240) by reflexivity.
  assert (HKi : INDEX_OF_AK = 8272) by reflexivity.
  pose proof HP as (mbs0 & kbs0 & tab0 & nm0 & al0 & HM0 & HWF0 & HN0 & HNW0 & HT0 & _ & _ & _ & _ & _ & _ & _
                    & HRM0 & HHM0 & HMR0 & _ & _ & HGM0 & HFM0 & _).
  rewrite (mw_anlk_unique SEGS (mw_m0 cx) LA_G_NL kbs0 kbs HN0 HNK) in HNW0.
  destruct (mw_side_facts SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB)
    as (F1 & F2 & F3 & F4 & FL1 & FL2 & ESH & EF & EFL & HFp & HSp & HFLp & HFLi).
  unfold MW_FB in F2, F4. unfold MW_SHN in HSp.
  destruct (mw_cut_facts SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms3 md3 HPX HB)
    as (HARc & HAR3 & Hbl & Hfrs & Hfa & _ & _ & Hin3 & Hfpos & Hnin & _ & _).
  assert (HL : 0 <= Z.of_nat (length sa) < 256) by (unfold ALIAS_MAX in HAL; lia).
  assert (Hlen : 36 <= 32 + nl_align (RTA_HDR + Z.of_nat (length sa)) <= 292) by (unfold nl_align, RTA_HDR; lia).
  assert (HF8 : mw_F cx fpos mod 8 = 0).
  { apply Z.mod_divide; [lia|]. apply Z.mod_divide in F3; [|lia]. destruct F3 as [q Hq]. exists (8 * q). lia. }
  assert (HEI : img_env VAL A_LIM (mwE ms3 [])) by apply Eimg_env.
  assert (Hms : ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_RQ)) (ms_mem ms3) (seg_rom SEGS))
    by (apply (mw_mkst_at ms3 MW_RQ); assumption).
  assert (Hrms : restrict (w_H W3) ms3 =
     mkst (ms_regs ms3) (Z_to_bv 64 (BASE + MW_RQ)) (mrestrict (w_H W3) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite Hms at 1. rewrite restrict_mkst_fx. reflexivity. }
  assert (HS : st_ok_pi SEGS VAL (mwE ms3 []) (mkSS MW_RQ sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W3) ms3)).
  { rewrite Hrms. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose (RUNC := paj_run_call_plain_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  (* ---- +0x1d8 .. +0x1f4: talk's arguments ---- *)
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
      lazymatch r with (?ssf, PRS_call ?sf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
        eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ3);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  cbv beta. intros ms5 mat5 HS5 HJ5 HF5 HFr5 HG5.
  cbn [ms_mem mkst] in HF5, HFr5, HG5.
  assert (Hmem5 : ms_mem ms5 = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF5. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS5 eq_refl) as Hms5. cbn [ss_pc setpc] in Hms5.
  pmkst HS5.
  prreg HS5 (1%bv : bv 5) Q1. prreg HS5 (10%bv : bv 5) Q10. prreg HS5 (11%bv : bv 5) Q11.
  prreg HS5 (12%bv : bv 5) Q12. prreg HS5 (13%bv : bv 5) Q13. prreg HS5 (14%bv : bv 5) Q14.
  prreg HS5 (15%bv : bv 5) Q15. prreg HS5 (16%bv : bv 5) Q16.
  rewrite (mwE_reg ms3 [] 20%nat 20%bv eq_refl) in Q10.
  rewrite (mwE_reg ms3 [] 25%nat 25%bv eq_refl) in Q11.
  rewrite (mwE_reg ms3 [] 26%nat 26%bv eq_refl) in Q12.
  assert (HR5 : mw_rsame (ms_regs ms3) (ms_regs ms5)) by (unfold mw_rsame; mwc_rsame HS5 ms3).
  assert (R20 : getr (ms_regs ms3) 20 = w64 (mw_m cx)).
  { pose proof HB as HB0. unfold mw_base in HB0. cbv zeta in HB0.
    destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20' & _).
    exact R20'. }
  assert (HB5 : mw_base SK B cx fpos NoX ly3 S3 W3 ms5 (with_vm_backing (m_vm_lazy md3) mat5 md3)).
  { apply (mw_base_nomemX cx fpos NoX ly3 S3 W3 ms3 md3 ms5 _ HPX HB Hmem5); try (rewrite Hms5 at 1; reflexivity).
    - exact HJ5.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md3) mat5 md3)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md3) mat5 md3)).
    - exact HR5. }
  set (md5 := with_vm_backing (m_vm_lazy md3) mat5 md3) in *.
  pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (mw_base_jx SK B cx fpos NoX ly3 S3 W3 ms5 md5 HB5)) as HAR5.
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms5 md5 HPX HB5) as Hsp5.
  assert (Hm64 : 0 <= mw_m cx < 2 ^ 47)
    by (destruct (mw_blk_facts SK B cx (mw_m cx) HPX (mw_blk_in cx (mw_m cx) ltac:(unfold MD_SIZE; lia)))
          as (_ & _ & _ & _ & H47); exact H47).
  pose proof (mw_aarg (ms_regs ms5) 0 10%bv (mw_m cx) ltac:(apply bv_eq; reflexivity) (eq_trans Q10 R20) ltac:(lia)) as A0.
  pose proof (mw_aarg (ms_regs ms5) 1 11%bv (mw_F cx fpos + 32) ltac:(apply bv_eq; reflexivity) (eq_trans Q11 R25)
    ltac:(lia)) as A1.
  pose proof (mw_aarg (ms_regs ms5) 2 12%bv (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))
    ltac:(apply bv_eq; reflexivity) (eq_trans Q12 R26) ltac:(lia)) as A2.
  assert (A3 : aarg (ms_regs ms5) 3 = 0).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 3)) with (13%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q13. reflexivity. }
  assert (A4 : aarg (ms_regs ms5) 4 = 0).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 4)) with (14%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q14. reflexivity. }
  assert (A5 : aarg (ms_regs ms5) 5 = 0).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 5)) with (15%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q15. reflexivity. }
  assert (A6 : aarg (ms_regs ms5) 6 = 0).
  { unfold aarg, argZ. replace (Z_to_bv 5 (10 + 6)) with (16%bv : bv 5) by (apply bv_eq; reflexivity).
    rewrite Q16. reflexivity. }
  (* the model block at the call *)
  assert (HVM : forall a, mw_m cx <= a < mw_m cx + MD_SIZE ->
            aview SEGS (w_H W3) (ms_mem ms5) a = aview SEGS (w_H (mw_W cx)) (mw_memc cx) a).
  { intros a Ha. apply (mw_view_akb SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms5 md5 a HPX HB5).
    exact (mw_blk_akb' cx a HPX Ha). }
  assert (HM5 : amodel_at SEGS (rdW W3 (ms_mem ms5)) (mw_m cx) mbs0).
  { apply (mw_amodel_move SEGS (mw_m0 cx) (rdW W3 (ms_mem ms5)) (mw_m cx) mbs0 HM0).
    - intros x Hx. exact (mbyte_of_aview_eq SEGS _ _ _ _ x x (HVM x Hx)).
    - intros x Hx. exact (mw_base_blk_writable cx fpos NoX ly3 S3 W3 ms5 md5 x HPX HB5 (mw_blk_in cx x Hx)). }
  destruct (mw_gnl_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms5 md5 kbs tab HPX HB5 HNK HIT) as (HNK5 & _).
  assert (HREQ5 : abytes SEGS (rdW W3 (ms_mem ms5)) (mw_F cx fpos + 32) (req_write (index_of tab sn) sa))
    by (rewrite Hmem5; exact HREQ).
  assert (HRL : Z.of_nat (length (req_write (index_of tab sn) sa)) = 32 + nl_align (RTA_HDR + Z.of_nat (length sa)))
    by apply mw_req_write_length.
  (* the request's shadow and the frame's shadow hull *)
  assert (HRA5 : range_addressable (ard SEGS (rdW W3 (ms_mem ms5))) SHADOW_OFF (mw_F cx fpos + 32)
                   (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))).
  { apply (mw_req_ra (ard SEGS (rdW W3 (ms_mem ms5))) (mw_F cx fpos) (mw_F cx fpos + 32) _ HF8 ltac:(lia)); [| lia | lia].
    intros j Hj. change (ard SEGS (rdW W3 (ms_mem ms5))) with (aview SEGS (w_H W3) (ms_mem ms5)). rewrite Hmem5.
    exact (HSHZ j Hj). }
  assert (HHV5 : shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms5))) (mw_F cx fpos + 32)
                   (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))).
  { intros x Hx. change (ard SEGS (rdW W3 (ms_mem ms5))) with (aview SEGS (w_H W3) (ms_mem ms5)).
    apply (mw_aview_present SK B LAWS TB HSEGS). rewrite Hmem5. apply HSp.
    apply Z.mod_divide in F3; [|lia]. destruct F3 as [q Hq].
    unfold shadow_addr in Hx. unfold mw_SH. rewrite Hq in Hx |- *. unfold SHADOW_OFF in *. lia. }
  destruct (mw_shadow_at SK B LAWS TB HSEGS cx fpos ly3 S3 W3 ms5 md5 (mw_m cx) MD_SIZE HPX HB5 ltac:(unfold MD_SIZE; lia)
              (fun a Ha => mw_blk_akb' cx a HPX Ha) HRM0 HHM0) as (HRM5 & HHM5).
  (* the request is apart from the block: no block byte is a byte of the side frame *)
  assert (HAP : apart (mw_F cx fpos + 32) (32 + nl_align (RTA_HDR + Z.of_nat (length sa))) (mw_m cx) MD_SIZE).
  { unfold apart.
    destruct (Z_le_gt_dec (mw_F cx fpos + 32 + (32 + nl_align (RTA_HDR + Z.of_nat (length sa)))) (mw_m cx)) as [H | H];
      [left; exact H|].
    destruct (Z_le_gt_dec (mw_m cx + MD_SIZE) (mw_F cx fpos + 32)) as [H' | H']; [right; exact H'|].
    exfalso. assert (HMD : 0 < MD_SIZE) by (unfold MD_SIZE; lia).
    destruct (Z_le_gt_dec (mw_F cx fpos + 32) (mw_m cx)) as [Hle | Hgt].
    - assert (Hx : mw_m cx <= mw_m cx < mw_m cx + MD_SIZE) by lia.
      apply (mw_blk_not_side' cx fpos (mw_m cx) HPX Hfpos Hnin Hx).
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with (mw_F cx fpos). lia.
    - assert (Hx : mw_m cx <= mw_F cx fpos + 32 < mw_m cx + MD_SIZE) by lia.
      apply (mw_blk_not_side' cx fpos (mw_F cx fpos + 32) HPX Hfpos Hnin Hx).
      left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes MW_CID) with 1024.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with (mw_F cx fpos). lia. }
  (* talk's Pre *)
  assert (HPRE5 : talk_apre SEGS (ms_regs ms5) (rdW W3 (ms_mem ms5))).
  { exists mbs0, kbs, (req_write (index_of tab sn) sa).
    rewrite A0, A1, A2, A3, A4, A5, A6.
    split; [exact HM5|]. split; [exact HWF0|]. split; [exact HNK5|]. split; [exact HNW0|].
    split; [exact HREQ5|]. split; [exact HRL|]. split; [unfold NL_SENT_LEN; lia|].
    split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
    split; [exact HRM5|]. split; [exact HHM5|]. split; [exact HMR0|].
    assert (HZ : range_addressable (ard SEGS (rdW W3 (ms_mem ms5))) SHADOW_OFF LA_G_NL NK_SIZE /\
                 shadow_hull_vis (ard SEGS (rdW W3 (ms_mem ms5))) LA_G_NL NK_SIZE)
      by (eapply zsh_gnl_ard; eassumption).
    destruct HZ as (Hgra & Hghv).
    split; [apply (mw_ra_sub _ LA_G_NL NK_SIZE); [exact Hgra | unfold NK_CHUNK; lia | unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE; lia]|].
    split; [apply (mw_hull_sub _ LA_G_NL NK_SIZE); [exact Hghv | unfold NK_CHUNK; lia | unfold NK_N_CHUNKS; lia
                                                   | unfold NK_CHUNK, NK_N_CHUNKS, NK_SIZE; lia | unfold LA_G_NL; lia]|].
    split; [unfold amem_range, MW_FB in *; unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; destruct F4; lia|].
    split; [exact HRA5|]. split; [intros _; exact HHV5|]. split; [exact HAP|].
    split; [intros H0; exfalso; exact (H0 eq_refl)|]. split; [intros H0; exfalso; exact (H0 eq_refl)|].
    split; [intros H0; exfalso; exact (H0 eq_refl)|].
    split; [exact HGM0|].
    split; [unfold apart_frame in *; rewrite Hsp5; unfold mw_sp, mw_m in *; lia|].
    split; [unfold apart_frame; rewrite Hsp5; unfold MW_FB in *; lia|].
    split; intros H0; exfalso; exact (H0 eq_refl). }
  assert (HRD5 : forall a, talk_ard (ms_regs ms5) (rdW W3 (ms_mem ms5)) a ->
                   akb SEGS B ly3 S3 (spZ (ms_regs ms5) - TALK_AK) (spZ (ms_regs ms5)) a).
  { intros a Ha. unfold talk_ard, rd_ivl in Ha. rewrite A1, A2 in Ha.
    apply (mw_akb_frame SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms5 md5 _ _ a HPX HB5). unfold MW_FB. lia. }
  assert (HWR5 : forall a, inFP (talk_awr (ms_regs ms5) (rdW W3 (ms_mem ms5))) a -> mw_E cx a).
  { intros a (r0 & Hin & Hr0). unfold talk_awr in Hin. rewrite A0, A3, A4, A5, A6 in Hin.
    destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd aivl Z.eqb] in Hr0; [exact (mw_blk_in cx a Hr0) | lia | lia]. }
  assert (Hret5 : YK0s.ret_ok (getr (ms_regs ms5) 1))
    by (rewrite Q1; apply ret_ok_codeptr_v; [unfold AF_model_write; lia | reflexivity]).
  assert (Hra5 : 4096 <= raZ (ms_regs ms5)).
  { unfold raZ. rewrite Q1. pose proof pa_B_ok as (HB0 & HB1 & HB2). unfold AF_model_write.
    rewrite unsigned_lit_small by lia. lia. }
  pose proof (mw_call_apre SK B LAWS TB HSEGS cx fpos NoX ly3 S3 W3 ms5 md5 TALK_AK
    (talk_awr (ms_regs ms5) (rdW W3 (ms_mem ms5)))
    HPX HB5 (fun a H => match H with end) ltac:(lia) Hret5 Hra5 HWR5) as HAPRE5.
  assert (Hsig : pa_sigma LS_talk = TALK_A) by (rewrite (lv_sigma LV); reflexivity).
  rewrite Hsig.
  eapply SRr_bind.
  { exact (TALK 0 0 (mw_G cx) (mw_XO cx) (mw_OUT cx) (mw_STK cx) (mw_sp0 cx) (mw_FP cx) (mw_ly cx) (mw_S cx)
      (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly3 S3 W3 (ms_mem ms5) md5 (mw_k cx)
      (ms_regs ms5) HAPRE5 HRD5 HPRE5). }
  intros W6 c6 _ Hpost.
  destruct (mw_call_back SK B LAWS TB HSEGS cx fpos NoX (mw_E cx) ly3 S3 W3 ms5 md5 TALK_AK _
              (talk_apost SEGS (ms_regs ms5) (rdW W3 (ms_mem ms5))) W6 c6 HPX HB5 ltac:(lia)
              (fun a H => match H with end) HWR5 (fun a H => H) Hpost)
    as (ly6 & S6 & regs6 & mem6 & md6 & -> & HB6 & KEEP6 & HK6 & HTK).
  destruct (HTK mbs0 kbs (req_write (index_of tab sn) sa) ltac:(rewrite A0; exact HM5) HNK5
              ltac:(rewrite A1; exact HREQ5) ltac:(rewrite A2; exact HRL)) as (HRC6 & HNL6 & _).
  cbv zeta in HRC6, HNL6. rewrite A0 in HNL6.
  pose proof HB6 as HB60. unfold mw_base in HB60. cbv zeta in HB60.
  destruct HB60 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R23_6 & _).
  (* ---- +0x1f8 .. +0x204: s8 := a0, the call of meta_fill_f8 ---- *)
  set (ms6 := mkst regs6 (getr (ms_regs ms5) 1) mem6 (seg_rom SEGS)) in *.
  assert (HEI6 : img_env VAL A_LIM (mwE ms6 [])) by apply Eimg_env.
  assert (Hrms6 : restrict (w_H W6) ms6 =
     mkst regs6 (Z_to_bv 64 (BASE + MW_TK)) (mrestrict (w_H W6) mem6) (seg_rom SEGS)).
  { unfold ms6. rewrite restrict_mkst_fx, Q1. reflexivity. }
  assert (HS6 : st_ok_pi SEGS VAL (mwE ms6 []) (mkSS MW_TK sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W6) ms6)).
  { rewrite Hrms6. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose proof (mw_base_jx SK B cx fpos (mw_E cx) ly6 S6 W6 ms6 md6 HB6) as HJ6.
  lazymatch type of HS6 with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
      let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
      lazymatch r with (?ssf, PRS_call ?sf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
        eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI6 HS6 Hrun HJ6);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  cbv beta. intros ms7 mat7 HS7 HJ7 HF7 HFr7 HG7.
  cbn [ms_mem mkst] in HF7, HFr7, HG7.
  assert (Hmem7 : ms_mem ms7 = ms_mem ms6).
  { apply functional_extensionality. intros x. apply HF7. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_restrict_mkst SEGS _ _ _ _ HS7 eq_refl) as Hms7. cbn [ss_pc setpc] in Hms7.
  pmkst HS7.
  prreg HS7 (1%bv : bv 5) T1. prreg HS7 (10%bv : bv 5) T10. prreg HS7 (11%bv : bv 5) T11.
  prreg HS7 (24%bv : bv 5) T24.
  rewrite (mwE_reg ms6 [] 23%nat 23%bv eq_refl) in T10.
  rewrite (mwE_reg ms6 [] 10%nat 10%bv eq_refl) in T24.
  assert (HR7 : mw_rsame (ms_regs ms6) (ms_regs ms7)) by (unfold mw_rsame; mwc_rsame HS7 ms6).
  assert (HB7 : mw_base SK B cx fpos (mw_E cx) ly6 S6 W6 ms7 (with_vm_backing (m_vm_lazy md6) mat7 md6)).
  { apply (mw_base_nomemX cx fpos (mw_E cx) ly6 S6 W6 ms6 md6 ms7 _ HPX HB6 Hmem7);
      try (rewrite Hms7 at 1; reflexivity).
    - exact HJ7.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md6) mat7 md6)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md6) mat7 md6)).
    - exact HR7. }
  set (md7 := with_vm_backing (m_vm_lazy md6) mat7 md6) in *.
  pose proof (mw_base_sp SK B LAWS TB HSEGS cx fpos (mw_E cx) ly6 S6 W6 ms7 md7 HPX HB7) as Hsp7.
  pose proof HB7 as HB70. unfold mw_base in HB70. cbv zeta in HB70.
  destruct HB70 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HfS7 & Hperm7 & _ & Hfa7 & _ & _ & _ & _ & _ & _ & _ & _ & _
                    & R3_7 & R4_7 & _).
  (* ---- +0x204: meta_fill_f8(the request's shadow, 64) ---- *)
  eapply SRr_bind.
  { eapply (aj_gx_set_shadow_at SK SEGS B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f8) 0xf8 MFF8
      (mw_G cx) (mw_XO cx) (mw_OUT cx) W6 (ms_regs ms7) (ms_mem ms7) (mw_STK cx) (mw_sp0 cx) (mw_FP cx)
      (mw_ly cx) (mw_S cx) (mw_W0 cx) (mw_mem0 cx) (mw_md0 cx) ((MW_CID, fpos) :: mw_own cx) ly6 S6 md7 (mw_k cx)
      4 fpos (mw_SH cx fpos + 4) 64 (getr (ms_regs ms7) 1) HGx HJ7 (or_introl eq_refl)).
    - exact (eq_trans T10 R23_6).
    - rewrite T11. reflexivity.
    - lia.
    - rewrite (Hfa7 4 fpos). change (frame_addr (mw_lyc cx) 4 fpos) with (mw_F cx fpos). rewrite <- ESH. lia.
    - rewrite (Hfa7 4 fpos). change (frame_addr (mw_lyc cx) 4 fpos) with (mw_F cx fpos). rewrite <- ESH.
      change (fs_frame_bytes 4 / 8) with 128. lia.
    - rewrite Hsp7. lia.
    - rewrite Hsp7, (eq_refl : ESTACK = 4096). unfold mw_sp in *. lia.
    - rewrite Hsp7. unfold mw_sp in *. lia.
    - rewrite R3_7. pose proof HAPRE as (_ & _ & _ & _ & _ & Hgp & _). exact Hgp.
    - rewrite R4_7. pose proof HAPRE as (_ & _ & _ & _ & _ & _ & Htp & _). exact Htp.
    - reflexivity.
    - rewrite T1. apply ret_ok_codeptr_v; [unfold AF_model_write; lia | reflexivity]. }
  cbv beta. intros W8 c8 _ (-> & regs8 & mem8 & md8 & -> & HJ8 & HP8 & Hset8 & Hun8 & Hpres8 & Hsm8).
  set (ms8 := mkst regs8 (getr (ms_regs ms7) 1) mem8 (seg_rom SEGS)) in *.
  assert (HB8 : mw_base SK B cx fpos (mw_E cx) ly6 S6 W6 ms8 md8).
  { pose proof (ajournal_gx_AR SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mw_base_jx SK B cx fpos _ _ _ _ _ _ HB7)) as HAR7.
    apply (mw_base_step SK B LAWS TB HSEGS cx fpos (mw_E cx) ly6 S6 W6 ms7 md7 ly6 S6 W6 ms8 md8 (mw_sp1 cx) (mw_sp1 cx)
             (fun a => mw_SH cx fpos + 4 <= a < mw_SH cx fpos + 4 + 64) HPX HB7); try reflexivity.
    - exact HJ8.
    - exact HfS7.
    - exact Hperm7.
    - apply (mw_akept_un SK B LAWS TB HSEGS ly6 S6 W6 (ms_mem ms7) md7 mem8 (mw_sp1 cx) (mw_sp1 cx) _ HAR7);
        [lia | lia | intros a Ha; lia | | ].
      + intros a Ha Hn _. exact (Hun8 a Ha Hn).
      + intros a _ Hp. exact (Hpres8 a Hp).
    - unfold mw_sp in *. lia.
    - intros a Ha. right. right. left. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes MW_CID / 8) with 128.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with (mw_F cx fpos). cbv beta in Ha. rewrite ESH in Ha.
      unfold shadow_addr in Ha. lia.
    - intros a Ha Hs. cbv beta in Hs. rewrite ESH in Hs. unfold shadow_addr in Hs. unfold mw_sp in *.
      unfold SHADOW_OFF, MW_FB, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    - intros a Ha Hs. cbv beta in Hs. rewrite ESH in Hs. unfold shadow_addr in Hs. unfold MW_FLAGPTR in Ha.
      unfold SHADOW_OFF, MW_FB, kLowMemEnd, kHighMemBeg in *. destruct F4; lia.
    - exact (mw_rsame_of_pres SK B LAWS TB HSEGS _ _ HP8).
    - exact (proj1 (mw_sbm_fds2 _ _ Hsm8)).
    - exact (proj2 (mw_sbm_fds2 _ _ Hsm8)). }
  (* ---- +0x208: `j` to the EXIT cut ---- *)
  assert (HEI8 : img_env VAL A_LIM (mwE ms8 [])) by apply Eimg_env.
  assert (Hrms8 : restrict (w_H W6) ms8 =
     mkst regs8 (Z_to_bv 64 (BASE + MW_F8)) (mrestrict (w_H W6) mem8) (seg_rom SEGS)).
  { unfold ms8. rewrite restrict_mkst_fx, T1. reflexivity. }
  assert (HS8 : st_ok_pi SEGS VAL (mwE ms8 []) (mkSS MW_F8 sr_atoms [] None (mkFacts [] [] []))
                 (restrict (w_H W6) ms8)).
  { rewrite Hrms8. apply pa_entry_st_ok_full.
    - apply regs_ok_Eimg_Ereg.
    - vm_compute; reflexivity.
    - constructor.
    - exact I.
    - split; [exact I | split; exact I]. }
  pose (RUNTOP := paj_run_to_plain_x SK B LAWS (mw_G cx) HGx (mw_XO cx) (mw_OUT cx)).
  lazymatch type of HS8 with
  | st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    lazymatch type of RUNTOP with context [sym_run_toN_pi ?tpi _ _ _] =>
      let r := eval vm_compute in (sym_run_toN_pi tpi FUEL MW_CUT_EXIT ssx) in
      lazymatch r with (?ssf, ?stf) =>
        let Hrun := fresh "Hrun" in
        assert (Hrun : sym_run_toN_pi tpi FUEL MW_CUT_EXIT ssx = (ssf, stf)) by (vm_compute; reflexivity);
        eapply (RUNTOP Wx FUEL MW_CUT_EXIT Ev ssx ssf stf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI8 HS8 Hrun I HJ8);
        clear Hrun
      end
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  cbv beta. intros ms9 mat9 HS9 HJ9 HF9 HFr9 HG9.
  cbn [ms_mem mkst] in HF9, HFr9, HG9.
  assert (Hmem9 : ms_mem ms9 = ms_mem ms8).
  { apply functional_extensionality. intros x. apply HF9. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  pose proof (st_ok_pi_restrict_mkst (w_H W6) _ _ _ HS9 eq_refl) as Hms9.
  prreg HS9 (24%bv : bv 5) U24. rewrite (mwE_reg ms8 [] 24%nat 24%bv eq_refl) in U24.
  assert (HR9 : mw_rsame (ms_regs ms8) (ms_regs ms9)) by (unfold mw_rsame; mwc_rsame HS9 ms8).
  assert (HB9 : mw_base SK B cx fpos (mw_E cx) ly6 S6 W6 ms9 (with_vm_backing (m_vm_lazy md8) mat9 md8)).
  { apply (mw_base_nomemX cx fpos (mw_E cx) ly6 S6 W6 ms8 md8 ms9 _ HPX HB8 Hmem9);
      try (rewrite Hms9 at 1; reflexivity).
    - exact HJ9.
    - exact (proj1 (wvb_fds_fs (m_vm_lazy md8) mat9 md8)).
    - exact (proj2 (wvb_fds_fs (m_vm_lazy md8) mat9 md8)).
    - exact HR9. }
  (* ---- the EXIT cut ---- *)
  apply (EXIT cx fpos ly6 S6 W6 ms9 _ HPX).
  split; [rewrite Hms9 at 1; reflexivity|].
  split; [exact HB9|].
  assert (R24_9 : getr (ms_regs ms9) 24 = w64 (talk_rc_model (md_kstate mbs0 kbs))).
  { etransitivity; [exact U24|]. change (ms_regs ms8) with regs8.
    etransitivity; [exact (HP8 24 ltac:(unfold acallee_saved; lia))|].
    etransitivity; [exact T24|]. exact HRC6. }
  rewrite R24_9.
  apply (mw_pf_talk cx W6 (ms_mem ms9) mbs0 kbs tab sn sa HM0 HNK HIT HSN Hn0 Hsn HSA Ha0 HAL Hidx).
  destruct HNL6 as (mbs' & N1 & Nrest).
  exists mbs'. split; [|exact Nrest].
  apply (mw_amodel_move SEGS (rdW W6 mem6) (rdW W6 (ms_mem ms9)) (mw_m cx) mbs' N1).
  - intros x Hx. apply (mbyte_of_aview_eq SEGS _ _ _ _ x x). rewrite Hmem9. change (ms_mem ms8) with mem8.
    assert (Hns : ~ aside_rng (mw_lyc cx) MW_CID fpos x) by exact (mw_blk_not_side' cx fpos x HPX Hfpos Hnin Hx).
    rewrite (Hun8 x ltac:(unfold MD_SIZE in *; lia)).
    + rewrite Hmem7. reflexivity.
    + intros Hq. apply Hns. right. left. unfold in_zr, shadow_addr. cbn [fst snd].
      change (fs_frame_bytes MW_CID / 8) with 128.
      change (frame_addr (mw_lyc cx) MW_CID fpos) with (mw_F cx fpos). rewrite ESH in Hq. unfold shadow_addr in Hq. lia.
  - intros x Hx. exact (mw_base_blk_writable cx fpos (mw_E cx) ly6 S6 W6 ms9 _ x HPX HB9 (mw_blk_in cx x Hx)).
Qed.

End b.
End a.
