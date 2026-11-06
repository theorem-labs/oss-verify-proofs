(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L4A.v, with its module paths and module names changed; 300 of its 745 lines of code are new or changed and 262 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102, PIN sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4):
   SEGMENT L4 of LLVMFuzzerTestOneInput (entry 0x815e0), proved against lib/A/Ent102CutsA.v's `seg_L4_stmt`
   (cut_caw E fk -> cut_free E fk \/ cut_crs0 E fk \/ exists t D, cut_acc E fk t D), at the EXACT room position:
     +0x1b8  beqz a0, +0x2c8       r = check_as_written's return; cut_caw states only r = 0 (the record keeps only
                                    the no-refusal arms after cut_cno), so the branch is taken and FREE is not reached.
     +0x2c8  sub s7, s9, s7         took = count after - count before = calls tr = ck_ncalls x
     +0x2cc  beqz s8, +0x2f8        rc = 0: the accepted arm (+0x2f8 = cut_acc, at cut_caw's index: no event).
                                    rc = -1: falls through to the refused tail
     +0x2d0 .. +0x2dc  mv a0,s8; mv a1,s5; mv a2,s6; jal check_reject_clean     (the kit's tcheck_reject_clean_specX; no
                                    event, S' = S, so the index is kept)
     +0x2e0 .. +0x2f0  mv a0,s4; mv a1,s3; mv a2,s7; mv a3,zero; jal check_reject_clean_starved
                                    (doc = 0, CTX0 = ec_ctx0; its run premise `ck_crcs_evs (e_sm E) x took 0 JNull` is
                                    SUPPLIED from the call's run - Ent102L4ADefs.v l4_supply_rej: Ent102PosA's
                                    ec_supply_run, ec_call_evs_ranout_false and call_tail's None arm - through the
                                    BRIDGE l4_rej_bridge: that list is ec_rej E when e_sm E = jr_strtod)
     +0x2f4  the return site = EC_AR_CRS0 = cut_crs0, at cut_caw's index + |ec_rej E| (l4_idx_crs0).
   STATEMENT: lib/A/Ent102CutsA.v blob 2fb50b636f51 (a working branch 83576a163e5b, statements of CUT STABLE
   2ab248e3b164: the exact room position of 5e3a8d7d8a3b, its record fix 9a4f89c34639 - e_sm E = jr_strtod in ec_pre,
   cut_caw at r = 0 only, cut_crs0 at ran = 0 with `e_n E <= EC_NMAX /\ fst (jr_run (e_sm E) (e_x E) []) = None`,
   ech_noref - the decff kit sync eb783552c019 (the ledger's `.. ran most own`), ei_empty over both image bounds, the
   segments over `ec_hyps (e_dw E)` with ec_pre's `In (e_p E + e_n E) (e_dw E)`, ei_most_w);
   lib/A/Ent102PosA.v blob fd7e26dd0721 (ec_supply_run, ec_run_split, ec_call_evs_ranout_false, ec_rd_ck_read).
   LISTING: a Theorem Labs lane's whole-program listing lib/A/Listing_prog.v (blob 1ab147923c5d; slot k = byte offset 4k from the
   entry), with the PAListing PL_102_A of lib/A/Ent102PLA.v (blob a55fa7414ddf); the image half stays generic
   ({PA : PAImg A_prog_listing}; lib/A/PAImg_prog.v, PresetCfnA.v, PresetCfnB.v are not loaded, no vm_compute on pa_val /
   pa_sigma).
   The kit TEXTS (the kit of record f97c8b2f046b by path on the record): lib/A/PRH_Base.v fdb45545469b (fpre with its last
   conjunct frm_zero, FRM0-ENTRY: each call's fy from ec_at; fpostm, fpostFm, src_rd, kept_at, kept_img, prh_run_at,
   prh_ledger's named projections), lib/A/PRH_FnCheck.v 9ecd8eb167c6 (tcheck_reject_clean_specX, ck_crcs_evs,
   ck_crcs_max, LIVE_check_reject_clean_starved, RQ_crcs), lib/A/PRH_FnPj.v 908f34f0beaa (RQ_pj_parse). Proved helpers
   cited: lib/A/Ent102ReqA.v ec_rq_pj_parse, lib/Spec/PjReqBoundW.v rq_read_bound / rq_read_bound_56.
   rule 24: proves function LLVMFuzzerTestOneInput, segment L4 (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + cold/* lemma index / proof-index LLVMFuzzerTestOneInput exit=0, checker CONFIRM;
   NEW walk on the #102 pins).
   NO SECTION HYPOTHESIS (decision (A), owner 22:35Z, on the kit's pre-landing batch): the call cites ec_texts'
   et_check_reject_clean_starved = the batch kit's entry-keyed tcheck_reject_clean_starved_specX, which states the refusal arm
   DEAD (ran' = ran) under its consumer window `prh_cons_from .. rp_i (length (ck_crcs_evs ..))` and the two room-count
   bounds of the starved reading; LL4 supplies the window by Ent102Win.cons_from_at_cut and the counts by
   l4_peaks (PresetRoomCounts.peak_sec_at_tail / peak_c24_at_tail at cut_caw's position). The provisional
   ec_l4_crs_noref (GrantA's retired tcheck_reject_clean_starved_grantX) is gone.
   The refused arm's count and live budgets are ec_pay's epay_crs0 / ecov_crs0 (ech_pay, by name), at the one tree
   they fix (PjTree.JNull, the text's t at doc = 0).
   THE WILD BUDGET (the cut file's statements: ec_inv's last argument; cut_caw / cut_acc at ec_wk_caw, cut_crs0 at
   ec_wk_crs0): this row's own code and check_reject_clean (the kit's text, empty budget) store no wild trace, so cut_caw's
   budgeted journal is taken to the plain one from the entry with its depot moved to S's (Ent102CutsA.v
   ec_journal_rebase), the steps and that call run on it, and ec_journal_unbase returns it at cut_caw's budget WSc (the
   accepted arm's journal, and the caller's journal at the starved call). The batch kit's starved text is BUDGETED (its entry
   wild_room and its journal's wbudget at prh_wk F_check_reject_clean_starved): the call is Ent102L4ADefs.v
   l4_call_xbF (YCbqGwild.v aj_call_xbF_sp at a concrete entry), its room is Ent102CutsA.ec_room_at at cut_caw's
   journal (the call's S is cut_caw's: check_reject_clean keeps it), and the exit journal is at WSc ++ WS1, where
   YCbqGwild.wbudget_app gives ec_wk_caw + prh_wk F_check_reject_clean_starved = ec_wk_crs0.
   SHARED FILES CITED (by path on the record): lib/A/Prog/Ent102CallA.v (blob aefcab75548d: ec_step_branch for both
   `beqz`, ec_chain_at for both calls' frame chain, ec_ctx_call_img for the starved call's context, ec_src_home for a
   non-empty payload, ec_conj_split for ec_pre's parts by type, ec_ledger_cells for the ledger's two harness cells) and
   lib/A/Prog/Ent102L6AfLem.v (blob a37e0dc13d12: the addi / jal steps, the frame geometry, the byte and register keeps).
   TEMPLATES TAKEN (by path): the call and its post follow lib/A/Prog/Ent102L6Af.v of a working branch
   (seg_L6f_A: the registers, the window and the exit assembly from the two journals); the arm structure follows
   lib/B/Prog/EntS3B.v of a working branch 9a84f11012ba (es3_pay, es3_doc_src; old pin, its image facts
   not cited). The sub step, the concrete call rules, the doc's window and the refused tail's run supply are
   lib/A/Prog/Ent102L4ADefs.v's.
   NUMERALS: 0x1b8 / 0x1bc / 0x2c8 / 0x2cc / 0x2d0 .. 0x2f4 / 0x2f8 are this lane's slot offsets (DERIVED from the cut
   pcs EC_AR_CAW, EC_FREE, EC_REJ, EC_AR_CRC, EC_AR_CRS0, EC_ACC); 0x110 / 0x2c are the two branch offsets (read off
   the decoded slots); 128 / 120 / 104 / 56 / 32 / 16 / 8 are LENGTHs; 144 is EC_SAVE + 16; 0x300000 is EC_NMAX; 4096,
   2 ^ 26, 2 ^ 28, 2 ^ 40, 2 ^ 47, 2 ^ 62, 2 ^ 64 and the ASan band constants are the engine's and the texts' range
   facts. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK1d YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0lawscf YGcallcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive YG0scf YG0sshcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PjReqBoundW PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomCounts PresetRoom PresetLiveBounds.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnWriter.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog Ent102PLA Ent102CutsA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Ent102ReqA Ent102PosA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger Ent102L6AfLem Ent102CallA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Ent102L4ADefs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Ent102Win.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* a register copy `mv rd, rs` (= addi rd, rs, 0) and a `beqz rs` test, at the decoded slot's register fields *)
Ltac l4_mv r :=
  lazymatch goal with |- v_addi (getr _ ?rs) (bv_signed ?im) = _ =>
    replace rs with (r : bv 5) by (apply bv_eq; vm_compute; reflexivity);
    replace (bv_signed im) with 0 by (vm_compute; reflexivity) end;
  unfold v_addi; rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
(* a `beqz rs` slot's branch condition, refuted at a known register value: the hypothesis is
   `branch_taken BC_EQ (getr regs rs) (getr regs zero) = b` with the opposite value of b *)
Ltac l4_br_absurd r R :=
  let Hb := fresh "Hb" in intros Hb;
  lazymatch type of Hb with context [branch_taken _ (getr _ ?a) (getr _ ?b)] =>
    replace a with (r : bv 5) in Hb by (apply bv_eq; vm_compute; reflexivity);
    replace b with (0%bv : bv 5) in Hb by (apply bv_eq; vm_compute; reflexivity) end;
  rewrite R in Hb; vm_compute in Hb; discriminate Hb.

Section L4. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : @PAImg rc A_prog_listing}.
Variable B : asyms.
Variable SK : YI16.sink_head.
Variables EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP : Z.
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.
Variable ec_ccut : @ecx rc A_prog_listing PA -> nat -> Z.
Variable ec_lcut : @ecx rc A_prog_listing PA -> nat -> Z.

#[local] Notation SEGS := (@pa_segs rc A_prog_listing PA).
#[local] Notation VAL := (@pa_val rc A_prog_listing PA).
#[local] Notation BASE := (@pa_val rc A_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst PI).
#[local] Notation ARc := (@ec_ARx rc ci cp A_prog_listing PA B).
(* segment L4 is after check_no_overread's frees: its cuts, journals and lanes are at wle' over the fixed zone
   (Ent102CutsA.v ec_invR / ec_laneR WLE') *)
#[local] Notation WLE' := (wle' SEGS (@YGcfRehidePost.RZ_cf rc)).
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARc WLE').
#[local] Notation AJW := (ajournal_xwR (SK := SK) SEGS B PST ARc WLE').

(* THE ROOM COUNTS at the refused tail (the CONSUMER WINDOW is Ent102Win.cons_from_at_cut) (decision (A), owner 22:35Z): the batch kit's entry-keyed
   tcheck_reject_clean_starved_specX takes `prh_cons_from .. rp_i (length (ck_crcs_evs ..))` and the two pkR bounds of
   the starved reading. The window is the shared lemma Ent102Win.cons_from_after_cno (the call's events lie after
   check_no_overread's piece; an empty event list is vacuous), the counts are PresetRoomCounts.peak_sec_at_tail /
   peak_c24_at_tail at cut_caw's position (the batch kit's text, PRH_FnCheck.v:1099-1109, names this supply). *)
Lemma l4_peaks : forall (E : @ecx rc A_prog_listing PA) trp hist S,
  Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_ranout E trp = false ->
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) ->
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
    (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat (e_H0 E) hist S ->
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs (e_sm E) (e_x E) [])) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.parse_evs (e_sm E) (e_x E) [])) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV.
Proof.
  intros E [[o1 o2] o0] hist S Hn Hro Hi0 HR.
  pose proof (Ent102PosA.ec_call_evs_ranout_false _ _ _ E (o1, o2, o0) Hn Hro) as Hce.
  rewrite Hi0 in HR. split.
  - exact (PresetRoomCounts.peak_sec_at_tail (e_sm E) (e_x E) (e_os E) o1 o2 o0 (ec_cno_evs E (o1, o2, o0)) (e_H0 E)
      hist S Hce Hro HR).
  - exact (PresetRoomCounts.peak_c24_at_tail (e_sm E) (e_x E) (e_os E) o1 o2 o0 (ec_cno_evs E (o1, o2, o0)) (e_H0 E)
      hist S Hce Hro HR).
Qed.

(* a record part by name: the projection applied to the record, its explicit parameters left to unification *)
Ltac l4_get H f N :=
  first [ pose proof (f _ _ _ H) as N | pose proof (f _ _ _ _ H) as N | pose proof (f _ _ _ _ _ _ H) as N
        | pose proof (f _ _ _ _ _ _ _ H) as N | pose proof (f _ _ _ _ _ _ _ _ _ _ _ H) as N
        | pose proof (f _ H) as N | pose proof (f _ _ H) as N | pose proof (f _ _ _ _ _ H) as N
        | pose proof (f _ _ _ _ _ _ _ _ H) as N | pose proof (f _ _ _ _ _ _ _ _ _ H) as N
        | pose proof (f _ _ _ _ _ _ _ _ _ _ H) as N | pose proof (f _ _ _ _ _ _ _ _ _ _ _ _ H) as N ].

(* ---------------------------------------------------------------------- *)
(* the frame and the fake frame's flag word across a callee whose journal runs at sp = A with an empty footprint, at
   any budget WS (a plain journal is the one at []) (Ent102L6Af.v's exit assembly, by path) *)
Lemma l4_after_frame : forall (E : @ecx rc A_prog_listing PA) fk ly S Hp W mem md own pos STK1
    ly2 S2 Hp2 W2 mem2 md2 k1 WS,
  own = [(LLVMF_FS_CLASS, pos)] -> fk = frame_addr ly LLVMF_FS_CLASS pos -> In (LLVMF_FS_CLASS, pos) (frames S) ->
  YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47 -> e_sp0 E - 144 <= e_A E <= e_sp0 E - 128 -> 0 <= STK1 ->
  AJW STK1 (e_A E) [] ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 WS ->
  ec_own (L := A_prog_listing) fk ly W mem own -> ec_frame (L := A_prog_listing) E fk W mem ->
  ec_own (L := A_prog_listing) fk ly2 W2 mem2 own /\ ec_frame (L := A_prog_listing) E fk W2 mem2 /\
  In (LLVMF_FS_CLASS, pos) (frames S2) /\ fk = frame_addr ly2 LLVMF_FS_CLASS pos.
Proof.
intros E fk ly S Hp W mem md own pos STK1 ly2 S2 Hp2 W2 mem2 md2 k1 WS Ho Hfa Hin Hsp HA HS1 HJ1 HOWN Hfr.
pose proof HJ1 as (_ & Hly1 & _ & _ & _ & Hfrs1 & _ & _ & F1 & _ & _ & F4 & _).
pose proof Hly1 as (_ & _ & _ & _ & _ & EF2 & _).
assert (Hfa2 : frame_addr ly2 LLVMF_FS_CLASS pos = frame_addr ly LLVMF_FS_CLASS pos)
  by (unfold frame_addr; rewrite EF2; reflexivity).
assert (Hga2 : flag_addr ly2 LLVMF_FS_CLASS pos = flag_addr ly LLVMF_FS_CLASS pos)
  by (unfold flag_addr; rewrite EF2; reflexivity).
assert (HNF : forall a, ~ inFP [] a) by (intros a; apply inFP_nil).
destruct HOWN as (pos' & Ho' & Hfk' & Hfk0 & Hflagw). rewrite Ho in Ho'. injection Ho' as <-.
split.
{ exists pos. split; [exact Ho|]. split; [rewrite Hfa2; exact Hfa|]. split; [exact Hfk0|].
  rewrite Hga2. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hflagw].
  intros i Hi. apply (F4 LLVMF_FS_CLASS pos _ Hin).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- Hfa.
    change (fs_frame_bytes LLVMF_FS_CLASS) with 128. unfold EC_FRAME_BYTES. lia.
  - apply HNF. }
split.
{ destruct Hfr as (Hsaved & Hshv & Hal32).
  split; [|split; [|exact Hal32]].
  - assert (KS : forall a v, e_sp0 E - 104 <= a -> a + 8 <= e_sp0 E ->
      rd64 (aview SEGS (w_H W) mem) a v -> rd64 (aview SEGS (w_H W2) mem2) a v).
    { intros a v Ha1 Ha2 Hr. apply (l6f_rd64_kept (aview SEGS (w_H W) mem)); [|exact Hr].
      intros j Hj. apply F1; lia. }
    unfold ec_saved in Hsaved |- *.
    repeat (split; [apply KS; [lia | lia | exact (proj1 Hsaved)] | apply proj2 in Hsaved]).
    apply KS; [lia | lia | exact Hsaved].
  - apply (l6f_garr8_kept (w_H W) (w_H W2) mem mem2); [|exact Hshv].
    intros i Hi. change (Z.of_nat (length ec_frame_shadow)) with 16 in Hi.
    apply (F4 LLVMF_FS_CLASS pos _ Hin).
    + right. unfold in_zr. cbn [fst snd]. rewrite <- Hfa. change (fs_frame_bytes LLVMF_FS_CLASS / 8) with 16. lia.
    + apply HNF. }
split; [rewrite Hfrs1; exact Hin|].
rewrite Hfa2. exact Hfa.
Qed.

(* the stdio half and the read-only view at a state the entry's journal (footprint [], any budget WS) reaches *)
Lemma l4_entry_keep : forall (E : @ecx rc A_prog_listing PA) own ly2 S2 Hp2 W2 mem2 md2 k2 WS,
  ec_img (rc := rc) (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO
    EC_SIO_IMG ->
  EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E)) ->
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
    (aview SEGS (w_H (e_W E)) (e_mem E)) ->
  AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own ly2 S2 Hp2 W2 mem2 md2 k2 WS ->
  EC_SIO (aview SEGS (w_H W2) mem2) /\
  arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
    (aview SEGS (w_H W2) mem2).
Proof.
intros E own ly2 S2 Hp2 W2 mem2 md2 k2 WS HIMG HSIO0 HRO0 HJc.
l4_get HIMG ei_sio Hsio. l4_get HIMG ei_sio_frame Hsioframe.
l4_get HIMG ei_pst_ro Hpstro.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3c & _).
split.
- apply (Hsioframe (aview SEGS (w_H (e_W E)) (e_mem E)) (aview SEGS (w_H W2) mem2)); [|exact HSIO0].
  intros a Ha. destruct (Hsio a Ha) as ((Ho & He) & Hi & Hnp).
  apply F3c; [exact Hi | exact Ho | exact He | exact Hnp | apply fp_spares_closed; exact sink_closed_nil].
- intros a Hro Ho He.
  assert (Hi : in_img SEGS a).
  { destruct Hro as [(s & Hs & _ & Hlo & Hhi) | Hr];
    [exists s; split; [exact Hs | lia] | exact (@pa_relro_img rc A_prog_listing PA a Hr)]. }
  assert (Hsp : fp_spares (SK := SK) [] a) by (apply fp_spares_closed; exact sink_closed_nil).
  rewrite (F3c a Hi Ho He (fun Hp' => Hpstro a Hp' Hro) Hsp).
  exact (HRO0 a Hro Ho He).
Qed.

(* THE EMPTY PAYLOAD (n = 0, p = EC_EMPTY): the kit's src_rd of no byte, the range facts and the reader's text home by
   kept_at's image case (kept_img of zero bytes), from ei_empty: its YImgTop half for src_rd's range facts, its
   instance half (pa_lo / pa_hi) for kept_img. Ent102CallA.v ec_src_home covers 0 < n only. *)
Lemma l4_pay_empty : forall (E : @ecx rc A_prog_listing PA) ly S (W : world SEGS) mem,
  ec_img (rc := rc) (cp := cp) (PI := PI) (L := A_prog_listing) (PA := PA) B EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO
    EC_SIO_IMG ->
  e_n E = 0 -> e_p E = EC_EMPTY -> e_n E = Z.of_nat (length (e_x E)) ->
  0 < e_p E /\ e_p E + e_n E < 2 ^ 62 /\
  src_rd (L := A_prog_listing) (PA := PA) W mem (e_p E) (e_x E) /\
  PRH_FnReader.prhReader_home (L := A_prog_listing) (PA := PA) B ly S [] [] (e_p E) (e_n E).
Proof.
intros E ly S W mem HIMG Hn0 Hp0 Hlen.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
l4_get HIMG ei_empty Hemp. destruct Hemp as ((He1 & He2) & (Hq1 & Hq2)).
rewrite IMG_LO_val in He1. rewrite IMG_TOP_val in He2.
assert (Hx : e_x E = []) by (destruct (e_x E); [reflexivity | cbn [length] in Hlen; lia]).
rewrite Hp0, Hn0.
split; [lia|]. split; [lia|].
split.
{ unfold src_rd. rewrite Hx. cbn [length]. change (Z.of_nat 0) with 0.
  split; [apply garr8_nil|]. split; [lia|]. split; [unfold YM05.alloc_ceiling in *; lia|].
  split; [unfold amem_range, kLowMemEnd; lia|].
  split; [apply range_addressable_nil; lia | intros H; lia]. }
left. right. right. split; [lia|]. split; [lia|]. intros a Ha. lia.
Qed.

(* ---------------------------------------------------------------------- *)
Theorem seg_L4_A :
  @seg_L4_stmt fx rc ci cp PI RL A_prog_listing PA B SK EC_RA EC_EMPTY EC_A_MOD_AT EC_A_STAMP EC_SIO EC_SIO_IMG
    ec_ccut ec_lcut.
Proof.
unfold seg_L4_stmt, ec_laneR.
intros E fk HYP W c Hcut.
l4_get HYP ech_texts HTX. l4_get HYP ech_img HIMG. l4_get HYP ech_univ HUNIV.
l4_get HYP ech_ccut_ok HCC. l4_get HYP ech_lcut_ok HLC.
l4_get HIMG ei_frame Hfrm. l4_get HIMG ei_malloc_max Hmmax.
l4_get HIMG ei_fp Hfp. l4_get HIMG ei_rets Hrets.
l4_get HUNIV eu_crs HUCRS. l4_get HTX et_stk HSTKT.
l4_get HTX et_check_reject_clean CRC.
l4_get HYP ech_noref HNOREF.
l4_get HYP ech_pay HPAYR. l4_get HPAYR epay_crs0 Hepay. l4_get HPAYR ecov_crs0 Hecov.
destruct Hcut as (ly & S & Hp & regs & mem & md & own & Lam & peak & cnt0 & cnt & ran & k & ok & res & tr & D & r &
  trp & Hat & Hinv & Hro & HCB & HLB & Hrkd & Hfr & Hnmax & R22 & R23 & R24 & R25 & Hparsed & Hdoc & Hpjfr & Hmost & R10 &
  o & Hown & (-> & -> & -> & Hres & Hcalls)).
destruct Hat as (fy & Hfz & Hkept & Hc). subst c.
pose proof Hinv as (HJx & HOWN & HLEDx & HSIO & HRO & HLIVE & HROOM & HCNT & HPRE & HPAY & HPERM & HBYTES & HMN).
(* THE JOURNAL AT cut_caw's WILD BUDGET ec_wk_caw. This row's own code makes no wild trace up to the starved call:
   the plain journal from the entry with its depot moved to S's (Ent102CutsA.v ec_journal_rebase) runs the steps and
   the check_reject_clean call (an empty-budget text), and ec_journal_unbase returns it at the same budget WSc *)
destruct HJx as (WSc & HJw & Hwb).
assert (HJ : AJ LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E)
  own ly S Hp W mem md k) by (eapply ec_journal_rebaseR; exact HJw).
(* the ledger at the cells' named values: g_most = PJ_ALLOC_BOUND n (ec_most), g_own_ran_out = 0 (cut_caw);
   Ent102CallA.v ec_ledger_cells *)
destruct HLEDx as (mostL & ownL & HLED0).
pose proof (ec_ledger_cells B ly S Hp W mem Lam peak cnt SIZE_MAX 0 mostL ownL _ _ HLED0 Hmost Hown) as HLED.
pose proof HOWN as (pos & Hown0 & Hfkeq & Hfk0 & Hflagw).
(* ec_pre's parts BY TYPE (Ent102CallA.v ec_conj_split): a conjunct added to ec_pre breaks no line here *)
pose proof (proj1 HPRE) as HPREX.
pose proof HPRE as HPc. unfold ec_pre in HPc. ec_conj_split HPc.
assert (HS0E : s0Z (e_regs E) < YM05.alloc_ceiling) by assumption.
assert (HRA0 : raZ (e_regs E) = EC_RA) by assumption.
assert (HNC : (e_n E = 0 /\ e_p E = EC_EMPTY) \/
  (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E)))) by assumption.
assert (HNL : e_n E = Z.of_nat (length (e_pl E))) by assumption.
assert (HG0 : garr8 SEGS (mrestrict (w_H (e_W E)) (e_mem E)) (e_p E) (e_x E)) by assumption.
assert (HFR0 : frames (e_S E) = []) by assumption.
assert (HRO0 : arodata_okP SEGS (@pa_relro_lo rc A_prog_listing PA) (@pa_relro_hi rc A_prog_listing PA) B
  (aview SEGS (w_H (e_W E)) (e_mem E))) by assumption.
assert (HSIO0 : EC_SIO (aview SEGS (w_H (e_W E)) (e_mem E))) by assumption.
assert (HHEAD : e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30) by assumption.
assert (H8 : 0 < e_n E -> e_p E + e_n E + 8 <= YM05.alloc_ceiling) by assumption.
assert (Hi0t : e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E))) by assumption.
assert (Hsm : e_sm E = ReaderRes.jr_strtod) by assumption.
pose proof HPREX as (_ & _ & Hra40 & Hgp0 & Htp0 & _ & _ & _ & _).
pose proof HJw as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof HAR as (HARcf & HXS).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof Hstk as (Hal16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (@pa_B_ok rc A_prog_listing PA) as (HB0 & HB1 & _).
assert (WS : LLVMF_STK = 32768) by reflexivity.
assert (LAWS : AR_laws_x SEGS B ARc cf_head) by exact (l6f_LAWS B).
assert (Hin : In (LLVMF_FS_CLASS, pos) (frames S)) by (rewrite Hfrs, Hown0; left; reflexivity).
assert (HfrsS : frames S = [(LLVMF_FS_CLASS, pos)]) by (rewrite Hfrs, Hown0, HFR0; reflexivity).
destruct (l6f_geom B ly S Hp W mem md pos fk HARcf Hin Hfkeq) as (Gal & G4096 & Gceil & Gapp & Gfr & Gsh).
change (EC_FRAME_BYTES / 8) with 16 in Gsh.
unfold EC_FRAME_BYTES in Gceil, Gfr, Gapp.
destruct Hrkd as (Hrk & R21).
pose proof Hrk as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R26 & R27).
pose proof Hfr as (Hsaved & Hshv & Hal32).
destruct HROOM as (hist0 & HR0).
(* ---- the arithmetic of the cut: sp0, A = (sp0 - 128) & -32 ---- *)
assert (Rsp : YM05.alloc_ceiling + 32768 <= e_sp0 E <= 2 ^ 47) by lia.
assert (Hsp16 : e_sp0 E = 16 * (e_sp0 E / 16))
  by (pose proof (Z.div_mod (e_sp0 E) 16 ltac:(lia)) as D0; rewrite Hal16 in D0; lia).
assert (EA : e_A E = (e_sp0 E - 128) / 32 * 32).
{ unfold e_A, ec_A, EC_SAVE. apply l6f_land_neg32. lia. }
assert (HA32 : e_A E mod 32 = 0) by (rewrite EA; apply Z.mod_mul; lia).
assert (HAb : e_sp0 E - 144 <= e_A E <= e_sp0 E - 128).
{ rewrite EA.
  pose proof (Z.div_mod (e_sp0 E - 128) 32 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (e_sp0 E - 128) 32 ltac:(lia)) as D2. lia. }
assert (HO16 : (e_A E - e_sp0 E) mod 16 = 0).
{ pose proof (Z.div_mod (e_A E) 32 ltac:(lia)) as D1. rewrite HA32 in D1.
  replace (e_A E - e_sp0 E) with ((2 * (e_A E / 32) - e_sp0 E / 16) * 16) by lia.
  apply Z.mod_mul. lia. }
assert (Hlenx : e_n E = Z.of_nat (length (e_x E))) by (unfold e_x, ec_bytes; rewrite length_map; exact HNL).
(* ======== +0x1b8  beqz a0, +0x2c8 ======== *)
unfold cfg_at.
change (w64 EC_AR_CAW) with (Z_to_bv 64 (BASE + 0x1b8)).
l6f_fd 0x1b8 Hpl1 Hd1.
(* cut_caw states only r = 0: the branch is taken *)
  eapply (ec_step_branchR (fx := fy) WLE' W regs mem md _ 0x1b8 _ 0x2c8 _ _ _ _ ltac:(lia) ltac:(lia) Hpl1 Hd1).
  { vm_compute. reflexivity. }
  2: { l4_br_absurd (10%bv : bv 5) R10. }
  intros _ X1.
  pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X1 HJ) as HJm1.
  (* ======== +0x2c8  sub s7, s9, s7 ======== *)
  l6f_fd 0x2c8 Hpl2 Hd2.
  eapply (l4_step_subR (fx := fy) WLE' W regs mem _ _ 0x2c8 _ _ _ _ (23%bv : bv 5) (w64 (Z.of_nat (calls tr)))
    ltac:(lia) Hpl2 Hd2).
  { vm_compute. reflexivity. }
  { apply bv_eq. vm_compute. reflexivity. }
  { lazymatch goal with |- v_sub (getr _ ?a) (getr _ ?b) = _ =>
      replace a with (25%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity);
      replace b with (23%bv : bv 5) by (apply bv_eq; vm_compute; reflexivity) end.
    rewrite R25, R23. unfold v_sub, w64. apply bv_eq. rewrite !Z_to_bv_unsigned.
    unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
    rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. f_equal. lia. }
  intros X2.
  pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X2 HJm1) as HJm2.
  change (0x2c8 + 4) with 0x2cc.
  remember (regupd regs (23%bv : bv 5) (w64 (Z.of_nat (calls tr)))) as regs1 eqn:Eregs1.
  assert (R1o : forall r0 : bv 5, r0 <> (23%bv : bv 5) -> getr regs1 r0 = getr regs r0)
    by (intros r0 Hr0; rewrite Eregs1; apply getr_other; exact Hr0).
  assert (R1_23 : getr regs1 23 = w64 (Z.of_nat (calls tr))) by (rewrite Eregs1; apply getr_same; l6f_regne).
  assert (Hrk1 : ec_rk (L := A_prog_listing) E fk regs1).
  { unfold ec_rk. rewrite !R1o by l6f_regne. exact Hrk. }
  assert (R1_21 : getr regs1 21 = w64 (ec_doc fk)) by (rewrite R1o by l6f_regne; exact R21).
  assert (R1_24 : getr regs1 24 = getr regs 24) by (apply R1o; l6f_regne).
  (* ======== +0x2cc  beqz s8, +0x2f8 ======== *)
  l6f_fd 0x2cc Hpl3 Hd3.
  destruct res as [t|].
  + (* ---- rc = 0: the accepted arm ---- *)
    assert (R1_24v : getr regs1 24 = w64 0) by (rewrite R1_24; exact R24).
    eapply (ec_step_branchR (fx := fy) WLE' W regs1 mem _ _ 0x2cc _ 0x2f8 _ _ _ _ ltac:(lia) ltac:(lia) Hpl3 Hd3).
    { vm_compute. reflexivity. }
    2: { l4_br_absurd (24%bv : bv 5) R1_24v. }
    intros _ X3.
    lazymatch goal with |- SRrG _ _ _ (mkCfg _ ?m) _ => set (md3 := m) in * end.
    apply (SRr'_ret SEGS (@YGcfRehidePost.RZ_cf rc)). right. right. exists t, D.
    destruct Hdoc as (HLD & Hnode).
    exists ly, S, Hp, regs1, mem, md3, own, Lam, peak, cnt, k, (Z.of_nat (calls tr)), trp.
    split; [exists fy; split; [exact Hfz|]; split; [exact Hkept|]; reflexivity|].
    split.
    { (* cut_acc's journal at cut_caw's budget: no call on this arm *)
      split; [exists WSc; split; [|exact Hwb]; eapply ec_journal_unbaseR; [exact HJw|]|].
      { exact (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
          _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJm2). }
      exact (proj2 Hinv). }
    split; [exact Hro|].
    split; [pose proof (HCC E 4%nat 6%nat) as (_ & Hm); specialize (Hm ltac:(lia)); lia|].
    split; [pose proof (HLC E 4%nat 6%nat) as (_ & Hm); specialize (Hm ltac:(lia)); lia|].
    split; [split; [exact Hrk1 | exact R1_21]|].
    split; [exact Hfr|].
    split; [exact Hnmax|].
    split; [exact R1_23|].
    split; [exact Hcalls|].
    split; [rewrite R1_24; exact R24|].
    split; [symmetry; exact Hres|].
    split; [exact HLD|].
    split; [exact Hnode|].
    split; [exact Hpjfr|]. (* the free-order conjunct, kept: no store between cut_caw and cut_acc *)
    split; [exact Hmost | exact Hown].
  + (* ---- rc = -1: the refused arm ---- *)
    destruct Hdoc as (-> & -> & Hz).
    assert (HHp : Hp = []).
    { pose proof (prh_ledger_heads B ly S Hp W mem [] peak cnt SIZE_MAX 0 _ _ HLED) as Hh. cbn [map] in Hh.
      apply Permutation_sym, Permutation_nil in Hh. exact Hh. }
    subst Hp.
    assert (R1_24v : getr regs1 24 = w64 (-1)) by (rewrite R1_24; exact R24).
    eapply (ec_step_branchR (fx := fy) WLE' W regs1 mem _ _ 0x2cc _ 0x2f8 _ _ _ _ ltac:(lia) ltac:(lia) Hpl3 Hd3).
    { vm_compute. reflexivity. }
    { l4_br_absurd (24%bv : bv 5) R1_24v. }
    intros _ X3.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X3 HJm2) as HJm3.
    change (0x2cc + 4) with 0x2d0.
    (* ======== +0x2d0 .. +0x2dc  mv a0,s8; mv a1,s5; mv a2,s6; jal check_reject_clean ======== *)
    l6f_fd 0x2d0 Hpl4 Hd4.
    eapply (l6f_step_addiR (fx := fy) WLE' W regs1 mem _ _ 0x2d0 _ _ _ _ (10%bv : bv 5) (w64 (-1)) ltac:(lia) Hpl4 Hd4).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (24%bv : bv 5). rewrite R1_24. exact R24. }
    intros X4.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X4 HJm3) as HJm4.
    change (0x2d0 + 4) with 0x2d4.
    l6f_fd 0x2d4 Hpl5 Hd5.
    eapply (l6f_step_addiR (fx := fy) WLE' W _ mem _ _ 0x2d4 _ _ _ _ (11%bv : bv 5) (w64 (ec_doc fk)) ltac:(lia) Hpl5 Hd5).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (21%bv : bv 5). rewrite getr_other by l6f_regne. exact R1_21. }
    intros X5.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X5 HJm4) as HJm5.
    change (0x2d4 + 4) with 0x2d8.
    l6f_fd 0x2d8 Hpl6 Hd6.
    eapply (l6f_step_addiR (fx := fy) WLE' W _ mem _ _ 0x2d8 _ _ _ _ (12%bv : bv 5) (w64 0) ltac:(lia) Hpl6 Hd6).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (22%bv : bv 5). rewrite !getr_other by l6f_regne. rewrite R1o by l6f_regne. exact R22. }
    intros X6.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X6 HJm5) as HJm6.
    change (0x2d8 + 4) with 0x2dc.
    l6f_fdc 0x2dc Hpl7.
    eapply (l6f_step_callR (fx := fy) WLE' W _ mem _ _ 0x2dc _ _ (1%bv : bv 5) ltac:(lia) Hpl7).
    { apply bv_eq. vm_compute. reflexivity. }
    intros X7.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X7 HJm6) as HJm7.
    change (0x2dc + 4) with 0x2e0.
    lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
      remember r as regsc eqn:Eregsc; set (mdc := m) in * end.
    assert (Rco : forall r0 : bv 5, r0 <> (1%bv : bv 5) -> r0 <> (10%bv : bv 5) -> r0 <> (11%bv : bv 5) ->
      r0 <> (12%bv : bv 5) -> getr regsc r0 = getr regs1 r0).
    { intros r0 H1 H10 H11 H12. rewrite Eregsc, !getr_other by assumption. reflexivity. }
    assert (HSPC : spZ regsc = e_sp0 E + (e_A E - e_sp0 E)).
    { unfold spZ. rewrite Rco by l6f_regne. rewrite R1o by l6f_regne. rewrite R2. unfold w64.
      rewrite unsigned_lit_small by lia. lia. }
    assert (HS0C : s0Z regsc = e_sp0 E).
    { unfold s0Z. rewrite Rco by l6f_regne. rewrite R1o by l6f_regne. rewrite R8. unfold w64.
      apply unsigned_lit_small. lia. }
    assert (HGP : getr regsc 3 = w64 (as_gp B)) by (rewrite Rco, R1o by l6f_regne; rewrite R3; exact Hgp0).
    assert (HTP : getr regsc 4 = w64 (as_tp B)) by (rewrite Rco, R1o by l6f_regne; rewrite R4; exact Htp0).
    assert (HRA1 : getr regsc 1 = Z_to_bv 64 (BASE + 0x2e0)) by (rewrite Eregsc; apply getr_same; l6f_regne).
    assert (HA10 : getr regsc 10 = w64 (-1)).
    { rewrite Eregsc, getr_other, getr_other, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    assert (HA11 : getr regsc 11 = w64 (ec_doc fk)).
    { rewrite Eregsc, getr_other, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    assert (HA12 : getr regsc 12 = w64 0).
    { rewrite Eregsc, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    l6f_fd 0x2e0 Hpl8 Hd8.
    pose proof (l6f_img_bounds B ly S [] W mem md (BASE + 0x2e0) HAR
      (l6f_slot_img (PA := PA) 0x2e0 _ ltac:(lia) Hpl8)) as HRIMG.
    unfold kImgLo, kImgEnd in HRIMG.
    assert (HRAW : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x2e0)))
      by exact (ret_ok_codeptr_v (PI := PA) 0x2e0 ltac:(lia) eq_refl).
    assert (HRA4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 0x2e0))) by (rewrite unsigned_lit_small by lia; lia).
    assert (HRAC : raZ regsc < YM05.alloc_ceiling) by (unfold raZ; rewrite HRA1, unsigned_lit_small by lia; lia).
    (* the callee's stack: STK_check_reject_clean - (A - sp0) <= LLVMF_STK (et_stk, ei_frame) *)
    assert (HSTKC : 0 <= STK_check_reject_clean).
    { unfold STK_check_reject_clean. apply Z.add_nonneg_nonneg; [apply pi_frame_nonneg | apply l6f_zmaxl_nonneg]. }
    assert (HBUDC : STK_check_reject_clean - (e_A E - e_sp0 E) <= LLVMF_STK).
    { unfold STK_LLVMFuzzerTestOneInput in HSTKT.
      lazymatch type of HSTKT with _ + zmaxl ?l <= _ =>
        assert (Hz' : STK_check_reject_clean <= zmaxl l)
          by (apply l6f_zmaxl_in; cbn [In]; do 4 right; left; reflexivity) end.
      unfold EC_SAVE in Hfrm. lia. }
    (* the frame chain at the call: s0 = sp0, the entry's ra and s0 saved below it *)
    assert (Hch : exists ch1, achain ly (aview SEGS (w_H W) mem) (e_sp0 E + (e_A E - e_sp0 E)) (s0Z regsc) ch1 /\
      (spine ch1 = [] \/ spine ch1 = [raZ (e_regs E)])).
    { rewrite HS0C. pose proof Hsaved as (Sra & S8 & _).
      apply (ec_chain_at ly _ _ (e_sp0 E) (raZ (e_regs E)) (s0Z (e_regs E)) Sra S8).
      - unfold raZ. apply u64_range.
      - unfold s0Z. apply u64_range.
      - exact HS0E.
      - exact Hra40.
      - lia.
      - rewrite Hsp16. replace (16 * (e_sp0 E / 16)) with ((2 * (e_sp0 E / 16)) * 8) by lia.
        apply Z.mod_mul. lia.
      - rewrite Etop. lia.
      - lia. }
    destruct Hch as (ch1 & Hch & _).
    (* the doc's window for check_reject_clean's bcmp *)
    destruct (l4_doc_sh (PA := PA) (w_H W) mem fk Gal ltac:(lia) Hshv (fun i Hi => proj1 (Gsh i Hi))) as (Hdra & Hdhu).
    assert (HDSRC : src_rd (L := A_prog_listing) (PA := PA) W mem (ec_doc fk) (repeat 0 56)).
    { unfold src_rd. rewrite repeat_length. change (Z.of_nat 56) with 56.
      split; [exact Hz|]. unfold ec_doc. split; [lia|]. split; [lia|].
      split; [unfold amem_range, in_app, kLowShadowBeg, ASAN_CEIL in *; lia|].
      split; [exact Hdra | intros _; exact Hdhu]. }
    (* ======== the call: the kit's check_reject_clean text (empty budget: on the rebased plain journal) ======== *)
    eapply (SRrG_bind SEGS WLE' (wle'_trans SEGS _)).
    { eapply (l4_call_xR (fx := fy) (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE' (wle'_trans SEGS _) W regsc mem
        (@pa_sigma rc A_prog_listing PA AS_check_reject_clean)
        LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) [] (e_W E) (e_mem E) (e_md E)
        [(LLVMF_FS_CLASS, pos)] ly S [] mdc k
        STK_check_reject_clean [] (e_A E - e_sp0 E) (Z_to_bv 64 (BASE + 0x2e0)) ch1 _
        ltac:(rewrite <- Hown0; exact HJm7) HSPC HO16 ltac:(lia) HSTKC HBUDC HGP HTP HRA1 HRAW HRA4 Hch).
      - intros HPRE1.
        apply (l4_lift_x (SK := SK) SEGS B PST ARc WLE' (wle_wle' SEGS _)).
        eapply (CRC fy ly S [] W regsc mem mdc ch1 (-1) (ec_doc fk) 0 [] peak cnt SIZE_MAX 0
          (PJ_ALLOC_BOUND (e_n E)) 0).
        + split; [exact HPRE1|]. split; [exact HRO|].
          split; [rewrite HSPC, Eshi; lia | split; [exact HRAC | exact Hfz]].
        + exact HA10.
        + lia.
        + lia.
        + exact HA11.
        + exact HDSRC.
        + exact HA12.
        + reflexivity.
        + exact HLED.
      - apply l4_fp_sub_nil. }
    cbv beta. intros W1 c1 _ (ly1 & S1 & Hp1 & regs5 & mem1 & md1 & k1 & -> & HJc1 & HJ1 & HP1 & HQ1).
    destruct HQ1 as ((-> & -> & Eab1 & Hlive1 & HLED1) & Hmn1).
    replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) in HJ1 by lia.
    destruct (l4_after_frame E fk ly S [] W mem mdc own pos STK_check_reject_clean ly1 S [] W1 mem1 md1 k1 []
      Hown0 Hfkeq Hin ltac:(lia) HAb HSTKC HJ1 HOWN Hfr) as (HOWN1 & Hfr1 & Hin1 & Hfkeq1).
    (* the journal after the call, back at cut_caw's budget WSc *)
    assert (HJc1w : AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)]
      ly1 S [] W1 mem1 md1 (k + k1) WSc) by (eapply ec_journal_unbaseR; [exact HJw | exact HJc1]).
    pose proof Hfr1 as (Hsaved1 & Hshv1 & _).
    pose proof HJc1w as (HAR1 & Hly1 & _ & _ & _ & _ & _ & _ & _ & F2c1 & _ & _ & _ & _ & _ & _ & _).
    pose proof HAR1 as (HARcf1 & _).
    pose proof Hly1 as (_ & _ & _ & _ & _ & _ & _ & _ & Etop1 & _ & Eshi1 & _).
    destruct (l4_entry_keep E own ly1 S [] W1 mem1 md1 (k + k1) WSc HIMG HSIO0 HRO0
      ltac:(rewrite <- Hown0 in HJc1w; exact HJc1w))
      as (_ & HRO1).
    assert (R5p : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs5 r0 = getr regsc r0)
      by (intros r0 Hr0; exact (l6f_pres regsc regs5 r0 HP1 Hr0)).
    (* ======== +0x2e0 .. +0x2f0  mv a0,s4; mv a1,s3; mv a2,s7; mv a3,zero; jal check_reject_clean_starved ======== *)
    eapply (l6f_step_addiR (fx := fy) WLE' W1 regs5 mem1 md1 _ 0x2e0 _ _ _ _ (10%bv : bv 5) (w64 (e_p E))
      ltac:(lia) Hpl8 Hd8).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (20%bv : bv 5). rewrite R5p by l6f_cs. rewrite Rco, R1o by l6f_regne. exact R20. }
    intros Y1.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y1 HJc1) as HJn1.
    change (0x2e0 + 4) with 0x2e4.
    l6f_fd 0x2e4 Hpl9 Hd9.
    eapply (l6f_step_addiR (fx := fy) WLE' W1 _ mem1 _ _ 0x2e4 _ _ _ _ (11%bv : bv 5) (w64 (e_n E)) ltac:(lia) Hpl9 Hd9).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (19%bv : bv 5). rewrite getr_other by l6f_regne. rewrite R5p by l6f_cs. rewrite Rco, R1o by l6f_regne.
      exact R19. }
    intros Y2.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y2 HJn1) as HJn2.
    change (0x2e4 + 4) with 0x2e8.
    l6f_fd 0x2e8 Hpl10 Hd10.
    eapply (l6f_step_addiR (fx := fy) WLE' W1 _ mem1 _ _ 0x2e8 _ _ _ _ (12%bv : bv 5) (w64 (Z.of_nat (calls tr)))
      ltac:(lia) Hpl10 Hd10).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (23%bv : bv 5). rewrite !getr_other by l6f_regne. rewrite R5p by l6f_cs. rewrite Rco by l6f_regne.
      exact R1_23. }
    intros Y3.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y3 HJn2) as HJn3.
    change (0x2e8 + 4) with 0x2ec.
    l6f_fd 0x2ec Hpl11 Hd11.
    eapply (l6f_step_addiR (fx := fy) WLE' W1 _ mem1 _ _ 0x2ec _ _ _ _ (13%bv : bv 5) (w64 0) ltac:(lia) Hpl11 Hd11).
    { vm_compute. reflexivity. }
    { apply bv_eq. vm_compute. reflexivity. }
    { l4_mv (0%bv : bv 5). reflexivity. }
    intros Y4.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y4 HJn3) as HJn4.
    change (0x2ec + 4) with 0x2f0.
    l6f_fdc 0x2f0 Hpl12.
    eapply (l6f_step_callR (fx := fy) WLE' W1 _ mem1 _ _ 0x2f0 _ _ (1%bv : bv 5) ltac:(lia) Hpl12).
    { apply bv_eq. vm_compute. reflexivity. }
    intros Y5.
    pose proof (ajournal_x_materializeR (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE'
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Y5 HJn4) as HJn5.
    change (0x2f0 + 4) with 0x2f4.
    lazymatch goal with |- SRrG _ _ _ (mkCfg (@YK11.mkst _ ?r _ _ _) ?m) _ =>
      remember r as regsd eqn:Eregsd; set (mdd := m) in * end.
    assert (Rdo : forall r0 : bv 5, r0 <> (1%bv : bv 5) -> r0 <> (10%bv : bv 5) -> r0 <> (11%bv : bv 5) ->
      r0 <> (12%bv : bv 5) -> r0 <> (13%bv : bv 5) -> getr regsd r0 = getr regs5 r0).
    { intros r0 H1 H10 H11 H12 H13. rewrite Eregsd, !getr_other by assumption. reflexivity. }
    assert (Rd_s : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> r0 <> (1%bv : bv 5) ->
      r0 <> (10%bv : bv 5) -> r0 <> (11%bv : bv 5) -> r0 <> (12%bv : bv 5) -> r0 <> (13%bv : bv 5) ->
      getr regsd r0 = getr regsc r0).
    { intros r0 Hcs H1 H10 H11 H12 H13. rewrite Rdo by assumption. exact (R5p r0 Hcs). }
    assert (HSPD : spZ regsd = e_sp0 E + (e_A E - e_sp0 E)).
    { unfold spZ. rewrite Rd_s by (first [l6f_cs | l6f_regne]). exact HSPC. }
    assert (HS0D : s0Z regsd = e_sp0 E).
    { unfold s0Z. rewrite Rd_s by (first [l6f_cs | l6f_regne]). exact HS0C. }
    assert (HGPD : getr regsd 3 = w64 (as_gp B)) by (rewrite Rd_s by (first [l6f_cs | l6f_regne]); exact HGP).
    assert (HTPD : getr regsd 4 = w64 (as_tp B)) by (rewrite Rd_s by (first [l6f_cs | l6f_regne]); exact HTP).
    assert (HRAD : getr regsd 1 = Z_to_bv 64 (BASE + 0x2f4)) by (rewrite Eregsd; apply getr_same; l6f_regne).
    assert (HD10 : getr regsd 10 = w64 (e_p E)).
    { rewrite Eregsd, !getr_other by l6f_regne. apply getr_same. l6f_regne. }
    assert (HD11 : getr regsd 11 = w64 (e_n E)).
    { rewrite Eregsd, getr_other, getr_other, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    assert (HD12 : getr regsd 12 = w64 (Z.of_nat (calls tr))).
    { rewrite Eregsd, getr_other, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    assert (HD13 : getr regsd 13 = w64 0).
    { rewrite Eregsd, getr_other by l6f_regne. apply getr_same. l6f_regne. }
    l6f_fd 0x2f4 Hpl13 Hd13.
    pose proof (l6f_img_bounds B ly1 S [] W1 mem1 md1 (BASE + 0x2f4) HAR1
      (l6f_slot_img (PA := PA) 0x2f4 _ ltac:(lia) Hpl13)) as HRIMG2.
    unfold kImgLo, kImgEnd in HRIMG2.
    assert (HRAW2 : YK0s.ret_ok (Z_to_bv 64 (BASE + 0x2f4)))
      by exact (ret_ok_codeptr_v (PI := PA) 0x2f4 ltac:(lia) eq_refl).
    assert (HRA42 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + 0x2f4))) by (rewrite unsigned_lit_small by lia; lia).
    assert (HRAC2 : raZ regsd < YM05.alloc_ceiling) by (unfold raZ; rewrite HRAD, unsigned_lit_small by lia; lia).
    assert (HSTKS : 0 <= STK_check_reject_clean_starved).
    { unfold STK_check_reject_clean_starved. apply Z.add_nonneg_nonneg; [apply pi_frame_nonneg | apply l6f_zmaxl_nonneg]. }
    assert (HBUDS : STK_check_reject_clean_starved - (e_A E - e_sp0 E) <= LLVMF_STK).
    { unfold STK_LLVMFuzzerTestOneInput in HSTKT.
      lazymatch type of HSTKT with _ + zmaxl ?l <= _ =>
        assert (Hz' : STK_check_reject_clean_starved <= zmaxl l)
          by (apply l6f_zmaxl_in; cbn [In]; do 5 right; left; reflexivity) end.
      unfold EC_SAVE in Hfrm. lia. }
    assert (Hch2 : exists ch2, achain ly1 (aview SEGS (w_H W1) mem1) (e_sp0 E + (e_A E - e_sp0 E)) (s0Z regsd) ch2 /\
      (spine ch2 = [] \/ spine ch2 = [raZ (e_regs E)])).
    { rewrite HS0D. pose proof Hsaved1 as (Sra & S8 & _).
      apply (ec_chain_at ly1 _ _ (e_sp0 E) (raZ (e_regs E)) (s0Z (e_regs E)) Sra S8).
      - unfold raZ. apply u64_range.
      - unfold s0Z. apply u64_range.
      - exact HS0E.
      - exact Hra40.
      - lia.
      - rewrite Hsp16. replace (16 * (e_sp0 E / 16)) with ((2 * (e_sp0 E / 16)) * 8) by lia.
        apply Z.mod_mul. lia.
      - rewrite Etop1. lia.
      - lia. }
    destruct Hch2 as (ch2 & Hch2 & Hsp2).
    (* the observed context: the top's [EC_RA] (ec_ctx0) extended at the return site EC_AR_CRS0 (Ent102CallA.v) *)
    assert (HCTX : prh_ctx (ec_ctx0 EC_RA) F_check_reject_clean_starved (raZ regsd :: spine ch2)).
    { assert (Era : raZ regsd = EC_AR_CRS0).
      { unfold raZ. rewrite HRAD, unsigned_lit_small by lia. reflexivity. }
      rewrite Era. eapply ec_ctx_call_img; [exact HIMG | | rewrite <- HRA0; exact Hsp2].
      cbn [ec_call_rets In]. do 14 right. left. reflexivity. }
    (* the payload at state 1 *)
    assert (HPAY1 : (e_n E = 0 /\ e_p E = EC_EMPTY) \/ (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B ly1 S))).
    { destruct HNC as [Hn0 | (Hn & _)]; [left; exact Hn0|right]. split; [exact Hn|].
      rewrite Eab1. destruct HPAY as [Hn0 | Hinp]; [lia | exact Hinp]. }
    assert (HBY1 : garr8 SEGS (mrestrict (w_H W1) mem1) (e_p E) (e_x E)).
    { apply (l6f_garr8_kept (w_H (e_W E)) (w_H W1) (e_mem E) mem1); [|exact HG0].
      intros i Hi. rewrite <- Hlenx in Hi. destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
      pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
      destruct HPAY1 as [(Hn0 & _) | (_ & Hinp1)]; [lia|].
      apply (F2c1 (e_p E) (e_n E) i Hinp Hinp1 ltac:(lia)).
      apply inFP_nil. }
    (* the payload at state 1: the empty payload at EC_EMPTY (ei_empty), or a live entry block (Ent102CallA.v) *)
    assert (HPAYOK : 0 < e_p E /\ e_p E + e_n E < 2 ^ 62 /\ src_rd (L := A_prog_listing) (PA := PA) W1 mem1 (e_p E) (e_x E)
      /\ PRH_FnReader.prhReader_home (L := A_prog_listing) (PA := PA) B ly1 S [] [] (e_p E) (e_n E)).
    { destruct HPAY1 as [(Hn0 & Hp0) | (Hn & Hpb1)].
      - exact (l4_pay_empty E ly1 S W1 mem1 HIMG Hn0 Hp0 Hlenx).
      - destruct HNC as [(Hn0 & _) | (_ & Hin0)]; [lia|].
        assert (HSH : src_rd (L := A_prog_listing) (PA := PA) W1 mem1 (e_p E) (e_x E) /\
          PRH_FnReader.prhReader_home (L := A_prog_listing) (PA := PA) B ly1 S [] [] (e_p E) (e_n E)).
        { eapply (ec_src_home (PA := PA) B); [exact HARcf1 | eexists; eexists; exact HLED1 | rewrite Eab1; exact HPERM |
            exact Hin0 |
            exact Hpb1 | exact Hlenx | lia | exact (H8 ltac:(lia)) | exact HBY1]. }
        destruct HSH as (HS & HH).
        pose proof HS as (_ & H4 & Hc8 & _). rewrite <- Hlenx in Hc8.
        split; [lia|]. split; [unfold YM05.alloc_ceiling in Hc8; lia|]. split; [exact HS | exact HH]. }
    destruct HPAYOK as (Hp0 & Hpn & HSRC & HHOME).
    (* the room: nothing harness-held is live, so the blocks are the entry's *)
    assert (HBLK : Permutation (ablocks B ly S) (ablocks B (e_ly E) (e_S E))) by (exact HPERM).
    assert (HBBS : blocks_bytes S = blocks_bytes (e_S E)).
    { rewrite (prh_blocks_bytes_ablocks B ly S), (l6f_bsum_perm _ _ HBLK),
        <- (prh_blocks_bytes_ablocks B (e_ly E) (e_S E)). reflexivity. }
    assert (Hlen : Z.of_nat (length (e_x E)) <= EC_NMAX) by (rewrite <- Hlenx; exact Hnmax).
    pose proof (Hecov E Hlen) as Ht0.
    assert (HRQ : RQ_crcs (e_x E) + cf_head < cf_malloc_max).
    { unfold RQ_crcs, zmaxl. cbn [fold_right]. rewrite Ent102ReqA.ec_rq_pj_parse.
      pose proof (PjReqBoundW.rq_read_bound_56 prh_jr_strtod (e_x E)) as Hq.
      unfold PRH_FnWriter.prhWriter_WMAX in *. rewrite <- Hlenx in Hq. unfold EC_NMAX in Hnmax. lia. }
    assert (HRQP : PRH_FnPj.RQ_pj_parse (e_x E) <= PJ_ALLOC_BOUND (e_n E)).
    { rewrite Ent102ReqA.ec_rq_pj_parse. pose proof (PjReqBoundW.rq_read_bound prh_jr_strtod (e_x E)) as Hq.
      unfold PJ_ALLOC_BOUND. rewrite Hlenx. lia. }
    assert (HFR : FR_check_reject_clean_starved = ltac:(let v := eval vm_compute in FR_check_reject_clean_starved in
      exact v)) by (vm_compute; reflexivity).
    (* the exact room position: the refused tail's run events at cut_caw's index, supplied from the call's run *)
    assert (HMAXB : Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB) by (unfold PresetReqAt.MAXB; unfold EC_NMAX in Hlen; lia).
    assert (Hnone : fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None).
    { rewrite (Ent102PosA.ec_rd_ck_read _ _ _ E Hsm). symmetry. exact Hres. }
    assert (HRUN : prh_run_at (e_sm E) (e_x E) (e_os E ++ [trp])
      (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat
      (ck_crcs_evs (e_sm E) (e_x E) (Z.of_nat (calls tr)) 0 PjTree.JNull)).
    { rewrite (l4_rej_bridge E (calls tr) PjTree.JNull Hsm Hcalls).
      exact (l4_supply_rej E trp HMAXB Hro Hi0t Hnone). }
    l4_get HTX et_check_reject_clean_starved CRS0. pose proof (CRS0 fy) as CRSn.
    destruct (l4_peaks E trp hist0 S HMAXB Hro Hi0t HR0) as (HPKs & HPKc).
    (* THE BUDGETED CALL: the batch kit's starved text posts its journal at wbudget [] (prh_wk F_check_reject_clean_starved).
       The caller's journal before it is the rebased one taken back to cut_caw's budget WSc; the callee's room is
       Ent102CutsA.ec_room_at at cut_caw's journal (check_reject_clean keeps S, so the call's S is cut_caw's) *)
    assert (HJn5w : AJW LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)]
      ly1 S [] W1 mem1 mdd (k + k1) WSc) by (eapply ec_journal_unbaseR; [exact HJw | exact HJn5]).
    assert (HWR : YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_reject_clean_starved) (st_depot S)).
    { eapply (ec_room_atR (fx := fx)); [exact HPRE | exact HJw | exact Hwb | apply Nat.leb_le; vm_compute; reflexivity]. }
    (* ======== the call: the batch kit's check_reject_clean_starved text, doc = 0 ======== *)
    eapply SRrG_mono.
    { eapply (l4_call_xbFR (fx := fy) (SK := SK) SEGS B PST ARc LAWS (@pa_segs_low rc A_prog_listing PA) WLE' (wle'_trans SEGS _) W1 regsd mem1
        (@pa_sigma rc A_prog_listing PA AS_check_reject_clean_starved)
        LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) [(LLVMF_FS_CLASS, pos)] ly1 S [] mdd
        (k + k1) WSc STK_check_reject_clean_starved [] (e_A E - e_sp0 E) (Z_to_bv 64 (BASE + 0x2f4)) ch2 _ _
        HJn5w HSPD HO16 ltac:(lia) HSTKS HBUDS HGPD HTPD HRAD HRAW2 HRA42 Hch2).
      - intros HPRE2.
        eapply (CRSn (e_x E) (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat
          (e_H0 E) hist0 ly1 S [] W1 regsd mem1 mdd ch2 (e_p E) (e_x E)
          (Z.of_nat (calls tr)) 0 PjTree.JNull [] [] peak cnt 0 (PJ_ALLOC_BOUND (e_n E))).
        + split; [exact HPRE2|]. split; [exact HRO1|].
          split; [rewrite HSPD, Eshi1; lia | split; [exact HRAC2 | exact Hfz]].
        + exact (Hmn1 HMN).
        + exact HUCRS.
        + exact HCTX.
        + exact HD10.
        + rewrite <- Hlenx. exact HD11.
        + exact HD12.
        + exact HD13.
        + rewrite <- Hlenx. unfold EC_NMAX in Hnmax. lia.
        + exact Hp0.
        + rewrite <- Hlenx. exact Hpn.
        + exact HSRC.
        + rewrite <- Hlenx. exact HHOME.
        + rewrite <- Hcalls. lia.
        + left. reflexivity.
        + exact HLED1.
        + lia.
        + rewrite <- Hsm. exact HRUN.
        + reflexivity.
        + exact HRQP.
        + intros H0. exfalso. apply H0. reflexivity.
        + pose proof (HLC E 4%nat 4%nat) as (Hl4 & _). lia.
        + exact HRQ.
        + rewrite HfrsS, HFR. cbn [length]. unfold ck_FRAMES_CAP. lia.
        + exact (Hlive1 HLIVE).
        + rewrite <- Hsm. exact HR0.
        + exact Hfz.
        + (* the run has at most 4 calls: ec_pre's length (e_os E) <= 3 and this call's triple *)
          assert (HOS3 : (length (e_os E) <= 3)%nat)
            by (clear - HPRE; unfold ec_pre in HPRE; Ent102CallA.ec_conj_pick HPRE).
          rewrite length_app. cbn [length]. lia.
        + exact HWR.
        + rewrite <- Hsm. exact HPKs.
        + rewrite <- Hsm. exact HPKc.
        + rewrite <- Hsm. apply (Ent102Win.cons_from_at_cut (e_sm E) (e_x E) (e_os E) trp (e_i0 E) _ _ HMAXB Hro Hi0t);
          [change (Ent102Win.cno_part3 (e_sm E) (e_x E) trp) with (ec_cno_evs E trp); rewrite !length_app; lia | exact HRUN].
      - apply l4_fp_sub_nil. }
    cbv beta. intros W2 c2 _ (fx2 & ly2 & S2 & Hp2 & regs6 & mem2 & md2 & k2 & WS1 & -> & Hfz2 & Hkept2 & HPW & HJc2 &
      HJ2 & HP2 & HQ2).
    destruct HQ2 as ((HRL2 & Lam' & peak' & cnt' & ran' & HpLam & HpBlk & Hpk & Hcnt' & _ & Hran'
      & _ & Hpos & HLED2 & HBY2 & _) & Hmn2).
    subst ran'. destruct (Hpos eq_refl) as (h2 & HR2). rewrite <- Hsm in HR2.
    assert (HL0 : Lam' = []) by (apply Permutation_nil; apply Permutation_sym; exact HpLam).
    subst Lam'.
    assert (HHp2 : Hp2 = []).
    { pose proof (prh_ledger_heads B ly2 S2 Hp2 W2 mem2 [] peak' cnt' SIZE_MAXZ 0 _ _ HLED2) as Hh. cbn [map] in Hh.
      apply Permutation_sym, Permutation_nil in Hh. exact Hh. }
    subst Hp2.
    replace (e_sp0 E + (e_A E - e_sp0 E)) with (e_A E) in HJ2 by lia.
    destruct (l4_after_frame E fk ly1 S [] W1 mem1 mdd own pos STK_check_reject_clean_starved ly2 S2 [] W2 mem2 md2 k2 WS1
      Hown0 Hfkeq1 Hin1 ltac:(lia) HAb HSTKS HJ2 HOWN1 Hfr1) as (HOWN2 & Hfr2 & _ & _).
    assert (HBLK2 : Permutation (ablocks B ly2 S2) (ablocks B (e_ly E) (e_S E))).
    { apply (Permutation_trans HpBlk). rewrite Eab1. exact HBLK. }
    pose proof (proj1 (Hepay E Hlen)) as Hbud.
    rewrite <- Hcalls in Hbud.
    pose proof (HCC E 5%nat 5%nat) as (Hc5 & _).
    destruct (l4_entry_keep E own ly2 S2 [] W2 mem2 md2 (k + k1 + k2) (WSc ++ WS1) HIMG HSIO0 HRO0
      ltac:(rewrite <- Hown0 in HJc2; exact HJc2)) as (HSIO2 & HRO2).
    pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2c2 & _).
    right. left.
    exists ly2, S2, [], regs6, mem2, md2, own, peak', cnt', (k + k1 + k2), trp.
    split.
    { exists fx2. split; [exact Hfz2|]. split.
      - intros q Hq. rewrite (Hkept2 q Hq). exact (Hkept q Hq).
      - reflexivity. }
    split.
    { (* cut_crs0's journal at ec_wk_crs0 = ec_wk_caw + prh_wk F_check_reject_clean (none) + the starved call's: the
         budgets add *)
      split.
      { exists (WSc ++ WS1). split; [rewrite Hown0; exact HJc2|].
        replace ec_wk_crs0 with (ec_wk_caw + prh_wk F_check_reject_clean_starved)%nat by (vm_compute; reflexivity).
        exact (YCbqGwild.wbudget_app [] _ _ WSc WS1 Hwb HPW). }
      split; [exact HOWN2|].
      split; [exists (PJ_ALLOC_BOUND (e_n E)), 0; exact HLED2|].
      split; [exact HSIO2|].
      split; [exact HRO2|].
      split; [exact HRL2|].
      split; [exists h2; rewrite <- (l4_idx_crs0 E trp (calls tr) PjTree.JNull Hsm Hcalls); exact HR2|].
      split; [lia|].
      split; [exact HPRE|].
      split.
      { destruct HNC as [(Hn0 & _) | (_ & Hinp)];
        [left; exact Hn0 | right; exact (Permutation_in _ (Permutation_sym HBLK2) Hinp)]. }
      split; [unfold ck_hblks; cbn [map app]; exact HBLK2|].
      split.
      { intros i Hi. destruct HNC as [(Hn0 & _) | (Hn & Hinp)]; [lia|].
        pose proof (req_size_pos (e_n E) ltac:(lia)) as (_ & Hrq).
        apply (F2c2 (e_p E) (e_n E) i Hinp (Permutation_in _ (Permutation_sym HBLK2) Hinp) ltac:(lia)).
        apply inFP_nil. }
      exact (Hmn2 (Hmn1 HMN)). }
    split; [reflexivity|].
    split; [exact Hro|].
    split; [lia|].
    split.
    { rewrite (prh_blocks_bytes_ablocks B ly2 S2), (l6f_bsum_perm _ _ HBLK2),
        <- (prh_blocks_bytes_ablocks B (e_ly E) (e_S E)), <- HBBS.
      pose proof (HLC E 4%nat 5%nat) as (_ & Hm). specialize (Hm ltac:(lia)). lia. }
    split; [|split; [exact Hfr2 | split; [exact Hnmax | exact Hnone]]].
    (* ec_rkd: every register the cut reads is callee-saved; the four argument copies wrote a0 .. a3 and ra only *)
    assert (R6 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs6 r0 = getr regsd r0)
      by (intros r0 Hr0; exact (l6f_pres regsd regs6 r0 HP2 Hr0)).
    assert (Rall : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> r0 <> (1%bv : bv 5) ->
      r0 <> (10%bv : bv 5) -> r0 <> (11%bv : bv 5) -> r0 <> (12%bv : bv 5) -> r0 <> (13%bv : bv 5) ->
      r0 <> (23%bv : bv 5) -> getr regs6 r0 = getr regs r0).
    { intros r0 Hcs H1 H10 H11 H12 H13 H23. rewrite R6 by exact Hcs. rewrite Rd_s by assumption.
      rewrite Rco by assumption. exact (R1o r0 H23). }
    split; [unfold ec_rk; rewrite !Rall by (first [l6f_cs | l6f_regne]); exact Hrk|].
    rewrite Rall by (first [l6f_cs | l6f_regne]). exact R21.
Qed.

End L4.

Print Assumptions seg_L4_A.
About seg_L4_A.
