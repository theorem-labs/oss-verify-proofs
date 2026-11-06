(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of mix_call (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry BASE + AF_mix_call = 0x8ad54, 480 bytes, 120 instructions): tmix_call_spec of
   a Theorem Labs lane's lib/B/Prog/mix_call_c.v (blob ebd1fd295d8, the same on a working branch f490061c104 and 707acd856cb), proved in the A walk's
   style (lib/A/Prog/mix_call.v, a working branch fa7944d852b): the verified symbolic executor over
   cmd_listing (paj_run_tok / paj_run_to_tok / psrr_branch_tok, lib/B/Prog/CmdPaLib.v), the inline shadow checks
   removed by the token executor with their addressability obligations, the strlen wrapper through its Theorem Labs lane
   contract taken at the current FP state, and one lemma per loop (the 4 bytes of c->fn run straight; the argument
   loop and the byte loop are inductions over a re-seeded loop head).

   The B code, measured with capstone on the pinned fuzz_command.asan-ubsan (.symtab: mix_call LOCAL FUNC 0x8ad54,
   480 bytes), is A's code with a 96-byte frame (ra, s0-s10), other registers and the UBSan checks:
     0x8ad54 .. 0x8ad84  the frame; 0x8ad88 beqz a1 -> trap; 0x8ad94 bnez (c & 7) -> trap
     0x8ad98 / 0x8ada8   the two auipc pairs: the shadow-base GOT word 0xa5f50 (A_OBJ 0) and the FNV-1a offset
                         basis 0x10330 (A_OBJ 58), both object atoms bridged by VOBJS (no A_HI value: no VHIS)
     0x8adc8 .. 0x8adf8  the 4 bytes of c->fn (a4 counts 4 -> 0), each with 0x8adcc bgeu 1, b + 1 -> trap and the
                         load1 check 0x8add8 (slow path 0x8ae00, report 0x8ae08)
     0x8ae0c .. 0x8ae24  the load4 check on c->nargs 0x8ae18 (slow path 0x8af20, report 0x8af2c), blez nargs
     0x8ae28 .. 0x8ae4c  a := 0 (s4), s5 := c + 8, s6 := basis, s7 := ~s5, s8 := nargs, s9 := INT_MAX, s10 := 1
     0x8ae50 .. 0x8ae74  argument loop: 0x8ae54 bltu s7, 8a -> trap; load8 check 0x8ae64 (report 0x8af30);
                         s1 := c->args[a]; jal __interceptor_trampoline_strlen 0x4517c (at 0x8ae74)
     0x8ae78 .. 0x8ae84  basis if the digest is 0, a1 := len + 1, into the byte loop
     0x8ae88 .. 0x8ae94  0x8ae88 beq a, INT_MAX -> trap; a := a + 1; 0x8ae90 beq a, nargs -> epilogue
     0x8ae9c .. 0x8aed0  byte loop: 0x8aea0 bgeu 1, b + 1 -> trap; load1 check 0x8aeac (slow path 0x8aed4, report
                         0x8aedc); digest step; back to 0x8ae88 after the terminator
     0x8aee0 .. 0x8af18  epilogue; 0x8af1c unimp (the one UBSan trap)

   Report / trap edges, each refuted at its branch:
     0x8ad88 (c = NULL -> 0x8af1c): decided by the executor's decide_cond2 (lib/Reusable/YP0e.v:932, sound by
       decide_cond2_sound :981) in mc_core's first run, from the slot premise (atom 11's fact A_G_REC <= c in
       mc_facts0, established in mc_entry).
     0x8ad94 (c mod 8 <> 0 -> 0x8af1c): the same, from the slot premise (atom 11's alignment 2 ^ 3 in mc_facts0).
     0x8adcc (b + 1 <= 1 over c->fn -> 0x8af1c), 4 times: the same, in mc_core's second run (atom 11's range).
     0x8add8 -> 0x8ae00 -> 0x8ae08 (__asan_report_load1 on c->fn): removed by the token executor, whose obligation
       is range_addressable at c + k (OBL in mc_core), from the slot premise by mc_rec_addr (CmdZsh's
       cmd_addressable_in over the record's zero-shadow ranges of g_rec and record.spill, lib/B/YF0m.v:4650-4651).
     0x8ae18 -> 0x8af20 -> 0x8af2c (__asan_report_load4 on c->nargs): the same (OBL in mc_core).
     0x8ae54 (c + 8 + 8a overflows -> 0x8af1c): at a = 0 (mc_core) refuted by mc_ltu0 (s7 < 0 unsigned never
       holds); at a + 1 (mc_inc) decided by the executor from ss_inc's facts (atom 23 = ~(c + 8) >= MC_NOTC
       A_REC_SPILL, atom 20 = a <= 5), from the slot premise and acall_at's nargs <= 6.
     0x8ae64 -> 0x8af30 (__asan_report_load8 on c->args[a]): removed by the token executor in mc_args, its
       obligation discharged by mc_rec_addr from the slot premise.
     0x8ae88 (a = INT_MAX -> 0x8af1c): decided by the executor in mc_inc from ss_inc's facts (atom 20 = a <= 5,
       atom 25 = s9 = 0x7fffffff), from acall_at's nargs <= 6.
     0x8aea0 (b + 1 <= 1 over an argument -> 0x8af1c): decided by the executor in mc_bytes from mc_bl_facts (atom
       10 = b >= 4096, atom 26 = s10 = 1), from acall_at's argument block (AR's block law al_blocks).
     0x8aeac -> 0x8aed4 -> 0x8aedc (__asan_report_load1 on an argument's bytes): removed by the token executor in
       mc_bytes, its obligation discharged by range_addressable_of_block (AR's block law) from acall_at.

   Section hypotheses beyond the statement's (ASTRLEN, VOBJS): the per-binary allocator record CmdBSyms (HB), and
   the per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib at this walk's
   abstract segments (used for CmdRecCells' cmd_cf_env, the errno / trace facts of the runtime-entry call). The
   shadow-cell and GOT facts are CmdRecCells' cmd_cf_cell / cmd_cf_got (HB + VOBJS), the AR laws AR_laws_ok.

   TAKEN FROM: the A walk lib/A/Prog/mix_call.v (a working branch fa7944d852b), re-walked at the B
   addresses above; the Generation-N B walk lib/B/Prog/mix_call.v (a working branch a3f99d62c52) read as a
   template of the B code only, not ported and not required. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/mix_call.v, with its module paths and module names changed; 850 of its 923 lines of code are new or changed and 1166 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a YP0c YP0d YP07 YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacRateSnap.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rate_snap_c reac_master_only_cadence_ns_c.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YP0m YP0l YP0e YP06 YP03 YCbn YA0o YA0q YXcalls YK0o YK1b YP0k.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require FpStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_master_only_cadence_ns.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
Context {PX : YXcalls.PAXcalls lib_both3_0_listing}.
Context {PO : YXcalls.PAObjImg lib_both3_0_listing}.
Context {PH : YXcalls.PAHiImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TRATE : treac_rate_snap_spec B.
Definition REAC_MASTER_ONLY_CADENCE_NS_STK : Z := 112 + REAC_RATE_SNAP_STK.
Definition treac_master_only_cadence_ns_post (fq : YK11.FPState) (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists fq' : YK11.FPState,
    freg_kept (@YK11.fp_regs fq) (@YK11.fp_regs fq') /\ @YK11.fp_csr fq' = @YK11.fp_csr fq /\
    apost_base (fx := fq') SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK [] regs ly S W mem md 0
      (fun ly' S' W' regs' mem' md' =>
         getr regs' 10 = w64 (10 ^ 9) /\
         Permutation (ablocks B ly' S') (ablocks B ly S) /\
         W' = W /\ (forall a : word, ~ (spZ regs - REAC_MASTER_ONLY_CADENCE_NS_STK <= bv_unsigned a < spZ regs) -> mem' a = mem a)) W' c'.
Definition treac_master_only_cadence_ns_spec : Prop :=
  forall (fq : YK11.FPState) ly S W (regs : bvmap 5 word) mem md ch (fps : Z),
  afn_pre SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
  SRr SEGS W (cfg_at (fx := fq) SEGS (BASE + AF_both3_reac_master_only_cadence_ns) regs mem md)
    (treac_master_only_cadence_ns_post fq regs ly S W mem md).
Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP0m OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP0l
OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP0e OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP06
OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP03 OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YCbn
OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YA0o OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YA0q
OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YXcalls OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YK0o
OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YK1b OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable.YP0k
OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt.FpStep.
Definition MSB : Z := 0x7fff8000.
Definition moc_Bx : sv := SOff 32 0.
Definition moc_regions : smem := [stack_region 112; got_regionP; bcell_regionP 32].
Definition moc_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF MSB MSB 0); (A_OBJ 65, mkAF YImgTop.IMG_LO (YImgTop.IMG_TOP - 8) 0)] [] [].
Definition ss_moc : sstate := mkSS AF_both3_reac_master_only_cadence_ns sr_atoms moc_regions None moc_facts.
Definition moc_SH : list shent := [mkSHE (A_OBJ 65) 0 12].
Definition moc_Bspan : Z * Z := (MSB, MSB + 2 ^ 44 - 1).
Definition moc_extra (f8 : word) : list word := [Z_to_bv 64 MSB; f8].
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

Lemma moc_keep : forall (fa fb : YK11.FPState) (W : world SEGS) E ss ms md Q (STK sp0 : Z) FPl ly S W0 mem0 md0 own lyc Sc k,
  st_ok_pi (fx := fa) SEGS VAL E ss (restrict (w_H W) ms) ->
  ss_resv ss = None -> 0 <= ss_pc ss < 2 ^ 40 ->
  RiscvSemantics.step SEGS (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) =
    MachineOk (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS)) ->
  ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  (forall md', st_ok_pi (fx := fb) SEGS VAL E (setpc ss (ss_pc ss + 4))
       (restrict (w_H W) (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS))) ->
     ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md' k ->
     SRr SEGS W (mkCfg (@mkst fb (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) (ms_mem ms) (seg_rom SEGS)) md') Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros fa fb W E ss ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k HS Hrv Hk Hst HJ HK.
pose proof (@pa_segs_low _ _ PI) as Hsegs.
pose proof (st_ok_pi_restrict_mkst (fx := fa) (w_H W) E ss ms HS Hrv) as Hms.
rewrite Hms. rewrite Hms in HS.
eapply (fp_keep_step SEGS B LAWS (@pa_wx _ _ PI) Hsegs W fa fb (ms_regs ms) (ms_regs ms) _ _ (ms_mem ms) md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k Hst HJ).
intros md' HJ'. apply HK; [|exact HJ'].
pose proof pa_B_ok as HB.
pose proof (fp_switch SEGS fa fb E (abs_ss VAL ss) (@mkst fa (ms_regs ms) (Z_to_bv 64 (BASE + ss_pc ss)) (ms_mem ms) (seg_rom SEGS)) (w_H W)
  (ss_regs ss) (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) HS) as H1.
assert (HR : regs_ok E (ss_regs ss) (ms_regs ms)).
{ destruct HS as (_ & _ & _ & _ & _ & _ & H7 & _). exact H7. }
specialize (H1 HR). unfold st_ok_pi, abs_ss, setpc. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in H1 |- *.
rewrite Hrv. rewrite unsigned_lit_small in H1 by lia. exact H1.
Qed.
Section w.
Context {fx : YK11.FPState}.
Lemma moc_entry : forall ly S W (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (moc_extra (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 8))))) ss_moc
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_both3_reac_master_only_cadence_ns)) mem (seg_rom SEGS))).
Proof.
intros ly S W regs mem md ch HPRE.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite fp_spZ_upd in Hstk, Hpres by (cbv; discriminate).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_MASTER_ONLY_CADENCE_NS_STK = 4208) by reflexivity.
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & _ & Kgot & _). rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
pose proof (pa_obj_img_all 65 ltac:(cbv; lia)) as HratesR.
unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HcellR, HgotR, HratesR.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (moc_extra (Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 8))))).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 MSB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E43 : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E306 : ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
unfold ss_moc. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold moc_regions, stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
    [cbn [sv_denot]; rewrite E43, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
  + rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by (pose proof (pa_val_range (A_OBJ 12)); lia). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 moc_Bx MSB);
    [cbn [sv_denot moc_Bx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold MSB; zside | zside |].
    rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
- apply pairwise_disjoint_of_extents. unfold moc_regions, stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
  rewrite (VB (A_OBJ 12) (VAL (A_OBJ 12)) E43) by (pose proof (pa_val_range (A_OBJ 12)); lia).
  cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  revert Hslo Hshi H47 Hceil C1 WS Hstk0 HcellR HgcD HgotR. clear. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [moc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, E306, !unsigned_lit_small by (unfold MSB; pose proof (pa_val_range (A_OBJ 65)); lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  revert Hslo Hshi H47 Hceil Hal16 C1 WS Hstk0 HratesR. clear. unfold MSB, YImgTop.IMG_LO, YImgTop.IMG_TOP. intros.
  repeat match goal with |- _ /\ _ => split end; lia.
Qed.

Lemma moc_fsd : forall (W : world SEGS) E ss ms md Q (STK sp0 : Z) FPl ly S W0 mem0 md0 own lyc Sc k rs' (rs1 rs2 : bv 5) (imm : bv 12),
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  plookup both3_0_tpi (ss_pc ss) = Some (PW 0x813027) -> 0 <= ss_pc ss < 2 ^ 40 ->
  decode_any (Z_to_bv 32 0x813027) = Some (FStore FMT_D rs1 rs2 imm, 4%Z) ->
  bv_unsigned rs1 = 2 -> bv_unsigned rs2 = 8 -> bv_signed imm = 0 ->
  sr_get (ss_regs ss) 2 = SOff 2 (-112) ->
  ew E 33 = Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 8) ->
  sstore (ss_mem ss) (Some 2%nat) (-112) SZ8 (SOff 33 0) = Some rs' ->
  ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms) md k ->
  awr_ok E (ss_mem ss) STK sp0 FPl (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall x : word, w_H W x = true -> ~ in_wrange E (ss_mem ss) (bv_unsigned x)) ->
  (forall ms1 mat', ms_regs ms1 = ms_regs ms ->
     (forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) -> ms_mem ms1 x = ms_mem ms x) ->
     st_ok_pi SEGS VAL E (mkSST (ss_pc ss + 4) (ss_regs ss) (ss_fregs ss) rs' None (ss_facts ss)) (restrict (w_H W) ms1) ->
     ajournal SEGS B STK sp0 FPl ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat' md) k ->
     SRr SEGS W (mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros W E ss ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k rs' rs1 rs2 imm HS Hrv Hpl Hk Hd Hrs1 Hrs2 Him Hr2 E33 Hst HJ Hawr Hnh HK.
replace rs1 with (2%bv : bv 5) in Hd by (apply bv_eq; rewrite Hrs1; reflexivity).
replace rs2 with (8%bv : bv 5) in Hd by (apply bv_eq; rewrite Hrs2; reflexivity).
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof (@pa_wx _ _ PI) as Hwx. pose proof pa_B_ok as HB.
pose proof (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv) as Hms.
pose proof HS as (Hfr & Hpc & Hsvc & Hres & Hfcsr & Hrom & Hregs & Hmem & HG).
cbn [restrict ms_mem ms_regs ms_svc_pending abs_ss setpc ss_mem ss_regs ss_facts] in Hmem, Hregs, Hsvc, HG.
destruct (sstore_sound SEGS E _ _ _ _ _ _ _ Hmem Hst) as [Hok Hmem'].
pose proof Hst as Hst0. unfold sstore in Hst0.
destruct (store_region_shape _ _ _ _ _ _ Hst0) as (l1 & r & l2 & Hrs & _ & Hrb & Hrlo & Hrhi & Hrwlo & Hrwhi).
assert (Hrok : region_ok SEGS E (mrestrict (w_H W) (ms_mem ms)) r).
{ apply (mem_ok_region SEGS E _ (ss_mem ss) r Hmem). rewrite Hrs. apply in_or_app. right. left. reflexivity. }
destruct Hrok as (Hr0 & Hr64 & _ & _). rewrite Hrb in Hr0, Hr64. cbn [nbytes Z.of_nat Pos.of_succ_nat Pos.succ] in Hrhi, Hrwhi.
set (bs := st_bytes (nbytes SZ8) (sv_denot E (SOff 33 0))) in *.
set (a := Z_to_bv 64 (base_val E (Some 2%nat) + -112)) in *.
set (mem' := wbytes (mrestrict (w_H W) (ms_mem ms)) a bs) in *.
assert (Hbl : length bs = 8%nat) by (unfold bs, st_bytes; apply length_zbytes).
assert (Ha : bv_unsigned a = base_val E (Some 2%nat) + -112) by (unfold a; apply unsigned_lit_small; lia).
assert (Hin : forall x : word, bv_unsigned a <= bv_unsigned x < bv_unsigned a + 8 -> in_wrange E (ss_mem ss) (bv_unsigned x)).
{ intros x Hx. exists r. split; [rewrite Hrs; apply in_or_app; right; left; reflexivity|]. rewrite Hrb. lia. }
assert (Hstep : RiscvSemantics.step SEGS (restrict (w_H W) ms) =
  MachineOk (@mkst fx (ms_regs ms) (Z_to_bv 64 (BASE + (ss_pc ss + 4))) mem' (seg_rom SEGS))).
{ rewrite Hms at 1. rewrite restrict_mkst_fx.
  rewrite (YK0o.fp_step_fsd fx SEGS (ms_regs ms) _ (mrestrict (w_H W) (ms_mem ms)) (seg_rom SEGS) (Z_to_bv 32 0x813027) 2%bv 8%bv imm a).
  - rewrite YCbn.v_addi_lit. unfold mem', bs. do 3 f_equal; [lia|].
    unfold word_to_le_bytes. rewrite Z_to_le_bytes_st. f_equal. cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - apply (pa_fetch_pw (PL := PL_both3_0)). exact Hpl.
  - vm_compute. reflexivity.
  - exact Hd.
  - rewrite Hregs, Hr2. unfold a, v_addi. cbn [sv_denot base_val]. f_equal. rewrite Z_to_bv_unsigned. rewrite Him.
    rewrite Z.add_0_r. unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). cbn [base_val] in Hr0, Hr64. lia.
  - rewrite <- Hbl. exact Hok. }
eapply (fp_write_step SEGS B LAWS Hwx Hsegs fx W E (abs_ss VAL (mkSST (ss_pc ss + 4) (ss_regs ss) (ss_fregs ss) rs' None (ss_facts ss)))
  ms md Q STK sp0 FPl ly S W0 mem0 md0 own lyc Sc k (in_wrange E (ss_mem ss)) mem' (Z_to_bv 64 (BASE + (ss_pc ss + 4)))).
- exact Hsvc.
- exact HJ.
- exact Hstep.
- unfold st_ok, abs_ss, setpc. cbn [mkst ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts resv_denot].
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [exact Hregs|]. split; [exact Hmem' | exact HG].
- intros x Hx. unfold mem'.
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
  { rewrite wbytes_below; [unfold mrestrict; rewrite Hx; reflexivity | rewrite Hbl; lia | exact Hlt]. }
  destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + 8)) as [Hlt2|Hge2].
  { exfalso. exact (Hnh x Hx (Hin x (conj Hge Hlt2))). }
  rewrite wbytes_above; [unfold mrestrict; rewrite Hx; reflexivity | rewrite Hbl; lia].
- intros x Hx. unfold mem'. unfold a.
  pose proof (store_region_frame SEGS E (mrestrict (w_H W) (ms_mem ms)) (ss_mem ss) (Some 2%nat) (-112) (CVal (N.of_nat (nbytes SZ8)) (SOff 33 0)) bs rs' Hmem) as Hf.
  rewrite Hbl in Hf. specialize (Hf Hst0 ltac:(lia)). exact (Hf x Hx).
- apply wbytes_grows.
- intros x Hx. exact (Hawr x Hx).
- intros ms1 mat' R1 HM1 Hhid HS1 HJ1. apply HK; [exact R1 | | exact HS1 | exact HJ1].
  intros x Hx. destruct (w_H W x) eqn:Hh; [exact (Hhid x Hh)|].
  pose proof (f_equal (fun f => f x) HM1) as E1. cbn beta in E1. unfold mrestrict in E1. rewrite Hh in E1. rewrite E1.
  unfold mem', a. pose proof (store_region_frame SEGS E (mrestrict (w_H W) (ms_mem ms)) (ss_mem ss) (Some 2%nat) (-112) (CVal (N.of_nat (nbytes SZ8)) (SOff 33 0)) bs rs' Hmem) as Hf.
  rewrite Hbl in Hf. specialize (Hf Hst0 ltac:(lia)). rewrite (Hf x Hx). unfold mrestrict. rewrite Hh. reflexivity.
Qed.

Lemma moc_ge0 : forall E fps, ew E 10 = Z_to_bv 64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff 10 0)) = (fps <=? 0).
Proof.
intros E fps H Hr. cbn [branch_taken sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned.
unfold bv_lts. rewrite !Z_to_bv_signed.
assert (S1 : bv_swrap 64 fps = fps).
{ unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64).
  rewrite Z.mod_small by lia. lia. }
rewrite S1. change (bv_swrap 64 0) with 0.
destruct (Z.leb_spec fps 0); destruct (Z.ltb_spec 0 fps); cbn [negb]; first [reflexivity | lia].
Qed.

Lemma moc_kept_ext : forall E (H : word -> bool) (m m' : word -> option byte) rs,
  (forall x, m' x = m x) -> Forall (region_kept SEGS E (mrestrict H m) (mrestrict H m')) rs.
Proof.
intros E H m m' rs Hm. apply Forall_forall. intros r _. split; intros a _.
- unfold mbyte, mrestrict. rewrite Hm. reflexivity.
- unfold writable_at, wview, mrestrict. rewrite Hm. exact (fun X => X).
Qed.
Lemma moc_csr_tr : forall c0 c1 c2 : bv 32,
  c1 = c0 \/ Z.land (Z.shiftr (bv_unsigned c1) 5) 7 = 0 ->
  c2 = c1 \/ Z.land (Z.shiftr (bv_unsigned c2) 5) 7 = 0 ->
  c2 = c0 \/ Z.land (Z.shiftr (bv_unsigned c2) 5) 7 = 0.
Proof.
intros c0 c1 c2 [H1|H1] [H2|H2]; [left; congruence | right; exact H2 | right; subst c2; exact H1 | right; exact H2].
Qed.
Lemma moc_call : forall (fa : YK11.FPState) (W : world SEGS) E ss ms md Q (sp0 : Z) ly S mem0 md0 lyc Sc
    (k : nat) (rs : smem) retk,
  img_env VAL A_LIM E ->
  st_ok (fx := fa) SEGS E (setpc ss (SIGMA AS_reac_rate_snap)) (restrict (w_H W) ms) -> ss_resv ss = None ->
  ajournal SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK sp0 [] ly S W mem0 md0 [] lyc Sc W (ms_mem ms) md 0 ->
  sr_get (ss_regs ss) 1 = SOff A_TEXT retk -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  sr_get (ss_regs ss) 2 = SOff 2 (-112) -> bv_unsigned (ew E 2) = sp0 ->
  sr_get (ss_regs ss) 3 = SOff 3 0 -> ew E 3 = w64 (as_gp B) ->
  sr_get (ss_regs ss) 4 = SOff 4 0 -> ew E 4 = w64 (as_tp B) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem0) ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (VAL (A_HI 98) + 1812) 8 D3837 ->
  (k + 16 <= A_TEXT)%nat -> ss_atoms_p (pband k A_TEXT) ss = true ->
  regions_wf rs = true -> no_cdata rs = true -> mem_atoms_p (pband k A_TEXT) rs = true -> submem rs (ss_mem ss) ->
  (forall (fb : YK11.FPState) regs2 mem2 md2 ly2 S2,
     (forall k : bv 5, bv_unsigned k <> 10 ->
        Sem.reg_get (@YK11.fp_regs fb) k =
        Sem.reg_get (bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837) (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) (@YK11.fp_regs fa))) k) ->
     (@YK11.fp_csr fb = reac_rate_snap_fcsr (Sem.reg_get (@YK11.fp_regs fa) (Z_to_bv 5 10)) (@YK11.fp_csr fa) \/
      Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fb)) 5) 7 = 0) ->
     ajournal SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK sp0 [] ly S W mem0 md0 [] ly2 S2 W mem2 md2 0 ->
     getr regs2 10 = w64 (reac_rate_snap_model (Sem.reg_get (@YK11.fp_regs fa) (Z_to_bv 5 10))) ->
     Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) ->
     (forall x, mem2 x = ms_mem ms x) ->
     st_ok_pi (fx := fb) SEGS VAL (havoc E k (map (getr regs2) CLOB)) (ss_after_call ss rs k retk)
        (restrict (w_H W) (@mkst fb regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS))) ->
     SRr SEGS W (mkCfg (@mkst fb regs2 (Z_to_bv 64 (BASE + retk)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS W (mkCfg ms md) Q.
Proof.
intros fa W E ss ms md Q sp0 ly S mem0 md0 lyc Sc k rs retk HEI HS Hrv HJ Hr1 Hrk Hrk2 Hr2 Usp Hr3 E3 Hr4 E4 HROD H6 H3
  Hk Hat Hwf Hnc Hmat Hsub HK.
pose proof (@pa_segs_low _ _ PI) as Hsegs. pose proof pa_B_ok as HB. pose proof (pa_base_lo (PL := PL_both3_0)) as HBLO.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (Hrv' : ss_resv (setpc ss (SIGMA AS_reac_rate_snap)) = None) by exact Hrv.
pose proof (st_ok_restrict_mkst SEGS (w_H W) E _ ms HS Hrv') as Hms. cbn [ss_pc setpc] in Hms.
rewrite pa_sigma_reac_rate_snap in Hms.
pose proof HS as (_ & _ & _ & _ & _ & _ & Hregs & _).
cbn [restrict ms_regs setpc ss_regs] in Hregs.
set (R := ms_regs ms) in *. set (M := ms_mem ms) in *.
assert (R1 : getr R 1 = Z_to_bv 64 (BASE + retk)) by (rewrite Hregs, Hr1; exact (codeptr_val E retk HEI)).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (R2 : spZ R = sp0 - 112).
{ unfold spZ. rewrite Hregs, Hr2. rewrite denot_SOff, Usp. apply zcanon_id. unfold M64. pose proof (asan_consts) as (C1' & _). lia. }
assert (R3 : getr R 3 = w64 (as_gp B)) by (rewrite Hregs, Hr3; cbn [sv_denot]; rewrite E3, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (R4 : getr R 4 = w64 (as_tp B)) by (rewrite Hregs, Hr4; cbn [sv_denot]; rewrite E4, Z.add_0_r; apply Z_to_bv_bv_unsigned).
assert (HPRE : afn_pre SEGS B REAC_RATE_SNAP_STK lyc Sc W (regupd R 8 (Z_to_bv 64 0)) M md []).
{ eapply (afn_pre_at SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK sp0 [] ly S W mem0 md0 [] lyc Sc W M md 0 _ REAC_RATE_SNAP_STK (-112) [] HJ).
  - rewrite fp_spZ_upd by (cbv; discriminate). lia.
  - reflexivity.
  - lia.
  - unfold REAC_RATE_SNAP_STK, ESTACK. lia.
  - unfold REAC_RATE_SNAP_STK, REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK, ESTACK. lia.
  - rewrite fp_getr_upd by (cbv; discriminate). rewrite R1. apply ret_ok_codeptr_v; lia.
  - unfold raZ. rewrite fp_getr_upd by (cbv; discriminate). rewrite R1. rewrite unsigned_lit_small by lia. unfold YImgTop.IMG_LO in HBLO. lia.
  - rewrite fp_getr_upd by (cbv; discriminate). exact R3.
  - rewrite fp_getr_upd by (cbv; discriminate). exact R4.
  - apply achain_low. unfold s0Z. rewrite getr_same by (cbv; discriminate).
    rewrite unsigned_lit_small by lia. lia. }
assert (HROD' : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) M))
  by exact (arodata_ok_journalP SEGS pa_relro_lo pa_relro_hi pa_relro_img B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD).
rewrite Hms.
change (mkCfg (@mkst fa R (Z_to_bv 64 (BASE + AF_both3_reac_rate_snap)) M (seg_rom SEGS)) md)
  with (cfg_at (fx := fa) SEGS (BASE + AF_both3_reac_rate_snap) R M md).
eapply SRr_bind; [exact (TRATE fa lyc Sc W R M md [] HPRE HROD' H6 H3)|].
intros W2 c2 _ (fq' & Hfr & Hcsr & fb & ly2 & S2 & regs2 & mem2 & md2 & Hc2 & Hfr2 & Hcsr2 & HJ2 & HP2 & Ha0 & Hperm & HW2 & Hmem2).
subst W2 c2. rewrite R1.
assert (HFR : forall k : bv 5, bv_unsigned k <> 10 ->
  Sem.reg_get (@YK11.fp_regs fb) k =
  Sem.reg_get (bvmap_set (Z_to_bv 5 14) (Z_to_bv 64 D3837) (bvmap_set (Z_to_bv 5 15) (Z_to_bv 64 D6000) (@YK11.fp_regs fa))) k)
  by (intros kk K10; rewrite (Hfr2 kk K10), Hfr; reflexivity).
assert (HCSR : @YK11.fp_csr fb = reac_rate_snap_fcsr (Sem.reg_get (@YK11.fp_regs fa) (Z_to_bv 5 10)) (@YK11.fp_csr fa) \/
  Z.land (Z.shiftr (bv_unsigned (@YK11.fp_csr fb)) 5) 7 = 0) by (rewrite <- Hcsr; exact Hcsr2).
clear Hfr Hcsr Hfr2 Hcsr2.
assert (HJ3 : ajournal SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK sp0 [] ly S W mem0 md0 [] ly2 S2 W mem2 md2 0).
{ rewrite R2 in HJ2. replace 0 with (0 + 0) by reflexivity. change (@nil (Z * Z)) with (@nil (Z * Z) ++ []) at 2.
  eapply (ajournal_sub SEGS B LAWS Hsegs); [exact HJ | exact HJ2 | unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK, ESTACK; lia | lia | intros a (rg & [] & _)]. }
pose proof (st_ok_pi_after_call k E (setpc ss (SIGMA AS_reac_rate_snap)) (restrict (w_H W) ms) regs2 (mrestrict (w_H W) mem2) rs retk
  HEI Hrk HS Hrv' Hk Hat Hwf Hnc Hmat Hsub Hr1 HP2 (moc_kept_ext E (w_H W) M mem2 rs Hmem2)) as HS2.
apply (HK fb regs2 mem2 md2 ly2 S2 HFR HCSR HJ3 Ha0 Hperm Hmem2).
rewrite YA0o.restrict_mkst_fx.
exact (fp_st_ok_fx SEGS fa fb _ _ regs2 _ _ _ HS2).
Qed.

Lemma moc_keep_tr : forall (sp : Z) (m m' m0 : word -> option byte) E rs,
  (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp) -> m x = m0 x) ->
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> sp - 112 <= a < sp) ->
  forall x : word, ~ (sp - 112 <= bv_unsigned x < sp) -> m' x = m0 x.
Proof. intros sp m m' m0 E rs K HF Hw x Hx. rewrite HF; [apply K; exact Hx|]. intros Hin. apply Hx. apply Hw. exact Hin. Qed.
Ltac wr_tac Usp :=
  let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hrng := fresh "Hrng" in
  intros a (r & Hr & Hrng); vm_compute in Hr;
  repeat (destruct Hr as [<-|Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val ew ewset Nat.eqb] in Hrng; rewrite ?Usp in Hrng; lia|]);
  destruct Hr.
Ltac kup K Usp :=
  match goal with HF : frame_of _ _ _ _ |- _ =>
    let K' := fresh "K" in
    pose proof (moc_keep_tr _ _ _ _ _ _ K HF) as K'; specialize (K' ltac:(wr_tac Usp));
    clear K HF; rename K' into K
  end;
  repeat (match goal with H : frame_of _ _ _ _ |- _ => clear H end);
  repeat (match goal with H : mem_grows _ _ |- _ => clear H end).
Ltac pcr := lazymatch goal with |- 0 <= ?p < _ => let v := eval vm_compute in p in change p with v; lia end.
Ltac slot_w k := let w := eval vm_compute in (match plookup both3_0_tpi k with Some (PW w) => w | _ => 0 end) in w.

Ltac fmv_step W E fa fb :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  eapply (moc_keep fa fb W E ss msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS eq_refl ltac:(pcr));
  [ let k := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with k;
    let w := slot_w k in
    let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    lazymatch d with Some (Fsgnj _ _ ?rd ?rs ?rs2, _) =>
      rewrite (fp_step_fmv_d fa SEGS _ _ _ _ (Z_to_bv 32 w) rd rs (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity))
        ltac:(vm_compute; reflexivity)
        ltac:(transitivity (Some (Fsgnj F_SGNJ FMT_D rd rs rs2, 4%Z)); [vm_compute; reflexivity | do 3 f_equal; apply bv_eq; reflexivity]));
      rewrite YCbn.v_addi_lit, <- Z.add_assoc;
      replace rd with (Z_to_bv 5 10) by (apply bv_eq; reflexivity);
      replace rs with (Z_to_bv 5 8) by (apply bv_eq; reflexivity);
      reflexivity
    end
  | exact HJ | ]; clear HS HJ; intros ? HS HJ
  end.

Ltac prun Usp := lazymatch goal with HS : @st_ok_pi _ _ ?fc _ _ _, SHOK : YCbn.sh_ok _ _ _ _ _ |- _ =>
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R := constr:(paj_run (fx := fc) (PL := PL_both3_0) (PI := PI) B LAWS) in
  paj_run_tok R HS HJ SHOK moc_Bspan; [awr_ok_tac; exact Usp | ] end end.
Ltac prun_to Usp stop := lazymatch goal with HS : @st_ok_pi _ _ ?fc _ _ _, SHOK : YCbn.sh_ok _ _ _ _ _ |- _ =>
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let R := constr:(paj_run_to (fx := fc) (PL := PL_both3_0) (PI := PI) B LAWS) in
  paj_run_to_tok R HS HJ SHOK moc_Bspan stop; [awr_ok_tac; exact Usp | ] end end.
Ltac pbranch := lazymatch goal with HS : @st_ok_pi _ _ ?fc _ _ _, SHOK : YCbn.sh_ok _ _ _ _ _ |- _ =>
  let R := constr:(paj_run (fx := fc) (PL := PL_both3_0) (PI := PI) B LAWS) in
  let BRf := constr:(paj_branch (fx := fc) (PI := PI)) in
  psrr_branch_tok R BRf HS SHOK moc_Bspan end.

Lemma moc_vm_keep : forall (W : world SEGS) (m m0 : word -> option byte) sp a n v,
  (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp) -> m x = m0 x) ->
  0 <= a -> a + Z.of_nat n <= sp - 112 -> sp <= 2 ^ 64 ->
  val_mem SEGS (mrestrict (w_H W) m0) a n v -> val_mem SEGS (mrestrict (w_H W) m) a n v.
Proof.
intros W m m0 sp a n v K Ha Hn Hsp Hv k Hk. rewrite <- (Hv k Hk). unfold mbyte, mrestrict.
rewrite K; [reflexivity|]. rewrite unsigned_lit_small by lia. lia.
Qed.
Ltac pcall W E k Usp E3 E4 HROD HEI V6 V3 :=
  lazymatch goal with HS : st_ok _ _ (setpc ?ss _) (restrict _ ?msx) |- _ =>
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
    let retk := eval vm_compute in (match sr_get (ss_regs ss) 1%bv with SOff _ z => z | _ => 0 end) in
    eapply (moc_call _ W E ss msx _ _ _ _ _ _ _ _ _ k (ss_mem ss) retk HEI HS eq_refl HJ
       ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(reflexivity) ltac:(vm_compute; reflexivity) Usp
       ltac:(vm_compute; reflexivity) E3 ltac:(vm_compute; reflexivity) E4 HROD V6 V3
       ltac:(unfold A_TEXT; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
       ltac:(vm_compute; reflexivity) ltac:(submem_tac))
  end end.

Lemma rg_other_lit : forall (m : bvmap 5 word) n (k : bv 5) (v : word), bv_unsigned k <> n -> 0 <= n < 32 ->
  Sem.reg_get (bvmap_set (Z_to_bv 5 n) v m) k = Sem.reg_get m k.
Proof. intros m n k v Hk Hn. apply fp_rg_other. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia. Qed.
Ltac fld_step W Ec F8 E33 :=
  lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss (restrict _ ?msx) |- _ =>
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let HRg := fresh "HRg" in let HMm := fresh "HMm" in let HGf := fresh "HGf" in
  pose proof HS as (_ & _ & _ & _ & _ & _ & HRg & HMm & HGf);
  cbn [restrict ms_regs ms_mem abs_ss setpc ss_mem ss_regs ss_facts] in HRg, HMm, HGf;
  let bs := fresh "bs" in let Hrd := fresh "Hrd" in let Hbs := fresh "Hbs" in
  destruct (sload_sound SEGS Ec _ _ _ (Some 2%nat) (-112) SZ8 true (SOff 33 0) HGf HMm ltac:(vm_compute; reflexivity)) as (bs & Hrd & Hbs);
  cbn [load_result sv_denot] in Hbs; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned in Hbs;
  eapply (moc_keep fc (mkFP (bvmap_set (Z_to_bv 5 8) F8 (@YK11.fp_regs fc)) (@YK11.fp_csr fc)) W Ec ss msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS eq_refl ltac:(pcr));
  [ let k := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with k;
    let w := slot_w k in
    let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    lazymatch d with Some (FLoad _ ?rd ?rs ?im, _) =>
      rewrite (YK0o.fp_step_fld fc SEGS _ _ _ _ (Z_to_bv 32 w) rd rs im (Z_to_bv 64 (base_val Ec (Some 2%nat) + -112)) bs (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity))
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      [ rewrite YCbn.v_addi_lit, <- Z.add_assoc, bv_extract_0_64, <- Hbs;
        replace rd with (Z_to_bv 5 8) by (apply bv_eq; reflexivity); reflexivity
      | rewrite HRg; replace rs with (2%bv : bv 5) by (apply bv_eq; reflexivity);
        replace (bv_signed im) with 0 by reflexivity;
        lazymatch goal with |- v_addi (sv_denot _ ?e) 0 = _ => let e' := eval vm_compute in e in change e with e' end;
        cbn [sv_denot base_val]; rewrite v_addi_0; reflexivity
      | exact Hrd ]
    end
  | exact HJ | ];
  clear HS HJ HRg HMm HGf Hrd Hbs; intros ? HS HJ
  end end.

Definition moc_rates_region : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 65)) 0 12 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit 44100)); YP09.mkChunk 4 (CVal 4 (SLit 48000)); YP09.mkChunk 8 (CVal 4 (SLit 96000))].
Lemma moc_garr8_vm : forall (m : word -> option byte) base l off (n : nat) v,
  garr8 SEGS m base l -> (off + n <= length l)%nat ->
  (forall k, (k < n)%nat -> Z_to_bv 8 (le_byte v n k) = Z_to_bv 8 (le_byte (nth (off + k) l 0) 1 0)) ->
  val_mem SEGS m (base + Z.of_nat off) n v.
Proof.
intros m base l off n v HG Hn Hb k Hk. destruct (HG (off + k)%nat ltac:(lia)) as [Hv _].
specialize (Hv 0%nat ltac:(lia)). rewrite Nat2Z.inj_add, Z.add_0_r, Z.add_assoc in Hv. rewrite Hv. f_equal. symmetry. apply Hb. exact Hk.
Qed.
Lemma moc_rates_ok : forall E (m : word -> option byte),
  ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)) ->
  garr8 SEGS m (VAL (A_OBJ 65)) [68; 172; 0; 0; 128; 187; 0; 0; 0; 119; 1; 0] ->
  region_ok SEGS E m moc_rates_region.
Proof.
intros E m E306 HG. pose proof (pa_obj_img_all 65 ltac:(cbv; lia)) as HR. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HR.
unfold region_ok, moc_rates_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E306, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 65)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat constructor.
- apply (chunk_ok_val SEGS E _ _ 0 4 (SLit 44100) 44100); [reflexivity | lia | lia |].
  apply (moc_garr8_vm m _ _ 0 4 44100 HG); [cbn; lia|]. intros k Hk. destruct k as [|[|[|[|k]]]]; try lia; apply bv_eq; reflexivity.
- apply (chunk_ok_val SEGS E _ _ 4 4 (SLit 48000) 48000); [reflexivity | lia | lia |].
  apply (moc_garr8_vm m _ _ 4 4 48000 HG); [cbn; lia|]. intros k Hk. destruct k as [|[|[|[|k]]]]; try lia; apply bv_eq; reflexivity.
- apply (chunk_ok_val SEGS E _ _ 8 4 (SLit 96000) 96000); [reflexivity | lia | lia |].
  apply (moc_garr8_vm m _ _ 8 4 96000 HG); [cbn; lia|]. intros k Hk. destruct k as [|[|[|[|k]]]]; try lia; apply bv_eq; reflexivity.
Qed.
Lemma moc_shok : forall E (W : world SEGS) (m mem : word -> option byte) (sp : Z),
  ew E 32 = Z_to_bv 64 MSB -> ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)) ->
  (forall x : word, ~ (sp - 112 <= bv_unsigned x < sp) -> m x = mem x) -> 2 ^ 46 <= sp - 112 -> sp <= 2 ^ 64 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  YCbn.sh_ok SEGS moc_Bx moc_SH E (mrestrict (w_H W) m).
Proof.
intros E W m mem sp E32 E306 K Hsp Hsp2 HRA. pose proof (pa_obj_img_all 65 ltac:(cbv; lia)) as HR. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HR.
pose proof (pa_val_range (A_OBJ 65)) as HV.
unfold YCbn.sh_ok, moc_SH. constructor; [|constructor]. split.
- cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi]. unfold moc_Bx.
  rewrite (U_atom E 32 MSB E32) by (unfold MSB; lia). rewrite (U_atom E (A_OBJ 65) _ E306) by lia. rewrite Z.add_0_r.
  apply (range_addressable_agree (aview SEGS (w_H W) mem)); [|exact HRA].
  intros x Hx. unfold YCbn.rd_of, aview, mbyte, mrestrict, shadow_of_addr, SHADOW_OFF, MSB.
  rewrite K; [reflexivity|]. rewrite unsigned_lit_small; [lia|]. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] | ].
  assert (x / 8 <= x) by (apply Z.div_le_upper_bound; lia). lia.
- unfold YCbn.app_apart. cbn [YCbn.she_m YCbn.she_lo YCbn.she_hi]. unfold moc_Bx.
  rewrite (U_atom E 32 MSB E32) by (unfold MSB; lia). rewrite (U_atom E (A_OBJ 65) _ E306) by lia.
  intros a Ha. unfold MSB. lia.
Qed.
Lemma moc_drop : forall (fc : YK11.FPState) E ss ms rs',
  st_ok_pi (fx := fc) SEGS VAL E ss ms -> submem rs' (ss_mem ss) -> regions_wf rs' = true ->
  st_ok_pi (fx := fc) SEGS VAL E (mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) rs' (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros fc E ss ms rs' HS Hsub Hwf. unfold st_ok_pi, abs_ss, setpc, st_ok in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
repeat (split; [assumption|]). split; [|exact H9]. exact (mem_ok_sub SEGS E _ _ _ Hsub Hwf H8).
Qed.

Ltac fcvt_lit_step W E fa z :=
  lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  let Ra := fresh "Ra" in
  prreg HS (10%bv : bv 5) Ra;
  eapply (moc_keep fa (mkFP (bvmap_set (Z_to_bv 5 10) (FP.fcvt_d_wu RNE (Z_to_bv 64 z)) (@YK11.fp_regs fa)) (@YK11.fp_csr fa))
    W E ss msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS eq_refl ltac:(pcr));
  [ let k := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with k;
    let w := slot_w k in
    let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    lazymatch d with Some (Fcvt _ _ ?rd ?rs ?rm, _) =>
      rewrite (fp_step_fcvt_d_wu fa SEGS _ _ _ _ (Z_to_bv 32 w) rd rs rm
        (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      rewrite YCbn.v_addi_lit, <- Z.add_assoc;
      replace rs with (10%bv : bv 5) by (apply bv_eq; reflexivity);
      replace rd with (Z_to_bv 5 10) by (apply bv_eq; reflexivity);
      rewrite Ra, unsigned_lit_small by lia;
      rewrite (reac_master_only_cadence_ns.cvt_fcsr _ z) by lia;
      unfold FP.fcvt_d_wu; rewrite unsigned_lit_small by lia; reflexivity
    end
  | exact HJ | ]; clear HS HJ Ra; intros ? HS HJ
  end.

Lemma moc_agree_ewset : forall E0 E n v, YP06.env_agree 32 E0 E -> (32 <= n)%nat -> YP06.env_agree 32 E0 (ewset E n v).
Proof.
intros E0 E n v [H1 H2] Hn. split; [|exact H2]. intros i Hi. cbn [ew ewset].
replace (Nat.eqb i n) with false by (symmetry; apply Nat.eqb_neq; lia). apply H1. exact Hi.
Qed.

Ltac moc_fp_post :=
  try (lazymatch goal with |- freg_kept _ _ =>
    unfold freg_kept; let kk := fresh "kk" in let K10 := fresh in let K14 := fresh in let K15 := fresh in let K8 := fresh in
    intros kk K10 K14 K15; cbn [YK11.fp_regs];
    destruct (Z.eq_dec (bv_unsigned kk) 8) as [K8|K8];
    [ replace kk with (Z_to_bv 5 8) by (apply bv_eq; rewrite K8; reflexivity); rewrite fp_rg_same; reflexivity
    | repeat first [ rewrite rg_other_lit by lia
                   | match goal with
                     | H : forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@YK11.fp_regs ?f) k = _
                       |- context [Sem.reg_get (@YK11.fp_regs ?f) kk] => rewrite (H kk K10)
                     end
                   | progress cbn [YK11.fp_regs] ]; reflexivity ]
  end);
  try (lazymatch goal with |- @YK11.fp_csr _ = _ => cbn [YK11.fp_csr]; reflexivity end).

Lemma moc_walk : forall ly S W (regs : bvmap 5 word) mem md ch (fps : Z),
  afn_pre SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 fps -> -2 ^ 31 <= fps < 2 ^ 31 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (VAL (A_OBJ 65)) 12 ->
  garr8 SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 65)) (map (fun b : byte => bv_unsigned b) RATES) ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 99) + 1608) 8 D6000 ->
  val_mem SEGS (mrestrict (w_H W) mem) (VAL (A_HI 98) + 1812) 8 D3837 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_both3_reac_master_only_cadence_ns) regs mem md)
    (treac_master_only_cadence_ns_post fx regs ly S W mem md).
Proof.
intros ly S W regs mem md ch fps HPRE HROD H10 Hfps HRA HRT H6 H3.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (moc_entry ly S W regs mem md ch HPRE) as HS.
set (F8 := Sem.reg_get (@YK11.fp_regs fx) (Z_to_bv 5 8)) in HS.
pose proof (ajournal_init SEGS B REAC_MASTER_ONLY_CADENCE_NS_STK [] ly S W (regupd regs 8 (Z_to_bv 64 0)) mem md ch HPRE) as HJ.
rewrite fp_spZ_upd in HJ by (cbv; discriminate).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
rewrite fp_spZ_upd in Hstk, Hpres by (cbv; discriminate).
unfold raZ in Hra4. rewrite fp_getr_upd in Hra, Hra4, Hgp, Htp by (cbv; discriminate).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : REAC_MASTER_ONLY_CADENCE_NS_STK = 4208) by reflexivity.
remember (Eimg (Ereg regs (moc_extra F8))) as E eqn:HE.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 fps) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 MSB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = F8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : YP06.env_agree 32 (Ereg regs (moc_extra F8)) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
unfold cfg_at. change (w64 (BASE + AF_both3_reac_master_only_cadence_ns)) with (Z_to_bv 64 (BASE + AF_both3_reac_master_only_cadence_ns)).
assert (K0 : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem x = mem x) by (intros; reflexivity).
prun Usp.
assert (K1 : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> ms_mem ms x = mem x).
{ intros x Hx. apply HF. intros (r & Hr & Hrng). vm_compute in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?Usp in Hrng; lia. }
clear HF HFr HG K0.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  let rs' := eval vm_compute in (match sstore (ss_mem ss) (Some 2%nat) (-112) SZ8 (SOff 33 0) with Some r => r | None => [] end) in
  let d := eval vm_compute in (decode_any (Z_to_bv 32 0x813027)) in
  lazymatch d with Some (FStore _ ?r1 ?r2 ?im, _) =>
  eapply (moc_fsd W E ss msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ rs' r1 r2 im HS eq_refl); 
  [ vm_compute; reflexivity | lazymatch goal with |- 0 <= ?p < _ => let v := eval vm_compute in p in change p with v end; lia | vm_compute; reflexivity | reflexivity | reflexivity | reflexivity
  | vm_compute; reflexivity | exact E33 | vm_compute; reflexivity | exact HJ | awr_ok_tac; exact Usp
  | intros x Hx (r & Hr & Hrng); vm_compute in Hr;
    destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?Usp in Hrng; try lia;
    destruct (HJpres (bv_unsigned x) ltac:(lia)) as [Hh _]; rewrite Z_to_bv_bv_unsigned in Hh; congruence
  | ]
  end
end.
intros ms1 mat1 R1 HM1 HS1 HJ1.
assert (K : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> ms_mem ms1 x = mem x).
{ intros x Hx. rewrite HM1; [apply K1; exact Hx|]. intros (r & Hr & Hrng). vm_compute in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrng; rewrite ?Usp in Hrng; lia. }
clear K1 HM1 HS HJ SHOK.
rename HS1 into HS, HJ1 into HJ.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx [] E (mrestrict (w_H W) (ms_mem ms1))) by constructor.
prun Usp.
kup K Usp.
assert (E3' : ew E 3 = w64 (as_gp B)) by (rewrite E3; exact Hgp).
assert (E4' : ew E 4 = w64 (as_tp B)) by (rewrite E4; exact Htp).
pose proof (pa_hi_img 99 ltac:(cbv; lia)) as Hh99. pose proof (pa_hi_img 98 ltac:(cbv; lia)) as Hh98.
unfold YImgTop.IMG_TOP in Hh99, Hh98.
pbranch.
2:{
rewrite (moc_ge0 E fps E10 Hfps) in Hc. apply Z.leb_gt in Hc.
prun Usp.
kup K Usp.
set (F0 := @YK11.fp_regs fx) in *. set (C0 := @YK11.fp_csr fx) in *.
set (X := FP.fcvt_d_wu RNE (Z_to_bv 64 fps)).
assert (HXn : fp_is_nan fmt_double (bv_unsigned X) = false) by (apply reac_master_only_cadence_ns.cvt_nan; lia).
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  prreg HS (10%bv : bv 5) Ra0; rewrite E10 in Ra0;
  eapply (moc_keep fx (mkFP (bvmap_set (Z_to_bv 5 8) X F0) C0) W E ss msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS eq_refl ltac:(pcr));
  [ let k := eval vm_compute in (ss_pc ss) in change (ss_pc ss) with k;
    let w := slot_w k in
    let d := eval vm_compute in (decode_any (Z_to_bv 32 w)) in
    lazymatch d with Some (Fcvt _ _ ?rd ?rs ?rm, _) =>
      rewrite (fp_step_fcvt_d_wu fx SEGS (ms_regs msx) _ _ _ (Z_to_bv 32 w) rd rs rm
        (pa_fetch_pw (PL := PL_both3_0) k w ltac:(vm_compute; reflexivity)) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
      rewrite YCbn.v_addi_lit, <- Z.add_assoc;
      replace rs with (10%bv : bv 5) by (apply bv_eq; reflexivity);
      replace rd with (Z_to_bv 5 8) by (apply bv_eq; reflexivity);
      rewrite Ra0, unsigned_lit_small by lia; fold F0 C0;
      rewrite (reac_master_only_cadence_ns.cvt_fcsr C0 fps) by lia;
      unfold X, FP.fcvt_d_wu; rewrite unsigned_lit_small by lia; reflexivity
    end
  | exact HJ | ]
end.
clear HS HJ. intros md1 HS HJ.
fmv_step W E (mkFP (bvmap_set (Z_to_bv 5 8) X F0) C0)
  (mkFP (bvmap_set (Z_to_bv 5 10) (Sem.reg_get (bvmap_set (Z_to_bv 5 8) X F0) (Z_to_bv 5 8)) (bvmap_set (Z_to_bv 5 8) X F0)) C0).
rewrite fp_rg_same in HS |- *.
prun Usp.
kup K Usp.
lazymatch goal with HS : st_ok _ _ (setpc _ _) (restrict _ ?msx) |- _ =>
  assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 99) + 1608) 8 D6000)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D6000 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H6]);
  assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 98) + 1812) 8 D3837)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D3837 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H3])
end.
pcall W E 34%nat Usp E3' E4' HROD HEI V6 V3.
clear V6 V3.
clear HS HJ SHOK.
intros fb3 regs2 mem2 md2 ly2 S2 Hfr3 Hcsr3 HJ Ha0 Hperm2 Hmem2 HS.
cbn [YK11.fp_regs YK11.fp_csr] in Hfr3, Hcsr3, Ha0. rewrite fp_rg_same in Hcsr3, Ha0.
rewrite (reac_master_only_cadence_ns.snap_fcsr_keep X C0 HXn) in Hcsr3.
assert (K' : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem2 x = mem x) by (intros x Hx; rewrite Hmem2; apply K; exact Hx).
clear K Hmem2. rename K' into K.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 34)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [lia | exact HAE]).
assert (A38 : ew Ea 38 = getr regs2 10) by (rewrite HEa; reflexivity).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (Ea3 : ew Ea 3 = w64 (as_gp B)) by (rewrite OLDa by lia; exact E3').
assert (Ea4 : ew Ea 4 = w64 (as_tp B)) by (rewrite OLDa by lia; exact E4').
assert (Ea33 : ew Ea 33 = F8) by (rewrite OLDa by lia; exact E33).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx [] Ea (mrestrict (w_H W) mem2)) by constructor.
destruct (reac_master_only_cadence_ns.snap_cases X) as [HM|[HM|HM]]; rewrite HM in Ha0.
all: lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss ?msx |- _ =>
  lazymatch type of Ha0 with getr _ _ = w64 ?z =>
  pose proof (st_ok_pi_pin_reg' (fx := fc) Ea ss msx (10%bv : bv 5) z HS Ha0 eq_refl) as HSp; clear HS; rename HSp into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
  end end.
all: prun Uspa.
all: kup K Uspa.
all: fmv_step W Ea fb3 (mkFP (bvmap_set (Z_to_bv 5 10) (Sem.reg_get (@YK11.fp_regs fb3) (Z_to_bv 5 8)) (@YK11.fp_regs fb3)) (@YK11.fp_csr fb3)).
all: assert (F3_8 : Sem.reg_get (@YK11.fp_regs fb3) (Z_to_bv 5 8) = X)
  by (rewrite Hfr3 by (cbv; discriminate); rewrite !fp_rg_other by (cbv; discriminate); apply fp_rg_same).
all: rewrite F3_8 in HS |- *.
all: prun Uspa.
all: kup K Uspa.
all: lazymatch goal with HS : st_ok _ _ (setpc _ _) (restrict _ ?msx) |- _ =>
  assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 99) + 1608) 8 D6000)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D6000 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H6]);
  assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 98) + 1812) 8 D3837)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D3837 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H3])
end.
all: pcall W Ea 50%nat Uspa Ea3 Ea4 HROD HEIa V6 V3.
all: clear V6 V3 HS HJ SHOK.
all: intros fb5 regs3 mem3 md3 ly3 S3 Hfr5 Hcsr5 HJ Hb0 Hperm3 Hmem3 HS.
all: cbn [YK11.fp_regs YK11.fp_csr] in Hfr5, Hcsr5, Hb0; rewrite fp_rg_same in Hcsr5, Hb0.
all: rewrite (reac_master_only_cadence_ns.snap_fcsr_keep X _ HXn) in Hcsr5; apply (moc_csr_tr _ _ _ Hcsr3) in Hcsr5.
all: rewrite HM in Hb0.
all: assert (K' : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem3 x = mem x) by (intros x Hx; rewrite Hmem3; apply K; exact Hx).
all: clear K Hmem3; rename K' into K.
all: remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
all: assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
all: assert (OLDb : forall n, (n < 50)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEb; apply YN3v.ew_havoc_old; exact Hn).
all: assert (HAEb : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Eb) by (rewrite HEb; apply env_agree_havoc_ge; [lia | exact HAEa]).
all: clear HEb.
all: assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Uspa).
all: assert (Eb33 : ew Eb 33 = F8) by (rewrite OLDb by lia; exact Ea33).
all: lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
all: assert (SHOK : YCbn.sh_ok SEGS moc_Bx [] Eb (mrestrict (w_H W) mem3)) by constructor.
all: lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss ?msx |- _ =>
  lazymatch type of Hb0 with getr _ _ = w64 ?z =>
  pose proof (st_ok_pi_pin_reg' (fx := fc) Eb ss msx (10%bv : bv 5) z HS Hb0 eq_refl) as HSp; clear HS; rename HSp into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
  end end.
all: prun Uspb.
all: kup K Uspb.
all: fld_step W Eb F8 Eb33.
all: prun Uspb.
all: kup K Uspb.
all: lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) Rf1; prreg HS (10%bv : bv 5) Rf10;
  eapply (paj_ret_at (fx := fc) (PL := PL_both3_0) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat;
  unfold treac_master_only_cadence_ns_post;
  exists (mkFP (@YK11.fp_regs fc) (@YK11.fp_csr fx));
  split; [| split; [| exists fc, ly3, S3, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite Rf1, OLDb, OLDa, E1, Hra by lia; reflexivity|];
    split; [intros ? _; reflexivity|];
    split; [cbn [YK11.fp_csr]; assumption|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok (fx := fc) SEGS _ Eb _ _ regs (moc_extra F8) HS); [exact HAEb | vm_compute; reflexivity]|];
    split; [rewrite Rf10; reflexivity|];
    split; [eapply perm_trans; [exact Hperm3 | exact Hperm2]|];
    split; [reflexivity|];
    intros a Ha; apply K; unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK, ESTACK in Ha; lia ]]
end.
all: moc_fp_post.
}
rewrite (moc_ge0 E fps E10 Hfps) in Hc. apply Z.leb_le in Hc.
prun_to Usp 0x84a8.
kup K Usp.
assert (E306 : ew E (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (rewrite <- (HEI (A_OBJ 65) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
pose proof (pa_obj_img_all 65 ltac:(cbv; lia)) as HR65. unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in HR65.
assert (Hsp1 : 2 ^ 46 <= spZ regs - 112) by (unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK, ESTACK in *; lia).
assert (Hsp2 : spZ regs <= 2 ^ 64) by lia.
change (map (fun b : byte => bv_unsigned b) RATES) with [68; 172; 0; 0; 128; 187; 0; 0; 0; 119; 1; 0] in HRT.
lazymatch goal with HS : st_ok_pi _ _ _ ?ss (restrict _ ?msx) |- _ =>
  pose proof (moc_drop fx E ss _ (firstn 1 (ss_mem ss)) HS ltac:(vm_compute; submem_tac) ltac:(vm_compute; reflexivity)) as HSd;
  clear HS;
  lazymatch type of HSd with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HSd end;
  lazymatch type of HSd with st_ok_pi _ _ _ ?ss4 _ =>
  pose proof (st_ok_pi_add_region E ss4 _ moc_rates_region HSd ltac:(vm_compute; reflexivity)) as HS;
  clear HSd
  end;
  specialize (HS ltac:(cbn [restrict ms_mem]; apply (moc_rates_ok E _ E306);
    apply (garr8_frame SEGS (mrestrict (w_H W) mem)); [exact HRT|];
    intros a Ha; cbn [length Z.of_nat Pos.of_succ_nat] in Ha; unfold mbyte, mrestrict; rewrite K; [reflexivity|];
    rewrite unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 65)); lia); lia));
  specialize (HS ltac:(apply all_disjoint_of_extents; unfold moc_rates_region, extent_of_region;
    lazymatch goal with |- context [ss_mem ?x] => let v := eval vm_compute in (ss_mem x) in change (ss_mem x) with v end;
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite E306, Usp, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 65)); lia);
    cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; lia));
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end;
  clear SHOK;
  assert (SHOK : YCbn.sh_ok SEGS moc_Bx moc_SH E (mrestrict (w_H W) (ms_mem msx)))
    by exact (moc_shok E W (ms_mem msx) mem (spZ regs) E32 E306 K Hsp1 Hsp2 HRA)
end.
prun Usp.
kup K Usp.
fcvt_lit_step W E fx 3675.
prun Usp.
kup K Usp.
lazymatch goal with HS : st_ok _ _ (setpc _ _) (restrict _ ?msx) |- _ =>
  assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 99) + 1608) 8 D6000)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D6000 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H6]);
  assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 98) + 1812) 8 D3837)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D3837 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H3])
end.
pcall W E 34%nat Usp E3' E4' HROD HEI V6 V3.
clear V6 V3 HS HJ SHOK.
intros h1 regs2 mem2 md2 ly2 S2 Hfr1 Hcsr1 HJ Ha0 Hperm2 Hmem2 HS.
cbn [YK11.fp_regs YK11.fp_csr] in Hfr1, Hcsr1, Ha0. rewrite fp_rg_same in Hcsr1, Ha0.
rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ (reac_master_only_cadence_ns.cvt_nan 3675 ltac:(lia))) in Hcsr1.
replace (reac_rate_snap_model (FP.fcvt_d_wu RNE (Z_to_bv 64 3675))) with 44100 in Ha0 by (vm_compute; reflexivity).
assert (K' : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem2 x = mem x) by (intros x Hx; rewrite Hmem2; apply K; exact Hx).
clear K Hmem2. rename K' into K.
remember (havoc E 34 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall n, (n < 34)%nat -> ew Ea n = ew E n) by (intros n Hn; rewrite HEa; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEa : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
assert (Ea3 : ew Ea 3 = w64 (as_gp B)) by (rewrite OLDa by lia; exact E3').
assert (Ea4 : ew Ea 4 = w64 (as_tp B)) by (rewrite OLDa by lia; exact E4').
assert (Ea32 : ew Ea 32 = Z_to_bv 64 MSB) by (rewrite OLDa by lia; exact E32).
assert (Ea33 : ew Ea 33 = F8) by (rewrite OLDa by lia; exact E33).
assert (Ea306 : ew Ea (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (rewrite <- (HEIa (A_OBJ 65) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx moc_SH Ea (mrestrict (w_H W) mem2)) by exact (moc_shok Ea W mem2 mem (spZ regs) Ea32 Ea306 K Hsp1 Hsp2 HRA).
lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss ?msx |- _ =>
  pose proof (st_ok_pi_pin_reg' (fx := fc) Ea ss msx (10%bv : bv 5) 44100 HS Ha0 eq_refl) as HSp; clear HS; rename HSp into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
end.
prun Uspa.
kup K Uspa.
fcvt_lit_step W Ea h1 4000.
prun Uspa.
kup K Uspa.
lazymatch goal with HS : st_ok _ _ (setpc _ _) (restrict _ ?msx) |- _ =>
  assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 99) + 1608) 8 D6000)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D6000 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H6]);
  assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 98) + 1812) 8 D3837)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D3837 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H3])
end.
pcall W Ea 50%nat Uspa Ea3 Ea4 HROD HEIa V6 V3.
clear V6 V3 HS HJ SHOK.
intros h2 regs3 mem3 md3 ly3 S3 Hfr2 Hcsr2 HJ Hb0 Hperm3 Hmemx HS.
cbn [YK11.fp_regs YK11.fp_csr] in Hfr2, Hcsr2, Hb0. rewrite fp_rg_same in Hcsr2, Hb0.
rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ (reac_master_only_cadence_ns.cvt_nan 4000 ltac:(lia))) in Hcsr2.
apply (moc_csr_tr _ _ _ Hcsr1) in Hcsr2.
replace (reac_rate_snap_model (FP.fcvt_d_wu RNE (Z_to_bv 64 4000))) with 48000 in Hb0 by (vm_compute; reflexivity).
assert (K' : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem3 x = mem x) by (intros x Hx; rewrite Hmemx; apply K; exact Hx).
clear K Hmemx. rename K' into K.
remember (havoc Ea 50 (map (getr regs3) CLOB)) as Eb eqn:HEx in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEx; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall n, (n < 50)%nat -> ew Eb n = ew Ea n) by (intros n Hn; rewrite HEx; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEb : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Eb) by (rewrite HEx; apply env_agree_havoc_ge; [lia | exact HAEa]).
clear HEx.
assert (Uspb : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact Uspa).
assert (Eb3 : ew Eb 3 = w64 (as_gp B)) by (rewrite OLDb by lia; exact Ea3).
assert (Eb4 : ew Eb 4 = w64 (as_tp B)) by (rewrite OLDb by lia; exact Ea4).
assert (Eb32 : ew Eb 32 = Z_to_bv 64 MSB) by (rewrite OLDb by lia; exact Ea32).
assert (Eb33 : ew Eb 33 = F8) by (rewrite OLDb by lia; exact Ea33).
assert (Eb306 : ew Eb (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (rewrite <- (HEIb (A_OBJ 65) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx moc_SH Eb (mrestrict (w_H W) mem3)) by exact (moc_shok Eb W mem3 mem (spZ regs) Eb32 Eb306 K Hsp1 Hsp2 HRA).
lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss ?msx |- _ =>
  pose proof (st_ok_pi_pin_reg' (fx := fc) Eb ss msx (10%bv : bv 5) 48000 HS Hb0 eq_refl) as HSp; clear HS; rename HSp into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
end.
prun Uspb.
kup K Uspb.
lazymatch goal with HS : st_ok_pi _ _ ?Ex _ _ |- _ => remember Ex as Ebx eqn:HEbx end.
assert (OLDbx : forall n, (n < 512)%nat -> ew Ebx n = ew Eb n)
  by (intros n Hn; rewrite HEbx; cbn [ew ewset]; replace (Nat.eqb n 513) with false by (symmetry; apply Nat.eqb_neq; lia);
      replace (Nat.eqb n 512) with false by (symmetry; apply Nat.eqb_neq; lia); reflexivity).
assert (HAEbx : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Ebx)
  by (rewrite HEbx; apply moc_agree_ewset; [apply moc_agree_ewset; [exact HAEb | lia] | lia]).
lazymatch goal with H : img_env _ _ Ebx |- _ => rename H into HEIbx end.
clear HEbx.
assert (Uspbx : bv_unsigned (ew Ebx 2) = spZ regs) by (rewrite OLDbx by lia; exact Uspb).
assert (Ebx3 : ew Ebx 3 = w64 (as_gp B)) by (rewrite OLDbx by lia; exact Eb3).
assert (Ebx4 : ew Ebx 4 = w64 (as_tp B)) by (rewrite OLDbx by lia; exact Eb4).
assert (Ebx32 : ew Ebx 32 = Z_to_bv 64 MSB) by (rewrite OLDbx by lia; exact Eb32).
assert (Ebx33 : ew Ebx 33 = F8) by (rewrite OLDbx by lia; exact Eb33).
fcvt_lit_step W Ebx h2 8000.
prun Uspbx.
kup K Uspbx.
lazymatch goal with HS : st_ok _ _ (setpc _ _) (restrict _ ?msx) |- _ =>
  assert (V6 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 99) + 1608) 8 D6000)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D6000 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H6]);
  assert (V3 : val_mem SEGS (mrestrict (w_H W) (ms_mem msx)) (VAL (A_HI 98) + 1812) 8 D3837)
    by (apply (moc_vm_keep W _ mem (spZ regs) _ 8 D3837 K); [lia | cbn [Z.of_nat Pos.of_succ_nat]; lia | lia | exact H3])
end.
pcall W Ebx 66%nat Uspbx Ebx3 Ebx4 HROD HEIbx V6 V3.
clear V6 V3 HS HJ SHOK.
intros h3 regs4 mem4 md4 ly4 S4 Hfr3 Hcsr3 HJ Hc0 Hperm4 Hmemx HS.
cbn [YK11.fp_regs YK11.fp_csr] in Hfr3, Hcsr3, Hc0. rewrite fp_rg_same in Hcsr3, Hc0.
rewrite (reac_master_only_cadence_ns.snap_fcsr_keep _ _ (reac_master_only_cadence_ns.cvt_nan 8000 ltac:(lia))) in Hcsr3.
apply (moc_csr_tr _ _ _ Hcsr2) in Hcsr3.
replace (reac_rate_snap_model (FP.fcvt_d_wu RNE (Z_to_bv 64 8000))) with 96000 in Hc0 by (vm_compute; reflexivity).
assert (K' : forall x : word, ~ (spZ regs - 112 <= bv_unsigned x < spZ regs) -> mem4 x = mem x) by (intros x Hx; rewrite Hmemx; apply K; exact Hx).
clear K Hmemx. rename K' into K.
remember (havoc Ebx 66 (map (getr regs4) CLOB)) as Ec eqn:HEx in HS.
assert (HEIc : img_env VAL A_LIM Ec) by (rewrite HEx; apply img_env_havoc; [exact HEIbx | cbv; lia]).
assert (OLDc : forall n, (n < 66)%nat -> ew Ec n = ew Ebx n) by (intros n Hn; rewrite HEx; apply YN3v.ew_havoc_old; exact Hn).
assert (HAEc : YP06.env_agree 32 (Ereg regs (moc_extra F8)) Ec) by (rewrite HEx; apply env_agree_havoc_ge; [lia | exact HAEbx]).
clear HEx.
assert (Uspc : bv_unsigned (ew Ec 2) = spZ regs) by (rewrite OLDc by lia; exact Uspbx).
assert (Ec3 : ew Ec 3 = w64 (as_gp B)) by (rewrite OLDc by lia; exact Ebx3).
assert (Ec4 : ew Ec 4 = w64 (as_tp B)) by (rewrite OLDc by lia; exact Ebx4).
assert (Ec32 : ew Ec 32 = Z_to_bv 64 MSB) by (rewrite OLDc by lia; exact Ebx32).
assert (Ec33 : ew Ec 33 = F8) by (rewrite OLDc by lia; exact Ebx33).
assert (Ec306 : ew Ec (A_OBJ 65) = Z_to_bv 64 (VAL (A_OBJ 65)))
  by (rewrite <- (HEIc (A_OBJ 65) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)); symmetry; apply Z_to_bv_bv_unsigned).
lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end.
assert (SHOK : YCbn.sh_ok SEGS moc_Bx moc_SH Ec (mrestrict (w_H W) mem4)) by exact (moc_shok Ec W mem4 mem (spZ regs) Ec32 Ec306 K Hsp1 Hsp2 HRA).
lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss ?msx |- _ =>
  pose proof (st_ok_pi_pin_reg' (fx := fc) Ec ss msx (10%bv : bv 5) 96000 HS Hc0 eq_refl) as HSp; clear HS; rename HSp into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
end.
prun Uspc.
kup K Uspc.
fld_step W Ec F8 Ec33.
prun Uspc.
kup K Uspc.
lazymatch goal with HS : @st_ok_pi _ _ ?fc _ ?ss (restrict _ ?msc) |- _ =>
  prreg HS (1%bv : bv 5) Rf1; prreg HS (10%bv : bv 5) Rf10;
  eapply (paj_ret_at (fx := fc) (PL := PL_both3_0) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat := fresh "mat" in intros mat;
  unfold treac_master_only_cadence_ns_post;
  exists (mkFP (@YK11.fp_regs fc) (@YK11.fp_csr fx));
  split; [| split; [| exists fc, ly4, S4, (ms_regs msc), (ms_mem msc); eexists;
    split; [cbn [ms_regs]; rewrite Rf1, OLDc, OLDbx, OLDb, OLDa, E1, Hra by lia; reflexivity|];
    split; [intros ? _; reflexivity|];
    split; [cbn [YK11.fp_csr]; assumption|];
    split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
    split; [eapply (aregs_preserved_of_st_ok (fx := fc) SEGS _ Ec _ _ regs (moc_extra F8) HS); [exact HAEc | vm_compute; reflexivity]|];
    split; [rewrite Rf10; reflexivity|];
    split; [eapply perm_trans; [exact Hperm4 | eapply perm_trans; [exact Hperm3 | exact Hperm2]]|];
    split; [reflexivity|];
    intros a Ha; apply K; unfold REAC_MASTER_ONLY_CADENCE_NS_STK, REAC_RATE_SNAP_STK, ESTACK in Ha; lia ]]
end.
all: moc_fp_post.
Qed.
End w.
Theorem pb_reac_master_only_cadence_ns : treac_master_only_cadence_ns_spec.
Proof. intros fq. exact (moc_walk (fx := fq)). Qed.
End h.
End f.
End d.
