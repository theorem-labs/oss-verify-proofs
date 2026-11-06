(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput
   (fuzz_reply.asan 0x845e4-0x84610 and 0x846e0-0x84980, fuzz_reply.c:633-655 and :718-720), in the form of the cgif
   entry walk's arms (proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v: a segment is an SRr from one cut point's invariant to
   the next) over the cut invariants of W_LLVMFuzzerTestOneInput_cut.v.
   THE ARM'S BASE: the pieces every phase of the arm shares.  The phases are proved in
   W_LLVMFuzzerTestOneInput_gone_p<n>.v and composed into lf_arm_gone (= _cut's ARM_gone) in
   W_LLVMFuzzerTestOneInput_gone.v.
   What is here:
   - the gx wrappers of W_frame.v's plain runs (SRr_run_pi_AJX0, SRr_run_to_pi_AJX0, SRr_run_pi_AJX0_call: a run
     that writes the fake frame's shadow, which the token run's static check refuses);
   - the arm's numeric facts from the cut (gn_nums), a shadow entry inside a live block (gn_shent_in_block), the
     entry state at 0x845e4 (gn_entryA, both in.n cases), the frame predicate with the fake frame's shadow as a
     parameter (gframe), and the gn_tools Ltac;
   - the arm's cut points and the predicate of each: GJN 0x846f0, GL1 0x84738 (the reads[] loop's head), GRG
     0x84834 (relay_instance_gone), GC1 0x84848 (the check_no_loss_read loop's head), GT0 0x84864, GCSD 0x8494c
     (check_shape_done, the re-poison and the latch);
   - the arm's model notions (gn_reads, gn_pairs, gn_after_rig, gn_cnl_ok, gn_cshe_ok and the table-order loop's
     relation gn_run), the G each check_* call is taken at (gn_Gs) and the texts of the model obligations
     (GN_RI_*, GN_LS_rig, GN_HG* and the rest), so that every phase file names the same Prop.  The callee
     contracts are W_contract.v's own (lf_arm_gone's Section hypotheses); none is restated here. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
(* Required, not Imported: the live counts (ReplyCnt.acnt) the count rules GN_CNT_rig / GN_CNT_step name, cited by
   their qualified names.  W_contract_x is NOT Required here: the callees' peaks are parameters of those rules *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section px. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {L : ptable wsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Variable G : list (Z * Z).
Lemma SRr_run_to_pi_AJX0 : forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_run_toN_pi pl_tpi n stop ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_to_pi_AJ B LAWS W n stop E ss ss' st ms STK sp0 FP ly S W0 memS md own lyc Sc mdc k Q HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') _ k memS H0 H1);
    [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
End px.
Ltac paj_run_to_shx RUNTOP HS HJ stop :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNTOP with
| forall W n stop E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_run_toN_pi ?tpi n stop ss = _ -> _ =>
let r := eval vm_compute in (sym_run_toN_pi tpi FUEL stop ss) in
lazymatch r with
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_pi tpi FUEL stop ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_to_shx: no hypothesis  img_env _ _ E" end in
eapply (RUNTOP W FUEL stop E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ; paj_after_run_plain HS HJ ]
end
end
| _ => fail "paj_run_to_shx: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.


Section pxc. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Variable G : list (Z * Z).
Lemma SRr_run_pi_AJX0_call : forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
  ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok pa_segs E (setpc ss' (pa_sigma s)) (restrict (w_H W) ms') ->
    ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_pi_AJ_call (PL := PL_fr) B LAWS W n E ss ss' s ms STK sp0 FP ly S W0 memS md own lyc Sc mdc k Q HE HS Hrun HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') _ k memS H0 H1);
    [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
End pxc.


Section pxr. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Variable G : list (Z * Z).
Lemma SRr_run_pi_AJX0 : forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
  img_env pa_val A_LIM E ->
  st_ok_pi pa_segs pa_val E ss (restrict (w_H W) ms) ->
  sym_runN_pi pl_tpi n ss = (ss', st) -> pi_plain_stop st ->
  ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
  awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
  (forall ms' mat',
    st_ok_pi pa_segs pa_val E ss' (restrict (w_H W) ms') ->
    ajournal_gx pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
    frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
    frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
    SRr pa_segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
  SRr pa_segs W (mkCfg ms mdc) Q.
Proof.
  intros W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun Hst HJ Hwr Hk.
  destruct HJ as (H0 & H1 & (memS & HJi & Hag) & Hout). rewrite !Z.add_0_r in HJi.
  apply (SRr_run_pi_AJ (PL := PL_fr) B LAWS W n E ss ss' st ms STK sp0 FP ly S W0 memS md own lyc Sc mdc k Q HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HG].
  apply (ajournal_gx_pack pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') _ k memS H0 H1);
    [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
End pxr.


Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PB_fr).

Lemma gn_nums : forall cx own ly3 S3 W mem md k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k -> own = [(1, fpos)] ->
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in let FF := frame_addr ly3 1 fpos in
  sp0 mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= sp0 <= 2 ^ 47 /\ F mod 32 = 0 /\ sp0 - 352 < F <= sp0 - 320 /\
  4096 <= FF /\ FF + 128 <= alloc_ceiling /\ in_app FF 128 /\ frames S3 = [(1, fpos)] /\
  AR segs B ly3 S3 W mem md.
Proof.
  intros cx own ly3 S3 W mem md k fpos (HAI & HPRE) HJ ->.
  pose proof HPRE as (HFN & _ & _ & _ & _ & _ & _ & Hfr0 & _).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  destruct HJ as (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  rewrite !Z.add_0_r in *.
  destruct HSTK as (Hal & _ & Hceil & Hlo & Hhi & H47 & _).
  rewrite Hfr0, app_nil_r in Hfrs.
  assert (Hin : In (1, fpos) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  pose proof (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HAR Hin) as (H4 & Hc & Happ).
  change (fs_frame_bytes 1) with 128 in Hc, Happ.
  pose proof (YM05.alloc_ceiling_value) as AC.
  cbv zeta. unfold lf_F. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)).
  split; [exact Hal|]. split; [unfold LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.


Lemma gn_shent_in_block : forall ly S (W : world segs) mem md E Bx (m : nat) q p n lo hi,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  U E Bx = SHADOW_OFF -> U E (SOff m 0) = q -> 0 <= lo -> lo <= hi -> p <= q + lo -> q + hi <= p + req_size n ->
  shent_ok segs Bx E (mrestrict (w_H W) mem) (mkSHE m lo hi).
Proof.
  intros ly S W mem md E Bx m q p n lo hi HAR Hin HB Hm Hlo Hlh Hp1 Hp2.
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. rewrite HB, Hm. rewrite <- (aview_rd_of segs).
  destruct (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as [Hbs _].
  split.
  - destruct (Z_lt_le_dec lo hi); [|apply range_addressable_nil; zlia].
    eapply block_shadow_range; [exact Hbs | zlia | zlia].
  - destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _).
    intros a Ha. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. zlia.
Qed.


Definition gn_Bx : sv := SOff 26 0.
Definition gn_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition gn_frA : YP09.region := YP09.mkRegion (Some 9%nat) 32 216 40 216 [YP09.mkChunk 32 (CVal 8 (SLit 6129888))].
Definition gn_inA : YP09.region := YP09.mkRegion (Some 28%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition gn_regA (more : bool) : smem := if more then [gn_frA; gn_inA] else [gn_frA].
Definition gn_factsA : facts :=
  mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (26%nat, mkAF SB SB 0); (28%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 0 255 0)] [] [].
Definition ss_gnA (more : bool) : sstate := mkSS AF_arm_gone sr_atoms (gn_regA more) None gn_factsA.
Definition gn_SHA (more : bool) : list shent := if more then [mkSHE 28 0 1] else [].
Definition gn_extraA (idv : Z) : list word := map (Z_to_bv 64) [idv].
Lemma gn_entryA : forall (W : world segs) ly S mem md regs (more : bool) idv F tv,
  AR segs B ly S W mem md ->
  getr regs 9 = w64 F -> getr regs 26 = w64 SB -> getr regs 28 = w64 tv ->
  2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> awr W mem F 216 -> sv8 W mem (F + 32) 6129888 ->
  4096 <= tv <= 2 ^ 47 -> tv + 1 <= F -> 0 <= idv < 256 ->
  (more = true -> val_mem segs (arm W mem) tv 1 idv /\
     exists p n, In (p, n) (ablocks B ly S) /\ p <= tv /\ tv + 1 <= p + req_size n) ->
  st_ok_pi segs VAL (Eimg (Ereg regs (gn_extraA idv))) (ss_gnA more)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arm_gone)) mem (seg_rom segs)))
  /\ sh_ok segs gn_Bx (gn_SHA more) (Eimg (Ereg regs (gn_extraA idv))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S mem md regs more idv F tv HAR R9 R26 R28 HF1 HF2 HF3 HFw HF32 Ht1 Ht2 Hid Hmore.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (gn_extraA idv))).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  assert (E32 : ew E 32 = Z_to_bv 64 idv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = SB) by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SB; lia).
  assert (U28 : bv_unsigned (ew E 28) = tv) by (rewrite (EE 28%nat 28%bv eq_refl), R28; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = idv) by (rewrite E32; apply unsigned_lit_small; lia).
  split.
  - unfold ss_gnA. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + destruct more; vm_compute; reflexivity.
    + assert (RF : region_ok segs E (mrestrict (w_H W) mem) gn_frA).
      { unfold region_ok, gn_frA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; replace (F + o) with (F + o) by lia; apply HFw; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ F 32 8 (SLit 6129888) 6129888); [reflexivity | lia | lia | exact HF32]. }
      destruct more; [|constructor; [exact RF | constructor]].
      destruct (Hmore eq_refl) as (Hv & _).
      constructor; [exact RF|]. constructor; [|constructor].
      unfold region_ok, gn_inA. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U28. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val segs E _ tv 0 1 (SOff 32 0) idv);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | rewrite Z.add_0_r; exact Hv].
    + apply pairwise_disjoint_of_extents. destruct more; unfold gn_regA, gn_frA, gn_inA, extent_of_region;
        cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U9, ?U28;
        cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd]; repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [gn_factsA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U26, U28, U32. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold SB. repeat match goal with |- _ /\ _ => split end; lia.
  - destruct more; unfold sh_ok, gn_SHA; [|constructor].
    destruct (Hmore eq_refl) as (_ & p & n & Hin & Hp1 & Hp2).
    constructor; [|constructor].
    apply (gn_shent_in_block ly S W mem md E gn_Bx 28 tv p n 0 1 HAR Hin); try lia.
    + unfold gn_Bx, U. cbn [sv_denot]. rewrite U26, Z.add_0_r, unsigned_lit_small by (unfold SB; lia). reflexivity.
    + unfold U. cbn [sv_denot]. rewrite U28, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
Qed.


Ltac kept KR := apply KR; repeat (first [left; reflexivity | right]).


Ltac gn_tools := 
  pose (RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 []);
  pose (RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 []);
  pose (BR := paj_branch (PI := PB_fr));
  pose (RUNP := SRr_run_pi_AJX0 B LAWS G_fr);
  pose (RUNTOP := SRr_run_to_pi_AJX0 (PL := PL_fr) (PI := PB_fr) B LAWS G_fr);
  pose (RUNC := SRr_run_pi_AJX0_call B LAWS G_fr).


(* ------------------------------------------------------------------ the arm's own cut points *)
Definition AF_gn_join : Z := 0x2404.    (* 0x846f0: the id read (or not); the prefix's shadow is unpoisoned next *)
Definition AF_gn_l1 : Z := 0x244c.      (* 0x84738: reads[k] = g_s[k].open && relay_reads(&g_s[k]) *)
Definition AF_gn_i1 : Z := 0x24a4.      (* 0x84790: relay_source's search over g_src, inlined *)
Definition AF_gn_rig : Z := 0x2548.     (* 0x84834: relay_instance_gone(id) *)
(* the fake frame's shadow while prefix[48] is unpoisoned (0x846f0-0x84704) *)
Definition fake_shadow_open : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0; 0; 0; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].
(* aframe_at at full = true, with the fake frame's shadow sh *)
Definition gframe (cx : lfcx) (sh : list Z) (FF : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  awr W mem F (sp0 - F) /\
  sv8 W mem (F + 24) 0xa21e0 /\ sv8 W mem (F + 48) 0x5d8204 /\ sv8 W mem (F + 56) 0x5d820c /\
  sv8 W mem (F + 64) 0x5d81fc /\ sv8 W mem (F + 72) 0x5d81f0 /\ sv8 W mem (F + 80) FF /\ sv8 W mem (F + 88) FF /\
  sv8 W mem (F + 96) (SB + FF / 8) /\ sv8 W mem (F + 184) FF /\
  sv8 W mem (F + 32) (rg_s fr_RG) /\ sv8 W mem (F + 104) HI_G_NOUT /\
  sv8 W mem (F + 112) (SB + rg_s fr_RG / 8) /\ sv8 W mem (F + 120) HI_G_NSRC /\ sv8 W mem (F + 128) (rg_s fr_RG + 4) /\
  sv8 W mem (F + 136) DIV10 /\ sv8 W mem (F + 152) (SB + (rg_s fr_RG + 4) / 8) /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) 0x840b0 /\ awr W mem FF 128 /\
  garr8 segs (arm W mem) (SB + FF / 8) sh /\ awr W mem (SB + FF / 8) 16.
Lemma gframe_of_aframe : forall cx FF W mem, aframe_at cx true FF W mem -> gframe cx fake_shadow FF W mem.
Proof.
  intros cx FF W mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18).
  destruct (H12 eq_refl) as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
  repeat (split; [assumption|]). assumption.
Qed.
Lemma aframe_of_gframe : forall cx FF W mem, gframe cx fake_shadow FF W mem -> aframe_at cx true FF W mem.
Proof.
  intros cx FF W mem (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & A1 & A2 & A3 & A4 & A5 & A6 & A7 &
    H13 & H14 & H15 & H16 & H17 & H18).
  repeat (split; [assumption|]). split; [intros _; repeat (split; [assumption|]); assumption|].
  repeat (split; [assumption|]). assumption.
Qed.
(* the id byte and the cursor after it (fuzz_u8 on in.n = 0 gives 0 and consumes nothing) *)
Definition gn_more (cx : lfcx) (m : lmod) : bool := lm_k m + 1 <? c_n cx.
Definition gn_id (cx : lfcx) (m : lmod) : Z := if gn_more cx m then in_byte cx (lm_k m + 1) else 0.
Definition gn_kq (cx : lfcx) (m : lmod) : Z := if gn_more cx m then lm_k m + 2 else lm_k m + 1.
(* what every cut point inside the arm carries: the journal, the frame (fake shadow sh), the cursor slots, the input,
   the image views *)
Definition gcom (cx : lfcx) (kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (lf_F cx + 40) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem /\
  (* the fake frame's flag word (lcut's, _cut.v:347-350): its last 8 bytes hold its flag pointer, which the
     shutdown stores through; no step of this arm writes them *)
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos).
(* the operation's facts: op 5 decoded at lm_k, the stream empty at the dispatch *)
Definition gn_op (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  in_byte cx (lm_k m) mod 10 = 5 /\ lm_O m = [] /\ 0 <= t < OPS_MAX /\ 0 <= lm_k m < c_n cx.
(* the registers the arm keeps from the dispatch (lregs_common's) *)
Definition gn_kregs (cx : lfcx) (t : Z) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\
  getr regs 23 = w64 HI_G_NSRC /\ getr regs 24 = w64 (SB + FF / 8) /\ getr regs 25 = w64 HI_G_NOUT /\
  getr regs 26 = w64 SB /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t.
(* 0x846f0: s4 = &g_s[0], s5 = id; F+40 / F+144 hold the cursor *)
Definition GJN (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom cx (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m).


(* ================================================================== the rest of the arm's cut points *)
Definition AF_gn_c1 : Z := 0x255c.      (* 0x84848: the check_no_loss_read loop's head *)
Definition AF_gn_t0 : Z := 0x2578.      (* 0x84864: g_nsrc is read, the table-order loop entered or skipped *)
Definition AF_gn_t1 : Z := 0x2584.      (* 0x84870: the table-order loop's outer head (i) *)
Definition AF_gn_t2 : Z := 0x259c.      (* 0x84888: its inner head (k) *)
Definition AF_gn_tn : Z := 0x2650.      (* 0x8493c: the outer latch *)
Definition AF_gn_csd : Z := 0x2660.     (* 0x8494c: check_shape_done(at), then the re-poison and the latch *)

(* ================================================================== the arm's model notions *)
Definition gn_e0 : rentry := relay_remove_b_c.no_entry.
Definition gn_hj0 : hsrc * nat := relay_instance_gone_b_c.no_hj.
Definition gn_q0 : rentry * hsrc := (gn_e0, fst gn_hj0).
Definition gn_sv4 (W : world segs) (mem : word -> option byte) (a v : Z) : Prop :=
  val_mem segs (arm W mem) a 4 v.
(* relay_source(fd): the first entry of the table whose fd is fd (arelay_at makes the fds distinct) *)
Fixpoint gn_find (es : list rentry) (fd : Z) (i : nat) : option nat :=
  match es with
  | [] => None
  | e :: es' => if re_fd e =? fd then Some i else gn_find es' fd (S i)
  end.
Definition gn_src (m : lmod) (fd : Z) : option nat := gn_find (lm_es m) fd 0.
(* reads[k] = g_s[k].open && relay_reads(&g_s[k]) *)
Definition gn_reads (m : lmod) (k : nat) : Z :=
  match nth k (lm_hs m) None with
  | None => 0
  | Some h => match gn_src m (hs_fd h) with
              | None => 0
              | Some j => if re_eof (nth j (lm_es m) gn_e0) =? 0 then 1 else 0
              end
  end.
(* the prefix snprintf writes into the fake frame, as check_shape_ends and relay_instance_gone read it *)
Definition gn_pre (cx : lfcx) (m : lmod) : list byte :=
  map (Z_to_bv 8) (relay_instance_gone_b_c.instance_prefix (gn_id cx m)).
(* a model slot replaced *)
Fixpoint gn_setn (k : nat) (x : option hsrc) (l : list (option hsrc)) : list (option hsrc) :=
  match k, l with
  | _, [] => []
  | O, _ :: l' => x :: l'
  | S k', y :: l' => y :: gn_setn k' x l'
  end.
Definition gn_set (m : lmod) (k : nat) (h : hsrc) : lmod :=
  LM (lm_k m) (gn_setn k (Some h) (lm_hs m)) (lm_G m) (lm_es m) (lm_c m) (lm_O m) (lm_mx m) (lm_cap m)
     (lm_out m) (lm_gn m) (lm_nfd m).
(* the harness source relay_instance_gone drains with the table entry e: the pure half of W_contract's
   dr_src_ok (its two memory clauses, asrc_at and aothers_at, the walk reads off amodel_at) *)
Definition gn_pair_ok (m : lmod) (e : rentry) (hj : hsrc * nat) : Prop :=
  (snd hj < 4)%nat /\ nth (snd hj) (lm_hs m) None = Some (fst hj) /\
  hs_fd (fst hj) = re_fd e /\ re_skip e = hs_overlong (fst hj) /\
  (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W (fst hj))) /\
  Z.of_nat (length (pending_stream (fst hj))) < 2 ^ 26 /\ hl_cap (hs_expected (fst hj)) < 2 ^ 26 /\
  re_nheld e + Z.of_nat (length (pending_stream (fst hj))) < 2 ^ 26.
Definition gn_pairs (m : lmod) (hs : list (hsrc * nat)) : Prop :=
  length hs = length (lm_es m) /\
  Forall (fun p => re_eof (fst p) = 0 -> gn_pair_ok m (fst p) (snd p)) (combine (lm_es m) hs) /\
  NoDup (rig_slots (combine (lm_es m) hs)).
(* the model after relay_instance_gone: the table is the first halves of rig_post's qs, the stream is its
   (c2, O2, cap2, out2), and every slot it drained holds the source rig_post gives for that entry *)
Definition gn_after_rig (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc))
    (c2 : ctl) (O2 : list byte) (cap2 out2 : Z) (m1 : lmod) : Prop :=
  lm_k m1 = gn_kq cx m /\ lm_G m1 = lm_G m /\ lm_es m1 = map fst qs /\
  lm_c m1 = c2 /\ lm_O m1 = O2 /\ lm_mx m1 = lm_mx m /\ lm_cap m1 = cap2 /\ lm_out m1 = out2 /\
  lm_gn m1 = lm_gn m /\ lm_nfd m1 = lm_nfd m /\ length (lm_hs m1) = 4%nat /\
  (forall j, (j < 4)%nat -> ~ In j (rig_slots (combine (lm_es m) hs)) ->
     nth j (lm_hs m1) None = nth j (lm_hs m) None) /\
  (forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
     nth (snd (nth i hs gn_hj0)) (lm_hs m1) None = Some (snd (nth i qs gn_q0))).
(* What relay_instance_gone's post says of the new table qs beyond where each drained source landed:
   rig_post's functional relation (W_contract.v rig_rel, which states dr_rel of each drained entry and
   entry_keys / geik of every entry), its length, and the model clauses of aentry_ok (W_rep.v:120-135) that
   rig_post's arelay_at gives of every entry of map fst qs, with the table's distinct fds.  Without it
   gn_after_rig leaves qs FREE, and GN_RI_read / GN_RI_step / GN_RI_end are false against every RINV
   (ATopKeeper, commit 382a1a20fb6, lib/A/ReplyRINV.v:540-579). *)
Definition gn_entry_model (e : rentry) : Prop :=
  (re_eof e = 0 \/ re_eof e = 1) /\ (re_skip e = 0 \/ re_skip e = 1) /\
  length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ 0 <= re_fd e < 2 ^ 31 /\
  re_nheld e < 2 ^ 26 /\ NoDup (map gestures_end_b_c.key_text (re_keys e)).
Definition gn_rig_ok (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc))
    (c2 : ctl) (O2 : list byte) (cap2 : Z) : Prop :=
  rig_rel (relay_instance_gone_b_c.instance_prefix (gn_id cx m)) (lm_mx m) (lm_c m) (lm_O m) (lm_cap m)
    (combine (lm_es m) hs) qs c2 O2 cap2 /\
  length qs = length (lm_es m) /\
  Forall gn_entry_model (map fst qs) /\ NoDup (map re_fd (map fst qs)).
(* check_no_loss's functional half, as cnl_post leaves the source; the last two conjuncts are cnl_post's last two (the
   held list's capacity never shrinks, and its EXACT capacity law, W_contract.v:2037-2041) *)
Definition gn_cnl_ok (h h' : hsrc) (E' H' : hlist) : Prop :=
  h' = set_exp_held h E' H' /\
  hl_recs E' = [] /\ hl_v E' = hl_v (hs_expected h) /\ hl_cap E' = hl_cap (hs_expected h) /\
  NoDup (texts H') /\ texts H' = RelayModel.upds (texts (hs_held h)) (texts (hs_expected h)) /\
  hl_cap H' <= Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) /\
  hl_cap (hs_held h) <= hl_cap H' /\
  hl_cap H' = cnl_cap (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)).
(* check_shape_ends's functional half, as cshe_post leaves the source *)
Definition gn_cshe_ok (P : list byte) (gone A0 : Z) (ob : list byte) (h h' : hsrc)
    (ds : list (Z * list byte)) (c : Z) : Prop :=
  exists H' : hlist,
  h' = set_held h H' /\ hl_v H' = hl_v (hs_held h) /\ hl_cap H' = hl_cap (hs_held h) /\
  NoDup (texts H') /\ 0 <= c /\
  ((gone <> 0 /\
    hl_recs H' = filter (fun r => negb (prefixb P (snd r))) (hl_recs (hs_held h)) /\
    ds = filter (fun r => prefixb P (snd r)) (hl_recs (hs_held h)) /\ c = 0) \/
   (gone = 0 /\
    ends_run P (hl_recs (hs_held h)) (skipn (Z.to_nat A0) ob) (want_of P (hl_recs (hs_held h)))
      = Some (hl_recs H', ds, c))).
(* where check_no_loss leaves `at` *)
Definition gn_at1 (gone A : Z) (h : hsrc) : Z :=
  if gone =? 0 then A + Z.of_nat (length (bstream (hs_expected h))) else A.
(* The table-order loop of fuzz_reply.c:647-653 as a relation over the model: from the state just after
   relay_instance_gone (m1, at = 0, i = k = 0), each step either passes slot k (closed, or its fd is not
   entry i's) or runs check_no_loss and check_shape_ends on it.  P is the prefix. *)
Inductive gn_run (P : list byte) (m1 : lmod) : lmod -> Z -> nat -> nat -> Prop :=
| gn_run0 : gn_run P m1 m1 0 0%nat 0%nat
| gn_run_skip : forall mc A i k, gn_run P m1 mc A i k -> (k < 4)%nat ->
    (nth k (lm_hs mc) None = None \/
     (forall h, nth k (lm_hs mc) None = Some h -> hs_fd h <> re_fd (nth i (lm_es m1) gn_e0))) ->
    gn_run P m1 mc A i (S k)
| gn_run_call : forall mc A i k h h' h'' E' H' ds c,
    gn_run P m1 mc A i k -> (k < 4)%nat -> (i < length (lm_es m1))%nat ->
    nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
    gn_cnl_ok h h' E' H' ->
    gn_cshe_ok P (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h' h'' ds c ->
    gn_run P m1 (gn_set mc k h'') (gn_at1 (lm_gn m1) A h + c) i (S k)
| gn_run_next : forall mc A i, gn_run P m1 mc A i 4%nat -> gn_run P m1 mc A (S i) 0%nat.
(* KF-COUNT (fuzz_reply's secondary-allocation count, meter MT): gn_run with the meter cost of its calls.  Each
   gn_run_call runs check_no_loss on the slot's source h (its post: mo_le .. (cnl_cost MT (hs_expected h) (hs_held h)),
   W_contract.v cnl_post) and then check_shape_ends on the source h' check_no_loss left (its post: mo_le ..
   (cshe_cost MT (hs_held h')), W_contract.v cshe_post); a skip and the latch call nothing.  q is the sum.  The
   relation is gn_run's constructor for constructor (gn_runc_run), so a fact about gn_run holds of gn_runc's run. *)
Inductive gn_runc (P : list byte) (m1 : lmod) : lmod -> Z -> nat -> nat -> Z -> Prop :=
| gn_runc0 : gn_runc P m1 m1 0 0%nat 0%nat 0
| gn_runc_skip : forall mc A i k q, gn_runc P m1 mc A i k q -> (k < 4)%nat ->
    (nth k (lm_hs mc) None = None \/
     (forall h, nth k (lm_hs mc) None = Some h -> hs_fd h <> re_fd (nth i (lm_es m1) gn_e0))) ->
    gn_runc P m1 mc A i (S k) q
| gn_runc_call : forall mc A i k q h h' h'' E' H' ds c,
    gn_runc P m1 mc A i k q -> (k < 4)%nat -> (i < length (lm_es m1))%nat ->
    nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
    gn_cnl_ok h h' E' H' ->
    gn_cshe_ok P (lm_gn m1) (gn_at1 (lm_gn m1) A h) (lm_O mc) h' h'' ds c ->
    gn_runc P m1 (gn_set mc k h'') (gn_at1 (lm_gn m1) A h + c) i (S k)
      (q + cnl_cost MT (hs_expected h) (hs_held h) + cshe_cost MT (hs_held h'))
| gn_runc_next : forall mc A i q, gn_runc P m1 mc A i 4%nat q -> gn_runc P m1 mc A (S i) 0%nat q.
Lemma gn_runc_run : forall P m1 mc A i k q, gn_runc P m1 mc A i k q -> gn_run P m1 mc A i k.
Proof.
  intros P m1 mc A i k q H. induction H.
  - exact (gn_run0 P m1).
  - exact (gn_run_skip P m1 mc A i k IHgn_runc H0 H1).
  - exact (gn_run_call P m1 mc A i k h h' h'' E' H' ds c IHgn_runc H0 H1 H2 H3 H4 H5).
  - exact (gn_run_next P m1 mc A i IHgn_runc).
Qed.
(* relay_instance_gone's meter cost, at a pairing hs it drained by (its post: mo_le .. (tr_cost MT (rig_tr ..)),
   W_contract.v rig_post).  hs is gdone's: the one gn_after_rig relates to m1. *)
Definition gn_rigc (cx : lfcx) (m m1 : lmod) (r : Z) : Prop :=
  exists hs qs c2 O2 cap2 out2,
    gn_pairs m hs /\ gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 /\
    r = tr_cost MT (rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m) (gn_id cx m) (lm_es m) hs).
(* the arm's meter cost from the operation's LS state: relay_instance_gone's, plus q for the table-order loop's
   calls so far (check_no_loss_read and check_shape_done are leaf calls: aleaf_post keeps the allocator state) *)
Definition gn_cst (cx : lfcx) (m m1 : lmod) (q cst : Z) : Prop := exists r, gn_rigc cx m m1 r /\ cst <= r + q.

(* ================================================================== what the other lanes owe *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* relay_instance_gone, W6: W_contract.v's rig_spec, with its placement premise rg_place, verbatim.
   snprintf: W_sites.v's asnprintf_realizes at the interceptor's entry, with aguard_ok at the image's two
   stack-protector cells.
   W3's four checks are W_contract.v's own texts on the W8 lane head (a3c72093c22): cnl_spec (:1968),
   cshe_spec (:1812), cnlr_spec (:454) and csd_spec (:130).  lf_arm_gone takes each as a Section hypothesis
   (W_LLVMFuzzerTestOneInput_gone.v); this file restates none of them. *)
(* The G each of the two calls is taken at: the 32 bytes of slot j's two lists (expected at +64, held at
   +80), which is exactly what the spec's own premise `forall a, HA + 64 <= a < HA + 96 -> inG G a` asks.
   NOT [(g_s, 384)]: a journal at G lets the callee change any byte of G (gagree, W_journal.v:214), so a
   G covering all four slots would lose the other three slots' amodel_at at every call.  W3's theorems are
   G-generic, and GN_HG_sub G_fr (gn_Gs j) follows from GN_HGs.  (p5's reading, 2026-10-29.) *)
Definition gn_Gs (j : nat) : list (Z * Z) := [(rg_s fr_RG + ASRC * Z.of_nat j + 64, 32)].

(* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr ---- *)
Definition GN_HGs : Prop := forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Definition GN_HG_RIG : Prop := forall a, inG (G_RIG B fr_RG) a -> inG G_fr a.
Definition GN_HG_sub (G : list (Z * Z)) : Prop := forall a, inG G a -> inG G_fr a.
(* Every cell amodel_at names, as one G-coverage fact.  A callee's journal keeps an image byte only when
   it is not an allocator static (the image clause, Reusable/YCbq.v:363), and the walk knows that of a
   byte only through G_fr (gx_ok's second half); HG alone covers g_s and the callees' own G, not the rest
   of the model's cells.  With glob_wr_law it also gives their writability after a call.  Discharged at
   G_fr_c by rng_cover: G_fr_obj holds all 20 program objects (lib/A/W_LLVMFuzzerTestOneInput_G.v's
   c_HGcells).  (p5's reading, 2026-10-29.) *)
Definition gn_cells : list (Z * Z) :=
  [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
   (rg_out fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_send_max fr_RG, 8);
   (rg_send_eintr fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_client fr_RG, 4);
   (rg_client_broken fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4);
   (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Definition GN_HGcells : Prop := forall a, inG gn_cells a -> inG G_fr a.
(* errno is none of the model's cells.  G_fr holds both errno and those cells, so gx_ok cannot separate
   them, and B is a Variable here.  check_shape_ends' cshe_home premise asks it of g_s's bytes, and the
   relay_instance_gone call asks it of four cells.  An errno hypothesis: proved for the concrete instance
   (as_errno B = 0x5d93cc) as lib/A/W_LLVMFuzzerTestOneInput_G.v's c_CELLS_ERRNO.  (p5 / p3, 2026-10-29.) *)
Definition GN_CELLS_ERRNO : Prop := forall a, inG gn_cells a -> ~ (as_errno B <= a < as_errno B + 4).
(* The read-only bytes the allocator owns are pinned in every AR state (W_journal.v:373-381): what
   ajournal_gx_rom_view's rom_out side needs to carry the cut's rom_view across a call.  This is the
   second half of W3's ROMNS; it is an instance fact, not derivable in the piece.  (p5, 2026-10-29.) *)
Definition GN_ROM_PIN : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* g_s lies in the instance's zero-shadow ranges (a global of the image) *)
Definition GN_HZS : Prop := azs B (rg_s fr_RG) (4 * ASRC).
(* the image objects this arm reads are apart; vm_compute at PB_fr *)
Definition GN_HAP : Prop :=
  (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 0) \/ VAL (A_OBJ 0) + 8 <= rg_s fr_RG) /\
  (rg_s fr_RG + 4 * ASRC <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= rg_s fr_RG).
(* errno's place (the shape of W_LLVMFuzzerTestOneInput_latch.v's ERRNO_LOW) *)
Definition GN_ERRNO_LOW : Prop := 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling + 8.
(* NO GN_GUARD HERE, on purpose.  snprintf's interceptor reads two stack-protector cells, the GOT word
   FR_GOT_GUARD = 0x9e658 and __stack_chk_guard FR_GUARD = 0x5f94b0 (W_sites.v:271,299-300), and two
   texts for them were tried and MEASURED FALSE at the pin on 2026-10-29:
     (1) `rom_view segs W mem -> aguard_ok W mem FR_GOT_GUARD FR_GUARD` is false - vm_compute over
         pa_segs at PB_fr gives inrom(0x9e658) = false and inrom(0x5f94b0) = false (both cells lie in
         writable segments), so rom_view constrains neither, and a memory with no byte at 0x9e658
         satisfies rom_view and fails aguard_ok;
     (2) the same fact at the function's ENTRY state, carried to the call by the journal, is useless:
         0x9e658 is one of the instance's owned statics (AF0m Tfib_owned_static), and the journal's
         image clause keeps a byte only when it is NOT an owned static, so nothing transports it.
   What is true at the pin is that the GOT word is a PINNED CONST CELL of the instance (AF0m
   Tfib_const_abs holds `z8 (ANum 0x9e658) 0x5f94b0`), readable at every AR state through am_const, and
   that the canary cell needs no hypothesis at all (seg_rom at [0x5f94b0, +8) is Some 0, so its aview is
   Some in every memory).  The snprintf phase (lib/A/W_LLVMFuzzerTestOneInput_gone_p1.v) states that as
   its own GN_GOT_PIN; it is the only phase with an interceptor call. *)

(* ---- the arm's model obligations (pure, over lmod and the plain records) ---- *)
(* every entry of the table the relay still reads is one of the four harness sources (the plain proof's
   pair_ok), and the pairing is injective on the slots relay_instance_gone drains *)
Definition GN_RI_pairs : Prop := forall cx t m, RINV cx t m -> exists hs, gn_pairs m hs.
(* the open sources have distinct fds (so aothers_at holds of the other three slots) *)
Definition GN_RI_fds : Prop := forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
(* every entry of the table has the two 4-byte paddings and an fd in range (aentry_ok, in model form) *)
Definition GN_RI_pads : Prop := forall cx t m, RINV cx t m ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (lm_es m) /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) (lm_es m).
(* check_no_loss_read's premise at every slot the arm calls it on: relay_instance_gone drained that slot,
   so its pending list is empty (the functional half of W_contract's dr_rel, in model form) *)
Definition GN_RI_read : Prop := forall cx t m hs qs c2 O2 cap2 out2 m1 k h,
  RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  (k < 4)%nat -> gn_reads m k = 1 -> nth k (lm_hs m1) None = Some h ->
  hl_recs (hs_pending h) = [] /\ hs_off h = 0.
(* what check_no_loss and check_shape_ends take of the state the table-order loop calls them in.  Sx / lyx are the
   loop's state; the premise after mo_le is the callee posts' block relation, composed from relay_instance_gone's
   rig_post (W_contract.v:1436-1441) through every check_no_loss / check_shape_ends post (:1978-1979, :1823): the
   live blocks are the input's, the model's and the same rest as at the operation's LS state (LS_rm_step's shape).
   Without it Sx is free at MT := ameter_triv and cnl_room's blocks_bytes bound is false.
   KF-COUNT: cst is no longer free.  The loop's state is reached from the LS state at most at relay_instance_gone's
   cost plus the loop calls' costs so far (gn_runc's q, gn_cst), and check_no_loss's post is taken at its own cost,
   so the meter conjuncts are bounded at a counting meter (MT_sec), not only at ameter_triv. *)
Definition GN_RI_step : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A i k h (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A i k -> gn_runc (gn_pre cx m) m1 mc A i k q ->
  mo_le MT S Sx cst -> gn_cst cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  NoDup (texts (hs_held h)) /\
  hl_n (hs_expected h) < 2 ^ 26 /\
  hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h))) < 2 ^ 22 /\
  0 <= A <= Z.of_nat (length (lm_O mc)) /\
  (* the stream's length fits next_line's memchr bound (both check_* specs ask NO <= 2 ^ 40 and
     0 < NO -> NO < 2 ^ 32); one operation sends at most 33,488,385 bytes (W_contract.v:594-595).  The
     model's, like the size bounds above; aout_at alone bounds it only by the allocator's MALLOC_MAX.  (p5) *)
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * Z.max 8 (Z.max (hl_cap (hs_held h))
    (2 * (hl_n (hs_held h) + Z.of_nat (count_begin (texts (hs_expected h)))))) < 2 ^ 32 /\
  cnl_room MMAX (blocks_bytes Sx) (texts (hs_held h)) (hl_cap (hs_held h)) (hl_recs (hs_expected h)) /\
  mo_ok MT Sx (cnl_cost MT (hs_expected h) (hs_held h)) /\
  (forall h' E' H' (Sy : astate), gn_cnl_ok h h' E' H' ->
     mo_le MT Sx Sy (cnl_cost MT (hs_expected h) (hs_held h)) ->
     hl_n (hs_held h') < 2 ^ 26 /\
     gn_at1 (lm_gn m1) A h <= Z.of_nat (length (lm_O mc)) /\
     (lm_gn m1 = 0 -> ends_run (gn_pre cx m) (hl_recs (hs_held h'))
        (skipn (Z.to_nat (gn_at1 (lm_gn m1) A h)) (lm_O mc))
        (want_of (gn_pre cx m) (hl_recs (hs_held h'))) <> None) /\
     mo_ok MT Sy (hl_n (hs_held h') * mo_free MT)).
(* the loop ran to its end: `at` is g_nout, which is what check_shape_done asks, and the relational
   invariant and the allocator-state invariant hold of the model after the operation.  The block relation
   premise is GN_RI_step's: without it lyx / Sx are free and LS's ablocks clause is false.  KF-COUNT: cst is bounded
   as in GN_RI_step (the whole loop's q). *)
Definition GN_RI_end : Prop :=
  forall cx t m ly S hs qs c2 O2 cap2 out2 m1 mc A (lyx : alayout) (Sx : astate) cst q,
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  (lm_gn m = 0 \/ lm_gn m = 1) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  LS cx t m ly S -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  gn_run (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat -> gn_runc (gn_pre cx m) m1 mc A (length (lm_es m1)) 0%nat q ->
  mo_le MT S Sx cst -> gn_cst cx m m1 q cst ->
  (forall rest, Permutation (ablocks B ly S) (input_blks cx ++ model_blks m ++ rest) ->
     Permutation (ablocks B lyx Sx) (input_blks cx ++ model_blks mc ++ rest)) ->
  A = Z.of_nat (length (lm_O mc)) /\ RINV cx (t + 1) mc /\ LS cx (t + 1) mc lyx Sx.
(* relay_instance_gone's budget, read off LS: rig_spec's three room premises (the room round's C3 peak form; the sum
   form and the g_capout premises are gone from rig_spec).  The text is s5-r1d's adopted TX_GN_LS_rig token for token
   (commit 1318828167d, lib/A/ReplyLS3Peak.v:171, with LS for LSx), so top_x plugs it by exact:
   - gn_op is this file's (:358), whose body ReplyLS3cTopxGoneF.gn_op copies (same commit, ReplyLS3cTopxGoneF.v:65);
   - the g_capout clause is ReplyLS3eCap.ent_capout_ok0 (same commit, ReplyLS3eCap.v:134) at the entry's world and
     memory, written out: that file Requires the AR arms, which this one must not.  It is the cut's CAPOUT clause
     (_cut.v:212-213), the last conjunct of the entry's pre;
   - the last two conclusions are the request bound of the table and the send room the plain rows prove too.
   The walk holds every premise at GRG: gn_op and gn_pairs, aentry_ok's |re_U| <= APARTIAL, the model blocks' sizes
   not negative (the AR block law), every open source's pending offset (asrc_at W_rep.v:104-105), and the pre's
   CAPOUT clause (lf_base) *)
Definition GN_LS_rig : Prop := forall cx t m ly S hs,
  LS cx t m ly S -> RINV cx t m -> gn_pairs m hs ->
  gn_op cx t m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL) (lm_es m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  (forall j h, nth j (lm_hs m) None = Some h ->
     (hl_recs (hs_pending h) = [] /\ hs_off h = 0) \/
     (exists r rs, hl_recs (hs_pending h) = r :: rs /\ 0 <= hs_off h < Z.of_nat (length (snd r)))) ->
  (exists c, val_mem segs (arm (c_W cx) (c_mem cx)) (rg_capout fr_RG) 8 c /\ 0 <= c <= CAPOUT_MAX) ->
  let tr := rig_tr (lm_c m) (lm_mx m) (Z.of_nat (length (lm_O m))) (lm_cap m)
              (gn_id cx m) (lm_es m) hs in
  tr_max tr < MMAX /\ blocks_bytes S + tr_peak tr <= LIVE_MAX /\ mo_ok MT S (tr_cost MT tr) /\
  lm_cap m < MMAX /\
  blocks_bytes S + tr_peak tr + 4 * Z.max (lm_cap m) (tr_max tr) <= LIVE_MAX.
(* ---- the count rules (the room round).  Each callee call asks `cnt_ok_pk RP pk (ablocks B ly S)` at its own state;
   the LS state's count bound is LS_cnt's, at the arm's peak gn_pk (a Theorem Labs lane's pk_gone, commit ba8e99b5bd2,
   lib/A/ReplyLScnt.v:476, at the instance).  The walk's block relation (gn_tie) makes a call's live blocks the input,
   the model's blocks at the call and the LS state's rest, so what a call needs beyond LS_cnt is a fact of the MODEL
   alone: the model's count at the call plus the callee's premise peak stays under the LS state's model count plus
   gn_pk, for every count predicate P.  Pure model rules, no astate. *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
(* the two callee premise peaks the arm meets, as functions of what the call is made at: relay_instance_gone's
   (W_contract_x.v rig_pk at its rig_tr) and check_no_loss's (cnl_pk of the slot's two lists).  They are PARAMETERS
   here, not W_contract_x's names: this file is AR-side and must not Require the _x kit (that kit's global zify flag
   reaches every file that Requires it, and breaks lia in the AR phases).  The _x arm passes W_contract_x's names;
   check_shape_ends' peak is the constant 0 (cshe_pk, W_contract_x.v:279), written out *)
Variable gn_rig_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Variable gn_cnl_pk : hsrc -> (Z -> bool) -> nat.
(* relay_instance_gone is called at the LS state itself (GRG holds LS at the call's state), so its premise peak
   must fit inside the arm's peak *)
Definition GN_CNT_rig : Prop := forall cx m hs (P : Z -> bool),
  (gn_rig_pk cx m hs P <= gn_pk cx m hs P)%nat.
(* check_no_loss on slot k of the table-order loop, at the loop model mc that relay_instance_gone and the earlier
   check_no_loss / check_shape_ends calls left; then check_shape_ends on the source check_no_loss left.  The premises
   are GN_RI_step's (the walk holds them at both calls), the model blocks' sizes not negative, and the representation
   clause of the table relay_instance_gone leaves (rig_post_x's arelay_at .. (map fst qs), W_contract_x.v:960 ->
   aentry_ok W_rep.v:131-132) *)
Definition GN_CNT_step : Prop :=
  forall cx t m hs qs c2 O2 cap2 out2 m1 mc A i k h (P : Z -> bool),
  RINV cx t m -> gn_op cx t m ->
  Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
    Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
      14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) ->
  0 <= lm_cap m ->
  Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
    ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) ->
  Forall (fun o => match o with
    | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                  (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                 Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
    | None => True end) (lm_hs m) ->
  (forall b, In b (model_blks m) -> 0 <= snd b) ->
  gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 -> gn_rig_ok cx m hs qs c2 O2 cap2 ->
  Forall (fun e => (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))
    (map fst qs) ->
  gn_run (gn_pre cx m) m1 mc A i k ->
  (i < length (lm_es m1))%nat -> (k < 4)%nat ->
  nth k (lm_hs mc) None = Some h -> hs_fd h = re_fd (nth i (lm_es m1) gn_e0) ->
  (forall j hj, nth j (lm_hs mc) None = Some hj -> hl_n (hs_held hj) <= hl_cap (hs_held hj)) ->
  (ReplyCnt.acnt P (model_blks mc) + gn_cnl_pk h P
     <= ReplyCnt.acnt P (model_blks m) + gn_pk cx m hs P)%nat /\
  (forall h' E' H', gn_cnl_ok h h' E' H' ->
     (ReplyCnt.acnt P (model_blks (gn_set mc k h')) + 0
        <= ReplyCnt.acnt P (model_blks m) + gn_pk cx m hs P)%nat).

(* ================================================================== the arm's own states *)
(* what every state of the arm after the join carries: the journal, the frame (with the fake frame's shadow
   sh), the cursor slots, the input, the image views, the model and its blocks *)
Definition gst (cx : lfcx) (kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom cx kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S.
(* the prefix snprintf left in the fake frame, as check_shape_ends reads it *)
Definition gn_prefix_at (cx : lfcx) (m : lmod) (W : world segs) (mem : word -> option byte) (FF : Z) : Prop :=
  (forall i, 0 <= i < Z.of_nat (length (gn_pre cx m)) ->
     aview segs (w_H W) mem (FF + 32 + i)
       = Some (bv_unsigned (nth (Z.to_nat i) (gn_pre cx m) (Z_to_bv 8 0)))) /\
  aview segs (w_H W) mem (FF + 32 + Z.of_nat (length (gn_pre cx m))) = Some 0 /\
  (forall a, FF + 32 <= a < FF + 80 -> aview segs (w_H W) mem a <> None) /\
  ~ In (Z_to_bv 8 0) (gn_pre cx m) /\ Z.of_nat (length (gn_pre cx m)) + 9 <= 48.
(* 0x84738: the reads[] loop's head, q of the four slots done; a2 = q, t0 = 4, t1 = F + 192,
   s4 = &g_s[0], s5 = id; prefix[48] is unpoisoned and holds the prefix; at = 0 *)
Definition GL1 (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 12 = w64 (Z.of_nat q) /\ getr regs 5 = w64 4 /\ getr regs 6 = w64 (lf_F cx + 192) /\
    (* q = 4 is not a state of 0x84738: the latch 0x847fc leaves the loop for 0x84834 at k + 1 = 4, and
       the head would read &g_s[4].open, whose granule is g_s's redzone - poison, so `azs` is FALSE
       there and the instrumented check could not be decided (p2's reading, 2026-10-29) *)
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84834: the four reads[] are written; relay_instance_gone(id) is next (s5 = id) *)
Definition GRG (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst cx (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (rg_s fr_RG) /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* what relay_instance_gone has fixed about the model, carried by every state after it.  The last four conjuncts are
   facts of amodel_at at the table and sources BEFORE the call (GRG's gst at m), which GN_RI_step / GN_RI_end take:
   aentry_ok's unfinished-line and key clauses (W_rep.v:125, :136-139; relay_instance_gone ends the keys with the
   prefix, so the table after it no longer holds them), aout_at's capacity clause (W_rep.v:187-188), aentry_ok's
   representation clauses (W_rep.v:124-125, :131-132), and asrc_at's pending-offset clause (W_rep.v:104-105) with
   alist_at's non-empty pending records (W_rep.v:91), the model blocks' sizes not negative (the AR block law over
   ablocks_sep's Permutation; GN_LS_rig / GN_CNT_step / LS_cnt take it), ReplyCnt.msz_ok of the table and sources
   (LS_cnt's guard, gn_msz_ok below), and the representation clause of the table relay_instance_gone LEAVES
   (GN_CNT_step's C2 premise, from rig_post's arelay_at .. (map fst qs), aentry_ok W_rep.v:131-132) *)
Definition gdone (cx : lfcx) (t : Z) (m m1 : lmod) : Prop :=
  exists hs qs c2 O2 cap2 out2,
    gn_pairs m hs /\ gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 /\ gn_rig_ok cx m hs qs c2 O2 cap2 /\
    RINV cx t m /\ gn_op cx t m /\
    Forall (fun e => ~ In (Z_to_bv 8 0) (re_U e) /\
      Forall (fun k => ~ In (Z_to_bv 8 0) (gestures_end_b_c.key_text k) /\
        14 <= Z.of_nat (length (gestures_end_b_c.key_text k)) <= APARTIAL) (re_keys e)) (lm_es m) /\
    0 <= lm_cap m /\
    Forall (fun e => Z.of_nat (length (re_U e)) <= APARTIAL /\ (re_cap e = 0 \/ re_cap e = 8192 \/ re_cap e = 16384) /\
      ((re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))) (lm_es m) /\
    Forall (fun o => match o with
      | Some h0 => ((hl_recs (hs_pending h0) = [] /\ hs_off h0 = 0) \/
                    (exists r rs, hl_recs (hs_pending h0) = r :: rs /\ 0 <= hs_off h0 < Z.of_nat (length (snd r)))) /\
                   Forall (fun r => (1 <= length (snd r))%nat) (hl_recs (hs_pending h0))
      | None => True end) (lm_hs m) /\
    (forall b, In b (model_blks m) -> 0 <= snd b) /\
    ReplyCnt.msz_ok (lm_es m) (lm_hs m) /\
    Forall (fun e => (re_hp e = 0 /\ re_keys e = []) \/ (re_hp e <> 0 /\ 8 * re_nheld e <= re_kh e /\ 8 <= re_kh e))
      (map fst qs).
(* ReplyCnt.msz_ok of the table and sources an amodel_at holds: aentry_ok's capacity and key clauses (W_rep.v:129,
   :139) and the open sources' expected / held alist_at `lines = true` record clause (W_rep.v:89-90) *)
Lemma gn_msz_ok : forall ly S (W : world segs) mem m,
  amodel_at B ly S W mem m -> ReplyCnt.msz_ok (lm_es m) (lm_hs m).
Proof.
  intros ly S W mem m (HM4 & HSLOT & HREL & _). split.
  - pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HAE & _).
    rewrite Forall_forall in HAE |- *. intros e He.
    destruct (HAE e He) as (_ & _ & _ & _ & _ & C6 & _ & _ & _ & _ & _ & _ & _ & _ & HK).
    split; [destruct C6 as [C6 | [C6 | C6]]; rewrite C6; lia|].
    rewrite Forall_forall in HK |- *. intros k Hk. destruct (HK k Hk) as (_ & _ & _ & Hl). lia.
  - rewrite Forall_forall. intros o Ho. apply (In_nth (lm_hs m) o None) in Ho as (i & Hi & <-).
    pose proof (HSLOT i ltac:(lia)) as Hsl. unfold aslot in Hsl.
    destruct (nth i (lm_hs m) None) as [h0|]; [|exact I].
    destruct Hsl as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HEX & HHE & _).
    unfold ReplyCnt.texts_ok. split.
    + destruct HEX as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
      rewrite Forall_forall in HF |- *. intros r Hr. destruct (HF r Hr) as (_ & _ & Hl & _).
      exact (proj2 (Hl eq_refl)).
    + destruct HHE as (_ & _ & _ & _ & _ & _ & _ & _ & HF).
      rewrite Forall_forall in HF |- *. intros r Hr. destruct (HF r Hr) as (_ & _ & Hl & _).
      exact (proj2 (Hl eq_refl)).
Qed.
(* the block relation from the operation's LS state (ly0, S0) at model m to the arm's state (ly, S) at model mc: the
   LS state's live blocks are the input's, m's and some rest0, and every such rest carries over: the arm's live
   blocks are the input's, mc's and the same rest.  Its second half is GN_RI_step's / GN_RI_end's premise, written
   out there; the first half lets a caller count the arm's state against the LS state's (the count rules).
   Established after relay_instance_gone (p3, from rig_post's two Permutations over one rest) and carried through
   every check_no_loss / check_shape_ends post (p5, gp5_tie_step) *)
Definition gn_tie (cx : lfcx) (m : lmod) (ly0 : alayout) (S0 : astate) (mc : lmod) (ly : alayout) (S : astate)
    : Prop :=
  (exists rest0, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest0)) /\
  forall rest, Permutation (ablocks B ly0 S0) (input_blks cx ++ model_blks m ++ rest) ->
    Permutation (ablocks B ly S) (input_blks cx ++ model_blks mc ++ rest).
(* 0x84848: the check_no_loss_read loop's head, q slots done; s4 = F + 192 + 4q, s5 = &g_s[q], s6 = F + 208 *)
Definition GC1 (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LS cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    getr regs 20 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 21 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (* 0x84848 is a do-while head (the body runs, then `bne s4,s6`), so q = 4 is not a state of it:
       at q = 4 the test s4 = s6 would already have left the loop (p4's reading, 2026-10-29) *)
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84864: the check_no_loss_read loop is done; the table-order loop is entered or skipped *)
Definition GT0 (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst cx (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LS cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx t (frame_addr ly 1 fpos) regs /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x8494c: the table-order loop is done; at = g_nout, and the model after the operation is mc *)
Definition GCSD (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst cx (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LS cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\
    getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
    getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (frame_addr ly 1 fpos + 32) /\
    getr regs 23 = w64 HI_G_NSRC /\ getr regs 26 = w64 SB /\
    getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\ getr regs 27 = w64 t.
End g.
