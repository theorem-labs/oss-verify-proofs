(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: KF-COUNT F3: gn_runc, gn_cst, the GN_RI_* / GC1 / GT0 cost bound (A 6151e80) *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput on image B
   (fuzz_reply.asan-ubsan 0x849a0-0x849d0, 0x84a9c-0x84cb4, 0x84da4-0x84dac, 0x84e30-0x84e38; fuzz_reply.c:633-655 and
   :718-720), the image-B twin of lib/A/W_LLVMFuzzerTestOneInput_gone_base.v (a working branch
   32b23a20c3e), over the cut invariants of lib/B/W_LLVMFuzzerTestOneInput_cut.v (a working branch
   9409d4da51f, merged with a working branch 990666444ab).  Every address, register, frame slot and object below is
   read from B's own objdump (of the pinned binary fuzz_reply.asan-ubsan, the pinned image
   sha256 10ffb5f9202ae2bd...), guided by the old-stack B walk's header (a working branch e29b582ba724,
   lib/B/Prog/SlotPass5.v:1-35), never by offset arithmetic from A.
   THE ARM'S BASE: the pieces every phase of the arm shares.  The phases are proved in
   W_LLVMFuzzerTestOneInput_gone_p<n>.v and composed into lf_arm_gone (= _cut's ARM_gone, :754) in
   W_LLVMFuzzerTestOneInput_gone.v:
     p0  INV_A 5 -> GJN     0x849a0 -> 0x84aa8  t to F+88; the id byte (or not); the cursor to F+16 / F+144
     p1  GJN -> GL1 0       0x84aa8 -> 0x84af8  Shadow(FF)+4..+9 := 0, at = 0 (F+208), snprintf (0x84ae0)
     p2  GL1 q -> GRG       0x84af8 -> 0x84b40  reads[q] = g_s[q].open ? relay_reads(&g_s[q]) (0x84b0c) : 0
     p3  GRG -> GC1 0       0x84b40 -> 0x84b5c  s10 to F+24; relay_instance_gone(id) (0x84b48)
     p4  GC1 q -> GT0       0x84b5c -> 0x84b78  check_no_loss_read(&g_s[q]) (0x84b68) for reads[q] != 0
     p5  GT0 -> GCSD        0x84b78 -> 0x84c84  the table-order loop: check_no_loss (0x84c14), check_shape_ends (0x84c24)
     p6  GCSD -> INV_K      0x84c84 -> 0x84804  check_shape_done(at) (0x84c88), Shadow(FF)+4..+9 := 0xf8, reloads
   B against A (each read from B's objdump):
   - B CALLS relay_reads (0x864e8) at 0x84b0c where A inlines relay_reads / relay_source: B's p2 is a loop with one call
     per open slot, cited through the cut's RRDS (:697).
   - B's registers: s1 = F, s2 = HI_G_SRC, s3 = FF + 32, s11 = SB are kept across the whole arm (gn_kregs); s9 = t is
     spilled to F+88 at 0x849a0 and reloaded at 0x84da4; s10 = HI_G_NOUT is spilled to F+24 at 0x84b40 and reloaded at
     0x84cb0; s8 = Shadow(FF) (SB + FF / 8) is reloaded from F+96 at 0x84c8c; s7 = 1 is re-made at 0x84da8; s4 = in.p is
     reloaded from F+16 at 0x84cac.  The cursor slots are F+16 (in.p) and F+144 (in.n) (A: F+40 / F+144).
   - Frame slots the arm writes: F+16, F+24, F+88, F+112 (p5's auipc spill 0x5d8b78, g_nsrc - 424), F+144,
     F+192 .. F+207 (reads[4]), F+208 (at); none is a slot of the cut's aframe_at.
   - UBSan trap edges (all to 0x850fc): 0x849ac `bgeu s7,a2` in p0; 0x84bd0 / 0x84be0 / 0x84be4 / 0x84bec in p5.
   - The callee texts: relay_reads is the cut's RRDS; snprintf W_sites.v:308 asnprintf_realizes; relay_instance_gone
     W_contract.v rig_spec / rg_place; check_no_loss_read and check_shape_done are WALKED INLINE in p4 / p6 (callee
     walked inline: the kit posts cnlr_spec / csd_spec are aleaf_post, which lacks the outside-frame-kept clause, so
     errno's view, which amodel_at's aout_at reads, is not carried; a Theorem Labs lane's ruling 14:1xZ); check_no_loss and
     check_shape_ends are the KIT's cnl_spec (W_contract.v Section w3n) and cshe_spec (Section w3e) at
     a working branch 990666444ab, cited per slot in GN_CNL / GN_CSHE below.  cnl_spec's last premise (the stack
     readable from sp up to ly_top) comes from the cut's STKR (gn_stkr below); cshe_spec's PF premise is taken by its
     fake-frame disjunct at 0x84c24. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YE01 YE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YCfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require ListRep RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_sites W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_LLVMFuzzerTestOneInput_cut.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) rule 3): every sink argument is passed with @ or from the Context *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
(* Required, not Imported: the live counts (ReplyCnt.acnt) the count rules GN_CNT_rig / GN_CNT_step name, cited by
   their qualified names.  W_contract_x is NOT Required here: the callees' peaks are parameters of those rules *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the program interface's stack budget and entry, from the generated lib/B/YCfn.v, as the cut names them *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.
Local Notation A_LLVMF := YCfn.A_LLVMF.

(* ------------------------------------------------------------------ the gx wrappers of W_frame.v's plain runs
   (A's base Sections px / pxc / pxr, at any placement of any listing): a run that writes the fake frame's shadow,
   which the token run's static check refuses, carried over W2's ajournal_gx at XO = 0, OUT = []. *)
Section px. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
  intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HGr].
  apply (ajournal_gx_pack pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') _ k memS H0 H1);
    [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
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
  apply (SRr_run_pi_AJ_call B LAWS W n E ss ss' s ms STK sp0 FP ly S W0 memS md own lyc Sc mdc k Q HE HS Hrun HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HGr].
  apply (ajournal_gx_pack pa_segs B G 0 [] STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') _ k memS H0 H1);
    [rewrite !Z.add_0_r; exact HJ' | exact Hag | intros a Ha; lia].
Qed.
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
  apply (SRr_run_pi_AJ B LAWS W n E ss ss' st ms STK sp0 FP ly S W0 memS md own lyc Sc mdc k Q HE HS Hrun Hst HJi Hwr).
  intros ms' mat' HS' HJ' HF HF' HGr. apply (Hk ms' mat' HS'); [|exact HF | exact HF' | exact HGr].
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

(* check_no_loss (CNL) and check_shape_ends (CSHE): the kit's texts, W_contract.v Section w3n cnl_spec and Section w3e
   cshe_spec (a working branch 990666444ab); no local copy (GN_CNL / GN_CSHE below cite them per slot). *)

Section g.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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

(* ------------------------------------------------------------------ the arm's numbers *)
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
  split; [exact Hal|]. split; [unfold YCfn.LLVMF_STK in *; lia|].
  split; [rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia; reflexivity|].
  split; [lia|]. split; [exact H4|]. split; [exact Hc|]. split; [exact Happ|]. split; [exact Hfrs|exact HAR].
Qed.

(* STKR: the caller's stack is readable from the entry's sp up to ly_top, the LAST conjunct of the cut's
   fr_lib_pre_cf (_cut.v:265); cnl_spec's last premise is built from it (p5b gp5_stk_rd). *)
Lemma gn_stkr : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  forall a, spZ (c_regs cx) <= a < ly_top (c_ly cx) -> aview segs (w_H (c_W cx)) (c_mem cx) a <> None.
Proof.
  intros cx (_ & HPRE). unfold fr_lib_pre_cf in HPRE.
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTKR & _). exact HSTKR.
Qed.

(* a shadow entry inside a live block (A's base, verbatim) *)
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

(* A callee's afn_pre at sp = F (the cut's frame), from the cut's journal and the saved registers the prologue
   stored: B's latch twin lt_afn_pre_at (a working branch ee519e5e2f5,
   lib/B/W_LLVMFuzzerTestOneInput_latch.v:625-698), with the saved-register clause of aframe_at in place of the whole
   frame, so that every call of the arm (relay_reads, relay_instance_gone, check_no_loss, check_shape_ends) names one
   lemma. *)
Lemma gn_afn_pre : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia | lia | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.

Ltac kept KR := apply KR; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ the arm's own cut points (offsets from fr_B0
   0x82344, B's objdump) *)
Definition AF_gn_join : Z := 0x2764.    (* 0x84aa8: the id read (or not); the prefix's shadow is unpoisoned next *)
Definition AF_gn_l1 : Z := 0x27b4.      (* 0x84af8: the reads[] loop's head (lb a0,0(s9)) *)
Definition AF_gn_rr : Z := 0x27c8.      (* 0x84b0c: jal relay_reads *)
Definition AF_gn_rig : Z := 0x27fc.     (* 0x84b40: sd s10,24(s1); relay_instance_gone(id) *)
Definition AF_gn_c1 : Z := 0x2818.      (* 0x84b5c: the check_no_loss_read loop's head (lw a0,0(s5)) *)
Definition AF_gn_t0 : Z := 0x2834.      (* 0x84b78: g_nsrc is read, the table-order loop entered or skipped *)
Definition AF_gn_t1 : Z := 0x2848.      (* 0x84b8c: the table-order loop's outer head (i = s7) *)
Definition AF_gn_t2 : Z := 0x286c.      (* 0x84bb0: its inner head (k: s6 = 4 - k) *)
Definition AF_gn_tn : Z := 0x2930.      (* 0x84c74: the outer latch (g_nsrc re-read) *)
Definition AF_gn_csd : Z := 0x2940.     (* 0x84c84: check_shape_done(at), then the re-poison and the latch *)
(* the fake frame's shadow while prefix[48] is unpoisoned (0x84aa8-0x84abc, re-poisoned at 0x84c94-0x84ca8) *)
Definition fake_shadow_open : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0; 0; 0; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3; 0xf3].
(* the cut's aframe_at, with the fake frame's shadow sh as a parameter (B's aframe_at has no `full` flag) *)
Definition gframe (cx : lfcx) (sh : list Z) (FF : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  awr W mem F (sp0 - F) /\
  sv8 W mem (F + 32) HI_G_CLIENT /\ sv8 W mem (F + 40) HI_G_SDEAD /\ sv8 W mem (F + 48) (rg_s fr_RG) /\
  sv8 W mem (F + 56) HI_G_SEINTR /\ sv8 W mem (F + 64) HI_G_GONE /\ sv8 W mem (F + 72) HI_G_SMAX /\
  sv8 W mem (F + 80) FF /\ sv8 W mem (F + 96) (SB + FF / 8) /\ sv8 W mem (F + 104) FF /\
  sv8 W mem (F + 120) (SB + rg_s fr_RG / 8) /\ sv8 W mem (F + 128) (rg_s fr_RG + 4) /\
  sv8 W mem (F + 136) DIV10 /\ sv8 W mem (F + 152) (SB + (rg_s fr_RG + 4) / 8) /\ sv8 W mem (F + 184) FF /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) A_LLVMF /\ awr W mem FF 128 /\
  garr8 segs (arm W mem) (SB + FF / 8) sh /\ awr W mem (SB + FF / 8) 16.
Lemma gframe_of_aframe : forall cx FF W mem, aframe_at cx FF W mem -> gframe cx fake_shadow FF W mem.
Proof. intros cx FF W mem H. exact H. Qed.
Lemma aframe_of_gframe : forall cx FF W mem, gframe cx fake_shadow FF W mem -> aframe_at cx FF W mem.
Proof. intros cx FF W mem H. exact H. Qed.
(* the id byte and the cursor after it (fuzz_u8 on in.n = 0 gives 0 and consumes nothing) *)
Definition gn_more (cx : lfcx) (m : lmod) : bool := lm_k m + 1 <? c_n cx.
Definition gn_id (cx : lfcx) (m : lmod) : Z := if gn_more cx m then in_byte cx (lm_k m + 1) else 0.
Definition gn_kq (cx : lfcx) (m : lmod) : Z := if gn_more cx m then lm_k m + 2 else lm_k m + 1.
(* what every cut point inside the arm carries: the journal, the frame (fake shadow sh), the fake frame's flag word
   (lcut's own clause), the cursor slots F+16 / F+144, t at F+88, the input, the image views *)
Definition gcom (cx : lfcx) (t kq : Z) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate) (W : world segs)
    (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly S W mem md kk /\
  gframe cx sh (frame_addr ly 1 fpos) W mem /\
  sv8 W mem (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos) /\
  sv8 W mem (lf_F cx + 16) (c_p cx + kq) /\ sv8 W mem (lf_F cx + 144) (c_n cx - kq) /\
  sv8 W mem (lf_F cx + 88) t /\
  ainput_at B cx ly S W mem /\ rom_view segs W mem /\ jt_rom W mem.
(* the operation's facts: op 5 decoded at lm_k, the stream empty at the dispatch *)
Definition gn_op (cx : lfcx) (t : Z) (m : lmod) : Prop :=
  in_byte cx (lm_k m) mod 10 = 5 /\ lm_O m = [] /\ 0 <= t < OPS_MAX /\ 0 <= lm_k m < c_n cx.
(* the registers the whole arm keeps (callee-saved, written by no instruction of the arm): sp = s1 = F, s0, s2, s3,
   s11, gp, tp *)
Definition gn_kregs (cx : lfcx) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 18 = w64 HI_G_SRC /\ getr regs 19 = w64 (FF + 32) /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).
(* 0x84aa8: s5 = id, s8 = Shadow(FF) (the unpoison's base), s10 = HI_G_NOUT (spilled in p3) *)
Definition GJN (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_join) regs mem md /\
    gcom cx t (gn_kq cx m) fake_shadow fpos ly S W mem md kk /\
    amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S /\ LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 24 = w64 (SB + frame_addr ly 1 fpos / 8) /\ getr regs 26 = w64 HI_G_NOUT /\
    getr regs 21 = w64 (gn_id cx m).

(* ================================================================== the arm's model notions (A's base, verbatim) *)
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
(* the harness source relay_instance_gone drains with the table entry e: the pure half of W_contract's dr_src_ok *)
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
(* the model after relay_instance_gone *)
Definition gn_after_rig (cx : lfcx) (m : lmod) (hs : list (hsrc * nat)) (qs : list (rentry * hsrc))
    (c2 : ctl) (O2 : list byte) (cap2 out2 : Z) (m1 : lmod) : Prop :=
  lm_k m1 = gn_kq cx m /\ lm_G m1 = lm_G m /\ lm_es m1 = map fst qs /\
  lm_c m1 = c2 /\ lm_O m1 = O2 /\ lm_mx m1 = lm_mx m /\ lm_cap m1 = cap2 /\ lm_out m1 = out2 /\
  lm_gn m1 = lm_gn m /\ lm_nfd m1 = lm_nfd m /\ length (lm_hs m1) = 4%nat /\
  (forall j, (j < 4)%nat -> ~ In j (rig_slots (combine (lm_es m) hs)) ->
     nth j (lm_hs m1) None = nth j (lm_hs m) None) /\
  (forall i, (i < length (lm_es m))%nat -> re_eof (nth i (lm_es m) gn_e0) = 0 ->
     nth (snd (nth i hs gn_hj0)) (lm_hs m1) None = Some (snd (nth i qs gn_q0))).
(* what relay_instance_gone's post says of the new table qs beyond where each drained source landed *)
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
   held list's capacity never shrinks, and its EXACT capacity law: W_contract.v:2093-2097, the twin of A's
   W_contract.v:2082-2086) *)
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
(* The table-order loop of fuzz_reply.c:647-653 as a relation over the model (A's base, verbatim) *)
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
   relation is gn_run's constructor for constructor (gn_runc_run), so a fact about gn_run holds of gn_runc's run
   (A's base, verbatim) *)
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

(* ================================================================== the callee texts *)
Variable MMAX : Z.                                   (* W6's / W7's request bound *)
(* The G each of the two table-order calls is taken at: the 32 bytes of slot j's two lists (expected at +64, held at
   +80), which is what both specs' premise `forall a, HA + 64 <= a < HA + 96 -> inG G a` asks (A's base, verbatim) *)
Definition gn_Gs (j : nat) : list (Z * Z) := [(rg_s fr_RG + ASRC * Z.of_nat j + 64, 32)].
(* check_no_loss (0x85e3c, AF_fr_check_no_loss 0x3af8): the kit's cnl_spec (W_contract.v Section w3n), at each slot's
   own G *)
Definition GN_CNL : Prop :=
  forall j, (j < 4)%nat -> cnl_spec (PI := PB_fr) B MT (gn_Gs j) MMAX (BASE + AF_fr_check_no_loss).
(* check_shape_ends (0x85770, AF_fr_check_shape_ends 0x342c): the kit's cshe_spec (W_contract.v Section w3e), at each
   slot's own G *)
Definition GN_CSHE : Prop :=
  forall j, (j < 4)%nat -> cshe_spec (PI := PB_fr) B MT (gn_Gs j) (BASE + AF_fr_check_shape_ends).

(* ---- the G-coverage facts: every global a callee writes is one of the entry's G_fr (A's base) ---- *)
Definition GN_HGs : Prop := forall a, rg_s fr_RG <= a < rg_s fr_RG + 4 * ASRC -> inG G_fr a.
Definition GN_HG_RIG : Prop := forall a, inG (G_RIG B fr_RG) a -> inG G_fr a.
(* every cell amodel_at names (B's globals by fr_RG and the cut's AG_NFD / AG_THREAD_UP / AG_LISTEN) *)
Definition gn_cells : list (Z * Z) :=
  [(rg_s fr_RG, 4 * ASRC); (rg_src fr_RG, 8); (rg_nsrc fr_RG, 4); (rg_capsrc fr_RG, 4);
   (rg_out fr_RG, 8); (rg_nout fr_RG, 8); (rg_capout fr_RG, 8); (rg_send_max fr_RG, 8);
   (rg_send_eintr fr_RG, 1); (rg_send_dead fr_RG, 1); (rg_gone fr_RG, 1); (rg_client fr_RG, 4);
   (rg_client_broken fr_RG, 1); (rg_lock fr_RG, 12); (rg_wake fr_RG + 4, 4);
   (AG_NFD, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)].
Definition GN_HGcells : Prop := forall a, inG gn_cells a -> inG G_fr a.
(* errno is none of the model's cells (an instance fact: as_errno B = 0x5d994c at the pin) *)
Definition GN_CELLS_ERRNO : Prop := forall a, inG gn_cells a -> ~ (as_errno B <= a < as_errno B + 4).
(* the read-only bytes the allocator owns are pinned in every AR state (an instance fact) *)
Definition GN_ROM_PIN : Prop :=
  forall a, in_rom segs a -> Exists (in_zr a) (as_owned_static B) -> rom_pinned segs B a.
(* A's GN_SEP_REQ (ablocks_sep's clause over the allocator's range of a block): on B the cut's ablocks_sep already
   states it over req_size (a987841a18c), so it is PROVED here, not taken *)
Definition GN_SEP_REQ : Prop :=
  forall cx m ly S, ablocks_sep B fr_FP cx m ly S ->
  forall b, In b (model_blks m) ->
    ~ In b (ablocks B (c_ly cx) (c_S cx)) \/
    (forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
Lemma gn_sep_req : GN_SEP_REQ.
Proof. intros cx m ly S (_ & H). exact H. Qed.
(* g_s lies in the instance's zero-shadow ranges (at B's pin: lib/B YF0m's Tfib_zero_shadow holds (0x5d8e60, 384)) *)
Definition GN_HZS : Prop := azs B (rg_s fr_RG) (4 * ASRC).
(* errno's place (lib/B/W_LLVMFuzzerTestOneInput_G.v c_ERRNO_LOW's text) *)
Definition GN_ERRNO_LOW : Prop := 0 <= as_errno B /\ as_errno B + 4 <= alloc_ceiling + 8.

(* ---- the arm's model obligations (pure, over lmod and the plain records; A's base with k4's cnl_room / cnl_cost
   in place of A's stub parameters) ---- *)
Definition GN_RI_pairs : Prop := forall cx t m, RINV cx t m -> exists hs, gn_pairs m hs.
Definition GN_RI_fds : Prop := forall cx t m i1 i2 h1 h2,
  RINV cx t m -> (i1 < 4)%nat -> (i2 < 4)%nat -> i1 <> i2 ->
  nth i1 (lm_hs m) None = Some h1 -> nth i2 (lm_hs m) None = Some h2 -> hs_fd h1 <> hs_fd h2.
Definition GN_RI_read : Prop := forall cx t m hs qs c2 O2 cap2 out2 m1 k h,
  RINV cx t m -> gn_pairs m hs -> gn_after_rig cx m hs qs c2 O2 cap2 out2 m1 ->
  gn_rig_ok cx m hs qs c2 O2 cap2 ->
  (k < 4)%nat -> gn_reads m k = 1 -> nth k (lm_hs m1) None = Some h ->
  hl_recs (hs_pending h) = [] /\ hs_off h = 0.
(* KF-COUNT: cst is no longer free.  The loop's state is reached from the LS state at most at relay_instance_gone's
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
  Z.of_nat (length (lm_O mc)) < 2 ^ 32 /\
  (lm_gn m1 = 0 -> exists rest, skipn (Z.to_nat A) (lm_O mc) = bstream (hs_expected h) ++ rest) /\
  AREC * capb (hs_held h) (hs_expected h) < 2 ^ 32 /\
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
(* KF-COUNT: cst is bounded as in GN_RI_step (the whole loop's q). *)
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
   form and the g_capout premises are gone from rig_spec).  The text is A's (3d17f490d56, f5d40188e29), which is
   s5-r1d's adopted TX_GN_LS_rig token for token (A: commit 1318828167d, lib/A/ReplyLS3Peak.v:171, with LS for LSx), so
   top_x plugs it by exact:
   - gn_op is this file's (:379), whose body A's ReplyLS3cTopxGoneF.gn_op copies (A: ReplyLS3cTopxGoneF.v:65);
   - the g_capout clause is A's ReplyLS3eCap.ent_capout_ok0 (A: ReplyLS3eCap.v:134) at the entry's world and memory,
     written out: that file Requires the AR arms, which this one must not.  It is the cut's CAPOUT clause
     (_cut.v:301-302), the last conjunct of the entry's pre;
   - the last two conclusions are the request bound of the table and the send room the plain rows prove too.
   The walk holds every premise at GRG: gn_op and gn_pairs, aentry_ok's |re_U| <= APARTIAL, the model blocks' sizes
   not negative (the AR block law), every open source's pending offset (asrc_at W_rep.v:107-108), and the pre's
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
   the LS state's count bound is LS_cnt's, at the arm's peak gn_pk (A: a Theorem Labs lane's pk_gone, commit ba8e99b5bd2,
   lib/A/ReplyLScnt.v:476, at the instance).  The walk's block relation (gn_tie) makes a call's live blocks the input,
   the model's blocks at the call and the LS state's rest, so what a call needs beyond LS_cnt is a fact of the MODEL
   alone: the model's count at the call plus the callee's premise peak stays under the LS state's model count plus
   gn_pk, for every count predicate P.  Pure model rules, no astate. *)
Variable gn_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
(* the two callee premise peaks the arm meets, as functions of what the call is made at: relay_instance_gone's
   (the room kit's W_contract_x.v rig_pk at its rig_tr) and check_no_loss's (cnl_pk of the slot's two lists).  They are
   PARAMETERS here, not W_contract_x's names: this file is AR-side and must not Require the _x kit (that kit's global
   zify flag reaches every file that Requires it, and breaks lia in the AR phases).  The _x arm passes W_contract_x's
   names; check_shape_ends' peak is the constant 0 (A: cshe_pk, W_contract_x.v:348), written out *)
Variable gn_rig_pk : lfcx -> lmod -> list (hsrc * nat) -> (Z -> bool) -> nat.
Variable gn_cnl_pk : hsrc -> (Z -> bool) -> nat.
(* relay_instance_gone is called at the LS state itself (GRG holds LS at the call's state), so its premise peak
   must fit inside the arm's peak *)
Definition GN_CNT_rig : Prop := forall cx m hs (P : Z -> bool),
  (gn_rig_pk cx m hs P <= gn_pk cx m hs P)%nat.
(* check_no_loss on slot k of the table-order loop, at the loop model mc that relay_instance_gone and the earlier
   check_no_loss / check_shape_ends calls left; then check_shape_ends on the source check_no_loss left.  The premises
   are GN_RI_step's (the walk holds them at both calls), the model blocks' sizes not negative, and the representation
   clause of the table relay_instance_gone leaves (rig_post_x's arelay_at .. (map fst qs) -> aentry_ok
   W_rep.v:134-135) *)
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
Definition gst (cx : lfcx) (t kq : Z) (m : lmod) (sh : list Z) (fpos : Z) (ly : alayout) (S : astate)
    (W : world segs) (mem : word -> option byte) (md : Model) (kk : Z) : Prop :=
  gcom cx t kq sh fpos ly S W mem md kk /\
  amodel_at B ly S W mem m /\ ablocks_sep B fr_FP cx m ly S.
(* the prefix snprintf left in the fake frame (FF + 32 = s3), as check_shape_ends reads it *)
Definition gn_prefix_at (cx : lfcx) (m : lmod) (W : world segs) (mem : word -> option byte) (FF : Z) : Prop :=
  (forall i, 0 <= i < Z.of_nat (length (gn_pre cx m)) ->
     aview segs (w_H W) mem (FF + 32 + i)
       = Some (bv_unsigned (nth (Z.to_nat i) (gn_pre cx m) (Z_to_bv 8 0)))) /\
  aview segs (w_H W) mem (FF + 32 + Z.of_nat (length (gn_pre cx m))) = Some 0 /\
  (forall a, FF + 32 <= a < FF + 80 -> aview segs (w_H W) mem a <> None) /\
  ~ In (Z_to_bv 8 0) (gn_pre cx m) /\ Z.of_nat (length (gn_pre cx m)) + 9 <= 48.
(* 0x84af8: the reads[] loop's head, q of the four slots done (a do-while: q = 4 leaves at 0x84b28):
   s6 = &g_s[q], s4 = &g_s[q].open, s7 = 4 - q, s8 = F + 192 + 4q, s9 = Shadow(&g_s[q].open), s5 = id *)
Definition GL1 (cx : lfcx) (t : Z) (m : lmod) (q : nat) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_l1) regs mem md /\
    gst cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    getr regs 22 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\ getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) /\
    getr regs 23 = w64 (4 - Z.of_nat q) /\ getr regs 24 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\
    getr regs 25 = w64 (SB + (rg_s fr_RG + 4) / 8 + 12 * Z.of_nat q) /\
    (q < 4)%nat /\
    (forall j, (j < q)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84b40: the four reads[] are written; relay_instance_gone(id) is next (s5 = id, s10 = HI_G_NOUT) *)
Definition GRG (cx : lfcx) (t : Z) (m : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_rig) regs mem md /\
    gst cx t (gn_kq cx m) m fake_shadow_open fpos ly S W mem md kk /\
    LS cx t m ly S /\ RINV cx t m /\ gn_op cx t m /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\
    getr regs 26 = w64 HI_G_NOUT /\ getr regs 21 = w64 (gn_id cx m) /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* what relay_instance_gone has fixed about the model, carried by every state after it.  The last four conjuncts are
   facts of amodel_at at the table and sources BEFORE the call (GRG's gst at m), which GN_RI_step / GN_RI_end take:
   aentry_ok's unfinished-line and key clauses (W_rep.v:128, :139-142; relay_instance_gone ends the keys with the
   prefix, so the table after it no longer holds them), aout_at's capacity clause (W_rep.v:190-191), aentry_ok's
   representation clauses (W_rep.v:127-128, :134-135), and asrc_at's pending-offset clause (W_rep.v:107-108) with
   alist_at's non-empty pending records (W_rep.v:94), the model blocks' sizes not negative (the AR block law over
   ablocks_sep's Permutation; GN_LS_rig / GN_CNT_step / LS_cnt take it), ReplyCnt.msz_ok of the table and sources
   (LS_cnt's guard, gn_msz_ok below), and the representation clause of the table relay_instance_gone LEAVES
   (GN_CNT_step's C2 premise, from rig_post's arelay_at .. (map fst qs), aentry_ok W_rep.v:134-135) *)
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
(* ReplyCnt.msz_ok of the table and sources an amodel_at holds: aentry_ok's capacity and key clauses (W_rep.v:127,
   :140) and the open sources' expected / held alist_at `lines = true` record clause (W_rep.v:93) *)
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
(* 0x84b5c: the check_no_loss_read loop's head, q slots done (a do-while, so q < 4): s4 = &g_s[q],
   s5 = F + 192 + 4q, s6 = F + 208; s10 is spilled at F+24 *)
Definition GC1 (cx : lfcx) (t : Z) (m m1 : lmod) (q : nat)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_c1) regs mem md /\
    gst cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LS cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    getr regs 20 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) /\
    getr regs 21 = w64 (lf_F cx + 192 + 4 * Z.of_nat q) /\ getr regs 22 = w64 (lf_F cx + 208) /\
    (q < 4)%nat /\
    (forall j, (j < 4)%nat -> gn_sv4 W mem (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84b78: the check_no_loss_read loop is done; the table-order loop is entered or skipped *)
Definition GT0 (cx : lfcx) (t : Z) (m m1 : lmod)
    : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_t0) regs mem md /\
    gst cx t (gn_kq cx m) m1 fake_shadow_open fpos ly S W mem md kk /\
    gdone cx t m m1 /\ (exists ly0 S0 cst, LS cx t m ly0 S0 /\ mo_le MT S0 S cst /\ gn_cst cx m m1 0 cst /\ gn_tie cx m ly0 S0 m1 ly S) /\
    gn_kregs cx (frame_addr ly 1 fpos) regs /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 208) 0 /\
    gn_prefix_at cx m W mem (frame_addr ly 1 fpos).
(* 0x84c84: the table-order loop is done; at = g_nout, and the model after the operation is mc *)
Definition GCSD (cx : lfcx) (t : Z) (m mc : lmod) : world segs -> config -> Prop :=
  fun W c => exists regs mem md ly S kk fpos, c = cfg_at segs (fr_B0 + AF_gn_csd) regs mem md /\
    gst cx t (gn_kq cx m) mc fake_shadow_open fpos ly S W mem md kk /\
    LS cx (t + 1) mc ly S /\ RINV cx (t + 1) mc /\ lm_k mc = gn_kq cx m /\
    0 <= gn_kq cx m <= c_n cx /\ 0 <= t < OPS_MAX /\
    sv8 W mem (lf_F cx + 208) (Z.of_nat (length (lm_O mc))) /\
    awr W mem (lf_F cx + 192) 16 /\ sv8 W mem (lf_F cx + 24) HI_G_NOUT /\
    gn_kregs cx (frame_addr ly 1 fpos) regs.
End g.
