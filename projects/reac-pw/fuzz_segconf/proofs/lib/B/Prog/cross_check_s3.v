(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of chain_words (0x8dfd4) on the ASan build of plugin-hostd/fuzz_command
   proves its statement tchain_words_spec (chain_words_c.v:94-134) directly: from the six segments and the transport
   (chain_words_a.v's cw_run), at statement passes 4 and 5 (the FP-existential post apost_baseF, the rounding-mode
   premise, no astack_pres). The returned block's size is exact in the statement
   (chain_words_c.v:127), as the walk's post cw_Q (chain_words_d.v) carries it from the two recorder callees. The
   callee contracts and runtime rules are the statement's, in its forall-fx0 form (chain_words_c.v:84-93); the
   per-binary facts the walk names are CmdRecFacts lemmas: relro_img and cmd_ro_ok_of_aro (CmdRecRo.v),
   cmd_prog_unowned (CmdRecImg.v), all over IMG : cmd_img_facts. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_exact.v, with its module paths and module names changed; 20 of its 39 lines of code are new or changed and 65 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/trim.v, with its module paths and module names changed; 44 of its 65 lines of code are new or changed and 18 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/cross_check_a.v, with its module names changed; 116 of its 142 lines of code are new or changed and 39 lines of the source are left out. *)
(* Segment 3 of the walk of cross_check on reac-pw/fuzz_segconf's ASan+UBSan IMAGE B
   (fuzz_segconf.asan-ubsan, pin c3796c0b38f3; cross_check 0x897cc): the epilogue, 0x899fc
   (CC_EPI = AF_cross_check + 0x230) to the return at 0x89a34. ADAPTED from the image-A G3 walk owner's image-A
   lib/A/Prog/cross_check_s3.v (commit 130284ff40f1), itself in the form of
   plugin-hostd/fuzz_command's lib/A/Prog/check_reply_s8.v and numberR.v (origin/ossv/recipes 501c0d516c69): a
   symbolic state is seeded at the cut from INV_EPI, one plain run (PaLibF.v paj_run_sh) walks the 15
   instructions, and paj_ret_at gives the return configuration, whose post is apost_base lifted to apost_baseF by
   PaFx.v apost_baseF_of_base (the epilogue changes no FP state).

   The instructions walked (cross_check.fuzz_segconf.asan-ubsan.s lines 142-156), no branch, no call, no
   store and no inline check; image B's save slots are image A's, so the only change from the image-A file is
   CC_EPI and the two object indices:
     0x899fc ld ra,120(sp)  0x89a00 ld s0,112(sp)  0x89a04 ld s1,104(sp)  0x89a08 ld s2,96(sp)
     0x89a0c ld s3,88(sp)   0x89a10 ld s4,80(sp)   0x89a14 ld s5,72(sp)   0x89a18 ld s6,64(sp)
     0x89a1c ld s7,56(sp)   0x89a20 ld s8,48(sp)   0x89a24 ld s9,40(sp)   0x89a28 ld s10,32(sp)
     0x89a2c ld s11,24(sp)  0x89a30 addi sp,sp,128 0x89a34 ret

   The seeded state: the registers are the cut's (atoms 0-31), atoms 32..44 are the entry's ra, s0, s1,
   s2..s11 (cc_saved, in slot order), and one READ-ONLY region on the sp atom, [0x18, 0x80), whose 13 chunks are
   the saved slots: slot j of cc_saved at sp + 0x78 - 8 j = sp0 - 8 - 8 j holds atom 32 + j (INV_EPI's
   fi_saved). The region has an empty write window, so the run writes nothing (awr_ok is vacuous and the
   memory at the return is the cut's).

   POSITIONAL NAMES (g3b-common.md): the listing object indices of the two formats are NOT image A's. On image A
   A_OBJ 73 = 0x21c00 = F_xmodel and A_OBJ 74 = 0x21ca0 = F_xbox; on image B lib/B/Prog/SegAddr.v's seg_objs has
   A_OBJ 73 = 0x21ca0 = F_xbox and A_OBJ 74 = 0x21c00 = F_xmodel -- the two are swapped. The hypotheses below
   are stated at image B's indices. (A_OBJ 0 = 0xa3210, the shadow-base GOT word, and A_OBJ 12 = 0xac7b8, the
   shadow-base cell, do keep image A's indices.) *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaRun PaShadow PaStep SegSyms
  SegList SegPa PaJournal SegPaLib PaLibG PaLibF.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegObj SegPgBase SegABase PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c cross_check_c cross_check_f cross_check_d.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

(* the 13 saved slots as chunks on the sp atom (sp = sp0 - 128): slot j at offset 0x78 - 8 j holds atom 32 + j *)
Definition cc3_chunks : list YP09.chunk :=
  map (fun j => YP09.mkChunk (0x78 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13).
(* the frame's save area [sp + 0x18, sp + 0x80), read-only (empty write window) *)
Definition cc3_r : YP09.region := YP09.mkRegion (Some 2%nat) 0x18 0x80 0x18 0x18 cc3_chunks.
(* the state at 0x89460 *)
Definition ss_cc3 : sstate := mkSS CC_EPI sr_atoms [cc3_r] None (mkFacts [] [] []).
(* atoms 32..44: the entry's values of the registers the prologue saved, in slot order *)
Definition cc3_extra (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) cc_saved.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* atom 32 + j of the seeded environment is the entry's value of slot j's register *)
Lemma cc3_ew : forall (regs3 regs0 : bvmap 5 word) j r, nth_error cc_saved j = Some r ->
  ew (Eimg (Ereg regs3 (cc3_extra regs0))) (32 + j) = getr regs0 (Z_to_bv 5 r).
Proof.
intros regs3 regs0 j r Hr.
assert (Hj : (j < length cc_saved)%nat) by (apply nth_error_Some; rewrite Hr; discriminate).
cbn [length cc_saved] in Hj.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold cc3_extra.
apply nth_error_nth. rewrite nth_error_map, Hr. reflexivity.
Qed.

(* the seed: the machine state at 0x89460 satisfies ss_cc3, from INV_EPI's sp and saved slots *)
Lemma cc3_seed : forall (v : ccx) (W3 : world SEGS) (regs3 : bvmap 5 word) (mem3 : word -> option byte),
  getr regs3 2 = w64 (cc_sp0 v - 128) -> 128 <= cc_sp0 v <= 2 ^ 47 ->
  (forall j r, nth_error cc_saved j = Some r ->
    rdword (rdW W3 mem3) (cc_sp0 v - 8 - 8 * Z.of_nat j) = Some (bv_unsigned (getr (x_regs v) (Z_to_bv 5 r)))) ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) ss_cc3
    (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + CC_EPI)) mem3 (seg_rom SEGS))).
Proof.
intros v W3 regs3 mem3 HSP Hsp HSV.
assert (U2 : bv_unsigned (ew (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) 2) = cc_sp0 v - 128).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs3 _ 2 2%bv eq_refl), HSP.
  unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. unfold ss_cc3. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor].
  unfold region_ok, cc3_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_forall. intros c Hc. unfold cc3_chunks in Hc. apply in_map_iff in Hc.
  destruct Hc as (j & <- & Hj). apply in_seq in Hj.
  destruct (nth_error cc_saved j) as [r|] eqn:Hr.
  2: { exfalso. apply nth_error_None in Hr. cbn [length cc_saved] in Hr. lia. }
  apply (chunk_ok_val SEGS _ _ _ _ 8%N _ (bv_unsigned (getr (x_regs v) (Z_to_bv 5 r)))).
  + cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact (cc3_ew regs3 (x_regs v) j r Hr).
  + change (8 * Z.of_N 8) with 64. apply u64_range.
  + lia.
  + replace (cc_sp0 v - 128 + (0x78 - 8 * Z.of_nat j)) with (cc_sp0 v - 8 - 8 * Z.of_nat j) by lia.
    exact (val_mem_of_rdword SEGS (w_H W3) mem3 _ _ (HSV j r Hr)).
- exact (conj I I).
- exact (conj I (conj I I)).
Qed.

(* S3: the epilogue, the 13 reloads and the return. *)
Theorem cc_s3 : forall (B : asyms) (lit : list Z -> Z) (gotw guard STK_REF : Z),
  PALib B -> PALibF B -> seg_val_objs -> seg_sig_prog ->
  (forall a, SEG_RLO <= a < SEG_RHI -> in_img SEGS a) ->
  (forall ly S (W : world SEGS) mem md,
     AR SEGS B ly S W mem md -> sa_ssp (aview SEGS (w_H W) mem) gotw guard) ->
  lit F_xmodel = VAL (A_OBJ 74) -> lit F_xbox = VAL (A_OBJ 73) -> 0 <= STK_REF ->
  (forall fx0 : YK11.FPState,
     @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_REF SEG_RLO SEG_RHI lit gotw guard) ->
  cc_S3P B lit gotw guard STK_REF.
Proof.
intros B lit gotw guard STK_REF TL TLF HVO HSG HRRO HSSP HLM HLB HSTK REF.
pose proof (YG0q.AR_laws_ok SEGS B) as LAWS.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
intros v HP. unfold from_EPI, cc_from. intros ly3 S3 W3 regs3 mem3 md3 (HFI & HRC).
destruct HFI as [HJ HSP HGP HTP HSV HNA].
assert (HPRE : afn_pre SEGS B (cc_STK STK_REF) (x_ly v) (x_S v) (x_W v) (x_regs v) (x_mem v) (x_md v) (x_ch v))
  by (destruct HP; assumption).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold cc_STK in Hslo.
assert (Hsp : 128 <= cc_sp0 v <= 2 ^ 47) by (unfold cc_sp0; lia).
pose proof (cc3_seed v W3 regs3 mem3 HSP Hsp HSV) as HS.
remember (Eimg (Ereg regs3 (cc3_extra (x_regs v)))) as E eqn:HE in HS.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hn. pose proof (u5_range r). rewrite HE, Eimg_low by (unfold A_TEXT; lia).
  apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j (r : bv 5), nth_error cc_saved j = Some (bv_unsigned r) -> ew E (32 + j) = getr (x_regs v) r).
{ intros j r Hr. rewrite HE, (cc3_ew regs3 (x_regs v) j _ Hr), Z_to_bv_bv_unsigned. reflexivity. }
assert (U2 : bv_unsigned (ew E 2) = cc_sp0 v - 128).
{ rewrite (EE 2%nat 2%bv eq_refl), HSP. unfold w64. apply unsigned_lit_small. lia. }
change (cfg_at SEGS (BASE + CC_EPI) regs3 mem3 md3)
  with (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + CC_EPI)) mem3 (seg_rom SEGS)) md3).
paj_run_sh RUNP HS HJ.
- (* the save area is read-only: the run writes no byte *)
  intros a (r & Hr & Ha). unfold ss_cc3 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  unfold cc3_r in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia.
- (* the return *)
  assert (Hmem : ms_mem ms = mem3).
  { apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
    intros (r & Hr & Ha). unfold ss_cc3 in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
    unfold cc3_r in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
  prreg HS (1%bv : bv 5) Q1.
  assert (X0 : ew E 32 = getr (x_regs v) (1%bv : bv 5)) by exact (EX 0%nat (1%bv : bv 5) eq_refl).
  eapply (RET W3 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. unfold cc_post. apply (apost_baseF_of_base SEGS). unfold apost_base.
  lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly3, S3, r, m, d end.
  split; [rewrite Q1, X0; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ|].
  split.
  + apply aregs_preserved_eqs.
    all: lazymatch goal with |- getr _ ?rr = getr _ _ => let Rq := fresh "Rq" in prreg HS rr Rq; rewrite Rq; clear Rq end.
    1: { rewrite U2. replace (cc_sp0 v - 128 + 128) with (cc_sp0 v) by lia. unfold cc_sp0, spZ.
         apply Z_to_bv_bv_unsigned. }
    1: { rewrite (EE 3%nat 3%bv eq_refl), HGP, Hgp. reflexivity. }
    1: { rewrite (EE 4%nat 4%bv eq_refl), HTP, Htp. reflexivity. }
    all: lazymatch goal with |- ew _ ?n = getr _ ?rr =>
      let j := eval compute in (n - 32)%nat in exact (EX j rr eq_refl) end.
  + unfold cc_Q. cbv beta. rewrite Hmem. split; [exact HRC | exact HNA].
Qed.
End f.
End d.
