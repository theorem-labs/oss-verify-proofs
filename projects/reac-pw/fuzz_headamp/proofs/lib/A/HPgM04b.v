(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgScanHead.v at cdde2c4d95b (its hd_reg_is lemma and the run-to-the-call form of hd_A / hd_B) for reac-pw/fuzz_headamp image A, segment M04b (C8 0x83764 -> C9 0x83794); every pc, register, cell and callee is headamp's, and the three runs end in block posts (lib/A/HPgSteps.v hd_blk_post). *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the segment M04b of
   LLVMFuzzerTestOneInput (0x80bc0), the second parse, proved against lib/A/HPgCSpec.v's fixed text
   headamp_plain_contract at image A's record lib/A/HPgImgA.v headamp_himg_A. Proves function
   LLVMFuzzerTestOneInput, segment M04b only (kind: segment lemma).

   THE CODE (fuzz_headamp.c:351-353)
     C8 0x83764  addi a1,zero,0xa5; mv a0,s8 (out); ld a2,0x118(s1) (3 cap + 3)
        0x83770  jal __asan_memset 0x521a8                         ra 0x83774
        0x83774  ld a0,0x110(s1) (the parse's first argument: pod when the null flag is 0, else 0); mv a1,s8; mv a2,s6
        0x83780  jal reac_headamp_prop_parse 0x845ac (res = NULL)  ra 0x83784
        0x83784  mv a1,s11 (rc); mv a2,s8 (out); mv a3,s2 (first)
        0x83790  jal check_plain 0x843e8                           ra 0x83794 = C9
   The walk is three engine runs (st_ok, aj_run_to), each ending at a `jal` in a block post (h4b_blkA, h4b_blkB,
   h4b_blkC: the journal, every byte, every register outside the run's clobbers, and the values the call reads),
   and three calls: the runtime's __asan_memset (lib/A/HPgIntrin.v hd_memset_at under the Section hypothesis
   AMEMSET), the parse (lib/A/HPgCalls.v hc_parse_call under PARSE, its arguments from lib/A/HPgSiteA.v
   headamp_A_site_parse_args_plain) and check_plain (hc_check_plain_call under CKPLAIN, its arguments from
   headamp_A_site_plain).

   THE FLOAT STATE. The memset and the first two runs keep the float state, so the parse is called at the
   segment's own float state fx; PARSE is stated there (the parse's proof, in a Section with Context {fx}, gives it
   at every float state). The parse returns at some fx2 with hd_fxk [14; 15] fx fx2, and the third run and
   check_plain run at fx2; check_plain's proof is in a Section with Context {fx} too, so CKPLAIN is stated as that
   proof gives it once its Section closes, for every float state, and used at fx2. check_plain keeps fx2, so the
   segment returns at fx2, which hd_fxk [14; 15] fx describes (the contract's FX).

   WHAT EACH BYTE DOES. The memset writes the out block and its own stack below R; the parse writes out's cells,
   the errno cell and its own stack below R; check_plain writes only its stack. So every byte outside
   [R - T_SEG_STK, R), out and the errno cell is as at C8 (the contract's E, hi_w5 being empty on image A); in
   particular the first block (apart from out, and from the errno cell, which lies in the image by errno_low), the
   real-frame cells of hi_L9 and the frame's shadow bytes. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSteps HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCalls HPgSiteA HPgIntrin.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== the code table and the cuts inside M04b ============================== *)
Definition H4B_C8 : Z := 0x83764.      (* = hi_c8 headamp_himg_A *)
Definition H4B_SET : Z := 0x83774.     (* the memset's return *)
Definition H4B_PRS : Z := 0x83784.     (* the parse's return, = HPgCalls.RA_PARSE *)
(* the twelve words 0x83764 .. 0x83790 *)
Definition h4b_tbl : ctable := build_table rsegs H4B_C8 12 TEmpty.
Lemma h4b_tbl_ok : table_ok rsegs h4b_tbl.
Proof. apply build_table_ok0. unfold H4B_C8. lia. Qed.
(* the real-frame cells the two loads read: R+0x118 (3 cap + 3) and R+0x110 (the parse's first argument), each the
   extra atom 32 of its run's env *)
Definition h4b_rA : YP09.region := YP09.mkRegion (Some 9%nat) 0x118 0x120 0 0 [YP09.mkChunk 0x118 (CVal 8 (SOff 32 0))].
Definition h4b_rB : YP09.region := YP09.mkRegion (Some 9%nat) 0x110 0x118 0 0 [YP09.mkChunk 0x110 (CVal 8 (SOff 32 0))].

(* a fact kept out of lia's sight *)
Definition h4b_hide (P : Prop) : Prop := P.
Lemma h4b_hide_intro : forall P : Prop, P -> h4b_hide P.
Proof. intros P H. exact H. Qed.

Lemma h4b_pres_trans : forall r1 r2 r3, aregs_preserved r1 r2 -> aregs_preserved r2 r3 -> aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

(* the first block's request 3 max(rc, 0) + (3 max(rc, 0) == 0) holds the parse's 3 n cell bytes *)
Lemma h4b_req3 : forall rcv len, (rcv = -1 /\ len = 0) \/ (0 <= rcv /\ rcv = len) ->
3 * len <= req_size (3 * Z.max rcv 0 + (if 3 * Z.max rcv 0 =? 0 then 1 else 0)).
Proof.
intros rcv len H. unfold req_size.
destruct (Z.eqb_spec (3 * Z.max rcv 0) 0);
  match goal with |- context [?x =? 0] => destruct (Z.eqb_spec x 0) end; lia.
Qed.

Section gen. Context {fx : YK11.FPState}.
(* a register the run left as an atom of the entry env holds that atom's register [RPgScanHead.v hd_reg_is] *)
Lemma h4b_reg_is : forall E ss ms (H : word -> bool) regs extra (r r' : bv 5) n,
st_ok rsegs E ss (restrict H ms) -> env_agree 32 (Ereg regs extra) E ->
sr_get (ss_regs ss) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' -> getr (ms_regs ms) r = getr regs r'.
Proof.
intros E ss ms H regs extra r r' n HS [HA _] Hr Hn.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite HA by (pose proof (u5_range r'); lia). apply ew_Ereg_nat. exact Hn.
Qed.
(* a register the run left as an atom n holds that atom's value *)
Lemma h4b_reg_x : forall E ss ms (H : word -> bool) (r : bv 5) n w,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = w -> getr (ms_regs ms) r = w.
Proof.
intros E ss ms H r n w HS Hr Hw.
rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
exact Hw.
Qed.
(* a register the run left as an expression e holds e's value *)
Lemma h4b_reg_sv : forall E ss ms (H : word -> bool) (r : bv 5) e w,
st_ok rsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof.
intros E ss ms H r e w HS Hr Hw. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hr. exact Hw.
Qed.
End gen.

Ltac h4b_reg_lit HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let x := eval vm_compute in (sr_get (ss_regs ss) r) in
    eapply (h4b_reg_sv _ ss ms _ r x _ HS); [vm_compute; reflexivity | reflexivity]
  end end.

(* ============================== the three runs ============================== *)
Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

(* C8 0x83764 .. the `jal` of __asan_memset 0x83770: a0 = s8, a2 = the cell R+0x118, ra = 0x83774 *)
Lemma h4b_blkA : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (R v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x120 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 v ->
SRr rsegs W (cfg_at rsegs H4B_C8 regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc A_ASAN_MEMSET [1; 10; 11; 12]%bv
 (fun regs2 => aregs_preserved regs regs2 /\ getr regs2 (Z_to_bv 5 1) = w64 H4B_SET /\
  getr regs2 (Z_to_bv 5 10) = getr regs (Z_to_bv 5 24) /\ getr regs2 (Z_to_bv 5 12) = w64 v)).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R v HJ H9 HR0 HR1 Hv Hval.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
assert (E9 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 v]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply hc_u64. lia. }
assert (E32 : ew (Ereg regs [Z_to_bv 64 v]) 32 = Z_to_bv 64 v)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (mkSS H4B_C8 sr_atoms [h4b_rA] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 H4B_C8) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold h4b_rA.
    apply (hm_ro_region rsegs _ (w_H W) memc 9%nat R 0x118 0x120 _ E9); [lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ R 0x118 8 (SOff 32 0) v).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
    + cbn. lia.
    + cbn. lia.
    + exact Hval.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 v]) (Ereg regs [Z_to_bv 64 v])) by apply env_agree_refl.
unfold cfg_at. change (w64 H4B_C8) with (Z_to_bv 64 H4B_C8).
aj_run_to h4b_tbl_ok HS HJ A_ASAN_MEMSET.
{ awr_ok_tac. }
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In ss_mem] in Hin. destruct Hin as [<-|[]].
  cbn [h4b_rA YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
split; [eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]|].
split; [h4b_reg_lit HS|].
split; [eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 24 HS HAE); [vm_compute; reflexivity | reflexivity]|].
eapply (h4b_reg_x _ _ ms (w_H W) _ 32 _ HS); [vm_compute; reflexivity | exact E32].
Qed.

(* the memset's return 0x83774 .. the `jal` of the parse 0x83780: a0 = the cell R+0x110, a1 = s8, a2 = s6,
   ra = 0x83784 *)
Lemma h4b_blkB : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word) (R v : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
getr regs (Z_to_bv 5 9) = w64 R -> 0 <= R -> R + 0x120 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 v ->
SRr rsegs W (cfg_at rsegs H4B_SET regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc A_PARSE [1; 10; 11; 12]%bv
 (fun regs2 => aregs_preserved regs regs2 /\ getr regs2 (Z_to_bv 5 1) = w64 H4B_PRS /\
  getr regs2 (Z_to_bv 5 10) = w64 v /\ getr regs2 (Z_to_bv 5 11) = getr regs (Z_to_bv 5 24) /\
  getr regs2 (Z_to_bv 5 12) = getr regs (Z_to_bv 5 22))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs R v HJ H9 HR0 HR1 Hv Hval.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
assert (E9 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 v]) 9) = R).
{ rewrite (ew_Ereg_nat regs _ 9 (Z_to_bv 5 9) eq_refl), H9. apply hc_u64. lia. }
assert (E32 : ew (Ereg regs [Z_to_bv 64 v]) 32 = Z_to_bv 64 v)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 v]) (mkSS H4B_SET sr_atoms [h4b_rB] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 H4B_SET) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold h4b_rB.
    apply (hm_ro_region rsegs _ (w_H W) memc 9%nat R 0x110 0x118 _ E9); [lia | lia |].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val rsegs _ _ R 0x110 8 (SOff 32 0) v).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E32.
    + cbn. lia.
    + cbn. lia.
    + exact Hval.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 v]) (Ereg regs [Z_to_bv 64 v])) by apply env_agree_refl.
unfold cfg_at. change (w64 H4B_SET) with (Z_to_bv 64 H4B_SET).
aj_run_to h4b_tbl_ok HS HJ A_PARSE.
{ awr_ok_tac. }
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & Hr). cbn [In ss_mem] in Hin. destruct Hin as [<-|[]].
  cbn [h4b_rB YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. lia. }
split; [eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]|].
split; [h4b_reg_lit HS|].
split; [eapply (h4b_reg_x _ _ ms (w_H W) _ 32 _ HS); [vm_compute; reflexivity | exact E32]|].
split; [eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 24 HS HAE); [vm_compute; reflexivity | reflexivity]|].
eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 22 HS HAE); [vm_compute; reflexivity | reflexivity].
Qed.

(* the parse's return 0x83784 .. the `jal` of check_plain 0x83790: a0 kept, a1 = s11, a2 = s8, a3 = s2,
   ra = 0x83794 *)
Lemma h4b_blkC : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 ->
SRr rsegs W (cfg_at rsegs H4B_PRS regs memc mdc)
(hd_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k0 regs lyc Sc W memc mdc A_CK_PLAIN [1; 11; 12; 13]%bv
 (fun regs2 => aregs_preserved regs regs2 /\ getr regs2 (Z_to_bv 5 1) = w64 RA_CK_PLAIN /\
  getr regs2 (Z_to_bv 5 10) = getr regs (Z_to_bv 5 10) /\ getr regs2 (Z_to_bv 5 11) = getr regs (Z_to_bv 5 27) /\
  getr regs2 (Z_to_bv 5 12) = getr regs (Z_to_bv 5 24) /\ getr regs2 (Z_to_bv 5 13) = getr regs (Z_to_bv 5 18))).
Proof using MTL.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k0 regs HJ.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
assert (HS : st_ok rsegs (Ereg regs []) (mkSS H4B_PRS sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W) (mkst regs (Z_to_bv 64 H4B_PRS) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. exact I. }
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
unfold cfg_at. change (w64 H4B_PRS) with (Z_to_bv 64 H4B_PRS).
aj_run_to h4b_tbl_ok HS HJ A_CK_PLAIN.
{ awr_ok_tac. }
apply SRr_ret.
red. exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdc) mat mdc).
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|].
split; [exact HJ|].
split; [eapply (regs_kept_of_st_ok rsegs _ _ ms regs _ (w_H W) _ HS HAE); vm_compute; reflexivity|].
split; [reflexivity|].
split; [apply Permutation_refl|].
split; [apply same_io_wvb|].
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a. unfold aview, mbyte. rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
  intros (rg & Hin & _). cbn [In ss_mem] in Hin. destruct Hin. }
split; [eapply aregs_preserved_of_st_ok; [exact HS | exact HAE | vm_compute; reflexivity]|].
split; [h4b_reg_lit HS|].
split; [eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 10 HS HAE); [vm_compute; reflexivity | reflexivity]|].
split; [eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 27 HS HAE); [vm_compute; reflexivity | reflexivity]|].
split; [eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 24 HS HAE); [vm_compute; reflexivity | reflexivity]|].
eapply (h4b_reg_is _ _ ms (w_H W) regs _ _ _ 18 HS HAE); [vm_compute; reflexivity | reflexivity].
Qed.

(* a state inside the segment: hc_core moves along a journal that keeps the callee-saved registers *)
Lemma h4b_core : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R
ly2 S2 W2 mem2 md2 (regs2 : bvmap 5 word),
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ->
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
aregs_preserved regs regs2 ->
hc_core rsegs B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 regs2 R.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R ly2 S2 W2 mem2 md2 regs2
  (HJ & Hev & H2 & H3 & H4 & Hal & Hwin & HRs) HJ2 Hp.
split; [exact HJ2|]. split; [exact Hev|].
split; [exact (eq_trans (Hp 2 ltac:(unfold acallee_saved; lia)) H2)|].
split; [exact (eq_trans (Hp 3 ltac:(unfold acallee_saved; lia)) H3)|].
split; [exact (eq_trans (Hp 4 ltac:(unfold acallee_saved; lia)) H4)|].
split; [exact Hal|]. split; [exact Hwin | exact HRs].
Qed.

Lemma h4b_mo : forall s1 s2 s3, mo_le MT s1 s2 0 -> mo_le MT s2 s3 0 -> mo_le MT s1 s3 0.
Proof using MTL. intros s1 s2 s3 H1 H2. exact (mo_le_trans MT MTL _ _ _ _ _ H1 H2). Qed.
End blk.

(* ============================== M04b ============================== *)
Section m04b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI : Z.
(* the runtime's __asan_memset at image A's entry (YG0d.v; discharged by the runtime layer) *)
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet 0x521a8.
(* the parse at reac_headamp_prop_parse 0x845ac with image A's literals, stack-guard cells and doubles, at the
   segment's float state (the memset keeps it) *)
Hypothesis PARSE : hd_parse_specX rsegs B MT 0x845ac RLO RHI 0x21460 0x21480 0x214a0 0x214c0 0x9cff8 0x5f7d90
  headamp_A_dcs.
(* check_plain at 0x843e8, at every float state: it runs at the parse's return state *)
Hypothesis CKPLAIN : forall fx' : YK11.FPState, hd_check_plain_specX (fx := fx') rsegs B MT 0x843e8.
(* the errno cell lies in the image, low (YCbq.v api_env: the malloc step's errno_low), so no block and no stack
   byte is it *)
Hypothesis errno_low : api_env rsegs B.
(* the meter's laws (YC5d.v): the segment's meter clause composes the callees' *)
Hypothesis MTL : ameter_laws MT.
(* the read-only window of arodata_okP lies in the image (HPgBase.v arodata_ok_journalP's relro_img;
   lib/A/HPgSiteA.v headamp_A_relro_img at lib/A/HPgLib.v's window 0x9bc80 .. 0x9d068) *)
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img rsegs a.

Theorem headamp_A_plain_holds : headamp_plain_contract rsegs B MT headamp_himg_A RLO RHI.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs e pos ev r
  HPRE HL8 Hwf Hlen Hpod HPf Hpra Hphull Hpam Hpal HOf Hora Hap HFf Hfra Hfirst Hrc Herr Hfrm.
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs. pose proof (YG0q.AR_laws_ok rsegs B) as LAWS.
pose proof HPRE as (HJ & Hev & H2 & H3 & H4 & HeS & HR32 & HRS & HSTK & Hown & HeF & Hfsh & Hcap & Hnull & _).
cbn [hi_rsz headamp_himg_A] in HRS.
pose proof errno_low as ((Herr0 & Herr4) & HEi & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hs16 & _) & _).
pose proof (hc_core_of_seg_pre_A rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos HPRE)
  as HC0.
pose proof (hc_core_R rsegs B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (e_R e) HC0) as (HRlo & HRhi & HspR).
pose proof HC0 as (_ & _ & _ & _ & _ & HR16 & _).
pose proof HPf as (Hp0 & Hpin & Hpout).
pose proof HOf as (Ho0 & HOin & HOout).
pose proof HFf as (Hf0 & HFin & HFout).
assert (Hcx : hd_cctx rsegs B lyc Sc W memc mdc e pos).
{ split; [exact (proj1 HJ)|]. split; [exact HOin|].
  split; [pose proof HJ as (_ & _ & _ & _ & _ & Hfr0 & _); rewrite Hfr0; apply in_or_app; left; exact Hown|].
  split; [exact HeF|]. split; [lia | exact Hcap]. }
pose proof (hd_cctx_facts rsegs B _ _ _ _ _ _ _ Hcx)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & _).
assert (HRv : 0x7fff7f800000 + 16384 <= e_R e <= 2 ^ 47) by (unfold T_SEG_STK, ASTACK in HRlo; lia).
apply h4b_hide_intro in Oapp. apply h4b_hide_intro in Fapp. apply h4b_hide_intro in Hap.
assert (Hrqo : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hlb). rewrite <- Hlen in Hlb.
assert (Hrqp : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ (proj1 HJ) Hpin) as (_ & P4 & Pce & _ & _).
rewrite Hrqp in Pce.
(* the first block: below the ceiling, outside the image *)
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc _ _ (proj1 HJ) HFin) as (_ & Q4 & Qce & _ & _).
assert (Qni : forall a, e_first e <= a < e_first e + req_size (hd_xv e XRc3NZ) -> ~ in_img rsegs a)
  by (intros a Ha; exact (hd_block_not_img rsegs B lyc Sc W memc mdc _ _ a (proj1 HJ) HFin Ha)).
(* the parse's answer: at most cap cells *)
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : Z.of_nat (length (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))
  <= e_cap e)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
assert (Hfq : 3 * Z.of_nat (length (ans_cells (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e))))
  <= req_size (hd_xv e XRc3NZ)).
{ cbn [hd_xv]. rewrite Hrc. apply h4b_req3.
  destruct Hcase as [(Hm1 & Hc & _)|(Hr & Hl & _)]; [left; rewrite Hc; cbn [length]; lia | right; lia]. }
apply h4b_hide_intro in Hcase.
(* the cut list at C8, value by value *)
pose proof HL8 as HL8c.
unfold hd_cut in HL8. cbn [hi_L8 headamp_himg_A] in HL8.
repeat rewrite Forall_cons_iff in HL8.
destruct HL8 as (A8 & A9 & A18 & A19 & A22 & A24 & A25 & A26 & A27 & C20 & Cf0 & C110 & C118 & _).
cbn [fst snd hd_at hd_xv] in A8, A9, A18, A19, A22, A24, A25, A26, A27, C20, Cf0, C110, C118.
rewrite Z.mod_small in C118 by lia.
assert (C110' : val_mem rsegs (mrestrict (w_H W) memc) (e_R e + 0x110) 8 (hd_xv e XProps)).
{ revert C110. cbn [hd_xv]. destruct (e_null e =? 0); intros C110; rewrite Z.mod_small in C110 by lia; exact C110. }
assert (Hprops : 0 <= hd_xv e XProps < 2 ^ 64) by (cbn [hd_xv]; destruct (e_null e =? 0); lia).
assert (HL9 : hd_cut rsegs (w_H W) memc regs e (hi_L9 headamp_himg_A)).
{ unfold hd_cut in HL8c |- *. cbn [hi_L8 hi_L9 headamp_himg_A] in HL8c |- *.
  rewrite Forall_forall in HL8c |- *. intros f Hf. apply HL8c. cbn [In] in Hf |- *. tauto. }
change (hi_c8 headamp_himg_A) with H4B_C8.
(* ---------------- run A: C8 .. the memset's `jal` ---------------- *)
eapply SRr_bind.
{ apply (h4b_blkA B MT MTL STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (e_R e) (3 * e_cap e + 3) HJ A9);
    [lia | lia | lia | exact C118]. }
intros WA cA HleA (lyA & SA & regsA & memA & mdA & -> & HJA & _ & HfrA & HpmA & HioA & HmoA & HmemA &
  (PA & RA1 & RA10 & RA12)).
assert (HOinA : In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyA SA))
  by exact (Permutation_in _ (Permutation_sym HpmA) HOin).
destruct (hm_blk_ra rsegs B lyA SA WA memA mdA (e_out e) (3 * (e_cap e + 1)) (e_out e) (3 * e_cap e + 3)
  (proj1 HJA) HOinA ltac:(lia) ltac:(rewrite Hrqo; lia)) as (HraA & HhullA).
assert (EspA : getr regsA 2 = w64 (e_R e)) by exact (eq_trans (PA 2 ltac:(unfold acallee_saved; lia)) H2).
(* ---------------- __asan_memset(out, 0xa5, 3 cap + 3) ---------------- *)
eapply SRr_bind.
{ apply (hd_memset_at B AMEMSET WA regsA memA STK sp0 FP ly S W0 mem0 md0 own lyA SA mdA k (e_out e)
    (bv_unsigned (getr regsA 11)) (3 * e_cap e + 3) (e_R e - sp0) (w64 H4B_SET) HJA).
  - exact (eq_trans RA10 A24).
  - unfold w64. symmetry. apply Z_to_bv_bv_unsigned.
  - exact RA12.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite EspA, hc_u64 by lia. ring.
  - rewrite Zminus_mod, HR16, Hs16. reflexivity.
  - lia.
  - unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - exact (eq_trans (PA 3 ltac:(unfold acallee_saved; lia)) H3).
  - exact (eq_trans (PA 4 ltac:(unfold acallee_saved; lia)) H4).
  - exact RA1.
  - apply hc_ret_ok; [unfold H4B_SET; lia | reflexivity].
  - intros a Ha. split.
    + replace a with (e_out e + (a - e_out e)) by lia.
      apply (hd_fresh_awr_n STK sp0 FP _ _ lyA own (e_out e) (3 * (e_cap e + 1)) HOinA HOout); lia.
    + unfold ESTACK, T_SEG_STK, ASTACK in *. lia.
  - unfold h4b_hide in Oapp. unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *. lia.
  - exact HraA.
  - exact HhullA. }
intros WM cM _ (-> & regsM & memM & mdM & -> & HJM & HioM & HpresM & _ & _ & HkeepM & _).
pose proof (h4b_pres_trans _ _ _ PA HpresM) as PM.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
  ~ (e_R e - ESTACK <= a < e_R e) -> aview rsegs (w_H WA) memM a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H5. rewrite (HkeepM a Ha); [apply HmemA | intros Hc; apply H1; lia | intros Hc; apply H5; lia]. }
(* ---------------- run B: the memset's return .. the parse's `jal` ---------------- *)
eapply SRr_bind.
{ apply (h4b_blkB B MT MTL STK sp0 FP ly S W0 mem0 md0 own lyA SA WA memM mdM k regsM (e_R e) (hd_xv e XProps) HJM).
  - exact (eq_trans (PM 9 ltac:(unfold acallee_saved; lia)) A9).
  - lia.
  - lia.
  - exact Hprops.
  - eapply hd_val_mem_kept; [|exact C110'].
    intros i Hi. cbn in Hi. apply KM; unfold ESTACK, T_SEG_STK, ASTACK in *; lia. }
intros WB cB HleB (lyB & SB & regsB & memB & mdB & -> & HJB & _ & HfrB & HpmB & HioB & HmoB & HmemB &
  (PBk & RB1 & RB10 & RB11 & RB12)).
pose proof (h4b_pres_trans _ _ _ PM PBk) as PB.
pose proof (h4b_core B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs (e_R e) lyB SB WB memB mdB regsB
  HC0 HJB PB) as HCB.
assert (HPmB : Permutation (ablocks B lyB SB) (ablocks B lyc Sc)) by exact (Permutation_trans HpmB HpmA).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
  ~ (e_R e - ESTACK <= a < e_R e) -> aview rsegs (w_H WB) memB a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H5. rewrite HmemB. exact (KM a Ha H1 H5). }
assert (HM5 : forall a, 0 <= a < 2 ^ 64 -> ~ (e_R e - T_SEG_STK <= a < e_R e) ->
  ~ (hd_inw e (hi_w5 headamp_himg_A) a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1))) ->
  aview rsegs (w_H WB) memB a = aview rsegs (w_H W) memc a).
{ intros a Ha Hs Hn. apply KB; [exact Ha | intros Ho; apply Hn; right; exact Ho |].
  unfold ESTACK, T_SEG_STK, ASTACK in *. lia. }
assert (HPB : hd_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regsB lyB SB WB memB mdB).
{ eapply hc_pre; [exact HCB | exact RB1 | unfold H4B_PRS; lia | reflexivity |].
  unfold T_parse_STK, T_PARSE_FRAME, ESTACK, T_SEG_STK, ASTACK. lia. }
pose proof (headamp_A_site_parse_args_plain rsegs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI
  e pos ev r k regsB lyB SB WB memB mdB headamp_A_segs_low RELRO errno_low headamp_A_img_bytes_rsegs HPRE Hwf Hlen
  Hpod HPf HOf Hap Herr Hfrm HPB HPmB HM5) as HPA.
(* ---------------- reac_headamp_prop_parse(props, out, cap) ---------------- *)
apply (hc_parse_call rsegs B MT RLO RHI (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A)
  (hi_asens headamp_himg_A) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A) PARSE _
  STK sp0 FP ly S W0 mem0 md0 own k lyB SB WB memB mdB regsB (e_R e) (e_null e) (e_pod e) (e_out e) (e_cap e) ev
  (Model.buf r) HCB RB1 Hnull RB10 (eq_trans RB11 (eq_trans (PM 24 ltac:(unfold acallee_saved; lia)) A24))
  (eq_trans RB12 (eq_trans (PM 22 ltac:(unfold acallee_saved; lia)) A22)) HPA).
intros WP fx2 lyP SP regsP memP mdP HleP Hfx2 HCP HpresP HfrP HpmP HioP HmoP HkeepP HP10 HPout _ HPerr.
set (O := Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)) in *.
pose proof (h4b_pres_trans _ _ _ PB HpresP) as PP.
assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
  ~ (e_R e - T_SEG_STK <= a < e_R e) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview rsegs (w_H WP) memP a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H5 H6. rewrite (HkeepP a Ha).
  - apply KB; [exact Ha | exact H1 | unfold ESTACK, T_SEG_STK, ASTACK in *; lia].
  - unfold T_parse_STK, T_PARSE_FRAME, ESTACK, T_SEG_STK, ASTACK in *. lia.
  - intros [Hc|[(Hc & _)|Hc]]; [apply H1; lia | exact (Hc eq_refl) | exact (H6 Hc)]. }
(* ---------------- run C: the parse's return .. check_plain's `jal` (at the parse's float state) ---------------- *)
eapply SRr_bind.
{ apply (h4b_blkC (fx := fx2) B MT MTL STK sp0 FP ly S W0 mem0 md0 own lyP SP WP memP mdP k regsP (proj1 HCP)). }
intros WC cC HleC (lyC & SC & regsC & memC & mdC & -> & HJC & _ & HfrC & HpmC & HioC & HmoC & HmemC &
  (PCk & RC1 & RC10 & RC11 & RC12 & RC13)).
pose proof (h4b_pres_trans _ _ _ PP PCk) as PC.
pose proof (h4b_core B STK sp0 FP ly S W0 mem0 md0 own k lyP SP WP memP mdP regsP (e_R e) lyC SC WC memC mdC regsC
  HCP HJC PCk) as HCC.
assert (HPmC : Permutation (ablocks B lyC SC) (ablocks B lyc Sc))
  by exact (Permutation_trans HpmC (Permutation_trans HpmP HPmB)).
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
  ~ (e_R e - T_SEG_STK <= a < e_R e) -> ~ (as_errno B <= a < as_errno B + 4) ->
  aview rsegs (w_H WC) memC a = aview rsegs (w_H W) memc a).
{ intros a Ha H1 H5 H6. rewrite HmemC. exact (KP a Ha H1 H5 H6). }
assert (HoutC : garr8 rsegs (mrestrict (w_H WC) memC) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells O)))).
{ eapply hd_garr8_kept; [|exact HPout]. intros j _. apply HmemC. }
assert (HfstC : garr8 rsegs (mrestrict (w_H WC) memC) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells O)))).
{ destruct (Z.eq_dec (e_first e) (e_out e)) as [Heq|Hne]; [rewrite Heq; exact HoutC|].
  pose proof (hm_blk_apart rsegs B lyc Sc W memc mdc (e_first e) (hd_xv e XRc3NZ) (e_out e) (3 * (e_cap e + 1))
    (proj1 HJ) HFin HOin Hne) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrqo in Hz.
  eapply hd_garr8_kept; [|exact Hfirst].
  intros j Hj. unfold hd_zbytes in Hj. rewrite length_map, length_ha_cells_bytes in Hj.
  apply KC.
  - unfold T_SEG_STK, ASTACK in *. lia.
  - lia.
  - unfold T_SEG_STK, ASTACK in *. lia.
  - intros He. apply (Qni (e_first e + Z.of_nat j)); [lia | exact (HEi _ He)]. }
assert (HPC : hd_pre rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regsC lyC SC WC memC mdC).
{ eapply hc_pre; [exact HCC | exact RC1 | unfold RA_CK_PLAIN; lia | reflexivity |].
  unfold T_check_STK, T_SEG_STK, ASTACK. lia. }
destruct (headamp_A_site_plain rsegs B STK sp0 FP ly S W0 mem0 md0 own k regsC lyC SC WC memC mdC e
  (hd_props (e_null e) (Model.buf r)) O O HPC (Permutation_in _ (Permutation_sym HPmC) HOin)
  (Permutation_in _ (Permutation_sym HPmC) HFin) Hcap eq_refl eq_refl Hrc HfstC HoutC) as (_ & Hrng & Hbig).
(* ---------------- check_plain(rc, rc, out, first) ---------------- *)
apply (hc_check_plain_call (fx := fx2) rsegs B MT (CKPLAIN fx2) _ STK sp0 FP ly S W0 mem0 md0 own k lyC SC WC memC mdC
  regsC (e_R e) (e_rc e) (e_out e) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells O))) HCC RC1).
- rewrite Hrc. exact (eq_trans RC10 HP10).
- exact (eq_trans RC11 (eq_trans (PP 27 ltac:(unfold acallee_saved; lia)) A27)).
- exact (eq_trans RC12 (eq_trans (PP 24 ltac:(unfold acallee_saved; lia)) A24)).
- exact (eq_trans RC13 (eq_trans (PP 18 ltac:(unfold acallee_saved; lia)) A18)).
- exact Hrng.
- exact Hbig.
- intros WF lyF SF regsF memF mdF HleF HCF HpresF HfrF HpmF HioF HmoF HkeepF.
  pose proof (h4b_pres_trans _ _ _ PC HpresF) as PF.
  assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
    ~ (e_R e - T_SEG_STK <= a < e_R e) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview rsegs (w_H WF) memF a = aview rsegs (w_H W) memc a).
  { intros a Ha H1 H5 H6. rewrite (HkeepF a Ha); [exact (KC a Ha H1 H5 H6)|].
    unfold T_check_STK, T_SEG_STK, ASTACK in *. lia. }
  apply SRr_ret. exists fx2, lyF, SF, regsF, memF, mdF.
  split; [reflexivity|].
  split; [exact Hfx2|].
  split; [exact (proj1 HCF)|].
  split; [intros r0 Hr0; apply PF; unfold acallee_saved; lia|].
  split; [rewrite HfrF, HfrC, HfrP, HfrB, HfrA; reflexivity|].
  split; [exact (Permutation_trans HpmF HPmC)|].
  split; [exact (same_io_trans _ _ _ HioA (same_io_trans _ _ _ HioM (same_io_trans _ _ _ HioB
    (same_io_trans _ _ _ HioP (same_io_trans _ _ _ HioC HioF)))))|].
  split; [exact (h4b_mo MT MTL _ _ _ HmoA (h4b_mo MT MTL _ _ _ HmoB (h4b_mo MT MTL _ _ _ HmoP
    (h4b_mo MT MTL _ _ _ HmoC HmoF))))|].
  split.
  { intros a Ha Hs Hn. cbv beta in Hn. rewrite HspR in Hs.
    apply KF; [exact Ha | intros H1; apply Hn; right; left; exact H1 | exact Hs |
      intros H1; apply Hn; right; right; exact H1]. }
  split; [|split].
  + apply (hm_cut_kept rsegs (w_H W) memc (w_H WF) memF regs regsF e _ HL9).
    intros f Hf. cbn [hi_L9 headamp_himg_A In] in Hf.
    destruct Hf as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst hm_keeps hd_xv];
      try (apply PF; unfold acallee_saved; lia);
      (intros i Hi; apply KF; unfold T_SEG_STK, ASTACK, kLowMemEnd in *; lia).
  + pose proof headamp_A_shB_facts as (Bl & _ & _).
    apply (hm_fsh_kept rsegs (w_H W) memc (w_H WF) memF (e_F e) (hi_shB headamp_himg_A) Hfsh).
    intros i Hi. rewrite Bl in Hi. change (Z.of_nat 80) with 80 in Hi.
    unfold h4b_hide in Oapp, Fapp.
    pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
    apply KF; unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK, kLowMemEnd, kLowShadowBeg, kHighMemBeg in *; lia.
  + destruct HPerr as (ev' & Hev'). exists ev'. intros kk Hkk.
    rewrite (HkeepF (as_errno B + Z.of_nat kk)), HmemC; [exact (Hev' kk Hkk) | unfold kLowMemEnd in *; lia |].
    unfold T_check_STK, T_SEG_STK, ASTACK, kLowMemEnd in *. lia.
Qed.
Print Assumptions headamp_A_plain_holds.
End m04b.

Print Assumptions h4b_blkA.
Print Assumptions h4b_blkB.
Print Assumptions h4b_blkC.
Print Assumptions headamp_A_plain_holds.
