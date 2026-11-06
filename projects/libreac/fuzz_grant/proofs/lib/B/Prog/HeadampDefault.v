(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry seat, the run and the return adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v for libreac/fuzz_grant's reac_headamp_default; the contract and the value lemma are new. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/HeadampDefault.v, ported from a working branch d98082bd58b: the same text over image B's listing and walk layer (lib/B/Prog). Image B's reac_headamp_default (0x85bf0) is byte-identical to image A's 0x84e54, all 4 words. *)
(* reac_headamp_default (image B fuzz_grant.asan-ubsan 0x85bf0; code-identical to fuzz_grant.asan 0x84e54, 4 instructions): the contract of the
   ASan build's code and its walk. The function reads no memory and has no frame: it
   returns Pau's dflt of a0 (32 for the SENS parameter 2, else 0) in a0. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantSyms GrantList GrantPa.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* a0 at the return, as the walk computes it: ((a0 - 2) <u 1) << 5. *)
Definition HD_R : sv := SAlu ALU_SLL (SAlu ALU_SLTU (SOff 10 (-2)) (SLit 1)) (SLit 5).
Lemma hd_value : forall E p, ew E 10 = Z_to_bv 64 p -> 0 <= p < 2 ^ 64 -> U E HD_R = dflt p.
Proof.
intros E p H Hp. unfold HD_R.
rewrite (U_SAlu E ALU_SLL), (U_SAlu E ALU_SLTU), U_SOff, H, !U_SLit, unsigned_lit_small by lia. cbn [zalu_raw].
unfold dflt. destruct (Z.eqb_spec p 2) as [-> | Hne]; [reflexivity|].
replace (zcanon (p + -2) <? zcanon 1) with false by (symmetry; apply Z.ltb_ge; unfold zcanon, M64; lia).
reflexivity.
Qed.
(* The memory is untouched: each run's frame (no writable window) keeps every byte. *)
Local Ltac upd_mem :=
repeat match goal with
| H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H
| H : mem_grows _ _ |- _ => clear H
end;
lazymatch goal with
| HF : frame_of _ ?rs ?m1 ?m2, HM : forall x, ?m1 x = ?m0 x |- _ =>
let HM' := fresh "HM" in
assert (HM' : forall x, m2 x = m0 x)
by (intros x; transitivity (m1 x); [|exact (HM x)]; apply HF; let rs' := eval vm_compute in rs in change rs with rs';
intros (r & Hr & _); destruct Hr);
clear HM HF; rename HM' into HM
end.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The function's address in the image and the stack it needs: no frame of its own,
   ESTACK for the runtime's use. *)
Definition A_reac_headamp_defaultP : Z := BASE + AF_reac_headamp_default.
Definition REAC_HEADAMP_DEFAULT_STK : Z := ESTACK.
Definition SB_HD : Z := 0x7fff8000.
Definition Bx_HD : sv := SLit SB_HD.
Definition Bspan_HD : Z * Z := (SB_HD, SB_HD + 2 ^ 44 - 1).
Definition ss_hd : sstate := mkSS AF_reac_headamp_default sr_atoms [] None (mkFacts [] [] []).
Section h.
Variable B : asyms.
Definition treac_headamp_default_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (p : Z) : world SEGS -> config -> Prop :=
apost_base SEGS B REAC_HEADAMP_DEFAULT_STK [] regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
getr regs' 10 = w64 (dflt p) /\ ly' = ly /\ S' = S /\ W' = W /\ (forall x, mem' x = mem x) /\
Permutation (ablocks B ly' S') (ablocks B ly S)).
Definition treac_headamp_default_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch (p : Z),
afn_pre SEGS B REAC_HEADAMP_DEFAULT_STK ly S W regs mem md ch ->
getr regs 10 = w64 p -> 0 <= p < 2 ^ 64 ->
SRr SEGS W (cfg_at SEGS A_reac_headamp_defaultP regs mem md) (treac_headamp_default_post regs ly S W mem md p).
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Lemma hd_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
st_ok_pi SEGS VAL (Eimg (Ereg regs [])) ss_hd (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_default)) mem (seg_rom SEGS))) /\
sh_ok SEGS Bx_HD [] (Eimg (Ereg regs [])) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split; [|constructor].
rewrite restrict_mkst_fx. unfold ss_hd. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I].
Qed.
Theorem pb_reac_headamp_default : treac_headamp_default_spec.
Proof.
unfold treac_headamp_default_spec.
intros ly S W regs mem md ch p HPRE H10 Hp.
pose proof (pa_wx) as Hwx. pose proof (pa_segs_low) as Hsegs.
destruct (hd_entry W regs mem) as [HS SHOK].
pose proof (ajournal_init SEGS B REAC_HEADAMP_DEFAULT_STK [] ly S W regs mem md ch HPRE) as HJ.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E1 : ew E 1 = getr regs 1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (HAE : env_agree 32 (Ereg regs []) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HM : forall x, mem x = mem x) by reflexivity.
clear HE.
unfold cfg_at, A_reac_headamp_defaultP.
change (w64 (BASE + AF_reac_headamp_default)) with (Z_to_bv 64 (BASE + AF_reac_headamp_default)).
paj_run_tok RUN HS HJ SHOK Bspan_HD; [first [apply awr_ok_nil | awr_ok_tac] |].
upd_mem.
lazymatch goal with HS : st_ok_pi _ _ _ ?ssx (restrict _ ?msc) |- _ =>
pose proof (st_ok_pi_restrict_reg _ E ssx msc (10%bv : bv 5) HS) as R10;
replace (sr_get (ss_regs ssx) (10%bv : bv 5)) with HD_R in R10 by (vm_compute; reflexivity);
prreg HS (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
intros mat';
unfold treac_headamp_default_post, apost_base;
exists ly, S, (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1, E1, Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS); [exact HAE | vm_compute; reflexivity]|];
split; [rewrite R10, denot_lit_U, (hd_value E p E10 Hp); reflexivity|];
split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|];
split; [exact HM | apply Permutation_refl]
end.
Qed.
End h.
End f.
End d.
