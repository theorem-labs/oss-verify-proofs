(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* CARRIED from this tree's proofs/plugin-hostd/fuzz_reply/lib/Reusable/YC80x.v, sha256 cf3f4df5ec612c6607e05a62aecd72975482067da98c80125349f02f167b9d30.
   Re-pointed for lib/B (fuzz_reply.asan-ubsan): each Require of a module that lib/B instantiates now names lib/B's
   module (lib/B/YCbq.v, the instance whose off_img cites YImgTop.IMG_TOP_B; lib/B/YCbqG.v, this carry's own lib/B
   copy).
   The exact changes (`lib.` is OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.; each source line is replaced
   by the lines after `->`, in that order):
   - line 29: `From lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.` -> `From lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.` / `From lib.B Require Import YCbq.`
   - line 30: `From lib.Reusable Require Import YM05 YI16 YG0p YCbqG.` -> `From lib.Reusable Require Import YM05 YI16 YG0p.` / `From lib.B Require Import YCbqG.`
   - line 33: `Unset Lia Cache. Unset Nia Cache.` -> `Local Unset Lia Cache. Local Unset Nia Cache.`
   The Unset Lia Cache / Unset Nia Cache line is made Local: a new file carries only Local settings.
   Nothing else changes: below this comment the bytes are the source's.
   DO NOT EDIT: change the source file on its branch, carry it again, and re-point it again. *)
(* reply-own since QMm W0' (a Theorem Labs lane 2026-10-30, the YCbqG grant); lineage: carried from a working branch
   9d080dc19ee7bf550e1d0ef68328c9cf18ff1605, proofs/omx-clap-core/fuzz_preset/lib/Reusable/YC80x.v, sha256
   60a68820a8c42f20233bb276819df697e03dd71fbaf5aadb99af0f7d928ee5e8, with the module prefix
   OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib -> OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.
   QMm W0' (a Theorem Labs lane): sections j and e take YCbqG's PST_nk (PST holds no kept byte) for ajournal_x_pst_write. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the position-abstract-listing runner of
   proofs/cgif/cgif_file_fuzzer/lib/YC80.v (origin/ossv/recipes c8557374ad2e :52-140) restated over YCbqG.v's journal
   ajournal_x (allocator invariant a parameter ARx, ghost head set Hp threaded as YCbqG.v's SRr_chain_tok_AJx does,
   program statics PST); plus mixed-write twins (suffix m) whose write premise also admits the program's own statics PST,
   from the journal lemma ajournal_x_exec_mixed below. Generic: no image class, no address, no ledger.
   SK (YI16.sink_head) is a Context parameter of every lemma here. Global sink_head instances exist in this tree
   (YI5b.v src0_sink_head, YE2k.v / AE2k.v tfib_sink_head): pass SK explicitly at every use, never let it be inferred. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI16 YG0p.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* Numerals in this file, all as cgif YC80.v / YCbqG.v state them: 64 and 32 (WORD: bit widths), 2 ^ 40 and 2 ^ 64
   (LENGTH: code-span bound, word range), 4 (LENGTH: instruction bytes; text alignment), 0 (DERIVED: listing start offset;
   lower bound). No ADDRESS. *)
(* Membership of an address in a list of ranges is decidable (in_zr is YG0n.v:197). *)
Lemma Exists_in_zr_dec : forall (R : list (Z * Z)) (a : Z), {Exists (in_zr a) R} + {~ Exists (in_zr a) R}.
Proof.
intros R a. apply Exists_dec. intros r. unfold in_zr.
destruct (Z_le_dec (fst r) a) as [H1|H1]; [destruct (Z_lt_dec a (fst r + snd r)) as [H2|H2]|].
- left. lia.
- right. lia.
- right. lia.
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis PST_nk : forall a, Exists (in_zr a) PST -> ~ kept_x segs B a.
(* YCbqG.v's ajournal_x_exec (:365) with a write set Wr that may also cover the program's own statics PST: a function's
   straight-line code writes its own frame and its statics between two calls. The memory change splits at an
   intermediate memory memi (memc' off PST, memc on PST): memc -> memi is ajournal_x_exec over Wr minus PST, and
   memi -> memc' is ajournal_x_pst_write (YCbqG.v:515). No premise beyond ajournal_x_exec's and PST_ok. *)
Lemma ajournal_x_exec_mixed : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
unfold mem_grows, mrestrict in Hgr. unfold mrestrict in Hfr.
pose (memi := fun x : word => if Exists_in_zr_dec PST (bv_unsigned x) then memc x else memc' x).
assert (HJi : ajournal_x segs B PST ARx STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k).
{ apply (ajournal_x_exec segs B PST ARx LAWS segs_low STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memi mdc'
(fun a => Wr a /\ ~ Exists (in_zr a) PST) HJ).
- intros x Hx. specialize (Hfr x). revert Hfr. unfold mrestrict, memi. destruct (w_H Wc x); intros Hfr; [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity|].
apply Hfr. intros Hw. exact (Hx (conj Hw Hq)).
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (fun H => H) | exact Hgr].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity | exact (Hhid x Hh)].
- exact Hsame.
- intros a [Hw Hq]. destruct (HW a Hw) as [Hb|Hb]; [exact Hb | contradiction]. }
apply (ajournal_x_pst_write segs B PST ARx LAWS segs_low PST_ok PST_nk STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k memc' mdc' HJi).
- intros x Hx. unfold mrestrict, memi. destruct (w_H Wc x); [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [contradiction | reflexivity].
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact Hgr | exact (fun H => H)].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (Hhid x Hh) | reflexivity].
- apply same_but_materialized_refl.
Qed.
End j.
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Hypothesis PST_nk : forall a, Exists (in_zr a) PST -> ~ kept_x segs B a.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
(* cgif YC80.v:52-68 (origin/ossv/recipes) over ajournal_x, Hp after S and Hpc after Sc. *)
Definition run_post_pi_tok_AJx (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(r : ptrun_status psym)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) (restrict (w_H W) ms')
| _ => st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms')
end ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
(* cgif YC80.v:69-102 (origin/ossv/recipes) over ajournal_x; the journal step is YCbqG.v's ajournal_x_exec. *)
Lemma SRr_chain_pi_tok_AJx : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* cgif YC80.v:103-121 (origin/ossv/recipes) over ajournal_x. *)
Lemma SRr_run_pi_tok_AJx : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJx; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* cgif YC80.v:122-140 (origin/ossv/recipes) over ajournal_x. *)
Lemma SRr_run_to_pi_tok_AJx : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJx; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* Mixed-write twins: the straight-line stretch may write, besides the bytes awr_byte admits (its frame, its own
   blocks), the program's own statics PST. The journal step is ajournal_x_exec_mixed above; otherwise
   cgif YC80.v:69-140 (origin/ossv/recipes) as the three lemmas above. *)
Lemma SRr_chain_pi_tok_AJxm : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_mixed segs B PST ARx LAWS segs_low PST_ok PST_nk) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJxm : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxm; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJxm : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST) ->
run_post_pi_tok_AJx W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxm; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End e.
End d.
