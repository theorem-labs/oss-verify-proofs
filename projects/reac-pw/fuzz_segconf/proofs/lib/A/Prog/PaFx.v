(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: made from lib/A/Prog/PaCall.v (cl_callS), PaNoChain.v (cl_callS_na, cl_callS_wide), PaCallPg.v (cl_callS_pg), PaArt.v (aj_art_at) and PaArtOwn.v (aj_art_own_at, aj_art_blk_at) for fuzz_command's program walk after statement pass 4 (CmdBase.v's apost_baseF): the relation fxrel between the FP state at a function's entry and the FP state a call returns (apost_baseF's two FP clauses), its reflexivity and transitivity and the rounding-mode-0 fact it carries; the lifts between apost_base and apost_baseF; the call rules for a callee whose post is apost_baseF and the steps through a runtime entry whose post is art_post at some FP state (with the bridge from the shared snprintf / sprintf post, lib/A/Rt/RtPFShared.v and RtPFCmd.v, to that form). Each proof is the original's with the FP-state existential added. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_command/lib/A/Prog/PaFx.v (origin/ossv/recipes 501c0d516c69) for reac-pw/fuzz_segconf's image A (fuzz_segconf.asan): module paths; csym -> ssym; CmdSyms, CmdPa -> SegSyms, SegPa; CmdBase -> SegPgBase SegBase. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegPa PaRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaNoChain PaArt PaArtOwn SegPgBase SegBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- (a) the FP relation of apost_baseF ---- *)
(* rounding mode 0 (frm = fcsr bits 5..7): the pre-condition clause of the printf-reaching statements and of the
   shared snprintf / sprintf contracts (frm0_entry) *)
Definition frm0 (fx : YK11.FPState) : Prop := Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0.
(* the FP state fx1 a call returns, against the FP state fx of the function's entry: apost_baseF's two FP clauses
   (CmdBase.v), with fx' := fx1 *)
Definition fxrel (fx fx1 : YK11.FPState) : Prop :=
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0).
Lemma fxrel_refl : forall fx : YK11.FPState, fxrel fx fx.
Proof. intros fx. split; [intros k _; reflexivity | left; reflexivity]. Qed.
Lemma fxrel_trans : forall fx fx1 fx2 : YK11.FPState, fxrel fx fx1 -> fxrel fx1 fx2 -> fxrel fx fx2.
Proof.
intros fx fx1 fx2 [R1 C1] [R2 C2]. split.
- intros k Hk. rewrite (R2 k Hk). exact (R1 k Hk).
- destruct C2 as [E2 | Z2]; [|right; exact Z2].
  destruct C1 as [E1 | Z1]; [left; rewrite E2; exact E1 | right; rewrite E2; exact Z1].
Qed.
(* rounding mode 0 at the entry (the statement's pre) or after the previous call is rounding mode 0 at the next call *)
Lemma fxrel_frm0 : forall fx fx1 : YK11.FPState, frm0 fx -> fxrel fx fx1 -> frm0 fx1.
Proof. intros fx fx1 H0 [_ [E | Z1]]; unfold frm0 in *; [rewrite E; exact H0 | exact Z1]. Qed.
(* the shared printf post (f registers but f10 kept, rounding mode 0) is the right disjunct *)
Lemma fxrel_of_frm0 : forall fx fx1 : YK11.FPState,
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) ->
frm0 fx1 -> fxrel fx fx1.
Proof. intros fx fx1 HR HZ. split; [exact HR | right; exact HZ]. Qed.
(* a symbolic state met by a restricted machine state at one FP state is met at any other FP state by the same
   registers, pc, memory and rom: st_ok reads the FP state only in its fregs and fcsr clauses, which mkst at the new
   FP state meets (the sup_chain_clear walk's scc_st_ok_fx, an earlier version of
   lib/A/Prog/sup_chain_clear_s2.v:107, which needs no relation between the two FP states). For an unrestricted
   `@mkst fx regs pc mem (seg_rom segs)` the core's YL05.st_ok_xfx is the same step. *)
Lemma st_ok_restrict_xfx : forall (fxa fxb : YK11.FPState) segs E ss (H : word -> bool) ms,
st_ok (fx := fxa) segs E ss (restrict H ms) -> ss_resv ss = None ->
st_ok (fx := fxb) segs E ss (restrict H (@mkst fxb (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms))).
Proof.
intros fxa fxb segs E ss H ms HS Hrv. hnf in HS |- *.
cbn [restrict mkst ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in HS |- *.
destruct HS as (_ & H2 & _ & _ & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [reflexivity|]. split; [rewrite Hrv; reflexivity|].
split; [reflexivity|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.
(* the same for st_ok_pi (the image-class walks' symbolic state, YP0l.v) over `restrict H (@mkst fx regs pc mem rom)`:
   the check_words_chain walk's st_ok_pi_fx (in an earlier version of the walk-tactic kit
   PaWalk.v), under a kit name *)
Lemma st_ok_pi_restrict_xfx : forall (fxa fxb : YK11.FPState) segs val E ss (H : word -> bool) regs pc mem rom,
st_ok_pi (fx := fxa) segs val E ss (restrict H (@mkst fxa regs pc mem rom)) ->
st_ok_pi (fx := fxb) segs val E ss (restrict H (@mkst fxb regs pc mem rom)).
Proof.
intros fxa fxb segs val E ss H regs pc mem rom HS.
unfold st_ok_pi in *.
destruct HS as (_ & H2 & H3 & H4 & _ & H6 & H7 & H8 & H9).
split; [reflexivity|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
split; [reflexivity|]. split; [exact H6|]. split; [exact H7|]. split; [exact H8 | exact H9].
Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- (b) apost_base and apost_baseF ---- *)
Section b.
Variable segs : list Segment.
(* a function whose callees keep the FP state: fx' := fx, the left disjunct *)
Lemma apost_baseF_of_base : forall B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (W' : world segs) c',
apost_base segs B STK FP regs ly S W mem md k Q W' c' -> apost_baseF segs B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros B STK FP regs ly S W mem md k Q W' c' (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HQ).
exists fx, ly', S', regs', mem', md'. split; [exact Hc|]. split; [intros k0 _; reflexivity|].
split; [left; reflexivity|]. split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.
(* the post proved at the FP state fx1 of a later point of the walk is the post at the entry's *)
Lemma apost_baseF_lift : forall (fx1 : YK11.FPState) B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (W' : world segs) c',
fxrel fx fx1 ->
apost_baseF (fx := fx1) segs B STK FP regs ly S W mem md k Q W' c' ->
apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros fx1 B STK FP regs ly S W mem md k Q W' c' H01 (fx2 & ly' & S' & regs' & mem' & md' & Hc & Hf1 & Hf2 & HJ & HP & HQ).
destruct (fxrel_trans fx fx1 fx2 H01 (conj Hf1 Hf2)) as [G1 G2].
exists fx2, ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact G1|]. split; [exact G2|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.
(* the post of a walk whose last FP change was a call that returned at fx1 and that calls no printf-reaching code
   after it: apost_base at fx1 *)
Lemma apost_base_liftF : forall (fx1 : YK11.FPState) B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (W' : world segs) c',
fxrel fx fx1 ->
apost_base (fx := fx1) segs B STK FP regs ly S W mem md k Q W' c' ->
apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q W' c'.
Proof.
intros fx1 B STK FP regs ly S W mem md k Q W' c' [G1 G2] (ly' & S' & regs' & mem' & md' & Hc & HJ & HP & HQ).
exists fx1, ly', S', regs', mem', md'. split; [exact Hc|]. split; [exact G1|]. split; [exact G2|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.
(* apost_baseF from its parts, at the return configuration of the F call rules below *)
Lemma apost_baseF_intro : forall (fx1 : YK11.FPState) B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) (W' : world segs)
ly' S' (regs' : bvmap 5 word) mem' md',
fxrel fx fx1 ->
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k ->
aregs_preserved regs regs' -> Q ly' S' W' regs' mem' md' ->
apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q W' (mkCfg (@mkst fx1 regs' (getr regs 1) mem' (seg_rom segs)) md').
Proof.
intros fx1 B STK FP regs ly S W mem md k Q W' ly' S' regs' mem' md' [G1 G2] HJ HP HQ.
exists fx1, ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact G1|]. split; [exact G2|].
split; [exact HJ|]. split; [exact HP | exact HQ].
Qed.
(* the two lifts through SRr: a walk segment proved at the FP state fx1 a call returned *)
Lemma srr_apost_baseF_lift : forall (fx1 : YK11.FPState) (W0 : world segs) (c : config) B STK FP (regs : bvmap 5 word) ly S
(W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
fxrel fx fx1 ->
SRr segs W0 c (apost_baseF (fx := fx1) segs B STK FP regs ly S W mem md k Q) ->
SRr segs W0 c (apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q).
Proof.
intros fx1 W0 c B STK FP regs ly S W mem md k Q H01 H. eapply SRr_mono; [exact H|].
intros W' c' _ HP. exact (apost_baseF_lift fx1 B STK FP regs ly S W mem md k Q W' c' H01 HP).
Qed.
Lemma srr_apost_base_liftF : forall (fx1 : YK11.FPState) (W0 : world segs) (c : config) B STK FP (regs : bvmap 5 word) ly S
(W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
fxrel fx fx1 ->
SRr segs W0 c (apost_base (fx := fx1) segs B STK FP regs ly S W mem md k Q) ->
SRr segs W0 c (apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q).
Proof.
intros fx1 W0 c B STK FP regs ly S W mem md k Q H01 H. eapply SRr_mono; [exact H|].
intros W' c' _ HP. exact (apost_base_liftF fx1 B STK FP regs ly S W mem md k Q W' c' H01 HP).
Qed.
(* After a call that returned at fx1 (the conclusion of an F call rule, section (c)): the rest of the walk is a
   segment proved at fx1, that is, a lemma of a closed section (so it holds at every ambient FP state) applied with
   (fx := fx1); its apost_baseF at fx1 is the function's apost_baseF at fx. *)
Lemma srr_after_callF : forall (W0 : world segs) (c : config) (raw : word)
(P : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
SRr segs W0 c (fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
  c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\ P ly2 S2 W2 regs2 mem2 md2) ->
(forall (fx1 : YK11.FPState) ly2 S2 (W2 : world segs) regs2 mem2 md2, wle W0 W2 -> fxrel fx fx1 ->
  P ly2 S2 W2 regs2 mem2 md2 ->
  SRr segs W2 (mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2)
    (apost_baseF (fx := fx1) segs B STK FP regs ly S W mem md k Q)) ->
SRr segs W0 c (apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q).
Proof.
intros W0 c raw P B STK FP regs ly S W mem md k Q H1 H2. eapply SRr_bind; [exact H1|].
intros W2 c2 Hle (fx1 & ly2 & S2 & regs2 & mem2 & md2 & H01 & -> & HP).
exact (srr_apost_baseF_lift fx1 W2 _ B STK FP regs ly S W mem md k Q H01 (H2 fx1 ly2 S2 W2 regs2 mem2 md2 Hle H01 HP)).
Qed.
(* the same when the segment after the call reaches no printf-reaching code: it proves apost_base at fx1 *)
Lemma srr_after_callF_base : forall (W0 : world segs) (c : config) (raw : word)
(P : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
SRr segs W0 c (fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
  c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\ P ly2 S2 W2 regs2 mem2 md2) ->
(forall (fx1 : YK11.FPState) ly2 S2 (W2 : world segs) regs2 mem2 md2, wle W0 W2 -> fxrel fx fx1 ->
  P ly2 S2 W2 regs2 mem2 md2 ->
  SRr segs W2 (mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2)
    (apost_base (fx := fx1) segs B STK FP regs ly S W mem md k Q)) ->
SRr segs W0 c (apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q).
Proof.
intros W0 c raw P B STK FP regs ly S W mem md k Q H1 H2. eapply SRr_bind; [exact H1|].
intros W2 c2 Hle (fx1 & ly2 & S2 & regs2 & mem2 & md2 & H01 & -> & HP).
exact (srr_apost_base_liftF fx1 W2 _ B STK FP regs ly S W mem md k Q H01 (H2 fx1 ly2 S2 W2 regs2 mem2 md2 Hle H01 HP)).
Qed.
(* after a runtime entry whose post is art_post at some fx1 (the F art steps, section (d)) *)
Lemma srr_after_artF : forall (W0 : world segs) (c : config) (raw : word)
(P : bvmap 5 word -> (word -> option byte) -> Model -> Prop)
B STK FP (regs : bvmap 5 word) ly S (W : world segs) mem md k
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
SRr segs W0 c (fun W2 c2 => W2 = W0 /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
  c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\ P regs2 mem2 md2) ->
(forall (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 -> P regs2 mem2 md2 ->
  SRr segs W0 (mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2)
    (apost_baseF (fx := fx1) segs B STK FP regs ly S W mem md k Q)) ->
SRr segs W0 c (apost_baseF (fx := fx) segs B STK FP regs ly S W mem md k Q).
Proof.
intros W0 c raw P B STK FP regs ly S W mem md k Q H1 H2. eapply SRr_bind; [exact H1|].
intros W2 c2 _ (-> & fx1 & regs2 & mem2 & md2 & H01 & -> & HP).
exact (srr_apost_baseF_lift fx1 W0 _ B STK FP regs ly S W mem md k Q H01 (H2 fx1 regs2 mem2 md2 H01 HP)).
Qed.
End b.

(* ---- (c) the call rules for a callee whose post is apost_baseF ---- *)
(* Each rule is the kit rule of the same name without F: the callee premise's post is apost_baseF unfolded (the
   callee returns at some fx1 with apost_baseF's FP clauses against the caller's fx; with raw := getr regsc 1 the
   callee's contract fits it by conversion, as it fits the original rule), and the continuation config carries
   that fx1 with fxrel fx fx1. *)
Section j.
Context {L : ptable ssym} {PI : PAImg L}.
#[local] Notation SEGS := (@pa_segs _ L PI).
Section l.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
(* PaCall.v's cl_callS *)
Lemma cl_callSF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0) /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ1 & HP & HK).
exists fx1, ly2, S2, regs2, mem2, md2. split; [exact (conj Hf1 Hf2)|]. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
(* PaNoChain.v's cl_callS_na: a callee stated with afn_pre_na *)
Lemma cl_callS_naF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
(afn_pre_na SEGS B STK1 lyc Sc W regsc memc mdc ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0) /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hcallee HF.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_na_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ1 & HP & HK).
exists fx1, ly2, S2, regs2, mem2, md2. split; [exact (conj Hf1 Hf2)|]. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_tok SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF].
Qed.
(* PaNoChain.v's cl_callS_wide: the core's ajournal_sub_wide composition *)
Lemma cl_callS_wideF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0) /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
(forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 ->
 forall a, inFP FP1 a -> sp0 - STK <= a < sp0 -> ~ (sp0 + o - STK1 <= a < sp0 + o) -> aview SEGS (w_H W2) mem2 a <> None) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF VIS.
eapply SRr_mono.
{ apply Hcallee. eapply (afn_pre_at SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1);
try eassumption. - rewrite Hra. exact Hraw. - unfold raZ. rewrite Hra. exact Hra4. - rewrite Hsp'. exact Hch. }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hf1 & Hf2 & HJ1 & HP & HK).
exists fx1, ly2, S2, regs2, mem2, md2. split; [exact (conj Hf1 Hf2)|]. split; [reflexivity|]. rewrite Hsp' in HJ1.
split; [| split; [exact HJ1 | split; [exact HP | exact HK]]].
change own with ([] ++ own). eapply (ajournal_sub_wide SEGS B LAWS pa_segs_low); [exact HJ | exact HJ1 | lia | lia | exact HF |].
intros a Hf Hw Hn. exact (VIS ly2 S2 W2 regs2 mem2 md2 HK a Hf Hw Hn).
Qed.
(* cl_callS_wideF under the statement image-B walks wrote first (dpgb_callS_wideF, the image-B
   descriptors_panel_get walk's lib/B/Prog/descriptors_panel_get_aux.v), verbatim, so that their copies swap to
   the kit by a pure rename: the same premises in the same order; the conclusion spells fxrel's two clauses after
   the configuration instead of bundling them first *)
Lemma callS_wideF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1
  (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
 SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
 (fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
   c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
   (forall kk : bv 5, bv_unsigned kk <> 10 -> Sem.reg_get (@fp_regs fx') kk = Sem.reg_get (@fp_regs fx) kk) /\
   (@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
   ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
(forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 ->
 forall a, inFP FP1 a -> sp0 - STK <= a < sp0 -> ~ (sp0 + o - STK1 <= a < sp0 + o) -> aview SEGS (w_H W2) mem2 a <> None) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx' : YK11.FPState) ly2 S2 regs2 mem2 md2,
 c2 = mkCfg (@mkst fx' regs2 raw mem2 (seg_rom SEGS)) md2 /\
 (forall kk : bv 5, bv_unsigned kk <> 10 -> Sem.reg_get (@fp_regs fx') kk = Sem.reg_get (@fp_regs fx) kk) /\
 (@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
 ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
 ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
 aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF VIS.
eapply SRr_mono.
{ exact (cl_callS_wideF W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
    HJ Hsp' Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF VIS). }
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & [Hf1 Hf2] & Hc & HJ0 & HJ1 & HP & HK).
exists fx1, ly2, S2, regs2, mem2, md2.
exact (conj Hc (conj Hf1 (conj Hf2 (conj HJ0 (conj HJ1 (conj HP HK)))))).
Qed.
(* PaCallPg.v's cl_callS_pg: the callee's footprint may hold the program's statics; from cl_callS_wideF as the
   original is from cl_callS_wide *)
Lemma cl_callS_pgF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 (o : Z) raw ch1
(K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
(afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2,
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0) /\
ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
(forall a, inFP FP1 a -> (inFP FP a /\ ((exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
(Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/
in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (mkCfg (mkst regsc pc memc (seg_rom SEGS)) mdc)
(fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
pose proof HSTK as (_ & _ & Hlo & Hlo2 & _).
pose proof (@pa_segs_low _ L PI) as Hlow. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (LOWFP : forall a, inFP FP1 a -> a < alloc_ceiling).
{ intros a Ha. destruct (HF a Ha) as [[_ [(b & m & Hb & Hab) | (_ & Himg)]] | (b & m & Hb & _ & Hab)].
  - pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & _). lia.
  - pose proof (Hlow a Himg). lia.
  - pose proof (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & _ & Hc & _). lia. }
assert (HWR : forall a, inFP FP1 a -> awr_byte SEGS B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a).
{ intros a Ha. destruct (HF a Ha) as [[Hfp [Hbl | Hpg]] | Htmp].
  - right; left. split; [exact Hfp | exact Hbl].
  - right; right; right; right. left. split; [exact Hfp | exact Hpg].
  - right; right; left. exact Htmp. }
assert (VIS : forall ly2 S2 W2 regs2 mem2 md2, K ly2 S2 W2 regs2 mem2 md2 ->
  forall a, inFP FP1 a -> sp0 - STK <= a < sp0 -> ~ (sp0 + o - STK1 <= a < sp0 + o) -> aview SEGS (w_H W2) mem2 a <> None).
{ intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (LOWFP a Ha). lia. }
exact (cl_callS_wideF W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
HJ Hsp Hal Hneg Hstk1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HWR VIS).
Qed.
End l.
End j.

(* ---- (d) the steps through a runtime entry whose post is art_post at some FP state ---- *)
Section a.
Variable segs : list Segment.
Variable B : asyms.
(* art_post (lib/A/Rt/RtDefs.v) at the FP state fx1 the entry returns, with fxrel fx fx1 *)
Definition art_postF (stk : Z) (ly : alayout) (S : astate) (W : world segs) (regs : bvmap 5 word)
(mem : word -> option byte) (md : Model) (E : Z -> Prop)
(Q : bvmap 5 word -> (word -> option byte) -> Prop) : world segs -> config -> Prop :=
fun W' c' => exists (fx1 : YK11.FPState), fxrel fx fx1 /\ art_post (fx := fx1) segs B stk ly S W regs mem md E Q W' c'.
(* the shared snprintf / sprintf post (RtPFShared.v sh_asnprintf_realizes: w := sn_len (n - 1) T,
   bs := sn_bytes (n - 1) T; RtPFCmd.v sh_asprintf_realizes: w := sp_len T, bs := sp_bytes T; r10 := |T|; the
   window stk := K) is art_postF with the written cells the destination [d, d + w) and Qr the value of a0 and the
   bytes at d. The scratch window is present after the call because it is present before (the contract's own
   premise) and the call keeps every present byte. *)
Lemma art_postF_of_pf : forall (stk : Z) ly S (W : world segs) (regs : bvmap 5 word) mem md (d w : Z) (bs : list Z) (r10 : Z)
(W' : world segs) (c' : config),
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
(W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 r10 /\
(forall i, 0 <= i < w -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) bs 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + w) ->
~ (spZ regs - stk <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)) ->
art_postF stk ly S W regs mem md (fun a => d <= a < d + w)
(fun regs' mem' => getr regs' 10 = w64 r10 /\
  forall i, 0 <= i < w -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) bs 0)) W' c'.
Proof.
intros stk ly S W regs mem md d w bs r10 W' c' Hscr0
  (-> & fx' & regs' & mem' & md' & -> & Hf1 & Hf2 & HAR & HP & Hsame & H10 & Hby & Hfr & Hpm).
exists fx'. split; [exact (fxrel_of_frm0 fx fx' Hf1 Hf2)|].
split; [reflexivity|]. exists regs', mem', md'.
split; [reflexivity|]. split; [exact HAR|]. split; [exact HP|]. split; [exact Hsame|].
split; [split; [exact H10 | exact Hby]|].
split; [intros a Ha Hs He; exact (Hfr a Ha He Hs)|].
split; [exact Hpm|].
intros a Ha. apply Hpm. apply Hscr0. exact Ha.
Qed.
Lemma srr_art_postF_of_pf : forall (stk : Z) ly S (W : world segs) (regs : bvmap 5 word) mem md (c : config)
(d w : Z) (bs : list Z) (r10 : Z),
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
SRr segs W c (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
c' = @cfg_at fx' segs (raZ regs) regs' mem' md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0 /\
AR segs B ly S W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 r10 /\
(forall i, 0 <= i < w -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) bs 0)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + w) ->
~ (spZ regs - stk <= a < spZ regs) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)) ->
SRr segs W c (art_postF stk ly S W regs mem md (fun a => d <= a < d + w)
(fun regs' mem' => getr regs' 10 = w64 r10 /\
  forall i, 0 <= i < w -> aview segs (w_H W) mem' (d + i) = Some (nth (Z.to_nat i) bs 0))).
Proof.
intros stk ly S W regs mem md c d w bs r10 Hscr0 H. eapply SRr_mono; [exact H|].
intros W' c' _ HP. exact (art_postF_of_pf stk ly S W regs mem md d w bs r10 W' c' Hscr0 HP).
Qed.
Hypothesis LAWS : AR_laws segs B.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* PaArtOwn.v's aj_art_own_at: the entry's cells are bytes the caller's journal may write (the snprintf / sprintf
   destination in the caller's side-stack frame or footprint) *)
Lemma aj_art_own_atF : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> awr_byte segs B STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_postF stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx1 & Hfx & -> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists fx1, regs2, mem2, md2. split; [exact Hfx|].
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
assert (Hfr' : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha Hw He. apply (Hfr a Ha); [unfold ascratch_stk; rewrite Hsp; exact Hw | exact He]. }
split.
{ eapply (ajournal_after_write segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k mem2 md2
    (fun a => Eb a \/ (sp0 + o - stk <= a < sp0 + o)) Sc own HJ).
  - intros a Ha Hna. apply (Hfr' a Ha); intros H'; apply Hna; [right | left]; exact H'.
  - exact Hpres2.
  - exact Hsame.
  - intros a [Ha | Ha]; left; [exact (HEb a Ha) | left; lia].
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact HQ|]. exact Hfr'.
Qed.
Hypothesis errno_low : api_env segs B.
(* PaArt.v's aj_art_at: the entry writes only its scratch window and cells of the errno cell *)
Lemma aj_art_atF : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k (o : Z) raw
(Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
(forall a, Eb a -> as_errno B <= a < as_errno B + 4) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_postF stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw Qr
HJ Hsp Hal Hneg Hstk Hbud Hraw HEb HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (ASTACK = 16384) as Has by reflexivity.
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx1 & Hfx & -> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists fx1, regs2, mem2, md2. split; [exact Hfx|].
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal segs B stk (spZ regsT) [] lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
{ eapply (call_effect_journal segs B LAWS segs_low errno_low stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
(fun _ => False) [] [] 0);
[exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr | exact HAR
| | reflexivity | lia | lia | lia | intros a [] | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
- intros a H0 _ _ H3 _. apply (Hfr a H0).
+ intros Hs. apply H3. left. exact Hs.
+ intros He. apply H3. right. exact (HEb a He).
- unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia]. }
pose proof (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT) []
[] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as HJ2.
rewrite app_nil_l, Z.add_0_r in HJ2. exact HJ2. }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.
(* PaArtOwn.v's aj_art_blk_at: the entry's cells lie inside one live block the call may write (the sprintf target
   on the heap) *)
Lemma aj_art_blk_atF : forall stk (Eb : Z -> Prop) pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k (o : Z) raw bq nq (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
In (bq, nq) (ablocks B lyc Sc) -> (forall a, Eb a -> bq <= a < bq + req_size nq) ->
(forall a, bq <= a < bq + req_size nq ->
  (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr segs W (cfg_at segs pc regsT memT mdc) (art_postF stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr segs W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom segs)) mdc)
(fun W2 c2 => W2 = W /\ exists (fx1 : YK11.FPState) regs2 mem2 md2, fxrel fx fx1 /\
  c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom segs)) md2 /\
  ajournal segs B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
   aview segs (w_H W) mem2 a = aview segs (w_H W) memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw bq nq Qr
  HJ Hsp Hal Hneg Hstk Hbud Hraw Hbq HEb Hcov HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (fx1 & Hfx & -> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists fx1, regs2, mem2, md2. split; [exact Hfx|].
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal segs B stk (spZ regsT) (ablocks_fp [(bq, nq)]) lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
  { eapply (call_effect_journal segs B LAWS segs_low errno_low stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
      Eb (ablocks_fp [(bq, nq)]) [] 0);
    [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr
    | exact HAR | | reflexivity | lia | lia | lia | | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
    - intros a H0 _ _ H3 H4. apply (Hfr a H0); [intros Hs; apply H3; left; exact Hs | exact H4].
    - unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
      repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia].
    - intros a Ha. exists bq, nq. split; [left; exact Hbq|]. split; [exact (HEb a Ha)|].
      left. pose proof (HEb a Ha) as Hr. replace a with (bq + (a - bq)) by lia.
      apply (inFP_ablocks_fp [(bq, nq)] bq nq (a - bq)); [left; reflexivity | lia]. }
  pose proof (ajournal_sub_tok segs B LAWS segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT)
    (ablocks_fp [(bq, nq)]) [] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)) as HJ2.
  rewrite app_nil_l, Z.add_0_r in HJ2. apply HJ2.
  intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p' & n' & Hpn & Hr).
  destruct Hpn as [Hpn | []]. injection Hpn as <- <-. exact (Hcov a Hr). }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.
End a.
End c.
