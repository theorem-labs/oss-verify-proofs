(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the part of proofs/cgif/cgif_file_fuzzer/lib/YC20.v that carries no cgif name, as fuzz_grant's lib/A/Prog/GrantBase.v (a working branch 4a980cd5011) and fuzz_identity's lib/A/Prog/IdentBase.v (a working branch ea5560a967b) carry it, with only the unit's module prefix changed, for libreac/fuzz_boxreg: the read-only range, the frame object and the shape of a call's post-condition. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition in_roP (segs : list Segment) (rlo rhi : Z) (a : Z) : Prop :=
(exists s, In s segs /\ seg_writable s = false /\ Z.of_N (seg_base s) <= a < Z.of_N (seg_base s) + Z.of_N (seg_size s))
\/ (rlo <= a < rhi).
Definition arodata_okP (segs : list Segment) (rlo rhi : Z) (B : asyms) (rd : reader) : Prop :=
forall a, in_roP segs rlo rhi a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
rd a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)).
Class ro_below_ofl (segs : list Segment) (rlo rhi : Z) {SK : YI16.sink_head} : Prop :=
ro_below_ofl_at : forall a, in_roP segs rlo rhi a -> a < YI16.sk_ofl_head.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable segs : list Segment.
Variables rlo rhi : Z.
Hypothesis relro_img : forall a, rlo <= a < rhi -> in_img segs a.
Context {RO : ro_below_ofl segs rlo rhi}.
Lemma ro_spares : forall FP a, in_roP segs rlo rhi a -> fp_spares FP a.
Proof. intros FP a Hro. apply fp_spares_below. exact (@ro_below_ofl_at segs rlo rhi SK RO a Hro). Qed.
Lemma arodata_ok_journalP : forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal segs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
arodata_okP segs rlo rhi B (aview segs (w_H W) mem) -> arodata_okP segs rlo rhi B (aview segs (w_H W') mem').
Proof.
intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | exact (ro_spares FP a Hro)].
destruct Hro as [(s & Hs & _ & Hr) | Hgot]; [exists s; split; [exact Hs | exact Hr]|].
exact (relro_img a Hgot).
Qed.
End e.
End d.
Section j. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section l.
Variable segs : list Segment.
Definition afobj (B : asyms) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte) (p n : Z) : Prop :=
(exists cid pos, In (cid, pos) (frames S) /\ 0 <= cid /\ frame_addr ly cid pos mod 8 = 0 /\
frame_addr ly cid pos <= p /\ p + n <= frame_addr ly cid pos + fs_frame_bytes cid) /\
p mod 8 = 0 /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF p n.
Definition apost_base (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists ly' S' regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
(* apost_base for a function that calls the snprintf wrapper (reac_boxreg_declare, reac_boxreg_set_name): the
   return configuration carries SOME fx' whose f registers equal the entry's except f10 and whose fcsr has rounding
   mode 0, or is the entry's own fcsr (a Theorem Labs lane's shared snprintf post, a working branch
   401616133a7 FMsnprintfShared.v:142-145, gives rounding mode 0; a path that never reaches the wrapper, e.g.
   set_name's two early returns, takes fx' := fx). The relation is reflexive and transitive, so a function with
   several calls composes. AR and the journal take no FP state, so the rest is apost_base's. The f-register clause
   reads fp_regs through getr, which returns 0 for register 0 (PropExec.v:28), so f0 is NOT covered by it; boxreg
   needs no f0 fact, since neither image's LLVMFuzzerTestOneInput holds an FP instruction (measured) and the
   compositions are proved for any float state. fuzz_disco's copy of this shape reads Sem.reg_get instead
   (a Theorem Labs lane, 2026-10-29 05:55Z). *)
Definition apost_baseF (B : asyms) (STK : Z) (FP : list (Z * Z)) (regs : bvmap 5 word) ly S W mem md (k : Z)
(Q : alayout -> astate -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
: world segs -> config -> Prop :=
fun W' c' => exists (fx' : YK11.FPState) ly' S' regs' mem' md',
c' = mkCfg (@mkst fx' regs' (getr regs 1) mem' (seg_rom segs)) md' /\
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0) /\
ajournal segs B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k /\
aregs_preserved regs regs' /\ Q ly' S' W' regs' mem' md'.
(* The FP relation apost_baseF states, as one name: f registers equal except f10, and the fcsr the entry's or at
   rounding mode 0. Reflexive and transitive, so several calls compose against the ENTRY fx. *)
Definition fxr (fx' : YK11.FPState) : Prop :=
(forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx') k = Sem.reg_get (@fp_regs fx) k) /\
(@fp_csr fx' = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx')) 5) 7 = 0).
Lemma fxr_refl : fxr fx.
Proof. split; [reflexivity | left; reflexivity]. Qed.
(* The continuation lemma for a call whose post is apost_baseF's, i.e. a call of reac_boxreg_declare or
   reac_boxreg_set_name. a Theorem Labs lane's srr_fx_continue (lib/A/Rt/FMsnprintfSx.v) does NOT fit there: it asks the
   continuation for rounding mode 0 at every returned state, which apost_baseF's left disjunct does not give
   (a Theorem Labs lane, 05:2xZ). One apply per cross-call site; the caller continues at fx' with its `forall fx`
   contracts. REST is the rest of the callee's post, which never mentions the ambient fx. *)
Lemma apost_baseF_continue : forall (W : world segs) (c : config) (ra : Z)
  (REST : YK11.FPState -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
  (Q : world segs -> config -> Prop),
  SRr segs W c
    (fun W' c' => W' = W /\ exists (fx' : YK11.FPState) regs' mem' md',
       c' = @cfg_at fx' segs ra regs' mem' md' /\ fxr fx' /\ REST fx' regs' mem' md') ->
  (forall (fx' : YK11.FPState) regs' mem' md',
     fxr fx' -> REST fx' regs' mem' md' ->
     SRr segs W (@cfg_at fx' segs ra regs' mem' md') Q) ->
  SRr segs W c Q.
Proof.
intros W c ra REST Q H1 H2. eapply SRr_bind; [exact H1|].
intros W' c' Hle (-> & fx' & regs' & mem' & md' & -> & Hfx & HR). exact (H2 fx' regs' mem' md' Hfx HR).
Qed.
End l.
End j.
