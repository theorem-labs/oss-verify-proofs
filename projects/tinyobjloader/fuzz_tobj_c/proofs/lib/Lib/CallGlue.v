(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "sprop"; "ss_next"; "valuation"; "ss_facts"; "holds"; "sprop_below"; "agree_below"; "sobj"; "@Corelib.Init.Datatypes"; "list"; "Some"; "option"; "bool"; "true"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "@Corelib.Lists.ListDef"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "lf_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "etriple"; "triple"; "world"; "assn"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "apply_xforms"; "xform"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Stdlib.Lists.List"; "forallb"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "add_facts"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "entails_fr"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "rho_absorb"; "rho_sub"; "wsub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "call_check"; "import_post"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG SymSummary SymObj Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CfgGlue ObjXform.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section CG.
Variable segs : list Segment.

Lemma xforms_facts : ltac2:(tb__ "0|0|
S9S19A1S0S0SeSbS0A1S18R2R3A2SaS0R1A2A3SeS9S1A1S4R2A1S4R3A1A3F_;FS';FS;Fxs;").
Proof using .
  induction xs as [|x r IH]; intros S S' H; cbn [apply_xforms] in H.
  - injection H as <-. reflexivity.
  - destruct (apply_xform S x) as [S1|] eqn:E; [|discriminate].
    rewrite (IH _ _ H). destruct x; cbn [apply_xform] in E.
    + unfold split_obj_at in E. destruct (nth_error (ss_objs S) i); [|discriminate].
      destruct (_ && _)%bool; [|discriminate]. destruct (obj_split s mid) as [[o1 o2]|]; [|discriminate].
      injection E as <-. reflexivity.
    + unfold merge_objs_at in E. destruct (nth_error (ss_objs S) i); [|discriminate].
      destruct (nth_error (ss_objs S) (Datatypes.S i)); [|discriminate].
      destruct (sitv _ _) as [[l1 ?]|]; [|discriminate]. destruct (sitv _ _) as [[? h2]|]; [|discriminate].
      destruct (_ <? _); [|discriminate]. destruct (obj_merge s s0); [|discriminate]. injection E as <-. reflexivity.
    + unfold rebase_obj_at in E. destruct (nth_error (ss_objs S) i); [|discriminate].
      destruct (rebase_obj _ _); [|discriminate]. injection E as <-. reflexivity.
    + destruct (select_ok _ _); [|discriminate]. injection E as <-. reflexivity.
Qed.

Theorem call_path : ltac2:(tb__ "0|2|
S3OF_;S16OF_;S9S1bA1S1aOF_;F_;M0G0S0S0S0S9S19A1S23S9S8A1M1S9S12A1S17S3SeSbS0A1S18R9R6A2SaS0R8A2A3SeSbG1A1S20R9R8R6A3SaG1R5A2A3SeScS24RaR9R7R6R5A5SdA3SeScS1cS1S6S2RbA1A1S4RcA1A3SdA3S3R12R1A1S15Vsegs;R12SfVsegs;R11RdR2A4S10Vsegs;R10S2RdA1R2R9A5A4F_;Frho1;S1eS11S1S5R7A1S4RfA1A3R14S22S21R8RbR2A3RcA2A1F_;Fms;S12S3S1dS12R2RbA3S7S2R11A1RaR2A3S11S1S5R3A1S4R13A1A3S15Vsegs;R17SfVsegs;R15S25R10S2R12A1S13R5A1S2R13A1RfA5R4A4RdA4F_;F_;F_;Frho';FL;S15Vsegs;R13SfVsegs;R12R10R8A4R9A4F_;F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;Fxs;FPre;FCX;FC;FK';FK;Fok;FPR;").
Proof using .
  intros PR ok K K' C CX Pre xs s R Posts Q rho Hx He Hchk Hfb Hsum HPR Hcont.
  apply triple_facts. intros HF.
  eapply triple_xforms; [exact Hx|].
  apply (call_sound_P segs (fun r => PR r) ok K K' CX Pre s R Posts Q rho He Hchk Hsum).
  - intros ms. apply HPR. exact HF.
  - intros L rho' HinL Hag. apply Hcont; [exact HinL | exact Hag |].
    apply Forall_forall. intros p Hp.
    apply (holds_agree (ss_next CX) rho rho' p Hag (proj1 (forallb_forall _ _) Hfb p Hp)).
    exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Theorem ecall_path : ltac2:(tb__ "0|2|
S3OF_;S9S1bA1S1aOF_;F_;M0G0S0S0S0S9S19A1S23S9S8A1M1S9S12A1S16OF_;S3SeSbS0A1S18R9R6A2SaS0R8A2A3SeSbG1A1S20R9R8R6A3SaG1R5A2A3SeScS24RaR9R7R6R5A5SdA3SeScS1cS1S6S2RbA1A1S4RcA1A3SdA3S3R11R1A1S14Vsegs;SfVsegs;R11RdR2A4S10Vsegs;R10S2RdA1R2R9A5A3F_;Frho1;S1eS11S1S5R7A1S4RfA1A3R13S22S21R8RbR2A3RcA2A1F_;Fms;S12S3S1dS12R2RbA3S7S2R11A1RaR2A3S11S1S5R3A1S4R13A1A3S14Vsegs;SfVsegs;R15S25R10S2R12A1S13R5A1S2R13A1RfA5R4A4RdA3F_;F_;F_;Frho';FL;S14Vsegs;SfVsegs;R12R10R8A4R9A3F_;F_;F_;F_;F_;F_;F_;Frho;FQ;FPosts;FR;Fs;Fxs;FPre;FCX;FC;FK';FK;FPR;").
Proof using .
  intros PR K K' C CX Pre xs s R Posts Q rho Hx He Hchk Hfb Hsum HPR Hcont.
  apply etriple_facts. intros HF.
  eapply etriple_xforms; [exact Hx|].
  apply (call_complete_P segs (fun r => PR r) K K' CX Pre s R Posts Q rho He Hchk Hsum).
  - intros ms. apply HPR. exact HF.
  - intros L rho' HinL Hag. apply Hcont; [exact HinL | exact Hag |].
    apply Forall_forall. intros p Hp.
    apply (holds_agree (ss_next CX) rho rho' p Hag (proj1 (forallb_forall _ _) Hfb p Hp)).
    exact (proj1 (Forall_forall _ _) HF p Hp).
Qed.

Theorem post_path : ltac2:(tb__ "0|0|
S16OF_;S9S1bA1S1aOF_;F_;S0S0S9S1A1S9S19A1S3S17SeScS1cS1S6S2R6A1A1R4A3SdA3SeSbS0A1S18S1fR5R7A2R4A2SaS0R6A2A3S11S1S5R4A1R6A3S15Vsegs;RbSfVsegs;RaR8R5A4R4A4S15Vsegs;RcSfVsegs;RbRaR6A4R5A4F_;F_;F_;F_;FQ;Frho;Fxs;FF;FT';FT;FK;Fok;").
Proof using .
  intros ok K T T' F xs rho Q Hb Hx HF HT.
  eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w [Hsm Hk]. eapply SP_xforms; [exact Hx|]. split; [|exact Hk].
  apply smatch_add_facts; [exact Hsm | exact HF | exact Hb].
Qed.

Theorem epost_path : ltac2:(tb__ "0|0|
S9S1bA1S1aOF_;F_;S0S0S9S1A1S9S19A1S3S16OF_;SeScS1cS1S6S2R6A1A1R4A3SdA3SeSbS0A1S18S1fR5R7A2R4A2SaS0R6A2A3S11S1S5R4A1R6A3S14Vsegs;SfVsegs;RaR8R5A4R4A3S14Vsegs;SfVsegs;RbRaR6A4R5A3F_;F_;F_;F_;FQ;Frho;Fxs;FF;FT';FT;FK;").
Proof using .
  intros K T T' F xs rho Q Hb Hx HF HT.
  eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w [Hsm Hk]. eapply SP_xforms; [exact Hx|]. split; [|exact Hk].
  apply smatch_add_facts; [exact Hsm | exact HF | exact Hb].
Qed.
End CG.
