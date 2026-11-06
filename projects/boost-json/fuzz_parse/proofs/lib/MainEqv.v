(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Scfg PropExec ShapeAlg SReach RegsEquivM.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import MState Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem3Run06config69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~j48realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRegsEquivM~~~~~~na7cfg_eqvj44TSet37Corelib7Numbers7BinNumss84Npos35stdpp9bitvectorbdefinitionsu82bv37Corelib4Init9Datatypeshga6optionhga4None3h5LinuxProcessSemantics5Riscv7Preludehj45bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hm32MS69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hq66fp_csrhq67fp_regshq64mkstna6mkR_ofna6ms_eqv37Corelib4Init5Logicih01Ihq64getru82BVu84BvWfih02eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ik33mkRhga4consu87Z_to_bvhga3nil37Corelib5Lists7ListDefipf3nth46Stdlib6ZArith6BinInt1Zird6to_natu8bbv_unsignedhga4list3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeiv57Segment" s.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section Eqv.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable segs : ltac2:(zQ "20!iud!jia@1$0$1").
  Context {SC : StepCfg}.

  (* [comment removed for export] *)
  Theorem realizes_eqv : ltac2:(zQ "40!ic!mf!r7!s1>1c$0>1T$3>0@4$1?4segs?2SC^2^1>2c'$0>0@2$2^4^1@4$1?4segs?2SC^2^4").
  Proof.
    intros c T H. induction H as [c I evs nx T i0 Hnode Hcont IH | c Hh | c T T' H IH Heq]; intros c' Heqv.
    - (* [comment removed for export] *)
      destruct Hnode as [N1 N2].
      set (I' := { p : I * config | sstep_cfg segs the_scfg c' (evs (fst p)) (SNext (snd p)) /\ cfg_eqv (nx (fst p)) (snd p) }).
      assert (X0 : forall i, exists c2, sstep_cfg segs the_scfg c' (evs i) (SNext c2) /\ cfg_eqv (nx i) c2).
      { intros i. ndestruct (sstep_scfg_cfg_eqv segs the_scfg c c' (evs i) (SNext (nx i)) Heqv (N1 i)) as (X' & Hs & HX).
        destruct X' as [c2|]; cbn in HX; [|contradiction]. exists c2. auto. }
      ndestruct (X0 i0) as (c20 & Hs0 & He0).
      apply (rz_conseq segs _ (t_alt (fun p : I' => t_emit (evs (fst (proj1_sig p))) (T (fst (proj1_sig p)))))).
      + apply (rz_node segs c' I' (fun p => evs (fst (proj1_sig p))) (fun p => snd (proj1_sig p))
                 (fun p => T (fst (proj1_sig p))) (exist _ (i0, c20) (conj Hs0 He0))).
        * split.
          -- intros [[i c2] [Hs He]]. cbn. exact Hs.
          -- intros e st Hst.
             ndestruct (sstep_scfg_cfg_eqv segs the_scfg c' c e st (cfg_eqv_sym c c' Heqv) Hst) as (X' & Hs & HX).
             ndestruct (N2 e X' Hs) as (i & -> & ->).
             destruct st as [c2|]; cbn in HX; [|contradiction].
             exists (exist _ (i, c2) (conj Hst (cfg_eqv_sym _ _ HX))). cbn. auto.
        * intros [[i c2] [Hs He]]. cbn. apply (IH i). exact He.
      + (* [comment removed for export] *)
        intros tr. split.
        * intros [[[i c2] [Hs He]] Htr]. cbn in Htr. exists i. exact Htr.
        * intros [i Htr]. ndestruct (X0 i) as (c2 & Hs & He). exists (exist _ (i, c2) (conj Hs He)). cbn. exact Htr.
    - apply rz_halt. destruct Heqv as [_ Hmo]. rewrite <- Hmo. exact Hh.
    - eapply rz_conseq; [apply IH; exact Heqv | exact Heq].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
End Eqv.

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma mkst_as_MS : ltac2:(zQ "b1!u1!hg5!hi2!hic!hla!hq0!hu1!hub!hv6!hve!ig7&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1R@2$4@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>1m~0>3rom~0@2$a@5$8?2fx^4^3^2^1@7$5@1$9^4@1$7?2fx^3@1$6?2fx@1$3@1$1@1$0#k0^2^1").
Proof.
  intros R pc m rom. unfold mkst, MS. split; [apply mkR_of_eqv|]. cbn. repeat split; try apply fregs_eqv_refl.
Qed.

(* [comment removed for export] *)
Lemma mkR_of_getr : ltac2:(zQ "a0!u1!ii4!ii9!ij1!ij6!hla!hg5!ijd!inf!hve>1R@2$5@1$0#5@1$6@1$0#k0@3$7@2$5@1$0#5@1$6@1$0#k0@1$9^1@hf$8@2$2^1@3$3@1$0#5+1Kv$1@2$4@1$0#5+1@2$2^1@3$3@1$0#5+2Kv$1@2$4@1$0#5+2@2$2^1@3$3@1$0#5+3Kv$1@2$4@1$0#5+3@2$2^1@3$3@1$0#5+4Kv$1@2$4@1$0#5+4@2$2^1@3$3@1$0#5+5Kv$1@2$4@1$0#5+5@2$2^1@3$3@1$0#5+6Kv$1@2$4@1$0#5+6@2$2^1@3$3@1$0#5+7Kv$1@2$4@1$0#5+7@2$2^1@3$3@1$0#5+8Kv$1@2$4@1$0#5+8@2$2^1@3$3@1$0#5+9Kv$1@2$4@1$0#5+9@2$2^1@3$3@1$0#5+aKv$1@2$4@1$0#5+a@2$2^1@3$3@1$0#5+bKv$1@2$4@1$0#5+b@2$2^1@3$3@1$0#5+cKv$1@2$4@1$0#5+c@2$2^1@3$3@1$0#5+dKv$1@2$4@1$0#5+d@2$2^1@3$3@1$0#5+eKv$1@2$4@1$0#5+e@2$2^1@3$3@1$0#5+fKv$1@2$4@1$0#5+f@2$2^1@3$3@1$0#5+h0Kv$1@2$4@1$0#5+h0@2$2^1@3$3@1$0#5+h1Kv$1@2$4@1$0#5+h1@2$2^1@3$3@1$0#5+h2Kv$1@2$4@1$0#5+h2@2$2^1@3$3@1$0#5+h3Kv$1@2$4@1$0#5+h3@2$2^1@3$3@1$0#5+h4Kv$1@2$4@1$0#5+h4@2$2^1@3$3@1$0#5+h5Kv$1@2$4@1$0#5+h5@2$2^1@3$3@1$0#5+h6Kv$1@2$4@1$0#5+h6@2$2^1@3$3@1$0#5+h7Kv$1@2$4@1$0#5+h7@2$2^1@3$3@1$0#5+h8Kv$1@2$4@1$0#5+h8@2$2^1@3$3@1$0#5+h9Kv$1@2$4@1$0#5+h9@2$2^1@3$3@1$0#5+haKv$1@2$4@1$0#5+ha@2$2^1@3$3@1$0#5+hbKv$1@2$4@1$0#5+hb@2$2^1@3$3@1$0#5+hcKv$1@2$4@1$0#5+hc@2$2^1@3$3@1$0#5+hdKv$1@2$4@1$0#5+hd@2$2^1@3$3@1$0#5+heKv$1@2$4@1$0#5+he@2$2^1@3$3@1$0#5+hfKv$1@2$4@1$0#5+hf").
Proof. intros R. reflexivity. Qed.

(* [comment removed for export] *)
Lemma getr_mkR : ltac2:(zQ "b0!u1!hg5!io6!ioe!ip8!ijd!ir6!inf!ii9!it5!itf>2x1@1$1@1$0#k0>2x2@1$1@1$0#k0>2x3@1$1@1$0#k0>2x4@1$1@1$0#k0>2x5@1$1@1$0#k0>2x6@1$1@1$0#k0>2x7@1$1@1$0#k0>2x8@1$1@1$0#k0>2x9@1$1@1$0#k0>3x10@1$1@1$0#k0>3x11@1$1@1$0#k0>3x12@1$1@1$0#k0>3x13@1$1@1$0#k0>3x14@1$1@1$0#k0>3x15@1$1@1$0#k0>3x16@1$1@1$0#k0>3x17@1$1@1$0#k0>3x18@1$1@1$0#k0>3x19@1$1@1$0#k0>3x20@1$1@1$0#k0>3x21@1$1@1$0#k0>3x22@1$1@1$0#k0>3x23@1$1@1$0#k0>3x24@1$1@1$0#k0>3x25@1$1@1$0#k0>3x26@1$1@1$0#k0>3x27@1$1@1$0#k0>3x28@1$1@1$0#k0>3x29@1$1@1$0#k0>3x30@1$1@1$0#k0>3x31@1$1@1$0#k0>1r@1$1@1$0#5@3$5@1$1@1$0#k0@2$8@hf$7^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5^4^3^2^1@4$6@1$1@1$0#k0@1$9@2$a@1$0#5^1@3$2@1$1@1$0#k0@2$3@1$0#k0Z@3$2@1$1@1$0#k0^i0@3$2@1$1@1$0#k0^hf@3$2@1$1@1$0#k0^he@3$2@1$1@1$0#k0^hd@3$2@1$1@1$0#k0^hc@3$2@1$1@1$0#k0^hb@3$2@1$1@1$0#k0^ha@3$2@1$1@1$0#k0^h9@3$2@1$1@1$0#k0^h8@3$2@1$1@1$0#k0^h7@3$2@1$1@1$0#k0^h6@3$2@1$1@1$0#k0^h5@3$2@1$1@1$0#k0^h4@3$2@1$1@1$0#k0^h3@3$2@1$1@1$0#k0^h2@3$2@1$1@1$0#k0^h1@3$2@1$1@1$0#k0^h0@3$2@1$1@1$0#k0^f@3$2@1$1@1$0#k0^e@3$2@1$1@1$0#k0^d@3$2@1$1@1$0#k0^c@3$2@1$1@1$0#k0^b@3$2@1$1@1$0#k0^a@3$2@1$1@1$0#k0^9@3$2@1$1@1$0#k0^8@3$2@1$1@1$0#k0^7@3$2@1$1@1$0#k0^6@3$2@1$1@1$0#k0^5@3$2@1$1@1$0#k0^4@3$2@1$1@1$0#k0^3@3$2@1$1@1$0#k0^2@1$4@1$1@1$0#k0@2$3@1$0#k0Z").
Proof.
  intros. ndestruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [vm_compute; reflexivity|]). lia.
Qed.
End FPX1.
(* [comment removed for export] *)
