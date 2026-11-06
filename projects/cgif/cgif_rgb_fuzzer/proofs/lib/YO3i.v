(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK15 YN06 YN02 YQ0b YO3v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YO04 YO2f
YO0f YO07 YO0a YO29 YO00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Section a.
Context {rc : YN05.RunCeil}.
Hypothesis AMH : forall fx : YK11.FPState, @alloc_meta_hyp fx rc src2_msyms.
Hypothesis MSH : forall fx : YK11.FPState, @malloc_small_hyp fx rc src2_msyms.
Hypothesis NTF : forall fx : YK11.FPState, @ntfree_hyp fx rc src2_msyms.
Lemma src2_calloc_vacuous {fx : YK11.FPState} : calloc_realizes src2_msyms (MRx src2_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
Definition src2_API : AllocAPI src2_msyms :=
{| aa_MR := MRx src2_msyms;
aa_laws := MRx_laws src2_msyms;
aa_init := fun mem md sec H Hs => MRx_init src2_msyms mem md sec src2_syms_ok H Hs;
aa_malloc := fun fx => @src2_malloc_realizes fx rc (AMH fx) (MSH fx);
aa_free := fun fx => @src2_free_realizes fx rc (NTF fx);
aa_free_null := fun fx => @src2_free_null fx;
aa_calloc := fun fx => @src2_calloc_vacuous fx |}.

End a.
