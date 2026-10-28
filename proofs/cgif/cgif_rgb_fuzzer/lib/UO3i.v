(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK15 YN06 YN02 YQ0b YO3v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YO04 YO2f
UO0f UO07 UO0a YO29 YO00.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Unset Lia Cache. Unset Nia Cache.
Section a.
Context {rc : YN05.RunCeil}.
Hypothesis AMH : forall fx : YK11.FPState, @alloc_meta_hyp fx rc ubs2_msyms.
Hypothesis MSH : forall fx : YK11.FPState, @malloc_small_hyp fx rc ubs2_msyms.
Hypothesis NTF : forall fx : YK11.FPState, @ntfree_hyp fx rc ubs2_msyms.
Lemma ubs2_calloc_vacuous {fx : YK11.FPState} : calloc_realizes ubs2_msyms (MRx ubs2_msyms).
Proof. intros pc L A regs mem md m n Hpc. cbn in Hpc. discriminate Hpc. Qed.
Definition ubs2_API : AllocAPI ubs2_msyms :=
{| aa_MR := MRx ubs2_msyms;
aa_laws := MRx_laws ubs2_msyms;
aa_init := fun mem md sec H Hs => MRx_init ubs2_msyms mem md sec ubs2_syms_ok H Hs;
aa_malloc := fun fx => @ubs2_malloc_realizes fx rc (AMH fx) (MSH fx);
aa_free := fun fx => @ubs2_free_realizes fx rc (NTF fx);
aa_free_null := fun fx => @ubs2_free_null fx;
aa_calloc := fun fx => @ubs2_calloc_vacuous fx |}.

End a.
