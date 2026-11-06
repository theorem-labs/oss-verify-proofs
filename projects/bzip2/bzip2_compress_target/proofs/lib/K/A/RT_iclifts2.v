(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts RT_facts0 I_consts I_qck R_m2s R_isPoisoned I_lift TopA_iodefs RT_io I_memcmpw I_memcmp I_lift3 RT_iclifts.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_artfacts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_icfacts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_consts.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_qck.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_isPoisoned.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_iodefs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_io.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_memcmpw.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_memcmp.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.I_lift3.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iclifts.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_icells_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m /\ m2s_cells m.
Proof.
  intros Σ m HA. cbn [ART RTA] in HA.
  pose proof (ART_consts Σ m HA) as (_ & (_ & G2 & _) & _ & MC & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof MC as (M1 & M2 & M3).
  pose proof (rta_io Σ m HA) as IO.
  split; [|exact MC]. unfold icells_cmp.
  split; [exact (ro_of_rw _ _ _ G2)|].
  split; [exact (ro_head _ _ _ _ (ro_of_rw _ _ _ M1))|].
  split; [exact (io_ro_at m IO 0xceb60 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  exact (io_ro_at m IO 0x168166 _ ltac:(io_in)).
Qed.

Theorem rta_memcmp : memcmp_icontract RTA.
Proof. exact (memcmp_lift RTA rta_art_facts rip_proof rta_icells_cmp rta_shw). Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface RT_state RT_rep RT_facts RT_artfacts RT_icfacts
  RT_facts0 I_consts I_qck R_m2s R_isPoisoned I_lift TopA_iodefs RT_io I_memcmpw I_memcmp I_lift3 RT_iclifts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_icells_cmp : forall Σ m, ART RTA Σ m -> icells_cmp m /\ m2s_cells m.
Proof.
  intros Σ m HA. cbn [ART RTA] in HA.
  pose proof (ART_consts Σ m HA) as (_ & (_ & G2 & _) & _ & MC & _).
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & (dtvbeg & _ & (T1 & _)) & _).
  pose proof MC as (M1 & M2 & M3).
  pose proof (rta_io Σ m HA) as IO.
  split; [|exact MC]. unfold icells_cmp.
  split; [exact (ro_of_rw _ _ _ G2)|].
  split; [exact (ro_head _ _ _ _ (ro_of_rw _ _ _ M1))|].
  split; [exact (io_ro_at m IO 0xc1780 _ ltac:(io_in))|].
  split; [exact (ro_of_rw _ _ _ M2)|].
  split; [exact T1|].
  exact (io_ro_at m IO 0x15ad66 _ ltac:(io_in)).
Qed.

Theorem rta_memcmp : memcmp_icontract RTA.
Proof. exact (memcmp_lift RTA rta_art_facts rip_proof rta_icells_cmp rta_shw). Qed.
