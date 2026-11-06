(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGif1dI.v (a working branch 84ee52cd012, file sha256 d346f5a87fc0) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: cgif_file's instance of the re-quarantine, Recycle and CacheDealloc fields of
   DGif0.DIface (DMiface.v types) and DIfaceR (DIfaceR.v types), restated from the released drain / DoRecycle walks
   (YFeu, YFey, YFhh): the facts DoRecycle reads from AR's ARm are exported over ARX_cgif and the recycle invariant
   DGif1dr.DRq_cgif.  Taken from DGif1d.v of a working branch cfc1ac03823; the drain fields (di_drain,
   dr_drain) stay in DGif1d.v. *)
(* cgif_file's instance of the re-quarantine and recycle-side fields of the generic Deallocate interface
   (DGif0.DIface, DIfaceR), at the agreed instantiation ARX := ARXr := AllocGcgif.ARX_cgif B, AOX := aowned B,
   DRq := DGif1dr.DRq_cgif B (the same body as DGif1.DRq_cgif), QB := qloose.

   - [di_requar_e_cgif]: ARXr = ARX, so the relation at DoRecycle's last cut is already ARX;
   - [di_requar_x_cgif], [di_requar_r_cgif]: AR at the drain's cuts from the cut memory (DGif1dq.requar_AR, over
     the released AFey.drain_fin_ARm); the merge arm is vacuous at cgif (DGif1dq.merge_vacuous), so the cut after the
     dequeue is the released one (AFey.S' X P R);
   - [dr_rchunk_cgif], [dr_cdealloc_cgif] (DIfaceR, the raw frame): DGif1dr's Recycle and CacheDealloc walks;
   - [di_rchunk_cgif], [di_cdealloc_cgif] (DIface, the aview frame): those two with the raw conjunct dropped. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFew AFeu AFf2.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFhh.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFhf AFey.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DIfaceR.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AllocGcgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DMspec DMiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif1dq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require DGif1dr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_requar_e.                                                                                                     *)
Lemma di_requar_e_cgif : forall B, di_requar_e_t (ARX_cgif B) (ARX_cgif B) (DGif1dr.DRq_cgif B).
Proof. intros B inst ly S W mem md H _. exact H. Qed.


(* ---------------------------------------------------------------------------------------------------------------- *)
(* di_requar_x, di_requar_r.                                                                                        *)
Lemma di_requar_x_cgif : forall B, TfibSyms B -> forall L24, di_requar_x_t B (ARX_cgif B) (aowned B) L24 qloose.
Proof.
intros B TB L24 inst ly X W mem md sp0 S' mem' md' [-> HAR] (HTB & HQL & HLB) (HXB & ->) H1 H2 DQ Ev El Ee.
assert (ES : set_qglobal (YFeuC.transfer_g X) (set_qthread qc0 X) = AFey.S' X [] (qc_list (st_qglobal X) ++ qc_list (st_qthread X))).
{ unfold AFey.S', AFey.XT, YFeuC.transfer_g, set_qglobal, set_qthread. cbn. rewrite Z.sub_0_r. reflexivity. }
rewrite ES in DQ |- *. split.
- split; [reflexivity|].
  exact (requar_AR B TB ly X W mem mem' md sp0 [] _ HAR HTB eq_refl (conj H1 H2) DQ (Forall_nil _) md' Ev El Ee).
- intros a O. exact (aowned_same_cf B ly X _ a eq_refl eq_refl O).
Qed.

Lemma di_requar_r_cgif : forall B, TfibSyms B -> forall L24,
di_requar_r_t B (ARX_cgif B) (ARX_cgif B) (aowned B) L24 qloose (DGif1dr.DRq_cgif B).
Proof.
intros B TB L24 inst ly X W mem md sp0 tmp S' P mem' md' [-> HAR] (HTB & HQL & HLB) (HXB & gm & ex & g' & popped & EM & EP & -> & ->)
  H1 H2 T1 T2 DQ PCELLS Ev El Ee.
pose proof HAR as (M & _).
rewrite (merge_vacuous _ X (am_wf B ly X _ M) HQL HXB) in EM. injection EM as <- <-. cbn [app] in *.
destruct g' as [R s].
pose proof (pop_batches_spec _ _ _ _ _ EP) as (P0 & EP0 & EL & EB). cbn [rev app] in EP0. subst P0. cbn [YFeuC.transfer_g qc_list qc_bytes] in EL, EB.
assert (ES : set_qglobal (mkQC R s) (set_qthread qc0 X) = AFey.S' X popped R).
{ unfold AFey.S', AFey.XT, set_qglobal, set_qthread. cbn. rewrite EB. reflexivity. }
rewrite ES in DQ |- *.
assert (PLC : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem')) (batch_cells popped)).
{ unfold plist_cells, qc_cells in PCELLS. cbn [qc_list qc_bytes] in PCELLS. do 4 (apply Forall_cons_iff in PCELLS as [_ PCELLS]). exact PCELLS. }
split; [split; [reflexivity|] | split].
- exact (requar_AR B TB ly X W mem mem' md sp0 popped R HAR HTB EL (conj H1 H2) DQ PLC md' Ev El Ee).
- unfold DGif1dr.DRq_cgif. apply RI_RIx_flat. exact (AFey.RIS' B ly X _ M HTB popped R EL).
- intros a O. exact (aowned_same_cf B ly X _ a eq_refl eq_refl O).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DIfaceR's recycle fields (the raw frame): DGif1dr.v's Recycle and CacheDealloc walks.                           *)
Lemma dr_rchunk_cgif : forall B, TfibSyms B -> dr_rchunk_t B (ARX_cgif B) (aowned B) (DGif1dr.DRq_cgif B).
Proof. intros B TB. exact (DGif1dr.dgif1_rchunk_cgif B TB). Qed.
Lemma dr_cdealloc_cgif : forall B, TfibSyms B -> dr_cdealloc_t B (ARX_cgif B) (aowned B) (DGif1dr.DRq_cgif B).
Proof. intros B TB. exact (DGif1dr.dgif1_cdealloc_cgif B TB). Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* DIface's recycle fields at the aview frame: the raw posts weakened (the raw conjunct dropped).                  *)
Lemma di_rchunk_cgif : forall B, TfibSyms B -> di_rchunk_t B (ARX_cgif B) (aowned B) (DGif1dr.DRq_cgif B).
Proof.
intros B TB inst ly X k ks zs cbp W regs mem md PREX RX.
eapply amreal_mono; [| exact (dr_rchunk_cgif B TB inst ly X k ks zs cbp W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & PUF & PM & DRQ & CI & OW).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact PUF|]. split; [exact PM|].
split; [exact DRQ|]. split; [exact CI | exact OW].
Qed.
Lemma di_cdealloc_cgif : forall B, TfibSyms B -> di_cdealloc_t B (ARX_cgif B) (aowned B) (DGif1dr.DRq_cgif B).
Proof.
intros B TB inst ly X its z zs W regs mem md PREX RX.
eapply amreal_mono; [| exact (dr_cdealloc_cgif B TB inst ly X its z zs W regs mem md PREX RX)].
intros r W' c' (regs' & mem' & md' & Hc & HP & _ & PUF & PM & DRQ & CI & OW).
exists regs', mem', md'. split; [exact Hc|]. split; [exact HP|]. split; [exact PUF|]. split; [exact PM|].
split; [exact DRQ|]. split; [exact CI | exact OW].
Qed.

End c.
