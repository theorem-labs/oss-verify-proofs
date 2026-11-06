(* The device the walk of plugin-hostd/fuzz_command's strdup entry uses to cross internal_strlen 0x69b10, a callee
   the symbolic runner cannot run: its body is given as [msteps] over the restricted memory, it returns through ra
   and leaves the memory as it found it, so the symbolic state keeps every region it had and the walk goes on from
   the state [ss_after_call] names. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AB1v AF0x AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* The memory a region of the symbolic state describes is unchanged, so the region is kept. *)
Lemma region_kept_same : forall E (m : word -> option byte) r, region_kept tfibsegs E m m r.
Proof. intros E m r. split; [intros a _; reflexivity | intros a _ Hw; exact Hw]. Qed.

(* A callee given as [msteps] over the restricted memory, which returns to the literal [retpc] its caller put in
   ra and leaves the memory as it was. *)
Lemma sd_call : forall (W : world tfibsegs) E ss ms md (k : nat) (rs : smem) (retpc : Z) (regs' : bvmap 5 word) Q,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
ss_resv ss = None ->
ss_atoms_lt k ss = true -> regions_wf rs = true -> no_cdata rs = true -> mem_atoms_lt k rs = true ->
submem rs (ss_mem ss) ->
sr_get (ss_regs ss) 1 = SLit retpc ->
getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
v_jalr (Z_to_bv 64 retpc) 0 = Z_to_bv 64 retpc ->
msteps tfibsegs (mkst (ms_regs ms) (Z_to_bv 64 (ss_pc ss)) (mrestrict (w_H W) (ms_mem ms)) (seg_rom tfibsegs))
(mkst regs' (v_jalr (getr (ms_regs ms) 1) 0) (mrestrict (w_H W) (ms_mem ms)) (seg_rom tfibsegs)) ->
regs_preserved (ms_regs ms) regs' ->
(forall md', same_but_materialized md md' ->
st_ok tfibsegs (havoc E k (map (getr regs') CLOB)) (ss_after_call ss rs k retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) (ms_mem ms) (seg_rom tfibsegs))) ->
SRr tfibsegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) (ms_mem ms) (seg_rom tfibsegs)) md') Q) ->
SRr tfibsegs W (mkCfg ms md) Q.
Proof.
intros W E ss ms md k rs retpc regs' Q HS Hrv Hat Hwf Hnc Hmat Hsub Hra Hra' Hjr Hms HP HK.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv) as Hshape.
rewrite Hra', Hjr in Hms.
rewrite Hshape.
eapply (SRr_msteps tfibsegs AF0x.Hwx_tfa W); [rewrite restrict_mkst_fx; exact Hms|].
intros md' Hsbm _. rewrite (same_but_materialized_wvb md md' Hsbm).
cbn [unrestrict ms_mem ms_regs mkst].
rewrite unrestrict_mkst_mrestrict.
apply (HK (with_vm_backing (m_vm_lazy md) (m_vm_materialized md') md)).
- apply with_vm_backing_same.
- exact (st_ok_after_call tfibsegs k E ss (restrict (w_H W) ms) regs' (mrestrict (w_H W) (ms_mem ms)) rs retpc
HS Hrv Hat Hwf Hnc Hmat Hsub Hra HP ltac:(apply Forall_forall; intros r _; apply region_kept_same)).
Qed.

End h.
