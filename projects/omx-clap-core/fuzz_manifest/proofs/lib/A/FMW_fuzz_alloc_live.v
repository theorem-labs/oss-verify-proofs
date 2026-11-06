(* fuzz_alloc_live 0x81b94 (alloc.c:118-121): auipc a0; ld a0, g_live; ret. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_fuzz_alloc_base.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Definition ss_live : sstate :=
  mkSS A_fuzz_alloc_live sr_atoms [fm_rcell G_LIVE 32] None (mkFacts [] [] []).

Theorem fuzz_alloc_live_holds : fuzz_alloc_live_spec tfibsegs B.
Proof.
intros ly S W regs mem md ch live peak cnt fail HPRE HG.
pose proof HPRE as (HAN & _).
pose proof HAN as (_ & Hra & _). unfold YK0s.ret_ok in Hra.
pose proof HG as (GL & _ & _ & _ & Hlp & Hp64 & _).
pose proof fma_wx as Hwx.
assert (HS : st_ok tfibsegs (Ereg regs [w64 live]) ss_live
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_fuzz_alloc_live) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. apply entry_st_ok.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    apply (region_ok_fm_rcell _ _ G_LIVE 32 live); [exact GL | | lia | unfold G_LIVE; lia | unfold G_LIVE; lia].
    exact (ew_Ereg_extra regs [w64 live] 0).
  - cbn. split; exact I.
  - exact I. }
unfold cfg_at. change (w64 A_fuzz_alloc_live) with (Z_to_bv 64 A_fuzz_alloc_live).
remember (Ereg regs [w64 live]) as E eqn:HE.
srr_run_with tbl_fma_ok HS.
eapply (SRr_ret_at tfibsegs tbl_fma tbl_fma_ok Hwx W E); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat2. rewrite wvb_collapse.
assert (Hm : ms_mem ms = mem) by exact (frame_of_read_only E (ss_mem ss_live) _ _ eq_refl HF).
rreg HS (1%bv : bv 5) R1. rreg HS (10%bv : bv 5) R10.
assert (E1 : ew E 1 = getr regs 1) by (rewrite HE; exact (ew_Ereg_nat regs [w64 live] 1 1%bv eq_refl)).
assert (E32 : ew E 32 = w64 live) by (rewrite HE; exact (ew_Ereg_extra regs [w64 live] 0)).
rewrite R1, E1, Hra, Hm.
apply (fpost_keep B STK_fuzz_alloc ly S W regs mem md ch (ms_regs ms) mat2); [exact HAN | |].
- eapply aregs_preserved_of_st_ok; [exact HS | rewrite HE; apply env_agree_refl | vm_compute; reflexivity].
- split; [rewrite R10, E32; reflexivity|]. split; [reflexivity | exact HG].
Qed.

End c.
