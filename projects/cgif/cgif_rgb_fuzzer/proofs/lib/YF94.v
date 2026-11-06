(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YK18 YK0s YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02 YQ0f YQ0g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YI00.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l YA0m YA0n YA0o.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0h YG0u YB0z YF8z YF90 YF9g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP09 YB10 YE2p.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YF00 YF1g.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache.
Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section b.
Section c.
Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Variable W : world trasegs.
Lemma memset_stretch_nw : forall (k : nat) (E : env) ss ms md (d len retpc : Z) (Q : world trasegs -> config -> Prop),
st_ok trasegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_pc ss = tra_A_musl_memset ->
ss_atoms_lt k ss = true -> no_cdata (ss_mem ss) = true ->
getr (ms_regs ms) 10 = Z_to_bv 64 d -> getr (ms_regs ms) 12 = Z_to_bv 64 len -> getr (ms_regs ms) 1 = Z_to_bv 64 retpc ->
0 <= len -> TRA_IMG_END <= d -> d + len < 2 ^ 64 -> retpc mod 4 = 0 -> 0 <= retpc < 2 ^ 64 ->
(forall a, d <= a < d + len -> apresent (w_H W) (ms_mem ms) a) ->
(forall r, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_hi r <= d \/ d + len <= base_val E (YQ0b.r_base r) + YQ0b.r_lo r
\/ YQ0b.r_hi r <= YQ0b.r_lo r) ->
(forall r a, In r (ss_mem ss) -> base_val E (YQ0b.r_base r) + YQ0b.r_lo r <= a < base_val E (YQ0b.r_base r) + YQ0b.r_hi r -> 0 <= a < 2 ^ 64) ->
(forall regs' mem' mat',
st_ok trasegs (havoc E k (map (getr regs') [11; 12; 13; 14; 15; 16]%bv))
(ss_after_stretch ss (ss_mem ss) k [11; 12; 13; 14; 15; 16]%bv retpc)
(restrict (w_H W) (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom trasegs))) ->
getr regs' 10 = Z_to_bv 64 d ->
(forall x : word, ~ (d <= bv_unsigned x < d + len) -> mem' x = ms_mem ms x) ->
(forall a, apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) mem' a) ->
(forall x : word, d <= bv_unsigned x < d + len -> mem' x = Some (Z_to_bv 8 (bv_unsigned (getr (ms_regs ms) 11) mod 256))) ->
SRr trasegs W (mkCfg (mkst regs' (Z_to_bv 64 retpc) mem' (seg_rom trasegs)) (with_vm_backing (m_vm_lazy md) mat' md)) Q) ->
SRr trasegs W (mkCfg ms md) Q.
Proof. first [ exact (YF1g.memset_stretch_nw (imgk := YF00.K_tra)) | exact ((YF1g.memset_stretch_nw (imgk := YF00.K_tra)) W) | exact (YF1g.memset_stretch_nw (imgk := YF00.K_tra)) | solve [ eapply (YF1g.memset_stretch_nw (imgk := YF00.K_tra)); eassumption ] | solve [ intros; eapply (YF1g.memset_stretch_nw (imgk := YF00.K_tra)); eassumption ] ]. Qed.
End c.
End b.
