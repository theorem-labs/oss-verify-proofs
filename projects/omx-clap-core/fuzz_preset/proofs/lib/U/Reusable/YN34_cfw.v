(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from lib/Reusable/YN34.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Reusable/YN34_cfw.v, with its module paths changed; 2 of its 124 lines of code are new or changed and 2 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK0n YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0f YP04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO00 YN3v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YH00 YN35 YN3f YN3g.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0d YH02 YN34 YK15_cfw YP03_cfw YN3f_cfw YN3g_cfw.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import SlotAgree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Theorem crealizes_stdio_writev_by_run : forall E ss ms model ch k s1 s2 zs fd T,
st_ok src0segs E ss ms -> m_halted model = None -> m_vm_lazy model = [] ->
wx_step k ss = Some (s1, s2, zs, fd) ->
fdchan (Z_to_bv 64 fd) ch model ->
(forall ms' ws, st_ok src0segs (havoc E k ws) s2 ms' ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
skeleton (ss_mem s2) = skeleton (ss_mem ss) -> mem_atoms_lt k (ss_mem s2) = true ->
crealizes src0_msyms (mkCfg ms' model) T) ->
crealizes src0_msyms (mkCfg ms model) (t_emit (map (WriteEv ch) (map (Z_to_bv 8) zs)) T).
Proof using.
intros E ss ms model ch k s1 s2 zs fd T HS Hh Hlz Hck Hch Hk. unfold wx_step in Hck.
destruct (sym_runN src0segs src0tbl FUEL ss) as [s1' st] eqn:Hrun. destruct st; try discriminate.
destruct (ss_pc s1' =? WL_ECALL1) eqn:Hpc; [|discriminate]. apply Z.eqb_eq in Hpc. cbn [negb] in Hck.
destruct (sr_get (ss_regs s1') 17) as [no| | | | | | | | | |] eqn:H17; try discriminate.
destruct no as [|p17|]; try discriminate. do 7 (destruct p17 as [p17|p17|]; try discriminate).
destruct (lit_sv (sr_get (ss_regs s1') 10)) as [fd'|] eqn:H10; [|discriminate].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 12)) as [cnt|] eqn:H12; [|discriminate].
destruct (iovcnt_of (ss_facts s1') (sr_get (ss_regs s1') 18)) as [cnt'|] eqn:H18; [|discriminate].
destruct (sr_get (ss_regs s1') 2) as [|b K| | | | | | | | |] eqn:H2; try discriminate.
destruct (sr_get (ss_regs s1') 9) as [F| | | | | | | | | |] eqn:H9; try discriminate.
destruct (ss_resv s1') eqn:Hrv; try discriminate.
destruct (negb ((fd' =? 1) || (fd' =? 2))) eqn:Hfd; [discriminate|].
assert (Hfd12 : fd' = 1 \/ fd' = 2).
{ apply negb_false_iff in Hfd. apply orb_prop in Hfd as [Hf|Hf]; apply Z.eqb_eq in Hf; lia. }
destruct (negb (cnt =? cnt')) eqn:Hcc; [discriminate|]. apply negb_false_iff in Hcc. apply Z.eqb_eq in Hcc. subst cnt'.
destruct (negb (zcanon F =? F)) eqn:HFc; [discriminate|]. apply negb_false_iff in HFc. apply Z.eqb_eq in HFc.
destruct (ss_atoms_lt k s1') eqn:Hat; [|discriminate]. cbn [negb] in Hck.
destruct (find_wregion (ss_mem s1') b (K + 8) (K + 40)) as [i|] eqn:Hwr; [|discriminate].
destruct (atom_lookup (f_atoms (ss_facts s1')) b) as [f|] eqn:Hf; [|discriminate].
destruct (lit_buf src0segs (ss_mem s1') (SLit (F + 120)) 4) as [fdz|] eqn:Hfdz; [|discriminate].
destruct ((0 <=? af_lo f + K) && (af_hi f + K + 40 <=? 2^47) && (0 <=? F) && (F + 124 <=? af_lo f + K + 8)
&& zlist_eqb fdz [fd'; 0; 0; 0]) eqn:Hbnd; [|discriminate]. cbn [negb] in Hck.
apply andb_prop in Hbnd as [Hbnd Hfdz4]. apply andb_prop in Hbnd as [Hbnd B4]. apply andb_prop in Hbnd as [Hbnd B3].
apply andb_prop in Hbnd as [B1 B2].
apply Z.leb_le in B1. apply Z.leb_le in B2. apply Z.leb_le in B3. apply Z.leb_le in B4. apply zlist_eqb_eq in Hfdz4. subst fdz.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (sr_get (ss_regs s1') 11)) eqn:H1911; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H1911.
destruct (find_wregion_sound _ _ _ _ _ Hwr) as (r & Hi & Hrb & Hrlo & Hrhi & Hwlo & Hwhi).
destruct (sym_run_sound src0segs src0tbl src0tbl_ok _ E ss s1' RS_ecall ms HS Hrun) as (_ & _ & _ & Hsk' & _).
pose proof (eq_sym Hsk') as Hsk. clear Hsk'.
assert (Hma : forall i K, mem_atoms_lt k (ss_mem (wl_after s1' i K k)) = true).
{ intros i0 K0. unfold wl_after; cbn [ss_mem].
apply (mem_atoms_lt_submem k _ (ss_mem s1')); [apply submem_forget_win|].
unfold ss_atoms_lt in Hat. apply andb_prop in Hat as [Hat' _]. apply andb_prop in Hat' as [Hat' _].
apply andb_prop in Hat' as [_ Hm]. exact Hm. }
assert (Hskafter : forall i K, skeleton (ss_mem (wl_after s1' i K k)) = skeleton (ss_mem ss)).
{ intros i0 K0. unfold wl_after; cbn [ss_mem]. rewrite skeleton_forget_win. symmetry. exact Hsk. }
eapply (crz_run_ecall src0_msyms src0tbl src0tbl_ok FUEL E ss s1' ms model _ Hh Hlz HS Hrun).
intros ms1 HS1 HF1.
pose proof HS1 as HS1copy.
destruct HS1copy as (_ & _ & _ & _ & _ & _ & Hregs1 & Hmem1 & HG1).
pose proof (lit_sv_sound E _ _ H10) as [D10 R10].
pose proof (iovcnt_of_sound E _ _ _ HG1 H12) as D12.
pose proof (iovcnt_of_sound E _ _ _ HG1 H18) as D18.
assert (H32 : fd32 (Z_to_bv 64 fd') = Z_to_bv 64 fd') by (destruct Hfd12 as [-> | ->]; reflexivity).
assert (Hfd31 : bv_unsigned (Z_to_bv 64 fd') < 2^31) by (rewrite u_Z2bv by lia; lia).
pose proof (atom_lookup_ok E _ _ _ (proj1 HG1) Hf) as (Hbf & _).
pose proof (lit_buf_sound src0segs E (ms_mem ms1) _ _ _ _ Hmem1 Hfdz) as Hfdrd. cbn [sv_denot] in Hfdrd.
assert (HfdB : bytes_le_to_Z (map (Z_to_bv 8) [fd'; 0; 0; 0]) = bv_unsigned (Z_to_bv 64 fd')).
{ clear -Hfd12. destruct Hfd12 as [-> | ->]; vm_compute; reflexivity. }
destruct (cnt =? 2) eqn:Hc2.
- apply Z.eqb_eq in Hc2. subst cnt.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 8))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 8)) as [[[[vb0 vl0] zs0] n0]|] eqn:Ho0; [|discriminate].
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|discriminate].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|discriminate].
destruct ((rem =? n0 + n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|discriminate].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. subst rem.
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho0) as (Hiov0 & Hrd0 & HU0 & Hlz0 & Hn0 & Hnw0 & Hd0).
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
rewrite map_app.
eapply (crz_sym_stdio_writev2 E s1' ms1 model (Z_to_bv 64 fd') ch i b K F r vb0 vl0 vb1 vl1 _ _ _ k T Hh Hlz HS1 Hrv Hpc);
[ exact H17 | exact D10 | exact Hch | exact H32 | exact Hfd31 | exact D12 | exact D18 | exact H2
| exact H19 | rewrite <- H1911; exact H19 | rewrite (lit_sv_U E _ _ H22), HU0, HU1; reflexivity
| rewrite H9, U_SLit; exact HFc
| exact Hi | exact Hrb | exact Hrlo | exact Hrhi | exact Hwlo | exact Hwhi
| unfold iov_read2; rewrite Hiov0; replace (K + 8 + 16) with (K + 24) by lia; rewrite Hiov1; reflexivity
| exact Hrd0 | exact Hrd1 | rewrite HU0, HU1; lia
| rewrite HU0; exact Hnw0 | rewrite HU0; exact Hd0 | rewrite HU1; exact Hnw1 | rewrite HU1; exact Hd1
| exact Hfdrd | exact HfdB | lia | unfold M64 in *; lia | lia | lia | unfold M64 in *; lia | exact Hat | ].
intros ms' ws HS' HF'. apply (Hk ms' ws HS'); [eapply frame_of_trans; [exact Hsk | exact HF1 | exact HF'] | apply Hskafter | apply Hma].
- destruct (cnt =? 1) eqn:Hc1; [|discriminate]. apply Z.eqb_eq in Hc1. subst cnt.
destruct (sv_eqb (sr_get (ss_regs s1') 19) (SOff b (K + 24))) eqn:H19; [|discriminate]. cbn [negb] in Hck.
apply sv_eqb_eq in H19.
destruct (wx_one s1' b K (K + 24)) as [[[[vb1 vl1] zs1] n1]|] eqn:Ho1; [|discriminate].
destruct (lit_sv (sr_get (ss_regs s1') 22)) as [rem|] eqn:H22; [|discriminate].
destruct ((rem =? n1) && (1 <=? rem) && (rem <=? 2 ^ 25)) eqn:Hrem; [|discriminate].
injection Hck as <- <- <- <-.
apply andb_prop in Hrem as [Hrem Q3]. apply andb_prop in Hrem as [Q1 Q2].
apply Z.eqb_eq in Q1. apply Z.leb_le in Q2. apply Z.leb_le in Q3. subst rem.
destruct (wx_one_sound E s1' (ms_mem ms1) b K _ _ _ _ _ Hmem1 HG1 Ho1) as (Hiov1 & Hrd1 & HU1 & Hlz1 & Hn1 & Hnw1 & Hd1).
eapply (crz_sym_stdio_writev1 E s1' ms1 model (Z_to_bv 64 fd') ch i b K F r vb1 vl1 _ _ k T Hh Hlz HS1 Hrv Hpc);
[ exact H17 | exact D10 | exact Hch | exact H32 | exact Hfd31 | exact D12 | exact D18 | exact H2
| exact H19 | rewrite <- H1911; exact H19 | rewrite (lit_sv_U E _ _ H22), HU1; reflexivity
| rewrite H9, U_SLit; exact HFc
| exact Hi | exact Hrb | exact Hrlo | exact Hrhi | exact Hwlo | exact Hwhi
| exact Hiov1
| exact Hrd1 | rewrite HU1; lia
| rewrite HU1; exact Hnw1 | rewrite HU1; exact Hd1
| exact Hfdrd | exact HfdB | lia | unfold M64 in *; lia | lia | lia | unfold M64 in *; lia | exact Hat | ].
intros ms' ws HS' HF'. apply (Hk ms' ws HS'); [eapply frame_of_trans; [exact Hsk | exact HF1 | exact HF'] | apply Hskafter | apply Hma].
Qed.
End e.
