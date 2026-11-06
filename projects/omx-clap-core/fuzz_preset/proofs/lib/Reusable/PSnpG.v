(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfGvsni.v; 394 of its 460 lines of code are new or changed and 704 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfG.v, with its module paths changed; 17 of its 49 lines of code are new or changed and 428 lines of the source are left out. *)
(* fm's snprintf: __wrap_snprintf 0x41314 (`j 0x45c90`) and __interceptor_snprintf 0x45c90 (frame 0x60; a3..a7 spilled
   at sp + 0x38, the va area P; TryAsanInitFromRtl; __interceptor_vsnprintf (str, size, format, ap = P)), and
   HarnessDesign's asnprintf_realizes (FMH_Rt.v) from the chain's contracts. Written new (no released proof names
   __interceptor_snprintf). *)
(* Modified by Theorem Labs, 2026-10: restated over the engine's generic ARx with the ghost list Hp fixed (route (a),
   c-omx-hpreset 10:51Z), from origin/cold/port-fm-rtprintf-param 7e395de08f5 proofs/omx-clap-core/fuzz_manifest/lib/A/
   FMsnprintfG.v; image-free (segs, B, ARx are Section variables; the fm addresses above are the source's comment, no
   numeral of them appears below). Only the five items the four roots' closure (snp_ok / svsni_ok / svsn_ok / svfi_ok)
   reaches are kept: sn_facts0 (:33), reg_is (:49), KEPT (:53), st_ok_take1 (:174-183) unchanged, and
   stack_zero_shadow (:101-138) as stack_zero_shadow_x, re-proved from the engine law alx_zshadow_byte (YCbqG.v:113-116,
   AR_laws_x field 13) over the real memory: ARx reads mem itself, so the U form's move through `unpoison U`
   (ARU_view_out, ARU_shadow_out_block, ARU_stack_not_block) and its layout facts (am_layout's lo_top) go away. The
   symbolic run of __interceptor_snprintf, snk_base_entry, snk_dest_entry, g_frame_run2, g_frame_mono,
   snprintf_of_vsni and snprintf_realizesU are on the HarnessDesign route, not reached by the roots, and not ported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI00 YI16 YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG PSnpGkit.
Import ListNotations.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
(* ---- the facts of the walks' entry states (atom 2 = the entry sp) ---- *)
Definition sn_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
(* what the proof reads off a run *)
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) v.
Definition KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* st_ok with the stack region only *)
Lemma st_ok_take1 : forall E ss ms r0 rest,
  st_ok segs E ss ms -> ss_mem ss = r0 :: rest -> st_ok segs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
End s.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {segs : list Segment}.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Hypothesis alx_zshadow_byte : ARx_zshadow_byte_law segs ARx.

(* the stack's shadow reads 0: the engine's per-byte zero-shadow law over the real memory, at each 8-byte granule of
   [lo, lo + len) *)
Lemma stack_zero_shadow_x : forall ly S Hp W mem md lo len,
  ARx ly S Hp W mem md -> ly_stk_lo ly <= lo -> lo + len <= ly_stk_hi ly -> lo mod 8 = 0 -> len mod 8 = 0 ->
  0 <= len -> zero_shadow (aview segs (w_H W) mem) SHADOW_OFF lo len.
Proof.
intros ly S Hp W mem md lo len HA Hlo Hhi H8 Hl8 Hl0 i Hi.
assert (E : shadow_of_addr SHADOW_OFF lo + i = SHADOW_OFF + (lo + 8 * i) / 8).
{ unfold shadow_of_addr. replace (lo + 8 * i) with (lo + i * 8) by lia. rewrite Z.div_add by lia. lia. }
rewrite E. apply (alx_zshadow_byte ly S Hp W mem md (lo + 8 * i) HA).
pose proof (Z.div_mod len 8 ltac:(lia)) as D. rewrite Hl8, Z.add_0_r in D. lia.
Qed.
End p.
