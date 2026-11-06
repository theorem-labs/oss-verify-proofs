(* Modified by Theorem Labs, 2026-10: relocated from omx-clap-core/fuzz_manifest lib/A/FMsnprintfGvsni0.v (a working branch 3e35620c52e) to libreac/fuzz_boxreg.asan: module paths changed; 6 address numerals relocated (port_addr_check 5033540ba83b predict mode, symbol + offset); 0x140000 kept: a bound over vsni_rodata's regions (r_hi r <= 0x140000), not an address; the tool's label __sanitizer::useCounts+0xc3c0 is a coincidence (the A lane's decision for the same line in FMsnprintfGvsni.v); re-pointed Requires: FMupoison -> lib.A.Rt; FMH_Base -> lib.A.Rt.SnprintfFmh. *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: a new walk of fm.asan's __interceptor_vsnprintf 0x458a0; the entry-state tactics
   (pairwise_disjoint_of_extents, facts_ok), the return-address step and the epilogue state built from the saved slots
   are adapted from A/AE35.v (tfib_vprintf_icpt_A / tfib_vprintf_icpt_E). *)
(* Modified by Theorem Labs, 2026-10: the window-free part of FMsnprintfGvsni.v moved here unchanged (vsni_rodata,
   vsni_rodata_chk, RUNTO, RUN, AC, SAVED, epi_chunks, ss_epi, epi_e, r_epi, stk_chunks, st_ok_head, den_atom, bvu5,
   ra_xfer, hull_xfer, EOK_havoc_lt, ro_low, saved_range); it reaches no file that fixes fm's stack bands
   (FMsnprintfImg / Gk0 / Gt0 in place of I / GI / Gk / Gt, no FMH_Rt). FMsnprintfGvsni.v re-exports it. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Rt/FMsnprintfGvsni0.v, with its module paths changed; 51 of its 79 lines of code are new or changed and 53 lines of the source are left out. *)
(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfG0.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMsnprintfG0.table). *)
(* fm's snprintf glue, the window-free part of FMsnprintfG.v: what the snprintf walks read off their runs (reg_is,
   KEPT), the entry facts of atom 2 (sn_facts0), st_ok with the stack region only (st_ok_take1) and the stack's zero
   shadow (stack_zero_shadow). Moved unchanged from FMsnprintfG.v (which Requires Export this file), so that a walk
   over the shared contracts reaches no file that fixes fm's stack bands. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YI00 YI16 YK06.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AE20 AE2y.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base FMsnprintfImg FMsnprintfK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMsnprintfGk0 FMsnprintfGt0.
Import ListNotations.
Open Scope Z_scope.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition sn_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
(* what the proof reads off the two runs *)
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 r)) v.
Definition KEPT : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
End s.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.

(* the stack's shadow reads 0 (the head of ARm's zero_shadow_ranges), seen through the user-poisoned ranges *)
Lemma stack_zero_shadow : forall ly S U W mem md lo len,
  ARU tfibsegs B ly S U W mem md -> ly_stk_lo ly <= lo -> lo + len <= ly_stk_hi ly -> lo mod 8 = 0 -> len mod 8 = 0 ->
  0 <= len -> zero_shadow (aview tfibsegs (w_H W) mem) SHADOW_OFF lo len.
Proof.
intros ly S U W mem md lo len HA Hlo Hhi H8 Hl8 Hl0 i Hi.
pose proof (ARU_ARm tfibsegs B ly S U W mem md HA) as HM.
pose proof (am_zshadow B ly S _ HM) as ZS. unfold zshadow_ok, zero_shadow_ranges in ZS.
apply Forall_inv in ZS. cbn [fst snd] in ZS.
pose proof (lo_top ly (am_layout B ly S _ HM)) as (_ & _ & _ & K2 & PA & _ & K1).
unfold page_aligned in PA. unfold kHighMemBeg, kHighMemEnd in *.
assert (Hlq : ly_stk_lo ly mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_lo ly) 4096 ltac:(lia)) as Dm. rewrite PA, Z.add_0_r in Dm. rewrite Dm.
  replace (4096 * (ly_stk_lo ly / 4096)) with ((ly_stk_lo ly / 4096 * 512) * 8) by ring. apply Z_mod_mult. }
set (j := (lo - ly_stk_lo ly) / 8 + i).
assert (Ej : shadow_of_addr SHADOW_OFF lo + i = shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + j).
{ unfold j, shadow_of_addr.
  pose proof (Z.div_mod lo 8 ltac:(lia)). pose proof (Z.div_mod (ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.div_mod (lo - ly_stk_lo ly) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (lo - ly_stk_lo ly) 8 ltac:(lia)).
  assert ((lo - ly_stk_lo ly) mod 8 = 0) by (rewrite Zminus_mod, H8, Hlq; reflexivity). lia. }
rewrite Ej.
assert (Hshz : shadow_of_addr SHADOW_OFF (ly_stk_lo ly) + j = shadow_addr (lo + 8 * i)).
{ rewrite <- Ej. unfold shadow_of_addr, shadow_addr.
  replace (lo + 8 * i) with (i * 8 + lo) by lia. rewrite Z.div_add_l by lia. lia. }
rewrite Hshz.
rewrite (ARU_view_out tfibsegs B ly S U W mem md _ HA).
- rewrite <- Hshz. apply ZS. unfold j.
  pose proof (Z.div_le_mono (lo - ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_pos (lo - ly_stk_lo ly) 8 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly) 8 ltac:(lia)).
  pose proof (Z.div_mod (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ly_stk_hi ly - ly_stk_lo ly - len) 8 ltac:(lia)).
  lia.
- pose proof (Z.div_mod len 8 ltac:(lia)). pose proof (Z.mod_pos_bound len 8 ltac:(lia)).
  pose proof (Z.div_pos len 8 ltac:(lia) ltac:(lia)).
  apply (ARU_shadow_out_block tfibsegs B ly S U W mem md _ HA); [lia|].
  apply (ARU_stack_not_block tfibsegs B LAWS ly S U W mem md _ HA). lia.
Qed.

(* st_ok with the stack region only *)
Lemma st_ok_take1 : forall E ss ms r0 rest,
  st_ok tfibsegs E ss ms -> ss_mem ss = r0 :: rest -> st_ok tfibsegs E (set_mem ss [r0]) ms.
Proof.
intros E ss ms r0 rest (H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hwf & Hok & Hpd) & H9) Hm.
rewrite Hm in Hwf, Hok, Hpd. unfold st_ok, set_mem. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts].
repeat (split; [assumption|]). split; [|exact H9]. split; [|split].
- cbn [regions_wf] in *. apply andb_prop in Hwf as [Ha _]. rewrite Ha. reflexivity.
- constructor; [exact (Forall_inv Hok) | constructor].
- cbn. tauto.
Qed.
End p.
