(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) call-step kit of parse_items.
   pic_after_callT is a B-local copy of the A-kit helper pig_after_callT of
   a working branch 1925446802a proofs/omx-clap-core/fuzz_state/lib/A/FSW_parse_items_grow.v
   (a Theorem Labs lane), with ONE change: the callee's journal is taken at the caller's RAISED window (STKc + (ot - spZ
   regsC), ot), which is the form every reader callee that writes the caller's struct pj_in has (skip_ws_spec,
   parse_string_spec, parse_value_spec); A's copy takes it at the callee's own sp, which is what its grow has.
   It resumes in FSW_ret's fss_retT - the frame with its saved-register chunks, the two shadow-base cells of image B
   and the walk's extra regions rs with their atom facts gf - which is the state shape every stage of
   lib/B/Prog/FSW_parse_items.v consumes (pi_ssB0 = fss_retT 0x84f5c 144 pi_cs [pi_qR; pi_vR] pi_gfR).
   The five call steps themselves (skip_ws x4, grow x2, parse_string, __asan_memset, parse_value) are NOT here yet. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_K3 FSW_ret FSW_rd FSW_pj FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.Prog Require Import FSW_parse_items_tbl FSW_parse_items.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* ---- the T resume after a program call whose post is at the caller's RAISED window top ot ---- *)
Lemma pic_after_callT : forall B STK ot FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 sf f regsC
  ly' S' U' W' regs' mem' md' kc xs cs rs gf r,
  as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address ->
  as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address ->
  ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sf - f -> 0 < f -> 0 <= STKc -> spZ regsC mod 16 = 0 -> sf <= ot -> ot - STK <= spZ regsC - STKc ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem') (sf - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (mrestrict (w_H W') mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros B STK ot FP own ly S U W mem md W0 lyc Sc Uc memC mdC k STKc FP1 sf f regsC ly' S' U' W' regs' mem' md' kc
  xs cs rs gf r Hgot Hcell HJ HARUc HJc HF OK' PO' HP Hsp Hf HSc Hal Hsf Hlo Hwf Hcs Hrs Hpd Hgf.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (HJ2 : ajournal tfibsegs B STK ot FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc)).
{ pose proof (fsw_ajournal_sub5 B STK ot FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
    (STKc + (ot - spZ regsC)) ot FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc ltac:(lia) ltac:(lia) HF) as H.
  cbn [app] in H. exact H. }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
pose proof HJ2 as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Esp : YK11.getr regs' 2 = YK11.getr regsC 2) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (Usp : spZ regs' = sf - f) by (unfold spZ; rewrite Esp; exact Hsp).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 2) = sf - f)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ xs) 2 2%bv eq_refl); exact Usp).
assert (E32 : ew (Ereg regs' (fs_extraT ++ xs)) 32 = Z_to_bv 64 SHADOW_OFF)
  by (change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U32 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ xs)) 32) = SHADOW_OFF)
  by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
destruct (fsw_got_shadow B ly' S' W' (unpoison U' mem') md' Hgot Hcell HAR2) as [Kgot Kcell].
assert (MB : forall x, 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W') mem') x = mbyte tfibsegs (mrestrict (w_H W') (unpoison U' mem')) x).
{ intros x Hx. unfold mbyte, mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly' S' U' W' mem' md' (Z_to_bv 64 x) HARU'
    ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
  reflexivity. }
assert (VM : forall a vv, 0 <= a -> a + 8 <= SHADOW_OFF ->
  val_mem tfibsegs (mrestrict (w_H W') (unpoison U' mem')) a 8 vv ->
  val_mem tfibsegs (mrestrict (w_H W') mem') a 8 vv).
{ intros a vv Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
assert (Vgot : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_GOT_asan_shadow_memory_dynamic_address 8
  tfib_D_asan_shadow_memory_dynamic_address).
{ apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kgot)]. }
assert (Vcell : val_mem tfibsegs (mrestrict (w_H W') mem') tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
{ apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
  | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
  | exact (val_mem_of_rdword tfibsegs (w_H W') (unpoison U' mem') _ _ Kcell)]. }
assert (Hin : forall c, In c cs -> 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f).
{ pose proof Hwf as Hw. unfold fsT_ret_regions in Hw. cbn [app regions_wf] in Hw.
  apply andb_prop in Hw as [Hw _]. unfold YP09.region_wf in Hw.
  apply andb_prop in Hw as [_ Hfa]. rewrite forallb_forall in Hfa.
  intros c Hc. pose proof (Hfa c Hc) as Hci. unfold YP09.chunk_inside, fstk_ret in Hci.
  cbn [YP09.r_lo YP09.r_hi] in Hci. apply andb_prop in Hci as [Hci _]. apply andb_prop in Hci as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. split; [exact H1 | exact H2]. }
rewrite restrict_mkst_fx. unfold fss_retT, fsT_ret_regions in *. cbn [app] in *. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- exact Hwf.
- constructor; [|constructor; [|constructor; [|exact Hrs]]].
  + unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E2. split; [lia|]. split; [lia|]. split.
    * intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
    * exact Hcs.
  + unfold fs_got_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
      (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
      [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
  + unfold fs_bcell_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
    split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
      [rewrite fsw_SOff0, E32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
- exact Hpd.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok at 1 2. cbn [af_lo af_hi af_al2].
  rewrite E2, U32. split; [|split; [|exact Hgf]].
  + change (2 ^ 4) with 16. split; [lia|]. split; [|lia]. rewrite <- Hsp. exact Hal.
  + rewrite Z.pow_0_r. split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.
End t.
