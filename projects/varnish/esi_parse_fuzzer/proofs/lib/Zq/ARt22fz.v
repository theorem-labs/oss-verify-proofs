(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6 ARtStmts ARtSscs ARt2_lib AMTac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp2qw ARt2onl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt_u2d.ARt_fts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2qw OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.ARt2onl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd Require Import DA_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amstep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AMTac.amz ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.amf_zstep.
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac br_auto := first [ br_not_taken | br_taken ].
Ltac bstepA := first [ amz | if_false | if_true | br_auto ].
Ltac run_to pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => bstepA; fold_xlits end).
(* [comment removed for export] *)
Ltac rebundle := repeat (lazymatch goal with
  | |- ro_cells _ _ _ _ => eassumption
  | |- rw_cells _ _ _ _ => eassumption
  | |- bytes_at _ _ _ _ => eassumption
  | |- mapped _ _ _ => eassumption
  | |- thread_cells _ _ _ _ _ => unfold thread_cells
  | |- tls_consts _ => unfold tls_consts
  | |- tls_dyn _ _ _ => unfold tls_dyn
  | |- poison_consts _ => unfold poison_consts
  | |- _ /\ _ => split
  | |- _ => first [eassumption | plia] end).

Definition keep (P : Prop) : Prop := P.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Theorem ia_init_ok : ia_init_stmt.
Proof.
  unfold ia_init_stmt. intros until ws. intros MI ST LOLE CEIL HI LCK GPS PSZ RB RMAP RST LWS RSEC RTL RA.
  pose proof alloc_ceiling_val as CV. unfold ia_entry, IAB in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (0x144648, 0x14464c); (744896, 744896 + 1); (744896 + 8, 744896 + 8 + 262144);
                           (744896 + 0x40040, 744896 + 0x40040 + 3456); (744896 + 0x40dc0, 744896 + 0x40dc0 + 262728); (744896 + 0x81008, 744896 + 0x81008 + 40)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  lit_addrs.
  (* [comment removed for export] *) lazymatch goal with |- evt _ ?hotQ0 _ => set (hotQ := hotQ0) end. carve_frame 48%nat ST.
  do 8 amz. (* [comment removed for export] *)
  amz. amz. amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  change (bv_swrap 32 256) with 256. change (bv_swrap 32 65280) with 65280.
  apply (hdr4_join _ _ 0 0 hi) in LCK; [| lia | lia | lia | cbn; tauto]. replace (0 + 256 * 0 + 65536 * hi) with (65536 * hi) in LCK by lia.
  amz. (* [comment removed for export] *) rewrite sx32_small by lia.
  amz. amz. amz. amz.
  replace (Z.lxor (65536 * hi) (Z.land (Z.lxor (65536 * hi) 256) 65280)) with (256 * 1 + 65536 * hi)
    by (pose proof (cas_set_byte1 hi 0 1) as E; rewrite Z.mul_0_r, Z.add_0_l, Z.mul_1_r in E; symmetry; apply E; lia).
  scstep; zsimp. (* [comment removed for export] *)
  amz. if_false. (* [comment removed for export] *)
  amz. amz. rewrite (srlw8_byte (65536 * hi)) by lia.
  replace (65536 * hi / 256) with (hi * 256) by (apply Z.div_unique_exact; lia). rewrite Z_mod_mult.
  amz. if_false. (* [comment removed for export] *)
  replace (256 + 65536 * hi) with (0 + 256 * 1 + 65536 * hi) in LCK by lia.
  apply (hdr4_split _ _ 0 1 hi) in LCK; [| lia | lia | lia | cbn; tauto].
  amz. amz. if_false. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [eapply imemset_byte_spec with (n := 40%nat); rewrite ?unsigned_lit by lia;
                     [exact RTL | lia | reflexivity | lia | cbv; discriminate | exact MI] | post_call_z rsegs mc ] end.
  try clear RTL. rename MI0 into MI.
  amz. (* [comment removed for export] *)
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [eapply imemset_byte_spec with (n := Z.to_nat 262144); rewrite ?unsigned_lit, ?Z2Nat.id by lia;
                     [exact RMAP | lia | reflexivity | lia | cbv; discriminate | exact MI] | post_call_z rsegs mc ] end.
  try clear RMAP. rename MI0 into MI.
  amz. amz. amz. amz. amz. (* [comment removed for export] *)
  replace (Z_to_bv 64 3456) with (Z_to_bv 64 (8 * Z.of_nat 432%nat)) by reflexivity.
  amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    eapply evt_cut; [eapply (imemset16_zero_spec) with (ws := ws); [exact RST | exact LWS | exists 216%nat; reflexivity | lia | reflexivity | lia | lia | exact MI]
                    | post_call_z rsegs mc ] end.
  try clear RST. rename MI0 into MI.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells rsegs _ 744904 _ |- _ => rename H into RMAPZ end.
  lazymatch goal with H : u64arr rsegs _ 1007104 _ |- _ => rename H into RSTZ end.
  lazymatch type of RMAPZ with ?t => change t with (keep t) in RMAPZ end.
  lazymatch type of RSTZ with ?t => change t with (keep t) in RSTZ end.
  amz. amz. amz. amz. amz. amz. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into mA end.
  eapply evt_cut; [eapply imemset_byte_spec with (n := Z.to_nat 262728); rewrite ?unsigned_lit, ?Z2Nat.id by lia;
                   [exact RSEC | lia | reflexivity | lia | cbv; discriminate | exact MI] | ].
  clear RSEC.
  intros ms' PO. destruct_exs PO. destruct PO as (E & MUc & WMc & MIc & RSEC). subst ms'.
  rewrite ?unsigned_lit in MUc, RSEC by lia. rewrite ?Z2Nat.id in MUc by lia.
  lazymatch type of MUc with munch ?Wc _ ?m' =>
    transport_after_call rsegs mA m' MUc WMc;
    unfold keep in RMAPZ, RSTZ;
    (apply (rw_cells_transport rsegs Wc mA m') in RMAPZ; [| exact MUc | exact WMc | cbn [disjoint_from cells_size csize Nat.add]; lia]);
    (apply (u64arr_transport rsegs Wc mA m') in RSTZ; [| exact MUc | exact WMc | cbn [disjoint_from]; rewrite repeat_length; lia])
  end.
  clear MUc WMc MI. rename MIc into MI.
  replace (ret_pc (Z_to_bv 64 411200)) with (Z_to_bv 64 411200) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  lazymatch goal with H : rw_cells rsegs _ 1010560 _ |- _ => apply zeros_split16 in H; [| plia]; rename H into RSEC0 end.
  change (Z.to_nat (262728 - 16)) with (Z.to_nat 262712) in RSEC0.
  (* [comment removed for export] *)
  lazymatch type of RSEC0 with rw_cells _ ?mm _ (?c1 :: ?c2 :: ?rest) =>
    destruct (ARt_u2d.rw_cells_app_split mm 1010560 [c1; c2] rest RSEC0) as [RSEC1 RSEC2] end.
  clear RSEC0. change (1010560 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])) with 1010576 in RSEC2.
  lazymatch type of RSEC2 with ?t => change t with (keep t) in RSEC2 end.
  lazymatch type of RMAPZ with ?t => change t with (keep t) in RMAPZ end.
  lazymatch type of RSTZ with ?t => change t with (keep t) in RSTZ end.
  lazymatch goal with H : rw_cells rsegs _ 1273288 _ |- _ => rename H into RTLZ end.
  lazymatch type of RTLZ with ?t => change t with (keep t) in RTLZ end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (1328712, 1328716); (1010560, 1010576)] mc) as MU3;
    pose proof (wmono_refl rsegs mc) as WM3 end.
  amz. amz. amz. amz. if_true. (* [comment removed for export] *)
  amz. amz. amz. amz.
  amz. (* [comment removed for export] *)
  amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  amz. amz. (* [comment removed for export] *)
  do 9 amz. (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
    unfold keep in RMAPZ, RSTZ, RSEC2, RTLZ;
    lazymatch type of MU3 with munch ?W3 ?m3 _ =>
      apply (rw_cells_transport rsegs W3 m3 mf) in RMAPZ; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (u64arr_transport rsegs W3 m3 mf) in RSTZ; [| exact MU3 | exact WM3 | cbn [disjoint_from]; rewrite repeat_length; lia];
      apply (rw_cells_transport rsegs W3 m3 mf) in RSEC2; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia];
      apply (rw_cells_transport rsegs W3 m3 mf) in RTLZ; [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; lia]
    end end.
  apply (ARt_u2d.rw_cells_app_join _ _ _ _ RSEC1) in RSEC2. cbn [app] in RSEC2. clear RSEC1.
  (subst hotQ; apply evt_done).
  lazymatch goal with |- context [MS _ _ _ _ _ ?mm _] =>
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, mm end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [exact LCK|].
  split. { lazymatch goal with H : rw_cells rsegs _ 744896 _ |- _ => exact H end. }
  split; [exact RMAPZ|]. split; [exact RSTZ|]. split; [exact RSEC2|]. exact RTLZ.
Qed.

End CEIL.
