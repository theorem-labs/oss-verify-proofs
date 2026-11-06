(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module paths and module names changed; 347 of its 420 lines of code are new or changed and 1587 lines of the source are left out. *)
(* check_words' ASan+UBSan walk (plugin-hostd/fuzz_command.asan-ubsan), segment I2: item a of call c, from the point
   IK (0x87db8, listing 0x1888) to ICMP (0x87ee4, listing 0x19b4). The B twin of lib/A/Prog/check_words_sI2.v
   (an earlier version).
   This file proves the stretch from IK to the first atoi (i2_K_run: the kind dispatch, the trap site 0x87df4 and the
   atoi call at 0x87dfc) and assembles seg_I2 from the two stretches after a call, each proved in its own file:
   i2_at_A (0x87e00, check_words_sI2x.v) and i2_at_H (0x87ea0, check_words_sI2h.v); their statements are frozen in
   check_words_sI2a.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_d check_words_ki check_words_sI2a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import check_words_sI2x check_words_sI2h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the seed at IK (0x87db8): the two bytes the stretch reads are the kind byte at the cursor s7 (atom 32) and the
   line pointer at the scratch slot sp1 + 152 (atom 33) *)
Definition k_regions : smem :=
[ YP09.mkRegion (Some 23%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
  YP09.mkRegion (Some 9%nat) 152 160 0 0 [YP09.mkChunk 152 (CVal 8 (SOff 33 0))] ].
Definition k_facts : facts :=
mkFacts [ (9%nat, mkAF (2^46) (2^47) 5); (22%nat, mkAF CW_SB CW_SB 0); (23%nat, mkAF 0x21160 0x21af0 0);
          (32%nat, mkAF 0 255 0); (33%nat, mkAF 4096 (2^47) 0) ] [] [].
Definition ssK : sstate := mkSS CW_PC_IK sr_atoms k_regions None k_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's hypotheses (check_words_c.v:124-141) this file uses, word for word *)
Hypothesis AATOI : forall fx0 : YK11.FPState, @aatoi_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae455 0xa6bf8 0x604158.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState, @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis RRO : RRO_P.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
(* the record facts of check_words_d.v (check_words_rf.v proves them from lib/B/Prog/CmdRecFacts.v) *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the value of a register at a symbolic state (check_words_sI2a.v's tactic, re-stated: an Ltac does not leave its
   section) *)
Ltac i2_preg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  | st_ok ?segs ?E ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh E ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst] in H
  end.

(* the seed's validity *)
Lemma i2_seedK : forall (W : world SEGS) (regsc : bvmap 5 word) memc sp1 p b line,
  getr regsc 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> getr regsc 22 = w64 CW_SB ->
  getr regsc 23 = w64 p -> 0x21160 <= p <= 0x21af0 -> 0 <= b <= 255 -> 4096 <= line <= 2 ^ 47 ->
  aval_mem (rdW W memc) p 1 b -> aval_mem (rdW W memc) (sp1 + 152) 8 line ->
  st_ok_pi SEGS VAL (Eimg (Ereg regsc [Z_to_bv 64 b; Z_to_bv 64 line])) ssK
    (restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + CW_PC_IK)) memc (seg_rom SEGS))).
Proof.
intros W regsc memc sp1 p b line H9 Hsp Hsp32 H22 H23 Hp Hb Hl Vb Vl.
set (E := Eimg (Ereg regsc [Z_to_bv 64 b; Z_to_bv 64 line])).
assert (E9 : ew E 9 = Z_to_bv 64 sp1) by (subst E; rewrite (i2_EE regsc _ 9%nat 9%bv eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 CW_SB) by (subst E; rewrite (i2_EE regsc _ 22%nat 22%bv eq_refl); exact H22).
assert (E23 : ew E 23 = Z_to_bv 64 p) by (subst E; rewrite (i2_EE regsc _ 23%nat 23%bv eq_refl); exact H23).
assert (E32 : ew E 32 = Z_to_bv 64 b) by (subst E; exact (i2_EX regsc _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 line) by (subst E; exact (i2_EX regsc _ 1 ltac:(unfold A_TEXT; lia))).
unfold ssK. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold k_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E23, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ p 0 1 (SOff 32 0) b);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact (i2_val_of_aval _ _ _ _ _ Vb).
  + rewrite E9, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ sp1 152 8 (SOff 33 0) line);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    exact (i2_val_of_aval _ _ _ _ _ Vl).
- apply pairwise_disjoint_of_extents. unfold k_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E23, E9, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok k_facts]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, E22, E23, E32, E33, !unsigned_lit_small by (unfold CW_SB; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  change (2 ^ 5) with 32. unfold CW_SB. repeat split; lia.
Qed.

(* the kept registers of two stretches in a row (i2_rk0 of check_words_sI2a.v is transitive) *)
Lemma i2k_rk0_trans : forall r1 r2 r3, i2_rk0 r1 r2 -> i2_rk0 r2 r3 -> i2_rk0 r1 r3.
Proof.
intros r1 r2 r3 (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12)
  (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12).
repeat split; congruence.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* IK (0x87db8): s4 := the kind byte at s7, s3 := ~s7, and the arms. The post is any Q; the two continuations are
   the state after the first atoi (0x87e00, listing 0x18d0) and ICMP (for '*' and 'L'). The trap site 0x87df4
   (s7 + a0 past 2^64 - 1) is refuted by the template's address range (i2_nowrap of check_words_sI2a.v). *)
Lemma i2_K_run : forall e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 Q,
  cw_ent B MT e -> cw_icommon B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args ->
  (j1 <= length (cw_tpl fn))%nat -> getr regs 23 = w64 (cw_tptr fn + Z.of_nat j1) ->
  item_of_a (skipn j1 (cw_tpl fn)) :: cw_parse (skipn (cw_cs (cw_tpl fn) j1) (skipn j1 (cw_tpl fn)))
    = skipn (Z.to_nat a) (PCW.call_items fn) ->
  (forall regs2 mem2 md2 b k, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) -> b <> 42 -> b <> 76 ->
     item_of_a (skipn j1 (cw_tpl fn)) = i2_kitem b k -> getr regs2 20 = w64 b -> getr regs2 10 = w64 k ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x18d0)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2 q wq, INV_ICMP B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a j1 q wq ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + CW_PC_ICMP)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + CW_PC_IK)) mem (seg_rom SEGS)) md) Q.
Proof.
intros e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 Q HE HC Hj1 H23 Heq KA KI.
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & H168 & Hiregs & Hcr & Hnth & Ha).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _ & H9 & H22 & _).
pose proof HE as ((_ & _ & _ & Hgp & Htp & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16848) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem md pos EV_JOINED fn HE HJ)
  as ([TB TN] & TRA & THV & TTL & Tlo & Thi & T8).
set (b := bv_unsigned (nth j1 (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
assert (Rb : 0 <= b < 256).
{ pose proof (bv_unsigned_in_range 8 (nth j1 (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R. }
assert (Hbv : aval_mem (rdW Wc mem) (cw_tptr fn + Z.of_nat j1) 1 b).
{ intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  rewrite (TB j1 ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
  unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !(Z.mod_small b 256) by lia. reflexivity. }
assert (Hbhd : b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))))
  by (subst b; rewrite i2_nth_hd by exact Hj1; reflexivity).
assert (Hb0 : b <> 0 -> (j1 < length (cw_tpl fn))%nat).
{ intros Hne. destruct (Nat.eq_dec j1 (length (cw_tpl fn))) as [Hq|Hne']; [|lia]. exfalso. apply Hne. subst b.
  rewrite Hq, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
set (p := cw_tptr fn + Z.of_nat j1) in *.
assert (Hp : 0x21160 <= p <= 0x21af0) by (subst p; lia).
pose proof Hlscr as (L152 & _).
pose proof Hline as (Hperm & Hl4096 & _ & Hlb & _).
assert (Hlin : In (line, cw_JN e) (ablocks B lyc Sc))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc Wc mem md line (cw_JN e) (proj1 HJ) Hlin)
  as (_ & _ & Hlceil & _ & _ & _ & HJN).
pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [Hrq _].
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
pose proof (i2_seedK Wc regs mem sp1 p b line H9 Hsp1 Hsp32 H22 H23 Hp ltac:(lia) ltac:(lia) Hbv L152) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) (mrestrict (w_H Wc) mem))
  by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) as HEI.
pose proof (i2_EE regs [Z_to_bv 64 b; Z_to_bv 64 line]) as EV.
pose proof (i2_HAE regs [Z_to_bv 64 b; Z_to_bv 64 line]) as HAE.
pose proof (i2_EX regs [Z_to_bv 64 b; Z_to_bv 64 line] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (i2_EX regs [Z_to_bv 64 b; Z_to_bv 64 line] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth] in E32, E33.
remember (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) as E0 eqn:HE0. clear HE0.
assert (E23 : ew E0 23 = Z_to_bv 64 p) by (rewrite (EV 23%nat 23%bv eq_refl); exact H23).
assert (U23 : U E0 (SOff 23 0) = p) by (apply U_atom; [exact E23 | lia]).
(* the facts every arm's continuation needs: the state at the end, from the registers kept and the memory *)
assert (KEEPST : forall regs2 mem2 md2,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem2 md2 EV_JOINED ->
  i2_rk0 regs regs2 -> getr regs2 19 = w64 (cw_not p) ->
  cw_mem_kept B (rdW Wc mem) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
  i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1).
{ intros regs2 mem2 md2 HJ2 HRK R19 HMK.
  exact (i2_st_of_ik B MT LAWS TL e lyc Sc Wc regs mem md regs2 mem2 md2 pos sp1 line c a fn args j1
    HE HC Hj1 H23 Heq HJ2 HRK R19 HMK). }
assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite G3; exact Hgp).
assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite G4; exact Htp).
(* 0x87db8 .. 0x87dc4: s4 := the byte, s3 := ~s7, `beq s4, 35` *)
paj_run_tok RUN HS HJ SHOK IBspan.
{ awr_ok_tac. }
set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* '#': a0 := 1, the trap site 0x87df4, then atoi(s7 + 1) *)
  rename Hc into Hc35. rewrite (i2_eq_lit E0 32 b 35 E32 ltac:(lia) ltac:(lia)) in Hc35. apply Z.eqb_eq in Hc35.
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* the trap site 0x87df4: s7 + 1 does not wrap *)
    exfalso. rewrite (i2_nowrap E0 23 p (SLit 1) 1 E23 ltac:(lia) ltac:(rewrite U_SLit; reflexivity) ltac:(lia)) in Hc.
    discriminate Hc.
  + (* 0x87df8 .. 0x87dfc: a0 := s7 + 1, atoi *)
    clear Hc.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    i2_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 23 10%bv _ 1 E23) in Ra0.
    i2_preg HS (1%bv : bv 5) Rra. change (SOff 240 6352) with (SOff A_TEXT 6352) in Rra.
    rewrite (codeptr_val E0 6352 HEI) in Rra.
    i2_preg HS (20%bv : bv 5) R20. apply (i2_reg_off _ _ 32 20%bv _ 0 E32) in R20. rewrite Z.add_0_r in R20.
    i2_preg HS (19%bv : bv 5) R19. rewrite (i2_den_not E0 23 p E23 ltac:(lia)) in R19.
    pose proof (i2_rk0_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
    cbn [ms_regs restrict] in HRK, R19, R20, Ra0, Rra.
    pmkst HS.
    assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms3) x = rdW Wc mem x)
      by (intros x Hx; rewrite K3, K2, K1 by exact Hx; reflexivity).
    pose proof HRK as (R2 & R3 & R4 & _).
    apply (i2_call_atoi B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
      e lyc Sc Wc (ms_regs ms3) (ms_mem ms3) mdv3 pos sp1 fn (S j1) 6352 Q HE HJ).
    * unfold spZ. rewrite R2. exact Hsp.
    * lia.
    * exact Hsp32.
    * rewrite R3. exact Hgp'.
    * rewrite R4. exact Htp'.
    * exact Rra.
    * lia.
    * reflexivity.
    * rewrite Ra0. unfold w64. f_equal. subst p. lia.
    * apply Hb0. lia.
    * intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
      apply (KA regs2 mem2 md2 b (atoi_a (skipn (S j1) (cw_tpl fn)))).
      -- apply (KEEPST regs2 mem2 md2 HJ2).
         ++ exact (i2k_rk0_trans _ _ _ HRK (proj1 (i2_rk_of_pres _ _ HP2))).
         ++ rewrite (proj2 (i2_rk_of_pres _ _ HP2)). exact R19.
         ++ intros x Hx H1 H2 H3. rewrite (HMK2 x Hx H1 H2 H3). exact (KT x Hx).
      -- exact Hbhd.
      -- lia.
      -- lia.
      -- rewrite (i2_item_A (skipn j1 (cw_tpl fn))) by (rewrite <- Hbhd; lia). rewrite <- Hbhd, Hc35.
         cbn [Z.eqb orb]. change ((35 =? 35) || (35 =? 63)) with true. cbv iota. rewrite i2_tl_skipn. reflexivity.
      -- etransitivity; [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20].
      -- exact Hk2.
- (* not '#' *)
  rename Hc into Hc35. rewrite (i2_eq_lit E0 32 b 35 E32 ltac:(lia) ltac:(lia)) in Hc35. apply Z.eqb_neq in Hc35.
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* '*': s5 := 0, on to ICMP with want_at = None *)
    rename Hc into Hc42. rewrite (i2_eq_lit E0 32 b 42 E32 ltac:(lia) ltac:(lia)) in Hc42. apply Z.eqb_eq in Hc42.
    paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
    { awr_ok_tac. }
    set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    i2_preg HS (21%bv : bv 5) R21. cbn [sv_denot] in R21.
    i2_preg HS (19%bv : bv 5) R19. rewrite (i2_den_not E0 23 p E23 ltac:(lia)) in R19.
    pose proof (i2_rk0_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
    cbn [ms_regs restrict] in HRK, R19, R21.
    pmkst HS.
    assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms3) x = rdW Wc mem x)
      by (intros x Hx; rewrite K3, K2, K1 by exact Hx; reflexivity).
    apply (KI (ms_regs ms3) (ms_mem ms3) mdv3 0 None).
    apply (i2_icmp B MT e lyc Sc Wc _ _ mdv3 pos sp1 line c a fn args j1 0 None).
    * exact (KEEPST _ _ _ HJ HRK R19 ltac:(intros x Hx _ _ _; exact (KT x Hx))).
    * exact R21.
    * reflexivity.
    * unfold item_of_a. cbv zeta. rewrite <- Hbhd, Hc42. reflexivity.
  + (* not '*' *)
    rename Hc into Hc42. rewrite (i2_eq_lit E0 32 b 42 E32 ltac:(lia) ltac:(lia)) in Hc42. apply Z.eqb_neq in Hc42.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* 'L': s5 = line, on to ICMP *)
      rename Hc into Hc76. rewrite (i2_eq_lit E0 32 b 76 E32 ltac:(lia) ltac:(lia)) in Hc76. apply Z.eqb_eq in Hc76.
      paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
      { awr_ok_tac. }
      set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
      i2_preg HS (21%bv : bv 5) R21. apply (i2_reg_off _ _ 33 21%bv _ 0 E33) in R21. rewrite Z.add_0_r in R21.
      i2_preg HS (19%bv : bv 5) R19. rewrite (i2_den_not E0 23 p E23 ltac:(lia)) in R19.
      pose proof (i2_rk0_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
      cbn [ms_regs restrict] in HRK, R19, R21.
      pmkst HS.
      assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
        by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
      pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwords & _).
      pose proof (KEEPST _ _ _ HJ HRK R19 ltac:(intros x Hx _ _ _; exact (KT x Hx))) as HST4.
      pose proof HST4 as (HC4 & _).
      pose proof HC4 as (_ & HL4 & _).
      pose proof HL4 as (_ & Hl4096' & _ & Hlb4 & _).
      apply (KI (ms_regs ms4) (ms_mem ms4) mdv4 line (Some (join_sp (e_ws e)))).
      apply (i2_icmp B MT e lyc Sc Wc _ _ mdv4 pos sp1 line c a fn args j1 line (Some (join_sp (e_ws e)))).
      -- exact HST4.
      -- exact R21.
      -- split; [split|].
         ++ exact Hlb4.
         ++ apply cw_join_nonul. intros k Hk. exact (proj2 (proj2 (proj2 (proj2 (Hwords k Hk))))).
         ++ split; [lia | left; split; reflexivity].
      -- unfold item_of_a. cbv zeta. rewrite <- Hbhd, Hc76. reflexivity.
    * (* a word item or '?': a0 := (s4 = '?'), the trap site 0x87df4, then atoi(s7 + a0) *)
      rename Hc into Hc76. rewrite (i2_eq_lit E0 32 b 76 E32 ltac:(lia) ltac:(lia)) in Hc76. apply Z.eqb_neq in Hc76.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
      psrr_branch_tok RUN BR HS SHOK IBspan.
      -- (* the trap site 0x87df4: s7 + (b = '?') does not wrap *)
         exfalso.
         rewrite (i2_nowrap E0 23 p (SAlu ALU_SLTU (SOff 32 (-63)) (SLit 1)) (if b =? 63 then 1 else 0) E23
           ltac:(lia) (i2_U_seq63 E0 32 b E32 ltac:(lia)) ltac:(destruct (b =? 63); lia)) in Hc.
         discriminate Hc.
      -- (* 0x87df8 .. 0x87dfc: a0 := s7 + (b = '?'), atoi *)
         clear Hc.
         paj_run_tok RUN HS HJ SHOK IBspan.
         { awr_ok_tac. }
         set (mdv5 := with_vm_backing _ _ _) in *. clearbody mdv5.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K5 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms5 end.
         set (jA := if b =? 63 then S j1 else j1).
         assert (HjA : (jA <= length (cw_tpl fn))%nat)
           by (subst jA; destruct (Z.eqb_spec b 63); [apply Hb0; lia | exact Hj1]).
         i2_preg HS (10%bv : bv 5) Ra0.
         rewrite (i2_den_U _ _ _ (i2_U_seqz E0 23 32 p b U23 E32 ltac:(lia) ltac:(lia) ltac:(lia))) in Ra0.
         i2_preg HS (1%bv : bv 5) Rra. change (SOff 240 6352) with (SOff A_TEXT 6352) in Rra.
         rewrite (codeptr_val E0 6352 HEI) in Rra.
         i2_preg HS (20%bv : bv 5) R20. apply (i2_reg_off _ _ 32 20%bv _ 0 E32) in R20. rewrite Z.add_0_r in R20.
         i2_preg HS (19%bv : bv 5) R19. rewrite (i2_den_not E0 23 p E23 ltac:(lia)) in R19.
         pose proof (i2_rk0_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as HRK.
         cbn [ms_regs restrict] in HRK, R19, R20, Ra0, Rra.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms5) x = rdW Wc mem x)
           by (intros x Hx; rewrite K5, K4, K3, K2, K1 by exact Hx; reflexivity).
         pose proof HRK as (R2 & R3 & R4 & _).
         apply (i2_call_atoi B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
           e lyc Sc Wc (ms_regs ms5) (ms_mem ms5) mdv5 pos sp1 fn jA 6352 Q HE HJ).
         ++ unfold spZ. rewrite R2. exact Hsp.
         ++ lia.
         ++ exact Hsp32.
         ++ rewrite R3. exact Hgp'.
         ++ rewrite R4. exact Htp'.
         ++ exact Rra.
         ++ lia.
         ++ reflexivity.
         ++ rewrite Ra0. unfold w64. f_equal. subst jA p. destruct (b =? 63); lia.
         ++ exact HjA.
         ++ intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
            apply (KA regs2 mem2 md2 b (atoi_a (skipn jA (cw_tpl fn)))).
            ** apply (KEEPST regs2 mem2 md2 HJ2).
               --- exact (i2k_rk0_trans _ _ _ HRK (proj1 (i2_rk_of_pres _ _ HP2))).
               --- rewrite (proj2 (i2_rk_of_pres _ _ HP2)). exact R19.
               --- intros x Hx H1 H2 H3. rewrite (HMK2 x Hx H1 H2 H3). exact (KT x Hx).
            ** exact Hbhd.
            ** exact Hc42.
            ** exact Hc76.
            ** rewrite (i2_item_A (skipn j1 (cw_tpl fn))) by (rewrite <- Hbhd; assumption). rewrite <- Hbhd.
               subst jA. rewrite (proj2 (Z.eqb_neq _ _) Hc35). cbn [orb].
               destruct (b =? 63); [rewrite i2_tl_skipn|]; reflexivity.
            ** etransitivity; [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact R20].
            ** exact Hk2.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the segment, from the stretch after the first atoi *)
Lemma seg_I2_of : i2_A_spec B MT ->
  forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) -> ST_IK B MT c a.
Proof.
intros HA c a HICMP. unfold ST_IK.
intros e lyc Sc Wc regsc memc mdc pos sp1 line j1 HE HI.
destruct HI as (fn & args & HC & Hj1 & H23 & Heq).
unfold cw_at.
apply (i2_K_run e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args j1 (cw_post B MT e) HE HC Hj1 H23 Heq).
- intros regs2 mem2 md2 b k HST2 Hb H42 H76 Hit H20 H10.
  exact (HA c a HICMP e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 b k HE HST2 Hb H42 H76 Hit H20 H10).
- intros regs2 mem2 md2 q wq HINV.
  exact (HICMP fx e lyc Sc Wc regs2 mem2 md2 pos sp1 line j1 q wq HE HINV).
Qed.

(* the segment (pass 4: the '#' arm goes on at the FP state snprintf returns, so ST_ICMP at every FP state) *)
Lemma seg_I2 : forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) -> ST_IK B MT c a.
Proof.
exact (seg_I2_of
  (i2_at_A B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on cmd_heap_tail_vis ZSH_cw cw_ro_unowned cmd_tail_vis
     (i2_at_H B MT ASNPRINTF LAWS TL RRO cmd_rec_cells ZSH_cw cw_ro_unowned cmd_tail_vis HB IMG))).
Qed.
End e.
End f.
End d.
