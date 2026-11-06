(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 370 of its 466 lines of code are new or changed and 1564 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command), segment I2: item a of call c, from the point IK (0x87b38,
   listing 0x1654) to ICMP, ICMP2 or the latch IL. The stretches after the calls are lemmas of their own
   (check_words_sI2a.v states them): i2_at_A (0x168c, check_words_sI2x.v), i2_at_H (0x1700, check_words_sI2h.v),
   and here i2_at_S (0x16ac) and i2_at_C (0x1778). This file proves the stretch from IK to the calls (i2_K_run)
   and assembles seg_I2. *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaSB PaLibF PaLibG PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtNumber RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel printf_facts_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
joined_c check_words_add_c check_words_chain_c check_words_pin_set_c sup_reply_code_c HarnessPropsA check_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_art check_words_ki check_words_sI2a.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_words_sI2h check_words_sI2x.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

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
(* the statement's hypotheses (check_words_c.v:88-104), word for word *)
Hypothesis HJOINED : tjoined_spec B MT.
Hypothesis HADD : tcheck_words_add_spec B MT.
Hypothesis HCHAIN : tcheck_words_chain_spec B MT.
Hypothesis HPIN : tcwps_spec B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASMALLOC0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASTRSPN : astrspn_realizes SEGS B (SIG CS___interceptor_trampoline_strspn) 0xa7098 0x6045d8.
Hypothesis ASTRCSPN : astrcspn_realizes SEGS B (SIG CS___interceptor_trampoline_strcspn) 0xa7098 0x6045d8.
Hypothesis ASTRCMP : astrcmp_realizes SEGS B (SIG CS___interceptor_trampoline_strcmp).
Hypothesis AATOI : aatoi_realizes SEGS B (SIG CS___interceptor_trampoline_atoi) 0xae8d5 0xa7098 0x6045d8.
Hypothesis ASNPRINTF : asnprintf_realizes SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa7098 0x6045d8.
(* the per-binary walk facts *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTFL : ameter_fs_laws MT.
Hypothesis RRO : RRO_P.
Hypothesis SIGP : cmd_sig_prog.
(* the record facts of lib/A/Prog/CmdRecFacts.v, carried until that file lands *)
Hypothesis cmd_rec_cells : cmd_rec_cells_P B.
Hypothesis cmd_rom_view_on : cmd_rom_view_on_P B.
Hypothesis cmd_heap_tail_vis : cmd_heap_tail_vis_P B.
Hypothesis cmd_prog_unowned : cmd_prog_unowned_P B.
Hypothesis ZSH_cw : CW_ZSH_P B.
Hypothesis cw_ro_unowned : cw_ro_unowned_P B.
Hypothesis cmd_tail_vis : cmd_tail_vis_P B.
Hypothesis cmd_got_rec : cmd_got_rec_P B.
(* the record and the image facts (walk hypotheses HB and IMG, cgif's names), for i2_at_H's snprintf step *)
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

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

(* ---------------------------------------------------------------------------------------------------------- *)
(* 0x16ac .. 0x16b0: s2 += the span, `j` to the latch *)
Lemma i2_at_S : i2_S_spec B MT.
Proof.
unfold i2_S_spec. intros c a HIL e lyc Sc Wc regs mem md pos sp1 line fn args j1 HE HST H10.
pose proof HST as (HC & Hj1 & H18 & Heq).
pose proof HC as (Hcore & _).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H23 & _).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem md pos EV_JOINED fn HE HJ)
  as (_ & _ & _ & _ & Tlo & Thi & T8).
set (cs := PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn))) in *.
assert (Hcs : (cs <= length (cw_tpl fn) - j1)%nat)
  by (pose proof (i2_cspn_le CW_SP1 (skipn j1 (cw_tpl fn))) as L; rewrite length_skipn in L; exact L).
pose proof (i2_seedS Wc regs mem H23) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [])) (mrestrict (w_H Wc) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regs [])) as HEI.
pose proof (i2_EE regs []) as EV.
pose proof (i2_HAE regs []) as HAE.
remember (Eimg (Ereg regs [])) as E0 eqn:HE0. clear HE0.
assert (U10 : U E0 (SOff 10 0) = Z.of_nat cs) by (apply U_atom; [rewrite (EV 10%nat 10%bv eq_refl); exact H10 | lia]).
assert (U18 : U E0 (SOff 18 0) = cw_tptr fn + Z.of_nat j1)
  by (apply U_atom; [rewrite (EV 18%nat 18%bv eq_refl); exact H18 | lia]).
paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_IL.
{ awr_ok_tac. }
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
pmkst HS.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
destruct (i2_rk0_pi _ _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)) as [HRK _].
i2_preg HS (18%bv : bv 5) R18.
rewrite (i2_den_U _ _ _ (i2_U_add E0 _ _ _ _ U10 U18 ltac:(lia))) in R18.
assert (HMK : cw_mem_kept B (rdW Wc mem) (rdW Wc (ms_mem ms1)) sp1 (frame_addr (e_ly e) 0 pos))
  by (intros x Hx _ _ _; rewrite K1 by exact Hx; reflexivity).
pose proof (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regs mem md (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line c a fn args
  HE HC HJ HRK HMK) as HC2.
destruct (i2_parse_next fn a j1 cs Heq) as [Hpar _].
assert (HINV : INV_IL B MT e lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line c a (j1 + cs)%nat).
{ exists fn, args. split; [exact HC2|]. split; [lia|]. split; [|exact Hpar].
  rewrite R18. unfold w64. f_equal. lia. }
change (BASE + 5964) with (BASE + CW_PC_IL).
exact (HIL e lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line (j1 + cs)%nat HE HINV).
Qed.

(* 0x1778 .. 0x1780: s2 += the span, `bnez s5` (s5 is a word pointer) to ICMP2 *)
Lemma i2_at_C : i2_C_spec B MT.
Proof.
unfold i2_C_spec. intros c a HICMP2 e lyc Sc Wc regs mem md pos sp1 line fn args j1 q y HE HST H10 H21 Hq Hqy Hws Hwant.
pose proof HST as (HC & Hj1 & H18 & Heq).
pose proof HC as (Hcore & _).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & _ & _ & _ & H9 & H23 & _).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem md pos EV_JOINED fn HE HJ)
  as (_ & _ & _ & _ & Tlo & Thi & T8).
set (cs := PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn))) in *.
assert (Hcs : (cs <= length (cw_tpl fn) - j1)%nat)
  by (pose proof (i2_cspn_le CW_SP1 (skipn j1 (cw_tpl fn))) as L; rewrite length_skipn in L; exact L).
pose proof (Zle_0_nat (length y)) as Hy0.
pose proof (i2_seedC Wc regs mem q H23 H21 ltac:(unfold PCEIL in *; lia)) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [])) (mrestrict (w_H Wc) mem)) by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regs [])) as HEI.
pose proof (i2_EE regs []) as EV.
pose proof (i2_HAE regs []) as HAE.
remember (Eimg (Ereg regs [])) as E0 eqn:HE0. clear HE0.
assert (U10 : U E0 (SOff 10 0) = Z.of_nat cs) by (apply U_atom; [rewrite (EV 10%nat 10%bv eq_refl); exact H10 | lia]).
assert (U18 : U E0 (SOff 18 0) = cw_tptr fn + Z.of_nat j1)
  by (apply U_atom; [rewrite (EV 18%nat 18%bv eq_refl); exact H18 | lia]).
paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP2.
{ awr_ok_tac. }
set (mdv := with_vm_backing _ _ _) in *. clearbody mdv.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
pmkst HS.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
destruct (i2_rk0_pi _ _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)) as [HRK R21].
cbn [ms_regs restrict] in HRK, R21.
i2_preg HS (18%bv : bv 5) R18.
rewrite (i2_den_U _ _ _ (i2_U_add E0 _ _ _ _ U10 U18 ltac:(lia))) in R18.
assert (HMK : cw_mem_kept B (rdW Wc mem) (rdW Wc (ms_mem ms1)) sp1 (frame_addr (e_ly e) 0 pos))
  by (intros x Hx _ _ _; rewrite K1 by exact Hx; reflexivity).
pose proof (cw_icommon_kept B MT LAWS TL e lyc Sc Wc regs mem md (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line c a fn args
  HE HC HJ HRK HMK) as HC2.
destruct (i2_parse_next fn a j1 cs Heq) as [Hpar Hnth].
assert (HINV : INV_ICMP2 B MT e lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line c a (j1 + cs)%nat q y).
{ exists fn, args, (item_of_a (skipn j1 (cw_tpl fn))).
  split; [exact HC2|]. split; [lia|]. split; [rewrite R18; unfold w64; f_equal; lia|].
  split; [exact Hnth|]. split; [exact Hpar|]. split; [rewrite R21; exact H21|].
  split; [|exact Hwant].
  apply (i2_wsrc_eq B e lyc Sc (rdW Wc mem) _ pos line q y); [exact K1 | lia | unfold PCEIL in *; lia | exact Hws]. }
change (BASE + 5928) with (BASE + CW_PC_ICMP2).
exact (HICMP2 e lyc Sc Wc (ms_regs ms1) (ms_mem ms1) mdv pos sp1 line (j1 + cs)%nat q y HE HINV).
Qed.
(* ---------------------------------------------------------------------------------------------------------- *)
(* IK (0x87b38): the kind byte s6 = the template byte at s2, and the four arms. The post is any Q; the three
   continuations are the states after atoi (0x168c), after strcspn (0x16ac) and at ICMP for 'L'. *)
Lemma i2_K_run : forall e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 Q,
  cw_ent B MT e -> i2_st B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  (forall regs2 mem2 md2 b k, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) -> b <> 42 -> b <> 76 ->
     item_of_a (skipn j1 (cw_tpl fn)) = i2_kitem b k -> getr regs2 22 = w64 b -> getr regs2 10 = w64 k ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x168c)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x16ac)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     getr regs2 21 = w64 line -> bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) = 76 ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + CW_PC_ICMP)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + CW_PC_IK)) mem (seg_rom SEGS)) md) Q.
Proof.
intros e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 Q HE HST KA KS KL.
pose proof HST as (HC & Hj1 & H18 & Heq).
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & Hiregs & Hcr & Hnth & Ha).
unfold cw_iregs in Hiregs. cbv zeta in Hiregs. destruct Hiregs as (H19 & H20 & H25 & H26 & H27 & H24).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _ & H9 & H23 & _).
pose proof HE as ((_ & _ & _ & Hgp & Htp & _) & _ & _ & _ & _ & HOBJ & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (V23 : VAL (A_OBJ 23) = 0x21120) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem md pos EV_JOINED fn HE HJ)
  as ([TB TN] & TRA & THV & TTL & Tlo & Thi & T8).
set (b := bv_unsigned (nth j1 (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))).
assert (Rb : 0 <= b < 256).
{ pose proof (bv_unsigned_in_range 8 (nth j1 (cw_tpl fn ++ [Z_to_bv 8 0]) (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R. }
assert (Hb : aval_mem (rdW Wc mem) (cw_tptr fn + Z.of_nat j1) 1 b).
{ intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r.
  rewrite (TB j1 ltac:(rewrite length_app; cbn [length]; lia)). f_equal.
  unfold le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite !(Z.mod_small b 256) by lia. reflexivity. }
assert (Hbhd : b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn)))) by (subst b; rewrite i2_nth_hd by exact Hj1; reflexivity).
assert (Hb0 : b <> 0 -> (j1 < length (cw_tpl fn))%nat).
{ intros Hne. destruct (Nat.eq_dec j1 (length (cw_tpl fn))) as [Hq|Hne']; [|lia]. exfalso. apply Hne. subst b.
  rewrite Hq, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
pose proof Hlscr as (L144 & _).
pose proof Hline as (Hperm & Hl4096 & _).
assert (Hlin : In (line, cw_JN e) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc Wc mem md line (cw_JN e) (proj1 HJ) Hlin) as (_ & _ & Hlceil & _ & _ & _ & HJN).
pose proof (req_size_pos (cw_JN e) ltac:(lia)) as [Hrq _].
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
pose proof (i2_seedK Wc regs mem sp1 (cw_tptr fn + Z.of_nat j1) b line H9 Hsp1 Hsp32 H23 H18 ltac:(lia) ltac:(lia)
  ltac:(lia) Hb L144) as HS.
assert (SHOK : sh_ok SEGS IBx [] (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) (mrestrict (w_H Wc) mem))
  by (unfold sh_ok; apply Forall_nil).
pose proof (Eimg_env (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) as HEI.
pose proof (i2_EE regs [Z_to_bv 64 b; Z_to_bv 64 line]) as EV.
pose proof (i2_HAE regs [Z_to_bv 64 b; Z_to_bv 64 line]) as HAE.
pose proof (i2_EX regs [Z_to_bv 64 b; Z_to_bv 64 line] 0 ltac:(unfold A_TEXT; lia)) as E32.
pose proof (i2_EX regs [Z_to_bv 64 b; Z_to_bv 64 line] 1 ltac:(unfold A_TEXT; lia)) as E33.
cbn [Nat.add nth] in E32, E33.
remember (Eimg (Ereg regs [Z_to_bv 64 b; Z_to_bv 64 line])) as E0 eqn:HE0. clear HE0.
assert (U18 : U E0 (SOff 18 0) = cw_tptr fn + Z.of_nat j1)
  by (apply U_atom; [rewrite (EV 18%nat 18%bv eq_refl); exact H18 | lia]).
(* the facts every arm's continuation needs: the state at the end, from the registers kept and the memory *)
assert (KEEPST : forall regs2 mem2 md2 (rT : bvmap 5 word) mT,
  ajournal SEGS B CHECK_WORDS_STK (cw_sp0 e) [] (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [(0, pos)]
    lyc Sc Wc mem2 md2 EV_JOINED ->
  cw_regs_kept regs rT -> getr rT 18 = getr regs 18 -> (forall x, 0 <= x < 2 ^ 64 -> rdW Wc mT x = rdW Wc mem x) ->
  aregs_preserved rT regs2 -> cw_mem_kept B (rdW Wc mT) (rdW Wc mem2) sp1 (frame_addr (e_ly e) 0 pos) ->
  i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1).
{ intros regs2 mem2 md2 rT mT HJ2 HRK R18 KT HP HMK.
  apply (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md regs2 mem2 md2 pos sp1 line c a fn args j1 HE HST HJ2).
  - exact (cw_regs_kept_trans _ _ _ HRK (cw_regs_kept_of_pres _ _ HP)).
  - rewrite <- R18. exact (HP 18 ltac:(unfold acallee_saved; lia)).
  - intros x Hx Hs Herr Hf. rewrite (HMK x Hx Hs Herr Hf). exact (KT x Hx). }
assert (Hgp' : getr regs 3 = w64 (as_gp B)) by (rewrite G3; exact Hgp).
assert (Htp' : getr regs 4 = w64 (as_tp B)) by (rewrite G4; exact Htp).
unfold cw_at.
(* 0x87b38 .. 0x87b40: s6 := the byte, `beq s6, 35` *)
paj_run_tok RUN HS HJ SHOK IBspan.
{ awr_ok_tac. }
set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
  pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
clear HF HFr HG.
lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
psrr_branch_tok RUN BR HS SHOK IBspan.
- (* '#': atoi(s2 + 1) *)
  rename Hc into Hc35. rewrite (i2_eq_lit E0 32 b 35 E32 ltac:(lia) ltac:(lia)) in Hc35. apply Z.eqb_eq in Hc35.
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
  i2_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 18 10%bv _ 1 (eq_trans (EV 18%nat 18%bv eq_refl) H18)) in Ra0.
  i2_preg HS (1%bv : bv 5) Rra. change (SOff 240 5772) with (SOff A_TEXT 5772) in Rra. rewrite (codeptr_val E0 5772 HEI) in Rra.
  i2_preg HS (22%bv : bv 5) R22. apply (i2_reg_off _ _ 32 22%bv _ 0 E32) in R22. rewrite Z.add_0_r in R22.
  destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
  pmkst HS.
  assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms2) x = rdW Wc mem x)
    by (intros x Hx; rewrite K2, K1 by exact Hx; reflexivity).
  pose proof HRK as (R2 & R3 & R4 & _).
  apply (i2_call_atoi B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis HB
    e lyc Sc Wc (ms_regs ms2) (ms_mem ms2) mdv2 pos sp1 fn (S j1) 5772 Q HE HJ).
  + unfold spZ. rewrite R2. exact Hsp.
  + lia.
  + exact Hsp32.
  + rewrite R3. exact Hgp'.
  + rewrite R4. exact Htp'.
  + exact Rra.
  + lia.
  + reflexivity.
  + rewrite Ra0. unfold w64. f_equal. lia.
  + apply Hb0. lia.
  + intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
    apply (KA regs2 mem2 md2 b (atoi_a (skipn (S j1) (cw_tpl fn)))).
    * exact (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2).
    * exact Hbhd.
    * lia.
    * lia.
    * rewrite (i2_item_A (skipn j1 (cw_tpl fn))) by (rewrite <- Hbhd; lia). rewrite <- Hbhd, Hc35.
      cbn [Z.eqb orb]. change ((35 =? 35) || (35 =? 63)) with true. cbv iota. rewrite i2_tl_skipn. reflexivity.
    * etransitivity; [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22].
    * exact Hk2.
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
  + (* '*': strcspn(s2, " "), then the latch *)
    rename Hc into Hc42. rewrite (i2_eq_lit E0 32 b 42 E32 ltac:(lia) ltac:(lia)) in Hc42. apply Z.eqb_eq in Hc42.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
    i2_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 18 10%bv _ 0 (eq_trans (EV 18%nat 18%bv eq_refl) H18)) in Ra0.
    rewrite Z.add_0_r in Ra0.
    i2_preg HS (11%bv : bv 5) Ra1. cbn [sv_denot] in Ra1. rewrite (HEI 264%nat ltac:(cbv; lia)), Z.add_0_r in Ra1.
    change (VAL 264%nat) with (VAL (A_OBJ 23)) in Ra1. rewrite V23 in Ra1.
    i2_preg HS (1%bv : bv 5) Rra. change (SOff 240 5804) with (SOff A_TEXT 5804) in Rra. rewrite (codeptr_val E0 5804 HEI) in Rra.
    destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
    pmkst HS.
    assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms3) x = rdW Wc mem x)
      by (intros x Hx; rewrite K3, K2, K1 by exact Hx; reflexivity).
    pose proof HRK as (R2 & R3 & R4 & _).
    apply (i2_call_cspn B MT ASTRCSPN LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
      e lyc Sc Wc (ms_regs ms3) (ms_mem ms3) mdv3 pos sp1 fn j1 5804 Q HE HJ).
    * unfold spZ. rewrite R2. exact Hsp.
    * lia.
    * exact Hsp32.
    * rewrite R3. exact Hgp'.
    * rewrite R4. exact Htp'.
    * exact Rra.
    * lia.
    * reflexivity.
    * exact Ra0.
    * exact Ra1.
    * exact Hj1.
    * intros regs2 mem2 md2 HJ2 HP2 Hcs2 HMK2.
      exact (KS regs2 mem2 md2 (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2) Hcs2).
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
    * (* 'L': s5 := line, on to ICMP *)
      rename Hc into Hc76. rewrite (i2_eq_lit E0 32 b 76 E32 ltac:(lia) ltac:(lia)) in Hc76. apply Z.eqb_eq in Hc76.
      paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
      { awr_ok_tac. }
      set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
      i2_preg HS (21%bv : bv 5) R21. apply (i2_reg_off _ _ 33 21%bv _ 0 E33) in R21. rewrite Z.add_0_r in R21.
      destruct (i2_rk_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
      pmkst HS.
      assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
        by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
      change (BASE + 5912) with (BASE + CW_PC_ICMP).
      apply (KL (ms_regs ms4) (ms_mem ms4) mdv4).
      -- apply (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md _ _ mdv4 pos sp1 line c a fn args j1 HE HST HJ HRK R18).
         intros x Hx _ _ _. exact (KT x Hx).
      -- exact R21.
      -- rewrite <- Hbhd. exact Hc76.
    * (* a word item: atoi(s2 + (s6 = '?')) *)
      rename Hc into Hc76. rewrite (i2_eq_lit E0 32 b 76 E32 ltac:(lia) ltac:(lia)) in Hc76. apply Z.eqb_neq in Hc76.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
      set (jA := if b =? 63 then S j1 else j1).
      assert (HjA : (jA <= length (cw_tpl fn))%nat) by (subst jA; destruct (Z.eqb_spec b 63); [apply Hb0; lia | exact Hj1]).
      i2_preg HS (10%bv : bv 5) Ra0.
      rewrite (i2_den_U _ _ _ (i2_U_seqz E0 _ b U18 E32 ltac:(lia) ltac:(lia) ltac:(lia))) in Ra0.
      i2_preg HS (1%bv : bv 5) Rra. change (SOff 240 5772) with (SOff A_TEXT 5772) in Rra. rewrite (codeptr_val E0 5772 HEI) in Rra.
      i2_preg HS (22%bv : bv 5) R22. apply (i2_reg_off _ _ 32 22%bv _ 0 E32) in R22. rewrite Z.add_0_r in R22.
      destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
      pmkst HS.
      assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
        by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
      pose proof HRK as (R2 & R3 & R4 & _).
      apply (i2_call_atoi B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis HB
        e lyc Sc Wc (ms_regs ms4) (ms_mem ms4) mdv4 pos sp1 fn jA 5772 Q HE HJ).
      -- unfold spZ. rewrite R2. exact Hsp.
      -- lia.
      -- exact Hsp32.
      -- rewrite R3. exact Hgp'.
      -- rewrite R4. exact Htp'.
      -- exact Rra.
      -- lia.
      -- reflexivity.
      -- rewrite Ra0. unfold w64. f_equal. subst jA. destruct (b =? 63); lia.
      -- exact HjA.
      -- intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
         apply (KA regs2 mem2 md2 b (atoi_a (skipn jA (cw_tpl fn)))).
         ++ exact (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2).
         ++ exact Hbhd.
         ++ exact Hc42.
         ++ exact Hc76.
         ++ rewrite (i2_item_A (skipn j1 (cw_tpl fn))) by (rewrite <- Hbhd; assumption). rewrite <- Hbhd.
            subst jA. rewrite (proj2 (Z.eqb_neq _ _) Hc35). cbn [orb].
            destruct (b =? 63); [rewrite i2_tl_skipn|]; reflexivity.
         ++ etransitivity; [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact R22].
         ++ exact Hk2.
Qed.
(* ---------------------------------------------------------------------------------------------------------- *)
(* the segment, from the stretches after the calls *)
Lemma seg_I2_of : i2_A_spec B MT -> i2_S_spec B MT ->
  forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) -> ST_ICMP2 B MT c a -> ST_IL B MT c a ->
  ST_IK B MT c a.
Proof.
intros HA HSs c a HICMP HICMP2 HIL. unfold ST_IK.
intros e lyc Sc Wc regsc memc mdc pos sp1 line j1 HE HI.
destruct HI as (fn & args & HC & Hj1 & H18 & Heq).
assert (HST : i2_st B MT e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args j1)
  by exact (conj HC (conj Hj1 (conj H18 Heq))).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwords & _).
unfold cw_at.
apply (i2_K_run e lyc Sc Wc regsc memc mdc pos sp1 line c a fn args j1 (cw_post B MT e) HE HST).
- intros regs2 mem2 md2 b k HST2 Hb H42 H76 Hit H22 H10.
  exact (HA c a HICMP HICMP2 HIL e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 b k HE HST2 Hb H42 H76 Hit H22 H10).
- intros regs2 mem2 md2 HST2 H10.
  exact (HSs c a HIL e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 HE HST2 H10).
- intros regs2 mem2 md2 HST2 H21 Hb76.
  destruct HST2 as (HC2 & Hj2 & H182 & Heq2).
  pose proof HC2 as (_ & HL2 & _).
  pose proof HL2 as (_ & Hl4096 & _ & Hlb & _).
  assert (HINV : INV_ICMP B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a j1 line (join_sp (e_ws e))).
  { exists fn, args. split; [exact HC2|]. split; [exact Hj2|]. split; [exact H182|]. split; [exact Heq2|].
    split; [exact H21|]. split.
    - split; [split; [exact Hlb|]|split; [lia | left; split; reflexivity]].
      apply cw_join_nonul. intros k Hk. exact (proj2 (proj2 (proj2 (proj2 (Hwords k Hk))))).
    - unfold item_of_a. cbv zeta. rewrite Hb76. reflexivity. }
  exact (HICMP fx e lyc Sc Wc regs2 mem2 md2 pos sp1 line j1 line (join_sp (e_ws e)) HE HINV).
Qed.
(* the segment (pass 4: the '#' arm goes on at the FP state snprintf returns, so ST_ICMP at every FP state) *)
Lemma seg_I2 : forall c a, (forall fx0 : YK11.FPState, ST_ICMP (fx := fx0) B MT c a) -> ST_ICMP2 B MT c a ->
  ST_IL B MT c a -> ST_IK B MT c a.
Proof.
exact (seg_I2_of
  (i2_at_A B MT ASTRCSPN AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on cmd_heap_tail_vis ZSH_cw cw_ro_unowned
     cmd_tail_vis
     (i2_at_H B MT ASNPRINTF LAWS TL RRO cmd_rec_cells ZSH_cw cw_ro_unowned cmd_tail_vis HB IMG)
     i2_at_S i2_at_C)
  i2_at_S).
Qed.
End e.
End f.
End d.
