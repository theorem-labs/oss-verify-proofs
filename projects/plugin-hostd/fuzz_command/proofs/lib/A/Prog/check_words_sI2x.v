(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment D of check_words' ASan walk (plugin-hostd/fuzz_command, 0x87c90 .. 0x87d64), in the form of lib/A/Prog/sup_reply_code.v and proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (seeds, symbolic runs, calls). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_words_sD.v, with its module names changed; 418 of its 508 lines of code are new or changed and 1570 lines of the source are left out. *)
(* check_words' ASan walk (plugin-hostd/fuzz_command), segment I2: the stretch after the first atoi, from 0x87b70
   (listing 0x168c), with the kind byte b in s6 and the word number k in a0.
     0x87b70 .. 0x87b7c  `bne s6, '?'`; for '?', `blt a0, read`: '?' with k >= read -> strcspn(s2, " ") at 0x87b8c,
                         back at 0x16ac (i2_S_spec).
     0x87b98 .. 0x87ba0  s5 := "" (0x21280); `bge a0, read`: k >= read -> ICMP (0x87bfc) with "".
     0x87ba4 .. 0x87bd0  k < read: s5 := w->w[k] through the two inline checks (the shadow of W + 16 and of &w->w[k],
                         removed by the seed's shadow entries); `bne s6, '#'`.
     0x87bdc .. 0x87be0  '#': atoi(w->w[k]), back at 0x1700 (i2_H_spec).
     0x87c50 .. 0x87c58  a word item ('?' or a number item) with k < read: strcspn(s2, " "), back at 0x1778
                         (i2_C_spec).
   The stretch is proved for any post Q from its four continuations (i2_A_go); i2_at_A instantiates it with
   check_words' post and the three frozen statements of check_words_sI2a.v. *)
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
Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).

Ltac i2x_preg HS r H :=
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
(* 0x168c: the stretch for any post Q, from its four continuations: after strcspn at 0x16ac ('?' with k >= read),
   ICMP with "" (k >= read, not '?'), after strcspn at 0x1778 (a word item with k < read, s5 = w->w[k]) and after
   atoi(w->w[k]) at 0x1700 ('#' with k < read) *)
Lemma i2_A_go : forall e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 b k Q,
  cw_ent B MT e -> i2_st B MT e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 ->
  b = bv_unsigned (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn))) -> b <> 42 -> b <> 76 ->
  item_of_a (skipn j1 (cw_tpl fn)) = i2_kitem b k ->
  getr regs 22 = w64 b -> getr regs 10 = w64 k ->
  (forall regs2 mem2 md2, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x16ac)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2 q y, INV_ICMP B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a j1 q y ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + CW_PC_ICMP)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2 q y, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     getr regs2 10 = w64 (Z.of_nat (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn)))) ->
     getr regs2 21 = w64 q -> 4096 <= q -> q + Z.of_nat (length y) + 1 <= PCEIL ->
     cw_wsrc B e lyc Sc (rdW Wc mem2) pos line q y ->
     want_at atoi_a (cw_read e) (e_ws e) (item_of_a (skipn j1 (cw_tpl fn))) = Some y ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x1778)) mem2 (seg_rom SEGS)) md2) Q) ->
  (forall regs2 mem2 md2, i2_st B MT e lyc Sc Wc regs2 mem2 md2 pos sp1 line c a fn args j1 ->
     item_of_a (skipn j1 (cw_tpl fn)) = PCW.INum k -> 0 <= k < cw_read e ->
     getr regs2 10 = w64 (atoi_a (nth (Z.to_nat k) (e_ws e) [])) ->
     SRr SEGS Wc (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 0x1700)) mem2 (seg_rom SEGS)) md2) Q) ->
  SRr SEGS Wc (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x168c)) mem (seg_rom SEGS)) md) Q.
Proof.
intros e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 b k Q HE HST Hbhd H42 H76 Hit H22 H10 KS KI KC KH.
pose proof HST as (HC & Hj1 & H18 & Heq).
pose proof HC as (Hcore & Hline & Hlscr & Hcscr & Hiregs & Hcr & Hnth & Ha).
unfold cw_iregs in Hiregs. cbv zeta in Hiregs. destruct Hiregs as (H19 & H20 & H25 & H26 & H27 & H24).
pose proof Hcore as Hcore'. unfold cw_core in Hcore'. cbv zeta in Hcore'.
destruct Hcore' as (HJ & Hsp & Hsp32 & Hspr & G3 & G4 & _ & H9 & H23 & _ & _ & _ & _ & V152 & _).
pose proof HE as ((_ & _ & _ & Hgp & Htp & _) & _ & _ & _ & _ & HOBJ & HspW & HWhi & _ & Harr64 & _).
assert (HspW' : cw_sp0 e <= e_Wd e + 16) by exact HspW.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
pose proof Hastk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
assert (WS : CHECK_WORDS_STK = 16800) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (PC : PCEIL = 0x7fffff800000) by reflexivity.
assert (V23 : VAL (A_OBJ 23) = 0x21120) by (rewrite HOBJ by (vm_compute; lia); vm_compute; reflexivity).
pose proof Hlscr as (_ & _ & _ & _ & _ & _ & _ & L88 & L96 & L104 & _).
pose proof Hline as (Hperm & _).
assert (Hsub : forall bk, In bk (ablocks B (e_ly e) (e_S e)) -> In bk (ablocks B lyc Sc))
  by (intros bk Hbk; apply (Permutation_in _ (Permutation_sym Hperm)); right; exact Hbk).
destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc mem md pos EV_JOINED fn HE HJ)
  as (_ & _ & _ & _ & Tlo & Thi & T8).
destruct (i2_parse_next fn a j1 (PCspn.cspn_len CW_SP1 (skipn j1 (cw_tpl fn))) Heq) as [_ Hnit].
rewrite Hit in Hnit.
pose proof (i2_kitem_k b k (i2_item_k fn (Z.to_nat a) _ Hnit)) as Hk3.
assert (Rb : 0 <= b < 256).
{ rewrite Hbhd. pose proof (bv_unsigned_in_range 8 (hd (Z_to_bv 8 0) (skipn j1 (cw_tpl fn)))) as R.
  change (bv_modulus 8) with 256 in R. exact R. }
assert (Hrd : 0 <= cw_read e <= 64) by (unfold cw_read, cw_n; lia).
assert (Hrdn : cw_read e <= Z.of_nat (length (e_ws e))) by (unfold cw_read, cw_n; lia).
assert (Hsp1 : 2 ^ 46 <= sp1 <= 2 ^ 47) by lia.
assert (HW16 : 2 ^ 46 <= e_Wd e + 16 <= 2 ^ 47 - 16) by lia.
assert (HW16s : sp1 + 160 <= e_Wd e + 16) by lia.
assert (Hp : 0x21120 <= cw_tptr fn + Z.of_nat j1 <= 0x21ab0) by lia.
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
destruct (Z_lt_ge_dec k (cw_read e)) as [Hkr | Hkr].
- (* k < read: the word w->w[k] is read *)
  assert (Hkn : (Z.to_nat k < length (e_ws e))%nat) by (unfold cw_read, cw_n in Hkr; lia).
  destruct (cw_word_at B MT LAWS e lyc Sc Wc mem md pos EV_JOINED (Z.to_nat k) HE HJ Hsub Hkn)
    as (VW & _ & (pA & mA & HinA & HpA & HmA) & Vq & Hwq64 & (pW & mW & HinW & HpW & HmW) & _).
  rewrite Z2Nat.id in Vq by lia.
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem md pA mA HAR HinA) as (_ & HpA4 & HpAc & HappA & _ & _ & HmA0).
  destruct (al_blocks _ _ LAWS lyc Sc Wc mem md pW mW HAR HinW) as (_ & HpW4 & HpWc & _ & _ & _ & HmW0).
  pose proof (req_size_pos mA ltac:(lia)) as [_ HrqA].
  pose proof (req_size_pos mW ltac:(lia)) as [_ HrqW].
  set (wq := nth (Z.to_nat k) (e_wp e) 0) in *.
  set (y := nth (Z.to_nat k) (e_ws e) []) in *.
  assert (Hq : 4096 <= e_arr e + 8 * k /\ e_arr e + 8 * k + 8 <= alloc_ceiling) by lia.
  assert (Hwq : 4096 <= wq /\ wq + Z.of_nat (length y) + 1 <= alloc_ceiling) by lia.
  pose proof (i2_seedA true Wc regs mem sp1 (cw_tptr fn + Z.of_nat j1) b k (e_Wd e + 16) (cw_read e) (e_arr e)
    (e_arr e + 8 * k) wq H9 Hsp1 Hsp32 H23 H10 Hk3 H18 Hp H22 ltac:(lia) HW16 HW16s Hrd Harr64
    ltac:(rewrite PC; lia) ltac:(lia) ltac:(rewrite PC; lia) L88 L96 L104 V152 (fun _ => conj eq_refl (conj VW Vq))) as HS.
  assert (HRA : true = true -> range_addressable (rdW Wc mem) SHADOW_OFF (e_Wd e + 16) 8 /\
    range_addressable (rdW Wc mem) SHADOW_OFF (e_arr e + 8 * k) 8 /\ in_app (e_arr e + 8 * k) 8).
  { intros _. split; [|split].
    - apply (i2_stk_addressable B lyc Sc Wc mem md (e_Wd e + 16) 8 HAR); [rewrite Eslo; lia | rewrite Eshi; lia | lia].
    - apply (range_addressable_of_block SEGS B LAWS lyc Sc Wc mem md pA mA); [exact HAR | exact HinA | lia | lia].
    - apply (in_app_sub pA (req_size mA)); [exact HappA | lia | lia | lia]. }
  pose proof (i2_shokA true Wc regs mem (e_Wd e + 16) (cw_read e) (e_arr e) (e_arr e + 8 * k) wq H23 HW16
    ltac:(rewrite PC; lia) HRA) as SHOK.
  pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) as HEI.
  pose proof (i2_EE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq])) as EV.
  pose proof (i2_HAE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq])) as HAE.
  assert (E33 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 33 =
    Z_to_bv 64 (cw_read e)) by exact (i2_EX regs _ 1 ltac:(unfold A_TEXT; lia)).
  assert (E36 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) 36 =
    Z_to_bv 64 wq) by exact (i2_EX regs _ 4 ltac:(unfold A_TEXT; lia)).
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; e_arr e + 8 * k; wq]))) as E0 eqn:HE0.
  clear HE0.
  pose proof (eq_trans (EV 10%nat 10%bv eq_refl) H10) as E10.
  pose proof (eq_trans (EV 22%nat 22%bv eq_refl) H22) as E22.
  (* 0x87b70 .. 0x87b74: `bne s6, '?'` *)
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  (* the arm of a word item with k < read at 0x87bd8: strcspn(s2, " ") and the continuation at 0x1778; the
     first goal is the not-'#' arm, whose b <> 35 the branch gives *)
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* not '?': 0x87b98 .. 0x87ba0, `bge a0, read` *)
    rename Hc into Hc63. rewrite (i2_ne_lit E0 22 b 63 E22 ltac:(lia) ltac:(lia)) in Hc63.
    apply negb_true_iff, Z.eqb_neq in Hc63.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* k >= read: not this case *)
      rename Hc into Hcg. rewrite (i2_ge E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcg.
      apply negb_true_iff, Z.ltb_ge in Hcg. lia.
    * (* 0x87ba4 .. 0x87bd8: w->w[k] through the two inline checks, `bne s6, '#'` *)
      clear Hc.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      psrr_branch_tok RUN BR HS SHOK IBspan.
      -- (* a word item: 0x87c50 .. 0x87c58, strcspn(s2, " ") *)
         rename Hc into Hc35. rewrite (i2_ne_lit E0 22 b 35 E22 ltac:(lia) ltac:(lia)) in Hc35.
         apply negb_true_iff, Z.eqb_neq in Hc35.
         paj_run_tok RUN HS HJ SHOK IBspan.
         { awr_ok_tac. }
         set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
         i2x_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 18 10%bv _ 0 (eq_trans (EV 18%nat 18%bv eq_refl) H18)) in Ra0.
         rewrite Z.add_0_r in Ra0.
         i2x_preg HS (11%bv : bv 5) Ra1. apply (i2_reg_off _ _ 24 11%bv _ 0 (eq_trans (EV 24%nat 24%bv eq_refl) H24)) in Ra1.
         rewrite Z.add_0_r in Ra1.
         i2x_preg HS (21%bv : bv 5) R21. apply (i2_reg_off _ _ 36 21%bv _ 0 E36) in R21. rewrite Z.add_0_r in R21.
         i2x_preg HS (1%bv : bv 5) Rra. change (SOff 240 6008) with (SOff A_TEXT 6008) in Rra.
         rewrite (codeptr_val E0 6008 HEI) in Rra.
         destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
           by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
         pose proof HRK as (R2 & R3 & R4 & _).
         apply (i2_call_cspn B MT ASTRCSPN LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
           e lyc Sc Wc (ms_regs ms4) (ms_mem ms4) mdv4 pos sp1 fn j1 6008 Q HE HJ).
         ++ unfold spZ. rewrite R2. exact Hsp.
         ++ lia.
         ++ exact Hsp32.
         ++ rewrite R3. exact Hgp'.
         ++ rewrite R4. exact Htp'.
         ++ exact Rra.
         ++ lia.
         ++ reflexivity.
         ++ exact Ra0.
         ++ exact Ra1.
         ++ exact Hj1.
         ++ intros regs2 mem2 md2 HJ2 HP2 Hcs2 HMK2.
            destruct (cw_word_at B MT LAWS e lyc Sc Wc mem2 md2 pos EV_JOINED (Z.to_nat k) HE HJ2 Hsub Hkn)
              as (_ & _ & _ & _ & _ & HblkW2 & HSTR2).
            apply (KC regs2 mem2 md2 wq y (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2) Hcs2).
            ** etransitivity; [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21].
            ** lia.
            ** rewrite PC. lia.
            ** split; [exact HSTR2|]. split; [lia|]. right; right; right.
               exists (Z.to_nat k). split; [exact Hkn|]. split; [reflexivity|]. split; [reflexivity | exact HblkW2].
            ** rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 35) Hc35), (proj2 (Z.eqb_neq b 63) Hc63).
               cbn [want_at]. rewrite (proj2 (Z.ltb_lt k (cw_read e)) Hkr). reflexivity.
      -- (* '#': 0x87bdc .. 0x87be0, atoi(w->w[k]) *)
         rename Hc into Hc35. rewrite (i2_ne_lit E0 22 b 35 E22 ltac:(lia) ltac:(lia)) in Hc35.
         apply negb_false_iff, Z.eqb_eq in Hc35.
         paj_run_tok RUN HS HJ SHOK IBspan.
         { awr_ok_tac. }
         set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
         i2x_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 36 10%bv _ 0 E36) in Ra0. rewrite Z.add_0_r in Ra0.
         i2x_preg HS (1%bv : bv 5) Rra. change (SOff 240 5888) with (SOff A_TEXT 5888) in Rra.
         rewrite (codeptr_val E0 5888 HEI) in Rra.
         destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
           by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
         pose proof HRK as (R2 & R3 & R4 & _).
         apply (i2_call_atoi_w B MT AATOI LAWS TL RRO cmd_rec_cells cmd_rom_view_on cmd_heap_tail_vis
           e lyc Sc Wc (ms_regs ms4) (ms_mem ms4) mdv4 pos sp1 (Z.to_nat k) 5888 Q HE HJ Hsub Hkn).
         ++ unfold spZ. rewrite R2. exact Hsp.
         ++ lia.
         ++ exact Hsp32.
         ++ rewrite R3. exact Hgp'.
         ++ rewrite R4. exact Htp'.
         ++ exact Rra.
         ++ lia.
         ++ reflexivity.
         ++ exact Ra0.
         ++ intros regs2 mem2 md2 HJ2 HP2 Hk2 HMK2.
            apply (KH regs2 mem2 md2 (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2)).
            ** rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_eq b 35) Hc35). reflexivity.
            ** lia.
            ** exact Hk2.
  + (* '?': 0x87b7c, `blt a0, read` *)
    rename Hc into Hc63. rewrite (i2_ne_lit E0 22 b 63 E22 ltac:(lia) ltac:(lia)) in Hc63.
    apply negb_false_iff, Z.eqb_eq in Hc63.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* k < read: 0x87b98 .. 0x87bd8, w->w[k] through the two inline checks, `bne s6, '#'` *)
      clear Hc.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      psrr_branch_tok RUN BR HS SHOK IBspan.
      -- (* '?' is not '#': 0x87c50 .. 0x87c58, strcspn(s2, " ") *)
         rename Hc into Hc35. rewrite (i2_ne_lit E0 22 b 35 E22 ltac:(lia) ltac:(lia)) in Hc35.
         apply negb_true_iff, Z.eqb_neq in Hc35.
         paj_run_tok RUN HS HJ SHOK IBspan.
         { awr_ok_tac. }
         set (mdv4 := with_vm_backing _ _ _) in *. clearbody mdv4.
         lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
           pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K4 end.
         clear HF HFr HG.
         lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms4 end.
         i2x_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 18 10%bv _ 0 (eq_trans (EV 18%nat 18%bv eq_refl) H18)) in Ra0.
         rewrite Z.add_0_r in Ra0.
         i2x_preg HS (11%bv : bv 5) Ra1. apply (i2_reg_off _ _ 24 11%bv _ 0 (eq_trans (EV 24%nat 24%bv eq_refl) H24)) in Ra1.
         rewrite Z.add_0_r in Ra1.
         i2x_preg HS (21%bv : bv 5) R21. apply (i2_reg_off _ _ 36 21%bv _ 0 E36) in R21. rewrite Z.add_0_r in R21.
         i2x_preg HS (1%bv : bv 5) Rra. change (SOff 240 6008) with (SOff A_TEXT 6008) in Rra.
         rewrite (codeptr_val E0 6008 HEI) in Rra.
         destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
         pmkst HS.
         assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms4) x = rdW Wc mem x)
           by (intros x Hx; rewrite K4, K3, K2, K1 by exact Hx; reflexivity).
         pose proof HRK as (R2 & R3 & R4 & _).
         apply (i2_call_cspn B MT ASTRCSPN LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
           e lyc Sc Wc (ms_regs ms4) (ms_mem ms4) mdv4 pos sp1 fn j1 6008 Q HE HJ).
         ++ unfold spZ. rewrite R2. exact Hsp.
         ++ lia.
         ++ exact Hsp32.
         ++ rewrite R3. exact Hgp'.
         ++ rewrite R4. exact Htp'.
         ++ exact Rra.
         ++ lia.
         ++ reflexivity.
         ++ exact Ra0.
         ++ exact Ra1.
         ++ exact Hj1.
         ++ intros regs2 mem2 md2 HJ2 HP2 Hcs2 HMK2.
            destruct (cw_word_at B MT LAWS e lyc Sc Wc mem2 md2 pos EV_JOINED (Z.to_nat k) HE HJ2 Hsub Hkn)
              as (_ & _ & _ & _ & _ & HblkW2 & HSTR2).
            apply (KC regs2 mem2 md2 wq y (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2) Hcs2).
            ** etransitivity; [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21].
            ** lia.
            ** rewrite PC. lia.
            ** split; [exact HSTR2|]. split; [lia|]. right; right; right.
               exists (Z.to_nat k). split; [exact Hkn|]. split; [reflexivity|]. split; [reflexivity | exact HblkW2].
            ** rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 35) Hc35), (proj2 (Z.eqb_eq b 63) Hc63).
               cbn [want_at]. rewrite (proj2 (Z.ltb_lt k (cw_read e)) Hkr). reflexivity.
      -- (* '#' is not '?': not this case *)
         rename Hc into Hc35. rewrite (i2_ne_lit E0 22 b 35 E22 ltac:(lia) ltac:(lia)) in Hc35.
         apply negb_false_iff, Z.eqb_eq in Hc35. lia.
    * (* k >= read: not this case *)
      rename Hc into Hcl. rewrite (i2_lt E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcl.
      apply Z.ltb_ge in Hcl. lia.
- (* k >= read: no word is read; the seed's high regions and shadow entries are absent *)
  pose proof (i2_seedA false Wc regs mem sp1 (cw_tptr fn + Z.of_nat j1) b k (e_Wd e + 16) (cw_read e) (e_arr e)
    4096 4096 H9 Hsp1 Hsp32 H23 H10 Hk3 H18 Hp H22 ltac:(lia) HW16 HW16s Hrd Harr64
    ltac:(rewrite PC; lia) ltac:(lia) ltac:(rewrite PC; lia) L88 L96 L104 V152 ltac:(intros Hft; discriminate Hft)) as HS.
  pose proof (i2_shokA false Wc regs mem (e_Wd e + 16) (cw_read e) (e_arr e) 4096 4096 H23 HW16
    ltac:(rewrite PC; lia) ltac:(intros Hft; discriminate Hft)) as SHOK.
  pose proof (Eimg_env (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; 4096; 4096]))) as HEI.
  pose proof (i2_EE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; 4096; 4096])) as EV.
  pose proof (i2_HAE regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; 4096; 4096])) as HAE.
  assert (E33 : ew (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; 4096; 4096]))) 33 =
    Z_to_bv 64 (cw_read e)) by exact (i2_EX regs _ 1 ltac:(unfold A_TEXT; lia)).
  remember (Eimg (Ereg regs (map (Z_to_bv 64) [e_Wd e + 16; cw_read e; e_arr e; 4096; 4096]))) as E0 eqn:HE0.
  clear HE0.
  pose proof (eq_trans (EV 10%nat 10%bv eq_refl) H10) as E10.
  pose proof (eq_trans (EV 22%nat 22%bv eq_refl) H22) as E22.
  (* 0x87b70 .. 0x87b74: `bne s6, '?'` *)
  paj_run_tok RUN HS HJ SHOK IBspan.
  { awr_ok_tac. }
  set (mdv1 := with_vm_backing _ _ _) in *. clearbody mdv1.
  lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
    pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K1 end.
  clear HF HFr HG.
  lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms1 end.
  psrr_branch_tok RUN BR HS SHOK IBspan.
  + (* not '?': 0x87b98 .. 0x87ba0, s5 := "", `bge a0, read` *)
    rename Hc into Hc63. rewrite (i2_ne_lit E0 22 b 63 E22 ltac:(lia) ltac:(lia)) in Hc63.
    apply negb_true_iff, Z.eqb_neq in Hc63.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* k >= read: on to ICMP (0x87bfc) with "" *)
      clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK IBspan CW_PC_ICMP.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      i2x_preg HS (21%bv : bv 5) R21. cbn [sv_denot] in R21.
      destruct (i2_rk_pi _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
      pmkst HS.
      assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms3) x = rdW Wc mem x)
        by (intros x Hx; rewrite K3, K2, K1 by exact Hx; reflexivity).
      change (BASE + 5912) with (BASE + CW_PC_ICMP).
      pose proof (i2_st_kept B MT LAWS TL e lyc Sc Wc regs mem md _ _ mdv3 pos sp1 line c a fn args j1 HE HST HJ HRK R18
        ltac:(intros x Hx _ _ _; exact (KT x Hx))) as HST3.
      destruct HST3 as (HC3 & Hj3 & H183 & Heq3).
      destruct (cw_tpl_at B MT ZSH_cw cw_ro_unowned cmd_tail_vis e lyc Sc Wc (ms_mem ms3) mdv3 pos EV_JOINED 3 HE HJ)
        as (T3 & _).
      apply (KI (ms_regs ms3) (ms_mem ms3) mdv3 0x21280 []).
      exists fn, args. split; [exact HC3|]. split; [exact Hj3|]. split; [exact H183|]. split; [exact Heq3|].
      split; [exact R21|]. split.
      -- split; [exact T3|]. split; [lia|]. right; left. split; reflexivity.
      -- rewrite Hit. unfold i2_kitem. rewrite (proj2 (Z.eqb_neq b 63) Hc63).
         destruct (b =? 35); cbn [want_at]; rewrite (proj2 (Z.ltb_ge k (cw_read e)) ltac:(lia)); reflexivity.
    * (* k < read: not this case *)
      rename Hc into Hcg. rewrite (i2_ge E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcg.
      apply negb_false_iff, Z.ltb_lt in Hcg. lia.
  + (* '?': 0x87b7c, `blt a0, read` *)
    rename Hc into Hc63. rewrite (i2_ne_lit E0 22 b 63 E22 ltac:(lia) ltac:(lia)) in Hc63.
    apply negb_false_iff, Z.eqb_eq in Hc63.
    paj_run_tok RUN HS HJ SHOK IBspan.
    { awr_ok_tac. }
    set (mdv2 := with_vm_backing _ _ _) in *. clearbody mdv2.
    lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
      pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K2 end.
    clear HF HFr HG.
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?m) |- _ => rename m into ms2 end.
    psrr_branch_tok RUN BR HS SHOK IBspan.
    * (* k < read: not this case *)
      rename Hc into Hcl. rewrite (i2_lt E0 10 33 k (cw_read e) E10 E33 ltac:(lia) ltac:(lia)) in Hcl.
      apply Z.ltb_lt in Hcl. lia.
    * (* k >= read: 0x87b80 .. 0x87b8c, strcspn(s2, " ") *)
      clear Hc.
      paj_run_tok RUN HS HJ SHOK IBspan.
      { awr_ok_tac. }
      set (mdv3 := with_vm_backing _ _ _) in *. clearbody mdv3.
      lazymatch goal with HFr : frame_of _ ?rs (mrestrict _ ?m1) (mrestrict _ ?m2) |- _ =>
        pose proof (i2_kept_ro _ rs _ m1 m2 HFr ltac:(vm_compute; reflexivity)) as K3 end.
      clear HF HFr HG.
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into ms3 end.
      i2x_preg HS (10%bv : bv 5) Ra0. apply (i2_reg_off _ _ 18 10%bv _ 0 (eq_trans (EV 18%nat 18%bv eq_refl) H18)) in Ra0.
      rewrite Z.add_0_r in Ra0.
      i2x_preg HS (11%bv : bv 5) Ra1. cbn [sv_denot] in Ra1. rewrite (HEI 264%nat ltac:(cbv; lia)), Z.add_0_r in Ra1.
      change (VAL 264%nat) with (VAL (A_OBJ 23)) in Ra1. rewrite V23 in Ra1.
      i2x_preg HS (1%bv : bv 5) Rra. change (SOff 240 5804) with (SOff A_TEXT 5804) in Rra.
      rewrite (codeptr_val E0 5804 HEI) in Rra.
      destruct (i2_rk_st _ _ _ regs _ HS HAE ltac:(vm_compute; reflexivity)) as [HRK R18]. cbn [ms_regs restrict] in HRK, R18.
      pmkst HS.
      assert (KT : forall x, 0 <= x < 2 ^ 64 -> rdW Wc (ms_mem ms3) x = rdW Wc mem x)
        by (intros x Hx; rewrite K3, K2, K1 by exact Hx; reflexivity).
      pose proof HRK as (R2 & R3 & R4 & _).
      apply (i2_call_cspn B MT ASTRCSPN LAWS TL RRO cmd_rec_cells cmd_rom_view_on ZSH_cw cw_ro_unowned cmd_tail_vis
        e lyc Sc Wc (ms_regs ms3) (ms_mem ms3) mdv3 pos sp1 fn j1 5804 Q HE HJ).
      -- unfold spZ. rewrite R2. exact Hsp.
      -- lia.
      -- exact Hsp32.
      -- rewrite R3. exact Hgp'.
      -- rewrite R4. exact Htp'.
      -- exact Rra.
      -- lia.
      -- reflexivity.
      -- exact Ra0.
      -- exact Ra1.
      -- exact Hj1.
      -- intros regs2 mem2 md2 HJ2 HP2 Hcs2 HMK2.
         exact (KS regs2 mem2 md2 (KEEPST regs2 mem2 md2 _ _ HJ2 HRK R18 KT HP2 HMK2) Hcs2).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* the frozen statement of the stretch (check_words_sI2a.v's i2_A_spec), from those of its three continuations *)
Lemma i2_at_A : i2_H_spec B MT -> i2_S_spec B MT -> i2_C_spec B MT -> i2_A_spec B MT.
Proof.
intros HH HS HCs. unfold i2_A_spec.
intros c a HICMP HICMP2 HIL e lyc Sc Wc regs mem md pos sp1 line fn args j1 b k HE HST Hb H42 H76 Hit H22 H10.
exact (i2_A_go e lyc Sc Wc regs mem md pos sp1 line c a fn args j1 b k (cw_post B MT e) HE HST Hb H42 H76 Hit H22 H10
  (fun regs2 mem2 md2 HST2 Hcs => HS c a HIL e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 HE HST2 Hcs)
  (fun regs2 mem2 md2 q y HINV => HICMP fx e lyc Sc Wc regs2 mem2 md2 pos sp1 line j1 q y HE HINV)
  (fun regs2 mem2 md2 q y HST2 Hcs H21 Hq Hqy Hws Hwant =>
     HCs c a HICMP2 e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 q y HE HST2 Hcs H21 Hq Hqy Hws Hwant)
  (fun regs2 mem2 md2 HST2 Hnum Hkr Hat =>
     HH c a HICMP e lyc Sc Wc regs2 mem2 md2 pos sp1 line fn args j1 k HE HST2 Hnum Hkr Hat)).
Qed.

End e.
End f.
End d.
