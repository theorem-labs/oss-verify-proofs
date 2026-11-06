(* check_as_written, the epilogue (fs.asan 0x819a8 .. 0x819cc): from the state FSW_caw_back.cawb_mid gives at the bcmp
   return 0x819a8 (a0 = 0, equal bytes) or at the join 0x819ac, to check_as_written_spec's post cawb_post:
   - 0x819a8 `bnez a0, 0x819d0` falls through (a0 = 0, an assumed branch condition of the symbolic state);
   - 0x819ac `mv a0, s2` (a0 = want), 0x819b0 .. 0x819c4 the six reloads of ra, s0 .. s4 from the frame (the extra atoms
     37 .. 32 of FSW_caw_back.cawb_cs), 0x819c8 `addi sp, sp, 48`;
   - 0x819cc `j 0x53070`, the tail call of __wrap_free (PC_free = pc_wrap_free (as_code B), RTf: FsRt.fr_free's
     type), whose return is check_as_written's: FSW_caw_back.cawb_tail from there.
   The reloads are frame-spill loads with no ASan check (fs.asan listing 0x819b0 .. 0x819c4: plain `ld` off sp), so the
   run is the plain engine (FSW_K fsw_aj_runU) over the frame region [sp, sp + 48) at atom 2 holding cawb_cs.
   Rule 24: proves function check_as_written (segment: epilogue cawb_epi); none ported, written new; templates only:
   FSW_K.v fsw_after_callU (the resumed-state builder), FSW_caw_tail.v (the run form), FSW_caw_back.v cawb_tail.
   Section hypotheses: FSW_caw_back.v's Section W, by name (of the runtime, RTf only). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w AF0l FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_rres FSW_rd
FSW_strkit FSW_malloc_free FSW_caw_defs FSH_Fn_checks FSW_caw_back.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the symbolic state at 0x819a8 / 0x819ac: the registers are the machine's (sr_atoms under Ereg regs (cawb_extra regs0)),
   the frame [sp, sp + 48) is one region at atom 2 holding cawb_cs, atom 2 is 16-aligned in [2^46, 2^47], and gc are
   assumed branch conditions (at 0x819a8: a0 = 0, which decides `bnez a0`; the engine's interval facts decide no
   equality, YP0e.decide_cond2) *)
Definition cawe_ss (pc : Z) (gc : list acond) : sstate :=
  mkSS pc sr_atoms [fstk_ret 48 cawb_cs] None (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] gc []).
(* what the run leaves in the callee-saved registers: sp back up by 48, s0 .. s4 the reloaded entry values (extra atoms
   36 .. 32), the others their atoms at 0x819a8 (gp, tp, s5 .. s11: the entry's by cawb_mid) *)
Definition cawe_expect (r : bv 5) : sv :=
  let z := bv_unsigned r in
  if z =? 2 then SOff 2 48 else if z =? 8 then SOff 36 0 else if z =? 9 then SOff 35 0 else
  if z =? 18 then SOff 34 0 else if z =? 19 then SOff 33 0 else if z =? 20 then SOff 32 0 else
  SOff (Z.to_nat z) 0.
Definition cawe_cs_ok (rs : list sv) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get rs r) (cawe_expect r)) CALLEE_SAVED.

(* a register the run left as its atom at 0x819a8, whose value there is the entry's *)
Lemma cawe_kept : forall regs regs0 extra (r : bv 5) n, Z.of_nat n = bv_unsigned r -> getr regs r = getr regs0 r ->
  sv_denot (Ereg regs extra) (SOff n 0) = getr regs0 r.
Proof. intros regs regs0 extra r n Hn H. rewrite fsw_SOff0, (ew_Ereg_nat regs extra n r Hn). exact H. Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis RTf : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* the state cawb_mid gives, as the engine's symbolic state cawe_ss (FSW_K.fsw_after_callU's builder, without a call) *)
Lemma cawe_st : forall regs0 ly S U (W : world tfibsegs) regs mem mdc STK ly0 S0 W0 mem0 md0 pc gc,
  @ajournal rc SK tfibsegs B STK (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 [] ly S W (unpoison U mem) mdc 3 ->
  ARU tfibsegs B ly S U W mem mdc ->
  48 <= STK -> spZ regs = spZ regs0 - 48 ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (cawb_extra regs0)) (mrestrict (w_H W) mem) (spZ regs0 - 48)) cawb_cs ->
  conds_ok (Ereg regs (cawb_extra regs0)) gc ->
  st_ok tfibsegs (Ereg regs (cawb_extra regs0)) (cawe_ss pc gc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros regs0 ly S U W regs mem mdc STK ly0 S0 W0 mem0 md0 pc gc HJ HARU HSTK Hsp Hcs Hgc.
pose proof asan_consts as (C1 & _ & C3 & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 48)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
rewrite restrict_mkst_fx. unfold cawe_ss. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor]. unfold region_ok, fstk_ret.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2. split; [lia|]. split; [lia|]. split.
  + intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly S U W mem mdc _ HARU); [lia|]. apply Hpres. lia.
  + exact Hcs.
- cbn. tauto.
- split; [|split; [exact Hgc | exact I]]. cbn [f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E2.
  change (2 ^ 4) with 16. split; [lia|]. split; [|lia].
  rewrite Zminus_mod, Hal16. reflexivity.
Qed.

(* at pc_wrap_free after the run: the registers the symbolic state names, then cawb_tail *)
Lemma cawe_after : forall regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw ly S W regs ss ms md,
  fpreU tfibsegs B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch ->
  fs_heads B ly0 S0 U ->
  fs_glob tfibsegs W0 mem0 live peak cnt fail ->
  st_nev S0 + EV_check_as_written <= EV_MAX ->
  @ajournal rc SK tfibsegs B STK_check_as_written (spZ regs0) [] ly0 S0 W0 (unpoison U mem0) md0 []
    ly S W (unpoison U (ms_mem ms)) md 3 ->
  ARU tfibsegs B ly S U W (ms_mem ms) md ->
  Permutation (ablocks B ly S) ((want, nw) :: ablocks B ly0 S0) ->
  (forall m, ~ In (want, m) (ablocks B ly0 S0)) ->
  getr regs 18 = w64 want -> spZ regs = spZ regs0 - 48 ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  (forall r : bv 5, 21 <= bv_unsigned r <= 27 -> getr regs r = getr regs0 r) ->
  st_ok tfibsegs (Ereg regs (cawb_extra regs0)) ss (restrict (w_H W) ms) ->
  ss_pc ss = PC_free -> ss_resv ss = None -> cawe_cs_ok (ss_regs ss) = true ->
  sr_get (ss_regs ss) 1%bv = SOff 37 0 -> sr_get (ss_regs ss) 10%bv = SOff 18 0 ->
  SRr tfibsegs W (mkCfg ms md) (cawb_post B regs0 ly0 S0 U W0 mem0 md0 live peak cnt fail).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw ly S W regs ss ms md
  HPRE HH HG Hev HJ HARU HPerm Hfresh Hs2 Hsp Hgp Htp Hs5 HS Hpc Hrv Hcs Hra Ha0.
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 48)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ ss ms HS Hrv), Hpc.
rewrite <- (proj1 RTf).
apply (@cawb_tail fx rc SK B IMG FS_ENV ML RTf regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail (ms_regs ms)
  (ms_mem ms) md ly S W want nw HPRE HH HG Hev HJ HARU HPerm Hfresh).
- apply (fsw_preserved (w_H W) _ ss ms regs0 cawe_expect HS Hcs).
  intros r Hr; cbv [CALLEE_SAVED In] in Hr; repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (cawe_expect ?q) = _ =>
    let e := eval vm_compute in (cawe_expect q) in change (cawe_expect q) with e end;
  first
  [ apply fsw_sp_back; exact E2
  | rewrite fsw_SOff0; reflexivity
  | apply cawe_kept;
    [ vm_compute; reflexivity
    | first
      [ exact Hgp
      | exact Htp
      | apply Hs5; lazymatch goal with |- context [bv_unsigned ?q] =>
          let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia ] ] ].
- exact (fsw_reg_extra (w_H W) regs (cawb_extra regs0) ss ms 1%bv 5 HS Hra).
- exact (eq_trans (fsw_reg_atom (w_H W) regs (cawb_extra regs0) ss ms 10%bv 18%bv 18 HS Ha0 eq_refl) Hs2).
Qed.

(* the run's write window: the frame region [sp, sp + 48) at atom 2 = entry sp - 48 *)
Ltac cawe_awr E2 :=
  cbn [cawe_ss ss_mem];
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -48);
  [ reflexivity | rewrite E2; lia | cbn [fstk_ret YP09.r_wlo]; lia | cbn [fstk_ret YP09.r_whi]; lia | apply awr_ok_nil ].

(* the epilogue: cawb_mid at 0x819a8 or 0x819ac to cawb_post. cawb_mid and cawb_post are FSW_caw_back.v's Section W
   definitions, closed over B there, so they take this Section's B explicitly here *)
Lemma cawb_epi : forall regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw pc W c,
  fpreU tfibsegs B STK_check_as_written ly0 S0 U W0 regs0 mem0 md0 ch ->
  fs_heads B ly0 S0 U ->
  fs_glob tfibsegs W0 mem0 live peak cnt fail ->
  st_nev S0 + EV_check_as_written <= EV_MAX ->
  (pc = 0x819a8 \/ pc = 0x819ac) ->
  cawb_mid B pc regs0 ly0 S0 U W0 mem0 md0 want nw W c ->
  SRr tfibsegs W c (cawb_post B regs0 ly0 S0 U W0 mem0 md0 live peak cnt fail).
Proof.
intros regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw pc W c HPRE HH HG Hev Hpc HMID.
destruct HMID as (ly & S & regs & mem & mdc & -> & Ha0 & HJ & HARU & HPerm & Hfresh & Hs2 & Hsp & Hgp & Htp & Hs5 & Hcs).
assert (FS : STK_check_as_written = ltac:(let v := eval vm_compute in STK_check_as_written in exact v)) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs (cawb_extra regs0)) 2) = spZ regs0 - 48)
  by (rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact Hsp).
destruct Hpc as [-> | ->].
- (* 0x819a8: bcmp's answer a0 = 0 *)
  assert (E10 : ew (Ereg regs (cawb_extra regs0)) 10 = w64 0)
    by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact (Ha0 eq_refl)).
  pose proof (cawe_st regs0 ly S U W regs mem mdc STK_check_as_written ly0 S0 W0 mem0 md0 0x819a8
    [mkAC BC_EQ (SOff 10 0) (SLit 0)] HJ HARU ltac:(lia) Hsp Hcs
    ltac:(split; [|exact I]; unfold acond_ok; cbn [ac_c ac_a ac_b]; rewrite fsw_SOff0, E10; reflexivity)) as HS.
  clear Ha0 E10.
  fsw_aj_runU caw_tbl_ok HS HJ HARU.
  + cawe_awr E2.
  + eapply (cawe_after regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw ly S W regs);
      [ exact HPRE | exact HH | exact HG | exact Hev | exact HJ | exact HARU | exact HPerm
      | exact Hfresh | exact Hs2 | exact Hsp | exact Hgp | exact Htp | exact Hs5 | exact HS
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity ].
- (* 0x819ac: the join *)
  pose proof (cawe_st regs0 ly S U W regs mem mdc STK_check_as_written ly0 S0 W0 mem0 md0 0x819ac
    [] HJ HARU ltac:(lia) Hsp Hcs I) as HS.
  clear Ha0.
  fsw_aj_runU caw_tbl_ok HS HJ HARU.
  + cawe_awr E2.
  + eapply (cawe_after regs0 ly0 S0 U W0 mem0 md0 ch live peak cnt fail want nw ly S W regs);
      [ exact HPRE | exact HH | exact HG | exact Hev | exact HJ | exact HARU | exact HPerm
      | exact Hfresh | exact Hs2 | exact Hsp | exact Hgp | exact Htp | exact Hs5 | exact HS
      | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity ].
Qed.

End W.
