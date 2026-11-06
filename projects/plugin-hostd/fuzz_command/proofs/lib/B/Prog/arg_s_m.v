(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: arg_s's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   entry 0x8a820) from B0 (+0x70, both arms of `bnez s3` meet) to the return, after
   lib/A/Prog/sup_pin_accept_s2.v (a working branch 3cc8391594b: the inlined xstrdup's call and the two
   checks and stores on the slot) and lib/B/Prog/socket_send.v (a working branch fb79536f218: xmalloc
   through cl_callS, __asan_memcpy through aj_intrin_atS, the return through paj_ret_at), at B's addresses.

   The segment (lib/B/Prog/arg_s_aux.v lists the code):
     +0x70 .. +0x74  a0 := s3 (the string q), the call of the strlen wrapper (aj_art_at with RtString's
                     astrlen_realizes)
     +0x78 .. +0x80  s4 := |y| + 1, a0 := s4, the call of xmalloc (cl_callS with xmalloc_c's contract; s0 = c + 4 is
                     an image address, so the frame chain is achain_low's empty one)
     +0x84 .. +0x90  s2 := the block p, a1 := q, a2 := |y| + 1, the call of __asan_memcpy (aj_intrin_atS)
     +0x94 .. +0x110 the tail, for each m = 0 .. 5: the load4 check of c->nargs, the UBSan check of c->nargs + 1
                     (`blt a2,a1`, trap site 0x8a8c4), the store4 check, nargs := m + 1, the two UBSan checks of
                     c->args + m (`beqz a0`, 0x8a8e0; `beqz a1`, 0x8a8f4), the store8 check, args[m] := p, the frame
                     back, ret.
   Report and trap edges of the tail, each refuted at its branch by the symbolic executor's step there (PaShadow.v
   sym_step_pi_tok, from the state as_tail_run builds):
     0x8a8b8 `bnez a0` (load4 check, report 0x8a95c) and 0x8a8cc `bnez a0` (store4 check, report 0x8a970): tok_branch_pi's
       shadow token of c + 4, whose shadow byte the slot's shadow entry (as_shok, the record's zero shadow of g_rec /
       record.spill) makes 0 (with the slow path's `andi; addi; blt` back to the fast path, slow_block);
     0x8a904 `bnez a1` (store8 check, report 0x8a974): tok_branch_pi's granule check of c + 8 + 8 m, in the same entry;
     0x8a8c4 `blt a2,a1`: decide_cond2 (YP0e.v) on SLit (m + 1) and SLit m;
     0x8a8e0 `beqz a0` and 0x8a8f4 `beqz a1`: a0 is SOff 33 (8 + 8 m), atom 33 the slot with the fact
       [A_G_REC + 16, A_REC_SPILL] (as_factsB), so decide_cond2 decides a0 <> 0 and a0 >=u c + 8. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
CmdRecBase CmdRecCells CmdRecRo CmdRecRest CmdRecImg RecBLemmas RecBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c arg_s_aux.
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
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's contracts (arg_s_c.v:83-85; VOBJS is the entry segment's, lib/B/Prog/arg_s.v) *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
(* the walk's: the per-binary allocator record, the call target of xmalloc (CmdObj.v cmd_sig_prog, under a Theorem Labs lane's
   lemma name), the per-binary image facts (a Theorem Labs lane's CmdRecImg.v cmd_img_facts_tfib, at this walk's segments), and the
   program statics' writability (CmdRecCells.v PROG_WRITABLE's premise, under the name PRW) *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let ENV : api_env SEGS B := cmd_cf_env SEGS B LAWS HB IMG.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RET := paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI).

Lemma as_sig_xmalloc : SIG CS_xmalloc = BASE + AF_xmalloc.
Proof. rewrite (cmd_sig_prog_PB CS_xmalloc ltac:(vm_compute; repeat (first [left; reflexivity | right]))). reflexivity. Qed.

(* the walk from B0 to the return *)
Lemma as_from_B0 : forall ly S W (regs : bvmap 5 word) mem md ch (c fn : Z) (A : list (list byte))
  (v : option (list byte)) (R : rstate) (O : list (Z * Z)) q (regs1 : bvmap 5 word) mem1 md1,
afn_pre SEGS B ARG_S_STK ly S W regs mem md ch ->
arodata_okP SEGS RLO RHI B (rdW W mem) ->
c = rec_slot R ->
rec_repA B ly S (rdW W mem) (rec_record R fn A) O ->
(length A < 6)%nat ->
as_str_ok B ly S W mem q (sarg v) ->
st_nev S + EV_ARG_S <= EV_MAX -> blocks_bytes S + LIVE_ARG_S v <= LIVE_MAX ->
mo_ok MT S (XM_ARG_S MT v) ->
ajournal SEGS B ARG_S_STK (spZ regs) (as_FP c (Z.of_nat (length A))) ly S W mem md [] ly S W mem1 md1 0 ->
aval_mem (rdW W mem1) (c + CALL_OFF_NARGS) 4 (Z.of_nat (length A)) ->
spZ regs1 = spZ regs - AS_FRAME ->
getr regs1 8 = w64 (c + CALL_OFF_NARGS) -> getr regs1 9 = w64 c -> getr regs1 19 = w64 q ->
getr regs1 21 = w64 SB -> getr regs1 22 = w64 (SB + (c + CALL_OFF_NARGS) / 8) ->
getr regs1 3 = getr regs 3 -> getr regs1 4 = getr regs 4 ->
(forall r, 23 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error as_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) mem1) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
SRr SEGS W (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + AS_B0)) mem1 (seg_rom SEGS)) md1)
(apost_base SEGS B ARG_S_STK (as_FP c (Z.of_nat (length A))) regs ly S W mem md EV_ARG_S
(fun ly' S' W' regs' mem' md' =>
 blocks_bytes S' <= blocks_bytes S + LIVE_ARG_S v /\
 mo_le MT S S' (XM_ARG_S MT v) /\
 ((Z.of_nat (length A) = REC_ARGS_MAX /\ Permutation (ablocks B ly' S') (ablocks B ly S) /\
   rec_repA B ly' S' (rdW W' mem') (rec_record R fn A) O) \/
  (Z.of_nat (length A) < REC_ARGS_MAX /\ exists p,
    let n := Z.of_nat (length (sarg v)) + 1 in
    4096 <= p < 2 ^ 64 /\
    Permutation (ablocks B ly' S') ((p, n) :: ablocks B ly S) /\
    Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B ly S) /\
    rec_repA B ly' S' (rdW W' mem') (rec_record R fn (A ++ [sarg v])) ((p, n) :: O))))).
Proof.
intros ly S W regs mem md ch c fn A v R O q regs1 mem1 md1 HPRE HROD Hc HREP Hm6 HSTR Hev Hlive HMOK HJ HNA1
  Rsp R8 R9 R19 R21 R22 R3 R4 Rhi HFR.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof alloc_ceiling_value as [_ HAC].
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
assert (XS : XMALLOC_STK = 16400) by (vm_compute; reflexivity).
destruct (rec_bridge_slot B ly S (rdW W mem) R fn A O HREP) as (Hslot & _ & _ & _).
assert (Hc' : as_slot_ok c) by (rewrite Hc; exact Hslot).
destruct (as_slot_bounds c Hc') as (Hcb & Hc8 & _). pose proof (as_slot_range c Hc') as Hcr.
set (sp0 := spZ regs) in *.
set (m := Z.of_nat (length A)) in *.
assert (Hm : 0 <= m <= 5) by (subst m; lia).
set (y := sarg v) in *.
set (n := Z.of_nat (length y) + 1) in *.
pose proof (as_str_bounds B HB IMG ly S W mem md q y HAR0 HSTR) as [Hq1 Hq2].
assert (Hn : 1 <= n <= LMAX + 1) by (destruct HSTR as (_ & _ & Hn & _); subst n; lia).
assert (Esp0 : sp0 = spZ regs) by reflexivity.
assert (Em : m = Z.of_nat (length A)) by reflexivity.
assert (En : n = Z.of_nat (length y) + 1) by reflexivity.
assert (Hsp64 : 2 ^ 46 <= sp0 - AS_FRAME) by (unfold AS_FRAME; rewrite WS in Hslo; lia).
(* ---- the state at B0 ---- *)
pose proof (as_seed_B0 W mem1 regs regs1 c sp0 Hsp64 ltac:(lia) Hal16 Hc' Rsp R8 R9 R21 R22 HFR) as HS.
set (E := as_EB regs1 regs c) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs1 r).
{ intros nn r Hnn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold as_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hnn. }
assert (EX : forall j, (j < 10)%nat -> ew E (32 + j) = nth j (as_extraB regs c) (Z_to_bv 64 0)).
{ intros j Hj. subst E. unfold as_EB. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (ESB : ew E 32 = Z_to_bv 64 SB) by (exact (EX 0%nat ltac:(lia))).
assert (EC : ew E 33 = Z_to_bv 64 c) by (exact (EX 1%nat ltac:(lia))).
assert (Usp : bv_unsigned (ew E 2) = sp0 - AS_FRAME) by (rewrite (EE 2%nat 2%bv eq_refl); exact Rsp).
assert (SHOK : sh_ok SEGS as_BxB [] E (mrestrict (w_H W) mem1)) by (unfold sh_ok; apply Forall_nil).
(* B0 .. +0x74: a0 := q, the call of the strlen wrapper *)
paj_run_tok RUN HS HJ SHOK as_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
clear HF HG. rename HFr into HFr0. rename ms into ms0.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 19%nat 19%bv eq_refl) in P10.
assert (Hsp0 : spZ (ms_regs ms0) = sp0 + -64) by (unfold spZ at 1; rewrite P2; fold (spZ regs1); rewrite Rsp; unfold AS_FRAME; lia).
assert (HraT0 : YK0s.ret_ok (getr (ms_regs ms0) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the run writes no memory *)
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms0) a = rdW W mem1 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr0);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
pose proof (proj1 HJ) as HAR1.
assert (HSTR1 : as_str_ok B ly S W (ms_mem ms0) q y)
  by exact (as_str_journal B HB IMG ARG_S_STK sp0 c m ly S W mem md [] ly S W (ms_mem ms0) mdv 0 q y HAR0 Hc' Hm HJ HSTR).
assert (HROD1 : arodata_okP SEGS RLO RHI B (rdW W (ms_mem ms0))).
{ apply (cmd_rodata_kept SEGS B LAWS HB IMG ly S W mem md ly S W (ms_mem ms0) mdv ARG_S_STK sp0 (as_FP c m) [] 0 HAR0 HJ);
    [|exact HROD].
  intros a Hf. left. exact (as_slot_static c a Hc' (as_FP_slot c m a Hm Hf)). }
(* the call of the strlen wrapper on q *)
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low ENV ESTACK (fun _ => False) (SIG CS___interceptor_trampoline_strlen)
    W (ms_regs ms0) (ms_mem ms0) ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly S mdv 0 (-64) (getr (ms_regs ms0) 1) _
    HJ Hsp0 eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite WS; unfold ESTACK; lia) eq_refl (fun a (H : False) => False_ind _ H)).
  apply (ASTRLEN fx ly S W (ms_regs ms0) (ms_mem ms0) mdv q y).
  - apply (ecall_pre_stk_at SEGS B ESTACK ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly S W (ms_mem ms0) mdv 0
      (ms_regs ms0) (-64) HJ Hsp0 eq_refl ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite WS; unfold ESTACK; lia) HraT0);
      [rewrite P3, R3; exact Hgp | rewrite P4, R4; exact Htp].
  - rewrite P10, R19. reflexivity.
  - lia.
  - apply (astr_atR_view SEGS). exact (proj1 (proj2 HSTR1)).
  - apply (as_str_read B HB IMG ESTACK ly S W (ms_regs ms0) (ms_mem ms0) mdv q y HAR1 HSTR1).
    rewrite Hsp0. rewrite WS in Hslo. unfold ESTACK. lia.
  - unfold astr_len. exact (proj1 (proj2 (proj2 (proj2 HSTR1)))).
  - exact (cmd_rom_view_on SEGS B LAWS HB IMG RLO RHI W (ms_mem ms0) HROD1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
rewrite P1.
jafter_call_keep_pi HS 42%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  + apply (mbyte_of_aview SEGS). apply HK2; [unfold AS_FRAME in *; lia | unfold ESTACK, AS_FRAME in *; lia | intros []].
  + unfold AS_FRAME in *. lia. }
rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS.
remember (havoc E 42 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD2 : forall nn, (nn < 42)%nat -> ew E2 nn = ew E nn) by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E46 : ew E2 46 = getr regs2 10) by (rewrite HE2; reflexivity).
clear HE2.
assert (SHOK2 : sh_ok SEGS as_BxB [] E2 (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
(* +0x78 .. +0x80: s4 := |y| + 1, a0 := s4, the call of xmalloc *)
paj_run_tok RUN HS HJ2 SHOK2 as_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
clear HF HG. rename HFr into HFr1. rename ms into ms1.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
assert (Hsp1 : spZ (ms_regs ms1) = sp0 + -64)
  by (unfold spZ at 1; rewrite Q2, (OLD2 2%nat) by lia; rewrite Usp; unfold AS_FRAME; lia).
assert (Q3' : getr (ms_regs ms1) 3 = w64 (as_gp B)) by (rewrite Q3, (OLD2 3%nat), (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp).
assert (Q4' : getr (ms_regs ms1) 4 = w64 (as_tp B)) by (rewrite Q4, (OLD2 4%nat), (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp).
assert (Q8' : s0Z (ms_regs ms1) = c + CALL_OFF_NARGS).
{ unfold s0Z. rewrite Q8, (OLD2 33%nat), EC by lia. rewrite (unsigned_lit_small c) by lia. unfold CALL_OFF_NARGS.
  apply unsigned_lit_small. lia. }
assert (Q10' : getr (ms_regs ms1) 10 = w64 n).
{ rewrite Q10, E46, HQ2. unfold w64, astr_len. rewrite unsigned_lit_small by (unfold LMAX in Hn; lia). reflexivity. }
(* the call of xmalloc(|y| + 1) through its contract (xmalloc_c.v txmalloc_spec, at this FP state) *)
rewrite as_sig_xmalloc.
eapply SRr_bind.
{ eapply (cl_callS B LAWS W (ms_regs ms1) (ms_mem ms1) _ ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly S mdv2 0
    XMALLOC_STK [] EV_XMALLOC (-64) (getr (ms_regs ms1) 1) []
    (fun ly' S' W' regs' mem' md' => exists p : Z,
       getr regs' 10 = w64 p /\ 4096 <= p < 2 ^ 64 /\
       Permutation (ablocks B ly' S') ((p, LIVE_XMALLOC n) :: ablocks B ly S) /\
       Forall (fun qk => iv_apart p (LIVE_XMALLOC n) (fst qk) (snd qk)) (ablocks B ly S) /\
       in_blockA (ablocks B ly' S') p (LIVE_XMALLOC n) /\
       blocks_bytes S' <= blocks_bytes S + LIVE_XMALLOC n /\
       mo_le MT S S' (XM_XMALLOC MT n)) HJ2 Hsp1).
  - reflexivity.
  - lia.
  - unfold XMALLOC_STK, ASTACK. lia.
  - rewrite WS, XS. lia.
  - exact Q3'.
  - exact Q4'.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite Q1, unsigned_lit_small by lia. lia.
  - apply achain_low. rewrite Q8'. unfold CALL_OFF_NARGS. lia.
  - intros HPX. exact (TXMALLOC fx ly S W (ms_regs ms1) (ms_mem ms1) mdv2 [] n HPX Q10'
      ltac:(unfold MALLOC_MAX, LMAX in *; lia) Hev Hlive HMOK).
  - intros a (r & Hr & _). destruct Hr. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJi & HP4 &
  (p & Hp10 & Hp4096 & Hperm4 & Hap4 & Hblk4 & Hbb4 & MLE4)).
assert (LXn : LIVE_XMALLOC n = n) by (unfold LIVE_XMALLOC; lia).
rewrite LXn in Hperm4, Hap4, Hblk4, Hbb4.
pose proof (proj1 HJ4) as HAR4.
assert (Hpin : In (p, n) (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym Hperm4)); left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR4 Hpin) as (_ & _ & Hpc & _ & Hppres & _ & _).
pose proof (crf_req_size_ge n) as Hrqn.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & FI1 & FI2 & FI3 & FI4 & _).
rewrite Q1.
jafter_call_keep_pi HS 58%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0]%nat HS4.
match type of HS4 with ?t -> _ => assert (HRK : t); [|specialize (HS4 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite (OLD2 2%nat), Usp by lia;
    intros a Ha.
  + apply (mbyte_of_aview SEGS). apply FI1;
      [unfold AS_FRAME in *; lia | rewrite XS; unfold AS_FRAME in *; lia | intros (r & Hr & _); destruct Hr].
  + unfold AS_FRAME in *. lia. }
rewrite <- restrict_mkst_fx in HS4. clear HS. rename HS4 into HS.
remember (havoc E2 58 (map (getr regs4) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env VAL A_LIM E4) by (rewrite HE4; apply img_env_havoc; [exact HEI2 | cbv; lia]).
assert (OLD4 : forall nn, (nn < 58)%nat -> ew E4 nn = ew E2 nn) by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
assert (E62 : ew E4 62 = getr regs4 10) by (rewrite HE4; reflexivity).
clear HE4.
assert (SHOK4 : sh_ok SEGS as_BxB [] E4 (mrestrict (w_H W4) mem4)) by (unfold sh_ok; apply Forall_nil).
(* +0x84 .. +0x90: s2 := p, a1 := q, a2 := |y| + 1, the call of __asan_memcpy *)
paj_run_tok RUN HS HJ4 SHOK4 as_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv3 := mdx) in *; clearbody mdv3 end.
clear HF HG. rename HFr into HFr2. rename ms into ms2.
pmkst HS.
prreg HS (1%bv : bv 5) T1. prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4.
prreg HS (10%bv : bv 5) T10. prreg HS (11%bv : bv 5) T11. prreg HS (12%bv : bv 5) T12.
(* the two runs since strlen write no memory *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms1) a = rdW W mem2 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr1);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW W4 (ms_mem ms2) a = rdW W4 mem4 a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr2);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
assert (Hsp2 : spZ (ms_regs ms2) = sp0 + -64)
  by (unfold spZ at 1; rewrite T2, (OLD4 2%nat), (OLD2 2%nat) by lia; rewrite Usp; unfold AS_FRAME; lia).
assert (T3' : getr (ms_regs ms2) 3 = w64 (as_gp B))
  by (rewrite T3, (OLD4 3%nat), (OLD2 3%nat), (EE 3%nat 3%bv eq_refl), R3 by lia; exact Hgp).
assert (T4' : getr (ms_regs ms2) 4 = w64 (as_tp B))
  by (rewrite T4, (OLD4 4%nat), (OLD2 4%nat), (EE 4%nat 4%bv eq_refl), R4 by lia; exact Htp).
assert (T10' : getr (ms_regs ms2) 10 = w64 p) by (rewrite T10, E62; exact Hp10).
assert (T11' : getr (ms_regs ms2) 11 = w64 q)
  by (rewrite T11, (OLD4 19%nat), (OLD2 19%nat), (EE 19%nat 19%bv eq_refl) by lia; exact R19).
assert (T12' : getr (ms_regs ms2) 12 = w64 n).
{ rewrite T12, (OLD4 46%nat), E46, HQ2 by lia. unfold w64, astr_len.
  rewrite unsigned_lit_small by (unfold LMAX in Hn; lia). reflexivity. }
assert (HraT2 : YK0s.ret_ok (getr (ms_regs ms2) 1)) by (rewrite T1; apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (proj1 HJ4) as HAR4'.
assert (HSTR2 : as_str_ok B ly4 S4 W4 (ms_mem ms2) q y)
  by exact (as_str_journal B HB IMG ARG_S_STK sp0 c m ly S W mem md [] ly4 S4 W4 (ms_mem ms2) mdv3 (0 + EV_XMALLOC) q y
    HAR0 Hc' Hm HJ4 HSTR).
pose proof (as_str_read B HB IMG ESTACK ly4 S4 W4 (ms_regs ms2) (ms_mem ms2) mdv3 q y HAR4' HSTR2
  ltac:(rewrite Hsp2; rewrite WS in Hslo; unfold ESTACK; lia)) as (R1q & R2q & R3q & R4q & R5q & R6q & R7q).
pose proof (as_str_apart B HB IMG ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly4 S4 W4 (ms_mem ms2) mdv3 _ q y p n
  HAR0 HJ4 Hperm4 HSTR) as Hpq.
(* the call of __asan_memcpy(p, q, |y| + 1) *)
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIG CS___asan_memcpy) (AMEMCPY fx) W4 (ms_regs ms2) (ms_mem ms2)
    ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly4 S4 mdv3 (0 + EV_XMALLOC) p q n (-64) (getr (ms_regs ms2) 1) HJ4
    T10' T11' T12' ltac:(unfold LMAX in Hn; lia) ltac:(lia) ltac:(lia) Hsp2 eq_refl ltac:(lia)
    ltac:(rewrite WS; unfold ESTACK; lia) T3' T4' eq_refl HraT2).
  - intros a Ha. split.
    + replace a with (p + (a - p)) by lia.
      exact (recb_awr_new_block_perm_m B ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly S W (ms_mem ms1) mdv2 0 ly4 S4 W4 mem4 md4
        p n (ablocks B ly4 S4) (a - p) ly4 HJ2 HAR4 Hperm4 Hpin ltac:(lia)).
    + rewrite WS in Hslo. unfold ESTACK. lia.
  - intros a Ha Hf _. exfalso.
    apply (blk_img SEGS B LAWS ly4 S4 W4 mem4 md4 p n a HAR4 Hpin ltac:(lia)).
    exact (cif_prog_img _ _ IMG a (as_slot_PG c a Hc' (as_FP_slot c m a Hm Hf))).
  - exact (amem_range_of_block SEGS B LAWS ly4 S4 W4 (ms_mem ms2) mdv3 p n p n HAR4' Hpin ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly4 S4 W4 (ms_mem ms2) mdv3 p n p n HAR4' Hpin ltac:(lia) ltac:(lia)).
  - intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly4 S4 W4 (ms_mem ms2) mdv3 p n p n HAR4' Hpin
      ltac:(lia) ltac:(lia) Hn0).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. destruct (R4q a Ha) as [H1 H2]. unfold ascratch_stk in H2. split; [exact H1 | exact H2]. }
    split; [lia|]. split; [exact R5q|]. split; [exact R6q | exact R7q]. }
cbv beta. intros W5 c5 Hwle5 (-> & regs5 & mem5 & md5 & -> & HJ5 & HP5 & Ha05 & Heff5 & Hfr5 & Hpres5 & Hsame5).
rewrite T1.
jafter_call_keep_pi HS 74%nat regs5 (mrestrict (w_H W4) mem5) HP5 [0]%nat HS5.
match type of HS5 with ?t -> _ => assert (HRK : t); [|specialize (HS5 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite (OLD4 2%nat), (OLD2 2%nat), Usp by lia; intros a Ha.
  + apply (mbyte_of_aview SEGS). apply Hfr5; unfold ESTACK, AS_FRAME in *; rewrite WS in Hslo; lia.
  + unfold AS_FRAME in *. lia. }
rewrite <- restrict_mkst_fx in HS5. clear HS. rename HS5 into HS.
remember (havoc E4 74 (map (getr regs5) CLOB)) as E5 eqn:HE5 in HS.
assert (HEI5 : img_env VAL A_LIM E5) by (rewrite HE5; apply img_env_havoc; [exact HEI4 | cbv; lia]).
assert (OLD5 : forall nn, (nn < 74)%nat -> ew E5 nn = ew E4 nn) by (intros nn Hnn; rewrite HE5; apply YN3v.ew_havoc_old; exact Hnn).
clear HE5.
assert (OLD : forall nn, (nn < 42)%nat -> ew E5 nn = ew E nn)
  by (intros nn Hnn; rewrite OLD5, OLD4, OLD2 by lia; reflexivity).
pose proof (proj1 HJ5) as HAR5.
assert (EC5 : ew E5 33 = Z_to_bv 64 c) by (rewrite OLD by lia; exact EC).
assert (ESB5 : ew E5 32 = Z_to_bv 64 SB) by (rewrite OLD by lia; exact ESB).
assert (UC5 : bv_unsigned (ew E5 33) = c) by (rewrite EC5; apply unsigned_lit_small; lia).
assert (E62' : ew E5 62 = Z_to_bv 64 p) by (rewrite OLD5 by lia; rewrite E62; exact Hp10).
(* the slot's nargs field still holds m *)
assert (HNA5 : aval_mem (rdW W4 mem5) (c + CALL_OFF_NARGS) 4 m).
{ intros kk Hkk.
  assert (Ha : c <= c + CALL_OFF_NARGS + Z.of_nat kk < c + CALL_SIZE) by (unfold CALL_OFF_NARGS, CALL_SIZE; lia).
  assert (Ha2 : 0 <= c + CALL_OFF_NARGS + Z.of_nat kk < 0x606000) by (unfold CALL_OFF_NARGS; lia).
  destruct (cmd_prog_unowned SEGS B LAWS HB IMG _ (as_slot_PG c _ Hc' Ha)) as (Hi & Ho & He).
  rewrite Hfr5; [| lia | | unfold ESTACK; rewrite WS in Hslo; lia].
  2:{ intros Hp. exact (blk_img SEGS B LAWS ly4 S4 W4 mem4 md4 p n (c + CALL_OFF_NARGS + Z.of_nat kk) HAR4 Hpin ltac:(lia) Hi). }
  rewrite KEEP2 by lia.
  rewrite FI3; [| exact Hi | exact Ho | exact He | exact (fp_spares_closed [] _ sink_closed_nil (inFP_nil _))].
  rewrite KEEP1 by lia.
  rewrite HK2; [| lia | unfold ESTACK; rewrite WS in Hslo; lia | intros []].
  rewrite KEEP0 by lia.
  exact (HNA1 kk Hkk). }
(* ---- the tail (+0x94 .. +0x110), shared facts ---- *)
assert (Usp5 : bv_unsigned (ew E5 2) = sp0 - AS_FRAME) by (rewrite OLD by lia; exact Usp).
assert (HRA34 : ew E5 34 = getr regs 1) by (rewrite OLD by lia; exact (EX 2%nat ltac:(lia))).
assert (EN : forall j, (j < 8)%nat -> ew E5 (34 + j) = getr regs (Z_to_bv 5 (nth j as_saved 0))).
{ intros j Hj. rewrite OLD by lia. replace (34 + j)%nat with (32 + (2 + j))%nat by lia.
  rewrite (EX (2 + j)%nat ltac:(lia)).
  do 8 (destruct j as [|j]; [reflexivity|]). lia. }
assert (ER : forall r, r = 3 \/ r = 4 \/ 23 <= r <= 27 -> ew E5 (Z.to_nat r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite OLD by lia. rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)).
  - destruct Hr as [-> | [-> | Hr]]; [exact R3 | exact R4 | exact (Rhi r Hr)].
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small; lia. }
assert (HDEN : forall r, acallee_saved r -> sv_denot E5 (as_restore r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. unfold acallee_saved in Hr.
  assert (Hc15 : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  repeat (destruct Hc15 as [-> | Hc15];
    [ lazymatch goal with |- sv_denot _ (as_restore ?rr) = _ =>
        let vv := eval vm_compute in (as_restore rr) in change (as_restore rr) with vv end;
      cbn [sv_denot];
      first
      [ rewrite Usp5; unfold AS_FRAME; replace (sp0 - 64 + 64) with (spZ regs) by lia; unfold spZ;
        apply Z_to_bv_bv_unsigned
      | rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        first [ exact (EN 1%nat ltac:(lia)) | exact (EN 2%nat ltac:(lia)) | exact (EN 3%nat ltac:(lia))
              | exact (EN 4%nat ltac:(lia)) | exact (EN 5%nat ltac:(lia)) | exact (EN 6%nat ltac:(lia))
              | exact (EN 7%nat ltac:(lia))
              | exact (ER 3 ltac:(lia)) | exact (ER 4 ltac:(lia)) | exact (ER 23 ltac:(lia))
              | exact (ER 24 ltac:(lia)) | exact (ER 25 ltac:(lia)) | exact (ER 26 ltac:(lia))
              | exact (ER 27 ltac:(lia)) ] ]
    | ]).
  subst r.
  lazymatch goal with |- sv_denot _ (as_restore ?rr) = _ =>
    let vv := eval vm_compute in (as_restore rr) in change (as_restore rr) with vv end.
  cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (ER 27 ltac:(lia)). }
(* the slot's two fields are the footprint's bytes *)
assert (HINA : forall a, c + CALL_OFF_NARGS <= a < c + CALL_OFF_NARGS + 4 -> inFP (as_FP c m) a).
{ intros a Ha. exists (c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4). split; [left; reflexivity | exact Ha]. }
assert (HINB : forall a, c + CALL_OFF_ARGS + 8 * m <= a < c + CALL_OFF_ARGS + 8 * m + 8 -> inFP (as_FP c m) a).
{ intros a Ha. exists (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8).
  split; [right; left; reflexivity | exact Ha]. }
assert (HAWR : forall a, inFP (as_FP c m) a ->
  awr_byte SEGS B ARG_S_STK sp0 (as_FP c m) (ablocks B ly S) (ablocks B ly4 S4) (frames S) ly4 [] a).
{ intros a Hf. exact (as_awr_slot B HB IMG c a ARG_S_STK sp0 (as_FP c m) _ _ _ ly4 [] Hc' (as_FP_slot c m a Hm Hf) Hf). }
assert (HROA : region_ok SEGS E5 (mrestrict (w_H W4) mem5) (as_slotA m)).
{ unfold YP09.region_ok, as_slotA, AB_C.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UC5.
  split; [unfold CALL_OFF_NARGS; lia|]. split; [unfold CALL_OFF_NARGS; lia|].
  split; [intros o Ho; apply (as_slot_writable B HB PRW _ c (c + o) Hc'); unfold CALL_OFF_NARGS, CALL_SIZE in *; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E5 _ c CALL_OFF_NARGS 4 (SLit m) m); [reflexivity | cbn; lia | cbn; lia |].
  exact (val_mem_of_aval SEGS (w_H W4) mem5 (c + CALL_OFF_NARGS) 4%nat m HNA5). }
assert (HROB : region_ok SEGS E5 (mrestrict (w_H W4) mem5) (as_slotB m)).
{ unfold YP09.region_ok, as_slotB, AB_C.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UC5.
  split; [unfold CALL_OFF_ARGS; lia|]. split; [unfold CALL_OFF_ARGS; lia|].
  split; [intros o Ho; apply (as_slot_writable B HB PRW _ c (c + o) Hc'); unfold CALL_OFF_ARGS, CALL_SIZE in *; lia|].
  apply Forall_nil. }
assert (SHOK3 : sh_ok SEGS as_BxB as_SHB E5 (mrestrict (w_H W4) mem5))
  by exact (as_shok B HB ly4 S4 W4 mem5 md5 E5 AB_C AB_SB c HAR5 Hc' EC5 ESB5).
(* the post from the facts the tail leaves, for every m *)
lazymatch goal with |- SRr _ _ _ ?Q => set (POSTQ := Q) end.
assert (TAILK : forall (msF : machine_state) mdF,
  ajournal SEGS B ARG_S_STK sp0 (as_FP c m) ly S W mem md [] ly4 S4 W4 (ms_mem msF) mdF (0 + EV_XMALLOC) ->
  aregs_preserved regs (ms_regs msF) -> getr (ms_regs msF) 1 = getr regs 1 ->
  aval_mem (rdW W4 (ms_mem msF)) (c + CALL_OFF_NARGS) 4 (m + 1) ->
  aval_mem (rdW W4 (ms_mem msF)) (c + CALL_OFF_ARGS + 8 * m) 8 p ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ inFP (as_FP c m) a -> rdW W4 (ms_mem msF) a = rdW W4 mem5 a) ->
  forall mat', POSTQ W4 (mkCfg (mkst (ms_regs msF) (v_jalr (getr (ms_regs msF) 1) 0) (ms_mem msF) (seg_rom SEGS))
    (with_vm_backing (m_vm_lazy mdF) mat' mdF))).
{ intros msF mdF HJF HPF HraF HNAF HARGF HKF mat'. subst POSTQ. unfold apost_base.
  pose proof (proj1 HJF) as HARF.
  pose proof HJF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FF2 & FF3 & _).
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  exists ly4, S4, (ms_regs msF), (ms_mem msF), (with_vm_backing (m_vm_lazy mdF) mat' mdF).
  split; [rewrite HraF, Hra'; reflexivity|].
  split; [apply (ajournal_mono_k SEGS B) with (k := 0 + EV_XMALLOC);
    [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJF | unfold EV_ARG_S, EV_XMALLOC; lia]|].
  split; [exact HPF|].
  assert (HLV : LIVE_ARG_S v = n) by (unfold LIVE_ARG_S; exact LXn).
  split; [rewrite HLV; exact Hbb4|]. split; [exact MLE4|].
  right. split; [unfold REC_ARGS_MAX; lia|].
  exists p. cbv zeta. split; [lia|]. split; [exact Hperm4|]. split; [exact Hap4|].
  apply (rec_bridge_add B ly S ly4 S4 (rdW W mem) (rdW W4 (ms_mem msF)) R fn A O y p n HREP Hm6).
  - intros a Ha Hn1 Hn2. rewrite <- Hc in Hn1, Hn2.
    assert (HPG : inFP cmd_PG a).
    { destruct Ha as [Ha | Ha].
      - exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; lia].
      - exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; lia]. }
    destruct (cmd_prog_unowned SEGS B LAWS HB IMG a HPG) as (Hi & Ho & He).
    apply FF3; [exact Hi | exact Ho | exact He |].
    apply fp_spares_closed.
    + apply sink_closed_pos. unfold as_FP. repeat constructor; cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; lia.
    + intros (r & Hr & Har). unfold as_FP in Hr.
      destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Har; [apply Hn1 | apply Hn2]; rewrite <- ?Em; lia.
  - intros [b k] Hbk. pose proof (as_O_in B ly S (rdW W mem) _ O HREP (b, k) Hbk) as Hin0.
    assert (Hin4 : In (b, k) (ablocks B ly4 S4)) by (apply (Permutation_in _ (Permutation_sym Hperm4)); right; exact Hin0).
    split; [exact Hin4|]. intros i Hi. cbn [fst snd] in Hi |- *.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b k HAR0 Hin0) as (_ & _ & _ & _ & _ & _ & Hk). pose proof (crf_req_size_ge k).
    apply (FF2 b k i Hin0 Hin4 ltac:(lia)).
    intros Hf. apply (blk_img SEGS B LAWS ly S W mem md b k (b + i) HAR0 Hin0 ltac:(lia)).
    exact (cif_prog_img _ _ IMG _ (as_slot_PG c _ Hc' (as_FP_slot c m _ Hm Hf))).
  - exact Hpin.
  - intros Hin. apply in_map_iff in Hin as ([b k] & Hb & Hbk). cbn [fst] in Hb. subst b.
    pose proof (as_O_in B ly S (rdW W mem) _ O HREP (p, k) Hbk) as Hin0.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR0 Hin0) as (_ & _ & _ & _ & _ & _ & Hk).
    pose proof (req_size_pos k ltac:(lia)) as [Hrk _]. pose proof (req_size_pos n ltac:(lia)) as [Hrn _].
    pose proof (recb_fresh_disj_perm_m B ly4 S4 W4 mem4 md4 (ablocks B ly S) p n p k HAR4 Hperm4 Hin0) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. destruct D as [D | D]; lia.
  - apply (recb_heap_apart_m B ly4 S4 W4 mem4 md4 p n A_G_REC REC_SIZE HAR4 Hpin ltac:(lia) ltac:(unfold REC_SIZE; lia)).
    intros a Ha. apply (cif_prog_img _ _ IMG). exists (A_G_REC, A_G_REC + REC_SIZE).
    split; [left; reflexivity | cbn [fst snd]; lia].
  - apply (recb_heap_apart_m B ly4 S4 W4 mem4 md4 p n A_REC_SPILL SC_SIZE HAR4 Hpin ltac:(lia) ltac:(unfold SC_SIZE; lia)).
    intros a Ha. apply (cif_prog_img _ _ IMG). exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
    split; [right; left; reflexivity | cbn [fst snd]; lia].
  - lia.
  - unfold LMAX in *. lia.
  - unfold LMAX in *. lia.
  - rewrite <- Hc, <- Em. exact HNAF.
  - rewrite <- Hc, <- Em. exact HARGF.
  - destruct HSTR2 as (_ & [HBy Hno0] & _). split; [|exact Hno0].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    rewrite HKF.
    2:{ lia. }
    2:{ intros Hf. apply (blk_img SEGS B LAWS ly4 S4 W4 mem4 md4 p n (p + Z.of_nat i) HAR4 Hpin ltac:(lia)).
        exact (cif_prog_img _ _ IMG _ (as_slot_PG c _ Hc' (as_FP_slot c m _ Hm Hf))). }
    rewrite (Heff5 (Z.of_nat i) ltac:(lia)).
    exact (HBy i ltac:(rewrite length_app; cbn [length]; lia)). }
clearbody m.
assert (Hm5 : m = 0 \/ m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5) by lia.
destruct Hm5 as [-> | [-> | [-> | [-> | [-> | ->]]]]].
(* the slot's two fields as regions of the state, each with its disjointness from the frame closed on the concrete
   regions (no evar reaches a vm_compute) *)
all: lazymatch type of HROA with region_ok _ _ _ ?rA =>
  pose proof (st_ok_pi_add_region E5 _ _ rA HS) as HSa end;
  specialize (HSa ltac:(vm_compute; reflexivity) HROA).
all: lazymatch type of HSa with all_disjoint ?Ex ?rx ?lx -> _ =>
  assert (HDA : all_disjoint Ex rx lx) end;
  [ apply all_disjoint_of_extents; unfold as_slotA, AB_C;
    cbn [ss_mem map zall_disjoint]; unfold zdisj, extent_of_region;
    cbn [fst snd base_val YP09.r_base YP09.r_lo YP09.r_hi]; rewrite UC5, Usp5; unfold AS_FRAME, CALL_OFF_NARGS;
    repeat split; lia
  | specialize (HSa HDA); clear HDA ].
all: lazymatch type of HROB with region_ok _ _ _ ?rB =>
  pose proof (st_ok_pi_add_region E5 _ _ rB HSa) as HSb end;
  specialize (HSb ltac:(vm_compute; reflexivity) HROB).
all: lazymatch type of HSb with all_disjoint ?Ex ?rx ?lx -> _ =>
  assert (HDB : all_disjoint Ex rx lx) end;
  [ apply all_disjoint_of_extents; unfold as_slotA, as_slotB, AB_C;
    cbn [ss_mem map zall_disjoint]; unfold zdisj, extent_of_region;
    cbn [fst snd base_val YP09.r_base YP09.r_lo YP09.r_hi]; rewrite UC5, Usp5;
    unfold AS_FRAME, CALL_OFF_NARGS, CALL_OFF_ARGS; repeat split; lia
  | specialize (HSb HDB); clear HDB ].
all: clear HS HSa; rename HSb into HS.
all: paj_run_tok RUN HS HJ5 SHOK3 as_Bspan;
  [ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end;
    eapply awr_ok_cons_gen; [reflexivity | exact UC5 | intros a Ha; cbn in Ha; apply HAWR, HINB; unfold CALL_OFF_ARGS; lia |];
    eapply awr_ok_cons_gen; [reflexivity | exact UC5 | intros a Ha; cbn in Ha; apply HAWR, HINA; unfold CALL_OFF_NARGS; lia |];
    apply (awr_ok_cons_ro SEGS B); [cbn; lia|]; apply (awr_ok_nil SEGS B)
  | ].
all: lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdvT := mdx) in *; clearbody mdvT end;
  clear HF HG.
all: eapply (RET W4 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat'.
all: prreg HS (1%bv : bv 5) Rf1.
all: lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (as_slotB 0)) in
    pose proof (st_ok_pi_region_nth E5 ssx (restrict (w_H W4) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRB;
    let r1 := eval vm_compute in (nth 1 (ss_mem ssx) (as_slotA 0)) in
    pose proof (st_ok_pi_region_nth E5 ssx (restrict (w_H W4) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HRAA end.
all: cbn [ms_mem restrict] in HRB, HRAA.
all: apply TAILK;
  [ exact HJ5
  | exact (as_regs_restored (w_H W4) E5 _ _ regs HS ltac:(vm_compute; reflexivity) HDEN)
  | rewrite Rf1; exact HRA34
  | apply (aval_mem_view SEGS); change 4%nat with (N.to_nat 4);
    eapply (field_of_region E5 _ 33 c _ _ _ _ _ 4 4%N _ _ HRAA UC5);
    [ cbn [In]; left; reflexivity | reflexivity | cbn; lia | cbn; lia ]
  | apply (aval_mem_view SEGS); change 8%nat with (N.to_nat 8); rewrite <- Z.add_assoc;
    eapply (field_of_region E5 _ 33 c _ _ _ _ _ _ 8%N (SOff 62 0) p HRB UC5);
    [ cbn [In]; left; reflexivity
    | cbn [sv_denot]; rewrite E62', Z.add_0_r, unsigned_lit_small by lia; reflexivity
    | cbn; lia | cbn; lia ]
  | lazymatch goal with |- forall a, _ -> ~ inFP ?fp a -> _ =>
      intros a Ha Hna; apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => inFP fp a) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?UC5, ?Usp5 in Hrr;
           first [apply HINA; unfold CALL_OFF_NARGS; lia | apply HINB; unfold CALL_OFF_ARGS; lia
                 | unfold AS_FRAME in Hrr; lia] |]); destruct Hin
      | exact Ha | exact Hna ] end ].
Qed.

End e.
End f.
End d.
