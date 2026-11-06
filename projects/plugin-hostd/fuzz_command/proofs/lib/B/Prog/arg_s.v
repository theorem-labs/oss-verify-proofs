(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: arg_s's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan,
   .symtab LOCAL FUNC arg_s at 0x8a820, 344 bytes, 86 instructions; lib/B/Prog/arg_s_aux.v lists the code). It proves
   a Theorem Labs lane's targ_s_spec (lib/B/Prog/arg_s_c.v) unchanged. The A image inlines arg_s at every call site, so this walk
   follows the B code alone, after the A walks' inlined segments (lib/A/Prog/sup_pin_accept_s4.v, a working branch
   3cc8391594b: the entry seed, the branch split, the run to the meet).

   The segments:
   - the entry (+0x00 .. +0x64): the frame, the two UBSan checks of c, the shadow base, the load4 check of c->nargs,
     the branch on c->nargs >= 6 and, when c->nargs <= 5, the branch on s;
   - c->nargs = 6: the frame back and ret (nothing written but the frame);
   - c->nargs <= 5: both arms of `bnez s3` run to B0 (+0x70); lib/B/Prog/arg_s_m.v (as_from_B0) walks on.
   Report and trap edges of the entry, each refuted at its branch by the symbolic executor's step there (PaShadow.v
   sym_step_pi_tok, decide_cond2 of YP0e.v over the entry state's facts, as_factsE of arg_s_aux.v):
     0x8a844 `beqz a0` (UBSan: c = NULL): a0 is atom 10 (c) with the fact [A_G_REC + 16, A_REC_SPILL], from as_slot_ok
       c (rec_bridge_slot, RecBridge.v);
     0x8a850 `bnez a0` after `andi a0,a0,7` (UBSan: c misaligned): atom 10's fact has alignment 2^3 (as_slot_bounds);
     0x8a874 `bnez a0` (load4 check of c + 4, report 0x8a948): tok_branch_pi's shadow token over the slot's shadow
       entry (as_shok: the record's zero shadow of g_rec / record.spill);
     0x8a880 `blt a1,a0` with a1 = 5: decided by atom 33's fact (c->nargs = m, [0, 5] or [6, 6]). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
xmalloc_c record_c arg_s_c arg_s_aux arg_s_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the conjunct of a cmd_ro_in fact the goal names *)
Ltac as_pick H :=
lazymatch type of H with
| ?P /\ ?Q => first [ exact (proj1 H) | let H' := fresh "Hp" in pose proof (proj2 H) as H'; clear H; as_pick H' ]
| _ => exact H
end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the frame's eight words, read off the entry run's stack region (sup_pin_accept_s4.v spa_frame_words, 8 words) *)
Lemma as_frame_words : forall (W : world SEGS) m (regs : bvmap 5 word) E0 sp0 cs,
(forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E0 nn = getr regs r) ->
bv_unsigned (ew E0 2) = sp0 ->
region_ok SEGS E0 (mrestrict (w_H W) m) (YP09.mkRegion (Some 2%nat) (-64) 0 (-64) 0 cs) ->
(forall j r, nth_error as_saved j = Some r ->
   In (YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (Z.to_nat r) 0))) cs) ->
forall j r, nth_error as_saved j = Some r ->
  val_mem SEGS (mrestrict (w_H W) m) (sp0 - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
intros W m regs E0 sp0 cs HEL Hsp HR HIn j r Hj.
assert (Hr : In r as_saved) by (eapply nth_error_In; exact Hj).
assert (Hr32 : 0 <= r < 32) by (cbv [as_saved In] in Hr; lia).
replace (sp0 - 8 - 8 * Z.of_nat j) with (sp0 + (-8 - 8 * Z.of_nat j)) by lia.
change 8%nat with (N.to_nat 8).
apply (field_of_region (segs:=SEGS) E0 _ 2%nat sp0 cs _ _ _ _ (-8 - 8 * Z.of_nat j) 8%N
  (SOff (Z.to_nat r) 0) (bv_unsigned (getr regs (Z_to_bv 5 r))) HR Hsp (HIn j r Hj)).
- cbn [sv_denot]. rewrite (HEL (Z.to_nat r) (Z_to_bv 5 r)).
  + rewrite Z.add_0_r. reflexivity.
  + rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32.
    rewrite Z.mod_small by lia. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HRr. change (bv_modulus 64) with (2 ^ 64) in HRr.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- cbn. lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the statement's Section hypotheses (arg_s_c.v:83-86) *)
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG CS___asan_memcpy).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis VOBJS : cmd_val_objs.
(* the walk's (arg_s_m.v's): the allocator record, the meter's laws, the call target of xmalloc, the per-binary image
   facts, the program statics' writability *)
Hypothesis HB : CmdBSyms B.
Hypothesis MTL : ameter_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> @cmd_img_facts SK SEGS B0.
Hypothesis PRW : prog_rw SEGS B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let IMG : @cmd_img_facts SK SEGS B := cmd_img_facts_tfib B HB.
Let RUN := paj_run (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let RUNTO := paj_run_to (L := cmd_listing) (PL := PL_cmd) (PI := PI) B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).
Let RET := paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI).

(* the default "(null)" (RO_lit_224c0) is a string as_str_ok takes *)
Lemma as_null_ok : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> as_str_ok B ly S W mem 0x224c0 (sarg None).
Proof.
intros ly S W mem md HAR HROD.
assert (HIN : In (0x224c0, RO_lit_224c0) cmd_ro_list) by (unfold cmd_ro_list; repeat (first [left; reflexivity | right])).
pose proof (cmd_ro_obj_bytes SEGS B LAWS HB IMG ly S W mem md _ HAR HROD HIN) as HBY. cbn [fst snd] in HBY.
assert (HEND : In 0x224c6 cmd_ro_ends).
{ assert (H : existsb (Z.eqb 0x224c6) cmd_ro_ends = true) by (vm_compute; reflexivity).
  apply existsb_exists in H as (e & He & Heq). apply Z.eqb_eq in Heq. subst e. exact He. }
assert (HRO7 : forall i, 0 <= i < 7 -> in_roP SEGS RLO RHI (0x224c0 + i)).
{ pose proof (cif_ro_in _ _ IMG) as Hro. unfold cmd_ro_in in Hro. as_pick Hro. }
assert (HUN7 : forall i, 0 <= i < 7 -> ~ Exists (in_zr (0x224c0 + i)) (as_owned_static B) /\
  ~ (as_errno B <= 0x224c0 + i < as_errno B + 4)).
{ pose proof (cif_ro_unowned _ _ IMG) as Hro. unfold cmd_ro_in in Hro. as_pick Hro. }
unfold as_str_ok. split; [lia|]. split.
{ split; [exact HBY | vm_compute; intros H; repeat (destruct H as [H | H]; [discriminate H|]); exact H]. }
split; [change (Z.of_nat (length (sarg None))) with 6; unfold LMAX; lia|]. split.
{ exact (cmd_tail_vis_at SEGS B LAWS HB IMG ly S W mem md 0x224c6 HAR HEND). }
right; left. split; [|split; vm_compute; reflexivity].
intros i Hi. change (Z.of_nat (length (sarg None)) + 1) with 7 in Hi.
destruct (HUN7 i Hi) as [H1 H2]. exact (conj (HRO7 i Hi) (conj H1 H2)).
Qed.

Theorem targ_s_holds : targ_s_spec B MT.
Proof.
unfold targ_s_spec.
intros ly S W regs mem md ch c s fn A v R O HPRE HROD HRO H10 H11 Hc HREP HSTR HTL Hev Hlive HMOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (WS : ARG_S_STK = 16464) by (vm_compute; reflexivity).
destruct (rec_bridge_slot B ly S (rdW W mem) R fn A O HREP) as (Hslot & HNA & Hle6 & _).
rewrite <- Hc in Hslot, HNA.
assert (Hc' : as_slot_ok c) by exact Hslot.
clear Hslot.
destruct (as_slot_bounds c Hc') as (Hcb & Hc8 & _). pose proof (as_slot_range c Hc') as Hcr.
set (m := Z.of_nat (length A)) in *.
assert (Hm6 : 0 <= m <= 6) by (subst m; lia).
(* the entry state, at c->nargs in [mlo, mhi] *)
assert (SEED : forall mlo mhi, 0 <= mlo -> mlo <= m <= mhi -> mhi < 2 ^ 31 ->
  st_ok_pi SEGS VAL (as_EE regs m) (ss_E mlo mhi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_arg_s)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS as_BxE as_SHE (as_EE regs m) (mrestrict (w_H W) mem)).
{ intros mlo mhi H1 H2 H3.
  exact (as_seed_E B VOBJS HB ly S W regs mem md c m mlo mhi ARG_S_STK HAR0 Hstk
    ltac:(rewrite WS; unfold AS_FRAME; lia) Hpres H10 Hc' H1 H2 H3 HNA). }
set (E := as_EE regs m) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs r).
{ intros kk r Hk. subst E. unfold as_EE. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk. }
assert (HAE : env_agree 32 (Ereg regs (as_extraE m)) E)
  by (subst E; unfold as_EE; split; [intros nn Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SB)
  by (subst E; unfold as_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0%nat)).
assert (E33 : ew E 33 = Z_to_bv 64 m)
  by (subst E; unfold as_EE; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1%nat)).
assert (E10 : ew E 10 = Z_to_bv 64 c) by (rewrite (EL 10%nat 10%bv eq_refl); exact H10).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EL 2%nat 2%bv eq_refl); reflexivity).
assert (UC : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
clearbody E.
unfold cfg_at, w64.
destruct (Z.eq_dec m 6) as [Hm | Hm].
- (* ---- c->nargs = 6: the frame back, ret ---- *)
  assert (Hif : (m <? REC_ARGS_MAX) = false) by (apply Z.ltb_ge; unfold REC_ARGS_MAX; lia).
  rewrite Hif.
  destruct (SEED 6 6 ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
  pose proof (ajournal_init SEGS B ARG_S_STK [] ly S W regs mem md ch HPRE) as HJ.
  paj_run_tok RUN HS HJ SHOK as_Bspan.
  { awr_ok_tac; exact Usp. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
  clear HF HG.
  eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)). intros mat'.
  prreg HS (1%bv : bv 5) Rf1.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => spZ regs - 64 <= a < spZ regs) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?Usp in Hrr; lia|]);
        destruct Hin
      | exact Ha | exact H1 ]. }
  pose proof Hra as Hra'. unfold YK0s.ret_ok in Hra'.
  unfold apost_base. exists ly, S, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy mdv) mat' mdv).
  split; [rewrite Rf1, (EL 1%nat 1%bv eq_refl), Hra'; reflexivity|].
  split; [apply (ajournal_mono_k SEGS B) with (k := 0);
    [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ | unfold EV_ARG_S, EV_XMALLOC; lia]|].
  split; [exact (aregs_preserved_of_st_ok SEGS (w_H W) E _ ms regs (as_extraE m) HS HAE ltac:(vm_compute; reflexivity))|].
  split; [unfold LIVE_ARG_S, LIVE_XMALLOC; lia|].
  split.
  { apply (mle_weaken MT S S 0 _ MTL (mle_start MT S MTL)). unfold XM_ARG_S, XM_XMALLOC.
    apply (mo_malloc_nonneg MT MTL). unfold LIVE_XMALLOC. lia. }
  left. split; [unfold REC_ARGS_MAX; exact Hm|]. split; [apply Permutation_refl|].
  apply (as_rep_keep B ly S ly S (rdW W mem) (rdW W (ms_mem ms)) _ O HREP (as_O_in B ly S (rdW W mem) _ O HREP)).
  intros a Ha. rewrite WS in Hslo.
  assert (Hal : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | [Ha | (pn & Hpn & Ha)]]; [unfold A_G_REC, REC_SIZE in *; lia | unfold A_REC_SPILL, SC_SIZE in *; lia|].
    destruct pn as [p k]. pose proof (as_O_in B ly S (rdW W mem) _ O HREP (p, k) Hpn) as Hin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ p k HAR0 Hin) as (_ & H4096 & Hpc & _ & _ & _ & Hk).
    pose proof (crf_req_size_ge k). cbn [fst snd] in Ha. lia. }
  apply KEEP; lia.
- (* ---- c->nargs <= 5 ---- *)
  assert (Hm5 : 0 <= m <= 5) by lia.
  assert (Hm6' : (length A < 6)%nat) by (subst m; lia).
  assert (Hif : (m <? REC_ARGS_MAX) = true) by (apply Z.ltb_lt; unfold REC_ARGS_MAX; lia).
  rewrite Hif. change [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * m, c + CALL_OFF_ARGS + 8 * m + 8)]
    with (as_FP c m).
  (* the caller's string: NULL, or one as_str_ok takes (arg_s_c.v:106-112) *)
  assert (HSTR' : (v = None /\ s = 0) \/ (exists x, v = Some x /\ as_str_ok B ly S W mem s x)).
  { destruct HSTR as [Hargs | (x & -> & Hstr & Hn & Hobj)].
    - destruct v as [x|]; cbn [astr_argA] in Hargs; [right | left; split; [reflexivity | exact Hargs]].
      destruct Hargs as (Hs0 & Hstr & Hn & Hk). exists x. split; [reflexivity|].
      unfold as_str_ok. split; [exact Hs0|]. split; [exact Hstr|]. split; [exact Hn|].
      split; [exact (HTL x eq_refl)|].
      destruct Hk as [(Hblk & _) | (Hro & Ha & Hh & _)];
        [left; exact Hblk | right; left; split; [exact Hro | split; [exact Ha | exact Hh]]].
    - right. exists x. split; [reflexivity|]. unfold as_str_ok.
      split.
      { destruct Hobj as ((cid & pos & Hin & _ & _ & Hf1 & _) & _).
        destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR0 Hin) as (Hb1 & _).
        pose proof alloc_ceiling_value as [_ HAC]. lia. }
      split; [exact Hstr|]. split; [exact Hn|]. split; [exact (HTL x eq_refl)|].
      right; right. exact Hobj. }
  destruct (SEED 0 5 ltac:(lia) ltac:(lia) ltac:(lia)) as [HS SHOK].
  pose proof (ajournal_init SEGS B ARG_S_STK (as_FP c m) ly S W regs mem md ch HPRE) as HJ.
  paj_run_tok RUN HS HJ SHOK as_Bspan.
  { awr_ok_tac; exact Usp. }
  (* 0x8a884: `bnez s3`, the two arms of the NULL test *)
  psrr_branch_tok RUN BR HS SHOK as_Bspan.
  all: paj_run_to_tok RUNTO HS HJ SHOK as_Bspan AS_B0; [awr_ok_tac; exact Usp|].
  all: lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msB end.
  all: repeat rewrite wvb_collapse in HJ.
  (* B0 (+0x70): the registers, the slot's nargs field and the frame's eight words, in both arms *)
  all: pmkst HS.
  all: lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
  all: prreg HS (2%bv : bv 5) P2; prreg HS (3%bv : bv 5) P3; prreg HS (4%bv : bv 5) P4;
    prreg HS (8%bv : bv 5) P8; prreg HS (9%bv : bv 5) P9; prreg HS (19%bv : bv 5) P19;
    prreg HS (21%bv : bv 5) P21.
  all: pose proof (st_ok_pi_restrict_reg (w_H W) E _ _ (22%bv : bv 5) HS) as P22;
    lazymatch type of P22 with _ = sv_denot _ (sr_get ?aa ?rr) =>
      let vv := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with vv in P22 end;
    cbn [ms_regs restrict mkst] in P22.
  all: assert (Rsp1 : spZ (ms_regs msB) = spZ regs - AS_FRAME)
    by (unfold spZ at 1; rewrite P2; cbn [sv_denot]; rewrite Usp;
        pose proof alloc_ceiling_value as [_ HAC]; rewrite WS in Hslo;
        rewrite unsigned_lit_small by lia; unfold AS_FRAME; lia).
  all: assert (R8 : getr (ms_regs msB) 8 = w64 (c + CALL_OFF_NARGS)) by (rewrite P8; cbn [sv_denot]; rewrite UC; reflexivity).
  all: assert (R9 : getr (ms_regs msB) 9 = w64 c) by (rewrite P9; exact E10).
  all: assert (R21 : getr (ms_regs msB) 21 = w64 SB) by (rewrite P21; exact E32).
  all: assert (R22 : getr (ms_regs msB) 22 = w64 (SB + (c + CALL_OFF_NARGS) / 8))
    by (rewrite P22, (denot_shx E 10 32 4 c SB E10 E32) by (unfold SB; lia); unfold CALL_OFF_NARGS; reflexivity).
  all: assert (R3 : getr (ms_regs msB) 3 = getr regs 3) by (rewrite P3; apply EL; reflexivity).
  all: assert (R4 : getr (ms_regs msB) 4 = getr regs 4) by (rewrite P4; apply EL; reflexivity).
  all: assert (Rhi : forall r, 23 <= r <= 27 -> getr (ms_regs msB) (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r));
    [ intros r Hr;
      assert (Hr5 : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
      destruct Hr5 as [-> | [-> | [-> | [-> | ->]]]];
      (lazymatch goal with |- getr _ ?rr = _ => prreg HS rr Pr end; rewrite Pr; apply EL; reflexivity)
    | ].
  all: lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) (stack_region AS_FRAME)) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HRst;
      let r3 := eval vm_compute in (nth 3 (ss_mem ssx) as_slotE) in
      pose proof (st_ok_pi_region_nth E ssx (restrict (w_H W) msx) 3 r3 HS ltac:(vm_compute; reflexivity)) as HRn end.
  all: cbn [ms_mem restrict mkst] in HRst, HRn.
  all: assert (HNA1 : aval_mem (rdW W (ms_mem msB)) (c + CALL_OFF_NARGS) 4 m);
    [ apply (aval_mem_view SEGS); change 4%nat with (N.to_nat 4);
      eapply (field_of_region E _ 10 c _ _ _ _ _ 4 4%N (SOff 33 0) m HRn UC);
      [ cbn [In]; left; reflexivity
      | cbn [sv_denot]; rewrite E33, Z.add_0_r, unsigned_lit_small by lia; reflexivity
      | cbn; lia | cbn; lia ]
    | ].
  all: assert (HFR : forall j r, nth_error as_saved j = Some r ->
    val_mem SEGS (mrestrict (w_H W) (ms_mem msB)) (spZ regs - 8 - 8 * Z.of_nat j) 8
      (bv_unsigned (getr regs (Z_to_bv 5 r))));
    [ apply (as_frame_words W (ms_mem msB) regs E (spZ regs) _ EL Usp HRst);
      intros j r Hj;
      do 8 (destruct j as [|j];
        [ cbn [nth_error as_saved] in Hj; injection Hj as <-;
          lazymatch goal with |- In ?x ?l => let y := eval vm_compute in x in change (In y l) end;
          cbn [In]; repeat (first [left; reflexivity | right]) |]);
      destruct j; cbn in Hj; discriminate
    | ].
  + (* s <> 0: s3 is the caller's string *)
    destruct HSTR' as [(Hv & Hs0) | (x & Hv & HSx)].
    { exfalso. subst s.
      assert (HU : U E (SOff 11 0) = 0) by (apply (U_atom E 11 0); [rewrite (EL 11%nat 11%bv eq_refl); exact H11 | lia]).
      rewrite branch_ne_U, HU, U_SLit in Hc0. vm_compute in Hc0. discriminate Hc0. }
    pose proof (as_str_bounds B HB IMG ly S W mem md s x HAR0 HSx) as [Hs1 Hs2].
    pose proof alloc_ceiling_value as [_ HAC].
    assert (R19 : getr (ms_regs msB) 19 = w64 s) by (rewrite P19, (EL 11%nat 11%bv eq_refl); exact H11).
    subst v.
    exact (as_from_B0 B MT TXMALLOC AMEMCPY ASTRLEN HB cmd_sig_prog_PB cmd_img_facts_tfib PRW
      ly S W regs mem md ch c fn A (Some x) R O s (ms_regs msB) (ms_mem msB) mdv
      HPRE HROD Hc HREP Hm6' HSx Hev Hlive HMOK HJ HNA1 Rsp1 R8 R9 R19 R21 R22 R3 R4 Rhi HFR).
  + (* s = 0: s3 is "(null)" *)
    destruct HSTR' as [(Hv & Hs0) | (x & Hv & HSx)].
    2:{ exfalso.
        pose proof (as_str_bounds B HB IMG ly S W mem md s x HAR0 HSx) as [Hs1 Hs2].
        pose proof alloc_ceiling_value as [_ HAC].
        assert (HU : U E (SOff 11 0) = s) by (apply (U_atom E 11 s); [rewrite (EL 11%nat 11%bv eq_refl); exact H11 | lia]).
        rewrite branch_ne_U, HU, U_SLit in Hc0. replace (zcanon 0) with 0 in Hc0 by (vm_compute; reflexivity).
        apply Bool.negb_false_iff, Z.eqb_eq in Hc0. lia. }
    subst v.
    assert (U54 : VAL (A_OBJ 54) = 0x224c0) by (rewrite (VOBJS 54%nat ltac:(vm_compute; lia)); reflexivity).
    assert (R19 : getr (ms_regs msB) 19 = w64 0x224c0).
    { rewrite P19. change 295%nat with (A_OBJ 54).
      rewrite (img_env_atomP E (A_OBJ 54) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), U54. reflexivity. }
    exact (as_from_B0 B MT TXMALLOC AMEMCPY ASTRLEN HB cmd_sig_prog_PB cmd_img_facts_tfib PRW
      ly S W regs mem md ch c fn A None R O 0x224c0 (ms_regs msB) (ms_mem msB) mdv
      HPRE HROD Hc HREP Hm6' (as_null_ok ly S W mem md HAR0 HROD) Hev Hlive HMOK HJ HNA1 Rsp1 R8 R9 R19 R21 R22
      R3 R4 Rhi HFR).
Qed.

End e.
End f.
End d.

Print Assumptions targ_s_holds.
