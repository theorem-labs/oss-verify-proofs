(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of sup_chain_clear on plugin-hostd/fuzz_command's ASan+UBSan build
   (fuzz_command.asan-ubsan, entry 0x8c570, 122 instructions to the `ret` at 0x8c754), proving a Theorem Labs lane's
   tsup_chain_clear_spec (lib/B/Prog/sup_chain_clear_c.v). A B re-walk of lib/A/Prog/sup_chain_clear.v and its _s1,
   _s2 (a working branch abd8a14a6b8): B calls record (A inlines it) and inlines arg_i (A calls it), so the
   frame, snprintf and release steps follow lib/A/Prog/answer_code.v (a working branch 2ba4488ce71). The B
   code: a 96-byte frame realigned by `andi sp,sp,-32`; a class-0 side-stack frame from __asan_stack_malloc_0
   (0x8c5d0, the use-after-return flag read through the record's const cell) with its header and shadow; record(18)
   at 0x8c668; snprintf(b, 16, "%d", id) at 0x8c68c into the frame's buffer b = F + 32, in pass 4b's art form
   (PASS4-REFIT.md E, the `+ 8` destination band of E.0 from the frame's room); arg_s(slot, b) at 0x8c698;
   rec_shape_of("chain_clear", 11) at 0x8c6b0; answer(slot, shape, 1) at 0x8c6c0 by PaFx.callS_wideF; the frame's
   release (magic, shadow f5, the flag byte through F + 56) and the epilogue. No __asan_report call and no UBSan trap
   site lies in [0x8c570, 0x8c758). Every call's frame chain is afn_pre's chain pushed at the frame pointer
   (achain_push, scc_chain_call). After the snprintf and answer, whose posts are at a new FP state, the walk goes on
   at that state (scc_st_ok_fx, PASS4-REFIT.md A.5's second way). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/sup_chain_clear.v, with its module paths and module names changed; 100 of its 144 lines of code are new or changed and 1728 lines of the source are left out. *)
(* sup_host_setting's ASan+UBSan walk (plugin-hostd/fuzz_command, fuzz_command.asan-ubsan, entry 0x8b53c = BASE +
   AF_sup_host_setting, 956 bytes, 239 instructions): a Theorem Labs lane's tsup_host_setting_spec (lib/B/Prog/sup_host_setting_c.v
   on a working branch 92195a003c6, B BASE 2) at Qed, the B re-walk of the ASan walk lib/A/Prog/sup_host_setting.v
   (a working branch e323bbe76d2).

   The walk is cut at the program points of sup_host_setting_s0.v; each segment file proves the statement of one point
   from the next one's:
     entry -> REC                 s2 (hs_seg_entry: prologue, __asan_stack_malloc_0, frame header and shadow, record)
     REC -> AL                    s3 (hs_seg_rec: arg_line)
     AL -> AS1 (at every fx1)     s8 (hs_seg_al: unpoison b, the snprintf wrapper, arg_s)
     AS1 -> L1H 0                 s4 (hs_seg_as1: re-poison b, blez, spills, the length loop's init)
     L1H n -> L1R n -> ...        s5 (hs_seg_l1h, hs_seg_l1r: the length loop; hs_seg_xm: xmalloc's return, words[0])
     L2C n -> L2S (n+1) -> ...    s6 (hs_seg_l2c, hs_seg_l2s: the join loop, then arg_s)
     AS2 -> FR -> MIX -> post     s7 (hs_seg_as2: free; hs_seg_fr: mix_call; hs_seg_mix: the digest store, the frame
                                      release, the epilogue)
   Here: the two loops by induction on the tokens left (hs_loop1, hs_loop2), the chain from AS1 at any FP state
   (hs_from_as1: the snprintf wrapper may change the FP state, so the rest of the walk runs at the state it returns),
   and the theorem (tsup_host_setting_holds), whose Section hypotheses are the statement's own and the walk's named
   record facts (a Theorem Labs lane's names, a Theorem Labs lane 09:2xZ: cmd_sig_prog_PB, cmd_val_his_PB, cmd_img_facts_tfib, PRW, FFL). The
   closing file SupHostSettingClosed.v discharges the record facts at the pinned image.

   The report and UBSan edges, each refuted at its branch (the comment line at each branch has the same text):
     0x8b6bc bltu s6,s8  -> unimp 0x8b8c0: refuted by hsb_ub_6bc at sup_host_setting_aux.v:94, from hs_cx's token
                            array premise (hsb5_arr_now)
     0x8b6c8 beqz a0     -> unimp: refuted by hsb5_seed_H at sup_host_setting_s5.v:175, from hs_regsL1's s2 = 1
     0x8b6cc beqz s7     -> unimp: refuted by hsb5_seed_H at sup_host_setting_s5.v:175, from hs_regsL1's s7 = 1
     0x8b6dc bnez a0     -> report load8 0x8b8e8: refuted by shent_ok_of_range at sup_host_setting_s5.v:605, from
                            range_addressable of &tok[n] (hsb5_arr_now)
     0x8b718 / 0x8b8c8   -> report store1 0x8b8d0: refuted by shent_ok_of_block at sup_host_setting_s5.v:1137, from
                            xmalloc's block (w, LIVE_XMALLOC (hs_wsz x)) in hs_mid's Nw
     0x8b774 bltu s5,s7  -> unimp: refuted by hsb_ub_774 at sup_host_setting_aux.v:126, from hs_cx's token array
                            premise (pass 0: sup_host_setting_s5.v:1169; passes n >= 1: sup_host_setting_s6.v:710)
     0x8b788 bnez a1     -> report load8 0x8b8ec: refuted by shent_ok_of_range at sup_host_setting_s5.v:1138
                            (pass 0) and by hsb6_seedS at sup_host_setting_s6.v:469 (passes n >= 1), from
                            range_addressable of &tok[n]
     0x8b754 / 0x8b7ac   -> report store_n 0x8b8f4: refuted by hsb6_seedS at sup_host_setting_s6.v:469, from the word
                            list's block, with |join_sp (firstn n toks)| + 2 <= |join_sp toks| + 1 (hsb_join_sep_in)
     0x8b768 / 0x8b7b8   -> report store_n 0x8b7c4: refuted by hsb6_seedS at sup_host_setting_s6.v:469, from the same
     0x8b68c blez s5     -> the ntok <= 0 arm 0x8b7d8 .. (its store1 check 0x8b7f0 -> report 0x8b8e0): refuted by
                            paj_run_to_sh at sup_host_setting_s4.v:147 (SRr_run_to_pi_AJ, the run of hs_seg_as1, seed fact s5 in
                            [1, 64], hs4_ssA), from hs_cx's 1 <= length toks <= 64 (hsb_blez_ntok,
                            sup_host_setting_aux.v:86, states the same branch fact) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05 YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString RtFormat RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
rec_calls_free_c rec_canonical_c record_c arg_line_c arg_s_c xmalloc_c mix_call_c sup_host_setting_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
sup_host_setting_aux sup_host_setting_s1 sup_host_setting_s0 sup_host_setting_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require
sup_host_setting_s2 sup_host_setting_s4 sup_host_setting_s5 sup_host_setting_s6 sup_host_setting_s7 sup_host_setting_s8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the i-th elements of two related lists are related *)
Lemma hs_forall2_nth : forall {X Y : Type} (P : X -> Y -> Prop) l1 l2 i a b,
  Forall2 P l1 l2 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b.
Proof.
intros X Y P l1 l2 i a b H. revert i. induction H as [|a' b' l1 l2 Hab H IH]; intros i H1 H2;
  [destruct i; discriminate|].
destruct i as [|i]; cbn in H1, H2; [injection H1 as <-; injection H2 as <-; exact Hab | exact (IH i H1 H2)].
Qed.

Lemma hs_fxrel_refl : forall fx0 : YK11.FPState, hs_fxrel fx0 fx0.
Proof. intros fx0. split; [intros k _; reflexivity | left; reflexivity]. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis HH : hs_hyps B MT.

(* the join loop: from AS2, every pass n is proved, by induction on the passes left *)
Lemma hs_loop2 : forall x, ST_AS2 B MT x -> forall k n, (n + k = length (i_toks x) - 1)%nat -> ST_L2C B MT x n.
Proof.
intros x AS2 k. induction k as [|k IH]; intros n Hn.
- apply (sup_host_setting_s6.hs_seg_l2c B MT HH x n); [intros H; exfalso; lia | intros _; exact AS2].
- apply (sup_host_setting_s6.hs_seg_l2c B MT HH x n); [|intros _; exact AS2].
  intros _. apply (sup_host_setting_s6.hs_seg_l2s B MT HH x (S n)). apply IH. lia.
Qed.

(* the length loop: from XM, every pass n is proved, by induction on the passes left *)
Lemma hs_loop1 : forall x, ST_XM B MT x -> forall k n, (n + k = length (i_toks x) - 1)%nat -> ST_L1R B MT x n.
Proof.
intros x XM k. induction k as [|k IH]; intros n Hn.
- apply (sup_host_setting_s5.hs_seg_l1r B MT HH x n); [intros H; exfalso; lia | intros _; exact XM].
- apply (sup_host_setting_s5.hs_seg_l1r B MT HH x n); [|intros _; exact XM].
  intros _. apply (sup_host_setting_s5.hs_seg_l1h B MT HH x (S n)). apply IH. lia.
Qed.

(* from AS1 (back from arg_s(c, b)) to the end, at the FP state of this Section *)
Lemma hs_from_as1 : forall x, ST_AS1 B MT x.
Proof.
intros x.
pose proof (sup_host_setting_s7.hs_seg_as2 B MT HH x
  (sup_host_setting_s7.hs_seg_fr B MT HH x (sup_host_setting_s7.hs_seg_mix B MT HH x))) as AS2.
pose proof (sup_host_setting_s5.hs_seg_xm B MT HH x (hs_loop2 x AS2 (length (i_toks x) - 1) 0 ltac:(lia))) as XM.
exact (sup_host_setting_s4.hs_seg_as1 B MT x
  (sup_host_setting_s5.hs_seg_l1h B MT HH x 0 (hs_loop1 x XM (length (i_toks x) - 1) 0 ltac:(lia)))).
Qed.
End e.
End f.
End d.

Section d2. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f2.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e2.
Variable B : asyms.
Variable MT : ameter_ops.
(* tsup_host_setting_spec's own hypotheses (sup_host_setting_c.v Section e) *)
Hypothesis TRECORD : forall fx0 : YK11.FPState, @trecord_spec fx0 rc SK PI B MT.
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TARG_S : forall fx0 : YK11.FPState, @targ_s_spec fx0 rc SK PI B MT.
Hypothesis TXMALLOC : forall fx0 : YK11.FPState, @txmalloc_spec fx0 rc SK PI B MT.
Hypothesis TMIX_CALL : forall fx0 : YK11.FPState, @tmix_call_spec fx0 rc SK PI B MT.
Hypothesis ASTACK_MALLOC0 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 0.
Hypothesis AFREE_LAW : astack_free_law SEGS B.
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @asnprintf_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_snprintf) 0xa6bf8 0x604158.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, @afree04_rule fx0 rc SK SEGS B MT.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strlen).
Hypothesis ASTRCAT : forall fx0 : YK11.FPState, @astrcat_realizes fx0 rc SEGS B (SIG CS___interceptor_trampoline_strcat).
Hypothesis VOBJS : cmd_val_objs.
(* the walk's: the allocator record, the trampolines' and side-stack entries' pcs, the meter's laws, and the facts
   a Theorem Labs lane states at the pinned listing only (named as its lemmas: CmdRecRest.cmd_sig_prog_PB / cmd_val_his_PB,
   CmdRecImg.cmd_img_facts_tfib; PRW, the program statics' writability; FFL, the frames' flag law, as A's walks name
   CmdRecRest.cmd_frame_flag_law) *)
Hypothesis HB : CmdBSyms B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTLF : ameter_fs_laws MT.
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Hypothesis cmd_val_his_PB : cmd_val_his.
Hypothesis cmd_img_facts_tfib : forall B0, CmdBSyms B0 -> cmd_img_facts SEGS B0.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.

Lemma hs_hyps_of : hs_hyps B MT.
Proof.
exact {| hh_record := TRECORD; hh_arg_line := TARG_LINE; hh_arg_s := TARG_S; hh_xmalloc := TXMALLOC;
  hh_mix := TMIX_CALL; hh_smalloc0 := ASTACK_MALLOC0; hh_free_law := AFREE_LAW; hh_snprintf := ASNPRINTF;
  hh_free := AFREE4; hh_strlen := ASTRLEN; hh_strcat := ASTRCAT; hh_vobjs := VOBJS; hh_HB := HB; hh_TL := TL;
  hh_TLF := TLF; hh_MTL := MTL; hh_MTLF := MTLF; hh_sigp := cmd_sig_prog_PB; hh_vhis := cmd_val_his_PB;
  hh_img := cmd_img_facts_tfib B HB; hh_prw := PRW; hh_FFL := FFL |}.
Qed.

Theorem tsup_host_setting_holds : tsup_host_setting_spec B MT.
Proof.
pose proof hs_hyps_of as HH.
unfold tsup_host_setting_spec.
intros ly S W regs mem md ch pl ptok ps line toks R O HPRE HRM0 HROD HRO H10 Hpl H11 Hptok H12 HNT
  (LB & LAP & LSTR & LLEN) Hp0 Hp8 HARR HLPS HPS HTOKS HWL HREP HFRM HEV HLIVE HMO.
pose proof HPRE as (HAR & _).
(* a string of the statement's block form is the walk's hs_str: its pointer lies in a live block, so it is not 0 *)
assert (STR : forall p w, in_blockA (ablocks B ly S) p (Z.of_nat (length w) + 1) ->
  Forall (fun qk => iv_apart p (Z.of_nat (length w) + 1) (fst qk) (snd qk)) O ->
  astr_atR (rdW W mem) p w -> Z.of_nat (length w) + 1 <= LMAX + 1 -> hs_str B ly S (rdW W mem) O p w).
{ intros p w Hb Hap Hs Hl. pose proof Hb as (q & m & Hqm & Hq1 & Hq2).
  destruct (al_blocks _ _ (AR_laws_ok SEGS B) _ _ _ _ _ q m HAR Hqm) as (_ & Hq4096 & _).
  split; [lia|]. split; [exact Hs|]. split; [exact Hl|]. split; [exact Hb | exact Hap]. }
assert (CX : hs_cx B MT (mkHsIn ly S W regs mem md ch pl ptok ps line toks R O fx)).
{ refine (conj HPRE (conj HROD (conj HRO (conj (conj Hpl Hptok) (conj H10 (conj H11 (conj H12 (conj HNT
    (conj (STR pl line LB LAP LSTR LLEN) (conj Hp0 (conj Hp8 (conj HARR (conj HLPS (conj HPS (conj _
    (conj HWL (conj HREP (conj HFRM (conj HEV (conj HLIVE (conj HMO (conj _ HRM0)))))))))))))))))))))).
  - eapply Forall2_impl; [|exact HTOKS]. intros p w (Hb & Hap & Hs & Hl). exact (STR p w Hb Hap Hs Hl).
  - (* each token's terminator lies in its block, so its tail is visible *)
    intros i p w Hp Hw. destruct (hs_forall2_nth _ _ _ i p w HTOKS Hp Hw) as ((q & m & Hqm & Hq1 & Hq2) & _ & _ & _).
    apply (hh_heap_tail B MT HH ly S W mem md q m _ HAR Hqm). lia. }
exact (sup_host_setting_s2.hs_seg_entry B MT HH _ CX (hs_fxrel_refl fx)
  (sup_host_setting_s3.hs_seg_rec B MT HH _
    (sup_host_setting_s8.hs_seg_al B MT HH _ (fun fx1 => @hs_from_as1 fx1 rc SK PI B MT HH _)))).
Qed.
End e2.
End f2.
End d2.
Print Assumptions tsup_host_setting_holds.
