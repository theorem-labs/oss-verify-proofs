(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/B/Prog/LLVMFuzzerTestOneInput_segX_exit_td.v, with its module paths, module names and numbers changed; 619 of its 648 lines of code are new or changed and 323 lines of the source are left out. *)
(* fuzz_preset, image A' (#102 pins: asan sha256 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the PROOF of
   CA11 End of the re-walk of check_no_overread (cno) against the kit's text tcheck_no_overread_specX: from CN_END
   (offset 1108, A' 0x81d58) to the `ret` at 1464 (0x81ebc). Lane CnoA102f's sub-lane CnoA102fE (a Theorem Labs lane, #102
   plan, the internal file PLAN-cno-caw-102.md section 5.1 row CA11); re-fitted to the kit's Batch 2, to the #102 kit and
   then to the kit cut 7cdbb61b5fa0 by lane CnoABatch2.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   STATEMENT: lib/A/Prog/Cno102A_F.v cn_seg_endP (re-fitted to the re-hiding move), over the contract
   lib/A/Prog/Cno102A_Base.v (same commit, blob
   ba76a7bc31c9, the kit cut, with its R forms): no run-word list DW (DW-SPLIT: `cn_pre CTX0 D`, read BY NAME
   through the base's cn_pre_* projections); the cut cn_at_end lies AFTER the frees, so it is at
   `cn_baseR .. (wle' SEGS RZ_cf) .. k 6`, its journal at the walk's relation wle' SEGS RZ_cf AND AT THE WILD BUDGET
   (`exists WS, ajournal_xwR .. (wle' SEGS RZ_cf) .. k WS /\ wbudget [] 6 WS`), carries g_own_ran_out / g_most in its
   ledger `.. ran (ci_most D) ownl`, under ownl = 0 the events made since entry, `exists o1 o2 o0, cn_prog D (cn_C3 D
   ++ cn_revs3 D o1 o2 o0 ++ cn_fevs D o1 o2 o0) S /\ ran = cn_ranz D o1 o2 o0`, `ownl <> 0 -> cn_cdead D`
   (CNO-COPY) and last the hull budget `hull_budget S (cn_hF3 (ci_x D))` (unused here: CA11 makes no allocator
   call); the exit cn_ex_ret
   is the text's full post cn_Q under the kit's `fpostFb .. (wbudget [] (prh_wk F_check_no_overread))`, which is
   YCbqGwild.apost_base_xbFR at wle' SEGS RZ_cf (one more binder WS and its budget), its ledger `.. ran' (ci_most D)
   own'`, the r fact, CNO-COPY (own' = 0 at a consumer run whose next events are ck_cno_copies) and, under own' =
   0, the grants' r, live set and position implication over ck_cno_evs. The segment concludes SRr' SEGS RZ_cf: CA11
   frees nothing, but its journal from entry crosses the frees, and the engine's runner and call rules over R
   (YC1fPx paj_run_x_invR, YGcallMxmn aj_set_shadow_at_xmR, Cno102_FKit paj_flag_store_x_invR) conclude SRrG at the
   journal's R. Neither file is changed here.
   THE CODE (the A' disassembly of check_no_overread; DERIVED offsets inside cno, slot
   kinds on Listing_prog.v, CN_SLOT = 201, CN_OFF = 804):
     1108 li a0, -8 ; 1112-1192 21 x `sb a0, off(s2)` (the struct slots' shadow re-poisoned, offs 4..7, 8..0xa,
     0x10..0x16, 0x1c..0x22, all inside F's shadow) ; 1196 / 1200 a0 = 0x45e0360e ; 1204 sd a0, 0(s11) (the frame's
     magic) ; 1208 ld s3, 32(s1) (= F) ; 1212 beqz s3 (NOT taken: F >= 4096 by the frame law) ; 1216 li a1, 64 ;
     1220 mv a0, s2 ; 1224 jal __asan_set_shadow_f5 (PCall, ra = cn_pc CN_SS5R) ; 1228 ld a0, 504(s3) (the flag
     pointer, at F + fs_frame_bytes 3 - 8) ; 1232 sb zero, 0(a0) (the inline release) ; 1236 j 1400 ;
     1400 mv a0, s5 ; 1404 addi sp, s0, -192 ; 1408-1456 13 x ld (the saved registers) ; 1460 addi sp, sp, 192 ;
     1464 ret.
   THE WILD BUDGET: the epilogue's rules are all at the empty budget. The cut's journal at budget WS is REBASED
   (YCbqGwild.ajournal_xw_rebaseR at wle' SEGS RZ_cf: a plain journal from the entry with its depot moved to the
   cut's, `set_depot (st_depot S) (ci_S D)`), the three stages run the engine's journal rules over R on it, and the
   post UNBASES it back to the entry at the cut's own WS (YCbqGwild.ajournal_xw_unbase0R, its depot inclusion the cut
   journal's ajxR_wild); the post's budget is that WS, `wbudget [] 6 WS` (prh_wk F_check_no_overread = 6). The entry
   facts of the journal (ARx, layout, block and image keeps) are read from the cut's journal by the ajxR_ projections.
   THE THREE STAGES (each checked by the engine on the listing, no hand-stepping):
     1. 1108 -> the call at 1224: one run of the P-carrying runner twin over R, paj_run_x_invR (YC1fPx.v) at
        R := wle' SEGS RZ_cf; the writes are F's shadow bytes and F's first word, both the own frame's (awr_byte's
        in_frames arm at own = [(3, fpos)]); the branch at 1212 is decided by the frame atom's range fact.
     2. the call: YGcallMxmn.aj_set_shadow_at_xmR at R := wle' SEGS RZ_cf with its two laws (the engine's set_shadow
        rule over a journal at R; the call keeps the world, so the rule concludes plain SRr, lifted by
        YA0nH.SRr_SRr') at q = shadow_addr F, n = 64, cid = 3 (fs_frame_bytes 3 = 512, so q + 64 = shadow_addr F +
        fs_frame_bytes 3 / 8), the contract the Section hypothesis SS5M; P crosses it by srr_inv_call at the rule's
        memnorm keep; YSRrG.SRr'_bind after it.
     3. 1228 -> the `ret`: one run of Cno102_FKit.paj_flag_store_x_invR (the R form of the P-carrying twin of
        YGcallSx's aj_flag_store_x) at ARcfx and R := wle' SEGS RZ_cf, its three allocator hypotheses discharged by
        YGcallScf (astack_free_x_xs, frame_flag_x_xs, stack_free_x_any); then YC1fP.paj_ret_at, lifted by
        YA0nH.SRr_SRrG at wle_wle', and the post.
   THE POST cn_Q: Lam, peak, cnt, ran and own' := ownl of the cut; the cut's ledger `.. ran (ci_most D) ownl` carried
   across the three stages by S1Ledger.prh_ledger_kept_aview: the statics (g_most and g_own_ran_out among them) are
   prh_pst cells, image bytes, so PSTK keeps them (the run writes F's shadow and F's first word, set_shadow writes
   [q, q + 64), the release the flag byte; none is an image byte: frm_img_x, Fimg), and HEADK keeps the head words.
   The r fact: the cut's (r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0) with the ledger's own
   cell (PRH_Base.prh_ledger_own: ownl = 0 \/ ownl = 1). CNO-COPY: own' = ownl is 0, or the cut's cn_cdead D
   refutes the consumer run. Under own' = ownl = 0: the cut's grants o1 o2 o0; the events
   are ck_cno_evs by the base's cn_ck_cno_evs; r = ran (the r fact at ownl = 0) = cn_ranz D o1 o2 o0, which is the
   post's `if ck_cno_ranout .. then 1 else 0`; the stages change the allocator state only by the release's
   stack_free_state, a set_fs, so the live list rs_live (room_of_cf S) is the same by conversion and the position
   after the events is kept by PresetRoomPosKeep.room_pos_stack_free.
   SECTION HYPOTHESES (owners): SS5M (the frozen __asan_set_shadow_f5 contract with the memnorm keep, the engine's
   YGcallMxmn.aset_shadow_realizes_xm, fx-generic because the run is at the cut's float state fxk; owner a Theorem Labs lane);
   ENV (api_env SEGS B, aj_set_shadow_at_xmR's errno_low; no cf fact of this walk gives it; owner the unit's image
   binding of B, as FuzzFree.v's PAL); HW (PRH_Base.v:241 prh_head_wide, the ONE spelling: the ledger's head
   words are kept only if the head is a granule wide; owner a Theorem Labs lane, discharged at the preset instance by
   preset_head_wide, CfParamsPreset.v:103); IMG (the base's cn_img B). No other; no Admitted, no axiom, no stand-in.
   INPUTS (by path; blobs at the kit cut 7cdbb61b5fa0 unless named): the base and the statement above; kit
   lib/A/Prog/Cno102_FKit.v 16b038eac014 (4b59cadb07a1) and lib/A/Prog/S1Ledger.v 8cf15eeb6311
   (prh_ledger_kept_aview, prh_ledger_hblock; `most own` their last binders); lib/A/PRH_Base.v (prh_ledger,
   prh_ledger_own, fpre, fpostFb at wle', prh_wk); PRH_FnCheck.v (tcheck_no_overread_specX); lib/Spec/
   PresetRoomPosKeep.v dc3f6bee1e0e (room_pos_stack_free); engine by path (YC1fPx, YC80x, YCbqG, YCbqGwild,
   YGcallMxmn, YGcallSx, YGcallScf, YSRrMemnorm; the re-hiding move: YA0nH SRr' / wle' / SRr_SRr' / SRr_SRrG,
   YSRrG SRr'_bind, YGcfRehidePost RZ_cf); the kit texts of the base's set.
   Numerals: the offsets above (DERIVED); 192 / 32 / 504 / 64 / 8 / 16 / 4 (LENGTH: frame, slot and shadow-range
   offsets and widths); 3 (the frame class); 245 (WORD: the shadow byte 0xf5); register and atom numbers (WORD);
   2 ^ 63 (DERIVED: the runs' empty shadow span). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00cf YG01cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallx YGcallcf YGcallSx YGcallScf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcall YCbqGcallW YG0lawscf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YCbqGwild.
(* the re-hiding move: SRr' / wle' / the lifts (YA0nH), SRr'_bind (YSRrG), the zone RZ_cf (YGcfRehidePost) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger PvFdZeroR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos PresetLiveBounds
  PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Img PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ PRW_StepKit Cno102_FKit
  Cno102A_Base Cno102A_F.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1Ledger.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
(* PRW_StepKit loads YF0v.v, which turns the euclidean-division flag OFF globally (lead's build trap, WalkS4's
   measurement): turn it back on, as S4_PsU.v does, so lia sees the Z.div / Z.modulo of shadow_addr and the
   realigned sp. MEASURED NEEDED (the lead's 15:2xZ rule: only where a build fails without it): without this line the
   file fails at the lia of cn_seg_end's first stage, "No applicable tactic" (a Theorem Labs lane
   the internal file build-20261029T160953Z.log). *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the realigned body sp: `addi sp, sp, -192 ; andi sp, sp, -32` ---- *)
Lemma cn_land32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (- 2 ^ 5). rewrite land_neg_pow2 by lia. change (2 ^ 5) with 32. reflexivity.
Qed.

(* ---- the symbolic states (no image value: atoms only; 0..31 the ENTRY registers, 32..63 the current ones,
   64 the flag pointer) ---- *)
Definition cn_cur (regs : bvmap 5 word) : list word := map (getr regs) all_regs.
(* at CN_END: every register its current atom *)
Definition cn_sr1 : list sv := SLit 0 :: map (fun i => SOff (32 + i) 0) (seq 1 31).
(* F's shadow (s2, atom 50), F's first word (s11, atom 59), and the body-sp slot at s1 + 32 holding F *)
Definition cn_rg_sh : YP09.region := YP09.mkRegion (Some 50%nat) 4 35 4 35 [].
Definition cn_rg_F : YP09.region := YP09.mkRegion (Some 59%nat) 0 8 0 8 [].
Definition cn_rg_s1 : YP09.region := YP09.mkRegion (Some 41%nat) 32 40 32 32 [YP09.mkChunk 32 (CVal 8 (SOff 59 0))].
Definition cn_facts1 : facts :=
  mkFacts [(59%nat, mkAF 4096 (2 ^ 47) 5); (50%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
           (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] [].
Definition cn_ss1 : sstate := mkSS (CN_OFF + CN_END) cn_sr1 [cn_rg_sh; cn_rg_F; cn_rg_s1] None cn_facts1.

(* at CN_SS5R (the call's return site): sp / s0 / gp / tp are the entry's atoms, the rest current; s3 = F *)
Definition cn_sr3 : list sv :=
  [SLit 0; SOff 33 0; SOff 34 0; SOff 3 0; SOff 4 0; SOff 37 0; SOff 38 0; SOff 39 0; SOff 2 0] ++
  map (fun i => SOff (32 + i) 0) (seq 9 23).
(* the flag word at F + 504 (= F + fs_frame_bytes 3 - 8), the flag byte, and the 13 saved words below the entry sp *)
Definition cn_rg_ff : YP09.region := YP09.mkRegion (Some 51%nat) 504 512 504 504 [YP09.mkChunk 504 (CVal 8 (SOff 64 0))].
Definition cn_rg_fl : YP09.region := YP09.mkRegion (Some 64%nat) 0 1 0 1 [].
Definition cn_rg_fr : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 0 0
  [ YP09.mkChunk (-8) (CVal 8 (SOff 1 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
    YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
    YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
    YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
    YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
    YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
    YP09.mkChunk (-104) (CVal 8 (SOff 27 0)) ].
Definition cn_facts3 : facts :=
  mkFacts [(51%nat, mkAF 4096 (2 ^ 47) 5); (64%nat, mkAF 0 (2 ^ 47) 0); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
Definition cn_ss3 : sstate := mkSS (CN_OFF + CN_SS5R) cn_sr3 [cn_rg_ff; cn_rg_fl; cn_rg_fr] None cn_facts3.
(* the run of stage 3, by computation: the flag store, the jump, the epilogue, the `ret` *)
Definition cn_K3 : nat := Eval vm_compute in (run_K A_LIM (SLit 0) [] cn_ss3).
Definition cn_res3 := Eval vm_compute in
  (sym_runN_pi_tok (@pl_tpi _ PL_cno_A) (@pl_tw _ PL_cno_A) cn_K3 (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL cn_ss3).
Definition cn_st3 : shst := Eval vm_compute in (fst cn_res3).
Definition cn_r3 : ptrun_status asym := Eval vm_compute in (snd cn_res3).
Definition cn_mem3 : smem := Eval vm_compute in (ss_mem (sh_ss cn_st3)).
Lemma cn_run3_eq : sym_runN_pi_tok (@pl_tpi _ PL_cno_A) (@pl_tw _ PL_cno_A) cn_K3 (SLit 0) (2 ^ 63, 2 ^ 63) [] FUEL cn_ss3
  = (cn_st3, cn_r3).
Proof. vm_compute. reflexivity. Qed.
Lemma cn_r3_not_call : match cn_r3 with PTS_call _ => False | PTS_ecall => False | _ => True end.
Proof. vm_compute. exact I. Qed.
Lemma cn_j3 : sh_j cn_st3 = 0%nat.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_obls3 : sh_obls cn_st3 = [].
Proof. vm_compute. reflexivity. Qed.
Lemma cn_mem3_eq : ss_mem (sh_ss cn_st3) = cn_mem3.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_static3 : sh_static_ok cn_K3 (SLit 0) (2 ^ 63, 2 ^ 63) [] (ss_facts cn_ss3) (ss_mem cn_ss3) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cn_K3_lim : (A_LIM <= cn_K3)%nat.
Proof. unfold A_LIM, cn_K3. lia. Qed.
Lemma cn_off_ss5r : CN_OFF + CN_SS5R = 2032.
Proof. vm_compute. reflexivity. Qed.

Section env. Context {rc : YM05.RunCeil}.
Context {L : ptable asym} {PI : PAImg L}.
Lemma cn_ew_hi : forall R X n, (32 <= n < A_TEXT)%nat -> ew (Eimg (Ereg R X)) n = nth (n - 32) X (Z_to_bv 64 0).
Proof.
intros R X n Hn. rewrite Eimg_low by lia. unfold Ereg. cbn [ew].
replace (n <? 32)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity.
Qed.
Lemma cn_ew_lo : forall R X n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (Eimg (Ereg R X)) n = getr R r.
Proof.
intros R X n r H. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat R X n r H).
Qed.

Ltac cn_reg1 :=
  lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite cn_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth cn_cur map all_regs];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ].

Lemma cn_regs_ok_1 : forall (R : bvmap 5 word) (regs : bvmap 5 word),
  regs_ok (Eimg (Ereg R (cn_cur regs))) cn_sr1 regs.
Proof.
intros R regs. apply regs_ok_by_cases. intros rr Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cn_reg1|]). destruct Hr.
Qed.

Ltac cn_reg3 H3 H4 H8 :=
  lazymatch goal with |- _ = sv_denot ?E (sr_get ?sr ?r) =>
    let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
  cbn [sv_denot];
  first
  [ rewrite getr_zero; reflexivity
  | rewrite (cn_ew_lo _ _ 3 3 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H3
  | rewrite (cn_ew_lo _ _ 4 4 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H4
  | rewrite (cn_ew_lo _ _ 2 2 eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact H8
  | rewrite cn_ew_hi by (unfold A_TEXT; lia); cbn [Nat.sub nth cn_cur map all_regs app];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity ].

Lemma cn_regs_ok_3 : forall (R : bvmap 5 word) (regs : bvmap 5 word) (flw : word),
  getr regs 3 = getr R 3 -> getr regs 4 = getr R 4 -> getr regs 8 = getr R 2 ->
  regs_ok (Eimg (Ereg R (cn_cur regs ++ [flw]))) cn_sr3 regs.
Proof.
intros R regs flw H3 H4 H8. apply regs_ok_by_cases. intros rr Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [cn_reg3 H3 H4 H8|]). destruct Hr.
Qed.
End env.

(* ONE saved word of the epilogue's frame region: the chunk at coff below the entry sp holds the entry
   register rn (the cut's cn_saved fact SA, at the saved offset soff), and the two steps before the
   epilogue kept it (SVk). YE is `ew E n = getr R rn` for the environment of the stretch. *)
Ltac cn_frch YE SVk n rn coff soff SA :=
  lazymatch type of SA with
  | _ = Some (bv_unsigned (getr ?R _)) =>
    lazymatch goal with
    | |- YP09.chunk_ok ?segs ?E ?m ?base _ =>
      apply (chunk_ok_val segs E m base coff 8 (SOff n 0) (bv_unsigned (getr R rn)));
      [ cbn [sv_denot]; rewrite (YE n rn eq_refl); rewrite ?Z.add_0_r; reflexivity
      | pose proof (u64_range (getr R rn)); change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia
      | cbn; lia
      | lazymatch goal with
        | |- val_mem _ _ ?a _ _ => replace a with (base - 192 + soff) by lia
        end;
        apply (val_mem_of_rdword segs); rewrite SVk by lia; exact SA ]
    end
  end.

Section cfe. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_A.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B prh_pst ARcfx).
#[local] Notation STK := STK_check_no_overread.
Variable CTX0 : list (list Z).

(* the allocator's laws at the cf instance (FuzzFree.v:405-406) *)
Let LAWS : AR_laws_x SEGS B ARcfx cf_head := AR_laws_x_xs SEGS B (AR_laws_ok_cf SEGS B).

(* ---- the Section hypotheses (header: owners) ---- *)
Hypothesis SS5M : forall fz : YK11.FPState,
  @YGcallMxmn.aset_shadow_realizes_xm fz SEGS B ARcfx (SIGMA AS___asan_set_shadow_f5) 245.
Hypothesis ENV : api_env SEGS B.
Hypothesis HW : prh_head_wide.
Hypothesis IMG : cn_img B.

(* a read-only image byte is an image byte (S4_PsRet.v ps_ro_img) *)
Lemma cn_ro_img : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> in_img SEGS a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PA a Hr)].
Qed.
(* the view determines the byte *)
Lemma cn_mbyte_of_aview : forall (W W' : world SEGS) (m m' : word -> option byte) a,
  aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a ->
  mbyte SEGS (mrestrict (w_H W') m') a = mbyte SEGS (mrestrict (w_H W) m) a.
Proof.
intros W W' m m' a H. unfold aview, option_map in H.
destruct (mbyte SEGS (mrestrict (w_H W') m') a) as [b1|] eqn:E1;
destruct (mbyte SEGS (mrestrict (w_H W) m) a) as [b2|] eqn:E2; try discriminate; [|reflexivity].
injection H as H. f_equal. apply bv_eq. exact H.
Qed.

Theorem cn_seg_end : cn_seg_endP B CTX0.
Proof.
intros P PLAW PCALL D fxk ly S Hp W regs mem md k Lam peak cnt ran r ownl HPRE HAT HPM.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cf_head_nonneg as CH0.
assert (HF512 : fs_frame_bytes CN_CID = 512) by (vm_compute; reflexivity).
assert (HSTKv : STK_check_no_overread = 27424) by (vm_compute; reflexivity).
assert (HESv : ESTACK = 4096) by reflexivity.
(* ---- the cut ---- *)
pose proof HAT as (HBASE & HRS & HFw & HLED & HPL & HPB & HPK & HCNT & HRL & HRES & HEVS & HCD & _).
pose proof HBASE as (Hfrm & Hfk & (WS & HJW & HWB) & HFRM & HSV & Hgp & Htp & HROD).
(* THE CUT'S JOURNAL IS AT THE WALK'S RELATION wle' SEGS RZ_cf AND AT THE WILD BUDGET wbudget [] 6 WS. The epilogue
   (the stores, set_shadow, the release) runs on it REBASED: a journal at R from the entry with its depot moved to the
   cut's (YCbqGwild.ajournal_xw_rebaseR); the post unbases it back to WS (ajournal_xw_unbase0R, by ajxR_wild of HJW) *)
pose proof (YCbqGwild.ajournal_xw_rebaseR (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf) _ _ _ _ _ (ci_Hp D)
  _ _ _ _ _ _ _ _ _ _ _ _ HJW) as HJ.
pose proof HFRM as (Hfrs & Hnew & Hflagw & HFpres & HSHpres).
unfold cn_regsat, cn_core in HRS.
apply Forall_cons_iff in HRS as (Rsp & HRS).
apply Forall_cons_iff in HRS as (Rs0 & HRS).
apply Forall_cons_iff in HRS as (Rs1 & HRS).
apply Forall_cons_iff in HRS as (Rs2 & HRS).
apply Forall_cons_iff in HRS as (Rs11 & HRS).
apply Forall_cons_iff in HRS as (Rs5 & HRS). clear HRS.
cbn [fst snd] in Rsp, Rs0, Rs1, Rs2, Rs11, Rs5.
(* ---- the entry ---- *)
(* cn_pre BY NAME (the base's projections) *)
pose proof (cn_pre_fpre (fx := fx) B ARcfx CTX0 D HPRE) as HFP.
pose proof (cn_pre_src (fx := fx) B ARcfx CTX0 D HPRE) as HSRC.
pose proof (cn_pre_home (fx := fx) B ARcfx CTX0 D HPRE) as HHOME.
pose proof (cn_pre_ledger (fx := fx) B ARcfx CTX0 D HPRE) as HLED0.
pose proof HFP as (HPX & HROD0 & HSTKHI & HRAZ & HFZ0).
pose proof HPX as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof Hstk0 as (Hal16 & HSTK0 & Hceil0 & Hslo0 & Hshi0 & H47a & Hbot0 & Htop0).
(* ---- the journal, the frame and the flag ---- *)
(* the journal read BY NAME (YCbqG's ajxR_ projections) at the cut's own budget WS, from the entry *)
pose proof (ajxR_ar HJW) as HARc. pose proof (ajxR_ly HJW) as Hly. pose proof (ajxR_blk HJW) as Jblk.
pose proof (ajxR_img HJW) as Jimg.
set (fp := ci_fpos D) in *.
assert (Hin : In (CN_CID, fp) (frames S)) by (rewrite Hfrs; left; reflexivity).
pose proof Hly as (_ & _ & _ & _ & _ & ELF & _ & _ & Etop & Eslo & Eshi & _).
assert (EFa : frame_addr ly CN_CID fp = cn_F D) by (unfold cn_F, frame_addr; rewrite ELF; reflexivity).
destruct (frames_bounds_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID fp HARc Hin) as (Fb1 & Fb2 & Fb3).
destruct (alx_frames SEGS B ARcfx LAWS ly S Hp W mem md CN_CID fp HARc Hin) as (Fal & _ & Ffr & Fsh).
rewrite ?EFa, ?HF512 in Fb1, Fb2, Fb3, Fal, Ffr, Fsh.
assert (FappL : cn_F D + 512 <= kLowShadowBeg \/ kHighMemBeg <= cn_F D)
  by (unfold in_app in Fb3; rewrite HF512 in Fb3; tauto).
unfold kLowShadowBeg, kHighMemBeg in FappL.
destruct (frame_flag_x_xs SEGS B ly S Hp W mem md CN_CID fp HARc Hin) as (Fown & Fapp & Fimg).
set (fl := flag_addr ly CN_CID fp) in *.
assert (Hflf : fl + 1 <= cn_F D \/ cn_F D + 512 <= fl).
{ destruct (Z_lt_le_dec fl (cn_F D)) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (cn_F D + 512) fl) as [Hg|Hg]; [right; lia|].
  exfalso. exact (proj2 (Ffr fl ltac:(lia)) Fown). }
assert (Hsh1 : SHADOW_OFF <= shadow_addr (cn_F D) /\ shadow_addr (cn_F D) + 64 <= SHADOW_OFF + 2 ^ 44)
  by (unfold shadow_addr, SHADOW_OFF in *; lia).
assert (Hfls : fl + 1 <= shadow_addr (cn_F D) \/ shadow_addr (cn_F D) + 64 <= fl).
{ destruct (Z_lt_le_dec fl (shadow_addr (cn_F D))) as [Hl|Hl]; [left; lia|].
  destruct (Z_le_gt_dec (shadow_addr (cn_F D) + 64) fl) as [Hg|Hg]; [right; lia|].
  exfalso. replace fl with (shadow_addr (cn_F D) + (fl - shadow_addr (cn_F D))) in Fown by lia.
  exact (proj2 (Fsh (fl - shadow_addr (cn_F D)) ltac:(change (512 / 8) with 64; lia)) Fown). }
assert (Hflow : 4096 <= fl /\ fl < YM05.alloc_ceiling).
{ unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Fapp. lia. }
(* the two stacks *)
assert (HS1lo : cn_sp0 D - 224 <= cn_S1 D <= cn_sp0 D - 192).
{ unfold cn_S1. rewrite cn_land32. pose proof (Z.mod_pos_bound (cn_sp0 D - 192) 32 ltac:(lia)). lia. }
assert (HS1m32 : cn_S1 D mod 32 = 0).
{ unfold cn_S1. rewrite cn_land32. rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
assert (Hsp016 : cn_sp0 D mod 16 = 0) by exact Hal16.
assert (HS1m16 : cn_S1 D mod 16 = 0) by lia.
assert (Hsp0lo : YM05.alloc_ceiling + 27424 <= cn_sp0 D) by (unfold cn_sp0 in *; lia).
assert (Hsp0hi : cn_sp0 D <= 2 ^ 47) by (unfold cn_sp0 in *; lia).
assert (HFAR : cn_F D + 512 < cn_sp0 D - 104 /\ shadow_addr (cn_F D) + 64 < cn_sp0 D - 104)
  by (unfold SHADOW_OFF in *; lia).
assert (Hsp0 : spZ regs = cn_S1 D)
  by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small; lia).
(* ---- STAGE 1: the run from CN_END to the call ---- *)
set (E1 := Eimg (Ereg (ci_regs D) (cn_cur regs))).
assert (HEI : img_env VAL A_LIM E1) by (unfold E1; apply Eimg_env).
assert (X50 : bv_unsigned (ew E1 50) = shadow_addr (cn_F D)).
{ unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs].
  rewrite Rs2. unfold w64. apply unsigned_lit_small. unfold SHADOW_OFF in *; lia. }
assert (X59 : bv_unsigned (ew E1 59) = cn_F D).
{ unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs].
  rewrite Rs11. unfold w64. apply unsigned_lit_small. lia. }
assert (X41 : bv_unsigned (ew E1 41) = cn_S1 D).
{ unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs].
  rewrite Rs1. unfold w64. apply unsigned_lit_small. lia. }
assert (HS1 : st_ok_pi SEGS VAL E1 cn_ss1
  (restrict (w_H W) (@YK11.mkst fxk regs (Z_to_bv 64 (BASE + (CN_OFF + CN_END))) mem (YK11.seg_rom SEGS)))).
{ unfold cn_ss1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply cn_regs_ok_1.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [..|apply Forall_nil];
      unfold region_ok, cn_rg_sh, cn_rg_F, cn_rg_s1;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite X50. split; [unfold SHADOW_OFF in *; lia|]. split; [unfold SHADOW_OFF in *; lia|].
      split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HSHpres. rewrite HF512. change (512 / 8) with 64. lia.
    + rewrite X59. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply HFpres. rewrite HF512. lia.
    + rewrite X41. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E1 _ _ 32 8 (SOff 59 0) (cn_F D)).
      * cbn [sv_denot]. rewrite X59, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * exact (val_mem_of_rdword SEGS (w_H W) mem _ _ HFw).
  - apply pairwise_disjoint_of_extents.
    unfold cn_rg_sh, cn_rg_F, cn_rg_s1, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite X50, X59, X41.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [cn_facts1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    split; [|split; [|split; [|exact I]]].
    + rewrite X59. change (2 ^ 5) with 32. split; [lia|]. split; [exact Fal | lia].
    + rewrite X50. change (2 ^ 0) with 1. split; [unfold SHADOW_OFF in *; lia|].
      split; [apply Z.mod_1_r | lia].
    + rewrite X41. change (2 ^ 5) with 32. split; [lia|]. split; [exact HS1m32 | lia]. }
assert (SHOK1 : sh_ok SEGS (SLit 0) [] E1 (mrestrict (w_H W) mem)) by (unfold sh_ok; apply Forall_nil).
(* the runner and the release over the journal's relation R := wle' SEGS RZ_cf (YC1fPx's R runner: R and its two
   laws; the flag store's R form: R alone, its steps use no law of R) *)
pose (RUN := @paj_run_x_invR fxk rc SK _ PL_cno_A PA B prh_pst ARcfx _ LAWS P PLAW (wle' SEGS RZ_cf)
  (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)).
pose (RET := @paj_ret_at fxk rc _ PL_cno_A PA).
pose (FLAG := @paj_flag_store_x_invR fxk rc SK _ PL_cno_A PA B prh_pst ARcfx _ LAWS
  (astack_free_x_xs SEGS B) (frame_flag_x_xs SEGS B) (stack_free_x_any SEGS ARcfx) P PLAW (wle' SEGS RZ_cf)).
unfold cn_cfg, cn_pc, w64.
replace (BASE + CN_OFF + CN_END) with (BASE + (CN_OFF + CN_END)) by lia.
paj_run_tok_x_invR RUN HS1 HJ SHOK1 HPM (2 ^ 63, 2 ^ 63).
{ (* the writes: F's shadow and F's own first word *)
  intros a (rg & Hrg & Ha). cbn [cn_ss1 ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[]]]];
    cbn [cn_rg_sh cn_rg_F cn_rg_s1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?X50, ?X59, ?X41 in Ha.
  - right; right; right. exists CN_CID, fp. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFa, HF512. change (512 / 8) with 64. lia.
  - right; right; right. exists CN_CID, fp. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFa, HF512. lia.
  - exfalso. lia. }
(* ---- the state at the call ---- *)
pose proof (st_ok_restrict_mkst SEGS (w_H W) _ _ _ HS1 ltac:(vm_compute; reflexivity)) as Ems.
cbn [ss_pc setpc] in Ems. rewrite Ems.
prreg HS1 (1%bv : bv 5) R1. prreg HS1 (2%bv : bv 5) R2. prreg HS1 (3%bv : bv 5) R3.
prreg HS1 (4%bv : bv 5) R4. prreg HS1 (8%bv : bv 5) R8. prreg HS1 (10%bv : bv 5) R10.
prreg HS1 (11%bv : bv 5) R11. prreg HS1 (19%bv : bv 5) R19. prreg HS1 (21%bv : bv 5) R21.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (cn_F D <= a < cn_F D + 8) ->
  ~ (shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64) ->
  aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ intros a Ha H1a H2a. apply aview_eq_of. apply HFr. rewrite unsigned_lit_small by lia.
  intros (rg & Hrg & Hr). cbn [cn_ss1 ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[]]]];
    cbn [cn_rg_sh cn_rg_F cn_rg_s1 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?X50, ?X59, ?X41 in Hr; lia. }
(* ---- STAGE 2: the call (the rule keeps the world and concludes plain SRr, lifted into SRr' by SRr_SRr') ---- *)
eapply SRr'_bind.
{ apply (SRr_SRr' SEGS RZ_cf).
  eapply (@YGcallMxmn.aj_set_shadow_at_xmR fxk rc SK SEGS B prh_pst ARcfx _ LAWS pa_segs_low ENV (wle' SEGS RZ_cf)
    (wle'_refl SEGS RZ_cf) (wle'_trans SEGS RZ_cf)
    (SIGMA AS___asan_set_shadow_f5) 245 (SS5M fxk) W (ms_regs ms) (ms_mem ms) STK (cn_sp0 D) []
    (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) [(CN_CID, fp)] ly S Hp _ k CN_CID fp
    (shadow_addr (cn_F D)) 64 (cn_S1 D - cn_sp0 D) _).
  - exact HJ.
  - left. reflexivity.
  - rewrite R10. unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia).
    cbn [Nat.sub nth cn_cur map all_regs]. exact Rs2.
  - rewrite R11. reflexivity.
  - lia.
  - rewrite EFa. lia.
  - rewrite EFa, HF512. change (512 / 8) with 64. lia.
  - unfold spZ. rewrite R2. unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia).
    cbn [Nat.sub nth cn_cur map all_regs]. rewrite Rsp. unfold w64.
    rewrite unsigned_lit_small by lia. lia.
  - rewrite Zminus_mod, HS1m16, Hsp016. reflexivity.
  - lia.
  - rewrite HESv, HSTKv. lia.
  - rewrite R3. unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia).
    cbn [Nat.sub nth cn_cur map all_regs]. rewrite Hgp. exact Hgp0.
  - rewrite R4. unfold E1. rewrite cn_ew_hi by (unfold A_TEXT; lia).
    cbn [Nat.sub nth cn_cur map all_regs]. rewrite Htp. exact Htp0.
  - reflexivity.
  - rewrite R1. rewrite <- cn_off_ss5r.
    apply (ret_ok_codeptr_v (CN_OFF + CN_SS5R)); [rewrite cn_off_ss5r; split; [lia | vm_compute; reflexivity]
                                                 | rewrite cn_off_ss5r; reflexivity]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HPR2 & Hshv & Hfr2 & Hkeep2).
assert (HPM2 : P mem2) by exact (PCALL (ms_mem ms) mem2 Hkeep2 HPM).
pose proof (ajxR_ar HJ2) as HAR2.
(* ---- the registers the callee kept ---- *)
assert (K3a : getr regs2 3 = getr (ms_regs ms) 3) by exact (HPR2 3 ltac:(unfold acallee_saved; lia)).
assert (K4a : getr regs2 4 = getr (ms_regs ms) 4) by exact (HPR2 4 ltac:(unfold acallee_saved; lia)).
assert (K8a : getr regs2 8 = getr (ms_regs ms) 8) by exact (HPR2 8 ltac:(unfold acallee_saved; lia)).
assert (K19a : getr regs2 19 = getr (ms_regs ms) 19) by exact (HPR2 19 ltac:(unfold acallee_saved; lia)).
assert (K21a : getr regs2 21 = getr (ms_regs ms) 21) by exact (HPR2 21 ltac:(unfold acallee_saved; lia)).
assert (G3 : getr regs2 3 = getr (ci_regs D) 3).
{ rewrite K3a, R3. unfold E1.
  rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs]. exact Hgp. }
assert (G4 : getr regs2 4 = getr (ci_regs D) 4).
{ rewrite K4a, R4. unfold E1.
  rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs]. exact Htp. }
assert (G8 : getr regs2 8 = getr (ci_regs D) 2).
{ rewrite K8a, R8. unfold E1.
  rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs]. rewrite Rs0.
  unfold w64, cn_sp0, spZ. apply Z_to_bv_bv_unsigned. }
assert (G19 : getr regs2 19 = w64 (cn_F D)).
{ rewrite K19a, R19. unfold E1.
  rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs]. exact Rs11. }
assert (G21 : getr regs2 21 = w64 r).
{ rewrite K21a, R21. unfold E1.
  rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs]. exact Rs5. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (cn_F D <= a < cn_F D + 8) ->
  ~ (shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64) ->
  aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem a).
{ intros a Ha H1a H2a. rewrite (Hfr2 a Ha ltac:(lia)). apply K1; [lia | lia | lia]. }
(* ---- STAGE 3: the release, the epilogue and the `ret` ---- *)
set (E3 := Eimg (Ereg (ci_regs D) (cn_cur regs2 ++ [w64 fl]))).
assert (HEI3 : img_env VAL A_LIM E3) by (unfold E3; apply Eimg_env).
assert (Y51 : bv_unsigned (ew E3 51) = cn_F D).
{ unfold E3. rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs app].
  rewrite G19. unfold w64. apply unsigned_lit_small. lia. }
assert (Y64 : ew E3 64 = w64 fl).
{ unfold E3. rewrite cn_ew_hi by (unfold A_TEXT; lia). cbn [Nat.sub nth cn_cur map all_regs app]. reflexivity. }
assert (Y64u : bv_unsigned (ew E3 64) = fl) by (rewrite Y64; unfold w64; apply unsigned_lit_small; lia).
assert (Y2 : bv_unsigned (ew E3 2) = cn_sp0 D)
  by (unfold E3; rewrite (cn_ew_lo _ _ 2 2 eq_refl); reflexivity).
assert (YE : forall (n : nat) (rn : bv 5), Z.of_nat n = bv_unsigned rn -> ew E3 n = getr (ci_regs D) rn)
  by (intros n rn Hn; unfold E3; apply (cn_ew_lo _ _ n rn Hn)).
assert (HFFw : rdword (aview SEGS (w_H W) mem2) (cn_F D + 504) = Some fl).
{ rewrite (rdword_ext (aview SEGS (w_H W) mem) (aview SEGS (w_H W) mem2) (cn_F D + 504)).
  - replace (cn_F D + 504) with (cn_F D + fs_frame_bytes CN_CID - 8) by (rewrite HF512; lia). exact Hflagw.
  - intros j Hj. apply K2; [lia | lia | unfold shadow_addr, SHADOW_OFF in *; lia]. }
(* the 13 saved words, and the keep that carries them to the memory the call left *)
assert (SVk : forall a, cn_sp0 D - 104 <= a -> a + 8 <= cn_sp0 D ->
  rdword (aview SEGS (w_H W) mem2) a = rdword (aview SEGS (w_H W) mem) a).
{ intros a Ha1 Ha2. apply rdword_ext. intros j Hj. apply K2; [lia | lia | unfold SHADOW_OFF in *; lia]. }
unfold cn_saved in HSV.
pose proof (Forall_inv HSV) as SA1. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA2. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA3. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA4. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA5. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA6. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA7. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA8. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA9. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA10. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA11. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA12. apply Forall_inv_tail in HSV.
pose proof (Forall_inv HSV) as SA13. clear HSV.
cbn [fst snd] in SA1, SA2, SA3, SA4, SA5, SA6, SA7, SA8, SA9, SA10, SA11, SA12, SA13.
assert (HS3 : st_ok_pi SEGS VAL E3 cn_ss3
  (restrict (w_H W) (@YK11.mkst fxk regs2 (Z_to_bv 64 (BASE + (CN_OFF + CN_SS5R))) mem2 (YK11.seg_rom SEGS)))).
{ unfold cn_ss3. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - apply (cn_regs_ok_3 (ci_regs D) regs2 (w64 fl) G3 G4 G8).
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; [..|apply Forall_nil];
      unfold region_ok, cn_rg_ff, cn_rg_fl, cn_rg_fr;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite Y51. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E3 _ _ 504 8 (SOff 64 0) fl).
      * cbn [sv_denot]. rewrite Y64u, Z.add_0_r. reflexivity.
      * change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      * cbn. lia.
      * exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ HFFw).
    + rewrite Y64u. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace (fl + o) with fl by lia.
      exact (proj1 (alc_flag SEGS B (AR_laws_ok_cf SEGS B) ly S Hp W mem2 md2 CN_CID fp (proj1 HAR2) Hin)).
    + rewrite Y2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; [..|apply Forall_nil].
      { cn_frch YE SVk 1%nat (1%bv : bv 5) (-8) 184 SA1. }
      { cn_frch YE SVk 8%nat (8%bv : bv 5) (-16) 176 SA2. }
      { cn_frch YE SVk 9%nat (9%bv : bv 5) (-24) 168 SA3. }
      { cn_frch YE SVk 18%nat (18%bv : bv 5) (-32) 160 SA4. }
      { cn_frch YE SVk 19%nat (19%bv : bv 5) (-40) 152 SA5. }
      { cn_frch YE SVk 20%nat (20%bv : bv 5) (-48) 144 SA6. }
      { cn_frch YE SVk 21%nat (21%bv : bv 5) (-56) 136 SA7. }
      { cn_frch YE SVk 22%nat (22%bv : bv 5) (-64) 128 SA8. }
      { cn_frch YE SVk 23%nat (23%bv : bv 5) (-72) 120 SA9. }
      { cn_frch YE SVk 24%nat (24%bv : bv 5) (-80) 112 SA10. }
      { cn_frch YE SVk 25%nat (25%bv : bv 5) (-88) 104 SA11. }
      { cn_frch YE SVk 26%nat (26%bv : bv 5) (-96) 96 SA12. }
      { cn_frch YE SVk 27%nat (27%bv : bv 5) (-104) 88 SA13. }
  - apply pairwise_disjoint_of_extents.
    unfold cn_rg_ff, cn_rg_fl, cn_rg_fr, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Y51, Y64u, Y2.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [cn_facts3 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    split; [|split; [|split; [|exact I]]].
    + rewrite Y51. change (2 ^ 5) with 32. split; [lia|]. split; [exact Fal | lia].
    + rewrite Y64u. change (2 ^ 0) with 1. split; [lia|]. split; [apply Z.mod_1_r | lia].
    + rewrite Y2. change (2 ^ 4) with 16. split; [lia|]. split; [exact Hsp016 | lia]. }
assert (SHOK3 : sh_ok SEGS (SLit 0) [] E3 (mrestrict (w_H W) mem2)) by (unfold sh_ok; apply Forall_nil).
rewrite R1, <- cn_off_ss5r.
eapply (FLAG W FUEL E3 cn_K3 (SLit 0) (2 ^ 63, 2 ^ 63) [] cn_ss3 cn_st3 cn_r3 _ STK (cn_sp0 D) []
  (ci_ly D) (set_depot (st_depot S) (ci_S D)) (ci_Hp D) (ci_W D) (ci_mem D) (ci_md D) [] ly S Hp md2 k CN_CID fp _
  cn_K3_lim HEI3 ltac:(unfold CN_CID; lia) HS3 SHOK3 cn_static3 cn_run3_eq cn_r3_not_call HJ2 HPM2).
- (* no obligation *)
  rewrite cn_obls3. apply Forall_nil.
- (* the one write: the flag byte *)
  intros a (rg & Hrg & Ha). cbn [cn_ss3 ss_mem In] in Hrg.
  destruct Hrg as [<-|[<-|[<-|[]]]];
    cbn [cn_rg_ff cn_rg_fl cn_rg_fr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    rewrite ?Y51, ?Y64u, ?Y2 in Ha.
  + exfalso. lia.
  + right. lia.
  + exfalso. lia.
- (* the flag byte is 0 after the run *)
  intros ws3 msr Hlen3 HSr.
  pose proof (st_ok_mem_ok SEGS _ _ _ HSr) as (_ & HRS3 & _).
  cbn [abs_ss setpc ss_mem] in HRS3. rewrite cn_mem3_eq in HRS3. unfold cn_mem3 in HRS3.
  apply Forall_cons_iff in HRS3 as (_ & HRS3). apply Forall_cons_iff in HRS3 as (HRfl & _).
  destruct HRfl as (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
  pose proof (Forall_inv HC) as HC0.
  assert (Y64x : bv_unsigned (ew (extK E3 cn_K3 ws3) 64) = fl).
  { rewrite (proj1 (env_agree_extK E3 cn_K3 ws3) 64%nat ltac:(unfold cn_K3; cbv; lia)). exact Y64u. }
  rewrite Y64x in HC0.
  pose proof (val_of_chunk_ok SEGS (extK E3 cn_K3 ws3) (ms_mem msr) fl 0 1%N (SLit 0) 0 HC0
    ltac:(cbn; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  pose proof (HV 0%nat ltac:(cbn; lia)) as HV0. cbn [Z.of_nat] in HV0. rewrite !Z.add_0_r in HV0.
  exact HV0.
- (* ---- after the release: the epilogue has run, the `ret` is next ---- *)
  intros ws3 ms3 mat3 Hlen3 HEI3' HS3' SHOK3' HJ3 HPM3 HF1 HF2 HG2.
  assert (Ews : ws3 = []) by (destruct ws3; [reflexivity | rewrite cn_j3 in Hlen3; cbn in Hlen3; discriminate]).
  subst ws3. cbn [extK] in HS3', HEI3', SHOK3', HF1, HF2, HG2.
  cbn [ms_mem YK11.mkst] in HF1, HF2, HG2.
  (* the run wrote only the flag byte *)
  assert (K3 : forall a, 0 <= a < 2 ^ 64 -> a <> fl ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem2 a).
  { intros a Ha Hne. apply aview_eq_of. apply HF2. rewrite unsigned_lit_small by lia.
    intros (rg & Hrg & Hr). cbn [cn_ss3 ss_mem In] in Hrg.
    destruct Hrg as [<-|[<-|[<-|[]]]];
      cbn [cn_rg_ff cn_rg_fl cn_rg_fr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?Y51, ?Y64u, ?Y2 in Hr; lia. }
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (cn_F D <= a < cn_F D + 8) ->
    ~ (shadow_addr (cn_F D) <= a < shadow_addr (cn_F D) + 64) -> a <> fl ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a)
    by (intros a Ha H1a H2a H3a; rewrite (K3 a Ha H3a); apply K2; assumption).
  (* a live block's bytes are kept, from the current state and from the entry *)
  assert (BLK2 : forall b m a, In (b, m) (ablocks B ly S) -> b <= a < b + req_size m ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
  { intros b m a Hbm Ha.
    destruct (alx_blocks SEGS B ARcfx LAWS ly S Hp W mem md b m HARc Hbm)
      as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpres & _).
    pose proof (sep_block_frame_x SEGS B ARcfx LAWS ly S Hp W mem md b m CN_CID fp HARc Hbm Hin) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa, HF512 in Hd.
    apply KALL.
    - unfold in_app in Hbapp. unfold ASAN_CEIL in Hbapp. lia.
    - lia.
    - unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp. unfold SHADOW_OFF in *. lia.
    - intros Ea. subst a. exact (proj2 (Hbpres fl ltac:(lia)) Fown). }
  assert (BLK0 : forall b m a, In (b, m) (ablocks B (ci_ly D) (ci_S D)) -> b <= a < b + req_size m ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
  { intros b m a Hbm Ha.
    assert (Hbmc : In (b, m) (ablocks B ly S))
      by (apply (Permutation_in _ (Permutation_sym HPB)); exact Hbm).
    rewrite (BLK2 b m a Hbmc Ha).
    replace a with (b + (a - b)) by lia.
    apply (Jblk b m (a - b) Hbm Hbmc ltac:(lia)). intros Hfp'. exact (inFP_nil _ Hfp'). }
  (* a read-only image byte is kept *)
  assert (IMGK : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a ->
    ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H (ci_W D)) (ci_mem D) a).
  { intros a Hro Hown Herr.
    assert (Hima : in_img SEGS a) by (apply cn_ro_img; exact Hro).
    pose proof (pa_segs_low a Hima) as Hlowa.
    assert (Hpst : ~ Exists (in_zr a) prh_pst) by (intros Hx; exact (cni_pst_rw B IMG a Hx Hro)).
    rewrite KALL.
    - apply (Jimg a Hima Hown Herr Hpst). apply fp_spares_closed. intros (rg & Hrg & _). destruct Hrg.
    - unfold kLowMemEnd in Hlowa. lia.
    - intros Hx. exact (frm_img_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID fp a HARc Hin
        ltac:(rewrite EFa, HF512; lia) Hima).
    - unfold kLowMemEnd, SHADOW_OFF in *. lia.
    - intros Ea. subst a. exact (Fimg Hima). }
  (* the statics and the ledger's head words are kept from the current state *)
  assert (PSTK : forall a, Exists (in_zr a) prh_pst ->
    aview SEGS (w_H W) (ms_mem ms3) a = aview SEGS (w_H W) mem a).
  { intros a Ha. destruct (cni_pst_ok B IMG a Ha) as (Hima & _).
    pose proof (pa_segs_low a Hima) as Hlowa.
    apply KALL.
    - unfold kLowMemEnd in Hlowa. lia.
    - intros Hx. exact (frm_img_x SEGS B ARcfx LAWS ly S Hp W mem md CN_CID fp a HARc Hin
        ltac:(rewrite EFa, HF512; lia) Hima).
    - unfold kLowMemEnd, SHADOW_OFF in *. lia.
    - intros Ea. subst a. exact (Fimg Hima). }
  assert (HEADK : forall a kk i, In (a, kk) Lam -> 0 <= i < 8 ->
    aview SEGS (w_H W) (ms_mem ms3) (a - cf_head + i) = aview SEGS (w_H W) mem (a - cf_head + i)).
  { intros a kk i Hin' Hi.
    pose proof (S1Ledger.prh_ledger_hblock B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran a kk (ci_most D) ownl HLED Hin')
      as (Hk0' & Hab & _).
    apply (BLK2 (a - cf_head) (kk + cf_head)); [exact Hab|].
    unfold req_size. destruct (Z.eqb_spec (kk + cf_head) 0) as [Ez|Ez]; unfold prh_head_wide in HW; lia. }
  (* the own cell the post reports: the cut's ledger at ownl (g_own_ran_out is 0 or 1) *)
  pose proof (PRH_Base.prh_ledger_own B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (ci_most D) ownl HLED)
    as (_ & HOWN01).
  (* the state the post reports *)
  assert (EAB : ablocks B ly (stack_free_state CN_CID fp S) = ablocks B ly S)
    by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
  assert (HLED3 : prh_ledger B ly (stack_free_state CN_CID fp S) Hp W (ms_mem ms3) Lam peak cnt SIZE_MAXZ ran
    (ci_most D) ownl).
  { apply (S1Ledger.prh_ledger_kept_aview B ly S Hp W mem); [exact HLED | exact PSTK | exact HEADK | | apply Permutation_refl].
    intros a kk Hin' Hab. rewrite EAB. exact Hab. }
  (* the data the reader was given is still there *)
  assert (HBY : bytes_at W (ms_mem ms3) (ci_data D) (ci_x D)).
  { unfold bytes_at. intros j Hj.
    assert (Hsz : 0 < cn_size D) by (unfold cn_size; lia).
    pose proof HSRC as (HG0 & Hd4096 & Hdceil & Hdmr & Hdra & Hdhull).
    destruct (HG0 j Hj) as (HVj & Hbj). split; [|exact Hbj].
    intros kq Hkq. cbn in Hkq. assert (Ekq : kq = 0%nat) by lia. subst kq.
    rewrite (cn_mbyte_of_aview (ci_W D) W (ci_mem D) (ms_mem ms3) (ci_data D + Z.of_nat j + Z.of_nat 0)).
    - exact (HVj 0%nat ltac:(cbn; lia)).
    - replace (ci_data D + Z.of_nat j + Z.of_nat 0) with (ci_data D + Z.of_nat j) by (cbn; lia).
      destruct (HHOME Hsz) as [HK | (b & m & Hbm & Hnb & Hb1 & Hb2)].
      + destruct HK as [(b & m & Hbm & Hb1 & Hb2) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]].
        * pose proof (S1Ledger.prh_ledger_hblock B (ci_ly D) (ci_S D) (ci_Hp D) (ci_W D) (ci_mem D)
            (ci_Lam D) (ci_peak D) (ci_cnt D) SIZE_MAXZ (ci_ran D) b m (ci_most D) 0 HLED0 Hbm) as (Hm0 & Hab & _).
          apply (BLK0 (b - cf_head) (m + cf_head)); [exact Hab|].
          unfold req_size. destruct (Z.eqb_spec (m + cf_head) 0); unfold cn_size in *; lia.
        * destruct (Hro (ci_data D + Z.of_nat j) ltac:(unfold cn_size in *; lia)) as (H1 & H2 & H3).
          exact (IMGK _ H1 H2 H3).
        * destruct (Hro (ci_data D + Z.of_nat j) ltac:(unfold cn_size in *; lia)) as (H1 & H2 & H3 & _).
          exact (IMGK _ H1 H2 H3).
      + apply (BLK0 b m); [exact Hbm|].
        unfold req_size. destruct (Z.eqb_spec m 0); unfold cn_size in *; lia. }
  (* ---- the `ret` ---- *)
  prreg HS3' (1%bv : bv 5) Q1. prreg HS3' (10%bv : bv 5) Q10.
  assert (Q1e : getr (ms_regs ms3) 1 = getr (ci_regs D) 1)
    by (rewrite Q1; unfold E3; apply (cn_ew_lo _ _ 1 1 eq_refl)).
  assert (Q10e : getr (ms_regs ms3) 10 = w64 r).
  { rewrite Q10. unfold E3. rewrite cn_ew_hi by (unfold A_TEXT; lia).
    cbn [Nat.sub nth cn_cur map all_regs app]. exact G21. }
  assert (HAE3 : env_agree 32 (Ereg (ci_regs D) (cn_cur regs2 ++ [w64 fl])) E3).
  { split; [intros n Hn; unfold E3; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
  (* the release's continuation is at R; the `ret` keeps the world, so the plain rule lifts by SRr_SRrG *)
  apply (SRr_SRrG SEGS (wle' SEGS RZ_cf) (wle_wle' SEGS RZ_cf)).
  eapply (RET W E3 (sh_ss cn_st3) ms3 _ _ HS3' ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
  intros mat4. rewrite Q1e.
  unfold YK0s.ret_ok in Hra0. rewrite Hra0.
  split.
  + (* The kit's fpostFb is at the walk's relation: YCbqGwild.apost_base_xbFR .. (wle' SEGS RZ_cf) *)
    unfold cn_ex_ret, fpostFb, YCbqGwild.apost_base_xbFR.
    exists fxk, ly, (stack_free_state CN_CID fp S), Hp, (ms_regs ms3), (ms_mem ms3). eexists. exists k, WS.
    split; [reflexivity|].
    split; [exact Hfrm|].
    split; [exact Hfk|].
    (* the post's budget is the cut's own WS: wbudget [] 6 (prh_wk F_check_no_overread = 6) *)
    split; [exact HWB|].
    (* the epilogue's journal, from the rebased entry, back at the entry with the budget WS *)
    split.
    { apply (YCbqGwild.ajournal_xw_unbase0R (SK := SK) SEGS B prh_pst ARcfx (wle' SEGS RZ_cf) _ _ _ _ _ (ci_Hp D)
        _ _ _ _ _ _ _ _ _ _ _ (st_depot S) WS).
      - apply (ajournal_x_materializeR SEGS B prh_pst ARcfx LAWS pa_segs_low (wle' SEGS RZ_cf)). exact HJ3.
      - exact (ajxR_wild HJW). }
    split.
    { exact (aregs_preserved_of_st_ok SEGS _ _ _ _ (ci_regs D) (cn_cur regs2 ++ [w64 fl]) HS3' HAE3
        ltac:(vm_compute; reflexivity)). }
    unfold cn_Q.
    split; [exact (RL_stack_free S CN_CID fp HRL)|].
    exists Lam, peak, cnt, ran, ownl.
    split; [exact HPL|].
    split; [rewrite EAB; exact HPB|].
    split; [exact HPK|].
    split; [exact HCNT|].
    split; [exact HLED3|].
    split; [exact HBY|].
    exists r. split; [exact Q10e|].
    split.
    { destruct HRES as [(Hr1 & Ho1) | (Hr0 & Ho0 & Hran0)].
      - left. split; [exact Hr1|].
        destruct Ho1 as [Hne | Hran1]; [left; destruct HOWN01 as [Eo0 | Eo1]; [contradiction | exact Eo1] | right; exact Hran1].
      - right. exact (conj Hr0 (conj Ho0 Hran0)). }
    (* CNO-COPY: at a consumer run whose next events are the three copies, own' = ownl = 0; a refused copy
       (ownl <> 0) is dead there by the cut's cn_cdead *)
    split.
    { intros sm x0 os i H0 hist Hrp Hrun Hcons.
      destruct (Z.eq_dec ownl 0) as [Eo | Eo]; [exact Eo|].
      destruct (HCD Eo sm x0 os i H0 hist Hrp Hrun Hcons). }
    (* under own' = ownl = 0: the cut's grants, the events = ck_cno_evs, r = ran = cn_ranz *)
    intros Eo0. destruct (HEVS Eo0) as (o1 & o2 & o0 & HPG & Eran).
    unfold cn_prog in HPG. destruct HPG as (HLV & HPOS).
    rewrite cn_ck_cno_evs in HLV, HPOS.
    exists o1, o2, o0.
    split.
    { transitivity ran; [|exact Eran].
      destruct HRES as [(Hr1 & [Hne | Hran1]) | (Hr0 & _ & Hran0)];
        [contradiction | rewrite Hr1, Hran1; reflexivity | rewrite Hr0, Hran0; reflexivity]. }
    split; [exact HLV|].
    intros sm x0 os i H0 hist Hrp Hrun.
    destruct (HPOS sm x0 os i H0 hist Hrp Hrun) as (hist' & Hrp').
    exists hist'. exact (PresetRoomPosKeep.room_pos_stack_free _ _ _ _ _ _ _ CN_CID fp Hrp').
  + exact HPM3.
Qed.

End cfe.

Print Assumptions cn_seg_end.
