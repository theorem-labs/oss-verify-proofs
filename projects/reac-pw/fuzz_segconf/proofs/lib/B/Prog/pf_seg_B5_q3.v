(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 224 of its 281 lines of code are new or changed and 4996 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B5 of reac_segconf_parse_file,
   the piece Q3 -> R3 of lib/B/Prog/pf_seg_B5_d.v (the B5 segment lane of the image-B G3 walk owner, piece prover: a sub-lane, 2026-10-30).
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-B walk; the function's rule-24 record
   is the rule-24 lookup record).
   ADAPTED from the image-A G3 walk owner's image-A piece lib/A/Prog/pf_a5_r3.v a5_q3_ok (commit 003b9dc874eb)
   and the unit owner's UBSan piece lib/U/Prog/pf_p2.v (the lineno++ check), re-derived on image B's code: B's lineno is
   s8 -> s6 (A: s10), the increment carries the UBSan trap T05, and B loads meta_fill_00's first argument from the
   spill slot 0xd8 (A: s3 = SH + 8), so the seed carries a read-only region on s1 (x9) whose chunk at 0xd8 is
   s5 (x21) + 8 = SH + 8 (PF_SL's 0xd8).
   The code (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s), 5 of its 6 instructions walked (0x88240, the
   trap's jump, excluded):
     Q3 0x88238 addiw s6,s8,1        s6 = lineno + 1 (32-bit add, sign-extended)
        0x8823c bge s6,s8,0x88244    UBSan trap T05 (signed overflow of `lineno++`, reac_segconf.c:136): not taken
                                     only when ln + 1 < ln as 32-bit signed values; refuted: 0 <= ln <= o <=
                                     length s <= 65535 (pfA_facts.pf_lctx_ln, pf_tf / b5_text), so the increment
                                     does not wrap
        0x88240 j 0x891c8            the trap's jump to the `unimp` (never reached)
        0x88244 li a1,64
        0x88248 ld a0,216(s1)        slot 0xd8 = SH + 8 (PF_SL, 0x87f48)
        0x8824c jal meta_fill_00     __asan_set_shadow_00 on buf's 64 shadow cells (call C7): buf in scope;
                                     returns to 0x88250 = R3.
   The proof: a seed at Q3 (every register its own atom, the slot read-only on s1's atom), a run of the plain
   executor to the trap branch, the branch split (the not-taken side refuted), a run to the call, the call by
   pf_seg_B5_sh.v aj_set_shadow_atS (v = 0, q = SH + 8, n = 64, the frame (5, pos) the journal owns), INV_R3 rebuilt
   with the kit's b5_move, b5_keep_fsh (b = true: PF_SC_LINE) and b5_keep_st. The one Section hypothesis is
   ASH00. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YK1g YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtShadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
  SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
  PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB
  pf_pieces pf_seg_B5_d pf_seg_B5_sh pf_seg_B5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small facts and tactics (pf_a5_r3.v's, with B's register lists) ---------- *)
Lemma b5q3_bvr : forall (rr : bvmap 5 word) (r : bv 5) k v, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = v -> getr rr r = v.
Proof. intros rr r k v Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma b5q3_dec : forall x lo hi, (lo <= x < hi) \/ ~ (lo <= x < hi).
Proof.
intros x lo hi. destruct (Z_lt_le_dec x lo) as [H1 | H1]; [right; lia|].
destruct (Z_lt_le_dec x hi) as [H2 | H2]; [left; lia | right; lia].
Qed.
(* b5_text's 65535%nat is an abstract numeral that zify cannot read: its Z form *)
Lemma b5q3_le65535 : forall k : nat, (k <= 65535)%nat -> Z.of_nat k <= 65535.
Proof. intros k H. apply Nat2Z.inj_le in H. exact H. Qed.
(* 0x88238 addiw s6,s8,1 on a lineno that does not wrap *)
Lemma b5q3_addiw : forall x, 0 <= x -> x + 1 < 2 ^ 31 ->
  sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 x)) (low32 (Z_to_bv 64 1))) = Z_to_bv 64 (x + 1).
Proof.
intros x H0 H1. rewrite YK1g.aluw_addi_lit. apply bv_eq.
rewrite (v_addiw_small (Z_to_bv 64 x) 1); rewrite ?unsigned_lit_small; lia.
Qed.
(* the trap T05 (0x8823c `bge s6,s8` not taken): ln + 1 < ln as signed 64-bit values is false *)
Lemma b5q3_t05 : forall E a b x, sv_denot E a = Z_to_bv 64 (x + 1) -> sv_denot E b = Z_to_bv 64 x ->
  0 <= x -> x + 1 < 2 ^ 63 -> branch_taken BC_GE (sv_denot E a) (sv_denot E b) = false -> False.
Proof.
intros E a b x Ha Hb H0 H1 Hc. rewrite Ha, Hb, YO0c.branch_ge, !unsigned_lit_small in Hc by lia.
rewrite !YO0b.s64_small in Hc by lia. apply Bool.negb_false_iff, Z.ltb_lt in Hc. lia.
Qed.
Ltac b5q3_in := unfold PF_RL, PF_RM, b5_FI; cbn [In app]; repeat first [left; reflexivity | right].
Ltac b5q3_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* a register the run left as an atom of the seed: its value is the seed register's, from the cut's list R *)
Ltac b5q3_atom HS EE R :=
  lazymatch type of R with pf_rg ?rx _ =>
    b5q3_rreg HS; rewrite b5_den_atom0;
    lazymatch goal with |- ew _ ?nn = _ =>
      let k := eval vm_compute in (Z.of_nat nn) in
      transitivity (getr rx (Z_to_bv 5 k)); [apply EE; reflexivity | apply (b5_rg _ _ k _ R); b5q3_in] end end.
Ltac b5q3_atoms := repeat (apply Forall_cons; [split; [cbn [fst]; lia | cbn [fst]; vm_compute; reflexivity] |]); apply Forall_nil.
Ltac b5q3_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Ltac b5q3_awr := lazymatch goal with |- awr_ok ?sg ?Bx ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bx Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* a run whose regions write nothing keeps every byte *)
Ltac b5q3_kept HFr :=
  lazymatch type of HFr with frame_of ?Ex ?rs (mrestrict ?Hh ?m0) (mrestrict _ ?m1) =>
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    lazymatch goal with |- aview ?sg _ _ _ = _ =>
    apply (kept_of_frame (segs := sg) Ex rs Hh m0 m1 (fun _ => False) HFr); [|exact Ha | tauto] end;
    let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
    let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
    intros b wlo whi a' Hin Hrr; vm_compute in Hin;
    repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
    destruct Hin end.

(* the seed at Q3 (0x88238): every register its own atom; slot 0xd8 read-only on s1's atom (x9), its chunk
   s5 + 8 = SH + 8 (x21 = SH, PF_RL) *)
Definition b5q3_ss : sstate := mkSS B5_Q3 sr_atoms
  [YP09.mkRegion (Some 9%nat) 0xd8 0xe0 0xd8 0xd8 [YP09.mkChunk 0xd8 (CVal 8 (SOff 21 8))]] None (mkFacts [] [] []).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the registers a run left as their own atoms keep the values they had *)
Lemma b5q3_rg_keep : forall E ss ms (H : word -> bool) (rX : bvmap 5 word) L,
  st_ok SEGS E ss (restrict H ms) ->
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r) ->
  Forall (fun rv => 0 <= fst rv < 32 /\ sr_get (ss_regs ss) (Z_to_bv 5 (fst rv)) = SOff (Z.to_nat (fst rv)) 0) L ->
  pf_rg rX L -> pf_rg (ms_regs ms) L.
Proof.
intros E ss ms H rX L HS EE HL HR. unfold pf_rg in *. rewrite Forall_forall in *. intros [r x] Hin.
destruct (HL _ Hin) as [Hr Hs]. cbn [fst snd] in *.
rewrite (st_ok_restrict_reg SEGS H E ss ms _ HS), Hs, b5_den_atom0.
rewrite (EE (Z.to_nat r) (Z_to_bv 5 r)); [exact (HR _ Hin)|].
rewrite Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; cbn; lia). reflexivity.
Qed.

Lemma b5q3_seed : forall v pos (Wc : world SEGS) (rX : bvmap 5 word) memc,
  getr rX (Z_to_bv 5 9) = w64 (pf_s1 v) -> 0 <= pf_s1 v -> pf_s1 v + 0xe0 <= 2 ^ 64 ->
  getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos) -> 0 <= pf_SH v pos -> pf_SH v pos + 8 < 2 ^ 64 ->
  rdword (rdW Wc memc) (pf_s1 v + 0xd8) = Some (pf_SH v pos + 8) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [])) b5q3_ss
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + B5_Q3)) memc (seg_rom SEGS))).
Proof.
intros v pos Wc rX memc R9 S0 S1 R21 H0 H1 HB8.
set (E := Eimg (Ereg rX [])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (E21 : ew E 21 = Z_to_bv 64 (pf_SH v pos)) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity).
rewrite restrict_mkst_fx. unfold b5q3_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (pf_s1 v) 0xd8 8 (SOff 21 8) (pf_SH v pos + 8)).
  + exact (b5_den_off E 21 (pf_SH v pos) 8 E21 ltac:(lia)).
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + change (Z.of_N 8) with 8. lia.
  + exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ HB8).
- cbn. tauto.
- split; [exact I | split; exact I].
Qed.

Section e.
Variable B : asyms.
Hypothesis ASH00 : forall fx0 : YK11.FPState, @aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_00) 0.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (fx := fx) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (fx := fx) B LAWS.
Let BR := paj_branch (PI := PI).

(* ======================= Q3 (0x88238): lineno++ (T05), buf into scope (meta_fill_00) ======================= *)
Lemma b5_q3_ok : forall n, H_R3 B n -> H_Q3 B n.
Proof.
intros n HR3 v pos lyc Sc Wc rX memc mdc cf cur nm o ln d HI.
pose proof HI as (HB & HLN & HRG).
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
destruct (b5_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (G & Hin & EF & Hfrs & HAR).
pose proof HFI as (HJ & Hly & _ & _ & _ & _ & _ & _ & _ & HRG0).
subst lyc.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11).
pose proof (b5_SHv v pos G) as (ESH & SH1 & SH2 & F8).
pose proof (b5_text B _ _ _ _ _ _ _ _ _ HB) as (_ & HLS & _ & _ & _ & HC).
pose proof HLN as (HCTX & Ho & Hk & HST).
pose proof (pf_lctx_ln _ _ _ _ HCTX) as (Hln & _).
pose proof (b5q3_le65535 _ HLS) as HLSZ.
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_lt as Hac.
assert (ES : ESTACK = 4096) by reflexivity.
assert (Hln31 : ln + 1 < 2 ^ 31) by lia.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (b5_rg rX _ 9 _ HRG0); b5q3_in).
assert (R21 : getr rX (Z_to_bv 5 21) = w64 (pf_SH v pos)) by (apply (b5_rg rX _ 21 _ HRG); b5q3_in).
assert (R24 : getr rX (Z_to_bv 5 24) = w64 ln) by (apply (b5_rg rX _ 24 _ HRG); b5q3_in).
assert (HB8 : rdword (rdW Wc memc) (pf_s1 v + 0xd8) = Some (pf_SH v pos + 8)).
{ unfold pf_sl in HSL. rewrite Forall_forall in HSL.
  exact (HSL (0xd8, pf_SH v pos + 8) ltac:(unfold PF_SL; cbn [In]; repeat first [left; reflexivity | right])). }
pose proof (b5q3_seed v pos Wc rX memc R9 ltac:(lia) ltac:(lia) R21 ltac:(lia) ltac:(lia) HB8) as HS.
set (E := Eimg (Ereg rX [])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n0 (r : bv 5), Z.of_nat n0 = bv_unsigned r -> ew E n0 = getr rX r)
  by (intros n0 r Hn0; subst E; apply ew_Eimg_Ereg_nat; exact Hn0).
assert (E21 : ew E 21 = Z_to_bv 64 (pf_SH v pos)) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; reflexivity).
assert (E24 : ew E 24 = Z_to_bv 64 ln) by (rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), R24; reflexivity).
unfold cfg_at. change (w64 (BASE + B5_Q3)) with (Z_to_bv 64 (BASE + B5_Q3)).
(* 0x88238 addiw s6,s8,1, up to the trap branch 0x8823c *)
paj_run_sh RUNP HS HJ.
{ b5q3_awr. }
cbn [ms_mem mkst] in HFr, HG, HF.
b5q3_clear_md.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a) by b5q3_kept HFr.
clear HFr HG HF.
psrr_branch_pi RUNP BR HS.
2: { (* not taken: the trap T05, refuted *)
  exfalso.
  lazymatch type of Hc with branch_taken BC_GE (sv_denot _ ?a) (sv_denot _ ?b) = false =>
    refine (b5q3_t05 E a b ln _ _ ltac:(lia) ltac:(lia) Hc) end.
  - transitivity (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 ln)) (low32 (Z_to_bv 64 1)))).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. reflexivity.
    + exact (b5q3_addiw ln ltac:(lia) Hln31).
  - rewrite b5_den_atom0. exact E24. }
(* taken: 0x88244 li a1,64; 0x88248 ld a0,216(s1); 0x8824c the call *)
clear Hc.
paj_run_shc RUNP RUNC HS HJ.
{ b5q3_awr. }
b5q3_clear_md.
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a) by b5q3_kept HFr.
assert (KR : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms0) a = rdW Wc memc a)
  by (intros a Ha; rewrite (K2 a Ha); exact (K1 a Ha)).
(* the registers at the call *)
assert (QFI : pf_rg (ms_regs ms0) (b5_FI B v)).
{ apply (b5q3_rg_keep E _ ms0 (w_H Wc) rX _ HS EE); [unfold b5_FI; b5q3_atoms | exact HRG0]. }
assert (Q2 : getr (ms_regs ms0) (Z_to_bv 5 2) = w64 (pf_s1 v)) by (apply (b5_rg _ _ 2 _ QFI); b5q3_in).
assert (Q3 : getr (ms_regs ms0) (Z_to_bv 5 3) = w64 (as_gp B)) by (apply (b5_rg _ _ 3 _ QFI); b5q3_in).
assert (Q4 : getr (ms_regs ms0) (Z_to_bv 5 4) = w64 (as_tp B)) by (apply (b5_rg _ _ 4 _ QFI); b5q3_in).
assert (Q1 : getr (ms_regs ms0) (Z_to_bv 5 1) = Z_to_bv 64 (BASE + B5_R3)).
{ b5q3_rreg HS. rewrite (codeptr_val _ _ HEI). reflexivity. }
assert (Q10 : getr (ms_regs ms0) (Z_to_bv 5 10) = w64 (pf_SH v pos + 8)).
{ b5q3_rreg HS. rewrite (b5_den_off E 21 (pf_SH v pos) 8 E21) by lia. reflexivity. }
assert (Q11 : getr (ms_regs ms0) (Z_to_bv 5 11) = w64 64) by (b5q3_rreg HS; reflexivity).
assert (Q22 : getr (ms_regs ms0) (Z_to_bv 5 22) = w64 (ln + 1)).
{ b5q3_rreg HS. transitivity (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 ln)) (low32 (Z_to_bv 64 1)))).
  - cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E24. reflexivity.
  - exact (b5q3_addiw ln ltac:(lia) Hln31). }
assert (QL : pf_rg (ms_regs ms0) (PF_RL v pos ++ PF_RM v o ln ++
    [(27, p_t v + Z.of_nat o); (23, Z.of_nat (b5_len v o))])).
{ unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [exact Q22 | b5q3_atom HS EE HRG]. }
assert (Hsp : spZ (ms_regs ms0) = pf_sp0 v + (pf_s1 v - pf_sp0 v)).
{ unfold spZ. rewrite (b5q3_bvr (ms_regs ms0) 2%bv 2 _ eq_refl Q2). unfold w64. rewrite unsigned_lit_small by lia. lia. }
pmkst HS.
eapply SRr_bind.
{ apply (aj_set_shadow_atS SEGS B LAWS pa_segs_low (SIG SS___asan_set_shadow_00) 0 (ASH00 fx) Wc
    (ms_regs ms0) (ms_mem ms0) STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v)
    (p_W v) (p_mem v) (p_md v) [(5, pos)] (p_ly v) Sc _ 0 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + B5_R3)) 5 pos
    (pf_SH v pos + 8) 64 HJ).
  - left. reflexivity.
  - exact Hsp.
  - exact (b5_m16 _ _ G6 G3).
  - lia.
  - rewrite ESTK, ES. lia.
  - apply (b5q3_bvr _ _ 3); [reflexivity | exact Q3].
  - apply (b5q3_bvr _ _ 4); [reflexivity | exact Q4].
  - apply (b5q3_bvr _ _ 1); [reflexivity | exact Q1].
  - apply ret_ok_codeptr_v; [unfold B5_R3, AF_reac_segconf_parse_file; lia | reflexivity].
  - apply (b5q3_bvr _ _ 10); [reflexivity | exact Q10].
  - apply (b5q3_bvr _ _ 11); [reflexivity | exact Q11].
  - lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). lia.
  - change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos). change (fs_frame_bytes 5 / 8) with 256. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hval & HK2).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + B5_R3)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + B5_R3) regs2 mem2 md2).
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HK2 by lia.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
rewrite ESTK in Hpres2.
(* every byte off b5_Wr kept, every visible byte visible *)
assert (KP : b5_kept v pos (rdW Wc memc) (rdW Wc mem2)).
{ split.
  - intros a Ha Hn. rewrite (HK2 a Ha); [exact (KR a Ha) | |]; intros Hq; apply Hn; unfold b5_Wr.
    + right; right. lia.
    + left. rewrite ES in Hq. rewrite ESTK. lia.
  - intros a Ha Hv.
    destruct (b5q3_dec a (pf_SH v pos + 8) (pf_SH v pos + 8 + 64)) as [Ds | Ds].
    { replace a with (pf_SH v pos + 8 + (a - (pf_SH v pos + 8))) by lia. rewrite Hval by lia. discriminate. }
    destruct (b5q3_dec a (pf_s1 v - ESTACK) (pf_s1 v)) as [Dw | Dw].
    { apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ES in Dw. lia. }
    rewrite (HK2 a Ha Ds Dw), (KR a Ha). exact Hv. }
assert (HF0 : forall i, 8 <= i < 72 -> rdW Wc mem2 (pf_SH v pos + i) = Some (pf_io true)).
{ intros i Hi. replace (pf_SH v pos + i) with (pf_SH v pos + 8 + (i - 8)) by lia. rewrite Hval by lia. reflexivity. }
assert (HFS : pf_fsh (rdW Wc mem2) (pf_SH v pos) PF_SC_LINE)
  by exact (b5_keep_fsh v pos _ _ PF_SC_HEAD true G KP HF0 HFSH).
refine (HR3 v pos (p_ly v) Sc Wc regs2 mem2 md2 cf cur nm o ln d _).
split; [|split].
- apply (b5_move B v pos (p_ly v) Sc Wc rX memc mdc PF_SC_HEAD Sc regs2 mem2 md2 PF_SC_LINE HB HJ2).
  + exists (st_fs Sc). destruct Sc; reflexivity.
  + apply Permutation_refl.
  + exact KP.
  + exact (b5_rg_pres (ms_regs ms0) regs2 _ HP2 (b5_FI_cs B v) QFI).
  + exact HFS.
- split; [exact HCTX|]. split; [exact Ho|]. split; [exact Hk|].
  exact (b5_keep_st B v pos (p_ly v) Sc Wc memc mdc _ _ cf cur nm _ G HAR Hin EF KP HC HST).
- apply (b5_rg_pres (ms_regs ms0) regs2 _ HP2); [|exact QL].
  unfold PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia.
Qed.
End e.
End f.
End d.
