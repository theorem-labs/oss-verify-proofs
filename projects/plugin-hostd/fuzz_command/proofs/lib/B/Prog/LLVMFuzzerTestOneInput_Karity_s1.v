(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the reader transports of segment K of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86a04 .. 0x86a38), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_Karity_s1.v and _Krefusal_s1.v (kr_state_keep_loc): the cut facts (lt_body, lt_kregs, lt_words, lt_rec of lib/B/Prog/LLVMFuzzerTestOneInput_defs.v and _Kcut.v) kept by a state whose callee-saved registers are the cut's and whose reader agrees on the frame, the live blocks and the program statics, an 8-byte word read as the recorder vocabulary's field, and the events allowed at a cut; in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh4.v (cl_vkept: the values kept across a call) and lib/B/Prog/PaCallPg.v (rec_repA_kept). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YCfn YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep
  CmdObj CmdRo CmdGlob PaCallPg CmdRecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import rec_clear_c send_message_c check_reply_c
  check_arity_c check_words_c check_refusal_c check_round_trip_c verbs_receive_c LLVMFuzzerTestOneInput_c
  LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_Kcut.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* a callee-saved register, named by its bv literal, is kept by aregs_preserved (stated over Z_to_bv 5 z) *)
Lemma lt_pres_loc : forall (regs regs' : bvmap 5 word) (rr : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned rr) -> getr regs' rr = getr regs rr.
Proof.
intros regs regs' rr HP Hc. pose proof (HP (bv_unsigned rr) Hc) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
Ltac lt_cs := match goal with |- acallee_saved ?t => let v := eval vm_compute in t in change t with v end;
  unfold acallee_saved; lia.
(* aregs_preserved composes *)
Lemma lt_pres_trans : forall r1 r2 r3 : bvmap 5 word, aregs_preserved r1 r2 -> aregs_preserved r2 r3 ->
  aregs_preserved r1 r3.
Proof. intros r1 r2 r3 H12 H23 z Hz. rewrite (H23 z Hz). exact (H12 z Hz). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* an 8-byte word read through the ASan view is the 8-byte field the recorder's vocabulary reads *)
Lemma lt_rdword_aval8_loc : forall (segs : list Segment) H mem a v,
  rdword (aview segs H mem) a = Some v -> aval_mem (aview segs H mem) a 8 v.
Proof.
intros segs H mem a v E k Hk.
pose proof (val_mem_of_rdword segs H mem a v E k Hk) as Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte.
apply Z.mod_small. apply Z.mod_pos_bound. lia.
Qed.

Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Section e.
Variable B : asyms.
Variable MT : ameter_ops.

(* the cut's facts at a state that keeps the callee-saved registers, the frame [sp1, sp0), the live blocks and the
   program's statics, with the journal from the entry (lib/A/Prog/LLVMFuzzerTestOneInput_Krefusal_s1.v
   kr_state_keep_loc, over aregs_preserved) *)
Lemma lt_kcut_keep : forall cx ly S (W : world SEGS) regs mem md k ly' S' (W' : world SEGS) regs' mem' md' k'
  m r Rh R O q text copy arr wp,
  lt_body B cx ly S W regs mem md k m -> lt_kregs cx regs (rdW W mem) r Rh ->
  lt_words cx (rdW W mem) (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp ->
  lt_rec B cx ly S W mem R O q (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly' S' W' mem' md' k' ->
  aregs_preserved regs regs' ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall a, (x_sp1 cx <= a < x_sp0 cx \/ (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
     inFP cmd_PG a) -> rdW W' mem' a = rdW W mem a) ->
  lt_body B cx ly' S' W' regs' mem' md' k' m /\ lt_kregs cx regs' (rdW W' mem') r Rh /\
  lt_words cx (rdW W' mem') (lt_D (x_pl cx) (x_n cx) r) (lt_ws (x_pl cx) (x_n cx) r) text copy arr wp /\
  lt_rec B cx ly' S' W' mem' R O q (lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr).
Proof.
intros cx ly S W regs mem md k ly' S' W' regs' mem' md' k' m r Rh R O q text copy arr wp
  HBODY HKR HWORDS HREC HJ' HP HPERM HK.
assert (HR : forall rr : bv 5, acallee_saved (bv_unsigned rr) -> getr regs' rr = getr regs rr)
  by (intros rr Hc; exact (lt_pres_loc regs regs' rr HP Hc)).
assert (KF : forall a, x_sp1 cx <= a < x_sp0 cx -> rdW W' mem' a = rdW W mem a) by (intros a Ha; apply HK; left; exact Ha).
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> rdW W' mem' a = rdW W mem a)
  by (intros p n a Hp Ha; apply HK; right; left; exists p, n; split; [exact Hp | exact Ha]).
assert (KG : forall a, inFP cmd_PG a -> rdW W' mem' a = rdW W mem a) by (intros a Ha; apply HK; right; right; exact Ha).
assert (RW : forall a v, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> rdword (rdW W mem) a = Some v ->
  rdword (rdW W' mem') a = Some v).
{ intros a v H1 H2 H. rewrite (rdword_ext (rdW W mem) (rdW W' mem') a); [exact H|]. intros j Hj. apply KF; lia. }
assert (Hsp01 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
destruct HBODY as (HFR & HSL & H8 & H9 & H18 & H25 & H26 & H27 & Hm).
destruct HFR as (_ & Hsp & H3 & H4 & HSV).
destruct HKR as (Hr & H23 & H24 & H21 & Rs & Rh' & HWh).
destruct HREC as (HREP & HSP & HCL & HQ & RQ & HPR).
pose proof (lt_ws_bounds (x_pl cx) (x_n cx) r) as (HL0 & _ & _ & H8ws & _).
assert (HINB : forall pn, In pn (O ++ x_bl0 B cx ++ lt_wblocks (lt_D (x_pl cx) (x_n cx) r) text copy arr) ->
  In pn (ablocks B ly S)) by (intros pn Hq; exact (Permutation_in _ (Permutation_sym HPR) Hq)).
assert (HO : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hq; apply HINB; apply in_or_app; left; exact Hq).
split; [|split; [|split]].
- (* lt_body *)
  split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|exact Hm]]]]]]]].
  + split; [exact HJ'|]. split; [unfold spZ; rewrite (HR 2%bv ltac:(lt_cs)); exact Hsp|].
    split; [rewrite (HR 3%bv ltac:(lt_cs)); exact H3|]. split; [rewrite (HR 4%bv ltac:(lt_cs)); exact H4|].
    intros i rr Hi. specialize (HSV i rr Hi).
    assert (Hi13 : (i < 13)%nat).
    { pose proof (proj1 (nth_error_Some LT_SAVED i) ltac:(rewrite Hi; discriminate)) as Hlt.
      cbn [LT_SAVED length] in Hlt. exact Hlt. }
    apply RW; [lia | lia | exact HSV].
  + intros o v Hin. specialize (HSL o v Hin).
    assert (Ho : 32 <= o <= 104).
    { unfold LT_SLOTS in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Heq|Hin]; [injection Heq as Heq _; lia|]). destruct Hin. }
    apply RW; [lia | lia | exact HSL].
  + rewrite (HR 8%bv ltac:(lt_cs)). exact H8.
  + rewrite (HR 9%bv ltac:(lt_cs)). exact H9.
  + rewrite (HR 18%bv ltac:(lt_cs)). exact H18.
  + rewrite (HR 25%bv ltac:(lt_cs)). exact H25.
  + rewrite (HR 26%bv ltac:(lt_cs)). exact H26.
  + rewrite (HR 27%bv ltac:(lt_cs)). exact H27.
- (* lt_kregs *)
  split; [exact Hr|]. split; [rewrite (HR 23%bv ltac:(lt_cs)); exact H23|].
  split; [rewrite (HR 24%bv ltac:(lt_cs)); exact H24|]. split; [rewrite (HR 21%bv ltac:(lt_cs)); exact H21|].
  split; [exact Rs|]. split; [exact Rh'|].
  apply RW; [unfold LT_HOSTB; lia | unfold LT_HOSTB; lia | exact HWh].
- (* lt_words *)
  unfold lt_words in HWORDS |- *. cbv zeta in HWORDS |- *.
  destruct HWORDS as (WT & WC & WA & WN & WL & WP & WS).
  set (L0 := StrFun.strnlen_res (Z.of_nat (length (lt_D (x_pl cx) (x_n cx) r))) (lt_D (x_pl cx) (x_n cx) r)) in *.
  assert (HARR : In (arr, SlotSpec.arr_size L0) (ablocks B ly S)).
  { apply HINB. apply in_or_app; right. apply in_or_app; right. unfold lt_wblocks. cbn [In]. right; right; left. reflexivity. }
  assert (HCPY : In (copy, L0 + 1) (ablocks B ly S)).
  { apply HINB. apply in_or_app; right. apply in_or_app; right. unfold lt_wblocks. cbn [In]. right; left. reflexivity. }
  pose proof (req_size_pos (SlotSpec.arr_size L0) ltac:(unfold SlotSpec.arr_size; pose proof (Z.div_pos L0 2); lia))
    as [_ HRA].
  pose proof (req_size_pos (L0 + 1) ltac:(lia)) as [_ HRC].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WT]|].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WC]|].
  split; [apply RW; [unfold LT_W; lia | unfold LT_W; lia | exact WA]|].
  split; [apply (aval_mem_kept_r (rdW W mem)); [intros x Hx; apply KF; unfold LT_W in *;
    cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia | exact WN]|].
  split; [exact WL|]. split.
  + intros i pt Hi. specialize (WP i pt Hi).
    assert (Hil : (i < length (lt_ws (x_pl cx) (x_n cx) r))%nat)
      by (rewrite <- WL; apply nth_error_Some; rewrite Hi; discriminate).
    rewrite (rdword_ext (rdW W mem) (rdW W' mem') (arr + 8 * Z.of_nat i)); [exact WP|].
    intros j Hj. apply (KB arr (SlotSpec.arr_size L0)); [exact HARR | lia].
  + intros i pt w Hi Hw. destruct (WS i pt w Hi Hw) as (C1 & C2 & C3).
    split; [exact C1|]. split; [exact C2|].
    apply (astr_atR_kept_r (rdW W mem)); [|exact C3].
    intros x Hx. apply (KB copy (L0 + 1)); [exact HCPY | lia].
- (* lt_rec *)
  split; [|split; [exact HSP|split; [exact HCL|split; [|split; [exact RQ | exact (perm_trans HPERM HPR)]]]]].
  + apply (rec_repA_kept B ly S (rdW W mem) ly' S' (rdW W' mem') R O HREP).
    * intros pn Hq. exact (Permutation_in _ (Permutation_sym HPERM) (HO pn Hq)).
    * intros a [Ha | [Ha | Ha]].
      -- apply KG. exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity | unfold REC_SIZE in Ha; cbn [fst snd]; lia].
      -- apply KG. exists (A_REC_SPILL, A_REC_SPILL + 56).
         split; [right; left; reflexivity | unfold SC_SIZE in Ha; cbn [fst snd]; lia].
      -- destruct Ha as (rg & Hrg & Hrga). unfold ablocks_fp in Hrg. apply in_map_iff in Hrg as ([p n] & <- & Hq).
         cbn [fst snd] in Hrga. exact (KB p n a (HO _ Hq) Hrga).
  + apply (aval_mem_kept_r (rdW W mem)); [|exact HQ].
    intros x Hx. apply KG. exists (A_G_QUITTING, A_G_QUITTING + 4).
    split; [right; right; left; reflexivity | cbn [fst snd]; cbn [Z.of_nat Pos.of_succ_nat] in Hx; lia].
Qed.

(* what a callee journal without footprint keeps, for a call made at sp1 = x_sp0 cx - 256 that left the layout's
   live blocks as a Permutation of the caller's: the caller's frame above the callee's window, the live blocks and
   the program's statics (CmdRecImg.v's cmd_prog_unowned: outside the owned statics and the errno cell) *)
Lemma lt_call_kept : forall (HB : CmdBSyms B) (LAWS : AR_laws SEGS B) (IMG : cmd_img_facts SEGS B)
  cx STK1 ly S (W : world SEGS) mem md ly' S' (W' : world SEGS) mem' md' kk,
  ajournal SEGS B STK1 (x_sp0 cx + -256) [] ly S W mem md [] ly' S' W' mem' md' kk ->
  alloc_ceiling <= x_sp1 cx -> x_sp0 cx <= 2 ^ 64 ->
  Permutation (ablocks B ly' S') (ablocks B ly S) ->
  forall a, (x_sp1 cx <= a < x_sp0 cx \/ (exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n) \/
     inFP cmd_PG a) -> rdW W' mem' a = rdW W mem a.
Proof.
intros HB LAWS IMG cx STK1 ly S W mem md ly' S' W' mem' md' kk HJ Hsp Hsp0 HPERM a Ha.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & F2 & F3 & _).
assert (Hsp01 : x_sp1 cx = x_sp0 cx + -256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
destruct Ha as [Ha | [(p & n & Hpn & Ha) | Ha]].
- apply F1; [lia | lia | apply inFP_nil].
- replace a with (p + (a - p)) by lia.
  apply (F2 p n (a - p) Hpn (Permutation_in _ (Permutation_sym HPERM) Hpn)); [lia | apply inFP_nil].
- destruct (cmd_prog_unowned SEGS B LAWS HB IMG a Ha) as (Hi & Ho & He). apply F3; [exact Hi | exact Ho | exact He |].
  apply fp_spares_closed; [exact sink_closed_nil | apply inFP_nil].
Qed.

(* every point of the walk is within the event budget the entry has: the rest of the budget is still allowed *)
Lemma lt_nev_bud : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  lt_bud MT cx S k acc rem -> st_nev S + rem <= EV_MAX.
Proof.
intros cx ly S W mem md k acc rem HBASE HJ (Hk & Hrem & Hkr & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
destruct HBASE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hev & _).
revert Hk Hrem Hkr Hnev Hev. generalize (EV_LTOI (x_pl cx)). intros. lia.
Qed.

(* the events allowed now (a call of no event at a cut) *)
Lemma lt_nev_now : forall cx ly S (W : world SEGS) mem md k acc rem,
  lt_base B MT cx ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem md k ->
  lt_bud MT cx S k acc rem -> st_nev S <= EV_MAX.
Proof.
intros cx ly S W mem md k acc rem HBASE HJ HBUD.
pose proof (lt_nev_bud cx ly S W mem md k acc rem HBASE HJ HBUD) as H1. destruct HBUD as (_ & H2 & _).
revert H1 H2. generalize rem. intros. lia.
Qed.

(* the budget with its counts rewritten *)
Lemma lt_bud_eq : forall cx S k acc rem k' rem', lt_bud MT cx S k acc rem -> k' = k -> rem' = rem ->
  lt_bud MT cx S k' acc rem'.
Proof. intros cx S k acc rem k' rem' H -> ->. exact H. Qed.
End e.
End f.
End d.
