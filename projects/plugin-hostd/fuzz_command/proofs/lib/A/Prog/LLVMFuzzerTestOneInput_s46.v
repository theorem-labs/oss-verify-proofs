(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment E of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x8692c .. 0x8693c: the word count's store into the struct and the three restores s2, s11, s5 from the frame), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a state inside the function, run to the next segment's statement). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaArt PaSB PaDenot CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s40.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ---- the seed state at 0x8692c (AW_E) ----
   The environment's atoms 0 .. 31 are the registers at 0x8692c; atom 32 is the word the split loop spilled at
   sp + 88 (r - hdr_n), atom 33 the one at sp + 96 (the pass m). One region: the frame at sp, read at sp + 32
   (&g_rec, lt_slots' word), sp + 88 and sp + 96, written at sp + 144 .. 148 (w.n). No inline check, so no shadow
   entry. *)
Definition AEx : sv := SOff 9 0.
Definition AEspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ae_frame : YP09.region :=
YP09.mkRegion (Some 2%nat) 0 148 144 148
  [YP09.mkChunk 32 (CVal 8 (SLit A_G_REC)); YP09.mkChunk 88 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0))].
Definition ae_facts : facts := mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (9%nat, mkAF LT_SB LT_SB 0) ] [] [].
Definition ss_ae : sstate := mkSS AW_E sr_atoms [ae_frame] None ae_facts.
Definition ae_SH : list shent := [].
Definition ae_extra (s5 mv : Z) : list word := [Z_to_bv 64 s5; Z_to_bv 64 mv].

(* ---- the words of the line: at most (|line| + 1) / 2 of them, none holds a NUL ---- *)
(* lib/Prog/SlotRec.v words_acc_count / words_count, carried here (that file is outside this walk's closure) *)
Lemma ae_words_acc_count_loc : forall l cur,
  (2 * length (Verbs.words_acc cur l) <= length l + 1 + match cur with [] => 0 | _ :: _ => 1 end)%nat.
Proof.
induction l as [|b l IH]; intros cur.
- destruct cur; cbn; lia.
- cbn [Verbs.words_acc]. destruct (Verbs.is_sep b).
  + specialize (IH []). destruct cur as [|c cur]; cbn in IH |- *; lia.
  + specialize (IH (cur ++ [b])). destruct cur as [|c cur]; cbn in IH |- *; lia.
Qed.
Lemma ae_words_count_loc : forall l, (2 * length (Verbs.words l) <= length l + 1)%nat.
Proof. intros l. unfold Verbs.words. pose proof (ae_words_acc_count_loc l []) as H. cbv beta iota in H. lia. Qed.
Lemma ae_words_nz_loc : forall D w, In w (Verbs.words (Verbs.line D)) -> ~ In (Z_to_bv 8 0) w.
Proof.
intros D w Hw Hin.
destruct (Verbs.words_acc_spec (fun b => bv_unsigned b <> 0) (Verbs.line D) [] (fun b H => False_ind _ H)
  (Verbs.line_nonul D) w Hw) as [_ Hb].
destruct (Hb _ Hin) as [Hz _]. apply Hz. reflexivity.
Qed.

(* ---- readers kept outside the 4 bytes of w.n ---- *)
Lemma ae_rdword_kept : forall (rd rd' : reader) lo hi a v, kept_out rd rd' lo hi -> rdword rd a = Some v ->
  0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= lo \/ hi <= a) -> rdword rd' a = Some v.
Proof.
intros rd rd' lo hi a v HK H Ha Hb Hs. rewrite (rdword_ext rd rd' a); [exact H|]. intros j Hj. apply HK; lia.
Qed.
Lemma ae_aval_kept : forall (rd rd' : reader) lo hi a n v, kept_out rd rd' lo hi -> aval_mem rd a n v ->
  0 <= a -> a + Z.of_nat n <= lo -> lo < 2 ^ 64 -> aval_mem rd' a n v.
Proof. intros rd rd' lo hi a n v HK H Ha Hl Hlo k Hk. rewrite (HK (a + Z.of_nat k)) by lia. exact (H k Hk). Qed.
(* a word found in the copy buffer is a C string where it starts *)
Lemma ae_str_of_found : forall (rd : reader) copy (C : list byte) pt (w : list byte),
  abytes_atR rd copy C -> copy <= pt ->
  (forall t, (t <= length w)%nat -> nth_error C (Z.to_nat (pt - copy) + t) = nth_error (w ++ [Z_to_bv 8 0]) t) ->
  ~ In (Z_to_bv 8 0) w -> astr_atR rd pt w.
Proof.
intros rd copy C pt w HC Hp HW Hn. split; [|exact Hn].
intros t Ht. rewrite length_app in Ht. cbn [length] in Ht.
pose proof (HW t ltac:(lia)) as Ht2.
destruct (nth_error (w ++ [Z_to_bv 8 0]) t) as [x|] eqn:Ex;
  [|apply nth_error_None in Ex; rewrite length_app in Ex; cbn [length] in Ex; lia].
try rewrite Ex in Ht2.
assert (Hj : (Z.to_nat (pt - copy) + t < length C)%nat) by (apply nth_error_Some; rewrite Ht2; discriminate).
pose proof (HC _ Hj) as Hr.
replace (nth (Z.to_nat (pt - copy) + t) C (Z_to_bv 8 0)) with x in Hr by (symmetry; apply nth_error_nth; exact Ht2).
replace (nth t (w ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)) with x by (symmetry; apply nth_error_nth; exact Ex).
replace (pt + Z.of_nat t) with (copy + Z.of_nat (Z.to_nat (pt - copy) + t)) by lia. exact Hr.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition ae_E (regs : bvmap 5 word) (s5 mv : Z) : env := Eimg (Ereg regs (ae_extra s5 mv)).

Lemma ae_aval_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
unfold YO0f.le_byte, YG0f.le_byte. apply Z.mod_mod. lia.
Qed.

(* the seed: the symbolic state at 0x8692c *)
Lemma ae_seed : forall (W : world SEGS) regs mem s5 mv,
  2 ^ 46 <= spZ regs -> spZ regs + 256 <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
  getr regs 9 = w64 LT_SB ->
  (forall a, spZ regs + 144 <= a < spZ regs + 148 -> apresent (w_H W) mem a) ->
  rdword (rdW W mem) (spZ regs + 32) = Some A_G_REC ->
  rdword (rdW W mem) (spZ regs + 88) = Some s5 -> 0 <= s5 < 2 ^ 64 ->
  rdword (rdW W mem) (spZ regs + 96) = Some mv -> 0 <= mv < 2 ^ 64 ->
  st_ok_pi SEGS VAL (ae_E regs s5 mv) ss_ae (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_E)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s5 mv Hs1 Hs2 Hal R9 Hpres G32 G88 R88 G96 R96.
set (E := ae_E regs s5 mv).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (ae_extra s5 mv)) n)
  by (intros n Hn; subst E; unfold ae_E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E9 : ew E 9 = getr regs 9) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 s5) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 mv) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
unfold ss_ae. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold ae_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, ae_frame.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
  split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply Hpres; lia|].
  constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (chunk_ok_val SEGS E _ _ 32 8 (SLit A_G_REC) A_G_REC); [reflexivity | unfold A_G_REC; zside | zside |].
    exact (val_mem_of_rdword SEGS _ _ _ _ G32).
  + apply (chunk_ok_val SEGS E _ _ 88 8 (SOff 32 0) s5);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
    * replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. exact R88.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G88).
  + apply (chunk_ok_val SEGS E _ _ 96 8 (SOff 33 0) mv);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | | zside |].
    * replace (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) by reflexivity. exact R96.
    * exact (val_mem_of_rdword SEGS _ _ _ _ G96).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  cbn [ae_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E9, R9. unfold w64. rewrite unsigned_lit_small by (unfold LT_SB; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold LT_SB.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.

Ltac ae_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- segment E: 0x8692c .. 0x8693c ---- *)
Lemma aw_seg_E : forall m, LT_K_stmt B MT m -> AW_E_stmt B MT m.
Proof.
intros m HK. unfold AW_E_stmt.
intros cx q ly S W regs mem md k acc text copy arr C wp Hm HFP0 HC HR HWS R24 R23 R25 R19 R20 R21 HSP5 HSP11 Hlwp HCb HCl
  HARR HFD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as ((HB0 & HFRM & HSl & R8 & R9 & R22 & Hm32 & Hn & Hp & Hr & Hh & Hs) & Hbud).
pose proof HFRM as (HJ & Hsp & R3 & R4 & HSV). clear HFRM.
pose proof HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HWS as (HW0 & HW8 & HW16).
pose proof HR as (HRR & Hspill & Hcalls & HQ & HQr & HPERM).
assert (HSTK : LTOI_STK = 32768) by reflexivity.
(* the frame lies above the heap: sp = entry sp - 256 *)
assert (HSP : alloc_ceiling + 32768 - 256 <= x_sp1 cx /\ x_sp1 cx + 256 <= 2 ^ 47).
{ unfold x_sp1, LT_FRAME. rewrite HSTK in Hslo. lia. }
assert (Hal1 : x_sp1 cx mod 16 = 0).
{ unfold x_sp1, LT_FRAME. rewrite Zminus_mod, Hal16. reflexivity. }
(* the three blocks of the message, live and below the frame *)
change (aw_blocks cx q text copy arr) with
  [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] in HPERM.
assert (HinB : forall pn, In pn [(text, q_L0 cx q + 1); (copy, q_L0 cx q + 1); (arr, SlotSpec.arr_size (q_L0 cx q))] ->
  In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. apply in_or_app. right.
  exact Hpn. }
assert (HO1 : forall pn, In pn (q_O1 q) -> In pn (ablocks B ly S)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hpn. }
destruct (al_blocks _ _ LAWS ly S W mem md copy _ HAR0 (HinB _ (in_cons _ _ _ (in_eq _ _))))
  as (_ & Hc4096 & Hcceil & _ & _ & _ & HcMM).
destruct (al_blocks _ _ LAWS ly S W mem md arr _ HAR0 (HinB _ (in_cons _ _ _ (in_cons _ _ _ (in_eq _ _)))))
  as (_ & Ha4096 & Haceil & _).
unfold MALLOC_MAX in HcMM.
(* L0, the line and the word count *)
pose proof (q_L0_U cx q) as HL0.
pose proof (SlotWords.sw_line_le (q_D cx q)) as HLN.
change (Verbs.line (q_D cx q)) with (q_LN cx q) in HLN. change (Verbs.upto0 (q_D cx q)) with (q_U cx q) in HLN.
pose proof (ae_words_count_loc (q_LN cx q)) as HWC. change (Verbs.words (q_LN cx q)) with (q_ws cx q) in HWC.
pose proof (Z.div_mod (q_L0 cx q) 2 ltac:(lia)) as HDM.
pose proof (Z.mod_pos_bound (q_L0 cx q) 2 ltac:(lia)) as HMB.
assert (HAS : SlotSpec.arr_size (q_L0 cx q) = 8 * (q_L0 cx q / 2) + 16) by reflexivity.
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [_ Hrq1].
pose proof (req_size_pos (SlotSpec.arr_size (q_L0 cx q)) ltac:(lia)) as [_ Hrq2].
(* the seed *)
assert (Hr5 : 0 <= q_r q - SlotSpec.hdr_n (q_r q) < 2 ^ 64) by (unfold SlotSpec.hdr_n; lia).
assert (Hmv : 0 <= Z.of_nat (q_m q) < 2 ^ 64) by lia.
assert (G32 : rdword (rdW W mem) (spZ regs + 32) = Some A_G_REC).
{ rewrite Hsp. apply HSl. unfold LT_SLOTS. do 4 right. left. reflexivity. }
assert (G88 : rdword (rdW W mem) (spZ regs + 88) = Some (q_r q - SlotSpec.hdr_n (q_r q))) by (rewrite Hsp; exact HSP5).
assert (G96 : rdword (rdW W mem) (spZ regs + 96) = Some (Z.of_nat (q_m q))) by (rewrite Hsp; exact HSP11).
assert (HP144 : forall a, spZ regs + 144 <= a < spZ regs + 148 -> apresent (w_H W) mem a).
{ intros a Ha. apply Hpres. rewrite HSTK. rewrite Hsp in Ha. unfold x_sp1, x_sp0, LT_FRAME in *. lia. }
pose proof (ae_seed W regs mem (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))
  ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; lia) ltac:(rewrite Hsp; exact Hal1) R9 HP144 G32 G88 Hr5 G96 Hmv) as HS.
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew (ae_E regs (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))) n =
  ew (Ereg regs (ae_extra (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q)))) n)
  by (intros n Hn0; unfold ae_E; apply Eimg_low; exact Hn0).
assert (HED : ed (ae_E regs (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))) =
  ed (Ereg regs (ae_extra (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))))) by reflexivity.
assert (HEI : img_env VAL A_LIM (ae_E regs (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))))
  by (unfold ae_E; apply Eimg_env).
remember (ae_E regs (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q))) as E eqn:HE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr).
{ intros n rr Hn0. pose proof (bv_unsigned_in_range 5 rr) as Hr5'. change (bv_modulus 5) with 32 in Hr5'.
  rewrite EL by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn0. }
assert (E2 : ew E 2 = getr regs 2) by (apply EEo; reflexivity).
assert (E21 : ew E 21 = getr regs 21) by (apply EEo; reflexivity).
assert (E32 : ew E 32 = Z_to_bv 64 (q_r q - SlotSpec.hdr_n (q_r q)))
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (q_m q))) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (ae_extra (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q)))) E).
{ split; [intros n Hn0; rewrite EL by (unfold A_TEXT; lia); reflexivity | exact HED]. }
assert (SHOK : sh_ok SEGS AEx ae_SH E (mrestrict (w_H W) mem)) by (unfold sh_ok, ae_SH; apply Forall_nil).
clear HE EL HED.
(* 0x8692c .. 0x8693c: sw s5,144(sp); ld s2,32(sp); ld s11,96(sp); ld s5,88(sp) *)
paj_run_to_tok RUNTO HS HJ SHOK AEspan LO_K.
{ unfold ss_ae. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -256); [reflexivity | | | | apply awr_ok_nil];
    cbv [ae_frame YP09.r_wlo YP09.r_whi].
  - rewrite Usp, Hsp. unfold x_sp1, x_sp0, LT_FRAME. lia.
  - rewrite HSTK. lia.
  - lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv := d) in *; clearbody mdv end.
(* memory outside w.n's 4 bytes is kept by the run *)
assert (KEEP : kept_out (rdW W mem) (rdW W (ms_mem ms)) (x_sp1 cx + 144) (x_sp1 cx + 148)).
{ lazymatch goal with Hfr : frame_of E _ (mrestrict _ mem) (mrestrict _ _) |- _ =>
  intros a Ha Hna;
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_sp1 cx + 144 <= a < x_sp1 cx + 148) Hfr);
    [|exact Ha | exact Hna];
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  destruct Hin as [Hq0 | []]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite Usp, Hsp in Hrr; lia end. }
(* w.n holds the word count *)
assert (HST : aval_mem (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 24) 4 (Z.of_nat (length (q_ws cx q)))).
{ pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
  pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR1.
  pose proof (region_ok_chunk SEGS _ _ _ _ HR1 (in_eq _ _)) as HC1.
  cbn [YP09.r_base base_val] in HC1. rewrite Usp in HC1.
  assert (HV : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs + 144) (N.to_nat 4)
    (Z.of_nat (length (q_ws cx q)))).
  { apply (val_of_chunk_ok SEGS E _ _ 144 4 (SOff 21 0) _ HC1).
    - cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned. exact R21.
    - replace (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) by reflexivity. lia.
    - zside. }
  replace (x_sp1 cx + LT_W + 24) with (spZ regs + 144) by (rewrite Hsp; unfold LT_W; lia).
  exact (ae_aval_of_val _ _ _ _ _ HV). }
pmkst HS.
prreg HS (18%bv : bv 5) P18. prreg HS (21%bv : bv 5) P21. prreg HS (27%bv : bv 5) P27.
pose proof (regs_kept_of_st_ok_pi E _ _ regs (ae_extra (q_r q - SlotSpec.hdr_n (q_r q)) (Z.of_nat (q_m q)))
  [2; 3; 4; 8; 9; 19; 20; 22; 23; 24; 25]%bv HS HAE ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
assert (K2 : getr (ms_regs ms) 2 = getr regs 2) by (apply HKR; ae_in).
assert (K3 : getr (ms_regs ms) 3 = getr regs 3) by (apply HKR; ae_in).
assert (K4 : getr (ms_regs ms) 4 = getr regs 4) by (apply HKR; ae_in).
assert (K8 : getr (ms_regs ms) 8 = getr regs 8) by (apply HKR; ae_in).
assert (K9 : getr (ms_regs ms) 9 = getr regs 9) by (apply HKR; ae_in).
assert (K19 : getr (ms_regs ms) 19 = getr regs 19) by (apply HKR; ae_in).
assert (K20 : getr (ms_regs ms) 20 = getr regs 20) by (apply HKR; ae_in).
assert (K22 : getr (ms_regs ms) 22 = getr regs 22) by (apply HKR; ae_in).
assert (K23 : getr (ms_regs ms) 23 = getr regs 23) by (apply HKR; ae_in).
assert (K24 : getr (ms_regs ms) 24 = getr regs 24) by (apply HKR; ae_in).
assert (K25 : getr (ms_regs ms) 25 = getr regs 25) by (apply HKR; ae_in).
(* the frame words the next segments read, kept *)
assert (HSV' : lt_saved cx (rdW W (ms_mem ms))).
{ intros i r Hir. pose proof (HSV i r Hir) as H1.
  assert (Hi : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hir; discriminate).
  change (length LT_SAVED) with 13%nat in Hi.
  apply (ae_rdword_kept _ _ _ _ _ _ KEEP H1); unfold x_sp1, x_sp0, LT_FRAME in *; lia. }
assert (HSl' : lt_slots cx (rdW W (ms_mem ms))).
{ intros o v Hin. pose proof (HSl o v Hin) as H1.
  assert (Ho : 0 <= o <= 80).
  { assert (HF8 : forallb (fun p => (0 <=? fst p) && (fst p <=? 80)) LT_SLOTS = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in HF8. specialize (HF8 _ Hin). cbn [fst] in HF8.
    apply andb_prop in HF8 as [H2 H3]. apply Z.leb_le in H2. apply Z.leb_le in H3. lia. }
  apply (ae_rdword_kept _ _ _ _ _ _ KEEP H1); lia. }
assert (Hh' : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_HOSTB) = Some (r_host (q_Rh q)))
  by (apply (ae_rdword_kept _ _ _ _ _ _ KEEP Hh); unfold LT_HOSTB; lia).
assert (Hs' : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_STATEB) = Some (r_state (q_Rh q)))
  by (apply (ae_rdword_kept _ _ _ _ _ _ KEEP Hs); unfold LT_STATEB; lia).
assert (HW0' : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W) = Some text)
  by (apply (ae_rdword_kept _ _ _ _ _ _ KEEP HW0); unfold LT_W; lia).
assert (HW8' : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 8) = Some copy)
  by (apply (ae_rdword_kept _ _ _ _ _ _ KEEP HW8); unfold LT_W; lia).
assert (HW16' : rdword (rdW W (ms_mem ms)) (x_sp1 cx + LT_W + 16) = Some arr)
  by (apply (ae_rdword_kept _ _ _ _ _ _ KEEP HW16); unfold LT_W; lia).
(* the pointer array and the words, in their blocks below the frame *)
assert (HARR' : forall i pt, nth_error wp i = Some pt -> rdword (rdW W (ms_mem ms)) (arr + 8 * Z.of_nat i) = Some pt).
{ intros i pt Hip. assert (Hi : (i < length wp)%nat) by (apply nth_error_Some; rewrite Hip; discriminate).
  apply (rdword_kept _ _ _ _ _ _ KEEP (HARR i pt Hip)); lia. }
assert (HWD' : forall i pt w, nth_error wp i = Some pt -> nth_error (q_ws cx q) i = Some w ->
  copy <= pt /\ pt + Z.of_nat (length w) + 1 <= copy + q_L0 cx q + 1 /\ astr_atR (rdW W (ms_mem ms)) pt w).
{ intros i pt w Hip Hiw. destruct (HFD i pt w Hip Hiw) as (P1 & P2 & P3).
  rewrite Z2Nat.id in P2 by lia.
  pose proof (ae_str_of_found (rdW W mem) copy C pt w HCb P1 P3 (ae_words_nz_loc (q_D cx q) w (nth_error_In _ _ Hiw)))
    as Hstr.
  split; [exact P1|]. split; [lia|].
  apply (astr_atR_kept _ _ _ _ pt w KEEP Hstr); lia. }
(* the recorder, g_quitting, in the image below the frame *)
assert (HRR' : rec_repA B ly S (rdW W (ms_mem ms)) (q_R1 cx q) (q_O1 q)).
{ apply (rec_repA_kept B ly S (rdW W mem) ly S _ _ _ HRR HO1). intros a Ha.
  assert (Hal : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | [Ha | Ha]].
    - unfold A_G_REC, REC_SIZE in Ha. lia.
    - unfold A_REC_SPILL, SC_SIZE in Ha. lia.
    - destruct Ha as (r & Hr0 & Hlo & Hhi). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([p n] & <- & Hpn).
      cbn [fst snd] in Hlo, Hhi.
      destruct (al_blocks _ _ LAWS ly S W mem md p n HAR0 (HO1 _ Hpn)) as (_ & Hp4096 & Hpceil & _). lia. }
  apply KEEP; lia. }
assert (HQ' : aval_mem (rdW W (ms_mem ms)) A_G_QUITTING 4 (if q_quit cx q then 1 else 0))
  by (apply (ae_aval_kept _ _ _ _ _ _ _ KEEP HQ); unfold A_G_QUITTING; cbn [Z.of_nat Pos.of_succ_nat]; lia).
(* the registers at 0x8693c *)
assert (Hsp' : spZ (ms_regs ms) = x_sp1 cx) by (unfold spZ; rewrite K2; exact Hsp).
assert (R3' : getr (ms_regs ms) 3 = getr (x_regs cx) 3) by (rewrite K3; exact R3).
assert (R4' : getr (ms_regs ms) 4 = getr (x_regs cx) 4) by (rewrite K4; exact R4).
assert (R8' : getr (ms_regs ms) 8 = w64 32) by (rewrite K8; exact R8).
assert (R9' : getr (ms_regs ms) 9 = w64 LT_SB) by (rewrite K9; exact R9).
assert (R22' : getr (ms_regs ms) 22 = w64 LT_MASK) by (rewrite K22; exact R22).
assert (R18' : getr (ms_regs ms) 18 = w64 A_G_REC) by (rewrite P18; reflexivity).
assert (R19' : getr (ms_regs ms) 19 = w64 (lt_len (x_pl cx) (x_n cx) (q_r q))) by (rewrite K19; exact R19).
assert (R20' : getr (ms_regs ms) 20 = w64 (q_src cx q)) by (rewrite K20; exact R20).
assert (R21' : getr (ms_regs ms) 21 = w64 (q_r q - SlotSpec.hdr_n (q_r q))) by (rewrite P21, E32; reflexivity).
assert (R27' : getr (ms_regs ms) 27 = w64 (Z.of_nat (q_m q))) by (rewrite P27, E33; reflexivity).
assert (R23' : getr (ms_regs ms) 23 = w64 copy) by (rewrite K23; exact R23).
assert (R24' : getr (ms_regs ms) 24 = w64 text) by (rewrite K24; exact R24).
assert (R25' : getr (ms_regs ms) 25 = w64 arr) by (rewrite K25; exact R25).
(* the four facts aw_LT_K takes *)
exact (aw_LT_K B MT m HK cx q ly S W (ms_regs ms) (ms_mem ms) mdv k acc text copy arr wp Hm HFP0
  (conj (conj HB0 (conj (conj HJ (conj Hsp' (conj R3' (conj R4' HSV')))) (conj HSl' (conj R8' (conj R9' (conj R22'
    (conj Hm32 (conj Hn (conj Hp (conj Hr (conj Hh' Hs'))))))))))) Hbud)
  (conj R18' (conj R19' (conj R20' (conj R21' R27'))))
  (conj R24' (conj R23' (conj R25' (conj HW0' (conj HW8' (conj HW16' (conj HST (conj Hlwp (conj HARR' HWD')))))))))
  (conj HRR' (conj Hspill (conj Hcalls (conj HQ' (conj HQr HPERM)))))).
Qed.

End e.
End f.
End d.
