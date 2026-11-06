(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: segment T of the inlined words_of of LLVMFuzzerTestOneInput's ASan walk (plugin-hostd/fuzz_command, 0x86770 .. the trim loop's head 0x867a4, or 0x8680c when the prefix is empty: the copy of the message into text by __asan_memcpy, the inline check of text + L0 and its NUL), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (cl_seedX: the seed of a state inside the function) and A/ACh2.v (a call and back, here a runtime entry through aj_intrin_atS). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv CommandModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdBase CmdRep CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_clear_c send_message_c check_reply_c check_arity_c check_words_c check_refusal_c check_round_trip_c
verbs_receive_c LLVMFuzzerTestOneInput_c LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s01
LLVMFuzzerTestOneInput_s40 LLVMFuzzerTestOneInput_s49.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require SlotSpec HarnessProps SlotWords SlotWordsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the two symbolic states of this segment ----
   A, at 0x86770 (AW_M): every register is its own atom, no region (the three moves and the jal read no memory).
   It runs to the call of __asan_memcpy (0x8677c, ra = 0x86780).
   B, at 0x86780, seated afresh after the call: every register is its own atom, atom 32 = text + L0 (the value
   `add a0,s8,s10` computes, given to the engine as the alias s8 + s10 = atom 32), and the one byte at text + L0 is
   a write window without a chunk. Its shadow entry makes the 1-byte inline check at 0x86784 a token with no
   obligation; the run stops at `beqz s10` (0x86798). *)
Definition WCx : sv := SOff 9 0.
Definition WCspan : Z * Z := (LT_SB, LT_SB + 2 ^ 44 - 1).
Definition ss_wcA : sstate := mkSS AW_M sr_atoms [] None (mkFacts [] [] []).
Definition wc_regionsB : smem := [YP09.mkRegion (Some 32%nat) 0 1 0 1 []].
Definition wc_factsB : facts :=
  mkFacts [ (9%nat, mkAF LT_SB LT_SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 1) 0) ] []
    [ (SAlu ALU_ADD (SOff 24 0) (SOff 26 0), SOff 32 0) ].
Definition ss_wcB : sstate := mkSS 0x29c sr_atoms wc_regionsB None wc_factsB.
Definition wc_SHB : list shent := [mkSHE 32 0 1].

(* ---- lists ---- *)
Lemma wc_nth_firstn_loc : forall (l : list byte) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
induction l as [|b l IH]; intros [|L] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia. apply IH. lia.
Qed.
(* text after the copy and the NUL: the first L bytes of the message, then 0 *)
Lemma wc_text_bytes_loc : forall (rd0 rd3 : reader) text src (D : list byte) (L : nat),
  abytes_atR rd0 src D -> (L <= length D)%nat ->
  (forall i, 0 <= i < Z.of_nat L -> rd3 (text + i) = rd0 (src + i)) ->
  rd3 (text + Z.of_nat L) = Some 0 ->
  abytes_atR rd3 text (firstn L D ++ [Z_to_bv 8 0]).
Proof.
intros rd0 rd3 text src D L HD HL HC HZ i Hi.
rewrite length_app, length_firstn in Hi. cbn [length] in Hi.
destruct (Nat.lt_ge_cases i L) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite length_firstn; lia). rewrite wc_nth_firstn_loc by exact Hlt.
  rewrite (HC (Z.of_nat i)) by lia. exact (HD i ltac:(lia)).
- assert (Hi' : i = L) by lia. subst i.
  rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
  replace (L - Nat.min L (length D))%nat with 0%nat by lia. cbn [nth]. rewrite HZ. reflexivity.
Qed.
Lemma wc_nodup_app_loc : forall {A} (l1 l2 : list A) a, List.NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
Proof.
intros A l1. induction l1 as [|b l1 IH]; intros l2 a H H1 H2; [destruct H1|].
cbn [app] in H. apply NoDup_cons_iff in H as [Hn Hd].
destruct H1 as [<- | H1]; [apply Hn; apply in_or_app; right; exact H2 | exact (IH l2 a Hd H1 H2)].
Qed.
Lemma wc_nodup_app_r_loc : forall {A} (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
intros A l1. induction l1 as [|a l1 IH]; intros l2 H; [exact H|].
cbn [app] in H. apply NoDup_cons_iff in H as [_ H]. exact (IH l2 H).
Qed.
(* the eleven slot words lie at sp + 0 .. sp + 80 *)
Lemma wc_slots_range : forall o v, In (o, v) LT_SLOTS -> 0 <= o <= 80.
Proof.
intros o v H. unfold LT_SLOTS in H. cbn [In] in H.
repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H.
Qed.
Lemma wc_pres_loc : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the environments: atoms 0 .. 31 the registers of the state the stretch starts from; B's atom 32 = text + L0 *)
Definition wc_EA (regs : bvmap 5 word) : env := Eimg (Ereg regs []).
Definition wc_EB (regs : bvmap 5 word) (e : Z) : env := Eimg (Ereg regs [Z_to_bv 64 e]).
Lemma wc_EA_lo : forall regs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wc_EA regs) n = getr regs r.
Proof.
intros regs n r Hr. pose proof (u5_range r) as R5. unfold wc_EA. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma wc_EB_lo : forall regs e n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (wc_EB regs e) n = getr regs r.
Proof.
intros regs e n r Hr. pose proof (u5_range r) as R5. unfold wc_EB. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma wc_EB_32 : forall regs e, ew (wc_EB regs e) 32 = Z_to_bv 64 e.
Proof. intros regs e. unfold wc_EB. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
Lemma wc_EA_agree : forall regs, env_agree 32 (Ereg regs []) (wc_EA regs).
Proof. intros regs. split; [intros n Hn; unfold wc_EA; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
Lemma wc_EB_agree : forall regs e, env_agree 32 (Ereg regs [Z_to_bv 64 e]) (wc_EB regs e).
Proof. intros regs e. split; [intros n Hn; unfold wc_EB; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.
(* a byte the symbolic state holds as the chunk 0 *)
Lemma wc_rd_zero_loc : forall H (m : word -> option byte) a,
  val_mem SEGS (mrestrict H m) a 1 0 -> aview SEGS H m a = Some 0.
Proof.
intros H m a Hv. pose proof (Hv 0%nat ltac:(lia)) as H0. change (a + Z.of_nat 0) with (a + 0) in H0.
rewrite Z.add_0_r in H0. unfold aview. rewrite H0. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the walk's Section hypotheses, with cgif's names *)
Hypothesis LAWS : AR_laws SEGS B.
(* the memory-checking runtime's memcpy entry, the statement's own hypothesis (LLVMFuzzerTestOneInput_c.v:186) *)
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIG CS___asan_memcpy).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- the seeds ---- *)
Lemma wc_seedA : forall (W : world SEGS) regs mem,
  st_ok_pi SEGS VAL (wc_EA regs) ss_wcA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AW_M)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS WCx [] (wc_EA regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem. split.
- unfold ss_wcA. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold wc_EA. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_nil.
  + apply pairwise_disjoint_of_extents. exact I.
  + split; [exact I | split; exact I].
- unfold sh_ok. apply Forall_nil.
Qed.

Lemma wc_seedB : forall ly S (W : world SEGS) regs mem md text n,
  AR SEGS B ly S W mem md -> In (text, n + 1) (ablocks B ly S) -> 0 <= n ->
  getr regs 9 = w64 LT_SB -> getr regs 24 = w64 text -> getr regs 26 = w64 n ->
  st_ok_pi SEGS VAL (wc_EB regs (text + n)) ss_wcB
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x29c)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS WCx wc_SHB (wc_EB regs (text + n)) (mrestrict (w_H W) mem).
Proof.
intros ly S W regs mem md text n HAR Hin Hn R9 R24 R26.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (al_blocks _ _ LAWS ly S W mem md text (n + 1) HAR Hin) as (_ & Ht4096 & Htceil & Htapp & Htpres & _ & _).
pose proof (req_size_pos (n + 1) ltac:(lia)) as [Hr1 Hr2].
set (E := wc_EB regs (text + n)).
assert (E9 : ew E 9 = Z_to_bv 64 LT_SB) by (subst E; rewrite (wc_EB_lo regs _ 9%nat 9%bv eq_refl); exact R9).
assert (E24 : ew E 24 = Z_to_bv 64 text) by (subst E; rewrite (wc_EB_lo regs _ 24%nat 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = Z_to_bv 64 n) by (subst E; rewrite (wc_EB_lo regs _ 26%nat 26%bv eq_refl); exact R26).
assert (E32 : ew E 32 = Z_to_bv 64 (text + n)) by (subst E; apply wc_EB_32).
assert (U9 : bv_unsigned (ew E 9) = LT_SB) by (rewrite E9; apply unsigned_lit_small; unfold LT_SB; lia).
assert (U24 : bv_unsigned (ew E 24) = text) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = n) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = text + n) by (rewrite E32; apply unsigned_lit_small; lia).
split.
- unfold ss_wcB. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold wc_EB. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold wc_regionsB. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Htpres (text + n + o) ltac:(lia))).
  + apply pairwise_disjoint_of_extents. cbn [wc_regionsB map zpairwise_disjoint zall_disjoint]. repeat split.
  + split; [|split; [exact I|]].
    * cbn [wc_factsB f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U32. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold LT_SB.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
    * cbn [wc_factsB f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U24, U26, U32, !Z.add_0_r.
      rewrite (zcanon_small text) by lia. rewrite (zcanon_small n) by lia. reflexivity.
- unfold sh_ok, wc_SHB. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E WCx 32 (text + n) 1 (text + n) 0 1).
  + exact (range_addressable_of_block SEGS B LAWS ly S W mem md text (n + 1) (text + n) 1 HAR Hin ltac:(lia) ltac:(lia)).
  + unfold U, WCx. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold LT_SB; lia). reflexivity.
  + unfold U. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  + lia.
  + lia.
  + intros x Hx. change (Z.min 0 1) with 0 in Hx. change (Z.max 0 1) with 1 in Hx.
    unfold in_app, kLowShadowBeg in Htapp. rewrite C3 in Htapp. unfold SHADOW_OFF. lia.
Qed.

(* ---- the segment's context, carried to a state whose registers are the callee-saved ones and whose memory
   differs only in text's L0 + 1 bytes and the runtime's stack window below sp ---- *)
Lemma wc_ctx_kept : forall cx q ly S (W : world SEGS) regs mem md k acc text copy arr regs' mem' md',
  aw_ctx B MT cx q ly S W regs mem md k acc -> aw_msgregs cx q regs ->
  aw_rec B cx q ly S W mem (aw_blocks cx q text copy arr) -> aw_wslots cx (rdW W mem) text copy arr ->
  ajournal SEGS B LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S W mem' md' k ->
  aregs_preserved regs regs' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) -> ~ (x_sp1 cx - 4096 <= a < x_sp1 cx) ->
     rdW W mem' a = rdW W mem a) ->
  aw_ctx B MT cx q ly S W regs' mem' md' k acc /\ aw_msgregs cx q regs' /\
  aw_rec B cx q ly S W mem' (aw_blocks cx q text copy arr) /\ aw_wslots cx (rdW W mem') text copy arr.
Proof.
intros cx q ly S W regs mem md k acc text copy arr regs' mem' md' HC HMG HREC HWS HJ' HP HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HC as ((HB0 & (HJ & Hsp & R3 & R4 & HSV) & HSL & R8 & R9 & R22 & Hmq & Hn & Hp & Hr & Hh & Hs) & Hbud).
destruct HMG as (R18 & R19 & R20 & R21 & R27).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
assert (WS : LTOI_STK = 32768) by reflexivity.
rewrite WS in Hslo.
assert (Hs0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
pose proof (proj1 HJ) as HAR.
pose proof HREC as (HRR & Hspill & Hcalls & Hquit & Hq & HPERM).
pose proof (q_L0_U cx q) as HL0U.
assert (HtB : In (text, q_L0 cx q + 1) (aw_blocks cx q text copy arr)) by (rewrite aw_blocks_eq; left; reflexivity).
assert (HtIn : In (text, q_L0 cx q + 1) (ablocks B ly S))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror HtB))))).
destruct (al_blocks _ _ LAWS ly S W mem md text (q_L0 cx q + 1) HAR HtIn) as (_ & Ht4096 & Htceil & _ & _ & _ & _).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (blk_off_imgP B ly S W mem md text (q_L0 cx q + 1) HAR HtIn) as Hoff. unfold off_img in Hoff.
(* the frame [sp, entry sp) keeps its bytes *)
assert (KW : forall a v, x_sp1 cx <= a -> a + 8 <= x_sp0 cx -> rdword (rdW W mem) a = Some v ->
  rdword (rdW W mem') a = Some v).
{ intros a v H1 H2 H. rewrite (rdword_ext (rdW W mem) (rdW W mem') a); [exact H|].
  intros k0 Hk0. apply HK; lia. }
(* the image's statics keep theirs: text is off the image *)
assert (KI : forall a, 0x10000 <= a < 0x606000 -> rdW W mem' a = rdW W mem a) by (intros a Ha; apply HK; lia).
(* the recorder's blocks keep theirs: they are not text *)
pose proof (lt_ablocks_NoDup B LAWS ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup HPERM HND) as HND2.
assert (HtO : ~ In (text, q_L0 cx q + 1) (q_O1 q)).
{ intros Hin. exact (wc_nodup_app_loc _ _ _ HND2 Hin (in_or_app _ _ _ (or_intror HtB))). }
assert (KO : forall a, inFP (ablocks_fp (q_O1 q)) a -> rdW W mem' a = rdW W mem a).
{ intros a (r0 & Hr0 & Hlo & Hhi). unfold ablocks_fp in Hr0. apply in_map_iff in Hr0 as ([p n] & <- & Hpn).
  cbn [fst snd] in Hlo, Hhi.
  assert (HpIn : In (p, n) (ablocks B ly S))
    by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_introl Hpn))).
  assert (Hne : (p, n) <> (text, q_L0 cx q + 1)) by (intros Heq; rewrite Heq in Hpn; exact (HtO Hpn)).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md p n text (q_L0 cx q + 1) HAR HpIn HtIn Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR HpIn) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
  apply HK; lia. }
assert (P : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r)
  by (intros r z Hz Hr0; exact (wc_pres_loc regs regs' r z HP Hz Hr0)).
split.
{ split; [|exact Hbud].
  split; [exact HB0|].
  split.
  { split; [exact HJ'|].
    split; [unfold spZ; rewrite (P 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact Hsp|].
    split; [rewrite (P 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R3|].
    split; [rewrite (P 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R4|].
    intros i r Hi. pose proof (HSV i r Hi) as H.
    assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    cbn [LT_SAVED length] in Hi13.
    refine (KW _ _ _ _ H); lia. }
  split; [intros o v Hin; pose proof (wc_slots_range o v Hin); refine (KW _ _ _ _ (HSL o v Hin)); lia|].
  split; [rewrite (P 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R8|].
  split; [rewrite (P 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R9|].
  split; [rewrite (P 22%bv 22 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R22|].
  split; [exact Hmq|]. split; [exact Hn|]. split; [exact Hp|]. split; [exact Hr|].
  split; [refine (KW _ _ _ _ Hh); unfold LT_HOSTB; lia|].
  refine (KW _ _ _ _ Hs); unfold LT_STATEB; lia. }
split.
{ split; [rewrite (P 18%bv 18 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R18|].
  split; [rewrite (P 19%bv 19 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R19|].
  split; [rewrite (P 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R20|].
  split; [rewrite (P 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R21|].
  rewrite (P 27%bv 27 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R27. }
split.
{ apply (aw_rec_kept B cx q ly S W mem mem' _ HREC).
  intros a [Ha | [Ha | [Ha | Ha]]].
  - apply KI. unfold A_G_REC, REC_SIZE in Ha. lia.
  - apply KI. unfold A_REC_SPILL, SC_SIZE in Ha. lia.
  - apply KI. unfold A_G_QUITTING in Ha. lia.
  - exact (KO a Ha). }
destruct HWS as (W1 & W2 & W3).
split; [refine (KW _ _ _ _ W1); unfold LT_W; lia|].
split; [refine (KW _ _ _ _ W2); unfold LT_W; lia|].
refine (KW _ _ _ _ W3); unfold LT_W; lia.
Qed.

(* ---- segment T: 0x86770 .. 0x867a4 (AW_T) or 0x8680c (AW_J) ---- *)
Lemma aw_seg_T : forall m, (forall j, AW_T_stmt B MT m j) -> AW_J_stmt B MT m -> AW_M_stmt B MT m.
Proof.
intros m HT HJm. unfold AW_M_stmt.
intros cx q ly S W regs mem md k acc text copy arr Hm HFRM HC HMG HREC HMSG HWS R24 R23 R25 R10 R26.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS : LTOI_STK = 32768) by reflexivity.
pose proof HC as ((HB0 & (HJ & Hsp & R3 & R4 & HSV) & HSL & R8 & R9 & R22 & Hmq & Hn & Hp & Hr & Hh & Hs) & Hbud).
pose proof HMG as (R18 & R19 & R20 & R21 & R27).
pose proof HB0 as (HPRE & _).
pose proof HPRE as (_ & _ & _ & Hgp & Htp & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
rewrite WS in Hslo.
assert (Hs0 : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47) by (unfold x_sp0; lia).
assert (Hs1 : x_sp1 cx = x_sp0 cx - 256) by (unfold x_sp1, x_sp0, LT_FRAME; lia).
pose proof (proj1 HJ) as HAR.
pose proof HREC as (HRR & Hspill & Hcalls & Hquit & Hq & HPERM).
(* the model: L0 = |U|, U a prefix of the message D, D inside the payload block *)
pose proof (q_L0_U cx q) as HL0U.
assert (HUf : q_U cx q = firstn (length (q_U cx q)) (q_D cx q))
  by (unfold q_U, Verbs.upto0; apply SlotWords.sw_upto_prefix).
assert (HUD : (length (q_U cx q) <= length (q_D cx q))%nat)
  by (pose proof (f_equal (@length byte) HUf) as HL; rewrite length_firstn in HL; lia).
pose proof (lt_len_range (x_pl cx) (x_n cx) (q_r q) ltac:(lia)) as HLR.
assert (HDl : Z.of_nat (length (q_D cx q)) <= lt_len (x_pl cx) (x_n cx) (q_r q))
  by (unfold q_D, lt_D; rewrite length_firstn; lia).
assert (Hhdr : 0 < SlotSpec.hdr_n (q_r q) <= q_r q) by (unfold SlotSpec.hdr_n; lia).
assert (Hsrc : q_src cx q = x_p cx + (x_n cx - q_r q) + SlotSpec.hdr_n (q_r q)) by reflexivity.
assert (HL0r : 0 <= q_L0 cx q < 2 ^ 32) by lia.
(* the blocks: text is made since the entry, the payload is the entry's; they are apart *)
assert (HtB : In (text, q_L0 cx q + 1) (aw_blocks cx q text copy arr)) by (rewrite aw_blocks_eq; left; reflexivity).
assert (HtIn : In (text, q_L0 cx q + 1) (ablocks B ly S))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_intror HtB))))).
assert (HpIn : In (x_p cx, x_n cx) (ablocks B ly S))
  by exact (Permutation_in _ (Permutation_sym HPERM) (in_or_app _ _ _ (or_intror (in_or_app _ _ _ (or_introl Hp))))).
pose proof (lt_ablocks_NoDup B LAWS ly S W mem md HAR) as HND.
pose proof (Permutation_NoDup HPERM HND) as HND2.
assert (Htnot : ~ In (text, q_L0 cx q + 1) (x_bl0 B cx)).
{ intros Hin. exact (wc_nodup_app_loc _ _ _ (wc_nodup_app_r_loc _ _ HND2) Hin HtB). }
assert (Hne : (text, q_L0 cx q + 1) <> (x_p cx, x_n cx)) by (intros Heq; apply Htnot; rewrite Heq; exact Hp).
pose proof (sep_blocks SEGS B LAWS ly S W mem md text (q_L0 cx q + 1) (x_p cx) (x_n cx) HAR HtIn HpIn Hne) as Hdisj.
unfold zdisjoint in Hdisj. cbn [fst snd] in Hdisj.
destruct (al_blocks _ _ LAWS ly S W mem md text (q_L0 cx q + 1) HAR HtIn) as (_ & Ht4096 & Htceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md (x_p cx) (x_n cx) HAR HpIn) as (_ & Hp4096 & Hpceil & _ & _ & _ & _).
pose proof (req_size_pos (q_L0 cx q + 1) ltac:(lia)) as [Hrq1 Hrq2].
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [Hrp1 Hrp2].
pose proof (blk_off_imgP B ly S W mem md text (q_L0 cx q + 1) HAR HtIn) as Hoff. unfold off_img in Hoff.
(* 0x86770 .. 0x8677c: a0 = text, a1 = the message, a2 = L0, jal __asan_memcpy *)
destruct (wc_seedA W regs mem) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (wc_EA regs)) by (unfold wc_EA; apply Eimg_env).
pose proof (wc_EA_agree regs) as HAE.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (wc_EA regs) n = getr regs rr)
  by (intros n rr Hrr; exact (wc_EA_lo regs n rr Hrr)).
remember (wc_EA regs) as E eqn:HE. clear HE.
paj_run_tok RUN HS HJ SHOK WCspan.
{ awr_ok_tac. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv1 := d) in *; clearbody mdv1 end.
(* the stretch writes no memory *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha. apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin. destruct Hin. }
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
pose proof (aregs_preserved_of_st_ok SEGS _ E _ _ regs [] HS HAE ltac:(vm_compute; reflexivity)) as HPA.
cbn [ms_regs restrict] in HPA.
rename ms into msA.
assert (PA : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs msA) r = getr regs r)
  by (intros r z Hz Hr0; exact (wc_pres_loc regs (ms_regs msA) r z HPA Hz Hr0)).
assert (HspT : spZ (ms_regs msA) = x_sp0 cx + -256).
{ unfold spZ at 1. rewrite (PA 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)).
  change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Hsp, Hs1. lia. }
assert (P3' : getr (ms_regs msA) 3 = w64 (as_gp B))
  by (rewrite (PA 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R3; exact Hgp).
assert (P4' : getr (ms_regs msA) 4 = w64 (as_tp B))
  by (rewrite (PA 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), R4; exact Htp).
assert (P10' : getr (ms_regs msA) 10 = w64 text) by (rewrite P10, (EEo 24%nat 24%bv eq_refl); exact R24).
assert (P11' : getr (ms_regs msA) 11 = w64 (q_src cx q)) by (rewrite P11, (EEo 20%nat 20%bv eq_refl); exact R20).
assert (P12' : getr (ms_regs msA) 12 = w64 (q_L0 cx q)) by (rewrite P12, (EEo 26%nat 26%bv eq_refl); exact R26).
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 668))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (proj1 HJ) as HAR1.
destruct (al_blocks _ _ LAWS ly S W (ms_mem msA) mdv1 (x_p cx) (x_n cx) HAR1 HpIn) as (_ & _ & _ & _ & Hppres1 & _ & _).
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG CS___asan_memcpy) AMEMCPY W (ms_regs msA) (ms_mem msA)
    LTOI_STK (x_sp0 cx) cmd_PG (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [] ly S mdv1 k
    text (q_src cx q) (q_L0 cx q) (-256) (Z_to_bv 64 (BASE + 668))
    HJ P10' P11' P12' HL0r ltac:(lia) ltac:(lia) HspT eq_refl ltac:(lia) ltac:(rewrite Hes, WS; lia) P3' P4' P1 HraT).
  - intros a Ha. split.
    + right; right; left. exists text, (q_L0 cx q + 1). split; [exact HtIn | split; [exact Htnot | lia]].
    + rewrite Hes. lia.
  - intros a Ha (r0 & Hr0 & Hlo & Hhi). exfalso. unfold cmd_PG in Hr0. cbn [In] in Hr0.
    destruct Hr0 as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hlo, Hhi; unfold A_G_REC, A_REC_SPILL, A_G_QUITTING in *; lia.
  - exact (amem_range_of_block SEGS B LAWS ly S W mem md text (q_L0 cx q + 1) text (q_L0 cx q) HAR HtIn ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 text (q_L0 cx q + 1) text (q_L0 cx q)
      HAR1 HtIn ltac:(lia) ltac:(lia)).
  - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 text (q_L0 cx q + 1) text (q_L0 cx q)
      HAR1 HtIn ltac:(lia) ltac:(lia) Hpos).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent SEGS). exact (proj1 (Hppres1 a ltac:(lia))).
      - rewrite HspT, Hes. lia. }
    split; [lia|].
    split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md (x_p cx) (x_n cx) (q_src cx q) (q_L0 cx q) HAR HpIn
              ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 (x_p cx) (x_n cx) (q_src cx q)
              (q_L0 cx q) HAR1 HpIn ltac:(lia) ltac:(lia))|].
    intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msA) mdv1 (x_p cx) (x_n cx) (q_src cx q)
      (q_L0 cx q) HAR1 HpIn ltac:(lia) ltac:(lia) Hpos). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
(* back at 0x86780 *)
assert (HP12 : aregs_preserved regs regs2) by exact (aregs_preserved_trans _ _ _ HPA HP2).
assert (P2 : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr regs r)
  by (intros r z Hz Hr0; exact (wc_pres_loc regs regs2 r z HP12 Hz Hr0)).
assert (R9b : getr regs2 9 = w64 LT_SB)
  by (rewrite (P2 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R9).
assert (R24b : getr regs2 24 = w64 text)
  by (rewrite (P2 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R24).
assert (R26b : getr regs2 26 = w64 (q_L0 cx q))
  by (rewrite (P2 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R26).
pose proof (proj1 HJ2) as HAR2.
clear HS SHOK.
destruct (wc_seedB ly S W regs2 mem2 md2 text (q_L0 cx q) HAR2 HtIn ltac:(lia) R9b R24b R26b) as [HS SHOK].
assert (HEIB : img_env VAL A_LIM (wc_EB regs2 (text + q_L0 cx q))) by (unfold wc_EB; apply Eimg_env).
pose proof (wc_EB_agree regs2 (text + q_L0 cx q)) as HAEB.
assert (EEoB : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (wc_EB regs2 (text + q_L0 cx q)) n = getr regs2 rr)
  by (intros n rr Hrr; exact (wc_EB_lo regs2 _ n rr Hrr)).
assert (E32u : bv_unsigned (ew (wc_EB regs2 (text + q_L0 cx q)) 32) = text + q_L0 cx q)
  by (rewrite wc_EB_32; apply unsigned_lit_small; lia).
remember (wc_EB regs2 (text + q_L0 cx q)) as EB eqn:HEB. clear HEB.
(* 0x86780 .. 0x86798: a0 = text + L0, its 1-byte check (a token), text[L0] = 0, then beqz s10 *)
paj_run_tok RUN HS HJ2 SHOK WCspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  eapply awr_ok_cons_gen; [reflexivity | exact E32u | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
  right; right; left. exists text, (q_L0 cx q + 1). split; [exact HtIn | split; [exact Htnot | lia]]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv3 := d) in *; clearbody mdv3 end.
(* the stretch writes text[L0] only *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (text + q_L0 cx q <= a < text + q_L0 cx q + 1) ->
  rdW W (ms_mem ms) a = rdW W mem2 a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => text + q_L0 cx q <= a < text + q_L0 cx q + 1) HFr);
    [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | []]. injection Hq0 as <- <- <-. cbn [base_val] in Hrr. rewrite E32u in Hrr. lia. }
clear HF HFr HG.
rename ms into msB.
lazymatch type of HS with st_ok_pi _ _ ?E4 _ _ =>
  assert (U26 : U E4 (SOff 26 0) = q_L0 cx q)
    by (apply U_atom; [cbn [ew ewset Nat.eqb]; rewrite (EEoB 26%nat 26%bv eq_refl); exact R26b | lia]);
  assert (E32u' : bv_unsigned (ew E4 32) = text + q_L0 cx q) by (cbn [ew ewset Nat.eqb]; exact E32u);
  assert (HAE4 : env_agree 32 (Ereg regs2 [Z_to_bv 64 (text + q_L0 cx q)]) E4)
end.
{ pose proof HAEB as [HA1 HA2]. split.
  - intros n Hn32. cbn [ew ewset].
    repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [lia|] end.
    exact (HA1 n Hn32).
  - cbn [ed ewset]. exact HA2. }
(* the text bytes after the copy *)
assert (HCOPY0 : forall i, 0 <= i < q_L0 cx q -> rdW W (ms_mem msB) (text + i) = rdW W mem (q_src cx q + i)).
{ intros i Hi. rewrite (KB (text + i) ltac:(lia) ltac:(lia)), (HCPY i Hi). exact (KA (q_src cx q + i) ltac:(lia)). }
assert (KAB : forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) -> ~ (x_sp1 cx - 4096 <= a < x_sp1 cx) ->
  rdW W (ms_mem msB) a = rdW W mem a).
{ intros a Ha H1 H2. rewrite (KB a Ha ltac:(lia)), (HKC a Ha ltac:(lia) ltac:(rewrite Hes; lia)). exact (KA a Ha). }
psrr_branch_tok RUN BR HS SHOK WCspan.
- (* L0 = 0: 0x86808 li a2,1, on to 0x8680c *)
  assert (HL0z : q_L0 cx q = 0).
  { rewrite branch_eq_U, U26, U_SLit in Hc. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ2 SHOK WCspan 0x328.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact E32u' | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; left. exists text, (q_L0 cx q + 1). split; [exact HtIn | split; [exact Htnot | lia]]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv4 := d) in *; clearbody mdv4 end.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (text + q_L0 cx q <= a < text + q_L0 cx q + 1) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem msB) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => text + q_L0 cx q <= a < text + q_L0 cx q + 1) HFr);
      [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | []]. injection Hq0 as <- <- <-. cbn [base_val] in Hrr. rewrite E32u' in Hrr. lia. }
  assert (HZ : rdW W (ms_mem ms) (text + q_L0 cx q) = Some 0).
  { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
    pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR3.
    pose proof (region_ok_chunk SEGS _ _ _ _ HR3 (in_eq _ _)) as HCk.
    cbn [YP09.r_base YP09.r_chunks base_val] in HCk. rewrite E32u' in HCk.
    pose proof (val_of_chunk_ok SEGS _ _ _ 0 1 (SLit 0) 0 HCk eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
    rewrite Z.add_0_r in HV. exact (wc_rd_zero_loc _ _ _ HV). }
  pmkst HS.
  prreg HS (12%bv : bv 5) F12.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [Z_to_bv 64 (text + q_L0 cx q)] HS HAE4
    ltac:(vm_compute; reflexivity)) as HPB.
  cbn [ms_regs restrict] in HPB.
  assert (HPall : aregs_preserved regs (ms_regs ms)) by exact (aregs_preserved_trans _ _ _ HP12 HPB).
  assert (PF : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs ms) r = getr regs r)
    by (intros r z Hz Hr0; exact (wc_pres_loc regs (ms_regs ms) r z HPall Hz Hr0)).
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) ->
    ~ (x_sp1 cx - 4096 <= a < x_sp1 cx) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite (KC a Ha ltac:(lia)). exact (KAB a Ha H1 H2). }
  assert (HCOPY' : forall i, 0 <= i < Z.of_nat (length (q_U cx q)) ->
    rdW W (ms_mem ms) (text + i) = rdW W mem (q_src cx q + i)).
  { intros i Hi. rewrite <- HL0U in Hi. rewrite (KC (text + i) ltac:(lia) ltac:(lia)). exact (HCOPY0 i Hi). }
  pose proof (wc_text_bytes_loc (rdW W mem) (rdW W (ms_mem ms)) text (q_src cx q) (q_D cx q) (length (q_U cx q))
    HMSG HUD HCOPY' ltac:(rewrite <- HL0U; exact HZ)) as HTB.
  rewrite <- HUf in HTB.
  destruct (wc_ctx_kept cx q ly S W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv4
    HC HMG HREC HWS HJ2 HPall KALL) as (HC' & HMG' & HREC' & HWS').
  assert (F24 : getr (ms_regs ms) 24 = w64 text)
    by (rewrite (PF 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R24).
  assert (F23 : getr (ms_regs ms) 23 = w64 copy)
    by (rewrite (PF 23%bv 23 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R23).
  assert (F25 : getr (ms_regs ms) 25 = w64 arr)
    by (rewrite (PF 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R25).
  assert (F26 : getr (ms_regs ms) 26 = w64 (q_L0 cx q))
    by (rewrite (PF 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R26).
  assert (HU0 : q_U cx q = []) by (apply length_zero_iff_nil; lia).
  assert (HLN : q_LN cx q = []) by (change (q_LN cx q) with (Verbs.trim (q_U cx q)); rewrite HU0; reflexivity).
  assert (HTX : exists T, abytes_atR (rdW W (ms_mem ms)) text T /\ length T = Z.to_nat (q_L0 cx q + 1) /\
    firstn (length (q_LN cx q) + 1) T = q_LN cx q ++ [Z_to_bv 8 0]).
  { exists (q_U cx q ++ [Z_to_bv 8 0]). split; [exact HTB|]. split.
    - rewrite length_app. cbn [length]. rewrite HL0U. lia.
    - rewrite HLN, HU0. reflexivity. }
  assert (F12' : getr (ms_regs ms) 12 = w64 (Z.of_nat (length (q_LN cx q)) + 1)) by (rewrite F12, HLN; reflexivity).
  assert (F26' : getr (ms_regs ms) 26 = w64 (Z.of_nat (length (q_LN cx q)))) by (rewrite F26, HLN, HL0z; reflexivity).
  exact (HJm cx q ly S W (ms_regs ms) (ms_mem ms) mdv4 k acc text copy arr Hm HFRM HC' HMG' HREC' HWS' F24 F23 F25
    HTX F12' F26').
- (* L0 <> 0: 0x8679c a1 = a0 = text + L0 - 1, on to the trim loop's head *)
  assert (HL0nz : q_L0 cx q <> 0).
  { rewrite branch_eq_U, U26, U_SLit in Hc. apply Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ2 SHOK WCspan 0x2c0.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    eapply awr_ok_cons_gen; [reflexivity | exact E32u' | | apply awr_ok_nil].
    intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; left. exists text, (q_L0 cx q + 1). split; [exact HtIn | split; [exact Htnot | lia]]. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (mdv4 := d) in *; clearbody mdv4 end.
  assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (text + q_L0 cx q <= a < text + q_L0 cx q + 1) ->
    rdW W (ms_mem ms) a = rdW W (ms_mem msB) a).
  { intros a Ha Hna.
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => text + q_L0 cx q <= a < text + q_L0 cx q + 1) HFr);
      [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | []]. injection Hq0 as <- <- <-. cbn [base_val] in Hrr. rewrite E32u' in Hrr. lia. }
  assert (HZ : rdW W (ms_mem ms) (text + q_L0 cx q) = Some 0).
  { pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
    pose proof (mem_ok_region SEGS _ _ _ _ HM (in_eq _ _)) as HR3.
    pose proof (region_ok_chunk SEGS _ _ _ _ HR3 (in_eq _ _)) as HCk.
    cbn [YP09.r_base YP09.r_chunks base_val] in HCk. rewrite E32u' in HCk.
    pose proof (val_of_chunk_ok SEGS _ _ _ 0 1 (SLit 0) 0 HCk eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
    rewrite Z.add_0_r in HV. exact (wc_rd_zero_loc _ _ _ HV). }
  pmkst HS.
  prreg HS (10%bv : bv 5) F10. prreg HS (11%bv : bv 5) F11.
  pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [Z_to_bv 64 (text + q_L0 cx q)] HS HAE4
    ltac:(vm_compute; reflexivity)) as HPB.
  cbn [ms_regs restrict] in HPB.
  assert (HPall : aregs_preserved regs (ms_regs ms)) by exact (aregs_preserved_trans _ _ _ HP12 HPB).
  assert (PF : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr (ms_regs ms) r = getr regs r)
    by (intros r z Hz Hr0; exact (wc_pres_loc regs (ms_regs ms) r z HPall Hz Hr0)).
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (text <= a < text + q_L0 cx q + 1) ->
    ~ (x_sp1 cx - 4096 <= a < x_sp1 cx) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha H1 H2. rewrite (KC a Ha ltac:(lia)). exact (KAB a Ha H1 H2). }
  assert (HCOPY' : forall i, 0 <= i < Z.of_nat (length (q_U cx q)) ->
    rdW W (ms_mem ms) (text + i) = rdW W mem (q_src cx q + i)).
  { intros i Hi. rewrite <- HL0U in Hi. rewrite (KC (text + i) ltac:(lia) ltac:(lia)). exact (HCOPY0 i Hi). }
  pose proof (wc_text_bytes_loc (rdW W mem) (rdW W (ms_mem ms)) text (q_src cx q) (q_D cx q) (length (q_U cx q))
    HMSG HUD HCOPY' ltac:(rewrite <- HL0U; exact HZ)) as HTB.
  rewrite <- HUf in HTB.
  destruct (wc_ctx_kept cx q ly S W regs mem md k acc text copy arr (ms_regs ms) (ms_mem ms) mdv4
    HC HMG HREC HWS HJ2 HPall KALL) as (HC' & HMG' & HREC' & HWS').
  assert (F24 : getr (ms_regs ms) 24 = w64 text)
    by (rewrite (PF 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R24).
  assert (F23 : getr (ms_regs ms) 23 = w64 copy)
    by (rewrite (PF 23%bv 23 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R23).
  assert (F25 : getr (ms_regs ms) 25 = w64 arr)
    by (rewrite (PF 25%bv 25 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact R25).
  assert (F26' : getr (ms_regs ms) 26 = w64 (Z.of_nat (length (q_U cx q))))
    by (rewrite (PF 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), <- HL0U; exact R26).
  assert (Hj : (1 <= length (q_U cx q) <= length (q_U cx q))%nat) by lia.
  assert (Htrim : Verbs.trim (q_U cx q) = Verbs.trim (firstn (length (q_U cx q)) (q_U cx q)))
    by (rewrite firstn_all; reflexivity).
  assert (HTZ : abytes_atR (rdW W (ms_mem ms)) text (SlotWordsRun.tz (q_U cx q) (length (q_U cx q))))
    by (rewrite SlotWordsRun.tz_full; exact HTB).
  assert (F10' : getr (ms_regs ms) 10 = w64 (text + Z.of_nat (length (q_U cx q)) - 1))
    by (rewrite F10, E32u, <- HL0U; unfold w64; f_equal; lia).
  assert (F11' : getr (ms_regs ms) 11 = w64 (text + Z.of_nat (length (q_U cx q)) - 1))
    by (rewrite F11, E32u, <- HL0U; unfold w64; f_equal; lia).
  exact (HT (length (q_U cx q)) cx q ly S W (ms_regs ms) (ms_mem ms) mdv4 k acc text copy arr Hm HFRM HC' HMG' HREC' HWS'
    F24 F23 F25 Hj Htrim HTZ F10' F11' F26').
Qed.

End e.
End f.
End d.
