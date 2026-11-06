(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s1.v, with its module names changed; 326 of its 371 lines of code are new or changed and 521 lines of the source are left out. *)
(* Segment Tb of the walk of pin_set_words on the ASan build of plugin-hostd/fuzz_command (interface:
   lib/A/Prog/pin_set_words_s4.v): from K2 (0x8e784, pins_set has returned rc in a0) to the `ret`.

     0x8e784  mv s1,a0
     0x8e788  bnez a0,0x8e794                 rc <> 0: the epilogue returns rc
     0x8e78c  jal lv2_refusals_forget          rc = 0: lv2_refusals_forget(NULL) (a0 = rc = 0)
     0x8e790  li s1,0
     0x8e794  mv a0,s1; ld ra..s4; addi sp,sp,48
     0x8e7b4  ret

   The symbolic state at K2 and after the call is psw_seedJ's (registers as atoms, the saved words in a read-only
   frame region), so no run writes memory (frame_of_read_only). The call goes through the kit's cl_callS_pg
   (PaCallPg.v) with the callee's statement (Section hypothesis LV2_REFUSALS_FORGET); its premises at K2 come from
   INV_K2 (pins_set's post and the journal from the entry) and pin_set_words' own premises (psw_pre). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain PaCallPg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecBase CmdRecRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import xstrdup_c hand_back_c answer_code_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pin_set_words_s1 pin_set_words_s2 pin_set_words_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import pin_set_words_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the model side: pins_set records at most one call; with fewer than 16 calls record() takes no spill slot *)
Lemma tb_calls_pins_set : forall R u f l v,
  (length (r_calls (fst (pins_set_m R u f l v))) <= S (length (r_calls R)))%nat.
Proof.
intros R u f l v.
unfold pins_set_m, rec_stub_code, rec_answer_code, rec_mix, rec_record, set_state, set_answer, set_calls, set_spill.
destruct (Nat.ltb _ 16); cbn [r_calls r_refuse r_code fst]; destruct (_ =? 0); cbn [r_calls fst];
rewrite ?length_app; cbn [length]; lia.
Qed.
Lemma tb_rsf0 : forall R, (length (r_calls R) < 16)%nat -> rec_spill_frees R = 0.
Proof. intros R H. unfold rec_spill_frees. destruct (Nat.ltb_spec (length (r_calls R)) 16); [reflexivity | lia]. Qed.

(* the live bytes of both recorder calls fit in pin_set_words' own bound *)
Lemma tb_live_bound : forall (R : rstate) (u f l : list byte) (v : option (list byte)),
  (length u <= 8192)%nat -> (length f <= 8192)%nat -> (length l <= 8192)%nat ->
  (forall x, v = Some x -> (length x <= 8192)%nat) ->
  LIVE_PINS_SET R (Some u) (Some f) (Some l) v + LIVE_LV2_REFUSALS_FORGET None <= LIVE_PIN_SET_WORDS.
Proof.
intros R u f l v Hu Hf Hl Hv.
apply psw3_nat8192 in Hu. apply psw3_nat8192 in Hf. apply psw3_nat8192 in Hl.
unfold LIVE_LV2_REFUSALS_FORGET, LIVE_PINS_SET, LIVE_PIN_SET_WORDS, LIVE_ANSWER_CODE, LIVE_HAND_BACK, LIVE_XSTRDUP,
  PIN_SET_WORDS_MALLOCS, PIN_SET_WORDS_REQ.
match goal with |- context [resp ?c] => pose proof (psw3_resp_len c) as Hr end.
assert (Hd : Z.of_nat (length (darg v (bstr "-"%string))) <= 8192).
{ destruct v as [x|]; cbn [darg]; [exact (psw3_nat8192 _ (Hv x eq_refl)) | rewrite psw3_len_dash; lia]. }
rewrite psw3_len_star. cbn [sarg]. lia.
Qed.

(* a value of rc in [-2^31, 2^31) that is 0 modulo 2^64 is 0 *)
Lemma tb_mod64_zero : forall r, -2^31 <= r < 2^31 -> r mod 2^64 = 0 -> r = 0.
Proof.
intros r Hr H. destruct (Z_lt_le_dec r 0) as [Hn|Hp].
- rewrite <- (Z_mod_plus_full r 1 (2^64)) in H. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.

(* a literal register name and its Z_to_bv form name the same register *)
Lemma tb_LT : forall (b : bv 5) z, bv_unsigned b = z -> Z_to_bv 5 z = b.
Proof.
intros b z Hbz. apply bv_eq. rewrite <- Hbz, Z_to_bv_unsigned. unfold bv_wrap.
apply Z.mod_small. exact (bv_unsigned_in_range 5 b).
Qed.
Lemma tb_kept1 : forall (regsa regsb : bvmap 5 word) (b : bv 5) z, bv_unsigned b = z ->
  getr regsa (Z_to_bv 5 z) = getr regsb (Z_to_bv 5 z) -> getr regsa b = getr regsb b.
Proof. intros regsa regsb b z Hz H. rewrite <- (tb_LT b z Hz). exact H. Qed.

(* the six saved words, through a reader that agrees on the frame *)
Lemma tb_saved_kept : forall regs (rd rd' : reader),
  (forall x, spZ regs - 48 <= x < spZ regs -> rd' x = rd x) -> psw_saved regs rd -> psw_saved regs rd'.
Proof.
intros regs rd rd' HK (S1 & S8 & S9 & S18 & S19 & S20).
assert (G : forall o v, 8 <= o <= 48 -> aval_mem rd (spZ regs - o) 8 v -> aval_mem rd' (spZ regs - o) 8 v).
{ intros o v Ho Hv. apply (aval_mem_kept_r rd rd' _ 8 v); [|exact Hv].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK. lia. }
exact (conj (G 8 _ ltac:(lia) S1) (conj (G 16 _ ltac:(lia) S8) (conj (G 24 _ ltac:(lia) S9)
  (conj (G 32 _ ltac:(lia) S18) (conj (G 40 _ ltac:(lia) S19) (G 48 _ ltac:(lia) S20)))))).
Qed.

Ltac tb_in := cbn [In]; repeat (first [left; reflexivity | right]).
(* the seed's only region is read-only: every run writes nothing *)
Ltac tb_awr := lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ =>
  let rs' := eval vm_compute in rs in change rs with rs' end;
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
(* a symbolic run from a psw_seedJ state; afterwards the model is named mdv, the machine state ms', and Hm says the
   memory is the one before the run *)
Ltac tb_run RUNP RUNC HS HJ ms' mdv Hm :=
  paj_run_shc RUNP RUNC HS HJ;
  [ tb_awr
  | lazymatch goal with |- SRr _ _ (mkCfg ?m ?d) _ => rename m into ms'; set (mdv := d) in *; clearbody mdv end;
    lazymatch goal with HF0 : frame_of _ ?rs _ (ms_mem ms') |- _ =>
      let Hro := fresh "Hro" in assert (Hro : rs_read_only rs = true) by (vm_compute; reflexivity);
      pose proof (frame_of_read_only _ _ _ _ Hro HF0) as Hm; clear Hro end;
    repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end ].

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma tb_EJ_reg : forall (regs1 regs : bvmap 5 word) p1 p2 p4 n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (EJ regs1 regs p1 p2 p4) n = getr regs1 r.
Proof. intros regs1 regs p1 p2 p4 n r Hn. unfold EJ. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis LV2_REFUSALS_FORGET : tlv2_refusals_forget_spec B MT.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (L := cmd_listing) (PI := PI).

(* arodata_okP through a journal whose footprint holds no read-only byte (CmdBase.v's arodata_ok_journalP, with
   the image facts of IMG) *)
Lemma tb_aro : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  (forall a, in_roP SEGS CMD_RLO CMD_RHI a -> ~ inFP FP a) ->
  arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He | ].
- destruct Hro as [(s & Hs & _ & Hr) | Hg]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img _ _ IMG a Hg)].
- apply fp_spares_off; [| exact (HFP a Hro)]. pose proof (cif_ro_below_ofl _ _ IMG a Hro) as Hb. unfold AOFL_HEAD. lia.
Qed.

Theorem psw_Tb : forall c, psw_pre B MT c -> from_K2 B MT c.
Proof using TL HB IMG MTL SIGP LV2_REFUSALS_FORGET.
intros c HP. unfold from_K2. intros ly2 S2 W2 regs2 mem2 md2 HK.
destruct HK as (u & f & l & v & R1 & r & O1 & HJ & HSV & Q2 & Q3 & Q4 & Q8 & Q20 & Qhi & Q10 & Hm & Hu & Hf & Hl & Hv
  & Hps & Hr & Hrec1 & HO1 & Hsurv1 & Hall1 & Hlive1 & Hmo1).
destruct HP as [HAFN HROD0 HA0 HL64 HA1 HT64 HA2 HLB HLO HLT HLN HTOBJ HTOKS HCB HCBO HNTOK HNTOKR HVERB HREC0
  HREFUSE HCALLS HRO0 HVOBJS HFRAMES HNEV HLIVE HMETER].
pose proof HAFN as (HAR0 & Hra & Hra40 & Hgp & Htp & Hstk & Hpres0 & Hch0 & HQT0).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTKb : 48 + LV2_REFUSALS_FORGET_STK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_r (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)).
  pose proof (Z.le_max_r PINS_SET_STK LV2_REFUSALS_FORGET_STK). lia. }
assert (HLS0 : 0 <= LV2_REFUSALS_FORGET_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (H48 : 48 <= spZ (x_regs c)) by lia.
(* the token array: in a side-stack frame below the allocator's ceiling *)
destruct HTOBJ as ((cid & pos & Hfr & Hcid & Hfal & Hflo & Hfhi) & Htok8 & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hfr) as (Hf0 & Hfc & _).
assert (Htok : 4096 <= x_tok c < 140737479966720) by lia.
assert (Htokc : x_tok c < alloc_ceiling) by lia.
(* the recorder's spill slot stays unused across both calls *)
assert (Hsf0 : rec_spill_frees (x_R c) = 0) by (apply tb_rsf0; lia).
assert (Hsf1 : rec_spill_frees R1 = 0).
{ pose proof (tb_calls_pins_set (x_R c) (Some u) (Some f) (Some l) v) as Hc1. rewrite Hps in Hc1. cbn [fst] in Hc1.
  apply tb_rsf0. lia. }
(* the entry's footprint lies below the allocator's ceiling and holds no read-only byte *)
assert (HFPlow : forall a, inFP (psw_FP c) a -> a < alloc_ceiling).
{ intros a Ha. unfold psw_FP, PIN_SET_WORDS_PG in Ha. apply inFP_app in Ha as [Ha|Ha].
  - apply inFP_cons in Ha as [G|Ha]; [unfold A_G_REC, REC_SIZE in G; lia|].
    apply inFP_cons in Ha as [G|Ha]; [unfold A_REC_SPILL, SC_SIZE in G; lia | exact (False_ind _ (inFP_nil a Ha))].
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hrg).
    destruct (al_blocks SEGS B LAWS _ _ _ _ _ p n HAR0 (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn)) as (_ & _ & Hc & _).
    lia. }
assert (HFPro : forall a, in_roP SEGS CMD_RLO CMD_RHI a -> ~ inFP (psw_FP c) a).
{ intros a Hro Ha. unfold psw_FP, PIN_SET_WORDS_PG in Ha. apply inFP_app in Ha as [Ha|Ha].
  - apply (cif_prog_not_ro _ _ IMG a); [|exact Hro]. unfold cmd_PG.
    apply inFP_cons in Ha as [G|Ha]; [apply inFP_cons; left; unfold REC_SIZE in G; exact G|].
    apply inFP_cons in Ha as [G|Ha];
      [apply inFP_cons; right; apply inFP_cons; left; unfold SC_SIZE in G; exact G | exact (False_ind _ (inFP_nil a Ha))].
  - destruct (inFP_ablocks_fp_inv _ a Ha) as (p & n & Hpn & Hrg).
    apply (blk_img SEGS B LAWS _ _ _ _ _ p n a HAR0 (rec_repA_in_blocks B _ _ _ _ _ _ HREC0 Hpn) Hrg).
    destruct Hro as [(s & Hs & _ & Hr') | Hg]; [exists s; split; [exact Hs | exact Hr'] | exact (cif_relro_img _ _ IMG a Hg)]. }
(* the seed at K2 *)
pose proof (psw_seedJ (x_ly c) W2 mem2 (x_regs c) regs2 PSW_K2 (x_tok c) 0 0 0 Hstk HSV Q2 Q8 Q20 Htok Htok8
  ltac:(lia) ltac:(lia) ltac:(lia)) as HS.
set (E := EJ regs2 (x_regs c) 0 0 0) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EJ; apply Eimg_env).
assert (HAG : env_agree 41 (EJ regs2 (x_regs c) 0 0 0) E) by (subst E; split; [intros; reflexivity | reflexivity]).
assert (HAE : env_agree 32 (Ereg regs2 (psw_extraJ (x_regs c) 0 0 0)) E).
{ subst E. unfold EJ. split; [intros kk Hkk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. }
assert (E10 : ew E 10%nat = w64 r)
  by (subst E; rewrite (tb_EJ_reg regs2 (x_regs c) 0 0 0 10%nat 10%bv eq_refl); exact Q10).
clearbody E.
(* 0x8e784 mv s1,a0; 0x8e788 bnez a0 *)
tb_run RUNP RUNC HS HJ msA mdA Hm0.
psrr_branch_pi RUNP BR HS.
- (* rc <> 0: 0x8e794 mv a0,s1; the epilogue; ret *)
  assert (Hrc0 : r <> 0).
  { intros ->. rewrite branch_ne_U in Hc. rewrite U_SOff, E10, Z.add_0_r in Hc.
    change (U E (SLit 0)) with 0 in Hc. vm_compute in Hc. discriminate Hc. }
  assert (Hr0 : (r =? 0) = false) by (apply Z.eqb_neq; exact Hrc0).
  clear Hc.
  tb_run RUNP RUNC HS HJ msB mdB Hm1.
  destruct (psw_aregs_leaf (x_regs c) regs2 0 0 0 E _ (w_H W2) msB HS HAG ltac:(vm_compute; reflexivity)
    Q2 Q3 Q4 Qhi H48) as [Hra1 Haregs].
  prreg HS (10%bv : bv 5) Q10e.
  assert (Hk : EV_PINS_SET (x_R c) <= EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c))).
  { rewrite (psw_ev_split (x_R c) R1 u f l v r (x_T c) (tl (x_tks c)) Hm Hps), Hr0. cbv iota. lia. }
  eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) _ _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (psw_leaf_post B MT c W2 (ms_regs msB) (ms_mem msB) mdB ly2 S2 (EV_PINS_SET (x_R c)) Hra Hra1 Haregs HJ Hk mat').
  unfold psw_Q. rewrite (psw_run_set (x_R c) (x_T c) (tl (x_tks c)) u f l v R1 r Hm Hps), Hr0. cbv beta iota.
  exists O1.
  split; [rewrite Q10e, E10; reflexivity|].
  split; [exact Hr|].
  split; [rewrite Hm1, Hm0; exact Hrec1|].
  split; [exact Hsurv1|]. split; [exact Hall1|]. split; [exact HO1|].
  split; [pose proof (psw_live_bound (x_R c) u f l v (x_T c) (tl (x_tks c)) Hm Hu Hf Hl Hv); lia|].
  apply (mle_weaken MT _ _ _ _ MTL Hmo1).
  pose proof (psw_xm_bound MT MTL (x_R c) R1 u f l v r (x_T c) (tl (x_tks c)) Hm Hps Hu Hf Hl Hv Hsf0 Hsf1) as HX.
  rewrite Hr0 in HX. cbv iota in HX. lia.
- (* rc = 0: 0x8e78c jal lv2_refusals_forget with a0 = 0 *)
  assert (Hrz : r = 0).
  { rewrite branch_ne_U in Hc. rewrite U_SOff, E10, Z.add_0_r in Hc. change (U E (SLit 0)) with 0 in Hc.
    apply negb_false_iff, Z.eqb_eq in Hc. unfold w64 in Hc. rewrite Z_to_bv_unsigned in Hc.
    unfold zcanon, M64, bv_wrap in Hc. change (bv_modulus 64) with (2 ^ 64) in Hc. rewrite Zmod_mod in Hc.
    exact (tb_mod64_zero r Hr Hc). }
  subst r. clear Hc.
  assert (HEVs : EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)) = EV_PINS_SET (x_R c) + EV_LV2_REFUSALS_FORGET R1).
  { rewrite (psw_ev_split (x_R c) R1 u f l v 0 (x_T c) (tl (x_tks c)) Hm Hps), Z.eqb_refl. reflexivity. }
  pose proof (psw_xm_bound MT MTL (x_R c) R1 u f l v 0 (x_T c) (tl (x_tks c)) Hm Hps Hu Hf Hl Hv Hsf0 Hsf1) as HX.
  rewrite Z.eqb_refl in HX. cbv iota in HX.
  pose proof (tb_live_bound (x_R c) u f l v Hu Hf Hl Hv) as HLVB.
  tb_run RUNP RUNC HS HJ msC mdC Hm1.
  assert (Hmc : ms_mem msC = mem2) by (rewrite Hm1; exact Hm0).
  rewrite Hmc in HJ.
  prreg HS (1%bv : bv 5) Q1.
  pose proof (fun z (Hz : In z [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) =>
    regs_kept_of_st_ok SEGS E _ _ regs2 (psw_extraJ (x_regs c) 0 0 0)
      (map (Z_to_bv 5) [2; 3; 4; 8; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]) HS HAE
      ltac:(vm_compute; reflexivity) (Z_to_bv 5 z) (in_map _ _ _ Hz)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS. rewrite Hmc.
  rewrite (SIGP CS_lv2_refusals_forget ltac:(unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right])).
  change (cmd_af CS_lv2_refusals_forget) with AF_lv2_refusals_forget.
  set (regsc := ms_regs msC) in *.
  (* the registers at the call *)
  assert (R2c : getr regsc 2 = w64 (psw_sp0 c - 48)) by exact (eq_trans (tb_kept1 regsc regs2 2%bv 2 eq_refl (KR 2 ltac:(tb_in))) Q2).
  assert (R3c : getr regsc 3 = getr (x_regs c) 3) by exact (eq_trans (tb_kept1 regsc regs2 3%bv 3 eq_refl (KR 3 ltac:(tb_in))) Q3).
  assert (R4c : getr regsc 4 = getr (x_regs c) 4) by exact (eq_trans (tb_kept1 regsc regs2 4%bv 4 eq_refl (KR 4 ltac:(tb_in))) Q4).
  assert (R8c : getr regsc 8 = w64 (x_tok c)) by exact (eq_trans (tb_kept1 regsc regs2 8%bv 8 eq_refl (KR 8 ltac:(tb_in))) Q8).
  assert (R10c : getr regsc 10 = w64 0) by exact (eq_trans (tb_kept1 regsc regs2 10%bv 10 eq_refl (KR 10 ltac:(tb_in))) Q10).
  assert (R20c : getr regsc 20 = w64 SB) by exact (eq_trans (tb_kept1 regsc regs2 20%bv 20 eq_refl (KR 20 ltac:(tb_in))) Q20).
  assert (Rhic : forall z, 21 <= z <= 27 -> getr regsc (Z_to_bv 5 z) = getr (x_regs c) (Z_to_bv 5 z)).
  { intros z Hz. rewrite <- (Qhi z Hz). apply KR.
    assert (Hzc : z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by lia.
    destruct Hzc as [->|[->|[->|[->|[->|[->| ->]]]]]]; tb_in. }
  assert (Hsp : spZ regsc = psw_sp0 c + -48).
  { unfold spZ at 1. rewrite R2c. unfold w64. rewrite unsigned_lit_small by (unfold psw_sp0; lia). lia. }
  assert (Hs0 : s0Z regsc = x_tok c) by (unfold s0Z; rewrite R8c; unfold w64; apply unsigned_lit_small; lia).
  assert (Q1' : getr regsc 1 = Z_to_bv 64 (BASE + (PSW_K2 + 12))) by (rewrite Q1; reflexivity).
  assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + (PSW_K2 + 12)))).
  { apply ret_ok_codeptr_v; [unfold PSW_K2, AF_pin_set_words; lia | reflexivity]. }
  assert (Hra4 : 4096 <= bv_unsigned (Z_to_bv 64 (BASE + (PSW_K2 + 12)))).
  { unfold PSW_K2, AF_pin_set_words. rewrite unsigned_lit_small by lia. lia. }
  (* the state at the call: the journal, the stack, the read-only bytes, the frame chain of s0 = tok *)
  pose proof (proj1 HJ) as HAR2.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev2 & _).
  (* the frame chain of s0 = tok: tok lies in verbs_receive's side-stack frame, below alloc_ceiling (achain's
     empty case; pass 5 removed astack_pres) *)
  pose (ch1 := @nil (Z * Z * Z)).
  assert (Hch : achain ly2 (rdW W2 mem2) (psw_sp0 c + -48) (s0Z regsc) ch1)
    by (unfold ch1; rewrite Hs0; apply achain_low; lia).
  assert (HROD : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W2 mem2)) by exact (tb_aro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HFPro HROD0).
  pose proof (cmd_ro_ok_of_aro SEGS B LAWS HB IMG ly2 S2 W2 mem2 mdC HAR2 HROD) as HRO.
  assert (HARG : astr_argA B ly2 S2 (rdW W2 mem2) (in_roP SEGS CMD_RLO CMD_RHI) O1 0 None) by exact eq_refl.
  assert (HTAIL : forall x, @None (list byte) = Some x -> atail_vis SEGS W2 mem2 (0 + Z.of_nat (length x)))
    by (intros x Hx; discriminate Hx).
  assert (HEV1 : st_nev S2 + EV_LV2_REFUSALS_FORGET R1 <= EV_MAX) by lia.
  assert (HLV1 : blocks_bytes S2 + LIVE_LV2_REFUSALS_FORGET None <= LIVE_MAX) by lia.
  assert (HXL0 : 0 <= XM_LV2_REFUSALS_FORGET MT R1 None).
  { unfold XM_LV2_REFUSALS_FORGET, XM_XSTRDUP. rewrite Hsf1.
    lazymatch goal with |- context [mo_malloc MT ?x] => pose proof (mo_malloc_nonneg MT MTL x ltac:(lia)) end. lia. }
  pose proof (mok_station MT (x_S c) S2 _ _ _ MTL HMETER Hmo1 HXL0 HX) as HMO1.
  pose proof (fun HPRE : afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly2 S2 W2 regsc mem2 mdC ch1 =>
    LV2_REFUSALS_FORGET ly2 S2 W2 regsc mem2 mdC ch1 0 None R1 O1 HPRE HROD HRO R10c ltac:(lia) HARG HTAIL
      Hrec1 HEV1 HLV1 HMO1) as HCALL.
  lazymatch type of HCALL with _ -> SRr _ _ _ (apost_base _ _ _ ?F _ _ _ _ _ _ _ ?K) =>
    set (FP1 := F) in HCALL; set (Kp := K) in HCALL end.
  assert (HFP1low : forall a, inFP FP1 a -> a < alloc_ceiling).
  { intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [G|Ha]; [unfold A_G_REC, REC_SIZE in G; lia|].
    apply inFP_cons in Ha as [G|Ha]; [unfold A_REC_SPILL, SC_SIZE in G; lia|].
    destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & n & Hpn & Hrg).
    destruct (al_blocks SEGS B LAWS _ _ _ _ _ p n HAR2 (rec_repA_in_blocks B _ _ _ _ _ _ Hrec1 Hpn)) as (_ & _ & Hc & _).
    lia. }
  (* the callee's footprint: g_rec and record.spill (program statics in the image), and the recorder's blocks O1 *)
  assert (HFP1 : forall a, inFP FP1 a -> (inFP (psw_FP c) a /\ ((exists b n, In (b, n) (ablocks B ly2 S2) /\
      b <= a < b + req_size n) \/ (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/
      in_tmp_block (ablocks B (x_ly c) (x_S c)) (ablocks B ly2 S2) a).
  { intros a Ha. unfold FP1 in Ha. apply inFP_cons in Ha as [G|Ha].
    - left. split; [unfold psw_FP, PIN_SET_WORDS_PG; apply inFP_app; left; apply inFP_cons; left; exact G|].
      right. split.
      + rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd.
        unfold in_zr, A_G_REC, REC_SIZE in *. cbn [fst snd]. lia.
      + apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. left. unfold REC_SIZE in G. exact G.
    - apply inFP_cons in Ha as [G|Ha].
      + left. split; [unfold psw_FP, PIN_SET_WORDS_PG; apply inFP_app; left; apply inFP_cons; right; apply inFP_cons; left; exact G|].
        right. split.
        * rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_tl. apply Exists_cons_hd.
          unfold in_zr, A_REC_SPILL, SC_SIZE in *. cbn [fst snd]. lia.
        * apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left.
          unfold SC_SIZE in G. exact G.
      + destruct (inFP_ablocks_fp_inv O1 a Ha) as (p & n & Hpn & Hrg).
        pose proof (rec_repA_in_blocks B _ _ _ _ _ _ Hrec1 Hpn) as Hin2.
        destruct (HO1 _ Hpn) as [HinO | Hnot].
        * left. split.
          -- unfold psw_FP. apply inFP_app. right. exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
             unfold ablocks_fp. exact (in_map (fun b => (fst b, fst b + req_size (snd b))) _ (p, n) HinO).
          -- left. exists p, n. split; [exact Hin2 | exact Hrg].
        * right. exists p, n. split; [exact Hin2|]. split; [exact Hnot | exact Hrg]. }
  assert (HCALLEE : afn_pre SEGS B LV2_REFUSALS_FORGET_STK ly2 S2 W2 regsc mem2 mdC ch1 ->
    SRr SEGS W2 (mkCfg (mkst regsc (Z_to_bv 64 (BASE + AF_lv2_refusals_forget)) mem2 (seg_rom SEGS)) mdC)
    (fun W' c' => exists ly' S' regs' mem' md', c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (PSW_K2 + 12))) mem' (seg_rom SEGS)) md' /\
       ajournal SEGS B LV2_REFUSALS_FORGET_STK (spZ regsc) FP1 ly2 S2 W2 mem2 mdC [] ly' S' W' mem' md'
         (EV_LV2_REFUSALS_FORGET R1) /\
       aregs_preserved regsc regs' /\ Kp ly' S' W' regs' mem' md')).
  { intros HPRE. pose proof (HCALL HPRE) as HC1. unfold cfg_at, w64 in HC1. eapply SRr_mono; [exact HC1|].
    cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ' & HP' & HK').
    exists ly', S', regs', mem', md'. rewrite Q1'. split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP' | exact HK']. }
  eapply SRr_bind.
  { exact (cl_callS_pg B LAWS W2 regsc mem2 (Z_to_bv 64 (BASE + AF_lv2_refusals_forget)) PIN_SET_WORDS_STK (psw_sp0 c)
      (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [] ly2 S2 mdC (EV_PINS_SET (x_R c)) LV2_REFUSALS_FORGET_STK
      FP1 (EV_LV2_REFUSALS_FORGET R1) (-48) (Z_to_bv 64 (BASE + (PSW_K2 + 12))) ch1 Kp HJ Hsp eq_refl ltac:(lia) HLS0
      ltac:(lia) (eq_trans R3c Hgp) (eq_trans R4c Htp) Q1' Hraw Hra4 Hch HCALLEE HFP1). }
  cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HJc & HP3 & HK3).
  unfold Kp in HK3. destruct HK3 as (O3 & Hrec3 & HO3 & Hsurv3 & Hall3 & Hlive3 & Hmo3).
  (* the frame is kept across the call: it lies above the callee's window and outside its footprint *)
  assert (HKF : forall x, spZ (x_regs c) - 48 <= x < spZ (x_regs c) -> rdW W3 mem3 x = rdW W2 mem2 x).
  { intros x Hx. pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
    apply F1; [lia | unfold psw_sp0; lia |]. intros Hfa. pose proof (HFP1low x Hfa). lia. }
  pose proof (tb_saved_kept (x_regs c) _ _ HKF HSV) as HSV3.
  (* the registers after the call: the callee-saved ones of the call state *)
  assert (HCS : forall z, acallee_saved z -> getr regs3 (Z_to_bv 5 z) = getr regsc (Z_to_bv 5 z)) by exact HP3.
  assert (R2' : getr regs3 2 = w64 (spZ (x_regs c) - 48))
    by exact (eq_trans (tb_kept1 regs3 regsc 2%bv 2 eq_refl (HCS 2 ltac:(unfold acallee_saved; lia))) R2c).
  assert (R3' : getr regs3 3 = getr (x_regs c) 3)
    by exact (eq_trans (tb_kept1 regs3 regsc 3%bv 3 eq_refl (HCS 3 ltac:(unfold acallee_saved; lia))) R3c).
  assert (R4' : getr regs3 4 = getr (x_regs c) 4)
    by exact (eq_trans (tb_kept1 regs3 regsc 4%bv 4 eq_refl (HCS 4 ltac:(unfold acallee_saved; lia))) R4c).
  assert (R8' : getr regs3 8 = w64 (x_tok c))
    by exact (eq_trans (tb_kept1 regs3 regsc 8%bv 8 eq_refl (HCS 8 ltac:(unfold acallee_saved; lia))) R8c).
  assert (R20' : getr regs3 20 = w64 SB)
    by exact (eq_trans (tb_kept1 regs3 regsc 20%bv 20 eq_refl (HCS 20 ltac:(unfold acallee_saved; lia))) R20c).
  assert (Rhi' : forall z, 21 <= z <= 27 -> getr regs3 (Z_to_bv 5 z) = getr (x_regs c) (Z_to_bv 5 z)).
  { intros z Hz. rewrite (HCS z ltac:(unfold acallee_saved; lia)). exact (Rhic z Hz). }
  (* the seed at 0x8e790, the return address of the call *)
  pose proof (psw_seedJ (x_ly c) W3 mem3 (x_regs c) regs3 (PSW_K2 + 12) (x_tok c) 0 0 0 Hstk HSV3 R2' R8' R20' Htok Htok8
    ltac:(lia) ltac:(lia) ltac:(lia)) as HS3.
  set (E3 := EJ regs3 (x_regs c) 0 0 0) in HS3.
  assert (HEI3 : img_env VAL A_LIM E3) by (subst E3; unfold EJ; apply Eimg_env).
  assert (HAG3 : env_agree 41 (EJ regs3 (x_regs c) 0 0 0) E3) by (subst E3; split; [intros; reflexivity | reflexivity]).
  clearbody E3.
  clear HS HEI HAG HAE E10 KR.
  (* 0x8e790 li s1,0; 0x8e794 mv a0,s1; the epilogue; ret *)
  tb_run RUNP RUNC HS3 HJ3 msD mdD Hm2.
  destruct (psw_aregs_leaf (x_regs c) regs3 0 0 0 E3 _ (w_H W3) msD HS3 HAG3 ltac:(vm_compute; reflexivity)
    R2' R3' R4' Rhi' H48) as [Hra1 Haregs].
  prreg HS3 (10%bv : bv 5) Q10e.
  assert (Hk : EV_PINS_SET (x_R c) + EV_LV2_REFUSALS_FORGET R1 <= EV_PIN_SET_WORDS (x_R c) (x_T c) (tl (x_tks c)))
    by lia.
  eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) _ _ _ _ _ _ HS3 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  apply (psw_leaf_post B MT c W3 (ms_regs msD) (ms_mem msD) mdD ly3 S3 (EV_PINS_SET (x_R c) + EV_LV2_REFUSALS_FORGET R1)
    Hra Hra1 Haregs HJ3 Hk mat').
  unfold psw_Q. rewrite (psw_run_set (x_R c) (x_T c) (tl (x_tks c)) u f l v R1 0 Hm Hps), Z.eqb_refl. cbv beta iota.
  exists O3.
  split; [rewrite Q10e; reflexivity|].
  split; [lia|].
  split; [rewrite Hm2; exact Hrec3|].
  split.
  { intros pn Hpn Hno. apply Hsurv3; [exact (Hsurv1 pn Hpn Hno)|].
    intros HinO1. destruct (HO1 pn HinO1) as [H|H]; [exact (Hno H) | exact (H Hpn)]. }
  split.
  { intros pn Hpn. destruct (Hall3 pn Hpn) as [[Hin2 Hno1] | HinO3]; [|right; exact HinO3].
    destruct (Hall1 pn Hin2) as [H|H]; [left; exact H | exact (False_ind _ (Hno1 H))]. }
  split.
  { intros pn Hpn. destruct (HO3 pn Hpn) as [HinO1 | Hnot2]; [exact (HO1 pn HinO1)|].
    destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) pn (x_O c)) as [Hi|Hi]; [left; exact Hi|].
    right. intros Hin. exact (Hnot2 (Hsurv1 pn Hin Hi)). }
  split; [lia|].
  apply (mle_weaken MT _ _ _ _ MTL (mle_station MT _ _ _ _ _ MTL Hmo1 Hmo3)). lia.
Qed.
End e.
End f.
End d.
