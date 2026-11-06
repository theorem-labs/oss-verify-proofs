(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: chain_words' walk on the ASan build of plugin-hostd/fuzz_command, segment S1
   (chain_words_d.v cw_S1P): from the entry (0x8dfd4) through __asan_stack_malloc_3 (0x8e044) to the refusal cut KR
   (0x8e278) or the first-check cut KC (0x8e1ec). In the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACa2.v (entry,
   aj_stack_malloc_atS, re-seat) with the entry seed of lib/A/Prog/numberE.v: a run to the call, the call, a re-seat
   that keeps the three stack regions and adds the frame (the call's a0) and its shadow (the alias of
   (s8 >> 3) + s7), a plain run through the 88 shadow stores to the branch on ntok < 3, and the cut facts (cw_pc)
   read back from the symbolic state at the cut. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/chain_words_s1.v, with its module paths and module names changed; 318 of its 363 lines of code are new or changed and 521 lines of the source are left out. *)
(* Segment Ta of the walk of pin_set_words (0x8e17c) on the ASan+UBSan build of plugin-hostd/fuzz_command (image B,
   fuzz_command.asan-ubsan), against the segment interface lib/B/Prog/pin_set_words_s4.v: from the join JOIN
   (0x8e284, every check passed, a3 = the verdict pointer) through the UBSan checks on tok + 8 and tok + 16
   (0x8e288 / 0x8e294 / 0x8e2ac / 0x8e2b8: wrap and misalignment, each a branch to the `unimp` at 0x8e310) and the
   two inline load8 checks of &tok[1] and &tok[2] (0x8e284 .. 0x8e2c8), the loads of tok[2] and tok[1] and
   `mv a2,s1` (0x8e2cc .. 0x8e2d4; on B s1 holds tok[3]) and the call `jal pins_set` (0x8e2d8, pins_set at 0x8c938)
   to K2 (0x8e2dc), where it hands INV_K2 to the next segment (from_K2).

   The four UBSan branches are decided not taken by the symbolic run itself, from the fact on tok (atom 8 of the
   seed psw_seedJ: in [4096, 0x7fffff800000], 8-aligned). The run writes no memory (every region of its symbolic
   state is read-only), so the memory at the call is the memory at JOIN, and that is the entry memory outside the
   stack window (psw_cut's kept_out): every fact pins_set's contract (lib/B/Prog/pins_set_c.v:87-143) asks of the
   caller's objects is carried from the entry facts (psw_pre). pins_set reaches the snprintf wrapper (answer_code),
   so it returns at some FP state fx1 (apost_baseF): the call goes through the B kit's cl_callS_pgF
   (lib/B/Prog/PaFx.v:344), the segment after it is taken at fx1 (from_K2 at fx1) and its post is lifted
   back to the entry's FP state by psw_post_lift. pins_set's pre asks rounding mode 0 at the call, which is the
   entry's (the segment theorem's premise). tok is in verbs_receive's side-stack frame, below alloc_ceiling, so the
   frame chain the call asks of s0 = tok is achain's empty case (achain_low).

   Section hypotheses: HB (ts_prog: g_rec and record.spill are program statics; cmd_heap_tail_vis, the verdict's
   word tail), IMG (cif_prog_img: they are image bytes), MTL, SIGP (the call target) and PINS_SET. The B twin
   of a Theorem Labs lane's A file lib/A/Prog/pin_set_words_ta.v. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YI08 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Verbs VerbsRun StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdChk.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdObj CmdRo CmdBase CmdRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaArt PaNoChain PaCallPg PaFx.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdRecBase CmdRecImg.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import xmalloc_c record_c arg_s_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s1 pin_set_words_s2 pin_set_words_s3.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pins_set_c lv2_refusals_forget_c pin_set_words_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import pin_set_words_s4.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the symbolic state at JOIN after the two token words are added: tok[2] (atom 39), tok[1] (atom 38), the frame *)
Definition ss_ta : sstate := mkSS PSW_JOIN sr_atoms [psw_tokJ 2 39; psw_tokJ 1 38; psw_frameJ] None psw_factsJ.

(* a callee-saved register, named by its literal, through aregs_preserved *)
Lemma ta_pres : forall (regs regs' : bvmap 5 word) (b : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned b) -> getr regs' b = getr regs b.
Proof. intros regs regs' b H Hc. pose proof (H _ Hc) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Ltac ta_cs := cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.

(* the call of pins_set records one call in a table that holds at most 14 before it: no spill, before or after *)
Lemma ta_spill0 : forall R u f l v R1 r, (length (r_calls R) + 2 <= 16)%nat -> pins_set_m R u f l v = (R1, r) ->
  rec_spill_frees R = 0 /\ rec_spill_frees R1 = 0.
Proof.
intros R u f l v R1 r Hc HS.
assert (Hlt : Nat.ltb (length (r_calls R)) 16 = true) by (apply Nat.ltb_lt; lia).
unfold rec_spill_frees. rewrite Hlt. split; [reflexivity|].
unfold pins_set_m, rec_stub_code, rec_answer_code, rec_mix, rec_record in HS. cbv zeta in HS. rewrite Hlt in HS.
match type of HS with context [if ?b then _ else _] => destruct b end;
injection HS as <- _; cbn [set_answer set_state set_calls r_calls];
match goal with |- context [Nat.ltb ?x 16] => replace (Nat.ltb x 16) with true; [reflexivity|] end;
symmetry; apply Nat.ltb_lt; rewrite length_app; cbn [length]; lia.
Qed.

(* the six saved words, through a reader that agrees on the frame *)
Lemma ta_saved_kept : forall regs (rd rd' : reader), psw_saved regs rd ->
  (forall x, spZ regs - 48 <= x < spZ regs -> rd' x = rd x) -> psw_saved regs rd'.
Proof.
intros regs rd rd' (S1 & S8 & S9 & S18 & S19 & S20) HK.
assert (G : forall o v, 8 <= o <= 48 -> aval_mem rd (spZ regs - o) 8 v -> aval_mem rd' (spZ regs - o) 8 v).
{ intros o v Ho Hv. apply (aval_mem_kept_r rd rd'); [|exact Hv]. intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HK. lia. }
refine (conj (G _ _ _ S1) (conj (G _ _ _ S8) (conj (G _ _ _ S9) (conj (G _ _ _ S18) (conj (G _ _ _ S19) (G _ _ _ S20))))));
lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the read-only bytes the statements name lie in the image, below any stack window *)
Lemma ta_aro_kept : forall B (rd rd' : reader) lo hi, arodata_okP SEGS CMD_RLO CMD_RHI B rd ->
  kept_out rd rd' lo hi -> 0x606000 <= lo -> arodata_okP SEGS CMD_RLO CMD_RHI B rd'.
Proof.
intros B rd rd' lo hi H HK Hlo a Ha Ho He.
assert (Hr : 0 <= a < 0x606000).
{ destruct Ha as [(s & Hs & _ & Hr) | Hr].
  - assert (Himg : in_img SEGS a) by (exists s; split; [exact Hs | exact Hr]).
    pose proof (pa_img_range a Himg). lia.
  - unfold CMD_RLO, CMD_RHI in Hr. lia. }
rewrite (HK a) by lia. exact (H a Ha Ho He).
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis HB : CmdBSyms B.
Hypothesis IMG : cmd_img_facts SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis SIGP : cmd_sig_prog.
Hypothesis PINS_SET : forall fx0 : YK11.FPState, @tpins_set_spec fx0 rc SK PI B MT.
Let RUN := paj_run B LAWS.

(* a word inside the block `copy`, which the recorder does not own: inside a live block and apart from each of the
   recorder's blocks (AR's disjoint live blocks; pin_set_words_s3.v psw3_argA_at) *)
Lemma ta_blk : forall ly S (W : world SEGS) mem md (O : list (Z * Z)) cb ncb p n,
  AR SEGS B ly S W mem md -> In (cb, ncb) (ablocks B ly S) -> ~ In (cb, ncb) O ->
  (forall pn, In pn O -> In pn (ablocks B ly S)) -> cb <= p -> p + n <= cb + ncb -> 0 <= n ->
  in_blockA (ablocks B ly S) p n /\ Forall (fun qk => iv_apart p n (fst qk) (snd qk)) O.
Proof.
intros ly S W mem md O cb ncb p n HAR Hin Hno HO Hlo Hhi Hn.
split; [exists cb, ncb; split; [exact Hin | lia]|].
apply Forall_forall. intros [q k] Hqk. cbn [fst snd].
assert (Hne : (cb, ncb) <> (q, k)) by (intros E; apply Hno; rewrite E; exact Hqk).
pose proof (sep_blocks SEGS B LAWS ly S W mem md cb ncb q k HAR Hin (HO _ Hqk) Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd.
pose proof (psw3_req_ge ncb). pose proof (psw3_req_ge k).
unfold iv_apart. lia.
Qed.

Theorem psw_Ta : forall c, psw_pre B MT c -> Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
  (forall fx1 : YK11.FPState, from_K2 (fx := fx1) B MT c) -> from_JOIN B MT c.
Proof.
intros c HP HFRM HFK2. unfold from_JOIN.
intros regs1 memc mdc (p1 & p2 & p3 & u & f & l & v & vptr & HCUT & H13 & Hp1 & Hp2 & Hp3 & Hu & Hf & Hl & Hm & HV).
destruct HCUT as [HJ HKEEP HSAVED Q2 Q3 Q4 Q8 Q9 Q20 QHI].
unfold psw_sp0 in *.
pose proof (pp_afn B MT c HP) as HPRE.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HSTK : 48 + PINS_SET_STK <= PIN_SET_WORDS_STK).
{ unfold PIN_SET_WORDS_STK. pose proof (Z.le_max_r (2 * ESTACK) (Z.max PINS_SET_STK LV2_REFUSALS_FORGET_STK)).
  pose proof (Z.le_max_l PINS_SET_STK LV2_REFUSALS_FORGET_STK). lia. }
assert (HPS0 : 0 <= PINS_SET_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HLO : alloc_ceiling <= spZ (x_regs c) - PIN_SET_WORDS_STK) by lia.
(* the token array and its words *)
pose proof (pp_toks B MT c HP) as HTOKS.
pose proof HTOKS as (Htok8 & Hlen & Hptr & Hwd).
pose proof (pp_cb B MT c HP) as HCB. pose proof (pp_cbO B MT c HP) as HCBO.
pose proof (pp_rec B MT c HP) as HREC0.
destruct (al_blocks SEGS B LAWS _ _ _ _ _ _ _ HAR0 HCB) as (_ & Hcb4096 & Hcbc & _).
pose proof (psw3_req_ge (x_ncb c)) as Hreqcb.
destruct (Hwd 1%nat p1 u Hp1 Hu) as (HSu & HLu & Hu1 & Hu2).
destruct (Hwd 2%nat p2 f Hp2 Hf) as (HSf & HLf & Hf1 & Hf2).
destruct (Hwd 3%nat p3 l Hp3 Hl) as (HSl & HLl & Hl1 & Hl2).
pose proof (Hptr 1%nat p1 Hp1) as HM1. pose proof (Hptr 2%nat p2 Hp2) as HM2.
change (Z.of_nat 1) with 1 in HM1. change (Z.of_nat 2) with 2 in HM2.
pose proof (pp_tokobj B MT c HP) as ((cid & pos & Hfr & Hcid & Hfa8 & Hflo & Hfhi) & _ & HRA0).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR0 Hfr) as (Hf0 & Hfc & Happ).
assert (Hn4 : 4 <= x_ntok c).
{ assert (H3 : (3 < length (x_tks c))%nat) by (apply nth_error_Some; rewrite Hl; discriminate).
  pose proof (pp_ntok B MT c HP). lia. }
pose proof (pp_ntokr B MT c HP) as Hntokr.
assert (Hp1r : 0 <= p1 < 2 ^ 64) by lia.
assert (Hp2r : 0 <= p2 < 2 ^ 64) by lia.
(* the seed at JOIN *)
pose proof (psw_seedJ (x_ly c) (x_W c) memc (x_regs c) regs1 PSW_JOIN (x_tok c) p1 p2 0 Hstk HSAVED Q2 Q8 Q20
  ltac:(lia) Htok8 Hp1r Hp2r ltac:(lia)) as HS0.
set (E := EJ regs1 (x_regs c) p1 p2 0) in HS0.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r)
  by (intros n r Hn; subst E; unfold EJ; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ES : forall j, (j < 9)%nat -> ew E (32 + j) = nth j (psw_extraJ (x_regs c) p1 p2 0) (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold EJ; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
assert (E38 : ew E 38 = Z_to_bv 64 p1) by exact (ES 6%nat ltac:(lia)).
assert (E39 : ew E 39 = Z_to_bv 64 p2) by exact (ES 7%nat ltac:(lia)).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EJ; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (psw_extraJ (x_regs c) p1 p2 0)) E).
{ split; [intros n Hn; subst E; unfold EJ; apply Eimg_low; unfold A_TEXT; lia | subst E; reflexivity]. }
assert (U8 : bv_unsigned (ew E 8) = x_tok c)
  by (rewrite (EE 8%nat 8%bv eq_refl), Q8; unfold w64; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = spZ (x_regs c) - 48)
  by (rewrite (EE 2%nat 2%bv eq_refl), Q2; unfold w64; apply unsigned_lit_small; lia).
clearbody E.
(* tok[1] and tok[2] as read-only regions over s0 *)
assert (V1 : val_mem SEGS (mrestrict (w_H (x_W c)) memc) (x_tok c + 8 * 1) 8 p1).
{ apply psw_val_mem_of_aval. apply (aval_mem_kept_r (rdW (x_W c) (x_mem c))); [|exact HM1].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HKEEP; lia. }
assert (V2 : val_mem SEGS (mrestrict (w_H (x_W c)) memc) (x_tok c + 8 * 2) 8 p2).
{ apply psw_val_mem_of_aval. apply (aval_mem_kept_r (rdW (x_W c) (x_mem c))); [|exact HM2].
  intros x Hx. change (Z.of_nat 8) with 8 in Hx. apply HKEEP; lia. }
assert (D1 : all_disjoint E (psw_tokJ 1 38) (ss_mem (ss_pswJ PSW_JOIN))).
{ apply all_disjoint_of_extents. unfold ss_pswJ, psw_tokJ, psw_frameJ.
  cbn [ss_mem map extent_of_region YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].
  unfold extent_of_region, zdisj, base_val. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi]. split; [lia | exact I]. }
assert (D2 : all_disjoint E (psw_tokJ 2 39) (psw_tokJ 1 38 :: ss_mem (ss_pswJ PSW_JOIN))).
{ apply all_disjoint_of_extents. unfold ss_pswJ, psw_tokJ, psw_frameJ.
  cbn [ss_mem map extent_of_region YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint].
  unfold extent_of_region, zdisj, base_val. cbn [fst snd YP09.r_base YP09.r_lo YP09.r_hi].
  split; [lia | split; [lia | exact I]]. }
pose proof (psw_add_tok E (ss_pswJ PSW_JOIN) _ 1 38 (x_tok c) p1 HS0 ltac:(vm_compute; reflexivity) U8 E38 Hp1r
  ltac:(lia) ltac:(lia) ltac:(lia) V1 D1) as HS1.
pose proof (psw_add_tok E _ _ 2 39 (x_tok c) p2 HS1 ltac:(vm_compute; reflexivity) U8 E39 Hp2r
  ltac:(lia) ltac:(lia) ltac:(lia) V2 D2) as HS2.
assert (HS : st_ok_pi SEGS VAL E ss_ta
  (restrict (w_H (x_W c)) (mkst regs1 (Z_to_bv 64 (BASE + PSW_JOIN)) memc (seg_rom SEGS)))) by exact HS2.
clear HS0 HS1 HS2 V1 V2 D1 D2.
(* the shadow entry of the two load8 checks: [tok, tok + 24) of the token array *)
assert (HRA : range_addressable (rdW (x_W c) memc) SHADOW_OFF (x_tok c) (8 * x_ntok c)).
{ apply (range_addressable_kept_win (rdW (x_W c) (x_mem c)) _ (spZ (x_regs c) - PIN_SET_WORDS_STK) (spZ (x_regs c)));
  [exact HKEEP | lia | lia | lia | exact HRA0]. }
assert (SHOK : sh_ok SEGS BxJ [mkSHE 8 0 24] E (mrestrict (w_H (x_W c)) memc)).
{ apply (psw_shokJ (x_W c) memc E (x_tok c) (x_ntok c) 24).
  - unfold BxJ. apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), Q20; reflexivity | unfold SHADOW_OFF; lia].
  - apply U_atom; [rewrite (EE 8%nat 8%bv eq_refl), Q8; reflexivity | lia].
  - exact HRA.
  - lia.
  - apply (in_app_sub _ _ _ _ Happ); lia.
  - lia. }
(* 0x8e284 .. 0x8e2d8: the UBSan checks on tok + 8 and tok + 16 (decided by the run from atom 8's fact), the two
   load8 checks, a1 = tok[2], a0 = tok[1], a2 = s1 = tok[3], to the call of pins_set *)
paj_run_tok RUN HS HJ SHOK RBspanJ.
{ unfold ss_ta. cbn [ss_mem].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_cons_ro SEGS B); [cbn; lia|].
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
pmkst HS.
match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?t ?m] =>
  set (mdv := with_vm_backing (m_vm_lazy m) t m) in *; clearbody mdv end.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
prreg HS (13%bv : bv 5) P13.
(* the run wrote no byte: the memory at the call is the memory at JOIN, the entry's outside the stack window *)
assert (HSAME : forall a, 0 <= a < 2 ^ 64 -> rdW (x_W c) (ms_mem ms) a = rdW (x_W c) memc a)
  by exact (psw_frame_same E (ss_mem ss_ta) (w_H (x_W c)) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)).
clear HF HFr HG.
assert (HKc : kept_out (rdW (x_W c) (x_mem c)) (rdW (x_W c) (ms_mem ms))
  (spZ (x_regs c) - PIN_SET_WORDS_STK) (spZ (x_regs c))).
{ intros a Ha Hn. rewrite (HSAME a Ha). exact (HKEEP a Ha Hn). }
(* the registers at the call *)
assert (Qsp : spZ (ms_regs ms) = spZ (x_regs c) + -48).
{ change (spZ (ms_regs ms)) with (bv_unsigned (getr (ms_regs ms) 2)). rewrite P2, U2. lia. }
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, (EE 3%nat 3%bv eq_refl), Q3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, (EE 4%nat 4%bv eq_refl), Q4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 p1) by (rewrite P10, E38; reflexivity).
assert (P11' : getr (ms_regs ms) 11 = w64 p2) by (rewrite P11, E39; reflexivity).
assert (P12' : getr (ms_regs ms) 12 = w64 p3) by (rewrite P12, (EE 9%nat 9%bv eq_refl); exact Q9).
assert (P13' : getr (ms_regs ms) 13 = w64 vptr) by (rewrite P13, (EE 13%nat 13%bv eq_refl); exact H13).
assert (Hs0 : s0Z (ms_regs ms) = x_tok c) by (unfold s0Z; rewrite P8; exact U8).
assert (HRA1 : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs ms) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
assert (HK2pc : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PSW_K2)) by (rewrite P1; reflexivity).
assert (HPR1 : aregs_preserved regs1 (ms_regs ms))
  by exact (aregs_preserved_of_st_ok SEGS _ E _ ms regs1 (psw_extraJ (x_regs c) p1 p2 0) HS HAE ltac:(vm_compute; reflexivity)).
assert (HCH : achain (x_ly c) (rdW (x_W c) (ms_mem ms)) (spZ (x_regs c) + -48) (s0Z (ms_regs ms)) [])
  by (rewrite Hs0; apply achain_low; lia).
(* the caller's objects at the call *)
pose proof (proj1 HJ) as HARc.
assert (HOb : forall pn, In pn (x_O c) -> In pn (ablocks B (x_ly c) (x_S c)))
  by (intros pn Hpn; exact (rec_repA_in_blocks B _ _ _ _ _ pn HREC0 Hpn)).
assert (HOlo : forall p n a, In (p, n) (x_O c) -> p <= a < p + req_size n -> 0 <= a < alloc_ceiling).
{ intros p n a Hpn Hr. destruct (al_blocks SEGS B LAWS _ _ _ _ _ p n HAR0 (HOb _ Hpn)) as (_ & Hp4 & Hc & _). lia. }
assert (HFPlo : forall a, inFP (psw_FP c) a -> a < alloc_ceiling).
{ intros a Ha. unfold psw_FP, PIN_SET_WORDS_PG in Ha. cbn [app] in Ha.
  apply inFP_cons in Ha as [Ha | Ha]; [unfold A_G_REC, REC_SIZE in Ha; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold A_REC_SPILL, SC_SIZE in Ha; lia|].
  destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & n & Hpn & Hr). pose proof (HOlo p n a Hpn Hr). lia. }
assert (HRODc : arodata_okP SEGS CMD_RLO CMD_RHI B (rdW (x_W c) (ms_mem ms)))
  by exact (ta_aro_kept B _ _ _ _ (pp_rod B MT c HP) HKc ltac:(lia)).
assert (HROc : cmd_ro_ok (rdW (x_W c) (ms_mem ms)))
  by exact (cmd_ro_ok_kept _ _ _ _ HKc (pp_ro B MT c HP) ltac:(lia) ltac:(lia)).
assert (Hp3r : 0 <= p3 < 2 ^ 64) by lia.
destruct (ta_blk (x_ly c) (x_S c) (x_W c) (ms_mem ms) mdv (x_O c) (x_cb c) (x_ncb c) p1 (Z.of_nat (length u) + 1)
  HARc HCB HCBO HOb Hu1 ltac:(lia) ltac:(lia)) as [BU AU].
destruct (ta_blk (x_ly c) (x_S c) (x_W c) (ms_mem ms) mdv (x_O c) (x_cb c) (x_ncb c) p2 (Z.of_nat (length f) + 1)
  HARc HCB HCBO HOb Hf1 ltac:(lia) ltac:(lia)) as [BF AF].
destruct (ta_blk (x_ly c) (x_S c) (x_W c) (ms_mem ms) mdv (x_O c) (x_cb c) (x_ncb c) p3 (Z.of_nat (length l) + 1)
  HARc HCB HCBO HOb Hl1 ltac:(lia) ltac:(lia)) as [BL AL].
assert (SU : astr_atR (rdW (x_W c) (ms_mem ms)) p1 u)
  by exact (astr_atR_kept _ _ _ _ p1 u HKc HSu ltac:(lia) ltac:(lia) ltac:(lia)).
assert (SF : astr_atR (rdW (x_W c) (ms_mem ms)) p2 f)
  by exact (astr_atR_kept _ _ _ _ p2 f HKc HSf ltac:(lia) ltac:(lia) ltac:(lia)).
assert (SL : astr_atR (rdW (x_W c) (ms_mem ms)) p3 l)
  by exact (astr_atR_kept _ _ _ _ p3 l HKc HSl ltac:(lia) ltac:(lia) ltac:(lia)).
assert (HTOKc : atoks_atA (rdW (x_W c) (ms_mem ms)) (x_tok c) (x_ptrs c) (x_tks c) (x_cb c) (x_ncb c)).
{ apply (atoks_atA_agree (rdW (x_W c) (x_mem c))); [exact HTOKS | |].
  - intros k Hk. rewrite Hlen in Hk. pose proof (pp_ntok B MT c HP). apply HKc; lia.
  - intros k Hk. apply HKc; lia. }
(* the verdict: NULL, or the tail of tok[4] after "verdict=" inside the block `copy` *)
assert (HVA : astr_argA B (x_ly c) (x_S c) (rdW (x_W c) (ms_mem ms)) (in_roP SEGS CMD_RLO CMD_RHI) (x_O c) vptr v /\
  (forall x, v = Some x -> atail_vis SEGS (x_W c) (ms_mem ms) (vptr + Z.of_nat (length x))) /\
  (forall x, v = Some x -> (length x <= 8192)%nat) /\ 0 <= vptr < 2 ^ 64).
{ destruct HV as [[-> ->] | (p4 & w4 & Hp4 & Hw4 & H8 & -> & ->)].
  - split; [reflexivity|]. split; [intros x Hx; discriminate Hx|]. split; [intros x Hx; discriminate Hx | lia].
  - destruct (Hwd 4%nat p4 w4 Hp4 Hw4) as (_ & HL4 & H41 & H42).
    pose proof (psw3_len_skipn 8 w4 H8) as Ls. change (Z.of_nat 8) with 8 in Ls.
    split; [exact (psw_argA_skipn B CMD_RLO CMD_RHI _ _ _ _ _ _ _ _ _ _ _ 4%nat p4 w4 HARc HTOKc HCB HCBO HOb Hp4 Hw4 H8)|].
    split; [intros x Hx; injection Hx as <-;
      apply (cmd_heap_tail_vis SEGS B LAWS HB (x_ly c) (x_S c) (x_W c) (ms_mem ms) mdv (x_cb c) (x_ncb c));
      [exact HARc | exact HCB | lia]|].
    split; [intros x Hx; injection Hx as <-; apply psw3_z8192; lia | lia]. }
destruct HVA as (HVA1 & HVA2 & HVL & Hvr).
assert (HRECc : rec_repA B (x_ly c) (x_S c) (rdW (x_W c) (ms_mem ms)) (x_R c) (x_O c)).
{ apply (rec_repA_kept B (x_ly c) (x_S c) _ (x_ly c) (x_S c) _ (x_R c) (x_O c) HREC0 HOb).
  intros a Ha. assert (Hlo : 0 <= a < alloc_ceiling).
  { destruct Ha as [Ha | [Ha | Ha]]; [unfold A_G_REC, REC_SIZE in Ha; lia | unfold A_REC_SPILL, SC_SIZE in Ha; lia |].
    destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & n & Hpn & Hr). exact (HOlo p n a Hpn Hr). }
  apply HKc; lia. }
(* the events, the live bytes and the meter of pins_set within pin_set_words' own (B: record + 4 arg_s +
   answer_code, lib/B/Prog/pins_set_c.v:63-80) *)
destruct (pins_set_m (x_R c) (Some u) (Some f) (Some l) v) as [R1 r] eqn:HPS.
destruct (ta_spill0 _ _ _ _ _ _ _ (pp_calls B MT c HP) HPS) as [SP0 SP1].
assert (Hlu : (length u <= 8192)%nat) by exact (psw3_z8192 _ HLu).
assert (Hlf : (length f <= 8192)%nat) by exact (psw3_z8192 _ HLf).
assert (Hll : (length l <= 8192)%nat) by exact (psw3_z8192 _ HLl).
assert (HEVn : st_nev (x_S c) + EV_PINS_SET (x_R c) <= EV_MAX).
{ pose proof (pp_nev B MT c HP) as N. rewrite (psw_ev_split _ _ _ _ _ _ _ _ _ Hm HPS) in N.
  assert (N1 : 0 <= EV_LV2_REFUSALS_FORGET R1)
    by (unfold EV_LV2_REFUSALS_FORGET, EV_RECORD, EV_ARG_S, EV_XMALLOC; rewrite SP1; lia).
  destruct (r =? 0); lia. }
assert (HLV : blocks_bytes (x_S c) + LIVE_PINS_SET (x_R c) (Some u) (Some f) (Some l) v <= LIVE_MAX).
{ pose proof (pp_live B MT c HP). pose proof (psw_live_bound (x_R c) u f l v _ _ Hm Hlu Hlf Hll HVL). lia. }
assert (HMT : mo_ok MT (x_S c) (XM_PINS_SET MT (x_R c) (Some u) (Some f) (Some l) v)).
{ apply (mo_ok_le MT MTL (x_S c) _ _ (pp_meter B MT c HP)).
  pose proof (psw_xm_bound MT MTL _ _ _ _ _ _ _ _ _ Hm HPS Hlu Hlf Hll HVL SP0 SP1) as HXM.
  assert (0 <= (if r =? 0 then XM_LV2_REFUSALS_FORGET MT R1 None else 0)); [|lia].
  destruct (r =? 0); [|lia]. unfold XM_LV2_REFUSALS_FORGET, XM_RECORD, XM_ARG_S, XM_XMALLOC. rewrite SP1.
  match goal with |- context [mo_malloc MT ?n] =>
    pose proof (mo_malloc_nonneg MT MTL n ltac:(unfold LIVE_XMALLOC; lia)) end.
  lia. }
(* pins_set's footprint: g_rec and record.spill (program statics of the image) and the recorder's blocks *)
assert (HFOOT : forall a, inFP ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp (x_O c)) a ->
  (inFP (psw_FP c) a /\ ((exists b n, In (b, n) (ablocks B (x_ly c) (x_S c)) /\ b <= a < b + req_size n) \/
   (Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a))) \/
  in_tmp_block (ablocks B (x_ly c) (x_S c)) (ablocks B (x_ly c) (x_S c)) a).
{ intros a Ha. left. split; [exact Ha|].
  apply inFP_cons in Ha as [Ha | Ha].
  - right. split.
    + rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
      unfold A_G_REC, REC_SIZE in Ha. lia.
    + apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. left. unfold REC_SIZE in Ha. exact Ha.
  - apply inFP_cons in Ha as [Ha | Ha].
    + right. split.
      * rewrite (ts_prog B HB). unfold TFIB_PROG_STATIC. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd].
        unfold A_REC_SPILL, SC_SIZE in Ha. lia.
      * apply (cif_prog_img _ _ IMG). unfold cmd_PG. apply inFP_cons. right. apply inFP_cons. left.
        unfold SC_SIZE in Ha. exact Ha.
    + left. destruct (inFP_ablocks_fp_inv _ _ Ha) as (p & n & Hpn & Hr). exists p, n. split; [exact (HOb _ Hpn) | exact Hr]. }
(* 0x8e2d8: jal pins_set, through the B kit's program call rule for a callee whose post is apost_baseF *)
pose (KP := fun (ly' : alayout) (S' : astate) (W' : world SEGS) (regs' : bvmap 5 word) (mem' : word -> option byte)
  (md' : Model) => exists (R' : rstate) (r' : Z) (O' : list (Z * Z)),
  pins_set_m (x_R c) (Some u) (Some f) (Some l) v = (R', r') /\
  getr regs' 10 = w64 r' /\ -2 ^ 31 <= r' < 2 ^ 31 /\
  rec_repA B ly' S' (rdW W' mem') R' O' /\
  (forall pn, In pn O' -> In pn (x_O c) \/ ~ In pn (ablocks B (x_ly c) (x_S c))) /\
  (forall pn, In pn (ablocks B (x_ly c) (x_S c)) -> ~ In pn (x_O c) -> In pn (ablocks B ly' S')) /\
  (forall pn, In pn (ablocks B ly' S') -> (In pn (ablocks B (x_ly c) (x_S c)) /\ ~ In pn (x_O c)) \/ In pn O') /\
  blocks_bytes S' <= blocks_bytes (x_S c) + LIVE_PINS_SET (x_R c) (Some u) (Some f) (Some l) v /\
  mo_le MT (x_S c) S' (XM_PINS_SET MT (x_R c) (Some u) (Some f) (Some l) v)).
rewrite (SIGP CS_pins_set) by (unfold cmd_prog_syms; cbn [In]; repeat first [left; reflexivity | right]).
change (cmd_af CS_pins_set) with AF_pins_set.
eapply SRr_bind.
{ refine (cl_callS_pgF (fx := fx) B LAWS (x_W c) (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_pins_set)) PIN_SET_WORDS_STK
    (spZ (x_regs c)) (psw_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [] (x_ly c) (x_S c) mdv 0 PINS_SET_STK
    ((A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp (x_O c))
    (EV_PINS_SET (x_R c)) (-48) (getr (ms_regs ms) 1) [] KP HJ Qsp eq_refl ltac:(lia) HPS0 ltac:(lia) P3' P4' eq_refl
    HRA1 HRA4 HCH _ HFOOT).
  intros HPRE1. eapply SRr_mono.
  { exact (PINS_SET fx (x_ly c) (x_S c) (x_W c) (ms_regs ms) (ms_mem ms) mdv [] p1 p2 p3 vptr u f l v (x_R c) (x_O c)
      HPRE1 HFRM HRODc HROc P10' Hp1r P11' Hp2r P12' Hp3r P13' Hvr BU AU SU ltac:(unfold LMAX; lia)
      BF AF SF ltac:(unfold LMAX; lia) BL AL SL ltac:(unfold LMAX; lia) HVA1 HVA2 HRECc
      ltac:(pose proof (pp_frames B MT c HP); lia) HEVn HLV HMT). }
  cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Gf1 & Gf2 & HJ' & HP' & HK').
  exists fx', ly', S', regs', mem', md'. split; [reflexivity|]. split; [exact Gf1|]. split; [exact Gf2|].
  split; [exact HJ'|]. split; [exact HP' | exact HK']. }
cbv beta. intros W2 c2 Hwle2 (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJc2 & HP2 & HK2).
(* K2 (0x8e2dc): pins_set has returned at fx1; hand INV_K2 to the next segment, taken at fx1, and lift its post
   back to the entry's FP state *)
apply (psw_post_lift fx fx1 B MT c _ _ Hfx).
rewrite HK2pc.
apply (HFK2 fx1 ly2 S2 W2 regs2 mem2 md2).
destruct HK2 as (R1' & r' & O1 & HPS' & H10 & Hr & HREC1 & HO1 & HKB & HCL & HBB & HMLE).
rewrite HPS in HPS'. injection HPS' as <- <-.
assert (HPT : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPR1 HP2).
unfold INV_K2. exists u, f, l, v, R1, r, O1.
split; [rewrite Z.add_0_l in HJ2; exact HJ2|].
split.
{ apply (ta_saved_kept (x_regs c) (rdW (x_W c) memc)); [exact HSAVED|].
  intros x Hx. pose proof HJc2 as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & _).
  rewrite (G1 x ltac:(lia) ltac:(lia) ltac:(intros Hf'; pose proof (HFPlo x Hf'); lia)). apply HSAME. lia. }
split; [rewrite (ta_pres regs1 regs2 2%bv HPT ltac:(ta_cs)); exact Q2|].
split; [rewrite (ta_pres regs1 regs2 3%bv HPT ltac:(ta_cs)); exact Q3|].
split; [rewrite (ta_pres regs1 regs2 4%bv HPT ltac:(ta_cs)); exact Q4|].
split; [rewrite (ta_pres regs1 regs2 8%bv HPT ltac:(ta_cs)); exact Q8|].
split; [rewrite (ta_pres regs1 regs2 20%bv HPT ltac:(ta_cs)); exact Q20|].
split; [intros rr Hrr; rewrite (HPT rr ltac:(unfold acallee_saved; lia)); exact (QHI rr Hrr)|].
split; [exact H10|]. split; [exact Hm|].
split; [exact Hlu|]. split; [exact Hlf|]. split; [exact Hll|]. split; [exact HVL|].
split; [exact HPS|]. split; [exact Hr|]. split; [exact HREC1|].
split; [exact HO1|]. split; [exact HKB|]. split; [exact HCL|]. split; [exact HBB | exact HMLE].
Qed.

End e.
End f.
End d.
