(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of descriptors_get (plugin-hostd/fuzz_command.asan) from the join of
   record()'s arms to the tail jump into answer, after proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v and ACh2.v (a walk
   segment: run, call out by cl_callS, resume) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/descriptors_get_s3.v, with its module names changed; 366 of its 441 lines of code are new or changed and 938 lines of the source are left out. *)
(* Two segment lemmas of sup_host_setting's ASan walk (plugin-hostd/fuzz_command), on the points and statements of
   sup_host_setting_s0.v:
   - hs_seg_al: from AL (0x8b168, back from arg_line) a0 := c, a1 := ntok, the call of arg_i (0x8a238) through
     CL_CALL_PG's form for a callee with an FP-existential post (hs4_cl_call_pgF, from PaFx.v's cl_callS_wideF),
     back at AI (0x8b174) at the FP state fx1 arg_i returned: the rest of the walk is ST_AI at fx1 (it reaches no
     printf-reaching code, so its post is apost_base at fx1), lifted to the statement's apost_baseF at the entry's
     FP state by apost_base_liftF (hs4_post_liftF);
   - hs_seg_ai: from AI the blez on ntok (not taken, ntok >= 1) and loop 1's init (s9 := 0, s5 := the shadow byte
     of s2, s10 := s1, s11 := s4 := s2), to the loop's head L1H at token 0 (0x8b190). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtString RtAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaLibF PaLibG PaLibH PaSB PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1 sup_host_setting_s0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas PaFx.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.

(* the shadow base and its span, the symbolic executor's Bx / Bspan *)
Definition hs4_Bx : sv := SOff 23 0.
Definition hs4_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).

(* a run that writes nothing keeps every byte *)
Lemma hs4_view_nil : forall E (H : word -> bool) m m',
  frame_of E [] (mrestrict H m) (mrestrict H m') -> forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E H m m' Hf a. unfold aview, mbyte. rewrite (Hf (Z_to_bv 64 a)); [reflexivity|].
intros (r & Hr & _). destruct Hr.
Qed.

Lemma hs4_aval_kept : forall (rd rd' : reader) a n v,
  (forall b, rd' b = rd b) -> aval_mem rd a n v -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Heq H k Hk. rewrite Heq. exact (H k Hk). Qed.

Lemma hs4_frame_kept : forall (rd rd' : reader) sp0 regs,
  (forall b, rd' b = rd b) -> hs_frame rd sp0 regs -> hs_frame rd' sp0 regs.
Proof. intros rd rd' sp0 regs Heq H j r Hj. exact (hs4_aval_kept rd rd' _ _ _ Heq (H j r Hj)). Qed.

(* s5 := s7 + (s2 >> 3), the shadow byte's address, in the executor's operand order *)
Lemma hs4_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))))). f_equal.
change (U E (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SRL (SOff n 0) (SLit 3))) = sb + v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite ?(zcanon_small v), ?(zcanon_small (v / 8)), ?(zcanon_small sb) by lia. rewrite zcanon_small by lia. lia.
Qed.

(* the token array lies below the allocator's ceiling: in a side-stack frame or in a live block *)
Lemma hs4_ptok_range : forall x, hs_cx B MT x -> 4096 <= i_ptok x < 2 ^ 63.
Proof.
intros x CX.
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & HNT & _ & _ & _ & HTA & _).
pose proof HPRE as (HAR0 & _). pose proof asan_consts as (C1 & _).
destruct HTA as [((cid & pos & Hin & _ & _ & Hlo & Hhi) & _) | ((p & q & Hin & Hlo & Hhi) & _)].
- destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HAR0 Hin) as (F1 & F2 & _). lia.
- destruct (al_blocks _ _ LAWS _ _ _ _ _ p q HAR0 Hin) as (_ & B1 & B2 & _ & _ & _ & B3).
  pose proof (req_size_pos q ltac:(lia)) as [_ Hq]. lia.
Qed.

(* the entry facts at the FP state fx1 a call returned: only the rounding-mode conjunct names the FP state *)
Lemma hs4_cx_fx : forall x (fx1 : YK11.FPState), fxrel fx fx1 -> hs_cx (fx := fx) B MT x -> hs_cx (fx := fx1) B MT x.
Proof.
intros x fx1 Hfx CX. unfold hs_cx in *. cbv zeta in *.
destruct CX as (C1 & C2 & C3 & C4 & C5).
exact (conj C1 (conj C2 (conj C3 (conj (fxrel_frm0 fx fx1 C4 Hfx) C5)))).
Qed.

(* the post of the points from AI on, at the FP state fx1 arg_i returned, is the statement's post *)
Lemma hs4_post_liftF : forall x (fx1 : YK11.FPState) (W0 : world SEGS) c, fxrel fx fx1 ->
  SRr SEGS W0 c (hs_post (fx := fx1) B MT x) -> SRr SEGS W0 c (hs_postF (fx := fx) B MT x).
Proof.
intros x fx1 W0 c Hfx H. unfold hs_postF. unfold hs_post in H. cbv zeta in H |- *.
exact (srr_apost_base_liftF (fx := fx) SEGS fx1 W0 c B SUP_HOST_SETTING_STK _ (i_regs x) (i_ly x) (i_S x) (i_W x)
  (i_mem x) (i_md x) _ (hs_Q B MT x) Hfx H).
Qed.

(* CL_CALL_PG's form for a callee whose post is apost_baseF: PaFx.v's cl_callS_wideF with the inner footprint
   widened to the program's statics, as sup_host_setting.v's hs_cl_call_pg from PaNoChain.v's cl_callS_wide *)
Lemma hs4_cl_call_pgF : forall W (regsc : bvmap 5 word) memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1
  (o : Z) raw ch1 (K : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memc mdc k ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  getr regsc 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
  achain lyc (aview SEGS (w_H W) memc) (sp0 + o) (s0Z regsc) ch1 ->
  (afn_pre SEGS B STK1 lyc Sc W regsc memc mdc ch1 ->
   SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
   (fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
    (forall k : bv 5, bv_unsigned k <> 10 -> Sem.reg_get (@fp_regs fx1) k = Sem.reg_get (@fp_regs fx) k) /\
    (@fp_csr fx1 = @fp_csr fx \/ Z.land (Z.shiftr (bv_unsigned (@fp_csr fx1)) 5) 7 = 0) /\
    ajournal SEGS B STK1 (spZ regsc) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
    aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2)) ->
  (forall a, inFP FP1 a -> (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n)
    \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a
    \/ (inFP FP a /\ Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a)) ->
  SRr SEGS W (mkCfg (@mkst fx regsc pc memc (seg_rom SEGS)) mdc)
  (fun W2 c2 => exists (fx1 : YK11.FPState) ly2 S2 regs2 mem2 md2, fxrel fx fx1 /\
   c2 = mkCfg (@mkst fx1 regs2 raw mem2 (seg_rom SEGS)) md2 /\
   ajournal SEGS B STK sp0 FP ly S W0 mem md own ly2 S2 W2 mem2 md2 (k + EV1) /\
   ajournal SEGS B STK1 (sp0 + o) FP1 lyc Sc W memc mdc [] ly2 S2 W2 mem2 md2 EV1 /\
   aregs_preserved regsc regs2 /\ K ly2 S2 W2 regs2 mem2 md2).
Proof.
intros W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw ch1 K
  HJ Hsp Hal Hneg Hs1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee HF.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & _).
apply (cl_callS_wideF (fx := fx) B LAWS W regsc memc pc STK sp0 FP ly S W0 mem md own lyc Sc mdc k STK1 FP1 EV1 o raw
  ch1 K HJ Hsp Hal Hneg Hs1 Hbud Hgp Htp Hra Hraw Hra4 Hch Hcallee).
- intros a Ha. unfold awr_byte, awr_prog_or_caller.
  destruct (HF a Ha) as [H1 | [H2 | H3]].
  + right; left. exact H1.
  + right; right; left. exact H2.
  + right; right; right; right; left. exact H3.
- intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso.
  destruct (HF a Ha) as [(_ & b & n & Hb & Hr) | [(b & n & Hb & _ & Hr) | (_ & _ & Himg)]].
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & Hbc & _). lia.
  + destruct (al_blocks _ _ LAWS _ _ _ _ _ b n HAR Hb) as (_ & _ & Hbc & _). lia.
  + pose proof (pa_img_range a Himg). lia.
Qed.

Definition hs4_pair_dec (a b : Z * Z) : {a = b} + {a <> b}.
Proof. decide equality; apply Z.eq_dec. Defined.

Lemma hs4_wl_nonneg : forall l, 0 <= hs_words_len l.
Proof. intros l. unfold hs_words_len. induction l as [|w l IH]; cbn [fold_right]; lia. Qed.

(* a callee keeps the frame: the 13 saved registers lie in [sp0 - 104, sp0) *)
Lemma hs4_frame_kept_on : forall (rd rd' : reader) sp0 regs,
  (forall b, sp0 - 104 <= b < sp0 -> rd' b = rd b) -> hs_frame rd sp0 regs -> hs_frame rd' sp0 regs.
Proof.
intros rd rd' sp0 regs Heq H j r Hj k Hk.
assert (Hj13 : (j < length HS_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
change (length HS_SAVED) with 13%nat in Hj13.
rewrite Heq by lia. exact (H j r Hj k Hk).
Qed.

(* the slot is a call of g_rec's table or record.spill, as arg_i's contract asks *)
Lemma hs4_slot_cases : forall R,
  (exists i, 0 <= i < REC_CALLS_MAX /\ hs_slot R = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ hs_slot R = A_REC_SPILL.
Proof.
intros R. unfold hs_slot. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [H|H].
- left. exists (Z.of_nat (length (r_calls R))). split; [unfold REC_CALLS_MAX; lia | reflexivity].
- right. reflexivity.
Qed.

(* the slot's bytes are bytes of the recorder's two statics, both in the whole call's footprint *)
Lemma hs4_slot_rec : forall R a, hs_slot R <= a < hs_slot R + CALL_SIZE -> hs_in_rec a.
Proof.
intros R a Ha. destruct (hs_slot_bounds R) as (B1 & B2 & _ & [B4 | B4]); unfold hs_in_rec; [left | right];
  unfold A_G_REC, REC_SIZE, OFF_CALLS, CALL_SIZE, OFF_ANSWER, A_REC_SPILL, SC_SIZE in *; lia.
Qed.

Lemma hs4_rec_fp : forall O a, hs_in_rec a -> inFP (hs_FP O) a /\ Exists (in_zr a) recb_PG.
Proof.
intros O a [Ha | Ha]; split.
- exists (A_G_REC, A_G_REC + REC_SIZE). split; [apply in_eq | cbn [fst snd]; lia].
- apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [apply in_cons, in_eq | cbn [fst snd]; lia].
- apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* the read-only bytes lie outside the whole call's footprint (arodata_ok_journalP's premise) *)
Lemma hs4_ro_off_fp : forall x, hs_cx B MT x -> forall a, in_roP SEGS RLO RHI a -> ~ inFP (hs_FP (i_O x)) a.
Proof.
intros x CX a Hro (r & Hr & Ha).
pose proof CX as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HREP0 & _).
pose proof HPRE as (HAR0 & _).
destruct (hh_ro_prog_apart B MT HH a Hro) as [Himg Hnpg].
unfold hs_FP in Hr. destruct Hr as [<- | [<- | Hr]].
- apply Hnpg. apply Exists_cons_hd. unfold in_zr. cbn [fst snd] in *. lia.
- apply Hnpg. apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd] in *. lia.
- unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p q] & <- & Hpq). cbn [fst snd] in Ha.
  destruct (hs_rec_own B _ _ _ _ _ HREP0 (p, q) Hpq) as [Hin _].
  exact (blk_img SEGS B LAWS _ _ _ _ _ p q a HAR0 Hin Ha Himg).
Qed.

(* a heap block is apart from a range of image bytes *)
Lemma hs4_heap_apart : forall ly S (W : world SEGS) mem md p n lo len,
  AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < len ->
  (forall a, lo <= a < lo + len -> in_img SEGS a) -> iv_apart p n lo len.
Proof.
intros ly S W mem md p n lo len HAR Hin Hlen Himg. unfold iv_apart.
destruct (al_blocks _ _ LAWS _ _ _ _ _ p n HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (Z_le_gt_dec (p + n) lo) as [H|H]; [left; exact H|].
destruct (Z_le_gt_dec (lo + len) p) as [H'|H']; [right; exact H'|]. exfalso.
pose proof (req_size_pos n ltac:(lia)) as Hq.
apply (blk_img SEGS B LAWS ly S W mem md p n (Z.max p lo) HAR Hin); [lia | apply Himg; lia].
Qed.

Lemma hs_seg_ai : forall x, ST_L1H B MT x 0 -> ST_AI B MT x.
Proof.
intros x L1. unfold ST_AI.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 CX MID SB0 SB1 REP RG R18.
pose proof CX as (HPRE & HROD & HRO & HROIN & HGRD & H10 & H11 & H12 & HNT & _).
pose proof (hs4_ptok_range x CX) as HPT.
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R22 & R23) & R19 & R24).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HBA).
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E
  (mkSS HS_AI sr_atoms [] None (mkFacts [(9%nat, mkAF 1 64 0); (23%nat, mkAF HS_SB HS_SB 0)] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_AI)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 9%nat 9%bv eq_refl), (EE 23%nat 23%bv eq_refl), R9, R23. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs4_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b174 .. 0x8b18c: blez s1 (ntok >= 1, not taken), loop 1's init; stop at the loop's head *)
paj_run_to_tok RUNTO HS HJ SHOK hs4_Bspan HS_L1H.
{ apply awr_ok_nil. }
pmkst HS.
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
pose proof (hs4_view_nil E (w_H Wc) memc (ms_mem ms) HFr) as KEQ.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8.
prreg HS (9%bv : bv 5) P9. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23. prreg HS (19%bv : bv 5) P19.
prreg HS (24%bv : bv 5) P24. prreg HS (18%bv : bv 5) P18. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
prreg HS (27%bv : bv 5) P27. prreg HS (20%bv : bv 5) P20.
lazymatch type of HS with st_ok_pi _ _ _ ?ss (restrict _ _) =>
  pose proof (st_ok_pi_restrict_reg (w_H Wc) E ss ms (21%bv : bv 5) HS) as P21;
  let e := eval vm_compute in (sr_get (ss_regs ss) (21%bv : bv 5)) in change (sr_get (ss_regs ss) (21%bv : bv 5)) with e in P21 end.
rewrite (hs4_denot_shx E 18 23 (i_ptok x) HS_SB) in P21;
  [| rewrite (EE 18%nat 18%bv eq_refl); exact R18 | rewrite (EE 23%nat 23%bv eq_refl); exact R23 | lia | unfold HS_SB; lia].
refine (L1 lyc Sc Wc (ms_mem ms) _ (ms_regs ms) k O1 Rest b0 b1 _ CX _ SB0 SB1 _ _ _ _ _ _ _ _).
- lia.
- refine (conj HJ (conj Hk (conj HMLE (conj HBB (conj _ HBA))))).
  exact (hs4_frame_kept _ _ _ _ KEQ HFR).
- exact (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ REP (fun a _ => KEQ a)
    (fun pn H => proj1 (hs_rec_own B _ _ _ _ _ REP pn H))).
- split; [split|split].
  + rewrite P2, (EE 2%nat 2%bv eq_refl). exact R2.
  + rewrite P3, (EE 3%nat 3%bv eq_refl). split; [exact R3|].
    rewrite P4, (EE 4%nat 4%bv eq_refl). split; [exact R4|].
    rewrite P8, (EE 8%nat 8%bv eq_refl). split; [exact R8|].
    rewrite P9, (EE 9%nat 9%bv eq_refl). split; [exact R9|].
    rewrite P22, (EE 22%nat 22%bv eq_refl). split; [exact R22|].
    rewrite P23, (EE 23%nat 23%bv eq_refl). exact R23.
  + rewrite P19, (EE 19%nat 19%bv eq_refl). exact R19.
  + rewrite P24, (EE 24%nat 24%bv eq_refl). exact R24.
- rewrite P18, (EE 18%nat 18%bv eq_refl). exact R18.
- rewrite P25. reflexivity.
- rewrite P26, (EE 9%nat 9%bv eq_refl), R9, Nat.sub_0_r. reflexivity.
- rewrite P27, (EE 18%nat 18%bv eq_refl), R18. unfold w64. f_equal. lia.
- rewrite P20, (EE 18%nat 18%bv eq_refl), R18. unfold w64. f_equal. lia.
- rewrite P21. unfold w64. f_equal. replace (i_ptok x + 8 * Z.of_nat 0) with (i_ptok x) by lia. reflexivity.
Qed.

(* AI is taken at every FP state: arg_i returns at some fx1 (its post is apost_baseF) *)
Lemma hs_seg_al : forall x, (forall fx1 : YK11.FPState, ST_AI (fx := fx1) B MT x) -> ST_AL (fx := fx) B MT x.
Proof.
intros x AI. unfold ST_AL.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 CX MID SB0 REP RG R18.
pose proof CX as (HPRE & HROD & HRO & HRM & HGRD & H10 & H11 & H12 & HNT & HLINE & Hp0 & Hp8 & HTA & HLPS & HPS &
  HTOKS & HWL & HREP0 & HFRM & HEV & HLIVE & HMO & HTAIL).
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof RG as ((R2 & R3 & R4 & R8 & R9 & R22 & R23) & R19 & R24).
pose proof MID as (HJ & Hk & HMLE & HBB & HFR & HBA).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (hs_slot_bounds (i_R x)) as (SL1 & SL2 & _ & _).
assert (HSTK : 112 + ARG_I_STK <= SUP_HOST_SETTING_STK) by (unfold SUP_HOST_SETTING_STK; lia).
assert (HAIS : 0 <= ARG_I_STK) by (unfold ARG_I_STK, ESTACK, XSTRDUP_STK, ASTACK; lia).
assert (HPSB : as_prog_static B = recb_PG) by (rewrite (ts_prog B (hh_HB B MT HH)); reflexivity).
pose proof (hh_RRO B MT HH) as RRO.
pose (E := Eimg (Ereg regs1 [])).
assert (HEI : img_env VAL A_LIM E) by apply Eimg_env.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r).
{ intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (HS : st_ok_pi SEGS VAL E (mkSS HS_AL sr_atoms [] None (mkFacts [(23%nat, mkAF HS_SB HS_SB 0)] [] []))
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + HS_AL)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - exact (regs_ok_Eimg_Ereg regs1 []).
  - reflexivity.
  - constructor.
  - exact I.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (EE 23%nat 23%bv eq_refl), R23. unfold w64.
    rewrite !unsigned_lit_small by (unfold HS_SB; lia). rewrite Z.pow_0_r, !Z.mod_1_r. unfold HS_SB. lia. }
assert (SHOK : sh_ok SEGS hs4_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
clearbody E.
(* 0x8b168 .. 0x8b170: a0 := c, a1 := ntok, the call of arg_i *)
paj_run_tok RUN HS HJ SHOK hs4_Bspan.
{ apply awr_ok_nil. }
pmkst HS.
set (mdv := with_vm_backing (m_vm_lazy mdc) mat mdc) in *. clearbody mdv.
pose proof (hs4_view_nil E (w_H Wc) memc (ms_mem ms) HFr) as KEQ.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
prreg HS (24%bv : bv 5) P24.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3. rewrite (EE 4%nat 4%bv eq_refl) in P4.
rewrite (EE 8%nat 8%bv eq_refl) in P8. rewrite (EE 9%nat 9%bv eq_refl) in P9.
rewrite (EE 8%nat 8%bv eq_refl), R8 in P10. rewrite (EE 9%nat 9%bv eq_refl), R9 in P11.
rewrite (EE 18%nat 18%bv eq_refl) in P18. rewrite (EE 19%nat 19%bv eq_refl) in P19.
rewrite (EE 22%nat 22%bv eq_refl) in P22. rewrite (EE 23%nat 23%bv eq_refl) in P23.
rewrite (EE 24%nat 24%bv eq_refl) in P24.
assert (Qsp : spZ (ms_regs ms) = spZ (i_regs x) + -112).
{ unfold spZ at 1. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
assert (HAF : cmd_af CS_arg_i = AF_arg_i) by (vm_compute; reflexivity).
assert (SIGAI : SIG CS_arg_i = BASE + AF_arg_i).
{ rewrite (hh_sigp B MT HH CS_arg_i ltac:(unfold cmd_prog_syms; repeat (first [left; reflexivity | right]))), HAF.
  reflexivity. }
rewrite SIGAI.
(* arg_i's premises at the call *)
pose proof HJ as (HARc & _ & _ & _ & _ & HFRSc & HNEVc & _).
assert (HRODc : arodata_okP SEGS RLO RHI B (rdW Wc (ms_mem ms)))
  by exact (arodata_ok_journalP SEGS RLO RHI (hh_RELRO_IMG B MT HH) B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ
    (hs4_ro_off_fp x CX) HROD).
assert (HROc : cmd_ro_ok (rdW Wc (ms_mem ms))) by exact (hh_ro_ok_of_aro B MT HH _ _ _ _ _ HARc HRODc).
assert (HFRc : Z.of_nat (length (frames Sc)) <= 8) by (rewrite HFRSc; exact HFRM).
destruct (hs_rec_last B _ _ _ _ _ _ REP) as (P0 & HCA & _).
pose proof HCA as (_ & _ & _ & _ & HNA & _).
assert (HNA1 : aval_mem (rdW Wc (ms_mem ms)) (hs_slot (i_R x) + CALL_OFF_NARGS) 4 1)
  by exact (hs4_aval_kept _ _ _ _ _ KEQ HNA).
assert (HEVc : st_nev Sc + EV_ARG_I <= EV_MAX).
{ unfold EV_SUP_HOST_SETTING, hs_k0, EV_ARG_I, EV_XSTRDUP in *. lia. }
assert (HLIVEc : blocks_bytes Sc + LIVE_ARG_I (Z.of_nat (length (i_toks x))) <= LIVE_MAX).
{ pose proof (hs4_wl_nonneg (i_toks x)). cbn [bsum fold_right] in HBB.
  unfold LIVE_SUP_HOST_SETTING, LIVE_XSTRDUP in HLIVE. lia. }
assert (HMOc : mo_ok MT Sc (XM_ARG_I MT (Z.of_nat (length (i_toks x))))).
{ pose proof (hh_MTL B MT HH) as ML.
  apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x))
    (hs_m0 MT x + XM_ARG_LINE MT (i_line x)) _ ML HMO HMLE).
  - unfold XM_ARG_I, XM_XSTRDUP. apply (mo_malloc_nonneg MT ML). lia.
  - unfold XM_SUP_HOST_SETTING, hs_m0.
    pose proof (mo_malloc_nonneg MT ML (hs_words_len (i_toks x) + 1) ltac:(pose proof (hs4_wl_nonneg (i_toks x)); lia)).
    pose proof (mo_malloc_nonneg MT ML (Z.of_nat (length (join_sp (i_toks x))) + 1) ltac:(lia)).
    pose proof (mo_free_nonneg MT ML). unfold XM_XSTRDUP. lia. }
(* arg_i writes c->nargs and c->args[1] *)
pose (FP1 := [(hs_slot (i_R x) + CALL_OFF_NARGS, hs_slot (i_R x) + CALL_OFF_NARGS + 4);
  (hs_slot (i_R x) + CALL_OFF_ARGS + 8 * 1, hs_slot (i_R x) + CALL_OFF_ARGS + 8 * 1 + 8)]).
assert (HFP1 : forall a, inFP FP1 a -> hs_slot (i_R x) <= a < hs_slot (i_R x) + CALL_SIZE).
{ intros a (r & Hr & Ha). unfold FP1 in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Ha;
  unfold CALL_OFF_NARGS, CALL_OFF_ARGS, CALL_SIZE in *; lia. }
(* arg_i reaches the snprintf wrapper: it returns at some fx1 (CL_CALL_PG's form with apost_baseF's FP clauses) *)
eapply SRr_bind.
{ eapply (hs4_cl_call_pgF Wc (ms_regs ms) (ms_mem ms) (Z_to_bv 64 (BASE + AF_arg_i)) SUP_HOST_SETTING_STK (spZ (i_regs x))
    (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc _ k ARG_I_STK FP1 EV_ARG_I (-112)
    (getr (ms_regs ms) 1) [] _ HJ Qsp eq_refl ltac:(lia) HAIS ltac:(lia)).
  - rewrite P3, R3. exact Hgp.
  - rewrite P4, R4. exact Htp.
  - reflexivity.
  - rewrite P1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite P1, unsigned_lit_small by lia. lia.
  - unfold achain. left. split; [left | reflexivity]. unfold s0Z. rewrite P8, R8. unfold w64.
    rewrite unsigned_lit_small by (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia.
  - intros HPRE1.
    exact (hh_arg_i B MT HH fx lyc Sc Wc (ms_regs ms) (ms_mem ms) _ [] (hs_slot (i_R x)) (Z.of_nat (length (i_toks x)))
      1 HPRE1 HRM HFRc HRODc HROc P10 P11 ltac:(lia) (hs4_slot_cases (i_R x)) HNA1 ltac:(unfold REC_ARGS_MAX; lia)
      HEVc HLIVEc HMOc).
  - intros a Ha. right; right.
    destruct (hs4_rec_fp (i_O x) a (hs4_slot_rec (i_R x) a (HFP1 a Ha))) as [Hfp Hpg].
    split; [exact Hfp|]. split; [rewrite HPSB; exact Hpg | exact (hh_prog_img B MT HH a Hpg)]. }
(* back at 0x8b174, at the FP state fx1 arg_i returned: the rest is ST_AI at fx1, its post lifted to the entry's *)
cbv beta. intros W2 c2 Hwle (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx & -> & HJ2 & HJ2c & HP2 & HK2).
apply (hs4_post_liftF x fx1 _ _ Hfx).
cbv zeta in HK2.
destruct HK2 as (HBB2 & HMLE2 & [(Hm6 & _) | (_ & p & Hp4096 & HPERM2 & HAPART & HNA2 & HARG2 & HSTR2)]);
  [unfold REC_ARGS_MAX in Hm6; lia|].
pose proof HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & K1 & K2 & K3 & _).
pose proof (dec_length (Z.of_nat (length (i_toks x))) ltac:(lia)) as HDL.
assert (HIN2 : In (p, Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1) (ablocks B ly2 S2))
  by exact (Permutation_in _ (Permutation_sym HPERM2) (in_eq _ _)).
rewrite P1.
refine (AI fx1 ly2 S2 W2 mem2 md2 regs2 (k + EV_ARG_I) O1 Rest b0
  (p, Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1) (hs4_cx_fx x fx1 Hfx CX) _ SB0 eq_refl _ _ _).
- refine (conj HJ2 (conj _ (conj _ (conj _ (conj _ _))))).
  + unfold hs_k2, EV_ARG_I, EV_XSTRDUP in *. lia.
  + exact (mle_station MT _ _ _ _ _ (hh_MTL B MT HH) HMLE HMLE2).
  + rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPERM2), bsum_cons, <- (blocks_bytes_bsum B lyc Sc).
    cbn [bsum fold_right snd] in HBB |- *. lia.
  + apply (hs4_frame_kept_on (rdW Wc memc)); [|exact HFR].
    intros b Hb. rewrite <- (KEQ b). apply K1; [lia | lia |].
    intros Hin. apply HFP1 in Hin. unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia.
  + pose proof HBA as (BA1 & BA2 & BA3 & BA4 & BA5 & BA6 & BA7).
    split; [|split; [exact BA2|split; [exact BA3|split; [exact BA4|split; [exact BA5|split; [|exact BA7]]]]]].
    * eapply Permutation_trans; [exact HPERM2|]. eapply Permutation_trans; [apply perm_skip; exact BA1|].
      cbn [app]. apply perm_swap.
    * intros pn [<- | [<- | []]] Hin; [exact (BA6 b0 (or_introl eq_refl) Hin)|].
      destruct (in_dec hs4_pair_dec (p, Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1) (i_O x))
        as [Ho | Hno]; [exact Ho|]. exfalso.
      pose proof (Permutation_in _ (Permutation_sym BA1) (in_cons b0 _ _ (BA3 _ Hin Hno))) as Hc.
      pose proof (proj1 (Forall_forall _ _) HAPART _ Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- assert (REP2 : rec_repA B ly2 S2 (rdW W2 mem2)
    (rec_record (i_R x) REC_HOST_SETTING ([canon (i_line x)] ++ [dec (Z.of_nat (length (i_toks x)))]))
    ((O1 ++ [b0]) ++ [(p, Z.of_nat (length (dec (Z.of_nat (length (i_toks x))))) + 1)])).
  { apply (hs_rec_arg B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2));
      [exact REP | cbn; lia | exact HNA2 | exact HARG2 | | lia | exact HSTR2 | unfold LMAX; lia | unfold LMAX; lia
      | exact HIN2 | | | |].
    - intros a Ha Hn1 Hn2. rewrite <- (KEQ a).
      change (Z.of_nat (length [canon (i_line x)])) with 1 in Hn2.
      assert (HnF : ~ inFP FP1 a).
      { intros (r & Hr & Hrq). unfold FP1 in Hr. destruct Hr as [<- | [<- | []]]; cbn [fst snd] in Hrq;
        [apply Hn1 | apply Hn2]; lia. }
      destruct Ha as [Hrec | ([q m] & Hpn & Hpa)].
      + pose proof (hs4_rec_fp (i_O x) a Hrec) as [_ Hpg].
        assert (Hpg' : Exists (in_zr a) (as_prog_static B)) by (rewrite HPSB; exact Hpg).
        destruct (prog_static_sep B a (ts_ok B (hh_HB B MT HH)) Hpg') as (Hno & Hne & _).
        apply K3; [exact (hh_prog_img B MT HH a Hpg) | exact Hno | exact Hne |].
        apply fp_spares_closed; [| exact HnF]. apply sink_closed_pos. unfold FP1.
        apply Forall_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS, CALL_OFF_NARGS in *; lia|].
        apply Forall_cons; [cbn [fst]; unfold A_G_REC, OFF_CALLS, CALL_OFF_ARGS in *; lia|].
        apply Forall_nil.
      + cbn [fst snd] in Hpa.
        destruct (hs_rec_own B _ _ _ _ _ REP (q, m) Hpn) as [Hinc _].
        assert (Hin2 : In (q, m) (ablocks B ly2 S2))
          by exact (Permutation_in _ (Permutation_sym HPERM2) (in_cons _ _ _ Hinc)).
        destruct (al_blocks _ _ LAWS _ _ _ _ _ q m HARc Hinc) as (_ & _ & _ & _ & _ & _ & Hm).
        pose proof (req_size_pos m ltac:(lia)) as [_ Hrq].
        replace a with (q + (a - q)) by lia.
        apply (K2 q m (a - q)); [exact Hinc | exact Hin2 | lia | replace (q + (a - q)) with a by lia; exact HnF].
    - intros pn Hpn.
      exact (Permutation_in _ (Permutation_sym HPERM2) (in_cons _ _ _ (proj1 (hs_rec_own B _ _ _ _ _ REP pn Hpn)))).
    - apply Forall_forall. intros q Hq.
      exact (proj1 (Forall_forall _ _) HAPART q (proj1 (hs_rec_own B _ _ _ _ _ REP q Hq))).
    - apply (hs4_heap_apart ly2 S2 W2 mem2 md2 p _ A_G_REC REC_SIZE HAR2 HIN2); [unfold REC_SIZE; lia|].
      intros a Ha. apply (hh_prog_img B MT HH). apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
    - apply (hs4_heap_apart ly2 S2 W2 mem2 md2 p _ A_REC_SPILL SC_SIZE HAR2 HIN2); [unfold SC_SIZE; lia|].
      intros a Ha. apply (hh_prog_img B MT HH). apply Exists_cons_tl, Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia. }
  rewrite <- app_assoc in REP2. exact REP2.
- split; [split|split].
  + transitivity (getr (ms_regs ms) 2); [exact (HP2 2 ltac:(unfold acallee_saved; lia)) | rewrite P2; exact R2].
  + split; [transitivity (getr (ms_regs ms) 3); [exact (HP2 3 ltac:(unfold acallee_saved; lia)) | rewrite P3; exact R3]|].
    split; [transitivity (getr (ms_regs ms) 4); [exact (HP2 4 ltac:(unfold acallee_saved; lia)) | rewrite P4; exact R4]|].
    split; [transitivity (getr (ms_regs ms) 8); [exact (HP2 8 ltac:(unfold acallee_saved; lia)) | rewrite P8; exact R8]|].
    split; [transitivity (getr (ms_regs ms) 9); [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | rewrite P9; exact R9]|].
    split; [transitivity (getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | rewrite P22; exact R22]|].
    transitivity (getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | rewrite P23; exact R23].
  + transitivity (getr (ms_regs ms) 19); [exact (HP2 19 ltac:(unfold acallee_saved; lia)) | rewrite P19; exact R19].
  + transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | rewrite P24; exact R24].
- transitivity (getr (ms_regs ms) 18); [exact (HP2 18 ltac:(unfold acallee_saved; lia)) | rewrite P18; exact R18].
Qed.

End e.
End f.
End d.
