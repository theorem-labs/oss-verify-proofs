(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the second segment of check_reply's walk (fuzz_command.asan, 0x86d78), from the
   memchr call 0x86ef8 to the return of sup_reply_code 0x86f18, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh1.v..ACh8.v, AChc.v and ACke.v (cgif_close's call steps: cl_callS, the state
   after the return) at c8557374ad2e.

   The pieces: 0x86ef8 jal memchr (the reply holds no NUL, so the wrapper returns 0: the not-found contract
   through PaArt.v's aj_art_at); 0x86efc bnez a0 (not taken); 0x86f00 mv a0,s3; 0x86f04 jal check_reply_answer
   (cl_callS); 0x86f08 the inline check of &g_rec.reply (a shadow entry of g_rec makes it a literal 0); 0x86f10
   ld a0,928(s9); 0x86f14 jal sup_reply_code (cl_callS), whose return point 0x86f18 is CR_CODE_stmt's.
   After each call the mid-walk invariant cr_mid and the registers cr_regs_at are rebuilt from the callee's journal
   (the frame (1, pos) is among the caller's frames, the saved registers lie above the callee's stack pointer, g_rec
   is a program static), and the walk is seeded again with check_reply_sd.v's cr_seed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s2.v, with its module paths and module names changed; 330 of its 373 lines of code are new or changed and 542 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/m_file_s_kign_1.v; 174 of its 267 lines of code are new or changed and 280 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of LEN (0x86490, the header strip's end):
   `mv s7,s6` (s7 := line + 1), `sub s6,s4,s10` (s6 := be - b), `blt s6,8` (0x8649c) to REF2 0x8652c when the
   header is shorter than 8 bytes, else ieq(b, 7, "segment") (`jal ieq` 0x864b0, through m_file_iq.v's shared
   mf_ieq_call) returning to RIEQ 0x864b4. No byte is written before the call. The HDRA segment lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e m_file_s_hdra_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the engine's s4 - s10 (`sub` as s4 + s10 * -1), when it does not wrap (m_file_s_hdra_7.v hda7_U_subm) *)
Lemma hda10_U_subm : forall E x y, 0 <= U E x - U E y < M64 ->
  U E (SAlu ALU_ADD x (SMd M_MUL y (SLit (-1)))) = U E x - U E y.
Proof.
intros E x y H. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1).
unfold zcanon, M64 in *. rewrite Zplus_mod_idemp_r.
replace (U E x + U E y * (2 ^ 64 - 1)) with ((U E x - U E y) + U E y * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* a signed compare of a small value with a small literal (fuzz_command chain_words_s1.v cw1_lt_atom's form) *)
Lemma hda10_lt_lit : forall E x z, 0 <= U E x < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E x) (sv_denot E (SLit z)) = (U E x <? z).
Proof.
intros E x z Hx Hz. cbn [branch_taken]. rewrite bv_lts_signed.
change (bv_signed (sv_denot E x)) with (Sg E x). change (bv_signed (sv_denot E (SLit z))) with (Sg E (SLit z)).
rewrite S_of_U, S_SLit. rewrite !swrap64_id by (unfold half64; lia). reflexivity.
Qed.
(* the line's facts across the last token run (no byte changed) *)
Ltac hda10_carry HLo HLn :=
  lazymatch goal with
  | HFr : frame_of _ _ (mrestrict (w_H ?W) ?m0) (mrestrict (w_H ?W) ?m1),
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?m1 ?md1 _ |- _ =>
    pose proof (hda_line_carry _ _ _ _ _ _ m0 _ m1 md1 _ _ _ _ _ _ HLo HJ
      (hda_frame_ro _ _ (w_H W) m0 m1 HFr ltac:(vm_compute; reflexivity))) as HLn;
    clear HFr; try (match goal with HF : frame_of _ _ m0 m1 |- _ => clear HF end)
  end.
(* sv_denot through U *)
Lemma hda10_denot_U : forall E x, sv_denot E x = Z_to_bv 64 (U E x).
Proof. intros E x. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* ieq_pre's bytes: a list Z read through an ASan reader, as list byte, and back (m_file_s_kign_t.v) *)
Lemma hda10_zs_zb : forall l, Forall (fun z => 0 <= z < 256) l -> seg_spec.zs (seg_spec.zb l) = l.
Proof.
induction l as [|x r IH]; intros H; [reflexivity|]. apply Forall_cons_iff in H as [Hx Hr].
unfold seg_spec.zs, seg_spec.zb in *. cbn [map]. rewrite IH by exact Hr. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. exact Hx.
Qed.
Lemma hda10_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l /\
  Forall (fun z => 0 <= z < 256) l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  destruct (aview_byte segs H mem _ _ (HZ i Hi)) as (_ & _ & _ & R). exact R. }
split; [|split; [exact (hda10_zs_zb l HR) | exact HR]].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom (m_file_s_kign_1.v ki_st_reg) *)
Lemma hda10_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstA.STK_ieq SegInstA.RLO_A SegInstA.RHI_A.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Hypothesis SIGP : seg_sig_prog.
(* the text left's sub-range [o, o + n) inside the line: its bytes as list byte, addressable, in the text block
   (m_file_s_kign_1.v ki_slice_facts) *)
Lemma hda10_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos lowsh mcc -> mf_loop v Wc memc mcc cur line p rest ->
  (o + n <= length rest)%nat ->
  sa_bytes (rdW Wc memc) (p + Z.of_nat o) (seg_spec.zb (firstn n (skipn o rest))) /\
  seg_spec.zs (seg_spec.zb (firstn n (skipn o rest))) = firstn n (skipn o rest) /\
  Z.of_nat (length (seg_spec.zb (firstn n (skipn o rest)))) = Z.of_nat n /\
  sa_addr (rdW Wc memc) (p + Z.of_nat o) (Z.of_nat n) /\ sa_heap B lyc Sc (p + Z.of_nat o) (Z.of_nat n) /\
  p + Z.of_nat o <> 0.
Proof.
intros v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n CX CORE LOOP Hon.
pose proof LOOP as (L1 & L2 & L3 & ((LZ & LN) & LT) & LADDR & _).
pose proof CORE as (HJ & _). pose proof HJ as (HAR & _).
assert (HZ : sa_zs (rdW Wc memc) (p + Z.of_nat o) (firstn n (skipn o rest))).
{ intros i Hi. rewrite length_firstn, length_skipn in Hi.
  replace (p + Z.of_nat o + Z.of_nat i) with (p + Z.of_nat (o + i)) by lia.
  rewrite (LZ (o + i)%nat) by (rewrite length_app; cbn [length]; lia).
  f_equal. rewrite nth_firstn. destruct (Nat.ltb_spec i n) as [Hlt|Hge]; [|lia].
  rewrite nth_skipn. apply app_nth1. lia. }
destruct (hda10_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB & _).
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos lowsh mcc CX CORE) as (bt & mt & Hin & Hb & He).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bt mt HAR Hin) as (_ & Hbt4096 & Hbtceil & _ & _ & _ & Hmt).
pose proof (req_size_pos mt ltac:(lia)) as [_ Hrt].
assert (Hlen : length (seg_spec.zb (firstn n (skipn o rest))) = n).
{ unfold seg_spec.zb. rewrite length_map, length_firstn, length_skipn. lia. }
pose proof LADDR as (A0 & A1 & AM & ARA & AHV).
assert (Hpe : p + Z.of_nat (length rest) <= mv_t v + Z.of_nat (length (mv_s v))) by (rewrite L3; lia).
assert (Hpt : mv_t v <= p) by (rewrite L3; lia).
split; [exact HB|]. split; [exact HZB|]. split; [rewrite Hlen; reflexivity|]. split.
- split; [lia|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
  + exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR Hin
      ltac:(lia) ltac:(lia)).
  + intros Hn. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc bt mt (p + Z.of_nat o) (Z.of_nat n) HAR
      Hin ltac:(lia) ltac:(lia) Hn).
- split; [exists bt, mt; split; [exact Hin | lia] | lia].
Qed.

Lemma hda_len : forall n, HDA_REF2_stmt B n -> HDA_RIEQ_stmt B n -> HDA_LEN_stmt B n.
Proof.
intros n REF2 RIEQ. unfold HDA_LEN_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j k q r HL HR HH HC HST R27 R22 R26 R20.
pose proof HL as (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R24).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & HSTR & HADDR & HCOK & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] HDA_LEN
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> ew E k0 = getr regs1 r0)
  by (intros k0 r0 Hk; subst E; apply mfE_reg; exact Hk).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
pose proof HH as (HL512 & Hij & HjL & HSL & HLB & HFIN).
pose proof HST as ((Hq1 & Hqr) & (Hrk & Hk) & _).
pose proof (hda_line_le rest) as HLr.
pose proof HADDR as (Hp0 & Hp1 & _).
pose proof HC as (HMC & HSK).
assert (Lsl : length (hda_sl rest i j) = (j - i)%nat) by (unfold hda_sl; apply hda_slice_length; lia).
unfold mf_at.
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
hda10_carry HL HL1.
assert (U20 : U E (SOff 20 0) = p + Z.of_nat (i + r)).
{ apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl), R20; reflexivity | lia]. }
assert (U26 : U E (SOff 26 0) = p + Z.of_nat (i + q)).
{ apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity | lia]. }
assert (UD : U E (SAlu ALU_ADD (SOff 20 0) (SMd M_MUL (SOff 26 0) (SLit (-1)))) = Z.of_nat (r - q)).
{ rewrite hda10_U_subm, U20, U26; [lia|]. rewrite U20, U26. unfold M64. lia. }
psrr_branch_tok RUN BR HS SHOK Bspan.
{ (* be - b < 8: refuse *)
  hda_U Hc. rewrite hda10_lt_lit, UD in Hc by (rewrite ?UD; lia). apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF2; [hda_awr_ro|].
  hda10_carry HL1 HL2. pmkst HS.
  apply (REF2 v lyc Sc Wc _ _ _ pos mcc cur line p rest HL2).
  - hda_regs_carry HS EE E32 HR.
  - rewrite <- HFIN. f_equal. f_equal.
    rewrite (hda_hdr_refuse_short mcc (hda_sl rest i j) (line + 1) k q r HMC HST ltac:(lia)). reflexivity.
  - prreg HS (23%bv : bv 5) Q23. hda_ew Q23. rewrite Q23, (EE 22%nat 22%bv eq_refl). exact R22. }
(* be - b >= 8: ieq(b, 7, "segment") *)
hda_U Hc. rewrite hda10_lt_lit, UD in Hc by (rewrite ?UD; lia). apply Z.ltb_ge in Hc.
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
hda10_carry HL1 HL2.
(* at `jal ieq` 0x864b0: a0 = b (atom 26), a1 = 7, a2 = "segment", ra = RIEQ; the run changed no byte *)
rewrite !wvb_collapse in HL2.
pose proof HL2 as (_ & LS' & _ & CORE' & CELLS' & _ & _ & LOOP' & NP').
assert (Q2 : getr (ms_regs ms0) 2 = w64 (mf_s1 (mv_sp v))) by (hda_rg HS EE 2%nat (2%bv : bv 5); exact R2).
assert (Q3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (hda_rg HS EE 3%nat (3%bv : bv 5); exact R3).
assert (Q4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (hda_rg HS EE 4%nat (4%bv : bv 5); exact R4).
assert (Q8 : getr (ms_regs ms0) 8 = w64 (mv_sp v)) by (hda_rg HS EE 8%nat (8%bv : bv 5); exact R8).
assert (Q9 : getr (ms_regs ms0) 9 = w64 (mf_s1 (mv_sp v))).
{ rewrite (hda10_st_reg SEGS _ _ _ _ 9%bv 2%nat HS) by (vm_compute; reflexivity).
  rewrite (EE 2%nat 2%bv eq_refl). exact R2. }
assert (Q18 : getr (ms_regs ms0) 18 = w64 SHADOW_OFF).
{ rewrite (hda10_st_reg SEGS _ _ _ _ 18%bv 32%nat HS) by (vm_compute; reflexivity). exact E32. }
assert (Q19 : getr (ms_regs ms0) 19 = w64 32) by (hda_rg HS EE 19%nat (19%bv : bv 5); exact R19).
assert (Q25 : getr (ms_regs ms0) 25 = w64 MF_BLANK) by (hda_rg HS EE 25%nat (25%bv : bv 5); exact R25).
assert (Q24 : getr (ms_regs ms0) 24 = w64 (frame_addr lyc 1 pos)) by (hda_rg HS EE 24%nat (24%bv : bv 5); exact R24).
assert (Q27 : getr (ms_regs ms0) 27 = w64 (p + Z.of_nat i)) by (hda_rg HS EE 27%nat (27%bv : bv 5); exact R27).
assert (Q26 : getr (ms_regs ms0) 26 = w64 (p + Z.of_nat (i + q))) by (hda_rg HS EE 26%nat (26%bv : bv 5); exact R26).
assert (Q20 : getr (ms_regs ms0) 20 = w64 (p + Z.of_nat (i + r))) by (hda_rg HS EE 20%nat (20%bv : bv 5); exact R20).
assert (Q23 : getr (ms_regs ms0) 23 = w64 (line + 1)).
{ rewrite (hda10_st_reg SEGS _ _ _ _ 23%bv 22%nat HS) by (vm_compute; reflexivity).
  rewrite (EE 22%nat 22%bv eq_refl). exact R22. }
assert (Q22 : getr (ms_regs ms0) 22 = w64 (Z.of_nat (r - q))).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms0 22%bv HS), hda10_denot_U.
  lazymatch goal with |- Z_to_bv 64 (U E ?x) = _ => let x' := eval vm_compute in x in change x with x' end.
  rewrite UD. reflexivity. }
assert (Q10 : getr (ms_regs ms0) 10 = w64 (p + Z.of_nat (i + q))).
{ rewrite (hda10_st_reg SEGS _ _ _ _ 10%bv 26%nat HS) by (vm_compute; reflexivity).
  rewrite (EE 26%nat 26%bv eq_refl). exact R26. }
assert (Q11 : getr (ms_regs ms0) 11 = w64 7).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms0 11%bv HS).
  lazymatch goal with |- sv_denot E ?x = _ => let x' := eval vm_compute in x in change x with x' end.
  reflexivity. }
assert (Q12 : getr (ms_regs ms0) 12 = w64 (SegInstA.seg_litA_fz S_segment)).
{ rewrite (hda10_st_reg SEGS _ _ _ _ 12%bv (A_OBJ 16) HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_img regs1 v lyc pos cur (mf_next p rest) [] (A_OBJ 16) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  rewrite (mf_lit_obj VOBJS S_segment 16 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
  reflexivity. }
assert (Q1 : getr (ms_regs ms0) 1 = Z_to_bv 64 (BASE + HDA_RIEQ)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms0 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E HDA_RIEQ HEI). }
pmkst HS.
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the 7 bytes at b: hb's first 7, present, addressable, in the text's block *)
destruct (hda10_slice_facts v lyc Sc Wc (ms_mem ms0) _ pos MF_LOW_OFF mcc cur line p rest (i + q) 7 CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
refine (mf_ieq_call B RELRO IEQ v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos MF_LOW_OFF mcc cur
  line p rest (mf_next p rest) HDA_RIEQ (p + Z.of_nat (i + q)) 7 (seg_spec.zb (firstn 7 (skipn (i + q) rest)))
  S_segment CX LS' CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold HDA_RIEQ, AF_m_file; lia.
- unfold HDA_RIEQ, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (KP : forall z : Z, acallee_saved z -> getr regs2 (Z_to_bv 5 z) = getr (ms_regs ms0) (Z_to_bv 5 z))
    by exact HP2.
  apply (RIEQ v lyc S2 W2 regs2 mem2 md2 pos mcc cur line p rest i j k q r).
  + exact (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj Hlen (conj Hne (conj LOOP2 NP2)))))))).
  + unfold hda_regs.
    split; [rewrite <- Q2; exact (KP 2 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q3; exact (KP 3 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q4; exact (KP 4 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q8; exact (KP 8 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q9; exact (KP 9 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q18; exact (KP 18 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q19; exact (KP 19 ltac:(unfold acallee_saved; lia))|].
    split; [rewrite <- Q25; exact (KP 25 ltac:(unfold acallee_saved; lia))|].
    rewrite <- Q24; exact (KP 24 ltac:(unfold acallee_saved; lia)).
  + exact HH.
  + exact HC.
  + exact HST.
  + lia.
  + rewrite A02, SZ. unfold hda_sl.
    destruct (hda_sl_run rest i j q (q + 7) ltac:(lia) ltac:(lia)) as (ES & _). rewrite ES.
    replace (q + 7 - q)%nat with 7%nat by lia. reflexivity.
  + rewrite <- Q27; exact (KP 27 ltac:(unfold acallee_saved; lia)).
  + rewrite <- Q23; exact (KP 23 ltac:(unfold acallee_saved; lia)).
  + rewrite <- Q26; exact (KP 26 ltac:(unfold acallee_saved; lia)).
  + rewrite <- Q20; exact (KP 20 ltac:(unfold acallee_saved; lia)).
  + rewrite <- Q22; exact (KP 22 ltac:(unfold acallee_saved; lia)).
Qed.
End e.
End f.
End d.
