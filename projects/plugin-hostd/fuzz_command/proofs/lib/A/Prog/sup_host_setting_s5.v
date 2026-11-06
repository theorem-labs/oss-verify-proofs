(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module names changed; 1320 of its 1376 lines of code are new or changed and 356 lines of the source are left out. *)
(* Three segment lemmas of sup_host_setting's ASan walk (plugin-hostd/fuzz_command, lib/A/Prog/sup_host_setting_s0.v):
   the length loop's head (ST_L1H n from ST_L1R n: the inline load8 check on &tok[n] and the strlen wrapper on
   token n), the loop's return (ST_L1R n from ST_L1H (S n) and ST_MAL: the back edge, and on the exit the malloc
   wrapper on the word list), and the malloc return (ST_MAL from ST_L2C 0: the store1 check on the new block, the
   empty word list and the first strcat wrapper). *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c arg_line_c arg_i_c xstrdup_c mix_call_c sup_host_setting_c sup_host_setting_s1 sup_host_setting_s0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* lia without the Euclidean-division equations, as this file was proved: PaDenot.v set the flag for every file
   that imported it until an earlier commit; now each file sets it for itself *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* ---- the symbolic seeds (measured in a probe run) ---- *)
Definition hs5_Bx : sv := SOff 23 0.
Definition hs5_Bspan : Z * Z := (HS_SB, HS_SB + 2 ^ 44 - 1).
Definition hs5_shx (m : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m 0) (SLit 3)) (SOff 23 0).
Definition hs5_PTRF : afact := mkAF 4096 0x7fffff800000 3.
(* L1H 0x8b190: s11 = &tok[n] (atom 27), s5 its shadow byte, the word at &tok[n] the token pointer (atom 32) *)
Definition hs5_fH : facts := mkFacts [(23%nat, mkAF HS_SB HS_SB 0); (27%nat, hs5_PTRF)] [] [].
Definition hs5_ssH : sstate := mkSS HS_L1H (sr_set sr_atoms 21 (hs5_shx 27))
  [YP09.mkRegion (Some 27%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None hs5_fH.
Definition hs5_SHH : list shent := [mkSHE 27 0 8].
(* L1R 0x8b1a0: the loop's tail, no memory touched *)
Definition hs5_ssR : sstate := mkSS HS_L1R sr_atoms [] None (mkFacts [] [] []).
(* MAL 0x8b1d4: a0 = the new block (atom 10), s2 = &tok[0] (atom 18), the word there the token pointer (atom 32) *)
Definition hs5_fM : facts := mkFacts [(9%nat, mkAF 1 64 0); (10%nat, mkAF 4096 0x7fffff800000 4);
  (18%nat, hs5_PTRF); (23%nat, mkAF HS_SB HS_SB 0)] [] [].
Definition hs5_ssM : sstate := mkSS HS_MAL sr_atoms
  [YP09.mkRegion (Some 10%nat) 0 1 0 1 []; YP09.mkRegion (Some 18%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]]
  None hs5_fM.
Definition hs5_SHM : list shent := [mkSHE 10 0 1; mkSHE 18 0 8].

(* ---- arithmetic and list facts ---- *)
Lemma hs5_words_nil : hs_words_len [] = 0.
Proof. reflexivity. Qed.
Lemma hs5_words_cons : forall w l, hs_words_len (w :: l) = Z.of_nat (length w) + 1 + hs_words_len l.
Proof. reflexivity. Qed.
Lemma hs5_words_app : forall l1 l2, hs_words_len (l1 ++ l2) = hs_words_len l1 + hs_words_len l2.
Proof.
induction l1 as [|w l1 IH]; intros l2; [rewrite hs5_words_nil; reflexivity|].
cbn [app]. rewrite !hs5_words_cons, IH. lia.
Qed.
Lemma hs5_words_nonneg : forall l, 0 <= hs_words_len l.
Proof.
induction l as [|w l IH]; [rewrite hs5_words_nil; lia | rewrite hs5_words_cons; lia].
Qed.
Lemma hs5_firstn_S : forall n (l : list (list byte)), (n < length l)%nat ->
firstn (S n) l = firstn n l ++ [nth n l []].
Proof.
induction n as [|n IH]; intros [|w l] Hn; cbn [length] in Hn; try lia.
- reflexivity.
- cbn [firstn nth app]. rewrite (IH l ltac:(cbn in Hn; lia)). reflexivity.
Qed.
Lemma hs5_words_firstn_S : forall n (l : list (list byte)), (n < length l)%nat ->
hs_words_len (firstn (S n) l) = hs_words_len (firstn n l) + Z.of_nat (length (nth n l [])) + 1.
Proof.
intros n l Hn. rewrite (hs5_firstn_S n l Hn), hs5_words_app, hs5_words_cons, hs5_words_nil. lia.
Qed.
Lemma hs5_words_firstn_le : forall n (l : list (list byte)), hs_words_len (firstn n l) <= hs_words_len l.
Proof.
intros n l. pose proof (hs5_words_app (firstn n l) (skipn n l)) as E. rewrite (firstn_skipn n l) in E.
pose proof (hs5_words_nonneg (skipn n l)). lia.
Qed.
Lemma hs5_words_tok_le : forall n (l : list (list byte)), (n < length l)%nat ->
Z.of_nat (length (nth n l [])) + 1 <= hs_words_len l.
Proof.
intros n l Hn. pose proof (hs5_words_firstn_S n l Hn) as E.
pose proof (hs5_words_firstn_le (S n) l). pose proof (hs5_words_nonneg (firstn n l)). lia.
Qed.

Lemma hs5_join_one : forall (l : list (list byte)), (0 < length l)%nat -> join_sp (firstn 1 l) = nth 0 l [].
Proof. intros [|w l] H; [cbn in H; lia | reflexivity]. Qed.

Lemma hs5_bsum_nonneg : forall l, Forall (fun pn => 0 <= snd pn) l -> 0 <= bsum l.
Proof.
induction l as [|q l IH]; intros HF; [change (bsum []) with 0; lia|].
inversion HF as [|a b Hq HF' Heq]; subst. rewrite bsum_cons. pose proof (IH HF'). lia.
Qed.
Lemma hs5_bsum_le : forall l, Forall (fun pn => 0 <= snd pn) l -> forall pn, In pn l -> snd pn <= bsum l.
Proof.
induction l as [|q l IH]; intros HF pn Hin; [destruct Hin|].
inversion HF as [|a b Hq HF' Heq]; subst. rewrite bsum_cons.
destruct Hin as [<- | Hin]; [pose proof (hs5_bsum_nonneg l HF') | pose proof (IH HF' pn Hin)]; lia.
Qed.

Lemma hs5_forall2_nth : forall {A C} (R : A -> C -> Prop) l1 l2 i a c,
Forall2 R l1 l2 -> nth_error l1 i = Some a -> nth_error l2 i = Some c -> R a c.
Proof.
intros A C R l1 l2 i. revert l1 l2.
induction i as [|i IH]; intros [|u l1] [|v l2] a c HF H1 H2; cbn in H1, H2; try discriminate;
  inversion HF as [|u' v' l1' l2' Huv HF' E1 E2]; subst.
- injection H1 as <-. injection H2 as <-. exact Huv.
- exact (IH l1 l2 a c HF' H1 H2).
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Definition hs5_E (regs1 : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs1 extra).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HH : hs_hyps B MT.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* the record's fields, at this walk's hypotheses; the runtime entries at the ambient FP state (the segments of
   this file run after arg_i, at the FP state it returned) *)
Let hPIMG := hh_prog_img B MT HH.
Let hPWR := hh_prog_writable B MT HH.
Let hROPG := hh_ro_prog_apart B MT HH.
Let hATAIL := hh_atail_kept B MT HH.
Let hHB := hh_HB B MT HH.
Let hHEAPT := hh_heap_tail B MT HH.
Let hMTL := hh_MTL B MT HH.
Let hTL := hh_TL B MT HH.
Let hSTRLEN := hh_strlen B MT HH fx.
Let hSTRCAT := hh_strcat B MT HH fx.
Let hMALLOC := hh_malloc B MT HH fx.
Let hROM := hh_rom_view B MT HH.
Let hRELRO := hh_RELRO_IMG B MT HH.
Let hRRO : ro_below_ofl SEGS RLO RHI := hh_RRO B MT HH.

(* ---- what the footprint of the whole call holds ---- *)
Lemma hs5_fp_closed : forall ly S (W : world SEGS) mem md O,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
~ YI16.sink_open_fp (hs_FP O).
Proof.
intros ly S W mem md O HAR HO. unfold hs_FP.
apply sink_closed_cons; [cbn; unfold A_G_REC; lia|].
apply sink_closed_cons; [cbn; unfold A_REC_SPILL; lia|].
apply sink_closed_ablocks_fp. apply Forall_forall. intros [p n] Hin. cbn [fst].
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR (HO (p, n) Hin)) as (_ & H4096 & _). lia.
Qed.

(* a byte of a live block that is none of the recorder's is outside the footprint *)
Lemma hs5_blk_outFP : forall ly S (W : world SEGS) mem md O p n a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (p, n) (ablocks B ly S) -> ~ In (p, n) O -> p <= a < p + req_size n -> ~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O p n a HAR HO Hin Hno Ha Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha
    (hPIMG a (recb_grec_in a ltac:(lia)))). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (blk_img SEGS B LAWS ly S W mem md p n a HAR Hin Ha
    (hPIMG a (recb_spill_in a ltac:(lia)))). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
assert (Hne : (q, m) <> (p, n)) by (intros E; rewrite E in Hqm; exact (Hno Hqm)).
pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR (HO (q, m) Hqm) Hin Hne) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* an image byte that is none of the program's statics is outside the footprint *)
Lemma hs5_img_outFP : forall ly S (W : world SEGS) mem md O a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
in_img SEGS a -> ~ Exists (in_zr a) recb_PG -> ~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O a HAR HO Himg Hpg Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (Hpg (recb_grec_in a ltac:(lia))). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (Hpg (recb_spill_in a ltac:(lia))). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
exact (blk_img SEGS B LAWS ly S W mem md q m a HAR (HO (q, m) Hqm) Hr Himg).
Qed.

(* a byte of a live frame is outside the footprint *)
Lemma hs5_frm_outFP : forall ly S (W : world SEGS) mem md O cid pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (cid, pos) (frames S) -> frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O cid pos a HAR HO Hin Ha Hfp.
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ exact (frm_img SEGS B LAWS ly S W mem md cid pos a HAR Hin Ha
    (hPIMG a (recb_grec_in a ltac:(lia)))). }
apply inFP_cons in Hfp as [Hs | Hfp].
{ exact (frm_img SEGS B LAWS ly S W mem md cid pos a HAR Hin Ha
    (hPIMG a (recb_spill_in a ltac:(lia)))). }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md q m cid pos HAR (HO (q, m) Hqm) Hin) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

(* a shadow byte of a live frame is outside the footprint *)
Lemma hs5_frmsh_outFP : forall ly S (W : world SEGS) mem md O cid pos a,
AR SEGS B ly S W mem md -> (forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (cid, pos) (frames S) ->
shadow_addr (frame_addr ly cid pos) <= a < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8 ->
~ inFP (hs_FP O) a.
Proof.
intros ly S W mem md O cid pos a HAR HO Hin Ha Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (Hf0 & Hfc & Happ).
pose proof (fs_frame_bytes_nonneg cid) as Hfb.
assert (Hlo : SHADOW_OFF <= a).
{ unfold shadow_addr in Ha. assert (0 <= frame_addr ly cid pos / 8) by (apply Z.div_pos; lia). lia. }
assert (Hhi : a < kHighMemBeg).
{ pose proof (shadow_range_end (frame_addr ly cid pos) (fs_frame_bytes cid) Hfb) as Hre.
  assert (Hle : shadow_addr (frame_addr ly cid pos + fs_frame_bytes cid) <= shadow_addr alloc_ceiling)
    by (apply shadow_mono; lia).
  assert (Hc8 : alloc_ceiling / 8 <= 17592184995840)
    by (replace 17592184995840 with (140737479966720 / 8) by (vm_compute; reflexivity); apply Z.div_le_mono; lia).
  unfold shadow_addr in *. unfold SHADOW_OFF, kHighMemBeg in *. lia. }
unfold hs_FP in Hfp. apply inFP_cons in Hfp as [Hg | Hfp].
{ cbn in Hg. unfold A_G_REC, REC_SIZE, SHADOW_OFF in *. lia. }
apply inFP_cons in Hfp as [Hs | Hfp].
{ cbn in Hs. unfold A_REC_SPILL, SC_SIZE, SHADOW_OFF in *. lia. }
destruct (inFP_ablocks_fp_inv O a Hfp) as (q & m & Hqm & Hr).
destruct (al_blocks _ _ LAWS ly S W mem md q m HAR (HO (q, m) Hqm)) as (_ & _ & _ & Hqapp & _).
destruct Hqapp as (_ & [Hq | [Hq1 Hq2]]); unfold kLowShadowBeg, SHADOW_OFF, kHighMemBeg in *; lia.
Qed.

(* ---- the env of a seed ---- *)
Lemma hs5_E_img : forall regs1 extra, img_env VAL A_LIM (hs5_E regs1 extra).
Proof. intros regs1 extra. unfold hs5_E. apply Eimg_env. Qed.
Lemma hs5_E_reg : forall regs1 extra k (r : bv 5), Z.of_nat k = bv_unsigned r ->
ew (hs5_E regs1 extra) k = getr regs1 r.
Proof. intros regs1 extra k r Hk. unfold hs5_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma hs5_E_x32 : forall regs1 v l, ew (hs5_E regs1 (v :: l)) 32 = v.
Proof.
intros regs1 v l. unfold hs5_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra regs1 (v :: l) 0).
Qed.
Lemma hs5_U_off0 : forall E m v, bv_unsigned (ew E m) = v -> 0 <= v < M64 -> U E (SOff m 0) = v.
Proof. intros E m v Hm Hv. rewrite U_SOff, Hm, Z.add_0_r. apply zcanon_id. exact Hv. Qed.
Lemma hs5_U_shx : forall E m v, bv_unsigned (ew E 23) = HS_SB -> bv_unsigned (ew E m) = v ->
0 <= v < 2 ^ 47 -> U E (hs5_shx m) = HS_SB + v / 8.
Proof.
intros E m v H23 Hm Hv.
assert (Hd : 0 <= v / 8 <= v) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
unfold hs5_shx. rewrite !U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw].
rewrite H23, Hm, !Z.add_0_r.
rewrite (zcanon_id 3) by (unfold M64; lia).
rewrite (zcanon_id v) by (unfold M64; lia).
rewrite (zcanon_id HS_SB) by (unfold HS_SB, M64; lia).
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v / 8)) by (unfold M64; lia).
rewrite (zcanon_id (v / 8 + HS_SB)) by (unfold HS_SB, M64; lia).
lia.
Qed.

(* ---- the entry state of the run at L1H ---- *)
Lemma hs5_seed_H : forall (W : world SEGS) (regs1 : bvmap 5 word) mem q p,
getr regs1 23 = w64 HS_SB -> getr regs1 27 = w64 q -> getr regs1 21 = w64 (HS_SB + q / 8) ->
4096 <= q -> q + 8 <= 0x7fffff800000 -> q mod 8 = 0 -> 0 <= p < 2 ^ 64 ->
val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
st_ok_pi SEGS VAL (hs5_E regs1 [Z_to_bv 64 p]) hs5_ssH
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_L1H)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem q p H23 H27 H21 Hq1 Hq2 Hq8 Hp Hv.
rewrite restrict_mkst_fx. unfold hs5_ssH.
set (E := hs5_E regs1 [Z_to_bv 64 p]).
assert (E23 : ew E 23 = w64 HS_SB) by (unfold E; rewrite (hs5_E_reg regs1 _ 23%nat 23%bv eq_refl); exact H23).
assert (E27 : ew E 27 = w64 q) by (unfold E; rewrite (hs5_E_reg regs1 _ 27%nat 27%bv eq_refl); exact H27).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (unfold E; exact (hs5_E_x32 regs1 _ [])).
assert (U23 : bv_unsigned (ew E 23) = HS_SB) by (rewrite E23; apply unsigned_lit_small; unfold HS_SB; lia).
assert (U27 : bv_unsigned (ew E 27) = q) by (rewrite E27; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- apply YI04.regs_ok_pin; [unfold E, hs5_E; apply regs_ok_Eimg_Ereg | | ].
  + intros Hc. apply (f_equal bv_unsigned) in Hc. vm_compute in Hc. discriminate Hc.
  + rewrite H21, denot_lit_U, (hs5_U_shx E 27%nat q U23 U27 ltac:(lia)). reflexivity.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  rewrite Z.add_0_r. exact Hv.
- cbn [pairwise_disjoint all_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [hs5_fH f_atoms atoms_ok]. unfold afact_ok, hs5_PTRF. cbn [af_lo af_hi af_al2].
  rewrite U23, U27.
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I
          | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
          | (change (2 ^ 3) with 8; exact Hq8)
          | (unfold HS_SB; lia) ].
Qed.

(* ---- the entry state of the run at MAL ---- *)
Lemma hs5_seed_M : forall (W : world SEGS) (regs1 : bvmap 5 word) mem w ntok q p,
getr regs1 23 = w64 HS_SB -> getr regs1 9 = w64 ntok -> getr regs1 10 = w64 w ->
getr regs1 18 = w64 q ->
1 <= ntok <= 64 -> 4096 <= w -> w + 1 <= 0x7fffff800000 -> w mod 16 = 0 ->
4096 <= q -> q + 8 <= 0x7fffff800000 -> q mod 8 = 0 -> 0 <= p < 2 ^ 64 ->
(w + 1 <= q \/ q + 8 <= w) ->
(forall o, 0 <= o < 1 -> YP09.writable_at SEGS (mrestrict (w_H W) mem) (w + o)) ->
val_mem SEGS (mrestrict (w_H W) mem) q 8 p ->
st_ok_pi SEGS VAL (hs5_E regs1 [Z_to_bv 64 p]) hs5_ssM
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_MAL)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem w ntok q p H23 H9 H10 H18 Hnt Hw1 Hw2 Hw16 Hq1 Hq2 Hq8 Hp Hdisj Hwr Hv.
rewrite restrict_mkst_fx. unfold hs5_ssM.
set (E := hs5_E regs1 [Z_to_bv 64 p]).
assert (E23 : ew E 23 = w64 HS_SB) by (unfold E; rewrite (hs5_E_reg regs1 _ 23%nat 23%bv eq_refl); exact H23).
assert (E9 : ew E 9 = w64 ntok) by (unfold E; rewrite (hs5_E_reg regs1 _ 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = w64 w) by (unfold E; rewrite (hs5_E_reg regs1 _ 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = w64 q) by (unfold E; rewrite (hs5_E_reg regs1 _ 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 p) by (unfold E; exact (hs5_E_x32 regs1 _ [])).
assert (U23 : bv_unsigned (ew E 23) = HS_SB) by (rewrite E23; apply unsigned_lit_small; unfold HS_SB; lia).
assert (U9 : bv_unsigned (ew E 9) = ntok) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = w) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = q) by (rewrite E18; apply unsigned_lit_small; lia).
apply pa_entry_st_ok_full.
- unfold E, hs5_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U10. split; [lia|]. split; [lia|]. split; [exact Hwr | apply Forall_nil].
  + rewrite U18. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ q 0 8 (SOff 32 0) p);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    rewrite Z.add_0_r. exact Hv.
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U10, U18.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [hs5_fM f_atoms atoms_ok]. unfold afact_ok, hs5_PTRF. cbn [af_lo af_hi af_al2].
  rewrite U23, U9, U10, U18.
  repeat match goal with |- _ /\ _ => split end;
    first [ exact I
          | (rewrite Z.pow_0_r, Z.mod_1_r; reflexivity)
          | (change (2 ^ 3) with 8; exact Hq8)
          | (change (2 ^ 4) with 16; exact Hw16)
          | (unfold HS_SB; lia) ].
Qed.

(* ---- what a journal of the call keeps ---- *)
Lemma hs5_j_AR : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> AR SEGS B lyc Sc Wc memc mdc.
Proof. intros * HJ. exact (proj1 HJ). Qed.
Lemma hs5_j_frames : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> frames Sc = own ++ frames S.
Proof. intros * HJ. destruct HJ as (_ & _ & _ & _ & _ & H & _). exact H. Qed.
Lemma hs5_j_lay : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k cid pos,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
frame_addr lyc cid pos = frame_addr ly cid pos.
Proof.
intros * HJ. destruct HJ as (_ & Hly & _). unfold frame_addr.
destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.
Lemma hs5_j_blk : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k p n i,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B lyc Sc) -> 0 <= i < req_size n -> ~ inFP FP (p + i) ->
rdW Wc memc (p + i) = rdW W mem (p + i).
Proof.
intros * HJ H1 H2 H3 H4. destruct HJ as (_&_&_&_&_&_&_&_&_& F2 &_). exact (F2 p n i H1 H2 H3 H4).
Qed.
Lemma hs5_j_img : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k a,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
fp_spares FP a -> rdW Wc memc a = rdW W mem a.
Proof.
intros * HJ H1 H2 H3 H4. destruct HJ as (_&_&_&_&_&_&_&_&_&_& F3 &_). exact (F3 a H1 H2 H3 H4).
Qed.
Lemma hs5_j_frm : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k cid pos a,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k ->
In (cid, pos) (frames S) ->
(in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8)) ->
~ inFP FP a -> rdW Wc memc a = rdW W mem a.
Proof.
intros * HJ H1 H2 H3. destruct HJ as (_&_&_&_&_&_&_&_&_&_&_& F4 &_). exact (F4 cid pos a H1 H2 H3).
Qed.

(* the read-only bytes of the image, at a state of the call *)
Lemma hs5_rod_now : forall STK sp0 ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k O,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (hs_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW Wc memc).
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k O HARe HJ HO HR.
eapply (arodata_ok_journalP SEGS RLO RHI hRELRO (RO := hRRO) B STK sp0 (hs_FP O)
  ly S W mem md own lyc Sc Wc memc mdc k HJ); [|exact HR].
intros a Hro. destruct (hROPG a Hro) as [Himg Hpg].
exact (hs5_img_outFP ly S W mem md O a HARe HO Himg Hpg).
Qed.

(* what the walk needs of a string argument at a state of the call *)
Definition hs5_argok (Wc : world SEGS) (memc : word -> option byte) (p : Z) (s : list byte) : Prop :=
4096 <= p /\ p + Z.of_nat (length s) + 1 <= alloc_ceiling /\ Z.of_nat (length s) + 1 <= LMAX + 1 /\
astr_atR (rdW Wc memc) p s /\ atail_vis SEGS Wc memc (p + Z.of_nat (length s)) /\
amem_range p (Z.of_nat (length s) + 1) /\
range_addressable (rdW Wc memc) SHADOW_OFF p (Z.of_nat (length s) + 1) /\
shadow_hull_vis (rdW Wc memc) p (Z.of_nat (length s) + 1) /\
(* 8 bytes of band room past the string (the string entries' `+ 8` premise, band-premise survey, call site 19) *)
amem_range p (Z.of_nat (length s) + 8).

Lemma hs5_arg_now : forall STK sp0 ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k O p s,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (hs_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
hs_str B ly S (rdW W mem) O p s ->
atail_vis SEGS W mem (p + Z.of_nat (length s)) ->
hs5_argok Wc memc p s.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k O p s HARe HJ HO Hlive HARG HT.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
unfold hs_str in HARG. destruct HARG as (Hp0 & HSTR & Hnle & HBLK & HAP).
destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
assert (Hno : ~ In (q, m) O).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
pose proof (Hlive (q, m) Hqm Hno) as Hqc.
destruct (al_blocks _ _ LAWS ly S W mem md q m HARe Hqm) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hmr).
pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
assert (Hkept : forall a, q <= a < q + req_size m -> rdW Wc memc a = rdW W mem a).
{ intros a Ha. replace a with (q + (a - q)) by lia.
  apply (hs5_j_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m (a - q) HJ Hqm Hqc ltac:(lia)).
  exact (hs5_blk_outFP ly S W mem md O q m (q + (a - q)) HARe HO Hqm Hno ltac:(lia)). }
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ destruct HSTR as [HB Hnz]. split; [|exact Hnz]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  rewrite (Hkept (p + Z.of_nat i)) by lia. exact (HB i ltac:(rewrite length_app; cbn [length]; lia)). }
split.
{ apply (hATAIL ly S W mem md lyc Sc Wc memc mdc q m (p + Z.of_nat (length s)) HARe HARc);
    [left; split; [exact Hqm | split; [exact Hqc | lia]] | exact HT]. }
split.
{ exact (amem_range_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia)). }
split.
{ exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia)). }
split; [exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s) + 1) HARc Hqc ltac:(lia) ltac:(lia) ltac:(lia))|].
exact (amem8_of_block SEGS B LAWS lyc Sc Wc memc mdc q m p (Z.of_nat (length s)) HARc Hqc ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* a string argument is a range the runtime entries may read *)
Lemma hs5_read_of_arg : forall stk (Wc : world SEGS) memc (regs : bvmap 5 word) p s,
hs5_argok Wc memc p s -> alloc_ceiling <= spZ regs - stk -> 0 <= stk ->
aread_ok SEGS stk Wc regs memc p (astr_len s + 1).
Proof.
intros stk Wc memc regs p s (H1 & H2 & H3 & HSTR & HTl & HMR & HRA & HHU & _) Hsp Hstk.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold aread_ok, astr_len. split; [lia|]. split; [lia|]. split; [unfold LMAX in H3; lia|].
split.
- intros a Ha. split.
  + destruct HSTR as [HB _].
    replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
    rewrite (HB (Z.to_nat (a - p)) ltac:(rewrite length_app; cbn [length]; lia)). discriminate.
  + unfold ascratch_stk. lia.
- split; [exact HMR|]. split; [exact HRA | intros _; exact HHU].
Qed.

(* the eight bytes of one slot of the token array, at a state of the call *)
Lemma hs5_arr_now : forall STK sp0 ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k O ptok N j,
AR SEGS B ly S W mem md ->
ajournal SEGS B STK sp0 (hs_FP O) ly S W mem md own lyc Sc Wc memc mdc k ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
(afobj SEGS B ly S W mem ptok N \/
 (in_blockA (ablocks B ly S) ptok N /\ Forall (fun qk => iv_apart ptok N (fst qk) (snd qk)) O)) ->
0 <= j -> j + 8 <= N ->
4096 <= ptok + j /\ ptok + j + 8 <= alloc_ceiling /\ in_app (ptok + j) 8 /\
(forall i, 0 <= i < 8 -> rdW Wc memc (ptok + j + i) = rdW W mem (ptok + j + i)) /\
range_addressable (rdW Wc memc) SHADOW_OFF (ptok + j) 8.
Proof.
intros STK sp0 ly S W mem md own lyc Sc Wc memc mdc k O ptok N j HARe HJ HO Hlive HARR Hj0 HjN.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
destruct HARR as [((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & Hp8 & HRA) | [HBLK HAP]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HARe Hin) as (Hb1 & Hb2 & Happ).
  pose proof (fs_frame_bytes_nonneg cid) as Hfb.
  assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
  { unfold fs_frame_bytes. rewrite Z.shiftl_mul_pow2 by lia.
    replace (64 * 2 ^ cid) with ((8 * 2 ^ cid) * 8) by lia. apply Z.mod_mul. lia. }
  assert (Hdiv : forall x, frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
    shadow_addr (frame_addr ly cid pos) <= shadow_addr x < shadow_addr (frame_addr ly cid pos) + fs_frame_bytes cid / 8).
  { intros x Hx. split; [apply shadow_mono; lia|].
    assert (Hlt : x / 8 < frame_addr ly cid pos / 8 + fs_frame_bytes cid / 8).
    { apply Z.div_lt_upper_bound; [lia|].
      pose proof (Z.div_mod (frame_addr ly cid pos) 8 ltac:(lia)) as D1.
      pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D2. rewrite Hal in D1. rewrite Hb8 in D2. lia. }
    unfold shadow_addr. lia. }
  split; [lia|]. split; [lia|].
  split; [apply (in_app_sub (frame_addr ly cid pos) (fs_frame_bytes cid)); [exact Happ | lia | lia | lia]|].
  split.
  { intros i Hi.
    apply (hs5_j_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (ptok + j + i) HJ Hin).
    - left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
    - exact (hs5_frm_outFP ly S W mem md O cid pos (ptok + j + i) HARe HO Hin ltac:(lia)). }
  intros x Hx. destruct (HRA x ltac:(lia)) as (s & Hs & Hok). exists s. split; [|exact Hok].
  rewrite <- Hs.
  apply (hs5_j_frm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos (shadow_of_addr SHADOW_OFF x) HJ Hin).
  + right. unfold in_zr. cbn [fst snd].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) by reflexivity.
    exact (Hdiv x ltac:(lia)).
  + replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) by reflexivity.
    exact (hs5_frmsh_outFP ly S W mem md O cid pos (shadow_addr x) HARe HO Hin (Hdiv x ltac:(lia))).
- destruct HBLK as (q & m & Hqm & Hq1 & Hq2).
  assert (Hno : ~ In (q, m) O).
  { intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
    unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
  pose proof (Hlive (q, m) Hqm Hno) as Hqc.
  destruct (al_blocks _ _ LAWS ly S W mem md q m HARe Hqm) as (_ & Hq4096 & Hqceil & Happ & _ & _ & Hmr).
  pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
  split; [lia|]. split; [lia|].
  split; [apply (in_app_sub q (req_size m)); [exact Happ | lia | lia | lia]|].
  split.
  { intros i Hi. replace (ptok + j + i) with (q + (ptok + j + i - q)) by lia.
    apply (hs5_j_blk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q m (ptok + j + i - q) HJ Hqm Hqc ltac:(lia)).
    exact (hs5_blk_outFP ly S W mem md O q m (q + (ptok + j + i - q)) HARe HO Hqm Hno ltac:(lia)). }
  exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc memc mdc q m (ptok + j) 8 HARc Hqc ltac:(lia) ltac:(lia)).
Qed.

(* a callee-saved register is the one the call was entered with *)
Lemma hs5_pres_at : forall (regs regs' : bvmap 5 word) (r : bv 5) z,
aregs_preserved regs regs' -> bv_unsigned r = z -> acallee_saved z -> getr regs' r = getr regs r.
Proof.
intros regs regs' r z HP Hz Hc. pose proof (HP z Hc) as H. rewrite <- Hz, Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* the stack this call takes is wider than any entry's window *)
Lemma hs5_stk : 112 + ASTACK <= SUP_HOST_SETTING_STK.
Proof.
unfold SUP_HOST_SETTING_STK.
pose proof (Z.le_max_r REC_CALLS_FREE_STK (Z.max ARG_LINE_STK (Z.max ARG_I_STK (Z.max XSTRDUP_STK (Z.max MIX_CALL_STK ASTACK))))).
pose proof (Z.le_max_r ARG_LINE_STK (Z.max ARG_I_STK (Z.max XSTRDUP_STK (Z.max MIX_CALL_STK ASTACK)))).
pose proof (Z.le_max_r ARG_I_STK (Z.max XSTRDUP_STK (Z.max MIX_CALL_STK ASTACK))).
pose proof (Z.le_max_r XSTRDUP_STK (Z.max MIX_CALL_STK ASTACK)).
pose proof (Z.le_max_r MIX_CALL_STK ASTACK). lia.
Qed.

(* ---- L1H n: the load8 check on &tok[n] and the strlen wrapper ---- *)
Lemma hs_seg_l1h : forall x n, ST_L1R B MT x n -> ST_L1H B MT x n.
Proof.
intros x n HR. unfold ST_L1H.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 Hn HCX HMID Hb0 Hb1 HREP HREG H18 H25 H26 H27 H20 H21.
pose proof HCX as HCXc. unfold hs_cx in HCXc. cbv zeta in HCXc.
destruct HCXc as (HPRE & HROD & HROO & HROIN & HGRD & Hr10 & Hr11 & Hr12 & Hntok & HLINE & Hptok0 & Hptok8 &
  HARR & Hlenps & HPTR & HTOKS & HWL & HREPe & HFRe & HEV & HLIVE & HMOK & HTAIL).
pose proof HMID as HMIDc. unfold hs_mid in HMIDc. cbv zeta in HMIDc.
destruct HMIDc as (HJ & Hk & HMLE & HBB & HFRAME & HBA).
pose proof HBA as HBAc. unfold hs_ba in HBAc. cbv zeta in HBAc.
destruct HBAc as (HPERM & HRest1 & HRest2 & HO1a & HO1b & HNwO & HO1R).
pose proof HREG as HREGc. destruct HREGc as (HREG0 & H19 & H24).
destruct HREG0 as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
pose proof HPRE as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof hs5_stk as WS. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
(* the recorder's blocks are live at the entry, and the others are live now *)
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x))).
{ intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREPe pn Hpn)). }
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_or_app. right. exact (HRest2 pn Hpn Hno). }
(* token n: its pointer and its bytes *)
assert (Hnp : nth_error (i_ps x) n = Some (hs_ptr x n)) by (apply nth_error_nth'; lia).
assert (Hnt : nth_error (i_toks x) n = Some (hs_tok x n)) by (apply nth_error_nth'; lia).
pose proof (HPTR n _ Hnp) as HVAL.
pose proof (hs5_forall2_nth _ _ _ n _ _ HTOKS Hnp Hnt) as HARG.
pose proof (HTAIL n _ _ Hnp Hnt) as HTl.
(* the slot of the token array at the current state *)
destruct (hs5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) (8 * Z.of_nat n)
  HARe HJ HO Hlive HARR ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & Hkeptarr & HRAarr).
pose proof (hs5_arg_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k (i_O x) (hs_ptr x n) (hs_tok x n) HARe HJ HO Hlive HARG HTl) as HAOK0.
pose proof HAOK0 as (Hp1 & Hp2 & Hp3 & _).
assert (HVALc : val_mem SEGS (mrestrict (w_H Wc) memc) (i_ptok x + 8 * Z.of_nat n) 8 (hs_ptr x n)).
{ apply val_mem_view. intros kk Hkk. rewrite (Hkeptarr (Z.of_nat kk) ltac:(lia)). exact (HVAL kk Hkk). }
assert (Hm8 : (i_ptok x + 8 * Z.of_nat n) mod 8 = 0).
{ rewrite Z.add_mod by lia. rewrite Hptok8.
  replace (8 * Z.of_nat n) with (Z.of_nat n * 8) by lia. rewrite Z.mod_mul by lia. reflexivity. }
pose proof (hs5_seed_H Wc regs1 memc (i_ptok x + 8 * Z.of_nat n) (hs_ptr x n)
  R23 H27 H21 ltac:(lia) ltac:(lia) Hm8 ltac:(lia) HVALc) as HS.
set (E := hs5_E regs1 [Z_to_bv 64 (hs_ptr x n)]) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hs5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hs5_E_img).
assert (UBx : U E hs5_Bx = SHADOW_OFF).
{ unfold hs5_Bx. rewrite U_SOff, (EE 23%nat 23%bv eq_refl), R23, Z.add_0_r.
  unfold w64, HS_SB, SHADOW_OFF. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U27 : U E (SOff 27 0) = i_ptok x + 8 * Z.of_nat n).
{ apply hs5_U_off0; [rewrite (EE 27%nat 27%bv eq_refl), H27; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (SHOK : sh_ok SEGS hs5_Bx hs5_SHH E (mrestrict (w_H Wc) memc)).
{ unfold hs5_SHH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS); [exact HRAarr | exact UBx | exact U27 | lia | lia |].
  cbn [Z.min Z.max]. intros z Hz. destruct Happ as (_ & [Hk1 | [Hk1 Hk2]]);
    unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
unfold hs_at.
(* 0x8b190 .. 0x8b19c: the shadow check of &tok[n], a0 := tok[n], the call of the strlen wrapper *)
paj_run_tok RUN HS HJ SHOK hs5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
(* the run writes no memory *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin
    | exact Ha | intros [] ]. }
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (10%bv : bv 5) P10.
rewrite (EE 2%nat 2%bv eq_refl) in P2. rewrite (EE 3%nat 3%bv eq_refl) in P3.
rewrite (EE 4%nat 4%bv eq_refl) in P4.
assert (P32 : ew E 32 = Z_to_bv 64 (hs_ptr x n)) by (unfold E; apply hs5_E_x32).
rewrite P32 in P10.
assert (Hsp : spZ (ms_regs ms) = spZ (i_regs x) + -112).
{ unfold spZ at 1. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the facts of token n at the state of the call *)
pose proof (hs5_arg_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc (ms_mem ms) mdv k (i_O x) (hs_ptr x n) (hs_tok x n) HARe HJ HO Hlive HARG HTl) as HAOK.
pose proof HAOK as (G1 & G2 & G3 & GSTR & GTl & GMR & GRA & GHU & _).
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B hTL) ESTACK (fun _ => False)
    (SIG CS___interceptor_trampoline_strlen) Wc (ms_regs ms) (ms_mem ms) SUP_HOST_SETTING_STK
    (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc _ k (-112)
    (Z_to_bv 64 (BASE + HS_L1R)) _ HJ Hsp eq_refl ltac:(lia) ltac:(lia) ltac:(rewrite Hes; lia) P1
    (fun a (H : False) => False_ind _ H)).
  apply (hSTRLEN lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv (hs_ptr x n) (hs_tok x n)).
  - eapply (ecall_pre_stk_at SEGS B ESTACK SUP_HOST_SETTING_STK
      (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc Wc (ms_mem ms) mdv k
      (ms_regs ms) (-112) HJ Hsp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HraT);
      [rewrite P3, R3; exact Hgp | rewrite P4, R4; exact Htp].
  - rewrite P10. reflexivity.
  - lia.
  - apply (astr_atR_view SEGS). exact GSTR.
  - exact (hs5_read_of_arg ESTACK Wc (ms_mem ms) (ms_regs ms) (hs_ptr x n) (hs_tok x n) HAOK ltac:(lia) ltac:(lia)).
  - unfold astr_len. exact GTl.
  - apply hROM. exact (hs5_rod_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
      [] lyc Sc Wc (ms_mem ms) mdv k (i_O x) HARe HJ HO HROD). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
(* back at 0x8b1a0 with a0 = |tok[n]| *)
assert (KEEPA : forall a, 0 <= a < alloc_ceiling -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(intros [])). apply KEEP1. lia. }
assert (KEEPF : forall a, spZ (i_regs x) - 112 <= a < spZ (i_regs x) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(intros [])). apply KEEP1. lia. }
assert (HFR2 : hs_frame (rdW Wc mem2) (spZ (i_regs x)) (i_regs x)).
{ intros j r Hjr.
  assert (Hj : (j < length HS_SAVED)%nat) by (apply (proj1 (nth_error_Some HS_SAVED j)); rewrite Hjr; discriminate).
  unfold HS_SAVED in Hj. cbn [length] in Hj.
  intros kk Hkk. rewrite (KEEPF (spZ (i_regs x) - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)).
  exact (HFRAME j r Hjr kk Hkk). }
assert (HBLIVE : forall pn, In pn (O1 ++ [b0; b1]) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_app_or in Hpn as [Hpn | Hpn]; apply in_or_app; [right; exact (HO1R pn Hpn) | left; exact Hpn]. }
assert (HREP2 : rec_repA B lyc Sc (rdW Wc mem2) (rec_record (i_R x) REC_HOST_SETTING (hs_A2 x)) (O1 ++ [b0; b1])).
{ apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP); [|exact HBLIVE].
  intros a [Hrec | Hown].
  - apply KEEPA. unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hrec. lia.
  - destruct Hown as ([q m] & Hpn & Hr). cbn [fst snd] in Hr.
    destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv q m (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
      (HBLIVE (q, m) Hpn)) as (_ & Hq4 & Hqc & _ & _ & _ & Hmr).
    pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2]. apply KEEPA. lia. }
assert (Q2 : getr regs2 2 = getr regs1 2)
  by (rewrite (hs5_pres_at _ _ (2%bv : bv 5) 2 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P2).
assert (Q3 : getr regs2 3 = getr regs1 3)
  by (rewrite (hs5_pres_at _ _ (3%bv : bv 5) 3 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P3).
assert (Q4 : getr regs2 4 = getr regs1 4)
  by (rewrite (hs5_pres_at _ _ (4%bv : bv 5) 4 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P4).
prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
prreg HS (18%bv : bv 5) P18. rewrite (EE 18%nat 18%bv eq_refl) in P18.
prreg HS (19%bv : bv 5) P19. rewrite (EE 19%nat 19%bv eq_refl) in P19.
prreg HS (20%bv : bv 5) P20. rewrite (EE 20%nat 20%bv eq_refl) in P20.
prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl) in P22.
prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl) in P23.
prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl) in P24.
prreg HS (25%bv : bv 5) P25. rewrite (EE 25%nat 25%bv eq_refl) in P25.
prreg HS (26%bv : bv 5) P26. rewrite (EE 26%nat 26%bv eq_refl) in P26.
prreg HS (27%bv : bv 5) P27. rewrite (EE 27%nat 27%bv eq_refl) in P27.
prreg HS (21%bv : bv 5) P21.
assert (Q8 : getr regs2 8 = getr regs1 8)
  by (rewrite (hs5_pres_at _ _ (8%bv : bv 5) 8 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P8).
assert (Q9 : getr regs2 9 = getr regs1 9)
  by (rewrite (hs5_pres_at _ _ (9%bv : bv 5) 9 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P9).
assert (Q18 : getr regs2 18 = getr regs1 18)
  by (rewrite (hs5_pres_at _ _ (18%bv : bv 5) 18 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P18).
assert (Q19 : getr regs2 19 = getr regs1 19)
  by (rewrite (hs5_pres_at _ _ (19%bv : bv 5) 19 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P19).
assert (Q20 : getr regs2 20 = getr regs1 20)
  by (rewrite (hs5_pres_at _ _ (20%bv : bv 5) 20 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P20).
assert (Q22 : getr regs2 22 = getr regs1 22)
  by (rewrite (hs5_pres_at _ _ (22%bv : bv 5) 22 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P22).
assert (Q23 : getr regs2 23 = getr regs1 23)
  by (rewrite (hs5_pres_at _ _ (23%bv : bv 5) 23 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P23).
assert (Q24 : getr regs2 24 = getr regs1 24)
  by (rewrite (hs5_pres_at _ _ (24%bv : bv 5) 24 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P24).
assert (Q25 : getr regs2 25 = getr regs1 25)
  by (rewrite (hs5_pres_at _ _ (25%bv : bv 5) 25 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P25).
assert (Q26 : getr regs2 26 = getr regs1 26)
  by (rewrite (hs5_pres_at _ _ (26%bv : bv 5) 26 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P26).
assert (Q27 : getr regs2 27 = getr regs1 27)
  by (rewrite (hs5_pres_at _ _ (27%bv : bv 5) 27 HP2 eq_refl ltac:(unfold acallee_saved; lia)); exact P27).
assert (Q21 : getr regs2 21 = getr regs1 21).
{ rewrite (hs5_pres_at _ _ (21%bv : bv 5) 21 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P21, H21.
  transitivity (sv_denot E (hs5_shx 27)).
  { unfold hs5_shx. cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
  rewrite denot_lit_U, (hs5_U_shx E 27%nat (i_ptok x + 8 * Z.of_nat n)); [reflexivity | | |].
  - rewrite (EE 23%nat 23%bv eq_refl), R23. apply unsigned_lit_small. unfold HS_SB. lia.
  - rewrite (EE 27%nat 27%bv eq_refl), H27. apply unsigned_lit_small. lia.
  - lia. }
apply (HR lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 b1 Hn HCX).
- unfold hs_mid. cbv zeta.
  split; [exact HJ2|]. split; [exact Hk|]. split; [exact HMLE|]. split; [exact HBB|].
  split; [exact HFR2 | exact HBA].
- exact Hb0.
- exact Hb1.
- exact HREP2.
- split; [|split; [rewrite Q19; exact H19 | rewrite Q24; exact H24]].
  split; [rewrite Q2; exact R2|]. split; [rewrite Q3; exact R3|]. split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|]. split; [rewrite Q9; exact R9|].
  split; [rewrite Q22; exact R22 | rewrite Q23; exact R23].
- rewrite Q18. exact H18.
- rewrite HQ2. reflexivity.
- rewrite Q25. exact H25.
- rewrite Q26. exact H26.
- rewrite Q27. exact H27.
- rewrite Q20. exact H20.
- rewrite Q21. exact H21.
Qed.

(* ---- the loop's tail ---- *)
Lemma hs5_seed_R : forall (W : world SEGS) (regs1 : bvmap 5 word) mem,
st_ok_pi SEGS VAL (hs5_E regs1 []) hs5_ssR
  (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + HS_L1R)) mem (seg_rom SEGS))).
Proof.
intros W regs1 mem. rewrite restrict_mkst_fx. unfold hs5_ssR.
apply pa_entry_st_ok_full.
- unfold hs5_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma hs5_j_nev : forall STK sp0 FP ly S (W : world SEGS) mem md own lyc Sc (Wc : world SEGS) memc mdc k,
ajournal SEGS B STK sp0 FP ly S W mem md own lyc Sc Wc memc mdc k -> st_nev Sc <= st_nev S + k.
Proof. intros * HJ. destruct HJ as (_&_&_&_&_&_& H &_). exact H. Qed.

Lemma hs5_U_wsz : forall E m1 m2 v1 v2, bv_unsigned (ew E m1) = v1 -> bv_unsigned (ew E m2) = v2 ->
0 <= v1 -> 0 <= v2 -> v1 + 2 + v2 < M64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SOff m1 2) (SOff m2 0))
      (SAlu ALU_SLTU (SAlu ALU_ADD (SOff m1 2) (SOff m2 0)) (SLit 1))) = v1 + 2 + v2.
Proof.
intros E m1 m2 v1 v2 H1 H2 R1 R2 R3.
assert (HA : U E (SAlu ALU_ADD (SOff m1 2) (SOff m2 0)) = v1 + 2 + v2).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, H1, H2.
  rewrite (zcanon_id (v1 + 2)) by lia. rewrite (zcanon_id (v2 + 0)) by lia.
  rewrite Z.add_0_r. apply zcanon_id. lia. }
rewrite (U_SAlu E ALU_ADD). cbn [zalu_raw]. rewrite (U_SAlu E ALU_SLTU). cbn [zalu_raw].
rewrite !HA, U_SLit, (zcanon_id 1) by (unfold M64; lia).
replace (v1 + 2 + v2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (zcanon_id 0) by (unfold M64; lia). rewrite Z.add_0_r. apply zcanon_id. lia.
Qed.

Lemma hs5_U_add2 : forall E m1 z1 m2 z2 v1 v2,
bv_unsigned (ew E m1) = v1 -> bv_unsigned (ew E m2) = v2 ->
0 <= v1 + z1 < M64 -> 0 <= v2 + z2 < M64 -> 0 <= v1 + z1 + (v2 + z2) < M64 ->
U E (SAlu ALU_ADD (SOff m1 z1) (SOff m2 z2)) = v1 + z1 + (v2 + z2).
Proof.
intros E m1 z1 m2 z2 v1 v2 H1 H2 R1 R2 R3. rewrite U_SAlu. cbn [zalu_raw].
rewrite !U_SOff, H1, H2, (zcanon_id (v1 + z1)) by lia. rewrite (zcanon_id (v2 + z2)) by lia.
apply zcanon_id. lia.
Qed.

Lemma hs_seg_l1r : forall x n,
((S n < length (i_toks x))%nat -> ST_L1H B MT x (S n)) ->
(S n = length (i_toks x) -> ST_MAL B MT x) ->
ST_L1R B MT x n.
Proof.
intros x n HNX HMAL. unfold ST_L1R.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 Hn HCX HMID Hb0 Hb1 HREP HREG H18 H10 H25 H26 H27 H20 H21.
pose proof HCX as HCXc. unfold hs_cx in HCXc. cbv zeta in HCXc.
destruct HCXc as (HPRE & HROD & HROO & HROIN & HGRD & Hr10 & Hr11 & Hr12 & Hntok & HLINE & Hptok0 & Hptok8 &
  HARR & Hlenps & HPTR & HTOKS & HWL & HREPe & HFRe & HEV & HLIVE & HMOK & HTAIL).
pose proof HMID as HMIDc. unfold hs_mid in HMIDc. cbv zeta in HMIDc.
destruct HMIDc as (HJ & Hk & HMLE & HBB & HFRAME & HBA).
pose proof HBA as HBAc. unfold hs_ba in HBAc. cbv zeta in HBAc.
destruct HBAc as (HPERM & HRest1 & HRest2 & HO1a & HO1b & HNwO & HO1R).
pose proof HREG as HREGc. destruct HREGc as (HREG0 & H19 & H24).
destruct HREG0 as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
pose proof HPRE as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
pose proof hs5_stk as WS. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x))).
{ intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREPe pn Hpn)). }
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_or_app. right. exact (HRest2 pn Hpn Hno). }
assert (HBLIVE : forall pn, In pn (O1 ++ [b0; b1]) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_app_or in Hpn as [Hpn | Hpn]; apply in_or_app; [right; exact (HO1R pn Hpn) | left; exact Hpn]. }
(* the size of the word list *)
assert (Htokn : Z.of_nat (length (hs_tok x n)) + 1 <= hs_words_len (i_toks x))
  by (apply hs5_words_tok_le; lia).
pose proof (hs5_words_firstn_le n (i_toks x)) as Hfle.
pose proof (hs5_words_nonneg (firstn n (i_toks x))) as Hfnn.
pose proof (hs5_words_nonneg (i_toks x)) as Hwnn.
pose proof (hs5_words_firstn_S n (i_toks x) ltac:(lia)) as HfS.
change (nth n (i_toks x) []) with (hs_tok x n) in HfS.
destruct (hs5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) (8 * Z.of_nat n)
  HARe HJ HO Hlive HARR ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & _ & _).
assert (Hdq : 0 <= (i_ptok x + 8 * Z.of_nat n) / 8 <= i_ptok x + 8 * Z.of_nat n)
  by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
pose proof (hs5_seed_R Wc regs1 memc) as HS.
set (E := hs5_E regs1 []) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hs5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hs5_E_img).
assert (SHOK : sh_ok SEGS hs5_Bx (@nil shent) E (mrestrict (w_H Wc) memc)) by apply Forall_nil.
unfold hs_at.
(* 0x8b1a0 .. 0x8b1b8: the loop's increments and the back edge *)
paj_run_tok RUN HS HJ SHOK hs5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
rename HFr into HFRa. rename ms into msa.
psrr_branch_tok RUN BR HS SHOK hs5_Bspan.
- (* taken: tokens are left, back to 0x8b190 *)
  assert (HSn : (S n < length (i_toks x))%nat).
  { rewrite branch_ne_U in Hc. apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    rewrite U_SOff, (EE 26%nat 26%bv eq_refl), H26, U_SLit in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite (zcanon_id (Z.of_nat (length (i_toks x) - n) + -1)) in Hc by (unfold M64; lia).
    rewrite (zcanon_id 0) in Hc by (unfold M64; lia). lia. }
  paj_run_to_tok RUNTO HS HJ SHOK hs5_Bspan HS_L1H.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
    apply (awr_ok_nil SEGS B). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl) in P2.
  prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl) in P3.
  prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  prreg HS (18%bv : bv 5) P18. rewrite (EE 18%nat 18%bv eq_refl) in P18.
  prreg HS (19%bv : bv 5) P19. rewrite (EE 19%nat 19%bv eq_refl) in P19.
  prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl) in P22.
  prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl) in P23.
  prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl) in P24.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
  prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26. prreg HS (27%bv : bv 5) P27.
  apply (HNX HSn lyc Sc Wc (ms_mem ms) mdw (ms_regs ms) k O1 Rest b0 b1 HSn HCX).
  + unfold hs_mid. cbv zeta.
    split; [exact HJ|]. split; [exact Hk|]. split; [exact HMLE|]. split; [exact HBB|]. split; [|exact HBA].
    intros j r Hjr.
    assert (Hj : (j < length HS_SAVED)%nat) by (apply (proj1 (nth_error_Some HS_SAVED j)); rewrite Hjr; discriminate).
    unfold HS_SAVED in Hj. cbn [length] in Hj.
    intros kk Hkk. rewrite (KEEP2 (spZ (i_regs x) - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)).
    exact (HFRAME j r Hjr kk Hkk).
  + exact Hb0.
  + exact Hb1.
  + apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc (ms_mem ms)) _ _ HREP); [|exact HBLIVE].
    intros a [Hrec | Hown].
    * apply KEEP2. unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hrec. lia.
    * destruct Hown as ([q m] & Hpn & Hr). cbn [fst snd] in Hr.
      destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdw q m (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
        (HBLIVE (q, m) Hpn)) as (_ & Hq4 & Hqc & _ & _ & _ & Hmr).
      pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2]. apply KEEP2. lia.
  + split; [|split; [rewrite P19; exact H19 | rewrite P24; exact H24]].
    split; [rewrite P2; exact R2|]. split; [rewrite P3; exact R3|]. split; [rewrite P4; exact R4|].
    split; [rewrite P8; exact R8|]. split; [rewrite P9; exact R9|].
    split; [rewrite P22; exact R22 | rewrite P23; exact R23].
  + rewrite P18. exact H18.
  + rewrite P25. transitivity (sv_denot E (SAlu ALU_ADD (SOff 10 1) (SOff 25 0))).
    { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
    rewrite denot_lit_U, (hs5_U_add2 E 10%nat 1 25%nat 0
      (Z.of_nat (length (hs_tok x n))) (hs_words_len (firstn n (i_toks x))));
      [ unfold w64; f_equal; lia
      | rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | rewrite (EE 25%nat 25%bv eq_refl), H25; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia | unfold M64, LMAX in *; lia ].
  + rewrite P26, (EE 26%nat 26%bv eq_refl), H26. unfold w64. rewrite unsigned_lit_small by lia.
    f_equal. lia.
  + rewrite P27, (EE 27%nat 27%bv eq_refl), H27. unfold w64. rewrite unsigned_lit_small by lia.
    f_equal. lia.
  + rewrite P20, (EE 20%nat 20%bv eq_refl), H20. unfold w64. rewrite unsigned_lit_small by lia.
    f_equal. lia.
  + rewrite P21, (EE 21%nat 21%bv eq_refl), H21. unfold w64. rewrite unsigned_lit_small by (unfold HS_SB; lia).
    f_equal. replace (i_ptok x + 8 * Z.of_nat (S n)) with (i_ptok x + 8 * Z.of_nat n + 1 * 8) by lia.
    rewrite Z.div_add by lia. lia.
- (* the exit: the last token was read; the malloc of the word list *)
  assert (HSn : S n = length (i_toks x)).
  { rewrite branch_ne_U in Hc. apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    rewrite U_SOff, (EE 26%nat 26%bv eq_refl), H26, U_SLit in Hc.
    unfold w64 in Hc. rewrite unsigned_lit_small in Hc by lia.
    rewrite (zcanon_id (Z.of_nat (length (i_toks x) - n) + -1)) in Hc by (unfold M64; lia).
    rewrite (zcanon_id 0) in Hc by (unfold M64; lia). lia. }
  assert (HWSZ : hs_wsz x = Z.of_nat (length (hs_tok x n)) + 2 + hs_words_len (firstn n (i_toks x))).
  { assert (Hall : firstn (S n) (i_toks x) = i_toks x) by (rewrite HSn; apply firstn_all).
    rewrite Hall in HfS. unfold hs_wsz. lia. }
  paj_run_tok RUN HS HJ SHOK hs5_Bspan.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
    apply (awr_ok_nil SEGS B). }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdw := mdx) in *; clearbody mdw end.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha. rewrite <- (KEEP1 a Ha).
    apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr);
      [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin; destruct Hin | exact Ha | intros [] ]. }
  pmkst HS. rewrite (pal_malloc B hTL).
  prreg HS (1%bv : bv 5) P1.
  prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl) in P2.
  prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl) in P3.
  prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl) in P4.
  prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
  prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
  prreg HS (18%bv : bv 5) P18. rewrite (EE 18%nat 18%bv eq_refl) in P18.
  prreg HS (19%bv : bv 5) P19. rewrite (EE 19%nat 19%bv eq_refl) in P19.
  prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl) in P22.
  prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl) in P23.
  prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl) in P24.
  prreg HS (10%bv : bv 5) P10.
  assert (Hsp : spZ (ms_regs ms) = spZ (i_regs x) + -112).
  { unfold spZ at 1. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (Hram : 4096 <= raZ (ms_regs ms)).
  { unfold raZ. rewrite P1. rewrite unsigned_lit_small by lia. lia. }
  assert (HA0 : getr (ms_regs ms) 10 = w64 (hs_wsz x)).
  { rewrite P10.
    transitivity (sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 10 2) (SOff 25 0))
      (SAlu ALU_SLTU (SAlu ALU_ADD (SOff 10 2) (SOff 25 0)) (SLit 1)))).
    { cbn [sv_denot]. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity. }
    rewrite denot_lit_U, (hs5_U_wsz E 10%nat 25%nat
      (Z.of_nat (length (hs_tok x n))) (hs_words_len (firstn n (i_toks x))));
      [ unfold w64; f_equal; lia
      | rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | rewrite (EE 25%nat 25%bv eq_refl), H25; unfold w64; apply unsigned_lit_small; unfold LMAX in *; lia
      | lia | lia | unfold M64, LMAX in *; lia ]. }
  assert (Hnev : st_nev Sc < EV_MAX).
  { pose proof (hs5_j_nev _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as Hn7.
    unfold hs_k2, hs_k0 in Hk. unfold EV_SUP_HOST_SETTING, EV_XSTRDUP in HEV. lia. }
  assert (Hwsz1 : 0 <= hs_wsz x < MALLOC_MAX).
  { unfold hs_wsz, MALLOC_MAX, LMAX in *. lia. }
  assert (Hwlive : blocks_bytes Sc + hs_wsz x <= LIVE_MAX).
  { pose proof HBB as HBB'. rewrite !bsum_cons in HBB'. change (bsum (@nil (Z * Z))) with 0 in HBB'.
    rewrite Hb0, Hb1 in HBB'.
    pose proof HLIVE as HL'. unfold LIVE_SUP_HOST_SETTING, LIVE_XSTRDUP in HL'.
    unfold hs_wsz. lia. }
  assert (Hchain : chain_pre lyc (rdW Wc (ms_mem ms)) (ms_regs ms) []).
  { pose proof (hs_slot_bounds (i_R x)) as (Hs1 & Hs2 & _ & _).
    apply (achain_chain_pre lyc (rdW Wc (ms_mem ms)) (spZ (ms_regs ms)) (s0Z (ms_regs ms)) [] (ms_regs ms));
      [| lia | reflexivity | exact Hram].
    apply achain_low. unfold s0Z. rewrite P8, R8. unfold w64. rewrite unsigned_lit_small by
      (unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *; lia).
    unfold A_G_REC, OFF_CALLS, A_REC_SPILL, SC_SIZE, CALL_SIZE in *. lia. }
  assert (MOK2 : mo_ok MT Sc (mo_malloc MT (hs_wsz x))).
  { apply (mok_station MT (i_S x) Sc (XM_SUP_HOST_SETTING MT (i_R x) (i_line x) (i_toks x)) (hs_m2 MT x)
      (mo_malloc MT (hs_wsz x)) hMTL HMOK HMLE).
    - apply (mo_malloc_nonneg MT hMTL). unfold hs_wsz. lia.
    - unfold XM_SUP_HOST_SETTING, hs_m2, hs_m0, hs_wsz.
      pose proof (mo_free_nonneg MT hMTL) as Hfr0.
      pose proof (mo_malloc_nonneg MT hMTL (Z.of_nat (length (join_sp (i_toks x))) + 1) ltac:(lia)) as Hx0.
      unfold XM_XSTRDUP. lia. }
  eapply SRr_bind.
  { eapply (amalloc04_sub SEGS B LAWS pa_segs_low MT hMALLOC Wc (ms_regs ms) (ms_mem ms)
      SUP_HOST_SETTING_STK (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
      lyc Sc mdw k (hs_wsz x) (-112) (Z_to_bv 64 (BASE + HS_MAL)) [] HJ HA0 Hwsz1 Hwlive Hsp eq_refl
      ltac:(lia) ltac:(lia));
      [rewrite P3, R3; exact Hgp | rewrite P4, R4; exact Htp | exact P1
      | apply ret_ok_codeptr_v; [unfold HS_MAL; lia | unfold HS_MAL; reflexivity]
      | exact Hnev | exact Hchain | exact MOK2]. }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Hres10 & Hfrs2 & Hr4096 &
    Eab & HK2 & MLE2 & HJin).
  (* back at 0x8b1d4 with the new block *)
  pose proof (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HAR2.
  assert (Hfresh : forall q m, In (q, m) (ablocks B lyc Sc) -> zdisjoint (q, req_size m) (res, req_size (hs_wsz x)))
    by (intros q m Hin; exact (recb_fresh_disj_m B ly2 S2 W2 mem2 md2 (ablocks B lyc Sc) res (hs_wsz x) q m HAR2 Eab Hin)).
  assert (KEEPB : forall q m i, In (q, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
    rdW W2 mem2 (q + i) = rdW Wc (ms_mem ms) (q + i)).
  { intros q m i Hin Hi. destruct HK2 as (_ & K2 & _). apply (K2 q m i Hin Hi).
    pose proof (Hfresh q m Hin) as Hd. unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
  assert (KEEPI : forall a, Exists (in_zr a) recb_PG -> rdW W2 mem2 a = rdW Wc (ms_mem ms) a).
  { intros a Hpg. destruct HK2 as (_ & _ & K3 & _). destruct (recb_prog_unowned_m B hHB hPIMG a Hpg) as (G1 & G2 & G3).
    exact (K3 a G1 G2 G3). }
  assert (KEEPFR : forall a, spZ (i_regs x) - 112 <= a < spZ (i_regs x) -> rdW W2 mem2 a = rdW Wc memc a).
  { intros a Ha. destruct HK2 as (K1 & _). rewrite (K1 a ltac:(lia) ltac:(lia)). apply KEEP2. lia. }
  assert (HBLIVE2 : forall pn, In pn (O1 ++ [b0; b1]) -> In pn (ablocks B ly2 S2)).
  { intros pn Hpn. rewrite Eab. apply in_or_app. left. exact (HBLIVE pn Hpn). }
  apply (HMAL HSn ly2 S2 W2 mem2 md2 regs2 (k + 1) O1 Rest b0 b1 res HCX).
  + unfold hs_mid. cbv zeta.
    split; [exact HJ2|].
    split; [unfold hs_k3; lia|].
    split.
    { apply (mle_weaken MT (i_S x) S2 (hs_m2 MT x + mo_malloc MT (hs_wsz x)) (hs_m3 MT x) hMTL);
        [exact (mle_station MT (i_S x) Sc S2 (hs_m2 MT x) (mo_malloc MT (hs_wsz x)) hMTL HMLE MLE2)
        | unfold hs_m3, hs_wsz; lia]. }
    split.
    { pose proof HBB as HBB2. rewrite (blocks_bytes_bsum B lyc Sc) in HBB2.
      rewrite !bsum_cons in HBB2. change (bsum (@nil (Z * Z))) with 0 in HBB2.
      rewrite (blocks_bytes_bsum B ly2 S2), Eab, bsum_app.
      rewrite !bsum_cons. change (bsum (@nil (Z * Z))) with 0. cbn [snd]. lia. }
    split.
    { intros j r Hjr.
      assert (Hj : (j < length HS_SAVED)%nat) by (apply (proj1 (nth_error_Some HS_SAVED j)); rewrite Hjr; discriminate).
      unfold HS_SAVED in Hj. cbn [length] in Hj.
      intros kk Hkk. rewrite (KEEPFR (spZ (i_regs x) - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)).
      exact (HFRAME j r Hjr kk Hkk). }
    unfold hs_ba. cbv zeta.
    split.
    { rewrite Eab.
      eapply Permutation_trans; [apply (Permutation_app_tail [(res, hs_wsz x)] HPERM)|].
      cbn [app]. apply perm_skip. apply perm_skip. apply (Permutation_app_comm Rest [(res, hs_wsz x)]). }
    split; [exact HRest1|]. split; [exact HRest2|]. split; [exact HO1a|]. split; [exact HO1b|].
    split; [|exact HO1R].
    intros pn Hpn Hin. cbn [In] in Hpn.
    destruct Hpn as [Hb | [Hb | [Hb | []]]].
    * apply (HNwO pn); [cbn [In]; left; exact Hb | exact Hin].
    * apply (HNwO pn); [cbn [In]; right; left; exact Hb | exact Hin].
    * rewrite <- Hb. rewrite <- Hb in Hin.
      destruct (in_dec (fun u v : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (res, hs_wsz x) (i_O x))
        as [Ho | Ho]; [exact Ho|].
      exfalso. pose proof (req_size_pos (hs_wsz x) ltac:(unfold hs_wsz; lia)) as [Hr1 _].
      pose proof (Hfresh res (hs_wsz x) (Hlive (res, hs_wsz x) Hin Ho)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  + exact Hb0.
  + exact Hb1.
  + apply (hs_rec_kept B lyc Sc ly2 S2 (rdW Wc memc) (rdW W2 mem2) _ _ HREP); [|exact HBLIVE2].
    intros a [Hrec | Hown].
    * rewrite (KEEPI a).
      { apply KEEP2. unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hrec. lia. }
      { unfold hs_in_rec in Hrec. destruct Hrec as [Hg | Hs];
          [apply recb_grec_in; lia | apply recb_spill_in; lia]. }
    * destruct Hown as ([q m] & Hpn & Hr). cbn [fst snd] in Hr.
      destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdw q m (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
        (HBLIVE (q, m) Hpn)) as (_ & Hq4 & Hqc & _ & _ & _ & Hmr).
      pose proof (req_size_pos m ltac:(lia)) as [Hr1 Hr2].
      replace a with (q + (a - q)) by lia.
      rewrite (KEEPB q m (a - q) (HBLIVE (q, m) Hpn) ltac:(lia)). apply KEEP2. lia.
  + split; [|split].
    * split; [rewrite (hs5_pres_at _ _ (2%bv : bv 5) 2 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P2; exact R2|].
      split; [rewrite (hs5_pres_at _ _ (3%bv : bv 5) 3 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P3; exact R3|].
      split; [rewrite (hs5_pres_at _ _ (4%bv : bv 5) 4 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P4; exact R4|].
      split; [rewrite (hs5_pres_at _ _ (8%bv : bv 5) 8 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P8; exact R8|].
      split; [rewrite (hs5_pres_at _ _ (9%bv : bv 5) 9 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P9; exact R9|].
      split; [rewrite (hs5_pres_at _ _ (22%bv : bv 5) 22 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P22; exact R22
             |rewrite (hs5_pres_at _ _ (23%bv : bv 5) 23 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P23; exact R23].
    * rewrite (hs5_pres_at _ _ (19%bv : bv 5) 19 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P19. exact H19.
    * rewrite (hs5_pres_at _ _ (24%bv : bv 5) 24 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P24. exact H24.
  + rewrite (hs5_pres_at _ _ (18%bv : bv 5) 18 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P18. exact H18.
  + exact Hres10.
  + exact Hr4096.
Qed.

(* ---- the malloc return: the empty word list and the strcat wrapper on token 0 ---- *)
(* The step through a runtime entry (art_post, lib/A/Rt/RtDefs.v) that writes inside one live block [bq, bq + req_size
   nq), a block the call may write (footprint or made in this call): PaArt's aj_art_at with the entry's cells in that
   block instead of the errno cell, the inner journal's footprint the block. *)
Lemma hs5_art_wr_at : forall stk (Eb : Z -> Prop) pc (W : world SEGS) regsT memT STK sp0 FP ly S W0 mem md own lyc Sc
  mdc k (o : Z) raw bq nq (Qr : bvmap 5 word -> (word -> option byte) -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= stk -> stk - o <= STK ->
getr regsT 1 = raw ->
In (bq, nq) (ablocks B lyc Sc) -> (forall a, Eb a -> bq <= a < bq + req_size nq) ->
(forall a, bq <= a < bq + req_size nq ->
  (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n) \/
  in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a) ->
SRr SEGS W (cfg_at SEGS pc regsT memT mdc) (art_post SEGS B stk lyc Sc W regsT memT mdc Eb Qr) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 pc) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 k /\
  aregs_preserved regsT regs2 /\ Qr regs2 mem2 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - stk <= a < sp0 + o) -> ~ Eb a ->
   rdW W mem2 a = rdW W memT a)).
Proof.
intros stk Eb pc W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc k o raw bq nq Qr
  HJ Hsp Hal Hneg Hstk Hbud Hraw Hbq HEb Hcov HC.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
eapply SRr_mono; [exact HC|].
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & HQ & Hfr & Hpres2 & Hscr).
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Hraw, Z_to_bv_bv_unsigned; reflexivity|].
split.
{ assert (HJ1 : ajournal SEGS B stk (spZ regsT) (ablocks_fp [(bq, nq)]) lyc Sc W memT mdc [] lyc Sc W mem2 md2 0).
  { eapply (call_effect_journal SEGS B LAWS pa_segs_low (pal_env B hTL) stk lyc Sc W regsT memT mdc lyc Sc W mem2 md2
      Eb (ablocks_fp [(bq, nq)]) [] 0);
    [exact HAR2 | apply layout_le_refl | apply wle_refl | apply same_io_materialized; exact Hsame | | exact Hscr
    | exact HAR | | reflexivity | lia | lia | lia | | intros p n i H1 H2; exfalso; exact (H2 H1) | exact HQT].
    - intros a H0 _ _ H3 H4. apply (Hfr a H0); [intros Hs; apply H3; left; exact Hs | exact H4].
    - unfold astk_ok, ly_bot in *. rewrite Etop, Eslo, Eshi. rewrite Hsp.
      repeat split; first [rewrite Z.add_mod, Hal16, Hal by lia; reflexivity | lia].
    - intros a Ha. exists bq, nq. split; [left; exact Hbq|]. split; [exact (HEb a Ha)|].
      left. pose proof (HEb a Ha) as Hr. replace a with (bq + (a - bq)) by lia.
      apply (inFP_ablocks_fp [(bq, nq)] bq nq (a - bq)); [left; reflexivity | lia]. }
  pose proof (ajournal_sub_tok SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc k stk (spZ regsT)
    (ablocks_fp [(bq, nq)]) [] lyc Sc W mem2 md2 0 HJ HJ1 ltac:(lia) ltac:(lia)) as HJ2.
  rewrite app_nil_l, Z.add_0_r in HJ2. apply HJ2.
  intros a Ha. destruct (inFP_ablocks_fp_inv _ a Ha) as (p' & n' & Hpn & Hr).
  destruct Hpn as [Hpn | []]. injection Hpn as <- <-. exact (Hcov a Hr). }
split; [exact HP|]. split; [exact HQ|].
intros a Ha Hw He. apply (Hfr a Ha); [|exact He]. unfold ascratch_stk. rewrite Hsp. exact Hw.
Qed.

(* a string argument is apart from a live block that is the recorder's or was made in the call *)
Lemma hs5_arg_apart : forall ly S (W : world SEGS) mem md lyc Sc (Wc : world SEGS) memc mdc O p s q m,
AR SEGS B ly S W mem md -> AR SEGS B lyc Sc Wc memc mdc ->
hs_str B ly S (rdW W mem) O p s ->
(forall pn, In pn (ablocks B ly S) -> ~ In pn O -> In pn (ablocks B lyc Sc)) ->
In (q, m) (ablocks B lyc Sc) -> (In (q, m) O \/ ~ In (q, m) (ablocks B ly S)) ->
q + req_size m <= p \/ p + Z.of_nat (length s) + 1 <= q.
Proof.
intros ly S W mem md lyc Sc Wc memc mdc O p s q m HARe HARc HARG Hlive Hqm HqO.
unfold hs_str in HARG. destruct HARG as (Hp0 & HSTR & Hnle & HBLK & HAP).
destruct HBLK as (q0 & m0 & Hq0 & Hq1 & Hq2).
assert (Hno : ~ In (q0, m0) O).
{ intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q0, m0) Hin) as Hap.
  unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
assert (Hne : (q0, m0) <> (q, m)).
{ intros E. rewrite E in Hno, Hq0. destruct HqO as [H | H]; [exact (Hno H) | exact (H Hq0)]. }
pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q0 m0 q m HARc (Hlive (q0, m0) Hq0 Hno) Hqm Hne) as Hd.
destruct (al_blocks _ _ LAWS ly S W mem md q0 m0 HARe Hq0) as (_ & _ & _ & _ & _ & _ & Hmr).
pose proof (req_size_pos m0 ltac:(lia)) as [_ Hr0].
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Lemma hs_seg_mal : forall x, ST_L2C B MT x 0 -> ST_MAL B MT x.
Proof.
intros x HL2. unfold ST_MAL.
intros lyc Sc Wc memc mdc regs1 k O1 Rest b0 b1 w HCX HMID Hb0 Hb1 HREP HREG H18 H10 Hw4096.
pose proof HCX as HCXc. unfold hs_cx in HCXc. cbv zeta in HCXc.
destruct HCXc as (HPRE & HROD & HROO & HROIN & HGRD & Hr10 & Hr11 & Hr12 & Hntok & HLINE & Hptok0 & Hptok8 &
  HARR & Hlenps & HPTR & HTOKS & HWL & HREPe & HFRe & HEV & HLIVE & HMOK & HTAIL).
pose proof HMID as HMIDc. unfold hs_mid in HMIDc. cbv zeta in HMIDc.
destruct HMIDc as (HJ & Hk & HMLE & HBB & HFRAME & HBA).
pose proof HBA as HBAc. unfold hs_ba in HBAc. cbv zeta in HBAc.
destruct HBAc as (HPERM & HRest1 & HRest2 & HO1a & HO1b & HNwO & HO1R).
pose proof HREG as HREGc. destruct HREGc as (HREG0 & H19 & H24).
destruct HREG0 as (R2 & R3 & R4 & R8 & R9 & R22 & R23).
pose proof HPRE as (HARe & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE.
pose proof hs5_stk as WS. assert (Has : ASTACK = 16384) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HO : forall pn, In pn (i_O x) -> In pn (ablocks B (i_ly x) (i_S x))).
{ intros pn Hpn. exact (proj1 (hs_rec_own B _ _ _ _ _ HREPe pn Hpn)). }
assert (Hlive : forall pn, In pn (ablocks B (i_ly x) (i_S x)) -> ~ In pn (i_O x) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn Hno. apply (Permutation_in _ (Permutation_sym HPERM)).
  apply in_or_app. right. exact (HRest2 pn Hpn Hno). }
assert (HNWL : forall pn, In pn [b0; b1; (w, hs_wsz x)] -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. left. exact Hpn. }
assert (HBLIVE : forall pn, In pn (O1 ++ [b0; b1]) -> In pn (ablocks B lyc Sc)).
{ intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn].
  - apply (Permutation_in _ (Permutation_sym HPERM)). apply in_or_app. right. exact (HO1R pn Hpn).
  - apply HNWL. destruct Hpn as [<- | [<- | []]]; [left | right; left]; reflexivity. }
pose proof (HJ) as HJ0.
pose proof (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARc.
(* the word list's block *)
assert (Hwin : In (w, hs_wsz x) (ablocks B lyc Sc)) by (apply HNWL; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc w (hs_wsz x) HARc Hwin) as (Hw16 & _ & Hwceil & Hwapp & Hwpres & _ & Hwmr).
pose proof (hs5_words_nonneg (i_toks x)) as Hwnn.
assert (Hrw : req_size (hs_wsz x) = hs_wsz x) by (unfold req_size, hs_wsz; destruct (_ =? 0) eqn:E;
  [apply Z.eqb_eq in E; lia | reflexivity]).
assert (Hwsz1 : 1 <= hs_wsz x) by (unfold hs_wsz; lia).
assert (HwO : In (w, hs_wsz x) (i_O x) \/ ~ In (w, hs_wsz x) (ablocks B (i_ly x) (i_S x))).
{ destruct (in_dec (fun u v : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (w, hs_wsz x) (i_O x)) as [Ho | Ho];
    [left; exact Ho | right; intros Hin; apply Ho; apply (HNwO _ ltac:(right; right; left; reflexivity) Hin)]. }
assert (Hwcov : forall a, w <= a < w + req_size (hs_wsz x) ->
  (inFP (hs_FP (i_O x)) a /\ exists bb nn, In (bb, nn) (ablocks B lyc Sc) /\ bb <= a < bb + req_size nn) \/
  in_tmp_block (ablocks B (i_ly x) (i_S x)) (ablocks B lyc Sc) a).
{ intros a Ha. destruct HwO as [Ho | Hn].
  - left. split; [|exists w, (hs_wsz x); split; [exact Hwin | exact Ha]].
    unfold hs_FP. apply inFP_cons. right. apply inFP_cons. right.
    replace a with (w + (a - w)) by lia. apply (inFP_ablocks_fp (i_O x) w (hs_wsz x) (a - w)); [exact Ho | lia].
  - right. exists w, (hs_wsz x). split; [exact Hwin|]. split; [exact Hn | exact Ha]. }
(* token 0 *)
assert (Hn0 : (0 < length (i_toks x))%nat) by lia.
assert (Hnp : nth_error (i_ps x) 0 = Some (hs_ptr x 0)) by (apply nth_error_nth'; lia).
assert (Hnt : nth_error (i_toks x) 0 = Some (hs_tok x 0)) by (apply nth_error_nth'; lia).
pose proof (HPTR 0%nat _ Hnp) as HVAL.
pose proof (hs5_forall2_nth _ _ _ 0%nat _ _ HTOKS Hnp Hnt) as HARG.
pose proof (HTAIL 0%nat _ _ Hnp Hnt) as HTl.
assert (Htok0 : Z.of_nat (length (hs_tok x 0)) + 1 <= hs_words_len (i_toks x)) by (apply hs5_words_tok_le; lia).
pose proof (hs5_arg_apart (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) lyc Sc Wc memc mdc (i_O x)
  (hs_ptr x 0) (hs_tok x 0) w (hs_wsz x) HARe HARc HARG Hlive Hwin HwO) as Hapart.
destruct (hs5_arr_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k (i_O x) (i_ptok x) (8 * Z.of_nat (length (i_toks x))) 0
  HARe HJ HO Hlive HARR ltac:(lia) ltac:(lia)) as (Ha1 & Ha2 & Happ & Hkeptarr & HRAarr).
rewrite Z.add_0_r in Ha1, Ha2, Happ, Hkeptarr, HRAarr.
pose proof (hs5_arg_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc memc mdc k (i_O x) (hs_ptr x 0) (hs_tok x 0) HARe HJ HO Hlive HARG HTl) as HAOK0.
pose proof HAOK0 as (Hp1 & Hp2 & Hp3 & _).
assert (HVALc : val_mem SEGS (mrestrict (w_H Wc) memc) (i_ptok x) 8 (hs_ptr x 0)).
{ apply val_mem_view. intros kk Hkk. rewrite (Hkeptarr (Z.of_nat kk) ltac:(lia)).
  pose proof (HVAL kk Hkk) as Hv. rewrite Z.add_0_r in Hv. exact Hv. }
(* the token array is apart from the word list's block *)
assert (Hdisj : w + 1 <= i_ptok x \/ i_ptok x + 8 <= w).
{ destruct HARR as [((cid & pos & Hin & Hcid & Hal & Hf1 & Hf2) & _ & _) | [(q & m & Hqm & Hq1 & Hq2) HAP]].
  - assert (Hfc : In (cid, pos) (frames Sc)) by (rewrite (hs5_j_frames _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); exact Hin).
    pose proof (sep_block_frame SEGS B LAWS lyc Sc Wc memc mdc w (hs_wsz x) cid pos HARc Hwin Hfc) as Hd.
    rewrite (hs5_j_lay _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ cid pos HJ) in Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
  - assert (Hno : ~ In (q, m) (i_O x)).
    { intros Hin. rewrite Forall_forall in HAP. pose proof (HAP (q, m) Hin) as Hap.
      unfold iv_apart in Hap. cbn [fst snd] in Hap. lia. }
    assert (Hne : (q, m) <> (w, hs_wsz x)).
    { intros E. rewrite E in Hno, Hqm. destruct HwO as [H | H]; [exact (Hno H) | exact (H Hqm)]. }
    pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m w (hs_wsz x) HARc (Hlive (q, m) Hqm Hno) Hwin Hne) as Hd.
    destruct (al_blocks _ _ LAWS (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) q m HARe Hqm) as (_ & _ & _ & _ & _ & _ & Hmr).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hr0].
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
(* the seed at 0x8b1d4 *)
pose proof (hs5_seed_M Wc regs1 memc w (Z.of_nat (length (i_toks x))) (i_ptok x) (hs_ptr x 0)
  R23 R9 H10 H18 ltac:(lia) Hw4096 ltac:(lia) Hw16 ltac:(lia) ltac:(lia) Hptok8 ltac:(lia) Hdisj
  ltac:(intros o Ho; apply (apresent_writable SEGS); exact (proj1 (Hwpres (w + o) ltac:(lia))))
  HVALc) as HS.
set (E := hs5_E regs1 [Z_to_bv 64 (hs_ptr x 0)]) in HS.
assert (EE : forall kk (r : bv 5), Z.of_nat kk = bv_unsigned r -> ew E kk = getr regs1 r)
  by (intros kk r Hkk; unfold E; apply hs5_E_reg; exact Hkk).
assert (HEI : img_env VAL A_LIM E) by (unfold E; apply hs5_E_img).
assert (UBx : U E hs5_Bx = SHADOW_OFF).
{ unfold hs5_Bx. rewrite U_SOff, (EE 23%nat 23%bv eq_refl), R23, Z.add_0_r.
  unfold w64, HS_SB, SHADOW_OFF. rewrite unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U10 : U E (SOff 10 0) = w).
{ apply hs5_U_off0; [rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (U18 : U E (SOff 18 0) = i_ptok x).
{ apply hs5_U_off0; [rewrite (EE 18%nat 18%bv eq_refl), H18; unfold w64; apply unsigned_lit_small; lia
  | unfold M64; lia]. }
assert (SHOK : sh_ok SEGS hs5_Bx hs5_SHM E (mrestrict (w_H Wc) memc)).
{ unfold hs5_SHM. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (shent_ok_of_block SEGS B LAWS lyc Sc Wc memc mdc E hs5_Bx 10%nat w (hs_wsz x) 0 1 HARc Hwin UBx U10);
      lia.
  - eapply (shent_ok_of_range SEGS); [exact HRAarr | exact UBx | exact U18 | lia | lia |].
    cbn [Z.min Z.max]. intros z Hz. destruct Happ as (_ & [Hk1 | [Hk1 Hk2]]);
      unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia. }
unfold hs_at.
(* 0x8b1d4 .. 0x8b254: the null test, the store1 check, words[0] := 0, the loop entry, the load8 check on
   &tok[0], the call of the strcat wrapper on (w, tok[0]) *)
paj_run_tok RUN HS HJ SHOK hs5_Bspan.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0' ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0' bc fr lyx own) end.
  eapply awr_ok_cons_gen; [reflexivity | rewrite (EE 10%nat 10%bv eq_refl), H10; unfold w64;
    apply unsigned_lit_small; lia | |].
  - cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    destruct (Hwcov a ltac:(lia)) as [(Hfp & Hbl) | Htmp].
    + right; left. split; [exact Hfp | exact Hbl].
    + right; right; left. exact Htmp.
  - apply (awr_ok_cons_ro SEGS B); [cbn; lia|]. apply (awr_ok_nil SEGS B). }
lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdv := mdx) in *; clearbody mdv end.
(* the run wrote words[0] only *)
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (w <= a < w + 1) -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => w <= a < w + 1) HFr);
    [ intros bb wlo whi a' Hin Hrr; vm_compute in Hin;
      destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Hrr;
      rewrite (EE 10%nat 10%bv eq_refl), H10 in Hrr || idtac; unfold w64 in Hrr;
      first [rewrite unsigned_lit_small in Hrr by lia; lia | lia]
    | exact Ha | exact Hn ]. }
(* words[0] = 0 *)
pose proof (st_ok_region_nth _ _ _ 0 _ HS eq_refl) as HRg.
pose proof (field_of_region_any _ _ _ w _ _ _ _ _ 0 1 (SLit 0) HRg) as Hw0.
assert (Hw0' : rdW Wc (ms_mem ms) w = Some 0).
{ match type of Hw0 with ?A -> _ => assert (HA : A) end.
  { cbn [ew ewset Nat.eqb]. rewrite (EE 10%nat 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia. }
  specialize (Hw0 HA (or_introl eq_refl) ltac:(cbn; lia)).
  cbn [ms_mem restrict] in Hw0. rewrite Z.add_0_r in Hw0.
  pose proof (aval_mem_view SEGS (w_H Wc) (ms_mem ms) w 1 _ Hw0 0%nat ltac:(lia)) as Hb.
  rewrite Z.add_0_r in Hb. rewrite Hb. reflexivity. }
pmkst HS.
prreg HS (1%bv : bv 5) P1.
prreg HS (2%bv : bv 5) P2. rewrite (EE 2%nat 2%bv eq_refl) in P2.
prreg HS (3%bv : bv 5) P3. rewrite (EE 3%nat 3%bv eq_refl) in P3.
prreg HS (4%bv : bv 5) P4. rewrite (EE 4%nat 4%bv eq_refl) in P4.
prreg HS (8%bv : bv 5) P8. rewrite (EE 8%nat 8%bv eq_refl) in P8.
prreg HS (9%bv : bv 5) P9. rewrite (EE 9%nat 9%bv eq_refl) in P9.
prreg HS (10%bv : bv 5) P10. rewrite (EE 10%nat 10%bv eq_refl) in P10.
prreg HS (11%bv : bv 5) P11.
prreg HS (18%bv : bv 5) P18. rewrite (EE 18%nat 18%bv eq_refl) in P18.
prreg HS (19%bv : bv 5) P19. rewrite (EE 19%nat 19%bv eq_refl) in P19.
prreg HS (20%bv : bv 5) P20. rewrite (EE 10%nat 10%bv eq_refl) in P20.
prreg HS (21%bv : bv 5) P21. rewrite (EE 18%nat 18%bv eq_refl) in P21.
prreg HS (22%bv : bv 5) P22. rewrite (EE 22%nat 22%bv eq_refl) in P22.
prreg HS (23%bv : bv 5) P23. rewrite (EE 23%nat 23%bv eq_refl) in P23.
prreg HS (24%bv : bv 5) P24. rewrite (EE 24%nat 24%bv eq_refl) in P24.
prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
assert (P32 : ew E 32 = Z_to_bv 64 (hs_ptr x 0)) by (unfold E; apply hs5_E_x32).
rewrite P32 in P11.
assert (Hsp : spZ (ms_regs ms) = spZ (i_regs x) + -112).
{ unfold spZ at 1. rewrite P2, R2. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (HraT : YK0s.ret_ok (getr (ms_regs ms) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
(* token 0 at the state of the call *)
pose proof (hs5_arg_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) []
  lyc Sc Wc (ms_mem ms) mdv k (i_O x) (hs_ptr x 0) (hs_tok x 0) HARe HJ HO Hlive HARG HTl) as HAOK.
pose proof HAOK as (G1 & G2 & G3 & GSTR & GTl & GMR & GRA & GHU & GM8).
pose proof (hs5_j_AR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARm.
assert (Hwszd : hs_wsz x = hs_words_len (i_toks x) + 1) by reflexivity.
eapply SRr_bind.
{ eapply (hs5_art_wr_at (2 * ESTACK)
    (fun a => w + astr_len [] <= a < w + astr_len [] + astr_len (hs_tok x 0) + 1)
    (SIG CS___interceptor_trampoline_strcat) Wc (ms_regs ms) (ms_mem ms) SUP_HOST_SETTING_STK (spZ (i_regs x))
    (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc mdv k (-112)
    (Z_to_bv 64 (BASE + HS_L2C)) w (hs_wsz x) _ HJ Hsp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) P1 Hwin
    ltac:(intros a Ha; unfold astr_len in Ha; cbn [length] in Ha; lia) Hwcov).
  apply (hSTRCAT lyc Sc Wc (ms_regs ms) (ms_mem ms) mdv w (hs_ptr x 0) [] (hs_tok x 0)).
  - eapply (ecall_pre_stk_at SEGS B (2 * ESTACK) SUP_HOST_SETTING_STK
      (spZ (i_regs x)) (hs_FP (i_O x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x) [] lyc Sc Wc (ms_mem ms) mdv k
      (ms_regs ms) (-112) HJ Hsp eq_refl ltac:(lia) ltac:(lia) ltac:(lia) HraT);
      [rewrite P3, R3; exact Hgp | rewrite P4, R4; exact Htp].
  - rewrite P10. exact H10.
  - rewrite P11. reflexivity.
  - lia.
  - lia.
  - apply (astr_atR_view SEGS). split; [|intros []].
    intros i Hi. cbn [length app] in Hi. assert (i = 0%nat) as -> by lia. rewrite Z.add_0_r, Hw0'. reflexivity.
  - apply (astr_atR_view SEGS). exact GSTR.
  - unfold astr_len. cbn [length]. split; [lia|]. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [replace a with w by lia; rewrite Hw0'; discriminate | unfold ascratch_stk; lia]. }
    split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w 1 HARm Hwin ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w 1 HARm Hwin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w 1 HARm Hwin ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* to = the word list, a heap block: 8 bytes of band room past its (empty) string *)
    apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (astr_len []) HARm); [|unfold astr_len; cbn [length]; lia].
    exists w, (hs_wsz x). split; [exact Hwin | unfold astr_len; cbn [length]; split; lia].
  - exact (hs5_read_of_arg (2 * ESTACK) Wc (ms_mem ms) (ms_regs ms) (hs_ptr x 0) (hs_tok x 0) HAOK ltac:(lia) ltac:(lia)).
  - (* from = tok[0], in an entry block *)
    unfold astr_len. exact GM8.
  - unfold astr_len. cbn [length]. rewrite Z.add_0_r.
    split; [lia|]. split; [lia|]. split; [unfold LMAX in *; lia|]. split.
    { intros a Ha. destruct (Hwpres a ltac:(lia)) as [Hap Hno]. split; [|split].
      - apply (apresent_writable SEGS).
        destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) HARm Hwin) as (_ & _ & _ & _ & Hpm & _).
        exact (proj1 (Hpm a ltac:(lia))).
      - destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) HARm Hwin) as (_ & _ & _ & _ & Hpm & _).
        exact (proj2 (Hpm a ltac:(lia))).
      - unfold ascratch_stk. lia. }
    split; [exact (amem_range_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia))|].
    intros _. exact (shadow_hull_vis_of_block SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w (Z.of_nat (length (hs_tok x 0)) + 1) HARm Hwin ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* the written range, in the word list's block *)
    unfold astr_len. cbn [length]. rewrite Z.add_0_r.
    apply (amem8_of_blockA SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv w (Z.of_nat (length (hs_tok x 0))) HARm); [|lia].
    exists w, (hs_wsz x). split; [exact Hwin | split; lia].
  - (* the written range is the word list's block: a heap byte is no image byte, and a read-only byte is one *)
    intros a Ha _ (sg & Hsg & _ & Hrg). unfold astr_len in Ha. cbn [length] in Ha.
    exact (recb_heap_noimg_m B lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) a HARm Hwin ltac:(lia)
      (ex_intro _ sg (conj Hsg Hrg))).
  - unfold astr_len. cbn [length]. rewrite Z.add_0_r.
    exact (hHEAPT lyc Sc Wc (ms_mem ms) mdv w (hs_wsz x) w HARm Hwin ltac:(lia)).
  - unfold astr_len. exact GTl.
  - unfold astr_len. cbn [length]. lia.
  - (* the destination tail does not start inside the token's last word: the token's block and the word list's are
       apart (hs5_arg_apart) and the word list's block is 16-aligned, so the token's rounded end is at or below it *)
    unfold astr_len, aword_end. cbn [length]. destruct Hapart as [Hap | Hap]; [left; lia | right].
    pose proof (Z.mod_pos_bound (- (hs_ptr x 0 + (Z.of_nat (length (hs_tok x 0)) + 1))) 8 ltac:(lia)) as Hmb.
    pose proof (Z.div_mod (- (hs_ptr x 0 + (Z.of_nat (length (hs_tok x 0)) + 1))) 8 ltac:(discriminate)) as Hdm.
    pose proof (Z.div_mod w 16 ltac:(discriminate)) as Hdw. rewrite Hw16 in Hdw. lia.
  - apply hROM. exact (hs5_rod_now SUP_HOST_SETTING_STK (spZ (i_regs x)) (i_ly x) (i_S x) (i_W x) (i_mem x) (i_md x)
      [] lyc Sc Wc (ms_mem ms) mdv k (i_O x) HARe HJ HO HROD). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & (HQa & HQb) & HK2).
(* back at 0x8b258: the word list holds token 0 *)
(* the word list's block is none of the recorder's *)
assert (HNDc : List.NoDup ([b0; b1; (w, hs_wsz x)] ++ Rest))
  by exact (Permutation_NoDup HPERM (recb_ablocks_nodup_m B lyc Sc Wc memc mdc HARc)).
cbn [app] in HNDc.
apply List.NoDup_cons_iff in HNDc as [Hb0n HNDc].
apply List.NoDup_cons_iff in HNDc as [Hb1n HNDc].
apply List.NoDup_cons_iff in HNDc as [Hwn _].
assert (HNOTW : forall pn, In pn (O1 ++ [b0; b1]) -> pn <> (w, hs_wsz x)).
{ intros pn Hpn E0. subst pn. apply in_app_or in Hpn as [Hpn | Hpn].
  - exact (Hwn (HO1R _ Hpn)).
  - destruct Hpn as [Hq | [Hq | []]].
    + apply Hb0n. rewrite Hq. right. left. reflexivity.
    + apply Hb1n. rewrite Hq. left. reflexivity. }
assert (KEEPR : forall a, hs_in_rec a \/ hs_in_own (O1 ++ [b0; b1]) a -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha.
  assert (Hout : ~ (w <= a < w + hs_wsz x) /\ 0 <= a < alloc_ceiling).
  { destruct Ha as [Hrec | (pn & Hpn & Hr)].
    - assert (Hpg : Exists (in_zr a) recb_PG).
      { unfold hs_in_rec in Hrec. destruct Hrec as [Hg | Hs]; [apply recb_grec_in | apply recb_spill_in]; lia. }
      split; [|unfold hs_in_rec, A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Hrec; lia].
      intros Hw. exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc w (hs_wsz x) a HARc Hwin ltac:(lia) (hPIMG a Hpg)).
    - destruct pn as [q m]. cbn [fst snd] in Hr.
      pose proof (HBLIVE (q, m) Hpn) as Hqm.
      destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc q m HARc Hqm) as (_ & Hq4 & Hqc & _ & _ & _ & Hmr).
      pose proof (req_size_pos m ltac:(lia)) as [_ Hr2].
      pose proof (sep_blocks SEGS B LAWS lyc Sc Wc memc mdc q m w (hs_wsz x) HARc Hqm Hwin (HNOTW (q, m) Hpn)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. split; lia. }
  destruct Hout as [Hnw Ha0].
  rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(cbv beta; unfold astr_len; cbn [length]; lia)).
  apply KEEP1; lia. }
assert (KEEPF : forall a, spZ (i_regs x) - 112 <= a < spZ (i_regs x) -> rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha. rewrite (HK2 a ltac:(lia) ltac:(lia) ltac:(cbv beta; unfold astr_len; cbn [length]; lia)).
  apply KEEP1; lia. }
apply (HL2 lyc Sc Wc mem2 md2 regs2 k O1 Rest b0 b1 w ltac:(lia) HCX).
- unfold hs_mid. cbv zeta.
  split; [exact HJ2|]. split; [exact Hk|]. split; [exact HMLE|]. split; [exact HBB|]. split; [|exact HBA].
  intros j r Hjr.
  assert (Hj : (j < length HS_SAVED)%nat) by (apply (proj1 (nth_error_Some HS_SAVED j)); rewrite Hjr; discriminate).
  unfold HS_SAVED in Hj. cbn [length] in Hj.
  intros kk Hkk. rewrite (KEEPF (spZ (i_regs x) - 8 - 8 * Z.of_nat j + Z.of_nat kk) ltac:(lia)).
  exact (HFRAME j r Hjr kk Hkk).
- exact Hb0.
- exact Hb1.
- apply (hs_rec_kept B lyc Sc lyc Sc (rdW Wc memc) (rdW Wc mem2) _ _ HREP); [exact KEEPR | exact HBLIVE].
- rewrite (hs5_join_one (i_toks x) ltac:(lia)). change (nth 0 (i_toks x) []) with (hs_tok x 0).
  split; [|exact (proj2 GSTR)].
  apply (abytes_atR_view SEGS). rewrite app_nil_l in HQb. exact HQb.
- split; [|split].
  + split; [rewrite (hs5_pres_at _ _ (2%bv : bv 5) 2 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P2; exact R2|].
    split; [rewrite (hs5_pres_at _ _ (3%bv : bv 5) 3 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P3; exact R3|].
    split; [rewrite (hs5_pres_at _ _ (4%bv : bv 5) 4 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P4; exact R4|].
    split; [rewrite (hs5_pres_at _ _ (8%bv : bv 5) 8 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P8; exact R8|].
    split; [rewrite (hs5_pres_at _ _ (9%bv : bv 5) 9 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P9; exact R9|].
    split; [rewrite (hs5_pres_at _ _ (22%bv : bv 5) 22 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P22; exact R22
           |rewrite (hs5_pres_at _ _ (23%bv : bv 5) 23 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P23; exact R23].
  + rewrite (hs5_pres_at _ _ (19%bv : bv 5) 19 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P19. exact H19.
  + rewrite (hs5_pres_at _ _ (24%bv : bv 5) 24 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P24. exact H24.
- rewrite (hs5_pres_at _ _ (20%bv : bv 5) 20 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P20. exact H10.
- exact Hw4096.
- rewrite (hs5_pres_at _ _ (25%bv : bv 5) 25 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P25. reflexivity.
- rewrite (hs5_pres_at _ _ (26%bv : bv 5) 26 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P26. reflexivity.
- rewrite (hs5_pres_at _ _ (18%bv : bv 5) 18 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P18, H18.
  f_equal. lia.
- rewrite (hs5_pres_at _ _ (21%bv : bv 5) 21 HP2 eq_refl ltac:(unfold acallee_saved; lia)), P21, H18.
  f_equal. lia.
Qed.
End e.
End f.
End d.
