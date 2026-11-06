(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the call of arg_line in plugin-hostd/fuzz_command's sup_broadcast walk (0x8b044),
   in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v: arg_line's statement (a Section hypothesis) through the
   kit's cl_callS_wide, then the walk's last segment (sup_broadcast_s3.v).

   Pass-4/5 re-fit: arg_line keeps the FP state (its post is apost_base), so its call keeps
   the kit's cl_callS_wide with TARG_LINE at the entry's fx; the segment ends at apost_baseF through sb_tail, which
   takes the rounding-mode-0 premise HFRM. Statement pass 5 removed astack_pres from arg_line's pre; the frame chain
   at the call is achain's empty case (s0 = line, a heap pointer below alloc_ceiling). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI16.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaLibG PaLibH PaArt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo CmdAddr.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_canonical_c xstrdup_c hand_back_c rec_calls_free_c arg_line_c answer_c sup_broadcast_c PaNoChain sup_broadcast_s1 sup_broadcast_s2
sup_broadcast_s3.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis VOBJS : cmd_val_objs.
Hypothesis SIGP : cmd_sig_prog.
(* fields of cmd_img_facts (CmdRecBase.v) and lemmas of CmdRecFacts.v, under their final names and forms until
   the kit has them (statement pass 3) *)
Hypothesis cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a.
Hypothesis cif_prog_not_ro : forall a, inFP cmd_PG a -> ~ in_roP SEGS CMD_RLO CMD_RHI a.
Hypothesis cif_relro_img : forall a, CMD_RLO <= a < CMD_RHI -> in_img SEGS a.
Hypothesis cmd_ro_in_img : cmd_ro_in (in_roP SEGS CMD_RLO CMD_RHI).
Hypothesis cmd_ro_ok_of_aro : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md ->
arodata_okP SEGS CMD_RLO CMD_RHI B (rdW W mem) -> cmd_ro_ok (rdW W mem).
Hypothesis TARG_LINE : forall fx0 : YK11.FPState, @targ_line_spec fx0 rc SK PI B MT.
Hypothesis TANSWER : forall fx0 : YK11.FPState, @tanswer_spec fx0 rc SK PI B MT.

Let TAIL := sb_tail B MT HB LAWS MTL VOBJS SIGP cif_prog_img cmd_ro_in_img cmd_ro_ok_of_aro TANSWER.

Lemma sb_sig_argline : SIGMA CS_arg_line = BASE + AF_arg_line.
Proof. rewrite (SIGP CS_arg_line); [reflexivity | cbn [cmd_prog_syms In]; repeat (first [left; reflexivity | right])]. Qed.

(* the read-only view survives a journal whose footprint holds no read-only byte (CmdBase.v's arodata_ok_journalP,
   with the read-only range fixed and the footprint closed to the sink) *)
Lemma sb_arod_journal : forall STK sp0 FP ly S W mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP -> (forall a, inFP FP a -> inFP cmd_PG a) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k HJ Hso HFP HR a Hro Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a); [exact (HR a Hro Ho He) | | exact Ho | exact He |].
- destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (cif_relro_img a Hr)].
- split; [intros Hs; exfalso; exact (Hso Hs)|]. intros Hf. exact (cif_prog_not_ro a (HFP a Hf) Hro).
Qed.

(* the slot's bytes are statics *)
Definition sb_slot (c : Z) : Prop :=
(exists i, 0 <= i < REC_CALLS_MAX /\ c = A_G_REC + OFF_CALLS + CALL_SIZE * i) \/ c = A_REC_SPILL.
Lemma sb_slot_pg : forall c a, sb_slot c -> c <= a < c + 56 -> inFP cmd_PG a.
Proof.
intros c a [(i & Hi & ->) | ->] Ha.
- exists (A_G_REC, A_G_REC + 960). split; [left; reflexivity|]. cbn [fst snd].
  unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX in *. lia.
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [right; left; reflexivity|]. cbn [fst snd]. lia.
Qed.
Lemma sb_slot_fp : forall c a O, sb_slot c -> c <= a < c + 16 -> inFP (sb_FP O) a.
Proof.
intros c a O [(i & Hi & ->) | ->] Ha; unfold sb_FP.
- apply inFP_cons; right. apply inFP_cons; left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, CALL_SIZE, REC_CALLS_MAX in *. lia.
- do 3 (apply inFP_cons; right). apply inFP_cons; left. unfold SC_SIZE. lia.
Qed.
Lemma sb_slot_range : forall c, sb_slot c -> 0x5e3740 + 16 <= c <= 0x5e3be0.
Proof. intros c [(i & Hi & ->) | ->]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, REC_CALLS_MAX, A_REC_SPILL in *; lia. Qed.

(* 0x8b044: the call of arg_line, then the last segment *)
Lemma sb_mid : forall ly S W regs mem md ch pl line R O lyX SX (WX : world SEGS) regsX memX mdX c F Omid,
afn_pre SEGS B SUP_BROADCAST_STK ly S W regs mem md ch ->
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 ->
Z.of_nat (length (frames S)) <= 8 ->
rec_repA B ly S (rdW W mem) R O ->
st_nev S + EV_SUP_BROADCAST R <= EV_MAX ->
blocks_bytes S + LIVE_SUP_BROADCAST line (snd (sup_broadcast_m R line)) <= LIVE_MAX ->
mo_ok MT S (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line))) ->
ajournal SEGS B SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyX SX WX memX mdX (rec_spill_frees R) ->
spZ regsX = spZ regs - 32 -> getr regsX 1 = Z_to_bv 64 (BASE + SB_RET_AL) ->
getr regsX 8 = w64 pl -> getr regsX 9 = w64 c -> getr regsX 10 = w64 c -> getr regsX 11 = w64 pl ->
(forall r, acallee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> getr regsX (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
aval_mem (rdW WX memX) (spZ regs - 8) 8 (raZ regs) -> aval_mem (rdW WX memX) (spZ regs - 16) 8 (s0Z regs) ->
aval_mem (rdW WX memX) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
aval_mem (rdW WX memX) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
arodata_okP SEGS RLO RHI B (rdW WX memX) ->
sb_slot c -> aval_mem (rdW WX memX) (c + CALL_OFF_NARGS) 4 0 ->
(forall bl' (rd' : reader) p k s,
 (forall a, inFP cmd_PG a -> ~ (c + 4 <= a < c + 16) -> rd' a = rdW WX memX a) ->
 (forall pn, In pn Omid -> forall j, 0 <= j < snd pn -> rd' (fst pn + j) = rdW WX memX (fst pn + j)) ->
 (forall pn, In pn Omid -> In pn bl') ->
 aval_mem rd' (c + CALL_OFF_NARGS) 4 1 -> aval_mem rd' (c + CALL_OFF_ARGS) 8 p ->
 In (p, k) bl' -> 4096 <= p -> Z.of_nat (length s) + 1 <= k <= LMAX + 2 -> Z.of_nat (length s) <= LMAX ->
 astr_atR rd' p s -> (forall pn, In pn Omid -> iv_apart p k (fst pn) (snd pn)) ->
 iv_apart p k A_G_REC REC_SIZE -> iv_apart p k A_REC_SPILL SC_SIZE ->
 rec_repL bl' rd' (rec_record R REC_BROADCAST [s]) (Omid ++ [(p, k)])) ->
((exists kk, nth_error (r_calls (rec_record R REC_BROADCAST [canon line])) kk = Some (REC_BROADCAST, [canon line]) /\
  c = A_G_REC + OFF_CALLS + CALL_SIZE * Z.of_nat kk) \/
 (c = A_REC_SPILL /\ (REC_BROADCAST, [canon line]) = r_spill (rec_record R REC_BROADCAST [canon line]))) ->
astr_atR (rdW WX memX) pl line -> Z.of_nat (length line) + 1 <= LMAX + 1 ->
in_blockA (ablocks B lyX SX) pl (Z.of_nat (length line) + 1) ->
Permutation (ablocks B ly S) (ablocks B lyX SX ++ F) -> (forall pn, In pn F -> In pn O) ->
(forall pn, In pn Omid -> In pn O) -> (forall pn, In pn O -> In pn Omid \/ In pn F) ->
(forall pn, In pn Omid -> In pn (ablocks B lyX SX)) ->
mo_le MT S SX (rec_spill_frees R * mo_free MT) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (SIGMA CS_arg_line)) memX (seg_rom SEGS)) mdX)
(apost_baseF SEGS B SUP_BROADCAST_STK (sb_FP O) regs ly S W mem md (EV_SUP_BROADCAST R)
 (sb_post B MT ly S R line O)).
Proof.
intros ly S W regs mem md ch pl line R O lyX SX WX regsX memX mdX c F Omid
HPRE HFRM Hfr8 HREC Hev Hlive HMOK HJ Hsp H1 H8 H9 H10 H11 Hcs Vra Vs0 Vs1 Vs2 HROD Hsl Hn0 HREC1 HCE
HSTR HLEN HBLK HP0 HF0 HOm1 HOm2 HOmX HMLE.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HJ as (HARX & _).
pose proof (sb_slot_range c Hsl) as Hcr.
assert (WSTK : SUP_BROADCAST_STK = 16592) by reflexivity.
assert (WAL : ARG_LINE_STK = 16464) by reflexivity.
assert (HOb : forall pn, In pn O -> In pn (ablocks B ly S)) by (intros pn Hpn; exact (proj2 (sb_rep_pos _ _ _ _ pn HREC Hpn))).
destruct HBLK as (pb & kb & Hinb & Hpb & Hpbe).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb kb HARX Hinb) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hkb).
assert (Hpl : 4096 <= pl < alloc_ceiling) by (pose proof (req_size_pos kb ltac:(lia)); lia).
assert (HbbX : blocks_bytes SX <= blocks_bytes S).
{ rewrite (blocks_bytes_bsum B lyX SX), (blocks_bytes_bsum B ly S), (bsum_perm _ _ HP0), bsum_app.
  assert (0 <= bsum F); [|lia]. apply sb_bsum_nonneg. intros [b m] Hb.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR (HOb _ (HF0 _ Hb))) as (_ & _ & _ & _ & _ & _ & Hm). cbn [snd]. lia. }
assert (HXA : 0 <= XM_ANSWER MT (snd (sup_broadcast_m R line))).
{ unfold XM_ANSWER, XM_HAND_BACK, XM_XSTRDUP. pose proof (mo_free_nonneg MT MTL).
  pose proof (mo_malloc_nonneg MT MTL (Z.of_nat (length (snd (sup_broadcast_m R line))) + 1) ltac:(lia)). lia. }
assert (HMOKX : mo_ok MT SX (XM_ARG_LINE MT line)).
{ apply (mo_ok_step MT MTL S SX (rec_spill_frees R * mo_free MT) (XM_ARG_LINE MT line)); [|exact HMLE].
  apply (mo_ok_le MT MTL S _ (XM_SUP_BROADCAST MT R line (snd (sup_broadcast_m R line)))); [exact HMOK|].
  unfold XM_SUP_BROADCAST. lia. }
assert (HFP1 : forall a, inFP [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)] a ->
  c + 4 <= a < c + 16).
{ intros a Ha. apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_NARGS in Ha; lia|].
  apply inFP_cons in Ha as [Ha | Ha]; [unfold CALL_OFF_ARGS in Ha; lia | exfalso; exact (inFP_nil a Ha)]. }
eapply SRr_bind.
{ eapply (cl_callS_wide B LAWS WX regsX memX (Z_to_bv 64 (SIGMA CS_arg_line))
    SUP_BROADCAST_STK (spZ regs) (sb_FP O) ly S W mem md [] lyX SX mdX (rec_spill_frees R)
    ARG_LINE_STK [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]
    EV_ARG_LINE (-32) (Z_to_bv 64 (BASE + SB_RET_AL)) [] _ HJ).
  - lia.
  - reflexivity.
  - lia.
  - rewrite WAL. lia.
  - rewrite WAL, WSTK. lia.
  - etransitivity; [exact (Hcs 3 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Hgp].
  - etransitivity; [exact (Hcs 4 ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) | exact Htp].
  - exact H1.
  - apply ret_ok_codeptr_v; [unfold SB_RET_AL, AF_sup_broadcast; lia | reflexivity].
  - unfold SB_RET_AL, AF_sup_broadcast. rewrite unsigned_lit_small by lia. lia.
  - apply achain_low. unfold s0Z. rewrite H8. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - intros HPRE2. rewrite sb_sig_argline.
    eapply SRr_mono.
    { apply (TARG_LINE fx lyX SX WX regsX memX mdX [] c pl 0 line HPRE2).
      - exact HROD.
      - exact H10.
      - exact H11.
      - lia.
      - exact Hsl.
      - exact Hn0.
      - unfold REC_ARGS_MAX. lia.
      - exists pb, kb. split; [exact Hinb | lia].
      - exact HSTR.
      - exact HLEN.
      - pose proof HJ as (_ & _ & _ & _ & _ & _ & HnevX & _). unfold EV_SUP_BROADCAST, EV_ANSWER, EV_HAND_BACK, EV_XSTRDUP in Hev. lia.
      - unfold LIVE_SUP_BROADCAST, LIVE_ANSWER, LIVE_HAND_BACK, LIVE_XSTRDUP in Hlive. lia.
      - exact HMOKX. }
    cbv beta. unfold apost_base. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2).
    exists ly2, S2, regs2, mem2, md2. split; [rewrite H1; reflexivity|]. split; [exact HJ2|]. split; [exact HP2 | exact HK2].
  - intros a Ha. pose proof (HFP1 a Ha) as Ha'. unfold awr_byte, awr_prog_or_caller. do 4 right. left.
    split; [exact (sb_slot_fp c a O Hsl ltac:(lia))|].
    split; [apply (HPROG B HB); exact (sb_slot_pg c a Hsl ltac:(lia)) | apply cif_prog_img; exact (sb_slot_pg c a Hsl ltac:(lia))].
  - intros ly2 S2 W2 regs2 mem2 md2 _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha). lia. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & HK2).
destruct HK2 as (Hbb2 & Hmle2 & [(Hm6 & _) | (_ & p & HK2)]); [unfold REC_ARGS_MAX in Hm6; lia|].
cbv zeta in HK2. destruct HK2 as (Hp4096 & HPm & HAp & Hn1 & Ha0 & Hcan).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
set (k := Z.of_nat (length line) + 1) in *.
assert (Hso1 : ~ YI16.sink_open_fp [(c + CALL_OFF_NARGS, c + CALL_OFF_NARGS + 4); (c + CALL_OFF_ARGS + 8 * 0, c + CALL_OFF_ARGS + 8 * 0 + 8)]).
{ apply sink_closed_pos. repeat constructor; cbn [fst]; unfold CALL_OFF_NARGS, CALL_OFF_ARGS; lia. }
assert (KS : forall a, spZ regs - 32 <= a < spZ regs -> rdW W2 mem2 a = rdW WX memX a).
{ intros a Ha. apply G1; [lia | rewrite WAL; lia | intros Hf; pose proof (HFP1 a Hf); lia]. }
assert (Hin2 : In (p, k) (ablocks B ly2 S2)) by (apply (Permutation_in _ (Permutation_sym HPm)); left; reflexivity).
assert (HoffP : off_img p (req_size k)) by exact (blk_off_imgP B ly2 S2 W2 mem2 md2 p k HAR2 Hin2).
pose proof (req_size_pos k ltac:(lia)) as [_ Hreqk].
pose proof (canon_length line) as Hcanl.
apply (TAIL ly S W regs mem md ch line R O ly2 S2 W2 regs2 mem2 md2 c F (ablocks B lyX SX) Omid p k).
- exact HPRE.
- exact HFRM.
- exact Hfr8.
- exact HREC.
- exact Hev.
- exact Hlive.
- exact HMOK.
- exact HJ2.
- assert (E2 : getr regs2 2 = getr regsX 2) by exact (HP2 2 ltac:(unfold acallee_saved; lia)).
  unfold spZ in *. rewrite E2. exact Hsp.
- etransitivity; [exact (HP2 9 ltac:(unfold acallee_saved; lia)) | exact H9].
- lia.
- intros r Hr H2' H8' H9' H18'. rewrite (HP2 r Hr). exact (Hcs r Hr H2' H8' H9' H18').
- intros kk Hkk. rewrite KS by lia. exact (Vra kk Hkk).
- intros kk Hkk. rewrite KS by lia. exact (Vs0 kk Hkk).
- intros kk Hkk. rewrite KS by lia. exact (Vs1 kk Hkk).
- intros kk Hkk. rewrite KS by lia. exact (Vs2 kk Hkk).
- exact (sb_arod_journal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hso1 (fun a Ha => sb_slot_pg c a Hsl ltac:(pose proof (HFP1 a Ha); lia)) HROD).
- apply (HREC1 (ablocks B ly2 S2) (rdW W2 mem2) p k (canon line)).
  + intros a Hpg Hna. apply G3.
    * exact (cif_prog_img a Hpg).
    * exact (proj1 (sb_pg_unowned B HB a Hpg)).
    * exact (proj2 (sb_pg_unowned B HB a Hpg)).
    * split; [intros Hs; exfalso; exact (Hso1 Hs)|]. intros Hf. exact (Hna (HFP1 a Hf)).
  + intros [b m] Hpn j Hj. cbn [fst snd] in *.
    pose proof (HOmX _ Hpn) as HbX.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HARX HbX) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m ltac:(lia)) as [_ Hreqm].
    apply (G2 b m j); [exact HbX | apply (Permutation_in _ (Permutation_sym HPm)); right; exact HbX | lia |].
    intros Hf. apply (blk_img SEGS B LAWS lyX SX WX memX mdX b m (b + j) HARX HbX ltac:(lia)).
    apply cif_prog_img. apply (sb_slot_pg c _ Hsl). pose proof (HFP1 _ Hf). lia.
  + intros pn Hpn. apply (Permutation_in _ (Permutation_sym HPm)). right. exact (HOmX _ Hpn).
  + exact Hn1.
  + replace (c + CALL_OFF_ARGS) with (c + CALL_OFF_ARGS + 8 * 0) by lia. exact Ha0.
  + exact Hin2.
  + lia.
  + unfold k. unfold LMAX in *. lia.
  + unfold LMAX in *. lia.
  + exact Hcan.
  + intros pn Hpn. exact (proj1 (Forall_forall _ _) HAp pn (HOmX _ Hpn)).
  + unfold iv_apart, off_img, A_G_REC, REC_SIZE in *. lia.
  + unfold iv_apart, off_img, A_REC_SPILL, SC_SIZE in *. lia.
- exact HCE.
- exact HP0.
- exact HF0.
- exact HOm1.
- exact HOm2.
- exact HPm.
- exact HAp.
- reflexivity.
- unfold XM_SUP_BROADCAST. exact (mle_station MT S SX S2 _ _ MTL HMLE Hmle2).
Qed.

End e.
End f.
End d.
