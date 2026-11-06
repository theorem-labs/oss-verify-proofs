(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the segment statements of descriptors_panel_get's walk (plugin-hostd/fuzz_command.asan), in the form of proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v / ACh1.v (cl_cx, cl_mid, the CL_*_stmtX statements each segment proves from the next). *)

(* The walk of descriptors_panel_get is cut in three segments, each a statement the earlier one proves from the next
   (cgif's cl_B_okX : CL_RC_stmtX -> CL_B_stmtX):
   - dpg_X_stmt: from the call of xstrdup (0x8d1c0) to the end: xstrdup, the arg_s stores, rec_shape_of, the
     frame's release and the tail jump into answer;
   - dpg_J_stmt: from 0x8d180, where the two arms of the inlined record() meet, to the call of xstrdup;
   - the entry and the two arms (descriptors_panel_get.v).
   Every statement keeps the entry's state (ly S W regs mem md) and promises the contract's post, apost_base of the
   entry with the post's conjuncts verbatim (descriptors_panel_get_c.v:99-118, `dpg_postQ`). uri is a string x
   in a live heap block (the contract's premise at descriptors_panel_get_c.v:86-89). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0s YK15 YP09 YI00 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable CmdSyms CmdList CmdPa CmdBase CmdRep PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdObj CmdRo.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import rec_calls_free_c xstrdup_c rec_shape_of_c answer_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import descriptors_panel_get_c descriptors_panel_get_s1.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* the verb's bytes "panel_get" at 0x21f80 (RO_lit_21f80 without its terminator) *)
Definition dpg_verb : list byte := map (Z_to_bv 8) [112; 97; 110; 101; 108; 95; 103; 101; 116].
Lemma dpg_verb_bstr : dpg_verb = bstr "panel_get".
Proof. vm_compute. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

Definition DPG_STK : Z := DESCRIPTORS_PANEL_GET_STK.
Definition dpg_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* the contract's post (descriptors_panel_get_c.v:99-118), verbatim *)
Definition dpg_postQ (ly : alayout) (S : astate) (R : rstate) (uri : option (list byte)) (O : list (Z * Z))
: alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' => exists (R' : rstate) (t : list byte) (q : Z) (O' : list (Z * Z)),
 descriptors_panel_get_m R uri = (R', t) /\
 getr regs' 10 = w64 q /\ 4096 <= q < 2 ^ 64 /\
 rec_repA B ly' S' (rdW W' mem') R' O' /\
 (forall pn, In pn O' -> In pn O \/ ~ In pn (ablocks B ly S)) /\
 In (q, Z.of_nat (length t) + 1) (ablocks B ly' S') /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O -> pn <> (q, Z.of_nat (length t) + 1)) /\ ~ In q (map fst O') /\
 astr_atR (rdW W' mem') q t /\
 (forall pn, In pn (ablocks B ly S) -> ~ In pn O ->
    In pn (ablocks B ly' S') /\ iv_apart (fst pn) (snd pn) q (Z.of_nat (length t) + 1)) /\
 (forall pn, In pn (ablocks B ly' S') ->
    (In pn (ablocks B ly S) /\ ~ In pn O) \/ In pn O' \/ pn = (q, Z.of_nat (length t) + 1)) /\
 blocks_bytes S' <= blocks_bytes S + LIVE_DESCRIPTORS_PANEL_GET R uri /\
 mo_le MT S S' (XM_DESCRIPTORS_PANEL_GET MT R uri).

Definition dpg_post (ly : alayout) (S : astate) (W : world SEGS) (regs : bvmap 5 word) mem md
(R : rstate) (uri : option (list byte)) (O : list (Z * Z)) : world SEGS -> config -> Prop :=
apost_baseF SEGS B DPG_STK (dpg_FP O) regs ly S W mem md (EV_DESCRIPTORS_PANEL_GET R) (dpg_postQ ly S R uri O).

(* the contract's premises (descriptors_panel_get_c.v:74-94) with uri = Some x *)
Definition dpg_ctx ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch (pu : Z) (x : list byte)
(R : rstate) (O : list (Z * Z)) : Prop :=
afn_pre SEGS B DPG_STK ly S W regs mem md ch /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr fx)) 5) 7 = 0 /\
arodata_okP SEGS RLO RHI B (rdW W mem) /\
cmd_ro_ok (rdW W mem) /\
getr regs 10 = w64 pu /\ 0 <= pu < 2 ^ 64 /\
in_blockA (ablocks B ly S) pu (Z.of_nat (length x) + 1) /\ astr_atR (rdW W mem) pu x /\
Z.of_nat (length x) + 1 <= LMAX + 1 /\
Forall (fun qk => iv_apart pu (Z.of_nat (length x) + 1) (fst qk) (snd qk)) O /\
rec_repA B ly S (rdW W mem) R O /\
Z.of_nat (length (frames S)) <= 8 /\
st_nev S + EV_DESCRIPTORS_PANEL_GET R <= EV_MAX /\
blocks_bytes S + LIVE_DESCRIPTORS_PANEL_GET R (Some x) <= LIVE_MAX /\
mo_ok MT S (XM_DESCRIPTORS_PANEL_GET MT R (Some x)).

(* how the blocks at a point of the walk relate to the entry's: the live ones are entry blocks, and an entry block
   that is gone is one of the recorder's and went on record()'s spill arm; O1 is what the recorder owns now *)
Definition dpg_blk ly S (R : rstate) (O : list (Z * Z)) lyc Sc (O1 : list (Z * Z)) : Prop :=
(forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly S)) /\
(forall pn, In pn (ablocks B ly S) -> ~ In pn (ablocks B lyc Sc) -> In pn O /\ (16 <= length (r_calls R))%nat) /\
(forall pn, In pn O1 -> In pn O) /\
(forall pn, In pn O -> ~ In pn O1 -> ~ In pn (ablocks B lyc Sc)) /\
(exists fr, Permutation (ablocks B ly S) (ablocks B lyc Sc ++ fr)).

(* what is common to every point of the walk with the frame up: the journal from the entry (k events: the spill
   arm's frees), the meter, the registers the rest of the walk reads and the frame's saved registers *)
Definition dpg_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc : Prop :=
ajournal SEGS B DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] lyc Sc Wc memc mdc (rec_spill_frees R) /\
mo_le MT S Sc (rec_spill_frees R * mo_free MT) /\
spZ regs1 = spZ regs - DPG_FRAME /\
getr regs1 3 = w64 (as_gp B) /\ getr regs1 4 = w64 (as_tp B) /\
getr regs1 8 = w64 (dpg_c R) /\ getr regs1 19 = w64 SB /\
(forall r, 21 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
(forall j r, nth_error dpg_saved j = Some r ->
 aval_mem (rdW Wc memc) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))).

(* the segment from the call of xstrdup: the recorder holds the new call (24, []) in the slot, xstrdup is
   handed s, the string x in a live heap block *)
Definition dpg_X_stmt : Prop :=
forall ly S W regs mem md ch pu x R O,
dpg_ctx ly S W regs mem md ch pu x R O ->
forall lyc Sc Wc (regs1 : bvmap 5 word) memc mdc Q1 O1 (s : Z),
dpg_mid ly S W regs mem md R O lyc Sc Wc regs1 memc mdc ->
dpg_blk ly S R O lyc Sc O1 ->
arep_at (ablocks B lyc Sc) (rdW Wc memc) A_G_REC A_REC_SPILL (rec_record R REC_DESCRIPTORS_PANEL_GET []) Q1 ->
(forall pn, In pn O1 <-> In pn (lay_blocks Q1)) ->
getr regs1 1 = Z_to_bv 64 (BASE + DPG_RET_X) ->
getr regs1 10 = w64 s ->
getr regs1 18 = w64 (dpg_c R + 4) -> getr regs1 20 = w64 (SB + (dpg_c R + 4) / 8) ->
in_blockA (ablocks B lyc Sc) s (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memc) s x ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (SIG CS_xstrdup)) memc (seg_rom SEGS)) mdc)
  (dpg_post ly S W regs mem md R (Some x) O).

(* the segment from 0x8d180: s0 is the slot, s1 uri; the record()'s two stores at the slot (fn := 24,
   nargs := 0) make the recorder's state rec_record R 24 [] *)
Definition dpg_J_stmt : Prop :=
forall ly S W regs mem md ch pu x R O,
dpg_ctx ly S W regs mem md ch pu x R O ->
forall lyc Sc Wc (regs1 : bvmap 5 word) memc mdc Q1 O1,
dpg_mid ly S W regs mem md R O lyc Sc Wc regs1 memc mdc ->
dpg_blk ly S R O lyc Sc O1 ->
(forall rd', aval_mem rd' (dpg_c R + CALL_OFF_FN) 4 REC_DESCRIPTORS_PANEL_GET ->
  aval_mem rd' (dpg_c R + CALL_OFF_NARGS) 4 0 ->
  (forall a, ((A_G_REC <= a < A_G_REC + REC_SIZE) \/ (A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) \/
              (exists pn, In pn (lay_blocks Q1) /\ fst pn <= a < fst pn + snd pn)) ->
     ~ (dpg_c R <= a < dpg_c R + 8) -> rd' a = rdW Wc memc a) ->
  arep_at (ablocks B lyc Sc) rd' A_G_REC A_REC_SPILL (rec_record R REC_DESCRIPTORS_PANEL_GET []) Q1) ->
(forall pn, In pn O1 <-> In pn (lay_blocks Q1)) ->
getr regs1 9 = w64 pu ->
in_blockA (ablocks B lyc Sc) pu (Z.of_nat (length x) + 1) -> astr_atR (rdW Wc memc) pu x ->
SRr SEGS Wc (mkCfg (mkst regs1 (Z_to_bv 64 (BASE + DPG_JOIN)) memc (seg_rom SEGS)) mdc)
  (dpg_post ly S W regs mem md R (Some x) O).

(* the segment from the call of rec_shape_of (0x8d204): xstrdup returned the copy p, a fresh block; arg_s stored
   nargs := 1 and args[0] := p, so the recorder holds the call (24, [x]) (O1 and the copy are its blocks); a0 is
   the verb "panel_get" (0x21f80) and a1 its length 9 *)
Definition dpg_R_stmt : Prop :=
forall ly S W regs mem md ch pu x R O,
dpg_ctx ly S W regs mem md ch pu x R O ->
forall lyc Sc O1 ly2 S2 W2 (regs2 : bvmap 5 word) mem2 md2 Q2 (p : Z),
dpg_blk ly S R O lyc Sc O1 ->
ajournal SEGS B DPG_STK (spZ regs) (dpg_FP O) ly S W mem md [] ly2 S2 W2 mem2 md2 (rec_spill_frees R + EV_XSTRDUP) ->
mo_le MT S S2 (rec_spill_frees R * mo_free MT + XM_XSTRDUP MT x) ->
blocks_bytes S2 <= blocks_bytes S + LIVE_XSTRDUP x ->
Permutation (ablocks B ly2 S2) ((p, LIVE_XSTRDUP x) :: ablocks B lyc Sc) ->
Forall (fun qk => iv_apart p (LIVE_XSTRDUP x) (fst qk) (snd qk)) (ablocks B lyc Sc) ->
4096 <= p < 2 ^ 64 ->
arep_at (ablocks B ly2 S2) (rdW W2 mem2) A_G_REC A_REC_SPILL (rec_record R REC_DESCRIPTORS_PANEL_GET [x]) Q2 ->
(forall pn, In pn (lay_blocks Q2) <-> In pn O1 \/ pn = (p, Z.of_nat (length x) + 1)) ->
spZ regs2 = spZ regs - DPG_FRAME ->
getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) ->
getr regs2 1 = Z_to_bv 64 (BASE + DPG_RET_R) ->
getr regs2 8 = w64 (dpg_c R) ->
getr regs2 10 = w64 0x21f80 -> getr regs2 11 = w64 9 ->
(forall r, 21 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall j r, nth_error dpg_saved j = Some r ->
 aval_mem (rdW W2 mem2) (spZ regs - 8 - 8 * Z.of_nat j) 8 (bv_unsigned (getr regs (Z_to_bv 5 r)))) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (SIG CS_rec_shape_of)) mem2 (seg_rom SEGS)) md2)
  (dpg_post ly S W regs mem md R (Some x) O).

End e.
End f.
End d.
