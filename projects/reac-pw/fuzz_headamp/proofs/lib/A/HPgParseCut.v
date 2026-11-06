(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKit.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A), the block pcs, the code table's range (1573 words: headamp's out-of-line slow blocks are four instructions long), module paths; kept_run from proofs/reac-pw/fuzz_role/lib/A/RPgCfgChanges.v at a529a88a618 (role's cfg functions have no twin in headamp; same_io_wvb is HPgSteps'). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropKit.v, with its module paths and module names changed; 118 of its 150 lines of code are new or changed and 97 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the code table, the ok-statements and the segment statements in the form of
   proofs/reac-pw/fuzz_role/lib/A/RPgParseBase.v at afaa3cb55c1 (parse_tbl, H_ok .. T_ok, segE1_stmt .. segT_stmt),
   with the cuts of headamp's plain walk (proofs/reac-pw/fuzz_headamp/lib/Prog/Seg/ParseCut.v at 3e9fc5c8969: S_EPI,
   S_EXIT, S_WALK, K_ADV, S_KEY, S_VALUE) at image A's pcs and registers. *)
(* reac_headamp_prop_parse_result 0x845b4 (2416 bytes, 604 instructions, all 4 bytes) of reac-pw/fuzz_headamp's ASan
   image A (fuzz_headamp.asan, pinned sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47;
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the cut
   states of its walk against lib/A/HPgCSpec.v's hd_parse_result_specX. Statement text only. Proves no function
   (kind: statement text). The image-independent parts are lib/A/HPgParseBase.v's.

   THE CUTS (pcs read from the code, capstone over the pinned file):
     E     0x845b4 entry        -> EPI (NULL: rc -1; the header tests: -1 or 0) | FIND (r = 16)
     FIND  0x847c4 find loop    -> EPI (rc 0) | FIND (next property) | WALK (the params Struct's first child) | EXIT
     WALK  0x84910 pair loop    -> EXIT (no child left) | ADV (no key yet, or strncmp says no prefix) | KEY
     KEY   0x849e4 prefix ok    -> ADV (a refusal) | VAL
     VAL   0x84b30 value        -> ADV (a refusal, or the cell written) | EXIT (n >= cap)
     ADV   0x84b00 advance      -> WALK (the next child) | EXIT
     EXIT  0x84890 walk's end   -> EPI (res written when res <> 0)
     EPI   0x84738 epilogue     -> ret 0x847a8 (the hole closed, the saves reloaded)
   Every cut but E carries HPgParseBase.hp_core with the pattern PAT_KEY (f1 f1 f1 f1 f8 f3 f3 f3): the hole is
   opened at 0x84648 .. 0x84668 inside E, its byte 4 is 00 only inside KEY (0x849f8, before the strtol call, back to
   f8 at 0x84aec on KEY's refusal paths and at 0x84b2c before VAL), and it is closed inside EPI (0x84744 .. 0x84760).

   THE REGISTERS AND FRAME CELLS (spa = (sp0 - 0x100) & -32, sp0 the entry sp):
   - every cut (hp_core): sp = spa, s0 = sp0, gp, tp, s1 = res, s2 = cap, s3 = out, s10 = the hole's first byte,
     s11 = SHADOW_OFF; the saves at sp0 - 8 .. sp0 - 112;
   - FIND 0x847c4 (0x847ac .. 0x847c0): a0 = P + 8, a1 = P + r, a2 = SZ - 16, a3 = P + SZ - 8, a4 = 0x80001
     (POD_PROP_PARAMS), s4 = 0;
   - the pair loop (WALK, ADV, KEY, VAL; set at 0x848e0 .. 0x8490c): s4 = n (cells written), s5 = the shadow address
     of s6, s6 = P + r + 8 (the Struct pod), s7 = P + cc (the child), a4 = P + r + 16 (the body), a5 = 8,
     [spa + 16] = ((P + r + 8) mod 8) + 3 (the slow arm's bound for s6's checks), [spa + 32] = P + r + 16,
     [spa + 40] = keys; WALK and ADV: s8 = the key slot (0 or the key text P + ck + 8), s9 = rf; ADV also
     a6 = the shadow address of s7; KEY: s8 = the key text, s9 = rf, [spa + 48] = the shadow address of s7
     (0x849b4); VAL: s8 = ch, a3 = p, a6 = the shadow address of s7, [spa + 8] = the value bound (2, or 0x38 for
     sens: 0x84a54 / 0x84aa4), [spa + 24] = rf (0x849e4), [spa + 40] = keys + 1 (0x849f0), [spa + 48];
   - EXIT 0x84890: s4 = n, s9 = rf, [spa + 40] = keys;
   - EPI 0x84738: s4 = the answer's rc. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Accessors Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgHole HPgParseBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= the image ======================================= *)
(* A_PARSE_RESULT 0x845b4, the trampolines A_TRAMP_STRNCMP 0x41ba4, A_TRAMP_STRTOL 0x41c28, A_TRAMP_STRCMP 0x41ba0
   and the call pcs are lib/A/HPgHole.v's. *)
Definition N_PARSE : nat := 604.
Definition PA_WRAP : Z := 0x845ac.            (* reac_headamp_prop_parse: `mv a3,zero; j 0x845b4` *)
Definition PC_EPI : Z := 0x84738.
Definition PC_FIND : Z := 0x847c4.
Definition PC_EXIT : Z := 0x84890.
Definition PC_WALK : Z := 0x84910.
Definition PC_KEY : Z := 0x849e4.
Definition PC_ADV : Z := 0x84b00.
Definition PC_VAL : Z := 0x84b30.
(* the .got word that holds the shadow-offset cell's address, and the cell (0x8461c, 0x8462c) *)
Definition PA_GOT_SH : Z := 0x9c370.
Definition PA_SH_CELL : Z := 0xa4db8.

Definition pa_tbl : ctable := Eval vm_compute in (build_table rsegs A_PARSE_RESULT N_PARSE TEmpty).
Lemma pa_tbl_eq : pa_tbl = build_table rsegs A_PARSE_RESULT N_PARSE TEmpty.
Proof. vm_cast_no_check (eq_refl pa_tbl). Qed.
Lemma pa_tbl_ok : table_ok rsegs pa_tbl.
Proof. rewrite pa_tbl_eq. apply build_table_ok0. unfold A_PARSE_RESULT. lia. Qed.
Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma pa_segs_low : forall a, in_img rsegs a -> 0 <= a < kLowMemEnd.
Proof.
intros a (sg & Hin & Hr).
assert (HB : forallb (fun s : Segment => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? kLowMemEnd) rsegs = true)
by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) HB sg Hin) as H. apply Z.leb_le in H. lia.
Qed.

Local Notation pctx := (@hp_ctx rsegs).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the call's premises and post at image A's literals: "reac.headamp." 0x21460, "phantom" 0x21480, "pad" 0x214a0,
   "sens" 0x214c0, the stack-guard cells 0x9cff8 / 0x5f7d90, the doubles 0.5 at 0x10378 and 256.0 at 0x10340 *)
Definition call_ok (x : pctx) : Prop :=
hp_call_ok B (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A) x.
Definition PPOST (x : pctx) : world rsegs -> config -> Prop := hp_post B MT x.

(* ---------------------------------- image A's registers and frame cells ---------------------------------- *)
(* the pair loop's registers (s4, s5, s6, a4, a5) and frame cells ([spa + 16], [spa + 32], [spa + 40] = kv) *)
Definition pa_loop (x : pctx) (r : Z) (cl : list Headamp.cell) (kv : Z) (regs : bvmap 5 word)
  (mem : word -> option byte) : Prop :=
getr regs 20 = w64 (Z.of_nat (length cl)) /\ getr regs 21 = w64 (shadow_addr (hx_P x + r + 8)) /\
getr regs 22 = w64 (hx_P x + r + 8) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 16) 8 ((hx_P x + r + 8) mod 8 + 3) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 32) 8 (hx_P x + r + 16) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 40) 8 kv.
Definition pa_a45 (x : pctx) (r : Z) (regs : bvmap 5 word) : Prop :=
getr regs 14 = w64 (hx_P x + r + 16) /\ getr regs 15 = w64 8.

(* ---------------------------------- the cuts ---------------------------------- *)
(* EPI 0x84738: s4 = the answer's rc; out holds its cells and res (when res <> 0) its three words *)
Definition EPI_at (x : pctx) (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : Prop :=
hp_core B x PAT_KEY (ans_cells (hx_ans x)) (ans_res_bytes (hx_ans x)) regs mem md /\ hp_fx F fc /\
getr regs 20 = w64 (ans_rc (hx_ans x)).

(* EXIT 0x84890: the folded state (cl, keys, rf); res still zero *)
Definition EXIT_at (x : pctx) (cl : list Headamp.cell) (keys rf : Z) (F : bvmap 5 word) (fc : bv 32)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fx F fc /\ hp_m_exit x cl keys rf /\
getr regs 20 = w64 (Z.of_nat (length cl)) /\ getr regs 25 = w64 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 40) 8 keys.

(* FIND 0x847c4: the find loop at the property offset r, fuel n *)
Definition FIND_at (x : pctx) (r : Z) (n : nat) (F : bvmap 5 word) (fc : bv 32)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY [] (ha_res_bytes 0 0 0) regs mem md /\ hp_fx F fc /\ hp_m_find x r n /\
getr regs 10 = w64 (hx_P x + 8) /\ getr regs 11 = w64 (hx_P x + r) /\ getr regs 12 = w64 (hx_SZ x - 16) /\
getr regs 13 = w64 (hx_P x + hx_SZ x - 8) /\ getr regs 14 = w64 Model.POD_PROP_PARAMS /\ getr regs 20 = w64 0.

(* WALK 0x84910: the pair loop's head at the child cc, fuel n, key slot ko, state (cl, keys, rf) *)
Definition WALK_at (x : pctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_walk x r cc n ko cl keys rf /\
pa_loop x r cl keys regs mem /\ pa_a45 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hp_keyv x ko) /\ getr regs 25 = w64 rf.

(* ADV 0x84b00: the advance from the child cc, fuel n at the next child, the new key slot ko *)
Definition ADV_at (x : pctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_adv x r cc n ko cl keys rf /\
pa_loop x r cl keys regs mem /\ pa_a45 x r regs /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hp_keyv x ko) /\ getr regs 25 = w64 rf /\
getr regs 16 = w64 (shadow_addr (hx_P x + cc)).

(* KEY 0x849e4: strncmp returned 0 for the key at ck; its value is the child cc *)
Definition KEY_at (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_key x r cc n ck cl keys rf /\
pa_loop x r cl keys regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 (hx_P x + ck + 8) /\ getr regs 25 = w64 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

(* VAL 0x84b30: the key read as (ch, p), keys counted; its value is the child cc *)
Definition VAL_at (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z)
  (F : bvmap 5 word) (fc : bv 32) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
hp_core B x PAT_KEY cl (ha_res_bytes 0 0 0) regs mem md /\ hp_fxw F fc /\ hp_m_val x r cc n ch p cl keys rf /\
pa_loop x r cl (keys + 1) regs mem /\
getr regs 23 = w64 (hx_P x + cc) /\ getr regs 24 = w64 ch /\ getr regs 13 = w64 p /\
getr regs 16 = w64 (shadow_addr (hx_P x + cc)) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 8) 8 (if p =? Headamp.HA_SENS then 0x38 else 2) /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 24) 8 rf /\
val_mem rsegs (hx_rd x mem) (hx_spa x + 48) 8 (shadow_addr (hx_P x + cc)).

(* ---------------------------------- what reaching a cut means ---------------------------------- *)
Definition EPI_ok (x : pctx) : Prop := forall F fc regs mem md,
EPI_at x F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_EPI regs mem md) (PPOST x).
Definition EXIT_ok (x : pctx) : Prop := forall cl keys rf F fc regs mem md,
EXIT_at x cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_EXIT regs mem md) (PPOST x).
Definition FIND_ok (x : pctx) (r : Z) (n : nat) : Prop := forall F fc regs mem md,
FIND_at x r n F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_FIND regs mem md) (PPOST x).
Definition WALK_ok (x : pctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md,
WALK_at x r cc n ko cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_WALK regs mem md) (PPOST x).
Definition ADV_ok (x : pctx) (r cc : Z) (n : nat) (ko : option Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md,
ADV_at x r cc n ko cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_ADV regs mem md) (PPOST x).
Definition KEY_ok (x : pctx) (r cc : Z) (n : nat) (ck : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md,
KEY_at x r cc n ck cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_KEY regs mem md) (PPOST x).
Definition VAL_ok (x : pctx) (r cc : Z) (n : nat) (ch p : Z) (cl : list Headamp.cell) (keys rf : Z) : Prop :=
forall F fc regs mem md,
VAL_at x r cc n ch p cl keys rf F fc regs mem md ->
SRr rsegs (hx_W x) (cfg_at (fx := mkFP F fc) rsegs PC_VAL regs mem md) (PPOST x).

(* ---------------------------------- the segment statements ---------------------------------- *)
(* Each walk file proves one of these under the Section hypotheses it needs of these: MTL : ameter_laws MT;
   HBgot : as_got_shadow B = PA_GOT_SH; HBcell : as_shadow_cell B = PA_SH_CELL; errno_low : api_env rsegs B;
   HBerrno : as_errno B = 0x5d7cac (image A's errno cell, lib/A/AF0m.v TFIB_ERRNO, the record's field
   ts_errno; it puts the errno cell, which is in the parse's write set, apart from every image byte a later pass reads:
   the stack-guard GOT word 0x9cff8, the literals 0x21460 .. 0x214c0, the doubles; segments WALK, KEY, VAL); and,
   for every float state, the wrapper contracts in hole form at image A's trampolines (HPgHole.v):
   STRNCMP : forall F fc, hd_astrncmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRNCMP (segment WALK),
   STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRTOL (hi_gotw headamp_himg_A)
     (hi_guard headamp_himg_A) (segment KEY),
   STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRCMP (segment KEY).
   lib/A/HPgParse.v composes them. *)
Definition segE_stmt : Prop := forall x, call_ok x -> EPI_ok x -> (forall r n, FIND_ok x r n) ->
SRr rsegs (hx_W x) (cfg_at rsegs A_PARSE_RESULT (hx_regs x) (hx_memc x) (hx_mdc x)) (PPOST x).
Definition segEPI_stmt : Prop := forall x, call_ok x -> EPI_ok x.
Definition segEXIT_stmt : Prop := forall x, call_ok x -> EPI_ok x -> EXIT_ok x.
Definition segFIND_stmt : Prop := forall x r n, call_ok x ->
(forall r', FIND_ok x r' n) -> EPI_ok x -> EXIT_ok x ->
(forall r' cc n' ko cl keys rf, WALK_ok x r' cc n' ko cl keys rf) -> FIND_ok x r (S n).
Definition segWALK_stmt : Prop := forall x r cc n ko cl keys rf, call_ok x ->
(forall ko', ADV_ok x r cc n ko' cl keys rf) -> (forall ck, ko = Some ck -> KEY_ok x r cc n ck cl keys rf) ->
EXIT_ok x -> WALK_ok x r cc (S n) ko cl keys rf.
Definition segADV_stmt : Prop := forall x r cc n ko cl keys rf, call_ok x ->
(forall cc', WALK_ok x r cc' n ko cl keys rf) -> EXIT_ok x -> ADV_ok x r cc n ko cl keys rf.
Definition segKEY_stmt : Prop := forall x r cc n ck cl keys rf, call_ok x ->
(forall rf', ADV_ok x r cc n None cl (keys + 1) rf') -> (forall ch p, VAL_ok x r cc n ch p cl keys rf) ->
KEY_ok x r cc n ck cl keys rf.
Definition segVAL_stmt : Prop := forall x r cc n ch p cl keys rf, call_ok x ->
(forall cl' rf', ADV_ok x r cc n None cl' (keys + 1) rf') -> EXIT_ok x -> VAL_ok x r cc n ch p cl keys rf.

End b.
