(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0s YK15 YM06 YP09.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0d YO03
YO0p YO0j YO0m YO0l YO0n YO0k YO0o.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 YI06 UI5b YI09 YI08 YI00.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 UI5c UI21.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0t YI0r UI3p YI0u UI2z.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UI3t UI3u UI4l UI2m UI22 YI5a.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO08.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition rawnew_room (b : rbound) : Prop := room b RAW_SIZE.
Definition rawnew_rb (b : rbound) : rbound := rb_malloc b RAW_SIZE.
Section d.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition lzw_specX : Prop :=
forall STK sp0 FP L A mem md Lc Ac memc mdc (regs : bvmap 5 word) (pR nP img idl icl bi Li : Z) (PIX : list Z) (bq : rbound),
journal ubs0_msyms MR STK sp0 FP L A mem md Lc Ac memc mdc -> st_init_done Ac = true ->
YK0s.ret_ok (getr regs 1) -> getr regs 4 = Z_to_bv 64 (ms_tp ubs0_msyms) ->
getr regs 10 = Z_to_bv 64 pR -> getr regs 11 = Z_to_bv 64 nP -> getr regs 12 = Z_to_bv 64 img ->
getr regs 13 = Z_to_bv 64 idl -> getr regs 14 = Z_to_bv 64 icl ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - LZW_STK ->
spZ regs <= pR -> pR + 16 <= sp0 -> pR mod 8 = 0 ->
1 <= nP <= 100000000 -> 2 <= idl <= 256 -> 0 <= icl <= 12 ->
In (bi, Li) (blocks Lc Ac) -> bi <= img -> img + nP <= bi + Li ->
lzw_rodata_ok memc ->
garr8 ubs0segs memc img PIX -> length PIX = Z.to_nat nP ->
res_ok Ac bq -> lzw_room bq nP ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_LZW_GenerateStream) memc (seg_rom ubs0segs)) mdc)
(fun c' => exists L2 A2 regs2 mem2 md2 (res : Z),
c' = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom ubs0segs)) md2 /\
journal ubs0_msyms MR STK sp0 FP L A mem md L2 A2 mem2 md2 /\
st_init_done A2 = true /\ regs_preserved regs regs2 /\
getr regs2 10 = Z_to_bv 64 res /\
(forall a, alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - LZW_STK <= a < spZ regs) -> ~ (pR <= a < pR + 12) ->
mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\
(forall b m i, In (b, m) (blocks Lc Ac) -> 0 <= i < m ->
mbyte ubs0segs mem2 (b + i) = mbyte ubs0segs memc (b + i)) /\
((res = 0 /\
exists bb Lbb M,
Permutation (blocks L2 A2) ((bb, Lbb) :: blocks Lc Ac) /\
(forall blc i, In (bb, Lbb) blc -> 0 <= i < Lbb -> wr_byte STK sp0 FP (blocks L A) blc (bb + i)) /\
word_mem ubs0segs mem2 pR bb /\ val_mem ubs0segs mem2 (pR + 8) 4 M /\ 1 <= M <= Lbb /\ M <= 2 * nP + 16 /\ lzw_vok idl icl PIX mem2 bb M /\
res_ok A2 (lzw_rb bq (prN Lbb)))
\/ (res = 5 /\
Permutation (blocks L2 A2) (blocks Lc Ac) /\
(forall a, pR <= a < pR + 12 -> mbyte ubs0segs mem2 a = mbyte ubs0segs memc a) /\ lzw_vnone idl icl PIX /\
res_ok A2 (lzw_rb bq 0)))).
Definition rawadd_specX : Prop :=
forall L A (regs : bvmap 5 word) mem md
(raw g cfp : Z) (gvals : list Z) (gct rattr W H sgct loops rcur : Z)
(lct img fattr w h top left delay slct disp tidx : Z) (Nimg : Z) (rest : list (Z * Z)) (f : Z) (S IMG LCT : list Z) (b : rbound),
fn_pre ubs0_msyms MR RAWADD_STK L A regs mem md -> st_init_done A = true ->
In (f, FILE_BLOCK) rest -> sink_at ubs0_msyms mem md f S -> Z.of_nat (length S) + (2 * (w * h) + 2048) <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 raw -> getr regs 11 = Z_to_bv 64 cfp ->
cfp mod 8 = 0 -> spZ regs <= cfp -> cfp + 40 <= 2 ^ 63 ->
obj_at ubs0segs mem cfp LAY_RawFrameConfig [lct; img; fattr; w; h; top; left; delay; slct; disp; tidx] ->
obj_at ubs0segs mem raw LAY_Raw [ubs0_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur] ->
sgct <= 256 ->
obj_at ubs0segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
1 <= w -> 1 <= h -> w * h <= 100000000 ->
w * h <= Nimg ->
Permutation (blocks L A) ((raw, RAW_SIZE) :: (g, CGIF_SIZE) :: (img, Nimg) :: rest) ->
(0 < slct <= 256 -> exists Nl, In (lct, Nl) rest /\ 3 * slct <= Nl /\ (lct, Nl) <> (f, FILE_BLOCK) /\
garr8 ubs0segs mem lct LCT /\ 3 * slct <= Z.of_nat (length LCT)) ->
garr8 ubs0segs mem img IMG -> Z.of_nat (length IMG) = w * h ->
res_ok A b -> rawadd_room b (w * h) ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_addframe) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWADD_STK (spZ regs) ((raw + 40, raw + 44) :: sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem' raw LAY_Raw [ubs0_A_cgif_writecb; g; gct; rattr; W; H; sgct; loops; rcur'] /\
Permutation (blocks L' A') (blocks L A) /\
(exists code bytes, YO07.raw_addframe (YO07.flag rattr 1) sgct (rc_int rcur) IMG fattr w h top left delay slct LCT disp tidx = (code, bytes) /\
Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32 /\ sink_at ubs0_msyms mem' md' f (S ++ bytes) /\
Z.of_nat (length bytes) <= 2 * (w * h) + 2048) /\
res_ok A' (rawadd_rb b)).
Definition rawnew_specX : Prop :=
forall L A regs mem md (cfgp g pgct rattr W H sgct loops : Z) gvals (f pga Npg : Z) (S GCT : list Z) (b : rbound),
fn_pre ubs0_msyms MR RAWNEW_STK L A regs mem md -> st_init_done A = true ->
getr regs 10 = Z_to_bv 64 cfgp -> cfgp mod 8 = 0 -> spZ regs <= cfgp -> cfgp + 40 <= 2 ^ 63 ->
obj_at ubs0segs mem cfgp LAY_RawConfig [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops] ->
(forall i, 0 <= i < 40 -> exists b8, mbyte ubs0segs mem (cfgp + i) = Some b8) ->
obj_at ubs0segs mem g LAY_CGIF gvals ->
nth_error gvals CG_wfn = Some 0 -> nth_error gvals CG_file = Some f ->
In (g, CGIF_SIZE) (blocks L A) ->
In (f, FILE_BLOCK) (blocks L A) -> sink_at ubs0_msyms mem md f S -> Z.of_nat (length S) + 1024 <= SINK_MAX ->
spZ regs <= 2 ^ 47 ->
(sgct <> 0 -> In (pga, Npg) (blocks L A) /\ Z_to_bv 64 pga = Z_to_bv 64 pgct /\ 3 * sgct <= Npg /\ (pga, Npg) <> (f, FILE_BLOCK) /\
garr8 ubs0segs mem pga GCT /\ 3 * sgct <= Z.of_nat (length GCT)) ->
res_ok A b -> rawnew_room b ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_cgif_raw_newgif) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (res : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWNEW_STK (spZ regs) (sink_fp f) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
((res = 0 /\ 256 < sgct /\ blocks L' A' = blocks L A /\ sink_at ubs0_msyms mem' md' f S /\ res_ok A' b) \/
(res <> 0 /\ sgct <= 256 /\
sink_at ubs0_msyms mem' md' f (S ++ YO07.raw_header W H sgct GCT rattr loops) /\
(exists b1 b2, blocks L' A' = b1 ++ (res, RAW_SIZE) :: b2 /\ blocks L A = b1 ++ b2) /\
obj_at ubs0segs mem' res LAY_Raw [ubs0_A_cgif_writecb; g; pgct; rattr; W; H; sgct; loops; R_PENDING] /\
res_ok A' (rawnew_rb b)))).
Definition flush_gen (g : YO07.gcfg) (cur : YO07.frame) (bef : option YO07.frame) : Z :=
let useLCT := YO07.flag (YO07.f_attr cur) 1 in
let hasAlpha := YO07.flag (YO07.g_attr g) 8 || YO07.flag (YO07.f_attr cur) 2 in
let hasSet := YO07.flag (YO07.f_attr cur) 4 in
let gen0 := YO07.f_gen cur in
let gen1 := match bef with None => YO07.clr gen0 3 | Some _ => if hasAlpha then YO07.clr gen0 3 else gen0 end in
let gen2 := if hasSet then YO07.clr gen1 1 else gen1 in
let npal := if useLCT then YO07.f_nlp cur else YO07.g_ngp g in
if npal =? 256 then YO07.clr gen2 1 else gen2.
Definition flush_specX : Prop :=
forall L A (regs : bvmap 5 word) mem md (g : Z) (s : cgif_st) (N : Z) (i : nat) (f : frame_st) (rest : list (Z * Z)) (S : list Z)
(GPAL : list Z) (cur : YO07.frame) (bef : option YO07.frame) (b : rbound),
fn_pre ubs0_msyms MR FLUSH_STK L A regs mem md -> st_init_done A = true ->
sink_at ubs0_msyms mem md (cg_file s) S -> Z.of_nat (length S) + FRAME_OUT N <= SINK_MAX -> spZ regs <= 2 ^ 47 ->
getr regs 10 = Z_to_bv 64 g ->
cgif_at mem g s -> cgif_wf s N ->
(i = 1%nat \/ i = 2%nat) -> nth_error (cg_frames s) i = Some (Some f) ->
getr regs 11 = Z_to_bv 64 (fr_ptr f) ->
getr regs 12 = Z_to_bv 64 (frame_ptr (nth (i - 1) (cg_frames s) None)) ->
Permutation (blocks L A) (cgif_blocks g s N ++ rest) ->
(Z.land (cg_attr s) 4 = 0 -> garr8 ubs0segs mem (cg_pal s) GPAL /\ Z.of_nat (length GPAL) = 3 * cg_ngp s) ->
frame_rel mem N f cur -> oframe_rel0 mem N (nth (i - 1) (cg_frames s) None) bef ->
res_ok A b -> flush_room b N ->
SR ubs0segs (mkCfg (mkst regs (Z_to_bv 64 ubs0_A_flushFrame) mem (seg_rom ubs0segs)) md)
(fun c' => exists L' A' regs' mem' md' (r rwcur' : Z),
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR FLUSH_STK (spZ regs) (cgif_fp g s N) L A mem md L' A' mem' md' /\
regs_preserved regs regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 r /\ 0 <= r < 2 ^ 64 /\
cgif_at mem' g (flush_upd s i (flush_gen (gcfg_of s GPAL) cur bef) rwcur') /\
cgif_wf (flush_upd s i (flush_gen (gcfg_of s GPAL) cur bef) rwcur') N /\
Permutation (blocks L' A') (cgif_blocks g s N ++ rest) /\
(exists code bytes, YO07.flush_frame (gcfg_of s GPAL) (rc_int (rw_cur s)) cur bef = (code, bytes) /\
Z_to_bv 64 r = Z_to_bv 64 code /\ rwcur' = code mod 2 ^ 32 /\
sink_at ubs0_msyms mem' md' (cg_file s) (S ++ bytes) /\ Z.of_nat (length bytes) <= FRAME_OUT N) /\
res_ok A' (flush_rb b)).
End d.
End c.
