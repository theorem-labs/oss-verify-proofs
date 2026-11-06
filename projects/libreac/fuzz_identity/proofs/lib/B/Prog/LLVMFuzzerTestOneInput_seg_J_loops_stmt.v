(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_H.v, with its module paths and module names changed; 261 of its 299 lines of code are new or changed and 1105 lines of the source are left out. *)
(* The loop helper statements of segment J of LLVMFuzzerTestOneInput's build-B walk
   (fuzz_identity.asan-ubsan, seg_J +0x1388..+0x1988 of lib/B/Prog/LLVMFuzzerTestOneInput_inv.v).

   Six of segment J's seven loops are B's own code, with no call inside them. Each is stated here as one
   closed `Prop`, so that it can be proved in a file of its own and used as a premise of seg_J:

     j_stemcpy_stmt   0x81cc8..0x81d0c   the stem copy into `exp_nm` (SF+528), to the join at 0x81d38
     j_w4cpy_stmt     0x81db8..0x81dfc   the four width digits appended to `exp_nm`, to 0x81e2c
     j_dpcpy_stmt     0x81e5c..0x81e9c   `exp_dp` (SF+592) := `exp_nm`, to 0x81ebc
     j_lit1_stmt      0x81ed4..0x81f14   the literal " ("     appended to `exp_dp`, to 0x81f3c
     j_lit2_stmt      0x81f78..0x81fb8   the literal " in / " appended to `exp_dp`, to 0x81fe0
     j_lit3_stmt      0x8201c..0x8205c   the literal " out)"  appended to `exp_dp`, to 0x82084

   Each statement is of the shape `<premises> -> forall ..., <head cut> W2 c2 -> SRr SEGS W2 c2 <exit cut>`,
   where both cuts are the boundary file's `acut` at the loop's slot with an explicit invariant. Every fact a
   proof needs is in the statement: the journal, the entry's own class-4 frame (`own = [(4, pos)]`, which gives
   the right to write the frame variables), the register values the loop reads, the bytes and the shadow of the
   ranges it touches, and the model bounds. The only Section hypothesis is `AR_laws SEGS B`; the image facts the
   loops use (the literal's bytes and its shadow) are premises of the cut, not of the image hypothesis, so a
   proof of one of these lemmas needs nothing of the contract file beyond the allocator laws.

   Addresses are the offsets in the neutral listing of fuzz_identity.asan-ubsan from the entry
   0x80774, as `BASE + 0xNNN`, as in the boundary file. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v and of the boundary file, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

(* ---- the model values the loops build -------------------------------------------------------------------- *)
(* The length of `exp_dp` before each of the three literal copies: the expected name, then one decimal field
   and the literal before it. n_EXP_DP = n_EXP_NM ++ " (" ++ DEC t_in 1 ++ " in / " ++ DEC t_out 1 ++ " out)". *)
Definition j_d1 (inp : list byte) : Z := Z.of_nat (length (IdentSpec.DEC (SlotModel.t_in inp) 1)).
Definition j_d2 (inp : list byte) : Z := Z.of_nat (length (IdentSpec.DEC (SlotModel.t_out inp) 1)).
Definition j_L1 (inp : list byte) : Z := SlotModel.n_ln inp.
Definition j_L2 (inp : list byte) : Z := j_L1 inp + 2 + j_d1 inp.
Definition j_L3 (inp : list byte) : Z := j_L2 inp + 6 + j_d2 inp.
(* The three literals, as the image holds them (object 9 " (", object 10 " in / ", object 11 " out)"). *)
Definition j_lit_paren : list byte := SlotModel.str_bytes " ("%string.
Definition j_lit_in : list byte := SlotModel.str_bytes " in / "%string.
Definition j_lit_out : list byte := SlotModel.str_bytes " out)"%string.
(* The content of `exp_dp` before each literal copy. *)
Definition j_dp1 (inp : list byte) : list byte := SlotModel.n_EXP_NM inp.
Definition j_dp2 (inp : list byte) : list byte :=
j_dp1 inp ++ j_lit_paren ++ IdentSpec.DEC (SlotModel.t_in inp) 1.
Definition j_dp3 (inp : list byte) : list byte :=
j_dp2 inp ++ j_lit_in ++ IdentSpec.DEC (SlotModel.t_out inp) 1.

(* ---- what every cut of this file carries ----------------------------------------------------------------- *)
(* The part of inv_J_end that no loop of segment J changes: the three heap buffers, the frame-shadow register
   x23, x24 = n_r, x21 = tk, the six machine-frame slots the rest of the segment reads, and the bytes of the
   three buffers when reac_box_name wrote them. mf+176 and mf+160 hold t_in and t_out (seg_F wrote them). *)
Definition jkeep (g : ectx) (pos mf nm tk dp : Z) (ly2 : alayout) (S2 : astate) (W2 : world SEGS)
(regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\
sh_reg g pos regs2 /\
getr regs2 24 = w64 (SlotModel.n_r (e_pl g)) /\ getr regs2 21 = w64 tk /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
val_mem SEGS (rd W2 mem2) (mf + 144) 8 (SlotModel.t_cap_name (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 128) 8 (SlotModel.t_cap_tok (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 120) 8 (SlotModel.t_cap_disp (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 176) 8 (SlotModel.t_in (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 160) 8 (SlotModel.t_out (e_pl g)) /\
val_mem SEGS (rd W2 mem2) (mf + 112) 8 (SlotModel.t_row (e_pl g)) /\
id_at g pos (m_nrec g) W2 mem2 /\
(SlotModel.n_r (e_pl g) = 0 ->
bytes_at8 W2 mem2 nm (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 tk (SlotModel.n_TK (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])).

(* The two frame variables the segment builds, and the registers that address them. x25 = &exp_nm (0x81b70),
   x26 = &exp_dp (0x81b74), x6 = the shadow base (0x81c78, reloaded after each call), x18 = the bitwise
   complement of &exp_dp (0x81e48: the UBSan bound of the `exp_dp` index). Their shadow was cleared at
   0x81b78..0x81ba4, so every byte of the two is addressable. *)
Definition jdp_regs (g : ectx) (pos : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (Z.lnot (SFa g pos + V_dp)) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp).
Definition jdp_mem (g : ectx) (pos : Z) (W2 : world SEGS) (mem2 : word -> option byte) (l : list byte) : Prop :=
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
bytes_at8 W2 mem2 (SFa g pos + V_dp) l.

(* ---- the three literal copies ---------------------------------------------------------------------------- *)
(* The shape of all three (0x81ed4, 0x81f78, 0x8201c), with the registers each one uses:
     a1 = i, the index; a5 = the literal's length; a6 = the literal's byte i;
     the destination `exp_dp + ld + i` and the source `lit + i` each from one register pair.
   Every step: the UBSan bound check of `ld + i` against x18, the shadow test of the destination byte, the
   store, the shadow test of the next source byte, its load, and the test `i + 1 = len`. The loop leaves
   `exp_dp` holding `l ++ lit`. The literal's bytes and its shadow are premises: the image is read-only and the
   loop does not change it, so the caller passes them from llvmf_img and from the registered globals. *)
Definition j_lit_pre (g : ectx) (pos mf nm tk dp : Z) (lit : Z) (lb : list byte) (l : list byte)
(ly2 : alayout) (S2 : astate) (W2 : world SEGS) (regs2 : bvmap 5 word) (mem2 : word -> option byte) : Prop :=
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 l /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
SlotModel.n_wok (e_pl g) = true /\
Z.of_nat (length l) + Z.of_nat (length lb) + 1 <= N_dp /\
(* the literal, as the image holds it: its bytes with the closing NUL, and its shadow *)
bytes_at8 W2 mem2 lit (lb ++ [RcIdentModel.zb 0]) /\
block_shadow (aview SEGS (w_H W2) mem2) SHADOW_OFF lit (Z.of_nat (length lb) + 1) /\
IMG_LO <= lit /\ lit + Z.of_nat (length lb) + 1 <= IMG_TOP /\
~ In (RcIdentModel.zb 0) lb.

(* 0x81ed4 .. 0x81f3c, the literal " (" (object 9). a2 = ld, a3 = &exp_dp + ld, a4 = the literal. *)
Definition j_lit1_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp i W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1760)
(fun ly2 S2 W2 regs2 mem2 md2 =>
j_lit_pre g pos mf nm tk dp (VAL (A_OBJ 9)) j_lit_paren
(j_dp1 (e_pl g) ++ firstn (Z.to_nat i) j_lit_paren) ly2 S2 W2 regs2 mem2 /\
0 <= i < 2 /\
getr regs2 11 = w64 i /\
getr regs2 12 = w64 (j_L1 (e_pl g)) /\
getr regs2 13 = w64 (SFa g pos + V_dp + j_L1 (e_pl g)) /\
getr regs2 14 = w64 (VAL (A_OBJ 9)) /\
getr regs2 15 = w64 2 /\
getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat i) j_lit_paren (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x17c8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp1 (e_pl g) ++ j_lit_paren) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 2 /\
getr regs2 12 = w64 (j_L1 (e_pl g)))).

(* 0x81f78 .. 0x81fe0, the literal " in / " (object 10). a2 = ld, a3 = the literal, a4 = &exp_dp + ld. *)
Definition j_lit2_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp i W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1804)
(fun ly2 S2 W2 regs2 mem2 md2 =>
j_lit_pre g pos mf nm tk dp (VAL (A_OBJ 10)) j_lit_in
(j_dp2 (e_pl g) ++ firstn (Z.to_nat i) j_lit_in) ly2 S2 W2 regs2 mem2 /\
0 <= i < 6 /\
getr regs2 11 = w64 i /\
getr regs2 12 = w64 (j_L2 (e_pl g)) /\
getr regs2 13 = w64 (VAL (A_OBJ 10)) /\
getr regs2 14 = w64 (SFa g pos + V_dp + j_L2 (e_pl g)) /\
getr regs2 15 = w64 6 /\
getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat i) j_lit_in (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x186c)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp2 (e_pl g) ++ j_lit_in) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 6 /\
getr regs2 12 = w64 (j_L2 (e_pl g)))).

(* 0x8201c .. 0x82084, the literal " out)" (object 11). a3 = ld, a2 = &exp_dp + ld, a4 = the literal.
   The exit slot is the one that computes x19 = ld + 5 = n_ld, so the cut keeps a2 and a3. *)
Definition j_lit3_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp i W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x18a8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
j_lit_pre g pos mf nm tk dp (VAL (A_OBJ 11)) j_lit_out
(j_dp3 (e_pl g) ++ firstn (Z.to_nat i) j_lit_out) ly2 S2 W2 regs2 mem2 /\
0 <= i < 5 /\
getr regs2 11 = w64 i /\
getr regs2 12 = w64 (SFa g pos + V_dp + j_L3 (e_pl g)) /\
getr regs2 13 = w64 (j_L3 (e_pl g)) /\
getr regs2 14 = w64 (VAL (A_OBJ 11)) /\
getr regs2 15 = w64 5 /\
getr regs2 16 = w64 (bv_unsigned (nth (Z.to_nat i) j_lit_out (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1910)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\ jdp_mem g pos W2 mem2 (j_dp3 (e_pl g) ++ j_lit_out) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 11 = w64 5 /\
getr regs2 12 = w64 (SFa g pos + V_dp + j_L3 (e_pl g)) /\
getr regs2 13 = w64 (j_L3 (e_pl g)))).

(* ---- the stem copy, 0x81cc8 .. the join at 0x81d38 ------------------------------------------------------- *)
(* The loop copies the NUL-terminated stem at `st` into `exp_nm` (SF+528) byte by byte: x5 = st + j,
   x10 = st + j + 1, x11 = x14 = &exp_nm + j, x12 = -j, x13 = -1, x15 = the byte st[j] (not NUL), x6 = the
   shadow base. It stops at the first NUL of the stem; 0x81d2c then puts the count in x27 (`neg s11,a2`) and
   joins the empty-stem path at 0x81d38, which this statement ends at. `sb` is the stem without its NUL; the
   caller's stem is either `id.model_name` (a frame range) or an image string, so its bytes and its shadow are
   premises. x18 = &w4 (SF+688) and x26 = &exp_dp are live across the loop. *)
Definition j_stemcpy_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp st (sb : list byte) j W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1554)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
SlotModel.n_wok (e_pl g) = true /\
(* the stem: its bytes with the closing NUL, its shadow, and that it is not in the stack window *)
bytes_at8 W2 mem2 st (sb ++ [RcIdentModel.zb 0]) /\
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF st (Z.of_nat (length sb) + 1) /\
amem_range st (Z.of_nat (length sb) + 1) /\
0 < st /\ (Z.of_nat (length sb) <= 16)%Z /\
~ In (RcIdentModel.zb 0) sb /\
(* the stem is not the buffer it is copied into: the loop stores a byte before it reads the next one *)
(st + Z.of_nat (length sb) + 1 <= SFa g pos + V_nm \/ SFa g pos + V_nm + N_nm <= st) /\
(* j bytes are copied; the loop is entered only with a byte left *)
0 <= j < Z.of_nat (length sb) /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (firstn (Z.to_nat j) sb) /\
getr regs2 5 = w64 (st + j) /\
getr regs2 10 = w64 (st + j + 1) /\
getr regs2 11 = w64 (SFa g pos + V_nm + j) /\
getr regs2 14 = w64 (SFa g pos + V_nm + j) /\
getr regs2 12 = w64 (- j) /\
getr regs2 13 = w64 (-1) /\
getr regs2 15 = w64 (bv_unsigned (nth (Z.to_nat j) sb (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x15c4)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (Z.of_nat (length sb)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) sb)).

(* ---- the width-digit copy, 0x81db8 .. 0x81e2c ------------------------------------------------------------ *)
(* After the dash at `exp_nm[ln]` the loop appends the four digits of `w4` (SF+688): x10 = i, x11 = the
   destination of the shadow test (&exp_nm + ln + 1), x12 = &exp_nm + ln + 1 (the store base), x13 = &w4 + 1,
   x14 = -1, x15 = w4[i], x18 = &w4, x27 = ln + 1. It ends at 0x81e20 (`add s11,s11,a0`) and the statement
   stops at the join 0x81e2c, where x27 is the whole length of the expected name. `ld` is the length of the
   name before the digits (the stem and the dash). *)
Definition j_w4cpy_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp ld i (pre : list byte) W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1644)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 ld /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
sh_zero W2 mem2 (SFa g pos + V_w4) N_w4 /\
bytes_at8 W2 mem2 (SFa g pos + V_w4) (SlotModel.n_W4 (e_pl g) ++ [RcIdentModel.zb 0]) /\
SlotModel.n_wok (e_pl g) = true /\
length (SlotModel.n_W4 (e_pl g)) = 4%nat /\
~ In (RcIdentModel.zb 0) (SlotModel.n_W4 (e_pl g)) /\
1 <= ld /\ ld + 4 + 1 <= N_nm /\
0 <= i < 4 /\
Z.of_nat (length pre) = ld /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (pre ++ firstn (Z.to_nat i) (SlotModel.n_W4 (e_pl g))) /\
getr regs2 10 = w64 i /\
getr regs2 11 = w64 (SFa g pos + V_nm + ld) /\
getr regs2 12 = w64 (SFa g pos + V_nm + ld) /\
getr regs2 13 = w64 (SFa g pos + V_w4 + 1) /\
getr regs2 14 = w64 (-1) /\
getr regs2 15 = w64 (bv_unsigned (nth (Z.to_nat i) (SlotModel.n_W4 (e_pl g)) (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16b8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
getr regs2 6 = w64 SHADOW_OFF /\
getr regs2 18 = w64 (SFa g pos + V_w4) /\
getr regs2 25 = w64 (SFa g pos + V_nm) /\
getr regs2 26 = w64 (SFa g pos + V_dp) /\
getr regs2 27 = w64 (ld + 4) /\
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (pre ++ SlotModel.n_W4 (e_pl g)))).

(* ---- exp_dp := exp_nm, 0x81e5c .. 0x81ebc ---------------------------------------------------------------- *)
(* The loop copies the NUL-terminated `exp_nm` into `exp_dp`: x14 = &exp_nm + i, x10 = &exp_nm + i + 1,
   x12 = i (the running length, which the slot mf+200 is set from later), x13 = -1, x15 = exp_nm[i],
   x18 = the complement of &exp_dp. It ends at 0x81ebc with x12 = n_ln. *)
Definition j_dpcpy_stmt : Prop :=
AR_laws SEGS B ->
forall (g : ectx) pos mf nm tk dp i W2 c2,
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16e8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
bytes_at8 W2 mem2 (SFa g pos + V_nm)
(SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 (SFa g pos + V_dp) (firstn (Z.to_nat i) (SlotModel.n_EXP_NM (e_pl g))) /\
SlotModel.n_wok (e_pl g) = true /\
~ In (RcIdentModel.zb 0) (SlotModel.n_EXP_NM (e_pl g)) /\
0 <= i < SlotModel.n_ln (e_pl g) /\
getr regs2 10 = w64 (SFa g pos + V_nm + i + 1) /\
getr regs2 12 = w64 i /\
getr regs2 13 = w64 (-1) /\
getr regs2 14 = w64 (SFa g pos + V_nm + i) /\
getr regs2 15 = w64 (bv_unsigned (nth (Z.to_nat i) (SlotModel.n_EXP_NM (e_pl g)) (RcIdentModel.zb 0)))) W2 c2 ->
SRr SEGS W2 c2
(ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x1748)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
jdp_regs g pos regs2 /\
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) /\
getr regs2 12 = w64 (SlotModel.n_ln (e_pl g)) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
bytes_at8 W2 mem2 (SFa g pos + V_nm)
(SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]) /\
bytes_at8 W2 mem2 (SFa g pos + V_dp) (SlotModel.n_EXP_NM (e_pl g)))).

End c.
End b.
End a.
