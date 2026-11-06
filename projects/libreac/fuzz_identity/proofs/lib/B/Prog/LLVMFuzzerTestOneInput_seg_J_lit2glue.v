(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:2300-2306, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_I.v, with its addresses changed; 887 of its 998 lines of code are new or changed and 3050 lines of the source are left out. *)
(* Piece +0x17e8 .. +0x188c (0x81f5c .. 0x82000) of segment J of LLVMFuzzerTestOneInput's build-B walk
   (fuzz_identity.asan-ubsan): `j_lit2_glue_stmt` of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v.

   0x81f5c..0x81f74 set the copy of the literal " in / " up (x11 = 0, x12 = the counter at mf+200,
   x13 = the literal, x14 = &exp_dp + ld, x15 = 6, x16 = 32) and fall into the loop head 0x81f78, which is
   `j_lit2_stmt` with i = 0.  Its exit 0x81fe0 adds the six bytes to the counter and stores it at mf+200
   (0x81fe4), 0x81fe8..0x81ff8 call put_dec (b = &exp_dp, p = mf+200, v = t_out, mn = 1), and 0x81ffc reloads
   the shadow base into x6.  +0x188c is the cut jc8. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI08 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_seg_J_loops_stmt.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require LLVMFuzzerTestOneInput_seg_J_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require put_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec put_dec_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off; this piece's address arithmetic (shadow_addr, the
   frame's 64-byte alignment) needs it, so this file turns it back on, as the prefix file does. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- pure arithmetic and model lemmas ------------------------------------------------------------------ *)
Lemma jl2_alu : forall op a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 ->
alu64 op (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (zalu_raw 63 64 op a b).
Proof.
intros op a b Ha Hb. apply bv_eq. rewrite alu64_unsigned.
rewrite (unsigned_lit_small a Ha), (unsigned_lit_small b Hb). rewrite Z_to_bv_unsigned. reflexivity.
Qed.

Lemma jl2_m8 : forall a, a mod 32 = 0 -> (a + 200) mod 8 = 0.
Proof.
intros a Ha. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide; [lia|]. destruct Ha as [p ->].
exists (4 * p + 25). ring.
Qed.

Lemma jl2_ra_of_zs : forall rdr lo len x n, zero_shadow rdr SHADOW_OFF lo len ->
lo mod 8 = 0 -> len mod 8 = 0 -> lo <= x -> x + n <= lo + len -> 0 <= n ->
range_addressable rdr SHADOW_OFF x n.
Proof.
intros rdr lo len x n Hz Hlo Hlen Hx Hxn Hn y Hy. exists 0. split; [|left; reflexivity].
replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
by (unfold shadow_of_addr; lia).
apply Hz. clear - Hy Hx Hxn Hlo Hlen Hn. Z.div_mod_to_equations. lia.
Qed.

Lemma jl2_zsh : forall rdr lo len x n, zero_shadow rdr SHADOW_OFF lo len -> 0 <= lo ->
lo + 64 <= x -> 0 < n -> x + n + 96 <= lo + len ->
range_addressable rdr SHADOW_OFF x n /\ shadow_hull_vis rdr x n.
Proof.
intros rdr lo len x n Hz Hlo Hx Hn Hxn. unfold zero_shadow in Hz. split.
- intros y Hy. exists 0. split; [|left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF y) with (shadow_of_addr SHADOW_OFF lo + (y / 8 - lo / 8))
  by (unfold shadow_of_addr; lia).
  apply Hz. clear - Hy Hx Hxn Hn Hlo. Z.div_mod_to_equations. lia.
- intros s Hs. unfold shadow_addr in Hs.
  replace s with (shadow_of_addr SHADOW_OFF lo + (s - SHADOW_OFF - lo / 8)) by (unfold shadow_of_addr; lia).
  rewrite Hz; [discriminate|]. clear - Hs Hx Hxn Hn Hlo. unfold SHADOW_OFF in *.
  Z.div_mod_to_equations. lia.
Qed.

Lemma jl2_len2 : forall inp, Z.of_nat (length (j_dp2 inp)) = j_L2 inp.
Proof.
intro inp.
assert (E : j_dp2 inp = LLVMFuzzerTestOneInput_seg_J_model.m2_dp2 inp) by reflexivity.
assert (F : j_L2 inp = LLVMFuzzerTestOneInput_seg_J_model.m2_L2 inp) by reflexivity.
rewrite E, F. apply LLVMFuzzerTestOneInput_seg_J_model.m2_len2.
Qed.

Lemma jl2_bounds : forall inp, SlotModel.n_wok inp = true ->
1 <= j_d1 inp <= 2 /\ 1 <= j_d2 inp <= 2 /\ 4 <= j_L2 inp <= 25 /\ 11 <= j_L3 inp <= 33.
Proof.
intros inp Hw.
destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_d_range inp Hw) as (Ha & Hb).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le inp Hw) as Hc.
assert (D1 : j_d1 inp = LLVMFuzzerTestOneInput_seg_J_model.m2_d1 inp) by reflexivity.
assert (D2 : j_d2 inp = LLVMFuzzerTestOneInput_seg_J_model.m2_d2 inp) by reflexivity.
unfold j_L3, j_L2, j_L1. rewrite D1, D2. clear - Ha Hb Hc. lia.
Qed.

(* the token buffer's length, as the plain model gives it (lib/B/Prog/LLVMFuzzerTestOneInput_seg_I.v si_tk_len) *)
Lemma jl2_has_dash_len : forall l, SlotModel.has_dash l = true -> (1 <= length l)%nat.
Proof. intros [|b r] H; [discriminate H | cbn; lia]. Qed.

Lemma jl2_tok_len : forall l d,
length (SlotModel.tok_go d l) = (length l - (if negb d && SlotModel.has_dash l then 1 else 0))%nat.
Proof.
induction l as [|b r IH]; intros d; [reflexivity|].
assert (HD : SlotModel.has_dash (b :: r) = (RcIdentModel.bz b =? 45) || SlotModel.has_dash r) by reflexivity.
rewrite HD. destruct d.
- cbn [SlotModel.tok_go negb andb Datatypes.length]. rewrite IH. cbn [negb andb]. lia.
- destruct (RcIdentModel.bz b =? 45) eqn:E;
  cbn [SlotModel.tok_go negb andb orb Datatypes.length]; rewrite E; cbn [andb orb].
  + rewrite IH. cbn [negb andb]. lia.
  + cbn [Datatypes.length]. rewrite IH. cbn [negb andb]. destruct (SlotModel.has_dash r) eqn:D; [|lia].
    pose proof (jl2_has_dash_len r D). lia.
Qed.

Lemma jl2_tk_len : forall inp, Z.of_nat (length (SlotModel.n_TK inp)) = SlotModel.n_lt inp.
Proof.
intro inp. unfold SlotModel.n_TK, SlotModel.TOK, SlotModel.n_lt, SlotModel.n_ln.
rewrite jl2_tok_len. cbn [negb andb].
destruct (SlotModel.has_dash (SlotModel.n_EXP_NM inp)) eqn:D; [|lia].
pose proof (jl2_has_dash_len _ D). lia.
Qed.

(* ---- the symbolic states of the three runs ------------------------------------------------------------- *)
(* run 1 (0x81f5c .. 0x81f78) reads the counter at mf+200 and writes nothing; atom 32 is its value. *)
Definition jl2_regA : YP09.region :=
YP09.mkRegion (Some 9%nat) 200 208 200 200 [YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition jl2_ssA (pc : Z) : sstate := mkSS pc sr_atoms [jl2_regA] None (mkFacts [] [] []).
(* run 2 (0x81fe0 .. the call at 0x81ff8) reads t_out at mf+160 (atom 32) and writes the counter at mf+200. *)
Definition jl2_regB : YP09.region :=
YP09.mkRegion (Some 9%nat) 160 208 200 208 [YP09.mkChunk 160 (CVal 8 (SOff 32 0))].
Definition jl2_ssB (pc : Z) : sstate := mkSS pc sr_atoms [jl2_regB] None (mkFacts [] [] []).
(* run 3 (0x81ffc .. 0x82000) reloads the shadow base from mf+168 and writes nothing. *)
Definition jl2_regC : YP09.region :=
YP09.mkRegion (Some 9%nat) 168 176 168 168 [YP09.mkChunk 168 (CVal 8 (SLit SHADOW_OFF))].
Definition jl2_ssC (pc : Z) : sstate := mkSS pc sr_atoms [jl2_regC] None (mkFacts [] [] []).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
(* the two image hypotheses of the contract (LLVMFuzzerTestOneInput.v:299 and the prefix file's HRO), which
   `j_img` of the prefix file needs; j_lit2_glue_stmt does not carry them. *)
Hypothesis HRO : forall rdr, arodata_okS SEGS B RLO RHI rdr -> arodata_okP SEGS pa_relro_lo pa_relro_hi B rdr.
Hypothesis HIMG : forall (W : world SEGS) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) -> llvmf_img B G W mem.

#[local] Notation ACUT := (acut B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JKEEP := (jkeep B).
#[local] Notation AJ g pos := (ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g)
(e_md g) [(4, pos)]).

(* A journal whose footprint is empty keeps the fd table and the file system (the contract's AJ_NIL_IO,
   here from aos_step_closed since the footprint is []). *)
Lemma jl2_nil_io : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ.
pose proof HJ as (_ & _ & _ & _ & Hio & _).
destruct (aos_step_closed [] md md' ltac:(intros (x & Hx & _); destruct Hx) Hio) as (E1 & E2 & _ & _).
unfold m_fds, m_fs. rewrite E1, E2. split; reflexivity.
Qed.

(* The meter across a call that leaves it where it was. *)
Lemma jl2_meter : ameter_laws MT -> (forall s s' : astate, mo_le MT s s' 0) ->
forall S0 S2 S3 k, mo_le MT S0 S2 (k * MEV MT) -> mo_ok MT S2 ((EV_LLVMF - k) * MEV MT) ->
mo_le MT S0 S3 (k * MEV MT) /\ mo_ok MT S3 ((EV_LLVMF - k) * MEV MT).
Proof.
intros MTL HMT0 S0 S2 S3 k MLE MOK.
pose proof (HMT0 S2 S3) as M23.
split.
- pose proof (mo_le_trans MT MTL _ _ _ _ _ MLE M23) as H. rewrite Z.add_0_r in H. exact H.
- apply (mo_ok_step MT MTL S2 S3 0 ((EV_LLVMF - k) * MEV MT)); [|exact M23].
  apply (mo_ok_le MT MTL _ ((EV_LLVMF - k) * MEV MT) ((EV_LLVMF - k) * MEV MT) MOK). lia.
Qed.

(* A register a call preserves, by name. *)
Lemma jl2_pres : forall (regs regs' : bvmap 5 word) (r : bv 5),
aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros regs regs' r HP Hc. pose proof (HP (bv_unsigned r) Hc) as H.
rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

Lemma jl2_blocks3 : forall (g : ectx) ly S nm tk dp,
hblocks B g ly S [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
In (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) (ablocks B ly S) /\
In (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) (ablocks B ly S) /\
In (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) (ablocks B ly S).
Proof.
intros g ly S nm tk dp (Hperm & _).
split; [|split]; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left.
- left; reflexivity.
- right; left; reflexivity.
- right; right; left; reflexivity.
Qed.

(* ---- the bytes this piece does not touch ---------------------------------------------------------------- *)
(* Every fact the cut carries lives in one of these zones: the machine frame and the saved words above it,
   except the counter slot mf+200 the piece rewrites; the class-4 frame, except `exp_dp`; the frame's shadow;
   the input block; and the three heap buffers. *)
Definition jl2_area (g : ectx) (pos mf nm tk dp : Z) (a : Z) : Prop :=
(mf <= a < mf + M_n2 \/ mf + M_n2 + 8 <= a < e_sp0 g) \/
(SFa g pos <= a < SFa g pos + V_dp \/ SFa g pos + V_dp + N_dp <= a < SFa g pos + 1024) \/
(shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) \/
(e_p g <= a < e_p g + e_n g) \/
(exists b m, In (b, m) [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] /\ b <= a < b + req_size m).

(* The memory part of ecommon, of jkeep and of the two frame variables the cut speaks of. *)
Definition jl2_vals (g : ectx) (pos mf nm tk dp : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 16) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 64) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 192) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 168) 8 SHADOW_OFF /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)) /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
bytes_at8 W2 mem2 (e_p g) (e_pl g) /\
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
bytes_at8 W2 mem2 dp (SlotModel.n_EXP_DP (e_pl g) ++ [RcIdentModel.zb 0])) /\
sh_zero W2 mem2 (SFa g pos + V_nm) N_nm /\
sh_zero W2 mem2 (SFa g pos + V_dp) N_dp /\
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g) ++ [RcIdentModel.zb 0]).

Lemma jl2_vals_moved : forall (g : ectx) pos mf nm tk dp (W : world SEGS) m (W' : world SEGS) m',
mf + 320 <= e_sp0 g -> SFa g pos mod 8 = 0 -> e_n g = Z.of_nat (length (e_pl g)) ->
SlotModel.n_wok (e_pl g) = true ->
(forall a, jl2_area g pos mf nm tk dp a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
jl2_vals g pos mf nm tk dp W m -> jl2_vals g pos mf nm tk dp W' m'.
Proof.
intros g pos mf nm tk dp W m W' m' Hsp HSF8 Hlen Hwok HK HV.
assert (Hid38 : length (m_id g (m_nrec g)) = 38%nat) by apply SlotModel.rec_id_length.
pose proof (SlotModel.n_ln_le (e_pl g) Hwok) as Hlnle. unfold SlotModel.n_ln in Hlnle.
assert (VM : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n -> jl2_area g pos mf nm tk dp (a + k)) ->
val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W' m') a n v).
{ intros a n v Ha Hv. apply (val_mem_kept SEGS (w_H W) (w_H W') m m' a n v); [|exact Hv].
  intros k Hk. apply HK, Ha, Hk. }
assert (GA : forall a l, (forall k, 0 <= k < Z.of_nat (length l) -> jl2_area g pos mf nm tk dp (a + k)) ->
garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W' m') a l).
{ intros a l Ha Hg. apply (garr8_frame SEGS _ _ a l Hg). intros x Hx.
  apply (mbyte_of_aview SEGS). replace x with (a + (x - a)) by lia. apply HK, Ha. lia. }
assert (ESHid : shadow_of_addr SHADOW_OFF (SFa g pos + V_id) = shadow_addr (SFa g pos) + 44).
{ unfold shadow_of_addr, shadow_addr, V_id. clear - HSF8. Z.div_mod_to_equations. lia. }
assert (ESHnm : shadow_of_addr SHADOW_OFF (SFa g pos + V_nm) = shadow_addr (SFa g pos) + 66).
{ unfold shadow_of_addr, shadow_addr, V_nm. clear - HSF8. Z.div_mod_to_equations. lia. }
assert (ESHdp : shadow_of_addr SHADOW_OFF (SFa g pos + V_dp) = shadow_addr (SFa g pos) + 74).
{ unfold shadow_of_addr, shadow_addr, V_dp. clear - HSF8. Z.div_mod_to_equations. lia. }
destruct HV as (V16 & V64 & V192 & V168 & Vra & Vs0 & S9 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 &
S26 & S27 & Vflag & Hinb & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs &
Hshnm & Hshdp & Hnmb).
unfold jl2_vals, jl2_area in *.
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V16]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V64]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V192]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V168]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact Vra]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact Vs0]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S9]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S18]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S19]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S20]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S21]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S22]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S23]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S24]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S25]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S26]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; right; lia | exact S27]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold V_dp, N_dp; clear - Hk; right; left; right; lia
| exact Vflag]|].
split.
{ unfold bytes_at8 in *. apply GA; [|exact Hinb]. rewrite length_map. intros k Hk.
  right; right; right; left. clear - Hk Hlen. lia. }
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V152]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V184]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V144]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V128]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V120]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V176]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V160]|].
split; [apply VM; [intros k Hk; cbn in Hk; unfold M_n2; clear - Hk Hsp; left; left; lia | exact V112]|].
split.
{ unfold id_at, bytes_at8, sh_zero, sh_blk in *. destruct Hid as (Hidb & Hidz & Hidk).
  split.
  { apply GA; [|exact Hidb]. rewrite length_map, Hid38.
    intros k Hk. right; left; left. unfold V_id, V_dp. clear - Hk. lia. }
  split.
  { intros i Hi. rewrite HK; [exact (Hidz i Hi)|]. rewrite ESHid.
    right; right; left. unfold N_id in Hi. clear - Hi. lia. }
  { destruct Hidk as (Hm & Hn0 & Hb). split; [exact Hm|]. split; [exact Hn0|].
    intros i Hi. rewrite HK; [exact (Hb i Hi)|]. rewrite ESHid.
    right; right; left. unfold N_id in Hi. clear - Hi. lia. } }
split.
{ intros Hr0. destruct (Hbufs Hr0) as (Hb1 & Hb2 & Hb3).
  destruct (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (_ & Hc1 & Hc2 & Hc3).
  pose proof (jl2_tk_len (e_pl g)) as Htk.
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(lia)) as [_ Rq1].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(lia)) as [_ Rq2].
  pose proof (req_size_pos (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(lia)) as [_ Rq3].
  unfold bytes_at8 in *.
  split.
  { apply GA; [|exact Hb1]. rewrite length_map, length_app. cbn [length]. intros k Hk.
    right; right; right; right. exists nm, (Z.max (SlotModel.t_cap_name (e_pl g)) 1).
    split; [left; reflexivity|]. unfold SlotModel.n_ln in Hc1. clear - Hk Hc1 Rq1. lia. }
  split.
  { apply GA; [|exact Hb2]. rewrite length_map, length_app. cbn [length]. intros k Hk.
    right; right; right; right. exists tk, (Z.max (SlotModel.t_cap_tok (e_pl g)) 1).
    split; [right; left; reflexivity|]. clear - Hk Hc2 Rq2 Htk. lia. }
  { apply GA; [|exact Hb3]. rewrite length_map, length_app. cbn [length]. intros k Hk.
    right; right; right; right. exists dp, (Z.max (SlotModel.t_cap_disp (e_pl g)) 1).
    split; [right; right; left; reflexivity|]. unfold SlotModel.n_ld in Hc3. clear - Hk Hc3 Rq3. lia. } }
split.
{ unfold sh_zero in *. intros i Hi. rewrite HK; [exact (Hshnm i Hi)|]. rewrite ESHnm.
  right; right; left. unfold N_nm in Hi. clear - Hi. lia. }
split.
{ unfold sh_zero in *. intros i Hi. rewrite HK; [exact (Hshdp i Hi)|]. rewrite ESHdp.
  right; right; left. unfold N_dp in Hi. clear - Hi. lia. }
{ unfold bytes_at8 in *. apply GA; [|exact Hnmb]. rewrite length_map, length_app. cbn [length].
  intros k Hk. right; left; left. unfold V_nm, V_dp. clear - Hk Hlnle. lia. }
Qed.

(* What put_dec keeps, as a fact about jl2_area: outside its two write ranges every zone of the cut is kept
   (the machine stack above sp, the entry's frame and its shadow, the heap blocks). *)
Lemma jl2_call_keep : AR_laws SEGS B -> STK_LLVMF <= LLVMF_STK ->
forall (g : ectx) pos mf nm tk dp ly2 S2 (W : world SEGS) memc md2 k (W2 : world SEGS) mem2 (Ewr : Z -> Prop),
AJ g pos ly2 S2 W memc md2 k -> frames S2 = [(4, pos)] ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
hblocks B g ly2 S2 [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1);
(dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
EPRE g ->
tcj_kept B put_dec.PUT_DEC_STK ly2 S2 W memc W2 mem2 mf Ewr ->
(forall a, Ewr a -> (mf + M_n2 <= a < mf + M_n2 + 8) \/
(SFa g pos + V_dp <= a < SFa g pos + V_dp + N_dp)) ->
forall a, jl2_area g pos mf nm tk dp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a.
Proof.
intros LAWS HSTK g pos mf nm tk dp ly2 S2 W memc md2 k W2 mem2 Ewr HJ Hfrs Hmfb Hbl HPRE HKP HE a Ha.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hmf0 : alloc_ceiling + 16400 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
destruct (j_geo B LLVMF_STK LAWS g pos k ly2 S2 W memc md2 HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
destruct HKP as (K1 & K2 & K3 & K4 & K5 & K6).
destruct (jl2_blocks3 g ly2 S2 nm tk dp Hbl) as (Inm & Itk & Idp).
assert (HBK : forall b m, In (b, m) (ablocks B ly2 S2) -> b <= a < b + req_size m ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a).
{ intros b m Hin Hr.
  destruct (al_blocks _ _ LAWS ly2 S2 W memc md2 b m HAR Hin) as (_ & Hb4096 & Hbceil & _).
  pose proof (sep_block_frame _ _ LAWS ly2 S2 W memc md2 b m 4 pos HAR Hin Hin4) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFa, HFB in Hsep.
  replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hin ltac:(clear - Hr; lia)).
  intros HEa. destruct (HE (b + (a - b)) HEa) as [Hx | Hx].
  - clear - Hx Hr Hbceil Hmf0 Has C1. unfold M_n2 in Hx. lia.
  - clear - Hx Hr Hsep. unfold V_dp, N_dp in Hx. lia. }
unfold jl2_area in Ha.
destruct Ha as [Hs | [Hf | [Hsh | [Hi | Hhp]]]].
- apply K1.
  + clear - Hs Hmf0 Hmfb H47 Hshi Has C1. unfold M_n2 in Hs. lia.
  + unfold put_dec.PUT_DEC_STK, ESTACK. clear - Hs. unfold M_n2 in Hs. lia.
  + intros HEa. destruct (HE a HEa) as [Hx | Hx].
    * clear - Hs Hx. unfold M_n2 in *. lia.
    * clear - Hs Hx HSF0 HSF1 Hmf0 Has C1. unfold V_dp, N_dp, M_n2 in *. lia.
- apply (K4 4 pos a Hin4).
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB.
    clear - Hf. unfold V_dp, N_dp in Hf. lia.
  + intros HEa. destruct (HE a HEa) as [Hx | Hx].
    * clear - Hf Hx HSF0 HSF1 Hmf0 Has C1. unfold V_dp, N_dp, M_n2 in *. lia.
    * clear - Hf Hx. unfold V_dp, N_dp in *. lia.
- apply (K4 4 pos a Hin4).
  + right. unfold in_zr. cbn [fst snd]. rewrite EFa, HFB. clear - Hsh. lia.
  + intros HEa. destruct (HE a HEa) as [Hx | Hx].
    * clear - Hsh Hx Hsh0 Hsh1 Hmf0 Has C1. unfold M_n2 in Hx. lia.
    * clear - Hsh Hx Hsfsh HSF0 HSF1 Hsh0 Hsh1. unfold V_dp, N_dp in Hx. lia.
- destruct HPRE as (_ & _ & _ & _ & Hpn & _).
  destruct Hpn as [(Hn0 & _) | (Hn0 & Hine)]; [clear - Hi Hn0; lia|].
  assert (Iinp : In (e_p g, e_n g) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym (proj1 Hbl))); apply in_or_app; right; exact Hine).
  pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as [_ Rq].
  apply (HBK (e_p g) (e_n g) Iinp). clear - Hi Rq. lia.
- destruct Hhp as (b & m & Hinl & Hr).
  apply (HBK b m); [|exact Hr].
  cbn [In] in Hinl. destruct Hinl as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <-; assumption.
Qed.

Lemma j_lit2_glue : j_lit2_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS G.
Proof.
unfold j_lit2_glue_stmt.
intros LAWS HSTK HEV HPD PSIG MTL HMT0 GM HG10 HL2 g pos mf nm tk dp W2 c2 Hstart Hwok.
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
(* ---- the start cut jc7 at +0x17e8 ---- *)
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK0 & HDR0 & HDM0 & R27 & Vn2 & Hnmb0).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
SS9 & SS18 & SS19 & SS20 & SS21 & SS22 & SS23 & SS24 & SS25 & SS26 & SS27 & Vflag & HPRE & Hfds & Hfs & Hinb).
pose proof HK0 as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
destruct HDR0 as (R6 & R18 & R25 & R26).
destruct HDM0 as (Hshnm & Hshdp & Hdpb).
(* ---- constants and geometry ---- *)
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof pa_segs_low as Hsegs. pose proof pa_wx as Hwx.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic & _).
pose proof Hstatic as (Hsp0al & _ & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
destruct (j_geo B LLVMF_STK LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs)
as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
assert (Hmf0 : alloc_ceiling + 16400 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Hmfhi : mf + 320 <= e_sp0 g) by (clear - Hmfb; lia).
assert (HSF8 : SFa g pos mod 8 = 0) by (clear - HSF64; lia).
pose proof HPRE as (_ & _ & _ & _ & Hpn & Hlen & _ & _ & Hnev0 & _).
destruct (jl2_bounds (e_pl g) Hwok) as (Hd1 & Hd2 & HL2b & HL3b).
assert (HLI : Z.of_nat (length j_lit_in) = 6) by reflexivity.
pose proof (jl2_len2 (e_pl g)) as HDP2len.
assert (Hti : 0 <= SlotModel.t_in (e_pl g) < 256) by exact (SlotModel.inb_range _ _).
assert (Hto : 0 <= SlotModel.t_out (e_pl g) < 256) by exact (SlotModel.inb_range _ _).
(* ---- the bundle of memory facts at the start ---- *)
assert (HV0 : jl2_vals g pos mf nm tk dp W2 mem2).
{ unfold jl2_vals.
  split; [exact V16|]. split; [exact V64|]. split; [exact V192|]. split; [exact V168|].
  split; [exact Vra|]. split; [exact Vs0|]. split; [exact SS9|]. split; [exact SS18|].
  split; [exact SS19|]. split; [exact SS20|]. split; [exact SS21|]. split; [exact SS22|].
  split; [exact SS23|]. split; [exact SS24|]. split; [exact SS25|]. split; [exact SS26|].
  split; [exact SS27|]. split; [exact Vflag|]. split; [exact Hinb|].
  split; [exact V152|]. split; [exact V184|]. split; [exact V144|]. split; [exact V128|].
  split; [exact V120|]. split; [exact V176|]. split; [exact V160|]. split; [exact V112|].
  split; [exact Hid|]. split; [exact Hbufs|]. split; [exact Hshnm|]. split; [exact Hshdp|].
  exact Hnmb0. }
(* ---- run 1: +0x17e8 .. +0x1804 (the loop head) ---- *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 (j_L2 (e_pl g))])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs2 r)
by (intros n r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER1 : regs_ok E1 sr_atoms regs2) by (rewrite HE1; apply regs_ok_Eimg_Ereg).
assert (HAE1 : env_agree 32 (Ereg regs2 [Z_to_bv 64 (j_L2 (e_pl g))]) E1)
by (rewrite HE1; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EX1 : ew E1 32 = Z_to_bv 64 (j_L2 (e_pl g))).
{ rewrite HE1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs2 _ 0). }
clear HE1.
assert (U9_1 : bv_unsigned (ew E1 9) = mf).
{ rewrite (EE1 9%nat 9%bv eq_refl), Rs1. apply unsigned_lit_small.
  clear - Hmf0 H47 Hmfb Hshi C1 Has. lia. }
assert (HS1 : st_ok_pi SEGS VAL E1 (jl2_ssA 0x17e8)
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x17e8)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold jl2_ssA. apply pa_entry_st_ok_full.
  - exact ER1.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    unfold jl2_regA, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9_1. split; [clear - Hmf0 C1; lia|].
    split; [clear - Hmfb H47 Hshi; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E1 _ mf 200 8 (SOff 32 0) (j_L2 (e_pl g)));
    [cbn [sv_denot]; rewrite EX1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - HL2b; lia | lia | exact Vn2].
  - apply pairwise_disjoint_of_extents. unfold jl2_regA, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x17e8)) with (Z_to_bv 64 (BASE + 0x17e8)).
paj_run_to_sh RUNTOP HS1 HJ 0x1804.
{ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jl2_regA]; lia | apply awr_ok_nil]. }
rename ms into msA. rename mat into matA. rename HFr into HFrA. clear HF HG.
assert (EQR1 : mrestrict (w_H W2) (ms_mem msA) = mrestrict (w_H W2) mem2).
{ apply functional_extensionality. intros xq. apply HFrA.
  intros (r & Hin & Hr). cbn [ss_mem jl2_ssA In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi jl2_regA] in Hr. clear - Hr. lia. }
assert (EQV1 : aview SEGS (w_H W2) (ms_mem msA) = aview SEGS (w_H W2) mem2)
by (unfold aview; rewrite EQR1; reflexivity).
assert (HV1 : jl2_vals g pos mf nm tk dp W2 (ms_mem msA)).
{ apply (jl2_vals_moved g pos mf nm tk dp W2 mem2 W2 (ms_mem msA) Hmfhi HSF8 Hlen Hwok);
  [intros a _; rewrite EQV1; reflexivity | exact HV0]. }
unfold bytes_at8 in Hdpb. rewrite <- EQR1 in Hdpb.
destruct HV1 as (V16a & V64a & V192a & V168a & Vraa & Vs0a & SS9a & SS18a & SS19a & SS20a & SS21a & SS22a &
SS23a & SS24a & SS25a & SS26a & SS27a & Vflaga & Hinba & V152a & V184a & V144a & V128a & V120a & V176a &
V160a & V112a & Hida & Hbufsa & Hshnma & Hshdpa & Hnmba).
assert (RKA : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv;
26%bv; 27%bv] -> getr (ms_regs msA) r = getr regs2 r).
{ eapply (regs_kept_of_st_ok_pi E1 _ (restrict (w_H W2) msA) regs2 _
  [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS1 HAE1).
  vm_compute. reflexivity. }
prreg HS1 (11%bv : bv 5) A11. prreg HS1 (12%bv : bv 5) A12. prreg HS1 (13%bv : bv 5) A13.
prreg HS1 (14%bv : bv 5) A14. prreg HS1 (15%bv : bv 5) A15. prreg HS1 (16%bv : bv 5) A16.
assert (EO10 : bv_unsigned (ew E1 251%nat) = VAL (A_OBJ 10))
by (apply (HEI1 251%nat); unfold A_TEXT, A_LIM; lia).
destruct (pa_obj_img 10%nat ltac:(lia)) as (Hobj1 & Hobj2).
rewrite (EE1 26%nat 26%bv eq_refl), R26, EX1 in A14. unfold w64 in A14.
rewrite (jl2_alu ALU_ADD (SFa g pos + V_dp) (j_L2 (e_pl g))
ltac:(clear - HSF0 HSF1 C1; unfold V_dp; lia) ltac:(clear - HL2b; lia)) in A14.
cbn [zalu_raw] in A14.
assert (HIM1 : llvmf_img B G W2 (ms_mem msA))
by exact (j_img B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB asink_syms_T KS asink_none
ameta_inv arodata_okS G HRO HIMG g pos _ ly2 S2 W2 (ms_mem msA) _ HJ HPRE).
destruct HIM1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlit10 & _).
assert (HLB : bytes_at8 W2 (ms_mem msA) (VAL (A_OBJ 10)) (j_lit_in ++ [RcIdentModel.zb 0])).
{ unfold bytes_at8.
  replace (map (fun b : byte => bv_unsigned b) (j_lit_in ++ [RcIdentModel.zb 0]))
  with [32; 105; 110; 32; 47; 32; 0] by (vm_compute; reflexivity).
  exact Hlit10. }
assert (HBS : block_shadow (aview SEGS (w_H W2) (ms_mem msA)) SHADOW_OFF (VAL (A_OBJ 10)) 7)
by exact (GM ly2 S2 W2 (ms_mem msA) _ (VAL (A_OBJ 10)) 7 HG10 (proj1 HJ)).
assert (HNZ : ~ In (RcIdentModel.zb 0) j_lit_in).
{ apply LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_notin.
  apply LLVMFuzzerTestOneInput_seg_J_model.m2_NZ_b. vm_compute. reflexivity. }
(* ---- the loop j_lit2_stmt, entered with i = 0 ---- *)
eapply SRr_bind.
{ apply (HL2 LAWS g pos mf nm tk dp 0).
  unfold acut. pmkst HS1.
  exists ly2, S2, (ms_regs msA), (ms_mem msA). eexists.
  split; [reflexivity|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
  split; [exact MLE|]. split; [exact MOK|].
  split.
  { unfold ecommon.
    split; [rewrite (RKA 2%bv ltac:(cbn; tauto)); exact Rsp|].
    split; [rewrite (RKA 9%bv ltac:(cbn; tauto)); exact Rs1|].
    split; [rewrite (RKA 8%bv ltac:(cbn; tauto)); exact Rs0|].
    split; [exact Hmfb|]. split; [exact Hmf32|].
    split; [rewrite (RKA 3%bv ltac:(cbn; tauto)); exact Rgp|].
    split; [rewrite (RKA 4%bv ltac:(cbn; tauto)); exact Rtp|].
    split; [exact V16a|]. split; [exact V64a|]. split; [exact V192a|]. split; [exact V168a|].
    split; [exact Vraa|]. split; [exact Vs0a|]. split; [exact SS9a|]. split; [exact SS18a|].
    split; [exact SS19a|]. split; [exact SS20a|]. split; [exact SS21a|]. split; [exact SS22a|].
    split; [exact SS23a|]. split; [exact SS24a|]. split; [exact SS25a|]. split; [exact SS26a|].
    split; [exact SS27a|]. split; [exact Vflaga|]. split; [exact HPRE|].
    split; [rewrite j_wvb_fds; exact Hfds|]. split; [rewrite j_wvb_fs; exact Hfs|]. exact Hinba. }
  cbn [Z.to_nat firstn]. rewrite app_nil_r.
  split.
  { unfold j_lit_pre.
    split.
    { unfold jkeep.
      split; [exact Hbl|].
      split; [unfold sh_reg; rewrite (RKA 23%bv ltac:(cbn; tauto)); exact Rs7|].
      split; [rewrite (RKA 24%bv ltac:(cbn; tauto)); exact R24|].
      split; [rewrite (RKA 21%bv ltac:(cbn; tauto)); exact R21|].
      split; [exact V152a|]. split; [exact V184a|]. split; [exact V144a|]. split; [exact V128a|].
      split; [exact V120a|]. split; [exact V176a|]. split; [exact V160a|]. split; [exact V112a|].
      split; [exact Hida|]. exact Hbufsa. }
    split.
    { unfold jdp_regs.
      split; [rewrite (RKA 6%bv ltac:(cbn; tauto)); exact R6|].
      split; [rewrite (RKA 18%bv ltac:(cbn; tauto)); exact R18|].
      split; [rewrite (RKA 25%bv ltac:(cbn; tauto)); exact R25|].
      rewrite (RKA 26%bv ltac:(cbn; tauto)); exact R26. }
    split.
    { unfold jdp_mem. split; [exact Hshnma|]. split; [exact Hshdpa|]. exact Hdpb. }
    split; [exact Hnmba|].
    split; [rewrite (RKA 27%bv ltac:(cbn; tauto)); exact R27|].
    split; [exact Hwok|].
    split; [rewrite HDP2len, HLI; unfold N_dp; clear - HL2b; lia|].
    split; [exact HLB|].
    split; [rewrite HLI; exact HBS|].
    split; [clear - Hobj1; lia|].
    split; [rewrite HLI; clear - Hobj2; lia|].
    exact HNZ. }
  split; [lia|].
  split; [rewrite A11; reflexivity|].
  split; [rewrite A12, EX1; reflexivity|].
  split; [rewrite A13; unfold w64; rewrite <- EO10, Z_to_bv_bv_unsigned; reflexivity|].
  split; [rewrite A14; reflexivity|].
  split; [rewrite A15; reflexivity|].
  rewrite A16.
  replace (bv_unsigned (nth (Z.to_nat 0) j_lit_in (RcIdentModel.zb 0))) with 32
  by (vm_compute; reflexivity).
  reflexivity. }
cbv beta.
intros W3 c3 Hwle3 (lyh & Sh & regsh & memh & mdh & -> & HJh & Hfrsh & Hkh & MLEh & MOKh & HCh & HPh).
(* ---- the loop's exit cut at +0x186c ---- *)
destruct HPh as (HKh & HDRh & HDMh & Hnmbh & R27h & R11h & R12h).
pose proof HCh as (Rsph & Rs1h & Rs0h & Hmfbh & Hmf32h & Rgph & Rtph & V16h & V64h & V192h & V168h & Vrah &
Vs0h & SS9h & SS18h & SS19h & SS20h & SS21h & SS22h & SS23h & SS24h & SS25h & SS26h & SS27h & Vflagh &
_ & Hfdsh & Hfsh & Hinbh).
pose proof HKh as (Hblh & Rs7h & R24h & R21h & V152h & V184h & V144h & V128h & V120h & V176h & V160h &
V112h & Hidh & Hbufsh).
destruct HDRh as (R6h & R18h & R25h & R26h).
destruct HDMh as (Hshnmh & Hshdph & Hdpbh).
pose proof HJh as (HARh & Hlyh & _ & _ & _ & _ & Hnevh & _ & _ & _ & _ & _ & _ & Hpresh & Hstatich & _).
pose proof Hstatich as (_ & _ & Hceilh & Hsloh & Hshih & H47h & _).
pose proof Hlyh as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Esloh & Eshih & _).
destruct (j_geo B LLVMF_STK LAWS g pos _ lyh Sh W3 memh mdh HJh Hfrsh)
as (EFah & HSF0h & HSF1h & HSF64h & Hsh0h & Hsh1h & Hsfshh).
assert (Hin4h : In (4, pos) (frames Sh)) by (rewrite Hfrsh; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyh Sh W3 memh mdh 4 pos HARh Hin4h) as (_ & _ & Happ).
rewrite EFah, HFB in Happ.
destruct (jl2_blocks3 g lyh Sh nm tk dp Hblh) as (Inmh & Itkh & Idph).
destruct (al_blocks _ _ LAWS lyh Sh W3 memh mdh _ _ HARh Inmh) as (_ & Hnm4 & Hnmc & _).
destruct (al_blocks _ _ LAWS lyh Sh W3 memh mdh _ _ HARh Itkh) as (_ & Htk4 & Htkc & _).
destruct (al_blocks _ _ LAWS lyh Sh W3 memh mdh _ _ HARh Idph) as (_ & Hdp4 & Hdpc & _).
assert (HINP : 0 < e_n g -> 4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling).
{ intros Hn0. destruct Hpn as [(Hz & _) | (_ & Hine)]; [clear - Hz Hn0; lia|].
  assert (Iin : In (e_p g, e_n g) (ablocks B lyh Sh))
  by (apply (Permutation_in _ (Permutation_sym (proj1 Hblh))); apply in_or_app; right; exact Hine).
  destruct (al_blocks _ _ LAWS lyh Sh W3 memh mdh _ _ HARh Iin) as (_ & Hp4 & Hpc & _).
  pose proof (req_size_pos (e_n g) ltac:(clear - Hn0; lia)) as [_ Rq]. clear - Hp4 Hpc Rq. lia. }
assert (AREA_RNG : forall a, jl2_area g pos mf nm tk dp a ->
0 <= a < 2 ^ 64 /\ ~ (mf + 200 <= a < mf + 208)).
{ intros a Ha. unfold jl2_area in Ha.
  destruct Ha as [Hs | [Hf | [Hsh | [Hi | Hhp]]]].
  - unfold M_n2 in Hs. clear - Hs Hmf0 Hmfb H47 Hshi C1. lia.
  - clear - Hf HSF0h HSF1h Hmf0 C1. unfold V_dp, N_dp in Hf. lia.
  - clear - Hsh Hsh0h Hsh1h Hmf0 C1. lia.
  - assert (Hn0 : 0 < e_n g) by (clear - Hi; lia). destruct (HINP Hn0) as [Hp4 Hpc].
    clear - Hi Hp4 Hpc Hmf0 C1. lia.
  - destruct Hhp as (b & m & Hinl & Hr). cbn [In] in Hinl.
    destruct Hinl as [Eq|[Eq|[Eq|[]]]]; injection Eq as <- <-;
    [clear - Hr Hnm4 Hnmc Hmf0 C1 | clear - Hr Htk4 Htkc Hmf0 C1 | clear - Hr Hdp4 Hdpc Hmf0 C1]; lia. }
assert (HVh : jl2_vals g pos mf nm tk dp W3 memh).
{ unfold jl2_vals.
  split; [exact V16h|]. split; [exact V64h|]. split; [exact V192h|]. split; [exact V168h|].
  split; [exact Vrah|]. split; [exact Vs0h|]. split; [exact SS9h|]. split; [exact SS18h|].
  split; [exact SS19h|]. split; [exact SS20h|]. split; [exact SS21h|]. split; [exact SS22h|].
  split; [exact SS23h|]. split; [exact SS24h|]. split; [exact SS25h|]. split; [exact SS26h|].
  split; [exact SS27h|]. split; [exact Vflagh|]. split; [exact Hinbh|].
  split; [exact V152h|]. split; [exact V184h|]. split; [exact V144h|]. split; [exact V128h|].
  split; [exact V120h|]. split; [exact V176h|]. split; [exact V160h|]. split; [exact V112h|].
  split; [exact Hidh|]. split; [exact Hbufsh|]. split; [exact Hshnmh|]. split; [exact Hshdph|].
  exact Hnmbh. }
(* ---- run 2: +0x186c .. the call at 0x81ff8 ---- *)
remember (j_L2 (e_pl g) + 6) as n2 eqn:En2.
assert (Hn2b : 10 <= n2 <= 31) by (clear - HL2b En2; lia).
remember (Eimg (Ereg regsh [Z_to_bv 64 (SlotModel.t_out (e_pl g))])) as E2 eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regsh r)
by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER2 : regs_ok E2 sr_atoms regsh) by (rewrite HE2; apply regs_ok_Eimg_Ereg).
assert (HAE2 : env_agree 32 (Ereg regsh [Z_to_bv 64 (SlotModel.t_out (e_pl g))]) E2)
by (rewrite HE2; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EX2 : ew E2 32 = Z_to_bv 64 (SlotModel.t_out (e_pl g))).
{ rewrite HE2. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regsh _ 0). }
clear HE2.
assert (U9_2 : bv_unsigned (ew E2 9) = mf).
{ rewrite (EE2 9%nat 9%bv eq_refl), Rs1h. apply unsigned_lit_small.
  clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (HS2 : st_ok_pi SEGS VAL E2 (jl2_ssB 0x186c)
(restrict (w_H W3) (mkst regsh (Z_to_bv 64 (BASE + 0x186c)) memh (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold jl2_ssB. apply pa_entry_st_ok_full.
  - exact ER2.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    unfold jl2_regB, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9_2. split; [clear - Hmf0 C1; lia|].
    split; [clear - Hmfb H47 Hshi; lia|].
    split; [intros o Ho; apply (apresent_writable SEGS); apply Hpresh;
    clear - Ho Hmfb HSTK' Has; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E2 _ mf 160 8 (SOff 32 0) (SlotModel.t_out (e_pl g)));
    [cbn [sv_denot]; rewrite EX2, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hto; lia | lia | exact V160h].
  - apply pairwise_disjoint_of_extents. unfold jl2_regB, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
unfold cfg_at. change (w64 (BASE + 0x186c)) with (Z_to_bv 64 (BASE + 0x186c)).
paj_run_to_sh RUNTOP HS2 HJh 0x1870.
{ apply (awr_ok_cons_gen E2 jl2_regB [] LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g))
  (ablocks B lyh Sh) lyh [(4, pos)] 9%nat mf).
  - reflexivity.
  - exact U9_2.
  - cbn [YP09.r_wlo YP09.r_whi jl2_regB]. intros a Ha. left. clear - Ha Hmfb HSTK' Has. lia.
  - apply awr_ok_nil. }
rename ms into msB. rename mat into matB. rename HFr into HFrB. clear HF HG.
prreg HS2 (11%bv : bv 5) B11.
rewrite (EE2 12%nat 12%bv eq_refl), R12h, (EE2 11%nat 11%bv eq_refl), R11h in B11.
unfold w64 in B11.
rewrite (jl2_alu ALU_ADD 6 (j_L2 (e_pl g)) ltac:(clear; lia) ltac:(clear - HL2b; lia)) in B11.
cbn [zalu_raw] in B11.
replace (6 + j_L2 (e_pl g)) with n2 in B11 by (clear - En2; lia).
pose proof (st_ok_pi_pin_reg' _ _ _ (11%bv : bv 5) n2 HS2 B11 eq_refl) as HS2p.
clear HS2 B11.
paj_run_shc RUNP RUNC HS2p HJh.
{ apply (awr_ok_cons_gen E2 jl2_regB [] LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g))
  (ablocks B lyh Sh) lyh [(4, pos)] 9%nat mf).
  - reflexivity.
  - exact U9_2.
  - cbn [YP09.r_wlo YP09.r_whi jl2_regB]. intros a Ha. left. clear - Ha Hmfb HSTK' Has. lia.
  - apply awr_ok_nil. }
rename ms into msC. rename mat into matC. rename HFr into HFrC. clear HF HG.
(* what run 2 kept *)
assert (KEEP2a : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 200 <= a < mf + 208) ->
aview SEGS (w_H W3) (ms_mem msB) a = aview SEGS (w_H W3) memh a).
{ intros a Ha Hw. apply (kept_of_frame E2 _ (w_H W3) memh (ms_mem msB)
  (fun x => mf + 200 <= x < mf + 208) HFrB); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold jl2_ssB, jl2_regB, windows in Hin. cbn in Hin.
  destruct Hin as [Eq|[]]; injection Eq as <- <- <-.
  cbn [base_val] in Hr. rewrite U9_2 in Hr. clear - Hr. lia. }
assert (KEEP2b : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 200 <= a < mf + 208) ->
aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) (ms_mem msB) a).
{ intros a Ha Hw. apply (kept_of_frame E2 _ (w_H W3) (ms_mem msB) (ms_mem msC)
  (fun x => mf + 200 <= x < mf + 208) HFrC); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold windows in Hin. cbn in Hin.
  destruct Hin as [Eq|[]]; injection Eq as <- <- <-.
  cbn [base_val] in Hr. rewrite U9_2 in Hr. clear - Hr. lia. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf + 200 <= a < mf + 208) ->
aview SEGS (w_H W3) (ms_mem msC) a = aview SEGS (w_H W3) memh a)
by (intros a Ha Hw; rewrite (KEEP2b a Ha Hw); exact (KEEP2a a Ha Hw)).
assert (HVc : jl2_vals g pos mf nm tk dp W3 (ms_mem msC)).
{ apply (jl2_vals_moved g pos mf nm tk dp W3 memh W3 (ms_mem msC) Hmfhi HSF8 Hlen Hwok); [|exact HVh].
  intros a Ha. destruct (AREA_RNG a Ha) as [Hr Hw]. exact (KEEP2 a Hr Hw). }
assert (Hdpbc : bytes_at8 W3 (ms_mem msC) (SFa g pos + V_dp) (j_dp2 (e_pl g) ++ j_lit_in)).
{ unfold bytes_at8 in *. apply (garr8_frame SEGS _ _ _ _ Hdpbh). intros x Hx.
  rewrite length_map, length_app in Hx. unfold V_dp in Hx.
  apply (mbyte_of_aview SEGS). apply KEEP2.
  - clear - Hx HSF0h HSF1h C1 HDP2len HL2b HLI. lia.
  - clear - Hx HSF0h HSF1h Hmf0 C1 HDP2len HL2b HLI. lia. }
pose proof HVc as (V16c & V64c & V192c & V168c & Vrac & Vs0c & SS9c & SS18c & SS19c & SS20c & SS21c &
SS22c & SS23c & SS24c & SS25c & SS26c & SS27c & Vflagc & Hinbc & V152c & V184c & V144c & V128c & V120c &
V176c & V160c & V112c & Hidc & Hbufsc & Hshnmc & Hshdpc & Hnmbc).
pose proof HJh as (HARc & _ & _ & _ & _ & _ & Hnevc & _ & _ & _ & _ & _ & _ & Hpresc & _).
(* the registers at the call *)
prreg HS2p (1%bv : bv 5) C1r. prreg HS2p (2%bv : bv 5) C2r. prreg HS2p (3%bv : bv 5) C3r.
prreg HS2p (4%bv : bv 5) C4r. prreg HS2p (10%bv : bv 5) C10. prreg HS2p (11%bv : bv 5) C11.
prreg HS2p (12%bv : bv 5) C12. prreg HS2p (13%bv : bv 5) C13.
rewrite (EE2 2%nat 2%bv eq_refl), Rsph in C2r.
rewrite (EE2 3%nat 3%bv eq_refl), Rgph in C3r.
rewrite (EE2 4%nat 4%bv eq_refl), Rtph in C4r.
rewrite (EE2 26%nat 26%bv eq_refl), R26h in C10.
rewrite U9_2 in C11. rewrite EX2 in C12.
assert (Usp : spZ (ms_regs msC) = mf).
{ unfold spZ. rewrite C2r. unfold w64. apply unsigned_lit_small.
  clear - Hmf0 H47 Hmfb Hshi C1. lia. }
(* the counter the run stored at mf+200 *)
pose proof (st_ok_region_nth E2 _ _ 0 _ HS2p eq_refl) as RGc.
cbn [ms_mem restrict] in RGc.
assert (VN2 : val_mem SEGS (rd W3 (ms_mem msC)) (mf + M_n2) 8 n2).
{ unfold M_n2.
  apply (field_of_region E2 _ 9%nat mf _ 160 208 200 208 200 8%N (SLit n2) n2 RGc U9_2).
  - cbn [YP09.r_chunks]. repeat (first [apply in_eq | apply in_cons]).
  - cbn [sv_denot]. reflexivity.
  - clear - Hn2b. lia.
  - lia. }
assert (HDL : put_dec_c.dec_len (SlotModel.t_out (e_pl g)) 1 = j_d2 (e_pl g)) by reflexivity.
(* the two ranges put_dec writes *)
assert (Hstk : forall q n, mf <= q -> 0 < n -> q + n + 96 <= e_sp0 g ->
twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyh Sh [(4, pos)] W3 (ms_mem msC) mf q n /\
tsrc_ok W3 (ms_mem msC) mf q n).
{ intros q n Hq Hn Hqn.
  pose proof (al_zshadow _ _ LAWS lyh Sh W3 (ms_mem msC) _ (ly_stk_lo lyh, ly_stk_hi lyh - ly_stk_lo lyh)
  HARc ltac:(left; reflexivity)) as HZ.
  cbn [fst snd] in HZ.
  destruct (jl2_zsh (aview SEGS (w_H W3) (ms_mem msC)) (ly_stk_lo lyh)
  (ly_stk_hi lyh - ly_stk_lo lyh) q n HZ ltac:(clear - Hceilh C1 Esloh; lia)
  ltac:(clear - Hq Hmfb Hsloh HSTK' Has Esloh; lia) Hn ltac:(clear - Hqn Hshih Eshih; lia)) as [HRA HHV].
  assert (Hw : forall a, q <= a < q + n -> awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g))
  (ablocks B lyh Sh) lyh [(4, pos)] a)
  by (intros a Ha; left; clear - Ha Hq Hqn Hmfb HSTK' Has; lia).
  split.
  - intros a Ha.
    destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJh (Hw a Ha)) as [Hp Ho].
    split; [exact (Hw a Ha)|]. split; [exact Hp|]. split; [exact Ho|].
    unfold ESTACK. clear - Ha Hq. lia.
  - split.
    { intros a Ha. split.
      - apply aview_some_of_apresent. apply Hpresc. clear - Ha Hq Hqn Hmfb HSTK' Has. lia.
      - unfold ESTACK. clear - Ha Hq. lia. }
    split; [exact HRA|]. split; [exact HHV|].
    split; [right; clear - Hq Hqn Hmf0 C1 C3 C4 Hshih H47h; lia|].
    clear - Hq Hqn Hmf0 C1 Hshih H47h. lia. }
assert (Hfrm : forall q n, SFa g pos <= q -> 0 < n -> q + n <= SFa g pos + 1024 ->
twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyh Sh [(4, pos)] W3 (ms_mem msC) mf q n).
{ intros q n Hq Hn Hqn a Ha.
  assert (Hw : awr_byte LLVMF_STK (e_sp0 g) [] (ablocks B (e_ly g) (e_S g)) (ablocks B lyh Sh) lyh
  [(4, pos)] a).
  { right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFah, HFB. clear - Ha Hq Hqn. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJh Hw) as [Hp Ho].
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho|].
  unfold ESTACK. clear - Ha Hq Hqn HSF0h HSF1h Hmf0 C1. lia. }
destruct (Hstk (mf + M_n2) 8 ltac:(unfold M_n2; clear; lia) ltac:(lia)
ltac:(unfold M_n2; clear - Hmfb; lia)) as [WRP SRP].
assert (WRF : twr_ok B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) lyh Sh [(4, pos)] W3 (ms_mem msC) mf
(SFa g pos + V_dp + n2) (put_dec_c.dec_len (SlotModel.t_out (e_pl g)) 1)).
{ rewrite HDL. apply Hfrm; unfold V_dp; clear - Hn2b Hd2; lia. }
assert (SRF : tsrc_ok W3 (ms_mem msC) mf (SFa g pos + V_dp + n2)
(put_dec_c.dec_len (SlotModel.t_out (e_pl g)) 1)).
{ rewrite HDL. split.
  { intros a Ha. split.
    - apply aview_some_of_apresent.
      destruct (Hfrm (SFa g pos + V_dp + n2) (j_d2 (e_pl g))
      ltac:(unfold V_dp; clear - Hn2b; lia) ltac:(clear - Hd2; lia)
      ltac:(unfold V_dp; clear - Hn2b Hd2; lia) a Ha) as (_ & Hp & _). exact Hp.
    - unfold ESTACK. clear - Ha HSF0h HSF1h Hmf0 C1 Hn2b Hd2. unfold V_dp in *. lia. }
  split.
  { apply (jl2_ra_of_zs (aview SEGS (w_H W3) (ms_mem msC)) (SFa g pos + V_dp) N_dp
    (SFa g pos + V_dp + n2) (j_d2 (e_pl g)) Hshdpc).
    - clear - HSF8. unfold V_dp. Z.div_mod_to_equations. lia.
    - reflexivity.
    - clear - Hn2b. lia.
    - unfold N_dp. clear - Hn2b Hd2. lia.
    - clear - Hd2. lia. }
  split.
  { apply (shadow_hull_vis_of_frame _ _ LAWS lyh Sh W3 (ms_mem msC) _ 4 pos _ _ HARc Hin4h).
    - rewrite EFah. clear - Hn2b. unfold V_dp. lia.
    - rewrite EFah, HFB. clear - Hn2b Hd2. unfold V_dp. lia.
    - clear - Hd2. lia. }
  split.
  { apply (amem_range_sub_app (SFa g pos) 1024 (SFa g pos + V_dp + n2) (j_d2 (e_pl g)) Happ);
    [clear - HSF1h; lia | clear - Hn2b; unfold V_dp; lia | clear - Hn2b Hd2; unfold V_dp; lia
    | clear - Hd2; lia]. }
  split; [clear - HSF0h Hn2b; unfold V_dp; lia | clear - HSF1h Hn2b Hd2 C1; unfold V_dp; lia]. }
(* ---- the call put_dec (b = &exp_dp, p = mf+200, n = n2, v = t_out, mn = 1) at 0x81ff8 ---- *)
pmkst HS2p. rewrite (PSIG IB_put_dec AF_put_dec eq_refl).
eapply SRr_bind.
{ eapply (HPD LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
  lyh Sh W3 (ms_mem msC) _ _ (ms_regs msC) (SFa g pos + V_dp) (mf + M_n2) n2
  (SlotModel.t_out (e_pl g)) 1 HJh).
  - rewrite C1r. apply ret_ok_codeptr_v; [clear; lia | reflexivity].
  - unfold raZ. rewrite C1r, unsigned_lit_small by (clear - HBASE; lia). clear - HBLO. lia.
  - exact C3r.
  - exact C4r.
  - exact C10.
  - rewrite C11. unfold w64, M_n2. reflexivity.
  - rewrite C12. unfold w64. rewrite unsigned_lit_small by (clear - Hto; lia).
    apply Z.mod_small. clear - Hto. lia.
  - left. rewrite C12. unfold w64. rewrite unsigned_lit_small by (clear - Hto; lia).
    clear - Hto. lia.
  - rewrite C13. reflexivity.
  - clear; lia.
  - rewrite Usp. exact Hmf32h.
  - rewrite Usp. unfold put_dec.PUT_DEC_STK, ESTACK. clear - Hmfb HSTK' Has. lia.
  - rewrite Usp. clear - Hmfb. lia.
  - rewrite Hfrsh. cbn [length]. clear; lia.
  - unfold M_n2. exact (jl2_m8 mf Hmf32h).
  - clear - HSF0h. unfold V_dp. lia.
  - clear - Hn2b. lia.
  - exact VN2.
  - rewrite Usp. exact WRP.
  - rewrite Usp. exact WRF.
  - rewrite Usp. exact SRP.
  - rewrite Usp. exact SRF.
  - right. rewrite HDL. clear - HSF0h HSF1h Hmf0 C1 Hn2b Hd2. unfold V_dp, M_n2. lia.
  - left. rewrite Usp. unfold M_n2. clear; lia.
  - right. rewrite Usp, HDL. unfold put_dec.PUT_DEC_STK, ESTACK.
    clear - HSF0h HSF1h Hmf0 C1 Hn2b Hd2. unfold V_dp. lia.
  - unfold put_dec.EV_PUT_DEC. clear - Hnevc Hnev0 Hkh HEV. lia. }
(* ---- back at +0x1888, with put_dec's post ---- *)
cbv beta.
intros W4 c4 Hwle4 (lyr & Sr & regsr & memr & mdr & -> & HJr & HPr & Hfrsr & Hblkr & HKEPT & HGARR & HVALN).
unfold put_dec.EV_PUT_DEC in HJr. rewrite Z.add_0_r in HJr.
rewrite Usp in HKEPT.
assert (HDLn : n2 + put_dec_c.dec_len (SlotModel.t_out (e_pl g)) 1 = j_L3 (e_pl g))
by (rewrite HDL; unfold j_L3; clear - En2; lia).
rewrite HDLn in HVALN.
(* what the call kept *)
assert (KEEPC : forall a, jl2_area g pos mf nm tk dp a ->
aview SEGS (w_H W4) memr a = aview SEGS (w_H W3) (ms_mem msC) a).
{ apply (jl2_call_keep LAWS HSTK g pos mf nm tk dp lyh Sh W3 (ms_mem msC) _ _ W4 memr _
  HJh Hfrsh Hmfbh Hblh HPRE HKEPT).
  intros a [Hx | Hx]; [left; exact Hx|].
  right. rewrite HDL in Hx. clear - Hx Hn2b Hd2. unfold V_dp, N_dp in *. lia. }
assert (KEEPDP : forall a, SFa g pos + V_dp <= a < SFa g pos + V_dp + n2 ->
aview SEGS (w_H W4) memr a = aview SEGS (w_H W3) (ms_mem msC) a).
{ intros a Ha. pose proof HKEPT as (_ & _ & _ & K4 & _).
  apply (K4 4 pos a Hin4h).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFah, HFB.
    clear - Ha Hn2b. unfold V_dp in *. lia.
  - intros [Hx | Hx].
    + clear - Ha Hx HSF0h HSF1h Hmf0 C1 Hn2b. unfold V_dp, M_n2 in *. lia.
    + clear - Ha Hx. lia. }
assert (HVr : jl2_vals g pos mf nm tk dp W4 memr).
{ apply (jl2_vals_moved g pos mf nm tk dp W3 (ms_mem msC) W4 memr Hmfhi HSF8 Hlen Hwok);
  [exact KEEPC | exact HVc]. }
assert (HDP3r : bytes_at8 W4 memr (SFa g pos + V_dp) (j_dp3 (e_pl g))).
{ unfold bytes_at8.
  replace (j_dp3 (e_pl g))
  with ((j_dp2 (e_pl g) ++ j_lit_in) ++ IdentSpec.DEC (SlotModel.t_out (e_pl g)) 1)
  by (unfold j_dp3; rewrite app_assoc; reflexivity).
  rewrite map_app.
  apply (proj2 (garr8_app SEGS (rd W4 memr) (SFa g pos + V_dp) _ _)). split.
  - apply (garr8_frame SEGS _ _ _ _ Hdpbc). intros x Hx. apply (mbyte_of_aview SEGS).
    apply KEEPDP. rewrite length_map, length_app in Hx. clear - Hx HDP2len HLI En2. lia.
  - replace (Z.of_nat (length (map (fun b : byte => bv_unsigned b) (j_dp2 (e_pl g) ++ j_lit_in))))
    with n2 by (rewrite length_map, length_app; clear - HDP2len HLI En2; lia).
    exact HGARR. }
(* the registers the call preserved *)
assert (RPR : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regsr r = getr (ms_regs msC) r)
by (intros r Hc; exact (jl2_pres _ _ r HPr Hc)).
assert (RKC : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv;
27%bv] -> getr (ms_regs msC) r = getr regsh r).
{ eapply (regs_kept_of_st_ok SEGS E2 _ (restrict (w_H W3) msC) regsh _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS2p HAE2).
  vm_compute. reflexivity. }
assert (RF : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv;
27%bv] -> acallee_saved (bv_unsigned r) -> getr regsr r = getr regsh r)
by (intros r Hin Hc; rewrite (RPR r Hc); exact (RKC r Hin)).
(* ---- run 3: +0x1888 .. +0x188c (the shadow base reloaded) ---- *)
pose proof HVr as (V16r & V64r & V192r & V168r & Vrar & Vs0r & SS9r & SS18r & SS19r & SS20r & SS21r &
SS22r & SS23r & SS24r & SS25r & SS26r & SS27r & Vflagr & Hinbr & V152r & V184r & V144r & V128r & V120r &
V176r & V160r & V112r & Hidr & Hbufsr & Hshnmr & Hshdpr & Hnmbr).
remember (Eimg (Ereg regsr [])) as E3 eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3) by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3 n = getr regsr r)
by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (ER3 : regs_ok E3 sr_atoms regsr) by (rewrite HE3; apply regs_ok_Eimg_Ereg).
assert (HAE3 : env_agree 32 (Ereg regsr []) E3)
by (rewrite HE3; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE3.
assert (U9_3 : bv_unsigned (ew E3 9) = mf).
{ rewrite (EE3 9%nat 9%bv eq_refl), (RF 9%bv ltac:(cbn; tauto) ltac:(do 4 right; left; reflexivity)),
  Rs1h. apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
rewrite C1r.
assert (HS3 : st_ok_pi SEGS VAL E3 (jl2_ssC 0x1888)
(restrict (w_H W4) (mkst regsr (Z_to_bv 64 (BASE + 0x1888)) memr (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold jl2_ssC. apply pa_entry_st_ok_full.
  - exact ER3.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil.
    unfold jl2_regC, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9_3. split; [clear - Hmf0 C1; lia|].
    split; [clear - Hmfb H47 Hshi; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E3 _ mf 168 8 (SLit SHADOW_OFF) SHADOW_OFF);
    [cbn [sv_denot]; reflexivity | unfold SHADOW_OFF; clear; lia | lia | exact V168r].
  - apply pairwise_disjoint_of_extents. unfold jl2_regC, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_to_sh RUNTOP HS3 HJr 0x188c.
{ apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jl2_regC]; lia | apply awr_ok_nil]. }
rename ms into msF. rename mat into matF. rename HFr into HFrF. clear HF HG.
assert (EQR3 : mrestrict (w_H W4) (ms_mem msF) = mrestrict (w_H W4) memr).
{ apply functional_extensionality. intros xq. apply HFrF.
  intros (r & Hin & Hr). cbn [ss_mem jl2_ssC In] in Hin. destruct Hin as [<-|[]].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi jl2_regC] in Hr. clear - Hr. lia. }
assert (EQV3 : aview SEGS (w_H W4) (ms_mem msF) = aview SEGS (w_H W4) memr)
by (unfold aview; rewrite EQR3; reflexivity).
assert (HVf : jl2_vals g pos mf nm tk dp W4 (ms_mem msF)).
{ apply (jl2_vals_moved g pos mf nm tk dp W4 memr W4 (ms_mem msF) Hmfhi HSF8 Hlen Hwok);
  [intros a _; rewrite EQV3; reflexivity | exact HVr]. }
unfold bytes_at8 in HDP3r. rewrite <- EQR3 in HDP3r.
rewrite <- EQR3 in HVALN.
pose proof HVf as (V16f & V64f & V192f & V168f & Vraf & Vs0f & SS9f & SS18f & SS19f & SS20f & SS21f &
SS22f & SS23f & SS24f & SS25f & SS26f & SS27f & Vflagf & Hinbf & V152f & V184f & V144f & V128f & V120f &
V176f & V160f & V112f & Hidf & Hbufsf & Hshnmf & Hshdpf & Hnmbf).
assert (RKF : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv;
27%bv] -> getr (ms_regs msF) r = getr regsr r).
{ eapply (regs_kept_of_st_ok_pi E3 _ (restrict (w_H W4) msF) regsr _
  [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS3 HAE3).
  vm_compute. reflexivity. }
assert (RFF : forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 21%bv; 23%bv; 24%bv; 25%bv; 26%bv;
27%bv] -> acallee_saved (bv_unsigned r) -> getr (ms_regs msF) r = getr regsh r)
by (intros r Hin Hc; rewrite (RKF r Hin); exact (RF r Hin Hc)).
prreg HS3 (6%bv : bv 5) F6.
destruct (jl2_nil_io _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJr) as [Efd Efs].
destruct (jl2_meter MTL HMT0 (e_S g) Sh Sr (4 * Z.of_nat (m_nrec g) + 7) MLEh MOKh) as [MLEr MOKr].
(* ---- the cut jc8 at +0x188c ---- *)
apply SRr_ret. unfold jc8, acut. pmkst HS3.
exists lyr, Sr, (ms_regs msF), (ms_mem msF). eexists.
split; [reflexivity|]. split; [exact HJr|].
split; [rewrite Hfrsr; exact Hfrsh|]. split; [exact Hkh|].
split; [exact MLEr|]. split; [exact MOKr|].
split.
{ unfold ecommon.
  split; [rewrite (RFF 2%bv ltac:(cbn; tauto) ltac:(left; reflexivity)); exact Rsph|].
  split; [rewrite (RFF 9%bv ltac:(cbn; tauto) ltac:(do 4 right; left; reflexivity)); exact Rs1h|].
  split; [rewrite (RFF 8%bv ltac:(cbn; tauto) ltac:(do 3 right; left; reflexivity)); exact Rs0h|].
  split; [exact Hmfbh|]. split; [exact Hmf32h|].
  split; [rewrite (RFF 3%bv ltac:(cbn; tauto) ltac:(right; left; reflexivity)); exact Rgph|].
  split; [rewrite (RFF 4%bv ltac:(cbn; tauto) ltac:(do 2 right; left; reflexivity)); exact Rtph|].
  split; [exact V16f|]. split; [exact V64f|]. split; [exact V192f|]. split; [exact V168f|].
  split; [exact Vraf|]. split; [exact Vs0f|]. split; [exact SS9f|]. split; [exact SS18f|].
  split; [exact SS19f|]. split; [exact SS20f|]. split; [exact SS21f|]. split; [exact SS22f|].
  split; [exact SS23f|]. split; [exact SS24f|]. split; [exact SS25f|]. split; [exact SS26f|].
  split; [exact SS27f|]. split; [exact Vflagf|]. split; [exact HPRE|].
  split; [intros fd; rewrite Efd; reflexivity|].
  split; [exact Efs|]. exact Hinbf. }
split.
{ unfold jkeep.
  split; [split; [rewrite Hblkr; exact (proj1 Hblh) | exact (proj2 Hblh)]|].
  split; [unfold sh_reg; rewrite (RFF 23%bv ltac:(cbn; tauto)
  ltac:(do 5 right; split; apply Z.leb_le; reflexivity)); exact Rs7h|].
  split; [rewrite (RFF 24%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity));
  exact R24h|].
  split; [rewrite (RFF 21%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity));
  exact R21h|].
  split; [exact V152f|]. split; [exact V184f|]. split; [exact V144f|]. split; [exact V128f|].
  split; [exact V120f|]. split; [exact V176f|]. split; [exact V160f|]. split; [exact V112f|].
  split; [exact Hidf|]. exact Hbufsf. }
split.
{ unfold jdp_regs.
  split; [rewrite F6; reflexivity|].
  split; [rewrite (RFF 18%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity));
  exact R18h|].
  split; [rewrite (RFF 25%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity));
  exact R25h|].
  rewrite (RFF 26%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity)); exact R26h. }
split.
{ unfold jdp_mem. split; [exact Hshnmf|]. split; [exact Hshdpf|]. exact HDP3r. }
split; [rewrite (RFF 27%bv ltac:(cbn; tauto) ltac:(do 5 right; split; apply Z.leb_le; reflexivity));
exact R27h|].
split; [exact HVALN|]. exact Hnmbf.
Qed.

Check (j_lit2_glue : j_lit2_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS G).

End c.
End b.
End a.
