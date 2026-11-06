(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACik.v:90-93, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v; 574 of its 694 lines of code are new or changed and 535 lines of the source are left out. *)
(* Segment J of LLVMFuzzerTestOneInput's build-B walk (fuzz_identity.asan-ubsan), the piece +0x16b8 .. +0x1748
   (0x81e2c .. 0x81ebc): j_dpcpy_glue_stmt of lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v, from the cut jc5 to
   the cut jc6 around the copy loop j_dpcpy_stmt (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_loops_stmt.v).

   The run +0x16b8 .. +0x16e8 (0x81e2c .. 0x81e5c):
     0x81e2c, 0x81e30  UBSan bound: branch to the trap 0x82610 when x27 = n_ln > 31;
     0x81e34           UBSan bound: branch to the trap when x22 = ~&exp_nm < n_ln;
     0x81e38, 0x81e3c  a0 := x25 + x27 = &exp_nm + n_ln; store the byte 0 there (no shadow test);
     0x81e40           a5 := exp_nm[0] (no shadow test);
     0x81e44           a2 := the word at mf+200, the display counter (jc5: 0);
     0x81e48           x18 := ~x26 = ~&exp_dp;
     0x81e4c           branch to 0x81ebc when a5 = 0;
     0x81e50 .. 0x81e58  a0 := &exp_nm + 1, a3 := -1, a4 := &exp_nm; then the loop head 0x81e5c.
   SlotModel bounds n_ln to 1 .. 21 and exp_nm[0] to 1 .. 255 (no byte of n_EXP_NM is NUL), so the symbolic state
   carries them as atom facts and the engine decides all three branches. The store address &exp_nm + n_ln is the
   atom 32 by an alias fact; its byte is the one write window of the run. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef StrcmpDef MemchrDef SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import LLVMFuzzerTestOneInput_seg_J_pre.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* The frame's 64-byte alignment and the shadow cells need lia's division handling, which YC4b turns off. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
(* Membership in a literal list, by walking it. (`cbn; tauto` would also unfold the elements and may close a
   sub-goal with a section variable, which then becomes an argument of the closed lemma.) *)
Local Ltac jin := cbn [In]; repeat (first [left; reflexivity | right]).

(* ---- facts of the plain model and of the words, independent of the program ----------------------------- *)
Lemma jdg_lnot_u : forall x, 0 <= x < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 (Z.lnot x)) = 2 ^ 64 - 1 - x.
Proof.
intros x Hx. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
assert (Hl : Z.lnot x = - x - 1) by (unfold Z.lnot; lia). rewrite Hl.
replace (- x - 1) with ((2 ^ 64 - 1 - x) + (-1) * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma jdg_lxor_ones : forall w, 0 <= w < 2 ^ 64 -> Z.lxor w (Z.ones 64) = (Z.lnot w) mod 2 ^ 64.
Proof.
intros w Hw. rewrite <- Z.land_ones by lia.
apply Z.bits_inj'. intros i Hi. rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
destruct (Z.lt_ge_cases i 64).
- rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
- rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
  destruct (Z.eq_dec w 0) as [->|]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia].
Qed.

(* 0x81e48 `not s2,s10` (xori with -1). *)
Lemma jdg_xor_m1 : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_XOR (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = Z_to_bv 64 (Z.lnot x).
Proof.
intros x Hx. rewrite zalu64_sound. apply Z_to_bv64_eq_mod. unfold zalu64, zcanon, M64. cbn [zalu_raw].
rewrite (Z.mod_small x) by lia.
replace ((-1) mod 2 ^ 64) with (Z.ones 64) by (vm_compute; reflexivity).
rewrite (jdg_lxor_ones x Hx). rewrite !Z.mod_mod by lia. reflexivity.
Qed.

Lemma jdg_nth0 : forall (l : list byte), (0 < length l)%nat ->
  nth 0 (map (fun b : byte => bv_unsigned b) l) 0 = bv_unsigned (nth 0 l (RcIdentModel.zb 0)).
Proof. intros l Hl. destruct l as [|x r]; [cbn in Hl; lia | reflexivity]. Qed.

Lemma jdg_b0_range : forall (l : list byte), (0 < length l)%nat -> ~ In (RcIdentModel.zb 0) l ->
  1 <= bv_unsigned (nth 0 l (RcIdentModel.zb 0)) <= 255.
Proof.
intros l Hl Hn. destruct l as [|x r]; [cbn in Hl; lia|]. cbn [nth].
pose proof (bv_unsigned_in_range 8 x) as Hr. change (bv_modulus 8) with 256 in Hr.
assert (Hx : bv_unsigned x <> 0).
{ intros H0. apply Hn. left. apply bv_eq. rewrite H0. vm_compute. reflexivity. }
lia.
Qed.

(* A byte string followed by the NUL the run stores. *)
Lemma jdg_garr8_snoc : forall segs (m : word -> option byte) a (l : list byte),
  garr8 segs m a (map (fun b : byte => bv_unsigned b) l) ->
  val_mem segs m (a + Z.of_nat (length l)) 1 0 ->
  garr8 segs m a (map (fun b : byte => bv_unsigned b) (l ++ [RcIdentModel.zb 0])).
Proof.
intros segs m a l Hg Hv j Hj.
rewrite length_map, length_app in Hj. cbn [length] in Hj.
rewrite map_app.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt | Hge].
- rewrite app_nth1 by (rewrite length_map; exact Hlt). apply Hg. rewrite length_map. exact Hlt.
- assert (Hj' : j = length l) by lia. subst j.
  rewrite app_nth2 by (rewrite length_map; lia). rewrite length_map, Nat.sub_diag. cbn [nth map].
  replace (bv_unsigned (RcIdentModel.zb 0)) with 0 by (vm_compute; reflexivity).
  split; [exact Hv | lia].
Qed.

(* The token is the name without its first dash: one byte shorter when it has one (SlotModel.n_lt). *)
Lemma jdg_tok_len : forall l : list byte,
  Z.of_nat (length (SlotModel.tok_go true l)) = Z.of_nat (length l) /\
  Z.of_nat (length (SlotModel.tok_go false l)) = Z.of_nat (length l) - (if SlotModel.has_dash l then 1 else 0).
Proof.
induction l as [|b r [IHt IHf]]; [split; reflexivity|].
assert (Hd : SlotModel.has_dash (b :: r) = (RcIdentModel.bz b =? 45) || SlotModel.has_dash r) by reflexivity.
rewrite Hd.
cbn [SlotModel.tok_go negb andb length].
split.
- clear IHf Hd. lia.
- clear Hd. revert IHt IHf.
  match goal with |- context [if (?x =? 45) then _ else _] => destruct (x =? 45) end;
  destruct (SlotModel.has_dash r); cbn [orb length]; intros IHt IHf; lia.
Qed.

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
#[local] Notation JKEEP := (jkeep B).
#[local] Notation EPRE := (e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation ECOMMON := (ecommon B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC5 := (jc5 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
#[local] Notation JC6 := (jc6 B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).
Variable G : list (Z * Z).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

(* ---- the symbolic state at +0x16b8 ---------------------------------------------------------------------- *)
(* Region 0: the display counter mf+200 (base s1, atom 9), read-only, holding 0. Region 1: exp_nm[0] (base s9,
   atom 25), read-only, holding atom 33. Region 2: the byte exp_nm[n_ln] (atom 32), writable. The atom facts are
   the ranges of x22 = ~&exp_nm, of x27 = n_ln and of exp_nm[0]; the alias names the store address. *)
Definition jdg_mf : YP09.region := YP09.mkRegion (Some 9%nat) 200 208 200 200 [YP09.mkChunk 200 (CVal 8 (SLit 0))].
Definition jdg_nm0 : YP09.region := YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition jdg_nul : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition jdg_facts : facts :=
mkFacts [(22%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (27%nat, mkAF 1 21 0); (33%nat, mkAF 1 255 0)] []
[(SAlu ALU_ADD (SOff 25 0) (SOff 27 0), SOff 32 0)].
Definition jdg_ss : sstate := mkSS 0x16b8 sr_atoms [jdg_mf; jdg_nm0; jdg_nul] None jdg_facts.
(* The environment: the registers, then atom 32 = &exp_nm + n_ln and atom 33 = exp_nm[0]. *)
Definition jdg_E (regs : bvmap 5 word) (wa b0 : Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) [wa; b0])).
Definition jdg_b0 (inp : list byte) : Z := bv_unsigned (nth 0 (SlotModel.n_EXP_NM inp) (RcIdentModel.zb 0)).

(* The cut at the loop head 0x81e5c, as j_dpcpy_stmt states it. *)
Definition jdg_head (g : ectx) (pos mf nm tk dp i : Z) : world SEGS -> config -> Prop :=
ACUT g pos mf (4 * Z.of_nat (m_nrec g) + 7) (BASE + 0x16e8)
(fun ly2 S2 W2 regs2 mem2 md2 =>
jkeep B g pos mf nm tk dp ly2 S2 W2 regs2 mem2 /\
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
getr regs2 15 = w64 (bv_unsigned (nth (Z.to_nat i) (SlotModel.n_EXP_NM (e_pl g)) (RcIdentModel.zb 0)))).

(* ---- moving a fact over the run's one written byte ----------------------------------------------------- *)
Definition jdg_keep (W : world SEGS) (m m' : word -> option byte) (Wa : Z) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> a <> Wa -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.

Lemma jdg_vm : forall (W : world SEGS) m m' Wa a (n : nat) v, jdg_keep W m m' Wa ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (a + Z.of_nat n <= Wa \/ Wa < a) ->
val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m') a n v.
Proof.
intros W m m' Wa a n v K H0 H1 H2 Hv.
apply (val_mem_moved SEGS (w_H W) (w_H W) m m' a a n v); [|exact Hv].
intros k Hk. apply K; clear - H0 H1 H2 Hk; lia.
Qed.

Lemma jdg_ga : forall (W : world SEGS) m m' Wa a l, jdg_keep W m m' Wa ->
0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (a + Z.of_nat (length l) <= Wa \/ Wa < a) ->
garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m') a l.
Proof.
intros W m m' Wa a l K H0 H1 H2 Hg.
apply (j_garr8_moved SEGS (w_H W) (w_H W) m m' a l); [|exact Hg].
intros k Hk. apply K; clear - H0 H1 H2 Hk; lia.
Qed.

Lemma jdg_shz : forall (W : world SEGS) m m' Wa SF off n, jdg_keep W m m' Wa ->
SF mod 64 = 0 -> 0 <= off -> off mod 8 = 0 -> 0 <= n -> off + n <= 1024 ->
0 <= shadow_addr SF -> shadow_addr SF + 128 <= 2 ^ 64 ->
(Wa < shadow_addr SF \/ shadow_addr SF + 128 <= Wa) ->
sh_zero W m (SF + off) n -> sh_zero W m' (SF + off) n.
Proof.
intros W m m' Wa SF off n K H64 Ho0 Ho8 Hn0 Hon Hs0 Hs1 Hws Hz. unfold sh_zero in *.
apply (j_zero_shadow_moved (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') SHADOW_OFF (SF + off) n); [|exact Hz].
intros i Hi. assert (Esh : shadow_addr SF = SHADOW_OFF + SF / 8) by reflexivity.
rewrite Esh in Hs0, Hs1, Hws. unfold shadow_of_addr.
apply K; clear - H64 Ho0 Ho8 Hn0 Hon Hs0 Hs1 Hws Hi; lia.
Qed.

Lemma jdg_shb : forall (W : world SEGS) m m' Wa SF off n, jdg_keep W m m' Wa ->
SF mod 64 = 0 -> 0 <= off -> off mod 8 = 0 -> 0 <= n -> off + n <= 1024 ->
0 <= shadow_addr SF -> shadow_addr SF + 128 <= 2 ^ 64 ->
(Wa < shadow_addr SF \/ shadow_addr SF + 128 <= Wa) ->
sh_blk W m (SF + off) n -> sh_blk W m' (SF + off) n.
Proof.
intros W m m' Wa SF off n K H64 Ho0 Ho8 Hn0 Hon Hs0 Hs1 Hws Hz. unfold sh_blk in *.
apply (j_block_shadow_moved (aview SEGS (w_H W) m) (aview SEGS (w_H W) m') SHADOW_OFF (SF + off) n); [|exact Hz].
intros i Hi. assert (Esh : shadow_addr SF = SHADOW_OFF + SF / 8) by reflexivity.
rewrite Esh in Hs0, Hs1, Hws. unfold shadow_of_addr.
apply K; clear - H64 Ho0 Ho8 Hn0 Hon Hs0 Hs1 Hws Hi; lia.
Qed.

(* ---- where things are ---------------------------------------------------------------------------------- *)
(* The entry's class-4 frame (lib/B/Prog/LLVMFuzzerTestOneInput_seg_J_pre.v j_geo, with the allocator laws as a
   premise). *)
Lemma jdg_geo : AR_laws SEGS B -> forall (g : ectx) pos k ly2 S2 (W2 : world SEGS) mem2 md2,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] ->
frame_addr ly2 4 pos = SFa g pos /\
4096 <= SFa g pos /\ SFa g pos + 1024 <= alloc_ceiling /\ SFa g pos mod 64 = 0 /\
0 <= shadow_addr (SFa g pos) /\ shadow_addr (SFa g pos) + 128 <= alloc_ceiling /\
(SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos).
Proof.
intros LAWS g pos k ly2 S2 W2 mem2 md2 HJ Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (EFa : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
destruct (frame_al64 SEGS B ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF64 & _ & _).
rewrite EFa in HSF0, HSF1, HSFapp, HSF64. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = SHADOW_OFF + SFa g pos / 8) by reflexivity.
split; [exact EFa|]. split; [exact HSF0|]. split; [exact HSF1|]. split; [exact HSF64|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
split; [clear - Esh HSF0 HSF1 C1; unfold SHADOW_OFF in Esh; lia|].
clear - Esh HSF0 HSF1 HSFapp C1.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
destruct HSFapp as (_ & [Hlo | [Hhi1 Hhi2]]); [left | right]; lia.
Qed.

(* The input block is a heap block (or empty), so it is beside the frame. *)
Lemma jdg_inp : AR_laws SEGS B -> forall (g : ectx) pos ly2 S2 (W2 : world SEGS) mem2 md2 hs,
AR SEGS B ly2 S2 W2 mem2 md2 -> In (4, pos) (frames S2) -> frame_addr ly2 4 pos = SFa g pos ->
hblocks B g ly2 S2 hs -> EPRE g ->
e_n g = 0 \/ (4096 <= e_p g /\ e_p g + e_n g <= alloc_ceiling /\
(e_p g + e_n g <= SFa g pos \/ SFa g pos + 1024 <= e_p g)).
Proof.
intros LAWS g pos ly2 S2 W2 mem2 md2 hs HAR Hin4 EFa (Hperm & _) HPRE.
pose proof HPRE as (_ & _ & _ & _ & Hinp & _).
destruct Hinp as [[Hn0 _] | [Hn Hine]]; [left; exact Hn0|right].
assert (I2 : In (e_p g, e_n g) (ablocks B ly2 S2))
by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; exact Hine).
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ HAR I2) as (_ & Hp4 & Hpce & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 _ _ 4 pos HAR I2 Hin4) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa in Hd.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in Hd.
pose proof (req_size_pos (e_n g) ltac:(clear - Hn; lia)) as [_ Hrq].
clear - Hp4 Hpce Hd Hrq. lia.
Qed.

(* A heap block's bytes: the block is beside the frame and the run wrote one byte of the frame. *)
Lemma jdg_blk_bytes : AR_laws SEGS B -> forall ly2 S2 (W2 : world SEGS) mem2 md2 mem3 pos SF Wa b m (L : list byte),
AR SEGS B ly2 S2 W2 mem2 md2 -> In (4, pos) (frames S2) -> frame_addr ly2 4 pos = SF ->
In (b, m) (ablocks B ly2 S2) -> 0 <= m -> Z.of_nat (length L) <= m ->
SF <= Wa < SF + 1024 -> jdg_keep W2 mem2 mem3 Wa ->
bytes_at8 W2 mem2 b L -> bytes_at8 W2 mem3 b L.
Proof.
intros LAWS ly2 S2 W2 mem2 md2 mem3 pos SF Wa b m L HAR Hin4 EFa Hin Hm Hlen HW K Hb.
destruct (al_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m HAR Hin) as (_ & Hb4 & Hbce & _).
pose proof (sep_block_frame SEGS B LAWS ly2 S2 W2 mem2 md2 b m 4 pos HAR Hin Hin4) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFa in Hd.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity. rewrite HFB in Hd.
pose proof (req_size_pos m Hm) as [_ Hrq].
pose proof asan_consts as (C1 & _).
unfold bytes_at8 in *. apply (jdg_ga W2 mem2 mem3 Wa b _ K).
- clear - Hb4. lia.
- rewrite length_map. clear - Hlen Hrq Hbce C1. lia.
- rewrite length_map. clear - Hlen Hrq Hd HW. lia.
- exact Hb.
Qed.

(* ecommon over the run: its registers are kept and its bytes are not the written one. *)
Lemma jdg_ecommon : forall (g : ectx) pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 regs3 mem3 md3 Wa,
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling ->
alloc_ceiling <= e_sp0 g -> e_sp0 g <= 2 ^ 47 ->
SFa g pos <= Wa < SFa g pos + 560 ->
(e_n g = 0 \/ (0 <= e_p g /\ e_p g + e_n g <= 2 ^ 64 /\ (e_p g + e_n g <= Wa \/ Wa < e_p g))) ->
jdg_keep W2 mem2 mem3 Wa ->
(forall r, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv] -> getr regs3 r = getr regs2 r) ->
m_fds md3 = m_fds md2 -> m_fs md3 = m_fs md2 ->
ECOMMON g pos mf ly2 S2 W2 regs3 mem3 md3.
Proof.
intros g pos mf ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 Wa HC HSF0 HSF1 Hsp0lo Hsp0hi HW HINP K RK Efds Efs.
pose proof asan_consts as (C1 & _).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & V16 & V64 & V192 & V168 & Vra & Vs0 &
V24 & V32 & V40 & V48 & V56 & V64b & V72 & V80 & V88 & V96 & V104 & Vflag & HPRE & Hfds & Hfs & Hinb).
assert (VS : forall a (n : nat) v, e_sp0 g - 336 <= a -> a + Z.of_nat n <= e_sp0 g ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv. apply (jdg_vm W2 mem2 mem3 Wa a n v K).
  - clear - H1 Hsp0lo C1. lia.
  - clear - H2 Hsp0hi. lia.
  - right. clear - H1 Hsp0lo HSF1 HW. lia.
  - exact Hv. }
unfold ecommon.
split; [rewrite (RK 2%bv ltac:(jin)); exact Rsp|].
split; [rewrite (RK 9%bv ltac:(jin)); exact Rs1|].
split; [rewrite (RK 8%bv ltac:(jin)); exact Rs0|].
split; [exact Hmfb|]. split; [exact Hmf32|].
split; [rewrite (RK 3%bv ltac:(jin)); exact Rgp|].
split; [rewrite (RK 4%bv ltac:(jin)); exact Rtp|].
split; [apply VS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V16]|].
split; [apply VS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V64]|].
split; [apply VS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V192]|].
split; [apply VS; [clear - Hmfb; lia | clear - Hmfb; lia | exact V168]|].
split; [apply VS; [clear; lia | clear; lia | exact Vra]|].
split; [apply VS; [clear; lia | clear; lia | exact Vs0]|].
split; [apply VS; [clear; lia | clear; lia | exact V24]|].
split; [apply VS; [clear; lia | clear; lia | exact V32]|].
split; [apply VS; [clear; lia | clear; lia | exact V40]|].
split; [apply VS; [clear; lia | clear; lia | exact V48]|].
split; [apply VS; [clear; lia | clear; lia | exact V56]|].
split; [apply VS; [clear; lia | clear; lia | exact V64b]|].
split; [apply VS; [clear; lia | clear; lia | exact V72]|].
split; [apply VS; [clear; lia | clear; lia | exact V80]|].
split; [apply VS; [clear; lia | clear; lia | exact V88]|].
split; [apply VS; [clear; lia | clear; lia | exact V96]|].
split; [apply VS; [clear; lia | clear; lia | exact V104]|].
split.
{ apply (jdg_vm W2 mem2 mem3 Wa _ 8 _ K); [clear - HSF0; lia | clear - HSF1 C1; lia | right; clear - HW; lia | exact Vflag]. }
split; [exact HPRE|].
split; [intros fd; rewrite Efds; apply Hfds|].
split; [rewrite Efs; exact Hfs|].
pose proof HPRE as (_ & _ & _ & _ & _ & Hlen & _).
destruct HINP as [Hn0 | (Hp0 & Hp1 & Hp2)].
- unfold bytes_at8. intros j Hj. rewrite length_map in Hj. clear - Hj Hlen Hn0. lia.
- unfold bytes_at8 in *. apply (jdg_ga W2 mem2 mem3 Wa _ _ K).
  + exact Hp0.
  + rewrite length_map, <- Hlen. exact Hp1.
  + rewrite length_map, <- Hlen. exact Hp2.
  + exact Hinb.
Qed.

(* jkeep over the run. *)
Lemma jdg_jkeep : AR_laws SEGS B -> forall (g : ectx) pos mf nm tk dp ly2 S2 (W2 : world SEGS) regs2 mem2 md2
regs3 mem3 Wa,
AR SEGS B ly2 S2 W2 mem2 md2 -> In (4, pos) (frames S2) -> frame_addr ly2 4 pos = SFa g pos ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs2 mem2 ->
4096 <= SFa g pos -> SFa g pos + 1024 <= alloc_ceiling -> SFa g pos mod 64 = 0 ->
0 <= shadow_addr (SFa g pos) -> shadow_addr (SFa g pos) + 128 <= alloc_ceiling ->
(SFa g pos + 1024 <= shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= SFa g pos) ->
alloc_ceiling - 336 <= mf -> mf + 192 <= 2 ^ 47 ->
SFa g pos + V_nm < Wa < SFa g pos + 560 ->
jdg_keep W2 mem2 mem3 Wa ->
(forall r, In r [21%bv; 23%bv; 24%bv] -> getr regs3 r = getr regs2 r) ->
JKEEP g pos mf nm tk dp ly2 S2 W2 regs3 mem3.
Proof.
intros LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 regs3 mem3 Wa HAR Hin4 EFa HK
HSF0 HSF1 HSF64 Hsh0 Hsh1 Hsfsh Hmf0 Hmf1 HW K RK.
pose proof asan_consts as (C1 & _).
assert (HVnm : V_nm = 528) by reflexivity.
destruct HK as (Hbl & Rs7 & R24 & R21 & V152 & V184 & V144 & V128 & V120 & V176 & V160 & V112 & Hid & Hbufs).
assert (VM : forall a (n : nat) v, mf + 112 <= a -> a + Z.of_nat n <= mf + 192 ->
val_mem SEGS (rd W2 mem2) a n v -> val_mem SEGS (rd W2 mem3) a n v).
{ intros a n v H1 H2 Hv. apply (jdg_vm W2 mem2 mem3 Wa a n v K).
  - clear - H1 Hmf0 C1. lia.
  - clear - H2 Hmf1. lia.
  - right. clear - H1 Hmf0 HSF1 HW. lia.
  - exact Hv. }
assert (Hws : Wa < shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= Wa)
by (clear - Hsfsh HW HVnm; lia).
assert (Hsh2 : shadow_addr (SFa g pos) + 128 <= 2 ^ 64) by (clear - Hsh1 C1; lia).
unfold jkeep.
split; [exact Hbl|].
split; [unfold sh_reg in *; rewrite (RK 23%bv ltac:(jin)); exact Rs7|].
split; [rewrite (RK 24%bv ltac:(jin)); exact R24|].
split; [rewrite (RK 21%bv ltac:(jin)); exact R21|].
split; [apply VM; [clear; lia | clear; lia | exact V152]|].
split; [apply VM; [clear; lia | clear; lia | exact V184]|].
split; [apply VM; [clear; lia | clear; lia | exact V144]|].
split; [apply VM; [clear; lia | clear; lia | exact V128]|].
split; [apply VM; [clear; lia | clear; lia | exact V120]|].
split; [apply VM; [clear; lia | clear; lia | exact V176]|].
split; [apply VM; [clear; lia | clear; lia | exact V160]|].
split; [apply VM; [clear; lia | clear; lia | exact V112]|].
split.
{ destruct Hid as (Hidb & Hidz & Hidk). unfold id_at. split; [|split].
  - unfold bytes_at8 in *. apply (jdg_ga W2 mem2 mem3 Wa _ _ K).
    + unfold V_id. clear - HSF0. lia.
    + rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
      unfold V_id, RcIdentModel.ID_SIZE. clear - HSF1 C1. lia.
    + left. rewrite length_map. unfold m_id. rewrite SlotModel.rec_id_length.
      unfold V_id, RcIdentModel.ID_SIZE. clear - HW HVnm. lia.
    + exact Hidb.
  - apply (jdg_shz W2 mem2 mem3 Wa (SFa g pos) V_id N_id K HSF64); [clear; unfold V_id; lia | reflexivity
    | clear; unfold N_id; lia | clear; unfold V_id, N_id; lia | exact Hsh0 | exact Hsh2 | exact Hws | exact Hidz].
  - apply (jdg_shb W2 mem2 mem3 Wa (SFa g pos) V_id N_id K HSF64); [clear; unfold V_id; lia | reflexivity
    | clear; unfold N_id; lia | clear; unfold V_id, N_id; lia | exact Hsh0 | exact Hsh2 | exact Hws | exact Hidk]. }
intros Hr0. destruct (Hbufs Hr0) as (Bn & Bt & Bd).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_fits_r0 (e_pl g) Hr0) as (_ & Fn & Ft & Fd).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m2_caps (e_pl g)) as (Cn & Ct & Cd).
destruct Hbl as [Hperm _].
assert (IN : forall x, In x [(nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1);
(tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1); (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1)] ->
In x (ablocks B ly2 S2))
by (intros x Hx; apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; left; exact Hx).
assert (HW' : SFa g pos <= Wa < SFa g pos + 1024) by (clear - HW HVnm; lia).
split; [|split].
- apply (jdg_blk_bytes LAWS ly2 S2 W2 mem2 md2 mem3 pos (SFa g pos) Wa nm (Z.max (SlotModel.t_cap_name (e_pl g)) 1) _
    HAR Hin4 EFa (IN (nm, Z.max (SlotModel.t_cap_name (e_pl g)) 1) ltac:(jin))).
  + clear. lia.
  + rewrite length_app. cbn [length]. unfold SlotModel.n_ln in Fn. clear - Fn. lia.
  + exact HW'.
  + exact K.
  + exact Bn.
- apply (jdg_blk_bytes LAWS ly2 S2 W2 mem2 md2 mem3 pos (SFa g pos) Wa tk (Z.max (SlotModel.t_cap_tok (e_pl g)) 1) _
    HAR Hin4 EFa (IN (tk, Z.max (SlotModel.t_cap_tok (e_pl g)) 1) ltac:(jin))).
  + clear. lia.
  + rewrite length_app. cbn [length]. unfold SlotModel.n_TK, SlotModel.TOK.
    destruct (jdg_tok_len (SlotModel.n_EXP_NM (e_pl g))) as [_ Htk].
    unfold SlotModel.n_lt, SlotModel.n_ln in Ft. clear - Ft Htk.
    revert Ft Htk. destruct (SlotModel.has_dash (SlotModel.n_EXP_NM (e_pl g))); intros Ft Htk; lia.
  + exact HW'.
  + exact K.
  + exact Bt.
- apply (jdg_blk_bytes LAWS ly2 S2 W2 mem2 md2 mem3 pos (SFa g pos) Wa dp (Z.max (SlotModel.t_cap_disp (e_pl g)) 1) _
    HAR Hin4 EFa (IN (dp, Z.max (SlotModel.t_cap_disp (e_pl g)) 1) ltac:(jin))).
  + clear. lia.
  + rewrite length_app. cbn [length]. unfold SlotModel.n_ld in Fd. clear - Fd. lia.
  + exact HW'.
  + exact K.
  + exact Bd.
Qed.

(* ---- the symbolic state at +0x16b8 holds ---------------------------------------------------------------- *)
Lemma jdg_entry : AR_laws SEGS B -> forall (g : ectx) pos mf ly2 S2 (W2 : world SEGS) regs2 mem2 md2 k Wa b0,
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly2 S2 W2 mem2 md2 k ->
frames S2 = [(4, pos)] ->
ECOMMON g pos mf ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 22 = w64 (Z.lnot (SFa g pos + V_nm)) ->
getr regs2 25 = w64 (SFa g pos + V_nm) ->
getr regs2 27 = w64 (SlotModel.n_ln (e_pl g)) ->
val_mem SEGS (rd W2 mem2) (mf + M_n2) 8 0 ->
bytes_at8 W2 mem2 (SFa g pos + V_nm) (SlotModel.n_EXP_NM (e_pl g)) ->
SlotModel.n_wok (e_pl g) = true ->
Wa = SFa g pos + V_nm + SlotModel.n_ln (e_pl g) -> b0 = jdg_b0 (e_pl g) ->
st_ok_pi SEGS VAL (jdg_E regs2 Wa b0) jdg_ss
(restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x16b8)) mem2 (seg_rom SEGS))).
Proof.
intros LAWS g pos mf ly2 S2 W2 regs2 mem2 md2 k Wa b0 HJ Hfrs HC R22 R25 R27 V200 Bnm Hwok HWa Hb0e.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
destruct (jdg_geo LAWS g pos k ly2 S2 W2 mem2 md2 HJ Hfrs) as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as Hln.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_EXP_NM_nonul (e_pl g) Hwok) as Hnul.
assert (Hlen : Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) = SlotModel.n_ln (e_pl g)) by reflexivity.
assert (HVnm : V_nm = 528) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (L0 : (0 < length (SlotModel.n_EXP_NM (e_pl g)))%nat) by (clear - Hlen Hln; lia).
assert (Hb0 : 1 <= b0 <= 255) by (rewrite Hb0e; unfold jdg_b0; exact (jdg_b0_range _ L0 Hnul)).
assert (V0 : val_mem SEGS (rd W2 mem2) (SFa g pos + V_nm) 1 b0).
{ assert (L0' : (0 < length (map (fun b : byte => bv_unsigned b) (SlotModel.n_EXP_NM (e_pl g))))%nat)
  by (rewrite length_map; exact L0).
  destruct (Bnm 0%nat L0') as [Hv _]. cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
  rewrite (jdg_nth0 _ L0) in Hv. rewrite Hb0e. exact Hv. }
rewrite restrict_mkst_fx.
set (E := jdg_E regs2 Wa b0).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs2 (map (Z_to_bv 64) [Wa; b0])) n)
by (intros n Hn; subst E; unfold jdg_E; apply Eimg_low; exact Hn).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; subst E; unfold jdg_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 Wa)
by (rewrite EL by (clear; unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0)
by (rewrite EL by (clear; unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (E25 : ew E 25 = Z_to_bv 64 (SFa g pos + V_nm)) by (rewrite (EE 25%nat 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = Z_to_bv 64 (SlotModel.n_ln (e_pl g))) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (Hmf0 : alloc_ceiling - 336 <= mf) by (clear - Hmfb Hceil Hslo HSTK0; lia).
assert (Hmf1 : mf + 320 <= 2 ^ 47) by (clear - Hmfb Hshi H47; lia).
assert (U9 : bv_unsigned (ew E 9) = mf)
by (rewrite (EE 9%nat 9%bv eq_refl), Rs1; apply unsigned_lit_small; clear - Hmf0 Hmf1 C1; lia).
assert (U22 : bv_unsigned (ew E 22) = 2 ^ 64 - 1 - (SFa g pos + V_nm)).
{ rewrite (EE 22%nat 22%bv eq_refl), R22. apply jdg_lnot_u. clear - HSF0 HSF1 C1 HVnm. lia. }
assert (U25 : bv_unsigned (ew E 25) = SFa g pos + V_nm)
by (rewrite E25; apply unsigned_lit_small; clear - HSF0 HSF1 C1 HVnm; lia).
assert (U27 : bv_unsigned (ew E 27) = SlotModel.n_ln (e_pl g))
by (rewrite E27; apply unsigned_lit_small; clear - Hln; lia).
assert (U32 : bv_unsigned (ew E 32) = Wa)
by (rewrite E32; apply unsigned_lit_small; clear - HWa HSF0 HSF1 C1 HVnm Hln; lia).
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite E33; apply unsigned_lit_small; clear - Hb0; lia).
assert (RO0 : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) jdg_mf).
{ unfold jdg_mf, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf1; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ mf 200 8 (SLit 0) 0); [cbn [sv_denot]; reflexivity | clear; lia | clear; lia | exact V200]. }
assert (RO1 : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) jdg_nm0).
{ unfold jdg_nm0, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U25. split; [clear - HSF0 HVnm; lia|]. split; [clear - HSF1 C1 HVnm; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (SFa g pos + V_nm) 0 1 (SOff 33 0) b0);
  [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | clear - Hb0; lia | clear; lia |].
  rewrite Z.add_0_r. exact V0. }
assert (RO2 : YP09.region_ok SEGS E (mrestrict (w_H W2) mem2) jdg_nul).
{ unfold jdg_nul, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U32. split; [clear - HWa HSF0 HVnm Hln; lia|]. split; [clear - HWa HSF1 C1 HVnm Hln; lia|].
  split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS).
  apply (proj1 (awr_byte_present SEGS B LAWS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
  [(4, pos)] ly2 S2 W2 mem2 md2 k (Wa + o) HJ ltac:(
  right; right; right; exists 4, pos; split; [left; reflexivity|]; left;
  unfold in_zr; cbn [fst snd]; rewrite EFa, HFB; clear - Ho HWa HVnm Hln; lia))). }
assert (A22 : afact_ok E 22 (mkAF (2 ^ 63) (2 ^ 64 - 1) 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22, Z.pow_0_r, Z.mod_1_r.
  clear - HSF0 HSF1 C1 HVnm. lia. }
assert (A27 : afact_ok E 27 (mkAF 1 21 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U27, Z.pow_0_r, Z.mod_1_r. clear - Hln. lia. }
assert (A33 : afact_ok E 33 (mkAF 1 255 0)).
{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, Z.pow_0_r, Z.mod_1_r. clear - Hb0. lia. }
assert (AL : sv_denot E (SAlu ALU_ADD (SOff 25 0) (SOff 27 0)) = sv_denot E (SOff 32 0)).
{ apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E 25 (SFa g pos + V_nm) E25) by (clear - HSF0 HSF1 C1 HVnm; lia).
  rewrite (U_atom E 27 (SlotModel.n_ln (e_pl g)) E27) by (clear - Hln; lia).
  rewrite (U_atom E 32 Wa E32) by (clear - HWa HSF0 HSF1 C1 HVnm Hln; lia).
  unfold zcanon, M64. rewrite Z.mod_small by (clear - HWa HSF0 HSF1 C1 HVnm Hln; lia).
  rewrite HWa. reflexivity. }
unfold jdg_ss. apply pa_entry_st_ok_full.
- subst E. unfold jdg_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; assumption.
- apply pairwise_disjoint_of_extents. unfold jdg_mf, jdg_nm0, jdg_nul, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U25, U32.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  clear - HWa HSF0 HSF1 HVnm Hln Hmf0 C1. repeat split; lia.
- unfold facts_ok, jdg_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [split; [exact A22 | split; [exact A27 | split; [exact A33 | exact I]]]|].
  split; [exact I|]. split; [exact AL | exact I].
Qed.

(* ---- +0x16b8 .. the loop head +0x16e8 ------------------------------------------------------------------- *)
Lemma jdg_run : AR_laws SEGS B -> forall (g : ectx) pos mf nm tk dp W2 c2,
JC5 g pos mf nm tk dp W2 c2 -> SlotModel.n_wok (e_pl g) = true ->
SRr SEGS W2 c2 (jdg_head g pos mf nm tk dp 0).
Proof.
intros LAWS g pos mf nm tk dp W2 c2 Hstart Hwok.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HP as (HK & R6 & R22 & R25 & R26 & R27 & SZn & SZd & V200 & Bnm).
pose proof (SRr_run_to_pi_AJ B LAWS) as RUNTOP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & _ & _ & _ & _ & _ & _ &
_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRE & _).
pose proof HJ as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof Hstatic as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
destruct (jdg_geo LAWS g pos _ ly2 S2 W2 mem2 md2 HJ Hfrs) as (EFa & HSF0 & HSF1 & HSF64 & Hsh0 & Hsh1 & Hsfsh).
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_n_ln_le (e_pl g) Hwok) as Hln.
pose proof (LLVMFuzzerTestOneInput_seg_J_model.m1_EXP_NM_nonul (e_pl g) Hwok) as Hnul.
assert (Hlen : Z.of_nat (length (SlotModel.n_EXP_NM (e_pl g))) = SlotModel.n_ln (e_pl g)) by reflexivity.
assert (HVnm : V_nm = 528) by reflexivity. assert (HVdp : V_dp = 592) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
pose (Wa0 := SFa g pos + V_nm + SlotModel.n_ln (e_pl g)).
assert (HWa : Wa0 = SFa g pos + V_nm + SlotModel.n_ln (e_pl g)) by reflexivity.
clearbody Wa0. rename Wa0 into Wa.
pose (b00 := jdg_b0 (e_pl g)).
assert (Hb0e : b00 = jdg_b0 (e_pl g)) by reflexivity.
clearbody b00. rename b00 into b0.
pose proof (jdg_entry LAWS g pos mf ly2 S2 W2 regs2 mem2 md2 _ Wa b0 HJ Hfrs HC R22 R25 R27 V200 Bnm Hwok HWa Hb0e)
as HS.
remember (jdg_E regs2 Wa b0) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; unfold jdg_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r)
by (intros n r Hn; rewrite HE; unfold jdg_E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 Wa)
by (rewrite HE; unfold jdg_E; rewrite Eimg_low by (clear; unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 b0)
by (rewrite HE; unfold jdg_E; rewrite Eimg_low by (clear; unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 1)).
assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) [Wa; b0])) E)
by (rewrite HE; split; [intros n Hn; unfold jdg_E; apply Eimg_low; clear - Hn; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (U32 : bv_unsigned (ew E 32) = Wa)
by (rewrite E32; apply unsigned_lit_small; clear - HWa HSF0 HSF1 C1 HVnm Hln; lia).
assert (U25 : bv_unsigned (ew E 25) = SFa g pos + V_nm)
by (rewrite (EE 25%nat 25%bv eq_refl), R25; apply unsigned_lit_small; clear - HSF0 HSF1 C1 HVnm; lia).
unfold cfg_at. change (w64 (BASE + 0x16b8)) with (Z_to_bv 64 (BASE + 0x16b8)).
(* the run: its one write is the byte at atom 32, a byte of the entry's own frame *)
paj_run_to_sh RUNTOP HS HJ 0x16e8.
{ unfold jdg_ss. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jdg_mf]; clear; lia|].
  apply awr_ok_cons_ro; [cbn [YP09.r_whi YP09.r_wlo jdg_nm0]; clear; lia|].
  eapply awr_ok_cons_gen.
  - reflexivity.
  - exact U32.
  - intros a Ha. cbn [jdg_nul YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right. exists 4, pos. split; [left; reflexivity|]. left.
    unfold in_zr; cbn [fst snd]. rewrite EFa, HFB. clear - Ha HWa HVnm Hln. lia.
  - apply awr_ok_nil. }
cbn [ms_mem mkst] in HFr.
assert (KEEP : jdg_keep W2 mem2 (ms_mem ms) Wa).
{ unfold jdg_keep. intros a Ha Hw.
  apply (kept_of_frame E _ (w_H W2) mem2 (ms_mem ms) (fun x => x = Wa) HFr); [|exact Ha|exact Hw].
  intros bb wlo whi aa Hin Hr. unfold jdg_ss, jdg_mf, jdg_nm0, jdg_nul, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-; cbn [base_val] in Hr.
  - clear - Hr. lia.
  - clear - Hr. lia.
  - rewrite U32 in Hr. cbv beta. clear - Hr. lia. }
(* the byte the run stored *)
pose proof (st_ok_pi_region_nth _ _ _ 2 _ HS eq_refl) as RG2. cbn [ms_mem restrict] in RG2.
assert (VW : val_mem SEGS (rd W2 (ms_mem ms)) (Wa + 0) 1 0).
{ apply (field_of_region E _ 32%nat Wa _ 0 1 0 1 0 1%N (SLit 0) 0 RG2 U32);
  [jin | cbn [sv_denot]; reflexivity | clear; lia | clear; lia]. }
clear RG2.
(* the registers at +0x16e8 *)
assert (RK : forall r, In r [2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] ->
getr (ms_regs ms) r = getr regs2 r)
by (eapply (regs_kept_of_st_ok_pi E _ (restrict (w_H W2) ms) regs2 _
[2%bv; 3%bv; 4%bv; 6%bv; 8%bv; 9%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv] HS HAE);
vm_compute; reflexivity).
prreg HS (10%bv : bv 5) Q10. prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
prreg HS (14%bv : bv 5) Q14. prreg HS (15%bv : bv 5) Q15. prreg HS (18%bv : bv 5) Q18.
pose proof (jdg_inp LAWS g pos ly2 S2 W2 mem2 md2 _ HAR2 Hin4 EFa (proj1 HK) HPRE) as HINP0.
assert (HINP : e_n g = 0 \/ (0 <= e_p g /\ e_p g + e_n g <= 2 ^ 64 /\ (e_p g + e_n g <= Wa \/ Wa < e_p g))).
{ destruct HINP0 as [H0 | (H1 & H2 & H3)]; [left; exact H0 | right].
  clear - H1 H2 H3 HWa Hln HVnm HSF1 C1. lia. }
clear HINP0.
(* ---- the cut at the loop head ---- *)
apply SRr_ret.
unfold jdg_head, acut. pmkst HS.
exists ly2, S2, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|].
split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact MLE|]. split; [exact MOK|].
split.
{ apply (jdg_ecommon g pos mf ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms)
  (with_vm_backing (m_vm_lazy md2) mat md2) Wa HC HSF0 HSF1).
  - clear - Hceil Hslo HSTK0. lia.
  - clear - Hshi H47. lia.
  - clear - HWa Hln HVnm. lia.
  - exact HINP.
  - exact KEEP.
  - intros r Hr. apply RK. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; jin.
  - apply j_wvb_fds.
  - apply j_wvb_fs. }
split.
{ apply (jdg_jkeep LAWS g pos mf nm tk dp ly2 S2 W2 regs2 mem2 md2 (ms_regs ms) (ms_mem ms) Wa HAR2 Hin4 EFa HK
  HSF0 HSF1 HSF64 Hsh0 Hsh1 Hsfsh).
  - clear - Hmfb Hceil Hslo HSTK0. lia.
  - clear - Hmfb Hshi H47. lia.
  - clear - HWa Hln HVnm. lia.
  - exact KEEP.
  - intros r Hr. apply RK. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[]]]]; jin. }
assert (Hws : Wa < shadow_addr (SFa g pos) \/ shadow_addr (SFa g pos) + 128 <= Wa)
by (clear - Hsfsh HWa HVnm Hln; lia).
assert (Hsh2 : shadow_addr (SFa g pos) + 128 <= 2 ^ 64) by (clear - Hsh1 C1; lia).
split.
{ unfold jdp_regs.
  split; [rewrite (RK 6%bv ltac:(jin)); exact R6|].
  split.
  { rewrite Q18, (EE 26%nat 26%bv eq_refl), R26. apply jdg_xor_m1.
    clear - HSF0 HSF1 C1 HVdp. lia. }
  split; [rewrite (RK 25%bv ltac:(jin)); exact R25|].
  rewrite (RK 26%bv ltac:(jin)); exact R26. }
split; [rewrite (RK 27%bv ltac:(jin)); exact R27|].
split.
{ apply (jdg_shz W2 mem2 (ms_mem ms) Wa (SFa g pos) V_nm N_nm KEEP HSF64); [clear; unfold V_nm; lia | reflexivity
  | clear; unfold N_nm; lia | clear; unfold V_nm, N_nm; lia | exact Hsh0 | exact Hsh2 | exact Hws | exact SZn]. }
split.
{ apply (jdg_shz W2 mem2 (ms_mem ms) Wa (SFa g pos) V_dp N_dp KEEP HSF64); [clear; unfold V_dp; lia | reflexivity
  | clear; unfold N_dp; lia | clear; unfold V_dp, N_dp; lia | exact Hsh0 | exact Hsh2 | exact Hws | exact SZd]. }
split.
{ unfold bytes_at8 in *. apply jdg_garr8_snoc.
  - apply (jdg_ga W2 mem2 (ms_mem ms) Wa _ _ KEEP).
    + clear - HSF0 HVnm. lia.
    + rewrite length_map, Hlen. clear - HSF1 C1 HVnm Hln. lia.
    + left. rewrite length_map, Hlen. clear - HWa. lia.
    + exact Bnm.
  - rewrite Hlen. replace (SFa g pos + V_nm + SlotModel.n_ln (e_pl g)) with (Wa + 0) by (clear - HWa; lia).
    exact VW. }
split.
{ unfold bytes_at8. change (Z.to_nat 0) with 0%nat. cbn [firstn map]. apply garr8_nil. }
split; [exact Hwok|].
split; [exact Hnul|].
split; [clear - Hln; lia|].
split.
{ rewrite Q10, U25. apply (f_equal (Z_to_bv 64)). clear. lia. }
split.
{ rewrite Q12. reflexivity. }
split.
{ rewrite Q13. apply Z_to_bv64_eq_mod. reflexivity. }
split.
{ rewrite Q14, (EE 25%nat 25%bv eq_refl), R25. apply (f_equal (Z_to_bv 64)). clear. lia. }
rewrite Q15, E33, Hb0e. reflexivity.
Qed.

(* ---- the piece ------------------------------------------------------------------------------------------ *)
Lemma j_dpcpy_glue : j_dpcpy_glue_stmt B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros LAWS HLOOP g pos mf nm tk dp W2 c2 Hstart Hwok.
eapply SRr_bind; [exact (jdg_run LAWS g pos mf nm tk dp W2 c2 Hstart Hwok)|].
intros W3 c3 _ Hh.
eapply SRr_mono; [exact (HLOOP LAWS g pos mf nm tk dp 0 W3 c3 Hh)|].
intros W4 c4 _ Hx.
destruct Hx as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hfrs4 & Hk4 & MLE4 & MOK4 & HC4 & HP4).
destruct HP4 as (HK4 & HR4 & R27 & R12 & SZn & SZd & Bnm & Bdp).
unfold jc6, acut.
exists ly4, S4, regs4, mem4, md4.
split; [reflexivity|]. split; [exact HJ4|]. split; [exact Hfrs4|]. split; [exact Hk4|].
split; [exact MLE4|]. split; [exact MOK4|]. split; [exact HC4|].
split; [exact HK4|]. split; [exact HR4|].
split; [exact (conj SZn (conj SZd Bdp))|].
split; [exact R27|]. split; [exact R12|]. exact Bnm.
Qed.

End c.
End b.
End a.
