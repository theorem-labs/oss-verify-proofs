(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_ctrl_build_grant_sweep on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8c.v, proofs/cgif/cgif_file_fuzzer/lib/A/AC8k.v, proofs/cgif/cgif_file_fuzzer/lib/A/AE2d.v, proofs/cgif/cgif_file_fuzzer/lib/UI2d.v. *)
(* reac_ctrl_build_grant_sweep (0x82d8c) on fuzz_grant's ASan build.

   It fills the caller's row buffer `uint8_t sweep[][34]` with the enrolment
   burst: the ACK head row (A_OBJ 20 = 0x211c0), the first channel's three
   head-amp rows, the MARK head row (A_OBJ 21 = 0x21220), the six group-B rows
   (A_OBJ 19 = 0x21040), then the remaining channels' head-amp rows. Each
   head-amp row is built by reac_ctrl_stamp_headamp into the 1492-byte scratch
   frame in this function's own machine stack (sp+36, no side-stack frame here)
   and its [16, 50) lifted into the row. The rows are Pau's
   SWEEP base w vals (lib/Prog/GrantSweepModel.v:62-64).

   It writes the caller's buffer, so the contract is in the caller-journal form
   (cgif lib/YC20.v:311-365). The contract itself is CtrlBuildGrantSweepSpec.v;
   tcj_kept, twr_ok and tsrc_ok are CtrlFinish.v's. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YG0t.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase
YC4b YC81 YC88 YCbw YCkd YC1g YC1h YC45 YC85 GrantFrame GrantRo.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1i ACj1 ACbf GrantACja GrantACjr.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
CtrlFinish CtrlLayBlockSpec CtrlStampHeadampSpec CtrlBuildGrantSweepSpec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require BgsTurn BgsLoop.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YImgTop.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* signed comparison and 32-bit add on literals, for the five refusals *)
Lemma signed_lit : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. assert (Hh : bv_half_modulus 64 = 2 ^ 63) by reflexivity. assert (Hm : bv_modulus 64 = 2 ^ 64) by reflexivity.
unfold bv_signed, bv_swrap. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite Hh, Hm.
rewrite Zplus_mod_idemp_l. rewrite Z.mod_small by lia. lia.
Qed.
Lemma blt_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.
Lemma bge_lit : forall a b, - 2 ^ 63 <= a < 2 ^ 63 -> - 2 ^ 63 <= b < 2 ^ 63 ->
branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !signed_lit by lia. reflexivity. Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma U_addw_big : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 2 ^ 31 <= x + y < 2 ^ 32 ->
2 ^ 32 <= U E (SAluw ALU_ADD a b).
Proof.
intros E a b x y Ha Hb Hx Hy Hxy. rewrite (U_of_S E (SAluw _ _ _)), S_SAluw. cbn [zalu_raw]. rewrite Ha, Hb.
rewrite (Z.mod_small x), (Z.mod_small y) by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
lia.
Qed.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
Context {RO : ro_below_ofl (@pa_segs _ grant_listing PI) (@pa_relro_lo _ grant_listing PI) (@pa_relro_hi _ grant_listing PI)}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* A_ACK, A_MARK, A_GB, TBGS_STK, EV_BGS, sweep_rows and bgs_ok are
   CtrlBuildGrantSweepSpec.v's, with the contract. *)
Definition BxS : sv := SOff 32 0.
Definition BspanS : Z * Z := (0x7fff8000, 0x7fff8000 + 2 ^ 44 - 1).
Definition ss_bgs : sstate :=
mkSS AF_reac_ctrl_build_grant_sweep sr_atoms [stack_region 1632; got_regionP; bcell_regionP 32] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF 0x7fff8000 0x7fff8000 0)] [] []).
Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
(* the one program function it calls *)
Hypothesis TSTAMP : tctrl_stamp_headamp_spec B (BASE + AF_reac_ctrl_stamp_headamp) pa_relro_lo pa_relro_hi.
(* ---- what the image holds: the three row tables -------------------------- *)
Hypothesis HACK : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_ACK)) HEAD_ACK34z.
Hypothesis HMARK : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_MARK)) HEAD_MARK34z.
Hypothesis HGB : forall (H : word -> bool) mem,
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
garr8 SEGS (mrestrict H mem) (VAL (A_OBJ A_GB)) GBallz.
Hypothesis HACK_rng : IMG_LO + 64 <= VAL (A_OBJ A_ACK) /\ VAL (A_OBJ A_ACK) + 34 + 64 <= IMG_HI.
Hypothesis HMARK_rng : IMG_LO + 64 <= VAL (A_OBJ A_MARK) /\ VAL (A_OBJ A_MARK) + 34 + 64 <= IMG_HI.
Hypothesis HGB_rng : IMG_LO + 64 <= VAL (A_OBJ A_GB) /\ VAL (A_OBJ A_GB) + 204 + 64 <= IMG_HI.
(* The three tables are registered globals whose last granule is partial (34,
   34 and 204 bytes), so the runtime marks their last granule with `sz mod 8`
   and no zero-shadow range covers it: they are read through GrantRo.v's
   `globs_marked` and not through `in_zs`. *)
Variable GL : list (Z * Z).
Hypothesis HGL : globs_marked SEGS B GL.
Hypothesis HIMGSH : img_shadow_vis SEGS B.
Hypothesis HIN_ACK : In (VAL (A_OBJ A_ACK), 34) GL.
Hypothesis HIN_MARK : In (VAL (A_OBJ A_MARK), 34) GL.
Hypothesis HIN_GB : In (VAL (A_OBJ A_GB), 204) GL.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
(* ---- the contract: CtrlBuildGrantSweepSpec.v ------------------------------ *)
#[local] Notation TBP := (tbgs_post B).
(* ---- the walk ------------------------------------------------------------- *)
(* The shadow of the stack is zero in every state: a range well inside the stack
   is marked usable and the shadow window around it is readable. *)
Lemma stk_shadow : forall ly2 S2 (W2 : world SEGS) mem2 md2 a n,
AR SEGS B ly2 S2 W2 mem2 md2 -> ly_stk_lo ly2 + 64 <= a -> a + n + 64 <= ly_stk_hi ly2 -> 0 < n ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W2) mem2) a n.
Proof.
intros ly2 S2 W2 mem2 md2 a n HAR Hlo Hhi Hn.
assert (Hin : In (ly_stk_lo ly2, ly_stk_hi ly2 - ly_stk_lo ly2) (zero_shadow_ranges B ly2)) by (left; reflexivity).
pose proof (al_zshadow _ _ LAWS ly2 S2 W2 mem2 md2 _ HAR Hin) as Z0. cbn [fst snd] in Z0.
destruct (zshadow_range_facts B ly2 S2 _ _ (proj1 HAR) Hin) as (A1 & A2 & A3 & _). cbn [fst snd] in A1, A2, A3.
set (lo := ly_stk_lo ly2) in *. set (hi := ly_stk_hi ly2) in *.
pose proof (Z.div_mod lo 8 ltac:(lia)) as Dlo.
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  assert (Hq : lo / 8 + 8 <= x / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hq2 : x / 8 < lo / 8 + (hi - lo) / 8) by (apply Z.div_lt_upper_bound; [lia|]; pose proof (Z.div_mod (hi - lo) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (hi - lo) 8 ltac:(lia)); lia).
  replace (shadow_of_addr SHADOW_OFF x) with (shadow_of_addr SHADOW_OFF lo + (x / 8 - lo / 8)) by (unfold shadow_of_addr; lia).
  apply Z0. lia.
- intros sh Hsh. unfold shadow_addr in Hsh.
  assert (Hq : lo / 8 + 8 <= a / 8) by (apply Z.div_le_lower_bound; lia).
  assert (Hq2 : (a + n - 1) / 8 + 8 <= lo / 8 + (hi - lo) / 8) by (pose proof (Z.div_mod (hi - lo) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (hi - lo) 8 ltac:(lia)); pose proof (Z.div_mod (a + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (a + n - 1) 8 ltac:(lia)); lia).
  pose proof (Z.mul_div_le (SHADOW_OFF + a / 8) 8 ltac:(lia)).
  pose proof (Z.mul_div_le (SHADOW_OFF + (a + n - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (SHADOW_OFF + a / 8) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (SHADOW_OFF + a / 8) 8 ltac:(lia)).
  replace sh with (shadow_of_addr SHADOW_OFF lo + (sh - SHADOW_OFF - lo / 8)) by (unfold shadow_of_addr; lia).
  rewrite Z0; [discriminate|]. unfold SHADOW_OFF in *. lia.
Qed.
Lemma tcj_kept_E : forall STK1 lyc1 Sc1 W1 m1 W2 m2 sp (E1 E2 : Z -> Prop),
tcj_kept B STK1 lyc1 Sc1 W1 m1 W2 m2 sp E1 -> (forall a, E1 a -> E2 a) -> tcj_kept B STK1 lyc1 Sc1 W1 m1 W2 m2 sp E2.
Proof.
intros STK1 lyc1 Sc1 W1 m1 W2 m2 sp E1 E2 (K1 & K2 & K3 & K4 & K5 & K6) HE.
split; [|split; [|split; [|split; [|split]]]]; try assumption.
- intros a Ha Hw Hn. apply K1; [exact Ha | exact Hw | intros X; exact (Hn (HE a X))].
- intros b m i Hin Hi Hn. apply (K2 b m i); [exact Hin | exact Hi | intros X; exact (Hn (HE _ X))].
- intros cid pos a Hin Hr Hn. apply (K4 cid pos a); [exact Hin | exact Hr | intros X; exact (Hn (HE a X))].
Qed.
(* ---- the call's fixed data ------------------------------------------------ *)
Section w.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
(W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
(s mx base w V : Z) (vals : list byte).
Hypothesis HJc : ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HROD : arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc).
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4 : 4096 <= raZ regs.
Hypothesis Hgp : getr regs 3 = w64 (as_gp B).
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis Hal16 : spZ regs mod 16 = 0.
Hypothesis Hwlo : sp0 - STK <= spZ regs - TBGS_STK.
Hypothesis Hwhi : spZ regs <= sp0.
Hypothesis Hfr8 : Z.of_nat (length (frames Sc)) <= 8.
Hypothesis H10 : getr regs 10 = w64 s.
Hypothesis H11 : getr regs 11 = w64 mx.
Hypothesis H12 : getr regs 12 = w64 base.
Hypothesis H13 : getr regs 13 = w64 w.
Hypothesis H14 : getr regs 14 = w64 V.
Hypothesis Rs : 0 <= s < 2 ^ 63.
Hypothesis Rmx : - 2 ^ 31 <= mx < 2 ^ 31.
Hypothesis Rbase : 0 <= base < 256.
Hypothesis Rw : - 2 ^ 31 <= w < 2 ^ 31.
Hypothesis RV : 0 <= V < 2 ^ 63.
Hypothesis HVALS : 1 <= w -> V <> 0 ->
length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals /\
garr8 SEGS (mrestrict (w_H W) memc) V (map bv_unsigned vals) /\
tsrc_ok W memc (spZ regs) V (3 * w) /\
afobj SEGS B lyc Sc W memc V (3 * w) /\
(spZ regs <= V \/ V + 3 * w <= spZ regs - TBGS_STK).
#[local] Notation SP := (spZ regs).
#[local] Notation FR := (spZ regs - 1632).
Definition RowsE (a : Z) : Prop := s <= a < s + 34 * sweep_rows w.
(* the caller's callee-saved registers, which the prologue stores at sp+1528.. *)
Definition SAVED : list (Z * nat) :=
[(1624, 1%nat); (1616, 8%nat); (1608, 9%nat); (1600, 18%nat); (1592, 19%nat); (1584, 20%nat); (1576, 21%nat);
(1568, 22%nat); (1560, 23%nat); (1552, 24%nat); (1544, 25%nat); (1536, 26%nat); (1528, 27%nat)].
Lemma saved_off : forall o r, In (o, r) SAVED -> 1528 <= o <= 1624.
Proof. intros o r Hin. unfold SAVED in Hin. repeat (destruct Hin as [Hq | Hin]; [inversion Hq; subst; lia |]). destruct Hin. Qed.
Definition bgs_saved (m : word -> option byte) : Prop :=
Forall (fun p => val_mem SEGS m (spZ regs - 1632 + fst p) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat (snd p)))))) SAVED.
(* What holds at each point between two calls. *)
Definition binv (W2 : world SEGS) (ly2 : alayout) (S2 : astate) (mem2 : word -> option byte) (md2 : Model) (rows : list Z) : Prop :=
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
tcj_kept B TBGS_STK lyc Sc W memc W2 mem2 (spZ regs) RowsE /\
bgs_saved (mrestrict (w_H W2) mem2) /\
garr8 SEGS (mrestrict (w_H W2) mem2) s rows /\ Z.of_nat (length rows) <= 34 * sweep_rows w /\
(exists f, S2 = set_fs f Sc).
Lemma m16 : forall a b c, a mod 16 = 0 -> b mod 16 = 0 -> c mod 16 = 0 -> (a - c - b) mod 16 = 0.
Proof.
intros a b c Ha Hb Hc. pose proof (Z.div_mod a 16 ltac:(lia)). pose proof (Z.div_mod b 16 ltac:(lia)). pose proof (Z.div_mod c 16 ltac:(lia)).
replace (a - c - b) with ((a / 16 - c / 16 - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma stk_bounds : alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + 6016 <= SP /\
SP <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\ sp0 mod 16 = 0 /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly.
Proof.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (TBGS_STK = 6016) as WS by reflexivity. lia.
Qed.
Lemma j_layout : forall W2 ly2 S2 mem2 md2 kk, ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 kk ->
ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly /\ (forall c p, frame_addr ly2 c p = frame_addr ly c p).
Proof.
intros W2 ly2 S2 mem2 md2 kk (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Eslo & Eshi & _).
split; [exact Eslo|]. split; [exact Eshi|]. intros c p. unfold frame_addr. rewrite EF. reflexivity.
Qed.
Lemma binv_layout : forall W2 ly2 S2 mem2 md2 rows, binv W2 ly2 S2 mem2 md2 rows ->
ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly /\ (forall c p, frame_addr ly2 c p = frame_addr ly c p).
Proof. intros W2 ly2 S2 mem2 md2 rows (HJ & _). exact (j_layout W2 ly2 S2 mem2 md2 k HJ). Qed.
Lemma lyc_layout : forall c p, frame_addr lyc c p = frame_addr ly c p.
Proof.
intros c p. pose proof HJc as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
unfold frame_addr. rewrite EF. reflexivity.
Qed.
(* this function's frame: zero shadow *)
Lemma frame_shadow : forall W2 ly2 S2 mem2 md2 rows a n, binv W2 ly2 S2 mem2 md2 rows ->
FR <= a -> a + n + 64 <= SP -> 0 < n ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF a n /\ shadow_hull_vis (aview SEGS (w_H W2) mem2) a n.
Proof.
intros W2 ly2 S2 mem2 md2 rows a n HI Ha Hn Hn0.
destruct (binv_layout _ _ _ _ _ _ HI) as (Elo & Ehi & _).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
eapply (stk_shadow ly2 S2 W2 mem2 md2); [exact (proj1 (proj1 HI)) | rewrite Elo; lia | rewrite Ehi; lia | exact Hn0].
Qed.
Definition SBV : Z := 0x7fff8000.
Definition ss_l1a : sstate := mkSS 0x2788 sr_atoms
[YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
(mkFacts [(25%nat, mkAF SBV SBV 0); (23%nat, mkAF 0 (2 ^ 47 - 2) 0); (27%nat, mkAF 0 (2 ^ 47 - 2) 0); (32%nat, mkAF 0 255 0)] [] []).
Definition BxL : sv := SOff 25 0.
Lemma len_GAz : forall ch p v, length (GAz ch p v) = 34%nat.
Proof. reflexivity. Qed.
Lemma nth_mapu : forall (l : list byte) j, nth j (map bv_unsigned l) 0 = bv_unsigned (nth j l (Z_to_bv 8 0)).
Proof. induction l as [|x l IH]; intros [|j]; cbn; try reflexivity. apply IH. Qed.
(* ---- the rows, as Pau's prefixB counts them ---------------------------------- *)
Definition prefixZ (c : Z) : list Z := map bv_unsigned (BgsLoop.prefixB base vals (Z.to_nat c)).
Lemma vz_range : forall j, 0 <= vz vals j < 256.
Proof. intros j. unfold vz. pose proof (bv_unsigned_in_range 8 (nth j vals (Z_to_bv 8 0))) as H. exact H. Qed.
Lemma gaz_row : forall c p, 0 <= c -> 0 <= p < 3 -> base + c < 256 ->
map bv_unsigned (ga_row base vals (Z.to_nat c) (Z.to_nat p)) = GAz (base + c) p (vz vals (Z.to_nat (3 * c + p))).
Proof.
intros c p Hc Hp Hb. rewrite <- BgsLoop.ga_row_eq by lia. unfold GA. apply map_unsigned_bl.
apply GA_bytes_range; [lia | lia | apply vz_range].
Qed.
Lemma prefix_step : forall c, 1 <= c -> base + c < 256 ->
((prefixZ c ++ GAz (base + c) 0 (vz vals (Z.to_nat (3 * c + 0)))) ++ GAz (base + c) 1 (vz vals (Z.to_nat (3 * c + 1))))
++ GAz (base + c) 2 (vz vals (Z.to_nat (3 * c + 2))) = prefixZ (c + 1).
Proof.
intros c Hc Hb. unfold prefixZ. replace (Z.to_nat (c + 1)) with (Datatypes.S (Z.to_nat c)) by lia.
rewrite <- BgsLoop.prefixB_step by lia. rewrite !map_app.
rewrite <- (gaz_row c 0), <- (gaz_row c 1), <- (gaz_row c 2) by lia. reflexivity.
Qed.
Lemma prefix_one : ((((HEAD_ACK34z ++ GAz base 0 (vz vals (Z.to_nat 0))) ++ GAz base 1 (vz vals (Z.to_nat 1)))
++ GAz base 2 (vz vals (Z.to_nat 2))) ++ HEAD_MARK34z) ++ GBallz = prefixZ 1.
Proof.
unfold prefixZ. change (Z.to_nat 1) with 1%nat. rewrite BgsLoop.prefixB1 by lia. rewrite !map_app.
unfold HEAD_ACK34, HEAD_MARK34, GBall, GA.
rewrite !map_unsigned_bl; [reflexivity | | | | | | ];
first [ apply GA_bytes_range; [lia | lia | apply vz_range] | unfold HEAD_ACK34z, HEAD_MARK34z, GBallz, GBz, gb_tail; cbn; repeat constructor; lia ].
Qed.
Lemma len_chans : forall l, length (concat (map (ga_chan base vals) l)) = (102 * length l)%nat.
Proof.
induction l as [|x l IH]; [reflexivity|]. cbn [map concat length]. rewrite length_app, IH.
assert (Hl : length (ga_chan base vals x) = 102%nat) by (unfold ga_chan, ga_row; rewrite !length_app, !length_GA; reflexivity).
rewrite Hl. lia.
Qed.
Lemma len_prefixZ : forall c, 1 <= c -> Z.of_nat (length (prefixZ c)) = 34 * (3 * c + 8).
Proof.
intros c Hc. unfold prefixZ, BgsLoop.prefixB. rewrite length_map, !length_app, len_chans, length_seq.
assert (L1 : length HEAD_ACK34 = 34%nat) by reflexivity.
assert (L2 : length (ga_chan base vals 0) = 102%nat) by (unfold ga_chan, ga_row; rewrite !length_app, !length_GA; reflexivity).
assert (L3 : length HEAD_MARK34 = 34%nat) by reflexivity. assert (L4 : length GBall = 204%nat) by reflexivity.
rewrite L1, L2, L3, L4. lia.
Qed.
Hypothesis HROWS : bgs_ok s V mx base w ->
amem_range s (34 * sweep_rows w) /\ s + 34 * sweep_rows w <= 2 ^ 47 - 8 /\
(forall x, s <= x < s + 34 * sweep_rows w -> ~ in_img SEGS x) /\
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) s (34 * sweep_rows w) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s (34 * sweep_rows w) /\
shadow_hull_vis (aview SEGS (w_H W) memc) s (34 * sweep_rows w) /\
(exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 34 * sweep_rows w <= b + req_size m) /\
(spZ regs <= s \/ s + 34 * sweep_rows w <= spZ regs - TBGS_STK) /\
(V + 3 * w <= s \/ s + 34 * sweep_rows w <= V).
Lemma ap_eq : forall (R1 R2 : bvmap 5 word) (r : bv 5), aregs_preserved R1 R2 -> acallee_saved (bv_unsigned r) -> getr R2 r = getr R1 r.
Proof. intros R1 R2 r HP Hr. pose proof (HP (bv_unsigned r) Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
Ltac nowin := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia |]); try destruct Hr.
Ltac mkshok HS SHOK := lazymatch type of HS with st_ok_pi _ _ ?Ex _ (restrict (w_H ?Wx) ?msx) =>
assert (SHOK : sh_ok SEGS BxL [] Ex (mrestrict (w_H Wx) (ms_mem msx))) by (apply Forall_nil) end.
Ltac rebase HS AG := let HEv := fresh "HEv" in rebaseE HS AG HEv; clear HEv;
try (lazymatch type of HS with st_ok_pi _ _ _ _ _ => repeat (match goal with H : sh_ok _ _ _ _ _ |- _ => clear H end);
let SH := fresh "SHOK" in mkshok HS SH; cbn [ms_mem mkst] in SH end).
Ltac upd_garr HGold HGnew :=
lazymatch type of HGold with garr8 _ (mrestrict ?Hh ?m0) ?q ?L =>
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
assert (HGnew : garr8 SEGS (mrestrict Hh (ms_mem m1)) q L) by
(apply (garr8_aview_kept SEGS Hh Hh m0 (ms_mem m1)); [intros a Ha; rewrite ?len_GAz in Ha; change (Z.of_nat 34) with 34 in Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin | exact HGold])
end end.
Ltac rfact AG E H :=
repeat (rewrite AG in H by lia);
repeat match type of H with context [ew E ?n] => match goal with En : ew E n = _ |- _ => rewrite En in H end end.
Ltac regs_close HS AG E :=
lazymatch goal with |- getr _ ?r = w64 _ =>
let H := fresh "Rx" in prreg HS r H; rfact AG E H; rewrite H; clear H; unfold w64;
rewrite ?unsigned_lit_small by lia; first [reflexivity | f_equal; lia] end.
Ltac ap_reg HP r :=
rewrite (ap_eq _ _ r HP) by (unfold acallee_saved; let x := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with x; lia).
Ltac ap_close HP HS AG E := lazymatch goal with |- getr _ ?r = w64 _ => ap_reg HP r; regs_close HS AG E end.
Ltac r20_close HS AG E20 c p :=
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict _ ?msx) =>
let H := fresh "R20x" in
pose proof (st_ok_pi_restrict_reg _ Ev ss msx (20%bv : bv 5) HS) as H;
let e := eval vm_compute in (sr_get (ss_regs ss) (20%bv : bv 5)) in change (sr_get (ss_regs ss) (20%bv : bv 5)) with e in H;
cbn [ms_regs restrict mkst] in H; rewrite H, denot_lit_U; unfold w64; f_equal;
let F := fresh "F20" in assert (F : ew Ev 20 = Z_to_bv 64 (3 * c + 8 + p)) by (rewrite AG by lia; exact E20);
rewrite (U_addw_small Ev (SOff 20 0) (SLit 1) (3 * c + 8 + p) 1); [lia | apply U_atom; [exact F | lia] | apply U_lit; lia | lia | lia | lia]
end.
Ltac winout := let r := fresh "r" in let Hr := fresh "Hr" in let Hw := fresh "Hw" in
intros (r & Hr & Hw); lazymatch type of Hr with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In r rs1) in Hr end;
cbn [In] in Hr; repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hw;
  repeat match goal with H : ew ?Ex ?n = Z_to_bv 64 _ |- _ => rewrite H in Hw end; rewrite ?unsigned_lit_small in Hw by lia; lia |]); try destruct Hr.
Lemma kept_out : forall mem3 md3 (EE2 : Z -> Prop),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 1632 <= a < spZ regs) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a) ->
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem3) ->
tcj_kept B TBGS_STK lyc Sc W memc W mem3 (spZ regs) EE2.
Proof.
intros mem3 md3 EE2 HJ3 Hout Hgr.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
pose proof (proj1 HJc) as HAR.
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hw _. apply Hout; lia.
- intros b m i Hin Hi _.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & _). apply Hout; lia.
- intros a Hi _ _. pose proof (pa_img_range a Hi). apply Hout; lia.
- intros cid pos a Hin Hr _.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. unfold kLowMemEnd, kHighShadowEnd in *.
  apply Hout; destruct Hr; lia.
- intros a Ha Hw Hp. exact (apresent_grows _ _ _ a Hgr Hp).
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). apply HP. lia.
Qed.
Ltac upd_out :=
lazymatch goal with
| Ho : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 1632 <= a < spZ regs) -> aview SEGS (w_H W) ?m0 a = aview SEGS (w_H W) memc a,
  Hg : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) ?m0) |- _ =>
  lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)), HG : mem_grows (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (Hout' : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 1632 <= a < spZ regs) -> aview SEGS (w_H W) (ms_mem m1) a = aview SEGS (w_H W) memc a)
    by (let a := fresh "a" in let Ha := fresh "Ha" in let Hw0 := fresh "Hw0" in
        intros a Ha Hw0; rewrite (aview_kept_out Eo rs _ _ _ HFr a Ha) by winout; exact (Ho a Ha Hw0));
  assert (Hgr' : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem m1))) by exact (mem_grows_trans _ _ _ Hg HG);
  clear Ho Hg HFr HG; rename Hout' into Hout; rename Hgr' into Hgr
  end
end.
Ltac clear_fr := repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
Ltac bgs_awr Usp := lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [azlit_tac|]
| eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
Section ok.
Hypothesis HOK : bgs_ok s V mx base w.
Lemma rows_win : SP <= s \/ s + 34 * sweep_rows w <= SP - TBGS_STK.
Proof. destruct (HROWS HOK) as (_ & _ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
(* A step that changes only this call's own window and, at most, the next row
   [D, D + n) keeps the invariant (the rows written so far included). *)
Lemma binv_kept : forall W2 ly2 S2 mem2 md2 rows mem3 md3 D n,
binv W2 ly2 S2 mem2 md2 rows ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 k ->
s + Z.of_nat (length rows) <= D -> D + n <= s + 34 * sweep_rows w -> 0 <= n ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (SP - TBGS_STK <= a < SP) -> ~ (D <= a < D + n) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
(forall a, FR + 1528 <= a < FR + 1632 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
(forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
binv W2 ly2 S2 mem3 md3 rows.
Proof.
intros W2 ly2 S2 mem2 md2 rows mem3 md3 D n (HJ & Hfr & Hbl & HKe & Hsv & Hrw & Hlen & Hfs) HJ3 HD1 HD2 Hn Hout Hsave Hpres.
pose proof rows_win as Hrwin. pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
assert (HRE : forall a, D <= a < D + n -> RowsE a) by (intros a Ha; unfold RowsE; lia).
pose proof (proj1 HJ) as HAR.
destruct (j_layout W2 ly2 S2 mem2 md2 k HJ) as (Elo & Ehi & EF).
split; [exact HJ3|]. split; [exact Hfr|]. split; [exact Hbl|].
destruct HKe as (K1 & K2 & K3 & K4 & K5 & K6).
split; [split; [|split; [|split; [|split; [|split]]]]|].
- intros a Ha Hw HE. rewrite Hout; [exact (K1 a Ha Hw HE) | lia | lia | intros X; exact (HE (HRE a X))].
- intros b m i Hin Hi HE.
  assert (Hin2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin2) as (_ & Hb4096 & Hbceil & _).
  rewrite Hout; [exact (K2 b m i Hin Hi HE) | lia | lia | intros X; exact (HE (HRE _ X))].
- intros a Hi Hns He. pose proof (pa_img_range a Hi) as HIa.
  rewrite Hout; [exact (K3 a Hi Hns He) | lia | lia | intros X; pose proof (HRE a X) as X2; unfold RowsE in X2;
  destruct (HROWS HOK) as (_ & _ & Hni & _); exact (Hni a X2 Hi)].
- intros cid pos a Hin Hr HE.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin2) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid).
  pose proof (shadow_addr_bounds (frame_addr ly2 cid pos) ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr ly2 cid pos + fs_frame_bytes cid) ltac:(lia)).
  pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  pose proof (fs_frame_bytes_nonneg cid).
  pose proof Hr as Hr0.
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. rewrite lyc_layout, <- EF in Hr.
  rewrite Hout; [exact (K4 cid pos a Hin Hr0 HE) | | | intros X; exact (HE (HRE a X))];
  destruct Hr as [Hr | Hr]; unfold kLowMemEnd, kHighShadowEnd in *; lia.
- intros a Ha Hw Hp. apply Hpres. apply K5; auto.
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP3 & _). apply HP3. lia.
- split.
  + unfold bgs_saved in *. apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) Hsv _ Hin) as Hv.
    pose proof (saved_off o r Hin) as Ho. cbn [fst snd] in *.
    eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hv].
    intros x Hx. apply Hsave. lia.
  + split; [|split; [exact Hlen | exact Hfs]].
    eapply (garr8_aview_kept SEGS (w_H W2) (w_H W2) mem2 mem3); [|exact Hrw].
    destruct (HROWS HOK) as (_ & Hs47 & _).
    intros a Ha. apply Hout; [lia | lia | lia].
Qed.
Lemma awr_ly : forall l1 l2 bl0 blc a, (forall c p, frame_addr l1 c p = frame_addr l2 c p) ->
awr_byte STK sp0 FP bl0 blc l1 own a -> awr_byte STK sp0 FP bl0 blc l2 own a.
Proof.
intros l1 l2 bl0 blc a EF [H|[H|[H|(cid & pos & Hin & H)]]]; [left; exact H | right; left; exact H | right; right; left; exact H|].
right; right; right. exists cid, pos. rewrite <- !EF. split; [exact Hin | exact H].
Qed.
Lemma arod_binv : forall W2 ly2 S2 mem2 md2 rows, binv W2 ly2 S2 mem2 md2 rows ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W2) mem2).
Proof.
intros W2 ly2 S2 mem2 md2 rows (_ & _ & _ & (_ & _ & K3 & _) & _) a Hro Hns He.
rewrite (K3 a); [exact (HROD a Hro Hns He) | | exact Hns | exact He].
destruct Hro as [(sg & Hsg & _ & Hr) | Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (pa_relro_img a Hr)].
Qed.
Lemma win_present : forall W2 ly2 S2 mem2 md2 rows a, binv W2 ly2 S2 mem2 md2 rows -> FR <= a < SP ->
apresent (w_H W2) mem2 a.
Proof.
intros W2 ly2 S2 mem2 md2 rows a ((_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _) & _) Ha.
apply HP. pose proof stk_bounds. assert (TBGS_STK = 6016) by reflexivity. lia.
Qed.
Lemma amem_stack : forall a n, FR <= a -> a + n < SP -> 0 <= n -> amem_range a n.
Proof.
intros a n H1 H2 H3. pose proof stk_bounds as (B1 & B2 & B3 & B4 & _). pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold amem_range. right. lia.
Qed.
(* __asan_memset over the scratch frame at sp+36 *)
Lemma call_memset : forall W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret Q,
binv W2 ly2 S2 mem2 md2 rows ->
getr regsT 10 = w64 (FR + 36) -> getr regsT 11 = w64 0 -> getr regsT 12 = w64 1492 ->
spZ regsT = FR -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
(forall mem3 md3 regs3, binv W2 ly2 S2 mem3 md3 rows ->
 (forall a, FR <= a < FR + 36 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) -> aregs_preserved regsT regs3 ->
 SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memset)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros W2 ly2 S2 mem2 md2 rows regsT ret Q HI H10' H11' H12' Hsp H3 H4 H1 Hret Hret2 HK.
pose proof HI as (HJ & Hfr & Hbl & HKe & Hsv & Hrw & Hlen & Hfs).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (frame_shadow W2 ly2 S2 mem2 md2 rows (FR + 36) 1492 HI ltac:(lia) ltac:(lia) ltac:(lia)) as [Hrd Hhl].
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (SIGMA GS___asan_memset) AMEMSET W2 regsT mem2 STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 k (FR + 36) 0 1492 (FR - sp0) (Z_to_bv 64 (BASE + ret)) HJ H10' H11' H12').
  - lia. - lia. - lia.
  - rewrite Hsp. lia.
  - apply m16; [exact Hal16 | exact B5 | reflexivity].
  - lia.
  - rewrite Hes. lia.
  - exact H3. - exact H4. - exact H1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - intros a Ha. split; [left; lia | rewrite Hes; lia].
  - apply amem_stack; lia.
  - exact Hrd.
  - intros _. exact Hhl.
  - exact I. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & _ & Hout & Hpres3 & _).
apply HK; [| intros a Ha; apply Hout; [lia | lia | rewrite Hes; lia] | exact HP3].
eapply (binv_kept W2 ly2 S2 mem2 md2 rows mem3 md3 (s + Z.of_nat (length rows)) 0 HI HJ3); try lia.
- intros a Ha Hw _. apply Hout; [lia | lia | rewrite Hes; lia].
- intros a Ha. apply Hout; [lia | lia | rewrite Hes; lia].
- exact Hpres3.
Qed.
(* __asan_memcpy of L (n bytes) from x into the next row s + |rows| *)
Lemma call_cpy : forall W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret x (L : list Z) Q,
binv W2 ly2 S2 mem2 md2 rows ->
let d := s + Z.of_nat (length rows) in let n := Z.of_nat (length L) in
0 < n < 2 ^ 32 -> Z.of_nat (length rows) + n <= 34 * sweep_rows w ->
garr8 SEGS (mrestrict (w_H W2) mem2) x L ->
0 <= x -> x + n <= 2 ^ 63 -> (d + n <= x \/ x + n <= d) -> amem_range x n ->
(forall a, x <= a < x + n -> ~ (FR - ESTACK <= a < FR)) ->
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF x n -> shadow_hull_vis (aview SEGS (w_H W2) mem2) x n ->
getr regsT 10 = w64 d -> getr regsT 11 = w64 x -> getr regsT 12 = w64 n ->
spZ regsT = FR -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
(forall mem3 md3 regs3, binv W2 ly2 S2 mem3 md3 (rows ++ L) ->
 (forall a, FR <= a < FR + 36 -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) -> aregs_preserved regsT regs3 ->
 SRr SEGS W2 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA GS___asan_memcpy)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros W2 ly2 S2 mem2 md2 rows regsT ret x L Q HI d n Hn Hlen2 HL Hx0 Hx63 Hdx Hxam Hxw Hxra Hxhl H10' H11' H12' Hsp H3 H4 H1 Hret Hret2 HK.
pose proof HI as (HJ & Hfr & Hbl & HKe & Hsv & Hrw & Hlen & Hfs).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
destruct (HROWS HOK) as (Ram & R47 & Rimg & Rwr & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Rwin & _).
pose proof (proj1 HJ) as HAR.
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hbm).
destruct (binv_layout W2 ly2 S2 mem2 md2 rows HI) as (Elo & Ehi & EF).
eapply SRr_bind.
{ eapply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (SIGMA GS___asan_memcpy) AMEMCPY W2 regsT mem2 STK sp0 FP ly S W0 mem0 md0 own ly2 S2 md2 k d x n (FR - sp0) (Z_to_bv 64 (BASE + ret)) HJ H10' H11' H12').
  - lia. - unfold d; lia. - unfold d, n in *; lia.
  - rewrite Hsp. lia.
  - apply m16; [exact Hal16 | exact B5 | reflexivity].
  - lia.
  - rewrite Hes. lia.
  - exact H3. - exact H4. - exact H1.
  - apply ret_ok_codeptr_v; [lia | exact Hret2].
  - intros a Ha. destruct (Rwr a ltac:(unfold d, n in *; lia)) as (Haw & _ & _ & Hne).
    split; [rewrite Hbl; apply (awr_ly lyc ly2); [intros c p0; rewrite lyc_layout, EF; reflexivity | exact Haw] | rewrite Hes; unfold d, n in *; lia].
  - unfold amem_range in *. unfold d, n in *. lia.
  - apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m); [exact HAR | exact Hbm2 | unfold d; lia | unfold d, n in *; lia].
  - intros Hn0. apply (shadow_hull_vis_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 b m); [exact HAR | exact Hbm2 | unfold d; lia | unfold d, n in *; lia | exact Hn0].
  - split; [exact Hx0|]. split; [exact Hx63|]. split.
    { intros a Ha. split; [|rewrite Hsp; exact (Hxw a Ha)].
      destruct (garr8_nthZ SEGS _ x L (a - x) HL ltac:(lia) ltac:(unfold n in Ha; lia)) as [Hv Hvr].
      replace (x + (a - x)) with a in Hv by lia. eapply aview_of_val_mem1 in Hv; [| exact Hvr]. rewrite Hv. discriminate. }
    split; [exact Hdx|]. split; [exact Hxam|]. split; [exact Hxra | intros _; exact Hxhl]. }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & _ & Heff & Hout & Hpres3 & _).
apply HK; [| intros a Ha; apply Hout; [lia | unfold d, n in *; lia | rewrite Hes; lia] | exact HP3].
assert (HI3 : binv W2 ly2 S2 mem3 md3 rows).
{ eapply (binv_kept W2 ly2 S2 mem2 md2 rows mem3 md3 d n HI HJ3); try (unfold d, n in *; lia).
  - intros a Ha Hw Hd. apply Hout; [lia | exact Hd | rewrite Hes; lia].
  - intros a Ha. apply Hout; [lia | unfold d, n in *; lia | rewrite Hes; lia].
  - exact Hpres3. }
destruct HI3 as (HJ4 & Hfr4 & Hbl4 & HK4 & Hsv4 & Hrw4 & _ & Hfs4).
split; [exact HJ4|]. split; [exact Hfr4|]. split; [exact Hbl4|]. split; [exact HK4|]. split; [exact Hsv4|].
rewrite length_app. split; [|split; [lia | exact Hfs4]].
apply garr8_app. split; [exact Hrw4|].
apply (garr8_aview SEGS (w_H W2) (w_H W2) mem2 mem3 x d L); [|exact HL].
intros i Hi. rewrite Heff by (unfold n; lia). reflexivity.
Qed.
(* reac_ctrl_stamp_headamp on the scratch frame at sp+36 *)
Lemma call_stamp : forall W2 ly2 S2 mem2 md2 rows (regsT : bvmap 5 word) ret ch pm v Q,
binv W2 ly2 S2 mem2 md2 rows ->
getr regsT 10 = w64 (FR + 36) -> getr regsT 11 = w64 ch -> getr regsT 12 = w64 pm -> getr regsT 13 = w64 v ->
0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 -> legalb pm v = true ->
spZ regsT = FR -> getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 ->
s0Z regsT < alloc_ceiling ->
(forall W3 ly3 S3 mem3 md3 regs3, binv W3 ly3 S3 mem3 md3 rows ->
 (forall a, FR <= a < FR + 36 -> aview SEGS (w_H W3) mem3 a = aview SEGS (w_H W2) mem2 a) ->
 aregs_preserved regsT regs3 -> getr regs3 10 = w64 0 ->
 garr8 SEGS (mrestrict (w_H W3) mem3) (FR + 52) (GAz ch pm v) ->
 SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + ret)) mem3 (seg_rom SEGS)) md3) Q) ->
SRr SEGS W2 (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)) mem2 (seg_rom SEGS)) md2) Q.
Proof.
intros W2 ly2 S2 mem2 md2 rows regsT ret ch pm v Q HI H10' H11' H12' H13' Rch Rpm Rv Hleg Hsp H3 H4 H1 Hret Hret2 Hs0 HK.
pose proof HI as (HJ & Hfr & Hbl & HKe & Hsv & Hrw & Hlen & Hfs).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (WS2 : TSTAMP_STK = 4384) by reflexivity.
pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
destruct (HROWS HOK) as (Ram & R47 & Rimg & Rwr & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Rwin & _).
pose proof (proj1 HJ) as HAR.
assert (Hbm2 : In (b, m) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hbm).
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm2) as (_ & Hb4096 & Hbceil & _).
destruct (binv_layout W2 ly2 S2 mem2 md2 rows HI) as (Elo & Ehi & EF).
eapply SRr_bind.
{ change (Z_to_bv 64 (BASE + AF_reac_ctrl_stamp_headamp)) with (w64 (BASE + AF_reac_ctrl_stamp_headamp)).
  eapply (TSTAMP STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k regsT (FR + 36) ch pm v [] HJ).
  - exact (arod_binv W2 ly2 S2 mem2 md2 rows HI).
  - rewrite H1. apply ret_ok_codeptr_v; [lia | exact Hret2].
  - unfold raZ. rewrite H1, unsigned_lit_small by lia. lia.
  - exact H3. - exact H4. - exact H10'. - exact H11'. - exact H12'. - exact H13'.
  - exact Rch. - exact Rpm. - exact Rv.
  - left. split; [left; exact Hs0 | reflexivity].
  - rewrite Hsp. replace (spZ regs - 1632) with (spZ regs - 1632 - 0) by lia. apply m16; [exact Hal16 | reflexivity | reflexivity].
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - rewrite Hfr. exact Hfr8.
  - lia. - lia.
  - apply amem_stack; lia.
  - intros xx Hx Himg. pose proof (pa_img_range xx Himg). lia.
  - rewrite Hsp. lia.
  - lia.
  - intros _. intros a Ha. split; [left; lia|]. split; [exact (win_present W2 ly2 S2 mem2 md2 rows a HI ltac:(lia))|].
    split; [apply (al_stack _ _ LAWS ly2 S2 W2 mem2 md2 a HAR); rewrite Elo, Ehi; lia | rewrite Hsp, Hes; lia]. }
cbv beta. intros W3 c3 Hwle (ly3 & S3 & regs3 & mem3 & md3 & res & -> & HJ3 & HP3 & Hfr3 & Hbl3 & Hfs3 & Hres & HK3 & Hcase).
rewrite Hleg in Hcase. destruct Hcase as (-> & Hga).
rewrite H1. apply (HK W3 ly3 S3 mem3 md3 regs3); [| | exact HP3 | exact Hres | replace (FR + 52) with (FR + 36 + 16) by lia; exact Hga].
2:{ destruct HK3 as (L1 & _). rewrite Hsp in L1. intros a Ha. apply L1; lia. }
unfold EV_STAMP, EV_LAY in HJ3. rewrite Z.add_0_r in HJ3.
destruct HK3 as (L1 & L2 & L3 & L4 & L5 & L6). rewrite Hsp in L1, L5, L6.
destruct HKe as (K1 & K2 & K3 & K4 & K5 & K6).
destruct (j_layout W3 ly3 S3 mem3 md3 k HJ3) as (Elo3 & Ehi3 & EF3).
split; [exact HJ3|]. split; [rewrite Hfr3; exact Hfr|]. split; [rewrite Hbl3; exact Hbl|].
split; [split; [|split; [|split; [|split; [|split]]]]|].
- intros a Ha Hw HE. rewrite L1; [exact (K1 a Ha Hw HE) | lia | lia | lia].
- intros b0 m0 i Hin Hi HE.
  assert (Hin2 : In (b0, m0) (ablocks B ly2 S2)) by (rewrite Hbl; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HAR Hin2) as (_ & Hb4096' & Hbceil' & _).
  rewrite (L2 b0 m0 i Hin2 Hi ltac:(lia)). exact (K2 b0 m0 i Hin Hi HE).
- intros a Hi Hns He. rewrite L3; [exact (K3 a Hi Hns He) | exact Hi | exact Hns | exact He].
- intros cid pos a Hin Hr HE.
  assert (Hin2 : In (cid, pos) (frames S2)) by (rewrite Hfr; exact Hin).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin2) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid).
  pose proof (shadow_addr_bounds (frame_addr ly2 cid pos) ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr ly2 cid pos + fs_frame_bytes cid) ltac:(lia)).
  pose proof (shadow_range_end (frame_addr ly2 cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  assert (Hr2 : in_zr a (frame_rng ly2 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly2 cid pos), fs_frame_bytes cid / 8)).
  { unfold frame_rng in *. cbn [fst snd] in *. rewrite lyc_layout, <- EF in Hr. exact Hr. }
  rewrite (L4 cid pos a Hin2 Hr2); [exact (K4 cid pos a Hin Hr HE) |].
  unfold frame_rng, in_zr in Hr2. cbn [fst snd] in Hr2. unfold kLowMemEnd, kHighShadowEnd in *. destruct Hr2; lia.
- intros a Ha Hw Hp. apply L5; [lia | lia | exact (K5 a Ha Hw Hp)].
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). apply HP. lia.
- split.
  + unfold bgs_saved in *. apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) Hsv _ Hin) as Hv.
    pose proof (saved_off o r Hin) as Ho. cbn [fst snd] in *.
    eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact Hv].
    intros xx Hx. apply L1; lia.
  + split; [|split; [exact Hlen | destruct Hfs3 as (f3 & ->); destruct Hfs as (f & ->); exists f3; reflexivity]].
    eapply (garr8_aview_kept SEGS (w_H W2) (w_H W3) mem2 mem3); [|exact Hrw].
    intros a Ha. replace a with (b + (a - b)) by lia. apply (L2 b m (a - b) Hbm2); lia.
Qed.
Lemma binv_init : forall mem3 md3,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem3 md3 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (FR <= a < SP) -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a) ->
mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem3) ->
bgs_saved (mrestrict (w_H W) mem3) ->
binv W lyc Sc mem3 md3 [].
Proof.
intros mem3 md3 HJ3 Hout Hgr Hsv.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
pose proof (proj1 HJc) as HAR.
split; [exact HJ3|]. split; [reflexivity|]. split; [reflexivity|].
split; [split; [|split; [|split; [|split; [|split]]]]|].
- intros a Ha Hw _. apply Hout; lia.
- intros b m i Hin Hi _.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & Hb4096 & Hbceil & _). apply Hout; lia.
- intros a Hi _ _. pose proof (pa_img_range a Hi). apply Hout; lia.
- intros cid pos a Hin Hr _.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)).
  pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)).
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) (fs_frame_bytes_nonneg cid)).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. unfold kLowMemEnd, kHighShadowEnd in *.
  apply Hout; destruct Hr; lia.
- intros a Ha Hw Hp. exact (apresent_grows _ _ _ a Hgr Hp).
- intros a Ha. pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). apply HP. lia.
- split; [exact Hsv|]. split; [apply garr8_nil|]. split; [cbn; unfold sweep_rows; destruct HOK as (_ & _ & Hw1 & _); lia|].
  exists (st_fs Sc). destruct Sc; reflexivity.
Qed.
Lemma binv_frame : forall W2 ly2 S2 mem2 md2 rows mem3 md3,
binv W2 ly2 S2 mem2 md2 rows -> ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem3 md3 k ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (FR <= a < FR + 1528) -> aview SEGS (w_H W2) mem3 a = aview SEGS (w_H W2) mem2 a) ->
mem_grows (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) mem3) ->
binv W2 ly2 S2 mem3 md3 rows.
Proof.
intros W2 ly2 S2 mem2 md2 rows mem3 md3 HI HJ3 Hout Hgr.
pose proof HI as (_ & _ & _ & _ & _ & _ & Hlen & _). pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7). assert (WS : TBGS_STK = 6016) by reflexivity.
eapply (binv_kept W2 ly2 S2 mem2 md2 rows mem3 md3 (s + Z.of_nat (length rows)) 0 HI HJ3); try lia.
- intros a Ha Hw _. apply Hout; lia.
- intros a Ha. apply Hout; lia.
- intros a Hp. exact (apresent_grows _ _ _ a Hgr Hp).
Qed.
Lemma fsb8 : forall c, 0 <= c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c Hc. unfold fs_frame_bytes.
rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z_mod_mult.
Qed.
(* the values: their bytes and their shadow are the caller's, at every point *)
Lemma vals_at : forall W2 ly2 S2 mem2 md2 rows, binv W2 ly2 S2 mem2 md2 rows ->
garr8 SEGS (mrestrict (w_H W2) mem2) V (map bv_unsigned vals) /\
range_addressable (aview SEGS (w_H W2) mem2) SHADOW_OFF V (3 * w) /\
0 <= V /\ V + 3 * w <= 2 ^ 47 - 1 /\ length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals.
Proof.
intros W2 ly2 S2 mem2 md2 rows HI.
pose proof HI as (HJ & Hfr & Hbl & (K1 & K2 & K3 & K4 & K5 & K6) & _).
pose proof HOK as (Hs0 & HV0 & Hw1 & Hbw & Hmx).
destruct (HVALS Hw1 HV0) as (Hlen & Hleg & HG & (_ & HraV & _ & Ham & HVz & _) & ((cid & pos & Hin & Hcid & Hal & Hlo & Hhi) & _ & _) & _).
destruct (HROWS HOK) as (_ & _ & _ & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & _ & Hdis).
pose proof (proj1 HJc) as HAR.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hbm) as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (H47 : V + 3 * w <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemEnd in *; lia).
split; [|split; [|split; [lia | split; [exact H47 | split; [exact Hlen | exact Hleg]]]]].
- eapply (garr8_aview_kept SEGS (w_H W) (w_H W2) memc mem2); [|exact HG].
  rewrite length_map, Hlen. intros a Ha. apply (K4 cid pos a Hin).
  + left. unfold frame_rng, in_zr. cbn [fst snd]. lia.
  + unfold RowsE. lia.
- eapply range_addressable_agree; [|exact HraV].
  intros x Hx. apply (K4 cid pos _ Hin).
  + right. unfold in_zr, shadow_addr, shadow_of_addr. cbn [fst snd].
    pose proof (fsb8 cid Hcid) as Hb8. pose proof (fs_frame_bytes_nonneg cid).
    set (f := frame_addr lyc cid pos) in *. set (bs := fs_frame_bytes cid) in *.
    pose proof (Z.div_mod f 8 ltac:(lia)) as Df. pose proof (Z.div_mod bs 8 ltac:(lia)) as Db.
    assert (Hq : f / 8 <= x / 8) by (apply Z.div_le_mono; lia).
    assert (Hq2 : x / 8 < f / 8 + bs / 8) by (apply Z.div_lt_upper_bound; lia).
    lia.
  + unfold RowsE, shadow_of_addr, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
    assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Definition l1regs (R : bvmap 5 word) (p : Z) : Prop :=
getr R 2 = w64 FR /\ getr R 3 = w64 (as_gp B) /\ getr R 4 = w64 (as_tp B) /\ getr R 8 = w64 w /\ getr R 9 = w64 base /\
getr R 18 = w64 s /\ getr R 19 = w64 V /\ getr R 20 = w64 p /\ getr R 21 = w64 (FR + 52) /\
getr R 22 = w64 (s + 34 * (1 + p)) /\ getr R 23 = w64 (V + p) /\ getr R 25 = w64 SBV /\ getr R 26 = w64 3 /\
getr R 27 = w64 (V + p).
Definition L1post (p : Z) (rows : list Z) : world SEGS -> config -> Prop :=
fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (if p =? 3 then 10236 else 10120))) mem3 (seg_rom SEGS)) md3 /\
binv W3 ly3 S3 mem3 md3 rows /\ l1regs regs3 p.
Ltac upd_binv HIold HInew :=
lazymatch type of HIold with binv ?Wx ?lyx ?Sx ?m0 ?md0 ?rws =>
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem m1) ?mdx _, HG : mem_grows (mrestrict _ m0) _ |- _ =>
assert (HInew : binv Wx lyx Sx (ms_mem m1) mdx rws) by
(eapply (binv_frame Wx lyx Sx m0 md0 rws); [exact HIold | exact HJ | intros a Ha _; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); nowin | exact HG])
end end end.
Lemma row1 : forall p rows W2 ly2 S2 regs2 mem2 md2, 0 <= p < 3 -> binv W2 ly2 S2 mem2 md2 rows ->
Z.of_nat (length rows) = 34 * (1 + p) -> l1regs regs2 p ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10120)) mem2 (seg_rom SEGS)) md2)
(L1post (p + 1) (rows ++ GAz base p (vz vals (Z.to_nat p)))).
Proof.
intros p rows W2 ly2 S2 regs2 mem2 md2 Hp HI Hlen (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
destruct (vals_at W2 ly2 S2 mem2 md2 rows HI) as (HGV & HRV & HV0 & HV47 & Hvlen & Hvleg).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold sweep_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold sweep_rows in Hs47, Hrwin.
set (vb := vz vals (Z.to_nat p)).
destruct (garr8_nthZ SEGS _ V (map bv_unsigned vals) p HGV ltac:(lia) ltac:(rewrite length_map, Hvlen; lia)) as [Mvb Rvb].
rewrite nth_mapu in Mvb, Rvb. change (bv_unsigned (nth (Z.to_nat p) vals (Z_to_bv 8 0))) with vb in Mvb, Rvb.
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [Z_to_bv 64 vb])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 vb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E ss_l1a (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10120)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_l1a. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E27, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (V + p) 0 1 (SOff 32 0) vb);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | rewrite Z.add_0_r; exact Mvb].
- cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E25, E23, E27, E32, !unsigned_lit_small by (unfold SBV; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SBV. repeat split; lia. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
unfold cfg_at.
(* run 1: to the memset *)
paj_run_tok RUN HS HJ SHOK BspanS.
{ cbn [ms_mem]. rewrite <- (aview_rd_of SEGS). unfold BxL. rewrite (U_atom E 25 SBV E25) by (unfold SBV; lia).
  rewrite (U_atom E 23 (V + p) E23) by lia. unfold SBV. change 2147450880 with SHADOW_OFF.
  apply (range_addressable_sub _ _ V (3 * w)); [exact HRV | lia | lia]. }
{ awr_ok_tac. }
rebase HS AG.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ |- _ =>
assert (HI1 : binv W2 ly2 S2 (ms_mem m1) mdx rows) by
(eapply (binv_frame W2 ly2 S2 mem2 md2 rows); [exact HI | exact HJ | intros a Ha _; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); nowin | exact HG]) end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp.
rewrite ?unsigned_lit_small in Ra0 by lia.
pmkst HS. clear_frames.
eapply (call_memset W2 ly2 S2 _ _ rows _ 10156 _ HI1); [exact Ra0 | exact Ra1 | exact Ra2 | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
| exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem3 md3 regs3 HI3 _ HP3. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI1 HJ SHOK.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
(* run 2: to reac_ctrl_stamp_headamp *)
paj_run_tok RUN HS HJ3 SHOK BspanS. { awr_ok_tac. }
rebase HS AG.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem3) (mrestrict _ (ms_mem ?m1)), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ |- _ =>
assert (HI1 : binv W2 ly2 S2 (ms_mem m1) mdx rows) by
(eapply (binv_frame W2 ly2 S2 mem3 md3 rows); [exact HI3 | exact HJ | intros a Ha _; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); nowin | exact HG]) end.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Rs0.
rfact AG E Ra0. rfact AG E Ra1. rfact AG E Ra2. rfact AG E Ra3. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp. rfact AG E Rs0.
rewrite ?unsigned_lit_small in Ra0 by lia.
pmkst HS. clear_frames. rewrite pa_sigma_reac_ctrl_stamp_headamp.
assert (Hleg : legalb p vb = true).
{ apply BgsTurn.legal_legalb. pose proof (Hvleg (Z.to_nat p) ltac:(lia)) as L.
  replace (Z.of_nat (Z.to_nat p mod 3)) with p in L by (rewrite Nat.mod_small by lia; lia). exact L. }
eapply (call_stamp W2 ly2 S2 _ _ rows _ 10176 base p vb _ HI1); [exact Ra0 | exact Ra1 | exact Ra2 | exact Ra3 | lia | lia | lia | exact Hleg
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity
| unfold s0Z; rewrite Rs0, unsigned_lit_small by lia; lia |].
intros W4 ly4 S4 mem4 md4 regs4 HI4 _ HP4 R10' HGA. clear Ra0 Ra1 Ra2 Ra3 Rsp Rgp Rtp Rra Rs0 HI1 SHOK HI3 HJ3.
pose proof (proj1 HI4) as HJ4.
reseat HS HJ4 HP4 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
prreg HS (10%bv : bv 5) Rz. rewrite R10' in Rz. symmetry in Rz.
(* run 3: the stamp's result is 0, so on to the memcpy *)
paj_run_tok RUN HS HJ4 SHOK BspanS. { awr_ok_tac. }
rebase HS AG.
upd_binv HI4 HI4a. upd_garr HGA HGAa. clear_frames. clear HI4 HGA.
psrr_branch_tok RUN BR HS SHOK BspanS.
{ exfalso. cbn [sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hc. rewrite Rz in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc Rz.
paj_run_tok RUN HS HJ4 SHOK BspanS. { awr_ok_tac. }
rebase HS AG.
upd_binv HI4a HI1. upd_garr HGAa HGA1. clear_frames. clear HI4a HGAa.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Ra1. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp.
pmkst HS. clear_frames.
eapply (call_cpy W4 ly4 S4 _ _ rows _ 10196 (FR + 52) (GAz base p vb) _ HI1);
change (length (GAz base p vb)) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold sweep_rows;
[ lia | lia | exact HGA1 | lia | lia | lia | apply amem_stack; lia | unfold ESTACK; lia
| exact (proj1 (frame_shadow W4 ly4 S4 _ _ rows (FR + 52) 34 HI1 ltac:(lia) ltac:(lia) ltac:(lia)))
| exact (proj2 (frame_shadow W4 ly4 S4 _ _ rows (FR + 52) 34 HI1 ltac:(lia) ltac:(lia) ltac:(lia)))
| rewrite Ra0; unfold w64; f_equal; lia | exact Ra1 | exact Ra2
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem5 md5 regs5 HI5 _ HP5. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI1 HJ4 HGA1.
pose proof (proj1 HI5) as HJ5.
reseat HS HJ5 HP5 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
(* run 4: the counters, and back to the loop head or on *)
paj_run_tok RUN HS HJ5 SHOK BspanS. { awr_ok_tac. }
rebase HS AG. upd_binv HI5 HI5a. clear_frames. clear HI5.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F20 : ew Ev 20 = Z_to_bv 64 p) by (rewrite AG by lia; exact E20);
assert (F26 : ew Ev 26 = Z_to_bv 64 3) by (rewrite AG by lia; exact E26) end.
psrr_branch_tok RUN BR HS SHOK BspanS.
- rewrite branch_ne_U, (U_atom_off _ 20 p 1 F20), (U_atom _ 26 3 F26) in Hc by lia.
  assert (Hp1 : p + 1 <> 3) by (destruct (Z.eqb_spec (p + 1) 3); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10120. { awr_ok_tac. }
  rebase HS AG. upd_binv HI5a HI6. clear_frames.
  pmkst HS. apply SRr_ret. unfold L1post.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [replace (p + 1 =? 3) with false by (symmetry; apply Z.eqb_neq; exact Hp1); reflexivity|].
  split; [exact HI6|].
  unfold l1regs. repeat split; regs_close HS AG E.
- rewrite branch_ne_U, (U_atom_off _ 20 p 1 F20), (U_atom _ 26 3 F26) in Hc by lia.
  assert (Hp1 : p + 1 = 3) by (destruct (Z.eqb_spec (p + 1) 3); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10236. { awr_ok_tac. }
  rebase HS AG. upd_binv HI5a HI6. clear_frames.
  pmkst HS. apply SRr_ret. unfold L1post.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [replace (p + 1 =? 3) with true by (symmetry; apply Z.eqb_eq; exact Hp1); reflexivity|].
  split; [exact HI6|].
  unfold l1regs. repeat split; regs_close HS AG E.
Qed.
Definition i2regs (R : bvmap 5 word) (c p : Z) : Prop :=
getr R 2 = w64 FR /\ getr R 3 = w64 (as_gp B) /\ getr R 4 = w64 (as_tp B) /\ getr R 8 = w64 w /\ getr R 9 = w64 base /\
getr R 18 = w64 s /\ getr R 19 = w64 (s + 34 * (3 * c + 8 + p)) /\ getr R 20 = w64 (3 * c + 8 + p) /\ getr R 21 = w64 p /\
getr R 22 = w64 (base + c) /\ getr R 24 = w64 3 /\ getr R 25 = w64 SBV /\ getr R 26 = w64 (V + 3 * c) /\ getr R 27 = w64 (V + 3 * c).
Definition slots (m : word -> option byte) (c : Z) : Prop :=
val_mem SEGS m (FR + 16) 8 c /\ val_mem SEGS m (FR + 24) 8 (3 * c + 8).
Definition I2A (c p vb : Z) (rows : list Z) : world SEGS -> config -> Prop :=
fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + 10384)) mem3 (seg_rom SEGS)) md3 /\
binv W3 ly3 S3 mem3 md3 rows /\ i2regs regs3 c p /\ getr regs3 23 = w64 vb /\ slots (mrestrict (w_H W3) mem3) c.
Definition ss_l2a (p : Z) : sstate := mkSS 10340 (sr_set sr_atoms 21%bv (SLit p))
[YP09.mkRegion (Some 27%nat) p (p + 1) 0 0 [YP09.mkChunk p (CVal 1 (SOff 32 0))]] None
(mkFacts [(25%nat, mkAF SBV SBV 0); (26%nat, mkAF 0 (2 ^ 47 - 4) 0); (27%nat, mkAF 0 (2 ^ 47 - 4) 0); (32%nat, mkAF 0 255 0)] [] []).
Lemma row2a : forall c p rows W2 ly2 S2 regs2 mem2 md2, 1 <= c < w -> (p = 0 \/ p = 1 \/ p = 2) -> binv W2 ly2 S2 mem2 md2 rows ->
i2regs regs2 c p -> slots (mrestrict (w_H W2) mem2) c ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10340)) mem2 (seg_rom SEGS)) md2)
(I2A c p (vz vals (Z.to_nat (3 * c + p))) rows).
Proof.
intros c p rows W2 ly2 S2 regs2 mem2 md2 Hcw Hp HI (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R24 & R25 & R26 & R27) HSL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
destruct (vals_at W2 ly2 S2 mem2 md2 rows HI) as (HGV & HRV & HV0 & HV47 & Hvlen & Hvleg).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold sweep_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold sweep_rows in Hs47, Hrwin.
assert (Hp3 : 0 <= p < 3) by lia.
set (vb := vz vals (Z.to_nat (3 * c + p))).
destruct (garr8_nthZ SEGS _ V (map bv_unsigned vals) (3 * c + p) HGV ltac:(lia) ltac:(rewrite length_map, Hvlen; lia)) as [Mvb Rvb].
rewrite nth_mapu in Mvb, Rvb. change (bv_unsigned (nth (Z.to_nat (3 * c + p)) vals (Z_to_bv 8 0))) with vb in Mvb, Rvb.
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [Z_to_bv 64 vb])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
assert (E32 : ew E 32 = Z_to_bv 64 vb) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E22, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E (ss_l2a p) (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10340)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_l2a. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X | cbn [sv_denot]; rewrite R21; reflexivity].
- destruct Hp as [-> | [-> | ->]]; vm_compute; reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E27, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (V + 3 * c) p 1 (SOff 32 0) vb);
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | lia | replace (V + 3 * c + p) with (V + (3 * c + p)) by lia; exact Mvb].
- cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E25, E26, E27, E32, !unsigned_lit_small by (unfold SBV; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SBV. repeat split; lia. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
destruct Hp as [-> | [-> | ->]].
all: paj_run_tok RUN HS HJ SHOK BspanS.
all: lazymatch goal with
| |- awr_ok _ _ _ _ _ _ _ _ _ => awr_ok_tac
| |- range_addressable _ _ (U _ (SOff 26 ?q)) _ =>
  cbn [ms_mem]; rewrite <- (aview_rd_of SEGS); unfold BxL; rewrite (U_atom E 25 SBV E25) by (unfold SBV; lia);
  rewrite (U_atom_off E 26 (V + 3 * c) q E26) by lia; unfold SBV; change 2147450880 with SHADOW_OFF;
  apply (range_addressable_sub _ _ V (3 * w)); [exact HRV | lia | lia]
| |- _ => idtac end.
all: rebase HS AG.
all: upd_binv HI HI1.
all: match goal with HIo : binv ?Wo _ _ ?m0 _ _ |- _ =>
  match goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HK1 : forall a, FR <= a < FR + 36 -> aview SEGS (w_H Wo) (ms_mem m1) a = aview SEGS (w_H Wo) m0 a)
  by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end end.
all: clear_frames.
all: prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
  prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp; prreg HS (1%bv : bv 5) Rra.
all: rfact AG E Ra0; rfact AG E Rsp; rfact AG E Rgp; rfact AG E Rtp; rewrite ?unsigned_lit_small in Ra0 by lia.
all: pmkst HS.
all: eapply (call_memset W2 ly2 S2 _ _ rows _ 10384 _ HI1); [exact Ra0 | exact Ra1 | exact Ra2 | unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity
  | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
all: intros mem3 md3 regs3 HI3 HK3 HP3.
all: apply SRr_ret; unfold I2A; exists ly2, S2, regs3, mem3, md3.
all: split; [reflexivity|]; split; [exact HI3|].
all: split; [unfold i2regs; repeat split; ap_close HP3 HS AG E|].
all: split; [ap_close HP3 HS AG E|].
all: destruct HSL as [HS16 HS24]; split;
  (eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W2) mem2 mem3); [|eassumption]);
  intros x Hx; rewrite HK3 by lia; apply HK1; lia.
Qed.
Lemma and255 : forall p, 0 <= p < 256 -> alu64 ALU_AND (Z_to_bv 64 p) (Z_to_bv 64 255) = Z_to_bv 64 p.
Proof.
intros p Hp. apply bv_eq. cbn [alu64 alu]. rewrite bv_and_unsigned, !unsigned_lit_small by lia.
change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.
Definition I2post (c p : Z) (rows : list Z) : world SEGS -> config -> Prop :=
fun W3 c3 => exists ly3 S3 regs3 mem3 md3,
c3 = mkCfg (mkst regs3 (Z_to_bv 64 (BASE + (if p + 1 =? 3 then 10456 else 10340))) mem3 (seg_rom SEGS)) md3 /\
binv W3 ly3 S3 mem3 md3 rows /\ i2regs regs3 c (p + 1) /\ slots (mrestrict (w_H W3) mem3) c.
Definition ss_l2b : sstate := mkSS 10384 sr_atoms [] None (mkFacts [] [] []).
Lemma row2b : forall c p rows W2 ly2 S2 regs2 mem2 md2, 1 <= c < w -> 0 <= p < 3 -> binv W2 ly2 S2 mem2 md2 rows ->
Z.of_nat (length rows) = 34 * (3 * c + 8 + p) ->
i2regs regs2 c p -> getr regs2 23 = w64 (vz vals (Z.to_nat (3 * c + p))) -> slots (mrestrict (w_H W2) mem2) c ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10384)) mem2 (seg_rom SEGS)) md2)
(I2post c p (rows ++ GAz (base + c) p (vz vals (Z.to_nat (3 * c + p))))).
Proof.
intros c p rows W2 ly2 S2 regs2 mem2 md2 Hcw Hp HI Hlen (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R24 & R25 & R26 & R27) R23 HSL.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
destruct (vals_at W2 ly2 S2 mem2 md2 rows HI) as (HGV & HRV & HV0 & HV47 & Hvlen & Hvleg).
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold sweep_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold sweep_rows in Hs47, Hrwin.
set (vb := vz vals (Z.to_nat (3 * c + p))) in *.
assert (Rvb : 0 <= vb < 256) by (unfold vb, vz; apply (bv_unsigned_in_range 8 _)).
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite R21 in E21.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 23%nat 23%bv eq_refl) as E23. rewrite R23 in E23.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E ss_l2b (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10384)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_l2b. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
(* run 1: to reac_ctrl_stamp_headamp *)
paj_run_tok RUN HS HJ SHOK BspanS. { awr_ok_tac. }
rebase HS AG. upd_binv HI HI1.
match goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HK1 : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W2) (ms_mem m1) a = aview SEGS (w_H W2) mem2 a)
  by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end.
clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2. prreg HS (13%bv : bv 5) Ra3.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra. prreg HS (8%bv : bv 5) Rs0.
rfact AG E Ra0. rfact AG E Ra1. rfact AG E Ra2. rfact AG E Ra3. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp. rfact AG E Rs0.
rewrite ?unsigned_lit_small in Ra0 by lia. rewrite and255 in Ra2 by lia.
pmkst HS. clear_frames. rewrite pa_sigma_reac_ctrl_stamp_headamp.
assert (Hleg : legalb p vb = true).
{ apply BgsTurn.legal_legalb. pose proof (Hvleg (Z.to_nat (3 * c + p)) ltac:(lia)) as L.
  replace (Z.of_nat (Z.to_nat (3 * c + p) mod 3)) with p in L. { exact L. }
  replace (Z.to_nat (3 * c + p)) with (Z.to_nat p + Z.to_nat c * 3)%nat by lia. rewrite Nat.Div0.mod_add, Nat.mod_small by lia. lia. }
eapply (call_stamp W2 ly2 S2 _ _ rows _ 10404 (base + c) p vb _ HI1); [exact Ra0 | exact Ra1 | exact Ra2 | exact Ra3 | lia | lia | lia | exact Hleg
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity
| unfold s0Z; rewrite Rs0, unsigned_lit_small by lia; lia |].
intros W4 ly4 S4 mem4 md4 regs4 HI4 HK4 HP4 R10' HGA. clear Ra0 Ra1 Ra2 Ra3 Rsp Rgp Rtp Rra Rs0 HI1 SHOK HI.
pose proof (proj1 HI4) as HJ4.
reseat HS HJ4 HP4 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
prreg HS (10%bv : bv 5) Rz. rewrite R10' in Rz. symmetry in Rz.
(* run 2: the stamp's result is 0, so on to the memcpy *)
paj_run_tok RUN HS HJ4 SHOK BspanS. { awr_ok_tac. }
rebase HS AG.
upd_binv HI4 HI4a. upd_garr HGA HGAa.
match goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem4) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HK4a : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W4) (ms_mem m1) a = aview SEGS (w_H W4) mem4 a)
  by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end.
clear_frames. clear HI4 HGA.
psrr_branch_tok RUN BR HS SHOK BspanS.
{ exfalso. cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hc. rewrite Rz in Hc. vm_compute in Hc. discriminate Hc. }
clear Hc Rz.
paj_run_tok RUN HS HJ4 SHOK BspanS. { awr_ok_tac. }
rebase HS AG.
upd_binv HI4a HI1. upd_garr HGAa HGA1.
match goal with HIo : binv _ _ _ ?m0 _ _ |- _ =>
match goal with HFr : frame_of ?Eo ?rs (mrestrict _ m0) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HK4b : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W4) (ms_mem m1) a = aview SEGS (w_H W4) m0 a)
  by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end end.
clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Ra1. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp.
rewrite ?unsigned_lit_small in Ra1 by lia.
pmkst HS.
eapply (call_cpy W4 ly4 S4 _ _ rows _ 10424 (FR + 52) (GAz (base + c) p vb) _ HI1);
change (length (GAz (base + c) p vb)) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold sweep_rows;
[ lia | lia | exact HGA1 | lia | lia | lia | apply amem_stack; lia | unfold ESTACK; lia
| exact (proj1 (frame_shadow W4 ly4 S4 _ _ rows (FR + 52) 34 HI1 ltac:(lia) ltac:(lia) ltac:(lia)))
| exact (proj2 (frame_shadow W4 ly4 S4 _ _ rows (FR + 52) 34 HI1 ltac:(lia) ltac:(lia) ltac:(lia)))
| rewrite Ra0; unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia | exact Ra1 | exact Ra2
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem5 md5 regs5 HI5 HK5 HP5. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI1 HJ4 HGA1.
pose proof (proj1 HI5) as HJ5.
reseat HS HJ5 HP5 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
(* run 3: the counters, and back to the loop head or on *)
paj_run_tok RUN HS HJ5 SHOK BspanS. { awr_ok_tac. }
rebase HS AG. upd_binv HI5 HI5a.
match goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem5) (mrestrict _ (ms_mem ?m1)) |- _ =>
  assert (HK5a : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W4) (ms_mem m1) a = aview SEGS (w_H W4) mem5 a)
  by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end.
clear_frames. clear HI5.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss _ =>
assert (F21 : ew Ev 21 = Z_to_bv 64 p) by (rewrite AG by lia; exact E21);
assert (F24 : ew Ev 24 = Z_to_bv 64 3) by (rewrite AG by lia; exact E24);
idtac end.
assert (HSL5 : slots (mrestrict (w_H W4) mem5) c).
{ destruct HSL as [HS16 HS24]. split;
  (eapply (val_mem_aview_kept_x SEGS (w_H W2) (w_H W4) mem2 mem5); [|eassumption]);
  intros x Hx; rewrite HK5, HK4b, HK4a, HK4, HK1 by lia; reflexivity. }
clear HSL.
psrr_branch_tok RUN BR HS SHOK BspanS.
- rewrite branch_ne_U, (U_atom_off _ 21 p 1 F21), (U_atom _ 24 3 F24) in Hc by lia.
  assert (Hp1 : p + 1 <> 3) by (destruct (Z.eqb_spec (p + 1) 3); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10340. { awr_ok_tac. }
  rebase HS AG. upd_binv HI5a HI6.
  match goal with HFr : frame_of ?Eo ?rs (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |- _ =>
    assert (HK6 : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W4) (ms_mem m1) a = aview SEGS (w_H W4) (ms_mem m0) a)
    by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end.
  clear_frames.
  pmkst HS. apply SRr_ret. unfold I2post.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [replace (p + 1 =? 3) with false by (symmetry; apply Z.eqb_neq; exact Hp1); reflexivity|].
  split; [exact HI6|].
  split; [unfold i2regs; repeat split; first [regs_close HS AG E | r20_close HS AG E20 c p]|].
  destruct HSL5 as [HS16 HS24]. split;
  (eapply (val_mem_aview_kept_x SEGS (w_H W4) (w_H W4) mem5); [|eassumption]);
  intros x Hx; rewrite HK6, HK5a by lia; reflexivity.
- rewrite branch_ne_U, (U_atom_off _ 21 p 1 F21), (U_atom _ 24 3 F24) in Hc by lia.
  assert (Hp1 : p + 1 = 3) by (destruct (Z.eqb_spec (p + 1) 3); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10456. { awr_ok_tac. }
  rebase HS AG. upd_binv HI5a HI6.
  match goal with HFr : frame_of ?Eo ?rs (mrestrict _ (ms_mem ?m0)) (mrestrict _ (ms_mem ?m1)) |- _ =>
    assert (HK6 : forall a, FR <= a < FR + 36 -> aview SEGS (w_H W4) (ms_mem m1) a = aview SEGS (w_H W4) (ms_mem m0) a)
    by (intros a Ha; apply (aview_kept_out Eo rs _ _ _ HFr a ltac:(lia)); nowin) end.
  clear_frames.
  pmkst HS. apply SRr_ret. unfold I2post.
  lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
  exists ly4, S4, (ms_regs m1), (ms_mem m1), mdx end.
  split; [replace (p + 1 =? 3) with true by (symmetry; apply Z.eqb_eq; exact Hp1); reflexivity|].
  split; [exact HI6|].
  split; [unfold i2regs; repeat split; first [regs_close HS AG E | r20_close HS AG E20 c p]|].
  destruct HSL5 as [HS16 HS24]. split;
  (eapply (val_mem_aview_kept_x SEGS (w_H W4) (w_H W4) mem5); [|eassumption]);
  intros x Hx; rewrite HK6, HK5a by lia; reflexivity.
Qed.
Definition saved_extra : list word := map (fun p => getr regs (Z_to_bv 5 (Z.of_nat (snd p)))) SAVED.
Definition ss_epi : sstate := mkSS 10504 sr_atoms
[YP09.mkRegion (Some 2%nat) 1528 1632 0 0
 [YP09.mkChunk 1624 (CVal 8 (SOff 32 0)); YP09.mkChunk 1616 (CVal 8 (SOff 33 0)); YP09.mkChunk 1608 (CVal 8 (SOff 34 0));
  YP09.mkChunk 1600 (CVal 8 (SOff 35 0)); YP09.mkChunk 1592 (CVal 8 (SOff 36 0)); YP09.mkChunk 1584 (CVal 8 (SOff 37 0));
  YP09.mkChunk 1576 (CVal 8 (SOff 38 0)); YP09.mkChunk 1568 (CVal 8 (SOff 39 0)); YP09.mkChunk 1560 (CVal 8 (SOff 40 0));
  YP09.mkChunk 1552 (CVal 8 (SOff 41 0)); YP09.mkChunk 1544 (CVal 8 (SOff 42 0)); YP09.mkChunk 1536 (CVal 8 (SOff 43 0));
  YP09.mkChunk 1528 (CVal 8 (SOff 44 0))]] None (mkFacts [] [] []).
Lemma sv_saved : forall E j, (j < 13)%nat -> ew E (32 + j) = nth j saved_extra (Z_to_bv 64 0) ->
sv_denot E (SOff (32 + j) 0) = Z_to_bv 64 (bv_unsigned (nth j saved_extra (Z_to_bv 64 0))).
Proof. intros E j Hj H. cbn [sv_denot]. rewrite H, Z.add_0_r. reflexivity. Qed.
Lemma reg_lit : forall n : Z, 0 <= n < 32 -> Z_to_bv 5 n = Z_to_bv 5 n.
Proof. reflexivity. Qed.
(* the epilogue: the callee-saved registers come back from sp+1528.., and the
   call returns its row count *)
Lemma epi : forall W2 ly2 S2 regs2 mem2 md2,
binv W2 ly2 S2 mem2 md2 (map bv_unsigned (SWEEP base (Z.to_nat w) vals)) ->
getr regs2 2 = w64 FR -> getr regs2 3 = w64 (as_gp B) -> getr regs2 4 = w64 (as_tp B) -> getr regs2 20 = w64 (sweep_rows w) ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10504)) mem2 (seg_rom SEGS)) md2)
(TBP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Proof.
intros W2 ly2 S2 regs2 mem2 md2 HI R2 R3 R4 R20.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx).
pose proof HI as (HJ & Hfr & Hbl & HKe & Hsv & Hrw & Hlen & Hfs).
remember (Eimg (Ereg regs2 saved_extra)) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 13)%nat -> ew E (32 + j) = nth j saved_extra (Z_to_bv 64 0)) by (intros j Hj; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite R20 in E20.
unfold w64 in E2, E3, E4, E20.
assert (HS : st_ok_pi SEGS VAL E ss_epi (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10504)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  unfold bgs_saved in Hsv.
  repeat (apply Forall_cons; [|]); [..|apply Forall_nil];
  lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?off (CVal 8 (SOff ?n 0))) =>
    let j := eval vm_compute in (n - 32)%nat in
    let r := eval vm_compute in (snd (nth j SAVED (0, 0%nat))) in
    pose proof (proj1 (Forall_forall _ _) Hsv (off, r) ltac:(cbn; tauto)) as Hv; cbn [fst snd] in Hv;
    apply (chunk_ok_val SEGS E _ FR off 8 (SOff n 0) (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat r)))));
    [ cbn [sv_denot]; change n with (32 + j)%nat; rewrite EX by lia; rewrite Z.add_0_r; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as Hq; exact Hq
    | cbn; lia | exact Hv ] end.
- cbn. tauto.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
clear HE EE.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
paj_run_tok RUN HS HJ SHOK BspanS. { awr_ok_tac. }
upd_binv HI HI1. clear_frames.
assert (EX2 : forall j, (j < 13)%nat -> ew E (32 + j) = nth j saved_extra (Z_to_bv 64 0)) by exact EX.
lazymatch goal with HS : st_ok_pi _ _ ?Ev ?ssx (restrict _ ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ |- _ =>
eapply (RET W2 _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)); intros mat';
exists ly2, S2, (ms_regs msc), (ms_mem msc), (with_vm_backing (m_vm_lazy mdx) mat' mdx), (sweep_rows w) end.
pose proof HI1 as (HJ1 & _ & _ & HK1 & _ & HR1 & _).
split.
{ prreg HS (1%bv : bv 5) R1. rewrite R1. pose proof (EX2 0%nat ltac:(lia)) as H2. cbn [Nat.add] in H2. rewrite H2. cbn [nth saved_extra SAVED map snd].
  replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Hra. reflexivity. }
split; [apply (ajournal_materialize SEGS B LAWS Hsegs); unfold EV_BGS, EV_STAMP, EV_LAY; rewrite Z.add_0_r; exact HJ1|].
split.
{ apply aregs_preserved_eqs.
  all: lazymatch goal with |- getr _ ?r = getr regs ?r =>
    let H := fresh "Rr" in prreg HS r H; rewrite H; clear H;
    first [ rewrite E3; exact (eq_sym Hgp)
          | rewrite E4; exact (eq_sym Htp)
          | rewrite E2, unsigned_lit_small by lia; replace (spZ regs - 1632 + 1632) with (bv_unsigned (getr regs 2)) by (unfold spZ; lia); apply Z_to_bv_bv_unsigned
          | lazymatch goal with |- ew _ ?n = _ =>
              let j := eval vm_compute in (n - 32)%nat in
              pose proof (EX2 j ltac:(cbv; lia)) as H2; cbn [Nat.add] in H2; rewrite H2; clear H2;
              cbn [nth saved_extra SAVED map snd]; f_equal; apply bv_eq; reflexivity end ] end. }
split; [exact Hfr|]. split; [exact Hbl|]. split; [exact Hfs|].
split; [prreg HS (10%bv : bv 5) R10; rewrite R10, E20; reflexivity|].
split; [apply (tcj_kept_E _ _ _ _ _ _ _ _ _ _ HK1); intros a Ha; split; [exact HOK | exact Ha]|].
left. split; [exact HOK|]. split; [reflexivity|]. exact HR1.
Qed.
Definition oregs (R : bvmap 5 word) (c : Z) : Prop :=
getr R 2 = w64 FR /\ getr R 3 = w64 (as_gp B) /\ getr R 4 = w64 (as_tp B) /\ getr R 8 = w64 w /\ getr R 9 = w64 base /\
getr R 10 = w64 c /\ getr R 11 = w64 (3 * c + 8) /\ getr R 18 = w64 s /\ getr R 22 = w64 34 /\ getr R 24 = w64 3 /\
getr R 25 = w64 SBV /\ getr R 26 = w64 (V + 3 * c) /\ getr R 27 = w64 (V + 3 * c).
Definition ss_o1 : sstate := mkSS 10308 sr_atoms [YP09.mkRegion (Some 2%nat) 16 32 16 32 []] None
(mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition ss_o2 : sstate := mkSS 10456 sr_atoms
[YP09.mkRegion (Some 2%nat) 16 32 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 24 (CVal 8 (SOff 33 0))]] None
(mkFacts [] [] []).
Lemma outer : forall n c W2 ly2 S2 regs2 mem2 md2, Z.of_nat n = w - c -> 1 <= c < w -> binv W2 ly2 S2 mem2 md2 (prefixZ c) -> oregs regs2 c ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10308)) mem2 (seg_rom SEGS)) md2)
(TBP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Proof.
intros ni; induction ni as [|ni IH]; intros c W2 ly2 S2 regs2 mem2 md2 Hni Hcw HI (R2 & R3 & R4 & R8 & R9 & R10 & R11 & R18 & R22 & R24 & R25 & R26 & R27); [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold sweep_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & _ & _ & _ & _ & _ & Hrwin & _). unfold sweep_rows in Hs47, Hrwin.
destruct (vals_at W2 ly2 S2 mem2 md2 _ HI) as (_ & _ & HV0 & HV47 & _ & _).
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite R10 in E10.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite R11 in E11.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 22%nat 22%bv eq_refl) as E22. rewrite R22 in E22.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite R24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite R26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite R27 in E27.
unfold w64 in E2, E3, E4, E8, E9, E10, E11, E18, E22, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL E ss_o1 (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10308)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_o1. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply (win_present W2 ly2 S2 mem2 md2 _ (FR + o) HI). lia.
- cbn. tauto.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, unsigned_lit_small by lia. change (2 ^ 4) with 16.
  split; [|exact I]. split; [lia|]. split; [|lia]. replace (spZ regs - 1632) with (spZ regs - 1632 - 0) by lia. apply m16; [exact Hal16 | reflexivity | reflexivity]. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
clear HE EE.
paj_run_to_tok RUNTO HS HJ SHOK BspanS 10340.
{ eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - 1632)); [reflexivity | rewrite E2; apply unsigned_lit_small; lia | | apply awr_ok_nil].
  cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. left. lia. }
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem2) (mrestrict _ (ms_mem ?m1)), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _, HG : mem_grows _ _ |- _ =>
assert (HI1 : binv W2 ly2 S2 (ms_mem m1) mdx (prefixZ c)) by
(eapply (binv_frame W2 ly2 S2 mem2 md2 (prefixZ c)); [exact HI | exact HJ | intros a Ha Ho; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); winout | exact HG]) end.
clear_frames.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ss (restrict _ ?msx) =>
let r := eval vm_compute in (nth 0 (ss_mem ss) got_regionP) in
pose proof (st_ok_pi_region_nth Ev ss (restrict (w_H W2) msx) 0 r HS ltac:(vm_compute; reflexivity)) as RG end.
cbn [ms_mem restrict] in RG.
assert (HSL : slots (mrestrict (w_H W2) (ms_mem ms)) c).
{ split.
  - apply (field_of_region E _ 2 FR _ 16 32 16 32 16 8 (SOff 10 0) c RG); [rewrite E2; apply unsigned_lit_small; lia | cbn; tauto | cbn [sv_denot]; rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia].
  - apply (field_of_region E _ 2 FR _ 16 32 16 32 24 8 (SOff 11 0) (3 * c + 8) RG); [rewrite E2; apply unsigned_lit_small; lia | cbn; tauto | cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia]. }
clear RG.
assert (HR : i2regs (ms_regs ms) c 0).
{ unfold i2regs. repeat split; try (regs_close HS AG E).
  - pose proof (st_ok_pi_restrict_reg _ E _ _ (19%bv : bv 5) HS) as H.
    change (sr_get (ss_regs _) (19%bv : bv 5)) with (SAlu ALU_ADD (SOff 18 0) (SMd M_MUL (SOff 11 0) (SOff 22 0))) in H.
    cbn [ms_regs restrict mkst] in H. rewrite H, denot_lit_U. unfold w64. f_equal.
    assert (UM : U E (SMd M_MUL (SOff 11 0) (SOff 22 0)) = (3 * c + 8) * 34).
    { unfold U. rewrite (denot_mul_hw E 11 22 (3 * c + 8) 34 E11 E22) by lia. apply unsigned_lit_small. lia. }
    rewrite (U_add_small E (SOff 18 0) (SMd M_MUL (SOff 11 0) (SOff 22 0)) s ((3 * c + 8) * 34)); [lia | apply U_atom; [exact E18 | lia] | exact UM | lia | lia | lia].
  - pose proof (st_ok_pi_restrict_reg _ E _ _ (22%bv : bv 5) HS) as H.
    change (sr_get (ss_regs _) (22%bv : bv 5)) with (SAlu ALU_AND (SAlu ALU_ADD (SOff 9 0) (SOff 10 0)) (SLit 255)) in H.
    cbn [ms_regs restrict mkst] in H. rewrite H, denot_lit_U. unfold w64. f_equal.
    rewrite U_and_lit by lia.
    rewrite (U_add_small E (SOff 9 0) (SOff 10 0) base c); [| apply U_atom; [exact E9 | lia] | apply U_atom; [exact E10 | lia] | lia | lia | lia].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
pmkst HS.
(* the inner loop: three rows *)
pose proof (len_prefixZ c ltac:(lia)) as Hl0.
eapply SRr_bind.
{ eapply (row2a c 0 (prefixZ c) W2 ly2 S2 _ _ _ Hcw ltac:(lia) HI1 HR HSL). }
cbv beta. intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HI3 & HR3 & R23 & HSL3).
eapply SRr_bind.
{ eapply (row2b c 0 (prefixZ c) W3 ly3 S3 _ _ _ Hcw ltac:(lia) HI3 ltac:(lia) HR3 R23 HSL3). }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HI4 & HR4 & HSL4).
change (0 + 1 =? 3) with false. cbv iota. change (0 + 1) with 1 in HR4.
eapply SRr_bind.
{ eapply (row2a c 1 _ W4 ly4 S4 _ _ _ Hcw ltac:(lia) HI4 HR4 HSL4). }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HI5 & HR5 & R23' & HSL5).
eapply SRr_bind.
{ eapply (row2b c 1 _ W5 ly5 S5 _ _ _ Hcw ltac:(lia) HI5 ltac:(rewrite length_app, len_GAz; lia) HR5 R23' HSL5). }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HI6 & HR6 & HSL6).
change (1 + 1 =? 3) with false. cbv iota. change (1 + 1) with 2 in HR6.
eapply SRr_bind.
{ eapply (row2a c 2 _ W6 ly6 S6 _ _ _ Hcw ltac:(lia) HI6 HR6 HSL6). }
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HI7 & HR7 & R23'' & HSL7).
eapply SRr_bind.
{ eapply (row2b c 2 _ W7 ly7 S7 _ _ _ Hcw ltac:(lia) HI7 ltac:(rewrite !length_app, !len_GAz; lia) HR7 R23'' HSL7). }
cbv beta. intros W8 c8 _ (ly8 & S8 & regs8 & mem8 & md8 & -> & HI8 & HR8 & HSL8).
change (2 + 1 =? 3) with true. cbv iota. change (2 + 1) with 3 in HR8.
rewrite prefix_step in HI8 by lia.
clear HI1 HI3 HI4 HI5 HI6 HI7 HR HR3 HR4 HR5 HR6 HR7 HSL HSL3 HSL4 HSL5 HSL6 HSL7 R23 R23' R23'' HS SHOK AG HEI.
clear E2 E3 E4 E8 E9 E10 E11 E18 E22 E24 E25 E26 E27.
(* the end of the channel: c and its row index back from sp+16 and sp+24 *)
destruct HR8 as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q24 & Q25 & Q26 & Q27).
destruct HSL8 as [HS16 HS24].
pose proof HI8 as (HJ8 & _).
remember (Eimg (Ereg regs8 [Z_to_bv 64 c; Z_to_bv 64 (3 * c + 8)])) as Eo2 eqn:HE.
assert (HEI : img_env VAL A_LIM Eo2) by (subst Eo2; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Eo2 n = getr regs8 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite Q2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite Q3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite Q4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite Q8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite Q9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite Q18 in E18.
pose proof (EE 20%nat 20%bv eq_refl) as E20. rewrite Q20 in E20.
pose proof (EE 21%nat 21%bv eq_refl) as E21. rewrite Q21 in E21.
pose proof (EE 24%nat 24%bv eq_refl) as E24. rewrite Q24 in E24.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite Q25 in E25.
pose proof (EE 26%nat 26%bv eq_refl) as E26. rewrite Q26 in E26.
pose proof (EE 27%nat 27%bv eq_refl) as E27. rewrite Q27 in E27.
assert (E32 : ew Eo2 32 = Z_to_bv 64 c) by (subst Eo2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs8 _ 0)).
assert (E33 : ew Eo2 33 = Z_to_bv 64 (3 * c + 8)) by (subst Eo2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs8 _ 1)).
unfold w64 in E2, E3, E4, E8, E9, E18, E20, E21, E24, E25, E26, E27.
assert (HS : st_ok_pi SEGS VAL Eo2 ss_o2 (restrict (w_H W8) (mkst regs8 (Z_to_bv 64 (BASE + 10456)) mem8 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_o2. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + apply (chunk_ok_val SEGS Eo2 _ FR 16 8 (SOff 32 0) c); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HS16].
  + apply (chunk_ok_val SEGS Eo2 _ FR 24 8 (SOff 33 0) (3 * c + 8)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HS24].
- cbn. tauto.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS BxL [] Eo2 (mrestrict (w_H W8) mem8)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew Eo2 n = ew Eo2 n) by reflexivity.
clear HE EE.
paj_run_tok RUN HS HJ8 SHOK BspanS. { awr_ok_tac. }
upd_binv HI8 HI9. clear_frames.
psrr_branch_tok RUN BR HS SHOK BspanS.
- rewrite branch_ne_U, (U_atom_off _ 32 c 1 E32), (U_atom _ 8 w E8) in Hc by lia.
  assert (Hc1 : c + 1 <> w) by (destruct (Z.eqb_spec (c + 1) w); [discriminate | lia]).
  paj_run_to_tok RUNTO HS HJ8 SHOK BspanS 10308. { awr_ok_tac. }
  upd_binv HI9 HI10. clear_frames.
  pmkst HS.
  eapply (IH (c + 1)); [lia | lia | exact HI10 |].
  unfold oregs. repeat split; try (regs_close HS AG Eo2).
  pose proof (st_ok_pi_restrict_reg _ Eo2 _ _ (11%bv : bv 5) HS) as H.
  change (sr_get (ss_regs _) (11%bv : bv 5)) with (SAluw ALU_ADD (SOff 33 0) (SOff 21 0)) in H.
  cbn [ms_regs restrict mkst] in H. rewrite H, denot_lit_U. unfold w64. f_equal.
  rewrite (U_addw_small Eo2 (SOff 33 0) (SOff 21 0) (3 * c + 8) 3); [lia | apply U_atom; [exact E33 | lia] | apply U_atom; [exact E21 | lia] | lia | lia | lia].
- rewrite branch_ne_U, (U_atom_off _ 32 c 1 E32), (U_atom _ 8 w E8) in Hc by lia.
  assert (Hc1 : c + 1 = w) by (destruct (Z.eqb_spec (c + 1) w); [lia | discriminate]).
  paj_run_to_tok RUNTO HS HJ8 SHOK BspanS 10504. { awr_ok_tac. }
  upd_binv HI9 HI10. clear_frames.
  pmkst HS.
  replace (c + 1) with w in HI10 by lia. unfold prefixZ in HI10. rewrite BgsLoop.prefixB_SWEEP in HI10.
  eapply (epi _ _ _ _ _ _ HI10); unfold sweep_rows; regs_close HS AG Eo2.
Qed.
(* the second segment: GRANT_HEAD_MARK and GRANT_GROUPB, then `w < 2` *)
Definition ss_m : sstate := mkSS 10236 sr_atoms [] None (mkFacts [] [] []).
Lemma seg_mark : forall W2 ly2 S2 regs2 mem2 md2, binv W2 ly2 S2 mem2 md2
(((HEAD_ACK34z ++ GAz base 0 (vz vals (Z.to_nat 0))) ++ GAz base 1 (vz vals (Z.to_nat 1))) ++ GAz base 2 (vz vals (Z.to_nat 2))) ->
l1regs regs2 3 ->
SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 10236)) mem2 (seg_rom SEGS)) md2)
(TBP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Proof.
intros W2 ly2 S2 regs2 mem2 md2 HI (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R20 & R21 & R22 & R23 & R25 & R26 & R27).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
pose proof HOK as (Hs0 & HVn0 & Hw1 & Hbw & Hmx). unfold sweep_rows in Hmx.
destruct (HROWS HOK) as (_ & Hs47 & Rimg & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Hrwin & _). unfold sweep_rows in Hs47, Hrwin, Hb2.
destruct (vals_at W2 ly2 S2 mem2 md2 _ HI) as (_ & _ & HV0 & HV47 & _ & _).
pose proof HI as (HJ & _).
remember (Eimg (Ereg regs2 [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs2 r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
pose proof (EE 2%nat 2%bv eq_refl) as E2. rewrite R2 in E2.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite R3 in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite R4 in E4.
pose proof (EE 8%nat 8%bv eq_refl) as E8. rewrite R8 in E8.
pose proof (EE 9%nat 9%bv eq_refl) as E9. rewrite R9 in E9.
pose proof (EE 18%nat 18%bv eq_refl) as E18. rewrite R18 in E18.
pose proof (EE 19%nat 19%bv eq_refl) as E19. rewrite R19 in E19.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
unfold w64 in E2, E3, E4, E8, E9, E18, E19, E25.
assert (EM : ew E (A_OBJ A_MARK) = Z_to_bv 64 (VAL (A_OBJ A_MARK))) by (apply (img_env_atomP E (A_OBJ A_MARK) HEI); unfold A_OBJ, A_MARK, A_TEXT, A_LIM; lia).
assert (EG : ew E (A_OBJ A_GB) = Z_to_bv 64 (VAL (A_OBJ A_GB))) by (apply (img_env_atomP E (A_OBJ A_GB) HEI); unfold A_OBJ, A_GB, A_TEXT, A_LIM; lia).
assert (HS : st_ok_pi SEGS VAL E ss_m (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 10236)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_m. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I | split; exact I]. }
assert (SHOK : sh_ok SEGS BxL [] E (mrestrict (w_H W2) mem2)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
clear HE EE.
paj_run_tok RUN HS HJ SHOK BspanS. { awr_ok_tac. }
upd_binv HI HI1. clear_frames.
assert (Hl3 : Z.of_nat (length (((HEAD_ACK34z ++ GAz base 0 (vz vals (Z.to_nat 0))) ++ GAz base 1 (vz vals (Z.to_nat 1))) ++ GAz base 2 (vz vals (Z.to_nat 2)))) = 136)
by (rewrite !length_app, !len_GAz; reflexivity).
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp. rewrite ?unsigned_lit_small in Ra0 by lia.
change (ew E 262) with (ew E (A_OBJ A_MARK)) in Ra1. rewrite EM in Ra1.
pmkst HS.
pose proof (blk_off_imgP _ _ _ _ _ _ b m (proj1 (proj1 HI1)) ltac:(rewrite (proj1 (proj2 (proj2 HI1))); exact Hbm)) as Hoff.
unfold off_img in Hoff.
destruct (ro_read_ok_glob SEGS B GL ly2 S2 W2 _ _ (VAL (A_OBJ A_MARK)) 34 (VAL (A_OBJ A_MARK)) 34 HGL HIN_MARK HIMGSH (proj1 (proj1 HI1)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [MRa MHl].
eapply (call_cpy W2 ly2 S2 _ _ _ _ 10260 (VAL (A_OBJ A_MARK)) HEAD_MARK34z _ HI1);
change (length HEAD_MARK34z) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold sweep_rows; rewrite ?Hl3;
[ lia | lia | exact (HMARK _ _ (arod_binv _ _ _ _ _ _ HI1)) | lia | lia | lia | unfold amem_range, kLowMemEnd; lia | unfold ESTACK; lia
| exact MRa | exact MHl | rewrite Ra0; unfold w64; f_equal; lia | exact Ra1 | exact Ra2
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem3 md3 regs3 HI3 _ HP3. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI1 HJ SHOK MRa MHl.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
paj_run_tok RUN HS HJ3 SHOK BspanS. { awr_ok_tac. }
upd_binv HI3 HI4. clear_frames.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp. rewrite ?unsigned_lit_small in Ra0 by lia.
lazymatch type of Ra1 with context [ew ?Ex 260] =>
assert (EG' : ew Ex (A_OBJ A_GB) = Z_to_bv 64 (VAL (A_OBJ A_GB))) by (apply img_env_atomP; [assumption | unfold A_OBJ, A_GB, A_TEXT, A_LIM; lia]);
change (ew Ex 260) with (ew Ex (A_OBJ A_GB)) in Ra1 end.
rewrite EG' in Ra1.
pmkst HS.
destruct (ro_read_ok_glob SEGS B GL ly2 S2 W2 _ _ (VAL (A_OBJ A_GB)) 204 (VAL (A_OBJ A_GB)) 204 HGL HIN_GB HIMGSH (proj1 (proj1 HI4)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [GRa GHl].
assert (Hl4 : Z.of_nat (length ((((HEAD_ACK34z ++ GAz base 0 (vz vals (Z.to_nat 0))) ++ GAz base 1 (vz vals (Z.to_nat 1))) ++ GAz base 2 (vz vals (Z.to_nat 2))) ++ HEAD_MARK34z)) = 170)
by (rewrite length_app, Nat2Z.inj_add, Hl3; reflexivity).
eapply (call_cpy W2 ly2 S2 _ _ _ _ 10280 (VAL (A_OBJ A_GB)) GBallz _ HI4);
change (length GBallz) with 204%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold sweep_rows; rewrite ?Hl4;
[ lia | lia | exact (HGB _ _ (arod_binv _ _ _ _ _ _ HI4)) | lia | lia | lia | unfold amem_range, kLowMemEnd; lia | unfold ESTACK; lia
| exact GRa | exact GHl | rewrite Ra0; unfold w64; f_equal; lia | exact Ra1 | exact Ra2
| unfold spZ; rewrite Rsp, unsigned_lit_small by lia; reflexivity | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem5 md5 regs5 HI5 _ HP5. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI3 HI4 HJ3 SHOK GRa GHl.
pose proof (proj1 HI5) as HJ5.
reseat HS HJ5 HP5 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
rewrite prefix_one in HI5.
paj_run_tok RUN HS HJ5 SHOK BspanS. { awr_ok_tac. }
upd_binv HI5 HI6. clear_frames. clear HI5.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
assert (F8 : ew Ev 8 = Z_to_bv 64 w) by (rewrite AG by lia; exact E8) end.
psrr_branch_tok RUN BR HS SHOK BspanS.
- cbn [sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, F8 in Hc. rewrite blt_lit in Hc by lia.
  assert (Hw : w = 1) by (apply Z.ltb_lt in Hc; lia).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10504. { awr_ok_tac. }
  upd_binv HI6 HI7. clear_frames.
  pmkst HS.
  replace (prefixZ 1) with (map bv_unsigned (SWEEP base (Z.to_nat w) vals)) in HI7
    by (unfold prefixZ; rewrite BgsLoop.prefixB_SWEEP; rewrite Hw; reflexivity).
  eapply (epi _ _ _ _ _ _ HI7); unfold sweep_rows; regs_close HS AG E.
- cbn [sv_denot] in Hc. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, F8 in Hc. rewrite blt_lit in Hc by lia.
  assert (Hw : 2 <= w) by (apply Z.ltb_ge in Hc; lia).
  paj_run_to_tok RUNTO HS HJ5 SHOK BspanS 10308. { awr_ok_tac. }
  upd_binv HI6 HI7. clear_frames.
  pmkst HS.
  eapply (outer (Z.to_nat (w - 1)) 1 _ _ _ _ _ _ ltac:(lia) ltac:(lia) HI7).
  unfold oregs. repeat split; regs_close HS AG E.
Qed.
End ok.
Ltac bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR :=
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |];
upd_out; clear_fr;
lazymatch goal with HS' : st_ok_pi _ _ _ ?ssx (restrict _ ?msc), HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?msc) ?mdx _ |- _ =>
let R1 := fresh "R1" in let R10 := fresh "R10" in let mat' := fresh "mat" in
prreg HS' (1%bv : bv 5) R1; prreg HS' (10%bv : bv 5) R10;
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)); intros mat';
exists lyc, Sc, (ms_regs msc), (ms_mem msc), (with_vm_backing (m_vm_lazy mdx) mat' mdx), (-1);
split; [cbn [ms_regs]; rewrite R1; rewrite ?E1; rewrite Hra; reflexivity|];
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); unfold EV_BGS, EV_STAMP, EV_LAY; rewrite Z.add_0_r; exact HJ'|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs _ HS'); [exact HAE | vm_compute; reflexivity]|];
split; [reflexivity|]; split; [reflexivity|]; split; [exists (st_fs Sc); destruct Sc; reflexivity|];
split; [rewrite R10; unfold w64; first [reflexivity | apply bv_eq; reflexivity]|];
split; [eapply kept_out; eassumption|];
right; split; [exact Hnb|]; split; [reflexivity|]; split;
[ let a := fresh "a" in let Ha := fresh "Ha" in let Hw0 := fresh "Hw0" in intros a Ha Hw0;
  lazymatch goal with Ho : forall a, 0 <= a < 2 ^ 64 -> _ -> aview _ _ _ a = _ |- _ => apply Ho end; lia
| let b0 := fresh "b" in let m0 := fresh "m" in let i := fresh "i" in let Hin := fresh "Hin" in let Hi := fresh "Hi" in
  intros b0 m0 i Hin Hi; destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m0 HAR Hin) as (_ & ? & ? & _);
  lazymatch goal with Ho : forall a, 0 <= a < 2 ^ 64 -> _ -> aview _ _ _ a = _ |- _ => apply Ho end; lia ]
end.
(* the entry: the frame, the five refusals, then GRANT_HEAD_ACK into the first row *)
Lemma entry : SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_build_grant_sweep)) memc (seg_rom SEGS)) mdc)
(TBP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Proof.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_base_lo as HBLO. pose proof pa_B_ok as HBASE.
pose proof stk_bounds as (B1 & B2 & B3 & B4 & B5 & B6 & B7).
pose proof HJc as HJ.
pose proof HJc as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5). assert (WS : TBGS_STK = 6016) by reflexivity.
remember (Eimg (Ereg regs [Z_to_bv 64 SBV])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 SBV]) E) by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SBV) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite (EE 2%nat 2%bv eq_refl); unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (EE 1%nat 1%bv eq_refl) as E1.
pose proof (EE 3%nat 3%bv eq_refl) as E3. rewrite Hgp in E3.
pose proof (EE 4%nat 4%bv eq_refl) as E4. rewrite Htp in E4.
pose proof (EE 10%nat 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (EE 11%nat 11%bv eq_refl) as E11. rewrite H11 in E11.
pose proof (EE 12%nat 12%bv eq_refl) as E12. rewrite H12 in E12.
pose proof (EE 13%nat 13%bv eq_refl) as E13. rewrite H13 in E13.
pose proof (EE 14%nat 14%bv eq_refl) as E14. rewrite H14 in E14.
unfold w64 in E3, E4, E10, E11, E12, E13, E14.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; apply unsigned_lit_small; lia).
assert (EG1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (apply (img_env_atomP E (A_OBJ 1) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (EG32 : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (apply (img_env_atomP E (A_OBJ 32) HEI); unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 1 ltac:(lia)) as HO1. pose proof (pa_obj_img 32 ltac:(lia)) as HO32.
aconstsF HJ Kgot Kcell Kguar Kuar.
assert (HS : st_ok_pi SEGS VAL E ss_bgs (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_ctrl_build_grant_sweep)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_bgs. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region, got_regionP, bcell_regionP.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + cbn [base_val]. rewrite EG1, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
    [cbn [sv_denot]; rewrite EG32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia |].
    rewrite Z.add_0_r. exact Kgot.
  + cbn [base_val]. rewrite EG32, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 (SOff 32 0) SHADOW_OFF);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; lia | lia |].
    rewrite Z.add_0_r. exact Kcell.
- apply pairwise_disjoint_of_extents. unfold stack_region, got_regionP, bcell_regionP, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, EG1, EG32, !unsigned_lit_small by lia.
  pose proof (pal_got_cell B TL) as HgcD.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite Usp, E32, !unsigned_lit_small by (unfold SBV; lia). change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SBV. repeat split; lia. }
assert (SHOK : sh_ok SEGS BxS [] E (mrestrict (w_H W) memc)) by constructor.
assert (AG : forall n, (n < 33)%nat -> ew E n = ew E n) by reflexivity.
assert (Hout : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 1632 <= a < spZ regs) -> aview SEGS (w_H W) memc a = aview SEGS (w_H W) memc a)
  by (intros; reflexivity).
assert (Hgr : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
clear HE.
(* the frame and the saves, up to `blez a3` *)
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
psrr_branch_tok RUN BR HS SHOK BspanS.
{ (* w <= 0 *)
  cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E13 in Hc. rewrite bge_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.ltb_spec 0 w); [discriminate | unfold bgs_ok; lia]).
  bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR. }
cbn [sv_denot] in Hc. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, E13 in Hc. rewrite bge_lit in Hc by lia.
assert (Hw1 : 1 <= w) by (destruct (Z.ltb_spec 0 w); [lia | discriminate]). clear Hc.
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
psrr_branch_tok RUN BR HS SHOK BspanS.
{ (* s = 0 *)
  rewrite branch_eq_U, (U_atom E 10 s E10), U_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.eqb_spec s 0); [unfold bgs_ok; lia | discriminate]).
  bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR. }
rewrite branch_eq_U, (U_atom E 10 s E10), U_lit in Hc by lia.
assert (Hs0 : s <> 0) by (destruct (Z.eqb_spec s 0); [discriminate | lia]). clear Hc.
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
psrr_branch_tok RUN BR HS SHOK BspanS.
{ (* V = 0 *)
  rewrite branch_eq_U, (U_atom E 14 V E14), U_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.eqb_spec V 0); [unfold bgs_ok; lia | discriminate]).
  bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR. }
rewrite branch_eq_U, (U_atom E 14 V E14), U_lit in Hc by lia.
assert (HV0 : V <> 0) by (destruct (Z.eqb_spec V 0); [discriminate | lia]). clear Hc.
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
assert (UW : U E (SOff 13 0) = w) by (apply (U_atom E 13 w E13); lia).
assert (UB : U E (SOff 12 0) = base) by (apply (U_atom E 12 base E12); lia).
psrr_branch_tok RUN BR HS SHOK BspanS.
{ (* 48 < base + w *)
  rewrite branch_ltu_U, U_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w).
  { destruct (Z_lt_le_dec (w + base) (2 ^ 31)) as [Hsm | Hbg].
    - rewrite (U_addw_small E (SOff 13 0) (SOff 12 0) w base UW UB) in Hc by lia.
      destruct (Z.ltb_spec 48 (w + base)); [unfold bgs_ok; lia | discriminate].
    - unfold bgs_ok; lia. }
  bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR. }
rewrite branch_ltu_U, U_lit in Hc by lia.
assert (Hbw : base + w <= 48).
{ destruct (Z_lt_le_dec (w + base) (2 ^ 31)) as [Hsm | Hbg].
  - rewrite (U_addw_small E (SOff 13 0) (SOff 12 0) w base UW UB) in Hc by lia.
    destruct (Z.ltb_spec 48 (w + base)); [discriminate | lia].
  - pose proof (U_addw_big E (SOff 13 0) (SOff 12 0) w base UW UB ltac:(lia) ltac:(lia) ltac:(lia)) as Hbig.
    destruct (Z.ltb_spec 48 (U E (SAluw ALU_ADD (SOff 13 0) (SOff 12 0)))); [discriminate | lia]. }
clear Hc.
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
assert (UA : U E (SAluw ALU_ADD (SMd M_MUL (SOff 13 0) (SLit 3)) (SLit 8)) = 3 * w + 8).
{ apply (U_addw_small E _ _ (3 * w) 8); [| apply U_lit; lia | lia | lia | lia].
  rewrite U_SMd. cbn [zmd_raw]. rewrite UW, U_lit by lia. rewrite zcanon_id; [lia | unfold M64; lia]. }
assert (D11 : sv_denot E (SOff 11 0) = Z_to_bv 64 mx) by (cbn [sv_denot]; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
psrr_branch_tok RUN BR HS SHOK BspanS.
{ (* mx < 8 + 3w *)
  rewrite D11, (denot_lit_U E (SAluw ALU_ADD (SMd M_MUL (SOff 13 0) (SLit 3)) (SLit 8))), UA, blt_lit in Hc by lia.
  assert (Hnb : ~ bgs_ok s V mx base w) by (destruct (Z.ltb_spec mx (3 * w + 8)); [unfold bgs_ok, sweep_rows; lia | discriminate]).
  bgs_refuse HS HJ SHOK Usp HAE E1 Hnb HAR. }
rewrite D11, (denot_lit_U E (SAluw ALU_ADD (SMd M_MUL (SOff 13 0) (SLit 3)) (SLit 8))), UA, blt_lit in Hc by lia.
assert (Hmx : 3 * w + 8 <= mx) by (destruct (Z.ltb_spec mx (3 * w + 8)); [discriminate | lia]). clear Hc.
assert (Hok : bgs_ok s V mx base w) by (unfold bgs_ok, sweep_rows; lia).
destruct (HROWS Hok) as (Ram & Rs47 & Rimg & _ & _ & _ & (b & m & Hbm & Hb1 & Hb2) & Rwin & _).
unfold sweep_rows in Rs47, Hb2, Rwin.
pose proof (blk_off_imgP _ _ _ _ _ _ b m HAR Hbm) as Hoff. unfold off_img in Hoff.
(* GRANT_HEAD_ACK into the first row *)
paj_run_tok RUN HS HJ SHOK BspanS; [bgs_awr Usp |].
upd_out. clear_fr.
rebase HS AG.
lazymatch type of HS with
| st_ok _ ?Ex ?ssx (restrict ?Hh ?msx) => pose proof (st_ok_region_nth Ex ssx (restrict Hh msx) 0 _ HS eq_refl) as RG
| st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) => pose proof (st_ok_pi_region_nth Ex ssx (restrict Hh msx) 0 _ HS eq_refl) as RG
end.
lazymatch type of RG with region_ok ?a ?b ?c ?r0 => let r1 := eval vm_compute in r0 in change r0 with r1 in RG end.
cbn [ms_mem restrict] in RG.
lazymatch type of RG with region_ok _ ?Ex _ _ =>
assert (Usp0 : bv_unsigned (ew Ex 2) = spZ regs) by (rewrite AG by lia; exact Usp) end.
lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _ |- _ =>
assert (HSV : bgs_saved (mrestrict (w_H W) (ms_mem m1)));
[ unfold bgs_saved, SAVED; repeat apply Forall_cons; try apply Forall_nil; cbv beta; cbn [fst snd];
  lazymatch goal with |- val_mem _ _ (_ + ?off) 8 (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat ?r)))) =>
    replace (spZ regs - 1632 + off) with (spZ regs + (off - 1632)) by lia;
    let od := eval vm_compute in (off - 1632) in change (off - 1632) with od;
    lazymatch type of RG with region_ok _ ?Ex _ _ =>
    apply (field_of_region Ex _ 2 (spZ regs) _ (-1632) 0 (-1632) 0 od 8%N (SOff r 0) _ RG);
    [ exact Usp0 | cbn; tauto
    | cbn [sv_denot]; rewrite Z.add_0_r, (AG r) by lia; rewrite (EE r (Z_to_bv 5 (Z.of_nat r)) eq_refl), Z_to_bv_bv_unsigned; reflexivity
    | pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (Z.of_nat r)))) as Hq; exact Hq | cbn; lia ] end end
| assert (HI1 : binv W lyc Sc (ms_mem m1) mdx []) by (eapply (binv_init Hok); eassumption) ] end.
clear RG.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp. prreg HS (1%bv : bv 5) Rra.
rfact AG E Ra0. rfact AG E Rsp. rfact AG E Rgp. rfact AG E Rtp.
rewrite ?unsigned_lit_small in Ra0 by lia. rewrite (unsigned_lit_small (spZ regs)) in Rsp by lia.
lazymatch type of Ra1 with context [ew ?Ex ?n] =>
assert (EA' : ew Ex (A_OBJ A_ACK) = Z_to_bv 64 (VAL (A_OBJ A_ACK))) by (apply img_env_atomP; [assumption | unfold A_OBJ, A_ACK, A_TEXT, A_LIM; lia]);
change (ew Ex n) with (ew Ex (A_OBJ A_ACK)) in Ra1 end.
rewrite EA' in Ra1.
pmkst HS.
destruct (ro_read_ok_glob SEGS B GL lyc Sc W _ _ (VAL (A_OBJ A_ACK)) 34 (VAL (A_OBJ A_ACK)) 34 HGL HIN_ACK HIMGSH (proj1 (proj1 HI1)) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [ARa AHl].
eapply (call_cpy Hok W lyc Sc _ _ [] _ 10096 (VAL (A_OBJ A_ACK)) HEAD_ACK34z _ HI1);
change (length HEAD_ACK34z) with 34%nat; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; unfold sweep_rows;
[ lia | lia | exact (HACK _ _ ltac:(eapply arod_binv; eassumption)) | lia | lia | lia | unfold amem_range, kLowMemEnd; lia | unfold ESTACK; lia
| exact ARa | exact AHl | rewrite Ra0; unfold w64; f_equal; lia | exact Ra1 | exact Ra2
| unfold spZ at 1; rewrite Rsp, unsigned_lit_small by lia; lia | exact Rgp | exact Rtp | exact Rra | lia | reflexivity |].
intros mem3 md3 regs3 HI3 _ HP3. clear Ra0 Ra1 Ra2 Rsp Rgp Rtp Rra HI1 HJ SHOK ARa AHl.
cbn [app] in HI3.
pose proof (proj1 HI3) as HJ3.
reseat HS HJ3 HP3 (@nil nat) AG ltac:(idtac).
try clear SHOK. mkshok HS SHOK. cbn [ms_mem] in SHOK.
paj_run_to_tok RUNTO HS HJ3 SHOK BspanS 10120. { awr_ok_tac. }
lazymatch goal with HFr : frame_of ?Eo ?rs (mrestrict _ mem3) (mrestrict _ (ms_mem ?m1)), HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_mem ?m1) ?mdx _, HG : mem_grows (mrestrict _ mem3) _ |- _ =>
assert (HI4 : binv W lyc Sc (ms_mem m1) mdx HEAD_ACK34z) by
(eapply (binv_frame Hok W lyc Sc mem3 md3 HEAD_ACK34z); [exact HI3 | exact HJ' | intros a Ha _; apply (aview_kept_out Eo rs _ _ _ HFr a Ha); nowin | exact HG]) end.
clear_frames.
pmkst HS.
(* the first channel's three rows *)
eapply SRr_bind.
{ eapply (row1 Hok 0 HEAD_ACK34z W lyc Sc); [lia | exact HI4 | reflexivity | unfold l1regs; repeat split; regs_close HS AG E]. }
cbv beta. intros W5 c5 _ (ly5 & S5 & regs5 & mem5 & md5 & -> & HI5 & HR5).
change (0 + 1 =? 3) with false. cbv iota. change (0 + 1) with 1 in HR5.
eapply SRr_bind.
{ eapply (row1 Hok 1 _ W5 ly5 S5); [lia | exact HI5 | rewrite length_app, len_GAz; reflexivity | exact HR5]. }
cbv beta. intros W6 c6 _ (ly6 & S6 & regs6 & mem6 & md6 & -> & HI6 & HR6).
change (1 + 1 =? 3) with false. cbv iota. change (1 + 1) with 2 in HR6.
eapply SRr_bind.
{ eapply (row1 Hok 2 _ W6 ly6 S6); [lia | exact HI6 | rewrite !length_app, !len_GAz; reflexivity | exact HR6]. }
cbv beta. intros W7 c7 _ (ly7 & S7 & regs7 & mem7 & md7 & -> & HI7 & HR7).
change (2 + 1 =? 3) with true. cbv iota. change (2 + 1) with 3 in HR7.
exact (seg_mark Hok W7 ly7 S7 _ _ _ HI7 HR7).
Qed.
End w.
Theorem pb_reac_ctrl_build_grant_sweep :
tctrl_build_grant_sweep_spec B (BASE + AF_reac_ctrl_build_grant_sweep) pa_relro_lo pa_relro_hi.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs s mx base w V vals cl
  HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 H14 Rs Rmx Rbase Rw RV Hch Hal16 Hwlo Hwhi Hfr8 HVALS HROWS.
unfold cfg_at, w64. eapply entry; eassumption.
Qed.
End e.
End d.
End b.
