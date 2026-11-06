(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/CrcB.v, with its module paths and module names changed; 697 of its 748 lines of code are new or changed and 463 lines of the source are left out. *)
(* On the Step-1 contract texts (the re-hiding move): the L1 stretch at the re-hiding
   contract: the walk in YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf (ct5_K, the goal patterns), the
   journal at R := YA0nH.wle' SEGS RZ_cf; strcmp by the engine's YGcallMxmn.aj_strcmp_at_xromR (Crt102B_T6.v's
   local copy is deleted) at R, lifted by YA0nH.SRr_SRr' under YSRrG.SRr'_bind, the journal rebased / unbased by the R
   forms YCbqGwild.ajournal_xw_rebaseR / ajournal_xw_unbase0R. *)
(* fuzz_preset, walk of check_round_trip on the #102 pins, IMAGE B' (asan-ubsan d663f82d7f488d30,
   unstripped twin c90d4fa54d43160b), FREE-PIECES-102 Part 7a row T5 (CRT-B-L012): the L1 STRETCH, the at-search head
   B' entry + 0x4f8 (index i; s5 = i + 1, s8 = s10 = &doc->keys[i]) -> `__wrap_strcmp (doc->keys[i], MOD_AT)` at
   + 0x53c -> + 0x540 -> L1 at i + 1 (no hit, i + 1 < doc->n) or L2 (+0x56c: a hit, or i + 1 = doc->n). The six UBSan
   branches to + 0x810 and the shadow report are decided by the symbolic runner. ct5_L1 : CT5_L1_STMT
   (Crt102B_T5_bd.v).

   proves no function (kind: segment lemma support).

   KB ROUND (the wild budget, Crt102Glue.v's G3 / G4): the cuts carry crt_live at kb = prh_wk F_check_round_trip (the
   notation liveB) and its journal at a budget WS with wbudget [] (prh_wk F_check_round_trip) WS. The runs keep WS
   (Crt102Kit.crt_run_xw_inv / crt_run_to_xw_inv); strcmp keeps it (its empty-budget rule over the journal rebased by
   YCbqGwild.ajournal_xw_rebase, stepped back by ajournal_xw_unbase0, as the A' twin Crt102Loops.cl_strcmp_call).
   ct5_L1's statement is unchanged.

   NUMERALS. DERIVED: 0x540 (strcmp's return site, 4 * the slot), 243 (A_OBJ 2, the engine's atom of .rodata's
   object), 69824 = 0x110c0 (MOD_AT's offset in it, the listing's PAddHi). LENGTH: the s1 slots 16 / 24 / 32 / 40 /
   64 / 72, 8 (the keys stride), 64 / 72 (the write window), 96, 2 ^ 44 / 2 ^ 46 / 2 ^ 47 / 2 ^ 60 (bounds). WORD:
   register and atom numbers. No ADDRESS literal. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK0o YK06.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YGcallx YCbqGcall YCbqGcallW.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallSx YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomLive YAkMemnorm YGcallMx YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PjRoundTrip PresetRoomPos PresetReqAt PresetReqAtNoMiss.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes WriterValue WriterApp WriterSpec PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnCheck PRH_FnEx CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnPj PRH_FnWriter PRH_FnAlloc PRH_Supply.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S10Env S1Ledger Crt102Glue Crt102Img Crt102Model.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crt102Kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import S1ImgB Crt102KitB Crt102B_T6_st Crt102B_T7_kit Crt102B_T7_tree Crt102B_T6 Crt102B_T5_bd Crt102B_T5_L2.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import Crt102ImgB.
(* The re-hiding move's world relation and step relation (YA0nH), its step lemmas (YSRrG), the
   zone (YGcfRehidePost.RZ_cf) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH YSRrG YGcfRehidePost.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Local Open Scope bv_scope.
Local Open Scope Z_scope.


(* the L1 state at the head (pc L1, xr = [], xc = []) and at strcmp's return site (pc + 0x540, xr = [slot 0x40 = i],
   xc = the compare's answer and i + 1 against doc->n): x21 = i + 1 (atom 53), x24 = x26 = &doc->keys[i]; extras
   64 = doc->keys, 65 = doc->n, 66 = &doc->keys[i], 67 = doc->keys[i] *)
Definition CRT_K_OFF5_B : Z := 0x540.
Definition ct5_regs1 : list sv := sr_set (sr_set cur_atoms 24%bv (SOff 66 0)) 26%bv (SOff 66 0).
Definition ct5_C40 : YP09.chunk := YP09.mkChunk 64 (CVal 8 (SOff 53 (-1))).
Definition ct5_xr (b : bool) : list YP09.chunk := if b then [ct5_C40] else [].
Definition ct5_s1R1 (b : bool) : YP09.region :=
  YP09.mkRegion (Some 41%nat) 0 96 (if b then 0 else 64) (if b then 0 else 72)
  (ct5_xr b ++ [YP09.mkChunk 16 (CVal 8 (SOff 243 69824)); YP09.mkChunk 24 (CVal 8 (SLit 1));
   YP09.mkChunk 32 (CVal 8 (SOff 64 0)); YP09.mkChunk 40 (CVal 8 (SLit 1)); YP09.mkChunk 72 (CVal 8 (SOff 65 0))]).
Definition ct5_keysR1 : YP09.region := YP09.mkRegion (Some 66%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 67 0))].
Definition ct5_atoms1 : list (nat * afact) :=
  [(59%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (41%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (51%nat, mkAF 4096 CT6_HI 5);
   (54%nat, mkAF 4096 CT6_HI 3); (53%nat, mkAF 1 (2 ^ 44) 0); (64%nat, mkAF 4096 CT6_HI 4);
   (65%nat, mkAF 1 (2 ^ 44) 0); (66%nat, mkAF 4096 CT6_HI 3); (67%nat, mkAF 4096 CT6_HI 4)].
Definition ct5_conds1 : list acond :=
  [mkAC BC_GEU (SOff 66 0) (SOff 64 0); mkAC BC_LTU (SOff 53 (-1)) (SOff 65 0)].
Definition ct5_alias1 : list (sv * sv) := [(SAlu ALU_SRL (SOff 53 (-1)) (SLit 60), SLit 0)].
Definition ct5_SH1 : list shent := [mkSHE 66 0 8].
Definition ct5_ss1 (pc : Z) (b : bool) (xc : list acond) : sstate :=
  mkSS pc ct5_regs1 [ct5_s1R1 b; ct5_keysR1] None (mkFacts ct5_atoms1 (xc ++ ct5_conds1) ct5_alias1).
Definition ct5_HIT : acond := mkAC BC_EQ (SOff 42 0) (SLit 0).
Definition ct5_MISS : acond := mkAC BC_NE (SOff 42 0) (SLit 0).
Definition ct5_ILT : acond := mkAC BC_LTU (SOff 53 0) (SOff 65 0).
Definition ct5_IGE : acond := mkAC BC_GEU (SOff 53 0) (SOff 65 0).
Definition ct5_INE : acond := mkAC BC_NE (SOff 53 (-1)) (SOff 65 0).
Definition ct5_more1 (kd n i xd : Z) : list word := [w64 kd; w64 n; w64 (kd + 8 * i); w64 xd].

Lemma ct5_lxor_lt : forall a b, 0 <= a < 2 ^ 63 -> 0 <= b < 2 ^ 63 -> Z.lxor a b < 2 ^ 64.
Proof.
intros a b Ha Hb. destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]; [lia|].
assert (0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)) as L.
assert (La : Z.log2 a < 63) by (destruct (Z.eq_dec a 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
assert (Lb : Z.log2 b < 63) by (destruct (Z.eq_dec b 0) as [->|]; [cbn; lia | apply Z.log2_lt_pow2; lia]).
apply (Z.lt_trans _ (2 ^ 63)); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Section t5w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
#[local] Existing Instance CfParams_preset.
#[local] Existing Instance prh_img_B.
Context {RL : PrhRoomLive} {SK : YI16.sink_head}.
#[local] Notation PA := (PI_prog_B).
#[local] Notation PL := (PL_prog_B).
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation RLO := (@pa_relro_lo _ B_prog_listing PA).
#[local] Notation RHI := (@pa_relro_hi _ B_prog_listing PA).
#[local] Notation PST := (@prh_pst prh_img_B).
#[local] Notation STKC := (@STK_check_round_trip prh_img_B).
#[local] Notation TEB := (TE (L := B_prog_listing) (PA := PA)).

Lemma ct5_rd_u64_uniq : forall (H : word -> bool) m a v v',
  rd_u64 SEGS (mrestrict H m) a v -> rd_u64 SEGS (mrestrict H m) a v' -> v = v'.
Proof.
intros H m a v v' (Hv & Mv) (Hv' & Mv').
assert (RD : forall w, 0 <= w < 2 ^ 64 -> val_mem SEGS (mrestrict H m) a 8 w -> rdword (aview SEGS H m) a = Some w).
{ intros w Hr Hw.
  assert (Bk : forall k, (k < 8)%nat -> aview SEGS H m (a + Z.of_nat k) = Some (le_byte w 8 k)).
  { intros k Hk. unfold aview. rewrite (Hw k Hk). cbn [option_map]. f_equal.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
  unfold rdword.
  rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
  change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
  change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
  change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
  change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
  f_equal. apply le_bytes8. exact Hr. }
pose proof (RD v Hv Mv) as E1. pose proof (RD v' Hv' Mv') as E2.
rewrite E1 in E2. injection E2 as E2. exact E2.
Qed.

(* the compare's answer is 0 exactly when the key IS the read-only string *)
Lemma ct5_cmp : forall (Wc : world SEGS) memX lblk x k y (nm s : list Z) (v : word),
  pj_cstrR SEGS (mrestrict (w_H Wc) memX) lblk x k nm ->
  (forall j, (j < length s)%nat -> aview SEGS (w_H Wc) memX (y + Z.of_nat j) = Some (nth j s 0)) ->
  (v = w64 0 <-> Z.of_nat (length nm) = Z.of_nat (length s) /\ forall i, 0 <= i < Z.of_nat (length nm) ->
     aview SEGS (w_H Wc) memX (x + i) = aview SEGS (w_H Wc) memX (y + i)) ->
  (v = w64 0 <-> nm = s).
Proof.
intros Wc memX lblk px k y nm s v Hc Hy Hv. pose proof Hc as (_ & _ & _ & _ & Hg).
assert (Hx : forall j, (j < length nm)%nat -> aview SEGS (w_H Wc) memX (px + Z.of_nat j) = Some (nth j nm 0)).
{ intros j Hj. rewrite (cb7t_garr8_at SEGS (w_H Wc) memX px (nm ++ [0]) j Hg ltac:(rewrite length_app; cbn [length]; lia)).
  rewrite app_nth1 by lia. reflexivity. }
rewrite Hv. split.
- intros (El & He). apply Nat2Z.inj in El. apply (nth_ext nm s 0 0 El). intros j Hj.
  specialize (He (Z.of_nat j) ltac:(lia)). rewrite (Hx j Hj), (Hy j ltac:(lia)) in He. injection He as He. exact He.
- intros <-. split; [reflexivity|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (Hx (Z.to_nat i) ltac:(lia)), (Hy (Z.to_nat i) ltac:(lia)). reflexivity.
Qed.

Lemma ct5_img_den : forall E n z v, img_env VAL A_LIM E -> (A_TEXT <= n < A_LIM)%nat -> VAL n + z = v ->
  sv_denot E (SOff n z) = Z_to_bv 64 v.
Proof. intros E n z v HE Hn Hv. cbn [sv_denot]. rewrite (HE n Hn), Hv. reflexivity. Qed.



Section f.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
(* The re-hiding move: the journal at R := YA0nH.wle' SEGS YGcfRehidePost.RZ_cf *)
#[local] Notation AJ := (ajournal_xR (SK := SK) SEGS B PST ARx (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf)).
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.

Section g.
Variables (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
  (rp_i : nat) (rp_H0 : list Z).
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z))
  (doc : Z) (t : PjTree.jv) (D : list (Z * Z)) (x : list Z)
  (Lam : list (Z * Z)) (peak cnt ran most : Z).
(* tcheck_round_trip_specX's premises at the entry this row reads (PRH_FnCheck.v, the text's own; Crt102Top
   discharges them) *)
Hypothesis HPRE : fpre B ARx STKC ly S Hp W regs mem md ch.
Hypothesis HTREE : ck_tree_ok ly S Lam W mem doc t D.
Hypothesis HMN : YAkMemnorm.memnorm SEGS mem.
Hypothesis HREAD : ck_read x = Some t.
Hypothesis HLENX : Z.of_nat (length x) <= 3 * 2 ^ 20.
Hypothesis HWL0 : PjWriteHyp.wlen t false <= 3 * Z.of_nat (length x).
Hypothesis HWL1 : PjWriteHyp.wlen t true <= 56 * Z.of_nat (length x) - 54.
Hypothesis HCNT : cnt < 2 ^ 62 - 2 ^ 30.
Hypothesis HLED0 : prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran most 0.
(* the text's own request bound (PRH_FnCheck.v tcheck_round_trip_specX): every ledger request is within g_most *)
Hypothesis HRQA : RQA_crt t <= most.
(* the read-only string "modifiedAt" the at-search compares with: the text's own `kept_img B a_mod_at 11` at the
   instance's a_mod_at := CRT_MOD_AT_B (Crt102Img.v:1024) *)
Hypothesis HKMA : @kept_img _ B_prog_listing PA B (@CRT_MOD_AT_B _ PA) (Z.of_nat (length ck_MOD_AT) + 1).
(* NAMED HYPOTHESES BOK (asyms_ok B; owner image B's start-up record) and IMGVIS (the image's shadow is
   visible in every ARx state; owner the instance owner, img_shadow_vis_cf), as row T7's Crt102B_T7_tree.v takes them for its
   read-only strcmp operands (cb7t_rom_prem_mod_at) *)
Hypothesis BOK : asyms_ok B.
Hypothesis IMGVIS : forall ly S Hp (W : world SEGS) mem md a,
  ARx ly S Hp W mem md -> @cf_img_lo CfImgB.CfImg_B <= a < @cf_img_top CfImgB.CfImg_B ->
  aview SEGS (w_H W) mem (shadow_addr a) <> None.
(* THE CALLEE TEXTS, each at ANY float state.
   NAMED HYPOTHESIS ASTRCMP (owner: the libc strcmp row): the __wrap_strcmp row in its read-only-premise form WITH the memnorm
   keep (YGcallMxmn.v:898 astrcmp_realizes_xrom). The _xro form (:849) is not enough here: crt_live's last field
   (Crt102Glue.v crt_live_memnorm, `memnorm mem -> memnorm memc`) must hold again after the call, and astrcmp_realizes_xro's post
   (YGcallMxmn.v:866-873) keeps no memnorm.
   *)
Hypothesis ASTRCMP : forall fxk : YK11.FPState,
  astrcmp_realizes_xrom (fx := fxk) SEGS B ARx RLO RHI (SIGMA AS___wrap_strcmp).
#[local] Notation sp0 := (spZ regs).
#[local] Notation sp1 := (@CRT_sp1 regs).
#[local] Notation liveB := (crt_live (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc)
  (t := t) (D := D) (Lam := Lam) (peak := peak) (most := most) (prh_wk F_check_round_trip)).
#[local] Notation L3B := (crt_at_L3_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation CB := (crt_at_C_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).
#[local] Notation QFb := (QF (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing) (PA := PA)
  (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (ran := ran) (most := most)).
#[local] Notation cfgB := (crt_cfg (rc := rc) (L := B_prog_listing) (PA := PA) (CRT_PC := CRT_PC_B)).

#[local] Notation ENT := (ct6_entry B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam
  peak cnt most HPRE HTREE).
#[local] Notation L0B := (crt_at_L0_B (fx := fx) (rc := rc) (PI := prh_img_B) (RL := RL) (SK := SK) (L := B_prog_listing)
  (PA := PA) (B := B) (ARx := ARx) (rp_sm := rp_sm) (rp_x := rp_x) (rp_os := rp_os) (rp_i := rp_i) (rp_H0 := rp_H0)
  (ly := ly) (S := S) (Hp := Hp) (W := W) (regs := regs) (mem := mem) (md := md) (doc := doc) (t := t) (D := D)
  (Lam := Lam) (peak := peak) (cnt := cnt) (most := most)).


Lemma ct5_st1 : forall (fxk : YK11.FPState) pc (Wc : world SEGS) memc rg sp1v F doc' kd nn xd (i : nat) (b : bool) xc,
  getr rg 9 = w64 sp1v -> getr rg 19 = w64 F -> getr rg 22 = w64 doc' -> getr rg 27 = w64 SHADOW_OFF ->
  getr rg 21 = w64 (Z.of_nat i + 1) -> getr rg 24 = w64 (kd + 8 * Z.of_nat i) ->
  getr rg 26 = w64 (kd + 8 * Z.of_nat i) ->
  2 ^ 46 <= sp1v <= 2 ^ 47 -> sp1v mod 32 = 0 ->
  4096 <= F -> F + 512 <= CT6_HI -> F mod 32 = 0 ->
  4096 <= doc' -> doc' + 56 <= CT6_HI -> doc' mod 8 = 0 ->
  4096 <= kd -> kd + 8 * nn <= CT6_HI -> kd + 8 * nn <= sp1v -> kd mod 16 = 0 -> Z.of_nat i < nn <= 2 ^ 44 ->
  4096 <= xd <= CT6_HI -> xd mod 16 = 0 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 16) 8 (@CRT_MOD_AT_B _ PA) ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 24) 8 1 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 32) 8 kd ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 40) 8 1 ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 72) 8 nn ->
  val_mem SEGS (mrestrict (w_H Wc) memc) (kd + 8 * Z.of_nat i) 8 xd ->
  range_addressable (aview SEGS (w_H Wc) memc) SHADOW_OFF (kd + 8 * Z.of_nat i) 8 -> in_app (kd + 8 * Z.of_nat i) 8 ->
  (forall a, sp1v + 64 <= a < sp1v + 72 -> apresent (w_H Wc) memc a) ->
  (b = true -> val_mem SEGS (mrestrict (w_H Wc) memc) (sp1v + 64) 8 (Z.of_nat i)) ->
  conds_ok (TEB regs rg (ct5_more1 kd nn (Z.of_nat i) xd)) xc ->
  st_ok_pi SEGS VAL (TEB regs rg (ct5_more1 kd nn (Z.of_nat i) xd)) (ct5_ss1 pc b xc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff 59 0) ct5_SH1 (TEB regs rg (ct5_more1 kd nn (Z.of_nat i) xd)) (mrestrict (w_H Wc) memc).
Proof.
intros fxk pc Wc memc rg sp1v F doc' kd nn xd i b xc R9 R19 R22 R27 R21 R24 R26 Hs1 Hs1a HF1 HF2 HF3 Hd1 Hd2 Hd3
  Hk1 Hk2 Hk2' Hk3 Hin Hx1 Hx3 C16 C24 C32 C40 C72 CK RAk APk HPR XR XC.
set (mo := ct5_more1 kd nn (Z.of_nat i) xd). set (E := TEB regs rg mo).
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
assert (Hi0 : 0 <= Z.of_nat i) by lia.
assert (A41 : ew E 41 = w64 sp1v) by exact (eq_trans (te_cur regs rg mo 9%bv 9 eq_refl) R9).
assert (A51 : ew E 51 = w64 F) by exact (eq_trans (te_cur regs rg mo 19%bv 19 eq_refl) R19).
assert (A54 : ew E 54 = w64 doc') by exact (eq_trans (te_cur regs rg mo 22%bv 22 eq_refl) R22).
assert (A59 : ew E 59 = w64 SHADOW_OFF) by exact (eq_trans (te_cur regs rg mo 27%bv 27 eq_refl) R27).
assert (A53 : ew E 53 = w64 (Z.of_nat i + 1)) by exact (eq_trans (te_cur regs rg mo 21%bv 21 eq_refl) R21).
assert (A64 : ew E 64 = w64 kd) by exact (te_more_lt regs rg mo 0 ltac:(cbn; lia)).
assert (A65 : ew E 65 = w64 nn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
assert (A66 : ew E 66 = w64 (kd + 8 * Z.of_nat i)) by exact (te_more_lt regs rg mo 2 ltac:(cbn; lia)).
assert (A67 : ew E 67 = w64 xd) by exact (te_more_lt regs rg mo 3 ltac:(cbn; lia)).
assert (U41 : bv_unsigned (ew E 41) = sp1v) by (rewrite A41; apply unsigned_lit_small; lia).
assert (U51 : bv_unsigned (ew E 51) = F) by (rewrite A51; apply unsigned_lit_small; lia).
assert (U54 : bv_unsigned (ew E 54) = doc') by (rewrite A54; apply unsigned_lit_small; lia).
assert (U59 : bv_unsigned (ew E 59) = SHADOW_OFF) by (rewrite A59; apply unsigned_lit_small; cbv [SHADOW_OFF]; lia).
assert (U53 : bv_unsigned (ew E 53) = Z.of_nat i + 1) by (rewrite A53; apply unsigned_lit_small; lia).
assert (U64 : bv_unsigned (ew E 64) = kd) by (rewrite A64; apply unsigned_lit_small; lia).
assert (U65 : bv_unsigned (ew E 65) = nn) by (rewrite A65; apply unsigned_lit_small; lia).
assert (U66 : bv_unsigned (ew E 66) = kd + 8 * Z.of_nat i) by (rewrite A66; apply unsigned_lit_small; lia).
assert (U67 : bv_unsigned (ew E 67) = xd) by (rewrite A67; apply unsigned_lit_small; lia).
assert (UA : forall n v, bv_unsigned (ew E n) = v -> U E (SOff n 0) = v).
{ intros n v H. rewrite ts_U0. exact H. }
assert (HEI : img_env VAL A_LIM E) by apply te_env.
split.
2:{ unfold sh_ok, ct5_SH1. apply Forall_cons; [|apply Forall_nil].
    unfold shent_ok, app_apart; cbn [she_m she_lo she_hi]; rewrite <- (aview_rd_of SEGS);
    rewrite (UA 59%nat SHADOW_OFF U59); rewrite ?Z.add_0_r, ?Z.sub_0_r.
    rewrite (UA 66%nat _ U66). split; [exact RAk|].
    intros a Ha. destruct APk as (A1 & [A2 | (A3 & A4)]); cbv [kLowShadowBeg kHighMemBeg SHADOW_OFF] in *; lia. }
unfold ct5_ss1. apply ts_st_ok.
all: fold E.
- intros r. unfold ct5_regs1. destruct (bv_eqb r 26%bv) eqn:E26.
  + apply bv_eqb_eq in E26. subst r. rewrite sr_get_set_same by reflexivity. rewrite R26. symmetry.
    apply (ct6_denot_at E 66%nat _ A66); lia.
  + rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in E26; discriminate).
    destruct (bv_eqb r 24%bv) eqn:E24.
    * apply bv_eqb_eq in E24. subst r. rewrite sr_get_set_same by reflexivity. rewrite R24. symmetry.
      apply (ct6_denot_at E 66%nat _ A66); lia.
    * rewrite sr_get_set_other by (intros ->; rewrite bv_eqb_refl in E24; discriminate). apply te_regs_ok.
- destruct b; vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
  + apply (ts_rok E _ 41 sp1v); [exact U41 | lia | lia | |].
    { intros o Ho. destruct b; [lia|]. apply (apresent_writable SEGS). apply HPR. lia. }
    apply Forall_app. split.
    { destruct b; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
      apply (ts_chunk E _ sp1v 64 8 _ (Z.of_nat i)); [| lia | lia | exact (XR eq_refl)].
      rewrite (ct6_denot_off E 53%nat (-1) (Z.of_nat i + 1) A53) by lia. f_equal. lia. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
    * apply (ts_chunk E _ sp1v 16 8 _ (@CRT_MOD_AT_B _ PA)); [| split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity | lia | exact C16].
      apply ct5_img_den; [exact HEI | unfold A_TEXT, A_LIM; lia | vm_compute; reflexivity].
    * apply (ts_chunk E _ sp1v 24 8 _ 1); [reflexivity | lia | lia | exact C24].
    * apply (ts_chunk E _ sp1v 32 8 _ kd); [| lia | lia | exact C32].
      apply (ct6_denot_at E 64%nat kd A64); lia.
    * apply (ts_chunk E _ sp1v 40 8 _ 1); [reflexivity | lia | lia | exact C40].
    * apply (ts_chunk E _ sp1v 72 8 _ nn); [| lia | lia | exact C72].
      apply (ct6_denot_at E 65%nat nn A65); lia.
  + apply (ts_rok E _ 66 (kd + 8 * Z.of_nat i)); [exact U66 | lia | lia | intros o Ho; lia |].
    constructor; [|constructor].
    apply (ts_chunk E _ (kd + 8 * Z.of_nat i) 0 8 _ xd); [| lia | lia | rewrite Z.add_0_r; exact CK].
    apply (ct6_denot_at E 67%nat xd A67); lia.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi ct5_s1R1 ct5_keysR1]. rewrite !ts_bv_some.
  rewrite U41, U66. repeat split; lia.
- split; [|split].
  + clearbody E mo. cbn [f_atoms]. unfold ct5_atoms1. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U59, U41, U51, U54, U53, U64, U65, U66, U67.
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. change (2 ^ 4) with 16. change (2 ^ 5) with 32.
    rewrite !Z.mod_1_r. cbv [SHADOW_OFF]. repeat split; lia.
  + cbn [f_conds]. apply ct6_conds_app; [exact XC|]. clearbody E mo. unfold ct5_conds1. cbn [conds_ok]. unfold acond_ok.
    cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, branch_ltu_U.
    rewrite (UA 66%nat _ U66), (UA 64%nat _ U64), (UA 65%nat _ U65), U_SOff, U53.
    rewrite zcanon_id by (unfold M64; lia).
    repeat split; first [apply Z.ltb_lt; lia | apply negb_true_iff, Z.ltb_ge; lia].
  + clearbody E mo. cbn [f_alias]. unfold ct5_alias1. cbn [alias_ok].
    split; [|exact I]. apply U_inj. rewrite U_SAlu, U_SOff, U53, !U_SLit.
    unfold zcanon, M64, zalu_raw. rewrite (Z.mod_small (Z.of_nat i + 1 + -1)) by lia.
    rewrite (Z.mod_small 60) by lia. change (Z.land 60 63) with 60. rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.div_small by lia. reflexivity.
Qed.

#[local] Notation CORE := (@crt5_core fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt most).
#[local] Notation L1B := (@crt5_L1 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt most).
#[local] Notation L2B := (@crt5_L2 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt most).
(* the live state with a new journal at the same memory (Crt102B_T6.v ct6_live_md) *)
#[local] Notation LMD := (ct6_live_md B ARx ly S Hp W regs mem md doc t D Lam peak most).
#[local] Notation spillB := (crt_spill (rc := rc) (L := B_prog_listing) (PA := PA) (regs := regs)).

(* ---- the L1 facts give the L1 state at any pc (with slot 0x40 = i when b), and member i's key ---- *)
Lemma ct5_L1_ent : forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i pc
    (b : bool),
  L1B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i ->
  (b = true -> spillB Wc memc 64 (Z.of_nat i)) ->
  exists xd kxd nm u,
    nth_error mms i = Some (nm, u) /\ pj_cstrR SEGS (mrestrict (w_H Wc) memc) (prh_lin Lamc) xd kxd nm /\
    Z.of_nat (length mms) <= 2 ^ 44 /\ 4096 <= kd /\ kd + 8 * Z.of_nat (length mms) <= YM05.alloc_ceiling /\
    sh_ok SEGS (SOff 59 0) ct5_SH1 (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd))
      (mrestrict (w_H Wc) memc) /\
    (forall xc, conds_ok (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd)) xc ->
      st_ok_pi SEGS VAL (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd)) (ct5_ss1 pc b xc)
        (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS)))).
Proof.
intros fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i pc b HL1 H64.
destruct HL1 as (HCORE & R21 & R24 & R26 & S16 & S24 & S32 & S40 & S72 & Hkd & Hi & Hbefore).
pose proof HCORE as (Ht & HFZ & HFK & HL & HDR & S0 & S8 & S48 & S56 & S80 & S88 & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 &
  Hcnt & Hsv & HTC & HFD & HBK & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_side_ledger (crt_live_side HL)) as HLED.
pose proof (crt_side_doc (crt_live_side HL)) as HDOC. pose proof (crt_side_doc_blocks (crt_live_side HL)) as HDL.
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & Hdc3 & Hdc4).
pose proof YM05.alloc_ceiling_val as Hac.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRc & _).
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
set (F := frame_addr lyc CRT_CID pos) in *.
set (m := mrestrict (w_H Wc) memc) in *.
(* doc's header and member i *)
rewrite Ht in HDOC.
destruct (ct6_obj_hdr SEGS m (prh_lin Lamc) doc mms D HDOC ltac:(lia))
  as (kid & kd' & capd & Ddi & _ & Cd32 & _ & _ & Hncd & _ & Lkd & _ & _ & Hmd).
assert (Ekd : kd' = kd) by (unfold PJ_OFF_KEYS in Hkd; exact (ct5_rd_u64_uniq _ _ _ _ _ Cd32 Hkd)).
subst kd'.
destruct (nth_error mms i) as [[nm u]|] eqn:Enth; [|apply nth_error_None in Enth; lia].
destruct (ct6_mems_nth SEGS m (prh_lin Lamc) _ mms kid kd Ddi i nm u Hmd Enth)
  as (xd & kxd & Dd1 & Cxd & Hcd & _ & Hind & _).
unfold prh_lin in Lkd.
destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 kd (8 * capd) (proj1 HJ) HLED Lkd)
  as (kd0 & kd16 & kd4 & kdc & kdapp & _ & kdra & _ & _).
pose proof Hcd as (Lxd & _ & _ & _). unfold prh_lin in Lxd.
destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 xd kxd (proj1 HJ) HLED Lxd)
  as (xd0 & xd16 & xd4 & xdc & _).
assert (Hn44 : Z.of_nat (length mms) <= 2 ^ 44) by lia.
exists xd, kxd, nm, u. split; [reflexivity|]. split; [exact Hcd|]. split; [exact Hn44|]. split; [lia|]. split; [lia|].
destruct Cxd as (_ & Cxd).
unfold crt_spill in S16, S24, S32, S40, S72.
assert (HIc : CT6_HI = 2 ^ 47 - 2 ^ 23) by reflexivity.
cut (forall xc,
  conds_ok (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd)) xc ->
  st_ok_pi SEGS VAL (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd)) (ct5_ss1 pc b xc)
    (restrict (w_H Wc) (@YK11.mkst fxk rg (Z_to_bv 64 (BASE + pc)) memc (YK11.seg_rom SEGS))) /\
  sh_ok SEGS (SOff 59 0) ct5_SH1 (TEB regs rg (ct5_more1 kd (Z.of_nat (length mms)) (Z.of_nat i) xd)) m).
{ intros HX. split; [exact (proj2 (HX [] I))|]. intros xc XC. exact (proj1 (HX xc XC)). }
intros xc XC.
apply (ct5_st1 fxk pc Wc memc rg sp1 F doc kd (Z.of_nat (length mms)) xd i b xc R9 R19 R22 R27 R21 R24 R26).
all: try (unfold CT6_HI; lia).
all: first [ assumption | exact H64 | (apply kdra; lia) | (apply (in_app_sub _ _ _ _ kdapp); lia)
           | (intros a Ha; apply HPRc; rewrite HSTKC; lia) ].
Qed.

(* a key string kept by a memory change that keeps its block's bytes *)
Lemma ct5_cstr_keep : forall m m' lblk a k s, pj_cstrR SEGS m lblk a k s ->
  (forall y, a <= y < a + k -> mbyte SEGS m' y = mbyte SEGS m y) -> pj_cstrR SEGS m' lblk a k s.
Proof.
intros m m' lblk a k s (Hl & Hk & H32 & Fs & Gs) E.
split; [exact Hl|]. split; [exact Hk|]. split; [exact H32|]. split; [exact Fs|].
eapply garr8_frame; [exact Gs|]. intros y Hy. rewrite length_app in Hy. cbn [length] in Hy. apply E. lia.
Qed.

(* the read-only string's bytes (the text's kept_img, arodata_okP, the image bytes) *)
Lemma ct5_rom_bytes : forall (Wc : world SEGS) memX y (s : list Z),
  arodata_okP SEGS RLO RHI B (aview SEGS (w_H Wc) memX) ->
  @kept_img _ B_prog_listing PA B y (Z.of_nat (length s) + 1) ->
  (forall j, (j < length (s ++ [0%Z]))%nat ->
     option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom SEGS (Z_to_bv 64 (y + Z.of_nat j))) =
     Some (nth j (s ++ [0]) 0)) ->
  forall j, (j < length s)%nat -> aview SEGS (w_H Wc) memX (y + Z.of_nat j) = Some (nth j s 0).
Proof.
intros Wc memX y s HRO (Hlo & Hhi & HK) HROM j Hj.
destruct (HK (y + Z.of_nat j) ltac:(lia)) as (Hr & Ho & He & _).
rewrite (HRO _ Hr Ho He). rewrite (HROM j ltac:(rewrite length_app; cbn [length]; lia)).
rewrite app_nth1 by lia. reflexivity.
Qed.

#[local] Notation ATL2 Pd := (@CT5_AT_L2 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D Lam
  peak cnt ran most Pd).
#[local] Notation ATL1 Pd j ms := (@CT5_AT_L1 fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D
  Lam peak cnt ran most Pd j ms).

(* ---- K (+0x540, strcmp's return site) -> L1 at i + 1 (no hit, i + 1 < doc->n) or L2 (a hit, or i + 1 = doc->n) ---- *)
Lemma ct5_K : forall Pd, ATL2 Pd -> forall i mms, (forall j, (i < j)%nat -> ATL1 Pd j mms) ->
  forall fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw kd,
  L1B fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i ->
  spillB Wc memc 64 (Z.of_nat i) ->
  (forall nm u, nth_error mms i = Some (nm, u) -> (getr rg 10 = w64 0 <-> nm = ck_MOD_AT)) ->
  Pd Dc Dback kw mms ->
  YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_K_OFF5_B rg memc mdc) QFb.
Proof.
intros Pd HL2s i mms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw kd HL1 H64 Hcmp HPd.
destruct (ct5_L1_ent fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i
  (CRT_PC_B + CRT_K_OFF5_B) true HL1 (fun _ => H64))
  as (xd & kxd & nm & u & Enth & Hcd & Hn44 & Hkd0 & Hkdc & SHOK & HSx).
pose proof YM05.alloc_ceiling_val as Hac.
specialize (Hcmp nm u Enth).
pose proof HL1 as (HCORE & R21 & R24 & R26 & S16 & S24 & S32 & S40 & S72 & Hkd & Hi & Hbefore).
pose proof HCORE as (Ht & HFZ & HFK & HL & HDR & S0 & S8 & S48 & S56 & S80 & S88 & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 &
  Hcnt & Hsv & HTC & HFD & HBK & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & Hdc3 & Hdc4).
set (nn := Z.of_nat (length mms)) in *.
set (mo := ct5_more1 kd nn (Z.of_nat i) xd) in *.
assert (A42 : ew (TEB regs rg mo) 42 = getr rg 10) by exact (te_cur regs rg mo 10%bv 10 eq_refl).
assert (A53 : ew (TEB regs rg mo) 53 = w64 (Z.of_nat i + 1))
  by exact (eq_trans (te_cur regs rg mo 21%bv 21 eq_refl) R21).
assert (A65 : ew (TEB regs rg mo) 65 = w64 nn) by exact (te_more_lt regs rg mo 1 ltac:(cbn; lia)).
assert (A66 : ew (TEB regs rg mo) 66 = w64 (kd + 8 * Z.of_nat i)) by exact (te_more_lt regs rg mo 2 ltac:(cbn; lia)).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
assert (Hl : (i < length mms)%nat) by exact Hi.
assert (Hnn : 1 <= nn <= 2 ^ 44) by (unfold nn; lia).
assert (U53 : U (TEB regs rg mo) (SOff 53 0) = Z.of_nat i + 1).
{ rewrite ts_U0, A53. unfold w64. apply unsigned_lit_small. lia. }
assert (U53m : U (TEB regs rg mo) (SOff 53 (-1)) = Z.of_nat i).
{ rewrite U_SOff, A53. unfold w64. rewrite unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). lia. }
assert (U65 : U (TEB regs rg mo) (SOff 65 0) = nn).
{ rewrite ts_U0, A65. unfold w64. apply unsigned_lit_small. lia. }
assert (UL : forall z, 0 <= z < 2 ^ 64 -> U (TEB regs rg mo) (SLit z) = z).
{ intros z Hz. rewrite U_SLit. apply zcanon_id. unfold M64. lia. }
pose (RUNTO := @crt_run_to_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (Hat_inv : cm_at_inv mms i (length mms)).
{ split; [lia|]. left. split; [reflexivity|]. exact Hbefore. }
unfold crt_cfg.
destruct (list_eq_dec Z.eq_dec nm ck_MOD_AT) as [Hhit | Hmiss].
- (* a hit: at = i *)
  assert (H10 : getr rg 10 = w64 0) by (apply Hcmp; exact Hhit).
  assert (XH : acond_ok (TEB regs rg mo) ct5_HIT).
  { unfold acond_ok, ct5_HIT. cbn [ac_c ac_a ac_b]. rewrite branch_eq_U, ts_U0, A42, H10, UL by lia.
    unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
  destruct (cm_at_inv_hit mms i (length mms) u Hat_inv eq_refl ltac:(rewrite Enth, Hhit; reflexivity)) as (Eat & _).
  destruct (Nat.lt_ge_cases (Datatypes.S i) (length mms)) as [Hlt | Hge].
  + assert (XC : conds_ok (TEB regs rg mo) [ct5_HIT; ct5_ILT; ct5_INE]).
    { split; [exact XH|]. split.
      - unfold acond_ok, ct5_ILT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, U53, U65. apply Z.ltb_lt. unfold nn. lia.
      - split; [|exact I]. unfold acond_ok, ct5_INE. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, U53m, U65.
        apply negb_true_iff, Z.eqb_neq. unfold nn. lia. }
    pose proof (HSx _ XC) as HS.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L2_OFF_B).
    { ct6_ro. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pmkst HS. rewrite HF in HJ, HPM |- *.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT_L2_OFF_B) end.
    pose proof HJ as HJm.
    set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
    assert (HDR2 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
    { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
      apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
    refine (HL2s fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw i _ HPd).
    refine (conj (conj Ht (conj HFZ (conj HFK (conj (LMD HL HJm HB_HJ) (conj HDR2 (conj S0 (conj S8 (conj S48 (conj S56 (conj S80 (conj S88 (conj Hd8 (conj RAd (conj RAb (conj RAv (conj Hcs1 (conj Hcs2 (conj Hcnt (conj Hsv (conj HTC (conj HFD (conj HBK HPOS)))))))))))))))))))))) (conj _ (conj _ _))).
    { ct6_reg HS (11%bv : bv 5) Hr. rewrite Hr. apply bv_eq. change (bv_unsigned (sv_denot (TEB regs rg mo) (SOff 53 (-1))))
        with (U (TEB regs rg mo) (SOff 53 (-1))). rewrite U53m. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    { ct6_reg HS (12%bv : bv 5) Hr. rewrite Hr. apply bv_eq.
      change (bv_unsigned (sv_denot (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 53 (-1)) (SOff 65 0)) (SLit 1))))
        with (U (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 53 (-1)) (SOff 65 0)) (SLit 1))).
      rewrite !U_SAlu, U53m, U65, UL by lia. rewrite (proj2 (Nat.eqb_neq i (length mms)) ltac:(lia)).
      unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64, zalu_raw.
      rewrite (Z.mod_small (Z.lxor _ _)) by (split; [apply Z.lxor_nonneg; unfold nn; lia | ]; apply ct5_lxor_lt; unfold nn; lia).
      assert (Hx : Z.lxor (Z.of_nat i) nn <> 0) by (rewrite Z.lxor_eq_0_iff; unfold nn; lia).
      assert (0 <= Z.lxor (Z.of_nat i) nn) by (apply Z.lxor_nonneg; unfold nn; lia).
      destruct (Z.ltb_spec (Z.lxor (Z.of_nat i) nn) 1); [lia|]. reflexivity. }
    { exact Eat. }
  + assert (XC : conds_ok (TEB regs rg mo) [ct5_HIT; ct5_IGE]).
    { split; [exact XH|]. split; [|exact I].
      unfold acond_ok, ct5_IGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, U53, U65.
      apply negb_true_iff, Z.ltb_ge. unfold nn. lia. }
    pose proof (HSx _ XC) as HS.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L2_OFF_B).
    { ct6_ro. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pmkst HS. rewrite HF in HJ, HPM |- *.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT_L2_OFF_B) end.
    pose proof HJ as HJm.
    set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
    assert (HDR2 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
    { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
      apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
    refine (HL2s fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw i _ HPd).
    refine (conj (conj Ht (conj HFZ (conj HFK (conj (LMD HL HJm HB_HJ) (conj HDR2 (conj S0 (conj S8 (conj S48 (conj S56 (conj S80 (conj S88 (conj Hd8 (conj RAd (conj RAb (conj RAv (conj Hcs1 (conj Hcs2 (conj Hcnt (conj Hsv (conj HTC (conj HFD (conj HBK HPOS)))))))))))))))))))))) (conj _ (conj _ _))).
    { ct6_reg HS (11%bv : bv 5) Hr. rewrite Hr. apply bv_eq. change (bv_unsigned (sv_denot (TEB regs rg mo) (SOff 53 (-1))))
        with (U (TEB regs rg mo) (SOff 53 (-1))). rewrite U53m. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    { ct6_reg HS (12%bv : bv 5) Hr. rewrite Hr. apply bv_eq.
      change (bv_unsigned (sv_denot (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 53 (-1)) (SOff 65 0)) (SLit 1))))
        with (U (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 53 (-1)) (SOff 65 0)) (SLit 1))).
      rewrite !U_SAlu, U53m, U65, UL by lia. rewrite (proj2 (Nat.eqb_neq i (length mms)) ltac:(lia)).
      unfold w64. rewrite unsigned_lit_small by lia. unfold zcanon, M64, zalu_raw.
      rewrite (Z.mod_small (Z.lxor _ _)) by (split; [apply Z.lxor_nonneg; unfold nn; lia | ]; apply ct5_lxor_lt; unfold nn; lia).
      assert (Hx : Z.lxor (Z.of_nat i) nn <> 0) by (rewrite Z.lxor_eq_0_iff; unfold nn; lia).
      assert (0 <= Z.lxor (Z.of_nat i) nn) by (apply Z.lxor_nonneg; unfold nn; lia).
      destruct (Z.ltb_spec (Z.lxor (Z.of_nat i) nn) 1); [lia|]. reflexivity. }
    { exact Eat. }
- (* no hit *)
  assert (H10 : getr rg 10 <> w64 0) by (intros E0; exact (Hmiss (proj1 Hcmp E0))).
  assert (XM : acond_ok (TEB regs rg mo) ct5_MISS).
  { unfold acond_ok, ct5_MISS. cbn [ac_c ac_a ac_b]. rewrite branch_ne_U, ts_U0, A42, UL by lia.
    apply negb_true_iff, Z.eqb_neq. intros E0. apply H10. apply bv_eq. rewrite E0. unfold w64.
    rewrite unsigned_lit_small by lia. reflexivity. }
  pose proof (cm_at_inv_miss mms i (length mms) nm u Hat_inv eq_refl Enth Hmiss) as Hinv1.
  destruct (Nat.lt_ge_cases (Datatypes.S i) (length mms)) as [Hlt | Hge].
  + assert (XC : conds_ok (TEB regs rg mo) [ct5_MISS; ct5_ILT]).
    { split; [exact XM|]. split; [|exact I].
      unfold acond_ok, ct5_ILT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, U53, U65. apply Z.ltb_lt. unfold nn. lia. }
    pose proof (HSx _ XC) as HS.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L1_OFF_B).
    { ct6_ro. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pmkst HS. rewrite HF in HJ, HPM |- *.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT_L1_OFF_B) end.
    pose proof HJ as HJm.
    set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
    assert (HDR2 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
    { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
      apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
    refine (IH (Datatypes.S i) ltac:(lia) fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) cset
      saved kw kd _ HPd).
    refine (conj (conj Ht (conj HFZ (conj HFK (conj (LMD HL HJm HB_HJ) (conj HDR2 (conj S0 (conj S8 (conj S48 (conj S56 (conj S80 (conj S88 (conj Hd8 (conj RAd (conj RAb (conj RAv (conj Hcs1 (conj Hcs2 (conj Hcnt (conj Hsv (conj HTC (conj HFD (conj HBK HPOS)))))))))))))))))))))) (conj _ (conj _ (conj _ (conj S16 (conj S24 (conj S32 (conj S40 (conj S72 (conj Hkd
      (conj Hlt _))))))))))).
    { ct6_reg HS (21%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 53%nat 1 (Z.of_nat i + 1) A53) by lia.
      f_equal. lia. }
    { ct6_reg HS (24%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 66%nat 8 (kd + 8 * Z.of_nat i) A66) by lia.
      f_equal. lia. }
    { ct6_reg HS (26%bv : bv 5) Hr. rewrite Hr. rewrite (ct6_denot_off _ 66%nat 8 (kd + 8 * Z.of_nat i) A66) by lia.
      f_equal. lia. }
    { destruct Hinv1 as (_ & [(_ & Hb1) | (Ea & Hlt2)]); [exact Hb1|]. lia. }
  + assert (XC : conds_ok (TEB regs rg mo) [ct5_MISS; ct5_IGE]).
    { split; [exact XM|]. split; [|exact I].
      unfold acond_ok, ct5_IGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, U53, U65.
      apply negb_true_iff, Z.ltb_ge. unfold nn. lia. }
    assert (Eat : length mms = cm_at mms).
    { apply (cm_at_inv_exit mms (Datatypes.S i) (length mms) Hinv1). left. lia. }
    pose proof (HSx _ XC) as HS.
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) (CRT_PC_B + CRT_L2_OFF_B).
    { ct6_ro. }
    apply frame_of_read_only in HF; [|vm_compute; reflexivity].
    pmkst HS. rewrite HF in HJ, HPM |- *.
    lazymatch goal with |- YA0nH.SRr' _ _ _ {| cfg_ms := mkst _ (Z_to_bv 64 (_ + ?n)) _ _; cfg_model := _ |} _ =>
      change n with (CRT_PC_B + CRT_L2_OFF_B) end.
    pose proof HJ as HJm.
    set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
    assert (HDR2 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
    { refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
      apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
      repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
    refine (HL2s fxk lyc Sc Hpc Wc memc mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw (length mms) _ HPd).
    refine (conj (conj Ht (conj HFZ (conj HFK (conj (LMD HL HJm HB_HJ) (conj HDR2 (conj S0 (conj S8 (conj S48 (conj S56 (conj S80 (conj S88 (conj Hd8 (conj RAd (conj RAb (conj RAv (conj Hcs1 (conj Hcs2 (conj Hcnt (conj Hsv (conj HTC (conj HFD (conj HBK HPOS)))))))))))))))))))))) (conj _ (conj _ _))).
    { ct6_reg HS (11%bv : bv 5) Hr. rewrite Hr. apply bv_eq. change (bv_unsigned (sv_denot (TEB regs rg mo) (SOff 65 0)))
        with (U (TEB regs rg mo) (SOff 65 0)). rewrite U65. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    { ct6_reg HS (12%bv : bv 5) Hr. rewrite Hr. apply bv_eq.
      change (bv_unsigned (sv_denot (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 65 0) (SOff 65 0)) (SLit 1))))
        with (U (TEB regs rg mo) (SAlu ALU_SLTU (SAlu ALU_XOR (SOff 65 0) (SOff 65 0)) (SLit 1))).
      rewrite !U_SAlu, U65, UL by lia. rewrite Nat.eqb_refl. rewrite Z.lxor_nilpotent.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
    { exact Eat. }
Qed.

#[local] Notation L1STMT Pd := (@CT5_L1_STMT fx rc RL SK B ARx rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md doc t D
  Lam peak cnt ran most Pd).

(* ---- L1 (+0x4f8, the at-search head at index i) -> `__wrap_strcmp (doc->keys[i], MOD_AT)` at +0x53c -> K ---- *)
Lemma ct5_L1 : forall Pd, L1STMT Pd.
Proof.
intros Pd. unfold CT5_L1_STMT.
intros HL2s i mms IH fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg cset saved kw kd HL1 HPd.
destruct (ct5_L1_ent fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw kd i
  (CRT_PC_B + CRT_L1_OFF_B) false HL1 (fun E0 => False_ind _ (diff_false_true E0)))
  as (xd & kxd & nm & u & Enth & Hcd & Hn44 & Hkd0 & Hkdc & SHOK & HSx).
pose proof HL1 as (HCORE & R21 & R24 & R26 & S16 & S24 & S32 & S40 & S72 & Hkd & Hi & Hbefore).
pose proof HCORE as (Ht & HFZ & HFK & HL & HDR & S0 & S8 & S48 & S56 & S80 & S88 & Hd8 & RAd & RAb & RAv & Hcs1 & Hcs2 &
  Hcnt & Hsv & HTC & HFD & HBK & HPOS).
destruct (crt_live_journal HL) as (WS_HJ & HJ & HB_HJ). pose proof (crt_live_memnorm HL) as HPM.
pose proof (crt_side_ledger (crt_live_side HL)) as HLED. pose proof (crt_side_arodata (crt_live_side HL)) as HROc.
pose proof (crt_dregs_B_bregs HDR) as HBR. pose proof (crt_dregs_B_s6 HDR) as R22.
pose proof (crt_bregs_B_sp HBR) as R2. pose proof (crt_bregs_B_gp HBR) as R3. pose proof (crt_bregs_B_tp HBR) as R4.
pose proof (crt_bregs_B_s0 HBR) as R8. pose proof (crt_bregs_B_s1 HBR) as R9. pose proof (crt_bregs_B_s2 HBR) as R18.
pose proof (crt_bregs_B_s4 HBR) as R20. pose proof (crt_bregs_B_s3 HBR) as R19. pose proof (crt_bregs_B_s7 HBR) as R23.
pose proof (crt_bregs_B_s9 HBR) as R25. pose proof (crt_bregs_B_s11 HBR) as R27.
destruct (cb4_ff B ARx ly S Hp W regs mem md LAWS lyc Sc Hpc Wc memc mdc kj pos HJ)
  as (Hin & Fb1 & Fb2 & Fb3 & F32 & Ffr & Fsh).
pose proof (cb4_sp B ARx ly S Hp W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & Hs1 & Hs1a & Hs1b).
pose proof (cb4_doc_home B ARx ly S Hp W regs mem md ch doc t D Lam LAWS HPRE HTREE) as (Hdc1 & Hdc2 & Hdc3 & Hdc4).
pose proof YM05.alloc_ceiling_val as Hac.
assert (HSTKC : STKC = 27632) by (vm_compute; reflexivity).
assert (Hes : ESTACK = 4096) by reflexivity.
set (nn := Z.of_nat (length mms)) in *.
set (mo := ct5_more1 kd nn (Z.of_nat i) xd) in *.
assert (U41 : bv_unsigned (ew (TEB regs rg mo) 41) = sp1).
{ rewrite (te_cur regs rg mo 9%bv 9 eq_refl), R9. apply unsigned_lit_small. lia. }
assert (A66 : ew (TEB regs rg mo) 66 = w64 (kd + 8 * Z.of_nat i)) by exact (te_more_lt regs rg mo 2 ltac:(cbn; lia)).
assert (A67 : ew (TEB regs rg mo) 67 = w64 xd) by exact (te_more_lt regs rg mo 3 ltac:(cbn; lia)).
assert (A53 : ew (TEB regs rg mo) 53 = w64 (Z.of_nat i + 1)) by exact (eq_trans (te_cur regs rg mo 21%bv 21 eq_refl) R21).
assert (HEI : img_env VAL A_LIM (TEB regs rg mo)) by apply te_env.
pose proof (HSx [] I) as HS.
pose proof Hcd as (Lxd & _ & _ & _). unfold prh_lin in Lxd.
destruct (ct6_blk B ARx LAWS lyc Sc Hpc Wc memc mdc Lamc peakc cntc 0 xd kxd (proj1 HJ) HLED Lxd)
  as (xd0 & xd16 & xd4 & xdc & _).
pose (RUN := @crt_run_xw_inv fxk rc SK B_prog_listing PL PA B PST ARx _ LAWS
  (fun m => YAkMemnorm.memnorm SEGS mem -> YAkMemnorm.memnorm SEGS m)
  (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) mem (srr_inv_laws_memnorm_k SEGS)) WS_HJ).
assert (Hwr : forall a, in_wrange (TEB regs rg mo) (ss_mem (ct5_ss1 (CRT_PC_B + CRT_L1_OFF_B) false [])) a -> sp1 + 64 <= a < sp1 + 72).
{ intros a (rr & Hr & Ha). cbv [ct5_ss1 ss_mem In] in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi ct5_s1R1 ct5_keysR1] in Ha;
  rewrite ts_bv_some in Ha; [rewrite U41 in Ha|]; lia. }
unfold crt_cfg.
paj_run_tok_x_inv RUN HS HJ SHOK HPM (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
{ lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0' ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0' bc ly' own') end.
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 41%nat (sp1 - sp0)); [reflexivity | | | |].
  - rewrite U41. lia.
  - cbn [YP09.r_wlo]. rewrite HSTKC. lia.
  - cbn [YP09.r_whi]. lia.
  - apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
(* the run's memory: slot 0x40 = i; everything else kept *)
pmkst HS.
set (mdc' := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 + 64 <= a < sp1 + 72) ->
  aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a).
{ intros a Ha Hn. exact (ts_keep Wc (TEB regs rg mo) _ memc (ms_mem ms) _ HFr Hwr a Ha Hn). }
assert (KSP : forall off v, (0 <= off /\ off + 8 <= 64 \/ 72 <= off < 2 ^ 32) -> spillB Wc memc off v ->
  spillB Wc (ms_mem ms) off v).
{ intros off v Hoff Hv. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hv].
  intros k Hk. apply K; lia. }
assert (KL : forall a, 0 <= a < YM05.alloc_ceiling -> aview SEGS (w_H Wc) (ms_mem ms) a = aview SEGS (w_H Wc) memc a)
  by (intros a Ha; apply K; lia).
pose proof (ts_region_nth_c (TEB regs rg mo) _ _ 0 _ HS eq_refl) as HR0. cbn [ms_mem restrict] in HR0.
assert (V64 : spillB Wc (ms_mem ms) 64 (Z.of_nat i)).
{ unfold crt_spill.
  apply (ct5_fld (TEB regs rg mo) _ 41 sp1 _ 0 96 64 72 64 (SOff 53 (-1)) (Z.of_nat i) HR0 U41); [ct5_in | | lia].
  rewrite (ct6_denot_off (TEB regs rg mo) 53%nat (-1) (Z.of_nat i + 1) A53) by lia. f_equal. lia. }
assert (HDR1 : crt_dregs_B (regs := regs) (doc := doc) (ms_regs ms) (frame_addr lyc CRT_CID pos)).
{ refine {| crt_dregs_B_bregs := _; crt_dregs_B_s6 := _ |}; [|rewrite <- R22; ct6_keep HS].
  apply (ct6_bregs_eq regs rg (ms_regs ms) _ HBR); intros r Hr; unfold CT6_BREGS in Hr; cbn [In] in Hr;
  repeat (destruct Hr as [<- | Hr]; [ct6_keep HS|]); destruct Hr. }
assert (HCORE1 : CORE fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw).
{ refine (ct5_core_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
    HPRE HTREE fxk lyc Sc Hpc Wc memc mdc kj pos Dc Dback Lamc peakc cntc rg mms cset saved kw (ms_mem ms) mdc'
    (ms_regs ms) (fun a => sp1 + 64 <= a < sp1 + 72) HCORE HJ HB_HJ ltac:(intros a Ha; cbv beta in Ha; lia)
    ltac:(intros a Ha Hn; apply K; [exact Ha | cbv beta in Hn; exact Hn]) HPM HDR1
    (KSP CRT_SP_SAVED_B saved ltac:(unfold CRT_SP_SAVED_B; lia) S0) (KSP 8 nn ltac:(lia) S8)
    (KSP CRT_SP_KEYS_B _ ltac:(unfold CRT_SP_KEYS_B; lia) S48) (KSP CRT_SP_BACK _ ltac:(unfold CRT_SP_BACK; lia) S56)
    (KSP CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80) (KSP CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88)). }
assert (Hkd1 : rd_u64 SEGS (mrestrict (w_H Wc) (ms_mem ms)) (doc + PJ_OFF_KEYS) kd).
{ destruct Hkd as (Hk1 & Hk2). split; [exact Hk1|]. apply (ts_vm_av (w_H Wc) (w_H Wc) memc (ms_mem ms) _ 8 _); [|exact Hk2].
  intros k Hk. apply KL. unfold PJ_OFF_KEYS. lia. }
assert (HL1' : L1B fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw kd i).
{ refine (conj HCORE1 (conj _ (conj _ (conj _ (conj (KSP 16 _ ltac:(lia) S16) (conj (KSP 24 _ ltac:(lia) S24)
    (conj (KSP 32 _ ltac:(lia) S32) (conj (KSP 40 _ ltac:(lia) S40) (conj (KSP 72 _ ltac:(lia) S72) (conj Hkd1
    (conj Hi Hbefore))))))))))).
  - rewrite <- R21. ct6_keep HS.
  - ct6_reg HS (24%bv : bv 5) Hr. rewrite Hr. apply (ct6_denot_at _ 66%nat _ A66); lia.
  - ct6_reg HS (26%bv : bv 5) Hr. rewrite Hr. apply (ct6_denot_at _ 66%nat _ A66); lia. }
(* the call's arguments *)
assert (Hsp1 : spZ (ms_regs ms) = sp1).
{ pose proof (crt_bregs_B_sp (crt_dregs_B_bregs HDR1)) as R2c. unfold spZ. rewrite R2c. unfold w64. apply unsigned_lit_small. lia. }
pose proof (crt_bregs_B_gp (crt_dregs_B_bregs HDR1)) as R3c. pose proof (crt_bregs_B_tp (crt_dregs_B_bregs HDR1)) as R4c.
ct6_reg HS (10%bv : bv 5) Q10. rewrite (ct6_denot_at _ 67%nat xd A67) in Q10 by lia.
ct6_reg HS (11%bv : bv 5) Q11.
rewrite (ct5_img_den _ 243 69824 (@CRT_MOD_AT_B _ PA) HEI ltac:(unfold A_TEXT, A_LIM; lia) ltac:(vm_compute; reflexivity))
  in Q11.
destruct (cb7k_ret CRT_K_OFF5_B ltac:(unfold CRT_K_OFF5_B; lia) ltac:(reflexivity)) as (Hr1 & Hr2 & Hr3).
ct6_reg HS (1%bv : bv 5) Q1.
assert (E240 : ew (TEB regs rg mo) 240 = Z_to_bv 64 BASE)
  by exact (te_img (L := B_prog_listing) (PA := PA) regs rg mo 240 ltac:(vm_compute; lia)).
lazymatch type of Q1 with context [SOff 240 ?c] =>
  replace c with (CRT_PC_B + CRT_K_OFF5_B) in Q1 by (vm_compute; reflexivity) end.
assert (HPC : 0 <= CRT_PC_B < 2 ^ 16) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
assert (HBS : 4096 <= BASE < 2 ^ 30) by (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity).
rewrite (ct6_denot_off _ 240 _ BASE E240) in Q1 by (unfold CRT_K_OFF5_B; lia).
pose proof HPRE as ((_ & _ & _ & Hgp & Htp & _) & _).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite R3c; exact Hgp).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite R4c; exact Htp).
pose proof HCORE1 as (_ & _ & _ & HLm & _).
destruct (crt_live_journal HLm) as (WS_HJm & HJm & HB_HJm). pose proof (crt_side_arodata (crt_live_side HLm)) as HROm.
assert (Hcd1 : pj_cstrR SEGS (mrestrict (w_H Wc) (ms_mem ms)) (prh_lin Lamc) xd kxd nm).
{ apply (ct5_cstr_keep _ _ _ _ _ _ Hcd). intros y Hy. apply (mbyte_of_aview SEGS). apply KL. lia. }
destruct (@cb7t_str_prem rc prh_img_B B_prog_listing PA B ARx LAWS lyc Sc Hpc Wc memc Lamc peakc cntc SIZE_MAXZ 0 most 0
  lyc Sc Hpc Wc (ms_mem ms) mdc' (ms_regs ms) xd kxd nm HLED (proj1 HJm) eq_refl eq_refl Hcd1
  ltac:(rewrite Hsp1; lia))
  as (Xd0 & Xd1 & Xd2 & Xd3 & Xdfb & Xdsrc & Xdlo & Xdam & Xdra & Xdhv & Xdtl).
destruct (cb7t_rom_prem_mod_at B ARx LAWS BOK IMGVIS lyc Sc Hpc Wc (ms_mem ms) mdc' (ms_regs ms) (proj1 HJm) HROm HKMA
  ltac:(rewrite Hsp1; lia))
  as (Y0 & Y1 & Y2 & Y3 & Yfb & Ysrc & Ylo & Yam & Yra & Yhv & Ytl).
(* strcmp's rule over the R journal (the engine's YGcallMxmn.aj_strcmp_at_xromR): the journal
   rebased to the current depot (YCbqGwild.ajournal_xw_rebaseR) and stepped back to its budget after it
   (YCbqGwild.ajournal_xw_unbase0R); the plain SRr conclusion is lifted by YA0nH.SRr_SRr' under YSRrG.SRr'_bind *)
pose proof (crt_jw_wild B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJm) as Hinc.
pose proof HJm as HJr. apply YCbqGwild.ajournal_xw_rebaseR in HJr.
eapply (YSRrG.SRr'_bind SEGS YGcfRehidePost.RZ_cf).
{ apply YA0nH.SRr_SRr'.
  refine (YGcallMxmn.aj_strcmp_at_xromR (SK := SK) SEGS B PST ARx RLO RHI LAWS (@pa_segs_low rc B_prog_listing PA)
    (YA0nH.wle' SEGS YGcfRehidePost.RZ_cf) (YA0nH.wle'_refl SEGS YGcfRehidePost.RZ_cf)
    (YA0nH.wle'_trans SEGS YGcfRehidePost.RZ_cf)
    (SIGMA AS___wrap_strcmp) (ASTRCMP fxk) Wc (ms_regs ms) (ms_mem ms) STKC sp0 [] ly (set_depot (st_depot Sc) S) Hp W
    mem md [(CRT_CID, pos)]
    lyc Sc Hpc mdc' kj xd (@CRT_MOD_AT_B _ PA) (Z.of_nat (length nm)) (Z.of_nat (length ck_MOD_AT)) (sp1 - sp0) _ HJr
    Q10 Q11 _ _ _ _ _ _ _ _ _ _ _ _ Q3 Q4 Q1 _ Xdfb Yfb Xdsrc Ysrc _ _ Xdam Yam Xdra Xdhv Yra Yhv Xdtl Ytl HROm).
  all: try lia.
  all: first [ (apply (ret_ok_codeptr_v (PI := PA)); [exact Hr3 | exact Hr2])
             | (intros a Ha; pose proof (Xdlo a Ha); lia)
             | (intros a Ha; pose proof (Ylo a Ha); lia) ]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & vr & -> & HJ3 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & HMN2).
eapply YCbqGwild.ajournal_xw_unbase0R in HJ3; [|exact Hinc].
(* after the call: the L1 facts at the new memory, slot 0x40 kept, and the compare's answer *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
  aview SEGS (w_H Wc) mem2 a = aview SEGS (w_H Wc) (ms_mem ms) a).
{ intros a Ha Hn. apply Hfr2; [exact Ha|]. replace (sp0 + (sp1 - sp0)) with sp1 by lia. exact Hn. }
assert (KSP2 : forall off v, 0 <= off < 2 ^ 32 -> spillB Wc (ms_mem ms) off v -> spillB Wc mem2 off v).
{ intros off v Hoff Hv'. unfold crt_spill in *. apply (ts_vm_av (w_H Wc) (w_H Wc) (ms_mem ms) mem2 _ 8 _); [|exact Hv'].
  intros k Hk. apply K2; lia. }
pose proof HCORE1 as (_ & _ & _ & _ & _ & S0' & S8' & S48' & S56' & S80' & S88' & _).
assert (HDR2 : crt_dregs_B (regs := regs) (doc := doc) regs2 (frame_addr lyc CRT_CID pos)).
{ pose proof (crt_dregs_B_bregs HDR1) as HB1. pose proof (crt_dregs_B_s6 HDR1) as H22.
  refine {| crt_dregs_B_bregs := ct6_bregs_pres regs _ regs2 _ HB1 HP2; crt_dregs_B_s6 := _ |}.
  rewrite (ts_ap _ regs2 22%bv HP2) by ts_cs. exact H22. }
assert (HCORE2 : CORE fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc regs2 mms cset saved kw).
{ refine (ct5_core_run B ARx LAWS rp_sm rp_x rp_os rp_i rp_H0 ly S Hp W regs mem md ch doc t D x Lam peak cnt most
    HPRE HTREE fxk lyc Sc Hpc Wc (ms_mem ms) mdc' kj pos Dc Dback Lamc peakc cntc (ms_regs ms) mms cset saved kw mem2 md2
    regs2 (fun a => sp1 - 2 * ESTACK <= a < sp1) HCORE1 HJ3 HB_HJm ltac:(intros a Ha; cbv beta in Ha; lia)
    ltac:(intros a Ha Hn; apply K2; [exact Ha | cbv beta in Hn; exact Hn]) (fun H0 => HMN2 (HPM H0)) HDR2
    (KSP2 CRT_SP_SAVED_B _ ltac:(unfold CRT_SP_SAVED_B; lia) S0') (KSP2 8 _ ltac:(lia) S8')
    (KSP2 CRT_SP_KEYS_B _ ltac:(unfold CRT_SP_KEYS_B; lia) S48') (KSP2 CRT_SP_BACK _ ltac:(unfold CRT_SP_BACK; lia) S56')
    (KSP2 CRT_SP_SHN_B _ ltac:(unfold CRT_SP_SHN_B; lia) S80') (KSP2 CRT_SP_PN_B _ ltac:(unfold CRT_SP_PN_B; lia) S88')). }
pose proof HL1' as (_ & R21' & R24' & R26' & S16' & S24' & S32' & S40' & S72' & Hkd' & _).
assert (HL1'' : L1B fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc regs2 mms cset saved kw kd i).
{ refine (conj HCORE2 (conj _ (conj _ (conj _ (conj (KSP2 16 _ ltac:(lia) S16') (conj (KSP2 24 _ ltac:(lia) S24')
    (conj (KSP2 32 _ ltac:(lia) S32') (conj (KSP2 40 _ ltac:(lia) S40') (conj (KSP2 72 _ ltac:(lia) S72') (conj _
    (conj Hi Hbefore))))))))))).
  - rewrite (ts_ap _ regs2 21%bv HP2) by ts_cs. exact R21'.
  - rewrite (ts_ap _ regs2 24%bv HP2) by ts_cs. exact R24'.
  - rewrite (ts_ap _ regs2 26%bv HP2) by ts_cs. exact R26'.
  - destruct Hkd' as (Hk1 & Hk2). split; [exact Hk1|].
    apply (ts_vm_av (w_H Wc) (w_H Wc) (ms_mem ms) mem2 _ 8 _); [|exact Hk2].
    intros k Hk. unfold PJ_OFF_KEYS. apply K2; lia. }
change (YA0nH.SRr' SEGS YGcfRehidePost.RZ_cf Wc (cfgB fxk CRT_K_OFF5_B regs2 mem2 md2) QFb).
apply (ct5_K Pd HL2s i mms IH fxk lyc Sc Hpc Wc mem2 md2 kj pos Dc Dback Lamc peakc cntc regs2 cset saved kw kd HL1''
  (KSP2 64 _ ltac:(lia) V64)).
- intros nm' u' Enth'. rewrite Enth in Enth'. injection Enth' as <- <-. rewrite Hv.
  apply (ct5_cmp Wc memc (prh_lin Lamc) xd kxd (@CRT_MOD_AT_B _ PA) nm ck_MOD_AT vr Hcd).
  + apply (ct5_rom_bytes Wc memc _ ck_MOD_AT HROc HKMA).
    exact (proj1 (crt_str_rom_B (PA := PA) cb7t_base_B eq_refl)).
  + rewrite Hcmp. split; intros (El & He); split; try exact El; intros j Hj; specialize (He j Hj).
    * pose proof (Xdlo (xd + j) ltac:(lia)). pose proof (Ylo (@CRT_MOD_AT_B _ PA + j)) as HY.
      assert (HY' : @CRT_MOD_AT_B _ PA + j < YM05.alloc_ceiling).
      { apply HY. split; [lia|]. lia. }
      rewrite <- !KL by lia. exact He.
    * pose proof (Xdlo (xd + j) ltac:(lia)). pose proof (Ylo (@CRT_MOD_AT_B _ PA + j)) as HY.
      assert (HY' : @CRT_MOD_AT_B _ PA + j < YM05.alloc_ceiling) by (apply HY; lia).
      rewrite !KL by lia. exact He.
- exact HPd.
Qed.

End g.
End f.
End t5w.
