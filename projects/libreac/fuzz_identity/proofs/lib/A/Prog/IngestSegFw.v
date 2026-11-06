(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:358-361
   [Apache-2.0]; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC4t.v:438 [Apache-2.0 OR MIT], for libreac/fuzz_identity's ASan
   build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/IngestWalk.v; 463 of its 539 lines of code are new or changed and 291 lines of the source are left out. *)
(* The firmware arm of the walk of reac_identity_ingest (fuzz_identity.asan), the statement ting_seg_fw of
   lib/A/Prog/IngestSeg.v: 0x83944 .. 0x83984 (the digit loop; its counter a4 is the literal 4 at the hand-over,
   so the walk unrolls its four rounds), 0x83c08 .. 0x83c9c (p[0] * 1000 + p[1] * 100 + p[2] * 10 + p[3] to id,
   2 bytes), 0x83ca0 .. 0x83cb8 (1 to id + 2), and the tail 0x83cbc .. ret (reac_identity_ingest.v ing_tail).
   A byte above 9 leaves the loop for 0x83b48 (a4 := 0) and the tail; nothing is written then.
   Every shadow test is decided by two shadow entries: the payload's first four bytes (they lie in a heap block of
   the caller, so AR gives their shadow) and the record (ting_rec_ok's range_addressable). The record's region is
   added to the symbolic state only for the stores after the loop, so the runs of the loop and of the exits write
   nothing. The functional result is the plain model, used as it is: RcIdentLib.ING_fw and RcIdentLib.fw_bad. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase IdentCJ YC4b
reac_identity_ingest IngestSeg.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel RcIdentLib reac_identity_ingest_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Lemma if_bz_range : forall b, 0 <= RcIdentModel.bz b < 256.
Proof.
  intros b. unfold RcIdentModel.bz. pose proof (bv_unsigned_in_range 8 b) as H.
  change (bv_modulus 8) with 256 in H. exact H.
Qed.
Lemma if_nth_error_skipn : forall (l : list byte) n i, nth_error (skipn n l) i = nth_error l (n + i).
Proof.
  induction l as [|x l IH]; intros [|n] i; cbn [skipn Nat.add]; [reflexivity | destruct i; reflexivity | reflexivity |].
  cbn [nth_error]. apply IH.
Qed.
(* A range the shadow says is addressable stays so when the shadow cells it reads are kept. *)
Lemma if_ra_kept : forall (rd rd' : Z -> option Z) a len,
  (forall x, a <= x < a + len -> rd' (shadow_of_addr SHADOW_OFF x) = rd (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable rd SHADOW_OFF a len -> range_addressable rd' SHADOW_OFF a len.
Proof.
  intros rd rd' a len Hk H x Hx. destruct (H x Hx) as (s & Hs & Hok). exists s.
  rewrite (Hk x Hx). split; [exact Hs | exact Hok].
Qed.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* The test 0x83964 bltu a3,a7 with a3 = 9 and a7 the zero-extended payload byte j (atom 33 + j). *)
Lemma if_digit : forall E' (j : nat) (b : byte) (c : bool),
  ew E' (33 + j) = Z_to_bv 64 (RcIdentModel.bz b) ->
  branch_taken BC_LTU (sv_denot E' (SLit 9)) (sv_denot E' (SExt false 8 (SOff (33 + j) 0))) = c ->
  (9 <? RcIdentModel.bz b) = c.
Proof.
  intros E' j b c Hb Hc. pose proof (if_bz_range b) as R.
  rewrite branch_ltu_U in Hc. rewrite U_lit in Hc by lia. rewrite U_SExt in Hc. cbv iota in Hc.
  rewrite (U_atom E' (33 + j) _ Hb) in Hc by lia.
  change (2 ^ Z.of_N 8) with 256 in Hc. rewrite (Z.mod_small (RcIdentModel.bz b) 256) in Hc by lia.
  rewrite zcanon_id in Hc by (unfold M64; lia). exact Hc.
Qed.
(* The value 0x83c78 .. 0x83c94 compute from the four payload bytes. *)
Lemma if_U_ext8 : forall E' n b, ew E' n = Z_to_bv 64 b -> 0 <= b < 256 -> U E' (SExt false 8 (SOff n 0)) = b.
Proof.
  intros E' n b Hn Hb. rewrite U_SExt. cbv iota. rewrite (U_atom E' n b Hn) by lia.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma if_U_mul : forall E' x a c, U E' x = a -> 0 <= a -> 0 <= c < 2 ^ 64 -> a * c < 2 ^ 64 ->
  U E' (SMd M_MUL x (SLit c)) = a * c.
Proof.
  intros E' x a c Hx Ha Hc Hac. rewrite U_SMd, Hx, U_SLit. rewrite (zcanon_id c) by (unfold M64; lia).
  cbn [zmd_raw]. apply zcanon_id. unfold M64. nia.
Qed.
Lemma if_U_add : forall E' x y a b, U E' x = a -> U E' y = b -> 0 <= a -> 0 <= b -> a + b < 2 ^ 64 ->
  U E' (SAlu ALU_ADD x y) = a + b.
Proof. intros E' x y a b Hx Hy Ha Hb Hab. rewrite U_SAlu, Hx, Hy. cbn [zalu_raw]. apply zcanon_id. unfold M64. lia. Qed.
Definition if_sum_sv : sv :=
  SAlu ALU_ADD
    (SAlu ALU_ADD (SMd M_MUL (SExt false 8 (SOff 34 0)) (SLit 100)) (SMd M_MUL (SExt false 8 (SOff 33 0)) (SLit 1000)))
    (SAlu ALU_ADD (SMd M_MUL (SExt false 8 (SOff 35 0)) (SLit 10)) (SExt false 8 (SOff 36 0))).
Lemma if_sum : forall E' (pb : list byte),
  ew E' 33 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 0)) ->
  ew E' 34 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 1)) ->
  ew E' 35 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 2)) ->
  ew E' 36 = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb 3)) ->
  bv_unsigned (sv_denot E' if_sum_sv) = RcIdentModel.fw_value pb.
Proof.
  intros E' pb P0 P1 P2 P3.
  pose proof (if_bz_range (RcIdentModel.nthb pb 0)) as R0. pose proof (if_bz_range (RcIdentModel.nthb pb 1)) as R1.
  pose proof (if_bz_range (RcIdentModel.nthb pb 2)) as R2. pose proof (if_bz_range (RcIdentModel.nthb pb 3)) as R3.
  unfold RcIdentModel.fw_value.
  set (b0 := RcIdentModel.bz (RcIdentModel.nthb pb 0)) in *. set (b1 := RcIdentModel.bz (RcIdentModel.nthb pb 1)) in *.
  set (b2 := RcIdentModel.bz (RcIdentModel.nthb pb 2)) in *. set (b3 := RcIdentModel.bz (RcIdentModel.nthb pb 3)) in *.
  pose proof (if_U_ext8 E' 33 b0 P0 R0) as X0. pose proof (if_U_ext8 E' 34 b1 P1 R1) as X1.
  pose proof (if_U_ext8 E' 35 b2 P2 R2) as X2. pose proof (if_U_ext8 E' 36 b3 P3 R3) as X3.
  pose proof (if_U_mul E' _ b1 100 X1 ltac:(lia) ltac:(lia) ltac:(lia)) as M1.
  pose proof (if_U_mul E' _ b0 1000 X0 ltac:(lia) ltac:(lia) ltac:(lia)) as M0.
  pose proof (if_U_mul E' _ b2 10 X2 ltac:(lia) ltac:(lia) ltac:(lia)) as M2.
  pose proof (if_U_add E' _ _ _ _ M1 M0 ltac:(lia) ltac:(lia) ltac:(lia)) as A1.
  pose proof (if_U_add E' _ _ _ _ M2 X3 ltac:(lia) ltac:(lia) ltac:(lia)) as A2.
  pose proof (if_U_add E' _ _ _ _ A1 A2 ltac:(lia) ltac:(lia) ltac:(lia)) as A3.
  change (bv_unsigned (sv_denot E' if_sum_sv)) with (U E' if_sum_sv). unfold if_sum_sv. rewrite A3. lia.
Qed.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
(* The walk's symbolic state at 0x83944: the registers of the hand-over (a4 is pinned to the literal 4 by the
   walk), the payload's first four bytes (pay_region 4, atoms 33 .. 36), and the facts the shadow tests need:
   atom 10 is id (8-aligned), atom 12 is p, atom 16 is a6, the shadow base. *)
Definition Bx_IF : sv := SOff 16 0.
Definition if_SH : list shent := [mkSHE 12 0 4; mkSHE 10 0 38].
Definition if_facts : facts :=
  mkFacts [ (10%nat, mkAF 4096 (2 ^ 47 - 38) 3); (12%nat, mkAF 4096 (2 ^ 47 - 4) 0);
            (16%nat, mkAF SB_ING SB_ING 0) ] [] [].
Definition ss_if : sstate := mkSS AF_ing_fw sr_atoms [pay_region 4] None if_facts.
Definition EIF (regsT : bvmap 5 word) (pb : list byte) : env := Eimg (Ereg regsT (ing_extra pb)).
(* The callee-saved registers the arm does not touch (all but sp). *)
Definition IF_KEPT : list (bv 5) := [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma if_in_kept : forall q, 0 <= q < 32 ->
  existsb (fun r : bv 5 => Z.eqb (bv_unsigned r) q) IF_KEPT = true -> In (Z_to_bv 5 q) IF_KEPT.
Proof.
  intros q Hq H. apply existsb_exists in H as (r & Hin & Hr). apply Z.eqb_eq in Hr.
  replace (Z_to_bv 5 q) with r; [exact Hin|]. apply bv_eq. rewrite Z_to_bv_unsigned, Hr.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma if_kept_q : forall q, acallee_saved q -> q <> 2 -> In (Z_to_bv 5 q) IF_KEPT.
Proof.
  intros q Hq Hq2. apply if_in_kept; [unfold acallee_saved in Hq; lia|].
  assert (Hc : q = 3 \/ q = 4 \/ q = 8 \/ q = 9 \/ q = 18 \/ q = 19 \/ q = 20 \/ q = 21 \/ q = 22
               \/ q = 23 \/ q = 24 \/ q = 25 \/ q = 26 \/ q = 27)
    by (unfold acallee_saved in Hq; lia).
  clear - Hc.
  repeat (destruct Hc as [Hc | Hc]; [subst q; vm_compute; reflexivity |]).
  subst q; vm_compute; reflexivity.
Qed.
Lemma EIF_reg : forall regsT pb n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (EIF regsT pb) n = getr regsT r.
Proof.
  intros regsT pb n r Hn. unfold EIF. rewrite Eimg_low; [apply ew_Ereg_nat; exact Hn|].
  pose proof (bv_unsigned_in_range 5 r) as Q. change (bv_modulus 5) with 32 in Q. unfold A_TEXT. lia.
Qed.
Lemma EIF_pay : forall regsT pb j, (j < 17)%nat ->
  ew (EIF regsT pb) (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j)).
Proof.
  intros regsT pb j Hj. unfold EIF. rewrite Eimg_low by (unfold A_TEXT; lia).
  replace (33 + j)%nat with (32 + Datatypes.S j)%nat by lia. rewrite ew_Ereg_extra. exact (ing_extra_pay pb j Hj).
Qed.
Lemma EIF_agree : forall regsT pb, env_agree 32 (Ereg regsT (ing_extra pb)) (EIF regsT pb).
Proof.
  intros regsT pb. split; [|reflexivity]. intros n Hn. unfold EIF. rewrite Eimg_low by (unfold A_TEXT; lia).
  reflexivity.
Qed.
(* The record after the stores: the value's two bytes at id, 1 at id + 2, the rest kept. *)
Lemma if_rec_bytes : forall (m mc : word -> option byte) id (idb pb : list byte) (v : word),
  length idb = RcIdentModel.ID_SIZE ->
  mbytes_at SEGS mc id idb ->
  (forall j, (3 <= j < 38)%nat -> mbyte SEGS m (id + Z.of_nat j) = mbyte SEGS mc (id + Z.of_nat j)) ->
  mbyte SEGS m (id + 0 + 0) = Some (byte_of_word v 0) ->
  mbyte SEGS m (id + 0 + 1) = Some (byte_of_word v 1) ->
  mbyte SEGS m (id + 2 + 0) = Some (byte_of_word (Z_to_bv 64 1) 0) ->
  bv_unsigned v = RcIdentModel.fw_value pb ->
  mbytes_at SEGS m id
    (RcIdentModel.upd (RcIdentModel.upd idb RcIdentModel.OFF_FW (RcIdentModel.le16 (RcIdentModel.fw_value pb)))
       RcIdentModel.OFF_HAS_FW [RcIdentModel.zb 1]).
Proof.
  intros m mc id idb pb v Hl Hmc Hk M0 M1 M2 Hv j Hj.
  assert (Lin : length (RcIdentModel.upd idb RcIdentModel.OFF_FW (RcIdentModel.le16 (RcIdentModel.fw_value pb)))
                = RcIdentModel.ID_SIZE)
    by (rewrite RcIdentModel.upd_length; [exact Hl | rewrite Hl; unfold RcIdentModel.ID_SIZE, RcIdentModel.OFF_FW; cbn; lia]).
  assert (Lout : length (RcIdentModel.upd (RcIdentModel.upd idb RcIdentModel.OFF_FW
                   (RcIdentModel.le16 (RcIdentModel.fw_value pb))) RcIdentModel.OFF_HAS_FW [RcIdentModel.zb 1])
                 = RcIdentModel.ID_SIZE)
    by (rewrite RcIdentModel.upd_length; [exact Lin | rewrite Lin; unfold RcIdentModel.ID_SIZE, RcIdentModel.OFF_HAS_FW; cbn; lia]).
  rewrite Lout in Hj. unfold RcIdentModel.ID_SIZE in Hj, Lin.
  destruct (Nat.lt_ge_cases j 3) as [J3 | J3].
  2: { rewrite (nth_error_nth' _ (RcIdentModel.zb 0)) by (rewrite Lout; unfold RcIdentModel.ID_SIZE; lia).
       change (nth j ?l (RcIdentModel.zb 0)) with (RcIdentModel.nthb l j).
       rewrite RcIdentLib.nthb_upd_ge by (cbn [length]; unfold RcIdentModel.OFF_HAS_FW; lia).
       rewrite RcIdentLib.nthb_upd_ge by (rewrite ?RcIdentLib.length_le16; unfold RcIdentModel.OFF_FW; lia).
       rewrite (Hk j ltac:(lia)). rewrite (Hmc j ltac:(rewrite Hl; unfold RcIdentModel.ID_SIZE; lia)).
       apply nth_error_nth'. rewrite Hl. unfold RcIdentModel.ID_SIZE. lia. }
  clear Lin Lout.
  unfold RcIdentModel.upd, RcIdentModel.OFF_FW, RcIdentModel.OFF_HAS_FW, RcIdentModel.le16.
  cbn [app firstn skipn length Nat.add].
  set (fw := RcIdentModel.fw_value pb) in *.
  destruct j as [|[|[|j]]]; cbn [nth_error]; [| | | lia].
  - replace (id + Z.of_nat 0) with (id + 0 + 0) by lia. rewrite M0. f_equal.
    unfold byte_of_word, RcIdentModel.zb. rewrite Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
    rewrite Z.mul_0_r, Z.shiftr_0_r. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_mod by lia. reflexivity.
  - replace (id + Z.of_nat 1) with (id + 0 + 1) by lia. rewrite M1. f_equal.
    unfold byte_of_word, RcIdentModel.zb. rewrite Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
    change (8 * 1) with 8. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
  - replace (id + Z.of_nat 2) with (id + 2 + 0) by lia. rewrite M2. f_equal; apply bv_eq; reflexivity.
Qed.
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* Where the record lies, it is off the shadow band. *)
Lemma if_rec_app : forall STK sp0 FP ly S own lyc Sc W memc mdc sp id idb,
  AR SEGS B lyc Sc W memc mdc -> alloc_ceiling <= ly_stk_lo lyc ->
  ting_rec_ok B STK sp0 FP ly S own lyc Sc W memc sp id idb ->
  id + 38 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= id.
Proof.
  intros STK sp0 FP ly S own lyc Sc W memc mdc sp id idb HAR Hslo HR.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct HR as (_ & HL & _).
  destruct HL as [(cid & pos & Hin & Hr) | Hs].
  - pose proof (Hr id ltac:(lia)) as Hr0. pose proof (Hr (id + 37) ltac:(lia)) as Hr1.
    unfold frame_rng, in_zr in Hr0, Hr1. cbn [fst snd] in Hr0, Hr1.
    destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F0 & Fc & Fapp).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
  - unfold SHADOW_OFF. lia.
Qed.
(* The symbolic state at the arm's entry, and the shadow entries of the payload's first four bytes and of the
   record. *)
Lemma if_entry : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) id p len idb pb
    (regsT : bvmap 5 word) memT mdT,
  ing_arm_at B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id 0 p len idb pb regsT memT mdT ->
  4 <= len ->
  st_ok_pi SEGS VAL (EIF regsT pb) ss_if
    (restrict (w_H W) (mkst regsT (Z_to_bv 64 (BASE + AF_ing_fw)) memT (seg_rom SEGS))) /\
  sh_ok SEGS Bx_IF if_SH (EIF regsT pb) (mrestrict (w_H W) memT).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb regsT memT mdT HA Hlen4.
  pose proof HA as (HJc & Hra & Hra4 & Hid & _ & Hp & Hlen & Hal16 & Hlo & Hhi & Hpl & HNR & HREC & HPAY & Hev & Hlive &
                    HJ & T10 & T12 & T13 & T16 & T2 & T1 & Tcs & Mra & Ms0 & Ms1 & KEEPT & GROWT).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hceil.
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (_ & _ & Hceil0 & _ & _ & H470 & _).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  pose proof HJ as (HART & _).
  pose proof HREC as (Hal8 & _ & HD & HW & HRA0 & Hidl & HMBc).
  destruct (ing_zones B LAWS STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs) id idb p len pb
              HARc Hceil Hslo Hshi HREC HPAY ltac:(lia))
    as (Zi & Zp & Zip & Zi4 & Zi47 & Zp4 & Zpc & Zsp & bi & Li & Hbin & Hb1 & Hb2).
  assert (HrqL : Li <= req_size Li) by (unfold req_size; destruct (Li =? 0) eqn:EL; [apply Z.eqb_eq in EL|]; lia).
  unfold INGEST_STK, ESTACK in *.
  (* the payload's bytes, now *)
  assert (HPB : mbytes_at SEGS (mrestrict (w_H W) memT) p pb).
  { destruct HPAY as (_ & HPB0). apply (mbytes_kept (w_H W) memc memT p pb); [|exact HPB0].
    intros j Hj. rewrite Hpl in Hj. apply KEEPT; lia. }
  (* the record's shadow, now *)
  assert (HRA : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF id 38).
  { apply (if_ra_kept (aview SEGS (w_H W) memc)); [|exact HRA0].
    intros x Hx. unfold shadow_of_addr.
    assert (0 <= x / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    apply KEEPT; unfold SHADOW_OFF; lia. }
  (* the payload's shadow: its block's *)
  assert (HRP : range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF p 4)
    by (apply (range_addressable_of_block SEGS B LAWS lyc Sc W memT mdT bi Li p 4 HART Hbin); lia).
  assert (HPapp : p + 4 <= SHADOW_OFF \/ SHADOW_OFF + 17592186044416 <= p).
  { destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bi Li HARc Hbin) as (_ & _ & _ & Happ & _).
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia. }
  pose proof (if_rec_app STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs) id idb HARc Hslo HREC) as HRapp.
  pose proof (EIF_reg regsT pb 10 10%bv eq_refl) as E10. rewrite T10 in E10. unfold w64 in E10.
  pose proof (EIF_reg regsT pb 12 12%bv eq_refl) as E12. rewrite T12 in E12. unfold w64 in E12.
  pose proof (EIF_reg regsT pb 16 16%bv eq_refl) as E16. rewrite T16 in E16. unfold w64 in E16.
  split.
  - rewrite restrict_mkst_fx. unfold ss_if. apply pa_entry_st_ok_full.
    + unfold EIF. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_nil].
      apply (pay_region_ok (EIF regsT pb) _ p pb 4 ltac:(lia) ltac:(rewrite Hpl; lia) E12 Hp ltac:(lia)
               (EIF_pay regsT pb) HPB).
    + cbn [pairwise_disjoint all_disjoint]. split; exact I.
    + split; [|split; exact I]. cbn [if_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E10, E12, E16, !unsigned_lit_small by (unfold SB_ING; lia).
      rewrite Z.pow_0_r, !Z.mod_1_r. change (2 ^ 3) with 8. unfold SB_ING. repeat split; lia.
  - unfold sh_ok, if_SH. constructor; [|constructor; [|constructor]].
    + apply (shent_ok_of_range SEGS (w_H W) memT (EIF regsT pb) Bx_IF 12 p 4 p 0 4 HRP).
      * unfold Bx_IF. rewrite (U_atom _ 16 SB_ING E16) by (unfold SB_ING; lia). reflexivity.
      * exact (U_atom _ 12 p E12 Hp).
      * lia.
      * lia.
      * intros x Hx. unfold SHADOW_OFF in *. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memT (EIF regsT pb) Bx_IF 10 id 38 id 0 38 HRA).
      * unfold Bx_IF. rewrite (U_atom _ 16 SB_ING E16) by (unfold SB_ING; lia). reflexivity.
      * exact (U_atom _ 10 id E10 Hid).
      * lia.
      * lia.
      * intros x Hx. unfold SHADOW_OFF in *. lia.
Qed.
(* The tail: from 0x83cbc with the result r in a4 and the record as the plain model says, the post of the call. *)
Lemma if_fin : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) id p len idb pb
    (regsT : bvmap 5 word) memT mdT (regsF : bvmap 5 word) memF mdF r,
  ing_arm_at B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id 0 p len idb pb regsT memT mdT ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k ->
  getr regsF 2 = getr regsT 2 -> getr regsF 14 = w64 r ->
  (forall q, acallee_saved q -> q <> 2 -> getr regsF (Z_to_bv 5 q) = getr regsT (Z_to_bv 5 q)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 3) -> aview SEGS (w_H W) memF a = aview SEGS (w_H W) memT a) ->
  (forall a, apresent (w_H W) memT a -> apresent (w_H W) memF a) ->
  fst (RcIdentModel.ING idb 0 pb) = r ->
  mbytes_at SEGS (mrestrict (w_H W) memF) id (snd (RcIdentModel.ING idb 0 pb)) ->
  SRr SEGS W (mkCfg (mkst regsF (Z_to_bv 64 (BASE + AF_ing_tail)) memF (seg_rom SEGS)) mdF)
    (treac_identity_ingest_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs id 0 p len idb pb).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb regsT memT mdT regsF memF mdF r
    HA HJF F2 F14 Fcs KF GF Hr HMB.
  pose proof HA as (HJc & Hra & Hra4 & Hid & _ & Hp & Hlen & Hal16 & Hlo & Hhi & Hpl & HNR & HREC & HPAY & Hev & Hlive &
                    HJ & T10 & T12 & T13 & T16 & T2 & T1 & Tcs & Mra & Ms0 & Ms1 & KEEPT & GROWT).
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hceil.
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (_ & _ & Hceil0 & _ & _ & H470 & _).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  pose proof HREC as (Hal8 & _ & HD & _).
  assert (Hr01 : 0 <= r < 2 ^ 64)
    by (rewrite <- Hr; destruct (RcIdentModel.ING_ret idb 0 pb) as [Q|Q]; rewrite Q; lia).
  assert (VK : forall a n v, spZ regs - 32 <= a -> a + Z.of_nat n <= spZ regs ->
            val_mem SEGS (mrestrict (w_H W) memT) a n v -> val_mem SEGS (mrestrict (w_H W) memF) a n v).
  { intros a n v H1 H2 Hv kk Hk. rewrite <- (Hv kk Hk).
    apply (mbyte_of_aview SEGS (w_H W) (w_H W) memT memF).
    apply KF; unfold INGEST_STK, ESTACK in *; lia. }
  eapply SRr_mono.
  { change (mkCfg (mkst regsF (Z_to_bv 64 (BASE + AF_ing_tail)) memF (seg_rom SEGS)) mdF)
      with (cfg_at SEGS (BASE + AF_ing_tail) regsF memF mdF).
    apply (ing_tail B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memF mdF k regs regsF r HJF Hra Hal16 Hlo Hhi).
    - rewrite F2. exact T2.
    - exact F14.
    - exact Hr01.
    - intros q Hq H2 _ _. rewrite (Fcs q Hq H2). exact (Tcs q Hq H2).
    - apply VK; [lia | cbn; lia | exact Mra].
    - apply VK; [lia | cbn; lia | exact Ms0].
    - apply VK; [lia | cbn; lia | exact Ms1]. }
  intros W' c' _ (HW' & regs2 & mem2 & md2 & Hc2 & HJ2 & HP & H10 & HM2).
  unfold treac_identity_ingest_post. split; [exact HW'|]. exists regs2, mem2, md2.
  split; [exact Hc2|].
  split; [unfold EV_INGEST; rewrite Z.add_0_r; exact HJ2|].
  split; [exact HP|].
  split; [rewrite H10; unfold reac_identity_ingest_c.ingest_ret; rewrite HNR, Hr; reflexivity|].
  assert (A2 : forall a, aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memF a)
    by (intros a; unfold aview, mbyte, mrestrict; rewrite HM2; reflexivity).
  split.
  - eapply (ing_kept_of B LAWS lyc Sc W memc mdc mem2 (spZ regs) _ HARc Hceil ltac:(lia)).
    + intros a Ha Hw HE. rewrite A2. rewrite KF; [apply KEEPT; [exact Ha | exact Hw] | exact Ha |].
      intros Hi. apply HE. unfold ting_E. split; [exact HNR | lia].
    + intros a Hpa. destruct (GF a (GROWT a Hpa)) as (Hh & b & Hb). split; [exact Hh|]. exists b.
      rewrite HM2. exact Hb.
    + intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpF & _).
      apply HpF. unfold INGEST_STK, ESTACK in *. lia.
    + intros a Hi (_ & Ha).
      exact (proj1 (ting_rec_apart B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HARc Hceil Hslo Hshi HREC Ha) Hi).
  - intros _. apply (mbytes_kept (w_H W) memF mem2 id _); [|exact HMB].
    intros j _. apply A2.
Qed.
(* After a run: memory is the hand-over's memory outside the zone [lo, hi) (the record bytes the stores may
   write), and nothing present went away. *)
Ltac if_keep U10 :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    HG : mem_grows (mrestrict (w_H ?W) ?m1) (mrestrict (w_H ?W) ?m2),
    KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (?lo <= a < ?hi) -> aview ?sg (w_H ?W) ?m1 a = aview ?sg (w_H ?W) ?m0 a,
    GROW : forall a, apresent (w_H ?W) ?m0 a -> apresent (w_H ?W) ?m1 a |- _ =>
    let K2 := fresh "K2" in let G2 := fresh "G2" in
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview sg (w_H W) m2 a = aview sg (w_H W) m0 a);
    [ let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
      intros a Ha Hw; transitivity (aview sg (w_H W) m1 a); [| exact (KEEPM a Ha Hw)];
      apply (kept_of_frame Ex rs (w_H W) m1 m2 (fun x => lo <= x < hi) HFr); [| exact Ha | exact Hw];
      let bb := fresh "bb" in let wl := fresh "wl" in let wh := fresh "wh" in let aa := fresh "aa" in
      let Hin := fresh "Hin" in let Hr := fresh "Hr" in
      intros bb wl wh aa Hin Hr;
      let w := eval vm_compute in (windows rs) in change (windows rs) with w in Hin;
      repeat (destruct Hin as [Hin | Hin];
              [ injection Hin as <- <- <-; cbn [base_val] in Hr;
                cbn [ew ewset havoc Nat.eqb Nat.ltb extK] in Hr; rewrite ?U10 in Hr; clear - Hr; lia | ]);
      destruct Hin
    | assert (G2 : forall a, apresent (w_H W) m0 a -> apresent (w_H W) m2 a)
        by (let a := fresh "a" in let Hp := fresh "Hp" in
            intros a Hp; exact (apresent_grows _ _ _ a HG (GROW a Hp)));
      clear KEEPM GROW HFr HG; rename K2 into KEEPM; rename G2 into GROW ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
(* A run's write right: the payload region is read-only; the record region writes [id, id + 3), which the caller
   lets the call write (ting_rec_ok). *)
Ltac if_awr U10 HW :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; first [apply Z.le_refl | lia] |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat);
    [ reflexivity | cbn [ew ewset Nat.eqb]; exact U10
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in
      intros a Ha; exact (proj1 (HW a ltac:(clear - Ha; lia))) | ] ].
(* The payload byte j against 9, from the branch at 0x83964. *)
Ltac if_dig EP pb D j :=
  lazymatch goal with
  | Hc : branch_taken BC_LTU (sv_denot ?Ex (SLit 9)) _ = _ |- _ =>
    let Hb := fresh "Hb" in
    assert (Hb : ew Ex (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j)))
      by (cbn [ew ewset Nat.eqb Nat.add]; exact (EP j (proj1 (Nat.ltb_lt j 17) eq_refl)));
    pose proof (if_digit Ex j _ _ Hb Hc) as D; clear Hc Hb
  end.
(* At 0x83cbc: the tail lemma, with the registers and the memory facts of the last run. Leaves the result and
   the record. *)
Ltac if_tail r HA E2 HAE HJ KEEPM GROW :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H ?W) ?msx) |- _ =>
    pmkst HS;
    change (BASE + 13744) with (BASE + AF_ing_tail);
    let R2 := fresh "R2" in let R14 := fresh "R14" in
    prreg HS (2%bv : bv 5) R2; prreg HS (14%bv : bv 5) R14;
    eapply (if_fin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r HA);
    [ exact HJ
    | rewrite R2; exact E2
    | rewrite R14; reflexivity
    | let q := fresh "q" in let Hq := fresh "Hq" in let Hq2 := fresh "Hq2" in
      intros q Hq Hq2;
      eapply (regs_kept_of_st_ok_pi _ _ _ _ _ IF_KEPT HS);
      [ env_agree_chain HAE | vm_compute; reflexivity | exact (if_kept_q q Hq Hq2) ]
    | let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in let Hc := fresh "Hc" in
      intros a Ha Hw; apply KEEPM; [exact Ha | intros Hc; apply Hw; clear - Hc; lia]
    | exact GROW
    | |]
  end.
(* A digit above 9 at round j: 0x83b48 a4 := 0, the tail; ING returns (0, idb) and nothing was written. *)
Ltac if_bad j EP pb idb Hl4 HA E2 HAE U10 HARc Hceil Hslo Hshi HREC KEEPT HS HJ SHOK KEEPM GROW :=
  lazymatch goal with
  | Hc : branch_taken BC_LTU (sv_denot ?Ex (SLit 9)) _ = true |- _ =>
    let Hb := fresh "Hb" in let D := fresh "D" in let HING := fresh "HING" in
    assert (Hb : ew Ex (33 + j) = Z_to_bv 64 (RcIdentModel.bz (RcIdentModel.nthb pb j)))
      by (cbn [ew ewset Nat.eqb Nat.add]; exact (EP j (proj1 (Nat.ltb_lt j 17) eq_refl)));
    pose proof (if_digit Ex j _ _ Hb Hc) as D; apply Z.ltb_lt in D;
    assert (HING : RcIdentModel.ING idb 0 pb = (0, idb))
      by exact (RcIdentLib.fw_bad idb pb j Hl4 (proj1 (Nat.ltb_lt j 4) eq_refl) D);
    clear Hc Hb;
    paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING 13744%Z; [awr_ok_tac|];
    if_keep U10;
    if_tail 0 HA E2 HAE HJ KEEPM GROW;
    [ rewrite HING; reflexivity
    | rewrite HING; cbn [snd];
      lazymatch goal with
      | KM : forall a, 0 <= a < 2 ^ 64 -> ~ (?x <= a < ?x) -> aview ?sg ?H ?m1 a = aview ?sg ?H ?m0 a |- _ =>
        apply (ting_rec_kept B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 HARc Hceil Hslo Hshi HREC);
        let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
        intros a Ha Hw; rewrite (KM a Ha ltac:(let Hz := fresh "Hz" in intros Hz; clear - Hz; lia));
        exact (KEEPT a Ha Hw)
      end ]
  end.
Theorem pb_ing_seg_fw : ting_seg_fw B.
Proof.
  unfold ting_seg_fw.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id ad p len idb pb regsT memT mdT HA Had0 Hlen4 H14.
  subst ad.
  pose proof pa_segs_low as Hsegs.
  destruct (if_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs id p len idb pb regsT memT mdT HA Hlen4)
    as [HS0 SHOK].
  pose proof HA as (HJc & Hra & Hra4 & Hid & _ & Hp & Hlen & Hal16 & Hlo & Hhi & Hpl & HNR & HREC & HPAY & Hev & Hlive &
                    HJ & T10 & T12 & T13 & T16 & T2 & T1 & Tcs & Mra & Ms0 & Ms1 & KEEPT & GROWT).
  pose proof (ing_sp B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hsp.
  pose proof (ing_sp_ceil B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJc Hlo Hhi) as Hceil.
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatc & _).
  pose proof Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstatc as (_ & _ & Hceil0 & _ & _ & H470 & _).
  assert (Hslo : alloc_ceiling <= ly_stk_lo lyc) by (rewrite Elo; exact Hceil0).
  assert (Hshi : ly_stk_hi lyc <= 2 ^ 47) by (rewrite Ehi; exact H470).
  pose proof HREC as (Hal8 & _ & HD & HW & _ & Hidl & HMBc).
  destruct (ing_zones B LAWS STK sp0 FP ly S own lyc Sc W memc mdc (spZ regs) id idb p len pb
              HARc Hceil Hslo Hshi HREC HPAY ltac:(lia))
    as (Zi & Zp & Zip & Zi4 & Zi47 & Zp4 & Zpc & Zsp & _).
  assert (Hl4 : (4 <= length pb)%nat) by (rewrite Hpl; lia).
  (* a4 is the counter 4: the walk knows it, so the loop's exit test is decided in each round *)
  pose proof (st_ok_pi_pin_reg' _ _ _ (14%bv : bv 5) 4 HS0
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; exact H14) ltac:(vm_compute; reflexivity)) as HS.
  clear HS0.
  pose proof (EIF_reg regsT pb 2 2%bv eq_refl) as E2.
  pose proof (EIF_reg regsT pb 10 10%bv eq_refl) as E10. rewrite T10 in E10. unfold w64 in E10.
  pose proof (EIF_reg regsT pb 12 12%bv eq_refl) as E12. rewrite T12 in E12. unfold w64 in E12.
  pose proof (EIF_pay regsT pb) as EP.
  pose proof (EIF_agree regsT pb) as HAE.
  assert (HEI : img_env VAL A_LIM (EIF regsT pb)) by apply Eimg_env.
  assert (U10 : bv_unsigned (ew (EIF regsT pb) 10) = id) by (rewrite E10; apply unsigned_lit_small; lia).
  assert (U12 : bv_unsigned (ew (EIF regsT pb) 12) = p) by (rewrite E12; apply unsigned_lit_small; lia).
  remember (EIF regsT pb) as E eqn:HE. clear HE.
  assert (KEEPM : forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id) ->
                    aview SEGS (w_H W) memT a = aview SEGS (w_H W) memT a) by (intros; reflexivity).
  assert (GROW : forall a, apresent (w_H W) memT a -> apresent (w_H W) memT a) by (intros a Ha; exact Ha).
  assert (Q01 : 0 <= 0 < 1) by lia. assert (Q02 : 0 <= 0 < 2) by lia. assert (Q12 : 0 <= 1 < 2) by lia.
  (* 0x83944 .. the test of p[0] at 0x83964 *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [awr_ok_tac|]. if_keep U10.
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  { if_bad 0%nat EP pb idb Hl4 HA E2 HAE U10 HARc Hceil Hslo Hshi HREC KEEPT HS HJ SHOK KEEPM GROW. }
  if_dig EP pb D0 0%nat.
  (* round 2: p[1] *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [awr_ok_tac|]. if_keep U10.
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  { if_bad 1%nat EP pb idb Hl4 HA E2 HAE U10 HARc Hceil Hslo Hshi HREC KEEPT HS HJ SHOK KEEPM GROW. }
  if_dig EP pb D1 1%nat.
  (* round 3: p[2] *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [awr_ok_tac|]. if_keep U10.
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  { if_bad 2%nat EP pb idb Hl4 HA E2 HAE U10 HARc Hceil Hslo Hshi HREC KEEPT HS HJ SHOK KEEPM GROW. }
  if_dig EP pb D2 2%nat.
  (* round 4: p[3] *)
  paj_run_tok RUN HS HJ SHOK Bspan_ING; [awr_ok_tac|]. if_keep U10.
  psrr_branch_tok RUN BR HS SHOK Bspan_ING.
  { if_bad 3%nat EP pb idb Hl4 HA E2 HAE U10 HARc Hceil Hslo Hshi HREC KEEPT HS HJ SHOK KEEPM GROW. }
  if_dig EP pb D3 3%nat.
  apply Z.ltb_ge in D0, D1, D2, D3.
  assert (HING : RcIdentModel.ING idb 0 pb =
                 (1, RcIdentModel.upd (RcIdentModel.upd idb RcIdentModel.OFF_FW
                       (RcIdentModel.le16 (RcIdentModel.fw_value pb))) RcIdentModel.OFF_HAS_FW [RcIdentModel.zb 1])).
  { rewrite (RcIdentLib.ING_fw idb pb Hl4).
    rewrite (proj2 (Z.leb_le _ 9) D0), (proj2 (Z.leb_le _ 9) D1), (proj2 (Z.leb_le _ 9) D2), (proj2 (Z.leb_le _ 9) D3).
    reflexivity. }
  (* the stores: the record's region joins the state, writable on [id, id + 3) *)
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
    let HR := fresh "HSR" in
    assert (HR : st_ok_pi SEGS VAL Ex
                   (mkSS (ss_pc ssx) (ss_regs ssx) (rec_region 0 3 :: ss_mem ssx) (ss_resv ssx) (ss_facts ssx))
                   (restrict (w_H W) msx));
    [ apply (st_ok_pi_add_region Ex ssx (restrict (w_H W) msx) (rec_region 0 3) HSx);
      [ vm_compute; reflexivity
      | apply (rec_region_ok Ex _ id 0 3);
        [cbn [ew ewset Nat.eqb]; exact U10 | clear - Zi4; lia | clear - Zi47; lia |];
        intros o Ho; cbn [ms_mem restrict]; apply (apresent_writable SEGS); apply GROW; apply GROWT;
        exact (proj2 (HW (id + o) ltac:(clear - Ho; lia)))
      | apply all_disjoint_of_extents;
        let rs := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with rs;
        unfold extent_of_region, rec_region; cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zall_disjoint];
        unfold zdisj; cbn [fst snd ew ewset Nat.eqb]; rewrite U10, U12; split; [clear - Zip Hlen4; lia | exact I] ]
    | clear HSx; rename HR into HSx ]
  end.
  lazymatch goal with KM : forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id) -> aview ?sg ?H ?m1 a = aview ?sg ?H memT a |- _ =>
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (id <= a < id + 3) -> aview sg H m1 a = aview sg H memT a)
      by (intros a Ha Hw; apply KM; [exact Ha | let Hc := fresh "Hc" in intros Hc; clear - Hc; lia]);
    clear KM; rename K3 into KEEPM
  end.
  (* 0x83968 .. 0x83cb8: the end of round 4, the value to id, 1 to id + 2 *)
  paj_run_to_tok RUNTO HS HJ SHOK Bspan_ING 13744%Z; [if_awr U10 HW|]. if_keep U10.
  (* the record's region at 0x83cbc *)
  lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) |- _ =>
    pose proof (st_ok_mem_ok SEGS _ _ _ HSx) as (_ & HRok & _);
    lazymatch type of HRok with Forall _ ?rs =>
      let rs' := eval vm_compute in rs in change rs with rs' in HRok end;
    pose proof (Forall_inv HRok) as HR0;
    destruct HR0 as (_ & _ & _ & HCH);
    cbn [YP09.r_chunks YP09.r_base base_val ew ewset Nat.eqb] in HCH; rewrite U10 in HCH;
    pose proof (Forall_inv HCH) as C2; pose proof (Forall_inv (Forall_inv_tail HCH)) as C0;
    destruct (C2 0 ltac:(cbn; exact Q01)) as (b2 & Hb2 & M2);
    destruct (C0 0 ltac:(cbn; exact Q02)) as (b00 & Hb00 & M00);
    destruct (C0 1 ltac:(cbn; exact Q12)) as (b01 & Hb01 & M01);
    cbn [cbyte YP09.c_off YP09.c_val] in Hb2, Hb00, Hb01;
    injection Hb2 as <-; injection Hb00 as <-; injection Hb01 as <-;
    cbn [sv_denot] in M2;
    assert (HV : bv_unsigned (sv_denot Ex if_sum_sv) = RcIdentModel.fw_value pb)
      by (apply if_sum; cbn [ew ewset Nat.eqb];
          [ exact (EP 0%nat (proj1 (Nat.ltb_lt 0 17) eq_refl)) | exact (EP 1%nat (proj1 (Nat.ltb_lt 1 17) eq_refl))
          | exact (EP 2%nat (proj1 (Nat.ltb_lt 2 17) eq_refl)) | exact (EP 3%nat (proj1 (Nat.ltb_lt 3 17) eq_refl)) ])
  end.
  if_tail 1 HA E2 HAE HJ KEEPM GROW.
  - rewrite HING. reflexivity.
  - rewrite HING. cbn [snd].
    eapply (if_rec_bytes _ (mrestrict (w_H W) memc) id idb pb _ Hidl HMBc); [| exact M00 | exact M01 | exact M2 | exact HV].
    intros j Hj. apply (mbyte_of_aview SEGS (w_H W) (w_H W) memc).
    rewrite KEEPM; [| clear - Hj Zi4 Zi47; lia | clear - Hj; lia].
    apply KEEPT; [clear - Hj Zi4 Zi47; lia | clear - Hj Zsp; unfold INGEST_STK, ESTACK in Zsp; lia].
Qed.
End h.
End f.
End d.
