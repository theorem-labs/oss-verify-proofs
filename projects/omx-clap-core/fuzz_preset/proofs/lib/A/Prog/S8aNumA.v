(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, unstripped twin bff8519b), ex_value piece 5
   (ev_number), sub-piece A of S8aNumCut.v: ev_A (ev_A_stmt), EV_NUM (+0x2c4, 0x83568) -> CT (+0x9f4) | CL (+0x364).
   Code walked: +0x2c4 .. +0x360 (0x83568-0x83604, 40 instructions) and the slow arms of its two shadow checks,
   +0xbac (0x83e50-0x83e54) and +0xc6c (0x83f10-0x83f14), which the engine absorbs (YCbn.v slow_block).
   fuzz_preset.c @0b89c6c1bd :216-226 (ex_number up to the scan).
   Engine: YC80x / YC1fPx (paj_run_to_x, as YSRrMemnorm's twin paj_run_to_x_inv) over YCbqG's ajournal_x, at
   L := A_prog_listing with a generic PA : PAImg A_prog_listing and a generic PrhImg (ev_img_ok bounds ex_value's
   frame), the float state of the cut (fxc) as the engine's fx.
   Two engine runs: run 1 (+0x2c4 .. +0x2d4: the v spill and the two frame shadow bytes, with an empty token band,
   since the frame's shadow bytes lie in the shadow band) and run 2 (+0x2d4 onward, the shadow band
   [SHADOW_OFF, SHADOW_OFF + 2 ^ 44), the text bytes x[j0], x[j0 + 1] as a read-only region). The case split is
   up front on c = '-' (sg) and on the bytes left after j0 = i1 + sg (none, one, two or more): 15 leaves.
   The refusals use WalkS8a's model S8aModel.v (prhex_V_cons, prhex_V_num) and the byte tests S8aNumPure.v
   (asm_first_digit_digit, asm_next_digit_digit).
   Section hypotheses: LAWS (AR_laws_x), Hent (the instance's entry of ex_value, PAImg_prog.v A_entry_ex_value)
   and ev_mid_keep (lane M's ev_mid_keep_stmt of S8aNumCut.v, cited, supplied at the integration).
   MEMNORM (brief-mn lane a): YAkMemnorm.memnorm SEGS mem is ev_mid's last conjunct, a state fact. It comes from
   ev_at_kind's MID at EV_NUM, crosses every run by lib/Reusable/YSRrMemnorm.v's runner twin paj_run_to_x_inv at
   P := YAkMemnorm.memnorm SEGS (laws srr_inv_laws_memnorm_k; the same body as YAkMemnorm.memnorm, by conversion),
   driven by the tactic twin paj_run_to_tok_x_inv (the start memory's P goes in as HPM, the end memory's P comes back
   as HPM), and is the premise ev_mid_keep takes for the new memory; so CL's / CT's MID carries it. A branch
   (paj_branch) and the region edits (eva_drop, eva_addRT) keep the machine state, so HPM stays.
   rule 24: done for the piece (proof-index ex_value ex_number strtod checked_memcpy, index
   2026-10-28T04:13:31Z, R24CheckNum2 "NUM: CONFIRM"); no released file is Required, no released lemma cited.
   Numerals (brief rule 4): no ADDRESS. DERIVED: 7364 (ex_value's slot 1841 * 4, PAImg_prog.v A_entry_ex_value,
   the PRW_pj_write.v Hent form); 8088 = 7364 + 0x2d4, 8232 = 7364 + 0x364, 9912 = 7364 + 0x9f4; 16384 + 272
   (STK_RT_STRTOD plus ev_img_ok's frame bound); 0x7fff7f800000 / 0x7fffff800000 (the bounds of alloc_ceiling,
   YCbq.v asan_consts); 0x7fff8000 (SHADOW_OFF, YG0f.v); 2 ^ 44 (the shadow band); 16 = 128 / 8 (the frame's shadow
   bytes, fs_frame_bytes 1 = 128). LENGTH: the offsets 0x2c4, 0x2d4, 0x364, 0x9f4 into ex_value; 104, 112, 120, 128
   (the s1-relative spills); 4, 8, 9 (the frame's shadow bytes +4, +8); 32, 64 (frame slots of `end` / `num`);
   4096, 2 ^ 47, 2 ^ 47 - 64, 2 ^ 64 (the model's address bounds); 2 ^ 5 (s1's alignment); 0, 1, 2 (byte counts).
   WORD: 45 '-', 48 '0', 58, -10, -11, -45, -58, -1, 18446744073709551605 / ..606 / ..615 (= -11, -10, -1 mod
   2 ^ 64: the listing's immediates as the engine prints them), 288230376218820621 (a5, +0x350 .. +0x360:
   2 ^ 58 + 2 ^ 26 + 13), 255 / 256 (a byte); register and atom numbers (2 .. 33). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aModel S8aNumPure.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== pure: the number arm's refusals at its first bytes (fuzz_preset.c :221-226), from WalkS8a's model
   S8aModel.v (prhex_V_cons :106, prhex_V_num :342) and the byte tests of S8aNumPure.v ======== *)

Lemma eva_skipn_nth : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
induction x as [|y x IH]; intros [|i] Hi; cbn [length] in Hi; try lia; [reflexivity|].
cbn [skipn nth]. apply IH. lia.
Qed.

(* the dispatch facts ev_at_kind / KN give the number arm's first byte *)
Definition eva_disp (c : Z) : Prop :=
  PjGrammar.ws c = false /\ c <> 123 /\ c <> 91 /\ c <> 34 /\ c <> 116 /\ c <> 102 /\ c <> 110.

(* ev_N at such a byte is the grammar's reading prhex_V there, in S8aModel's prhex_V_num form *)
Lemma eva_N_num : forall c y, eva_disp c ->
  ev_N (c :: y) =
    let j := if c =? 45 then 1%nat else 0%nat in
    match skipn j (c :: y) with
    | [] => None
    | c0 :: z =>
      if negb (PjGrammar.digit c0) then None
      else if (c0 =? 48) && match z with c1 :: _ => PjGrammar.digit c1 | [] => false end then None
      else let (a, r) := PjGrammar.span PjGrammar.numch z in
           let txt := firstn j (c :: y) ++ c0 :: a in
           if PjGrammar.whole ReaderRes.jr_strtod txt
           then Some (PjTree.JNum txt (snd (ReaderRes.jr_strtod txt)), r) else None
    end.
Proof.
intros c y (Hw & H1 & H2 & H3 & H4 & H5 & H6).
rewrite <- (S8aModel.prhex_V_num 0 c y Hw H1 H2 H3 H4 H5 H6).
rewrite (S8aModel.prhex_V_cons 0 c y Hw).
rewrite (proj2 (Z.eqb_neq c 123) H1), (proj2 (Z.eqb_neq c 91) H2), (proj2 (Z.eqb_neq c 34) H3),
  (proj2 (Z.eqb_neq c 116) H4), (proj2 (Z.eqb_neq c 102) H5), (proj2 (Z.eqb_neq c 110) H6).
reflexivity.
Qed.

(* the three refusals before the scan: no byte after the sign, a non-digit, a leading zero before a digit *)
Lemma eva_N_refuse : forall x i1 c, (i1 < length x)%nat -> nth i1 x 0 = c -> eva_disp c ->
  ((length x <= i1 + ev_sg c)%nat \/
   ((i1 + ev_sg c < length x)%nat /\ PjGrammar.digit (nth (i1 + ev_sg c) x 0) = false) \/
   ((S (i1 + ev_sg c) < length x)%nat /\ nth (i1 + ev_sg c) x 0 = 48 /\
    PjGrammar.digit (nth (S (i1 + ev_sg c)) x 0) = true)) ->
  ev_N (skipn i1 x) = None.
Proof.
intros x i1 c Hi Hc Hd Hr. rewrite (eva_skipn_nth x i1 Hi), Hc, (eva_N_num c _ Hd). cbv zeta.
unfold ev_sg in Hr. revert Hr. destruct (c =? 45) eqn:E; intros Hr; cbn [skipn].
- replace (i1 + 1)%nat with (S i1) in Hr by lia.
  destruct Hr as [Hl | [[Hl Hd0] | (Hl & H0 & Hd1)]].
  + rewrite (skipn_all2 x) by lia. cbn [skipn]. reflexivity.
  + rewrite (eva_skipn_nth x (S i1) Hl). cbn [skipn]. cbv beta iota. rewrite Hd0. reflexivity.
  + rewrite (eva_skipn_nth x (S i1) ltac:(lia)), (eva_skipn_nth x (S (S i1)) Hl). cbn [skipn]. cbv beta iota.
    rewrite H0, Hd1. reflexivity.
- rewrite Nat.add_0_r in Hr. rewrite Hc in Hr.
  destruct Hr as [Hl | [[Hl Hd0] | (Hl & H0 & Hd1)]]; [lia | |].
  + cbn [skipn]. cbv beta iota. rewrite Hd0. reflexivity.
  + subst c. rewrite (eva_skipn_nth x (S i1) Hl). cbn [skipn]. cbv beta iota. rewrite H0, Hd1. reflexivity.
Qed.

(* ======== arithmetic: the listing's byte tests as the engine states them, S8aNumPure's classifiers ======== *)

(* +0x2fc `addi a4, a0, -58; li a5, -10; bltu a4, a5`: taken iff the byte is not a digit *)
Lemma eva_digit_lt : forall b, 0 <= b < 256 ->
  (zcanon (b + -58) <? zcanon 18446744073709551606) = negb (PjGrammar.digit b).
Proof.
intros b Hb. rewrite <- (S8aNumPure.asm_first_digit_digit b Hb).
unfold S8aNumPure.asm_first_digit, S8aNumPure.ult, S8aNumPure.M64, zcanon, M64. rewrite negb_involutive.
replace (18446744073709551606 mod 2 ^ 64) with (-10 mod 2 ^ 64) by reflexivity. reflexivity.
Qed.

(* +0x32c `addi a0, a0, -58; li a4, -11; bltu a4, a0`: taken iff the byte is a digit *)
Lemma eva_digit_gt : forall b, 0 <= b < 256 ->
  (zcanon 18446744073709551605 <? zcanon (b + -58)) = PjGrammar.digit b.
Proof.
intros b Hb. rewrite <- (S8aNumPure.asm_next_digit_digit b Hb).
unfold S8aNumPure.asm_next_digit, S8aNumPure.ult, S8aNumPure.M64, zcanon, M64.
replace (18446744073709551605 mod 2 ^ 64) with (-11 mod 2 ^ 64) by reflexivity. reflexivity.
Qed.

Lemma eva_w64_m1 : Z_to_bv 64 18446744073709551615 = w64 (-1).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.
Lemma eva_w64_m11 : Z_to_bv 64 18446744073709551605 = w64 (-11).
Proof. apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

Lemma eva_val_mem_wrap : forall segs m p v, val_mem segs m p 8 (v mod 2 ^ 64) -> val_mem segs m p 8 v.
Proof.
intros segs m p v H k Hk. rewrite (H k Hk). f_equal. f_equal. cbv [YG0f.le_byte YO0f.le_byte].
replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) by reflexivity. rewrite Zmod_mod. reflexivity.
Qed.

Lemma eva_nth_byte : forall segs m p (x : list Z) j, YI00.garr8 segs m p x -> 0 <= nth j x 0 < 256.
Proof.
intros segs m p x j H. destruct (Nat.lt_ge_cases j (length x)) as [Hj|Hj].
- exact (proj2 (H j Hj)).
- rewrite nth_overflow by exact Hj. lia.
Qed.

(* the in_wrange of a concrete region list, one region at a time *)
Lemma eva_inw_cons : forall E r rs z, in_wrange E (r :: rs) z ->
  (base_val E (r_base r) + r_wlo r <= z < base_val E (r_base r) + r_whi r) \/ in_wrange E rs z.
Proof. intros E r rs z (r' & [<-|Hin] & Hr); [left; exact Hr | right; exists r'; auto]. Qed.
Lemma eva_inw_nil : forall E z, ~ in_wrange E [] z.
Proof. intros E z (r & Hin & _). destruct Hin. Qed.

Lemma eva_agree_ewset : forall k E E' n v, (k <= n)%nat -> YP06.env_agree k E E' -> YP06.env_agree k E (ewset E' n v).
Proof.
intros k E E' n v Hk [H1 H2]. split.
- intros i Hi. cbn [ew ewset]. destruct (Nat.eqb_spec i n); [lia|]. apply H1. exact Hi.
- cbn [ed ewset]. exact H2.
Qed.

(* the memory frame of a run: outside its write windows the view is unchanged *)
Lemma eva_frame_view : forall segs E rs H mem mem' (Z0 : Z -> Prop),
  frame_of E rs (mrestrict H mem) (mrestrict H mem') ->
  (forall z, 0 <= z < 2 ^ 64 -> in_wrange E rs z -> Z0 z) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ Z0 z -> aview segs H mem' z = aview segs H mem z.
Proof.
intros segs E rs H mem mem' Z0 HF Hw z Hz HZ. unfold aview, YP09.mbyte.
rewrite (HF (Z_to_bv 64 z)); [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
intros Hin. exact (HZ (Hw z Hz Hin)).
Qed.

(* ======== the symbolic states ======== *)

(* ex_value's entry as a byte offset from the listing's base (DERIVED: slot 1841 * 4) *)
Definition EVA_K (off : Z) : Z := 7364 + off.
Definition EVA_Bx : sv := SOff 24 0.
Definition EVA_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* run 1 checks no shadow byte; its band is empty so the frame's shadow bytes may be written *)
Definition EVA_Bspan0 : Z * Z := (0, 0).
Definition EVA_CEIL : Z := 0x7fff7f800000.
(* s1 + 104 .. s1 + 120: the spills of v (+0x2c4) and &num (+0x340) *)
Definition eva_R1 : YP09.region := YP09.mkRegion (Some 9%nat) 104 120 104 120 [].
(* the frame's shadow bytes +4 and +8 (+0x2cc, +0x2d0) *)
Definition eva_R4 : YP09.region := YP09.mkRegion (Some 25%nat) 4 5 4 5 [].
Definition eva_R8 : YP09.region := YP09.mkRegion (Some 25%nat) 8 9 8 9 [].
(* the text bytes x[j0] (atom 32) and x[j0 + 1] (atom 33), read-only, at a1 = x0 + i1 plus sg *)
Definition eva_RT (sg n : Z) : YP09.region :=
  YP09.mkRegion (Some 11%nat) sg (sg + n) 0 0
    (if n =? 1 then [YP09.mkChunk sg (CVal 1 (SOff 32 0))]
     else [YP09.mkChunk sg (CVal 1 (SOff 32 0)); YP09.mkChunk (sg + 1) (CVal 1 (SOff 33 0))]).
Definition eva_atoms : list (nat * afact) :=
  [(9%nat, mkAF EVA_CEIL (2 ^ 47) 5); (11%nat, mkAF 4096 (2 ^ 47 - 64) 0); (12%nat, mkAF 4096 (2 ^ 47 - 64) 0);
   (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (25%nat, mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0);
   (32%nat, mkAF 0 255 0); (33%nat, mkAF 0 255 0)].
(* a1 + (s5 = '-'), as +0x2d0 .. +0x2e0 compute it; aliased to x0 + i1 + sg *)
Definition eva_sgv : sv := SAlu ALU_ADD (SOff 11 0) (SAlu ALU_SLTU (SOff 21 (-45)) (SLit 1)).
Definition eva_ss1 (sg : Z) (cs : list acond) : sstate :=
  mkSS (EVA_K EV_NUM) sr_atoms [eva_R1; eva_R4; eva_R8] None (mkFacts eva_atoms cs [(eva_sgv, SOff 11 sg)]).
(* the length conditions: x0 + i1 + o < x0 + len, or >= *)
Definition eva_cLT (o : Z) : acond := mkAC BC_LTU (SOff 11 o) (SOff 12 0).
Definition eva_cGE (o : Z) : acond := mkAC BC_GEU (SOff 11 o) (SOff 12 0).

(* the text byte x[j] as a one-byte chunk of atom n *)
Lemma eva_byte_chunk : forall segs E m base off n j (x : list Z) x0,
  YI00.garr8 segs m x0 x -> (j < length x)%nat -> base + off = x0 + Z.of_nat j ->
  bv_unsigned (ew E n) = nth j x 0 -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros segs E m base off n j x x0 Hg Hj Hb Hn i Hi. cbn [YP09.c_len YP09.c_val cv_len YP09.c_off] in *.
assert (i = 0) by lia. subst i. exists (Z_to_bv 8 (nth j x 0)). split.
- cbn [cbyte]. f_equal. unfold byte_of_word. cbn [sv_denot]. rewrite Hn, Z.add_0_r.
  pose proof (proj2 (Hg j Hj)) as Hr. rewrite unsigned_lit_small by lia. rewrite Z.shiftr_0_r. reflexivity.
- rewrite Z.add_0_r, Hb. exact (YI00.garr8_mbyte _ _ _ _ _ Hg Hj).
Qed.

(* the S1 + off slot of a run's state: an 8-byte chunk of region (Some 9) *)
Lemma eva_chunk8 {fx : YK11.FPState} : forall segs val E ss ms r off e,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 8 e)) (r_chunks r) ->
  forall v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem segs (ms_mem ms) (base_val E (r_base r) + off) 8 v.
Proof.
intros segs val E ss ms r off e HS Hr Hc v He Hv.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
exact (val_of_chunk_ok segs E _ _ off 8 e v (proj1 (Forall_forall _ _) Hcs _ Hc) He ltac:(exact Hv) ltac:(lia)).
Qed.

(* a one-byte zero chunk of a run's state (the frame shadow bytes +0x2cc / +0x2d0 store) *)
Lemma eva_chunk1z {fx : YK11.FPState} : forall segs val E ss ms r off,
  st_ok_pi segs val E ss ms -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal 1 (SLit 0))) (r_chunks r) ->
  YP09.mbyte segs (ms_mem ms) (base_val E (r_base r) + off) = Some (Z_to_bv 8 0).
Proof.
intros segs val E ss ms r off HS Hr Hc.
pose proof (st_ok_mem_ok segs E _ ms HS) as (_ & Hrs & _). cbn [abs_ss setpc ss_mem] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
destruct (proj1 (Forall_forall _ _) Hcs _ Hc 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2).
cbn [YP09.c_off] in Hb2. rewrite Z.add_0_r in Hb2. rewrite Hb2. cbn [cbyte YP09.c_val] in Hb1.
injection Hb1 as <-. reflexivity.
Qed.

(* dropping regions of a run's state (YP06.v st_ok_submem at the position-abstract form) *)
Lemma eva_submem {fx : YK11.FPState} : forall segs val E ss ms rs,
  st_ok_pi segs val E ss ms -> submem rs (ss_mem ss) -> regions_wf rs = true ->
  st_ok_pi segs val E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros segs val E ss ms rs HS Hsub Hwf. unfold st_ok_pi, abs_ss in *.
exact (st_ok_submem segs E (setpc ss (val A_TEXT + ss_pc ss)) ms rs HS Hsub Hwf).
Qed.

Lemma eva_sltu45 : forall c, 0 <= c < 256 -> (zcanon (c + -45) <? zcanon 1) = (c =? 45).
Proof.
intros c Hc. unfold zcanon, M64. rewrite (Z.mod_small 1) by lia.
destruct (Z.lt_ge_cases c 45) as [H|H].
- rewrite <- (Z.mod_unique (c + -45) (2 ^ 64) (-1) (c - 45 + 2 ^ 64)) by lia.
  destruct (Z.ltb_spec (c - 45 + 2 ^ 64) 1); destruct (Z.eqb_spec c 45); first [reflexivity | lia].
- rewrite (Z.mod_small (c + -45)) by lia.
  destruct (Z.ltb_spec (c + -45) 1); destruct (Z.eqb_spec c 45); first [reflexivity | lia].
Qed.

Lemma eva_eq48 : forall b, 0 <= b < 256 -> (zcanon (b + 0) =? zcanon 48) = (b =? 48).
Proof. intros b Hb. rewrite Z.add_0_r, !zcanon_id by (unfold M64; lia). reflexivity. Qed.

Lemma eva_u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.

Lemma eva_zmaxl_strtod : forall l1 l2, STK_RT_STRTOD <= zmaxl (l1 ++ STK_RT_STRTOD :: l2).
Proof.
intros l1 l2. unfold zmaxl. induction l1 as [|y l1 IH]; cbn [app fold_right]; lia.
Qed.

Section core.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the image fact of the instance (PAImg_prog.v A_entry_ex_value at PI_prog_A): ex_value is slot 1841 *)
Hypothesis Hent : pa_sigma AS_ex_value = BASE + 7364.
Hypothesis IMG : ev_img_ok.
Let RUNTO := @paj_run_to_x_inv fx rc SK A_prog_listing PL_prog_A PA B (@prh_pst PI) ARx _ LAWS
  (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS).
Let BR := paj_branch (PI := PA).

Lemma eva_cfg : forall off regs mem md,
  mkCfg (mkst regs (Z_to_bv 64 (BASE + EVA_K off)) mem (seg_rom SEGS)) md = ev_cfg fx regs off mem md.
Proof. intros off regs mem md. unfold ev_cfg, ev_pc. rewrite Hent. unfold EVA_K. do 3 f_equal. lia. Qed.
Lemma eva_cfg_CT : forall regs mem md,
  mkCfg (mkst regs (Z_to_bv 64 (BASE + 9912)) mem (seg_rom SEGS)) md = ev_cfg fx regs 0x9f4 mem md.
Proof. intros. rewrite <- eva_cfg. reflexivity. Qed.
Lemma eva_cfg_CL : forall regs mem md,
  mkCfg (mkst regs (Z_to_bv 64 (BASE + 8232)) mem (seg_rom SEGS)) md = ev_cfg fx regs 0x364 mem md.
Proof. intros. rewrite <- eva_cfg. reflexivity. Qed.

Lemma eva_STK : forall a, 16384 + 272 <= ea_STK a.
Proof.
intros a. unfold ea_STK, STK_ex_value. unfold ev_img_ok in IMG.
pose proof (eva_zmaxl_strtod [STK_RT_ECALL; STK_RT_STR] [STK_ex_string; STK_ex_word; STK_ex_ws]) as H.
cbn [app] in H. unfold STK_RT_STRTOD, ESTACK in H |- *. nia.
Qed.

Variable a : ev_act.
Local Notation MID := (ev_mid B ARx SK a).
Local Notation AJ ly S Hp W mem md k := (ajournal_x (SK := SK) SEGS B prh_pst ARx (ea_STK a + ea_d a)
  (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)]
  ly S Hp W mem md k).
(* lane M's ev_mid_keep_stmt, ev_pre applied; the new memory's memnorm is its premise *)
Hypothesis KEEP : forall ly S Hp W mem md k p dep dl mem' md' k',
  MID ly S Hp W mem md k p dep dl -> AJ ly S Hp W mem' md' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz B a z -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  YAkMemnorm.memnorm SEGS mem' ->
  MID ly S Hp W mem' md' k' p dep dl.
(* from ev_pre: the allocator at the activation's entry, the caller window, the differs flag *)
Hypothesis HAR0 : ARx (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a).
Hypothesis Hd0 : 0 <= ea_d a.
Hypothesis Hdl : ea_dl a = 0 \/ ea_dl a = 1.

Lemma eva_mid_aj : forall ly S Hp W mem md k p dep dl, MID ly S Hp W mem md k p dep dl -> AJ ly S Hp W mem md k.
Proof. intros ly S Hp W mem md k p dep dl H. exact (proj1 H). Qed.
Lemma eva_mid_src : forall ly S Hp W mem md k p dep dl, MID ly S Hp W mem md k p dep dl ->
  src_rd W mem (ea_x0 a) (ea_x a).
Proof. intros ly S Hp W mem md k p dep dl (_ & _ & _ & _ & _ & _ & H & _). exact H. Qed.
(* ev_mid's last conjunct, as the runner twin's P *)
Lemma eva_mid_mn : forall ly S Hp W mem md k p dep dl, MID ly S Hp W mem md k p dep dl ->
  YAkMemnorm.memnorm SEGS mem.
Proof. intros ly S Hp W mem md k p dep dl (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H). exact H. Qed.

Section ctx.
Variables (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (ly : alayout) (Sa : astate) (Hp : list Z) (k : Z) (i1 : nat) (c : Z).
Hypothesis HK : ev_at_kind B ARx SK a W regs mem md ly Sa Hp k i1 c.
Hypothesis HD : eva_disp c.
Local Notation x := (ea_x a).
Local Notation x0 := (ea_x0 a).
Local Notation len := (ea_len a).
Local Notation S1 := (ea_S1 a).
Local Notation fr := (ea_fr a).

(* the arithmetic facts of the cut *)
Lemma eva_cut_facts :
  ea_sp0 a - ea_STK a <= S1 + 104 /\ S1 + 128 <= ea_sp0 a /\ EVA_CEIL <= S1 /\ S1 + 128 <= 2 ^ 47 /\
  S1 mod 32 = 0 /\ 4096 <= x0 /\ x0 + len <= alloc_ceiling /\ alloc_ceiling <= S1 /\
  alloc_ceiling <= 0x7fffff800000 /\ frame_addr ly 1 (ea_pos a) = fr /\ 4096 <= fr /\ fr + 128 <= alloc_ceiling /\
  fs_frame_bytes 1 = 128 /\
  (forall z, ea_sp0 a - ea_STK a <= z < ea_sp0 a + ea_d a -> apresent (w_H W) mem z) /\
  (forall i, 0 <= i < 16 -> apresent (w_H W) mem (shadow_addr fr + i)) /\
  In (1, ea_pos a) (frames Sa).
Proof.
destruct HK as (HM & _).
pose proof (eva_mid_aj _ _ _ _ _ _ _ _ _ _ HM) as
  (HAR & Hlay & _ & _ & _ & Hfrm & _ & _ & _ & _ & _ & _ & _ & Hstk & Hastk & _ & _).
pose proof (eva_mid_src _ _ _ _ _ _ _ _ _ _ HM) as (_ & Hx0 & Hxe & _).
pose proof (eva_STK a) as HSTK.
pose proof asan_consts as (C1 & _).
destruct Hastk as (_ & _ & Hlo & Hlo2 & Hhi & Hhi2 & _).
assert (Hin : In (1, ea_pos a) (frames Sa)) by (rewrite Hfrm; left; reflexivity).
destruct (alx_layout _ _ _ LAWS _ _ _ _ _ _ _ HAR0 Hlay) as (_ & Hfa & _).
assert (Hfr : frame_addr ly 1 (ea_pos a) = fr) by (unfold ea_fr; apply Hfa).
destruct (alx_frames _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & Hsh).
destruct (alx_sep _ _ _ LAWS _ _ _ _ _ _ HAR) as (_ & Hsep).
pose proof (proj1 (Forall_forall _ _) Hsep _ Hin) as Hsep1. cbn [fst snd] in Hsep1.
assert (Hfs : fs_frame_bytes 1 = 128) by reflexivity.
rewrite Hfr, Hfs in Hsep1. rewrite Hfr, Hfs in Hsh.
pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)) as Hm.
assert (Hmm : (ea_SA a - ea_SA a mod 32) mod 32 = 0).
{ rewrite Zminus_mod, Zmod_mod, Z.sub_diag. reflexivity. }
unfold ea_S1, ea_len. unfold ea_SA in Hm, Hmm |- *. unfold EVA_CEIL.
repeat match goal with |- _ /\ _ => split end.
all: first [ lia | exact Hin | (intros z Hz; apply Hstk; lia)
  | (intros i Hi; exact (proj1 (Hsh i ltac:(change (128 / 8) with 16; lia)))) ].
Qed.

(* the registers the piece leaves as they were at the cut *)
Definition eva_kept : list Prelude.reg := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 18%bv; 19%bv; 24%bv; 25%bv; 26%bv].

Lemma eva_base : forall regs' mem',
  (forall r, In r eva_kept -> getr regs' r = getr regs r) -> getr regs' 23 = getr regs 22 ->
  val_mem SEGS (mrestrict (w_H W) mem') (S1 + 104) 8 (bv_unsigned (getr regs 23)) ->
  ev_base a W regs' mem' i1 c.
Proof.
intros regs' mem' Hkp H23 Hv.
destruct HK as (_ & Hregs & _ & _ & H22 & H23' & _ & _ & _ & Hi1 & Hc & Hws & Hskip).
destruct HD as (_ & D1 & D2 & D3 & D4 & D5 & D6).
pose proof (Hkp 2%bv ltac:(cbn; tauto)) as K2. pose proof (Hkp 3%bv ltac:(cbn; tauto)) as K3.
pose proof (Hkp 4%bv ltac:(cbn; tauto)) as K4. pose proof (Hkp 8%bv ltac:(cbn; tauto)) as K8.
pose proof (Hkp 9%bv ltac:(cbn; tauto)) as K9. pose proof (Hkp 18%bv ltac:(cbn; tauto)) as K18.
pose proof (Hkp 19%bv ltac:(cbn; tauto)) as K19. pose proof (Hkp 24%bv ltac:(cbn; tauto)) as K24.
pose proof (Hkp 25%bv ltac:(cbn; tauto)) as K25. pose proof (Hkp 26%bv ltac:(cbn; tauto)) as K26.
destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
unfold ev_base, ev_regs.
rewrite K2, K3, K4, K8, K9, K18, K19, K24, K25, K26, H23, H22.
repeat match goal with |- _ /\ _ => split end; try reflexivity; try assumption.
rewrite H23' in Hv. unfold w64 in Hv. rewrite Z_to_bv_unsigned in Hv. apply eva_val_mem_wrap. exact Hv.
Qed.

Lemma eva_CT : forall regs' mem' md',
  ev_mid B ARx SK a ly Sa Hp W mem' md' k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) ->
  (forall r, In r eva_kept -> getr regs' r = getr regs r) -> getr regs' 23 = getr regs 22 ->
  getr regs' 21 = w64 (-1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (S1 + 104) 8 (bv_unsigned (getr regs 23)) ->
  ev_N (skipn i1 x) = None ->
  ev_CT B ARx SK a W regs' mem' md' ly Sa Hp k i1 c.
Proof.
intros regs' mem' md' HM Hkp H23 H21 Hv HN. unfold ev_CT. split; [exact (eva_base regs' mem' Hkp H23 Hv)|].
exists (-1), (Z.of_nat i1), (ea_dl a). rewrite HN.
split; [exact H21|]. split; [exact HM|]. split; [exact Hdl|]. auto.
Qed.

Lemma eva_CL : forall regs' mem' md',
  ev_mid B ARx SK a ly Sa Hp W mem' md' k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) ->
  (forall r, In r eva_kept -> getr regs' r = getr regs r) -> getr regs' 23 = getr regs 22 ->
  getr regs' 21 = w64 (-1) ->
  val_mem SEGS (mrestrict (w_H W) mem') (S1 + 104) 8 (bv_unsigned (getr regs 23)) ->
  getr regs' 27 = w64 (fr + 32) -> val_mem SEGS (mrestrict (w_H W) mem') (S1 + 112) 8 (fr + 64) ->
  getr regs' 22 = w64 (x0 + Z.of_nat (i1 + ev_sg c)) -> getr regs' 10 = w64 (x0 + Z.of_nat (i1 + ev_sg c)) ->
  getr regs' 13 = w64 (-11) -> getr regs' 14 = w64 58 -> getr regs' 15 = w64 288230376218820621 ->
  ev_fsh a W mem' -> ev_lead_ok x (i1 + ev_sg c) ->
  ev_CL B ARx SK a W regs' mem' md' ly Sa Hp k i1 c (i1 + ev_sg c).
Proof.
intros regs' mem' md' HM Hkp H23 H21 Hv H27 Hv112 R22 R10 R13 R14 R15 Hfsh Hlead.
pose proof (eva_base regs' mem' Hkp H23 Hv) as Hb.
destruct HK as (_ & _ & _ & _ & _ & _ & _ & H11 & H12 & _).
pose proof (Hkp 11%bv ltac:(cbn; tauto)) as K11. pose proof (Hkp 12%bv ltac:(cbn; tauto)) as K12.
unfold ev_CL. split; [exact HM|]. split; [exact Hb|].
split; [unfold ev_scanregs; rewrite K11, K12; repeat match goal with |- _ /\ _ => split end; assumption|].
split; [unfold ev_span; split; [exact Hlead | unfold ev_sub; rewrite Nat.sub_diag; constructor]|].
destruct Hlead as (Hl & _).
split; [lia|]. repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Lemma eva_shf : 0x7fff8000 <= shadow_addr fr <= 0x7fff8000 + 2 ^ 44.
Proof.
pose proof eva_cut_facts as (_ & _ & _ & _ & _ & _ & _ & _ & F9 & _ & F11 & F12 & _).
unfold shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia|].
pose proof (Z.div_le_upper_bound fr 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
Qed.

(* the frame's shadow bytes +4 and +8 read 0 once +0x2cc / +0x2d0 stored them, and stay so outside s1's spills *)
Lemma eva_fsh_of : forall mem',
  YP09.mbyte SEGS (mrestrict (w_H W) mem') (shadow_addr fr + 4) = Some (Z_to_bv 8 0) ->
  YP09.mbyte SEGS (mrestrict (w_H W) mem') (shadow_addr fr + 8) = Some (Z_to_bv 8 0) -> ev_fsh a W mem'.
Proof. intros mem' H4 H8. unfold ev_fsh, aview. rewrite H4, H8. split; reflexivity. Qed.

Lemma eva_fsh_keep : forall mem1 mem2,
  (forall z, 0 <= z < 2 ^ 64 -> ~ (S1 + 104 <= z < S1 + 120) -> aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem1 z) ->
  ev_fsh a W mem1 -> ev_fsh a W mem2.
Proof.
intros mem1 mem2 Hv [H4 H8]. pose proof eva_shf as Hs.
pose proof eva_cut_facts as (_ & _ & F3 & F4 & _ & _ & _ & F8 & _). unfold EVA_CEIL in F3.
unfold ev_fsh. rewrite !Hv by lia. split; assumption.
Qed.

(* the shadow check of a text byte at a1 + o (+0x2e4, +0x318): the text is addressable at the run's memory *)
Lemma eva_obl : forall E M mdM kM o,
  ev_mid B ARx SK a ly Sa Hp W M mdM kM (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) ->
  bv_unsigned (ew E 24) = SHADOW_OFF -> bv_unsigned (ew E 11) = x0 + Z.of_nat i1 -> 0 <= o ->
  Z.of_nat i1 + o + 1 <= len ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) M)) (U E (SOff 24 0)) (U E (SOff 11 o)) 1.
Proof.
intros E M mdM kM o HM H24 H11 Ho Hl.
pose proof (eva_mid_src _ _ _ _ _ _ _ _ _ _ HM) as (_ & Hx0 & Hxe & _ & Hra & _).
unfold ea_len in Hl.
apply (obl_of_range SEGS (w_H W) M E (SOff 24 0) (U E (SOff 11 o)) 1 x0 (Z.of_nat (length x)) Hra).
- rewrite U_SOff, H24, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
- rewrite U_SOff, H11, zcanon_id by (unfold M64; pose proof asan_consts as (C1 & _); lia). lia.
- rewrite U_SOff, H11, zcanon_id by (unfold M64; pose proof asan_consts as (C1 & _); lia). lia.
Qed.

(* the text region x[j0 ..] at a1 + sg, at the memory of run 2's start *)
Lemma eva_RT_ok : forall E M mdM kM sg n b0 b1,
  ev_mid B ARx SK a ly Sa Hp W M mdM kM (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) ->
  bv_unsigned (ew E 11) = x0 + Z.of_nat i1 -> sg = Z.of_nat (ev_sg c) ->
  b0 = nth (i1 + ev_sg c)%nat x 0 -> b1 = nth (S (i1 + ev_sg c)) x 0 ->
  bv_unsigned (ew E 32) = b0 -> bv_unsigned (ew E 33) = b1 ->
  (n = 1 \/ n = 2) -> Z.of_nat i1 + sg + n <= len ->
  region_ok SEGS E (mrestrict (w_H W) M) (eva_RT sg n).
Proof.
intros E M mdM kM sg n b0 b1 HM H11 Hsg Hb0 Hb1 H32 H33 Hn Hl.
pose proof (eva_mid_src _ _ _ _ _ _ _ _ _ _ HM) as (Hg & Hx0 & Hxe & _).
unfold ea_len in Hl. unfold bytes_at in Hg. pose proof asan_consts as (C1 & _).
unfold region_ok, eva_RT. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite H11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
destruct Hn as [-> | ->]; cbn [Z.eqb].
- constructor; [|constructor].
  apply (eva_byte_chunk SEGS E _ _ sg 32 (i1 + ev_sg c)%nat x x0 Hg); [lia | rewrite Nat2Z.inj_add; lia | congruence].
- constructor; [|constructor; [|constructor]].
  + apply (eva_byte_chunk SEGS E _ _ sg 32 (i1 + ev_sg c)%nat x x0 Hg); [lia | rewrite Nat2Z.inj_add; lia | congruence].
  + apply (eva_byte_chunk SEGS E _ _ (sg + 1) 33 (S (i1 + ev_sg c)) x x0 Hg);
      [apply Nat2Z.inj_lt; rewrite Nat2Z.inj_succ, Nat2Z.inj_add; lia
      | rewrite Nat2Z.inj_succ, Nat2Z.inj_add; lia | congruence].
Qed.

Lemma eva_RT_disj : forall E r1 sg n, r_base r1 = Some 9%nat -> r_lo r1 = 104 ->
  bv_unsigned (ew E 9) = S1 -> bv_unsigned (ew E 11) = x0 + Z.of_nat i1 -> 0 <= sg -> 0 <= n ->
  Z.of_nat i1 + sg + n <= len -> all_disjoint E (eva_RT sg n) [r1].
Proof.
intros E r1 sg n Hb Hlo H9 H11 Hsg Hn Hl. pose proof eva_cut_facts as (_ & _ & _ & _ & _ & _ & F7 & F8 & _).
cbn [all_disjoint]. split; [|exact I]. unfold extent_disjoint, eva_RT.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hb, Hlo. cbn [base_val]. rewrite H9, H11. left. lia.
Qed.

Section env.
Variables (b0 b1 : Z) (E0 : env).
Hypothesis Hb0 : b0 = nth (i1 + ev_sg c)%nat x 0.
Hypothesis Hb1 : b1 = nth (S (i1 + ev_sg c)) x 0.
Hypothesis HB0 : 0 <= b0 < 256.
Hypothesis HB1 : 0 <= b1 < 256.
Hypothesis HEI : img_env VAL A_LIM E0.
Hypothesis HAG0 : YP06.env_agree 32 (Ereg regs []) E0.
Hypothesis HRE : regs_ok E0 sr_atoms regs.
Hypothesis HA : forall r : Prelude.reg, ew E0 (Z.to_nat (bv_unsigned r)) = getr regs r.
Hypothesis U9 : bv_unsigned (ew E0 9) = S1.
Hypothesis U11 : bv_unsigned (ew E0 11) = x0 + Z.of_nat i1.
Hypothesis U12 : bv_unsigned (ew E0 12) = x0 + len.
Hypothesis U18 : bv_unsigned (ew E0 18) = fr.
Hypothesis U21 : bv_unsigned (ew E0 21) = c.
Hypothesis U24 : bv_unsigned (ew E0 24) = SHADOW_OFF.
Hypothesis U25 : bv_unsigned (ew E0 25) = shadow_addr fr.
Hypothesis U32 : bv_unsigned (ew E0 32) = b0.
Hypothesis U33 : bv_unsigned (ew E0 33) = b1.

Lemma eva_cLT_ok : forall o, 0 <= o <= 2 -> Z.of_nat i1 + o < len -> acond_ok E0 (eva_cLT o).
Proof.
intros o Ho Hl. pose proof eva_cut_facts as (_ & _ & _ & _ & _ & F6 & F7 & F8 & F9 & _).
unfold acond_ok, eva_cLT. cbn [ac_c ac_a ac_b]. rewrite branch_ltu_U, !U_SOff, U11, U12.
unfold ea_len in *. clear Hb0 Hb1.
rewrite !zcanon_id by (unfold M64; lia). apply Z.ltb_lt. lia.
Qed.
Lemma eva_cGE_ok : forall o, 0 <= o <= 2 -> len <= Z.of_nat i1 + o -> acond_ok E0 (eva_cGE o).
Proof.
intros o Ho Hl. pose proof eva_cut_facts as (_ & _ & _ & _ & _ & F6 & F7 & F8 & F9 & _).
unfold acond_ok, eva_cGE. cbn [ac_c ac_a ac_b]. rewrite branch_geu_U, !U_SOff, U11, U12.
unfold ea_len in *. clear Hb0 Hb1. pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hi1 & _).
rewrite !zcanon_id by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge. lia.
Qed.

Lemma eva_zadd : forall p s, 0 <= p -> p + s < 2 ^ 64 -> 0 <= s <= 1 -> zcanon (zcanon (p + 0) + zcanon s) = zcanon (p + s).
Proof.
intros p s Hp0 Hps Hs. unfold zcanon, M64.
rewrite (Z.mod_small (p + 0)), (Z.mod_small s), (Z.mod_small (p + s)), Z.mod_small by lia. lia.
Qed.

Lemma eva_entry : forall sg cs, (sg = 1 /\ c = 45 \/ sg = 0 /\ c <> 45) -> conds_ok E0 cs ->
  st_ok_pi SEGS VAL E0 (eva_ss1 sg cs)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + EVA_K EV_NUM)) mem (seg_rom SEGS))).
Proof.
intros sg cs Hsg Hcs.
pose proof eva_cut_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
pose proof asan_consts as (C1 & _). pose proof HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hi1 & _).
assert (Hsf : 0x7fff8000 <= shadow_addr fr <= 0x7fff8000 + 2 ^ 44).
{ unfold shadow_addr, SHADOW_OFF. split; [pose proof (Z.div_pos fr 8 ltac:(lia) ltac:(lia)); lia|].
  pose proof (Z.div_le_upper_bound fr 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
assert (HC : 0 <= c < 256).
{ destruct HK as (HM & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hc & _).
  pose proof (eva_mid_src _ _ _ _ _ _ _ _ _ _ HM) as (Hg & _). unfold bytes_at in Hg.
  rewrite <- Hc. exact (eva_nth_byte _ _ _ _ _ Hg). }
rewrite restrict_mkst_fx. unfold eva_ss1. apply pa_entry_st_ok_full.
- exact HRE.
- vm_compute. reflexivity.
- unfold eva_R1, eva_R4, eva_R8. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U9, ?U25;
    (split; [lia|]); (split; [lia|]); (split; [|constructor]); intros o Ho; apply apresent_writable.
  + apply F14. lia.
  + apply F15. lia.
  + apply F15. lia.
- unfold eva_R1, eva_R4, eva_R8.
  cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.base_val YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite ?U9, ?U25. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split].
  + unfold eva_atoms. cbn [YP0m.f_atoms YP0m.atoms_ok]. unfold YP0m.afact_ok. cbn [YP0m.af_lo YP0m.af_hi YP0m.af_al2].
    rewrite U9, U11, U12, U24, U25, U32, U33. unfold EVA_CEIL, SHADOW_OFF in *. unfold ea_len in *.
    repeat match goal with |- _ /\ _ => split end;
      first [ exact I | lia | (change (2 ^ 5) with 32; exact F5) | (change (2 ^ 0) with 1; apply Z.mod_1_r) ].
  + exact Hcs.
  + cbn [YP0m.f_alias YP0m.alias_ok]. split; [|exact I]. apply U_inj. unfold eva_sgv.
    rewrite !U_SAlu, !U_SOff, !U_SLit. cbn [zalu_raw]. rewrite U11, U21, (eva_sltu45 c HC).
    unfold ea_len in *.
    destruct (Z.eqb_spec c 45) as [E45|N45]; destruct Hsg as [[-> E]|[-> E]]; try congruence;
      apply eva_zadd; lia.
Qed.

(* ---- the engine runs. The tactics find the walk's hypotheses by their types: the state (st_ok_pi), the
   journal (ajournal_x), the shadow facts (sh_ok), ev_mid, ev_fsh, the run's frames (frame_of / mem_grows). ---- *)
Ltac eva_regcbn H :=
  cbn [YP09.base_val YP09.r_base YP09.r_wlo YP09.r_whi] in H; cbn [ew ewset Nat.eqb] in H;
  rewrite ?U9, ?U25, ?U11 in H.
Ltac eva_awr1 :=
  unfold awr_byte;
  first [ exfalso; lia
        | left; lia
        | right; right; right; unfold in_frames; exists 1, (ea_pos a); split; [left; reflexivity|];
          right; unfold in_zr; cbn [fst snd];
          match goal with Hfa : frame_addr _ 1 (ea_pos a) = ea_fr a |- _ => rewrite Hfa end;
          change (fs_frame_bytes 1 / 8) with 16; lia ].
Ltac eva_awr :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?lyc ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc lyc own) end;
  unfold awr_ok; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz;
  repeat (apply eva_inw_cons in Hz; destruct Hz as [Hz|Hz]; [eva_regcbn Hz; eva_awr1|]);
  exfalso; exact (eva_inw_nil _ _ Hz).
Ltac eva_inw_split Hin tac :=
  lazymatch type of Hin with in_wrange ?E ?rs ?zz =>
    let rs' := eval vm_compute in rs in change (in_wrange E rs' zz) in Hin end;
  repeat (apply eva_inw_cons in Hin; destruct Hin as [Hin|Hin]; [eva_regcbn Hin; tac|]);
  exfalso; exact (eva_inw_nil _ _ Hin).
Ltac eva_wz :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Hin := fresh "Hin" in intros z Hz Hin;
  eva_inw_split Hin ltac:(unfold ev_wz, STK_RT_STRTOD, ESTACK; first [exfalso; lia | lia]).
Ltac eva_wzS :=
  let z := fresh "z" in let Hz := fresh "Hz" in let Hin := fresh "Hin" in intros z Hz Hin;
  eva_inw_split Hin ltac:(cbv beta; lia).
(* after a run: ev_mid (lane M's keep, with the run's end memnorm HPM) and the frame shadow bytes at the new memory *)
Ltac eva_keep :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
  try (match goal with HFSH : ev_fsh _ _ _ |- _ =>
    let HV := fresh "HV" in let HF' := fresh "HFSH" in
    pose proof (eva_frame_view SEGS _ _ _ _ _ (fun z => ea_S1 a + 104 <= z < ea_S1 a + 120) HFr ltac:(eva_wzS)) as HV;
    pose proof (eva_fsh_keep _ _ HV HFSH) as HF'; clear HFSH HV end);
  lazymatch goal with
  | HM : ev_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HPM : YAkMemnorm.memnorm _ _ |- _ =>
    let HM' := fresh "HM" in
    pose proof (KEEP _ _ _ _ _ _ _ _ _ _ _ _ _ HM HJ) as HM';
    specialize (HM' (eva_frame_view SEGS _ _ _ _ _ (ev_wz B a) HFr ltac:(eva_wz)));
    specialize (HM' ltac:(exact HPM));
    clear HM HFr;
    repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end
  end end.
Ltac eva_obl_tac :=
  unfold EVA_Bx;
  lazymatch goal with HM : ev_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  eapply eva_obl; [ exact HM | cbn [ew ewset Nat.eqb]; exact U24 | cbn [ew ewset Nat.eqb]; exact U11 | lia | lia ] end.
Ltac eva_run Bsp stop :=
  lazymatch goal with
  | HS : st_ok_pi _ _ _ _ _, HJ : ajournal_x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _,
    HPM : YAkMemnorm.memnorm _ _ |- _ =>
    paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM Bsp stop
  end;
  lazymatch goal with
  | |- awr_ok _ _ _ _ _ _ _ _ _ => eva_awr
  | |- range_addressable _ _ _ _ => eva_obl_tac
  | |- SRr _ _ _ _ => eva_keep
  end.
(* the frame's shadow bytes after run 1, from its two one-byte zero chunks *)
Ltac eva_fsh_init :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict (w_H W) ?ms) |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with [?r1; ?r4; ?r8] =>
      let H4 := fresh "Hz4" in let H8 := fresh "Hz8" in
      pose proof (eva_chunk1z SEGS VAL E ss (restrict (w_H W) ms) r4 4 HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as H4;
      pose proof (eva_chunk1z SEGS VAL E ss (restrict (w_H W) ms) r8 8 HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as H8;
      cbn [YP09.base_val YP09.r_base ms_mem restrict] in H4, H8; rewrite U25 in H4, H8;
      let HF := fresh "HFSH" in pose proof (eva_fsh_of _ H4 H8) as HF; clear H4 H8
    end end.
(* run 2 drops the frame's shadow bytes (they lie in the token band) and reads the text *)
Ltac eva_drop :=
  lazymatch goal with HS : st_ok_pi ?sgs ?v ?E ?ss ?ms |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with ?r1 :: _ =>
      let HS' := fresh "HS" in
      pose proof (eva_submem sgs v E ss ms [r1] HS
        (submem_keep _ _ _ _ (subregion_refl _) (submem_nil _)) eq_refl) as HS';
      clear HS end end.
Ltac eva_addRT sg n :=
  lazymatch goal with HS : st_ok_pi ?sgs ?v ?E ?ss ?ms, HM : ev_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    Hsg : ev_sg c = _ |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with [?r1] =>
      let HS' := fresh "HS" in
      pose proof (st_ok_pi_add_region E ss ms (eva_RT sg n) HS eq_refl
        ltac:(eapply eva_RT_ok; [exact HM | exact U11 | rewrite Hsg; reflexivity | exact Hb0 | exact Hb1
                                | exact U32 | exact U33 | lia | lia])
        ltac:(change (ss_mem ss) with rs; apply eva_RT_disj; [reflexivity | reflexivity | exact U9 | exact U11 | lia | lia | lia]))
        as HS';
      clear HS end end.
(* a branch: the two cases, the engine's condition as a byte fact *)
Ltac eva_hc :=
  match goal with H : branch_taken _ _ _ = _ |- _ =>
    first [rewrite branch_ltu_U in H | rewrite branch_ne_U in H];
    rewrite ?U_SOff, ?U_SLit in H; cbn [ew ewset Nat.eqb] in H; rewrite ?U32, ?U33 in H;
    first [ rewrite (eva_digit_lt _ HB0) in H | rewrite (eva_digit_gt _ HB1) in H | rewrite (eva_eq48 _ HB0) in H ];
    repeat lazymatch type of H with
    | negb _ = true => apply negb_true_iff in H
    | negb _ = false => apply negb_false_iff in H
    | Z.eqb _ _ = true => apply Z.eqb_eq in H
    | Z.eqb _ _ = false => apply Z.eqb_neq in H
    end
  end.
Ltac eva_branch :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    psrr_branch_tok RUNTO BR HS SHOK EVA_Bspan end; eva_hc.
(* the leaves: the machine registers and memory at CT / CL *)
Ltac eva_reg r R :=
  lazymatch goal with HS : st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) |- _ =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R;
    cbn [sv_denot ew ewset Nat.eqb] in R
  end.
Ltac eva_kept_tac :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss (restrict _ ?ms) |- _ =>
    let Hk := fresh "Hkp" in
    pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W) ms) regs [] eva_kept HS
       ltac:(repeat (apply eva_agree_ewset; [lia|]); exact HAG0) ltac:(vm_compute; reflexivity)) as Hk;
    cbn [ms_regs restrict] in Hk; exact Hk end.
Ltac eva_v8 off e :=
  lazymatch goal with HS : st_ok_pi _ _ ?E ?ss ?msr |- _ =>
    let rs := eval vm_compute in (ss_mem ss) in
    lazymatch rs with context [YP09.mkRegion (Some 9%nat) ?lo ?hi ?wl ?wh ?cs] =>
      let Hv := fresh "Hv" in
      pose proof (eva_chunk8 SEGS VAL E ss msr (YP09.mkRegion (Some 9%nat) lo hi wl wh cs) off e HS
        ltac:(change (ss_mem ss) with rs; cbn [In]; tauto) ltac:(cbn [YP09.r_chunks In]; tauto)) as Hv;
      cbn [YP09.base_val YP09.r_base ms_mem restrict ew ewset Nat.eqb] in Hv; rewrite U9 in Hv; apply Hv
    end end.
Ltac eva_r23 := let R := fresh "R" in eva_reg (23%bv : bv 5) R; rewrite R, Z.add_0_r, Z_to_bv_bv_unsigned; exact (HA 22%bv).
Ltac eva_r21 := let R := fresh "R" in eva_reg (21%bv : bv 5) R; rewrite R; exact eva_w64_m1.
Ltac eva_v104 := eva_v8 104 (SOff 23 0);
  [ cbn [sv_denot ew ewset Nat.eqb]; rewrite Z.add_0_r, (HA 23%bv); reflexivity
  | let Hr := fresh "Hr" in pose proof (bv_unsigned_in_range _ (getr regs 23)) as Hr; unfold bv_modulus in Hr; exact Hr ].
Ltac eva_mid := lazymatch goal with HM : ev_mid _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => exact HM end.
Ltac eva_pmkst := lazymatch goal with HS : st_ok_pi _ _ _ _ _ |- _ => pmkst HS end.
Ltac eva_leaf_CT K Hi1 Hnc :=
  eva_pmkst; rewrite eva_cfg_CT; apply K;
  eapply eva_CT; [ eva_mid | eva_kept_tac | eva_r23 | eva_r21 | eva_v104 | ];
  apply (eva_N_refuse _ _ c); [ exact Hi1 | exact Hnc | exact HD | ].
Ltac eva_r27 := let R := fresh "R" in eva_reg (27%bv : bv 5) R; rewrite R, U18; reflexivity.
Ltac eva_v112 := eva_v8 112 (SOff 18 64); [ cbn [sv_denot ew ewset Nat.eqb]; rewrite U18; reflexivity | lia ].
Ltac eva_rj r := let R := fresh "R" in eva_reg r R; rewrite R, U11; unfold w64; f_equal; lia.
Ltac eva_rlit r := let R := fresh "R" in eva_reg r R; rewrite R; first [exact eva_w64_m11 | reflexivity].
Ltac eva_leaf_CL K :=
  eva_pmkst; rewrite eva_cfg_CL; eapply K;
  eapply eva_CL; [ eva_mid | eva_kept_tac | eva_r23 | eva_r21 | eva_v104 | eva_r27 | eva_v112
                 | eva_rj (22%bv : bv 5) | eva_rj (10%bv : bv 5) | eva_rlit (13%bv : bv 5) | eva_rlit (14%bv : bv 5)
                 | eva_rlit (15%bv : bv 5)
                 | lazymatch goal with H : ev_fsh _ _ _ |- _ => exact H end | ];
  unfold ev_lead_ok; rewrite <- Hb0, <- Hb1; split; [lia|]; split; [assumption|].

(* the walk of +0x2c4 .. +0x364 / +0x9f4 from P_KIND at a number's first byte *)
Lemma eva_walk : forall Q,
  (forall regs' mem' md', ev_CT B ARx SK a W regs' mem' md' ly Sa Hp k i1 c ->
     SRr SEGS W (ev_cfg fx regs' 0x9f4 mem' md') Q) ->
  (forall regs' mem' md' j, ev_CL B ARx SK a W regs' mem' md' ly Sa Hp k i1 c j ->
     SRr SEGS W (ev_cfg fx regs' 0x364 mem' md') Q) ->
  SRr SEGS W (ev_cfg fx regs EV_NUM mem md) Q.
Proof.
intros Q KTc KLc.
pose proof eva_cut_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
pose proof eva_shf as Hsf. pose proof asan_consts as (C1 & _).
pose proof HK as (HM & _ & _ & _ & _ & _ & _ & _ & _ & Hi1 & Hnc & _).
pose proof (eva_mid_aj _ _ _ _ _ _ _ _ _ _ HM) as HJ.
pose proof (eva_mid_mn _ _ _ _ _ _ _ _ _ _ HM) as HPM.
assert (SHOK : sh_ok SEGS EVA_Bx [] E0 (mrestrict (w_H W) mem)) by constructor.
assert (HLEN : ea_len a = Z.of_nat (length x)) by reflexivity.
unfold EVA_CEIL in F3.
rewrite <- (eva_cfg EV_NUM).
destruct (Z.eq_dec c 45) as [Hc45 | Hc45].
- assert (Hsg : ev_sg c = 1%nat) by (unfold ev_sg; rewrite (proj2 (Z.eqb_eq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases (i1 + ev_sg c) (length x)) as [Hj | Hj].
  + destruct (Nat.lt_ge_cases (i1 + ev_sg c + 1) (length x)) as [Hj2 | Hj2].
    * pose proof (eva_entry 1 [eva_cLT 1; eva_cLT 2] ltac:(left; split; [reflexivity | exact Hc45])
        ltac:(split; [apply eva_cLT_ok; lia | split; [apply eva_cLT_ok; lia | exact I]])) as HS.
      eva_run EVA_Bspan0 (EVA_K 0x2d4). eva_fsh_init. eva_drop. eva_addRT 1 2.
      eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
      -- eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
      -- eva_run EVA_Bspan (EVA_K 0x364). eva_branch.
         ++ eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (H48 & _). congruence.
         ++ eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
            ** eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc.
               right; right. split; [lia|]. split; [rewrite <- Hb0; assumption | rewrite <- Hb1; assumption].
            ** eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (_ & _ & Hd1). congruence.
    * pose proof (eva_entry 1 [eva_cLT 1; eva_cGE 2] ltac:(left; split; [reflexivity | exact Hc45])
        ltac:(split; [apply eva_cLT_ok; lia | split; [apply eva_cGE_ok; lia | exact I]])) as HS.
      eva_run EVA_Bspan0 (EVA_K 0x2d4). eva_fsh_init. eva_drop. eva_addRT 1 1.
      eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
      -- eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
      -- eva_run EVA_Bspan (EVA_K 0x364). eva_branch.
         ++ eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (H48 & _). congruence.
         ++ eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (_ & Hlt & _). lia.
  + pose proof (eva_entry 1 [eva_cGE 1] ltac:(left; split; [reflexivity | exact Hc45])
      ltac:(split; [apply eva_cGE_ok; lia | exact I])) as HS.
    eva_run EVA_Bspan0 (EVA_K 0x2d4). eva_drop.
    eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc. left. lia.
- assert (Hsg : ev_sg c = 0%nat) by (unfold ev_sg; rewrite (proj2 (Z.eqb_neq c 45) Hc45); reflexivity).
  destruct (Nat.lt_ge_cases (i1 + ev_sg c + 1) (length x)) as [Hj2 | Hj2].
  + pose proof (eva_entry 0 [eva_cLT 0; eva_cLT 1] ltac:(right; split; [reflexivity | exact Hc45])
      ltac:(split; [apply eva_cLT_ok; lia | split; [apply eva_cLT_ok; lia | exact I]])) as HS.
    eva_run EVA_Bspan0 (EVA_K 0x2d4). eva_fsh_init. eva_drop. eva_addRT 0 2.
    eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
    * eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
    * eva_run EVA_Bspan (EVA_K 0x364). eva_branch.
      -- eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (H48 & _). congruence.
      -- eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
         ++ eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc.
            right; right. split; [lia|]. split; [rewrite <- Hb0; assumption | rewrite <- Hb1; assumption].
         ++ eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (_ & _ & Hd1). congruence.
  + pose proof (eva_entry 0 [eva_cLT 0; eva_cGE 1] ltac:(right; split; [reflexivity | exact Hc45])
      ltac:(split; [apply eva_cLT_ok; lia | split; [apply eva_cGE_ok; lia | exact I]])) as HS.
    eva_run EVA_Bspan0 (EVA_K 0x2d4). eva_fsh_init. eva_drop. eva_addRT 0 1.
    eva_run EVA_Bspan (EVA_K 0x9f4). eva_branch.
    * eva_run EVA_Bspan (EVA_K 0x9f4). eva_leaf_CT KTc Hi1 Hnc. right; left. split; [lia | rewrite <- Hb0; assumption].
    * eva_run EVA_Bspan (EVA_K 0x364). eva_branch.
      -- eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (H48 & _). congruence.
      -- eva_run EVA_Bspan (EVA_K 0x364). eva_leaf_CL KLc. intros (_ & Hlt & _). lia.
Qed.

End env.

Lemma eva_E0_reg : forall extra n (r : Prelude.reg) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
  0 <= v < 2 ^ 64 -> bv_unsigned (ew (Eimg (Ereg regs extra)) n) = v.
Proof.
intros extra n r v Hn Hr Hv. pose proof (u5_range r) as Hr5.
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs extra n r Hn), Hr. apply eva_u64. exact Hv.
Qed.
Lemma eva_E0_extra : forall w0 w1, 0 <= w0 < 2 ^ 64 -> 0 <= w1 < 2 ^ 64 ->
  bv_unsigned (ew (Eimg (Ereg regs [w64 w0; w64 w1])) 32) = w0 /\
  bv_unsigned (ew (Eimg (Ereg regs [w64 w0; w64 w1])) 33) = w1.
Proof.
intros w0 w1 H0 H1. rewrite !Eimg_low by (unfold A_TEXT; lia).
pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 0) as E32. pose proof (ew_Ereg_extra regs [w64 w0; w64 w1] 1) as E33.
cbn [Nat.add nth] in E32, E33. rewrite E32, E33. split; apply eva_u64; assumption.
Qed.

(* the piece from the cut, at the machine's float state fx: the env of the walk is the cut's registers and the two
   text bytes after the sign *)
Lemma eva_core : forall Q,
  (forall regs' mem' md', ev_CT B ARx SK a W regs' mem' md' ly Sa Hp k i1 c ->
     SRr SEGS W (ev_cfg fx regs' 0x9f4 mem' md') Q) ->
  (forall regs' mem' md' j, ev_CL B ARx SK a W regs' mem' md' ly Sa Hp k i1 c j ->
     SRr SEGS W (ev_cfg fx regs' 0x364 mem' md') Q) ->
  SRr SEGS W (ev_cfg fx regs EV_NUM mem md) Q.
Proof.
intros Q KTc KLc.
pose proof HK as (HM & Hregs & _ & H21 & H22 & H23 & _ & H11 & H12 & Hi1 & Hnc & _).
destruct Hregs as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof (eva_mid_src _ _ _ _ _ _ _ _ _ _ HM) as (Hg & Hx0 & Hxe & _). unfold bytes_at in Hg.
pose proof eva_cut_facts as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13 & F14 & F15 & F16).
pose proof eva_shf as Hsf. unfold EVA_CEIL in F3. unfold ea_len in *.
pose proof (eva_nth_byte _ _ _ _ (i1 + ev_sg c)%nat Hg) as HB0.
pose proof (eva_nth_byte _ _ _ _ (S (i1 + ev_sg c)) Hg) as HB1.
pose proof (eva_nth_byte _ _ _ _ i1 Hg) as HC. rewrite Hnc in HC.
destruct (eva_E0_extra (nth (i1 + ev_sg c)%nat x 0) (nth (S (i1 + ev_sg c)) x 0) ltac:(lia) ltac:(lia)) as (U32 & U33).
refine (eva_walk (nth (i1 + ev_sg c)%nat x 0) (nth (S (i1 + ev_sg c)) x 0)
  (Eimg (Ereg regs [w64 (nth (i1 + ev_sg c)%nat x 0); w64 (nth (S (i1 + ev_sg c)) x 0)]))
  eq_refl eq_refl HB0 HB1 (Eimg_env _) _ (regs_ok_Eimg_Ereg _ _) _ _ _ _ _ _ _ _ U32 U33 Q KTc KLc).
- split; [|reflexivity]. intros n Hn. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite !ew_Ereg_lt by lia. reflexivity.
- intros r. pose proof (u5_range r) as Hr5. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_reg.
- apply (eva_E0_reg _ 9 9%bv); [reflexivity | exact R9 | lia].
- apply (eva_E0_reg _ 11 11%bv); [reflexivity | exact H11 | lia].
- apply (eva_E0_reg _ 12 12%bv); [reflexivity | exact H12 | unfold ea_len; lia].
- apply (eva_E0_reg _ 18 18%bv); [reflexivity | exact R18 | lia].
- apply (eva_E0_reg _ 21 21%bv); [reflexivity | exact H21 | lia].
- apply (eva_E0_reg _ 24 24%bv); [reflexivity | exact R24 | unfold SHADOW_OFF; lia].
- apply (eva_E0_reg _ 25 25%bv); [reflexivity | exact R25 | lia].
Qed.

End ctx.
End core.

(* ======== the sub-piece: ev_A_stmt (S8aNumCut.v), at the entry float state fx, the cut's state fxc ======== *)
Section main.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* the image fact of the instance (PAImg_prog.v A_entry_ex_value at PI_prog_A: ex_value is slot 1841) *)
Hypothesis Hent : pa_sigma AS_ex_value = pa_val A_TEXT + 7364.
(* lane M's ev_mid_keep (S8aNumCut.v ev_mid_keep_stmt), supplied at the integration *)
Hypothesis ev_mid_keep : forall a, ev_mid_keep_stmt B ARx SK a.

Theorem ev_A : ev_A_stmt B ARx SK.
Proof.
intros IMG a KTa KLa fxc W regs mem md ly S Hp k i1 c Hpre Hfx Hkind H34 H91 H123 H102 H110 H116.
pose proof Hpre as (((HAR0 & _) & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hd0 & _) & _ & _ & _ & _ & _ & _ & Hdl & _).
pose proof Hkind as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hws & _).
apply (@eva_core fxc rc cp PI RL PA B ARx SK hl LAWS Hent IMG a
  (fun ly' S' Hp' W' mem' md' k' p dep dl mem2 md2 k2 HM HJ HV HMN =>
     ev_mid_keep a ly' S' Hp' W' mem' md' k' p dep dl mem2 md2 k2 Hpre HM HJ HV HMN)
  HAR0 Hd0 Hdl W regs mem md ly S Hp k i1 c Hkind).
- unfold eva_disp. repeat split; assumption.
- intros regs' mem' md' HCT. exact (KTa fxc W regs' mem' md' ly S Hp k i1 c Hpre Hfx HCT).
- intros regs' mem' md' j HCL. exact (KLa fxc W regs' mem' md' ly S Hp k i1 c j Hpre Hfx HCL).
Qed.

End main.
