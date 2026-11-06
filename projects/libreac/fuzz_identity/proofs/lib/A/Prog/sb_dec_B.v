(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:138-139, for
   libreac/fuzz_identity's ASan build (lib/A). *)
(* sb_dec (fuzz_identity.asan 0x83494, AF_sb_dec = 0x2d88): segment B of the ASan-build walk,
   0x835f4 .. 0x836e8 (+0x160 .. +0x254, 61 slots), the checked emit loop. Proves seg_sbd_B of
   lib/A/Prog/sb_dec_inv.v.

   The loop runs kd = length (sb_dec_D v md) turns (1, 2 or 3). Turn i reads b->n and b->cap
   (0x8364c, 0x83650), tests n + i + 1 >=u cap (0x83658), and
   - with room: checks the shadow of d[kd-1-i] (0x83664, a token load whose slow block at 0x836c4 is
     decided by the frame's shadow byte 4 = 04), of b (0x8366c) and of b+16 (0x83674), stores
     b->n := n + i + 1 (0x83684), checks the shadow of p + n + i (0x83694) and stores the digit
     (0x8369c);
   - without room: checks the shadow of b+24 (0x836a4, the whole granule: t6 = (b+24) mod 8 + 3 is
     hoisted to 0x83620/0x83630) and stores b->over := 1 (0x836ac).
   The shadow of b .. b+32 is zero because b lies in the caller's machine stack (sb_dec.sbd_stack_zero);
   the shadow of p + n .. p + n + acc is the premise range_addressable that sbd_A_end carries; the
   frame's shadow byte 4 is 04. So no __asan_report_* call is reached.

   One symbolic state per (kd, acc) pair (acc = min kd room; nine pairs), run with paj_run_to_tok to
   0x836e8. The branch at 0x83658 stops each run and is decided from sb_dec_room / sb_dec_acc. After a
   turn without room b->n stops growing, so every later turn re-tests the same condition and the engine
   decides it from f_conds: at most acc + 1 stops. *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YI08.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentSyms IdentList IdentPa IdentPaLib IdentBase.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentFrame YC85 YC81 YC4b YC45 YC1g YC1h.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentCJ.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require sb_dec_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import sb_dec sb_dec_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b switches lia's euclidean-division handling off; this walk divides by 8 (shadow_of_addr). *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- general helpers ---------------------------------------------------------------------------- *)
(* An atom below the first token atom keeps its value when a run extends the environment. *)
Lemma ew_ewset_lo : forall E k w n, (n < k)%nat -> ew (ewset E k w) n = ew E n.
Proof. intros E k w n Hn. cbn [ew ewset]. rewrite (proj2 (Nat.eqb_neq n k) ltac:(lia)). reflexivity. Qed.
(* A byte range that meets no byte of [lo, hi) lies on one side of it. *)
Lemma sbB_apart : forall q n lo hi, 0 < n -> lo < hi -> (forall a, q <= a < q + n -> ~ (lo <= a < hi)) ->
  q + n <= lo \/ hi <= q.
Proof.
intros q n lo hi Hn Hlh H. destruct (Z_le_gt_dec (q + n) lo) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec hi q) as [H2|H2]; [right; exact H2|]. exfalso. apply (H (Z.max q lo)); lia.
Qed.
(* Selectors over a literal region list, so a fact of the final state is found by computation. *)
Fixpoint rgn_of (rs : smem) (n : nat) : YP09.region :=
  match rs with
  | [] => YP09.mkRegion None 0 0 0 0 []
  | r :: rs' => if YP09.obase_eqb (YP09.r_base r) (Some n) then r else rgn_of rs' n
  end.
Lemma rgn_of_In : forall rs n, YP09.r_base (rgn_of rs n) = Some n -> In (rgn_of rs n) rs.
Proof.
induction rs as [|r rs IH]; intros n H; cbn [rgn_of] in H |- *; [discriminate|].
destruct (YP09.obase_eqb (YP09.r_base r) (Some n)); [left; reflexivity | right; exact (IH n H)].
Qed.
Fixpoint chk_of (cs : list YP09.chunk) (off : Z) : option YP09.chunk :=
  match cs with
  | [] => None
  | c :: cs' => if YP09.c_off c =? off then Some c else chk_of cs' off
  end.
Lemma chk_of_In : forall cs off c, chk_of cs off = Some c -> In c cs.
Proof.
induction cs as [|c0 cs IH]; intros off c H; cbn [chk_of] in H; [discriminate|].
destruct (YP09.c_off c0 =? off); [injection H as <-; left; reflexivity | right; exact (IH off c H)].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg ident_listing}.
#[local] Notation SEGS := (@pa_segs _ ident_listing PI).
#[local] Notation VAL := (@pa_val _ ident_listing PI).
#[local] Notation BASE := (@pa_val _ ident_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).

(* ---- the symbolic state at 0x835f4 --------------------------------------------------------------
   Atoms 0..31 are the registers at the cut (10 = F, the side-stack frame; 18 = b; 21 = SB), 32..36 are
   p, cap, n, over and p + n (named by an alias, so that p + n + j is the region offset j), 37..39 are
   the digits as the frame holds them: rev (sb_dec_D v md). *)
Definition sbB_Bx : sv := SOff 21 0.
Definition sbB_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* a4 = F + 32 (the digit array, 0x83534 + 0x83604), a5 = kd (0x835b0 / 0x835f0). *)
Definition sbB_sr (kd : Z) : list sv :=
  sr_set (sr_set sr_atoms (14%bv : bv 5) (SOff 10 32)) (15%bv : bv 5) (SLit kd).
Definition sbB_rb : YP09.region := YP09.mkRegion (Some 18%nat) 0 28 16 28
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0));
   YP09.mkChunk 16 (CVal 8 (SOff 34 0)); YP09.mkChunk 24 (CVal 4 (SOff 35 0))].
Definition sbB_rd (kd : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 32 (32 + kd) 0 0
  (map (fun j => YP09.mkChunk (32 + Z.of_nat j) (CVal 1 (SOff (37 + j) 0))) (seq 0 (Z.to_nat kd))).
Definition sbB_rq (acc : Z) : YP09.region := YP09.mkRegion (Some 36%nat) 0 acc 0 acc [].
Definition sbB_mem (kd acc : Z) : smem := [sbB_rb; sbB_rd kd] ++ (if acc =? 0 then [] else [sbB_rq acc]).
Definition sbB_atoms (kd acc : Z) : list (nat * afact) :=
  [(10%nat, mkAF 4096 (2 ^ 47 - 64) 5); (18%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (21%nat, mkAF SB SB 0);
   (32%nat, mkAF 0 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 64 - 1) 0); (34%nat, mkAF 0 (2 ^ 64 - 5) 0);
   (35%nat, mkAF 0 (2 ^ 32 - 1) 0)]
  ++ (if acc =? 0 then [] else [(36%nat, mkAF 4096 (2 ^ 47 - acc) 0)])
  ++ map (fun j => ((37 + j)%nat, mkAF 0 255 0)) (seq 0 (Z.to_nat kd)).
Definition sbB_facts (kd acc : Z) : facts :=
  mkFacts (sbB_atoms kd acc) [] [(SAlu ALU_ADD (SOff 32 0) (SOff 34 0), SOff 36 0)].
Definition sbB_ss (kd acc : Z) : sstate :=
  mkSS (AF_sb_dec + SBD_A_END) (sbB_sr kd) (sbB_mem kd acc) None (sbB_facts kd acc).
Definition sbB_SH (acc : Z) : list shent :=
  [mkSHE 18 0 32; mkSHE 10 32 36] ++ (if acc =? 0 then [] else [mkSHE 36 0 acc]).
Definition sbB_stop : Z := AF_sb_dec + SBD_B_END.
(* The values of the extra atoms 32..39. *)
Definition sbB_vals (g : sbd_ctx) : list Z :=
  [sq_p g; sq_cap g; sq_n g; sq_ov g; sq_p g + sq_n g;
   nth 0 (rev (sq_D g)) 0; nth 1 (rev (sq_D g)) 0; nth 2 (rev (sq_D g)) 0].
Definition sbB_E (regs2 : bvmap 5 word) (g : sbd_ctx) : env :=
  Eimg (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))).
(* The bytes the segment writes: b->n, b->over and the digits. *)
Definition sbB_wr (g : sbd_ctx) (acc : Z) (a : Z) : Prop :=
  (sq_b g + 16 <= a < sq_b g + 28) \/ (sq_p g + sq_n g <= a < sq_p g + sq_n g + acc).

Section h.
Variable B : asyms.
Section walk.
Hypothesis LAWS : AR_laws SEGS B.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- a value read back out of a region's chunk ---------------------------------------------------- *)
Lemma sbB_vm_of_chunk : forall (E : env) (m : word -> option byte) (r : YP09.region) (off : Z) (w : N) (e : sv) (z : Z),
  YP09.region_ok SEGS E m r -> In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m (base_val E (YP09.r_base r) + off) (N.to_nat w) z.
Proof.
intros E m r off w e z Hr Hin He Hz Hw.
exact (val_of_chunk_ok SEGS E m (base_val E (YP09.r_base r)) off w e z
  (YP09.region_ok_chunk SEGS E m r _ Hr Hin) He Hz Hw).
Qed.
(* One byte of the shadow, as the engine's shadow reader gives it. *)
Lemma sbB_rdof_of_vm : forall (m : word -> option byte) a v, val_mem SEGS m a 1 v -> 0 <= v < 256 ->
  rd_of SEGS m a = Some v.
Proof.
intros m a v H Hv. pose proof (H 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0.
rewrite (le_byte_small v 1 0 ltac:(cbn; lia) ltac:(lia)) in H0.
assert (Hsh : Z.shiftr v (8 * Z.of_nat 0) = v)
  by (cbn [Z.of_nat]; rewrite Z.mul_0_r, Z.shiftr_0_r; reflexivity).
rewrite Hsh in H0.
unfold rd_of. rewrite H0. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. lia.
Qed.

(* ---- the buffer and sb_dec's own frame do not meet ------------------------------------------------ *)
Lemma sbB_frame_dst : forall (g : sbd_ctx) pos ly2 S2 mem2 md2 q n a,
  AR SEGS B ly2 S2 (sq_W g) mem2 md2 ->
  frames S2 = (0, pos) :: frames (sq_Sc g) ->
  ablocks B ly2 S2 = ablocks B (sq_lyc g) (sq_Sc g) ->
  ~ In (0, pos) (frames (sq_Sc g)) ->
  (forall cid p', frame_addr ly2 cid p' = frame_addr (sq_lyc g) cid p') ->
  tdst_ok B (sq_lyc g) (sq_Sc g) q n -> q <= a < q + n ->
  ~ (sq_F g pos <= a < sq_F g pos + 64).
Proof.
intros g pos ly2 S2 mem2 md2 q n a HAR Hfrs Hab Hni Hfa Hdst Ha Hin.
assert (HinS2 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFeq : frame_addr ly2 0 pos = sq_F g pos) by (unfold sq_F; apply Hfa).
destruct (Hdst a Ha) as [(bb & m & Hbin & Hbr) | (cid & pos' & Hfin & Hr)].
- rewrite <- Hab in Hbin.
  pose proof (sep_block_frame SEGS B LAWS ly2 S2 (sq_W g) mem2 md2 bb m 0 pos HAR Hbin HinS2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HFeq in Hd.
  change (fs_frame_bytes 0) with 64 in Hd. lia.
- apply in_split in Hfin as (f1 & f2 & Ef).
  pose proof (sep_frames_pos SEGS B LAWS ly2 S2 (sq_W g) mem2 md2 (0, pos) (cid, pos') [] f1 f2 HAR
    ltac:(rewrite Hfrs, Ef; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd.
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
  rewrite HFeq in Hd. rewrite (Hfa cid pos') in Hd.
  change (fs_frame_bytes 0) with 64 in Hd. lia.
Qed.

(* ---- the entry state of the segment --------------------------------------------------------------- *)
Lemma sbB_entry : forall (g : sbd_ctx) (pos : Z) (ly2 : alayout) (S2 : astate) (regs2 : bvmap 5 word)
  (mem2 : word -> option byte) (md2 : Model) (kd acc : Z),
  1 <= kd <= 3 -> 0 <= acc <= kd -> Z.of_nat (length (sq_D g)) = kd ->
  AR SEGS B ly2 S2 (sq_W g) mem2 md2 ->
  frames S2 = (0, pos) :: frames (sq_Sc g) ->
  ablocks B ly2 S2 = ablocks B (sq_lyc g) (sq_Sc g) ->
  ~ In (0, pos) (frames (sq_Sc g)) ->
  (forall cid p', frame_addr ly2 cid p' = frame_addr (sq_lyc g) cid p') ->
  ly_stk_lo ly2 = ly_stk_lo (sq_lyc g) -> ly_stk_hi ly2 = ly_stk_hi (sq_lyc g) ->
  alloc_ceiling <= ly_stk_lo (sq_lyc g) -> ly_stk_hi (sq_lyc g) <= 2 ^ 47 ->
  tsb_dec_rec_at (sq_lyc g) (sq_b g) -> sq_b g mod 8 = 0 ->
  0 <= sq_p g < 2 ^ 64 -> 0 <= sq_cap g < 2 ^ 64 -> 0 <= sq_n g -> sq_n g + 4 < 2 ^ 64 ->
  0 <= sq_ov g < 2 ^ 32 ->
  (forall a, sq_b g + 16 <= a < sq_b g + 28 -> apresent (w_H (sq_W g)) mem2 a) ->
  (0 < acc -> tdst_ok B (sq_lyc g) (sq_Sc g) (sq_p g + sq_n g) acc) ->
  (0 < acc -> range_addressable (aview SEGS (w_H (sq_W g)) mem2) SHADOW_OFF (sq_p g + sq_n g) acc) ->
  (0 < acc -> sq_p g + sq_n g + acc <= sq_b g \/ sq_b g + 28 <= sq_p g + sq_n g) ->
  (0 < acc -> forall a, sq_p g + sq_n g <= a < sq_p g + sq_n g + acc -> apresent (w_H (sq_W g)) mem2 a) ->
  getr regs2 10 = w64 (sq_F g pos) -> getr regs2 14 = w64 (sq_F g pos + 32) ->
  getr regs2 15 = w64 kd -> getr regs2 18 = w64 (sq_b g) -> getr regs2 21 = w64 SB ->
  val_mem SEGS (rd (sq_W g) mem2) (sq_b g) 8 (sq_p g) ->
  val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 8) 8 (sq_cap g) ->
  val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 16) 8 (sq_n g) ->
  val_mem SEGS (rd (sq_W g) mem2) (sq_b g + 24) 4 (sq_ov g) ->
  garr8 SEGS (rd (sq_W g) mem2) (sq_F g pos + 32) (rev (sq_D g)) ->
  garr8 SEGS (rd (sq_W g) mem2) (SB + sq_F g pos / 8) SBD_FRAME_SHADOW ->
  st_ok_pi SEGS VAL (sbB_E regs2 g) (sbB_ss kd acc)
    (restrict (w_H (sq_W g)) (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_A_END))) mem2 (seg_rom SEGS)))
  /\ sh_ok SEGS sbB_Bx (sbB_SH acc) (sbB_E regs2 g) (rd (sq_W g) mem2).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 kd acc Hkd Hacc HlenD HAR Hfrs Hab Hni Hfa Hslo Hshi Hcl Hs47
  Hrec Hb8 Rp Rcap Rn0 Rn4 Rov HPb HDst HRA HDisj HPq H10 H14 H15 H18 H21 Vp Vcap Vn Vov HD HFS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HinS2 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFeq : frame_addr ly2 0 pos = sq_F g pos) by (unfold sq_F; apply Hfa).
destruct (al_frames _ _ LAWS ly2 S2 (sq_W g) mem2 md2 0 pos HAR HinS2) as (HF32 & HFapp & _ & _).
destruct (frames_bounds SEGS B LAWS ly2 S2 (sq_W g) mem2 md2 0 pos HAR HinS2) as (HF0 & HFceil & _).
rewrite HFeq in HF32, HFapp, HF0, HFceil.
change (fs_frame_bytes 0) with 64 in HF32, HFapp, HF0, HFceil.
destruct Hrec as [Hblo Hbhi]. rewrite <- Hslo in Hcl. rewrite <- Hshi in Hs47.
assert (HbL : 2 ^ 46 <= sq_b g) by lia.
assert (HbH : sq_b g + 32 <= 2 ^ 47) by lia.
assert (HFL : 4096 <= sq_F g pos) by lia.
assert (HFH : sq_F g pos + 64 <= 2 ^ 47) by lia.
(* the frame lies off the shadow band and below the stack *)
unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp.
(* the digits *)
assert (HlenR : length (rev (sq_D g)) = Z.to_nat kd) by (rewrite length_rev; lia).
assert (HDb : forall j, (j < Z.to_nat kd)%nat ->
  val_mem SEGS (rd (sq_W g) mem2) (sq_F g pos + 32 + Z.of_nat j) 1 (nth j (rev (sq_D g)) 0) /\
  0 <= nth j (rev (sq_D g)) 0 < 256) by (intros j Hj; apply HD; lia).
(* the environment *)
assert (HEI : img_env VAL A_LIM (sbB_E regs2 g)) by (unfold sbB_E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sbB_E regs2 g) n = getr regs2 r).
{ intros n r Hn. unfold sbB_E. rewrite Eimg_low.
  - apply ew_Ereg_nat. exact Hn.
  - pose proof (bv_unsigned_in_range 5 r) as Q. change (bv_modulus 5) with 32 in Q. unfold A_TEXT. lia. }
assert (EX : forall j, (j < 8)%nat -> ew (sbB_E regs2 g) (32 + j) = Z_to_bv 64 (nth j (sbB_vals g) 0)).
{ intros j Hj. unfold sbB_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. exact (map_nth (Z_to_bv 64) (sbB_vals g) 0 j). }
pose proof (ER 10%nat 10%bv eq_refl) as E10. rewrite H10 in E10.
pose proof (ER 18%nat 18%bv eq_refl) as E18. rewrite H18 in E18.
pose proof (ER 21%nat 21%bv eq_refl) as E21. rewrite H21 in E21.
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [nth sbB_vals Nat.add] in E32, E33, E34, E35, E36.
assert (ED : forall j, (j < 3)%nat -> ew (sbB_E regs2 g) (37 + j) = Z_to_bv 64 (nth j (rev (sq_D g)) 0)).
{ intros j Hj. replace (37 + j)%nat with (32 + (5 + j))%nat by lia.
  rewrite (EX (5 + j)%nat ltac:(lia)). f_equal.
  destruct j as [|[|[|j]]]; cbn [nth sbB_vals]; [reflexivity|reflexivity|reflexivity|lia]. }
assert (VB : forall i z, ew (sbB_E regs2 g) i = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 ->
  base_val (sbB_E regs2 g) (Some i) = z).
{ intros i z Hi Hz. cbn [base_val]. rewrite Hi. apply unsigned_lit_small. exact Hz. }
(* the buffer, in the blocks and frames of the current state *)
assert (HDst2 : 0 < acc -> tdst_ok B ly2 S2 (sq_p g + sq_n g) acc).
{ intros Hp a Ha. destruct (HDst Hp a Ha) as [(bb & m & Hbin & Hbr) | (cid & p' & Hfin & Hr)].
  - left. exists bb, m. split; [rewrite Hab; exact Hbin | exact Hbr].
  - right. exists cid, p'. split; [rewrite Hfrs; right; exact Hfin|].
    unfold in_zr, frame_rng in Hr |- *. cbn [fst snd] in Hr |- *. rewrite (Hfa cid p'). exact Hr. }
assert (HQF : 0 < acc -> 4096 <= sq_p g + sq_n g /\ sq_p g + sq_n g + acc <= alloc_ceiling /\
  (forall x, sq_p g + sq_n g <= x < sq_p g + sq_n g + acc ->
     (x < IMG_LO \/ IMG_TOP <= x) /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))).
{ intros Hp. pose proof (HDst2 Hp) as Hd.
  pose proof (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) acc
    (sq_p g + sq_n g) HAR Hd ltac:(lia)) as (A1 & _).
  pose proof (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) acc
    (sq_p g + sq_n g + acc - 1) HAR Hd ltac:(lia)) as (A2 & _).
  split; [lia|]. split; [lia|]. intros x Hx.
  exact (proj2 (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) acc x HAR Hd Hx)). }
(* the buffer does not meet sb_dec's own frame *)
assert (HQF2 : 0 < acc -> sq_p g + sq_n g + acc <= sq_F g pos \/ sq_F g pos + 64 <= sq_p g + sq_n g).
{ intros Hp. apply (sbB_apart (sq_p g + sq_n g) acc (sq_F g pos) (sq_F g pos + 64)); [lia|lia|].
  intros a Ha. exact (sbB_frame_dst g pos ly2 S2 mem2 md2 (sq_p g + sq_n g) acc a HAR Hfrs Hab Hni Hfa
    (HDst Hp) Ha). }
split.
- rewrite restrict_mkst_fx. unfold sbB_ss. apply pa_entry_st_ok_full.
  + unfold sbB_sr. apply regs_ok_rereg; [apply regs_ok_rereg; [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity |] | vm_compute; reflexivity |].
    * rewrite H14, (denot_lit_U (sbB_E regs2 g) (SOff 10 32)). f_equal.
      rewrite U_SOff, E10, unsigned_lit_small by lia. symmetry. apply zcanon_id. unfold M64. lia.
    * rewrite H15, (denot_lit_U (sbB_E regs2 g) (SLit kd)). f_equal.
      rewrite U_SLit. symmetry. apply zcanon_id. unfold M64. lia.
  + assert (Hk3 : kd = 1 \/ kd = 2 \/ kd = 3) by lia.
    assert (Ha4 : acc = 0 \/ acc = 1 \/ acc = 2 \/ acc = 3) by lia.
    destruct Hk3 as [-> | [-> | ->]]; destruct Ha4 as [-> | [-> | [-> | ->]]]; vm_compute; reflexivity.
  + unfold sbB_mem. apply Forall_app. split; [apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]|].
    * (* the struct sb *)
      unfold YP09.region_ok, sbB_rb.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 18%nat (sq_b g) E18) by lia.
      split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPb; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
      -- apply (chunk_ok_val SEGS _ _ (sq_b g) 0 8 (SOff 32 0) (sq_p g));
         [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
         rewrite Z.add_0_r. exact Vp.
      -- apply (chunk_ok_val SEGS _ _ (sq_b g) 8 8 (SOff 33 0) (sq_cap g));
         [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vcap].
      -- apply (chunk_ok_val SEGS _ _ (sq_b g) 16 8 (SOff 34 0) (sq_n g));
         [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vn].
      -- apply (chunk_ok_val SEGS _ _ (sq_b g) 24 4 (SOff 35 0) (sq_ov g));
         [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vov].
    * (* the digits in sb_dec's frame *)
      unfold YP09.region_ok, sbB_rd.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 10%nat (sq_F g pos) E10) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
      destruct (HDb j ltac:(lia)) as (HVj & HRj).
      apply (chunk_ok_val SEGS _ _ (sq_F g pos) (32 + Z.of_nat j) 1 (SOff (37 + j) 0) (nth j (rev (sq_D g)) 0));
      [cbn [sv_denot]; rewrite (ED j ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | zside | zside |].
      cbn [N.to_nat]. replace (sq_F g pos + (32 + Z.of_nat j)) with (sq_F g pos + 32 + Z.of_nat j) by lia.
      exact HVj.
    * (* the emitted digits *)
      destruct (Z.eqb_spec acc 0) as [->|Hne]; [apply Forall_nil|].
      apply Forall_cons; [|apply Forall_nil].
      destruct (HQF ltac:(lia)) as (Q1 & Q2 & _).
      unfold YP09.region_ok, sbB_rq.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      rewrite (VB 36%nat (sq_p g + sq_n g) E36) by lia.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply (HPq ltac:(lia)). lia.
  + apply pairwise_disjoint_of_extents.
    unfold sbB_mem, sbB_rb, sbB_rd, sbB_rq, extent_of_region.
    destruct (Z.eqb_spec acc 0) as [->|Hne].
    * cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 18%nat (sq_b g) E18) by lia. rewrite (VB 10%nat (sq_F g pos) E10) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    * destruct (HQF ltac:(lia)) as (Q1 & Q2 & _). pose proof (HQF2 ltac:(lia)) as Q3.
      pose proof (HDisj ltac:(lia)) as Q4.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 18%nat (sq_b g) E18) by lia. rewrite (VB 10%nat (sq_F g pos) E10) by lia.
      rewrite (VB 36%nat (sq_p g + sq_n g) E36) by lia.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + split; [|split; [exact I|]].
    * unfold sbB_facts, sbB_atoms. cbn [f_atoms].
      assert (HDIG : forall i m, (forall j, (i <= j < i + m)%nat -> (j < Z.to_nat kd)%nat) ->
        atoms_ok (sbB_E regs2 g) (map (fun j => ((37 + j)%nat, mkAF 0 255 0)) (seq i m))).
      { intros i m. revert i. induction m as [|m IH]; intros i Hi; cbn [seq map atoms_ok]; [exact I|].
        pose proof (Hi i ltac:(lia)) as Hik.
        split.
        - unfold afact_ok. cbn [af_lo af_hi af_al2].
          destruct (HDb i Hik) as (_ & HRj).
          rewrite (ED i ltac:(lia)), unsigned_lit_small by lia.
          rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia].
        - apply IH. intros j Hj. apply Hi. lia. }
      destruct (Z.eqb_spec acc 0) as [->|Hne].
      -- cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
         rewrite E10, E18, E21, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB; lia).
         change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
         repeat match goal with |- _ /\ _ => split end;
         try solve [lia | reflexivity | unfold SB; lia | apply HDIG; intros j Hj; lia].
      -- destruct (HQF ltac:(lia)) as (Q1 & Q2 & _).
         cbn [app atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
         rewrite E10, E18, E21, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB; lia).
         change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
         repeat match goal with |- _ /\ _ => split end;
         try solve [lia | reflexivity | unfold SB; lia | apply HDIG; intros j Hj; lia].
    * cbn [sbB_facts f_alias alias_ok]. split; [|exact I].
      cbn [sv_denot]. rewrite E32, E34, E36, !Z.add_0_r, !Z_to_bv_bv_unsigned. apply YI08.alu64_add_lit.
- unfold sh_ok, sbB_SH.
  assert (UB : U (sbB_E regs2 g) sbB_Bx = SHADOW_OFF).
  { unfold U, sbB_Bx. cbn [sv_denot]. rewrite E21, Z.add_0_r, Z_to_bv_bv_unsigned.
    rewrite unsigned_lit_small by (unfold SB; lia). reflexivity. }
  apply Forall_app. split; [apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]|].
  + (* the struct sb: the caller's machine stack has zero shadow *)
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (U18 : U (sbB_E regs2 g) (SOff 18 0) = sq_b g) by (apply (U_atom _ 18%nat); [exact E18 | lia]).
    rewrite UB, U18, Z.add_0_r. rewrite <- (aview_rd_of SEGS). split.
    * replace (32 - 0) with 32 by lia.
      apply (sbd_stack_zero B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_b g) HAR); lia.
    * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF. lia.
  + (* the digit array: the frame's shadow byte 4 is 04 *)
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (U10 : U (sbB_E regs2 g) (SOff 10 0) = sq_F g pos) by (apply (U_atom _ 10%nat); [exact E10 | lia]).
    rewrite UB, U10. split.
    * intros x Hx. exists 4.
      assert (Hdiv : x / 8 = sq_F g pos / 8 + 4)
        by (symmetry; apply Z.div_unique with (r := x - (sq_F g pos + 32)); lia).
      destruct (HFS 4%nat ltac:(cbn [length SBD_FRAME_SHADOW]; lia)) as (HV & HR4).
      cbn [nth SBD_FRAME_SHADOW] in HV, HR4. split.
      -- replace (shadow_of_addr SHADOW_OFF x) with (SB + sq_F g pos / 8 + Z.of_nat 4)
           by (unfold shadow_of_addr, SB, SHADOW_OFF; cbn [Z.of_nat]; lia).
         exact (sbB_rdof_of_vm _ _ _ HV ltac:(lia)).
      -- right. split; [|lia].
         assert (Hm : x mod 8 = x - 8 * (x / 8)) by lia.
         assert (HFm : sq_F g pos = 8 * (sq_F g pos / 8)) by lia.
         lia.
    * intros a Ha. cbn [Z.min Z.max] in Ha. unfold SHADOW_OFF in *. lia.
  + (* the emitted digits *)
    destruct (Z.eqb_spec acc 0) as [->|Hne]; [apply Forall_nil|].
    apply Forall_cons; [|apply Forall_nil].
    destruct (HQF ltac:(lia)) as (Q1 & Q2 & Q3).
    unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    assert (U36 : U (sbB_E regs2 g) (SOff 36 0) = sq_p g + sq_n g) by (apply (U_atom _ 36%nat); [exact E36 | lia]).
    rewrite UB, U36, Z.add_0_r. rewrite <- (aview_rd_of SEGS). split.
    * replace (acc - 0) with acc by lia. exact (HRA ltac:(lia)).
    * intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.min_l, Z.max_r in Ha by lia.
      exact (proj2 (Q3 a ltac:(lia))).
Qed.

(* ---- the write rights and the write set of the segment -------------------------------------------- *)
Lemma sbB_awr_mono : forall STK sp0 FP bl0 blc blc' ly ly' own own' a,
  blc' = blc -> (forall c p, frame_addr ly' c p = frame_addr ly c p) ->
  (forall x, In x own -> In x own') ->
  awr_byte STK sp0 FP bl0 blc ly own a -> awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
intros STK sp0 FP bl0 blc blc' ly ly' own own' a Hb Hfa Ho H. subst blc'.
destruct H as [H | [H | [H | (cid & p' & Hin & Hr)]]];
[left; exact H | right; left; exact H | right; right; left; exact H |].
right; right; right. exists cid, p'. split; [exact (Ho _ Hin)|].
rewrite (Hfa cid p'). exact Hr.
Qed.
Lemma sbB_awr_of : forall (E : env) (rs : smem) (kd acc bb qq : Z) STK sp0 FP bl0 blc ly own,
  skeleton rs = skeleton (sbB_mem kd acc) ->
  bv_unsigned (ew E 18%nat) = bb -> bv_unsigned (ew E 36%nat) = qq ->
  (forall a, bb + 16 <= a < bb + 28 -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  (forall a, qq <= a < qq + acc -> awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E rs STK sp0 FP bl0 blc ly own.
Proof.
intros E rs kd acc bb qq STK sp0 FP bl0 blc ly own Hsk H18 H36 Hb Hq a Hin.
apply (in_wrange_skeleton E rs (sbB_mem kd acc) a Hsk) in Hin.
destruct Hin as (r & Hr & Hrr). unfold sbB_mem in Hr. apply in_app_or in Hr.
destruct Hr as [[<- | [<- | []]] | Hr].
- unfold sbB_rb in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
  rewrite H18 in Hrr. apply Hb. lia.
- unfold sbB_rd in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr. lia.
- destruct (acc =? 0); [destruct Hr | destruct Hr as [<- | []]].
  unfold sbB_rq in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
  rewrite H36 in Hrr. apply Hq. lia.
Qed.
(* in_wrange comes first, so that E and rs are fixed before the computed premise is elaborated. *)
Lemma sbB_wrange_of : forall (E : env) (rs : smem) (kd acc bb qq : Z) a,
  in_wrange E rs a ->
  skeleton rs = skeleton (sbB_mem kd acc) ->
  bv_unsigned (ew E 18%nat) = bb -> bv_unsigned (ew E 36%nat) = qq ->
  (bb + 16 <= a < bb + 28) \/ (qq <= a < qq + acc).
Proof.
intros E rs kd acc bb qq a Hin Hsk H18 H36.
apply (in_wrange_skeleton E rs (sbB_mem kd acc) a Hsk) in Hin.
destruct Hin as (r & Hr & Hrr). unfold sbB_mem in Hr. apply in_app_or in Hr.
destruct Hr as [[<- | [<- | []]] | Hr].
- unfold sbB_rb in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
  rewrite H18 in Hrr. left. lia.
- unfold sbB_rd in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr. lia.
- destruct (acc =? 0); [destruct Hr | destruct Hr as [<- | []]].
  unfold sbB_rq in Hrr. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrr.
  rewrite H36 in Hrr. right. lia.
Qed.

(* ---- what the runs keep ---------------------------------------------------------------------------- *)
Lemma sbB_eq_trans : forall (W : world SEGS) (Wr : Z -> Prop) (E : env) (rs : smem) m0 m1 m2,
  (forall x : word, ~ Wr (bv_unsigned x) -> rd W m1 x = rd W m0 x) ->
  frame_of E rs (rd W m1) (rd W m2) ->
  (forall a, in_wrange E rs a -> Wr a) ->
  (forall x : word, ~ Wr (bv_unsigned x) -> rd W m2 x = rd W m0 x).
Proof.
intros W Wr E rs m0 m1 m2 H0 H1 H2 x Hx.
rewrite (H1 x (fun Hin => Hx (H2 _ Hin))). apply H0, Hx.
Qed.
(* fuzz_disco's sbd_kept_run (projects/libreac/fuzz_disco/proofs/lib/A/Prog/SbDecLib.v:94) over IdentCJ's tcj_kept. *)
Lemma sbB_kept_run : forall lyc Sc (W : world SEGS) memc mem1 mem2 mdc sp (Er Wr : Z -> Prop),
  AR SEGS B lyc Sc W memc mdc ->
  tcj_kept B SB_DEC_STK lyc Sc W memc W mem1 sp Er ->
  (forall x : word, ~ Wr (bv_unsigned x) -> rd W mem2 x = rd W mem1 x) ->
  mem_grows (rd W mem1) (rd W mem2) ->
  (forall a, Wr a -> Er a /\ ~ in_img SEGS a) ->
  tcj_kept B SB_DEC_STK lyc Sc W memc W mem2 sp Er.
Proof.
intros lyc Sc W memc mem1 mem2 mdc sp Er Wr HAR (K1 & K2 & K3 & K4 & K5 & K6) Hfr Hgr Hwr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EQ : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem1 a).
{ intros a Ha Hn. apply aview_eq_of. apply Hfr. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by lia. exact Hn. }
split; [|split; [|split; [|split; [|split]]]].
- intros a Ha Hs He.
  rewrite (EQ a ltac:(lia) ltac:(intros Hw; exact (He (proj1 (Hwr a Hw))))). exact (K1 a Ha Hs He).
- intros b0 m i Hin Hi He.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b0 m HAR Hin) as (_ & H4096 & Hbc & _).
  rewrite (EQ (b0 + i) ltac:(lia) ltac:(intros Hw; exact (He (proj1 (Hwr _ Hw))))).
  exact (K2 b0 m i Hin Hi He).
- intros a Himg Hno Herr. pose proof (pa_segs_low a Himg) as Hlo. unfold kLowMemEnd in Hlo.
  rewrite (EQ a ltac:(lia) ltac:(intros Hw; exact (proj2 (Hwr a Hw) Himg))). exact (K3 a Himg Hno Herr).
- intros cid pos a Hin Hr He.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (H4096 & Hfc & _).
  pose proof (fs_frame_bytes_nonneg cid) as Hb0.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as S1.
  pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as S2.
  pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hb0) as S3.
  assert (Ha : 0 <= a < 2 ^ 64).
  { destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr;
    unfold kLowMemEnd, kHighShadowEnd in *; lia. }
  rewrite (EQ a Ha ltac:(intros Hw; exact (He (proj1 (Hwr a Hw))))). exact (K4 cid pos a Hin Hr He).
- intros a Ha Hs Hp. eapply apresent_grows; [exact Hgr | exact (K5 a Ha Hs Hp)].
- intros a Ha. eapply apresent_grows; [exact Hgr | exact (K6 a Ha)].
Qed.
Lemma sbB_vm_keep : forall (W : world SEGS) m1 m2 (Wr : Z -> Prop) a n v,
  (forall x : word, ~ Wr (bv_unsigned x) -> rd W m2 x = rd W m1 x) ->
  (forall k, 0 <= k < Z.of_nat n -> ~ Wr (a + k)) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem SEGS (rd W m1) a n v -> val_mem SEGS (rd W m2) a n v.
Proof.
intros W m1 m2 Wr a n v Hfr Hout Ha0 Han H k Hk. specialize (H k Hk). unfold mbyte in *.
rewrite (Hfr (Z_to_bv 64 (a + Z.of_nat k)) ltac:(rewrite unsigned_lit_small by lia; apply Hout; lia)).
exact H.
Qed.
Lemma sbB_rdw_keep : forall (W : world SEGS) m1 m2 (Wr : Z -> Prop) a v,
  (forall x : word, ~ Wr (bv_unsigned x) -> rd W m2 x = rd W m1 x) ->
  (forall k, 0 <= k < 8 -> ~ Wr (a + k)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) m1) a = Some v -> rdword (aview SEGS (w_H W) m2) a = Some v.
Proof.
intros W m1 m2 Wr a v Hfr Hout Ha0 Han H.
assert (EQ : forall x, a <= x < a + 8 -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x).
{ intros x Hx. apply aview_eq_of. apply Hfr. rewrite unsigned_lit_small by lia.
  replace x with (a + (x - a)) by lia. apply Hout. lia. }
unfold rdword in *.
rewrite (EQ a ltac:(lia)), (EQ (a + 1) ltac:(lia)), (EQ (a + 2) ltac:(lia)), (EQ (a + 3) ltac:(lia)),
  (EQ (a + 4) ltac:(lia)), (EQ (a + 5) ltac:(lia)), (EQ (a + 6) ltac:(lia)), (EQ (a + 7) ltac:(lia)).
exact H.
Qed.
(* Every byte of the buffer is present in the state the segment starts from. *)
Lemma sbB_dst_present : forall ly2 S2 (W : world SEGS) mem2 md2 q n a,
  AR SEGS B ly2 S2 W mem2 md2 -> tdst_ok B ly2 S2 q n -> q <= a < q + n ->
  apresent (w_H W) mem2 a.
Proof.
intros ly2 S2 W mem2 md2 q n a HAR Hd Ha.
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & p' & Hin & Hr)].
- destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  exact (proj1 (Hpres a Hr)).
- destruct (al_frames _ _ LAWS _ _ _ _ _ cid p' HAR Hin) as (_ & _ & Hpres & _).
  unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. exact (proj1 (Hpres a Hr)).
Qed.
(* The bytes a region's one-byte chunks hold. *)
Lemma sbB_garr_of : forall (E : env) m (r : YP09.region) (q : Z) (l : list Z),
  YP09.region_ok SEGS E m r -> base_val E (YP09.r_base r) = q ->
  (forall j, (j < length l)%nat -> exists e, In (YP09.mkChunk (Z.of_nat j) (CVal 1 e)) (YP09.r_chunks r) /\
     sv_denot E e = Z_to_bv 64 (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 SEGS m q l.
Proof.
intros E m r q l Hr Hq Hl j Hj. destruct (Hl j Hj) as (e & Hin & He & Hv).
pose proof (sbB_vm_of_chunk E m r (Z.of_nat j) 1 e (nth j l 0) Hr Hin He ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
rewrite Hq in HV. cbn [N.to_nat] in HV. split; [exact HV | exact Hv].
Qed.

(* ---- reading the exit facts off the final symbolic state ------------------------------------------- *)
Lemma sbB_ew_eq : forall (E E' : env) n z, ew E' n = z -> ew E n = ew E' n -> ew E n = z.
Proof. intros E E' n z H1 H2. rewrite H2. exact H1. Qed.
Lemma sbB_ewu_eq : forall (E E' : env) n z, bv_unsigned (ew E' n) = z -> ew E n = ew E' n ->
  bv_unsigned (ew E n) = z.
Proof. intros E E' n z H1 H2. rewrite H2. exact H1. Qed.
Lemma sbB_vm_at : forall (E : env) m (rs : smem) (nb : nat) (off : Z) (w : N) (e : sv) (z bb aa : Z),
  Forall (YP09.region_ok SEGS E m) rs ->
  YP09.r_base (rgn_of rs nb) = Some nb ->
  chk_of (YP09.r_chunks (rgn_of rs nb)) off = Some (YP09.mkChunk off (CVal w e)) ->
  bv_unsigned (ew E nb) = bb -> aa = bb + off ->
  sv_denot E e = Z_to_bv 64 z -> 0 <= z < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS m aa (N.to_nat w) z.
Proof.
intros E m rs nb off w e z bb aa HR Hb Hc Hbb Haa He Hz Hw.
pose proof (proj1 (Forall_forall _ _) HR _ (rgn_of_In rs nb Hb)) as Hr.
pose proof (sbB_vm_of_chunk E m (rgn_of rs nb) off w e z Hr (chk_of_In _ _ _ Hc) He Hz Hw) as HV.
rewrite Hb in HV. cbn [base_val] in HV. rewrite Hbb in HV. rewrite Haa. exact HV.
Qed.
Lemma sbB_garr_at : forall (E : env) m (rs : smem) (nb : nat) (q : Z) (l : list Z),
  Forall (YP09.region_ok SEGS E m) rs -> YP09.r_base (rgn_of rs nb) = Some nb ->
  bv_unsigned (ew E nb) = q ->
  (forall j, (j < length l)%nat -> exists e,
     chk_of (YP09.r_chunks (rgn_of rs nb)) (Z.of_nat j) = Some (YP09.mkChunk (Z.of_nat j) (CVal 1 e)) /\
     sv_denot E e = Z_to_bv 64 (nth j l 0) /\ 0 <= nth j l 0 < 256) ->
  garr8 SEGS m q l.
Proof.
intros E m rs nb q l HR Hb Hq Hl j Hj. destruct (Hl j Hj) as (e & Hc & He & Hv).
pose proof (proj1 (Forall_forall _ _) HR _ (rgn_of_In rs nb Hb)) as Hr.
pose proof (sbB_vm_of_chunk E m (rgn_of rs nb) (Z.of_nat j) 1 e (nth j l 0) Hr (chk_of_In _ _ _ Hc) He
  ltac:(cbn [Z.of_N N.to_nat Z.mul]; lia) ltac:(cbn [Z.of_N]; lia)) as HV.
rewrite Hb in HV. cbn [base_val N.to_nat] in HV. rewrite Hq in HV. split; [exact HV | exact Hv].
Qed.

(* ---- the common part of the boundary, moved to the state the segment ends in ----------------------- *)
Lemma sbB_common_keep : forall (g : sbd_ctx) pos (regs2 rf : bvmap 5 word)
  (mem2 mf : word -> option byte) (acc : Z),
  sbd_common g pos regs2 mem2 ->
  (forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5);
     (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5);
     (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r) ->
  (forall x : word, ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) acc (bv_unsigned x) ->
     rd (sq_W g) mf x = rd (sq_W g) mem2 x) ->
  (forall a, sq_sp g - 112 <= a < sq_sp g -> ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) acc a) ->
  (forall a, sq_F g pos <= a < sq_F g pos + 64 -> ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) acc a) ->
  112 <= sq_sp g -> sq_sp g <= 2 ^ 47 -> 0 <= sq_F g pos -> sq_F g pos + 64 <= 2 ^ 47 ->
  sbd_common g pos rf mf.
Proof.
intros g pos regs2 rf mem2 mf acc HC RK HEQ HAway HFaway Hs1 Hs2 HF1 HF2.
destruct HC as (R8 & Rsp1 & R3 & R4 & R24 & R25 & R26 & R27 & R10 & R16 & R17 & R18 & R21 &
  V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & Vflag).
split; [rewrite (RK (8%bv : bv 5) ltac:(cbn [In]; tauto)); exact R8|].
split; [destruct Rsp1 as (sp1v & Q1 & Q2 & Q3 & Q4); exists sp1v;
        split; [rewrite (RK (2%bv : bv 5) ltac:(cbn [In]; tauto)); exact Q1|];
        split; [rewrite (RK (9%bv : bv 5) ltac:(cbn [In]; tauto)); exact Q2|];
        split; [exact Q3 | exact Q4]|].
split; [rewrite (RK (3%bv : bv 5) ltac:(cbn [In]; tauto)); exact R3|].
split; [rewrite (RK (4%bv : bv 5) ltac:(cbn [In]; tauto)); exact R4|].
split; [rewrite (RK (24%bv : bv 5) ltac:(cbn [In]; tauto)); exact R24|].
split; [rewrite (RK (25%bv : bv 5) ltac:(cbn [In]; tauto)); exact R25|].
split; [rewrite (RK (26%bv : bv 5) ltac:(cbn [In]; tauto)); exact R26|].
split; [rewrite (RK (27%bv : bv 5) ltac:(cbn [In]; tauto)); exact R27|].
split; [rewrite (RK (10%bv : bv 5) ltac:(cbn [In]; tauto)); exact R10|].
split; [rewrite (RK (16%bv : bv 5) ltac:(cbn [In]; tauto)); exact R16|].
split; [rewrite (RK (17%bv : bv 5) ltac:(cbn [In]; tauto)); exact R17|].
split; [rewrite (RK (18%bv : bv 5) ltac:(cbn [In]; tauto)); exact R18|].
split; [rewrite (RK (21%bv : bv 5) ltac:(cbn [In]; tauto)); exact R21|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 8) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V1)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 16) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V2)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 24) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V3)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 32) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V4)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 40) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V5)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 48) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V6)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 56) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V7)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 64) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V8)|].
split; [apply (sbB_vm_keep (sq_W g) mem2 mf _ (sq_sp g - 72) 8%nat _ HEQ
  ltac:(intros kk Hkk; apply HAway; lia) ltac:(lia) ltac:(lia) V9)|].
apply (sbB_rdw_keep (sq_W g) mem2 mf _ (sq_F g pos + fs_frame_bytes 0 - 8) _ HEQ
  ltac:(intros kk Hkk; apply HFaway; change (fs_frame_bytes 0) with 64; lia)
  ltac:(change (fs_frame_bytes 0) with 64; lia)
  ltac:(change (fs_frame_bytes 0) with 64; lia) Vflag).
Qed.
Ltac sbB_agr := rewrite ?ew_ewset_lo by lia; reflexivity.
Ltac sbB_dig1 EF EB RS NB J AT ED :=
  let c := eval vm_compute in (chk_of (YP09.r_chunks (rgn_of RS NB)) (Z.of_nat J)) in
  lazymatch c with
  | Some (YP09.mkChunk _ (CVal 1 ?e0)) =>
    exists e0; split; [vm_compute; reflexivity|];
    split;
    [ cbn [sv_denot]; rewrite (sbB_ew_eq EF EB AT _ ED ltac:(sbB_agr));
      rewrite Z.add_0_r, Z_to_bv_bv_unsigned; cbn [nth firstn]; reflexivity
    | cbn [nth firstn]; lia ]
  end.

(* ---- the loop's arithmetic -------------------------------------------------------------------------
   acc = min kd room; turn i has room exactly while i < acc (0x83658 bgeu n+i+1, cap). *)
Lemma sbB_room : forall cap n, 0 <= sb_dec_c.sb_dec_room cap n /\
  (0 < sb_dec_c.sb_dec_room cap n -> cap = n + 1 + sb_dec_c.sb_dec_room cap n) /\
  (sb_dec_c.sb_dec_room cap n = 0 -> cap <= n + 1).
Proof.
intros cap n. unfold sb_dec_c.sb_dec_room. destruct (Z.leb_spec (n + 1) cap) as [H|H]; repeat split; lia.
Qed.

(* ---- the walk ---------------------------------------------------------------------------------------- *)
Theorem seg_sbd_B_holds : seg_sbd_B B.
Proof.
unfold seg_sbd_B. intros g pos W3 c3 Hpre HAe.
destruct HAe as (HW3 & ly2 & S2 & regs2 & mem2 & md2 & Hc3 & HJ & HKA & HabS & Hni & HCom & HPa).
subst W3. subst c3.
pose proof Hpre as (HJ0 & Hra & Hra4 & Hgp & Htp & Hal16 & Hsp1 & Hsp2 & Hb10 & Hv11 & Hmd12 & Hv & Hmd
  & Hb8 & Hb0 & Hb63 & Hbsp & Hrec & Vp0 & Vcap0 & Vn0 & Vov0 & Rp & Rcap & Rn0 & Rn4 & Rov & HWRb & HQ
  & Hfrlen & Hev & Hlive).
pose proof HJ as (HARc & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & _ & _ & _ & _ & _ & Hpres2 & Hstatic2 & _ & _).
pose proof HJ0 as (HAR0 & Hly0 & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & Hpres0 & Hstatic0 & _ & _).
pose proof Hstatic0 as (Hsp0al & HstkN & Hcl0 & Hslo0 & Hshi0 & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : SB_DEC_STK = 4208) by reflexivity.
pose proof HCom as (R8 & Rsp1 & R3 & R4 & R24 & R25 & R26 & R27 & R10 & R16 & R17 & R18 & R21 &
  V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & Vflag).
destruct HPa as (R22 & R23 & R14 & R15 & HDg & HFSg & P7 & P8 & P9 & P10 & P11).
(* the layouts of the cut state and of the call state agree where the walk looks *)
assert (Hfrs : frames S2 = (0, pos) :: frames (sq_Sc g)) by (rewrite Hfrs2, Hfrs0; reflexivity).
assert (Hfa : forall cid p', frame_addr ly2 cid p' = frame_addr (sq_lyc g) cid p').
{ intros cid p'. unfold frame_addr.
  destruct Hly2 as (_ & _ & _ & _ & _ & EF2 & _). destruct Hly0 as (_ & _ & _ & _ & _ & EF0 & _).
  rewrite EF2, EF0. reflexivity. }
assert (Hslo : ly_stk_lo ly2 = ly_stk_lo (sq_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Hshi : ly_stk_hi ly2 = ly_stk_hi (sq_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & _).
  destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Hcl : alloc_ceiling <= ly_stk_lo (sq_lyc g)).
{ destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _). rewrite E2. exact Hcl0. }
assert (Hs47 : ly_stk_hi (sq_lyc g) <= 2 ^ 47).
{ destruct Hly0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E2 & _). rewrite E2. exact H47. }
pose proof Hrec as [Hblo Hbhi].
assert (HbL : alloc_ceiling <= sq_b g) by lia.
assert (HbH : sq_b g + 32 <= 2 ^ 47) by lia.
(* sb_dec's own frame *)
assert (HinS2 : In (0, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
assert (HFeq : frame_addr ly2 0 pos = sq_F g pos) by (unfold sq_F; apply Hfa).
destruct (frames_bounds SEGS B LAWS ly2 S2 (sq_W g) mem2 md2 0 pos HARc HinS2) as (HF0 & HFceil & _).
rewrite HFeq in HF0, HFceil. change (fs_frame_bytes 0) with 64 in HF0, HFceil.
(* the loop's arithmetic *)
destruct (sbB_room (sq_cap g) (sq_n g)) as (Hroom0 & HroomP & HroomZ).
assert (Hlsd : 1 <= Z.of_nat (length (sb_dec_c.sb_dec_lsd (sq_v g) 3)) <= 3).
{ cbn [sb_dec_c.sb_dec_lsd]. destruct (sq_v g <? 10); [cbn [length]; lia|].
  destruct (sq_v g / 10 <? 10); [cbn [length]; lia|]. destruct (sq_v g / 10 / 10 <? 10); cbn [length]; lia. }
assert (HKD : 1 <= sq_kd g <= 3).
{ unfold sq_kd, sq_D, sb_dec_c.sb_dec_D. rewrite length_rev.
  destruct (Z.ltb_spec (Z.of_nat (length (sb_dec_c.sb_dec_lsd (sq_v g) 3))) (sq_md g)) as [Hc|Hc];
  [rewrite length_app; cbn [length]; lia | lia]. }
assert (HACC : sq_acc g = Z.min (sq_kd g) (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g))) by reflexivity.
assert (HAcc3 : 0 <= sq_acc g <= sq_kd g) by lia.
(* the premises of the call that mention the buffer *)
assert (HDstA : 0 < sq_acc g -> tdst_ok B (sq_lyc g) (sq_Sc g) (sq_p g + sq_n g) (sq_acc g)).
{ intros Hp. destruct (HQ ltac:(lia)) as (_ & _ & Qc & _). exact Qc. }
assert (HDst2 : 0 < sq_acc g -> tdst_ok B ly2 S2 (sq_p g + sq_n g) (sq_acc g)).
{ intros Hp a Ha. destruct (HDstA Hp a Ha) as [(bb & m & Hbin & Hbr) | (cid & p' & Hfin & Hr)].
  - left. exists bb, m. split; [rewrite HabS; exact Hbin | exact Hbr].
  - right. exists cid, p'. split; [rewrite Hfrs; right; exact Hfin|].
    unfold in_zr, frame_rng in Hr |- *. cbn [fst snd] in Hr |- *. rewrite (Hfa cid p'). exact Hr. }
assert (HQF : 0 < sq_acc g -> 4096 <= sq_p g + sq_n g /\ sq_p g + sq_n g + sq_acc g <= alloc_ceiling /\
  (forall x, sq_p g + sq_n g <= x < sq_p g + sq_n g + sq_acc g ->
     (x < IMG_LO \/ IMG_TOP <= x) /\ ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416))).
{ intros Hp. pose proof (HDst2 Hp) as Hd.
  pose proof (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) (sq_acc g)
    (sq_p g + sq_n g) HARc Hd ltac:(lia)) as (A1 & _).
  pose proof (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) (sq_acc g)
    (sq_p g + sq_n g + sq_acc g - 1) HARc Hd ltac:(lia)) as (A2 & _).
  split; [lia|]. split; [lia|]. intros x Hx.
  exact (proj2 (sbd_dst_byte B LAWS ly2 S2 (sq_W g) mem2 md2 (sq_p g + sq_n g) (sq_acc g) x HARc Hd Hx)). }
assert (HDisja : 0 < sq_acc g -> sq_p g + sq_n g + sq_acc g <= sq_b g \/ sq_b g + 28 <= sq_p g + sq_n g).
{ intros Hp. destruct (HQ ltac:(lia)) as (_ & _ & _ & _ & _ & Qf & _). exact Qf. }
assert (HQsp : 0 < sq_acc g -> sq_p g + sq_n g + sq_acc g <= spZ (sq_regs g) - SB_DEC_STK \/
  spZ (sq_regs g) <= sq_p g + sq_n g).
{ intros Hp. destruct (HQ ltac:(lia)) as (_ & _ & _ & _ & _ & _ & Qg). exact Qg. }
assert (HPqa : 0 < sq_acc g -> forall a, sq_p g + sq_n g <= a < sq_p g + sq_n g + sq_acc g ->
  apresent (w_H (sq_W g)) mem2 a)
  by (intros Hp a Ha; exact (sbB_dst_present ly2 S2 (sq_W g) mem2 md2 _ _ a HARc (HDst2 Hp) Ha)).
assert (HPb : forall a, sq_b g + 16 <= a < sq_b g + 28 -> apresent (w_H (sq_W g)) mem2 a).
{ intros a Ha. destruct HKA as (_ & _ & _ & _ & K5 & _).
  apply (K5 a ltac:(clear - Ha HbL HbH C1; lia) ltac:(clear - Ha Hbsp HSTK; unfold sq_sp; lia)).
  exact (proj1 (proj2 (HWRb a ltac:(clear - Ha; lia)))). }
(* the write rights, moved to the state the segment runs in *)
assert (HWb : forall a, sq_b g + 16 <= a < sq_b g + 28 ->
  awr_byte (sq_STK g) (sq_sp0 g) (sq_FP g) (ablocks B (sq_ly g) (sq_S g)) (ablocks B ly2 S2) ly2
    ((0, pos) :: sq_own g) a).
{ intros a Ha. apply (sbB_awr_mono _ _ _ _ (ablocks B (sq_lyc g) (sq_Sc g)) _ (sq_lyc g) _ (sq_own g));
  [exact HabS | exact Hfa | intros x Hx; right; exact Hx | exact (proj1 (HWRb a ltac:(lia)))]. }
assert (HWqA : 0 < sq_acc g -> forall a, sq_p g + sq_n g <= a < sq_p g + sq_n g + sq_acc g ->
  awr_byte (sq_STK g) (sq_sp0 g) (sq_FP g) (ablocks B (sq_ly g) (sq_S g)) (ablocks B ly2 S2) ly2
    ((0, pos) :: sq_own g) a).
{ intros Hp a Ha. destruct (HQ ltac:(lia)) as (_ & _ & _ & _ & Qe & _).
  apply (sbB_awr_mono _ _ _ _ (ablocks B (sq_lyc g) (sq_Sc g)) _ (sq_lyc g) _ (sq_own g));
  [exact HabS | exact Hfa | intros x Hx; right; exact Hx | exact (proj1 (Qe a Ha))]. }
(* the write set never meets the image *)
assert (HErImg : forall a, tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g) a -> ~ in_img SEGS a).
{ intros a [Ha | Ha] Himg; pose proof (pa_img_range a Himg) as Hr; [lia|].
  destruct (HQF ltac:(lia)) as (_ & _ & Q3). destruct (Q3 a Ha) as (Hq & _). lia. }
(* the environment of the walk *)
assert (HEI0 : img_env VAL A_LIM (sbB_E regs2 g)) by (unfold sbB_E; apply Eimg_env).
assert (ERb : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (sbB_E regs2 g) n = getr regs2 r).
{ intros n r Hn. unfold sbB_E. rewrite Eimg_low.
  - apply ew_Ereg_nat. exact Hn.
  - pose proof (bv_unsigned_in_range 5 r) as Qr. change (bv_modulus 5) with 32 in Qr. unfold A_TEXT. lia. }
assert (EXb : forall j, (j < 8)%nat -> ew (sbB_E regs2 g) (32 + j) = Z_to_bv 64 (nth j (sbB_vals g) 0)).
{ intros j Hj. unfold sbB_E. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. exact (map_nth (Z_to_bv 64) (sbB_vals g) 0 j). }
pose proof (ERb 18%nat 18%bv eq_refl) as E18b. rewrite R18 in E18b.
pose proof (EXb 1%nat ltac:(lia)) as E33b. pose proof (EXb 2%nat ltac:(lia)) as E34b.
pose proof (EXb 0%nat ltac:(lia)) as E32b. pose proof (EXb 3%nat ltac:(lia)) as E35b.
pose proof (EXb 4%nat ltac:(lia)) as E36b.
cbn [nth sbB_vals Nat.add] in E32b, E33b, E34b, E35b, E36b.
assert (EDb : forall j, (j < 3)%nat -> ew (sbB_E regs2 g) (37 + j) = Z_to_bv 64 (nth j (rev (sq_D g)) 0)).
{ intros j Hj. replace (37 + j)%nat with (32 + (5 + j))%nat by lia.
  rewrite (EXb (5 + j)%nat ltac:(lia)). f_equal.
  destruct j as [|[|[|j]]]; cbn [nth sbB_vals]; [reflexivity|reflexivity|reflexivity|lia]. }
assert (E18u : bv_unsigned (ew (sbB_E regs2 g) 18%nat) = sq_b g)
  by (rewrite E18b; apply unsigned_lit_small; lia).
set (qv := bv_unsigned (ew (sbB_E regs2 g) 36%nat)).
assert (Hqv : 0 < sq_acc g -> qv = sq_p g + sq_n g).
{ intros Hp. destruct (HQF Hp) as (Q1 & Q2 & _). unfold qv. rewrite E36b.
  apply unsigned_lit_small. lia. }
assert (HWq : forall a, qv <= a < qv + sq_acc g ->
  awr_byte (sq_STK g) (sq_sp0 g) (sq_FP g) (ablocks B (sq_ly g) (sq_S g)) (ablocks B ly2 S2) ly2
    ((0, pos) :: sq_own g) a).
{ intros a Ha. destruct (Z_le_gt_dec (sq_acc g) 0) as [Hz|Hz]; [lia|].
  rewrite (Hqv ltac:(lia)) in Ha. exact (HWqA ltac:(lia) a Ha). }
(* what the segment has kept so far: nothing has run yet *)
assert (HEQ : forall x : word, ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g) (bv_unsigned x) ->
  rd (sq_W g) mem2 x = rd (sq_W g) mem2 x) by (intros; reflexivity).
assert (HGR : mem_grows (rd (sq_W g) mem2) (rd (sq_W g) mem2)) by apply mem_grows_refl.
assert (HEW : forall n, (n < 40)%nat -> ew (sbB_E regs2 g) n = ew (sbB_E regs2 g) n) by (intros; reflexivity).
(* the stack window and sb_dec's own frame hold none of the written bytes *)
assert (HAway : forall a, spZ (sq_regs g) - 112 <= a < spZ (sq_regs g) ->
  ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g) a).
{ intros a Ha [Hx | Hx]; [clear - Ha Hx Hbsp HSTK; lia|].
  destruct (Z_le_gt_dec (sq_acc g) 0) as [Hz|Hz]; [clear - Hx Hz; lia|].
  pose proof (HQsp ltac:(clear - Hz; lia)) as Hq. clear - Ha Hx Hq HSTK; lia. }
assert (HFaway : forall a, sq_F g pos <= a < sq_F g pos + 64 ->
  ~ tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) (sq_acc g) a).
{ intros a Ha [Hx | Hx]; [clear - Ha Hx HFceil HbL; lia|].
  destruct (Z_le_gt_dec (sq_acc g) 0) as [Hz|Hz]; [clear - Hx Hz; lia|].
  exact (sbB_frame_dst g pos ly2 S2 mem2 md2 (sq_p g + sq_n g) (sq_acc g) a HARc Hfrs HabS Hni Hfa
    (HDstA ltac:(lia)) Hx Ha). }
(* bounds of the entry sp and of sb_dec's frame *)
assert (HspB : 112 <= sq_sp g /\ sq_sp g <= 2 ^ 47)
  by (unfold sq_sp; clear - Hsp1 Hsp2 Hslo0 Hcl0 Hshi0 H47 HSTK C1; lia).
assert (HFB : 0 <= sq_F g pos /\ sq_F g pos + 64 <= 2 ^ 47)
  by (clear - HF0 HFceil Hcl Hs47 C1 Hblo Hbhi; lia).
(* the entry state of the segment *)
destruct (sbB_entry g pos ly2 S2 regs2 mem2 md2 (sq_kd g) (sq_acc g) HKD HAcc3 eq_refl HARc Hfrs HabS Hni
  Hfa Hslo Hshi Hcl Hs47 Hrec Hb8 Rp Rcap Rn0 Rn4 Rov HPb HDstA P11 HDisja HPqa R10 R14 R15 R18 R21
  P7 P8 P9 P10 HDg HFSg) as (HS & SHOK).
unfold cfg_at.
replace (A_sb_dec + SBD_A_END) with (BASE + (AF_sb_dec + SBD_A_END)) by (unfold A_sb_dec; lia).
change (w64 (BASE + (AF_sb_dec + SBD_A_END))) with (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_A_END))).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + (AF_sb_dec + SBD_A_END))) mem2 (seg_rom SEGS))) in HJ.
assert (HK3 : sq_kd g = 1 \/ sq_kd g = 2 \/ sq_kd g = 3) by (clear - HKD; lia).
assert (HA4 : sq_acc g = 0 \/ sq_acc g = 1 \/ sq_acc g = 2 \/ sq_acc g = 3) by (clear - HKD HAcc3; lia).
destruct HK3 as [HK | [HK | HK]]; destruct HA4 as [HA | [HA | [HA | HA]]];
try (exfalso; clear - HK HA HAcc3; lia).
+ (* kd = 1, acc = 0 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 1) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 1 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 1 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 1 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 1 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 0) with 0%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 0 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 0) (sq_n g + 0)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      cbn [firstn Z.to_nat]; apply garr8_nil
    end
  end.
+ (* kd = 1, acc = 1 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = sq_ov g)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 1) as [Hlt|Hge];
        [exfalso; clear - HACC Hlt; lia | reflexivity]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 1 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 1 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 1 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 1 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 1) with 1%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 1 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 1) (sq_n g + 1)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SOff 35 0) (sq_ov g)
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 35%nat _ E35b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rov; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|j]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 37%nat ED0 | exfalso; clear - Hj; lia ]
    end
  end.
+ (* kd = 2, acc = 0 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 2) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 0) with 0%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 0 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 0) (sq_n g + 0)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      cbn [firstn Z.to_nat]; apply garr8_nil
    end
  end.
+ (* kd = 2, acc = 1 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 2) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 1) with 1%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 1 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 1) (sq_n g + 1)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|j]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 38%nat ED1 | exfalso; clear - Hj; lia ]
    end
  end.
+ (* kd = 2, acc = 2 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = sq_ov g)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 2) as [Hlt|Hge];
        [exfalso; clear - HACC Hlt; lia | reflexivity]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 2 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 2 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 2) with 2%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 2 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 2) (sq_n g + 2)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SOff 35 0) (sq_ov g)
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 35%nat _ E35b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rov; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0; d1] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|[|j]]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 38%nat ED1 | sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 1%nat 37%nat ED0 | exfalso; clear - Hj; lia ]
    end
  end.
+ (* kd = 3, acc = 0 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 3) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d2 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  pose proof (proj2 (HDg 2%nat ltac:(cbn [length rev app]; clear; lia))) as HR2. cbn [rev app nth] in HR2.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 0 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 0 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 0) with 0%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 0) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 0 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 0) (sq_n g + 0)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      cbn [firstn Z.to_nat]; apply garr8_nil
    end
  end.
+ (* kd = 3, acc = 1 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 3) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d2 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  pose proof (proj2 (HDg 2%nat ltac:(cbn [length rev app]; clear; lia))) as HR2. cbn [rev app nth] in HR2.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 1 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 1 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 1) with 1%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 1) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 1 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 1) (sq_n g + 1)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|j]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 39%nat ED2 | exfalso; clear - Hj; lia ]
    end
  end.
+ (* kd = 3, acc = 2 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = 1)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 3) as [Hlt|Hge];
        [reflexivity | exfalso; clear - HACC Hge; lia]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d2 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  pose proof (proj2 (HDg 2%nat ltac:(cbn [length rev app]; clear; lia))) as HR2. cbn [rev app nth] in HR2.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [ |
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 2 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 2 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 2) with 2%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 2) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 2 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 2) (sq_n g + 2)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SLit 1) 1
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(reflexivity) ltac:(clear; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0; d1] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|[|j]]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 39%nat ED2 | sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 1%nat 38%nat ED1 | exfalso; clear - Hj; lia ]
    end
  end.
+ (* kd = 3, acc = 3 *)
  rewrite HK in *; rewrite HA in *.
  assert (Hover : sq_over g = sq_ov g)
    by (unfold sq_over; rewrite HK; destruct (Z.ltb_spec (sb_dec_c.sb_dec_room (sq_cap g) (sq_n g)) 3) as [Hlt|Hge];
        [exfalso; clear - HACC Hlt; lia | reflexivity]).
  unfold sq_kd in HK. remember (sq_D g) as DD eqn:HDD.
  destruct DD as [|d0 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d1 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|d2 DD]; cbn [length] in HK; [clear - HK; lia|].
  destruct DD as [|dx DD]; cbn [length] in HK; [|clear - HK; lia].
  pose proof (EDb 0%nat ltac:(clear; lia)) as ED0. pose proof (EDb 1%nat ltac:(clear; lia)) as ED1.
  pose proof (EDb 2%nat ltac:(clear; lia)) as ED2.
  cbn [rev app nth Nat.add] in ED0, ED1, ED2.
  pose proof (proj2 (HDg 0%nat ltac:(cbn [length rev app]; clear; lia))) as HR0. cbn [rev app nth] in HR0.
  pose proof (proj2 (HDg 1%nat ltac:(cbn [length rev app]; clear; lia))) as HR1. cbn [rev app nth] in HR1.
  pose proof (proj2 (HDg 2%nat ltac:(cbn [length rev app]; clear; lia))) as HR2. cbn [rev app nth] in HR2.
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 3 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 3 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 3 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 3 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 3 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 3 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  psrr_branch_tok RUNTO BR HS SHOK sbB_Bspan;
  [
    lazymatch goal with
    | Hc : branch_taken _ (sv_denot ?Ec _) _ = _ |- _ =>
      rewrite branch_geu_U in Hc;
      rewrite (U_atom_off Ec 34%nat (sq_n g) _
        (sbB_ew_eq Ec (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) in Hc by lia;
      rewrite (U_atom Ec 33%nat (sq_cap g)
        (sbB_ew_eq Ec (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr))) in Hc by lia;
      first [ apply negb_true_iff, Z.ltb_ge in Hc | apply negb_false_iff, Z.ltb_lt in Hc ];
      exfalso; clear - Hc Hroom0 HroomP HroomZ HACC; lia
    end | ].
  paj_run_to_tok RUNTO HS HJ SHOK sbB_Bspan sbB_stop;
  [ lazymatch goal with |- awr_ok ?Ea ?rsa _ _ _ _ _ _ _ =>
      apply (sbB_awr_of Ea rsa 3 3 (sq_b g) qv _ _ _ _ _ _ _ ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ea (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ea (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr)) HWb HWq)
    end | ].
  lazymatch goal with
  | HFr : frame_of ?Ew ?rsw (mrestrict _ _) (mrestrict _ _) |- _ =>
    assert (HWR : forall aa, in_wrange Ew rsw aa -> tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3 aa);
    [ intros aa Hin; unfold tsb_dec_wr;
      destruct (sbB_wrange_of Ew rsw 3 3 (sq_b g) qv aa Hin ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ew (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr))
        (sbB_ewu_eq Ew (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))) as [HW | HW];
      [ left; exact HW | first [ right; rewrite (Hqv ltac:(clear; lia)) in HW; exact HW | exfalso; clear - HW; lia ] ]
    | pose proof (sbB_eq_trans _ _ Ew rsw _ _ _ HEQ HFr HWR) as HEQn;
      clear HEQ HWR; rename HEQn into HEQ ]
  end.
  match goal with
  | HG : mem_grows _ _ |- _ =>
    lazymatch HG with
    | HGR => fail
    | _ => pose proof (mem_grows_trans _ _ _ HGR HG) as HGRn; clear HGR HG; rename HGRn into HGR
    end
  end.
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end.
  pmkst HS.
  lazymatch goal with
  | |- SRr _ _ (mkCfg (mkst ?rf _ ?mf _) ?mdf) _ =>
    lazymatch goal with
    | HSf : st_ok_pi _ _ ?Ef ?ssf _ |- _ =>
      pose proof (st_ok_mem_ok SEGS _ _ _ HSf) as HMok;
      destruct HMok as (_ & HRok & _); cbn [ms_mem restrict] in HRok;
      assert (HAE : env_agree 32 (Ereg regs2 (map (Z_to_bv 64) (sbB_vals g))) Ef)
        by (split; [intros nn Hnn; rewrite ?ew_ewset_lo by lia; unfold sbB_E;
                    apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
      assert (RK : forall r, In r [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] -> getr rf r = getr regs2 r)
        by (intros r Hr; pose proof (regs_kept_of_st_ok_pi Ef ssf _ regs2
              (map (Z_to_bv 64) (sbB_vals g)) [(2%bv : bv 5); (3%bv : bv 5); (4%bv : bv 5); (8%bv : bv 5); (9%bv : bv 5); (10%bv : bv 5); (16%bv : bv 5); (17%bv : bv 5); (18%bv : bv 5); (21%bv : bv 5); (24%bv : bv 5); (25%bv : bv 5); (26%bv : bv 5); (27%bv : bv 5)] HSf HAE ltac:(vm_compute; reflexivity) r Hr) as Xk;
            cbn [ms_regs restrict] in Xk; exact Xk);
      apply SRr_ret; unfold sbd_B_end, sbd_cut;
      rewrite HA; rewrite Hover; rewrite <- HDD;
      change (Z.to_nat 3) with 3%nat;
      split; [reflexivity|];
      exists ly2, S2, rf, mf, mdf;
      split; [ unfold cfg_at; replace (A_sb_dec + SBD_B_END) with (BASE + (AF_sb_dec + SBD_B_END))
                 by (unfold A_sb_dec; clear; lia); reflexivity |];
      split; [ exact HJ |];
      split; [ apply (sbB_kept_run (sq_lyc g) (sq_Sc g) (sq_W g) (sq_memc g) mem2 mf (sq_mdc g)
                 (sq_sp g) (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3)
                 (tsb_dec_wr (sq_b g) (sq_p g) (sq_n g) 3) HAR0 HKA HEQ HGR);
               let aa := fresh "aa" in let Haa := fresh "Haa" in
               intros aa Haa; split; [exact Haa | exact (HErImg aa Haa)] |];
      split; [ exact HabS |];
      split; [ exact Hni |];
      split; [ apply (sbB_common_keep g pos regs2 rf mem2 mf 3 HCom RK HEQ
                 HAway HFaway (proj1 HspB) (proj2 HspB) (proj1 HFB) (proj2 HFB)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 0 8 (SOff 32 0) (sq_p g)
        (sq_b g) (sq_b g) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) ltac:(clear; lia)
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 32%nat _ E32b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rp; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 8 8 (SOff 33 0) (sq_cap g)
        (sq_b g) (sq_b g + 8) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 33%nat _ E33b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rcap; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 16 8 (SOff 34 3) (sq_n g + 3)
        (sq_b g) (sq_b g + 16) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(rewrite (denot_lit_U Ef (SOff 34 _)); f_equal; rewrite (U_atom_off Ef 34%nat (sq_n g) _ (sbB_ew_eq Ef (sbB_E regs2 g) 34%nat _ E34b ltac:(sbB_agr))) by (clear - Rn0 Rn4; lia); reflexivity) ltac:(clear - Rn0 Rn4; zside) ltac:(clear; zside)) |];
      split; [
      exact (sbB_vm_at Ef (rd (sq_W g) mf) (ss_mem ssf) 18%nat 24 4 (SOff 35 0) (sq_ov g)
        (sq_b g) (sq_b g + 24) HRok ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        (sbB_ewu_eq Ef (sbB_E regs2 g) 18%nat (sq_b g) E18u ltac:(sbB_agr)) eq_refl
        ltac:(cbn [sv_denot]; rewrite (sbB_ew_eq Ef (sbB_E regs2 g) 35%nat _ E35b ltac:(sbB_agr)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(clear - Rov; zside) ltac:(clear; zside)) |];
      apply (sbB_garr_at Ef (rd (sq_W g) mf) (ss_mem ssf) 36%nat (sq_p g + sq_n g)
        [d0; d1; d2] HRok ltac:(vm_compute; reflexivity)
        ltac:(rewrite <- (Hqv ltac:(clear; lia)); exact (sbB_ewu_eq Ef (sbB_E regs2 g) 36%nat qv eq_refl ltac:(sbB_agr))));
      let j := fresh "j" in let Hj := fresh "Hj" in
      intros j Hj; cbn [length firstn Z.to_nat Pos.to_nat] in Hj;
      destruct j as [|[|[|j]]]; [ sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 0%nat 39%nat ED2 | sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 1%nat 38%nat ED1 | sbB_dig1 Ef (sbB_E regs2 g) (ss_mem ssf) 36%nat 2%nat 37%nat ED0 | exfalso; clear - Hj; lia ]
    end
  end.
Qed.
End walk.
End h.
End f.
End d.
