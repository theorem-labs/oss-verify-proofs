(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryUnset), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryUnset.v, with its module paths and module names changed; 2249 of its 2361 lines of code are new or changed and 693 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxLxCase3.v, with its module paths and module names changed; 645 of its 725 lines of code are new or changed and 2281 lines of the source are left out. *)
(* The start of LLVMFuzzerTestOneInput's case 0 (declare, fuzz_boxreg.c:213-216) on the ASan build: from the case cut
   GI_T 0 (0x802ec, BoxLxDefs.v) the walk reads nch and base off the input cursor `struct fuzz_in in` (sp1 + 0x88: p,
   sp1 + 0x90: n), each through fuzz_u8: `ld a1, 0x90(s1)`; when n = 0 the byte is 0 (0x80508 / 0x8050c), else
   `ld a0, 0x88(s1)`, the shadow test of p (`srli; add s2; lb; bnez -> 0x80d50 / 0x80dd0`, the slow path into
   __asan_report_load1), the stores of p + 1 and n - 1 and `lbu`. Then s10 = base << 56, s11 = base >> 56 (the
   sign-extended byte), a0 = sp1 + 0x88 and `jal read_name` (0x8051c), whose caller-journal contract
   (ReadName.v tread_name_spec) gives the name; its return slot 0x80520 is the cut C0_N (BoxLxCase0Defs.v).
   The walk is split on the bytes left at the cursor (0, 1, 2 or more), so that each seat has exactly the input
   bytes it reads as read-only chunks (atoms 33 .. 35) and the cursor window [0x88, 0x98) writable; the two shadow
   tests leave range_addressable obligations at p and p + 1, which the caller's input block discharges
   (range_addressable_of_block), so the engine decides both `bnez` to the slow paths not taken. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YI16 YC5d YM05 YG0s YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC4b YC1g YC1h YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit BoxLxDefs ReadName.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Boxreg BoxregUpd LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require LLVMFuzzerTestOneInput_case0 LLVMFuzzerTestOneInput_rn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require read_name_c reac_boxreg_declare_c.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxCase0Defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.


(* The shadow base the runner reads against; the cursor window [0x88, 0x98) of the spill area (atom 9 = s1 = sp1),
   with n left at 0x90 (a closed numeral, or atom 33); the input bytes at the cursor p (atom 32), read-only. *)
Definition C0I_SB : Z := 0x7fff8000.
Definition C0I_Rsl (v90 : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x88 0x98 0x88 0x98 [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x90 (CVal 8 v90)].
Definition C0I_Rin (cs : list YP09.chunk) (n : Z) : YP09.region := YP09.mkRegion (Some 32%nat) 0 n 0 0 cs.
(* sp1 lies above the shadow span (2^46 <= alloc_ceiling <= sp1), s2 = SHADOW_OFF. *)
Definition C0I_F (ex : list (nat * afact)) : facts :=
  mkFacts ((9%nat, mkAF (2 ^ 46) (2 ^ 47) 5) :: (18%nat, mkAF C0I_SB C0I_SB 0) :: ex) [] [].
(* The registers the walk to the call keeps (it writes s3, s10, s11 and temporaries only). *)
Definition c0i_kl : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv].

Lemma c0i_skipn_cons : forall (l : list byte) n d, (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
induction l as [|x l IH]; intros n d Hn; [cbn in Hn; lia|].
destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in Hn. lia.
Qed.

Lemma c0i_bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof.
intros l1 l2. induction l1 as [|x l IH].
- change ([] ++ l2) with l2. change (bsum []) with 0. lia.
- change ((x :: l) ++ l2) with (x :: (l ++ l2)). change (bsum (x :: (l ++ l2))) with (snd x + bsum (l ++ l2)).
  change (bsum (x :: l)) with (snd x + bsum l). rewrite IH. lia.
Qed.

Lemma c0i_sl : forall y : byte, alu64 ALU_SLL (Z_to_bv 64 (bv_unsigned y)) (Z_to_bv 64 56) = Z_to_bv 64 (bv_signed y * 2 ^ 56).
Proof.
intros y. pose proof (bv_unsigned_in_range 8 y) as R. change (bv_modulus 8) with 256 in R.
rewrite alu64_sll_lit by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (LLVMFuzzerTestOneInput_case0.c0_byte_signed y) as [(E & _) | (E & _)]; rewrite E; [reflexivity|].
replace ((bv_unsigned y - 256) * 2 ^ 56) with (bv_unsigned y * 2 ^ 56 + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma c0i_sr : forall y : byte, alu64 ALU_SRA (Z_to_bv 64 (bv_signed y * 2 ^ 56)) (Z_to_bv 64 56) = Z_to_bv 64 (bv_signed y).
Proof.
intros y. pose proof (bv_unsigned_in_range 8 y) as R. change (bv_modulus 8) with 256 in R.
assert (Hs : -128 <= bv_signed y < 128) by (destruct (LLVMFuzzerTestOneInput_case0.c0_byte_signed y) as [(E & H) | (E & H)]; lia).
rewrite alu_sra. unfold v_sra. rewrite Boxreg.signed_lit by lia. rewrite unsigned_lit_small by lia. change (56 mod 64) with 56.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Lemma c0i_val_mem1 : forall (W : world SEGS) (m : word -> option byte) a v,
  aview SEGS (w_H W) m a = Some v -> val_mem SEGS (mrestrict (w_H W) m) a 1 v /\ 0 <= v < 256.
Proof.
intros W m a v Hv. destruct (aview_byte SEGS (w_H W) m a v Hv) as (b & Hb & -> & Hr).
split; [|exact Hr]. intros kk Hk. assert (kk = 0)%nat by lia. subst kk. cbn [Z.of_nat].
rewrite Z.add_0_r, Hb. f_equal. apply bv_eq. rewrite le_byte_small by (cbn [Z.of_nat]; lia).
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.shiftr_div_pow2 by lia. cbn [Z.of_nat Z.mul]. rewrite Z.div_1_r. symmetry. apply Z.mod_small. exact Hr.
Qed.

Lemma c0i_pl_cons : forall cx pos, 0 <= pos < c_n cx ->
  c0_pl cx pos = nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0) :: c0_pl cx (pos + 1).
Proof.
intros cx pos Hp. unfold c0_pl. replace (Z.to_nat (pos + 1)) with (S (Z.to_nat pos)) by lia.
apply c0i_skipn_cons. unfold c_n in Hp. lia.
Qed.
Lemma c0i_pl_nil : forall cx pos, c_n cx <= pos -> c0_pl cx pos = [].
Proof. intros cx pos Hp. unfold c0_pl. apply skipn_all2. unfold c_n in Hp. lia. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TREADNAME : tread_name_spec B MT.
Hypothesis HRNTR : In [pc_malloc_ra0 (as_code B); A_read_name_mallocRA] (as_universe B).

Lemma c0i_stk_ra : forall ly S W mem md a m,
  AR SEGS B ly S W mem md -> ly_stk_lo ly <= a -> 0 <= m -> a + m <= ly_stk_hi ly ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a m.
Proof.
  intros ly S W mem md a m HAR Ha Hm Hm2.
  pose proof (al_zshadow _ _ LAWS ly S W mem md (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR
    ltac:(left; reflexivity)) as HZ. cbn [fst snd] in HZ.
  pose proof (am_layout _ _ _ _ (proj1 HAR)) as LO.
  pose proof (lo_top _ LO) as (T1 & T2 & T3 & T4 & T5 & T6 & T7). unfold page_aligned in T5, T6.
  apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) a m);
    [| exact Ha | lia].
  apply zero_shadow_range; [| | exact HZ].
  - apply Z.mod_divide in T5; [|lia]. apply Z.mod_divide; [lia|]. destruct T5 as [q Hq]. exists (512 * q). lia.
  - apply Z.mod_divide in T5; [|lia]. apply Z.mod_divide in T6; [|lia]. apply Z.mod_divide; [lia|].
    destruct T5 as [q1 Hq1]. destruct T6 as [q2 Hq2]. exists (512 * q2 - 512 * q1). lia.
Qed.

Lemma c0i_pl_len : forall cx pos, 0 <= pos <= c_n cx -> Z.of_nat (length (c0_pl cx pos)) = c_n cx - pos.
Proof. intros cx pos Hp. unfold c0_pl, c_n in *. rewrite length_skipn. lia. Qed.

Lemma c0i_pl2_len : forall cx pos, 0 <= pos <= c_n cx ->
  Z.of_nat (length (c0_pl2 cx pos)) = c_n cx - pos - LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) /\
  0 <= LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) <= c_n cx - pos.
Proof.
  intros cx pos Hp. pose proof (c0i_pl_len cx pos Hp) as L.
  pose proof (LLVMFuzzerTestOneInput_case0.c0_skip_len (c0_pl cx pos)) as (S1 & S2).
  unfold c0_pl2. rewrite S1, L. lia.
Qed.

(* A byte of what read_name reads, as a byte of the input. *)
Lemma c0i_pl2_nth : forall cx pos j, 0 <= pos -> 0 <= j < Z.of_nat (length (c0_pl2 cx pos)) ->
  LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) = 2 /\
  nth (Z.to_nat j) (c0_pl2 cx pos) (Z_to_bv 8 0) = nth (Z.to_nat (pos + 2 + j)) (c_pl cx) (Z_to_bv 8 0) /\
  pos + 2 + j < c_n cx.
Proof.
  intros cx pos j Hp Hj. unfold c0_pl2, c0_pl in *. rewrite skipn_skipn in *. rewrite length_skipn in Hj.
  unfold LLVMFuzzerTestOneInput_case0.c0_used. rewrite length_skipn. unfold c_n.
  split; [lia|]. split; [|lia]. rewrite nth_skipn. f_equal. lia.
Qed.

(* A byte of the new block lies apart from every older block. *)
Lemma c0i_new_apart : forall ly2 S2 W2 mem2 md2 ly3 S3 s n b m j,
  AR SEGS B ly2 S2 W2 mem2 md2 -> ablocks B ly2 S2 = ablocks B ly3 S3 ++ [(s, n)] -> 0 < n ->
  In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m -> ~ (s <= b + j < s + n).
Proof.
  intros ly2 S2 W2 mem2 md2 ly3 S3 s n b m j HAR E Hn Hb Hj Hs.
  assert (Hb2 : In (b, m) (ablocks B ly2 S2)) by (rewrite E; apply in_or_app; left; exact Hb).
  assert (Hs2 : In (s, n) (ablocks B ly2 S2)) by (rewrite E; apply in_or_app; right; left; reflexivity).
  assert (Ne : (b, m) <> (s, n)).
  { intros Ee. apply in_split in Hb as (l1 & l2 & El). rewrite Ee in El.
    apply (c0_blk_twice LAWS ly2 S2 W2 mem2 md2 l1 l2 [] (s, n) HAR); [|cbn [snd]; lia].
    rewrite E, El. rewrite <- app_assoc. reflexivity. }
  { pose proof (sep_blocks SEGS B LAWS ly2 S2 W2 mem2 md2 b m s n HAR Hb2 Hs2 Ne) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. pose proof (req_size_pos n ltac:(lia)) as [_ Hq]. lia. }
Qed.

(* ---- the call of read_name (0x8051c) and the cut C0_N at its return slot ---- *)

Lemma c0i_call : forall i POST cx fp k acc ly3 S3 W3 md3 (regs : bvmap 5 word) mem r bs pos op,
  gb_from B MT POST (C0_N B MT i) ->
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0_mf i cx fp W3 (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) r bs ->
  0 <= i < 64 -> k <= 1 + 2 * i -> acc <= GB_A MT i ->
  gblk1 B cx ly3 S3 r -> greg B ly3 S3 W3 (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) r bs ->
  Boxreg.boxreg_inv bs -> 0 <= op < 256 -> Z.land op 3 = 0 -> 0 <= pos <= c_n cx ->
  gslot cx W3 (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) 0x88
    (c_p cx + pos + LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos)) ->
  gslot cx W3 (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) 0x90
    (c_n cx - pos - LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos)) ->
  gregs cx fp (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) ->
  getr regs 1 = w64 (BASE + GC_N) -> getr regs 10 = w64 (c_sp1 cx + 0x88) ->
  getr regs 19 = w64 (c0_nch cx pos) -> getr regs 20 = w64 r -> getr regs 22 = w64 op ->
  getr regs 25 = w64 (Boxreg.bx_fabric bs) -> getr regs 26 = w64 (c0_base cx pos * 2 ^ 56) ->
  getr regs 27 = w64 (c0_base cx pos) ->
  SRr SEGS W3 (cfg_at SEGS A_read_nameP regs mem md3) (POST cx).
Proof.
intros i POST cx fp k acc ly3 S3 W3 md3 regs mem r bs pos op HN HB HJ HFR HMO HMF Hi Hk Hacc HBLK HREG HINV Hop Hop3 Hpos
  C88 C90 HGR R1 R10 R19 R20 R22 R25 R26 R27.
pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24). cbn [ms_regs mkst] in G2, G8, G9, G3, G4, G18, G24.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof HB as (HPRE0 & _ & _ & Hinp & _ & _ & Hev & Hlive & _ & _ & _ & _ & _ & HMOK & HTR & HNEED).
pose proof HPRE0 as (HAR0 & _ & _ & Hgp & Htp & Hstk0 & _).
pose proof Hstk0 as (_ & _ & Hceil & Hslo & Hshi & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & Eshi & _).
pose proof (c0i_pl2_len cx pos Hpos) as (Lpl2 & Hused).
set (used := LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos)) in *.
set (pl := c0_pl2 cx pos) in *.
pose proof (LLVMFuzzerTestOneInput_rn.rn_k_range pl) as (Hrk & Hrk2).
assert (Usp : spZ regs = c_sp1 cx) by (unfold spZ; rewrite G2; unfold w64; apply unsigned_lit_small; lia).
assert (Hinp3 : c_n cx = 0 \/ (0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\
  4096 <= c_p cx /\ c_p cx + req_size (c_n cx) <= alloc_ceiling /\ in_app (c_p cx) (req_size (c_n cx)))).
{ destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & Happ & _).
  split; [lia|]. split; [exact Hin3|]. split; [lia|]. split; [lia|]. exact Happ. }
assert (Hpl0 : 0 <= c_p cx /\ c_p cx + c_n cx <= 2 ^ 47).
{ destruct Hinp as [(Hn0 & Hp0) | (Hn & _)]; [rewrite Hp0, Hn0; unfold GB_EMPTY; lia|].
  destruct Hinp3 as [Hn0 | (_ & _ & H1 & H2 & _)]; [lia|]. pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq]. lia. }
unfold GC_N in R1.

eapply SRr_bind.
{ apply (TREADNAME GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)]
    ly3 S3 W3 mem md3 k regs (c_sp1 cx + 0x88) (c_p cx + pos + used) (c_p cx) (c_n cx) pl HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - rewrite G3. exact Hgp.
  - rewrite G4. exact Htp.
  - rewrite Usp. apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp32; [|lia]. destruct Hsp32 as [q Hq]. exists (2 * q). lia.
  - rewrite Usp. unfold READ_NAME_STK, GB_STK. change ASTACK with 16384. lia.
  - rewrite Usp. lia.
  - exact R10.
  - apply Z.mod_divide; [lia|]. apply Z.mod_divide in Hsp32; [|lia]. destruct Hsp32 as [q Hq]. exists (4 * q + 17). lia.
  - rewrite Usp. lia.
  - apply (val_mem_of_rdword SEGS (w_H W3) mem). exact C88.
  - rewrite Lpl2. apply (val_mem_of_rdword SEGS (w_H W3) mem). replace (c_sp1 cx + 136 + 8) with (c_sp1 cx + 144) by lia. exact C90.
  - apply (c0i_stk_ra ly3 S3 W3 mem md3); [exact HAR3 | rewrite Eslo; unfold GB_STK in *; lia | lia | rewrite Eshi; lia].
  - intros a Ha. split; [left; unfold GB_STK; lia|]. split; [apply HPRES; unfold GB_STK; lia|].
    split; [apply (al_stack _ _ LAWS ly3 S3 W3 mem md3 a HAR3); rewrite Eslo, Eshi; unfold GB_STK in *; lia|].
    rewrite Usp. lia.
  - lia.
  - rewrite Lpl2. lia.

  - rewrite Lpl2. destruct Hinp as [(Hn0 & Hp0) | (Hn & Hin)].
    + left. rewrite Hp0. unfold GB_EMPTY. lia.
    + destruct Hinp3 as [Hn0 | (_ & _ & H1 & H2 & Happ)]; [lia|].
      pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hq].
      apply (amem_range_sub_app (c_p cx) (req_size (c_n cx))); [exact Happ | lia | lia | lia | lia].
  - intros Hne. destruct Hinp3 as [Hn0 | (_ & Hin3 & _)].
    + exfalso. apply Hne. apply length_zero_iff_nil. lia.
    + split; [exact Hin3|]. lia.
  - intros j Hj. destruct (c0i_pl2_nth cx pos j ltac:(lia) Hj) as (Hu2 & Enth & Hjn). fold used in Hu2. fold pl in Enth. rewrite Enth.
    pose proof HMF as (_ & _ & _ & _ & HIN & _). cbn [ms_mem mkst] in HIN.
    assert (Hjl : (Z.to_nat (pos + 2 + j) < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat) by (rewrite length_map; unfold c_n in Hjn; lia).
    destruct (HIN _ Hjl) as (Hv & Hr).
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by exact Hjl. rewrite map_nth in Hv, Hr.
    replace (c_p cx + pos + used + j) with (c_p cx + Z.of_nat (Z.to_nat (pos + 2 + j))) by lia.
    apply (aview_of_val_mem1 SEGS (w_H W3) mem); [exact Hv | exact Hr].
  - pose proof (c0_nev cx fp k ly3 S3 W3 mem md3 HB ltac:(lia) HJ). unfold EV_READ_NAME. lia.
  - pose proof HB as (_ & _ & _ & _ & _ & _ & _ & Hlv & _).
    rewrite (blocks_bytes_bsum B ly3 S3), HBLK, c0i_bsum_app. rewrite (blocks_bytes_bsum B (c_ly cx) (c_S cx)) in Hlv.
    cbn [bsum fold_right snd]. unfold GB_LIVE, LIVE_READ_NAME, REG_SIZE in *. lia.
  - apply (mok_station MT (c_S cx) S3 (c_T cx) acc _ MTL HMOK HMO); [apply mo_malloc_nonneg; [exact MTL | lia]|].
    pose proof (mo_malloc_mono MT MTL (read_name_c.rn_k pl + 1) 48 ltac:(lia)) as M1.
    pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as M2. pose proof (mo_free_nonneg MT MTL) as M3.
    unfold GB_NEED, GB_A in *. nia.
  - exact HRNTR. }

intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & s & -> & HJ2 & HP2 & R10' & Hfr2 & Hs4096 & Hab2 & _ & _ & Hname & Hc1 & Hc2 & Hmle & Hkept).
rewrite Usp in Hkept.
pose proof HJ2 as (HAR2 & _).
assert (HFR2 : frames S2 = [(GB_CID, fp)]) by (rewrite Hfr2; exact HFR).
pose proof (c0_geo LAWS cx fp k ly3 S3 W3 mem md3 HB HJ HFR) as (Hinp' & EgF & HF0 & HF1 & HF64 & HSH).
pose proof (c0_geo LAWS cx fp _ ly2 S2 W2 mem2 md2 HB HJ2 HFR2) as (_ & EgF2 & _).
assert (Hsin : In (s, read_name_c.rn_k pl + 1) (ablocks B ly2 S2)) by (rewrite Hab2; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hsin) as (_ & _ & Hsceil & _).
pose proof (req_size_pos (read_name_c.rn_k pl + 1) ltac:(lia)) as [_ Hsq].
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin3) as (_ & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
destruct Hkept as (K1 & K2 & _ & K4 & _).
(* what the call keeps *)
assert (KB : forall b m j, In (b, m) (ablocks B ly3 S3) -> 0 <= j < req_size m ->
  aview SEGS (w_H W2) mem2 (b + j) = aview SEGS (w_H W3) mem (b + j)).
{ intros b m j Hb Hj. apply (K2 b m j Hb Hj). intros [Hc | Hs'].
  - destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hb) as (_ & _ & Hbc & _). lia.
  - exact (c0i_new_apart ly2 S2 W2 mem2 md2 ly3 S3 s (read_name_c.rn_k pl + 1) b m j HAR2 Hab2 ltac:(lia) Hb Hj ltac:(lia)). }
assert (KZ : forall a, c0_zone cx fp a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem a).
{ intros a Ha.
  assert (Hnc : ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98)).
  { destruct Ha as [(_ & _ & _ & Hx) | [Hx | [Hx | Hx]]]; [exact Hx | destruct Hinp' as [Hn0 | Hn0]; lia | lia |].
    rewrite HSH in Hx. unfold SHADOW_OFF in Hx.
    pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia. }
  revert Hnc.
  apply (c0_zone_blocks LAWS cx fp k ly3 S3 W3 mem md3 (fun _ => False)
    (fun a => ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) mem a) HB HJ HFR); [| | | | | exact Ha].
  - intros p n Hp. unfold gblk1 in HBLK. rewrite HBLK. apply in_or_app. left. exact Hp.
  - intros a0 [].
  - intros a0 Ha0 Hs0 Hnc. apply K1; [exact Ha0 | lia |]. intros [Hc | Hs']; lia.
  - intros b m j Hb Hj _ Hnc. exact (KB b m j Hb Hj).
  - intros a0 Hz _ Hnc. apply (K4 GB_CID fp a0); [rewrite HFR; left; reflexivity | exact Hz |].
    assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
    intros [Hc | Hs'].
    + destruct (frame_zone SEGS B LAWS ly3 S3 W3 mem md3 GB_CID fp a0 HAR3 Hfin Hz) as (Hz1 & _). lia.
    + assert (Hfin2 : In (GB_CID, fp) (frames S2)) by (rewrite HFR2; left; reflexivity).
      apply (block_not_frame_zone SEGS B LAWS ly2 S2 W2 mem2 md2 s (read_name_c.rn_k pl + 1) (a0 - s) GB_CID fp HAR2 Hsin Hfin2); [lia|].
      replace (s + (a0 - s)) with a0 by lia. unfold frame_rng in *. cbn [fst snd] in *. rewrite EgF2. rewrite EgF in Hz. exact Hz. }

assert (KP : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr regs r0)
  by (intros r0 Hr; pose proof (HP2 (bv_unsigned r0) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
assert (Htnu : 0 <= tread_name_used pl <= Z.of_nat (length pl)) by (unfold tread_name_used; lia).
assert (Epos2 : c0_pos2 cx pos = pos + used + tread_name_used pl) by reflexivity.
rewrite R1.
eapply (HN cx fp (k + EV_READ_NAME) (acc + mo_malloc MT (read_name_c.rn_k pl + 1)) ly2 S2 W2 (mkst regs2 (w64 (BASE + 1492)) mem2 (seg_rom SEGS)) md2 HB HJ2 HFR2).
- exact (mle_station MT (c_S cx) S3 S2 acc _ MTL HMO Hmle).
- exists r, bs, pos, op, s.
  split; [apply (c0_ms_mkst cx fp GC_N regs2 regs mem2 (w64 A_read_nameP) HGR KP)|].
  split.
  { split; [exact (c0_mf_keep2 i cx fp W3 W2 (mkst regs (w64 A_read_nameP) mem (seg_rom SEGS)) (mkst regs2 (w64 (BASE + 1492)) mem2 (seg_rom SEGS)) r bs HB KZ HMF)|].
    split; [exact Hi|]. split; [unfold EV_READ_NAME; lia|].
    split; [unfold c0_nk; fold pl; lia|].
    split; [rewrite Hab2; unfold gblk1 in HBLK; rewrite HBLK, <- app_assoc; reflexivity|].
    split; [exact HINV|]. split; [exact Hpos|].
    split.
    { rewrite Epos2. split; [lia|]. unfold gslot. cbn [ms_mem mkst]. split.
      - replace (c_p cx + (pos + used + tread_name_used pl)) with (c_p cx + pos + used + tread_name_used pl) by lia.
        apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc1 | lia].
      - replace (c_n cx - (pos + used + tread_name_used pl)) with (Z.of_nat (length pl) - tread_name_used pl) by lia.
        replace (c_sp1 cx + 144) with (c_sp1 cx + 136 + 8) by lia.
        apply (rdword_of_val_mem SEGS (w_H W2) mem2); [exact Hc2 | lia]. }
    split; [exact Hs4096|].
    split; [intros j Hj; unfold c0_nk in Hj; fold pl in Hj; cbn [ms_mem mkst]; exact (Hname j Hj)|].
    split; [exact Hop|]. split; [exact Hop3|].
    cbn [ms_regs mkst]. rewrite KP by c0_cs. exact R20. }
  split.
  { pose proof HREG as (_ & HL & HR). split; [rewrite Hab2; apply in_or_app; left; exact Hrin3|]. split; [exact HL|].
    intros j Hj. cbn [ms_mem mkst]. rewrite (KB r REG_SIZE j Hrin3) by (change (req_size REG_SIZE) with 288; unfold REG_SIZE in Hj; lia).
    exact (HR j Hj). }
  cbn [ms_regs mkst].
  split; [exact R10'|].
  split; [rewrite KP by c0_cs; exact R19|].
  split; [rewrite KP by c0_cs; exact R22|].
  split; [rewrite KP by c0_cs; exact R25|].
  split; [rewrite KP by c0_cs; exact R26|].
  rewrite KP by c0_cs; exact R27.
Qed.

(* The call from the state the walk leaves: GI_T's facts at the case's start, kept outside the cursor window. *)
Lemma c0i_call2 : forall i POST cx fp k acc ly3 S3 W3 (ms3 : machine_state) (regs : bvmap 5 word) mem md r bs pos op,
  gb_from B MT POST (C0_N B MT i) ->
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 mem md k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0_mf i cx fp W3 ms3 r bs -> 0 <= i < 64 -> k <= 1 + 2 * i -> acc <= GB_A MT i ->
  gblk1 B cx ly3 S3 r -> greg B ly3 S3 W3 ms3 r bs ->
  Boxreg.boxreg_inv bs -> 0 <= op < 256 -> Z.land op 3 = 0 -> 0 <= pos <= c_n cx ->
  gregs cx fp ms3 -> getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 22 = w64 op ->
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
     aview SEGS (w_H W3) mem a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall r0 : bv 5, In r0 c0i_kl -> getr regs r0 = getr (ms_regs ms3) r0) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 0x88) = Some (c_p cx + pos + LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos)) ->
  rdword (aview SEGS (w_H W3) mem) (c_sp1 cx + 0x90) = Some (c_n cx - pos - LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos)) ->
  getr regs 1 = w64 (BASE + GC_N) -> getr regs 10 = w64 (c_sp1 cx + 0x88) ->
  getr regs 19 = w64 (c0_nch cx pos) -> getr regs 26 = w64 (c0_base cx pos * 2 ^ 56) ->
  getr regs 27 = w64 (c0_base cx pos) ->
  SRr SEGS W3 (cfg_at SEGS A_read_nameP regs mem md) (POST cx).
Proof.
intros i POST cx fp k acc ly3 S3 W3 ms3 regs mem md r bs pos op HN HB HJ HFR HMO HMF3 Hi Hk Hacc HBLK HREG3 HINV Hop Hop3 Hpos
  HGR3 R20 R22 R25 M1 KP C88 C90 R1 R10 R19 R26 R27.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & _). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & _).
pose proof HJ as (HAR3 & _).
pose proof (c0_geo LAWS cx fp k ly3 S3 W3 mem md HB HJ HFR) as (Hinp' & EgF & HF0 & HF1 & HF64 & HSH).
assert (ZR : forall a, c0_zone cx fp a -> 0 <= a < 2 ^ 64) by (intros a; apply c0_zone_range; first [exact Hinp' | lia | exact HSH]).
assert (Hrin3 : In (r, REG_SIZE) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hrin3) as (_ & Hr4096 & Hrceil & _).
change (req_size REG_SIZE) with 288 in Hrceil.
assert (KPk : forall n : nat, In (Z_to_bv 5 (Z.of_nat n)) c0i_kl -> getr regs (Z_to_bv 5 (Z.of_nat n)) = getr (ms_regs ms3) (Z_to_bv 5 (Z.of_nat n)))
  by (intros n Hn; exact (KP _ Hn)).
pose proof HGR3 as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
apply (c0i_call i POST cx fp k acc ly3 S3 W3 md regs mem r bs pos op HN HB HJ HFR HMO).
- apply (c0_mf_keep2 i cx fp W3 W3 ms3 _ r bs HB); [|exact HMF3]. intros a Ha. cbn [ms_mem mkst]. apply M1; [exact (ZR a Ha)|].
  destruct Ha as [(_ & _ & _ & Hx) | [Hx | [Hx | Hx]]]; [exact Hx | destruct Hinp' as [Hn0 | Hn0]; lia | lia |].
  rewrite HSH in Hx. unfold SHADOW_OFF in Hx.
  pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)). lia.
- exact Hi.
- exact Hk.
- exact Hacc.
- exact HBLK.
- pose proof HREG3 as (HI & HL & HR). split; [exact HI|]. split; [exact HL|]. intros j Hj. cbn [ms_mem mkst].
  rewrite M1 by (unfold REG_SIZE in Hj; lia). exact (HR j Hj).
- exact HINV.
- exact Hop.
- exact Hop3.
- exact Hpos.
- exact C88.
- exact C90.
- unfold gregs. cbn [ms_regs mkst].
  split; [rewrite (KP 2%bv) by (cbn; tauto); exact G2|]. split; [rewrite (KP 8%bv) by (cbn; tauto); exact G8|].
  split; [rewrite (KP 9%bv) by (cbn; tauto); exact G9|]. split; [rewrite (KP 3%bv) by (cbn; tauto); exact G3|].
  split; [rewrite (KP 4%bv) by (cbn; tauto); exact G4|]. split; [rewrite (KP 18%bv) by (cbn; tauto); exact G18|].
  rewrite (KP 24%bv) by (cbn; tauto); exact G24.
- exact R1.
- exact R10.
- exact R19.
- rewrite (KP 20%bv) by (cbn; tauto); exact R20.
- rewrite (KP 22%bv) by (cbn; tauto); exact R22.
- rewrite (KP 25%bv) by (cbn; tauto); exact R25.
- exact R26.
- exact R27.
Qed.

(* ---- the walk 0x802ec .. 0x8051c, split on the bytes left at the cursor ---- *)

Definition c0i_T (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (r : Z) (bs : list byte) (pos op : Z) : Prop :=
  gb_body cx fp (GP_T 0) W3 ms3 GSH_it /\ 0 <= i < 64 /\ k <= 1 + 2 * i /\ acc <= GB_A MT i /\
  gblk1 B cx ly3 S3 r /\ greg B ly3 S3 W3 ms3 r bs /\ gprev cx fp W3 ms3 bs /\ Boxreg.boxreg_inv bs /\
  0 <= op < 256 /\ Z.land op 3 = 0 /\
  getr (ms_regs ms3) 20 = w64 r /\ getr (ms_regs ms3) 22 = w64 op /\
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) /\ getr (ms_regs ms3) 26 = w64 (Boxreg.bx_n bs) /\
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) /\ gcursor cx W3 ms3 pos /\
  gslot cx W3 ms3 0x68 i /\ (0 <= 1 -> gslot cx W3 ms3 0x48 (Boxreg.bx_n bs)).

Lemma c0i_n0 : forall i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op,
  gb_from B MT POST (C0_N B MT i) -> gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0i_T i cx fp k acc ly3 S3 W3 ms3 r bs pos op -> c_n cx - pos = 0 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.

intros i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HI HCASE.
destruct HI as (HBODY & Hi & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3 & R20 & R22 & R25 & R26 & HSR & HCUR & S68 & S48).
specialize (S48 ltac:(lia)).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & HSV & HSH & Hshlen & HFL & HSF & HIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
pose proof HCUR as (Hpos & C88 & C90).
assert (HMS : c0_ms cx fp 0x3a0 ms3) by (repeat split; assumption).
assert (HMF : c0_mf i cx fp W3 ms3 r bs) by exact (conj HSV (conj HSH (conj HFL (conj HSF (conj HIN (conj HPREV (conj HSR (conj S68 S48)))))))).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).

set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos)])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; vm_compute; split; congruence).
assert (Hp64 : 0 <= c_p cx + pos < 2 ^ 64).
{ pose proof HB as (_ & _ & _ & Hinp & _). pose proof (c0_geo LAWS cx fp k ly3 S3 W3 _ _ HB HJ HFR) as (Hinp' & _).
  destruct Hinp as [(Hn0 & Hp0) | (Hn & _)]; [rewrite Hp0; unfold GB_EMPTY; lia | destruct Hinp' as [Hn0 | Hn0]; lia]. }
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x3a0 sr_atoms [C0I_Rsl (SLit 0)] None (C0I_F [])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp 0x3a0 ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok, C0I_Rsl. cbv zeta.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (chunk_ok_val SEGS E _ _ 0x88 8 (SOff 32 0) (c_p cx + pos)); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C88.
    + apply (chunk_ok_val SEGS E _ _ 0x90 8 (SLit 0) 0); [rewrite denot_lit_U, c0_U_lit_val by lia; reflexivity | cbn; lia | cbn; lia |].
      apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). rewrite <- HCASE. exact C90.
  - cbn. repeat split.
  - split; [|split; exact I]. cbn [C0I_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18. unfold C0I_SB. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hsp32 | reflexivity | lia]. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0I_SB, C0I_SB + 2 ^ 44 - 1).

{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]. }

assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). intros (rr & Hrr & Hb). cbn [ss_mem In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi C0I_Rsl base_val] in Hb; rewrite U9 in Hb; lia|]).
  destruct Hrr. }
clear HF HFr HG.
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos)]) E)
  by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP : forall r0 : bv 5, In r0 c0i_kl -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
  by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) ms) (ms_regs ms3) _ c0i_kl HS HAE ltac:(vm_compute; reflexivity) r0 Hr)).
pose proof (st_ok_region_nth E _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS. rewrite pa_sigma_read_name.
change (SRr SEGS W3 (cfg_at SEGS A_read_nameP (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)) (POST cx)).

assert (Eu : LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) = 0).
{ unfold LLVMFuzzerTestOneInput_case0.c0_used. rewrite (c0i_pl_len cx pos Hpos). lia. }
assert (Epl : c0_pl cx pos = []).
{ apply length_zero_iff_nil. pose proof (c0i_pl_len cx pos Hpos). lia. }
apply (c0i_call2 i POST cx fp k acc ly3 S3 W3 ms3 (ms_regs ms) (ms_mem ms) _ r bs pos op HN HB HJ HFR HMO HMF Hi Hk Hacc HBLK HREG HINV Hop Hop3 Hpos HGR R20 R22 R25 M1 KP).
- rewrite Eu, Z.add_0_r. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9. exact (field_of_region E _ 9%nat _ _ _ _ _ _ 0x88 8 (SOff 32 0) (c_p cx + pos) HRG eq_refl ltac:(cbn; tauto) ltac:(rewrite c0_denot_off0; exact F32) ltac:(cbn; lia) ltac:(cbn; lia)).
- rewrite Eu, Z.sub_0_r, HCASE. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9. exact (field_of_region E _ 9%nat _ _ _ _ _ _ 0x90 8 (SLit 0) 0 HRG eq_refl ltac:(cbn; tauto) ltac:(rewrite denot_lit_U, c0_U_lit_val by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
- exact Q1.
- rewrite Q10, U9. reflexivity.
- rewrite Q19. unfold c0_nch. rewrite Epl. reflexivity.
- rewrite Q26. unfold c0_base. rewrite Epl. reflexivity.
- rewrite Q27. unfold c0_base. rewrite Epl. reflexivity.
Qed.

Lemma c0i_n1 : forall i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op,
  gb_from B MT POST (C0_N B MT i) -> gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0i_T i cx fp k acc ly3 S3 W3 ms3 r bs pos op -> c_n cx - pos = 1 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.

intros i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HI HCASE.
destruct HI as (HBODY & Hi & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3 & R20 & R22 & R25 & R26 & HSR & HCUR & S68 & S48).
specialize (S48 ltac:(lia)).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & HSV & HSH & Hshlen & HFL & HSF & HIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
pose proof HCUR as (Hpos & C88 & C90).
assert (HMS : c0_ms cx fp 0x3a0 ms3) by (repeat split; assumption).
assert (HMF : c0_mf i cx fp W3 ms3 r bs) by exact (conj HSV (conj HSH (conj HFL (conj HSF (conj HIN (conj HPREV (conj HSR (conj S68 S48)))))))).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).

assert (Hn1 : 0 < c_n cx /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 4096 <= c_p cx /\ c_p cx + req_size (c_n cx) <= alloc_ceiling).
{ pose proof HB as (_ & _ & _ & Hinp & _). destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _). split; [lia|]. split; [exact Hin3|]. lia. }
destruct Hn1 as (Hn1 & Hin3 & Hp4096 & Hpceil).
pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
set (b0 := bv_unsigned (nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0))).
assert (Hb0 : aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + pos) = Some b0 /\ 0 <= b0 < 256).
{ assert (Hjl : (Z.to_nat pos < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat) by (rewrite length_map; unfold c_n in *; lia).
  destruct (HIN _ Hjl) as (Hv & Hr). rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by exact Hjl. rewrite map_nth in Hv, Hr.
  replace (c_p cx + Z.of_nat (Z.to_nat pos)) with (c_p cx + pos) in Hv by lia.
  split; [apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [exact Hv | exact Hr] | exact Hr]. }
destruct Hb0 as (Hb0 & Hb0r).
set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 b0])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 b0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; vm_compute; split; congruence).
assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (rewrite F32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite F33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x3a0 sr_atoms [C0I_Rsl (SLit 1); C0I_Rin [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] 1] None
  (C0I_F [(32%nat, mkAF 0 (2 ^ 47 - 2) 0); (33%nat, mkAF 0 255 0)])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp 0x3a0 ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold YP09.region_ok, C0I_Rsl. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ _ 0x88 8 (SOff 32 0) (c_p cx + pos)); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C88.
      * apply (chunk_ok_val SEGS E _ _ 0x90 8 (SLit 1) 1); [rewrite denot_lit_U, c0_U_lit_val by lia; reflexivity | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). rewrite <- HCASE. exact C90.
    + unfold YP09.region_ok, C0I_Rin. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 33 0) b0); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (proj1 (c0i_val_mem1 W3 (ms_mem ms3) _ _ Hb0)).
  - apply pairwise_disjoint_of_extents. unfold C0I_Rsl, C0I_Rin, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; exact I]. cbn [C0I_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, U32, U33. unfold C0I_SB. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hsp32 | reflexivity | lia]. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0I_SB, C0I_SB + 2 ^ 44 - 1).

{ assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  rewrite (c0_U_off_val E 18 SHADOW_OFF 0 F18) by (vm_compute; split; congruence).
  rewrite (c0_U_off_val E 32 (c_p cx + pos) 0 F32) by lia. rewrite !Z.add_0_r.
  exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) (c_p cx + pos) 1 HAR3 Hin3 ltac:(lia) ltac:(lia)). }

{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]. }

lazymatch type of HS with st_ok _ ?E2 _ _ => set (E1 := E2) in * end.
assert (EW : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; subst E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). intros (rr & Hrr & Hb). cbn [ss_mem In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi C0I_Rsl C0I_Rin base_val] in Hb; rewrite ?U9 in Hb; lia|]).
  destruct Hrr. }
clear HF HFr HG.
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 b0]) E1)
  by (split; [intros q Hq; rewrite EW by lia; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP : forall r0 : bv 5, In r0 c0i_kl -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
  by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W3) ms) (ms_regs ms3) _ c0i_kl HS HAE ltac:(vm_compute; reflexivity) r0 Hr)).
pose proof (st_ok_region_nth E1 _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS. rewrite pa_sigma_read_name.
change (SRr SEGS W3 (cfg_at SEGS A_read_nameP (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)) (POST cx)).

assert (Epl : c0_pl cx pos = [nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0)]).
{ rewrite (c0i_pl_cons cx pos) by lia. rewrite (c0i_pl_nil cx (pos + 1)) by lia. reflexivity. }
assert (Eu : LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) = 1) by (rewrite Epl; reflexivity).
assert (U9' : bv_unsigned (ew E1 9) = c_sp1 cx) by (rewrite EW by lia; exact U9).
assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite EW by lia; exact F32).
apply (c0i_call2 i POST cx fp k acc ly3 S3 W3 ms3 (ms_regs ms) (ms_mem ms) _ r bs pos op HN HB HJ HFR HMO HMF Hi Hk Hacc HBLK HREG HINV Hop Hop3 Hpos HGR R20 R22 R25 M1 KP).
- rewrite Eu. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x88 8 (SOff 32 1) (c_p cx + pos + 1) HRG eq_refl ltac:(cbn; tauto) ltac:(apply (c0_denot_off_val E1 32 (c_p cx + pos) 1 F32'); lia) ltac:(cbn; lia) ltac:(cbn; lia)).
- rewrite Eu. replace (c_n cx - pos - 1) with 0 by lia. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x90 8 (SLit 0) 0 HRG eq_refl ltac:(cbn; tauto) ltac:(rewrite denot_lit_U, c0_U_lit_val by lia; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)).
- exact Q1.
- rewrite Q10, U9'. reflexivity.
- rewrite Q19, EW by lia. rewrite F33. unfold c0_nch. rewrite Epl. reflexivity.
- rewrite Q26. unfold c0_base. rewrite Epl. reflexivity.
- rewrite Q27. unfold c0_base. rewrite Epl. reflexivity.
Qed.

Lemma c0i_n2 : forall i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op,
  gb_from B MT POST (C0_N B MT i) -> gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c0i_T i cx fp k acc ly3 S3 W3 ms3 r bs pos op -> 2 <= c_n cx - pos ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.

intros i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HI HCASE.
destruct HI as (HBODY & Hi & Hk & Hacc & HBLK & HREG & HPREV & HINV & Hop & Hop3 & R20 & R22 & R25 & R26 & HSR & HCUR & S68 & S48).
specialize (S48 ltac:(lia)).
pose proof HBODY as (Hpc & Hresv & Hsvc & Hrom & Hfregs & Hfcsr & HGR & HSV & HSH & Hshlen & HFL & HSF & HIN).
pose proof HGR as (G2 & G8 & G9 & G3 & G4 & G18 & G24).
pose proof HCUR as (Hpos & C88 & C90).
assert (HMS : c0_ms cx fp 0x3a0 ms3) by (repeat split; assumption).
assert (HMF : c0_mf i cx fp W3 ms3 r bs) by exact (conj HSV (conj HSH (conj HFL (conj HSF (conj HIN (conj HPREV (conj HSR (conj S68 S48)))))))).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBok.
pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
pose proof (c0_sp cx HB) as (Hsp & Hsp1 & Hsp32 & Hsp16). unfold GB_STK in Hsp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).

assert (Hn1 : 0 < c_n cx < 2 ^ 26 /\ In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ 4096 <= c_p cx /\ c_p cx + req_size (c_n cx) <= alloc_ceiling).
{ pose proof HB as (_ & _ & _ & Hinp & _). destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [lia|].
  assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _). split; [lia|]. split; [exact Hin3|]. lia. }
destruct Hn1 as (Hn1 & Hin3 & Hp4096 & Hpceil).
pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq].
set (b0 := bv_unsigned (nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0))).
set (b1 := bv_unsigned (nth (Z.to_nat (pos + 1)) (c_pl cx) (Z_to_bv 8 0))).
assert (BY : forall j, 0 <= j < c_n cx -> aview SEGS (w_H W3) (ms_mem ms3) (c_p cx + j) = Some (bv_unsigned (nth (Z.to_nat j) (c_pl cx) (Z_to_bv 8 0))) /\
  0 <= bv_unsigned (nth (Z.to_nat j) (c_pl cx) (Z_to_bv 8 0)) < 256).
{ intros j Hj. assert (Hjl : (Z.to_nat j < length (map (fun b : byte => bv_unsigned b) (c_pl cx)))%nat) by (rewrite length_map; unfold c_n in *; lia).
  destruct (HIN _ Hjl) as (Hv & Hr). rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hv, Hr by exact Hjl. rewrite map_nth in Hv, Hr.
  replace (c_p cx + Z.of_nat (Z.to_nat j)) with (c_p cx + j) in Hv by lia.
  split; [apply (aview_of_val_mem1 SEGS (w_H W3) (ms_mem ms3)); [exact Hv | exact Hr] | exact Hr]. }
destruct (BY pos ltac:(lia)) as (Hb0 & Hb0r). fold b0 in Hb0, Hb0r.
destruct (BY (pos + 1) ltac:(lia)) as (Hb1 & Hb1r). fold b1 in Hb1, Hb1r.
set (E := Eimg (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 (c_n cx - pos); Z_to_bv 64 b0; Z_to_bv 64 b1])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall q (r : bv 5), Z.of_nat q = bv_unsigned r -> ew E q = getr (ms_regs ms3) r)
  by (intros q r0 Hq; subst E; apply ew_Eimg_Ereg_nat; exact Hq).
assert (F32 : ew E 32 = Z_to_bv 64 (c_p cx + pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (F33 : ew E 33 = Z_to_bv 64 (c_n cx - pos)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (F34 : ew E 34 = Z_to_bv 64 b0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (F35 : ew E 35 = Z_to_bv 64 b1) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite (EE 9%nat 9%bv eq_refl), G9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl), G18; apply unsigned_lit_small; vm_compute; split; congruence).
assert (U32 : bv_unsigned (ew E 32) = c_p cx + pos) by (rewrite F32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = c_n cx - pos) by (rewrite F33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b0) by (rewrite F34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = b1) by (rewrite F35; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E (mkSS 0x3a0 sr_atoms [C0I_Rsl (SOff 33 0);
    C0I_Rin [YP09.mkChunk 0 (CVal 1 (SOff 34 0)); YP09.mkChunk 1 (CVal 1 (SOff 35 0))] 2] None
  (C0I_F [(32%nat, mkAF 0 (2 ^ 47 - 2) 0); (33%nat, mkAF 2 (2 ^ 26) 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)])) (restrict (w_H W3) ms3)).
{ rewrite (c0_mkst cx fp 0x3a0 ms3 (w_H W3) HMS). apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + unfold YP09.region_ok, C0I_Rsl. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ _ 0x88 8 (SOff 32 0) (c_p cx + pos)); [rewrite c0_denot_off0; exact F32 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C88.
      * apply (chunk_ok_val SEGS E _ _ 0x90 8 (SOff 33 0) (c_n cx - pos)); [rewrite c0_denot_off0; exact F33 | cbn; lia | cbn; lia |].
        apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms3)). exact C90.
    + unfold YP09.region_ok, C0I_Rin. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ _ 0 1 (SOff 34 0) b0); [rewrite c0_denot_off0; exact F34 | cbn; lia | cbn; lia |].
        rewrite Z.add_0_r. exact (proj1 (c0i_val_mem1 W3 (ms_mem ms3) _ _ Hb0)).
      * apply (chunk_ok_val SEGS E _ _ 1 1 (SOff 35 0) b1); [rewrite c0_denot_off0; exact F35 | cbn; lia | cbn; lia |].
        replace (c_p cx + pos + 1) with (c_p cx + (pos + 1)) by lia. exact (proj1 (c0i_val_mem1 W3 (ms_mem ms3) _ _ Hb1)).
  - apply pairwise_disjoint_of_extents. unfold C0I_Rsl, C0I_Rin, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - split; [|split; exact I]. cbn [C0I_F f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U18, U32, U33, U34, U35. unfold C0I_SB. change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | exact Hsp32 | reflexivity | lia]. }
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W3) (ms_mem ms3))) by constructor.
paj_run_tok (paj_run B LAWS) HS HJ SHOK (C0I_SB, C0I_SB + 2 ^ 44 - 1).

{ assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  rewrite (c0_U_off_val E 18 SHADOW_OFF 0 F18) by (vm_compute; split; congruence).
  rewrite (c0_U_off_val E 32 (c_p cx + pos) 1 F32) by lia. rewrite !Z.add_0_r.
  exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) (c_p cx + pos + 1) 1 HAR3 Hin3 ltac:(lia) ltac:(lia)). }

{ assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  rewrite (c0_U_off_val E 18 SHADOW_OFF 0 F18) by (vm_compute; split; congruence).
  rewrite (c0_U_off_val E 32 (c_p cx + pos) 0 F32) by lia. rewrite !Z.add_0_r.
  exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 (c_p cx) (c_n cx) (c_p cx + pos) 1 HAR3 Hin3 ltac:(lia) ltac:(lia)). }

{ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first [ apply awr_ok_nil
               | apply awr_ok_cons_ro; [cbn; lia|]
               | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                 [reflexivity | rewrite U9; lia | cbn; unfold GB_STK; lia | cbn; lia |] ]. }

lazymatch type of HS with st_ok _ ?E2 _ _ => set (E1 := E2) in * end.
assert (EW : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; subst E1; rewrite !ew_ewset_other by lia; reflexivity).
assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx + 0x88 <= a < c_sp1 cx + 0x98) ->
  aview SEGS (w_H W3) (ms_mem ms) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hn. apply (c0_keep_outside E _ _ _ (w_H W3) a HF Ha). intros (rr & Hrr & Hb). cbn [ss_mem In] in Hrr.
  repeat (destruct Hrr as [<- | Hrr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi C0I_Rsl C0I_Rin base_val] in Hb; rewrite ?U9 in Hb; lia|]).
  destruct Hrr. }
clear HF HFr HG.
assert (HAE : env_agree 32 (Ereg (ms_regs ms3) [Z_to_bv 64 (c_p cx + pos); Z_to_bv 64 (c_n cx - pos); Z_to_bv 64 b0; Z_to_bv 64 b1]) E1)
  by (split; [intros q Hq; rewrite EW by lia; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (KP : forall r0 : bv 5, In r0 c0i_kl -> getr (ms_regs ms) r0 = getr (ms_regs ms3) r0)
  by (intros r0 Hr; exact (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W3) ms) (ms_regs ms3) _ c0i_kl HS HAE ltac:(vm_compute; reflexivity) r0 Hr)).
pose proof (st_ok_region_nth E1 _ _ 0 _ HS eq_refl) as HRG. cbn [ms_mem restrict] in HRG.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (19%bv : bv 5) Q19.
prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
pmkst HS. rewrite pa_sigma_read_name.
change (SRr SEGS W3 (cfg_at SEGS A_read_nameP (ms_regs ms) (ms_mem ms) (with_vm_backing (m_vm_lazy md3) mat md3)) (POST cx)).

assert (Epl : c0_pl cx pos = nth (Z.to_nat pos) (c_pl cx) (Z_to_bv 8 0) :: nth (Z.to_nat (pos + 1)) (c_pl cx) (Z_to_bv 8 0) :: c0_pl cx (pos + 2)).
{ rewrite (c0i_pl_cons cx pos) by lia. rewrite (c0i_pl_cons cx (pos + 1)) by lia. replace (pos + 1 + 1) with (pos + 2) by lia. reflexivity. }
assert (Eu : LLVMFuzzerTestOneInput_case0.c0_used (c0_pl cx pos) = 2).
{ unfold LLVMFuzzerTestOneInput_case0.c0_used. rewrite (c0i_pl_len cx pos Hpos). lia. }
assert (U9' : bv_unsigned (ew E1 9) = c_sp1 cx) by (rewrite EW by lia; exact U9).
assert (F32' : ew E1 32 = Z_to_bv 64 (c_p cx + pos)) by (rewrite EW by lia; exact F32).
assert (F33' : ew E1 33 = Z_to_bv 64 (c_n cx - pos)) by (rewrite EW by lia; exact F33).
apply (c0i_call2 i POST cx fp k acc ly3 S3 W3 ms3 (ms_regs ms) (ms_mem ms) _ r bs pos op HN HB HJ HFR HMO HMF Hi Hk Hacc HBLK HREG HINV Hop Hop3 Hpos HGR R20 R22 R25 M1 KP).
- rewrite Eu. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x88 8 (SOff 32 2) (c_p cx + pos + 2) HRG eq_refl ltac:(cbn; tauto) ltac:(apply (c0_denot_off_val E1 32 (c_p cx + pos) 2 F32'); lia) ltac:(cbn; lia) ltac:(cbn; lia)).
- rewrite Eu. replace (c_n cx - pos - 2) with (c_n cx - pos + -2) by lia. apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  rewrite <- U9'. exact (field_of_region E1 _ 9%nat _ _ _ _ _ _ 0x90 8 (SOff 33 (-2)) (c_n cx - pos + -2) HRG eq_refl ltac:(cbn; tauto) ltac:(apply (c0_denot_off_val E1 33 (c_n cx - pos) (-2) F33'); lia) ltac:(cbn; lia) ltac:(cbn; lia)).
- exact Q1.
- rewrite Q10, U9'. reflexivity.
- rewrite Q19, EW by lia. rewrite F34. unfold c0_nch. rewrite Epl. reflexivity.
- rewrite Q26, EW by lia. rewrite F35. unfold b1. rewrite c0i_sl. unfold c0_base. rewrite Epl. reflexivity.
- rewrite Q27, EW by lia. rewrite F35. unfold b1. rewrite c0i_sl, c0i_sr. unfold c0_base. rewrite Epl. reflexivity.
Qed.

Theorem c0_inp : forall i POST, gb_from B MT POST (C0_N B MT i) -> gb_from B MT POST (GI_T B MT 0 i).
Proof.
intros i POST HN cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
destruct HI as (r & bs & pos & op & HI).
assert (HT : c0i_T i cx fp k acc ly3 S3 W3 ms3 r bs pos op) by exact HI.
pose proof HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hpos & _) & _).
destruct (Z.eq_dec (c_n cx - pos) 0) as [H0 | H0].
{ exact (c0i_n0 i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HT H0). }
destruct (Z.eq_dec (c_n cx - pos) 1) as [H1 | H1].
{ exact (c0i_n1 i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HT H1). }
exact (c0i_n2 i POST cx fp k acc ly3 S3 W3 ms3 md3 r bs pos op HN HB HJ HFR HMO HT ltac:(lia)).
Qed.

End c.
End b.
End a.
