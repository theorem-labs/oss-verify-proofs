(* One pass of diginet_counter_text's first loop in image B (segment L1 of diginet_counter_text_B_inv.v), split
   into three parts at two inner boundaries:
   a  0x86b74 .. : a dot after a digit whose dot is clear sets dot[n - 1] (to 0x86c28); every other byte runs to
      the call of diginet_seg7 (callee entry 0x86978, return address 0x86bc0).
   b  0x86978 .. : the call through diginet_seg7's contract, then E_RANGE (to 0x86dac) on a negative pattern or a
      ninth digit, else dot[n] := 1 for a dot, s[n] := pattern, n := n + 1 (to 0x86c28).
   c  0x86c28 .. : the next text byte: not 0 back to the loop head 0x86b74, 0 through the loop-2 set-up 0x86ca4 to
      the loop-2 head 0x86cd0.
   This file holds the two inner boundaries (P_C at the callee entry, P_N at 0x86c28), the three part statements
   and the facts every part takes from a boundary. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgEncU CPgChkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkU CPgWalkKeptU CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import diginet_counter_text_B_inv.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require ZBridge.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition PC_RET7 : Z := 0x86bc0.   (* mv a1,a0 after jal diginet_seg7 *)
Definition PC_NEXT : Z := 0x86c28.   (* li a0,-1: the checks of the next text byte *)
(* The character the loop draws: a dot draws as ' '. *)
Definition ct_c (ch : Z) : Z := if ch =? 46 then 32 else ch.
(* The pattern the first loop asks of diginet_seg7 for ch (the plain walk's ct1_v). *)
Definition ct1_v (ch : Z) : Z := seg7_spec (ct_c ch).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The bytes of the frame's two variables: s[8] at F + 32 and dot[8] at F + 64. *)
Definition ct_zv (g : ct_ctx) (pos a : Z) : Prop :=
  cg_F g pos + 32 <= a < cg_F g pos + 40 \/ cg_F g pos + 64 <= a < cg_F g pos + 96.

(* The callee entry 0x86978 of the call at 0x86bbc: ra = 0x86bc0, a0 = the character c (ct_c ch), s5 = ch, the
   loop's registers as at the head (t4 aside: the call does not keep it, 0x86bd4 reloads it), and the head's facts
   with the byte not a dot after a digit whose dot is clear. *)
Definition P_C (g : ct_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (j n ch : Z) (s dot : list Z),
    getr regs2 1 = w64 PC_RET7 /\ getr regs2 10 = w64 (ct_c ch) /\ getr regs2 21 = w64 ch /\
    getr regs2 20 = w64 46 /\
    getr regs2 22 = w64 (cg_q g + j) /\ getr regs2 23 = w64 (cg_q g + j + 1) /\
    getr regs2 25 = w64 n /\ getr regs2 27 = w64 (cg_F g pos + 32) /\
    getr regs2 18 = w64 (cw_not (cg_F g pos + 32)) /\ getr regs2 19 = w64 (cw_not (cg_F g pos + 64)) /\
    0 <= j /\ (Z.to_nat (cg_len g - j) <= S fuel)%nat /\
    nth (Z.to_nat j) (cg_tb g) 0 = ch /\ ch <> 0 /\ Forall (fun x => x <> 0) (firstn (S (Z.to_nat j)) (cg_tb g)) /\
    ct1_lib (skipn (Z.to_nat j) (cg_tb g)) n s dot = ct1_lib (cg_tb g) 0 [] (repeat 0 8) /\
    ~ (ch = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) /\
    ct_l1 n s dot /\ ct_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) /\ val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g).

(* 0x86c28, after byte j: the loop's registers (s6 = q + j, s7 = q + j + 1, the next byte's address), the bytes
   tb[0..j] not 0, and the first loop over the bytes after j from (n, s, dot) gives the result of the whole first
   loop. *)
Definition P_N (g : ct_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (j n : Z) (s dot : list Z),
    getr regs2 20 = w64 46 /\
    getr regs2 22 = w64 (cg_q g + j) /\ getr regs2 23 = w64 (cg_q g + j + 1) /\
    getr regs2 25 = w64 n /\ getr regs2 27 = w64 (cg_F g pos + 32) /\ getr regs2 29 = w64 (cg_F g pos + 64) /\
    getr regs2 18 = w64 (cw_not (cg_F g pos + 32)) /\ getr regs2 19 = w64 (cw_not (cg_F g pos + 64)) /\
    0 <= j /\ (Z.to_nat (cg_len g - j) <= S fuel)%nat /\
    Forall (fun x => x <> 0) (firstn (S (Z.to_nat j)) (cg_tb g)) /\
    ct1_lib (skipn (S (Z.to_nat j)) (cg_tb g)) n s dot = ct1_lib (cg_tb g) 0 [] (repeat 0 8) /\
    ct_l1 n s dot /\ ct_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) /\ val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI SEG7TBL : Z.

(* The three parts. *)
Definition ct_part_a : Prop :=
  forall g pos fuel W2 c2, ct_pre B g -> ct_now B RLO RHI SEG7TBL g ->
  ct_cut B MT g pos PC_L1 (P_L1 g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => ct_cut B MT g pos B_SEG7 (P_C g pos fuel) W3 c3 \/
                                   ct_cut B MT g pos PC_NEXT (P_N g pos fuel) W3 c3).
Definition ct_part_b : Prop :=
  forall g pos fuel W2 c2, ct_pre B g -> ct_now B RLO RHI SEG7TBL g ->
  ct_cut B MT g pos B_SEG7 (P_C g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => ct_cut B MT g pos PC_NEXT (P_N g pos fuel) W3 c3 \/
                                   ct_cut B MT g pos PC_X (P_X g) W3 c3).
Definition ct_part_c : Prop :=
  forall g pos fuel W2 c2, ct_pre B g -> ct_now B RLO RHI SEG7TBL g ->
  ct_cut B MT g pos PC_NEXT (P_N g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => ct_cut B MT g pos PC_L1 (P_L1 g pos fuel) W3 c3 \/
                                   ct_cut B MT g pos PC_L2 (P_L2 g pos 8) W3 c3).

(* The segment from its three parts. *)
Lemma ct_seg_L1_of_parts : ct_part_a -> ct_part_b -> ct_part_c -> ct_seg_L1 B MT RLO RHI SEG7TBL.
Proof.
intros HA HBp HC. unfold ct_seg_L1. intros g pos fuel W2 c2 Hpre Hnow Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HA g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H3 | H3].
- apply (SRr_bind tfibsegs _ _ _ _ (HBp g pos fuel W3 c3 Hpre Hnow H3)). intros W4 c4 _ [H4 | H4].
  + eapply SRr_mono; [exact (HC g pos fuel W4 c4 Hpre Hnow H4)|].
    intros W5 c5 _ [H5 | H5]; [left; exact H5 | right; left; exact H5].
  + apply SRr_ret. right; right. exact H4.
- eapply SRr_mono; [exact (HC g pos fuel W3 c3 Hpre Hnow H3)|].
  intros W5 c5 _ [H5 | H5]; [left; exact H5 | right; left; exact H5].
Qed.

Section l.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The stack of the call: the entry sp, the realigned sp1, the window. *)
Lemma ctl_stack : forall g, ct_pre B g ->
  alloc_ceiling <= cg_sp g - TB_counter_text /\ cg_sp g <= 2 ^ 47 /\ 2 ^ 46 + TB_counter_text <= cg_sp g /\
  cg_sp g mod 16 = 0 /\ cg_sp g - 224 <= cg_sp1 g <= cg_sp g - 192 /\ cg_sp1 g mod 32 = 0 /\
  cg_sp0 g - cg_STK g <= cg_sp g - TB_counter_text /\ cg_sp g <= cg_sp0 g.
Proof.
intros g Hpre. pose proof Hpre as (HE & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_counter_text HE ltac:(unfold TB_counter_text, ESTACK; lia))
  as (Hceil & H47 & H46 & Hal & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & Hwin & Hwhi & _).
unfold cg_sp1. fold (cg_sp g) in *. unfold spZ in *. fold (cg_sp g) in *.
pose proof (Z.div_mod (cg_sp g - 192) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (cg_sp g - 192) 32 ltac:(lia)) as M.
split; [exact Hceil|]. split; [exact H47|]. split; [exact H46|]. split; [exact Hal|].
split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; assumption.
Qed.

(* The walk's own frame at a boundary state. *)
Lemma ctl_frame : forall g pos ly2 S2 W2 mem2 md2, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  frames S2 = (1, pos) :: frames (cg_Sc g) /\
  (forall c p, frame_addr ly2 c p = frame_addr (cg_lyc g) c p) /\
  (forall c p, flag_addr ly2 c p = flag_addr (cg_lyc g) c p) /\
  4096 <= cg_F g pos /\ cg_F g pos + 128 <= alloc_ceiling /\ cg_F g pos mod 64 = 0 /\ in_app (cg_F g pos) 128 /\
  (forall a, cg_F g pos <= a < cg_F g pos + 128 -> apresent (w_H W2) mem2 a).
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
pose proof Hpre as ((HJc & _) & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (EF : ly_F ly2 = ly_F (cg_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr (cg_lyc g) c p) by (intros c p; unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr (cg_lyc g) c p) by (intros c p; unfold flag_addr; rewrite EF; reflexivity).
assert (Hfr : frames S2 = (1, pos) :: frames (cg_Sc g)) by (rewrite Hfrs2, Hfrsc; reflexivity).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H4096 & Hceil & Happ).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (_ & _ & HFp & _).
change (fs_frame_bytes 1) with 128 in Hceil, Happ, HFp.
rewrite Efa in H4096, Hceil, Happ, H64, HFp. fold (cg_F g pos) in H4096, Hceil, Happ, H64, HFp.
split; [exact Hfr|]. split; [exact Efa|]. split; [exact Efl|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H64|]. split; [exact Happ|].
intros a Ha. exact (proj1 (HFp a Ha)).
Qed.

(* A byte of the frame's variables is fresh for the call state. *)
Lemma ctl_fresh : forall g pos ly2 S2 W2 mem2 md2 a, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  ct_zv g pos a -> cw_fresh B (cg_lyc g) (cg_Sc g) a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha.
destruct (ctl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR2 & _).
apply (cw_fresh_own B LAWS (cg_lyc g) (cg_Sc g) ly2 S2 W2 mem2 md2 1 pos a HAR2 Hfr HP Efa).
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (cg_F g pos). change (fs_frame_bytes 1) with 128.
unfold ct_zv in Ha. lia.
Qed.
(* A byte the caller lets the call write (a block or a frame of the call state) is not one of them. *)
Lemma ctl_dst_not_zv : forall g pos ly2 S2 W2 mem2 md2 q n a, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  tdst_ok B (cg_lyc g) (cg_Sc g) q n -> q <= a < q + n -> ~ ct_zv g pos a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 q n a Hpre HJ HP Hd Ha Hz.
destruct (ctl_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hz) as (_ & _ & Hfb & Hff).
destruct (Hd a Ha) as [(bb & m & Hin & Hr) | (cid & p & Hin & Hr)].
- apply (Hfb bb m (a - bb) Hin); lia.
- exact (proj1 (Hff cid p Hin) Hr).
Qed.
Lemma ctl_rdword_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  rdword (aview tfibsegs H m) a = Some v -> rdword (aview tfibsegs H' m') a = Some v.
Proof.
intros H H' m m' a v Hk Hr. unfold rdword in *.
rewrite (Hk a), (Hk (a + 1)), (Hk (a + 2)), (Hk (a + 3)), (Hk (a + 4)), (Hk (a + 5)), (Hk (a + 6)), (Hk (a + 7))
  by lia. exact Hr.
Qed.
Lemma ctl_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q l,
  (forall x, q <= x < q + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cw_val_mem_kept H H' m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros x Hx. apply Hk. lia.
Qed.

(* What a boundary carries, kept by a run that changes no byte outside the frame's variables and none of the
   seven registers of ct_common. *)
Lemma ctl_keep : forall g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  ct_common g pos regs2 mem2 W2 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 26 = getr regs2 26 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ct_zv g pos a -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem3 (cg_sp g) (ct_wr g) /\
  ct_common g pos regs3 mem3 W2 /\
  (garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) -> garr8 tfibsegs (rd W2 mem3) (cg_sg g) (cg_sj g)) /\
  (val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g) -> val_mem tfibsegs (rd W2 mem3) (cg_dt g) 1 (cg_dj g)).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 Hpre HJ HP HK HC E8 E2 E9 E3 E4 E24 E26 KE KP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ctl_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ctl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as ((HJc & _) & _ & _ & _ & (Hsg0 & Hsg63 & Hsgd & _) & _ & _ & _ & (Hdt0 & Hdt63 & Hdtd & _) & _).
pose proof (proj1 HJc) as HARc.
assert (HF8 : cg_F g pos = 8 * (cg_F g pos / 8)).
{ pose proof (Z.div_mod (cg_F g pos) 64 ltac:(lia)) as D. pose proof (Z.div_mod (cg_F g pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (cg_F g pos) 8 ltac:(lia)) as M8. lia. }
unfold TB_counter_text, ESTACK in Hceil, Hwin, H46.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply KE; [lia|]. unfold ct_zv. lia. }
split.
{ apply (cw_kept_step B LAWS TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) (cg_mdc g) W2 mem2 mem3
    (cg_sp g) (ct_wr g) (ct_zv g pos)); [unfold TB_counter_text, ESTACK; lia | exact HARc | exact HK | exact KE | | exact KP].
  intros a Ha. right; right. exact (ctl_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha). }
split.
{ destruct HC as (R8 & R2 & R9 & R3 & R4 & R24 & R26 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 &
    V13 & V14 & V15 & V16 & V17 & V18 & Hfl & Hsh).
  split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
  split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E24; exact R24|].
  split; [rewrite E26; exact R26|].
  repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [intros x Hx; apply KH; cbn in Hx; lia | assumption]|]).
  split.
  - apply (ctl_rdword_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hfl]. intros x Hx. apply KE; [lia|]. unfold ct_zv. lia.
  - apply (ctl_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length CT_FRAME_SHADOW] in Hx.
    change (Z.of_nat 16) with 16 in Hx.
    apply KE; [unfold SB in *; lia|]. unfold ct_zv, SB in *. lia. }
split.
{ apply (ctl_garr8_kept (w_H W2) (w_H W2) mem2 mem3). intros x Hx.
  assert (Lsj : length (cg_sj g) = 8%nat) by (pose proof Hpre as (_ & _ & _ & _ & _ & _ & L & _); exact L).
  rewrite Lsj in Hx. change (Z.of_nat 8) with 8 in Hx.
  apply KE; [lia|]. exact (ctl_dst_not_zv g pos ly2 S2 W2 mem2 md2 (cg_sg g) 8 x Hpre HJ HP Hsgd Hx). }
{ apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3). intros x Hx. cbn in Hx.
  apply KE; [lia|]. exact (ctl_dst_not_zv g pos ly2 S2 W2 mem2 md2 (cg_dt g) 1 x Hpre HJ HP Hdtd Hx). }
Qed.

(* A boundary at the end of a run of the segment: the run kept the journal's layout and state, wrote only bytes of
   the frame's variables, kept the seven registers; P holds of the new state given seg and dt as before. *)
Lemma ctl_cut_close : forall g pos pc (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
    world tfibsegs -> Prop) ly2 S2 regs2 mem2 md2 W2 ms md3,
  ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  tcj_kept tfibsegs B TB_counter_text (cg_lyc g) (cg_Sc g) (cg_W g) (cg_memc g) W2 mem2 (cg_sp g) (ct_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) -> ~ In (1, pos) (frames (cg_Sc g)) ->
  same_io (cg_mdc g) md2 -> mo_le MT (cg_Sc g) S2 0 -> ct_common g pos regs2 mem2 W2 ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 (ms_mem ms) md3 (cg_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  getr (ms_regs ms) 8 = getr regs2 8 -> getr (ms_regs ms) 2 = getr regs2 2 -> getr (ms_regs ms) 9 = getr regs2 9 ->
  getr (ms_regs ms) 3 = getr regs2 3 -> getr (ms_regs ms) 4 = getr regs2 4 ->
  getr (ms_regs ms) 24 = getr regs2 24 -> getr (ms_regs ms) 26 = getr regs2 26 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ct_zv g pos a ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) ->
  garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) -> val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g) ->
  (garr8 tfibsegs (rd W2 (ms_mem ms)) (cg_sg g) (cg_sj g) ->
   val_mem tfibsegs (rd W2 (ms_mem ms)) (cg_dt g) 1 (cg_dj g) ->
   P ly2 S2 (ms_regs ms) (ms_mem ms) md3 W2) ->
  ct_cut B MT g pos pc P W2 (mkCfg ms md3).
Proof.
intros g pos pc P ly2 S2 regs2 mem2 md2 W2 ms md3 Hpre HJ HK HP Hni Hio Hmo HC HJ3 Hio3 Hms E8 E2 E9 E3 E4 E24 E26
  KE KP Hsj Hdj HPk.
destruct (ctl_keep g pos ly2 S2 regs2 mem2 md2 W2 (ms_regs ms) (ms_mem ms) Hpre HJ HP HK HC E8 E2 E9 E3 E4 E24 E26 KE KP)
  as (HK3 & HC3 & Ksj & Kdj).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact HK3|]. split; [exact HP|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|]. split; [exact HC3|].
exact (HPk (Ksj Hsj) (Kdj Hdj)).
Qed.

(* The usable marks of the frame's variables, from the frame's shadow bytes. *)
Lemma ctl_ra_var : forall (H : word -> bool) (m : word -> option byte) F lo len, F mod 8 = 0 -> 0 <= F ->
  ((32 <= lo /\ lo + len <= 40) \/ (64 <= lo /\ lo + len <= 96)) ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) CT_FRAME_SHADOW ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF (F + lo) len.
Proof.
intros H m F lo len HF8 HF0 Hlo Hsh x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Ex : x / 8 = F / 8 + (x - F) / 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
assert (Hk : (x - F) / 8 = 4 \/ (x - F) / 8 = 8 \/ (x - F) / 8 = 9 \/ (x - F) / 8 = 10 \/ (x - F) / 8 = 11).
{ assert (L1 : 4 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (x - F) / 8 < 12) by (apply Z.div_lt_upper_bound; lia).
  destruct Hlo as [Hlo | Hlo].
  - assert (L3 : (x - F) / 8 < 5) by (apply Z.div_lt_upper_bound; lia). lia.
  - assert (L3 : 8 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia). lia. }
rewrite Ex. rewrite <- SB_SHADOW_OFF.
assert (G : forall k, k = 4 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 ->
  aview tfibsegs H m (SB + F / 8 + k) = Some 0).
{ intros k Hk'. apply (aview_of_val_mem1 tfibsegs H m (SB + F / 8 + k) 0); [|lia].
  destruct Hk' as [-> | [-> | [-> | [-> | ->]]]];
  [ exact (proj1 (Hsh 4%nat ltac:(cbn; lia)))
  | exact (proj1 (Hsh 8%nat ltac:(cbn; lia)))
  | exact (proj1 (Hsh 9%nat ltac:(cbn; lia)))
  | exact (proj1 (Hsh 10%nat ltac:(cbn; lia)))
  | exact (proj1 (Hsh 11%nat ltac:(cbn; lia))) ]. }
rewrite Z.add_assoc. exact (G _ Hk).
Qed.

(* ch & 255 for a byte *)
Lemma ctl_land255 : forall ch, 0 <= ch < 256 -> Z.land ch 255 = ch.
Proof.
intros ch Hch. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia.
Qed.
(* s11 + s9, the address of s[n] (0x86c1c) *)
Lemma ctl_den_add : forall E (b c : nat) x n, ew E b = Z_to_bv 64 x -> ew E c = Z_to_bv 64 n ->
  0 <= x -> 0 <= n -> x + n < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff b 0) (SOff c 0)) = Z_to_bv 64 (x + n).
Proof. intros E b c x n Hb Hc Hx Hn Hxn. apply denot_add2; assumption. Qed.
Lemma ctl_nth_upd_same : forall (l : list Z) i v, (Z.to_nat i < length l)%nat -> nth (Z.to_nat i) (upd_at l i v) 0 = v.
Proof.
intros l i v Hi. unfold upd_at. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length l))%nat with 0%nat by lia. reflexivity.
Qed.
(* The plain walk's step lemmas of the first loop (lib/Spec/DgnLib.v ct1_lib). *)
Lemma ctl_ct1_dotset : forall rest n s dot, 0 < n -> nth (Z.to_nat (n - 1)) dot 0 = 0 ->
  ct1_lib (46 :: rest) n s dot = ct1_lib rest n s (upd_at dot (n - 1) 1).
Proof.
intros rest n s dot Hn Hd. cbn [ct1_lib]. rewrite (proj2 (Z.ltb_lt 0 n) Hn), Hd. reflexivity.
Qed.
Lemma ctl_ct1_digit : forall ch rest n s dot, ch <> 0 ->
  ~ (ch = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) ->
  ct1_lib (ch :: rest) n s dot =
    if (ct1_v ch <? 0) || (n =? 8) then None
    else ct1_lib rest (n + 1) (s ++ [ct1_v ch]) (if ch =? 46 then upd_at dot n 1 else dot).
Proof.
intros ch rest n s dot H0 Hd. cbn [ct1_lib]. rewrite (proj2 (Z.eqb_neq ch 0) H0).
destruct ((ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) eqn:E; [|reflexivity].
exfalso. apply Hd. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. auto.
Qed.
Lemma ctl_Forall_upd_at : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_at l i v).
Proof.
intros P l i v H Hv. unfold upd_at.
pose proof (firstn_skipn (Z.to_nat i) l) as E1. pose proof (firstn_skipn (S (Z.to_nat i)) l) as E2.
assert (H1 : Forall P (firstn (Z.to_nat i) l)) by (rewrite <- E1 in H; apply Forall_app in H; tauto).
assert (H2 : Forall P (skipn (S (Z.to_nat i)) l)) by (rewrite <- E2 in H; apply Forall_app in H; tauto).
apply Forall_app. split; [exact H1 | constructor; assumption].
Qed.
(* The byte j of the text exists and is a byte: the bytes up to j are not 0 and the text holds a 0. *)
Lemma ctl_tb_len : forall (tb : list Z) j, 0 <= j -> In 0 tb ->
  Forall (fun x => x <> 0) (firstn (S (Z.to_nat j)) tb) -> j + 1 < Z.of_nat (length tb).
Proof.
intros tb j Hj Hin Hf.
destruct (Nat.lt_ge_cases (S (Z.to_nat j)) (length tb)) as [Hl | Hl]; [lia|].
exfalso. rewrite firstn_all2 in Hf by exact Hl. rewrite Forall_forall in Hf. exact (Hf 0 Hin eq_refl).
Qed.
(* blez s11 (bge zero,s11) on 0 <= n <= 8 *)
Lemma ctl_bge0 : forall E k n, ew E k = Z_to_bv 64 n -> 0 <= n <= 8 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff k 0)) = (n <=? 0).
Proof.
intros E k n Hk Hn. rewrite sv_denot_SOff0, Hk. cbn [sv_denot branch_taken].
rewrite ZBridge.bv_lts_zero_l, unsigned_lit_small by lia.
destruct (Z.leb_spec n 0); destruct (Z.ltb_spec 0 n); cbn; try reflexivity; lia.
Qed.
(* The frame's variables kept by a run that wrote none of them. *)
Lemma ctl_arrays_kept : forall g pos W2 mem2 mem3 n s dot,
  (forall a, cg_F g pos <= a < cg_F g pos + 128 -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  n <= 8 -> ct_arrays g pos W2 mem2 n s dot -> ct_arrays g pos W2 mem3 n s dot.
Proof.
intros g pos W2 mem2 mem3 n s dot KF Hn (Hd & Hs). split.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)]. intros x Hx. apply KF. cbn in Hx. lia.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hs i Hi)]. intros x Hx. apply KF. cbn in Hx. lia.
Qed.
(* ... and with the word dot[n - 1] (at F + 60 + 4 n) now v. *)
Lemma ctl_arrays_word : forall g pos W2 mem2 mem3 n s dot v, 1 <= n <= 8 -> length dot = 8%nat ->
  (forall a, cg_F g pos <= a < cg_F g pos + 128 -> ~ (cg_F g pos + 60 + 4 * n <= a < cg_F g pos + 64 + 4 * n) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (rd W2 mem3) (cg_F g pos + 60 + 4 * n) 4 v ->
  ct_arrays g pos W2 mem2 n s dot -> ct_arrays g pos W2 mem3 n s (upd_at dot (n - 1) v).
Proof.
intros g pos W2 mem2 mem3 n s dot v Hn Hl KF Hv (Hd & Hs). split.
- intros i Hi. destruct (Z.eq_dec i (n - 1)) as [-> | Hne].
  + rewrite ctl_nth_upd_same by lia. replace (cg_F g pos + 64 + 4 * (n - 1)) with (cg_F g pos + 60 + 4 * n) by lia.
    exact Hv.
  + rewrite nth_upd_other by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)].
    intros x Hx. cbn in Hx. apply KF; lia.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hs i Hi)].
  intros x Hx. cbn in Hx. apply KF; lia.
Qed.
(* ... and with s[n] := v (byte at F + 32 + n) and, for a dot, dot[n] := 1 (word at F + 64 + 4 n). *)
Lemma ctl_arrays_next : forall g pos W2 mem2 mem3 n s dot dot' v (isdot : bool), 0 <= n < 8 ->
  length s = Z.to_nat n -> length dot = 8%nat ->
  dot' = (if isdot then upd_at dot n 1 else dot) ->
  (forall a, cg_F g pos <= a < cg_F g pos + 128 -> a <> cg_F g pos + 32 + n ->
     ~ (isdot = true /\ cg_F g pos + 64 + 4 * n <= a < cg_F g pos + 68 + 4 * n) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (rd W2 mem3) (cg_F g pos + 32 + n) 1 v ->
  (isdot = true -> val_mem tfibsegs (rd W2 mem3) (cg_F g pos + 64 + 4 * n) 4 1) ->
  ct_arrays g pos W2 mem2 n s dot -> ct_arrays g pos W2 mem3 (n + 1) (s ++ [v]) dot'.
Proof.
intros g pos W2 mem2 mem3 n s dot dot' v isdot Hn Hsl Hl -> KF Hv Hd1 (Hd & Hs). split.
- intros i Hi. destruct isdot.
  + destruct (Z.eq_dec i n) as [-> | Hne].
    * rewrite ctl_nth_upd_same by lia. exact (Hd1 eq_refl).
    * rewrite nth_upd_other by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)].
      intros x Hx. cbn in Hx. apply KF; [lia | lia | intros (_ & Hx'); lia].
  + apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)].
    intros x Hx. cbn in Hx. apply KF; [lia | lia | intros (Hf & _); discriminate Hf].
- intros i Hi. destruct (Z.eq_dec i n) as [-> | Hne].
  + rewrite app_nth2 by lia. rewrite Hsl. replace (Z.to_nat n - Z.to_nat n)%nat with 0%nat by lia. exact Hv.
  + rewrite app_nth1 by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hs i ltac:(lia))].
    intros x Hx. cbn in Hx. apply KF; [lia | lia | intros (_ & Hx'); lia].
Qed.
(* a callee-saved register after an own callee *)
Lemma ctl_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
(* What a boundary carries, kept across the call of diginet_seg7 (its post's tcj_kept, window [sp1 - 16, sp1),
   nothing written), with the seven registers preserved. *)
Lemma ctl_keep_call : forall g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3, ct_pre B g ->
  ajournal tfibsegs B (cg_STK g) (cg_sp0 g) (cg_FP g) (cg_ly g) (cg_S g) (cg_W0 g) (cg_mem0 g) (cg_md0 g)
    ((1, pos) :: cg_own g) ly2 S2 W2 mem2 md2 (cg_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (cg_lyc g) (cg_Sc g)) ->
  ct_common g pos regs2 mem2 W2 ->
  tcj_kept tfibsegs B TB_seg7 ly2 S2 W2 mem2 W3 mem3 (cg_sp1 g) cno_wr ->
  getr regs3 8 = getr regs2 8 -> getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 24 = getr regs2 24 ->
  getr regs3 26 = getr regs2 26 ->
  ct_common g pos regs3 mem3 W3 /\
  (forall a, cg_F g pos <= a < cg_F g pos + 128 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) /\
  (garr8 tfibsegs (rd W2 mem2) (cg_sg g) (cg_sj g) -> garr8 tfibsegs (rd W3 mem3) (cg_sg g) (cg_sj g)) /\
  (val_mem tfibsegs (rd W2 mem2) (cg_dt g) 1 (cg_dj g) -> val_mem tfibsegs (rd W3 mem3) (cg_dt g) 1 (cg_dj g)).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3 Hpre HJ HP HC (K1 & K2 & _ & K4 & _) E8 E2 E9 E3 E4 E24 E26.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (ctl_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ctl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as (_ & _ & _ & _ & (Hsg0 & Hsg63 & Hsgd & _) & _ & Lsj & _ & (Hdt0 & Hdt63 & Hdtd & _) & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
unfold TB_counter_text, ESTACK in Hceil, Hwin, H46.
assert (KH : forall x, cg_sp1 g <= x < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply K1; [lia | lia | intros []]. }
assert (KZ : forall x, (in_zr x (frame_rng ly2 (1, pos)) \/
    in_zr x (shadow_addr (frame_addr ly2 1 pos), fs_frame_bytes 1 / 8)) ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply (K4 1 pos x Hin Hx). intros []. }
assert (KF : forall a, cg_F g pos <= a < cg_F g pos + 128 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply KZ. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes 1) with 128.
  fold (cg_F g pos). lia. }
assert (HF8 : cg_F g pos = 8 * (cg_F g pos / 8)).
{ pose proof (Z.div_mod (cg_F g pos) 64 ltac:(lia)) as D. pose proof (Z.div_mod (cg_F g pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (cg_F g pos) 8 ltac:(lia)) as M8. lia. }
(* a byte of an object the caller lets the call write *)
assert (KD : forall q n x, tdst_ok B (cg_lyc g) (cg_Sc g) q n -> q <= x < q + n ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros q n x Hd Hx. destruct (Hd x Hx) as [(bb & m & Hb & Hr) | (cid & p & Hcp & Hr)].
  - replace x with (bb + (x - bb)) by lia.
    apply (K2 bb m (x - bb) (Permutation_in _ (Permutation_sym HP) Hb)); [lia | intros []].
  - apply (K4 cid p x); [rewrite Hfr; right; exact Hcp | | intros []].
    left. unfold in_zr, frame_rng in *. cbn [fst snd] in *. rewrite Efa. exact Hr. }
split.
{ destruct HC as (R8 & R2 & R9 & R3 & R4 & R24 & R26 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 &
    V13 & V14 & V15 & V16 & V17 & V18 & Hfl & Hsh).
  split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
  split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E24; exact R24|].
  split; [rewrite E26; exact R26|].
  repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [intros x Hx; apply KH; cbn in Hx; lia | assumption]|]).
  split.
  - apply (ctl_rdword_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hfl]. intros x Hx. apply KF. lia.
  - apply (ctl_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length CT_FRAME_SHADOW] in Hx.
    change (Z.of_nat 16) with 16 in Hx. apply KZ. right. unfold in_zr, shadow_addr. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes 1 / 8) with 16. fold (cg_F g pos). rewrite <- SB_SHADOW_OFF. lia. }
split; [exact KF|].
split.
{ apply (ctl_garr8_kept (w_H W2) (w_H W3) mem2 mem3). intros x Hx. rewrite Lsj in Hx. change (Z.of_nat 8) with 8 in Hx.
  exact (KD (cg_sg g) 8 x Hsgd Hx). }
{ apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3). intros x Hx. cbn in Hx. exact (KD (cg_dt g) 1 x Hdtd Hx). }
Qed.
(* bltz on seg7's pattern: -1 or a byte below 128 *)
Lemma ctl_blt0 : forall E k v, ew E k = Z_to_bv 64 v -> -1 <= v < 128 ->
  branch_taken BC_LT (sv_denot E (SOff k 0)) (sv_denot E (SLit 0)) = (v <? 0).
Proof.
intros E k v Hk Hv. rewrite sv_denot_SOff0, Hk. cbn [sv_denot branch_taken].
rewrite ZBridge.bv_lts_zero_r. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec v 0).
- assert (v = -1) as -> by lia. reflexivity.
- rewrite Z.mod_small by lia. apply Z.leb_gt. lia.
Qed.

End l.
End h.
End d.

(* ---- tactics of the three parts ---------------------------------------------------------------------------------- *)
Ltac awr_nil := cbn [ss_mem]; apply awr_ok_nil.
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
(* rewrite the goal's register r of the stopped state by its symbolic value *)
Ltac rv := lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let R := fresh "R" in rreg HS r R; rewrite R; clear R end.
(* hypotheses found by their form: the start env (Ereg), atom 32 = SB, s10 = SB, atom 11 = ch, atom 33 = the dot word *)
Ltac hEE := lazymatch goal with H : ?Ev = Ereg _ _ |- _ => rewrite H end.
Ltac hE32 := lazymatch goal with H : ew _ 32 = Z_to_bv 64 SB |- _ => rewrite H end.
Ltac hR26 := lazymatch goal with H : getr _ 26 = w64 SB |- _ => exact (eq_sym H) end.
Ltac hE11 := lazymatch goal with H : ew _ 11 = Z_to_bv 64 _ |- _ => exact H end.
Ltac hE33 := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H end.
Ltac hE33_in Hb := lazymatch goal with H : ew _ 33 = Z_to_bv 64 _ |- _ => rewrite H in Hb end.
Ltac hEfa := lazymatch goal with H : forall c p, frame_addr ?l c p = frame_addr _ c p |- context [frame_addr ?l _ _] =>
  rewrite H end.
Ltac hFa := lazymatch goal with H : frame_addr _ 1 _ = _ |- _ => rewrite H end.
(* a register of the stopped state: a literal, or an atom of the start (the boundary's register, or SB in atom 32) *)
Ltac rfin := rv; first
  [ reflexivity
  | rewrite ?sv_denot_SOff0; ewpeel;
    first [ hEE; apply ew_Ereg_nat; reflexivity | hE32; hR26 | assumption ] ].
(* the register as sv_denot of its symbolic value, unsimplified *)
Ltac rv0 := lazymatch goal with HS : YP0l.st_ok ?segs ?Ev ?ss (restrict ?H ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  let R := fresh "R" in
  assert (R : getr (ms_regs msv) r = sv_denot Ev e)
    by (refine (eq_trans (st_ok_restrict_reg segs H Ev ss msv r HS) _); reflexivity);
  rewrite R; clear R end.
(* zext.b of a1 = ch: s5 and a0 at the call *)
Ltac rand := rv0; lazymatch goal with HS : YP0l.st_ok _ ?Ev _ _ |- _ =>
  rewrite denot_lit_U, U_and_lit, (U_atom Ev 11 _ ltac:(ewpeel; hE11) ltac:(lia)), ctl_land255 by lia end.
(* the model's same_io through the runs' materializations *)
Ltac kio := first [ apply same_io_refl | eapply same_io_trans; [| apply cw_same_io_wvb]; kio ].
(* fold a run's growth into KP, its frame into KE *)
Ltac ctk_keep kwr :=
  lazymatch goal with HG : mem_grows (mrestrict ?H ?m1) (mrestrict ?H ?m2),
                      KP : forall a, apresent ?H ?m0 a -> apresent ?H ?m1 a |- _ =>
    let KQ := fresh "KQ" in
    assert (KQ : forall a, apresent H m0 a -> apresent H m2 a)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; eapply apresent_grows; [exact HG | exact (KP a Ha)]);
    clear KP; rename KQ into KP end;
  cw_keep kwr.
