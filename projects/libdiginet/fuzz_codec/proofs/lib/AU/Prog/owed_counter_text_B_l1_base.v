(* One pass of owed_counter_text's first loop in image B (segment L1 of owed_counter_text_B_inv.v), split into three
   parts at two inner boundaries:
   a  0x845d4 .. : the check and the load of the byte t[i] (0x845d4 .. 0x845e4); 0 ends the text (to 0x84728); a dot
      after a digit whose dot is clear sets dot[n - 1] (0x845f4 .. 0x84624, 0x846bc .. 0x846cc) and goes on to the
      next byte (0x846a8 .. 0x846b4, back to 0x845d4); every other byte runs to the call of owed_seg7 (callee entry
      0x84a54, return address 0x84634; a dot draws as ' ').
   b  0x84a54 .. : the call through owed_seg7's contract, then E_RANGE (to 0x84840) on a negative pattern or a ninth
      digit, else dot[n] := (t[i] is '.'), s[n] := pattern, n := n + 1 and the next byte (back to 0x845d4).
   e  0x84728 .. : the check of dt, *dt := 0, the loop-2 registers, to the loop-2 head 0x84764.
   This file holds the two inner boundaries (P_C at the callee entry, P_E at 0x84728), the three part statements, the
   segment from them, and the facts every part takes from a boundary. The form is
   lib/A/Prog/diginet_counter_text_A_l1_base.v's. *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_text codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU CPgWalkCallU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import owed_counter_text_B_inv owed_counter_text_B_s0_a.
(* DgnLib has another `st_ok`: take YP0l's back. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Definition PC_RET7 : Z := 0x84634.   (* mv a1,a0 after jal owed_seg7 *)
Definition PC_E : Z := 0x84728.      (* ld a0,40(s1): the text's end *)
(* The character the first loop draws: a dot draws as ' '. *)
Definition oc_c (ch : Z) : Z := if ch =? 46 then 32 else ch.
(* The pattern the first loop asks of owed_seg7 for ch. *)
Definition oc_v (ch : Z) : Z := owed_seg7_spec (oc_c ch).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).

(* The bytes of the frame's two variables: s[8] at F + 32 and dot[8] at F + 64. *)
Definition oc_zv (g : oc_ctx) (pos a : Z) : Prop :=
  og_F g pos + 32 <= a < og_F g pos + 40 \/ og_F g pos + 64 <= a < og_F g pos + 96.

(* The callee entry 0x84a54 of the call at 0x84630: ra = 0x84634, a0 = the character (oc_c ch), s9 = the shadow byte
   address of t[i], the loop's registers as at the head, and the head's facts with t[i] = ch, not 0 and not a dot
   after a digit whose dot is clear. *)
Definition P_C (g : oc_ctx) (pos : Z) (fuel : nat) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (i n ch : Z) (s dot : list Z),
    getr regs2 1 = w64 PC_RET7 /\ getr regs2 10 = w64 (oc_c ch) /\
    getr regs2 19 = w64 n /\ getr regs2 20 = w64 (og_q g + i) /\ getr regs2 22 = w64 (og_q g + i - 1) /\
    getr regs2 25 = w64 (SB + (og_q g + i) / 8) /\
    0 <= i /\ (Z.to_nat (og_len g - i) <= S fuel)%nat /\
    nth (Z.to_nat i) (og_tb g) 0 = ch /\ ch <> 0 /\ Forall (fun x => x <> 0) (firstn (Z.to_nat i) (og_tb g)) /\
    ct1_owe (skipn (Z.to_nat i) (og_tb g)) n s dot = ct1_owe (og_tb g) 0 [] (repeat 0 8) /\
    ~ (ch = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) /\
    oc_l1 n s dot /\ oc_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) /\ val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 (og_dj g).

(* 0x84728, the text's end: s3 = n, the first loop's result (n, s, dot), its arrays; seg and dt as at entry. *)
Definition P_E (g : oc_ctx) (pos : Z) : alayout -> astate -> bvmap 5 word -> (word -> option byte) ->
  Model -> world tfibsegs -> Prop :=
  fun ly2 S2 regs2 mem2 md2 W2 => exists (n : Z) (s dot : list Z),
    getr regs2 19 = w64 n /\
    owed_counter_text_spec (og_tb g) = ct2 n s dot /\
    oc_l1 n s dot /\ oc_arrays g pos W2 mem2 n s dot /\
    garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) /\ val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 (og_dj g).

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables RLO RHI GLYPHA : Z.
Variable ROSTRS : list (Z * Z).

(* The three parts. *)
Definition oc_part_a : Prop :=
  forall g pos fuel W2 c2, oc_pre B g -> oc_now B RLO RHI GLYPHA ROSTRS g ->
  oc_cut B MT g pos PC_L1 (P_L1 g pos (S fuel)) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => oc_cut B MT g pos PC_L1 (P_L1 g pos fuel) W3 c3 \/
                                   oc_cut B MT g pos B_OSEG7 (P_C g pos fuel) W3 c3 \/
                                   oc_cut B MT g pos PC_E (P_E g pos) W3 c3).
Definition oc_part_b : Prop :=
  forall g pos fuel W2 c2, oc_pre B g -> oc_now B RLO RHI GLYPHA ROSTRS g ->
  oc_cut B MT g pos B_OSEG7 (P_C g pos fuel) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => oc_cut B MT g pos PC_L1 (P_L1 g pos fuel) W3 c3 \/
                                   oc_cut B MT g pos PC_X (P_X g) W3 c3).
Definition oc_part_e : Prop :=
  forall g pos W2 c2, oc_pre B g -> oc_now B RLO RHI GLYPHA ROSTRS g ->
  oc_cut B MT g pos PC_E (P_E g pos) W2 c2 ->
  SRr tfibsegs W2 c2 (fun W3 c3 => oc_cut B MT g pos PC_L2 (P_L2 g pos 8) W3 c3).

(* The segment from its three parts. *)
Lemma oc_seg_L1_of_parts : oc_part_a -> oc_part_b -> oc_part_e -> oc_seg_L1 B MT RLO RHI GLYPHA ROSTRS.
Proof.
intros HA HBp HE. unfold oc_seg_L1. intros g pos fuel W2 c2 Hpre Hnow Hc.
apply (SRr_bind tfibsegs _ _ _ _ (HA g pos fuel W2 c2 Hpre Hnow Hc)). intros W3 c3 _ [H3 | [H3 | H3]].
- apply SRr_ret. left. exact H3.
- eapply SRr_mono; [exact (HBp g pos fuel W3 c3 Hpre Hnow H3)|].
  intros W4 c4 _ [H4 | H4]; [left; exact H4 | right; right; exact H4].
- eapply SRr_mono; [exact (HE g pos W3 c3 Hpre Hnow H3)|].
  intros W4 c4 _ H4. right; left. exact H4.
Qed.

Section l.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The stack of the call: the entry sp, the realigned sp1, the window. *)
Lemma ocl_stack : forall g, oc_pre B g ->
  alloc_ceiling <= og_sp g - TB_owed_counter_text /\ og_sp g <= 2 ^ 47 /\ 2 ^ 46 + TB_owed_counter_text <= og_sp g /\
  og_sp g mod 16 = 0 /\ og_sp g - 208 <= og_sp1 g <= og_sp g - 192 /\ og_sp1 g mod 32 = 0 /\
  og_sp0 g - og_STK g <= og_sp g - TB_owed_counter_text /\ og_sp g <= og_sp0 g.
Proof.
intros g Hpre. pose proof Hpre as (HE & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_owed_counter_text HE
  ltac:(unfold TB_owed_counter_text, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & Hwin & Hwhi & _).
change (spZ (og_regs g)) with (og_sp g) in *.
unfold og_sp1.
destruct (sp1_facts (og_sp g - 192) ltac:(unfold TB_owed_counter_text, ESTACK in *; lia)
  ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity)) as (Hsp1r & Hsp1al & _).
split; [exact Hceil|]. split; [exact H47|]. split; [exact H46|]. split; [exact Hal|].
split; [lia|]. split; [exact Hsp1al|]. split; assumption.
Qed.

(* The walk's own frame at a boundary state. *)
Lemma ocl_frame : forall g pos ly2 S2 W2 mem2 md2, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  frames S2 = (1, pos) :: frames (og_Sc g) /\
  (forall c p, frame_addr ly2 c p = frame_addr (og_lyc g) c p) /\
  (forall c p, flag_addr ly2 c p = flag_addr (og_lyc g) c p) /\
  4096 <= og_F g pos /\ og_F g pos + 128 <= alloc_ceiling /\ og_F g pos mod 64 = 0 /\ in_app (og_F g pos) 128 /\
  (forall a, og_F g pos <= a < og_F g pos + 128 -> apresent (w_H W2) mem2 a).
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
pose proof Hpre as ((HJc & _) & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (EF : ly_F ly2 = ly_F (og_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr (og_lyc g) c p) by (intros c p; unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr (og_lyc g) c p) by (intros c p; unfold flag_addr; rewrite EF; reflexivity).
assert (Hfr : frames S2 = (1, pos) :: frames (og_Sc g)) by (rewrite Hfrs2, Hfrsc; reflexivity).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H4096 & Hceil & Happ).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (H64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 1 pos HAR2 Hin) as (_ & _ & HFp & _).
change (fs_frame_bytes 1) with 128 in Hceil, Happ, HFp.
rewrite Efa in H4096, Hceil, Happ, H64, HFp. fold (og_F g pos) in H4096, Hceil, Happ, H64, HFp.
split; [exact Hfr|]. split; [exact Efa|]. split; [exact Efl|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H64|]. split; [exact Happ|].
intros a Ha. exact (proj1 (HFp a Ha)).
Qed.

(* A byte of the frame's variables is fresh for the call state. *)
Lemma ocl_fresh : forall g pos ly2 S2 W2 mem2 md2 a, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  oc_zv g pos a -> cw_fresh B (og_lyc g) (og_Sc g) a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha.
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR2 & _).
apply (cw_fresh_own B LAWS (og_lyc g) (og_Sc g) ly2 S2 W2 mem2 md2 1 pos a HAR2 Hfr HP Efa).
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (og_F g pos). change (fs_frame_bytes 1) with 128.
unfold oc_zv in Ha. lia.
Qed.
(* A byte of the write set is not one of them. *)
Lemma ocl_wr_not_zv : forall g pos ly2 S2 W2 mem2 md2 a, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  oc_wr g a -> ~ oc_zv g pos a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hw Hz.
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & _ & HFc & _ & _ & _).
pose proof alloc_ceiling_val as Hac.
destruct (ocl_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hz) as (_ & _ & Hfb & Hff).
destruct (oc_wr_where B g Hpre a Hw) as [(bb & m & Hin & Hr) | [(cid & p & Hin & Hr) | Hst]].
- apply (Hfb bb m (a - bb) Hin); lia.
- exact (proj1 (Hff cid p Hin) Hr).
- unfold oc_zv in Hz. lia.
Qed.
Lemma ocl_rdword_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  rdword (aview tfibsegs H m) a = Some v -> rdword (aview tfibsegs H' m') a = Some v.
Proof.
intros H H' m m' a v Hk Hr. unfold rdword in *.
rewrite (Hk a), (Hk (a + 1)), (Hk (a + 2)), (Hk (a + 3)), (Hk (a + 4)), (Hk (a + 5)), (Hk (a + 6)), (Hk (a + 7))
  by lia. exact Hr.
Qed.
Lemma ocl_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q l,
  (forall x, q <= x < q + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cw_val_mem_kept H H' m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros x Hx. apply Hk. lia.
Qed.

(* The registers of oc_common. *)
Definition oc_kregs (r3 r2 : bvmap 5 word) : Prop :=
  getr r3 8 = getr r2 8 /\ getr r3 2 = getr r2 2 /\ getr r3 9 = getr r2 9 /\ getr r3 3 = getr r2 3 /\
  getr r3 4 = getr r2 4 /\ getr r3 23 = getr r2 23 /\ getr r3 26 = getr r2 26 /\ getr r3 18 = getr r2 18 /\
  getr r3 21 = getr r2 21 /\ getr r3 24 = getr r2 24 /\ getr r3 27 = getr r2 27.
Lemma oc_common_regs : forall g pos regs2 regs3 mem2 W2, oc_kregs regs3 regs2 ->
  oc_common g pos regs2 mem2 W2 -> oc_common g pos regs3 mem2 W2.
Proof.
intros g pos regs2 regs3 mem2 W2 (E8 & E2 & E9 & E3 & E4 & E23 & E26 & E18 & E21 & E24 & E27)
  (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & Hrest).
split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E23; exact R23|].
split; [rewrite E26; exact R26|]. split; [rewrite E18; exact R18|]. split; [rewrite E21; exact R21|].
split; [rewrite E24; exact R24|]. split; [rewrite E27; exact R27|]. exact Hrest.
Qed.

(* What a boundary carries, kept by a run that changes no byte outside the frame's variables. *)
Lemma ocl_keep : forall g pos ly2 S2 regs2 mem2 md2 W2 mem3, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  oc_common g pos regs2 mem2 W2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ oc_zv g pos a -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem3 (og_sp g) (oc_wr g) /\
  oc_common g pos regs2 mem3 W2 /\
  (garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) -> garr8 tfibsegs (rd W2 mem3) (og_sg g) (og_sj g)) /\
  (forall d, val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 d -> val_mem tfibsegs (rd W2 mem3) (og_dt g) 1 d).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 mem3 Hpre HJ HP HK HC KE KP.
destruct (ocl_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as ((HJc & _) & _ & _ & _ & _ & _ & Lsj & _).
pose proof (proj1 HJc) as HARc.
pose proof alloc_ceiling_val as Hac.
assert (HF8 : og_F g pos = 8 * (og_F g pos / 8)).
{ pose proof (Z.div_mod (og_F g pos) 64 ltac:(lia)) as D. pose proof (Z.div_mod (og_F g pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (og_F g pos) 8 ltac:(lia)) as M8. lia. }
unfold TB_owed_counter_text, ESTACK in Hceil, Hwin, H46.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply KE; [lia|]. unfold oc_zv. lia. }
split.
{ apply (cw_kept_step B LAWS TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) (og_mdc g) W2 mem2 mem3
    (og_sp g) (oc_wr g) (oc_zv g pos)); [unfold TB_owed_counter_text, ESTACK; lia | exact HARc | exact HK | exact KE | | exact KP].
  intros a Ha. right; right. exact (ocl_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha). }
split.
{ destruct HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 &
    V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18 & V19 & Hfl & Hsh).
  do 11 (split; [assumption|]).
  repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [intros x Hx; apply KH; cbn in Hx; lia | assumption]|]).
  split.
  - apply (ocl_rdword_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hfl]. intros x Hx. apply KE; [lia|]. unfold oc_zv. lia.
  - apply (ocl_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length OC_FRAME_SHADOW] in Hx.
    change (Z.of_nat 16) with 16 in Hx.
    apply KE; [unfold SB in *; lia|]. unfold oc_zv, SB in *. lia. }
split.
{ apply (ocl_garr8_kept (w_H W2) (w_H W2) mem2 mem3). intros x Hx.
  rewrite Lsj in Hx. change (Z.of_nat 8) with 8 in Hx.
  assert (Hw : oc_wr g x) by (unfold oc_wr; left; exact Hx).
  pose proof (oc_wr_win B g Hpre x Hw) as Hww. unfold TB_owed_counter_text in Hww.
  apply KE; [pose proof Hpre as (_ & _ & _ & _ & (Hsg0 & Hsg63 & _) & _); lia|].
  exact (ocl_wr_not_zv g pos ly2 S2 W2 mem2 md2 x Hpre HJ HP Hw). }
{ intros d Hd. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hd]. intros x Hx. cbn in Hx.
  assert (Hw : oc_wr g x) by (unfold oc_wr; right; lia).
  apply KE; [|exact (ocl_wr_not_zv g pos ly2 S2 W2 mem2 md2 x Hpre HJ HP Hw)].
  pose proof Hpre as (_ & _ & _ & _ & _ & _ & _ & _ & Hdt & _).
  destruct Hdt as [((Hx0 & Hx1 & _) & _) | (Hx0 & Hx1 & _)]; lia. }
Qed.

(* A boundary at the end of a run of the segment: the run kept the journal's layout and state, wrote only bytes of
   the frame's variables, kept the eleven registers of oc_common; P holds of the new state given seg and dt as
   before. *)
Lemma ocl_cut_close : forall g pos pc (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
    world tfibsegs -> Prop) ly2 S2 regs2 mem2 md2 W2 ms md3,
  oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) -> ~ In (1, pos) (frames (og_Sc g)) ->
  same_io (og_mdc g) md2 -> mo_le MT (og_Sc g) S2 0 -> oc_common g pos regs2 mem2 W2 ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 (ms_mem ms) md3 (og_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  oc_kregs (ms_regs ms) regs2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ oc_zv g pos a ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) ->
  garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) -> val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 (og_dj g) ->
  (garr8 tfibsegs (rd W2 (ms_mem ms)) (og_sg g) (og_sj g) ->
   val_mem tfibsegs (rd W2 (ms_mem ms)) (og_dt g) 1 (og_dj g) ->
   P ly2 S2 (ms_regs ms) (ms_mem ms) md3 W2) ->
  oc_cut B MT g pos pc P W2 (mkCfg ms md3).
Proof.
intros g pos pc P ly2 S2 regs2 mem2 md2 W2 ms md3 Hpre HJ HK HP Hni Hio Hmo HC HJ3 Hio3 Hms HR KE KP Hsj Hdj HPk.
destruct (ocl_keep g pos ly2 S2 regs2 mem2 md2 W2 (ms_mem ms) Hpre HJ HP HK HC KE KP) as (HK3 & HC3 & Ksj & Kdj).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact HK3|]. split; [exact HP|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|].
split; [exact (oc_common_regs g pos regs2 (ms_regs ms) (ms_mem ms) W2 HR HC3)|].
exact (HPk (Ksj Hsj) (Kdj _ Hdj)).
Qed.

(* The usable marks of the frame's variables, from the frame's shadow bytes. *)
Lemma ocl_ra_var : forall (H : word -> bool) (m : word -> option byte) F lo len, F mod 8 = 0 -> 0 <= F ->
  ((32 <= lo /\ lo + len <= 40) \/ (64 <= lo /\ lo + len <= 96)) ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) OC_FRAME_SHADOW ->
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

Lemma ocl_nth_upd_same : forall (l : list Z) i v, (Z.to_nat i < length l)%nat -> nth (Z.to_nat i) (upd_at l i v) 0 = v.
Proof.
intros l i v Hi. unfold upd_at. rewrite app_nth2 by (rewrite length_firstn; lia).
rewrite length_firstn. replace (Z.to_nat i - Nat.min (Z.to_nat i) (length l))%nat with 0%nat by lia. reflexivity.
Qed.
(* The step lemmas of the first loop (lib/Prog/codec_owe.v ct1_owe). *)
Lemma ocl_ct1_end : forall rest n s dot, ct1_owe (0 :: rest) n s dot = Some (n, s, dot).
Proof. intros. reflexivity. Qed.
Lemma ocl_ct1_dotset : forall rest n s dot, 0 < n -> nth (Z.to_nat (n - 1)) dot 0 = 0 ->
  ct1_owe (46 :: rest) n s dot = ct1_owe rest n s (upd_at dot (n - 1) 1).
Proof.
intros rest n s dot Hn Hd. cbn [ct1_owe]. rewrite (proj2 (Z.ltb_lt 0 n) Hn), Hd. reflexivity.
Qed.
Lemma ocl_ct1_digit : forall ch rest n s dot, ch <> 0 ->
  ~ (ch = 46 /\ 0 < n /\ nth (Z.to_nat (n - 1)) dot 0 = 0) ->
  ct1_owe (ch :: rest) n s dot =
    if (oc_v ch <? 0) || (n =? 8) then None
    else ct1_owe rest (n + 1) (s ++ [oc_v ch]) (upd_at dot n (if ch =? 46 then 1 else 0)).
Proof.
intros ch rest n s dot H0 Hd. cbn [ct1_owe]. rewrite (proj2 (Z.eqb_neq ch 0) H0).
destruct ((ch =? 46) && (0 <? n) && (nth (Z.to_nat (n - 1)) dot 0 =? 0)) eqn:E; [|reflexivity].
exfalso. apply Hd. apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
apply Z.eqb_eq in E1. apply Z.ltb_lt in E2. apply Z.eqb_eq in E3. auto.
Qed.
Lemma ocl_Forall_upd_at : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (upd_at l i v).
Proof.
intros P l i v H Hv. unfold upd_at.
pose proof (firstn_skipn (Z.to_nat i) l) as E1. pose proof (firstn_skipn (S (Z.to_nat i)) l) as E2.
assert (H1 : Forall P (firstn (Z.to_nat i) l)) by (rewrite <- E1 in H; apply Forall_app in H; tauto).
assert (H2 : Forall P (skipn (S (Z.to_nat i)) l)) by (rewrite <- E2 in H; apply Forall_app in H; tauto).
apply Forall_app. split; [exact H1 | constructor; assumption].
Qed.
(* The byte i of the text exists: the bytes before it are not 0 and the text holds a 0. *)
Lemma ocl_tb_len : forall (tb : list Z) i, 0 <= i -> In 0 tb ->
  Forall (fun x => x <> 0) (firstn (Z.to_nat i) tb) -> i < Z.of_nat (length tb).
Proof.
intros tb i Hi Hin Hf.
destruct (Nat.lt_ge_cases (Z.to_nat i) (length tb)) as [Hl | Hl]; [lia|].
exfalso. rewrite firstn_all2 in Hf by exact Hl. rewrite Forall_forall in Hf. exact (Hf 0 Hin eq_refl).
Qed.
Lemma ocl_firstn_S : forall (l : list Z) k, (k < length l)%nat -> firstn (S k) l = firstn k l ++ [nth k l 0].
Proof.
induction l as [|x l IH]; intros k Hk; cbn in Hk; [lia|].
destruct k as [|k]; [reflexivity|]. cbn [firstn nth app]. rewrite (IH k) by lia. reflexivity.
Qed.
(* The frame's variables kept by a run that wrote none of them. *)
Lemma ocl_arrays_kept : forall g pos W2 W3 mem2 mem3 n s dot,
  (forall a, og_F g pos <= a < og_F g pos + 128 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  n <= 8 -> oc_arrays g pos W2 mem2 n s dot -> oc_arrays g pos W3 mem3 n s dot.
Proof.
intros g pos W2 W3 mem2 mem3 n s dot KF Hn (Hd & Hs). split.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact (Hd i Hi)]. intros x Hx. apply KF. cbn in Hx. lia.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [|exact (Hs i Hi)]. intros x Hx. apply KF. cbn in Hx. lia.
Qed.
(* ... and with the word dot[n - 1] (at F + 60 + 4 n) now v. *)
Lemma ocl_arrays_word : forall g pos W2 mem2 mem3 n s dot v, 1 <= n <= 8 -> length dot = 8%nat ->
  (forall a, og_F g pos <= a < og_F g pos + 128 -> ~ (og_F g pos + 60 + 4 * n <= a < og_F g pos + 64 + 4 * n) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (rd W2 mem3) (og_F g pos + 60 + 4 * n) 4 v ->
  oc_arrays g pos W2 mem2 n s dot -> oc_arrays g pos W2 mem3 n s (upd_at dot (n - 1) v).
Proof.
intros g pos W2 mem2 mem3 n s dot v Hn Hl KF Hv (Hd & Hs). split.
- intros i Hi. destruct (Z.eq_dec i (n - 1)) as [-> | Hne].
  + rewrite ocl_nth_upd_same by lia. replace (og_F g pos + 64 + 4 * (n - 1)) with (og_F g pos + 60 + 4 * n) by lia.
    exact Hv.
  + rewrite nth_upd_other by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)].
    intros x Hx. cbn in Hx. apply KF; lia.
- intros i Hi. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hs i Hi)].
  intros x Hx. cbn in Hx. apply KF; lia.
Qed.
(* ... and with dot[n] := b (word at F + 64 + 4 n) and s[n] := v (byte at F + 32 + n). *)
Lemma ocl_arrays_next : forall g pos W2 mem2 mem3 n s dot v b, 0 <= n < 8 ->
  length s = Z.to_nat n -> length dot = 8%nat ->
  (forall a, og_F g pos <= a < og_F g pos + 128 -> a <> og_F g pos + 32 + n ->
     ~ (og_F g pos + 64 + 4 * n <= a < og_F g pos + 68 + 4 * n) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  val_mem tfibsegs (rd W2 mem3) (og_F g pos + 32 + n) 1 v ->
  val_mem tfibsegs (rd W2 mem3) (og_F g pos + 64 + 4 * n) 4 b ->
  oc_arrays g pos W2 mem2 n s dot -> oc_arrays g pos W2 mem3 (n + 1) (s ++ [v]) (upd_at dot n b).
Proof.
intros g pos W2 mem2 mem3 n s dot v b Hn Hsl Hl KF Hv Hd1 (Hd & Hs). split.
- intros i Hi. destruct (Z.eq_dec i n) as [-> | Hne].
  + rewrite ocl_nth_upd_same by lia. exact Hd1.
  + rewrite nth_upd_other by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hd i Hi)].
    intros x Hx. cbn in Hx. apply KF; lia.
- intros i Hi. destruct (Z.eq_dec i n) as [-> | Hne].
  + rewrite app_nth2 by lia. rewrite Hsl. replace (Z.to_nat n - Z.to_nat n)%nat with 0%nat by lia. exact Hv.
  + rewrite app_nth1 by lia. apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [|exact (Hs i ltac:(lia))].
    intros x Hx. cbn in Hx. apply KF; lia.
Qed.
(* a callee-saved register after an own callee *)
Lemma ocl_pres : forall (regs regs2 : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs2 -> acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 r HP Hr. specialize (HP _ Hr). rewrite !Z_to_bv_bv_unsigned in HP. exact HP. Qed.
(* What a boundary carries, kept across the call of owed_seg7 (its post's tcj_kept, window [sp1 - 16, sp1),
   nothing written), with the eleven registers preserved. *)
Lemma ocl_keep_call : forall g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  oc_common g pos regs2 mem2 W2 ->
  tcj_kept tfibsegs B TB_owed_seg7 ly2 S2 W2 mem2 W3 mem3 (og_sp1 g) cno_wr ->
  oc_kregs regs3 regs2 ->
  oc_common g pos regs3 mem3 W3 /\
  (forall a, og_F g pos <= a < og_F g pos + 128 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a) /\
  (garr8 tfibsegs (rd W2 mem2) (og_sg g) (og_sj g) -> garr8 tfibsegs (rd W3 mem3) (og_sg g) (og_sj g)) /\
  (val_mem tfibsegs (rd W2 mem2) (og_dt g) 1 (og_dj g) -> val_mem tfibsegs (rd W3 mem3) (og_dt g) 1 (og_dj g)).
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 W3 Hpre HJ HP HC (K1 & K2 & _ & K4 & _) HR.
destruct (ocl_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as (_ & _ & _ & _ & (Hsg0 & Hsg63 & Hsgd & _) & _ & Lsj & _ & Hdt & _).
assert (Hin : In (1, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
unfold TB_owed_counter_text, ESTACK in Hceil, Hwin, H46.
assert (KH : forall x, og_sp1 g <= x < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply K1; [lia | lia | intros []]. }
assert (KZ : forall x, (in_zr x (frame_rng ly2 (1, pos)) \/
    in_zr x (shadow_addr (frame_addr ly2 1 pos), fs_frame_bytes 1 / 8)) ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply (K4 1 pos x Hin Hx). intros []. }
assert (KF : forall a, og_F g pos <= a < og_F g pos + 128 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H W2) mem2 a).
{ intros a Ha. apply KZ. left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. change (fs_frame_bytes 1) with 128.
  fold (og_F g pos). lia. }
(* a byte of an object of the call state: a block or a frame of it *)
assert (KO : forall x, (exists b m, In (b, m) (ablocks B (og_lyc g) (og_Sc g)) /\ b <= x < b + req_size m) \/
    (exists cid p, In (cid, p) (frames (og_Sc g)) /\ in_zr x (frame_rng (og_lyc g) (cid, p))) ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x [(bb & m & Hb & Hr) | (cid & p & Hcp & Hr)].
  - replace x with (bb + (x - bb)) by lia.
    apply (K2 bb m (x - bb) (Permutation_in _ (Permutation_sym HP) Hb)); [lia | intros []].
  - apply (K4 cid p x); [rewrite Hfr; right; exact Hcp | | intros []].
    left. unfold in_zr, frame_rng in *. cbn [fst snd] in *. rewrite Efa. exact Hr. }
assert (KD : forall q n x, tdst_ok B (og_lyc g) (og_Sc g) q n -> q <= x < q + n ->
  aview tfibsegs (w_H W3) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros q n x Hd Hx. apply KO. destruct (Hd x Hx) as [H | H]; [left; exact H | right; exact H]. }
split.
{ apply (oc_common_regs g pos regs2 regs3 mem3 W3 HR).
  destruct HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 &
    V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18 & V19 & Hfl & Hsh).
  do 11 (split; [assumption|]).
  repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3); [intros x Hx; apply KH; cbn in Hx; lia | assumption]|]).
  split.
  - apply (ocl_rdword_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hfl]. intros x Hx. apply KF. lia.
  - apply (ocl_garr8_kept (w_H W2) (w_H W3) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length OC_FRAME_SHADOW] in Hx.
    change (Z.of_nat 16) with 16 in Hx. apply KZ. right. unfold in_zr, shadow_addr. cbn [fst snd].
    rewrite Efa. change (fs_frame_bytes 1 / 8) with 16. fold (og_F g pos). rewrite <- SB_SHADOW_OFF. lia. }
split; [exact KF|].
split.
{ apply (ocl_garr8_kept (w_H W2) (w_H W3) mem2 mem3). intros x Hx. rewrite Lsj in Hx. change (Z.of_nat 8) with 8 in Hx.
  exact (KD (og_sg g) 8 x Hsgd Hx). }
{ apply (cw_val_mem_kept (w_H W2) (w_H W3) mem2 mem3). intros x Hx. cbn in Hx.
  assert (Hw : oc_wr g x) by (unfold oc_wr; right; lia).
  pose proof (oc_wr_win B g Hpre x Hw) as Hww. unfold TB_owed_counter_text, ESTACK in Hww.
  destruct (oc_wr_where B g Hpre x Hw) as [H | [H | Hst]].
  - apply KO. left. exact H.
  - apply KO. right. exact H.
  - apply K1; [lia | unfold TB_owed_seg7; lia | intros []]. }
Qed.

(* A byte of the write set is present at a boundary. *)
Lemma ocl_present : forall g pos ly2 S2 W2 mem2 md2 x, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  oc_wr g x -> apresent (w_H W2) mem2 x.
Proof.
intros g pos ly2 S2 W2 mem2 md2 x Hpre HJ Hperm HK Hx.
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfrs & Efa & _).
pose proof HJ as (HAR2 & _).
assert (Hobj : forall y, (exists b m, In (b, m) (ablocks B (og_lyc g) (og_Sc g)) /\ b <= y < b + req_size m) \/
    (exists cid p, In (cid, p) (frames (og_Sc g)) /\ in_zr y (frame_rng (og_lyc g) (cid, p))) -> apresent (w_H W2) mem2 y).
{ intros y [(bb & m & Hin & Hr) | (cid & p & Hin & Hr)].
  - assert (Hin2 : In (bb, m) (ablocks B ly2 S2)) by exact (Permutation_in _ (Permutation_sym Hperm) Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ bb m HAR2 Hin2) as (_ & _ & _ & _ & Hp & _).
    exact (proj1 (Hp y Hr)).
  - assert (Hin2 : In (cid, p) (frames S2)) by (rewrite Hfrs; right; exact Hin).
    destruct (al_frames _ _ LAWS _ _ _ _ _ cid p HAR2 Hin2) as (_ & _ & Hp & _).
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. rewrite <- Efa in Hr. exact (proj1 (Hp y Hr)). }
pose proof (oc_wr_win B g Hpre x Hx) as Hw.
pose proof Hpre as (_ & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
destruct Hx as [Hx | Hx].
- destruct Hsg as (_ & _ & Htd & _). exact (Hobj x (Htd x Hx)).
- destruct Hdt as [((_ & _ & Htd & _) & _) | Hdk].
  + exact (Hobj x (Htd x Hx)).
  + destruct (oc_wr_where B g Hpre x (or_intror Hx)) as [H | [H | Hst]];
      [exact (Hobj x (or_introl H)) | exact (Hobj x (or_intror H)) |].
    destruct Hdk as (_ & _ & _ & _ & Htw & _).
    destruct (Htw x Hx) as (_ & Hpr & _).
    destruct HK as (_ & _ & _ & _ & K5 & _).
    apply K5; [lia | exact Hw | exact Hpr].
Qed.
(* The walk may write a byte of the write set. *)
Lemma ocl_awr_wr : forall g pos ly2 S2 W2 mem2 md2 a, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  oc_wr g a ->
  awr_byte (og_STK g) (og_sp0 g) (og_FP g) (ablocks B (og_ly g) (og_S g)) (ablocks B ly2 S2) ly2 ((1, pos) :: og_own g) a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ Hperm Hx.
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & Efa & _).
pose proof Hpre as (_ & _ & _ & _ & Hsg & _ & _ & _ & Hdt & _).
assert (Hw : awr_byte (og_STK g) (og_sp0 g) (og_FP g) (ablocks B (og_ly g) (og_S g)) (ablocks B (og_lyc g) (og_Sc g))
  (og_lyc g) (og_own g) a).
{ destruct Hx as [Hx | Hx].
  - destruct Hsg as (_ & _ & _ & Htw & _). exact (proj1 (Htw a Hx)).
  - destruct Hdt as [((_ & _ & _ & Htw & _) & _) | (_ & _ & _ & _ & Htw & _)]; exact (proj1 (Htw a Hx)). }
destruct Hw as [H | [(H1 & b & m & Hin & Hr) | [(b & m & Hin & Hn & Hr) | (cid & p & Hin & Hr)]]].
- left. exact H.
- right; left. split; [exact H1|]. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hin) | exact Hr].
- right; right; left. exists b, m. split; [exact (Permutation_in _ (Permutation_sym Hperm) Hin)|]. split; [exact Hn | exact Hr].
- right; right; right. exists cid, p. split; [right; exact Hin|]. rewrite (Efa cid p). exact Hr.
Qed.
(* A byte of the write set is not a byte of the frame, of its shadow, or of the call's window. *)
Lemma ocl_wr_off : forall g pos ly2 S2 W2 mem2 md2 a, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  oc_wr g a ->
  ~ (og_F g pos <= a < og_F g pos + 128) /\ ~ (SB + og_F g pos / 8 <= a < SB + og_F g pos / 8 + 16) /\
  ~ (og_sp g - TB_owed_counter_text <= a < og_sp g).
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Hw.
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & HF0 & HFc & _ & HFapp & _).
pose proof HJ as (HAR2 & _).
pose proof alloc_ceiling_val as Hac.
assert (HF8 : og_F g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert (FR : (og_F g pos <= a < og_F g pos + 128) \/ (SB + og_F g pos / 8 <= a < SB + og_F g pos / 8 + 16) ->
  cw_fresh B (og_lyc g) (og_Sc g) a).
{ intros Hx. apply (cw_fresh_own B LAWS (og_lyc g) (og_Sc g) ly2 S2 W2 mem2 md2 1 pos a HAR2 Hfr HP Efa).
  destruct Hx as [Hx | Hx].
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (og_F g pos). change (fs_frame_bytes 1) with 128. lia.
  - right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite Efa. fold (og_F g pos). change (fs_frame_bytes 1 / 8) with 16.
    rewrite <- SB_SHADOW_OFF. lia. }
assert (NFF : ~ ((og_F g pos <= a < og_F g pos + 128) \/ (SB + og_F g pos / 8 <= a < SB + og_F g pos / 8 + 16))).
{ intros Hx. pose proof (FR Hx) as (_ & _ & Hb & Hf).
  destruct (oc_wr_where B g Hpre a Hw) as [(bb & m & Hinb & Hr) | [(cid & p & Hinf & Hr) | Hst]].
  - apply (Hb bb m (a - bb) Hinb); lia.
  - exact (proj1 (Hf cid p Hinf) Hr).
  - unfold SB in Hx. destruct Hx; lia. }
split; [intros Hx; apply NFF; left; exact Hx|]. split; [intros Hx; apply NFF; right; exact Hx|].
exact (oc_wr_win B g Hpre a Hw).
Qed.
(* A byte of the write set is not a byte of the image. *)
Lemma ocl_wr_not_img : forall g a, oc_pre B g -> oc_wr g a -> ~ in_img tfibsegs a.
Proof.
intros g a Hpre Hw Him.
pose proof Hpre as ((HJc & _) & _).
pose proof (proj1 HJc) as HARc.
pose proof alloc_ceiling_val as Hac.
destruct (oc_wr_where B g Hpre a Hw) as [H | [H | Hst]].
- assert (Htd : tdst_ok B (og_lyc g) (og_Sc g) a 1) by (intros x Hx; replace x with a by lia; left; exact H).
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ a 1 a HARc Htd ltac:(lia) Him).
- assert (Htd : tdst_ok B (og_lyc g) (og_Sc g) a 1) by (intros x Hx; replace x with a by lia; right; exact H).
  exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low _ _ _ _ _ a 1 a HARc Htd ltac:(lia) Him).
- pose proof (tfib_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo. lia.
Qed.
(* What a boundary carries, kept by a run that changes no byte outside the frame's variables and the write set. *)
Lemma ocl_keep_w : forall g pos ly2 S2 regs2 mem2 md2 W2 mem3, oc_pre B g ->
  ajournal tfibsegs B (og_STK g) (og_sp0 g) (og_FP g) (og_ly g) (og_S g) (og_W0 g) (og_mem0 g) (og_md0 g)
    ((1, pos) :: og_own g) ly2 S2 W2 mem2 md2 (og_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (og_lyc g) (og_Sc g)) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem2 (og_sp g) (oc_wr g) ->
  oc_common g pos regs2 mem2 W2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (oc_zv g pos a \/ oc_wr g a) ->
     aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  tcj_kept tfibsegs B TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) W2 mem3 (og_sp g) (oc_wr g) /\
  oc_common g pos regs2 mem3 W2.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 mem3 Hpre HJ HP HK HC KE KP.
destruct (ocl_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (ocl_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as ((HJc & _) & _).
pose proof (proj1 HJc) as HARc.
pose proof alloc_ceiling_val as Hac.
unfold TB_owed_counter_text, ESTACK in Hceil, Hwin, H46.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (KW : forall x, og_sp g - 4320 <= x < og_sp g -> aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply KE; [lia|]. intros [Hz | Hw]; [unfold oc_zv in Hz; lia|].
  destruct (ocl_wr_off g pos ly2 S2 W2 mem2 md2 x Hpre HJ HP Hw) as (_ & _ & H3). unfold TB_owed_counter_text, ESTACK in H3.
  lia. }
assert (KF : forall x, (og_F g pos + 96 <= x < og_F g pos + 128) \/ (SB + og_F g pos / 8 <= x < SB + og_F g pos / 8 + 16) ->
  aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ assert (HF8 : og_F g pos / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
  intros x Hx. apply KE; [unfold SB in *; lia|]. intros [Hz | Hw]; [unfold oc_zv, SB in *; lia|].
  destruct (ocl_wr_off g pos ly2 S2 W2 mem2 md2 x Hpre HJ HP Hw) as (H1 & H2 & _). lia. }
split.
{ apply (cw_kept_step B LAWS TB_owed_counter_text (og_lyc g) (og_Sc g) (og_W g) (og_memc g) (og_mdc g) W2 mem2 mem3
    (og_sp g) (oc_wr g) (fun a => oc_zv g pos a \/ oc_wr g a)); [unfold TB_owed_counter_text, ESTACK; lia | exact HARc | exact HK
    | exact KE | | exact KP].
  intros a [Ha | Ha]; [right; right; exact (ocl_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha) | right; left; split; [exact Ha | exact (ocl_wr_not_img g a Hpre Ha)]]. }
{ destruct HC as (R8 & R2 & R9 & R3 & R4 & R23 & R26 & R18 & R21 & R24 & R27 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 &
    V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18 & V19 & Hfl & Hsh).
  do 11 (split; [assumption|]).
  repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [intros x Hx; apply KW; cbn in Hx; lia | assumption]|]).
  split.
  - apply (ocl_rdword_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hfl]. intros x Hx. apply KF. lia.
  - apply (ocl_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length OC_FRAME_SHADOW] in Hx.
    change (Z.of_nat 16) with 16 in Hx. apply KF. lia. }
Qed.

End l.
End h.
End d.
