(* The facts every segment of check_text_scribble's walk in image B takes from a boundary
   (check_text_scribble_B_inv.v): the stack of the call, the walk's own frame, the bytes of want (the frame's one
   variable, [F + 32, F + 40)), the closing of a boundary after a run that wrote want only, and the owed text one
   output byte at a time (lib/Prog/codec_owe.v scr_owe). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgChkU CPgWalkU CPgWalkKeptU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgWalkFrameU check_text_scribble_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the owed text one output byte at a time ------------------------------------------------------------------ *)
Lemma bs_skipn_cons : forall (l : list Z) k, (k < length l)%nat -> skipn k l = nth k l 0 :: skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k] Hk; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.
Lemma bs_hd_skipn : forall (l : list Z) k, match skipn k l with y :: _ => y | [] => 0 end = nth k l 0.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma bs_tl_skipn : forall (l : list Z) k, tl (skipn k l) = skipn (S k) l.
Proof. induction l as [|x l IH]; intros [|k]; cbn; try reflexivity. apply IH. Qed.
Lemma bs_scr_0 : forall t, scr_owe t 0 = ([], 0).
Proof. intros [|x t]; reflexivity. Qed.
Lemma bs_scr_zero : forall t j k, (j < length t)%nat -> nth j t 0 = 0 -> scr_owe (skipn j t) k = (repeat 32 k, 0).
Proof.
intros t j k Hj Hx. rewrite (bs_skipn_cons t j Hj), Hx. destruct k as [|k]; reflexivity.
Qed.
Lemma bs_scr_step : forall t j k, (j < length t)%nat -> nth j t 0 <> 0 ->
  scr_owe (skipn j t) (S k) =
   (if (nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)
    then ((nth (S j) t 0 - 26) :: fst (scr_owe (skipn (S (S j)) t) k), snd (scr_owe (skipn (S (S j)) t) k) + 2)
    else ((if nth j t 0 <? 128 then nth j t 0 else 63) :: fst (scr_owe (skipn (S j) t) k),
          snd (scr_owe (skipn (S j) t) k) + 1)).
Proof.
intros t j k Hj Hx. rewrite (bs_skipn_cons t j Hj). cbn [scr_owe].
rewrite (proj2 (Z.eqb_neq _ _) Hx). rewrite bs_hd_skipn, bs_tl_skipn.
destruct ((nth j t 0 =? 46) && (49 <=? nth (S j) t 0) && (nth (S j) t 0 <=? 57)).
- destruct (scr_owe (skipn (S (S j)) t) k); reflexivity.
- destruct (scr_owe (skipn (S j) t) k); reflexivity.
Qed.
(* the byte i of the text exists: the bytes before it are not 0 and the text holds a 0 *)
Lemma bs_tb_len : forall (tb : list Z) i, In 0 tb -> Forall (fun x => x <> 0) (firstn i tb) -> (i < length tb)%nat.
Proof.
intros tb i Hin Hf. destruct (Nat.lt_ge_cases i (length tb)) as [Hl | Hl]; [exact Hl|].
exfalso. rewrite firstn_all2 in Hf by exact Hl. rewrite Forall_forall in Hf. exact (Hf 0 Hin eq_refl).
Qed.
Lemma bs_firstn_snoc : forall (tb : list Z) i, (i < length tb)%nat -> firstn (S i) tb = firstn i tb ++ [nth i tb 0].
Proof.
intros tb i. revert tb. induction i as [|i IH]; intros [|y t] Hi; cbn [length] in Hi; try lia.
- reflexivity.
- cbn [firstn nth app]. f_equal. apply IH. lia.
Qed.
Lemma bs_firstn_S : forall (tb : list Z) i, (i < length tb)%nat -> Forall (fun x => x <> 0) (firstn i tb) ->
  nth i tb 0 <> 0 -> Forall (fun x => x <> 0) (firstn (S i) tb).
Proof.
intros tb i Hi Hf Hx. rewrite (bs_firstn_snoc tb i Hi). apply Forall_app. split; [exact Hf|].
constructor; [exact Hx | constructor].
Qed.

(* the boundary's owed facts after one output byte: a digit after a dot takes two text bytes, any other byte one *)
Lemma bs_rest_digit : forall g i o w, 0 <= i -> 0 <= o < bs_n g ->
  (Z.to_nat i < length (bs_tb g))%nat -> nth (Z.to_nat i) (bs_tb g) 0 = 46 ->
  49 <= nth (S (Z.to_nat i)) (bs_tb g) 0 <= 57 ->
  fst (bs_owe g) = w ++ fst (bs_rest g i (bs_n g - o)) -> snd (bs_owe g) = i + snd (bs_rest g i (bs_n g - o)) ->
  fst (bs_owe g) = (w ++ [nth (S (Z.to_nat i)) (bs_tb g) 0 - 26]) ++ fst (bs_rest g (i + 2) (bs_n g - (o + 1))) /\
  snd (bs_owe g) = (i + 2) + snd (bs_rest g (i + 2) (bs_n g - (o + 1))).
Proof.
intros g i o w Hi Ho Hl Hx Hy H1 H2. unfold bs_rest in *.
replace (Z.to_nat (bs_n g - o)) with (S (Z.to_nat (bs_n g - (o + 1)))) in H1, H2 by lia.
rewrite (bs_scr_step (bs_tb g) (Z.to_nat i) _ Hl ltac:(rewrite Hx; lia)) in H1, H2.
rewrite Hx in H1, H2. rewrite (proj2 (Z.eqb_eq 46 46) eq_refl) in H1, H2.
rewrite (proj2 (Z.leb_le _ _) (proj1 Hy)), (proj2 (Z.leb_le _ _) (proj2 Hy)) in H1, H2. cbn [andb fst snd] in H1, H2.
replace (Z.to_nat (i + 2)) with (S (S (Z.to_nat i))) by lia.
rewrite <- app_assoc. split; [exact H1 | lia].
Qed.
Lemma bs_rest_plain : forall g i o w, 0 <= i -> 0 <= o < bs_n g ->
  (Z.to_nat i < length (bs_tb g))%nat -> nth (Z.to_nat i) (bs_tb g) 0 <> 0 ->
  ~ (nth (Z.to_nat i) (bs_tb g) 0 = 46 /\ 49 <= nth (S (Z.to_nat i)) (bs_tb g) 0 <= 57) ->
  fst (bs_owe g) = w ++ fst (bs_rest g i (bs_n g - o)) -> snd (bs_owe g) = i + snd (bs_rest g i (bs_n g - o)) ->
  let x := nth (Z.to_nat i) (bs_tb g) 0 in
  fst (bs_owe g) = (w ++ [if x <? 128 then x else 63]) ++ fst (bs_rest g (i + 1) (bs_n g - (o + 1))) /\
  snd (bs_owe g) = (i + 1) + snd (bs_rest g (i + 1) (bs_n g - (o + 1))).
Proof.
intros g i o w Hi Ho Hl Hx Hnd H1 H2 x. unfold bs_rest in *.
replace (Z.to_nat (bs_n g - o)) with (S (Z.to_nat (bs_n g - (o + 1)))) in H1, H2 by lia.
rewrite (bs_scr_step (bs_tb g) (Z.to_nat i) _ Hl Hx) in H1, H2.
replace ((nth (Z.to_nat i) (bs_tb g) 0 =? 46) && (49 <=? nth (S (Z.to_nat i)) (bs_tb g) 0) &&
         (nth (S (Z.to_nat i)) (bs_tb g) 0 <=? 57)) with false in H1, H2.
2: { symmetry. destruct (Z.eqb_spec (nth (Z.to_nat i) (bs_tb g) 0) 46); [|reflexivity].
     destruct (Z.leb_spec 49 (nth (S (Z.to_nat i)) (bs_tb g) 0)); [|reflexivity].
     destruct (Z.leb_spec (nth (S (Z.to_nat i)) (bs_tb g) 0) 57); [|reflexivity].
     exfalso. apply Hnd. split; [assumption | lia]. }
cbn [fst snd] in H1, H2. fold x in H1, H2.
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
rewrite <- app_assoc. split; [exact H1 | lia].
Qed.
(* the loop's exits: a 0 byte, or every slot filled *)
Lemma bs_rest_exit0 : forall g i o w, 0 <= i -> 0 <= o <= bs_n g ->
  (Z.to_nat i < length (bs_tb g))%nat -> nth (Z.to_nat i) (bs_tb g) 0 = 0 ->
  fst (bs_owe g) = w ++ fst (bs_rest g i (bs_n g - o)) -> snd (bs_owe g) = i + snd (bs_rest g i (bs_n g - o)) ->
  fst (bs_owe g) = w ++ repeat 32 (Z.to_nat (bs_n g - o)) /\ snd (bs_owe g) = i.
Proof.
intros g i o w Hi Ho Hl Hx H1 H2. unfold bs_rest in *.
rewrite (bs_scr_zero (bs_tb g) (Z.to_nat i) _ Hl Hx) in H1, H2. cbn [fst snd] in H1, H2. split; [exact H1 | lia].
Qed.
Lemma bs_rest_full : forall g i o w, o = bs_n g ->
  fst (bs_owe g) = w ++ fst (bs_rest g i (bs_n g - o)) -> snd (bs_owe g) = i + snd (bs_rest g i (bs_n g - o)) ->
  fst (bs_owe g) = w ++ repeat 32 (Z.to_nat (bs_n g - o)) /\ snd (bs_owe g) = i.
Proof.
intros g i o w -> H1 H2. unfold bs_rest in *. rewrite Z.sub_diag in *. cbn [Z.to_nat repeat] in *.
rewrite bs_scr_0 in H1, H2. cbn [fst snd] in H1, H2. split; [exact H1 | lia].
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Local Notation rd W mem := (mrestrict (w_H W) mem).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws tfibsegs B.

(* The bytes of want, the frame's one variable. *)
Definition bs_zv (g : bs_ctx) (pos a : Z) : Prop := bs_F g pos + 32 <= a < bs_F g pos + 40.

(* The stack of the call: the entry sp, the realigned sp1, the window. *)
Lemma bs_stack : forall g, bs_pre B g ->
  alloc_ceiling <= bs_sp g - TB_check_text_scribble /\ bs_sp g <= 2 ^ 47 /\
  2 ^ 46 + TB_check_text_scribble <= bs_sp g /\
  bs_sp g mod 16 = 0 /\ bs_sp g - 144 <= bs_sp1 g <= bs_sp g - 128 /\ bs_sp1 g mod 32 = 0 /\
  bs_sp0 g - bs_STK g <= bs_sp g - TB_check_text_scribble /\ bs_sp g <= bs_sp0 g.
Proof.
intros g Hpre. pose proof Hpre as (HE & _).
pose proof (cw_entry_stack B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TB_check_text_scribble HE
  ltac:(unfold TB_check_text_scribble, ESTACK; lia)) as (Hceil & H47 & H46 & Hal & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & Hwin & Hwhi & _).
unfold bs_sp1. fold (bs_sp g) in *. unfold spZ in *. fold (bs_sp g) in *.
assert (TT : TB_check_text_scribble = 8352) by reflexivity. rewrite TT in *.
destruct (sp1_facts (bs_sp g - 128) ltac:(lia) ltac:(rewrite <- Zminus_mod_idemp_l, Hal; reflexivity))
  as (Hr & Ha32 & _).
split; [exact Hceil|]. split; [exact H47|]. split; [exact H46|]. split; [exact Hal|].
split; [lia|]. split; [exact Ha32|]. split; assumption.
Qed.

(* The walk's own frame at a boundary state. *)
Lemma bs_frame : forall g pos ly2 S2 W2 mem2 md2, bs_pre B g ->
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) ->
  frames S2 = (0, pos) :: frames (bs_Sc g) /\
  (forall c p, frame_addr ly2 c p = frame_addr (bs_lyc g) c p) /\
  (forall c p, flag_addr ly2 c p = flag_addr (bs_lyc g) c p) /\
  4096 <= bs_F g pos /\ bs_F g pos + 64 <= alloc_ceiling /\ bs_F g pos mod 64 = 0 /\ in_app (bs_F g pos) 64 /\
  (forall a, bs_F g pos <= a < bs_F g pos + 64 -> apresent (w_H W2) mem2 a).
Proof.
intros g pos ly2 S2 W2 mem2 md2 Hpre HJ.
pose proof Hpre as ((HJc & _) & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _).
assert (EF : ly_F ly2 = ly_F (bs_lyc g)).
{ destruct Hly2 as (_ & _ & _ & _ & _ & E1 & _). destruct Hlyc as (_ & _ & _ & _ & _ & E2 & _). rewrite E1, E2. reflexivity. }
assert (Efa : forall c p, frame_addr ly2 c p = frame_addr (bs_lyc g) c p) by (intros c p; unfold frame_addr; rewrite EF; reflexivity).
assert (Efl : forall c p, flag_addr ly2 c p = flag_addr (bs_lyc g) c p) by (intros c p; unfold flag_addr; rewrite EF; reflexivity).
assert (Hfr : frames S2 = (0, pos) :: frames (bs_Sc g)) by (rewrite Hfrs2, Hfrsc; reflexivity).
assert (Hin : In (0, pos) (frames S2)) by (rewrite Hfr; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (H4096 & Hceil & Happ).
destruct (frame_al64 tfibsegs B ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (H64 & _ & _).
destruct (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 0 pos HAR2 Hin) as (_ & _ & HFp & _).
change (fs_frame_bytes 0) with 64 in Hceil, Happ, HFp.
rewrite Efa in H4096, Hceil, Happ, H64, HFp. fold (bs_F g pos) in H4096, Hceil, Happ, H64, HFp.
split; [exact Hfr|]. split; [exact Efa|]. split; [exact Efl|].
split; [exact H4096|]. split; [exact Hceil|]. split; [exact H64|]. split; [exact Happ|].
intros a Ha. exact (proj1 (HFp a Ha)).
Qed.

(* A byte of want is fresh for the call state. *)
Lemma bs_fresh : forall g pos ly2 S2 W2 mem2 md2 a, bs_pre B g ->
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (bs_lyc g) (bs_Sc g)) ->
  bs_zv g pos a -> cw_fresh B (bs_lyc g) (bs_Sc g) a.
Proof.
intros g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha.
destruct (bs_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (Hfr & Efa & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR2 & _).
apply (cw_fresh_own B LAWS (bs_lyc g) (bs_Sc g) ly2 S2 W2 mem2 md2 0 pos a HAR2 Hfr HP Efa).
left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite Efa. fold (bs_F g pos). change (fs_frame_bytes 0) with 64.
unfold bs_zv in Ha. lia.
Qed.

Lemma bs_rdword_kept : forall (H H' : word -> bool) (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  rdword (aview tfibsegs H m) a = Some v -> rdword (aview tfibsegs H' m') a = Some v.
Proof.
intros H H' m m' a v Hk Hr. unfold rdword in *.
rewrite (Hk a), (Hk (a + 1)), (Hk (a + 2)), (Hk (a + 3)), (Hk (a + 4)), (Hk (a + 5)), (Hk (a + 6)), (Hk (a + 7))
  by lia. exact Hr.
Qed.
Lemma bs_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q l,
  (forall x, q <= x < q + Z.of_nat (length l) -> aview tfibsegs H' m' x = aview tfibsegs H m x) ->
  garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk Hg j Hj. destruct (Hg j Hj) as (Hv & Hr). split; [|exact Hr].
apply (cw_val_mem_kept H H' m m' (q + Z.of_nat j) 1 (nth j l 0)); [|exact Hv].
intros x Hx. apply Hk. lia.
Qed.

(* What a boundary carries, kept by a run that changes no byte outside want and none of the thirteen registers of
   bs_common. *)
Lemma bs_keep : forall g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3, bs_pre B g ->
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (bs_lyc g) (bs_Sc g)) ->
  tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem2 (bs_sp g) (bs_wr g) ->
  bs_common g pos regs2 mem2 W2 ->
  getr regs3 8 = getr regs2 8 -> getr regs3 2 = getr regs2 2 -> getr regs3 9 = getr regs2 9 ->
  getr regs3 3 = getr regs2 3 -> getr regs3 4 = getr regs2 4 -> getr regs3 18 = getr regs2 18 ->
  getr regs3 24 = getr regs2 24 -> getr regs3 22 = getr regs2 22 -> getr regs3 23 = getr regs2 23 ->
  getr regs3 25 = getr regs2 25 -> getr regs3 19 = getr regs2 19 -> getr regs3 21 = getr regs2 21 ->
  getr regs3 27 = getr regs2 27 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ bs_zv g pos a -> aview tfibsegs (w_H W2) mem3 a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem3 a) ->
  tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem3 (bs_sp g) (bs_wr g) /\
  bs_common g pos regs3 mem3 W2.
Proof.
intros g pos ly2 S2 regs2 mem2 md2 W2 regs3 mem3 Hpre HJ HP HK HC E8 E2 E9 E3 E4 E18 E24 E22 E23 E25 E19 E21 E27 KE KP.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (bs_stack g Hpre) as (Hceil & H47 & H46 & Hal & Hsp1 & Hsp1a & Hwin & Hsp0).
destruct (bs_frame g pos ly2 S2 W2 mem2 md2 Hpre HJ) as (_ & _ & _ & HF0 & HFc & HF64 & HFapp & _).
pose proof Hpre as ((HJc & _) & _).
pose proof (proj1 HJc) as HARc.
unfold TB_check_text_scribble, ESTACK in Hceil, Hwin, H46.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HF8e : bs_F g pos = 8 * (bs_F g pos / 8)).
{ pose proof (Z.div_mod (bs_F g pos) 64 ltac:(lia)) as D. pose proof (Z.div_mod (bs_F g pos) 8 ltac:(lia)) as D8.
  pose proof (Z.mod_pos_bound (bs_F g pos) 8 ltac:(lia)) as M8. lia. }
assert (KH : forall x, alloc_ceiling <= x < 2 ^ 64 -> aview tfibsegs (w_H W2) mem3 x = aview tfibsegs (w_H W2) mem2 x).
{ intros x Hx. apply KE; [lia|]. unfold bs_zv. lia. }
split.
{ apply (cw_kept_step B LAWS TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) (bs_mdc g) W2 mem2 mem3
    (bs_sp g) (bs_wr g) (bs_zv g pos)); [unfold TB_check_text_scribble, ESTACK; lia | exact HARc | exact HK | exact KE | | exact KP].
  intros a Ha. right; right. exact (bs_fresh g pos ly2 S2 W2 mem2 md2 a Hpre HJ HP Ha). }
destruct HC as (R8 & R2 & R9 & R3 & R4 & R18 & R24 & R22 & R23 & R25 & R19 & R21 & R27 & V1 & V2 & V3 & V4 & V5 & V6 & V7 &
  V8 & V9 & V10 & V11 & V12 & Hfl & Hsh).
split; [rewrite E8; exact R8|]. split; [rewrite E2; exact R2|]. split; [rewrite E9; exact R9|].
split; [rewrite E3; exact R3|]. split; [rewrite E4; exact R4|]. split; [rewrite E18; exact R18|].
split; [rewrite E24; exact R24|]. split; [rewrite E22; exact R22|]. split; [rewrite E23; exact R23|].
split; [rewrite E25; exact R25|]. split; [rewrite E19; exact R19|]. split; [rewrite E21; exact R21|].
split; [rewrite E27; exact R27|].
repeat (split; [apply (cw_val_mem_kept (w_H W2) (w_H W2) mem2 mem3); [intros x Hx; apply KH; cbn in Hx; lia | assumption]|]).
split.
- apply (bs_rdword_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hfl]. intros x Hx. apply KE; [lia|]. unfold bs_zv. lia.
- apply (bs_garr8_kept (w_H W2) (w_H W2) mem2 mem3); [|exact Hsh]. intros x Hx. cbn [length BS_FRAME_SHADOW] in Hx.
  change (Z.of_nat 8) with 8 in Hx.
  apply KE; [unfold SB in *; lia|]. unfold bs_zv, SB in *. lia.
Qed.

(* A boundary at the end of a run of a segment: the run kept the journal's layout and state, wrote only bytes of
   want, kept the thirteen registers; P holds of the new state. *)
Lemma bs_cut_close : forall g pos pc (P : alayout -> astate -> bvmap 5 word -> (word -> option byte) -> Model ->
    world tfibsegs -> Prop) ly2 S2 regs2 mem2 md2 W2 ms md3,
  bs_pre B g ->
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 mem2 md2 (bs_k g) ->
  tcj_kept tfibsegs B TB_check_text_scribble (bs_lyc g) (bs_Sc g) (bs_W g) (bs_memc g) W2 mem2 (bs_sp g) (bs_wr g) ->
  Permutation (ablocks B ly2 S2) (ablocks B (bs_lyc g) (bs_Sc g)) -> ~ In (0, pos) (frames (bs_Sc g)) ->
  same_io (bs_mdc g) md2 -> mo_le MT (bs_Sc g) S2 0 -> bs_common g pos regs2 mem2 W2 ->
  ajournal tfibsegs B (bs_STK g) (bs_sp0 g) (bs_FP g) (bs_ly g) (bs_S g) (bs_W0 g) (bs_mem0 g) (bs_md0 g)
    ((0, pos) :: bs_own g) ly2 S2 W2 (ms_mem ms) md3 (bs_k g) ->
  same_io md2 md3 ->
  ms = mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs) ->
  getr (ms_regs ms) 8 = getr regs2 8 -> getr (ms_regs ms) 2 = getr regs2 2 -> getr (ms_regs ms) 9 = getr regs2 9 ->
  getr (ms_regs ms) 3 = getr regs2 3 -> getr (ms_regs ms) 4 = getr regs2 4 ->
  getr (ms_regs ms) 18 = getr regs2 18 -> getr (ms_regs ms) 24 = getr regs2 24 ->
  getr (ms_regs ms) 22 = getr regs2 22 -> getr (ms_regs ms) 23 = getr regs2 23 ->
  getr (ms_regs ms) 25 = getr regs2 25 -> getr (ms_regs ms) 19 = getr regs2 19 ->
  getr (ms_regs ms) 21 = getr regs2 21 -> getr (ms_regs ms) 27 = getr regs2 27 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ bs_zv g pos a ->
     aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
  (forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem ms) a) ->
  P ly2 S2 (ms_regs ms) (ms_mem ms) md3 W2 ->
  bs_cut B MT g pos pc P W2 (mkCfg ms md3).
Proof.
intros g pos pc P ly2 S2 regs2 mem2 md2 W2 ms md3 Hpre HJ HK HP Hni Hio Hmo HC HJ3 Hio3 Hms
  E8 E2 E9 E3 E4 E18 E24 E22 E23 E25 E19 E21 E27 KE KP HPk.
destruct (bs_keep g pos ly2 S2 regs2 mem2 md2 W2 (ms_regs ms) (ms_mem ms) Hpre HJ HP HK HC
  E8 E2 E9 E3 E4 E18 E24 E22 E23 E25 E19 E21 E27 KE KP) as (HK3 & HC3).
exists ly2, S2, (ms_regs ms), (ms_mem ms), md3.
split; [unfold cfg_at, w64; rewrite Hms at 1; reflexivity|].
split; [exact HJ3|]. split; [exact HK3|]. split; [exact HP|]. split; [exact Hni|].
split; [exact (same_io_trans _ _ _ Hio Hio3)|]. split; [exact Hmo|]. split; [exact HC3|].
exact HPk.
Qed.

(* The usable marks of want, from the frame's shadow bytes. *)
Lemma bs_ra_want : forall (H : word -> bool) (m : word -> option byte) F lo len, F mod 8 = 0 -> 0 <= F ->
  32 <= lo -> lo + len <= 40 ->
  garr8 tfibsegs (mrestrict H m) (SB + F / 8) BS_FRAME_SHADOW ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF (F + lo) len.
Proof.
intros H m F lo len HF8 HF0 Hlo Hhi Hsh x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Ex : x / 8 = F / 8 + (x - F) / 8).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite HF8, Z.add_0_r in D.
  replace x with ((x - F) + (F / 8) * 8) at 1 by lia. rewrite Z.div_add by lia. lia. }
assert (Hk : (x - F) / 8 = 4).
{ assert (L1 : 4 <= (x - F) / 8) by (apply Z.div_le_lower_bound; lia).
  assert (L2 : (x - F) / 8 < 5) by (apply Z.div_lt_upper_bound; lia). lia. }
rewrite Ex, Hk. rewrite <- SB_SHADOW_OFF. rewrite Z.add_assoc.
apply (aview_of_val_mem1 tfibsegs H m (SB + F / 8 + 4) 0); [|lia].
exact (proj1 (Hsh 4%nat ltac:(cbn; lia))).
Qed.

(* want after one more byte v at F + 32 + o *)
Lemma bs_want_snoc : forall (H : word -> bool) (m m' : word -> option byte) F w v,
  garr8 tfibsegs (mrestrict H m) (F + 32) w ->
  (forall x, F + 32 <= x < F + 32 + Z.of_nat (length w) -> aview tfibsegs H m' x = aview tfibsegs H m x) ->
  val_mem tfibsegs (mrestrict H m') (F + 32 + Z.of_nat (length w)) 1 v -> 0 <= v < 256 ->
  garr8 tfibsegs (mrestrict H m') (F + 32) (w ++ [v]).
Proof.
intros H m m' F w v Hg Hk Hv Hr j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length w)) as [Hl | Hl].
- rewrite app_nth1 by exact Hl. destruct (Hg j Hl) as (Vj & Rj). split; [|exact Rj].
  apply (cw_val_mem_kept H H m m' (F + 32 + Z.of_nat j) 1 (nth j w 0)); [|exact Vj].
  intros x Hx. apply Hk. cbn in Hx. lia.
- assert (j = length w) as -> by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [exact Hv | exact Hr].
Qed.
End h.
End d.

(* ---- tactics of the segments ------------------------------------------------------------------------------------ *)
(* an atom of the start env through the runs' extensions (havoc / ewset) *)
Ltac ewpeel := repeat (first [ rewrite ew_havoc_old by nat_side | rewrite ew_ewset_other by nat_side ]).
Ltac ewpeel_in H := repeat (first [ rewrite ew_havoc_old in H by nat_side | rewrite ew_ewset_other in H by nat_side ]).
(* the goal's register r of the stopped state as its symbolic value *)
Ltac rv := lazymatch goal with HS : st_ok _ _ _ (restrict _ ?msv) |- context [getr (ms_regs ?msv) ?r] =>
  let R := fresh "R" in rreg HS r R; rewrite R; clear R end.
(* a register of the stopped state: a literal, or an atom of the start (a fact ew E k = .. in context, or the start
   register through EE) *)
Ltac bs_rfin := rv; first
  [ reflexivity
  | rewrite ?sv_denot_SOff0; ewpeel;
    first [ assumption | match goal with H : _ |- _ => apply H; reflexivity end ] ].
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
