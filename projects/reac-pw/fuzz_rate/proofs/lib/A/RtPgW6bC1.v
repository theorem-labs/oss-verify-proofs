(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; every address measured on the unstripped twin
   0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, same loaded bytes): the block lemma w6b_c1 of
   lib/A/RtPgW6bBase.v, ent_build's case 1 (pod.h:286-294) inside LLVMFuzzerTestOneInput, from the case entry 0x817c4
   to the join J 0x81e00. Proves no function (kind: segment lemma).
   THE CHAIN (lib/A/RtPgW6bC1Kit.v):
     c1_head (RtPgW6bC1Head.v)   0x817c4 .. 0x42194   i = fuzz_u8 % 9, [R+0x100] := the cursor, a0 = s11 = vocab[i]
     the strlen wrapper           0x42194 .. 0x81a6c   ASTRLEN (lib/A/Rt/StrlenDef.v astrlen_realizes at W6B_STRLEN)
                                                       through lib/A/RtPgSteps.v rts_ecall_at: a0 = |vocab[i]|
     c1_mid (RtPgW6bC1Mid.v)      0x81a6c .. 0x51860   l = |vocab[i]| (12 .. 18, never clamped)
     __asan_memcpy                0x51860 .. 0x81a94   AMEMCPY (lib/Reusable/YG0d.v aintrin_realizes OCpy) through
                                                       lib/A/RtPgSteps.v rts_intrin_at: e.body[0..l) := vocab[i]
     c1_tail (RtPgW6bC1Tail.v)    0x81a94 .. J         the NUL, e.type, e.size, and with kind & 0x80 'x', NUL
   The post is RtPgSteps.rts_post at J with the layout, state and world of the entry (no call changes them), the
   registers outside w6b_clob kept by every piece, every byte outside w6b_wr kept, and w6b_J_R: e's 104 bytes are
   the header from the tail's stores, the string copied from the image (rt_cstr of w6b_vocab_ok), the three bytes
   after it from the tail and the rest the entry's zeros. The model's entry (c1_model): ent_text of vocab[i % 9]
   (at most 18 bytes, so the 95-byte clamp never cuts), extended by 'x', NUL when kind & 0x80 (|v| + 3 <= 96 always
   holds). *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec RtPgMem RtPgSteps RtPgW6aBase RtPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgW6bC1Kit RtPgW6bC1Head RtPgW6bC1Mid RtPgW6bC1Tail.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A.Rt Require Import StrlenDef WrapRo.
Require OSSVerify.reac_pw.fuzz_rate.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RtPgSteps.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.Asan.M.loaded_segments.
Local Abbreviation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ======================================== the model ======================================== *)
Definition c1_ent (x : bool) (j : Z) : ent :=
  if x then Ent POD_STRING (c1_len j + 3) ((c1_v j ++ [NUL]) ++ [Z_to_bv 8 120; NUL])
  else Ent POD_STRING (c1_len j + 1) (c1_v j ++ [NUL]).
Lemma c1_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 1 ->
  ent_build (b :: r) = (c1_ent (Z.testbit (bv_unsigned b) 7) (c1_j r), snd (fuzz_u8 r)).
Proof.
intros b r H. unfold ent_build, c1_j. cbn [fuzz_u8]. rewrite H.
destruct (fuzz_u8 r) as [i r'] eqn:Hf. cbn [fst snd]. f_equal.
assert (Hj : 0 <= i mod 9 < 9) by (apply Z.mod_pos_bound; lia).
revert Hj. generalize (i mod 9) as j. intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
destruct (Z.testbit (bv_unsigned b) 7);
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma c1_ent_bytes : forall x j, 0 <= j < 9 ->
  u8s (ent_mem (c1_ent x j)) =
  u8s (le32 8) ++ u8s (le32 (if x then c1_len j + 3 else c1_len j + 1)) ++ u8s (c1_v j) ++
  [0; (if x then 120 else 0); 0] ++ repeat 0 (Z.to_nat (93 - c1_len j)).
Proof.
intros x j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
destruct x; destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
Qed.

(* ======================================== helpers ======================================== *)
Lemma c1_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact Hr. Qed.
Ltac c1_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Lemma c1_garr8_3 : forall {fx : YK11.FPState} m a v0 v1 v2,
  val_mem rsegs m a 1 v0 -> val_mem rsegs m (a + 1) 1 v1 -> val_mem rsegs m (a + 2) 1 v2 ->
  0 <= v0 < 256 -> 0 <= v1 < 256 -> 0 <= v2 < 256 -> garr8 rsegs m a [v0; v1; v2].
Proof.
intros fx m a v0 v1 v2 H0 H1 H2 R0 R1 R2 q Hq. cbn [length] in Hq.
assert (Hc : q = 0%nat \/ q = 1%nat \/ q = 2%nat) by lia.
destruct Hc as [->|[->| ->]]; cbn [nth Z.of_nat]; [rewrite Z.add_0_r | |]; auto.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Let LAWS : AR_laws rsegs B := AR_laws_ok rsegs B.
(* __asan_memcpy at 0x51860 and the strlen wrapper's trampoline at 0x42194 *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6B_MEMCPY.
Hypothesis ASTRLEN : astrlen_realizes rsegs B W6B_STRLEN.

Theorem w6b_c1 : w6b_c1_stmt B MT.
Proof using MTL AMEMCPY ASTRLEN.
unfold w6b_c1_stmt, w6b_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp b r Hctx HP Hin Hvoc.
pose proof rts_segs_low as Hsegs. pose proof LAWS as HL.
pose proof Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
pose proof Hin as (H2 & H3 & H4 & H9 & H18 & H25 & H14 & H24 & H15 & H23 & H27 & H26 & H22 & V60 & Vb0 & Vc0 & Ve8 &
  V108 & V118 & V138 & Hvb & Hkd & Hpp & Hpp2 & HF4 & HF5 & HF32 & HFapp & Hez & Hera & Hehu & Hc1 & Hw6in & Hrhu & Hrdis).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HspR.
assert (HRlo : alloc_ceiling + 16384 <= R) by lia.
assert (HR47 : R + 0x1e0 <= 2 ^ 47) by lia.
assert (Hin3 : In (3, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (rts_fbounds F HF32 HFapp) as (_ & _ & Hsa0 & Hsac & Hsep & HamrF).
set (kd := bv_unsigned b) in *.
pose proof (H22 ltac:(lia)) as H22'.
set (cur := c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))).
set (j := c1_j r).
assert (Hj : 0 <= j < 9) by (apply c1_j_range).
set (x := w6b_vptr j).
set (l := c1_len j).
pose proof (c1_len_range j Hj) as Hl. fold l in Hl.
pose proof (c1_vptr_range j Hj) as Hx. fold x in Hx.
destruct (proj2 Hvoc j Hj) as [_ Hcs]. fold x in Hcs.
assert (Hlv : Z.of_nat (length (u8s (c1_v j))) = l) by (rewrite length_map; reflexivity).
assert (Hcur : 0 <= cur < 2 ^ 64).
{ subst cur. destruct r as [|b1 r1]; cbn [fuzz_u8 snd length]; destruct Hw6in as (_ & _ & Hc0 & Hcr & Ham & _);
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; cbn [length] in *; lia. }
(* ---------------- the head ---------------- *)
apply (c1_head B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp kd r _ Hctx Hin Hvoc).
intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G27 G26 Hm1 V100.
fold j x in G10, G27. fold cur in V100.
assert (L1 : c1_lowk W memc mem1) by (apply (c1_lowk_of W memc mem1 (fun a => R + 0x100 <= a < R + 0x108) Hm1); intros a Ha; lia).
change (nth (Z.to_nat j) vocab []) with (c1_v j) in Hcs.
assert (R2_1 : getr regs1 2 = w64 R) by (rewrite Hk1 by c1_out; exact H2).
assert (Hsp1 : spZ regs1 = sp0 + (R - sp0)) by (unfold spZ; rewrite R2_1; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (c1_cstr_lowk W memc mem1 _ _ L1 Hcs) as Hcs1.
pose proof (c1_rom_lowk W memc mem1 L1 Hrom) as Hrom1.
(* ---------------- the strlen wrapper ---------------- *)
eapply SRr_bind.
{ apply (rts_ecall_at B LAWS W regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k (R - sp0) (2 * ESTACK)
    (w64 C1_RSTR) (fun _ => False) (fun regs2 _ => getr regs2 10 = w64 l) W6B_STRLEN HJ1 Hsp1 ltac:(lia) ltac:(lia) G1
    ltac:(intros a [])).
  pose proof Hcs1 as (Hb1 & Hnul1 & Hrng1 & Hx0 & Hx63 & Himg1 & Ham1 & Hra1 & Hhu1).
  rewrite Hlv in Hb1, Hnul1, Hx63, Himg1, Ham1, Hra1, Hhu1.
  destruct (rts_stk_window B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 (R - sp0) (2 * ESTACK) HJ1 Hsp1
    ltac:(lia) ltac:(lia)) as (Hlo2 & Hpr2).
  eapply SRr_mono.
  - apply (ASTRLEN lyc Sc W regs1 mem1 md1 x l).
    + eapply (ecall_pre_at rsegs B) with (o := R - sp0); [exact HJ1 | exact Hsp1 | | lia | lia | | |].
      * rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
      * rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
      * rewrite Hk1 by c1_out. exact H3.
      * rewrite Hk1 by c1_out. exact H4.
    + exact Hlo2.
    + exact Hpr2.
    + exact G10.
    + lia.
    + lia.
    + lia.
    + lia.
    + split; [lia|]. split.
      * intros i Hi. exists (nth (Z.to_nat i) (u8s (c1_v j)) 0). split; [exact (Hb1 i ltac:(lia))|].
        assert (Hn : In (nth (Z.to_nat i) (u8s (c1_v j)) 0) (u8s (c1_v j))) by (apply nth_In; rewrite length_map; unfold l, c1_len in Hi |- *; lia).
        pose proof (proj1 (Forall_forall _ _) Hrng1 _ Hn) as Hb0. cbv beta in Hb0. lia.
      * intros _. exact Hnul1.
    + intros a Ha. split.
      * destruct (Z.eq_dec a (x + l)) as [->|Hne]; [rewrite Hnul1; discriminate|].
        replace a with (x + (a - x)) by lia. rewrite (Hb1 (a - x) ltac:(lia)). discriminate.
      * rewrite Hsp1. lia.
    + intros a Ha. rewrite Hsp1. lia.
    + exact Ham1.
    + exact Hra1.
    + exact Hhu1.
    + intros a Ha. destruct (c1_tail_rom j a Hj Ha) as [Hr1 Hr2].
      destruct (mbyte_rom W mem1 a Hrom1 Hr1 Hr2) as (bb & _ & Hm). unfold aview. rewrite Hm. discriminate.
    + intros a Ha _ _. exact (Hrom1 a Ha).
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HAR2 & HP2 & Hsame2 & H10 & Hfr2 & Hpres2).
    unfold rts_ecall_post. split; [reflexivity|]. exists regs2, mem2, md2.
    split; [exact Hc2|]. split; [exact HAR2|]. split; [exact HP2|]. split; [exact Hsame2|]. split; [exact H10|].
    split; [intros a Ha _ Hn; exact (Hfr2 a Ha Hn) | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame2 & H10s & K2).
assert (K2' : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 2 * ESTACK <= a < R) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn; apply K2; [exact Ha | intros [] | lia]).
clear K2. rename K2' into K2.
assert (L2 : c1_lowk W mem1 mem2) by (apply (c1_lowk_of W mem1 mem2 (fun a => R - 2 * ESTACK <= a < R) K2); intros a Ha; lia).
change (mkCfg (mkst regs2 (w64 C1_RSTR) mem2 (seg_rom rsegs)) md2) with (cfg_at rsegs C1_RSTR regs2 mem2 md2).
assert (R9_2 : getr regs2 9 = w64 R) by (rewrite (c1_pres regs1 regs2 9%bv HP2) by c1_cs; rewrite Hk1 by c1_out; exact H9).
assert (R27_2 : getr regs2 27 = w64 x) by (rewrite (c1_pres regs1 regs2 27%bv HP2) by c1_cs; exact G27).
(* ---------------- the middle ---------------- *)
apply (c1_mid B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 R F l x _ HJ2 R9_2 ltac:(lia) HR47 HR16
  H10s Hl R27_2).
{ apply (rts_val_kept (w_H W) memc mem2 (R + 0x108) 8); [|exact V108].
  intros q Hq. change (Z.of_nat 8) with 8 in Hq. rewrite K2 by lia. apply Hm1; lia. }
{ lia. }
{ lia. }
intros regs3 mem3 md3 HJ3 Hio3 Hk3 G1c G10c G11c G12c G23c G24c G25c Hm3.
assert (L3 : c1_lowk W memc mem3).
{ intros a Ha. rewrite Hm3. rewrite (L2 a Ha). exact (L1 a Ha). }
assert (R2_3 : getr regs3 2 = w64 R) by (rewrite Hk3 by c1_out; rewrite (c1_pres regs1 regs2 2%bv HP2) by c1_cs; exact R2_1).
assert (Hsp3 : spZ regs3 = sp0 + (R - sp0)) by (unfold spZ; rewrite R2_3; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (c1_cstr_lowk W memc mem3 _ _ L3 Hcs) as Hcs3.
pose proof Hcs3 as (Hb3 & _ & _ & Hx0' & Hx63 & Himg3 & Ham3 & Hra3 & Hhu3).
rewrite Hlv in Hb3, Hx63, Himg3, Ham3, Hra3, Hhu3.
(* the frame's bytes are not image bytes *)
assert (Hnimg : forall a, F <= a < F + 512 -> ~ in_img rsegs a).
{ intros a Ha. apply (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR ltac:(right; left; exists 3, pos; split;
    [exact Hin3 | rewrite <- HFa; change (fs_frame_bytes 3) with 512; lia]))). }
(* e's shadow bytes lie below the ceiling and outside e *)
assert (HshF : forall o, 0 <= o < 512 -> shadow_of_addr SHADOW_OFF (F + o) = shadow_addr F + o / 8)
  by (intros o Ho; apply rts_fsh_of; [exact HF32 | lia]).
(* ---------------- __asan_memcpy ---------------- *)
eapply SRr_bind.
{ apply (rts_intrin_at B LAWS OCpy W6B_MEMCPY AMEMCPY W regs3 mem3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md3 k
    (F + 0xf8) x l (R - sp0) (w64 C1_RCPY) HJ3 G10c G11c G12c).
  - lia.
  - lia.
  - lia.
  - exact Hsp3.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - lia.
  - rewrite Hk3 by c1_out. rewrite (c1_pres regs1 regs2 3%bv HP2) by c1_cs. rewrite Hk1 by c1_out. exact H3.
  - rewrite Hk3 by c1_out. rewrite (c1_pres regs1 regs2 4%bv HP2) by c1_cs. rewrite Hk1 by c1_out. exact H4.
  - exact G1c.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split; [apply (rts_awr_fobj STK sp0 FP _ _ lyc own pos a Hown); rewrite <- HFa; lia | lia].
  - apply HamrF; lia.
  - apply (rtm_ra_kept rsegs (w_H W) memc (w_H W) mem3 SHADOW_OFF (F + 0xf8) l).
    + apply (ra_sub _ _ (F + 0xf0) 104); [exact Hera | lia | lia].
    + intros a Ha. replace a with (F + (a - F)) by lia. rewrite (HshF (a - F)) by lia.
      apply L3. assert (0 <= (a - F) / 8 < 64) by (clear - Ha Hl; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      lia.
  - intros Hn s Hs. rewrite (L3 s).
    + exact (rtm_hull_sub _ (F + 0xf0) 104 (F + 0xf8) l Hehu ltac:(lia) ltac:(lia) ltac:(lia) s Hs).
    + assert (A1 : shadow_addr (F + 0xf8 + l - 1) <= shadow_addr F + 34).
      { replace (F + 0xf8 + l - 1) with (F + (0xf8 + l - 1)) by lia. rewrite (rts_fsh_addr F (0xf8 + l - 1) HF32) by lia.
        assert ((0xf8 + l - 1) / 8 <= 34) by (clear - Hl; apply Z.div_le_upper_bound; lia). lia. }
      assert (A2 : 0 <= shadow_addr (F + 0xf8)) by (clear - HF4; unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (F + 0xf8) 8); lia).
      clear - Hs A1 A2 Hsac. lia.
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite Hsp3; lia].
      replace a with (x + (a - x)) by lia. rewrite (Hb3 (a - x) ltac:(lia)). discriminate. }
    split.
    { destruct (Z_le_gt_dec (F + 0xf8 + l) x) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (x + l) (F + 0xf8)) as [Y|Y]; [right; exact Y|].
      exfalso. apply (Hnimg (Z.max x (F + 0xf8)) ltac:(lia)).
      replace (Z.max x (F + 0xf8)) with (x + (Z.max x (F + 0xf8) - x)) by lia. apply Himg3. lia. }
    split; [unfold amem_range in *; lia|].
    split; [apply (ra_sub _ _ x (l + 1)); [exact Hra3 | lia | lia]|].
    intros Hn. apply (rtm_hull_sub _ x (l + 1) x l Hhu3); lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hsame4 & H10m & Heff4 & K4).
replace (sp0 + (R - sp0)) with R in K4 by lia.
cbv iota in Heff4.
change (mkCfg (mkst regs4 (w64 C1_RCPY) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs C1_RCPY regs4 mem4 md4).
(* the bytes below the ceiling and outside the copy are the entry's *)
assert (KM4 : forall a, 0 <= a < alloc_ceiling -> ~ (F + 0xf8 <= a < F + 0xf8 + l) ->
  aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (K4 a ltac:(lia) Hn ltac:(lia)). exact (L3 a Ha). }
assert (RS : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> ~ In r0 c1m_clob -> getr regs4 r0 = getr regs2 r0).
{ intros r0 Hc Hn. rewrite (c1_pres regs3 regs4 r0 HP4 Hc). apply Hk3; [|exact Hn].
  intros E0. rewrite E0 in Hc. unfold acallee_saved in Hc. lia. }
assert (R9_4 : getr regs4 9 = w64 R) by (rewrite RS by first [c1_cs | c1_out]; exact R9_2).
assert (R18_4 : getr regs4 18 = w64 SHADOW_OFF)
  by (rewrite RS by first [c1_cs | c1_out]; rewrite (c1_pres regs1 regs2 18%bv HP2) by c1_cs; rewrite Hk1 by c1_out; exact H18).
assert (R22_4 : getr regs4 22 = w64 (c1_s6 kd))
  by (rewrite RS by first [c1_cs | c1_out]; rewrite (c1_pres regs1 regs2 22%bv HP2) by c1_cs; rewrite Hk1 by c1_out; exact H22').
assert (R26_4 : getr regs4 26 = w64 (Z.of_nat (length (snd (fuzz_u8 r)))))
  by (rewrite RS by first [c1_cs | c1_out]; rewrite (c1_pres regs1 regs2 26%bv HP2) by c1_cs; exact G26).
(* ---------------- the tail ---------------- *)
apply (c1_tail B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem4 md4 regs4 R F pos l vb pp cur kd _ HJ4 Hown HFa
  R9_4 ltac:(lia) HR47 HR16 R18_4 R22_4 ltac:(lia)).
{ rewrite (c1_pres regs3 regs4 23%bv HP4) by c1_cs. exact G23c. }
{ rewrite (c1_pres regs3 regs4 24%bv HP4) by c1_cs. exact G24c. }
{ rewrite (c1_pres regs3 regs4 25%bv HP4) by c1_cs. exact G25c. }
{ exact (c1_len_vals j Hj). }
{ exact Hvb. }
{ lia. }
{ exact Hpp2. }
{ exact Hcur. }
all: try (lazymatch goal with |- val_mem _ (mrestrict _ ?m4) (?R0 + ?o) 8 ?v =>
  apply (rts_val_kept (w_H W) memc m4 (R0 + o) 8); [intros q Hq; change (Z.of_nat 8) with 8 in Hq;
    rewrite K4 by lia; rewrite Hm3; rewrite K2 by lia; apply Hm1; lia|]; assumption end).
{ apply (rts_val_kept (w_H W) mem1 mem4 (R + 0x100) 8); [|exact V100].
  intros q Hq. change (Z.of_nat 8) with 8 in Hq. rewrite K4 by lia. rewrite Hm3. apply K2; lia. }
{ intros i Hi. rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem4) by (apply KM4; lia).
  replace (F + 0xf8 + l + i) with (F + 0xf0 + (8 + l + i)) by lia. apply Hez. lia. }
{ apply (rtm_ra_kept rsegs (w_H W) memc (w_H W) mem4 SHADOW_OFF (F + 0xf0) 104 Hera).
  intros a Ha. replace a with (F + (a - F)) by lia. rewrite (HshF (a - F)) by lia.
  assert (0 <= (a - F) / 8 < 64) by (clear - Ha; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply KM4; lia. }
intros regs5 mem5 md5 HJ5 Hio5 Hk5 J22 J23 J26 J27 J25 J24 V0 V4 Vt0 Vt1 Vt2 K5.
(* ---------------- the join's post ---------------- *)
apply SRr_ret. unfold rts_post. exists lyc, Sc, regs5, mem5, md5.
split; [reflexivity|].
split; [exact HJ5|].
split.
{ intros r0 Hr0 Hn.
  assert (Hcs0 : acallee_saved (bv_unsigned r0)).
  { apply (rts_callee r0 Hr0). intros X. apply Hn. unfold w6b_clob, rts_caller_saved in *. cbn [In] in X |- *. tauto. }
  assert (N1 : forall l0 : list (bv 5), incl l0 w6b_clob -> ~ In r0 l0) by (intros l0 Hi X; exact (Hn (Hi r0 X))).
  rewrite Hk5 by (first [exact Hr0 | apply N1; intros y Hy; cbn [In c1t_clob w6b_clob] in *; tauto]).
  rewrite RS by (first [exact Hcs0 | apply N1; intros y Hy; cbn [In c1m_clob w6b_clob] in *; tauto]).
  rewrite (c1_pres regs1 regs2 r0 HP2 Hcs0).
  apply Hk1; [exact Hr0 | apply N1; intros y Hy; cbn [In c1_hclob w6b_clob] in *; tauto]. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [apply same_io_materialized; exact Hsame2|].
  eapply same_io_trans; [exact Hio3|]. eapply same_io_trans; [apply same_io_materialized; exact Hsame4|]. exact Hio5. }
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. unfold w6b_wr, T_SEG_STK, ASTACK in Hn. rewrite (K5 a Ha ltac:(lia) ltac:(lia)), (K4 a Ha ltac:(lia) ltac:(lia)), Hm3.
  rewrite (K2 a Ha ltac:(lia)). apply Hm1; [exact Ha | lia]. }
unfold w6b_J_R. rewrite (c1_model b r HP). cbn [fst snd]. fold kd j cur.
split; [exact J22|]. split; [exact J23|]. split; [exact J26|]. split; [exact J27|].
split; [exact J25|].
split; [rewrite J24; exact R26_4|].
rewrite (c1_ent_bytes (Z.testbit kd 7) j Hj). fold l.
assert (EA : forall a l1 l2, garr8 rsegs (mrestrict (w_H W) mem5) a l1 ->
  garr8 rsegs (mrestrict (w_H W) mem5) (a + Z.of_nat (length l1)) l2 -> garr8 rsegs (mrestrict (w_H W) mem5) a (l1 ++ l2))
  by (intros a l1 l2 G1' G2'; apply (proj2 (garr8_app rsegs _ _ _ _)); split; assumption).
apply EA; [exact (rtm_bytes_of_val rsegs (w_H W) mem5 (F + 0xf0) 4%nat 8 V0)|].
rewrite length_map, length_le32. replace (F + 0xf0 + Z.of_nat 4) with (F + 0xf4) by lia.
apply EA; [exact (rtm_bytes_of_val rsegs (w_H W) mem5 (F + 0xf4) 4%nat _ V4)|].
rewrite length_map, length_le32. replace (F + 0xf4 + Z.of_nat 4) with (F + 0xf8) by lia.
apply EA.
{ intros q Hq. rewrite length_map in Hq.
  assert (Hq' : 0 <= Z.of_nat q < l) by (unfold l, c1_len; lia).
  apply (rtm_aview_val1 rsegs). rewrite K5 by lia.
  rewrite (Heff4 (Z.of_nat q) Hq').
  specialize (Hb3 (Z.of_nat q) ltac:(lia)). rewrite Nat2Z.id in Hb3. exact Hb3. }
rewrite length_map. replace (F + 0xf8 + Z.of_nat (length (c1_v j))) with (F + 0xf8 + l) by (unfold l, c1_len; lia).
apply EA.
{ apply c1_garr8_3;
  [ exact Vt0 | replace (F + 0xf8 + l + 1) with (F + 0xf9 + l) by lia; exact Vt1
  | replace (F + 0xf8 + l + 2) with (F + 0xfa + l) by lia; exact Vt2 | lia | destruct (Z.testbit kd 7); lia | lia ]. }
cbn [length]. apply garr8_zeros. intros a Ha. rewrite Z2Nat.id in Ha by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem5).
- replace a with (F + 0xf0 + (a - (F + 0xf0))) by lia. apply Hez. lia.
- rewrite (K5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply KM4; lia.
Qed.
End d.
End b.

Print Assumptions w6b_c1.
