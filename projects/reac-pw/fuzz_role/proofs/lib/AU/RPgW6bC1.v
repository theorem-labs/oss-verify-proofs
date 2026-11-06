(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bC1.v at 32f84792c2a6; for image B
   (fuzz_rate.asan-ubsan): the block lemma is w6bb_c1 of lib/AU/RtPgW6bBaseB.v over RtPgStepsB.rtsb_post; the pcs,
   registers and real-frame cells are image B's; the pod object is e62 (F + 0x210) in the class-4 frame (4, pos); the
   kind byte and what is left reach the tail through the spill cells [R+0x128] and [R+0x70]; the cursor stays in s10;
   the strlen wrapper's hypothesis is at image B's entry 0x421ec (lib/A/Rt/StrlenDef.v astrlen_realizes, the
   image-parametric definition only); the prefix c1_ becomes c1b_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bC1B.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v rl_ and lib/AU/RPgMem.v rm_ names, lib/AU/Rt/StrlenDef.v); the block lemma is
   lib/AU/RPgW6bBase.v's w6bb_c1_stmt over RPgSteps.rl_wpost; the chain runs through role B's pcs (checked_memcpy
   0x5116c, the strlen wrapper 0x41b60); the cursor reaches the tail through the spill cell [R+0x58] and the kind
   byte through [R+0x118]; what is left stays in s4 and e62.body in s10 (both callee-saved, kept by the two calls);
   at J a3 is the cursor, t1 what is left, s6 = pp + 0x4000 and a5 = pp. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the block lemma w6bb_c1 of
   lib/AU/RPgW6bBase.v, ent_build's case 1 (pod.h:286-294) inside LLVMFuzzerTestOneInput (0x80020), from the case
   entry 0x810d0 to the join J 0x818d8. Proves no function (kind: segment lemma).
   THE CHAIN (lib/AU/RPgW6bC1Kit.v):
     c1b_head (RPgW6bC1a.v)       0x810d0 .. 0x41b60   i = fuzz_u8 % 9, s10 = e62.body, [R+0x58] := the cursor,
                                                       [R+0x118] := the kind byte, s4 = what is left,
                                                       a0 = s6 = vocab[i]
     the strlen wrapper            0x41b60 .. 0x813f4   ASTRLEN (lib/AU/Rt/StrlenDef.v astrlen_realizes at W6BB_STRLEN)
                                                       through lib/AU/RPgSteps.v rl_ecall_at: a0 = |vocab[i]|
     c1b_mid (RPgW6bC1a.v)        0x813f4 .. 0x5116c   l = |vocab[i]| (12 .. 18, never clamped)
     checked_memcpy                0x5116c .. 0x81418   AMEMCPY (lib/Reusable/YG0d.v aintrin_realizes OCpy) through
                                                       lib/AU/RPgSteps.v rl_intrin_at: e62.body[0..l) := vocab[i]
     c1b_tail (RPgW6bC1b.v)       0x81418 .. J         the NUL, e62.type, e62.size, and with kind & 0x80 'x', NUL
   The post is RPgSteps.rl_wpost at J with the layout, state and world of the entry (no call changes them), the
   registers outside w6bb_clob kept by every piece, every byte outside w6bb_wr kept, and w6bb_J_R: e62's 104 bytes
   are the header from the tail's stores, the string copied from the image (rl_cstr of w6bb_vocab_ok), the three bytes
   after it from the tail and the rest the entry's zeros. The model's entry (c1b_model): ent_text of vocab[i % 9]
   (at most 18 bytes, so the 95-byte clamp never cuts), extended by 'x', NUL when kind & 0x80 (|v| + 3 <= 96 always
   holds). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YP08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgMem RPgSteps RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW6bC1Kit RPgW6bC1a RPgW6bC1b.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU.Rt Require Import StrlenDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* lia reasons about the divisions and remainders in this file (RPgSteps.v turns that off for its importers) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Local Abbreviation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ======================================== the model ======================================== *)
Definition c1b_ent (x : bool) (j : Z) : ent :=
  if x then Ent POD_STRING (c1b_len j + 3) ((c1b_v j ++ [NUL]) ++ [Z_to_bv 8 120; NUL])
  else Ent POD_STRING (c1b_len j + 1) (c1b_v j ++ [NUL]).
Lemma c1b_model : forall (b : byte) (r : list byte), bv_unsigned b mod 10 = 1 ->
  ent_build (b :: r) = (c1b_ent (Z.testbit (bv_unsigned b) 7) (c1b_j r), snd (fuzz_u8 r)).
Proof.
intros b r H. unfold ent_build, c1b_j. cbn [fuzz_u8]. rewrite H.
destruct (fuzz_u8 r) as [i r'] eqn:Hf. cbn [fst snd]. f_equal.
assert (Hj : 0 <= i mod 9 < 9) by (apply Z.mod_pos_bound; lia).
revert Hj. generalize (i mod 9) as j. intros j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
destruct (Z.testbit (bv_unsigned b) 7);
  destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
Qed.
Lemma c1b_ent_bytes : forall x j, 0 <= j < 9 ->
  u8s (ent_mem (c1b_ent x j)) =
  u8s (le32 8) ++ u8s (le32 (if x then c1b_len j + 3 else c1b_len j + 1)) ++ u8s (c1b_v j) ++
  [0; (if x then 120 else 0); 0] ++ repeat 0 (Z.to_nat (93 - c1b_len j)).
Proof.
intros x j Hj.
assert (E : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8) by lia.
destruct x; destruct E as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]; vm_compute; reflexivity.
Qed.

(* ======================================== helpers ======================================== *)
Lemma c1b_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply H. exact Hr. Qed.
Ltac c1b_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with v end; lia.
Lemma c1b_garr8_3 : forall {fx : YK11.FPState} m a v0 v1 v2,
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
(* checked_memcpy at 0x5116c and the strlen wrapper at 0x41b60 *)
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6BB_MEMCPY.
Hypothesis ASTRLEN : astrlen_realizes rsegs B W6BB_STRLEN.

Theorem w6bb_c1 : w6bb_c1_stmt B MT.
Proof using MTL AMEMCPY ASTRLEN.
unfold w6bb_c1_stmt, w6bb_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp b r Hctx HP Hin Hvoc.
pose proof rl_segs_low as Hsegs. pose proof LAWS as HL.
pose proof Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H19 & H18 & H16 & H22 & H6 & H20 & H13 & V48 & Vf0 & V110 & V130 & V140 &
  V158 & Hkd & Hpp & Hpp2 & HF4 & HF5 & HF32 & HFapp & Hez & Hera & Hehu & Hc1 & Hinp).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (Hes : ESTACK = 4096) by reflexivity.
unfold T_SEG_STK, ASTACK in HspR.
assert (HRlo : alloc_ceiling + 16384 <= R) by lia.
assert (HR47 : R + 0x200 <= 2 ^ 47) by lia.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (rl_fbounds F HF32 HFapp) as (_ & _ & Hsa0 & Hsac & Hsep & HamrF).
set (kd := bv_unsigned b) in *.
set (t := Z.of_nat (length (snd (fuzz_u8 r)))).
set (cur := c + Z.of_nat (length r) - t).
set (j := c1b_j r).
assert (Hj : 0 <= j < 9) by (apply c1b_j_range).
set (x := w6bb_vptr j).
set (l := c1b_len j).
pose proof (c1b_len_range j Hj) as Hl. fold l in Hl.
pose proof (c1b_vptr_range j Hj) as Hx. fold x in Hx.
destruct (proj2 Hvoc j Hj) as [_ Hcs]. fold x in Hcs.
assert (Hlv : Z.of_nat (length (u8s (c1b_v j))) = l) by (rewrite length_map; reflexivity).
assert (Ht : 0 <= t <= Z.of_nat (length r)).
{ subst t. destruct r as [|b1 r1]; cbn [fuzz_u8 snd length]; lia. }
assert (Hcur : 0 <= cur < 2 ^ 64).
{ subst cur. destruct Hinp as (_ & _ & Hc0 & Hcr & _). lia. }
(* ---------------- the head ---------------- *)
apply (c1b_head B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pp kd r _ Hctx Hin HP Hvoc).
intros regs1 mem1 md1 HJ1 Hio1 Hk1 G1 G10 G22 G20 G26 Hm1 V58 V118.
fold j x in G10, G22. fold t in G20. fold t cur in V58.
assert (L1 : c1b_lowk W memc mem1)
  by (apply (c1b_lowk_of W memc mem1 (fun a => R + 0x58 <= a < R + 0x60 \/ R + 0x118 <= a < R + 0x120) Hm1); intros a Ha; lia).
change (nth (Z.to_nat j) vocab []) with (c1b_v j) in Hcs.
assert (R2_1 : getr regs1 2 = w64 R) by (rewrite Hk1 by c1b_out; exact H2).
assert (Hsp1 : spZ regs1 = sp0 + (R - sp0)) by (unfold spZ; rewrite R2_1; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (c1b_cstr_lowk W memc mem1 _ _ L1 Hcs) as Hcs1.
pose proof (c1b_rom_lowk W memc mem1 L1 Hrom) as Hrom1.
(* ---------------- the strlen wrapper ---------------- *)
eapply SRr_bind.
{ apply (rl_ecall_at B LAWS W regs1 mem1 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md1 k (R - sp0) (2 * ESTACK)
    (w64 C1B_RSTR) (fun _ => False) (fun regs2 _ => getr regs2 10 = w64 l) W6BB_STRLEN HJ1 Hsp1 ltac:(lia) ltac:(lia) G1
    ltac:(intros a [])).
  pose proof Hcs1 as (Hb1 & Hnul1 & Hrng1 & Hx0 & Hx63 & Himg1 & Ham1 & Hra1 & Hhu1).
  rewrite Hlv in Hb1, Hnul1, Hx63, Himg1, Ham1, Hra1, Hhu1.
  destruct (rl_stk_window B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem1 md1 k regs1 (R - sp0) (2 * ESTACK) HJ1 Hsp1
    ltac:(lia) ltac:(lia)) as (Hlo2 & Hpr2).
  eapply SRr_mono.
  - apply (ASTRLEN lyc Sc W regs1 mem1 md1 x l).
    + eapply (ecall_pre_at rsegs B) with (o := R - sp0); [exact HJ1 | exact Hsp1 | | lia | lia | | |].
      * rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
      * rewrite G1. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
      * rewrite Hk1 by c1b_out. exact H3.
      * rewrite Hk1 by c1b_out. exact H4.
    + exact Hlo2.
    + exact Hpr2.
    + exact G10.
    + lia.
    + lia.
    + lia.
    + lia.
    + split; [lia|]. split.
      * intros i Hi. exists (nth (Z.to_nat i) (u8s (c1b_v j)) 0). split; [exact (Hb1 i ltac:(lia))|].
        assert (Hn : In (nth (Z.to_nat i) (u8s (c1b_v j)) 0) (u8s (c1b_v j)))
          by (apply nth_In; rewrite length_map; unfold l, c1b_len in Hi |- *; lia).
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
    + intros a Ha. destruct (c1b_tail_rom j a Hj Ha) as [Hr1 Hr2].
      destruct (mbyte_rom W mem1 a Hrom1 Hr1 Hr2) as (bb & _ & Hm). unfold aview. rewrite Hm. discriminate.
    + intros a Ha _ _. exact (Hrom1 a Ha).
  - cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & Hc2 & HAR2 & HP2 & Hsame2 & H10 & Hfr2 & Hpres2).
    unfold rl_ecall_post. split; [reflexivity|]. exists regs2, mem2, md2.
    split; [exact Hc2|]. split; [exact HAR2|]. split; [exact HP2|]. split; [exact Hsame2|]. split; [exact H10|].
    split; [intros a Ha _ Hn; exact (Hfr2 a Ha Hn) | exact Hpres2]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hsame2 & H10s & K2).
assert (K2' : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 2 * ESTACK <= a < R) -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) mem1 a)
  by (intros a Ha Hn; apply K2; [exact Ha | intros [] | lia]).
clear K2. rename K2' into K2.
assert (L2 : c1b_lowk W mem1 mem2)
  by (apply (c1b_lowk_of W mem1 mem2 (fun a => R - 2 * ESTACK <= a < R) K2); intros a Ha; lia).
change (mkCfg (mkst regs2 (w64 C1B_RSTR) mem2 (seg_rom rsegs)) md2) with (cfg_at rsegs C1B_RSTR regs2 mem2 md2).
assert (R22_2 : getr regs2 22 = w64 x) by (rewrite (c1b_pres regs1 regs2 22%bv HP2) by c1b_cs; exact G22).
assert (R26_2 : getr regs2 26 = w64 (F + 0x218)) by (rewrite (c1b_pres regs1 regs2 26%bv HP2) by c1b_cs; exact G26).
(* ---------------- the middle ---------------- *)
apply (c1b_mid B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem2 md2 regs2 F l x _ HJ2 H10s Hl R22_2 R26_2).
intros regs3 mem3 md3 HJ3 Hio3 Hk3 G1c G10c G11c G12c G18c G24c Hm3.
assert (L3 : c1b_lowk W memc mem3).
{ intros a Ha. rewrite Hm3. rewrite (L2 a Ha). exact (L1 a Ha). }
assert (R2_3 : getr regs3 2 = w64 R)
  by (rewrite Hk3 by c1b_out; rewrite (c1b_pres regs1 regs2 2%bv HP2) by c1b_cs; exact R2_1).
assert (Hsp3 : spZ regs3 = sp0 + (R - sp0)) by (unfold spZ; rewrite R2_3; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof (c1b_cstr_lowk W memc mem3 _ _ L3 Hcs) as Hcs3.
pose proof Hcs3 as (Hb3 & _ & _ & Hx0' & Hx63 & Himg3 & Ham3 & Hra3 & Hhu3).
rewrite Hlv in Hb3, Hx63, Himg3, Ham3, Hra3, Hhu3.
(* the frame's bytes are not image bytes *)
assert (Hnimg : forall a, F <= a < F + 1024 -> ~ in_img rsegs a).
{ intros a Ha. apply (proj2 (al_client_img _ _ LAWS lyc Sc W memc mdc a HAR ltac:(right; left; exists 4, pos; split;
    [exact Hin4 | rewrite <- HFa; change (fs_frame_bytes 4) with 1024; lia]))). }
(* e62's shadow bytes lie below the ceiling and outside e62 *)
assert (HshF : forall o, 0 <= o < 1024 -> shadow_of_addr SHADOW_OFF (F + o) = shadow_addr F + o / 8)
  by (intros o Ho; apply rl_fsh_of; [exact HF32 | lia]).
(* ---------------- checked_memcpy ---------------- *)
eapply SRr_bind.
{ apply (rl_intrin_at B LAWS OCpy W6BB_MEMCPY AMEMCPY W regs3 mem3 STK sp0 FP ly S W0 mem0 md0 own lyc Sc md3 k
    (F + 0x218) x l (R - sp0) (w64 C1B_RCPY) HJ3 G10c G11c G12c).
  - lia.
  - lia.
  - lia.
  - exact Hsp3.
  - rewrite Zminus_mod, HR16, Hsp0al. reflexivity.
  - lia.
  - lia.
  - rewrite Hk3 by c1b_out. rewrite (c1b_pres regs1 regs2 3%bv HP2) by c1b_cs. rewrite Hk1 by c1b_out. exact H3.
  - rewrite Hk3 by c1b_out. rewrite (c1b_pres regs1 regs2 4%bv HP2) by c1b_cs. rewrite Hk1 by c1b_out. exact H4.
  - exact G1c.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split; [apply (rl_awr_fobj STK sp0 FP _ _ lyc own pos a Hown); rewrite <- HFa; lia | lia].
  - apply HamrF; lia.
  - apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem3 SHADOW_OFF (F + 0x218) l).
    + apply (ra_sub _ _ (F + 0x210) 104); [exact Hera | lia | lia].
    + intros a Ha. replace a with (F + (a - F)) by lia. rewrite (HshF (a - F)) by lia.
      apply L3. assert (0 <= (a - F) / 8 < 128) by (clear - Ha Hl; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
      lia.
  - intros Hn s Hs. rewrite (L3 s).
    + exact (rm_hull_sub _ (F + 0x210) 104 (F + 0x218) l Hehu ltac:(lia) ltac:(lia) ltac:(lia) s Hs).
    + assert (A1 : shadow_addr (F + 0x218 + l - 1) <= shadow_addr F + 70).
      { replace (F + 0x218 + l - 1) with (F + (0x218 + l - 1)) by lia. rewrite (rl_fsh_addr F (0x218 + l - 1) HF32) by lia.
        assert ((0x218 + l - 1) / 8 <= 70) by (clear - Hl; apply Z.div_le_upper_bound; lia). lia. }
      assert (A2 : 0 <= shadow_addr (F + 0x218)) by (clear - HF4; unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos (F + 0x218) 8); lia).
      clear - Hs A1 A2 Hsac. lia.
  - cbv iota. split; [lia|]. split; [lia|]. split.
    { intros a Ha. split; [|rewrite Hsp3; lia].
      replace a with (x + (a - x)) by lia. rewrite (Hb3 (a - x) ltac:(lia)). discriminate. }
    split.
    { destruct (Z_le_gt_dec (F + 0x218 + l) x) as [X|X]; [left; exact X|].
      destruct (Z_le_gt_dec (x + l) (F + 0x218)) as [Y|Y]; [right; exact Y|].
      exfalso. apply (Hnimg (Z.max x (F + 0x218)) ltac:(lia)).
      replace (Z.max x (F + 0x218)) with (x + (Z.max x (F + 0x218) - x)) by lia. apply Himg3. lia. }
    split; [unfold amem_range in *; lia|].
    split; [apply (ra_sub _ _ x (l + 1)); [exact Hra3 | lia | lia]|].
    intros Hn. apply (rm_hull_sub _ x (l + 1) x l Hhu3); lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hsame4 & H10m & Heff4 & K4).
replace (sp0 + (R - sp0)) with R in K4 by lia.
cbv iota in Heff4.
change (mkCfg (mkst regs4 (w64 C1B_RCPY) mem4 (seg_rom rsegs)) md4) with (cfg_at rsegs C1B_RCPY regs4 mem4 md4).
(* the bytes below the ceiling and outside the copy are the entry's *)
assert (KM4 : forall a, 0 <= a < alloc_ceiling -> ~ (F + 0x218 <= a < F + 0x218 + l) ->
  aview rsegs (w_H W) mem4 a = aview rsegs (w_H W) memc a).
{ intros a Ha Hn. rewrite (K4 a ltac:(lia) Hn ltac:(lia)). exact (L3 a Ha). }
assert (RS : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> ~ In r0 c1bm_clob -> getr regs4 r0 = getr regs2 r0).
{ intros r0 Hc Hn. rewrite (c1b_pres regs3 regs4 r0 HP4 Hc). apply Hk3; [|exact Hn].
  intros E0. rewrite E0 in Hc. unfold acallee_saved in Hc. lia. }
assert (R9_4 : getr regs4 9 = w64 R)
  by (rewrite RS by first [c1b_cs | c1b_out]; rewrite (c1b_pres regs1 regs2 9%bv HP2) by c1b_cs; rewrite Hk1 by c1b_out; exact H9).
assert (R27_4 : getr regs4 27 = w64 SHADOW_OFF)
  by (rewrite RS by first [c1b_cs | c1b_out]; rewrite (c1b_pres regs1 regs2 27%bv HP2) by c1b_cs; rewrite Hk1 by c1b_out; exact H27).
assert (R20_4 : getr regs4 20 = w64 t)
  by (rewrite RS by first [c1b_cs | c1b_out]; rewrite (c1b_pres regs1 regs2 20%bv HP2) by c1b_cs; exact G20).
assert (R26_4 : getr regs4 26 = w64 (F + 0x218)) by (rewrite RS by first [c1b_cs | c1b_out]; exact R26_2).
(* ---------------- the tail ---------------- *)
apply (c1b_tail B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W mem4 md4 regs4 R F pos l pp t cur kd _ HJ4 Hown HFa
  R9_4 ltac:(lia) HR47 HR16 R27_4).
{ rewrite (c1b_pres regs3 regs4 18%bv HP4) by c1b_cs. exact G18c. }
{ rewrite (c1b_pres regs3 regs4 24%bv HP4) by c1b_cs. exact G24c. }
{ exact R26_4. }
{ exact R20_4. }
{ exact (c1b_len_vals j Hj). }
{ lia. }
{ lia. }
{ exact Hpp2. }
{ destruct Hinp as (_ & _ & _ & Hcr & _). lia. }
{ exact Hcur. }
all: try (lazymatch goal with |- val_mem _ (mrestrict _ ?m4) (?R0 + ?o) 8 ?v =>
  apply (rl_val_kept (w_H W) memc m4 (R0 + o) 8); [intros q Hq; change (Z.of_nat 8) with 8 in Hq;
    rewrite K4 by lia; rewrite Hm3; rewrite K2 by lia; apply Hm1; lia|]; assumption end).
{ apply (rl_val_kept (w_H W) mem1 mem4 (R + 0x58) 8); [|exact V58].
  intros q Hq. change (Z.of_nat 8) with 8 in Hq. rewrite K4 by lia. rewrite Hm3. apply K2; lia. }
{ apply (rl_val_kept (w_H W) mem1 mem4 (R + 0x118) 8); [|exact V118].
  intros q Hq. change (Z.of_nat 8) with 8 in Hq. rewrite K4 by lia. rewrite Hm3. apply K2; lia. }
{ intros i Hi. rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem4) by (apply KM4; lia).
  replace (F + 0x218 + l + i) with (F + 0x210 + (8 + l + i)) by lia. apply Hez. lia. }
{ apply (rm_ra_kept rsegs (w_H W) memc (w_H W) mem4 SHADOW_OFF (F + 0x210) 104 Hera).
  intros a Ha. replace a with (F + (a - F)) by lia. rewrite (HshF (a - F)) by lia.
  assert (0 <= (a - F) / 8 < 128) by (clear - Ha; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply KM4; lia. }
intros regs5 mem5 md5 HJ5 Hio5 Hk5 J22 J15 J13 J6 V0 V4 Vt0 Vt1 Vt2 K5.
(* ---------------- the join's post ---------------- *)
apply SRr_ret. unfold rl_wpost. exists lyc, Sc, regs5, mem5, md5.
split; [reflexivity|].
split; [exact HJ5|].
split.
{ intros r0 Hr0 Hn.
  assert (Hcs0 : acallee_saved (bv_unsigned r0)).
  { apply (rl_callee r0 Hr0). intros X. apply Hn. unfold w6bb_clob, rl_caller_saved in *. cbn [In] in X |- *. tauto. }
  assert (N1 : forall l0 : list (bv 5), incl l0 w6bb_clob -> ~ In r0 l0) by (intros l0 Hi X; exact (Hn (Hi r0 X))).
  rewrite Hk5 by (first [exact Hr0 | apply N1; intros y Hy; cbn [In c1bt_clob w6bb_clob] in *; tauto]).
  rewrite RS by (first [exact Hcs0 | apply N1; intros y Hy; cbn [In c1bm_clob w6bb_clob] in *; tauto]).
  rewrite (c1b_pres regs1 regs2 r0 HP2 Hcs0).
  apply Hk1; [exact Hr0 | apply N1; intros y Hy; cbn [In c1b_hclob w6bb_clob] in *; tauto]. }
split; [reflexivity|].
split; [apply Permutation_refl|].
split.
{ eapply same_io_trans; [exact Hio1|]. eapply same_io_trans; [apply same_io_materialized; exact Hsame2|].
  eapply same_io_trans; [exact Hio3|]. eapply same_io_trans; [apply same_io_materialized; exact Hsame4|]. exact Hio5. }
split; [apply mo_le_refl; exact MTL|].
split.
{ intros a Ha Hn. unfold w6bb_wr, T_SEG_STK, ASTACK in Hn.
  rewrite (K5 a Ha ltac:(lia) ltac:(lia)), (K4 a Ha ltac:(lia) ltac:(lia)), Hm3.
  rewrite (K2 a Ha ltac:(lia)). apply Hm1; [exact Ha | lia]. }
unfold w6bb_J_R. rewrite (c1b_model b r HP). cbn [fst snd]. fold kd j t cur.
split; [exact J22|]. split; [exact J15|].
split; [exact J13|].
split; [exact J6|].
rewrite (c1b_ent_bytes (Z.testbit kd 7) j Hj). fold l.
assert (EA : forall a l1 l2, garr8 rsegs (mrestrict (w_H W) mem5) a l1 ->
  garr8 rsegs (mrestrict (w_H W) mem5) (a + Z.of_nat (length l1)) l2 -> garr8 rsegs (mrestrict (w_H W) mem5) a (l1 ++ l2))
  by (intros a l1 l2 G1' G2'; apply (proj2 (garr8_app rsegs _ _ _ _)); split; assumption).
apply EA; [exact (rm_bytes_of_val rsegs (w_H W) mem5 (F + 0x210) 4%nat 8 V0)|].
rewrite length_map, length_le32. replace (F + 0x210 + Z.of_nat 4) with (F + 0x214) by lia.
apply EA; [exact (rm_bytes_of_val rsegs (w_H W) mem5 (F + 0x214) 4%nat _ V4)|].
rewrite length_map, length_le32. replace (F + 0x214 + Z.of_nat 4) with (F + 0x218) by lia.
apply EA.
{ intros q Hq. rewrite length_map in Hq.
  assert (Hq' : 0 <= Z.of_nat q < l) by (unfold l, c1b_len; lia).
  apply (rm_aview_val1 rsegs). rewrite K5 by lia.
  rewrite (Heff4 (Z.of_nat q) Hq').
  specialize (Hb3 (Z.of_nat q) ltac:(lia)). rewrite Nat2Z.id in Hb3. exact Hb3. }
rewrite length_map. replace (F + 0x218 + Z.of_nat (length (c1b_v j))) with (F + 0x218 + l) by (unfold l, c1b_len; lia).
apply EA.
{ apply c1b_garr8_3;
  [ exact Vt0 | replace (F + 0x218 + l + 1) with (F + 0x219 + l) by lia; exact Vt1
  | replace (F + 0x218 + l + 2) with (F + 0x21a + l) by lia; exact Vt2 | lia | destruct (Z.testbit kd 7); lia | lia ]. }
cbn [length]. apply garr8_zeros. intros a Ha. rewrite Z2Nat.id in Ha by lia.
rewrite (mbyte_of_aview rsegs (w_H W) (w_H W) memc mem5).
- replace a with (F + 0x210 + (a - (F + 0x210))) by lia. apply Hez. lia.
- rewrite (K5 a ltac:(lia) ltac:(lia) ltac:(lia)). apply KM4; lia.
Qed.
End d.
End b.
