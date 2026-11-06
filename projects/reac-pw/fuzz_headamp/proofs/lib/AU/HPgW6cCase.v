(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the case statements of the walk piece W6c of
   LLVMFuzzerTestOneInput (0x80c40), ent_build's cases 6, 7 and 8 (pod.h:340-366), each from its switch entry to the
   join J 0x82618, and the two lemmas that make a case of its head and its tail. Proves no function (kind: segment
   lemma).

   A CASE (w6c_case_stmt c) runs from w6c_pc c with the state w6c_in (HPgSeg.hsu_L_D's registers s1 = R, s11 = K,
   s2 = cur, a7 = cur - 1, t1 = |r| + 1, s4 = |r|, a6 = 1, sp = R, gp, tp; the cells R+0x10, R+0x118, R+0x130, R+0x138,
   R+0x148; e62 = 104 zero bytes in scope; the input r at cur; ent_build.t and ent_build.t.11 addressable; the image's
   read-only bytes) to J, where the post is HPgCaseBJ.cj_J_R of the turn's input b :: r with the registers w6c_clob
   and the bytes cj_wr R F [] (the callees' stack and e62).
   A HEAD runs from w6c_pc c to the tail's entry: for cases 6 and 7 the take block (W6C_T6, W6C_T7), for case 8 the
   fill block (W6C_F8). It reads the input, stores e62.type and leaves the type, the size and what is left
   (w6c_hpostT / w6c_hpostF, in the model's terms: HPgW6cEng.w6c_ent). w6c_case_of_headT / w6c_case_of_headF chain
   a head with HPgW6cTake.w6c_take / HPgW6cFill.w6c_fill and read e62's 104 bytes at J (w6c_e62_mem). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ
  HPgW6cEng HPgW6cFill HPgW6cTake.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the registers a case may change (none of HPgCaseBJ.cj_kregs) *)
Definition w6c_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 23; 26; 28; 29; 30; 31]%bv.
Lemma w6c_clob_ok : cj_clob_ok w6c_clob = true.
Proof. vm_compute. reflexivity. Qed.
Lemma w6c_ws_ok : cj_ws_ok [] = true.
Proof. reflexivity. Qed.
Lemma w6c_take_clob_sub : forall r, In r w6c_take_clob -> In r w6c_clob.
Proof. intros r H. cbv [In w6c_take_clob w6c_clob] in H |- *. tauto. Qed.
Lemma w6c_fill_clob_sub : forall r, In r w6c_fill_clob -> In r w6c_clob.
Proof. intros r H. cbv [In w6c_fill_clob w6c_clob] in H |- *. tauto. Qed.
Lemma w6c_23_take : ~ In (23%bv : bv 5) w6c_take_clob.
Proof. cbv [In w6c_take_clob]. intros X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. Qed.
Lemma w6c_23_fill : ~ In (23%bv : bv 5) w6c_fill_clob.
Proof. cbv [In w6c_fill_clob]. intros X. repeat (destruct X as [X|X]; [discriminate X|]). exact X. Qed.

(* the bytes a head writes: e62.type *)
Definition w6c_wrH (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x214.

(* what is left after a take head, in the model: the type, the size, the input q the take block reads *)
Definition w6c_tk_model (c : Z) (r : list byte) (ty sz : Z) (q : list byte) : Prop :=
0 <= sz <= 11 /\ 0 <= ty < 2 ^ 32 /\ is_rest q r /\
w6c_ent c r = (Ent ty sz (firstn (Z.to_nat sz) q ++ zeros (Z.to_nat sz - length (firstn (Z.to_nat sz) q))),
               skipn (Z.to_nat sz) q).
(* what is left after the fill head of case 8, in the model *)
Definition w6c_fl_model (r : list byte) (ty sz : Z) (q : list byte) : Prop :=
0 <= sz <= 3 /\ 0 <= ty < 2 ^ 32 /\ is_rest q r /\ w6c_ent 8 r = (Ent ty sz (zeros (Z.to_nat sz)), q).

(* e62's 104 bytes from its type, its size, its body p and the zero tail *)
Lemma w6c_e62_mem : forall (H : word -> bool) mem a ty sz (p : list byte),
  val_mem rsegs (mrestrict H mem) a 4 ty -> val_mem rsegs (mrestrict H mem) (a + 4) 4 sz ->
  hm_bytes rsegs H mem (a + 8) p ->
  (forall i, 0 <= i < 96 - Z.of_nat (length p) -> aview rsegs H mem (a + 8 + Z.of_nat (length p) + i) = Some 0) ->
  hm_bytes rsegs H mem a (le32 ty ++ le32 sz ++ p ++ zeros (96 - length p)).
Proof.
intros H mem a ty sz p V0 V4 Hp Hz.
unfold le32. apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V0|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4.
apply hm_bytes_app. split; [apply hm_bytes_of_val; exact V4|].
rewrite length_Z_to_le_bytes. change (Z.of_nat 4) with 4. replace (a + 4 + 4) with (a + 8) by lia.
apply hm_bytes_app. split; [exact Hp|].
apply (proj2 (hm_bytes_aview rsegs H mem _ (zeros (96 - length p)))). intros i Hi.
unfold zeros in *. rewrite repeat_length in Hi. unfold NUL. rewrite nth_repeat.
rewrite (Hz (Z.of_nat i) ltac:(lia)). reflexivity.
Qed.

(* the input after j bytes *)
Lemma w6c_bytes_skip : forall (H : word -> bool) mem cur (r : list byte) j, hm_bytes rsegs H mem cur r ->
  (j <= length r)%nat -> hm_bytes rsegs H mem (cur + Z.of_nat j) (skipn j r).
Proof.
intros H mem cur r j Hr Hj. rewrite <- (firstn_skipn j r) in Hr. apply hm_bytes_app in Hr as [_ Hr].
rewrite length_firstn, Nat.min_l in Hr by exact Hj. exact Hr.
Qed.


Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.

(* ===================== the state at a case entry ===================== *)
Definition w6c_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F cur pp : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 27 = w64 SHADOW_OFF /\
getr regs 18 = w64 cur /\ getr regs 17 = w64 (cur - 1) /\
getr regs 6 = w64 (Z.of_nat (length r) + 1) /\ getr regs 20 = w64 (Z.of_nat (length r)) /\ getr regs 16 = w64 1 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x10) 8 0x15555556 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x118) 8 (F + 0x218) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x138) 8 (pp + 0x4000) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x148) 8 pp /\
4096 <= pp /\ pp + Layout.PP_SIZE <= alloc_ceiling /\
(forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x210 + i) = Some (Z_to_bv 8 0)) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 /\
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 /\
hm_bytes rsegs (w_H W) memc cur r /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) cur (Z.of_nat (length r))) /\
amem_range cur (Z.of_nat (length r)) /\ 2 <= cur /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
   ~ (R - T_SEG_STK <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_TB6 16 /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6C_TB8 16 /\
rom_view rsegs W memc.

(* ===================== a case ===================== *)
Definition w6c_case_stmt (c : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur pp : Z)
  (b : byte) (r : list byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
bv_unsigned b mod 10 = c ->
w6c_in W memc regs R F cur pp r ->
SRr rsegs W (cfg_at rsegs (w6c_pc c) regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_J w6c_clob (cj_wr R F [])
   (cj_J_R R F pp cur r (b :: r))).

(* ===================== the heads ===================== *)
Definition w6c_hpostT (c R F cur pp : Z) (r : list byte) (W : world rsegs) :
  world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 => W2 = W /\ exists ty sz q, w6c_tk_model c r ty sz q /\
getr regs2 12 = w64 sz /\ getr regs2 11 = w64 (Z.of_nat (length q)) /\
getr regs2 18 = w64 (cur + Z.of_nat (length r) - Z.of_nat (length q)) /\
getr regs2 20 = w64 (F + 0x210) /\ getr regs2 23 = w64 pp /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x210) 4 ty /\
(forall o, 0 <= o < 1024 -> apresent (w_H W2) mem2 (F + o)).
Definition w6c_hpostF (R F cur pp : Z) (r : list byte) (W : world rsegs) :
  world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 => W2 = W /\ exists ty sz q, w6c_fl_model r ty sz q /\
getr regs2 12 = w64 sz /\ getr regs2 18 = w64 (cur + Z.of_nat (length r) - Z.of_nat (length q)) /\
getr regs2 20 = w64 (Z.of_nat (length q)) /\ getr regs2 23 = w64 pp /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x210) 4 ty /\
(forall o, 0 <= o < 1024 -> apresent (w_H W2) mem2 (F + o)).
Definition w6c_head_stmt (c pc1 : Z)
  (P : Z -> Z -> Z -> Z -> list byte -> world rsegs -> world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop)
  : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur pp : Z)
  (r : list byte),
w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6c_in W memc regs R F cur pp r ->
SRr rsegs W (cfg_at rsegs (w6c_pc c) regs memc mdc)
 (hdu_blk_postE B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc pc1 w6c_clob (w6c_wrH F)
   (P R F cur pp r W)).
Definition w6c_head6_stmt : Prop := w6c_head_stmt 6 W6C_T6 (w6c_hpostT 6).
Definition w6c_head7_stmt : Prop := w6c_head_stmt 7 W6C_T7 (w6c_hpostT 7).
Definition w6c_head8_stmt : Prop := w6c_head_stmt 8 W6C_F8 w6c_hpostF.

(* ===================== a head's engine state at its entry ===================== *)
Lemma w6c_val0 : forall m F o, (forall i, 0 <= i < 104 -> mbyte rsegs m (F + 0x210 + i) = Some (Z_to_bv 8 0)) ->
  0 <= o <= 100 -> val_mem rsegs m (F + 0x210 + o) 4 0.
Proof.
intros m F o Hz Ho k Hk. replace (F + 0x210 + o + Z.of_nat k) with (F + 0x210 + (o + Z.of_nat k)) by lia.
rewrite (Hz (o + Z.of_nat k)) by lia. destruct k as [|[|[|[|k]]]]; try (vm_compute; reflexivity); lia.
Qed.
(* the entry state HPgW6cEng.w6c_ss at pc with m <= 2 input bytes in its region, the bound lo20 .. hi20 of what is
   left and the bound hi17 of the kind byte's address, and the shadow entry over e62's header *)
Lemma w6c_head_entry : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  (R F pos cur pp : Z) (r : list byte) pc (m : nat) lo20 hi20 hi17,
  w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6c_in W memc regs R F cur pp r ->
  0 <= pc -> cur - 1 <= hi17 -> lo20 <= Z.of_nat (length r) <= hi20 -> (m <= length r)%nat -> (m <= 2)%nat ->
  st_ok rsegs (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) (w6c_ss pc m lo20 hi20 hi17)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))) /\
  sh_ok rsegs w6c_Bx w6c_SH (Ereg regs (w6c_extra F (u32_b r 0) (u32_b r 1) pp)) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r pc m lo20 hi20 hi17
  Hctx Hin Hpc H17b H20b Hm1 Hm2.
destruct Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
destruct Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof asan_consts as (Hceil & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _).
unfold T_SEG_STK, ASTACK in *.
assert (HRb : 0x10007fffc000 <= R <= 2 ^ 47 - 0x220) by lia.
assert (HFb : 4096 <= F <= 2 ^ 47 - 1024) by lia.
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
split.
- apply (w6c_entry pc m W regs memc R F cur pp r lo20 hi20 hi17 Hpc H9 H27 H17 H18 H20 H6 H16 HRb HR32 HFb HF32
    ltac:(lia) ltac:(lia) H17b H20b ltac:(unfold Layout.PP_SIZE in Hpp2; lia) ltac:(lia) Hm1 Hm2
    V10 V118 V130 V138 V148).
  + replace (F + 0x210) with (F + 0x210 + 0) by lia. exact (w6c_val0 _ F 0 Hez ltac:(lia)).
  + replace (F + 0x214) with (F + 0x210 + 4) by lia. exact (w6c_val0 _ F 4 Hez ltac:(lia)).
  + intros o Ho. apply HFp. lia.
  + exact Hr.
  + intros a Ha. destruct (Hdis a Ha) as [X Y]. split; [lia | exact Y].
- apply (w6c_shok regs (w_H W) memc F _ _ pp H27 HFb).
  + apply (ra_sub _ _ (F + 0x210) 104); [exact HraE | lia | lia].
  + intros a Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
End d.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis INTRIN : w6c_intrin_law B.
Hypothesis AMEMCPY : aintrin_realizes rsegs B OCpy W6C_CPY.
Hypothesis AMEMSET : aintrin_realizes rsegs B OSet W6C_SET.

(* the block context at a later state of the same journal *)
Lemma w6c_ctx_step : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ly2 S2 W2 mem2 md2,
  w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k ->
  (forall o, 0 <= o < 1024 -> apresent (w_H W2) mem2 (F + o)) ->
  w6c_ctx B STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W2 mem2 md2 R F pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ly2 S2 W2 mem2 md2
  (HJ & H1 & H2 & H3 & H4 & H5 & H6 & HF & H8 & H9 & H10 & H11 & _) HJ2 HP.
pose proof HJ as (_ & Hle & _). pose proof HJ2 as (_ & Hle2 & _).
split; [exact HJ2|]. repeat (split; [assumption|]).
split; [rewrite HF, (cj_frame_addr_le _ _ _ 4 pos Hle), (cj_frame_addr_le _ _ _ 4 pos Hle2); reflexivity|].
repeat (split; [assumption|]). exact HP.
Qed.

(* the facts of the input from cur + j on, at a state that kept every byte outside e62.type *)
Lemma w6c_in_rest : forall (W : world rsegs) memc mem2 R F cur (r : list byte) j,
  hm_bytes rsegs (w_H W) memc cur r ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) ->
  (0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) cur (Z.of_nat (length r))) ->
  amem_range cur (Z.of_nat (length r)) -> 2 <= cur -> 4096 <= F -> F + 1024 <= alloc_ceiling -> in_app F 1024 ->
  (forall a, cur <= a < cur + Z.of_nat (length r) ->
     ~ (R - T_SEG_STK <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) mem2 a = aview rsegs (w_H W) memc a) ->
  (j <= length r)%nat ->
  hm_bytes rsegs (w_H W) mem2 (cur + Z.of_nat j) (skipn j r) /\
  range_addressable (aview rsegs (w_H W) mem2) SHADOW_OFF (cur + Z.of_nat j) (Z.of_nat (length (skipn j r))) /\
  (0 < Z.of_nat (length (skipn j r)) ->
     shadow_hull_vis (aview rsegs (w_H W) mem2) (cur + Z.of_nat j) (Z.of_nat (length (skipn j r)))) /\
  amem_range (cur + Z.of_nat j) (Z.of_nat (length (skipn j r))) /\ 1 <= cur + Z.of_nat j /\
  (forall a, cur + Z.of_nat j <= a < cur + Z.of_nat j + Z.of_nat (length (skipn j r)) ->
     ~ (R - T_SEG_STK <= a < R + 0x198) /\ ~ (F + 0x20 <= a < F + 0x278)).
Proof.
intros W memc mem2 R F cur r j Hr Hra Hhull Ham Hc HF1 HF2 HFapp Hdis KE Hj.
pose proof asan_consts as (Hceil & _).
rewrite length_skipn.
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham; lia).
(* the shadow bytes of the input lie in the shadow band, apart from e62 *)
assert (KS : forall x, 0 <= x < 2 ^ 47 ->
  aview rsegs (w_H W) mem2 (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X.
  pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y.
  unfold kLowMemEnd, kHighMemBeg in X. apply KE; [lia|]. unfold w6c_wrH. lia. }
split.
{ apply (hm_bytes_kept rsegs (w_H W) memc); [exact (w6c_bytes_skip _ _ cur r j Hr Hj)|].
  intros x Hx. rewrite length_skipn in Hx. apply KE; [lia|]. unfold w6c_wrH.
  destruct (Hdis x ltac:(lia)) as [_ X]. lia. }
split.
{ apply (hm_ra_kept rsegs (w_H W) memc); [apply (ra_sub _ _ cur (Z.of_nat (length r))); [exact Hra | lia | lia]|].
  intros x Hx. apply KS. lia. }
split.
{ intros Hn. apply (hm_hull_kept rsegs (w_H W) memc).
  - apply (hm_hull_sub _ cur (Z.of_nat (length r))); [apply Hhull; lia | lia | lia | lia].
  - intros s Hs Hne. pose proof (cj_hull_band (cur + Z.of_nat j) (Z.of_nat (length r - j)) s ltac:(lia) ltac:(lia)
      ltac:(lia) Hs) as X.
    assert (Y : ~ (F + 0x210 <= s < F + 0x214)) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
      unfold kLowMemEnd, kHighMemBeg in X; lia).
    rewrite (KE s ltac:(unfold kLowMemEnd, kHighMemBeg in X; lia) Y). exact Hne. }
split; [unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia|].
split; [lia|].
intros a Ha. apply Hdis. lia.
Qed.

(* e62's zero tail at a case entry, as an aview *)
Lemma w6c_e62_zero : forall (H : word -> bool) mem F i,
  (forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict H mem) (F + 0x210 + i) = Some (Z_to_bv 8 0)) ->
  0 <= i < 104 -> aview rsegs H mem (F + 0x210 + i) = Some 0.
Proof. intros H mem F i Hz Hi. unfold aview. rewrite (Hz i Hi). reflexivity. Qed.

(* ===================== a take case of its head ===================== *)
Lemma w6c_case_of_headT : forall c pc0, (c = 6 /\ pc0 = W6C_T6) \/ (c = 7 /\ pc0 = W6C_T7) ->
  w6c_head_stmt B MT c pc0 (w6c_hpostT c) -> w6c_case_stmt B MT c.
Proof using MTL INTRIN AMEMCPY.
intros c pc0 Hcp HD. unfold w6c_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp b r Hctx Hb Hin.
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof asan_consts as (Hceil & _).
assert (Hpc0 : pc0 = W6C_T6 \/ pc0 = W6C_T7) by (destruct Hcp as [[_ E]|[_ E]]; [left|right]; exact E).
assert (Hcin : In c [6; 7; 8]) by (destruct Hcp as [[E _]|[E _]]; subst c; cbn; tauto).
assert (Ebuild : ent_build (b :: r) = w6c_ent c r).
{ rewrite <- Hb. apply (w6c_build_kind (b :: r) (bv_unsigned b) r); [reflexivity | discriminate | rewrite Hb; exact Hcin]. }
eapply SRr_bind; [exact (HD STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r Hctx Hin)|].
intros W2 c2' _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Kr2 & Hf2 & Hp2 & Hio2 & Hmo2 & KE2 & HR2).
destruct HR2 as (-> & ty & sz & q & HM & R12 & R11 & R18 & R20 & R23 & Vty & HFp2).
destruct HM as (Hsz & Hty & [j Hq] & Hent).
assert (Kg : forall rg : bv 5, In rg [2; 3; 4; 9; 27]%bv -> getr regs2 rg = getr regs rg).
{ intros rg Hrg. apply Kr2.
  - cbv [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [vm_compute; discriminate|]). destruct Hrg.
  - intros X. cbv [In w6c_clob] in Hrg, X.
    repeat (destruct Hrg as [<-|Hrg]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrg. }
(* q is what is left after j' = |r| - |q| bytes *)
set (j' := (length r - length q)%nat).
assert (Eq : q = skipn j' r).
{ subst j'. rewrite Hq, length_skipn. destruct (Nat.le_gt_cases j (length r)) as [L|L].
  - f_equal. lia.
  - rewrite skipn_all2 by lia. rewrite skipn_all2 by lia. reflexivity. }
assert (Ej' : Z.of_nat (length r) - Z.of_nat (length q) = Z.of_nat j').
{ subst j'. rewrite Hq, length_skipn. lia. }
assert (Hj' : (j' <= length r)%nat) by (subst j'; lia).
pose proof (w6c_in_rest W memc mem2 R F cur r j' Hr Hrar Hhr Hamr Hc2 HF1 HF2 HFapp Hdis KE2 Hj')
  as (Hq2 & Hraq & Hhq & Hamq & Hcq & Hdq).
rewrite <- Eq in Hq2, Hraq, Hhq, Hamq, Hdq.
(* the bytes the head kept *)
assert (KV : forall a n v, val_mem rsegs (mrestrict (w_H W) memc) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> 0 <= a + i < 2 ^ 64 /\ ~ w6c_wrH F (a + i)) ->
  val_mem rsegs (mrestrict (w_H W) mem2) a n v).
{ intros a n v V X. apply (w6c_val_kept (w_H W) (w_H W) memc mem2 a n v V). intros i Hi.
  destruct (X i Hi) as (X1 & X2). exact (KE2 (a + i) X1 X2). }
unfold T_SEG_STK, ASTACK in HRc, HSTK, Hdis, Hdq.
pose proof (KV _ _ _ V118 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V118'.
pose proof (KV _ _ _ V130 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V130'.
pose proof (KV _ _ _ V138 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V138'.
assert (KSh : forall x, 0 <= x < 2 ^ 47 ->
  aview rsegs (w_H W) mem2 (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X.
  pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y.
  unfold kLowMemEnd, kHighMemBeg in X. apply KE2; [lia|]. unfold w6c_wrH. lia. }
assert (HraE2 : range_addressable (aview rsegs (w_H W) mem2) SHADOW_OFF (F + 0x210) 104).
{ apply (hm_ra_kept rsegs (w_H W) memc); [exact HraE|]. intros x Hx. apply KSh. lia. }
assert (HhE2 : shadow_hull_vis (aview rsegs (w_H W) mem2) (F + 0x210) 104).
{ apply (hm_hull_kept rsegs (w_H W) memc); [exact HhE|]. intros s Hs Hne.
  pose proof (cj_hull_band (F + 0x210) 104 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as X.
  assert (Y : ~ (F + 0x210 <= s < F + 0x214)) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
    unfold kLowMemEnd, kHighMemBeg in X; lia).
  rewrite (KE2 s ltac:(unfold kLowMemEnd, kHighMemBeg in X; lia) Y). exact Hne. }
pose proof (w6c_ctx_step STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ly2 S2 W mem2 md2 Hctx HJ2 HFp2)
  as Hctx2.
(* the take block *)
eapply SRr_mono.
{ apply (w6c_take B MT MTL INTRIN AMEMCPY pc0 Hpc0 STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W mem2 md2 regs2 R F pos
    pp (cur + Z.of_nat j') sz q Hctx2).
  - rewrite (Kg 2%bv) by (cbv; tauto). exact H2.
  - rewrite (Kg 3%bv) by (cbv; tauto). exact H3.
  - rewrite (Kg 4%bv) by (cbv; tauto). exact H4.
  - rewrite (Kg 9%bv) by (cbv; tauto). exact H9.
  - rewrite (Kg 27%bv) by (cbv; tauto). exact H27.
  - exact R12.
  - exact R11.
  - rewrite R18. unfold w64. f_equal. lia.
  - exact R20.
  - exact Hsz.
  - unfold Layout.PP_SIZE in Hpp2. lia.
  - exact V118'.
  - exact V130'.
  - exact V138'.
  - exact HraE2.
  - exact HhE2.
  - exact Hq2.
  - exact Hraq.
  - exact Hhq.
  - exact Hamq.
  - exact Hcq.
  - unfold T_SEG_STK, ASTACK. exact Hdq. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Kr3 & Hf3 & Hp3 & Hio3 & Hmo3 & KE3 & HR3).
destruct HR3 as (-> & T13 & T6 & T18 & T20 & TVS & TB).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split.
{ intros rg Hr0 Hn. rewrite (Kr3 rg Hr0 (fun X => Hn (w6c_take_clob_sub rg X))). exact (Kr2 rg Hr0 Hn). }
split; [rewrite Hf3; exact Hf2|]. split; [eapply Permutation_trans; [exact Hp3 | exact Hp2]|].
split; [eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3)|].
set (n := Z.of_nat (length (firstn (Z.to_nat sz) q))) in *.
assert (Hn11 : 0 <= n <= 11) by (subst n; rewrite length_firstn; lia).
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R) -> ~ (F + 0x210 <= a < F + 0x218 + n) ->
  aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2. rewrite (KE3 a Ha ltac:(unfold w6c_take_wr, T_SEG_STK, ASTACK; lia)).
  apply KE2; [exact Ha | unfold w6c_wrH; lia]. }
split.
{ intros a Ha Hn. unfold cj_wr in Hn. rewrite (KE3 a Ha).
  - apply KE2; [exact Ha|]. unfold w6c_wrH, HSU_E62 in *. lia.
  - unfold w6c_take_wr, T_SEG_STK, ASTACK, HSU_E62 in *. intros [X|X]; apply Hn; [left; exact X|right; right; lia]. }
(* the join's values *)
unfold cj_J_R. rewrite Ebuild, Hent. cbn [fst snd].
assert (Lq : Z.of_nat (length (firstn (Z.to_nat sz) q)) + Z.of_nat (length (skipn (Z.to_nat sz) q)) =
             Z.of_nat (length q)) by (rewrite length_firstn, length_skipn; lia).
split; [rewrite T13; f_equal; lia|].
split; [exact T6|].
split; [rewrite T18; reflexivity|].
split; [rewrite T20; reflexivity|].
split; [rewrite (Kr3 23%bv ltac:(vm_compute; discriminate) w6c_23_take); exact R23|].
rewrite (w6c_ent_mem_pad ty sz (firstn (Z.to_nat sz) q) ltac:(rewrite length_firstn; lia) ltac:(lia)).
change (hm_bytes rsegs (w_H W) mem3 (F + HSU_E62)
  (le32 ty ++ le32 sz ++ firstn (Z.to_nat sz) q ++ zeros (96 - length (firstn (Z.to_nat sz) q)))).
unfold HSU_E62. apply w6c_e62_mem.
- apply (w6c_val_kept (w_H W) (w_H W) mem2 mem3 _ _ _ Vty). intros i Hi. cbn in Hi.
  apply KE3; [lia|]. unfold w6c_take_wr, T_SEG_STK, ASTACK. lia.
- replace (F + 0x210 + 4) with (F + 0x214) by lia. exact TVS.
- replace (F + 0x210 + 8) with (F + 0x218) by lia. exact TB.
- intros i Hi. fold n in Hi |- *. replace (F + 0x210 + 8 + n + i) with (F + 0x210 + (8 + n + i)) by lia.
  rewrite K3 by lia. apply (w6c_e62_zero _ _ F); [exact Hez | lia].
Qed.

(* ===================== the fill case of its head ===================== *)
Lemma w6c_case_of_headF : w6c_head_stmt B MT 8 W6C_F8 w6c_hpostF -> w6c_case_stmt B MT 8.
Proof using MTL INTRIN AMEMSET.
intros HD. unfold w6c_case_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp b r Hctx Hb Hin.
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof asan_consts as (Hceil & _).
assert (Ebuild : ent_build (b :: r) = w6c_ent 8 r).
{ rewrite <- Hb. apply (w6c_build_kind (b :: r) (bv_unsigned b) r); [reflexivity | discriminate | rewrite Hb; cbn; tauto]. }
eapply SRr_bind; [exact (HD STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r Hctx Hin)|].
intros W2 c2' _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & Kr2 & Hf2 & Hp2 & Hio2 & Hmo2 & KE2 & HR2).
destruct HR2 as (-> & ty & sz & q & HM & R12 & R18 & R20 & R23 & Vty & HFp2).
destruct HM as (Hsz & Hty & [j Hq] & Hent).
assert (Kg : forall rg : bv 5, In rg [2; 3; 4; 9; 27]%bv -> getr regs2 rg = getr regs rg).
{ intros rg Hrg. apply Kr2.
  - cbv [In] in Hrg. repeat (destruct Hrg as [<-|Hrg]; [vm_compute; discriminate|]). destruct Hrg.
  - intros X. cbv [In w6c_clob] in Hrg, X.
    repeat (destruct Hrg as [<-|Hrg]; [repeat (destruct X as [X|X]; [discriminate X|]); exact X|]). destruct Hrg. }
assert (Hql : (length q <= length r)%nat) by (rewrite Hq, length_skipn; lia).
assert (KV : forall a n v, val_mem rsegs (mrestrict (w_H W) memc) a n v ->
  (forall i, 0 <= i < Z.of_nat n -> 0 <= a + i < 2 ^ 64 /\ ~ w6c_wrH F (a + i)) ->
  val_mem rsegs (mrestrict (w_H W) mem2) a n v).
{ intros a n v V X. apply (w6c_val_kept (w_H W) (w_H W) memc mem2 a n v V). intros i Hi.
  destruct (X i Hi) as (X1 & X2). exact (KE2 (a + i) X1 X2). }
unfold T_SEG_STK, ASTACK in HRc, HSTK, Hdis.
pose proof (KV _ _ _ V118 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V118'.
pose proof (KV _ _ _ V130 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V130'.
pose proof (KV _ _ _ V138 ltac:(intros i Hi; cbn in Hi; unfold w6c_wrH; lia)) as V138'.
assert (KSh : forall x, 0 <= x < 2 ^ 47 ->
  aview rsegs (w_H W) mem2 (shadow_of_addr SHADOW_OFF x) = aview rsegs (w_H W) memc (shadow_of_addr SHADOW_OFF x)).
{ intros x Hx. pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X.
  pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y.
  unfold kLowMemEnd, kHighMemBeg in X. apply KE2; [lia|]. unfold w6c_wrH. lia. }
assert (HraE2 : range_addressable (aview rsegs (w_H W) mem2) SHADOW_OFF (F + 0x210) 104).
{ apply (hm_ra_kept rsegs (w_H W) memc); [exact HraE|]. intros x Hx. apply KSh. lia. }
assert (HhE2 : shadow_hull_vis (aview rsegs (w_H W) mem2) (F + 0x210) 104).
{ apply (hm_hull_kept rsegs (w_H W) memc); [exact HhE|]. intros s Hs Hne.
  pose proof (cj_hull_band (F + 0x210) 104 s ltac:(lia) ltac:(lia) ltac:(lia) Hs) as X.
  assert (Y : ~ (F + 0x210 <= s < F + 0x214)) by (unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp;
    unfold kLowMemEnd, kHighMemBeg in X; lia).
  rewrite (KE2 s ltac:(unfold kLowMemEnd, kHighMemBeg in X; lia) Y). exact Hne. }
pose proof (w6c_ctx_step STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ly2 S2 W mem2 md2 Hctx HJ2 HFp2)
  as Hctx2.
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
(* the fill block *)
eapply SRr_mono.
{ apply (w6c_fill B MT MTL INTRIN AMEMSET STK sp0 FP ly S W0 mem0 md0 own k ly2 S2 W mem2 md2 regs2 R F pos pp
    (cur + Z.of_nat (length r) - Z.of_nat (length q)) (Z.of_nat (length q)) sz Hctx2).
  - rewrite (Kg 2%bv) by (cbv; tauto). exact H2.
  - rewrite (Kg 3%bv) by (cbv; tauto). exact H3.
  - rewrite (Kg 4%bv) by (cbv; tauto). exact H4.
  - rewrite (Kg 9%bv) by (cbv; tauto). exact H9.
  - rewrite (Kg 27%bv) by (cbv; tauto). exact H27.
  - exact R12.
  - exact R18.
  - exact R20.
  - exact Hsz.
  - lia.
  - lia.
  - unfold Layout.PP_SIZE in Hpp2. lia.
  - exact V118'.
  - exact V130'.
  - exact V138'.
  - exact HraE2.
  - exact HhE2. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Kr3 & Hf3 & Hp3 & Hio3 & Hmo3 & KE3 & HR3).
destruct HR3 as (-> & T13 & T6 & T18 & T20 & TVS & TB).
exists ly3, S3, regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
split.
{ intros rg Hr0 Hn. rewrite (Kr3 rg Hr0 (fun X => Hn (w6c_fill_clob_sub rg X))). exact (Kr2 rg Hr0 Hn). }
split; [rewrite Hf3; exact Hf2|]. split; [eapply Permutation_trans; [exact Hp3 | exact Hp2]|].
split; [eapply same_io_trans; [exact Hio2 | exact Hio3]|].
split; [exact (mo_le_trans MT MTL _ _ _ _ _ Hmo2 Hmo3)|].
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - 16384 <= a < R) -> ~ (F + 0x210 <= a < F + 0x218 + sz) ->
  aview rsegs (w_H W) mem3 a = aview rsegs (w_H W) memc a).
{ intros a Ha X1 X2. rewrite (KE3 a Ha ltac:(unfold w6c_fill_wr, T_SEG_STK, ASTACK; lia)).
  apply KE2; [exact Ha | unfold w6c_wrH; lia]. }
split.
{ intros a Ha Hn. unfold cj_wr in Hn. rewrite (KE3 a Ha).
  - apply KE2; [exact Ha|]. unfold w6c_wrH, HSU_E62 in *. lia.
  - unfold w6c_fill_wr, T_SEG_STK, ASTACK, HSU_E62 in *. intros [X|X]; apply Hn; [left; exact X|right; right; lia]. }
(* the join's values *)
unfold cj_J_R. rewrite Ebuild, Hent. cbn [fst snd].
split; [rewrite T13; f_equal; lia|].
split; [exact T6|].
split; [rewrite T18; reflexivity|].
split; [rewrite T20; reflexivity|].
split; [rewrite (Kr3 23%bv ltac:(vm_compute; discriminate) w6c_23_fill); exact R23|].
assert (EZ : ent_mem (Ent ty sz (zeros (Z.to_nat sz))) = le32 ty ++ le32 sz ++ [] ++ zeros (96 - length (@nil byte))).
{ unfold ent_mem. cbn [e_type e_size e_body]. rewrite app_nil_l. cbn [length]. rewrite Nat.sub_0_r.
  do 2 f_equal. unfold zeros. rewrite repeat_length, <- repeat_app. f_equal. lia. }
rewrite EZ.
change (hm_bytes rsegs (w_H W) mem3 (F + HSU_E62) (le32 ty ++ le32 sz ++ [] ++ zeros (96 - length (@nil byte)))).
unfold HSU_E62. apply w6c_e62_mem.
- apply (w6c_val_kept (w_H W) (w_H W) mem2 mem3 _ _ _ Vty). intros i Hi. cbn in Hi.
  apply KE3; [lia|]. unfold w6c_fill_wr, T_SEG_STK, ASTACK. lia.
- replace (F + 0x210 + 4) with (F + 0x214) by lia. exact TVS.
- intros i Hi. cbn in Hi. lia.
- intros i Hi. cbn [length Z.of_nat] in Hi |- *. rewrite Z.add_0_r.
  destruct (Z_lt_le_dec i sz) as [Hl|Hl].
  + replace (F + 0x210 + 8 + i) with (F + 0x218 + i) by lia. exact (TB i ltac:(lia)).
  + replace (F + 0x210 + 8 + i) with (F + 0x210 + (8 + i)) by lia.
    rewrite K3 by lia. apply (w6c_e62_zero _ _ F); [exact Hez | lia].
Qed.
End c.
End b.

Print Assumptions w6c_e62_mem.
Print Assumptions w6c_ctx_step.
Print Assumptions w6c_in_rest.
Print Assumptions w6c_case_of_headT.
Print Assumptions w6c_case_of_headF.
