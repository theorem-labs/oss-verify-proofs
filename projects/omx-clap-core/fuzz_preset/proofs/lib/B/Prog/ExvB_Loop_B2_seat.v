(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX or memnorm: EXV_HYP has neither field since b29a52d6b76b / 379ec9e4a7d5. *)
(* Theorem Labs, 2026-10: fuzz_preset, image B, ex_value, segment CL piece B2 (the separator, after the nested
   ex_value: B 0x83ca0 = exv_pc 0x774 .. the back edge B 0x83d28, the closer B 0x83ef0-0x83f20, the exit B 0x83d6c):
   the SYMBOLIC STATES the piece runs the table engine from after its ex_ws call (B 0x83ca8 = exv_pc 0x77c), their
   seat lemmas (st_ok / sh_ok from EXB and the spills), and the frame geometry of a cut. Rule 24: proves no function
   (kind: segment lemma).
   Atoms: registers 0-31 (sr_atoms; s6 = shadow_addr (q + 8) and s7 = q + 8 as the cut holds them), 32 p (in->p
   after ex_ws), 33 the byte at p, 34 in->end, 35 the closer (64(s1)), 36 i (136(s1)), 37 56 i (112(s1)), 38 8 i
   (128(s1)). Each arm of the three branches (p >= end at B 0x83cc4, byte = ',' at B 0x83ce8, byte = closer at
   B 0x83f00) is fixed by a condition fact, so each arm is ONE run to its cut.
   Numerals: 9, 18, 19, 22, 23, 25 (WORD: register numbers s1, s2, s3, s6, s7, s9); 8, 64, 112, 120, 128, 136, 144,
   152, 16, 40 (LENGTH: B's spill slots, ExvB_Stmt.v CUT_CL, the cursor's fields / struct ex); 44 (WORD: ASCII ',');
   93, 125 (WORD: ASCII closers); 56 (LENGTH: pj node size, the 112(s1) stride); 3, 5 (WORD: shadow shift, alignment
   exponents); 288, 304, 320, 128, 4096, 2 ^ 30, 2 ^ 40, 2 ^ 46, 2 ^ 47, 2 ^ 64, 0x7fff8000 (LENGTH / DERIVED: frame
   sizes, address-space bounds, SHADOW_OFF); 0x77c (DERIVED: B 0x83ca8 minus B's ex_value entry). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_Loop_kit ExvB_Loop_Stmt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Open_kt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Loop_exw.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.

(* ---- the pcs (DERIVED offsets of ex_value's entry) ---- *)
Definition B2_LS : Z := exv_pc 0x774.   (* B 0x83ca0, the LS cut: mv a0, s3; jal ex_ws *)
Definition B2_PC : Z := exv_pc 0x77c.   (* B 0x83ca8, ex_ws's return site *)
Definition B2_CL : Z := exv_pc 0x534.   (* B 0x83a60, the loop head *)
Definition B2_CC : Z := exv_pc 0x9f8.   (* B 0x83f24, the close *)
Definition B2_CX : Z := exv_pc 0xa7c.   (* B 0x83fa8, the exit *)
Definition B2_SB : Z := 0x7fff8000.     (* SHADOW_OFF *)

(* ---- the symbolic states at B 0x83ca8 ---- *)
Definition b2_shx (e : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL e (SLit 3)) (SOff 25 0).
Definition B2_BX : sv := SOff 25 0.
Definition b2_regs : list sv := sr_set (sr_set sr_atoms 22%bv (b2_shx (SOff 19 8))) 23%bv (SOff 19 8).
Definition b2_R0 : YP09.region := YP09.mkRegion (Some 9%nat) 64 152 112 144
  [YP09.mkChunk 64 (CVal 8 (SOff 35 0)); YP09.mkChunk 112 (CVal 8 (SOff 37 0)); YP09.mkChunk 120 (CVal 8 (SOff 18 0));
   YP09.mkChunk 128 (CVal 8 (SOff 38 0)); YP09.mkChunk 136 (CVal 8 (SOff 36 0));
   YP09.mkChunk 144 (CVal 8 (b2_shx (SOff 19 0)))].
Definition b2_R1 : YP09.region := YP09.mkRegion (Some 19%nat) 0 16 0 8
  [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0))].
Definition b2_R2 : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition b2_factsB : list (nat * afact) :=
  [ (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 320) 5); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF B2_SB B2_SB 0);
    (32%nat, mkAF 4096 (2 ^ 47 - 2) 0); (34%nat, mkAF 4096 (2 ^ 47 - 1) 0); (35%nat, mkAF 93 125 0);
    (36%nat, mkAF 0 (2 ^ 30) 0); (37%nat, mkAF 0 (2 ^ 40) 0); (38%nat, mkAF 0 (2 ^ 40) 0) ].
Definition b2_factsA : list (nat * afact) := b2_factsB ++ [(33%nat, mkAF 0 255 0)].
Definition ss_b2 (rs : smem) (fa : list (nat * afact)) (cs : list acond) : sstate :=
  mkSS B2_PC b2_regs rs None (mkFacts fa cs []).
Definition b2_SHA : list shent := [mkSHE 19 0 40; mkSHE 32 0 1].
Definition b2_SHB : list shent := [mkSHE 19 0 40].
(* the arms' conditions *)
Definition b2_cGE : acond := mkAC BC_GEU (SOff 32 0) (SOff 34 0).
Definition b2_cLT : acond := mkAC BC_LTU (SOff 32 0) (SOff 34 0).
Definition b2_cEQ44 : acond := mkAC BC_EQ (SOff 33 0) (SLit 44).
Definition b2_cNE44 : acond := mkAC BC_NE (SOff 33 0) (SLit 44).
Definition b2_cEQC : acond := mkAC BC_EQ (SOff 33 0) (SOff 35 0).
Definition b2_cNEC : acond := mkAC BC_NE (SOff 33 0) (SOff 35 0).
(* the environment: the registers, then atoms 32 .. 38 *)
Definition b2_env (regs : bvmap 5 word) (p c0 e cl i : Z) : env :=
  Ereg regs (map (Z_to_bv 64) [p; c0; e; cl; i; 56 * i; 8 * i]).
(* the registers every arm keeps as atoms *)
Definition b2_keep : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 21; 25; 26; 27]%bv.

Lemma b2_env_reg : forall regs p c0 e cl i n (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (b2_env regs p c0 e cl i) n = getr regs r.
Proof. intros regs p c0 e cl i n r H. unfold b2_env. exact (ew_Ereg_nat regs _ n r H). Qed.
Lemma b2_env_x : forall regs p c0 e cl i,
  ew (b2_env regs p c0 e cl i) 32 = Z_to_bv 64 p /\ ew (b2_env regs p c0 e cl i) 33 = Z_to_bv 64 c0 /\
  ew (b2_env regs p c0 e cl i) 34 = Z_to_bv 64 e /\ ew (b2_env regs p c0 e cl i) 35 = Z_to_bv 64 cl /\
  ew (b2_env regs p c0 e cl i) 36 = Z_to_bv 64 i /\ ew (b2_env regs p c0 e cl i) 37 = Z_to_bv 64 (56 * i) /\
  ew (b2_env regs p c0 e cl i) 38 = Z_to_bv 64 (8 * i).
Proof.
intros regs p c0 e cl i. unfold b2_env.
refine (conj (ew_Ereg_extra regs _ 0) (conj (ew_Ereg_extra regs _ 1) (conj (ew_Ereg_extra regs _ 2)
  (conj (ew_Ereg_extra regs _ 3) (conj (ew_Ereg_extra regs _ 4) (conj (ew_Ereg_extra regs _ 5)
  (ew_Ereg_extra regs _ 6))))))).
Qed.

(* the shadow address q + c as the code computes it (`srli 3; add s9`) *)
Lemma b2_denot_shx : forall E c v sb, ew E 19 = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 sb ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (b2_shx (SOff 19 c)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E c v sb Hn Hm Hv Hc Hvc Hsb. unfold b2_shx.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 19 c) (SLit 3)) (SOff 25 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by lia. rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma b2_zmaxl_in : forall x l, In x l -> x <= zmaxl l.
Proof.
intros x l. induction l as [|y l IH]; intros H; [destruct H|]. cbn [zmaxl fold_right].
destruct H as [<-|H]; [lia|]. specialize (IH H). fold (zmaxl l). lia.
Qed.

(* ex_value's stack need covers its frame and ex_ws's *)
Lemma b2_stk_ge : forall n, 320 <= STK_ex_value (PI := prh_img_B) n.
Proof.
intros n. unfold STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304.
assert (H : STK_ex_ws <= zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws])
  by (apply b2_zmaxl_in; cbn [In]; tauto).
assert (H16 : @STK_ex_ws prh_img_B = 16) by reflexivity.
lia.
Qed.

Section s. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.

(* the geometry of a cut *)
Lemma b2_geom : forall (fx : YK11.FPState) E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  alloc_ceiling + exv_STK E <= exv_sp E /\ exv_sp E + e_d E <= 2 ^ 47 /\ exv_sp E mod 16 = 0 /\
  exv_sp E <= e_q E /\ e_q E mod 8 = 0 /\ e_q E + 40 <= exv_sp E + e_d E /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\
  exv_sp E - 304 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0 /\ 320 <= exv_STK E /\
  4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
  (forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a) /\
  ARx lyc Sc Hpc Wc memc mdc.
Proof.
intros fx E lyc Sc Hpc Wc regs memc mdc k pos HP HB.
pose proof (eh_laws B ARx SK HYP) as LAWS.
unfold EXV_PRE in HP. cbv zeta in HP. unfold EXB in HB. cbv zeta in HB.
destruct HP as (HFN & _ & _ & _ & _ & _ & PQ8 & _ & PSPQ & PQD & PWIN & _).
destruct HFN as ((_ & _ & _ & _ & _ & Hastk0 & _) & _).
destruct Hastk0 as (Al0 & _).
destruct PWIN as (Hd0 & Hd16 & _).
destruct HB as (HJ & _).
pose proof HJ as (JAR & _ & _ & _ & _ & JFRAMES & _ & _ & _ & _ & _ & _ & _ & JPRES & JSTK & _).
destruct JSTK as (A1 & A2 & A3 & A4 & A5 & A6 & _).
pose proof (b2_stk_ge (e_n E)) as HSTK.
pose proof (exv_s1_le E) as ((S1a & S1b) & S1c).
pose proof asan_consts as (C1 & _).
assert (Hin1 : In (1, pos) (frames Sc)) by (rewrite JFRAMES; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos JAR Hin1) as (F1 & F2 & _).
change (fs_frame_bytes 1) with 128 in F2.
assert (S1d : exv_sp E - 304 <= exv_s1 E).
{ unfold exv_s1. rewrite exv_land32. unfold exv_sp. lia. }
unfold exv_STK in *. unfold exv_sp in *.
repeat (split; [lia|]). split; [intros a Ha; apply JPRES; lia | exact JAR].
Qed.

(* the seat for an arm with p < end (the byte at p read) *)
Lemma b2_seatA : forall (fx : YK11.FPState) E ly2 S2 Hp2 (W2 : world rsegs) (regs2 regs0 : bvmap 5 word) mem2 md2 k pos
    (c : Z) (i : nat) (vv ip : Z) (Ex : env) (cs : list acond),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos ->
  (forall r : bv 5, r <> 24%bv -> getr regs2 r = getr regs0 r) ->
  getr regs2 22 = w64 (shadow_addr (e_q E + 8)) -> getr regs2 23 = w64 (e_q E + 8) ->
  (c = 91 \/ c = 123) -> 0 <= ip < exv_len E -> Z.of_nat i <= exv_len E ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + ip) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E + 8) 8 (e_x0 E + exv_len E) ->
  exv_spills E W2 mem2 ly2 pos c vv i ->
  Ex = b2_env regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + exv_len E)
      (if c =? 123 then 125 else 93) (Z.of_nat i) ->
  conds_ok Ex cs ->
  st_ok rsegs Ex (ss_b2 [b2_R0; b2_R1; b2_R2] b2_factsA cs)
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 B2_PC) mem2 (YK11.seg_rom rsegs))) /\
  sh_ok rsegs B2_BX b2_SHA Ex (mrestrict (w_H W2) mem2).
Proof.
intros fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex cs HP HB HAG H22 H23 Hc Hip Hi Vq Ve HSP HEx HCS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (b2_geom fx E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GPRES & GAR).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PLEN & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _ & _ & _
  & HSRC & _ & _ & _ & HQR & _).
destruct HSRC as (GT & Hx4 & Hxc & Hxam & Hxra & _).
destruct HSP as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104
  & S96 & S120 & S144).
unfold exv_len in *.
assert (Vc : val_mem rsegs (mrestrict (w_H W2) mem2) (e_x0 E + ip + 0) 1 (nth (Z.to_nat ip) (e_x E) 0) /\
  0 <= nth (Z.to_nat ip) (e_x E) 0 < 256).
{ destruct (GT (Z.to_nat ip) ltac:(lia)) as [V R].
  replace (e_x0 E + ip + 0) with (e_x0 E + Z.of_nat (Z.to_nat ip)) by lia. auto. }
destruct Vc as [Vc Hc8].
pose proof (b2_env_x regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + Z.of_nat (length (e_x E)))
  (if c =? 123 then 125 else 93) (Z.of_nat i)) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
rewrite <- HEx in E32, E33, E34, E35, E36, E37, E38.
assert (E9 : ew Ex 9 = Z_to_bv 64 (exv_s1 E)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 9 9%bv eq_refl), (HAG 9%bv ltac:(discriminate)). exact R9. }
assert (E19 : ew Ex 19 = Z_to_bv 64 (e_q E)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 19 19%bv eq_refl), (HAG 19%bv ltac:(discriminate)). exact R19. }
assert (E25 : ew Ex 25 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 25 25%bv eq_refl), (HAG 25%bv ltac:(discriminate)). exact R25. }
assert (E18 : ew Ex 18 = Z_to_bv 64 (frame_addr ly2 1 pos)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 18 18%bv eq_refl), (HAG 18%bv ltac:(discriminate)). exact R18. }
assert (Hcl : 93 <= (if c =? 123 then 125 else 93) <= 125) by (destruct (c =? 123); lia).
assert (U9 : bv_unsigned (ew Ex 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ex 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew Ex 18) = frame_addr ly2 1 pos) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew Ex 32) = e_x0 E + ip) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew Ex 33) = nth (Z.to_nat ip) (e_x E) 0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew Ex 34) = e_x0 E + Z.of_nat (length (e_x E))) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew Ex 35) = (if c =? 123 then 125 else 93)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew Ex 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew Ex 37) = 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Ex 38) = 8 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_b2. apply exw_st_ok_full.
  + unfold b2_regs. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HEx; apply regs_ok_Ereg | |] | |];
      try (intros X; discriminate X).
    * rewrite (b2_denot_shx Ex 8 (e_q E) SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia).
      rewrite H22. unfold shadow_addr. reflexivity.
    * cbn [sv_denot]. rewrite U19. exact H23.
  + vm_compute. reflexivity.
  + unfold b2_R0, b2_R1, b2_R2. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply GPRES; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 64 8 (SOff 35 0) (if c =? 123 then 125 else 93));
           [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | cbn; lia | zside | exact S64].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 112 8 (SOff 37 0) (56 * Z.of_nat i));
           [cbn [sv_denot]; rewrite U37, Z.add_0_r; reflexivity | cbn; lia | zside | exact S112].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 120 8 (SOff 18 0) (frame_addr ly2 1 pos));
           [cbn [sv_denot]; rewrite U18, Z.add_0_r; reflexivity | cbn; lia | zside | exact S120].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 128 8 (SOff 38 0) (8 * Z.of_nat i));
           [cbn [sv_denot]; rewrite U38, Z.add_0_r; reflexivity | cbn; lia | zside | exact S128].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 136 8 (SOff 36 0) (Z.of_nat i));
           [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | cbn; lia | zside | exact S136].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 144 8 (b2_shx (SOff 19 0)) (shadow_addr (e_q E)));
           [rewrite (b2_denot_shx Ex 0 (e_q E) SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia);
            unfold shadow_addr; rewrite Z.add_0_r; reflexivity
           | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144].
    * rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply GPRES; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs Ex _ (e_q E) 0 8 (SOff 32 0) (e_x0 E + ip));
           [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vq].
      -- apply (chunk_ok_val rsegs Ex _ (e_q E) 8 8 (SOff 34 0) (e_x0 E + Z.of_nat (length (e_x E))));
           [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve].
    * rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (chunk_ok_val rsegs Ex _ (e_x0 E + ip) 0 1 (SOff 33 0) (nth (Z.to_nat ip) (e_x E) 0));
        [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | exact Vc].
  + apply pairwise_disjoint_of_extents. unfold b2_R0, b2_R1, b2_R2. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact HCS | exact I]].
    cbn [f_atoms atoms_ok b2_factsA b2_factsB app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U25, U32, U34, U35, U36, U37, U38, U33. unfold B2_SB, SHADOW_OFF.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia.
- assert (HBx : U Ex B2_BX = SHADOW_OFF)
    by (unfold B2_BX; rewrite (U_atom Ex 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
  unfold b2_SHA. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range rsegs (w_H W2) mem2 Ex B2_BX 19 (e_q E) 40 (e_q E) 0 40 HQR HBx);
      [rewrite (U_atom Ex 19 (e_q E) E19) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold SHADOW_OFF. lia.
  + apply (shent_ok_of_range rsegs (w_H W2) mem2 Ex B2_BX 32 (e_x0 E) (Z.of_nat (length (e_x E))) (e_x0 E + ip) 0 1
      Hxra HBx); [rewrite (U_atom Ex 32 (e_x0 E + ip) E32) by lia; reflexivity | lia | lia |].
    intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hxam. unfold SHADOW_OFF. lia.
Qed.

(* the seat for the arm p = end (no byte read) *)
Lemma b2_seatB : forall (fx : YK11.FPState) E ly2 S2 Hp2 (W2 : world rsegs) (regs2 regs0 : bvmap 5 word) mem2 md2 k pos
    (c : Z) (i : nat) (vv ip : Z) (Ex : env) (cs : list acond),
  EXV_PRE B ARx E -> EXB (fx := fx) B ARx SK E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos ->
  (forall r : bv 5, r <> 24%bv -> getr regs2 r = getr regs0 r) ->
  getr regs2 22 = w64 (shadow_addr (e_q E + 8)) -> getr regs2 23 = w64 (e_q E + 8) ->
  (c = 91 \/ c = 123) -> 0 <= ip <= exv_len E -> Z.of_nat i <= exv_len E ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E) 8 (e_x0 E + ip) ->
  val_mem rsegs (mrestrict (w_H W2) mem2) (e_q E + 8) 8 (e_x0 E + exv_len E) ->
  exv_spills E W2 mem2 ly2 pos c vv i ->
  Ex = b2_env regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + exv_len E)
      (if c =? 123 then 125 else 93) (Z.of_nat i) ->
  conds_ok Ex cs ->
  st_ok rsegs Ex (ss_b2 [b2_R0; b2_R1] b2_factsB cs)
    (restrict (w_H W2) (@YK11.mkst fx regs2 (Z_to_bv 64 B2_PC) mem2 (YK11.seg_rom rsegs))) /\
  sh_ok rsegs B2_BX b2_SHB Ex (mrestrict (w_H W2) mem2).
Proof.
intros fx E ly2 S2 Hp2 W2 regs2 regs0 mem2 md2 k pos c i vv ip Ex cs HP HB HAG H22 H23 Hc Hip Hi Vq Ve HSP HEx HCS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (b2_geom fx E ly2 S2 Hp2 W2 regs0 mem2 md2 k pos HP HB)
  as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & GPRES & GAR).
pose proof HP as HP0. unfold EXV_PRE in HP0. cbv zeta in HP0.
destruct HP0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PLEN & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & _ & _ & _
  & HSRC & _ & _ & _ & HQR & _).
destruct HSRC as (GT & Hx4 & Hxc & Hxam & Hxra & _).
destruct HSP as (S152 & S88 & S56 & S48 & S40 & S80 & S24 & S16 & S72 & S8 & S32 & S136 & S112 & S128 & S64 & S104
  & S96 & S120 & S144).
unfold exv_len in *.
pose proof (b2_env_x regs2 (e_x0 E + ip) (nth (Z.to_nat ip) (e_x E) 0) (e_x0 E + Z.of_nat (length (e_x E)))
  (if c =? 123 then 125 else 93) (Z.of_nat i)) as (E32 & E33 & E34 & E35 & E36 & E37 & E38).
rewrite <- HEx in E32, E33, E34, E35, E36, E37, E38.
assert (E9 : ew Ex 9 = Z_to_bv 64 (exv_s1 E)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 9 9%bv eq_refl), (HAG 9%bv ltac:(discriminate)). exact R9. }
assert (E19 : ew Ex 19 = Z_to_bv 64 (e_q E)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 19 19%bv eq_refl), (HAG 19%bv ltac:(discriminate)). exact R19. }
assert (E25 : ew Ex 25 = Z_to_bv 64 SHADOW_OFF).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 25 25%bv eq_refl), (HAG 25%bv ltac:(discriminate)). exact R25. }
assert (E18 : ew Ex 18 = Z_to_bv 64 (frame_addr ly2 1 pos)).
{ rewrite HEx, (b2_env_reg _ _ _ _ _ _ 18 18%bv eq_refl), (HAG 18%bv ltac:(discriminate)). exact R18. }
assert (Hcl : 93 <= (if c =? 123 then 125 else 93) <= 125) by (destruct (c =? 123); lia).
assert (U9 : bv_unsigned (ew Ex 9) = exv_s1 E) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew Ex 19) = e_q E) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew Ex 25) = SHADOW_OFF) by (rewrite E25; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U18 : bv_unsigned (ew Ex 18) = frame_addr ly2 1 pos) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew Ex 32) = e_x0 E + ip) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew Ex 34) = e_x0 E + Z.of_nat (length (e_x E))) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew Ex 35) = (if c =? 123 then 125 else 93)) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew Ex 36) = Z.of_nat i) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew Ex 37) = 56 * Z.of_nat i) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew Ex 38) = 8 * Z.of_nat i) by (rewrite E38; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold ss_b2. apply exw_st_ok_full.
  + unfold b2_regs. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HEx; apply regs_ok_Ereg | |] | |];
      try (intros X; discriminate X).
    * rewrite (b2_denot_shx Ex 8 (e_q E) SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia).
      rewrite H22. unfold shadow_addr. reflexivity.
    * cbn [sv_denot]. rewrite U19. exact H23.
  + vm_compute. reflexivity.
  + unfold b2_R0, b2_R1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply GPRES; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 64 8 (SOff 35 0) (if c =? 123 then 125 else 93));
           [cbn [sv_denot]; rewrite U35, Z.add_0_r; reflexivity | cbn; lia | zside | exact S64].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 112 8 (SOff 37 0) (56 * Z.of_nat i));
           [cbn [sv_denot]; rewrite U37, Z.add_0_r; reflexivity | cbn; lia | zside | exact S112].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 120 8 (SOff 18 0) (frame_addr ly2 1 pos));
           [cbn [sv_denot]; rewrite U18, Z.add_0_r; reflexivity | cbn; lia | zside | exact S120].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 128 8 (SOff 38 0) (8 * Z.of_nat i));
           [cbn [sv_denot]; rewrite U38, Z.add_0_r; reflexivity | cbn; lia | zside | exact S128].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 136 8 (SOff 36 0) (Z.of_nat i));
           [cbn [sv_denot]; rewrite U36, Z.add_0_r; reflexivity | cbn; lia | zside | exact S136].
      -- apply (chunk_ok_val rsegs Ex _ (exv_s1 E) 144 8 (b2_shx (SOff 19 0)) (shadow_addr (e_q E)));
           [rewrite (b2_denot_shx Ex 0 (e_q E) SHADOW_OFF E19 E25) by (unfold SHADOW_OFF; lia);
            unfold shadow_addr; rewrite Z.add_0_r; reflexivity
           | unfold shadow_addr, SHADOW_OFF; cbn; lia | zside | exact S144].
    * rewrite U19. split; [lia|]. split; [lia|].
      split; [intros o Ho; apply (apresent_writable rsegs); apply GPRES; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (chunk_ok_val rsegs Ex _ (e_q E) 0 8 (SOff 32 0) (e_x0 E + ip));
           [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vq].
      -- apply (chunk_ok_val rsegs Ex _ (e_q E) 8 8 (SOff 34 0) (e_x0 E + Z.of_nat (length (e_x E))));
           [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve].
  + apply pairwise_disjoint_of_extents. unfold b2_R0, b2_R1. cbn [map]. unfold extent_of_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  + split; [|split; [exact HCS | exact I]].
    cbn [f_atoms atoms_ok b2_factsB]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U25, U32, U34, U35, U36, U37, U38. unfold B2_SB, SHADOW_OFF.
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia.
- assert (HBx : U Ex B2_BX = SHADOW_OFF)
    by (unfold B2_BX; rewrite (U_atom Ex 25 SHADOW_OFF E25) by (unfold SHADOW_OFF; lia); reflexivity).
  unfold b2_SHB. constructor; [|constructor].
  apply (shent_ok_of_range rsegs (w_H W2) mem2 Ex B2_BX 19 (e_q E) 40 (e_q E) 0 40 HQR HBx);
    [rewrite (U_atom Ex 19 (e_q E) E19) by lia; reflexivity | lia | lia |].
  intros x Hx. unfold SHADOW_OFF. lia.
Qed.
End s.
