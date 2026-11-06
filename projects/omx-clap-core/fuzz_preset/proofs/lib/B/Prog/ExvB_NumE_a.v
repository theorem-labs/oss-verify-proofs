(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Does not rest on tex_word_specX; memnorm only as EXN_keepM(_cur)'s keep: runs' frames, m-form call keeps (kit 4f18c75d4900). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece Ec (lib/B/Prog/ExvB_NumCut.v EXN_Ec), PART a: the symbolic states, their
   seats from the machine facts, the cut facts (geometry, the node header, the tree root), the close to CD and the
   arms v = 0 (exe_arm_0, B 0x83e3c beqz -> CD) and after __wrap_bcmp (exe_arm_r2, B 0x83eb0 to CD, including the
   in->differs store whose ASan guard 0x83ec8 -> errpath_store4 0x84180 the run shows not taken from q's shadow
   entry). ExvB_NumE.v proves EXN_Ec from them. Proves no function (kind: segment lemma). Code: the neutral listing
   the internal file ex_value.fuzz_preset.asan-ubsan.s (a Theorem Labs lane's listing of the B' pin), lines 582-619 (ExvB_NumE.v's header).
   Old-pin kit 4f18c75d4900 (rebind base a9d3e245c2b): the engine tactics are ExvB_Num_eng.v's (ex_ws_x.v's, restated);
   exe_mn_run / exe_mn_of give the memnorm keep EXN_keepM_cur asks across each engine run from the run's frame on the
   whole overlay; exe_v_rng / exe_first_byte_nz / exe_blk_op restate ExvB_Disp_str_k.v's exvs_v_rng /
   exvs_first_byte / exvs_blk_op (that file does not compile on the kit yet).
   Numerals: 0x968, 0x984 (DERIVED: the return-site offsets of `jal __wrap_strcmp` / `jal __wrap_bcmp`, B 0x83e94 /
   0x83eb0); 288, 304, 319, 16384, 16688 (DERIVED: ex_value's frame of the image record pi_frame F_ex_value = 304, the
   realigned s1's band below sp, strtod's window STK_RT_STRTOD and their sum); 1, 2, 3, 4, 8, 9, 10, 13, 18, 19, 20,
   22, 24, 25, 26, 27 (WORD: register numbers); 32, 33, 34, 35, 36 (LENGTH: the runner's extra atoms after the 32
   registers, and env_agree's register count); 5 (LENGTH: the register index width); 0, 8, 16, 24, 32, 36, 40, 56,
   64, 128, 136, 144, 152, 160 (LENGTH: field offsets v->type / v->num / v->str, in->scratch / in->differs, the
   cursor's and the node's sizes, the frame's num slot and bytes, the s1 spill slots and their end); 3, 6 (WORD: the
   alignment exponent and srli's shift, JNum's tag, the largest tag); 45, 48 (WORD: the bytes '-' and '0'); 256, 63,
   60 (LENGTH: the byte range, the ALU's shift mask, a quotient bound); 4096, 2 ^ 44 = 17592186044416, 2 ^ 32,
   2 ^ 46, 2 ^ 47, 2 ^ 63, 2 ^ 64 (LENGTH: the low page, the shadow's size, the length, stack, address-space and word
   bounds); 2 ^ 31, 0x7fff8000 (LENGTH: a bound above kLowMemEnd, and kLowMemEnd's value, the top of the image
   segments' range). No ADDRESS: every pc is exv_pc of a DERIVED offset or a callee's B_prog_sigma. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YGcfRoomKeep FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMx YP08.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S1ImgCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require S1ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import
ExvB_Stmt ExvB_Num_eng ExvB_Open_sh ExvB_Open_kt ExvB_Loop_kit ExvB_Loop_kitQ
ExvB_NumPure ExvB_NumCut.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Existing Instance prh_img_B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ======== the pcs of the piece (DERIVED offsets of ex_value's entry; callee entries from the listing) ======== *)
Definition EXE_CC : Z := exv_pc EXN_CC.        (* the cut CC *)
Definition EXE_CD : Z := exv_pc EXN_CD.        (* the cut CD *)
Definition EXE_R1 : Z := exv_pc 0x968.         (* the return site of `jal __wrap_strcmp` *)
Definition EXE_R2 : Z := exv_pc 0x984.         (* the return site of `jal __wrap_bcmp` *)
Definition EXE_SCMP : Z := B_prog_sigma AS___wrap_strcmp.
Definition EXE_BCMP : Z := B_prog_sigma AS___wrap_bcmp.
Definition EXE_SB : sv := SOff 25 0.           (* s9 = the shadow base *)

(* the shadow address of atom n + c as the code computes it: ((n + c) >> 3) + s9 *)
Definition exe_shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 25 0).

(* ======== the symbolic states ======== *)
(* the s1 spills the piece reads: 136(s1) = f + 64, 144(s1) = shadow (q), 152(s1) = v *)
Definition exe_Rs1 (vsv : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 136 160 0 0
    [YP09.mkChunk 136 (CVal 8 (SOff 24 64)); YP09.mkChunk 144 (CVal 8 (exe_shx 19 0)); YP09.mkChunk 152 (CVal 8 vsv)].
(* in->scratch (read) and in->differs (written) *)
Definition exe_Rq : YP09.region :=
  YP09.mkRegion (Some 19%nat) 24 36 32 36 [YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 4 (SOff 34 0))].
(* v->type and v->str (read) *)
Definition exe_Rv : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0))].
(* in->differs alone (the two return sites) *)
Definition exe_Rq1 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 32 36 32 36 [YP09.mkChunk 32 (CVal 4 (SOff 33 0))].
(* s4 = q + 24, s11 = shadow (q + 24) (EXN_CC_pre) *)
Definition exe_regs : list sv := sr_set (sr_set sr_atoms 20%bv (SOff 19 24)) 27%bv (exe_shx 19 24).
Definition exe_facts0 : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 3); (19%nat, mkAF (2 ^ 46) (2 ^ 47 - 40) 3); (25%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
(* CC, v <> 0: atoms 32 v, 33 in->scratch, 34 in->differs, 35 v->type, 36 v->str *)
Definition ss_exe_v : sstate :=
  mkSS EXE_CC exe_regs [exe_Rs1 (SOff 32 0); exe_Rq; exe_Rv] None
    (mkFacts (exe_facts0 ++ [(32%nat, mkAF 4096 (2 ^ 47 - 56) 3); (35%nat, mkAF 0 6 0)])
       [mkAC BC_NE (SOff 32 0) (SLit 0)] []).
Definition exe_SHv : list shent := [mkSHE 19 0 40; mkSHE 32 0 56].
(* CC, v = 0 *)
Definition ss_exe_0 : sstate := mkSS EXE_CC sr_atoms [exe_Rs1 (SLit 0)] None (mkFacts exe_facts0 [] []).
Definition exe_SH0 : list shent := [].
(* a return site: atoms 32 v, 33 in->differs *)
Definition ss_exe_r (pc : Z) : sstate := mkSS pc sr_atoms [exe_Rs1 (SOff 32 0); exe_Rq1] None (mkFacts exe_facts0 [] []).
Definition exe_SHr : list shent := [mkSHE 19 0 40].
(* the registers the piece keeps (the callee-saved ones but ra) *)
Definition exe_kept : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26]%bv.

(* ======== pure lemmas ======== *)
Lemma exe_numch_rng : forall z, PjGrammar.numch z = true -> 0 < z < 256.
Proof.
intros z H. unfold PjGrammar.numch, PjGrammar.digit in H.
repeat (apply orb_prop in H; destruct H as [H|H]); try (apply Z.eqb_eq in H; lia).
apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* the number arm's text is NUL-free bytes and its value is jr_strtod's (exn_N_unfold) *)
Lemma exe_N_txt : forall xs t bt r, exn_N xs = Some (PjTree.JNum t bt, r) ->
  Forall (fun z => 0 < z < 256) t /\ bt = snd (ReaderRes.jr_strtod t).
Proof.
intros xs t bt r H. rewrite exn_N_unfold in H. cbv zeta in H.
assert (DG : forall c, PjGrammar.digit c = true -> 0 < c < 256).
{ intros c0 Hc. unfold PjGrammar.digit in Hc. apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
assert (NC : forall l, Forall (fun z => 0 < z < 256) (fst (PjGrammar.span PjGrammar.numch l))).
{ intros l. eapply Forall_impl; [|exact (exn_span_all_numch l)]. intros z Hz. exact (exe_numch_rng z Hz). }
destruct xs as [|b0 xs']; [cbn in H; discriminate H|].
revert H. destruct (b0 =? 45) eqn:E45; cbn [skipn firstn app].
- apply Z.eqb_eq in E45. destruct xs' as [|c0 z]; cbn [skipn firstn app]; [intro H; discriminate H|].
  destruct (negb (PjGrammar.digit c0)) eqn:Edc; cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c0 =? 48) && ?m then _ else _] => destruct ((c0 =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [PjGrammar.whole ?a ?b] => destruct (PjGrammar.whole a b) end;
    cbv beta iota; [|intro H; discriminate H].
  intro H. injection H as Ht Hb _. subst t bt. split; [|reflexivity].
  constructor; [lia|]. constructor; [apply DG; apply negb_false_iff; exact Edc | apply NC].
- destruct (negb (PjGrammar.digit b0)) eqn:Edc; cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (b0 =? 48) && ?m then _ else _] => destruct ((b0 =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [PjGrammar.whole ?a ?b] => destruct (PjGrammar.whole a b) end;
    cbv beta iota; [|intro H; discriminate H].
  intro H. injection H as Ht Hb _. subst t bt. split; [|reflexivity].
  constructor; [apply DG; apply negb_false_iff; exact Edc | apply NC].
Qed.

(* ---- the strtod model's bit pattern is a 64-bit word (SoftFloat.f128_to_d packs 64-bit fields) ---- *)
Definition R64 (x : Z) : Prop := 0 <= x < 2 ^ 64.
Lemma exe_R_bits : forall x, 0 <= x -> (forall i, 64 <= i -> Z.testbit x i = false) -> R64 x.
Proof.
intros x Hx H. split; [exact Hx|]. destruct (Z.lt_ge_cases x (2 ^ 64)) as [h|h]; [exact h|].
exfalso. assert (Hl : 64 <= Z.log2 x).
{ rewrite <- (Z.log2_pow2 64) by lia. apply Z.log2_le_mono. exact h. }
pose proof (Z.bit_log2 x ltac:(lia)) as Hb. rewrite (H _ Hl) in Hb. discriminate.
Qed.
Lemma exe_R_hi : forall x i, R64 x -> 64 <= i -> Z.testbit x i = false.
Proof.
intros x i [H0 H1] Hi. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
apply Z.bits_above_log2; [lia|]. apply (proj1 (Z.log2_lt_pow2 x i ltac:(lia))).
apply Z.lt_le_trans with (2 ^ 64); [lia | apply Z.pow_le_mono_r; lia].
Qed.
Lemma exe_R_wrap : forall x, R64 (SoftFloat.wrap64 x).
Proof.
intros x. unfold R64, SoftFloat.wrap64. change SoftFloat.ONES64 with (Z.ones 64).
rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma exe_R_lor : forall a b, R64 a -> R64 b -> R64 (Z.lor a b).
Proof.
intros a b Ha Hb. apply exe_R_bits; [apply (proj2 (Z.lor_nonneg a b)); split; [exact (proj1 Ha) | exact (proj1 Hb)]|].
intros i Hi. rewrite Z.lor_spec, (exe_R_hi a i Ha Hi), (exe_R_hi b i Hb Hi). reflexivity.
Qed.
Lemma exe_R_lxor : forall a b, R64 a -> R64 b -> R64 (Z.lxor a b).
Proof.
intros a b Ha Hb. apply exe_R_bits.
- apply (proj2 (Z.lxor_nonneg a b)). split; intros _; [exact (proj1 Hb) | exact (proj1 Ha)].
- intros i Hi. rewrite Z.lxor_spec, (exe_R_hi a i Ha Hi), (exe_R_hi b i Hb Hi). reflexivity.
Qed.
Lemma exe_R_land1 : forall a b, R64 a -> 0 <= b -> R64 (Z.land a b).
Proof.
intros a b Ha Hb. apply exe_R_bits; [apply (proj2 (Z.land_nonneg a b)); left; exact (proj1 Ha)|].
intros i Hi. rewrite Z.land_spec, (exe_R_hi a i Ha Hi). reflexivity.
Qed.
Lemma exe_R_land2 : forall a b, 0 <= a -> R64 b -> R64 (Z.land a b).
Proof. intros a b Ha Hb. rewrite Z.land_comm. apply exe_R_land1; assumption. Qed.
Lemma exe_R_shr : forall a n, R64 a -> 0 <= n -> R64 (Z.shiftr a n).
Proof.
intros a n Ha Hn. apply exe_R_bits; [apply (proj2 (Z.shiftr_nonneg a n)); exact (proj1 Ha)|].
intros i Hi. rewrite Z.shiftr_spec by lia. apply exe_R_hi; [exact Ha | lia].
Qed.
Lemma exe_R_b2z : forall b, R64 (SoftFloat.b2z b).
Proof. intros [|]; unfold R64, SoftFloat.b2z; lia. Qed.
Lemma exe_R_sra : forall x, R64 (SoftFloat.sra63 x).
Proof. intros x. unfold SoftFloat.sra63. destruct (SoftFloat.is_neg64 x); unfold R64, SoftFloat.ONES64; lia. Qed.
Lemma exe_R_tr : forall s r, R64 s -> R64 (SoftFloat.trunc_round s r).
Proof.
intros s r Hs. unfold SoftFloat.trunc_round.
destruct (negb _); [apply exe_R_wrap|]. destruct (negb _); [apply exe_R_wrap | exact Hs].
Qed.
Ltac exe_nonneg :=
  first [ lia
        | apply (proj2 (Z.land_nonneg _ _)); right; lia
        | refine (proj1 (_ : R64 _)); exe_rtac ]
with exe_rtac :=
  lazymatch goal with
  | |- R64 (Z.lor _ _) => apply exe_R_lor; exe_rtac
  | |- R64 (Z.lxor _ _) => apply exe_R_lxor; exe_rtac
  | |- R64 (Z.land _ _) =>
      first [ apply exe_R_land1; [exe_rtac | exe_nonneg] | apply exe_R_land2; [exe_nonneg | exe_rtac] ]
  | |- R64 (Z.shiftr _ _) => apply exe_R_shr; [exe_rtac | exe_nonneg]
  | |- R64 (SoftFloat.trunc_round _ _) => apply exe_R_tr; exe_rtac
  | |- R64 (SoftFloat.b2z _) => apply exe_R_b2z
  | |- R64 (SoftFloat.nez64 _) => apply exe_R_b2z
  | |- R64 (SoftFloat.eqz64 _) => apply exe_R_b2z
  | |- R64 (SoftFloat.sra63 _) => apply exe_R_sra
  | |- R64 (SoftFloat.shl64 _ _) => apply exe_R_wrap
  | |- R64 (SoftFloat.add64 _ _) => apply exe_R_wrap
  | |- R64 (SoftFloat.sub64 _ _) => apply exe_R_wrap
  | |- R64 (SoftFloat.wrap64 _) => apply exe_R_wrap
  | |- R64 (SoftFloat.lo64 _) => apply exe_R_wrap
  | |- R64 (SoftFloat.hi64 _) => apply exe_R_wrap
  | |- R64 _ => unfold R64, SoftFloat.DQUIET; lia
  end.
Lemma exe_f128_range : forall y, R64 (SoftFloat.f128_to_d y).
Proof.
intros y. unfold SoftFloat.f128_to_d. cbv zeta.
match goal with |- context [match ?E with pair _ _ => _ end] => destruct E as [dE dS] eqn:Ep end.
assert (HdS : R64 dS).
{ repeat match type of Ep with context [if ?c then _ else _] => destruct c end;
  injection Ep as _ <-; exe_rtac. }
apply exe_R_lor; [apply exe_R_lor; [apply exe_R_wrap | exe_rtac] | exact HdS].
Qed.
Lemma exe_jr_strtod_bits : forall t, 0 <= snd (ReaderRes.jr_strtod t) < 2 ^ 64.
Proof.
intros t. unfold ReaderRes.jr_strtod.
destruct (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.strtod_c.strtod_model t) as [[bt cn]|] eqn:EM;
  cbn [snd]; [|lia].
revert EM. unfold OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.strtod_c.strtod_model,
  FloatScan.scan_strtod. cbv zeta.
match goal with |- context [FloatScan.floatscan ?a ?b ?c ?d] =>
  destruct (FloatScan.floatscan a b c d) as [[f y]|] end; cbv beta iota; intros EM; [|discriminate EM].
injection EM as <- _. apply exe_f128_range.
Qed.

(* ---- 8-byte words compare bytewise exactly when they are equal ---- *)
Lemma exe_le_inj : forall b1 b2, 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  (forall k, (k < 8)%nat -> YG0f.le_byte b1 8 k = YG0f.le_byte b2 8 k) -> b1 = b2.
Proof.
intros b1 b2 H1 H2 H. apply Z.bits_inj'. intros t Ht.
destruct (Z.lt_ge_cases t 64) as [Hlt|Hge].
- assert (Hk : (Z.to_nat (t / 8) < 8)%nat)
    by (assert (t / 8 < 8) by (apply Z.div_lt_upper_bound; lia); lia).
  pose proof (H _ Hk) as E. unfold YG0f.le_byte in E.
  change (8 * Z.of_nat 8) with 64 in E. rewrite !(Z.mod_small _ (2 ^ 64)) in E by lia.
  apply (f_equal (fun z => Z.testbit z (t mod 8))) in E. cbv beta in E.
  change 256 with (2 ^ 8) in E.
  pose proof (Z.mod_pos_bound t 8 ltac:(lia)) as Hm.
  rewrite !Z.testbit_mod_pow2 in E by lia.
  replace (t mod 8 <? 8) with true in E by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in E.
  rewrite !Z.shiftr_spec in E by lia. rewrite Z2Nat.id in E by (apply Z.div_pos; lia).
  replace (t mod 8 + 8 * (t / 8)) with t in E by (pose proof (Z.div_mod t 8 ltac:(lia)); lia).
  exact E.
- rewrite (exe_R_hi b1 t H1 Hge), (exe_R_hi b2 t H2 Hge). reflexivity.
Qed.

(* ---- bytes, strings and shadow facts in the view ---- *)
Section bview. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma exe_garr8_aview : forall (H : word -> bool) m p l j, garr8 segs (mrestrict H m) p l -> (j < length l)%nat ->
  aview segs H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j Hg Hj. unfold aview. rewrite (garr8_mbyte segs _ p l j Hg Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (Hg j Hj)).
Qed.
Lemma exe_first_byte : forall (W : world segs) m p l, garr8 segs (mrestrict (w_H W) m) p (l ++ [0]) ->
  Forall (fun c => 0 < c < 256) l -> first_byte segs W m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W m p l Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (exe_garr8_aview (w_H W) m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + assert (Hlt : (Z.to_nat i < length l)%nat) by lia.
    pose proof (proj1 (Forall_forall _ _) Hnz _ (nth_In l 0 Hlt)) as Hc. cbv beta in Hc. lia.
- intros _. rewrite (exe_garr8_aview (w_H W) m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma exe_val8_aview : forall (H : word -> bool) m p b k, val_mem segs (mrestrict H m) p 8 b -> (k < 8)%nat ->
  aview segs H m (p + Z.of_nat k) = Some (YG0f.le_byte b 8 k).
Proof.
intros H m p b k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma exe_val_aview : forall (H : word -> bool) m p (n : nat) b k, val_mem segs (mrestrict H m) p n b -> (k < n)%nat ->
  aview segs H m (p + Z.of_nat k) <> None.
Proof. intros H m p n b k Hv Hk. unfold aview. rewrite (Hv k Hk). discriminate. Qed.
Lemma exe_bytes_eq8 : forall (H : word -> bool) m p1 p2 b1 b2, 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  val_mem segs (mrestrict H m) p1 8 b1 -> val_mem segs (mrestrict H m) p2 8 b2 ->
  ((forall i, 0 <= i < 8 -> aview segs H m (p1 + i) = aview segs H m (p2 + i)) <-> b1 = b2).
Proof.
intros H m p1 p2 b1 b2 R1 R2 V1 V2. split.
- intros Heq. apply exe_le_inj; [exact R1 | exact R2|]. intros k Hk.
  pose proof (Heq (Z.of_nat k) ltac:(lia)) as E.
  rewrite (exe_val8_aview H m p1 b1 k V1 Hk), (exe_val8_aview H m p2 b2 k V2 Hk) in E.
  injection E as E. exact E.
- intros <- i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (exe_val8_aview H m p1 b1 _ V1), (exe_val8_aview H m p2 b1 _ V2) by lia. reflexivity.
Qed.
Lemma exe_str_eq : forall (H : word -> bool) m p1 p2 l1 l2,
  garr8 segs (mrestrict H m) p1 (l1 ++ [0]) -> garr8 segs (mrestrict H m) p2 (l2 ++ [0]) ->
  ((Z.of_nat (length l1) = Z.of_nat (length l2) /\
    forall i, 0 <= i < Z.of_nat (length l1) -> aview segs H m (p1 + i) = aview segs H m (p2 + i)) <-> l1 = l2).
Proof.
intros H m p1 p2 l1 l2 G1 G2. split.
- intros (Hl & Heq). apply (nth_ext l1 l2 0 0); [lia|]. intros jj Hj.
  pose proof (Heq (Z.of_nat jj) ltac:(lia)) as E.
  rewrite (exe_garr8_aview H m p1 (l1 ++ [0]) jj G1) in E by (rewrite length_app; cbn; lia).
  rewrite (exe_garr8_aview H m p2 (l2 ++ [0]) jj G2) in E by (rewrite length_app; cbn; lia).
  rewrite app_nth1 in E by lia. rewrite app_nth1 in E by lia. injection E as E. exact E.
- intros <-. split; [reflexivity|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
  rewrite (exe_garr8_aview H m p1 (l1 ++ [0]) _ G1), (exe_garr8_aview H m p2 (l1 ++ [0]) _ G2)
    by (rewrite length_app; cbn; lia). reflexivity.
Qed.
Lemma exe_val_move : forall (H : word -> bool) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
intros H m m' a n v HA Hv k Hk. rewrite (mbyte_of_aview segs H H m m' (a + Z.of_nat k)) by (apply HA; lia).
exact (Hv k Hk).
Qed.
Lemma exe_garr_move : forall (H : word -> bool) m m' a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H m') a l.
Proof.
intros H m m' a l HA Hg jj Hj. destruct (Hg jj Hj) as [Hv Hr]. split; [|exact Hr].
apply (exe_val_move H m m'); [|exact Hv]. intros i Hi. rewrite <- Z.add_assoc. apply HA. lia.
Qed.
Lemma exe_apresent_aview : forall (H : word -> bool) m a, apresent H m a -> aview segs H m a <> None.
Proof. intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
End bview.

(* ---- sv denotations ---- *)
Lemma exe_den_off : forall E n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n x c H Hx Hc. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
rewrite (U_atom_off E n x c H Hx Hc). rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma exe_den_shx : forall E n c v, ew E n = Z_to_bv 64 v -> ew E 25 = Z_to_bv 64 SHADOW_OFF ->
  0 <= v -> 0 <= c -> v + c < 2 ^ 63 -> sv_denot E (exe_shx n c) = Z_to_bv 64 (shadow_addr (v + c)).
Proof.
intros E n c v Hn Hm Hv Hc Hvc. unfold exe_shx, shadow_addr.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 25 0)))).
f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 25 0)) = SHADOW_OFF + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm.
rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia).
rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia.
Qed.
Lemma exe_ew : forall regs extra n (r : bv 5) x, Z.of_nat n = bv_unsigned r -> YK11.getr regs r = Z_to_bv 64 x ->
  ew (Ereg regs extra) n = Z_to_bv 64 x.
Proof. intros regs extra n r x Hn H. rewrite (ew_Ereg_nat regs extra n r Hn). exact H. Qed.
Lemma exe_U : forall E n x, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> bv_unsigned (ew E n) = x.
Proof. intros E n x H Hx. rewrite H. apply unsigned_lit_small. exact Hx. Qed.

(* ======== the seats: a symbolic state at a cut / return site from the machine facts ======== *)
Section seat. Context {rc : YM05.RunCeil}.
Lemma exe_rs1_ok : forall E (W : world rsegs) mem s1 q f vsv v,
  bv_unsigned (ew E 9) = s1 -> ew E 19 = Z_to_bv 64 q -> ew E 24 = Z_to_bv 64 f -> ew E 25 = Z_to_bv 64 SHADOW_OFF ->
  sv_denot E vsv = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  0 <= s1 -> s1 + 160 <= 2 ^ 64 -> 0 <= q -> q + 40 <= 2 ^ 47 -> 0 <= f -> f + 64 < 2 ^ 64 ->
  val_mem rsegs (rdW W mem) (s1 + 136) 8 (f + 64) -> val_mem rsegs (rdW W mem) (s1 + 144) 8 (shadow_addr q) ->
  val_mem rsegs (rdW W mem) (s1 + 152) 8 v ->
  YP09.region_ok rsegs E (rdW W mem) (exe_Rs1 vsv).
Proof.
intros E W mem s1 q f vsv v U9 E19 E24 E25 Ev Hv Hs0 Hs1 Hq0 Hq1 Hf0 Hf1 C136 C144 C152.
unfold YP09.region_ok, exe_Rs1.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
assert (Hsh : 0 <= shadow_addr q < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  assert (q / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. }
repeat apply Forall_cons; try apply Forall_nil.
- apply (chunk_ok_val rsegs E _ s1 136 8 (SOff 24 64) (f + 64)); [| cbn; lia | cbn; lia | exact C136].
  apply (exe_den_off E 24 f 64 E24); lia.
- apply (chunk_ok_val rsegs E _ s1 144 8 (exe_shx 19 0) (shadow_addr q)); [| cbn; lia | cbn; lia | exact C144].
  rewrite (exe_den_shx E 19 0 q E19 E25) by lia. rewrite Z.add_0_r. reflexivity.
- apply (chunk_ok_val rsegs E _ s1 152 8 vsv v); [exact Ev | cbn; lia | cbn; lia | exact C152].
Qed.

Lemma exe_st_v : forall (fxc : YK11.FPState) (W : world rsegs) regs mem s1 q f v scr dl tg str,
  YK11.getr regs 9 = Z_to_bv 64 s1 -> YK11.getr regs 19 = Z_to_bv 64 q -> YK11.getr regs 24 = Z_to_bv 64 f ->
  YK11.getr regs 25 = Z_to_bv 64 SHADOW_OFF -> YK11.getr regs 20 = Z_to_bv 64 (q + 24) ->
  YK11.getr regs 27 = Z_to_bv 64 (shadow_addr (q + 24)) ->
  2 ^ 46 <= s1 -> s1 mod 8 = 0 -> s1 + 160 <= q -> 2 ^ 46 <= q -> q + 40 <= 2 ^ 47 -> q mod 8 = 0 ->
  0 <= f < 2 ^ 47 -> 4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 ->
  0 <= scr < 2 ^ 64 -> 0 <= dl < 2 ^ 32 -> 0 <= tg <= 6 -> 0 <= str < 2 ^ 64 ->
  (q + 40 <= v \/ v + 56 <= q) -> (s1 + 160 <= v \/ v + 56 <= s1) ->
  val_mem rsegs (rdW W mem) (s1 + 136) 8 (f + 64) -> val_mem rsegs (rdW W mem) (s1 + 144) 8 (shadow_addr q) ->
  val_mem rsegs (rdW W mem) (s1 + 152) 8 v -> val_mem rsegs (rdW W mem) (q + 24) 8 scr ->
  val_mem rsegs (rdW W mem) (q + 32) 4 dl -> (forall o, 32 <= o < 36 -> writable_at rsegs (rdW W mem) (q + o)) ->
  val_mem rsegs (rdW W mem) v 4 tg -> val_mem rsegs (rdW W mem) (v + 16) 8 str ->
  st_ok rsegs (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 scr; Z_to_bv 64 dl; Z_to_bv 64 tg; Z_to_bv 64 str]) ss_exe_v
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 EXE_CC) mem (YK11.seg_rom rsegs))).
Proof.
intros fxc W regs mem s1 q f v scr dl tg str R9 R19 R24 R25 R20 R27 Hs1lo Hs18 Hs1q Hqlo Hqhi Hq8 Hf Hvlo Hvhi Hv8
  Hscr Hdl Htg Hstr Hvq Hvs1 C136 C144 C152 Cq24 Cq32 Hwr Cv0 Cv16.
remember (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 scr; Z_to_bv 64 dl; Z_to_bv 64 tg; Z_to_bv 64 str]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; exact (exe_ew regs _ 9 9%bv s1 eq_refl R9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (subst E; exact (exe_ew regs _ 19 19%bv q eq_refl R19)).
assert (E24 : ew E 24 = Z_to_bv 64 f) by (subst E; exact (exe_ew regs _ 24 24%bv f eq_refl R24)).
assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (exe_ew regs _ 25 25%bv SHADOW_OFF eq_refl R25)).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 scr) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 dl) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 tg) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = Z_to_bv 64 str) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (apply exe_U; [exact E9 | lia]).
assert (U19 : bv_unsigned (ew E 19) = q) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
assert (U32 : bv_unsigned (ew E 32) = v) by (apply exe_U; [exact E32 | lia]).
assert (U35 : bv_unsigned (ew E 35) = tg) by (apply exe_U; [exact E35 | lia]).
rewrite restrict_mkst_fx. unfold ss_exe_v. apply exw_st_ok_full.
- unfold exe_regs. apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg | |] | |];
    try (intros X; discriminate X).
  + rewrite (exe_den_off E 19 q 24 E19) by lia. exact R20.
  + rewrite (exe_den_shx E 19 24 q E19 E25) by lia. exact R27.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (exe_rs1_ok E W mem s1 q f (SOff 32 0) v U9 E19 E24 E25); try lia; try assumption.
    rewrite (exe_den_off E 32 v 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
  + unfold YP09.region_ok, exe_Rq.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [exact Hwr|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ q 24 8 (SOff 33 0) scr); [| cbn; lia | cbn; lia | exact Cq24].
      rewrite (exe_den_off E 33 scr 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (chunk_ok_val rsegs E _ q 32 4 (SOff 34 0) dl); [| cbn; lia | cbn; lia | exact Cq32].
      rewrite (exe_den_off E 34 dl 0 E34) by lia. rewrite Z.add_0_r. reflexivity.
  + unfold YP09.region_ok, exe_Rv.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (chunk_ok_val rsegs E _ v 0 4 (SOff 35 0) tg); [| cbn; lia | cbn; lia | rewrite Z.add_0_r; exact Cv0].
      rewrite (exe_den_off E 35 tg 0 E35) by lia. rewrite Z.add_0_r. reflexivity.
    * apply (chunk_ok_val rsegs E _ v 16 8 (SOff 36 0) str); [| cbn; lia | cbn; lia | exact Cv16].
      rewrite (exe_den_off E 36 str 0 E36) by lia. rewrite Z.add_0_r. reflexivity.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, exe_Rs1, exe_Rq, exe_Rv.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19, U32. repeat split; lia.
- split; [|split; [|exact I]].
  + unfold exe_facts0. cbn [f_atoms atoms_ok app]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U25, U32, U35. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF. repeat split; lia.
  + cbn [f_conds conds_ok]. split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ne_U, (U_atom E 32 v E32) by lia. rewrite U_lit by lia.
    apply negb_true_iff. apply Z.eqb_neq. lia.
Qed.

Lemma exe_st_0 : forall (fxc : YK11.FPState) (W : world rsegs) regs mem s1 q f,
  YK11.getr regs 9 = Z_to_bv 64 s1 -> YK11.getr regs 19 = Z_to_bv 64 q -> YK11.getr regs 24 = Z_to_bv 64 f ->
  YK11.getr regs 25 = Z_to_bv 64 SHADOW_OFF ->
  2 ^ 46 <= s1 -> s1 mod 8 = 0 -> s1 + 160 <= q -> 2 ^ 46 <= q -> q + 40 <= 2 ^ 47 -> q mod 8 = 0 -> 0 <= f < 2 ^ 47 ->
  val_mem rsegs (rdW W mem) (s1 + 136) 8 (f + 64) -> val_mem rsegs (rdW W mem) (s1 + 144) 8 (shadow_addr q) ->
  val_mem rsegs (rdW W mem) (s1 + 152) 8 0 ->
  st_ok rsegs (Ereg regs []) ss_exe_0 (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 EXE_CC) mem (YK11.seg_rom rsegs))).
Proof.
intros fxc W regs mem s1 q f R9 R19 R24 R25 Hs1lo Hs18 Hs1q Hqlo Hqhi Hq8 Hf C136 C144 C152.
remember (Ereg regs []) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; exact (exe_ew regs _ 9 9%bv s1 eq_refl R9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (subst E; exact (exe_ew regs _ 19 19%bv q eq_refl R19)).
assert (E24 : ew E 24 = Z_to_bv 64 f) by (subst E; exact (exe_ew regs _ 24 24%bv f eq_refl R24)).
assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (exe_ew regs _ 25 25%bv SHADOW_OFF eq_refl R25)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (apply exe_U; [exact E9 | lia]).
assert (U19 : bv_unsigned (ew E 19) = q) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
rewrite restrict_mkst_fx. unfold ss_exe_0. apply exw_st_ok_full.
- rewrite HE. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  apply (exe_rs1_ok E W mem s1 q f (SLit 0) 0 U9 E19 E24 E25); try lia; try assumption. reflexivity.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. exact (conj I I).
- split; [|split; exact I].
  unfold exe_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U19, U25. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

Lemma exe_st_r : forall (fxc : YK11.FPState) (W : world rsegs) regs mem pc s1 q f v dl,
  YK11.getr regs 9 = Z_to_bv 64 s1 -> YK11.getr regs 19 = Z_to_bv 64 q -> YK11.getr regs 24 = Z_to_bv 64 f ->
  YK11.getr regs 25 = Z_to_bv 64 SHADOW_OFF ->
  2 ^ 46 <= s1 -> s1 mod 8 = 0 -> s1 + 160 <= q -> 2 ^ 46 <= q -> q + 40 <= 2 ^ 47 -> q mod 8 = 0 -> 0 <= f < 2 ^ 47 ->
  0 <= v < 2 ^ 64 -> 0 <= dl < 2 ^ 32 ->
  val_mem rsegs (rdW W mem) (s1 + 136) 8 (f + 64) -> val_mem rsegs (rdW W mem) (s1 + 144) 8 (shadow_addr q) ->
  val_mem rsegs (rdW W mem) (s1 + 152) 8 v -> val_mem rsegs (rdW W mem) (q + 32) 4 dl ->
  (forall o, 32 <= o < 36 -> writable_at rsegs (rdW W mem) (q + o)) ->
  st_ok rsegs (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 dl]) (ss_exe_r pc)
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 pc) mem (YK11.seg_rom rsegs))).
Proof.
intros fxc W regs mem pc s1 q f v dl R9 R19 R24 R25 Hs1lo Hs18 Hs1q Hqlo Hqhi Hq8 Hf Hv Hdl C136 C144 C152 Cq32 Hwr.
remember (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 dl]) as E eqn:HE.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (subst E; exact (exe_ew regs _ 9 9%bv s1 eq_refl R9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (subst E; exact (exe_ew regs _ 19 19%bv q eq_refl R19)).
assert (E24 : ew E 24 = Z_to_bv 64 f) by (subst E; exact (exe_ew regs _ 24 24%bv f eq_refl R24)).
assert (E25 : ew E 25 = Z_to_bv 64 SHADOW_OFF) by (subst E; exact (exe_ew regs _ 25 25%bv SHADOW_OFF eq_refl R25)).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 dl) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew E 9) = s1) by (apply exe_U; [exact E9 | lia]).
assert (U19 : bv_unsigned (ew E 19) = q) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
rewrite restrict_mkst_fx. unfold ss_exe_r. apply exw_st_ok_full.
- rewrite HE. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + apply (exe_rs1_ok E W mem s1 q f (SOff 32 0) v U9 E19 E24 E25); try lia; try assumption.
    rewrite (exe_den_off E 32 v 0 E32) by lia. rewrite Z.add_0_r. reflexivity.
  + unfold YP09.region_ok, exe_Rq1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [exact Hwr|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val rsegs E _ q 32 4 (SOff 33 0) dl); [| cbn; lia | cbn; lia | exact Cq32].
    rewrite (exe_den_off E 33 dl 0 E33) by lia. rewrite Z.add_0_r. reflexivity.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint, exe_Rs1, exe_Rq1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U19. repeat split; lia.
- split; [|split; exact I].
  unfold exe_facts0. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U9, U19, U25. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF. repeat split; lia.
Qed.

(* the shadow entries: q's 40 bytes (EXB) and v's 56 (prhex_tree) *)
Lemma exe_shq : forall (H : word -> bool) mem E q,
  bv_unsigned (ew E 19) = q -> bv_unsigned (ew E 25) = SHADOW_OFF -> 2 ^ 46 <= q -> q + 40 <= 2 ^ 47 ->
  range_addressable (aview rsegs H mem) SHADOW_OFF q 40 -> shent_ok rsegs EXE_SB E (mrestrict H mem) (mkSHE 19 0 40).
Proof.
intros H mem E q U19 U25 Hq1 Hq2 HR.
apply (shent_ok_of_range rsegs H mem E EXE_SB 19 q 40 q 0 40 HR).
- unfold EXE_SB. rewrite U_SOff, U25, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
- rewrite U_SOff, U19, Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
- lia.
- intros x Hx. unfold SHADOW_OFF. lia.
Qed.
Lemma exe_shv : forall (H : word -> bool) mem E v,
  bv_unsigned (ew E 32) = v -> bv_unsigned (ew E 25) = SHADOW_OFF -> 0 <= v -> v + 56 <= 2 ^ 47 ->
  (forall x, v <= x < v + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  range_addressable (aview rsegs H mem) SHADOW_OFF v 56 -> shent_ok rsegs EXE_SB E (mrestrict H mem) (mkSHE 32 0 56).
Proof.
intros H mem E v U32 U25 Hv1 Hv2 Hband HR.
apply (shent_ok_of_range rsegs H mem E EXE_SB 32 v 56 v 0 56 HR).
- unfold EXE_SB. rewrite U_SOff, U25, Z.add_0_r. apply zcanon_id. unfold M64, SHADOW_OFF. lia.
- rewrite U_SOff, U32, Z.add_0_r. apply zcanon_id. unfold M64. lia.
- lia.
- lia.
- intros x Hx. apply Hband. lia.
Qed.
End seat.

(* ======== the facts of a cut state ======== *)
Section w. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Hypothesis HYP : EXV_HYP B ARx SK.
Let LAWS := eh_laws B ARx SK HYP.

(* ex_value's own stack need is at least its frame plus strtod's window *)
Lemma exe_stk : forall E, 16688 <= exv_STK E.
Proof.
intros E. unfold exv_STK, STK_ex_value.
assert (HF : @pi_frame prh_img_B F_ex_value = 304) by (vm_compute; reflexivity). rewrite HF.
assert (HZ : 16384 <= zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]).
{ unfold zmaxl. cbn [fold_right].
  assert (HS : STK_RT_STRTOD = 16384) by (vm_compute; reflexivity).
  pose proof (Z.le_max_l STK_RT_STRTOD (Z.max STK_ex_string (Z.max STK_ex_word (Z.max STK_ex_ws 0)))) as M1.
  pose proof (Z.le_max_r STK_RT_STR (Z.max STK_RT_STRTOD (Z.max STK_ex_string (Z.max STK_ex_word (Z.max STK_ex_ws 0))))) as M2.
  pose proof (Z.le_max_r STK_RT_ECALL (Z.max STK_RT_STR (Z.max STK_RT_STRTOD (Z.max STK_ex_string (Z.max STK_ex_word (Z.max STK_ex_ws 0)))))) as M3.
  lia. }
pose proof (Nat2Z.is_nonneg (e_n E)) as Hn. rewrite Nat2Z.inj_succ. nia.
Qed.

(* the geometry of a cut: the entry sp, the realigned base s1, the cursor q, the frame f *)
Lemma exe_geom : forall (fxc : YK11.FPState) E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  let f := frame_addr lyc 1 pos in
  ARx lyc Sc Hpc Wc memc mdc /\ In (1, pos) (frames Sc) /\
  16688 <= exv_STK E /\ 0 <= e_d E /\ e_d E mod 16 = 0 /\
  2 ^ 46 <= exv_sp E /\ exv_sp E + e_d E <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\
  YM05.alloc_ceiling + exv_STK E <= exv_sp E /\ ly_stk_lo lyc + exv_STK E <= exv_sp E /\ YM05.alloc_ceiling <= ly_stk_lo lyc /\
  exv_sp E - 319 <= exv_s1 E <= exv_sp E - 288 /\ exv_s1 E mod 32 = 0 /\ exv_sp E mod 16 = 0 /\
  exv_sp E <= e_q E /\ e_q E + 40 <= exv_sp E + e_d E /\ e_q E mod 8 = 0 /\
  4096 <= f /\ f + 128 <= YM05.alloc_ceiling /\ f mod 32 = 0 /\
  (forall a, exv_sp E - exv_STK E <= a < exv_sp E + e_d E -> apresent (w_H Wc) memc a).
Proof.
intros fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB f.
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (exe_stk E) as HSTK.
pose proof (exv_s1_le E) as [HS1a HS1b].
unfold EXV_PRE in HPRE. cbv zeta in HPRE.
destruct HPRE as (HFP & _ & _ & _ & _ & _ & Hq8 & _ & Hspq & Hqd & Hwin & _).
destruct HFP as (HAF & _ & _).
destruct HAF as (_ & _ & _ & _ & _ & HASK & _).
destruct HASK as (Hm16 & HSTK0 & Hclo & Hlosp & Hsphi & Hhi47 & _ & Hsptop & Htophi).
destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
change (spZ (e_regs E)) with (exv_sp E) in Hm16, Hlosp, Hsphi, Hsptop, Hspq, Hqd, Hdtop.
unfold EXB in HB. cbv zeta in HB.
destruct HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof (proj1 HJ) as HAR. cbv beta in HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & HpresJ & Hastk & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Elo & Ehi & _).
destruct Hastk as (_ & _ & _ & Hlosp' & Hsphi' & Hhi47' & _ & Hsptop' & Htophi').
assert (HIN : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds_x rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR HIN) as (HF1 & HF2 & _).
change (fs_frame_bytes 1) with 128 in HF2.
destruct (alx_frames rsegs B ARx LAWS lyc Sc Hpc Wc memc mdc 1 pos HAR HIN) as (HF32 & _ & _ & _).
unfold f.
split; [exact HAR|]. split; [exact HIN|]. split; [exact HSTK|]. split; [exact Hd0|]. split; [exact Hd16|].
split; [lia|]. split; [rewrite Ehi; lia|]. split; [rewrite Ehi; exact Hhi47|].
split; [lia|]. split; [rewrite Elo; exact Hlosp|]. split; [rewrite Elo; exact Hclo|].
split; [lia|]. split; [exact HS1b|]. split; [exact Hm16|].
split; [exact Hspq|]. split; [exact Hqd|]. split; [exact Hq8|].
split; [exact HF1|]. split; [exact HF2|]. split; [exact HF32|].
intros a Ha. apply HpresJ. lia.
Qed.

(* the node's header: the alignment, the tag and the str / num fields; for a JNum, its text block *)
Lemma exe_hdr : forall m lblk p t D, PRH_Reader.pj_nodeR rsegs m lblk p t D ->
  p mod 8 = 0 /\
  (exists str, PRH_Reader.rd_u32 rsegs m p (PjTree.tag t) /\ PRH_Reader.rd_u64 rsegs m (p + 16) str /\
     (forall txt bits, t = PjTree.JNum txt bits ->
        PRH_Reader.rd_u64 rsegs m (p + 8) bits /\
        exists kk, PRH_Reader.pj_cstrR rsegs m lblk str kk txt)).
Proof.
intros m lblk p t D H.
destruct t as [| | | txt0 bits0 | s0 | its | ms]; cbn [PRH_Reader.pj_nodeR] in H;
  destruct H as (_ & _ & num & str & kids & keys & nn & cap & Hh & Hb);
  destruct Hh as ((Hal & _) & Hty & Hnum & Hstr & _);
  cbn [PjTree.tag] in Hty |- *;
  (split; [exact Hal|]); exists str; (split; [exact Hty|]); (split; [exact Hstr|]);
  intros txt bits Heq; try discriminate Heq.
injection Heq as <- <-.
destruct Hb as (Hnb & _ & _ & _ & _ & kk & Hcs & _).
split; [rewrite <- Hnb; exact Hnum|]. exists kk. exact Hcs.
Qed.

(* the tree root at a cut: where it is, how big, and apart from the cursor / the stack / the scratch *)
Lemma exe_vfacts : forall (fxc : YK11.FPState) E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  PRH_Reader.pj_nodeR rsegs (rdW Wc memc) (prh_lin (e_Lam E)) (e_v E) (e_t E) (e_D E) /\
  prhex_home lyc Sc (e_Lam E) regs (e_v E) 56 /\
  range_addressable (aview rsegs (w_H Wc) memc) SHADOW_OFF (e_v E) 56 /\
  shadow_hull_vis (aview rsegs (w_H Wc) memc) (e_v E) 56 /\
  4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\ e_v E mod 8 = 0 /\
  (forall z, PRH_Reader.pj_footR (e_v E) (e_D E) z ->
     ~ (e_scr E <= z < e_scr E + exv_len E + 1) /\ ~ (e_q E <= z < e_q E + 40) /\
     ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (as_errno B <= z < as_errno B + 4)).
Proof.
intros fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv0.
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (@cf_head_nonneg cp) as CH0.
destruct (exe_geom fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
assert (HFOOT : forall z, PRH_Reader.pj_footR (e_v E) (e_D E) z ->
  ~ (e_scr E <= z < e_scr E + exv_len E + 1) /\ ~ (e_q E <= z < e_q E + 40) /\
  ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (as_errno B <= z < as_errno B + 4)).
{ unfold EXV_PRE in HPRE. cbv zeta in HPRE.
  repeat lazymatch type of HPRE with
  | (e_v E = 0 \/ _) /\ _ => destruct HPRE as [Hvt _]
  | _ /\ _ => destruct HPRE as [_ HPRE]
  end.
  destruct Hvt as [Hz|(_ & _ & Hf)]; [contradiction | exact Hf]. }
unfold EXB in HB. cbv zeta in HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & R2 & HB).
repeat lazymatch type of HB with
| (_ \/ _) => idtac
| _ /\ _ => destruct HB as [_ HB]
end.
destruct HB as [Hz|(Hnd & Hhome & Hra & Hhull)]; [contradiction|].
assert (LAMB : forall b kk, In (b, kk) (e_Lam E) -> 4096 <= b /\ b + kk <= YM05.alloc_ceiling).
{ intros b kk Hin. pose proof HLED as (_ & _ & HBl & _). rewrite Forall_forall in HBl.
  destruct (HBl (b, kk) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & Hc & _).
  assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia). lia. }
assert (HVR : 4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47).
{ destruct Hhome as [(b & mm & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  - destruct (LAMB b mm Hin). lia.
  - destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos' HAR Hin) as (G1 & G2 & _).
    pose proof (fs_frame_bytes_nonneg cid). lia.
  - assert (Esp : spZ regs = exv_s1 E).
    { unfold spZ, w64 in *. rewrite R2, Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64). lia. }
    rewrite Esp in H1. lia. }
pose proof (exe_hdr _ _ _ _ _ Hnd) as (Hal & _).
split; [exact Hnd|]. split; [exact Hhome|]. split; [exact Hra|]. split; [exact Hhull|].
split; [exact (proj1 HVR)|]. split; [exact (proj2 HVR)|]. split; [exact Hal | exact HFOOT].
Qed.

(* ---- ExvB_Disp_str_k.v's exvs_v_rng / exvs_first_byte / exvs_blk_op, restated here: that file (ExvDisp's) does not
   compile on the old-pin kit 4f18c75d4900 yet (its exvs_geom reads a stack-layout conjunct the kit no longer has),
   so this piece no longer Requires it ---- *)
Local Ltac exe_zl := Zify.zify; xlia zchecker.

(* the tree's root (not NULL): apart from the shadow band, the stack window and the cursor *)
Lemma exe_v_rng : forall (fxc : YK11.FPState) E lyc Sc Hpc Wc regs memc mdc k pos,
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  4096 <= e_v E /\ e_v E + 56 <= 2 ^ 47 /\
  (forall x, e_v E <= x < e_v E + 56 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 2 ^ 44)) /\
  (forall z, e_v E <= z < e_v E + 56 -> ~ (exv_sp E - exv_STK E <= z < exv_sp E) /\ ~ (e_q E <= z < e_q E + 40)).
Proof.
intros fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv0.
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (@cf_head_nonneg cp) as CH0.
destruct (exe_geom fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
destruct (exe_vfacts fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hv0)
  as (Hnd & Hhome & _ & _ & Hv4096 & Hv47 & _ & HFOOT).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & R2 & _).
split; [exact Hv4096|]. split; [exact Hv47|]. split.
- destruct Hhome as [(b & kk & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
  + pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
    destruct (HBL (b, kk) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
    destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & _ & Happ & _).
    assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
    intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  + destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos' HAR Hin) as (F2 & F3 & Happ).
    intros x Hx. pose proof (in_app_addr _ _ x Happ ltac:(lia)) as Hx'.
    unfold app_addr, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia.
  + assert (Esp : spZ regs = exv_s1 E).
    { unfold spZ, w64 in *. rewrite R2, Z_to_bv_unsigned. apply bv_wrap_small.
      change (bv_modulus 64) with (2 ^ 64). lia. }
    rewrite Esp in H1. intros x Hx. unfold SHADOW_OFF. lia.
- intros z Hz. destruct (HFOOT z ltac:(left; exact Hz)) as (_ & Hq & Hst & _). split; assumption.
Qed.

(* a NUL-terminated string of non-NUL bytes: strcmp's first_byte *)
Lemma exe_first_byte_nz : forall (W : world rsegs) mem a l,
  garr8 rsegs (mrestrict (w_H W) mem) a (l ++ [0]) -> Forall (fun b => b <> 0) l ->
  first_byte rsegs W mem a (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W mem a l G F. rewrite Forall_forall in F. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0).
  pose proof (exe_garr8_aview rsegs (w_H W) mem a (l ++ [0]) (Z.to_nat i) G ltac:(rewrite length_app; cbn; lia)) as A.
  rewrite Z2Nat.id in A by lia. rewrite app_nth1 in A by lia. split; [exact A|].
  apply F. apply nth_In. lia.
- intros _. pose proof (exe_garr8_aview rsegs (w_H W) mem a (l ++ [0]) (length l) G
    ltac:(rewrite length_app; cbn; lia)) as A.
  rewrite app_nth2, Nat.sub_diag in A by lia. exact A.
Qed.

(* a NUL-terminated string of non-NUL bytes inside a live block: what strcmp asks of each operand but the shadow *)
Lemma exe_blk_op : forall ly S Hp (W : world rsegs) mem md b m x l,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> b <= x -> x + Z.of_nat (length l) + 1 <= b + m ->
  garr8 rsegs (mrestrict (w_H W) mem) x (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  4096 <= x /\ Z.of_nat (length l) + 1 < 2 ^ 32 /\ x + Z.of_nat (length l) + 1 <= YM05.alloc_ceiling /\
  YGcallMx.amem_range8 x (Z.of_nat (length l) + 1) /\
  first_byte rsegs W mem x (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)) /\
  (forall a, x <= a < x + Z.of_nat (length l) + 1 -> aview rsegs (w_H W) mem a <> None) /\
  (forall a, x + Z.of_nat (length l) < a < x + Z.of_nat (length l) - (x + Z.of_nat (length l)) mod 8 + 8 ->
     aview rsegs (w_H W) mem a <> None).
Proof.
intros ly S Hp W mem md b m x l HAR Hin Hbx Hxm G F.
destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hin) as (_ & Hb4096 & Hbc & _ & Hpres & _).
pose proof (eh_blk32 B ARx SK HYP ly S Hp W mem md b m HAR Hin) as H32.
pose proof (eh_blk_amem8 B ARx SK HYP ly S Hp W mem md b m (x - b + Z.of_nat (length l)) HAR Hin ltac:(lia)) as HA8.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [lia|]. split; [lia|]. split; [lia|]. split.
{ unfold YGcallMx.amem_range8 in *. destruct HA8 as [H|[H1 H2]]; [left; lia | right; split; lia]. }
split; [exact (exe_first_byte_nz W mem x l G F)|]. split.
{ intros a Ha. replace a with (x + Z.of_nat (Z.to_nat (a - x))) by lia.
  rewrite (exe_garr8_aview rsegs (w_H W) mem x (l ++ [0]) (Z.to_nat (a - x)) G) by (rewrite length_app; cbn; lia).
  discriminate. }
intros a Ha. destruct (Z_lt_le_dec a (b + req_size m)) as [Hlt|Hge].
- apply (aview_some_of_apresent rsegs). apply (proj1 (Hpres a ltac:(lia))).
- apply (alx_blocks_tail rsegs B ARx LAWS ly S Hp W mem md b m a HAR Hin). split; [exact Hge|]. exe_zl.
Qed.
End w.

(* ======== the arms ======== *)
Lemma exe_mod8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof.
intros x H. assert (Hx : x = 4 * (x / 32) * 8) by lia. rewrite Hx. apply Z.mod_mul. lia.
Qed.

Lemma exe_mod16 : forall x, x mod 32 = 0 -> x mod 16 = 0.
Proof.
intros x H. assert (Hx : x = 2 * (x / 32) * 16) by lia. rewrite Hx. apply Z.mod_mul. lia.
Qed.

Lemma exe_kept_of_pres : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r exe_kept -> YK11.getr regs' r = YK11.getr regs r.
Proof.
intros regs regs' HP r Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). apply HP.
assert (Hz : In (bv_unsigned r) [2; 3; 4; 8; 9; 18; 19; 22; 24; 25; 26])
  by (unfold exe_kept in Hr; apply (in_map (@bv_unsigned 5)) in Hr; exact Hr).
unfold acallee_saved. cbn [In] in Hz. lia.
Qed.

Lemma exe_den_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = Z_to_bv 64 z.
Proof.
intros E z Hz. apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)).
rewrite U_SLit, Z_to_bv_unsigned, (zcanon_id z) by (unfold M64; lia).
symmetry. apply bv_wrap_small. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma exe_in_app_amem : forall {rc : YM05.RunCeil} lo len, in_app lo len -> amem_range lo len.
Proof.
intros rc lo len H. pose proof asan_consts as (AC & _ & _ & _ & _).
unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.

(* a call's result tested against 0 (BC_NE / BC_EQ against x0) *)
Lemma exe_br_ne_t : forall E n (w : word), ew E n = w ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> w <> w64 0.
Proof.
intros E n w Hw Hc ->. rewrite branch_ne_U, U_SOff, U_SLit, Hw in Hc. vm_compute in Hc. discriminate.
Qed.
Lemma exe_br_ne_f : forall E n (w : word), ew E n = w ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w = w64 0.
Proof.
intros E n w Hw Hc. rewrite branch_ne_U, U_SOff, U_SLit, Hw in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. transitivity 0; [lia | reflexivity].
Qed.
Lemma exe_br_eq_t : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> w = w64 0.
Proof.
intros E n w Hw Hc. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc.
apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. transitivity 0; [lia | reflexivity].
Qed.
Lemma exe_br_eq_f : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w <> w64 0.
Proof.
intros E n w Hw Hc ->. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc. vm_compute in Hc. discriminate.
Qed.

(* the write premise of a run whose only window is in->differs (atom 19 = q) *)
Ltac exe_awr U19 :=
  lazymatch goal with |- awr_ok ?E ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply exw_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; rewrite ?U19 in Ha;
    first [ lia | left; lia ] | ]);
  apply awr_ok_nil.

Ltac exe_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* the memnorm keep across an engine run (EXN_keepM / EXN_keepM_cur's premise, kit 4f18c75d4900): the run's frame on
   the whole overlay changes only bytes of its write windows; they lie in [2 ^ 31, 2 ^ 47) (the real stack), above
   every image segment (B_prog_segs_low) and below TASK_SIZE, so YAkMemnorm.memnorm_frame_off_segs applies *)
Lemma exe_mn_run : forall E rs (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs m m' ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  (forall a, Zs a -> 2 ^ 31 <= a < 2 ^ 47) ->
  YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m'.
Proof.
intros E rs m m' Zs HF Hw Hz Hm.
assert (HkL : kLowMemEnd = 0x7fff8000) by reflexivity.
assert (HTS : TASK_SIZE = 2 ^ 47) by reflexivity.
apply (YAkMemnorm.memnorm_frame_off_segs rsegs m m' (2 ^ 31) (2 ^ 47) Hm).
- intros x Hx. apply HF. intros Hin. destruct (in_wrange_windows E rs _ Hin) as (b & wlo & whi & Hi & Hr).
  pose proof (Hz _ (Hw b wlo whi _ Hi Hr)). lia.
- lia.
- intros x Hx. apply YCbq.find_segment_none. intros Himg. pose proof (B_prog_segs_low _ Himg). lia.
Qed.

(* MNK : memnorm m -> memnorm m' across the run that left HF (its frame on the whole overlay), its windows read off
   as exw_kept_of reads them; bnd closes `forall a, Zs a -> 2 ^ 31 <= a < 2 ^ 47` *)
Ltac exe_mn_of HF Zs ev bnd :=
  lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  let MN := fresh "MNK" in
  assert (MN : YAkMemnorm.memnorm rsegs m -> YAkMemnorm.memnorm rsegs m');
  [ apply (exe_mn_run E rs m m' Zs HF);
    [ intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
      repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
      destruct Hin_
    | bnd ]
  | ]
  end.

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis EF : EXN_F B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis MC : EXN_keepM_cur B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.
Let LAWS := eh_laws B ARx SK HYP.

(* from a state at CD whose in->differs is dl', with the piece's write set, to the cut CD *)
Lemma exe_close : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k c j bits
    (regs' : bvmap 5 word) memc' mdc' k' (dl' : Z),
  EXV_PRE B ARx E -> EXN_CC_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j bits ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc memc' mdc' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (exv_s1 E - 2 * ESTACK <= z < exv_s1 E) ->
     ~ (e_q E + 32 <= z < e_q E + 36) -> aview rsegs (w_H Wc) memc' z = aview rsegs (w_H Wc) memc z) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) memc' a) ->
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs memc') ->
  (forall r, In r exe_kept -> YK11.getr regs' r = YK11.getr regs r) ->
  YK11.getr regs' 13 = w64 (shadow_addr (e_q E)) ->
  val_mem rsegs (rdW Wc memc') (e_q E + 32) 4 dl' -> (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> e_dl E = 1 \/ (e_v E <> 0 /\ e_t E <> PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits)) ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc EXN_CD) regs' memc' mdc') (EXV_POST B ARx SK E).
Proof using All.
intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits regs' memc' mdc' k' dl'
  HPRE HCC HJ' HK HG HMN HR R13 HD1 Hdl01 Hiff.
pose proof HCC as HCC'. unfold EXN_CC_pre in HCC'. cbv zeta in HCC'.
destruct HCC' as (HBASE & HDISP & HCUR & HFSH & Hij & HN & Hgarr & Cnum & R22 & R13c & R21 & R20 & R27 & C136).
destruct HBASE as (HB & S144 & S152).
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
pose proof asan_consts as (AC & _ & _ & _ & _).
assert (HESTK : ESTACK = 4096) by reflexivity.
apply (EF fxc lyc Sc Hpc Wc regs' memc' mdc' k' j (PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits) HPRE).
unfold EXN_CD_pre. cbv zeta.
split.
{ split.
  - apply (MC fxc lyc Sc Hpc Wc regs memc mdc k regs' memc' mdc' k' HPRE HB HJ'); [| exact HG | exact HMN |].
    + intros z Hz Hwz Hq0 Hq32. apply HK; [exact Hz | | exact Hq32].
      intros Hc1. apply Hwz. unfold EXN_wz. left. unfold STK_RT_STRTOD. lia.
    + unfold EXN_regs_kept.
      repeat split; apply HR; cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]).
  - split.
    + apply (KS Wc memc memc' 144 (shadow_addr (e_q E)) S144).
      intros z Hz. apply HK; [lia | lia | lia].
    + apply (KS Wc memc memc' 152 (e_v E) S152).
      intros z Hz. apply HK; [lia | lia | lia]. }
split; [exact Hij|]. split; [exact HN|].
split; [rewrite (HR 22%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R22|].
split; [exact R13|].
exists dl'. split; [|split; [exact Hdl01 | exact Hiff]].
unfold EXN_cur in HCUR |- *.
destruct HCUR as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
split; [|split; [|split; [|split; [|exact HD1]]]];
  apply (exe_val_move rsegs (w_H Wc) memc memc'); try assumption;
  intros i Hi; apply HK; lia.
Qed.

(* ---- v = 0: nothing is compared, in->differs is kept ---- *)
Lemma exe_arm_0 : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k c j bits,
  EXV_PRE B ARx E -> EXN_CC_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j bits -> e_v E = 0 ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs EXE_CC regs memc mdc) (EXV_POST B ARx SK E).
Proof using All.
intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits HPRE HCC Hv0.
pose proof HCC as HCC'. unfold EXN_CC_pre in HCC'. cbv zeta in HCC'.
destruct HCC' as (HBASE & HDISP & HCUR & HFSH & Hij & HN & Hgarr & Cnum & R22 & R13c & R21 & R20 & R27 & C136).
destruct HBASE as (HB & S144 & S152).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & HWIN & HFRG & HFZ & HHP & HAB & HRM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & H176 & HFL & HSRC & HTB & HWD & HSB & HQRA & HTREE).
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (exe_mod8 _ HS132) as Hs18.
assert (Hdl01 : e_dl E = 0 \/ e_dl E = 1).
{ pose proof HPRE as HP2. unfold EXV_PRE in HP2. cbv zeta in HP2.
  repeat lazymatch type of HP2 with
  | (e_dl E = 0 \/ e_dl E = 1) /\ _ => destruct HP2 as [HP2 _]
  | _ /\ _ => destruct HP2 as [_ HP2]
  end. exact HP2. }
destruct HCUR as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
assert (HS : st_ok rsegs (Ereg regs []) ss_exe_0
  (restrict (w_H Wc) (@YK11.mkst fxc regs (Z_to_bv 64 EXE_CC) memc (YK11.seg_rom rsegs)))).
{ apply (exe_st_0 fxc Wc regs memc (exv_s1 E) (e_q E) (frame_addr lyc 1 pos) R9 R19 R24 R25);
    try lia; [exact C136 | exact S144 | rewrite <- Hv0; exact S152]. }
assert (SHOK : sh_ok rsegs EXE_SB exe_SH0 (Ereg regs []) (rdW Wc memc))
  by (unfold sh_ok, exe_SH0; apply Forall_nil).
assert (U19 : bv_unsigned (ew (Ereg regs []) 19) = e_q E)
  by (rewrite (ew_Ereg_nat regs [] 19 19%bv eq_refl), R19; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 EXE_CC) with (Z_to_bv 64 EXE_CC).
pose (RUNTO := SRr_run_to_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
exw_run_to RUNTO HS HJ SHOK EXE_CD.
{ exe_awr_ro. }
exw_kept_of HFr (fun a : Z => False) ltac:(fun h => idtac).
exe_mn_of HF (fun a : Z => False) ltac:(fun h => idtac) ltac:(intros amn Hamn; cbv beta in Hamn; destruct Hamn).
lazymatch type of HS with
| st_ok _ _ _ (restrict _ ?mx) =>
  assert (KALL : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H Wc) (ms_mem mx) a = aview rsegs (w_H Wc) memc a)
    by (intros a Ha; apply KEPT; [exact Ha | tauto]);
  assert (RK : forall r, In r (13%bv :: exe_kept) -> YK11.getr (ms_regs mx) r = YK11.getr regs r)
    by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs [] (13%bv :: exe_kept) HS
          (env_agree_refl 32 (Ereg regs [])) ltac:(vm_compute; reflexivity) r Hr))
end.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
  replace pc with (w64 (exv_pc EXN_CD)) by (vm_compute; reflexivity) end.
eapply (exe_close fxc lyc Sc Hpc Wc regs memc mdc k c j bits _ _ _ _ (e_dl E) HPRE HCC).
- exact HJ.
- intros z Hz _ _. apply KALL. exact Hz.
- intros a Ha. exact (apresent_grows (w_H Wc) _ _ a HG Ha).
- exact MNK.
- intros r Hr. apply RK. right. exact Hr.
- rewrite (RK 13%bv ltac:(cbn [In]; left; reflexivity)). exact R13c.
- apply (exe_val_move rsegs (w_H Wc) memc _ (e_q E + 32) 4 (e_dl E)); [|exact Cq32].
  intros i Hi. apply KALL. lia.
- exact Hdl01.
- split; [intros H1; left; exact H1 | intros [H1|(Hv & _)]; [exact H1 | exfalso; exact (Hv Hv0)]].
Qed.

(* ---- after __wrap_bcmp: rv2 = 0 exactly when the trees agree ---- *)
Lemma exe_arm_r2 : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k c j bits
    (regs3 : bvmap 5 word) mem3 md3 k3 (rv2 : word),
  EXV_PRE B ARx E -> EXN_CC_pre B ARx SK E pos fxc lyc Sc Hpc Wc regs memc mdc k c j bits -> e_v E <> 0 ->
  ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
    (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc mem3 md3 k3 ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (exv_s1 E - 2 * ESTACK <= z < exv_s1 E) ->
     ~ (e_q E + 32 <= z < e_q E + 36) -> aview rsegs (w_H Wc) mem3 z = aview rsegs (w_H Wc) memc z) ->
  val_mem rsegs (rdW Wc mem3) (e_q E + 32) 4 (e_dl E) ->
  (forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem3 a) ->
  (YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem3) ->
  (forall r, In r exe_kept -> YK11.getr regs3 r = YK11.getr regs r) ->
  YK11.getr regs3 10 = rv2 -> (rv2 = w64 0 <-> e_t E = PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits) ->
  SRr rsegs Wc (cfg_at (fx := fxc) rsegs EXE_R2 regs3 mem3 md3) (EXV_POST B ARx SK E).
Proof using All.
intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits regs3 mem3 md3 k3 rv2 HPRE HCC Hvn HJ3 HK3 Cq32m HG3 HMN3 HR3 Hrv
  Hcmp.
pose proof HCC as HCC'. unfold EXN_CC_pre in HCC'. cbv zeta in HCC'.
destruct HCC' as (HBASE & HDISP & HCUR & HFSH & Hij & HN & Hgarr & Cnum & R22 & R13c & R21 & R20 & R27 & C136).
destruct HBASE as (HB & S144 & S152).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (HJ & HWIN & HFRG & HFZ & HHP & HAB & HRM & HLED & HCNT &
  R2 & R8 & R9 & R18 & R24 & R25 & R26 & R19 & R3 & R4 & HSAV & H176 & HFL & HSRC & HTB & HWD & HSB & HQRA & HTREE).
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & HIN & HSTK & Hd0 & Hd16 & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & HS132 & Hsp16 &
      Hspq & Hqd & Hq8 & Hf1 & Hf2 & Hf32 & Hpres).
destruct (exe_vfacts B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (Hnd & Hhome & HVRA & HVHULL & Hv4096 & Hv47 & Hv8 & HFOOT).
pose proof asan_consts as (AC & _ & _ & _ & _).
pose proof (exe_mod8 _ HS132) as Hs18.
assert (HESTK : ESTACK = 4096) by reflexivity.
assert (Hdl01 : e_dl E = 0 \/ e_dl E = 1).
{ pose proof HPRE as HP2. unfold EXV_PRE in HP2. cbv zeta in HP2.
  repeat lazymatch type of HP2 with
  | (e_dl E = 0 \/ e_dl E = 1) /\ _ => destruct HP2 as [HP2 _]
  | _ /\ _ => destruct HP2 as [_ HP2]
  end. exact HP2. }
destruct HCUR as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
assert (MV : forall a (n : nat) v, exv_s1 E <= a -> a + Z.of_nat n <= e_q E ->
  val_mem rsegs (rdW Wc memc) a n v -> val_mem rsegs (rdW Wc mem3) a n v).
{ intros a n v Ha Han Hv. apply (exe_val_move rsegs (w_H Wc) memc mem3 a n v); [|exact Hv].
  intros i Hi. apply HK3; lia. }
assert (KIN : forall r : bv 5, In r exe_kept -> YK11.getr regs3 r = YK11.getr regs r) by exact HR3.
assert (G9 : YK11.getr regs3 9 = Z_to_bv 64 (exv_s1 E))
  by (rewrite (KIN 9%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R9).
assert (G19 : YK11.getr regs3 19 = Z_to_bv 64 (e_q E))
  by (rewrite (KIN 19%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R19).
assert (G24 : YK11.getr regs3 24 = Z_to_bv 64 (frame_addr lyc 1 pos))
  by (rewrite (KIN 24%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R24).
assert (G25 : YK11.getr regs3 25 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (KIN 25%bv ltac:(cbv [exe_kept]; cbn [In]; repeat (first [left; reflexivity | right]))); exact R25).
assert (HS : st_ok rsegs (Ereg regs3 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) (ss_exe_r EXE_R2)
  (restrict (w_H Wc) (@YK11.mkst fxc regs3 (Z_to_bv 64 EXE_R2) mem3 (YK11.seg_rom rsegs)))).
{ apply (exe_st_r fxc Wc regs3 mem3 EXE_R2 (exv_s1 E) (e_q E) (frame_addr lyc 1 pos) (e_v E) (e_dl E)
           G9 G19 G24 G25); try lia.
  - apply MV; [lia | lia | exact C136].
  - apply MV; [lia | lia | exact S144].
  - apply MV; [lia | lia | exact S152].
  - exact Cq32m.
  - intros o Ho. apply (apresent_writable rsegs). apply HpresJ. lia. }
set (E3 := Ereg regs3 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) in HS.
assert (E10 : ew E3 10 = rv2) by (unfold E3; rewrite (ew_Ereg_nat regs3 _ 10 10%bv eq_refl); exact Hrv).
assert (E19 : ew E3 19 = Z_to_bv 64 (e_q E)) by (unfold E3; exact (exe_ew regs3 _ 19 19%bv _ eq_refl G19)).
assert (E25 : ew E3 25 = Z_to_bv 64 SHADOW_OFF) by (unfold E3; exact (exe_ew regs3 _ 25 25%bv _ eq_refl G25)).
assert (E33 : ew E3 33 = Z_to_bv 64 (e_dl E)) by (unfold E3; exact (ew_Ereg_extra regs3 _ 1)).
assert (U19 : bv_unsigned (ew E3 19) = e_q E) by (apply exe_U; [exact E19 | lia]).
assert (U25 : bv_unsigned (ew E3 25) = SHADOW_OFF) by (apply exe_U; [exact E25 | unfold SHADOW_OFF; lia]).
assert (AG3 : env_agree 32 (Ereg regs3 [Z_to_bv 64 (e_v E); Z_to_bv 64 (e_dl E)]) E3)
  by (unfold E3; apply env_agree_refl).
assert (SHOK : sh_ok rsegs EXE_SB exe_SHr E3 (rdW Wc mem3)).
{ unfold sh_ok, exe_SHr. constructor; [|constructor].
  apply (exe_shq (w_H Wc) mem3 E3 (e_q E) U19 U25); [lia | lia |].
  apply (exv_ra_keep (aview rsegs (w_H Wc) memc)); [| lia | lia | exact HQRA].
  intros s0 Hs0. apply HK3; lia. }
clearbody E3.
unfold cfg_at. change (w64 EXE_R2) with (Z_to_bv 64 EXE_R2).
pose (RUN := SRr_run_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
pose (RUNTO := SRr_run_to_tok_AJx (SK := SK) (fx := fxc) rsegs B prh_pst ARx LAWS B_prog_segs_low
  B_prog_tbl B_prog_tbl_ok B_prog_wx).
clear HJ.
exw_run RUN HS HJ3 SHOK.
{ exe_awr U19. }
exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
  ltac:(intros amn Hamn; cbv beta in Hamn; lia).
rename KEPT into K1. rename HG into G1. rename MNK into MN1. clear HF HFr.
exw_branch HS SHOK.
- (* bcmp = 0: the trees agree, in->differs is kept *)
  pose proof (exe_br_eq_t E3 10 rv2 E10 Hc) as Hrv0.
  pose proof (proj1 Hcmp Hrv0) as Heq.
  exw_run_to RUNTO HS HJ3 SHOK EXE_CD.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (RK : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs3 r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs3 _ exe_kept HS AG3
            ltac:(vm_compute; reflexivity) r Hr))
  end.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 13%bv HS) as R13.
  lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 13%bv) with (exe_shx 19 0) in R13 end.
  rewrite (exe_den_shx E3 19 0 (e_q E) E19 E25) in R13 by lia. rewrite Z.add_0_r in R13.
  cbn [ms_regs restrict] in R13.
  pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SOff 33 0) (e_dl E) RQ U19
    ltac:(left; reflexivity) ltac:(rewrite (exe_den_off E3 33 (e_dl E) 0 E33) by lia; rewrite Z.add_0_r; reflexivity)
    ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 (exv_pc EXN_CD)) by (vm_compute; reflexivity) end.
  eapply (exe_close fxc lyc Sc Hpc Wc regs memc mdc k c j bits _ _ _ _ (e_dl E) HPRE HCC).
  + exact HJ3.
  + intros z Hz Hw Hq. rewrite (K2 z Hz Hq), (K1 z Hz Hq). exact (HK3 z Hz Hw Hq).
  + intros a Ha. apply (apresent_grows (w_H Wc) _ _ a G2), (apresent_grows (w_H Wc) _ _ a G1), HG3, Ha.
  + intros Hm. exact (MN2 (MN1 (HMN3 Hm))).
  + intros r Hr. rewrite (RK r Hr). exact (HR3 r Hr).
  + exact R13.
  + exact VQ.
  + exact Hdl01.
  + split; [intros H1; left; exact H1 | intros [H1|(_ & Hne)]; [exact H1 | exfalso; exact (Hne Heq)]].
- (* bcmp <> 0: in->differs := 1 *)
  pose proof (exe_br_eq_f E3 10 rv2 E10 Hc) as Hrv0.
  assert (Hne : e_t E <> PjTree.JNum (exn_sub (e_x E) (EXN_i1 E) j) bits)
    by (intros Heq; exact (Hrv0 (proj2 Hcmp Heq))).
  exw_run_to RUNTO HS HJ3 SHOK EXE_CD.
  { exe_awr U19. }
  exw_kept_of HFr (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h).
  exe_mn_of HF (fun a => e_q E + 32 <= a < e_q E + 36) ltac:(fun h => rewrite ?U19 in h)
    ltac:(intros amn Hamn; cbv beta in Hamn; lia).
  rename KEPT into K2. rename HG into G2. rename MNK into MN2. clear HF HFr.
  lazymatch type of HS with
  | st_ok _ _ _ (restrict _ ?mx) =>
    assert (RK : forall r, In r exe_kept -> YK11.getr (ms_regs mx) r = YK11.getr regs3 r)
      by (intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs3 _ exe_kept HS AG3
            ltac:(vm_compute; reflexivity) r Hr))
  end.
  pose proof (st_ok_restrict_reg rsegs (w_H Wc) _ _ _ 13%bv HS) as R13.
  lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
    change (sr_get l 13%bv) with (exe_shx 19 0) in R13 end.
  rewrite (exe_den_shx E3 19 0 (e_q E) E19 E25) in R13 by lia. rewrite Z.add_0_r in R13.
  cbn [ms_regs restrict] in R13.
  pose proof (exw_region_nth rsegs _ _ _ 1%nat _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
  pose proof (exw_field rsegs _ _ 19%nat (e_q E) _ _ _ _ _ 32 4 (SLit 1) 1 RQ U19
    ltac:(left; reflexivity) ltac:(apply exe_den_lit; lia) ltac:(cbn; lia) ltac:(cbn; lia)) as VQ.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (@YK11.mkst ?f ?rg ?pc ?mm ?rom) ?md) _ =>
    replace pc with (w64 (exv_pc EXN_CD)) by (vm_compute; reflexivity) end.
  eapply (exe_close fxc lyc Sc Hpc Wc regs memc mdc k c j bits _ _ _ _ 1 HPRE HCC).
  + exact HJ3.
  + intros z Hz Hw Hq. rewrite (K2 z Hz Hq), (K1 z Hz Hq). exact (HK3 z Hz Hw Hq).
  + intros a Ha. apply (apresent_grows (w_H Wc) _ _ a G2), (apresent_grows (w_H Wc) _ _ a G1), HG3, Ha.
  + intros Hm. exact (MN2 (MN1 (HMN3 Hm))).
  + intros r Hr. rewrite (RK r Hr). exact (HR3 r Hr).
  + exact R13.
  + exact VQ.
  + right; reflexivity.
  + split; [intros _; right; split; [exact Hvn | exact Hne] | intros _; reflexivity].
Qed.

(* the tree root's num field lies in application memory (its home: a Lam block, a fake frame, the real stack) *)
Lemma exe_vamem : forall (fxc : YK11.FPState) lyc Sc Hpc Wc regs memc mdc k,
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos -> e_v E <> 0 ->
  amem_range (e_v E + 8) 8.
Proof using All.
intros fxc lyc Sc Hpc Wc regs memc mdc k HPRE HB Hvn.
pose proof asan_consts as (AC & _ & _ & _ & _). pose proof (@cf_head_nonneg cp) as CH0.
destruct (exe_geom B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB)
  as (HAR & _ & HSTK & _ & _ & Hsplo & Hspd & Hhi47 & Hcsp & Hlosp & Hclo & HS1 & _ & _ & Hspq & Hqd & _).
destruct (exe_vfacts B ARx SK HYP fxc E lyc Sc Hpc Wc regs memc mdc k pos HPRE HB Hvn)
  as (_ & Hhome & _ & _ & Hv4096 & Hv47 & _ & _).
pose proof HB as HB0. unfold EXB in HB0. cbv zeta in HB0.
destruct HB0 as (_ & _ & _ & _ & _ & _ & _ & HLED & _ & R2 & _).
destruct Hhome as [(b & kk & Hin & H1 & H2) | [(cid & pos' & Hin & H1 & H2) | (H1 & H2)]].
- pose proof HLED as (_ & _ & HBL & _). rewrite Forall_forall in HBL.
  destruct (HBL (b, kk) Hin) as (Hk0 & Hblk & _ & _ & _). cbn [fst snd] in *.
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hblk) as (_ & H4096 & _ & Happ & _).
  assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  apply exe_in_app_amem. apply (in_app_sub _ _ _ _ Happ); lia.
- destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ cid pos' HAR Hin) as (F2 & F3 & Happ).
  apply exe_in_app_amem. apply (in_app_sub _ _ _ _ Happ); lia.
- unfold spZ in H1. rewrite R2 in H1. unfold w64 in H1. rewrite unsigned_lit_small in H1 by lia.
  unfold amem_range, kHighMemBeg, kHighMemEnd. right. lia.
Qed.
End p.
