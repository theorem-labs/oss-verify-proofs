(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, unstripped twin bff8519b), ex_value piece 5
   (ev_number), SUB-PIECE E of S8aNumCut.v: ev_E_stmt, from the cut CC (+0x958, 0x83bfc) to the cut CD (+0x9e4,
   0x83c88). Code walked: +0x958 .. +0x9e0 (0x83bfc-0x83c84, 35 instructions); the four ASan report arms +0xc4c,
   +0xc5c, +0xd84, +0xd88 are absorbed by the engine (YCbn tok_load / slow_block), never visited.
     a0 := v (s1 + 104); v = 0 -> CD (in->differs kept).
     v <> 0: 4-byte check of v->type; type <> 3 -> +0x9c8.
     type = 3: 8-byte check of v + 16, s1 + 96's shadow byte (q + 24); __wrap_strcmp (v->str, in->scratch) at +0x9a8;
       non-zero -> +0x9c8; __wrap_bcmp (v + 8, fr + 64, 8) at +0x9c0; zero -> CD (kept).
     +0x9c8: 4-byte check of q + 32; in->differs := 1; CD.
   Engine: YSRrMemnorm.v's runner twins paj_run_x_inv / paj_run_to_x_inv (YC80x / YC1fPx's runs with an invariant P)
   over YCbqG's ajournal_x at the cut's float state fxc (the internal file PIECES.md house rule 4), P := YAkMemnorm.memnorm SEGS (laws
   srr_inv_laws_memnorm_k; the same body as YAkMemnorm.memnorm, by conversion); the two calls through YGcallMxmn.v's
   aj_strcmp_at_xrom / aj_bcmp_at_xm at fx := fxc, resumed with YC1fP's jafter_call_keep_pi. The cut CD is reached by
   applying KD; ev_mid is carried by lane M's ev_mid_cur_stmt.
   MEMNORM: ev_mid's last conjunct at CC (YAkMemnorm.memnorm SEGS mem) is the runs' start P (HPM); each run gives P
   of its end memory; each call's keep (MN.memnorm memT -> MN.memnorm mem2) takes it across the call; the memory at
   CD gets it from the last run, and MIDC takes it as its memnorm premise (evE_close). A branch keeps the state.
   READ-ONLY BYTES at the strcmp call (the xrom text's arodata_okP over pa_relro_lo / pa_relro_hi): evE_rod, from
   fpre's arodata_okP at the entry (ev_pre's first conjunct) carried to the cut's memory by the journal's image clause
   for a byte off the statics PST, and by the ledger for a static byte (MID's prh_ledger and ev_pre's have the same
   values, so each static's bytes are the entry's); evE_rod_move takes it to the call (the runs write nothing below
   alloc_ceiling).
   Generic in PA : PAImg A_prog_listing (entry fact Hent, PRW_pj_write.v's form), in PI, RL, cp, ci and the allocator
   relation ARx (LAWS : AR_laws_x at the head length cf_head).
   SECTION HYPOTHESES: LAWS, Hent, MIDC (lane M's ev_mid_cur_stmt), and two open facts the cut / interface / generic
   kit does not carry: CUTFIX_blk32 (sent to h-w6u-pre) and CUTFIX_blk_amem8 (the shared eh_blk_amem8: a live block
   is an amem_range8 region, which the strcmp row of the YGcallMx.v of record asks, YGcallMx.v:77-78, :160) (see
   each). CUTFIX_rom (rom bytes not owned / errno / statics, for the old rom_view premise) is deleted: the xrom text
   takes arodata_okP, which evE_rod derives with no image fact. The real stack's shadow is AR_laws_x's
   alx_zshadow_byte (evE_qra); a harness block's shadow and hull alx_hshadow at cf_head, its granule tail alx_blocks +
   alx_blocks_tail (evE_lam, evE_scrtail); the tree root's hull prhex_tree's hull conjunct (evE_vhull); the tree
   node's fields PRH_Reader.v's pj_nodeR (evE_tree). The bcmp's num-slot shadow byte is ev_CC's ev_fsh (57a154b9a2f).
   Rule 24: done for the piece (proof-index ex_value ex_number strtod checked_memcpy; R24CheckNum2 "NUM:
   CONFIRM"): no released file is Required and no released lemma is cited; the small byte / shadow lemmas below are
   restated here (FuzzStrdupB.v sd_* and S8aClose.v s8c_* shapes, not Required). CJ.Spec SoftFloat / FloatScan (the
   strtod model, already in S8aNumCut's closure through strtod_c.v) are Required for their definitions only
   (eve_f128_range: the strtod model's value is a 64-bit word, for the bcmp of the num slot).
   Numerals, classified (layer brief rule 4): ADDRESS: none. LENGTH: the offsets 0x958, 0x9e4 from ex_value's entry
   (the f0d2e8d4 listing, the same at #102); 24, 32, 36 (struct ex fields scratch / differs and its end); 96, 104, 112, 120, 128 (the
   s1 spills of shadow (q + 24), v, fr + 64, q + 24, and their end); 8, 16, 24 (struct pj num / str fields and the
   end of str); 64 (the frame's num slot); 56 (a pj node); 8 / 3 (the shadow granule and its log); 4, 8 (access
   widths); 272 (ev_img_ok's frame bound, S8aNumCut.v); 256 / 32 / 16 (ex_value's prologue `addi sp, sp, -256`,
   `andi sp, sp, -32`, the ABI's 16); 2 ^ 44, 2 ^ 47, 2 ^ 64, 2 ^ 32, 2 ^ 63 (the shadow band, the model's address
   bound, word ranges); 3 * 2 ^ 20 (ev_pre's input bound); 64 (the word width, R64's bits); 256 (a byte).
   DERIVED: 7364 (= slot 1841 * 4: ex_value's offset in A_prog_listing, PAImg_prog.v:431); 512 (A_LIM, the first atom
   above the image atoms, where the runner's shadow loads go); 128 / 16 (fs_frame_bytes 1 and its shadow bytes);
   9840 / 9864 (= 7364 + 0x9ac / 0x9c4, the call return sites); 0x7fff7f800000 (= YK06's alloc_ceiling, the lower
   bound of ASAN_CEIL); 16384 / 8192 / 4096 (STK_RT_STRTOD, 2 * ESTACK, ESTACK); 16656 (= 272 + 16384); 48 / 64
   (havoc bases above the extra atoms) and the atom indices of the symbolic state (2 sp, 3 gp, 4 tp, 9 s1, 18 s2,
   19 s3, 22 s6, 23 s7, 24 s8; 32 v, 33 scratch, 34 differs, 35 type, 36 str; 52 / 68 the a0 of each call, CLOB's
   fifth entry). WORD: 3 (PjTree.tag of JNum), 0 / 1 (NULL, the differs flag), 6 (the largest tag). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallMxmn YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Mem Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Listing_prog PAImg_prog PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Spec Require SoftFloat FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aNumCut S8aModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======== the symbolic states at CC (closed terms; vm_compute runs the engine over them) ======== *)

(* the listing offset of ex_value + off (DERIVED: slot 1841 * 4 = 7364) *)
Definition EVE_PC (off : Z) : Z := 7364 + off.
(* the shadow address of atom n + c as the instrumented code computes it: ((n + c) >> 3) + s8 *)
Definition shx (n : nat) (c : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff 24 0).
Definition EVE_Bx : sv := SOff 24 0.
Definition EVE_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition EVE_TOP : Z := 2 ^ 47 - 40.
Definition EVE_CEIL : Z := 0x7fff7f800000.
(* the s1 spills the piece reads: shadow (q + 24), v, fr + 64, q + 24 *)
Definition eve_Rs1 (vsv : sv) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 96 128 0 0
    [YP09.mkChunk 96 (CVal 8 (shx 19 24)); YP09.mkChunk 104 (CVal 8 vsv);
     YP09.mkChunk 112 (CVal 8 (SOff 18 64)); YP09.mkChunk 120 (CVal 8 (SOff 19 24))].
(* in->scratch (read) and in->differs (written) *)
Definition eve_Rq : YP09.region :=
  YP09.mkRegion (Some 19%nat) 24 36 32 36 [YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 4 (SOff 34 0))].
(* v's type and str (read) *)
Definition eve_Rv : YP09.region :=
  YP09.mkRegion (Some 32%nat) 0 24 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0)); YP09.mkChunk 16 (CVal 8 (SOff 36 0))].
Definition eve_atoms0 : list (nat * afact) :=
  [(9%nat, mkAF EVE_CEIL EVE_TOP 5); (19%nat, mkAF EVE_CEIL EVE_TOP 3); (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0)].
Definition eve_ssv : sstate :=
  mkSS (EVE_PC 0x958) sr_atoms [eve_Rs1 (SOff 32 0); eve_Rq; eve_Rv] None
    (mkFacts (eve_atoms0 ++ [(32%nat, mkAF 8 (2 ^ 47 - 56) 3); (35%nat, mkAF 0 6 0)])
       [mkAC BC_NE (SOff 32 0) (SLit 0)] []).
(* in->scratch and in->differs, both read-only: the v = 0 path stores nothing *)
Definition eve_Rq0 : YP09.region :=
  YP09.mkRegion (Some 19%nat) 24 36 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 33 0)); YP09.mkChunk 32 (CVal 4 (SOff 34 0))].
Definition eve_ss0 : sstate :=
  mkSS (EVE_PC 0x958) sr_atoms [eve_Rs1 (SLit 0); eve_Rq0] None (mkFacts eve_atoms0 [] []).
Definition eve_SH : list shent := [].

(* ======== pure lemmas ======== *)

Lemma eve_span_all : forall p (z a r : list Z), span p z = (a, r) -> Forall (fun x => p x = true) a.
Proof.
  intros p z. induction z as [|b z IH]; intros a r H; cbn [span] in H.
  - injection H as <- _. constructor.
  - destruct (p b) eqn:Hb.
    + destruct (span p z) as [a1 r1] eqn:E1. injection H as <- _. constructor; [exact Hb | exact (IH a1 r1 eq_refl)].
    + injection H as <- _. constructor.
Qed.

(* the number arm's text is number characters (fuzz_preset.c :224-229; PjGrammar.jr_number) *)
Lemma eve_N_numch : forall xs t bt r, ev_N xs = Some (JNum t bt, r) -> Forall (fun z => numch z = true) t.
Proof.
  intros xs t bt r. unfold ev_N.
  change (fst (fst (jr_number ReaderRes.jr_strtod xs []))) with (ev_run0 (jr_number ReaderRes.jr_strtod xs)).
  unfold jr_number. cbv beta iota zeta.
  match goal with |- context [skipn ?j xs] => set (J := j) end.
  assert (HJ : Forall (fun z => numch z = true) (firstn J xs)).
  { subst J. destruct xs as [|b0 xs']; cbn [firstn]; [constructor|].
    destruct (Z.eqb_spec b0 45) as [->|_]; cbn [firstn]; [constructor; [reflexivity | constructor] | constructor]. }
  destruct (skipn J xs) as [|c0 z] eqn:Ez; cbv beta iota; [intro H; discriminate H|].
  destruct (negb (digit c0)) eqn:Edc; cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c0 =? 48) && ?m then _ else _] => destruct ((c0 =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  destruct (span numch z) as [a0 r0] eqn:Es; cbv beta iota zeta.
  rewrite evm_run0_alloc.
  match goal with |- context [whole ReaderRes.jr_strtod ?tt] => destruct (whole ReaderRes.jr_strtod tt) end;
    cbv beta iota; intro H; [|discriminate H].
  rewrite evm_run0_ret in H. injection H as <- _ _.
  apply Forall_app. split; [exact HJ|]. constructor.
  - apply negb_false_iff in Edc. unfold numch. rewrite Edc. reflexivity.
  - exact (eve_span_all numch z a0 r0 Es).
Qed.

Lemma eve_numch_nz : forall z, numch z = true -> 0 < z < 256.
Proof.
  intros z H. unfold numch, digit in H.
  repeat (apply orb_prop in H; destruct H as [H|H]); try (apply Z.eqb_eq in H; lia).
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(* ---- the strtod model's bit pattern is a 64-bit word (SoftFloat.f128_to_d packs 64-bit fields) ---- *)
Definition R64 (x : Z) : Prop := 0 <= x < 2 ^ 64.
Lemma eve_R_bits : forall x, 0 <= x -> (forall i, 64 <= i -> Z.testbit x i = false) -> R64 x.
Proof.
  intros x Hx H. split; [exact Hx|]. destruct (Z.lt_ge_cases x (2 ^ 64)) as [h|h]; [exact h|].
  exfalso. assert (Hl : 64 <= Z.log2 x).
  { rewrite <- (Z.log2_pow2 64) by lia. apply Z.log2_le_mono. exact h. }
  pose proof (Z.bit_log2 x ltac:(lia)) as Hb. rewrite (H _ Hl) in Hb. discriminate.
Qed.
Lemma eve_R_hi : forall x i, R64 x -> 64 <= i -> Z.testbit x i = false.
Proof.
  intros x i [H0 H1] Hi. destruct (Z.eq_dec x 0) as [->|Hn]; [apply Z.bits_0|].
  apply Z.bits_above_log2; [lia|]. apply (proj1 (Z.log2_lt_pow2 x i ltac:(lia))).
  apply Z.lt_le_trans with (2 ^ 64); [lia | apply Z.pow_le_mono_r; lia].
Qed.
Lemma eve_R_wrap : forall x, R64 (SoftFloat.wrap64 x).
Proof.
  intros x. unfold R64, SoftFloat.wrap64. change SoftFloat.ONES64 with (Z.ones 64).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.
Lemma eve_R_lor : forall a b, R64 a -> R64 b -> R64 (Z.lor a b).
Proof.
  intros a b Ha Hb. apply eve_R_bits; [apply (proj2 (Z.lor_nonneg a b)); split; [exact (proj1 Ha) | exact (proj1 Hb)]|].
  intros i Hi. rewrite Z.lor_spec, (eve_R_hi a i Ha Hi), (eve_R_hi b i Hb Hi). reflexivity.
Qed.
Lemma eve_R_lxor : forall a b, R64 a -> R64 b -> R64 (Z.lxor a b).
Proof.
  intros a b Ha Hb. apply eve_R_bits.
  - apply (proj2 (Z.lxor_nonneg a b)). split; intros _; [exact (proj1 Hb) | exact (proj1 Ha)].
  - intros i Hi. rewrite Z.lxor_spec, (eve_R_hi a i Ha Hi), (eve_R_hi b i Hb Hi). reflexivity.
Qed.
Lemma eve_R_land1 : forall a b, R64 a -> 0 <= b -> R64 (Z.land a b).
Proof.
  intros a b Ha Hb. apply eve_R_bits; [apply (proj2 (Z.land_nonneg a b)); left; exact (proj1 Ha)|].
  intros i Hi. rewrite Z.land_spec, (eve_R_hi a i Ha Hi). reflexivity.
Qed.
Lemma eve_R_land2 : forall a b, 0 <= a -> R64 b -> R64 (Z.land a b).
Proof. intros a b Ha Hb. rewrite Z.land_comm. apply eve_R_land1; assumption. Qed.
Lemma eve_R_shr : forall a n, R64 a -> 0 <= n -> R64 (Z.shiftr a n).
Proof.
  intros a n Ha Hn. apply eve_R_bits; [apply (proj2 (Z.shiftr_nonneg a n)); exact (proj1 Ha)|].
  intros i Hi. rewrite Z.shiftr_spec by lia. apply eve_R_hi; [exact Ha | lia].
Qed.
Lemma eve_R_b2z : forall b, R64 (SoftFloat.b2z b).
Proof. intros [|]; unfold R64, SoftFloat.b2z; lia. Qed.
Lemma eve_R_sra : forall x, R64 (SoftFloat.sra63 x).
Proof. intros x. unfold SoftFloat.sra63. destruct (SoftFloat.is_neg64 x); unfold R64, SoftFloat.ONES64; lia. Qed.
Lemma eve_R_tr : forall s r, R64 s -> R64 (SoftFloat.trunc_round s r).
Proof.
  intros s r Hs. unfold SoftFloat.trunc_round.
  destruct (negb _); [apply eve_R_wrap|]. destruct (negb _); [apply eve_R_wrap | exact Hs].
Qed.
Ltac eve_nonneg :=
  first [ lia
        | apply (proj2 (Z.land_nonneg _ _)); right; lia
        | refine (proj1 (_ : R64 _)); eve_rtac ]
with eve_rtac :=
  lazymatch goal with
  | |- R64 (Z.lor _ _) => apply eve_R_lor; eve_rtac
  | |- R64 (Z.lxor _ _) => apply eve_R_lxor; eve_rtac
  | |- R64 (Z.land _ _) =>
      first [ apply eve_R_land1; [eve_rtac | eve_nonneg] | apply eve_R_land2; [eve_nonneg | eve_rtac] ]
  | |- R64 (Z.shiftr _ _) => apply eve_R_shr; [eve_rtac | eve_nonneg]
  | |- R64 (SoftFloat.trunc_round _ _) => apply eve_R_tr; eve_rtac
  | |- R64 (SoftFloat.b2z _) => apply eve_R_b2z
  | |- R64 (SoftFloat.nez64 _) => apply eve_R_b2z
  | |- R64 (SoftFloat.eqz64 _) => apply eve_R_b2z
  | |- R64 (SoftFloat.sra63 _) => apply eve_R_sra
  | |- R64 (SoftFloat.shl64 _ _) => apply eve_R_wrap
  | |- R64 (SoftFloat.add64 _ _) => apply eve_R_wrap
  | |- R64 (SoftFloat.sub64 _ _) => apply eve_R_wrap
  | |- R64 (SoftFloat.wrap64 _) => apply eve_R_wrap
  | |- R64 (SoftFloat.lo64 _) => apply eve_R_wrap
  | |- R64 (SoftFloat.hi64 _) => apply eve_R_wrap
  | |- R64 _ => unfold R64, SoftFloat.DQUIET; lia
  end.
Lemma eve_f128_range : forall y, R64 (SoftFloat.f128_to_d y).
Proof.
  intros y. unfold SoftFloat.f128_to_d. cbv zeta.
  match goal with |- context [match ?E with pair _ _ => _ end] => destruct E as [dE dS] eqn:Ep end.
  assert (HdS : R64 dS).
  { repeat match type of Ep with context [if ?c then _ else _] => destruct c end;
    injection Ep as _ <-; eve_rtac. }
  apply eve_R_lor; [apply eve_R_lor; [apply eve_R_wrap | eve_rtac] | exact HdS].
Qed.
Lemma eve_jr_strtod_bits : forall t, 0 <= snd (ReaderRes.jr_strtod t) < 2 ^ 64.
Proof.
  intros t. unfold ReaderRes.jr_strtod, strtod_c.strtod_model, FloatScan.scan_strtod. cbv zeta.
  match goal with |- context [FloatScan.floatscan ?a ?b ?c ?d] =>
    destruct (FloatScan.floatscan a b c d) as [[f y]|] end; cbv beta iota; cbn [snd fst];
  [apply eve_f128_range | lia].
Qed.
(* the number arm's value is a 64-bit word *)
Lemma eve_N_bits : forall xs t bt r, ev_N xs = Some (JNum t bt, r) -> 0 <= bt < 2 ^ 64.
Proof.
  intros xs t bt r. unfold ev_N.
  change (fst (fst (jr_number ReaderRes.jr_strtod xs []))) with (ev_run0 (jr_number ReaderRes.jr_strtod xs)).
  unfold jr_number. cbv beta iota zeta.
  match goal with |- context [skipn ?j xs] => set (J := j) end.
  destruct (skipn J xs) as [|c0 z] eqn:Ez; cbv beta iota; [intro H; discriminate H|].
  destruct (negb (digit c0)) eqn:Edc; cbv beta iota; [intro H; discriminate H|].
  match goal with |- context [if (c0 =? 48) && ?m then _ else _] => destruct ((c0 =? 48) && m) end;
    cbv beta iota; [intro H; discriminate H|].
  destruct (span numch z) as [a0 r0] eqn:Es; cbv beta iota zeta.
  rewrite evm_run0_alloc.
  match goal with |- context [whole ReaderRes.jr_strtod ?tt] => destruct (whole ReaderRes.jr_strtod tt) end;
    cbv beta iota; intro H; [|discriminate H].
  rewrite evm_run0_ret in H. injection H as _ <- _.
  apply eve_jr_strtod_bits.
Qed.

(* ---- 8-byte words compare bytewise exactly when they are equal ---- *)
Lemma eve_le_inj : forall b1 b2, 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
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
  - rewrite (eve_R_hi b1 t H1 Hge), (eve_R_hi b2 t H2 Hge). reflexivity.
Qed.

Lemma eve_nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth_error]. rewrite IH by lia. f_equal. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Section bytes.
Variable segs : list Segment.

(* the plain representation's little-endian field at a as a val_mem cell *)
Lemma eve_le_val : forall m a (n : nat) v, (n <= 8)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) ->
  Lib.Mem.bytes_at segs m a (Z_to_le_bytes n v) -> val_mem segs m a n v.
Proof.
  intros m a n v Hn Hv (_ & _ & H) k Hk.
  rewrite length_Z_to_le_bytes in H. specialize (H k Hk).
  change (mbyte segs m (a + Z.of_nat k)) with (Lib.Mem.mrd segs m (Lib.Mem.wa (a + Z.of_nat k))).
  rewrite H, eve_nth_le_bytes by exact Hk. f_equal. symmetry. apply le_byte_small; [exact Hv | exact Hk].
Qed.

Lemma eve_val_le : forall m a (n : nat) v, (n <= 8)%nat -> 0 <= v < 2 ^ (8 * Z.of_nat n) -> 0 <= a ->
  a + Z.of_nat n <= 2 ^ 64 -> val_mem segs m a n v -> Lib.Mem.bytes_at segs m a (Z_to_le_bytes n v).
Proof.
  intros m a n v Hn Hv Ha Han H. split; [exact Ha|]. rewrite length_Z_to_le_bytes. split; [exact Han|].
  intros k Hk. change (Lib.Mem.mrd segs m (Lib.Mem.wa (a + Z.of_nat k))) with (mbyte segs m (a + Z.of_nat k)).
  rewrite (H k Hk), eve_nth_le_bytes by exact Hk. f_equal. apply le_byte_small; [exact Hv | exact Hk].
Qed.

Lemma eve_u32_val : forall m a v, PjStruct.pj_u32 segs m a v -> val_mem segs m a 4 v.
Proof.
  intros m a v (Hv & Hb). apply eve_le_val; [lia | cbn; lia |].
  replace (Z_to_le_bytes 4 v) with (Lib.Mem.le4 (Z_to_bv 64 v)); [exact Hb|].
  unfold Lib.Mem.le4. f_equal. apply unsigned_lit_small. lia.
Qed.

Lemma eve_u64_val : forall m a v, PjStruct.pj_u64 segs m a v -> val_mem segs m a 8 v.
Proof.
  intros m a v (Hv & Hb). apply eve_le_val; [lia | cbn; lia |].
  replace (Z_to_le_bytes 8 v) with (Lib.Mem.le8 (Z_to_bv 64 v)); [exact Hb|].
  unfold Lib.Mem.le8, word_to_le_bytes. f_equal. apply unsigned_lit_small. lia.
Qed.

Lemma eve_val_u64 : forall m a v, 0 <= v < 2 ^ 64 -> 0 <= a -> a + 8 <= 2 ^ 64 -> val_mem segs m a 8 v ->
  PjStruct.pj_u64 segs m a v.
Proof.
  intros m a v Hv Ha Han H. split; [exact Hv|].
  apply eve_val_le; [lia | rewrite unsigned_lit_small by lia; cbn; lia | exact Ha | cbn; lia |
    rewrite unsigned_lit_small by lia; exact H].
Qed.

(* a C string of the plain representation as a byte array *)
Lemma eve_cbytes_garr : forall m a s, PjStruct.pj_cbytes segs m a s ->
  garr8 segs m a (s ++ [0]) /\ Forall (fun c => c <> 0) s.
Proof.
  intros m a s (Hs & _ & _ & Hb). split.
  - intros jj Hj. rewrite length_map in Hb.
    assert (Hn : 0 <= nth jj (s ++ [0]) 0 < 256).
    { rewrite length_app in Hj. cbn [length] in Hj. destruct (Nat.lt_ge_cases jj (length s)) as [Hl|Hl].
      - rewrite app_nth1 by exact Hl. pose proof (proj1 (Forall_forall _ _) Hs (nth jj s 0) (nth_In s 0 Hl)) as Hc.
        cbv beta in Hc. lia.
      - rewrite app_nth2 by exact Hl. replace (jj - length s)%nat with 0%nat by lia. cbn. lia. }
    split; [|exact Hn]. intros kk Hk. assert (kk = 0%nat) by lia. subst kk. cbn [Z.of_nat]. rewrite Z.add_0_r.
    pose proof (Hb jj Hj) as Hb'.
    assert (Hmap : nth_error (map (Z_to_bv 8) (s ++ [0])) jj = Some (Z_to_bv 8 (nth jj (s ++ [0]) 0))).
    { apply (map_nth_error (Z_to_bv 8) jj (s ++ [0])).
      apply nth_error_nth'. exact Hj. }
    rewrite Hmap in Hb'.
    assert (Heq : Z_to_bv 8 (nth jj (s ++ [0]) 0) = Z_to_bv 8 (YG0f.le_byte (nth jj (s ++ [0]) 0) 1 0)).
    { apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YG0f.le_byte, bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 8) with 256. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
      rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. reflexivity. }
    rewrite Heq in Hb'. exact Hb'.
  - eapply Forall_impl; [|exact Hs]. intros c Hc. cbv beta in Hc |- *. lia.
Qed.
End bytes.

Section bview. Context {rc : YM05.RunCeil}.
Variable segs : list Segment.
Lemma eve_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros jj Hj. change 256 with (2 ^ 8). rewrite !Z.testbit_mod_pow2 by lia.
destruct (jj <? 8) eqn:Ej; [|reflexivity]. apply Z.ltb_lt in Ej.
rewrite !Z.shiftr_spec by lia. rewrite !Z.testbit_mod_pow2 by lia.
replace (jj + 8 * Z.of_nat k <? 8 * Z.of_nat n) with true by (symmetry; apply Z.ltb_lt; nia).
replace (jj + 8 * Z.of_nat k <? 64) with true by (symmetry; apply Z.ltb_lt; nia). reflexivity.
Qed.

Lemma eve_chunk_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem segs m (base + off) (N.to_nat w) v -> YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply eve_byte_eq; lia.
Qed.
Lemma eve_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok segs E m base (YP09.mkChunk off (CVal w e)) ->
  val_mem segs m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (eve_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.

Lemma eve_garr8_aview : forall (H : word -> bool) m p l j, garr8 segs (mrestrict H m) p l -> (j < length l)%nat ->
  aview segs H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
  intros H m p l j Hg Hj. unfold aview. rewrite (garr8_mbyte segs _ p l j Hg Hj). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. exact (proj2 (Hg j Hj)).
Qed.
Lemma eve_first_byte : forall (W : world segs) m p l, garr8 segs (mrestrict (w_H W) m) p (l ++ [0]) ->
  Forall (fun c => c <> 0) l -> first_byte segs W m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
  intros W m p l Hg Hnz. split; [lia|]. split.
  - intros i Hi. exists (nth (Z.to_nat i) l 0). split.
    + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
      rewrite (eve_garr8_aview (w_H W) m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
      rewrite app_nth1 by lia. reflexivity.
    + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
  - intros _. rewrite (eve_garr8_aview (w_H W) m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma eve_src_ok : forall (W : world segs) regs m p l, garr8 segs (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok segs W regs m p (Z.of_nat (length l)).
Proof.
  intros W regs m p l Hg Hw a Ha. split; [|exact (Hw a Ha)].
  replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
  rewrite (eve_garr8_aview (w_H W) m p l (Z.to_nat (a - p)) Hg) by lia. discriminate.
Qed.
Lemma eve_hull_sub : forall (rd : reader) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm -> 0 < n ->
  shadow_hull_vis rd d n.
Proof.
  intros rd p mm d n Hh Hpd Hdn Hn s Hs. apply Hh.
  pose proof (shadow_mono p d Hpd) as M1. pose proof (shadow_mono (d + n - 1) (p + mm - 1) ltac:(lia)) as M2.
  assert (R8 : forall u v, u <= v -> u / 8 * 8 <= v / 8 * 8)
    by (intros u v Huv; apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.div_le_mono; lia).
  pose proof (R8 _ _ M1). pose proof (R8 _ _ M2). lia.
Qed.
Lemma eve_aview_mbyte : forall (H : word -> bool) m m' a, aview segs H m' a = aview segs H m a ->
  mbyte segs (mrestrict H m') a = mbyte segs (mrestrict H m) a.
Proof. intros H m m' a E. exact (mbyte_of_aview segs H H m m' a E). Qed.
Lemma eve_val_move : forall (H : word -> bool) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H m') a n v.
Proof.
  intros H m m' a n v HA Hv k Hk. rewrite (eve_aview_mbyte H m m' (a + Z.of_nat k)) by (apply HA; lia). exact (Hv k Hk).
Qed.
Lemma eve_garr_move : forall (H : word -> bool) m m' a l,
  (forall i, 0 <= i < Z.of_nat (length l) -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
  garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H m') a l.
Proof.
  intros H m m' a l HA Hg jj Hj. destruct (Hg jj Hj) as [Hv Hr]. split; [|exact Hr].
  apply (eve_val_move H m m'); [|exact Hv]. intros i Hi. rewrite <- Z.add_assoc. apply HA. lia.
Qed.
Lemma eve_ra_move : forall (H : word -> bool) m m' a n, 0 <= a -> a + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> aview segs H m' s = aview segs H m s) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H m') SHADOW_OFF a n.
Proof.
  intros H m m' a n Ha Hn HA Hr. apply (range_addressable_agree (aview segs H m)); [|exact Hr].
  intros x Hx. unfold shadow_of_addr. pose proof alloc_ceiling_value as [C1 _].
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply HA. unfold SHADOW_OFF in *. lia.
Qed.
Lemma eve_hull_move : forall (H : word -> bool) m m' a n, 0 <= a -> 0 < n -> a + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> aview segs H m' s = aview segs H m s) ->
  shadow_hull_vis (aview segs H m) a n -> shadow_hull_vis (aview segs H m') a n.
Proof.
  intros H m m' a n Ha Hn Han HA Hh s Hs. pose proof alloc_ceiling_value as [C1 _].
  unfold shadow_addr in Hs.
  assert (0 <= (a + n - 1) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (0 <= a / 8) by (apply Z.div_pos; lia).
  assert (0 <= (SHADOW_OFF + a / 8) / 8 * 8) by (unfold SHADOW_OFF; pose proof (Z.div_pos (2147450880 + a / 8) 8); lia).
  assert ((SHADOW_OFF + (a + n - 1) / 8) / 8 * 8 <= SHADOW_OFF + (a + n - 1) / 8)
    by (pose proof (Z.mul_div_le (SHADOW_OFF + (a + n - 1) / 8) 8); lia).
  rewrite HA; [exact (Hh s Hs)|]. unfold SHADOW_OFF in *. lia.
Qed.
Lemma eve_apresent_aview : forall (H : word -> bool) m a, apresent H m a -> aview segs H m a <> None.
Proof.
  intros H m a (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
Qed.
Lemma eve_val8_aview : forall (H : word -> bool) m p b k, val_mem segs (mrestrict H m) p 8 b -> (k < 8)%nat ->
  aview segs H m (p + Z.of_nat k) = Some (YG0f.le_byte b 8 k).
Proof.
  intros H m p b k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
  apply Z.mod_small. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma eve_bytes_eq8 : forall (H : word -> bool) m p1 p2 b1 b2, 0 <= b1 < 2 ^ 64 -> 0 <= b2 < 2 ^ 64 ->
  val_mem segs (mrestrict H m) p1 8 b1 -> val_mem segs (mrestrict H m) p2 8 b2 ->
  ((forall i, 0 <= i < 8 -> aview segs H m (p1 + i) = aview segs H m (p2 + i)) <-> b1 = b2).
Proof.
  intros H m p1 p2 b1 b2 R1 R2 V1 V2. split.
  - intros Heq. apply eve_le_inj; [exact R1 | exact R2|]. intros k Hk.
    pose proof (Heq (Z.of_nat k) ltac:(lia)) as E.
    rewrite (eve_val8_aview H m p1 b1 k V1 Hk), (eve_val8_aview H m p2 b2 k V2 Hk) in E.
    injection E as E. exact E.
  - intros <- i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (eve_val8_aview H m p1 b1 _ V1), (eve_val8_aview H m p2 b1 _ V2) by lia. reflexivity.
Qed.
Lemma eve_str_eq : forall (H : word -> bool) m p1 p2 l1 l2,
  garr8 segs (mrestrict H m) p1 (l1 ++ [0]) -> garr8 segs (mrestrict H m) p2 (l2 ++ [0]) ->
  ((Z.of_nat (length l1) = Z.of_nat (length l2) /\
    forall i, 0 <= i < Z.of_nat (length l1) -> aview segs H m (p1 + i) = aview segs H m (p2 + i)) <-> l1 = l2).
Proof.
  intros H m p1 p2 l1 l2 G1 G2. split.
  - intros (Hl & Heq). apply (nth_ext l1 l2 0 0); [lia|]. intros jj Hj.
    pose proof (Heq (Z.of_nat jj) ltac:(lia)) as E.
    rewrite (eve_garr8_aview H m p1 (l1 ++ [0]) jj G1) in E by (rewrite length_app; cbn; lia).
    rewrite (eve_garr8_aview H m p2 (l2 ++ [0]) jj G2) in E by (rewrite length_app; cbn; lia).
    rewrite app_nth1 in E by lia. rewrite app_nth1 in E by lia. injection E as E. exact E.
  - intros <-. split; [reflexivity|]. intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    rewrite (eve_garr8_aview H m p1 (l1 ++ [0]) _ G1), (eve_garr8_aview H m p2 (l1 ++ [0]) _ G2)
      by (rewrite length_app; cbn; lia). reflexivity.
Qed.
Lemma eve_in_app_amem : forall lo len, in_app lo len -> amem_range lo len.
Proof.
  intros lo len H. pose proof alloc_ceiling_value as [C1 C2].
  unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
End bview.

(* sv denotations *)
Lemma eve_den_off : forall E n x c, bv_unsigned (ew E n) = x -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
  intros E n x c H. apply bv_eq. change (bv_unsigned (sv_denot E (SOff n c))) with (U E (SOff n c)).
  rewrite U_SOff, H. rewrite Z_to_bv_unsigned. reflexivity.
Qed.
Lemma eve_U_off : forall E n x c, bv_unsigned (ew E n) = x -> 0 <= x + c < 2 ^ 64 -> U E (SOff n c) = x + c.
Proof. intros E n x c H Hc. rewrite U_SOff, H. apply zcanon_id. unfold M64. lia. Qed.
Lemma eve_den_shx : forall E n c x, bv_unsigned (ew E n) = x -> 0 <= x + c < 2 ^ 64 ->
  bv_unsigned (ew E 24) = SHADOW_OFF -> sv_denot E (shx n c) = Z_to_bv 64 (shadow_addr (x + c)).
Proof.
  intros E n c x Hn Hxc H24. apply bv_eq.
  change (bv_unsigned (sv_denot E (shx n c))) with (U E (shx n c)). unfold shx.
  rewrite !U_SAlu, (eve_U_off E n x c Hn Hxc), U_SLit, (eve_U_off E 24 SHADOW_OFF 0 H24) by (unfold SHADOW_OFF; lia).
  cbn [zalu_raw]. change (zcanon 3) with 3. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ 3) with 8. rewrite Z_to_bv_unsigned. unfold bv_wrap, zcanon, M64, shadow_addr, SHADOW_OFF.
  change (bv_modulus 64) with (2 ^ 64).
  assert (0 <= (x + c) / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (Z.mod_small ((x + c) / 8)) by lia. rewrite Z.mod_small by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma evE_zmaxl_ge : forall l z, In z l -> z <= zmaxl l.
Proof.
  induction l as [|x l IH]; intros z Hin; cbn [zmaxl fold_right] in *; [contradiction|].
  destruct Hin as [->|Hin]; [apply Z.le_max_l|].
  eapply Z.le_trans; [apply IH; exact Hin | apply Z.le_max_r].
Qed.

(* ======== the walk ======== *)

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {PA : PAImg A_prog_listing}.
Local Notation SEGS := (@pa_segs _ A_prog_listing PA).
Local Notation VAL := (@pa_val _ A_prog_listing PA).
Local Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
Local Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
Local Notation PST := (@prh_pst PI).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Local Notation EVPRE := (@ev_pre fx rc cp PI A_prog_listing PA B ARx).
Local Notation EVMID := (@ev_mid rc cp PI RL A_prog_listing PA B ARx SK).
Local Notation EVCC := (@ev_CC rc cp PI RL A_prog_listing PA B ARx SK).
Local Notation EVCD := (@ev_CD rc cp PI RL A_prog_listing PA B ARx SK).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the kit's allocator laws at ARx; the head length of a harness block is cf_head (alx_hshadow is used at it) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* image fact of the instance, discharged at PI_prog_A by A_entry_ex_value (slot 1841) *)
Hypothesis Hent : SIGMA AS_ex_value = BASE + 7364.
(* lane M: ev_mid across the piece's own writes, with in->p / in->differs rewritten *)
Hypothesis MIDC : forall a, ev_mid_cur_stmt B ARx SK a.

(* ---- the open facts (see the file header) ---- *)
(* CUTFIX_blk32: a live block's size fits strcmp's int (astrcmp_realizes_x's `kx + 1 < 2 ^ 32` for v->str);
   ARcf's AR_blocks_law_cf gives `0 <= n < cf_malloc_max`, 2 ^ 29 - 2 ^ 20 at the preset (CfParamsPreset.v:7). *)
Hypothesis CUTFIX_blk32 : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 32.
(* CUTFIX_blk_amem8: a live block is a region of the string rows' amem_range8 (the shared text: lib/B/Prog/ExvB_Stmt.v
   eh_blk_amem8, origin/cold/h-rw-pre-7-b-ex_value, MARKED, owner h-mani-a8 / c-omx-alloc). CAUSE: the YGcallMx.v of
   record (c208cc03b35) states the strcmp row over amem_range8 (YGcallMx.v:77-78; astrcmp_realizes_x
   `amem_range8 x (kx + 1)` / `amem_range8 y (ky + 1)`, YGcallMx.v:160), for v->str and the scratch at +0x9a8. No ARx
   law gives it: alx_blocks (YCbqG.v:43) gives only in_app p (req_size n), whose high arm is `kHighMemBeg <= p`
   (YG0f.v:277), and at a generic cp a block based at kHighMemBeg meets every AR_laws_x field (v->str's block when
   cf_head = 0; the scratch's block when its base is not in Hp). A sub-range with the same end inherits it
   (evE_amr8). *)
Hypothesis CUTFIX_blk_amem8 : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> YGcallMx.amem_range8 p (req_size n).

(* ---- the numbers of one activation at the cut ---- *)
Lemma evE_num : forall a ly S Hp W mem md k p dep dl,
  ev_img_ok -> EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  ARx ly S Hp W mem md /\
  ly_stk_lo ly = ly_stk_lo (ea_ly a) /\ ly_stk_hi ly = ly_stk_hi (ea_ly a) /\
  16656 <= ea_STK a /\ 0 <= ea_d a /\ ea_d a mod 16 = 0 /\
  256 <= ea_sp0 a - ea_S1 a <= 272 /\ ea_S1 a mod 32 = 0 /\ ea_sp0 a mod 16 = 0 /\
  alloc_ceiling + 16384 <= ea_S1 a /\ ea_S1 a + 272 <= 2 ^ 47 /\
  alloc_ceiling <= ea_q a /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\
  ea_sp0 a + ea_d a <= ly_stk_hi ly /\ ly_stk_hi ly <= 2 ^ 47 /\ ea_q a mod 8 = 0 /\
  ly_stk_lo ly + ea_STK a <= ea_sp0 a /\
  In (1, ea_pos a) (frames S) /\ frame_addr ly 1 (ea_pos a) = ea_fr a /\
  4096 <= ea_fr a /\ ea_fr a + 128 <= alloc_ceiling /\
  (ea_v a <> 0 -> 4096 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47 /\ ea_v a mod 8 = 0).
Proof.
intros a ly S Hp W mem md k p dep dl HIMG HPRE HMID.
pose proof alloc_ceiling_value as [HCV HCM].
pose proof HPRE as HPRE'. unfold ev_pre in HPRE'. cbv zeta in HPRE'.
destruct HPRE' as ((HFPRE & HROD & _) & Hfrm0 & Hcnt & Ha0 & Ha1 & Hcur0 & Hq8 & Hchap & Hq1 & Hq2 & Hfwin & Hsrc0 &
  Hinblk0 & Hlen3 & Hi0 & Hdep & Hdepn & Hdl01 & Hwd0 & Hinblkscr & Hsep1 & Hsep2 & Hvt & HLED0).
destruct HFPRE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
destruct Hstk0 as (Hal16 & HSTK0 & Hclo & Hlosp & Hsphi & H47 & Hbot & Htop & Htop2).
destruct Hfwin as (Hd0 & Hd16 & Hdtop & Hdpres).
assert (Esp : spZ (ea_regs a) = ea_sp0 a) by reflexivity.
rewrite Esp in Hal16, Hlosp, Hsphi, Hbot, Htop, Hpres0, Hq1, Hq2, Hdtop, Hdpres.
destruct HMID as (HJ & Hwin & HHp & Hbl & HLED & Hcur & Hsrc & Hwd & Htree & Hsav & Hflag & Hroom).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk0 & Hhi9 & Hbk & Him & Hfrk & Hgone & HpresJ &
  Hstatic & Hextra & HQT).
destruct Hly as (_ & _ & _ & _ & _ & HFly & _ & _ & _ & Hlylo & Hlyhi & _).
assert (HSTK : 16656 <= ea_STK a).
{ unfold ea_STK, STK_ex_value. unfold ev_img_ok in HIMG.
  assert (HZ : 16384 <= zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]).
  { replace 16384 with STK_RT_STRTOD by reflexivity. apply evE_zmaxl_ge. right; right; left; reflexivity. }
  remember (zmaxl [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]) as MX eqn:EMX.
  clear EMX.
  assert (HP : 0 <= pi_frame F_ex_value) by lia.
  assert (HN : 1 <= Z.of_nat (Nat.succ (ea_n a)))
    by (rewrite Nat2Z.inj_succ; pose proof (Zle_0_nat (ea_n a)); lia).
  pose proof (Z.mul_le_mono_nonneg_r 1 (Z.of_nat (Nat.succ (ea_n a))) (pi_frame F_ex_value) HP HN) as Hmm.
  rewrite Z.mul_1_l in Hmm. clear - HIMG Hmm HZ. lia. }
assert (HS1 : 256 <= ea_sp0 a - ea_S1 a <= 272 /\ ea_S1 a mod 32 = 0).
{ unfold ea_S1, ea_SA. pose proof (Z.mod_pos_bound (ea_sp0 a - 256) 32 ltac:(lia)) as Hm.
  assert (Hm16 : (ea_sp0 a - 256) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  assert (Hcase : (ea_sp0 a - 256) mod 32 = 0 \/ (ea_sp0 a - 256) mod 32 = 16).
  { pose proof (Z.div_mod (ea_sp0 a - 256) 32 ltac:(lia)) as E32.
    pose proof (Z.div_mod (ea_sp0 a - 256) 16 ltac:(lia)) as E16. lia. }
  destruct Hcase as [Hc|Hc]; rewrite Hc.
  - split; [lia|]. replace (ea_sp0 a - 256 - 0) with (ea_sp0 a - 256) by lia. exact Hc.
  - split; [lia|]. rewrite Zminus_mod, Hc. reflexivity. }
assert (HFR : frame_addr ly 1 (ea_pos a) = ea_fr a)
  by (unfold ea_fr, frame_addr; rewrite HFly; reflexivity).
assert (HIN1 : In (1, ea_pos a) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (HFRB : 4096 <= ea_fr a /\ ea_fr a + 128 <= alloc_ceiling).
{ destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hall).
  pose proof (proj1 (Forall_forall _ _) Hall (1, ea_pos a) HIN1) as Hf. cbv beta in Hf. cbn [fst snd] in Hf.
  change (fs_frame_bytes 1) with 128 in Hf. rewrite HFR in Hf. lia. }
split; [exact HAR|]. split; [exact Hlylo|]. split; [exact Hlyhi|].
split; [exact HSTK|]. split; [exact Hd0|]. split; [exact Hd16|].
split; [exact (proj1 HS1)|]. split; [exact (proj2 HS1)|]. split; [exact Hal16|].
split; [lia|]. split; [lia|].
split; [lia|]. split; [exact Hq1|]. split; [exact Hq2|].
split; [rewrite Hlyhi; lia|]. split; [rewrite Hlyhi; exact H47|]. split; [exact Hq8|].
split; [rewrite Hlylo; exact Hlosp|].
split; [exact HIN1|]. split; [exact HFR|]. split; [exact (proj1 HFRB)|]. split; [exact (proj2 HFRB)|].
intros Hv0. destruct Htree as [Hz|Htr]; [contradiction|].
destruct Htr as (Hpj & Hhome & Hra & Hhull).
assert (Hal8 : ea_v a mod 8 = 0).
{ destruct (ea_t a) as [| | |t1 c1|s1|l1|m1]; cbn [PRH_Reader.pj_nodeR] in Hpj;
  destruct Hpj as (_ & _ & nm & st & kd & ky & nn & cp2 & Hhdr & _); exact (proj1 (proj1 Hhdr)). }
split; [|split; [|exact Hal8]].
- destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hb & Hm) | (Hb & Hm)]].
  + destruct HLED as (_ & _ & Hall & _).
    pose proof (proj1 (Forall_forall _ _) Hall (b, m) Hin) as Hhb. cbv beta in Hhb. cbn [fst snd] in Hhb.
    destruct Hhb as (Hm0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & _ & _ & _ & _).
    pose proof cf_head_nonneg. lia.
  + destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hall).
    pose proof (proj1 (Forall_forall _ _) Hall (cid, pos) Hin) as Hf. cbv beta in Hf. cbn [fst snd] in Hf. lia.
  + rewrite Esp in Hb. lia.
- destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hb & Hm) | (Hb & Hm)]].
  + destruct HLED as (_ & _ & Hall & _).
    pose proof (proj1 (Forall_forall _ _) Hall (b, m) Hin) as Hhb. cbv beta in Hhb. cbn [fst snd] in Hhb.
    destruct Hhb as (Hm0 & Hab & _).
    destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    unfold req_size in Hc. destruct (Z.eqb_spec (m + cf_head) 0) as [E|E];
      [pose proof cf_head_nonneg; lia | lia].
  + destruct (alx_sep SEGS B ARx LAWS ly S Hp W mem md HAR) as (_ & Hall).
    pose proof (proj1 (Forall_forall _ _) Hall (cid, pos) Hin) as Hf. cbv beta in Hf. cbn [fst snd] in Hf. lia.
  + rewrite Hlyhi in Hm. lia.
Qed.

(* ---- the tree node's fields at the cut, in the words of prhex_tree's node (PRH_Reader.v pj_nodeR / pj_hdrR) ---- *)
Lemma evE_tree : forall a ly S Hp W mem md k p dep dl,
  EVMID a ly S Hp W mem md k p dep dl -> ea_v a <> 0 ->
  exists str, PRH_Reader.rd_u32 SEGS (rdW W mem) (ea_v a) (PjTree.tag (ea_t a)) /\
    PRH_Reader.rd_u64 SEGS (rdW W mem) (ea_v a + 16) str /\
    (PjTree.tag (ea_t a) = 3 -> exists txt2 bits2 kk, ea_t a = PjTree.JNum txt2 bits2 /\
       In (str, kk) (ea_Lam a) /\ Z.of_nat (length txt2) + 1 <= kk /\
       PRH_Reader.pj_cbytesR SEGS (rdW W mem) str txt2 /\
       PRH_Reader.rd_u64 SEGS (rdW W mem) (ea_v a + 8) bits2).
Proof.
intros a ly S Hp W mem md k p dep dl HMID Hv0.
destruct HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
destruct Htree as [Hz|(Hpj & _ & _)]; [contradiction|].
destruct (ea_t a) as [| | |t1 c1|s1|l1|m1] eqn:Et; cbn [PRH_Reader.pj_nodeR] in Hpj;
destruct Hpj as (_ & _ & nm & st & kd & ky & nn & cp2 & Hhdr & Hrest);
destruct Hhdr as (Hrw & Hty & Hnum & Hstr & _);
exists st; cbn [PjTree.tag] in Hty |- *;
(split; [exact Hty|]); (split; [exact Hstr|]); intro H3; try discriminate H3.
destruct Hrest as (Hnb & _ & _ & _ & _ & kk & Hcs & _).
destruct Hcs as (Hlb & Hlen & Hcb).
exists t1, c1, kk. split; [reflexivity|]. split; [exact Hlb|]. split; [exact Hlen|].
(* the kit of record's string node (PRH_Reader.pj_nodeR) adds the length bound before the bytes: take the bytes *)
split; [exact (proj2 Hcb)|]. rewrite <- Hnb. exact Hnum.
Qed.

(* ---- the environment of the walk: the registers plus v, in->scratch, in->differs, v->type, v->str ---- *)
Definition eve_E (regs : bvmap 5 word) (v scr dl tg str : Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs [w64 v; w64 scr; w64 dl; w64 tg; w64 str]).

Lemma evE_ew : forall regs v scr dl tg str n (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  ew (eve_E regs v scr dl tg str) n = getr regs r.
Proof.
intros regs v scr dl tg str n r Hr Hn. unfold eve_E. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_nat. exact Hr.
Qed.
Lemma evE_ewx : forall regs v scr dl tg str j, (j < 5)%nat ->
  ew (eve_E regs v scr dl tg str) (32 + j) = nth j [w64 v; w64 scr; w64 dl; w64 tg; w64 str] (Z_to_bv 64 0).
Proof.
intros regs v scr dl tg str j Hj. unfold eve_E. rewrite Eimg_low by (unfold A_TEXT; lia).
apply ew_Ereg_extra.
Qed.
Lemma evE_ew32 : forall regs v scr dl tg str, ew (eve_E regs v scr dl tg str) 32 = w64 v.
Proof. intros. exact (evE_ewx regs v scr dl tg str 0%nat ltac:(lia)). Qed.
Lemma evE_ew35 : forall regs v scr dl tg str, ew (eve_E regs v scr dl tg str) 35 = w64 tg.
Proof. intros. exact (evE_ewx regs v scr dl tg str 3%nat ltac:(lia)). Qed.
Lemma evE_ew33 : forall regs v scr dl tg str, ew (eve_E regs v scr dl tg str) 33 = w64 scr.
Proof. intros. exact (evE_ewx regs v scr dl tg str 1%nat ltac:(lia)). Qed.
Lemma evE_ew34 : forall regs v scr dl tg str, ew (eve_E regs v scr dl tg str) 34 = w64 dl.
Proof. intros. exact (evE_ewx regs v scr dl tg str 2%nat ltac:(lia)). Qed.
Lemma evE_ew36 : forall regs v scr dl tg str, ew (eve_E regs v scr dl tg str) 36 = w64 str.
Proof. intros. exact (evE_ewx regs v scr dl tg str 4%nat ltac:(lia)). Qed.
Lemma evE_env : forall regs v scr dl tg str, img_env VAL A_LIM (eve_E regs v scr dl tg str).
Proof. intros. unfold eve_E. apply Eimg_env. Qed.
Lemma evE_regs_ok : forall regs v scr dl tg str, regs_ok (eve_E regs v scr dl tg str) sr_atoms regs.
Proof. intros. unfold eve_E. apply regs_ok_Eimg_Ereg. Qed.

(* ---- obligations: an engine obligation is a sub-range of a range_addressable window ---- *)
Lemma evE_obl : forall (W : world SEGS) mem E ux len a n,
  U E EVE_Bx = SHADOW_OFF ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF a n -> a <= ux -> ux + len <= a + n ->
  range_addressable (rd_of SEGS (rdW W mem)) (U E EVE_Bx) ux len.
Proof.
intros W mem E ux len a n HB Hra H1 H2. rewrite HB.
change (rd_of SEGS (rdW W mem)) with (aview SEGS (w_H W) mem).
apply (range_addressable_sub (aview SEGS (w_H W) mem) SHADOW_OFF a n ux len Hra H1 H2).
Qed.

(* ---- the cursor's bytes are on the real stack, whose shadow the runtime keeps at 0 ---- *)
Lemma evE_vra : forall a ly S Hp W mem md k p dep dl,
  EVMID a ly S Hp W mem md k p dep dl -> ea_v a <> 0 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_v a) 56.
Proof.
intros a ly S Hp W mem md k p dep dl HMID Hv0.
destruct HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
destruct Htree as [Hz|(_ & _ & Hra & _)]; [contradiction | exact Hra].
Qed.

(* ---- the tree root's 56-byte granule hull is visible: prhex_tree's hull conjunct (PRH_FnEx.v:115-119) ---- *)
Lemma evE_vhull : forall a ly S Hp W mem md k p dep dl,
  EVMID a ly S Hp W mem md k p dep dl -> ea_v a <> 0 ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (ea_v a) 56.
Proof.
intros a ly S Hp W mem md k p dep dl HMID Hv0.
destruct HMID as (_ & _ & _ & _ & _ & _ & _ & _ & Htree & _).
destruct Htree as [Hz|(_ & _ & _ & Hh)]; [contradiction | exact Hh].
Qed.

Lemma evE_qra : forall a ly S Hp W mem md k p dep dl b n,
  ev_img_ok -> EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  ea_q a + 24 <= b -> 0 <= n -> b + n <= ea_q a + 40 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF b n.
Proof.
intros a ly S Hp W mem md k p dep dl b n HIMG HPRE HMID Hb Hn Hbn.
destruct (evE_num a ly S Hp W mem md k p dep dl HIMG HPRE HMID)
  as (HAR & Hlylo & Hlyhi & HSTK & Hd0 & Hd16 & HS1a & HS1b & Hsp16 & HS1lo & HS1hi &
      Hqlo & Hqsp & Hqd & Hdhi & Hhi47 & Hq8 & Hlosp & _).
(* the shadow byte of each address of [b, b + n), on the real stack: AR_laws_x's alx_zshadow_byte *)
intros x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
apply (alx_zshadow_byte SEGS B ARx LAWS ly S Hp W mem md x HAR). lia.
Qed.

(* ---- the symbolic state at CC, v <> 0 ---- *)
Lemma evE_stv : forall (fxc : YK11.FPState) (W : world SEGS) E regs mem s1 q fr v scr dl tg str,
  ew E 2 = w64 s1 -> ew E 9 = w64 s1 -> ew E 18 = w64 fr -> ew E 19 = w64 q -> ew E 24 = w64 SHADOW_OFF ->
  ew E 32 = w64 v -> ew E 33 = w64 scr -> ew E 34 = w64 dl -> ew E 35 = w64 tg -> ew E 36 = w64 str ->
  regs_ok E sr_atoms regs ->
  EVE_CEIL <= s1 -> s1 + 272 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  EVE_CEIL <= q -> q + 40 <= 2 ^ 47 -> q mod 8 = 0 ->
  4096 <= v -> v + 56 <= 2 ^ 47 -> v mod 8 = 0 ->
  0 <= fr -> fr + 128 <= 2 ^ 47 -> 0 <= scr < 2 ^ 64 -> 0 <= dl < 2 ^ 32 -> 0 <= tg <= 6 -> 0 <= str < 2 ^ 64 ->
  s1 + 128 <= q -> (q + 40 <= v \/ v + 56 <= q) -> (s1 + 128 <= v \/ v + 56 <= s1) ->
  (forall o, 32 <= o < 36 -> writable_at SEGS (rdW W mem) (q + o)) ->
  val_mem SEGS (rdW W mem) (s1 + 96) 8 (shadow_addr (q + 24)) ->
  val_mem SEGS (rdW W mem) (s1 + 104) 8 v ->
  val_mem SEGS (rdW W mem) (s1 + 112) 8 (fr + 64) ->
  val_mem SEGS (rdW W mem) (s1 + 120) 8 (q + 24) ->
  val_mem SEGS (rdW W mem) (q + 24) 8 scr ->
  val_mem SEGS (rdW W mem) (q + 32) 4 dl ->
  val_mem SEGS (rdW W mem) v 4 tg ->
  val_mem SEGS (rdW W mem) (v + 16) 8 str ->
  st_ok_pi SEGS VAL E eve_ssv
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC 0x958)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc W E regs mem s1 q fr v scr dl tg str E2 E9 E18 E19 E24 E32 E33 E34 E35 E36 HRO
  Hs1lo Hs1hi Hs132 Hqlo Hqhi Hq8 Hvlo Hvhi Hv8 Hfr0 Hfrhi Hscr Hdl Htg Hstr Hs1q Hvq Hvs1
  Hwr C96 C104 C112 C120 Cq24 Cq32 Cv0 Cv16.
pose proof alloc_ceiling_value as [HCV _].
unfold EVE_CEIL in Hs1lo, Hqlo.
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = v) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = scr) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = dl) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = tg) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = str) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = s1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = fr) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Hsh : 0 <= shadow_addr (q + 24) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. assert (0 <= (q + 24) / 8 < 2 ^ 45)
    by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
rewrite restrict_mkst_fx.
unfold eve_ssv. apply pa_entry_st_ok_full.
- exact HRO.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold YP09.region_ok, eve_Rs1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (eve_chunk_val SEGS E _ s1 96 8 _ (shadow_addr (q + 24))); [lia| |exact C96].
      apply (eve_den_shx E 19 24 q U19 ltac:(lia) U24).
    * apply (eve_chunk_val SEGS E _ s1 104 8 _ v); [lia| |exact C104].
      rewrite (eve_den_off E 32 v 0 U32). f_equal. lia.
    * apply (eve_chunk_val SEGS E _ s1 112 8 _ (fr + 64)); [lia| |exact C112].
      apply (eve_den_off E 18 fr 64 U18).
    * apply (eve_chunk_val SEGS E _ s1 120 8 _ (q + 24)); [lia| |exact C120].
      apply (eve_den_off E 19 q 24 U19).
  + unfold YP09.region_ok, eve_Rq.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [exact Hwr|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (eve_chunk_val SEGS E _ q 24 8 _ scr); [lia| |exact Cq24].
      rewrite (eve_den_off E 33 scr 0 U33). f_equal. lia.
    * apply (eve_chunk_val SEGS E _ q 32 4 _ dl); [lia| |exact Cq32].
      rewrite (eve_den_off E 34 dl 0 U34). f_equal. lia.
  + unfold YP09.region_ok, eve_Rv.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (eve_chunk_val SEGS E _ v 0 4 _ tg); [lia| |rewrite Z.add_0_r; exact Cv0].
      rewrite (eve_den_off E 35 tg 0 U35). f_equal. lia.
    * apply (eve_chunk_val SEGS E _ v 16 8 _ str); [lia| |exact Cv16].
      rewrite (eve_den_off E 36 str 0 U36). f_equal. lia.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint].
  unfold YP09.extent_disjoint, eve_Rs1, eve_Rq, eve_Rv.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U19, U32. repeat split; lia.
- split.
  + cbn [f_atoms eve_atoms0 atoms_ok app].
    unfold afact_ok. cbn [af_lo af_hi af_al2].
    repeat split.
    all: try rewrite U9; try rewrite U19; try rewrite U24; try rewrite U32; try rewrite U35.
    all: unfold EVE_TOP, EVE_CEIL, SHADOW_OFF; try (change (2 ^ 5) with 32); try (change (2 ^ 3) with 8);
         try (change (2 ^ 0) with 1); try rewrite Z.mod_1_r; try lia.
  + split; [|exact I].
    cbn [f_conds conds_ok].
    split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    change (branch_taken BC_NE (sv_denot E (SOff 32 0)) (sv_denot E (SLit 0)) = true).
    rewrite branch_ne_U, (eve_U_off E 32 v 0 U32 ltac:(lia)), U_SLit.
    change (zcanon 0) with 0. apply negb_true_iff. apply Z.eqb_neq. lia.
Qed.

(* ---- the symbolic state at CC, v = 0 ---- *)
Lemma evE_st0 : forall (fxc : YK11.FPState) (W : world SEGS) E regs mem s1 q fr scr dl,
  ew E 2 = w64 s1 -> ew E 9 = w64 s1 -> ew E 18 = w64 fr -> ew E 19 = w64 q -> ew E 24 = w64 SHADOW_OFF ->
  ew E 33 = w64 scr -> ew E 34 = w64 dl ->
  regs_ok E sr_atoms regs ->
  EVE_CEIL <= s1 -> s1 + 272 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  EVE_CEIL <= q -> q + 40 <= 2 ^ 47 -> q mod 8 = 0 ->
  0 <= fr -> fr + 128 <= 2 ^ 47 -> 0 <= scr < 2 ^ 64 -> 0 <= dl < 2 ^ 32 -> s1 + 128 <= q ->
  val_mem SEGS (rdW W mem) (s1 + 96) 8 (shadow_addr (q + 24)) ->
  val_mem SEGS (rdW W mem) (s1 + 104) 8 0 ->
  val_mem SEGS (rdW W mem) (s1 + 112) 8 (fr + 64) ->
  val_mem SEGS (rdW W mem) (s1 + 120) 8 (q + 24) ->
  val_mem SEGS (rdW W mem) (q + 24) 8 scr ->
  val_mem SEGS (rdW W mem) (q + 32) 4 dl ->
  st_ok_pi SEGS VAL E eve_ss0
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC 0x958)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc W E regs mem s1 q fr scr dl E2 E9 E18 E19 E24 E33 E34 HRO
  Hs1lo Hs1hi Hs132 Hqlo Hqhi Hq8 Hfr0 Hfrhi Hscr Hdl Hs1q C96 C104 C112 C120 Cq24 Cq32.
pose proof alloc_ceiling_value as [HCV _].
unfold EVE_CEIL in Hs1lo, Hqlo.
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = q) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U24 : bv_unsigned (ew E 24) = SHADOW_OFF)
  by (rewrite E24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = scr) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = dl) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = fr) by (rewrite E18; apply unsigned_lit_small; lia).
assert (Hsh : 0 <= shadow_addr (q + 24) < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. assert (0 <= (q + 24) / 8 < 2 ^ 45)
    by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
rewrite restrict_mkst_fx.
unfold eve_ss0. apply pa_entry_st_ok_full.
- exact HRO.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil.
  + unfold YP09.region_ok, eve_Rs1.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (eve_chunk_val SEGS E _ s1 96 8 _ (shadow_addr (q + 24))); [lia| |exact C96].
      apply (eve_den_shx E 19 24 q U19 ltac:(lia) U24).
    * apply (eve_chunk_val SEGS E _ s1 104 8 _ 0); [lia| |exact C104].
      apply bv_eq. change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
      rewrite U_SLit, Z_to_bv_unsigned. reflexivity.
    * apply (eve_chunk_val SEGS E _ s1 112 8 _ (fr + 64)); [lia| |exact C112].
      apply (eve_den_off E 18 fr 64 U18).
    * apply (eve_chunk_val SEGS E _ s1 120 8 _ (q + 24)); [lia| |exact C120].
      apply (eve_den_off E 19 q 24 U19).
  + unfold YP09.region_ok, eve_Rq0.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (eve_chunk_val SEGS E _ q 24 8 _ scr); [lia| |exact Cq24].
      rewrite (eve_den_off E 33 scr 0 U33). f_equal. lia.
    * apply (eve_chunk_val SEGS E _ q 32 4 _ dl); [lia| |exact Cq32].
      rewrite (eve_den_off E 34 dl 0 U34). f_equal. lia.
- cbn [YP09.pairwise_disjoint YP09.all_disjoint].
  unfold YP09.extent_disjoint, eve_Rs1, eve_Rq0.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite U9, U19. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms eve_atoms0 atoms_ok app].
  unfold afact_ok. cbn [af_lo af_hi af_al2].
  repeat split.
  all: try rewrite U9; try rewrite U19; try rewrite U24.
  all: unfold EVE_TOP, EVE_CEIL, SHADOW_OFF; try (change (2 ^ 5) with 32); try (change (2 ^ 3) with 8);
       try (change (2 ^ 0) with 1); try rewrite Z.mod_1_r; try lia.
Qed.

(* ---- the cut's configuration in the engine's form ---- *)
Lemma evE_cfg : forall (fxc : YK11.FPState) regs off mem md,
  ev_cfg fxc regs off mem md
  = mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC off)) mem (YK11.seg_rom SEGS)) md.
Proof.
intros fxc regs off mem md. unfold ev_cfg, ev_pc, EVE_PC. rewrite Hent.
replace (BASE + 7364 + off) with (BASE + (7364 + off)) by lia. reflexivity.
Qed.
Lemma evE_goal : forall (fxc : YK11.FPState) (W : world SEGS) regs off mem md Q,
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC off)) mem (YK11.seg_rom SEGS)) md) Q ->
  SRr SEGS W (ev_cfg fxc regs off mem md) Q.
Proof. intros fxc W regs off mem md Q H. rewrite evE_cfg. exact H. Qed.
Lemma evE_goal' : forall (fxc : YK11.FPState) (W : world SEGS) regs off mem md Q,
  SRr SEGS W (ev_cfg fxc regs off mem md) Q ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC off)) mem (YK11.seg_rom SEGS)) md) Q.
Proof. intros fxc W regs off mem md Q H. rewrite <- evE_cfg. exact H. Qed.

(* ---- a chunk of the symbolic state is a memory cell ---- *)
Lemma evE_chunk_of_st : forall (fxc : YK11.FPState) E ss (ms : machine_state) (W : world SEGS) i r jj off (w : N) e,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> nth_error (YP09.r_chunks r) jj = Some (YP09.mkChunk off (CVal w e)) ->
  (w <= 8)%N ->
  val_mem SEGS (rdW W (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros fxc E ss ms W i r jj off w e HS Hr Hc Hw.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall r (nth_error_In _ i Hr)) as Hro.
destruct Hro as (_ & _ & _ & Hch).
pose proof (proj1 (Forall_forall _ _) Hch _ (nth_error_In _ jj Hc)) as Hck.
cbn [ms_mem restrict] in Hck |- *.
exact (eve_val_of_chunk SEGS E _ _ off w e Hw Hck).
Qed.

Lemma evE_frame_aview : forall E rs (W : world SEGS) m m' z,
  frame_of E rs (rdW W m) (rdW W m') -> 0 <= z < 2 ^ 64 -> ~ YP09.in_wrange E rs z ->
  aview SEGS (w_H W) m' z = aview SEGS (w_H W) m z.
Proof.
intros E rs W m m' z HF Hz Hn. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 z)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

Lemma evE_scr : forall a, EVPRE a ->
  0 <= ea_scr a /\ ea_scr a + ea_len a + 1 <= alloc_ceiling /\ (ea_dl a = 0 \/ ea_dl a = 1) /\ 0 <= ea_len a.
Proof.
intros a HPRE. pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdl01 & Hwd0 & _).
destruct Hwd0 as (H0 & Hc & _). unfold ea_len in *. pose proof (Zle_0_nat (length (ea_x a))).
split; [exact H0|]. split; [lia|]. split; [exact Hdl01 | lia].
Qed.

(* the next cut's continuation, elaborated at the section's entry float state fx *)
Definition EVKD (a : ev_act) : Prop := KD B ARx SK a.

(* ---- the scratch lies in a live block ---- *)
Lemma evE_scrblk : forall a, EVPRE a -> 4096 <= ea_scr a.
Proof.
intros a HPRE. pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as ((HFPRE & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinblk & _).
destruct HFPRE as (HAR0 & _).
destruct Hinblk as (b & m & Hin & Hb & Hm & _).
destruct (alx_blocks SEGS B ARx LAWS (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) b m HAR0 Hin)
  as (_ & H4096 & _ & _ & _ & _). lia.
Qed.

(* ---- two memories whose cells hold the same value at [p, p + n) agree on each of those bytes ---- *)
Lemma evE_val_same : forall (H H' : word -> bool) m m' p (n : nat) v z,
  val_mem SEGS (mrestrict H m) p n v -> val_mem SEGS (mrestrict H' m') p n v -> p <= z < p + Z.of_nat n ->
  aview SEGS H' m' z = aview SEGS H m z.
Proof.
intros H H' m m' p n v z V V' Hz. unfold aview.
replace z with (p + Z.of_nat (Z.to_nat (z - p))) by lia.
rewrite (V (Z.to_nat (z - p)) ltac:(lia)), (V' (Z.to_nat (z - p)) ltac:(lia)). reflexivity.
Qed.

(* ---- the statics PST (alloc.c's six and fuzz_preset.c's g_own_ran_out, prh_glob's cells): two states whose ledgers
   have the same values agree on every static byte ---- *)
Lemma evE_led_same : forall ly S Hp (W : world SEGS) mem ly' S' Hp' (W' : world SEGS) mem' Lam peak cnt fail ran most own z,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own ->
  Exists (in_zr z) PST -> aview SEGS (w_H W') mem' z = aview SEGS (w_H W) mem z.
Proof.
intros ly S Hp W mem ly' S' Hp' W' mem' Lam peak cnt fail ran most own z
  ((G1 & G2 & G3 & G4 & G5 & (G6 & _) & (G7 & _) & _) & _) ((G1' & G2' & G3' & G4' & G5' & (G6' & _) & (G7' & _) & _) & _) Hz.
unfold prh_pst in Hz.
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G1 G1' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G2 G2' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G3 G3' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G4 G4' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G5 G5' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G6 G6' Hz)|].
apply Exists_cons in Hz. destruct Hz as [Hz|Hz]; [exact (evE_val_same _ _ _ _ _ _ _ z G7 G7' Hz)|].
inversion Hz.
Qed.

(* ---- a read-only byte (in_roP over the relro range) is an image byte ---- *)
Lemma evE_ro_img : forall z, in_roP SEGS pa_relro_lo pa_relro_hi z -> in_img SEGS z.
Proof.
intros z [(sg & Hsg & _ & Hr)|Hr]; [exists sg; split; [exact Hsg | lia] | exact (pa_relro_img z Hr)].
Qed.

(* ---- the read-only bytes at every state of the piece (the xrom strcmp text's arodata_okP): fpre's arodata_okP at the
   entry (ev_pre's first conjunct), carried by the journal's image clause for a byte off the statics, and by the
   ledger (MID's and ev_pre's have the same values) for a static byte ---- *)
Lemma evE_rod : forall a ly S Hp W mem md k p dep dl,
  EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID.
pose proof (evE_scrblk a HPRE) as Hscr4096.
pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as ((HFPRE & HROD & _) & _ & _ & _ & _ & _ & _ & _ & Hq1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & HLED0 & _).
destruct HFPRE as (_ & _ & _ & _ & _ & Hstk0 & _).
destruct Hstk0 as (_ & HSTK0 & Hclo & Hlosp & _).
pose proof alloc_ceiling_value as [HCV _].
pose proof HMID as (HJ & _ & _ & _ & HLED & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Him & _).
intros z Hro Hown Herr.
rewrite <- (HROD z Hro Hown Herr).
assert (Hdec : forall r, {in_zr z r} + {~ in_zr z r}).
{ intros r. unfold in_zr. destruct (Z_le_gt_dec (fst r) z) as [h1|h1]; [|right; lia].
  destruct (Z_lt_ge_dec z (fst r + snd r)) as [h2|h2]; [left; lia | right; lia]. }
destruct (Exists_dec (in_zr z) PST Hdec) as [Hpst|Hpst].
- exact (evE_led_same _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ z HLED0 HLED Hpst).
- assert (Hfp : fp_spares (ea_FP a) z).
  { apply fp_spares_closed. unfold YI16.sink_open_fp, YI16.in_fp, ea_FP.
    intros (r & Hr & Hr0). cbn [In] in Hr.
    destruct Hr as [Hr|[Hr|[Hr|[Hr|[]]]]]; subst r; cbn [fst snd] in Hr0; lia. }
  exact (Him z (evE_ro_img z Hro) Hown Herr Hpst Hfp).
Qed.

(* ---- the read-only bytes survive any change at or above alloc_ceiling (FuzzStrdup.v sd_rod_kept's shape) ---- *)
Lemma evE_rod_move : forall (W W' : world SEGS) m m',
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) m) ->
  (forall s0, 0 <= s0 < alloc_ceiling -> aview SEGS (w_H W') m' s0 = aview SEGS (w_H W) m s0) ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W') m').
Proof.
intros W W' m m' H HA z Hro Hown Herr.
pose proof (@pa_segs_low _ A_prog_listing PA z (evE_ro_img z Hro)) as Hl.
pose proof alloc_ceiling_value as [HCV _].
rewrite HA by (unfold kLowMemEnd in Hl; lia).
exact (H z Hro Hown Herr).
Qed.

(* ---- a harness block of the ledger: its bounds, its shadow and hull over the user range (alx_hshadow at cf_head),
   its granule tail up to the granule of its last byte (alx_blocks + alx_blocks_tail) ---- *)
Lemma evE_lam : forall a ly S Hp W mem md k p dep dl b m,
  EVMID a ly S Hp W mem md k p dep dl -> In (b, m) (ea_Lam a) -> 0 < m ->
  4096 <= b /\ b + m <= alloc_ceiling /\ m < 2 ^ 32 /\ amem_range b m /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF b m /\
  shadow_hull_vis (aview SEGS (w_H W) mem) b m /\
  (forall z, b <= z < 8 * ((b + m - 1) / 8) + 8 -> aview SEGS (w_H W) mem z <> None).
Proof.
intros a ly S Hp W mem md k p dep dl b m HMID Hin Hm.
pose proof cf_head_nonneg as Hh.
destruct HMID as (HJ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & _).
destruct HLED as (_ & _ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall (b, m) Hin) as Hhb. cbv beta in Hhb. cbn [fst snd] in Hhb.
destruct Hhb as (Hm0 & Hab & HHp & Hb16 & _).
assert (Hreq : req_size (m + cf_head) = m + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & Hpres & _).
rewrite Hreq in Hc, Happ, Hpres.
pose proof (CUTFIX_blk32 ly S Hp W mem md _ _ HAR Hab) as H32.
destruct (alx_hshadow SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab HHp) as (Hbs & Hhull).
rewrite Hreq in Hbs, Hhull.
replace (b - cf_head + cf_head) with b in Hbs, Hhull by lia.
replace (m + cf_head - cf_head) with m in Hbs, Hhull by lia.
split; [lia|]. split; [lia|]. split; [lia|].
split; [apply eve_in_app_amem; apply (in_app_sub (b - cf_head) (m + cf_head) b m Happ); lia|].
split; [exact (block_shadow_range _ _ b m b m Hbs ltac:(lia) ltac:(lia))|].
split; [exact (Hhull ltac:(lia))|].
intros z Hz. destruct (Z_lt_le_dec z (b + m)) as [Hzl|Hzl].
- apply (eve_apresent_aview SEGS). exact (proj1 (Hpres z ltac:(lia))).
- apply (alx_blocks_tail SEGS B ARx LAWS ly S Hp W mem md _ _ z HAR Hab). rewrite Hreq. lia.
Qed.

(* ---- the scratch's block: its granule tail is mapped (alx_blocks + alx_blocks_tail) ---- *)
Lemma evE_scrtail : forall a ly S Hp W mem md k p dep dl,
  EVPRE a -> EVMID a ly S Hp W mem md k p dep dl ->
  forall z, ea_scr a <= z < 8 * ((ea_scr a + ea_len a) / 8) + 8 -> aview SEGS (w_H W) mem z <> None.
Proof.
intros a ly S Hp W mem md k p dep dl HPRE HMID z Hz.
pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinblk & _).
destruct Hinblk as (b & m & Hin & Hb & Hm & _).
destruct HMID as (HJ & _ & _ & Hbl & _).
pose proof HJ as (HAR & _).
rewrite <- Hbl in Hin.
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md b m HAR Hin) as (_ & _ & _ & _ & Hpres & _).
destruct (Z_lt_le_dec z (b + req_size m)) as [Hzl|Hzl].
- apply (eve_apresent_aview SEGS). exact (proj1 (Hpres z ltac:(lia))).
- apply (alx_blocks_tail SEGS B ARx LAWS ly S Hp W mem md b m z HAR Hin). lia.
Qed.

(* ---- the string rows' region premise (amem_range8) for bytes inside a live block that end by the block's end:
   CUTFIX_blk_amem8 at the block ---- *)
Lemma evE_amr8 : forall ly S Hp W mem md p n x len,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= x -> x + len <= p + req_size n ->
  amem_range8 x len.
Proof.
intros ly S Hp W mem md p n x len HAR Hin Hpx Hxl.
pose proof (CUTFIX_blk_amem8 ly S Hp W mem md p n HAR Hin) as Hb8.
unfold amem_range8 in *. lia.
Qed.
Lemma evE_lam_amr8 : forall a ly S Hp W mem md k p dep dl b m len,
  EVMID a ly S Hp W mem md k p dep dl -> In (b, m) (ea_Lam a) -> 0 <= len <= m -> amem_range8 b len.
Proof.
intros a ly S Hp W mem md k p dep dl b m len HMID Hin Hlen.
pose proof cf_head_nonneg as Hh.
destruct HMID as (HJ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & _).
destruct HLED as (_ & _ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall (b, m) Hin) as Hhb. cbv beta in Hhb. cbn [fst snd] in Hhb.
destruct Hhb as (Hm0 & Hab & _).
assert (Hreq : m + cf_head <= req_size (m + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
apply (evE_amr8 ly S Hp W mem md _ _ b len HAR Hab); lia.
Qed.
Lemma evE_scr_amr8 : forall a ly S Hp W mem md k p dep dl len,
  EVPRE a -> EVMID a ly S Hp W mem md k p dep dl -> 0 <= len <= ea_len a + 1 -> amem_range8 (ea_scr a) len.
Proof.
intros a ly S Hp W mem md k p dep dl len HPRE HMID Hlen.
pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinblk & _).
destruct Hinblk as (b & m & Hin & Hb & Hm & _).
destruct HMID as (HJ & _ & _ & Hbl & _).
pose proof HJ as (HAR & _).
rewrite <- Hbl in Hin.
assert (Hreq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
apply (evE_amr8 ly S Hp W mem md b m (ea_scr a) len HAR Hin); lia.
Qed.

(* ---- the tree root's num field lies in application memory ---- *)
Lemma evE_vamem8 : forall a ly S Hp W mem md k p dep dl,
  ev_img_ok -> EVPRE a -> EVMID a ly S Hp W mem md k p dep dl -> ea_v a <> 0 -> amem_range (ea_v a + 8) 8.
Proof.
intros a ly S Hp W mem md k p dep dl HIMG HPRE HMID Hv0.
pose proof alloc_ceiling_value as [HCV HCM]. pose proof cf_head_nonneg as Hh.
destruct (evE_num a ly S Hp W mem md k p dep dl HIMG HPRE HMID)
  as (HAR & Hlylo & Hlyhi & HSTK & Hd0 & Hd16 & HS1a & HS1b & Hsp16 & HS1lo & HS1hi &
      Hqlo & Hqsp & Hqd & Hdhi & Hhi47 & _).
destruct HMID as (_ & _ & _ & _ & HLED & _ & _ & _ & Htree & _).
destruct Htree as [Hz|(_ & Hhome & _)]; [contradiction|].
destruct Hhome as [(b & m & Hin & Hb & Hm) | [(cid & pos & Hin & Hb & Hm) | (Hb & Hm)]].
- destruct HLED as (_ & _ & Hall & _).
  pose proof (proj1 (Forall_forall _ _) Hall (b, m) Hin) as Hhb. cbv beta in Hhb. cbn [fst snd] in Hhb.
  destruct Hhb as (Hm0 & Hab & _).
  destruct (alx_blocks SEGS B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & _ & _ & Happ & _ & _).
  assert (m + cf_head <= req_size (m + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia).
  apply eve_in_app_amem. apply (in_app_sub _ _ _ _ Happ); lia.
- destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & Happ & _).
  apply eve_in_app_amem. apply (in_app_sub _ _ _ _ Happ); lia.
- assert (Esp : spZ (ea_regs a) = ea_sp0 a) by reflexivity. rewrite Esp in Hb.
  unfold amem_range, kHighMemBeg, kHighMemEnd. right. lia.
Qed.

Lemma evE_gptp : forall a, EVPRE a ->
  getr (ea_regs a) 3 = w64 (as_gp B) /\ getr (ea_regs a) 4 = w64 (as_tp B).
Proof.
intros a HPRE. pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as ((HFPRE & _) & _).
destruct HFPRE as (_ & _ & _ & Hgp0 & Htp0 & _). split; assumption.
Qed.

Lemma evE_img_ewset : forall E T v, img_env VAL A_LIM E -> (512 <= T)%nat -> img_env VAL A_LIM (ewset E T v).
Proof.
intros E T v HE HT aa Ha. rewrite ew_ewset_other by (unfold A_LIM in Ha; lia). exact (HE aa Ha).
Qed.

(* ---- a call's result tested against 0 ---- *)
Lemma evE_br_ne_t : forall E n (w : word), ew E n = w ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> w <> w64 0.
Proof.
intros E n w Hw Hc ->. rewrite branch_ne_U, U_SOff, U_SLit, Hw in Hc. vm_compute in Hc. discriminate.
Qed.
Lemma evE_br_ne_f : forall E n (w : word), ew E n = w ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w = w64 0.
Proof.
intros E n w Hw Hc. rewrite branch_ne_U, U_SOff, U_SLit, Hw in Hc.
apply negb_false_iff, Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. transitivity 0; [lia | reflexivity].
Qed.
Lemma evE_br_eq_t : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = true -> w = w64 0.
Proof.
intros E n w Hw Hc. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc.
apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
pose proof (bv_unsigned_in_range 64 w) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
rewrite zcanon_id in Hc by (unfold M64; lia).
apply bv_eq. transitivity 0; [lia | reflexivity].
Qed.
Lemma evE_br_eq_f : forall E n (w : word), ew E n = w ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = false -> w <> w64 0.
Proof.
intros E n w Hw Hc ->. rewrite branch_eq_U, U_SOff, U_SLit, Hw in Hc. vm_compute in Hc. discriminate.
Qed.
Lemma evE_agree_ewset : forall E0 E T v, env_agree 32 E0 E -> (32 <= T)%nat -> env_agree 32 E0 (ewset E T v).
Proof.
intros E0 E T v [HA HD] HT. split; [intros n Hn; rewrite ew_ewset_other by lia; apply HA; exact Hn | exact HD].
Qed.

(* ---- the common ending: from a state at CD with in->differs = dl' to the cut CD; the memory normal form of the
   memory at CD (the last run's P) is MIDC's memnorm premise ---- *)
Lemma evE_close : forall (fxc : YK11.FPState) a (W : world SEGS) regs regs' mem mem' md md' ly S Hp k i1 c j bits dl',
  ev_img_ok -> EVKD a -> EVPRE a -> @ev_fx fx fxc ->
  EVCC a W regs mem md ly S Hp k i1 c j bits ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  YAkMemnorm.memnorm SEGS mem' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
     aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  val_mem SEGS (rdW W mem') (ea_q a + 32) 4 dl' ->
  (forall r : Prelude.reg, In r CALLEE_SAVED -> getr regs' r = getr regs r) ->
  (dl' = 0 \/ dl' = 1) ->
  (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> PjTree.JNum (ev_sub (ea_x a) i1 j) bits)) ->
  SRr SEGS W (ev_cfg fxc regs' 0x9e4 mem' md') (@ev_to_exit fx rc cp PI RL A_prog_listing PA B ARx SK a).
Proof.
intros fxc a W regs regs' mem mem' md md' ly S Hp k i1 c j bits dl'
  HIMG KDa HPRE HFX HCC HJ HPMc Hmem Cdl HK Hdl' Hiff.
pose proof HCC as HCC'. unfold ev_CC in HCC'. cbv zeta in HCC'.
destruct HCC' as (HMID & HB & C112 & R21 & C120 & C96 & R22 & Hij & HN & Hgarr & Cnum & HFSH).
pose proof HB as HB'. unfold ev_base in HB'.
destruct HB' as (HREGS & R23 & Hi1lt & Hnth & Hwsc & Hskip & Hc34 & Hc91 & Hc123 & Hc102 & Hc110 & Hc116 & C104).
pose proof HREGS as HREGS'. unfold ev_regs in HREGS'.
destruct HREGS' as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (evE_num a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) HIMG HPRE HMID)
  as (HAR & Hlylo & Hlyhi & HSTK & Hd0 & Hd16 & HS1a & HS1b & Hsp16 & HS1lo & HS1hi &
      Hqlo & Hqsp & Hqd & Hdhi & Hhi47 & Hq8 & Hlosp & HIN1 & HFR & Hfrlo & Hfrhi & Hvfacts).
pose proof alloc_ceiling_value as [HCV _].
pose proof HMID as HMID2.
destruct HMID2 as (HJ0 & Hwin & HHp & Hbl & HLED & Hcur & Hsrcrd & Hwd & Htree & Hflag).
destruct Hcur as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
assert (HCUR : prhex_cur W mem' (ea_q a) (ea_x0 a + Z.of_nat i1) (ea_x0 a + ea_len a)
                 (ea_dep a) (ea_scr a) dl').
{ split; [|split; [|split; [|split; [|exact Cdl]]]];
  apply (eve_val_move SEGS (w_H W) mem mem'); solve [ intros i Hi; apply Hmem; lia | assumption ]. }
apply (KDa fxc W regs' mem' md' ly S Hp k i1 c j (PjTree.JNum (ev_sub (ea_x a) i1 j) bits) HPRE HFX).
unfold ev_CD. cbv zeta.
split.
{ unfold ev_base. split.
  - unfold ev_regs.
    rewrite (HK 2%bv ltac:(cbv; tauto)), (HK 3%bv ltac:(cbv; tauto)), (HK 4%bv ltac:(cbv; tauto)),
            (HK 8%bv ltac:(cbv; tauto)), (HK 9%bv ltac:(cbv; tauto)), (HK 18%bv ltac:(cbv; tauto)),
            (HK 19%bv ltac:(cbv; tauto)), (HK 24%bv ltac:(cbv; tauto)), (HK 25%bv ltac:(cbv; tauto)),
            (HK 26%bv ltac:(cbv; tauto)).
    repeat split; assumption.
  - rewrite (HK 23%bv ltac:(cbv; tauto)). split; [exact R23|].
    split; [exact Hi1lt|]. split; [exact Hnth|]. split; [exact Hwsc|]. split; [exact Hskip|].
    split; [exact Hc34|]. split; [exact Hc91|]. split; [exact Hc123|]. split; [exact Hc102|].
    split; [exact Hc110|]. split; [exact Hc116|].
    apply (eve_val_move SEGS (w_H W) mem mem'); [intros i Hi; apply Hmem; lia | exact C104]. }
split; [rewrite (HK 22%bv ltac:(cbv; tauto)); exact R22|].
split; [exact Hij|]. split; [exact HN|].
exists dl'. split.
{ apply (MIDC a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) mem' md' k
           (ea_x0 a + Z.of_nat i1) dl' HPRE HMID HJ); [| exact HCUR | exact HPMc].
  intros z Hz Hwz _ Hz2. apply Hmem; [exact Hz | | exact Hz2].
  intros Hc. apply Hwz. unfold ev_wz. left. unfold STK_RT_STRTOD, ESTACK. lia. }
split; [exact Hdl' | exact Hiff].
Qed.

Ltac evE_ewn := repeat (first [rewrite ew_ewset_other by lia | rewrite ew_havoc_old by lia]).
Ltac evE_ewn_in H := repeat (first [rewrite ew_ewset_other in H by lia | rewrite ew_havoc_old in H by lia]).

(* ======== ev_E: CC (+0x958) -> CD (+0x9e4) ======== *)
Theorem ev_E : ev_E_stmt B ARx SK.
Proof.
unfold ev_E_stmt. intros HIMG SCMP BCMP a KDa.
unfold KC. intros fxc W regs mem md ly S Hp k i1 c j bits HPRE HFX HCC.
pose proof HCC as HCC'. unfold ev_CC in HCC'. cbv zeta in HCC'.
destruct HCC' as (HMID & HB & C112 & R21 & C120 & C96 & R22 & Hij & HN & Hgarr & Cnum & HFSH).
pose proof HB as HB'. unfold ev_base in HB'.
destruct HB' as (HREGS & R23 & Hi1lt & Hnth & Hwsc & Hskip & Hc34 & Hc91 & Hc123 & Hc102 & Hc110 & Hc116 & C104).
pose proof HREGS as HREGS'. unfold ev_regs in HREGS'.
destruct HREGS' as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct (evE_num a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) HIMG HPRE HMID)
  as (HAR & Hlylo & Hlyhi & HSTK & Hd0 & Hd16 & HS1a & HS1b & Hsp16 & HS1lo & HS1hi &
      Hqlo & Hqsp & Hqd & Hdhi & Hhi47 & Hq8 & Hlosp & HIN1 & HFR & Hfrlo & Hfrhi & Hvfacts).
destruct (evE_scr a HPRE) as (Hscr0 & Hscrhi & Hdl01 & Hlen0).
pose proof alloc_ceiling_value as [HCV _].
pose proof HMID as HMID2.
destruct HMID2 as (HJ0 & Hwin & HHp & Hbl & HLED & Hcur & Hsrcrd & Hwd & Htree & Hsav & Hflag & Hroom & Hrpos & HMN).
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _ & _ & _).
destruct Hcur as (Cq0 & Cq8 & Cq16 & Cq24 & Cq32).
assert (Hwr : forall o, 32 <= o < 36 -> writable_at SEGS (rdW W mem) (ea_q a + o)).
{ intros o Ho. apply (apresent_writable SEGS). apply HpresJ. lia. }
(* the runs carry P := YAkMemnorm.memnorm SEGS (YSRrMemnorm.v); HPM is P at the run's start memory *)
pose (RUNTO := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS
                 (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
pose (RUN := paj_run_x_inv (fx := fxc) (SK := SK) (PL := PL_prog_A) (PI := PA) B PST ARx LAWS
               (YAkMemnorm.memnorm SEGS) (srr_inv_laws_memnorm_k SEGS)).
assert (HPM : YAkMemnorm.memnorm SEGS mem) by exact HMN.
pose (BR := paj_branch (PI := PA)).
apply (evE_goal fxc W regs 0x958 mem md).
destruct (Z.eq_dec (ea_v a) 0) as [Hv0|Hvn].
- (* ---- v = 0: nothing is compared, in->differs is kept ---- *)
  assert (HEI : img_env VAL A_LIM (eve_E regs 0 (ea_scr a) (ea_dl a) 0 0)) by apply evE_env.
  assert (HS : st_ok_pi SEGS VAL (eve_E regs 0 (ea_scr a) (ea_dl a) 0 0) eve_ss0
                 (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC 0x958)) mem (YK11.seg_rom SEGS)))).
  { apply (evE_st0 fxc W _ regs mem (ea_S1 a) (ea_q a) (ea_fr a) (ea_scr a) (ea_dl a)).
    - rewrite (evE_ew regs 0 (ea_scr a) (ea_dl a) 0 0 2%nat 2%bv eq_refl ltac:(lia)). exact R2.
    - rewrite (evE_ew regs 0 (ea_scr a) (ea_dl a) 0 0 9%nat 9%bv eq_refl ltac:(lia)). exact R9.
    - rewrite (evE_ew regs 0 (ea_scr a) (ea_dl a) 0 0 18%nat 18%bv eq_refl ltac:(lia)). exact R18.
    - rewrite (evE_ew regs 0 (ea_scr a) (ea_dl a) 0 0 19%nat 19%bv eq_refl ltac:(lia)). exact R19.
    - rewrite (evE_ew regs 0 (ea_scr a) (ea_dl a) 0 0 24%nat 24%bv eq_refl ltac:(lia)). exact R24.
    - exact (evE_ewx regs 0 (ea_scr a) (ea_dl a) 0 0 1%nat ltac:(lia)).
    - exact (evE_ewx regs 0 (ea_scr a) (ea_dl a) 0 0 2%nat ltac:(lia)).
    - apply evE_regs_ok.
    - unfold EVE_CEIL. lia.
    - lia.
    - exact HS1b.
    - unfold EVE_CEIL. lia.
    - lia.
    - exact Hq8.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact C96.
    - rewrite <- Hv0. exact C104.
    - exact C112.
    - exact C120.
    - exact Cq24.
    - exact Cq32. }
  assert (SHOK : sh_ok SEGS EVE_Bx eve_SH (eve_E regs 0 (ea_scr a) (ea_dl a) 0 0) (rdW W mem))
    by (unfold sh_ok, eve_SH; apply Forall_nil).
  pose proof HJ0 as HJ.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EVE_Bspan (EVE_PC 0x9e4).
  + (* the write premise: both regions are read-only *)
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + (* the state at CD *)
    assert (Hmem : forall z, 0 <= z < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) z = aview SEGS (w_H W) mem z).
    { intros z Hz. apply (evE_frame_aview _ _ W mem (ms_mem ms) z HFr Hz).
      intros (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [Hin|[Hin|Hin]]; try (subst r); cbn [eve_Rs1 eve_Rq0 YP09.r_wlo YP09.r_whi] in Hr;
        [lia | lia | destruct Hin]. }
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (18%bv : bv 5) P18.
    prreg HS (19%bv : bv 5) P19. prreg HS (22%bv : bv 5) P22. prreg HS (23%bv : bv 5) P23.
    prreg HS (24%bv : bv 5) P24. prreg HS (25%bv : bv 5) P25. prreg HS (26%bv : bv 5) P26.
    apply (evE_goal' fxc W (ms_regs ms) 0x9e4 (ms_mem ms)).
    apply (KDa fxc W (ms_regs ms) (ms_mem ms) _ ly S Hp k i1 c j
             (PjTree.JNum (ev_sub (ea_x a) i1 j) bits) HPRE HFX).
    assert (HCUR : prhex_cur W (ms_mem ms) (ea_q a) (ea_x0 a + Z.of_nat i1) (ea_x0 a + ea_len a)
                     (ea_dep a) (ea_scr a) (ea_dl a)).
    { split; [|split; [|split; [|split]]];
      apply (eve_val_move SEGS (w_H W) mem (ms_mem ms));
      solve [ intros i Hi; apply Hmem; lia | assumption ]. }
    unfold ev_CD. cbv zeta.
    split.
    { unfold ev_base. split.
      - unfold ev_regs. rewrite P2, P3, P4, P8, P9, P18, P19, P24, P25, P26.
        repeat split; assumption.
      - rewrite P23. split; [exact R23|].
        split; [exact Hi1lt|]. split; [exact Hnth|]. split; [exact Hwsc|]. split; [exact Hskip|].
        split; [exact Hc34|]. split; [exact Hc91|]. split; [exact Hc123|]. split; [exact Hc102|].
        split; [exact Hc110|]. split; [exact Hc116|].
        apply (eve_val_move SEGS (w_H W) mem (ms_mem ms)); [intros i Hi; apply Hmem; lia | exact C104]. }
    split; [rewrite P22; exact R22|].
    split; [exact Hij|]. split; [exact HN|].
    exists (ea_dl a).
    split.
    { apply (MIDC a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) (ms_mem ms) _ k
               (ea_x0 a + Z.of_nat i1) (ea_dl a) HPRE HMID HJ); [| exact HCUR | exact HPM].
      intros z Hz _ _ _. apply Hmem. exact Hz. }
    split; [exact Hdl01|].
    split; [intros H1; left; exact H1 | intros [H1|(Hv1 & _)]; [exact H1 | exfalso; apply Hv1; exact Hv0]].
- (* ---- v <> 0 ---- *)
  destruct (Hvfacts Hvn) as (Hvlo & Hvhi & Hv8).
  destruct (evE_tree a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) HMID Hvn)
    as (str & Htag & Hstr & Hnum3).
  pose proof (evE_vra a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) HMID Hvn) as HVRA.
  (* the tree's footprint is apart from in, from the entry stack window and from the scratch (ev_pre) *)
  assert (Hfoot : forall z, PjStruct.pj_foot (ea_v a) (ea_D a) z ->
            ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) /\ ~ (ea_q a <= z < ea_q a + 40) /\
            ~ (ea_sp0 a - ea_STK a <= z < ea_sp0 a) /\ ~ (as_errno B <= z < as_errno B + 4)).
  { pose proof HPRE as HP2. unfold ev_pre in HP2. cbv zeta in HP2.
    destruct HP2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hvt & _).
    destruct Hvt as [Hz|(_ & _ & Hf)]; [contradiction | exact Hf]. }
  assert (Hvq : ea_q a + 40 <= ea_v a \/ ea_v a + 56 <= ea_q a).
  { destruct (Z_le_gt_dec (ea_q a + 40) (ea_v a)) as [h|h]; [left; lia|].
    destruct (Z_le_gt_dec (ea_v a + 56) (ea_q a)) as [h2|h2]; [right; lia|].
    exfalso. destruct (Hfoot (Z.max (ea_v a) (ea_q a)) ltac:(left; lia)) as (_ & Hq' & _ & _).
    apply Hq'. lia. }
  assert (Hvs1 : ea_S1 a + 128 <= ea_v a \/ ea_v a + 56 <= ea_S1 a).
  { destruct (Z_le_gt_dec (ea_S1 a + 128) (ea_v a)) as [h|h]; [left; lia|].
    destruct (Z_le_gt_dec (ea_v a + 56) (ea_S1 a)) as [h2|h2]; [right; lia|].
    exfalso. destruct (Hfoot (Z.max (ea_v a) (ea_S1 a)) ltac:(left; lia)) as (_ & _ & Hs' & _).
    apply Hs'. lia. }
  assert (Htg6 : 0 <= PjTree.tag (ea_t a) <= 6) by (destruct (ea_t a); cbn [PjTree.tag]; lia).
  assert (Hstr64 : 0 <= str < 2 ^ 64) by (destruct Hstr as (Hs & _); lia).
  assert (HEI : img_env VAL A_LIM (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str))
    by apply evE_env.
  assert (U32 : bv_unsigned (ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) 32)
                = ea_v a).
  { rewrite evE_ew32. apply unsigned_lit_small. lia. }
  assert (U35 : bv_unsigned (ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) 35)
                = PjTree.tag (ea_t a)).
  { rewrite evE_ew35. apply unsigned_lit_small. lia. }
  assert (U24 : bv_unsigned (ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) 24)
                = SHADOW_OFF).
  { rewrite (evE_ew regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str 24%nat 24%bv eq_refl
      ltac:(lia)), R24. apply unsigned_lit_small. unfold SHADOW_OFF; lia. }
  assert (U19' : bv_unsigned (ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) 19)
                 = ea_q a).
  { rewrite (evE_ew regs _ _ _ _ str 19%nat 19%bv eq_refl ltac:(lia)), R19.
    apply unsigned_lit_small. lia. }
  assert (HAE : env_agree 32
                  (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str])
                  (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str))
    by (split; [intros n Hn; unfold eve_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HBx : U (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) EVE_Bx = SHADOW_OFF).
  { unfold EVE_Bx. rewrite (eve_U_off _ 24 SHADOW_OFF 0 U24 ltac:(unfold SHADOW_OFF; lia)). lia. }
  assert (HS : st_ok_pi SEGS VAL (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) eve_ssv
                 (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + EVE_PC 0x958)) mem (YK11.seg_rom SEGS)))).
  { apply (evE_stv fxc W _ regs mem (ea_S1 a) (ea_q a) (ea_fr a) (ea_v a) (ea_scr a) (ea_dl a)
             (PjTree.tag (ea_t a)) str).
    - rewrite (evE_ew regs _ _ _ _ str 2%nat 2%bv eq_refl ltac:(lia)). exact R2.
    - rewrite (evE_ew regs _ _ _ _ str 9%nat 9%bv eq_refl ltac:(lia)). exact R9.
    - rewrite (evE_ew regs _ _ _ _ str 18%nat 18%bv eq_refl ltac:(lia)). exact R18.
    - rewrite (evE_ew regs _ _ _ _ str 19%nat 19%bv eq_refl ltac:(lia)). exact R19.
    - rewrite (evE_ew regs _ _ _ _ str 24%nat 24%bv eq_refl ltac:(lia)). exact R24.
    - exact (evE_ewx regs _ _ _ _ str 0%nat ltac:(lia)).
    - exact (evE_ewx regs _ _ _ _ str 1%nat ltac:(lia)).
    - exact (evE_ewx regs _ _ _ _ str 2%nat ltac:(lia)).
    - exact (evE_ewx regs _ _ _ _ str 3%nat ltac:(lia)).
    - exact (evE_ewx regs _ _ _ _ str 4%nat ltac:(lia)).
    - apply evE_regs_ok.
    - unfold EVE_CEIL. lia.
    - lia.
    - exact HS1b.
    - unfold EVE_CEIL. lia.
    - lia.
    - exact Hq8.
    - lia.
    - lia.
    - exact Hv8.
    - lia.
    - lia.
    - lia.
    - lia.
    - exact Htg6.
    - exact Hstr64.
    - lia.
    - exact Hvq.
    - exact Hvs1.
    - exact Hwr.
    - exact C96.
    - exact C104.
    - exact C112.
    - exact C120.
    - exact Cq24.
    - exact Cq32.
    - exact (proj2 Htag).
    - exact (proj2 Hstr). }
  assert (SHOK : sh_ok SEGS EVE_Bx eve_SH
                   (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) (rdW W mem))
    by (unfold sh_ok, eve_SH; apply Forall_nil).
  pose proof HJ0 as HJ.
  paj_run_tok_x_inv RUN HS HJ SHOK HPM EVE_Bspan.
  + (* the 4-byte check of v->type *)
    rewrite (eve_U_off _ 32 (ea_v a) 0 U32 ltac:(lia)).
    apply (evE_obl W mem _ (ea_v a + 0) 4 (ea_v a) 56 HBx HVRA ltac:(lia) ltac:(lia)).
  + (* the write premise *)
    apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen.
    * reflexivity.
    * rewrite (evE_ew regs _ _ _ _ str 19%nat 19%bv eq_refl ltac:(lia)), R19.
      apply unsigned_lit_small. lia.
    * cbn [eve_Rq YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
    * apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + (* the type test *)
    assert (Hmem1 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
              aview SEGS (w_H W) (ms_mem ms) z = aview SEGS (w_H W) mem z).
    { intros z Hz Hnz. apply (evE_frame_aview _ _ W mem (ms_mem ms) z HFr Hz).
      intros (r & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [Hin|[Hin|[Hin|[]]]]; subst r;
        cbn [eve_Rs1 eve_Rq eve_Rv YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr;
        [lia | rewrite U19' in Hr; lia | lia]. }
    assert (HRAq1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (ea_q a + 32) 4).
    { apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms) (ea_q a + 32) 4 ltac:(lia) ltac:(lia)).
      - intros s0 Hs0. apply Hmem1; lia.
      - apply (evE_qra a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)
                 (ea_q a + 32) 4 HIMG HPRE HMID); lia. }
    assert (HRAv1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (ea_v a) 56).
    { apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms) (ea_v a) 56 ltac:(lia) ltac:(lia));
      [intros s0 Hs0; apply Hmem1; lia | exact HVRA]. }
    assert (HRAq24 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (ea_q a + 24) 8).
    { apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms) (ea_q a + 24) 8 ltac:(lia) ltac:(lia)).
      - intros s0 Hs0. apply Hmem1; lia.
      - apply (evE_qra a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)
                 (ea_q a + 24) 8 HIMG HPRE HMID); lia. }
    lazymatch type of HS with
    | st_ok_pi _ _ ?EE _ _ =>
      assert (HAG : forall n, (n < 512)%nat -> ew EE n = ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a)
                                                             (PjTree.tag (ea_t a)) str) n)
        by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
    end.
    psrr_branch_tok RUN BR HS SHOK EVE_Bspan.
    * (* v->type <> 3: in->differs := 1 *)
      assert (Htne : PjTree.tag (ea_t a) <> 3).
      { rewrite branch_ne_U, !U_SOff, U_SLit, (HAG 35%nat ltac:(lia)), U35 in Hc.
        rewrite (zcanon_id (PjTree.tag (ea_t a) + 0)) in Hc by (unfold M64; lia).
        rewrite (zcanon_id 3) in Hc by (unfold M64; lia).
        apply negb_true_iff, Z.eqb_neq in Hc. lia. }
      paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EVE_Bspan (EVE_PC 0x9e4).
      -- (* the 4-byte check of in->differs *)
         unfold EVE_Bx. rewrite !U_SOff, (HAG 19%nat ltac:(lia)), (HAG 24%nat ltac:(lia)), U19', U24.
         rewrite (zcanon_id (ea_q a + 32)) by (unfold M64; lia).
         rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
         replace (SHADOW_OFF + 0) with SHADOW_OFF by lia.
         change (rd_of SEGS (rdW W (ms_mem ms))) with (aview SEGS (w_H W) (ms_mem ms)).
         exact HRAq1.
      -- (* the write premise *)
         apply awr_ok_cons_ro; [cbn; lia|].
         eapply awr_ok_cons_gen.
         ++ reflexivity.
         ++ rewrite (HAG 19%nat ltac:(lia)). exact U19'.
         ++ cbn [eve_Rq YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
         ++ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
      -- (* CD with in->differs = 1 *)
         assert (Hmem2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
                   aview SEGS (w_H W) (ms_mem ms0) z = aview SEGS (w_H W) mem z).
         { intros z Hz Hnz. rewrite <- (Hmem1 z Hz Hnz).
           apply (evE_frame_aview _ _ W (ms_mem ms) (ms_mem ms0) z HFr0 Hz).
           intros (r & Hin & Hr). cbn [In] in Hin.
           destruct Hin as [Hin|[Hin|[Hin|[]]]]; subst r;
             cbn [eve_Rs1 eve_Rq eve_Rv YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr;
             rewrite ?(HAG 19%nat ltac:(lia)) in Hr; [lia | rewrite U19' in Hr; lia | lia]. }
         pmkst HS.
         lazymatch type of HS with
         | st_ok_pi _ _ ?EE2 ?ss2 _ =>
           assert (HAE2 : env_agree 32
             (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE2)
             by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; unfold eve_E;
                         apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
           pose proof (regs_kept_of_st_ok_pi EE2 ss2 _ regs
             [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]
             CALLEE_SAVED HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
           let rr := eval vm_compute in (nth_error (ss_mem ss2) 1%nat) in
           lazymatch rr with
           | Some ?r =>
             pose proof (evE_chunk_of_st fxc EE2 ss2 _ W 1%nat r 0%nat 32 4 (SLit 1) HS
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
           end;
           replace (bv_unsigned (sv_denot EE2 (SLit 1))) with 1 in HCH
             by (change (bv_unsigned (sv_denot EE2 (SLit 1))) with (U EE2 (SLit 1));
                 rewrite U_SLit; symmetry; apply zcanon_id; unfold M64; lia)
         end.
         cbn [ms_regs ms_mem restrict base_val YP09.r_base] in HK, HCH.
         rewrite ?ew_ewset_other in HCH by lia. rewrite U19' in HCH.
         apply (evE_goal' fxc W (ms_regs ms0) 0x9e4 (ms_mem ms0)).
         apply (evE_close fxc a W regs (ms_regs ms0) mem (ms_mem ms0) md _ ly S Hp k i1 c j bits 1
                  HIMG KDa HPRE HFX HCC HJ HPM (fun z Hz _ Hnz => Hmem2 z Hz Hnz) HCH HK ltac:(lia)).
         split; [intros _; right; split; [exact Hvn|] | intros _; reflexivity].
         intros Heq. rewrite Heq in Htne. cbn [PjTree.tag] in Htne. lia.
    * (* v->type = 3: __wrap_strcmp (v->str, in->scratch) *)
      assert (Htag3 : PjTree.tag (ea_t a) = 3).
      { rewrite branch_ne_U, !U_SOff, U_SLit, (HAG 35%nat ltac:(lia)), U35 in Hc.
        rewrite (zcanon_id (PjTree.tag (ea_t a) + 0)) in Hc by (unfold M64; lia).
        rewrite (zcanon_id 3) in Hc by (unfold M64; lia).
        apply negb_false_iff, Z.eqb_eq in Hc. lia. }
      paj_run_tok_x_inv RUN HS HJ SHOK HPM EVE_Bspan.
      -- (* the 8-byte check of q + 24 (through the s1 + 96 spill) *)
         unfold EVE_Bx. rewrite !U_SOff, (HAG 19%nat ltac:(lia)), (HAG 24%nat ltac:(lia)), U19', U24.
         rewrite (zcanon_id (ea_q a + 24)) by (unfold M64; lia).
         rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
         replace (SHADOW_OFF + 0) with SHADOW_OFF by lia.
         change (rd_of SEGS (rdW W (ms_mem ms))) with (aview SEGS (w_H W) (ms_mem ms)).
         exact HRAq24.
      -- (* the 8-byte check of v + 16 *)
         unfold EVE_Bx. rewrite !U_SOff, (HAG 32%nat ltac:(lia)), (HAG 24%nat ltac:(lia)), U32, U24.
         rewrite (zcanon_id (ea_v a + 16)) by (unfold M64; lia).
         rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
         replace (SHADOW_OFF + 0) with SHADOW_OFF by lia.
         change (rd_of SEGS (rdW W (ms_mem ms))) with (aview SEGS (w_H W) (ms_mem ms)).
         apply (range_addressable_sub (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (ea_v a) 56
                  (ea_v a + 16) 8 HRAv1 ltac:(lia) ltac:(lia)).
      -- (* the write premise *)
         apply awr_ok_cons_ro; [cbn; lia|].
         eapply awr_ok_cons_gen.
         ++ reflexivity.
         ++ rewrite (HAG 19%nat ltac:(lia)). exact U19'.
         ++ cbn [eve_Rq YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
         ++ apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
      -- (* at the call: __wrap_strcmp (v->str, in->scratch) *)
         pose proof alloc_ceiling_value as [_ HCM]. pose proof cf_head_nonneg as Hch.
         destruct (Hnum3 Htag3) as (txt2 & bits2 & kk & Et & Hlb & Hlen2 & Hcb & Hbits2).
         assert (Hlen3 : ea_len a <= 3 * 2 ^ 20).
         { pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
           destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hl & _). exact Hl. }
         pose proof (evE_lam a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) str kk HMID Hlb
           ltac:(lia)) as (Hs4096 & Hshi & Hkk32 & Hamx & Hrax & Hhullx & Htailx).
         pose proof Hwd as (Hw0 & Hwhi & Hwam & _ & Hwra & Hwhull).
         pose proof (evE_scrblk a HPRE) as Hscr4096.
         destruct Hcb as (Hcr & Gx).
         assert (Hnzx : Forall (fun c => c <> 0) txt2)
           by (eapply Forall_impl; [|exact Hcr]; intros c0 Hc0; cbv beta in Hc0 |- *; lia).
         assert (Hnzy : Forall (fun c => c <> 0) (ev_sub (ea_x a) i1 j)).
         { eapply Forall_impl; [|exact (eve_N_numch _ _ _ _ HN)]. intros c0 Hc0. cbv beta in Hc0 |- *.
           pose proof (eve_numch_nz c0 Hc0). lia. }
         assert (HlenT : Z.of_nat (length (ev_sub (ea_x a) i1 j)) <= ea_len a)
           by (unfold ev_sub, ea_len; rewrite length_firstn, length_skipn; lia).
         assert (HmemC : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a + 32 <= z < ea_q a + 36) ->
                   aview SEGS (w_H W) (ms_mem ms0) z = aview SEGS (w_H W) mem z).
         { intros z Hz Hnz. rewrite <- (Hmem1 z Hz Hnz).
           apply (evE_frame_aview _ _ W (ms_mem ms) (ms_mem ms0) z HFr0 Hz).
           intros (r & Hin & Hr). cbn [In] in Hin.
           destruct Hin as [Hin|[Hin|[Hin|[]]]]; subst r;
             cbn [eve_Rs1 eve_Rq eve_Rv YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr;
             rewrite ?ew_ewset_other in Hr by lia; [lia | rewrite U19' in Hr; lia | lia]. }
         assert (HAc : forall s0, 0 <= s0 < alloc_ceiling ->
                   aview SEGS (w_H W) (ms_mem ms0) s0 = aview SEGS (w_H W) mem s0)
           by (intros s0 Hs0; apply HmemC; lia).
         assert (Gx' : garr8 SEGS (rdW W (ms_mem ms0)) str (txt2 ++ [0])).
         { apply (eve_garr_move SEGS (w_H W) mem (ms_mem ms0)); [|exact Gx].
           intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HmemC; lia. }
         assert (Gy' : garr8 SEGS (rdW W (ms_mem ms0)) (ea_scr a) (ev_sub (ea_x a) i1 j ++ [0])).
         { apply (eve_garr_move SEGS (w_H W) mem (ms_mem ms0)); [|exact Hgarr].
           intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply HmemC; lia. }
         destruct (evE_gptp a HPRE) as [Hgp0 Htp0].
         pmkst HS.
         prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (1%bv : bv 5) Pra.
         prreg HS (2%bv : bv 5) Psp. prreg HS (3%bv : bv 5) Pgp. prreg HS (4%bv : bv 5) Ptp.
         assert (HspT : spZ (ms_regs ms0) = ea_sp0 a + ea_d a + (ea_S1 a - (ea_sp0 a + ea_d a))).
         { unfold spZ. rewrite Psp, (evE_ew regs _ _ _ _ str 2%nat 2%bv eq_refl ltac:(lia)), R2.
           rewrite unsigned_lit_small by lia. lia. }
         eapply SRr_bind.
         { eapply (aj_strcmp_at_xrom (fx := fxc) (SK := SK) SEGS B PST ARx _ _ LAWS (@pa_segs_low _ A_prog_listing PA)
             (SIGMA AS___wrap_strcmp) (SCMP fxc) W (ms_regs ms0) (ms_mem ms0)
             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ str (ea_scr a)
             (Z.of_nat (length txt2)) (Z.of_nat (length (ev_sub (ea_x a) i1 j)))
             (ea_S1 a - (ea_sp0 a + ea_d a)) _ HJ).
           - rewrite Pa0, evE_ew36. reflexivity.
           - rewrite Pa1, evE_ew33. reflexivity.
           - lia.
           - lia.
           - lia.
           - lia.
           - lia.
           - lia.
           - lia.
           - lia.
           - exact HspT.
           - lia.
           - lia.
           - unfold ESTACK. lia.
           - rewrite Pgp, (evE_ew regs _ _ _ _ str 3%nat 3%bv eq_refl ltac:(lia)), R3. exact Hgp0.
           - rewrite Ptp, (evE_ew regs _ _ _ _ str 4%nat 4%bv eq_refl ltac:(lia)), R4. exact Htp0.
           - exact Pra.
           - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
           - exact (eve_first_byte SEGS W (ms_mem ms0) str txt2 Gx' Hnzx).
           - exact (eve_first_byte SEGS W (ms_mem ms0) (ea_scr a) _ Gy' Hnzy).
           - replace (Z.of_nat (length txt2) + 1) with (Z.of_nat (length (txt2 ++ [0])))
               by (rewrite length_app; cbn [length]; lia).
             apply (eve_src_ok SEGS W (ms_regs ms0) (ms_mem ms0) str _ Gx').
             intros a0 Ha0. rewrite length_app in Ha0. cbn [length] in Ha0. rewrite HspT. unfold ESTACK. lia.
           - replace (Z.of_nat (length (ev_sub (ea_x a) i1 j)) + 1)
               with (Z.of_nat (length (ev_sub (ea_x a) i1 j ++ [0]))) by (rewrite length_app; cbn [length]; lia).
             apply (eve_src_ok SEGS W (ms_regs ms0) (ms_mem ms0) (ea_scr a) _ Gy').
             intros a0 Ha0. rewrite length_app in Ha0. cbn [length] in Ha0. rewrite HspT. unfold ESTACK. lia.
           - intros a0 Ha0. unfold ESTACK. lia.
           - intros a0 Ha0. unfold ESTACK. lia.
           - apply (evE_lam_amr8 a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) str kk _ HMID Hlb).
             lia.
           - apply (evE_scr_amr8 a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) _ HPRE HMID).
             lia.
           - apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms0) str (Z.of_nat (length txt2) + 1) ltac:(lia) ltac:(lia) HAc).
             apply (range_addressable_sub _ _ str kk); [exact Hrax | lia | lia].
           - apply (eve_hull_move SEGS (w_H W) mem (ms_mem ms0) str (Z.of_nat (length txt2) + 1) ltac:(lia) ltac:(lia) ltac:(lia) HAc).
             apply (eve_hull_sub _ str kk); [exact Hhullx | lia | lia | lia].
           - apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms0) (ea_scr a) (Z.of_nat (length (ev_sub (ea_x a) i1 j)) + 1) ltac:(lia) ltac:(lia) HAc).
             apply (range_addressable_sub _ _ (ea_scr a) (ea_len a + 1)); [exact Hwra | lia | lia].
           - apply (eve_hull_move SEGS (w_H W) mem (ms_mem ms0) (ea_scr a) (Z.of_nat (length (ev_sub (ea_x a) i1 j)) + 1) ltac:(lia) ltac:(lia) ltac:(lia) HAc).
             apply (eve_hull_sub _ (ea_scr a) (ea_len a + 1)); [exact (Hwhull ltac:(lia)) | lia | lia | lia].
           - intros a0 Ha0. rewrite HmemC by lia. apply Htailx. lia.
           - intros a0 Ha0. rewrite HmemC by lia.
             apply (evE_scrtail a ly S Hp W mem md k _ _ _ HPRE HMID). lia.
           - (* the read-only bytes: fpre's, carried to the cut (evE_rod) and to the call (nothing below
                alloc_ceiling written) *)
             exact (evE_rod_move W W mem (ms_mem ms0) (evE_rod a ly S Hp W mem md k _ _ _ HPRE HMID) HAc). }
         cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & rv & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2 & HKM2).
         (* the call's keep: P at the memory after strcmp *)
         pose proof (HKM2 HPM) as HPM2.
         pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2J & _).
         assert (Hcmp' : rv = w64 0 <-> txt2 = ev_sub (ea_x a) i1 j).
         { rewrite Hcmp. exact (eve_str_eq SEGS (w_H W) (ms_mem ms0) str (ea_scr a) txt2 _ Gx' Gy'). }
         assert (HA2 : forall s0, 0 <= s0 < alloc_ceiling ->
                   aview SEGS (w_H W) mem2 s0 = aview SEGS (w_H W) mem s0).
         { intros s0 Hs0. rewrite (Hfr2 s0 ltac:(lia) ltac:(unfold ESTACK; lia)). apply HAc. exact Hs0. }
         assert (Hmem2c : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                   ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem z).
         { intros z Hz Hw Hq. rewrite (Hfr2 z Hz ltac:(unfold ESTACK; lia)). apply HmemC; assumption. }
         let EE := lazymatch type of HS with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
           assert (HEIc : img_env VAL A_LIM EE) by (repeat (apply evE_img_ewset; [|lia]); apply evE_env);
           assert (HAEc : env_agree 32
             (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE)
             by (repeat (apply evE_agree_ewset; [|lia]); exact HAE).
         jafter_call_keep_pi HS 48%nat regs2 (mrestrict (w_H W) mem2) HP2 [0;1]%nat HSX.
         lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
         { constructor; [|constructor; [|apply Forall_nil]]; split.
           - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz.
             rewrite ?ew_ewset_other in Hz by lia.
             rewrite (evE_ew regs _ _ _ _ str 9%nat 9%bv eq_refl ltac:(lia)), R9 in Hz.
             rewrite unsigned_lit_small in Hz by lia.
             apply (mbyte_of_aview SEGS). apply Hfr2; [lia | unfold ESTACK; lia].
           - intros z Hz. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. exfalso. lia.
           - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz.
             rewrite ?ew_ewset_other in Hz by lia. rewrite U19' in Hz.
             apply (mbyte_of_aview SEGS). apply Hfr2; [lia | unfold ESTACK; lia].
           - intros z Hz _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz.
             rewrite ?ew_ewset_other in Hz by lia. rewrite U19' in Hz.
             apply (apresent_writable SEGS). apply Hpres2J. lia. }
         specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
         let E1 := lazymatch type of HSX with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
           assert (HEIs1 : img_env VAL A_LIM E1) by (apply img_env_havoc; [exact HEIc | cbv; lia]);
           assert (HAEs1 : env_agree 32
             (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) E1)
             by (apply env_agree_havoc_ge; [cbv; lia | exact HAEc]);
           assert (Es1a0 : ew E1 52 = rv) by (rewrite <- Hres; reflexivity);
           assert (SHOKs1 : sh_ok SEGS EVE_Bx eve_SH E1 (rdW W mem2)) by (unfold sh_ok, eve_SH; apply Forall_nil).
         clear HS HJ SHOK HPM. rename HSX into HS. rename HJ2 into HJ. rename SHOKs1 into SHOK. rename HPM2 into HPM.
         paj_run_tok_x_inv RUN HS HJ SHOK HPM EVE_Bspan.
         { apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
           - reflexivity.
           - evE_ewn. exact U19'.
           - cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
           - apply awr_ok_nil. }
         assert (Hmem1c : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                   ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms1) z = aview SEGS (w_H W) mem z).
         { intros z Hz Hw Hq. rewrite <- (Hmem2c z Hz Hw Hq).
           apply (evE_frame_aview _ _ W mem2 (ms_mem ms1) z HFr1 Hz).
           intros (r & Hin & Hr). cbn [In] in Hin.
           destruct Hin as [Hin|[Hin|[]]]; subst r;
             cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
             [lia | rewrite U19' in Hr; lia]. }
         psrr_branch_tok RUN BR HS SHOK EVE_Bspan.
         ++ (* strcmp <> 0: in->differs := 1 *)
            lazymatch goal with Hb : branch_taken BC_NE (sv_denot ?E (SOff 52 0)) _ = true |- _ =>
              pose proof (evE_br_ne_t E 52 rv ltac:(evE_ewn; exact Es1a0) Hb) as Hrv0 end.
            assert (Hne : txt2 <> ev_sub (ea_x a) i1 j) by (intro Heq; apply Hrv0; apply Hcmp'; exact Heq).
            assert (HRAq2 : range_addressable (aview SEGS (w_H W) (ms_mem ms1)) SHADOW_OFF (ea_q a + 32) 4).
            { apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms1) (ea_q a + 32) 4 ltac:(lia) ltac:(lia)).
              - intros s0 Hs0. apply Hmem1c; lia.
              - apply (evE_qra a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)
                   (ea_q a + 32) 4 HIMG HPRE HMID); lia. }
            paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EVE_Bspan (EVE_PC 0x9e4).
            ** unfold EVE_Bx. rewrite !U_SOff. evE_ewn. rewrite U19', U24.
               rewrite (zcanon_id (ea_q a + 32)) by (unfold M64; lia).
               rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
               replace (SHADOW_OFF + 0) with SHADOW_OFF by lia. exact HRAq2.
            ** apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
               --- reflexivity.
               --- evE_ewn. exact U19'.
               --- cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
               --- apply awr_ok_nil.
            ** assert (Hmem3 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                   ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms2) z = aview SEGS (w_H W) mem z).
               { intros z Hz Hw Hq. rewrite <- (Hmem1c z Hz Hw Hq).
                 apply (evE_frame_aview _ _ W (ms_mem ms1) (ms_mem ms2) z HFr2 Hz).
                 intros (r & Hin & Hr). cbn [In] in Hin.
                 destruct Hin as [Hin|[Hin|[]]]; subst r;
                   cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
                   [lia | rewrite U19' in Hr; lia]. }
               pmkst HS.
               let EE2 := lazymatch type of HS with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
               let ss2 := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => s | st_ok _ _ ?s _ => s end in
               (assert (HAE2 : env_agree 32
                  (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE2)
                  by (repeat (apply evE_agree_ewset; [|lia]); exact HAEs1);
                pose proof (regs_kept_of_st_ok_pi EE2 ss2 _ regs
                  [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]
                  CALLEE_SAVED HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
                let rr := eval vm_compute in (nth_error (ss_mem ss2) 1%nat) in
                lazymatch rr with
                | Some ?r =>
                  pose proof (evE_chunk_of_st fxc EE2 ss2 _ W 1%nat r 0%nat 32 4 (SLit 1) HS
                    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
                end;
                replace (bv_unsigned (sv_denot EE2 (SLit 1))) with 1 in HCH
                  by (change (bv_unsigned (sv_denot EE2 (SLit 1))) with (U EE2 (SLit 1));
                      rewrite U_SLit; symmetry; apply zcanon_id; unfold M64; lia)).
               cbn [ms_regs ms_mem restrict base_val YP09.r_base] in HK, HCH.
               evE_ewn_in HCH. rewrite U19' in HCH.
               apply (evE_goal' fxc W (ms_regs ms2) 0x9e4 (ms_mem ms2)).
               apply (evE_close fxc a W regs (ms_regs ms2) mem (ms_mem ms2) md _ ly S Hp k i1 c j bits 1
                        HIMG KDa HPRE HFX HCC HJ HPM Hmem3 HCH HK ltac:(lia)).
               split; [intros _; right; split; [exact Hvn|] | intros _; reflexivity].
               rewrite Et. intro Heq. injection Heq as E1 _. exact (Hne E1).
         ++ (* strcmp = 0: __wrap_bcmp (v + 8, fr + 64, 8) *)
            lazymatch goal with Hb : branch_taken BC_NE (sv_denot ?E (SOff 52 0)) _ = false |- _ =>
              pose proof (evE_br_ne_f E 52 rv ltac:(evE_ewn; exact Es1a0) Hb) as Hrv0 end.
            pose proof (proj1 Hcmp' Hrv0) as Heqt.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM EVE_Bspan.
            { apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
              - reflexivity.
              - evE_ewn. exact U19'.
              - cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
              - apply awr_ok_nil. }
            assert (HmemB : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                   ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms2) z = aview SEGS (w_H W) mem z).
            { intros z Hz Hw Hq. rewrite <- (Hmem1c z Hz Hw Hq).
              apply (evE_frame_aview _ _ W (ms_mem ms1) (ms_mem ms2) z HFr2 Hz).
              intros (r & Hin & Hr). cbn [In] in Hin.
              destruct Hin as [Hin|[Hin|[]]]; subst r;
                cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
                [lia | rewrite U19' in Hr; lia]. }
            assert (HAB : forall s0, 0 <= s0 < alloc_ceiling ->
                      aview SEGS (w_H W) (ms_mem ms2) s0 = aview SEGS (w_H W) mem s0)
              by (intros s0 Hs0; apply HmemB; lia).
            assert (hv_stack : forall z, ea_v a <= z < ea_v a + 56 -> ~ (ea_sp0 a - ea_STK a <= z < ea_sp0 a)).
            { intros z Hz. destruct (Hfoot z ltac:(left; lia)) as (_ & _ & Hs' & _). exact Hs'. }
            pose proof (eve_N_bits _ _ _ _ HN) as Rb.
            pose proof Hbits2 as (Rb2 & _).
            assert (Vb2 : val_mem SEGS (rdW W (ms_mem ms2)) (ea_v a + 8) 8 bits2).
            { apply (eve_val_move SEGS (w_H W) mem (ms_mem ms2)); [|exact (proj2 Hbits2)].
              intros i Hi. pose proof (hv_stack (ea_v a + 8 + i) ltac:(lia)). apply HmemB; lia. }
            assert (Vf2 : val_mem SEGS (rdW W (ms_mem ms2)) (ea_fr a + 64) 8 bits).
            { apply (eve_val_move SEGS (w_H W) mem (ms_mem ms2)); [|exact Cnum].
              intros i Hi. apply HmemB; lia. }
            destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md 1 (ea_pos a) HAR HIN1)
              as (Hfr32 & Hfrapp & _ & Hfsh).
            rewrite HFR in Hfr32, Hfrapp, Hfsh.
            pmkst HS.
            prreg HS (10%bv : bv 5) Pb0. prreg HS (11%bv : bv 5) Pb1. prreg HS (12%bv : bv 5) Pb2.
            prreg HS (1%bv : bv 5) Pbra. prreg HS (2%bv : bv 5) Pbsp.
            prreg HS (3%bv : bv 5) Pbgp. prreg HS (4%bv : bv 5) Pbtp.
            assert (HspB : spZ (ms_regs ms2) = ea_sp0 a + ea_d a + (ea_S1 a - (ea_sp0 a + ea_d a))).
            { unfold spZ. rewrite Pbsp, (evE_ew regs _ _ _ _ str 2%nat 2%bv eq_refl ltac:(lia)), R2.
              rewrite unsigned_lit_small by lia. lia. }
            assert (U18 : bv_unsigned (ew (eve_E regs (ea_v a) (ea_scr a) (ea_dl a) (PjTree.tag (ea_t a)) str) 18)
                          = ea_fr a).
            { rewrite (evE_ew regs _ _ _ _ str 18%nat 18%bv eq_refl ltac:(lia)), R18.
              apply unsigned_lit_small. lia. }
            pose proof (evE_vhull a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a) HMID Hvn)
              as Hvhull.
            eapply SRr_bind.
            { eapply (aj_bcmp_at_xm (fx := fxc) (SK := SK) SEGS B PST ARx LAWS (@pa_segs_low _ A_prog_listing PA)
                (SIGMA AS___wrap_bcmp) (BCMP fxc) W (ms_regs ms2) (ms_mem ms2)
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ea_v a + 8) (ea_fr a + 64) 8
                (ea_S1 a - (ea_sp0 a + ea_d a)) _ HJ).
              - rewrite Pb0, U32. reflexivity.
              - rewrite Pb1, U18. reflexivity.
              - rewrite Pb2. reflexivity.
              - lia.
              - lia.
              - lia.
              - lia.
              - lia.
              - exact HspB.
              - lia.
              - lia.
              - unfold ESTACK. lia.
              - rewrite Pbgp, (evE_ew regs _ _ _ _ str 3%nat 3%bv eq_refl ltac:(lia)), R3. exact Hgp0.
              - rewrite Pbtp, (evE_ew regs _ _ _ _ str 4%nat 4%bv eq_refl ltac:(lia)), R4. exact Htp0.
              - exact Pbra.
              - apply (ret_ok_codeptr_v (PI := PA)); [lia | reflexivity].
              - intros a0 Ha0. split.
                + replace a0 with (ea_v a + 8 + Z.of_nat (Z.to_nat (a0 - (ea_v a + 8)))) by lia.
                  rewrite (eve_val8_aview SEGS (w_H W) (ms_mem ms2) (ea_v a + 8) bits2 _ Vb2) by lia. discriminate.
                + pose proof (hv_stack a0 ltac:(lia)). rewrite HspB. unfold ESTACK. lia.
              - intros a0 Ha0. split.
                + replace a0 with (ea_fr a + 64 + Z.of_nat (Z.to_nat (a0 - (ea_fr a + 64)))) by lia.
                  rewrite (eve_val8_aview SEGS (w_H W) (ms_mem ms2) (ea_fr a + 64) bits _ Vf2) by lia. discriminate.
                + rewrite HspB. unfold ESTACK. lia.
              - intros a0 Ha0. pose proof (hv_stack a0 ltac:(lia)). unfold ESTACK. lia.
              - intros a0 Ha0. unfold ESTACK. lia.
              - exact (evE_vamem8 a ly S Hp W mem md k _ _ _ HIMG HPRE HMID Hvn).
              - apply eve_in_app_amem. apply (in_app_sub _ _ _ _ Hfrapp); change (fs_frame_bytes 1) with 128; lia.
              - apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms2) (ea_v a + 8) 8 ltac:(lia) ltac:(lia) HAB).
                apply (range_addressable_sub _ _ (ea_v a) 56); [exact HVRA | lia | lia].
              - intros _. apply (eve_hull_move SEGS (w_H W) mem (ms_mem ms2) (ea_v a + 8) 8 ltac:(lia) ltac:(lia) ltac:(lia) HAB).
                apply (eve_hull_sub _ (ea_v a) 56); [exact Hvhull | lia | lia | lia].
              - intros x0 Hx0. exists 0. split; [|left; reflexivity].
                replace (shadow_of_addr SHADOW_OFF x0) with (shadow_addr (ea_fr a) + 8)
                  by (unfold shadow_of_addr, shadow_addr; lia).
                rewrite HAB by (unfold shadow_addr, SHADOW_OFF; lia). exact (proj2 HFSH).
              - intros _ s0 Hs0. unfold shadow_addr in Hs0. rewrite HAB by (unfold SHADOW_OFF in *; lia).
                apply (eve_apresent_aview SEGS).
                replace s0 with (shadow_addr (ea_fr a) + (s0 - shadow_addr (ea_fr a))) by lia.
                apply (proj1 (Hfsh (s0 - shadow_addr (ea_fr a))
                  ltac:(change (fs_frame_bytes 1 / 8) with 16; unfold shadow_addr, SHADOW_OFF in *; lia))). }
            cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & rv2 & -> & HJ3 & HP3 & Hres2 & Hcmp2 & Hfr3 & Hpres3 &
              HKM3).
            (* the call's keep: P at the memory after bcmp *)
            pose proof (HKM3 HPM) as HPM3.
            pose proof HJ3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3J & _).
            assert (Hcmp2' : rv2 = w64 0 <-> bits2 = bits).
            { rewrite Hcmp2. exact (eve_bytes_eq8 SEGS (w_H W) (ms_mem ms2) (ea_v a + 8) (ea_fr a + 64) bits2 bits
                Rb2 Rb Vb2 Vf2). }
            assert (Hmem3c : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                      ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) mem3 z = aview SEGS (w_H W) mem z).
            { intros z Hz Hw Hq. rewrite (Hfr3 z Hz ltac:(unfold ESTACK; lia)). apply HmemB; assumption. }
            let EE := lazymatch type of HS with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
              assert (HEIc2 : img_env VAL A_LIM EE) by (repeat (apply evE_img_ewset; [|lia]); exact HEIs1);
              assert (HAEc2 : env_agree 32
                (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE)
                by (repeat (apply evE_agree_ewset; [|lia]); exact HAEs1).
            jafter_call_keep_pi HS 64%nat regs3 (mrestrict (w_H W) mem3) HP3 [0;1]%nat HSX.
            lazymatch type of HSX with ?T -> _ => assert (HRKX : T) end.
            { constructor; [|constructor; [|apply Forall_nil]]; split.
              - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz. evE_ewn_in Hz.
                rewrite (evE_ew regs _ _ _ _ str 9%nat 9%bv eq_refl ltac:(lia)), R9 in Hz.
                rewrite unsigned_lit_small in Hz by lia.
                apply (mbyte_of_aview SEGS). apply Hfr3; [lia | unfold ESTACK; lia].
              - intros z Hz. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. exfalso. lia.
              - intros z Hz. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Hz. evE_ewn_in Hz. rewrite U19' in Hz.
                apply (mbyte_of_aview SEGS). apply Hfr3; [lia | unfold ESTACK; lia].
              - intros z Hz _. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hz. evE_ewn_in Hz.
                rewrite U19' in Hz. apply (apresent_writable SEGS). apply Hpres3J. lia. }
            specialize (HSX HRKX). clear HRKX. rewrite <- restrict_mkst_fx in HSX.
            let E2 := lazymatch type of HSX with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
              assert (HEIs2 : img_env VAL A_LIM E2) by (apply img_env_havoc; [exact HEIc2 | cbv; lia]);
              assert (HAEs2 : env_agree 32
                (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) E2)
                by (apply env_agree_havoc_ge; [cbv; lia | exact HAEc2]);
              assert (Es2a0 : ew E2 68 = rv2) by (rewrite <- Hres2; reflexivity);
              assert (SHOKs2 : sh_ok SEGS EVE_Bx eve_SH E2 (rdW W mem3)) by (unfold sh_ok, eve_SH; apply Forall_nil).
            clear HS HJ SHOK HPM. rename HSX into HS. rename HJ3 into HJ. rename SHOKs2 into SHOK. rename HPM3 into HPM.
            paj_run_tok_x_inv RUN HS HJ SHOK HPM EVE_Bspan.
            { apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
              - reflexivity.
              - evE_ewn. exact U19'.
              - cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
              - apply awr_ok_nil. }
            assert (Hmem4 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                   ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms3) z = aview SEGS (w_H W) mem z).
            { intros z Hz Hw Hq. rewrite <- (Hmem3c z Hz Hw Hq).
              apply (evE_frame_aview _ _ W mem3 (ms_mem ms3) z HFr3 Hz).
              intros (r & Hin & Hr). cbn [In] in Hin.
              destruct Hin as [Hin|[Hin|[]]]; subst r;
                cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
                [lia | rewrite U19' in Hr; lia]. }
            psrr_branch_tok RUN BR HS SHOK EVE_Bspan.
            ** (* bcmp = 0: the trees agree, in->differs kept *)
               lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?E (SOff 68 0)) _ = true |- _ =>
                 pose proof (evE_br_eq_t E 68 rv2 ltac:(evE_ewn; exact Es2a0) Hb) as Hrv2 end.
               pose proof (proj1 Hcmp2' Hrv2) as Hbeq.
               paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EVE_Bspan (EVE_PC 0x9e4).
               --- apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
                   +++ reflexivity.
                   +++ evE_ewn. exact U19'.
                   +++ cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
                   +++ apply awr_ok_nil.
               --- assert (Hmem5 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                      ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms4) z = aview SEGS (w_H W) mem z).
                   { intros z Hz Hw Hq. rewrite <- (Hmem4 z Hz Hw Hq).
                     apply (evE_frame_aview _ _ W (ms_mem ms3) (ms_mem ms4) z HFr4 Hz).
                     intros (r & Hin & Hr). cbn [In] in Hin.
                     destruct Hin as [Hin|[Hin|[]]]; subst r;
                       cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
                       [lia | rewrite U19' in Hr; lia]. }
                   pmkst HS.
                   let EE2 := lazymatch type of HS with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
                   let ss2 := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => s | st_ok _ _ ?s _ => s end in
                   (assert (HAE2 : env_agree 32
                      (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE2)
                      by (repeat (apply evE_agree_ewset; [|lia]); exact HAEs2);
                    pose proof (regs_kept_of_st_ok_pi EE2 ss2 _ regs
                      [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]
                      CALLEE_SAVED HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
                    let rr := eval vm_compute in (nth_error (ss_mem ss2) 1%nat) in
                    lazymatch rr with
                    | Some ?r =>
                      first [ pose proof (evE_chunk_of_st fxc EE2 ss2 _ W 1%nat r 1%nat 32 4 (SOff 34 0) HS
                                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
                            | pose proof (evE_chunk_of_st fxc EE2 ss2 _ W 1%nat r 0%nat 32 4 (SOff 34 0) HS
                                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH ]
                    end;
                    replace (bv_unsigned (sv_denot EE2 (SOff 34 0))) with (ea_dl a) in HCH
                      by (change (bv_unsigned (sv_denot EE2 (SOff 34 0))) with (U EE2 (SOff 34 0));
                          rewrite U_SOff; evE_ewn; rewrite evE_ew34;
                          rewrite unsigned_lit_small by lia; rewrite Z.add_0_r; symmetry; apply zcanon_id; unfold M64; lia)).
                   cbn [ms_regs ms_mem restrict base_val YP09.r_base] in HK, HCH.
                   evE_ewn_in HCH. rewrite U19' in HCH.
                   apply (evE_goal' fxc W (ms_regs ms4) 0x9e4 (ms_mem ms4)).
                   apply (evE_close fxc a W regs (ms_regs ms4) mem (ms_mem ms4) md _ ly S Hp k i1 c j bits (ea_dl a)
                            HIMG KDa HPRE HFX HCC HJ HPM Hmem5 HCH HK Hdl01).
                   split; [intros H1; left; exact H1|].
                   intros [H1|(_ & Hne)]; [exact H1|]. exfalso. apply Hne. rewrite Et, Heqt, Hbeq. reflexivity.
            ** (* bcmp <> 0: in->differs := 1 *)
               lazymatch goal with Hb : branch_taken BC_EQ (sv_denot ?E (SOff 68 0)) _ = false |- _ =>
                 pose proof (evE_br_eq_f E 68 rv2 ltac:(evE_ewn; exact Es2a0) Hb) as Hrv2 end.
               assert (Hbne : bits2 <> bits) by (intro Heq; apply Hrv2; apply Hcmp2'; exact Heq).
               assert (HRAq4 : range_addressable (aview SEGS (w_H W) (ms_mem ms3)) SHADOW_OFF (ea_q a + 32) 4).
               { apply (eve_ra_move SEGS (w_H W) mem (ms_mem ms3) (ea_q a + 32) 4 ltac:(lia) ltac:(lia)).
                 - intros s0 Hs0. apply Hmem4; lia.
                 - apply (evE_qra a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a) (ea_dl a)
                      (ea_q a + 32) 4 HIMG HPRE HMID); lia. }
               paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM EVE_Bspan (EVE_PC 0x9e4).
               --- unfold EVE_Bx. rewrite !U_SOff. evE_ewn. rewrite U19', U24.
                   rewrite (zcanon_id (ea_q a + 32)) by (unfold M64; lia).
                   rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
                   replace (SHADOW_OFF + 0) with SHADOW_OFF by lia. exact HRAq4.
               --- apply awr_ok_cons_ro; [cbn; lia|]. eapply awr_ok_cons_gen.
                   +++ reflexivity.
                   +++ evE_ewn. exact U19'.
                   +++ cbn [YP09.r_wlo YP09.r_whi]. intros z Hz. left. lia.
                   +++ apply awr_ok_nil.
               --- assert (Hmem5 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a - 8192 <= z < ea_S1 a) ->
                      ~ (ea_q a + 32 <= z < ea_q a + 36) -> aview SEGS (w_H W) (ms_mem ms4) z = aview SEGS (w_H W) mem z).
                   { intros z Hz Hw Hq. rewrite <- (Hmem4 z Hz Hw Hq).
                     apply (evE_frame_aview _ _ W (ms_mem ms3) (ms_mem ms4) z HFr4 Hz).
                     intros (r & Hin & Hr). cbn [In] in Hin.
                     destruct Hin as [Hin|[Hin|[]]]; subst r;
                       cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hr; evE_ewn_in Hr;
                       [lia | rewrite U19' in Hr; lia]. }
                   pmkst HS.
                   let EE2 := lazymatch type of HS with st_ok_pi _ _ ?E _ _ => E | st_ok _ ?E _ _ => E end in
                   let ss2 := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => s | st_ok _ _ ?s _ => s end in
                   (assert (HAE2 : env_agree 32
                      (Ereg regs [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]) EE2)
                      by (repeat (apply evE_agree_ewset; [|lia]); exact HAEs2);
                    pose proof (regs_kept_of_st_ok_pi EE2 ss2 _ regs
                      [w64 (ea_v a); w64 (ea_scr a); w64 (ea_dl a); w64 (PjTree.tag (ea_t a)); w64 str]
                      CALLEE_SAVED HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
                    let rr := eval vm_compute in (nth_error (ss_mem ss2) 1%nat) in
                    lazymatch rr with
                    | Some ?r =>
                      pose proof (evE_chunk_of_st fxc EE2 ss2 _ W 1%nat r 0%nat 32 4 (SLit 1) HS
                        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(cbv; discriminate)) as HCH
                    end;
                    replace (bv_unsigned (sv_denot EE2 (SLit 1))) with 1 in HCH
                      by (change (bv_unsigned (sv_denot EE2 (SLit 1))) with (U EE2 (SLit 1));
                          rewrite U_SLit; symmetry; apply zcanon_id; unfold M64; lia)).
                   cbn [ms_regs ms_mem restrict base_val YP09.r_base] in HK, HCH.
                   evE_ewn_in HCH. rewrite U19' in HCH.
                   apply (evE_goal' fxc W (ms_regs ms4) 0x9e4 (ms_mem ms4)).
                   apply (evE_close fxc a W regs (ms_regs ms4) mem (ms_mem ms4) md _ ly S Hp k i1 c j bits 1
                            HIMG KDa HPRE HFX HCC HJ HPM Hmem5 HCH HK ltac:(lia)).
                   split; [intros _; right; split; [exact Hvn|] | intros _; reflexivity].
                   rewrite Et. intro Heq. injection Heq as _ E2. exact (Hbne E2).
Qed.

End w.
