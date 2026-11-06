(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACes.v:275-277
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhg.v:439 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:707-710, 1570-1572 [Apache-2.0 OR MIT], for libreac/fuzz_identity's
   asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, AF_reac_box_name = 0x2600): two segments of its program
   walk, stated between the cut points of lib/B/Prog/reac_box_name_inv.v:
     rbn_seg_c1_c2  C1 0x83000 (+0x28c) -> C2 0x83088 (+0x314), i = 0: the two sb_dec calls that fill wb with
                    w4 (0x8300c, 0x8301c), w4's NUL (0x83038), nm's scope and struct (0x83040..0x83060) and
                    the first character of the stem (0x83064..0x83084);
     rbn_seg_c3_c45 C3 0x830cc (+0x358) -> C4 0x83128 (+0x3b4), j = 0, or C5 0x8316c (+0x3f8): the suffix test
                    (strlen 0x830dc, bcmp 0x83104) and, when it fails, sb_ch(nb, '-') (0x83114).
   Form: cgif lib/A/AC8b.v tcbb_loopX (the state at a cut point as machine registers and memory facts), with
   the caller-journal shapes of lib/B/Prog/IdentBCJ.v. The runs between the calls are the plain engine
   (lib/B/Prog/IdentBFrame.v SRr_run_pi_AJ / YC45.v SRr_run_pi_AJ_call); the one shadow-checked read (the
   stem's first byte, 0x83064) is the token engine (lib/B/Prog/IdentBPaLib.v paj_run_to_tok).
   The UBSan pointer-overflow traps at 0x83024, 0x8302c, 0x830e8 and 0x830f4 are dead; each is decided inside
   its run from a condition the entry state carries. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI08 YI09 YI0s YI0t YI0m YI0n YP0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBProgSig IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef WrapRo.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import sb_ch sb_dec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import reac_box_name_sbm reac_box_name_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import disco_box_name_model.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_name_c sb_dec_c box_name_lemmas.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* #[local]: this flag must not leak to files that Require this one. *)
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section h.
Variable B : asyms.
Variable G : list (Z * Z).
Section walk.
Context {RO : ro_below_ofl SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI)}.
Hypothesis TL : PALib B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis TLF : PALibF B.
Hypothesis GM : globs_marked SEGS B G.
Hypothesis IV : img_shadow_vis SEGS B.
Hypothesis PSIG : identb_prog_sig_ok.
Hypothesis HSC : tsb_ch_spec B.
Hypothesis HSB : tsb_dec_spec B.
(* the memset of the struct initialisation at 0x83060 *)
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
(* the bcmp wrapper of the suffix test (0x83104) *)
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA IB___interceptor_trampoline_bcmp).
(* the strlen wrapper of the suffix test (0x830dc); its read-only premise aro_unowned (lib/B/Rt/WrapRo.v)
   comes from the journal-kept arodata_okP of rbn_pre by aro_unowned_of_arodata. *)
Hypothesis ASTRLEN : astrlen_realizes SEGS B (SIGMA IB___interceptor_trampoline_strlen).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* ============================================================================================
   Part A: the geometry of a cut point, what a step keeps, and the facts that cross a step.
   ============================================================================================ *)
(* The stack of reac_box_name (lib/B/Prog/reac_box_name.v REAC_BOX_NAME_STK; that file chains the segments,
   so it cannot be required here). *)
Local Notation RBN_STK := (336 + 2 * ESTACK).

(* ---- A0. the live heap bytes are a function of the block list ---- *)
Lemma rbn_bsum_perm : forall l1 l2 : list (Z * Z), Permutation l1 l2 -> bsum l1 = bsum l2.
Proof.
intros l1 l2 H. induction H as [| x l1 l2 _ IH | x y l | l1 l2 l3 _ IH1 _ IH2];
  rewrite ?bsum_cons; lia.
Qed.
Lemma rbn_live_bytes : forall ly1 S1 ly2 S2,
  Permutation (ablocks B ly1 S1) (ablocks B ly2 S2) -> blocks_bytes S1 = blocks_bytes S2.
Proof.
intros ly1 S1 ly2 S2 H.
rewrite (blocks_bytes_bsum B ly1 S1), (blocks_bytes_bsum B ly2 S2). exact (rbn_bsum_perm _ _ H).
Qed.

(* ---- A1. what a run or a call kept: the four classes of bytes the cut points speak about ---- *)
Definition rbn_k (c : rbx) (lyc : alayout) (Sc : astate) (m1 m2 : word -> option byte) (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ E a ->
     aview SEGS (w_H (x_W c)) m2 a = aview SEGS (w_H (x_W c)) m1 a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H (x_W c)) m2 (b + i) = aview SEGS (w_H (x_W c)) m1 (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H (x_W c)) m2 a = aview SEGS (w_H (x_W c)) m1 a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H (x_W c)) m2 a = aview SEGS (w_H (x_W c)) m1 a).
Lemma rbn_k_mono : forall c lyc Sc m1 m2 (E E' : Z -> Prop),
  rbn_k c lyc Sc m1 m2 E -> (forall a, E a -> E' a) -> rbn_k c lyc Sc m1 m2 E'.
Proof.
intros c lyc Sc m1 m2 E E' (A1 & A2 & A3 & A4) HE.
split; [intros a Ha He; apply A1; [exact Ha | intros X; exact (He (HE a X))]|].
split; [intros b m i Hin Hi He; apply (A2 b m i Hin Hi); intros X; exact (He (HE (b + i) X))|].
split; [exact A3|].
intros cid pos a Hin Hr He. apply (A4 cid pos a Hin Hr). intros X. exact (He (HE a X)).
Qed.
Lemma rbn_k_trans : forall c lyc Sc m1 m2 m3 (E1 E2 : Z -> Prop),
  rbn_k c lyc Sc m1 m2 E1 -> rbn_k c lyc Sc m2 m3 E2 -> rbn_k c lyc Sc m1 m3 (fun a => E1 a \/ E2 a).
Proof.
intros c lyc Sc m1 m2 m3 E1 E2 (A1 & A2 & A3 & A4) (C1 & C2 & C3 & C4).
split; [intros a Ha He; rewrite (C1 a Ha ltac:(tauto)); exact (A1 a Ha ltac:(tauto))|].
split; [intros b m i Hin Hi He; rewrite (C2 b m i Hin Hi ltac:(tauto)); exact (A2 b m i Hin Hi ltac:(tauto))|].
split; [intros a Hi Hs He; rewrite (C3 a Hi Hs He); exact (A3 a Hi Hs He)|].
intros cid pos a Hin Hr He. rewrite (C4 cid pos a Hin Hr ltac:(tauto)). exact (A4 cid pos a Hin Hr ltac:(tauto)).
Qed.
(* a later state with the same blocks and frames reports the same keeping *)
Lemma rbn_k_move : forall c ly1 S1 ly2 S2 m1 m2 E,
  rbn_k c ly2 S2 m1 m2 E -> Permutation (ablocks B ly2 S2) (ablocks B ly1 S1) -> frames S2 = frames S1 ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr ly1 cid pos) ->
  rbn_k c ly1 S1 m1 m2 E.
Proof.
intros c ly1 S1 ly2 S2 m1 m2 E (A1 & A2 & A3 & A4) Hp Hf Hfa.
split; [exact A1|].
split; [intros b m i Hin Hi He; exact (A2 b m i (Permutation_in _ (Permutation_sym Hp) Hin) Hi He)|].
split; [exact A3|].
intros cid pos a Hin Hr He. apply (A4 cid pos a); [rewrite Hf; exact Hin | | exact He].
unfold frame_rng in *. cbn [fst snd] in *. rewrite !Hfa. exact Hr.
Qed.
(* a callee's tcj_kept is one, with the callee's stack window added to the written bytes *)
Lemma rbn_k_of_tcj : forall c STK1 lyc Sc m1 m2 sp E,
  tcj_kept B STK1 lyc Sc (x_W c) m1 (x_W c) m2 sp E ->
  rbn_k c lyc Sc m1 m2 (fun a => (sp - STK1 <= a < sp) \/ E a).
Proof.
intros c STK1 lyc Sc m1 m2 sp E (A1 & A2 & A3 & A4 & _ & _).
split; [intros a Ha He; apply A1; [exact Ha | tauto | tauto]|].
split; [intros b m i Hin Hi He; apply (A2 b m i Hin Hi); tauto|].
split; [exact A3|].
intros cid pos a Hin Hr He. apply (A4 cid pos a Hin Hr). tauto.
Qed.
(* a run, or a runtime call, that changed nothing outside [lo, hi) and E *)
Lemma rbn_k_of_plain : forall c lyc Sc memc mdc m1 m2 lo hi (E : Z -> Prop),
  AR SEGS B lyc Sc (x_W c) memc mdc -> alloc_ceiling <= lo -> hi <= 2 ^ 64 ->
  (forall a, in_img SEGS a -> ~ (lo <= a < hi) /\ ~ E a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ E a ->
     aview SEGS (w_H (x_W c)) m2 a = aview SEGS (w_H (x_W c)) m1 a) ->
  rbn_k c lyc Sc m1 m2 (fun a => (lo <= a < hi) \/ E a).
Proof.
intros c lyc Sc memc mdc m1 m2 lo hi E HAR Hlo Hhi Himg KV.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [intros a Ha He; apply KV; [lia | tauto | tauto]|].
split.
{ intros b m i Hin Hi He. destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR Hin) as (_ & H4096 & Hcl & _).
  apply KV; [lia | tauto | tauto]. }
split.
{ intros a Hi Hns Herr. pose proof (pa_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
  destruct (Himg a Hi) as [X1 X2]. apply KV; [lia | exact X1 | exact X2]. }
intros cid pos a Hin Hr He.
destruct (frame_zone SEGS B LAWS _ _ _ _ _ cid pos a HAR Hin Hr) as (Hza & [(Hz1 & _) | Hz2]);
  [destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HAR Hin) as (Hf0 & _ & _)|];
  (apply KV; [unfold kLowMemEnd in *; lia | tauto | tauto]).
Qed.

(* ---- A2. the facts of a cut point, carried over an agreement on the bytes they speak about ---- *)
Lemma rbn_val_keep : forall (W : world SEGS) m1 m2 a n v,
  val_mem SEGS (mrestrict (w_H W) m1) a n v ->
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  val_mem SEGS (mrestrict (w_H W) m2) a n v.
Proof.
intros W m1 m2 a n v HV HA k Hk.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W) m1 m2 (a + Z.of_nat k) (HA (a + Z.of_nat k) ltac:(lia))).
exact (HV k Hk).
Qed.
Lemma rbn_garr_keep : forall (W : world SEGS) m1 m2 a l,
  garr8 SEGS (mrestrict (w_H W) m1) a l ->
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  garr8 SEGS (mrestrict (w_H W) m2) a l.
Proof.
intros W m1 m2 a l HG HA. apply (garr8_frame SEGS _ _ a l HG).
intros x Hx. exact (mbyte_of_aview SEGS (w_H W) (w_H W) m1 m2 x (HA x Hx)).
Qed.
Lemma rbn_rdword_keep : forall (W : world SEGS) m1 m2 a v,
  rdword (aview SEGS (w_H W) m1) a = Some v ->
  (forall x, a <= x < a + 8 -> aview SEGS (w_H W) m2 x = aview SEGS (w_H W) m1 x) ->
  rdword (aview SEGS (w_H W) m2) a = Some v.
Proof.
intros W m1 m2 a v HR HA. unfold rdword in *.
rewrite (HA a ltac:(lia)), (HA (a+1) ltac:(lia)), (HA (a+2) ltac:(lia)), (HA (a+3) ltac:(lia)),
  (HA (a+4) ltac:(lia)), (HA (a+5) ltac:(lia)), (HA (a+6) ltac:(lia)), (HA (a+7) ltac:(lia)).
exact HR.
Qed.
Lemma rbn_ra_keep : forall (W : world SEGS) m1 m2 q n,
  range_addressable (aview SEGS (w_H W) m1) SHADOW_OFF q n ->
  (forall x, q <= x < q + n -> aview SEGS (w_H W) m2 (shadow_addr x) = aview SEGS (w_H W) m1 (shadow_addr x)) ->
  range_addressable (aview SEGS (w_H W) m2) SHADOW_OFF q n.
Proof.
intros W m1 m2 q n HR HA x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
specialize (HA x Hx). unfold shadow_of_addr in *. unfold shadow_addr in HA. rewrite HA. exact Hs.
Qed.
Lemma rbn_sb_keep : forall c m1 m2 b q cap cs ov,
  rbn_sb c m1 b q cap cs ov ->
  (forall x, b <= x < b + 28 -> aview SEGS (w_H (x_W c)) m2 x = aview SEGS (w_H (x_W c)) m1 x) ->
  (forall x, q <= x < q + Z.of_nat (length cs) -> aview SEGS (w_H (x_W c)) m2 x = aview SEGS (w_H (x_W c)) m1 x) ->
  rbn_sb c m2 b q cap cs ov.
Proof.
intros c m1 m2 b q cap cs ov (V1 & V2 & V3 & V4 & Hov & Hlen & Hch & HG) HB HQ.
unfold rbn_sb, x_mem_at in *. cbn zeta in *.
split; [eapply rbn_val_keep; [exact V1 | intros x Hx; apply HB; cbn [Z.of_nat] in Hx; lia]|].
split; [eapply rbn_val_keep; [exact V2 | intros x Hx; apply HB; cbn [Z.of_nat] in Hx; lia]|].
split; [eapply rbn_val_keep; [exact V3 | intros x Hx; apply HB; cbn [Z.of_nat] in Hx; lia]|].
split; [eapply rbn_val_keep; [exact V4 | intros x Hx; apply HB; cbn [Z.of_nat] in Hx; lia]|].
split; [exact Hov|]. split; [exact Hlen|]. split; [exact Hch|].
eapply rbn_garr_keep; [exact HG | exact HQ].
Qed.
Lemma rbn_scope_keep : forall c m1 m2 w nm tk dp,
  rbn_scope c m1 w nm tk dp ->
  (forall x, x_FS c + 4 <= x < x_FS c + 30 -> aview SEGS (w_H (x_W c)) m2 x = aview SEGS (w_H (x_W c)) m1 x) ->
  rbn_scope c m2 w nm tk dp.
Proof.
intros c m1 m2 w nm tk dp (H4 & H8 & H16 & H24) HA. unfold rbn_scope in *. cbn zeta in *.
split; [rewrite (HA (x_FS c + 4) ltac:(lia)); exact H4|].
split; [intros j Hj; rewrite (HA (x_FS c + j) ltac:(lia)); exact (H8 j Hj)|].
split; [intros j Hj; rewrite (HA (x_FS c + j) ltac:(lia)); exact (H16 j Hj)|].
intros j Hj. rewrite (HA (x_FS c + j) ltac:(lia)). exact (H24 j Hj).
Qed.
Lemma rbn_slots_keep : forall c m1 m2,
  rbn_slots c m1 ->
  (forall x, x_s1 c <= x < x_s1 c + 88 -> aview SEGS (w_H (x_W c)) m2 x = aview SEGS (w_H (x_W c)) m1 x) ->
  rbn_slots c m2.
Proof.
intros c m1 m2 HS HA. unfold rbn_slots, x_mem_at in *. cbn zeta in *.
destruct HS as (A0 & A8 & A16 & A24 & A32 & A40 & A48 & A56 & A80).
assert (K : forall o v, 0 <= o -> o + 8 <= 88 -> val_mem SEGS (mrestrict (w_H (x_W c)) m1) (x_s1 c + o) 8 v ->
  val_mem SEGS (mrestrict (w_H (x_W c)) m2) (x_s1 c + o) 8 v).
{ intros o v Ho1 Ho2 HV. eapply rbn_val_keep; [exact HV | intros x Hx; apply HA; cbn [Z.of_nat] in Hx; lia]. }
split; [eapply rbn_val_keep; [exact A0 | intros x Hx; apply HA; cbn [Z.of_nat] in Hx; lia]|].
split; [exact (K 8 _ ltac:(lia) ltac:(lia) A8)|].
split; [exact (K 16 _ ltac:(lia) ltac:(lia) A16)|].
split; [exact (K 24 _ ltac:(lia) ltac:(lia) A24)|].
split; [exact (K 32 _ ltac:(lia) ltac:(lia) A32)|].
split; [exact (K 40 _ ltac:(lia) ltac:(lia) A40)|].
split; [exact (K 48 _ ltac:(lia) ltac:(lia) A48)|].
split; [exact (K 56 _ ltac:(lia) ltac:(lia) A56)|].
exact (K 80 _ ltac:(lia) ltac:(lia) A80).
Qed.
Lemma rbn_saved_keep : forall c m1 m2,
  rbn_saved c m1 ->
  (forall x, x_sp0 c - 104 <= x < x_sp0 c -> aview SEGS (w_H (x_W c)) m2 x = aview SEGS (w_H (x_W c)) m1 x) ->
  rbn_saved c m2.
Proof.
intros c m1 m2 HS HA. unfold rbn_saved, x_mem_at in *.
apply Forall_forall. intros p Hp.
pose proof (proj1 (Forall_forall _ _) HS p Hp) as HV.
assert (Hoff : 8 <= fst p <= 104)
  by (clear - Hp; unfold rbn_saved_regs in Hp;
      repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia |]); destruct Hp).
eapply rbn_val_keep; [exact HV | intros x Hx; apply HA; cbn [Z.of_nat] in Hx; lia].
Qed.
Lemma rbn_bufkept_keep : forall c lyc Sc m1 m2 E,
  rbn_bufkept B c m1 -> rbn_k c lyc Sc m1 m2 E ->
  Permutation (ablocks B lyc Sc) (ablocks B (x_ly c) (x_S c)) ->
  (forall a, E a -> forall q N, In (q, N) (ablocks B (x_ly c) (x_S c)) -> ~ (q <= a < q + N)) ->
  rbn_bufkept B c m2.
Proof.
intros c lyc Sc m1 m2 E HB (_ & A2 & _ & _) Hperm HE a Hfp (q & N & Hin & Hq).
rewrite <- (HB a Hfp (ex_intro _ q (ex_intro _ N (conj Hin Hq)))).
pose proof (Permutation_in _ (Permutation_sym Hperm) Hin) as Hin2.
pose proof (req_size_pos N) as Hrq.
replace a with (q + (a - q)) by lia.
apply (A2 q N (a - q) Hin2); [|replace (q + (a - q)) with a by lia; intros X; exact (HE a X q N Hin Hq)].
destruct (Z.le_gt_cases 0 N) as [HN|HN]; [lia|].
exfalso. unfold req_size in *. destruct (N =? 0) eqn:EN; [apply Z.eqb_eq in EN|apply Z.eqb_neq in EN]; lia.
Qed.

(* the pieces of the contract's pre-condition this file uses (rbn_pre is a long conjunction) *)
Lemma rbn_pre_parts : forall c, rbn_pre B G c ->
  afn_pre SEGS B RBN_STK (x_ly c) (x_S c) (x_W c) (x_regs c) (x_mem c) (x_md c) (x_ch c) /\
  arodata_okP SEGS (@pa_relro_lo _ identb_listing PI) (@pa_relro_hi _ identb_listing PI) B
    (aview SEGS (w_H (x_W c)) (x_mem c)) /\
  Z.of_nat (length (frames (x_S c))) <= 7 /\
  st_nev (x_S c) <= EV_MAX /\ blocks_bytes (x_S c) <= LIVE_MAX /\
  rbn_img B G (x_W c) (x_mem c).
Proof.
intros c H. unfold rbn_pre in H. decompose [and] H.
split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; assumption.
Qed.

(* ---- A3. the geometry of a cut point ---- *)
(* The bytes the two segments write: the deepest callee window below s1, the four structs of the window
   (db s1+88, tb s1+120, nb s1+152, wb s1+184, 28 bytes each), the frame arrays w4 (F+32) and nm (F+64),
   and nm's three scope shadow bytes (FS+8 .. FS+11). Everything a cut point speaks about is outside it,
   but for nm's scope bytes and the two structs, which the segments rebuild from the step they took. *)
Definition rbn_zone (c : rbx) (a : Z) : Prop :=
  (x_s1 c - 2 * ESTACK <= a < x_s1 c) \/ (x_s1 c + 88 <= a < x_s1 c + 212) \/
  (x_F c + 32 <= a < x_F c + 88) \/ (x_FS c + 8 <= a < x_FS c + 11).
Lemma rbn_geom : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  AR SEGS B lyc Sc (x_W c) memc mdc /\
  x_sp0 c mod 16 = 0 /\ alloc_ceiling + RBN_STK <= x_sp0 c /\ x_sp0 c <= 2 ^ 47 /\
  alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + RBN_STK <= x_sp0 c /\
  x_sp0 c <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\
  x_sp0 c - 336 <= x_s1 c <= x_sp0 c - 320 /\ x_s1 c mod 32 = 0 /\
  In (3, x_fpos c) (frames Sc) /\ frames Sc = (3, x_fpos c) :: frames (x_S c) /\
  4096 <= x_F c /\ x_F c + 512 <= alloc_ceiling /\ x_F c mod 64 = 0 /\ in_app (x_F c) 512 /\
  (forall a, x_F c <= a < x_F c + 512 -> apresent (w_H (x_W c)) memc a /\ ~ aowned B lyc Sc a) /\
  (forall a, x_sp0 c - RBN_STK <= a < x_sp0 c -> apresent (w_H (x_W c)) memc a) /\
  Z.of_nat (length (frames Sc)) <= 8 /\ st_nev Sc <= EV_MAX /\ blocks_bytes Sc <= LIVE_MAX /\
  (forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos).
Proof.
intros c lyc Sc memc mdc regs (HPRE & HJ & Hperm & _).
destruct (rbn_pre_parts c HPRE) as (HFN & _ & Hnf & Hnev & Hlive & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev2 & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : RBN_STK = 8528) by reflexivity.
assert (F3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof Hly as (_ & _ & _ & _ & _ & EFA & _ & _ & _ & Eslo & Eshi & _).
assert (Efa : forall cid pos, frame_addr lyc cid pos = frame_addr (x_ly c) cid pos)
  by (intros cid pos; unfold frame_addr; rewrite EFA; reflexivity).
assert (HinF : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (Hf0 & Hfc & Hfapp).
destruct (frame_al64 SEGS B lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (Hal64 & _ & _).
destruct (al_frames _ _ LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (_ & _ & Hby & _).
rewrite HF in Hf0, Hfc, Hfapp, Hal64, Hby. rewrite F3 in Hfc, Hfapp, Hby.
assert (Hs1 : x_sp0 c - 336 <= x_s1 c <= x_sp0 c - 320 /\ x_s1 c mod 32 = 0).
{ unfold x_s1. pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as Dr.
  pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as D16.
  rewrite Hsp0al, Z.add_0_r in D16.
  assert (Ht : exists t, (x_sp0 c - 320) mod 32 = 16 * t)
    by (exists (x_sp0 c / 16 - 20 - 2 * ((x_sp0 c - 320) / 32)); lia).
  destruct Ht as (t & Ht).
  split; [lia | rewrite Z.mul_comm; apply Z.mod_mul; lia]. }
split; [exact HAR|]. split; [exact Hsp0al|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [rewrite Eslo; lia|]. split; [rewrite Eshi; lia|]. split; [rewrite Eshi; lia|].
split; [lia|]. split; [lia|].
split; [exact HinF|]. split; [exact Hfrs|].
split; [lia|]. split; [lia|]. split; [exact Hal64|]. split; [exact Hfapp|].
split; [exact Hby|].
split; [intros a Ha; apply Hpres; lia|].
assert (Hlen : (length (frames Sc) = S (length (frames (x_S c))))%nat) by (rewrite Hfrs; reflexivity).
split; [rewrite Hlen, Nat2Z.inj_succ; lia|].
split; [lia|].
split; [rewrite (rbn_live_bytes lyc Sc (x_ly c) (x_S c) Hperm); exact Hlive | exact Efa].
Qed.
(* The stack and the frame of the call lie where the zone says, and the zone misses the window slots,
   the saved registers, the frame's flag word and the three other scopes. *)
Lemma rbn_zone_out : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  (forall a, x_s1 c <= a < x_s1 c + 88 -> ~ rbn_zone c a) /\
  (forall a, x_sp0 c - 104 <= a < x_sp0 c -> ~ rbn_zone c a) /\
  (forall a, x_F c + 504 <= a < x_F c + 512 -> ~ rbn_zone c a) /\
  (forall a, x_FS c + 4 <= a < x_FS c + 8 -> ~ rbn_zone c a) /\
  (forall a, x_FS c + 11 <= a < x_FS c + 30 -> ~ rbn_zone c a).
Proof.
intros c lyc Sc memc mdc regs HC.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & Hby & Hpres & Hnf & Hnev & Hlive & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8.
assert (HF8 : x_F c mod 8 = 0).
{ pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64.
  pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
  rewrite Hal64, Z.add_0_r in D64. lia. }
assert (HFSb : SHADOW_OFF <= x_FS c /\ x_FS c + 64 < alloc_ceiling)
  by (unfold SHADOW_OFF in *; split; [lia|];
      assert (x_F c / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia); unfold SHADOW_OFF; lia).
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
pose proof (YCbq.shadow_addr_bounds (x_F c) ltac:(unfold kHighMemEnd in *; lia)) as HSBd.
rewrite <- HFSa in HSBd.
destruct Hfapp as (_ & [Hlow | (Hhi1 & Hhi2)]);
  unfold rbn_zone; unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, ASAN_CEIL in *.
all: split; [intros a Ha [X|[X|[X|X]]]; lia|].
all: split; [intros a Ha [X|[X|[X|X]]]; lia|].
all: split; [intros a Ha [X|[X|[X|X]]]; lia|].
all: split; [intros a Ha [X|[X|[X|X]]]; lia|].
all: intros a Ha [X|[X|[X|X]]]; lia.
Qed.
(* where the frame's shadow lies: in the shadow band, below the allocation ceiling, off the frame *)
Lemma rbn_fs_apart : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  SHADOW_OFF <= x_FS c /\ x_FS c + 64 < alloc_ceiling /\
  (x_FS c + 64 <= x_F c \/ x_F c + 512 <= x_FS c).
Proof.
intros c lyc Sc memc mdc regs HC.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  _ & _ & Hf0 & Hfc & Hal64 & Hfapp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
assert (HFS64 : x_FS c + 64 = shadow_addr (x_F c + 512)).
{ unfold shadow_addr, x_FS. replace (x_F c + 512) with (x_F c + 64 * 8) by lia.
  rewrite (Z.div_add (x_F c) 64 8 ltac:(lia)). lia. }
pose proof (YCbq.shadow_addr_bounds (x_F c) ltac:(unfold kHighMemEnd in *; lia)) as HSBd.
pose proof (YCbq.shadow_addr_bounds (x_F c + 512) ltac:(unfold kHighMemEnd in *; lia)) as HSBe.
rewrite <- HFSa in HSBd. rewrite <- HFS64 in HSBe.
destruct Hfapp as (_ & [Hlow | (Hhi1 & Hhi2)]);
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, ASAN_CEIL in *;
  (split; [lia|]); (split; [lia|]); lia.
Qed.

(* ---- A4. the agreements a step gives, and the cut-point facts they carry ---- *)
Lemma rbn_ag_stack : forall c lyc Sc memc mdc regs memc' E,
  rbn_core B G c lyc Sc memc mdc regs -> rbn_k c lyc Sc memc memc' E ->
  forall a, x_s1 c - 2 * ESTACK <= a < x_sp0 c -> ~ E a ->
    aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a.
Proof.
intros c lyc Sc memc mdc regs memc' E HC (A1 & _ & _ & _) a Ha He.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hs1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
apply A1; [lia | exact He].
Qed.
Lemma rbn_ag_frame : forall c lyc Sc memc mdc regs memc' E,
  rbn_core B G c lyc Sc memc mdc regs -> rbn_k c lyc Sc memc memc' E ->
  forall a, (x_F c <= a < x_F c + 512 \/ x_FS c <= a < x_FS c + 64) -> ~ E a ->
    aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a.
Proof.
intros c lyc Sc memc mdc regs memc' E HC (_ & _ & _ & A4) a Ha He.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HinF & _ & _ & _ & _ & _ &
  _ & _ & _ & _ & _ & Efa).
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
assert (F3 : fs_frame_bytes 3 = 512) by reflexivity.
apply (A4 3 (x_fpos c) a HinF); [|exact He].
unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF, F3.
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
rewrite <- HFSa. change (512 / 8) with 64. lia.
Qed.
Lemma rbn_ag_img : forall c lyc Sc memc memc' E,
  rbn_k c lyc Sc memc memc' E ->
  forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a.
Proof. intros c lyc Sc memc memc' E (_ & _ & A3 & _) a H1 H2 H3. exact (A3 a H1 H2 H3). Qed.
(* a heap block of the entry state is outside the zone the segments write *)
Lemma rbn_zone_block : forall c lyc Sc memc mdc regs q N a,
  rbn_core B G c lyc Sc memc mdc regs -> In (q, N) (ablocks B (x_ly c) (x_S c)) -> q <= a < q + N ->
  ~ rbn_zone c a.
Proof.
intros c lyc Sc memc mdc regs q N a HC Hin Ha.
pose proof HC as (_ & _ & Hperm & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hs1 & _ &
  HinF & _ & Hf0 & Hfc & _ & Hfapp & _ & _ & _ & _ & _ & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (F3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
pose proof (Permutation_in _ (Permutation_sym Hperm) Hin) as Hin2.
destruct (al_blocks _ _ LAWS lyc Sc (x_W c) memc mdc q N HAR Hin2) as (_ & Hq4096 & Hqc & Hqapp & _).
destruct (Z.le_gt_cases 0 N) as [HN|HN]; [|exfalso; lia].
pose proof (req_size_pos N HN) as (Hrq1 & Hrq2).
pose proof (sep_block_frame SEGS B LAWS lyc Sc (x_W c) memc mdc q N 3 (x_fpos c) HAR Hin2 HinF) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite HF, F3 in Hd.
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
assert (HFS64 : x_FS c + 64 = shadow_addr (x_F c + 512)).
{ unfold shadow_addr, x_FS. replace (x_F c + 512) with (x_F c + 64 * 8) by lia.
  rewrite (Z.div_add (x_F c) 64 8 ltac:(lia)). lia. }
pose proof (YCbq.shadow_addr_bounds (x_F c) ltac:(unfold kHighMemEnd in *; lia)) as HSBd.
pose proof (YCbq.shadow_addr_bounds (x_F c + 512) ltac:(unfold kHighMemEnd in *; lia)) as HSBe.
rewrite <- HFSa in HSBd. rewrite <- HFS64 in HSBe.
destruct Hqapp as (_ & [Hlow | (Hhi1 & Hhi2)]); unfold rbn_zone;
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, ASAN_CEIL in *;
  intros [X|[X|[X|X]]]; lia.
Qed.
(* everything rbn_live says is outside the zone, so it crosses any step that writes inside it *)
Lemma rbn_live_keep9 : forall c lyc Sc memc mdc regs lyc' Sc' memc' mdc' regs' E,
  rbn_live B G c lyc Sc memc mdc regs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc' Sc' (x_W c) memc' mdc' 0 ->
  Permutation (ablocks B lyc' Sc') (ablocks B (x_ly c) (x_S c)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  rbn_k c lyc Sc memc memc' E -> (forall a, E a -> rbn_zone c a) ->
  rbn_live B G c lyc' Sc' memc' mdc' regs'.
Proof.
intros c lyc Sc memc mdc regs lyc' Sc' memc' mdc' regs' E HL HJ2 Hperm2 Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 HK HE.
pose proof HL as ((HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag) & Hargs & Hbuf & Hslots & R22).
pose proof HL as (HC & _).
destruct (rbn_zone_out c lyc Sc memc mdc regs HC) as (Zslots & Zsaved & Zflag & _ & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hs1 & _ &
  HinF & _ & Hf0 & Hfc & _ & _ & _ & _ & _ & _ & _ & Efa).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (AGs : forall a, x_s1 c - 2 * ESTACK <= a < x_sp0 c -> ~ rbn_zone c a ->
  aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a)
  by (intros a Ha Hz; exact (rbn_ag_stack c lyc Sc memc mdc regs memc' E HC HK a Ha ltac:(intros X; exact (Hz (HE a X))))).
assert (AGf : forall a, (x_F c <= a < x_F c + 512 \/ x_FS c <= a < x_FS c + 64) -> ~ rbn_zone c a ->
  aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a)
  by (intros a Ha Hz; exact (rbn_ag_frame c lyc Sc memc mdc regs memc' E HC HK a Ha ltac:(intros X; exact (Hz (HE a X))))).

split; [|split; [exact Hargs|]].
- split; [exact HPRE|]. split; [exact HJ2|]. split; [exact Hperm2|].
  split; [rewrite Q2; exact R2|].
  split; [rewrite Q3; exact R3|].
  split; [rewrite Q4; exact R4|].
  split; [rewrite Q8; exact R8|].
  split; [rewrite Q9; exact R9|].
  split; [rewrite Q18; exact R18|].
  split; [rewrite Q19; exact R19|].
  split; [rewrite Q23; exact R23|].
  split.
  + apply (rbn_saved_keep c memc memc' Hsav).
    intros x Hx. apply AGs; [lia | exact (Zsaved x Hx)].
  + apply (rbn_rdword_keep (x_W c) memc memc' _ _ Hflag).
    intros x Hx. apply AGf; [lia | apply Zflag; lia].
- split.
  + apply (rbn_bufkept_keep c lyc Sc memc memc' E Hbuf HK Hperm).
    intros a Ha q N Hin Hq. exact (rbn_zone_block c lyc Sc memc mdc regs q N a HC Hin Hq (HE a Ha)).
  + split; [|rewrite Q22; exact R22].
    apply (rbn_slots_keep c memc memc' Hslots).
    intros x Hx. apply AGs; [lia | exact (Zslots x Hx)].
Qed.
Lemma rbn_live_keep : forall c lyc Sc memc mdc regs lyc' Sc' memc' mdc' regs' E,
  rbn_live B G c lyc Sc memc mdc regs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc' Sc' (x_W c) memc' mdc' 0 ->
  Permutation (ablocks B lyc' Sc') (ablocks B (x_ly c) (x_S c)) ->
  aregs_preserved regs regs' ->
  rbn_k c lyc Sc memc memc' E -> (forall a, E a -> rbn_zone c a) ->
  rbn_live B G c lyc' Sc' memc' mdc' regs'.
Proof.
intros c lyc Sc memc mdc regs lyc' Sc' memc' mdc' regs' E HL HJ2 Hperm2 HP HK HE.
assert (RR : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regs' r = getr regs r).
{ intros r z Hz Hr. pose proof (HP z Hr) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X. exact X. }
eapply (rbn_live_keep9 c lyc Sc memc mdc regs lyc' Sc' memc' mdc' regs' E HL HJ2 Hperm2);
  [ exact (RR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia))
  | exact (RR 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia))
  | exact HK | exact HE ].
Qed.

(* ---- A5. the stem crosses a step: its bytes and its shadow are in the image or in a frame of the
   caller, both outside the zone; its shadow hull is re-derived at the later state ---- *)
Lemma rbn_caller_frame_out : forall c lyc Sc memc mdc regs cid pos a,
  rbn_core B G c lyc Sc memc mdc regs -> In (cid, pos) (frames (x_S c)) ->
  (in_zr a (frame_rng lyc (cid, pos)) \/
   in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
  ~ rbn_zone c a.
Proof.
intros c lyc Sc memc mdc regs cid pos a HC Hin Hr.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hs1 & _ &
  HinF & Hfrs & Hf0 & Hfc & _ & _ & _ & _ & _ & _ & _ & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (F3 : fs_frame_bytes 3 = 512) by reflexivity.
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
destruct (frame_zone SEGS B LAWS lyc Sc (x_W c) memc mdc cid pos a HAR HinC Hr) as (Hza & _).
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
destruct (in_split _ _ Hin) as (l1 & l2 & El).
assert (ES : frames Sc = [] ++ (3, x_fpos c) :: l1 ++ (cid, pos) :: l2) by (rewrite Hfrs, El; reflexivity).
(* a lies below the allocation ceiling, so it is in neither stack part of the zone *)
intros [X|[X|[X|X]]]; [lia | lia | | ].
- apply (frames_zone_disj SEGS B LAWS lyc Sc (x_W c) memc mdc (3, x_fpos c) (cid, pos) [] l1 l2 a HAR ES).
  + left. unfold frame_rng, in_zr. cbn [fst snd]. rewrite HF, F3. lia.
  + exact Hr.
- apply (frames_zone_disj SEGS B LAWS lyc Sc (x_W c) memc mdc (3, x_fpos c) (cid, pos) [] l1 l2 a HAR ES).
  + right. unfold in_zr. cbn [fst snd]. rewrite HF, F3, <- HFSa. change (512 / 8) with 64. lia.
  + exact Hr.
Qed.
Lemma rbn_stem_keep : forall c lyc' Sc' memc' mdc' memc st,
  rbn_stem B G c memc st ->
  AR SEGS B lyc' Sc' (x_W c) memc' mdc' ->
  (forall cid pos, In (cid, pos) (frames (x_S c)) ->
     In (cid, pos) (frames Sc') /\ frame_addr lyc' cid pos = frame_addr (x_ly c) cid pos) ->
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a) ->
  (forall cid pos a, In (cid, pos) (frames (x_S c)) ->
     (in_zr a (frame_rng (x_ly c) (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr (x_ly c) cid pos), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H (x_W c)) memc' a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_stem B G c memc' st.
Proof.
intros c lyc' Sc' memc' mdc' memc st HST HAR' Hfr AGi AGf.
destruct HST as [(Hsd & Hst & HC & (cid & pos & Hin & Hfa1 & Hfa2)) | (Hsd & HI)].
- left. split; [exact Hsd|]. split; [exact Hst|]. split; [|exists cid, pos; auto].
  destruct (Hfr cid pos Hin) as (Hin' & Hfa').
  destruct HC as (Hch & Hlen & Hpos & Hamr & HG & HRA & HHV & HTail).
  set (fa := frame_addr (x_ly c) cid pos) in *.
  destruct (frame_al64 SEGS B lyc' Sc' (x_W c) memc' mdc' cid pos HAR' Hin') as (Hal & Hbal & Hb64).
  rewrite Hfa' in Hal.
  assert (Hfa8 : fa mod 8 = 0).
  { pose proof (Z.div_mod fa 64 ltac:(lia)) as D64. pose proof (Z.mod_pos_bound fa 8 ltac:(lia)) as R8.
    pose proof (Z.div_mod fa 8 ltac:(lia)) as D8. rewrite Hal, Z.add_0_r in D64. lia. }
  assert (Hb8 : fs_frame_bytes cid mod 8 = 0).
  { pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D64.
    pose proof (Z.mod_pos_bound (fs_frame_bytes cid) 8 ltac:(lia)) as R8.
    pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as D8. rewrite Hbal, Z.add_0_r in D64. lia. }
  (* the string's bytes and the word tail are bytes of that frame *)
  assert (AGd : forall x, fa <= x < fa + fs_frame_bytes cid ->
    aview SEGS (w_H (x_W c)) memc' x = aview SEGS (w_H (x_W c)) memc x).
  { intros x Hx. apply (AGf cid pos x Hin). left. unfold frame_rng, in_zr. cbn [fst snd].
    change (frame_addr (x_ly c) cid pos) with fa. exact Hx. }
  (* its shadow bytes are shadow bytes of that frame *)
  assert (AGs : forall x, fa <= x < fa + fs_frame_bytes cid ->
    aview SEGS (w_H (x_W c)) memc' (shadow_addr x) = aview SEGS (w_H (x_W c)) memc (shadow_addr x)).
  { intros x Hx. apply (AGf cid pos (shadow_addr x) Hin). right. unfold in_zr. cbn [fst snd].
    change (frame_addr (x_ly c) cid pos) with fa. unfold shadow_addr. split.
    - apply Z.add_le_mono_l. apply Z.div_le_mono; lia.
    - assert (Hk : fa + fs_frame_bytes cid = 8 * (fa / 8 + fs_frame_bytes cid / 8)).
      { pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod (fs_frame_bytes cid) 8 ltac:(lia)) as Db.
        rewrite Hfa8, Z.add_0_r in Da. rewrite Hb8, Z.add_0_r in Db. lia. }
      assert (Hd : x / 8 < fa / 8 + fs_frame_bytes cid / 8)
        by (apply Z.div_lt_upper_bound; lia).
      lia. }
  split; [exact Hch|]. split; [exact Hlen|]. split; [exact Hpos|]. split; [exact Hamr|].
  split; [eapply rbn_garr_keep; [exact HG|]; intros x Hx; apply AGd; rewrite length_app in Hx; cbn [length] in Hx; lia|].
  split; [eapply rbn_ra_keep; [exact HRA|]; intros x Hx; apply AGs; lia|].
  split.
  + eapply (shadow_hull_vis_of_frame SEGS B LAWS lyc' Sc' (x_W c) memc' mdc' cid pos st
      (Z.of_nat (length (x_sd c)) + 1) HAR' Hin');
    rewrite ?Hfa'; change (frame_addr (x_ly c) cid pos) with fa; lia.
  + intros x Hx. rewrite (AGd x ltac:(lia)). exact (HTail x Hx).
- right. split; [exact Hsd|].
  destruct HI as (Hlo & Hhi & Hch & HG & Hglob & Hfix & HTail).
  split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hch|].
  split; [|split; [exact Hglob | split; [exact Hfix | exact HTail]]].
  eapply rbn_garr_keep; [exact HG|]. intros x Hx. rewrite length_app in Hx. cbn [length] in Hx.
  destruct (Hfix x ltac:(lia)) as (Hi & Ho & He). exact (AGi x Hi Ho He).
Qed.

(* ============================================================================================
   Part B: C1 0x83000 (+0x28c) -> C2 0x83088 (+0x314), i = 0.
   0x83000 .. 0x8301c  the two sb_dec calls that fill wb with w4;
   0x83020 .. 0x83060  w4's NUL, nm's scope bytes, nm's struct, the memset of nb.n / nb.over;
   0x83064 .. 0x83084  the stem's first byte (shadow-checked) and the loop's registers.
   ============================================================================================ *)
(* The state between the two sb_dec calls: wb holds cs, everything else is C1's. *)
Definition rbn_m1 (c : rbx) (st : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) (cs : list Z) : Prop :=
  rbn_live B G c lyc Sc memc mdc regs /\ rbn_stem B G c memc st /\
  getr regs 20 = w64 (x_W4 c) /\ getr regs 21 = w64 5 /\ getr regs 24 = w64 (x_name c) /\
  getr regs 25 = w64 st /\ getr regs 26 = w64 (x_token_len c) /\
  rbn_scope c memc 5 0xf8 0xf8 0xf8 /\
  rbn_sb c memc (x_wb c) (x_W4 c) 5 cs 0 /\
  garr8 SEGS (x_mem_at c memc) (x_W4 c) cs /\ Z.of_nat (length cs) <= 4.
Lemma rbn_garr_app : forall m a l1 l2,
  garr8 SEGS m a l1 -> garr8 SEGS m (a + Z.of_nat (length l1)) l2 -> garr8 SEGS m a (l1 ++ l2).
Proof.
intros m a l1 l2 H1 H2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (H1 j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (H2 (j - length l1)%nat ltac:(lia)) as (Hv & Hr).
  split; [|exact Hr].
  replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia.
  exact Hv.
Qed.
(* the pieces of the argument check the segments use *)
Lemma rbn_args_parts : forall c,
  reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c) (x_display c)
    (x_display_len c) (x_i c) (x_o c) = true ->
  x_name c <> 0 /\ x_token c <> 0 /\ x_display c <> 0 /\ bn_ok (x_i c) = true /\ bn_ok (x_o c) = true.
Proof.
intros c H. unfold reac_box_name_c.bn_args_ok in H. rewrite !andb_true_iff in H.
destruct H as ((((((((H1 & H2) & H3) & _) & _) & _) & H7) & H8) & _).
apply negb_true_iff, Z.eqb_neq in H1. apply negb_true_iff, Z.eqb_neq in H2.
apply negb_true_iff, Z.eqb_neq in H3.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H7 | exact H8].
Qed.
(* one sb_dec call of the pair: wb gains the two digits of v *)
Lemma rbn_dec_call : forall c st lyc Sc memc mdc regs cs v (regsT : bvmap 5 word) (mdT : Model) retk,
  rbn_m1 c st lyc Sc memc mdc regs cs -> mdT = mdc ->
  bn_ok v = true -> Z.of_nat (length cs) + 2 <= 4 ->
  (forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regsT r = getr regs r) ->
  getr regsT 1 = Z_to_bv 64 (BASE + retk) -> 0 <= retk < 2 ^ 40 -> retk mod 2 = 0 ->
  getr regsT 10 = w64 (x_wb c) -> getr regsT 11 = w64 v -> getr regsT 12 = w64 2 ->
  SRr SEGS (x_W c) (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_sb_dec)) memc (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = x_W c /\ exists lyc' Sc' regs' mem' md',
       c2 = mkCfg (mkst regs' (Z_to_bv 64 (BASE + retk)) mem' (seg_rom SEGS)) md' /\
       rbn_m1 c st lyc' Sc' mem' md' regs' (cs ++ bn_dec v 2) /\
       aregs_preserved regsT regs').
Proof.
intros c st lyc Sc memc mdc regs cs v regsT mdT retk HM -> Hv Hcs HR Rra Hrk Hrk2 Ra0 Ra1 Ra2.
pose proof HM as (HL & HST & R20 & R21 & R24 & R25 & R26 & HSCO & HSBO & HG0 & Hlen0).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & Hby & Hpres & Hnf & Hnev & Hlive & Efa).
destruct (rbn_zone_out c lyc Sc memc mdc regs HC) as (Zslots & Zsaved & Zflag & Zsc4 & Zsc16).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HSD : SB_DEC_STK = 4256) by reflexivity.
pose proof HSBO as (V0 & V8 & V16 & V24 & _ & Hcap & Hch & _).
destruct (reac_box_name.bn_ok_dec v Hv) as (Hv40 & Hlv & _ & HDv & _ & Hdig & _).
assert (HRz : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regsT r = getr regs r)
  by (intros r z Hz Hr; rewrite <- Hz in Hr; exact (HR r Hr)).
assert (Hsp : spZ regsT = x_s1 c)
  by (unfold spZ; rewrite (HRz 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia)), R2;
      apply unsigned_lit_small; lia).
(* the digits fit: room is 4 - n and the two digits need 2 *)
assert (Hacc : sb_dec_c.sb_dec_acc v 2 5 (Z.of_nat (length cs)) = 2).
{ unfold sb_dec_c.sb_dec_acc, sb_dec_c.sb_dec_room. rewrite HDv.
  replace (Z.of_nat (length cs) + 1 <=? 5) with true by (symmetry; apply Z.leb_le; lia).
  rewrite Hlv. lia. }
assert (Hroom : sb_dec_c.sb_dec_room 5 (Z.of_nat (length cs)) = 4 - Z.of_nat (length cs)).
{ unfold sb_dec_c.sb_dec_room.
  replace (Z.of_nat (length cs) + 1 <=? 5) with true by (symmetry; apply Z.leb_le; lia). lia. }
assert (Hovf : (sb_dec_c.sb_dec_room 5 (Z.of_nat (length cs)) <?
                Z.of_nat (length (sb_dec_c.sb_dec_D v 2))) = false)
  by (rewrite Hroom, HDv, Hlv; apply Z.ltb_ge; lia).
(* the frame bytes w4[n ..] the call writes *)
assert (HW4 : x_W4 c = x_F c + 32) by reflexivity.
assert (Hdst : tdst_ok B lyc Sc (x_W4 c + Z.of_nat (length cs)) 2).
{ intros a Ha. right. exists 3, (x_fpos c). split; [exact HinF|].
  unfold frame_rng, in_zr. cbn [fst snd].
  assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
  assert (F3 : fs_frame_bytes 3 = 512) by reflexivity. rewrite HF, F3. lia. }
assert (HRA4 : range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF (x_W4 c) 5).
{ pose proof HSCO as (Hs4 & _). apply (range_addressable_partial _ _ _ 5);
  [ unfold shadow_of_addr, x_FS in *; rewrite HW4;
    replace (x_F c + 32) with (x_F c + 4 * 8) by lia;
    rewrite (Z.div_add (x_F c) 4 8 ltac:(lia)); replace (SHADOW_OFF + (x_F c / 8 + 4)) with (x_FS c + 4) by (unfold x_FS; lia);
    exact Hs4
  | rewrite HW4; pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64;
    pose proof (Z.mod_pos_bound (x_F c + 32) 8 ltac:(lia));
    pose proof (Z.div_mod (x_F c + 32) 8 ltac:(lia)); rewrite Hal64, Z.add_0_r in D64; lia
  | lia ]. }
(* every byte of the struct and of the digits is one the caller may let the call write *)
assert (HWok : twr_ok B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) lyc Sc [(3, x_fpos c)] (x_W c) memc
  (spZ regsT) (x_wb c + 16) 12).
{ intros a Ha. unfold x_wb in Ha.
  assert (Hw : awr_byte RBN_STK (x_sp0 c) (x_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B lyc Sc) lyc
    [(3, x_fpos c)] a) by (left; lia).
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (Hp & Ho).
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho | rewrite Hsp; lia]. }
assert (HWbuf : twr_ok B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) lyc Sc [(3, x_fpos c)] (x_W c) memc
  (spZ regsT) (x_W4 c + Z.of_nat (length cs)) 2).
{ intros a Ha.
  assert (Hw : awr_byte RBN_STK (x_sp0 c) (x_FP c) (ablocks B (x_ly c) (x_S c)) (ablocks B lyc Sc) lyc
    [(3, x_fpos c)] a).
  { right. right. right. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd].
    assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
    assert (F3 : fs_frame_bytes 3 = 512) by reflexivity. rewrite HF, F3. lia. }
  destruct (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) as (Hp & Ho).
  split; [exact Hw|]. split; [exact Hp|]. split; [exact Ho | rewrite Hsp; lia]. }
eapply SRr_mono.
{ eapply (HSB RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) memc mdc 0 regsT (x_wb c) v 2 (x_W4 c) 5 (Z.of_nat (length cs)) 0 HJ).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | exact Hrk2].
  - unfold raZ. rewrite Rra, unsigned_lit_small by (pose proof pa_B_ok; lia). pose proof pa_base_lo. lia.
  - rewrite (HRz 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia)). exact R3.
  - rewrite (HRz 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia)). exact R4.
  - rewrite Hsp. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1m, Z.add_0_r in D.
    replace (x_s1 c) with (2 * (x_s1 c / 32) * 16) by lia. apply Z_mod_mult.
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - right; reflexivity.
  - unfold x_wb. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1m, Z.add_0_r in D.
    replace (x_s1 c + 184) with ((x_s1 c / 32 * 4 + 23) * 8) by lia. apply Z_mod_mult.
  - unfold x_wb. lia.
  - unfold x_wb. lia.
  - left. rewrite Hsp. unfold x_wb. lia.
  - unfold tsb_dec_rec_at, x_wb. split; lia.
  - exact V0.
  - exact V8.
  - exact V16.
  - exact V24.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - exact HWok.
  - intros Hr0. rewrite Hroom in Hr0.
    split; [lia|]. split; [lia|]. split; [rewrite Hacc; exact Hdst|].
    split; [rewrite Hacc; eapply range_addressable_sub; [exact HRA4 | lia | lia]|].
    split; [rewrite Hacc; exact HWbuf|].
    split; [unfold x_wb; rewrite Hacc; lia | rewrite Hacc, Hsp; unfold x_wb; lia].
  - exact Hnf.
  - unfold EV_SB_DEC. lia.
  - unfold LIVE_SB_DEC. lia. }
cbv beta. intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hfrs2 & Hperm2 & Htcj2 &
  Vp2 & Vcap2 & Vn2 & Vov2 & HGd).
rewrite Hacc in Vn2, HGd, Htcj2. rewrite Hovf in Vov2.
replace (0 + EV_SB_DEC) with 0 in HJ2 by reflexivity.
pose proof HJ2 as (HAR2 & Hly2 & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & EFA2 & _).
assert (Efa2 : forall cid pos, frame_addr ly2 cid pos = frame_addr (x_ly c) cid pos)
  by (intros cid pos; unfold frame_addr; rewrite EFA2; reflexivity).
pose proof (Permutation_trans Hperm2 Hperm) as Hperm3.
(* what the call wrote *)
pose proof (rbn_k_of_tcj c SB_DEC_STK lyc Sc memc mem2 (spZ regsT)
  (tsb_dec_wr (x_wb c) (x_W4 c) (Z.of_nat (length cs)) 2) Htcj2) as HK.
set (EE := fun a => (spZ regsT - SB_DEC_STK <= a < spZ regsT) \/
                    tsb_dec_wr (x_wb c) (x_W4 c) (Z.of_nat (length cs)) 2 a) in HK.
assert (HEz : forall a, EE a -> rbn_zone c a).
{ subst EE. unfold tsb_dec_wr, rbn_zone, x_wb, x_W4.
  intros a [Ha | [Ha | Ha]]; [left; rewrite Hsp in Ha; lia | right; left; lia | right; right; left; lia]. }
assert (AGf2 : forall a, (x_F c <= a < x_F c + 512 \/ x_FS c <= a < x_FS c + 64) -> ~ EE a ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a)
  by (intros a Ha He; exact (rbn_ag_frame c lyc Sc memc mdc regs mem2 EE HC HK a Ha He)).
split; [reflexivity|]. exists ly2, S2, regs2, mem2, md2.
split; [rewrite Rra; reflexivity|]. split; [|exact HP2].
assert (Rz : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z -> getr regs2 r = getr regs r).
{ intros r z Hz Hr. pose proof (HP2 z Hr) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X.
  rewrite X. exact (HR r ltac:(rewrite Hz; exact Hr)). }
(* the digits are bytes *)
assert (HchD : Forall (fun x => 0 <= x < 256) (bn_dec v 2))
  by (eapply Forall_impl; [|exact Hdig]; cbv beta; intros x Hx; lia).
assert (HGcs : garr8 SEGS (x_mem_at c mem2) (x_W4 c) cs).
{ eapply rbn_garr_keep; [exact HG0|]. intros x Hx. apply AGf2; [left; unfold x_W4 in *; lia|].
  subst EE. unfold tsb_dec_wr, x_wb, x_W4. rewrite Hsp. intros [X | [X | X]]; lia. }
assert (HGall : garr8 SEGS (x_mem_at c mem2) (x_W4 c) (cs ++ bn_dec v 2)).
{ apply rbn_garr_app; [exact HGcs|].
  rewrite HDv in HGd. change (Z.to_nat 2) with 2%nat in HGd.
  rewrite (fa2 (bn_dec v 2) 2 ltac:(lia)) in HGd. exact HGd. }
assert (U5 : forall z, 0 <= z < 32 -> bv_unsigned (Z_to_bv 5 z) = z)
  by (intros z Hz; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn [Z.of_N]; lia).
assert (HPc : aregs_preserved regs regs2).
{ intros r Hr. pose proof (HP2 r Hr) as X. rewrite X.
  apply HR. rewrite (U5 r ltac:(unfold acallee_saved in Hr; lia)). exact Hr. }
split.
{ eapply (rbn_live_keep c lyc Sc memc mdc regs ly2 S2 mem2 md2 regs2 EE HL HJ2 Hperm3 HPc HK HEz). }
split.
{ eapply (rbn_stem_keep c ly2 S2 mem2 md2 memc st HST HAR2).
  - intros cid pos Hin. split; [rewrite Hfrs2, Hfrs; right; exact Hin | exact (Efa2 cid pos)].
  - exact (rbn_ag_img c lyc Sc memc mem2 EE HK).
  - intros cid pos a Hin Hr.
    pose proof HK as (_ & _ & _ & A4).
    apply (A4 cid pos a ltac:(rewrite Hfrs; right; exact Hin)).
    + rewrite (Efa cid pos). unfold frame_rng in *. cbn [fst snd] in *. rewrite (Efa cid pos). exact Hr.
    + intros X. apply (rbn_caller_frame_out c lyc Sc memc mdc regs cid pos a HC Hin).
      * unfold frame_rng in *. cbn [fst snd] in *. rewrite (Efa cid pos). exact Hr.
      * exact (HEz a X). }
split; [rewrite (Rz 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia)); exact R20|].
split; [rewrite (Rz 21%bv 21 eq_refl ltac:(unfold acallee_saved; lia)); exact R21|].
split; [rewrite (Rz 24%bv 24 eq_refl ltac:(unfold acallee_saved; lia)); exact R24|].
split; [rewrite (Rz 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia)); exact R25|].
split; [rewrite (Rz 26%bv 26 eq_refl ltac:(unfold acallee_saved; lia)); exact R26|].
split.
{ eapply (rbn_scope_keep c memc mem2); [exact HSCO|].
  intros x Hx. apply AGf2; [right; lia|].
  destruct (rbn_fs_apart c lyc Sc memc mdc regs HC) as (Ha1 & Ha2 & Ha3).
  subst EE. unfold tsb_dec_wr, x_wb, x_W4. rewrite Hsp.
  intros [X | [X | X]]; clear - Hx X Ha1 Ha2 Ha3 Hs1 Hslo Hlo0 Hcl Hes HSD Hlen0; lia. }
split.
{ unfold rbn_sb, x_mem_at. cbn zeta.
  split; [exact Vp2|]. split; [exact Vcap2|].
  split; [rewrite length_app, Nat2Z.inj_add, Hlv; exact Vn2|].
  split; [exact Vov2|]. split; [left; reflexivity|].
  split; [rewrite length_app, Nat2Z.inj_add, Hlv; lia|].
  split; [apply Forall_app; split; [exact Hch | exact HchD] | exact HGall]. }
split; [exact HGall|].
rewrite length_app, Nat2Z.inj_add, Hlv. lia.
Qed.

(* the entry state of a run that only reads one window slot: the slot's region and s1's range *)
Definition rbn_ss_slot (off slot : Z) : sstate :=
  mkSS off sr_atoms
    [YP09.mkRegion (Some 9%nat) slot (slot + 8) 0 0 [YP09.mkChunk slot (CVal 8 (SOff 32 0))]] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma rbn_slot_entry : forall c lyc Sc memc mdc regs slot v,
  rbn_core B G c lyc Sc memc mdc regs -> rbn_slots c memc ->
  val_mem SEGS (x_mem_at c memc) (x_s1 c + slot) 8 v -> 0 <= v < 2 ^ 64 -> (slot = 40 \/ slot = 48) ->
  forall off,
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 v])) (rbn_ss_slot off slot)
    (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + off)) memc (seg_rom SEGS))).
Proof.
intros c lyc Sc memc mdc regs slot v HC Hslots HV Hv Hsl off.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hsb & Hs1m &
  _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof HC as (_ & HJ & _ & R2 & _ & _ & _ & R9 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
set (E := Eimg (Ereg regs [w64 v])).
assert (E9 : ew E 9 = w64 (x_s1 c))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 v)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
rewrite restrict_mkst_fx. unfold rbn_ss_slot. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- destruct Hsl as [-> | ->]; vm_compute; reflexivity.
- repeat apply Forall_cons; try apply Forall_nil. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [destruct Hsl; lia|]. split; [destruct Hsl; lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (x_s1 c) slot 8 (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact HV].
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; exact I]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
  split; [lia | split; [exact Hs1m | lia]].
Qed.
(* a run that writes nothing keeps every byte *)
Lemma rbn_run_kept : forall E rs (W : world SEGS) m m',
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  (forall b wlo whi, In (b, wlo, whi) (windows rs) -> whi <= wlo) ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Proof.
intros E rs W m m' HFr HW a Ha.
apply (kept_of_frame E rs (w_H W) m m' (fun _ => False) HFr); [|exact Ha|tauto].
intros b wlo whi x Hin Hx. pose proof (HW b wlo whi Hin). lia.
Qed.
(* rbn_m1 crosses a run that writes nothing *)
Lemma rbn_m1_kept : forall c st lyc Sc m md regs cs m' md',
  rbn_m1 c st lyc Sc m md regs cs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  rbn_m1 c st lyc Sc m' md' regs cs.
Proof.
intros c st lyc Sc m md regs cs m' md' HM HJ' AG.
pose proof HM as (HL & HST & R20 & R21 & R24 & R25 & R26 & HSCO & HSBO & HG0 & Hlen0).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & _).
destruct (rbn_geom c lyc Sc m md regs HC) as (HAR & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hsb & _ &
  HinF & Hfrs & Hf0 & Hfc & _ & _ & _ & _ & _ & _ & _ & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HK0 : rbn_k c lyc Sc m m' (fun a => (alloc_ceiling <= a < alloc_ceiling) \/ False)).
{ apply (rbn_k_of_plain c lyc Sc m md m m' alloc_ceiling alloc_ceiling (fun _ => False) HAR);
  [lia | lia | intros a _; split; [lia | tauto] | intros a Ha _ _; apply AG; lia]. }
assert (HK : rbn_k c lyc Sc m m' (fun a => rbn_zone c a /\ False))
  by (eapply rbn_k_mono; [exact HK0 | intros a [X|[]]; exfalso; lia]).
assert (HEz : forall a, (rbn_zone c a /\ False) -> rbn_zone c a) by tauto.
split; [eapply (rbn_live_keep c lyc Sc m md regs lyc Sc m' md' regs _ HL HJ' Hperm); [|exact HK | exact HEz]|].
{ intros r Hr. reflexivity. }
split.
{ eapply (rbn_stem_keep c lyc Sc m' md' m st HST (proj1 HJ')).
  - intros cid pos Hin. split; [rewrite Hfrs; right; exact Hin | exact (Efa cid pos)].
  - intros a H1 H2 H3. apply AG. pose proof (pa_segs_low a H1). unfold kLowMemEnd in *. lia.
  - intros cid pos a Hin Hr.
    assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
    assert (Hr' : in_zr a (frame_rng lyc (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))
      by (unfold frame_rng in *; cbn [fst snd] in *; rewrite (Efa cid pos); exact Hr).
    destruct (frame_zone SEGS B LAWS lyc Sc (x_W c) m md cid pos a HAR HinC Hr') as (Hza & [(Hz1 & _) | Hz2]);
    [destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) m md cid pos HAR HinC) as (Hfb0 & _ & _) |];
    apply AG; unfold kLowMemEnd in *; lia. }
split; [exact R20|]. split; [exact R21|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|].
split; [eapply (rbn_scope_keep c m m'); [exact HSCO|]; intros x Hx; apply AG;
  destruct (rbn_fs_apart c lyc Sc m md regs HC) as (Ha1 & Ha2 & _); unfold SHADOW_OFF in *; lia|].
split; [eapply (rbn_sb_keep c m m'); [exact HSBO| |]; intros x Hx; apply AG; unfold x_wb, x_W4 in *; lia|].
split; [|exact Hlen0].
eapply rbn_garr_keep; [exact HG0|]. intros x Hx. apply AG. unfold x_W4 in *. lia.
Qed.

(* 0x83000 .. 0x8300c (first) or 0x83010 .. 0x8301c (second): a0 = wb, a2 = 2, a1 = the slot's count,
   then the sb_dec call; back at the next pair *)
Lemma rbn_dec_stage : forall (second : bool) c st lyc Sc memc mdc regs cs,
  rbn_m1 c st lyc Sc memc mdc regs cs -> Z.of_nat (length cs) + 2 <= 4 ->
  SRr SEGS (x_W c)
    (mkCfg (mkst regs (Z_to_bv 64 (BASE + (if second then AF_reac_box_name + 0x29c else AF_reac_box_name + 0x28c)))
      memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (if second then AF_reac_box_name + 0x2ac else AF_reac_box_name + 0x29c)))
         mem' (seg_rom SEGS)) md' /\
       rbn_m1 c st lyc' Sc' mem' md' regs' (cs ++ bn_dec (if second then x_o c else x_i c) 2) /\
       aregs_preserved regs regs').
Proof.
intros second c st lyc Sc memc mdc regs cs HM Hcs.
pose proof HM as (HL & HST & R20 & R21 & R24 & R25 & R26 & HSCO & HSBO & HG0 & Hlen0).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hsb & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & Hby & Hpres & Hnf & Hnev & Hlive & Efa).
destruct (rbn_args_parts c Hargs) as (_ & _ & _ & Hoki & Hoko).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (U5 : forall z, 0 <= z < 32 -> bv_unsigned (Z_to_bv 5 z) = z)
  by (intros z Hz; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; cbn [Z.of_N]; lia).
set (v := if second then x_o c else x_i c).
set (slot := if second then 48 else 40).
assert (Hok : bn_ok v = true) by (subst v; destruct second; assumption).
destruct (reac_box_name.bn_ok_dec v Hok) as (Hv40 & _).
assert (HV : val_mem SEGS (x_mem_at c memc) (x_s1 c + slot) 8 v).
{ pose proof Hslots as (_ & _ & _ & _ & _ & S40 & S48 & _). subst v slot.
  destruct second; [rewrite Z.mod_small in S48 by lia; exact S48 | rewrite Z.mod_small in S40 by lia; exact S40]. }
pose proof (rbn_slot_entry c lyc Sc memc mdc regs slot v HC Hslots HV ltac:(lia)
  ltac:(subst slot; destruct second; [right | left]; reflexivity)
  (if second then AF_reac_box_name + 0x29c else AF_reac_box_name + 0x28c)) as HS.
remember (Eimg (Ereg regs [w64 v])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E9 : ew E 9 = w64 (x_s1 c))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 v)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (HAE : env_agree 32 (Ereg regs [w64 v]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
subst slot.
destruct second; cbn iota in HS |- *.
all: paj_run_shc RUNP RUNC HS HJ; [apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil] |].
all: assert (AG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a)
       by (apply (rbn_run_kept E _ (x_W c) memc (ms_mem ms) HFr); cbn; intros b wlo whi [X|[]]; injection X as <- <- <-; lia).
all: pose proof (rbn_m1_kept c st lyc Sc memc mdc regs cs (ms_mem ms) _ HM HJ AG) as HM1.
all: assert (HPrun : aregs_preserved regs (ms_regs ms))
       by (eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [w64 v] HS); [exact HAE | vm_compute; reflexivity]).
all: prreg HS (1%bv : bv 5) Rra; prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2.
all: rewrite U9 in Ra0; rewrite E32 in Ra1.
all: pmkst HS.
all: rewrite (PSIG IB_sb_dec AF_sb_dec eq_refl).
all: eapply SRr_mono;
  [ eapply (rbn_dec_call c st lyc Sc (ms_mem ms) _ regs cs v (ms_regs ms) _ _ HM1 eq_refl Hok Hcs);
    [ intros r Hr; pose proof (HPrun (bv_unsigned r) Hr) as X; rewrite Z_to_bv_bv_unsigned in X; exact X
    | first [ exact Rra | rewrite Rra; reflexivity ]
    | lia | reflexivity | exact Ra0 | exact Ra1 | exact Ra2 ]
  | ].
all: cbv beta; intros W2 c2 _ (-> & lyc' & Sc' & regs' & mem' & md' & -> & HM2 & HP2).
all: split; [reflexivity|]; exists lyc', Sc', regs', mem', md'; split; [reflexivity|].
all: split; [exact HM2 | exact (aregs_preserved_trans _ _ _ HPrun HP2)].
Qed.

(* ---- reading back what a run stored: a region's chunk is a val_mem / a garr8 ---- *)
Lemma rbn_byte_lit : forall v k, 0 <= v < 2 ^ 64 ->
  byte_of_word (Z_to_bv 64 v) (Z.of_nat k) = Z_to_bv 8 (le_byte v 8 k).
Proof.
intros v k Hv. unfold byte_of_word, le_byte. rewrite unsigned_lit_small by exact Hv.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small v (2 ^ 64)) by exact Hv.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma rbn_val_of_chunk : forall E m base off (e : sv) v,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8 e)) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  val_mem SEGS m (base + off) 8 v.
Proof.
intros E m base off e v Hc Hv Hr k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Eb & Mb).
cbn [YP09.c_off YP09.c_val cbyte] in Eb, Mb.
injection Eb as <-. rewrite Hv, (rbn_byte_lit v k Hr) in Mb. exact Mb.
Qed.
Lemma rbn_zero_of_chunk : forall E m base off,
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 1 (SLit 0))) ->
  val_mem SEGS m (base + off) 1 0.
Proof.
intros E m base off Hc k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k.
destruct (Hc 0 ltac:(cbn [YP09.c_len YP09.c_val cv_len]; lia)) as (b & Eb & Mb).
cbn [YP09.c_off YP09.c_val cbyte] in Eb, Mb. injection Eb as <-.
rewrite Z.add_0_r in Mb. cbn [Z.of_nat]. rewrite Z.add_0_r, Mb. reflexivity.
Qed.
Lemma rbn_region_of : forall E ss ms r,
  st_ok SEGS E ss ms -> In r (ss_mem ss) -> YP09.region_ok SEGS E (ms_mem ms) r.
Proof.
intros E ss ms r HS Hin.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _).
exact (proj1 (Forall_forall _ _) HRok r Hin).
Qed.
(* ---- the machine stack's shadow is zero, so a stack range is readable and its hull is visible ---- *)
Lemma rbn_mod4096_mod8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)). pose proof (Z.div_mod x 8 ltac:(lia)). lia.
Qed.
Lemma rbn_stack_shadow : forall c lyc Sc memc mdc regs q n,
  rbn_core B G c lyc Sc memc mdc regs ->
  ly_stk_lo lyc + 64 <= q -> q + n + 64 <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF q n /\
  shadow_hull_vis (aview SEGS (w_H (x_W c)) memc) q n.
Proof.
intros c lyc Sc memc mdc regs q n HC Hlo Hhi Hn.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
unfold page_aligned in Hpal, Hpah.
pose proof (rbn_mod4096_mod8 _ Hpal) as Hlo8. pose proof (rbn_mod4096_mod8 _ Hpah) as Hhi8.
pose proof (al_zshadow _ _ LAWS lyc Sc (x_W c) memc mdc (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
assert (Hsub : (ly_stk_hi lyc - ly_stk_lo lyc) mod 8 = 0).
{ pose proof (Z.div_mod (ly_stk_hi lyc) 8 ltac:(lia)) as D1. pose proof (Z.div_mod (ly_stk_lo lyc) 8 ltac:(lia)) as D2.
  rewrite Hlo8, Z.add_0_r in D2. rewrite Hhi8, Z.add_0_r in D1.
  pose proof (Z.mod_pos_bound (ly_stk_hi lyc - ly_stk_lo lyc) 8 ltac:(lia)) as D3.
  pose proof (Z.div_mod (ly_stk_hi lyc - ly_stk_lo lyc) 8 ltac:(lia)) as D4. lia. }
pose proof (zero_shadow_range (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF (ly_stk_lo lyc)
  (ly_stk_hi lyc - ly_stk_lo lyc) Hlo8 Hsub Hz) as HRA.
split; [eapply range_addressable_sub; [exact HRA | lia | lia]|].
intros s Hs.
assert (Hq8 : forall x y : Z, 0 <= y -> y <= x -> shadow_of_addr SHADOW_OFF y <= shadow_of_addr SHADOW_OFF x)
  by (intros x y Hy Hyx; unfold shadow_of_addr; pose proof (Z.div_le_mono y x 8 ltac:(lia) Hyx); lia).
assert (Hlo' : shadow_of_addr SHADOW_OFF (ly_stk_lo lyc) <= shadow_addr q / 8 * 8).
{ unfold shadow_addr in *. pose proof (Z.div_mod (SHADOW_OFF + q / 8) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + q / 8) 8 ltac:(lia)) as Dr.
  pose proof (Hq8 (q - 64) (ly_stk_lo lyc) ltac:(lia) ltac:(lia)) as H1.
  pose proof (Hq8 q (q - 64) ltac:(lia) ltac:(lia)) as H2.
  assert (Hd : shadow_of_addr SHADOW_OFF (q - 64) + 8 <= shadow_of_addr SHADOW_OFF q).
  { unfold shadow_of_addr. assert ((q - 64) / 8 + 8 <= q / 8) by (apply Z.div_le_lower_bound; [lia|];
      pose proof (Z.div_mod (q - 64) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q - 64) 8 ltac:(lia)); lia). lia. }
  unfold shadow_of_addr in *. lia. }
assert (Hhi' : shadow_addr (q + n - 1) / 8 * 8 + 8 <=
  shadow_of_addr SHADOW_OFF (ly_stk_lo lyc) + (ly_stk_hi lyc - ly_stk_lo lyc) / 8).
{ unfold shadow_addr, shadow_of_addr in *.
  pose proof (Z.div_mod (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (SHADOW_OFF + (q + n - 1) / 8) 8 ltac:(lia)) as Dr.
  assert (H1 : (q + n - 1) / 8 + 8 <= (ly_stk_hi lyc) / 8).
  { apply Z.div_le_lower_bound; [lia|].
    pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia)). lia. }
  assert (H2 : (ly_stk_hi lyc) / 8 = ly_stk_lo lyc / 8 + (ly_stk_hi lyc - ly_stk_lo lyc) / 8).
  { pose proof (Z.div_mod (ly_stk_hi lyc) 8 ltac:(lia)) as E1. pose proof (Z.div_mod (ly_stk_lo lyc) 8 ltac:(lia)) as E2.
    pose proof (Z.div_mod (ly_stk_hi lyc - ly_stk_lo lyc) 8 ltac:(lia)) as E3.
    rewrite Hlo8, Z.add_0_r in E2. rewrite Hhi8, Z.add_0_r in E1. rewrite Hsub, Z.add_0_r in E3. lia. }
  lia. }
assert (Hs' : exists i, 0 <= i < (ly_stk_hi lyc - ly_stk_lo lyc) / 8 /\
  s = shadow_of_addr SHADOW_OFF (ly_stk_lo lyc) + i)
  by (exists (s - shadow_of_addr SHADOW_OFF (ly_stk_lo lyc)); lia).
destruct Hs' as (i & Hi & ->). rewrite (Hz i Hi). discriminate.
Qed.

(* the frame's shadow bytes are present and not the runtime's own (AR_frames_law) *)
Lemma rbn_fs_present : forall c lyc Sc memc mdc regs,
  rbn_core B G c lyc Sc memc mdc regs ->
  forall i, 0 <= i < 64 -> apresent (w_H (x_W c)) memc (x_FS c + i) /\ ~ aowned B lyc Sc (x_FS c + i).
Proof.
intros c lyc Sc memc mdc regs HC i Hi.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ &
  HinF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Efa).
destruct (al_frames _ _ LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (_ & _ & _ & Hsh).
assert (HF : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F; rewrite Efa; reflexivity).
assert (HFSa : x_FS c = shadow_addr (x_F c)) by reflexivity.
rewrite HF in Hsh. rewrite HFSa. apply Hsh. change (fs_frame_bytes 3 / 8) with 64. exact Hi.
Qed.
(* the stem lies in app memory, off the shadow band, and its first byte is not NUL *)
Lemma rbn_stem_facts : forall c lyc Sc memc mdc regs st,
  rbn_core B G c lyc Sc memc mdc regs -> rbn_stem B G c memc st ->
  4096 <= st /\ st + Z.of_nat (length (x_stem c)) + 1 < 2 ^ 47 - 1 /\
  (st + 1 <= kLowShadowBeg \/ kHighMemBeg <= st) /\
  x_stem c <> [] /\ Forall (fun x => 0 < x < 256) (x_stem c) /\
  garr8 SEGS (x_mem_at c memc) st (x_stem c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) memc) SHADOW_OFF st 1.
Proof.
intros c lyc Sc memc mdc regs st HC HST.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & _ & _ & _ & _ & _ & _ & _ &
  HinF & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hne : x_stem c <> []).
{ unfold x_stem, bn_stem. destruct (x_sd c) as [|y r]; [|discriminate].
  unfold bn_STEM. destruct (x_f c =? 1); [discriminate|]. destruct (x_f c =? 2); [discriminate|].
  destruct (x_f c =? 3); discriminate. }
destruct HST as [(Hsd & -> & HCS & (cid & pos & Hin & Hfa1 & Hfa2)) | (Hsd & HI)].
- destruct HCS as (Hch & Hlen & Hpos & Hamr & HG & HRA & HHV & HTail).
  assert (Hst : x_stem c = x_sd c) by (unfold x_stem, bn_stem; destruct (x_sd c); [contradiction | reflexivity]).
  assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
  destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) memc mdc cid pos HAR HinC) as (Hf0 & Hfc & Hfapp).
  rewrite (Efa cid pos) in Hf0, Hfc, Hfapp.
  rewrite Hst in *.
  split; [lia|]. split; [lia|].
  split; [destruct Hfapp as (_ & [X|(X1 & X2)]);
          unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia|].
  split; [exact Hne|]. split; [exact Hch|].
  split; [exact HG|].
  eapply range_addressable_sub; [exact HRA | lia | lia].
- destruct HI as (Hlo & Hhi & Hch & HG & Hglob & Hfix & HTail).
  assert (Hst : x_stem c = bn_STEM (x_f c)) by (unfold x_stem, bn_stem; rewrite Hsd; reflexivity).
  rewrite Hst in *. destruct Hglob as (q & z & Hinq & Hq1 & Hq2).
  split; [lia|]. split; [lia|].
  split; [unfold kLowShadowBeg; lia|].
  split; [exact Hne|]. split; [exact Hch|]. split; [exact HG|].
  eapply (ro_usable_glob SEGS B G lyc Sc (x_W c) memc mdc q z st 1 GM Hinq HAR); lia.
Qed.

(* a range the memset zeroed is a val_mem of 0 *)
Lemma rbn_val_zero : forall (W : world SEGS) m a n,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS (w_H W) m (a + i) = Some 0) ->
  val_mem SEGS (mrestrict (w_H W) m) a n 0.
Proof.
intros W m a n H k Hk. specialize (H (Z.of_nat k) ltac:(lia)).
unfold aview in H. destruct (mbyte SEGS (mrestrict (w_H W) m) (a + Z.of_nat k)) as [b|] eqn:Eb;
  [|cbn [option_map] in H; discriminate].
cbn [option_map] in H. injection H as Hb. f_equal.
assert (HL0 : Z_to_bv 8 (le_byte 0 n k) = Z_to_bv 8 0).
{ unfold le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l, Z.mod_0_l by lia. reflexivity. }
transitivity (Z_to_bv 8 0); [apply bv_eq; rewrite Hb, Z_to_bv_unsigned; reflexivity | symmetry; exact HL0].
Qed.
(* the state at 0x83064: nm's struct and scope are set, wb holds w4 with its NUL *)
Definition rbn_m3 (c : rbx) (st : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live B G c lyc Sc memc mdc regs /\ rbn_stem B G c memc st /\ rbn_w4done c memc regs /\
  getr regs 20 = w64 (x_W4 c) /\ getr regs 25 = w64 st /\
  rbn_scope c memc 5 0 0xf8 0xf8 /\
  rbn_sb c memc (x_nb c) (x_NM c) 24 [] 0.
(* 0x83020 .. 0x83060: w4's NUL, nm's scope, nm's struct, then the memset of nb.n / nb.over *)
Definition rbn_ss_c : sstate :=
  mkSS (AF_reac_box_name + 0x2ac) sr_atoms
    [YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit 4))];
     YP09.mkRegion (Some 9%nat) 152 168 152 168 [];
     YP09.mkRegion (Some 20%nat) 4 5 4 5 [];
     YP09.mkRegion (Some 18%nat) 8 11 8 11 []] None
    (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF 4096 (2 ^ 47) 5); (21%nat, mkAF 5 5 0);
              (19%nat, mkAF 4096 (2 ^ 47) 6)]
             [mkAC BC_GEU (SAlu ALU_XOR (SOff 20 0) (SLit (-1))) (SLit 4)] []).
Ltac rbn_reg HS n HR :=
  let HRok := fresh "HRok" in pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & HRok & _);
  lazymatch type of HRok with Forall (YP09.region_ok _ ?Ek ?mx) ?rs =>
    let rs' := eval vm_compute in rs in
    let r := eval vm_compute in (nth n rs' got_regionP) in
    assert (HR : YP09.region_ok SEGS Ek mx r)
      by (apply (proj1 (Forall_forall _ _) HRok); change rs with rs'; cbn [In];
          repeat (first [left; reflexivity | right]))
  end; clear HRok.
(* a shadow byte of a 16-byte stack range of the window is in the shadow band: it is none of the bytes
   the stage writes *)
Lemma rbn_shq_out : forall c lyc Sc memc mdc regs q s,
  rbn_core B G c lyc Sc memc mdc regs -> x_s1 c <= q -> q + 16 <= x_sp0 c ->
  shadow_addr q - 7 <= s < shadow_addr (q + 15) + 8 ->
  0 <= s < 2 ^ 64 /\ ~ (x_s1 c + 152 <= s < x_s1 c + 184) /\ ~ (x_W4 c + 4 <= s < x_W4 c + 5) /\
  ~ (x_FS c + 8 <= s < x_FS c + 11) /\ ~ (x_s1 c - ESTACK <= s < x_s1 c).
Proof.
intros c lyc Sc memc mdc regs q s HC Hq1 Hq2 Hs.
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (YCbq.shadow_addr_bounds q ltac:(lia)) as HB1.
pose proof (YCbq.shadow_addr_bounds (q + 15) ltac:(lia)) as HB2.
assert (HqF : x_F c / 8 + 64 <= q / 8).
{ apply Z.div_le_lower_bound; [lia|].
  pose proof (Z.div_mod (x_F c) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)). lia. }
assert (HW4 : x_W4 c = x_F c + 32) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
unfold shadow_addr in *. rewrite HW4, HFS.
destruct Hfapp as (_ & [Hlow | (Hhi1 & Hhi2)]);
  unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, kHighShadowEnd, kLowMemEnd, ASAN_CEIL, kHighMemEnd in *;
  (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; lia).
Qed.
(* the shadow of a byte of the range, and the 8-aligned hull of the range's shadow, lie in that window *)
Lemma rbn_shq_byte : forall q x, 0 <= q -> q <= x < q + 16 ->
  shadow_addr q - 7 <= shadow_addr x < shadow_addr (q + 15) + 8.
Proof.
intros q x Hq Hx. unfold shadow_addr.
pose proof (Z.div_le_mono q x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_mono x (q + 15) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma rbn_shq_hull : forall q s,
  shadow_addr q / 8 * 8 <= s < shadow_addr (q + 16 - 1) / 8 * 8 + 8 ->
  shadow_addr q - 7 <= s < shadow_addr (q + 15) + 8.
Proof.
intros q s Hs. replace (q + 16 - 1) with (q + 15) in Hs by lia.
pose proof (Z.div_mod (shadow_addr q) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr q) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (q + 15)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (shadow_addr (q + 15)) 8 ltac:(lia)). lia.
Qed.
Lemma rbn_s1_c1 : forall c st lyc Sc memc mdc regs,
  rbn_m1 c st lyc Sc memc mdc regs (x_w4 c) ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2ac))) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2f0))) mem' (seg_rom SEGS)) md' /\
       rbn_m3 c st lyc' Sc' mem' md' regs').
Proof.
intros c st lyc Sc memc mdc regs HM.
pose proof HM as (HL & HST & R20 & R21 & R24 & R25 & R26 & HSCO & HSBO & HG0 & Hlen0).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & Hby & Hpres & Hnf & Hnev & Hlive & Efa).
destruct (rbn_zone_out c lyc Sc memc mdc regs HC) as (Zslots & Zsaved & Zflag & Zsc4 & Zsc16).
destruct (rbn_args_parts c Hargs) as (_ & _ & _ & Hoki & Hoko).
destruct (reac_box_name.bn_ok_dec (x_i c) Hoki) as (_ & Hli & _).
destruct (reac_box_name.bn_ok_dec (x_o c) Hoko) as (_ & Hlo & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hw4len : Z.of_nat (length (x_w4 c)) = 4)
  by (unfold x_w4, bn_w4; rewrite length_app, Hli, Hlo; reflexivity).
destruct (rbn_fs_apart c lyc Sc memc mdc regs HC) as (HFSlo & HFShi & HFSap).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HW4 : x_W4 c = x_F c + 32) by reflexivity.
assert (HNM : x_NM c = x_F c + 64) by reflexivity.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
assert (HF8 : x_F c mod 8 = 0).
{ pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8f.
  pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. rewrite Hal64, Z.add_0_r in D64. lia. }
pose proof HSBO as (V0 & V8 & V16 & V24 & _ & _ & Hchw & _).
(* the environment: no extra atoms *)
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E9 : ew E 9 = w64 (x_s1 c)) by (rewrite (EL 9%nat 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = w64 (x_FS c)) by (rewrite (EL 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = w64 (x_F c)) by (rewrite (EL 19%nat 19%bv eq_refl); exact R19).
assert (E20 : ew E 20 = w64 (x_W4 c)) by (rewrite (EL 20%nat 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = w64 5) by (rewrite (EL 21%nat 21%bv eq_refl); exact R21).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = x_FS c)
  by (rewrite E18; apply unsigned_lit_small; unfold SHADOW_OFF in *; lia).
assert (U19 : bv_unsigned (ew E 19) = x_F c) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = x_W4 c) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = 5) by (rewrite E21; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rbn_ss_c
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2ac))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ss_c. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_s1 c) 200 8 (SLit 4) 4);
        [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
      unfold x_wb in V16. rewrite Hw4len in V16.
      replace (x_s1 c + 184 + 16) with (x_s1 c + 200) in V16 by lia.
      change (N.to_nat 8) with 8%nat. exact V16.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite U20. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (Hby (x_W4 c + o) ltac:(lia))).
    + rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (proj1 (rbn_fs_present c lyc Sc memc mdc regs HC o ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18, U20.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold SHADOW_OFF in *. repeat split; lia.
  - split; [|split].
    + cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U19, U20, U21. change (2 ^ 5) with 32. change (2 ^ 6) with 64. change (2 ^ 0) with 1.
      rewrite Z.mod_1_r.
      split; [split; [lia | split; [exact Hs1m | lia]]|].
      split; [split; [lia | split; [|lia]]|].
      { rewrite HW4. pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64.
        rewrite Hal64, Z.add_0_r in D64.
        replace (x_F c + 32) with ((x_F c / 64 * 2 + 1) * 32) by lia. apply Z_mod_mult. }
      split; [split; [lia | split; [reflexivity | lia]]|].
      split; [|exact I]. split; [lia | split; [exact Hal64 | lia]].
    + cbn [f_conds conds_ok]. split; [|exact I].
      unfold acond_ok. cbn [ac_c ac_a ac_b].
      rewrite branch_geu_U, (U_not E 20 (x_W4 c) E20 ltac:(lia)), U_SLit.
      change (zcanon 4) with 4. apply negb_true_iff. apply Z.ltb_ge. lia.
    + exact I. }
paj_run_shc RUNP RUNC HS HJ.
{ unfold rbn_ss_c. cbn [ss_mem].
  apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 c - x_sp0 c));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 20%nat (x_W4 c));
    [reflexivity | exact U20 | cbn [YP09.r_wlo YP09.r_whi] |].
  { intros a Ha. right. right. right. exists 3, (x_fpos c). split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite (Efa 3 (x_fpos c)).
    change (fs_frame_bytes 3) with 512. unfold x_F in *. lia. }
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (x_FS c));
    [reflexivity | exact U18 | cbn [YP09.r_wlo YP09.r_whi] | apply awr_ok_nil].
  { intros a Ha. right. right. right. exists 3, (x_fpos c). split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite (Efa 3 (x_fpos c)).
    change (fs_frame_bytes 3 / 8) with 64. unfold shadow_addr, x_FS, x_F in *. lia. } }
(* the bytes the run wrote: nm's struct, w4's NUL, nm's three scope bytes *)
rbn_reg HS 1%nat HRnb. rbn_reg HS 2%nat HRw4. rbn_reg HS 3%nat HRfs.
destruct HRnb as (_ & _ & _ & HCHnb). cbn [YP09.r_chunks YP09.r_base base_val] in HCHnb. rewrite U9 in HCHnb.
destruct HRw4 as (_ & _ & _ & HCHw4). cbn [YP09.r_chunks YP09.r_base base_val] in HCHw4. rewrite U20 in HCHw4.
destruct HRfs as (_ & _ & _ & HCHfs). cbn [YP09.r_chunks YP09.r_base base_val] in HCHfs. rewrite U18 in HCHfs.
pose proof (Forall_inv HCHnb) as Hc160. pose proof (Forall_inv (Forall_inv_tail HCHnb)) as Hc152.
pose proof (Forall_inv HCHw4) as Hc4.
pose proof (Forall_inv HCHfs) as Hc10. pose proof (Forall_inv (Forall_inv_tail HCHfs)) as Hc9.
pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail HCHfs))) as Hc8.
assert (Vcap : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_nb c + 8) 8 24).
{ unfold x_nb. replace (x_s1 c + 152 + 8) with (x_s1 c + 160) by lia.
  apply (rbn_val_of_chunk E _ (x_s1 c) 160 (SLit 24) 24 Hc160); [cbn [sv_denot]; reflexivity | lia]. }
assert (Vnbp : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_nb c) 8 (x_NM c)).
{ unfold x_nb. apply (rbn_val_of_chunk E _ (x_s1 c) 152 (SOff 19 64) (x_NM c) Hc152);
  [cbn [sv_denot]; rewrite E19, unsigned_lit_small by lia; rewrite HNM; reflexivity | rewrite HNM; lia]. }
assert (VNUL : val_mem SEGS (x_mem_at c (ms_mem ms)) (x_W4 c + 4) 1 0)
  by (exact (rbn_zero_of_chunk E _ (x_W4 c) 4 Hc4)).
assert (Vsc : forall j, 8 <= j < 11 -> aview SEGS (w_H (x_W c)) (ms_mem ms) (x_FS c + j) = Some 0).
{ intros j Hj. assert (Hj3 : j = 8 \/ j = 9 \/ j = 10) by lia.
  destruct Hj3 as [Hj8 | [Hj9 | Hj10]]; subst j;
  [ exact (aview_of_val_mem1 SEGS _ _ _ 0 (rbn_zero_of_chunk E _ (x_FS c) 8 Hc8) ltac:(lia))
  | exact (aview_of_val_mem1 SEGS _ _ _ 0 (rbn_zero_of_chunk E _ (x_FS c) 9 Hc9) ltac:(lia))
  | exact (aview_of_val_mem1 SEGS _ _ _ 0 (rbn_zero_of_chunk E _ (x_FS c) 10 Hc10) ltac:(lia)) ]. }
(* what the run kept *)
assert (AG3 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (x_s1 c + 152 <= a < x_s1 c + 168) -> ~ (x_W4 c + 4 <= a < x_W4 c + 5) -> ~ (x_FS c + 8 <= a < x_FS c + 11) ->
  aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha H1 H2 H3.
  apply (kept_of_frame E (ss_mem rbn_ss_c) (w_H (x_W c)) memc (ms_mem ms)
    (fun x => (x_s1 c + 152 <= x < x_s1 c + 168) \/ (x_W4 c + 4 <= x < x_W4 c + 5) \/
              (x_FS c + 8 <= x < x_FS c + 11)) HFr); [| exact Ha | tauto].
  intros b wlo whi x Hin Hx. unfold rbn_ss_c in Hin. cbn [ss_mem windows map] in Hin.
  destruct Hin as [Eq|[Eq|[Eq|[Eq|[]]]]]; injection Eq as <- <- <-; cbn [base_val] in Hx;
  [ lia
  | rewrite U9 in Hx; left; lia
  | rewrite U20 in Hx; right; left; lia
  | rewrite U18 in Hx; right; right; lia ]. }
(* the memset call *)
prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
prreg HS (27%bv : bv 5) Rs11.
rewrite U9 in Ra0. rewrite U19 in Rs11.
rewrite (EL 2%nat 2%bv eq_refl) in Rsp. rewrite (EL 3%nat 3%bv eq_refl) in Rgp.
rewrite (EL 4%nat 4%bv eq_refl) in Rtp.
assert (Qsp : spZ (ms_regs ms) = x_s1 c)
  by (unfold spZ; rewrite Rsp, R2; apply unsigned_lit_small; lia).
pmkst HS.
eapply SRr_mono.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
  eapply (aj_intrin_at SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET (x_W c) (ms_regs msX)
    (ms_mem msX) RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc _ 0 (x_s1 c + 168) 0 16 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2f0))) HJ) end.
  - rewrite Ra0. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite Qsp. lia.
  - pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1m, Z.add_0_r in D.
    pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as D2. rewrite Hsp0al, Z.add_0_r in D2.
    replace (x_s1 c - x_sp0 c) with ((x_s1 c / 32 * 2 - x_sp0 c / 16) * 16) by lia. apply Z_mod_mult.
  - lia.
  - lia.
  - rewrite Rgp. exact R3.
  - rewrite Rtp. exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [unfold AF_reac_box_name; lia | reflexivity].
  - intros a Ha. split; [left; lia|]. lia.
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. right. lia.
  - destruct (rbn_stack_shadow c lyc Sc memc mdc regs (x_s1 c + 168) 16 HC ltac:(lia) ltac:(lia) ltac:(lia))
      as (HRA & HHV).
    eapply (rbn_ra_keep (x_W c) memc (ms_mem ms)); [exact HRA|].
    intros x Hx.
    destruct (rbn_shq_out c lyc Sc memc mdc regs (x_s1 c + 168) (shadow_addr x) HC ltac:(lia) ltac:(lia)
      (rbn_shq_byte (x_s1 c + 168) x ltac:(lia) Hx)) as (Q1 & Q2 & Q3 & Q4 & _).
    apply AG3; [exact Q1 | lia | exact Q3 | exact Q4].
  - intros _.
    destruct (rbn_stack_shadow c lyc Sc memc mdc regs (x_s1 c + 168) 16 HC ltac:(lia) ltac:(lia) ltac:(lia))
      as (HRA & HHV).
    intros s Hs.
    destruct (rbn_shq_out c lyc Sc memc mdc regs (x_s1 c + 168) s HC ltac:(lia) ltac:(lia)
      (rbn_shq_hull (x_s1 c + 168) s Hs)) as (Q1 & Q2 & Q3 & Q4 & _).
    rewrite (AG3 s Q1 ltac:(lia) Q3 Q4). exact (HHV s Hs).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha02 & Heff & Hfr2 & Hpres2).
change (0 mod 256) with 0 in Heff.
assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c + 168 <= a < x_s1 c + 184) ->
  ~ (x_s1 c - ESTACK <= a < x_s1 c) ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) (ms_mem ms) a)
  by (intros a H1 H2 H3; apply Hfr2; lia).
pose (EZ := fun a => (x_s1 c + 152 <= a < x_s1 c + 184) \/ (x_W4 c + 4 <= a < x_W4 c + 5) \/
                     (x_FS c + 8 <= a < x_FS c + 11) \/ (x_s1 c - ESTACK <= a < x_s1 c)).
assert (AGt : forall a, 0 <= a < 2 ^ 64 -> ~ EZ a ->
  aview SEGS (w_H (x_W c)) mem2 a = aview SEGS (w_H (x_W c)) memc a).
{ intros a Ha He. subst EZ. cbv beta in He.
  assert (H1 : ~ (x_s1 c + 152 <= a < x_s1 c + 184)) by tauto.
  assert (H2 : ~ (x_W4 c + 4 <= a < x_W4 c + 5)) by tauto.
  assert (H3 : ~ (x_FS c + 8 <= a < x_FS c + 11)) by tauto.
  assert (H4 : ~ (x_s1 c - ESTACK <= a < x_s1 c)) by tauto.
  rewrite (AG2 a Ha ltac:(lia) H4). apply AG3; [exact Ha | lia | exact H2 | exact H3]. }
pose proof (frm_off_imgP B lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as Hoff.
rewrite (Efa 3 (x_fpos c)) in Hoff. change (fs_frame_bytes 3) with 512 in Hoff.
change (frame_addr (x_ly c) 3 (x_fpos c)) with (x_F c) in Hoff.
assert (HK : rbn_k c lyc Sc memc mem2 (fun a => (alloc_ceiling <= a < alloc_ceiling) \/ EZ a)).
{ apply (rbn_k_of_plain c lyc Sc memc mdc memc mem2 alloc_ceiling alloc_ceiling EZ HAR);
  [lia | lia | | intros a Ha _ He; apply AGt; [exact Ha | exact He]].
  intros a Hi. split; [lia|]. pose proof (pa_img_range a Hi) as HR.
  subst EZ. cbv beta. intros [X|[X|[X|X]]]; lia. }
assert (HEz : forall a, ((alloc_ceiling <= a < alloc_ceiling) \/ EZ a) -> rbn_zone c a).
{ intros a [X|X]; [exfalso; lia|]. subst EZ. cbv beta in X. unfold rbn_zone.
  destruct X as [X|[X|[X|X]]];
  [right; left; lia | right; right; left; lia | right; right; right; lia | left; lia]. }
assert (HKEPT : forall r, In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26]%bv -> getr (ms_regs ms) r = getr regs r)
  by (apply (regs_kept_of_st_ok SEGS E _ _ regs (@nil word) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity]).
assert (RG : forall (r : bv 5) z, bv_unsigned r = z -> acallee_saved z ->
  In r [2;3;4;8;9;18;19;20;21;22;23;24;25;26]%bv -> getr regs2 r = getr regs r).
{ intros r z Hz Hr Hin. pose proof (HP2 z Hr) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X.
  rewrite X. exact (HKEPT r Hin). }
assert (R27' : getr regs2 27 = w64 (x_NM c)).
{ assert (Hz : bv_unsigned (27%bv : bv 5) = 27) by reflexivity.
  pose proof (HP2 27 ltac:(unfold acallee_saved; lia)) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X.
  rewrite X, Rs11, HNM. reflexivity. }
split; [reflexivity|]. exists lyc, Sc, regs2, mem2, md2. split; [reflexivity|].
split.
{ eapply (rbn_live_keep9 c lyc Sc memc mdc regs lyc Sc mem2 md2 regs2 _ HL HJ2 Hperm);
  [ exact (RG 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact (RG 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto))
  | exact HK | exact HEz ]. }
split.
{ eapply (rbn_stem_keep c lyc Sc mem2 md2 memc st HST (proj1 HJ2)).
  - intros cid pos Hin. split; [rewrite Hfrs; right; exact Hin | exact (Efa cid pos)].
  - exact (rbn_ag_img c lyc Sc memc mem2 _ HK).
  - intros cid pos a Hin Hr.
    pose proof HK as (_ & _ & _ & A4).
    apply (A4 cid pos a ltac:(rewrite Hfrs; right; exact Hin)).
    + unfold frame_rng in *. cbn [fst snd] in *. rewrite (Efa cid pos). exact Hr.
    + intros X. apply (rbn_caller_frame_out c lyc Sc memc mdc regs cid pos a HC Hin).
      * unfold frame_rng in *. cbn [fst snd] in *. rewrite (Efa cid pos). exact Hr.
      * exact (HEz a X). }
split.
{ split.
  { eapply (rbn_sb_keep c memc mem2); [exact HSBO| |];
    intros x Hx; apply AGt; [unfold x_wb in *; lia | | unfold x_W4 in *; lia |];
    subst EZ; cbv beta; unfold x_wb, x_W4 in *; rewrite Hw4len in *;
    intros [X|[X|[X|X]]]; lia. }
  split; [|exact R27'].
  apply rbn_garr_app.
  - eapply rbn_garr_keep; [exact HG0|]. intros x Hx. rewrite Hw4len in Hx.
    apply AGt; [unfold x_W4 in *; lia|]. subst EZ. cbv beta. intros [X|[X|[X|X]]];
      unfold x_W4 in *; lia.
  - rewrite Hw4len. intros j Hj. cbn [length] in Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
    cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [|lia].
    eapply rbn_val_keep; [exact VNUL|]. intros y Hy. cbn [Z.of_nat] in Hy.
    apply AG2; [unfold x_W4 in *; lia | unfold x_W4 in *; lia | unfold x_W4 in *; lia]. }
split; [rewrite (RG 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto)); exact R20|].
split.
{ rewrite (RG 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia) ltac:(cbn [In]; tauto)). exact R25. }
split.
{ pose proof HSCO as (S4 & S8 & S16 & S24). unfold rbn_scope. cbn zeta.
  split.
  { rewrite (AGt (x_FS c + 4) ltac:(lia) ltac:(subst EZ; cbv beta; intros [X|[X|[X|X]]]; lia)). exact S4. }
  split.
  { intros j Hj. rewrite (AG2 (x_FS c + j) ltac:(lia) ltac:(lia) ltac:(lia)). exact (Vsc j Hj). }
  split.
  { intros j Hj. rewrite (AGt (x_FS c + j) ltac:(lia) ltac:(subst EZ; cbv beta; intros [X|[X|[X|X]]]; lia)).
    exact (S16 j Hj). }
  { intros j Hj. rewrite (AGt (x_FS c + j) ltac:(lia) ltac:(subst EZ; cbv beta; intros [X|[X|[X|X]]]; lia)).
    exact (S24 j Hj). } }
unfold rbn_sb, x_mem_at. cbn zeta.
split.
{ eapply rbn_val_keep; [exact Vnbp|]. intros y Hy. cbn [Z.of_nat] in Hy.
  apply AG2; unfold x_nb in *; lia. }
split.
{ eapply rbn_val_keep; [exact Vcap|]. intros y Hy. cbn [Z.of_nat] in Hy.
  apply AG2; unfold x_nb in *; lia. }
split.
{ cbn [length Z.of_nat]. unfold x_nb. replace (x_s1 c + 152 + 16) with (x_s1 c + 168) by lia.
  apply (rbn_val_zero (x_W c) mem2 (x_s1 c + 168) 8). intros i Hi. cbn [Z.of_nat] in Hi.
  exact (Heff i ltac:(lia)). }
split.
{ unfold x_nb. replace (x_s1 c + 152 + 24) with (x_s1 c + 168 + 8) by lia.
  apply (rbn_val_zero (x_W c) mem2 (x_s1 c + 168 + 8) 4). intros i Hi. cbn [Z.of_nat] in Hi.
  replace (x_s1 c + 168 + 8 + i) with (x_s1 c + 168 + (8 + i)) by lia.
  exact (Heff (8 + i) ltac:(lia)). }
split; [left; reflexivity|].
split; [cbn [length Z.of_nat]; lia|].
split; [apply Forall_nil|].
intros j Hj. cbn [length] in Hj. lia.
Qed.

(* rbn_m3 crosses a run that writes nothing *)
Lemma rbn_m3_kept : forall c st lyc Sc m md regs m' md' regs',
  rbn_m3 c st lyc Sc m md regs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  getr regs' 20 = getr regs 20 -> getr regs' 25 = getr regs 25 -> getr regs' 27 = getr regs 27 ->
  rbn_m3 c st lyc Sc m' md' regs'.
Proof.
intros c st lyc Sc m md regs m' md' regs' HM HJ' AG Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q20 Q25 Q27.
pose proof HM as (HL & HST & (HWsb & HWg & R27) & R20 & R25 & HSCO & HNsb).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & _).
destruct (rbn_geom c lyc Sc m md regs HC) as (HAR & _ & Hcl & H47 & Hlo0 & Hslo & _ & _ & Hsb & _ &
  HinF & Hfrs & Hf0 & Hfc & _ & _ & _ & _ & _ & _ & _ & Efa).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (rbn_args_parts c Hargs) as (_ & _ & _ & Hoki & Hoko).
destruct (reac_box_name.bn_ok_dec (x_i c) Hoki) as (_ & Hli & _).
destruct (reac_box_name.bn_ok_dec (x_o c) Hoko) as (_ & Hlo & _).
assert (Hw4len : Z.of_nat (length (x_w4 c)) = 4)
  by (unfold x_w4, bn_w4; rewrite length_app, Hli, Hlo; reflexivity).
assert (HK0 : rbn_k c lyc Sc m m' (fun a => (alloc_ceiling <= a < alloc_ceiling) \/ False)).
{ apply (rbn_k_of_plain c lyc Sc m md m m' alloc_ceiling alloc_ceiling (fun _ => False) HAR);
  [lia | lia | intros a _; split; [lia | tauto] | intros a Ha _ _; apply AG; lia]. }
assert (HK : rbn_k c lyc Sc m m' (fun a => rbn_zone c a /\ False))
  by (eapply rbn_k_mono; [exact HK0 | intros a [X|[]]; exfalso; lia]).
assert (HEz : forall a, (rbn_zone c a /\ False) -> rbn_zone c a) by tauto.
split; [eapply (rbn_live_keep9 c lyc Sc m md regs lyc Sc m' md' regs' _ HL HJ' Hperm);
  [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q22 | exact Q23
  | exact HK | exact HEz]|].
split.
{ eapply (rbn_stem_keep c lyc Sc m' md' m st HST (proj1 HJ')).
  - intros cid pos Hin. split; [rewrite Hfrs; right; exact Hin | exact (Efa cid pos)].
  - intros a H1 H2 H3. apply AG. pose proof (pa_segs_low a H1). unfold kLowMemEnd in *. lia.
  - intros cid pos a Hin Hr.
    assert (HinC : In (cid, pos) (frames Sc)) by (rewrite Hfrs; right; exact Hin).
    assert (Hr' : in_zr a (frame_rng lyc (cid, pos)) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))
      by (unfold frame_rng in *; cbn [fst snd] in *; rewrite (Efa cid pos); exact Hr).
    destruct (frame_zone SEGS B LAWS lyc Sc (x_W c) m md cid pos a HAR HinC Hr') as (Hza & [(Hz1 & _) | Hz2]);
    [destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) m md cid pos HAR HinC) as (Hfb0 & _ & _) |];
    apply AG; unfold kLowMemEnd in *; lia. }
split.
{ split; [eapply (rbn_sb_keep c m m'); [exact HWsb| |]; intros x Hx; apply AG; unfold x_wb, x_W4 in *; lia|].
  split; [|rewrite Q27; exact R27].
  eapply rbn_garr_keep; [exact HWg|]. intros x Hx. apply AG. unfold x_W4 in *.
  rewrite length_app in Hx. cbn [length] in Hx. rewrite Nat2Z.inj_add, Hw4len in Hx. lia. }
split; [rewrite Q20; exact R20|]. split; [rewrite Q25; exact R25|].
split; [eapply (rbn_scope_keep c m m'); [exact HSCO|]; intros x Hx; apply AG;
  destruct (rbn_fs_apart c lyc Sc m md regs HC) as (Ha1 & Ha2 & _); unfold SHADOW_OFF in *; lia|].
eapply (rbn_sb_keep c m m'); [exact HNsb| |]; intros x Hx; apply AG; unfold x_nb, x_NM in *; cbn [length] in *; lia.
Qed.

(* 0x83064 .. 0x83084: the stem's first byte (shadow-checked) and the copy loop's registers *)
Definition rbn_ss_d : sstate :=
  mkSS (AF_reac_box_name + 0x2f0) sr_atoms
    [YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]] None
    (mkFacts [(22%nat, mkAF SB SB 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0); (32%nat, mkAF 1 255 0)] [] []).
Definition rbn_SH_d : list shent := [mkSHE 25 0 1].
Lemma rbn_s1_c2 : forall c st lyc Sc memc mdc regs,
  rbn_m3 c st lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2f0))) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x314))) mem' (seg_rom SEGS)) md' /\
       rbn_C2 B G c st 0 lyc' Sc' mem' md' regs').
Proof.
intros c st lyc Sc memc mdc regs HM.
pose proof HM as (HL & HST & HW4d & R20 & R25 & HSCO & HNsb).
pose proof HL as (HC & Hargs & Hbuf & Hslots & R22).
pose proof HC as (HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & Hby & Hpres & Hnf & Hnev & Hlive & Efa).
destruct (rbn_stem_facts c lyc Sc memc mdc regs st HC HST)
  as (Hst0 & Hst1 & Hstband & Hstne & Hstch & HstG & HstRA).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSBv : SB = SHADOW_OFF) by reflexivity.
set (b0 := nth 0 (x_stem c) 0).
assert (Hb0 : 0 < b0 < 256).
{ subst b0. destruct (x_stem c) as [|y r]; [contradiction|].
  cbn [nth]. exact (Forall_inv Hstch). }
assert (Hlenstem : 0 < Z.of_nat (length (x_stem c)))
  by (destruct (x_stem c) as [|y r]; [contradiction | cbn [length]; lia]).
remember (Eimg (Ereg regs [w64 b0])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E22 : ew E 22 = w64 SHADOW_OFF) by (rewrite (EL 22%nat 22%bv eq_refl); exact R22).
assert (E25 : ew E 25 = w64 st) by (rewrite (EL 25%nat 25%bv eq_refl); exact R25).
assert (E20 : ew E 20 = w64 (x_W4 c)) by (rewrite (EL 20%nat 20%bv eq_refl); exact R20).
assert (E32 : ew E 32 = w64 b0)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF)
  by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U25 : bv_unsigned (ew E 25) = st) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = b0) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HAE : env_agree 32 (Ereg regs [w64 b0]) E)
  by (subst E; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E rbn_ss_d
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x2f0))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ss_d. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil. unfold YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ st 0 1 (SOff 32 0) b0);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    destruct (HstG 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (HV & _).
    cbn [Z.of_nat] in HV. rewrite Z.add_0_r in HV |- *.
    replace (nth 0 (x_stem c ++ [0]) 0) with b0 in HV
      by (subst b0; rewrite app_nth1 by (destruct (x_stem c); [contradiction | cbn [length]; lia]); reflexivity).
    exact HV.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U22, U25, U32, HSBv. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
    split; [split; [lia | split; [reflexivity | lia]]|].
    split; [split; [lia | split; [reflexivity | lia]]|].
    split; [|exact I]. split; [lia | split; [reflexivity | lia]]. }
assert (SHOK : sh_ok SEGS (SOff 22 0) rbn_SH_d E (mrestrict (w_H (x_W c)) memc)).
{ unfold rbn_SH_d. apply Forall_cons; [|apply Forall_nil]. unfold shent_ok, app_apart.
  cbn [she_m she_lo she_hi]. rewrite !U_SOff, U22, U25, !Z.add_0_r.
  rewrite !(zcanon_id SHADOW_OFF) by (unfold SHADOW_OFF, M64; lia).
  rewrite !(zcanon_id st) by (unfold M64; lia).
  split.
  - replace (st + 0) with st by lia. exact HstRA.
  - intros a Ha. cbn [Z.min Z.max] in Ha.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_box_name + 0x314).
{ unfold rbn_ss_d. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia | apply awr_ok_nil]. }
assert (AG : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H (x_W c)) (ms_mem ms) a = aview SEGS (w_H (x_W c)) memc a).
{ apply (rbn_run_kept E _ (x_W c) memc (ms_mem ms) HFr).
  unfold rbn_ss_d. cbn [ss_mem windows map]. intros b wlo whi [X|[]]. injection X as <- <- <-. lia. }
assert (HKEPT : forall r, In r [2;3;4;8;9;18;19;20;22;23;25;27]%bv -> getr (ms_regs ms) r = getr regs r)
  by (apply (regs_kept_of_st_ok_pi _ _ _ regs [w64 b0] _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity]).
pose proof (rbn_m3_kept c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms) HM HJ AG
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)
  ltac:(apply HKEPT; cbn [In]; tauto) ltac:(apply HKEPT; cbn [In]; tauto)) as HM3.
pose proof HM3 as (HL' & HST' & HW4d' & R20' & R25' & HSCO' & HNsb').
prreg HS (10%bv : bv 5) Ra0; prreg HS (21%bv : bv 5) Rs5; prreg HS (26%bv : bv 5) Rs10;
prreg HS (24%bv : bv 5) Rs8.
rewrite E32 in Ra0. rewrite E25 in Rs5. rewrite U25 in Rs10.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists lyc, Sc, (ms_regs ms), (ms_mem ms). eexists.
split; [reflexivity|].
split; [exact HL'|]. split; [exact HST'|]. split; [exact HW4d'|].
split; [change (Z.of_nat (length (x_stem c))) with (Z.of_nat (length (x_stem c))); lia|].
split; [change (Z.to_nat 0) with 0%nat; rewrite Ra0; reflexivity|].
split; [rewrite Z.add_0_r; exact Rs5|].
split; [rewrite Z.add_0_r; exact Rs10|].
split; [rewrite Rs8; reflexivity|].
split; [exact R20'|]. split; [exact R25'|].
split; [exact HSCO'|].
change (Z.to_nat 0) with 0%nat. cbn [firstn]. unfold sbm_str. cbn [fold_left fst snd].
exact HNsb'.
Qed.

(* ---- the segment: C1 0x83000 (+0x28c) -> C2 0x83088 (+0x314), i = 0 ---- *)
Lemma rbn_seg_c1_c2 : forall c st lyc Sc memc mdc regs,
  rbn_C1 B G c st lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x28c)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x314)) mem' (seg_rom SEGS)) md' /\
       rbn_C2 B G c st 0 lyc' Sc' mem' md' regs').
Proof.
intros c st lyc Sc memc mdc regs HC1.
pose proof HC1 as (HL & HST & R20 & R21 & R24 & R25 & R26 & HSCO & HSBO).
pose proof HL as (HC & Hargs & _).
destruct (rbn_args_parts c Hargs) as (_ & _ & _ & Hoki & Hoko).
destruct (reac_box_name.bn_ok_dec (x_i c) Hoki) as (_ & Hli & _).
destruct (reac_box_name.bn_ok_dec (x_o c) Hoko) as (_ & Hlo & _).
assert (HM : rbn_m1 c st lyc Sc memc mdc regs []).
{ split; [exact HL|]. split; [exact HST|]. split; [exact R20|]. split; [exact R21|].
  split; [exact R24|]. split; [exact R25|]. split; [exact R26|]. split; [exact HSCO|].
  split; [exact HSBO|]. split; [intros j Hj; cbn [length] in Hj; lia | cbn [length]; lia]. }
replace (BASE + AF_reac_box_name + 0x28c) with (BASE + (AF_reac_box_name + 0x28c)) by lia.
replace (BASE + AF_reac_box_name + 0x314) with (BASE + (AF_reac_box_name + 0x314)) by lia.
eapply SRr_bind; [exact (rbn_dec_stage false c st lyc Sc memc mdc regs [] HM ltac:(cbn [length]; lia))|].
cbv beta. intros W1 c1 _ (-> & ly1 & S1 & regs1 & mem1 & md1 & -> & HM1 & _).
eapply SRr_bind;
  [exact (rbn_dec_stage true c st ly1 S1 mem1 md1 regs1 ([] ++ bn_dec (x_i c) 2) HM1
     ltac:(rewrite length_app, Hli; cbn [length]; lia))|].
cbv beta. intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & -> & HM2 & _).
replace (([] ++ bn_dec (x_i c) 2) ++ bn_dec (x_o c) 2) with (x_w4 c) in HM2
  by (unfold x_w4, bn_w4; rewrite app_nil_l; reflexivity).
eapply SRr_bind; [exact (rbn_s1_c1 c st ly2 S2 mem2 md2 regs2 HM2)|].
cbv beta. intros W3 c3 _ (-> & ly3 & S3 & regs3 & mem3 & md3 & -> & HM3).
exact (rbn_s1_c2 c st ly3 S3 mem3 md3 regs3 HM3).
Qed.


(* ============================================================================================
   Part C: rbn_seg_c3_c45, C3 0x830cc (+0x358) -> C4 0x83128 (+0x3b4), j = 0, or C5 0x8316c (+0x3f8).
   Five runs of the plain engine, cut at the three calls (strlen 0x830dc, bcmp 0x83104, sb_ch 0x83114).
   Each run rebuilds st_ok_pi from the machine registers and the memory facts; nothing symbolic crosses a call.
   ============================================================================================ *)
(* ---- C0. small facts ---- *)
Lemma rbn2_av_garr : forall (W : world SEGS) m a l j, garr8 SEGS (mrestrict (w_H W) m) a l -> (j < length l)%nat ->
  aview SEGS (w_H W) m (a + Z.of_nat j) = Some (nth j l 0).
Proof.
intros W m a l j Hg Hj. destruct (Hg j Hj) as [Hv Hr]. exact (aview_of_val_mem1 SEGS (w_H W) m _ _ Hv Hr).
Qed.
Lemma rbn2_w4 : forall c, reac_box_name_c.bn_args_ok (x_name c) (x_name_len c) (x_token c) (x_token_len c)
    (x_display c) (x_display_len c) (x_i c) (x_o c) = true ->
  length (x_w4 c) = 4%nat /\ Forall (fun x => 48 <= x <= 57) (x_w4 c).
Proof.
intros c H. unfold reac_box_name_c.bn_args_ok in H.
repeat rewrite andb_true_iff in H. destruct H as ((((((((_ & _) & _) & _) & _) & _) & Hi) & Ho) & _).
destruct (reac_box_name.bn_ok_dec (x_i c) Hi) as (_ & Li & _ & _ & _ & Di & _).
destruct (reac_box_name.bn_ok_dec (x_o c) Ho) as (_ & Lo & _ & _ & _ & Do & _).
unfold x_w4, bn_w4. rewrite length_app, Li, Lo. split; [reflexivity|]. apply Forall_app; split; assumption.
Qed.
Lemma rbn2_m8 : forall x, x mod 4096 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 4096 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D. replace (4096 * (x / 4096)) with ((512 * (x / 4096)) * 8) by lia. apply Z_mod_mult.
Qed.
(* a struct on the machine stack: the stack's shadow is zero (AR_zshadow_law) *)
Lemma rbn2_stk_ra : forall lyc Sc W m md b n, AR SEGS B lyc Sc W m md ->
  ly_stk_lo lyc <= b -> b + n <= ly_stk_hi lyc ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF b n.
Proof.
intros lyc Sc W m md b n HAR Hlo Hhi.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS lyc Sc W m md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah.
eapply range_addressable_sub;
[ apply zero_shadow_range; [ exact (rbn2_m8 _ Hpal) | | exact Hz ] | lia | lia ].
apply rbn2_m8. rewrite Zminus_mod, Hpal, Hpah. reflexivity.
Qed.

(* ---- C1. the registers a step keeps (those the cut points speak about) ---- *)
Definition rbn2_rk (r0 r : bvmap 5 word) : Prop :=
  getr r 2 = getr r0 2 /\ getr r 3 = getr r0 3 /\ getr r 4 = getr r0 4 /\ getr r 8 = getr r0 8 /\
  getr r 9 = getr r0 9 /\ getr r 18 = getr r0 18 /\ getr r 19 = getr r0 19 /\ getr r 20 = getr r0 20 /\
  getr r 22 = getr r0 22 /\ getr r 23 = getr r0 23 /\ getr r 25 = getr r0 25 /\ getr r 27 = getr r0 27.
Definition rbn2_kl : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 22%bv; 23%bv; 25%bv; 27%bv].
Lemma rbn2_rk_of : forall r0 r, (forall x, In x rbn2_kl -> getr r x = getr r0 x) -> rbn2_rk r0 r.
Proof.
intros r0 r H. unfold rbn2_rk.
repeat match goal with |- _ /\ _ => split end; apply H; unfold rbn2_kl;
  repeat first [left; reflexivity | right].
Qed.
Lemma rbn2_rk_trans : forall r0 r1 r2, rbn2_rk r0 r1 -> rbn2_rk r1 r2 -> rbn2_rk r0 r2.
Proof.
intros r0 r1 r2 (A2 & A3 & A4 & A8 & A9 & A18 & A19 & A20 & A22 & A23 & A25 & A27)
  (B2 & B3 & B4 & B8 & B9 & B18 & B19 & B20 & B22 & B23 & B25 & B27).
unfold rbn2_rk. rewrite B2, B3, B4, B8, B9, B18, B19, B20, B22, B23, B25, B27.
exact (conj A2 (conj A3 (conj A4 (conj A8 (conj A9 (conj A18 (conj A19 (conj A20 (conj A22 (conj A23 (conj A25 A27))))))))))).
Qed.
Lemma rbn2_rk_pres : forall r0 r1 r2, rbn2_rk r0 r1 -> aregs_preserved r1 r2 -> rbn2_rk r0 r2.
Proof.
intros r0 r1 r2 HK HP. apply (rbn2_rk_trans r0 r1 r2 HK).
assert (RR : forall (x : bv 5) z, bv_unsigned x = z -> acallee_saved z -> getr r2 x = getr r1 x).
{ intros x z Hz Hr. pose proof (HP z Hr) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X. exact X. }
unfold rbn2_rk.
split; [exact (RR 2%bv 2 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 3%bv 3 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 4%bv 4 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 8%bv 8 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 9%bv 9 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 18%bv 18 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 19%bv 19 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 20%bv 20 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 22%bv 22 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 23%bv 23 eq_refl ltac:(unfold acallee_saved; lia))|].
split; [exact (RR 25%bv 25 eq_refl ltac:(unfold acallee_saved; lia))|].
exact (RR 27%bv 27 eq_refl ltac:(unfold acallee_saved; lia)).
Qed.
Lemma rbn2_live_regs : forall c lyc Sc m md r0 r, rbn_live B G c lyc Sc m md r0 -> rbn2_rk r0 r ->
  rbn_live B G c lyc Sc m md r.
Proof.
intros c lyc Sc m md r0 r ((HPRE & HJ & Hperm & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & Hsav & Hflag) & Hargs & Hbuf & Hslots & R22)
  (E2 & E3 & E4 & E8 & E9 & E18 & E19 & _ & E22 & E23 & _ & _).
split; [|split; [exact Hargs | split; [exact Hbuf | split; [exact Hslots | rewrite E22; exact R22]]]].
split; [exact HPRE|]. split; [exact HJ|]. split; [exact Hperm|].
rewrite E2, E3, E4, E8, E9, E18, E19, E23.
exact (conj R2 (conj R3 (conj R4 (conj R8 (conj R9 (conj R18 (conj R19 (conj R23 (conj Hsav Hflag))))))))).
Qed.

(* ---- C2. the stem as the two wrappers read it ---- *)
Definition rbn2_sf (c : rbx) (m : word -> option byte) (st : Z) : Prop :=
  Forall (fun x => 0 < x < 256) (x_stem c) /\ Z.of_nat (length (x_stem c)) < 2 ^ 31 /\
  4096 <= st /\ st + Z.of_nat (length (x_stem c)) + 8 <= alloc_ceiling /\
  amem_range st (Z.of_nat (length (x_stem c)) + 1) /\
  garr8 SEGS (x_mem_at c m) st (x_stem c ++ [0]) /\
  range_addressable (aview SEGS (w_H (x_W c)) m) SHADOW_OFF st (Z.of_nat (length (x_stem c)) + 1) /\
  (forall a n, st <= a -> a + n <= st + Z.of_nat (length (x_stem c)) + 1 -> 0 < n ->
     shadow_hull_vis (aview SEGS (w_H (x_W c)) m) a n) /\
  (forall a, st + Z.of_nat (length (x_stem c)) < a <
     st + Z.of_nat (length (x_stem c)) - (st + Z.of_nat (length (x_stem c))) mod 8 + 8 ->
     aview SEGS (w_H (x_W c)) m a <> None).
Lemma rbn2_sf_of : forall c st lyc Sc m md, rbn_stem B G c m st -> AR SEGS B lyc Sc (x_W c) m md ->
  (forall cid pos, In (cid, pos) (frames (x_S c)) ->
     In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos = frame_addr (x_ly c) cid pos) ->
  rbn2_sf c m st.
Proof.
intros c st lyc Sc m md HST HAR Hfr.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HST as [(Hsd & Hst & HC & (cid & pos & Hin & Hfa1 & Hfa2)) | (Hsd & HI)].
- assert (Es : x_stem c = x_sd c) by (unfold x_stem; destruct (x_sd c); [congruence | reflexivity]).
  unfold rbn2_sf. rewrite Es. destruct (Hfr cid pos Hin) as (Hin' & Hfa').
  destruct HC as (Hch & Hlen & Hpos & Hamr & HG & HRA & HHV & HTail).
  destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) m md cid pos HAR Hin') as (Hf0 & Hfc & _).
  rewrite Hfa' in Hf0, Hfc.
  split; [exact Hch|]. split; [exact Hlen|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range in *; lia|]. split; [exact HG|]. split; [exact HRA|].
  split; [|exact HTail].
  intros a n Ha Han Hn.
  apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc (x_W c) m md cid pos a n HAR Hin'); rewrite ?Hfa'; lia.
- destruct HI as (Hlo & Hhi & Hch & HG & (q & z & Hq & Hq1 & Hq2) & Hfix & HTail).
  split; [exact Hch|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [unfold amem_range; lia|]. split; [exact HG|].
  split; [exact (proj1 (ro_read_ok_glob SEGS B G lyc Sc (x_W c) m md q z st (Z.of_nat (length (x_stem c)) + 1) GM Hq IV HAR
             ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)))|].
  split.
  + intros a n Ha Han Hn.
    exact (proj2 (ro_read_ok_glob SEGS B G lyc Sc (x_W c) m md q z a n GM Hq IV HAR
             ltac:(lia) ltac:(lia) Hn ltac:(lia) ltac:(unfold IMG_HI; lia))).
  + intros a Ha. specialize (HTail a Ha). unfold aview, mbyte.
    destruct (mrestrict (w_H (x_W c)) m (Z_to_bv 64 a)); [discriminate|].
    destruct (seg_rom SEGS (Z_to_bv 64 a)); [discriminate | congruence].
Qed.

(* ---- C3. the strlen wrapper in the caller's journal (the shape of YCbq.v aj_bcmp_at) ---- *)
Lemma rbn2_aj_strlen_at : forall W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k (o : Z) raw,
  ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj ->
  getr regsT 10 = w64 x -> 0 < x -> 0 <= k -> k + 1 < 2 ^ 32 -> x + k + 1 <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> getr regsT 1 = raw -> YK0s.ret_ok raw ->
  first_byte SEGS W memT x (k + 1) 0 k ->
  (forall a, x <= a <= x + k -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x (k + 1) ->
  range_addressable (aview SEGS (w_H W) memT) SHADOW_OFF x (k + 1) ->
  shadow_hull_vis (aview SEGS (w_H W) memT) x (k + 1) ->
  (forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview SEGS (w_H W) memT a <> None) ->
  aro_unowned SEGS B (aview SEGS (w_H W) memT) ->
  SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___interceptor_trampoline_strlen)) memT (seg_rom SEGS)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
       ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W mem2 md2 kj /\
       aregs_preserved regsT regs2 /\ getr regs2 10 = w64 k /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
          aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memT a)).
Proof.
intros W regsT memT STK sp0 FP ly S W0 mem md own lyc Sc mdc kj x k o raw
  HJ Ha0 Hx0 Hk0 Hk1 Hxk Hsp' Hal Hneg Hbud Hgp Htp Hra Hraw Hfb Hwin Hamr Hras Hhull Hslack Hrom.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & _ & _ & _ & _ & _ & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HPRE : ecall_pre SEGS B lyc Sc W regsT memT mdc).
{ eapply ecall_pre_at with (o := o); try eassumption; try lia. rewrite Hra. exact Hraw. }
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
assert (Hlo2 : ly_stk_lo lyc + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, Hsp'; lia).
assert (Hpres2E : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W) memT a)
  by (intros a Ha; apply Hpres; rewrite Hsp' in Ha; lia).
assert (Hsrc : src_ok SEGS W regsT memT x (k + 1)).
{ intros a Ha. split; [|rewrite Hsp'; pose proof (Hwin a ltac:(lia)); lia].
  destruct Hfb as (_ & Hlt & Hat). destruct (Z.lt_ge_cases a (x + k)) as [Hl | Hg].
  - destruct (Hlt (a - x) ltac:(lia)) as (b & Hb & _). replace a with (x + (a - x)) by lia. rewrite Hb. discriminate.
  - replace a with (x + k) by lia. rewrite (Hat ltac:(lia)). discriminate. }
eapply SRr_mono.
{ exact (ASTRLEN lyc Sc W regsT memT mdc x k HPRE Hlo2 Hpres2E Ha0 Hx0 Hk0 Hk1 Hxk Hfb Hsrc
    ltac:(intros a Ha; rewrite Hsp'; exact (Hwin a Ha)) Hamr Hras Hhull Hslack Hrom). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HAR2 & HP & Hsame & Hres & Hfr & Hpres2).
rewrite Hsp' in Hfr.
split; [reflexivity|]. exists regs2, mem2, md2.
split; [unfold cfg_at, raZ; rewrite Hra; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ eapply (ajournal_after_write SEGS B LAWS pa_segs_low STK sp0 FP ly S W0 mem md own lyc Sc W memT mdc kj mem2 md2
    (fun a => sp0 + o - 2 * ESTACK <= a < sp0 + o) Sc own HJ).
  - intros a Ha Hna. apply (Hfr a Ha). exact Hna.
  - exact Hpres2.
  - exact Hsame.
  - intros a Ha; left; left; lia.
  - exact HAR2.
  - reflexivity. - reflexivity. - lia. - exact Hfrs. - exact HQT. }
split; [exact HP|]. split; [exact Hres|]. exact Hfr.
Qed.

(* ---- C4. the segment's post, and the state between its pieces ---- *)
Definition rbn2_Q (c : rbx) : world SEGS -> config -> Prop :=
  fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
    (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3b4)) mem' (seg_rom SEGS)) md' /\
     rbn_C4 B G c 0 lyc' Sc' mem' md' regs') \/
    (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3f8)) mem' (seg_rom SEGS)) md' /\
     rbn_C5 B G c lyc' Sc' mem' md' regs').
(* between two pieces: C3 at (memc, regs), the journal at m, m = memc but in the callee window, the cut-point
   registers kept *)
Definition rbn2_M (c : rbx) (st : Z) (lyc : alayout) (Sc : astate) (memc : word -> option byte) (mdc : Model)
  (regs : bvmap 5 word) (m : word -> option byte) (md : Model) (r : bvmap 5 word) : Prop :=
  rbn_C3 B G c st lyc Sc memc mdc regs /\
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m md 0 /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c - 2 * ESTACK <= a < x_s1 c) ->
     aview SEGS (w_H (x_W c)) m a = aview SEGS (w_H (x_W c)) memc a) /\
  rbn2_rk regs r.
Lemma rbn2_rk_refl : forall r, rbn2_rk r r.
Proof. intros r. unfold rbn2_rk. repeat match goal with |- _ /\ _ => split end; reflexivity. Qed.
Lemma rbn2_k_nw : forall c st lyc Sc memc mdc regs m,
  rbn_C3 B G c st lyc Sc memc mdc regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c - 2 * ESTACK <= a < x_s1 c) ->
     aview SEGS (w_H (x_W c)) m a = aview SEGS (w_H (x_W c)) memc a) ->
  rbn_k c lyc Sc memc m (fun a => x_s1 c - 2 * ESTACK <= a < x_s1 c).
Proof.
intros c st lyc Sc memc mdc regs m (HL & _) NW. pose proof HL as (HC & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (rbn_k_mono c lyc Sc memc m (fun a => (x_s1 c - 2 * ESTACK <= a < x_s1 c) \/ False));
  [| intros a [X | []]; exact X].
apply (rbn_k_of_plain c lyc Sc memc mdc memc m (x_s1 c - 2 * ESTACK) (x_s1 c) (fun _ => False) HAR); [lia | lia | | ].
- intros a Hi. pose proof (pa_img_range a Hi) as Hr. split; [lia | tauto].
- intros a Ha Hw _. exact (NW a Ha Hw).
Qed.

(* ---- C5. the two ends ---- *)
Lemma rbn2_fin_C5 : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r -> rbn_skip (x_stem c) (x_w4 c) = true ->
  rbn_C5 B G c lyc Sc m md r.
Proof.
intros c st lyc Sc memc mdc regs m md r (HC3 & HJ & NW & RK) Hsk.
pose proof (rbn2_k_nw c st lyc Sc memc mdc regs m HC3 NW) as HK.
destruct HC3 as (HL & HST & (HWB & HWG & R27) & R20 & R25 & HSCO & HNB).
pose proof HL as (HC & Hargs & _).
pose proof HC as (_ & _ & Hperm & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _ &
  _ & _ & Hf0 & Hfc & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn2_w4 c Hargs) as (Lw4 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity. unfold SHADOW_OFF in HFS.
assert (AG : forall a, 0 <= a < alloc_ceiling \/ x_s1 c <= a < x_sp0 c ->
  aview SEGS (w_H (x_W c)) m a = aview SEGS (w_H (x_W c)) memc a) by (intros a Ha; apply NW; lia).
split; [|split; [|split]].
- apply (rbn2_live_regs c lyc Sc m md regs r); [|exact RK].
  apply (rbn_live_keep c lyc Sc memc mdc regs lyc Sc m md regs _ HL HJ Hperm ltac:(intros z _; reflexivity) HK).
  intros a Ha. left. exact Ha.
- destruct RK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E27).
  split; [|split; [|rewrite E27; exact R27]].
  + apply (rbn_sb_keep c memc m _ _ _ _ _ HWB); intros x Hx; apply AG.
    * unfold x_wb in Hx. lia.
    * rewrite Lw4 in Hx. change (Z.of_nat 4) with 4 in Hx. unfold x_W4 in Hx. lia.
  + apply (rbn_garr_keep (x_W c) memc m _ _ HWG); intros x Hx; apply AG.
    rewrite length_app, Lw4 in Hx. change (Z.of_nat (4 + length [0])) with 5 in Hx. unfold x_W4 in Hx. lia.
- apply (rbn_scope_keep c memc m _ _ _ _ HSCO). intros x Hx. apply AG. lia.
- assert (EF : x_nb_full c = x_nb_stem c) by exact (rbn_nm_skip _ _ Hsk).
  unfold x_nmc. rewrite EF.
  pose proof HNB as (_ & _ & _ & _ & _ & Hlen & _).
  apply (rbn_sb_keep c memc m _ _ _ _ _ HNB); intros x Hx; apply AG; unfold x_nb, x_NM in *; lia.
Qed.
(* what the sb_ch call at 0x83114 may write besides its window: nb's n / over and the byte NM + n *)
Definition rbn2_E4 (c : rbx) (a : Z) : Prop :=
  (x_s1 c - 2 * ESTACK <= a < x_s1 c) \/
  tsb_ch_wr (x_nb c) (x_NM c) (Z.of_nat (length (fst (x_nb_stem c)))) 24 a.
(* nb after sb_ch(nb, '-') (tsb_ch_post's struct clauses) *)
Definition rbn2_chpost (c : rbx) (m : word -> option byte) : Prop :=
  val_mem SEGS (x_mem_at c m) (x_nb c) 8 (x_NM c) /\ val_mem SEGS (x_mem_at c m) (x_nb c + 8) 8 24 /\
  (if Z.of_nat (length (fst (x_nb_stem c))) + 1 <? 24
   then val_mem SEGS (x_mem_at c m) (x_nb c + 16) 8 (Z.of_nat (length (fst (x_nb_stem c))) + 1) /\
        val_mem SEGS (x_mem_at c m) (x_nb c + 24) 4 (snd (x_nb_stem c)) /\
        garr8 SEGS (x_mem_at c m) (x_NM c + Z.of_nat (length (fst (x_nb_stem c)))) [45]
   else val_mem SEGS (x_mem_at c m) (x_nb c + 16) 8 (Z.of_nat (length (fst (x_nb_stem c)))) /\
        val_mem SEGS (x_mem_at c m) (x_nb c + 24) 4 1).
Lemma rbn2_fin_C4 : forall c st lyc Sc memc mdc regs m md r,
  rbn_C3 B G c st lyc Sc memc mdc regs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m md 0 ->
  rbn_k c lyc Sc memc m (rbn2_E4 c) -> rbn2_chpost c m -> rbn2_rk regs r ->
  getr r 10 = w64 (nth 0 (x_w4 c) 0) -> getr r 21 = w64 (x_W4 c + 1) -> getr r 24 = w64 (2 ^ 64 - 1) ->
  rbn_skip (x_stem c) (x_w4 c) = false ->
  rbn_C4 B G c 0 lyc Sc m md r.
Proof.
intros c st lyc Sc memc mdc regs m md r HC3 HJ HK HP RK R10 R21 R24 Hsk.
destruct HC3 as (HL & HST & (HWB & HWG & R27) & R20 & R25 & HSCO & HNB).
pose proof HL as (HC & Hargs & _).
pose proof HC as (_ & _ & Hperm & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & Hs1m &
  _ & _ & Hf0 & Hfc & Hal64 & Hfapp & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn2_w4 c Hargs) as (Lw4 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity. unfold SHADOW_OFF in HFS.
pose proof HNB as (_ & _ & _ & _ & Hov & Hlen & Hch & HG).
set (n := Z.of_nat (length (fst (x_nb_stem c)))) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp.
(* the bytes the call may write are none of the bytes C4 keeps from C3 *)
assert (NE : forall a, (x_s1 c + 184 <= a < x_s1 c + 212 \/ x_nb c <= a < x_nb c + 16 \/
    x_F c + 32 <= a < x_F c + 40 \/ x_NM c <= a < x_NM c + n \/ x_FS c <= a < x_FS c + 64) -> ~ rbn2_E4 c a).
{ intros a Ha. unfold rbn2_E4, tsb_ch_wr, x_nb, x_NM in *. fold n.
  intros [X | [X | (X1 & X2)]]; destruct Hfapp as (Hfa0 & [Hfl | (Hfh1 & Hfh2)]); lia. }
pose proof (rbn_ag_stack c lyc Sc memc mdc regs m (rbn2_E4 c) HC HK) as AGs.
pose proof (rbn_ag_frame c lyc Sc memc mdc regs m (rbn2_E4 c) HC HK) as AGf.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- apply (rbn2_live_regs c lyc Sc m md regs r); [|exact RK].
  apply (rbn_live_keep c lyc Sc memc mdc regs lyc Sc m md regs _ HL HJ Hperm ltac:(intros z _; reflexivity) HK).
  intros a Ha. unfold rbn2_E4, tsb_ch_wr, rbn_zone, x_nb, x_NM in *. fold n in Ha.
  destruct Ha as [X | [X | (X1 & X2)]]; [left; exact X | right; left; lia | right; right; left; lia].
- destruct RK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E27).
  split; [|split; [|rewrite E27; exact R27]].
  + apply (rbn_sb_keep c memc m _ _ _ _ _ HWB); intros x Hx.
    * unfold x_wb in Hx. apply AGs; [lia | apply NE; lia].
    * rewrite Lw4 in Hx. change (Z.of_nat 4) with 4 in Hx. unfold x_W4 in Hx.
      apply AGf; [lia | apply NE; lia].
  + apply (rbn_garr_keep (x_W c) memc m _ _ HWG); intros x Hx.
    rewrite length_app, Lw4 in Hx. change (Z.of_nat (4 + length [0])) with 5 in Hx. unfold x_W4 in Hx.
    apply AGf; [lia | apply NE; lia].
- lia.
- exact (rbn_nm_noskip _ _ Hsk).
- exact R10.
- destruct RK as (_ & _ & _ & _ & _ & _ & _ & E20 & _). rewrite E20, R20, Z.add_0_r. reflexivity.
- rewrite Z.add_0_r. exact R21.
- exact R24.
- apply (rbn_scope_keep c memc m _ _ _ _ HSCO). intros x Hx. apply AGf; [lia | apply NE; lia].
- change (Z.to_nat 0) with 0%nat. rewrite firstn_O, sbm_str_nil. unfold x_nb_dash, sbm_ch. fold n.
  unfold rbn2_chpost in HP. fold n in HP.
  destruct HP as (P0 & P8 & HP).
  assert (GK : garr8 SEGS (x_mem_at c m) (x_NM c) (fst (x_nb_stem c))).
  { apply (rbn_garr_keep (x_W c) memc m _ _ HG). intros x Hx. fold n in Hx.
    unfold x_NM in *. apply AGf; [lia | apply NE; unfold x_NM; lia]. }
  destruct (n + 1 <? 24) eqn:Er; cbn [fst snd].
  + apply Z.ltb_lt in Er. destruct HP as (P16 & P24 & P45).
    split; [exact P0|]. split; [exact P8|].
    split; [rewrite length_app, Nat2Z.inj_add; exact P16|].
    split; [exact P24|]. split; [exact Hov|].
    split; [rewrite length_app, Nat2Z.inj_add; cbn [length Z.of_nat]; lia|].
    split; [apply Forall_app; split; [exact Hch | repeat constructor; lia]|].
    apply (proj2 (garr8_app SEGS _ _ _ _)). split; [exact GK | exact P45].
  + apply Z.ltb_ge in Er. destruct HP as (P16 & P24).
    split; [exact P0|]. split; [exact P8|]. split; [exact P16|]. split; [exact P24|].
    split; [right; reflexivity|]. split; [exact Hlen|]. split; [exact Hch | exact GK].
Qed.

(* ---- C6. a run that writes nothing, and the facts that cross it ---- *)
Lemma rbn2_fr_nowin : forall E rs (m1 m2 : word -> option byte), frame_of E rs m1 m2 ->
  forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true -> forall x, m2 x = m1 x.
Proof.
intros E rs m1 m2 HF Hw x. apply HF. intros (rg & Hin & Hr).
pose proof (proj1 (forallb_forall _ rs) Hw rg Hin) as X. apply Z.leb_le in X. lia.
Qed.
Lemma rbn2_av_nowin : forall E rs (W : world SEGS) m1 m2,
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  forallb (fun rg => YP09.r_whi rg <=? YP09.r_wlo rg) rs = true ->
  forall a, aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a.
Proof.
intros E rs W m1 m2 HF Hw a. unfold aview, mbyte. rewrite (rbn2_fr_nowin E rs _ _ HF Hw). reflexivity.
Qed.
Lemma rbn2_k_same : forall c lyc Sc m1 m2 m3 E, rbn_k c lyc Sc m1 m2 E ->
  (forall a, aview SEGS (w_H (x_W c)) m3 a = aview SEGS (w_H (x_W c)) m2 a) -> rbn_k c lyc Sc m1 m3 E.
Proof.
intros c lyc Sc m1 m2 m3 E (A1 & A2 & A3 & A4) K.
split; [intros a Ha He; rewrite K; exact (A1 a Ha He)|].
split; [intros b mm i Hin Hi He; rewrite K; exact (A2 b mm i Hin Hi He)|].
split; [intros a H1 H2 H3; rewrite K; exact (A3 a H1 H2 H3)|].
intros cid pos a Hin Hr He. rewrite K. exact (A4 cid pos a Hin Hr He).
Qed.
Lemma rbn2_chpost_same : forall c m m', rbn2_chpost c m ->
  (forall a, aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) -> rbn2_chpost c m'.
Proof.
intros c m m' (P0 & P8 & P) K. unfold rbn2_chpost, x_mem_at in *.
assert (KV : forall a n v, val_mem SEGS (mrestrict (w_H (x_W c)) m) a n v ->
  val_mem SEGS (mrestrict (w_H (x_W c)) m') a n v)
  by (intros a n v H; apply (rbn_val_keep (x_W c) m m' a n v H); intros x _; apply K).
split; [exact (KV _ _ _ P0)|]. split; [exact (KV _ _ _ P8)|].
destruct (Z.of_nat (length (fst (x_nb_stem c))) + 1 <? 24).
- destruct P as (P16 & P24 & P45).
  split; [exact (KV _ _ _ P16)|]. split; [exact (KV _ _ _ P24)|].
  apply (rbn_garr_keep (x_W c) m m' _ _ P45). intros x _. apply K.
- destruct P as (P16 & P24). split; [exact (KV _ _ _ P16) | exact (KV _ _ _ P24)].
Qed.
Lemma rbn2_M_same : forall c st lyc Sc memc mdc regs m md r m' md' r',
  rbn2_M c st lyc Sc memc mdc regs m md r ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m' md' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 c - 2 * ESTACK <= a < x_s1 c) ->
     aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a) -> rbn2_rk r r' ->
  rbn2_M c st lyc Sc memc mdc regs m' md' r'.
Proof.
intros c st lyc Sc memc mdc regs m md r m' md' r' (HC3 & _ & NW & RK) HJ K RK'.
split; [exact HC3|]. split; [exact HJ|]. split; [intros a Ha Hw; rewrite (K a Ha Hw); exact (NW a Ha Hw)|].
exact (rbn2_rk_trans _ _ _ RK RK').
Qed.
Local Ltac rbn2_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.

(* ---- C7. 0x83118 .. 0x83128 (+0x3a4 .. +0x3b4): w4[0] loaded, s5 = w4 + 1, s8 = -1; then C4 ---- *)
Definition rbn2_ss8 : sstate := mkSS (AF_reac_box_name + 0x3a4) sr_atoms
  [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))]] None
  (mkFacts [(20%nat, mkAF 4096 (2 ^ 47) 5); (33%nat, mkAF 48 57 0)] [] []).
Lemma rbn2_p8 : forall c st lyc Sc memc mdc regs m md r,
  rbn_C3 B G c st lyc Sc memc mdc regs ->
  ajournal SEGS B RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) m md 0 ->
  rbn_k c lyc Sc memc m (rbn2_E4 c) -> rbn2_chpost c m -> rbn2_rk regs r ->
  rbn_skip (x_stem c) (x_w4 c) = false ->
  SRr SEGS (x_W c) (mkCfg (mkst r (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3a4)) m (seg_rom SEGS)) md) (rbn2_Q c).
Proof.
intros c st lyc Sc memc mdc regs m md r HC3 HJ HK HP RK Hsk.
pose proof HC3 as (HL & _ & (_ & HWG & _) & R20 & _).
pose proof HL as (HC & Hargs & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _ &
  _ & _ & Hf0 & Hfc & Hal64 & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAF : AF_reac_box_name = 9728) by reflexivity.
destruct (rbn2_w4 c Hargs) as (Lw4 & Dw4).
assert (Hd : 48 <= nth 0 (x_w4 c) 0 <= 57).
{ destruct (x_w4 c) as [|x l]; [discriminate Lw4|]. cbn [nth]. inversion Dw4; assumption. }
assert (V0 : val_mem SEGS (mrestrict (w_H (x_W c)) m) (x_W4 c + 0) 1 (nth 0 (x_w4 c) 0)).
{ pose proof (rbn_ag_frame c lyc Sc memc mdc regs m (rbn2_E4 c) HC HK) as AGf.
  assert (GK : garr8 SEGS (mrestrict (w_H (x_W c)) m) (x_W4 c) (x_w4 c ++ [0])).
  { apply (rbn_garr_keep (x_W c) memc m _ _ HWG). intros x Hx.
    rewrite length_app, Lw4 in Hx. change (Z.of_nat (4 + length [0])) with 5 in Hx. unfold x_W4 in Hx.
    apply AGf; [lia|]. unfold rbn2_E4, tsb_ch_wr, x_nb, x_NM. intros [X | [X | (X1 & X2)]]; lia. }
  destruct (GK 0%nat ltac:(rewrite length_app, Lw4; cbn [length]; lia)) as (G0 & _).
  change (Z.of_nat 0) with 0 in G0. rewrite app_nth1 in G0 by (rewrite Lw4; lia). exact G0. }
assert (R20' : getr r 20 = Z_to_bv 64 (x_W4 c))
  by (destruct RK as (_ & _ & _ & _ & _ & _ & _ & E20 & _); rewrite E20; exact R20).
remember (Eimg (Ereg r [Z_to_bv 64 0; Z_to_bv 64 (nth 0 (x_w4 c) 0)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg r [Z_to_bv 64 0; Z_to_bv 64 (nth 0 (x_w4 c) 0)]) E)
  by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E20 : ew E 20 = getr r 20) by (rewrite HE; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 (nth 0 (x_w4 c) 0))
  by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (UW : bv_unsigned (ew E 20) = x_W4 c)
  by (rewrite E20, R20', unsigned_lit_small by (unfold x_W4; lia); reflexivity).
assert (HS : st_ok_pi SEGS VAL E rbn2_ss8
  (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x3a4))) m (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn2_ss8. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UW.
    split; [unfold x_W4; lia|]. split; [unfold x_W4; lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 0 1%N (SOff 33 0) (nth 0 (x_w4 c) 0)).
    + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact E33.
    + change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    + cbn. lia.
    + exact V0.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite UW. change (2 ^ 5) with 32. unfold x_W4.
      split; [lia|]. split; [|lia].
      pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64. rewrite Hal64, Z.add_0_r in D64.
      rewrite D64. replace (64 * (x_F c / 64) + 32) with ((2 * (x_F c / 64) + 1) * 32) by lia. apply Z_mod_mult.
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
rewrite <- Z.add_assoc.
paj_run_to_shc RUNTOP HS HJ (AF_reac_box_name + 0x3b4).
{ unfold rbn2_ss8. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pose proof (rbn2_av_nowin E (ss_mem rbn2_ss8) (x_W c) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
pose proof (regs_kept_of_st_ok_pi _ _ _ r _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
prreg HS (10%bv : bv 5) Ra0. prreg HS (21%bv : bv 5) Rs5. prreg HS (24%bv : bv 5) Rs8.
rewrite E33 in Ra0. rewrite UW in Rs5.
pmkst HS.
apply SRr_ret. unfold rbn2_Q. split; [reflexivity|].
exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
left. split.
- replace (BASE + AF_reac_box_name + 0x3b4) with (BASE + 10676) by (clear - HAF; rewrite HAF; lia). reflexivity.
- apply (rbn2_fin_C4 c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms) HC3 HJ
    (rbn2_k_same c lyc Sc memc m (ms_mem ms) _ HK KA) (rbn2_chpost_same c m (ms_mem ms) HP KA)
    (rbn2_rk_trans _ _ _ RK (rbn2_rk_of r (ms_regs ms) KR))).
  + exact Ra0.
  + exact Rs5.
  + rewrite Rs8. reflexivity.
  + exact Hsk.
Qed.

(* ---- C8. sb_ch(nb, '-') at 0x83114 (tsb_ch_spec at BASE + AF_sb_ch), then C7 ---- *)
Lemma rbn2_psbch : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r ->
  getr r 1 = Z_to_bv 64 (BASE + 10660) -> getr r 10 = Z_to_bv 64 (x_nb c) -> getr r 11 = Z_to_bv 64 45 ->
  rbn_skip (x_stem c) (x_w4 c) = false ->
  SRr SEGS (x_W c) (mkCfg (mkst r (Z_to_bv 64 (BASE + AF_sb_ch)) m (seg_rom SEGS)) md) (rbn2_Q c).
Proof.
intros c st lyc Sc memc mdc regs m md r HM R1 R10 R11 Hsk.
pose proof HM as (HC3 & HJ & NW & RK).
pose proof HC3 as (HL & _ & _ & _ & _ & HSCO & HNB).
pose proof HL as (HC & _).
pose proof HC as (_ & _ & _ & G2 & G3 & G4 & _).
destruct RK as (E2 & E3 & E4 & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & Hsp0al & Hcl & H47 & Hlo0 & Hslo & Hshi & Hshi2 & Hs1 & Hs1m &
  HinF & Hfrs & Hf0 & Hfc & Hal64 & Hfapp & _ & _ & _ & _ & _ & Efa).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
assert (HAF : AF_reac_box_name = 9728) by reflexivity.
assert (F3 : fs_frame_bytes 3 = 512) by reflexivity.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Usp : spZ r = x_s1 c) by (unfold spZ; rewrite E2, G2; unfold w64; apply unsigned_lit_small; lia).
destruct HNB as (V0 & V8 & V16 & V24 & Hov & Hlen & _ & _).
set (n := Z.of_nat (length (fst (x_nb_stem c)))) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
assert (KV : forall a k v, x_s1 c <= a -> a + Z.of_nat k <= x_sp0 c ->
  val_mem SEGS (mrestrict (w_H (x_W c)) memc) a k v -> val_mem SEGS (mrestrict (w_H (x_W c)) m) a k v).
{ intros a k v Ha1 Ha2 HV. apply (rbn_val_keep (x_W c) memc m a k v HV). intros x Hx. apply NW; lia. }
pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64. rewrite Hal64, Z.add_0_r in D64.
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
assert (HF8 : x_F c mod 8 = 0) by lia.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity. unfold SHADOW_OFF in HFS.
assert (H8m : forall j, 8 <= j < 11 -> aview SEGS (w_H (x_W c)) m (x_FS c + j) = Some 0).
{ intros j Hj. destruct HSCO as (_ & H8 & _). rewrite <- (H8 j Hj). apply NW; lia. }
change (mkCfg (mkst r (Z_to_bv 64 (BASE + AF_sb_ch)) m (seg_rom SEGS)) md) with (cfg_at SEGS A_sb_ch r m md).
eapply SRr_bind.
{ apply (HSC RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] lyc Sc (x_W c) m md 0 r
    (x_nb c) 45 (x_NM c) 24 n (snd (x_nb_stem c)) HJ).
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
  - rewrite E3. exact G3.
  - rewrite E4. exact G4.
  - rewrite Usp. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as Ds. rewrite Hs1m, Z.add_0_r in Ds.
    rewrite Ds. replace (32 * (x_s1 c / 32)) with ((2 * (x_s1 c / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite Usp. unfold SB_CH_STK. lia.
  - rewrite Usp. lia.
  - exact R10.
  - exact R11.
  - lia.
  - unfold x_nb. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as Ds. rewrite Hs1m, Z.add_0_r in Ds.
    rewrite Ds. replace (32 * (x_s1 c / 32) + 152) with ((4 * (x_s1 c / 32) + 19) * 8) by lia. apply Z_mod_mult.
  - unfold x_nb. lia.
  - unfold x_nb. lia.
  - left. rewrite Usp. unfold x_nb. lia.
  - unfold tsb_ch_rec_at. right. unfold x_nb. lia.
  - apply KV; [unfold x_nb; lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold x_nb; lia | exact V0].
  - apply KV; [unfold x_nb; lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold x_nb; lia | exact V8].
  - apply KV; [unfold x_nb; lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold x_nb; lia | exact V16].
  - apply KV; [unfold x_nb; lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold x_nb; lia | exact V24].
  - unfold x_NM. lia.
  - lia.
  - exact Hn0.
  - lia.
  - destruct Hov as [-> | ->]; lia.
  - apply (rbn2_stk_ra lyc Sc (x_W c) m md (x_nb c) 28 HAR); unfold x_nb; lia.
  - intros a Ha. split; [left; unfold x_nb in Ha; lia|].
    split; [apply Hpres; unfold x_nb in Ha; lia|].
    split; [apply (al_stack _ _ LAWS lyc Sc (x_W c) m md a HAR); unfold x_nb in Ha; lia|].
    rewrite Usp. unfold x_nb in Ha. lia.
  - intros Hroom.
    destruct (al_frames _ _ LAWS lyc Sc (x_W c) m md 3 (x_fpos c) HAR HinF) as (_ & _ & Hfb & _).
    assert (EF : frame_addr lyc 3 (x_fpos c) = x_F c) by (rewrite Efa; reflexivity).
    rewrite EF, F3 in Hfb.
    split; [unfold x_NM; lia|]. split; [unfold x_NM; lia|].
    split.
    { intros a Ha. right. exists 3, (x_fpos c). split; [exact HinF|].
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite EF, F3. unfold x_NM in Ha. lia. }
    split.
    { intros x Hx. exists 0. split; [|left; reflexivity].
      assert (Hxe : x = x_NM c + n) by lia. subst x.
      assert (Ediv : (x_F c + 64 + n) / 8 = x_F c / 8 + 8 + n / 8).
      { replace (x_F c + 64 + n) with ((x_F c / 8 + 8) * 8 + n) by lia. rewrite Z.div_add_l by lia. lia. }
      pose proof (Z.div_pos n 8 Hn0 ltac:(lia)) as Hq0.
      assert (Hq3 : n / 8 < 3) by (apply Z.div_lt_upper_bound; lia).
      unfold shadow_of_addr, x_NM. rewrite Ediv.
      replace (SHADOW_OFF + (x_F c / 8 + 8 + n / 8)) with (x_FS c + (8 + n / 8)) by (unfold SHADOW_OFF; lia).
      apply H8m. lia. }
    split.
    { intros a Ha. unfold x_NM in Ha. destruct (Hfb a ltac:(lia)) as (Hp & Ho).
      split; [|split; [exact Hp | split; [exact Ho | rewrite Usp; lia]]].
      right. right. right. exists 3, (x_fpos c). split; [left; reflexivity|].
      left. unfold in_zr. cbn [fst snd]. rewrite EF, F3. lia. }
    split; [left; unfold x_NM, x_nb; lia|].
    left. rewrite Usp. unfold SB_CH_STK, x_NM. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & P0 & P8 & Pif).
rewrite R1.
replace (BASE + 10660) with (BASE + AF_reac_box_name + 0x3a4) by (clear - HAF; rewrite HAF; lia).
replace (0 + EV_SB_CH) with 0 in HJ2 by reflexivity.
apply (rbn2_p8 c st lyc Sc memc mdc regs mem2 md2 regs2 HC3 HJ2).
- pose proof (rbn_k_of_tcj c SB_CH_STK lyc Sc m mem2 (spZ r) _ HK2) as HK2'.
  pose proof (rbn_k_trans c lyc Sc memc m mem2 _ _ (rbn2_k_nw c st lyc Sc memc mdc regs m HC3 NW) HK2') as HKt.
  apply (rbn_k_mono c lyc Sc memc mem2 _ _ HKt).
  intros a [X | [X | X]]; unfold rbn2_E4;
    [left; exact X | left; rewrite Usp in X; unfold SB_CH_STK in X; clear - X Hes; lia | right; exact X].
- unfold rbn2_chpost, x_mem_at. exact (conj P0 (conj P8 Pif)).
- exact (rbn2_rk_pres _ _ _ (proj2 (proj2 (proj2 HM))) HP2).
- exact Hsk.
Qed.

(* ---- C9. 0x83108 (+0x394): the bcmp result; 0 -> C5 at +0x3f8, else sb_ch(nb, '-') ---- *)
Definition rbn2_ss7z : sstate :=
  mkSS (AF_reac_box_name + 0x394) (sr_set sr_atoms 10%bv (SLit 0)) [] None (mkFacts [] [] []).
Definition rbn2_ss7n : sstate :=
  mkSS (AF_reac_box_name + 0x394) sr_atoms [] None (mkFacts [(10%nat, mkAF 1 (2 ^ 64 - 1) 0)] [] []).
Lemma rbn2_p7 : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r ->
  (getr r 10 = Z_to_bv 64 0 <-> rbn_skip (x_stem c) (x_w4 c) = true) ->
  SRr SEGS (x_W c) (mkCfg (mkst r (Z_to_bv 64 (BASE + AF_reac_box_name + 0x394)) m (seg_rom SEGS)) md) (rbn2_Q c).
Proof.
intros c st lyc Sc memc mdc regs m md r HM Hv.
pose proof HM as (HC3 & HJ & NW & RK).
assert (HAF : AF_reac_box_name = 9728) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
remember (Eimg (Ereg r [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg r []) E)
  by (rewrite HE; split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E 9 = getr r 9) by (rewrite HE; apply ew_Eimg_Ereg_nat; reflexivity).
assert (E10 : ew E 10 = getr r 10) by (rewrite HE; apply ew_Eimg_Ereg_nat; reflexivity).
rewrite <- Z.add_assoc.
destruct (rbn_skip (x_stem c) (x_w4 c)) eqn:Hsk.
- (* a0 = 0: on to C5 *)
  assert (R10 : getr r 10 = Z_to_bv 64 0) by (apply Hv; reflexivity).
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS (AF_reac_box_name + 0x394) sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x394))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. split; [exact I | split; exact I]. }
  assert (HS : st_ok_pi SEGS VAL E rbn2_ss7z
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x394))) m (seg_rom SEGS))))
    by exact (st_ok_pi_pin_reg' E _ _ 10%bv 0 HS0 R10 eq_refl).
  clear HS0.
  paj_run_to_shc RUNTOP HS HJ (AF_reac_box_name + 0x3f8).
  { unfold rbn2_ss7z. cbn [ss_mem]. apply awr_ok_nil. }
  pose proof (rbn2_av_nowin E (ss_mem rbn2_ss7z) (x_W c) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (regs_kept_of_st_ok_pi _ _ _ r _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply SRr_ret. unfold rbn2_Q. split; [reflexivity|].
  exists lyc, Sc, (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md) mat md).
  right. split.
  + replace (BASE + AF_reac_box_name + 0x3f8) with (BASE + 10744) by (clear - HAF; rewrite HAF; lia). reflexivity.
  + apply (rbn2_fin_C5 c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms)); [|exact Hsk].
    apply (rbn2_M_same c st lyc Sc memc mdc regs m md r (ms_mem ms) _ (ms_regs ms) HM HJ);
      [intros a _ _; exact (KA a) | exact (rbn2_rk_of r (ms_regs ms) KR)].
- (* a0 <> 0: sb_ch(nb, '-') *)
  assert (Hnz : 1 <= bv_unsigned (getr r 10)).
  { pose proof (bv_unsigned_in_range 64 (getr r 10)) as Rr.
    destruct (Z.eq_dec (bv_unsigned (getr r 10)) 0) as [H0 | H0]; [|lia].
    exfalso. assert (X : getr r 10 = Z_to_bv 64 0) by (apply bv_eq; rewrite H0; reflexivity).
    pose proof (proj1 Hv X) as Y. congruence. }
  assert (HS : st_ok_pi SEGS VAL E rbn2_ss7n
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x394))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold rbn2_ss7n. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10.
      pose proof (bv_unsigned_in_range 64 (getr r 10)) as Rr. change (bv_modulus 64) with (2 ^ 64) in Rr.
      rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity | lia]. }
  paj_run_shc RUNP RUNC HS HJ.
  { unfold rbn2_ss7n. cbn [ss_mem]. apply awr_ok_nil. }
  pose proof (rbn2_av_nowin E (ss_mem rbn2_ss7n) (x_W c) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ r _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
  pmkst HS.
  rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl).
  pose proof HC3 as (HL & _). pose proof HL as (HC & _). pose proof HC as (_ & _ & _ & _ & _ & _ & _ & G9 & _).
  destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _).
  pose proof asan_consts as (C1 & _). assert (Hes : ESTACK = 4096) by reflexivity.
  assert (R9 : getr r 9 = Z_to_bv 64 (x_s1 c))
    by (destruct RK as (_ & _ & _ & _ & E9r & _); rewrite E9r; exact G9).
  apply (rbn2_psbch c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms)).
  + apply (rbn2_M_same c st lyc Sc memc mdc regs m md r (ms_mem ms) _ (ms_regs ms) HM HJ);
      [intros a _ _; exact (KA a) | exact (rbn2_rk_of r (ms_regs ms) KR)].
  + exact Rra.
  + rewrite Ra0, E9, R9, unsigned_lit_small by (clear - Hs1 Hcl H47 C1 Hes; lia). reflexivity.
  + exact Ra1.
  + exact Hsk.
Qed.

(* ---- C10. what the suffix test reads, at a state between pieces ---- *)
Lemma rbn2_lxor_ones : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof.
intros x Hx. change 18446744073709551615 with (Z.ones 64).
pose proof (Z.add_lnot_diag x).
assert (E : Z.lxor x (Z.ones 64) = (Z.lnot x) mod 2 ^ 64).
{ rewrite <- Z.land_ones by lia. apply Z.bits_inj'. intros i Hi.
  rewrite Z.lxor_spec, Z.land_spec, Z.lnot_spec by lia.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. rewrite xorb_true_r, andb_true_r. reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite xorb_false_r, andb_false_r.
    destruct (Z.eq_dec x 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia|lia]. }
rewrite E. unfold Z.ones. rewrite Z.shiftl_1_l. change (Z.pred (2 ^ 64)) with (2 ^ 64 - 1).
replace (Z.lnot x) with (- x - 1) by lia.
rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma rbn2_den_add : forall E k s, ew E 10 = Z_to_bv 64 k -> ew E 25 = Z_to_bv 64 s -> 4 <= k -> 0 <= s ->
  s + k < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff 10 (-4)) (SOff 25 0)) = Z_to_bv 64 (s + k - 4).
Proof.
intros E k s H10 H25 Hk Hs Hsk. rewrite denot_lit_U. f_equal.
rewrite U_SAlu, (U_atom E 25 s H25) by lia. rewrite U_SOff, H10, unsigned_lit_small by lia.
cbn [zalu_raw]. unfold zcanon, M64. rewrite (Z.mod_small (k + -4) (2 ^ 64)) by lia.
rewrite Z.mod_small by lia. lia.
Qed.
Lemma rbn2_garr_some : forall (W : world SEGS) m q l, garr8 SEGS (mrestrict (w_H W) m) q l ->
  forall a, q <= a < q + Z.of_nat (length l) -> aview SEGS (w_H W) m a <> None.
Proof.
intros W m q l HG a Ha. replace a with (q + Z.of_nat (Z.to_nat (a - q))) by lia.
rewrite (rbn2_av_garr W m q l _ HG) by lia. discriminate.
Qed.
Lemma rbn2_M_sf : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r -> rbn2_sf c m st.
Proof.
intros c st lyc Sc memc mdc regs m md r (HC3 & HJ & NW & _).
pose proof HC3 as (HL & HST & _). pose proof HL as (HC & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (HAR0 & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _ &
  _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & _ & Efa).
pose proof HJ as (HAR & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfr : forall cid pos, In (cid, pos) (frames (x_S c)) ->
  In (cid, pos) (frames Sc) /\ frame_addr lyc cid pos = frame_addr (x_ly c) cid pos)
  by (intros cid pos Hin; split; [rewrite Hfrs; right; exact Hin | apply Efa]).
apply (rbn2_sf_of c st lyc Sc m md); [|exact HAR | exact Hfr].
apply (rbn_stem_keep c lyc Sc m md memc st HST HAR Hfr).
- intros a Hi _ _. pose proof (pa_img_range a Hi). apply NW; lia.
- intros cid pos a Hin Hr. destruct (Hfr cid pos Hin) as (HinC & Hfa).
  assert (Hr' : in_zr a (frame_rng lyc (cid, pos)) \/
                in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8))
    by (unfold frame_rng in *; cbn [fst snd] in *; rewrite Hfa; exact Hr).
  destruct (frame_zone SEGS B LAWS lyc Sc (x_W c) memc mdc cid pos a HAR0 HinC Hr') as (Hza & Hz).
  destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) memc mdc cid pos HAR0 HinC) as (Hf0 & _).
  apply NW; [destruct Hz as [(Hz1 & _) | Hz2]; lia | lia].
Qed.
Lemma rbn2_M_w4 : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r ->
  garr8 SEGS (x_mem_at c m) (x_W4 c) (x_w4 c ++ [0]) /\ rbn_scope c m 5 0 0xf8 0xf8.
Proof.
intros c st lyc Sc memc mdc regs m md r (HC3 & _ & NW & _).
destruct HC3 as (HL & _ & (_ & HWG & _) & _ & _ & HSCO & _).
pose proof HL as (HC & Hargs & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _ &
  _ & _ & Hf0 & Hfc & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn2_w4 c Hargs) as (Lw4 & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity. unfold SHADOW_OFF in HFS.
split.
- apply (rbn_garr_keep (x_W c) memc m _ _ HWG). intros x Hx.
  rewrite length_app, Lw4 in Hx. change (Z.of_nat (4 + length [0])) with 5 in Hx. unfold x_W4 in Hx. apply NW; lia.
- apply (rbn_scope_keep c memc m _ _ _ _ HSCO). intros x Hx. apply NW; lia.
Qed.
(* bcmp's answer is the suffix test of rbn_skip (reac_box_name_sbm.v rbn_suffix_Z) *)
Lemma rbn2_cmp_iff : forall c m st, rbn2_sf c m st ->
  garr8 SEGS (x_mem_at c m) (x_W4 c) (x_w4 c ++ [0]) -> length (x_w4 c) = 4%nat ->
  4 <= Z.of_nat (length (x_stem c)) ->
  ((forall i, 0 <= i < 4 -> aview SEGS (w_H (x_W c)) m (st + Z.of_nat (length (x_stem c)) - 4 + i) =
                             aview SEGS (w_H (x_W c)) m (x_W4 c + i)) <->
   rbn_skip (x_stem c) (x_w4 c) = true).
Proof.
intros c m st (_ & _ & _ & _ & _ & HG & _) HW Lw Hk.
unfold rbn_skip. rewrite (proj2 (Z.leb_le 4 _) Hk), andb_true_l.
rewrite (rbn_suffix_Z (x_stem c) (x_w4 c) Lw Hk).
set (k := Z.of_nat (length (x_stem c))) in *.
assert (A1 : forall j, 0 <= j < 4 ->
  aview SEGS (w_H (x_W c)) m (st + k - 4 + j) = Some (nth (Z.to_nat (k - 4 + j)) (x_stem c) 0)).
{ intros j Hj.
  pose proof (rbn2_av_garr (x_W c) m st (x_stem c ++ [0]) (Z.to_nat (k - 4 + j)) HG
    ltac:(rewrite length_app; cbn [length]; unfold k in *; lia)) as X.
  rewrite Z2Nat.id in X by lia. rewrite app_nth1 in X by (unfold k in *; lia).
  replace (st + k - 4 + j) with (st + (k - 4 + j)) by lia. exact X. }
assert (A2 : forall j, 0 <= j < 4 ->
  aview SEGS (w_H (x_W c)) m (x_W4 c + j) = Some (nth (Z.to_nat j) (x_w4 c) 0)).
{ intros j Hj.
  pose proof (rbn2_av_garr (x_W c) m (x_W4 c) (x_w4 c ++ [0]) (Z.to_nat j) HW
    ltac:(rewrite length_app, Lw; cbn [length]; lia)) as X.
  rewrite Z2Nat.id in X by lia. rewrite app_nth1 in X by (rewrite Lw; lia). exact X. }
split; intros H j Hj.
- specialize (H j Hj). rewrite (A1 j Hj), (A2 j Hj) in H. congruence.
- rewrite (A1 j Hj), (A2 j Hj). f_equal. exact (H j Hj).
Qed.

(* ---- C11. 0x830e0 (+0x36c), back from strlen with a0 = k: k < 4 -> sb_ch(nb, '-'); else the two dead
   UBSan traps (decided by c6a / c6b) and bcmp(stem + k - 4, w4, 4) ---- *)
Definition rbn2_ss6s : sstate := mkSS (AF_reac_box_name + 0x36c) (sr_set sr_atoms 21%bv (SLit 4)) [] None
  (mkFacts [(10%nat, mkAF 0 3 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0)] [] []).
Definition rbn2_c6a : acond := mkAC BC_GEU (SAlu ALU_XOR (SOff 25 0) (SLit (-1))) (SOff 10 0).
Definition rbn2_c6b : acond := mkAC BC_GEU (SAlu ALU_ADD (SOff 25 0) (SOff 10 0)) (SLit 5).
Definition rbn2_ss6l : sstate := mkSS (AF_reac_box_name + 0x36c) (sr_set sr_atoms 21%bv (SLit 4)) [] None
  (mkFacts [(10%nat, mkAF 4 (2 ^ 31) 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF 4096 (2 ^ 47) 5)]
     [rbn2_c6a; rbn2_c6b] []).
Lemma rbn2_p6 : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r ->
  getr r 10 = Z_to_bv 64 (Z.of_nat (length (x_stem c))) -> getr r 21 = Z_to_bv 64 4 ->
  SRr SEGS (x_W c) (mkCfg (mkst r (Z_to_bv 64 (BASE + AF_reac_box_name + 0x36c)) m (seg_rom SEGS)) md) (rbn2_Q c).
Proof.
intros c st lyc Sc memc mdc regs m md r HM R10 R21.
pose proof HM as (HC3 & HJ & NW & RK).
pose proof (rbn2_M_sf c st lyc Sc memc mdc regs m md r HM) as SF.
pose proof SF as (_ & Hk31 & Hst0 & Hstc & Hamr & _).
pose proof HC3 as (HL & _ & _ & R20 & R25 & _).
pose proof HL as (HC & Hargs & _).
pose proof HC as (_ & _ & _ & G2 & G3 & G4 & _ & G9 & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & Hsp0al & Hcl & H47 & _ & _ & _ & _ & Hs1 & Hs1m &
  HinF & _ & Hf0 & Hfc & Hal64 & Hfapp & _ & _ & _ & _ & _ & Efa).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAF : AF_reac_box_name = 9728) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rbn2_w4 c Hargs) as (Lw4 & _).
pose proof RK as (E2r & E3r & E4r & _ & E9r & _ & _ & E20r & _ & _ & E25r & _).
set (k := Z.of_nat (length (x_stem c))) in *.
assert (Hk0 : 0 <= k) by (unfold k; lia).
remember (Eimg (Ereg r [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg r []) E)
  by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c))
  by (rewrite HE, (ew_Eimg_Ereg_nat r [] 9 9%bv eq_refl), E9r; exact G9).
assert (E10 : ew E 10 = Z_to_bv 64 k) by (rewrite HE, (ew_Eimg_Ereg_nat r [] 10 10%bv eq_refl); exact R10).
assert (E20 : ew E 20 = Z_to_bv 64 (x_W4 c))
  by (rewrite HE, (ew_Eimg_Ereg_nat r [] 20 20%bv eq_refl), E20r; exact R20).
assert (E25 : ew E 25 = Z_to_bv 64 st)
  by (rewrite HE, (ew_Eimg_Ereg_nat r [] 25 25%bv eq_refl), E25r; exact R25).
rewrite <- Z.add_assoc.
destruct (Z_lt_le_dec k 4) as [Hshort | Hlong].
- (* k < 4: the name gets '-' and w4 *)
  assert (Hsk : rbn_skip (x_stem c) (x_w4 c) = false)
    by (unfold rbn_skip; fold k; replace (4 <=? k) with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS (AF_reac_box_name + 0x36c) sr_atoms [] None
      (mkFacts [(10%nat, mkAF 0 3 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0)] [] []))
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x36c))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; exact I]. split; [|split; [|exact I]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia.
        rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
        rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
  assert (HS : st_ok_pi SEGS VAL E rbn2_ss6s
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x36c))) m (seg_rom SEGS))))
    by exact (st_ok_pi_pin_reg' E _ _ 21%bv 4 HS0 R21 eq_refl).
  clear HS0.
  paj_run_shc RUNP RUNC HS HJ.
  { unfold rbn2_ss6s. cbn [ss_mem]. apply awr_ok_nil. }
  pose proof (rbn2_av_nowin E (ss_mem rbn2_ss6s) (x_W c) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ r _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1.
  pmkst HS.
  rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl).
  apply (rbn2_psbch c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms)).
  + apply (rbn2_M_same c st lyc Sc memc mdc regs m md r (ms_mem ms) _ (ms_regs ms) HM HJ);
      [intros a _ _; exact (KA a) | exact (rbn2_rk_of r (ms_regs ms) KR)].
  + exact Rra.
  + rewrite Ra0, E9, unsigned_lit_small by (clear - Hs1 Hcl H47 C1 Hes; lia). reflexivity.
  + exact Ra1.
  + exact Hsk.
- (* 4 <= k: bcmp(stem + k - 4, w4, 4) *)
  assert (CA : acond_ok E rbn2_c6a).
  { unfold acond_ok, rbn2_c6a. cbn [ac_c ac_a ac_b].
    rewrite branch_geu_U, U_SAlu, U_SLit, (U_atom E 25 st E25), (U_atom E 10 k E10) by lia.
    cbn [zalu_raw]. change (zcanon (-1)) with 18446744073709551615. rewrite rbn2_lxor_ones by lia.
    unfold zcanon, M64. rewrite Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia. }
  assert (CB : acond_ok E rbn2_c6b).
  { unfold acond_ok, rbn2_c6b. cbn [ac_c ac_a ac_b].
    rewrite branch_geu_U, U_SAlu, U_SLit, (U_atom E 25 st E25), (U_atom E 10 k E10) by lia.
    cbn [zalu_raw]. unfold zcanon, M64. rewrite !Z.mod_small by lia. apply negb_true_iff, Z.ltb_ge. lia. }
  assert (HS0 : st_ok_pi SEGS VAL E (mkSS (AF_reac_box_name + 0x36c) sr_atoms [] None
      (mkFacts [(10%nat, mkAF 4 (2 ^ 31) 0); (25%nat, mkAF 4096 (2 ^ 47 - 1) 0); (20%nat, mkAF 4096 (2 ^ 47) 5)]
         [rbn2_c6a; rbn2_c6b] []))
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x36c))) m (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint]. exact I.
    - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      split; [|split; [split; [exact CA | split; [exact CB | exact I]] | exact I]].
      split; [|split; [|split; [|exact I]]].
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10, unsigned_lit_small by lia.
        rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E25, unsigned_lit_small by lia.
        rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
      + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E20, unsigned_lit_small by (unfold x_W4; lia).
        change (2 ^ 5) with 32. unfold x_W4. split; [lia|]. split; [|lia].
        pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64. rewrite Hal64, Z.add_0_r in D64.
        rewrite D64. replace (64 * (x_F c / 64) + 32) with ((2 * (x_F c / 64) + 1) * 32) by lia. apply Z_mod_mult. }
  assert (HS : st_ok_pi SEGS VAL E rbn2_ss6l
    (restrict (w_H (x_W c)) (mkst r (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x36c))) m (seg_rom SEGS))))
    by exact (st_ok_pi_pin_reg' E _ _ 21%bv 4 HS0 R21 eq_refl).
  clear HS0.
  (* the arithmetic the bcmp contract asks, while the context is small *)
  pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as R8.
  pose proof (Z.div_mod (x_F c) 64 ltac:(lia)) as D64. rewrite Hal64, Z.add_0_r in D64.
  assert (HF8 : x_F c mod 8 = 0) by lia.
  assert (HFS : x_FS c = SHADOW_OFF + x_F c / 8) by reflexivity.
  assert (E32 : SHADOW_OFF + (x_F c + 32) / 8 = x_FS c + 4).
  { rewrite HFS. replace (x_F c + 32) with ((x_F c / 8 + 4) * 8) by lia. rewrite Z.div_mul by lia. lia. }
  assert (Hom : (x_s1 c - x_sp0 c) mod 16 = 0).
  { pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as Ds. rewrite Hs1m, Z.add_0_r in Ds.
    pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as Dp. rewrite Hsp0al, Z.add_0_r in Dp.
    replace (x_s1 c - x_sp0 c) with ((2 * (x_s1 c / 32) - x_sp0 c / 16) * 16) by lia. apply Z_mod_mult. }
  assert (Ar : forall a, (st + k - 4 <= a < st + k - 4 + 4 \/ x_W4 c <= a < x_W4 c + 4) ->
    ~ (x_sp0 c + (x_s1 c - x_sp0 c) - 2 * ESTACK <= a < x_sp0 c + (x_s1 c - x_sp0 c)) /\
    ~ (x_s1 c - ESTACK <= a < x_s1 c)) by (intros a Ha; unfold x_W4 in Ha; lia).
  assert (Amx : amem_range (st + k - 4) 4) by (unfold amem_range in *; lia).
  assert (Amy : amem_range (x_W4 c) 4).
  { unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hfapp. unfold amem_range, x_W4.
    rewrite C3, C4, C5. lia. }
  assert (A1 : 0 <= st + k - 4 /\ st + k - 4 + 4 <= 2 ^ 63 /\ 0 <= x_W4 c /\ x_W4 c + 4 <= 2 ^ 63 /\
    x_s1 c - x_sp0 c <= 0 /\ 2 * ESTACK - (x_s1 c - x_sp0 c) <= RBN_STK /\ 0 <= st /\ st + k < 2 ^ 64 /\
    0 <= x_s1 c < 2 ^ 64 /\ x_sp0 c + (x_s1 c - x_sp0 c) = x_s1 c) by (unfold x_W4; lia).
  destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  assert (Hra : YK0s.ret_ok (Z_to_bv 64 (BASE + 10644))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
  paj_run_shc RUNP RUNC HS HJ.
  { unfold rbn2_ss6l. cbn [ss_mem]. apply awr_ok_nil. }
  pose proof (rbn2_av_nowin E (ss_mem rbn2_ss6l) (x_W c) m (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
  pose proof (regs_kept_of_st_ok SEGS _ _ _ r _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  pose proof (rbn2_rk_of r (ms_regs ms) KR) as RK1.
  rbn2_rreg HS (10%bv : bv 5) Ra0. prreg HS (1%bv : bv 5) Rra. prreg HS (11%bv : bv 5) Ra1.
  prreg HS (12%bv : bv 5) Ra2.
  rewrite (rbn2_den_add E k st E10 E25 Hlong A7 A8) in Ra0. rewrite E20 in Ra1.
  pmkst HS.
  pose proof (rbn2_M_same c st lyc Sc memc mdc regs m md r (ms_mem ms) _ (ms_regs ms) HM HJ
    (fun a _ _ => KA a) RK1) as HM1.
  pose proof (rbn2_M_sf c st lyc Sc memc mdc regs _ _ _ HM1) as SF1.
  pose proof (rbn2_M_w4 c st lyc Sc memc mdc regs _ _ _ HM1) as (W4G & (H4 & _)).
  pose proof SF1 as (_ & _ & _ & _ & _ & SG & SRA & SHV & _).
  fold k in SG, SRA, SHV.
  pose proof (rbn2_rk_trans _ _ _ RK RK1) as (K2 & K3 & K4 & _).
  assert (Usp : spZ (ms_regs ms) = x_sp0 c + (x_s1 c - x_sp0 c))
    by (unfold spZ; rewrite K2, G2, A10; unfold w64; apply unsigned_lit_small; exact A9).
  eapply SRr_bind.
  { apply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA IB___interceptor_trampoline_bcmp) ABCMP (x_W c)
      (ms_regs ms) (ms_mem ms) RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
      [(3, x_fpos c)] lyc Sc _ 0 (st + k - 4) (x_W4 c) 4 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + 10644)) HJ).
    - exact Ra0.
    - exact Ra1.
    - exact Ra2.
    - clear; lia.
    - exact A1.
    - exact A2.
    - exact A3.
    - exact A4.
    - exact Usp.
    - exact Hom.
    - exact A5.
    - exact A6.
    - rewrite K3. exact G3.
    - rewrite K4. exact G4.
    - exact Rra.
    - exact Hra.
    - intros a Ha. split; [|rewrite Usp, A10; exact (proj2 (Ar a (or_introl Ha)))].
      apply (rbn2_garr_some (x_W c) (ms_mem ms) st _ SG). rewrite length_app. cbn [length].
      fold k. clear - Ha Hlong Hk0. lia.
    - intros a Ha. split; [|rewrite Usp, A10; exact (proj2 (Ar a (or_intror Ha)))].
      apply (rbn2_garr_some (x_W c) (ms_mem ms) (x_W4 c) _ W4G). rewrite length_app, Lw4. cbn [length].
      clear - Ha. lia.
    - intros a Ha. exact (proj1 (Ar a (or_introl Ha))).
    - intros a Ha. exact (proj1 (Ar a (or_intror Ha))).
    - exact Amx.
    - exact Amy.
    - apply (range_addressable_sub _ SHADOW_OFF st (k + 1) _ _ SRA); clear - Hlong Hk0; lia.
    - intros _. apply SHV; clear - Hlong Hk0; lia.
    - apply (range_addressable_sub _ SHADOW_OFF (x_W4 c) 5 _ _); [| clear; lia | clear; lia].
      apply range_addressable_partial;
        [| unfold x_W4; clear - HF8 D8 R8; rewrite Z.add_mod, HF8 by lia; reflexivity | clear; lia].
      unfold shadow_of_addr, x_W4. rewrite E32. exact H4.
    - intros _. pose proof HM1 as (_ & HJ1 & _). pose proof HJ1 as (HAR1 & _).
      assert (EF : frame_addr lyc 3 (x_fpos c) = x_F c) by (rewrite Efa; reflexivity).
      apply (shadow_hull_vis_of_frame SEGS B LAWS lyc Sc (x_W c) (ms_mem ms) _ 3 (x_fpos c) (x_W4 c) 4 HAR1 HinF);
        rewrite ?EF; try change (fs_frame_bytes 3) with 512; unfold x_W4; clear - Hf0; lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr & _).
  replace (BASE + 10644) with (BASE + AF_reac_box_name + 0x394) by (clear - HAF; rewrite HAF; lia).
  apply (rbn2_p7 c st lyc Sc memc mdc regs mem2 md2 regs2).
  + apply (rbn2_M_same c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms) mem2 md2 regs2 HM1 HJ2).
    * intros a Ha Hw. apply Hfr; [exact Ha | rewrite A10; exact Hw].
    * exact (rbn2_rk_pres _ _ _ (rbn2_rk_refl _) HP2).
  + rewrite Hv.
    pose proof (rbn2_cmp_iff c (ms_mem ms) st SF1 W4G Lw4 Hlong) as CI. fold k in CI.
    split; intros H0.
    * apply (proj1 CI). apply (proj1 Hcmp). exact H0.
    * apply (proj2 Hcmp). apply (proj2 CI). exact H0.
Qed.

(* ---- C12. what the strlen call reads ---- *)
Lemma rbn2_fb : forall c m st, rbn2_sf c m st ->
  first_byte SEGS (x_W c) m st (Z.of_nat (length (x_stem c)) + 1) 0 (Z.of_nat (length (x_stem c))).
Proof.
intros c m st (Hch & _ & _ & _ & _ & HG & _).
split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) (x_stem c) 0). split.
  + pose proof (rbn2_av_garr (x_W c) m st (x_stem c ++ [0]) (Z.to_nat i) HG
      ltac:(rewrite length_app; cbn [length]; lia)) as X.
    rewrite Z2Nat.id in X by lia. rewrite app_nth1 in X by lia. exact X.
  + assert (Hin : In (nth (Z.to_nat i) (x_stem c) 0) (x_stem c)) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Hch _ Hin) as Y. cbv beta in Y. lia.
- intros _. pose proof (rbn2_av_garr (x_W c) m st (x_stem c ++ [0]) (length (x_stem c)) HG
    ltac:(rewrite length_app; cbn [length]; lia)) as X.
  rewrite app_nth2 in X by lia. rewrite Nat.sub_diag in X. exact X.
Qed.
(* the read-only bytes strlen may read: arodata_okP of the entry, kept by the journal (no FP range holds 0:
   reac_box_name_inv.v rbn_fp_closed) and by the steps since C3 *)
Lemma rbn2_aro : forall c st lyc Sc memc mdc regs m md r,
  rbn2_M c st lyc Sc memc mdc regs m md r -> aro_unowned SEGS B (aview SEGS (w_H (x_W c)) m).
Proof.
intros c st lyc Sc memc mdc regs m md r (HC3 & _ & NW & _).
pose proof HC3 as (HL & _). pose proof HL as (HC & _). pose proof HC as (HPRE & HJ0 & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & _ & Hcl & H47 & _ & _ & _ & _ & Hs1 & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (rbn_pre_parts c HPRE) as (_ & HRO & _).
pose proof (aro_unowned_of_arodata _ _ _ _ _ HRO) as HU.
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Fimg & _).
assert (HNS : ~ YI16.sink_open_fp (x_FP c)).
{ unfold rbn_pre in HPRE.
  destruct HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hn & _ & _ & _ & Ht & _ & _ & _ & _ & Hd & _).
  exact (rbn_fp_closed _ _ _ _ _ _ (proj1 Hn) (proj1 Ht) (proj1 Hd)). }
apply (aro_unowned_keep SEGS B _ _ HU).
intros a Hrom Ho He.
assert (Hi : in_img SEGS a) by (destruct Hrom as (sg & Hsg & _ & Ha); exists sg; split; [exact Hsg | exact Ha]).
pose proof (pa_img_range a Hi) as Hr.
rewrite (NW a ltac:(lia) ltac:(lia)). exact (Fimg a Hi Ho He (fp_spares_closed _ a HNS)).
Qed.
Lemma rbn2_pres_r : forall r1 r2, aregs_preserved r1 r2 ->
  forall (x : bv 5) z, bv_unsigned x = z -> acallee_saved z -> getr r2 x = getr r1 x.
Proof. intros r1 r2 HP x z Hz Hr. pose proof (HP z Hr) as X. rewrite <- Hz, Z_to_bv_bv_unsigned in X. exact X. Qed.

(* ---- C13. C3 0x830cc (+0x358): wb.n (= 4, the bne is dead), s5 = 4, strlen(stem) at 0x830dc; then C11 ---- *)
Definition rbn2_ss5 : sstate := mkSS (AF_reac_box_name + 0x358) sr_atoms
  [YP09.mkRegion (Some 9%nat) 200 208 0 0 [YP09.mkChunk 200 (CVal 8 (SLit 4))]] None
  (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma rbn_seg_c3_c45 : forall c st lyc Sc memc mdc regs,
  rbn_C3 B G c st lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x358)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3b4)) mem' (seg_rom SEGS)) md' /\
        rbn_C4 B G c 0 lyc' Sc' mem' md' regs') \/
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3f8)) mem' (seg_rom SEGS)) md' /\
        rbn_C5 B G c lyc' Sc' mem' md' regs')).
Proof.
intros c st lyc Sc memc mdc regs HC3.
change (SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x358)) memc (seg_rom SEGS)) mdc)
  (rbn2_Q c)).
pose proof HC3 as (HL & HST & (HWB & _ & _) & _ & R25 & _).
pose proof HL as (HC & Hargs & _).
pose proof HC as (_ & HJ & _ & G2 & G3 & G4 & _ & G9 & _).
destruct (rbn_geom c lyc Sc memc mdc regs HC) as (_ & Hsp0al & Hcl & H47 & _ & _ & _ & _ & Hs1 & Hs1m & _).
assert (Hes : ESTACK = 4096) by reflexivity. pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAF : AF_reac_box_name = 9728) by reflexivity.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (rbn2_w4 c Hargs) as (Lw4 & _).
assert (HM0 : rbn2_M c st lyc Sc memc mdc regs memc mdc regs)
  by exact (conj HC3 (conj HJ (conj (fun a _ _ => eq_refl) (rbn2_rk_refl regs)))).
pose proof (rbn2_M_sf c st lyc Sc memc mdc regs memc mdc regs HM0) as (_ & Hk31 & Hst0 & Hstc & _).
set (k := Z.of_nat (length (x_stem c))) in *.
assert (Hk0 : 0 <= k) by (unfold k; lia).
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg regs []) E)
  by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (US1 : bv_unsigned (ew E 9) = x_s1 c)
  by (rewrite HE, (ew_Eimg_Ereg_nat regs [] 9 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
assert (E25 : ew E 25 = Z_to_bv 64 st) by (rewrite HE, (ew_Eimg_Ereg_nat regs [] 25 25%bv eq_refl); exact R25).
assert (HS : st_ok_pi SEGS VAL E rbn2_ss5
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + (AF_reac_box_name + 0x358))) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn2_ss5. apply pa_entry_st_ok_full.
  - rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite US1.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E _ _ 200 8%N (SLit 4) 4); [reflexivity | cbn; lia | cbn; lia |].
    destruct HWB as (_ & _ & V16 & _). unfold x_mem_at, x_wb in V16. rewrite Lw4 in V16.
    change (Z.of_nat 4) with 4 in V16. replace (x_s1 c + 200) with (x_s1 c + 184 + 16) by lia. exact V16.
  - cbn [pairwise_disjoint all_disjoint]. split; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite US1. change (2 ^ 5) with 32. repeat split; lia. }
(* the arithmetic the strlen contract asks, while the context is small *)
assert (Hom : (x_s1 c - x_sp0 c) mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as Ds. rewrite Hs1m, Z.add_0_r in Ds.
  pose proof (Z.div_mod (x_sp0 c) 16 ltac:(lia)) as Dp. rewrite Hsp0al, Z.add_0_r in Dp.
  replace (x_s1 c - x_sp0 c) with ((2 * (x_s1 c / 32) - x_sp0 c / 16) * 16) by lia. apply Z_mod_mult. }
assert (A1 : 0 < st /\ k + 1 < 2 ^ 32 /\ st + k + 1 <= 2 ^ 63 /\ x_s1 c - x_sp0 c <= 0 /\
  2 * ESTACK - (x_s1 c - x_sp0 c) <= RBN_STK /\ 0 <= x_s1 c < 2 ^ 64 /\ x_sp0 c + (x_s1 c - x_sp0 c) = x_s1 c /\
  (forall a, st <= a <= st + k -> ~ (x_sp0 c + (x_s1 c - x_sp0 c) - 2 * ESTACK <= a < x_sp0 c + (x_s1 c - x_sp0 c))))
  by (repeat split; try lia; intros a Ha; lia).
destruct A1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
assert (Hra : YK0s.ret_ok (Z_to_bv 64 (BASE + 10604))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
rewrite <- Z.add_assoc.
paj_run_shc RUNP RUNC HS HJ.
{ unfold rbn2_ss5. cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]. }
pose proof (rbn2_av_nowin E (ss_mem rbn2_ss5) (x_W c) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ rbn2_kl HS AGE ltac:(vm_compute; reflexivity)) as KR.
cbn [ms_regs restrict] in KR.
pose proof (rbn2_rk_of regs (ms_regs ms) KR) as RK1.
prreg HS (1%bv : bv 5) Rra. prreg HS (10%bv : bv 5) Ra0. prreg HS (21%bv : bv 5) Rs5.
rewrite E25 in Ra0.
pmkst HS.
pose proof (rbn2_M_same c st lyc Sc memc mdc regs memc mdc regs (ms_mem ms) _ (ms_regs ms) HM0 HJ
  (fun a _ _ => KA a) RK1) as HM1.
pose proof (rbn2_M_sf c st lyc Sc memc mdc regs _ _ _ HM1) as SF1.
pose proof SF1 as (_ & _ & _ & _ & Hamr1 & _ & SRA1 & SHV1 & STL1).
fold k in Hamr1, SRA1, SHV1, STL1.
pose proof RK1 as (K2 & K3 & K4 & _).
assert (Usp : spZ (ms_regs ms) = x_sp0 c + (x_s1 c - x_sp0 c))
  by (unfold spZ; rewrite K2, G2, A7; unfold w64; apply unsigned_lit_small; exact A6).
eapply SRr_bind.
{ apply (rbn2_aj_strlen_at (x_W c) (ms_regs ms) (ms_mem ms) RBN_STK (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c)
    (x_mem c) (x_md c) [(3, x_fpos c)] lyc Sc _ 0 st k (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + 10604)) HJ).
  - exact Ra0.
  - exact A1.
  - exact Hk0.
  - exact A2.
  - exact A3.
  - exact Usp.
  - exact Hom.
  - exact A4.
  - exact A5.
  - rewrite K3. exact G3.
  - rewrite K4. exact G4.
  - exact Rra.
  - exact Hra.
  - exact (rbn2_fb c (ms_mem ms) st SF1).
  - exact A8.
  - exact Hamr1.
  - exact SRA1.
  - apply SHV1; clear - Hk0; lia.
  - exact STL1.
  - exact (rbn2_aro c st lyc Sc memc mdc regs _ _ _ HM1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hk2 & Hfr).
replace (BASE + 10604) with (BASE + AF_reac_box_name + 0x36c) by (clear - HAF; rewrite HAF; lia).
apply (rbn2_p6 c st lyc Sc memc mdc regs mem2 md2 regs2).
- apply (rbn2_M_same c st lyc Sc memc mdc regs (ms_mem ms) _ (ms_regs ms) mem2 md2 regs2 HM1 HJ2).
  + intros a Ha Hw. apply Hfr; [exact Ha | rewrite A7; exact Hw].
  + exact (rbn2_rk_pres _ _ _ (rbn2_rk_refl _) HP2).
- exact Hk2.
- rewrite (rbn2_pres_r _ _ HP2 21%bv 21 eq_refl ltac:(unfold acallee_saved; clear; lia)). exact Rs5.
Qed.

End walk.
End h.
End f.
End d.
