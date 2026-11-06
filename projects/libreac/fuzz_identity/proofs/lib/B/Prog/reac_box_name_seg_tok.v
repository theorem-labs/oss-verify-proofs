(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8j.v:156-159
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:360-363 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AFhg.v:439 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:367-370
   [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan build (lib/B). The [Apache-2.0 OR MIT] text is used
   under Apache-2.0. *)
(* reac_box_name (fuzz_identity.asan-ubsan 0x82d74, AF_reac_box_name = 0x2600): three segments of its program walk,
   between the cut points of lib/B/Prog/reac_box_name_inv.v (BINDING; the statements are the walk owner's,
   a Theorem Labs lane), in the split-walk form of cgif lib/A/AC8b.v tcbb_loopX. lib/B/Prog/reac_box_name.v composes them.
     rbn_seg_c5_c6  0x8316c .. 0x831c8 (C5 -> C6): nb.n bound traps (0x83174, 0x8317c), nm's NUL, tk's scope,
                    tb's p / cap, memset(tb.n, 0, 16) at 0x831b0 (AMEMSET), the nb.n = 0 branch (0x831b8) dead;
     rbn_tok_loop   0x831c8 .. 0x83230 (C6 -> C7): one char per round (rbn_tok_body: the i = 24 trap dead, nm[i]'s
                    shadow check by the token engine, the first '-' dropped, bn_low' and sb_ch(tb) at 0x83210;
                    rbn_tok_tail: the back edge 0x8321c), by induction on the chars left;
     rbn_seg_c7_c8  0x83230 .. 0x83298 (C7 -> C8): tb.n bound traps (0x83238, 0x83240), tk's NUL, dp's scope,
                    db's p / cap, memset(db.n, 0, 16) at 0x83280, the nm[0] = 0 branch (0x83288) dead.
   The two straight segments write shadow bytes and contain no instrumented check, so they run with an empty Bspan;
   the loop runs the token engine with a shadow entry for nm[i]. sb_ch is applied through HSC (lib/B/Prog/sb_ch.v
   tsb_ch_spec) at its PSIG address; its post keeps the cut state's facts by tcj_kept (rkeep below). *)
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
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import StrlenDef SetShadowDef.
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
Hypothesis AMEMSET : aintrin_realizes SEGS B OSet (SIGMA IB___asan_memset).
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
(* ---- Memory kept outside a set of addresses ---- *)
Definition mkeep (W : world SEGS) (m m' : word -> option byte) (Zs : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a.
Lemma mkeep_refl : forall W m Zs, mkeep W m m Zs.
Proof. intros W m Zs a _ _. reflexivity. Qed.
Lemma mkeep_trans : forall W m1 m2 m3 (Z1 Z2 : Z -> Prop),
  mkeep W m1 m2 Z1 -> mkeep W m2 m3 Z2 -> mkeep W m1 m3 (fun a => Z1 a \/ Z2 a).
Proof.
intros W m1 m2 m3 Z1 Z2 H1 H2 a Ha Hz.
rewrite (H2 a Ha (fun h => Hz (or_intror h))). exact (H1 a Ha (fun h => Hz (or_introl h))).
Qed.
Lemma mkeep_mono : forall W m m' (Z1 Z2 : Z -> Prop), mkeep W m m' Z1 -> (forall a, Z1 a -> Z2 a) ->
  mkeep W m m' Z2.
Proof. intros W m m' Z1 Z2 H HZ a Ha Hz. apply H; [exact Ha | intros h; exact (Hz (HZ a h))]. Qed.
Lemma mkeep_val : forall W m m' (Zs : Z -> Prop) a n v, mkeep W m m' Zs ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> ~ Zs x) ->
  val_mem SEGS (mrestrict (w_H W) m) a n v -> val_mem SEGS (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' Zs a n v HK H0 H1 HZ HV. apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [|exact HV].
intros k Hk. apply HK; [lia | apply HZ; lia].
Qed.
Lemma mkeep_garr8 : forall W m m' (Zs : Z -> Prop) a l, mkeep W m m' Zs ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat (length l) -> ~ Zs x) ->
  garr8 SEGS (mrestrict (w_H W) m) a l -> garr8 SEGS (mrestrict (w_H W) m') a l.
Proof.
intros W m m' Zs a l HK H0 H1 HZ HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
apply (mkeep_val W m m' Zs _ 1 _ HK); [lia | lia | | exact HV]. intros x Hx. apply HZ. lia.
Qed.
(* ---- What the cut states fix: the stack, the window and the frame ---- *)
Lemma rbn_core_bounds : forall c lyc Sc memc mdc regs, rbn_core B G c lyc Sc memc mdc regs ->
  x_sp0 c mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo lyc /\ ly_stk_lo lyc + 8528 <= x_sp0 c /\
  x_sp0 c <= ly_stk_hi lyc /\ ly_stk_hi lyc <= 2 ^ 47 /\
  x_s1 c mod 32 = 0 /\ x_sp0 c - 352 <= x_s1 c /\ x_s1 c + 320 <= x_sp0 c /\
  In (3, x_fpos c) (frames Sc) /\ frame_addr lyc 3 (x_fpos c) = x_F c /\
  4096 <= x_F c /\ x_F c + 512 <= alloc_ceiling /\ in_app (x_F c) 512 /\ x_F c mod 32 = 0 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof.
intros c lyc Sc memc mdc regs (HPRE & HJ & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
pose proof asan_consts as (C1 & _).
assert (Hes : ESTACK = 4096) by reflexivity.
assert (Hin : In (3, x_fpos c) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; left; reflexivity).
assert (EFa : frame_addr lyc 3 (x_fpos c) = x_F c) by (unfold x_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR Hin) as (F1 & F2 & F3).
destruct (al_frames _ _ LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR Hin) as (Fal & _).
change (fs_frame_bytes 3) with 512 in *.
rewrite EFa in F1, F2, F3, Fal. rewrite Elo, Ehi.
pose proof (Z.div_mod (x_sp0 c - 320) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x_sp0 c - 320) 32 ltac:(lia)) as M.
assert (S1 : x_s1 c = 32 * ((x_sp0 c - 320) / 32)) by reflexivity.
assert (S1m : x_s1 c mod 32 = 0) by (rewrite S1, Z.mul_comm; apply Z_mod_mult).
split; [exact Hal|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact S1m|]. split; [lia|]. split; [lia|]. split; [exact Hin|]. split; [exact EFa|].
split; [lia|]. split; [lia|]. split; [exact F3|]. split; [exact Fal | exact C1].
Qed.
(* x_nmc: one to 23 chars, each 1 .. 255 (the stem is non-empty; the chars of sd come from rbn_said). *)
Lemma bn_stem_ne : forall f sd, (1 <= length (bn_stem f sd))%nat.
Proof.
intros f [|x sd]; cbn [bn_stem length]; [|lia].
unfold bn_STEM; destruct (f =? 1); [|destruct (f =? 2); [|destruct (f =? 3)]]; cbn [length]; lia.
Qed.
Lemma rbn_nmc_facts : forall c lyc Sc memc mdc regs, rbn_live B G c lyc Sc memc mdc regs ->
  (1 <= length (x_nmc c) <= 23)%nat /\ Forall (fun x => 0 < x < 256) (x_nmc c).
Proof.
intros c lyc Sc memc mdc regs (HCORE & HARGS & _).
destruct HCORE as (HPRE & _).
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HACC & _).
destruct (HACC HARGS) as (HSAID & _).
assert (Hsd : Forall (fun x => 0 < x < 256) (x_sd c)).
{ destruct HSAID as [(_ & ->) | (_ & (Hf & _) & _)]; [constructor | exact Hf]. }
unfold reac_box_name_c.bn_args_ok in HARGS.
apply andb_prop in HARGS as [HA1 _]. apply andb_prop in HA1 as [HA2 Ho]. apply andb_prop in HA2 as [_ Hi].
pose proof (rbn_nm_spec (x_f c) (x_sd c) (x_i c) (x_o c) Hi Ho (bn_stem_chars _ _ Hsd)) as (_ & _ & _ & _ & Hlen & Hch).
unfold x_nmc, x_nb_full. split; [split; [|exact Hlen] | exact Hch].
rewrite rbn_nm_tr. unfold sbm_tr. cbn [fst]. rewrite length_firstn.
assert (L : (1 <= length (bn_NM (x_f c) (x_sd c) (x_i c) (x_o c)))%nat).
{ unfold bn_NM. cbv zeta. pose proof (bn_stem_ne (x_f c) (x_sd c)) as N1.
  destruct (_ && _); [lia | rewrite length_app; lia]. }
change (Z.to_nat (24 - 1)) with 23%nat. lia.
Qed.
(* ---- Bytes from aview facts ---- *)
Lemma val1_of_aview : forall H (m : word -> option byte) a v,
  aview SEGS H m a = Some v -> val_mem SEGS (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv j Hj. assert (j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H m a v Hv) as (b & Hb & -> & Hr). cbn [Z.of_nat]. rewrite Z.add_0_r, Hb. f_equal.
apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (bv_modulus 8) with 256. change (2 ^ 8) with 256. repeat rewrite (Z.mod_small (bv_unsigned b) 256 Hr). reflexivity.
Qed.
Lemma val_mem_zeros : forall H (m : word -> option byte) a n,
  (forall i, 0 <= i < Z.of_nat n -> aview SEGS H m (a + i) = Some 0) -> val_mem SEGS (mrestrict H m) a n 0.
Proof.
intros H m a n Hz j Hj. destruct (aview_byte SEGS H m (a + Z.of_nat j) 0 (Hz (Z.of_nat j) ltac:(lia))) as (b & Hb & Hv & _).
rewrite Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
repeat (rewrite Z.shiftr_0_l || rewrite Z.mod_0_l by ((first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate]))). lia.
Qed.
Lemma garr8_one : forall (mm : word -> option byte) a v, val_mem SEGS mm a 1 v -> 0 <= v < 256 -> garr8 SEGS mm a [v].
Proof.
intros mm a v Hv Hr j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. cbn [nth Z.of_nat].
rewrite Z.add_0_r. split; [exact Hv | exact Hr].
Qed.
(* ---- The pieces of a cut state, kept by a step that writes elsewhere ---- *)
Lemma rbn_sb_keep : forall c m m' (Zs : Z -> Prop) b q cap cs ov, mkeep (x_W c) m m' Zs ->
  0 <= b -> b + 28 <= 2 ^ 64 -> 0 <= q -> q + Z.of_nat (length cs) <= 2 ^ 64 ->
  (forall x, b <= x < b + 28 -> ~ Zs x) -> (forall x, q <= x < q + Z.of_nat (length cs) -> ~ Zs x) ->
  rbn_sb c m b q cap cs ov -> rbn_sb c m' b q cap cs ov.
Proof.
intros c m m' Zs b q cap cs ov HK Hb0 Hb1 Hq0 Hq1 Zb Zq (V0 & V1 & V2 & V3 & Hov & Hlen & Hfa & HG).
unfold x_mem_at in *.
split; [apply (mkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V0]|].
split; [apply (mkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V1]|].
split; [apply (mkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V2]|].
split; [apply (mkeep_val _ _ _ _ _ 4 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V3]|].
split; [exact Hov|]. split; [exact Hlen|]. split; [exact Hfa|].
apply (mkeep_garr8 _ _ _ _ _ _ HK); [lia | lia | intros x Hx; apply Zq; lia | exact HG].
Qed.
Definition rbn_zone (c : rbx) (a : Z) : Prop :=
  (x_s1 c - SB_CH_STK <= a < x_s1 c) \/ (x_s1 c + 88 <= a < x_s1 c + 152) \/
  (x_F c + 32 <= a < x_F c + 256) \/ (x_FS c + 4 <= a < x_FS c + 30).
(* The bytes a callee's post speaks of (IdentBCJ.v tcj_kept): the machine stack and above, the frame (3, fpos) and
   its shadow, the heap blocks of the entry state. Every fact of a cut state lies in them. *)
Definition rbn_cov (c : rbx) (a : Z) : Prop :=
  alloc_ceiling <= a \/ (x_F c <= a < x_F c + 512) \/ (x_FS c <= a < x_FS c + 64) \/
  (exists q N, In (q, N) (ablocks B (x_ly c) (x_S c)) /\ q <= a < q + N).
Definition rkeep (c : rbx) (m m' : word -> option byte) (Zs : Z -> Prop) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> rbn_cov c a -> ~ Zs a -> aview SEGS (w_H (x_W c)) m' a = aview SEGS (w_H (x_W c)) m a.
Lemma mkeep_rkeep : forall c m m' Zs, mkeep (x_W c) m m' Zs -> rkeep c m m' Zs.
Proof. intros c m m' Zs HK a Ha _ Hz. exact (HK a Ha Hz). Qed.
Lemma rkeep_mono : forall c m m' (Z1 Z2 : Z -> Prop), rkeep c m m' Z1 -> (forall a, Z1 a -> Z2 a) -> rkeep c m m' Z2.
Proof. intros c m m' Z1 Z2 H HZ a Ha Hc Hz. apply H; [exact Ha | exact Hc | intros h; exact (Hz (HZ a h))]. Qed.
Lemma rkeep_val : forall c m m' (Zs : Z -> Prop) a n v, rkeep c m m' Zs ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat n -> rbn_cov c x /\ ~ Zs x) ->
  val_mem SEGS (mrestrict (w_H (x_W c)) m) a n v -> val_mem SEGS (mrestrict (w_H (x_W c)) m') a n v.
Proof.
intros c m m' Zs a n v HK H0 H1 HZ HV. apply (val_mem_kept SEGS (w_H (x_W c)) (w_H (x_W c)) m m' a n v); [|exact HV].
intros k Hk. destruct (HZ (a + k) ltac:(lia)) as [Hc Hz]. apply HK; [lia | exact Hc | exact Hz].
Qed.
Lemma rkeep_garr8 : forall c m m' (Zs : Z -> Prop) a l, rkeep c m m' Zs ->
  0 <= a -> a + Z.of_nat (length l) <= 2 ^ 64 -> (forall x, a <= x < a + Z.of_nat (length l) -> rbn_cov c x /\ ~ Zs x) ->
  garr8 SEGS (mrestrict (w_H (x_W c)) m) a l -> garr8 SEGS (mrestrict (w_H (x_W c)) m') a l.
Proof.
intros c m m' Zs a l HK H0 H1 HZ HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
apply (rkeep_val c m m' Zs _ 1 _ HK); [lia | lia | | exact HV]. intros x Hx. apply HZ. lia.
Qed.
Lemma rbn_sb_rkeep : forall c m m' (Zs : Z -> Prop) b q cap cs ov, rkeep c m m' Zs ->
  0 <= b -> b + 28 <= 2 ^ 64 -> 0 <= q -> q + Z.of_nat (length cs) <= 2 ^ 64 ->
  (forall x, b <= x < b + 28 -> rbn_cov c x /\ ~ Zs x) ->
  (forall x, q <= x < q + Z.of_nat (length cs) -> rbn_cov c x /\ ~ Zs x) ->
  rbn_sb c m b q cap cs ov -> rbn_sb c m' b q cap cs ov.
Proof.
intros c m m' Zs b q cap cs ov HK Hb0 Hb1 Hq0 Hq1 Zb Zq (V0 & V1 & V2 & V3 & Hov & Hlen & Hfa & HG).
unfold x_mem_at in *.
split; [apply (rkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V0]|].
split; [apply (rkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V1]|].
split; [apply (rkeep_val _ _ _ _ _ 8 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V2]|].
split; [apply (rkeep_val _ _ _ _ _ 4 _ HK); [lia | lia | intros x Hx; apply Zb; lia | exact V3]|].
split; [exact Hov|]. split; [exact Hlen|]. split; [exact Hfa|].
apply (rkeep_garr8 _ _ _ _ _ _ HK); [lia | lia | intros x Hx; apply Zq; lia | exact HG].
Qed.
Lemma rbn_live_rkeep : forall c lyc Sc m md regs lyc' Sc' m' md' (regs' : bvmap 5 word),
  rbn_live B G c lyc Sc m md regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc' Sc' (x_W c) m' md' 0 ->
  Permutation (ablocks B lyc' Sc') (ablocks B (x_ly c) (x_S c)) ->
  rkeep c m m' (rbn_zone c) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  rbn_live B G c lyc' Sc' m' md' regs'.
Proof.
intros c lyc Sc m md regs lyc' Sc' m' md' regs' HL HJ' HP' HK Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23.
pose proof (rbn_core_bounds c lyc Sc m md regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
destruct HL as (HCORE & HARGS & HBK & HSLOT & R22).
destruct HCORE as (HPRE & _ & _ & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & HSAV & HFLAG).
pose proof HJ' as (HAR' & Hly' & _ & _ & _ & Hfrs' & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (HZ : forall a, rbn_zone c a -> (x_s1 c - 4112 <= a < x_s1 c) \/ (x_s1 c + 88 <= a < x_s1 c + 152) \/
   (x_F c + 32 <= a < x_F c + 256) \/ (2147450880 + x_F c / 8 + 4 <= a < 2147450880 + x_F c / 8 + 30)).
{ intros a Ha. unfold rbn_zone, x_FS in Ha. change SB_CH_STK with 4112 in Ha. change SHADOW_OFF with 2147450880 in Ha. exact Ha. }
split; [|split; [exact HARGS|split; [|split; [|rewrite Q22; exact R22]]]].
- split; [exact HPRE|]. split; [exact HJ'|]. split; [exact HP'|].
  rewrite Q2, Q3, Q4, Q8, Q9, Q18, Q19, Q23.
  do 8 (split; [assumption|]). split.
  + unfold rbn_saved in *. apply Forall_forall. intros p Hp. pose proof (proj1 (Forall_forall _ _) HSAV p Hp) as Hv.
    assert (Hfst : 8 <= fst p <= 104).
    { unfold rbn_saved_regs in Hp. repeat (destruct Hp as [<- | Hp]; [cbn [fst]; lia |]). destruct Hp. }
    unfold x_mem_at in *. apply (rkeep_val c m m' (rbn_zone c) _ 8 _ HK); [lia | lia | | exact Hv].
    intros x Hx. split; [left; lia | intros Hz; apply HZ in Hz; lia].
  + rewrite (rdword_ext (aview SEGS (w_H (x_W c)) m) (aview SEGS (w_H (x_W c)) m') (x_F c + 504)); [exact HFLAG|].
    intros k Hk. apply HK; [lia | right; left; lia |]. intros Hz. apply HZ in Hz.
    destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | lia |].
    apply (fshadow_not_app (x_F c) 30 (x_F c) 512 (x_F c + 504 + k)); [lia | lia | exact HFapp | lia | lia].
- intros a Hfp (q & N & Hin & Hq).
  rewrite <- (HBK a Hfp (ex_intro _ q (ex_intro _ N (conj Hin Hq)))).
  pose proof (Permutation_in _ (Permutation_sym HP') Hin) as Hin'.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ q N HAR' Hin') as (_ & Hq4096 & Hqc & Hqapp & _).
  assert (HinF' : In (3, x_fpos c) (frames Sc')) by (rewrite Hfrs'; apply in_or_app; left; left; reflexivity).
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ q N 3 (x_fpos c) HAR' Hin' HinF') as Hsep.
  assert (EFa' : frame_addr lyc' 3 (x_fpos c) = x_F c)
    by (pose proof Hly' as (_ & _ & _ & _ & _ & EF & _); unfold x_F, frame_addr; rewrite EF; reflexivity).
  rewrite EFa' in Hsep. change (fs_frame_bytes 3) with 512 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  assert (HrN : N <= req_size N) by (unfold req_size; destruct (Z.eqb_spec N 0); lia).
  apply HK; [lia | right; right; right; exists q, N; split; [exact Hin | lia] |].
  intros Hz. apply HZ in Hz. destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | lia |].
  apply (fshadow_not_app (x_F c) 30 q (req_size N) a); [lia | lia | exact Hqapp | lia | lia].
- unfold rbn_slots in *. cbv zeta in HSLOT |- *. unfold x_mem_at in *.
  destruct HSLOT as (V0 & V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8).
  repeat split; (apply (rkeep_val c m m' (rbn_zone c) _ 8 _ HK);
    [lia | lia | intros x Hx; split; [left; lia | intros Hz; apply HZ in Hz; lia] | assumption]).
Qed.
Lemma rbn_live_keep : forall c lyc Sc m md regs lyc' Sc' m' md' (regs' : bvmap 5 word),
  rbn_live B G c lyc Sc m md regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc' Sc' (x_W c) m' md' 0 ->
  Permutation (ablocks B lyc' Sc') (ablocks B (x_ly c) (x_S c)) ->
  mkeep (x_W c) m m' (rbn_zone c) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 ->
  getr regs' 19 = getr regs 19 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
  rbn_live B G c lyc' Sc' m' md' regs'.
Proof.
intros c lyc Sc m md regs lyc' Sc' m' md' regs' HL HJ' HP' HK.
exact (rbn_live_rkeep c lyc Sc m md regs lyc' Sc' m' md' regs' HL HJ' HP' (mkeep_rkeep c m m' _ HK)).
Qed.
(* ---- C5 -> C6: what the state at C6 needs from the memory and registers the segment leaves ---- *)
(* The bytes 0x8316c .. 0x831c4 write: memset's stack, tb (s1 + 120 .. 152), nm's NUL, tk's scope. *)
Definition rbn_z56 (c : rbx) (a : Z) : Prop :=
  (x_s1 c - SB_CH_STK <= a < x_s1 c) \/ (x_s1 c + 120 <= a < x_s1 c + 152) \/
  a = x_NM c + Z.of_nat (length (x_nmc c)) \/ (x_FS c + 16 <= a < x_FS c + 19).
Lemma rbn_C6_of_C5 : forall c lyc Sc memc mdc regs mF mdF (regsF : bvmap 5 word),
  rbn_C5 B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mF mdF 0 ->
  mkeep (x_W c) memc mF (rbn_z56 c) ->
  val_mem SEGS (x_mem_at c mF) (x_s1 c + 120) 8 (x_TK c) ->
  val_mem SEGS (x_mem_at c mF) (x_s1 c + 128) 8 24 ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H (x_W c)) mF (x_s1 c + 136 + i) = Some 0) ->
  aview SEGS (w_H (x_W c)) mF (x_NM c + Z.of_nat (length (x_nmc c))) = Some 0 ->
  (forall j, 16 <= j < 19 -> aview SEGS (w_H (x_W c)) mF (x_FS c + j) = Some 0) ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 22 = getr regs 22 -> getr regsF 23 = getr regs 23 ->
  getr regsF 27 = getr regs 27 ->
  getr regsF 25 = w64 (x_TK c) -> getr regsF 21 = w64 0 -> getr regsF 26 = w64 0 ->
  getr regsF 24 = w64 45 -> getr regsF 20 = w64 24 ->
  rbn_C6 B G c 0 lyc Sc mF mdF regsF.
Proof.
intros c lyc Sc memc mdc regs mF mdF regsF (HL & HW4 & HSCO & HNB) HJF HK VTp VTc Z16 ZN ZS
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q27 R25 R21 R26 R24 R20.
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (proj1 HL) as (_ & _ & HPERM & _).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (HZ : forall a, rbn_z56 c a -> (x_s1 c - 4112 <= a < x_s1 c) \/ (x_s1 c + 120 <= a < x_s1 c + 152) \/
   a = x_F c + 64 + Z.of_nat (length (x_nmc c)) \/ (2147450880 + x_F c / 8 + 16 <= a < 2147450880 + x_F c / 8 + 19)).
{ intros a Ha. unfold rbn_z56, x_FS, x_NM in Ha. change SB_CH_STK with 4112 in Ha.
  change SHADOW_OFF with 2147450880 in Ha. exact Ha. }
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (NZf : forall x, x_F c <= x < x_F c + 512 -> x <> x_F c + 64 + Z.of_nat (length (x_nmc c)) -> ~ rbn_z56 c x).
{ intros x Hx Hne Hz. apply HZ in Hz. destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | lia |].
  exact (fshadow_not_app (x_F c) 19 (x_F c) 512 x ltac:(lia) ltac:(lia) HFapp ltac:(lia) Hx). }
assert (NZs : forall x, x_FS c <= x < x_FS c + 64 -> ~ (x_FS c + 16 <= x < x_FS c + 19) -> ~ rbn_z56 c x).
{ intros x Hx Hne Hz. apply HZ in Hz. rewrite EFS in Hx, Hne.
  destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | |lia].
  subst x. exact (fshadow_not_app (x_F c) 64 (x_F c) 512 (x_F c + 64 + Z.of_nat (length (x_nmc c)))
    ltac:(lia) ltac:(lia) HFapp ltac:(lia) ltac:(lia)). }
assert (NZw : forall x, x_s1 c + 152 <= x < x_sp0 c -> ~ rbn_z56 c x).
{ intros x Hx Hz. apply HZ in Hz. lia. }
unfold rbn_C6.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- apply (rbn_live_keep c lyc Sc memc mdc regs lyc Sc mF mdF regsF HL HJF HPERM); try assumption.
  apply (mkeep_mono _ _ _ _ _ HK). intros a Ha. apply HZ in Ha. unfold rbn_zone. rewrite EFS.
  change SB_CH_STK with 4112. lia.
- destruct HW4 as (HWB & HGW & R27). split; [|split; [|rewrite Q27; exact R27]].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _).
    apply (rbn_sb_keep c memc mF (rbn_z56 c) _ _ _ _ _ HK); unfold x_wb, x_W4 in *;
      [lia | lia | lia | lia | intros x Hx; apply NZw; lia | intros x Hx; apply NZf; lia | exact HWB].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _). unfold x_mem_at, x_W4 in *.
    apply (mkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx; apply NZf; lia | exact HGW].
- split; [|split; [|exact R25]].
  + apply (rbn_sb_keep c memc mF (rbn_z56 c) _ _ _ _ _ HK); unfold x_nb, x_NM in *;
      [lia | lia | lia | lia | intros x Hx; apply NZw; lia | intros x Hx; apply NZf; lia | exact HNB].
  + destruct HNB as (_ & _ & _ & _ & _ & _ & _ & HG). unfold x_mem_at in *.
    apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    * apply (mkeep_garr8 _ _ _ _ _ _ HK); unfold x_NM in *; [lia | lia | intros x Hx; apply NZf; lia | exact HG].
    * apply garr8_one; [apply val1_of_aview; exact ZN | lia].
- lia.
- exact R21.
- change (firstn (Z.to_nat 0) (x_nmc c)) with (@nil Z). cbn [existsb]. exact R26.
- exact R24.
- exact R20.
- destruct HSCO as (S4 & S8 & S16 & S24). unfold rbn_scope. cbv zeta.
  split; [rewrite (HK (x_FS c + 4)); [exact S4 | lia | apply NZs; lia]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S8 j Hj) | lia | apply NZs; lia]|].
  split; [exact ZS|].
  intros j Hj; rewrite (HK (x_FS c + j)); [exact (S24 j Hj) | lia | apply NZs; lia].
- change (firstn (Z.to_nat 0) (x_nmc c)) with (@nil Z). change (rbn_tok []) with (@nil Z, 0). cbn [fst snd].
  unfold rbn_sb, x_tb, x_TK, x_mem_at in *. cbv zeta.
  split; [exact VTp|]. split; [replace (x_s1 c + 120 + 8) with (x_s1 c + 128) by lia; exact VTc|].
  split; [cbn [length Z.of_nat]; apply val_mem_zeros; intros i Hi;
          replace (x_s1 c + 120 + 16 + i) with (x_s1 c + 136 + i) by lia; apply Z16; lia|].
  split; [apply val_mem_zeros; intros i Hi;
          replace (x_s1 c + 120 + 24 + i) with (x_s1 c + 136 + (8 + i)) by lia; apply Z16; lia|].
  split; [left; reflexivity|]. split; [cbn [length Z.of_nat]; lia|]. split; [constructor|]. apply garr8_nil.
Qed.
(* ---- Calls with sp = s1 ---- *)
Lemma rbn_s1_mod16 : forall c, x_sp0 c mod 16 = 0 -> (x_s1 c - x_sp0 c) mod 16 = 0.
Proof.
intros c Hal. assert (H1 : x_s1 c mod 16 = 0).
{ unfold x_s1. replace (32 * ((x_sp0 c - 320) / 32)) with ((2 * ((x_sp0 c - 320) / 32)) * 16) by lia. apply Z_mod_mult. }
rewrite Zminus_mod, H1, Hal. reflexivity.
Qed.
(* The machine stack is marked usable (al_zshadow on the page-aligned stack range): a range inside it is
   addressable, and so is the 8-byte hull of its shadow bytes. *)
Lemma rbn_stack_shadow : forall lyc Sc (W : world SEGS) m md d n,
  AR SEGS B lyc Sc W m md -> ly_stk_lo lyc <= d -> d + n <= ly_stk_hi lyc -> 0 < n ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF d n /\ shadow_hull_vis (aview SEGS (w_H W) m) d n.
Proof.
intros lyc Sc W m md d n HAR Hlo Hhi Hn.
pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR))) as (_ & _ & _ & _ & Hpal & Hpah & _).
pose proof (al_zshadow _ _ LAWS lyc Sc W m md (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
  HAR ltac:(left; reflexivity)) as Hz. cbn [fst snd] in Hz.
unfold page_aligned in Hpal, Hpah.
pose proof (Z.div_mod (ly_stk_lo lyc) 4096 ltac:(lia)) as D1. pose proof (Z.div_mod (ly_stk_hi lyc) 4096 ltac:(lia)) as D2.
rewrite Hpal, Z.add_0_r in D1. rewrite Hpah, Z.add_0_r in D2.
assert (Hz' : forall y, ly_stk_lo lyc <= y < ly_stk_hi lyc -> aview SEGS (w_H W) m (SHADOW_OFF + y / 8) = Some 0).
{ intros y Hy.
  pose proof (Z.div_mod y 8 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound y 8 ltac:(lia)) as M3.
  assert (E1 : ly_stk_lo lyc / 8 = 512 * (ly_stk_lo lyc / 4096)).
  { rewrite D1 at 1. replace (4096 * (ly_stk_lo lyc / 4096)) with ((512 * (ly_stk_lo lyc / 4096)) * 8) by lia.
    apply Z.div_mul. lia. }
  assert (E2 : (ly_stk_hi lyc - ly_stk_lo lyc) / 8 = 512 * (ly_stk_hi lyc / 4096 - ly_stk_lo lyc / 4096)).
  { replace (ly_stk_hi lyc - ly_stk_lo lyc) with ((512 * (ly_stk_hi lyc / 4096 - ly_stk_lo lyc / 4096)) * 8) by lia.
    apply Z.div_mul. lia. }
  pose proof (Hz (y / 8 - 512 * (ly_stk_lo lyc / 4096))) as Hy'. rewrite E2 in Hy'. unfold shadow_of_addr in Hy'.
  rewrite E1 in Hy'.
  replace (SHADOW_OFF + 512 * (ly_stk_lo lyc / 4096) + (y / 8 - 512 * (ly_stk_lo lyc / 4096))) with (SHADOW_OFF + y / 8) in Hy' by lia.
  apply Hy'. lia. }
split.
- intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr. apply Hz'. lia.
- intros s Hs. unfold shadow_addr in Hs. change SHADOW_OFF with 2147450880 in Hs.
  pose proof (Z.div_mod d 8 ltac:(lia)) as Q1. pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as P1.
  pose proof (Z.div_mod (d + n - 1) 8 ltac:(lia)) as Q2. pose proof (Z.mod_pos_bound (d + n - 1) 8 ltac:(lia)) as P2.
  pose proof (Z.div_mod (2147450880 + d / 8) 8 ltac:(lia)) as Q3. pose proof (Z.mod_pos_bound (2147450880 + d / 8) 8 ltac:(lia)) as P3.
  pose proof (Z.div_mod (2147450880 + (d + n - 1) / 8) 8 ltac:(lia)) as Q4.
  pose proof (Z.mod_pos_bound (2147450880 + (d + n - 1) / 8) 8 ltac:(lia)) as P4.
  assert (Hy : ly_stk_lo lyc <= 8 * (s - 2147450880) < ly_stk_hi lyc) by lia.
  pose proof (Hz' _ Hy) as Hs'.
  replace (SHADOW_OFF + 8 * (s - 2147450880) / 8) with s in Hs'
    by (rewrite Z.mul_comm, Z.div_mul by lia; change SHADOW_OFF with 2147450880; lia).
  rewrite Hs'. discriminate.
Qed.
(* ---- The walk's tactics ---- *)
(* the window of a run's region lies in the zone Zs (kept_of_frame's premise) *)
Ltac rbn_win dummy :=
  let bb0 := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros bb0 wlo whi x Hin Hr; vm_compute in Hin;
  repeat (destruct Hin as [Hin | Hin];
    [ injection Hin as <- <- <-; cbn [base_val] in Hr;
      repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hr end;
      hnf; lia
    | ]);
  try destruct Hin.
(* a region's field after a run *)
Ltac rbn_fld HR nb vb od w v :=
  eapply (field_of_region _ _ nb vb _ _ _ _ _ od w _ v HR);
  [ assumption
  | repeat first [left; reflexivity | right]
  | cbn [sv_denot];
    first [ reflexivity
          | match goal with Ei : ew _ ?i = Z_to_bv 64 _ |- context [ew _ ?i] => rewrite Ei end;
            rewrite ?unsigned_lit_small by lia; rewrite ?Z.add_0_r; reflexivity ]
  | zside | zside ].

(* the write rights of the C5 -> C6 runs: the window (awr case 1), the frame byte and its shadow (case 4) *)
Ltac rbn_awr56 c n U9 U33 U18 EFa EFS :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 c - x_sp0 c));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (x_NM c + n));
    [ reflexivity | exact U33
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3) with 512; lia
    | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (x_FS c));
    [ reflexivity | exact U18
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3 / 8) with 64;
      unfold shadow_addr; change SHADOW_OFF with 2147450880; rewrite EFS in Ha; lia
    | ] ].

(* ---- C5 -> C6 (0x8316c .. 0x831c8) ---- *)
(* The state at 0x8316c (offset 0x3f8): atom 32 = nb.n = |nmc|, atom 33 = NM + |nmc| (the address
   0x83184 computes); the regions: nb.n (read at 0x8316c, 0x831b4), tb.p / tb.cap (written at 0x8319c / 0x831a0),
   nm's NUL (0x8318c) and tk's three scope bytes (0x83190 .. 0x83198). No instrumented check: the token engine
   is not used, Bspan is empty. *)
Definition rbn_rs56 : smem :=
  [ YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 120 136 120 136 [];
    YP09.mkRegion (Some 33%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 18%nat) 16 19 16 19 [] ].
Definition rbn_G56 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0);
           (19%nat, mkAF 4096 (2 ^ 47) 0); (27%nat, mkAF 4096 (2 ^ 47) 0);
           (18%nat, mkAF SB (SB + 2 ^ 44) 0);
           (32%nat, mkAF 0 23 0); (33%nat, mkAF 4096 (2 ^ 47) 0)] []
          [(SAlu ALU_ADD (SOff 27 0) (SOff 32 0), SOff 33 0)].
(* 10744 = AF_reac_box_name + 0x3f8 *)
Definition rbn_ss56 : sstate := mkSS 10744 sr_atoms rbn_rs56 None rbn_G56.
Definition rbn_Bx0 : sv := SLit SB.
(* the bytes the two runs before the memset write *)
Definition rbn_zr56 (c : rbx) (a : Z) : Prop :=
  (x_s1 c + 120 <= a < x_s1 c + 136) \/ a = x_NM c + Z.of_nat (length (x_nmc c)) \/ (x_FS c + 16 <= a < x_FS c + 19).
Definition rbn_Bsp0 : Z * Z := (0, 0).
Lemma rbn_seg_c5_c6 : forall c lyc Sc memc mdc regs,
  rbn_C5 B G c lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x3f8)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x454)) mem' (seg_rom SEGS)) md' /\
       rbn_C6 B G c 0 lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs HC.
pose proof HC as (HL & HW4 & HSCO & HNB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (rbn_s1_mod16 c Hal) as Hs16.
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HL as (HCORE & _ & _ & _ & R22).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HW4 as (_ & _ & R27).
pose proof HNB as (_ & _ & Vn & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (_ & C2 & C3 & C4 & C5).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (ENM : x_NM c = x_F c + 64) by reflexivity.
assert (DSF : x_FS c + 64 <= x_F c \/ x_F c + 512 <= x_FS c).
{ destruct (Z_le_gt_dec (x_FS c + 64) (x_F c)) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (x_F c + 512) (x_FS c)) as [Y|Y]; [right; exact Y|]. exfalso.
  apply (fshadow_not_app (x_F c) 64 (x_F c) 512 (Z.max (x_F c) (x_FS c))); [lia | lia | exact HFapp | lia | lia]. }
assert (ETK : x_TK c = x_F c + 128) by reflexivity.
set (n := Z.of_nat (length (x_nmc c))) in *.
assert (Hn' : 1 <= n <= 23) by (subst n; lia).
destruct (al_frames _ _ LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (_ & _ & HFb & HFs).
rewrite EFa in HFb, HFs. change (fs_frame_bytes 3) with 512 in HFb, HFs. change (512 / 8) with 64 in HFs.
remember (Eimg (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 (x_NM c + n)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 (x_NM c + n)]) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 n; Z_to_bv 64 (x_NM c + n)]) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 (x_FS c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (x_F c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E27 : ew E 27 = Z_to_bv 64 (x_NM c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x_NM c + n)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U2 : bv_unsigned (ew E 2) = x_s1 c) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = x_FS c) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = x_F c) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = x_NM c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = x_NM c + n) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rbn_ss56
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + 10744)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ss56. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn_rs56. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_s1 c) 168 8 (SOff 32 0) n);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold x_mem_at, x_nb in Vn. replace (x_s1 c + 168) with (x_s1 c + 152 + 16) by lia. exact Vn.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFb (x_NM c + n + o) ltac:(lia))).
    + rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (x_FS c + o) with (shadow_addr (x_F c) + o) by (unfold shadow_addr, x_FS; reflexivity).
      apply (proj1 (HFs o ltac:(lia))).
  - apply pairwise_disjoint_of_extents. unfold rbn_rs56, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - unfold facts_ok, rbn_G56. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U19, U27, U18, U32, U33.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 27 (x_NM c) E27), (U_atom E 32 n E32), (U_atom E 33 (x_NM c + n) E33) by lia.
      unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity. }
clear HE EL.
assert (SHOK : sh_ok SEGS rbn_Bx0 [] E (mrestrict (w_H (x_W c)) memc)) by constructor.
replace (BASE + AF_reac_box_name + 0x3f8) with (BASE + 10744) by (unfold AF_reac_box_name; lia).
replace (BASE + AF_reac_box_name + 0x454) with (BASE + 10836) by (unfold AF_reac_box_name; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 10744)) memc (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK rbn_Bsp0; [rbn_awr56 c n U9 U33 U18 EFa EFS |].
rename ms into ms1, HFr into HFr1. clear HF HG HEI0.
(* 0x8317c: NM + n does not wrap *)
psrr_branch_tok RUN BR HS SHOK rbn_Bsp0.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom E 27 (x_NM c) E27), U_SLit, (U_atom E 32 n E32) in Hc by lia.
  replace (zcanon (-1)) with (2 ^ 64 - 1) in Hc by (vm_compute; reflexivity).
  rewrite lxor_allones in Hc by lia. rewrite zcanon_id in Hc by (unfold M64; lia).
  destruct (Z.ltb_spec (2 ^ 64 - 1 - x_NM c) n); [lia | discriminate Hc]. }
paj_run_tok RUN HS HJ SHOK rbn_Bsp0; [rbn_awr56 c n U9 U33 U18 EFa EFS |].
rename ms into ms2, HFr into HFr2. clear HF HG HEI0.
(* the fields the run wrote *)
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HR2. cbn [restrict ms_mem] in HR2.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HR3. cbn [restrict ms_mem] in HR3.
assert (VTp : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_s1 c + 120) 8 (x_F c + 128))
  by (rbn_fld HR1 9%nat (x_s1 c) 120 8%N (x_F c + 128)).
assert (VTc : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_s1 c + 128) 8 24)
  by (rbn_fld HR1 9%nat (x_s1 c) 128 8%N 24).
assert (VNul : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_NM c + n + 0) 1 0)
  by (rbn_fld HR2 33%nat (x_NM c + n) 0 1%N 0).
assert (VS16 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 16) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 16 1%N 0).
assert (VS17 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 17) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 17 1%N 0).
assert (VS18 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 18) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 18 1%N 0).
clear HR1 HR2 HR3.
(* ---- 0x831b0: memset(s1 + 136, 0, 16) ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
rewrite U9 in Ra0. rewrite E2 in Rsp. rewrite E3 in Rgp. rewrite E4 in Rtp.
pose proof (rbn_stack_shadow lyc Sc (x_W c) (ms_mem ms2) _ (x_s1 c + 136) 16 (proj1 HJ) ltac:(lia) ltac:(lia) ltac:(lia))
  as (MRA & MHV).
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET (x_W c) (ms_regs ms2) (ms_mem ms2)
    (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] lyc Sc _ 0
    (x_s1 c + 136) 0 16 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + 10816)) HJ).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rsp, unsigned_lit_small by lia. lia.
  - exact Hs16.
  - lia.
  - lia.
  - rewrite Rgp. exact R3.
  - rewrite Rtp. exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [left; lia | lia].
  - unfold amem_range. right. lia.
  - exact MRA.
  - intros _. exact MHV.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2 & Hsame).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9; intros a Ha; [|lia].
  apply (mbyte_of_aview SEGS). apply Hout; lia. }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
(* what the two runs and the memset kept *)
assert (K1 : mkeep (x_W c) memc (ms_mem ms1) (rbn_zr56 c)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) memc (ms_mem ms1) (rbn_zr56 c) HFr1 _ a Ha Hz).
  rbn_win idtac. }
assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (rbn_zr56 c)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (rbn_zr56 c) HFr2 _ a Ha Hz).
  rbn_win idtac. }
assert (K3 : mkeep (x_W c) (ms_mem ms2) mem2 (fun a => (x_s1 c + 136 <= a < x_s1 c + 152) \/ (x_s1 c - 4096 <= a < x_s1 c))).
{ intros a Ha Hz. apply Hout; [exact Ha | intros h; apply Hz; left; lia | intros h; apply Hz; right; lia]. }
clear Hc HJ SHOK HFr1 HFr2 Hout HS HP2 Hsame Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 MRA MHV.
(* ---- 0x831b4 .. 0x831c8 ---- *)
assert (HEI2 : img_env VAL A_LIM (havoc E 512 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (SHOK2 : sh_ok SEGS rbn_Bx0 [] (havoc E 512 (map (getr regs2) CLOB)) (mrestrict (w_H (x_W c)) mem2)) by constructor.
assert (F32 : ew (havoc E 512 (map (getr regs2) CLOB)) 32 = Z_to_bv 64 n) by (rewrite ew_havoc_old by lia; exact E32).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 10816)) mem2 (seg_rom SEGS))) in HJ2.
paj_run_to_tok RUNTO HS2 HJ2 SHOK2 rbn_Bsp0 10836; [rbn_awr56 c n U9 U33 U18 EFa EFS |].
rename ms into ms3, HFr into HFr3. clear HF HG.
rename HS2 into HS, HJ2 into HJ, SHOK2 into SHOK.
(* 0x831b8: nb.n = |nmc| is not 0 *)
psrr_branch_tok RUN BR HS SHOK rbn_Bsp0.
{ exfalso. rewrite branch_eq_U, U_SLit, (U_atom _ 32 n F32) in Hc by lia. change (zcanon 0) with 0 in Hc.
  apply Z.eqb_eq in Hc. lia. }
paj_run_to_tok RUNTO HS HJ SHOK rbn_Bsp0 10836; [rbn_awr56 c n U9 U33 U18 EFa EFS |].
rename ms into ms4, HFr into HFr4. clear HF HG.
assert (K4 : mkeep (x_W c) mem2 (ms_mem ms3) (fun _ => False)).
{ intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) mem2 (ms_mem ms3) (fun _ => False) HFr3 _ a Ha Hz).
  rbn_win idtac. }
assert (K5 : mkeep (x_W c) (ms_mem ms3) (ms_mem ms4) (fun _ => False)).
{ intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) (ms_mem ms3) (ms_mem ms4) (fun _ => False) HFr4 _ a Ha Hz).
  rbn_win idtac. }
clear HFr3 HFr4.
assert (K35 : mkeep (x_W c) (ms_mem ms2) (ms_mem ms4) (fun a => (x_s1 c + 136 <= a < x_s1 c + 152) \/ (x_s1 c - 4096 <= a < x_s1 c))).
{ intros a Ha Hz. rewrite (K5 a Ha (fun h => h)), (K4 a Ha (fun h => h)). exact (K3 a Ha Hz). }
(* ---- the state at 0x831c8 is rbn_C6 c 0 ---- *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;22;23;27]%bv HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
prreg HS (25%bv : bv 5) R25f. prreg HS (21%bv : bv 5) R21f. prreg HS (26%bv : bv 5) R26f.
prreg HS (24%bv : bv 5) R24f. prreg HS (20%bv : bv 5) R20f.
rewrite U19 in R25f.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists lyc, Sc, (ms_regs ms4), (ms_mem ms4), (with_vm_backing (m_vm_lazy md2) mat md2). split; [reflexivity|].
unfold n in *.
apply (rbn_C6_of_C5 c lyc Sc memc mdc regs (ms_mem ms4) _ (ms_regs ms4) HC HJ).
- intros a Ha Hz. unfold rbn_z56 in Hz. change SB_CH_STK with 4112 in Hz.
  rewrite (K35 a Ha) by lia. rewrite (K2 a Ha) by (unfold rbn_zr56; lia). rewrite (K1 a Ha) by (unfold rbn_zr56; lia).
  reflexivity.
- unfold x_mem_at. rewrite ETK. apply (mkeep_val _ _ _ _ _ 8 _ K35); [lia | lia | intros x Hx; lia | exact VTp].
- unfold x_mem_at. apply (mkeep_val _ _ _ _ _ 8 _ K35); [lia | lia | intros x Hx; lia | exact VTc].
- intros i Hi. rewrite (K5 (x_s1 c + 136 + i) ltac:(lia) (fun h => h)), (K4 (x_s1 c + 136 + i) ltac:(lia) (fun h => h)), Heff by lia.
  reflexivity.
- rewrite (K35 (x_NM c + Z.of_nat (length (x_nmc c))) ltac:(lia)) by lia. apply (aview_of_val_mem1 SEGS); [rewrite Z.add_0_r in VNul; exact VNul | lia].
- intros j Hj. rewrite (K35 (x_FS c + j) ltac:(lia)) by lia. apply (aview_of_val_mem1 SEGS); [|lia].
  assert (j = 16 \/ j = 17 \/ j = 18) as [-> | [-> | ->]] by lia; assumption.
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- rewrite R25f, ETK. reflexivity.
- exact R21f.
- exact R26f.
- exact R24f.
- exact R20f.
Qed.
(* ---- The token loop (0x831c8 .. 0x8322c) ---- *)
(* The state at 0x83214 (offset 0x4a0), after one char of the loop: the loop registers of C6 with the char i
   consumed (s5 still i, s10 the seen flag after it), tb the token of the first i + 1 chars. *)
Definition rbn_T (c : rbx) (i : Z) (lyc : alayout) (Sc : astate) (mem : word -> option byte) (md : Model)
  (regs : bvmap 5 word) : Prop :=
  rbn_live B G c lyc Sc mem md regs /\ rbn_w4done c mem regs /\ rbn_nmdone c mem regs /\
  0 <= i < Z.of_nat (length (x_nmc c)) /\
  getr regs 21 = w64 i /\
  getr regs 26 = w64 (if existsb (fun x => x =? 45) (firstn (Z.to_nat (i + 1)) (x_nmc c)) then 1 else 0) /\
  getr regs 24 = w64 45 /\ getr regs 20 = w64 24 /\
  rbn_scope c mem 5 0 0 0xf8 /\
  rbn_sb c mem (x_tb c) (x_TK c) 24 (fst (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c))))
    (snd (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c)))).
(* The bytes one char of the loop may write: sb_ch's stack and tb's n / over and one byte of tk. *)
Definition rbn_ztk (c : rbx) (a : Z) : Prop :=
  (x_s1 c - SB_CH_STK <= a < x_s1 c) \/ (x_s1 c + 136 <= a < x_s1 c + 148) \/ (x_TK c <= a < x_TK c + 24).
Lemma rbn_T_of_C6 : forall c i lyc Sc memc mdc regs mF mdF (regsF : bvmap 5 word),
  rbn_C6 B G c i lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mF mdF 0 ->
  rkeep c memc mF (rbn_ztk c) ->
  rbn_sb c mF (x_tb c) (x_TK c) 24 (fst (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c))))
    (snd (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c)))) ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 22 = getr regs 22 -> getr regsF 23 = getr regs 23 ->
  getr regsF 25 = getr regs 25 -> getr regsF 27 = getr regs 27 ->
  getr regsF 21 = w64 i ->
  getr regsF 26 = w64 (if existsb (fun x => x =? 45) (firstn (Z.to_nat (i + 1)) (x_nmc c)) then 1 else 0) ->
  getr regsF 24 = w64 45 -> getr regsF 20 = w64 24 ->
  rbn_T c i lyc Sc mF mdF regsF.
Proof.
intros c i lyc Sc memc mdc regs mF mdF regsF (HL & HW4 & HNM & Hi & _ & _ & _ & _ & HSCO & _) HJF HK HTB
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q25 Q27 R21 R26 R24 R20.
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (proj1 HL) as (_ & _ & HPERM & _).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (HZ : forall a, rbn_ztk c a -> (x_s1 c - 4112 <= a < x_s1 c) \/ (x_s1 c + 136 <= a < x_s1 c + 148) \/
   (x_F c + 128 <= a < x_F c + 152)).
{ intros a Ha. unfold rbn_ztk, x_TK in Ha. change SB_CH_STK with 4112 in Ha. lia. }
assert (NZf : forall x, x_F c <= x < x_F c + 128 \/ x_F c + 152 <= x < x_F c + 512 -> ~ rbn_ztk c x).
{ intros x Hx Hz. apply HZ in Hz. lia. }
assert (NZs : forall x, x_FS c <= x < x_FS c + 64 -> ~ rbn_ztk c x).
{ intros x Hx Hz. apply HZ in Hz. rewrite EFS in Hx.
  destruct Hz as [Hz|[Hz|Hz]]; [lia | lia |].
  exact (fshadow_not_app (x_F c) 64 (x_F c) 512 x ltac:(lia) ltac:(lia) HFapp ltac:(lia) ltac:(lia)). }
assert (NZw : forall x, x_s1 c + 152 <= x < x_sp0 c -> ~ rbn_ztk c x).
{ intros x Hx Hz. apply HZ in Hz. lia. }
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]].
- apply (rbn_live_rkeep c lyc Sc memc mdc regs lyc Sc mF mdF regsF HL HJF HPERM); try assumption.
  apply (rkeep_mono _ _ _ _ _ HK). intros a Ha. apply HZ in Ha. unfold rbn_zone. rewrite EFS.
  change SB_CH_STK with 4112. lia.
- destruct HW4 as (HWB & HGW & R27). split; [|split; [|rewrite Q27; exact R27]].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _).
    apply (rbn_sb_rkeep c memc mF (rbn_ztk c) _ _ _ _ _ HK); unfold x_wb, x_W4 in *;
      [lia | lia | lia | lia | intros x Hx; split; [left; lia | apply NZw; lia]
      | intros x Hx; split; [right; left; lia | apply NZf; lia] | exact HWB].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _). unfold x_mem_at, x_W4 in *.
    apply (rkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx; split; [right; left; lia | apply NZf; lia] | exact HGW].
- destruct HNM as (HNB & HGN & R25). split; [|split; [|rewrite Q25; exact R25]].
  + apply (rbn_sb_rkeep c memc mF (rbn_ztk c) _ _ _ _ _ HK); unfold x_nb, x_NM in *;
      [lia | lia | lia | lia | intros x Hx; split; [left; lia | apply NZw; lia]
      | intros x Hx; split; [right; left; lia | apply NZf; lia] | exact HNB].
  + unfold x_mem_at, x_NM in *.
    apply (rkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx; split; [right; left; lia | apply NZf; lia] | exact HGN].
- exact Hi.
- exact R21.
- exact R26.
- exact R24.
- exact R20.
- destruct HSCO as (S4 & S8 & S16 & S24). unfold rbn_scope. cbv zeta.
  split; [rewrite (HK (x_FS c + 4)); [exact S4 | lia | right; right; left; lia | apply NZs; lia]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S8 j Hj) | lia | right; right; left; lia | apply NZs; lia]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S16 j Hj) | lia | right; right; left; lia | apply NZs; lia]|].
  intros j Hj; rewrite (HK (x_FS c + j)); [exact (S24 j Hj) | lia | right; right; left; lia | apply NZs; lia].
- exact HTB.
Qed.
(* The loop's back edge (0x8321c): with nothing written, the state at 0x83214 is C6 (i + 1) or C7. *)
Lemma rbn_next_of_T : forall c i lyc Sc memc mdc regs mF mdF (regsF : bvmap 5 word),
  rbn_T c i lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mF mdF 0 ->
  mkeep (x_W c) memc mF (fun _ => False) ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 20 = getr regs 20 -> getr regsF 22 = getr regs 22 ->
  getr regsF 23 = getr regs 23 -> getr regsF 24 = getr regs 24 -> getr regsF 25 = getr regs 25 ->
  getr regsF 26 = getr regs 26 -> getr regsF 27 = getr regs 27 ->
  getr regsF 21 = w64 (i + 1) ->
  (i + 1 < Z.of_nat (length (x_nmc c)) -> rbn_C6 B G c (i + 1) lyc Sc mF mdF regsF) /\
  (Z.of_nat (length (x_nmc c)) <= i + 1 -> rbn_C7 B G c lyc Sc mF mdF regsF).
Proof.
intros c i lyc Sc memc mdc regs mF mdF regsF (HL & HW4 & HNM & Hi & R21 & R26 & R24 & R20 & HSCO & HTB) HJF HK
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q22 Q23 Q24 Q25 Q26 Q27 R21F.
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (proj1 HL) as (_ & _ & HPERM & _).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (L : rbn_live B G c lyc Sc mF mdF regsF).
{ apply (rbn_live_keep c lyc Sc memc mdc regs lyc Sc mF mdF regsF HL HJF HPERM); try assumption.
  apply (mkeep_mono _ _ _ _ _ HK). intros a []. }
assert (W4 : rbn_w4done c mF regsF).
{ destruct HW4 as (HWB & HGW & R27). split; [|split; [|rewrite Q27; exact R27]].
  - pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _).
    apply (rbn_sb_keep c memc mF (fun _ => False) _ _ _ _ _ HK); unfold x_wb, x_W4 in *;
      [lia | lia | lia | lia | intros x Hx [] | intros x Hx [] | exact HWB].
  - pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _). unfold x_mem_at, x_W4 in *.
    apply (mkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx [] | exact HGW]. }
assert (NM : rbn_nmdone c mF regsF).
{ destruct HNM as (HNB & HGN & R25). split; [|split; [|rewrite Q25; exact R25]].
  - pose proof HNB as (_ & _ & _ & _ & _ & Hln & _).
    apply (rbn_sb_keep c memc mF (fun _ => False) _ _ _ _ _ HK); unfold x_nb, x_NM in *;
      [lia | lia | lia | lia | intros x Hx [] | intros x Hx [] | exact HNB].
  - unfold x_mem_at, x_NM in *.
    apply (mkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx [] | exact HGN]. }
assert (SC : rbn_scope c mF 5 0 0 0xf8).
{ destruct HSCO as (S4 & S8 & S16 & S24). unfold rbn_scope. cbv zeta.
  split; [rewrite (HK (x_FS c + 4)); [exact S4 | lia | intros []]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S8 j Hj) | lia | intros []]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S16 j Hj) | lia | intros []]|].
  intros j Hj; rewrite (HK (x_FS c + j)); [exact (S24 j Hj) | lia | intros []]. }
assert (TB : rbn_sb c mF (x_tb c) (x_TK c) 24 (fst (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c))))
    (snd (rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c))))).
{ pose proof HTB as (_ & _ & _ & _ & _ & Hlt & _).
  apply (rbn_sb_keep c memc mF (fun _ => False) _ _ _ _ _ HK); unfold x_tb, x_TK in *;
    [lia | lia | lia | lia | intros x Hx [] | intros x Hx [] | exact HTB]. }
split.
- intros Hlt. split; [exact L|]. split; [exact W4|]. split; [exact NM|]. split; [lia|].
  split; [exact R21F|]. split; [rewrite Q26; exact R26|]. split; [rewrite Q24; exact R24|].
  split; [rewrite Q20; exact R20|]. split; [exact SC | exact TB].
- intros Hge. rewrite (firstn_all2 (x_nmc c)) in TB by lia.
  split; [exact L|]. split; [exact W4|]. split; [exact NM|]. split; [exact SC | exact TB].
Qed.
(* write rights of a run that writes nothing *)
Ltac rbn_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first [ apply awr_ok_nil | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |] ].
(* a register the run left as it was *)
Ltac rbn_kr HKR := apply HKR; repeat first [left; reflexivity | right].
(* The state at 0x83214 (offset 0x4a0 = 10912): nb.n read again (atom 32 = |nmc|), then the back edge. *)
Definition rbn_rsT : smem := [ YP09.mkRegion (Some 9%nat) 168 176 0 0 [YP09.mkChunk 168 (CVal 8 (SOff 32 0))] ].
Definition rbn_GT : facts := mkFacts [(21%nat, mkAF 0 22 0); (32%nat, mkAF 1 23 0)] [] [].
Definition rbn_ssT : sstate := mkSS 10912 sr_atoms rbn_rsT None rbn_GT.
Lemma rbn_tok_tail : forall c i lyc Sc memc mdc regs,
  rbn_T c i lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + 10912)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 10836)) mem' (seg_rom SEGS)) md' /\
        i + 1 < Z.of_nat (length (x_nmc c)) /\ rbn_C6 B G c (i + 1) lyc' Sc' mem' md' regs') \/
       (c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 10940)) mem' (seg_rom SEGS)) md' /\
        rbn_C7 B G c lyc' Sc' mem' md' regs')).
Proof.
intros c i lyc Sc memc mdc regs HT.
pose proof HT as (HL & HW4 & HNM & Hi & R21 & R26 & R24 & R20 & HSCO & HTB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HL as (HCORE & _).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HNM as ((_ & _ & Vn & _) & _ & _).
set (n := Z.of_nat (length (x_nmc c))) in *.
assert (Hn' : 1 <= n <= 23) by (subst n; lia).
remember (Eimg (Ereg regs [Z_to_bv 64 n])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall k, (k < A_TEXT)%nat -> ew E k = ew (Ereg regs [Z_to_bv 64 n]) k)
  by (intros k Hk; subst E; apply Eimg_low; exact Hk).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 n]) E)
  by (split; [intros k Hk; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E32 : ew E 32 = Z_to_bv 64 n) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = i) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rbn_ssT
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + 10912)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ssT. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn_rsT. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (x_s1 c) 168 8 (SOff 32 0) n);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    unfold x_mem_at, x_nb in Vn. replace (x_s1 c + 168) with (x_s1 c + 152 + 16) by lia. exact Vn.
  - apply pairwise_disjoint_of_extents. unfold rbn_rsT, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok, rbn_GT. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U21, U32.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
clear HE EL.
assert (SHOK : sh_ok SEGS rbn_Bx0 [] E (mrestrict (w_H (x_W c)) memc)) by constructor.
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 10912)) memc (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK rbn_Bsp0; [rbn_awr_ro |].
rename ms into ms1, HFr into HFr1. clear HF HG.
assert (K1 : mkeep (x_W c) memc (ms_mem ms1) (fun _ => False)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) memc (ms_mem ms1) (fun _ => False) HFr1 _ a Ha Hz).
  rbn_win idtac. }
clear HFr1.
(* 0x8321c: i + 1 < |nmc| ? *)
psrr_branch_tok RUN BR HS SHOK rbn_Bsp0.
- rewrite branch_ltu_U, (U_atom_off E 21 i 1 E21), (U_atom E 32 n E32) in Hc by lia. apply Z.ltb_lt in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rbn_Bsp0 10836; [rbn_awr_ro |].
  rename ms into ms2, HFr into HFr2. clear HF HG.
  assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (fun _ => False)).
  { intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr2 _ a Ha Hz).
    rbn_win idtac. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;20;22;23;24;25;26;27]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (21%bv : bv 5) R21f. rewrite U21 in R21f.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  do 5 eexists. left. split; [reflexivity|]. split; [exact Hc|].
  refine (proj1 (rbn_next_of_T c i lyc Sc memc mdc regs (ms_mem ms2) _ (ms_regs ms2) HT HJ
    (fun a Ha Hz => eq_trans (K2 a Ha Hz) (K1 a Ha Hz)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ R21f) Hc);
    rbn_kr HKR.
- rewrite branch_ltu_U, (U_atom_off E 21 i 1 E21), (U_atom E 32 n E32) in Hc by lia. apply Z.ltb_ge in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rbn_Bsp0 10940; [rbn_awr_ro |].
  rename ms into ms2, HFr into HFr2. clear HF HG.
  assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (fun _ => False)).
  { intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr2 _ a Ha Hz).
    rbn_win idtac. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;20;22;23;24;25;26;27]%bv HS
    ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
  cbn [ms_regs restrict] in HKR.
  prreg HS (21%bv : bv 5) R21f. rewrite U21 in R21f.
  pmkst HS.
  apply SRr_ret. split; [reflexivity|].
  do 5 eexists. right. split; [reflexivity|].
  refine (proj2 (rbn_next_of_T c i lyc Sc memc mdc regs (ms_mem ms2) _ (ms_regs ms2) HT HJ
    (fun a Ha Hz => eq_trans (K2 a Ha Hz) (K1 a Ha Hz)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ R21f) Hc);
    rbn_kr HKR.
Qed.
(* ---- One char of the token loop that calls sb_ch(tb, bn_low' c) (0x83210) ---- *)
Lemma div8_add : forall F t, F mod 8 = 0 -> (F + t) / 8 = F / 8 + t / 8.
Proof.
intros F t H. pose proof (Z.div_mod F 8 ltac:(lia)) as D. rewrite H, Z.add_0_r in D.
rewrite D at 1. rewrite (Z.mul_comm 8 (F / 8)), Z.div_add_l by lia. reflexivity.
Qed.
Lemma all256 : forall (P : Z -> bool), forallb P (map Z.of_nat (seq 0 256)) = true -> forall x, 0 <= x < 256 -> P x = true.
Proof.
intros P H x Hx. rewrite forallb_forall in H. apply H. apply in_map_iff. exists (Z.to_nat x). split; [lia|].
apply in_seq. lia.
Qed.
(* the listing's lower-casing 0x831f4 .. 0x83208 on a byte held in atom m is bn_low' *)
Lemma rbn_low_U : forall E (m : nat) x, ew E m = Z_to_bv 64 x -> 0 <= x < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_ADD (SOff m 0) (SAlu ALU_SLL (SAlu ALU_SLTU (SAlu ALU_AND (SOff m (-65)) (SLit 255))
    (SLit 26)) (SLit 5))) (SLit 255)) = bn_low' x.
Proof.
intros E m x Hm Hx.
rewrite !U_SAlu, !U_SLit, !U_SOff, Hm, unsigned_lit_small by lia. cbn [zalu_raw].
apply Z.eqb_eq. clear Hm. revert x Hx.
apply (all256 (fun x => zcanon (Z.land (zcanon (zcanon (x + 0) + zcanon (Z.shiftl (zcanon (if zcanon (Z.land (zcanon (x + -65))
  (zcanon 255)) <? zcanon 26 then 1 else 0)) (Z.land (zcanon 5) 63)))) (zcanon 255)) =? bn_low' x)).
vm_compute. reflexivity.
Qed.
(* the token of the first k chars has at most k chars *)
Lemma rbn_tok_len : forall (l : list Z) k, (k <= length l)%nat -> (length (fst (rbn_tok (firstn k l))) <= k)%nat.
Proof.
intros l k. induction k as [|k IH]; intros Hk.
- change (firstn 0 l) with (@nil Z). change (rbn_tok []) with (@nil Z, 0). cbn [fst length]. lia.
- rewrite rbn_tok_snoc by lia. pose proof (IH ltac:(lia)) as H. destruct (_ && _); [lia|].
  unfold sbm_ch. destruct (_ <? _); cbn [fst]; [rewrite length_app; cbn [length]|]; lia.
Qed.
Lemma rbn_tok_call : forall c i lyc Sc memc mdc regs (regsT : bvmap 5 word) mT mdT,
  rbn_C6 B G c i lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mT mdT 0 ->
  mkeep (x_W c) memc mT (fun _ => False) ->
  (nth (Z.to_nat i) (x_nmc c) 0 =? 45) && negb (existsb (fun x => x =? 45) (firstn (Z.to_nat i) (x_nmc c))) = false ->
  getr regsT 1 = Z_to_bv 64 (BASE + 10912) ->
  getr regsT 10 = Z_to_bv 64 (x_s1 c + 120) ->
  getr regsT 11 = Z_to_bv 64 (bn_low' (nth (Z.to_nat i) (x_nmc c) 0)) ->
  getr regsT 2 = getr regs 2 -> getr regsT 3 = getr regs 3 -> getr regsT 4 = getr regs 4 ->
  getr regsT 8 = getr regs 8 -> getr regsT 9 = getr regs 9 -> getr regsT 18 = getr regs 18 ->
  getr regsT 19 = getr regs 19 -> getr regsT 20 = getr regs 20 -> getr regsT 21 = getr regs 21 ->
  getr regsT 22 = getr regs 22 -> getr regsT 23 = getr regs 23 -> getr regsT 24 = getr regs 24 ->
  getr regsT 25 = getr regs 25 -> getr regsT 26 = getr regs 26 -> getr regsT 27 = getr regs 27 ->
  SRr SEGS (x_W c) (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_sb_ch)) mT (seg_rom SEGS)) mdT)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 10912)) mem' (seg_rom SEGS)) md' /\ rbn_T c i lyc' Sc' mem' md' regs').
Proof.
intros c i lyc Sc memc mdc regs regsT mT mdT HC HJT HKT Hmod Rra Ra0 Ra1
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27.
pose proof HC as (HL & HW4 & HNM & Hi & R21 & R26 & R24 & R20 & HSCO & HTB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HL as (HCORE & _).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HJT as (HART & HlyT & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresT & _).
pose proof asan_consts as (_ & C2 & C3 & C4 & C5).
pose proof pa_B_ok as HBok. pose proof pa_base_lo as HBlo.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HCS : SB_CH_STK = 4112) by reflexivity.
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (ETK : x_TK c = x_F c + 128) by reflexivity.
assert (F8 : x_F c mod 8 = 0) by (apply mod32_mod8; exact HFal).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
set (k := Z.to_nat i) in *.
assert (Hk : (k < length (x_nmc c))%nat) by (subst k; lia).
set (x := nth k (x_nmc c) 0) in *.
assert (Hx : 0 < x < 256) by (subst x; exact (proj1 (Forall_forall _ _) Hch _ (nth_In _ 0 Hk))).
set (tok := rbn_tok (firstn k (x_nmc c))) in *.
assert (Htl : (length (fst tok) <= k)%nat) by (subst tok; apply rbn_tok_len; lia).
assert (TBT : rbn_sb c mT (x_tb c) (x_TK c) 24 (fst tok) (snd tok)).
{ pose proof HTB as (_ & _ & _ & _ & _ & Hlt & _).
  apply (rbn_sb_keep c memc mT (fun _ => False) _ _ _ _ _ HKT); unfold x_tb, x_TK in *;
    [lia | lia | lia | lia | intros y Hy [] | intros y Hy [] | exact HTB]. }
destruct TBT as (Vp & Vcap & Vn & Vov & Hov & Hlen & Hfa & HG).
unfold x_mem_at in Vp, Vcap, Vn, Vov, HG.
set (nT := Z.of_nat (length (fst tok))) in *.
assert (HnT : 0 <= nT <= 22) by (subst nT; lia).
assert (Hmodel : rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c)) = sbm_ch 24 tok (bn_low' x)).
{ replace (Z.to_nat (i + 1)) with (S k) by lia. rewrite rbn_tok_snoc by lia. fold x. rewrite Hmod. reflexivity. }
assert (Hseen : existsb (fun y => y =? 45) (firstn (Z.to_nat (i + 1)) (x_nmc c)) =
                existsb (fun y => y =? 45) (firstn k (x_nmc c))).
{ replace (Z.to_nat (i + 1)) with (S k) by lia. rewrite (box_name_lemmas.bl_firstn_snoc _ k 0) by lia.
  rewrite existsb_app. cbn [existsb]. fold x.
  destruct (x =? 45); destruct (existsb _ (firstn k _)); cbn in Hmod |- *; first [reflexivity | discriminate]. }
assert (Hsp : spZ regsT = x_s1 c) by (unfold spZ; rewrite Q2, R2; apply unsigned_lit_small; lia).
(* the scope of tk at mT: the shadow of TK + nT is 0 *)
destruct HSCO as (S4 & S8 & S16 & S24).
assert (RAp : range_addressable (aview SEGS (w_H (x_W c)) mT) SHADOW_OFF (x_TK c + nT) 1).
{ intros y Hy. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
  replace y with (x_TK c + nT) by lia. rewrite ETK, <- Z.add_assoc, div8_add by exact F8.
  replace (128 + nT) with (nT + 16 * 8) by lia. rewrite Z.div_add by lia.
  pose proof (Z.div_pos nT 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono nT 22 8 ltac:(lia) ltac:(lia)).
  change (22 / 8) with 2 in *.
  rewrite (HKT (SHADOW_OFF + (x_F c / 8 + (nT / 8 + 16)))); [|change SHADOW_OFF with 2147450880; lia | intros []].
  replace (SHADOW_OFF + (x_F c / 8 + (nT / 8 + 16))) with (x_FS c + (16 + nT / 8)) by (unfold x_FS; lia).
  apply S16. lia. }
pose proof (rbn_stack_shadow lyc Sc (x_W c) mT _ (x_s1 c + 120) 28 HART ltac:(lia) ltac:(lia) ltac:(lia)) as (RAb & _).
destruct (al_frames _ _ LAWS lyc Sc (x_W c) mT mdT 3 (x_fpos c) HART HinF) as (_ & _ & HFb & _).
rewrite EFa in HFb. change (fs_frame_bytes 3) with 512 in HFb.
eapply SRr_bind.
{ change (mkCfg (mkst regsT (Z_to_bv 64 (BASE + AF_sb_ch)) mT (seg_rom SEGS)) mdT) with (cfg_at SEGS A_sb_ch regsT mT mdT).
  apply (HSC (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)]
    lyc Sc (x_W c) mT mdT 0 regsT (x_s1 c + 120) (bn_low' x) (x_TK c) 24 nT (snd tok) HJT).
  - rewrite Rra. apply ret_ok_codeptr_v; [lia | reflexivity].
  - unfold raZ. rewrite Rra, unsigned_lit_small by lia. lia.
  - rewrite Q3. exact R3.
  - rewrite Q4. exact R4.
  - rewrite Hsp. pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1al, Z.add_0_r in D.
    rewrite D. replace (32 * (x_s1 c / 32)) with ((2 * (x_s1 c / 32)) * 16) by lia. apply Z_mod_mult.
  - rewrite Hsp. lia.
  - rewrite Hsp. lia.
  - exact Ra0.
  - exact Ra1.
  - unfold bn_low'. apply Z.mod_pos_bound. lia.
  - pose proof (Z.div_mod (x_s1 c) 32 ltac:(lia)) as D. rewrite Hs1al, Z.add_0_r in D.
    rewrite D. replace (32 * (x_s1 c / 32) + 120) with ((4 * (x_s1 c / 32) + 15) * 8) by lia. apply Z_mod_mult.
  - lia.
  - lia.
  - left. rewrite Hsp. lia.
  - right. lia.
  - unfold x_tb in Vp. exact Vp.
  - unfold x_tb in Vcap. exact Vcap.
  - unfold x_tb in Vn. exact Vn.
  - unfold x_tb in Vov. exact Vov.
  - unfold x_TK. lia.
  - lia.
  - lia.
  - lia.
  - destruct Hov as [-> | ->]; lia.
  - exact RAb.
  - intros a Ha. split; [left; lia|]. split; [apply HpresT; lia|].
    split; [apply (al_stack _ _ LAWS _ _ _ _ _ a HART); lia|]. rewrite Hsp, Hes. lia.
  - intros _. split; [unfold x_TK; lia|]. split; [unfold x_TK; lia|].
    split; [intros a Ha; right; exists 3, (x_fpos c); split; [exact HinF|];
            unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3) with 512; unfold x_TK in Ha; lia|].
    split; [exact RAp|].
    split; [intros a Ha; split; [right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
              left; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3) with 512; unfold x_TK in Ha; lia|];
            destruct (HFb a ltac:(unfold x_TK in Ha; lia)) as [Hp Ho]; split; [exact Hp|]; split; [exact Ho|];
            rewrite Hsp, Hes; unfold x_TK in Ha; lia|].
    split; [unfold x_TK; lia | rewrite Hsp; unfold x_TK; lia]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & Vp2 & Vc2 & Hif).
rewrite (proj2 (Z.ltb_lt (nT + 1) 24) ltac:(lia)) in Hif. destruct Hif as (Vn2 & Vov2 & Hgc).
unfold EV_SB_CH in HJ2. rewrite Z.add_0_r in HJ2.
destruct HK2 as (T1 & T2 & T3 & T4 & _).
assert (NE : forall a, ~ rbn_ztk c a -> ~ tsb_ch_wr (x_s1 c + 120) (x_TK c) nT 24 a).
{ intros a Hz [h | (_ & ->)]; apply Hz; unfold rbn_ztk; [right; left; lia | right; right; unfold x_TK in *; lia]. }
apply SRr_ret. split; [reflexivity|]. exists lyc, Sc, regs2, mem2, md2. split; [rewrite Rra; reflexivity|].
apply (rbn_T_of_C6 c i lyc Sc memc mdc regs mem2 md2 regs2 HC HJ2).
- intros a Ha Hcov Hz. rewrite <- (HKT a Ha (fun h => h)).
  destruct Hcov as [Hc1 | [Hc2 | [Hc3 | (q & N & Hin & Hq)]]].
  + apply T1; [lia | rewrite Hsp; intros h; apply Hz; left; exact h | exact (NE a Hz)].
  + apply (T4 3 (x_fpos c) a HinF); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa; exact Hc2 | exact (NE a Hz)].
  + apply (T4 3 (x_fpos c) a HinF); [|exact (NE a Hz)].
    right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite EFa. change (fs_frame_bytes 3 / 8) with 64.
    unfold x_FS in Hc3. exact Hc3.
  + pose proof (T2 q N (a - q) (Permutation_in _ (Permutation_sym HPERM) Hin)) as T2'.
    replace (q + (a - q)) with a in T2' by lia. apply T2'; [|exact (NE a Hz)].
    split; [lia|]. unfold req_size. destruct (Z.eqb_spec N 0); lia.
- rewrite Hmodel. rewrite (surjective_pairing tok). rewrite sbm_ch_room by lia. cbn [fst snd].
  unfold rbn_sb, x_mem_at, x_tb. cbv zeta.
  split; [exact Vp2|]. split; [exact Vc2|].
  split; [rewrite length_app; cbn [length]; rewrite Nat2Z.inj_add; exact Vn2|].
  split; [exact Vov2|]. split; [exact Hov|].
  split; [rewrite length_app; cbn [length]; lia|].
  split; [apply Forall_app; split; [exact Hfa | constructor; [unfold bn_low'; apply Z.mod_pos_bound; lia | constructor]]|].
  apply (proj2 (garr8_app SEGS _ _ _ _)). split.
  + apply (garr8_frame SEGS _ _ _ _ HG). intros a Ha. apply (mbyte_of_aview SEGS).
    apply (T4 3 (x_fpos c) a HinF); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa;
      change (fs_frame_bytes 3) with 512; unfold x_TK in Ha |- *; lia|].
    intros [h | (_ & h)]; [unfold x_TK in Ha; lia | subst nT; lia].
  + exact Hgc.
- exact (eq_trans (HP2 2 ltac:(unfold acallee_saved; lia)) Q2).
- exact (eq_trans (HP2 3 ltac:(unfold acallee_saved; lia)) Q3).
- exact (eq_trans (HP2 4 ltac:(unfold acallee_saved; lia)) Q4).
- exact (eq_trans (HP2 8 ltac:(unfold acallee_saved; lia)) Q8).
- exact (eq_trans (HP2 9 ltac:(unfold acallee_saved; lia)) Q9).
- exact (eq_trans (HP2 18 ltac:(unfold acallee_saved; lia)) Q18).
- exact (eq_trans (HP2 19 ltac:(unfold acallee_saved; lia)) Q19).
- exact (eq_trans (HP2 22 ltac:(unfold acallee_saved; lia)) Q22).
- exact (eq_trans (HP2 23 ltac:(unfold acallee_saved; lia)) Q23).
- exact (eq_trans (HP2 25 ltac:(unfold acallee_saved; lia)) Q25).
- exact (eq_trans (HP2 27 ltac:(unfold acallee_saved; lia)) Q27).
- exact (eq_trans (eq_trans (HP2 21 ltac:(unfold acallee_saved; lia)) Q21) R21).
- rewrite Hseen. exact (eq_trans (eq_trans (HP2 26 ltac:(unfold acallee_saved; lia)) Q26) R26).
- exact (eq_trans (eq_trans (HP2 24 ltac:(unfold acallee_saved; lia)) Q24) R24).
- exact (eq_trans (eq_trans (HP2 20 ltac:(unfold acallee_saved; lia)) Q20) R20).
Qed.
(* One char that is the first '-': no call, s10 := 1 (0x831ec). *)
Lemma rbn_T_skip : forall c i lyc Sc memc mdc regs mF mdF (regsF : bvmap 5 word),
  rbn_C6 B G c i lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mF mdF 0 ->
  mkeep (x_W c) memc mF (fun _ => False) ->
  nth (Z.to_nat i) (x_nmc c) 0 = 45 ->
  existsb (fun x => x =? 45) (firstn (Z.to_nat i) (x_nmc c)) = false ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 20 = getr regs 20 -> getr regsF 21 = getr regs 21 ->
  getr regsF 22 = getr regs 22 -> getr regsF 23 = getr regs 23 -> getr regsF 24 = getr regs 24 ->
  getr regsF 25 = getr regs 25 -> getr regsF 27 = getr regs 27 ->
  getr regsF 26 = w64 1 ->
  rbn_T c i lyc Sc mF mdF regsF.
Proof.
intros c i lyc Sc memc mdc regs mF mdF regsF HC HJF HK Hx Hex
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q27 R26F.
pose proof HC as (HL & HW4 & HNM & Hi & R21 & R26 & R24 & R20 & HSCO & HTB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
assert (HS1 : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
assert (Hmodel : rbn_tok (firstn (Z.to_nat (i + 1)) (x_nmc c)) = rbn_tok (firstn (Z.to_nat i) (x_nmc c))).
{ rewrite HS1, rbn_tok_snoc by lia. rewrite Hx, Hex. reflexivity. }
assert (Hseen : existsb (fun y => y =? 45) (firstn (Z.to_nat (i + 1)) (x_nmc c)) = true).
{ rewrite HS1, (box_name_lemmas.bl_firstn_snoc _ (Z.to_nat i) 0) by lia. rewrite existsb_app, Hx. cbn [existsb].
  apply orb_true_r. }
apply (rbn_T_of_C6 c i lyc Sc memc mdc regs mF mdF regsF HC HJF).
- apply mkeep_rkeep. apply (mkeep_mono _ _ _ _ _ HK). intros a [].
- rewrite Hmodel. pose proof HTB as (_ & _ & _ & _ & _ & Hlt & _).
  apply (rbn_sb_keep c memc mF (fun _ => False) _ _ _ _ _ HK); unfold x_tb, x_TK in *;
    [lia | lia | lia | lia | intros y Hy [] | intros y Hy [] | exact HTB].
- exact Q2. - exact Q3. - exact Q4. - exact Q8. - exact Q9. - exact Q18. - exact Q19. - exact Q22. - exact Q23.
- exact Q25. - exact Q27.
- rewrite Q21. exact R21.
- rewrite Hseen. exact R26F.
- rewrite Q24. exact R24.
- rewrite Q20. exact R20.
Qed.
(* a register of a state, as the symbolic state holds it, without normalising the value *)
Ltac prreg_raw HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* a branch condition in terms of the atoms' values *)
Ltac rbn_Ux H :=
  repeat match type of H with
  | context [U ?Ex (SOff ?i ?c)] =>
      lazymatch goal with Ei : ew ?E0 i = Z_to_bv 64 ?v |- _ =>
        let Xi := fresh "X" in
        assert (Xi : ew Ex i = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb havoc Nat.ltb]; exact Ei);
        rewrite (U_atom_off Ex i v c Xi) in H by lia; clear Xi
      end
  | context [U ?Ex (SLit ?z)] => rewrite (U_SLit Ex z) in H
  end.
(* at the sb_ch call slot of the token loop (0x83210): the call's arguments, then rbn_tok_call *)
Ltac rbn_tok_callstep HC HJ Kmk Hmod HAE U9 E33 x :=
  lazymatch type of HC with rbn_C6 _ _ ?c ?i ?lyc ?Sc ?memc ?mdc ?regs =>
  lazymatch goal with HS : st_ok _ ?Ex _ (restrict _ ?msx) |- _ =>
    pmkst HS; rewrite (PSIG IB_sb_ch AF_sb_ch eq_refl);
    let Rra := fresh "Rra" in let Ra0 := fresh "Ra0" in let Ra1 := fresh "Ra1" in let HKR := fresh "HKR" in
    prreg HS (1%bv : bv 5) Rra; prreg HS (10%bv : bv 5) Ra0; rewrite U9 in Ra0;
    prreg_raw HS (11%bv : bv 5) Ra1;
    let X33 := fresh "X33" in
    assert (X33 : ew Ex 33 = Z_to_bv 64 x) by (cbn [ew ewset Nat.eqb]; exact E33);
    rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot _ _)) in Ra1;
    lazymatch type of Ra1 with _ = Z_to_bv 64 (bv_unsigned (sv_denot ?Ey ?v)) =>
      change (bv_unsigned (sv_denot Ey v)) with (U Ey v) in Ra1 end;
    rewrite (rbn_low_U Ex 33 x X33) in Ra1 by lia;
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ [2;3;4;8;9;18;19;20;21;22;23;24;25;26;27]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR;
    cbn [ms_regs restrict] in HKR;
    apply (rbn_tok_call c i lyc Sc memc mdc regs (ms_regs msx) (ms_mem msx) _ HC HJ Kmk Hmod Rra Ra0 Ra1); rbn_kr HKR
  end end.
(* The state at the head of the loop (0x831c8, offset 0x454 = 10836): atom 32 = NM + i (0x831cc computes it),
   atom 33 = nmc[i]; the read of nm[i] (0x831e0) and its shadow check (0x831d0 .. 0x831dc: the token engine,
   shadow entry for atom 32). *)
Definition rbn_rsB : smem := [ YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))] ].
Definition rbn_GB : facts :=
  mkFacts [(20%nat, mkAF 24 24 0); (21%nat, mkAF 0 22 0); (22%nat, mkAF SB SB 0); (24%nat, mkAF 45 45 0);
           (26%nat, mkAF 0 1 0); (27%nat, mkAF 4096 (2 ^ 47) 0); (32%nat, mkAF 4096 (2 ^ 47 - 4096) 0);
           (33%nat, mkAF 1 255 0)] []
          [(SAlu ALU_ADD (SOff 27 0) (SOff 21 0), SOff 32 0)].
Definition rbn_ssB : sstate := mkSS 10836 sr_atoms rbn_rsB None rbn_GB.
Definition rbn_BxB : sv := SOff 22 0.
Definition rbn_SHB : list shent := [mkSHE 32 0 1].
Lemma rbn_tok_body : forall c i lyc Sc memc mdc regs,
  rbn_C6 B G c i lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + 10836)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 10912)) mem' (seg_rom SEGS)) md' /\ rbn_T c i lyc' Sc' mem' md' regs').
Proof.
intros c i lyc Sc memc mdc regs HC.
pose proof HC as (HL & HW4 & HNM & Hi & R21 & R26 & R24 & R20 & HSCO & HTB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HL as (HCORE & _ & _ & _ & R22).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HNM as (_ & HGN & R25).
pose proof HW4 as (_ & _ & R27).
pose proof asan_consts as (_ & C2 & C3 & C4 & C5).
assert (F8 : x_F c mod 8 = 0) by (apply mod32_mod8; exact HFal).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (ENM : x_NM c = x_F c + 64) by reflexivity.
set (k := Z.to_nat i) in *.
assert (Hk : (k < length (x_nmc c))%nat) by (subst k; lia).
set (x := nth k (x_nmc c) 0) in *.
assert (Hx : 0 < x < 256) by (subst x; exact (proj1 (Forall_forall _ _) Hch _ (nth_In _ 0 Hk))).
set (sn := if existsb (fun y => y =? 45) (firstn k (x_nmc c)) then 1 else 0) in *.
assert (Hsn : sn = 0 \/ sn = 1) by (subst sn; destruct (existsb _ _); auto).
remember (Eimg (Ereg regs [Z_to_bv 64 (x_NM c + i); Z_to_bv 64 x])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall j, (j < A_TEXT)%nat -> ew E j = ew (Ereg regs [Z_to_bv 64 (x_NM c + i); Z_to_bv 64 x]) j)
  by (intros j Hj; subst E; apply Eimg_low; exact Hj).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (x_NM c + i); Z_to_bv 64 x]) E)
  by (split; [intros j Hj; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 24) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 i) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = Z_to_bv 64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E24 : ew E 24 = Z_to_bv 64 45) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
assert (E26 : ew E 26 = Z_to_bv 64 sn) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 26 26%bv eq_refl); exact R26).
assert (E27 : ew E 27 = Z_to_bv 64 (x_NM c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 (x_NM c + i)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 x) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = 24) by (rewrite E20; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E 21) = i) by (rewrite E21; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = SHADOW_OFF) by (rewrite E22; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U24 : bv_unsigned (ew E 24) = 45) by (rewrite E24; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = sn) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = x_NM c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = x_NM c + i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = x) by (rewrite E33; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rbn_ssB
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + 10836)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ssB. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn_rsB. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (x_NM c + i) 0 1 (SOff 33 0) x);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    unfold x_mem_at in HGN. destruct (HGN k ltac:(rewrite length_app; cbn [length]; lia)) as [Hv _].
    rewrite app_nth1 in Hv by lia. fold x in Hv. subst k. rewrite Z2Nat.id in Hv by lia.
    rewrite Z.add_0_r. exact Hv.
  - apply pairwise_disjoint_of_extents. unfold rbn_rsB, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
  - unfold facts_ok, rbn_GB. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U21, U22, U24, U26, U27, U32, U33.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB, SHADOW_OFF. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 27 (x_NM c) E27), (U_atom E 21 i E21), (U_atom E 32 (x_NM c + i) E32) by lia.
      unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity. }
assert (SHOK : sh_ok SEGS rbn_BxB rbn_SHB E (mrestrict (w_H (x_W c)) memc)).
{ unfold sh_ok, rbn_SHB. constructor; [|constructor]. unfold shent_ok, app_apart, rbn_BxB. cbn [she_m she_lo she_hi].
  rewrite (U_atom E 22 SHADOW_OFF E22) by (unfold SHADOW_OFF; lia). rewrite (U_atom E 32 (x_NM c + i) E32) by lia.
  split.
  - intros y Hy. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    replace y with (x_F c + (64 + i)) by lia. rewrite div8_add by exact F8.
    replace (64 + i) with (i + 8 * 8) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_pos i 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono i 22 8 ltac:(lia) ltac:(lia)).
    change (22 / 8) with 2 in *.
    destruct HSCO as (_ & S8 & _ & _).
    replace (SHADOW_OFF + (x_F c / 8 + (i / 8 + 8))) with (x_FS c + (8 + i / 8)) by (unfold x_FS; lia).
    apply S8. lia.
  - intros a Ha. cbn [Z.min Z.max] in Ha. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
    unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
clear HE EL.
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 10836)) memc (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK Bspan; [rbn_awr_ro |].
rename ms into ms1, HFr into HFr1. clear HF HG.
assert (K1 : mkeep (x_W c) memc (ms_mem ms1) (fun _ => False)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) memc (ms_mem ms1) (fun _ => False) HFr1 _ a Ha Hz).
  rbn_win idtac. }
clear HFr1.
(* 0x831e4: c <> '-' ? *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- rewrite branch_ne_U in Hc. rbn_Ux Hc. rewrite ?Z.add_0_r in Hc. try change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [rbn_awr_ro |].
  rename ms into ms2, HFr into HFr2. clear HF HG.
  assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (fun _ => False)).
  { intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr2 _ a Ha Hz).
    rbn_win idtac. }
  assert (Hmod : (x =? 45) && negb (existsb (fun y => y =? 45) (firstn k (x_nmc c))) = false)
    by (rewrite (proj2 (Z.eqb_neq x 45) Hc); reflexivity).
  rbn_tok_callstep HC HJ (fun a (Ha : 0 <= a < 2 ^ 64) (Hz : ~ False) => eq_trans (K2 a Ha Hz) (K1 a Ha Hz)) Hmod HAE U9 E33 x.
- rewrite branch_ne_U in Hc. rbn_Ux Hc. rewrite ?Z.add_0_r in Hc. try change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_tok RUN HS HJ SHOK Bspan; [rbn_awr_ro |].
  rename ms into ms2, HFr into HFr2. clear HF HG.
  assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (fun _ => False)).
  { intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (fun _ => False) HFr2 _ a Ha Hz).
    rbn_win idtac. }
  rename Hc into Hx45.
  (* 0x831e8: a '-' was read before ? *)
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + rewrite branch_ne_U in Hc. rbn_Ux Hc. rewrite ?Z.add_0_r in Hc. try change (zcanon 0) with 0 in Hc. apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_tok RUN HS HJ SHOK Bspan; [rbn_awr_ro |].
    rename ms into ms3, HFr into HFr3. clear HF HG.
    assert (K3 : mkeep (x_W c) (ms_mem ms2) (ms_mem ms3) (fun _ => False)).
    { intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) (ms_mem ms2) (ms_mem ms3) (fun _ => False) HFr3 _ a Ha Hz).
      rbn_win idtac. }
    assert (Hmod : (x =? 45) && negb (existsb (fun y => y =? 45) (firstn k (x_nmc c))) = false).
    { rewrite Hx45. subst sn. destruct (existsb (fun y => y =? 45) (firstn k (x_nmc c))) eqn:Ee;
      [reflexivity | try rewrite Ee in Hc; cbn in Hc; lia]. }
    rbn_tok_callstep HC HJ (fun a (Ha : 0 <= a < 2 ^ 64) (Hz : ~ False) => eq_trans (K3 a Ha Hz) (eq_trans (K2 a Ha Hz) (K1 a Ha Hz)))
      Hmod HAE U9 E33 x.
  + rewrite branch_ne_U in Hc. rbn_Ux Hc. rewrite ?Z.add_0_r in Hc. try change (zcanon 0) with 0 in Hc. apply negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 10912; [rbn_awr_ro |].
    rename ms into ms3, HFr into HFr3. clear HF HG.
    assert (K3 : mkeep (x_W c) (ms_mem ms2) (ms_mem ms3) (fun _ => False)).
    { intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) (ms_mem ms2) (ms_mem ms3) (fun _ => False) HFr3 _ a Ha Hz).
      rbn_win idtac. }
    assert (Hex : existsb (fun y => y =? 45) (firstn k (x_nmc c)) = false).
    { subst sn. destruct (existsb (fun y => y =? 45) (firstn k (x_nmc c))) eqn:Ee;
      [try rewrite Ee in Hc; cbn in Hc; lia | reflexivity]. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;20;21;22;23;24;25;27]%bv HS
      ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
    cbn [ms_regs restrict] in HKR.
    prreg HS (26%bv : bv 5) R26f.
    pmkst HS.
    apply SRr_ret. split; [reflexivity|].
    do 5 eexists. split; [reflexivity|].
    refine (rbn_T_skip c i lyc Sc memc mdc regs (ms_mem ms3) _ (ms_regs ms3) HC HJ
      (fun a Ha Hz => eq_trans (K3 a Ha Hz) (eq_trans (K2 a Ha Hz) (K1 a Ha Hz))) Hx45 Hex
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ R26f); rbn_kr HKR.
Qed.
(* The token loop: one char per round (rbn_tok_body, then the back edge rbn_tok_tail), by induction on the chars left. *)
Lemma rbn_tok_loop : forall (k : nat) c i lyc Sc memc mdc regs,
  Z.of_nat k = Z.of_nat (length (x_nmc c)) - i ->
  rbn_C6 B G c i lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x454)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x4bc)) mem' (seg_rom SEGS)) md' /\
       rbn_C7 B G c lyc' Sc' mem' md' regs').
Proof.
induction k as [|k IH]; intros c i lyc Sc memc mdc regs Hk HC.
- exfalso. pose proof HC as (_ & _ & _ & Hi & _). lia.
- replace (BASE + AF_reac_box_name + 0x454) with (BASE + 10836) by (unfold AF_reac_box_name; lia).
  replace (BASE + AF_reac_box_name + 0x4bc) with (BASE + 10940) by (unfold AF_reac_box_name; lia).
  eapply SRr_bind; [exact (rbn_tok_body c i lyc Sc memc mdc regs HC)|].
  intros W1 c1 _ (-> & ly1 & S1 & regs1 & mem1 & md1 & -> & HT).
  eapply SRr_bind; [exact (rbn_tok_tail c i ly1 S1 mem1 md1 regs1 HT)|].
  intros W2 c2 _ (-> & ly2 & S2 & regs2 & mem2 & md2 & [(-> & Hlt & HC2) | (-> & HC7)]).
  + pose proof (IH c (i + 1) ly2 S2 mem2 md2 regs2 ltac:(lia) HC2) as H.
    replace (BASE + AF_reac_box_name + 0x454) with (BASE + 10836) in H by (unfold AF_reac_box_name; lia).
    replace (BASE + AF_reac_box_name + 0x4bc) with (BASE + 10940) in H by (unfold AF_reac_box_name; lia).
    exact H.
  + apply SRr_ret. split; [reflexivity|]. exists ly2, S2, regs2, mem2, md2. split; [reflexivity | exact HC7].
Qed.
(* ---- C7 -> C8: what the state at C8 needs from the memory and registers the segment leaves ---- *)
(* The bytes 0x83230 .. 0x83294 write: memset's stack, db (s1 + 88 .. 120), tk's NUL, dp's scope. *)
Definition rbn_z78 (c : rbx) (a : Z) : Prop :=
  (x_s1 c - SB_CH_STK <= a < x_s1 c) \/ (x_s1 c + 88 <= a < x_s1 c + 120) \/
  a = x_TK c + Z.of_nat (length (fst (rbn_tok (x_nmc c)))) \/ (x_FS c + 24 <= a < x_FS c + 30).
Lemma rbn_C8_of_C7 : forall c lyc Sc memc mdc regs mF mdF (regsF : bvmap 5 word),
  rbn_C7 B G c lyc Sc memc mdc regs ->
  ajournal SEGS B (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c)
    [(3, x_fpos c)] lyc Sc (x_W c) mF mdF 0 ->
  mkeep (x_W c) memc mF (rbn_z78 c) ->
  val_mem SEGS (x_mem_at c mF) (x_s1 c + 88) 8 (x_DP c) ->
  val_mem SEGS (x_mem_at c mF) (x_s1 c + 96) 8 48 ->
  (forall i, 0 <= i < 16 -> aview SEGS (w_H (x_W c)) mF (x_s1 c + 104 + i) = Some 0) ->
  aview SEGS (w_H (x_W c)) mF (x_TK c + Z.of_nat (length (fst (rbn_tok (x_nmc c))))) = Some 0 ->
  (forall j, 24 <= j < 30 -> aview SEGS (w_H (x_W c)) mF (x_FS c + j) = Some 0) ->
  getr regsF 2 = getr regs 2 -> getr regsF 3 = getr regs 3 -> getr regsF 4 = getr regs 4 ->
  getr regsF 8 = getr regs 8 -> getr regsF 9 = getr regs 9 -> getr regsF 18 = getr regs 18 ->
  getr regsF 19 = getr regs 19 -> getr regsF 22 = getr regs 22 -> getr regsF 23 = getr regs 23 ->
  getr regsF 25 = getr regs 25 -> getr regsF 27 = getr regs 27 ->
  getr regsF 26 = w64 (x_DP c) -> getr regsF 10 = w64 (nth 0 (x_nmc c) 0) ->
  getr regsF 24 = w64 (x_NM c) -> getr regsF 20 = w64 (x_NM c + 1) -> getr regsF 21 = w64 (2 ^ 64 - 1) ->
  rbn_C8 B G c 0 lyc Sc mF mdF regsF.
Proof.
intros c lyc Sc memc mdc regs mF mdF regsF (HL & HW4 & HNM & HSCO & HTB) HJF HK VDp VDc Z16 ZT ZS
  Q2 Q3 Q4 Q8 Q9 Q18 Q19 Q22 Q23 Q25 Q27 R26 R10 R24 R20 R21.
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (proj1 HL) as (_ & _ & HPERM & _).
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HTB as (_ & _ & _ & _ & _ & Htl & _).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (HZ : forall a, rbn_z78 c a -> (x_s1 c - 4112 <= a < x_s1 c) \/ (x_s1 c + 88 <= a < x_s1 c + 120) \/
   a = x_F c + 128 + Z.of_nat (length (fst (rbn_tok (x_nmc c)))) \/
   (2147450880 + x_F c / 8 + 24 <= a < 2147450880 + x_F c / 8 + 30)).
{ intros a Ha. unfold rbn_z78, x_FS, x_TK in Ha. change SB_CH_STK with 4112 in Ha.
  change SHADOW_OFF with 2147450880 in Ha. exact Ha. }
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (NZf : forall x, x_F c <= x < x_F c + 512 -> x <> x_F c + 128 + Z.of_nat (length (fst (rbn_tok (x_nmc c)))) ->
  ~ rbn_z78 c x).
{ intros x Hx Hne Hz. apply HZ in Hz. destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | lia |].
  exact (fshadow_not_app (x_F c) 30 (x_F c) 512 x ltac:(lia) ltac:(lia) HFapp ltac:(lia) Hx). }
assert (NZs : forall x, x_FS c <= x < x_FS c + 64 -> ~ (x_FS c + 24 <= x < x_FS c + 30) -> ~ rbn_z78 c x).
{ intros x Hx Hne Hz. apply HZ in Hz. rewrite EFS in Hx, Hne.
  destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [lia | lia | |lia].
  subst x. exact (fshadow_not_app (x_F c) 64 (x_F c) 512 (x_F c + 128 + Z.of_nat (length (fst (rbn_tok (x_nmc c)))))
    ltac:(lia) ltac:(lia) HFapp ltac:(lia) ltac:(lia)). }
assert (NZw : forall x, x_s1 c + 120 <= x < x_sp0 c -> ~ rbn_z78 c x).
{ intros x Hx Hz. apply HZ in Hz. lia. }
unfold rbn_C8.
split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
- apply (rbn_live_keep c lyc Sc memc mdc regs lyc Sc mF mdF regsF HL HJF HPERM); try assumption.
  apply (mkeep_mono _ _ _ _ _ HK). intros a Ha. apply HZ in Ha. unfold rbn_zone. rewrite EFS.
  change SB_CH_STK with 4112. lia.
- destruct HW4 as (HWB & HGW & R27). split; [|split; [|rewrite Q27; exact R27]].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _).
    apply (rbn_sb_keep c memc mF (rbn_z78 c) _ _ _ _ _ HK); unfold x_wb, x_W4 in *;
      [lia | lia | lia | lia | intros x Hx; apply NZw; lia | intros x Hx; apply NZf; lia | exact HWB].
  + pose proof HWB as (_ & _ & _ & _ & _ & Hlw & _). unfold x_mem_at, x_W4 in *.
    apply (mkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx; apply NZf; lia | exact HGW].
- destruct HNM as (HNB & HGN & R25). split; [|split; [|rewrite Q25; exact R25]].
  + pose proof HNB as (_ & _ & _ & _ & _ & Hln & _).
    apply (rbn_sb_keep c memc mF (rbn_z78 c) _ _ _ _ _ HK); unfold x_nb, x_NM in *;
      [lia | lia | lia | lia | intros x Hx; apply NZw; lia | intros x Hx; apply NZf; lia | exact HNB].
  + pose proof HNB as (_ & _ & _ & _ & _ & Hln & _). unfold x_mem_at, x_NM in *.
    apply (mkeep_garr8 _ _ _ _ _ _ HK); rewrite ?length_app; cbn [length];
      [lia | lia | intros x Hx; apply NZf; lia | exact HGN].
- split; [|split; [|exact R26]].
  + apply (rbn_sb_keep c memc mF (rbn_z78 c) _ _ _ _ _ HK); unfold x_tb, x_TK in *;
      [lia | lia | lia | lia | intros x Hx; apply NZw; lia | intros x Hx; apply NZf; lia | exact HTB].
  + destruct HTB as (_ & _ & _ & _ & _ & _ & _ & HG). unfold x_mem_at in *.
    apply (proj2 (garr8_app SEGS _ _ _ _)). split.
    * apply (mkeep_garr8 _ _ _ _ _ _ HK); unfold x_TK in *; [lia | lia | intros x Hx; apply NZf; lia | exact HG].
    * apply garr8_one; [apply val1_of_aview; exact ZT | lia].
- lia.
- change (Z.to_nat 0) with 0%nat. exact R10.
- rewrite Z.add_0_r. exact R24.
- rewrite Z.add_0_r. exact R20.
- exact R21.
- destruct HSCO as (S4 & S8 & S16 & S24). unfold rbn_scope. cbv zeta.
  split; [rewrite (HK (x_FS c + 4)); [exact S4 | lia | apply NZs; lia]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S8 j Hj) | lia | apply NZs; lia]|].
  split; [intros j Hj; rewrite (HK (x_FS c + j)); [exact (S16 j Hj) | lia | apply NZs; lia]|].
  exact ZS.
- change (firstn (Z.to_nat 0) (x_nmc c)) with (@nil Z).
  change (sbm_str 48 (@nil Z, 0) (@nil Z)) with (@nil Z, 0). cbn [fst snd].
  unfold rbn_sb, x_db, x_DP, x_mem_at in *. cbv zeta.
  split; [exact VDp|]. split; [replace (x_s1 c + 88 + 8) with (x_s1 c + 96) by lia; exact VDc|].
  split; [cbn [length Z.of_nat]; apply val_mem_zeros; intros i Hi;
          replace (x_s1 c + 88 + 16 + i) with (x_s1 c + 104 + i) by lia; apply Z16; lia|].
  split; [apply val_mem_zeros; intros i Hi;
          replace (x_s1 c + 88 + 24 + i) with (x_s1 c + 104 + (8 + i)) by lia; apply Z16; lia|].
  split; [left; reflexivity|]. split; [cbn [length Z.of_nat]; lia|]. split; [constructor|]. apply garr8_nil.
Qed.

(* ---- C7 -> C8 (0x83230 .. 0x83298) ---- *)
(* The state at 0x83230 (offset 0x4bc): atom 32 = tb.n = |tok|, atom 33 = TK + |tok| (the address 0x83248
   computes), atom 34 = nm[0]; the regions: tb.n (read at 0x83230), db.p / db.cap (written at 0x8326c / 0x83270),
   tk's NUL (0x8324c), dp's six scope bytes (0x83254 .. 0x83268) and nm[0] (read at 0x83284, after the memset).
   No instrumented check: Bspan is empty. *)
Definition rbn_rs78 : smem :=
  [ YP09.mkRegion (Some 9%nat) 136 144 0 0 [YP09.mkChunk 136 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 9%nat) 88 104 88 104 [];
    YP09.mkRegion (Some 33%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 18%nat) 24 30 24 30 [];
    YP09.mkRegion (Some 27%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 34 0))] ].
Definition rbn_G78 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 0);
           (19%nat, mkAF 4096 (2 ^ 47) 0); (25%nat, mkAF 4096 (2 ^ 47) 0); (27%nat, mkAF 4096 (2 ^ 47) 0);
           (18%nat, mkAF SB (SB + 2 ^ 44) 0);
           (32%nat, mkAF 0 23 0); (33%nat, mkAF 4096 (2 ^ 47) 0); (34%nat, mkAF 1 255 0)] []
          [(SAlu ALU_ADD (SOff 25 0) (SOff 32 0), SOff 33 0)].
(* 10940 = AF_reac_box_name + 0x4bc *)
Definition rbn_ss78 : sstate := mkSS 10940 sr_atoms rbn_rs78 None rbn_G78.
(* the write rights of the C7 -> C8 runs: the window (awr case 1), tk's NUL and dp's scope bytes (case 4) *)
Ltac rbn_awr78 c n U9 U33 U18 EFa EFS :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0' fp b0 bc ly own) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (x_s1 c - x_sp0 c));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat (x_TK c + n));
    [ reflexivity | exact U33
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3) with 512; unfold x_TK in Ha; lia
    | ]
  | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat (x_FS c));
    [ reflexivity | exact U18
    | cbn [YP09.r_wlo YP09.r_whi]; let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      right; right; right; exists 3, (x_fpos c); split; [left; reflexivity|];
      right; unfold in_zr; cbn [fst snd]; rewrite EFa; change (fs_frame_bytes 3 / 8) with 64;
      unfold shadow_addr; change SHADOW_OFF with 2147450880; rewrite EFS in Ha; lia
    | ] ].

(* the bytes the two runs before the memset write *)
Definition rbn_zr78 (c : rbx) (a : Z) : Prop :=
  (x_s1 c + 88 <= a < x_s1 c + 104) \/ a = x_TK c + Z.of_nat (length (fst (rbn_tok (x_nmc c)))) \/
  (x_FS c + 24 <= a < x_FS c + 30).
Lemma rbn_seg_c7_c8 : forall c lyc Sc memc mdc regs,
  rbn_C7 B G c lyc Sc memc mdc regs ->
  SRr SEGS (x_W c) (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_box_name + 0x4bc)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = x_W c /\ exists lyc' Sc' regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_reac_box_name + 0x524)) mem' (seg_rom SEGS)) md' /\
       rbn_C8 B G c 0 lyc' Sc' mem' md' regs').
Proof.
intros c lyc Sc memc mdc regs HC.
pose proof HC as (HL & HW4 & HNM & HSCO & HTB).
pose proof (rbn_core_bounds c lyc Sc memc mdc regs (proj1 HL))
  as (Hal & Hceil & Hslo & Hshi & H47 & Hs1al & Hs1lo & Hs1hi & HinF & EFa & HF0 & HF1 & HFapp & HFal & C1).
pose proof (rbn_s1_mod16 c Hal) as Hs16.
destruct (rbn_nmc_facts c lyc Sc memc mdc regs HL) as (Hn & Hch).
pose proof HL as (HCORE & _ & _ & _ & R22).
pose proof HCORE as (HPRE & HJ & HPERM & R2 & R3 & R4 & R8 & R9 & R18 & R19 & R23 & _).
pose proof HW4 as (_ & _ & R27).
pose proof HNM as (_ & HGN & R25).
pose proof HTB as (_ & _ & Vt & _ & _ & Htl & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (_ & C2 & C3 & C4 & C5).
pose proof (Z.div_mod (x_F c) 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound (x_F c) 8 ltac:(lia)) as MF.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (EFS : x_FS c = 2147450880 + x_F c / 8) by reflexivity.
assert (ENM : x_NM c = x_F c + 64) by reflexivity.
assert (DSF : x_FS c + 64 <= x_F c \/ x_F c + 512 <= x_FS c).
{ destruct (Z_le_gt_dec (x_FS c + 64) (x_F c)) as [X|X]; [left; exact X|].
  destruct (Z_le_gt_dec (x_F c + 512) (x_FS c)) as [Y|Y]; [right; exact Y|]. exfalso.
  apply (fshadow_not_app (x_F c) 64 (x_F c) 512 (Z.max (x_F c) (x_FS c))); [lia | lia | exact HFapp | lia | lia]. }
assert (ETK : x_TK c = x_F c + 128) by reflexivity.
(* nm[0], the byte 0x83284 reads *)
assert (Hv0 : 0 < nth 0 (x_nmc c) 0 < 256).
{ apply (proj1 (Forall_forall _ _) Hch). apply nth_In. lia. }
assert (Vnm0 : val_mem SEGS (mrestrict (w_H (x_W c)) memc) (x_NM c + 0) 1 (nth 0 (x_nmc c) 0)).
{ unfold x_mem_at in HGN. destruct (HGN 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as (HV & _).
  rewrite app_nth1 in HV by lia. cbn [Z.of_nat] in HV. exact HV. }
set (t := Z.of_nat (length (fst (rbn_tok (x_nmc c))))) in *.
assert (Ht : 0 <= t <= 23) by (subst t; lia).
set (v0 := nth 0 (x_nmc c) 0) in *.
destruct (al_frames _ _ LAWS lyc Sc (x_W c) memc mdc 3 (x_fpos c) HAR HinF) as (_ & _ & HFb & HFs).
rewrite EFa in HFb, HFs. change (fs_frame_bytes 3) with 512 in HFb, HFs. change (512 / 8) with 64 in HFs.
remember (Eimg (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 (x_TK c + t); Z_to_bv 64 v0])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall i, (i < A_TEXT)%nat -> ew E i = ew (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 (x_TK c + t); Z_to_bv 64 v0]) i)
  by (intros i Hi; subst E; apply Eimg_low; exact Hi).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 t; Z_to_bv 64 (x_TK c + t); Z_to_bv 64 v0]) E)
  by (split; [intros i Hi; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
assert (E2 : ew E 2 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E3 : ew E 3 = getr regs 3) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E9 : ew E 9 = Z_to_bv 64 (x_s1 c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
assert (E18 : ew E 18 = Z_to_bv 64 (x_FS c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 18 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 (x_F c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 19 19%bv eq_refl); exact R19).
assert (E25 : ew E 25 = Z_to_bv 64 (x_TK c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl); exact R25).
assert (E27 : ew E 27 = Z_to_bv 64 (x_NM c)) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
assert (E32 : ew E 32 = Z_to_bv 64 t) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (x_TK c + t)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U2 : bv_unsigned (ew E 2) = x_s1 c) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = x_s1 c) by (rewrite E9; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = x_FS c) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = x_F c) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U25 : bv_unsigned (ew E 25) = x_TK c) by (rewrite E25; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = x_NM c) by (rewrite E27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = t) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = x_TK c + t) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v0) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E rbn_ss78
  (restrict (w_H (x_W c)) (mkst regs (Z_to_bv 64 (BASE + 10940)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold rbn_ss78. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold rbn_rs78. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_s1 c) 136 8 (SOff 32 0) t);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      unfold x_mem_at, x_tb in Vt. replace (x_s1 c + 136) with (x_s1 c + 120 + 16) by lia. exact Vt.
    + rewrite U9. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
    + rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFb (x_TK c + t + o) ltac:(lia))).
    + rewrite U18. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      replace (x_FS c + o) with (shadow_addr (x_F c) + o) by (unfold shadow_addr, x_FS; reflexivity).
      apply (proj1 (HFs o ltac:(lia))).
    + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_NM c) 0 1 (SOff 34 0) v0);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Vnm0].
  - apply pairwise_disjoint_of_extents. unfold rbn_rs78, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U18, U27.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; lia.
  - unfold facts_ok, rbn_G78. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; [exact I|]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U9, U19, U25, U27, U18, U32, U33, U34.
      rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    + split; [|exact I]. apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 25 (x_TK c) E25), (U_atom E 32 t E32), (U_atom E 33 (x_TK c + t) E33) by lia.
      unfold zcanon, M64. rewrite Z.mod_small by lia. reflexivity. }
clear HE EL.
assert (SHOK : sh_ok SEGS rbn_Bx0 [] E (mrestrict (w_H (x_W c)) memc)) by constructor.
replace (BASE + AF_reac_box_name + 0x4bc) with (BASE + 10940) by (unfold AF_reac_box_name; lia).
replace (BASE + AF_reac_box_name + 0x524) with (BASE + 11044) by (unfold AF_reac_box_name; lia).
change memc with (ms_mem (mkst regs (Z_to_bv 64 (BASE + 10940)) memc (seg_rom SEGS))) in HJ.
paj_run_tok RUN HS HJ SHOK rbn_Bsp0; [rbn_awr78 c t U9 U33 U18 EFa EFS |].
rename ms into ms1, HFr into HFr1. clear HF HG HEI0.
(* 0x83240: TK + t does not wrap *)
psrr_branch_tok RUN BR HS SHOK rbn_Bsp0.
{ exfalso. rewrite branch_ltu_U, U_SAlu in Hc. cbn [zalu_raw] in Hc.
  rewrite (U_atom E 25 (x_TK c) E25), U_SLit, (U_atom E 32 t E32) in Hc by lia.
  replace (zcanon (-1)) with (2 ^ 64 - 1) in Hc by (vm_compute; reflexivity).
  rewrite lxor_allones in Hc by lia. rewrite zcanon_id in Hc by (unfold M64; lia).
  destruct (Z.ltb_spec (2 ^ 64 - 1 - x_TK c) t); [lia | discriminate Hc]. }
paj_run_tok RUN HS HJ SHOK rbn_Bsp0; [rbn_awr78 c t U9 U33 U18 EFa EFS |].
rename ms into ms2, HFr into HFr2. clear HF HG HEI0.
(* the fields the run wrote *)
pose proof (st_ok_region_nth E _ _ 1%nat _ HS eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
pose proof (st_ok_region_nth E _ _ 2%nat _ HS eq_refl) as HR2. cbn [restrict ms_mem] in HR2.
pose proof (st_ok_region_nth E _ _ 3%nat _ HS eq_refl) as HR3. cbn [restrict ms_mem] in HR3.
assert (VDp : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_s1 c + 88) 8 (x_F c + 192))
  by (rbn_fld HR1 9%nat (x_s1 c) 88 8%N (x_F c + 192)).
assert (VDc : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_s1 c + 96) 8 48)
  by (rbn_fld HR1 9%nat (x_s1 c) 96 8%N 48).
assert (VNul : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_TK c + t + 0) 1 0)
  by (rbn_fld HR2 33%nat (x_TK c + t) 0 1%N 0).
assert (VS24 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 24) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 24 1%N 0).
assert (VS25 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 25) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 25 1%N 0).
assert (VS26 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 26) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 26 1%N 0).
assert (VS27 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 27) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 27 1%N 0).
assert (VS28 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 28) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 28 1%N 0).
assert (VS29 : val_mem SEGS (mrestrict (w_H (x_W c)) (ms_mem ms2)) (x_FS c + 29) 1 0)
  by (rbn_fld HR3 18%nat (x_FS c) 29 1%N 0).
clear HR1 HR2 HR3.
(* ---- 0x83280: memset(s1 + 104, 0, 16) ---- *)
pmkst HS.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
rewrite U9 in Ra0. rewrite E2 in Rsp. rewrite E3 in Rgp. rewrite E4 in Rtp.
pose proof (rbn_stack_shadow lyc Sc (x_W c) (ms_mem ms2) _ (x_s1 c + 104) 16 (proj1 HJ) ltac:(lia) ltac:(lia) ltac:(lia))
  as (MRA & MHV).
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIGMA IB___asan_memset) AMEMSET (x_W c) (ms_regs ms2) (ms_mem ms2)
    (336 + 2 * ESTACK) (x_sp0 c) (x_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(3, x_fpos c)] lyc Sc _ 0
    (x_s1 c + 104) 0 16 (x_s1 c - x_sp0 c) (Z_to_bv 64 (BASE + 11024)) HJ).
  - exact Ra0.
  - exact Ra1.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - unfold spZ. rewrite Rsp, unsigned_lit_small by lia. lia.
  - exact Hs16.
  - lia.
  - lia.
  - rewrite Rgp. exact R3.
  - rewrite Rtp. exact R4.
  - exact Rra.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [left; lia | lia].
  - unfold amem_range. right. lia.
  - exact MRA.
  - intros _. exact MHV.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0' & Heff & Hout & Hpres2 & Hsame).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H (x_W c)) mem2) HP2 [4]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. constructor; [|constructor].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U27; intros a Ha; [|lia].
  apply (mbyte_of_aview SEGS). apply Hout; lia. }
specialize (HS2 HRK). clear HRK. rewrite <- restrict_mkst_fx in HS2.
(* what the two runs and the memset kept *)
assert (K1 : mkeep (x_W c) memc (ms_mem ms1) (rbn_zr78 c)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) memc (ms_mem ms1) (rbn_zr78 c) HFr1 _ a Ha Hz).
  rbn_win idtac. }
assert (K2 : mkeep (x_W c) (ms_mem ms1) (ms_mem ms2) (rbn_zr78 c)).
{ intros a Ha Hz. refine (kept_of_frame E _ (w_H (x_W c)) (ms_mem ms1) (ms_mem ms2) (rbn_zr78 c) HFr2 _ a Ha Hz).
  rbn_win idtac. }
assert (K3 : mkeep (x_W c) (ms_mem ms2) mem2 (fun a => (x_s1 c + 104 <= a < x_s1 c + 120) \/ (x_s1 c - 4096 <= a < x_s1 c))).
{ intros a Ha Hz. apply Hout; [exact Ha | intros h; apply Hz; left; lia | intros h; apply Hz; right; lia]. }
clear Hc HJ SHOK HFr1 HFr2 Hout HS HP2 Hsame Rra Rsp Rgp Rtp Ra0 Ra1 Ra2 MRA MHV.
(* ---- 0x83284 .. 0x83298 ---- *)
assert (HEI2 : img_env VAL A_LIM (havoc E 512 (map (getr regs2) CLOB))) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (SHOK2 : sh_ok SEGS rbn_Bx0 [] (havoc E 512 (map (getr regs2) CLOB)) (mrestrict (w_H (x_W c)) mem2)) by constructor.
assert (F34 : ew (havoc E 512 (map (getr regs2) CLOB)) 34 = Z_to_bv 64 v0) by (rewrite ew_havoc_old by lia; exact E34).
change mem2 with (ms_mem (mkst regs2 (Z_to_bv 64 (BASE + 11024)) mem2 (seg_rom SEGS))) in HJ2.
paj_run_to_tok RUNTO HS2 HJ2 SHOK2 rbn_Bsp0 11044; [rbn_awr78 c t U9 U33 U18 EFa EFS |].
rename ms into ms3, HFr into HFr3. clear HF HG.
rename HS2 into HS, HJ2 into HJ, SHOK2 into SHOK.
assert (K4 : mkeep (x_W c) mem2 (ms_mem ms3) (fun _ => False)).
{ intros a Ha Hz. refine (kept_of_frame _ _ (w_H (x_W c)) mem2 (ms_mem ms3) (fun _ => False) HFr3 _ a Ha Hz).
  rbn_win idtac. }
clear HFr3.
assert (K35 : mkeep (x_W c) (ms_mem ms2) (ms_mem ms3) (fun a => (x_s1 c + 104 <= a < x_s1 c + 120) \/ (x_s1 c - 4096 <= a < x_s1 c))).
{ intros a Ha Hz. rewrite (K4 a Ha (fun h => h)). exact (K3 a Ha Hz). }
(* ---- the state at 0x83298 is rbn_C8 c 0 ---- *)
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2;3;4;8;9;18;19;22;23;25;27]%bv HS
  ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
prreg HS (26%bv : bv 5) R26f. prreg HS (10%bv : bv 5) R10f. prreg HS (24%bv : bv 5) R24f.
prreg HS (20%bv : bv 5) R20f. prreg HS (21%bv : bv 5) R21f.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
exists lyc, Sc. do 3 eexists. split; [reflexivity|].
unfold t, v0 in *.
apply (rbn_C8_of_C7 c lyc Sc memc mdc regs (ms_mem ms3) _ (ms_regs ms3) HC HJ).
- intros a Ha Hz. unfold rbn_z78 in Hz. change SB_CH_STK with 4112 in Hz.
  rewrite (K35 a Ha) by lia. rewrite (K2 a Ha) by (unfold rbn_zr78; lia). rewrite (K1 a Ha) by (unfold rbn_zr78; lia).
  reflexivity.
- unfold x_mem_at, x_DP. apply (mkeep_val _ _ _ _ _ 8 _ K35); [lia | lia | intros x Hx; lia | exact VDp].
- unfold x_mem_at. apply (mkeep_val _ _ _ _ _ 8 _ K35); [lia | lia | intros x Hx; lia | exact VDc].
- intros i Hi. rewrite (K4 (x_s1 c + 104 + i) ltac:(lia) (fun h => h)), Heff by lia. reflexivity.
- rewrite (K35 (x_TK c + Z.of_nat (length (fst (rbn_tok (x_nmc c))))) ltac:(lia)) by lia.
  apply (aview_of_val_mem1 SEGS); [rewrite Z.add_0_r in VNul; exact VNul | lia].
- intros j Hj. rewrite (K35 (x_FS c + j) ltac:(lia)) by lia. apply (aview_of_val_mem1 SEGS); [|lia].
  assert (j = 24 \/ j = 25 \/ j = 26 \/ j = 27 \/ j = 28 \/ j = 29) as [-> | [-> | [-> | [-> | [-> | ->]]]]] by lia;
    assumption.
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- apply HKR. repeat first [left; reflexivity | right].
- rewrite R26f, U19. reflexivity.
- rewrite R10f, E34. reflexivity.
- rewrite R24f, E27. reflexivity.
- rewrite R20f, U27. reflexivity.
- rewrite R21f. reflexivity.
Qed.
End walk.
End h.
End f.
End d.
