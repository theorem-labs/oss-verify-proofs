(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the shared part of
   stretch SB9_5 of segment B9 of reac_segconf_parse_file's walk (lib/B/Prog/pf_seg_B9_d.v: J4 0x88440 -> K5 0x88570,
   the unquote of reac_segconf.c:78-86). A B9 sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's walk: helper facts of stretch SB9_5).
   ADAPTED from a working branch's lib/A/Prog/pf_a9_s1.v / pf_a9_s1_k.v (A9's internal cuts with a
   continuation premise, the buf strings after a NUL store) and lib/B/Prog/pf_seg_B9_s1.v (the B9 cut rebuild by
   b9_move0), re-derived on image B's code.

   The stretch is cut at three internal points of its own, each right after an `add a0,s3,a1` (so the byte address
   vp0 + |v0| - 1 is one atom of a fresh seed, the base of a one-byte region):
     B9S5_DQ 0x88480  the DQ arm, before check B#11 (v0[0] = DQ, 34)
     B9S5_SQ 0x88530  the SQ arm, before check B#13 (v0[0] = SQ, 39)
     B9S5_ST 0x88554  the strip, before check B#14 and the store (v0[0] = v0[n - 1] = the quote)
   Here: the cut predicates b9s5_D (INV_J4 without its registers), b9s5_Q (an arm), b9s5_S (the strip) and their
   from-this-point-to-the-goal forms from_Q5 / from_S5; the buf strings after the strip's store
   (b9s5_strip_str: the value without its quotes at vp0 + 1); and K5's predicate rebuilt after a run that keeps
   every byte but at most a range of buf at or above vp0 (b9s5_k5: pf_base by pf_seg_B9_k.v b9_move0, the key
   below vp0 kept whole). No Section hypothesis. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces pf_seg_B9_d pf_seg_B9_f
  pf_seg_B9_k pf_seg_B9_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** ** The internal cut pcs (listing offsets; BASE + AF_reac_segconf_parse_file = 0x87e38) *)
Definition B9S5_DQ : Z := AF_reac_segconf_parse_file + 0x648.   (* 0x88480 the DQ arm after `add a0,s3,a1` *)
Definition B9S5_SQ : Z := AF_reac_segconf_parse_file + 0x6f8.   (* 0x88530 the SQ arm after `add a0,s3,a1` *)
Definition B9S5_ST : Z := AF_reac_segconf_parse_file + 0x71c.   (* 0x88554 the strip after `add a0,s3,a1` *)
Lemma b9s5_pcs : seg_text + B9S5_DQ = 0x88480 /\ seg_text + B9S5_SQ = 0x88530 /\ seg_text + B9S5_ST = 0x88554.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** Lists and readers (no machine state) *)
Lemma b9s5_nth_skipn : forall (l : list Z) k i, nth i (skipn k l) 0 = nth (k + i) l 0.
Proof.
induction l as [|a l IH]; intros k i.
- destruct k; destruct i; reflexivity.
- destruct k as [|k]; [reflexivity|]. cbn [skipn]. rewrite IH. reflexivity.
Qed.

Lemma b9s5_slice_len : forall (V : list Z), (2 <= length V)%nat ->
  length (slice 1 (length V - 1) V) = (length V - 2)%nat.
Proof. intros V H. unfold slice. rewrite length_firstn, length_skipn. lia. Qed.

Lemma b9s5_slice_nth : forall (V : list Z) i, (i < length V - 2)%nat ->
  nth i (slice 1 (length V - 1) V) 0 = nth (S i) V 0.
Proof.
intros V i Hi. unfold slice. rewrite nth_firstn.
replace ((i <? length V - 1 - 1)%nat) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite b9s5_nth_skipn. reflexivity.
Qed.

(* the 8-byte granule of an address is monotone *)
Lemma b9s5_gran : forall w e, w <= e -> w - w mod 8 <= e - e mod 8.
Proof.
intros w e H. pose proof (Z.div_mod w 8 ltac:(lia)). pose proof (Z.div_mod e 8 ltac:(lia)).
assert (w / 8 <= e / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

(* a C string carried to a reader that agrees on its bytes and its NUL and keeps every mapped byte mapped *)
Lemma b9s5_str_keep : forall (rd rd' : reader) p s,
  sa_str rd p s -> (forall a, p <= a <= p + Z.of_nat (length s) -> rd' a = rd a) ->
  (forall a, rd a <> None -> rd' a <> None) -> sa_str rd' p s.
Proof.
intros rd rd' p s [[Hz Hn] Ht] HK HV. split; [split|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite HK by lia.
  apply Hz. rewrite length_app. cbn [length]. lia.
- exact Hn.
- intros y Hy. apply HV. exact (Ht y Hy).
Qed.

(* the strip of R:83-85: the NUL stored on the last byte of V (at p + |V| - 1) leaves V without its first and
   last bytes as the C string at p + 1 *)
Lemma b9s5_strip_str : forall (rd rd' : reader) p V,
  sa_str rd p V -> (2 <= length V)%nat ->
  (forall a, p < a < p + Z.of_nat (length V) - 1 -> rd' a = rd a) ->
  rd' (p + Z.of_nat (length V) - 1) = Some 0 ->
  (forall a, rd a <> None -> rd' a <> None) ->
  sa_str rd' (p + 1) (slice 1 (length V - 1) V).
Proof.
intros rd rd' p V [[Hz Hn] Ht] HL HK H0 HV.
pose proof (b9s5_slice_len V HL) as Lk.
split; [split|].
- intros i Hi. rewrite length_app, Lk in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length V - 2)) as [Hik | Hik].
  + rewrite app_nth1 by (rewrite Lk; exact Hik).
    rewrite b9s5_slice_nth by exact Hik.
    rewrite HK by lia.
    replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (S i)) by lia.
    rewrite (Hz (S i)) by (rewrite length_app; cbn [length]; lia).
    rewrite app_nth1 by lia. reflexivity.
  + assert (i = (length V - 2)%nat) as -> by lia.
    rewrite app_nth2 by (rewrite Lk; lia). rewrite Lk, Nat.sub_diag. cbn [nth].
    replace (p + 1 + Z.of_nat (length V - 2)) with (p + Z.of_nat (length V) - 1) by lia. exact H0.
- intros Hin. apply Hn. unfold slice in Hin. exact (b9_in_skipn 1 V 0 (b9_in_firstn _ _ _ Hin)).
- rewrite Lk. intros y Hy.
  replace (p + 1 + Z.of_nat (length V - 2)) with (p + Z.of_nat (length V) - 1) in Hy by lia.
  apply HV.
  destruct (Z.eq_dec y (p + Z.of_nat (length V))) as [-> | Hne].
  + rewrite (Hz (length V)) by (rewrite length_app; cbn [length]; lia). discriminate.
  + apply Ht. pose proof (b9s5_gran (p + Z.of_nat (length V) - 1) (p + Z.of_nat (length V)) ltac:(lia)). lia.
Qed.

(* a reader at a reads the byte at a mod 2 ^ 64 (pf_seg_B9_s1.v b9s1_aview_mod) *)
Lemma b9s5_aview_mod : forall segs H m a, aview segs H m a = aview segs H m (a mod 2 ^ 64).
Proof.
intros segs H m a. unfold aview, mbyte.
replace (Z_to_bv 64 (a mod 2 ^ 64)) with (Z_to_bv 64 a); [reflexivity|].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zmod_mod. reflexivity.
Qed.

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
Lemma b9s5_inbuf_keep : forall (rd rd' : reader) x p s,
  b9_inbuf rd x p s -> (forall a, p <= a <= p + Z.of_nat (length s) -> rd' a = rd a) ->
  (forall a, rd a <> None -> rd' a <> None) -> b9_inbuf rd' x p s.
Proof.
intros rd rd' x p s [HS HI] HK HV. split; [exact (b9s5_str_keep rd rd' p s HS HK HV) | exact HI].
Qed.


Section x. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(** ** The cut predicates of the stretch *)
(* INV_J4 without its registers: the cut, the '=' at ei, the key at kp below vp0, the trimmed value v0 at vp0 *)
Definition b9s5_D (n : nat) (x : b9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS)
  (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9_core B n x lyc Sc Wc rX memc mdc /\
  strchr (b9_line x) EQ = Some ei /\
  b9_inbuf (rdW Wc memc) x kp (b9_key x ei) /\
  kp + Z.of_nat (length (b9_key x ei)) < vp0 /\
  b9_inbuf (rdW Wc memc) x vp0 (b9_v0 x ei).

(* an arm (B9S5_DQ with q = DQ, B9S5_SQ with q = SQ): v0 starts with q, |v0| >= 2, a0 = vp0 + |v0| - 1 (the last
   byte), a1 = |v0| - 1, a2 = ~vp0 (0x88470 / 0x88520 .. 0x8852c), a5 = cur (slot 0xc0, 0x88454) *)
Definition b9s5_Q (q : Z) (n : nat) (x : b9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate)
  (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc /\
  (2 <= length (b9_v0 x ei))%nat /\ nth 0 (b9_v0 x ei) 0 = q /\
  pf_rg rX (B9_R x ++ [(23, kp); (19, vp0); (15, b9_cp x);
                       (10, vp0 + Z.of_nat (length (b9_v0 x ei)) - 1);
                       (11, Z.of_nat (length (b9_v0 x ei)) - 1); (12, 2 ^ 64 - 1 - vp0)]).

(* the strip (B9S5_ST): v0 starts and ends with the quote q, a0 = vp0 + |v0| - 1 *)
Definition b9s5_S (q : Z) (n : nat) (x : b9x) (ei : nat) (kp vp0 : Z) (lyc : alayout) (Sc : astate)
  (Wc : world SEGS) (rX : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : Prop :=
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc /\
  (2 <= length (b9_v0 x ei))%nat /\ (q = DQ \/ q = SQ) /\
  nth 0 (b9_v0 x ei) 0 = q /\ nth (length (b9_v0 x ei) - 1) (b9_v0 x ei) 0 = q /\
  pf_rg rX (B9_R x ++ [(23, kp); (19, vp0); (15, b9_cp x); (10, vp0 + Z.of_nat (length (b9_v0 x ei)) - 1)]).

Definition from_Q5 (q pc : Z) (n : nat) : Prop := forall x ei kp vp0, b9_from B pc (b9s5_Q q n x ei kp vp0) x.
Definition from_S5 (n : nat) : Prop := forall q x ei kp vp0, b9_from B B9S5_ST (b9s5_S q n x ei kp vp0) x.

Lemma b9s5_D_of_J4 : forall n x ei kp vp0 lyc Sc Wc rX memc mdc,
  INV_J4 B n x ei kp vp0 lyc Sc Wc rX memc mdc -> b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc.
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc (H1 & H2 & H3 & H4 & H5 & _).
exact (conj H1 (conj H2 (conj H3 (conj H4 H5)))).
Qed.

(* the numbers of the value string at vp0: inside buf, so in the frame, below alloc_ceiling and 2 ^ 47 *)
Lemma b9s5_D_rng : forall n x ei kp vp0 lyc Sc Wc rX memc mdc,
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  4096 < b9_buf x /\ b9_buf x <= kp /\ kp + Z.of_nat (length (b9_key x ei)) < vp0 /\
  vp0 + Z.of_nat (length (b9_v0 x ei)) < b9_buf x + 512 /\ b9_buf x + 512 <= pf_F (y_v x) (y_pos x) + 2048 /\
  pf_F (y_v x) (y_pos x) + 2048 <= alloc_ceiling /\ alloc_ceiling <= 0x7fffff800000 /\
  ~ In 0 (b9_v0 x ei).
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc ((HB & _) & _ & [_ [Hk1 Hk2]] & HKLT & [HS [Hv1 Hv2]]).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (_ & _ & _ & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof asan_consts as (C1 & _).
pose proof HS as ((_ & HNZ) & _).
unfold b9_buf, PF_O_BUF in *.
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
exact HNZ.
Qed.

(** ** K5 (0x88570) rebuilt after a run of the stretch: the run kept every byte off a range [wlo, whi) of buf at
    or above vp0 (empty, or the strip's NUL), kept every mapped byte mapped, returned the journal at the same frame
    state, and left the registers of pf_fi, B9_R, s7 = kp, s3 = vp, a5 = cur; the value is at vp. The key lies
    below vp0, so it is kept whole (INV_J4's kp + |key| < vp0). *)
Lemma b9s5_k5 : forall n x ei kp vp0 vp lyc Sc Wc rX memc mdc rX' memc' mdc' wlo whi,
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  vp0 <= wlo -> whi <= b9_buf x + 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (b9_FI B (y_v x)) ->
  pf_rg rX' (B9_R x ++ [(23, kp); (19, vp); (15, b9_cp x)]) ->
  b9_inbuf (rdW Wc memc') x vp (b9_val x ei) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp0 vp lyc Sc Wc rX memc mdc rX' memc' mdc' wlo whi HD HJ' Hwlo Hwhi KM KV0 HFI' HRG' HVAL.
pose proof (b9s5_D_rng _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & _).
destruct HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5, Hwhi.
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ intros a0 Hv0. rewrite b9s5_aview_mod in Hv0 |- *.
  apply KV0; [apply Z.mod_pos_bound; lia | exact Hv0]. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW Wc memc' a = rdW Wc memc a).
{ intros a Ha HW. apply KM; [exact Ha|]. intros Hw. apply HW. unfold b9_Wrx, PF_O_BUF. right; right. lia. }
assert (HB' : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ');
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact HK | exact KV | exact HFI' |].
  eapply b9_keep_fsh; [exact G | exact HK | exact HFSH]. }
split; [|split; [exact HCH|split; [|split; [exact HVAL | exact HRG']]]].
- split; [exact HB'|]. split; [exact HM|].
  split; [eapply b9_keep_st; eassumption|].
  split; [exact HL|]. split; [exact HD0 | exact HDL].
- apply (b9s5_inbuf_keep (rdW Wc memc) (rdW Wc memc') x kp (b9_key x ei) HKEY); [|exact KV].
  intros a Ha. apply KM; lia.
Qed.

(* the cut's facts carried across a run that wrote nothing (every byte kept) at the same frame state *)
Lemma b9s5_D_move : forall n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (b9_FI B (y_v x)) ->
  b9s5_D n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV0 HFI'.
pose proof (b9s5_D_rng _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & _).
destruct HD as (HC & HCH & HKEY & HKLT & HV0).
pose proof HC as (HB & HM & HST & HL & HD0 & HDL).
destruct (b9_geo B _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
assert (HC5 : sa_heap B lyc Sc (p_c (y_v x)) seg_spec.SEG_C_SIZE) by (destruct HOBJ as (_ & _ & _ & _ & H5 & _); exact H5).
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
{ intros a0 Hv0. rewrite b9s5_aview_mod in Hv0 |- *.
  apply KV0; [apply Z.mod_pos_bound; lia | exact Hv0]. }
assert (HK : forall a, 0 <= a < 2 ^ 64 -> ~ b9_Wrx (y_v x) (y_pos x) true a -> rdW Wc memc' a = rdW Wc memc a)
  by (intros a Ha _; exact (KM a Ha)).
assert (HB' : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' PF_SC_LINE).
{ eapply (b9_move0 B (y_v x) (y_pos x) lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ');
    [exists (st_fs Sc); destruct Sc; reflexivity | apply Permutation_refl | exact HK | exact KV | exact HFI' |].
  eapply b9_keep_fsh; [exact G | exact HK | exact HFSH]. }
split; [|split; [exact HCH|split; [|split; [exact HKLT|]]]].
- split; [exact HB'|]. split; [exact HM|].
  split; [eapply b9_keep_st; eassumption|].
  split; [exact HL|]. split; [exact HD0 | exact HDL].
- apply (b9s5_inbuf_keep (rdW Wc memc) (rdW Wc memc') x kp (b9_key x ei) HKEY); [|exact KV].
  intros a Ha. apply KM; lia.
- apply (b9s5_inbuf_keep (rdW Wc memc) (rdW Wc memc') x vp0 (b9_v0 x ei) HV0); [|exact KV].
  intros a Ha. apply KM; lia.
Qed.

(* K5 after a run that wrote nothing, the value unchanged (r_unquote v0 = v0: the short and the kept cases) *)
Lemma b9s5_k5_keep : forall n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc',
  b9s5_D n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x)))
    (p_ly (y_v x)) (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  pf_rg rX' (b9_FI B (y_v x)) ->
  pf_rg rX' (B9_R x ++ [(23, kp); (19, vp0); (15, b9_cp x)]) ->
  b9_val x ei = b9_v0 x ei ->
  INV_K5 B n x ei kp vp0 lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' HD HJ' KM KV0 HFI' HRG' HVAL.
pose proof (b9s5_D_rng _ _ _ _ _ _ _ _ _ _ _ HD) as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & _).
unfold b9_buf, PF_O_BUF in R1, R2, R4, R5.
apply (b9s5_k5 n x ei kp vp0 vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' vp0 vp0 HD HJ').
- lia.
- unfold b9_buf, PF_O_BUF. lia.
- intros a Ha _. exact (KM a Ha).
- exact KV0.
- exact HFI'.
- exact HRG'.
- rewrite HVAL. destruct HD as (_ & _ & _ & _ & HV0).
  assert (KV : forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None).
  { intros a0 Hv0. rewrite b9s5_aview_mod in Hv0 |- *.
    apply KV0; [apply Z.mod_pos_bound; lia | exact Hv0]. }
  apply (b9s5_inbuf_keep (rdW Wc memc) (rdW Wc memc') x vp0 (b9_v0 x ei) HV0); [|exact KV].
  intros a Ha. apply KM; lia.
Qed.

End x.
End d.
