From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import YC1i DiscoACjr ACj1 DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacBoxName JsonScalar.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import
disco_table_c disco_classify_c hunt_c SightModel reac_master_only_cadence_ns_c reac_rate_snap_c
reac_frame_clean_len_c slot_inv slot_frame reac_hunt_verdict_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoEntryInv DiscoRo DiscoEntBodyStmt DiscoEntBody.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma inFP_range_dec : forall FP lo hi,
  {exists a, inFP FP a /\ lo <= a < hi} + {forall a, inFP FP a -> ~ (lo <= a < hi)}.
Proof.
intros FP lo hi. induction FP as [|[x y] FP IH].
- right. intros a Ha. destruct (inFP_nil a Ha).
- destruct (Z.max x lo <? Z.min y hi) eqn:E.
  + left. apply Z.ltb_lt in E. exists (Z.max x lo). split; [|lia].
    exists (x, y). split; [left; reflexivity | cbn [fst snd]; lia].
  + destruct IH as [IH | IH].
    * left. destruct IH as (a & (r & Hr & Ha) & Hl).
      exists a. split; [exists r; split; [right; exact Hr | exact Ha] | exact Hl].
    * right. apply Z.ltb_ge in E. intros a (r & [<- | Hr] & Ha) Hl; [cbn [fst snd] in Ha; lia|].
      exact (IH a (ex_intro _ r (conj Hr Ha)) Hl).
Qed.

Lemma Forall_drop_mid : forall {X} (P : X -> Prop) (a : X) L1 M L2,
  Forall P (a :: L1 ++ M ++ L2) -> Forall P (a :: L1 ++ L2).
Proof.
intros X P a L1 M L2 H. apply Forall_forall. intros x Hx. apply (proj1 (Forall_forall _ _) H).
destruct Hx as [<- | Hx]; [left; reflexivity | right].
apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left; exact Hx | right; apply in_or_app; right; exact Hx].
Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.
Lemma trk_cases : forall cx h a, d_trk cx h a ->
  (h <= a < h + HUNT_SIZE) \/ (d_FB cx <= a < d_FB cx + DFRAME_SIZE).
Proof.
intros cx h a Ht. unfold d_trk in Ht.
destruct Ht as [Ht | [Ht | [Ht | [Ht | Ht]]]]; try (right; exact (objr_frame _ _ _ Ht)). left. exact Ht.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Lemma d_base_input : forall cx, d_base B MT XM_LIB RLO RHI tfib_K cx -> 0 < c_n cx ->
  In (c_p cx, c_n cx) (ablocks B (c_ly cx) (c_S cx)).
Proof.
intros cx ((_ & _ & _ & _ & Hin & _) & _) Hn. destruct Hin as [(E & _) | (_ & Hin)]; [lia | exact Hin].
Qed.

Lemma sep_perm2 : AR_laws SEGS B -> forall ly S W m md x y L1 L2 L3,
  AR SEGS B ly S W m md -> Permutation (ablocks B ly S) (L1 ++ x :: L2 ++ y :: L3) ->
  zdisjoint (block_rng x) (block_rng y).
Proof.
intros LAWS ly S W m md x y L1 L2 L3 HAR HP.
apply (sep_blocks_perm SEGS B LAWS ly S W m md x y (L1 ++ L2 ++ L3) HAR).
eapply Permutation_trans; [exact HP|].
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
apply perm_skip. rewrite app_assoc.
eapply Permutation_trans; [apply Permutation_sym, Permutation_middle|].
apply perm_skip. rewrite app_assoc. apply Permutation_refl.
Qed.

Lemma d_body_frame_disj : AR_laws SEGS B -> forall cx ly S W m md k b n,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k -> In (b, n) (ablocks B ly S) ->
  b + req_size n <= d_FB cx \/ d_FB cx + 4096 <= b.
Proof.
intros LAWS cx ly S W m md k b n Hjr Hb.
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly S W m md k Hjr) as (HAR & Hfin & EFB & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W m md b n DFRAME_CLASS (c_fpos cx) HAR Hb Hfin) as Hz.
rewrite EFB, fs6 in Hz. unfold zdisjoint in Hz. cbn [fst snd] in Hz. exact Hz.
Qed.

Lemma d_body_frame_low : AR_laws SEGS B -> forall cx ly S W m md k,
  d_jr B MT XM_LIB RLO RHI tfib_K cx ly S W m md k -> 4096 <= d_FB cx.
Proof.
intros LAWS cx ly S W m md k Hjr.
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly S W m md k Hjr) as (HAR & Hfin & EFB & _ & _).
pose proof (frames_bounds SEGS B LAWS ly S W m md DFRAME_CLASS (c_fpos cx) HAR Hfin) as (F & _).
rewrite EFB in F. exact F.
Qed.

Lemma d_objs_of_kept : forall cx h T G Lk H W m W' m',
  d_objs cx h T G Lk H W m ->
  (forall a, h <= a < h + HUNT_SIZE -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  (forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
  d_objs cx h T G Lk H W' m'.
Proof.
intros cx h T G Lk H W m W' m' Ho KH KF. apply (d_objs_kept cx h T G Lk H W m W' m' Ho).
intros a Ht. destruct (trk_cases cx h a Ht) as [Ha | Ha]; [exact (KH a Ha) | exact (KF a Ha)].
Qed.

Theorem d_body_pcall : d_body_pcall_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS HRO HCAN cx h n xb shf shf' ly3 S3 W3 m3 md3 ly4 S4 W4 m4 md4 k4 STK sp FP kc
  HB Hjr CJ Hlo Hhi HFP Hhn HP Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7.
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 Hjr) as (HAR4 & Hfin4 & EFB4 & _ & _).
pose proof (d_body_frame_low LAWS cx ly4 S4 W4 m4 md4 k4 Hjr) as F4096.
pose proof CJ as (_ & Hly & _ & _ & _ & Hfrs & _ & _ & C1 & C2 & C3 & C4 & _).
cbn [app] in Hfrs.
assert (Hfin3 : In (DFRAME_CLASS, c_fpos cx) (frames S3)) by (rewrite <- Hfrs; exact Hfin4).
assert (EFB3 : frame_addr ly3 DFRAME_CLASS (c_fpos cx) = d_FB cx).
{ rewrite <- EFB4. unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof Hbl as (Hperm & Hnot & _ & _).
assert (IN3 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (IN4 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly4 S4)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym (Permutation_trans HP Hperm)) Hx). }
assert (NFF : forall a, d_FB cx <= a < d_FB cx + 4096 -> ~ inFP FP a).
{ intros a Ha Hf. destruct (HFP a Hf) as [(b & m & Hbm & Hr) | [Hh | Hd]].
  - pose proof (d_body_frame_disj LAWS cx ly4 S4 W4 m4 md4 k4 b m Hjr (IN4 _ (in_or_app _ _ _ (or_introl Hbm)))). lia.
  - unfold HUNT_SIZE in *. lia.
  - destruct (inFP_nil a Hd). }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (C4 DFRAME_CLASS (c_fpos cx) a Hfin3); [|apply NFF; lia].
  left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, fs6. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hh4 : In (h, HUNT_SIZE) (ablocks B ly4 S4)) by (apply IN4, in_or_app; right; left; reflexivity).
assert (Hobj4 : exists T' G' Lk' H', d_objs cx h T' G' Lk' H' W4 m4).
{ destruct (inFP_range_dec FP h (h + HUNT_SIZE)) as [Htouch | Hno].
  - destruct (d_objs_hupd cx h T G Lk H W3 m3 W4 m4 Hgeo Hobj) as (H' & Ho).
    + intros a Ht Hnh. destruct (trk_cases cx h a Ht) as [Ha | Ha]; [exfalso; exact (Hnh Ha) | exact (KF a Ha)].
    + exact (Hhn Htouch).
    + exists T, G, Lk, H'. exact Ho.
  - exists T, G, Lk, H. apply (d_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
    intros a Ha. replace a with (h + (a - h)) by lia.
    apply (C2 h HUNT_SIZE (a - h) Hh3 Hh4); [unfold req_size, HUNT_SIZE in *; cbn; lia|].
    intros Hf. apply (Hno _ Hf). lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. destruct (G8 Hc) as (P0 & P1 & P2 & P3).
  pose proof (d_base_input cx (proj1 Hjr) Hc) as HpE.
  assert (Hp3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; right; exact HpE).
  assert (Hp4 : In (c_p cx, c_n cx) (ablocks B ly4 S4)) by (apply IN4, in_or_app; right; right; exact HpE).
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  pose proof (al_blocks _ _ LAWS ly4 S4 W4 m4 md4 _ _ HAR4 Hp4) as (_ & Hp4096 & _).
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (C2 (c_p cx) (c_n cx) (a - c_p cx) Hp3 Hp4); [lia|].
  replace (c_p cx + (a - c_p cx)) with a by lia.
  intros Hf. destruct (HFP a Hf) as [(b & m & Hbm & Hr) | [Hh | Hd]].
  - assert (Hne : (b, m) <> (c_p cx, c_n cx)).
    { intros E. rewrite E in Hbm. exact (proj1 (Forall_forall _ _) Hnot _ (or_intror Hbm) HpE). }
    pose proof (sep_blocks SEGS B LAWS ly4 S4 W4 m4 md4 b m _ _ HAR4 (IN4 _ (in_or_app _ _ _ (or_introl Hbm))) Hp4 Hne) as Hz.
    unfold zdisjoint in Hz. cbn [fst snd] in Hz. lia.
  - unfold HUNT_SIZE in *. lia.
  - destruct (inFP_nil a Hd). }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He.
  exact (C3 a (in_roP_img a Hro) Ho He (fp_spares_below FP a (@ro_below_ofl_at SEGS pa_relro_lo pa_relro_hi SK RO a Hro))). }
destruct Hobj4 as (T' & G' & Lk' & H' & Hobj4).
exact (d_body_step B MT XM_LIB RLO RHI tfib_K LAWS HRO HCAN cx h n xb xb shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
  T' G' Lk' H' HB Hjr (d_blocks_perm B cx h xb ly3 S3 ly4 S4 Hbl HP) Hobj4 KI KR Hfr' Hsh').
Qed.

Theorem d_body_malloc : d_body_malloc_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS HRO HCAN cx h n xb shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi xr
  HB Hjr3 Hjr4 Hlen Hlo Hhi Hab Hoffr K Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7.
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 Hjr3) as (HAR3 & Hfin3 & EFB3 & _ & _).
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly4 S4 W4 m4 md4 k4 Hjr4) as (HAR4 & Hfin4 & EFB4 & _ & _).
pose proof K as (_ & K2 & K3 & K4 & _).
pose proof Hbl as (Hperm & Hnot & Hbb & Hoffs).
assert (IN3 : forall x, In x (xb ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) -> In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (XR4 : forall x, In x xr -> In x (ablocks B ly4 S4)).
{ intros x Hx. rewrite Hab. apply in_or_app. right. exact Hx. }
assert (SEP : forall x y, In x (ablocks B ly3 S3) -> In y xr -> zdisjoint (block_rng x) (block_rng y)).
{ intros x y Hx Hy. apply in_split in Hx as (l1 & l2 & E1). apply in_split in Hy as (l3 & l4 & E2).
  apply (sep_blocks_pos SEGS B LAWS ly4 S4 W4 m4 md4 x y l1 (l2 ++ l3) l4 HAR4).
  rewrite Hab, E1, E2. rewrite <- !app_assoc. reflexivity. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, fs6. lia.
  - intros (b & m & Hbm & Hr).
    pose proof (d_body_frame_disj LAWS cx ly4 S4 W4 m4 md4 k4 b m Hjr4 (XR4 _ Hbm)). lia. }
assert (KB : forall b m a, In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros b m a Hx Ha. replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hx); [lia|]. replace (b + (a - b)) with a by lia.
  intros (b' & m' & Hbm & Hr). pose proof (SEP (b, m) (b', m') Hx Hbm) as Hz.
  unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hobj4 : d_objs cx h T G Lk H W4 m4).
{ apply (d_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
  intros a Ha. apply (KB h HUNT_SIZE a Hh3). unfold req_size, HUNT_SIZE in *. cbn. lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. pose proof (d_base_input cx (proj1 Hjr3) Hc) as HpE.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  apply (KB (c_p cx) (c_n cx) a); [apply IN3, in_or_app; right; right; exact HpE | lia]. }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He. exact (K3 a (in_roP_img a Hro) Ho He). }
assert (Hbl4 : d_blocks B cx h (xr ++ xb) ly4 S4).
{ unfold d_blocks. split; [|split; [|split]].
  - rewrite Hab, <- app_assoc. eapply Permutation_trans; [apply Permutation_app_comm|].
    apply Permutation_app_head. exact Hperm.
  - apply Forall_forall. intros x Hx. destruct Hx as [<- | Hx]; [exact (Forall_inv Hnot)|].
    apply in_app_or in Hx as [Hx | Hx]; [| exact (proj1 (Forall_forall _ _) Hnot x (or_intror Hx))].
    intros HE. destruct x as [b m].
    pose proof (SEP (b, m) (b, m) (IN3 (b, m) (in_or_app xb ((h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) (b, m)
      (or_intror (or_intror HE)))) Hx) as Hz.
    pose proof (al_blocks _ _ LAWS ly4 S4 W4 m4 md4 b m HAR4 (XR4 _ Hx)) as (_ & _ & _ & _ & _ & _ & Hm).
    pose proof (req_size_pos m (proj1 Hm)) as (Hr1 & _).
    unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia.
  - assert (Hbb' : bsum (ablocks B ly3 S3) <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum xb)
      by (rewrite <- blocks_bytes_bsum; exact Hbb).
    change (blocks_bytes S4 <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xr ++ xb)).
    rewrite (blocks_bytes_bsum B ly4 S4), Hab, !bsum_app. lia.
  - apply Forall_cons; [exact (Forall_inv Hoffs)|]. apply Forall_app. split; [exact Hoffr | exact (Forall_inv_tail Hoffs)]. }
exact (d_body_step B MT XM_LIB RLO RHI tfib_K LAWS HRO HCAN cx h n xb (xr ++ xb) shf shf' ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4
  T G Lk H HB Hjr4 Hbl4 Hobj4 KI KR Hfr' Hsh').
Qed.

Theorem d_body_free : d_body_free_stmt B MT XM_LIB RLO RHI tfib_K.
Proof.
intros LAWS HRO HCAN cx h n xb1 xb2 pz shf shf' ly3 S3 W3 m3 md3 k3 ly4 S4 W4 m4 md4 k4 lo hi l1 l2
  HB Hjr3 Hjr4 Hlen Hlo Hhi Hab3 Hab4 K Hfr' Hsh'.
pose proof HB as (T & G & Lk & H & Hfr & Hsh & Hobj & Hbl & Hin & Himg & Hoff & Hgeo & Hcan & Hstk & Hwr).
pose proof Hgeo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8). rewrite fs6 in G2, G7.
destruct (d_jr_facts B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W3 m3 md3 k3 Hjr3) as (HAR3 & Hfin3 & EFB3 & _ & _).
pose proof K as (_ & K2 & K3 & K4 & _).
pose proof Hbl as (Hperm & Hnot & Hbb & Hoffs).
assert (IN3 : forall x, In x ((xb1 ++ pz ++ xb2) ++ (h, HUNT_SIZE) :: ablocks B (c_ly cx) (c_S cx)) ->
  In x (ablocks B ly3 S3)).
{ intros x Hx. exact (Permutation_in _ (Permutation_sym Hperm) Hx). }
assert (PZXB : forall x, In x pz -> In x (xb1 ++ pz ++ xb2)).
{ intros x Hx. apply in_or_app. right. apply in_or_app. left. exact Hx. }
assert (PZ3 : forall x, In x pz -> In x (ablocks B ly3 S3)).
{ intros x Hx. apply IN3, in_or_app. left. exact (PZXB x Hx). }
assert (PZH : forall x, In x pz -> zdisjoint (block_rng x) (block_rng (h, HUNT_SIZE))).
{ intros x Hx. destruct (in_split _ _ (PZXB x Hx)) as (L1 & L2 & E1).
  apply (sep_perm2 LAWS ly3 S3 W3 m3 md3 x (h, HUNT_SIZE) L1 L2 (ablocks B (c_ly cx) (c_S cx)) HAR3).
  pose proof Hperm as HP'. rewrite E1, <- app_assoc in HP'. exact HP'. }
assert (KF : forall a, d_FB cx <= a < d_FB cx + DFRAME_SIZE -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Ha. unfold DFRAME_SIZE in Ha. apply (K4 DFRAME_CLASS (c_fpos cx) a Hfin3).
  - left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFB3, fs6. lia.
  - intros (b & m & Hbm & Hr).
    pose proof (d_body_frame_disj LAWS cx ly3 S3 W3 m3 md3 k3 b m Hjr3 (PZ3 _ Hbm)). lia. }
assert (KB : forall b m a, In (b, m) (ablocks B ly3 S3) ->
  (forall y, In y pz -> zdisjoint (block_rng (b, m)) (block_rng y)) -> b <= a < b + req_size m ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros b m a Hx Hd Ha. replace a with (b + (a - b)) by lia.
  apply (K2 b m (a - b) Hx); [lia|]. replace (b + (a - b)) with a by lia.
  intros (b' & m' & Hbm & Hr). pose proof (Hd (b', m') Hbm) as Hz.
  unfold zdisjoint, block_rng in Hz. cbn [fst snd] in Hz. lia. }
assert (Hh3 : In (h, HUNT_SIZE) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; left; reflexivity).
assert (Hobj4 : d_objs cx h T G Lk H W4 m4).
{ apply (d_objs_of_kept cx h T G Lk H W3 m3 W4 m4 Hobj); [|exact KF].
  intros a Ha. apply (KB h HUNT_SIZE a Hh3); [|unfold req_size, HUNT_SIZE in *; cbn; lia].
  intros y Hy. pose proof (PZH y Hy) as Hz. unfold zdisjoint in *. lia. }
assert (KI : forall a, 0 < c_n cx -> c_p cx <= a < c_p cx + c_n cx ->
  aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hc Ha. pose proof (d_base_input cx (proj1 Hjr3) Hc) as HpE.
  pose proof (req_size_pos (c_n cx) ltac:(lia)) as (_ & Hrs).
  assert (Hp3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by (apply IN3, in_or_app; right; right; exact HpE).
  apply (KB (c_p cx) (c_n cx) a Hp3); [|lia].
  intros [b m] Hy. assert (Hne : (b, m) <> (c_p cx, c_n cx)).
  { intros E. rewrite E in Hy. exact (proj1 (Forall_forall _ _) Hnot _ (or_intror (PZXB _ Hy)) HpE). }
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 m3 md3 b m _ _ HAR3 (PZ3 _ Hy) Hp3 Hne) as Hz.
  unfold zdisjoint, block_rng in *. cbn [fst snd] in *. lia. }
assert (KR : forall a, in_roP SEGS pa_relro_lo pa_relro_hi a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview SEGS (w_H W4) m4 a = aview SEGS (w_H W3) m3 a).
{ intros a Hro Ho He. exact (K3 a (in_roP_img a Hro) Ho He). }
assert (Hbl4 : d_blocks B cx h (xb1 ++ xb2) ly4 S4).
{ unfold d_blocks. split; [|split; [|split]].
  - rewrite Hab4, <- app_assoc. rewrite Hab3, <- !app_assoc in Hperm.
    exact (Permutation_app_inv_m _ _ _ _ _ Hperm).
  - exact (Forall_drop_mid _ _ _ _ _ Hnot).
  - assert (Hbb' : bsum (ablocks B ly3 S3) <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xb1 ++ pz ++ xb2))
      by (rewrite <- blocks_bytes_bsum; exact Hbb).
    rewrite Hab3, !bsum_app in Hbb'.
    change (blocks_bytes S4 <= blocks_bytes (c_S cx) + HUNT_SIZE + bsum (xb1 ++ xb2)).
    rewrite (blocks_bytes_bsum B ly4 S4), Hab4, !bsum_app. lia.
  - exact (Forall_drop_mid _ _ _ _ _ Hoffs). }
exact (d_body_step B MT XM_LIB RLO RHI tfib_K LAWS HRO HCAN cx h n (xb1 ++ pz ++ xb2) (xb1 ++ xb2) shf shf'
  ly3 S3 W3 m3 ly4 S4 W4 m4 md4 k4 T G Lk H HB Hjr4 Hbl4 Hobj4 KI KR Hfr' Hsh').
Qed.
End h.
End f.
End d.
