(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0il X0gp X0h2 X0j4 X0hf X0j3 X0hi X0fy X0fg X0da X0g4 X0d8 X0fq X04b
X0d7 X0ff X0h3 X0hn X0h4 X0h5 X0ej X0fv.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X196 X17a X17n X19n X180 X19m X183 X16j X161 X13v X16p X13t X16b X0v9 X13s X160 X17o X188 X17p X17q X154 X16g.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X160 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X154 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16g.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sf_W (c FSB pos usp : Z) : list (Z * Z) :=
[(fl_base FSB c + pos, fl_base FSB c + pos + 1);
(shad (frame_addr FSB c pos), shad (frame_addr FSB c pos) + fsz c / 8);
(usp - 64, usp)].

Section SFree.
Variables (Σ : rtsA) (m m' : mem) (f : Z) (k : nat) (fr : list (Z * nat)) (p usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, k) :: fr.
Hypothesis HPN : fr = [] -> rtA_pois Σ = [].
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation K := (Z.of_nat k).
#[local] Notation g := (fs_of Σ k).
#[local] Notation g' := (mkFs (fss_hint (fs_of Σ k)) (upd (fss_flags (fs_of Σ k)) (Z.to_nat p) 0)).
Hypothesis Hk : (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat.
Hypothesis Hp : 0 <= p < NF K.
Hypothesis Hf : f = frame_addr FSB K p.
Hypothesis Hb : nth (Z.to_nat p) (fss_flags g) 0 = 1.
Hypothesis Hlo : l_ACEIL L <= lo.
Hypothesis Husp : lo + 64 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sf_W K FSB p usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis P_flags : fs_flags FSB K m' (upd (fss_flags g) (Z.to_nat p) 0).

Lemma sf_cls : K = 0 \/ K = 2 \/ K = 4 \/ K = 5 \/ K = 8.
Proof using Hk. clear - Hk. destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia. Qed.

Lemma sf_pieces :
FSB + 0x1000 <= fl_base FSB K + p /\ fl_base FSB K + p + 1 <= FSB + 0x9000
/\ FSB + 0x9000 <= f /\ f + fsz K <= FSB + 0xb09000
/\ shad FSB <= shad f /\ shad f + fsz K / 8 <= shad (FSB + 0xb09000)
/\ l_ACEIL L <= usp - 64.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
pose proof sf_cls as Hc. pose proof (push_bounds Σ m HA) as (B1 & B2 & _).
pose proof (frame_addr_range FSB K p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2. pose proof (flags_range _ Hc) as (F1 & F2).
pose proof (frame_shad_in FSB K p B2 Hc Hp) as (S1 & S2). rewrite shad_fsb_end. rewrite <- Hf in *.
unfold fl_base. destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E in *; cbn in *; lia.
Qed.

Lemma dsf_gen : forall a n, (a + n <= FSB \/ FSB + 0xb09000 <= a) -> (a + n <= shad FSB \/ shad (FSB + 0xb09000) <= a) ->
(a + n <= l_ACEIL L \/ usp <= a) -> disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros a n H1 H2 H3. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
unfold sf_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_head : forall a n, FSB <= a -> a + n <= FSB + 0x1000 -> disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros a n H1 H2. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
unfold sf_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_flags : forall c, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> c <> K -> disjoint_from (sf_W K FSB p usp) (fl_base FSB c) (NF c).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c Hc' Hne. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof (flags_range _ Hc') as (F1 & F2). pose proof (flags_apart _ _ Hc Hc' (not_eq_sym Hne)) as FA.
unfold sf_W. cbn [disjoint_from]. unfold fl_base in *. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_frame : forall c q, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> 0 <= q < NF c ->
disjoint_from (sf_W K FSB p usp) (frame_addr FSB c q) (fsz c).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c q Hc' Hq. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (_ & B2 & _ & B4 & _ & B6 & B7 & B8 & _).
pose proof (frame_addr_range FSB c q Hc' Hq) as (R1 & R2). unfold kFakeStackSize in R2.
assert (Z8' : 0 <= fsz K / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 K ltac:(lia)); lia | lia]).
unfold sf_W. cbn [disjoint_from].
set (a := frame_addr FSB c q) in *. set (fc := fsz c) in *. set (fk := fsz K) in *.
split; [clear - R1 P3; lia|]. split; [clear - B7 R1 R2 P6 P7 Z8'; lia|]. split; [clear - R2 B4 P8; lia | exact I].
Qed.

Lemma dsf_shad : forall c q, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> 0 <= q < NF c -> (c <> K \/ q <> p) ->
disjoint_from (sf_W K FSB p usp) (shad (frame_addr FSB c q)) (fsz c / 8).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c q Hc' Hq Hne. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (_ & B2 & _ & B4 & _ & B6 & B7 & B8 & _).
pose proof (frame_shad_in2 FSB c q B2 Hc' Hq) as (S1 & S2).
pose proof (frame_shads_apart_all FSB c K q p B2 Hc' Hc Hq Hp Hne) as SA.
assert (Z8 : 0 <= fsz c / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 c ltac:(destruct Hc' as [E|[E|[E|[E|E]]]]; lia)); lia | lia]).
unfold sf_W. cbn [disjoint_from].
set (a := frame_addr FSB c q) in *. set (sa := shad a) in *. set (fc := fsz c) in *. set (fk := fsz K) in *.
split; [clear - B7 S1 S2 P2 P3 Z8; lia|]. split; [clear - SA; lia|]. split; [clear - S2 B6 B8 P8; lia | exact I].
Qed.

Lemma sf_munch : munch ([(FSB, FSB + 0xb09000)] ++ [(shad FSB, shad (FSB + 0xb09000))] ++ [(l_ACEIL L, USTACK_TOP)]) m m'.
Proof using HA Hk Hp Hf Hlo Husp Husp2 MU.
pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
apply (munch_weaken (sf_W K FSB p usp)); [|exact MU].
intros x Hx. cbn in Hx. destruct Hx as (X1 & X2 & X3 & _). unfold sf_W. cbn [outside].
split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_grant : forall i b gn a n, (i <> 5)%nat -> nth_error (startup_grants L) i = Some (b, gn) -> b <= a -> a + n <= b + gn ->
disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros i b gn a n Hi Hn H1 H2. pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
assert (Hin : In (b, gn) (startup_grants L)) by (eapply nth_error_In; exact Hn).
pose proof (geo_grant Σ m HA b gn Hin) as (G1 & G2 & G3 & G4 & G5).
assert (AP : apart b gn FSB 0xb09000).
{ destruct (Nat.lt_ge_cases i 5) as [Hl|Hl].
- exact (geo_apart Σ m HA i 5 _ _ Hl Hn eq_refl).
- pose proof (geo_apart Σ m HA 5 i _ _ ltac:(lia) eq_refl Hn) as X. cbn [fst snd] in X. unfold apart in *. lia. }
unfold apart in AP. apply dsf_gen; [lia | unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | lia].
Qed.

Lemma sf_wf : rt_wf (fs_release Σ k p fr).
Proof using HA HF Hk Hp Hf Hb.
clear - HA HF Hk Hp Hf Hb.
pose proof sf_cls as Hc. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & Hfl01).
assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ k)))%nat) by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia).
pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10).
pose proof W6 as (FW0 & FW2 & (FW4 & FW5 & FW8) & FWr & FND & FLN & FCNT & FHINT).
apply NoDup_ListNoDup in FND. rewrite HF in FND, FWr, FLN. apply NoDup_cons_iff in FND as [FNI FND]. apply Forall_cons_iff in FWr as [_ FWr].
assert (Wg' : fs_cls_wf (Z.of_nat k) g').
{ assert (Wg : fs_cls_wf (Z.of_nat k) (fs_of Σ k)) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; assumption).
destruct Wg as ((L1 & L2) & H1 & H2). split; [split|split]; cbn [fss_flags fss_hint].
- rewrite upd_length. exact L1.
- apply Forall_upd; [exact L2 | left; reflexivity].
- exact H1.
- pose proof (nbusy_upd0 (fss_flags (fs_of Σ k)) (Z.to_nat p)). lia. }
assert (Hfr : forall f2 k2, In (f2, k2) fr -> (f2, k2) <> (f, k)) by (intros f2 k2 Hin E; rewrite E in Hin; exact (FNI Hin)).
assert (Wfr : Forall (fun fk => (snd fk = 0%nat \/ snd fk = 2%nat \/ snd fk = 4%nat \/ snd fk = 5%nat \/ snd fk = 8%nat)
/\ exists q, 0 <= q < NF (Z.of_nat (snd fk)) /\ fst fk = frame_addr FSB (Z.of_nat (snd fk)) q
/\ nth (Z.to_nat q) (fss_flags (fs_of (fs_release Σ k p fr) (snd fk))) 0 = 1) fr).
{ apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & p2 & Hp2 & Hf2 & Hb2).
cbn [fst snd] in *. split; [exact Hk2|]. exists p2. split; [exact Hp2|]. split; [exact Hf2|].
unfold fs_release. rewrite (fs_of_set Σ k _ fr k2 Hk Hk2). destruct (Nat.eqb_spec k k2) as [<-|Hne]; [|exact Hb2].
cbn [fss_flags]. rewrite nth_upd_other; [exact Hb2|]. intros E. apply (Hfr f2 k Hin).
assert (p2 = p) by (apply Z2Nat.inj; [lia | lia | symmetry; exact E]). subst p2. rewrite Hf2, Hf. reflexivity. }
split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
split; [|split; [exact W7|split; [exact W8|split; [exact W9 | exact W10]]]].
assert (CNT' : forall k', (k' = 0 \/ k' = 2 \/ k' = 4 \/ k' = 5 \/ k' = 8)%nat ->
Z.of_nat (nbusy (fss_flags (fs_of (fs_release Σ k p fr) k'))) = Z.of_nat (length (List.filter (fun fk => Nat.eqb (snd fk) k') fr))).
{ intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). pose proof (FCNT k' Hk') as Ck. rewrite HF in Ck.
rewrite (filter_cons_class f k fr k') in Ck. destruct (Nat.eqb_spec k k') as [<-|Hne]; cbn [fss_flags].
- cbn [length] in Ck. pose proof (nbusy_upd1to0 (fss_flags (fs_of Σ k)) (Z.to_nat p) Hpl Hb) as X. lia.
- exact Ck. }
assert (HNT' : forall k', (k' = 0 \/ k' = 2 \/ k' = 4 \/ k' = 5 \/ k' = 8)%nat -> fss_hint (fs_of (fs_release Σ k p fr) k') <= 2 ^ 14 * (CREDIT0 - credit (fs_release Σ k p fr))).
{ intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). cbn [credit fs_set]. pose proof (FHINT k' Hk') as Hh.
destruct (Nat.eqb_spec k k') as [<-|Hne]; [cbn [fss_hint]; exact Hh | exact Hh]. }
split; [|split; [|split; [|split; [exact Wfr|split; [apply NoDup_ListNoDup; exact FND | split; [cbn [length] in FLN; cbn [frames fs_release fs_set]; lia|split; [exact CNT' | exact HNT']]]]]]].
all: unfold fs_release, fs_set; destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn [fs0 fs2 fs4 fsc];
first [exact Wg' | assumption | (split; [first [exact Wg' | assumption]| split; first [exact Wg' | assumption]])].
Qed.

Lemma sf_fs_rep : fs_rep (fs_release Σ k p fr) m'.
Proof using HA HF Hk Hp Hf Hb Hlo Husp MU WM P_flags.
pose proof sf_cls as Hc. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & Hfl01).
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & W6 & _).
pose proof W6 as (_ & _ & _ & FWr & FND & _). apply NoDup_ListNoDup in FND. rewrite HF in FND, FWr.
apply NoDup_cons_iff in FND as [FNI FND]. apply Forall_cons_iff in FWr as [_ FWr].
pose proof (ART_fs Σ m HA) as FS. pose proof (fs_rep_cls Σ m k FS Hk) as (CH & CF & CFr).
destruct FS as (F1 & _ & _ & _ & FT & (dtvbeg & Hdb & TG) & (tb & te & TT) & FB). unfold fs_busy in FB. rewrite HF in FB.
apply Forall_cons_iff in FB as [FB0 FBr].
destruct FB0 as (p0 & Hf0 & FWr0 & FWs0 & _). cbn [fst snd] in *.

assert (CLSo : forall c, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8)%nat -> c <> k -> fs_cls_rep FSB (Z.of_nat c) (fs_of Σ c) m').
{ intros c Hcc Hne. pose proof (fs_rep_cls Σ m c (ART_fs Σ m HA) Hcc) as X. pose proof (rel_flags_ok Σ m HA c Hcc) as (Lc & _).
assert (Hc2 : Z.of_nat c = 0 \/ Z.of_nat c = 2 \/ Z.of_nat c = 4 \/ Z.of_nat c = 5 \/ Z.of_nat c = 8) by (destruct Hcc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
assert (HcK : Z.of_nat c <> K) by lia.
apply (fs_cls_rep_transport _ _ _ _ m m' X MU WM). split; [|split].
- apply dsf_head; destruct Hc2 as [E|[E|[E|[E|E]]]]; rewrite E; lia.
- rewrite Lc. exact (dsf_flags _ Hc2 HcK).
- intros q Hq _. split; [exact (dsf_frame _ q Hc2 Hq) | exact (dsf_shad _ q Hc2 Hq (or_introl HcK))]. }

assert (CLSk : fs_cls_rep FSB K g' m').
{ split; [|split].
- unfold fs_hint in *. apply (rw_cells_transport bsegs _ m m' _ _ CH MU WM). cbn [cells_size csize Nat.add].
apply dsf_head; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; lia.
- exact P_flags.
- intros q Hq Hq0. cbn [fss_flags] in Hq0. destruct (Z.eq_dec q p) as [->|Hne].
+ rewrite <- Hf. assert (Hsz : fsz K = fs_size k) by (symmetry; apply fs_size_fsz).
assert (Hpos : 0 < fs_size k) by (rewrite <- Hsz; unfold fsz; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
split.
* pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWr0 WM) ltac:(lia)) as St.
destruct (stk_bytes bsegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (f + fs_size k - f) with (fs_size k) in Hl by lia; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWr0 WM).
* assert (Hs8 : 0 <= fs_size k / 8) by (apply Z.div_pos; lia).
pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWs0 WM) Hs8) as St.
destruct (stk_bytes bsegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (shad f + fs_size k / 8 - shad f) with (fs_size k / 8) in Hl by lia; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWs0 WM).
+ rewrite nth_upd_other in Hq0 by (intros E; apply Hne; apply Z2Nat.inj; [lia | lia | symmetry; exact E]).
destruct (CFr q Hq Hq0) as [(j1 & J1) (j2 & J2)].
assert (Z0 : 0 <= fsz K) by (unfold fsz; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
assert (Z8 : 0 <= fsz K / 8) by (apply Z.div_pos; lia).
split; [exists j1; apply (rw_cells_transport bsegs _ m m' _ _ J1 MU WM) | exists j2; apply (rw_cells_transport bsegs _ m m' _ _ J2 MU WM)];
cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia;
[exact (dsf_frame _ q Hc Hq) | exact (dsf_shad _ q Hc Hq (or_intror Hne))]. }
assert (DIMG : forall a n, a + n <= SEGTOP_A -> disjoint_from (sf_W K FSB p usp) a n).
{ intros a n H. apply dsf_gen; [lia | unfold SHB, SEGTOP_A in *; lia | lia]. }
assert (F1' : fs_const FSB m').
{ unfold fs_const in *. apply (rw_cells_transport bsegs _ m m' _ _ F1 MU WM). cbn [cells_size csize Nat.add]. apply dsf_head; lia. }
assert (T' : rw_cells bsegs m' tpA [C8 (Z_to_bv 64 FSB)]).
{ apply (rw_cells_transport bsegs _ m m' _ _ FT MU WM). apply DIMG. unfold tpA, SEGTOP_A. cbn. lia. }
assert (TG' : tga_cells (l_DTV L) dtvbeg m').
{ unfold tga_cells, dtls_cells in *. destruct TG as (G1' & G2' & G3' & G4' & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)).
repeat (split; [eapply (rw_cells_transport bsegs _ m m'); [eassumption | exact MU | exact WM | apply DIMG;
unfold g_real_tls_get_addr, g_dtv_ptr, g_dtv1, X19n.g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity,
g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; cbn; lia]|]).
apply (rw_cells_transport bsegs _ m m' _ _ D8 MU WM). cbn [cells_size csize Nat.add].
apply (dsf_grant 4%nat (l_DTV L) 4096); [lia | reflexivity | lia | lia]. }
assert (TT' : ttls_cells (l_T L) m' tb te).
{ unfold ttls_cells in *. apply (rw_cells_transport bsegs _ m m' _ _ TT MU WM). cbn [cells_size csize Nat.add].
apply (dsf_grant 2%nat (l_T L) 4096); [lia | reflexivity | lia | lia]. }
assert (FB' : fs_busy L fr m').
{ unfold fs_busy. apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FBr (f2, k2) Hin) as (q & Hq & Wq1 & Wq2 & Cq).
destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & q' & Hq' & Hf2 & _). cbn [fst snd] in *.
assert (Hc2 : Z.of_nat k2 = 0 \/ Z.of_nat k2 = 2 \/ Z.of_nat k2 = 4 \/ Z.of_nat k2 = 5 \/ Z.of_nat k2 = 8) by (destruct Hk2 as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
exists q. split; [exact Hq|]. split; [exact (wr_at_wmono m m' _ _ Wq1 WM)|]. split; [exact (wr_at_wmono m m' _ _ Wq2 WM)|].
apply (rw_cells_transport bsegs _ m m' _ _ Cq MU WM). cbn [cells_size csize Nat.add].
pose proof (dsf_frame _ q' Hc2 Hq') as D1. rewrite <- Hf2 in D1. rewrite fs_size_fsz.
assert (8 <= fsz (Z.of_nat k2)) by (unfold fsz; destruct Hc2 as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
apply (dsj_sub _ f2 (fsz (Z.of_nat k2))); [exact D1 | lia | lia]. }
unfold fs_rep. cbn [lay fs_release fs_set frames].
destruct Hk as [E|[E|[E|[E|E]]]]; subst k; cbn [fs0 fs2 fs4 fsc];
(split; [exact F1'|]); (split; [first [exact CLSk | exact (CLSo 0%nat ltac:(lia) ltac:(lia))]|]);
(split; [first [exact CLSk | exact (CLSo 2%nat ltac:(lia) ltac:(lia))]|]); (split; [split; [first [exact CLSk | exact (CLSo 4%nat ltac:(lia) ltac:(lia))]| split; [first [exact CLSk | exact (CLSo 5%nat ltac:(lia) ltac:(lia))]| first [exact CLSk | exact (CLSo 8%nat ltac:(lia) ltac:(lia))]]]|]);
(split; [exact T'|]); (split; [exists dtvbeg; split; [exact Hdb | exact TG']|]); (split; [exists tb, te; exact TT' | exact FB']).
Qed.

Lemma sf_pois : rtA_pois (fs_release Σ k p fr) = rtA_pois Σ.
Proof using HF HPN.
clear - HF HPN.
unfold rtA_pois at 1. cbn [frames pois fs_release fs_set]. destruct fr as [|x fr']; [symmetry; exact (HPN eq_refl)|]. unfold rtA_pois. rewrite HF. reflexivity.
Qed.

Theorem sf_art : ART_A (fs_release Σ k p fr) m'.
Proof using HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM P_flags.
pose proof (ART_transport_but_fs _ Σ m m' HA sf_munch WM
(art_avoid_but_fs_app _ _ Σ (fsb_avoid Σ m HA) (art_avoid_but_fs_app _ _ Σ (fshad_avoid Σ m HA) (stack_avoid Σ m HA)))) as BF.
assert (BF' : ART_but_fs (fs_release Σ k p fr) m') by (unfold ART_but_fs in *; rewrite sf_pois; exact BF).
exact (ART_of_but_fs _ m' sf_wf BF' sf_fs_rep).
Qed.

Lemma sf_pres : rt_pres (live Σ) fr usp m m'.
Proof using HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM P_flags.
intros a Ha. apply MU. set (x := bv_unsigned a) in *.
pose proof sf_art as HA'. set (Σ' := fs_release Σ k p fr) in *.
pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). pose proof (rel_flags_ok Σ m HA k Hk) as (Hfl & _).
assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ k)))%nat) by (apply Nat2Z.inj_lt; rewrite Hfl, Z2Nat.id by lia; lia).
assert (SP0 : rtA_sp0 Σ' = rtA_sp0 Σ) by reflexivity.
pose proof (art_avoid_client Σ' m' usp HA' ltac:(rewrite SP0; unfold l_ACEIL in Hlo; unfold rtA_sp0; lia)) as (_ & _ & _ & _ & _ & _ & _ & AF & _).
destruct AF as (_ & A0 & A2 & (A4 & A5 & A8) & _).
assert (EK : fs_of Σ' k = g') by (unfold Σ', fs_release; rewrite (fs_of_set Σ k _ fr k Hk Hk), Nat.eqb_refl; reflexivity).
assert (AK : fs_cls_avoid (W_client Σ' usp) FSB K g').
{ rewrite <- EK. change FSB with (l_FSB (lay Σ')). destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; assumption. }
destruct AK as (AK1 & AK2 & AK3). cbn [fss_flags] in AK2, AK3. rewrite upd_length, Hfl in AK2.
destruct (AK3 p Hp ltac:(rewrite (nth_indep_Z _ _ 1 0) by (rewrite upd_length; exact Hpl); apply nth_upd_same; exact Hpl)) as (AK4 & AK5).
rewrite <- Hf in AK4, AK5.
assert (STK : disjoint_from (W_client Σ' usp) (usp - 64) 64).
{ apply avoid_client_intro; [lia | apply dsj_CS_out; right; unfold l_ACEIL, STACK_WIN, SEGTOP_A in *; lia | | |].
- apply Forall_forall. intros [q n] Hin. destruct (rta_live_range Σ' m' q n HA' Hin) as (_ & X & _). cbn [fst snd].
rewrite SP0 in X. unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ' m' HA' f2 k2 Hin) as (_ & X & _). cbn [fst snd].
rewrite SP0 in X. unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ' m' HA' f2 k2 Hin) as (X0 & X & _). cbn [fst snd].
rewrite SP0 in X.
assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
{ unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
right. unfold l_ACEIL, rtA_sp0 in *. lia. }
pose proof (W_client_cover Σ' usp x Ha) as NO.
unfold sf_W. cbn [outside].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK2); unfold fl_base in *; lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK5); rewrite Hf; lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ STK); lia | exact I].
Qed.

End SFree.

Lemma wr_at_cell : forall (m : mem) a (n : nat), wr_at bsegs m a (Z.of_nat n) -> exists bs, rw_cells bsegs m a [CB n bs].
Proof.
intros m a n H. pose proof (wr_at_stk m _ _ H ltac:(lia)) as St.
destruct (stk_bytes bsegs m _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs.
split; [split; [cbn; split; [rewrite Hl; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact H.
Qed.

Lemma sf_pre : forall Σ m f k fr, ART_A Σ m -> frames Σ = (f, k) :: fr ->
(k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat /\ exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p
/\ nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1
/\ rw_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p))]
/\ wr_at bsegs m (shad f) (fs_size k / 8).
Proof.
intros Σ m f k fr HA HF. destruct (rel_slot Σ m f k fr HA HF) as (Hk & p & Hp & Hf & Hb).
split; [exact Hk|]. exists p. split; [exact Hp|]. split; [exact Hf|]. split; [exact Hb|].
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (ART_fs Σ m HA) as FS. destruct FS as (_ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB.
apply Forall_cons_iff in FB as [FB0 _]. destruct FB0 as (p' & Hf' & _ & FWs0 & Cw). cbn [fst snd] in *.
rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ Hc) in Hf'. subst p'. split; [exact Cw | exact FWs0].
Qed.

Lemma sf_finish : forall (Σ : rtsA) PMc (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m : mem)
(f : Z) (k : nat) (fr : list (Z * nat)) (p lo : Z) (Pm : machine_state -> Prop) c1,
ART_A Σ m -> frames Σ = (f, k) :: fr -> (fr = [] -> rtA_pois Σ = []) ->
(k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> 0 <= p < NF (Z.of_nat k) -> f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p ->
nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1 ->
rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
(forall ms, Pm ms -> exists m',
ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p (bv_unsigned sp)) m m'
/\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
/\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m' (upd (fss_flags (fs_of Σ k)) (Z.to_nat p) 0)) ->
exists (Σ' : rts RTA) (v : word),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) fr (bv_unsigned sp) m m') c1
/\ rt_frames RTA Σ' = fr /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ /\ rt_credit RTA Σ' = rt_credit RTA Σ
/\ rt_pois RTA Σ' = rt_pois RTA Σ.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f k fr p lo Pm c1 HA HF HPN Hk Hp Hf Hb LOW LOR SPT HAST HPm.
set (usp := bv_unsigned sp) in *.
assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; unfold rtA_sp0 in LOW; lia).
assert (Husp : lo + 64 <= usp) by (unfold RT_STACK in LOR; lia).
assert (Husp2 : usp <= USTACK_TOP) by lia.
exists (fs_release Σ k p fr), v.
split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity | exact (sf_pois Σ f k fr p HF HPN)]]]]].
unfold ASTA. change (rt_allow RTA (fs_release Σ k p fr)) with (rtA_allow Σ).
eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & PF).
exists m'. split; [exact RS|].
split; [split; [exact (sf_art Σ m m' f k fr p usp lo HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM PF) | split; [exact MI | split; [exact WM | exact ST']]]|].
exact (sf_pres Σ m m' f k fr p usp lo HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM PF).
Qed.

Theorem rta_stack_free_5 : stack_free_contract RTA 5.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR _ HPN ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sf_pre Σ m f 5%nat fr ART0 HFR) as (_ & p & Hp & Hf & Hb & LASTW & SHW).
destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
change (Z.of_nat 5) with 5 in *. change (NF 5) with 512 in Hp. change (fs_size 5) with 2048 in *. change (2048 / 8) with (Z.of_nat 256) in SHW.
destruct (wr_at_cell m _ 256 SHW) as (shj & SHC).
assert (W1 : evt bsegs (sf5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p (fss_flags (fs_of Σ 5)) lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_free 5) m)).
{ unfold entry_st. rewrite Hf in LASTW, SHC |- *. replace (frame_addr (l_FSB (lay Σ)) 5 p + 2048 - 8) with (frame_addr (l_FSB (lay Σ)) 5 p + 2040) in LASTW by lia.
exact (stack_free_5_spec ra sp gp tp t0 t1 t2 s0 s1 _ a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) p (fss_flags (fs_of Σ 5)) lo shj eq_refl Hp FL OK LASTW SHC M2S FSOK HLO FSL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sf5_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1). apply AST_exI in Hc1 as (a0' & Hc1).
apply (sf_finish Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0' m f 5%nat fr p lo _ c1 ART0 HFR HPN ltac:(lia)
ltac:(change (NF (Z.of_nat 5)) with 512; lia) Hf Hb LOW LOR SPT Hc1).
intros ms HP.
destruct HP as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PF & _).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [|split; [exact WM|split; [exact MI|split; [exact ST' | exact PF]]]].
apply (munch_weaken (sf5_W (l_FSB (lay Σ)) p (bv_unsigned sp))); [|exact MU].
intros x Hx. unfold sf_W in Hx. unfold sf5_W. change (Z.of_nat 5) with 5 in Hx. change (fsz 5 / 8) with 256 in Hx. cbn [outside] in *.
destruct Hx as (X1 & X2 & X3 & _). split; [exact X1|]. split; [exact X2|]. split; [lia | exact I].
Qed.

Theorem rta_stack_free_8 : stack_free_contract RTA 8.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR HSZ HPN ART0 MI0 CALL.
destruct (HSZ eq_refl) as (-> & SZ8 & SZR). change (fs_size 8) with 16384 in SZR.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sf_pre Σ m f 8%nat fr ART0 HFR) as (_ & p & Hp & Hf & Hb & LASTW & SHW).
destruct (sm_pre Σ m 8%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
change (Z.of_nat 8) with 8 in *. change (NF 8) with 64 in Hp. change (fs_size 8) with 16384 in *. change (16384 / 8) with 2048 in SHW.
assert (SZD : 0 <= size / 8 <= 2048) by (Z.div_mod_to_equations; lia).
assert (SHW' : wr_at bsegs m (shad f) (Z.of_nat (Z.to_nat (size / 8)))).
{ rewrite Z2Nat.id by lia. destruct SHW as (W0 & W1 & W2). split; [exact W0|]. split; [lia|]. intros i Hi. apply W2. lia. }
destruct (wr_at_cell m _ _ SHW') as (shj & SHC).
assert (W1 : evt bsegs (sf8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p size (fss_flags (fs_of Σ 8)) lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_free 8) m)).
{ unfold entry_st. rewrite Hf in LASTW, SHC |- *. replace (frame_addr (l_FSB (lay Σ)) 8 p + 16384 - 8) with (frame_addr (l_FSB (lay Σ)) 8 p + 16376) in LASTW by lia.
assert (HLO8 : 0x10007fff8008 <= lo) by (pose proof (rta_sp0_win Σ m ART0) as Hw; pose proof LOW as LOW'; cbn [rt_sp0 RTA] in LOW'; unfold STACK_WIN in LOW'; lia).
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (ART_consts Σ m ART0)))))) as PS.
exact (stack_free_8_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) p size (fss_flags (fs_of Σ 8)) lo shj eq_refl eq_refl Hp SZ8 SZR PS FL OK LASTW SHC FSOK HLO8 FSL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sf8_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1). apply AST_exI in Hc1 as (a0' & Hc1).
apply (sf_finish Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0' m f 8%nat fr p lo _ c1 ART0 HFR HPN ltac:(lia)
ltac:(change (NF (Z.of_nat 8)) with 64; lia) Hf Hb LOW LOR SPT Hc1).
intros ms HP.
destruct HP as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PF & _).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [|split; [exact WM|split; [exact MI|split; [exact ST' | exact PF]]]].
apply (munch_weaken (sf8_W (l_FSB (lay Σ)) p (bv_unsigned sp))); [|exact MU].
intros x Hx. unfold sf_W in Hx. unfold sf8_W. change (Z.of_nat 8) with 8 in Hx. change (fsz 8 / 8) with 2048 in Hx. exact Hx.
Qed.

Theorem rta_stack_free : forall k, (k = 5 \/ k = 6 \/ k = 8)%nat -> stack_free_contract RTA k.
Proof.
intros k [ -> | [ -> | -> ] ]; [exact rta_stack_free_5 | | exact rta_stack_free_8].
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR _ HPN ART0 MI0 CALL.
cbn [ART rt_frames RTA] in *. unfold rtA_frames in *.
destruct (rel_slot Σ m f 6%nat fr ART0 HFR) as (Hk6 & _). lia.
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition sf_W (c FSB pos usp : Z) : list (Z * Z) :=
[(fl_base FSB c + pos, fl_base FSB c + pos + 1);
(shad (frame_addr FSB c pos), shad (frame_addr FSB c pos) + fsz c / 8);
(usp - 64, usp)].

Section SFree.
Variables (Σ : rtsA) (m m' : mem) (f : Z) (k : nat) (fr : list (Z * nat)) (p usp lo : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis HF : frames Σ = (f, k) :: fr.
Hypothesis HPN : fr = [] -> rtA_pois Σ = [].
#[local] Notation L := (lay Σ).
#[local] Notation FSB := (l_FSB (lay Σ)).
#[local] Notation K := (Z.of_nat k).
#[local] Notation g := (fs_of Σ k).
#[local] Notation g' := (mkFs (fss_hint (fs_of Σ k)) (upd (fss_flags (fs_of Σ k)) (Z.to_nat p) 0)).
Hypothesis Hk : (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat.
Hypothesis Hp : 0 <= p < NF K.
Hypothesis Hf : f = frame_addr FSB K p.
Hypothesis Hb : nth (Z.to_nat p) (fss_flags g) 0 = 1.
Hypothesis Hlo : l_ACEIL L <= lo.
Hypothesis Husp : lo + 64 <= usp.
Hypothesis Husp2 : usp <= USTACK_TOP.
Hypothesis MU : munch (sf_W K FSB p usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis P_flags : fs_flags FSB K m' (upd (fss_flags g) (Z.to_nat p) 0).

Lemma sf_cls : K = 0 \/ K = 2 \/ K = 4 \/ K = 5 \/ K = 8.
Proof using Hk. clear - Hk. destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia. Qed.

Lemma sf_pieces :
FSB + 0x1000 <= fl_base FSB K + p /\ fl_base FSB K + p + 1 <= FSB + 0x9000
/\ FSB + 0x9000 <= f /\ f + fsz K <= FSB + 0xb09000
/\ shad FSB <= shad f /\ shad f + fsz K / 8 <= shad (FSB + 0xb09000)
/\ l_ACEIL L <= usp - 64.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
pose proof sf_cls as Hc. pose proof (push_bounds Σ m HA) as (B1 & B2 & _).
pose proof (frame_addr_range FSB K p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2. pose proof (flags_range _ Hc) as (F1 & F2).
pose proof (frame_shad_in FSB K p B2 Hc Hp) as (S1 & S2). rewrite shad_fsb_end. rewrite <- Hf in *.
unfold fl_base. destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E in *; cbn in *; lia.
Qed.

Lemma dsf_gen : forall a n, (a + n <= FSB \/ FSB + 0xb09000 <= a) -> (a + n <= shad FSB \/ shad (FSB + 0xb09000) <= a) ->
(a + n <= l_ACEIL L \/ usp <= a) -> disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros a n H1 H2 H3. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
unfold sf_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_head : forall a n, FSB <= a -> a + n <= FSB + 0x1000 -> disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros a n H1 H2. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
unfold sf_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_flags : forall c, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> c <> K -> disjoint_from (sf_W K FSB p usp) (fl_base FSB c) (NF c).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c Hc' Hne. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof (flags_range _ Hc') as (F1 & F2). pose proof (flags_apart _ _ Hc Hc' (not_eq_sym Hne)) as FA.
unfold sf_W. cbn [disjoint_from]. unfold fl_base in *. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_frame : forall c q, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> 0 <= q < NF c ->
disjoint_from (sf_W K FSB p usp) (frame_addr FSB c q) (fsz c).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c q Hc' Hq. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (_ & B2 & _ & B4 & _ & B6 & B7 & B8 & _).
pose proof (frame_addr_range FSB c q Hc' Hq) as (R1 & R2). unfold kFakeStackSize in R2.
assert (Z8' : 0 <= fsz K / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 K ltac:(lia)); lia | lia]).
unfold sf_W. cbn [disjoint_from].
set (a := frame_addr FSB c q) in *. set (fc := fsz c) in *. set (fk := fsz K) in *.
split; [clear - R1 P3; lia|]. split; [clear - B7 R1 R2 P6 P7 Z8'; lia|]. split; [clear - R2 B4 P8; lia | exact I].
Qed.

Lemma dsf_shad : forall c q, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8) -> 0 <= q < NF c -> (c <> K \/ q <> p) ->
disjoint_from (sf_W K FSB p usp) (shad (frame_addr FSB c q)) (fsz c / 8).
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros c q Hc' Hq Hne. pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7. pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (_ & B2 & _ & B4 & _ & B6 & B7 & B8 & _).
pose proof (frame_shad_in2 FSB c q B2 Hc' Hq) as (S1 & S2).
pose proof (frame_shads_apart_all FSB c K q p B2 Hc' Hc Hq Hp Hne) as SA.
assert (Z8 : 0 <= fsz c / 8) by (apply Z.div_pos; [unfold fsz; pose proof (Z.pow_nonneg 2 c ltac:(destruct Hc' as [E|[E|[E|[E|E]]]]; lia)); lia | lia]).
unfold sf_W. cbn [disjoint_from].
set (a := frame_addr FSB c q) in *. set (sa := shad a) in *. set (fc := fsz c) in *. set (fk := fsz K) in *.
split; [clear - B7 S1 S2 P2 P3 Z8; lia|]. split; [clear - SA; lia|]. split; [clear - S2 B6 B8 P8; lia | exact I].
Qed.

Lemma sf_munch : munch ([(FSB, FSB + 0xb09000)] ++ [(shad FSB, shad (FSB + 0xb09000))] ++ [(l_ACEIL L, USTACK_TOP)]) m m'.
Proof using HA Hk Hp Hf Hlo Husp Husp2 MU.
pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). rewrite Hf in P6, P7.
apply (munch_weaken (sf_W K FSB p usp)); [|exact MU].
intros x Hx. cbn in Hx. destruct Hx as (X1 & X2 & X3 & _). unfold sf_W. cbn [outside].
split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma dsf_grant : forall i b gn a n, (i <> 5)%nat -> nth_error (startup_grants L) i = Some (b, gn) -> b <= a -> a + n <= b + gn ->
disjoint_from (sf_W K FSB p usp) a n.
Proof using HA Hk Hp Hf Hlo Husp.
clear - HA Hk Hp Hf Hlo Husp.
intros i b gn a n Hi Hn H1 H2. pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
assert (Hin : In (b, gn) (startup_grants L)) by (eapply nth_error_In; exact Hn).
pose proof (geo_grant Σ m HA b gn Hin) as (G1 & G2 & G3 & G4 & G5).
assert (AP : apart b gn FSB 0xb09000).
{ destruct (Nat.lt_ge_cases i 5) as [Hl|Hl].
- exact (geo_apart Σ m HA i 5 _ _ Hl Hn eq_refl).
- pose proof (geo_apart Σ m HA 5 i _ _ ltac:(lia) eq_refl Hn) as X. cbn [fst snd] in X. unfold apart in *. lia. }
unfold apart in AP. apply dsf_gen; [lia | unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | lia].
Qed.

Lemma sf_wf : rt_wf (fs_release Σ k p fr).
Proof using HA HF Hk Hp Hf Hb.
clear - HA HF Hk Hp Hf Hb.
pose proof sf_cls as Hc. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & Hfl01).
assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ k)))%nat) by (apply Nat2Z.inj_lt; rewrite Hlen, Z2Nat.id by lia; lia).
pose proof (ART_wf Σ m HA) as (W1 & W2 & W3 & W4 & W5 & W6 & W7 & W8 & W9 & W10).
pose proof W6 as (FW0 & FW2 & (FW4 & FW5 & FW8) & FWr & FND & FLN & FCNT & FHINT).
apply NoDup_ListNoDup in FND. rewrite HF in FND, FWr, FLN. apply NoDup_cons_iff in FND as [FNI FND]. apply Forall_cons_iff in FWr as [_ FWr].
assert (Wg' : fs_cls_wf (Z.of_nat k) g').
{ assert (Wg : fs_cls_wf (Z.of_nat k) (fs_of Σ k)) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; assumption).
destruct Wg as ((L1 & L2) & H1 & H2). split; [split|split]; cbn [fss_flags fss_hint].
- rewrite upd_length. exact L1.
- apply Forall_upd; [exact L2 | left; reflexivity].
- exact H1.
- pose proof (nbusy_upd0 (fss_flags (fs_of Σ k)) (Z.to_nat p)). lia. }
assert (Hfr : forall f2 k2, In (f2, k2) fr -> (f2, k2) <> (f, k)) by (intros f2 k2 Hin E; rewrite E in Hin; exact (FNI Hin)).
assert (Wfr : Forall (fun fk => (snd fk = 0%nat \/ snd fk = 2%nat \/ snd fk = 4%nat \/ snd fk = 5%nat \/ snd fk = 8%nat)
/\ exists q, 0 <= q < NF (Z.of_nat (snd fk)) /\ fst fk = frame_addr FSB (Z.of_nat (snd fk)) q
/\ nth (Z.to_nat q) (fss_flags (fs_of (fs_release Σ k p fr) (snd fk))) 0 = 1) fr).
{ apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & p2 & Hp2 & Hf2 & Hb2).
cbn [fst snd] in *. split; [exact Hk2|]. exists p2. split; [exact Hp2|]. split; [exact Hf2|].
unfold fs_release. rewrite (fs_of_set Σ k _ fr k2 Hk Hk2). destruct (Nat.eqb_spec k k2) as [<-|Hne]; [|exact Hb2].
cbn [fss_flags]. rewrite nth_upd_other; [exact Hb2|]. intros E. apply (Hfr f2 k Hin).
assert (p2 = p) by (apply Z2Nat.inj; [lia | lia | symmetry; exact E]). subst p2. rewrite Hf2, Hf. reflexivity. }
split; [exact W1|]. split; [exact W2|]. split; [exact W3|]. split; [exact W4|]. split; [exact W5|].
split; [|split; [exact W7|split; [exact W8|split; [exact W9 | exact W10]]]].
assert (CNT' : forall k', (k' = 0 \/ k' = 2 \/ k' = 4 \/ k' = 5 \/ k' = 8)%nat ->
Z.of_nat (nbusy (fss_flags (fs_of (fs_release Σ k p fr) k'))) = Z.of_nat (length (List.filter (fun fk => Nat.eqb (snd fk) k') fr))).
{ intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). pose proof (FCNT k' Hk') as Ck. rewrite HF in Ck.
rewrite (filter_cons_class f k fr k') in Ck. destruct (Nat.eqb_spec k k') as [<-|Hne]; cbn [fss_flags].
- cbn [length] in Ck. pose proof (nbusy_upd1to0 (fss_flags (fs_of Σ k)) (Z.to_nat p) Hpl Hb) as X. lia.
- exact Ck. }
assert (HNT' : forall k', (k' = 0 \/ k' = 2 \/ k' = 4 \/ k' = 5 \/ k' = 8)%nat -> fss_hint (fs_of (fs_release Σ k p fr) k') <= 2 ^ 14 * (CREDIT0 - credit (fs_release Σ k p fr))).
{ intros k' Hk'. unfold fs_release. rewrite (fs_of_set Σ k _ fr k' Hk Hk'). cbn [credit fs_set]. pose proof (FHINT k' Hk') as Hh.
destruct (Nat.eqb_spec k k') as [<-|Hne]; [cbn [fss_hint]; exact Hh | exact Hh]. }
split; [|split; [|split; [|split; [exact Wfr|split; [apply NoDup_ListNoDup; exact FND | split; [cbn [length] in FLN; cbn [frames fs_release fs_set]; lia|split; [exact CNT' | exact HNT']]]]]]].
all: unfold fs_release, fs_set; destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn [fs0 fs2 fs4 fsc];
first [exact Wg' | assumption | (split; [first [exact Wg' | assumption]| split; first [exact Wg' | assumption]])].
Qed.

Lemma sf_fs_rep : fs_rep (fs_release Σ k p fr) m'.
Proof using HA HF Hk Hp Hf Hb Hlo Husp MU WM P_flags.
pose proof sf_cls as Hc. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & Hfl01).
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof (ART_wf Σ m HA) as (_ & _ & _ & _ & _ & W6 & _).
pose proof W6 as (_ & _ & _ & FWr & FND & _). apply NoDup_ListNoDup in FND. rewrite HF in FND, FWr.
apply NoDup_cons_iff in FND as [FNI FND]. apply Forall_cons_iff in FWr as [_ FWr].
pose proof (ART_fs Σ m HA) as FS. pose proof (fs_rep_cls Σ m k FS Hk) as (CH & CF & CFr).
destruct FS as (F1 & _ & _ & _ & FT & (dtvbeg & Hdb & TG) & (tb & te & TT) & FB). unfold fs_busy in FB. rewrite HF in FB.
apply Forall_cons_iff in FB as [FB0 FBr].
destruct FB0 as (p0 & Hf0 & FWr0 & FWs0 & _). cbn [fst snd] in *.

assert (CLSo : forall c, (c = 0 \/ c = 2 \/ c = 4 \/ c = 5 \/ c = 8)%nat -> c <> k -> fs_cls_rep FSB (Z.of_nat c) (fs_of Σ c) m').
{ intros c Hcc Hne. pose proof (fs_rep_cls Σ m c (ART_fs Σ m HA) Hcc) as X. pose proof (rel_flags_ok Σ m HA c Hcc) as (Lc & _).
assert (Hc2 : Z.of_nat c = 0 \/ Z.of_nat c = 2 \/ Z.of_nat c = 4 \/ Z.of_nat c = 5 \/ Z.of_nat c = 8) by (destruct Hcc as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
assert (HcK : Z.of_nat c <> K) by lia.
apply (fs_cls_rep_transport _ _ _ _ m m' X MU WM). split; [|split].
- apply dsf_head; destruct Hc2 as [E|[E|[E|[E|E]]]]; rewrite E; lia.
- rewrite Lc. exact (dsf_flags _ Hc2 HcK).
- intros q Hq _. split; [exact (dsf_frame _ q Hc2 Hq) | exact (dsf_shad _ q Hc2 Hq (or_introl HcK))]. }

assert (CLSk : fs_cls_rep FSB K g' m').
{ split; [|split].
- unfold fs_hint in *. apply (rw_cells_transport asegs _ m m' _ _ CH MU WM). cbn [cells_size csize Nat.add].
apply dsf_head; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; lia.
- exact P_flags.
- intros q Hq Hq0. cbn [fss_flags] in Hq0. destruct (Z.eq_dec q p) as [->|Hne].
+ rewrite <- Hf. assert (Hsz : fsz K = fs_size k) by (symmetry; apply fs_size_fsz).
assert (Hpos : 0 < fs_size k) by (rewrite <- Hsz; unfold fsz; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
split.
* pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWr0 WM) ltac:(lia)) as St.
destruct (stk_bytes asegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (f + fs_size k - f) with (fs_size k) in Hl by lia; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWr0 WM).
* assert (Hs8 : 0 <= fs_size k / 8) by (apply Z.div_pos; lia).
pose proof (wr_at_stk m' _ _ (wr_at_wmono m m' _ _ FWs0 WM) Hs8) as St.
destruct (stk_bytes asegs m' _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs. rewrite Hsz.
split; [split; [cbn; split; [rewrite Hl; f_equal; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; replace (shad f + fs_size k / 8 - shad f) with (fs_size k / 8) in Hl by lia; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono m m' _ _ FWs0 WM).
+ rewrite nth_upd_other in Hq0 by (intros E; apply Hne; apply Z2Nat.inj; [lia | lia | symmetry; exact E]).
destruct (CFr q Hq Hq0) as [(j1 & J1) (j2 & J2)].
assert (Z0 : 0 <= fsz K) by (unfold fsz; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
assert (Z8 : 0 <= fsz K / 8) by (apply Z.div_pos; lia).
split; [exists j1; apply (rw_cells_transport asegs _ m m' _ _ J1 MU WM) | exists j2; apply (rw_cells_transport asegs _ m m' _ _ J2 MU WM)];
cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia;
[exact (dsf_frame _ q Hc Hq) | exact (dsf_shad _ q Hc Hq (or_intror Hne))]. }
assert (DIMG : forall a n, a + n <= SEGTOP_A -> disjoint_from (sf_W K FSB p usp) a n).
{ intros a n H. apply dsf_gen; [lia | unfold SHB, SEGTOP_A in *; lia | lia]. }
assert (F1' : fs_const FSB m').
{ unfold fs_const in *. apply (rw_cells_transport asegs _ m m' _ _ F1 MU WM). cbn [cells_size csize Nat.add]. apply dsf_head; lia. }
assert (T' : rw_cells asegs m' tpA [C8 (Z_to_bv 64 FSB)]).
{ apply (rw_cells_transport asegs _ m m' _ _ FT MU WM). apply DIMG. unfold tpA, SEGTOP_A. cbn. lia. }
assert (TG' : tga_cells (l_DTV L) dtvbeg m').
{ unfold tga_cells, dtls_cells in *. destruct TG as (G1' & G2' & G3' & G4' & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8)).
repeat (split; [eapply (rw_cells_transport asegs _ m m'); [eassumption | exact MU | exact WM | apply DIMG;
unfold g_real_tls_get_addr, g_dtv_ptr, g_dtv1, X0j4.g_got_common_flags, g_intercept_tls_get_addr, g_got_verbosity,
g_current_verbosity, g_tls_index, g_got_dtls_off, g_tls_dtls, SEGTOP_A; cbn; lia]|]).
apply (rw_cells_transport asegs _ m m' _ _ D8 MU WM). cbn [cells_size csize Nat.add].
apply (dsf_grant 4%nat (l_DTV L) 4096); [lia | reflexivity | lia | lia]. }
assert (TT' : ttls_cells (l_T L) m' tb te).
{ unfold ttls_cells in *. apply (rw_cells_transport asegs _ m m' _ _ TT MU WM). cbn [cells_size csize Nat.add].
apply (dsf_grant 2%nat (l_T L) 4096); [lia | reflexivity | lia | lia]. }
assert (FB' : fs_busy L fr m').
{ unfold fs_busy. apply Forall_forall. intros [f2 k2] Hin. destruct (proj1 (Forall_forall _ _) FBr (f2, k2) Hin) as (q & Hq & Wq1 & Wq2 & Cq).
destruct (proj1 (Forall_forall _ _) FWr (f2, k2) Hin) as (Hk2 & q' & Hq' & Hf2 & _). cbn [fst snd] in *.
assert (Hc2 : Z.of_nat k2 = 0 \/ Z.of_nat k2 = 2 \/ Z.of_nat k2 = 4 \/ Z.of_nat k2 = 5 \/ Z.of_nat k2 = 8) by (destruct Hk2 as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
exists q. split; [exact Hq|]. split; [exact (wr_at_wmono m m' _ _ Wq1 WM)|]. split; [exact (wr_at_wmono m m' _ _ Wq2 WM)|].
apply (rw_cells_transport asegs _ m m' _ _ Cq MU WM). cbn [cells_size csize Nat.add].
pose proof (dsf_frame _ q' Hc2 Hq') as D1. rewrite <- Hf2 in D1. rewrite fs_size_fsz.
assert (8 <= fsz (Z.of_nat k2)) by (unfold fsz; destruct Hc2 as [E|[E|[E|[E|E]]]]; rewrite E; cbn; lia).
apply (dsj_sub _ f2 (fsz (Z.of_nat k2))); [exact D1 | lia | lia]. }
unfold fs_rep. cbn [lay fs_release fs_set frames].
destruct Hk as [E|[E|[E|[E|E]]]]; subst k; cbn [fs0 fs2 fs4 fsc];
(split; [exact F1'|]); (split; [first [exact CLSk | exact (CLSo 0%nat ltac:(lia) ltac:(lia))]|]);
(split; [first [exact CLSk | exact (CLSo 2%nat ltac:(lia) ltac:(lia))]|]); (split; [split; [first [exact CLSk | exact (CLSo 4%nat ltac:(lia) ltac:(lia))]| split; [first [exact CLSk | exact (CLSo 5%nat ltac:(lia) ltac:(lia))]| first [exact CLSk | exact (CLSo 8%nat ltac:(lia) ltac:(lia))]]]|]);
(split; [exact T'|]); (split; [exists dtvbeg; split; [exact Hdb | exact TG']|]); (split; [exists tb, te; exact TT' | exact FB']).
Qed.

Lemma sf_pois : rtA_pois (fs_release Σ k p fr) = rtA_pois Σ.
Proof using HF HPN.
clear - HF HPN.
unfold rtA_pois at 1. cbn [frames pois fs_release fs_set]. destruct fr as [|x fr']; [symmetry; exact (HPN eq_refl)|]. unfold rtA_pois. rewrite HF. reflexivity.
Qed.

Theorem sf_art : ART_A (fs_release Σ k p fr) m'.
Proof using HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM P_flags.
pose proof (ART_transport_but_fs _ Σ m m' HA sf_munch WM
(art_avoid_but_fs_app _ _ Σ (fsb_avoid Σ m HA) (art_avoid_but_fs_app _ _ Σ (fshad_avoid Σ m HA) (stack_avoid Σ m HA)))) as BF.
assert (BF' : ART_but_fs (fs_release Σ k p fr) m') by (unfold ART_but_fs in *; rewrite sf_pois; exact BF).
exact (ART_of_but_fs _ m' sf_wf BF' sf_fs_rep).
Qed.

Lemma sf_pres : rt_pres (live Σ) fr usp m m'.
Proof using HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM P_flags.
intros a Ha. apply MU. set (x := bv_unsigned a) in *.
pose proof sf_art as HA'. set (Σ' := fs_release Σ k p fr) in *.
pose proof sf_pieces as (P2 & P3 & P4 & P5 & P6 & P7 & P8). pose proof sf_cls as Hc.
pose proof (push_bounds Σ m HA) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9). pose proof (rel_flags_ok Σ m HA k Hk) as (Hfl & _).
assert (Hpl : (Z.to_nat p < length (fss_flags (fs_of Σ k)))%nat) by (apply Nat2Z.inj_lt; rewrite Hfl, Z2Nat.id by lia; lia).
assert (SP0 : rtA_sp0 Σ' = rtA_sp0 Σ) by reflexivity.
pose proof (art_avoid_client Σ' m' usp HA' ltac:(rewrite SP0; unfold l_ACEIL in Hlo; unfold rtA_sp0; lia)) as (_ & _ & _ & _ & _ & _ & _ & AF & _).
destruct AF as (_ & A0 & A2 & (A4 & A5 & A8) & _).
assert (EK : fs_of Σ' k = g') by (unfold Σ', fs_release; rewrite (fs_of_set Σ k _ fr k Hk Hk), Nat.eqb_refl; reflexivity).
assert (AK : fs_cls_avoid (W_client Σ' usp) FSB K g').
{ rewrite <- EK. change FSB with (l_FSB (lay Σ')). destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; assumption. }
destruct AK as (AK1 & AK2 & AK3). cbn [fss_flags] in AK2, AK3. rewrite upd_length, Hfl in AK2.
destruct (AK3 p Hp ltac:(rewrite (nth_indep_Z _ _ 1 0) by (rewrite upd_length; exact Hpl); apply nth_upd_same; exact Hpl)) as (AK4 & AK5).
rewrite <- Hf in AK4, AK5.
assert (STK : disjoint_from (W_client Σ' usp) (usp - 64) 64).
{ apply avoid_client_intro; [lia | apply dsj_CS_out; right; unfold l_ACEIL, STACK_WIN, SEGTOP_A in *; lia | | |].
- apply Forall_forall. intros [q n] Hin. destruct (rta_live_range Σ' m' q n HA' Hin) as (_ & X & _). cbn [fst snd].
rewrite SP0 in X. unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ' m' HA' f2 k2 Hin) as (_ & X & _). cbn [fst snd].
rewrite SP0 in X. unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ' m' HA' f2 k2 Hin) as (X0 & X & _). cbn [fst snd].
rewrite SP0 in X.
assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
{ unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
right. unfold l_ACEIL, rtA_sp0 in *. lia. }
pose proof (W_client_cover Σ' usp x Ha) as NO.
unfold sf_W. cbn [outside].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK2); unfold fl_base in *; lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ AK5); rewrite Hf; lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ STK); lia | exact I].
Qed.

End SFree.

Lemma wr_at_cell : forall (m : mem) a (n : nat), wr_at asegs m a (Z.of_nat n) -> exists bs, rw_cells asegs m a [CB n bs].
Proof.
intros m a n H. pose proof (wr_at_stk m _ _ H ltac:(lia)) as St.
destruct (stk_bytes asegs m _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs.
split; [split; [cbn; split; [rewrite Hl; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact H.
Qed.

Lemma sf_pre : forall Σ m f k fr, ART_A Σ m -> frames Σ = (f, k) :: fr ->
(k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat /\ exists p, 0 <= p < NF (Z.of_nat k) /\ f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p
/\ nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1
/\ rw_cells asegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 (fl_base (l_FSB (lay Σ)) (Z.of_nat k) + p))]
/\ wr_at asegs m (shad f) (fs_size k / 8).
Proof.
intros Σ m f k fr HA HF. destruct (rel_slot Σ m f k fr HA HF) as (Hk & p & Hp & Hf & Hb).
split; [exact Hk|]. exists p. split; [exact Hp|]. split; [exact Hf|]. split; [exact Hb|].
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (ART_fs Σ m HA) as FS. destruct FS as (_ & _ & _ & _ & _ & _ & _ & FB). unfold fs_busy in FB. rewrite HF in FB.
apply Forall_cons_iff in FB as [FB0 _]. destruct FB0 as (p' & Hf' & _ & FWs0 & Cw). cbn [fst snd] in *.
rewrite Hf in Hf'. apply (frame_addr_inj _ _ _ _ Hc) in Hf'. subst p'. split; [exact Cw | exact FWs0].
Qed.

Lemma sf_finish : forall (Σ : rtsA) PMc (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m : mem)
(f : Z) (k : nat) (fr : list (Z * nat)) (p lo : Z) (Pm : machine_state -> Prop) c1,
ART_A Σ m -> frames Σ = (f, k) :: fr -> (fr = [] -> rtA_pois Σ = []) ->
(k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> 0 <= p < NF (Z.of_nat k) -> f = frame_addr (l_FSB (lay Σ)) (Z.of_nat k) p ->
nth (Z.to_nat p) (fss_flags (fs_of Σ k)) 0 = 1 ->
rtA_sp0 Σ - STACK_WIN <= lo -> lo + RT_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP ->
AST SEGTOP_A (rtA_allow Σ) Pm (fun mo => ARTM RTA Σ mo /\ PMc mo) c1 ->
(forall ms, Pm ms -> exists m',
ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ munch (sf_W (Z.of_nat k) (l_FSB (lay Σ)) p (bv_unsigned sp)) m m'
/\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
/\ fs_flags (l_FSB (lay Σ)) (Z.of_nat k) m' (upd (fss_flags (fs_of Σ k)) (Z.to_nat p) 0)) ->
exists (Σ' : rts RTA) (v : word),
ASTA RTA Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RTA Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RTA Σ) fr (bv_unsigned sp) m m') c1
/\ rt_frames RTA Σ' = fr /\ rt_live RTA Σ' = rt_live RTA Σ /\ rt_sp0 RTA Σ' = rt_sp0 RTA Σ /\ rt_credit RTA Σ' = rt_credit RTA Σ
/\ rt_pois RTA Σ' = rt_pois RTA Σ.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m f k fr p lo Pm c1 HA HF HPN Hk Hp Hf Hb LOW LOR SPT HAST HPm.
set (usp := bv_unsigned sp) in *.
assert (Hlo : l_ACEIL (lay Σ) <= lo) by (unfold l_ACEIL; unfold rtA_sp0 in LOW; lia).
assert (Husp : lo + 64 <= usp) by (unfold RT_STACK in LOR; lia).
assert (Husp2 : usp <= USTACK_TOP) by lia.
exists (fs_release Σ k p fr), v.
split; [|split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [reflexivity | exact (sf_pois Σ f k fr p HF HPN)]]]]].
unfold ASTA. change (rt_allow RTA (fs_release Σ k p fr)) with (rtA_allow Σ).
eapply AST_conseq; [exact HAST| |intros mo Hmo; exact Hmo].
intros ms HP. destruct (HPm ms HP) as (m' & RS & MU & WM & MI & ST' & PF).
exists m'. split; [exact RS|].
split; [split; [exact (sf_art Σ m m' f k fr p usp lo HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM PF) | split; [exact MI | split; [exact WM | exact ST']]]|].
exact (sf_pres Σ m m' f k fr p usp lo HA HF HPN Hk Hp Hf Hb Hlo Husp Husp2 MU WM PF).
Qed.

Theorem rta_stack_free_5 : stack_free_contract RTA 5.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR _ HPN ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sf_pre Σ m f 5%nat fr ART0 HFR) as (_ & p & Hp & Hf & Hb & LASTW & SHW).
destruct (sm_pre Σ m 5%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
change (Z.of_nat 5) with 5 in *. change (NF 5) with 512 in Hp. change (fs_size 5) with 2048 in *. change (2048 / 8) with (Z.of_nat 256) in SHW.
destruct (wr_at_cell m _ 256 SHW) as (shj & SHC).
assert (W1 : evt asegs (sf5_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p (fss_flags (fs_of Σ 5)) lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_free 5) m)).
{ unfold entry_st. rewrite Hf in LASTW, SHC |- *. replace (frame_addr (l_FSB (lay Σ)) 5 p + 2048 - 8) with (frame_addr (l_FSB (lay Σ)) 5 p + 2040) in LASTW by lia.
exact (stack_free_5_spec ra sp gp tp t0 t1 t2 s0 s1 _ a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) p (fss_flags (fs_of Σ 5)) lo shj eq_refl Hp FL OK LASTW SHC M2S FSOK HLO FSL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sf5_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1). apply AST_exI in Hc1 as (a0' & Hc1).
apply (sf_finish Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0' m f 5%nat fr p lo _ c1 ART0 HFR HPN ltac:(lia)
ltac:(change (NF (Z.of_nat 5)) with 512; lia) Hf Hb LOW LOR SPT Hc1).
intros ms HP.
destruct HP as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PF & _).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [|split; [exact WM|split; [exact MI|split; [exact ST' | exact PF]]]].
apply (munch_weaken (sf5_W (l_FSB (lay Σ)) p (bv_unsigned sp))); [|exact MU].
intros x Hx. unfold sf_W in Hx. unfold sf5_W. change (Z.of_nat 5) with 5 in Hx. change (fsz 5 / 8) with 256 in Hx. cbn [outside] in *.
destruct Hx as (X1 & X2 & X3 & _). split; [exact X1|]. split; [exact X2|]. split; [lia | exact I].
Qed.

Theorem rta_stack_free_8 : stack_free_contract RTA 8.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR HSZ HPN ART0 MI0 CALL.
destruct (HSZ eq_refl) as (-> & SZ8 & SZR). change (fs_size 8) with 16384 in SZR.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
pose proof CALL as (ST & LOW & LOR & SPT & SPA).
destruct (sf_pre Σ m f 8%nat fr ART0 HFR) as (_ & p & Hp & Hf & Hb & LASTW & SHW).
destruct (sm_pre Σ m 8%nat lo ART0 ltac:(lia) LOW) as (FC & FH & FL & OK & NB & HH & FF & TLS & (dtvbeg & Hdb & TGA) & TC & (tb & te & TT)
& M2S & FSOK & HLO & FSL & HD & HDL & HX & HXL & HT & HTL).
change (Z.of_nat 8) with 8 in *. change (NF 8) with 64 in Hp. change (fs_size 8) with 16384 in *. change (16384 / 8) with 2048 in SHW.
assert (SZD : 0 <= size / 8 <= 2048) by (Z.div_mod_to_equations; lia).
assert (SHW' : wr_at asegs m (shad f) (Z.of_nat (Z.to_nat (size / 8)))).
{ rewrite Z2Nat.id by lia. destruct SHW as (W0 & W1 & W2). split; [exact W0|]. split; [lia|]. intros i Hi. apply W2. lia. }
destruct (wr_at_cell m _ _ SHW') as (shj & SHC).
assert (W1 : evt asegs (sf8_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (l_FSB (lay Σ)) p size (fss_flags (fs_of Σ 8)) lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc (e_stack_free 8) m)).
{ unfold entry_st. rewrite Hf in LASTW, SHC |- *. replace (frame_addr (l_FSB (lay Σ)) 8 p + 16384 - 8) with (frame_addr (l_FSB (lay Σ)) 8 p + 16376) in LASTW by lia.
assert (HLO8 : 0x10007fff8008 <= lo) by (pose proof (rta_sp0_win Σ m ART0) as Hw; pose proof LOW as LOW'; cbn [rt_sp0 RTA] in LOW'; unfold STACK_WIN in LOW'; lia).
pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (ART_consts Σ m ART0)))))) as PS.
exact (stack_free_8_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(l_FSB (lay Σ)) p size (fss_flags (fs_of Σ 8)) lo shj eq_refl eq_refl Hp SZ8 SZR PS FL OK LASTW SHC FSOK HLO8 FSL ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold USTACK_TOP in *; lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (sm_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold sf8_post in Hc1.
apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1). apply AST_exI in Hc1 as (a0' & Hc1).
apply (sf_finish Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0' m f 8%nat fr p lo _ c1 ART0 HFR HPN ltac:(lia)
ltac:(change (NF (Z.of_nat 8)) with 64; lia) Hf Hb LOW LOR SPT Hc1).
intros ms HP.
destruct HP as (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PF & _).
exists m'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split; [|split; [exact WM|split; [exact MI|split; [exact ST' | exact PF]]]].
apply (munch_weaken (sf8_W (l_FSB (lay Σ)) p (bv_unsigned sp))); [|exact MU].
intros x Hx. unfold sf_W in Hx. unfold sf8_W. change (Z.of_nat 8) with 8 in Hx. change (fsz 8 / 8) with 2048 in Hx. exact Hx.
Qed.

Theorem rta_stack_free : forall k, (k = 5 \/ k = 6 \/ k = 8)%nat -> stack_free_contract RTA k.
Proof.
intros k [ -> | [ -> | -> ] ]; [exact rta_stack_free_5 | | exact rta_stack_free_8].
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f fr lo size
FDO MST Hk -> HFR _ HPN ART0 MI0 CALL.
cbn [ART rt_frames RTA] in *. unfold rtA_frames in *.
destruct (rel_slot Σ m f 6%nat fr ART0 HFR) as (Hk6 & _). lia.
Qed.
