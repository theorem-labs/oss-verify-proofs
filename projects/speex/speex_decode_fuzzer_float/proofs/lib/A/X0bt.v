(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X0j1 X0gi X0hr X0hb
X0il X0gp X0h2 X0j4 X0hf X0j3 X0hi X0fy X0fg X0da X0g4 X0d8 X0fq X04b
X0d7 X0ff X0h3 X0hn X0j0 X0g6 X0g7 X0ej X0fv X0fr.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X173 X18c X17w X196 X17a X17n X19n X180 X19m X183 X16j X161 X13v X16p X13t X16b X0v9 X13s X160 X17o X188 X19k X16r X16s X154 X16g X16c.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19n OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X180 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X160 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17o OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19k OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16r OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16s OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X154 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16c.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W_ss (hlo hhi usp N : Z) : list (Z * Z) := [(shad hlo, shad hhi); (usp - N, usp)].

Definition pois_set (Σ : rtsA) (P : list (Z * Z)) : rtsA :=
mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fsc Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ) P.

Lemma shad_mono : forall x y, x <= y -> shad x <= shad y.
Proof. intros x y H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Section StkShadow.
Variables (Σ : rtsA) (m m' : mem) (hlo hhi usp N : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation W := (W_ss hlo hhi usp N).
Hypothesis Hh1 : l_ACEIL L <= hlo.
Hypothesis Hh3 : hhi <= 2 ^ 47.
Hypothesis HN : l_ACEIL L <= usp - N.
Hypothesis Husp : usp <= USTACK_TOP.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma ss_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ l_ACEIL L mod 8 = 0 /\ SEGTOP_A <= l_ACEIL L.
Proof using HA.
clear - HA. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. pose proof (rta_sp0 Σ m HA) as (_ & X3).
split; [unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia|]. split; [unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia|].
split; [|unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia].
unfold rtA_sp0 in X3. unfold l_ACEIL, STACK_WIN. apply Z.mod_divide in X3; [|lia]. destruct X3 as [q Hq]. rewrite Hq.
replace (q * 16 - 8388608) with ((2 * q - 1048576) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma ss_off : forall a n, (a + n <= shad (l_ACEIL L) \/ shad (2 ^ 47) <= a) -> (a + n <= l_ACEIL L \/ USTACK_TOP <= a) -> disjoint_from W a n.
Proof using Hh1 Hh3 HN Husp.
clear - Hh1 Hh3 HN Husp. intros a n H1 H2. pose proof (shad_mono _ _ Hh1) as S1. pose proof (shad_mono _ _ Hh3) as S2.
unfold W_ss. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ss_shad_aceil : shad (l_ACEIL L) = l_ACEIL L / 8 + SHB /\ SHB <= shad (l_ACEIL L) /\ shad (2 ^ 47) = 2 ^ 44 + SHB.
Proof using HA. clear - HA. pose proof ss_aceil as (A1 & A2 & A3 & A4). unfold shad. split; [reflexivity|]. split; [|reflexivity].
pose proof (Z.div_pos (l_ACEIL L) 8 ltac:(unfold SHB in *; lia) ltac:(lia)). lia. Qed.

Lemma ss_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2 _. pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof ss_shad_aceil as (_ & S0 & _).
apply ss_off; unfold SEGTOP_A, SHB in *; lia.
Qed.

Lemma ss_granted : forall b gn a n, grant_ok L b gn -> b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros b gn a n (G1 & G2 & G3 & G4 & G5) H1 H2. pose proof ss_shad_aceil as (_ & S0 & S1).
apply ss_off; [|lia]. rewrite S1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma ss_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp. intros b gn a n Hin _ _ H1 H2. exact (ss_granted b gn a n (geo_grant Σ m HA b gn Hin) H1 H2). Qed.

Lemma ss_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
(forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
(hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> hi <= l_ACEIL L -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros lo hi a n _ _ H0 H47 H1 H2 _ _ HC. pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof (shad_mono _ _ HC) as S1. pose proof (shad_mono _ _ H47) as S2.
pose proof ss_shad_aceil as (_ & _ & S3). apply ss_off; lia.
Qed.

Lemma ss_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
(forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
a + n <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2 _. exact (ss_granted _ _ a n (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) H1 H2).
Qed.

Lemma ss_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
(s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros k0 s0 a n Hk H1 H2 _. destruct (X16b.map_geo Σ m HA k0 s0 Hk) as (_ & G & _). exact (ss_granted _ _ a n G H1 H2).
Qed.

Lemma ss_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2. exact (ss_granted _ _ a n (fsb_grant Σ m HA) H1 H2).
Qed.

Lemma ss_fshad : forall a n, shad (l_FSB L) <= a -> a + n <= shad (l_FSB L + 0xb09000) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2. pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof ss_aceil as (A1 & A2 & A3 & A4).
pose proof (shad_mono _ _ G3) as S1. pose proof (shad_mono _ _ A2) as S2. pose proof ss_shad_aceil as (_ & _ & S3). apply ss_off; lia.
Qed.

Lemma ss_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using HA Hh1 Hh3 HN Husp.
intros k Hk. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & _).
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (push_bounds Σ m HA) as (B1 & B2 & _). pose proof (flags_range _ Hc) as (F1 & F2).
split; [apply ss_fsb; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; lia|].
split; [rewrite Hlen; apply ss_fsb; unfold fl_base; lia|].
intros p Hp _. pose proof (frame_addr_range (l_FSB L) _ p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2.
pose proof (frame_shad_in2 (l_FSB L) _ p B2 Hc Hp) as (S1 & S2).
split; [apply ss_fsb; lia | apply ss_fshad; lia].
Qed.

Lemma ss_fs : fs_avoid W Σ.
Proof using HA Hh1 Hh3 HN Husp.
pose proof (fsb_grant Σ m HA) as (G1 & _).
unfold fs_avoid. split; [apply ss_fsb; lia|].
split; [exact (ss_fs_cls 0%nat ltac:(lia))|]. split; [exact (ss_fs_cls 2%nat ltac:(lia))|].
split; [split; [exact (ss_fs_cls 4%nat ltac:(lia))| split; [exact (ss_fs_cls 5%nat ltac:(lia))| exact (ss_fs_cls 8%nat ltac:(lia))]]|].
split; [apply (X16c.ac_lits W ss_img); vm_compute; reflexivity|].
split; [apply (ss_granted (l_DTV L) 4096); [exact (geo_grant Σ m HA _ _ ltac:(unfold startup_grants; do 4 right; left; reflexivity)) | lia | lia]|].
split; [apply (ss_granted (l_T L) 4096); [exact (geo_grant Σ m HA _ _ ltac:(unfold startup_grants; do 2 right; left; reflexivity)) | lia | lia]|].
apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X & Y & Z0). apply ss_fsb; lia.
Qed.

Lemma ss_but_shadow : consts_rep L m' /\ prim_rep Σ m' /\ cache_rep Σ m' /\ chunk_rep Σ m' /\ sec_rep Σ m' /\ quar_rep Σ m'
/\ dep_rep L (dep Σ) m' /\ fs_rep Σ m' /\ ia_rep Σ m' /\ vis_rep L (rtA_allow Σ) m'.
Proof using HA Hh1 Hh3 HN Husp MU WM.
pose proof (ART_wf Σ m HA) as Hwf.
pose proof (X16c.av_consts Σ m W HA ss_img ss_grant) as A1.
pose proof (X16c.av_reg Σ m W HA ss_grant ss_shad ss_prb) as A2.
pose proof (X16c.av_pchunk Σ m W HA ss_shad ss_prb) as A3.
pose proof (X16c.av_schunk Σ m W HA ss_shad ss_secmap) as A4.
pose proof (X16c.av_sec Σ m W HA ss_img ss_grant) as A5.
pose proof (X16c.av_quar Σ m W HA ss_img ss_grant ss_prb) as A6.
pose proof (X16c.av_dep Σ m W HA ss_img ss_grant) as A7.
pose proof (X16c.av_ia W ss_img) as A9.
split; [exact (consts_rep_transport W _ m m' (ART_consts Σ m HA) MU WM A1)|].
split; [intros c Hc; exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (A2 c Hc)))|].
split; [intros c Hc; exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (A2 c Hc)))|].
split; [destruct (ART_chunk Σ m HA) as [P S]; split;
[intros c i st Hc Hn; exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn))
| intros k s Hk; exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk))]|].
split; [exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM A5)|].
split; [exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM A6)|].
split; [destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _); exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM A7)|].
split; [exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM ss_fs)|].
split; [exact (ia_rep_transport W Σ m m' (ART_ia Σ m HA) MU WM A9)|].
exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

Theorem ss_art : forall Pr, stack_shadow_rep L (rtA_pois (pois_set Σ Pr)) m' -> ART_A (pois_set Σ Pr) m'.
Proof using HA Hh1 Hh3 HN Husp MU WM.
intros Pr SSR. pose proof ss_but_shadow as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C11).
pose proof (ART_shadow Σ m HA) as (_ & S1 & S2 & SA).
apply (ART_intro (pois_set Σ Pr) m' (ART_wf Σ m HA) C1 C2 C3 C4 C5 C6 C7 C8 C9); [|exact C11].
split; [exact SSR|]. split; [exact (stk_wmono m m' _ _ S1 WM)|]. split; [exact (stk_wmono m m' _ _ S2 WM)|].
pose proof (X16c.av_static_shad Σ m W HA ss_shad) as AS.
unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
pose proof (proj1 (Forall_forall _ _) AS r Hr) as D. cbv beta in X, D.
assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
Qed.

Lemma ss_pres : 0 <= N -> rt_pres (live Σ) (frames Σ) usp m m'.
Proof using HA Hh1 Hh3 HN Husp MU.
intros HN0 a Ha. apply MU. set (x := bv_unsigned a) in *.
pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof ss_shad_aceil as (S0 & _ & S1).
assert (Hsp : rtA_sp0 Σ - STACK_WIN <= usp) by (unfold l_ACEIL in HN; unfold rtA_sp0; lia).
pose proof (art_avoid_client Σ m usp HA Hsp) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (ASH & _)).
assert (E : shad (l_ACEIL L) + Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8) = shad (2 ^ 47)).
{ apply Z.mod_divide in A3; [|lia]. destruct A3 as [q Hq]. unfold shad. rewrite Hq, Z.div_mul by lia.
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. change (2 ^ 47 / 8) with (2 ^ 44). lia. }
assert (STK : disjoint_from (W_client Σ usp) (usp - N) N).
{ apply avoid_client_intro; [lia | apply dsj_CS_out; right; unfold l_ACEIL, STACK_WIN, SEGTOP_A in *; lia | | |].
- apply Forall_forall. intros [q n] Hin. destruct (rta_live_range Σ m q n HA Hin) as (_ & X & _). cbn [fst snd].
unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (_ & X & _). cbn [fst snd].
unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (X0 & X & _). cbn [fst snd].
assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
{ unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
right. unfold l_ACEIL, rtA_sp0 in *. lia. }
pose proof (W_client_cover Σ usp x Ha) as NO. pose proof (shad_mono _ _ Hh1) as M1. pose proof (shad_mono _ _ Hh3) as M2.
unfold W_ss. cbn [outside].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ ASH); lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ STK); lia | exact I].
Qed.

End StkShadow.

Lemma shad_add8 : forall x k, shad (x + 8 * k) = shad x + k.
Proof. intros x k. unfold shad. replace (x + 8 * k) with (x + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma shad_lt_al : forall a b, b mod 8 = 0 -> a < b -> shad a < shad b.
Proof.
intros a b Hb H. unfold shad. apply Z.mod_divide in Hb; [|lia]. destruct Hb as [q ->]. rewrite Z.div_mul by lia.
assert (a / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma shad_top : forall a, a < 2 ^ 47 -> shad a < 2 ^ 44 + SHB.
Proof. intros a H. unfold shad. assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma alloca_rr_ap : forall A n, alloca_rr A n = ap_rr A n + 32.
Proof. reflexivity. Qed.

Lemma ap_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.

Lemma mod32_8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with (4 * q * 8) by lia. apply Z.mod_mul. lia. Qed.

Definition ap_W (A n usp : Z) : list (Z * Z) :=
[(shad (A - 32), shad (A - 32) + 4); (shad (A + n), shad (ap_rr A n) + 4); (usp - 64, usp)].

Section AllocaPoison.
Variables (Σ : rtsA) (m m' : mem) (A n usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis HA32 : A mod 32 = 0.
Hypothesis Hn : 0 <= n.
Hypothesis Hsp : usp <= A - 32.
Hypothesis Htop : alloca_rr A n <= USTACK_TOP - 16.
Hypothesis HPA : pois_above P (alloca_rr A n).
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (ap_W A n usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis P_part : (A + n) mod 8 <> 0 -> rw_cells bsegs m' (shad (A + n)) [C1 (Z_to_bv 8 ((A + n) mod 8))].

Lemma ap_geo : (A - 32) mod 8 = 0 /\ alloca_rr A n mod 32 = 0 /\ A + n < alloca_rr A n /\ shad (A - 32) + 4 = shad A
/\ shad (ap_rr A n) + 4 = shad (alloca_rr A n) /\ shad A <= shad (A + n) /\ shad (A + n) < shad (alloca_rr A n).
Proof using HA32 Hn.
clear - HA32 Hn. pose proof (alloca_rr_bounds A n) as (RB & RM). pose proof (mod32_8 _ RM) as R8.
split; [rewrite Zminus_mod, (mod32_8 _ HA32); reflexivity|]. split; [exact RM|]. split; [lia|].
split; [replace A with (A - 32 + 8 * 4) at 2 by lia; rewrite shad_add8; lia|].
split; [rewrite alloca_rr_ap; replace (ap_rr A n + 32) with (ap_rr A n + 8 * 4) by lia; rewrite shad_add8; lia|].
split; [apply shad_mono; lia | apply shad_lt_al; [exact R8 | lia]].
Qed.

Lemma ap_munch : munch (W_ss (A - 32) (alloca_rr A n) usp 64) m m'.
Proof using HA32 Hn MU.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
apply (munch_weaken (ap_W A n usp)); [|exact MU].
intros x Hx. unfold W_ss in Hx. unfold ap_W. cbn [outside] in *. destruct Hx as (X1 & X2 & _).
pose proof (shad_mono (A - 32) (A + n) ltac:(lia)) as S1.
split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_dsj : forall s k, (s + k <= shad (A - 32) \/ shad (alloca_rr A n) <= s) -> s + k <= 2 ^ 44 + SHB -> disjoint_from (ap_W A n usp) s k.
Proof using HA HA32 Hn Husp.
intros s k H1 H2. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & _).
pose proof (shad_mono (A - 32) (A + n) ltac:(lia)) as S1.
unfold ap_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_dsj_mid : forall s, shad A <= s < shad (A + n) -> disjoint_from (ap_W A n usp) s 1.
Proof using HA HA32 Hn Husp Htop.
intros s Hs. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & _).
pose proof (shad_top (A + n) ltac:(unfold USTACK_TOP in Htop; lia)) as T1.
unfold ap_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_acc_new : acc bsegs m' A n.
Proof using HA HA32 Hn Hsp Htop HPA Husp MU P_part.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
intros i Hi. destruct (Z_lt_le_dec (shad (A + i)) (shad (A + n))) as [Hlt|Hge].
-
exists z8. split; [|left; reflexivity].
assert (Hz : bytes_at bsegs m (shad (A + i)) [z8]).
{ apply Z0; [unfold USTACK_TOP in *; lia|]. intros (e & He & E1 & E2). specialize (HPA e He). lia. }
apply (bytes_at_transport bsegs _ m m' _ _ Hz MU). change (Z.of_nat (length [z8])) with 1.
apply ap_dsj_mid. split; [apply shad_mono; lia | exact Hlt].
-
assert (E : shad (A + i) = shad (A + n)) by (pose proof (shad_mono (A + i) (A + n) ltac:(lia)); lia).
assert (K : (A + n) mod 8 <> 0).
{ intros K0. pose proof (shad_lt_al (A + i) (A + n) K0 ltac:(lia)). lia. }
exists (Z_to_bv 8 ((A + n) mod 8)). rewrite E.
split; [destruct (P_part K) as [[_ PB] _]; cbn [cells_bytes cbytes app] in PB; exact PB|].
pose proof (Z.mod_pos_bound (A + n) 8 ltac:(lia)) as B. right. rewrite ap_lit8 by lia. split; [lia|].
unfold shad in E. assert (E' : (A + i) / 8 = (A + n) / 8) by lia.
pose proof (Z.div_mod (A + i) 8 ltac:(lia)). pose proof (Z.div_mod (A + n) 8 ltac:(lia)). lia.
Qed.

Lemma ap_ssr : stack_shadow_rep L ((A, n) :: P) m'.
Proof using HA HA32 Hn Hsp Htop HPA Husp MU P_part.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
assert (Hno : ~ in_pois P a) by (intros (e & He & E); apply Hnp; exists e; split; [right; exact He | exact E]).
assert (Hnh : a < A - 32 \/ alloca_rr A n <= a).
{ destruct (Z_lt_le_dec a (A - 32)) as [X|X]; [left; exact X|]. destruct (Z_lt_le_dec a (alloca_rr A n)) as [Y|Y]; [|right; exact Y].
exfalso. apply Hnp. exists (A, n). split; [left; reflexivity|]. unfold pz_lo, pz_hi. cbn [fst snd]. lia. }
apply (bytes_at_transport bsegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1.
apply ap_dsj; [|lia]. destruct Hnh as [X|X]; [left; pose proof (shad_lt_al a (A - 32) G1 X); lia | right; apply shad_mono; exact X].
- apply Forall_cons; [exact ap_acc_new|].
apply Forall_forall. intros [a0 n0] He. pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4). specialize (HPA _ He).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply ap_dsj; [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_cons; [|exact WF1]. cbn [fst snd]. unfold pz_lo, pz_hi. cbn [fst snd]. split; [exact HA32|]. split; [exact Hn|]. split; [lia | exact Htop].
+ apply FOP_cons; [|exact WF2]. apply Forall_forall. intros e He. specialize (HPA e He). unfold pz_hi at 1. cbn [fst snd]. exact HPA.
Qed.

Lemma ap_acc_tr : forall o k, acc bsegs m o k -> o + k <= USTACK_TOP -> o + k <= A - 32 \/ alloca_rr A n <= o -> acc bsegs m' o k.
Proof using HA HA32 Hn Husp MU.
intros o k H HT Hoff. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
destruct (Z_le_gt_dec k 0) as [K0|K0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ H MU ltac:(lia)).
pose proof (shad_top (o + k - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply ap_dsj; [|lia]. destruct Hoff as [X|X]; [left; pose proof (shad_lt_al (o + k - 1) (A - 32) G1 ltac:(lia)); lia | right; apply shad_mono; exact X].
Qed.

End AllocaPoison.

Lemma ss_stk_sub : forall (m : mem) lo hi a b, stk bsegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk bsegs m a b.
Proof. intros m lo hi a b (H0 & H1 & H) Ha Hab Hb. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma ss_stk_cell : forall (m : mem) a (n : nat), stk bsegs m a (a + Z.of_nat n) -> exists bs, rw_cells bsegs m a [CB n bs].
Proof.
intros m a n St. pose proof (stk_wr_at' m a _ St) as H.
destruct (stk_bytes bsegs m _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs.
split; [split; [cbn; split; [rewrite Hl; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact H.
Qed.

Lemma ss_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Lemma ss_pre : forall Σ m (sp : word) lo, ART_A Σ m -> call_ok RTA Σ m sp lo ->
m2s_cells m /\ setshadow_cells m /\ rw_cells bsegs m 0xfc110 [C8 (Z_to_bv 64 0x1032b8)] /\ rw_cells bsegs m (0x1032b8 + 85) [C1 (Z_to_bv 8 1)]
/\ stk bsegs m (shad (l_ACEIL (lay Σ))) (shad (2 ^ 47))
/\ l_ACEIL (lay Σ) <= lo /\ lo + RT_STACK <= bv_unsigned sp /\ bv_unsigned sp + 16 <= USTACK_TOP /\ stk bsegs m lo (bv_unsigned sp)
/\ 2 ^ 44 + SHB <= l_ACEIL (lay Σ) /\ l_ACEIL (lay Σ) <= 2 ^ 47 /\ l_ACEIL (lay Σ) mod 8 = 0 /\ SEGTOP_A <= l_ACEIL (lay Σ).
Proof.
intros Σ m sp lo HA (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & PS & _ & _ & ICR).
destruct ICR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22
& X23 & X24 & X25 & X26 & _).
destruct PS as (_ & _ & SS & _). destruct (ART_shadow Σ m HA) as (_ & S1 & _).
pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
split; [exact M2S|]. split; [exact SS|]. split; [exact X23|]. split; [exact X26|]. split; [exact S1|].
split; [unfold l_ACEIL; lia|]. split; [exact LOR|]. split; [exact SPT|]. split; [exact ST|].
split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.

Theorem rta_alloca_poison : alloca_poison_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo
FDO MST -> -> HA32 HSZ HSP HTOP HPA HFR ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & GF & PPF & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
pose proof (alloca_rr_bounds addr size) as (RB & RM). pose proof (mod32_8 _ RM) as R8.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
assert (G4 : shad (addr - 32) + 4 = shad addr) by (replace addr with (addr - 32 + 8 * 4) at 2 by lia; rewrite shad_add8; lia).
assert (G5 : shad (ap_rr addr size) + 4 = shad (alloca_rr addr size)) by (rewrite alloca_rr_ap; replace (ap_rr addr size + 32) with (ap_rr addr size + 8 * 4) by lia; rewrite shad_add8; lia).
assert (T1 : shad (alloca_rr addr size) <= 2 ^ 44 + SHB) by (pose proof (shad_mono (alloca_rr addr size) (2 ^ 47) ltac:(unfold USTACK_TOP in *; lia)) as X; unfold shad in X |- *; change (2 ^ 47 / 8) with (2 ^ 44) in X; lia).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad (addr - 32)) by (apply shad_mono; lia).
assert (B2 : shad (alloca_rr addr size) <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad addr <= shad (addr + size)) by (apply shad_mono; lia).
assert (B4 : shad (addr + size) < shad (alloca_rr addr size)) by (apply shad_lt_al; [exact R8 | lia]).
assert (HSUM : addr + size + 64 <= 2 ^ 47).
{ unfold alloca_rr, USTACK_TOP in HTOP. pose proof (Z.div_mod (addr + size + 31) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (addr + size + 31) 32 ltac:(lia)) as B.
set (q := (addr + size + 31) / 32) in *. lia. }
assert (SHL0 : stk bsegs m (shad (addr - 32)) (shad (addr - 32) + Z.of_nat 4)) by (apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad (addr - 32)) 4 SHL0) as (j1 & SHL).
assert (SHR : stk bsegs m (shad (addr + size)) (shad (ap_rr addr size) + 4)) by (apply (ss_stk_sub m _ _ _ _ SHS); lia).
assert (W1 : evt bsegs (alloca_poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_alloca_poison m)).
{ unfold entry_st.
exact (alloca_poison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo j1
eq_refl eq_refl HA32 HSZ ltac:(unfold SEGTOP_A, RT_STACK in *; lia) HSUM M2S SS GF PPF SHL SHR ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold alloca_poison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ ((addr, size) :: pois Σ)) = (addr, size) :: rtA_pois Σ).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); [contradiction HFR; reflexivity | reflexivity]. }
exists (pois_set Σ ((addr, size) :: pois Σ)).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ ((addr, size) :: pois Σ))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & _ & _ & PP).
assert (MU' : munch (W_ss (addr - 32) (alloca_rr addr size) usp 64) m m')
by exact (ap_munch m m' addr size usp HA32 ltac:(lia) MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' (addr - 32) (alloca_rr addr size) usp 64 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (ap_ssr Σ m m' addr size usp ART0 HA32 ltac:(lia) HSP HTOP HPA HUS MU PP). }
split; [exact (ss_pres Σ m m' (addr - 32) (alloca_rr addr size) usp 64 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
split; [exact (ap_acc_new Σ m m' addr size usp ART0 HA32 ltac:(lia) HSP HTOP HPA HUS MU PP)|].
intros o k Hacc HT Hoff. exact (ap_acc_tr Σ m m' addr size usp ART0 HA32 ltac:(lia) HUS MU o k Hacc HT Hoff).
Qed.

Definition au_W (top bottom usp : Z) : list (Z * Z) := [(shad top, shad top + (bottom - top) / 8); (usp - 32, usp)].

Lemma FOP_filter : forall {X} (R : X -> X -> Prop) (f : X -> bool) l, ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
intros X R f l H. induction H as [|x l Hx Hl IH]; cbn [List.filter]; [constructor|].
destruct (f x); [|exact IH]. apply FOP_cons; [|exact IH].
apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Section AllocasUnpoison.
Variables (Σ : rtsA) (m m' : mem) (top bottom usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis Htb : 0 < top <= bottom.
Hypothesis Ht8 : top mod 8 = 0.
Hypothesis Hb8 : bottom mod 8 = 0.
Hypothesis Hsp : usp <= top.
Hypothesis Hbt : bottom <= USTACK_TOP - 16.
Hypothesis HST : forall e, In e P -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e.
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (au_W top bottom usp) m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis P_zero : rw_cells bsegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma au_geo : shad top + (bottom - top) / 8 = shad bottom /\ 0 <= (bottom - top) / 8.
Proof using Htb Ht8 Hb8.
clear - Htb Ht8 Hb8. apply Z.mod_divide in Ht8, Hb8; try lia. destruct Ht8 as [q1 E1]. destruct Hb8 as [q2 E2]. unfold shad. rewrite E1, E2.
replace (q2 * 8 - q1 * 8) with ((q2 - q1) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.

Lemma au_munch : munch (W_ss top bottom usp 32) m m'.
Proof using Htb Ht8 Hb8 MU.
pose proof au_geo as (G1 & G2). apply (munch_weaken (au_W top bottom usp)); [|exact MU].
intros x Hx. unfold W_ss in Hx. unfold au_W. cbn [outside] in *. destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
Qed.

Lemma au_dsj : forall s k, (s + k <= shad top \/ shad bottom <= s) -> s + k <= 2 ^ 44 + SHB -> disjoint_from (au_W top bottom usp) s k.
Proof using HA Htb Ht8 Hb8 Husp.
intros s k H1 H2. pose proof au_geo as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & _).
unfold au_W. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma au_ssr : stack_shadow_rep L (pois_drop bottom P) m'.
Proof using HA Htb Ht8 Hb8 Hsp Hbt HST Husp MU P_zero.
pose proof au_geo as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
destruct (Z_lt_le_dec a top) as [X|X]; [|destruct (Z_lt_le_dec a bottom) as [Y|Y]].
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport bsegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_lt_al a top Ht8 X). apply au_dsj; lia.
+
destruct P_zero as [[_ PB] _]. cbn [cells_bytes cbytes] in PB. rewrite app_nil_r in PB.
assert (Hj : 0 <= shad a - shad top < (bottom - top) / 8).
{ pose proof (shad_mono top a X). pose proof (shad_lt_al a bottom Hb8 Y). lia. }
replace (shad a) with (shad top + Z.of_nat (Z.to_nat (shad a - shad top))) by (rewrite Z2Nat.id by lia; lia).
apply (bytes_at_nth1 bsegs m' _ _ _ _ PB). apply nth_error_repeat. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport bsegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_mono bottom a Y). apply au_dsj; lia.
- apply Forall_forall. intros [a0 n0] He. unfold pois_drop in He. apply filter_In in He as [He Hb]. apply Z.leb_le in Hb.
pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply au_dsj; [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_forall. intros e He. unfold pois_drop in He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) WF1 e He).
+ exact (FOP_filter _ _ _ WF2).
Qed.

Lemma au_acc_tr : forall o k, acc bsegs m o k -> o + k <= USTACK_TOP -> o + k <= top \/ bottom <= o -> acc bsegs m' o k.
Proof using HA Htb Ht8 Hb8 Husp MU.
intros o k H HT Hoff. destruct (Z_le_gt_dec k 0) as [K0|K0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ H MU ltac:(lia)).
pose proof (shad_top (o + k - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply au_dsj; [|lia]. destruct Hoff as [X|X]; [left; pose proof (shad_lt_al (o + k - 1) top Ht8 ltac:(lia)); lia | right; apply shad_mono; exact X].
Qed.

End AllocasUnpoison.

Theorem rta_allocas_unpoison : allocas_unpoison_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST -> -> HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & _ & _ & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
destruct (au_geo top bottom HTB HT8 HB8) as (G1 & G2).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad top) by (apply shad_mono; lia).
assert (B2 : shad bottom <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
assert (SHT0 : stk bsegs m (shad top) (shad top + Z.of_nat (Z.to_nat ((bottom - top) / 8)))) by (rewrite Z2Nat.id by lia; apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad top) _ SHT0) as (shj & SHC).
assert (W1 : evt bsegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) (Z_to_bv 64 bottom) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_allocas_unpoison m)).
{ unfold entry_st.
exact (allocas_unpoison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo shj
eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
ltac:(right; unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, SHB, RT_STACK in *; lia) M2S SS SHC ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold allocas_unpoison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ (pois_drop bottom (pois Σ))) = pois_drop bottom (rtA_pois Σ)).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); reflexivity. }
exists (pois_set Σ (pois_drop bottom (pois Σ))).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ (pois_drop bottom (pois Σ)))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PZ).
assert (MU' : munch (W_ss top bottom usp 32) m m') by exact (au_munch m m' top bottom usp HTB HT8 HB8 MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (au_ssr Σ m m' top bottom usp ART0 HTB HT8 HB8 HSP HBT HST HUS MU PZ). }
split; [exact (ss_pres Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
intros o k Hacc HT Hoff. exact (au_acc_tr Σ m m' top bottom usp ART0 HTB HT8 HB8 HUS MU o k Hacc HT Hoff).
Qed.

Theorem rta_allocas_unpoison_nop : allocas_unpoison_nop_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FDO MST HC MI0.
intros T cf Hc Hkont.
pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
assert (W1 : evt bsegs (fun ms' => exists (a2' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom bsegs))
(entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_allocas_unpoison m)).
{ unfold entry_st.
apply (allocas_unpoison_nop_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(bv_unsigned a0) (bv_unsigned a1)); [symmetry; apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned | lia | lia | | exact MI0].
destruct HC as [->|HC]; [left; reflexivity | right; exact HC]. }
lazymatch type of W1 with evt bsegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes bsegs _ _ _ cf (ast_evt bsegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (a2' & ->). exists a0. exists t0, t1, t2, a1, a2', a3, a4, a5, a6, a7, t3, t4, t5, t6. reflexivity.
Qed.
End B_TWIN.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W_ss (hlo hhi usp N : Z) : list (Z * Z) := [(shad hlo, shad hhi); (usp - N, usp)].

Definition pois_set (Σ : rtsA) (P : list (Z * Z)) : rtsA :=
mkRtsA (lay Σ) (pr Σ) (ca Σ) (ca_init Σ) (sec Σ) (sec_nres Σ) (aw Σ) (ql Σ) (qg Σ) (dep Σ) (fsc Σ) (ia_init Σ) (credit Σ) (live Σ) (frames Σ) P.

Lemma shad_mono : forall x y, x <= y -> shad x <= shad y.
Proof. intros x y H. unfold shad. apply Z.add_le_mono_r. apply Z.div_le_mono; lia. Qed.

Section StkShadow.
Variables (Σ : rtsA) (m m' : mem) (hlo hhi usp N : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation W := (W_ss hlo hhi usp N).
Hypothesis Hh1 : l_ACEIL L <= hlo.
Hypothesis Hh3 : hhi <= 2 ^ 47.
Hypothesis HN : l_ACEIL L <= usp - N.
Hypothesis Husp : usp <= USTACK_TOP.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.

Lemma ss_aceil : 2 ^ 44 + SHB <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ l_ACEIL L mod 8 = 0 /\ SEGTOP_A <= l_ACEIL L.
Proof using HA.
clear - HA. pose proof (rta_sp0_win Σ m HA) as X. pose proof (rta_sp0_range Σ m HA) as Y. pose proof (rta_sp0 Σ m HA) as (_ & X3).
split; [unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia|]. split; [unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia|].
split; [|unfold l_ACEIL, rtA_sp0, STACK_WIN, SHB, USTACK_TOP in *; lia].
unfold rtA_sp0 in X3. unfold l_ACEIL, STACK_WIN. apply Z.mod_divide in X3; [|lia]. destruct X3 as [q Hq]. rewrite Hq.
replace (q * 16 - 8388608) with ((2 * q - 1048576) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma ss_off : forall a n, (a + n <= shad (l_ACEIL L) \/ shad (2 ^ 47) <= a) -> (a + n <= l_ACEIL L \/ USTACK_TOP <= a) -> disjoint_from W a n.
Proof using Hh1 Hh3 HN Husp.
clear - Hh1 Hh3 HN Husp. intros a n H1 H2. pose proof (shad_mono _ _ Hh1) as S1. pose proof (shad_mono _ _ Hh3) as S2.
unfold W_ss. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ss_shad_aceil : shad (l_ACEIL L) = l_ACEIL L / 8 + SHB /\ SHB <= shad (l_ACEIL L) /\ shad (2 ^ 47) = 2 ^ 44 + SHB.
Proof using HA. clear - HA. pose proof ss_aceil as (A1 & A2 & A3 & A4). unfold shad. split; [reflexivity|]. split; [|reflexivity].
pose proof (Z.div_pos (l_ACEIL L) 8 ltac:(unfold SHB in *; lia) ltac:(lia)). lia. Qed.

Lemma ss_img : forall a n, 0x10000 <= a -> a + n <= SEGTOP_A -> disjoint_from CS_W a n -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2 _. pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof ss_shad_aceil as (_ & S0 & _).
apply ss_off; unfold SEGTOP_A, SHB in *; lia.
Qed.

Lemma ss_granted : forall b gn a n, grant_ok L b gn -> b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros b gn a n (G1 & G2 & G3 & G4 & G5) H1 H2. pose proof ss_shad_aceil as (_ & S0 & S1).
apply ss_off; [|lia]. rewrite S1. unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. lia.
Qed.

Lemma ss_grant : forall b gn a n, In (b, gn) (startup_grants L) -> apart b gn (l_PRB L) 0x2000011000 -> apart b gn (l_FSB L) 0xb09000 ->
b <= a -> a + n <= b + gn -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp. intros b gn a n Hin _ _ H1 H2. exact (ss_granted b gn a n (geo_grant Σ m HA b gn Hin) H1 H2). Qed.

Lemma ss_shad : forall lo hi a n, lo mod 8 = 0 -> hi mod 8 = 0 -> 0 <= lo -> hi <= 2 ^ 47 -> shad lo <= a -> a + n <= shad hi ->
(forall f k, In (f, k) (frames Σ) -> hi <= f \/ f + fs_size k <= lo) ->
(hi <= l_FSB L \/ l_FSB L + 0xb09000 <= lo) -> hi <= l_ACEIL L -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros lo hi a n _ _ H0 H47 H1 H2 _ _ HC. pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof (shad_mono _ _ HC) as S1. pose proof (shad_mono _ _ H47) as S2.
pose proof ss_shad_aceil as (_ & _ & S3). apply ss_off; lia.
Qed.

Lemma ss_prb : forall a n, l_PRB L <= a -> a + n <= l_PRB L + 0x2000011000 ->
(forall c i n', 1 <= c <= 31 -> nth_error (r_st (pr Σ c)) i = Some (CkAlloc n') ->
a + n <= p_ubeg (l_SB L) c i n' \/ p_ubeg (l_SB L) c i n' + n' <= a) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2 _. exact (ss_granted _ _ a n (geo_grant Σ m HA (l_PRB L) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) H1 H2).
Qed.

Lemma ss_secmap : forall k0 s0 a n, nth_error (sec Σ) k0 = Some s0 -> s_mb s0 <= a -> a + n <= s_mb s0 + smsz (s_n s0) ->
(s_quar s0 = false -> a + n <= s_ubeg s0 \/ s_ubeg s0 + s_n s0 <= a) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros k0 s0 a n Hk H1 H2 _. destruct (X0fq.map_geo Σ m HA k0 s0 Hk) as (_ & G & _). exact (ss_granted _ _ a n G H1 H2).
Qed.

Lemma ss_fsb : forall a n, l_FSB L <= a -> a + n <= l_FSB L + 0xb09000 -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2. exact (ss_granted _ _ a n (fsb_grant Σ m HA) H1 H2).
Qed.

Lemma ss_fshad : forall a n, shad (l_FSB L) <= a -> a + n <= shad (l_FSB L + 0xb09000) -> disjoint_from W a n.
Proof using HA Hh1 Hh3 HN Husp.
intros a n H1 H2. pose proof (fsb_grant Σ m HA) as (G1 & G2 & G3 & G4 & G5). pose proof ss_aceil as (A1 & A2 & A3 & A4).
pose proof (shad_mono _ _ G3) as S1. pose proof (shad_mono _ _ A2) as S2. pose proof ss_shad_aceil as (_ & _ & S3). apply ss_off; lia.
Qed.

Lemma ss_fs_cls : forall k, (k = 0 \/ k = 2 \/ k = 4 \/ k = 5 \/ k = 8)%nat -> fs_cls_avoid W (l_FSB L) (Z.of_nat k) (fs_of Σ k).
Proof using HA Hh1 Hh3 HN Husp.
intros k Hk. pose proof (rel_flags_ok Σ m HA k Hk) as (Hlen & _).
assert (Hc : Z.of_nat k = 0 \/ Z.of_nat k = 2 \/ Z.of_nat k = 4 \/ Z.of_nat k = 5 \/ Z.of_nat k = 8) by (destruct Hk as [ -> | [ -> | [ -> | [ -> | -> ] ] ] ]; cbn; lia).
pose proof (push_bounds Σ m HA) as (B1 & B2 & _). pose proof (flags_range _ Hc) as (F1 & F2).
split; [apply ss_fsb; destruct Hc as [E|[E|[E|[E|E]]]]; rewrite E; lia|].
split; [rewrite Hlen; apply ss_fsb; unfold fl_base; lia|].
intros p Hp _. pose proof (frame_addr_range (l_FSB L) _ p Hc Hp) as (R1 & R2). unfold kFakeStackSize in R2.
pose proof (frame_shad_in2 (l_FSB L) _ p B2 Hc Hp) as (S1 & S2).
split; [apply ss_fsb; lia | apply ss_fshad; lia].
Qed.

Lemma ss_fs : fs_avoid W Σ.
Proof using HA Hh1 Hh3 HN Husp.
pose proof (fsb_grant Σ m HA) as (G1 & _).
unfold fs_avoid. split; [apply ss_fsb; lia|].
split; [exact (ss_fs_cls 0%nat ltac:(lia))|]. split; [exact (ss_fs_cls 2%nat ltac:(lia))|].
split; [split; [exact (ss_fs_cls 4%nat ltac:(lia))| split; [exact (ss_fs_cls 5%nat ltac:(lia))| exact (ss_fs_cls 8%nat ltac:(lia))]]|].
split; [apply (X0fr.ac_lits W ss_img); vm_compute; reflexivity|].
split; [apply (ss_granted (l_DTV L) 4096); [exact (geo_grant Σ m HA _ _ ltac:(unfold startup_grants; do 4 right; left; reflexivity)) | lia | lia]|].
split; [apply (ss_granted (l_T L) 4096); [exact (geo_grant Σ m HA _ _ ltac:(unfold startup_grants; do 2 right; left; reflexivity)) | lia | lia]|].
apply Forall_forall. intros [f k] Hin. cbn [fst snd]. destruct (sep_frame Σ m HA f k Hin) as (X & Y & Z0). apply ss_fsb; lia.
Qed.

Lemma ss_but_shadow : consts_rep L m' /\ prim_rep Σ m' /\ cache_rep Σ m' /\ chunk_rep Σ m' /\ sec_rep Σ m' /\ quar_rep Σ m'
/\ dep_rep L (dep Σ) m' /\ fs_rep Σ m' /\ ia_rep Σ m' /\ vis_rep L (rtA_allow Σ) m'.
Proof using HA Hh1 Hh3 HN Husp MU WM.
pose proof (ART_wf Σ m HA) as Hwf.
pose proof (X0fr.av_consts Σ m W HA ss_img ss_grant) as A1.
pose proof (X0fr.av_reg Σ m W HA ss_grant ss_shad ss_prb) as A2.
pose proof (X0fr.av_pchunk Σ m W HA ss_shad ss_prb) as A3.
pose proof (X0fr.av_schunk Σ m W HA ss_shad ss_secmap) as A4.
pose proof (X0fr.av_sec Σ m W HA ss_img ss_grant) as A5.
pose proof (X0fr.av_quar Σ m W HA ss_img ss_grant ss_prb) as A6.
pose proof (X0fr.av_dep Σ m W HA ss_img ss_grant) as A7.
pose proof (X0fr.av_ia W ss_img) as A9.
split; [exact (consts_rep_transport W _ m m' (ART_consts Σ m HA) MU WM A1)|].
split; [intros c Hc; exact (reg_rep_transport W _ c _ m m' (ART_prim Σ m HA c Hc) MU WM (proj1 (A2 c Hc)))|].
split; [intros c Hc; exact (pclass_rep_transport W _ c _ _ m m' (ART_cache Σ m HA c Hc) MU WM (proj2 (A2 c Hc)))|].
split; [destruct (ART_chunk Σ m HA) as [P S]; split;
[intros c i st Hc Hn; exact (pchunk_transport W _ c i st m m' (P c i st Hc Hn) MU WM (A3 c i st Hc Hn))
| intros k s Hk; exact (schunk_transport W k s m m' (S k s Hk) MU WM (A4 k s Hk))]|].
split; [exact (sec_rep_transport W Σ m m' (ART_sec Σ m HA) MU WM A5)|].
split; [exact (quar_rep_transport W Σ m m' (ART_quar Σ m HA) MU WM A6)|].
split; [destruct Hwf as (_ & _ & _ & _ & _ & _ & _ & Hdok & _); exact (dep_rep_transport W _ _ m m' (ART_dep Σ m HA) Hdok MU WM A7)|].
split; [exact (fs_rep_transport W Σ m m' (ART_fs Σ m HA) MU WM ss_fs)|].
split; [exact (ia_rep_transport W Σ m m' (ART_ia Σ m HA) MU WM A9)|].
exact (vis_rep_wmono _ m m' (ART_vis Σ m HA) WM).
Qed.

Theorem ss_art : forall Pr, stack_shadow_rep L (rtA_pois (pois_set Σ Pr)) m' -> ART_A (pois_set Σ Pr) m'.
Proof using HA Hh1 Hh3 HN Husp MU WM.
intros Pr SSR. pose proof ss_but_shadow as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C11).
pose proof (ART_shadow Σ m HA) as (_ & S1 & S2 & SA).
apply (ART_intro (pois_set Σ Pr) m' (ART_wf Σ m HA) C1 C2 C3 C4 C5 C6 C7 C8 C9); [|exact C11].
split; [exact SSR|]. split; [exact (stk_wmono m m' _ _ S1 WM)|]. split; [exact (stk_wmono m m' _ _ S2 WM)|].
pose proof (X0fr.av_static_shad Σ m W HA ss_shad) as AS.
unfold static_acc in *. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) SA r Hr) as X.
pose proof (proj1 (Forall_forall _ _) AS r Hr) as D. cbv beta in X, D.
assert (Hlh : fst r < snd r) by (unfold CS_ACC in Hr; repeat (destruct Hr as [Hr|Hr]; [subst r; cbn; lia|]); destruct Hr).
apply (acc_transport W m m' _ _ X MU ltac:(lia)). replace (fst r + (snd r - fst r) - 1) with (snd r - 1) by lia. exact D.
Qed.

Lemma ss_pres : 0 <= N -> rt_pres (live Σ) (frames Σ) usp m m'.
Proof using HA Hh1 Hh3 HN Husp MU.
intros HN0 a Ha. apply MU. set (x := bv_unsigned a) in *.
pose proof ss_aceil as (A1 & A2 & A3 & A4). pose proof ss_shad_aceil as (S0 & _ & S1).
assert (Hsp : rtA_sp0 Σ - STACK_WIN <= usp) by (unfold l_ACEIL in HN; unfold rtA_sp0; lia).
pose proof (art_avoid_client Σ m usp HA Hsp) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (ASH & _)).
assert (E : shad (l_ACEIL L) + Z.max 0 ((2 ^ 47 - l_ACEIL L) / 8) = shad (2 ^ 47)).
{ apply Z.mod_divide in A3; [|lia]. destruct A3 as [q Hq]. unfold shad. rewrite Hq, Z.div_mul by lia.
replace (2 ^ 47 - q * 8) with ((2 ^ 44 - q) * 8) by ring. rewrite Z.div_mul by lia. change (2 ^ 47 / 8) with (2 ^ 44). lia. }
assert (STK : disjoint_from (W_client Σ usp) (usp - N) N).
{ apply avoid_client_intro; [lia | apply dsj_CS_out; right; unfold l_ACEIL, STACK_WIN, SEGTOP_A in *; lia | | |].
- apply Forall_forall. intros [q n] Hin. destruct (rta_live_range Σ m q n HA Hin) as (_ & X & _). cbn [fst snd].
unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (_ & X & _). cbn [fst snd].
unfold l_ACEIL, rtA_sp0 in *. lia.
- apply Forall_forall. intros [f2 k2] Hin. destruct (rta_frames_range Σ m HA f2 k2 Hin) as (X0 & X & _). cbn [fst snd].
assert (shad (f2 + fs_size k2) <= 2 ^ 44 + SHB).
{ unfold shad. assert ((f2 + fs_size k2) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; unfold l_ACEIL, rtA_sp0, STACK_WIN, USTACK_TOP in *; lia). lia. }
right. unfold l_ACEIL, rtA_sp0 in *. lia. }
pose proof (W_client_cover Σ usp x Ha) as NO. pose proof (shad_mono _ _ Hh1) as M1. pose proof (shad_mono _ _ Hh3) as M2.
unfold W_ss. cbn [outside].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ ASH); lia|].
split; [intros Hx; apply NO; apply (disjoint_outside _ _ _ _ STK); lia | exact I].
Qed.

End StkShadow.

Lemma shad_add8 : forall x k, shad (x + 8 * k) = shad x + k.
Proof. intros x k. unfold shad. replace (x + 8 * k) with (x + k * 8) by lia. rewrite Z.div_add by lia. lia. Qed.

Lemma shad_lt_al : forall a b, b mod 8 = 0 -> a < b -> shad a < shad b.
Proof.
intros a b Hb H. unfold shad. apply Z.mod_divide in Hb; [|lia]. destruct Hb as [q ->]. rewrite Z.div_mul by lia.
assert (a / 8 < q) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

Lemma shad_top : forall a, a < 2 ^ 47 -> shad a < 2 ^ 44 + SHB.
Proof. intros a H. unfold shad. assert (a / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia. Qed.

Lemma alloca_rr_ap : forall A n, alloca_rr A n = ap_rr A n + 32.
Proof. reflexivity. Qed.

Lemma ap_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. cbn. lia. Qed.

Lemma mod32_8 : forall x, x mod 32 = 0 -> x mod 8 = 0.
Proof. intros x H. apply Z.mod_divide in H; [|lia]. destruct H as [q ->]. replace (q * 32) with (4 * q * 8) by lia. apply Z.mod_mul. lia. Qed.

Definition ap_W (A n usp : Z) : list (Z * Z) :=
[(shad (A - 32), shad (A - 32) + 4); (shad (A + n), shad (ap_rr A n) + 4); (usp - 64, usp)].

Section AllocaPoison.
Variables (Σ : rtsA) (m m' : mem) (A n usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis HA32 : A mod 32 = 0.
Hypothesis Hn : 0 <= n.
Hypothesis Hsp : usp <= A - 32.
Hypothesis Htop : alloca_rr A n <= USTACK_TOP - 16.
Hypothesis HPA : pois_above P (alloca_rr A n).
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (ap_W A n usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis P_part : (A + n) mod 8 <> 0 -> rw_cells asegs m' (shad (A + n)) [C1 (Z_to_bv 8 ((A + n) mod 8))].

Lemma ap_geo : (A - 32) mod 8 = 0 /\ alloca_rr A n mod 32 = 0 /\ A + n < alloca_rr A n /\ shad (A - 32) + 4 = shad A
/\ shad (ap_rr A n) + 4 = shad (alloca_rr A n) /\ shad A <= shad (A + n) /\ shad (A + n) < shad (alloca_rr A n).
Proof using HA32 Hn.
clear - HA32 Hn. pose proof (alloca_rr_bounds A n) as (RB & RM). pose proof (mod32_8 _ RM) as R8.
split; [rewrite Zminus_mod, (mod32_8 _ HA32); reflexivity|]. split; [exact RM|]. split; [lia|].
split; [replace A with (A - 32 + 8 * 4) at 2 by lia; rewrite shad_add8; lia|].
split; [rewrite alloca_rr_ap; replace (ap_rr A n + 32) with (ap_rr A n + 8 * 4) by lia; rewrite shad_add8; lia|].
split; [apply shad_mono; lia | apply shad_lt_al; [exact R8 | lia]].
Qed.

Lemma ap_munch : munch (W_ss (A - 32) (alloca_rr A n) usp 64) m m'.
Proof using HA32 Hn MU.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
apply (munch_weaken (ap_W A n usp)); [|exact MU].
intros x Hx. unfold W_ss in Hx. unfold ap_W. cbn [outside] in *. destruct Hx as (X1 & X2 & _).
pose proof (shad_mono (A - 32) (A + n) ltac:(lia)) as S1.
split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_dsj : forall s k, (s + k <= shad (A - 32) \/ shad (alloca_rr A n) <= s) -> s + k <= 2 ^ 44 + SHB -> disjoint_from (ap_W A n usp) s k.
Proof using HA HA32 Hn Husp.
intros s k H1 H2. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & _).
pose proof (shad_mono (A - 32) (A + n) ltac:(lia)) as S1.
unfold ap_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_dsj_mid : forall s, shad A <= s < shad (A + n) -> disjoint_from (ap_W A n usp) s 1.
Proof using HA HA32 Hn Husp Htop.
intros s Hs. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & _).
pose proof (shad_top (A + n) ltac:(unfold USTACK_TOP in Htop; lia)) as T1.
unfold ap_W. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma ap_acc_new : acc asegs m' A n.
Proof using HA HA32 Hn Hsp Htop HPA Husp MU P_part.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
intros i Hi. destruct (Z_lt_le_dec (shad (A + i)) (shad (A + n))) as [Hlt|Hge].
-
exists z8. split; [|left; reflexivity].
assert (Hz : bytes_at asegs m (shad (A + i)) [z8]).
{ apply Z0; [unfold USTACK_TOP in *; lia|]. intros (e & He & E1 & E2). specialize (HPA e He). lia. }
apply (bytes_at_transport asegs _ m m' _ _ Hz MU). change (Z.of_nat (length [z8])) with 1.
apply ap_dsj_mid. split; [apply shad_mono; lia | exact Hlt].
-
assert (E : shad (A + i) = shad (A + n)) by (pose proof (shad_mono (A + i) (A + n) ltac:(lia)); lia).
assert (K : (A + n) mod 8 <> 0).
{ intros K0. pose proof (shad_lt_al (A + i) (A + n) K0 ltac:(lia)). lia. }
exists (Z_to_bv 8 ((A + n) mod 8)). rewrite E.
split; [destruct (P_part K) as [[_ PB] _]; cbn [cells_bytes cbytes app] in PB; exact PB|].
pose proof (Z.mod_pos_bound (A + n) 8 ltac:(lia)) as B. right. rewrite ap_lit8 by lia. split; [lia|].
unfold shad in E. assert (E' : (A + i) / 8 = (A + n) / 8) by lia.
pose proof (Z.div_mod (A + i) 8 ltac:(lia)). pose proof (Z.div_mod (A + n) 8 ltac:(lia)). lia.
Qed.

Lemma ap_ssr : stack_shadow_rep L ((A, n) :: P) m'.
Proof using HA HA32 Hn Hsp Htop HPA Husp MU P_part.
pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
assert (Hno : ~ in_pois P a) by (intros (e & He & E); apply Hnp; exists e; split; [right; exact He | exact E]).
assert (Hnh : a < A - 32 \/ alloca_rr A n <= a).
{ destruct (Z_lt_le_dec a (A - 32)) as [X|X]; [left; exact X|]. destruct (Z_lt_le_dec a (alloca_rr A n)) as [Y|Y]; [|right; exact Y].
exfalso. apply Hnp. exists (A, n). split; [left; reflexivity|]. unfold pz_lo, pz_hi. cbn [fst snd]. lia. }
apply (bytes_at_transport asegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1.
apply ap_dsj; [|lia]. destruct Hnh as [X|X]; [left; pose proof (shad_lt_al a (A - 32) G1 X); lia | right; apply shad_mono; exact X].
- apply Forall_cons; [exact ap_acc_new|].
apply Forall_forall. intros [a0 n0] He. pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4). specialize (HPA _ He).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply ap_dsj; [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_cons; [|exact WF1]. cbn [fst snd]. unfold pz_lo, pz_hi. cbn [fst snd]. split; [exact HA32|]. split; [exact Hn|]. split; [lia | exact Htop].
+ apply FOP_cons; [|exact WF2]. apply Forall_forall. intros e He. specialize (HPA e He). unfold pz_hi at 1. cbn [fst snd]. exact HPA.
Qed.

Lemma ap_acc_tr : forall o k, acc asegs m o k -> o + k <= USTACK_TOP -> o + k <= A - 32 \/ alloca_rr A n <= o -> acc asegs m' o k.
Proof using HA HA32 Hn Husp MU.
intros o k H HT Hoff. pose proof ap_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
destruct (Z_le_gt_dec k 0) as [K0|K0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ H MU ltac:(lia)).
pose proof (shad_top (o + k - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply ap_dsj; [|lia]. destruct Hoff as [X|X]; [left; pose proof (shad_lt_al (o + k - 1) (A - 32) G1 ltac:(lia)); lia | right; apply shad_mono; exact X].
Qed.

End AllocaPoison.

Lemma ss_stk_sub : forall (m : mem) lo hi a b, stk asegs m lo hi -> lo <= a -> a <= b -> b <= hi -> stk asegs m a b.
Proof. intros m lo hi a b (H0 & H1 & H) Ha Hab Hb. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia. Qed.

Lemma ss_stk_cell : forall (m : mem) a (n : nat), stk asegs m a (a + Z.of_nat n) -> exists bs, rw_cells asegs m a [CB n bs].
Proof.
intros m a n St. pose proof (stk_wr_at' m a _ St) as H.
destruct (stk_bytes asegs m _ _ St ltac:(lia)) as (bs & Hl & Hbs). exists bs.
split; [split; [cbn; split; [rewrite Hl; lia | exact I] | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hbs]|].
cbn [cells_size csize]. rewrite Nat.add_0_r. exact H.
Qed.

Lemma ss_mat_stable : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Lemma ss_pre : forall Σ m (sp : word) lo, ART_A Σ m -> call_ok RTA Σ m sp lo ->
m2s_cells m /\ setshadow_cells m /\ rw_cells asegs m 0xf3890 [C8 (Z_to_bv 64 0xfaa78)] /\ rw_cells asegs m (0xfaa78 + 85) [C1 (Z_to_bv 8 1)]
/\ stk asegs m (shad (l_ACEIL (lay Σ))) (shad (2 ^ 47))
/\ l_ACEIL (lay Σ) <= lo /\ lo + RT_STACK <= bv_unsigned sp /\ bv_unsigned sp + 16 <= USTACK_TOP /\ stk asegs m lo (bv_unsigned sp)
/\ 2 ^ 44 + SHB <= l_ACEIL (lay Σ) /\ l_ACEIL (lay Σ) <= 2 ^ 47 /\ l_ACEIL (lay Σ) mod 8 = 0 /\ SEGTOP_A <= l_ACEIL (lay Σ).
Proof.
intros Σ m sp lo HA (ST & LOW & LOR & SPT & SPA). cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
pose proof (ART_consts Σ m HA) as (_ & _ & _ & M2S & PS & _ & _ & ICR).
destruct ICR as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & X21 & X22
& X23 & X24 & X25 & X26 & _).
destruct PS as (_ & _ & SS & _). destruct (ART_shadow Σ m HA) as (_ & S1 & _).
pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
split; [exact M2S|]. split; [exact SS|]. split; [exact X23|]. split; [exact X26|]. split; [exact S1|].
split; [unfold l_ACEIL; lia|]. split; [exact LOR|]. split; [exact SPT|]. split; [exact ST|].
split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.

Theorem rta_alloca_poison : alloca_poison_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo
FDO MST -> -> HA32 HSZ HSP HTOP HPA HFR ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & GF & PPF & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
pose proof (alloca_rr_bounds addr size) as (RB & RM). pose proof (mod32_8 _ RM) as R8.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
assert (G4 : shad (addr - 32) + 4 = shad addr) by (replace addr with (addr - 32 + 8 * 4) at 2 by lia; rewrite shad_add8; lia).
assert (G5 : shad (ap_rr addr size) + 4 = shad (alloca_rr addr size)) by (rewrite alloca_rr_ap; replace (ap_rr addr size + 32) with (ap_rr addr size + 8 * 4) by lia; rewrite shad_add8; lia).
assert (T1 : shad (alloca_rr addr size) <= 2 ^ 44 + SHB) by (pose proof (shad_mono (alloca_rr addr size) (2 ^ 47) ltac:(unfold USTACK_TOP in *; lia)) as X; unfold shad in X |- *; change (2 ^ 47 / 8) with (2 ^ 44) in X; lia).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad (addr - 32)) by (apply shad_mono; lia).
assert (B2 : shad (alloca_rr addr size) <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad addr <= shad (addr + size)) by (apply shad_mono; lia).
assert (B4 : shad (addr + size) < shad (alloca_rr addr size)) by (apply shad_lt_al; [exact R8 | lia]).
assert (HSUM : addr + size + 64 <= 2 ^ 47).
{ unfold alloca_rr, USTACK_TOP in HTOP. pose proof (Z.div_mod (addr + size + 31) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (addr + size + 31) 32 ltac:(lia)) as B.
set (q := (addr + size + 31) / 32) in *. lia. }
assert (SHL0 : stk asegs m (shad (addr - 32)) (shad (addr - 32) + Z.of_nat 4)) by (apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad (addr - 32)) 4 SHL0) as (j1 & SHL).
assert (SHR : stk asegs m (shad (addr + size)) (shad (ap_rr addr size) + 4)) by (apply (ss_stk_sub m _ _ _ _ SHS); lia).
assert (W1 : evt asegs (alloca_poison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc addr size lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 addr) (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_alloca_poison m)).
{ unfold entry_st.
exact (alloca_poison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m addr size lo j1
eq_refl eq_refl HA32 HSZ ltac:(unfold SEGTOP_A, RT_STACK in *; lia) HSUM M2S SS GF PPF SHL SHR ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold alloca_poison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ ((addr, size) :: pois Σ)) = (addr, size) :: rtA_pois Σ).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); [contradiction HFR; reflexivity | reflexivity]. }
exists (pois_set Σ ((addr, size) :: pois Σ)).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ ((addr, size) :: pois Σ))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & _ & _ & PP).
assert (MU' : munch (W_ss (addr - 32) (alloca_rr addr size) usp 64) m m')
by exact (ap_munch m m' addr size usp HA32 ltac:(lia) MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' (addr - 32) (alloca_rr addr size) usp 64 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (ap_ssr Σ m m' addr size usp ART0 HA32 ltac:(lia) HSP HTOP HPA HUS MU PP). }
split; [exact (ss_pres Σ m m' (addr - 32) (alloca_rr addr size) usp 64 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
split; [exact (ap_acc_new Σ m m' addr size usp ART0 HA32 ltac:(lia) HSP HTOP HPA HUS MU PP)|].
intros o k Hacc HT Hoff. exact (ap_acc_tr Σ m m' addr size usp ART0 HA32 ltac:(lia) HUS MU o k Hacc HT Hoff).
Qed.

Definition au_W (top bottom usp : Z) : list (Z * Z) := [(shad top, shad top + (bottom - top) / 8); (usp - 32, usp)].

Lemma FOP_filter : forall {X} (R : X -> X -> Prop) (f : X -> bool) l, ForallOrdPairs R l -> ForallOrdPairs R (List.filter f l).
Proof.
intros X R f l H. induction H as [|x l Hx Hl IH]; cbn [List.filter]; [constructor|].
destruct (f x); [|exact IH]. apply FOP_cons; [|exact IH].
apply Forall_forall. intros y Hy. apply filter_In in Hy as [Hy _]. exact (proj1 (Forall_forall _ _) Hx y Hy).
Qed.

Section AllocasUnpoison.
Variables (Σ : rtsA) (m m' : mem) (top bottom usp : Z).
Hypothesis HA : ART_A Σ m.
#[local] Notation L := (lay Σ).
#[local] Notation P := (rtA_pois Σ).
Hypothesis Htb : 0 < top <= bottom.
Hypothesis Ht8 : top mod 8 = 0.
Hypothesis Hb8 : bottom mod 8 = 0.
Hypothesis Hsp : usp <= top.
Hypothesis Hbt : bottom <= USTACK_TOP - 16.
Hypothesis HST : forall e, In e P -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e.
Hypothesis Husp : l_ACEIL L + 128 <= usp.
Hypothesis MU : munch (au_W top bottom usp) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis P_zero : rw_cells asegs m' (shad top) [CB (Z.to_nat ((bottom - top) / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat ((bottom - top) / 8)))].

Lemma au_geo : shad top + (bottom - top) / 8 = shad bottom /\ 0 <= (bottom - top) / 8.
Proof using Htb Ht8 Hb8.
clear - Htb Ht8 Hb8. apply Z.mod_divide in Ht8, Hb8; try lia. destruct Ht8 as [q1 E1]. destruct Hb8 as [q2 E2]. unfold shad. rewrite E1, E2.
replace (q2 * 8 - q1 * 8) with ((q2 - q1) * 8) by ring. rewrite !Z.div_mul by lia. lia.
Qed.

Lemma au_munch : munch (W_ss top bottom usp 32) m m'.
Proof using Htb Ht8 Hb8 MU.
pose proof au_geo as (G1 & G2). apply (munch_weaken (au_W top bottom usp)); [|exact MU].
intros x Hx. unfold W_ss in Hx. unfold au_W. cbn [outside] in *. destruct Hx as (X1 & X2 & _). split; [lia|]. split; [lia | exact I].
Qed.

Lemma au_dsj : forall s k, (s + k <= shad top \/ shad bottom <= s) -> s + k <= 2 ^ 44 + SHB -> disjoint_from (au_W top bottom usp) s k.
Proof using HA Htb Ht8 Hb8 Husp.
intros s k H1 H2. pose proof au_geo as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & _).
unfold au_W. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
Qed.

Lemma au_ssr : stack_shadow_rep L (pois_drop bottom P) m'.
Proof using HA Htb Ht8 Hb8 Hsp Hbt HST Husp MU P_zero.
pose proof au_geo as (G1 & G2). pose proof (ss_aceil Σ m HA) as (A1 & A2 & A3 & A4).
destruct (ART_shadow Σ m HA) as ((M8 & Z0 & AC & WF) & _).
split; [exact M8|]. split; [|split].
- intros a Ha Hnp.
destruct (Z_lt_le_dec a top) as [X|X]; [|destruct (Z_lt_le_dec a bottom) as [Y|Y]].
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport asegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_lt_al a top Ht8 X). apply au_dsj; lia.
+
destruct P_zero as [[_ PB] _]. cbn [cells_bytes cbytes] in PB. rewrite app_nil_r in PB.
assert (Hj : 0 <= shad a - shad top < (bottom - top) / 8).
{ pose proof (shad_mono top a X). pose proof (shad_lt_al a bottom Hb8 Y). lia. }
replace (shad a) with (shad top + Z.of_nat (Z.to_nat (shad a - shad top))) by (rewrite Z2Nat.id by lia; lia).
apply (bytes_at_nth1 asegs m' _ _ _ _ PB). apply nth_error_repeat. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
+
assert (Hno : ~ in_pois P a).
{ intros (e & He & E). destruct (HST e He) as [(S1 & S2)|S1]; [lia|]. apply Hnp. exists e. split; [|exact E].
unfold pois_drop. apply filter_In. split; [exact He | apply Z.leb_le; exact S1]. }
apply (bytes_at_transport asegs _ m m' _ _ (Z0 a Ha Hno) MU). change (Z.of_nat (length [z8])) with 1.
pose proof (shad_top a ltac:(lia)) as T1. pose proof (shad_mono bottom a Y). apply au_dsj; lia.
- apply Forall_forall. intros [a0 n0] He. unfold pois_drop in He. apply filter_In in He as [He Hb]. apply Z.leb_le in Hb.
pose proof (proj1 (Forall_forall _ _) AC _ He) as X.
pose proof (proj1 (Forall_forall _ _) (proj1 WF) _ He) as (W1 & W2 & W3 & W4).
cbn [fst snd] in *. unfold pz_lo, pz_hi in *. cbn [fst snd] in *. pose proof (alloca_rr_bounds a0 n0) as (RB & _).
destruct (Z.eq_dec n0 0) as [->|Hn0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ X MU ltac:(lia)).
pose proof (shad_top (a0 + n0 - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply au_dsj; [right; apply shad_mono; lia | lia].
- destruct WF as (WF1 & WF2). split.
+ apply Forall_forall. intros e He. unfold pois_drop in He. apply filter_In in He as [He _]. exact (proj1 (Forall_forall _ _) WF1 e He).
+ exact (FOP_filter _ _ _ WF2).
Qed.

Lemma au_acc_tr : forall o k, acc asegs m o k -> o + k <= USTACK_TOP -> o + k <= top \/ bottom <= o -> acc asegs m' o k.
Proof using HA Htb Ht8 Hb8 Husp MU.
intros o k H HT Hoff. destruct (Z_le_gt_dec k 0) as [K0|K0]; [intros i Hi; lia|].
apply (acc_transport _ m m' _ _ H MU ltac:(lia)).
pose proof (shad_top (o + k - 1) ltac:(unfold USTACK_TOP in *; lia)) as T1.
apply au_dsj; [|lia]. destruct Hoff as [X|X]; [left; pose proof (shad_lt_al (o + k - 1) top Ht8 ltac:(lia)); lia | right; apply shad_mono; exact X].
Qed.

End AllocasUnpoison.

Theorem rta_allocas_unpoison : allocas_unpoison_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo
FDO MST -> -> HTB HT8 HB8 HSP HBT HST ART0 MI0 CALL.
intros T cf Hc Hkont. cbn [ART rt_frames rt_live rt_sp0 rt_credit rt_pois RTA] in *. unfold rtA_frames, rtA_live, rtA_credit in *.
destruct (ss_pre Σ m sp lo ART0 CALL) as (M2S & SS & _ & _ & SHS & LOW & LOR & SPT & ST & A1 & A2 & A3 & A4).
set (usp := bv_unsigned sp) in *.
assert (HUS : l_ACEIL (lay Σ) + 128 <= usp) by (unfold RT_STACK in LOR; lia).
destruct (au_geo top bottom HTB HT8 HB8) as (G1 & G2).
assert (B1 : shad (l_ACEIL (lay Σ)) <= shad top) by (apply shad_mono; lia).
assert (B2 : shad bottom <= shad (2 ^ 47)) by (apply shad_mono; unfold USTACK_TOP in *; lia).
assert (B3 : shad (2 ^ 47) = 2 ^ 44 + SHB) by reflexivity.
assert (SHT0 : stk asegs m (shad top) (shad top + Z.of_nat (Z.to_nat ((bottom - top) / 8)))) by (rewrite Z2Nat.id by lia; apply (ss_stk_sub m _ _ _ _ SHS); lia).
destruct (ss_stk_cell m (shad top) _ SHT0) as (shj & SHC).
assert (W1 : evt asegs (allocas_unpoison_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc top bottom lo m)
(entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 top) (Z_to_bv 64 bottom) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc e_allocas_unpoison m)).
{ unfold entry_st.
exact (allocas_unpoison_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m top bottom lo shj
eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(unfold USTACK_TOP in *; lia)
ltac:(right; unfold kHighShadowEnd, kHighMemEnd, USTACK_TOP, SHB, RT_STACK in *; lia) M2S SS SHC ST
ltac:(unfold RT_STACK in *; lia) ltac:(unfold SEGTOP_A in *; lia) ltac:(lia) MI0). }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold allocas_unpoison_post in Hc1.
assert (EP : rtA_pois (pois_set Σ (pois_drop bottom (pois Σ))) = pois_drop bottom (rtA_pois Σ)).
{ unfold rtA_pois. cbn [frames pois pois_set]. destruct (frames Σ); reflexivity. }
exists (pois_set Σ (pois_drop bottom (pois Σ))).
split; [|split; [exact EP | split; [reflexivity | split; [reflexivity | split; reflexivity]]]].
unfold ASTA. change (rt_allow RTA (pois_set Σ (pois_drop bottom (pois Σ)))) with (rtA_allow Σ).
eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & ST' & PZ).
assert (MU' : munch (W_ss top bottom usp 32) m m') by exact (au_munch m m' top bottom usp HTB HT8 HB8 MU).
exists m', a0'. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'; reflexivity|].
split.
{ split; [|split; [exact MI | split; [exact WM | exact ST']]].
apply (ss_art Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' WM).
rewrite EP. exact (au_ssr Σ m m' top bottom usp ART0 HTB HT8 HB8 HSP HBT HST HUS MU PZ). }
split; [exact (ss_pres Σ m m' top bottom usp 32 ART0 ltac:(lia) ltac:(unfold USTACK_TOP in *; lia) ltac:(lia) ltac:(lia) MU' ltac:(lia))|].
intros o k Hacc HT Hoff. exact (au_acc_tr Σ m m' top bottom usp ART0 HTB HT8 HB8 HUS MU o k Hacc HT Hoff).
Qed.

Theorem rta_allocas_unpoison_nop : allocas_unpoison_nop_contract RTA.
Proof.
intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m FDO MST HC MI0.
intros T cf Hc Hkont.
pose proof (bv_unsigned_in_range 64 a0) as R0. pose proof (bv_unsigned_in_range 64 a1) as R1. unfold bv_modulus in R0, R1. cbn in R0, R1.
assert (W1 : evt asegs (fun ms' => exists (a2' : word),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom asegs))
(entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_allocas_unpoison m)).
{ unfold entry_st.
apply (allocas_unpoison_nop_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
(bv_unsigned a0) (bv_unsigned a1)); [symmetry; apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned | lia | lia | | exact MI0].
destruct HC as [->|HC]; [left; reflexivity | right; exact HC]. }
lazymatch type of W1 with evt asegs _ ?X =>
assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
clear W1.
apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rt_allow RTA Σ) _ _ _ (ss_mat_stable Σ PMc MST) W1') Hc).
intros c1 Hc1. apply Hkont. unfold ASTA. eapply AST_conseq; [exact Hc1| |intros mo Hmo; exact Hmo].
intros ms (a2' & ->). exists a0. exists t0, t1, t2, a1, a2', a3, a4, a5, a6, a7, t3, t4, t5, t6. reflexivity.
Qed.
