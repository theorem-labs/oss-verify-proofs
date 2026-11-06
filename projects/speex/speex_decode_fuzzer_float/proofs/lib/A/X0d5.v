(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cy X1cp X1cj X1dd X1cg X1cs X1cm X1da X1cx X1cq.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X0j1 X0gi X0hr
X0hb X0hi X0j3 X0hn X0hs X0gp X0id X0i8 X0ib X0hx X0hv
X0il X0hm X0fy X0fg X0da X0g4 X0fq X0e4 X0e8 X0d9 X0e5
X0ci X0cr X0cp X0cn X0ck X0co X0cq X0cl X0cm
X0d0 X0d4 X0cz.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X173 X18c X17w X183 X19m X188 X18d X17a X18y X18t X18w X18i X18g X196 X187 X16j X161 X13v X16p X16b X14p X14t X13u X14q X133 X13c X13a X138 X135 X139 X13b X136 X137 X13l X13p X13k.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X173 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X183 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19m OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X188 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18d OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X17a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18y OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18w OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18i OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X18g OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X196 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X187 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16j OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X161 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13v OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X16b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14t OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13u OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14q OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X133 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13a OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X138 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X135 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X139 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13b OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X136 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X137 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13l OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13p OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X13k.
Import ListNotations.
Open Scope Z_scope.

Lemma ds_client_map : forall Σ k s z a, geo_ok Σ -> live_wf Σ -> nth_error (sec Σ) k = Some s -> s_quar s = true ->
l_ACEIL (lay Σ) <= z -> aclient (live Σ) (frames Σ) z a ->
~ (s_mb s <= a < s_mb s + smsz (s_n s)) /\ (z <= a \/ a < l_ACEIL (lay Σ)).
Proof.
intros Σ k s z a HG Hlive Hk Hq Hz Ha.
pose proof (an_map Σ k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _). unfold apart in AF.
destruct Ha as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
- split; [clear - Hs Hz M2; lia | left; lia].
- destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split; [clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia |
clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia | clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia].
- destruct Hl as (p & n & Hin & Hx). destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Htq & Htn & Ep)].
+ pose proof (dk_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx.
split; [clear - Hx S1 S2 G7 M5 Hfit R1 R2; lia | right; clear - Hx S1 S2 G7 G4 Hfit R1 R2; lia].
+ subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
destruct (In_nth_error _ _ Ht) as (jt & Hjt).
pose proof (dk_map Σ HG _ t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & T9).
pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
destruct (Nat.eq_dec jt k) as [->|Hne].
* rewrite Hk in Hjt. injection Hjt as <-. rewrite Hq in Htq. discriminate.
* pose proof (T9 k s Hk (fun E => Hne (eq_sym E))) as A. unfold apart in A.
split; [clear - Hx A Tbig Tn1; lia | right; clear - Hx T2 Tbig Tn1; lia].
- destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
split; [clear - Hx Y1 Y2 Y3 AF; lia | right; clear - Hx Y2 Y3 Q3; lia].
- destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1. pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
split; [clear - Hx X1 X2 M3; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | right; clear - Hx X2 G1; lia].
Qed.

Section Ret.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).

Definition mun_eff : SyscallEffect := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s)))] [] [].

Lemma ds_ret : forall ms0, svc_mun p j b ents i rest Σk k s ms0 -> evt bsegs (dl_N p j b ents i rest (recs Σk k)) (nretA ms0 mun_eff).
Proof using HOK HWP HS Hk Hq Hib Eb.
intros ms0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & HA' & MI' & UF' & ST' & LM').
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (an_map Σk k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
pose proof (dg_consts L m' (proj1 HA')) as (_ & MMG' & _).
eapply evt_mono.
{ unfold mun_eff.
apply (uod_B_spec (Z_to_bv 64 0x47f68) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' a2' a3' a4' a5' a6'
(Z_to_bv 64 1058568) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) m' (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1057944)
MB MSZ lo); rewrite ?RSP.
- exact M1. - exact M7. - clear - M2 HLk; lia.
- unfold hide, img_hull_lo, img_hull_hi. clear - M4; unfold SEGTOP_A in *; lia.
- exact UF'. - exact MMG'. - exact ST'.
- clear - HLk G1 G8 G4. unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. lia.
- clear - N5; lia. - clear - N6; lia. - exact MI'. }
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m'' & -> & MU & WB & MI'' & ST'' & _).
rewrite RSP in MU, ST''.
pose proof LM' as ((G & WG & HGo) & RP & FR & QR & QB).

assert (CLI : forall a, aclient (live Σ0) (frames Σ0) (C + 32) a -> outside [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a).
{ intros a Ha. rewrite <- Elv, <- Efr in Ha.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Ha) as (X1 & X2).
cbn [outside]. split; [exact X1|]. split; [|exact I]. clear - X2 HLk N5. lia. }
assert (STA : forall a n0, C - 112 <= a -> 0 <= n0 -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a n0).
{ intros a n0 H1 H2. cbn [disjoint_from]. clear - H1 H2 M2 HLk N5. split; [lia | split; [lia | exact I]]. }
assert (SLA : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dk_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2.
cbn [disjoint_from]. clear - S1 S2 M5 G7 G4 HLk N5. split; [lia | split; [lia | exact I]]. }
exists (Z_to_bv 64 0x47f68), y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m''.
split; [rewrite ret_pc_even; [reflexivity | clear; lia | reflexivity]|].
split.
-
split; [exact (ds_art_nw Σk k s lo (C - 112) HG Hk HLk ltac:(clear - N5; lia) ltac:(clear - N6; lia) Hdep HQB m' m'' HA' MU)|].
split; [exact MI''|]. split; [exact ST''|].
split.
{ exists ((MB, MB + MSZ) :: G). split.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2). apply (WB x); [clear - Ho1; lia | exact (WG x Hx Ho2)].
- apply Forall_cons; [|exact HGo]. cbn [fst snd]. intros a Ha. split.
+ intros Hc. rewrite <- Elv, <- Efr in Hc.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Hc) as (X1 & _). exact (X1 Ha).
+ clear - Ha M2 HLk. lia. }
split; [exact (rt_pres_trans _ _ _ _ m' m'' RP (fun a Ha => MU a (CLI _ Ha)))|].
split.
{ pose proof FR as (FR1 & FR2 & FR3). split; [|split].
- apply (rwc_nw _ m' m'' _ _ FR1 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR2 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR3 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia. }
apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
apply (proj2 (qcache_rep_iff _ _ _)). split.
+ apply (rwc_nw _ m' m'' _ _ QH MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
+ apply (qchain_nw _ m' m'' _ QC MU). apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLA j' Hj').
- apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (B1 & (ws & U & Hl & Hf) & Hn).
apply (proj2 (qbatch_iff _ _ _ _)). split; [|split; [|exact Hn]].
+ apply (rwc_nw _ m' m'' _ _ B1 MU). cbn [cells_size csize Nat.add Z.of_nat]. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
+ exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64_nw _ m' m'' _ _ U MU). rewrite Hl. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
Qed.

End Ret.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Lemma ds_client_map : forall Σ k s z a, geo_ok Σ -> live_wf Σ -> nth_error (sec Σ) k = Some s -> s_quar s = true ->
l_ACEIL (lay Σ) <= z -> aclient (live Σ) (frames Σ) z a ->
~ (s_mb s <= a < s_mb s + smsz (s_n s)) /\ (z <= a \/ a < l_ACEIL (lay Σ)).
Proof.
intros Σ k s z a HG Hlive Hk Hq Hz Ha.
pose proof (an_map Σ k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
pose proof HG as (_ & _ & HSW & _). pose proof HSW as (_ & _ & _ & SW4 & SW5 & _).
pose proof (proj1 (Forall_forall _ _) SW4 s (nth_error_In _ _ Hk)) as (_ & _ & _ & AF & _). unfold apart in AF.
destruct Ha as [Hs|[Hcs|[Hl|[Hf|Hfs]]]].
- split; [clear - Hs Hz M2; lia | left; lia].
- destruct Hcs as ((lo0 & hi0 & Hin & Hx) & _). unfold CLIENT_STATIC in Hin.
destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; split; [clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia |
clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia | clear - Hx M4; unfold SEGTOP_A in *; lia | right; clear - Hx G1; unfold SHB in *; lia].
- destruct Hl as (p & n & Hin & Hx). destruct Hlive as (_ & _ & V3 & _). destruct (V3 p n Hin) as [(c' & i' & Hc' & Hn & Ep)|(t & Ht & Htq & Htn & Ep)].
+ pose proof (dk_slot_in Σ HG c' i' _ Hc' Hn) as (S1 & S2 & _).
assert (Hfit : rz_size n + n <= ClassSize c' /\ 0 <= n).
{ pose proof HG as (_ & HR & _). destruct HR as (HR & _).
pose proof (HR c' Hc') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & W10 & _).
pose proof (proj1 (Forall_forall _ _) W10 _ (nth_error_In _ _ Hn)) as X. cbv beta iota in X. lia. }
pose proof (fl_rz_facts n) as (R1 & R2). subst p. unfold p_ubeg in Hx.
split; [clear - Hx S1 S2 G7 M5 Hfit R1 R2; lia | right; clear - Hx S1 S2 G7 G4 Hfit R1 R2; lia].
+ subst p. unfold s_ubeg in Hx. rewrite <- Htn in Hx.
destruct (In_nth_error _ _ Ht) as (jt & Hjt).
pose proof (dk_map Σ HG _ t Hjt) as (T1 & T2 & _ & _ & _ & _ & _ & T8 & T9).
pose proof (proj1 (Forall_forall _ _) SW4 t Ht) as ((Tn1 & _) & _). pose proof (smsz_big (s_n t) ltac:(lia)) as Tbig.
destruct (Nat.eq_dec jt k) as [->|Hne].
* rewrite Hk in Hjt. injection Hjt as <-. rewrite Hq in Htq. discriminate.
* pose proof (T9 k s Hk (fun E => Hne (eq_sym E))) as A. unfold apart in A.
split; [clear - Hx A Tbig Tn1; lia | right; clear - Hx T2 Tbig Tn1; lia].
- destruct Hf as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
split; [clear - Hx Y1 Y2 Y3 AF; lia | right; clear - Hx Y2 Y3 Q3; lia].
- destruct Hfs as (f & k0 & Hin & Hx). destruct (g_frame Σ HG f k0 Hin) as (Y1 & Y2 & Y3).
pose proof (g_grant Σ HG (l_FSB (lay Σ)) 0xb09000 ltac:(unfold startup_grants; right; right; right; right; right; left; reflexivity)) as (Q1 & _ & Q3 & _).
pose proof (dk_geo Σ HG) as (Z1 & Z2 & _).
pose proof (dk_shad_rng f ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X1. pose proof (dk_shad_rng (f + fs_size k0) ltac:(clear - Y1 Q1 Y2 Y3 Q3 Z2; lia)) as X2.
split; [clear - Hx X1 X2 M3; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; lia | right; clear - Hx X2 G1; lia].
Qed.

Section Ret.
Variables (p : dlp) (j : list byte) (b : Z) (ib : nat) (ents : list (Z * Z)) (i : nat) (rest : list batch) (Σk : rtsA) (k : nat)
(s : secst).
Hypothesis HOK : dl_ok p.
Hypothesis HWP : rt_wfP Σk ((b, skipn i ents) :: rest).
Hypothesis HS : dl_sig p Σk.
Hypothesis Hk : nth_error (sec Σk) k = Some s.
Hypothesis Hq : s_quar s = true.
Hypothesis Hib : nth_error (r_st (pr Σk 24)) ib = Some CkBatch.
Hypothesis Eb : b = p_abeg (l_SB (lay Σk)) 24 ib.
#[local] Notation Σ0 := (dl_Σ0 p).
#[local] Notation usp := (dl_usp p).
#[local] Notation lo := (dl_lo p).
#[local] Notation C := (dl_usp p - 2288).
#[local] Notation L := (lay Σk).
#[local] Notation SB := (l_SB (lay Σk)).
#[local] Notation MB := (s_mb s).
#[local] Notation MSZ := (smsz (s_n s)).

Definition mun_eff : SyscallEffect := mkEffectU (Z_to_bv 64 0) [] [] [(Z_to_bv 64 (s_mb s), Z_to_bv 64 (smsz (s_n s)))] [] [].

Lemma ds_ret : forall ms0, svc_mun p j b ents i rest Σk k s ms0 -> evt asegs (dl_N p j b ents i rest (recs Σk k)) (nretA ms0 mun_eff).
Proof using HOK HWP HS Hk Hq Hib Eb.
intros ms0 (t0' & t1' & t2' & a2' & a3' & a4' & a5' & a6' & t3' & t4' & t5' & t6' & m' & -> & HA' & MI' & UF' & ST' & LM').
pose proof HOK as (FDO & MST & HLO & HLO2 & HSP & HG0).
pose proof HS as (El & Elv & Efr & Ecr & Eql & Einit & Epo).
pose proof (geo_of_wfP _ _ HWP) as HG.
pose proof (dl_nums p HLO HLO2 HSP HG0) as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9).
assert (HLk : l_ACEIL L <= lo) by (rewrite El; exact N9).
pose proof HWP as (_ & _ & Hlive & _ & _ & _ & _ & Hdep & _).
pose proof (hqb_of_wfP _ _ HWP) as HQB.
pose proof (an_map Σk k s HG Hk) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & G1 & G4 & G6 & G7 & G8).
assert (RSP : bv_unsigned (Z_to_bv 64 (C - 112)) = C - 112) by (apply unsigned_lit; clear - N5 N6 N4; lia).
pose proof (dg_consts L m' (proj1 HA')) as (_ & MMG' & _).
eapply evt_mono.
{ unfold mun_eff.
apply (uod_B_spec (Z_to_bv 64 0x47e7c) (Z_to_bv 64 (C - 112)) (dl_gp p) (Z_to_bv 64 tpA) t0' t1' t2' a2' a3' a4' a5' a6'
(Z_to_bv 64 1023688) (Z_to_bv 64 b) (Z_to_bv 64 (2^37)) (Z_to_bv 64 (Z.of_nat (length ents)))
(Z_to_bv 64 (b + 152 + 8 * Z.of_nat i)) (Z_to_bv 64 (Z.of_nat (length ents) + 16)) (Z_to_bv 64 (16 + Z.of_nat i))
(dl_s10 p) (dl_s11 p) t3' t4' t5' t6' (dl_F p) (dl_fc p) m' (Z_to_bv 64 C) (Z_to_bv 64 INST) (Z_to_bv 64 1023064)
MB MSZ lo); rewrite ?RSP.
- exact M1. - exact M7. - clear - M2 HLk; lia.
- unfold hide, img_hull_lo, img_hull_hi. clear - M4; unfold SEGTOP_A in *; lia.
- exact UF'. - exact MMG'. - exact ST'.
- clear - HLk G1 G8 G4. unfold kHighShadowEnd, K_HIGH_SHADOW_hi, SHB in *. lia.
- clear - N5; lia. - clear - N6; lia. - exact MI'. }
intros ms (y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m'' & -> & MU & WB & MI'' & ST'' & _).
rewrite RSP in MU, ST''.
pose proof LM' as ((G & WG & HGo) & RP & FR & QR & QB).

assert (CLI : forall a, aclient (live Σ0) (frames Σ0) (C + 32) a -> outside [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a).
{ intros a Ha. rewrite <- Elv, <- Efr in Ha.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Ha) as (X1 & X2).
cbn [outside]. split; [exact X1|]. split; [|exact I]. clear - X2 HLk N5. lia. }
assert (STA : forall a n0, C - 112 <= a -> 0 <= n0 -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] a n0).
{ intros a n0 H1 H2. cbn [disjoint_from]. clear - H1 H2 M2 HLk N5. split; [lia | split; [lia | exact I]]. }
assert (SLA : forall j', nth_error (r_st (pr Σk 24)) j' = Some CkBatch -> disjoint_from [(MB, MB + MSZ); (C - 112 - 48, C - 112)] (p_abeg SB 24 j') 8192).
{ intros j' Hj'. pose proof (dk_slot_in Σk HG 24 j' _ ltac:(clear; lia) Hj') as (S1 & S2 & _). change (ClassSize 24) with 8192 in S1, S2.
cbn [disjoint_from]. clear - S1 S2 M5 G7 G4 HLk N5. split; [lia | split; [lia | exact I]]. }
exists (Z_to_bv 64 0x47e7c), y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, m''.
split; [rewrite ret_pc_even; [reflexivity | clear; lia | reflexivity]|].
split.
-
split; [exact (ds_art_nw Σk k s lo (C - 112) HG Hk HLk ltac:(clear - N5; lia) ltac:(clear - N6; lia) Hdep HQB m' m'' HA' MU)|].
split; [exact MI''|]. split; [exact ST''|].
split.
{ exists ((MB, MB + MSZ) :: G). split.
- intros x Hx Ho. cbn [outside] in Ho. destruct Ho as (Ho1 & Ho2). apply (WB x); [clear - Ho1; lia | exact (WG x Hx Ho2)].
- apply Forall_cons; [|exact HGo]. cbn [fst snd]. intros a Ha. split.
+ intros Hc. rewrite <- Elv, <- Efr in Hc.
destruct (ds_client_map Σk k s (C + 32) a HG Hlive Hk Hq ltac:(clear - HLk N5; lia) Hc) as (X1 & _). exact (X1 Ha).
+ clear - Ha M2 HLk. lia. }
split; [exact (rt_pres_trans _ _ _ _ m' m'' RP (fun a Ha => MU a (CLI _ Ha)))|].
split.
{ pose proof FR as (FR1 & FR2 & FR3). split; [|split].
- apply (rwc_nw _ m' m'' _ _ FR1 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR2 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
- apply (rwc_nw _ m' m'' _ _ FR3 MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia. }
apply (proj1 (qcache_rep_iff _ _ _)) in QR. destruct QR as (QH & QC).
apply (proj2 (qcache_rep_iff _ _ _)). split.
+ apply (rwc_nw _ m' m'' _ _ QH MU). apply STA; cbn [cells_size csize Nat.add Z.of_nat]; clear; lia.
+ apply (qchain_nw _ m' m'' _ QC MU). apply Forall_forall. intros (b', ents') Hin.
destruct (dl_batch_of_in Σk _ b' ents' HWP (or_intror Hin)) as (j' & Hj' & Eb'). cbn [fst]. rewrite Eb'. exact (SLA j' Hj').
- apply (proj1 (qbatch_iff _ _ _ _)) in QB. destruct QB as (B1 & (ws & U & Hl & Hf) & Hn).
apply (proj2 (qbatch_iff _ _ _ _)). split; [|split; [|exact Hn]].
+ apply (rwc_nw _ m' m'' _ _ B1 MU). cbn [cells_size csize Nat.add Z.of_nat]. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
+ exists ws. split; [|split; [exact Hl | exact Hf]]. apply (u64_nw _ m' m'' _ _ U MU). rewrite Hl. rewrite Eb.
apply (dsj_sub _ (p_abeg SB 24 ib) 8192); [exact (SLA ib Hib) | clear; lia | clear; lia].
Qed.

End Ret.
