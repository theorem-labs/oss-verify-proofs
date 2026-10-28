(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS MState ITree Nodes.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_defs R_cache_defs R_prim_defs R_glue_defs R_thread R_m2s R_poison R_sec_defs R_mmapordie R_mmapfixed R_mapordie R_secalloc R_secalloc_p4 R_secalloc_B0 R_secalloc_B R_secalloc_B1 R_secalloc_B2 R_comballoc2 R_asan_defs R_allocate1 RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_icfacts RT_maltail RT_malcore_stmt RT_sys_stmt RT_vis RT_malsec_state RT_malsec_front RT_malsec_front2 RT_malsec_rev RT_malsec_pre.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.

#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GWf.
Lemma firstn_upd_last : forall {X} (ws : list X) k x, (k < length ws)%nat -> firstn (S k) (upd ws k x) = firstn k ws ++ [x].
Proof.
  intros X ws. induction ws as [|w ws IH]; intros k x Hk; cbn in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [upd firstn app]. f_equal. apply IH. lia.
Qed.

Lemma sub_fp_of : forall (W W' : list ivl), Forall (fun p => exists q, In q W' /\ fst q <= fst p /\ snd p <= snd q) W -> sub_fp W W'.
Proof.
  intros W W' H x Hx. induction W as [|[lo hi] W IH]; [exact I|]. apply Forall_cons_iff in H as [(q & Hq & H1 & H2) H].
  cbn [outside]. split; [|exact (IH H)]. intros Hy. destruct q as [ql qh]. cbn [fst snd] in *.
  exact (not_outside W' ql qh x Hq ltac:(lia) Hx).
Qed.

Ltac in_pick := first [ left; reflexivity | right; in_pick ].

Ltac sfp_piece := match goal with |- exists q, In q ?W' /\ _ =>
  let rec go l := match l with
    | ?q :: ?l' => first [ exists q; split; [in_pick | cbn [fst snd]; lia] | go l' ]
    end in go W' end.
Ltac sfp := apply sub_fp_of; repeat (apply Forall_cons; [sfp_piece|]); apply Forall_nil.

Lemma dsj_hi : forall (W : list ivl) a k, Forall (fun p => snd p <= a) W -> disjoint_from W a k.
Proof.
  induction W as [|[x y] W IH]; intros a k H; [exact I|]. apply Forall_cons_iff in H as [H1 H]. cbn [fst snd] in H1.
  cbn [disjoint_from]. split; [right; lia | exact (IH a k H)].
Qed.
Ltac dsj_hi_tac := apply dsj_hi; repeat (apply Forall_cons; [cbn [fst snd]; lia|]); apply Forall_nil.

Lemma rw_C8_of_stk : forall (m : mem) lo hi a, stk bsegs m lo hi -> lo <= a -> a + 8 <= hi -> exists w, rw_cells bsegs m a [C8 w].
Proof.
  intros m lo hi a S H1 H2. destruct (stk_split bsegs m lo a hi S ltac:(lia)) as [_ S2].
  destruct (stk_split bsegs m a (a + 8) hi S2 ltac:(lia)) as [S3 _].
  destruct (stk_CB m a 8 S3 ltac:(lia)) as (bs & Hb). destruct (word_of_stk m a (a + 8) a S3 ltac:(lia) ltac:(lia)) as (v & Hv).
  exists v. split; [exact Hv | exact (proj2 Hb)].
Qed.

Lemma sb_div8 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) / 8 = a / 8 + b / 8 /\ (a - b) / 8 = a / 8 - b / 8.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha, Hb; try lia. destruct Ha as [x ->]. destruct Hb as [y ->].
  replace (x * 8 + y * 8) with ((x + y) * 8) by ring. replace (x * 8 - y * 8) with ((x - y) * 8) by ring.
  rewrite !Z.div_mul by lia. lia.
Qed.

Lemma pg_dn_ge : forall x y, x mod 4096 = 0 -> 0 <= x <= y -> x <= pg_dn y.
Proof.
  intros x y Hx Hy. unfold pg_dn. pose proof (Z.div_le_mono x y 4096 ltac:(lia) ltac:(lia)) as D.
  pose proof (Z.div_mod x 4096 ltac:(lia)) as E. rewrite Hx in E. lia.
Qed.

Lemma stk_of_present : forall (m : mem) lo hi, 0 <= lo -> hi <= 2 ^ 64 ->
  (forall a, lo <= a < hi -> shreg a /\ m (Z_to_bv 64 a) <> None) -> stk bsegs m lo hi.
Proof.
  intros m lo hi H0 H1 H. split; [exact H0|]. split; [exact H1|]. intros a Ha. destruct (H a Ha) as (Hs & Hp).
  assert (Ea : bv_unsigned (wa a) = a) by (apply wa_unsigned; lia).
  assert (Hs' : shreg (bv_unsigned (wa a))) by (rewrite Ea; exact Hs).
  rewrite (wview_shreg m (wa a) Hs'). split; [exact Hp|]. unfold mrd. unfold wa in *.
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | congruence].
Qed.

Section SB.
Variables (Σ : rtsA) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word)
          (F : bvmap 5 word) (fc : bv 32) (n lo P : Z) (tr : list Z) (tb : list word) (j0 : list byte).
Hypothesis Hn : 64512 < n <= 0x20001000.
Hypothesis HA : ART_A Σ mX.
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 2144 <= USTACK_TOP.
Hypothesis HG : sgrant_ok Σ P (smsz n).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation PAB := (l_PAB (lay Σ)).
#[local] Notation msz := (smsz n).
#[local] Notation SZ := (needed2 n).
#[local] Notation k := (Z.of_nat (length (sec Σ))).

Lemma sb_geo :
  65536 < SZ /\ SZ mod 8 = 0 /\ SZ + 16384 <= 2 ^ 47 /\ sa_msz SZ = msz /\ P mod 4096 = 0 /\ PAB mod 4096 = 0
  /\ kHighShadowEnd + 8 <= lo /\ 2 ^ 44 + SHB + 8 <= l_ACEIL L /\ l_ACEIL L <= 2 ^ 47 /\ B + 2144 <= 2 ^ 47
  /\ SEGTOP_A <= P /\ P + msz <= l_ACEIL L /\ 72704 <= msz /\ msz mod 4096 = 0 /\ msz <= 0x20005000
  /\ 0 < T /\ T + 4096 <= l_ACEIL L /\ SEGTOP_A <= TCX /\ TCX + 0x10000 <= l_ACEIL L
  /\ SEGTOP_A <= PAB /\ PAB + 0x800000 <= l_ACEIL L.
Proof using Hn HA LOW LOR SPT HG.
  pose proof (msec_size n Hn) as (K1 & K2 & K3 & _).
  pose proof (smsz_sa n Hn) as (E1 & _ & _).
  pose proof (rv_map Σ mX P n HA HG Hn) as (M1 & M2 & M3 & _ & M5 & M6 & M7 & M8 & M9).
  pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & _ & T3 & _ & T5).
  pose proof (geo_grant Σ mX HA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (X1 & _ & X3 & _ & X5).
  pose proof (geo_grant Σ mX HA PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (A1 & A2 & A3 & _ & A5).
  pose proof (g_aceil Σ (geo_of_ART Σ mX HA)) as (Y1 & Y2 & Y3).
  assert (X5' : SEGTOP_A <= TCX) by (clear - X1 X5; unfold SEGTOP_A in *; destruct X5; lia).
  assert (A5' : SEGTOP_A <= PAB) by (clear - A1 A5; unfold SEGTOP_A in *; destruct A5; lia).
  clear T5 X5 A5.
  split; [exact K1|]. split; [exact K2|]. split; [clear - Hn K3; lia|]. split; [symmetry; exact E1|]. split; [exact M2|].
  split; [exact A2|].
  split; [clear - LOW Y3; unfold kHighShadowEnd, SHB in *; lia|]. split; [clear - Y3; unfold SHB in *; lia|]. split; [exact Y2|].
  split; [clear - SPT; unfold USTACK_TOP in *; lia|].
  split; [exact M5|]. split; [exact M3|]. split; [exact M6|]. split; [exact M7|]. split; [exact M8|].
  split; [exact T1|]. split; [exact T3|]. split; [exact X5'|]. split; [exact X3|]. split; [exact A5' | exact A3].
Qed.

Lemma sb_obj :
  gobj P (sa_msz SZ) lo /\ gobj T 4096 lo /\ gobj TCX 0xa0 lo /\ gobj PAB 0x800000 lo
  /\ sapart P (sa_msz SZ) T 4096 /\ sapart P (sa_msz SZ) TCX 0xa0 /\ sapart T 4096 TCX 0xa0
  /\ sapart P (sa_msz SZ) PAB 0x800000 /\ sapart T 4096 PAB 0x800000.
Proof using Hn HA LOW LOR SPT HG.
  pose proof (smsz_sa n Hn) as (E1 & _ & _).
  pose proof (rv_map Σ mX P n HA HG Hn) as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9).
  pose proof (rv_grant_apart Σ mX P n HA HG) as GA.
  pose proof (geo_grant Σ mX HA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as (T1 & T2 & T3 & T4 & T5).
  pose proof (geo_grant Σ mX HA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as (X1 & X2 & X3 & X4 & X5).
  pose proof (geo_grant Σ mX HA PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as (A1 & A2 & A3 & A4 & A5).
  pose proof (GA T 4096 ltac:(unfold startup_grants; do 2 right; left; reflexivity)) as PT.
  pose proof (GA TCX 0x10000 ltac:(unfold startup_grants; do 3 right; left; reflexivity)) as PX.
  pose proof (GA PAB 0x800000 ltac:(unfold startup_grants; right; left; reflexivity)) as PA.
  pose proof (geo_apart Σ mX HA 2 3 _ _ ltac:(lia) eq_refl eq_refl) as TX. pose proof (geo_apart Σ mX HA 1 2 _ _ ltac:(lia) eq_refl eq_refl) as AT.
  cbn [fst snd] in TX, AT. clear GA.
  rewrite <- E1.
  unfold gobj, sapart, img_hull_lo, img_hull_hi, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SEGTOP_A in *.
  unfold apart in PT, PX, PA, TX, AT.
  split; [split; [clear - M1; lia|]; split; [clear - M3 LOW; lia|]; split; [clear - M4; lia | clear - M5; lia]|].
  split; [split; [clear - T1; lia|]; split; [clear - T3 LOW; lia|]; split; [clear - T4; destruct T4; lia | clear - T5; destruct T5; lia]|].
  split; [split; [clear - X1; lia|]; split; [clear - X3 LOW; lia|]; split; [clear - X4; destruct X4; lia | clear - X5; destruct X5; lia]|].
  split; [split; [clear - A1; lia|]; split; [clear - A3 LOW; lia|]; split; [clear - A4; destruct A4; lia | clear - A5; destruct A5; lia]|].
  split; [clear - PT; lia|]. split; [clear - PX; destruct PX; lia|]. split; [clear - TX; destruct TX; lia|].
  split; [clear - PA; lia | clear - AT; destruct AT; lia].
Qed.

Lemma sb_shad_stk : forall (m : mem), vis_rep L (shw P n :: rtA_allow Σ) m -> stk bsegs m (shad P) (shad (P + msz)).
Proof using Hn HA LOW LOR SPT HG.
  intros m HV. pose proof (rv_shad Σ mX P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (rv_map Σ mX P n HA HG Hn) as (M1 & M2 & M3 & _ & M5 & M6 & M7 & M8 & M9).
  pose proof (fk_aceil Σ (geo_of_ART Σ mX HA)) as (Y1 & Y2).
  pose proof HG as (_ & Hap).
  assert (Hp : P + msz <= pg_dn (l_ACEIL L)) by (apply pg_dn_ge; [rewrite Z.add_mod, M2, M7 by lia; reflexivity | lia]).
  pose proof (fk_shad_mono _ _ Hp) as Hsp.
  apply stk_of_present; [unfold SHB in *; lia | unfold K_HIGH_SHADOW_hi in *; lia|]. intros a Ha.
  assert (Hs : shreg a).
  { clear - Ha S5 S6 S7. unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *. destruct S7; lia. }
  split; [exact Hs|].
  assert (Ea : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; clear - Hs; unfold shreg, K_LOW_SHADOW_lo, K_LOW_SHADOW_hi, K_HIGH_SHADOW_lo, K_HIGH_SHADOW_hi in Hs; lia).
  unfold vis_rep in HV. apply HV.
  - rewrite Ea. exact Hs.
  - rewrite page_base_eq, Ea. pose proof (pg_dn_facts a ltac:(unfold SHB in *; lia)) as (D1 & D2 & D3).
    destruct (page_meet (pg_dn a) a (a + 1) (shad P) (shad (P + msz)) D2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (Q1 & Q2).
    apply (allowed_of_window _ (pg_dn (shad P)) (pg_up (shad (P + msz))) (pg_dn a)); [left; reflexivity | exact Q1 | exact Q2|].
    unfold K_HIGH_SHADOW_hi in *. lia.
  - rewrite Ea. lia.
  - intros e He. rewrite Ea.
    pose proof (proj1 (Forall_forall _ _) Hap e ltac:(unfold rt_maps; apply in_or_app; right; exact He)) as X. unfold apart in X.
    pose proof (bv_unsigned_in_range 64 (fst e)) as R1. pose proof (bv_unsigned_in_range 64 (snd e)) as R2.
    unfold bv_modulus in R1, R2. cbn [Z.of_N] in R1, R2.
    destruct X as [X|X].
    + pose proof (fk_shad_mono _ _ X). lia.
    + pose proof (fk_shad_mono _ _ X). lia.
Qed.

Lemma sb_cells : forall (mA : mem), ART_A Σ mA ->
  ps_cells mA /\ thread_cells TCX T mA /\ exists mm md, rw_cells bsegs mA (T + 2872) [C8 mm; C8 md].
Proof.
  intros mA HAA. pose proof (ART_consts Σ mA HAA) as (_ & _ & THC & _ & PSC & _ & _ & ICR).
  destruct ICR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
                   & _ & _ & St & _).
  split; [exact PSC|]. split; [exact THC|].
  destruct (rw_C8_of_stk mA _ _ (T + 2872) St ltac:(lia) ltac:(lia)) as (mm & MM).
  destruct (rw_C8_of_stk mA _ _ (T + 2880) St ltac:(lia) ltac:(lia)) as (md & MD).
  exists mm, md. apply (proj2 (sec_rw_app2 mA (T + 2872) [C8 mm] [C8 md])). split; [exact MM|]. cs_size. replace (T + 2872 + Z.of_nat 8) with (T + 2880) by lia. exact MD.
Qed.

Lemma sb_shad_geo : shad P + 512 + SZ / 8 = shad (P + 4096 + SZ) /\ shad (P + 4096 + SZ) + (sa_msz SZ - 4096 - SZ) / 8 = shad (P + msz)
  /\ 0 <= (sa_msz SZ - 4096 - SZ) / 8 /\ SHB <= shad P /\ shad (P + msz) <= K_HIGH_SHADOW_hi /\ shad (P + msz) = shad P + msz / 8
  /\ 9088 <= msz / 8.
Proof using Hn HA LOW LOR SPT HG.
  pose proof sb_geo as (Q1 & Q2 & Q3 & Q4 & Q5 & _ & _ & _ & _ & _ & _ & _ & Q13 & Q14 & _).
  pose proof (rv_shad Σ mX P n HA HG Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (sa_msz_facts SZ ltac:(lia)) as (F1 & F2). rewrite Q4 in *.
  assert (P8 : P mod 8 = 0) by (apply Z.mod_divide in Q5; [|lia]; apply Z.mod_divide; [lia|]; apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact Q5]).
  assert (M8 : msz mod 8 = 0) by (apply Z.mod_divide in Q14; [|lia]; apply Z.mod_divide; [lia|]; apply (Z.divide_trans 8 4096); [exists 512; reflexivity | exact Q14]).
  assert (E1 : shad (P + 4096 + SZ) = shad P + (4096 + SZ) / 8) by (rewrite <- Z.add_assoc; apply shad_add8; [exact P8 | rewrite Z.add_mod, Q2 by lia; reflexivity]).
  destruct (sb_div8 4096 SZ ltac:(reflexivity) Q2) as (D1 & _). change (4096 / 8) with 512 in D1.
  assert (E2 : (msz - 4096 - SZ) / 8 = msz / 8 - (4096 + SZ) / 8).
  { replace (msz - 4096 - SZ) with (msz - (4096 + SZ)) by ring.
    exact (proj2 (sb_div8 msz (4096 + SZ) M8 ltac:(rewrite Z.add_mod, Q2 by lia; reflexivity))). }
  split; [rewrite E1, D1; ring|]. split; [rewrite E1, E2, S2; ring|]. split; [apply Z.div_pos; lia|].
  split; [exact S5|]. split; [exact S6|]. split; [exact S2 | exact S4].
Qed.

Lemma stk_hdr_zeros : forall (m : mem) kk, shdr m P msz SZ kk ->
  rw_cells bsegs m (P + 32) [CB (Z.to_nat (msz - 32)) (repeat (Z_to_bv 8 0) (Z.to_nat (msz - 32)))] -> stk bsegs m P (P + msz).
Proof using Hn HA LOW LOR SPT HG.
  intros m kk HD ZB. pose proof sb_geo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Q13 & _).
  pose proof (stk_of_rw_cells bsegs m P _ HD) as S1. pose proof (stk_of_rw_cells bsegs m (P + 32) _ ZB) as S2.
  cbn [cells_size csize Nat.add] in S1, S2. rewrite Nat.add_0_r, Z2Nat.id in S2 by lia.
  replace (P + 32 + (msz - 32)) with (P + msz) in S2 by lia.
  exact (stk_merge bsegs m P (P + 32) (P + msz) S1 S2 ltac:(lia)).
Qed.

Definition bfacts (mA : mem) : Prop :=
  ART_A Σ mA /\ mem_inv bsegs mA /\ wmono bsegs mX mA
  /\ (forall a : word, aclient (live Σ) (frames Σ) (B + -16) (bv_unsigned a) -> mA a = mX a)
  /\ vis_rep L (shw P n :: rtA_allow Σ) mA
  /\ rw_cells bsegs mA (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 8);
                                    C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x598c0)]
  /\ af_cells B s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A mA j0 /\ trc_cells B tr mA tb.

Definition W_1s (usp : Z) : list ivl :=
  [(P, P + msz); (shad P, shad (P + msz)); (T + 2872, T + 2888); (INST + 0x70, INST + 0x2d0); (PAB, PAB + 0x20000);
   (l_ACEIL L, usp)].
Definition W_1 : list ivl := W_1s (B + -144).

Definition smid_facts (m : mem) : Prop :=
  shdr m P msz SZ k /\ stk bsegs m P (P + msz)
  /\ rw_cells bsegs m (shad P) [CB 512 (repeat (Z_to_bv 8 250) 512)]
  /\ sec_core m PAB 0x4000 (k + 1) /\ sec_pad m /\ sec_junk m
  /\ (exists ws, u64arr bsegs m PAB ws /\ Z.of_nat (length ws) = 0x4000
                 /\ firstn (length (sec Σ) + 1) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ ++ [sec_new P n])).

Definition smid (ms : machine_state) : Prop :=
  exists (mA m2 : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    bfacts mA
    /\ ms = MS (mkR (Z_to_bv 64 0x598c0) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
                 (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 (P + 4096)) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
                 (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
               F (Z_to_bv 64 0x598c0) fc None m2 (seg_rom bsegs)
    /\ munch W_1 mA m2 /\ wmono bsegs mA m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (B + -144) /\ smid_facts m2.

Lemma sb_epi : forall (mA m1 : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  bfacts mA -> munch (W_1s (B + -192)) mA m1 -> wmono bsegs mA m1 -> mem_inv bsegs m1 -> stk bsegs m1 lo (B + -192) -> smid_facts m1 ->
  evt bsegs smid (MS (mkR (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -192)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 8) (Z_to_bv 64 n)
                        (Z_to_bv 64 (P + 4096)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n))
                        (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T)
                        (Z_to_bv 64 1) t3 t4 t5 t6)
                    F (ret_pc (Z_to_bv 64 comballoc_retS)) fc None m1 (seg_rom bsegs)).
Proof using Hn HA LOW LOR SPT HG.
  intros mA m1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 BF MU1 WM1 MI1 ST1 SF1.
  pose proof sb_geo as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof sb_shad_geo as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  pose proof BF as (_ & _ & _ & _ & _ & FRA & _).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by lia.
  assert (FR1 : rw_cells bsegs m1 (B + -192) [C8 (Z_to_bv 64 (rz_size n)); C8 (Z_to_bv 64 SZ); C8 (Z_to_bv 64 8);
                                    C8 (Z_to_bv 64 n); C8 (Z_to_bv 64 (Z.b2z (from_primary n))); C8 (Z_to_bv 64 0x598c0)]).
  { apply (rw_cells_transport bsegs _ mA m1 _ _ FRA MU1 WM1). cs_size. unfold W_1s. cbn [disjoint_from].
    split; [lia|]. split; [unfold K_HIGH_SHADOW_hi, SHB in *; lia|].
    split; [lia|]. split; [unfold INST, g_instance, SEGTOP_A in *; lia|]. split; [lia|]. split; [lia | exact I]. }
  rewrite (ret_pc_even comballoc_retS) by (unfold comballoc_retS; lia || reflexivity).
  replace (Z_to_bv 64 (B + -192)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (B + -144)) - 48)) by (rewrite unsigned_lit by exact RS; f_equal; lia).
  eapply evt_mono.
  { apply (comballoc_big_B_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 (P + 4096)) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
             (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6 F fc m1
             (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 0x598c0) (l_ACEIL L) lo);
      rewrite ?(unsigned_lit (B + -144)) by exact RS.
    - replace (B + -144 - 48) with (B + -192) by lia. exact FR1.
    - replace (B + -144 - 48) with (B + -192) by lia. exact ST1.
    - exact LOW.
    - exact Q7.
    - lia.
    - lia.
    - exact MI1. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite (unsigned_lit (B + -144)) in MU2, ST2 by exact RS. replace (B + -144 - 48) with (B + -192) in MU2 by lia.
  rewrite (ret_pc_even 0x598c0) by (lia || reflexivity). rewrite (unsigned_lit (P + 4096)) by (unfold SEGTOP_A in *; lia).
  exists mA, m2, t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6'. split; [exact BF|]. split; [reflexivity|].
  split.
  { apply (munch_trans _ mA m1 m2).
    - eapply munch_weaken; [|exact MU1]. unfold W_1, W_1s. sfp.
    - eapply munch_weaken; [|exact MU2]. unfold W_1, W_1s. sfp. }
  split; [exact (wmono_trans bsegs _ _ _ WM1 WM2)|]. split; [exact MI2|]. split; [exact ST2|].

  assert (D2 : forall a j, a + j <= l_ACEIL L -> disjoint_from [(B + -192, B + -144)] a j)
    by (intros a j Hj; cbn [disjoint_from]; split; [left; lia | exact I]).
  destruct SF1 as (HD & SK & SH & SC & PAD & SJ & (ws & WS & Hws & Hwsf)).
  unfold shdr, sec_core, sec_pad, sec_junk in *. destruct SC as (C1 & C2 & C3).
  destruct SJ as ((b & jj & w1 & w2 & w3 & w4 & J1) & (bl & Hbl & J2) & (ga & gm & J3)).
  assert (IMG : forall a k0, a + k0 <= SEGTOP_A -> disjoint_from [(B + -192, B + -144)] a k0) by (intros a k0 Hk0; apply D2; lia).
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ HD MU2 WM2); cs_size; apply D2; lia|].
  split; [exact (stk_wmono m1 m2 _ _ SK WM2)|].
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ SH MU2 WM2); cs_size; apply D2; unfold K_HIGH_SHADOW_hi, SHB in *; lia|].
  split; [split; [|split]|].
  { apply (rw_cells_transport bsegs _ m1 m2 _ _ C1 MU2 WM2). cs_size. apply IMG. unfold i_sec_chunks, INST, g_instance, SEGTOP_A; lia. }
  { apply (rw_cells_transport bsegs _ m1 m2 _ _ C2 MU2 WM2). cs_size. apply IMG. unfold i_sec_nres, INST, g_instance, SEGTOP_A; lia. }
  { apply (rw_cells_transport bsegs _ m1 m2 _ _ C3 MU2 WM2). cs_size. apply IMG. unfold i_sec_mutex, INST, g_instance, SEGTOP_A; lia. }
  split; [apply (rw_cells_transport bsegs _ m1 m2 _ _ PAD MU2 WM2); cs_size; apply IMG; unfold i_sec_mutex, INST, g_instance, SEGTOP_A; lia|].
  split.
  { split; [exists b, jj, w1, w2, w3, w4; apply (rw_cells_transport bsegs _ m1 m2 _ _ J1 MU2 WM2); cs_size; apply IMG;
            unfold i_sec_sorted, INST, g_instance, SEGTOP_A; lia|].
    split; [exists bl; split; [exact Hbl|]; apply (u64arr_transport bsegs _ m1 m2 _ _ J2 MU2 WM2); rewrite Hbl; apply IMG;
            unfold i_sec_bylog, INST, g_instance, SEGTOP_A; lia|].
    exists ga, gm. apply (rw_cells_transport bsegs _ m1 m2 _ _ J3 MU2 WM2). cs_size. apply IMG. unfold i_gstat_alloc, INST, g_instance, SEGTOP_A; lia. }
  exists ws. split; [|split; [exact Hws | exact Hwsf]]. apply (u64arr_transport bsegs _ m1 m2 _ _ WS MU2 WM2). rewrite Hws. apply D2. lia.
Qed.

Lemma sb_ecall_cells : forall (mA : mem), ART_A Σ mA -> vis_rep L (shw P n :: rtA_allow Σ) mA ->
  ps_cells mA /\ thread_cells TCX T mA /\ (exists mm md, rw_cells bsegs mA (T + 2872) [C8 mm; C8 md])
  /\ sec_core mA PAB (sec_nres Σ) k /\ sec_pad mA /\ sec_junk mA /\ sec_range mA PAB
  /\ (exists ws, u64arr bsegs mA PAB ws /\ Z.of_nat (length ws) = sec_nres Σ
                 /\ firstn (length (sec Σ)) ws = map (fun s => Z_to_bv 64 (s_mb s)) (sec Σ))
  /\ (exists shj1, rw_cells bsegs mA (shad P) [CB 512 shj1])
  /\ (exists shj2, rw_cells bsegs mA (shad (P + 4096 + SZ)) [CB (Z.to_nat ((sa_msz SZ - 4096 - SZ) / 8)) shj2]).
Proof using Hn HA LOW LOR SPT HG.
  intros mA HAA HV. pose proof (sb_cells mA HAA) as (PSC & THC & TS). pose proof (ART_sec Σ mA HAA) as (SC & PAD & WS & _ & SRG & SJ & _).
  pose proof (sb_shad_stk mA HV) as SST. pose proof sb_shad_geo as (H1 & H2 & H3 & H4 & H5 & H6 & H7).
  pose proof sb_geo as (Q1 & _).
  split; [exact PSC|]. split; [exact THC|]. split; [exact TS|]. split; [exact SC|]. split; [exact PAD|]. split; [exact SJ|].
  split; [exact SRG|]. split; [exact WS|].
  split.
  - apply (stk_CB mA (shad P) 512); [|lia]. exact (proj1 (stk_split bsegs mA _ (shad P + 512) _ SST ltac:(lia))).
  - apply (stk_CB mA (shad (P + 4096 + SZ)) ((sa_msz SZ - 4096 - SZ) / 8)); [|exact H3]. rewrite H2.
    exact (proj2 (stk_split bsegs mA (shad P) (shad (P + 4096 + SZ)) (shad (P + msz)) SST ltac:(pose proof (Z.div_pos SZ 8 ltac:(lia) ltac:(lia)); lia))).
Qed.

Ltac sb_sfp_pre := pose proof sb_shad_geo as (Hh1 & Hh2 & Hh3 & Hh4 & Hh5 & Hh6 & Hh7);
  pose proof (Z.div_pos SZ 8 ltac:(lia) ltac:(lia));
  unfold i_sec_mutex, i_sec_nres, i_sec_sorted, i_sec_bylog, i_gstat_alloc.

Theorem sb_notfirst : forall ms, bpre Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 ms ->
  k < sec_nres Σ -> evt bsegs smid ms.
Proof using Hn HA LOW LOR SPT HG.
  intros ms (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & mA & -> & HAA & MIA & WMA & CLA & VIA & FRA & SAF & MODF & STA & MMA
             & PGA & NMA & AFA & TRA) Hk.
  assert (BF : bfacts mA) by exact (conj HAA (conj MIA (conj WMA (conj CLA (conj VIA (conj FRA (conj AFA TRA))))))).
  pose proof sb_geo as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof sb_obj as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
  pose proof (sb_ecall_cells mA HAA VIA) as (PSC & THC & (mm & md & TS) & SC & PAD & SJ & SRG & (ws & WS & Hws & Hwsf) & (shj1 & SH1)
                                             & (shj2 & SH2)).
  pose proof (ART_wf Σ mA HAA) as (_ & _ & _ & (HSM & HN & _) & _).
  assert (Hnres : sec_nres Σ = 0x4000) by (destruct HN as [E|E]; [rewrite E in Hk; lia | exact E]).
  assert (RS : 0 <= B + -192 < 2 ^ 64) by lia.
  eapply evt_cut.
  { exact (secalloc_B_spec (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -192)) gp t0' t1' t2' a6' (Z_to_bv 64 8) (Z_to_bv 64 n)
             (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
             (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6' F fc mA SZ P PAB (sec_nres Σ) k
             TCX T lo ws mm md shj1 shj2 (conj Q1 (conj Q2 Q3)) Q5 O1 O2 O3 O4 O5 O6 O7 O8 O9 ltac:(lia) Hws ltac:(lia)
             ltac:(rewrite Hnres; reflexivity) SAF MODF STA MMA PGA PSC THC TS SC PAD SJ WS SRG SH1 SH2 Q7
             ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) MIA). }
  intros ms1 (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & MU1 & WM1 & MI1 & ST1 & K1).
  rewrite (unsigned_lit (B + -192)) in MU1, ST1 by exact RS.
  apply (sb_epi mA m1 t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a BF); [| exact WM1 | exact MI1 | exact ST1 |].
  - eapply munch_weaken; [|exact MU1]. unfold sb_W, W_1s. rewrite Q4. sb_sfp_pre. sfp.
  - destruct K1 as (HD & ZB & SH & _ & _ & SC1 & PAD1 & SJ1 & WS1). rewrite Q4 in HD, ZB.
    split; [exact HD|]. split; [exact (stk_hdr_zeros m1 _ HD ZB)|]. split; [exact SH|]. split; [rewrite <- Hnres; exact SC1|]. split; [exact PAD1|]. split; [exact SJ1|].
    exists (upd ws (Z.to_nat k) (Z_to_bv 64 P)). split; [exact WS1|]. split; [rewrite upd_length; lia|].
    rewrite Nat2Z.id, Nat.add_1_r. rewrite firstn_upd_last by lia. rewrite Hwsf, map_app. reflexivity.
Qed.

Definition sb1_st (ms : machine_state) : Prop :=
  exists (mA : mem) (mm md : word), bfacts mA /\ sec Σ = [] /\ sec_nres Σ = 0
    /\ secalloc_B1_post (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -192)) gp (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8)
         (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B) (Z_to_bv 64 (0 + - (8)))
         (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) F fc P SZ PAB 0 T lo [] mm md mA ms.

Theorem sb_first_A : forall ms, bpre Σ mX B gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc n lo P tr tb j0 ms ->
  sec_nres Σ = 0 -> evt bsegs sb1_st ms.
Proof using Hn HA LOW LOR SPT HG.
  intros ms (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & mA & -> & HAA & MIA & WMA & CLA & VIA & FRA & SAF & MODF & STA & MMA
             & PGA & NMA & AFA & TRA) Hk.
  assert (BF : bfacts mA) by exact (conj HAA (conj MIA (conj WMA (conj CLA (conj VIA (conj FRA (conj AFA TRA))))))).
  pose proof sb_geo as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof sb_obj as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
  pose proof (sb_ecall_cells mA HAA VIA) as (PSC & THC & (mm & md & TS) & SC & PAD & SJ & SRG & (ws & WS & Hws & Hwsf) & (shj1 & SH1)
                                             & (shj2 & SH2)).
  pose proof (ART_wf Σ mA HAA) as (_ & _ & _ & (HSM & HN & HNE & _) & _).
  assert (Hs0 : sec Σ = []).
  { destruct (sec Σ) as [|s l] eqn:E; [reflexivity|]. exfalso.
    assert (X : sec Σ <> []) by (rewrite E; discriminate). pose proof (HNE ltac:(first [exact X | discriminate])) as Y.
    rewrite Y in Hk. discriminate. }
  assert (Hw0 : ws = []) by (destruct ws; [reflexivity | rewrite Hk in Hws; cbn [length] in Hws; lia]). subst ws.
  rewrite Hk, Hs0 in SC. cbn [length Z.of_nat] in SC.
  assert (RS : 0 <= B + -192 < 2 ^ 64) by lia.
  eapply evt_mono.
  { exact (secalloc_B1_spec (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -192)) gp t0' t1' t2' a6' (Z_to_bv 64 8) (Z_to_bv 64 n)
             (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
             (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6' F fc mA SZ P PAB 0
             TCX T lo [] mm md shj1 shj2 (conj Q1 (conj Q2 Q3)) Q5 O1 O2 O3 O4 O5 O6 O7 O8 O9 ltac:(lia) eq_refl ltac:(lia)
             eq_refl Q6 SAF MODF STA MMA PGA PSC THC TS SC PAD SJ WS SRG SH1 SH2 Q7
             ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) MIA). }
  intros ms1 HP. exists mA, mm, md. split; [exact BF|]. split; [exact Hs0|]. split; [exact Hk|]. exact HP.
Qed.

Definition eff_pab : SyscallEffect := mkEffect (Z_to_bv 64 (PAB + 8 * 0)) [] [(Z_to_bv 64 (PAB + 8 * 0), Z_to_bv 64 0x20000)].

Lemma sb1_regs : forall ms, sb1_st ms -> ms_svc_pending ms = Some (Z_to_bv 64 222) /\ areg ms 10 = Z_to_bv 64 (PAB + 8 * 0)
  /\ areg ms 11 = Z_to_bv 64 0x20000 /\ areg ms 12 = Z_to_bv 64 3 /\ areg ms 13 = Z_to_bv 64 50 /\ areg ms 15 = Z_to_bv 64 0.
Proof.
  intros ms (mA & mm & md & _ & _ & _ & (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & kk & m' & -> & _)).
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity | reflexivity].
Qed.

Theorem sb_first_B : forall ms, sb1_st ms -> evt bsegs smid (nretA ms eff_pab).
Proof using Hn HA LOW LOR SPT HG.
  intros ms (mA & mm & md & BF & Hs0 & Hk & (t0' & t1' & t2' & a6' & t3' & t4' & t5' & t6' & kk & mB & -> & MU & WM & MI & MF & ST & MM
                                            & Hkk & Hx & MID)).
  pose proof sb_geo as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15 & Q16 & Q17 & Q18 & Q19 & Q20 & Q21).
  pose proof sb_obj as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
  assert (RS : 0 <= B + -192 < 2 ^ 64) by lia.
  rewrite (unsigned_lit (B + -192)) in MU by exact RS.
  unfold eff_pab.
  eapply evt_cut.
  { exact (secalloc_B2_spec (Z_to_bv 64 comballoc_retS) (Z_to_bv 64 (B + -192)) gp t0' t1' t2' a6' (Z_to_bv 64 8) (Z_to_bv 64 n)
             (Z_to_bv 64 8) (Z_to_bv 64 SZ) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST) (Z_to_bv 64 B)
             (Z_to_bv 64 (0 + - (8))) (Z_to_bv 64 7) (Z_to_bv 64 T) (Z_to_bv 64 1) t3' t4' t5' t6' F fc mB SZ P PAB 0 T lo kk [] mm md
             (conj Q1 (conj Q2 Q3)) Q5 Q6 O1 O2 O4 O5 O8 O9 eq_refl ltac:(lia) ltac:(lia) eq_refl Hkk Hx MF ST MM MID Q7
             ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) ltac:(rewrite (unsigned_lit (B + -192)) by exact RS; lia) MI). }
  intros ms1 (t0a & t1a & t2a & a1a & a2a & a3a & a4a & a5a & a6a & a7a & t3a & t4a & t5a & t6a & m1 & -> & MU1 & WM1 & MI1 & ST1 & K1).
  rewrite (unsigned_lit (B + -192)) in MU1, ST1 by exact RS.
  apply (sb_epi mA m1 t0a t1a t2a a1a a2a a3a a4a a5a a6a a7a t3a t4a t5a t6a BF); [| exact (wmono_trans bsegs _ _ _ WM WM1) | exact MI1
                                                                                   | exact ST1 |].
  - apply (munch_trans _ mA mB m1).
    + eapply munch_weaken; [|exact MU]. unfold sb1_W, sb_W, W_1s. rewrite Q4. sb_sfp_pre. sfp.
    + eapply munch_weaken; [|exact MU1]. unfold sb2_W, sa_W4, W_1s. sb_sfp_pre. sfp.
  - destruct K1 as (HD & ZB & SH & _ & _ & SC1 & PAD1 & SJ1 & WS1). rewrite Q4 in HD, ZB. unfold smid_facts. rewrite Hs0. cbn [length Z.of_nat app].
    split; [exact HD|]. split; [exact (stk_hdr_zeros m1 _ HD ZB)|]. split; [exact SH|]. split; [exact SC1|]. split; [exact PAD1|]. split; [exact SJ1|].
    exists (upd ([] ++ repeat (Z_to_bv 64 0) (Z.to_nat 16384)) (Z.to_nat 0) (Z_to_bv 64 P)). split; [exact WS1|].
    split; [rewrite upd_length, app_nil_l, repeat_length; reflexivity|]. reflexivity.
Qed.

End SB.
