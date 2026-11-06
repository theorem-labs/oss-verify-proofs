(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1d7 X1cx X1cy X1cp X1cj X1dd X1cg X1cm X1cs X1da.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require Import X1rw X1sa X1rn X1s9.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.SpecA Require X1rx X1ry.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require X1cn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X058 X0j5.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X19o.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X19o.
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition SEGTOP_A : Z := 0x65b000.

Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.

Definition RT_STACK : Z := 0x10000.

Definition LIVE_MAX : Z := 64.
Definition FRAMES_MAX : nat := 16.

Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

Definition e_malloc : Z := 0x67f84.
Definition e_free : Z := 0x67f80.
Definition e_calloc : Z := 0x67f88.
Definition e_realloc : Z := 0x67f8c.
Definition e_strlen : Z := 0x56ccc.
Definition e_strnlen : Z := 0x56cd0.
Definition e_memchr : Z := 0x56ce4.
Definition e_memset : Z := 0x663f4.
Definition e_memcpy : Z := 0x663fc.
Definition e_memmove : Z := 0x663f8.
Definition e_bcmp : Z := 0x56ce0.
Definition e_asan_memmove : Z := 0x66adc.
Definition e_asan_memcpy : Z := 0x66400.
Definition e_asan_memset : Z := 0x6689c.
Definition e_read : Z := 0x56cec.
Definition e_fwrite : Z := 0x56cf0.
Definition e_vprintf : Z := 0x56cfc.
Definition e_vfprintf : Z := 0x56d00.
Definition e_fprintf : Z := 0x56d08.

Definition FS_CLASSES : list nat := [0; 2; 5; 8]%nat.
Definition e_stack_malloc (k : nat) : Z :=
match k with 0%nat => 0x51314 | 1%nat => 0x51488 | 2%nat => 0x51618 | 5%nat => 0x517b4 | 6%nat => 0x51a74 | _ => 0x51c58 end.

Definition e_stack_free (k : nat) : Z := match k with 5%nat => 0x519c0 | 6%nat => 0x51c10 | _ => 0x51dd4 end.

Definition e_alloca_poison : Z := 0x51e24.
Definition e_allocas_unpoison : Z := 0x51f50.

Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
match v with
| 0 => 0x6a1ac | 1 => 0x6a1c4 | 2 => 0x6a1dc | 3 => 0x6a1f4 | 4 => 0x6a20c | 5 => 0x6a224 | 6 => 0x6a23c
| 7 => 0x6a254 | 241 => 0x6a26c | 242 => 0x6a284 | 243 => 0x6a29c | 245 => 0x6a2b4 | _ => 0x6a2cc
end.

Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

Definition ALLOC_RAS : list Z :=

[0x96308; 0x9635c; 0x96380; 0x964b0; 0x965e8; 0x9667c; 0x976d8; 0x976e0; 0x977a0; 0x97ba0;
0x9a0a4; 0xbd470; 0xbd48c; 0xbd4a8; 0xbd4c4; 0xbd4e0; 0xbd4fc; 0xbd518; 0xbd534; 0xbd550;
0xc122c; 0xc123c; 0xc124c; 0xc12b4; 0xc12c0; 0xc12cc; 0xc1550; 0xc15fc; 0xc1614; 0xc168c;
0xc1734; 0xc1764; 0xc1774].

Definition SITE_TRACES : list (list Z) :=
map (fun r => [r]) ALLOC_RAS ++
[[0x97310; 0x96650];
[0x97440; 0x96650];
[0x9744c; 0x96650];
[0x97470; 0x96650];
[0x99f28; 0x96650];
[0xa0410; 0x96650];
[0xa0410; 0x971d0; 0x96650];
[0xa0410; 0xbcd9c; 0x971d0; 0x96650];
[0xbcd18; 0x971d0; 0x96650];
[0xbcd18; 0xbcd9c; 0x971d0; 0x96650];
[0xbcf8c; 0x971d0; 0x96650];
[0xbcf8c; 0xbcd9c; 0x971d0; 0x96650];
[0xbcfb0; 0x971d0; 0x96650];
[0xbcfb0; 0xbcd9c; 0x971d0; 0x96650];
[0xbcfe0; 0x971d0; 0x96650];
[0xbcfe0; 0xbcd9c; 0x971d0; 0x96650];
[0xbd018; 0x971d0; 0x96650];
[0xbd018; 0xbcd9c; 0x971d0; 0x96650];
[0xbd048; 0x971d0; 0x96650];
[0xbd048; 0xbcd9c; 0x971d0; 0x96650];
[0xbd078; 0x971d0; 0x96650];
[0xbd078; 0xbcd9c; 0x971d0; 0x96650];
[0xbd0a8; 0x971d0; 0x96650];
[0xbd0a8; 0xbcd9c; 0x971d0; 0x96650];
[0xbd0e4; 0x971d0; 0x96650];
[0xbd0e4; 0xbcd9c; 0x971d0; 0x96650]].

Record rt_sig : Type := mkRTS {
rts : Type;
ART : rts -> mem -> Prop;
ARTM : rts -> Model -> Prop;
rt_live : rts -> list (Z * Z);
rt_frames : rts -> list (Z * nat);
rt_allow : rts -> list (Z * Z);
rt_sp0 : rts -> Z;

rt_credit : rts -> Z;
rt_pois : rts -> list (Z * Z)
}.

Definition fdfs_only (PMc : Model -> Prop) : Prop :=
forall mo mo', m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> PMc mo -> PMc mo'.

Definition ASTA (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (Pm : machine_state -> Prop) : config -> Prop :=
AST SEGTOP_A (rt_allow RT Σ) Pm (fun mo => ARTM RT Σ mo /\ PMc mo).

Definition CLIENT_STATIC : list (Z * Z) :=
[(0x100750, 0x102458); (0x628110, 0x638110); (0x638110, 0x65a578)].

Definition RT_STATIC : list (Z * Z) :=
[(0x638c40, 0x638c48); (0x638c90, 0x638cb0); (0x638cb8, 0x638cc8); (0x658f58, 0x658f60); (0x65a040, 0x65a048)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) l /\ lo <= a < hi.
Definition client_static (a : Z) : Prop := in_ranges CLIENT_STATIC a /\ ~ in_ranges RT_STATIC a.

Definition in_live (live : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) live /\ p <= a < p + n.

Definition in_fframe (frames : list (Z * nat)) (a : Z) : Prop :=
exists f k, In (f, k) frames /\ f <= a < f + fs_size k - 8.

Definition in_fframe_shadow (frames : list (Z * nat)) (a : Z) : Prop :=
exists f k, In (f, k) frames /\ shad f <= a < shad (f + fs_size k).

Definition aclient (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (a : Z) : Prop :=
(sp <= a < USTACK_TOP) \/ client_static a \/ in_live live a \/ in_fframe frames a \/ in_fframe_shadow frames a.

Definition alloca_rr (addr size : Z) : Z := (addr + size + 31) / 32 * 32 + 32.
Definition pz_lo (e : Z * Z) : Z := fst e - 32.
Definition pz_hi (e : Z * Z) : Z := alloca_rr (fst e) (snd e).
Definition in_pois (P : list (Z * Z)) (a : Z) : Prop := exists e, In e P /\ pz_lo e <= a < pz_hi e.

Definition pois_above (P : list (Z * Z)) (s : Z) : Prop := forall e, In e P -> s <= pz_lo e.

Definition pois_apart (P : list (Z * Z)) (a n : Z) : Prop := forall e, In e P -> a + n <= pz_lo e \/ pz_hi e <= a.

Lemma pois_above_nil : forall s, pois_above [] s.
Proof. intros s e []. Qed.
Lemma pois_apart_nil : forall a n, pois_apart [] a n.
Proof. intros a n e []. Qed.
Lemma pois_above_le : forall P s s', pois_above P s -> s' <= s -> pois_above P s'.
Proof. intros P s s' H Hs e He. specialize (H e He). lia. Qed.
Lemma pois_apart_above : forall P s a n, pois_above P s -> a + n <= s -> pois_apart P a n.
Proof. intros P s a n H Hs e He. left. specialize (H e He). lia. Qed.
Lemma alloca_rr_bounds : forall a n, a + n < alloca_rr a n <= a + n + 63 /\ alloca_rr a n mod 32 = 0.
Proof.
intros a n. unfold alloca_rr. pose proof (Z.div_mod (a + n + 31) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (a + n + 31) 32 ltac:(lia)) as B.
split; [lia|]. replace ((a + n + 31) / 32 * 32 + 32) with (((a + n + 31) / 32 + 1) * 32) by ring. apply Z.mod_mul. lia.
Qed.
Lemma pois_above_cons : forall P s a n, pois_above P (alloca_rr a n) -> s <= a - 32 -> 0 <= n -> pois_above ((a, n) :: P) s.
Proof.
intros P s a n H Hs Hn e [<-|He]; [exact Hs|]. specialize (H e He). pose proof (alloca_rr_bounds a n). lia.
Qed.

Definition pois_drop (bottom : Z) (P : list (Z * Z)) : list (Z * Z) := List.filter (fun e => bottom <=? pz_lo e) P.
Lemma pois_drop_above : forall b P, pois_above P b -> pois_drop b P = P.
Proof.
intros b P H. unfold pois_drop. induction P as [|e P IH]; [reflexivity|]. cbn [List.filter].
replace (b <=? pz_lo e) with true by (symmetry; apply Z.leb_le; apply H; left; reflexivity). f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.
Lemma pois_drop_cons_below : forall b e P, pz_lo e < b -> pois_drop b (e :: P) = pois_drop b P.
Proof. intros b e P H. unfold pois_drop. cbn [List.filter]. replace (b <=? pz_lo e) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

Definition rt_pres (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> m' a = m a.

Definition rt_pres_ex (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (d n : Z) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> ~ (d <= bv_unsigned a < d + n) -> m' a = m a.

Definition rng_class (RT : rt_sig) (Σ : rts RT) (s n : Z) : Prop :=
(exists p k, In (p, k) (rt_live RT Σ) /\ p <= s /\ s + n <= p + k)
\/ (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= s /\ s + n <= f + fs_size k - 8)
\/ (rt_sp0 RT Σ - STACK_WIN + 64 <= s /\ s + n <= USTACK_TOP - 16)
\/ (0x10000 <= s /\ s + n <= SEGTOP_A).

Definition call_ok (RT : rt_sig) (Σ : rts RT) (m : mem) (sp : word) (lo : Z) : Prop :=
stk bsegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
/\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0.

Definition unwind_ok (ra s0 sp : word) : Prop :=
In (bv_unsigned ra) ALLOC_RAS
/\ (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0).

Definition unwind_ch (m : mem) (ra s0 sp : word) : Prop :=
exists ras, In (bv_unsigned ra :: ras) SITE_TRACES /\ uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.

Lemma unwind_ok_ch : forall (m : mem) ra s0 sp, unwind_ok ra s0 sp -> unwind_ch m ra s0 sp.
Proof.
intros m ra s0 sp (H1 & H2). exists []. split.
- unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists (bv_unsigned ra). split; [reflexivity | exact H1].
- cbn [uw_chain]. unfold fp_stop. destruct H2 as [H2|[H2|H2]]; [left; lia | right; left; exact H2 | right; right; exact H2].
Qed.

Definition entry_st (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : mem) : machine_state :=
MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs).

Definition ret_stF (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom bsegs).
Lemma ret_stF_w : forall F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms,
ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms -> ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms.
Proof.
intros F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc. reflexivity.
Qed.

Definition ret_stR (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom bsegs) /\ (X1cn.frm0 fc -> X1cn.frm0 fc').

Lemma cps_post : forall (P Q Q' : config -> Prop), cps bsegs P Q -> (forall c, Q c -> Q' c) -> cps bsegs P Q'.
Proof. intros P Q Q' H HQ. eapply cps_conseq; [exact H | intros c Hc; exact Hc | exact HQ]. Qed.

Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
ART RT Σ' m' /\ mem_inv bsegs m' /\ wmono bsegs m m' /\ stk bsegs m' lo sp.

Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
ART RT Σ' m' /\ mem_inv bsegs m' /\ stk bsegs m' lo sp.

Lemma rt_after_f_of : forall RT Σ' sp lo m m', rt_after RT Σ' sp lo m m' -> rt_after_f RT Σ' sp lo m m'.
Proof. intros RT Σ' sp lo m m' (H1 & H2 & _ & H4). exact (conj H1 (conj H2 H4)). Qed.

Definition icpt_post (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

Definition icpt_postF (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
ASTA RT Σ PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

Lemma icpt_postF_w : forall RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c,
icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c ->
icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c.
Proof.
intros RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c H. unfold icpt_postF, icpt_post, ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Section Contracts.
Variable RT : rt_sig.

Definition malloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at bsegs m' p n /\ acc bsegs m' p n) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at bsegs m' p n /\ acc bsegs m' p n) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ.

Lemma malloc_postF_w : forall Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c,
malloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c -> malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c (Σ' & y & H & R). exists Σ', y. split; [|tauto]. unfold ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Definition malloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Definition malloc_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Lemma malloc_contract_ok_of : malloc_contract -> malloc_contract_ok.
Proof.
intros H. unfold malloc_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 Hc0. eapply malloc_postF_w. exact Hc0.
Qed.

Definition live_remove (p : Z) (live : list (Z * Z)) : list (Z * Z) := filter (fun e => negb (fst e =? p)) live.

Definition free_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
/\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ.

Definition free_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
/\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ.

Lemma free_postF_w : forall Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c,
free_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c -> free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c (Σ' & y & H & R). exists Σ', y. split; [|tauto]. unfold ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Definition free_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x638c98 ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Definition free_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x638c98 ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Lemma free_contract_ok_of : free_contract -> free_contract_ok.
Proof.
intros H. unfold free_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 Hc0. eapply free_postF_w. exact Hc0.
Qed.

Definition free_null_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x638c98 ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(fun c => exists v, icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition free_null_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x638c98 ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Lemma free_null_contract_ok_of : free_null_contract -> free_null_contract_ok.
Proof.
intros H. unfold free_null_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 (v & Hc0). exists v. eapply icpt_postF_w. exact Hc0.
Qed.

Definition calloc_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at bsegs m' p n /\ acc bsegs m' p n /\ bytes_at bsegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ.

Definition calloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (k sz lo : Z),
fdfs_only PMc -> mat_stable PMc ->
0 <= k < 2^64 -> 0 <= sz < 2^64 -> 1 <= k * sz <= 64512 ->
a0 = Z_to_bv 64 k -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 0x638c98 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (k * sz) <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_calloc m)))
(calloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (k * sz) lo m).

Definition realloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n0 n lo : Z) (bs : list byte),
fdfs_only PMc -> mat_stable PMc ->
In (p, n0) (rt_live RT Σ) -> 1 <= n <= 64512 -> n0 <= 64512 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x638c98 ->
bytes_at bsegs m p bs -> Z.of_nat (length bs) = n0 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp -> unwind_ch m ra s0 sp ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_realloc m)))
(fun c => exists (Σ' : rts RT) (q : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at bsegs m' q n /\ acc bsegs m' q n
/\ bytes_at bsegs m' q (firstn (Z.to_nat (Z.min n0 n)) bs)) c
/\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q <> p /\ q + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
(0 < n -> acc bsegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).

Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
(0 < n -> acc bsegs m d n /\ rng_class RT Σ d n)
/\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at bsegs m d n.

Definition memcpy_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
(d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at bsegs m' d bs)).

Definition memcpy_icontract_w (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
(d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at bsegs m' d bs)).

Lemma memcpy_icontract_w_of : forall entry, memcpy_icontract entry -> memcpy_icontract_w entry.
Proof.
intros entry H. unfold memcpy_icontract_w. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply icpt_postF_w. exact Hc0.
Qed.

Definition memset_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
(fun m' => bytes_at bsegs m' d (repeat c (Z.to_nat n)))).

Definition memchr_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at bsegs m s buf -> memchr_ok s cz n buf ->
(s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s)   ->
checked_src Σ m sp lo s (memchr_chk cz n buf) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_memchr m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
(fun _ => True)).

Definition strlen_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
bytes_at bsegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_strlen m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
(fun _ => True)).

Definition strnlen_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at bsegs m s buf -> strnlen_ok s n buf ->
(s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s)   ->
checked_src Σ m sp lo s (strnlen_chk n buf) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_strnlen m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
(fun _ => True)).

Definition memmove_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at bsegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at bsegs m' d bs)).

Definition bcmp_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
length b1 = length b2 -> 0 < Z.of_nat (length b1) < 2^31 -> 0 < p1 <= 2^47 -> 0 < p2 <= 2^47 ->
bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 ->
checked_src Σ m sp lo p1 (Z.of_nat (length b1)) -> checked_src Σ m sp lo p2 (Z.of_nat (length b1)) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_bcmp m)))
(fun c => exists v : word, (bv_unsigned v = 0 <-> b1 = b2)
/\ icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition stack_malloc_contract (k : nat) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo size : Z),
fdfs_only PMc -> mat_stable PMc -> In k FS_CLASSES -> tp = Z_to_bv 64 0x638c98 ->
(k = 8%nat -> a0 = Z_to_bv 64 size /\ size mod 8 = 0 /\ 0 < size <= fs_size 8)   ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
(fun c => exists (Σ' : rts RT) (f : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at bsegs m' f (fs_size k - 8) /\ wr_at bsegs m' (shad f) (fs_size k / 8)) c
/\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition stack_free_contract (k : nat) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo size : Z),
fdfs_only PMc -> mat_stable PMc -> (k = 5 \/ k = 6 \/ k = 8)%nat -> a0 = Z_to_bv 64 f -> rt_frames RT Σ = (f, k) :: fr ->
(k = 8%nat -> a1 = Z_to_bv 64 size /\ size mod 8 = 0 /\ 0 < size <= fs_size 8)   ->
(fr = [] -> rt_pois RT Σ = [])   ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_stack_free k) m)))
(fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m') c
/\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Definition set_shadow_contract (v : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d n : Z) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at bsegs m d n ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_set_shadow v) m)))
(fun c => exists v0, icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
(fun m' => bytes_at bsegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

Definition alloca_poison_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (addr size lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
addr mod 32 = 0 -> 0 <= size < 2^40 -> bv_unsigned sp <= addr - 32 -> alloca_rr addr size <= USTACK_TOP - 16 ->
pois_above (rt_pois RT Σ) (alloca_rr addr size) -> rt_frames RT Σ <> [] ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_alloca_poison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ acc bsegs m' addr size
/\ (forall o n, acc bsegs m o n -> o + n <= USTACK_TOP -> o + n <= addr - 32 \/ alloca_rr addr size <= o -> acc bsegs m' o n)) c
/\ rt_pois RT Σ' = (addr, size) :: rt_pois RT Σ
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Definition allocas_unpoison_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (top bottom lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom ->
0 < top <= bottom -> top mod 8 = 0 -> bottom mod 8 = 0 -> bv_unsigned sp <= top -> bottom <= USTACK_TOP - 16 ->
(forall e, In e (rt_pois RT Σ) -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ (forall o n, acc bsegs m o n -> o + n <= USTACK_TOP -> o + n <= top \/ bottom <= o -> acc bsegs m' o n)) c
/\ rt_pois RT Σ' = pois_drop bottom (rt_pois RT Σ)
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Definition allocas_unpoison_nop_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> (a0 = Z_to_bv 64 0 \/ bv_unsigned a1 < bv_unsigned a0) -> mem_inv bsegs m ->
cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(ASTA RT Σ PMc (fun ms => exists v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m ms)).

Definition client_consts (m : mem) : Prop :=
ro_cells bsegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
/\ ro_cells bsegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
/\ ro_cells bsegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
/\ ro_cells bsegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].

Definition ACC_LITS : list (Z * Z) :=
[(0x232a0, 24); (0x232e0, 6); (0x23360, 39); (0x233c0, 48); (0x23420, 51); (0x23480, 30); (0x234c0, 43); (0x23520, 37);
(0x23580, 18); (0x235c0, 13); (0x23600, 32); (0x23640, 16); (0x23760, 16); (0x237a0, 9); (0x237c0, 23); (0x23800, 39);
(0x23860, 18); (0x238c0, 11); (0x23a80, 25); (0x23ac0, 37); (0x23b20, 28); (0x23b60, 32); (0x23ba0, 4); (0x23bc0, 8);
(0x23be0, 44); (0x23c40, 40); (0x23ca0, 32); (0x23ce0, 51); (0x23d40, 62); (0x23da0, 39); (0x23e00, 46); (0x23e60, 16);
(0x23e80, 43); (0x23ee0, 18); (0x23f20, 44); (0x23f80, 800); (0x24380, 396); (0x24580, 220); (0x24680, 88); (0x24720, 60);
(0x24780, 60); (0x247e0, 84); (0x24880, 640); (0x24ba0, 320); (0x24d20, 320); (0x24ea0, 320); (0x25020, 320); (0x251c0, 512);
(0x25440, 512); (0x256e0, 128); (0x257a0, 160); (0x25880, 320); (0x25a20, 1024); (0x25f40, 512); (0x261e0, 320); (0x26380, 1280);
(0x269e0, 640); (0x26d20, 25); (0x26d60, 32); (0x26da0, 31); (0x26de0, 16); (0x26fc0, 25); (0x27000, 256); (0x27140, 128);
(0x271e0, 64); (0x27240, 51); (0x272a0, 16); (0x272c0, 18); (0x27320, 320); (0x274c0, 1024); (0xf8380, 208); (0xf8480, 96);
(0xf8500, 88); (0xf8580, 88); (0xf8600, 88); (0xf8680, 88); (0xf8700, 88); (0xf8780, 88); (0xf8800, 88); (0xf8880, 88);
(0xf8900, 16); (0xf8920, 24); (0xf8960, 16); (0xf8980, 24); (0xf89c0, 16); (0xf89e0, 24); (0xf8a20, 16); (0xf8a40, 24);
(0xf8a80, 24); (0xf8ac0, 24); (0xf8b00, 96); (0xf8b80, 96); (0xf8c00, 24); (0xf8c40, 88); (0xf8cc0, 88); (0xf8d40, 88);
(0xf8dc0, 88); (0xf8e40, 216); (0xf8f40, 24); (0xf8f80, 24); (0xf8fc0, 216)].

Record art_facts : Prop := mkAF {
af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;

af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
(forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
wmono bsegs m m' -> ART RT Σ m';

af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);

af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at bsegs m p n /\ acc bsegs m p n;

af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
exists slack, bytes_at bsegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
/\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;

af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP ->
pois_apart (rt_pois RT Σ) a n   -> acc bsegs m a n;

af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
(forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x100ab0 <= a + i < 0x1023f0)) -> acc bsegs m a n;

af_live_range : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p);
af_live_disj : forall Σ m p1 n1 p2 n2 l1 l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) ->
p1 + n1 <= p2 \/ p2 + n2 <= p1;
af_frames_range : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
0 < f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
/\ forall p n, In (p, n) (rt_live RT Σ) -> f + fs_size k <= p \/ p + n <= f;
af_sp0_range : forall Σ m, ART RT Σ m -> SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ <= USTACK_TOP;

af_sp0_win : forall Σ m, ART RT Σ m -> 0x7fff80000000 <= rt_sp0 RT Σ;

af_frame_release : forall Σ (m : mem) f k fr, ART RT Σ m -> rt_frames RT Σ = (f, k) :: fr ->
(fr = [] -> rt_pois RT Σ = [])   ->
exists (Σ' : rts RT) (fl : Z), rw_cells bsegs m fl [C1 (Z_to_bv 8 1)]
/\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl

/\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN

/\ ro_cells bsegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
/\ forall m', munch [(fl, fl + 1)] m m' -> wmono bsegs m m' -> rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)] ->
ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo)
/\ rt_pois RT Σ' = rt_pois RT Σ;

af_frames_align : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f;
af_frames_disj : forall Σ m f1 k1 f2 k2 l1 l2, ART RT Σ m -> rt_frames RT Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1;
af_fshadow_apart : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
(forall p n, In (p, n) (rt_live RT Σ) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
/\ (forall f' k', In (f', k') (rt_frames RT Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f');

af_got_lib : forall Σ m, ART RT Σ m ->
ro_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)] /\ ro_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)];

af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc bsegs m (fst r) (snd r)) ACC_LITS;

af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;

af_live_offshadow : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;

af_credit_nonneg : forall Σ m, ART RT Σ m -> 0 <= rt_credit RT Σ;

af_acc_pois : forall Σ m a n, ART RT Σ m -> In (a, n) (rt_pois RT Σ) -> acc bsegs m a n;

af_pois_nil : forall Σ m, ART RT Σ m -> rt_frames RT Σ = [] -> rt_pois RT Σ = [];

af_pois_range : forall Σ m a n, ART RT Σ m -> In (a, n) (rt_pois RT Σ) ->
a mod 32 = 0 /\ 0 <= n /\ rt_sp0 RT Σ - STACK_WIN + 64 <= a - 32 /\ alloca_rr a n <= USTACK_TOP - 16;

af_live_small : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p
}.

Record rt_contracts : Prop := mkRTC {
rc_malloc : malloc_contract;
rc_free : free_contract;
rc_free_null : free_null_contract;
rc_calloc : calloc_contract;
rc_memcpy : memcpy_icontract e_memcpy;
rc_asan_memcpy : memcpy_icontract e_asan_memcpy;
rc_memset : memset_icontract e_memset;
rc_asan_memset : memset_icontract e_asan_memset;
rc_memchr : memchr_icontract;
rc_strlen : strlen_icontract;
rc_strnlen : strnlen_icontract;
rc_stack_malloc_0 : stack_malloc_contract 0;
rc_stack_malloc_2 : stack_malloc_contract 2;
rc_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract v;
rc_facts : art_facts
}.

Record rt_contracts_x : Prop := mkRTX {
rx_realloc : realloc_contract;
rx_stack_malloc_5 : stack_malloc_contract 5;
rx_stack_malloc_8 : stack_malloc_contract 8;
rx_stack_free : forall k, (k = 5 \/ k = 6 \/ k = 8)%nat -> stack_free_contract k;
rx_asan_memmove : memmove_icontract e_asan_memmove;
rx_memmove : memmove_icontract e_memmove;
rx_bcmp : bcmp_icontract;
rx_alloca_poison : alloca_poison_contract;
rx_allocas_unpoison : allocas_unpoison_contract;
rx_allocas_unpoison_nop : allocas_unpoison_nop_contract
}.

Lemma pois_release_ok : art_facts -> forall Σ0 m0 Σ fr, ART RT Σ0 m0 -> rt_frames RT Σ0 = fr -> rt_pois RT Σ = rt_pois RT Σ0 -> (fr = [] -> rt_pois RT Σ = []).
Proof. intros AF Σ0 m0 Σ fr HA HF HP E. rewrite HP. apply (af_pois_nil AF Σ0 m0 HA). rewrite HF. exact E. Qed.

End Contracts.

Ltac frames_nil_tac :=
first [ assumption
| match goal with E : rt_frames ?RT ?S' = rt_frames ?RT ?S |- rt_frames ?RT ?S' = [] => rewrite E; frames_nil_tac end
| match goal with H : _ /\ rt_frames ?RT ?S = [] /\ _ |- rt_frames ?RT ?S = [] => exact (proj1 (proj2 H)) end
| match goal with H : ?P |- rt_frames ?RT ?S = [] =>
let P' := eval hnf in P in lazymatch P' with _ /\ rt_frames RT S = [] /\ _ => exact (proj1 (proj2 H)) end end ].
Ltac pois_nil_tac AF :=
match goal with
| HA : ART ?RT ?S ?m |- pois_above (rt_pois ?RT ?S) _ => rewrite (af_pois_nil RT AF S m HA ltac:(frames_nil_tac)); apply pois_above_nil
| HA : ART ?RT ?S ?m |- pois_apart (rt_pois ?RT ?S) _ _ => rewrite (af_pois_nil RT AF S m HA ltac:(frames_nil_tac)); apply pois_apart_nil
end.

Definition PMfd (F0 : list (word * FdEntry)) (fs0 : Fs) : Model -> Prop := fun mo => m_fds mo = F0 /\ m_fs mo = fs0.

Lemma PMfd_fdfs_only : forall F0 fs0, fdfs_only (PMfd F0 fs0).
Proof. intros F0 fs0 mo mo' E1 E2 [H1 H2]. split; congruence. Qed.

Definition rt_pres_fp (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> outside W (bv_unsigned a) -> m' a = m a.

Definition errno_cell (tp : word) : Z := bv_unsigned tp - 164.

Definition FMT_usage : Z := 0x165d7.
Definition FMT_cannot_open : Z := 0x1f32d.
Definition FMT_read_error : Z := 0x1f342.
Definition FMT_too_big : Z := 0x1ac77.
Definition FMT_emit : Z := 0x1529e.

Definition STDERR_FILE : Z := 0x1007b0.

Inductive fp_case : Type :=
| FPusage (argv0 : Z) (s : list byte)
| FPcannot_open (path : Z) (s : list byte)
| FPread_error (path : Z) (s : list byte)
| FPtoo_big.

Definition fp_fmt (c : fp_case) : Z :=
match c with FPusage _ _ => FMT_usage | FPcannot_open _ _ => FMT_cannot_open
| FPread_error _ _ => FMT_read_error | FPtoo_big => FMT_too_big end.
Definition fp_arg (c : fp_case) : Z :=
match c with FPusage a _ | FPcannot_open a _ | FPread_error a _ => a | FPtoo_big => 67108864 end.

Definition fp_str (c : fp_case) : option (Z * list byte) :=
match c with FPusage a s | FPcannot_open a s | FPread_error a s => Some (a, s) | FPtoo_big => None end.

Definition fp_msg (c : fp_case) : list Z :=
match c with
| FPusage _ s => msg_usage (map bv_unsigned s)
| FPcannot_open _ s => msg_cannot_open (map bv_unsigned s)
| FPread_error _ s => msg_read_error (map bv_unsigned s)
| FPtoo_big => msg_too_big
end.

Definition so_lines (k : nat) : stdout_st := mkStdout true (zeros_out k) false false.

Definition io_ssp (m : mem) : Prop :=
exists g : word, ro_cells bsegs m 0xfce58 [C8 (Z_to_bv 64 0x658cd8)] /\ ro_cells bsegs m 0x658cd8 [C8 g].

Section IO.
Variable RT : rt_sig.

Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.

Variable IO_FP : list (Z * Z).

Definition read_icontract_file : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage   ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
let bs := file_read data off (Z_to_bv 64 count) in
cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
(fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
/\ bytes_at bsegs m' buf bs)).

Definition read_icontract_dir : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage   ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
(forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
tp = Z_to_bv 64 0x638c98 -> (exists v, rw_cells bsegs m (errno_cell tp) [C4 v]) ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cps bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(errno_cell tp, errno_cell tp + 4)] m m')).

Definition fprintf_stderr_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (c : fp_case) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 (fp_fmt c) -> a2 = Z_to_bv 64 (fp_arg c) ->
errp = STDERR_FILE ->
(forall a s, fp_str c = Some (a, s) -> bytes_at bsegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)

/\ bv_unsigned sp <= a
/\ exists slack, bytes_at bsegs m (a + Z.of_nat (length s) + 1) slack
/\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
/\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
(evw 2 (fp_msg c))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Definition fwrite_stderr_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (sa : Z) (s : list byte) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 errp ->
errp = STDERR_FILE -> 0 < Z.of_nat (length s) <= 64 ->
(sa = 0x219c8 \/ sa = 0x165e8)   ->
bytes_at bsegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
(evw 2 (map bv_unsigned s))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Definition emit0_out (so : stdout_st) : list Z := if so_first so then [48; 10] else [].
Definition emit0_next (so : stdout_st) : stdout_st :=
if so_first so then so_lines 0 else mkStdout true (so_buf so ++ [48; 10]) false false.

Definition vprintf_emit0_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
rw_cells bsegs m ap [C8 (Z_to_bv 64 0)]   ->
ap = bv_unsigned sp + 24   ->
(so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
OUT_rep so m -> io_ssp m ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
(evw 1 (emit0_out so))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).

Inductive fpl_kind : Type := FLnotify | FLwarn | FLwarn_int.
Definition fpl_fmts (k : fpl_kind) : list Z :=
match k with
| FLnotify => [0x23580; 0x23860; 0x23ee0; 0x272c0]
| FLwarn => [0x235c0]
| FLwarn_int => [0x23640; 0x23e60; 0x26de0; 0x272a0]
end.
Definition FPL_NOTIFY : list Z := [110; 111; 116; 105; 102; 105; 99; 97; 116; 105; 111; 110; 58; 32].
Definition FPL_WARN : list Z := [119; 97; 114; 110; 105; 110; 103; 58; 32].
Definition fpl_int (v : Z) : list Z :=
if v =? 0 then [48] else if v <? 0 then 45 :: X1ry.dec_digits (- v) else X1ry.dec_digits v.
Definition fpl_msg (k : fpl_kind) (str : list byte) (v : Z) : list Z :=
match k with
| FLnotify => FPL_NOTIFY ++ map bv_unsigned str ++ [10]
| FLwarn => FPL_WARN ++ map bv_unsigned str ++ [10]
| FLwarn_int => FPL_WARN ++ map bv_unsigned str ++ [32] ++ fpl_int v ++ [10]
end.

Definition fprintf_lib_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (k : fpl_kind) (fmt sa v : Z) (str : list byte) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 fmt -> a2 = Z_to_bv 64 sa -> (k = FLwarn_int -> a3 = Z_to_bv 64 v /\ - 2^31 <= v < 2^31) ->
errp = STDERR_FILE -> In fmt (fpl_fmts k) ->
(exists n, In (sa, n) ACC_LITS /\ Z.of_nat (length str) + 1 <= n) -> bytes_at bsegs m sa (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE bsegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
(evw 2 (fpl_msg k str v))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists r m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Record io_contracts : Prop := mkIOC {
ioc_read_file : read_icontract_file;
ioc_read_dir : read_icontract_dir;
ioc_fprintf : fprintf_stderr_icontract;
ioc_fwrite : fwrite_stderr_icontract;
ioc_vprintf : vprintf_emit0_icontract
}.

Record io_contracts_x : Prop := mkIOX {
iox_fprintf_lib : fprintf_lib_icontract
}.

End IO.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

Definition SEGTOP_A : Z := 0x652000.

Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.

Definition RT_STACK : Z := 0x10000.

Definition LIVE_MAX : Z := 64.
Definition FRAMES_MAX : nat := 16.

Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

Definition e_malloc : Z := 0x67e98.
Definition e_free : Z := 0x67e94.
Definition e_calloc : Z := 0x67e9c.
Definition e_realloc : Z := 0x67ea0.
Definition e_strlen : Z := 0x56be0.
Definition e_strnlen : Z := 0x56be4.
Definition e_memchr : Z := 0x56bf8.
Definition e_memset : Z := 0x66308.
Definition e_memcpy : Z := 0x66310.
Definition e_memmove : Z := 0x6630c.
Definition e_bcmp : Z := 0x56bf4.
Definition e_asan_memmove : Z := 0x669f0.
Definition e_asan_memcpy : Z := 0x66314.
Definition e_asan_memset : Z := 0x667b0.
Definition e_read : Z := 0x56c00.
Definition e_fwrite : Z := 0x56c04.
Definition e_vprintf : Z := 0x56c10.
Definition e_vfprintf : Z := 0x56c14.
Definition e_fprintf : Z := 0x56c1c.

Definition FS_CLASSES : list nat := [0; 2; 5; 8]%nat.
Definition e_stack_malloc (k : nat) : Z :=
match k with 0%nat => 0x51228 | 1%nat => 0x5139c | 2%nat => 0x5152c | 5%nat => 0x516c8 | 6%nat => 0x51988 | _ => 0x51b6c end.

Definition e_stack_free (k : nat) : Z := match k with 5%nat => 0x518d4 | 6%nat => 0x51b24 | _ => 0x51ce8 end.

Definition e_alloca_poison : Z := 0x51d38.
Definition e_allocas_unpoison : Z := 0x51e64.

Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
match v with
| 0 => 0x6a0c0 | 1 => 0x6a0d8 | 2 => 0x6a0f0 | 3 => 0x6a108 | 4 => 0x6a120 | 5 => 0x6a138 | 6 => 0x6a150
| 7 => 0x6a168 | 241 => 0x6a180 | 242 => 0x6a198 | 243 => 0x6a1b0 | 245 => 0x6a1c8 | _ => 0x6a1e0
end.

Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

Definition ALLOC_RAS : list Z :=

[0x9621c; 0x96270; 0x96294; 0x963c4; 0x964fc; 0x96590; 0x97424; 0x9742c; 0x974ec; 0x97880;
0x995b4; 0xb599c; 0xb59b8; 0xb59d4; 0xb59f0; 0xb5a0c; 0xb5a28; 0xb5a44; 0xb5a60; 0xb5a7c;
0xb8afc; 0xb8b0c; 0xb8b1c; 0xb8b84; 0xb8b90; 0xb8b9c; 0xb8e20; 0xb8ecc; 0xb8ee4; 0xb8f5c;
0xb9004; 0xb9034; 0xb9044].

Definition SITE_TRACES : list (list Z) :=
map (fun r => [r]) ALLOC_RAS ++
[[0x97068; 0x96564];
[0x971bc; 0x96564];
[0x971c8; 0x96564];
[0x971ec; 0x96564];
[0x994c4; 0x96564];
[0x9e854; 0x96564];
[0x9e854; 0x96f2c; 0x96564];
[0x9e854; 0xb530c; 0x96f2c; 0x96564];
[0xb52a8; 0x96f2c; 0x96564];
[0xb52a8; 0xb530c; 0x96f2c; 0x96564];
[0xb54dc; 0x96f2c; 0x96564];
[0xb54dc; 0xb530c; 0x96f2c; 0x96564];
[0xb5500; 0x96f2c; 0x96564];
[0xb5500; 0xb530c; 0x96f2c; 0x96564];
[0xb5530; 0x96f2c; 0x96564];
[0xb5530; 0xb530c; 0x96f2c; 0x96564];
[0xb5564; 0x96f2c; 0x96564];
[0xb5564; 0xb530c; 0x96f2c; 0x96564];
[0xb5594; 0x96f2c; 0x96564];
[0xb5594; 0xb530c; 0x96f2c; 0x96564];
[0xb55c4; 0x96f2c; 0x96564];
[0xb55c4; 0xb530c; 0x96f2c; 0x96564];
[0xb55f4; 0x96f2c; 0x96564];
[0xb55f4; 0xb530c; 0x96f2c; 0x96564];
[0xb5624; 0x96f2c; 0x96564];
[0xb5624; 0xb530c; 0x96f2c; 0x96564]].

Record rt_sig : Type := mkRTS {
rts : Type;
ART : rts -> mem -> Prop;
ARTM : rts -> Model -> Prop;
rt_live : rts -> list (Z * Z);
rt_frames : rts -> list (Z * nat);
rt_allow : rts -> list (Z * Z);
rt_sp0 : rts -> Z;

rt_credit : rts -> Z;
rt_pois : rts -> list (Z * Z)
}.

Definition fdfs_only (PMc : Model -> Prop) : Prop :=
forall mo mo', m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> PMc mo -> PMc mo'.

Definition ASTA (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (Pm : machine_state -> Prop) : config -> Prop :=
AST SEGTOP_A (rt_allow RT Σ) Pm (fun mo => ARTM RT Σ mo /\ PMc mo).

Definition CLIENT_STATIC : list (Z * Z) :=
[(0xf7ed0, 0xf9c18); (0x61f8d0, 0x62f8d0); (0x62f8d0, 0x651d38)].

Definition RT_STATIC : list (Z * Z) :=
[(0x630400, 0x630408); (0x630450, 0x630470); (0x630478, 0x630488); (0x650718, 0x650720); (0x651800, 0x651808)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) l /\ lo <= a < hi.
Definition client_static (a : Z) : Prop := in_ranges CLIENT_STATIC a /\ ~ in_ranges RT_STATIC a.

Definition in_live (live : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) live /\ p <= a < p + n.

Definition in_fframe (frames : list (Z * nat)) (a : Z) : Prop :=
exists f k, In (f, k) frames /\ f <= a < f + fs_size k - 8.

Definition in_fframe_shadow (frames : list (Z * nat)) (a : Z) : Prop :=
exists f k, In (f, k) frames /\ shad f <= a < shad (f + fs_size k).

Definition aclient (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (a : Z) : Prop :=
(sp <= a < USTACK_TOP) \/ client_static a \/ in_live live a \/ in_fframe frames a \/ in_fframe_shadow frames a.

Definition alloca_rr (addr size : Z) : Z := (addr + size + 31) / 32 * 32 + 32.
Definition pz_lo (e : Z * Z) : Z := fst e - 32.
Definition pz_hi (e : Z * Z) : Z := alloca_rr (fst e) (snd e).
Definition in_pois (P : list (Z * Z)) (a : Z) : Prop := exists e, In e P /\ pz_lo e <= a < pz_hi e.

Definition pois_above (P : list (Z * Z)) (s : Z) : Prop := forall e, In e P -> s <= pz_lo e.

Definition pois_apart (P : list (Z * Z)) (a n : Z) : Prop := forall e, In e P -> a + n <= pz_lo e \/ pz_hi e <= a.

Lemma pois_above_nil : forall s, pois_above [] s.
Proof. intros s e []. Qed.
Lemma pois_apart_nil : forall a n, pois_apart [] a n.
Proof. intros a n e []. Qed.
Lemma pois_above_le : forall P s s', pois_above P s -> s' <= s -> pois_above P s'.
Proof. intros P s s' H Hs e He. specialize (H e He). lia. Qed.
Lemma pois_apart_above : forall P s a n, pois_above P s -> a + n <= s -> pois_apart P a n.
Proof. intros P s a n H Hs e He. left. specialize (H e He). lia. Qed.
Lemma alloca_rr_bounds : forall a n, a + n < alloca_rr a n <= a + n + 63 /\ alloca_rr a n mod 32 = 0.
Proof.
intros a n. unfold alloca_rr. pose proof (Z.div_mod (a + n + 31) 32 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (a + n + 31) 32 ltac:(lia)) as B.
split; [lia|]. replace ((a + n + 31) / 32 * 32 + 32) with (((a + n + 31) / 32 + 1) * 32) by ring. apply Z.mod_mul. lia.
Qed.
Lemma pois_above_cons : forall P s a n, pois_above P (alloca_rr a n) -> s <= a - 32 -> 0 <= n -> pois_above ((a, n) :: P) s.
Proof.
intros P s a n H Hs Hn e [<-|He]; [exact Hs|]. specialize (H e He). pose proof (alloca_rr_bounds a n). lia.
Qed.

Definition pois_drop (bottom : Z) (P : list (Z * Z)) : list (Z * Z) := List.filter (fun e => bottom <=? pz_lo e) P.
Lemma pois_drop_above : forall b P, pois_above P b -> pois_drop b P = P.
Proof.
intros b P H. unfold pois_drop. induction P as [|e P IH]; [reflexivity|]. cbn [List.filter].
replace (b <=? pz_lo e) with true by (symmetry; apply Z.leb_le; apply H; left; reflexivity). f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.
Lemma pois_drop_cons_below : forall b e P, pz_lo e < b -> pois_drop b (e :: P) = pois_drop b P.
Proof. intros b e P H. unfold pois_drop. cbn [List.filter]. replace (b <=? pz_lo e) with false by (symmetry; apply Z.leb_gt; exact H). reflexivity. Qed.

Definition rt_pres (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> m' a = m a.

Definition rt_pres_ex (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (d n : Z) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> ~ (d <= bv_unsigned a < d + n) -> m' a = m a.

Definition rng_class (RT : rt_sig) (Σ : rts RT) (s n : Z) : Prop :=
(exists p k, In (p, k) (rt_live RT Σ) /\ p <= s /\ s + n <= p + k)
\/ (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= s /\ s + n <= f + fs_size k - 8)
\/ (rt_sp0 RT Σ - STACK_WIN + 64 <= s /\ s + n <= USTACK_TOP - 16)
\/ (0x10000 <= s /\ s + n <= SEGTOP_A).

Definition call_ok (RT : rt_sig) (Σ : rts RT) (m : mem) (sp : word) (lo : Z) : Prop :=
stk asegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
/\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0.

Definition unwind_ok (ra s0 sp : word) : Prop :=
In (bv_unsigned ra) ALLOC_RAS
/\ (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0).

Definition unwind_ch (m : mem) (ra s0 sp : word) : Prop :=
exists ras, In (bv_unsigned ra :: ras) SITE_TRACES /\ uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.

Lemma unwind_ok_ch : forall (m : mem) ra s0 sp, unwind_ok ra s0 sp -> unwind_ch m ra s0 sp.
Proof.
intros m ra s0 sp (H1 & H2). exists []. split.
- unfold SITE_TRACES. apply in_or_app. left. apply in_map_iff. exists (bv_unsigned ra). split; [reflexivity | exact H1].
- cbn [uw_chain]. unfold fp_stop. destruct H2 as [H2|[H2|H2]]; [left; lia | right; left; exact H2 | right; right; exact H2].
Qed.

Definition entry_st (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : mem) : machine_state :=
MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs).

Definition ret_stF (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom asegs).
Lemma ret_stF_w : forall F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms,
ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms -> ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms.
Proof.
intros F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & ->).
exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, F, fc. reflexivity.
Qed.

Definition ret_stR (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F' (ret_pc ra) fc' None m' (seg_rom asegs) /\ (X1cn.frm0 fc -> X1cn.frm0 fc').

Lemma cps_post : forall (P Q Q' : config -> Prop), cps asegs P Q -> (forall c, Q c -> Q' c) -> cps asegs P Q'.
Proof. intros P Q Q' H HQ. eapply cps_conseq; [exact H | intros c Hc; exact Hc | exact HQ]. Qed.

Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
ART RT Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo sp.

Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo sp.

Lemma rt_after_f_of : forall RT Σ' sp lo m m', rt_after RT Σ' sp lo m m' -> rt_after_f RT Σ' sp lo m m'.
Proof. intros RT Σ' sp lo m m' (H1 & H2 & _ & H4). exact (conj H1 (conj H2 H4)). Qed.

Definition icpt_post (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

Definition icpt_postF (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32)
(ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
ASTA RT Σ PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

Lemma icpt_postF_w : forall RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c,
icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c ->
icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c.
Proof.
intros RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo d n m Q c H. unfold icpt_postF, icpt_post, ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Section Contracts.
Variable RT : rt_sig.

Definition malloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at asegs m' p n /\ acc asegs m' p n) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at asegs m' p n /\ acc asegs m' p n) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ.

Lemma malloc_postF_w : forall Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c,
malloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c -> malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c (Σ' & y & H & R). exists Σ', y. split; [|tauto]. unfold ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Definition malloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Definition malloc_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_malloc m)))
(malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Lemma malloc_contract_ok_of : malloc_contract -> malloc_contract_ok.
Proof.
intros H. unfold malloc_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 Hc0. eapply malloc_postF_w. exact Hc0.
Qed.

Definition live_remove (p : Z) (live : list (Z * Z)) : list (Z * Z) := filter (fun e => negb (fst e =? p)) live.

Definition free_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
/\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ.

Definition free_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(p lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
/\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ.

Lemma free_postF_w : forall Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c,
free_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c -> free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c.
Proof.
intros Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x lo m c (Σ' & y & H & R). exists Σ', y. split; [|tauto]. unfold ASTA in *.
eapply AST_conseq; [exact H | | intros mo Hmo; exact Hmo]. intros ms (m' & RS & X). exists m'. split; [exact (ret_stF_w _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RS) | exact X].
Qed.

Definition free_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x630458 ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Definition free_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n lo : Z),
fdfs_only PMc -> mat_stable PMc ->
In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x630458 ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

Lemma free_contract_ok_of : free_contract -> free_contract_ok.
Proof.
intros H. unfold free_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 Hc0. eapply free_postF_w. exact Hc0.
Qed.

Definition free_null_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x630458 ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(fun c => exists v, icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition free_null_contract_ok : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x630458 ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_free m)))
(fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Lemma free_null_contract_ok_of : free_null_contract -> free_null_contract_ok.
Proof.
intros H. unfold free_null_contract_ok. intros. eapply cps_post; [eapply H; try eassumption; apply unwind_ok_ch; assumption |].
intros c0 (v & Hc0). exists v. eapply icpt_postF_w. exact Hc0.
Qed.

Definition calloc_postF (Σ : rts RT) (PMc : Model -> Prop) (F : bvmap 5 word) (fc : bv 32) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
(n lo : Z) (m : mem) : config -> Prop :=
fun c => exists (Σ' : rts RT) (p : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at asegs m' p n /\ acc asegs m' p n /\ bytes_at asegs m' p (repeat (Z_to_bv 8 0) (Z.to_nat n))) c
/\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ.

Definition calloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (k sz lo : Z),
fdfs_only PMc -> mat_stable PMc ->
0 <= k < 2^64 -> 0 <= sz < 2^64 -> 1 <= k * sz <= 64512 ->
a0 = Z_to_bv 64 k -> a1 = Z_to_bv 64 sz -> tp = Z_to_bv 64 0x630458 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (k * sz) <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_calloc m)))
(calloc_postF Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (k * sz) lo m).

Definition realloc_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p n0 n lo : Z) (bs : list byte),
fdfs_only PMc -> mat_stable PMc ->
In (p, n0) (rt_live RT Σ) -> 1 <= n <= 64512 -> n0 <= 64512 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x630458 ->
bytes_at asegs m p bs -> Z.of_nat (length bs) = n0 ->
Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 80 <= bv_unsigned sp -> unwind_ch m ra s0 sp ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_realloc m)))
(fun c => exists (Σ' : rts RT) (q : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 q) m' ms
/\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
/\ rt_pres (live_remove p (rt_live RT Σ)) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at asegs m' q n /\ acc asegs m' q n
/\ bytes_at asegs m' q (firstn (Z.to_nat (Z.min n0 n)) bs)) c
/\ rt_live RT Σ' = (q, n) :: live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < q /\ q mod 16 = 0 /\ q <> p /\ q + n < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
(0 < n -> acc asegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).

Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
(0 < n -> acc asegs m d n /\ rng_class RT Σ d n)
/\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at asegs m d n.

Definition memcpy_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
(d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at asegs m' d bs)).

Definition memcpy_icontract_w (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
(d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at asegs m' d bs)).

Lemma memcpy_icontract_w_of : forall entry, memcpy_icontract entry -> memcpy_icontract_w entry.
Proof.
intros entry H. unfold memcpy_icontract_w. intros. eapply cps_post; [eapply H; eassumption |].
intros c0 Hc0. eapply icpt_postF_w. exact Hc0.
Qed.

Definition memset_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
(fun m' => bytes_at asegs m' d (repeat c (Z.to_nat n)))).

Definition memchr_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> memchr_ok s cz n buf ->
(s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s)   ->
checked_src Σ m sp lo s (memchr_chk cz n buf) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_memchr m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
(fun _ => True)).

Definition strlen_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
(- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_strlen m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
(fun _ => True)).

Definition strnlen_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> strnlen_ok s n buf ->
(s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s)   ->
checked_src Σ m sp lo s (strnlen_chk n buf) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_strnlen m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
(fun _ => True)).

Definition memmove_icontract (entry : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc entry m)))
(icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
(fun m' => bytes_at asegs m' d bs)).

Definition bcmp_icontract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (p1 p2 : Z) (b1 b2 : list byte) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 (Z.of_nat (length b1)) ->
length b1 = length b2 -> 0 < Z.of_nat (length b1) < 2^31 -> 0 < p1 <= 2^47 -> 0 < p2 <= 2^47 ->
bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 ->
checked_src Σ m sp lo p1 (Z.of_nat (length b1)) -> checked_src Σ m sp lo p2 (Z.of_nat (length b1)) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_bcmp m)))
(fun c => exists v : word, (bv_unsigned v = 0 <-> b1 = b2)
/\ icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

Definition stack_malloc_contract (k : nat) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (lo size : Z),
fdfs_only PMc -> mat_stable PMc -> In k FS_CLASSES -> tp = Z_to_bv 64 0x630458 ->
(k = 8%nat -> a0 = Z_to_bv 64 size /\ size mod 8 = 0 /\ 0 < size <= fs_size 8)   ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
(fun c => exists (Σ' : rts RT) (f : Z),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
/\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP /\ rt_pois RT Σ' = rt_pois RT Σ).

Definition stack_free_contract (k : nat) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo size : Z),
fdfs_only PMc -> mat_stable PMc -> (k = 5 \/ k = 6 \/ k = 8)%nat -> a0 = Z_to_bv 64 f -> rt_frames RT Σ = (f, k) :: fr ->
(k = 8%nat -> a1 = Z_to_bv 64 size /\ size mod 8 = 0 /\ 0 < size <= fs_size 8)   ->
(fr = [] -> rt_pois RT Σ = [])   ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_stack_free k) m)))
(fun c => exists (Σ' : rts RT) (v : word),
ASTA RT Σ' PMc (fun ms => exists m', ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m') c
/\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ
/\ rt_pois RT Σ' = rt_pois RT Σ).

Definition set_shadow_contract (v : Z) : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (d n : Z) (lo : Z),
fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at asegs m d n ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc (e_set_shadow v) m)))
(fun c => exists v0, icpt_postF RT Σ PMc F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
(fun m' => bytes_at asegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

Definition alloca_poison_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (addr size lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 addr -> a1 = Z_to_bv 64 size ->
addr mod 32 = 0 -> 0 <= size < 2^40 -> bv_unsigned sp <= addr - 32 -> alloca_rr addr size <= USTACK_TOP - 16 ->
pois_above (rt_pois RT Σ) (alloca_rr addr size) -> rt_frames RT Σ <> [] ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_alloca_poison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ acc asegs m' addr size
/\ (forall o n, acc asegs m o n -> o + n <= USTACK_TOP -> o + n <= addr - 32 \/ alloca_rr addr size <= o -> acc asegs m' o n)) c
/\ rt_pois RT Σ' = (addr, size) :: rt_pois RT Σ
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Definition allocas_unpoison_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (top bottom lo : Z),
fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 top -> a1 = Z_to_bv 64 bottom ->
0 < top <= bottom -> top mod 8 = 0 -> bottom mod 8 = 0 -> bv_unsigned sp <= top -> bottom <= USTACK_TOP - 16 ->
(forall e, In e (rt_pois RT Σ) -> (top <= pz_lo e /\ pz_hi e <= bottom) \/ bottom <= pz_lo e) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms => exists m' v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m' ms
/\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
/\ (forall o n, acc asegs m o n -> o + n <= USTACK_TOP -> o + n <= top \/ bottom <= o -> acc asegs m' o n)) c
/\ rt_pois RT Σ' = pois_drop bottom (rt_pois RT Σ)
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ).

Definition allocas_unpoison_nop_contract : Prop :=
forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem),
fdfs_only PMc -> mat_stable PMc -> (a0 = Z_to_bv 64 0 \/ bv_unsigned a1 < bv_unsigned a0) -> mem_inv asegs m ->
cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
t3 t4 t5 t6 F fc e_allocas_unpoison m)))
(ASTA RT Σ PMc (fun ms => exists v0, ret_stF F fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 m ms)).

Definition client_consts (m : mem) : Prop :=
ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
/\ ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
/\ ro_cells asegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
/\ ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].

Definition ACC_LITS : list (Z * Z) :=
[(0x23260, 24); (0x232a0, 6); (0x23320, 39); (0x23380, 48); (0x233e0, 51); (0x23440, 30); (0x23480, 43); (0x234e0, 37);
(0x23540, 18); (0x23580, 13); (0x235c0, 32); (0x23600, 16); (0x23720, 16); (0x23760, 9); (0x23780, 23); (0x237c0, 39);
(0x23820, 18); (0x23880, 11); (0x23a40, 25); (0x23a80, 37); (0x23ae0, 10); (0x23b00, 28); (0x23b40, 32); (0x23b80, 4);
(0x23ba0, 8); (0x23bc0, 44); (0x23c20, 40); (0x23c80, 32); (0x23cc0, 51); (0x23d20, 62); (0x23d80, 39); (0x23de0, 46);
(0x23e40, 16); (0x23e60, 43); (0x23ec0, 18); (0x23f20, 44); (0x23f80, 800); (0x24380, 396); (0x24580, 220); (0x24680, 88);
(0x24720, 60); (0x24780, 60); (0x247e0, 84); (0x24880, 640); (0x24ba0, 320); (0x24d20, 320); (0x24ea0, 320); (0x25020, 320);
(0x251c0, 512); (0x25440, 512); (0x256e0, 128); (0x257a0, 160); (0x25880, 320); (0x25a20, 1024); (0x25f40, 512); (0x261e0, 320);
(0x26380, 1280); (0x269e0, 640); (0x26d20, 25); (0x26d60, 32); (0x26da0, 31); (0x26de0, 16); (0x26fc0, 25); (0x27000, 256);
(0x27140, 128); (0x271e0, 64); (0x27240, 51); (0x272a0, 16); (0x272c0, 18); (0x27320, 320); (0x274c0, 1024); (0xefb00, 208);
(0xefc00, 96); (0xefc80, 88); (0xefd00, 88); (0xefd80, 88); (0xefe00, 88); (0xefe80, 88); (0xeff00, 88); (0xeff80, 88);
(0xf0000, 88); (0xf0080, 16); (0xf00a0, 24); (0xf00e0, 16); (0xf0100, 24); (0xf0140, 16); (0xf0160, 24); (0xf01a0, 16);
(0xf01c0, 24); (0xf0200, 24); (0xf0240, 24); (0xf0280, 96); (0xf0300, 96); (0xf0380, 24); (0xf03c0, 88); (0xf0440, 88);
(0xf04c0, 88); (0xf0540, 88); (0xf05c0, 216); (0xf06c0, 24); (0xf0700, 24); (0xf0740, 216)].

Record art_facts : Prop := mkAF {
af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;

af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
(forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
wmono asegs m m' -> ART RT Σ m';

af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);

af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at asegs m p n /\ acc asegs m p n;

af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
exists slack, bytes_at asegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
/\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;

af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP ->
pois_apart (rt_pois RT Σ) a n   -> acc asegs m a n;

af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
(forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0xf8230 <= a + i < 0xf9bb0)) -> acc asegs m a n;

af_live_range : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p);
af_live_disj : forall Σ m p1 n1 p2 n2 l1 l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) ->
p1 + n1 <= p2 \/ p2 + n2 <= p1;
af_frames_range : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
0 < f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
/\ forall p n, In (p, n) (rt_live RT Σ) -> f + fs_size k <= p \/ p + n <= f;
af_sp0_range : forall Σ m, ART RT Σ m -> SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ <= USTACK_TOP;

af_sp0_win : forall Σ m, ART RT Σ m -> 0x7fff80000000 <= rt_sp0 RT Σ;

af_frame_release : forall Σ (m : mem) f k fr, ART RT Σ m -> rt_frames RT Σ = (f, k) :: fr ->
(fr = [] -> rt_pois RT Σ = [])   ->
exists (Σ' : rts RT) (fl : Z), rw_cells asegs m fl [C1 (Z_to_bv 8 1)]
/\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl

/\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN

/\ ro_cells asegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
/\ forall m', munch [(fl, fl + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' fl [C1 (Z_to_bv 8 0)] ->
ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo)
/\ rt_pois RT Σ' = rt_pois RT Σ;

af_frames_align : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f;
af_frames_disj : forall Σ m f1 k1 f2 k2 l1 l2, ART RT Σ m -> rt_frames RT Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1;
af_fshadow_apart : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
(forall p n, In (p, n) (rt_live RT Σ) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
/\ (forall f' k', In (f', k') (rt_frames RT Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f');

af_got_lib : forall Σ m, ART RT Σ m ->
ro_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)] /\ ro_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)];

af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) ACC_LITS;

af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;

af_live_offshadow : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;

af_credit_nonneg : forall Σ m, ART RT Σ m -> 0 <= rt_credit RT Σ;

af_acc_pois : forall Σ m a n, ART RT Σ m -> In (a, n) (rt_pois RT Σ) -> acc asegs m a n;

af_pois_nil : forall Σ m, ART RT Σ m -> rt_frames RT Σ = [] -> rt_pois RT Σ = [];

af_pois_range : forall Σ m a n, ART RT Σ m -> In (a, n) (rt_pois RT Σ) ->
a mod 32 = 0 /\ 0 <= n /\ rt_sp0 RT Σ - STACK_WIN + 64 <= a - 32 /\ alloca_rr a n <= USTACK_TOP - 16;

af_live_small : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> n <= 64512 -> SEGTOP_A <= p
}.

Record rt_contracts : Prop := mkRTC {
rc_malloc : malloc_contract;
rc_free : free_contract;
rc_free_null : free_null_contract;
rc_calloc : calloc_contract;
rc_memcpy : memcpy_icontract e_memcpy;
rc_asan_memcpy : memcpy_icontract e_asan_memcpy;
rc_memset : memset_icontract e_memset;
rc_asan_memset : memset_icontract e_asan_memset;
rc_memchr : memchr_icontract;
rc_strlen : strlen_icontract;
rc_strnlen : strnlen_icontract;
rc_stack_malloc_0 : stack_malloc_contract 0;
rc_stack_malloc_2 : stack_malloc_contract 2;
rc_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract v;
rc_facts : art_facts
}.

Record rt_contracts_x : Prop := mkRTX {
rx_realloc : realloc_contract;
rx_stack_malloc_5 : stack_malloc_contract 5;
rx_stack_malloc_8 : stack_malloc_contract 8;
rx_stack_free : forall k, (k = 5 \/ k = 6 \/ k = 8)%nat -> stack_free_contract k;
rx_asan_memmove : memmove_icontract e_asan_memmove;
rx_memmove : memmove_icontract e_memmove;
rx_bcmp : bcmp_icontract;
rx_alloca_poison : alloca_poison_contract;
rx_allocas_unpoison : allocas_unpoison_contract;
rx_allocas_unpoison_nop : allocas_unpoison_nop_contract
}.

Lemma pois_release_ok : art_facts -> forall Σ0 m0 Σ fr, ART RT Σ0 m0 -> rt_frames RT Σ0 = fr -> rt_pois RT Σ = rt_pois RT Σ0 -> (fr = [] -> rt_pois RT Σ = []).
Proof. intros AF Σ0 m0 Σ fr HA HF HP E. rewrite HP. apply (af_pois_nil AF Σ0 m0 HA). rewrite HF. exact E. Qed.

End Contracts.

Ltac frames_nil_tac :=
first [ assumption
| match goal with E : rt_frames ?RT ?S' = rt_frames ?RT ?S |- rt_frames ?RT ?S' = [] => rewrite E; frames_nil_tac end
| match goal with H : _ /\ rt_frames ?RT ?S = [] /\ _ |- rt_frames ?RT ?S = [] => exact (proj1 (proj2 H)) end
| match goal with H : ?P |- rt_frames ?RT ?S = [] =>
let P' := eval hnf in P in lazymatch P' with _ /\ rt_frames RT S = [] /\ _ => exact (proj1 (proj2 H)) end end ].
Ltac pois_nil_tac AF :=
match goal with
| HA : ART ?RT ?S ?m |- pois_above (rt_pois ?RT ?S) _ => rewrite (af_pois_nil RT AF S m HA ltac:(frames_nil_tac)); apply pois_above_nil
| HA : ART ?RT ?S ?m |- pois_apart (rt_pois ?RT ?S) _ _ => rewrite (af_pois_nil RT AF S m HA ltac:(frames_nil_tac)); apply pois_apart_nil
end.

Definition PMfd (F0 : list (word * FdEntry)) (fs0 : Fs) : Model -> Prop := fun mo => m_fds mo = F0 /\ m_fs mo = fs0.

Lemma PMfd_fdfs_only : forall F0 fs0, fdfs_only (PMfd F0 fs0).
Proof. intros F0 fs0 mo mo' E1 E2 [H1 H2]. split; congruence. Qed.

Definition rt_pres_fp (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
forall a : word, aclient live frames sp (bv_unsigned a) -> outside W (bv_unsigned a) -> m' a = m a.

Definition errno_cell (tp : word) : Z := bv_unsigned tp - 164.

Definition FMT_usage : Z := 0x164e7.
Definition FMT_cannot_open : Z := 0x1f2f3.
Definition FMT_read_error : Z := 0x1f308.
Definition FMT_too_big : Z := 0x1ab8e.
Definition FMT_emit : Z := 0x151ae.

Definition STDERR_FILE : Z := 0xf7f30.

Inductive fp_case : Type :=
| FPusage (argv0 : Z) (s : list byte)
| FPcannot_open (path : Z) (s : list byte)
| FPread_error (path : Z) (s : list byte)
| FPtoo_big.

Definition fp_fmt (c : fp_case) : Z :=
match c with FPusage _ _ => FMT_usage | FPcannot_open _ _ => FMT_cannot_open
| FPread_error _ _ => FMT_read_error | FPtoo_big => FMT_too_big end.
Definition fp_arg (c : fp_case) : Z :=
match c with FPusage a _ | FPcannot_open a _ | FPread_error a _ => a | FPtoo_big => 67108864 end.

Definition fp_str (c : fp_case) : option (Z * list byte) :=
match c with FPusage a s | FPcannot_open a s | FPread_error a s => Some (a, s) | FPtoo_big => None end.

Definition fp_msg (c : fp_case) : list Z :=
match c with
| FPusage _ s => msg_usage (map bv_unsigned s)
| FPcannot_open _ s => msg_cannot_open (map bv_unsigned s)
| FPread_error _ s => msg_read_error (map bv_unsigned s)
| FPtoo_big => msg_too_big
end.

Definition so_lines (k : nat) : stdout_st := mkStdout true (zeros_out k) false false.

Definition io_ssp (m : mem) : Prop :=
exists g : word, ro_cells asegs m 0xf45d8 [C8 (Z_to_bv 64 0x650498)] /\ ro_cells asegs m 0x650498 [C8 g].

Section IO.
Variable RT : rt_sig.

Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.

Variable IO_FP : list (Z * Z).

Definition read_icontract_file : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage   ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
let bs := file_read data off (Z_to_bv 64 count) in
cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
(fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
/\ bytes_at asegs m' buf bs)).

Definition read_icontract_dir : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (fd buf count : Z) (lo : Z),
a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
buf = g_read_stage   ->
3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
(forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
tp = Z_to_bv 64 0x630458 -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_read m)))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m'
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(errno_cell tp, errno_cell tp + 4)] m m')).

Definition fprintf_stderr_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (c : fp_case) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 (fp_fmt c) -> a2 = Z_to_bv 64 (fp_arg c) ->
errp = STDERR_FILE ->
(forall a s, fp_str c = Some (a, s) -> bytes_at asegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
/\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)

/\ bv_unsigned sp <= a
/\ exists slack, bytes_at asegs m (a + Z.of_nat (length s) + 1) slack
/\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
/\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
(evw 2 (fp_msg c))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Definition fwrite_stderr_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (sa : Z) (s : list byte) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 errp ->
errp = STDERR_FILE -> 0 < Z.of_nat (length s) <= 64 ->
(sa = 0x2198e \/ sa = 0x164f8)   ->
bytes_at asegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
(evw 2 (map bv_unsigned s))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Definition emit0_out (so : stdout_st) : list Z := if so_first so then [48; 10] else [].
Definition emit0_next (so : stdout_st) : stdout_st :=
if so_first so then so_lines 0 else mkStdout true (so_buf so ++ [48; 10]) false false.

Definition vprintf_emit0_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
rw_cells asegs m ap [C8 (Z_to_bv 64 0)]   ->
ap = bv_unsigned sp + 24   ->
(so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
OUT_rep so m -> io_ssp m ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
(evw 1 (emit0_out so))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).

Inductive fpl_kind : Type := FLnotify | FLwarn | FLwarn_int.
Definition fpl_fmts (k : fpl_kind) : list Z :=
match k with
| FLnotify => [0x23540; 0x23820; 0x23ec0; 0x272c0]
| FLwarn => [0x23580]
| FLwarn_int => [0x23600; 0x23e40; 0x26de0; 0x272a0]
end.
Definition FPL_NOTIFY : list Z := [110; 111; 116; 105; 102; 105; 99; 97; 116; 105; 111; 110; 58; 32].
Definition FPL_WARN : list Z := [119; 97; 114; 110; 105; 110; 103; 58; 32].
Definition fpl_int (v : Z) : list Z :=
if v =? 0 then [48] else if v <? 0 then 45 :: X1ry.dec_digits (- v) else X1ry.dec_digits v.
Definition fpl_msg (k : fpl_kind) (str : list byte) (v : Z) : list Z :=
match k with
| FLnotify => FPL_NOTIFY ++ map bv_unsigned str ++ [10]
| FLwarn => FPL_WARN ++ map bv_unsigned str ++ [10]
| FLwarn_int => FPL_WARN ++ map bv_unsigned str ++ [32] ++ fpl_int v ++ [10]
end.

Definition fprintf_lib_icontract : Prop :=
forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
F fc (m : mem) (k : fpl_kind) (fmt sa v : Z) (str : list byte) (errp : Z) (lo : Z),
a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 fmt -> a2 = Z_to_bv 64 sa -> (k = FLwarn_int -> a3 = Z_to_bv 64 v /\ - 2^31 <= v < 2^31) ->
errp = STDERR_FILE -> In fmt (fpl_fmts k) ->
(exists n, In (sa, n) ACC_LITS /\ Z.of_nat (length str) + 1 <= n) -> bytes_at asegs m sa (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str ->
fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
ERR_rep m -> io_ssp m ->
ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> pois_above (rt_pois RT Σ) (bv_unsigned sp) ->
cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
(evw 2 (fpl_msg k str v))
(ASTA RT Σ (PMfd F0 fs0)
(fun ms => exists r m', ret_stR fc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r m' ms
/\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
/\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

Record io_contracts : Prop := mkIOC {
ioc_read_file : read_icontract_file;
ioc_read_dir : read_icontract_dir;
ioc_fprintf : fprintf_stderr_icontract;
ioc_fwrite : fwrite_stderr_icontract;
ioc_vprintf : vprintf_emit0_icontract
}.

Record io_contracts_x : Prop := mkIOX {
iox_fprintf_lib : fprintf_lib_icontract
}.

End IO.
