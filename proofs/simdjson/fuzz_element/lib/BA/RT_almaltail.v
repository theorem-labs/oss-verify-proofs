(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs R_glue_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_poison R_leaves R_setshadow R_depot_defs R_unwind_defs R_asan_defs R_allocate1 R_allocate2 R_allocate3 R_asan_malloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_facts RT_icfacts RT_malstate RT_maltail R_alalloc1 R_alalloc2 R_alalloc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.

Lemma hb1al_props : forall b1, 0 <= b1 < 256 -> 0 <= hb1al b1 < 256 /\ hb1al b1 mod 4 = 1.
Proof.
  intros b1 Hb. assert (H : forallb (fun k => (0 <=? hb1al k) && (hb1al k <? 256) && (hb1al k mod 4 =? 1)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H b1 ltac:(apply in_map_iff; exists (Z.to_nat b1); split; [lia | apply in_seq; lia])).
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.eqb_eq in H3. lia.
Qed.

Section TailAl.
Variables (Σ : rtsA) (mX : mem) (B : Z) (gp s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A : word) (F : bvmap 5 word) (fc : bv 32)
  (n lo : Z) (tr : list Z).
Hypothesis HA : ART_A Σ mX.
Hypothesis Hn : 1 <= n <= 64512.
Hypothesis Hca : ca Σ (ClassID (needed2 n)) <> [].
Hypothesis LOW : l_ACEIL (lay Σ) <= lo.
Hypothesis LOR : lo + 0x1000 <= B + -144.
Hypothesis SPT : B + 16 <= USTACK_TOP.
Hypothesis SPA : B mod 16 = 0.
Hypothesis Htr : tr_ok tr.
Hypothesis Htrl : (1 <= length tr <= 30)%nat.
Hypothesis HR16 : rounded n mod 16 = 0.
Hypothesis HS16 : needed n + 16 <= ClassSize (ClassID (needed2 n)).
Hypothesis SPT2 : B + 24 + 2064 <= 2 ^ 63.

#[local] Notation L := (lay Σ).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation TCX := (l_TCX (lay Σ)).
#[local] Notation DNB := (l_DNB (lay Σ)).
#[local] Notation SSB := (l_SSB (lay Σ)).
#[local] Notation c := (ClassID (needed2 n)).
#[local] Notation i := (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0)).
#[local] Notation AB := (p_abeg (l_SB (lay Σ)) (ClassID (needed2 n)) (Z.to_nat (last (ca Σ (ClassID (needed2 n))) 0))).
#[local] Notation S := (ClassSize (ClassID (needed2 n))).
#[local] Notation D := (dep Σ).
#[local] Notation BK := (DEP_BK (hash_of (d_hs (dep Σ)) 1)).
#[local] Notation W_tail := (RT_maltail.W_tail Σ B n).
#[local] Notation tail_facts := (RT_maltail.tail_facts Σ n tr).

#[local] Notation tl_geo := (RT_maltail.tl_geo Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation tl_cls := (RT_maltail.tl_cls n Hn).
#[local] Notation tl_room := (RT_maltail.tl_room n Hn).
#[local] Notation tl_rr := (RT_maltail.tl_rr n Hn).
#[local] Notation tl_fp := (RT_maltail.tl_fp n Hn).
#[local] Notation tl_apart := (RT_maltail.tl_apart Σ mX HA).
#[local] Notation tl_shad := (RT_maltail.tl_shad Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation tl_shadows := (RT_maltail.tl_shadows Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation tl_dep := (RT_maltail.tl_dep Σ mX tr HA Htrl).
#[local] Notation tl_static := (RT_maltail.tl_static Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation tl_chunk_stk := (RT_maltail.tl_chunk_stk Σ mX n HA Hn Hca).
#[local] Notation tl_shadow_stk := (RT_maltail.tl_shadow_stk Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation tl_p3stats := (RT_maltail.tl_p3stats Σ mX HA).
#[local] Notation dep_far_T := (RT_maltail.dep_far_T Σ mX HA).
#[local] Notation dep_far_stk := (RT_maltail.dep_far_stk Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation dep_far_shad := (RT_maltail.dep_far_shad Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation dep_far_chunk := (RT_maltail.dep_far_chunk Σ mX B n lo HA Hn Hca LOW LOR SPT SPA).
#[local] Notation dep_frame_far := (RT_maltail.dep_frame_far Σ).

Definition tail_post_al : machine_state -> Prop :=
  fun ms => exists m', ret_stF fc (Z_to_bv 64 0x5c248) (Z_to_bv 64 (B + -16)) gp (Z_to_bv 64 tpA) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A
                         s10A s11A (Z_to_bv 64 (AB + rz_size n)) m' ms
    /\ munch W_tail mX m' /\ wmono asegs mX m' /\ mem_inv asegs m' /\ stk asegs m' lo (B + -16) /\ tail_facts m'.

Definition af32_cells (m : mem) (j0 : list byte) : Prop :=
  alloc_frame32 m (B + -144) (Z_to_bv 64 0x5c248) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A
  /\ rw_cells asegs m (B + -144) [CB 8 j0].

Lemma af32_transport : forall W (m m' : mem) j0, af32_cells m j0 -> munch W m m' -> wmono asegs m m' ->
  disjoint_from W (B + -144) 128 -> af32_cells m' j0.
Proof.
  clear HA Hn Hca LOW LOR SPT SPA Htr Htrl HR16 HS16 SPT2.
  intros W m m' j0 (A1 & A2) MU WM DJ. unfold alloc_frame32 in *.
  split; [apply (rw_cells_transport asegs _ m m' _ _ A1 MU WM); cbn [cells_size csize Nat.add]; eapply dsj_sub; [exact DJ | lia | lia]|].
  apply (rw_cells_transport asegs _ m m' _ _ A2 MU WM); cbn [cells_size csize Nat.add]; eapply dsj_sub; [exact DJ | lia | lia].
Qed.

Local Ltac clear_disj := repeat match goal with X : _ \/ _ |- _ => clear X end.
Local Ltac sep_one := clear_disj; first
  [ unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A in *; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (_ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (_ & X & _); unfold apart in X; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia
  | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia ].

Local Ltac sep_s0 := unfold SHB, K_HIGH_SHADOW_hi, K_LOW_SHADOW_lo, SEGTOP_A in *; lia.
Local Ltac sep_s1 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s2 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X);
    unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s3 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s4 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia.
Local Ltac sep_s5 := pose proof tl_apart as (_ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s6 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s7 := pose proof tl_apart as (X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s8 := pose proof tl_apart as (_ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s9 := pose proof tl_apart as (_ & _ & _ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s10 := pose proof tl_apart as (_ & X & _); unfold apart in X; destruct X; lia.
Local Ltac sep_s11 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct X; lia.
Local Ltac sep_s12 := pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _); unfold SEGTOP_A in *; destruct X; lia.
Local Ltac sep_fast := clear_disj; first
  [ lazymatch goal with
    | |- context [l_T _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s5 | |- context [l_SSB _] => sep_s6 | |- context [l_PRB _] => sep_s7
         | |- context [shad _] => sep_s3 | |- context [p_abeg _ _ _] => sep_s7 | |- context [17594333495296%Z] => sep_s3
         | |- _ => first [ sep_s4 | sep_s3 | sep_s0 ] end
    | |- context [l_TCX _] => lazymatch goal with
         | |- context [17594333495296%Z] => sep_s11 | |- context [l_PRB _] => sep_s10 | |- _ => first [ sep_s12 | sep_s0 ] end
    | |- context [shad _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s1 | |- context [l_SSB _] => sep_s2 | |- _ => sep_s0 end
    | |- context [p_abeg _ _ _] => lazymatch goal with
         | |- context [l_DNB _] => sep_s8 | |- context [l_SSB _] => sep_s9 | |- _ => sep_s0 end
    | |- _ => sep_s0
    end
  | sep_one ].

Local Ltac piece k Hx := let Hy := fresh "Hy" in intros Hy;
  eapply (not_outside W_tail _ _ _ (nth_error_In W_tail k eq_refl)); [|exact Hx]; cbn [fst snd]; lia.

Lemma tl_p3b_al : forall (m6 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail mX m6 -> wmono asegs mX m6 -> mem_inv asegs m6 -> stk asegs m6 lo (B + -144) ->
  af32_cells m6 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells asegs m6 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at asegs m6 (shad (AB + rz_size n)) (ushadow n) -> bytes_at asegs m6 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at asegs m6 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m6 ->
  pc_cells m6 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt asegs tail_post_al (MS (mkR ra0 (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 s0v (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) s3v (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16)) s6v
                             (Z_to_bv 64 (B + 24)) (Z_to_bv 64 0) s9v (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x5bd14) fc None m6 (seg_rom asegs)).
Proof using HA Hn Hca LOW LOR SPT SPA Htrl HR16 HS16 SPT2.
  intros m6 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 s0v s6v s9v s3v j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD US RZ1 RZ2 DR PC.
  pose proof tl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room as (R1 & R2 & R3 & R4 & R5).
  pose proof (tl_chunk_stk m6 WM) as CH.
  assert (CH2 : stk asegs m6 (AB + rz_size n) (AB + rz_size n + Z.min n 4096)).
  { pose proof (proj2 (stk_split asegs m6 AB (AB + rz_size n) (AB + S) CH ltac:(lia))) as X.
    exact (proj1 (stk_split asegs m6 (AB + rz_size n) (AB + rz_size n + Z.min n 4096) (AB + S) X ltac:(lia))). }
  destruct (stk_CB m6 (AB + rz_size n) (Z.min n 4096) CH2 ltac:(lia)) as (uj & UJ).
  destruct (stk_CB m6 AB 16 ltac:(apply (proj1 (stk_split asegs m6 AB (AB + 16) (AB + S) CH ltac:(lia)))) ltac:(lia)) as (lj & LJ).
  destruct (tl_static m6 MU WM) as (_ & _ & _ & SS & GAF & F44 & F52 & _ & TP16 & G9a & MFH & _).
  destruct AF as (AF & J0).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_mono.
  { apply (allocate_p3b_al_spec (Z_to_bv 64 (B + -144)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s0v s6v s9v s3v
             (Z_to_bv 64 0x5c248) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m6 n AB (B + 24) T lo b1 h0 uj lj j0 ctx);
      rewrite ?unsigned_lit by exact RS; try assumption; try (intros _; exact LJ);
      unfold kHighShadowEnd, kHighMemEnd, K_HIGH_SHADOW_hi, SHB in *; lia. }
  intros ms (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m7 & -> & MU7 & WM7 & MI7 & HD7 & UJ7 & LCH7 & ST7).
  rewrite unsigned_lit in MU7, ST7 by exact RS. rewrite sp_off by exact RS.
  replace (B + -144 + 128) with (B + -16) in * by lia.
  assert (D7 : forall a k, (a + k <= AB \/ AB + S <= a) -> (a + k <= B + -176 \/ B + -16 <= a) ->
               disjoint_from [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (B + -144 - 32, B + -16)] a k).
  { intros a k H1 H2. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (DSH : forall a k, shad AB <= a -> a + k <= shad AB + S / 8 ->
               disjoint_from [(AB, AB + 16); (AB + rz_size n + -16, AB + rz_size n + Z.min n 4096); (B + -144 - 32, B + -16)] a k).
  { intros a k H1 H2. pose proof tl_shad as (S1 & S2 & S3). apply D7; unfold SHB, K_HIGH_SHADOW_hi in *; lia. }
  exists m7. split; [exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', F; reflexivity|].
  split.
  { apply (munch_into _ _ mX m6 m7 MU MU7). intros x Hx. cbn [outside]. split; [piece 3%nat Hx|]. split; [piece 3%nat Hx|].
    split; [piece 2%nat Hx | exact I]. }
  split; [exact (wmono_trans asegs _ _ _ WM WM7)|]. split; [exact MI7|]. split; [exact ST7|].
  pose proof tl_apart as (A02 & _ & A06 & A07 & _). pose proof tl_dep as (_ & _ & OK' & _).
  unfold apart in *. split; [exists (Z_to_bv 8 (Z.land b1 243)), ctx; split; [exact (land243_mod4 b1 Hb1 Hb4) | exact HD7]|].
  split; [intros Hr; exact (LCH7 Hr)|].
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_shadows as (E1 & E2 & _ & E4 & _).
  split; [apply (bytes_at_transport asegs _ m6 m7 _ _ US MU7); apply DSH; [rewrite E1; lia | rewrite E1, R3; lia]|].
  split; [apply (bytes_at_transport asegs _ m6 m7 _ _ RZ1 MU7); apply DSH; [lia | rewrite FL by lia; lia]|].
  split; [apply (bytes_at_transport asegs _ m6 m7 _ _ RZ2 MU7); apply DSH; [rewrite E2; lia|];
          rewrite E2, FL by (apply Z.div_pos; lia); pose proof tl_rr as (Hrr0 & _); lia|].
  split; [apply (dep_frame_far _ _ _ _ m6 m7 DR OK' MU7 WM7); cbn [far_all];
          split; [apply dep_far_chunk; lia|]; split; [apply dep_far_chunk; lia|]; split; [apply dep_far_stk; lia | exact I]|].
  apply (rw_cells_transport asegs _ m6 m7 _ _ PC MU7 WM7). cbn [cells_size csize Nat.add]. apply D7; unfold pc_addr; pose proof tl_cls as (K1' & _); sep_fast.
Qed.

Lemma tl_p3a_al : forall (m5 : mem) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail mX m5 -> wmono asegs mX m5 -> mem_inv asegs m5 -> stk asegs m5 lo (B + -144) ->
  af32_cells m5 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells asegs m5 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at asegs m5 (shad (AB + rz_size n)) (zrun (size_rd n / 8)) -> bytes_at asegs m5 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at asegs m5 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m5 ->
  pc_cells m5 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt asegs tail_post_al (MS (mkR ra0 (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x5bb20) fc None m5 (seg_rom asegs)).
Proof using HA Hn Hca LOW LOR SPT SPA Htrl HR16 HS16 SPT2.
  intros m5 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra0 j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD ZR RZ1 RZ2 DR PC.
  pose proof tl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). pose proof (size_rd_facts n ltac:(lia)) as (D1 & D2 & D3).
  pose proof tl_shad as (S1 & S2 & S3). pose proof (tl_shadow_stk m5 WM) as SST.
  destruct (tl_static m5 MU WM) as (TC & M2S & _ & _ & GAF & _ & _ & F85 & _ & _ & _ & CP & _ & _).
  assert (S8 : 0 <= size_rd n / 8) by (apply Z.div_pos; lia). assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  assert (PBx : exists pb : byte, n mod 8 <> 0 -> rw_cells asegs m5 (shad (AB + rz_size n + size_rd n)) [C1 pb]).
  { destruct (Z.eq_dec (n mod 8) 0) as [Hm0|Hm0]; [exists (Z_to_bv 8 0); intros X; contradiction|].
    pose proof (E7 Hm0) as X7.
    assert (SP1 : stk asegs m5 (shad AB + rz_size n / 8 + size_rd n / 8) (shad AB + S / 8))
      by exact (proj2 (stk_split asegs m5 (shad AB) (shad AB + rz_size n / 8 + size_rd n / 8) (shad AB + S / 8) SST ltac:(lia))).
    destruct (rw_C1_of m5 (shad (AB + rz_size n + size_rd n))
                ltac:(rewrite E3; exact (proj1 (stk_split asegs m5 _ (shad AB + rz_size n / 8 + size_rd n / 8 + 1) _ SP1 ltac:(lia)))))
      as (pb & PB).
    exists pb. intros _. exact PB. }
  destruct PBx as (pb & PB).
  destruct AF as (AF & J0).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_cut.
  { apply (allocate_p3a_al_spec (Z_to_bv 64 (B + -144)) gp ra0 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (Z_to_bv 64 1) (Z_to_bv 64 (AB + rz_size n + n))
             (Z_to_bv 64 0x5c248) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m5 n AB (B + 24) TCX T lo pb);
      rewrite ?unsigned_lit by exact RS; try assumption; try exact PB; try exact (tl_p3stats m5 WM);
      unfold kHighShadowEnd, kHighMemEnd in *; sep_fast. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & s6' & m6 & -> & MU6 & WM6 & MI6 & SC6 & PB6 & ST6).
  rewrite unsigned_lit in MU6, ST6 by exact RS. rewrite E3 in MU6, PB6.
  set (PW := if n mod 8 =? 0 then 0 else 1) in MU6.
  assert (HPW : 0 <= PW <= 1 /\ (n mod 8 = 0 -> PW = 0) /\ (n mod 8 <> 0 -> PW = 1)).
  { unfold PW. destruct (Z.eqb_spec (n mod 8) 0); lia. }
  clearbody PW. destruct HPW as (PW1 & PW2 & PW3).
  assert (D6 : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 + size_rd n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 + PW <= a) ->
               (a + k <= T + 2800 \/ T + 3168 <= a) -> (a + k <= B + -144 - 32 \/ B + -144 <= a) ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -144 - 32, B + -144)] a k).
  { intros a k Hk H1 H2 H3. cbn [disjoint_from]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia | exact I]. }
  assert (TSH : forall a k, shad AB <= a -> a + k <= shad AB + S / 8 -> (a + k <= T + 2800 \/ T + 3168 <= a)).
  { intros a k H1 H2. sep_fast. }
  assert (USH : bytes_at asegs m6 (shad (AB + rz_size n)) (ushadow n)).
  { pose proof (bytes_at_transport asegs _ m5 m6 _ _ ZR MU6) as ZR6.
    assert (Lz : Z.of_nat (length (zrun (size_rd n / 8))) = size_rd n / 8) by (unfold zrun; rewrite repeat_length; lia).
    rewrite Lz in ZR6. specialize (ZR6 ltac:(rewrite E1; apply D6; [lia | lia | apply TSH; lia | lia])).
    assert (E8' : size_rd n / 8 = n / 8) by (unfold size_rd; rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
    unfold ushadow. unfold zrun in ZR6. rewrite E8' in ZR6. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm].
    - rewrite app_nil_r. exact ZR6.
    - apply bytes_at_app. split; [exact ZR6|]. rewrite repeat_length, Z2Nat.id by (apply Z.div_pos; lia). rewrite E1.
      destruct (PB6 Hm) as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. rewrite <- E8'. exact Hb. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr as (Hrr & _).
  assert (DSH : forall a k, 0 <= k -> shad AB <= a -> a + k <= shad AB + S / 8 ->
               (a + k <= shad AB + rz_size n / 8 + size_rd n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 + PW <= a) ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -144 - 32, B + -144)] a k).
  { intros a k Hk H1 H2 H3. apply D6; [lia | exact H3 | apply (TSH a k H1 H2) | unfold SHB in *; lia]. }
  assert (DCH : forall a k, 0 <= k -> AB <= a -> a + k <= AB + S ->
               disjoint_from [(shad AB + rz_size n / 8 + size_rd n / 8, shad AB + rz_size n / 8 + size_rd n / 8 + PW); (T + 2800, T + 2824);
                              (T + 2904, T + 2912 + 256); (B + -144 - 32, B + -144)] a k).
  { intros a k Hk H1 H2. pose proof tl_apart as (A02 & _). unfold apart, K_HIGH_SHADOW_hi, SHB in *. apply D6; [lia | lia | lia | lia]. }
  apply (tl_p3b_al m6 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ra' (Z_to_bv 64 1) s6' (Z_to_bv 64 (AB + rz_size n + n))
           (Z_to_bv 64 (needed n + 16)) j0 h0 b1 ctx).
  - apply (munch_into _ _ mX m5 m6 MU MU6). intros x Hx. cbn [outside]. split; [piece 4%nat Hx|]. split; [piece 1%nat Hx|].
    split; [piece 1%nat Hx|]. split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans asegs _ _ _ WM WM6).
  - exact MI6.
  - exact ST6.
  - apply (af32_transport _ m5 m6 _ (conj AF J0) MU6 WM6). apply D6; sep_fast.
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport asegs _ m5 m6 _ _ HD MU6 WM6). cbn [cells_size csize Nat.add]. apply DCH; lia.
  - exact USH.
  - apply (bytes_at_transport asegs _ m5 m6 _ _ RZ1 MU6). rewrite FL by (apply Z.div_pos; lia). apply DSH; lia.
  - apply (bytes_at_transport asegs _ m5 m6 _ _ RZ2 MU6). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DSH; [lia | lia | lia |].
    right. destruct (Z.eqb_spec (n mod 8) 0) as [Hm|Hm]; [rewrite (PW2 Hm), (E8 Hm); lia | rewrite (PW3 Hm), <- (E7 Hm); lia].
  - pose proof tl_dep as (_ & _ & OK' & _).
    apply (dep_frame_far _ _ _ _ m5 m6 DR OK' MU6 WM6). cbn [far_all].
    split; [apply dep_far_shad; lia|]. split; [apply dep_far_T; lia|]. split; [apply dep_far_T; lia|]. split; [apply dep_far_stk; lia | exact I].
  - apply (rw_cells_transport asegs _ m5 m6 _ _ PC MU6 WM6). cbn [cells_size csize Nat.add]. unfold pc_addr. pose proof tl_cls as (K1' & _).
    apply D6; sep_fast.
Qed.

Lemma tl_ps_al : forall (m4 : mem) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  8 <= n ->
  munch W_tail mX m4 -> wmono asegs mX m4 -> mem_inv asegs m4 -> stk asegs m4 lo (B + -144) ->
  af32_cells m4 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells asegs m4 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at asegs m4 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at asegs m4 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m4 ->
  pc_cells m4 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt asegs tail_post_al (MS (mkR (Z_to_bv 64 0x5bb20) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
                             (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 0) a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 ps_entry) fc None m4 (seg_rom asegs)).
Proof using HA Hn Hca LOW LOR SPT SPA Htrl HR16 HS16 SPT2.
  intros m4 t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 h0 b1 ctx H8 MU WM MI ST AF Hb1 Hb4 HD RZ1 RZ2 DR PC.
  pose proof tl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_room as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8). pose proof (size_rd_facts n ltac:(lia)) as (D1 & D2 & D3).
  pose proof tl_shad as (S1 & S2 & S3). pose proof (tl_shadow_stk m4 WM) as SST.
  destruct (tl_static m4 MU WM) as (_ & _ & PSC & _).
  assert (S8 : 1 <= size_rd n / 8) by (unfold size_rd; rewrite Z.mul_comm, Z.div_mul by lia; apply Z.div_le_lower_bound; lia).
  destruct (stk_CB m4 (shad (AB + rz_size n)) (size_rd n / 8)
              ltac:(rewrite E1; apply (proj1 (stk_split asegs m4 _ (shad AB + rz_size n / 8 + size_rd n / 8) _
                    (proj2 (stk_split asegs m4 (shad AB) (shad AB + rz_size n / 8) _ SST ltac:(lia))) ltac:(lia)))) ltac:(lia))
    as (shj & SHJ).
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold SHB in *; lia).
  assert (PSA : ps_args_ok (AB + rz_size n) (size_rd n)).
  { unfold ps_args_ok. split; [split; [rewrite Z.add_mod, (mod8_of AB 16 ltac:(lia) G3 ltac:(exists 2; reflexivity)),
                                      (mod8_of (rz_size n) 16 ltac:(lia) ltac:(exact (rz_size_mod16 n)) ltac:(exists 2; reflexivity)) by lia; reflexivity|]|].
    - split; [exact D1 | lia].
    - right. unfold kHighShadowEnd, kHighMemEnd, K_HIGH_SHADOW_hi in *. lia. }
  assert (S8u : size_rd n / 8 < 0x10000) by (apply Z.div_lt_upper_bound; lia).
  eapply evt_cut.
  { apply (poison_small_spec (Z_to_bv 64 0x5bb20) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n)
             a3 a4 a5 a6 a7 (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
             (Z_to_bv 64 (size_rd n)) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n)) (Z_to_bv 64 T) (Z_to_bv 64 1)
             t3 t4 t5 t6 F fc m4 (AB + rz_size n) (size_rd n) 0 lo shj); rewrite ?unsigned_lit by exact RS; try assumption;
      first [ right; exact S8u | unfold kHighShadowEnd, SHB in *; lia ]. }
  intros ms (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m5 & -> & MU5 & WM5 & MI5 & ZR5 & ST5).
  rewrite unsigned_lit in MU5, ST5 by exact RS. rewrite (ret_pc_even 0x5bb20) by (lia || reflexivity). rewrite E1 in MU5, ZR5.
  assert (D5 : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 <= a) ->
               (a + k <= B + -144 - 64 \/ B + -144 <= a) ->
               disjoint_from [(shad AB + rz_size n / 8, shad AB + rz_size n / 8 + size_rd n / 8); (B + -144 - 64, B + -144)] a k).
  { intros a k Hk H1 H2. cbn [disjoint_from]. split; [lia|]. split; [lia | exact I]. }
  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr as (Hrr & _).
  assert (DFAR : forall a k, 0 <= k -> (a + k <= shad AB + rz_size n / 8 \/ shad AB + rz_size n / 8 + size_rd n / 8 <= a) ->
               a + k <= l_ACEIL L -> disjoint_from [(shad AB + rz_size n / 8, shad AB + rz_size n / 8 + size_rd n / 8); (B + -144 - 64, B + -144)] a k).
  { intros a k Hk H1 H2. apply D5; [lia | lia | left; lia]. }
  apply (tl_p3a_al m5 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (Z_to_bv 64 0x5bb20) j0 h0 b1 ctx).
  - apply (munch_into _ _ mX m4 m5 MU MU5). intros x Hx. cbn [outside]. split; [piece 4%nat Hx|]. split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans asegs _ _ _ WM WM5).
  - exact MI5.
  - exact ST5.
  - apply (af32_transport _ m4 m5 _ AF MU5 WM5). apply D5; [lia | unfold SHB in *; lia | lia].
  - exact Hb1.
  - exact Hb4.
  - apply (rw_cells_transport asegs _ m4 m5 _ _ HD MU5 WM5). cbn [cells_size csize Nat.add]. apply DFAR; [lia | unfold SHB, K_HIGH_SHADOW_hi in *; lia | lia].
  - rewrite E1. destruct ZR5 as [[_ Hb] _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
  - apply (bytes_at_transport asegs _ m4 m5 _ _ RZ1 MU5). rewrite FL by (apply Z.div_pos; lia). apply DFAR; lia.
  - apply (bytes_at_transport asegs _ m4 m5 _ _ RZ2 MU5). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DFAR; lia.
  - pose proof tl_dep as (_ & _ & OK' & _). pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & BS).
    apply (dep_frame_far _ _ _ _ m4 m5 DR OK' MU5 WM5). cbn [far_all].
    split; [apply dep_far_shad; lia|]. split; [apply dep_far_stk; lia | exact I].
  - apply (rw_cells_transport asegs _ m4 m5 _ _ PC MU5 WM5). cbn [cells_size csize Nat.add]. unfold pc_addr. pose proof tl_cls as (K1' & _).
    apply D5; sep_fast.
Qed.

Lemma tl_p2P_al : forall (m3 : mem) (ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (j0 h0 : list byte) (b1 : Z) (ctx : word),
  munch W_tail mX m3 -> wmono asegs mX m3 -> mem_inv asegs m3 -> stk asegs m3 lo (B + -144) ->
  af32_cells m3 j0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 ->
  rw_cells asegs m3 (AB + rz_size n + -16) [CB 1 h0; C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 ctx] ->
  bytes_at asegs m3 (shad AB) (farun (rz_size n / 8)) ->
  bytes_at asegs m3 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8)) ->
  depot_rep (fst (depot_put D tr)) BK DNB SSB m3 ->
  pc_cells m3 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt asegs tail_post_al (MS (mkR ra' (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 AB) (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 (AB + rz_size n)) (Z_to_bv 64 (AB + rz_size n + -16))
                             (Z_to_bv 64 INST) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 0) (Z_to_bv 64 (AB + rz_size n + n))
                             (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x5ba24) fc None m3 (seg_rom asegs)).
Proof using HA Hn Hca LOW LOR SPT SPA Htrl HR16 HS16 SPT2.
  intros m3 ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j0 h0 b1 ctx MU WM MI ST AF Hb1 Hb4 HD RZ1 RZ2 DR PC.
  pose proof tl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls as (K1 & K2 & K3 & K4 & K5 & K6 & _ & K8 & _). pose proof tl_shadows as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  pose proof (tl_shadow_stk m3 WM) as SST. pose proof tl_shad as (S1 & S2 & S3).
  assert (S8p : 2 <= S / 8) by (apply Z.div_le_lower_bound; lia).
  destruct (tl_static m3 MU WM) as (_ & (M1 & M2 & _) & _).
  assert (M1' : rw_cells asegs m3 0x16a230 [C8 (Z_to_bv 64 0x173c38)]) by exact (rw_cells_app_l m3 _ [C8 (Z_to_bv 64 0x173c38)] _ M1).
  assert (SB0 : rw_cells asegs m3 (shad AB) [C1 (Z_to_bv 8 K_kAsanHeapLeftRedzoneMagic)]).
  { destruct (rw_C1_of m3 (shad AB) ltac:(apply (proj1 (stk_split asegs m3 _ (shad AB + 1) _ SST ltac:(lia))))) as (b & Hb).
    destruct Hb as [[Hw Hb] R]. split; [split; [exact Hw|] | exact R].
    unfold farun in RZ1. replace (Z.to_nat (rz_size n / 8)) with (Datatypes.S (Z.to_nat (rz_size n / 8) - 1)) in RZ1 by lia.
    cbn [repeat] in RZ1. cbn [cells_bytes cbytes app]. apply (bytes_at_app asegs m3 _ [_] _) in RZ1 as [X _]. exact X. }
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold SHB in *; lia).
  eapply evt_cut.
  { apply (allocate_p2P_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra' F fc m3 n AB
             (B + 24) T lo (Z_to_bv 8 K_kAsanHeapLeftRedzoneMagic) (Z_to_bv 64 (needed n + 16))); rewrite ?unsigned_lit by exact RS; try assumption;
      try (unfold K_kAsanHeapLeftRedzoneMagic; rewrite Z_to_bv_unsigned; cbn; discriminate);
      unfold kHighShadowEnd, K_HIGH_SHADOW_hi in *; lia. }
  intros ms (m4 & HS & MU4 & WM4 & MI4 & _ & ST4).
  assert (MUe : munch W_tail mX m4) by (apply (munch_into _ _ mX m3 m4 MU MU4); intros x _; exact I).
  assert (TR : forall a cs, rw_cells asegs m3 a cs -> rw_cells asegs m4 a cs) by (intros a cs H; exact (rw_cells_transport asegs [] m3 m4 _ _ H MU4 WM4 I)).
  assert (TB' : forall a bs, bytes_at asegs m3 a bs -> bytes_at asegs m4 a bs) by (intros a bs H; exact (bytes_at_transport asegs [] m3 m4 _ _ H MU4 I)).
  assert (AF4 : af32_cells m4 j0) by exact (af32_transport [] m3 m4 j0 AF MU4 WM4 I).
  assert (DR4 : depot_rep (fst (depot_put D tr)) BK DNB SSB m4).
  { pose proof tl_dep as (_ & _ & OK' & _). exact (depot_rep_frame _ _ _ _ _ [] m3 m4 DR OK' MU4 WM4 I I I I I I). }
  destruct (8 <=? n) eqn:E8n.
  - apply Z.leb_le in E8n. destruct HS as (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    rewrite unsigned_lit in ST4 by lia.
    exact (tl_ps_al m4 t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j0 h0 b1 ctx E8n MUe (wmono_trans asegs _ _ _ WM WM4) MI4 ST4
             AF4 Hb1 Hb4 (TR _ _ HD) (TB' _ _ RZ1) (TB' _ _ RZ2) DR4 (TR _ _ PC)).
  - apply Z.leb_gt in E8n. destruct HS as (ra'' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & ->).
    rewrite unsigned_lit in ST4 by lia.
    assert (Hz0 : size_rd n = 0) by (unfold size_rd; rewrite Z.div_small by lia; reflexivity).
    eapply evt_eq; [| apply (tl_p3a_al m4 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' ra'' j0 h0 b1 ctx MUe
                               (wmono_trans asegs _ _ _ WM WM4) MI4 ST4 AF4 Hb1 Hb4 (TR _ _ HD) ltac:(rewrite Hz0; apply bytes_at_nil; unfold SHB in *; lia)
                               (TB' _ _ RZ1) (TB' _ _ RZ2) DR4 (TR _ _ PC))].
    rewrite Hz0. reflexivity.
Qed.

Lemma tl_p2a_al : forall (m2 : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (tb : list word) (j0 : list byte),
  munch W_tail mX m2 -> wmono asegs mX m2 -> mem_inv asegs m2 -> stk asegs m2 lo (B + -144) ->
  af32_cells m2 j0 -> trc_cells (B + 24) tr m2 tb ->
  bytes_at asegs m2 (shad AB) (farun (S / 8)) -> depot_rep D BK DNB SSB m2 ->
  pc_cells m2 (pc_addr T c) (Z.of_nat (length (ca Σ c)) - 1) (MaxCount c) (ClassSize c) ->
  evt asegs tail_post_al (MS (mkR (Z_to_bv 64 0x5b908) (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2
                             (Z_to_bv 64 (Z.b2z (from_primary n))) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
                             (Z_to_bv 64 16) (Z_to_bv 64 (needed n + 16)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n) (Z_to_bv 64 INST)
                             (Z_to_bv 64 (B + 24)) (Z_to_bv 64 (0 + - (16))) (Z_to_bv 64 15) (Z_to_bv 64 T) (Z_to_bv 64 1) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x5b908) fc None m2 (seg_rom asegs)).
Proof using HA Hn Hca LOW LOR SPT SPA Htr Htrl HR16 HS16 SPT2.
  intros m2 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 tb j0 MU WM MI ST AF IC SH DR PC.
  pose proof tl_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21).
  pose proof tl_cls as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9). pose proof tl_room as (R1 & R2 & R3 & R4 & R5).
  pose proof tl_shadows as (E1 & E2 & E3 & E4 & E5 & E6 & _ & _). pose proof tl_shad as (S1 & S2 & S3).
  pose proof tl_dep as (OK & DI & OK' & DN2 & DT).
  destruct (tl_static m2 MU WM) as (TC & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TX8 & TT0).
  pose proof (tl_chunk_stk m2 WM) as CH.
  destruct (stk_CB m2 (AB + rz_size n - 16) 16 ltac:(apply (proj1 (stk_split asegs m2 _ (AB + rz_size n - 16 + 16) _
              (proj2 (stk_split asegs m2 AB (AB + rz_size n - 16) _ CH ltac:(lia))) ltac:(lia)))) ltac:(lia)) as (hdr & HD).

  assert (FL : forall k, 0 <= k -> Z.of_nat (length (farun k)) = k) by (intros k Hk; unfold farun; rewrite repeat_length; lia).
  pose proof tl_rr as (Hrr & _).
  assert (U8 : 0 <= ru8 n / 8) by (apply Z.div_pos; lia).
  assert (SPL : farun (S / 8) = farun (rz_size n / 8) ++ farun (ru8 n / 8) ++ farun ((S - rz_size n - ru8 n) / 8)).
  { unfold farun. rewrite <- !repeat_app. f_equal. rewrite Hrr. clear - E4 E6 U8. lia. }
  rewrite SPL in SH. apply bytes_at_app in SH as [RZ1 SH]. rewrite FL in SH by (apply Z.div_pos; lia).
  apply bytes_at_app in SH as [_ RZ2]. rewrite FL in RZ2 by lia.
  assert (RZ2' : bytes_at asegs m2 (shad (AB + rz_size n + ru8 n)) (farun ((S - rz_size n - ru8 n) / 8))) by (rewrite E2; replace (shad AB + rz_size n / 8 + ru8 n / 8) with (shad AB + rz_size n / 8 + ru8 n / 8) by lia; exact RZ2).
  clear RZ2. rename RZ2' into RZ2.
  destruct IC as (I6 & I4 & HTB).
  assert (I6' : rw_cells asegs m2 (B + 24) [C8 (Z_to_bv 64 (B + 24 + 16)); C8 (Z_to_bv 64 (Z.of_nat (length (map (Z_to_bv 64) tr))))])
    by (rewrite map_length; exact I6).
  assert (I4' : u64arr asegs m2 (B + 24 + 16) (map (Z_to_bv 64) tr ++ skipn (length tr) tb))
    by exact I4.
  assert (RS : 0 <= B + -144 < 2 ^ 64) by (unfold SHB in *; lia).
  pose proof (T_MAIN_range tr Htr) as TRR.
  assert (HBK : In (bkt (depot_hash (map bv_unsigned (map (Z_to_bv 64) tr)))) BK).
  { rewrite (map_unsigned_lit tr TRR). unfold DEP_BK. apply in_BK_ALL. unfold bkt. apply Z.mod_pos_bound. lia. }
  eapply evt_cut.
  { apply (allocate_p2aal_spec (Z_to_bv 64 (B + -144)) gp (Z_to_bv 64 tpA) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
             (Z_to_bv 64 0x5c248) s0A s1A s2A s3A s4A s5A s6A s7A s8A s9A s10A s11A F fc m2 n AB (B + 24) TCX T lo hdr D BK DNB SSB
             (map (Z_to_bv 64) tr) (skipn (length tr) tb)); rewrite ?unsigned_lit by exact RS.
    - lia.
    - unfold K_HIGH_SHADOW_hi in *. lia.
    - exact G3.
    - lia.
    - exact HD.
    - exact (proj1 AF).
    - exact TT0.
    - exact TX8.
    - exact I6'.
    - exact I4'.
    - rewrite app_length, map_length, skipn_length. lia.
    - rewrite map_length. lia.
    - apply (depot_ok_mono _ _ _ _ _ OK). lia.
    - exact DR.
    - rewrite map_length. exact DT.
    - exact HBK.
    - exact DN2.
    - exact ST.
    - lia.
    - lia.
    - lia.
    - pose proof tl_apart as (A02 & _). unfold apart in A02. destruct A02; lia.
    - pose proof tl_apart as (_ & A03 & _). unfold apart in A03. destruct A03; lia.
    - pose proof tl_apart as (_ & _ & A06 & _). unfold apart in A06. destruct A06; lia.
    - pose proof tl_apart as (_ & _ & _ & A07 & _). unfold apart in A07. destruct A07; lia.
    - lia.
    - lia.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & A26 & _). unfold apart in A26. destruct A26; lia.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & _ & A27 & _). unfold apart in A27. destruct A27; lia.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & A36 & _). unfold apart in A36. destruct A36; lia.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & A37 & _). unfold apart in A37. destruct A37; lia.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _). unfold SEGTOP_A in TP. exact TP.
    - pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & XP & _). unfold SEGTOP_A in XP. destruct XP; lia.
    - exact MI. }
  intros ms (ra' & t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & MU3 & WM3 & MI3 & HD3 & DR3 & TB3 & ST3).
  rewrite unsigned_lit in MU3, ST3 by exact RS. rewrite (map_unsigned_lit tr TRR) in HD3, DR3. rewrite tl_fp.
  pose proof (hb1al_props (hdr_b1 hdr) (hdr_b1_range hdr)) as (HB1 & HB4).
  assert (D3 : forall a k, 0 <= k -> (a + k <= AB + rz_size n + -16 \/ AB + rz_size n <= a) ->
               (a + k <= 0x245b08 \/ 0x655b30 <= a) -> (a + k <= DNB \/ DNB + 2 ^ 20 <= a) -> (a + k <= SSB \/ SSB + 2 ^ 23 <= a) ->
               (a + k <= B + -144 - 224 \/ B + -144 <= a) ->
               disjoint_from [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
                              (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (B + -144 - 224, B + -144)] a k).
  { intros a k Hk H1 H2 H3 H4 H5. cbn [disjoint_from]. split; [exact H1|]. split; [clear H1 H3 H4 H5; destruct H2; lia|].
    split; [clear H1 H3 H4 H5; destruct H2; lia|]. split; [exact H3|]. split; [clear H1 H3 H4 H5; destruct H2; lia|].
    split; [clear H1 H3 H4 H5; destruct H2; lia|]. split; [exact H4|]. split; [exact H5 | exact I]. }
  assert (DSH : forall a k, 0 <= k -> shad AB <= a -> a + k <= shad AB + S / 8 ->
               disjoint_from [(AB + rz_size n + -16, AB + rz_size n); (d_tab, d_nuniq + 4); (d_map1, d_map1 + 8); (DNB, DNB + 2 ^ 20);
                              (s_total, s_total + 8); (s_data0, s_stored0 + 4); (SSB, SSB + 2 ^ 23); (B + -144 - 224, B + -144)] a k).
  { intros a k Hk H1 H2. pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & DS & BS).
    apply D3; [lia | unfold K_HIGH_SHADOW_hi, SHB in *; lia | unfold SHB in *; lia | clear BS; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct DS; lia
              | clear DS; unfold K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi, SHB in *; destruct BS; lia | unfold SHB in *; lia]. }
  apply (tl_p2P_al m3 ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' j0
           (firstn 1 hdr) (hb1al (hdr_b1 hdr)) (Z_to_bv 64 (snd (depot_put D tr)))).
  - apply (munch_into _ _ mX m2 m3 MU MU3). intros x Hx. cbn [outside]. split; [piece 3%nat Hx|]. split; [piece 5%nat Hx|].
    split; [piece 6%nat Hx|]. split; [piece 7%nat Hx|]. split; [piece 8%nat Hx|]. split; [piece 9%nat Hx|]. split; [piece 10%nat Hx|].
    split; [piece 2%nat Hx | exact I].
  - exact (wmono_trans asegs _ _ _ WM WM3).
  - exact MI3.
  - exact ST3.
  - apply (af32_transport _ m2 m3 _ AF MU3 WM3). apply D3; unfold apart, K_HIGH_SHADOW_hi, SEGTOP_A in *; try lia.
  - exact HB1.
  - exact HB4.
  - exact HD3.
  - apply (bytes_at_transport asegs _ m2 m3 _ _ RZ1 MU3). rewrite FL by lia. apply DSH; lia.
  - apply (bytes_at_transport asegs _ m2 m3 _ _ RZ2 MU3). rewrite FL by (apply Z.div_pos; lia). rewrite E2. apply DSH; lia.
  - exact DR3.
  - apply (rw_cells_transport asegs _ m2 m3 _ _ PC MU3 WM3). cbn [cells_size csize Nat.add]. unfold pc_addr in *.
    pose proof tl_cls as (K1' & _).
    apply D3; [lia | pose proof tl_apart as (A02 & _); unfold apart in A02; destruct A02; lia
              | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TP & _); unfold SEGTOP_A in TP; destruct TP; lia
              | pose proof tl_apart as (_ & _ & _ & _ & _ & A26 & _); unfold apart in A26; destruct A26; lia
              | pose proof tl_apart as (_ & _ & _ & _ & _ & _ & A27 & _); unfold apart in A27; destruct A27; lia | lia].
Qed.

End TailAl.

End GWIN.
