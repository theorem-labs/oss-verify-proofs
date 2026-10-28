(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 AKitQ AKitR ARep ARepKit ARepFrame RT_stubs
     F_apoison F_acache F_aalloc_s F_aalloc1 F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom F_arefill F_amaybe F_areturn F_acdrain F_acdealloc AFreeGeo.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac zr_known e := match goal with | _ : context [e] |- _ => idtac | _ := context [e] |- _ => idtac end.
Local Ltac zrange ::=
  lazymatch goal with
  | |- inr64 ?e =>
      lazymatch e with
      | bv_unsigned _ => first [ apply zr_word | apply zr_bv; vm_compute; congruence ]
      | Z.land _ ?mk => first [ is_Zlit_zb mk; apply zr_land_lit; flia
                              | apply zr_land_l; [zrange | zrange_nonneg] | apply zr_land_r; [zrange_nonneg | zrange] ]
      | Z.lor _ _ => apply zr_lor; [zrange | zrange]
      | Z.lxor _ _ => apply zr_lxor; [zrange | zrange]
      | Z.shiftr _ _ => apply zr_shiftr; [zrange | flia]
      | Z.modulo _ (2^64)%Z => apply zr_mod64
      | Z.modulo _ _ => first [ apply zr_mod_any; flia | apply zr_mod; flia ]
      | Z.div _ _ => apply zr_div; [zrange | flia]
      | Z.b2z _ => apply zr_b2z
      | (if _ then _ else _) => apply zr_ite; [zrange | zrange]
      | Z.shiftl _ _ => zr_known e; apply zr_lit; flia
      | bv_signed _ => zr_known e; apply zr_lit; flia   (* [comment removed for export] *)
      | _ => first [ apply zr_lit; flia
                   | is_var e; progress (unfold e); zrange ]   (* [comment removed for export] *)
      end
  | |- (0 <= ?e < _)%Z => change (inr64 e); zrange
  end.

Section CANSEC1. Context {rc : runConstT}.
Definition recyc1_entry : Z := 0x35b54.
End CANSEC1.
Notation RECYC1_STACK := 688 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma v_divuw_low : forall x y, 0 <= x < 2^64 -> 0 < y < 2^31 -> (x mod 2^32) / y < 2^31 ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 ((x mod 2^32) / y).
Proof.
  intros x y Hx Hy Hq. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *. change (2^32) with 4294967296 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal.
  assert (B : 0 <= (x mod 4294967296) / y) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Lemma class_of_offset : forall c off, 0 <= c < 32 -> 0 <= off < 2^32 ->
  Z.shiftr (Z.shiftl (c * 4294967296 + off) 27 mod 2^64) 59 = c.
Proof.
  intros c off Hc Ho. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616. change (2^59) with 576460752303423488. change (2^27) with 134217728. change (2^32) with 4294967296 in Ho.
  rewrite Z.mod_small by nia. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition recyc1_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c kslot n b1 ctx lo : Z) (chunks : list word) (m : amem)
    (stX : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let AB := aslot_addr L c kslot in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  exists m1,
     munch [(bv_unsigned sp - 112, bv_unsigned sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z m m1
  /\ wmono bsegs m m1
  /\ cdealloc_ret L RNG sp st c AB lo chunks m1 stX RNG' m'
  /\ (16 < rz -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 HB)])
  /\ rw_cells bsegs m' HB [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (granules n)))].

(* [comment removed for export] *)
Lemma disjoint_from_app : forall W1 W2 A k, disjoint_from W1 A k -> disjoint_from W2 A k -> disjoint_from (W1 ++ W2) A k.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 A k H1 H2; cbn in *; [exact H2|]. destruct H1 as [H H1]. split; [exact H| apply IH; assumption]. Qed.

Lemma cd_W_disjoint_user : forall L sp c nf mfa mfa' c' A k,
  1 <= c < 32 -> 1 <= c' < 32 -> 0 <= nf -> 0 <= mfa -> mfa' <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP ->
  sclr (al_t L) 4096 -> (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  ATOP <= sp - 688 ->
  aregion L c' <= A -> 0 <= k -> A + k <= aregion L c' + K_FREEARR_OFF ->
  disjoint_from (cd_W L sp c nf mfa mfa') A k.
Proof.
  intros L sp c nf mfa mfa' c' A k HC HC' NF MFA MFA' SP1 SP2 T0 TSP CEIL R0 K0 R1. band_lin.   (* [comment removed for export] *)
  assert (RBE : aregion L c' = al_space_beg L + c' * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr, aregion, K_REGION, K_FREEARR_OFF; change (2^32) with 4294967296; reflexivity).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (SHF : shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= 0x10007fff8000).
  { rewrite shad_div, shlen_div, FAE. unfold ASHOFF, K_FREEARR_MAX in *. clear -SP1 SP2 HC MFA MFA'. unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. Z.div_mod_to_equations. lia. }
  assert (SHB2 : 2148256256 <= shad (afreearr L c + mfa)) by (rewrite shad_div, FAE; unfold ASHOFF; clear -SP1 HC MFA NF; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold cd_W. cbv zeta. unfold K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
  assert (RR : c' <> c -> aregion L c' + 4294967296 <= aregion L c \/ aregion L c + 4294967296 <= aregion L c') by (intros NE; rewrite RBE; unfold aregion, K_REGION; change (2^32) with 4294967296; clear -NE HC HC'; nia).
  apply disjoint_from_app; [cbn; split; [clear -CEIL R0 R1 RBE SP1 SP2 HC'; lia| exact I]|].
  apply disjoint_from_app.
  { destruct TSP as [T|T].
    - apply ic_W_disjoint_gen; [right; rewrite RBE in R0; clear -R0 T SP1 HC' T0; lia| clear; cbn; lia| clear; lia].
    - apply ic_W_disjoint_gen; [left; unfold acache_addr; rewrite RBE in R1; clear -R1 T SP1 SP2 HC'; lia| clear; cbn; lia| clear; lia]. }
  cbn. unfold acache_addr.
  repeat split; try exact I.
  all: try (clear -R0 R1 RBE TSP HC HC' SP1 SP2 T0; lia).
  all: try (clear -R0 R1 RBE HC HC' SP1 SP2 RIE; lia).
  all: try (clear -SHF R0 RBE SP1 HC'; lia).
  all: destruct (Z.eq_dec c' c) as [->|NE]; [rewrite ?FAE; clear -R0 R1 RBE NF; lia| specialize (RR NE); rewrite ?FAE; rewrite RBE in *; unfold aregion, K_REGION in RR; change (2^32) with 4294967296 in RR; clear -R0 R1 RR NF HC HC' MFA'; lia].
Qed.

Lemma cd_W_disjoint_ushadow : forall L sp c nf mfa mfa' c' A k,
  1 <= c < 32 -> 1 <= c' < 32 -> 0 <= nf -> 0 <= mfa -> mfa <= mfa' <= K_FREEARR_MAX ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_t L) 4096 ->
  ATOP <= sp - 688 ->
  shad (aregion L c') <= A -> 0 <= k -> A + k <= shad (aregion L c' + K_FREEARR_OFF) ->
  disjoint_from (cd_W L sp c nf mfa mfa') A k.
Proof.
  intros L sp c nf mfa mfa' c' A k HC HC' NF MFA MFA' SP1 SP2 SP3 T0 CEIL R0 K0 R1. band_lin.   (* [comment removed for export] *)
  unfold sclr, KLS in T0.   (* [comment removed for export] *)
  assert (RBE : aregion L c' = al_space_beg L + c' * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (RBE2 : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (FAE : afreearr L c = aregion L c + 3758096384) by (unfold afreearr, K_FREEARR_OFF; reflexivity).
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  unfold K_FREEARR_OFF, K_FREEARR_MAX, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  assert (SH : 0x2008fff7000 <= shad (aregion L c') /\ shad (aregion L c' + 3758096384) <= 0x10007fff8000
               /\ (c' <> c -> shad (aregion L c' + 3758096384) <= shad (afreearr L c + mfa) \/ shad (afreearr L c + mfa) + shlen (mfa' - mfa) <= shad (aregion L c'))
               /\ (c' = c -> shad (aregion L c' + 3758096384) <= shad (afreearr L c + mfa))).
  { rewrite !shad_div, shlen_div, FAE, RBE, RBE2. unfold ASHOFF. clear -SP1 SP2 SP3 HC HC' MFA MFA' NF. Z.div_mod_to_equations. nia. }
  destruct SH as (S1 & S2 & S3 & S4).
  unfold cd_W. cbv zeta.
  apply disjoint_from_app; [cbn; split; [clear -CEIL R0 R1 S1 S2; lia| exact I]|].
  apply disjoint_from_app; [apply ic_W_disjoint_gen; [unfold acache_addr; clear -R0 R1 S1 S2 T0; lia| clear; cbn; lia| clear; lia]|].
  cbn. unfold acache_addr.
  repeat split; try exact I.
  all: try (clear -R0 R1 S1 S2 T0 HC; lia).
  all: try (clear -R0 R1 S1 S2 RIE SP1 HC; lia).
  all: try (rewrite FAE, RBE2; clear -R0 R1 S1 S2 SP1 NF HC; lia).
  all: destruct (Z.eq_dec c' c) as [E|NE]; [specialize (S4 E); clear -R0 R1 S4; lia| specialize (S3 NE); clear -R0 R1 S3; lia].
Qed.

End CANSEC2.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read bsegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok bsegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) (le8 ?v)) _) =>
      let S2 := fresh "STATS" in
      pose proof (u64arr_write bsegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

Section CANSEC3. Context {rc : runConstT}.
Lemma recyc1_spec : forall RNG {R} (k : astate -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c kslot n b1 ctx CBA lo : Z) (sj chunks : list word) (sta cbs : word) (shj : list byte),
  let r := get_cls st c in let RI := aregion_info L c in let FA := afreearr L c in let CA := acache_addr L c in
  let nf := c_num_freed r in let mfa := c_mapped_free_array r in let cnt := c_count r in let S := size_of_class c in
  let AB := aslot_addr L c kslot in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 HB ->
  rw_cells bsegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  m3_cells L m ->
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  u32arr bsegs m (CA + 16) chunks -> length chunks = 16%nat -> Forall (fun w : word => bv_unsigned w < 2^31) (firstn (Z.to_nat cnt) chunks) ->
  rw_cells bsegs m (al_t L + 2784) [C8 sta] ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0);
      C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0)] ->
  junk_at m (RI + 72) 56 ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  junk_at m (FA + 4 * nf) (mfa - 4 * nf) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  rw_cells bsegs m HB [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  (16 < rz -> rw_cells bsegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 HB)]) ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (granules n)) shj] ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  (forall j, 1 <= j <= 31 -> 0 <= c_count (get_cls st j) <= max_count st j) ->
  0 <= nf -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 -> 4 * (nf + max_cached c / 2) <= K_FREEARR_MAX ->
  0 <= kslot -> (kslot + 1) * S <= c_mapped_user r -> c_mapped_user r <= K_FREEARR_OFF ->
  1 <= n -> rz + n <= S -> 0 <= b1 < 256 -> 0 <= ctx < 2^64 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa -> rng RNG AB S -> rng RNG (shad AB) (shlen S) -> rng RNG CBA 16 ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      recyc1_ret L RNG sp st c kslot n b1 ctx lo chunks m stX RNG' m' ->
      implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until shj. cbv zeta.
  intros ST CEIL LO MI TP -> -> CBC CB0 CB1 MC RECS CH LCH CH31 STA MTX REG J72 STATS LSJ FJ AZF HDR MAG SHU
         SBE HC CNTS NF MFA MFAM NFN KS KMU MUB N1 FIT B1 CTX SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP
         RIMG RSTK RCTX RT RRI RFA RAB RSAB RCB CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  destruct (sclr_int _ _ T0 ltac:(clear -TIC; lia) ltac:(pose proof atop_range as AR; clear -T1 AR; lia)) as (kT0 & T0k).   (* [comment removed for export] *)
  destruct (sclr_int _ _ CX0 ltac:(clear -CXI; unfold AIMG_HI in *; lia) ltac:(pose proof atop_range as AR; clear -CX1 AR; lia)) as (kC & CXk).   (* [comment removed for export] *)
  unfold AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, recyc1_entry in *.
  change (2^37) with 137438953472 in *. change (2^32) with 4294967296 in *.
  word_range sp SPR.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (mu := c_mapped_user (get_cls st c)) in *.
  pose proof (size_of_class_pos c ltac:(unfold K_NUM_CLASSES; exact HC)) as [SZ SZ32].
  set (S := size_of_class c) in *.
  pose proof (rz_size_facts n ltac:(clear -N1; lia)) as [RZ1 RZ16].
  set (rz := rz_size n) in *.
  assert (RBE : aregion L c = al_space_beg L + c * 4294967296) by (unfold aregion, K_REGION; change (2^32) with 4294967296; reflexivity).
  assert (ABE : aslot_addr L c kslot = al_space_beg L + c * 4294967296 + kslot * S) by (unfold aslot_addr; rewrite RBE; reflexivity).
  set (AB := aslot_addr L c kslot) in *.
  assert (RIE : aregion_info L c = al_space_beg L + 137438953472 + c * 128) by (unfold aregion_info, K_SPACE_SIZE, ARI_STRIDE; change (2^37) with 137438953472; reflexivity).
  assert (FAE : afreearr L c = al_space_beg L + c * 4294967296 + 3758096384) by (unfold afreearr; rewrite RBE; unfold K_FREEARR_OFF; reflexivity).
  assert (CAE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (KSS : 0 <= kslot * S /\ kslot * S + S <= mu) by (clear -KS KMU SZ; nia).
  destruct KSS as [KS0 KS1].
  assert (AB16 : AB mod 16 = 0).
  { rewrite ABE. assert (QS : exists q, S = 32 * q) by (exists (S / 32); clear -SZ32 SZ; Z.div_mod_to_equations; lia).
    destruct QS as [q Hq]. rewrite Hq. replace (kslot * (32 * q)) with (32 * (kslot * q)) by (clear; lia).
    clear -SP3. Z.div_mod_to_equations. lia. }
  assert (SHUB : shad (AB + rz) = shad AB + shlen rz) by (apply shad_add_shlen; clear -AB16; Z.div_mod_to_equations; lia).
  assert (GR : shlen (rup n 8) = granules n) by (unfold granules, rup; rewrite !shlen_div; clear -N1; Z.div_mod_to_equations; lia).
  assert (GR0 : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -N1; Z.div_mod_to_equations; lia).
  assert (SHRZ : 2 <= shlen rz) by (rewrite shlen_div; clear -RZ1; Z.div_mod_to_equations; lia).
  assert (GRS : shlen rz + granules n <= shlen S).
  { unfold granules. rewrite !shlen_div. clear -N1 FIT RZ16 SZ32. Z.div_mod_to_equations. lia. }
  assert (SHLO : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fff8000).
  { rewrite shad_div, shlen_div, ABE. unfold ASHOFF. clear -SP1 SP2 HC KS0 KS1 MUB SZ. Z.div_mod_to_equations. lia. }
  destruct SHLO as [SHLO SHHI].
  assert (RUP8 : rup n 8 mod 8 = 0 /\ n <= rup n 8 <= n + 7) by (unfold rup; clear -N1; Z.div_mod_to_equations; lia).
  destruct RUP8 as [RUP8 RUPN].
  box TCX. box SCX. box TSP.
  iprefix.
  carve_frame 48%nat ST.
  box MTX. box REG. box STA. box CH. box STATS. box HDR. box MAG. box SHU. box CBC.
  snapshot [(bv_unsigned sp - 112, bv_unsigned sp)]%Z MUN WM.
  do 7 step.                                                   (* [comment removed for export] *)
  carry STATS MUN WM ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
  carry MTX MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry REG MUN WM ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
  carry STA MUN WM ltac:(clear -SPR CEIL LO T0 T1; lia).
  carry CH MUN WM ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
  carry HDR MUN WM ltac:(rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia).
  unbox MAG.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MAG' : 16 < rz -> rw_cells bsegs mm AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (AB + rz - 16))]);
    [ intros Hrz; pose proof (MAG Hrz) as MG; xport MG MUN WM ltac:(rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia); exact MG |]
  end.
  clear MAG.
  carry SHU MUN WM ltac:(clear -SPR CEIL LO SHUB SHLO SHHI GRS GR0; lia).
  carry CBC MUN WM ltac:(clear -SPR CB0 CB1; lia).
  assert (HB16 : (AB + rz - 16) mod 16 = 0) by (clear -AB16 RZ16; Z.div_mod_to_equations; lia).
  set (HB := AB + rz - 16) in *.
  assert (RHB : rng RNG HB 16) by (eapply rng_sub'; [exact RAB| subst HB; clear -RZ1 RZ16 FIT N1 SZ; lia]).
  assert (SHB : shad (HB + 16) = shad AB + shlen rz) by (replace (HB + 16) with (AB + rz) by (subst HB; clear; lia); exact SHUB).
  assert (OFF : 0 <= kslot * S + rz - 16 < 4294967296) by (clear -KS0 KS1 MUB RZ1 FIT N1; lia).
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MC1 : m3_cells L mm);
    [ eapply m3_cells_frame; [exact MC | exact MUN | exact WM |]; unfold AIMG_HI, AIMG_LO;
      apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 CXI TIC SPR CEIL LO; lia |]; apply Forall_nil |]
  end.
  clear MC. pose proof MC1 as MC0. destruct MC0 as (PC & RC & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
  step. step. step. step.                                      (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  assert (HBR : 0 <= HB < 2^64) by (clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 ABE SPR; subst HB; lia).   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by (clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 ABE SPR; subst HB; lia); clear -K1 SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 ABE; subst HB; lia|].   (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit in K2 by (clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 ABE SPR; subst HB; lia); clear -K2 SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 ABE; subst HB; lia|].   (* [comment removed for export] *)
  clear HBR.
  zstep.                                                       (* [comment removed for export] *)
  setreg 14 (Z_to_bv 64 (c * 4294967296 + (kslot * S + rz - 16))) ltac:(apply Z_to_bv_eqm; subst HB; rewrite ABE; clear -OFF SP1; Z.div_mod_to_equations; lia).
  zstep.                                                       (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 c) ltac:(rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^32) with 4294967296; f_equal; rewrite ?Z.mod_small by (clear -OFF HC; lia); clear -OFF HC; Z.div_mod_to_equations; nia).
  zstep.                                                       (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 c) ltac:(f_equal; change 31 with (Z.ones 5); rewrite Z.land_ones by (clear; lia); symmetry; apply Z.mod_small; clear -HC; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P (MS ?R ?FF _ ?fcc ?rv ?mm ?ro) =>
    let p15 := eval vm_compute in (bv_key (15 : bv 5)) in
    let p16 := eval vm_compute in (bv_key (16 : bv 5)) in
    let p17 := eval vm_compute in (bv_key (17 : bv 5)) in
    let T := eval cbv beta iota delta [tset] in
               (fun v6 v7 : word => MS (tset p17 v7 (tset p16 v6 (tset p15 (Z_to_bv 64 S : word) R))) FF (Z_to_bv 64 0x35c04) fcc rv mm ro) in
    assert (TAIL : forall v6 v7 : word, evtF bsegs RNG P (T v6 v7))
  end.
  { intros v6 v7. cbv beta.
    step.                                                      (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 kslot)
      ltac:(symmetry; etransitivity; [apply v_divuw_low; [clear -OFF HC; lia | fold S; clear -SZ; lia | ] |];
            [ change (2^32) with 4294967296; rewrite Z.add_comm, Z_mod_plus_full, Z.mod_small by (clear -OFF; lia); fold S; clear -OFF SZ RZ1 FIT N1 KS; Z.div_mod_to_equations; nia
            | f_equal; change (2^32) with 4294967296; rewrite Z.add_comm, Z_mod_plus_full, Z.mod_small by (clear -OFF; lia); fold S; clear -OFF SZ RZ1 FIT N1 KS; Z.div_mod_to_equations; nia ]).
    zstep.                                                     (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.                                (* [comment removed for export] *)
    setreg 12 (Z_to_bv 64 (aregion_info L c)) ltac:(rewrite RIE; unfold K_SPACE_SIZE; change (2^37) with 137438953472; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
    setreg 13 (Z_to_bv 64 (aregion L c)) ltac:(rewrite RBE; apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear; Z.div_mod_to_equations; lia).
    step.                                                      (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 14 (Z_to_bv 64 kslot) ltac:(rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by (clear; lia); rewrite ?Z.mod_small by (clear -KS OFF SZ RZ1; nia); f_equal; clear -KS; Z.div_mod_to_equations; nia).
    zstep. zstep. zstep.                                       (* [comment removed for export] *)
    replace (mu <? S * kslot + S) with false by (symmetry; apply Z.ltb_ge; clear -KS1; lia). cbn [Z.b2z].
    zstep.                                                     (* [comment removed for export] *)
    setreg 13 (Z_to_bv 64 AB) ltac:(rewrite ABE, RBE; f_equal; clear; lia).
    zstep. zstep.                                              (* [comment removed for export] *)
    setreg 18 (Z_to_bv 64 AB) ltac:(f_equal; change 18446744073709551615 with (Z.ones 64); rewrite Z.land_comm, Z.land_ones by (clear; lia);
                                   symmetry; apply Z.mod_small; rewrite ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia).
    step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K3; clear -K3 SP1 HC KS0; lia|].   (* [comment removed for export] *)
    step. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K4; clear -K4 SP1 SP2 HC KS0 OFF RZ1; lia|].   (* [comment removed for export] *)
    destruct (Z.lt_ge_cases 16 rz) as [RZBIG|RZ16x].
    - (* [comment removed for export] *)
      step. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by (subst HB; rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; subst HB; clear -K5 RZBIG; lia|].   (* [comment removed for export] *)
      pose proof (MAG' RZBIG) as MAGC. clear MAG'.
      clear PC RC TI TK T88 TSD CT ISB IREL ISE IPRE. box MUN.
      step. step.                                              (* [comment removed for export] *)
      assert (AMOD : amo_aligned AD (Z_to_bv 64 AB) = true) by (apply amo_alignedD_intro; [rewrite ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia| clear -AB16; Z.div_mod_to_equations; lia]).
      lrsc_stepA AMOD.                                         (* [comment removed for export] *)
      step. if_lit.                                            (* [comment removed for export] *)
      box HDR. box SHU. box STATS. box CBC. box CH. box STA. box MTX. box REG. box FR.
      snapshot [(AB, AB + 8)]%Z MUg WMg.
      lrsc_stepA AMOD.                                         (* [comment removed for export] *)
      carry HDR MUg WMg ltac:(subst HB; clear -RZBIG RZ16; Z.div_mod_to_equations; lia).
      carry SHU MUg WMg ltac:(clear -SHHI SHUB RZ1 SP1 HC KS0 ABE GRS GR0; lia).
      carry STATS MUg WMg ltac:(rewrite LSJ, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry CBC MUg WMg ltac:(rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CB0 SPR CEIL LO; lia).
      carry CH MUg WMg ltac:(rewrite LCH, CAE, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry STA MUg WMg ltac:(rewrite ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry MTX MUg WMg ltac:(rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry REG MUg WMg ltac:(rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry FR MUg WMg ltac:(rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 SPR CEIL LO; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC2 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC1 | exact MUg | exact WMg |]; unfold AIMG_HI, AIMG_LO; ub SCX;
          apply Forall_cons; [cbn [fst snd]; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CX0 CX1 CXI TIC Y; lia |]; apply Forall_nil |]
      end.
      clear MC1.
      step. if_lit.                                            (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep. step. step.                                (* [comment removed for export] *)
      change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by (subst HB; rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia).
      replace (HB - HB mod 2 ^ 2) with HB by (clear -HB16; Z.div_mod_to_equations; lia).
      zstep. zstep.                                            (* [comment removed for export] *)
      replace ((Z.shiftl HB 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -HB16; Z.div_mod_to_equations; lia).
      change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
      apply (rw_hdr_to_C4 _ _ 3 b1 _ ltac:(clear; lia) ltac:(exact B1)) in HDR.
      assert (AMOW : amo_aligned AW (Z_to_bv 64 HB) = true) by (apply amo_alignedW_intro; [subst HB; rewrite ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia| clear -HB16; Z.div_mod_to_equations; lia]).
      amo_stepA AMOW. rewrite sx32_lit by (clear -B1; lia).   (* [comment removed for export] *)
      zstep. rewrite (byte0_of_word 3 b1) by (clear -B1; lia).   (* [comment removed for export] *)
      step. if_lit.                                            (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      rewrite (byte0_cas 3 0 b1) by (clear -B1; lia).
      box SHU. box STATS. box CBC. box CH. box STA. box MTX. box REG. box FR. try box MAGC. try box MUg.
      snapshot [(HB, HB + 4)]%Z MUh WMh.
      amo_stepA AMOW.                                          (* [comment removed for export] *)
      carry SHU MUh WMh ltac:(subst HB; clear -SHHI SHUB RZ1 SP1 HC KS0 ABE GRS GR0; lia).
      carry STATS MUh WMh ltac:(subst HB; rewrite LSJ, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry CBC MUh WMh ltac:(subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CB0 SPR CEIL LO; lia).
      carry CH MUh WMh ltac:(subst HB; rewrite LCH, CAE, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry STA MUh WMh ltac:(subst HB; rewrite ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry MTX MUh WMh ltac:(subst HB; rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry REG MUh WMh ltac:(subst HB; rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry FR MUh WMh ltac:(subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 SPR CEIL LO; lia).
      try carry MAGC MUh WMh ltac:(subst HB; clear -RZBIG RZ16; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC3 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC2 | exact MUh | exact WMh |]; unfold AIMG_HI, AIMG_LO; ub SCX;
          apply Forall_cons; [cbn [fst snd]; subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CX0 CX1 CXI TIC Y; lia |]; apply Forall_nil |]
      end.
      clear MC2.
      step. if_lit.                                            (* [comment removed for export] *)
      apply (rw_C4_to_hdr _ _ 0 b1 _ ltac:(clear; lia) ltac:(exact B1)) in HDR.
      lstep. lstep.                                            (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      rewrite Z.lor_0_l.
      zstep. zstep.                                            (* [comment removed for export] *)
      setreg 11 (Z_to_bv 64 (rup n 8)) ltac:(change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -N1 FIT SZ RZ1; lia); unfold rup; f_equal; clear -N1; Z.div_mod_to_equations; lia).
      step.                                                    (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SHU' : rw_cells bsegs mm (shad (HB + 16)) [CB (Z.to_nat (shlen (rup n 8))) shj]) by (rewrite GR; replace (HB + 16) with (AB + rz) by (subst HB; clear; lia); exact SHU)
      end.
      pose proof MC3 as MC3'. destruct MC3' as (PC3 & _).
      box STATS. box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box MUh. box FR.
      snapshot [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (shad (HB + 16), shad (HB + 16) + shlen (rup n 8))]%Z MUp WMp.
      (* [comment removed for export] *)
      clear SHU. box SHU'. box ST.
      assert (RG1 : rng RNG lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) - lo))
        by (rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub; [exact RSTK | clear; lia | clear -CEIL LO; lia]).
      assert (RG2 : rng RNG (shad (HB + 16)) (shlen (rup n 8))) by (rewrite SHB; eapply rng_sub; [exact RSAB | clear -SHRZ; lia | rewrite GR; clear -GRS SHRZ; lia]).
      step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (HB + 16) (rup n 8) 250 lo shj);
        [ unboxed ST | atop_facts; exact CEIL | clear -LO; lia | assumption | exact PC3 | reflexivity | reflexivity | reflexivity
        | clear -HB16; Z.div_mod_to_equations; lia | exact RUP8 | clear -RUPN N1; lia
        | unfold ablk; right; subst HB; rewrite ABE; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 RUPN FIT N1; lia
        | pose proof atop_range as AR; subst HB; rewrite ABE; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 RUPN FIT N1 AR; lia
        | clear; lia | intros; discriminate | unboxed SHU' | ].
      clear ST SHU' RG1 RG2.
      rename PC into ST. rename POST into SHU2. try rename MI0 into MI.
      carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T0k T1 SHLO SHHI SHB SHRZ GRS GR ABE SP1 HC KS0 RZ1; lia).
      carry CBC MUp WMp ltac:(clear -SPR CEIL LO CB0 CB1 SHHI SHB SHRZ GRS GR ABE SP1 SP2 HC KS0 RZ1; lia).
      carry CH MUp WMp ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T0k T1 SHLO HC SHHI SHB SHRZ GRS GR ABE SP1 KS0 RZ1; lia).
      carry STA MUp WMp ltac:(clear -SPR CEIL LO T0 T0k T1 SHLO SHHI SHB SHRZ GRS GR ABE SP1 HC KS0 RZ1; lia).
      carry MTX MUp WMp ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 RZ1; lia).
      carry REG MUp WMp ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 RZ1; lia).
      carry HDR MUp WMp ltac:(subst HB; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 KS1 MUB RZ1 FIT N1; lia).
      try carry MAGC MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 KS1 MUB RZ1 FIT N1; lia).
      carry FR MUp WMp ltac:(clear -SPR CEIL LO SHHI SHB SHRZ GRS GR ABE SP1 SP2 HC KS0 RZ1; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC4 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC3 | exact MUp | exact WMp |]; unfold AIMG_HI, AIMG_LO;
          apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC; lia |];
          apply Forall_cons; [cbn [fst snd]; clear -SHLO SHHI SHB SHRZ GRS GR CX0 CXk; lia |]; apply Forall_nil |]
      end.
      clear MC3 PC3 WMp. box MUp.
      pose proof MC4 as MC4'. destruct MC4' as (PC4 & RC4 & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
      (* [comment removed for export] *)
      box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box FR. box SHU2. box STATS.
      snapshot [(bv_unsigned sp + -48 - 32, bv_unsigned sp + -48)]%Z MUt WMt.
      (* [comment removed for export] *)
      box ST. box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
      assert (RG1 : rng RNG lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) - lo))
        by (rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub; [exact RSTK | clear; lia | clear -CEIL LO; lia]).
      step. call_sp (thread_stats_spec RNG (al_ctx L) (al_t L) lo);
        [ unboxed ST | atop_facts; exact CEIL | clear -LO; lia | assumption | exact TP | unboxed TI | unboxed TK | unboxed T88 | unboxed TSD | unboxed CT
        | clear -CXI; unfold AIMG_HI in *; lia | atop_facts; exact CX1 | exact TIC | atop_facts; exact T1 | ].   (* [comment removed for export] *)
      clear ST TI TK T88 TSD CT ISB IREL ISE IPRE RG1.
      rename POST into ST. try rename MI0 into MI.
      carry CBC MUt WMt ltac:(clear -SPR CEIL LO CB0; lia).
      carry CH MUt WMt ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      carry STA MUt WMt ltac:(clear -SPR CEIL LO T0 T1; lia).
      carry MTX MUt WMt ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
      carry REG MUt WMt ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
      carry HDR MUt WMt ltac:(subst HB; rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia).
      try carry MAGC MUt WMt ltac:(rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia).
      carry FR MUt WMt ltac:(clear -SPR CEIL LO; lia).
      carry SHU2 MUt WMt ltac:(clear -SPR CEIL LO SHHI SHB SHRZ GRS GR GR0 ABE SP1 HC KS0 RZ1; lia).
      carry STATS MUt WMt ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC5 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC4 | exact MUt | exact WMt |]; unfold AIMG_HI, AIMG_LO;
          apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC; lia |]; apply Forall_nil |]
      end.
      clear MC4 PC4 RC4 WMt. box MUt. try clear TI. try clear TK. try clear T88. try clear TSD. try clear CT. try clear ISB. try clear IREL. try clear ISE. try clear IPRE.
      lstep. lstep.                                            (* [comment removed for export] *)
      aload STATS 6 (al_t L + 2800 + 48).                      (* [comment removed for export] *)
      aload STATS 5 (al_t L + 2800 + 40).                      (* [comment removed for export] *)
      zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.           (* [comment removed for export] *)
      box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box FR. box SHU2.
      snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
      astore STATS 5.                                          (* [comment removed for export] *)
      astore STATS 6.                                          (* [comment removed for export] *)
      carry CBC MUs WMs ltac:(clear -SPR CEIL LO CB0 T1; lia).
      carry CH MUs WMs ltac:(rewrite LCH, CAE; clear -HC; lia).
      carry STA MUs WMs ltac:(clear; lia).
      carry MTX MUs WMs ltac:(rewrite RIE; ub TSP; clear -SP1 SP2 HC T0 T1 Y; lia).
      carry REG MUs WMs ltac:(rewrite RIE; ub TSP; clear -SP1 SP2 HC T0 T1 Y; lia).
      carry HDR MUs WMs ltac:(subst HB; rewrite ABE; ub TSP; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 T0 T1 Y; lia).
      try carry MAGC MUs WMs ltac:(rewrite ABE; ub TSP; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 T0 T1 Y; lia).
      carry FR MUs WMs ltac:(clear -SPR CEIL LO T1; lia).
      carry SHU2 MUs WMs ltac:(clear -SHLO SHHI SHB SHRZ GRS GR GR0 T0 T0k; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC6 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC5 | exact MUs | exact WMs |]; unfold AIMG_HI, AIMG_LO; ub TCX;
          apply Forall_cons; [cbn [fst snd]; clear -T0 T1 CX0 CX1 CXI TIC Y; lia |]; apply Forall_nil |]
      end.
      clear MC5. pose proof MC6 as MC6'. destruct MC6' as (_ & _ & _ & _ & _ & _ & _ & ISB & _).
      step. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K6; clear -K6 SP1 HC KS0; lia|].   (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      step. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K7; clear -K7 SP1 HC KS0; lia|].   (* [comment removed for export] *)
      zstep.                                                   (* [comment removed for export] *)
      step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K8; clear -K8 SP1 SP2 HC KS0 OFF RZ1; lia|].   (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      setreg 12 (Z_to_bv 64 c) ltac:(f_equal; rewrite ABE; replace (al_space_beg L + c * 4294967296 + kslot * S - al_space_beg L) with (c * 4294967296 + kslot * S) by (clear; lia);
                                  symmetry; apply class_of_offset; [clear -HC; lia| clear -OFF RZ1 KS0; lia]).
      step. step. step.                                        (* [comment removed for export] *)
      do 8 step.                                               (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MU0D : munch [(bv_unsigned sp - 112, bv_unsigned sp); (AB, AB + 8); (HB, HB + 4); (shad (AB + rz), shad (AB + rz) + granules n); (al_t L + 2800, al_t L + 3168)]%Z m mm)
      end.
      { unbox MUN. try unbox MUg. unbox MUh. unbox MUp. unbox MUt.
        eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR; lia)|].
        try (eapply munch_trans; [eapply munch_weaken; [| exact MUg]; solve_sub_fpw ltac:(clear; lia)|]).
        eapply munch_trans; [eapply munch_weaken; [| exact MUh]; solve_sub_fpw ltac:(clear; lia)|].
        eapply munch_trans; [eapply munch_weaken; [| exact MUp]; solve_sub_fpw ltac:(clear -SPR SHB SHUB GR; lia)|].
        eapply munch_trans; [eapply munch_weaken; [| exact MUt]; solve_sub_fpw ltac:(clear -SPR; lia)|].
        eapply munch_weaken; [| exact MUs]; solve_sub_fpw ltac:(clear; lia). }
      assert (WM0D : wmono bsegs m _) by (first [exact WM | eapply wmono_trans; [exact WM|]; eassumption]).
      assert (AZD : shad AB + shlen S <= shad (afreearr L c + mfa)).
      { rewrite <- shad_add_shlen by (clear -AB16; Z.div_mod_to_equations; lia). apply shad_mono. rewrite ABE, FAE. clear -KS1 MUB MFA NF. lia. }
      assert (ABFA : AB + S <= afreearr L c) by (rewrite ABE, FAE; clear -KS1 MUB; lia).
      assert (ABHI : AB + S <= al_space_beg L + 137438953472) by (rewrite ABE; clear -KS1 MUB HC; lia).
      pose proof MU0D as MU0E. rewrite SHUB in MU0E.
      assert (SHF2 : shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000) by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC MFA; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RECSD : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
        [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MU0E | exact WM0D |];
          cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; subst HB; ub TSP;
          clear -Hj SPR CEIL LO T0 T0k T1 K3 ABHI SZ RZ1 FIT N1 SHLO SHB SHHI SHRZ GRS GR0 Y; lia |];
        eapply junk_frame in J72; [| exact MU0E | exact WM0D | intros _; cbn [disjoint_from]; rewrite RIE; subst HB; ub TSP;
          clear -SPR CEIL LO SP1 SP2 HC ABHI SZ RZ1 FIT N1 SHHI GRS GR0 Y; lia];
        eapply junk_frame in FJ; [| exact MU0E | exact WM0D | intros _; cbn [disjoint_from]; subst HB; ub TSP;
          pose proof FAE as FAE'; clear -SPR CEIL LO SP1 SP2 HC ABFA SZ RZ1 FIT N1 SHHI GRS GR0 FAE' NF MFA Y; lia];
        assert (AZFD : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
        [ eapply azero_frame; [exact AZF | exact MU0E | exact WM0D |]; intros _; cbn [disjoint_from]; subst HB;
          clear -SPR CEIL LO T0 T0k SHLO SP1 K3 RZ1 SHF2 AZD GRS GR0 SHRZ MFA; lia |]
      end.
      clear MU0E.
      apply evtF_done.
      eapply cdealloc_spec with (lo := lo) (L := L) (chunks := chunks) (sta := sta) (P := AB);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC6
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => exact RECSD
       | |- forall j, _ -> _ => exact CNTS
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LCH | rewrite ?upd_length; exact LSJ]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZFD
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472; change (2^32) with 4294967296;
              clear KONT; fold nf mfa mu S AB; first [assumption | rewrite ?ABE, ?RBE; clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL KS0 OFF RZ1; lia]).
      (* [comment removed for export] *)
      intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CD.
      eapply KONT. unfold recyc1_ret. cbv zeta. fold S rz AB. fold HB.
      pose proof CD as CD0. unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP in CD0. cbv zeta in CD0. fold nf mfa in CD0.
      destruct CD0 as (FPLE & dr & mfa' & sjx & stax & _ & _ & _ & _ & NEWB & NEWGE & _ & MUD & WMD & _).
      eexists. split; [exact MU0D|]. split; [exact WM0D|]. split; [exact CD|].
      split. { intros Hrz. eapply cells_frame; [exact MAGC | exact MUD | exact WMD |].
               eapply cd_W_disjoint_user with (c' := c); unfold K_FREEARR_MAX, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472;
                 try (first [exact HC | exact T0 | unboxed TSP]); rewrite ?RBE, ?ABE; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                 clear -HC NF MFA NEWB NEWGE SP1 SP2 T0 CEIL LO KS0 KS1 MUB RZ1 FIT N1; lia. }
      split. { eapply cells_frame; [exact HDR | exact MUD | exact WMD |].
               eapply cd_W_disjoint_user with (c' := c); unfold K_FREEARR_MAX, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472;
                 try (first [exact HC | exact T0 | unboxed TSP]); subst HB; rewrite ?RBE, ?ABE; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                 clear -HC NF MFA NEWB NEWGE SP1 SP2 T0 CEIL LO KS0 KS1 MUB RZ1 FIT N1; lia. }
      rewrite <- GR. replace (AB + rz) with (HB + 16) by (subst HB; clear; lia).
      eapply cells_frame; [exact SHU2 | exact MUD | exact WMD |].
      eapply cd_W_disjoint_ushadow with (c' := c); unfold K_FREEARR_MAX, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
        try (first [exact HC | exact SP3 | exact T0]); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z2Nat.id by (clear -GR GR0; lia);
        try (clear -HC NF MFA NEWB NEWGE SP1 SP2 T0 CEIL LO; lia).
      + rewrite SHB. transitivity (shad AB); [apply shad_mono; rewrite ABE, RBE; clear -KS0; lia| clear -SHRZ; lia].
      + rewrite ?Nat.add_0_r. rewrite ?Z2Nat.id by (clear -GR GR0; lia). rewrite ?SHB, ?GR.
        pose proof (shad_add_shlen AB S ltac:(clear -AB16; Z.div_mod_to_equations; lia)) as E1.
        assert (M2 : shad (AB + S) <= shad (aregion L c + 3758096384)) by (apply shad_mono; rewrite ABE, RBE; clear -KS1 MUB; lia).
        clear -E1 M2 GRS GR GR0. lia.
    - (* [comment removed for export] *)
      assert (E16 : rz = 16) by (clear -RZ16x RZ1; lia).
      step. if_cases K5; zify_cond K5; rewrite ?unsigned_lit in K5 by (subst HB; rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [| exfalso; subst HB; clear -K5 E16; lia].   (* [comment removed for export] *)
      clear MAG'.
      clear PC RC TI TK T88 TSD CT ISB IREL ISE IPRE. box MUN. rename MC1 into MC2.
      (* [comment removed for export] *)
      zstep. zstep. step. step.                                (* [comment removed for export] *)
      change 18446744073709551612 with (2^64 - 2^2). rewrite land_align_down by (subst HB; rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia).
      replace (HB - HB mod 2 ^ 2) with HB by (clear -HB16; Z.div_mod_to_equations; lia).
      zstep. zstep.                                            (* [comment removed for export] *)
      replace ((Z.shiftl HB 3 mod 18446744073709551616) mod 32) with 0 by (rewrite Z.shiftl_mul_pow2 by (clear; lia); clear -HB16; Z.div_mod_to_equations; lia).
      change (bv_swrap 32 (Z.shiftl 255 0)) with 255. change (bv_swrap 32 (Z.shiftl 3 0)) with 3.
      apply (rw_hdr_to_C4 _ _ 3 b1 _ ltac:(clear; lia) ltac:(exact B1)) in HDR.
      assert (AMOW : amo_aligned AW (Z_to_bv 64 HB) = true) by (apply amo_alignedW_intro; [subst HB; rewrite ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia| clear -HB16; Z.div_mod_to_equations; lia]).
      amo_stepA AMOW. rewrite sx32_lit by (clear -B1; lia).   (* [comment removed for export] *)
      zstep. rewrite (byte0_of_word 3 b1) by (clear -B1; lia).   (* [comment removed for export] *)
      step. if_lit.                                            (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      rewrite (byte0_cas 3 0 b1) by (clear -B1; lia).
      box SHU. box STATS. box CBC. box CH. box STA. box MTX. box REG. box FR. try box MAGC. try box MUg.
      snapshot [(HB, HB + 4)]%Z MUh WMh.
      amo_stepA AMOW.                                          (* [comment removed for export] *)
      carry SHU MUh WMh ltac:(subst HB; clear -SHHI SHUB RZ1 SP1 HC KS0 ABE GRS GR0; lia).
      carry STATS MUh WMh ltac:(subst HB; rewrite LSJ, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry CBC MUh WMh ltac:(subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CB0 SPR CEIL LO; lia).
      carry CH MUh WMh ltac:(subst HB; rewrite LCH, CAE, ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry STA MUh WMh ltac:(subst HB; rewrite ABE; ub TSP; clear -SP1 SP2 HC OFF KS0 RZ1 T0 T1 Y; lia).
      carry MTX MUh WMh ltac:(subst HB; rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry REG MUh WMh ltac:(subst HB; rewrite ABE, RIE; clear -SP1 SP2 HC OFF KS0 KS1 MUB RZ1; lia).
      carry FR MUh WMh ltac:(subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 SPR CEIL LO; lia).
      try carry MAGC MUh WMh ltac:(subst HB; clear -RZBIG RZ16; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC3 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC2 | exact MUh | exact WMh |]; unfold AIMG_HI, AIMG_LO; ub SCX;
          apply Forall_cons; [cbn [fst snd]; subst HB; rewrite ABE; clear -SP1 SP2 HC OFF KS0 RZ1 CX0 CX1 CXI TIC Y; lia |]; apply Forall_nil |]
      end.
      clear MC2.
      step. if_lit.                                            (* [comment removed for export] *)
      apply (rw_C4_to_hdr _ _ 0 b1 _ ltac:(clear; lia) ltac:(exact B1)) in HDR.
      lstep. lstep.                                            (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      rewrite Z.lor_0_l.
      zstep. zstep.                                            (* [comment removed for export] *)
      setreg 11 (Z_to_bv 64 (rup n 8)) ltac:(change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -N1 FIT SZ RZ1; lia); unfold rup; f_equal; clear -N1; Z.div_mod_to_equations; lia).
      step.                                                    (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (SHU' : rw_cells bsegs mm (shad (HB + 16)) [CB (Z.to_nat (shlen (rup n 8))) shj]) by (rewrite GR; replace (HB + 16) with (AB + rz) by (subst HB; clear; lia); exact SHU)
      end.
      pose proof MC3 as MC3'. destruct MC3' as (PC3 & _).
      box STATS. box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box MUh. box FR.
      snapshot [(bv_unsigned sp + -48 - 64, bv_unsigned sp + -48); (shad (HB + 16), shad (HB + 16) + shlen (rup n 8))]%Z MUp WMp.
      (* [comment removed for export] *)
      clear SHU. box SHU'. box ST.
      assert (RG1 : rng RNG lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) - lo))
        by (rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub; [exact RSTK | clear; lia | clear -CEIL LO; lia]).
      assert (RG2 : rng RNG (shad (HB + 16)) (shlen (rup n 8))) by (rewrite SHB; eapply rng_sub; [exact RSAB | clear -SHRZ; lia | rewrite GR; clear -GRS SHRZ; lia]).
      step. call_sp (poison_shadow_spec RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (HB + 16) (rup n 8) 250 lo shj);
        [ unboxed ST | atop_facts; exact CEIL | clear -LO; lia | assumption | exact PC3 | reflexivity | reflexivity | reflexivity
        | clear -HB16; Z.div_mod_to_equations; lia | exact RUP8 | clear -RUPN N1; lia
        | unfold ablk; right; subst HB; rewrite ABE; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 RUPN FIT N1; lia
        | pose proof atop_range as AR; subst HB; rewrite ABE; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 RUPN FIT N1 AR; lia
        | clear; lia | intros; discriminate | unboxed SHU' | ].
      clear ST SHU' RG1 RG2.
      rename PC into ST. rename POST into SHU2. try rename MI0 into MI.
      carry STATS MUp WMp ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T0k T1 SHLO SHHI SHB SHRZ GRS GR ABE SP1 HC KS0 RZ1; lia).
      carry CBC MUp WMp ltac:(clear -SPR CEIL LO CB0 CB1 SHHI SHB SHRZ GRS GR ABE SP1 SP2 HC KS0 RZ1; lia).
      carry CH MUp WMp ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T0k T1 SHLO HC SHHI SHB SHRZ GRS GR ABE SP1 KS0 RZ1; lia).
      carry STA MUp WMp ltac:(clear -SPR CEIL LO T0 T0k T1 SHLO SHHI SHB SHRZ GRS GR ABE SP1 HC KS0 RZ1; lia).
      carry MTX MUp WMp ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 RZ1; lia).
      carry REG MUp WMp ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 RZ1; lia).
      carry HDR MUp WMp ltac:(subst HB; clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 KS1 MUB RZ1 FIT N1; lia).
      try carry MAGC MUp WMp ltac:(clear -SPR CEIL LO SP1 SP2 HC SHHI SHB SHRZ GRS GR ABE KS0 KS1 MUB RZ1 FIT N1; lia).
      carry FR MUp WMp ltac:(clear -SPR CEIL LO SHHI SHB SHRZ GRS GR ABE SP1 SP2 HC KS0 RZ1; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC4 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC3 | exact MUp | exact WMp |]; unfold AIMG_HI, AIMG_LO;
          apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC; lia |];
          apply Forall_cons; [cbn [fst snd]; clear -SHLO SHHI SHB SHRZ GRS GR CX0 CXk; lia |]; apply Forall_nil |]
      end.
      clear MC3 PC3 WMp. box MUp.
      pose proof MC4 as MC4'. destruct MC4' as (PC4 & RC4 & TI & TK & T88 & TSD & CT & ISB & IREL & ISE & IPRE).
      (* [comment removed for export] *)
      box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box FR. box SHU2. box STATS.
      snapshot [(bv_unsigned sp + -48 - 32, bv_unsigned sp + -48)]%Z MUt WMt.
      (* [comment removed for export] *)
      box ST. box TI. box TK. box T88. box TSD. box CT. box ISB. box IREL. box ISE. box IPRE.
      assert (RG1 : rng RNG lo (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) - lo))
        by (rewrite unsigned_lit by (clear -SPR CEIL LO; lia); eapply rng_sub; [exact RSTK | clear; lia | clear -CEIL LO; lia]).
      step. call_sp (thread_stats_spec RNG (al_ctx L) (al_t L) lo);
        [ unboxed ST | atop_facts; exact CEIL | clear -LO; lia | assumption | exact TP | unboxed TI | unboxed TK | unboxed T88 | unboxed TSD | unboxed CT
        | clear -CXI; unfold AIMG_HI in *; lia | atop_facts; exact CX1 | exact TIC | atop_facts; exact T1 | ].   (* [comment removed for export] *)
      clear ST TI TK T88 TSD CT ISB IREL ISE IPRE RG1.
      rename POST into ST. try rename MI0 into MI.
      carry CBC MUt WMt ltac:(clear -SPR CEIL LO CB0; lia).
      carry CH MUt WMt ltac:(rewrite LCH, CAE; clear -SPR CEIL LO T0 T1 HC; lia).
      carry STA MUt WMt ltac:(clear -SPR CEIL LO T0 T1; lia).
      carry MTX MUt WMt ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
      carry REG MUt WMt ltac:(rewrite RIE; clear -SPR CEIL LO SP1 SP2 HC; lia).
      carry HDR MUt WMt ltac:(subst HB; rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia).
      try carry MAGC MUt WMt ltac:(rewrite ABE; clear -SPR CEIL LO SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1; lia).
      carry FR MUt WMt ltac:(clear -SPR CEIL LO; lia).
      carry SHU2 MUt WMt ltac:(clear -SPR CEIL LO SHHI SHB SHRZ GRS GR GR0 ABE SP1 HC KS0 RZ1; lia).
      carry STATS MUt WMt ltac:(rewrite LSJ; clear -SPR CEIL LO T0 T1; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC5 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC4 | exact MUt | exact WMt |]; unfold AIMG_HI, AIMG_LO;
          apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 CXI TIC; lia |]; apply Forall_nil |]
      end.
      clear MC4 PC4 RC4 WMt. box MUt. try clear TI. try clear TK. try clear T88. try clear TSD. try clear CT. try clear ISB. try clear IREL. try clear ISE. try clear IPRE.
      lstep. lstep.                                            (* [comment removed for export] *)
      aload STATS 6 (al_t L + 2800 + 48).                      (* [comment removed for export] *)
      aload STATS 5 (al_t L + 2800 + 40).                      (* [comment removed for export] *)
      zstep. zstep. rewrite Z.lor_0_l. zstep. zstep.           (* [comment removed for export] *)
      box CBC. box CH. box STA. box MTX. box REG. box HDR. try box MAGC. box FR. box SHU2.
      snapshot [(al_t L + 2800, al_t L + 3168)]%Z MUs WMs.
      astore STATS 5.                                          (* [comment removed for export] *)
      astore STATS 6.                                          (* [comment removed for export] *)
      carry CBC MUs WMs ltac:(clear -SPR CEIL LO CB0 T1; lia).
      carry CH MUs WMs ltac:(rewrite LCH, CAE; clear -HC; lia).
      carry STA MUs WMs ltac:(clear; lia).
      carry MTX MUs WMs ltac:(rewrite RIE; ub TSP; clear -SP1 SP2 HC T0 T1 Y; lia).
      carry REG MUs WMs ltac:(rewrite RIE; ub TSP; clear -SP1 SP2 HC T0 T1 Y; lia).
      carry HDR MUs WMs ltac:(subst HB; rewrite ABE; ub TSP; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 T0 T1 Y; lia).
      try carry MAGC MUs WMs ltac:(rewrite ABE; ub TSP; clear -SP1 SP2 HC KS0 KS1 MUB RZ1 FIT N1 T0 T1 Y; lia).
      carry FR MUs WMs ltac:(clear -SPR CEIL LO T1; lia).
      carry SHU2 MUs WMs ltac:(clear -SHLO SHHI SHB SHRZ GRS GR GR0 T0 T0k; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MC6 : m3_cells L mm);
        [ eapply m3_cells_frame; [exact MC5 | exact MUs | exact WMs |]; unfold AIMG_HI, AIMG_LO; ub TCX;
          apply Forall_cons; [cbn [fst snd]; clear -T0 T1 CX0 CX1 CXI TIC Y; lia |]; apply Forall_nil |]
      end.
      clear MC5. pose proof MC6 as MC6'. destruct MC6' as (_ & _ & _ & _ & _ & _ & _ & ISB & _).
      step. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K6; clear -K6 SP1 HC KS0; lia|].   (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      step. if_cases K7; zify_cond K7; rewrite ?unsigned_lit in K7 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K7; clear -K7 SP1 HC KS0; lia|].   (* [comment removed for export] *)
      zstep.                                                   (* [comment removed for export] *)
      step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (rewrite ?ABE; clear -SP1 SP2 HC OFF RZ1 KS0; lia); [exfalso; rewrite ABE in K8; clear -K8 SP1 SP2 HC KS0 OFF RZ1; lia|].   (* [comment removed for export] *)
      step.                                                    (* [comment removed for export] *)
      zstep. zstep. zstep.                                     (* [comment removed for export] *)
      setreg 12 (Z_to_bv 64 c) ltac:(f_equal; rewrite ABE; replace (al_space_beg L + c * 4294967296 + kslot * S - al_space_beg L) with (c * 4294967296 + kslot * S) by (clear; lia);
                                  symmetry; apply class_of_offset; [clear -HC; lia| clear -OFF RZ1 KS0; lia]).
      step. step. step.                                        (* [comment removed for export] *)
      do 8 step.                                               (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      (* [comment removed for export] *)
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (MU0D : munch [(bv_unsigned sp - 112, bv_unsigned sp); (AB, AB + 8); (HB, HB + 4); (shad (AB + rz), shad (AB + rz) + granules n); (al_t L + 2800, al_t L + 3168)]%Z m mm)
      end.
      { unbox MUN. try unbox MUg. unbox MUh. unbox MUp. unbox MUt.
        eapply munch_trans; [eapply munch_weaken; [| exact MUN]; solve_sub_fpw ltac:(clear -SPR; lia)|].
        try (eapply munch_trans; [eapply munch_weaken; [| exact MUg]; solve_sub_fpw ltac:(clear; lia)|]).
        eapply munch_trans; [eapply munch_weaken; [| exact MUh]; solve_sub_fpw ltac:(clear; lia)|].
        eapply munch_trans; [eapply munch_weaken; [| exact MUp]; solve_sub_fpw ltac:(clear -SPR SHB SHUB GR; lia)|].
        eapply munch_trans; [eapply munch_weaken; [| exact MUt]; solve_sub_fpw ltac:(clear -SPR; lia)|].
        eapply munch_weaken; [| exact MUs]; solve_sub_fpw ltac:(clear; lia). }
      assert (WM0D : wmono bsegs m _) by (first [exact WM | eapply wmono_trans; [exact WM|]; eassumption]).
      assert (AZD : shad AB + shlen S <= shad (afreearr L c + mfa)).
      { rewrite <- shad_add_shlen by (clear -AB16; Z.div_mod_to_equations; lia). apply shad_mono. rewrite ABE, FAE. clear -KS1 MUB MFA NF. lia. }
      assert (ABFA : AB + S <= afreearr L c) by (rewrite ABE, FAE; clear -KS1 MUB; lia).
      assert (ABHI : AB + S <= al_space_beg L + 137438953472) by (rewrite ABE; clear -KS1 MUB HC; lia).
      pose proof MU0D as MU0E. rewrite SHUB in MU0E.
      assert (SHF2 : shad (afreearr L c + mfa) + shlen (536870912 - mfa) <= 0x10007fff8000) by (rewrite shad_div, shlen_div, FAE; unfold ASHOFF; clear -SP1 SP2 HC MFA; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        assert (RECSD : forall j, 1 <= j <= 31 -> arec_hdr L mm j (c_count (get_cls st j)) (max_count st j) (if a_cinit st then size_of_class j else 0));
        [ intros j Hj; unfold arec_hdr; eapply cells_frame; [exact (RECS j Hj) | exact MU0E | exact WM0D |];
          cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; subst HB; ub TSP;
          clear -Hj SPR CEIL LO T0 T0k T1 K3 ABHI SZ RZ1 FIT N1 SHLO SHB SHHI SHRZ GRS GR0 Y; lia |];
        eapply junk_frame in J72; [| exact MU0E | exact WM0D | intros _; cbn [disjoint_from]; rewrite RIE; subst HB; ub TSP;
          clear -SPR CEIL LO SP1 SP2 HC ABHI SZ RZ1 FIT N1 SHHI GRS GR0 Y; lia];
        eapply junk_frame in FJ; [| exact MU0E | exact WM0D | intros _; cbn [disjoint_from]; subst HB; ub TSP;
          pose proof FAE as FAE'; clear -SPR CEIL LO SP1 SP2 HC ABFA SZ RZ1 FIT N1 SHHI GRS GR0 FAE' NF MFA Y; lia];
        assert (AZFD : azero mm (shad (afreearr L c + mfa)) (shlen (536870912 - mfa)));
        [ eapply azero_frame; [exact AZF | exact MU0E | exact WM0D |]; intros _; cbn [disjoint_from]; subst HB;
          clear -SPR CEIL LO T0 T0k SHLO SP1 K3 RZ1 SHF2 AZD GRS GR0 SHRZ MFA; lia |]
      end.
      clear MU0E.
      apply evtF_done.
      eapply cdealloc_spec with (lo := lo) (L := L) (chunks := chunks) (sta := sta) (P := AB);
      try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => assumption
       | |- iclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- m3_cells _ _ => exact MC6
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => exact RECSD
       | |- forall j, _ -> _ => exact CNTS
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact J72
       | |- junk_at _ _ _ => exact FJ
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- length _ = _ => first [exact LCH | rewrite ?upd_length; exact LSJ]
       | |- Forall _ _ => exact CH31
       | |- azero _ _ _ => exact AZFD
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ _ _ => solve_rng
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
      all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472; change (2^32) with 4294967296;
              clear KONT; fold nf mfa mu S AB; first [assumption | rewrite ?ABE, ?RBE; clear -NF MFA MFAM NFN HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL KS0 OFF RZ1; lia]).
      (* [comment removed for export] *)
      intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CD.
      eapply KONT. unfold recyc1_ret. cbv zeta. fold S rz AB. fold HB.
      pose proof CD as CD0. unfold cdealloc_ret, K_FREEARR_MAX, K_FREEARR_MAP in CD0. cbv zeta in CD0. fold nf mfa in CD0.
      destruct CD0 as (FPLE & dr & mfa' & sjx & stax & _ & _ & _ & _ & NEWB & NEWGE & _ & MUD & WMD & _).
      eexists. split; [exact MU0D|]. split; [exact WM0D|]. split; [exact CD|].
      split. { intros Hrz. exfalso. clear -Hrz E16. lia. }
      split. { eapply cells_frame; [exact HDR | exact MUD | exact WMD |].
               eapply cd_W_disjoint_user with (c' := c); unfold K_FREEARR_MAX, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472;
                 try (first [exact HC | exact T0 | unboxed TSP]); subst HB; rewrite ?RBE, ?ABE; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                 clear -HC NF MFA NEWB NEWGE SP1 SP2 T0 CEIL LO KS0 KS1 MUB RZ1 FIT N1; lia. }
      rewrite <- GR. replace (AB + rz) with (HB + 16) by (subst HB; clear; lia).
      eapply cells_frame; [exact SHU2 | exact MUD | exact WMD |].
      eapply cd_W_disjoint_ushadow with (c' := c); unfold K_FREEARR_MAX, K_FREEARR_OFF, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
        try (first [exact HC | exact SP3 | exact T0]); cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z2Nat.id by (clear -GR GR0; lia);
        try (clear -HC NF MFA NEWB NEWGE SP1 SP2 T0 CEIL LO; lia).
      + rewrite SHB. transitivity (shad AB); [apply shad_mono; rewrite ABE, RBE; clear -KS0; lia| clear -SHRZ; lia].
      + rewrite ?Nat.add_0_r. rewrite ?Z2Nat.id by (clear -GR GR0; lia). rewrite ?SHB, ?GR.
        pose proof (shad_add_shlen AB S ltac:(clear -AB16; Z.div_mod_to_equations; lia)) as E1.
        assert (M2 : shad (AB + S) <= shad (aregion L c + 3758096384)) by (apply shad_mono; rewrite ABE, RBE; clear -KS1 MUB; lia).
        clear -E1 M2 GRS GR GR0. lia. }
  step. step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -HC; lia).   (* [comment removed for export] *)
  { step. step.                                                (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 S : word) ltac:(subst S; rewrite K31; reflexivity). apply TAIL. }
  step. step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -HC; lia).   (* [comment removed for export] *)
  { do 9 zstep.                                                (* [comment removed for export] *)
    setreg 15 (Z_to_bv 64 S : word) ltac:(subst S; symmetry; apply size_formula2; clear -K17 K31 HC; lia).
    apply TAIL. }
  step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -HC; lia); [exfalso; clear -K0 HC; lia|].   (* [comment removed for export] *)
  zstep. step.                                                 (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 S : word)
    ltac:(subst S; unfold size_of_class; replace (c <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); rewrite Z.shiftl_mul_pow2 by (clear; lia); apply Z_to_bv_eqm; rewrite ?Z.mod_small by (clear -HC; lia); clear -HC; Z.div_mod_to_equations; lia).
  apply TAIL.
Qed.
End CANSEC3.
