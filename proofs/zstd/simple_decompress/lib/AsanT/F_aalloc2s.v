(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanCtrlProps AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AKit2 AModelFacts APrimFacts ASecFacts
     ADepot_iface ARep ARepFrame F_ammap F_apoison F_apoison0 APoisonR_iface F_aalloc2 F_aalloc2g.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTier0U.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTuningK.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_tier0u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.tlia ::= tlia_u.
Local Ltac OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib.StoreFast.lia3 ::= lia3_u.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::=
  first [ zify_prune_relevant_nog; zify_noeuclid_nosat; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. destruct HP as ([lo' hi'] & HI & [H1 H2]). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_find8s X tac := first [ lazymatch goal with |- Exists _ ((?lo', _) :: _) => let Y := leftmost lo' in constr_eq X Y end; apply Exists_cons_hd; cbn [fst snd]; split; tac
                                    | apply Exists_cons_tl; fp_find8s X tac ].
Local Ltac fp_piece8 :=
  first [ lazymatch goal with |- (_ <= ?lo)%Z \/ _ => let X := leftmost lo in right; first [ fp_find8s X ltac:(fp_cheap8) | fp_find8s X ltac:(lia) ] end
        | left; fp_cheap8 | right; fp_find8c | right; fp_find8 ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; fp_piece8 | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
  repeat match goal with E : shad _ = _ |- _ => rewrite E in MU end;   (* [comment removed for export] *)
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ (* [comment removed for export] *)
              lazymatch W with context [(Z.sub (bv_unsigned ?s0) (Zpos _), bv_unsigned ?s0)] => assert_succeeds (assert (bv_unsigned s0 = hiq) by fp_cheap8) end; clear H
            | apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148256256 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
Lemma gaas_sec_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a SB ms needed idx : Z),
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 SB)] ->                         (* [comment removed for export] *)
  rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] ->                       (* [comment removed for export] *)
  rw_cells bsegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 needed); C8 (Z_to_bv 64 idx)] ->   (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= needed <= ms -> 8192 <= ms -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) ->
  rng_aimg RNG -> rng RNG a 32 ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) s1
                    (Z_to_bv 64 4096) (Z_to_bv 64 (needed + 4095)) (Z_to_bv 64 needed) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33f74) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ee4) fc None m (seg_rom bsegs)).
Proof.
  intros until idx. intros I32 I64 HDR AL LO HI ND MS SB0 SBH DJ RIMG RA. pose proof (ablk_lin _ _ LO) as (ALO & AZ0 & _ & _).   (* [comment removed for export] *)
  unfold AINSTANCE in *.
  pose proof HDR as HDR0. rw_split HDR0 2%nat HDRa HDRb. rw_split HDRb 1%nat HDRs HDRc. clear HDRa HDRc.
  replace (a + Z.of_nat (cells_size [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms)])) with (a + 16) in HDRs by (cbn; lia).
  lstep.                                                         (* [comment removed for export] *)
  step. if_cases K0; zify_cond K0.                               (* [comment removed for export] *)
  2: step; zstep; zstep; step; if_cases K1; zify_cond K1.        (* [comment removed for export] *)
  3: { exfalso. clear -K0 K1 DJ ND ALO HI AL MS; lia. }
  (* [comment removed for export] *)
  all: lstep.                                                    (* [comment removed for export] *)
  all: zstep; zstep.                                             (* [comment removed for export] *)
  all: step; if_cases K2; [zify_cond K2| clear K2].              (* [comment removed for export] *)
  1,3: exfalso; apply K2; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by lia; change (2^12) with 4096; clear -AL; Z.div_mod_to_equations; lia.
  all: zstep; step; if_lit.                                      (* [comment removed for export] *)
  all: zstep.                                                    (* [comment removed for export] *)
  all: setreg 12 (Z_to_bv 64 a) ltac:(f_equal; lia).
  all: lstep.                                                    (* [comment removed for export] *)
  all: zstep; zstep; zstep.                                      (* [comment removed for export] *)
  all: setreg 8 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) ltac:(rewrite land_align4096 by lia; f_equal; clear -ND MS HI ALO; Z.div_mod_to_equations; lia).
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wpiece_ok (iv : Z * Z) : Prop := AIMG_HI <= fst iv \/ (0x1a1bc8 <= fst iv /\ snd iv <= 0x5f1c10).

Lemma disjoint_img2 : forall W A n, Forall wpiece_ok W -> 0 <= n ->
  (A + n <= 0x1a1bc8 \/ (0x5f1c10 <= A /\ A + n <= AIMG_HI)) -> disjoint_from W A n.
Proof.
  intros W A n HW Hn HA. unfold wpiece_ok, AIMG_HI in *. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH].
Qed.

Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' -> Forall wpiece_ok W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold poison_cells in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]).
Qed.

Lemma premap_cells_frame2 : forall m m' W,
  premap_cells m -> munch W m m' -> wmono bsegs m m' -> Forall wpiece_ok W -> premap_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold premap_cells in *. destruct PC as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]) ].
Qed.

Lemma arelro_frame2 : forall m m' W,
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) -> munch W m m' -> Forall wpiece_ok W ->
  forall i, ARELRO_LO <= i < ARELRO_HI -> m' (wa i) = None.
Proof.
  intros m m' W RR MU HW i Hi. rewrite <- (RR i Hi). pose proof (MU (wa i)) as E.
  unfold ARELRO_LO, ARELRO_HI in Hi. rewrite wa_unsigned in E by lia. apply E.
  eapply disjoint_outside with (a := i) (n := 1); [| lia]. apply disjoint_img2; [exact HW| lia| unfold AIMG_HI; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_lnot7_eq : forall n, 0 <= n -> Z.land n (Z.lnot 7) = n - n mod 8.
Proof.
  intros n Hn. rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
Qed.

Section WithDepot.
Variable DI : ADepotIface.
(* [comment removed for export] *)
Hypothesis PR : poison_remap_stmt.

(* [comment removed for export] *)
Notation allocBC_WS L sp a ms :=
  ([(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (a + 6128, a + 6144);
    (shad a + 512, shad a + ms / 8);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocBC_postS (L : alayout) (RNG : footprint) (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t a ms lo : Z) (m : amem) (RNG' : footprint) (m' : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 t3 t4 t5 t6,
    let AB := a + 4096 in let UB := a + 6144 in
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 AB) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x34054) fc None m' (seg_rom bsegs)
    /\ fp_le RNG RNG'
    /\ munch (allocBC_WS L sp a ms) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells bsegs m' (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (hdr_b1_mid 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
       (* [comment removed for export] *)
    /\ fill_at m' (shad a + 512) 256 0xfa
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))])
    /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
    /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

Lemma allocBC_sec : forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t a ms idx SB lo sz pc : Z) (tb : list word) (tr : list Z) (fr0 : list byte)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  stk bsegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= al_ctx L \/ al_ctx L + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells bsegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells bsegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 idx)] ->
  rw_cells bsegs m (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (shad AB) [CB 256 (repeat (Z_to_bv 8 0) 256)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))] ->
  (n mod 8 <> 0 -> rw_cells bsegs m (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]) ->
  (exists junk, rw_cells bsegs m (shad UB + granules n) [CB (Z.to_nat (ms / 8 - 768 - granules n)) junk]) ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0xcd54d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 SB)] -> rw_cells bsegs m 0xcc6d8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP ->
  sclr t 4096 -> sclr (al_ctx L) 65536 -> sclr (al_nodes L) 1048576 -> sclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  (* [comment removed for export] *)
  (forall RNG' m' id rax t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6',
     allocBC_postS L RNG sp gp tp F fc n S t a ms lo m RNG' m'
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x34054) fc None m' (seg_rom bsegs)) ->
     0 < id < 2^31 ->
     implS bsegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x34054) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33da8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33da8) fc None m (seg_rom bsegs)).
Proof.
  intros until s11v. cbv zeta.
  intros ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS FR HDRP HDR SHL SHU SHP [junkT SHT] PC PMC RELRO PP I32 I64
         CT8 TT0 CX0 CX1 T0 T1 SHT0 SHC SHN SHS SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1
         RIMG RSTK RS RNO RST RCTX RT RA RSA KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AREQMAX in *.
  pose proof (sec_facts n ltac:(unfold AREQMAX; clear -N; lia) PRIM) as (NB & RZ & RSE & RSR & RSM & NSE & MSE & MSR & MSM & MSB). rewrite <- HMS in MSE, MSR, MSM, MSB.
  word_range sp SPR.
  destruct PC as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7).
  rewrite (land_lnot7_eq n) by (clear -N; lia).
  (* [comment removed for export] *)
  pose proof (ablk_lin _ _ ALO) as (ALO1 & AZ0 & _ & _). unfold AIMG_HI in ALO1.   (* [comment removed for export] *)
  destruct (ablk_int _ _ ALO) as (kA & ABND & ABNDa & ABNDb & ABNDc & ABNDd).        (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768 /\ 0x800bca00 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1 /\ 768 + granules n + 256 <= ms / 8
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -AAL ABND ABNDa ABNDb ABNDc ABNDd AHI N RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9).
  destruct (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) as (kS & ASD & ASDa & ASDb & _ & _).   (* [comment removed for export] *)
  destruct (sclr_int _ _ SHN ltac:(clear -N0; unfold AIMG_HI in *; lia) ltac:(clear -N1; lia)) as (kN & NBND & NBNDa & NBNDb).   (* [comment removed for export] *)
  destruct (sclr_int _ _ SHS ltac:(clear -R0; unfold AIMG_HI in *; lia) ltac:(clear -R1; lia)) as (kR & SBND & SBNDa & SBNDb).
  pose proof (munch_refl (allocBC_WS L sp a ms) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  box TT0. box CT8. box DJT. box DJC. box DJN. box DJS. box DJSB.
  box SHP. box PMC.
  iprefix.
  snapshot [(a + 6128, a + 6144)]%Z MUh WMh.
  (* [comment removed for export] *)
  snapshot [(bv_unsigned sp + -128 - ADEPOT_STACK, bv_unsigned sp + -128); (a + 6128, a + 6144); (shad a + 512, shad a + 768);
            (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z MUq WMq.
  step. step. if_cases K0; zify_cond K0. { exfalso. clear -K0 ALO AHI MSR NSE RSR ALO1; lia. }     (* [comment removed for export] *)
  zstep. rewrite RZ. setreg 20 (Z_to_bv 64 (a + 6144)) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  zstep. zstep.                                                   (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.                                (* [comment removed for export] *)
  2: { exfalso. apply K1. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. clear -AAL. Z.div_mod_to_equations. lia. }
  zstep.                                                          (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 NSE RSR MSR AHI ALO N ALO1; lia. }   (* [comment removed for export] *)
  lstep.                                                         (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  rewrite (Z.shiftr_eq_0 n 32) by (try lia; apply Z.log2_lt_pow2; lia).
  rewrite (Z.shiftr_eq_0 n 48) by (try lia; apply Z.log2_lt_pow2; lia).
  sstep. step. step.                                             (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. zstep.                                     (* [comment removed for export] *)
  sstep.                                                         (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. clear -K3 T0 SHT0; lia. }   (* [comment removed for export] *)
  carry TT0 MUh WMh ltac:(with_box DJT lia).
  step.                                                          (* [comment removed for export] *)
  carry CT8 MUh WMh ltac:(with_box DJC lia).
  lstep. zstep. step.                                            (* [comment removed for export] *)
  step. step.                                                    (* [comment removed for export] *)
  clear TT0 CT8.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEP' : ADEPOT DI L mm) end.
  { eapply (adi_frame DI); [exact DEP | exact MUh | exact WMh |].
    apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
    intros x Hx. pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2. clear -Hx X1 X2 SHN SHS ALO MSB ALO1. lia. }
  clear MUh WMh. box HDR. box HDRP.
  box SHL. box SHU. box SHT.          (* [comment removed for export] *)
  box FR. box PC1. box PC2. box PC3. box PC4. box PC5. box PC6. box PC7. box PP. box I32. box I64.   (* [comment removed for export] *)
  snapshot (adepot_W L (bv_unsigned sp + -128)) MUd WMd.
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ = 1 + _ => exact SZ
       | |- u64arr _ _ _ _ => exact TB
       | |- length _ = _ => exact LTB
       | |- map _ _ = _ => exact TRF
       | |- In _ _ => exact TRU
       | |- ADEPOT _ _ _ => exact DEP'
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- _ => unfold AIMG_HI; clear -SPR CEIL LO SPS S47 SZB N0 N1 R0 R1 SHN SHS CX0 CX1 T0 T1; lia
       end.
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-DEPOT" G end.
  (* [comment removed for export] *)
  lazymatch goal with H : 0 < ?i < 2 ^ 31 |- _ => rename H into IDR end.
  lazymatch goal with H : ADEPOT DI L _ |- _ => rename H into DEP2 end.
  snapshot [(bv_unsigned sp + -128 - 592, bv_unsigned sp + -128); (a + 6128, a + 6144); (shad a + 512, shad a + ms / 8)]%Z MUp WMp.
  carry HDR MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; clear -X1 X2 SPR CEIL LO AHI ALO SHN SHS MSB ALO1; lia).
  carry HDRP MUd WMd ltac:(pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2; clear -X1 X2 SPR CEIL LO AHI ALO SHN SHS MSB ALO1; lia).
  carry FR MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PP MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry I32 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry I64 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC1 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC2 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC3 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC4 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC5 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia). carry PC6 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry PC7 MUd WMd ltac:(clear -SPR CEIL LO N0 N1 R0 R1; lia).
  carry SHL MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).   (* [comment removed for export] *)
  carry SHU MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).
  carry SHT MUd WMd ltac:(clear -SPR CEIL LO ALO1 AHI MSB SG1 SG2 SG3 SG4 SG5 SG7 NBND NBNDa NBNDb SBND SBNDa SBNDb N1 R1; dlia).
  clear MUd WMd.
  zstep. zstep. zstep.                                           (* [comment removed for export] *)
  rewrite Z.lor_0_l. rewrite (Z.mod_small x 4294967296) by lia.
  step.                                                          (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (gaas_sec_spec RNG).
    all: try lazymatch goal with
         | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
         | |- rw_cells _ _ _ _ => first [exact I32 | exact I64 | exact HDRP]
         | |- rng_aimg _ => exact RIMG
         | |- rng _ _ _ => eapply rng_sub'; [exact RA|]; clear -MSB; lia
         | |- _ \/ _ => unboxed DJSB
         | |- _ => atop_facts; clear -AAL ALO AHI N NSE RSR MSR MSE MSB SB0 SBH ALO1; lia
         end.
    all: match goal with |- ?G => idtac "REM-GAAS" G end. }
  cbv beta. intros msG ->.
  setreg 8 (Z_to_bv 64 (ms - 4096)) ltac:(f_equal; clear -MSE; lia).
  (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  setreg 22 (Z_to_bv 64 (a + 6144 + 8 * granules n)) ltac:(f_equal; change 18446744073709551608 with (2^64 - 2^3); rewrite land_align_down by (clear -ALO AHI N NSE RSR MSR ALO1; lia); change (2^3) with 8; rewrite SG9; clear -N AAL; Z.div_mod_to_equations; lia).
  zstep. step. step.                                             (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 2048) ltac:(f_equal; clear; lia).
  rewrite SG1 in SHL.
  step. call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096) 2048 256 250 lo (repeat (Z_to_bv 8 0) 256)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG1; exact SHL
       | |- shlen _ = _ => reflexivity
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => first [solve_rng | rewrite SG1; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB N ALO1; first [lia | Z.div_mod_to_equations; lia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; Z.div_mod_to_equations; lia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | Z.div_mod_to_equations; lia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-P1" G end.
  rename POST into ST.
  lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHL' end.
  rewrite SG1 in SHL'.
  (* [comment removed for export] *)
  zstep. zstep.                                                  (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (ms - 6144 - 8 * granules n)) ltac:(f_equal; clear -SG7 MSB SG5; Z.div_mod_to_equations; lia).
  step. step.                                                    (* [comment removed for export] *)
  assert (SGX : shad (a + 6144 + 8 * granules n) = shad a + 768 + granules n) by (rewrite !shad_div; clear -AAL SG9 N; Z.div_mod_to_equations; lia).
  assert (SLX : shlen (ms - 6144 - 8 * granules n) = ms / 8 - 768 - granules n) by (rewrite shlen_div; clear -MSM SG7; Z.div_mod_to_equations; lia).
  rewrite SG2 in SHU. rewrite SG2 in SHT.
  (* [comment removed for export] *)
  unbox SHP.
  destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
  1: clear SHP.
  2: specialize (SHP M0); rewrite SG2 in SHP; box SHP; carry SHP MUq WMq ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 SHN SHS ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; dlia);
     assert (GLT : shlen (n - n mod 8) + 1 = granules n) by (rewrite SG8, SG9; clear -M0 N; Z.div_mod_to_equations; lia).
  all: clear MUq WMq.
  all: step; call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        (a + 6144 + 8 * granules n) (ms - 6144 - 8 * granules n) (ms / 8 - 768 - granules n) 250 lo junkT).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SGX; exact SHT
       | |- shlen _ = _ => exact SLX
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => first [solve_rng | rewrite SGX; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSM SG5 SG7 N ALO1; first [lia | Z.div_mod_to_equations; lia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; Z.div_mod_to_equations; lia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | Z.div_mod_to_equations; lia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-P2" G end.
  all: rename POST into ST.
  all: lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHT' end.
  all: rewrite SGX in SHT'.
  (* [comment removed for export] *)
  all: step; zstep; zstep.                                       (* [comment removed for export] *)
  all: rewrite (land_align8_48 n) by (clear -N; lia).
  all: step; if_cases K4; [zify_cond K4; exfalso; clear -K4 NB N; Z.div_mod_to_equations; lia| clear K4].   (* [comment removed for export] *)
  all: step; step; step.                                         (* [comment removed for export] *)
  all: step.                                                     (* [comment removed for export] *)
  all: apply evtF_done.
  all: destruct (Z_lt_le_dec (shlen (n - n mod 8)) 65536) as [SM|BG].
  (* [comment removed for export] *)
  1,3: rewrite (poison0_small R (a + 6144) (n - n mod 8) k) by (first [clear -AAL; Z.div_mod_to_equations; lia | rewrite SG8 in SM; clear -SM N; Z.div_mod_to_equations; lia]).
  1,2: iprefix.
  1,2: call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (a + 6144) (n - n mod 8) (shlen (n - n mod 8)) 0 lo (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; exact SHU
       | |- shlen _ = _ => reflexivity
       | |- _ = 0 -> _ => intros _; exact SM
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- rng _ _ _ => first [solve_rng | rewrite SG2; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSM MSR NSE RSR SG5 SG7 N NB ALO1; first [lia | Z.div_mod_to_equations; lia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; Z.div_mod_to_equations; lia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | Z.div_mod_to_equations; lia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- implS _ _ _ _ _ => idtac | |- ?G => idtac "REM-P3m" G end.
  1,2: rename POST into ST.
  1,2: lazymatch goal with H : rw_cells _ _ (shad _) [CB _ (repeat _ _)] |- _ => rename H into SHU' end.
  1,2: rewrite SG2 in SHU'.
  1,2: pose proof (fp_le_refl RNG) as FPLE.
  1,2: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PMC' : premap_cells mm) end.
  1,3: eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
       repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil.
  (* [comment removed for export] *)
  3,4: eapply (PR R k Q RNG) with (lo := lo).
  all: try lazymatch goal with |- evtF _ _ _ _ => idtac | |- implS _ _ _ _ _ => idtac | |- forall RNG' m', _ => idtac
                            | |- _ => rewrite !(unsigned_lit (bv_unsigned sp + -128)) by (clear -SPR CEIL LO; lia) end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => eassumption
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- premap_cells _ => eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
                              repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil
       | |- forall i, _ -> _ = None => eapply arelro_frame2; [exact RELRO| exact MU|]; unfold wpiece_ok;
                              repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; exact SHU
       | |- _ <= shlen _ => exact BG
       | |- forall RNG' m', _ => idtac
       end.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- forall RNG' m', _ => idtac
       | |- rng _ _ _ => first [solve_rng | rewrite SG2; eapply rng_sub'; [exact RSA|]; clear -SG7 SG5; lia]
       | |- _ => unfold PZR_STACK; clear -SPR CEIL LO AAL ALO AHI MSB MSM MSR NSE RSR SG5 SG7 N NB ALO1; first [lia | Z.div_mod_to_equations; lia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; Z.div_mod_to_equations; lia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | Z.div_mod_to_equations; lia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- forall RNG' m', _ => idtac | |- ?G => idtac "REM-P3r" G end.
  3,4: intros RNG' mR t0r t1r t2r a0r a1r a2r a3r a4r a5r a6r a7r t3r t4r t5r t6r PRP;
       destruct PRP as (FPLE & MUr & WMr & MIr & STr & SHU' & RSU & PCr & PMC');   (* [comment removed for export] *) rewrite SG2 in SHU'; rewrite SG2 in RSU;
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in MUr by (clear -SPR CEIL LO; lia);
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in STr by (clear -SPR CEIL LO; lia);
       rewrite SG2 in MUr; unfold PZR_STACK in MUr, STr; iprefix.
  (* [comment removed for export] *)
  3,4: lazymatch type of MU with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MU2 : munch W m0 mm) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WM2 : wmono bsegs m0 mm) by (eapply wmono_trans; [exact WM| exact WMr]);
         clear MU WM; rename MU2 into MU; rename WM2 into WM end end.
  3,4: lazymatch type of MUp with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MUp2 : munch W m0 mm) by (eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WMp2 : wmono bsegs m0 mm) by (eapply wmono_trans; [exact WMp| exact WMr]);
         clear MUp WMp; rename MUp2 into MUp; rename WMp2 into WMp end end.
  3,4: xport HDR MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHL' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHT' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG6 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport PP MUr WMr ltac:(clear -SPR CEIL LO SG3; lia).
  4: xport SHP MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 GLT ALO1 ASD ASDa ASDb; dlia).
  3,4: destruct PCr as (PC1' & PC2' & PC3' & PC4' & PC5' & PC6' & PC7').
  (* [comment removed for export] *)
  all: replace (ret_pc (Z_to_bv 64 0x33fc0)) with (Z_to_bv 64 0x33fc0 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  3,4: clear MUr WMr.
  3,4: pose proof (rng_fp_le _ _ _ _ FPLE RIMG) as RIMGq.   (* [comment removed for export] *)
  all: first [ lazymatch goal with H : _ mod 8 <> 0 |- _ => fail | _ => idtac end;
               call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 0 (Z_to_bv 8 0))
             | call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 1 (Z_to_bv 8 0)) ].
  all: try clear RIMGq.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- _ = shad _ + _ => rewrite SG2; reflexivity
       | |- _ = (if _ then _ else _) => first [rewrite (proj2 (Z.eqb_eq _ _) M0); reflexivity | rewrite (proj2 (Z.eqb_neq _ _) M0); reflexivity]
       | |- rw_cells _ _ 0xc72f8 _ => assumption
       | |- rw_cells _ _ 0xcfcf8 _ => assumption
       | |- rw_cells _ _ 0xd09e0 _ => assumption
       | |- rw_cells _ _ 0xcf55c _ => assumption
       | |- rw_cells _ _ 0xcd54d _ => assumption
       | |- rng_aimg _ => first [exact RIMG | unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]]
       | |- ~ _ -> rng _ _ _ => intros _; first [ eapply rng_sub'; [exact RSA|]; clear -SG5 SG7; lia
                                            | eapply rng_sub'; [eapply rng_fp_le; [eassumption| exact RSA]|]; clear -SG5 SG7; lia ]
       | |- ~ _ -> rw_cells _ _ _ _ => first [intros _; assumption | intros NE; exfalso; clear -NE M0; lia]
       | |- _ => atop_facts; clear -SPR CEIL LO AAL ALO AHI MSB MSR NSE RSR N NB SG5 SG7 ALO1; first [lia | Z.div_mod_to_equations; lia]
       end.
  all: try (eapply ablk_sub; [exact ALO | clear -SG5 SG9 N; Z.div_mod_to_equations; lia | clear -MSE NSE RSR MSB SG5 SG7 SG9 N; first [lia | Z.div_mod_to_equations; lia]]).   (* [comment removed for export] *)
  all: match goal with |- evtF _ _ _ _ => idtac | |- ?G => idtac "REM-PART" G end.
  (* [comment removed for export] *)
  all: try lazymatch goal with H : _ -> rw_cells _ _ _ [C1 (Z_to_bv 8 (_ mod 8))] |- _ => rename H into SHPf end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (DEPF : ADEPOT DI L mm) by
         (eapply (adi_frame DI); [exact DEP2 | exact MUp | exact WMp |];
          repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; pose proof DJN as X1; unbox X1; pose proof DJS as X2; unbox X2;
                                     clear -Hq X1 X2 SPR CEIL LO SHN SHS N1 R1 SG3 SG4 SG5 SG7 ALO AHI MSB ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil) end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PCF : poison_cells mm) by
         (unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)) end.
  all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => assert (PMF : premap_cells mm) by
         (first [ assumption
                | eapply premap_cells_frame2; [unboxed PMC| exact MU| exact WM|]; unfold wpiece_ok;
                  repeat (apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; clear -SPR CEIL LO SG3 SHN SHS ALO ALO1 ASD ASDa ASDb NBND NBNDa NBNDb SBND SBNDa SBNDb N0 R0; lia|]); apply Forall_nil ]) end.
  all: apply evtF_done; eapply KONT; [| exact IDR].
  all: unfold allocBC_postS; cbv zeta.
  all: lazymatch goal with |- exists id, _ => exists x end; do 17 eexists.
  all: split; [reflexivity|].
  all: split; [exact FPLE|].
  all: split; [exact MU|]. all: split; [exact WM|]. all: split; [assumption|]. all: split; [assumption|]. all: split; [exact IDR|].
  all: split; [exact HDR|].
  all: split; [unfold fill_at; exact SHL'|].
  all: split; [rewrite SG2; exact SHU'|].
  all: split; [rewrite SG2; first [exact SHPf | intros NE; exfalso; clear -NE M0; lia]|].
  all: split; [unfold fill_at; rewrite SG2; exact SHT'|].
  all: split; [exact DEPF| split; [exact PCF| exact PMF]].
Qed.
End WithDepot.
End CANSEC1.
