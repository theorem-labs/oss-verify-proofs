(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA SysStepF StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanCtrlProps AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison0 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
(* [comment removed for export] *)
Local Ltac fph_ok := lazymatch goal with |- (?a <= ?b /\ _)%Z =>
  lazymatch b with context [shad _] => lazymatch a with context [shad _] => idtac end end end.
Local Ltac fp_find8h := first [ apply Exists_cons_hd; cbn [fst snd]; fph_ok; split; lia | apply Exists_cons_tl; fp_find8h ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8h | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148238848 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma gaas_sec_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a SB ms needed idx : Z),
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] ->                         (* [comment removed for export] *)
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] ->                       (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 needed); C8 (Z_to_bv 64 idx)] ->   (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= needed <= ms -> 8192 <= ms -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG a 32 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) s1
                    (Z_to_bv 64 4096) (Z_to_bv 64 (needed + 4095)) (Z_to_bv 64 needed) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x34074) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33fe4) fc None m (seg_rom asegs)).
Proof.
  intros until idx. intros I32 I64 HDR AL LO HI ND MS SB0 SBH DJ RIMG RTLS RA. (pose proof (ablk_lin _ _ LO) as ndP__; nd_pre ndP__ 4%nat; intros ALO AZ0 _ _; nd_post).   (* [comment removed for export] *)
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
Definition wpiece_ok (iv : Z * Z) : Prop := AIMG_HI <= fst iv \/ (0x1804c8 <= fst iv /\ snd iv <= 0x5d0510).

#[using="Type"] Lemma disjoint_img2 : forall W A n, Forall wpiece_ok W -> 0 <= n ->
  (A + n <= 0x1804c8 \/ (0x5d0510 <= A /\ A + n <= AIMG_HI)) -> disjoint_from W A n.
Proof.
  intros W A n HW Hn HA. unfold wpiece_ok, AIMG_HI in *. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH].
Qed.

#[using="Type"] Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold poison_cells in *. (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]).
Qed.

#[using="Type"] Lemma premap_cells_frame2 : forall m m' W,
  premap_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> premap_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold premap_cells in *. (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]) ].
Qed.

#[using="Type"] Lemma arelro_frame2 : forall m m' W,
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
#[using="Type"] Lemma land_lnot7_eq : forall n, 0 <= n -> Z.land n (Z.lnot 7) = n - n mod 8.
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
             F (Z_to_bv 64 0x34154) fc None m' (seg_rom asegs)
    /\ fp_le RNG RNG'
    /\ munch (allocBC_WS L sp a ms) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (hdr_b1_mid 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
       (* [comment removed for export] *)
    /\ fill_at m' (shad a + 512) 256 0xfa
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))])
    /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
    /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

Definition allocBC_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t a ms idx SB lo sz pc : Z) (tb : list word) (tr : list Z) (fr0 : list byte)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= al_ctx L \/ al_ctx L + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (shad AB) [CB 256 (repeat (Z_to_bv 8 0) 256)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]) ->
  (exists junk, rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (ms / 8 - 768 - granules n)) junk]) ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  sclr t 4096 -> sclr (al_ctx L) 65536 -> sclr (al_nodes L) 1048576 -> sclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  (* [comment removed for export] *)
  (forall RNG' m' id rax t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6',
     allocBC_postS L RNG sp gp tp F fc n S t a ms lo m RNG' m'
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x34154) fc None m' (seg_rom asegs)) ->
     0 < id < 2^31 ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x34154) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33ea8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ea8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 17).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 18).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 19).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 20).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 21).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 22).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 23).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 24).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 25).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 26).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 27).
Variable a : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 28).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 29).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 30).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 32).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 33).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 34).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 35).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 36).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 37).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 38).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 39).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 40).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 41).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 42).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 43).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 44).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 45).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 46).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 47).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 48).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 49).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 50).
#[using="PR"] Lemma allocBC_sec__body : ltac:(let T := type of (fun (h : allocBC_sec__stmt) => h L RNG R k Q sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t a ms idx SB lo sz pc tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (a, (ms, (idx, (SB, (lo, (sz, (pc, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS FR HDRP HDR SHL SHU SHP [junkT SHT] PC PMC RELRO PP I32 I64
         CT8 TT0 CX0 CX1 T0 T1 SHT0 SHC SHN SHS SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1
         RIMG RTLS RSTK RS RNO RST RCTX RT RA RSA KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AREQMAX in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; clear -N; lia) PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  rewrite (land_lnot7_eq n) by (clear -N; lia).
  (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).        (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768 /\ 0x800b8600 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1 /\ 768 + granules n + 256 <= ms / 8
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -AAL ABND ABNDa ABNDb ABNDc ABNDd AHI N RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  (nd_pre SG 9%nat; intros SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9; nd_post).
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb _ _; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ SHN ltac:(clear -N0; unfold AIMG_HI in *; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ SHS ltac:(clear -R0; unfold AIMG_HI in *; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  pose proof (munch_refl (allocBC_WS L sp a ms) m) as MU. pose proof (wmono_refl asegs m) as WM.
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
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
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
         | |- rng_atls _ => exact RTLS
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
  box SHL.   (* [comment removed for export] *)
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096) 2048 256 250 lo (repeat (Z_to_bv 8 0) 256)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear SHL; try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG1; unboxed SHL
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
  all: try box SHT.   (* [comment removed for export] *)
  all: match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  all: step; call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        (a + 6144 + 8 * granules n) (ms - 6144 - 8 * granules n) (ms / 8 - 768 - granules n) 250 lo junkT).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear SHT; try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SGX; unboxed SHT
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
  1,2: box SHU.   (* [comment removed for export] *)
  1,2: match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  1,2: call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (a + 6144) (n - n mod 8) (shlen (n - n mod 8)) 0 lo (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; first [exact SHU | unboxed SHU]
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
       (nd_pre PRP 10%nat; intros FPLE FBW MUr WMr MIr STr SHU' RSU PCr PMC'; nd_post); rewrite SG2 in SHU'; rewrite SG2 in RSU;
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in MUr by (clear -SPR CEIL LO; lia);
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in STr by (clear -SPR CEIL LO; lia);
       rewrite SG2 in MUr; unfold PZR_STACK in MUr, STr; iprefix.
  (* [comment removed for export] *)
  3,4: lazymatch type of MU with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MU2 : munch W m0 mm) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WM2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WM| exact WMr]);
         clear MU WM; rename MU2 into MU; rename WM2 into WM end end.
  3,4: lazymatch type of MUp with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MUp2 : munch W m0 mm) by (eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WMp2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WMp| exact WMr]);
         clear MUp WMp; rename MUp2 into MUp; rename WMp2 into WMp end end.
  3,4: xport HDR MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHL' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHT' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG6 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport PP MUr WMr ltac:(clear -SPR CEIL LO SG3; lia).
  4: xport SHP MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 GLT ALO1 ASD ASDa ASDb; dlia).
  3,4: (nd_pre PCr 7%nat; intros PC1' PC2' PC3' PC4' PC5' PC6' PC7'; nd_post).
  (* [comment removed for export] *)
  all: replace (ret_pc (Z_to_bv 64 0x340c0)) with (Z_to_bv 64 0x340c0 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  3,4: clear MUr WMr.
  (* [comment removed for export] *)
  3,4: assert (RIMG' : rng_aimg RNG') by (unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]).
  3,4: assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).
  all: first [ lazymatch goal with H : _ mod 8 <> 0 |- _ => fail | _ => idtac end;
               call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 0 (Z_to_bv 8 0))
             | call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 1 (Z_to_bv 8 0)) ].
  all: try clear RIMG' RTLS'.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- _ = shad _ + _ => rewrite SG2; reflexivity
       | |- _ = (if _ then _ else _) => first [rewrite (proj2 (Z.eqb_eq _ _) M0); reflexivity | rewrite (proj2 (Z.eqb_neq _ _) M0); reflexivity]
       | |- rw_cells _ _ 0xa54a0 _ => assumption
       | |- rw_cells _ _ 0xae5f8 _ => assumption
       | |- rw_cells _ _ 0xaf2e0 _ => assumption
       | |- rw_cells _ _ 0xade5c _ => assumption
       | |- rw_cells _ _ 0xabe4d _ => assumption
       | |- rng_aimg _ => first [exact RIMG | unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]]
       | |- rng_atls _ => first [exact RTLS | eapply rng_fp_le; [exact FPLE| exact RTLS]]
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
End Zd1.
#[using="PR"] Lemma allocBC_sec : ltac:(let t := eval cbv delta [allocBC_sec__stmt] in allocBC_sec__stmt in exact t).
Proof. exact allocBC_sec__body. Qed.
End WithDepot.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrlProps OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison0.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2g.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Lemma outside_In8 : forall (W : list ivl) x lo hi, outside W x -> In (lo, hi) W -> ~ (lo <= x < hi)%Z.
Proof. induction W as [|[a b] W IH]; cbn; intros x lo hi H HI; [tauto|]. destruct HI as [E|HI]; [injection E; intros; subst; tauto| apply (IH x); tauto]. Qed.
Local Lemma sub_fp_cover8 : forall W W' : list ivl,
  Forall (fun iv : ivl => (snd iv <= fst iv)%Z \/ Exists (fun jv : ivl => (fst jv <= fst iv /\ snd iv <= snd jv)%Z) W') W -> sub_fp W W'.
Proof.
  intros W W' HF x HO. induction HF as [|[lo hi] W HP HF IH]; cbn; [exact I|]. split; [| exact IH].
  cbn in HP. destruct HP as [HE|HP]; [lia|]. apply Exists_exists in HP. (nd_pre HP 3%nat; intros [lo' hi'] HI [H1 H2]; nd_post). cbn in H1, H2.
  pose proof (outside_In8 _ _ _ _ HO HI). lia.
Qed.
Local Ltac fp_cheap8 := first [ match goal with Hs : bv_unsigned _ = (bv_unsigned _ + _)%Z |- _ => clear -Hs end | clear ]; Stdlib.micromega.Lia.lia.   (* [comment removed for export] *)
Local Ltac fp_find8c := first [ apply Exists_cons_hd; cbn [fst snd]; split; fp_cheap8 | apply Exists_cons_tl; fp_find8c ].
Local Ltac fp_find8 := first [ apply Exists_cons_hd; cbn [fst snd]; split; lia | apply Exists_cons_tl; fp_find8 ].
(* [comment removed for export] *)
Local Ltac fp_base8 := lazymatch goal with |- (?a <= ?b /\ _)%Z => let X := leftmost a in let Y := leftmost b in first [ constr_eq X Y | is_Zlit X; is_Zlit Y ] end.
Local Ltac fp_find8s := first [ apply Exists_cons_hd; cbn [fst snd]; fp_base8; split; lia | apply Exists_cons_tl; fp_find8s ].
(* [comment removed for export] *)
Local Ltac fph_ok := lazymatch goal with |- (?a <= ?b /\ _)%Z =>
  lazymatch b with context [shad _] => lazymatch a with context [shad _] => idtac end end end.
Local Ltac fp_find8h := first [ apply Exists_cons_hd; cbn [fst snd]; fph_ok; split; lia | apply Exists_cons_tl; fp_find8h ].
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8s | right; fp_find8h | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_call_munch_tac ::= first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ].
(* [comment removed for export] *)
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
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_shad_int : forall a ms, ablk a (a + ms) -> a mod 8 = 0 -> 0 <= ms ->
  exists k, 0 <= k <= 1 /\ a + ms <= shad a + k * 18446744073709551616 /\ shad a + ms / 8 + 8 <= a + (1 - k) * 18446744073709551616
            /\ 2148239360 <= shad a /\ shad a + ms / 8 <= 17594333495296.
Proof.
  intros a ms H A8 M0. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. rewrite !Shadow.shad_div. unfold AsanEmbed.ASHOFF.
  destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma gaas_sec_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (a SB ms needed idx : Z),
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] ->                         (* [comment removed for export] *)
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] ->                       (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 needed); C8 (Z_to_bv 64 idx)] ->   (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= needed <= ms -> 8192 <= ms -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG a 32 ->
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 ((needed + 4095) / 4096 * 4096)) s1
                    (Z_to_bv 64 4096) (Z_to_bv 64 (needed + 4095)) (Z_to_bv 64 needed) a3 a4 a5 a6 a7
                    (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x340dc) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (a + 4096)) s3 s4 s5 (Z_to_bv 64 AINSTANCE) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3404c) fc None m (seg_rom asegs)).
Proof.
  intros until idx. intros I32 I64 HDR AL LO HI ND MS SB0 SBH DJ RIMG RTLS RA. (pose proof (ablk_lin _ _ LO) as ndP__; nd_pre ndP__ 4%nat; intros ALO AZ0 _ _; nd_post).   (* [comment removed for export] *)
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
Definition wpiece_ok (iv : Z * Z) : Prop := AIMG_HI <= fst iv \/ (0x1808c8 <= fst iv /\ snd iv <= 0x5d0910).

#[using="Type"] Lemma disjoint_img2 : forall W A n, Forall wpiece_ok W -> 0 <= n ->
  (A + n <= 0x1808c8 \/ (0x5d0910 <= A /\ A + n <= AIMG_HI)) -> disjoint_from W A n.
Proof.
  intros W A n HW Hn HA. unfold wpiece_ok, AIMG_HI in *. induction HW as [|[lo hi] W H1 H2 IH]; cbn in *; [exact I|]. split; [lia| exact IH].
Qed.

#[using="Type"] Lemma poison_cells_frame2 : forall m m' W,
  poison_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> poison_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold poison_cells in *. (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat lazymatch goal with |- _ /\ _ => split end;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]).
Qed.

#[using="Type"] Lemma premap_cells_frame2 : forall m m' W,
  premap_cells m -> munch W m m' -> wmono asegs m m' -> Forall wpiece_ok W -> premap_cells m'.
Proof.
  intros m m' W PC MU WM HW. unfold premap_cells in *. (nd_pre PC 7%nat; intros P1 P2 P3 P4 P5 P6 P7; nd_post).
  repeat lazymatch goal with |- _ /\ _ => split end;
    first [ apply premap_canary_any
          | (eapply rw_cells_transport; [eassumption | exact MU | exact WM | apply disjoint_img2; [exact HW| cbn; lia| cbn; unfold AIMG_HI; lia]]) ].
Qed.

#[using="Type"] Lemma arelro_frame2 : forall m m' W,
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
#[using="Type"] Lemma land_lnot7_eq : forall n, 0 <= n -> Z.land n (Z.lnot 7) = n - n mod 8.
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
             F (Z_to_bv 64 0x341bc) fc None m' (seg_rom asegs)
    /\ fp_le RNG RNG'
    /\ munch (allocBC_WS L sp a ms) m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -128)
    /\ 0 < id < 2^31
    /\ rw_cells asegs m' (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (hdr_b1_mid 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
       (* [comment removed for export] *)
    /\ fill_at m' (shad a + 512) 256 0xfa
    /\ rw_cells asegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells asegs m' (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 (n mod 8))])
    /\ fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa
    /\ ADEPOT DI L m' /\ poison_cells m' /\ premap_cells m'.

Definition allocBC_sec__stmt : Prop := forall (L : alayout) RNG (R : Type) (k : AM R) (Q : R -> footprint -> machine_state -> Prop)
    sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S t a ms idx SB lo sz pc : Z) (tb : list word) (tr : list Z) (fr0 : list byte)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
  let AB := a + 4096 in let UB := a + 6144 in let size := needed_size n in
  stk asegs m lo (bv_unsigned sp + -128) -> ATOP <= lo -> lo <= bv_unsigned sp + -128 - ADEPOT_STACK ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  1 <= n <= AREQMAX -> is_primary n = false -> ms = sec_map_size n ->
  (* [comment removed for export] *)
  a mod 4096 = 0 -> ablk a (a + ms) -> a + ms <= ATOP ->
  (a + ms <= SB \/ SB + 137438953472 <= a) -> 0 <= SB -> SB + 137438953472 <= ATOP ->
  (a + ms <= t \/ t + 4096 <= a) -> (a + ms <= al_ctx L \/ al_ctx L + 65536 <= a) ->
  (a + ms <= al_nodes L \/ al_nodes L + 1048576 <= a) -> (a + ms <= al_store L \/ al_store L + 8388608 <= a) ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -128)
     [CB 8 fr0; C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 16); C8 s11v; C8 s10v; C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v;
      C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 size); C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (a + 6128) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m (shad AB) [CB 256 (repeat (Z_to_bv 8 0) 256)] ->
  rw_cells asegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))] ->
  (n mod 8 <> 0 -> rw_cells asegs m (shad UB + shlen (n - n mod 8)) [C1 (Z_to_bv 8 0)]) ->
  (exists junk, rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (ms / 8 - 768 - granules n)) junk]) ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)] (* [comment removed for export] *) ->
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] ->
  rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)] -> rw_cells asegs m t [C8 (Z_to_bv 64 (al_ctx L))] ->
  AIMG_HI <= al_ctx L -> al_ctx L + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  sclr t 4096 -> sclr (al_ctx L) 65536 -> sclr (al_nodes L) 1048576 -> sclr (al_store L) 8388608 ->
  (* [comment removed for export] *)
  rw_cells asegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr asegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  AIMG_HI <= al_nodes L -> al_nodes L + 1048576 <= ATOP -> AIMG_HI <= al_store L -> al_store L + 8388608 <= ATOP ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 -> rng RNG (al_ctx L) 4096 -> rng RNG t 4096 ->
  rng RNG a ms -> rng RNG (shad a) (ms / 8) ->
  (* [comment removed for export] *)
  (forall RNG' m' id rax t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s6' t3' t4' t5' t6',
     allocBC_postS L RNG sp gp tp F fc n S t a ms lo m RNG' m'
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x341bc) fc None m' (seg_rom asegs)) ->
     0 < id < 2^31 ->
     implS asegs RNG' (aembed ATOP k) (epostF Q)
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0' t1' t2'
                  (Z_to_bv 64 (ms - 4096)) (Z_to_bv 64 n) a0' a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 AB) (Z_to_bv 64 size) (Z_to_bv 64 UB) (Z_to_bv 64 (a + 6128)) s6'
                  (Z_to_bv 64 S) (Z_to_bv 64 0) (Z_to_bv 64 (UB + n + 7)) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3' t4' t5' t6') F (Z_to_bv 64 0x341bc) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (poison0 UB (Z.land n (Z.lnot 7)) k)) (epostF Q)
    (MS (mkR (Z_to_bv 64 0x33f10) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
              (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 AB) a1 a2 a3 a4 a5 a6 a7
              (Z_to_bv 64 8) (Z_to_bv 64 size) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
              (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
              t3 t4 t5 t6)
        F (Z_to_bv 64 0x33f10) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 1).
Variable R : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 2).
Variable k : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 5).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 6).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 7).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 8).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 9).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 10).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 11).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 12).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 13).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 14).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 15).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 16).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 17).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 18).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 19).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 20).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 21).
Variable F : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 22).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 23).
Variable m : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 24).
Variable n : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 25).
Variable S : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 26).
Variable t : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 27).
Variable a : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 28).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 29).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 30).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 31).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 32).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 33).
Variable pc : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 34).
Variable tb : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 35).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 36).
Variable fr0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 37).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 38).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 39).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 40).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 41).
Variable s3v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 42).
Variable s4v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 43).
Variable s5v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 44).
Variable s6v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 45).
Variable s7v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 46).
Variable s8v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 47).
Variable s9v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 48).
Variable s10v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 49).
Variable s11v : ltac2:(SecDietF.SzSecF.ty 'allocBC_sec__stmt 50).
#[using="PR"] Lemma allocBC_sec__body : ltac:(let T := type of (fun (h : allocBC_sec__stmt) => h L RNG R k Q sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n S t a ms idx SB lo sz pc tb tr fr0 ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (R, (k, (Q, (sp, (gp, (tp, (t0, (t1, (t2, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (t3, (t4, (t5, (t6, (F, (fc, (m, (n, (S, (t, (a, (ms, (idx, (SB, (lo, (sz, (pc, (tb, (tr, (fr0, (ra0, (s0v, (s1v, (s2v, (s3v, (s4v, (s5v, (s6v, (s7v, (s8v, (s9v, (s10v, s11v))))))))))))))))))))))))))))))))))))))))))))))))))) as _.
 cbv zeta.
  intros ST CEIL LO MI TP N PRIM HMS AAL ALO AHI DJSB SB0 SBH DJT DJC DJN DJS FR HDRP HDR SHL SHU SHP [junkT SHT] PC PMC RELRO PP I32 I64
         CT8 TT0 CX0 CX1 T0 T1 SHT0 SHC SHN SHS SS SZ SZB TB LTB TRF TRU SPS S47 DEP N0 N1 R0 R1
         RIMG RTLS RSTK RS RNO RST RCTX RT RA RSA KONT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, AREQMAX in *.
  (pose proof (sec_facts n ltac:(unfold AREQMAX; clear -N; lia) PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB RZ RSE RSR RSM NSE MSE MSR MSM MSB; nd_post). rewrite <- HMS in MSE, MSR, MSM, MSB.
  word_range sp SPR.
  (nd_pre PC 7%nat; intros PC1 PC2 PC3 PC4 PC5 PC6 PC7; nd_post).
  rewrite (land_lnot7_eq n) by (clear -N; lia).
  (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros ALO1 AZ0 _ _; nd_post). unfold AIMG_HI in ALO1.   (* [comment removed for export] *)
  (nd_pre (ablk_int _ _ ALO) 6%nat; intros kA ABND ABNDa ABNDb ABNDc ABNDd; nd_post).        (* [comment removed for export] *)
  assert (SG : shad (a + 4096) = shad a + 512 /\ shad (a + 6144) = shad a + 768 /\ 0x800b8800 <= shad a /\ shad a + ms / 8 <= 0x10007fff8000
               /\ 0 <= shlen (n - n mod 8) <= granules n /\ granules n <= shlen (n - n mod 8) + 1 /\ 768 + granules n + 256 <= ms / 8
               /\ shlen (n - n mod 8) = (n - n mod 8) / 8 /\ granules n = (n + 7) / 8).
  { unfold granules. rewrite !shad_div, !shlen_div. unfold ASHOFF. clear -AAL ABND ABNDa ABNDb ABNDc ABNDd AHI N RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  (nd_pre SG 9%nat; intros SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9; nd_post).
  (nd_pre (ablk_shad_int _ _ ALO ltac:(clear -AAL; Z.div_mod_to_equations; lia) ltac:(clear -MSB; lia)) 6%nat; intros kS ASD ASDa ASDb _ _; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ SHN ltac:(clear -N0; unfold AIMG_HI in *; lia) ltac:(clear -N1; lia)) 4%nat; intros kN NBND NBNDa NBNDb; nd_post).   (* [comment removed for export] *)
  (nd_pre (sclr_int _ _ SHS ltac:(clear -R0; unfold AIMG_HI in *; lia) ltac:(clear -R1; lia)) 4%nat; intros kR SBND SBNDa SBNDb; nd_post).
  pose proof (munch_refl (allocBC_WS L sp a ms) m) as MU. pose proof (wmono_refl asegs m) as WM.
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
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp ((adi_put DI) L RNG).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
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
         | |- rng_atls _ => exact RTLS
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
  box SHL.   (* [comment removed for export] *)
  match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  step. call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (a + 4096) 2048 256 250 lo (repeat (Z_to_bv 8 0) 256)).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear SHL; try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG1; unboxed SHL
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
  all: try box SHT.   (* [comment removed for export] *)
  all: match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  all: step; call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        (a + 6144 + 8 * granules n) (ms - 6144 - 8 * granules n) (ms / 8 - 768 - granules n) 250 lo junkT).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear SHT; try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SGX; unboxed SHT
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
  1,2: box SHU.   (* [comment removed for export] *)
  1,2: match goal with H : stk asegs ?mm _ _ |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => rename H into STK__; box STK__ end.   (* [comment removed for export] *)
  1,2: call_sp (poison_shadow_spec_k RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (a + 6144) (n - n mod 8) (shlen (n - n mod 8)) 0 lo (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => try clear STK__
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => unboxed STK__
       | |- mem_inv _ _ => assumption
       | |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => assumption | |- _ /\ _ => split end)
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ (shad _) _ => rewrite SG2; first [exact SHU | unboxed SHU]
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
       (nd_pre PRP 10%nat; intros FPLE FBW MUr WMr MIr STr SHU' RSU PCr PMC'; nd_post); rewrite SG2 in SHU'; rewrite SG2 in RSU;
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in MUr by (clear -SPR CEIL LO; lia);
       rewrite (unsigned_lit (bv_unsigned sp + -128)) in STr by (clear -SPR CEIL LO; lia);
       rewrite SG2 in MUr; unfold PZR_STACK in MUr, STr; iprefix.
  (* [comment removed for export] *)
  3,4: lazymatch type of MU with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MU2 : munch W m0 mm) by (eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WM2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WM| exact WMr]);
         clear MU WM; rename MU2 into MU; rename WM2 into WM end end.
  3,4: lazymatch type of MUp with munch ?W ?m0 ?m3 => lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
         assert (MUp2 : munch W m0 mm) by (eapply munch_trans; [exact MUp| eapply munch_weaken; [| exact MUr]; unfold sub_fp; cbn [outside]; intros q Hq; clear -Hq SPR SG5 SG7; lia]);
         assert (WMp2 : wmono asegs m0 mm) by (eapply wmono_trans; [exact WMp| exact WMr]);
         clear MUp WMp; rename MUp2 into MUp; rename WMp2 into WMp end end.
  3,4: xport HDR MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHL' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport SHT' MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG6 SG7 ALO1 ASD ASDa ASDb; dlia).
  3,4: xport PP MUr WMr ltac:(clear -SPR CEIL LO SG3; lia).
  4: xport SHP MUr WMr ltac:(clear -SPR CEIL LO ALO AHI MSB SG3 SG4 SG5 SG7 GLT ALO1 ASD ASDa ASDb; dlia).
  3,4: (nd_pre PCr 7%nat; intros PC1' PC2' PC3' PC4' PC5' PC6' PC7'; nd_post).
  (* [comment removed for export] *)
  all: replace (ret_pc (Z_to_bv 64 0x34128)) with (Z_to_bv 64 0x34128 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  3,4: clear MUr WMr.
  (* [comment removed for export] *)
  3,4: assert (RIMG' : rng_aimg RNG') by (unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]).
  3,4: assert (RTLS' : rng_atls RNG') by (eapply rng_fp_le; [exact FPLE| exact RTLS]).
  all: first [ lazymatch goal with H : _ mod 8 <> 0 |- _ => fail | _ => idtac end;
               call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 0 (Z_to_bv 8 0))
             | call (partial_specG _ n (a + 6144) (shad a + 768 + shlen (n - n mod 8)) 1 (Z_to_bv 8 0)) ].
  all: try clear RIMG' RTLS'.
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- mem_inv _ _ => assumption
       | |- _ = shad _ + _ => rewrite SG2; reflexivity
       | |- _ = (if _ then _ else _) => first [rewrite (proj2 (Z.eqb_eq _ _) M0); reflexivity | rewrite (proj2 (Z.eqb_neq _ _) M0); reflexivity]
       | |- rw_cells _ _ 0xa5880 _ => assumption
       | |- rw_cells _ _ 0xae9f8 _ => assumption
       | |- rw_cells _ _ 0xaf6e0 _ => assumption
       | |- rw_cells _ _ 0xae25c _ => assumption
       | |- rw_cells _ _ 0xac24d _ => assumption
       | |- rng_aimg _ => first [exact RIMG | unfold rng_aimg; eapply rng_fp_le; [exact FPLE| exact RIMG]]
       | |- rng_atls _ => first [exact RTLS | eapply rng_fp_le; [exact FPLE| exact RTLS]]
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
End Zd1.
#[using="PR"] Lemma allocBC_sec : ltac:(let t := eval cbv delta [allocBC_sec__stmt] in allocBC_sec__stmt in exact t).
Proof. exact allocBC_sec__body. Qed.
End WithDepot.
End CANSEC1.
End TwB.
