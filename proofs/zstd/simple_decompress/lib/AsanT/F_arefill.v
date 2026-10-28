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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MM_syscalls WStr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase AKit AKit2 ARep ARepKit ARepFrame ARefill_iface RT_stubs
     F_apoison F_acache F_aalloc3 F_ammap F_aensure F_apopulate F_agetfrom.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
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
Local Ltac fp_cover8 := apply sub_fp_cover8; repeat (apply Forall_cons; [ cbn [fst snd]; first [left; fp_cheap8 | right; fp_find8c | right; fp_find8] | ]); apply Forall_nil.
(* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::=
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
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; slia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ first [ fp_cover8 | unfold sub_fp; cbn [outside]; first [ match goal with Hs : bv_unsigned _ = bv_unsigned _ + _ |- _ => clear -Hs; intros; lia end | clear; intros; lia | intros; slia ] ] | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac refresh H := let X := fresh in pose proof H as X; clear H; rename X into H.

Section CANSEC1. Context {rc : runConstT}.
Definition refill_entry := 0x386ec.
End CANSEC1.
Notation REFILL_STACK := 672 (only parsing).    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT}.
Lemma v_divuw_lit : forall x y, 0 <= x < 2^31 -> 0 < y < 2^31 -> v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (x / y).
Proof.
  intros x y Hx Hy. unfold v_divuw. rewrite !unsigned_lit by lia.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. replace (Z.of_N (32 - 1)) with 31 by reflexivity.
  change (2^31) with 2147483648 in *.
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite (Z.mod_small x) by lia. f_equal.
  assert (B : 0 <= x / y <= x) by (Z.div_mod_to_equations; nia).
  Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
Definition arec_hdr (L : alayout) (m : amem) (j cnt mc cs : Z) : Prop :=
  rw_cells bsegs m (acache_addr L j) [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 mc); C8 (Z_to_bv 64 cs)].

End CANSEC2.
Ltac zfact := first [ split; zfact | vm_compute; first [reflexivity | discriminate | intros ?; discriminate] ].
Section CANSEC3. Context {rc : runConstT}.
Lemma mc_le4 : forall i, 1 <= i <= 4 -> max_cached i = 16 /\ 8 <= 1024 / (32 * i).
Proof.
  intros i Hi. assert (E : i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_mid : forall i, 5 <= i <= 16 -> max_cached i = 2 * (1024 / (32 * i)) /\ 1 <= 1024 / (32 * i) < 8.
Proof.
  intros i Hi. assert (E : i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_big : forall i, 17 <= i <= 30 -> max_cached i = 2 /\ 768 <= size_of_class i <= 65536 /\ 1024 / size_of_class i <= 1.
Proof.
  intros i Hi. assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.
Lemma mc_31 : max_cached 31 = 16. Proof. vm_compute. reflexivity. Qed.

Lemma size_formula2 : forall i, 17 <= i <= 30 ->
  Z_to_bv 64 (Z.land ((Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl i 63))) 63) mod 18446744073709551616)
                     (Z.shiftr ((Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) mod 18446744073709551616) 1)
              + Z.shiftl 512 ((Z.shiftr (i - 16) 1) mod 64)) = Z_to_bv 64 (size_of_class i).
Proof.
  intros i Hi.
  assert (E : i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30) by lia.
  repeat (destruct E as [->|E]; [apply f_equal; vm_compute; reflexivity|]). subst. apply f_equal. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint ic_W (L : alayout) (i : Z) (d : nat) : list (Z * Z) :=
  match d with O => [] | Datatypes.S d' => (acache_addr L i + 4, acache_addr L i + 16) :: ic_W L (i + 1) d' end.

Lemma munch_cons_trans : forall p W m m1 m', munch [p] m m1 -> munch W m1 m' -> munch (p :: W) m m'.
Proof.
  intros [lo hi] W m m1 m' A B. eapply munch_trans; [eapply munch_weaken; [| exact A] | eapply munch_weaken; [| exact B]];
    unfold sub_fp; intros x Hx; cbn [outside] in *; tauto.
Qed.

Lemma ic_W_disjoint_below : forall L i d A n, A + n <= acache_addr L i + 4 -> disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH. unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_gen : forall L i d A n, (A + n <= acache_addr L i + 4 \/ al_t L + 2768 <= A) -> i + Z.of_nat d <= 32 -> 1 <= i ->
  disjoint_from (ic_W L i d) A n.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i A n H Hd Hi; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma ic_W_disjoint_chunks : forall L i d c, disjoint_from (ic_W L i d) (acache_addr L c + 16) 64.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i c; cbn [ic_W disjoint_from]; [exact I|].
  split; [unfold acache_addr; lia|]. apply IH.
Qed.

(* [comment removed for export] *)
End CANSEC3.
Ltac icdj tac := cbn [disjoint_from cells_size csize Nat.add length]; split; [tac | first [apply ic_W_disjoint_chunks | apply ic_W_disjoint_gen; [tac | clear; cbn; lia | clear; lia]]].

Section CANSEC4. Context {rc : runConstT}.
Lemma ic_W_outside : forall L i d x, (x < acache_addr L i + 4 \/ al_t L + 2768 <= x) -> i + Z.of_nat d <= 32 -> 1 <= i -> outside (ic_W L i d) x.
Proof.
  intros L i d. revert i. induction d as [|d IH]; intros i x Hx Hd Hi; cbn [ic_W outside]; [exact I|].
  split; [unfold acache_addr in *; lia|]. apply IH; unfold acache_addr in *; lia.
Qed.

Lemma initcache_loop_spec : forall RNG (d : nat) (i : Z) (L : alayout) (cnt : Z -> Z)
    ra sp gp tp s0 s1 a0 a2 a4 t3 t4 t5 t6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) fc (m : amem),
  d = Z.to_nat (32 - i) -> 1 <= i <= 31 ->
  (forall j, i <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) ->
  mem_inv bsegs m -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP ->
  rng RNG (al_t L) 4096 ->
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  evtF bsegs RNG (fun ms' => exists a1' a3' a5' t3' t4' t5' m',
      ms' = MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 a1' a2 a3' a4 a5' (Z_to_bv 64 15) (Z_to_bv 64 1024)
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6) F (Z_to_bv 64 0x387e4) fc None m' (seg_rom bsegs)
      /\ munch (ic_W L i d) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ (forall j, i <= j <= 31 -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)))
    (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
             (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x38790) fc None m (seg_rom bsegs)).
Proof.
  intros RNG d. induction d as [|d IH]; intros until m; intros HD I RECS MI T0 T1 RT TIC; [lia|]. band_lin.   (* [comment removed for export] *)
  atop_facts.
  pose proof (RECS i ltac:(lia)) as REC. unfold arec_hdr in REC.
  assert (ACE : acache_addr L i = al_t L + 208 + i * 80) by reflexivity.
  pose proof (munch_refl [(acache_addr L i + 4, acache_addr L i + 16)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  (* [comment removed for export] *)
  lazymatch goal with |- evtF _ _ ?P _ =>
  assert (TAILI : forall (q : Z) (t5x : word) (mm : amem), 0 <= q <= 8 -> 2 * Z.max 1 q = max_cached i ->
    rw_cells bsegs mm (acache_addr L i) [C4 (Z_to_bv 64 (cnt i)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
    (forall j, i + 1 <= j <= 31 -> arec_hdr L mm j (cnt j) 0 0) -> mem_inv bsegs mm -> munch [(acache_addr L i + 4, acache_addr L i + 16)]%Z m mm -> wmono bsegs m mm ->
    evtF bsegs RNG P
      (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (acache_addr L i + 8)) a2 (Z_to_bv 64 (32 * i)) a4
               (Z_to_bv 64 (i - 16)) (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (size_of_class i)) (Z_to_bv 64 q) t5x t6)
          F (Z_to_bv 64 0x3876c) fc None mm (seg_rom bsegs)))
  end.
  { intros q t5x mm Q QM RECi RECS' MI' MU' WM'. clear REC MI MU WM.
    zstep. zstep. zstep. zstep. zstep.                         (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (max_cached i))
      ltac:(apply Z_to_bv_eqm; rewrite <- QM; clear -Q; destruct (Z.ltb_spec q 1); cbn [Z.b2z]; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            change (2^1) with 2; lia).
    snapshot [(acache_addr L i + 4, acache_addr L i + 16)]%Z MUs WMs.
    step. step.                                                (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L (i + 1) + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    setreg 13 (Z_to_bv 64 (32 * (i + 1))) ltac:(f_equal; clear; lia).
    setreg 15 (Z_to_bv 64 (i + 1 - 16)) ltac:(f_equal; clear; lia).
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m2 _) => assert (RECS2 : forall j, i + 1 <= j <= 31 -> arec_hdr L m2 j (cnt j) 0 0) end.
    { intros j Hj. unfold arec_hdr. eapply cells_frame; [exact (RECS' j Hj) | exact MUs | exact WMs |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -Hj; lia. }
    step. if_cases KX; zify_cond KX; rewrite ?unsigned_lit in KX by (clear -I; lia).   (* [comment removed for export] *)
    - assert (I31 : i = 31) by (clear -KX I; lia). assert (D0 : d = 0%nat) by (clear -KX I HD; lia). subst d.
      apply evtF_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU'|]. split; [exact WM'|]. split; [assumption|].
      intros j Hj. assert (J : j = i) by (clear -Hj I31 I; lia). subst j. unfold arec_hdr.
      lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end.
    - eapply evtF_mono.
      { eapply (IH (i + 1) L cnt); try eassumption; clear -KX I HD T0 T1 TIC; lia. }
      cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m' & -> & MU2 & WM2 & MI2 & RECS3).
      do 7 eexists. split; [reflexivity|].
      split; [cbn [ic_W]; eapply munch_cons_trans; [exact MU' | exact MU2]|].
      split; [eapply wmono_trans; [exact WM' | exact WM2]|]. split; [exact MI2|].
      intros j Hj. destruct (Z.eq_dec j i) as [->|NE].
      + unfold arec_hdr. eapply cells_frame; [| exact MU2 | exact WM2 |]; [lazymatch goal with H : rw_cells bsegs _ (acache_addr L i) _ |- _ => exact H end|].
        cbn [cells_size csize Nat.add]. apply ic_W_disjoint_below. unfold acache_addr. clear -I; lia.
      + apply RECS3. clear -Hj NE; lia. }
  assert (RECS' : forall j, i + 1 <= j <= 31 -> arec_hdr L m j (cnt j) 0 0) by (intros j Hj; apply RECS; clear -Hj; lia).
  step. if_cases K31; zify_cond K31; rewrite ?unsigned_lit in K31 by (clear -I; lia).   (* [comment removed for export] *)
  { (* [comment removed for export] *)
    assert (I31 : i = 31) by (clear -K31 I; lia).
    step. step. step. step. if_lit.                            (* [comment removed for export] *)
    step. step. step.                                          (* [comment removed for export] *)
    replace (Z_to_bv 64 64) with (Z_to_bv 64 (size_of_class i) : word) by (rewrite I31; reflexivity).
    eapply (TAILI 8); [clear; lia | rewrite I31, mc_31; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM]. }
  zstep. setreg 29 (Z_to_bv 64 i) ltac:(f_equal; clear; lia).   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K17; zify_cond K17; rewrite ?unsigned_lit in K17 by (clear -I; lia).   (* [comment removed for export] *)
  - (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / (32 * i))) ltac:(symmetry; apply v_divuw_lit; clear -I; lia).
    assert (SZE : size_of_class i = 32 * i) by (unfold size_of_class; replace (i <=? 16) with true by (symmetry; apply Z.leb_le; clear -K17; lia); reflexivity).
    pose proof TAILI as TL. rewrite SZE in TL. clear TAILI.
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -I; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    + destruct (mc_mid i ltac:(clear -I K17 K8; assert (5 <= i) by (destruct (Z_lt_le_dec i 5); [exfalso; pose proof (proj2 (mc_le4 i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL (1024 / (32 * i))); [clear -Q8; lia | rewrite MC; clear -Q8; lia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
    + step. step.                                              (* [comment removed for export] *)
      destruct (mc_le4 i ltac:(clear -I K8; assert (i <= 4) by (destruct (Z_lt_le_dec 4 i); [exfalso; pose proof (proj2 (mc_mid i ltac:(lia))); lia| lia]); lia)) as [MC Q8].
      eapply (TL 8); [clear; lia | rewrite MC; reflexivity | exact REC | exact RECS' | exact MI | exact MU | exact WM].
  - (* [comment removed for export] *)
    do 7 zstep.                                                (* [comment removed for export] *)
    setreg 28 (Z_to_bv 64 (size_of_class i)) ltac:(symmetry; apply size_formula2; clear -I K17 K31; lia).
    destruct (mc_big i ltac:(clear -I K17 K31; lia)) as (MC & SB & Q1).
    step.                                                      (* [comment removed for export] *)
    setreg 29 (Z_to_bv 64 (1024 / size_of_class i)) ltac:(symmetry; apply v_divuw_lit; clear -SB; lia).
    step. step. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by (clear -SB Q1; Z.div_mod_to_equations; nia).   (* [comment removed for export] *)
    2: { exfalso. clear -K8 Q1. lia. }
    eapply (TAILI (1024 / size_of_class i)); [clear -Q1 SB; Z.div_mod_to_equations; nia | rewrite MC; clear -Q1 SB; Z.div_mod_to_equations; nia | exact REC | exact RECS' | exact MI | exact MU | exact WM].
Qed.

Lemma max_cached_range : forall c, 1 <= c <= 31 -> 2 <= max_cached c <= 16 /\ max_cached c mod 2 = 0.
Proof.
  intros c Hc. unfold max_cached.
  assert (E : c = 1 \/ c = 2 \/ c = 3 \/ c = 4 \/ c = 5 \/ c = 6 \/ c = 7 \/ c = 8 \/ c = 9 \/ c = 10 \/ c = 11 \/ c = 12 \/ c = 13 \/ c = 14 \/ c = 15 \/ c = 16
              \/ c = 17 \/ c = 18 \/ c = 19 \/ c = 20 \/ c = 21 \/ c = 22 \/ c = 23 \/ c = 24 \/ c = 25 \/ c = 26 \/ c = 27 \/ c = 28 \/ c = 29 \/ c = 30 \/ c = 31) by lia.
  repeat (destruct E as [->|E]; [zfact|]). subst; zfact.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition KKref {R} (k : astate -> bool -> AM R) (c n : Z) (st2 : astate) : AM R :=
  k (put_cls c (cls_set_count (n - 1) (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2) true.

(* [comment removed for export] *)
Definition refill_tail_ret (L : alayout) (RNG : footprint) (sp : word) (st1 : astate) (c lo : Z) (fl chunks0 : list word) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  fp_le RNG RNG' /\
  exists mu' mfa' ncnt sj' (stm' stn' : word),
  let nf2 := nf + ncnt in let au2 := au + ncnt * S in
     (   mu' = mu
      \/ (nf < n /\ mu < au + (n - nf) * S /\ mu' = mu + rup (au + (n - nf) * S - mu) K_USER_MAP
          /\ rw_cells bsegs m' (RB + mu) [CB (Z.to_nat (mu' - mu)) (repeat (Z_to_bv 8 0) (Z.to_nat (mu' - mu)))]
          /\ fill_at m' (shad (RB + mu)) (shlen (mu' - mu)) 0xfa
          /\ rng RNG' (RB + mu) (mu' - mu) /\ rng RNG' (shad (RB + mu)) (shlen (mu' - mu)) /\ fp_bw RNG'))
  /\ mu <= mu' <= K_FREEARR_OFF /\ mu' mod K_USER_MAP = 0
  /\ ((n <= nf /\ ncnt = 0) \/ (nf < n /\ ncnt = (mu' - au) / S)) /\ 0 <= ncnt /\ au2 <= mu'
  /\ (   mfa' = mfa
      \/ (mfa < 4 * nf2 /\ mfa' = rup (4 * nf2) K_FREEARR_MAP
          /\ fill_at m' (shad (FA + mfa)) (shlen (mfa' - mfa)) 0xfa
          /\ rng RNG' (FA + mfa) (mfa' - mfa) /\ rng RNG' (shad (FA + mfa)) (shlen (mfa' - mfa)) /\ fp_bw RNG'))
  /\ 4 * nf2 <= mfa' <= K_FREEARR_MAX /\ mfa <= mfa' /\ mfa' mod K_FREEARR_MAP = 0
  /\ n <= nf2
  /\ u32arr bsegs m' FA (fl ++ fvals au S (Z.to_nat ncnt))
  /\ junk_at m' (FA + 4 * nf2) (mfa' - 4 * nf2)
  /\ get_cls st2 c = mkAClass mu' au2 nf2 mfa' (c_count r)
  /\ (st2 = st1 \/ st2 = put_cls c (get_cls st2 c) st1)
  /\ munch [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp);
            (RB + mu, RB + mu'); (shad (RB + mu), shad (RB + mu) + shlen (mu' - mu));
            (FA + 4 * nf, FA + mfa'); (shad (FA + mfa), shad (FA + mfa) + shlen (mfa' - mfa));
            (al_t L + 2792, al_t L + 2800); (al_t L + 2800, al_t L + 3168);
            (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
            (acache_addr L c, acache_addr L c + 4); (CHK, CHK + 4 * n)]%Z m m'
  /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
  /\ rw_cells bsegs m' RI [C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 16)
       [C8 (Z_to_bv 64 (nf2 - n)); C8 (Z_to_bv 64 mfa'); C8 (Z_to_bv 64 au2); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu'); C8 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m' (RI + 68) [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m' (RI + 72) [C8 stn']
  /\ u64arr bsegs m' (al_t L + 2800) sj' /\ length sj' = 46%nat
  /\ rw_cells bsegs m' (al_t L + 2792) [C8 stm']
  /\ rw_cells bsegs m' (acache_addr L c) [C4 (Z_to_bv 64 n); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)]
  /\ u32arr bsegs m' CHK (skipn (Z.to_nat (nf2 - n)) (fl ++ fvals au S (Z.to_nat ncnt)) ++ skipn (Z.to_nat n) chunks0)
  /\ azero m' (shad (RB + mu')) (shlen (K_FREEARR_OFF - mu'))
  /\ azero m' (shad (FA + mfa')) (shlen (K_FREEARR_MAX - mfa'))
  /\ m3_cells L m'.

Lemma refill_tail_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    (rav sp gp tp t0 t1 t2 s0v s1v a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rax a1x a3x : word)
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st1 : astate) (c lo cntc : Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st1 c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  rw_cells bsegs m (bv_unsigned sp + -32) [CB 8 fr0; C8 s1v; C8 s0v; C8 rav] ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  rw_cells bsegs m (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st1 = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_tail_ret L RNG sp st1 c lo fl chunks0 m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR rav sp gp tp t0' t1' t2' s0v s1v (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc rav) fc None m' (seg_rom bsegs))) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1v
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3870c) fc None m (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros ST CEIL LO MI TP FR MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ REC CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  set (n := max_cached c / 2) in *.
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  zstep.                                                       (* [comment removed for export] *)
  setreg 9 (Z_to_bv 64 n) ltac:(subst n; f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
                                replace (Z.of_N (32-1)) with 31 by reflexivity; change (2^31) with 2147483648;
                                rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^1) with 2; clear -MCR; Z.div_mod_to_equations; lia).
  zstep. zstep. zstep.                                         (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 (al_t L + 2768)) ltac:(f_equal; clear; lia).
  step. step. step.                                            (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  apply evtF_done. name_sp sp (-32).
  eapply getfrom_spec with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => rewrite Hsp; exact ST
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- _ <= bv_unsigned _ - _ => rewrite Hsp; clear -LO; lia
       | |- mem_inv _ _ => assumption
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => rewrite Hsp; eapply rng_sub'; [exact RSTK|]; clear -LO SPR CEIL; lia
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP | rewrite ACE; f_equal; clear; lia]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            clear KONT; rewrite ?ACE; first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM N HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros st2 RNG' m2 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' GR.
  unfold getfrom_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in GR. cbv zeta in GR.
  destruct GR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR & JR & GC2 & ST2E
                  & MU2 & WM2 & MI2 & ST2 & MTX2 & REG2 & EXH2 & STN2 & STATS2 & LSJ2 & STM2 & CH2 & AZU2 & AZF2 & MC2).
  box UD. box FD. box NCE. box ST2E. unname_sp.
  apply (rng_fp_le _ _ _ _ FPLE) in RIMG. apply (rng_fp_le _ _ _ _ FPLE) in RSTK. apply (rng_fp_le _ _ _ _ FPLE) in RT.
  assert (SHF : shad (afreearr L c + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 0x10007fff8000
                /\ shad (aregion L c + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 0x10007fff8000
                /\ 0x2008fff7000 <= shad (afreearr L c + c_mapped_free_array (get_cls st1 c))
                /\ 0x2008fff7000 <= shad (aregion L c + c_mapped_user (get_cls st1 c))).   (* [comment removed for export] *)
  { unfold afreearr, aregion, K_REGION, K_FREEARR_OFF. change (2^32) with 4294967296. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM. Z.div_mod_to_equations. lia. }
  destruct SHF as (SHF1 & SHF2 & SHF3 & SHF4).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  xport FR MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  xport REC MU2 WM2 ltac:(ub TSP; clear -SPR CEIL LO SP1 SP2 HC RIE RBE FAE ACE T0 T1 MU MUB NF MFA NEWB NEWM SHF1 SHF2 N Y TIC TB SHF3 SHF4; lia).
  clear ST MI MC MTX REG EXH STN STATS STM FL FJ CH AZU AZF.
  replace (ret_pc (Z_to_bv 64 231212)) with (Z_to_bv 64 231212 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  iprefix.
  step. if_lit.                                                (* [comment removed for export] *)
  snapshot [(acache_addr L c, acache_addr L c + 4)]%Z MUc WMc.
  box MTX2. box REG2. box EXH2. box STN2. box CH2. box STATS2. box STM2. box AR. box MU2. clear MUN WM.
  step.                                                        (* [comment removed for export] *)
  unbox MU2.
  carry AR MUc WMc ltac:(rewrite length_app, fvals_length, LFL, FAE, ACE; ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 NEWB Y TIC TB; lia).
  carry MTX2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry REG2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry EXH2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry STN2 MUc WMc ltac:(ub TSP; clear -SP1 SP2 HC RIE ACE T0 T1 Y TIC TB; lia).
  carry CH2 MUc WMc ltac:(rewrite length_app, !length_skipn, length_app, fvals_length, LFL, LCH, ACE; clear -HC NC0 N NLE NF; lia).
  carry STATS2 MUc WMc ltac:(rewrite LSJ2, ACE; clear -HC; lia).
  carry STM2 MUc WMc ltac:(rewrite ACE; clear -HC; lia).
  lazymatch goal with |- evtF _ _ ?P _ => remember P as PP eqn:HPP end.
  refresh RSTK. do 5 step.                                            (* [comment removed for export] *)
  lazymatch goal with FRM : rw_cells bsegs ?mm (bv_unsigned sp + -32) _, STK : stk bsegs _ lo _ |- _ => release_frame FRM STK (bv_unsigned sp) end.
  subst PP. apply evtF_done. eapply KONT.
  unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP. cbv zeta. fold n.
  split; [exact FPLE|]. exists mu', mfa', ncnt, sj', stm', stn'.
  split. { with_box UD ltac:(destruct DX as [Emu|(LT1 & LT & Emu & ZN & FI & G1 & G2 & BW)];
           [ left; exact Emu
           | right; split; [exact LT1|]; split; [exact LT|]; split; [exact Emu|]; split; [| split; [| split; [exact G1| split; [exact G2| exact BW]]]];
             [ eapply cells_frame; [exact ZN | exact MUc | exact WMc |]; cbn [disjoint_from cells_size csize Nat.add]; rewrite ?Z2Nat.id by (clear -MUB; lia)
             | eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from] ];
             ub TSP; rewrite RBE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB SHF2 Y TIC TB SHF3 SHF4; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact MUB|]. split; [exact MUM'|]. split; [unboxed NCE|]. split; [exact NC0|]. split; [exact NCS|].
  split. { with_box FD ltac:(destruct DX as [Emfa|(LT & Emfa & FI & G1 & G2 & BW)];
           [ left; exact Emfa
           | right; split; [exact LT|]; split; [exact Emfa|]; split; [| split; [exact G1| split; [exact G2| exact BW]]];
             eapply fill_frame; [exact FI | exact MUc | exact WMc |]; intros _; cbn [disjoint_from];
             ub TSP; rewrite FAE, ACE in *; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MFA NF NEWB NEWM SHF1 Y TIC TB; rewrite ?shad_div, ?shlen_div in *; unfold ASHOFF in *; Z.div_mod_to_equations; lia ]). }
  split; [exact NEWB|]. split; [exact NEWM|]. split; [exact NEWMOD|]. split; [exact NLE|].
  split; [exact AR|].
  split. { eapply junk_frame; [exact JR | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. ub TSP; clear -SP1 SP2 HC T0 T1 NF NC0 MFA NEWB NEWM Y TIC TB; lia. }
  split; [exact GC2|]. split; [unboxed ST2E|].
  split. { eapply munch_trans; [eapply munch_weaken; [| exact MU2] | eapply munch_weaken; [| exact MUc]]; unfold sub_fp; cbn [outside]; clear; intros x Hx; lia. }
  split; [exact WM2|]. split; [assumption|]. split; [assumption|].
  split; [exact MTX2|]. split; [exact REG2|]. split; [exact EXH2|]. split; [exact STN2|]. split; [exact STATS2|]. split; [exact LSJ2|]. split; [exact STM2|].
  split; [assumption|]. split; [exact CH2|].
  split. { eapply azero_frame; [exact AZU2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite RBE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MU MUB Y TIC TB; Z.div_mod_to_equations; lia. }
  split. { eapply azero_frame; [exact AZF2 | exact MUc | exact WMc |]. intros _; cbn [disjoint_from]. rewrite FAE, ACE. rewrite shad_div, shlen_div. unfold ASHOFF.
           ub TSP; clear -SP1 SP2 HC T0 T1 MFA NF NEWB NEWM Y TIC TB; Z.div_mod_to_equations; lia. }
  eapply m3_cells_frame; [exact MC2 | exact MUc | exact WMc |]. ub TCX. unfold AIMG_HI, AIMG_LO.
  apply Forall_cons; [cbn [fst snd]; rewrite ACE; clear -CX0 CX1 T0 T1 TIC HC Y TB CXI; with_band CX0 ltac:(lia) | apply Forall_nil].   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition refill_ret (L : alayout) (RNG : footprint) (sp : word) (st : astate) (c lo : Z) (fl chunks0 : list word) (cnt : Z -> Z) (m : amem)
    (st2 : astate) (RNG' : footprint) (m' : amem) : Prop :=
  exists m1, munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 /\ wmono bsegs m m1
  /\ refill_tail_ret L RNG sp (init_cache st) c lo fl chunks0 m1 st2 RNG' m'
  /\ (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m' j (cnt j) (max_cached j) (size_of_class j)).

Lemma init_cache_cinit : forall st, a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; [exact E| reflexivity]. Qed.
Lemma init_cache_cls : forall st c, get_cls (init_cache st) c = get_cls st c.
Proof. intros st c. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma init_cache_space : forall st, a_space_beg (init_cache st) = a_space_beg st.
Proof. intros st. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

(* [comment removed for export] *)
Lemma refill_tailK : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a5x a6x a7x s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6 (a3x : word)
    (F : bvmap 5 word) fc (m m1 : amem) (L : alayout) (st st1 : astate) (c lo cntc : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj fr0 : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  st1 = init_cache st ->
  ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK -> tp = Z_to_bv 64 ATP ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  (* [comment removed for export] *)
  munch ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
  stk bsegs m1 lo (bv_unsigned sp + -32) ->
  rw_cells bsegs m1 (bv_unsigned sp + -32) [CB 8 fr0; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m1 (acache_addr L c) [C4 (Z_to_bv 64 cntc); C4 (Z_to_bv 64 (max_cached c)); C8 (Z_to_bv 64 S)] ->
  (forall j, 1 <= j <= 31 -> j <> c -> arec_hdr L m1 j (cnt j) (max_cached j) (size_of_class j)) ->
  evtF bsegs RNG (fun ms' => implS bsegs RNG (aembed ATOP (gfa_tree st1 c n k (KKref k c n))) (epostF Q) ms')
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (acache_addr L c)) s1
             (Z_to_bv 64 (al_t L + 208)) (Z_to_bv 64 (max_cached c)) (Z_to_bv 64 AINSTANCE) a3x (Z_to_bv 64 c) a5x a6x a7x
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3x t4x t5x t6)
        F (Z_to_bv 64 0x3870c) fc None m1 (seg_rom bsegs)).
Proof.
  intros until fr0. cbv zeta.
  intros E1 CEIL LO TP MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA CXI TIC KONT MU1 WM1 MI1 ST1 FR1 REC1 RECS1. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  unfold AIMG_HI, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR. box TCX. box SCX. box TSP.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296 /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384).
  { unfold aregion_info, afreearr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE).
  assert (WOK1 : Forall (fun iv => (AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) /\ (snd iv <= al_ctx L + 152 \/ al_ctx L + 160 <= fst iv))
                  ((bv_unsigned sp - REFILL_STACK, bv_unsigned sp) :: ic_W L 1 31)%Z).
  { ub TCX. unfold AIMG_HI, AIMG_LO. apply Forall_cons; [cbn [fst snd]; clear -SPR CEIL LO CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |].   (* [comment removed for export] *)
    cbn [ic_W]. unfold acache_addr. repeat (apply Forall_cons; [cbn [fst snd]; clear -CX0 CX1 T0 T1 TIC Y TB CXI; with_band CX0 ltac:(lia) |]). apply Forall_nil. }   (* [comment removed for export] *)
  assert (GC1 : get_cls st1 c = get_cls st c) by (rewrite E1; apply init_cache_cls).
  assert (SB1 : a_space_beg st1 = al_space_beg L) by (rewrite E1, init_cache_space; exact SBE).
  (* [comment removed for export] *)
  eapply cells_frame in MTX; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in REG; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in EXH; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply cells_frame in STN; [| exact MU1 | exact WM1 | icdj ltac:(ub TSP; rewrite ?RIE; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 Y TIC TB; lia)].
  eapply u64arr_frame in STATS; [| exact MU1 | exact WM1 | rewrite LSJ; icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply cells_frame in STM; [| exact MU1 | exact WM1 | icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia)].
  eapply u32arr_frame in FL; [| exact MU1 | exact WM1 | rewrite LFL, FAE; icdj ltac:(ub TSP; unfold acache_addr; clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply cells_frame in FJ; [| exact MU1 | exact WM1 | rewrite FAE; icdj ltac:(ub TSP; unfold acache_addr; rewrite ?Z2Nat.id by (clear -NF MFA; lia); clear -SPR CEIL LO SP1 SP2 HC T0 T1 NF MFA Y TIC TB; lia)].
  eapply u32arr_frame in CH; [| exact MU1 | exact WM1 | rewrite LCH; icdj ltac:(rewrite ACE; clear -SPR CEIL LO T0 T1 HC TIC TB; lia)].
  assert (MC1 : m3_cells L m1) by (eapply m3_cells_frame; [exact MC | exact MU1 | exact WM1 | exact WOK1]).
  assert (AZU1 : azero m1 (shad (aregion L c + c_mapped_user (get_cls st c))) (shlen (3758096384 - c_mapped_user (get_cls st c)))).
  { eapply azero_frame; [exact AZU | exact MU1 | exact WM1 |]. intros _. rewrite RBE.
    assert (B : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)) + shlen (3758096384 - c_mapped_user (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUX; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  assert (AZF1 : azero m1 (shad (afreearr L c + c_mapped_free_array (get_cls st c))) (shlen (536870912 - c_mapped_free_array (get_cls st c)))).
  { eapply azero_frame; [exact AZF | exact MU1 | exact WM1 |]. intros _. rewrite FAE.
    assert (B : shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)) + shlen (536870912 - c_mapped_free_array (get_cls st c)) <= 17594333495296
                /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st c)))   (* [comment removed for export] *)
      by (rewrite shad_div, shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MFA NF; Z.div_mod_to_equations; lia).
    icdj ltac:(unfold acache_addr; clear -SPR CEIL LO T0 T1 B TIC TB; lia). }
  clear MC AZU AZF.
  rewrite <- GC1 in REG, LFL, FJ, AZU1, AZF1, MU, MUX, MUM, AUM, NF, NFA, MFA, MFAM, RFA.
  eapply (refill_tail_spec RNG k Q ra sp gp tp) with (lo := lo) (L := L);
  try lazymatch goal with
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- AIMG_HI <= al_ctx _ => assumption   (* [comment removed for export] *)
       | |- stk _ _ _ _ => exact ST1
       | |- ATOP <= _ => atop_facts; exact CEIL
       | |- mem_inv _ _ => exact MI1
       | |- m3_cells _ _ => exact MC1
       | |- rw_cells _ _ (bv_unsigned _ + _) _ => exact FR1
       | |- rw_cells _ _ (acache_addr _ _) _ => exact REC1
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length _ = _ => first [exact LSJ | exact LFL | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU1
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF1
       | |- a_space_beg _ = _ => exact SB1
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => exact RRI
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => exact RCTX
       | |- rng _ (al_t _) _ => exact RT
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
       | |- forall st2, _ => idtac
       end.
  all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
            first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TIC TB CXI; lia]).
  (* [comment removed for export] *)
  intros * TR. eapply KONT. exists m1. split; [exact MU1|]. split; [exact WM1|]. split; [rewrite <- E1; exact TR|].
  intros j Hj Hjc. unfold refill_tail_ret, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP in TR. cbv zeta in TR.
  destruct TR as (_ & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & MUB & _ & _ & NC0 & _ & _ & NEWB & NEWM & _ & NLE & _ & _ & _ & _ & MUT & WMT & _).
  eapply cells_frame; [exact (RECS1 j Hj Hjc) | exact MUT | exact WMT |]. cbn [disjoint_from cells_size csize Nat.add].
  rewrite RIE, RBE, FAE. unfold acache_addr.
  assert (B1 : shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c)) + shlen (mu' - c_mapped_user (get_cls st1 c)) <= 17594333495296
             /\ shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)) + shlen (mfa' - c_mapped_free_array (get_cls st1 c)) <= 17594333495296
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + c_mapped_user (get_cls st1 c))
             /\ 0x2008fff7000 <= shad (al_space_beg L + c * 4294967296 + 3758096384 + c_mapped_free_array (get_cls st1 c)))   (* [comment removed for export] *)
    by (rewrite !shad_div, !shlen_div; unfold ASHOFF; clear -SP1 SP2 HC MU MUB MFA NF NEWB NEWM; Z.div_mod_to_equations; lia).
  destruct B1 as (B1 & B2 & B3 & B4).
  ub TSP; clear -SPR CEIL LO SP1 SP2 HC T0 T1 MU MUB NF NC0 MFA NEWB NEWM NLE MCR Hj Hjc B1 B2 B3 B4 Y TIC TB. lia.
Qed.

Lemma refill_spec : forall RNG {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (L : alayout) (st : astate) (c lo : Z) (cnt : Z -> Z) (sj fl chunks0 : list word) (stm stn : word) (fj : list byte),
  let r := get_cls st c in let S := size_of_class c in let n := max_cached c / 2 in let CHK := acache_addr L c + 16 in
  let RB := aregion L c in let FA := afreearr L c in let RI := aregion_info L c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - REFILL_STACK ->
  mem_inv bsegs m -> tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  m3_cells L m ->
  rw_cells bsegs m RI [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 16)
     [C8 (Z_to_bv 64 nf); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m (RI + 68) [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m (RI + 72) [C8 stn] ->
  u64arr bsegs m (al_t L + 2800) sj -> length sj = 46%nat ->
  rw_cells bsegs m (al_t L + 2792) [C8 stm] ->
  u32arr bsegs m FA fl -> length fl = Z.to_nat nf -> Forall (fun w : word => bv_unsigned w < 2^31) fl ->
  rw_cells bsegs m (FA + 4 * nf) [CB (Z.to_nat (mfa - 4 * nf)) fj] ->
  u32arr bsegs m CHK chunks0 -> length chunks0 = 16%nat ->
  azero m (shad (RB + mu)) (shlen (K_FREEARR_OFF - mu)) ->
  azero m (shad (FA + mfa)) (shlen (K_FREEARR_MAX - mfa)) ->
  (* [comment removed for export] *)
  a_space_beg st = al_space_beg L -> 1 <= c < K_NUM_CLASSES ->
  0 <= au <= mu -> mu <= K_FREEARR_OFF -> mu mod K_USER_MAP = 0 -> au mod S = 0 ->
  0 <= nf -> nf <= au / S -> 4 * nf <= mfa <= K_FREEARR_MAX -> mfa mod K_FREEARR_MAP = 0 ->
  0x10007fff8000 <= al_space_beg L -> al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP -> al_space_beg L mod K_ALIGN = 0 ->
  sclr (al_ctx L) 65536 -> al_ctx L + 4096 <= ATOP -> sclr (al_t L) 4096 -> al_t L + 4096 <= ATOP -> al_t L mod 4096 = 0 ->
  (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L) ->
  (al_ctx L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L) ->
  (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L) ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG (al_ctx L) 4096 -> rng RNG (al_t L) 4096 -> rng RNG RI 128 ->
  rng RNG FA mfa ->
  (* [comment removed for export] *)
  (forall j, 1 <= j <= 31 -> arec_hdr L m j (cnt j) (max_count st j) (if a_cinit st then size_of_class j else 0)) ->
  AIMG_HI <= al_ctx L ->      (* [comment removed for export] *)
  iclr (al_t L) 4096 ->      (* [comment removed for export] *)
  (forall st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      refill_ret L RNG sp st c lo fl chunks0 cnt m st2 RNG' m' ->
      implS bsegs RNG' (aembed ATOP (KKref k c n st2)) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 refill_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until fj. cbv zeta.
  intros ST CEIL LO MI TP -> -> -> -> MC MTX REG EXH STN STATS LSJ STM FL LFL FL31 FJ CH LCH AZU AZF SBE HC MU MUX MUM AUM NF NFA MFA MFAM
         SP1 SP2 SP3 CX0 CX1 T0 T1 TAL TCX SCX TSP RIMG RSTK RCTX RT RRI RFA RECS CXI TIC KONT. band_lin.   (* [comment removed for export] *)
  pose proof T0 as TB. unfold sclr, KLS in TB.   (* [comment removed for export] *)
  rewrite cache_refill_tree_gfa. cbv zeta.
  change (fun st2 : astate => k (put_cls c (cls_set_count (max_count (init_cache st) c / 2 - 1)
     (cls_set_num_freed (c_num_freed (get_cls st2 c) - max_count (init_cache st) c / 2) (get_cls st2 c))) st2) true)
    with (KKref k c (max_count (init_cache st) c / 2)).
  replace (max_count (init_cache st) c) with (max_cached c) by (unfold max_count; rewrite init_cache_cinit; reflexivity).
  (* [comment removed for export] *)
  pose proof (@refill_tailK RNG R k Q ra sp gp tp) as TK.
  unfold AIMG_HI, AINSTANCE, K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, refill_entry in *.
  change (2^37) with 137438953472 in *.
  word_range sp SPR.
  pose proof (RECS c ltac:(clear -HC; lia)) as REC. unfold arec_hdr in REC.
  pose proof (max_cached_range c ltac:(clear -HC; lia)) as [MCR MCE].
  assert (ACE : acache_addr L c = al_t L + 208 + c * 80) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - REFILL_STACK, bv_unsigned sp)]%Z m) as MUN. pose proof (wmono_refl bsegs m) as WM.
  iprefix.
  carve_frame 32%nat ST.
  refresh RSTK.
  box MTX. box REG. box EXH. box STN. box STATS. box STM. box FL. box FJ. box CH.
  step. step. step. step.                                      (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  unfold max_count in REC, RECS |- *. revert REC RECS. destruct (a_cinit st) eqn:CI; intros REC RECS.
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear -MCR; lia).
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear -MCR; lia); [exfalso; clear -K0 MCR; lia|].   (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_weaken; [| exact MUN]; unfold sub_fp; cbn [outside]; clear; intros x Hx; tauto
         | |- forall j, _ => intros j Hj Hjc; pose proof (RECS j Hj) as RJ; unfold arec_hdr in RJ |- *;
               eapply cells_frame; [exact RJ | exact MUN | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; unfold acache_addr; clear -SPR CEIL LO T0 T1 Hj TIC TB; lia
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
  - (* [comment removed for export] *)
    rewrite sx32_lit by (clear; lia).
    step. if_lit.                                              (* [comment removed for export] *)
    zstep.                                                     (* [comment removed for export] *)
    setreg 11 (Z_to_bv 64 (acache_addr L 1 + 8)) ltac:(unfold acache_addr; f_equal; clear; lia).
    do 7 step.                                                 (* [comment removed for export] *)
    replace (Z_to_bv 64 32) with (Z_to_bv 64 (32 * 1) : word) by reflexivity.
    replace (Z_to_bv 64 (-15)) with (Z_to_bv 64 (1 - 16) : word) by reflexivity.
    step.                                                      (* [comment removed for export] *)
    eapply evtF_cut.
    { eapply (initcache_loop_spec RNG 31%nat 1 L cnt); try reflexivity; try eassumption; try (clear -T0 T1 TIC TB; atop_facts; lia).
      intros j Hj. pose proof (RECS j Hj) as RJ. unfold arec_hdr in RJ |- *. cbn [negb] in RJ.
      eapply cells_frame; [exact RJ | exact MUN | exact WM |]. cbn [disjoint_from cells_size csize Nat.add]. unfold acache_addr. clear -SPR CEIL LO T0 T1 Hj TIC TB; lia. }
    cbv beta. intros ms' (a1' & a3' & a5' & t3' & t4' & t5' & m2 & -> & MUL & WML & MI2 & RECS2).
    pose proof (RECS2 c ltac:(clear -HC; lia)) as REC2. unfold arec_hdr in REC2.
    step. rewrite sx32_lit by (clear -MCR; lia).               (* [comment removed for export] *)
    step.                                                      (* [comment removed for export] *)
    unbox MTX. unbox REG. unbox EXH. unbox STN. unbox STATS. unbox STM. unbox FL. unbox FJ. unbox CH.
    eapply TK with (st := st) (lo := lo) (cnt := cnt); try eassumption.
    all: try lazymatch goal with
         | |- _ = init_cache _ => unfold init_cache; rewrite CI; reflexivity
         | |- _ \/ _ => first [unboxed TCX | unboxed SCX | unboxed TSP]
         | |- munch _ _ _ => eapply munch_cons_trans; [exact MUN | exact MUL]
         | |- wmono _ _ _ => eapply wmono_trans; [exact WM | exact WML]
         | |- stk _ _ _ _ => eapply stk_transport_disjoint; [exact ST | exact MUL | exact WML |]; apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- rw_cells _ _ (bv_unsigned _ + _) _ => eapply cells_frame; [exact FR | exact MUL | exact WML |]; cbn [cells_size csize Nat.add];
               apply ic_W_disjoint_gen; [unfold acache_addr; clear -SPR CEIL LO T0 T1 TIC TB; lia | clear; cbn; lia | clear; lia]
         | |- forall j, _ => intros j Hj Hjc; apply RECS2; exact Hj
         end.
    all: try (unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN; change (2^37) with 137438953472;
              first [assumption | clear -MU MUX MUM AUM NF NFA MFA MFAM HC SP1 SP2 SP3 CX0 CX1 T0 T1 TAL LO CEIL TIC TB CXI; lia]).
Qed.
End CANSEC4.
