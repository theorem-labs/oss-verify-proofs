(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import EvtBridge Image.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import U.S0HarnStmt U.S0TRDefs.
From Stdlib Require Lia. Unset Lia Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(Z.div_mod_to_equations; lia).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition M100 : Z := 0x28f5c28f5c28f5c3.   (* [comment removed for export] *)
Definition M11  : Z := 0x2e8ba2e8ba2e8ba3.   (* [comment removed for export] *)
Definition M251 : Z := 0x5197f7d73404147.    (* [comment removed for export] *)

Lemma div100_magic : forall x, 0 <= x < 2 ^ 32 -> (x / 4 * M100) / 2 ^ 64 / 4 = x / 100.
Proof.
  intros x Hx. unfold M100. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 4) by lia.
  set (y := x / 4). assert (Hy : 0 <= y < 2 ^ 30) by (subst y; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  replace (x / 100) with (y / 25) by (subst y; rewrite (Zdiv.Zdiv_Zdiv x 4 25) by lia; reflexivity).
  symmetry. apply Z.div_unique_pos with (r := 11 * (y / 25) + (y mod 25) * 2951479051793528259).
  - pose proof (Z.mod_pos_bound y 25 ltac:(lia)). pose proof (Z.div_pos y 25 ltac:(lia) ltac:(lia)).
    assert (y / 25 < 2 ^ 26) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod y 25 ltac:(lia)). nia.
Qed.

Lemma div11_magic : forall x, 0 <= x < 2 ^ 32 -> (x * M11) / 2 ^ 64 / 2 = x / 11.
Proof.
  intros x Hx. unfold M11. rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) 2) by lia.
  symmetry. apply Z.div_unique_pos with (r := (x / 11) + (x mod 11) * 3353953467947191203).
  - pose proof (Z.mod_pos_bound x 11 ltac:(lia)). pose proof (Z.div_pos x 11 ltac:(lia) ltac:(lia)).
    assert (x / 11 < 2 ^ 29) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 11 ltac:(lia)). nia.
Qed.

Lemma div251_magic : forall x, 0 <= x < 2 ^ 32 ->
  let q0 := (x * M251) / 2 ^ 64 in ((x - q0) / 2 + q0) / 2 ^ 7 = x / 251.
Proof.
  intros x Hx. cbv zeta. unfold M251.
  set (q0 := x * 367465021388636487 / 2 ^ 64).
  assert (Q0 : 0 <= q0 <= x).
  { subst q0. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  replace ((x - q0) / 2 + q0) with ((x + q0) / 2).
  2:{ replace (x + q0) with ((x - q0) + q0 * 2) by lia. rewrite Z.div_add by lia. reflexivity. }
  rewrite (Zdiv.Zdiv_Zdiv _ 2 (2 ^ 7)) by lia.
  (* [comment removed for export] *)
  replace (x + q0) with ((x * 2 ^ 64 + x * 367465021388636487) / 2 ^ 64).
  2:{ subst q0. rewrite Z.add_comm, <- Z.div_add_l by lia. f_equal. lia. }
  rewrite (Zdiv.Zdiv_Zdiv _ (2 ^ 64) (2 * 2 ^ 7)) by lia.
  replace (x * 2 ^ 64 + x * 367465021388636487) with (x * (2 ^ 64 + 367465021388636487)) by lia.
  symmetry. apply Z.div_unique_pos with (r := 157 * (x / 251) + (x mod 251) * (2 ^ 64 + 367465021388636487)).
  - pose proof (Z.mod_pos_bound x 251 ltac:(lia)). pose proof (Z.div_pos x 251 ltac:(lia) ltac:(lia)).
    assert (x / 251 < 2 ^ 25) by (apply Z.div_lt_upper_bound; lia). nia.
  - pose proof (Z.div_mod x 251 ltac:(lia)). nia.
Qed.

(* [comment removed for export] *)
Lemma div100_reg : forall len, 0 <= len < 2 ^ 32 ->
  Z.shiftr ((Z.shiftr (Z.shiftr len 2 * (M100 mod 18446744073709551616)) 64) mod 18446744073709551616) 2 = len / 100.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change (M100 mod 2 ^ 64) with M100.
  assert (B : 0 <= len / 2 ^ 2 * M100 / 2 ^ 64 < 2 ^ 64).
  { unfold M100. split; [apply Z.div_pos; [| lia]; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]|].
    apply Z.div_lt_upper_bound; [lia|]. assert (len / 2 ^ 2 < 2 ^ 30) by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos len (2 ^ 2) ltac:(lia) ltac:(lia)). nia. }
  rewrite Z.mod_small by exact B. change (2 ^ 2) with 4. apply div100_magic. exact H.
Qed.
Lemma mod11_reg : forall len, 0 <= len < 2 ^ 32 ->
  bv_swrap 32 (len - (Z.shiftr ((Z.shiftr (len * (M11 mod 18446744073709551616)) 64) mod 18446744073709551616) 1 * 11) mod 18446744073709551616)
  = len mod 11.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change (M11 mod 2 ^ 64) with M11.
  assert (B : 0 <= len * M11 / 2 ^ 64 < 2 ^ 64).
  { unfold M11. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small _ _ B). change (2 ^ 1) with 2. rewrite div11_magic by exact H.
  pose proof (Z.mod_pos_bound len 11 ltac:(lia)). pose proof (Z.div_mod len 11 ltac:(lia)).
  rewrite Z.mod_small by lia. rewrite swrap32_small by lia. lia.
Qed.
Lemma mod251_reg : forall len, 0 <= len < 2 ^ 32 ->
  len - (Z.shiftr ((Z.shiftr ((len - (Z.shiftr (len * (M251 mod 18446744073709551616)) 64) mod 18446744073709551616) mod 18446744073709551616) 1
                   + Z.shiftr (len * (M251 mod 18446744073709551616)) 64) mod 18446744073709551616) 7 * 251) mod 18446744073709551616
  = len mod 251.
Proof.
  intros len H. change 18446744073709551616 with (2 ^ 64). rewrite !Z.shiftr_div_pow2 by lia. change (M251 mod 2 ^ 64) with M251.
  assert (B : 0 <= len * M251 / 2 ^ 64 <= len).
  { unfold M251. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite (Z.mod_small (len * M251 / 2 ^ 64) (2 ^ 64)) by lia. change (2 ^ 1) with 2.
  rewrite (Z.mod_small (len - len * M251 / 2 ^ 64) (2 ^ 64)) by lia.
  assert (B2 : 0 <= (len - len * M251 / 2 ^ 64) / 2 + len * M251 / 2 ^ 64 <= len).
  { pose proof (Z.div_pos (len - len * M251 / 2 ^ 64) 2 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (len - len * M251 / 2 ^ 64) 2 (len - len * M251 / 2 ^ 64) ltac:(lia) ltac:(lia)). lia. }
  rewrite (Z.mod_small ((len - len * M251 / 2 ^ 64) / 2 + len * M251 / 2 ^ 64) (2 ^ 64)) by lia.
  pose proof (div251_magic len H) as E. cbv zeta in E. rewrite E.
  pose proof (Z.mod_pos_bound len 251 ltac:(lia)). pose proof (Z.div_mod len 251 ltac:(lia)).
  rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition imgb (a : Z) (n : nat) : list byte := match image_bytes s0segs a n with Some bs => bs | None => [] end.
Lemma ro_cells_C8_of_CB : forall m A bs (v : word), ro_cells s0segs m A [CB 8 bs] -> Mem.le8 v = bs -> ro_cells s0segs m A [C8 v].
Proof. intros m A bs v [W B] E. split; [cbn; split; exact Logic.I|]. cbn [cells_bytes cbytes] in *. rewrite E. exact B. Qed.
Lemma map_unsigned_inj : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma M100_ro : forall m, mem_inv s0segs m -> ro_cells s0segs m 0x10d40 [C8 (Z_to_bv 64 M100)].
Proof. intros m MI. eapply ro_cells_C8_of_CB; [apply (ro_cells_image s0segs m _ (imgb 0x10d40 8)); [exact MI | vm_compute; reflexivity | lia | first [cbn; lia | vm_compute; intros; discriminate] ] | apply map_unsigned_inj; vm_compute; reflexivity]. Qed.
Lemma M11_ro : forall m, mem_inv s0segs m -> ro_cells s0segs m 0x10d10 [C8 (Z_to_bv 64 M11)].
Proof. intros m MI. eapply ro_cells_C8_of_CB; [apply (ro_cells_image s0segs m _ (imgb 0x10d10 8)); [exact MI | vm_compute; reflexivity | lia | first [cbn; lia | vm_compute; intros; discriminate] ] | apply map_unsigned_inj; vm_compute; reflexivity]. Qed.
Lemma M251_ro : forall m, mem_inv s0segs m -> ro_cells s0segs m 0x10d50 [C8 (Z_to_bv 64 M251)].
Proof. intros m MI. eapply ro_cells_C8_of_CB; [apply (ro_cells_image s0segs m _ (imgb 0x10d50 8)); [exact MI | vm_compute; reflexivity | lia | first [cbn; lia | vm_compute; intros; discriminate] ] | apply map_unsigned_inj; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition nZ_of (len : Z) : Z := len + 600 + len / 100.
Definition bs_of (len : Z) : Z := Z.min (len mod 11) 8 + 1.
Definition wf_of (len : Z) : Z := len mod 251.

Section W.
  Variables (ra0 sp0 gp tp : word) (x8 x9 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Let usp := bv_unsigned sp0.
  Variable lo : Z.
  Hypothesis LO : lo <= bv_unsigned sp0 - 65536.
  Hypothesis LOI : 0x66000 <= lo.
  Hypothesis SPH : bv_unsigned sp0 + 48 <= 2 ^ 47.
  Hypothesis SPA : bv_unsigned sp0 mod 16 = 0.
  (* [comment removed for export] *)
  Set Default Proof Using "LO LOI SPH SPA".

  Definition hsp : word := Z_to_bv 64 (usp - 48).
  (* [comment removed for export] *)
  Definition hst (pc : Z) (ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 : word) (m : mem) : machine_state :=
    MS (mkR ra hsp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
       F (Z_to_bv 64 pc) fc None m (seg_rom s0segs).
  (* [comment removed for export] *)
  Definition upper : list cell := [C8 x19; C8 x18; C8 x9; C8 x8; C8 ra0].

  Local Ltac prep := unfold hst, hsp; replace (usp - 48) with (bv_unsigned sp0 + -48) by (subst usp; lia).

  (* [comment removed for export] *)
  Lemma hG1 : forall t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : mem) (src len : Z),
    stk s0segs m lo usp -> mem_inv s0segs m -> 0 <= len < 2 ^ 26 -> 0 <= src < 2 ^ 64 ->
    evt s0segs (fun ms' => exists t0' t1' t2' a1' (m' : mem) (j4 : list byte),
        ms' = hst 0x29504 (Z_to_bv 64 0x13a6c) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 src) (Z_to_bv 64 (nZ_of len)) a1' a2 a3 a4 a5 a6 a7 x18 x19 t3 t4 t5 t6 m'
        /\ munch [(usp - 48, usp)] m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
        /\ rw_cells s0segs m' (usp - 48) ([CB 4 j4; C4 (Z_to_bv 64 (nZ_of len))] ++ upper)
        /\ stk s0segs m' lo (usp - 48))
      (MS (mkR ra0 sp0 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 src) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x13a20) fc None m (seg_rom s0segs)).
  Proof.
    intros until len. intros ST MI LEN SRC.
    prep. replace (usp - 48) with (bv_unsigned sp0 + -48) by (subst usp; lia). unfold usp in ST |- *.
    pose proof (munch_refl [(bv_unsigned sp0 + -48, bv_unsigned sp0)] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    pose proof (M100_ro m MI) as ROa.
    carve_frame 48%nat ST.
    do 8 step.   (* [comment removed for export] *)
    step. step.  (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (len + ?e + 600)] =>
      replace (len + e + 600) with (nZ_of len) by (unfold nZ_of; rewrite div100_reg by lia; lia) end.
    assert (NZ : 0 <= nZ_of len < 2 ^ 27) by (unfold nZ_of; pose proof (Z.div_pos len 100 ltac:(lia) ltac:(lia)); pose proof (Z.mul_div_le len 100 ltac:(lia)); lia).
    step.        (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    rewrite (Z.mod_small (nZ_of len) 4294967296) by lia.
    step.        (* [comment removed for export] *)
    unfold upper. cbn [app]. finish. exact FR.
  Qed.

  (* [comment removed for export] *)
  Local Ltac gfin := unfold hst, hsp; apply evt_done; reflexivity.
  Local Ltac gfinx := unfold hst, hsp; apply evt_done; repeat eexists; reflexivity.

  (* [comment removed for export] *)
  Lemma hG2 : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 (m : mem) (src len r : Z),
    mem_inv s0segs m -> 0 <= len < 2 ^ 26 -> 0 <= src < 2 ^ 64 -> 0 <= r < 2 ^ 64 ->
    evt s0segs (fun ms' => exists t0' t1' t2',
        ms' = hst 0x15e1c (Z_to_bv 64 0x13adc) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 src)
                  (Z_to_bv 64 r) (Z_to_bv 64 (usp - 48 + 4)) (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 (bs_of len)) (Z_to_bv 64 0) (Z_to_bv 64 (wf_of len)) a7
                  (Z_to_bv 64 r) s3 t3 t4 t5 t6 m)
      (hst 0x13a6c ra t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 src) (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m).
  Proof.
    intros until r. intros MI LEN SRC HR. prep.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    pose proof (M11_ro m MI) as ROb. pose proof (M251_ro m MI) as ROc.
    step. step. step. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    rewrite mod11_reg by lia. pose proof (Z.mod_pos_bound len 11 ltac:(lia)) as M11B.
    step. step. (* [comment removed for export] *)
    step. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (len mod 11) with (bs_of len - 1) by (unfold bs_of; lia).
      step. step. zstep. (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. step. zstep. zstep. (* [comment removed for export] *)
      rewrite mod251_reg by lia. replace (bs_of len - 1 + 1) with (bs_of len) by lia.
      zstep. (* [comment removed for export] *) rewrite Z.add_0_r, (swrap32_small len) by lia.
      step. step. step. step. step. (* [comment removed for export] *)
      replace (bv_unsigned sp0 + -44) with (bv_unsigned sp0 + -48 + 4) by lia. gfinx.
    - (* [comment removed for export] *)
      replace (bs_of len) with 9 by (unfold bs_of; lia).
      step. step. step. zstep. (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. step. zstep. zstep. (* [comment removed for export] *)
      rewrite mod251_reg by lia.
      zstep. (* [comment removed for export] *) rewrite Z.add_0_r, (swrap32_small len) by lia.
      step. step. step. step. step. (* [comment removed for export] *)
      replace (bv_unsigned sp0 + -44) with (bv_unsigned sp0 + -48 + 4) by lia. gfinx.
  Qed.

  (* [comment removed for export] *)
  Lemma hG3f : forall ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 (m : mem) (rc zb : Z),
    mem_inv s0segs m -> rc mod 2 ^ 64 <> 0 ->
    evt s0segs (fun ms' => ms' = hst 0x293c4 (Z_to_bv 64 0x13b48) t0 t1 t2 s0 s1 (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) (Z_to_bv 64 zb) t3 t4 t5 t6 m)
      (hst 0x13adc ra t0 t1 t2 s0 s1 (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m).
  Proof.
    intros until zb. intros MI RC. prep.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; apply RC; rewrite <- K; reflexivity|].
    step. step. step. step. gfin.
  Qed.

  (* [comment removed for export] *)
  Lemma hG3t : forall ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 (m : mem) (len : Z) (j4 : list byte),
    mem_inv s0segs m -> 0 <= len < 2 ^ 26 -> rw_cells s0segs m (usp - 48) [CB 4 j4] ->
    evt s0segs (fun ms' => exists (m' : mem),
        ms' = hst 0x29504 (Z_to_bv 64 0x13afc) t0 t1 t2 (Z_to_bv 64 len) s1 (Z_to_bv 64 (2 * len)) a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m'
        /\ munch [(usp - 48, usp - 44)] m m' /\ wmono s0segs m m' /\ mem_inv s0segs m'
        /\ rw_cells s0segs m' (usp - 48) [C4 (Z_to_bv 64 (2 * len))])
      (hst 0x13adc ra t0 t1 t2 (Z_to_bv 64 len) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m).
  Proof.
    intros until j4. intros MI LEN FR. prep. replace (usp - 44) with (bv_unsigned sp0 + -44) by (subst usp; lia). unfold usp in FR.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp0 + -48) in FR by lia.
    pose proof (munch_refl [(bv_unsigned sp0 + -48, bv_unsigned sp0 + -44)] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity].
    zstep. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 len 1) by lia. change (2 ^ 1) with 2. rewrite (Z.mul_comm len 2).
    step. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *) rewrite (Z.mod_small (2 * len) 4294967296) by lia.
    step. (* [comment removed for export] *)
    finish.
  Qed.

  (* [comment removed for export] *)
  Lemma hG4 : forall ra t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 (m : mem) (len zb r2 nz1 : Z),
    mem_inv s0segs m -> 0 <= len < 2 ^ 26 -> 0 <= nz1 < 2 ^ 31 -> rw_cells s0segs m (usp - 44) [C4 (Z_to_bv 64 nz1)] ->
    evt s0segs (fun ms' => exists t0' t1' t2',
        ms' = hst 0x15f2c (Z_to_bv 64 0x13b18) t0' t1' t2' (Z_to_bv 64 len) s1
                  (Z_to_bv 64 r2) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 zb) (Z_to_bv 64 nz1) (Z_to_bv 64 (len mod 2)) (Z_to_bv 64 0) a6 a7
                  (Z_to_bv 64 zb) (Z_to_bv 64 r2) t3 t4 t5 t6 m)
      (hst 0x13afc ra t0 t1 t2 (Z_to_bv 64 len) s1 (Z_to_bv 64 r2) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m).
  Proof.
    intros until nz1. intros MI LEN NZ1 CZ. prep. unfold usp in CZ. replace (bv_unsigned sp0 - 44) with (bv_unsigned sp0 + -44) in CZ by lia.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. zstep. (* [comment removed for export] *) rewrite sx32_small by (rewrite unsigned_lit by lia; lia).
    zstep. (* [comment removed for export] *) change (Z.land len 1) with (Z.land len (Z.ones 1)). rewrite Z.land_ones by lia. change (2 ^ 1) with 2.
    step. step. step. step. (* [comment removed for export] *)
    gfinx.
  Qed.

  (* [comment removed for export] *)
  Lemma hG5f : forall ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 (m : mem) (rc zb : Z),
    mem_inv s0segs m -> rc mod 2 ^ 64 <> 0 ->
    evt s0segs (fun ms' => ms' = hst 0x293c4 (Z_to_bv 64 0x13b40) t0 t1 t2 s0 s1 (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m)
      (hst 0x13b18 ra t0 t1 t2 s0 s1 (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m).
  Proof.
    intros until zb. intros MI RC. prep.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. if_cases K; zify_cond K; [| exfalso; apply RC; rewrite <- K; reflexivity].
    step. step. gfin.
  Qed.

  (* [comment removed for export] *)
  Lemma hG5t : forall ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (m : mem) (len src zb ob : Z),
    mem_inv s0segs m -> 0 <= len < 2 ^ 26 -> rw_cells s0segs m (usp - 48) [C4 (Z_to_bv 64 len)] ->
    evt s0segs (fun ms' => exists t0' t1' t2',
        ms' = hst 0x30678 (Z_to_bv 64 0x13b34) t0' t1' t2' (Z_to_bv 64 len) (Z_to_bv 64 src)
                  (Z_to_bv 64 src) (Z_to_bv 64 ob) (Z_to_bv 64 len) a3 a4 a5 a6 a7 (Z_to_bv 64 zb) (Z_to_bv 64 ob) t3 t4 t5 t6 m)
      (hst 0x13b18 ra t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 src) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) (Z_to_bv 64 ob) t3 t4 t5 t6 m).
  Proof.
    intros until ob. intros MI LEN C0. prep. unfold usp in C0. replace (bv_unsigned sp0 - 48) with (bv_unsigned sp0 + -48) in C0 by lia.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|].
    zstep. (* [comment removed for export] *)
    replace (zx32 (Z_to_bv 64 len)) with (Z_to_bv 64 len) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
    step. if_cases K2; zify_cond K2; [exfalso; apply K2; reflexivity|].   (* [comment removed for export] *)
    step. step. step. step. (* [comment removed for export] *)
    gfinx.
  Qed.

  (* [comment removed for export] *)
  Lemma hG6 : forall ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 (m : mem) (zb : Z),
    mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = hst 0x293c4 (Z_to_bv 64 0x13b40) t0 t1 t2 s0 s1 (Z_to_bv 64 zb) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m)
      (hst 0x13b34 ra t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 zb) s3 t3 t4 t5 t6 m).
  Proof.
    intros until zb. intros MI. prep.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. if_cases K; zify_cond K; [exfalso; apply K; reflexivity|].   (* [comment removed for export] *)
    step. step. gfin.
  Qed.

  (* [comment removed for export] *)
  Lemma hG7 : forall ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 t4 t5 t6 (m : mem) (ob : Z),
    mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = hst 0x293c4 (Z_to_bv 64 0x13b48) t0 t1 t2 s0 s1 (Z_to_bv 64 ob) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ob) t3 t4 t5 t6 m)
      (hst 0x13b40 ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 ob) t3 t4 t5 t6 m).
  Proof.
    intros until ob. intros MI. prep.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    step. step. gfin.
  Qed.

  (* [comment removed for export] *)
  Lemma hG8 : forall ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 (m : mem) (j8 : list byte),
    rw_cells s0segs m (usp - 48) [CB 8 j8] -> rw_cells s0segs m (usp - 40) upper -> stk s0segs m lo (usp - 48) -> mem_inv s0segs m ->
    evt s0segs (fun ms' => ms' = MS (mkR ra0 sp0 gp tp t0 t1 t2 x8 x9 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (ret_pc ra0) fc None m (seg_rom s0segs)
                           /\ stk s0segs m lo usp)
      (hst 0x13b48 ra t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 t3 t4 t5 t6 m).
  Proof.
    intros until j8. intros LOW FR ST MI. prep. unfold usp in LOW, FR, ST |- *. unfold upper in FR.
    replace (bv_unsigned sp0 - 48) with (bv_unsigned sp0 + -48) in LOW, ST by lia.
    replace (bv_unsigned sp0 - 40) with (bv_unsigned sp0 + -40) in FR by lia.
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl s0segs m) as WM.
    release_frame LOW ST (bv_unsigned sp0 + -40).
    step. (* [comment removed for export] *)
    do 5 step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp0).
    step. step. (* [comment removed for export] *)
    apply evt_done. split; [reflexivity | exact ST].
  Qed.
End W.
