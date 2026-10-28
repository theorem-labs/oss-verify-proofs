(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocWf BllocKit BllocRep BsAtomics B_memset BsDepotInv BsDepotHash BsDepotPut BidBits BW_Combined BW_PoisonShadow BW_Leaves BW_DepotFrame BllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

Definition kAllocBegMagic : Z := 0xCC6E96B9CC6E96B9.

Definition alloc_shadow (rz size csz : Z) : list byte :=
  repeat (b8 0xfa) (Z.to_nat (rz / 8)) ++ shadow_of size ++ repeat (b8 0xfa) (Z.to_nat ((csz - rz - round_up size 8) / 8)).

Definition b1_ok (b : Z) : Prop := 0 <= b < 256 /\ b mod 128 = 0x11.

Lemma rw_cells_CB1 : forall m A b cs, rw_cells asegs m A (CB 1 [b] :: cs) -> rw_cells asegs m A (C1 b :: cs).
Proof. intros m A b cs [[[_ W] B] R]. exact (conj (conj (conj I W) B) R). Qed.

Lemma land_mask_down : forall x k j, 0 <= x < 2^k -> 0 <= j <= k -> Z.land x (2^k - 2^j) = x - x mod 2^j.
Proof.
  intros x k j Hx Hj.
  replace (2^k - 2^j)%Z with (Z.ldiff (Z.ones k) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^k)%Z with (2^j * 2^(k-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      assert (0 < 2^(k-j)) by (apply Z.pow_pos_nonneg; lia). assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (k - j))))%Z with ((2^(k-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  assert (0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
  pose proof (Z.div_mod x (2^j)%Z ltac:(hci; lia)). lia.
Qed.

Lemma land_m48_8 : forall x, 0 <= x < 2^48 -> Z.land x 281474976710648 = x - x mod 8.
Proof. intros x Hx. change 281474976710648 with (2^48 - 2^3). rewrite land_mask_down by lia. reflexivity. Qed.

Lemma d_putid_range : forall d h, d_wf d -> d_ids d + 1 < 65536 -> 1 <= d_putid d h < 65536.
Proof.
  intros d h WF CAP. unfold d_putid. pose proof (wf_ids d WF).
  destruct (Z.eqb_spec (d_find d h) 0) as [E0|NE]; [lia|].
  pose proof (d_find_range d h WF NE). lia.
Qed.

Definition hb1_of (o : Z) : Z := Z.lor (Z.land (Z.lor (o - o mod 2 ^ 2) 1) 143) 16.
Lemma hb1_facts : forall o, 0 <= o < 256 -> 0 <= hb1_of o < 256 /\ b1_ok (Z.land (hb1_of o) 243).
Proof.
  intros o Ho.
  pose proof (forall_rangeZ_spec (fun o => let v := hb1_of o in
       (0 <=? v) && (v <? 256) && (0 <=? Z.land v 243) && (Z.land v 243 <? 256) && (Z.land v 243 mod 128 =? 17)) 0 256 o) as C.
  cbn beta in C. specialize (C ltac:(hci; vm_compute; reflexivity) ltac:(hci; lia) ltac:(hci; lia)).
  cbn zeta in C. rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt, Z.eqb_eq in C. unfold b1_ok. lia.
Qed.

Definition pre_shadow (rz8 q8 csz8 : Z) : list byte :=
  repeat (b8 0xfa) (Z.to_nat rz8) ++ (repeat (b8 0) (Z.to_nat q8) ++ repeat (b8 0xfa) (Z.to_nat (csz8 - rz8 - q8))).
Lemma pre_shadow_length : forall rz8 q8 csz8, 0 <= rz8 -> 0 <= q8 -> rz8 + q8 <= csz8 ->
  Z.of_nat (length (pre_shadow rz8 q8 csz8)) = csz8.
Proof. intros. unfold pre_shadow. rewrite !length_app, !repeat_length. lia. Qed.
Lemma pre_shadow_0 : forall rz8 csz8, 0 <= rz8 <= csz8 -> pre_shadow rz8 0 csz8 = repeat (b8 0xfa) (Z.to_nat csz8).
Proof.
  intros rz8 csz8 H. unfold pre_shadow. change (repeat (b8 0) (Z.to_nat 0)) with (@nil byte). rewrite app_nil_l, Z.sub_0_r.
  rewrite <- repeat_app. f_equal. lia.
Qed.
Lemma rw_cells_C1 : forall m A b cs, rw_cells asegs m A (C1 b :: cs) -> rw_cells asegs m A (CB 1 [b] :: cs).
Proof. intros m A b cs [[[_ W] B] R]. exact (conj (conj (conj (eq_refl _) W) B) R). Qed.
Lemma b8_of_byte : forall b : byte, b8 (bv_unsigned b) = b.
Proof. intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Definition poison_postK (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo shA k v : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (shA, shA + k)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ u8arr asegs m' shA (repeat (b8 v) (Z.to_nat k)).

Lemma poison_shadow_specK : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo addr shA k v : Z) (sbs : list byte),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + 64 <= bv_unsigned sp ->
  a0 = wz addr -> a1 = wz (8 * k) -> a2 = wz v -> shA = sh addr ->
  (AHI_LO <= addr \/ 0 <= addr /\ addr + 8 * k <= ALOWSH_LO) /\ 1 <= k /\ addr + 8 * k <= aceil /\ addr mod 8 = 0 ->
  0 <= v < 256 ->
  u8arr asegs m shA sbs -> Z.of_nat (length sbs) = k ->
  rw_cells asegs m ACANPOISON [C1 (b8 1)] ->
  rw_cells asegs m AGOT_LO (map (fun v => C8 (wz v)) AGOT_VALS) ->
  rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
  rw_cells asegs m AHIGHMEMEND [C8 (wz (2^47 - 1)); C8 (wz 0); C8 (wz 0)] ->
  rw_cells asegs m (ACFLAGS + 120) [C8 (wz 0xffffffffffffffff)] ->
  rw_cells asegs m AREALMEMSET [C8 (wz AMEMSET)] ->
  evt asegs (poison_postK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo shA k v)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xbb428) fc None m (seg_rom asegs)).
Proof.
  intros until sbs. intros MI ST LO HI Ha0 Ha1 Ha2 HshA AR VR SH SHL CCAN GOT CSHB CHME CTHR CRMS. subst shA.
  assert (K8 : 8 * k / 8 = k) by (rewrite Z.mul_comm, Z.div_mul by lia; reflexivity).
  eapply evt_mono.
  - eapply (poison_shadow_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m lo addr (8 * k) v sbs); try eassumption.
    + destruct AR as (ARS & K1 & ARC & AR8). split; [| repeat split; try lia; rewrite Z.mul_comm; apply Z.mod_mul; lia].
      destruct ARS as [H|H]; [left| right]; lia.
    + rewrite K8. exact SHL.
  - intros ms' PO. unfold poison_post, poison_postK in *. rewrite K8 in PO.
    destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & MU & WM & MI' & ST' & PZ).
    unfold poisoned, SHAD, poison_bytes in PZ. destruct PZ as (_ & _ & U8).
    do 16 eexists. split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'| exact U8].
Qed.

End HCW.

Ltac lia_with_neg H := (repeat match goal with Hq : ~ _ |- _ => tryif constr_eq H Hq then fail else clear Hq end); lia.
Ltac sub_fp_struct :=
  let x := fresh "ox" in let Hx := fresh "OX" in
  unfold sub_fp; cbn [outside fst snd]; intros x Hx;
  repeat (lazymatch type of Hx with _ /\ _ => let H := fresh "OW" in destruct Hx as [H Hx] end);
  repeat (lazymatch goal with |- _ /\ _ => split end);

  first [ assumption | exact I | match goal with H : ~ _ |- _ => lia_with_neg H end | lia ].

Ltac transport_after_call segs m m' MU WM ::=
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
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ sub_fp_struct | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac post_callDep segs m :=
  let ms := fresh "ms" in let PO := fresh "PO" in
  intros ms PO; unfold put_post, depot_W in PO;
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms PO; post_call segs m.
Tactic Notation "callDep" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callDep segs m ]
  end.

Section HCW2.
  Context {HCEIL : HeapCeil}.

Record AENV (tp : word) (TSD CTX TH sb SO : Z) (T : list Z) (rest : list word) (m : mem) : Prop := mkAENV {
  e_tsdi : rw_cells asegs m 1640608 [C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]; C4 (wz 0)];
  e_tp   : rw_cells asegs m (bv_unsigned tp + -88) [C8 (wz TSD)];
  e_tsd  : rw_cells asegs m TSD [C8 (wz CTX)];
  e_ctx  : rw_cells asegs m (CTX + 152) [C8 (wz TH)];
  e_lsan : rw_cells asegs m (bv_unsigned tp + 16) [C4 (wz 0)];
  e_got2 : rw_cells asegs m 0x185d00 [C8 (wz 0x10)];
  e_thr  : rw_cells asegs m TH [C8 (wz CTX)];
  e_tid  : rw_cells asegs m (CTX + 8) [C4 (wz 0)];
  e_init : rw_cells asegs m 1645848 [C1 (b8 1)];
  e_afl  : rw_cells asegs m 2175648 [C1 (b8 0); C1 (b8 1); C1 (b8 0)];
  e_can  : rw_cells asegs m 1640604 [C1 (b8 1)];
  e_got  : rw_cells asegs m 1593472 (map (fun v => C8 (wz v)) AGOT_VALS);
  e_shb  : rw_cells asegs m 1642552 [C8 (wz 2147450880)];
  e_hme  : rw_cells asegs m 1645856 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];
  e_thresh : rw_cells asegs m 2239456 [C8 (wz 0xffffffffffffffff)];
  e_rms  : rw_cells asegs m 1601864 [C8 (wz 1535652)];
  e_fill : rw_cells asegs m 1632356 [C4 (wz 4096); C4 (wz 0); C4 (wz 0xbe)];
  e_part : rw_cells asegs m 1632397 [C1 (b8 1)];
  e_hooks : rw_cells asegs m 2239232 (repeat (C8 (wz 0)) 10);
  e_inst1 : rw_cells asegs m 1628664 [C8 (wz sb)];
  e_inst2 : rw_cells asegs m 1632248 [C8 (wz (2^40)); C2 (wz 16); C2 (wz 2048); C1 (b8 1); CB 3 [b8 0; b8 0; b8 0]];
  e_so   : rw_cells asegs m SO [C8 (wz (SO + 16)); C8 (wz (Z.of_nat (length T)))];
  e_tr   : u64arr asegs m (SO + 16) (map wz T ++ rest)
}.

End HCW2.

Ltac open_env E :=
  destruct E as [Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr];
  unfold AGOT_VALS in Egot; cbn [map] in Egot; cbn [repeat] in Ehooks.

Section HCW3.
  Context {HCEIL : HeapCeil}.

Definition allocate_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (W : list ivl) (lo size AB U rz csz P cnt mc TH id : Z) (chunks : list Z) (d' : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (j0 j1 j2 j3 : word) (b1 : Z) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz U) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch W m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)

    /\ rw_cells asegs m' P [C4 (wz (cnt - 1)); C4 (wz mc)]
    /\ u32arr asegs m' (P + 16) (wlist (rev (tl chunks)))
    /\ stk asegs m' (P + 16 + 4 * (cnt - 1)) (P + 80)
    /\ rw_cells asegs m' (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3]

    /\ rw_cells asegs m' (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz id)] /\ b1_ok b1
    /\ (rz = 16 \/ (rw_cells asegs m' AB [C8 (wz kAllocBegMagic); C8 (wz (U + -16))] /\ stk asegs m' (AB + 16) (U + -16)))
    /\ u8arr asegs m' U (repeat (b8 0xbe) (Z.to_nat (Z.min size 4096)))
    /\ stk asegs m' (U + Z.min size 4096) (AB + csz)
    /\ u8arr asegs m' (sh AB) (alloc_shadow rz size csz)

    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs d' m'.

Lemma combined_hit_specP : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo size CA sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word) (c P csz : Z),
  c = class_id size -> P = CA + 80 * c -> csz = class_size c ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
  a0 = wz AINST -> a1 = wz CA -> a2 = wz size -> a3 = wz 8 -> 17 <= size <= kMaxSize ->
  akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0 ->
  0 <= sb /\ sb + kSpaceSize <= aceil ->
  rw_cells asegs m (AINST + OI_SPACEBEG) [C8 (wz sb)] ->
  rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs m (P + 8) [C8 (wz csz)] ->
  u32arr asegs m (P + 16) (wlist (rev chunks)) -> cnt = zlen chunks -> 1 <= cnt <= 16 ->
  stk asegs m (P + 16 + 4 * cnt) (P + 80) -> Forall (fun cp => 0 <= cp < 2^32) chunks ->
  rw_cells asegs m (CA + CACHE_STATS) [C8 j0; C8 j1; C8 j2; C8 j3] ->
  evt asegs (combined_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo P CA c sb cnt mc chunks)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x96bf4) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros -> -> ->. intros. unfold PCLASS_SIZE in *.
  eapply combined_hit_spec; eauto.
Qed.

Definition aframe (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : mem) (j8 : list byte) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -128)
    [CB 8 j8; C8 (wz 1); C8 (wz 16); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

End HCW3.

