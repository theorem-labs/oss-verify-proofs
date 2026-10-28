(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV FPStepsB Reach.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib GrayLib LeptDefs LeptStructs LeptArith DitherLib DitherLoop LeptExecB LeptFPB LeptArithB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpBound FpReal FpSiteD.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptUb V2_code_pixBilateralGrayExact.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac fpn := cbn [fp_regs fp_csr]; unfold fpv_sgnj; cbn [fpv_box];
  repeat first [ rewrite fpv_read_S_box | rewrite fpv_read_D_same | rewrite fpv_read_other by reg_neq_tac
               | rewrite fpv_get_same | rewrite fpv_get_other by reg_neq_tac ].
Ltac fz Hz := cbn [fp_csr]; repeat apply fpv_frm_acc; exact Hz.
(* [comment removed for export] *)
Ltac zvalw := gres; pin; imm_norm; rewrite ?zbv_addiw_small by lia; rewrite ?zbv_addw_small by lia; rewrite ?zbv_mulw_small by lia; rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia].
Ltac zvw F D v := stepat F D v zvalw.

Lemma wr_readable_bge : forall {fx : FPState}, wr_readable SEGS.
Proof.
  intros fx seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.
(* [comment removed for export] *)
#[local] Instance bge_fxd : FPState | 100 := mkFP bvmap_empty (Z_to_bv 32 0).

(* [comment removed for export] *)
Lemma zbv_srai63 : forall k, (- 2 ^ 63 <= k < 2 ^ 63)%Z -> v_srai (Z_to_bv 64 k) 63 = Z_to_bv 64 (if (k <? 0)%Z then -1 else 0)%Z.
Proof.
  intros k Hk. unfold v_srai. rewrite bv_signed_Zs by lia. f_equal. rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z.ltb_spec k 0) as [N|P]; cbv beta iota.
  - symmetry. apply Z.div_unique with (r := (k + 2 ^ 63)%Z); lia.
  - apply Z.div_small. lia.
Qed.
Lemma abs_idiom64 : forall k, (- 2 ^ 63 < k < 2 ^ 63)%Z ->
  v_sub (v_xor (Z_to_bv 64 k) (v_srai (Z_to_bv 64 k) 63)) (v_srai (Z_to_bv 64 k) 63) = Z_to_bv 64 (Z.abs k).
Proof.
  intros k Hk. rewrite zbv_srai63 by lia. destruct (Z.ltb_spec k 0) as [N|P]; cbv beta iota.
  - unfold v_xor. rewrite !u_Z2bv_mod.
    assert (E1 : (k mod 2 ^ 64 = k + 2 ^ 64)%Z) by (symmetry; apply Z.mod_unique with (q := (-1)%Z); lia).
    assert (E2 : ((-1) mod 2 ^ 64 = 2 ^ 64 - 1)%Z) by (symmetry; apply Z.mod_unique with (q := (-1)%Z); lia).
    rewrite E1, E2. rewrite lxor_ones64B by lia. rewrite zbv_sub. f_equal. lia.
  - unfold v_xor. rewrite !u_Z2bv by lia. rewrite Z.lxor_0_r. rewrite zbv_sub. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma row_geo : forall d W hs r, (d mod 4 = 0)%Z -> (W mod 4 = 0)%Z -> (0 <= W)%Z -> (0 <= r < hs)%Z ->
  ((d + W * r) mod 4 = 0 /\ d <= d + W * r /\ d + W * r + W <= d + W * hs)%Z.
Proof.
  intros d W hs r Hd HW HW0 Hr.
  assert (A1 : (0 <= W * r)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (A2 : (W * (r + 1) <= W * hs)%Z) by (apply Z.mul_le_mono_nonneg_l; lia).
  split; [|lia].
  rewrite Z.add_mod by lia. rewrite Z.mul_mod by lia. rewrite Hd, HW. rewrite Z.mul_0_l. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ge_rd_half : forall (m : word -> option byte), exists bs, rdn SEGS m (Z_to_bv 64 0x125b8) 8 = Some bs /\ length bs = 8%nat.
Proof.
  intros m. eapply rdn_rom_any.
  match goal with |- rdn ?sg ?mm ?a ?n = Some ?e =>
    let v := eval vm_compute in (rdn sg mm a n) in
    lazymatch v with Some ?bs => unify e bs; vm_compute; reflexivity end end.
Qed.

Lemma ge_cst_vals : (p_half_d = 0x3fe0000000000000 /\ p_lo_d = 0xc1e0000000200000 /\ p_hi_d = 0x41e0000000000000 /\ p_one_s = 0x3f800000 /\ p_zero = 0)%Z.
Proof. repeat split; reflexivity. Qed.

Section Segs.
Variable rom : word -> option byte.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition ge_fp (fr fr' : bvmap 5 word) : Prop :=
  forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> reg_get fr' r = reg_get fr r.
Definition ge_fq (fr fr' : bvmap 5 word) : Prop :=
  forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> reg_get fr' r = reg_get fr r.
Definition ge_acc (fr : bvmap 5 word) (s n : Z) : Prop :=
  reg_get fr 13%bv = nan_box (Z_to_bv 32 s) /\ reg_get fr 14%bv = nan_box (Z_to_bv 32 n).
(* [comment removed for export] *)
Definition GML : list reg := [1; 18; 21; 22; 23; 25; 26; 27]%bv.
Definition GKL : list reg := [1; 6; 18; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition GJL : list reg := [1; 5; 6; 7; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition GIL : list reg := [1; 5; 6; 7; 11; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition GNL : list reg := [1; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Lemma gm_loop : forall (n : nat) fr0 regs0 fr cs regs (M : word -> option byte) (Wt krow rrow cval rb col m : Z)
    (keli arrk rng arrr k kt s nv : Z) (kf : Z -> Z -> Z) (rf : Z -> Z) (cb ctr : bool),
  Z.of_nat n = (41 - m)%Z -> (0 <= m <= 40)%Z -> frm_zero cs ->
  (rb mod 4 = 0)%Z -> (Wt mod 4 = 0)%Z -> (4096 <= rb)%Z -> (rb + Wt <= 2 ^ 47)%Z -> (0 <= col)%Z -> (col + 40 < Wt)%Z -> (Wt <= 2 ^ 26)%Z ->
  (4096 <= krow)%Z -> (krow + 164 <= 2 ^ 47)%Z -> (krow mod 4 = 0)%Z -> (4096 <= rrow)%Z -> (rrow + 1024 <= 2 ^ 47)%Z -> (rrow mod 4 = 0)%Z ->
  (0 <= cval <= 255)%Z -> (0 <= k <= 40)%Z -> (4096 <= arrk)%Z -> (arrk + 328 <= 2 ^ 47)%Z -> (arrk mod 8 = 0)%Z ->
  (4096 <= arrr)%Z -> (arrr + 8 <= 2 ^ 47)%Z -> (arrr mod 8 = 0)%Z ->
  (forall p, (rb <= p < rb + Wt)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) ->
  rdn SEGS M (Z_to_bv 64 (keli + 16)) 8 = Some (Z_to_le_bytes 8 arrk) -> rdn SEGS M (Z_to_bv 64 (arrk + 8 * k)) 8 = Some (Z_to_le_bytes 8 krow) ->
  rdn SEGS M (Z_to_bv 64 (rng + 16)) 8 = Some (Z_to_le_bytes 8 arrr) -> rdn SEGS M (Z_to_bv 64 arrr) 8 = Some (Z_to_le_bytes 8 rrow) ->
  (forall q, (0 <= q <= 40)%Z -> rdn SEGS M (Z_to_bv 64 (krow + 4 * q)) 4 = Some (Z_to_le_bytes 4 (kf k q)) /\ FB fmt_single 1 (kf k q)) ->
  (forall d, (0 <= d <= 255)%Z -> rdn SEGS M (Z_to_bv 64 (rrow + 4 * d)) 4 = Some (Z_to_le_bytes 4 (rf d)) /\ FB fmt_single 1 (rf d)) ->
  (rf 0 = p_one_s)%Z ->
  (ctr = true -> (kf k 20 = p_one_s)%Z /\ exists b, rdn SEGS M (Z_to_bv 64 (Z.lxor (rb + col + 20) 3)) 1 = Some [b] /\ cval = u b) ->
  (ctr = true -> cb = true \/ (m <= 20)%Z) ->
  getr regs 23 = Z_to_bv 64 m -> getr regs 22 = Z_to_bv 64 (4 * m) -> getr regs 24 = Z_to_bv 64 (8 * k) -> getr regs 20 = Z_to_bv 64 rb ->
  getr regs 17 = Z_to_bv 64 col -> getr regs 31 = Z_to_bv 64 164 -> getr regs 29 = Z_to_bv 64 0 -> getr regs 7 = Z_to_bv 64 keli ->
  getr regs 8 = Z_to_bv 64 rng -> getr regs 28 = Z_to_bv 64 cval -> getr regs 14 = Z_to_bv 64 3 -> getr regs 13 = Z_to_bv 64 1 ->
  ge_acc fr s nv -> ge_avg kt cb s nv -> (0 <= kt)%Z -> (kt + (41 - m) <= 2048)%Z ->
  regs_agree (fun r => In r GML) regs0 regs -> ge_fq fr0 fr ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3b1d4 : word) M rom)
    (fun fin => exists fr' cs' regs' s' nv' cb', fin = @mkst (mkFP fr' cs') regs' (0x3b2d4 : word) M rom /\ frm_zero cs' /\
                regs_agree (fun r => In r GML) regs0 regs' /\ ge_fq fr0 fr' /\
                ge_acc fr' s' nv' /\ ge_avg (kt + (41 - m)) cb' s' nv' /\ (cb = true -> cb' = true) /\ (ctr = true -> cb' = true)).
Proof.
  intros n; induction n as [|n IH];
    intros fr0 regs0 fr cs regs M Wt krow rrow cval rb col m keli arrk rng arrr k kt s nv kf rf cb ctr
      Hn Hm FZ Hrb4 HWt4 Hrb1 Hrb2 Hcol0 Hcol1 HWt Hkr1 Hkr2 Hkr4 Hrr1 Hrr2 Hrr4 Hcv Hk Hak1 Hak2 Hak8 Har1 Har2 Har8
      Hrow Rarrk Rkrow Rarrr Rrrow Hkf Hrf Hrf0 Hctr Hcb H23 H22 H24 H20 H17 H31 H29 H7 H8 H28 H14 H13
      ACC AVG Hkt0 Hkt1 AG FQ; [lia|].
  assert (CL : forall z, (0 <= z < 2 ^ 32)%Z -> bv_extract 0%N 32%N (le_bytes_to_word (Z_to_le_bytes 4 z)) = Z_to_bv 32 z).
  { intros z Hz. apply bv_eq. unfold le_bytes_to_word. rewrite lez4 by lia. rewrite (u_Z2bv z) by lia.
    change (bv_extract 0%N 32%N (Z_to_bv 64 z)) with (low32 (Z_to_bv 64 z)).
    rewrite low32_unsigned, (u_Z2bv z), fp_u_Z2bv32 by lia.
    apply bv_wrap_small. change (bv_modulus 32) with (2 ^ 32)%Z. lia. }
  assert (M4 : forall x y, (x mod 4 = 0)%Z -> ((x + 4 * y) mod 4 = 0)%Z).
  { intros x y Hx. replace (x + 4 * y)%Z with (x + y * 4)%Z by ring. rewrite Z.mod_add by lia. exact Hx. }
  assert (M8 : forall x y, (x mod 8 = 0)%Z -> ((x + 8 * y) mod 8 = 0)%Z).
  { intros x y Hx. replace (x + 8 * y)%Z with (x + y * 8)%Z by ring. rewrite Z.mod_add by lia. exact Hx. }
  destruct (Hkf m ltac:(lia)) as [Rkf FBsp].
  assert (HP : (rb <= Z.lxor (rb + col + m) 3 < rb + Wt)%Z).
  { rewrite lxor3_eq by lia.
    pose proof (Z.div_mod (rb + col + m) 4 ltac:(lia)) as D1.
    pose proof (Z.mod_pos_bound (rb + col + m) 4 ltac:(lia)) as D2.
    pose proof (Z.div_mod rb 4 ltac:(lia)) as D3.
    pose proof (Z.div_mod Wt 4 ltac:(lia)) as D4.
    lia. }
  destruct (Hrow _ HP) as [b Rb].
  assert (Hb : (0 <= bv_unsigned b < 256)%Z) by (pose proof (bv_unsigned_in_range _ b) as R; change (bv_modulus 8) with 256%Z in R; lia).
  assert (Hd : (0 <= Z.abs (cval - bv_unsigned b) <= 255)%Z) by lia.
  destruct (Hrf _ Hd) as [Rrf FBrg].
  destruct (ge_avg_range _ _ _ _ AVG) as [Rs Rnv].
  assert (Hflag : (cb || (ctr && (m =? 20)%Z))%bool = true -> cb = true \/ (kf k m = p_one_s /\ rf (Z.abs (cval - bv_unsigned b)) = p_one_s)).
  { intro E. destruct cb; [left; reflexivity|]. right. destruct ctr; [|discriminate E].
    cbn [orb andb] in E. apply Z.eqb_eq in E. subst m.
    destruct (Hctr eq_refl) as (Hk20 & b0 & Rb0 & Hcv0).
    rewrite Rb in Rb0. injection Rb0 as Eb. subst b0.
    split; [exact Hk20|]. rewrite Hcv0, Z.sub_diag. exact Hrf0. }
  assert (Hcb1 : ctr = true -> (cb || (ctr && (m =? 20)%Z))%bool = true \/ (m + 1 <= 20)%Z).
  { intro Hc. destruct (Hcb Hc) as [E|E].
    - left. rewrite E. reflexivity.
    - destruct (Z.eq_dec m 20) as [->|N].
      + left. rewrite Hc. destruct cb; reflexivity.
      + right. lia. }
  pose proof (ge_tap_full kt cb (cb || (ctr && (m =? 20)%Z))%bool s nv (kf k m) (rf (Z.abs (cval - bv_unsigned b))) RNE (bv_unsigned b)
    AVG Hkt0 ltac:(lia) FBsp FBrg ltac:(lia) Hflag) as T.
  cbv zeta in T. destruct T as (AVG1 & Rsp & Rrg & Rbf & Rkern & Rs1 & Rn1).
  pose proof ACC as ACC0. unfold ge_acc in ACC0. destruct ACC0 as [A13 A14].
  assert (S13 : fpv_read fr FMT_S 13 = s).
  { cbn [fpv_read]. rewrite A13, fpv_unbox_box. apply fp_u_Z2bv32. lia. }
  assert (S14 : fpv_read fr FMT_S 14 = nv).
  { cbn [fpv_read]. rewrite A14, fpv_unbox_box. apply fp_u_Z2bv32. lia. }
  norm_pc.
  stepat F_3b1d4 D_3b1d4 (Z_to_bv 64 (col + m)) ltac:(gres; pin; rewrite zbv_add; reflexivity).
  stepi F_3b1d8 D_3b1d8.
  lazymatch goal with |- context [v_addw ?x ?y] =>
    replace (v_addw x y) with (Z_to_bv 64 (col + m)) by (symmetry; gres; pin; apply zbv_addw_small; lia) end.
  stepb_ft F_3b1dc D_3b1dc ltac:(rewrite c_eq_Zm; apply Z.eqb_refl).
  stepat F_3b1e0 D_3b1e0 (Z_to_bv 64 (col + m)) ltac:(gres; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
  stepat F_3b1e4 D_3b1e4 (Z_to_bv 64 (rb + col + m)) ltac:(gres; pin; rewrite zbv_add; f_equal; lia).
  stepat F_3b1e8 D_3b1e8 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
  stepb_ft F_3b1ec D_3b1ec ltac:(pin; first [reflexivity | vm_compute; reflexivity]).
  stepat F_3b1f0 D_3b1f0 (Z_to_bv 64 0) ltac:(gres; pin; rewrite zbv_sltu_ge by lia; reflexivity).
  stepat F_3b1f4 D_3b1f4 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_slti0 by lia; reflexivity).
  stepat F_3b1f8 D_3b1f8 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
  stepat F_3b1fc D_3b1fc (Z_to_bv 64 1) ltac:(gres; imm_norm; first [reflexivity | bveq]).
  stepb_ft F_3b200 D_3b200 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepb_ft F_3b204 D_3b204 ltac:(pin; rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
  stepb_ft F_3b208 D_3b208 ltac:(pin; first [reflexivity | vm_compute; reflexivity]).
  stepLD F_3b20c D_3b20c (Z_to_le_bytes 8 arrk) (Z_to_bv 64 arrk) ltac:(rewrite zbv_addi; exact Rarrk) ltac:(apply lez8; lia).
  stepat F_3b210 D_3b210 (Z_to_bv 64 (arrk + 8 * k)) ltac:(gres; pin; rewrite zbv_add; reflexivity).
  stepat F_3b214 D_3b214 (Z_to_bv 64 1) ltac:(gres; rewrite zbv_snez by lia; reflexivity).
  stepat F_3b218 D_3b218 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
  stepb_ft F_3b21c D_3b21c ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepb_ft F_3b220 D_3b220 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
  stepb_ft F_3b224 D_3b224 ltac:(rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
  stepat F_3b228 D_3b228 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite andi_7, (u_Z2bv (arrk + 8 * k)%Z) by lia; rewrite (M8 arrk k Hak8); reflexivity).
  stepb_ft F_3b22c D_3b22c ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepLD F_3b230 D_3b230 (Z_to_le_bytes 8 krow) (Z_to_bv 64 krow) ltac:(rewrite zbv_addi, Z.add_0_r; exact Rkrow) ltac:(apply lez8; lia).
  stepat F_3b234 D_3b234 (Z_to_bv 64 (krow + 4 * m)) ltac:(gres; pin; rewrite zbv_add; reflexivity).
  stepb_ft F_3b238 D_3b238 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
  stepat F_3b23c D_3b23c (Z_to_bv 64 1) ltac:(gres; rewrite zbv_snez by lia; reflexivity).
  stepat F_3b240 D_3b240 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
  stepat F_3b244 D_3b244 (Z_to_bv 64 1) ltac:(gres; first [reflexivity | bveq]).
  stepb_ft F_3b248 D_3b248 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepb_ft F_3b24c D_3b24c ltac:(rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
  stepat F_3b250 D_3b250 (Z_to_bv 64 (krow + 4 * m)) ltac:(gres; pin; rewrite zbv_add; f_equal; lia).
  stepat F_3b254 D_3b254 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite andi_3, (u_Z2bv (krow + 4 * m)%Z) by lia; rewrite (M4 krow m Hkr4); reflexivity).
  stepb_ft F_3b258 D_3b258 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepLD F_3b25c D_3b25c (Z_to_le_bytes 8 arrr) (Z_to_bv 64 arrr) ltac:(rewrite zbv_addi; exact Rarrr) ltac:(apply lez8; lia).
  stepb_ft F_3b260 D_3b260 ltac:(rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
  stepat F_3b264 D_3b264 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite andi_7, (u_Z2bv arrr) by lia; rewrite Har8; reflexivity).
  stepb_ft F_3b268 D_3b268 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepat F_3b26c D_3b26c (Z_to_bv 64 (Z.lxor (rb + col + m) 3)) ltac:(gres; imm_norm; rewrite zbv_xori3 by lia; rewrite lxor3_eq by lia; reflexivity).
  stepLBU F_3b270 D_3b270 b ltac:(rewrite zbv_addi, Z.add_0_r; exact Rb).
  stepLD F_3b274 D_3b274 (Z_to_le_bytes 8 rrow) (Z_to_bv 64 rrow) ltac:(rewrite zbv_addi, Z.add_0_r; exact Rrrow) ltac:(apply lez8; lia).
  stepat F_3b278 D_3b278 (Z_to_bv 64 (cval - bv_unsigned b)) ltac:(gres; pin; rewrite zbv_sub; reflexivity).
  stepat F_3b27c D_3b27c (v_srai (Z_to_bv 64 (cval - bv_unsigned b)) 63) ltac:(gres; imm_norm; reflexivity).
  stepat F_3b280 D_3b280 (v_xor (Z_to_bv 64 (cval - bv_unsigned b)) (v_srai (Z_to_bv 64 (cval - bv_unsigned b)) 63)) ltac:(gres; reflexivity).
  stepat F_3b284 D_3b284 (Z_to_bv 64 (Z.abs (cval - bv_unsigned b))) ltac:(gres; rewrite abs_idiom64 by lia; reflexivity).
  stepat F_3b288 D_3b288 (Z_to_bv 64 (4 * Z.abs (cval - bv_unsigned b))) ltac:(gres; imm_norm; rewrite zbv_slli by lia; f_equal; ring).
  stepat F_3b28c D_3b28c (Z_to_bv 64 (rrow + 4 * Z.abs (cval - bv_unsigned b))) ltac:(gres; rewrite zbv_add; reflexivity).
  stepb_ft F_3b290 D_3b290 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia).
  stepat F_3b294 D_3b294 (Z_to_bv 64 1) ltac:(gres; rewrite zbv_snez by lia; reflexivity).
  stepat F_3b298 D_3b298 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
  stepat F_3b29c D_3b29c (Z_to_bv 64 1) ltac:(gres; first [reflexivity | bveq]).
  stepb_ft F_3b2a0 D_3b2a0 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepb_ft F_3b2a4 D_3b2a4 ltac:(rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
  stepat F_3b2a8 D_3b2a8 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite andi_3, (u_Z2bv (rrow + 4 * Z.abs (cval - bv_unsigned b))%Z) by lia; rewrite (M4 rrow (Z.abs (cval - bv_unsigned b)) Hrr4); reflexivity).
  stepb_ft F_3b2ac D_3b2ac ltac:(first [reflexivity | vm_compute; reflexivity]).
  eapply reach_step;
    [ reflexivity
    | eapply fp_step_flw with (a := Z_to_bv 64 (krow + 4 * m)) (bs := Z_to_le_bytes 4 (kf k m));
        [ exact F_3b2b0 | reflexivity | exact D_3b2b0 | gres; imm_norm; rewrite zbv_addi; f_equal; lia | exact Rkf ]
    | ].
  cbn [fp_regs fp_csr]. rewrite (CL (kf k m)) by lia. step_simpl.
  eapply reach_step;
    [ reflexivity
    | eapply fp_step_flw with (a := Z_to_bv 64 (rrow + 4 * Z.abs (cval - bv_unsigned b))) (bs := Z_to_le_bytes 4 (rf (Z.abs (cval - bv_unsigned b))));
        [ exact F_3b2b4 | reflexivity | exact D_3b2b4 | gres; imm_norm; rewrite zbv_addi; f_equal; lia | exact Rrf ]
    | ].
  cbn [fp_regs fp_csr]. rewrite (CL (rf (Z.abs (cval - bv_unsigned b)))) by lia. step_simpl.
  eapply reach_step;
    [ reflexivity
    | eapply fpv_step_fcvt_f_of_x;
        [ exact F_3b2b8 | reflexivity | exact D_3b2b8 | left; split; reflexivity
        | right; left; split; [reflexivity | split; reflexivity] | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | exact fpv_rm_dyn ]
    | ].
  cbn [fp_regs fp_csr fpv_box fp_format]. gres. rewrite (u_Z2bv (bv_unsigned b)) by lia. step_simpl.
  stepat F_3b2bc D_3b2bc (Z_to_bv 64 (4 * (m + 1))) ltac:(gres; pin; imm_norm; rewrite zbv_addi; f_equal; lia).
  eapply reach_step;
    [ reflexivity
    | eapply fpv_step_fari; [ exact F_3b2c0 | reflexivity | exact D_3b2c0 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | exact fpv_rm_dyn ]
    | ].
  cbn [fp_regs fp_csr fpv_box fpv_ari fp_format]. fpn.
  rewrite (fp_u_Z2bv32 (kf k m)), (fp_u_Z2bv32 (rf (Z.abs (cval - bv_unsigned b)))) by lia. step_simpl.
  eapply reach_step;
    [ reflexivity
    | eapply fpv_step_fma; [ exact F_3b2c4 | reflexivity | exact D_3b2c4 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | exact fpv_rm_dyn ]
    | ].
  cbn [fp_regs fp_csr fpv_box fpv_fma fpv_fma_args fp_format]. fpn. rewrite S13.
  rewrite (fp_u_Z2bv32 (fst (fp_of_int fmt_single RNE false 32%Z (bv_unsigned b)))),
    (fp_u_Z2bv32 (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b)))))) by lia.
  step_simpl.
  eapply reach_step;
    [ reflexivity
    | eapply fpv_step_fari; [ exact F_3b2c8 | reflexivity | exact D_3b2c8 | cbn [fp_csr]; repeat apply fpv_frm_acc; exact FZ | exact fpv_rm_dyn ]
    | ].
  cbn [fp_regs fp_csr fpv_box fpv_ari fp_format]. fpn. rewrite S14.
  rewrite (fp_u_Z2bv32 (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b)))))) by lia.
  step_simpl.
  stepat F_3b2cc D_3b2cc (Z_to_bv 64 (m + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
  destruct (Z_lt_ge_dec m 40) as [Hlt|Hge].
  - stepb_tk F_3b2d0 D_3b2d0 ltac:(pin; rewrite c_eq_Zm; apply Z.eqb_neq; rewrite !Z.mod_small by lia; lia).
    lazymatch goal with |- reach _ (@mkst (mkFP ?FR ?CS) ?RL _ _ _) _ =>
      eapply reach_weaken;
      [ | exact (IH fr0 regs0 FR CS RL M Wt krow rrow cval rb col (m + 1)%Z keli arrk rng arrr k (kt + 1)%Z
            (fst (fp_fma fmt_single RNE (fst (fp_of_int fmt_single RNE false 32%Z (bv_unsigned b)))
               (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b))))) s))
            (fst (fp_add fmt_single RNE nv (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b)))))))
            kf rf (cb || (ctr && (m =? 20)%Z))%bool ctr
            ltac:(lia) ltac:(lia) ltac:(repeat apply fpv_frm_acc; exact FZ)
            Hrb4 HWt4 Hrb1 Hrb2 Hcol0 Hcol1 HWt Hkr1 Hkr2 Hkr4 Hrr1 Hrr2 Hrr4 Hcv Hk Hak1 Hak2 Hak8 Har1 Har2 Har8
            Hrow Rarrk Rkrow Rarrr Rrrow Hkf Hrf Hrf0 Hctr Hcb1
            ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
            ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
            ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
            ltac:(unfold ge_acc; split; [rewrite fpv_get_other by reg_neq_tac; rewrite fpv_get_same; reflexivity | rewrite fpv_get_same; reflexivity])
            AVG1 ltac:(lia) ltac:(lia)
            ltac:(eapply regs_agree_trans; [exact AG|]; repeat (apply regs_agree_upd; [cbv beta; unfold GML; in_list|]); apply regs_agree_refl)
            ltac:(unfold ge_fq in FQ |- *; intros r a1 a2 a3 a4 a5; repeat (rewrite fpv_get_other by assumption); apply FQ; assumption)) ]
    end.
    intros fin (fr' & cs' & regs' & s' & nv' & cb' & -> & FZ' & AG' & FQ' & ACC' & AVG' & C1 & C2).
    exists fr', cs', regs', s', nv', cb'. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact AG'|]. split; [exact FQ'|]. split; [exact ACC'|].
    split; [replace (kt + (41 - m))%Z with (kt + 1 + (41 - (m + 1)))%Z by lia; exact AVG'|].
    split; [intro E; apply C1; rewrite E; reflexivity | exact C2].
  - stepb_ft F_3b2d0 D_3b2d0 ltac:(pin; rewrite c_eq_Zm; apply Z.eqb_eq; f_equal; lia).
    apply reach_done.
    do 3 eexists.
    exists (fst (fp_fma fmt_single RNE (fst (fp_of_int fmt_single RNE false 32%Z (bv_unsigned b)))
               (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b))))) s)),
      (fst (fp_add fmt_single RNE nv (fst (fp_mul fmt_single RNE (kf k m) (rf (Z.abs (cval - bv_unsigned b))))))),
      (cb || (ctr && (m =? 20)%Z))%bool.
    split; [reflexivity|].
    split; [repeat apply fpv_frm_acc; exact FZ|].
    split; [eapply regs_agree_trans; [exact AG|]; repeat (apply regs_agree_upd; [cbv beta; unfold GML; in_list|]); apply regs_agree_refl|].
    split; [unfold ge_fq in FQ |- *; intros r a1 a2 a3 a4 a5; repeat (rewrite fpv_get_other by assumption); apply FQ; assumption|].
    split; [unfold ge_acc; split; [rewrite fpv_get_other by reg_neq_tac; rewrite fpv_get_same; reflexivity | rewrite fpv_get_same; reflexivity]|].
    split; [replace (kt + (41 - m))%Z with (kt + 1)%Z by lia; exact AVG1|].
    split; [intro E; rewrite E; reflexivity | intro Hc; destruct (Hcb1 Hc) as [E|E]; [exact E | lia]].
Qed.

(* [comment removed for export] *)
Lemma gk_loop : forall (n : nat) fr0 regs0 fr cs regs (M : word -> option byte) (Wt hs datat keli arrk rng arrr rrow cval i col k : Z) (rowk : Z -> Z)
    (wplt s nv : Z) (kf : Z -> Z -> Z) (rf : Z -> Z),
  Z.of_nat n = (41 - k)%Z -> (0 <= k <= 40)%Z -> frm_zero cs ->
  (datat mod 4 = 0)%Z -> (Wt mod 4 = 0)%Z -> (0 <= Wt)%Z -> (4096 <= datat)%Z -> (datat + Wt * hs <= 2 ^ 47)%Z -> (0 <= i)%Z -> (i + 40 < hs)%Z ->
  (Wt = 4 * wplt)%Z -> (Wt * hs <= 2 ^ 26)%Z ->
  (0 <= col)%Z -> (col + 40 < Wt)%Z -> (0 <= cval <= 255)%Z ->
  (4096 <= keli)%Z -> (keli + 24 <= 2 ^ 47)%Z -> (4096 <= arrk)%Z -> (arrk + 328 <= 2 ^ 47)%Z -> (arrk mod 8 = 0)%Z ->
  (4096 <= rng)%Z -> (rng + 24 <= 2 ^ 47)%Z -> (4096 <= arrr)%Z -> (arrr + 8 <= 2 ^ 47)%Z -> (arrr mod 8 = 0)%Z ->
  (4096 <= rrow)%Z -> (rrow + 1024 <= 2 ^ 47)%Z -> (rrow mod 4 = 0)%Z ->
  (forall p, (datat <= p < datat + Wt * hs)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) ->
  rdn SEGS M (Z_to_bv 64 (keli + 16)) 8 = Some (Z_to_le_bytes 8 arrk) ->
  (forall q, (0 <= q < 41)%Z -> rdn SEGS M (Z_to_bv 64 (arrk + 8 * q)) 8 = Some (Z_to_le_bytes 8 (rowk q)) /\ (4096 <= rowk q)%Z /\ (rowk q + 164 <= 2 ^ 47)%Z /\ (rowk q mod 4 = 0)%Z) ->
  (forall q t, (0 <= q < 41)%Z -> (0 <= t <= 40)%Z -> rdn SEGS M (Z_to_bv 64 (rowk q + 4 * t)) 4 = Some (Z_to_le_bytes 4 (kf q t)) /\ FB fmt_single 1 (kf q t)) ->
  rdn SEGS M (Z_to_bv 64 (rng + 16)) 8 = Some (Z_to_le_bytes 8 arrr) -> rdn SEGS M (Z_to_bv 64 arrr) 8 = Some (Z_to_le_bytes 8 rrow) ->
  (forall d, (0 <= d <= 255)%Z -> rdn SEGS M (Z_to_bv 64 (rrow + 4 * d)) 4 = Some (Z_to_le_bytes 4 (rf d)) /\ FB fmt_single 1 (rf d)) ->
  (kf 20 20 = p_one_s)%Z -> (rf 0 = p_one_s)%Z ->
  (exists b, rdn SEGS M (Z_to_bv 64 (Z.lxor (datat + Wt * (i + 20) + col + 20) 3)) 1 = Some [b] /\ cval = u b) ->
  getr regs 6 = Z_to_bv 64 k -> getr regs 5 = Z_to_bv 64 41 -> getr regs 7 = Z_to_bv 64 keli -> getr regs 8 = Z_to_bv 64 rng ->
  getr regs 9 = Z_to_bv 64 datat -> getr regs 19 = Z_to_bv 64 wplt -> getr regs 11 = Z_to_bv 64 i -> getr regs 17 = Z_to_bv 64 col ->
  getr regs 28 = Z_to_bv 64 cval -> getr regs 29 = Z_to_bv 64 0 -> getr regs 30 = Z_to_bv 64 41 -> getr regs 31 = Z_to_bv 64 164 ->
  getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 3 ->
  ge_acc fr s nv -> ge_avg (41 * k) (20 <? k)%Z s nv ->
  regs_agree (fun r => In r GKL) regs0 regs -> ge_fq fr0 fr ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3b17c : word) M rom)
    (fun fin => exists fr' cs' regs' s' nv', fin = @mkst (mkFP fr' cs') regs' (0x3b2d8 : word) M rom /\ frm_zero cs' /\
                regs_agree (fun r => In r GKL) regs0 regs' /\ ge_fq fr0 fr' /\ ge_acc fr' s' nv' /\ ge_avg 1681 true s' nv').
Proof.
  induction n as [|n IH]; intros fr0 regs0 fr cs regs M Wt hs datat keli arrk rng arrr rrow cval i col k rowk wplt s nv kf rf
    Hn Hk FZ Hdm HWm HW0 Hd0 Hd1 Hi0 Hi1 HWt HWh Hc0 Hc1 Hcv Hke0 Hke1 Ha0 Ha1 Ha2 Hr0 Hr1 Hb0 Hb1 Hb2 Hw0 Hw1 Hw2
    Hdat Rka Hrowk Hkf Rra Rrr Hrf Hk20 Hrf0 Hcen E6 E5 E7 E8 E9 E19 E11 E17 E28 E29 E30 E31 E13 E14 ACC AVG AG FQ; [lia|].
  assert (Hhs : (hs <= 2 ^ 26)%Z) by (assert (hs * 1 <= hs * Wt)%Z by (apply Z.mul_le_mono_nonneg_l; lia); lia).
  assert (HWt26 : (Wt <= 2 ^ 26)%Z) by (assert (Wt * 1 <= Wt * hs)%Z by (apply Z.mul_le_mono_nonneg_l; lia); lia).
  assert (HP0 : (0 <= (i + k) * wplt)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  assert (HP1 : ((i + k) * wplt <= hs * wplt)%Z) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (HP2 : (4 * (hs * wplt) <= 2 ^ 26)%Z) by (rewrite HWt in HWh; lia).
  pose proof (Hrowk k ltac:(lia)) as (Rk & Rk1 & Rk2 & Rk3).
  pose proof (row_geo datat Wt hs (i + k) Hdm HWm HW0 ltac:(lia)) as (RG1 & RG2 & RG3).
  eapply reach_msteps.
  { zvw F_3b17c D_3b17c (Z_to_bv 64 k).
    zv F_3b180 D_3b180 (Z_to_bv 64 (i + k)).
    sn F_3b184 D_3b184. fixv (Z_to_bv 64 (i + k)) ltac:(rewrite zbv_addw_small by lia; reflexivity).
    stepb_ft F_3b188 D_3b188 ltac:(condZ).
    zvw F_3b18c D_3b18c (Z_to_bv 64 (i + k)).
    zv F_3b190 D_3b190 (Z_to_bv 64 ((i + k) * wplt)).
    zvw F_3b194 D_3b194 (Z_to_bv 64 ((i + k) * wplt)).
    stepb_ft F_3b198 D_3b198 ltac:(condZ).
    zvw F_3b19c D_3b19c (Z_to_bv 64 ((i + k) * wplt)).
    stepiv F_3b1a0 D_3b1a0 (Z_to_bv 64 (Wt * (i + k))) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; rewrite HWt; ring).
    zv F_3b1a4 D_3b1a4 (Z_to_bv 64 (datat + Wt * (i + k))).
    stepiv F_3b1a8 D_3b1a8 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
    stepb_ft F_3b1ac D_3b1ac ltac:(condZ).
    stepat F_3b1b0 D_3b1b0 (Z_to_bv 64 0) ltac:(gres; pin; rewrite zbv_sltu_ge by lia; reflexivity).
    stepat F_3b1b4 D_3b1b4 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite zbv_slti0 by lia; reflexivity).
    stepat F_3b1b8 D_3b1b8 (Z_to_bv 64 0) ltac:(gres; apply bv_eq; vm_compute; reflexivity).
    stepiv F_3b1bc D_3b1bc (Z_to_bv 64 1) ltac:(gres; imm_norm; apply bv_eq; vm_compute; reflexivity).
    stepb_ft F_3b1c0 D_3b1c0 ltac:(condZ).
    stepb_ft F_3b1c4 D_3b1c4 ltac:(condZ).
    zv F_3b1c8 D_3b1c8 (Z_to_bv 64 0).
    zv F_3b1cc D_3b1cc (Z_to_bv 64 0).
    stepiv F_3b1d0 D_3b1d0 (Z_to_bv 64 (8 * k)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 3)%Z with 8%Z; lia).
    apply mst_refl. }
  match goal with |- reach _ (@mkst _ ?R _ _ _) _ => set (R1 := R) end.
  eapply reach_bind.
  { apply (gm_loop 41%nat fr R1 fr cs R1 M Wt (rowk k) rrow cval (datat + Wt * (i + k))%Z col 0%Z keli arrk rng arrr k (41 * k)%Z s nv kf rf
             (20 <? k)%Z (k =? 20)%Z).
    all: first [ exact FZ | assumption | apply regs_agree_refl | (unfold ge_fq; intros; reflexivity)
               | (intros p Hp; apply Hdat; lia)
               | (intros q Hq; exact (Hkf k q ltac:(lia) Hq))
               | (intros _; right; lia)
               | (intros Hc; apply Z.eqb_eq in Hc; subst k; split; [exact Hk20 | exact Hcen])
               | (subst R1; gres; pin; first [reflexivity | f_equal; lia])
               | reflexivity | lia ]. }
  intros fin (fr2 & cs2 & regs2 & s2 & nv2 & cb2 & -> & FZ2 & AG2 & FQ2 & ACC2 & AVG2 & CB1 & CB2).
  assert (G6 : getr regs2 6 = Z_to_bv 64 k) by (rewrite (AG2 6) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G5 : getr regs2 5 = Z_to_bv 64 41) by (rewrite (AG2 5) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G7 : getr regs2 7 = Z_to_bv 64 keli) by (rewrite (AG2 7) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G8 : getr regs2 8 = Z_to_bv 64 rng) by (rewrite (AG2 8) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G9 : getr regs2 9 = Z_to_bv 64 datat) by (rewrite (AG2 9) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G19 : getr regs2 19 = Z_to_bv 64 wplt) by (rewrite (AG2 19) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G11 : getr regs2 11 = Z_to_bv 64 i) by (rewrite (AG2 11) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G17 : getr regs2 17 = Z_to_bv 64 col) by (rewrite (AG2 17) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G28 : getr regs2 28 = Z_to_bv 64 cval) by (rewrite (AG2 28) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G29 : getr regs2 29 = Z_to_bv 64 0) by (rewrite (AG2 29) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G30 : getr regs2 30 = Z_to_bv 64 41) by (rewrite (AG2 30) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G31 : getr regs2 31 = Z_to_bv 64 164) by (rewrite (AG2 31) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G13 : getr regs2 13 = Z_to_bv 64 1) by (rewrite (AG2 13) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (G14 : getr regs2 14 = Z_to_bv 64 3) by (rewrite (AG2 14) by (unfold GML; notin_list); subst R1; gres; pin; reflexivity).
  assert (FQr : ge_fq fr0 fr2).
  { unfold ge_fq in FQ, FQ2 |- *. intros r R10 R11 R12 R13 R14. rewrite (FQ2 r R10 R11 R12 R13 R14). exact (FQ r R10 R11 R12 R13 R14). }
  assert (AGr : regs_agree (fun r => In r GKL) regs0 regs2).
  { eapply regs_agree_trans; [exact AG|]. apply (regs_agree_trans _ _ R1).
    - subst R1. unfold GKL. solve_regs_agree.
    - eapply regs_agree_mono; [|exact AG2]. intros r Hr. unfold GML in Hr. unfold GKL. cbn [In] in Hr |- *. tauto. }
  assert (AVGn : ge_avg (41 * (k + 1)) (20 <? k + 1)%Z s2 nv2).
  { apply (ge_avg_flag_mono _ cb2 _ s2 nv2).
    - replace (41 * (k + 1))%Z with (41 * k + (41 - 0))%Z by lia. exact AVG2.
    - intros Hc. apply Z.ltb_lt in Hc. destruct (Z.eq_dec k 20) as [Ek|Ek].
      + apply CB2. apply Z.eqb_eq. exact Ek.
      + apply CB1. apply Z.ltb_lt. lia. }
  destruct n as [|n].
  - eapply reach_msteps.
    { stepj F_3b2d4 D_3b2d4.
      zv F_3b174 D_3b174 (Z_to_bv 64 (k + 1)).
      stepb_tk F_3b178 D_3b178 ltac:(condZ).
      apply mst_refl. }
    apply reach_done. do 5 eexists. split; [reflexivity|].
    split; [exact FZ2|]. split; [apply regs_agree_upd; [unfold GKL; in_list | exact AGr]|].
    split; [exact FQr|]. split; [exact ACC2|].
    replace 1681%Z with (41 * (k + 1))%Z by lia.
    apply (ge_avg_flag_mono _ _ true s2 nv2 AVGn). intros _. apply Z.ltb_lt. lia.
  - eapply reach_msteps.
    { stepj F_3b2d4 D_3b2d4.
      zv F_3b174 D_3b174 (Z_to_bv 64 (k + 1)).
      stepb_ft F_3b178 D_3b178 ltac:(condZ).
      apply mst_refl. }
    apply (IH fr0 regs0 fr2 cs2 _ M Wt hs datat keli arrk rng arrr rrow cval i col (k + 1)%Z rowk wplt s2 nv2 kf rf).
    all: first [ exact FZ2 | assumption | (apply regs_agree_upd; [unfold GKL; in_list | exact AGr])
               | (gres; pin; first [reflexivity | f_equal; lia]) | lia ].
Qed.

(* [comment removed for export] *)
Definition ge_rd (M : word -> option byte) (sf w h Wt hs datat datad keli arrk rng arrr rrow : Z) (rowk : Z -> Z) (kf : Z -> Z -> Z) (rf : Z -> Z) : Prop :=
  rdn SEGS M (Z_to_bv 64 (sf + 32)) 8 = Some (Z_to_le_bytes 8 keli) /\ rdn SEGS M (Z_to_bv 64 (sf + 16)) 8 = Some (Z_to_le_bytes 8 datad) /\
  rdn SEGS M (Z_to_bv 64 (sf + 44)) 4 = Some (Z_to_le_bytes 4 20) /\ rdn SEGS M (Z_to_bv 64 (sf + 48)) 4 = Some (Z_to_le_bytes 4 20) /\
  rdn SEGS M (Z_to_bv 64 (sf + 52)) 4 = Some (Z_to_le_bytes 4 41) /\ rdn SEGS M (Z_to_bv 64 (sf + 56)) 4 = Some (Z_to_le_bytes 4 41) /\
  rdn SEGS M (Z_to_bv 64 (sf + 64)) 4 = Some (Z_to_le_bytes 4 h) /\ rdn SEGS M (Z_to_bv 64 (sf + 68)) 4 = Some (Z_to_le_bytes 4 w) /\
  (forall p, (datat <= p < datat + Wt * hs)%Z -> exists b, rdn SEGS M (Z_to_bv 64 p) 1 = Some [b]) /\
  rdn SEGS M (Z_to_bv 64 (keli + 16)) 8 = Some (Z_to_le_bytes 8 arrk) /\
  (forall q, (0 <= q < 41)%Z -> rdn SEGS M (Z_to_bv 64 (arrk + 8 * q)) 8 = Some (Z_to_le_bytes 8 (rowk q)) /\ (4096 <= rowk q)%Z /\ (rowk q + 164 <= 2 ^ 47)%Z /\ (rowk q mod 4 = 0)%Z) /\
  (forall q t, (0 <= q < 41)%Z -> (0 <= t <= 40)%Z -> rdn SEGS M (Z_to_bv 64 (rowk q + 4 * t)) 4 = Some (Z_to_le_bytes 4 (kf q t)) /\ FB fmt_single 1 (kf q t)) /\
  rdn SEGS M (Z_to_bv 64 (rng + 16)) 8 = Some (Z_to_le_bytes 8 arrr) /\ rdn SEGS M (Z_to_bv 64 arrr) 8 = Some (Z_to_le_bytes 8 rrow) /\
  (forall d, (0 <= d <= 255)%Z -> rdn SEGS M (Z_to_bv 64 (rrow + 4 * d)) 4 = Some (Z_to_le_bytes 4 (rf d)) /\ FB fmt_single 1 (rf d)) /\
  (forall q, (0x12588 <= q < 0x125d8)%Z -> M (Z_to_bv 64 q) = None) /\
  (kf 20 20 = p_one_s)%Z /\ (rf 0 = p_one_s)%Z.

(* [comment removed for export] *)
Definition ge_geo (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow : Z) : Prop :=
  (4096 <= sf)%Z /\ (sf + 176 <= 2 ^ 47)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (hs = h + 41)%Z /\
  (0 <= wplt)%Z /\ (Wt = 4 * wplt)%Z /\ (w + 41 <= Wt)%Z /\ (Wt * hs <= 2 ^ 26)%Z /\
  (0 <= wpld)%Z /\ (Wd = 4 * wpld)%Z /\ (w <= Wd)%Z /\ (Wd * h <= 2 ^ 26)%Z /\
  (datat mod 4 = 0)%Z /\ (4096 <= datat)%Z /\ (datat + Wt * hs <= 2 ^ 47)%Z /\
  (datad mod 4 = 0)%Z /\ (4096 <= datad)%Z /\ (datad + Wd * h <= 2 ^ 47)%Z /\ (datad + Wd * h <= sf \/ sf + 176 <= datad)%Z /\
  (4096 <= keli)%Z /\ (keli + 24 <= 2 ^ 47)%Z /\ (keli mod 8 = 0)%Z /\ (4096 <= arrk)%Z /\ (arrk + 328 <= 2 ^ 47)%Z /\ (arrk mod 8 = 0)%Z /\
  (4096 <= rng)%Z /\ (rng + 24 <= 2 ^ 47)%Z /\ (4096 <= arrr)%Z /\ (arrr + 8 <= 2 ^ 47)%Z /\ (arrr mod 8 = 0)%Z /\
  (4096 <= rrow)%Z /\ (rrow + 1024 <= 2 ^ 47)%Z /\ (rrow mod 4 = 0)%Z.

Definition GJB : list reg := [1; 5; 6; 7; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section GJ.
Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LeptExec LeptExecW LeptExecFP LeptExecX.
Import SX2. Import SX2S.
#[local] Existing Instance exf_fxd | 100.

Ltac gjb_srv HR' k :=
  rewrite (reg_val _ _ _ k HR');
  match goal with |- context [sr_get ?sr ?kk] => let e := eval vm_compute in (sr_get sr kk) in change (sr_get sr kk) with e end;
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add].
Ltac gjb_val := rewrite ?alu_add, ?zbv_add, ?w_addw, ?w_mulw, ?m_mul;
  rewrite ?zbv_addw_small by lia; rewrite ?zbv_mulw_small by lia; rewrite ?zbv_mul; first [reflexivity | f_equal; lia].

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma gjb_swrap : forall t r k : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> t = (r + k * 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r k Hr ->. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.
Lemma gjb_swrap_mod : forall t r : Z, (- 2 ^ 31 <= r < 2 ^ 31)%Z -> (t mod 2 ^ 32 = r mod 2 ^ 32)%Z -> bv_swrap 32 t = r.
Proof. intros t r Hr Ht. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N]. lia. Qed.
Lemma gjb_addw : forall a b : Z, (- 2 ^ 31 <= a + b < 2 ^ 31)%Z -> v_addw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b H. unfold v_addw. rewrite !u_Z2bv_mod. f_equal.
  apply gjb_swrap with (k := (- 2 ^ 32 * (a / 2 ^ 64) - 2 ^ 32 * (b / 2 ^ 64))%Z); lia.
Qed.
Lemma gjb_mulw : forall a b : Z, (- 2 ^ 31 <= a * b < 2 ^ 31)%Z -> v_mulw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b H. unfold v_mulw. rewrite !u_Z2bv_mod. f_equal. apply gjb_swrap_mod; [exact H |].
  assert (Ea : ((a mod 2 ^ 64) mod 2 ^ 32 = a mod 2 ^ 32)%Z) by lia.
  assert (Eb : ((b mod 2 ^ 64) mod 2 ^ 32 = b mod 2 ^ 32)%Z) by lia.
  rewrite (Z.mul_mod (a mod 2 ^ 64) (b mod 2 ^ 64) (2 ^ 32)) by lia. rewrite Ea, Eb.
  rewrite <- (Z.mul_mod a b (2 ^ 32)) by lia. reflexivity.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma gjb_xor : forall a b : Z, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z ->
  v_xor (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lxor a b).
Proof. intros a b Ha Hb. unfold v_xor. rewrite !u_Z2bv by lia. reflexivity. Qed.

Ltac gjb_lit x := lazymatch x with Z0 => idtac | Zpos _ => idtac end.
Ltac gjb_z1 :=
  first [ rewrite Z.add_0_r | rewrite zbv_add | rewrite zbv_sub | rewrite zbv_mul | rewrite zbv_addi
        | rewrite gjb_mulw by lia | rewrite gjb_addw by lia
        | rewrite v_sltu_Z by lia | rewrite v_slt_Z by lia | rewrite gjb_xor by lia | rewrite zbv_or by lia
        | match goal with |- context [(?a <? ?b)%Z] =>
            first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ] end
        | match goal with |- context [Z.lxor ?x ?y] =>
            gjb_lit x; gjb_lit y; let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v end
        | match goal with |- context [alu64 ALU_ADD ?a ?b] => change (alu64 ALU_ADD a b) with (v_add a b) end
        | match goal with |- context [alu64 ALU_SUB ?a ?b] => change (alu64 ALU_SUB a b) with (v_sub a b) end
        | match goal with |- context [alu64 ALU_SLTU ?a ?b] => change (alu64 ALU_SLTU a b) with (v_sltu a b) end
        | match goal with |- context [alu64 ALU_SLT ?a ?b] => change (alu64 ALU_SLT a b) with (v_slt a b) end
        | match goal with |- context [alu64 ALU_XOR ?a ?b] => change (alu64 ALU_XOR a b) with (v_xor a b) end
        | match goal with |- context [alu64 ALU_OR ?a ?b] => change (alu64 ALU_OR a b) with (v_or a b) end
        | match goal with |- context [mul_div M_MUL ?a ?b] => change (mul_div M_MUL a b) with (v_mul a b) end ].
Ltac gjb_z :=
  rewrite ?alu_add, ?alu_sub, ?alu_slt, ?alu_sltu, ?alu_and, ?alu_or, ?alu_xor, ?w_addw, ?w_subw, ?w_mulw, ?m_mul;
  repeat gjb_z1.
Ltac gjb_sc := gjb_z; first [ ex_br | (rewrite ?u_Z2bv by lia; lia) ].
Lemma gjb_lez1 : forall b : byte, bytes_le_to_Z [b] = bv_unsigned b.
Proof. intros b. cbn. rewrite ?Z.shiftl_0_l, ?Z.lor_0_r, ?Z.mul_0_r, ?Z.add_0_r. first [reflexivity | lia]. Qed.
Ltac gjb_rd b Hb :=
  exists [b]; split;
  [ gjb_z; first [ exact Hb
                 | match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                     match type of Hb with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a with a' by (f_equal; lia); exact Hb end end ]
  | cbn [extz]; f_equal; apply gjb_lez1 ].
Ltac gjb_fsgnj F D := chain_step; [ reflexivity | eapply fpv_step_fsgnj; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac gjb_step F D := first [ gjb_fsgnj F D | sn F D | stepj F D | stepb_ft F D ltac:(condZ) | stepb_tk F D ltac:(condZ) ].
Ltac gjb_fcmp F D := chain_step; [ reflexivity | eapply fpv_step_fcmp; [exact F | reflexivity | exact D] | step_simpl ]; fpn.
Ltac gjb_fari F D Hz := chain_step; [ reflexivity | eapply fpv_step_fari; [exact F | reflexivity | exact D | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac gjb_fcvt_ds F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_f_of_f;
  [exact F | reflexivity | exact D | right; split; reflexivity | left; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac gjb_fcvt_wd F D Hz := chain_step; [ reflexivity | eapply fpv_step_fcvt_x_of_f;
  [exact F | reflexivity | exact D | left; repeat split; reflexivity | right; split; reflexivity | fz Hz | reflexivity] | step_simpl ]; fpn.
Ltac gjb_try F D Hz := first [ gjb_fari F D Hz | gjb_fcvt_ds F D Hz | gjb_fcvt_wd F D Hz | gjb_fcmp F D | gjb_fsgnj F D | sn F D | stepj F D ].

Ltac gjp_fld F D A K R := chain_step;
  [ reflexivity
  | eapply fp_step_fld with (a := Z_to_bv 64 A) (bs := Z_to_le_bytes 8 K);
    [exact F | reflexivity | exact D | gres; imm_norm; apply bv_eq; vm_compute; reflexivity | exact R]
  | step_simpl ]; fpn.
Ltac gjp_n := repeat first
  [ match goal with H : fpv_read _ _ _ = _ |- _ => rewrite H end
  | match goal with H : bv_extract 0 64 _ = _ |- _ => rewrite H end
  | match goal with H : fst _ = _ |- _ => rewrite H end
  | match goal with |- context [bv_unsigned (Z_to_bv 32 ?z)] => rewrite (fp_u_Z2bv32 z) by lia end
  | match goal with |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u_Z2bv z) by lia end ].
Ltac gjp_c := first [ cond_compute | condZ ].

Lemma gjb_post : forall fr cs regs (M0 M : word -> option byte) (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j s nv : Z)
    (rowk : Z -> Z) (kf : Z -> Z -> Z) (rf : Z -> Z),
  frm_zero cs -> ge_geo sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow ->
  ge_rd M sf w h Wt hs datat datad keli arrk rng arrr rrow rowk kf rf ->
  store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat (Wd * h)) = true -> rinv [(datad, (Wd * h)%Z)] M0 M ->
  (0 <= i < h)%Z -> (0 <= j < w)%Z ->
  getr regs 2 = Z_to_bv 64 sf -> getr regs 16 = Z_to_bv 64 j -> getr regs 17 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 (datad + Wd * i) ->
  getr regs 11 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 wplt -> getr regs 8 = Z_to_bv 64 rng -> getr regs 9 = Z_to_bv 64 datat ->
  getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 3 ->
  ge_acc fr s nv -> ge_avg 1681 true s nv ->
  reach SEGS (@mkst (mkFP fr cs) regs (Z_to_bv 64 0x3b2d8) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b330 : word) M' rom /\ frm_zero cs' /\
       (exists p bs, (datad <= p < datad + Wd * h)%Z /\ length bs = 1%nat /\ M' = wbytes M (Z_to_bv 64 p) bs) /\
       getr regs' 5 = Z_to_bv 64 w /\ regs_agree (fun r => In r GJB) regs regs' /\ ge_fq fr fr').
Proof.
  intros fr cs regs M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j s nv rowk kf rf
    FZ GEO RD SOKd RI Hi Hj H2 H16 H17 H15 H11 H19 H8 H9 H12 H13 H14 ACC AVG.
  destruct RD as (Rkeli & Rdatad & Rcy & Rcx & Rsy & Rsx & Rh & Rw & Rdt & Rarrk & Rrowk & Rkf & Rarrr & Rrrow & Rrf
                  & Rimg & Hk20 & Hr0).
  unfold ge_geo in GEO. decompose [and] GEO. clear GEO.
  assert (HWd0 : (0 <= Wd)%Z) by lia.
  assert (HWi0 : (0 <= Wd * i)%Z) by nia.
  assert (HWi1 : (Wd * i + Wd <= Wd * h)%Z) by nia.
  pose proof (xo_bound j wpld ltac:(lia)) as HX.
  assert (HA : ((datad + Wd * i) mod 4 = 0)%Z).
  { replace (datad + Wd * i)%Z with (datad + wpld * i * 4)%Z by (subst Wd; ring). rewrite Z_mod_plus_full. assumption. }
  pose proof (ge_avg_range _ _ _ _ AVG) as (Hsr & Hnr).
  pose proof p_consts_range as (PC0 & PC1 & PC2 & PC3 & PC4).
  assert (Hs : fpv_read fr FMT_S 13 = s) by (unfold fpv_read; rewrite (proj1 ACC), fpv_unbox_box; apply fp_u_Z2bv32; lia).
  assert (Hn : fpv_read fr FMT_S 14 = nv) by (unfold fpv_read; rewrite (proj2 ACC), fpv_unbox_box; apply fp_u_Z2bv32; lia).
  pose proof (ge_site_full 1681 s nv RNE RNE AVG ltac:(lia)) as GS. cbv zeta in GS.
  set (gq := fst (fp_div fmt_single RNE s nv)) in GS.
  set (gqd := fst (fp_convert fmt_single fmt_double RNE gq)) in GS.
  set (gv := fst (fp_add fmt_double RNE gqd p_half_d)) in GS.
  assert (Eq1 : fst (fpv_ari F_DIV FMT_S RNE s nv) = gq) by reflexivity.
  assert (Eq2 : fst (fp_convert (fp_format FMT_S) (fp_format FMT_D) RNE gq) = gqd) by reflexivity.
  assert (Eq3 : fst (fpv_ari F_ADD FMT_D RNE gqd p_half_d) = gv) by reflexivity.
  destruct GS as (Q1 & Q2 & Q3 & LT1 & LT2 & _).
  assert (Eq4 : fst (fpv_cmp F_LT FMT_D p_lo_d gv) = true) by exact LT1.
  assert (Eq5 : fst (fpv_cmp F_LT FMT_D gv p_hi_d) = true) by exact LT2.
  clearbody gv gqd gq.
  assert (RH : rdn SEGS M (Z_to_bv 64 0x125b8) 8 = Some (Z_to_le_bytes 8 p_half_d)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ _ _ Rimg) by lia. apply (bool_decide_eq_true_1 _); vm_compute; reflexivity. }
  assert (RL : rdn SEGS M (Z_to_bv 64 0x125d0) 8 = Some (Z_to_le_bytes 8 p_lo_d)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ _ _ Rimg) by lia. apply (bool_decide_eq_true_1 _); vm_compute; reflexivity. }
  assert (RU : rdn SEGS M (Z_to_bv 64 0x12588) 8 = Some (Z_to_le_bytes 8 p_hi_d)).
  { rewrite (SumWalkTac.rdn_img _ _ _ _ _ _ Rimg) by lia. apply (bool_decide_eq_true_1 _); vm_compute; reflexivity. }
  assert (KH : bv_extract 0 64 (le_bytes_to_word (Z_to_le_bytes 8 p_half_d)) = Z_to_bv 64 p_half_d) by (apply bv_eq; vm_compute; reflexivity).
  assert (KL : bv_extract 0 64 (le_bytes_to_word (Z_to_le_bytes 8 p_lo_d)) = Z_to_bv 64 p_lo_d) by (apply bv_eq; vm_compute; reflexivity).
  assert (KU : bv_extract 0 64 (le_bytes_to_word (Z_to_le_bytes 8 p_hi_d)) = Z_to_bv 64 p_hi_d) by (apply bv_eq; vm_compute; reflexivity).
  assert (SOKp : store_ok SEGS M (Z_to_bv 64 (datad + Wd * i + xo j)) 1%nat = true).
  { eapply store_ok_sub with (lo := Z_to_bv 64 datad) (N := Z.to_nat (Wd * h)).
    - rewrite u_Z2bv by lia. rewrite Z2Nat.id by lia. lia.
    - eapply store_ok_mono; [exact (proj1 RI) | exact SOKd].
    - rewrite !u_Z2bv by lia. lia.
    - rewrite !u_Z2bv by lia. rewrite Z2Nat.id by lia. lia. }
  replace (Z_to_bv 64 0x3b2d8) with (0x3b2d8 : word) by (apply bv_eq; reflexivity).
  eapply reach_msteps.
  { sn F_3b2d8 D_3b2d8.
    gjp_fld F_3b2dc D_3b2dc (0x125b8)%Z p_half_d RH. gjp_n.
    sn F_3b2e0 D_3b2e0.
    gjp_fld F_3b2e4 D_3b2e4 (0x125d0)%Z p_lo_d RL. gjp_n.
    gjb_fari F_3b2e8 D_3b2e8 FZ. gjp_n.
    gjb_fcvt_ds F_3b2ec D_3b2ec FZ. gjp_n.
    gjb_fari F_3b2f0 D_3b2f0 FZ. gjp_n.
    gjb_fcmp F_3b2f4 D_3b2f4. gjp_n.
    stepb_ft F_3b2f8 D_3b2f8 ltac:(gjp_c).
    sn F_3b2fc D_3b2fc.
    gjp_fld F_3b300 D_3b300 (0x12588)%Z p_hi_d RU. gjp_n.
    gjb_fcmp F_3b304 D_3b304. gjp_n.
    stepb_ft F_3b308 D_3b308 ltac:(gjp_c).
    zv F_3b30c D_3b30c (Z_to_bv 64 (datad + Wd * i + j)).
    stepat F_3b310 D_3b310 (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).
    stepb_ft F_3b314 D_3b314 ltac:(gjp_c).
    stepb_ft F_3b318 D_3b318 ltac:(gjp_c).
    stepb_ft F_3b31c D_3b31c ltac:(gjp_c).
    gjb_fcvt_wd F_3b320 D_3b320 FZ.
    stepat F_3b324 D_3b324 (Z_to_bv 64 (datad + Wd * i + xo j)) ltac:(gres; pin; imm_norm; apply xor3_xo; first [exact HA | lia]).
    chain_step;
      [ reflexivity
      | eapply MmapSim.step_sb_at with (a := Z_to_bv 64 (datad + Wd * i + xo j));
        [ exact F_3b328 | reflexivity | exact D_3b328
        | gres; imm_norm; rewrite ?v_addi_0, ?zbv_addi; first [reflexivity | f_equal; lia]
        | reflexivity | reflexivity | exact SOKp ]
      | step_simpl ].
    chain_step;
      [ reflexivity
      | eapply PropExec.step_lw with (bs := Z_to_le_bytes 4 w) (v := Z_to_bv 64 w);
        [ exact F_3b32c | reflexivity | exact D_3b32c
        | gres; pin; imm_norm; rewrite zbv_addi; (rewrite CatExec.rdn_wbytes_out; [exact Rw | | | ]);
          rewrite ?u_Z2bv by lia; cbn [length]; lia
        | apply W2Lib.lez4; lia ]
      | step_simpl ].
    apply mst_refl. }
  apply reach_done.
  do 4 eexists. split; [reflexivity |].
  split; [fz FZ |].
  split.
  { exists (datad + Wd * i + xo j)%Z. eexists. split; [lia |]. split; [| reflexivity]. reflexivity. }
  split.
  { gres. rewrite SumWalkTac.v_lw_small by lia. reflexivity. }
  split.
  { unfold GJB. solve_regs_agree. }
  { intros r N10 N11 N12 N13 N14. rewrite ?fpv_get_other by assumption. reflexivity. }
Qed.

(* [comment removed for export] *)
Lemma gj_body : forall fr0 regs0 fr cs regs (M0 M : word -> option byte) (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j : Z) (rowk : Z -> Z)
    (kf : Z -> Z -> Z) (rf : Z -> Z),
  frm_zero cs -> ge_geo sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow ->
  (forall M', rinv [(datad, (Wd * h)%Z)] M0 M' -> ge_rd M' sf w h Wt hs datat datad keli arrk rng arrr rrow rowk kf rf) ->
  store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat (Wd * h)) = true -> rinv [(datad, (Wd * h)%Z)] M0 M ->
  (0 <= i < h)%Z -> (0 <= j < w)%Z ->
  getr regs 2 = Z_to_bv 64 sf -> getr regs 16 = Z_to_bv 64 j -> getr regs 17 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 (datad + Wd * i) ->
  getr regs 11 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 wplt -> getr regs 8 = Z_to_bv 64 rng -> getr regs 9 = Z_to_bv 64 datat ->
  getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 3 -> reg_get fr 15%bv = nan_box (Z_to_bv 32 0) ->
  regs_agree (fun r => In r GJB) regs0 regs -> ge_fq fr0 fr ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3b0b4 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b330 : word) M' rom /\ frm_zero cs' /\
                (exists p bs, (datad <= p < datad + Wd * h)%Z /\ length bs = 1%nat /\ M' = wbytes M (Z_to_bv 64 p) bs) /\
                getr regs' 5 = Z_to_bv 64 w /\ regs_agree (fun r => In r GJB) regs0 regs' /\ ge_fq fr0 fr').
Proof.
  intros fr0 regs0 fr cs regs M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j rowk kf rf
    FZ GEO RD SOKd RI Hi Hj H2 H16 H17 H15 H11 H19 H8 H9 H12 H13 H14 F15 AG FQ.
  destruct (RD M RI) as (Rkeli & Rdatad & Rcy & Rcx & Rsy & Rsx & Rh & Rw & Rdt & Rarrk & Rrowk & Rkf & Rarrr & Rrrow & Rrf
                         & Rimg & Hk20 & Hr0).
  pose proof GEO as GEO0. unfold ge_geo in GEO. decompose [and] GEO. clear GEO.
  assert (Hwp : (0 <= wplt <= 2 ^ 24)%Z) by nia.
  assert (HWd : (0 <= Wd * h)%Z) by nia. assert (HWt : (0 <= Wt * hs)%Z) by nia.
  replace (0x3b0b4 : word) with (Z_to_bv 64 0x3b0b4) by (apply bv_eq; reflexivity).
  ex_entry regs [sf; keli; datad; h; w; bv_unsigned (reg_get fr 15%bv)] HR.
  assert (HK : know_ok SEGS (ex_env regs [sf; keli; datad; h; w; bv_unsigned (reg_get fr 15%bv)]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 9) 4096 (2 ^ 47); KAlign (EVar 9) 4;
      KRange (EVar 11) 0 20000; KRange (EVar 16) 0 20000; KRange (EVar 17) 0 20000; KRange (EVar 19) 0 (2 ^ 24);
      KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8; KRange (EVar 8) 4096 (2 ^ 47);
      KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000;
      KWord (SA (EVar 32) 32) 8 (EVar 33); KWord (SA (EVar 32) 16) 8 (EVar 34);
      KWord (SA (EVar 32) 44) 4 (ELit 20); KWord (SA (EVar 32) 48) 4 (ELit 20);
      KWord (SA (EVar 32) 52) 4 (ELit 41); KWord (SA (EVar 32) 56) 4 (ELit 41);
      KWord (SA (EVar 32) 64) 4 (EVar 35); KWord (SA (EVar 32) 68) 4 (EVar 36)]).
  { ex_know regs. }
  exb_open HR HK ST.
  exb_adriveS 8%nat 400%nat [0x3b0d0%Z] (SCR [false] [] []) [(15%nat, 37%nat)] HK ST FZ.
  assert (Hpr : (0 <= (i + 20) * wplt <= 2 ^ 24)%Z) by nia.
  exb_exit ST R HR' Hlf Hms.
  assert (AGp1 : regs_agree (fun r => In r GJB) regs R) by (ex_agree HR HR').
  assert (E5 : getr R 5%bv = Z_to_bv 64 ((i + 20) * wplt)) by (gjb_srv HR' (5%bv : bv 5); rewrite ?H11, ?H19; gjb_val).
  assert (E6 : getr R 6%bv = Z_to_bv 64 ((i + 20) * wplt)) by (gjb_srv HR' (6%bv : bv 5); rewrite ?H11, ?H19; gjb_val).
  assert (R2 : getr R 2%bv = Z_to_bv 64 sf) by (ex_reg regs HR').
  assert (R8 : getr R 8%bv = Z_to_bv 64 rng) by (ex_reg regs HR').
  assert (R9 : getr R 9%bv = Z_to_bv 64 datat) by (ex_reg regs HR').
  assert (R11 : getr R 11%bv = Z_to_bv 64 i) by (ex_reg regs HR').
  assert (R12 : getr R 12%bv = Z_to_bv 64 1) by (ex_reg regs HR').
  assert (R13 : getr R 13%bv = Z_to_bv 64 1) by (ex_reg regs HR').
  assert (R14 : getr R 14%bv = Z_to_bv 64 3) by (ex_reg regs HR').
  assert (R15 : getr R 15%bv = Z_to_bv 64 (datad + Wd * i)) by (ex_reg regs HR').
  assert (R16 : getr R 16%bv = Z_to_bv 64 j) by (ex_reg regs HR').
  assert (R17 : getr R 17%bv = Z_to_bv 64 j) by (ex_reg regs HR').
  assert (R19 : getr R 19%bv = Z_to_bv 64 wplt) by (ex_reg regs HR').
  apply (reach_msteps _ _ _ _ Hms). clear Hms.
  lazymatch goal with |- context [fr_denot ?E [] fr] => change (fr_denot E [] fr) with fr end.
  lazymatch goal with |- context [mem_denot ?E M []] => change (mem_denot E M []) with M end.
  clear HR HK HR' Hlf.
  assert (Hpc : (datat <= Z.lxor (datat + (4 * ((i + 20) * wplt) + (j + 20))) 3 < datat + Wt * hs)%Z).
  { rewrite lxor3_eq by nia. pose proof (Z.mod_pos_bound (datat + (4 * ((i + 20) * wplt) + (j + 20))) 4 ltac:(lia)).
    assert (wplt * (i + 21) <= wplt * hs)%Z by (apply Z.mul_le_mono_nonneg_l; lia). nia. }
  destruct (Rdt _ Hpc) as (bc & Hbc).
  ex_entry R [sf; keli; datad; h; w; bv_unsigned (reg_get fr 15%bv); bv_unsigned bc] HR.
  assert (HK : know_ok SEGS (ex_env R [sf; keli; datad; h; w; bv_unsigned (reg_get fr 15%bv); bv_unsigned bc]) M
     [KRange (EVar 32) 4096 (2 ^ 47); KRange (EVar 9) 4096 (2 ^ 47); KAlign (EVar 9) 4;
      KRange (EVar 11) 0 20000; KRange (EVar 16) 0 20000; KRange (EVar 17) 0 20000; KRange (EVar 19) 0 (2 ^ 24);
      KRange (EVar 5) 0 (2 ^ 24); KRange (EVar 6) 0 (2 ^ 24);
      KRange (EVar 33) 4096 (2 ^ 47); KAlign (EVar 33) 8; KRange (EVar 8) 4096 (2 ^ 47);
      KRange (EVar 35) 1 20000; KRange (EVar 36) 1 20000;
      KWord (SA (EVar 32) 32) 8 (EVar 33); KWord (SA (EVar 32) 16) 8 (EVar 34);
      KWord (SA (EVar 32) 44) 4 (ELit 20); KWord (SA (EVar 32) 48) 4 (ELit 20);
      KWord (SA (EVar 32) 52) 4 (ELit 41); KWord (SA (EVar 32) 56) 4 (ELit 41);
      KWord (SA (EVar 32) 64) 4 (EVar 35); KWord (SA (EVar 32) 68) 4 (EVar 36)]).
  { ex_know R. }
  ex_open HR HK Hms Hlf.
  ex_cont 400%nat [0x3b17c%Z] (SCR [false; false; false; false; false; false; false; false; false; false] [EVar 38] []) HR Hlf HK Hms.
  all: lazymatch goal with
       | |- reach _ _ _ => idtac
       | |- ex _ => gjb_rd bc Hbc
       | |- _ => gjb_sc
       end.
  lazymatch type of Hms with msteps _ _ (@mkst _ ?RR _ _ _) => set (R3 := RR) in * end.
  assert (AGp2 : regs_agree (fun r => In r GJB) R R3) by (ex_agree HRo HR).
  assert (K2 : getr R3 2%bv = Z_to_bv 64 sf) by (ex_reg R HR).
  assert (K5 : getr R3 5%bv = Z_to_bv 64 41) by (ex_reg R HR).
  assert (K6 : getr R3 6%bv = Z_to_bv 64 0) by (ex_reg R HR).
  assert (K7 : getr R3 7%bv = Z_to_bv 64 keli) by (ex_reg R HR).
  assert (K8 : getr R3 8%bv = Z_to_bv 64 rng) by (ex_reg R HR).
  assert (K9 : getr R3 9%bv = Z_to_bv 64 datat) by (ex_reg R HR).
  assert (K11 : getr R3 11%bv = Z_to_bv 64 i) by (ex_reg R HR).
  assert (K12 : getr R3 12%bv = Z_to_bv 64 1) by (ex_reg R HR).
  assert (K13 : getr R3 13%bv = Z_to_bv 64 1) by (ex_reg R HR).
  assert (K14 : getr R3 14%bv = Z_to_bv 64 3) by (ex_reg R HR).
  assert (K15 : getr R3 15%bv = Z_to_bv 64 (datad + Wd * i)) by (ex_reg R HR).
  assert (K16 : getr R3 16%bv = Z_to_bv 64 j) by (ex_reg R HR).
  assert (K17 : getr R3 17%bv = Z_to_bv 64 j) by (ex_reg R HR).
  assert (K19 : getr R3 19%bv = Z_to_bv 64 wplt) by (ex_reg R HR).
  assert (K28 : getr R3 28%bv = Z_to_bv 64 (bv_unsigned bc)) by (ex_reg R HR).
  assert (K29 : getr R3 29%bv = Z_to_bv 64 0)
    by (first [ solve [ex_reg R HR] | (gjb_srv HR (29%bv : bv 5); gjb_z; first [reflexivity | f_equal; lia]) ]).
  assert (K30 : getr R3 30%bv = Z_to_bv 64 41) by (ex_reg R HR).
  assert (K31 : getr R3 31%bv = Z_to_bv 64 164) by (ex_reg R HR).
  apply (reach_msteps _ _ _ _ Hms). clear Hms.
  lazymatch goal with |- context [mem_denot ?E M []] => change (mem_denot E M []) with M end.
  eapply reach_msteps.
  { repeat first [ gjb_step F_3b168 D_3b168 | gjb_step F_3b16c D_3b16c | gjb_step F_3b170 D_3b170
                 | gjb_step F_3b174 D_3b174 | gjb_step F_3b178 D_3b178 ].
    apply mst_refl. }
  lazymatch goal with |- reach _ (@mkst (mkFP ?fr1 _) ?rg1 _ _ _) _ => set (FR1 := fr1) in *; set (RG1 := rg1) in * end.
  assert (F13 : reg_get FR1 13%bv = nan_box (Z_to_bv 32 p_zero))
    by (unfold FR1; rewrite ?fpv_get_other by reg_neq_tac; rewrite ?fpv_get_same; rewrite F15; vm_compute; reflexivity).
  assert (F14 : reg_get FR1 14%bv = nan_box (Z_to_bv 32 p_zero))
    by (unfold FR1; rewrite ?fpv_get_other by reg_neq_tac; rewrite ?fpv_get_same; rewrite F15; vm_compute; reflexivity).
  assert (FQ1 : ge_fq fr FR1)
    by (intros r N10 N11 N12 N13 N14; unfold FR1; rewrite ?fpv_get_other by assumption; reflexivity).
  pose proof (bv_unsigned_in_range _ bc) as Hbcr. unfold bv_modulus in Hbcr. cbn in Hbcr.
  eapply reach_bind.
  { eapply (gk_loop 41%nat FR1 RG1 FR1 cs RG1 M Wt hs datat keli arrk rng arrr rrow (bv_unsigned bc) i j 0 rowk wplt p_zero p_zero kf rf).
    all: try lia.
    all: try assumption.
    all: lazymatch goal with
         | |- ex _ => exists bc; split; [match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                       match type of Hbc with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a with a' by (f_equal; nia); exact Hbc end end | reflexivity]
         | |- ge_acc _ _ _ => split; assumption
         | |- ge_avg _ _ _ _ => exact ge_avg_init
         | |- regs_agree _ _ _ => intros r _; reflexivity
         | |- ge_fq _ _ => intros r _ _ _ _ _; reflexivity
         | |- (?x mod 4 = 0)%Z => match goal with H : x = (4 * ?y)%Z |- _ => rewrite H, Z.mul_comm; apply Z_mod_mult end
         end. }
  intros fin (fr2 & cs2 & regs2 & s2 & nv2 & -> & FZ2 & AG2 & FQ2 & ACC2 & AVG2).
  assert (G : forall k : reg, ~ In k GKL -> getr regs2 k = getr RG1 k) by (intros k Hk; exact (AG2 k Hk)).
  replace (0x3b2d8 : word) with (Z_to_bv 64 0x3b2d8) by (apply bv_eq; reflexivity).
  eapply reach_weaken; [| eapply (gjb_post fr2 cs2 regs2 M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j s2 nv2
                                    rowk kf rf FZ2 GEO0 (RD M RI) SOKd RI Hi Hj); first [ exact ACC2 | exact AVG2 |
                                    (rewrite G by notin_list; assumption) ] ].
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & ST' & X5 & AG' & FQ').
  exists fr', cs', regs', M'. split; [reflexivity |]. split; [exact FZ' |]. split; [exact ST' |]. split; [exact X5 |].
  split.
  - eapply regs_agree_trans; [exact AG |]. eapply regs_agree_trans; [exact AGp1 |]. eapply regs_agree_trans; [exact AGp2 |].
    eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG'].
  - intros r N10 N11 N12 N13 N14. rewrite (FQ' r N10 N11 N12 N13 N14), (FQ2 r N10 N11 N12 N13 N14), (FQ1 r N10 N11 N12 N13 N14).
    exact (FQ r N10 N11 N12 N13 N14).
Qed.
End GJ.

(* [comment removed for export] *)
Lemma gj_loop : forall (n : nat) fr0 regs0 fr cs regs (M0 M : word -> option byte) (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j : Z) (rowk : Z -> Z)
    (kf : Z -> Z -> Z) (rf : Z -> Z),
  Z.of_nat n = (w - j)%Z -> (0 <= j < w)%Z -> frm_zero cs -> ge_geo sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow ->
  (forall M', rinv [(datad, (Wd * h)%Z)] M0 M' -> ge_rd M' sf w h Wt hs datat datad keli arrk rng arrr rrow rowk kf rf) ->
  store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat (Wd * h)) = true -> rinv [(datad, (Wd * h)%Z)] M0 M ->
  (0 <= i < h)%Z ->
  getr regs 2 = Z_to_bv 64 sf -> getr regs 16 = Z_to_bv 64 j -> getr regs 17 = Z_to_bv 64 j -> getr regs 15 = Z_to_bv 64 (datad + Wd * i) ->
  getr regs 11 = Z_to_bv 64 i -> getr regs 19 = Z_to_bv 64 wplt -> getr regs 8 = Z_to_bv 64 rng -> getr regs 9 = Z_to_bv 64 datat ->
  getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 3 -> reg_get fr 15%bv = nan_box (Z_to_bv 32 0) ->
  regs_agree (fun r => In r GJL) regs0 regs -> ge_fq fr0 fr ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3b0b4 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b05c : word) M' rom /\ frm_zero cs' /\ rinv [(datad, (Wd * h)%Z)] M0 M' /\
                getr regs' 5 = Z_to_bv 64 w /\ regs_agree (fun r => In r GJL) regs0 regs' /\ ge_fq fr0 fr').
Proof.
  induction n as [|n IH]; intros fr0 regs0 fr cs regs M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j rowk kf rf
    Hn Hj FZ GEO RD SOK RI Hi E2 E16 E17 E15 E11 E19 E8 E9 E12 E13 E14 F15 AG FQ; [lia|].
  eapply reach_bind.
  { apply (gj_body fr regs fr cs regs M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i j rowk kf rf
             FZ GEO RD SOK RI Hi Hj E2 E16 E17 E15 E11 E19 E8 E9 E12 E13 E14 F15 (regs_agree_refl _ _) ltac:(unfold ge_fq; intros; reflexivity)). }
  intros fin (fr1 & cs1 & regs1 & M1 & -> & FZ1 & (p & bs & Hp & Hbs & EM1) & E5 & AG1 & FQ1).
  pose proof GEO as G. unfold ge_geo in G. decompose [and] G. clear G.
  assert (RI1 : rinv [(datad, (Wd * h)%Z)] M0 M1).
  { rewrite EM1. apply (rinv_wbytes _ M0 M p 1 bs RI); [rewrite Hbs; reflexivity | lia | lia |].
    exists (datad, (Wd * h)%Z). split; [cbn [In]; left; reflexivity | cbn [fst snd]; lia]. }
  unfold ge_fq in FQ, FQ1.
  assert (FQr : ge_fq fr0 fr1).
  { unfold ge_fq. intros r R10 R11 R12 R13 R14. rewrite (FQ1 r R10 R11 R12 R13 R14). exact (FQ r R10 R11 R12 R13 R14). }
  assert (F15' : reg_get fr1 15%bv = nan_box (Z_to_bv 32 0)) by (rewrite (FQ1 15%bv) by reg_neq_tac; exact F15).
  assert (AGr : regs_agree (fun r => In r GJL) regs0 regs1).
  { eapply regs_agree_trans; [exact AG|]. eapply regs_agree_mono; [|exact AG1].
    intros r Hr. unfold GJB in Hr. unfold GJL. cbn [In] in Hr |- *. tauto. }
  assert (G2 : getr regs1 2 = Z_to_bv 64 sf) by (rewrite (AG1 2) by (unfold GJB; notin_list); exact E2).
  assert (G16 : getr regs1 16 = Z_to_bv 64 j) by (rewrite (AG1 16) by (unfold GJB; notin_list); exact E16).
  assert (G17 : getr regs1 17 = Z_to_bv 64 j) by (rewrite (AG1 17) by (unfold GJB; notin_list); exact E17).
  assert (G15 : getr regs1 15 = Z_to_bv 64 (datad + Wd * i)) by (rewrite (AG1 15) by (unfold GJB; notin_list); exact E15).
  assert (G11 : getr regs1 11 = Z_to_bv 64 i) by (rewrite (AG1 11) by (unfold GJB; notin_list); exact E11).
  assert (G19 : getr regs1 19 = Z_to_bv 64 wplt) by (rewrite (AG1 19) by (unfold GJB; notin_list); exact E19).
  assert (G8 : getr regs1 8 = Z_to_bv 64 rng) by (rewrite (AG1 8) by (unfold GJB; notin_list); exact E8).
  assert (G9 : getr regs1 9 = Z_to_bv 64 datat) by (rewrite (AG1 9) by (unfold GJB; notin_list); exact E9).
  assert (G12 : getr regs1 12 = Z_to_bv 64 1) by (rewrite (AG1 12) by (unfold GJB; notin_list); exact E12).
  assert (G13 : getr regs1 13 = Z_to_bv 64 1) by (rewrite (AG1 13) by (unfold GJB; notin_list); exact E13).
  assert (G14 : getr regs1 14 = Z_to_bv 64 3) by (rewrite (AG1 14) by (unfold GJB; notin_list); exact E14).
  destruct (Z_lt_ge_dec (j + 1) w) as [Hlt | Hge].
  - eapply reach_msteps.
    { zv F_3b330 D_3b330 (Z_to_bv 64 (j + 1)).
      zvw F_3b334 D_3b334 (Z_to_bv 64 (j + 1)).
      stepb_tk F_3b338 D_3b338 ltac:(condZ).
      apply mst_refl. }
    apply (IH fr0 regs0 fr1 cs1 _ M0 M1 sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i (j + 1)%Z rowk kf rf
             ltac:(lia) ltac:(lia) FZ1 GEO RD SOK RI1 Hi);
      try (gres; first [exact G2 | exact G15 | exact G11 | exact G19 | exact G8 | exact G9 | exact G12 | exact G13 | exact G14 | reflexivity]).
    + exact F15'.
    + apply regs_agree_upd; [unfold GJL; in_list|]. apply regs_agree_upd; [unfold GJL; in_list|]. exact AGr.
    + exact FQr.
  - eapply reach_msteps.
    { zv F_3b330 D_3b330 (Z_to_bv 64 (j + 1)).
      zvw F_3b334 D_3b334 (Z_to_bv 64 (j + 1)).
      stepb_ft F_3b338 D_3b338 ltac:(condZ).
      stepj F_3b33c D_3b33c.
      apply mst_refl. }
    apply reach_done. do 4 eexists. split; [reflexivity|].
    split; [exact FZ1|]. split; [exact RI1|]. split; [gres; exact E5|]. split.
    + apply regs_agree_upd; [unfold GJL; in_list|]. apply regs_agree_upd; [unfold GJL; in_list|]. exact AGr.
    + exact FQr.
Qed.

(* [comment removed for export] *)
Lemma gi_loop : forall (n : nat) fr0 regs0 fr cs regs (M0 M : word -> option byte) (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i : Z) (rowk : Z -> Z)
    (kf : Z -> Z -> Z) (rf : Z -> Z),
  Z.of_nat n = (h - i)%Z -> (0 <= i < h)%Z -> frm_zero cs -> ge_geo sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow ->
  (forall M', rinv [(datad, (Wd * h)%Z)] M0 M' -> ge_rd M' sf w h Wt hs datat datad keli arrk rng arrr rrow rowk kf rf) ->
  store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat (Wd * h)) = true -> rinv [(datad, (Wd * h)%Z)] M0 M ->
  getr regs 2 = Z_to_bv 64 sf -> getr regs 11 = Z_to_bv 64 i -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 19 = Z_to_bv 64 wplt ->
  getr regs 8 = Z_to_bv 64 rng -> getr regs 9 = Z_to_bv 64 datat ->
  getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 3 -> reg_get fr 15%bv = nan_box (Z_to_bv 32 0) ->
  regs_agree (fun r => In r GIL) regs0 regs -> ge_fq fr0 fr ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3b068 : word) M rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b3cc : word) M' rom /\ frm_zero cs' /\ rinv [(datad, (Wd * h)%Z)] M0 M' /\
                regs_agree (fun r => In r GIL) regs0 regs' /\ ge_fq fr0 fr').
Proof.
  intros n; induction n as [|n IH];
    intros fr0 regs0 fr cs regs M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i rowk kf rf
      Hn Hi FZ G RD SOK RI H2 H11 H10 H19 H8 H9 H12 H13 H14 F15 AG FQ; [lia|].
  pose proof G as G'. unfold ge_geo in G'.
  destruct G' as (Hsf1 & Hsf2 & Hw & Hh & Hhs & Hwplt & HWt & HwWt & HWths & Hwpld & HWd & HwWd & HWdh & Hdt4 & Hdt1 & Hdt2 & Hdd4 & Hdd1 & Hdd2 & _).
  destruct (RD M RI) as (_ & Rdatad & _ & _ & _ & _ & _ & Rw & _).
  assert (HWd0 : (0 <= Wd)%Z) by lia.
  assert (HWd26 : (Wd <= 2 ^ 26)%Z) by nia.
  assert (Hiw : (0 <= i * wpld <= 2 ^ 24)%Z) by (rewrite HWd in HWdh; nia).
  assert (HWi : (0 <= Wd * i <= Wd * h)%Z) by nia.
  norm_pc.
  stepat F_3b068 D_3b068 (Z_to_bv 64 (i * wpld)) ltac:(gres; pin; rewrite zbv_mul; reflexivity).
  stepat F_3b06c D_3b06c (Z_to_bv 64 (i * wpld)) ltac:(gres; pin; rewrite zbv_mulw_small by lia; reflexivity).
  stepb_ft F_3b070 D_3b070 ltac:(rewrite c_eq_Zm; apply Z.eqb_refl).
  stepat F_3b074 D_3b074 (Z_to_bv 64 (i * wpld)) ltac:(gres; imm_norm; rewrite zbv_addiw_small by lia; f_equal; lia).
  stepat F_3b078 D_3b078 (Z_to_bv 64 (Wd * i)) ltac:(gres; imm_norm; rewrite zbv_slli by lia; f_equal; rewrite HWd; ring).
  stepLD F_3b07c D_3b07c (Z_to_le_bytes 8 datad) (Z_to_bv 64 datad) ltac:(addr_norm; exact Rdatad) ltac:(apply lez8; lia).
  stepat F_3b080 D_3b080 (Z_to_bv 64 (datad + Wd * i)) ltac:(gres; rewrite zbv_add; reflexivity).
  stepat F_3b084 D_3b084 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_seqz_nz by lia; reflexivity).
  stepb_ft F_3b088 D_3b088 ltac:(pin; first [reflexivity | vm_compute; reflexivity]).
  stepLD F_3b08c D_3b08c (Z_to_le_bytes 8 datad) (Z_to_bv 64 datad) ltac:(addr_norm; exact Rdatad) ltac:(apply lez8; lia).
  stepat F_3b090 D_3b090 (Z_to_bv 64 0) ltac:(gres; rewrite zbv_sltu_ge by lia; reflexivity).
  stepat F_3b094 D_3b094 (Z_to_bv 64 0) ltac:(gres; imm_norm; rewrite zbv_slti0 by lia; reflexivity).
  stepat F_3b098 D_3b098 (Z_to_bv 64 0) ltac:(gres; first [reflexivity | bveq]).
  stepat F_3b09c D_3b09c (Z_to_bv 64 1) ltac:(gres; imm_norm; first [reflexivity | bveq]).
  stepb_ft F_3b0a0 D_3b0a0 ltac:(first [reflexivity | vm_compute; reflexivity]).
  stepLD F_3b0a4 D_3b0a4 (Z_to_le_bytes 4 w) (Z_to_bv 64 w) ltac:(addr_norm; exact Rw) ltac:(apply lez4; lia).
  rewrite ?(v_lw_small w) by lia.
  stepb_ft F_3b0a8 D_3b0a8 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
  zv F_3b0ac D_3b0ac (Z_to_bv 64 0).
  zv F_3b0b0 D_3b0b0 (Z_to_bv 64 0).
  lazymatch goal with |- reach _ (@mkst _ ?R _ _ _) _ =>
    apply (reach_bind SEGS _ _ _ (gj_loop (Z.to_nat w) fr R fr cs R M0 M sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow i 0%Z rowk kf rf
      ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) FZ G RD SOK RI ltac:(lia)
      ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
      ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
      ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) F15
      (regs_agree_refl _ _) ltac:(unfold ge_fq; intros; reflexivity)))
  end.
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & _ & AG' & FQ').
  destruct (RD M' RI') as (_ & _ & _ & _ & _ & _ & Rh' & _).
  assert (E2 : getr regs' 2 = Z_to_bv 64 sf) by (rewrite (AG' 2%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E11 : getr regs' 11 = Z_to_bv 64 i) by (rewrite (AG' 11%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E10 : getr regs' 10 = Z_to_bv 64 wpld) by (rewrite (AG' 10%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E19 : getr regs' 19 = Z_to_bv 64 wplt) by (rewrite (AG' 19%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E8 : getr regs' 8 = Z_to_bv 64 rng) by (rewrite (AG' 8%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E9 : getr regs' 9 = Z_to_bv 64 datat) by (rewrite (AG' 9%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E12 : getr regs' 12 = Z_to_bv 64 1) by (rewrite (AG' 12%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E13 : getr regs' 13 = Z_to_bv 64 1) by (rewrite (AG' 13%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  assert (E14 : getr regs' 14 = Z_to_bv 64 3) by (rewrite (AG' 14%bv) by (cbv beta; unfold GJL; notin_list); gres; pin; reflexivity).
  stepLD F_3b05c D_3b05c (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh') ltac:(apply lez4; lia).
  rewrite ?(v_lw_small h) by lia.
  stepat F_3b060 D_3b060 (Z_to_bv 64 (i + 1)) ltac:(gres; pin; imm_norm; rewrite zbv_addiw_small by lia; reflexivity).
  assert (RA : forall RL, regs_agree (fun r => In r GIL) regs' RL -> regs_agree (fun r => In r GIL) regs0 RL).
  { intros RL HL. eapply regs_agree_trans; [exact AG|]. eapply regs_agree_trans; [|exact HL].
    eapply regs_agree_trans; [|eapply regs_agree_mono; [|exact AG']].
    - repeat (apply regs_agree_upd; [cbv beta; unfold GIL; in_list|]); apply regs_agree_refl.
    - intros r Hr; cbv beta in Hr |- *; unfold GJL in Hr; unfold GIL; cbn [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr. }
  assert (FQ2 : ge_fq fr0 fr').
  { unfold ge_fq in *. intros r a b c d e. rewrite FQ' by assumption. apply FQ; assumption. }
  destruct (Z_lt_ge_dec (i + 1) h) as [Hlt|Hge].
  - stepb_ft F_3b064 D_3b064 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
    lazymatch goal with |- reach _ (@mkst _ ?RL _ _ _) _ =>
      exact (IH fr0 regs0 fr' cs' RL M0 M' sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow (i + 1)%Z rowk kf rf
        ltac:(lia) ltac:(lia) FZ' G RD SOK RI'
        ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
        ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
        ltac:(gres; pin; reflexivity)
        ltac:(unfold ge_fq in FQ'; rewrite FQ' by reg_neq_tac; exact F15)
        ltac:(apply RA; repeat (apply regs_agree_upd; [cbv beta; unfold GIL; in_list|]); apply regs_agree_refl)
        FQ2)
    end.
  - stepb_tk F_3b064 D_3b064 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_ge; lia).
    apply reach_done.
    do 4 eexists. split; [reflexivity|].
    split; [exact FZ'|]. split; [exact RI'|]. split; [|exact FQ2].
    apply RA. repeat (apply regs_agree_upd; [cbv beta; unfold GIL; in_list|]). apply regs_agree_refl.
Qed.

(* [comment removed for export] *)
Lemma ge_nest : forall fr cs regs (M0 : word -> option byte) (sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow : Z) (rowk : Z -> Z)
    (kf : Z -> Z -> Z) (rf : Z -> Z),
  frm_zero cs -> ge_geo sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow ->
  (forall M', rinv [(datad, (Wd * h)%Z)] M0 M' -> ge_rd M' sf w h Wt hs datat datad keli arrk rng arrr rrow rowk kf rf) ->
  store_ok SEGS M0 (Z_to_bv 64 datad) (Z.to_nat (Wd * h)) = true ->
  getr regs 2 = Z_to_bv 64 sf -> getr regs 10 = Z_to_bv 64 wpld -> getr regs 9 = Z_to_bv 64 datat -> getr regs 19 = Z_to_bv 64 wplt ->
  getr regs 8 = Z_to_bv 64 rng ->
  reach SEGS (@mkst (mkFP fr cs) regs (0x3aefc : word) M0 rom)
    (fun fin => exists fr' cs' regs' M', fin = @mkst (mkFP fr' cs') regs' (0x3b3cc : word) M' rom /\ frm_zero cs' /\ rinv [(datad, (Wd * h)%Z)] M0 M' /\
                regs_agree (fun r => In r GNL) regs regs' /\ ge_fp fr fr').
Proof.
  intros fr cs regs M0 sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow rowk kf rf FZ G RD SOK H2 H10 H9 H19 H8.
  pose proof G as G'. unfold ge_geo in G'.
  destruct G' as (Hsf1 & Hsf2 & Hw & Hh & Hhs & Hwplt & HWt & HwWt & HWths & Hwpld & HWd & HwWd & HWdh & Hdt4 & Hdt1 & Hdt2 & Hdd4 & Hdd1 & Hdd2 & _).
  destruct (RD M0 (rinv_refl _ _)) as (_ & Rdatad & _ & _ & _ & _ & Rh & _).
  assert (HWd0 : (0 <= Wd)%Z) by lia.
  assert (HWh : (0 <= Wd * h)%Z) by nia.
  norm_pc.
  stepLD F_3aefc D_3aefc (Z_to_le_bytes 4 h) (Z_to_bv 64 h) ltac:(addr_norm; exact Rh) ltac:(apply lez4; lia).
  rewrite ?(v_lw_small h) by lia.
  stepb_ft F_3af00 D_3af00 ltac:(rewrite c_lts_Z by lia; apply Z.ltb_lt; lia).
  zv F_3af04 D_3af04 (Z_to_bv 64 0).
  stepLD F_3af08 D_3af08 (Z_to_le_bytes 8 datad) (Z_to_bv 64 datad) ltac:(addr_norm; exact Rdatad) ltac:(apply lez8; lia).
  stepat F_3af0c D_3af0c (Z_to_bv 64 1) ltac:(gres; pin; rewrite zbv_snez by lia; reflexivity).
  stepat F_3af10 D_3af10 (Z_to_bv 64 1) ltac:(gres; pin; rewrite zbv_snez by lia; reflexivity).
  zv F_3af14 D_3af14 (Z_to_bv 64 3).
  eapply reach_step; [reflexivity | eapply fp_step_fmv_w_x; [exact F_3af18 | reflexivity | exact D_3af18] | step_simpl].
  cbn [fp_regs fp_csr].
  stepj F_3af1c D_3af1c.
  lazymatch goal with |- reach _ (@mkst (mkFP ?F1 _) ?R1 _ _ _) _ =>
    eapply reach_weaken;
    [ | exact (gi_loop (Z.to_nat h) F1 R1 F1 cs R1 M0 M0 sf w h wplt Wt hs wpld Wd datat datad keli arrk rng arrr rrow 0%Z rowk kf rf
          ltac:(rewrite Z2Nat.id by lia; lia) ltac:(lia) FZ G RD SOK (rinv_refl _ _)
          ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
          ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity) ltac:(gres; pin; reflexivity)
          ltac:(gres; pin; reflexivity)
          ltac:(rewrite fpv_get_same; gres; first [reflexivity | f_equal; bveq])
          (regs_agree_refl _ _) ltac:(unfold ge_fq; intros; reflexivity)) ]
  end.
  intros fin (fr' & cs' & regs' & M' & -> & FZ' & RI' & AG' & FQ').
  do 4 eexists. split; [reflexivity|].
  split; [exact FZ'|]. split; [exact RI'|]. split.
  - eapply regs_agree_trans; [|eapply regs_agree_mono; [|exact AG']].
    + repeat (apply regs_agree_upd; [cbv beta; unfold GNL; in_list|]); apply regs_agree_refl.
    + intros r Hr; cbv beta in Hr |- *; unfold GIL in Hr; unfold GNL; cbn [In] in Hr;
        repeat (destruct Hr as [<-|Hr]; [in_list|]); destruct Hr.
  - unfold ge_fp, ge_fq in *. intros r a b c d e f.
    rewrite FQ' by assumption. apply fpv_get_other. exact f.
Qed.

End Segs.
