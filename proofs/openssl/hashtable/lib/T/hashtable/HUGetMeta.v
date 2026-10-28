(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim Frame
  HUExitBase RefMemcpyLib MallocDefs LibMaskBits HU_code_26c000_26d000.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn1_of_mem : forall M (a : word) b, M a = Some b -> rdn RSEGS M a 1%nat = Some [b].
Proof. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma bytes_le_to_Z_2 : forall v : word, (bv_unsigned v < 2^16)%Z ->
  bytes_le_to_Z (word_to_le_bytes 2 v) = bv_unsigned v.
Proof.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2^16)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma pow_2_1 : (2^1 = 2)%Z. Proof. reflexivity. Qed.
Lemma pow_2_8 : (2^8 = 256)%Z. Proof. reflexivity. Qed.

Lemma u8_Z2bv : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply (bv_wrap_small 8). change (bv_modulus 8) with 256%Z. lia. Qed.

(* [comment removed for export] *)
Ltac stepLHU F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | eapply step_lhu with (bs := bsv) (v := vv);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sz_img (mem : word -> option byte) : Prop :=
  forall i, (0x72234 <= i < 0x72294)%Z -> mem (Z_to_bv 64 i) = None.

Lemma sz_entry_none : forall k, (k < 48)%nat ->
  exists bs, rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x72234 + 2 * Z.of_nat k)) 2%nat = Some bs
             /\ bytes_le_to_Z bs = size_class (Z.of_nat k).
Proof.
  intros k Hk.
  enum_nat k 48%nat ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Z.mul Pos.mul];
    lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in
      lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | vm_compute; reflexivity] end end).
Qed.

Lemma sz_entry : forall mem sc, sz_img mem -> (0 <= sc < 48)%Z ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 (0x72234 + 2 * sc)) 2%nat = Some bs
             /\ bytes_le_to_Z bs = size_class sc.
Proof.
  intros mem sc Himg Hsc.
  rewrite (rdn_img RSEGS mem _ 2 0x72234 0x72294 Himg) by (cbn; lia).
  destruct (sz_entry_none (Z.to_nat sc)) as (bs & Hbs & Hv); [lia|].
  rewrite Z2Nat.id in Hbs, Hv by lia. exists bs. split; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record gm_reads (mem : word -> option byte) (p M g idx rc q W avail freed : Z) (sec : word) : Prop := GMR {
  gm_b4   : mem (Z_to_bv 64 (p - 4)) = Some (Z_to_bv 8 0);
  gm_b3   : mem (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * rc));
  gm_off  : rdn RSEGS mem (Z_to_bv 64 (p - 2)) 2%nat = Some (word_to_le_bytes 2 (Z_to_bv 64 q));
  gm_meta : rdn RSEGS mem (Z_to_bv 64 M) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g));
  gm_mem  : rdn RSEGS mem (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  gm_W    : rdn RSEGS mem (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  gm_av   : rdn RSEGS mem (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail));
  gm_fr   : rdn RSEGS mem (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed));
  gm_area : rdn RSEGS mem (Z_to_bv 64 (g - g mod 4096)) 8%nat = Some (word_to_le_bytes 8 sec);
  gm_sec  : rdn RSEGS mem (Z_to_bv 64 0x351df0) 8%nat = Some (word_to_le_bytes 8 sec);
  gm_img  : sz_img mem
}.

(* [comment removed for export] *)
Record gm_pure (p M g idx rc q W avail freed : Z) : Prop := GMP {
  gp_al   : (p mod 16 = 0)%Z;
  gp_idx  : (0 <= idx <= w_lastidx W)%Z;
  gp_rc   : (0 <= rc < 8)%Z;
  gp_q    : (0 <= q < 65536)%Z;
  gp_p    : (p = M + 16 + 16 * q)%Z;
  gp_M    : (0 <= M)%Z;
  gp_pe   : (p < 2^64)%Z;
  gp_g    : (0 <= g)%Z; gp_g2 : (g + 40 < 2^64)%Z;
  gp_W    : (0 <= W < 2^64)%Z;
  gp_av   : (0 <= avail < 2^32)%Z; gp_avb : Z.testbit avail idx = false;
  gp_fr   : (0 <= freed < 2^32)%Z; gp_frb : Z.testbit freed idx = false;
  gp_sc   : ((w_sizeclass W < 48 /\ size_class (w_sizeclass W) * idx <= q
              /\ q < size_class (w_sizeclass W) * (idx + 1))
             \/ (w_sizeclass W = 63 /\ w_maplen W <> 0 /\ w_lastidx W = 0))%Z;
  gp_ml   : (w_maplen W <> 0 -> q <= w_maplen W * 256 - 1)%Z
}.

(* [comment removed for export] *)
Definition gm_clob : list reg := [10; 11; 12; 13; 14; 15]%bv.
Definition gm_keeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, ~ In r gm_clob -> getr regs' r = getr regs r.
Lemma gm_keeps_upd : forall regs regs' (rd : reg) v,
  gm_keeps regs regs' -> In rd gm_clob -> gm_keeps regs (regupd regs' rd v).
Proof. intros regs regs' rd v K Hin r Hr. rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hr Hin). Qed.
Lemma gm_keeps_refl : forall regs, gm_keeps regs regs. Proof. intros regs r _. reflexivity. Qed.
Ltac solve_gm_keeps :=
  repeat (apply gm_keeps_upd; [| cbv [gm_clob In]; repeat first [left; reflexivity | right] ]); apply gm_keeps_refl.

(* [comment removed for export] *)
Lemma gm_keeps_reg : forall regs regs' (r : reg),
  gm_keeps regs regs' ->
  (r <> 10)%bv -> (r <> 11)%bv -> (r <> 12)%bv -> (r <> 13)%bv -> (r <> 14)%bv -> (r <> 15)%bv ->
  getr regs' r = getr regs r.
Proof.
  intros regs regs' r K ? ? ? ? ? ?. apply K. cbv [gm_clob In]. intuition congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Walk.
  Variables (regs : bvmap 5 word) (mem : word -> option byte) (rom : word -> option byte) (ret : word).
  Variables (p M g idx rc q W avail freed : Z) (sec : word).
  Hypothesis R : gm_reads mem p M g idx rc q W avail freed sec.
  Hypothesis P : gm_pure p M g idx rc q W avail freed.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 p.
  Hypothesis H1 : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.

  Let h3 := (idx + 32 * rc)%Z.

  (* [comment removed for export] *)
  Lemma r_last : (0 <= w_lastidx W < 32)%Z.
  Proof. unfold w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_sc : (0 <= w_sizeclass W < 64)%Z.
  Proof. unfold w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_ml : (0 <= w_maplen W < 2^52)%Z.
  Proof. destruct P. unfold w_maplen. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
  Lemma r_gm : (0 <= g mod 4096 < 4096)%Z.
  Proof. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_h3 : (0 <= h3 < 256)%Z /\ (h3 mod 32 = idx)%Z.
  Proof.
    destruct P. pose proof r_last. subst h3. split; [lia|].
    replace (idx + 32 * rc)%Z with (idx + rc * 32)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma E_al : v_andi (Z_to_bv 64 p) 15 = Z_to_bv 64 0.
  Proof.
    destruct P. rewrite v_andi_Z by lia. change 15%Z with (2^4 - 1)%Z. rewrite land_ones_mod by lia.
    change (2^4)%Z with 16%Z. rewrite gp_al0. reflexivity.
  Qed.
  Lemma E_b3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 8 h3)) = Z_to_bv 64 h3.
  Proof. pose proof r_h3. rewrite u8_Z2bv by lia. reflexivity. Qed.
  Lemma E_idx : v_andi (Z_to_bv 64 h3) 31 = Z_to_bv 64 idx.
  Proof.
    pose proof r_h3. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia.
    change (2^5)%Z with 32%Z. f_equal. lia.
  Qed.
  Lemma E_off4 : v_slli (Z_to_bv 64 q) 4 = Z_to_bv 64 (16 * q).
  Proof. destruct P. rewrite v_slli_Z by (cbn; lia). f_equal. cbn. lia. Qed.
  Lemma E_base : v_sub (Z_to_bv 64 p) (Z_to_bv 64 (16 * q)) = Z_to_bv 64 (M + 16).
  Proof. destruct P. rewrite v_sub_ZZ by lia. f_equal. lia. Qed.
  Lemma E_last : v_andi (Z_to_bv 64 W) 31 = Z_to_bv 64 (w_lastidx W).
  Proof. destruct P. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_avt : v_and (v_lw (Z_to_bv 64 avail)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
  Proof. destruct P. pose proof r_last. apply mask_test_clear; try lia. assumption. Qed.
  Lemma E_frt : v_and (v_lw (Z_to_bv 64 freed)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
  Proof. destruct P. pose proof r_last. apply mask_test_clear; try lia. assumption. Qed.
  Lemma E_area : v_and (Z_to_bv 64 g) (Z_to_bv 64 18446744073709547520) = Z_to_bv 64 (g - g mod 4096).
  Proof. destruct P. rewrite v_and_Z by lia. f_equal. apply land_pagemask. lia. Qed.
  Lemma E_sc : v_srli (v_slli (Z_to_bv 64 W) 52) 58 = Z_to_bv 64 (w_sizeclass W).
  Proof.
    destruct P. unfold v_srli, v_slli, w_sizeclass. f_equal. rewrite (u_Z2bv W) by lia.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. apply sc_extract. lia.
  Qed.
  Lemma E_ml : v_srli (Z_to_bv 64 W) 12 = Z_to_bv 64 (w_maplen W).
  Proof. destruct P. rewrite v_srli_Z by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac gm_prefix :=
    pose proof r_last as Hlast; pose proof r_sc as Hscr; pose proof r_ml as Hmlr; pose proof r_gm as Hgm;
    pose proof r_h3 as Hh3;
    destruct R as [Hb4 Hb3 Hoff Hmeta Hmem HW Hav Hfr Harea Hsec Himg];
    pose proof P as P'; destruct P' as [Hal Hidx Hrc Hq Hp HM Hpe Hg Hg2 HWr Havr Havb Hfrr Hfrb _ Hml];
    stepn F_26c234 D_26c234; rewrite H10, E_al;
    stepb_tk F_26c238 D_26c238 ltac:(cond_compute);
    stepLBU F_26c240 D_26c240 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact Hb4); vals_lit;
    stepLBU F_26c244 D_26c244 (Z_to_bv 8 h3) ltac:(addr_norm; apply rdn1_of_mem; exact Hb3); rewrite E_b3;
    stepLHU F_26c248 D_26c248 (word_to_le_bytes 2 (Z_to_bv 64 q)) (Z_to_bv 64 q)
      ltac:(addr_norm; exact Hoff) ltac:(apply bytes_le_to_Z_2; u_norm; lia);
    stepb_tk F_26c24c D_26c24c ltac:(cond_compute);
    stepn F_26c268 D_26c268; rewrite E_off4;
    stepn F_26c26c D_26c26c; rewrite H10, E_base;
    stepLD F_26c270 D_26c270 (word_to_le_bytes 8 (Z_to_bv 64 g)) (Z_to_bv 64 g)
      ltac:(replace (v_addi (Z_to_bv 64 (M + 16)) (-16)) with (Z_to_bv 64 M) by (unfold v_addi; unorm; f_equal; lia); exact Hmeta)
      ltac:(apply bytes_le_to_Z_8);
    stepLD8 F_26c274 D_26c274 (Z_to_bv 64 M);
    stepn F_26c278 D_26c278; addi_renorm; replace (M + 0)%Z with M by lia;
    stepn F_26c27c D_26c27c; rewrite E_idx;
    stepb_tk F_26c280 D_26c280 ltac:(apply c_eq_refl);
    stepLD8 F_26c288 D_26c288 (Z_to_bv 64 W);
    stepn F_26c28c D_26c28c; rewrite E_last;
    stepb_tk F_26c290 D_26c290 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepLD F_26c298 D_26c298 (word_to_le_bytes 4 (Z_to_bv 64 avail)) (Z_to_bv 64 avail)
      ltac:(addr_norm; exact Hav) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    stepn F_26c29c D_26c29c;
    stepn F_26c2a0 D_26c2a0;
    stepn F_26c2a4 D_26c2a4; rewrite E_avt;
    stepb_tk F_26c2a8 D_26c2a8 ltac:(cond_compute);
    stepLD F_26c2b0 D_26c2b0 (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed)
      ltac:(addr_norm; exact Hfr) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    stepn F_26c2b4 D_26c2b4; rewrite E_frt;
    stepb_tk F_26c2b8 D_26c2b8 ltac:(cond_compute);
    stepn F_26c2c0 D_26c2c0;
    stepn F_26c2c4 D_26c2c4;
    stepn F_26c2c8 D_26c2c8; rewrite E_area;
    stepLD8 F_26c2cc D_26c2cc sec;
    stepLD8 F_26c2d0 D_26c2d0 sec;
    stepb_tk F_26c2d4 D_26c2d4 ltac:(apply c_eq_refl);
    stepn F_26c2dc D_26c2dc;
    stepn F_26c2e0 D_26c2e0; rewrite E_sc;
    stepn F_26c2e4 D_26c2e4.

  (* [comment removed for export] *)
  Local Ltac gm_tail :=
    stepn F_26c328 D_26c328; rewrite E_ml;
    lazymatch goal with
    | Hz : (w_maplen W = 0)%Z |- _ =>
        stepb_tk F_26c32c D_26c32c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia)
    | Hnz : (w_maplen W <> 0)%Z |- _ =>
        stepb_ft F_26c32c D_26c32c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia);
        stepn F_26c330 D_26c330; rewrite (v_slli_Z (w_maplen W) 8) by (rewrite ?pow_2_8; lia); rewrite pow_2_8;
        stepn F_26c334 D_26c334; addi_renorm;
        stepb_tk F_26c338 D_26c338 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia)
    end;
    stepret F_26c340 D_26c340 ret ltac:(getr_hyps; reflexivity).

  Definition gm_goal : Prop :=
    exists regs',
      msteps RSEGS (mkst regs (0x2b1e20 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 q /\ gm_keeps regs regs'.

  (* [comment removed for export] *)
  Local Ltac gm_sized_walk :=
    gm_prefix;
    stepb_ft F_26c2e8 D_26c2e8 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_26c2ec D_26c2ec; rewrite (v_slli_Z (w_sizeclass W) 1) by (rewrite ?pow_2_1; lia); rewrite pow_2_1;
    stepn F_26c2f0 D_26c2f0;
    stepn F_26c2f4 D_26c2f4;
    stepn F_26c2f8 D_26c2f8; rewrite (v_add_ZZ 467508 (w_sizeclass W * 2)) by lia;
    replace (467508 + w_sizeclass W * 2)%Z with (0x72234 + 2 * w_sizeclass W)%Z by lia;
    lazymatch goal with Hsbs : rdn _ _ (Z_to_bv 64 (0x72234 + 2 * w_sizeclass W)%Z) 2%nat = Some ?sbs,
                        Hsv : bytes_le_to_Z ?sbs = _ |- _ =>
      stepLHU F_26c2fc D_26c2fc sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia)
    end;
    stepn F_26c300 D_26c300; rewrite (v_mul_Z (size_class (w_sizeclass W)) idx) by lia;
    stepb_tk F_26c304 D_26c304 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_26c30c D_26c30c; addi_renorm;
    stepn F_26c310 D_26c310; rewrite (v_mul_Z (idx + 1) (size_class (w_sizeclass W))) by lia;
    stepb_ft F_26c314 D_26c314 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia);
    stepn F_26c318 D_26c318;
    gm_tail;
    apply mst_refl.

  Local Ltac gm_post := split; [gres; reflexivity | split; [gres; reflexivity | solve_gm_keeps]].

  Lemma gm_sized :
    (w_sizeclass W < 48)%Z -> (size_class (w_sizeclass W) * idx <= q)%Z ->
    (q < size_class (w_sizeclass W) * (idx + 1))%Z -> gm_goal.
  Proof.
    intros Hsc48 Hlo Hhi. unfold gm_goal.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof r_sc; lia)) as Hszc.
    destruct (sz_entry mem (w_sizeclass W) (gm_img _ _ _ _ _ _ _ _ _ _ _ R) ltac:(pose proof r_sc; lia)) as (sbs & Hsbs & Hsv).
    destruct (Z.eq_dec (w_maplen W) 0) as [Hml0 | Hmln]; (eexists; split; [gm_sized_walk | gm_post]).
  Qed.

  (* [comment removed for export] *)
  Lemma gm_mmapped :
    (w_sizeclass W = 63)%Z -> (w_maplen W <> 0)%Z -> gm_goal.
  Proof.
    intros Hsc63 Hmln. unfold gm_goal.
    eexists. split.
    - gm_prefix.
      stepb_tk F_26c2e8 D_26c2e8 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_26c31c D_26c31c.
      stepb_tk F_26c320 D_26c320 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      gm_tail.
      apply mst_refl.
    - gm_post.
  Qed.

  Lemma get_meta_run_sec : gm_goal.
  Proof.
    destruct (gp_sc _ _ _ _ _ _ _ _ _ P) as [(Hsc48 & Hlo & Hhi) | (Hsc63 & Hmln & _)].
    - exact (gm_sized Hsc48 Hlo Hhi).
    - exact (gm_mmapped Hsc63 Hmln).
  Qed.
End Walk.

Theorem get_meta_run : forall regs mem rom (ret : word) (p M g idx rc q W avail freed : Z) (sec : word),
  gm_reads mem p M g idx rc q W avail freed sec -> gm_pure p M g idx rc q W avail freed ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b1e20 : word) mem rom) (mkst regs' ret mem rom)
    /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 q /\ gm_keeps regs regs'.
Proof.
  intros. eapply get_meta_run_sec; eassumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
