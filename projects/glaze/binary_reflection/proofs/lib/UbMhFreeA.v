(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhGetMeta.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.


Lemma rdn1_of_mem : forall M (a : word) b, M a = Some b -> rdn RSEGS M a 1%nat = Some [b].
Proof using. intros M a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma bytes_le_to_Z_2 : forall v : word, (bv_unsigned v < 2^16)%Z ->
  bytes_le_to_Z (word_to_le_bytes 2 v) = bv_unsigned v.
Proof using.
  intros v Hv. rewrite bytes_le_N. change (2 ^ (8 * Z.of_nat 2))%Z with (2^16)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma pow_2_1 : (2^1 = 2)%Z. Proof using. reflexivity. Qed.
Lemma pow_2_8 : (2^8 = 256)%Z. Proof using. reflexivity. Qed.

Lemma u8_Z2bv : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
Proof using. intros z Hz. rewrite Z_to_bv_unsigned. apply (bv_wrap_small 8). change (bv_modulus 8) with 256%Z. lia. Qed.

(* [comment removed for export] *)
End FPGen1.

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
Section FPGen2.
Context {fx : FPState}.

Definition sz_img (mem : word -> option byte) : Prop :=
  forall i, (0x2396c <= i < 0x239cc)%Z -> mem (Z_to_bv 64 i) = None.

Lemma sz_entry_none : forall k, (k < 48)%nat ->
  exists bs, rdn RSEGS (fun _ => None) (Z_to_bv 64 (0x2396c + 2 * Z.of_nat k)) 2%nat = Some bs
             /\ bytes_le_to_Z bs = size_class (Z.of_nat k).
Proof using.
  intros k Hk.
  enum_nat k 48%nat ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.add Pos.add Z.mul Pos.mul];
    lazymatch goal with |- exists bs, ?l = Some bs /\ _ =>
      let v := eval vm_compute in l in
      lazymatch v with Some ?bs => exists bs; split; [vm_compute; reflexivity | vm_compute; reflexivity] end end).
Qed.

Lemma sz_entry : forall mem sc, sz_img mem -> (0 <= sc < 48)%Z ->
  exists bs, rdn RSEGS mem (Z_to_bv 64 (0x2396c + 2 * sc)) 2%nat = Some bs
             /\ bytes_le_to_Z bs = size_class sc.
Proof using.
  intros mem sc Himg Hsc.
  rewrite (rdn_img RSEGS mem _ 2 0x2396c 0x239cc Himg) by (cbn; lia).
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
  gm_sec  : rdn RSEGS mem (Z_to_bv 64 0xaae98) 8%nat = Some (word_to_le_bytes 8 sec);
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
Proof using. intros regs regs' rd v K Hin r Hr. rewrite getr_other; [apply K, Hr|]. intros ->. exact (Hr Hin). Qed.
Lemma gm_keeps_refl : forall regs, gm_keeps regs regs. Proof using. intros regs r _. reflexivity. Qed.
End FPGen2.

Ltac solve_gm_keeps :=
  repeat (apply gm_keeps_upd; [| cbv [gm_clob In]; repeat first [left; reflexivity | right] ]); apply gm_keeps_refl.

(* [comment removed for export] *)
Section FPGen3.
Context {fx : FPState}.

Lemma gm_keeps_reg : forall regs regs' (r : reg),
  gm_keeps regs regs' ->
  (r <> 10)%bv -> (r <> 11)%bv -> (r <> 12)%bv -> (r <> 13)%bv -> (r <> 14)%bv -> (r <> 15)%bv ->
  getr regs' r = getr regs r.
Proof using.
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
  Proof using h3 rc idx. unfold w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_sc : (0 <= w_sizeclass W < 64)%Z.
  Proof using h3 rc idx. unfold w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_ml : (0 <= w_maplen W < 2^52)%Z.
  Proof using h3 P freed avail q rc idx g M p. destruct P. unfold w_maplen. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.
  Lemma r_gm : (0 <= g mod 4096 < 4096)%Z.
  Proof using h3 rc idx. apply Z.mod_pos_bound. lia. Qed.
  Lemma r_h3 : (0 <= h3 < 256)%Z /\ (h3 mod 32 = idx)%Z.
  Proof using P freed avail W q g M p.
    destruct P. pose proof r_last. subst h3. split; [lia|].
    replace (idx + 32 * rc)%Z with (idx + rc * 32)%Z by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma E_al : v_andi (Z_to_bv 64 p) 15 = Z_to_bv 64 0.
  Proof using h3 P freed avail W q rc idx g M.
    destruct P. rewrite v_andi_Z by lia. change 15%Z with (2^4 - 1)%Z. rewrite land_ones_mod by lia.
    change (2^4)%Z with 16%Z. rewrite gp_al0. reflexivity.
  Qed.
  Lemma E_b3 : Z_to_bv 64 (bv_unsigned (Z_to_bv 8 h3)) = Z_to_bv 64 h3.
  Proof using P freed avail W q g M p. pose proof r_h3. rewrite u8_Z2bv by lia. reflexivity. Qed.
  Lemma E_idx : v_andi (Z_to_bv 64 h3) 31 = Z_to_bv 64 idx.
  Proof using P freed avail W q g M p.
    pose proof r_h3. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia.
    change (2^5)%Z with 32%Z. f_equal. lia.
  Qed.
  Lemma E_off4 : v_slli (Z_to_bv 64 q) 4 = Z_to_bv 64 (16 * q).
  Proof using h3 P freed avail W rc idx g M p. destruct P. rewrite v_slli_Z by (cbn; lia). f_equal. cbn. lia. Qed.
  Lemma E_base : v_sub (Z_to_bv 64 p) (Z_to_bv 64 (16 * q)) = Z_to_bv 64 (M + 16).
  Proof using h3 P freed avail W rc idx g. destruct P. rewrite v_sub_ZZ by lia. f_equal. lia. Qed.
  Lemma E_last : v_andi (Z_to_bv 64 W) 31 = Z_to_bv 64 (w_lastidx W).
  Proof using h3 P freed avail q rc idx g M p. destruct P. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_avt : v_and (v_lw (Z_to_bv 64 avail)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
  Proof using h3 P freed W q rc g M p. destruct P. pose proof r_last. apply mask_test_clear; try lia. assumption. Qed.
  Lemma E_frt : v_and (v_lw (Z_to_bv 64 freed)) (v_sllw (Z_to_bv 64 1) (Z_to_bv 64 idx)) = Z_to_bv 64 0.
  Proof using h3 P avail W q rc g M p. destruct P. pose proof r_last. apply mask_test_clear; try lia. assumption. Qed.
  Lemma E_area : v_and (Z_to_bv 64 g) (Z_to_bv 64 18446744073709547520) = Z_to_bv 64 (g - g mod 4096).
  Proof using h3 P freed avail W q rc idx M p. destruct P. rewrite v_and_Z by lia. f_equal. apply land_pagemask. lia. Qed.
  Lemma E_sc : v_srli (v_slli (Z_to_bv 64 W) 52) 58 = Z_to_bv 64 (w_sizeclass W).
  Proof using h3 P freed avail q rc idx g M p.
    destruct P. unfold v_srli, v_slli, w_sizeclass. f_equal. rewrite (u_Z2bv W) by lia.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64)%Z. apply sc_extract. lia.
  Qed.
  Lemma E_ml : v_srli (Z_to_bv 64 W) 12 = Z_to_bv 64 (w_maplen W).
  Proof using h3 P freed avail q rc idx g M p. destruct P. rewrite v_srli_Z by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Local Ltac gm_prefix :=
    pose proof r_last as Hlast; pose proof r_sc as Hscr; pose proof r_ml as Hmlr; pose proof r_gm as Hgm;
    pose proof r_h3 as Hh3;
    destruct R as [Hb4 Hb3 Hoff Hmeta Hmem HW Hav Hfr Harea Hsec Himg];
    pose proof P as P'; destruct P' as [Hal Hidx Hrc Hq Hp HM Hpe Hg Hg2 HWr Havr Havb Hfrr Hfrb _ Hml];
    stepn F_6672c D_6672c; rewrite H10, E_al;
    stepb_tk F_66730 D_66730 ltac:(cond_compute);
    stepLBU F_66738 D_66738 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact Hb4); vals_lit;
    stepLBU F_6673c D_6673c (Z_to_bv 8 h3) ltac:(addr_norm; apply rdn1_of_mem; exact Hb3); rewrite E_b3;
    stepLHU F_66740 D_66740 (word_to_le_bytes 2 (Z_to_bv 64 q)) (Z_to_bv 64 q)
      ltac:(addr_norm; exact Hoff) ltac:(apply bytes_le_to_Z_2; u_norm; lia);
    stepb_tk F_66744 D_66744 ltac:(cond_compute);
    stepn F_66760 D_66760; rewrite E_off4;
    stepn F_66764 D_66764; rewrite H10, E_base;
    stepLD F_66768 D_66768 (word_to_le_bytes 8 (Z_to_bv 64 g)) (Z_to_bv 64 g)
      ltac:(replace (v_addi (Z_to_bv 64 (M + 16)) (-16)) with (Z_to_bv 64 M) by (unfold v_addi; unorm; f_equal; lia); exact Hmeta)
      ltac:(apply bytes_le_to_Z_8);
    stepLD8 F_6676c D_6676c (Z_to_bv 64 M);
    stepn F_66770 D_66770; addi_renorm; replace (M + 0)%Z with M by lia;
    stepn F_66774 D_66774; rewrite E_idx;
    stepb_tk F_66778 D_66778 ltac:(apply c_eq_refl);
    stepLD8 F_66780 D_66780 (Z_to_bv 64 W);
    stepn F_66784 D_66784; rewrite E_last;
    stepb_tk F_66788 D_66788 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepLD F_66790 D_66790 (word_to_le_bytes 4 (Z_to_bv 64 avail)) (Z_to_bv 64 avail)
      ltac:(addr_norm; exact Hav) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    stepn F_66794 D_66794;
    stepn F_66798 D_66798;
    stepn F_6679c D_6679c; rewrite E_avt;
    stepb_tk F_667a0 D_667a0 ltac:(cond_compute);
    stepLD F_667a8 D_667a8 (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed)
      ltac:(addr_norm; exact Hfr) ltac:(apply bytes_le_to_Z_4; u_norm; lia);
    stepn F_667ac D_667ac; rewrite E_frt;
    stepb_tk F_667b0 D_667b0 ltac:(cond_compute);
    stepn F_667b8 D_667b8;
    stepn F_667bc D_667bc;
    stepn F_667c0 D_667c0; rewrite E_area;
    stepLD8 F_667c4 D_667c4 sec;
    stepLD8 F_667c8 D_667c8 sec;
    stepb_tk F_667cc D_667cc ltac:(apply c_eq_refl);
    stepn F_667d4 D_667d4;
    stepn F_667d8 D_667d8; rewrite E_sc;
    stepn F_667dc D_667dc.

  (* [comment removed for export] *)
  Local Ltac gm_tail :=
    stepn F_66820 D_66820; rewrite E_ml;
    lazymatch goal with
    | Hz : (w_maplen W = 0)%Z |- _ =>
        stepb_tk F_66824 D_66824 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia)
    | Hnz : (w_maplen W <> 0)%Z |- _ =>
        stepb_ft F_66824 D_66824 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia);
        stepn F_66828 D_66828; rewrite (v_slli_Z (w_maplen W) 8) by (rewrite ?pow_2_8; lia); rewrite pow_2_8;
        stepn F_6682c D_6682c; addi_renorm;
        stepb_tk F_66830 D_66830 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia)
    end;
    stepret F_66838 D_66838 ret ltac:(getr_hyps; reflexivity).

  Definition gm_goal : Prop :=
    exists regs',
      msteps RSEGS (mkst regs (0x66780 : word) mem rom) (mkst regs' ret mem rom)
      /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 q /\ gm_keeps regs regs'.

  (* [comment removed for export] *)
  Local Ltac gm_sized_walk :=
    gm_prefix;
    stepb_ft F_667e0 D_667e0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_667e4 D_667e4; rewrite (v_slli_Z (w_sizeclass W) 1) by (rewrite ?pow_2_1; lia); rewrite pow_2_1;
    stepn F_667e8 D_667e8;
    stepn F_667ec D_667ec;
    stepn F_667f0 D_667f0; rewrite (v_add_ZZ 145772 (w_sizeclass W * 2)) by lia;
    replace (145772 + w_sizeclass W * 2)%Z with (0x2396c + 2 * w_sizeclass W)%Z by lia;
    lazymatch goal with Hsbs : rdn _ _ (Z_to_bv 64 (0x2396c + 2 * w_sizeclass W)%Z) 2%nat = Some ?sbs,
                        Hsv : bytes_le_to_Z ?sbs = _ |- _ =>
      stepLHU F_667f4 D_667f4 sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia)
    end;
    stepn F_667f8 D_667f8; rewrite (v_mul_Z (size_class (w_sizeclass W)) idx) by lia;
    stepb_tk F_667fc D_667fc ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_66804 D_66804; addi_renorm;
    stepn F_66808 D_66808; rewrite (v_mul_Z (idx + 1) (size_class (w_sizeclass W))) by lia;
    stepb_ft F_6680c D_6680c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia);
    stepn F_66810 D_66810;
    gm_tail;
    pu_refl.

  Local Ltac gm_post := split; [gres; reflexivity | split; [gres; reflexivity | solve_gm_keeps]].

  Lemma gm_sized :
    (w_sizeclass W < 48)%Z -> (size_class (w_sizeclass W) * idx <= q)%Z ->
    (q < size_class (w_sizeclass W) * (idx + 1))%Z -> gm_goal.
  Proof using h3 Hret H1 H10 P R sec freed avail rc M p.
    intros Hsc48 Hlo Hhi. unfold gm_goal.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof r_sc; lia)) as Hszc.
    destruct (sz_entry mem (w_sizeclass W) (gm_img _ _ _ _ _ _ _ _ _ _ _ R) ltac:(pose proof r_sc; lia)) as (sbs & Hsbs & Hsv).
    destruct (Z.eq_dec (w_maplen W) 0) as [Hml0 | Hmln]; (eexists; split; [gm_sized_walk | gm_post]).
  Qed.

  (* [comment removed for export] *)
  Lemma gm_mmapped :
    (w_sizeclass W = 63)%Z -> (w_maplen W <> 0)%Z -> gm_goal.
  Proof using h3 Hret H1 H10 P R sec freed avail rc idx M p.
    intros Hsc63 Hmln. unfold gm_goal.
    eexists. split.
    - gm_prefix.
      stepb_tk F_667e0 D_667e0 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepn F_66814 D_66814.
      stepb_tk F_66818 D_66818 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      gm_tail.
      pu_refl.
    - gm_post.
  Qed.

  Lemma get_meta_run_sec : gm_goal.
  Proof using h3 Hret H1 H10 P R sec freed avail W rc idx M p.
    destruct (gp_sc _ _ _ _ _ _ _ _ _ P) as [(Hsc48 & Hlo & Hhi) | (Hsc63 & Hmln & _)].
    - exact (gm_sized Hsc48 Hlo Hhi).
    - exact (gm_mmapped Hsc63 Hmln).
  Qed.
End Walk.

Theorem get_meta_run : forall regs mem rom (ret : word) (p M g idx rc q W avail freed : Z) (sec : word),
  gm_reads mem p M g idx rc q W avail freed sec -> gm_pure p M g idx rc q W avail freed ->
  getr regs 10 = Z_to_bv 64 p -> getr regs 1 = ret -> ret_ok ret ->
  exists regs',
    msteps RSEGS (mkst regs (0x66780 : word) mem rom) (mkst regs' ret mem rom)
    /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 11 = Z_to_bv 64 q /\ gm_keeps regs regs'.
Proof using.
  intros. eapply get_meta_run_sec; eassumption.
Qed.
End FPGen3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMhGetMeta.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhFreePro.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac lia ::= lia_nd.
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPGen1.
Context {fx : FPState}.

Record free_pre (mem : word -> option byte)
       (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word) : Prop := FPRE {
  (* [comment removed for export] *)
  fp_stride : stride = slot_stride (w_maplen W) (w_lastidx W) (w_sizeclass W);
  fp_p      : p = (M + 16 + stride * idx + 16 * off)%Z;
  fp_e      : e = (M + 16 + stride * idx + stride - 4)%Z;
  fp_res    : reserved = (stride - 4 - n - 16 * off)%Z;
  fp_q      : q = (stride * idx / 16 + off)%Z;
  (* [comment removed for export] *)
  fp_al     : (p mod 16 = 0)%Z;
  fp_M      : (0 <= M)%Z;
  fp_idx    : (0 <= idx <= w_lastidx W)%Z;
  fp_off    : (0 <= off)%Z;
  fp_n      : (0 <= n)%Z;
  fp_resr   : (0 <= reserved < 2^32)%Z;
  fp_q16    : (q < 65536)%Z;
  fp_W      : (0 <= W < 2^64)%Z;
  fp_g      : (0 <= g)%Z;
  fp_sc     : ((w_sizeclass W < 48 /\ size_class (w_sizeclass W) * idx <= q
                /\ q < size_class (w_sizeclass W) * (idx + 1))
               \/ (w_sizeclass W = 63 /\ w_maplen W <> 0 /\ w_lastidx W = 0))%Z;
  fp_ml     : (w_maplen W <> 0 -> q <= w_maplen W * 256 - 1)%Z;
  fp_av     : (0 <= avail < 2^32)%Z;  fp_avb : Z.testbit avail idx = false;
  fp_fr     : (0 <= freed < 2^32)%Z;  fp_frb : Z.testbit freed idx = false;
  (* [comment removed for export] *)
  fp_sp     : (sp < 2^64)%Z;
  fp_hi     : (e + 4 <= sp - 48 /\ g + 40 <= sp - 48 /\ 0xaaea0 <= sp - 48)%Z;
  fp_sok    : store_ok RSEGS mem (Z_to_bv 64 (sp - 48)) 48%nat = true;
  (* [comment removed for export] *)
  fp_m4  : mem (Z_to_bv 64 (p - 4)) = Some (Z_to_bv 8 0);
  fp_m3  : mem (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code reserved));
  fp_m2  : rdn RSEGS mem (Z_to_bv 64 (p - 2)) 2%nat = Some (word_to_le_bytes 2 (Z_to_bv 64 q));
  fp_zr  : (0 < reserved)%Z -> mem (Z_to_bv 64 (p + n)) = Some (Z_to_bv 8 0);
  fp_e5  : (5 <= reserved)%Z -> mem (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0);
  fp_e4  : (5 <= reserved)%Z ->
           rdn RSEGS mem (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved));
  fp_end : mem (Z_to_bv 64 e) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  fp_meta : rdn RSEGS mem (Z_to_bv 64 M) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g));
  fp_mem  : rdn RSEGS mem (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  fp_Wm   : rdn RSEGS mem (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  fp_avm  : rdn RSEGS mem (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail));
  fp_frm  : rdn RSEGS mem (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed));
  fp_area : rdn RSEGS mem (Z_to_bv 64 (g - g mod 4096)) 8%nat = Some (word_to_le_bytes 8 sec);
  fp_secm : rdn RSEGS mem (Z_to_bv 64 0xaae98) 8%nat = Some (word_to_le_bytes 8 sec);
  fp_img  : sz_img mem
}.

(* [comment removed for export] *)
Definition free_mem1 (mem : word -> option byte) (sp : Z) (ra s0 s1 s2 s3 : word)
  : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3).

Lemma free_mem1_below : forall mem sp ra s0 s1 s2 s3 (x : word),
  (48 <= sp < 2^64)%Z -> (bv_unsigned x < sp - 48)%Z ->
  free_mem1 mem sp ra s0 s1 s2 s3 x = mem x.
Proof using.
  intros mem sp ra s0 s1 s2 s3 x Hsp Hx. cbv beta delta [free_mem1].
  rewrite !wbytes_below; wd_lenlit; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; try lia.
  reflexivity.
Qed.

Lemma free_mem1_byte : forall mem sp ra s0 s1 s2 s3 (a : Z),
  (48 <= sp < 2^64)%Z -> (0 <= a < sp - 48)%Z ->
  free_mem1 mem sp ra s0 s1 s2 s3 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof using. intros. apply free_mem1_below; u_norm; lia. Qed.

Lemma free_mem1_rdn : forall mem sp ra s0 s1 s2 s3 (a : Z) (k : nat),
  (48 <= sp < 2^64)%Z -> (0 <= a)%Z -> (a + Z.of_nat k <= sp - 48)%Z ->
  rdn RSEGS (free_mem1 mem sp ra s0 s1 s2 s3) (Z_to_bv 64 a) k = rdn RSEGS mem (Z_to_bv 64 a) k.
Proof using.
  intros mem sp ra s0 s1 s2 s3 a k Hsp Ha Hk.
  apply rdn_ext; [u_norm; lia|]. intros x Hx. revert Hx. u_norm. intros Hx.
  apply free_mem1_below; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
  Variables (mem : word -> option byte) (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word).
  Hypothesis PRE : free_pre mem sp p e M g idx off n stride reserved q W avail freed sec.
  (* [comment removed for export] *)
  Set Default Proof Using "PRE".

  Lemma f_last : (0 <= w_lastidx W < 32)%Z.
  Proof. unfold w_lastidx. apply Z.mod_pos_bound. lia. Qed.
  Lemma f_scr : (0 <= w_sizeclass W < 64)%Z.
  Proof. unfold w_sizeclass. apply Z.mod_pos_bound. lia. Qed.
  Lemma f_mlr : (0 <= w_maplen W < 2^52)%Z.
  Proof. destruct PRE. unfold w_maplen. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. Qed.

  (* [comment removed for export] *)
  Lemma f_stride_cases :
    ((w_maplen W <> 0 /\ w_lastidx W = 0 /\ stride = w_maplen W * 4096 - 16)
     \/ ((w_maplen W = 0 \/ w_lastidx W <> 0) /\ w_sizeclass W < 48 /\ stride = 16 * size_class (w_sizeclass W)))%Z.
  Proof.
    destruct PRE. rewrite fp_stride0. unfold slot_stride, UNIT.
    destruct (Z.eqb_spec (w_maplen W) 0) as [E|E]; destruct (Z.eqb_spec (w_lastidx W) 0) as [F|F]; cbn [negb andb];
      first [ left; repeat split; lia | right; (split; [lia|]); (split; [|reflexivity]); destruct fp_sc0 as [(?&?&?)|(?&?&?)]; lia ].
  Qed.

  Lemma f_stride16 : (16 <= stride)%Z /\ (stride mod 16 = 0)%Z.
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof f_mlr. destruct f_stride_cases as [(A & B & C)|(A & B & C)].
    - rewrite C. split; [lia|]. replace (w_maplen W * 4096 - 16)%Z with ((w_maplen W * 256 - 1) * 16)%Z by lia. apply Z.mod_mul; lia.
    - pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof f_scr; lia)). rewrite C. split; [lia|].
      rewrite Z.mul_comm. apply Z.mod_mul; lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma f_geom :
    (0 <= stride * idx)%Z /\ (16 <= p)%Z /\ (p + n + reserved = e)%Z /\ (e + 4 <= sp - 48)%Z /\ (48 <= sp < 2^64)%Z
    /\ (0 <= reserved)%Z /\ (0 <= n)%Z /\ (0 <= q < 65536)%Z /\ (p = M + 16 + 16 * q)%Z.
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof f_stride16 as [S1 S2]. destruct PRE. destruct fp_hi0 as (H1 & H2 & H3).
    assert (0 <= stride * idx)%Z by nia.
    assert (Hq' : (q * 16 = stride * idx + 16 * off)%Z).
    { rewrite fp_q0. assert ((stride * idx) mod 16 = 0)%Z by (rewrite Z.mul_mod, S2, Z.mul_0_l; [reflexivity|lia]). lia. }
    repeat split; try lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  (* [comment removed for export] *)
  Lemma f_gm_pure : gm_pure p M g idx (res_code reserved) q W avail freed.
  Proof.
    pose proof f_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). destruct PRE.
    constructor; try assumption; try lia.
    unfold res_code. destruct (reserved <? 5)%Z eqn:E; [apply Z.ltb_lt in E|]; lia.
  Qed.

  Lemma f_gm_reads : forall ra s0 s1 s2 s3,
    gm_reads (free_mem1 mem sp ra s0 s1 s2 s3) p M g idx (res_code reserved) q W avail freed sec.
  Proof.
    intros ra s0 s1 s2 s3.
    pose proof f_geom as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    pose proof (Z.mod_pos_bound g 4096 ltac:(lia)) as Gm. destruct PRE. destruct fp_hi0 as (H1 & H2 & H3).
    pose proof (Z.mod_le g 4096 ltac:(lia) ltac:(lia)) as Gm'.
    constructor; rewrite ?free_mem1_byte, ?free_mem1_rdn by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia); try assumption.
    intros i Hi. rewrite free_mem1_byte by lia. apply fp_img0. exact Hi.
  Qed.
  Unset Default Proof Using.
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_eq_Z0_false : forall z, (0 < z < 2^64)%Z -> c_eq (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof using. intros z Hz. rewrite c_eq_Z by lia. apply Z.eqb_neq. lia. Qed.
End FPGen1.


Ltac sok48 SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOK | | ]; zsimp; lia.
Section FPGen2.
Context {fx : FPState}.


Lemma blockA : forall regs mem rom (sp p : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p ->
  (48 <= sp < 2^64)%Z -> (0 < p < 2^64)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (sp - 48)) 48%nat = true ->
  exists regs',
    msteps RSEGS (mkst regs (0x665b4 : word) mem rom)
                 (mkst regs' (0x66780 : word)
                       (free_mem1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 9 = Z_to_bv 64 p /\ getr regs' 1 = (0x665d8 : word)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48)
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
    /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof using.
  intros regs mem rom sp p H2 H10 Hsp Hp SOK.
  eexists. split.
  - stepb_ft F_66560 D_66560 ltac:(rewrite H10; apply c_eq_Z0_false; lia).
    stepn F_66564 D_66564. rewrite H2. addi_renorm.
    stepST F_66568 D_66568 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok48 SOK).
    stepST F_6656c D_6656c (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok48 SOK).
    stepST F_66570 D_66570 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok48 SOK).
    stepST F_66574 D_66574 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok48 SOK).
    stepST F_66578 D_66578 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok48 SOK).
    stepn F_6657c D_6657c. rewrite H10.
    stepn F_66580 D_66580.
    pu_refl.
  - repeat split; gres; first [reflexivity | assumption | apply bv_eq; reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BlockB.
  Variables (mem : word -> option byte) (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word).
  Hypothesis PRE : free_pre mem sp p e M g idx off n stride reserved q W avail freed sec.
  (* [comment removed for export] *)
  Variable m1 : word -> option byte.
  Hypothesis M_W   : rdn RSEGS m1 (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_b3  : m1 (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code reserved)).
  Hypothesis M_img : sz_img m1.
  Hypothesis M_mem : rdn RSEGS m1 (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M)).
  Hypothesis M_e5  : (5 <= reserved)%Z -> m1 (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0).
  Hypothesis M_e4  : (5 <= reserved)%Z ->
                     rdn RSEGS m1 (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved)).
  Hypothesis M_zr  : m1 (Z_to_bv 64 (e - reserved)) = Some (Z_to_bv 8 0).
  Hypothesis M_end : m1 (Z_to_bv 64 e) = Some (Z_to_bv 8 0).
  Set Default Proof Using "PRE M_W M_b3 M_img M_mem M_e5 M_e4 M_zr M_end".

  Let h3 := (idx + 32 * res_code reserved)%Z.

  Lemma b_rc : (0 <= res_code reserved <= 5)%Z /\ (res_code reserved <= reserved)%Z
               /\ (reserved < 5 -> res_code reserved = reserved)%Z /\ (5 <= reserved -> res_code reserved = 5)%Z.
  Proof.
    pose proof (f_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    unfold res_code. destruct (reserved <? 5)%Z eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
  Qed.

  Lemma b_h3 : (0 <= h3 < 256)%Z /\ (h3 / 32 = res_code reserved)%Z /\ (Z.land h3 31 = idx)%Z
               /\ ((reserved < 5)%Z -> (h3 < 160)%Z) /\ ((5 <= reserved)%Z -> (160 <= h3)%Z).
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof b_rc as (R1 & R2 & R3 & R4). pose proof (f_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE).
    destruct PRE. subst h3. split; [lia|]. split; [lia|]. split; [|split; intros; lia].
    change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. change (2^5)%Z with 32%Z. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma E_b3' : Z_to_bv 64 (bv_unsigned (Z_to_bv 8 h3)) = Z_to_bv 64 h3.
  Proof. pose proof b_h3 as (A & _). rewrite u8_Z2bv by lia. reflexivity. Qed.
  Lemma E_idx' : v_andi (Z_to_bv 64 h3) 31 = Z_to_bv 64 idx.
  Proof. pose proof b_h3 as (A & B & C & _). rewrite v_andi_Z by lia. rewrite C. reflexivity. Qed.
  Lemma E_rc : v_srli (Z_to_bv 64 h3) 5 = Z_to_bv 64 (res_code reserved).
  Proof. pose proof b_h3 as (A & B & _). rewrite v_srli_Z by lia. change (2^5)%Z with 32%Z. rewrite B. reflexivity. Qed.
  Lemma E_ml' : v_srli (Z_to_bv 64 W) 12 = Z_to_bv 64 (w_maplen W).
  Proof. destruct PRE. rewrite v_srli_Z by lia. reflexivity. Qed.
  Lemma E_last' : v_andi (Z_to_bv 64 W) 31 = Z_to_bv 64 (w_lastidx W).
  Proof. destruct PRE. rewrite v_andi_Z by lia. change 31%Z with (2^5 - 1)%Z. rewrite land_ones_mod by lia. reflexivity. Qed.
  Lemma E_pm : v_and (Z_to_bv 64 W) (Z_to_bv 64 18446744073709547520) = Z_to_bv 64 (w_maplen W * 4096).
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct PRE. rewrite v_and_Z by lia. f_equal. rewrite land_pagemask by lia. unfold w_maplen. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Lemma E_sc2 : v_andi (v_srli (Z_to_bv 64 W) 5) 126 = Z_to_bv 64 (2 * w_sizeclass W).
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    destruct PRE. unfold v_andi, v_srli. f_equal. rewrite (u_Z2bv W) by lia.
    change (bv_wrap 64 126) with 126%Z.
    assert (HR : (0 <= Z.shiftr W 5 < 2^64)%Z) by (rewrite Z.shiftr_div_pow2 by lia; lia).
    rewrite u_Z2bv by lia. unfold w_sizeclass. apply sc2_extract. lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Definition b1_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 12 = Z_to_bv 64 stride /\ getr regs' 11 = Z_to_bv 64 W /\ getr regs' 13 = Z_to_bv 64 h3
    /\ getr regs' 8 = Z_to_bv 64 idx
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 9 = getr regs 9 /\ getr regs' 2 = getr regs 2
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
    /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

  (* [comment removed for export] *)
  Local Ltac b1_head H10 H9 :=
    pose proof (f_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9);
    pose proof (f_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hlast;
    pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hscr;
    pose proof (f_mlr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as Hmlr;
    pose proof b_h3 as (Bh & _);
    pose proof PRE as P'; destruct P' as [Hstr _ _ _ _ _ HM Hidx Hoff Hn Hres Hq16 HWr Hg _ Hml _ _ _ _ Hsp64 (Hh1 & Hh2 & Hh3)
                                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _];
    stepLD8 F_66584 D_66584 (Z_to_bv 64 W);
    stepLBU F_66588 D_66588 (Z_to_bv 8 h3) ltac:(addr_norm; apply rdn1_of_mem; exact M_b3); rewrite E_b3';
    stepn F_6658c D_6658c; rewrite E_ml';
    stepn F_66590 D_66590; rewrite E_idx'.

  Local Ltac b1_post_tac := unfold b1_post; repeat split; gres; first [reflexivity | assumption].

  (* [comment removed for export] *)
  Lemma blockB1_map : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W <> 0)%Z -> (w_lastidx W = 0)%Z -> (stride = w_maplen W * 4096 - 16)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x665d8 : word) m1 rom) (mkst regs' (0x66620 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hl0 HS.
    eexists. split.
    - b1_head H10 H9.
      stepb_ft F_66594 D_66594 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_66598 D_66598. rewrite E_last'.
      stepb_ft F_6659c D_6659c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      stepn F_665a0 D_665a0.
      stepn F_665a4 D_665a4. rewrite E_pm.
      stepn F_665a8 D_665a8. addi_renorm. rewrite <- HS.
      stepn F_665ac D_665ac.
      pu_refl.
    - b1_post_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma blockB1_tab0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W = 0)%Z -> (w_sizeclass W < 48)%Z -> (stride = 16 * size_class (w_sizeclass W))%Z ->
    exists regs', msteps RSEGS (mkst regs (0x665d8 : word) m1 rom) (mkst regs' (0x66620 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hsc HS.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as Hszc.
    destruct (sz_entry m1 (w_sizeclass W) M_img ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as (sbs & Hsbs & Hsv).
    eexists. split.
    - b1_head H10 H9.
      stepb_tk F_66594 D_66594 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      stepn F_665b0 D_665b0.
      stepn F_665b4 D_665b4.
      stepn F_665b8 D_665b8. rewrite E_sc2.
      stepn F_665bc D_665bc.
      stepn F_665c0 D_665c0. rewrite (v_add_ZZ 145772 (2 * w_sizeclass W)) by lia.
      stepLHU F_665c4 D_665c4 sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia).
      stepn F_665c8 D_665c8. rewrite (v_slli_Z (size_class (w_sizeclass W)) 4) by (change (2^4)%Z with 16%Z; lia).
      change (2^4)%Z with 16%Z. replace (size_class (w_sizeclass W) * 16)%Z with stride by lia.
      pu_refl.
    - b1_post_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma blockB1_tab1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W <> 0)%Z -> (w_lastidx W <> 0)%Z -> (w_sizeclass W < 48)%Z ->
    (stride = 16 * size_class (w_sizeclass W))%Z ->
    exists regs', msteps RSEGS (mkst regs (0x665d8 : word) m1 rom) (mkst regs' (0x66620 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hl Hsc HS.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as Hszc.
    destruct (sz_entry m1 (w_sizeclass W) M_img ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as (sbs & Hsbs & Hsv).
    eexists. split.
    - b1_head H10 H9.
      stepb_ft F_66594 D_66594 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_66598 D_66598. rewrite E_last'.
      stepb_tk F_6659c D_6659c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_665b0 D_665b0.
      stepn F_665b4 D_665b4.
      stepn F_665b8 D_665b8. rewrite E_sc2.
      stepn F_665bc D_665bc.
      stepn F_665c0 D_665c0. rewrite (v_add_ZZ 145772 (2 * w_sizeclass W)) by lia.
      stepLHU F_665c4 D_665c4 sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia).
      stepn F_665c8 D_665c8. rewrite (v_slli_Z (size_class (w_sizeclass W)) 4) by (change (2^4)%Z with 16%Z; lia).
      change (2^4)%Z with 16%Z. replace (size_class (w_sizeclass W) * 16)%Z with stride by lia.
      pu_refl.
    - b1_post_tac.
  Qed.

  Lemma blockB1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    exists regs', msteps RSEGS (mkst regs (0x665d8 : word) m1 rom) (mkst regs' (0x66620 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9.
    destruct (f_stride_cases _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as [(A & B & C)|(A & B & C)].
    - exact (blockB1_map regs rom H10 H9 A B C).
    - destruct (Z.eq_dec (w_maplen W) 0) as [Z0|Z1].
      + exact (blockB1_tab0 regs rom H10 H9 Z0 B C).
      + apply (blockB1_tab1 regs rom H10 H9 Z1); [lia | exact B | exact C].
  Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

  Definition b2_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 14 = Z_to_bv 64 reserved /\ getr regs' 15 = Z_to_bv 64 (e - 12)
    /\ getr regs' 11 = getr regs 11 /\ getr regs' 8 = getr regs 8
    /\ getr regs' 10 = getr regs 10 /\ getr regs' 9 = getr regs 9 /\ getr regs' 2 = getr regs 2
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
    /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.

  Local Ltac b2_head H10 H9 H12 H13 H8 :=
    pose proof (f_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9);
    pose proof b_h3 as (Bh & _ & _ & Bh_lt & Bh_ge); pose proof b_rc as (R1 & R2 & R3 & R4);
    pose proof PRE as P'; destruct P' as [Hstr Hp He _ _ _ HM Hidx Hoff Hn Hres Hq16 HWr Hg _ Hml _ _ _ _ Hsp64 (Hh1 & Hh2 & Hh3)
                                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _];
    stepLD8 F_665cc D_665cc (Z_to_bv 64 M);
    stepn F_665d0 D_665d0; rewrite H12, H8, (v_mul_Z stride idx) by lia;
    stepn F_665d4 D_665d4;
    stepn F_665d8 D_665d8; rewrite H12, (v_add_ZZ M stride) by lia;
    stepn F_665dc D_665dc; rewrite (v_add_ZZ (M + stride) (stride * idx)) by lia;
    replace (M + stride + stride * idx)%Z with (e - 12)%Z by lia;
    stepn F_665e0 D_665e0; addi_renorm; replace (e - 0)%Z with e by lia;
    stepn F_665e4 D_665e4; rewrite H13, E_rc.

  Local Ltac b2_tail H9 :=
    stepn F_66614 D_66614; rewrite H9, (v_sub_ZZ e p) by lia;
    stepb_tk F_66618 D_66618 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_66620 D_66620; rewrite (v_sub_ZZ e reserved) by lia;
    stepLBU F_66624 D_66624 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact M_zr); vals_lit;
    stepb_tk F_66628 D_66628 ltac:(cond_compute);
    stepLBU F_66630 D_66630 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact M_end); vals_lit;
    stepb_tk F_66634 D_66634 ltac:(cond_compute);
    pu_refl.

  Local Ltac b2_post_tac := unfold b2_post; repeat split; gres; first [reflexivity | assumption].

  Lemma blockB2_small : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    (reserved < 5)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66620 : word) m1 rom) (mkst regs' (0x66690 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8 Hsmall.
    eexists. split.
    - b2_head H10 H9 H12 H13 H8.
      stepb_tk F_665e8 D_665e8 ltac:(rewrite H13; rewrite c_ltu_Z by lia; pose proof (Bh_lt Hsmall); apply Z.ltb_lt; lia).
      rewrite (R3 Hsmall).
      b2_tail H9.
    - b2_post_tac.
  Qed.

  Lemma blockB2_big : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    (5 <= reserved)%Z ->
    exists regs', msteps RSEGS (mkst regs (0x66620 : word) m1 rom) (mkst regs' (0x66690 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8 Hbig.
    pose proof (M_e5 Hbig) as Me5. pose proof (M_e4 Hbig) as Me4.
    eexists. split.
    - b2_head H10 H9 H12 H13 H8.
      stepb_ft F_665e8 D_665e8 ltac:(rewrite H13; rewrite c_ltu_Z by lia; pose proof (Bh_ge Hbig); apply Z.ltb_ge; lia).
      rewrite (R4 Hbig).
      stepn F_665ec D_665ec.
      stepb_tk F_665f0 D_665f0 ltac:(cond_compute).
      stepLD F_665f8 D_665f8 (word_to_le_bytes 4 (Z_to_bv 64 reserved)) (Z_to_bv 64 reserved)
        ltac:(addr_norm; exact Me4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_665fc D_665fc.
      stepb_tk F_66600 D_66600 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepLBU F_66608 D_66608 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact Me5). vals_lit.
      stepb_tk F_6660c D_6660c ltac:(cond_compute).
      b2_tail H9.
    - b2_post_tac.
  Qed.

  Lemma blockB2 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    exists regs', msteps RSEGS (mkst regs (0x66620 : word) m1 rom) (mkst regs' (0x66690 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8.
    destruct (Z.lt_ge_cases reserved 5) as [Hs|Hb].
    - exact (blockB2_small regs rom H10 H9 H12 H13 H8 Hs).
    - apply (blockB2_big regs rom H10 H9 H12 H13 H8). lia.
  Qed.
  Unset Default Proof Using.
End BlockB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_free_pro : forall regs mem rom (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word),
  free_pre mem sp p e M g idx off n stride reserved q W avail freed sec ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p ->
  exists regs',
    msteps RSEGS (mkst regs (0x665b4 : word) mem rom)
                 (mkst regs' (0x66690 : word)
                       (free_mem1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48)
    /\ getr regs' 9 = Z_to_bv 64 p            (* [comment removed for export] *)
    /\ getr regs' 8 = Z_to_bv 64 idx          (* [comment removed for export] *)
    /\ getr regs' 10 = Z_to_bv 64 g           (* [comment removed for export] *)
    /\ getr regs' 11 = Z_to_bv 64 W           (* [comment removed for export] *)
    /\ getr regs' 14 = Z_to_bv 64 reserved    (* [comment removed for export] *)
    /\ getr regs' 15 = Z_to_bv 64 (e - 12)    (* [comment removed for export] *)
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
    /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27             (* [comment removed for export] *).
Proof using.
  intros regs mem rom sp p e M g idx off n stride reserved q W avail freed sec PRE H2 H10.
  pose proof (f_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  set (m1 := free_mem1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  (* [comment removed for export] *)
  destruct (blockA regs mem rom sp p H2 H10 ltac:(lia) ltac:(lia) (fp_sok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE))
    as (r1 & RUN1 & A10 & A9 & A1 & A2 & A8 & A18 & A19 & A3 & A4 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  (* [comment removed for export] *)
  pose proof (f_gm_reads _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) as GR.
  pose proof (f_gm_pure _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as GP.
  destruct (get_meta_run r1 m1 rom (0x665d8 : word) p M g idx (res_code reserved) q W avail freed sec GR GP A10 A1
              ltac:(apply ret_ok_even; reflexivity)) as (r2 & RUN2 & B10 & B11 & K2).
  (* [comment removed for export] *)
  pose proof GR as GR'. destruct GR' as [_ Mb3 _ _ Mmem MW _ _ _ _ Mimg].
  pose proof PRE as P'. destruct P' as [_ _ _ _ _ _ _ _ _ _ Hres _ _ _ _ _ _ _ _ _ _ (Hh1 & Hh2 & Hh3) _ _ _ _ Fzr Fe5 Fe4 Fend _ _ _ _ _ _ _ _].
  assert (Me5 : (5 <= reserved)%Z -> m1 (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0)).
  { intros H5. subst m1. rewrite free_mem1_byte by lia. exact (Fe5 H5). }
  assert (Me4 : (5 <= reserved)%Z -> rdn RSEGS m1 (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved))).
  { intros H5. subst m1. rewrite free_mem1_rdn by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia). exact (Fe4 H5). }
  assert (Mend : m1 (Z_to_bv 64 e) = Some (Z_to_bv 8 0)).
  { subst m1. rewrite free_mem1_byte by lia. exact Fend. }
  assert (Mzr : m1 (Z_to_bv 64 (e - reserved)) = Some (Z_to_bv 8 0)).
  { destruct (Z.eq_dec reserved 0) as [R0|R0].
    - rewrite R0. replace (e - 0)%Z with e by lia. exact Mend.
    - replace (e - reserved)%Z with (p + n)%Z by lia. subst m1. rewrite free_mem1_byte by lia. apply Fzr. lia. }
  assert (C9 : getr r2 9 = Z_to_bv 64 p) by (rewrite (gm_keeps_reg _ _ 9 K2) by (intros E; discriminate E); exact A9).
  destruct (blockB1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE m1 MW Mb3 Mimg Mmem Me5 Me4 Mzr Mend r2 rom B10 C9)
    as (r3 & RUN3 & C12 & C11 & C13 & C8 & D10 & D9 & D2 & D18 & D19 & D3 & D4 & D20 & D21 & D22 & D23 & D24 & D25 & D26 & D27).
  rewrite B10 in D10. rewrite C9 in D9.
  destruct (blockB2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE m1 MW Mb3 Mimg Mmem Me5 Me4 Mzr Mend r3 rom D10 D9 C12 C13 C8)
    as (r4 & RUN4 & E14 & E15 & E11 & E8 & E10 & E9 & E2 & E18 & E19 & E3 & E4 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27).
  exists r4. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|].
    eapply msteps_trans; [exact RUN3|]. exact RUN4. }
  rewrite E11, E8, E10, E9, E2, E18, E19, E3, E4, E20, E21, E22, E23, E24, E25, E26, E27,
          C11, C8, D2, D18, D19, D3, D4, D20, D21, D22, D23, D24, D25, D26, D27.
  rewrite (gm_keeps_reg _ _ 2 K2), (gm_keeps_reg _ _ 18 K2), (gm_keeps_reg _ _ 19 K2),
          (gm_keeps_reg _ _ 3 K2), (gm_keeps_reg _ _ 4 K2),
          (gm_keeps_reg _ _ 20 K2), (gm_keeps_reg _ _ 21 K2), (gm_keeps_reg _ _ 22 K2), (gm_keeps_reg _ _ 23 K2),
          (gm_keeps_reg _ _ 24 K2), (gm_keeps_reg _ _ 25 K2), (gm_keeps_reg _ _ 26 K2), (gm_keeps_reg _ _ 27 K2)
    by (intros E; discriminate E).
  repeat split; assumption.
Qed.
End FPGen2.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbMhFreePro.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac UbMhFreePro OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition clobCT : list reg := [11; 12; 13; 14; 15; 16; 17; 5]%bv.

Section SegC.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m1 : mem) (sp0 p g idx W avail freed : Z).
  (* [comment removed for export] *)
  Hypothesis Hp : (HEAPLO + 4 <= p)%Z /\ (p + 16 <= CEIL)%Z /\ ((p + 16 <= IMG_LO)%Z \/ (IMG_HI <= p)%Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hpg : (p <= g \/ g + 40 <= p - 4)%Z.
  Hypothesis Hidx : (0 <= idx <= w_lastidx W)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Hav : (0 <= avail < 2^32)%Z.
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Havb : Z.testbit avail idx = false.
  Hypothesis Hfrb : Z.testbit freed idx = false.
  (* [comment removed for export] *)
  Hypothesis SOKp : store_ok RSEGS m1 (Z_to_bv 64 (p - 4)) 4%nat = true.
  Hypothesis M_av : rdn RSEGS m1 (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail)).
  Hypothesis M_fr : rdn RSEGS m1 (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed)).
  Hypothesis M_nl : rdn RSEGS m1 (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0].

  (* [comment removed for export] *)
  Definition m2 : mem :=
    wbytes (wbytes m1 (Z_to_bv 64 (p - 3)) (word_to_le_bytes 1 (Z_to_bv 64 18446744073709551615)))
           (Z_to_bv 64 (p - 2)) (word_to_le_bytes 2 (Z_to_bv 64 0)).

  Let mask := Z.lor avail freed.
  Let all := (2 * 2 ^ w_lastidx W - 1)%Z.

  Lemma r_last : (0 <= w_lastidx W < 32)%Z.
  Proof using all mask freed avail. unfold w_lastidx. apply Z.mod_pos_bound. lia. Qed.

  Lemma mask_range : (0 <= mask < 2^32)%Z.
  Proof using all Hfr Hav W. subst mask. apply Z_lor_range32; lia. Qed.

  Lemma mask_bit : Z.testbit mask idx = false.
  Proof using Hfrb Havb. subst mask. rewrite Z.lor_spec, Havb, Hfrb. reflexivity. Qed.

  Definition segC_post (regs regs' : bvmap 5 word) : Prop :=
    getr regs' 12 = s32 (2 ^ idx) /\ getr regs' 13 = s32 all /\ getr regs' 11 = Z_to_bv 64 (g + 28)
    /\ getr regs' 15 = s32 freed /\ getr regs' 16 = s32 mask /\ getr regs' 17 = Z_to_bv 64 0
    /\ getr regs' 10 = Z_to_bv 64 g /\ getr regs' 8 = Z_to_bv 64 idx /\ getr regs' 9 = Z_to_bv 64 p
    /\ keeps_but clobCT regs regs'.

  Lemma segC : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 W ->
    getr regs 8 = Z_to_bv 64 idx -> getr regs 9 = Z_to_bv 64 p ->
    exists regs',
      msteps RSEGS (mkst regs (0x66690 : word) m1 rom) (mkst regs' (0x666d4 : word) m2 rom)
      /\ segC_post regs regs'.
  Proof using M_nl M_fr M_av SOKp Hfrb Havb Hfr Hav HW Hidx Hpg Hg Hp RN.
    intros regs rom H10 H11 H8 H9.
    pose proof r_last as HL. pose proof mask_range as HM. ceil; unfold HEAPLO in *.
    eexists. split.
    - stepn F_6663c D_6663c.
      stepn F_66640 D_66640.
      stepn F_66644 D_66644.
      stepn F_66648 D_66648. rewrite H11. rewrite v_sllw_Z_s32 by lia.
      replace (W mod 32)%Z with (w_lastidx W) by reflexivity.
      stepn F_6664c D_6664c. rewrite H10. addi_renorm.
      stepn F_66650 D_66650. rewrite H8. rewrite v_sllw_Z_s32 by lia. rewrite (Z.mod_small idx 32) by lia.
      rewrite Z.mul_1_l.
      stepSTx F_66654 D_66654 (Z_to_bv 64 (p - 3)) (Z_to_bv 64 18446744073709551615)
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 4%nat); [ | exact SOKp | | ]; zsimp; lia).
      stepSTx F_66658 D_66658 (Z_to_bv 64 (p - 2)) (Z_to_bv 64 0)
        ltac:(store_ok_peel; eapply (store_ok_sub _ _ _ _ 4%nat); [ | exact SOKp | | ]; zsimp; lia).
      stepn F_6665c D_6665c. rewrite v_addiw_s32.
      stepn F_66660 D_66660.
      stepLD F_66664 D_66664 (word_to_le_bytes 4 (Z_to_bv 64 freed)) (Z_to_bv 64 freed)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepLD F_66668 D_66668 (word_to_le_bytes 4 (Z_to_bv 64 avail)) (Z_to_bv 64 avail)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      rewrite v_lw_s32 by lia.
      stepn F_6666c D_6666c. rewrite v_or_s32.
      stepn F_66670 D_66670. rewrite v_and_s32. fold mask.
      rewrite (s32_land_pow2_clear mask idx) by (try lia; apply mask_bit).
      stepb_tk F_66674 D_66674 ltac:(cond_compute).
      stepLBU F_6667c D_6667c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
      vals_lit.
      pu_refl.
    - unfold segC_post. repeat split; gres; try reflexivity; try assumption.
      solve_keeps_but.
  Qed.
End SegC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section SegT.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m1 : mem) (sp0 p g idx W avail freed : Z) (ra s0v s1v s2v s3v : word).
  Hypothesis Hp : (HEAPLO + 4 <= p)%Z /\ (p + 16 <= CEIL)%Z /\ ((p + 16 <= IMG_LO)%Z \/ (IMG_HI <= p)%Z).
  Hypothesis Hg : (HEAPLO <= g)%Z /\ (g + 40 <= CEIL)%Z /\ ((g + 40 <= IMG_LO)%Z \/ (IMG_HI <= g)%Z).
  Hypothesis Hpg : (p <= g \/ g + 40 <= p - 4)%Z.
  Hypothesis Hsp : (CEIL + 48 <= sp0)%Z /\ (sp0 < 2^64)%Z.
  Hypothesis Hidx : (0 <= idx <= w_lastidx W)%Z.
  Hypothesis HW : (0 <= W < 2^64)%Z.
  Hypothesis Hav : (0 <= avail < 2^32)%Z.
  Hypothesis Hfr : (0 <= freed < 2^32)%Z.
  Hypothesis Havb : Z.testbit avail idx = false.
  Hypothesis Hfrb : Z.testbit freed idx = false.
  Hypothesis Hra : ret_ok ra.
  Hypothesis SOKp : store_ok RSEGS m1 (Z_to_bv 64 (p - 4)) 4%nat = true.
  Hypothesis SOKg : store_ok RSEGS m1 (Z_to_bv 64 g) 40%nat = true.
  Hypothesis M_av : rdn RSEGS m1 (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail)).
  Hypothesis M_fr : rdn RSEGS m1 (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed)).
  Hypothesis M_nl : rdn RSEGS m1 (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0].
  Hypothesis M_ra : rdn RSEGS m1 (Z_to_bv 64 (sp0 - 8)) 8%nat = Some (word_to_le_bytes 8 ra).
  Hypothesis M_s0 : rdn RSEGS m1 (Z_to_bv 64 (sp0 - 16)) 8%nat = Some (word_to_le_bytes 8 s0v).
  Hypothesis M_s1 : rdn RSEGS m1 (Z_to_bv 64 (sp0 - 24)) 8%nat = Some (word_to_le_bytes 8 s1v).
  Hypothesis M_s2 : rdn RSEGS m1 (Z_to_bv 64 (sp0 - 32)) 8%nat = Some (word_to_le_bytes 8 s2v).
  Hypothesis M_s3 : rdn RSEGS m1 (Z_to_bv 64 (sp0 - 40)) 8%nat = Some (word_to_le_bytes 8 s3v).

  Let mask := Z.lor avail freed.
  Let all := (2 * 2 ^ w_lastidx W - 1)%Z.
  (* [comment removed for export] *)
  Hypothesis Hfr0 : freed <> 0%Z.
  Hypothesis Hnall : (mask + 2 ^ idx <> all)%Z.

  (* [comment removed for export] *)
  Definition m3 : mem :=
    wbytes (m2 m1 p) (Z_to_bv 64 (g + 28)) (word_to_le_bytes 4 (s32 (freed + 2 ^ idx))).

  Lemma w4_freed_self : word_to_le_bytes 4 (s32 (freed + 2 ^ idx)) = word_to_le_bytes 4 (Z_to_bv 64 (freed + 2 ^ idx)).
  Proof using Hfr0 all mask Hfrb Hfr Hidx avail W.
    assert (HL : (0 <= w_lastidx W < 32)%Z) by (unfold w_lastidx; apply Z.mod_pos_bound; lia).
    pose proof (add_pow2_nocarry32 freed idx ltac:(lia) ltac:(lia) Hfrb).
    assert (0 < 2 ^ idx)%Z by (apply Z.pow_pos_nonneg; lia).
    rewrite w2le4_s32. rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Definition clobT : list reg := (10%bv : reg) :: clobCT.

  Lemma segT : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 11 = Z_to_bv 64 W ->
    getr regs 8 = Z_to_bv 64 idx -> getr regs 9 = Z_to_bv 64 p -> getr regs 2 = Z_to_bv 64 (sp0 - 48) ->
    exists regs',
      msteps RSEGS (mkst regs (0x66690 : word) m1 rom) (mkst regs' ra m3 rom)
      /\ getr regs' 2 = Z_to_bv 64 sp0 /\ getr regs' 1 = ra
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v
      /\ keeps_but ([1; 2; 8; 9; 18; 19]%bv ++ clobT) regs regs'.
  Proof using Hnall Hfr0 all mask M_s3 M_s2 M_s1 M_s0 M_ra M_nl M_fr M_av SOKg SOKp Hra Hfrb Havb Hfr Hav HW Hidx Hsp Hpg Hg Hp avail RN.
    intros regs rom H10 H11 H8 H9 H2.
    assert (HL : (0 <= w_lastidx W < 32)%Z) by (unfold w_lastidx; apply Z.mod_pos_bound; lia).
    pose proof (add_pow2_nocarry32 freed idx ltac:(lia) ltac:(lia) Hfrb) as Hnc.
    assert (Hpi : (0 < 2 ^ idx <= 2 ^ 31)%Z) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    assert (HM : (0 <= mask < 2^32)%Z) by (subst mask; apply Z_lor_range32; lia).
    assert (HMb : Z.testbit mask idx = false) by (subst mask; rewrite Z.lor_spec, Havb, Hfrb; reflexivity).
    pose proof (add_pow2_nocarry32 mask idx HM ltac:(lia) HMb) as Hmc.
    assert (Hall : (0 <= all < 2^32)%Z).
    { subst all. assert (2 ^ w_lastidx W <= 2^31)%Z by (apply Z.pow_le_mono_r; lia).
      assert (0 < 2 ^ w_lastidx W)%Z by (apply Z.pow_pos_nonneg; lia). change (2^32)%Z with (2 * 2^31)%Z. lia. }
    destruct (segC m1 p g idx W avail freed Hp Hg Hpg Hidx HW Hav Hfr Havb Hfrb SOKp M_av M_fr M_nl regs rom H10 H11 H8 H9)
      as (r1 & RUN1 & C12 & C13 & C11 & C15 & C16 & C17 & C10 & C8 & C9 & K1).
    ceil; unfold HEAPLO in *.
    eexists. split.
    - eapply msteps_trans; [exact RUN1|].
      stepb_ft F_66680 D_66680 ltac:(rewrite C15, c_eq_s32_0, Z.mod_small by lia; apply Z.eqb_neq; lia).
      stepn F_66684 D_66684. rewrite C16, C12, v_addw_s32.
      stepb_ft F_66688 D_66688 ltac:(rewrite C13, c_eq_s32; fold mask all; rewrite !Z.mod_small by lia; apply Z.eqb_neq; exact Hnall).
      stepn F_6668c D_6668c. rewrite C15, C12, v_addw_s32.
      stepb_tk F_66690 D_66690 ltac:(rewrite C17; cond_compute).
      stepSTx F_6670c D_6670c (Z_to_bv 64 (g + 28)) (s32 (freed + 2 ^ idx))
        ltac:(unfold m2; store_ok_peel; eapply (store_ok_sub _ _ _ _ 40%nat); [ | exact SOKg | | ]; zsimp; lia).
      assert (C2 : getr r1 2 = Z_to_bv 64 (sp0 - 48)) by (kept_rw K1; exact H2).
      unfold m2.
      stepLD8 F_66710 D_66710 ra.
      stepLD8 F_66714 D_66714 s0v.
      stepLD8 F_66718 D_66718 s1v.
      stepLD8 F_6671c D_6671c s2v.
      stepLD8 F_66720 D_66720 s3v.
      stepn F_66724 D_66724. rewrite C2. addi_renorm.
      stepret F_66728 D_66728 ra ltac:(reflexivity).
      unfold m3, m2. pu_refl.
    - repeat split; gres; try reflexivity; try assumption.
      + f_equal. lia.
      + eapply keeps_but_trans; [eapply keeps_but_mono; [exact K1|]; intros r Hr; apply in_or_app; right; right; exact Hr|].
        solve_keeps_but.
  Qed.
End SegT.
