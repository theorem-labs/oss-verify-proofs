(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim Frame. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import SumWalkTac. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RefMemcpyLib. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import MallocDefs LibMaskBits GetMeta_utf8_ubsan Code_getmeta_utf8_ubsan Code_freepro_utf8_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Abbreviation MSEGS_utf8_ubsan := Ubsan.M.loaded_segments.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section WithFP1.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
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
  fp_hi     : (e + 4 <= sp - 48 /\ g + 40 <= sp - 48 /\ 0x10de90 <= sp - 48)%Z;
  fp_sok    : store_ok MSEGS_utf8_ubsan mem (Z_to_bv 64 (sp - 48)) 48%nat = true;
  (* [comment removed for export] *)
  fp_m4  : mem (Z_to_bv 64 (p - 4)) = Some (Z_to_bv 8 0);
  fp_m3  : mem (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code reserved));
  fp_m2  : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (p - 2)) 2%nat = Some (word_to_le_bytes 2 (Z_to_bv 64 q));
  fp_zr  : (0 < reserved)%Z -> mem (Z_to_bv 64 (p + n)) = Some (Z_to_bv 8 0);
  fp_e5  : (5 <= reserved)%Z -> mem (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0);
  fp_e4  : (5 <= reserved)%Z ->
           rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved));
  fp_end : mem (Z_to_bv 64 e) = Some (Z_to_bv 8 0);
  (* [comment removed for export] *)
  fp_meta : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 M) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 g));
  fp_mem  : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M));
  fp_Wm   : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W));
  fp_avm  : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (g + 24)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 avail));
  fp_frm  : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (g + 28)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 freed));
  fp_area : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 (g - g mod 4096)) 8%nat = Some (word_to_le_bytes 8 sec);
  fp_secm : rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 0x10de88) 8%nat = Some (word_to_le_bytes 8 sec);
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
Proof.
  intros mem sp ra s0 s1 s2 s3 x Hsp Hx. cbv beta delta [free_mem1].
  rewrite !wbytes_below; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; try lia.
  reflexivity.
Qed.

Lemma free_mem1_byte : forall mem sp ra s0 s1 s2 s3 (a : Z),
  (48 <= sp < 2^64)%Z -> (0 <= a < sp - 48)%Z ->
  free_mem1 mem sp ra s0 s1 s2 s3 (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof. intros. apply free_mem1_below; u_norm; lia. Qed.

Lemma free_mem1_rdn : forall mem sp ra s0 s1 s2 s3 (a : Z) (k : nat),
  (48 <= sp < 2^64)%Z -> (0 <= a)%Z -> (a + Z.of_nat k <= sp - 48)%Z ->
  rdn MSEGS_utf8_ubsan (free_mem1 mem sp ra s0 s1 s2 s3) (Z_to_bv 64 a) k = rdn MSEGS_utf8_ubsan mem (Z_to_bv 64 a) k.
Proof.
  intros mem sp ra s0 s1 s2 s3 a k Hsp Ha Hk.
  apply rdn_ext; [u_norm; lia|]. intros x Hx. revert Hx. u_norm. intros Hx.
  apply free_mem1_below; lia.
Qed.
End WithFP1.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Facts.
Context {fx : FPState}.
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
Section WithFP2.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma c_eq_Z0_false : forall z, (0 < z < 2^64)%Z -> c_eq (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof. intros z Hz. rewrite c_eq_Z by lia. apply Z.eqb_neq. lia. Qed.
End WithFP2.


Ltac sok48 SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 48%nat); [ | exact SOK | | ]; zsimp; lia.
Section WithFP3.
Context {fx : FPState}.


Lemma blockA : forall regs mem rom (sp p : Z),
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p ->
  (48 <= sp < 2^64)%Z -> (0 < p < 2^64)%Z ->
  store_ok MSEGS_utf8_ubsan mem (Z_to_bv 64 (sp - 48)) 48%nat = true ->
  exists regs',
    msteps MSEGS_utf8_ubsan (mkst regs (0xbf854 : word) mem rom)
                 (mkst regs' (0xbfa20 : word)
                       (free_mem1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 10 = Z_to_bv 64 p /\ getr regs' 9 = Z_to_bv 64 p /\ getr regs' 1 = (0xbf878 : word)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48)
    /\ getr regs' 8 = getr regs 8 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
    /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs mem rom sp p H2 H10 Hsp Hp SOK.
  eexists. split.
  - stepb_ft F_bf69c D_bf69c ltac:(rewrite H10; apply c_eq_Z0_false; lia).
    stepn F_bf6a0 D_bf6a0. rewrite H2. addi_renorm.
    stepST F_bf6a4 D_bf6a4 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok48 SOK).
    stepST F_bf6a8 D_bf6a8 (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok48 SOK).
    stepST F_bf6ac D_bf6ac (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok48 SOK).
    stepST F_bf6b0 D_bf6b0 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok48 SOK).
    stepST F_bf6b4 D_bf6b4 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok48 SOK).
    stepn F_bf6b8 D_bf6b8. rewrite H10.
    stepn F_bf6bc D_bf6bc.
    apply mst_refl.
  - repeat split; gres; first [reflexivity | assumption | apply bv_eq; reflexivity].
Qed.
End WithFP3.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BlockB.
Context {fx : FPState}.
  Variables (mem : word -> option byte) (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word).
  Hypothesis PRE : free_pre mem sp p e M g idx off n stride reserved q W avail freed sec.
  (* [comment removed for export] *)
  Variable m1 : word -> option byte.
  Hypothesis M_W   : rdn MSEGS_utf8_ubsan m1 (Z_to_bv 64 (g + 32)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 W)).
  Hypothesis M_b3  : m1 (Z_to_bv 64 (p - 3)) = Some (Z_to_bv 8 (idx + 32 * res_code reserved)).
  Hypothesis M_img : sz_img m1.
  Hypothesis M_mem : rdn MSEGS_utf8_ubsan m1 (Z_to_bv 64 (g + 16)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 M)).
  Hypothesis M_e5  : (5 <= reserved)%Z -> m1 (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0).
  Hypothesis M_e4  : (5 <= reserved)%Z ->
                     rdn MSEGS_utf8_ubsan m1 (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved)).
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
    stepLD8 F_bf6c0 D_bf6c0 (Z_to_bv 64 W);
    stepLBU F_bf6c4 D_bf6c4 (Z_to_bv 8 h3) ltac:(addr_norm; apply rdn1_of_mem; exact M_b3); rewrite E_b3';
    stepn F_bf6c8 D_bf6c8; rewrite E_ml';
    stepn F_bf6cc D_bf6cc; rewrite E_idx'.

  Local Ltac b1_post_tac := unfold b1_post; repeat split; gres; first [reflexivity | assumption].

  (* [comment removed for export] *)
  Lemma blockB1_map : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W <> 0)%Z -> (w_lastidx W = 0)%Z -> (stride = w_maplen W * 4096 - 16)%Z ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf878 : word) m1 rom) (mkst regs' (0xbf8c0 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hl0 HS.
    eexists. split.
    - b1_head H10 H9.
      stepb_ft F_bf6d0 D_bf6d0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_bf6d4 D_bf6d4. rewrite E_last'.
      stepb_ft F_bf6d8 D_bf6d8 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      stepn F_bf6dc D_bf6dc.
      stepn F_bf6e0 D_bf6e0. rewrite E_pm.
      stepn F_bf6e4 D_bf6e4. addi_renorm. rewrite <- HS.
      stepn F_bf6e8 D_bf6e8.
      apply mst_refl.
    - b1_post_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma blockB1_tab0 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W = 0)%Z -> (w_sizeclass W < 48)%Z -> (stride = 16 * size_class (w_sizeclass W))%Z ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf878 : word) m1 rom) (mkst regs' (0xbf8c0 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hsc HS.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as Hszc.
    destruct (sz_entry m1 (w_sizeclass W) M_img ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as (sbs & Hsbs & Hsv).
    eexists. split.
    - b1_head H10 H9.
      stepb_tk F_bf6d0 D_bf6d0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_eq; lia).
      stepn F_bf6ec D_bf6ec.
      stepn F_bf6f0 D_bf6f0.
      stepn F_bf6f4 D_bf6f4. rewrite E_sc2.
      stepn F_bf6f8 D_bf6f8.
      stepn F_bf6fc D_bf6fc. rewrite (v_add_ZZ 136528 (2 * w_sizeclass W)) by lia.
      stepLHU F_bf700 D_bf700 sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia).
      stepn F_bf704 D_bf704. rewrite (v_slli_Z (size_class (w_sizeclass W)) 4) by (change (2^4)%Z with 16%Z; lia).
      change (2^4)%Z with 16%Z. replace (size_class (w_sizeclass W) * 16)%Z with stride by lia.
      apply mst_refl.
    - b1_post_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma blockB1_tab1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    (w_maplen W <> 0)%Z -> (w_lastidx W <> 0)%Z -> (w_sizeclass W < 48)%Z ->
    (stride = 16 * size_class (w_sizeclass W))%Z ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf878 : word) m1 rom) (mkst regs' (0xbf8c0 : word) m1 rom)
                  /\ b1_post regs regs'.
  Proof.
    intros regs rom H10 H9 Hmz Hl Hsc HS.
    pose proof (size_class_pos (w_sizeclass W) ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as Hszc.
    destruct (sz_entry m1 (w_sizeclass W) M_img ltac:(pose proof (f_scr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE); lia)) as (sbs & Hsbs & Hsv).
    eexists. split.
    - b1_head H10 H9.
      stepb_ft F_bf6d0 D_bf6d0 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_bf6d4 D_bf6d4. rewrite E_last'.
      stepb_tk F_bf6d8 D_bf6d8 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
      stepn F_bf6ec D_bf6ec.
      stepn F_bf6f0 D_bf6f0.
      stepn F_bf6f4 D_bf6f4. rewrite E_sc2.
      stepn F_bf6f8 D_bf6f8.
      stepn F_bf6fc D_bf6fc. rewrite (v_add_ZZ 136528 (2 * w_sizeclass W)) by lia.
      stepLHU F_bf700 D_bf700 sbs (Z_to_bv 64 (size_class (w_sizeclass W)))
        ltac:(addr_norm; exact Hsbs) ltac:(rewrite Hsv; u_norm; lia).
      stepn F_bf704 D_bf704. rewrite (v_slli_Z (size_class (w_sizeclass W)) 4) by (change (2^4)%Z with 16%Z; lia).
      change (2^4)%Z with 16%Z. replace (size_class (w_sizeclass W) * 16)%Z with stride by lia.
      apply mst_refl.
    - b1_post_tac.
  Qed.

  Lemma blockB1 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf878 : word) m1 rom) (mkst regs' (0xbf8c0 : word) m1 rom)
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
    stepLD8 F_bf708 D_bf708 (Z_to_bv 64 M);
    stepn F_bf70c D_bf70c; rewrite H12, H8, (v_mul_Z stride idx) by lia;
    stepn F_bf710 D_bf710;
    stepn F_bf714 D_bf714; rewrite H12, (v_add_ZZ M stride) by lia;
    stepn F_bf718 D_bf718; rewrite (v_add_ZZ (M + stride) (stride * idx)) by lia;
    replace (M + stride + stride * idx)%Z with (e - 12)%Z by lia;
    stepn F_bf71c D_bf71c; addi_renorm; replace (e - 0)%Z with e by lia;
    stepn F_bf720 D_bf720; rewrite H13, E_rc.

  Local Ltac b2_tail H9 :=
    stepn F_bf750 D_bf750; rewrite H9, (v_sub_ZZ e p) by lia;
    stepb_tk F_bf754 D_bf754 ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_ge; lia);
    stepn F_bf75c D_bf75c; rewrite (v_sub_ZZ e reserved) by lia;
    stepLBU F_bf760 D_bf760 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact M_zr); vals_lit;
    stepb_tk F_bf764 D_bf764 ltac:(cond_compute);
    stepLBU F_bf76c D_bf76c (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact M_end); vals_lit;
    stepb_tk F_bf770 D_bf770 ltac:(cond_compute);
    apply mst_refl.

  Local Ltac b2_post_tac := unfold b2_post; repeat split; gres; first [reflexivity | assumption].

  Lemma blockB2_small : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    (reserved < 5)%Z ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf8c0 : word) m1 rom) (mkst regs' (0xbf930 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8 Hsmall.
    eexists. split.
    - b2_head H10 H9 H12 H13 H8.
      stepb_tk F_bf724 D_bf724 ltac:(rewrite H13; rewrite c_ltu_Z by lia; pose proof (Bh_lt Hsmall); apply Z.ltb_lt; lia).
      rewrite (R3 Hsmall).
      b2_tail H9.
    - b2_post_tac.
  Qed.

  Lemma blockB2_big : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    (5 <= reserved)%Z ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf8c0 : word) m1 rom) (mkst regs' (0xbf930 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8 Hbig.
    pose proof (M_e5 Hbig) as Me5. pose proof (M_e4 Hbig) as Me4.
    eexists. split.
    - b2_head H10 H9 H12 H13 H8.
      stepb_ft F_bf724 D_bf724 ltac:(rewrite H13; rewrite c_ltu_Z by lia; pose proof (Bh_ge Hbig); apply Z.ltb_ge; lia).
      rewrite (R4 Hbig).
      stepn F_bf728 D_bf728.
      stepb_tk F_bf72c D_bf72c ltac:(cond_compute).
      stepLD F_bf734 D_bf734 (word_to_le_bytes 4 (Z_to_bv 64 reserved)) (Z_to_bv 64 reserved)
        ltac:(addr_norm; exact Me4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      stepn F_bf738 D_bf738.
      stepb_tk F_bf73c D_bf73c ltac:(rewrite c_ltu_Z by lia; apply Z.ltb_lt; lia).
      stepLBU F_bf744 D_bf744 (Z_to_bv 8 0) ltac:(addr_norm; apply rdn1_of_mem; exact Me5). vals_lit.
      stepb_tk F_bf748 D_bf748 ltac:(cond_compute).
      b2_tail H9.
    - b2_post_tac.
  Qed.

  Lemma blockB2 : forall regs rom,
    getr regs 10 = Z_to_bv 64 g -> getr regs 9 = Z_to_bv 64 p -> getr regs 12 = Z_to_bv 64 stride ->
    getr regs 13 = Z_to_bv 64 h3 -> getr regs 8 = Z_to_bv 64 idx ->
    exists regs', msteps MSEGS_utf8_ubsan (mkst regs (0xbf8c0 : word) m1 rom) (mkst regs' (0xbf930 : word) m1 rom)
                  /\ b2_post regs regs'.
  Proof.
    intros regs rom H10 H9 H12 H13 H8.
    destruct (Z.lt_ge_cases reserved 5) as [Hs|Hb].
    - exact (blockB2_small regs rom H10 H9 H12 H13 H8 Hs).
    - apply (blockB2_big regs rom H10 H9 H12 H13 H8). lia.
  Qed.
  Unset Default Proof Using.
End BlockB.
Section WithFP4.
Context {fx : FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_free_pro : forall regs mem rom (sp p e M g idx off n stride reserved q W avail freed : Z) (sec : word),
  free_pre mem sp p e M g idx off n stride reserved q W avail freed sec ->
  getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 p ->
  exists regs',
    msteps MSEGS_utf8_ubsan (mkst regs (0xbf854 : word) mem rom)
                 (mkst regs' (0xbf930 : word)
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
Proof.
  intros regs mem rom sp p e M g idx off n stride reserved q W avail freed sec PRE H2 H10.
  pose proof (f_geom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
  set (m1 := free_mem1 mem sp (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)).
  (* [comment removed for export] *)
  destruct (blockA regs mem rom sp p H2 H10 ltac:(lia) ltac:(lia) (fp_sok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE))
    as (r1 & RUN1 & A10 & A9 & A1 & A2 & A8 & A18 & A19 & A3 & A4 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  (* [comment removed for export] *)
  pose proof (f_gm_reads _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)) as GR.
  pose proof (f_gm_pure _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PRE) as GP.
  destruct (get_meta_run r1 m1 rom (0xbf878 : word) p M g idx (res_code reserved) q W avail freed sec GR GP A10 A1
              ltac:(apply ret_ok_even; reflexivity)) as (r2 & RUN2 & B10 & B11 & K2).
  (* [comment removed for export] *)
  pose proof GR as GR'. destruct GR' as [_ Mb3 _ _ Mmem MW _ _ _ _ Mimg].
  pose proof PRE as P'. destruct P' as [_ _ _ _ _ _ _ _ _ _ Hres _ _ _ _ _ _ _ _ _ _ (Hh1 & Hh2 & Hh3) _ _ _ _ Fzr Fe5 Fe4 Fend _ _ _ _ _ _ _ _].
  assert (Me5 : (5 <= reserved)%Z -> m1 (Z_to_bv 64 (e - 5)) = Some (Z_to_bv 8 0)).
  { intros H5. subst m1. rewrite free_mem1_byte by lia. exact (Fe5 H5). }
  assert (Me4 : (5 <= reserved)%Z -> rdn MSEGS_utf8_ubsan m1 (Z_to_bv 64 (e - 4)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 reserved))).
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
End WithFP4.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
