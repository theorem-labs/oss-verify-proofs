(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MemsetLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemsetCode OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2.UbMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzStrResizeUbsan2.GlzStrResizeUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.PuUnorm.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
#[local] Ltac u_norm ::= pu_u_norm.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation USEGS := Ubsan.M.loaded_segments.
#[local] Notation W8 v := (word_to_le_bytes 8 v).
Ltac kept_in ::= cbv [callee_kept app_saved In]; first [ kin | kin_nt ].   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lor7_bounds : forall x, (0 <= x)%Z -> (x <= Z.lor x 7 <= x + 7)%Z.
Proof.
  intros x Hx. pose proof (Z.add_lor_land x 7) as E.
  pose proof (Z.land_nonneg x 7) as N. pose proof (AX2S.land_le_r x 7 Hx ltac:(lia)) as U. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac mlbu F D bb RD :=
  chain_step; [reflexivity
    | eapply (step_lbu _ _ _ _ _ _ _ _ _ bb);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            first [exact RD | replace a with c by (unfold v_addi; unorm; first [f_equal; lia | apply bv_eq; u_norm; lia]); exact RD] end end ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac mld F D vv RD :=
  chain_step; [reflexivity
    | eapply step_ld with (v := vv);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          lazymatch type of RD with rdn _ _ ?c _ = _ =>
            first [exact RD | replace a with c by (unfold v_addi; unorm; first [f_equal; lia | apply bv_eq; u_norm; lia]); exact RD] end end
      | apply bytes_le_to_Z_8 ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac msb F D aa bb oktac :=
  chain_step; [reflexivity
    | eapply step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia]
      | gres; rwH; reflexivity
      | u_norm; first [reflexivity | apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity]
      | oktac ]
    | step_simpl]; vnorm.
(* [comment removed for export] *)
Ltac msdg F D aa oktac :=
  chain_step; [reflexivity
    | eapply step_sd_at with (a := aa);
      [exact F | reflexivity | exact D
      | gres; imm_norm; rwH; rewrite ?v_addi_0; unfold v_addi, v_add; unorm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia]
      | gres; rwH; reflexivity
      | oktac ]
    | step_simpl]; vnorm.


Section PIECES.
Context {fx : FPState}.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Lemma grow_g1_short : forall r1 M1 (obj spl : word) (w0 cw : word) (s na : Z),
  rdn USEGS M1 obj 8 = Some (W8 w0) -> (bv_unsigned w0 mod 256 = 2 * s)%Z ->
  (0 <= s <= 22)%Z -> (22 < s + na)%Z -> (s + na < 2 ^ 62)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr r1 2 = spl -> getr r1 8 = obj -> getr r1 9 = Z_to_bv 64 na -> getr r1 12 = cw ->
  exists r',
    msteps USEGS (mkst r1 (0x5c038 : word) M1 rom) (mkst r' (0x5c08c : word) M1 rom)
    /\ getr r' 10 = Z_to_bv 64 0 /\ getr r' 23 = Z_to_bv 64 22 /\ getr r' 18 = Z_to_bv 64 s
    /\ getr r' 2 = spl /\ getr r' 8 = obj /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 12 = cw
    /\ (forall x : bv 5, In x [3; 4; 19; 20; 21; 22; 24; 25; 26; 27] -> getr r' x = getr r1 x).
Proof using.
  intros r1 M1 obj spl w0 cw s na RD8 Hw0 Hs Hgt Hsz Hobj H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M1 obj w0 RD8) as RD1.
  assert (Ulob : bv_unsigned (lob w0) = (2 * s)%Z) by (rewrite u_lob; exact Hw0).
  assert (Ev : (bv_unsigned w0 mod 2 = 0)%Z).
  { rewrite <- (Z.mod_mod_divide (bv_unsigned w0) 256 2) by (exists 128%Z; reflexivity). rewrite Hw0, Z.mul_comm. apply Z.mod_mul. lia. }
  eexists. split.
  - mlbu F_5bfd8 D_5bfd8 (lob w0) RD1.
    mld F_5bfdc D_5bfdc w0 RD8.
    stepiv F_5bfe0 D_5bfe0 (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; rewrite Ulob, u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; rewrite Z.mul_comm, Z.mod_mul; lia).
    stepb_ft F_5bfe4 D_5bfe4 ltac:(rwH; reflexivity).
    stepn F_5bfe8 D_5bfe8.
    stepiv F_5bfec D_5bfec (Z_to_bv 64 0)
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ev).
    stepb_ft F_5bff0 D_5bff0 ltac:(rwH; reflexivity).
    stepiv F_5bff4 D_5bff4 (Z_to_bv 64 (Z.shiftl (bv_unsigned w0) 56))
      ltac:(gres; rwH; unfold v_slli; reflexivity).
    stepiv F_5bff8 D_5bff8 (Z_to_bv 64 s)
      ltac:(gres; rwH; unfold v_srli; change (bv_unsigned (57%bv : bv 6)) with 57%Z; rewrite shl56_shr57 by lia;
            f_equal; rewrite Hw0, Z.mul_comm, Z.div_mul; lia).
    stepiv F_5bffc D_5bffc (Z_to_bv 64 (22 - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).
    stepb_tk F_5c000 D_5c000 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma grow_g1_long : forall r1 M1 (obj spl : word) (w0 cw : word) (cap s na : Z),
  rdn USEGS M1 obj 8 = Some (W8 w0) -> (bv_unsigned w0 = cap + 2)%Z -> ((cap + 1) mod 2 = 0)%Z ->
  rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = Some (W8 (Z_to_bv 64 s)) ->
  (0 <= s <= cap)%Z -> (cap < s + na)%Z -> (s + na < 2 ^ 62)%Z -> (cap < 2 ^ 62)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr r1 2 = spl -> getr r1 8 = obj -> getr r1 9 = Z_to_bv 64 na -> getr r1 12 = cw ->
  exists r',
    msteps USEGS (mkst r1 (0x5c038 : word) M1 rom) (mkst r' (0x5c08c : word) M1 rom)
    /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 23 = Z_to_bv 64 cap /\ getr r' 18 = Z_to_bv 64 s
    /\ getr r' 2 = spl /\ getr r' 8 = obj /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 12 = cw
    /\ (forall x : bv 5, In x [3; 4; 19; 20; 21; 22; 24; 25; 26; 27] -> getr r' x = getr r1 x).
Proof using.
  intros r1 M1 obj spl w0 cw cap s na RD8 Hw0 Hcap RDs Hs Hgt Hsz Hcap62 Hobj H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor. pose proof (u64_range w0) as Hwr.
  pose proof (rdn1_of_rdn8 M1 obj w0 RD8) as RD1.
  assert (Odd : (bv_unsigned w0 mod 2 = 1)%Z).
  { rewrite Hw0. replace (cap + 2)%Z with (cap + 1 + 1)%Z by lia. rewrite Z.add_mod, Hcap by lia. reflexivity. }
  assert (Ulob1 : (bv_unsigned (lob w0) mod 2 = 1)%Z).
  { rewrite u_lob. rewrite Z.mod_mod_divide by (exists 128%Z; reflexivity). exact Odd. }
  pose proof (conj (Z.mod_pos_bound (bv_unsigned w0) 256 ltac:(lia)) (u_lob w0)) as Ulr.
  eexists. split.
  - mlbu F_5bfd8 D_5bfd8 (lob w0) RD1.
    mld F_5bfdc D_5bfdc w0 RD8.
    stepiv F_5bfe0 D_5bfe0 (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; rewrite u64_lit by lia; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Ulob1).
    stepb_tk F_5bfe4 D_5bfe4 ltac:(rwH; reflexivity).
    stepiv F_5c010 D_5c010 (Z_to_bv 64 (cap + 1))
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (4094%bv : bv 12))) with (2 ^ 64 - 2 ^ 1)%Z;
            rewrite AX2S.land_highmask by lia; f_equal; change (2 ^ 1)%Z with 2%Z; lia).
    stepiv F_5c014 D_5c014 (Z_to_bv 64 cap)
      ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; f_equal; lia).
    stepiv F_5c018 D_5c018 (Z_to_bv 64 1)
      ltac:(gres; rwH; unfold v_andi; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z;
            rewrite land_1 by lia; f_equal; exact Odd).
    stepb_ft F_5c01c D_5c01c ltac:(rwH; reflexivity).
    mld F_5c020 D_5c020 (Z_to_bv 64 s) RDs.
    stepiv F_5c024 D_5c024 (Z_to_bv 64 (cap - s))
      ltac:(gres; rwH; unfold v_sub; u_norm; f_equal; lia).
    stepb_ft F_5c028 D_5c028 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Definition galloc (n cap : Z) : Z := Z.lor (Z.max n (2 * cap)) 7 + 1.

Lemma grow_g2_short : forall r M1 (obj spl cw : word) (s na : Z),
  let cap := 22%Z in let n := (s + na)%Z in
  (0 <= s <= cap)%Z -> (cap < n)%Z -> (n < 2 ^ 61)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr r 10 = Z_to_bv 64 0 -> getr r 23 = Z_to_bv 64 cap -> getr r 18 = Z_to_bv 64 s ->
  getr r 2 = spl -> getr r 8 = obj -> getr r 9 = Z_to_bv 64 na -> getr r 12 = cw ->
  exists r',
    msteps USEGS (mkst r (0x5c08c : word) M1 rom) (mkst r' (0x749a4 : word) M1 rom)
    /\ getr r' 1 = (0x5c12c : word) /\ getr r' 10 = Z_to_bv 64 (galloc n cap) /\ getr r' 21 = Z_to_bv 64 (galloc n cap)
    /\ getr r' 24 = cw /\ getr r' 19 = Z_to_bv 64 (bv_unsigned obj + 1) /\ getr r' 22 = Z_to_bv 64 n
    /\ getr r' 18 = Z_to_bv 64 s /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 8 = obj /\ getr r' 23 = Z_to_bv 64 cap /\ getr r' 2 = spl
    /\ (forall x : bv 5, In x [3; 4; 20; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M1 obj spl cw s na cap n Hs Hgt Hn61 Hobj H10 H23 H18 H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor.
  pose proof (lor7_bounds n ltac:(lia)) as L1. pose proof (lor7_bounds (2 * cap) ltac:(lia)) as L2.
  unfold galloc.
  destruct (Z.lt_ge_cases (2 * cap) n) as [Hgn|Hgn];
    [rewrite (Z.max_l n (2 * cap)) by lia | rewrite (Z.max_r n (2 * cap)) by lia]; eexists; split.
  - stepiv F_5c02c D_5c02c (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).   (* [comment removed for export] *)
    stepiv F_5c030 D_5c030 (Z_to_bv 64 (2 ^ 64 - 9)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    stepiv F_5c034 D_5c034 (Z_to_bv 64 (n - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepiv F_5c038 D_5c038 (Z_to_bv 64 (2 ^ 64 - 9 - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepb_ft F_5c03c D_5c03c ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)
    stepb_tk F_5c040 D_5c040 ltac:(rwH; reflexivity).                                           (* [comment removed for export] *)
    stepiv F_5c07c D_5c07c (Z_to_bv 64 (bv_unsigned obj + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; reflexivity).
    stepiv F_5c080 D_5c080 (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepiv F_5c084 D_5c084 (Z_to_bv 64 (2 ^ 63 - 14)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepb_ft F_5c088 D_5c088 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)

    stepiv F_5c08c D_5c08c (Z_to_bv 64 (2 * cap))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    stepn F_5c090 D_5c090.                                                (* [comment removed for export] *)
    stepb_tk F_5c094 D_5c094 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    stepiv F_5c09c D_5c09c (Z_to_bv 64 (Z.lor n 7))
      ltac:(gres; rwH; rewrite ?v_addi_0; unfold v_ori; u_norm; reflexivity).
    stepn F_5c0a0 D_5c0a0.
    stepb_tk F_5c0a4 D_5c0a4 ltac:(rwH; apply c_eq_neq; u_norm; cbn; lia).
    stepiv F_5c0b4 D_5c0b4 (Z_to_bv 64 (Z.lor n 7 + 1)) ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; reflexivity).
    stepb_tk F_5c0b8 D_5c0b8 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; cbn; lia).
    stepn F_5c0c0 D_5c0c0. stepn F_5c0c4 D_5c0c4. stepn F_5c0c8 D_5c0c8.
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
  - stepiv F_5c02c D_5c02c (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).   (* [comment removed for export] *)
    stepiv F_5c030 D_5c030 (Z_to_bv 64 (2 ^ 64 - 9)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    stepiv F_5c034 D_5c034 (Z_to_bv 64 (n - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepiv F_5c038 D_5c038 (Z_to_bv 64 (2 ^ 64 - 9 - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepb_ft F_5c03c D_5c03c ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)
    stepb_tk F_5c040 D_5c040 ltac:(rwH; reflexivity).                                           (* [comment removed for export] *)
    stepiv F_5c07c D_5c07c (Z_to_bv 64 (bv_unsigned obj + 1)) ltac:(gres; rwH; unfold v_addi; imm_norm; reflexivity).
    stepiv F_5c080 D_5c080 (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepiv F_5c084 D_5c084 (Z_to_bv 64 (2 ^ 63 - 14)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepb_ft F_5c088 D_5c088 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)

    stepiv F_5c08c D_5c08c (Z_to_bv 64 (2 * cap))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    stepn F_5c090 D_5c090.                                                (* [comment removed for export] *)
    stepb_ft F_5c094 D_5c094 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepn F_5c098 D_5c098.                                (* [comment removed for export] *)
    stepiv F_5c09c D_5c09c (Z_to_bv 64 (Z.lor (2 * cap) 7))
      ltac:(gres; rwH; rewrite ?v_addi_0; unfold v_ori; u_norm; reflexivity).
    stepn F_5c0a0 D_5c0a0.
    stepb_tk F_5c0a4 D_5c0a4 ltac:(rwH; apply c_eq_neq; u_norm; cbn; lia).
    stepiv F_5c0b4 D_5c0b4 (Z_to_bv 64 (Z.lor (2 * cap) 7 + 1)) ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; reflexivity).
    stepb_tk F_5c0b8 D_5c0b8 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; cbn; lia).
    stepn F_5c0c0 D_5c0c0. stepn F_5c0c4 D_5c0c4. stepn F_5c0c8 D_5c0c8.
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

Lemma grow_g2_long : forall r M1 (obj spl cw d : word) (cap s na : Z),
  let n := (s + na)%Z in
  rdn USEGS M1 (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = Some (W8 d) ->
  (22 <= cap)%Z -> (0 <= s <= cap)%Z -> (cap < n)%Z -> (n < 2 ^ 61)%Z -> (cap < 2 ^ 61)%Z -> (bv_unsigned obj + 24 <= 2 ^ 64)%Z ->
  getr r 10 = Z_to_bv 64 1 -> getr r 23 = Z_to_bv 64 cap -> getr r 18 = Z_to_bv 64 s ->
  getr r 2 = spl -> getr r 8 = obj -> getr r 9 = Z_to_bv 64 na -> getr r 12 = cw ->
  exists r',
    msteps USEGS (mkst r (0x5c08c : word) M1 rom) (mkst r' (0x749a4 : word) M1 rom)
    /\ getr r' 1 = (0x5c12c : word) /\ getr r' 10 = Z_to_bv 64 (galloc n cap) /\ getr r' 21 = Z_to_bv 64 (galloc n cap)
    /\ getr r' 24 = cw /\ getr r' 19 = d /\ getr r' 22 = Z_to_bv 64 n
    /\ getr r' 18 = Z_to_bv 64 s /\ getr r' 9 = Z_to_bv 64 na /\ getr r' 8 = obj /\ getr r' 23 = Z_to_bv 64 cap /\ getr r' 2 = spl
    /\ (forall x : bv 5, In x [3; 4; 20; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M1 obj spl cw d cap s na n RDd Hcap22 Hs Hgt Hn61 Hcap61 Hobj H10 H23 H18 H2 H8 H9 H12.
  pose proof (u64_range obj) as Hor.
  pose proof (lor7_bounds n ltac:(lia)) as L1. pose proof (lor7_bounds (2 * cap) ltac:(lia)) as L2.
  unfold galloc.
  destruct (Z.lt_ge_cases (2 * cap) n) as [Hgn|Hgn];
    [rewrite (Z.max_l n (2 * cap)) by lia | rewrite (Z.max_r n (2 * cap)) by lia]; eexists; split.
  - stepiv F_5c02c D_5c02c (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).   (* [comment removed for export] *)
    stepiv F_5c030 D_5c030 (Z_to_bv 64 (2 ^ 64 - 9)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    stepiv F_5c034 D_5c034 (Z_to_bv 64 (n - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepiv F_5c038 D_5c038 (Z_to_bv 64 (2 ^ 64 - 9 - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepb_ft F_5c03c D_5c03c ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)
    stepb_ft F_5c040 D_5c040 ltac:(rwH; reflexivity).                                           (* [comment removed for export] *)
    mld F_5c044 D_5c044 d RDd.                                                                   (* [comment removed for export] *)
    stepiv F_5c048 D_5c048 (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepiv F_5c04c D_5c04c (Z_to_bv 64 (2 ^ 63 - 14)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepb_tk F_5c050 D_5c050 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)

    stepiv F_5c08c D_5c08c (Z_to_bv 64 (2 * cap))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    stepn F_5c090 D_5c090.                                                (* [comment removed for export] *)
    stepb_tk F_5c094 D_5c094 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_lt; lia).  (* [comment removed for export] *)
    stepiv F_5c09c D_5c09c (Z_to_bv 64 (Z.lor n 7))
      ltac:(gres; rwH; rewrite ?v_addi_0; unfold v_ori; u_norm; reflexivity).
    stepn F_5c0a0 D_5c0a0.
    stepb_tk F_5c0a4 D_5c0a4 ltac:(rwH; apply c_eq_neq; u_norm; cbn; lia).
    stepiv F_5c0b4 D_5c0b4 (Z_to_bv 64 (Z.lor n 7 + 1)) ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; reflexivity).
    stepb_tk F_5c0b8 D_5c0b8 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; cbn; lia).
    stepn F_5c0c0 D_5c0c0. stepn F_5c0c4 D_5c0c4. stepn F_5c0c8 D_5c0c8.
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
  - stepiv F_5c02c D_5c02c (Z_to_bv 64 n) ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).   (* [comment removed for export] *)
    stepiv F_5c030 D_5c030 (Z_to_bv 64 (2 ^ 64 - 9)) ltac:(gres; apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    stepiv F_5c034 D_5c034 (Z_to_bv 64 (n - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepiv F_5c038 D_5c038 (Z_to_bv 64 (2 ^ 64 - 9 - cap)) ltac:(gres; rwH; unfold v_sub; u_norm; reflexivity).
    stepb_ft F_5c03c D_5c03c ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)
    stepb_ft F_5c040 D_5c040 ltac:(rwH; reflexivity).                                           (* [comment removed for export] *)
    mld F_5c044 D_5c044 d RDd.                                                                   (* [comment removed for export] *)
    stepiv F_5c048 D_5c048 (Z_to_bv 64 (2 ^ 64 - 27)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepiv F_5c04c D_5c04c (Z_to_bv 64 (2 ^ 63 - 14)) ltac:(gres; apply bv_eq; vm_compute; reflexivity). (* [comment removed for export] *)
    stepb_tk F_5c050 D_5c050 ltac:(rwH; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).    (* [comment removed for export] *)

    stepiv F_5c08c D_5c08c (Z_to_bv 64 (2 * cap))
      ltac:(gres; rwH; unfold v_slli; u_norm; change (bv_unsigned (1%bv : bv 6)) with 1%Z; rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia).
    stepn F_5c090 D_5c090.                                                (* [comment removed for export] *)
    stepb_ft F_5c094 D_5c094 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; lia).  (* [comment removed for export] *)
    stepn F_5c098 D_5c098.                                (* [comment removed for export] *)
    stepiv F_5c09c D_5c09c (Z_to_bv 64 (Z.lor (2 * cap) 7))
      ltac:(gres; rwH; rewrite ?v_addi_0; unfold v_ori; u_norm; reflexivity).
    stepn F_5c0a0 D_5c0a0.
    stepb_tk F_5c0a4 D_5c0a4 ltac:(rwH; apply c_eq_neq; u_norm; cbn; lia).
    stepiv F_5c0b4 D_5c0b4 (Z_to_bv 64 (Z.lor (2 * cap) 7 + 1)) ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; reflexivity).
    stepb_tk F_5c0b8 D_5c0b8 ltac:(rwH; rewrite ?v_addi_0; unfold c_ltu, bv_ltu; u_norm; apply Z.ltb_ge; cbn; lia).
    stepn F_5c0c0 D_5c0c0. stepn F_5c0c4 D_5c0c4. stepn F_5c0c8 D_5c0c8.
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma grow_g3_move : forall r M (p src : word) (s : Z),
  getr r 10 = p -> getr r 18 = Z_to_bv 64 s -> getr r 19 = src -> (0 < s < 2 ^ 63)%Z ->
  exists r',
    msteps USEGS (mkst r (0x5c12c : word) M rom) (mkst r' (0x736b4 : word) M rom)
    /\ getr r' 1 = (0x5c144 : word) /\ getr r' 10 = p /\ getr r' 11 = src /\ getr r' 12 = Z_to_bv 64 s /\ getr r' 20 = p
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M p src s H10 H18 H19 Hs.
  eexists. split.
  - stepn F_5c0cc D_5c0cc.                                                (* [comment removed for export] *)
    stepb_ft F_5c0d0 D_5c0d0 ltac:(rwH; rewrite ?v_addi_0; apply c_eq_neq; u_norm; cbn; lia).  (* [comment removed for export] *)
    stepn F_5c0d4 D_5c0d4. stepn F_5c0d8 D_5c0d8. stepn F_5c0dc D_5c0dc.  (* [comment removed for export] *)
    stepn F_5c0e0 D_5c0e0.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma grow_g3_nomove : forall r M (p : word),
  getr r 10 = p -> getr r 18 = Z_to_bv 64 0 ->
  exists r',
    msteps USEGS (mkst r (0x5c12c : word) M rom) (mkst r' (0x5c144 : word) M rom)
    /\ getr r' 20 = p
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M p H10 H18.
  eexists. split.
  - stepn F_5c0cc D_5c0cc.                                                (* [comment removed for export] *)
    stepb_tk F_5c0d0 D_5c0d0 ltac:(rwH; rewrite ?v_addi_0; reflexivity).  (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma grow_g4_long : forall r M (d : word) (cap : Z),
  getr r 23 = Z_to_bv 64 cap -> getr r 19 = d -> (23 <= cap < 2 ^ 63)%Z ->
  exists r',
    msteps USEGS (mkst r (0x5c144 : word) M rom) (mkst r' (0x5a5a4 : word) M rom)
    /\ getr r' 1 = (0x5c158 : word) /\ getr r' 10 = d
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M d cap H23 H19 Hcap.
  eexists. split.
  - stepiv F_5c0e4 D_5c0e4 (Z_to_bv 64 (cap + 1)) ltac:(gres; rwH; unfold v_addi; u_norm; imm_norm; reflexivity).  (* [comment removed for export] *)
    stepn F_5c0e8 D_5c0e8.                                                (* [comment removed for export] *)
    stepb_ft F_5c0ec D_5c0ec ltac:(rwH; apply c_eq_neq; u_norm; cbn; lia).  (* [comment removed for export] *)
    stepn F_5c0f0 D_5c0f0.                                                (* [comment removed for export] *)
    stepn F_5c0f4 D_5c0f4.                                                (* [comment removed for export] *)
    pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Lemma grow_g4_short : forall r M,
  getr r 23 = Z_to_bv 64 22 ->
  exists r',
    msteps USEGS (mkst r (0x5c144 : word) M rom) (mkst r' (0x5c158 : word) M rom)
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M H23.
  eexists. split.
  - stepn F_5c0e4 D_5c0e4.                                                (* [comment removed for export] *)
    stepn F_5c0e8 D_5c0e8.                                                (* [comment removed for export] *)
    stepb_tk F_5c0ec D_5c0ec ltac:(rwH; reflexivity).                    (* [comment removed for export] *)
    pu_refl.
  - intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

(* [comment removed for export] *)
Definition hdr_mem (M : word -> option byte) (obj p : word) (alloc s : Z) : word -> option byte :=
  wbytes (wbytes (wbytes M obj (W8 (Z_to_bv 64 (alloc + 1)))) (Z_to_bv 64 (bv_unsigned obj + 8)) (W8 (Z_to_bv 64 s)))
         (Z_to_bv 64 (bv_unsigned obj + 16)) (W8 p).

Lemma lor1_even : forall a, (0 <= a)%Z -> (a mod 2 = 0)%Z -> Z.lor a 1 = (a + 1)%Z.
Proof using.
  intros a Ha He. pose proof (Z.add_lor_land a 1) as E. rewrite land_1 in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma grow_g5 : forall r M (obj p cw : word) (alloc s na : Z),
  getr r 21 = Z_to_bv 64 alloc -> getr r 8 = obj -> getr r 18 = Z_to_bv 64 s -> getr r 20 = p -> getr r 24 = cw ->
  getr r 9 = Z_to_bv 64 na ->
  (0 <= alloc < 2 ^ 63)%Z -> (alloc mod 2 = 0)%Z -> (0 <= s)%Z -> (bv_unsigned p + s < 2 ^ 64)%Z ->
  (bv_unsigned obj + 24 <= 2 ^ 64)%Z -> store_ok USEGS M obj 24 = true ->
  exists r',
    msteps USEGS (mkst r (0x5c158 : word) M rom) (mkst r' (0x73830 : word) (hdr_mem M obj p alloc s) rom)
    /\ getr r' 1 = (0x5c17c : word) /\ getr r' 10 = Z_to_bv 64 (bv_unsigned p + s) /\ getr r' 11 = cw /\ getr r' 12 = Z_to_bv 64 na
    /\ (forall x : bv 5, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r' x = getr r x).
Proof using.
  intros r M obj p cw alloc s na H21 H8 H18 H20 H24 H9 Hal Hev Hs Hps Hobj STO.
  pose proof (u64_range obj) as Hor. pose proof (u64_range p) as Hpr.
  assert (ST0 : store_ok USEGS M obj 8 = true).
  { rewrite <- (Z_to_bv_bv_unsigned 64 obj). eapply (store_ok_sub USEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (ST8 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 8)) 8 = true).
  { eapply (store_ok_sub USEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  assert (ST16 : store_ok USEGS M (Z_to_bv 64 (bv_unsigned obj + 16)) 8 = true).
  { eapply (store_ok_sub USEGS M obj _ 24); [cbn; lia | exact STO | u_norm; lia | u_norm; cbn; lia]. }
  eexists. split.
  - stepiv F_5c0f8 D_5c0f8 (Z_to_bv 64 (alloc + 1))
      ltac:(gres; rwH; unfold v_ori; u_norm; change (bv_wrap 64 (bv_signed (1%bv : bv 12))) with 1%Z; rewrite lor1_even by lia; reflexivity).
    msdg F_5c0fc D_5c0fc obj ltac:(exact ST0).                                                   (* [comment removed for export] *)
    msdg F_5c100 D_5c100 (Z_to_bv 64 (bv_unsigned obj + 8)) ltac:(eapply store_ok_mono; [apply wbytes_grows | exact ST8]).
    msdg F_5c104 D_5c104 (Z_to_bv 64 (bv_unsigned obj + 16))
      ltac:(eapply store_ok_mono; [apply wbytes_grows|]; eapply store_ok_mono; [apply wbytes_grows | exact ST16]).
    stepn F_5c108 D_5c108.                                                (* [comment removed for export] *)
    stepiv F_5c10c D_5c10c (Z_to_bv 64 (bv_unsigned p + s)) ltac:(gres; rwH; unfold v_add; u_norm; reflexivity).
    stepn F_5c110 D_5c110. stepn F_5c114 D_5c114.                         (* [comment removed for export] *)
    stepn F_5c118 D_5c118.                                                (* [comment removed for export] *)
    unfold hdr_mem. pu_refl.
  - repeat split; gres; rwH; rewrite ?v_addi_0; try reflexivity; try bveq.
    intros x Hx. cbv [In] in Hx. repeat (destruct Hx as [<-|Hx]; [gres; rwH; reflexivity|]). destruct Hx.
Qed.

End PIECES.
