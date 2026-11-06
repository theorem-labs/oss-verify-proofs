(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EbtLeaf EbtAllocG EbtPoison ArtRuns ArtRunsMem EbtFp EbtFree1 EbtPopulate1 EbtCellEx EbtRecycle3.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r3ef18_4052c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Ltac zcl4 := lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ =>
  let v := eval vm_compute in (bv_unsigned x) in replace x with (Z_to_bv 64 v : word) by (apply bv_eq; vm_compute; reflexivity) end.

Lemma art_zb_divuw : forall x y, 0 <= x < 2 ^ 64 -> 0 < y < 2 ^ 32 -> (x mod 2 ^ 32) / y < 2 ^ 31 ->
  v_divuw (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 ((x mod 2 ^ 32) / y).
Proof.
  intros x y Hx Hy Hq. unfold v_divuw. rewrite !art_u_lit by lia. unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32).
  rewrite (Z.mod_small y) by lia. replace (y =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  assert (0 <= x mod 2 ^ 32 / y) by (apply Z.div_pos; [apply Z.mod_pos_bound|]; lia).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma art_land_31 : forall c, 0 <= c < 32 -> Z.land c 31 = c.
Proof. intros c Hc. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Definition art_cas30w_ok (b1 : Z) : bool :=
  bv_eqb (v_xor (Z_to_bv 64 (3 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (3 + 256 * b1)) (Z_to_bv 64 0)) (Z_to_bv 64 255))) (Z_to_bv 64 (256 * b1)).
Lemma art_cas30w_all : forallb art_cas30w_ok (AsanTab.zrange 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma art_cas30w : forall b1, 0 <= b1 < 256 ->
  v_xor (Z_to_bv 64 (3 + 256 * b1)) (v_and (v_xor (Z_to_bv 64 (3 + 256 * b1)) (Z_to_bv 64 0)) (Z_to_bv 64 255)) = Z_to_bv 64 (256 * b1).
Proof.
  intros b1 Hb. pose proof art_cas30w_all as H. rewrite forallb_forall in H.
  specialize (H b1 ltac:(unfold AsanTab.zrange; apply AsanTab.in_ziota; rewrite Z2Nat.id by lia; lia)). unfold art_cas30w_ok, bv_eqb in H.
  apply Z.eqb_eq in H. apply bv_eq. exact H.
Qed.

Ltac zlhu4 F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].
Lemma art_zb_or4 : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_cbr_pa1 : forall regs (M rom : word -> option byte) (raw : word) (sp cb m spb c off : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 -> 0 <= cb < 2 ^ 64 ->
  0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= off < 2 ^ 32 -> m = spb + c * 2 ^ 32 + off ->
  cellA M (1321624 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x55904 : word) M rom) (mkst regs' (0x559b4 : word) (art_f48 M sp raw regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 cb /\ getr regs' 9 = Z_to_bv 64 m /\ getr regs' 19 = Z_to_bv 64 1321624
    /\ getr regs' 20 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 spb /\ getr regs' 11 = Z_to_bv 64 (spb + 2 ^ 37) /\ getr regs' 12 = Z_to_bv 64 c
    /\ getr regs' 13 = Z_to_bv 64 c /\ getr regs' 14 = Z_to_bv 64 (m - spb) /\ getr regs' 15 = Z_to_bv 64 (AsanTab.class_size c)
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb m spb c off H1 H2 H10 H11 Hsp Hsp' W Hcb Hspb Hspb' Hc Hoff Em Cspb.
  assert (Ediv : (m - spb) / 2 ^ 32 = c).
  { symmetry. apply (Z.div_unique_pos (m - spb) (2 ^ 32) c off); lia. }
  destruct (Z_le_gt_dec c 16) as [Lc|Gc].
  - eexists. split.
    { zstep F_558b4 D_558b4.
      zsd F_558b8 D_558b8 (sp - 8) (U raw) ltac:(rewok W). zsd F_558bc D_558bc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_558c0 D_558c0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_558c4 D_558c4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_558c8 D_558c8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_558cc D_558cc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_558d0 D_558d0. zstep F_558d4 D_558d4.
      stepn F_558d8 D_558d8. stepn F_558dc D_558dc. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1321624 + 32) 8 spb) by zcell end.
      zld F_558e0 D_558e0 (1321624 + 32) Cspb'.
      zstep F_558e4 D_558e4. zstep F_558e8 D_558e8.
      zbft F_558ec D_558ec.
      zstep F_558f0 D_558f0.
      zbft F_558f4 D_558f4.
      zstep F_558f8 D_558f8.
      stepn F_558fc D_558fc. rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
      stepn F_55900 D_55900. rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
      zstep F_55904 D_55904.
      zbft F_55908 D_55908.
      zstep F_5590c D_5590c.
      zbft F_55910 D_55910.
      zbft F_55914 D_55914.
      zstep F_55918 D_55918.
      stepn F_5591c D_5591c.
      unfold art_f48. apply mst_refl. }
    rewrite (art_class_size_small c ltac:(lia)).
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_558b4 D_558b4.
      zsd F_558b8 D_558b8 (sp - 8) (U raw) ltac:(rewok W). zsd F_558bc D_558bc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_558c0 D_558c0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_558c4 D_558c4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_558c8 D_558c8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_558cc D_558cc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_558d0 D_558d0. zstep F_558d4 D_558d4.
      stepn F_558d8 D_558d8. stepn F_558dc D_558dc. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1321624 + 32) 8 spb) by zcell end.
      zld F_558e0 D_558e0 (1321624 + 32) Cspb'.
      zstep F_558e4 D_558e4. zstep F_558e8 D_558e8.
      zbft F_558ec D_558ec.
      zstep F_558f0 D_558f0.
      zbft F_558f4 D_558f4.
      zstep F_558f8 D_558f8.
      stepn F_558fc D_558fc. rwH. rewrite (art_zb_srli (m - spb) 32) by lia. rewrite Ediv.
      stepn F_55900 D_55900. rwH. rewrite (art_zb_andi c 31) by lia. rewrite (art_land_31 c) by lia.
      zstep F_55904 D_55904.
      zbft F_55908 D_55908.
      zstep F_5590c D_5590c.
      zbtk F_55910 D_55910.
      zstep F_55940 D_55940. zstep F_55944 D_55944. zstep F_55948 D_55948. zstep F_5594c D_5594c. zstep F_55950 D_55950. zstep F_55954 D_55954.
      zstep F_55958 D_55958. zstep F_5595c D_5595c. zstep F_55960 D_55960.
      fold (art_pop_szw c). rewrite (art_pop_szw_ok c ltac:(lia)).
      unfold art_f48. apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_pa2 : forall regs (M rom : word -> option byte) (m spb ris c off i mu : Z),
  let sz := AsanTab.class_size c in
  getr regs 10 = Z_to_bv 64 spb -> getr regs 11 = Z_to_bv 64 (spb + 2 ^ 37) -> getr regs 12 = Z_to_bv 64 c -> getr regs 13 = Z_to_bv 64 c ->
  getr regs 14 = Z_to_bv 64 (m - spb) -> getr regs 15 = Z_to_bv 64 sz -> getr regs 19 = Z_to_bv 64 1321624 ->
  0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> ris = spb + 2 ^ 37 -> 1 <= c <= 30 -> 0 <= off < 2 ^ 32 -> m = spb + c * 2 ^ 32 + off ->
  0 <= i -> sz * i <= off < sz * (i + 1) -> sz * i + sz <= mu -> mu <= 3758096384 ->
  cellA M (1321624 + 48) 8 ris -> cellA M (ris + 128 * c + 48) 8 mu ->
  exists regs', msteps ASEGS (mkst regs (0x559b4 : word) M rom) (mkst regs' (0x559f8 : word) M rom)
    /\ getr regs' 18 = Z_to_bv 64 (spb + c * 2 ^ 32 + sz * i)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m spb ris c off i mu sz H10 H11 H12 H13 H14 H15 H19 Hspb Hspb' Eris Hc Hoff Em Hi Hoi Hmu Hmu' Cris Cmu.
  pose proof (art_class_size_facts c Hc) as (Hsz & _). fold sz in Hsz.
  assert (Emod : (m - spb) mod 2 ^ 32 = off).
  { symmetry. apply (Z.mod_unique_pos (m - spb) (2 ^ 32) c off); lia. }
  assert (Eq : off / sz = i).
  { symmetry. apply (Z.div_unique_pos off sz i (off - sz * i)); lia. }
  assert (Hi' : i < 2 ^ 27). { assert (sz * i < 2 ^ 32) by lia. nia. }
  eexists. split.
  { stepn F_55964 D_55964. rwH. rewrite (art_zb_divuw (m - spb) sz) by (rewrite ?Emod, ?Eq; lia). rewrite Emod, Eq.
    zstep F_55968 D_55968.
    zld F_5596c D_5596c (1321624 + 48) Cris.
    zstep F_55970 D_55970. zstep F_55974 D_55974. zstep F_55978 D_55978. zstep F_5597c D_5597c.
    zld F_55980 D_55980 (ris + 128 * c + 48) Cmu.
    stepn F_55984 D_55984. rwH. rewrite (art_zb_srli_exact _ 32 i) by lia.
    zstep F_55988 D_55988. zstep F_5598c D_5598c. zstep F_55990 D_55990. zstep F_55994 D_55994. zstep F_55998 D_55998.
    stepn F_5599c D_5599c. rwH. rewrite (art_zb_and 18446744073709551615 (c * 2 ^ 32 + spb + sz * i)) by lia. rewrite art_land_full_l by lia.
    zbft F_559a0 D_559a0.
    zbft F_559a4 D_559a4.
    apply mst_refl. }
  split; [gres; f_equal; lia|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_magic : forall regs (M rom : word -> option byte) (m ab : Z),
  getr regs 9 = Z_to_bv 64 m -> getr regs 18 = Z_to_bv 64 ab ->
  0x69c000 <= ab -> ab + 8 < 2 ^ 47 -> 0 <= m < 2 ^ 64 -> ab mod 8 = 0 ->
  cellA M 0x10378 8 0xcc6e96b9cc6e96b9 ->
  (ab <> m -> cellA M ab 8 0xcc6e96b9cc6e96b9 /\ wrA M ab 8) ->
  exists regs', msteps ASEGS (mkst regs (0x559f8 : word) M rom) (mkst regs' (0x55a14 : word) (if ab =? m then M else Wn 8 M ab 0) rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m ab H9 H18 Hab Hab' Hm Hab8 Cmag Hne.
  destruct (Z.eqb_spec ab m) as [E|NE].
  - eexists. split.
    { zbtk F_559a8 D_559a8. apply mst_refl. }
    intros r Hr. reflexivity.
  - destruct (Hne NE) as [Cab Wab].
    eexists. split.
    { zbft F_559a8 D_559a8.
      stepn F_559ac D_559ac. zcl4.
      zld F_559b0 D_559b0 0x10378 Cmag.
      chain_step; [reflexivity
        | eapply (art_step_lr_d _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab) _ (Z_to_bv 64 0xcc6e96b9cc6e96b9));
          [exact F_559b4 | reflexivity | exact D_559b4 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8
          | exact Cab | apply bytes_le_to_Z_8 ]
        | ]. wpc.
      chain_step; [reflexivity
        | eapply art_step_branch_ft_r; [exact F_559b8 | reflexivity | exact D_559b8 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
        | ]. wpc.
      chain_step; [reflexivity
        | eapply (art_step_sc_d_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ab));
          [exact F_559bc | reflexivity | exact D_559bc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hab8 | gres; rwH; reflexivity
          | eapply (wr_wok _ _ _ _ Wab); lia ]
        | ]. wpc.
      change (wbytes ?M0 (Z_to_bv 64 ab) (word_to_le_bytes 8 (Z_to_bv 64 0))) with (Wn 8 M0 ab 0).
      zbft F_559c0 D_559c0.
      apply mst_refl. }
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_cas30 : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 9 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 256 ->
  cellA M m 4 (3 + 256 * b1) -> wrA M m 4 ->
  exists regs', msteps ASEGS (mkst regs (0x55a14 : word) M rom) (mkst regs' (0x55a4c : word) (Wn 4 M m (256 * b1)) rom)
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m b1 H9 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  eexists. split.
  { stepn F_559c4 D_559c4. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
    replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
    stepn F_559c8 D_559c8. rwH. rewrite art_zb_slli by lia.
    zstep F_559cc D_559cc. zstep F_559d0 D_559d0.
    stepn F_559d4 D_559d4. rwH. rewrite art_sllw_0 by lia.
    stepn F_559d8 D_559d8. rwH. rewrite art_sllw_0 by lia.
    chain_step; [reflexivity
      | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (3 + 256 * b1)));
        [exact F_559dc | reflexivity | exact D_559dc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
        | exact Chw | apply art_bytes4; lia ]
      | ]. wpc. rewrite art_v_lw_small by lia.
    chain_step; [reflexivity | eapply art_step_and_r; [exact F_559e0 | reflexivity | exact D_559e0 | reflexivity] | ]. wpc.
    gres. rewrite (art_zb_and (3 + 256 * b1) 255) by lia.
    replace (Z.land (3 + 256 * b1) 255) with 3.
    2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (3 + 256 * b1) with (3 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
    chain_step; [reflexivity
      | eapply art_step_branch_ft_r; [exact F_559e4 | reflexivity | exact D_559e4 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
      | ]. wpc.
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_559e8 | reflexivity | exact D_559e8 | reflexivity] | ]. wpc.
    chain_step; [reflexivity | eapply art_step_and_r; [exact F_559ec | reflexivity | exact D_559ec | reflexivity] | ]. wpc.
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_559f0 | reflexivity | exact D_559f0 | reflexivity] | ]. wpc.
    gres.
    rewrite art_cas30w by lia.
    match goal with |- msteps _ (mkstr _ _ ?X _ _) _ => assert (Whw' : wokA X m 4) by (eapply (wr_wok _ _ _ _ Whw); lia) end.
    chain_step; [reflexivity
      | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
        [exact F_559f4 | reflexivity | exact D_559f4 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
        | exact Whw' ]
      | ]. wpc.
    change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (256 * b1)))) with (Wn 4 M0 m (256 * b1)).
    zbft F_559f8 D_559f8.
    apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_pd : forall regs (M rom : word -> option byte) (m n : Z),
  getr regs 9 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
  cellA M (m + 2) 2 0 -> cellA M (m + 4) 4 n ->
  exists regs', msteps ASEGS (mkst regs (0x55a4c : word) M rom) (mkst regs' (0x7bce4 : word) M rom)
    /\ getr regs' 1 = (0x55a70 : bv 64)%bv /\ getr regs' 10 = Z_to_bv 64 (m + 16) /\ getr regs' 11 = Z_to_bv 64 ((n + 7) / 8 * 8) /\ getr regs' 12 = Z_to_bv 64 250
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom m n H9 Hm Hm' Hn Chi Cn.
  eexists. split.
  { zlhu4 F_559fc D_559fc (m + 2) Chi.
    zlwu F_55a00 D_55a00 (m + 4) Cn.
    zstep F_55a04 D_55a04. zstep F_55a08 D_55a08.
    stepn F_55a0c D_55a0c. rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
    zstep F_55a10 D_55a10.
    stepn F_55a14 D_55a14. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.
    zstep F_55a18 D_55a18.
    stepn F_55a1c D_55a1c.
    apply mst_refl. }
  split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

Definition art_cbr_stats_mem (M : word -> option byte) (sp1 t n f1 f2 : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp1 - 8) 0x55a74) (sp1 - 24) 0x83c68) (t + 2800 + 40) (f1 + 1)) (t + 2800 + 48) (n + f2).

#[using="Type"] Lemma art_cbr_stats : forall regs (M rom : word -> option byte) (sp1 HI tp key tsd ctx t m n f1 f2 : Z),
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 m ->
  0x69c000 <= HI -> HI <= sp1 - 32 -> sp1 < 2 ^ 64 -> wrA M (sp1 - 32) 32 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> wrA M t 4096 ->
  16 <= m -> m + 16 <= HI -> 0 <= n < 2 ^ 32 -> 0 <= f1 < 2 ^ 64 -> 0 <= f2 < 2 ^ 64 ->
  cellA M (m + 2) 2 0 -> cellA M (m + 4) 4 n -> cellA M (t + 2800 + 40) 8 f1 -> cellA M (t + 2800 + 48) 8 f2 ->
  exists regs', msteps ASEGS (mkst regs (0x55a70 : word) M rom) (mkst regs' (0x55a9c : word) (art_cbr_stats_mem M sp1 t n f1 f2) rom)
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 HI tp key tsd ctx t m n f1 f2 H2 H4 H9 HHI Hsp Hsp' W TSD Ht Ht' Htp Htsd Hctx Wt Hm Hm' Hn Hf1 Hf2 Chi Cn C40 C48.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  eexists. split.
  { stepn F_55a20 D_55a20.
    zcall (art_thread_stats_fn _ _ _ (0x55a74 : word) sp1 tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chi' : cellA X (m + 2) 2 0) by zcell; assert (Cn' : cellA X (m + 4) 4 n) by zcell;
      assert (C40' : cellA X (t + 2800 + 40) 8 f1) by zcell; assert (C48' : cellA X (t + 2800 + 48) 8 f2) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
    zlhu4 F_55a24 D_55a24 (m + 2) Chi'.
    zlwu F_55a28 D_55a28 (m + 4) Cn'.
    zld F_55a2c D_55a2c (t + 2800 + 48) C48'.
    zld F_55a30 D_55a30 (t + 2800 + 40) C40'.
    zstep F_55a34 D_55a34.
    stepn F_55a38 D_55a38. rwH. rewrite (art_zb_or4 0 n) by lia. rewrite Z.lor_0_l.
    zstep F_55a3c D_55a3c. zstep F_55a40 D_55a40.
    zsd F_55a44 D_55a44 (t + 2800 + 40) (f1 + 1) ltac:(zwok').
    zsd F_55a48 D_55a48 (t + 2800 + 48) (n + f2) ltac:(zwok').
    unfold art_cbr_stats_mem. apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; exact H2]|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_tailp : forall regs (M rom : word -> option byte) (raw : word) (sp cb cache spb c szi g8 g9 g18 g19 g20 : Z),
  let ab := spb + c * 2 ^ 32 + szi in
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 8 = Z_to_bv 64 cb -> getr regs 18 = Z_to_bv 64 ab -> getr regs 19 = Z_to_bv 64 1321624 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  48 <= sp -> sp < 2 ^ 64 -> 0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 1 <= c <= 30 -> 0 <= szi < 2 ^ 32 -> 0 <= cb -> cb + 8 < 2 ^ 64 ->
  cellA M (1321624 + 32) 8 spb -> cellA M cb 8 cache ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x55a9c : word) M rom) (mkst regs' (0x55d08 : word) M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 cache /\ getr regs' 11 = Z_to_bv 64 1321624
    /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 ab
    /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb cache spb c szi g8 g9 g18 g19 g20 ab H2 H8 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hc Hszi Hcb Hcb' Cspb Ccb F1 F8 F9 F18 F19 F20.
  assert (Hab : ab = spb + c * 2 ^ 32 + szi) by reflexivity. clearbody ab.
  assert (Ec : (ab - spb) * 2 ^ 27 / 2 ^ 59 = c).
  { symmetry. apply (Z.div_unique_pos ((ab - spb) * 2 ^ 27) (2 ^ 59) c (szi * 2 ^ 27)); lia. }
  eexists. split.
  { zbft F_55a4c D_55a4c.
    zld F_55a50 D_55a50 (1321624 + 32) Cspb.
    zbft F_55a54 D_55a54.
    zstep F_55a58 D_55a58.
    zbft F_55a5c D_55a5c.
    zld F_55a60 D_55a60 cb Ccb.
    zstep F_55a64 D_55a64.
    zstep F_55a68 D_55a68.
    stepn F_55a6c D_55a6c. rwH. rewrite (art_zb_srli ((ab - spb) * 2 ^ 27) 59) by lia. rewrite Ec.
    stepn F_55a70 D_55a70. stepn F_55a74 D_55a74. zcl4.
    zstep F_55a78 D_55a78.
    zld F_55a7c D_55a7c (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
    zld F_55a80 D_55a80 (sp - 16) F8. zld F_55a84 D_55a84 (sp - 24) F9. zld F_55a88 D_55a88 (sp - 32) F18. zld F_55a8c D_55a8c (sp - 40) F19. zld F_55a90 D_55a90 (sp - 48) F20.
    zstep F_55a94 D_55a94.
    stepn F_55a98 D_55a98.
    apply mst_refl. }
  split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; f_equal; lia|].
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_tails : forall regs (M rom : word -> option byte) (raw : word) (sp spb hb g8 g9 g18 g19 g20 : Z),
  getr regs 2 = Z_to_bv 64 (sp - 48) -> getr regs 18 = Z_to_bv 64 hb -> getr regs 19 = Z_to_bv 64 1321624 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  48 <= sp -> sp < 2 ^ 64 -> 0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 < hb < 2 ^ 64 -> (hb < spb \/ spb + 2 ^ 37 <= hb) ->
  cellA M (1321624 + 32) 8 spb ->
  cellA M (sp - 8) 8 (U raw) -> cellA M (sp - 16) 8 g8 -> cellA M (sp - 24) 8 g9 -> cellA M (sp - 32) 8 g18 -> cellA M (sp - 40) 8 g19 -> cellA M (sp - 48) 8 g20 ->
  exists regs', msteps ASEGS (mkst regs (0x55a9c : word) M rom) (mkst regs' (0x55ed0 : word) M rom)
    /\ getr regs' 1 = raw /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 10 = Z_to_bv 64 0x142ad8 /\ getr regs' 11 = Z_to_bv 64 0x142d48 /\ getr regs' 12 = Z_to_bv 64 hb
    /\ getr regs' 8 = Z_to_bv 64 g8 /\ getr regs' 9 = Z_to_bv 64 g9 /\ getr regs' 18 = Z_to_bv 64 g18 /\ getr regs' 19 = Z_to_bv 64 g19 /\ getr regs' 20 = Z_to_bv 64 g20
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp spb hb g8 g9 g18 g19 g20 H2 H18 H19 H20 Hsp Hsp' Hspb Hspb' Hhb Hsec Cspb F1 F8 F9 F18 F19 F20.
  destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
  - eexists. split.
    { zbft F_55a4c D_55a4c.
      zld F_55a50 D_55a50 (1321624 + 32) Cspb.
      zbtk F_55a54 D_55a54.
      zstep F_55abc D_55abc. zstep F_55ac0 D_55ac0. zstep F_55ac4 D_55ac4.
      zld F_55ac8 D_55ac8 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_55acc D_55acc (sp - 16) F8. zld F_55ad0 D_55ad0 (sp - 24) F9. zld F_55ad4 D_55ad4 (sp - 32) F18. zld F_55ad8 D_55ad8 (sp - 40) F19. zld F_55adc D_55adc (sp - 48) F20.
      zstep F_55ae0 D_55ae0.
      stepn F_55ae4 D_55ae4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zbft F_55a4c D_55a4c.
      zld F_55a50 D_55a50 (1321624 + 32) Cspb.
      zbft F_55a54 D_55a54.
      zstep F_55a58 D_55a58.
      zbtk F_55a5c D_55a5c.
      zstep F_55abc D_55abc. zstep F_55ac0 D_55ac0. zstep F_55ac4 D_55ac4.
      zld F_55ac8 D_55ac8 (sp - 8) F1. rewrite Z_to_bv_bv_unsigned.
      zld F_55acc D_55acc (sp - 16) F8. zld F_55ad0 D_55ad0 (sp - 24) F9. zld F_55ad4 D_55ad4 (sp - 32) F18. zld F_55ad8 D_55ad8 (sp - 40) F19. zld F_55adc D_55adc (sp - 48) F20.
      zstep F_55ae0 D_55ae0.
      stepn F_55ae4 D_55ae4.
      apply mst_refl. }
    split; [gres; reflexivity|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_sa : forall regs (M rom : word -> option byte) (raw : word) (sp cb m spb : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  0x69c000 + 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 -> 0 <= cb < 2 ^ 64 -> 0 <= m < 2 ^ 64 ->
  0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> (m < spb \/ spb + 2 ^ 37 <= m) ->
  cellA M (1321624 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x55904 : word) M rom) (mkst regs' (0x55b88 : word) (art_f48 M sp raw regs) rom)
    /\ getr regs' 1 = (0x5597c : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 48) /\ getr regs' 8 = Z_to_bv 64 cb /\ getr regs' 9 = Z_to_bv 64 m
    /\ getr regs' 19 = Z_to_bv 64 1321624 /\ getr regs' 20 = Z_to_bv 64 (2 ^ 37) /\ getr regs' 10 = Z_to_bv 64 0x142ad8 /\ getr regs' 11 = Z_to_bv 64 m
    /\ (forall r : reg, In r [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom raw sp cb m spb H1 H2 H10 H11 Hsp Hsp' W Hcb Hm Hspb Hspb' Hsec Cspb.
  destruct (Z_lt_le_dec m spb) as [Lo|Hi].
  - eexists. split.
    { zstep F_558b4 D_558b4.
      zsd F_558b8 D_558b8 (sp - 8) (U raw) ltac:(rewok W). zsd F_558bc D_558bc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_558c0 D_558c0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_558c4 D_558c4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_558c8 D_558c8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_558cc D_558cc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_558d0 D_558d0. zstep F_558d4 D_558d4.
      stepn F_558d8 D_558d8. stepn F_558dc D_558dc. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1321624 + 32) 8 spb) by zcell end.
      zld F_558e0 D_558e0 (1321624 + 32) Cspb'.
      zstep F_558e4 D_558e4. zstep F_558e8 D_558e8.
      zbtk F_558ec D_558ec.
      zstep F_55920 D_55920. zstep F_55924 D_55924.
      stepn F_55928 D_55928.
      unfold art_f48. apply mst_refl. }
    split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_558b4 D_558b4.
      zsd F_558b8 D_558b8 (sp - 8) (U raw) ltac:(rewok W). zsd F_558bc D_558bc (sp - 16) (U (getr regs 8)) ltac:(rewok W).
      zsd F_558c0 D_558c0 (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_558c4 D_558c4 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
      zsd F_558c8 D_558c8 (sp - 40) (U (getr regs 19)) ltac:(rewok W). zsd F_558cc D_558cc (sp - 48) (U (getr regs 20)) ltac:(rewok W).
      zstep F_558d0 D_558d0. zstep F_558d4 D_558d4.
      stepn F_558d8 D_558d8. stepn F_558dc D_558dc. zcl4.
      match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cspb' : cellA X (1321624 + 32) 8 spb) by zcell end.
      zld F_558e0 D_558e0 (1321624 + 32) Cspb'.
      zstep F_558e4 D_558e4. zstep F_558e8 D_558e8.
      zbft F_558ec D_558ec.
      zstep F_558f0 D_558f0.
      zbtk F_558f4 D_558f4.
      zstep F_55920 D_55920. zstep F_55924 D_55924.
      stepn F_55928 D_55928.
      unfold art_f48. apply mst_refl. }
    split; [gres; bveq|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
    split; [gres; f_equal; lia|]. split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.

#[using="Type"] Lemma art_cbr_sb : forall regs (M rom : word -> option byte) (spb hb : Z),
  getr regs 10 = Z_to_bv 64 hb -> getr regs 19 = Z_to_bv 64 1321624 -> getr regs 20 = Z_to_bv 64 (2 ^ 37) ->
  0x69c000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= hb < 2 ^ 64 -> (hb < spb \/ spb + 2 ^ 37 <= hb) ->
  cellA M (1321624 + 32) 8 spb ->
  exists regs', msteps ASEGS (mkst regs (0x5597c : word) M rom) (mkst regs' (0x55a70 : word) M rom)
    /\ getr regs' 18 = Z_to_bv 64 hb
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom spb hb H10 H19 H20 Hspb Hspb' Hhb Hsec Cspb.
  destruct (Z_lt_le_dec hb spb) as [Lo|Hi].
  - eexists. split.
    { zstep F_5592c D_5592c.
      zld F_55930 D_55930 (1321624 + 32) Cspb.
      zstep F_55934 D_55934.
      zbft F_55938 D_55938.
      stepn F_5593c D_5593c.
      apply mst_refl. }
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
  - eexists. split.
    { zstep F_5592c D_5592c.
      zld F_55930 D_55930 (1321624 + 32) Cspb.
      zstep F_55934 D_55934.
      zbtk F_55938 D_55938.
      zbtk F_559a4 D_559a4.
      apply mst_refl. }
    split; [gres; reflexivity|].
    intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; reflexivity|]). destruct Hr.
Qed.
End FPX.

Lemma art_cbr_stats_mem_facts : forall M sp1 t n f1 f2, 32 <= sp1 -> sp1 < 2 ^ 64 -> 0 <= t -> t + 4096 < 2 ^ 64 ->
  mem_grows M (art_cbr_stats_mem M sp1 t n f1 f2) /\ art_agree [(sp1 - 32, 32); (t + 2800 + 40, 16)] M (art_cbr_stats_mem M sp1 t n f1 f2).
Proof. intros M sp1 t n f1 f2 H1 H2 H3 H4. unfold art_cbr_stats_mem. split; [zgrows|]. eapply art_agree_sub; [zagree|]. zsub. Qed.

Lemma art_poison_mem_facts : forall M sp ra s0 s1 s2 s3 s4 s5 a k v, 64 <= sp -> sp < 2 ^ 64 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
  let M' := Wf (art_poison_frame M sp ra s0 s1 s2 s3 s4 s5) a k v in
  mem_grows M M' /\ art_agree [(sp - 64, 64); (a, Z.of_nat k)] M M'.
Proof.
  intros M sp ra s0 s1 s2 s3 s4 s5 a k v H1 H2 H3 H4 M'. unfold M', art_poison_frame. split; [zgrows|].
  eapply art_agree_sub; [eapply art_agree_trans; [|apply art_agree_Wf; [exact H3|exact H4]]; zagree|]. zsub.
Qed.
