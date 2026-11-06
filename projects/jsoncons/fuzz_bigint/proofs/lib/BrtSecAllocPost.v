(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac BrtLeaf BrtAllocG BrtDepotA BrtSecAlloc ArtSizeLog BrtPoison BrtPoisonRun BrtPoison2 BrtFp.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import Bo0_code_4183c_42d28 Bo0_code_735bc_737bc Bo0_code_71dc0_71df8 Bo0_code_6dcc4_6dd2c
     Bo0_code_7be7c_7be8c Bo0_code_73aec_73c7c Bo0_code_7418c_74398 Bo0_code_68c30_68c68.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma zdiv8_mul : forall x, x mod 8 = 0 -> x / 8 * 8 = x.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). lia. Qed.
Lemma zdiv8_up7 : forall x, x mod 8 = 0 -> (x + 7) / 8 * 8 = x.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)). lia. Qed.
Lemma mod8_add : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.
Ltac mod8 := first [ assumption | reflexivity | apply mod8_add; mod8 ].
Lemma mod8_of_4096 : forall r, r mod 4096 = 0 -> r mod 8 = 0.
Proof. intros r Hr4. apply (proj2 (Z.mod_divide r 8 ltac:(lia))). apply (Z.divide_trans 8 4096 r); [exists 512; reflexivity | apply (proj1 (Z.mod_divide r 4096 ltac:(lia))); exact Hr4]. Qed.
(* [comment removed for export] *)
Ltac zdef u e RNG :=
  let E := fresh "E" u in let R := fresh "R" u in
  pose (u := e); assert (E : u = e) by reflexivity; clearbody u;
  assert (R : 0 <= u < 2 ^ 64) by (rewrite E; RNG).
Ltac divfacts x d := pose proof (Z.div_mod x d ltac:(lia)); pose proof (Z.mod_pos_bound x d ltac:(lia)).
Ltac gresH H := repeat first [ rewrite getr_same in H by reg_neq_tac | rewrite getr_other in H by reg_neq_tac ]; rewrite ?getr_zero in H.
Ltac nlit := let E := fresh in intros E; discriminate E.
Ltac pk := unfold art_poison_kept; repeat split; nlit.

(* [comment removed for export] *)
Lemma art_layout_agree : forall M M' : word -> option byte,
  (forall x : word, U x < 0x634000 -> M' x = M x) -> art_layout M -> art_layout M'.
Proof.
  intros M M' AG L. unfold art_layout in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- cell _ _ ?c ?m _ => apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | tauto] end.
Qed.
Lemma art_tsd_agree : forall (M M' : word -> option byte) tp key tsd ctx t,
  (forall x : word, U x < 0x634000 -> M' x = M x) -> (forall x : word, ctx + 152 <= U x < ctx + 160 -> M' x = M x) ->
  tp < 0x634000 -> tsd + 8 * key + 8 <= 0x634000 ->
  art_tsd M tp key tsd ctx t -> art_tsd M' tp key tsd ctx t.
Proof.
  intros M M' tp key tsd ctx t AG AGc Htp Htsd T. unfold art_tsd in *.
  destruct T as (C1 & C2 & C3 & C4 & C5 & REST).
  repeat match goal with |- _ /\ _ => split end; try lia.
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C1].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C2].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C3].
  - apply (cell_agree M M'); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C4].
  - apply (cell_agree M M'); [intros x Hx; apply AGc; cbn in Hx; lia | lia | cbn; lia | exact C5].
Qed.

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
Lemma sec_h1_fn : forall regs (M rom : word -> option byte) (s sec stat msz n r F : Z),
  getr regs 1 = Z_to_bv 64 0x73734 -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 10 = Z_to_bv 64 r -> getr regs 19 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 8 -> getr regs 24 = Z_to_bv 64 7 ->
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> n + 4096 <= msz -> 4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> 0x10000 <= stat -> stat + 64 < 0x634000 -> 0x10000 <= F -> F + 512 < 0x634000 ->
  wrA M (s - 464) 464 ->
  cellA M (s - 104) 8 0x420dc -> cellA M (s - 112) 8 stat -> cellA M (s - 120) 8 sec -> cellA M (s - 128) 8 msz ->
  cellA M sec 8 4096 -> cellA M 0xd64b8 8 F -> cellA M (F + 144) 8 0 ->
  msteps ASEGS (mkst regs (0x71de8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x42134)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 stat)) 9 (Z_to_bv 64 sec)) 10 (Z_to_bv 64 r)) 11 (Z_to_bv 64 4096)) 12 (Z_to_bv 64 250))
             13 (Z_to_bv 64 18446744073709547521)) 18 (Z_to_bv 64 msz)) 20 (Z_to_bv 64 r)) 21 (Z_to_bv 64 (4096 + r + n))) 22 (Z_to_bv 64 (msz + r))) 23 (Z_to_bv 64 (4096 + r + n))) 25 (Z_to_bv 64 (4096 + r)))
          (0x611f8 : word) (Wn 4 M (s - 136) 18446744072277895850) rom).
Proof.
  intros regs M rom s sec stat msz n r F H1 H2 H10 H19 H21 H24 Hs Hs' Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hst Hst' HF HF' W C104 C112 C120 C128 Cpg C38 C144.
  pose proof (mod8_of_4096 r Hr4) as Hr8.
  stepret F_71de8 D_71de8 (Z_to_bv 64 0x73734 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zstep F_73734 D_73734.                                                         (* [comment removed for export] *)
  zstep F_73738 D_73738.                                                         (* [comment removed for export] *)
  stepn F_7373c D_7373c.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.                                  (* [comment removed for export] *)
  zbtk F_71dc8 D_71dc8.                                                          (* [comment removed for export] *)
  zstep F_71dd8 D_71dd8.                                                         (* [comment removed for export] *)
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73740 : word) ltac:(rwH; reflexivity).
  zstep F_73740 D_73740. zstep F_73744 D_73744.                                  (* [comment removed for export] *)
  zsw F_73748 D_73748 (s - 136) 18446744072277895850 ltac:(rewok W).             (* [comment removed for export] *)
  zstep F_7374c D_7374c. zstep F_73750 D_73750.                                  (* [comment removed for export] *)
  stepn F_73754 D_73754.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73758 : word) ltac:(rwH; reflexivity).
  zbft F_73758 D_73758.                                                          (* [comment removed for export] *)
  stepn F_7375c D_7375c.                                                         (* [comment removed for export] *)
  stepn F_73760 D_73760.                                                         (* [comment removed for export] *)
  zstep F_6dcc4 D_6dcc4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0xd64b8 8 F) by zcell; assert (C144' : cellA X (F + 144) 8 0) by zcell end.
  zld F_6dcc8 D_6dcc8 0xd64b8 C38'.
  zld F_6dccc D_6dccc (F + 144) C144'.
  zbtk F_6dcd0 D_6dcd0.                                                          (* [comment removed for export] *)
  stepret F_6dcec D_6dcec (Z_to_bv 64 0x73764 : word) ltac:(rwH; reflexivity).
  zstep F_73764 D_73764.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x420dc) by zcell; assert (R2 : cellA X (s - 112) 8 stat) by zcell;
    assert (R3 : cellA X (s - 120) 8 sec) by zcell; assert (R4 : cellA X (s - 128) 8 msz) by zcell; assert (Cpg' : cellA X sec 8 4096) by zcell end.
  zld F_73768 D_73768 (s - 104) R1. zld F_7376c D_7376c (s - 112) R2. zld F_73770 D_73770 (s - 120) R3. zld F_73774 D_73774 (s - 128) R4.
  zstep F_73778 D_73778.                                                         (* [comment removed for export] *)
  stepret F_7377c D_7377c (Z_to_bv 64 0x420dc : word) ltac:(rwH; reflexivity).
  zbft F_420dc D_420dc.                                                          (* [comment removed for export] *)
  zstep F_420e0 D_420e0.                                                         (* [comment removed for export] *)
  zld F_420e4 D_420e4 sec Cpg'.                                                  (* [comment removed for export] *)
  zstep F_420e8 D_420e8.                                                         (* [comment removed for export] *)
  stepn F_420ec D_420ec. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  replace (Z.land 4095 r) with 0 by (rewrite Z.land_comm; rewrite Z.land_ones with (n := 12); [|lia]; change (2 ^ 12) with 4096; lia).
  zbft F_420f0 D_420f0.                                                          (* [comment removed for export] *)
  zstep F_420f4 D_420f4. zstep F_420f8 D_420f8.                                  (* [comment removed for export] *)
  stepn F_420fc D_420fc. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  replace (Z.land (4096 + r) 7) with 0 by (rewrite Z.land_ones with (n := 3); [|lia]; change (2 ^ 3) with 8; rewrite Z.add_mod, Hr8 by lia; reflexivity).
  zstep F_42100 D_42100. zstep F_42104 D_42104. zstep F_42108 D_42108.           (* [comment removed for export] *)
  zstep F_4210c D_4210c.                                                         (* [comment removed for export] *)
  zstep F_42110 D_42110. zstep F_42114 D_42114. zstep F_42118 D_42118.           (* [comment removed for export] *)
  stepn F_4211c D_4211c. rwH. unfold v_andi. rewrite (art_u_lit (4096 + r + n)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.   (* [comment removed for export] *)
  rewrite zdiv8_mul by mod8.
  stepn F_42120 D_42120. rwH. unfold v_andi. rewrite (art_u_lit (4096 + r + 7)) by lia. change (bv_wrap 64 (-8)) with 18446744073709551608. rewrite art_land_m8 by lia.   (* [comment removed for export] *)
  rewrite zdiv8_up7 by mod8.
  zstep F_42124 D_42124. zstep F_42128 D_42128. zstep F_4212c D_4212c.           (* [comment removed for export] *)
  stepn F_42130 D_42130.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
Lemma sec_h3_run : forall regs (M rom : word -> option byte) (s sec msz n r thr C D nch : Z),
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 9 = Z_to_bv 64 sec -> getr regs 10 = Z_to_bv 64 thr -> getr regs 18 = Z_to_bv 64 msz -> getr regs 19 = Z_to_bv 64 n ->
  getr regs 20 = Z_to_bv 64 r -> getr regs 21 = Z_to_bv 64 (4096 + r + n) -> getr regs 22 = Z_to_bv 64 (msz + r) -> getr regs 24 = Z_to_bv 64 7 -> getr regs 25 = Z_to_bv 64 (4096 + r) ->
  0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> n + 4096 <= msz -> 4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> (sec + 616) mod 4 = 0 -> 4096 <= thr -> thr + 4096 < 2 ^ 64 -> 0 <= C -> C < 2 ^ 64 -> 0 <= D -> D < 2 ^ 64 -> 0 <= nch < 2 ^ 20 ->
  apart (thr + 72) 16 r 32 -> apart (thr + 72) 16 sec 1024 -> 0x634000 <= r ->
  cellA M (thr + 72) 8 C -> cellA M (thr + 80) 8 D -> cellA M sec 8 4096 -> cellA M (sec + 616) 4 0 -> cellA M (sec + 56) 8 nch ->
  wrA M (thr + 72) 16 -> wrA M r 32 -> wrA M (sec + 616) 4 ->
  exists regs', msteps ASEGS (mkst regs (0x42148 : word) M rom)
     (mkst regs' (0x421d8 : word) (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (thr + 72) (C + 1)) (thr + 80) (D + msz)) r r) (r + 8) msz) (r + 16) n) (sec + 616) 1) rom)
  /\ getr regs' 10 = Z_to_bv 64 (4096 + r) /\ getr regs' 13 = Z_to_bv 64 nch /\ getr regs' 21 = Z_to_bv 64 r /\ getr regs' 2 = Z_to_bv 64 (s - 96)
  /\ (forall rg : reg, rg <> 10%bv -> rg <> 11%bv -> rg <> 12%bv -> rg <> 13%bv -> rg <> 14%bv -> rg <> 15%bv -> rg <> 16%bv -> rg <> 21%bv -> getr regs' rg = getr regs rg).
Proof.
  intros regs M rom s sec msz n r thr C D nch H2 H9 H10 H18 H19 H20 H21 H22 H24 H25 Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hsec8 Ht Ht' HC HC' HD HD' Hnch A1 A2 Hri
    CC CD Cpg Clk Cnch WT WR WL.
  pose proof (mod8_of_4096 r Hr4) as Hr8.
  eexists. split; [|split; [|split; [|split; [|split]]]].
  - zld F_42148 D_42148 (thr + 72) CC.                                          (* [comment removed for export] *)
    zld F_4214c D_4214c (thr + 80) CD.                                          (* [comment removed for export] *)
    stepn F_42150 D_42150. rwH. rewrite art_zb_and by lia.                      (* [comment removed for export] *)
    replace (Z.land (4096 + r) 7) with 0 by (rewrite Z.land_ones with (n := 3); [|lia]; change (2 ^ 3) with 8; rewrite Z.add_mod, Hr8 by lia; reflexivity).
    zstep F_42154 D_42154. zstep F_42158 D_42158.                               (* [comment removed for export] *)
    zsd F_4215c D_4215c (thr + 72) (C + 1) ltac:(rewok WT).                     (* [comment removed for export] *)
    zsd F_42160 D_42160 (thr + 80) (D + msz) ltac:(rewok WT).                   (* [comment removed for export] *)
    zbft F_42164 D_42164.                                                       (* [comment removed for export] *)
    zstep F_42168 D_42168.                                                      (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cpg' : cellA X sec 8 4096) by zcell end.
    zld F_4216c D_4216c sec Cpg'.                                               (* [comment removed for export] *)
    zstep F_42170 D_42170.                                                      (* [comment removed for export] *)
    stepn F_42174 D_42174. rwH. rewrite art_zb_and by lia.                      (* [comment removed for export] *)
    replace (Z.land 4095 (4096 + r)) with 0 by (rewrite Z.land_comm; rewrite Z.land_ones with (n := 12); [|lia]; change (2 ^ 12) with 4096; rewrite Z.add_mod, Hr4 by lia; reflexivity).
    zbft F_42178 D_42178.                                                       (* [comment removed for export] *)
    zbft F_4217c D_4217c.                                                       (* [comment removed for export] *)
    zbft F_42180 D_42180.                                                       (* [comment removed for export] *)
    zstep F_42184 D_42184.                                                      (* [comment removed for export] *)
    replace (4096 + r - 4096) with r by lia.
    zsd F_42188 D_42188 r r ltac:(rewok WR).                                    (* [comment removed for export] *)
    zsd F_4218c D_4218c (r + 8) msz ltac:(rewok WR).                            (* [comment removed for export] *)
    zsd F_42190 D_42190 (r + 16) n ltac:(rewok WR).                             (* [comment removed for export] *)
    zbft F_42194 D_42194.                                                       (* [comment removed for export] *)
    zstep F_42198 D_42198. zstep F_4219c D_4219c.                               (* [comment removed for export] *)
    stepn F_421a0 D_421a0. rwH. unfold v_andi. rewrite (art_u_lit (sec + 616)) by lia. change (bv_wrap 64 (-4)) with 18446744073709551612.   (* [comment removed for export] *)
    change 18446744073709551612 with (2 ^ 64 - 2 ^ 2). rewrite sa_land_down by lia. change (2 ^ 2) with 4. rewrite Hsec8, Z.sub_0_r.
    zstep F_421a4 D_421a4.                                                      (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Clk' : cellA X (sec + 616) 4 0) by zcell; assert (WL' : wokA X (sec + 616) 4) by (rewok WL) end.
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (sec + 616)) _ (Z_to_bv 64 0));
        [exact F_421a8 | reflexivity | exact D_421a8 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hsec8
        | exact Clk' | apply art_bytes4; lia ]
      | ]. wpc. rewrite art_v_lw_small by lia.
    (* [comment removed for export] *)
    chain_step; [reflexivity | eapply art_step_addi_r; [exact F_421ac | reflexivity | exact D_421ac | reflexivity] | ]. wpc. gres. rwH.
    match goal with |- context [v_addi ?x (bv_signed ?i)] => replace (v_addi x (bv_signed i)) with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_421b0 | reflexivity | exact D_421b0 | reflexivity] | ]. wpc. gres. rewrite art_zb_xor by lia. change (Z.lxor 0 1) with 1.
    (* [comment removed for export] *)
    chain_step; [reflexivity | eapply art_step_and_r; [exact F_421b4 | reflexivity | exact D_421b4 | reflexivity] | ]. wpc. gres. rwH. rewrite art_zb_and by lia. change (Z.land 1 255) with 1.
    (* [comment removed for export] *)
    chain_step; [reflexivity | eapply art_step_xor_r; [exact F_421b8 | reflexivity | exact D_421b8 | reflexivity] | ]. wpc. gres. rewrite art_zb_xor by lia. change (Z.lxor 0 1) with 1.
    (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (sec + 616)));
        [exact F_421bc | reflexivity | exact D_421bc | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hsec8 | gres; reflexivity
        | exact WL' ]
      | ]. wpc.
    change (wbytes ?M0 (Z_to_bv 64 (sec + 616)) (word_to_le_bytes 4 (Z_to_bv 64 1))) with (Wn 4 M0 (sec + 616) 1).
    zbft F_421c0 D_421c0.                                                       (* [comment removed for export] *)
    zstep F_421c4 D_421c4.                                                      (* [comment removed for export] *)
    zbft F_421c8 D_421c8.                                                       (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cnch' : cellA X (sec + 56) 8 nch) by zcell end.
    zld F_421cc D_421cc (sec + 56) Cnch'.                                       (* [comment removed for export] *)
    stepn F_421d0 D_421d0. rwH. rewrite art_zb_srli by lia.                     (* [comment removed for export] *)
    replace (nch / 2 ^ 20) with 0 by (symmetry; apply Z.div_small; lia).
    zbft F_421d4 D_421d4.                                                       (* [comment removed for export] *)
    apply mst_refl.
  - kept_solve. - kept_solve. - kept_solve. - kept_solve.
  - intros rg N10 N11 N12 N13 N14 N15 N16 N21. kept_solve.
Qed.

(* [comment removed for export] *)
Lemma sec_sl_run : forall regs (M rom : word -> option byte) (msz sec nres : Z),
  getr regs 18 = Z_to_bv 64 msz -> getr regs 9 = Z_to_bv 64 sec -> 2 ^ 12 <= msz < 2 ^ 47 -> 4096 <= sec -> sec + 1024 < 2 ^ 64 -> 0 <= nres < 2 ^ 64 ->
  cellA M (sec + 48) 8 nres ->
  exists regs', msteps ASEGS (mkst regs (0x421d8 : word) M rom) (mkst regs' (0x42280 : word) M rom)
    /\ getr regs' 19 = Z_to_bv 64 (63 - Z.log2 msz) /\ getr regs' 14 = Z_to_bv 64 nres
    /\ (forall rg : reg, rg <> 11%bv -> rg <> 12%bv -> rg <> 14%bv -> rg <> 15%bv -> rg <> 16%bv -> rg <> 19%bv -> getr regs' rg = getr regs rg).
Proof.
  intros regs M rom msz sec nres H18 H9 Hm Hs Hs' Hn C48.
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  (* [comment removed for export] *)
  divfacts msz (2 ^ 1). zdef S1 (Z.lor msz (msz / 2 ^ 1)) ltac:(apply lor_range64; lia).
  divfacts S1 (2 ^ 2).  zdef S2 (Z.lor S1 (S1 / 2 ^ 2)) ltac:(apply lor_range64; lia).
  divfacts S2 (2 ^ 4).  zdef S3 (Z.lor S2 (S2 / 2 ^ 4)) ltac:(apply lor_range64; lia).
  divfacts S3 (2 ^ 8).  zdef S4 (Z.lor S3 (S3 / 2 ^ 8)) ltac:(apply lor_range64; lia).
  divfacts S4 (2 ^ 16). zdef S5 (Z.lor S4 (S4 / 2 ^ 16)) ltac:(apply lor_range64; lia).
  divfacts S5 (2 ^ 32). zdef S6 (Z.lor S5 (S5 / 2 ^ 32)) ltac:(apply lor_range64; lia).
  assert (SM : S6 = 2 ^ (Z.log2 msz + 1) - 1).
  { rewrite <- smear_eq by lia. unfold smear, smear5, smear4, smear3, smear2, smear1. cbv zeta. subst S1 S2 S3 S4 S5 S6. reflexivity. }
  (* [comment removed for export] *)
  zdef y (2 ^ 64 - 1 - S6) ltac:(lia).
  pose proof (slpop_ranges y ltac:(lia)) as PR. cbv zeta in PR. unfold C55, C33, C0F in PR.
  destruct PR as (PR1 & PR2 & PR3 & PR4 & PR5 & PR6 & PR7 & PR8 & PR9 & PR10).
  zdef t2 (Z.land (y / 2 ^ 1) 6148914691236517205) ltac:(lia). rewrite <- Et2 in *.
  zdef t3 (y - t2) ltac:(lia). rewrite <- Et3 in *.
  zdef t5 (Z.land t3 3689348814741910323) ltac:(lia). rewrite <- Et5 in *.
  zdef t6 (Z.land (t3 / 2 ^ 2) 3689348814741910323) ltac:(lia). rewrite <- Et6 in *.
  zdef t7 (t5 + t6) ltac:(lia). rewrite <- Et7 in *.
  zdef t9 (t7 + t7 / 2 ^ 4) ltac:(lia). rewrite <- Et9 in *.
  zdef t10 (Z.land t9 1085102592571150095) ltac:(lia). rewrite <- Et10 in *.
  zdef t11 ((t10 * 72340172838076673) mod 2 ^ 64) ltac:(apply Z.mod_pos_bound; lia).
  assert (SL : t11 / 2 ^ 56 = 63 - Z.log2 msz).
  { rewrite <- (slpop_tab (Z.log2 msz)) by lia. rewrite <- SM. unfold slpop, C55, C33, C0F, C01. cbv zeta. subst. reflexivity. }
  eexists. split; [|split; [|split]].
  - stepn F_421d8 D_421d8. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    zstep F_421dc D_421dc. zstep F_421e0 D_421e0. zstep F_421e4 D_421e4.           (* [comment removed for export] *)
    stepn F_421e8 D_421e8. rwH. rewrite art_zb_or by lia. rewrite <- ES1.          (* [comment removed for export] *)
    zstep F_421ec D_421ec. zstep F_421f0 D_421f0. zstep F_421f4 D_421f4.           (* [comment removed for export] *)
    stepn F_421f8 D_421f8. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_421fc D_421fc. rwH. rewrite art_zb_or by lia. rewrite <- ES2.          (* [comment removed for export] *)
    zstep F_42200 D_42200. zstep F_42204 D_42204. zstep F_42208 D_42208. zstep F_4220c D_4220c. zstep F_42210 D_42210. zstep F_42214 D_42214.  (* [comment removed for export] *)
    stepn F_42218 D_42218. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_4221c D_4221c. rwH. rewrite art_zb_or by lia. rewrite <- ES3.
    stepn F_42220 D_42220. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_42224 D_42224. rwH. rewrite art_zb_or by lia. rewrite <- ES4.
    stepn F_42228 D_42228. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_4222c D_4222c. rwH. rewrite art_zb_or by lia. rewrite <- ES5.
    stepn F_42230 D_42230. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_42234 D_42234. rwH. rewrite art_zb_or by lia. rewrite <- ES6.
    stepn F_42238 D_42238. rwH. rewrite art_zb_xori_m1 by lia. rewrite <- Ey.      (* [comment removed for export] *)
    stepn F_4223c D_4223c. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_42240 D_42240. rwH. rewrite art_zb_and by lia. rewrite <- Et2.         (* [comment removed for export] *)
    zstep F_42244 D_42244.                                                          (* [comment removed for export] *)
    stepn F_42248 D_42248. rwH. rewrite art_zb_sub. rewrite <- Et3.                (* [comment removed for export] *)
    stepn F_4224c D_4224c. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_42250 D_42250. rwH. rewrite art_zb_and by lia. rewrite <- Et5.         (* [comment removed for export] *)
    stepn F_42254 D_42254. rwH. rewrite art_zb_and by lia. rewrite <- Et6.         (* [comment removed for export] *)
    zld F_42258 D_42258 (sec + 48) C48.                                             (* [comment removed for export] *)
    zstep F_4225c D_4225c.                                                          (* [comment removed for export] *)
    stepn F_42260 D_42260. rwH. rewrite art_zb_add. rewrite <- Et7.                (* [comment removed for export] *)
    stepn F_42264 D_42264. rwH. rewrite art_zb_srli by lia.                        (* [comment removed for export] *)
    stepn F_42268 D_42268. rwH. rewrite art_zb_add. rewrite <- Et9.                (* [comment removed for export] *)
    zstep F_4226c D_4226c.                                                          (* [comment removed for export] *)
    stepn F_42270 D_42270. rwH. rewrite art_zb_and by lia. rewrite <- Et10.        (* [comment removed for export] *)
    zstep F_42274 D_42274.                                                          (* [comment removed for export] *)
    stepn F_42278 D_42278. rwH. rewrite art_zb_mul.                                (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (t10 * ?c)] =>
      replace (Z_to_bv 64 (t10 * c) : word) with (Z_to_bv 64 ((t10 * c) mod 2 ^ 64) : word) by (apply art_zb_eq; rewrite Z.mod_mod by lia; reflexivity) end.
    rewrite <- Et11.
    stepn F_4227c D_4227c. rwH. rewrite art_zb_srli by lia. rewrite SL.            (* [comment removed for export] *)
    apply mst_refl.
  - kept_solve. - kept_solve.
  - intros rg N11 N12 N14 N15 N16 N19. kept_solve.
Qed.

(* [comment removed for export] *)
Definition sec_mx (mx cur msz : Z) : Z := if (cur + msz) mod 2 ^ 64 <? mx then mx else (cur + msz) mod 2 ^ 64.

Definition sec_tail_mem (M : word -> option byte) (sec stat r msz nch pab na cur mx lg bsl st16 st24 : Z) : word -> option byte :=
  Wn 1 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 (Wn 8 (Wn 8 (Wn 8 M
    (r + 24) nch) (pab + 8 * nch) r) (sec + 56) (nch + 1)) (sec + 64) 0) (sec + 72) (na + 1)) (sec + 88) (cur + msz)) (sec + 96) (sec_mx mx cur msz))
    (sec + 104 + 8 * lg) (bsl + 1)) (stat + 16) (st16 + msz)) (stat + 24) (st24 + msz)) (sec + 616) 0.

Lemma sec_tail_fn : forall regs (M rom : word -> option byte) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 : word)
    (s sec stat r msz nch pab na cur mx lg bsl st16 st24 : Z),
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 stat -> getr regs 9 = Z_to_bv 64 sec -> getr regs 10 = Z_to_bv 64 (4096 + r) ->
  getr regs 13 = Z_to_bv 64 nch -> getr regs 18 = Z_to_bv 64 msz -> getr regs 19 = Z_to_bv 64 (63 - lg) -> getr regs 21 = Z_to_bv 64 r ->
  ret_ok x1 ->
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 2 ^ 12 <= msz -> 4096 <= r -> r + msz < 2 ^ 47 -> 0x634000 <= r ->
  0x10000 <= sec -> sec + 624 <= stat -> stat + 64 < 0x634000 -> stat mod 8 = 0 -> 0 <= nch < 2 ^ 20 -> 0x634000 <= pab -> pab + 8 * nch + 8 < 2 ^ 47 ->
  0 <= na -> na < 2 ^ 64 -> 0 <= cur -> cur < 2 ^ 64 -> 0 <= mx < 2 ^ 64 -> 0 <= lg <= 63 -> 0 <= bsl -> bsl < 2 ^ 64 ->
  0 <= st16 -> st16 < 2 ^ 64 -> 0 <= st24 -> st24 < 2 ^ 64 ->
  apart (pab + 8 * nch) 8 r 32 -> apart (pab + 8 * nch) 8 (s - 464) 464 -> apart r 32 (s - 464) 464 ->
  cellA M (sec + 8) 8 pab -> cellA M (sec + 72) 8 na -> cellA M (sec + 88) 8 cur -> cellA M (sec + 96) 8 mx -> cellA M (sec + 104 + 8 * lg) 8 bsl ->
  cellA M (stat + 16) 8 st16 -> cellA M (stat + 24) 8 st24 ->
  cellA M (s - 8) 8 (U x1) -> cellA M (s - 16) 8 (U x8) -> cellA M (s - 24) 8 (U x9) -> cellA M (s - 32) 8 (U x18) -> cellA M (s - 40) 8 (U x19) ->
  cellA M (s - 48) 8 (U x20) -> cellA M (s - 56) 8 (U x21) -> cellA M (s - 64) 8 (U x22) -> cellA M (s - 72) 8 (U x23) -> cellA M (s - 80) 8 (U x24) -> cellA M (s - 88) 8 (U x25) ->
  wrA M (r + 24) 8 -> wrA M (pab + 8 * nch) 8 -> wrA M sec 624 -> wrA M (stat + 16) 16 ->
  msteps ASEGS (mkst regs (0x42284 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 x1) 2 (Z_to_bv 64 s)) 8 x8) 9 x9) 11 (Z_to_bv 64 (stat + 16))) 12 (Z_to_bv 64 (sec_mx mx cur msz))) 13 (Z_to_bv 64 (bsl + 1))) 14 (Z_to_bv 64 (na + 1)))
             15 (Z_to_bv 64 cur)) 16 (Z_to_bv 64 (nch + 1))) 18 x18) 19 x19) 20 x20) 21 x21) 22 x22) 23 x23) 24 x24) 25 x25)
          x1 (sec_tail_mem M sec stat r msz nch pab na cur mx lg bsl st16 st24) rom).
Proof.
  intros regs M rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx lg bsl st16 st24
    H2 H8 H9 H10 H13 H18 H19 H21 Hret Hs Hs' Hm Hr Hrm Hri Hsec Hss Hst Hst8 Hnch Hpi Hpab' Hna Hna' Hcur Hcur' Hmx Hlg Hbsl Hbsl' H16 H16' H24 H24'
    A1 A2 A3 Cpab Cna Ccur Cmx Cbsl C16 C24 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 W1 W2 W3 W4.
  unfold sec_tail_mem.
  assert (M16 : (stat + 16) mod 8 = 0) by (rewrite Z.add_mod, Hst8 by lia; reflexivity).
  assert (M24 : (stat + 24) mod 8 = 0) by (rewrite Z.add_mod, Hst8 by lia; reflexivity).
      zld F_42284 D_42284 (sec + 8) Cpab.                                            (* [comment removed for export] *)
    stepn F_42288 D_42288; rwH; unfold v_xori; rewrite (art_u_lit (63 - lg)) by lia; change (bv_wrap 64 63) with 63; rewrite lxor_63 by lia.
    replace (63 - (63 - lg)) with lg by lia.                                       (* [comment removed for export] *)
    zsd F_4228c D_4228c (r + 24) nch ltac:(rewok W1).                              (* [comment removed for export] *)
    zstep F_42290 D_42290; zstep F_42294 D_42294.                                  (* [comment removed for export] *)
    zsd F_42298 D_42298 (pab + 8 * nch) r ltac:(rewok W2).                         (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (Cna' : cellA X (sec + 72) 8 na) by zcell; assert (Ccur' : cellA X (sec + 88) 8 cur) by zcell; assert (Cmx' : cellA X (sec + 96) 8 mx) by zcell end.
    zld F_4229c D_4229c (sec + 72) Cna'.                                           (* [comment removed for export] *)
    zld F_422a0 D_422a0 (sec + 88) Ccur'.                                          (* [comment removed for export] *)
    zstep F_422a4 D_422a4.                                                         (* [comment removed for export] *)
    zld F_422a8 D_422a8 (sec + 96) Cmx'.                                           (* [comment removed for export] *)
    zstep F_422ac D_422ac; zstep F_422b0 D_422b0.                                  (* [comment removed for export] *)
    zsd F_422b4 D_422b4 (sec + 56) (nch + 1) ltac:(rewok W3).                      (* [comment removed for export] *)
    zsb F_422b8 D_422b8 (sec + 64) 0 ltac:(rewok W3).                             (* [comment removed for export] *)
    zsd F_422bc D_422bc (sec + 72) (na + 1) ltac:(rewok W3).                       (* [comment removed for export] *)
    zsd F_422c0 D_422c0 (sec + 88) (cur + msz) ltac:(rewok W3).                    (* [comment removed for export] *)
  (* [comment removed for export] *)
  match goal with |- msteps _ ?S _ =>
    assert (BR : msteps ASEGS S ltac:(match S with mkst ?R _ ?X _ => exact (mkst (regupd R 12 (Z_to_bv 64 (sec_mx mx cur msz))) (0x422cc : word) X rom) end)) end.
  { pose proof (Z.mod_pos_bound (cur + msz) (2 ^ 64) ltac:(lia)) as Hcm.
    unfold sec_mx. rewrite <- (art_zb_mod64 (cur + msz)).
    destruct (Z.lt_ge_cases ((cur + msz) mod 2 ^ 64) mx) as [LT|GE].
    - replace ((cur + msz) mod 2 ^ 64 <? mx) with true by (symmetry; apply Z.ltb_lt; lia). zbtk F_422c4 D_422c4. zret.
    - replace ((cur + msz) mod 2 ^ 64 <? mx) with false by (symmetry; apply Z.ltb_ge; lia). zbft F_422c4 D_422c4. zstep F_422c8 D_422c8. zret. }
  eapply msteps_trans; [exact BR|]. clear BR.
    zstep F_422cc D_422cc; zstep F_422d0 D_422d0.                                  (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cbsl' : cellA X (sec + 104 + 8 * lg) 8 bsl) by zcell end.
    zld F_422d4 D_422d4 (sec + 104 + 8 * lg) Cbsl'.                               (* [comment removed for export] *)
    zstep F_422d8 D_422d8.                                                         (* [comment removed for export] *)
    zsd F_422dc D_422dc (sec + 96) (sec_mx mx cur msz) ltac:(rewok W3).          (* [comment removed for export] *)
    zsd F_422e0 D_422e0 (sec + 104 + 8 * lg) (bsl + 1) ltac:(rewok W3).            (* [comment removed for export] *)
    zstep F_422e4 D_422e4.                                                         (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C16' : cellA X (stat + 16) 8 st16) by zcell; assert (C24' : cellA X (stat + 24) 8 st24) by zcell end.
    zamoadd_d F_422e8 D_422e8 (stat + 16) st16 msz C16' ltac:(rewok W4).          (* [comment removed for export] *)
    zstep F_422ec D_422ec.                                                         (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C24'' : cellA X (stat + 24) 8 st24) by zcell end.
    zamoadd_d F_422f0 D_422f0 (stat + 24) st24 msz C24'' ltac:(rewok W4).         (* [comment removed for export] *)
    stepfence F_422f4 D_422f4.                                                     (* [comment removed for export] *)
    zsb F_422f8 D_422f8 (sec + 616) 0 ltac:(rewok W3).                            (* [comment removed for export] *)
    match goal with |- msteps _ (mkst _ _ ?X _) _ =>
      assert (L1' : cellA X (s - 8) 8 (U x1)) by zcell; assert (L2' : cellA X (s - 16) 8 (U x8)) by zcell; assert (L3' : cellA X (s - 24) 8 (U x9)) by zcell;
      assert (L4' : cellA X (s - 32) 8 (U x18)) by zcell; assert (L5' : cellA X (s - 40) 8 (U x19)) by zcell; assert (L6' : cellA X (s - 48) 8 (U x20)) by zcell;
      assert (L7' : cellA X (s - 56) 8 (U x21)) by zcell; assert (L8' : cellA X (s - 64) 8 (U x22)) by zcell; assert (L9' : cellA X (s - 72) 8 (U x23)) by zcell;
      assert (L10' : cellA X (s - 80) 8 (U x24)) by zcell; assert (L11' : cellA X (s - 88) 8 (U x25)) by zcell end.
    zld F_422fc D_422fc (s - 8) L1'; rewrite Z_to_bv_bv_unsigned.
    zld F_42300 D_42300 (s - 16) L2'; rewrite Z_to_bv_bv_unsigned.
    zld F_42304 D_42304 (s - 24) L3'; rewrite Z_to_bv_bv_unsigned.
    zld F_42308 D_42308 (s - 32) L4'; rewrite Z_to_bv_bv_unsigned.
    zld F_4230c D_4230c (s - 40) L5'; rewrite Z_to_bv_bv_unsigned.
    zld F_42310 D_42310 (s - 48) L6'; rewrite Z_to_bv_bv_unsigned.
    zld F_42314 D_42314 (s - 56) L7'; rewrite Z_to_bv_bv_unsigned.
    zld F_42318 D_42318 (s - 64) L8'; rewrite Z_to_bv_bv_unsigned.
    zld F_4231c D_4231c (s - 72) L9'; rewrite Z_to_bv_bv_unsigned.
    zld F_42320 D_42320 (s - 80) L10'; rewrite Z_to_bv_bv_unsigned.
    zld F_42324 D_42324 (s - 88) L11'; rewrite Z_to_bv_bv_unsigned.
    zstep F_42328 D_42328.                                                         (* [comment removed for export] *)
    stepret F_4232c D_4232c x1 ltac:(rwH; reflexivity).
    zret.
Qed.


(* [comment removed for export] *)
Definition sec_b1_mem (M : word -> option byte) (s stat sec msz lg r pab2 nch : Z) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M
    (s - 104) 0x4247c) (s - 112) stat) (s - 120) sec) (s - 128) msz) (s - 136) lg) (s - 144) (4096 + r)) (s - 192) 50)
    (s - 200) 0x73b88) (s - 208) 131072) (s - 216) 0) (s - 224) (pab2 + 8 * nch)) (s - 232) 0) (s - 240) 0x16e1e0) (s - 248) r.

(* [comment removed for export] *)
Lemma sec_b1_fn : forall regs (M rom : word -> option byte) (s sec stat lg nch pab2 r msz : Z),
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 8 = Z_to_bv 64 stat -> getr regs 9 = Z_to_bv 64 sec -> getr regs 10 = Z_to_bv 64 (4096 + r) ->
  getr regs 13 = Z_to_bv 64 nch -> getr regs 14 = Z_to_bv 64 nch -> getr regs 18 = Z_to_bv 64 msz -> getr regs 19 = Z_to_bv 64 lg -> getr regs 21 = Z_to_bv 64 r ->
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 4096 <= r -> r < 2 ^ 47 -> 0 <= msz < 2 ^ 47 -> 0 <= stat < 2 ^ 64 -> 0 <= lg <= 63 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> 0 <= nch < 2 ^ 20 -> 4096 <= pab2 -> pab2 + 8 * nch + 131072 < 2 ^ 47 -> (pab2 + 8 * nch) mod 4096 = 0 ->
  wrA M (s - 464) 464 ->
  cellA M (sec + 16) 8 pab2 -> cellA M 0xd64a8 8 0x16e1e0 -> cellA M 0x16e1e0 8 4096 ->
  msteps ASEGS (mkst regs (0x42280 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x73ba4)) 2 (Z_to_bv 64 (s - 192))) 8 (Z_to_bv 64 131072)) 9 (Z_to_bv 64 0)) 10 (Z_to_bv 64 (pab2 + 8 * nch))) 11 (Z_to_bv 64 131072)) 12 (Z_to_bv 64 3)) 13 (Z_to_bv 64 50))
             14 (Z_to_bv 64 18446744073709551615)) 15 (Z_to_bv 64 0)) 17 (Z_to_bv 64 222)) 18 (Z_to_bv 64 (pab2 + 8 * nch))) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 0x16e1e0)) 21 (Z_to_bv 64 r))
          (0x71de4 : word) (sec_b1_mem M s stat sec msz lg r pab2 nch) rom).
Proof.
  intros regs M rom s sec stat lg nch pab2 r msz H2 H8 H9 H10 H13 H14 H18 H19 H21 Hs Hs' Hr Hr' Hm Hst Hlg Hsec Hsec' Hnch Hpab Hpab' Hal W C16 Cg28 Cpc.
  unfold sec_b1_mem.
  zbtk F_42280 D_42280.                                                          (* [comment removed for export] *)
  zld F_42458 D_42458 (sec + 16) C16.                                            (* [comment removed for export] *)
  zstep F_4245c D_4245c. zstep F_42460 D_42460. zstep F_42464 D_42464.           (* [comment removed for export] *)
  zstep F_42468 D_42468. zstep F_4246c D_4246c. zstep F_42470 D_42470. zstep F_42474 D_42474.   (* [comment removed for export] *)
  stepn F_42478 D_42478.                                                         (* [comment removed for export] *)
  zstep F_7be7c D_7be7c. zstep F_7be80 D_7be80. zstep F_7be84 D_7be84.           (* [comment removed for export] *)
  stepn F_7be88 D_7be88.                                                         (* [comment removed for export] *)
  zstep F_73aec D_73aec. zstep F_73af0 D_73af0.                                  (* [comment removed for export] *)
  stepn F_73af4 D_73af4.                                                         (* [comment removed for export] *)
  zstep F_73af8 D_73af8.                                                         (* [comment removed for export] *)
  zsd F_73afc D_73afc (s - 104) 0x4247c ltac:(rewok W).
  zsd F_73b00 D_73b00 (s - 112) stat ltac:(rewok W).
  zsd F_73b04 D_73b04 (s - 120) sec ltac:(rewok W).
  zsd F_73b08 D_73b08 (s - 128) msz ltac:(rewok W).
  zsd F_73b0c D_73b0c (s - 136) lg ltac:(rewok W).
  zsd F_73b10 D_73b10 (s - 144) (4096 + r) ltac:(rewok W).
  zstep F_73b14 D_73b14. zstep F_73b18 D_73b18. zstep F_73b1c D_73b1c.           (* [comment removed for export] *)
  zstep F_73b20 D_73b20.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cg28' : cellA X 0xd64a8 8 0x16e1e0) by zcell; assert (Cpc' : cellA X 0x16e1e0 8 4096) by zcell end.
  zld F_73b24 D_73b24 0xd64a8 Cg28'. zld F_73b28 D_73b28 0x16e1e0 Cpc'.
  zstep F_73b2c D_73b2c.                                                         (* [comment removed for export] *)
  zbtk F_73b30 D_73b30.                                                          (* [comment removed for export] *)
  zstep F_73b40 D_73b40. zstep F_73b44 D_73b44.                                  (* [comment removed for export] *)
  zbft F_73b48 D_73b48.
  zstep F_73b4c D_73b4c. zstep F_73b50 D_73b50. zstep F_73b54 D_73b54.           (* [comment removed for export] *)
  zstep F_73b58 D_73b58.                                                         (* [comment removed for export] *)
  zbtk F_73b5c D_73b5c.                                                          (* [comment removed for export] *)
  stepn F_73b6c D_73b6c. rwH. rewrite art_zb_and by lia.                         (* [comment removed for export] *)
  change 18446744073709547520 with (2 ^ 64 - 2 ^ 12). rewrite sa_land_down by lia. change (2 ^ 12) with 4096.
  replace (nch * 2 ^ 3 + pab2) with (pab2 + 8 * nch) by lia. rewrite Hal, Z.sub_0_r.
  zstep F_73b70 D_73b70.                                                         (* [comment removed for export] *)
  zsw F_73b74 D_73b74 (s - 192) 50 ltac:(rewok W).                                 (* [comment removed for export] *)
  zstep F_73b78 D_73b78. zstep F_73b7c D_73b7c. zstep F_73b80 D_73b80.           (* [comment removed for export] *)
  stepn F_73b84 D_73b84.                                                         (* [comment removed for export] *)
  zstep F_7418c D_7418c.                                                         (* [comment removed for export] *)
  zsd F_74190 D_74190 (s - 200) 0x73b88 ltac:(rewok W).
  zsd F_74194 D_74194 (s - 208) 131072 ltac:(rewok W).
  zsd F_74198 D_74198 (s - 216) 0 ltac:(rewok W).
  zsd F_7419c D_7419c (s - 224) (pab2 + 8 * nch) ltac:(rewok W).
  zsd F_741a0 D_741a0 (s - 232) 0 ltac:(rewok W).
  zsd F_741a4 D_741a4 (s - 240) 0x16e1e0 ltac:(rewok W).
  zsd F_741a8 D_741a8 (s - 248) r ltac:(rewok W).
  zstep F_741ac D_741ac.                                                         (* [comment removed for export] *)
  zstep F_741b0 D_741b0.                                                         (* [comment removed for export] *)
  zbtk F_741b4 D_741b4.                                                          (* [comment removed for export] *)
  stepn F_742dc D_742dc.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 200) 8 0x73b88) by zcell; assert (R2 : cellA X (s - 208) 8 131072) by zcell;
    assert (R3 : cellA X (s - 216) 8 0) by zcell; assert (R4 : cellA X (s - 224) 8 (pab2 + 8 * nch)) by zcell;
    assert (R5 : cellA X (s - 232) 8 0) by zcell; assert (R6 : cellA X (s - 240) 8 0x16e1e0) by zcell;
    assert (R7 : cellA X (s - 248) 8 r) by zcell; assert (R8 : cellA X (s - 192) 4 50) by zcell end.
  zld F_742e0 D_742e0 (s - 200) R1. zld F_742e4 D_742e4 (s - 208) R2. zld F_742e8 D_742e8 (s - 216) R3. zld F_742ec D_742ec (s - 224) R4.
  zld F_742f0 D_742f0 (s - 232) R5. zld F_742f4 D_742f4 (s - 240) R6. zld F_742f8 D_742f8 (s - 248) R7.
  zstep F_742fc D_742fc.                                                         (* [comment removed for export] *)
  stepret F_74300 D_74300 (Z_to_bv 64 0x73b88 : word) ltac:(rwH; reflexivity).
  zlw F_73b88 D_73b88 (s - 192) R8.                                              (* [comment removed for export] *)
  zstep F_73b8c D_73b8c. zstep F_73b90 D_73b90. zstep F_73b94 D_73b94. zstep F_73b98 D_73b98. zstep F_73b9c D_73b9c.   (* [comment removed for export] *)
  stepn F_73ba0 D_73ba0.                                                         (* [comment removed for export] *)
  zstep F_71de0 D_71de0.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
Lemma sec_b2_fn : forall regs (M rom : word -> option byte) (s sec stat msz lg nch nres r q F : Z),
  getr regs 1 = Z_to_bv 64 0x73ba4 -> getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 8 = Z_to_bv 64 131072 -> getr regs 10 = Z_to_bv 64 q ->
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 4096 <= r -> r < 2 ^ 47 -> 0 <= msz < 2 ^ 47 -> 0 <= q < 2 ^ 64 - 4095 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> 0x10000 <= stat -> stat + 64 < 0x634000 -> 0 <= nch < 2 ^ 20 -> 0 <= nres < 2 ^ 40 -> 0 <= lg <= 63 -> 0x10000 <= F -> F + 512 < 0x634000 ->
  wrA M (s - 464) 464 -> wrA M sec 624 ->
  cellA M (s - 104) 8 0x4247c -> cellA M (s - 112) 8 stat -> cellA M (s - 120) 8 sec -> cellA M (s - 128) 8 msz -> cellA M (s - 136) 8 lg -> cellA M (s - 144) 8 (4096 + r) ->
  cellA M 0xd64b8 8 F -> cellA M (F + 144) 8 0 -> cellA M (sec + 48) 8 nres -> cellA M (sec + 56) 8 nch ->
  msteps ASEGS (mkst regs (0x71de8 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs
             1 (Z_to_bv 64 0x4247c)) 2 (Z_to_bv 64 (s - 96))) 8 (Z_to_bv 64 stat)) 9 (Z_to_bv 64 sec)) 10 (Z_to_bv 64 (4096 + r))) 11 (Z_to_bv 64 (nres + 16384))) 12 (Z_to_bv 64 16384))
             13 (Z_to_bv 64 nch)) 18 (Z_to_bv 64 msz)) 19 (Z_to_bv 64 lg)) 20 (Z_to_bv 64 (4096 + r)))
          (0x42284 : word) (Wn 8 (Wn 4 M (s - 148) 18446744072277895850) (sec + 48) (nres + 16384)) rom).
Proof.
  intros regs M rom s sec stat msz lg nch nres r q F H1 H2 H8 H10 Hs Hs' Hr Hr' Hm Hq Hsec Hsec' Hst Hst' Hnch Hnres Hlg HF HF' W W5
    C104 C112 C120 C128 C136 C144 C38 C144' Cnres Cnch.
  stepret F_71de8 D_71de8 (Z_to_bv 64 0x73ba4 : word) ltac:(rwH; reflexivity).        (* [comment removed for export] *)
  zstep F_73ba4 D_73ba4.                                                         (* [comment removed for export] *)
  zstep F_73ba8 D_73ba8.                                                         (* [comment removed for export] *)
  stepn F_73bac D_73bac.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73bb0 : word) ltac:(rwH; reflexivity).
  zstep F_73bb0 D_73bb0. zstep F_73bb4 D_73bb4.                                  (* [comment removed for export] *)
  zsw F_73bb8 D_73bb8 (s - 148) 18446744072277895850 ltac:(rewok W).             (* [comment removed for export] *)
  zstep F_73bbc D_73bbc. zstep F_73bc0 D_73bc0.                                  (* [comment removed for export] *)
  stepn F_73bc4 D_73bc4.                                                         (* [comment removed for export] *)
  zstep F_71dc0 D_71dc0. zstep F_71dc4 D_71dc4.
  zbtk F_71dc8 D_71dc8.
  zstep F_71dd8 D_71dd8.
  stepret F_71ddc D_71ddc (Z_to_bv 64 0x73bc8 : word) ltac:(rwH; reflexivity).
  zbft F_73bc8 D_73bc8.                                                          (* [comment removed for export] *)
  zstep F_73bcc D_73bcc.                                                         (* [comment removed for export] *)
  stepn F_73bd0 D_73bd0.                                                         (* [comment removed for export] *)
  zstep F_6dcc4 D_6dcc4.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (C38' : cellA X 0xd64b8 8 F) by zcell; assert (C144'' : cellA X (F + 144) 8 0) by zcell end.
  zld F_6dcc8 D_6dcc8 0xd64b8 C38'. zld F_6dccc D_6dccc (F + 144) C144''.
  zbtk F_6dcd0 D_6dcd0.
  stepret F_6dcec D_6dcec (Z_to_bv 64 0x73bd4 : word) ltac:(rwH; reflexivity).
  zstep F_73bd4 D_73bd4.                                                         (* [comment removed for export] *)
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (R1 : cellA X (s - 104) 8 0x4247c) by zcell; assert (R2 : cellA X (s - 112) 8 stat) by zcell; assert (R3 : cellA X (s - 120) 8 sec) by zcell;
    assert (R4 : cellA X (s - 128) 8 msz) by zcell; assert (R5 : cellA X (s - 136) 8 lg) by zcell; assert (R6 : cellA X (s - 144) 8 (4096 + r)) by zcell;
    assert (Cnres' : cellA X (sec + 48) 8 nres) by zcell; assert (Cnch' : cellA X (sec + 56) 8 nch) by zcell end.
  zld F_73bd8 D_73bd8 (s - 104) R1. zld F_73bdc D_73bdc (s - 112) R2. zld F_73be0 D_73be0 (s - 120) R3. zld F_73be4 D_73be4 (s - 128) R4.
  zld F_73be8 D_73be8 (s - 136) R5. zld F_73bec D_73bec (s - 144) R6.
  zstep F_73bf0 D_73bf0.                                                         (* [comment removed for export] *)
  stepret F_73bf4 D_73bf4 (Z_to_bv 64 0x4247c : word) ltac:(rwH; reflexivity).
  zstep F_4247c D_4247c.                                                         (* [comment removed for export] *)
  zld F_42480 D_42480 (sec + 48) Cnres'. zld F_42484 D_42484 (sec + 56) Cnch'.   (* [comment removed for export] *)
  zstep F_42488 D_42488. zstep F_4248c D_4248c.                                  (* [comment removed for export] *)
  zsd F_42490 D_42490 (sec + 48) (nres + 16384) ltac:(rewok W5).                (* [comment removed for export] *)
  stepn F_42494 D_42494.                                                         (* [comment removed for export] *)
  zret.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_pm1 (M1 : word -> option byte) (s stat sec msz n r : Z) : word -> option byte :=
  Wf (art_poison_frame (Wn 4 M1 (s - 136) 18446744072277895850) (s - 96) 0x42134 stat sec msz n r (4096 + r + n)) (SB + r / 8) (Z.to_nat (4096 / 8)) 250.
Definition sec_pm2 (M1 : word -> option byte) (s stat sec msz n r : Z) : word -> option byte :=
  Wf (art_poison_frame (sec_pm1 M1 s stat sec msz n r) (s - 96) 0x42144 stat sec msz n r (4096 + r + n)) (SB + (4096 + r + n) / 8) (Z.to_nat ((msz - 4096 - n) / 8)) 250.
Definition sec_hm (M1 : word -> option byte) (s stat sec msz n r t C D : Z) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (sec_pm2 M1 s stat sec msz n r) (s - 104) 0x42148) (s - 120) 0x68c3c)
     (t + 2800 + 72) (C + 1)) (t + 2800 + 80) (D + msz)) r r) (r + 8) msz) (r + 16) n) (sec + 616) 1.
Definition sec_postA_mem (M1 : word -> option byte) (s stat sec msz n r t C D nch pab na cur mx bsl st16 st24 : Z) : word -> option byte :=
  sec_tail_mem (sec_hm M1 s stat sec msz n r t C D) sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24.

(* [comment removed for export] *)
Definition appmem (a n : Z) : Prop := a + n <= SB - 4096 \/ kHighMemBeg <= a.

Lemma sec_head_run : forall regs (M1 rom : word -> option byte)
    (s sec stat msz n r F tp key tsd ctx t C D nch nres : Z),
  getr regs 1 = Z_to_bv 64 0x73734 -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 r -> getr regs 19 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 8 -> getr regs 24 = Z_to_bv 64 7 ->
  (* [comment removed for export] *)
  kHighMemBeg <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> msz mod 4096 = 0 -> n + 4096 <= msz ->
  4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 -> 0x634000 <= r -> appmem r msz -> apart r msz (s - 464) 464 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> sec + 624 <= stat -> stat + 64 < 0x634000 -> (sec + 616) mod 4 = 0 -> stat mod 8 = 0 ->
  0x10000 <= F -> F + 512 < 0x634000 ->
  ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x634000 <= t) -> t + 4096 < 2 ^ 47 -> appmem t 4096 -> apart (t + 2872) 16 r 32 -> apart (t + 2872) 16 (s - 464) 464 -> apart (t + 2872) 16 (ctx + 152) 8 ->
  0 <= C -> C < 2 ^ 64 -> 0 <= D -> D < 2 ^ 64 ->
  (* [comment removed for export] *)
  appmem ctx 4096 -> apart (ctx + 152) 8 r 32 -> apart (ctx + 152) 8 (s - 464) 464 -> 4096 <= tp - 88 -> tp < 0x634000 -> 4096 <= tsd -> tsd + 8 * key + 8 <= 0x634000 ->
  (* [comment removed for export] *)
  wrA M1 (s - 464) 464 -> wrA M1 r 32 -> wrA M1 (SB + r / 8) (msz / 8) -> wrA M1 (t + 2872) 16 -> wrA M1 sec 624 ->
  cellA M1 (s - 104) 8 0x420dc -> cellA M1 (s - 112) 8 stat -> cellA M1 (s - 120) 8 sec -> cellA M1 (s - 128) 8 msz ->
  cellA M1 sec 8 4096 -> cellA M1 0xd64b8 8 F -> cellA M1 (F + 144) 8 0 -> art_layout M1 -> art_tsd M1 tp key tsd ctx t ->
  cellA M1 (t + 2872) 8 C -> cellA M1 (t + 2880) 8 D -> cellA M1 (sec + 616) 4 0 -> cellA M1 (sec + 56) 8 nch -> cellA M1 (sec + 48) 8 nres ->
  0 <= nch < 2 ^ 20 -> 0 <= nres < 2 ^ 64 ->
  exists r7, msteps ASEGS (mkst regs (0x71de8 : word) M1 rom) (mkst r7 (0x42280 : word) (sec_hm M1 s stat sec msz n r t C D) rom)
  /\ getr r7 2 = Z_to_bv 64 (s - 96) /\ getr r7 4 = Z_to_bv 64 tp /\ getr r7 8 = Z_to_bv 64 stat /\ getr r7 9 = Z_to_bv 64 sec /\ getr r7 10 = Z_to_bv 64 (4096 + r)
  /\ getr r7 13 = Z_to_bv 64 nch /\ getr r7 14 = Z_to_bv 64 nres /\ getr r7 18 = Z_to_bv 64 msz /\ getr r7 19 = Z_to_bv 64 (63 - Z.log2 msz) /\ getr r7 21 = Z_to_bv 64 r
  /\ getr r7 3 = getr regs 3 /\ getr r7 26 = getr regs 26 /\ getr r7 27 = getr regs 27.
Proof.
  intros regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nres.
  intros H1 H2 H4 H10 H19 H21 H24.
  intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
  intros Ht Ht' APt ATr ATs ATc HC HC' HD HD'.
  intros APc ACr ACs Htp Htp' Htsd Htsd'.
  intros W1 W2 W3 W4 W5 C104 C112 C120 C128 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Hnch Hnres.
  unfold kHighMemBeg in *. 
  assert (ESB : SB = 2147450880) by reflexivity.
  pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8.
  divfacts r 8. divfacts n 8. divfacts msz 8.
  pose proof TSD as (Tc1 & Tc2 & Tc3 & Tc4 & Tc5 & Ttp & Ttp' & Tkey & Ttsd & Ttsd' & Tctx & Tctx' & Tt).
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  assert (K512 : Z.of_nat (Z.to_nat (4096 / 8)) = 512) by reflexivity.
  assert (E512 : 4096 / 8 = 512) by reflexivity.
  assert (HT8 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia). divfacts (msz - 4096 - n) 8.
  assert (MT8 : (msz - 4096 - n) mod 8 = 0) by (replace (msz - 4096 - n) with ((msz / 8 - 512 - n / 8) * 8) by lia; apply Z_mod_mult).
  assert (KT : Z.of_nat (Z.to_nat ((msz - 4096 - n) / 8)) = (msz - 4096 - n) / 8) by (apply Z2Nat.id; lia).
  assert (MU8 : (4096 + r + n) mod 8 = 0) by mod8. divfacts (4096 + r + n) 8.
  unfold appmem, kHighMemBeg in APr, APt, APc.
  assert (PO1 : art_poison_lo_ok r 4096 \/ art_poison_hi_ok r 4096).
  { clear APt APc. unfold art_poison_lo_ok, art_poison_hi_ok, kHighMemBeg, kHighMemEnd. destruct APr; [left; lia | right; lia]. }
  assert (PO2 : art_poison_lo_ok (4096 + r + n) (msz - 4096 - n) \/ art_poison_hi_ok (4096 + r + n) (msz - 4096 - n)).
  { clear APt APc. unfold art_poison_lo_ok, art_poison_hi_ok, kHighMemBeg, kHighMemEnd. destruct APr; [left; lia | right; lia]. }
  assert (ASr : apart (SB + r / 8) (msz / 8) r 32) by (clear APt APc; unfold apart; lia).
  assert (ASt : apart (SB + r / 8) (msz / 8) (t + 2872) 16) by (clear APr APc; unfold apart; lia).
  assert (ASc : apart (SB + r / 8) (msz / 8) (ctx + 152) 8) by (clear APr APt; unfold apart; lia).
  clear APr APt APc.
  (* [comment removed for export] *)
  pose proof (sec_h1_fn regs M1 rom s sec stat msz n r F H1 H2 H10 H19 H21 H24 ltac:(lia) Hs' Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' ltac:(lia) Hst HF HF'
                W1 C104 C112 C120 C128 Cpg C38 C144) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?X _) => set (r1 := R) in RUN1; set (M2 := X) in RUN1 end.
  (* [comment removed for export] *)
  assert (AG2 : forall x : word, ~ (s - 464 <= U x < s - 96) -> M2 x = M1 x).
  { intros x X1. pose proof (u64_range x). unfold M2. rewrite Wn_outside by (first [lia | cbn; lia]). reflexivity. }
  assert (LAY2 : art_layout M2) by (apply (art_layout_agree M1 M2); [intros x Hx; apply AG2; lia | exact LAY]).
  destruct (art_poison_run r1 M2 rom (Z_to_bv 64 0x42134) (s - 96) r 4096 250
              ltac:(unfold r1; gres; reflexivity) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
              ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(unfold M2; apply wr_Wn; apply (wr_sub _ _ _ _ _ _ W1); lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
              LAY2 PO1 Hr8 ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(rewrite E512; unfold M2; apply wr_Wn; apply (wr_sub _ _ _ _ _ _ W3); lia))
    as (r2 & RUN2 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & K2).
  match type of RUN2 with msteps _ _ (mkst _ _ ?X _) => assert (EQ2 : X = sec_pm1 M1 s stat sec msz n r) end.
  { unfold sec_pm1, r1, M2. gres. rewrite H19. rewrite !art_u_lit by lia. reflexivity. }
  rewrite EQ2 in RUN2. clear EQ2.
  set (PM1 := sec_pm1 M1 s stat sec msz n r) in RUN2.
  assert (AG3 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> PM1 x = M1 x).
  { intros x X1 X2. pose proof (u64_range x). unfold PM1, sec_pm1, art_poison_frame.
    rewrite Wf_outside; [ | lia | rewrite K512; lia | rewrite K512; lia ].
    rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
  assert (G3 : mem_grows M1 PM1).
  { unfold PM1, sec_pm1, art_poison_frame, M2. eapply mem_grows_trans; [ | apply Wf_grows ]. do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl. }
  (* [comment removed for export] *)
  assert (Q22 : getr r2 22 = Z_to_bv 64 (msz + r)) by (rewrite (K2 22%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q23 : getr r2 23 = Z_to_bv 64 (4096 + r + n)) by (rewrite (K2 23%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q24 : getr r2 24 = Z_to_bv 64 7) by (rewrite (K2 24%bv) by pk; unfold r1; gres; exact H24).
  assert (Q25 : getr r2 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K2 25%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q3x : getr r2 3 = getr regs 3) by (rewrite (K2 3%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q26x : getr r2 26 = getr regs 26) by (rewrite (K2 26%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q27x : getr r2 27 = getr regs 27) by (rewrite (K2 27%bv) by pk; unfold r1; gres; reflexivity).
  assert (Q4 : getr r2 4 = Z_to_bv 64 tp) by (rewrite (K2 4%bv) by pk; unfold r1; gres; exact H4).
  assert (Q8 : getr r2 8 = Z_to_bv 64 stat) by (rewrite P8; unfold r1; gres; reflexivity).
  assert (Q9 : getr r2 9 = Z_to_bv 64 sec) by (rewrite P9; unfold r1; gres; reflexivity).
  assert (Q18 : getr r2 18 = Z_to_bv 64 msz) by (rewrite P18; unfold r1; gres; reflexivity).
  assert (Q19 : getr r2 19 = Z_to_bv 64 n) by (rewrite P19; unfold r1; gres; exact H19).
  assert (Q20 : getr r2 20 = Z_to_bv 64 r) by (rewrite P20; unfold r1; gres; reflexivity).
  assert (Q21 : getr r2 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite P21; unfold r1; gres; reflexivity).
  clear P8 P9 P18 P19 P20 P21 P10 P1 K2.
  (* [comment removed for export] *)
  assert (S3 : exists r3, msteps ASEGS (mkst r2 (Z_to_bv 64 0x42134) PM1 rom) (mkst r3 (0x611f8 : word) PM1 rom)
            /\ r3 = regupd (regupd (regupd (regupd r2 11 (Z_to_bv 64 (msz - 4096 - n))) 12 (Z_to_bv 64 250)) 10 (Z_to_bv 64 (4096 + r + n))) 1 (Z_to_bv 64 0x42144)).
  { eexists. split; [|reflexivity]. wpc.
    zstep F_42134 D_42134. replace (msz + r - (4096 + r + n)) with (msz - 4096 - n) by lia.     (* [comment removed for export] *)
    zstep F_42138 D_42138. zstep F_4213c D_4213c.                                                 (* [comment removed for export] *)
    stepn F_42140 D_42140.                                                                        (* [comment removed for export] *)
    wpc. apply mst_refl. }
  destruct S3 as (r3 & RUN3 & Er3).
  (* [comment removed for export] *)
  assert (LAY3 : art_layout PM1) by (apply (art_layout_agree M1 PM1); [intros x Hx; apply AG3; lia | exact LAY]).
  destruct (art_poison_run r3 PM1 rom (Z_to_bv 64 0x42144) (s - 96) (4096 + r + n) (msz - 4096 - n) 250
              ltac:(subst r3; gres; reflexivity) ltac:(unfold ret_ok; apply bv_eq; vm_compute; reflexivity)
              ltac:(subst r3; gres; exact P2) ltac:(subst r3; gres; reflexivity) ltac:(subst r3; gres; reflexivity) ltac:(subst r3; gres; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(apply (wr_grows _ M1 PM1 _ _ G3); apply (wr_sub _ _ _ _ _ _ W1); lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
              LAY3 PO2 MU8 MT8 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(apply (wr_grows _ M1 PM1 _ _ G3); apply (wr_sub _ _ _ _ _ _ W3); lia))
    as (r4 & RUN4 & P10 & P1 & P2' & P8 & P9 & P18 & P19 & P20 & P21 & K4).
  match type of RUN4 with msteps _ _ (mkst _ _ ?X _) => assert (EQ4 : X = sec_pm2 M1 s stat sec msz n r) end.
  { unfold sec_pm2. subst r3. gres. rewrite Q8, Q9, Q18, Q19, Q20, Q21. rewrite !art_u_lit by lia. reflexivity. }
  rewrite EQ4 in RUN4. clear EQ4.
  set (PM2 := sec_pm2 M1 s stat sec msz n r) in RUN4.
  assert (AG4 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> PM2 x = M1 x).
  { intros x X1 X2. pose proof (u64_range x). unfold PM2, sec_pm2, art_poison_frame. fold PM1.
    rewrite Wf_outside; [ | lia | rewrite KT; lia | rewrite KT; lia ].
    rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG3; assumption. }
  assert (G4 : mem_grows M1 PM2).
  { unfold PM2, sec_pm2, art_poison_frame. fold PM1. eapply mem_grows_trans; [ | apply Wf_grows ]. do 7 (eapply mem_grows_trans; [ | apply Wn_grows ]). exact G3. }
  (* [comment removed for export] *)
  subst r3.
  assert (V4 : getr r4 4 = Z_to_bv 64 tp) by (rewrite (K4 4%bv) by pk; gres; exact Q4).
  assert (V8 : getr r4 8 = Z_to_bv 64 stat) by (rewrite P8; gres; exact Q8).
  assert (V9 : getr r4 9 = Z_to_bv 64 sec) by (rewrite P9; gres; exact Q9).
  assert (V18 : getr r4 18 = Z_to_bv 64 msz) by (rewrite P18; gres; exact Q18).
  assert (V19 : getr r4 19 = Z_to_bv 64 n) by (rewrite P19; gres; exact Q19).
  assert (V20 : getr r4 20 = Z_to_bv 64 r) by (rewrite P20; gres; exact Q20).
  assert (V21 : getr r4 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite P21; gres; exact Q21).
  assert (V22 : getr r4 22 = Z_to_bv 64 (msz + r)) by (rewrite (K4 22%bv) by pk; gres; exact Q22).
  assert (V24 : getr r4 24 = Z_to_bv 64 7) by (rewrite (K4 24%bv) by pk; gres; exact Q24).
  assert (V25 : getr r4 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K4 25%bv) by pk; gres; exact Q25).
  assert (V3x : getr r4 3 = getr regs 3) by (rewrite (K4 3%bv) by pk; gres; exact Q3x).
  assert (V26x : getr r4 26 = getr regs 26) by (rewrite (K4 26%bv) by pk; gres; exact Q26x).
  assert (V27x : getr r4 27 = getr regs 27) by (rewrite (K4 27%bv) by pk; gres; exact Q27x).
  clear P8 P9 P18 P19 P20 P21 P10 P1 K4 Q4 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25.
  (* [comment removed for export] *)
  assert (TSD4 : art_tsd PM2 tp key tsd ctx t).
  { apply (art_tsd_agree M1 PM2); [intros x Hx; apply AG4; lia | intros x Hx; apply AG4; [unfold apart in ACs; lia | unfold apart in ASc; lia] | lia | lia | exact TSD]. }
  assert (S5 : exists r5 M5, msteps ASEGS (mkst r4 (Z_to_bv 64 0x42144) PM2 rom) (mkst r5 (0x42148 : word) M5 rom)
            /\ M5 = Wn 8 (Wn 8 PM2 (s - 104) 0x42148) (s - 120) 0x68c3c
            /\ getr r5 10 = Z_to_bv 64 (t + 2800) /\ getr r5 2 = Z_to_bv 64 (s - 96)
            /\ (forall rg : reg, rg <> 1%bv -> rg <> 2%bv -> rg <> 10%bv -> rg <> 11%bv -> getr r5 rg = getr r4 rg)).
  { eexists. eexists. split; [ | split; [ | split; [ | split ] ] ].
    - wpc. stepn F_42144 D_42144.                                                                 (* [comment removed for export] *)
      eapply msteps_trans; [ eapply (art_thread_stats_fn _ _ _ _ (s - 96) tp key tsd ctx t);
        lazymatch goal with
        | |- getr _ _ = _ => gres; rwH; reflexivity
        | |- ret_ok _ => unfold ret_ok; apply bv_eq; vm_compute; reflexivity
        | |- art_tsd _ _ _ _ _ _ => exact TSD4
        | |- apart _ _ (ctx + 152) _ => unfold apart; unfold apart in ACs; lia
        | |- apart _ _ _ _ => unfold apart; lia
        | |- wr _ _ _ _ => apply (wr_grows _ M1 PM2 _ _ G4); apply (wr_sub _ _ _ _ _ _ W1); lia
        | |- _ => lia
        end .. | ].
      rnorm. norm_pc. apply mst_refl.
    - zmem_eq.
    - kept_solve. - kept_solve.
    - intros rg N1 N2 N10 N11. kept_solve. }
  destruct S5 as (r5 & M5 & RUN5 & EM5 & T10 & T2 & K5). subst M5.
  (* [comment removed for export] *)
  set (TM := Wn 8 (Wn 8 PM2 (s - 104) 0x42148) (s - 120) 0x68c3c) in RUN5.
  assert (AG5 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) -> TM x = M1 x).
  { intros x X1 X2. pose proof (u64_range x). unfold TM. rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG4; assumption. }
  assert (G5 : mem_grows M1 TM) by (unfold TM; do 2 (eapply mem_grows_trans; [ | apply Wn_grows ]); exact G4).
  assert (U9 : getr r5 9 = Z_to_bv 64 sec) by (rewrite (K5 9%bv) by nlit; exact V9).
  assert (U18 : getr r5 18 = Z_to_bv 64 msz) by (rewrite (K5 18%bv) by nlit; exact V18).
  assert (U19 : getr r5 19 = Z_to_bv 64 n) by (rewrite (K5 19%bv) by nlit; exact V19).
  assert (U20 : getr r5 20 = Z_to_bv 64 r) by (rewrite (K5 20%bv) by nlit; exact V20).
  assert (U21 : getr r5 21 = Z_to_bv 64 (4096 + r + n)) by (rewrite (K5 21%bv) by nlit; exact V21).
  assert (U22 : getr r5 22 = Z_to_bv 64 (msz + r)) by (rewrite (K5 22%bv) by nlit; exact V22).
  assert (U24 : getr r5 24 = Z_to_bv 64 7) by (rewrite (K5 24%bv) by nlit; exact V24).
  assert (U25 : getr r5 25 = Z_to_bv 64 (4096 + r)) by (rewrite (K5 25%bv) by nlit; exact V25).
  assert (U4 : getr r5 4 = Z_to_bv 64 tp) by (rewrite (K5 4%bv) by nlit; exact V4).
  assert (U8 : getr r5 8 = Z_to_bv 64 stat) by (rewrite (K5 8%bv) by nlit; exact V8).
  #[warnings="-ltac"]
  assert (CC6 : cellA TM (t + 2800 + 72) 8 C) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; [unfold apart in ATs; cbn in Hx; lia | unfold apart in ASt; cbn in Hx; lia] | lia | cbn; lia | replace (t + 2800 + 72) with (t + 2872) by lia; exact CC]).
  assert (CD6 : cellA TM (t + 2800 + 80) 8 D) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; [unfold apart in ATs; cbn in Hx; lia | unfold apart in ASt; cbn in Hx; lia] | lia | cbn; lia | replace (t + 2800 + 80) with (t + 2880) by lia; exact CD]).
  assert (Cpg6 : cellA TM sec 8 4096) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Cpg]).
  assert (Clk6 : cellA TM (sec + 616) 4 0) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Clk]).
  assert (Cnch6 : cellA TM (sec + 56) 8 nch) by (apply (cell_agree M1 TM); [intros x Hx; apply AG5; cbn in Hx; lia | lia | cbn; lia | exact Cnch]).
  destruct (sec_h3_run r5 TM rom s sec msz n r (t + 2800) C D nch T2 U9 T10 U18 U19 U20 U21 U22 U24 U25
              Hn Hn8 Hm Hnm Hr Hr4 Hrm Hsec Hsec' Hsec4 ltac:(lia) ltac:(lia) HC HC' HD HD' ltac:(lia)
              ltac:(unfold apart; unfold apart in ATr; lia) ltac:(unfold apart; lia) Hri CC6 CD6 Cpg6 Clk6 Cnch6
              ltac:(replace (t + 2800 + 72) with (t + 2872) by lia; apply (wr_grows _ M1 TM _ _ G5 W4))
              ltac:(apply (wr_grows _ M1 TM _ _ G5 W2)) ltac:(apply (wr_grows _ M1 TM _ _ G5); apply (wr_sub _ _ _ _ _ _ W5); lia))
    as (r6 & RUN6 & X10 & X13 & X21 & X2 & K6).
  match type of RUN6 with msteps _ _ (mkst _ _ ?X _) => set (HM := X) in RUN6 end.
  assert (AG6 : forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) ->
                                 ~ (t + 2872 <= U x < t + 2888) -> ~ (r <= U x < r + 32) -> ~ (sec + 616 <= U x < sec + 620) -> HM x = M1 x).
  { intros x Y1 Y2 Y3 Y4 Y5. pose proof (u64_range x). unfold HM. rewrite !Wn_outside by (first [lia | cbn; lia]). apply AG5; assumption. }
  assert (G6 : mem_grows M1 HM) by (unfold HM; do 6 (eapply mem_grows_trans; [ | apply Wn_grows ]); exact G5).
  (* [comment removed for export] *)
  assert (Z18 : getr r6 18 = Z_to_bv 64 msz) by (rewrite (K6 18%bv) by nlit; exact U18).
  assert (Z9 : getr r6 9 = Z_to_bv 64 sec) by (rewrite (K6 9%bv) by nlit; exact U9).
  assert (Cnres6 : cellA HM (sec + 48) 8 nres) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cnres]).
  destruct (sec_sl_run r6 HM rom msz sec nres Z18 Z9 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnres6) as (r7 & RUN7 & Y19 & Y14 & K7).
  exists r7. split; [ | repeat match goal with |- _ /\ _ => split end ].
  - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
    eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. unfold sec_hm. subst HM TM PM2 PM1. exact RUN7.
  - rewrite (K7 2%bv) by nlit. exact X2.
  - rewrite (K7 4%bv) by nlit. rewrite (K6 4%bv) by nlit. exact U4.
  - rewrite (K7 8%bv) by nlit. rewrite (K6 8%bv) by nlit. exact U8.
  - rewrite (K7 9%bv) by nlit. exact Z9.
  - rewrite (K7 10%bv) by nlit. exact X10.
  - rewrite (K7 13%bv) by nlit. exact X13.
  - exact Y14.
  - rewrite (K7 18%bv) by nlit. exact Z18.
  - exact Y19.
  - rewrite (K7 21%bv) by nlit. exact X21.
  - rewrite (K7 3%bv) by nlit. rewrite (K6 3%bv) by nlit. rewrite (K5 3%bv) by nlit. exact V3x.
  - rewrite (K7 26%bv) by nlit. rewrite (K6 26%bv) by nlit. rewrite (K5 26%bv) by nlit. exact V26x.
  - rewrite (K7 27%bv) by nlit. rewrite (K6 27%bv) by nlit. rewrite (K5 27%bv) by nlit. exact V27x.
Qed.

(* [comment removed for export] *)
Lemma sec_hm_agree : forall (M1 : word -> option byte) (s stat sec msz n r t C D : Z),
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> msz mod 4096 = 0 -> n + 4096 <= msz -> 4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 ->
  0 <= t -> t + 4096 < 2 ^ 47 -> 0 <= sec -> sec + 1024 < 2 ^ 64 ->
  forall x : word, ~ (s - 464 <= U x < s - 96) -> ~ (SB + r / 8 <= U x < SB + r / 8 + msz / 8) ->
                   ~ (t + 2872 <= U x < t + 2888) -> ~ (r <= U x < r + 32) -> ~ (sec + 616 <= U x < sec + 620) -> sec_hm M1 s stat sec msz n r t C D x = M1 x.
Proof.
  intros M1 s stat sec msz n r t C D Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Ht Ht' Hsec Hsec' x Y1 Y2 Y3 Y4 Y5.
  pose proof (u64_range x). assert (ESB : SB = 2147450880) by reflexivity.
  pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8.
  divfacts r 8. divfacts n 8. divfacts msz 8. divfacts (msz - 4096 - n) 8. divfacts (4096 + r + n) 8.
  assert (HT8 : 0 <= (msz - 4096 - n) / 8) by (apply Z.div_pos; lia).
  assert (MT8 : (msz - 4096 - n) mod 8 = 0) by (replace (msz - 4096 - n) with ((msz / 8 - 512 - n / 8) * 8) by lia; apply Z_mod_mult).
  assert (MU8 : (4096 + r + n) mod 8 = 0) by mod8.
  assert (K512 : Z.of_nat (Z.to_nat (4096 / 8)) = 512) by reflexivity. assert (E512 : 4096 / 8 = 512) by reflexivity.
  assert (KT : Z.of_nat (Z.to_nat ((msz - 4096 - n) / 8)) = (msz - 4096 - n) / 8) by (apply Z2Nat.id; lia).
  unfold sec_hm, sec_pm2, sec_pm1, art_poison_frame.
  rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y3 Y4; cbn; lia ].
  do 3 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y3 Y5; cbn; lia ]).
  do 2 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y1 Y2 Y4 Y5; cbn; lia ]).
  do 2 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
  rewrite Wf_outside; [ | lia | rewrite KT; lia | rewrite KT; clear Y1 Y3 Y4 Y5; lia ].
  do 7 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
  rewrite Wf_outside; [ | lia | rewrite K512; lia | rewrite K512; clear Y1 Y3 Y4 Y5; lia ].
  do 8 (rewrite Wn_outside; [ | lia | cbn; lia | clear Y2 Y3 Y4 Y5; cbn; lia ]).
  reflexivity.
Qed.
Lemma sec_hm_grows : forall (M1 : word -> option byte) (s stat sec msz n r t C D : Z), mem_grows M1 (sec_hm M1 s stat sec msz n r t C D).
Proof.
  intros. unfold sec_hm, sec_pm2, sec_pm1, art_poison_frame.
  do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). eapply mem_grows_trans; [ | apply Wf_grows ].
  do 7 (eapply mem_grows_trans; [ | apply Wn_grows ]). eapply mem_grows_trans; [ | apply Wf_grows ].
  do 8 (eapply mem_grows_trans; [ | apply Wn_grows ]). apply mem_grows_refl.
Qed.

Theorem art_sec_postA_run : forall regs (M1 rom : word -> option byte) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 : word)
    (s sec stat msz n r F tp key tsd ctx t C D nch nres pab na cur mx bsl st16 st24 : Z),
  getr regs 1 = Z_to_bv 64 0x73734 -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 r -> getr regs 19 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 8 -> getr regs 24 = Z_to_bv 64 7 ->
  ret_ok x1 ->
  (* [comment removed for export] *)
  kHighMemBeg <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> msz mod 4096 = 0 -> n + 4096 <= msz ->
  4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 -> 0x634000 <= r -> appmem r msz -> apart r msz (s - 464) 464 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> sec + 624 <= stat -> stat + 64 < 0x634000 -> (sec + 616) mod 4 = 0 -> stat mod 8 = 0 ->
  0x10000 <= F -> F + 512 < 0x634000 ->
  ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x634000 <= t) -> t + 4096 < 2 ^ 47 -> appmem t 4096 -> apart (t + 2872) 16 r 32 -> apart (t + 2872) 16 (s - 464) 464 -> apart (t + 2872) 16 (ctx + 152) 8 ->
  0 <= C -> C < 2 ^ 64 -> 0 <= D -> D < 2 ^ 64 ->
  0 <= nch < 2 ^ 20 -> 0 <= nres < 2 ^ 64 -> nch <> nres -> 0x634000 <= pab -> pab + 8 * nch + 8 < 2 ^ 47 -> appmem (pab + 8 * nch) 8 ->
  apart (pab + 8 * nch) 8 r 32 -> apart (pab + 8 * nch) 8 (s - 464) 464 -> apart (pab + 8 * nch) 8 (t + 2872) 16 ->
  0 <= na -> na < 2 ^ 64 -> 0 <= cur -> cur < 2 ^ 64 -> 0 <= mx < 2 ^ 64 -> 0 <= bsl -> bsl < 2 ^ 64 ->
  0 <= st16 -> st16 < 2 ^ 64 -> 0 <= st24 -> st24 < 2 ^ 64 ->
  (* [comment removed for export] *)
  appmem ctx 4096 -> apart (ctx + 152) 8 r 32 -> apart (ctx + 152) 8 (s - 464) 464 -> 4096 <= tp - 88 -> tp < 0x634000 -> 4096 <= tsd -> tsd + 8 * key + 8 <= 0x634000 ->
  (* [comment removed for export] *)
  wrA M1 (s - 464) 464 -> wrA M1 r 32 -> wrA M1 (SB + r / 8) (msz / 8) -> wrA M1 (t + 2872) 16 -> wrA M1 sec 624 -> wrA M1 (stat + 16) 16 -> wrA M1 (pab + 8 * nch) 8 ->
  cellA M1 (s - 104) 8 0x420dc -> cellA M1 (s - 112) 8 stat -> cellA M1 (s - 120) 8 sec -> cellA M1 (s - 128) 8 msz ->
  cellA M1 (s - 8) 8 (U x1) -> cellA M1 (s - 16) 8 (U x8) -> cellA M1 (s - 24) 8 (U x9) -> cellA M1 (s - 32) 8 (U x18) -> cellA M1 (s - 40) 8 (U x19) ->
  cellA M1 (s - 48) 8 (U x20) -> cellA M1 (s - 56) 8 (U x21) -> cellA M1 (s - 64) 8 (U x22) -> cellA M1 (s - 72) 8 (U x23) -> cellA M1 (s - 80) 8 (U x24) -> cellA M1 (s - 88) 8 (U x25) ->
  cellA M1 sec 8 4096 -> cellA M1 0xd64b8 8 F -> cellA M1 (F + 144) 8 0 -> art_layout M1 -> art_tsd M1 tp key tsd ctx t ->
  cellA M1 (t + 2872) 8 C -> cellA M1 (t + 2880) 8 D -> cellA M1 (sec + 616) 4 0 -> cellA M1 (sec + 56) 8 nch -> cellA M1 (sec + 48) 8 nres -> cellA M1 (sec + 8) 8 pab ->
  cellA M1 (sec + 72) 8 na -> cellA M1 (sec + 88) 8 cur -> cellA M1 (sec + 96) 8 mx -> cellA M1 (sec + 104 + 8 * Z.log2 msz) 8 bsl ->
  cellA M1 (stat + 16) 8 st16 -> cellA M1 (stat + 24) 8 st24 ->
  exists regs', msteps ASEGS (mkst regs (0x71de8 : word) M1 rom)
     (mkst regs' x1 (sec_postA_mem M1 s stat sec msz n r t C D nch pab na cur mx bsl st16 st24) rom)
  /\ getr regs' 10 = Z_to_bv 64 (4096 + r) /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = x1
  /\ getr regs' 8 = x8 /\ getr regs' 9 = x9 /\ getr regs' 18 = x18 /\ getr regs' 19 = x19 /\ getr regs' 20 = x20 /\ getr regs' 21 = x21
  /\ getr regs' 22 = x22 /\ getr regs' 23 = x23 /\ getr regs' 24 = x24 /\ getr regs' 25 = x25 /\ getr regs' 4 = Z_to_bv 64 tp
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs M1 rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat msz n r F tp key tsd ctx t C D nch nres pab na cur mx bsl st16 st24.
  intros H1 H2 H4 H10 H19 H21 H24 Hret.
  intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
  intros Ht Ht' APt ATr ATs ATc HC HC' HD HD' Hnch Hnres Hne Hpi Hpab' APp APPr APPs APPt.
  intros Hna Hna' Hcur Hcur' Hmx Hbsl Hbsl' H16 H16' H24a H24a'.
  intros APc ACr ACs Htp Htp' Htsd Htsd'.
  intros W1 W2 W3 W4 W5 W6 W7 C104 C112 C120 C128 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Cpab Cna Ccur Cmx Cbsl C16 C24.
  unfold kHighMemBeg in *.
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  assert (ESB : SB = 2147450880) by reflexivity.
  pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8. divfacts r 8. divfacts msz 8.
  (* [comment removed for export] *)
  pose proof (sec_head_run regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nres) as HEAD.
  repeat lazymatch type of HEAD with
    | ?P -> _ => let HP := fresh "HP" in assert (HP : P) by (first [assumption | lia]); specialize (HEAD HP); clear HP
    end.
  destruct HEAD as (r7 & RUNH & Y2 & Y4 & Y8 & Y9 & Y10 & Y13 & Y14 & Y18 & Y19 & Y21 & Y3x & Y26x & Y27x).
  set (HM := sec_hm M1 s stat sec msz n r t C D) in RUNH.
  pose proof (sec_hm_agree M1 s stat sec msz n r t C D ltac:(lia) Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm ltac:(lia) Ht' ltac:(lia) ltac:(lia)) as AG6. fold HM in AG6.
  pose proof (sec_hm_grows M1 s stat sec msz n r t C D) as G6. fold HM in G6.
  unfold appmem, kHighMemBeg in APt, APp.
  assert (ASt : apart (SB + r / 8) (msz / 8) (t + 2872) 16) by (clear APp; unfold apart; lia).
  assert (ASp : apart (SB + r / 8) (msz / 8) (pab + 8 * nch) 8) by (clear APt; unfold apart; lia).
  clear APt APp APr APc.
  (* [comment removed for export] *)
  assert (RUN8 : msteps ASEGS (mkst r7 (0x42280 : word) HM rom) (mkst r7 (0x42284 : word) HM rom)).
  { zbft F_42280 D_42280. apply mst_refl. }
  (* [comment removed for export] *)
  assert (ARs' : apart r 32 (s - 464) 464) by (unfold apart in ARs |- *; lia).
  assert (D1 : cellA HM (sec + 8) 8 pab) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cpab]).
  assert (D2 : cellA HM (sec + 72) 8 na) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cna]).
  assert (D3 : cellA HM (sec + 88) 8 cur) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Ccur]).
  assert (D4 : cellA HM (sec + 96) 8 mx) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cmx]).
  assert (D5 : cellA HM (sec + 104 + 8 * Z.log2 msz) 8 bsl) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cbsl]).
  assert (D6 : cellA HM (stat + 16) 8 st16) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact C16]).
  assert (D7 : cellA HM (stat + 24) 8 st24) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact C24]).
  assert (E1 : cellA HM (s - 8) 8 (U x1)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L1]).
  assert (E2 : cellA HM (s - 16) 8 (U x8)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L2]).
  assert (E3 : cellA HM (s - 24) 8 (U x9)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L3]).
  assert (E4 : cellA HM (s - 32) 8 (U x18)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L4]).
  assert (E5 : cellA HM (s - 40) 8 (U x19)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L5]).
  assert (E6 : cellA HM (s - 48) 8 (U x20)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L6]).
  assert (E7 : cellA HM (s - 56) 8 (U x21)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L7]).
  assert (E8 : cellA HM (s - 64) 8 (U x22)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L8]).
  assert (E9 : cellA HM (s - 72) 8 (U x23)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L9]).
  assert (E10 : cellA HM (s - 80) 8 (U x24)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L10]).
  assert (E11 : cellA HM (s - 88) 8 (U x25)) by (apply (cell_agree M1 HM); [intros x Hx; unfold apart in ATs, ARs'; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact L11]).
  pose proof (sec_tail_fn r7 HM rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24
                Y2 Y8 Y9 Y10 Y13 Y18 Y19 Y21 Hret ltac:(lia) Hs' Hm Hr Hrm Hri Hsec Hss Hst Hst8 ltac:(lia) Hpi Hpab'
                Hna Hna' Hcur Hcur' Hmx ltac:(lia) Hbsl Hbsl' H16 H16' H24a H24a' APPr APPs ARs'
                D1 D2 D3 D4 D5 D6 D7 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
                ltac:(apply (wr_grows _ M1 HM _ _ G6); apply (wr_sub _ _ _ _ _ _ W2); lia) ltac:(apply (wr_grows _ M1 HM _ _ G6 W7))
                ltac:(apply (wr_grows _ M1 HM _ _ G6 W5)) ltac:(apply (wr_grows _ M1 HM _ _ G6 W6))) as RUN9.
  (* [comment removed for export] *)
  match type of RUN9 with msteps _ _ (mkst ?R _ _ _) => exists R end.
  split; [ | repeat match goal with |- _ /\ _ => split end ].
  - eapply msteps_trans; [exact RUNH|]. eapply msteps_trans; [exact RUN8|]. unfold sec_postA_mem. subst HM. exact RUN9.
  - gres. exact Y10.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - gres. exact Y4.
  - gres. exact Y3x.
  - gres. exact Y26x.
  - gres. exact Y27x.
Qed.

Theorem art_sec_postB1_run : forall regs (M1 rom : word -> option byte)
    (s sec stat msz n r F tp key tsd ctx t C D nch pab2 : Z),
  getr regs 1 = Z_to_bv 64 0x73734 -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 r -> getr regs 19 = Z_to_bv 64 n ->
  getr regs 21 = Z_to_bv 64 8 -> getr regs 24 = Z_to_bv 64 7 ->
  (* [comment removed for export] *)
  kHighMemBeg <= s - 464 -> s < 2 ^ 47 -> 0 <= n -> n mod 8 = 0 -> 2 ^ 12 <= msz -> msz mod 4096 = 0 -> n + 4096 <= msz ->
  4096 <= r -> r mod 4096 = 0 -> r + msz < 2 ^ 47 -> 0x634000 <= r -> appmem r msz -> apart r msz (s - 464) 464 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> sec + 624 <= stat -> stat + 64 < 0x634000 -> (sec + 616) mod 4 = 0 -> stat mod 8 = 0 ->
  0x10000 <= F -> F + 512 < 0x634000 ->
  ((4096 <= t /\ t + 4096 <= 0x10000) \/ 0x634000 <= t) -> t + 4096 < 2 ^ 47 -> appmem t 4096 -> apart (t + 2872) 16 r 32 -> apart (t + 2872) 16 (s - 464) 464 -> apart (t + 2872) 16 (ctx + 152) 8 ->
  0 <= C -> C < 2 ^ 64 -> 0 <= D -> D < 2 ^ 64 ->
  (* [comment removed for export] *)
  appmem ctx 4096 -> apart (ctx + 152) 8 r 32 -> apart (ctx + 152) 8 (s - 464) 464 -> 4096 <= tp - 88 -> tp < 0x634000 -> 4096 <= tsd -> tsd + 8 * key + 8 <= 0x634000 ->
  (* [comment removed for export] *)
  wrA M1 (s - 464) 464 -> wrA M1 r 32 -> wrA M1 (SB + r / 8) (msz / 8) -> wrA M1 (t + 2872) 16 -> wrA M1 sec 624 ->
  cellA M1 (s - 104) 8 0x420dc -> cellA M1 (s - 112) 8 stat -> cellA M1 (s - 120) 8 sec -> cellA M1 (s - 128) 8 msz ->
  cellA M1 sec 8 4096 -> cellA M1 0xd64b8 8 F -> cellA M1 (F + 144) 8 0 -> art_layout M1 -> art_tsd M1 tp key tsd ctx t ->
  cellA M1 (t + 2872) 8 C -> cellA M1 (t + 2880) 8 D -> cellA M1 (sec + 616) 4 0 -> cellA M1 (sec + 56) 8 nch -> cellA M1 (sec + 48) 8 nch ->
  (* [comment removed for export] *)
  0 <= nch < 2 ^ 20 -> 0xd6f70 <= sec -> sec + 1024 <= 0x16e1e0 -> cellA M1 (sec + 16) 8 pab2 -> cellA M1 0xd64a8 8 0x16e1e0 -> cellA M1 0x16e1e0 8 4096 -> 4096 <= pab2 -> pab2 + 8 * nch + 131072 < 2 ^ 47 -> (pab2 + 8 * nch) mod 4096 = 0 ->
  exists regs', msteps ASEGS (mkst regs (0x71de8 : word) M1 rom)
     (mkst regs' (0x71de4 : word) (sec_b1_mem (sec_hm M1 s stat sec msz n r t C D) s stat sec msz (63 - Z.log2 msz) r pab2 nch) rom)
  /\ getr regs' 17 = Z_to_bv 64 222 /\ getr regs' 10 = Z_to_bv 64 (pab2 + 8 * nch) /\ getr regs' 11 = Z_to_bv 64 131072 /\ getr regs' 12 = Z_to_bv 64 3
  /\ getr regs' 13 = Z_to_bv 64 50 /\ getr regs' 14 = Z_to_bv 64 18446744073709551615 /\ getr regs' 15 = Z_to_bv 64 0
  /\ getr regs' 1 = Z_to_bv 64 0x73ba4 /\ getr regs' 2 = Z_to_bv 64 (s - 192) /\ getr regs' 8 = Z_to_bv 64 131072 /\ getr regs' 9 = Z_to_bv 64 0
  /\ getr regs' 18 = Z_to_bv 64 (pab2 + 8 * nch) /\ getr regs' 19 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 0x16e1e0 /\ getr regs' 21 = Z_to_bv 64 r /\ getr regs' 4 = Z_to_bv 64 tp
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch pab2.
  intros H1 H2 H4 H10 H19 H21 H24.
  intros Hs Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm Hri APr ARs Hsec Hsec' Hss Hst Hsec4 Hst8 HF HF'.
  intros Ht Ht' APt ATr ATs ATc HC HC' HD HD'.
  intros APc ACr ACs Htp Htp' Htsd Htsd'.
  intros W1 W2 W3 W4 W5 C104 C112 C120 C128 Cpg C38 C144 LAY TSD CC CD Clk Cnch Cnres Hnch Hsg Hsg' Cp2 Cg28 Cpc Hpab2 Hpab2' Hal.
  unfold kHighMemBeg in *.
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  assert (ESB : SB = 2147450880) by reflexivity.
  pose proof (mod8_of_4096 r Hr4) as Hr8. pose proof (mod8_of_4096 msz Hm4) as Hm8. divfacts r 8. divfacts msz 8.
  (* [comment removed for export] *)
  pose proof (sec_head_run regs M1 rom s sec stat msz n r F tp key tsd ctx t C D nch nch) as HEAD.
  repeat lazymatch type of HEAD with
    | ?P -> _ => let HP := fresh "HP" in assert (HP : P) by (first [assumption | lia]); specialize (HEAD HP); clear HP
    end.
  destruct HEAD as (r7 & RUNH & Y2 & Y4 & Y8 & Y9 & Y10 & Y13 & Y14 & Y18 & Y19 & Y21 & Y3x & Y26x & Y27x).
  set (HM := sec_hm M1 s stat sec msz n r t C D) in RUNH.
  pose proof (sec_hm_agree M1 s stat sec msz n r t C D ltac:(lia) Hs' Hn Hn8 Hm Hm4 Hnm Hr Hr4 Hrm ltac:(lia) Ht' ltac:(lia) ltac:(lia)) as AG6. fold HM in AG6.
  pose proof (sec_hm_grows M1 s stat sec msz n r t C D) as G6. fold HM in G6.
  clear APt APr APc.
  assert (D1 : cellA HM (sec + 16) 8 pab2) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cp2]).
  assert (D2 : cellA HM 0xd64a8 8 0x16e1e0) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cg28]).
  assert (D3 : cellA HM 0x16e1e0 8 4096) by (apply (cell_agree M1 HM); [intros x Hx; apply AG6; cbn in Hx; lia | lia | cbn; lia | exact Cpc]).
  pose proof (sec_b1_fn r7 HM rom s sec stat (63 - Z.log2 msz) nch pab2 r msz Y2 Y8 Y9 Y10 Y13 Y14 Y18 Y19 Y21
                ltac:(lia) Hs' Hr ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hsec Hsec' Hnch Hpab2 Hpab2' Hal
                ltac:(apply (wr_grows _ M1 HM _ _ G6 W1)) D1 D2 D3) as RUNB.
  match type of RUNB with msteps _ _ (mkst ?R _ _ _) => exists R end.
  split; [ | repeat match goal with |- _ /\ _ => split end ].
  - eapply msteps_trans; [exact RUNH|]. subst HM. exact RUNB.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - gres. reflexivity.
  - gres. exact Y4.
  - gres. exact Y3x.
  - gres. exact Y26x.
  - gres. exact Y27x.
Qed.

(* [comment removed for export] *)
Definition sec_postB_mem (M2 : word -> option byte) (s stat sec msz r nch nres pab na cur mx bsl st16 st24 : Z) : word -> option byte :=
  sec_tail_mem (Wn 8 (Wn 4 M2 (s - 148) 18446744072277895850) (sec + 48) (nres + 16384)) sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24.

Theorem art_sec_postB2_run : forall regs (M2 rom : word -> option byte) (x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 : word)
    (s sec stat msz r F tp nch nres q pab na cur mx bsl st16 st24 : Z),
  getr regs 1 = Z_to_bv 64 0x73ba4 -> getr regs 2 = Z_to_bv 64 (s - 192) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 131072 -> getr regs 10 = Z_to_bv 64 q ->
  getr regs 21 = Z_to_bv 64 r -> ret_ok x1 ->
  0x634000 <= s - 464 -> s < 2 ^ 47 -> 2 ^ 12 <= msz < 2 ^ 47 -> 4096 <= r -> r + msz < 2 ^ 47 -> 0x634000 <= r -> 0 <= q < 2 ^ 64 - 4095 ->
  0x10000 <= sec -> sec + 1024 < 0x634000 -> sec + 624 <= stat -> stat + 64 < 0x634000 -> stat mod 8 = 0 -> 0x10000 <= F -> F + 512 < 0x634000 ->
  0 <= nch < 2 ^ 20 -> 0 <= nres < 2 ^ 40 -> 0x634000 <= pab -> pab + 8 * nch + 8 < 2 ^ 47 ->
  apart (pab + 8 * nch) 8 r 32 -> apart (pab + 8 * nch) 8 (s - 464) 464 -> apart r 32 (s - 464) 464 ->
  0 <= na -> na < 2 ^ 64 -> 0 <= cur -> cur < 2 ^ 64 -> 0 <= mx < 2 ^ 64 -> 0 <= bsl -> bsl < 2 ^ 64 ->
  0 <= st16 -> st16 < 2 ^ 64 -> 0 <= st24 -> st24 < 2 ^ 64 ->
  wrA M2 (s - 464) 464 -> wrA M2 sec 624 -> wrA M2 (stat + 16) 16 -> wrA M2 (r + 24) 8 -> wrA M2 (pab + 8 * nch) 8 ->
  cellA M2 (s - 104) 8 0x4247c -> cellA M2 (s - 112) 8 stat -> cellA M2 (s - 120) 8 sec -> cellA M2 (s - 128) 8 msz -> cellA M2 (s - 136) 8 (63 - Z.log2 msz) -> cellA M2 (s - 144) 8 (4096 + r) ->
  cellA M2 0xd64b8 8 F -> cellA M2 (F + 144) 8 0 -> cellA M2 (sec + 48) 8 nres -> cellA M2 (sec + 56) 8 nch ->
  cellA M2 (sec + 8) 8 pab -> cellA M2 (sec + 72) 8 na -> cellA M2 (sec + 88) 8 cur -> cellA M2 (sec + 96) 8 mx -> cellA M2 (sec + 104 + 8 * Z.log2 msz) 8 bsl ->
  cellA M2 (stat + 16) 8 st16 -> cellA M2 (stat + 24) 8 st24 ->
  cellA M2 (s - 8) 8 (U x1) -> cellA M2 (s - 16) 8 (U x8) -> cellA M2 (s - 24) 8 (U x9) -> cellA M2 (s - 32) 8 (U x18) -> cellA M2 (s - 40) 8 (U x19) ->
  cellA M2 (s - 48) 8 (U x20) -> cellA M2 (s - 56) 8 (U x21) -> cellA M2 (s - 64) 8 (U x22) -> cellA M2 (s - 72) 8 (U x23) -> cellA M2 (s - 80) 8 (U x24) -> cellA M2 (s - 88) 8 (U x25) ->
  exists regs', msteps ASEGS (mkst regs (0x71de8 : word) M2 rom)
     (mkst regs' x1 (sec_postB_mem M2 s stat sec msz r nch nres pab na cur mx bsl st16 st24) rom)
  /\ getr regs' 10 = Z_to_bv 64 (4096 + r) /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = x1
  /\ getr regs' 8 = x8 /\ getr regs' 9 = x9 /\ getr regs' 18 = x18 /\ getr regs' 19 = x19 /\ getr regs' 20 = x20 /\ getr regs' 21 = x21
  /\ getr regs' 22 = x22 /\ getr regs' 23 = x23 /\ getr regs' 24 = x24 /\ getr regs' 25 = x25 /\ getr regs' 4 = Z_to_bv 64 tp
  /\ getr regs' 3 = getr regs 3 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27.
Proof.
  intros regs M2 rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat msz r F tp nch nres q pab na cur mx bsl st16 st24.
  intros H1 H2 H4 H8 H10 H21 Hret Hs Hs' Hm Hr Hrm Hri Hq Hsec Hsec' Hss Hst Hst8 HF HF' Hnch Hnres Hpi Hpab' APPr APPs ARs.
  intros Hna Hna' Hcur Hcur' Hmx Hbsl Hbsl' H16 H16' H24a H24a' W1 W5 W6 W2 W7.
  intros C104 C112 C120 C128 C136 C144 C38 CF Cnres Cnch Cpab Cna Ccur Cmx Cbsl C16 C24 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11.
  assert (HL : 12 <= Z.log2 msz <= 46).
  { split. apply Z.log2_le_pow2; lia. apply Z.lt_succ_r. apply Z.log2_lt_pow2; lia. }
  pose proof (sec_b2_fn regs M2 rom s sec stat msz (63 - Z.log2 msz) nch nres r q F H1 H2 H8 H10 Hs Hs' Hr ltac:(lia) ltac:(lia) Hq
                Hsec Hsec' ltac:(lia) Hst Hnch Hnres ltac:(lia) HF HF' W1 W5 C104 C112 C120 C128 C136 C144 C38 CF Cnres Cnch) as RUNB.
  match type of RUNB with msteps _ _ (mkst ?R _ ?X _) => set (rb := R) in RUNB; set (MB := X) in RUNB end.
  assert (AG : forall x : word, ~ (s - 148 <= U x < s - 144) -> ~ (sec + 48 <= U x < sec + 56) -> MB x = M2 x).
  { intros x Y1 Y2. pose proof (u64_range x). unfold MB. rewrite !Wn_outside by (first [lia | cbn; lia]). reflexivity. }
  assert (G : mem_grows M2 MB) by (unfold MB; do 2 (eapply mem_grows_trans; [ | apply Wn_grows ]); apply mem_grows_refl).
  assert (D1 : cellA MB (sec + 8) 8 pab) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cpab]).
  assert (D2 : cellA MB (sec + 72) 8 na) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cna]).
  assert (D3 : cellA MB (sec + 88) 8 cur) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Ccur]).
  assert (D4 : cellA MB (sec + 96) 8 mx) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cmx]).
  assert (D5 : cellA MB (sec + 104 + 8 * Z.log2 msz) 8 bsl) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact Cbsl]).
  assert (D6 : cellA MB (stat + 16) 8 st16) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C16]).
  assert (D7 : cellA MB (stat + 24) 8 st24) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact C24]).
  assert (E1 : cellA MB (s - 8) 8 (U x1)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L1]).
  assert (E2 : cellA MB (s - 16) 8 (U x8)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L2]).
  assert (E3 : cellA MB (s - 24) 8 (U x9)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L3]).
  assert (E4 : cellA MB (s - 32) 8 (U x18)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L4]).
  assert (E5 : cellA MB (s - 40) 8 (U x19)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L5]).
  assert (E6 : cellA MB (s - 48) 8 (U x20)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L6]).
  assert (E7 : cellA MB (s - 56) 8 (U x21)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L7]).
  assert (E8 : cellA MB (s - 64) 8 (U x22)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L8]).
  assert (E9 : cellA MB (s - 72) 8 (U x23)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L9]).
  assert (E10 : cellA MB (s - 80) 8 (U x24)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L10]).
  assert (E11 : cellA MB (s - 88) 8 (U x25)) by (apply (cell_agree M2 MB); [intros x Hx; apply AG; cbn in Hx; lia | lia | cbn; lia | exact L11]).
  pose proof (sec_tail_fn rb MB rom x1 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 s sec stat r msz nch pab na cur mx (Z.log2 msz) bsl st16 st24
                ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity)
                ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; reflexivity) ltac:(unfold rb; gres; exact H21)
                Hret Hs Hs' ltac:(lia) Hr Hrm Hri Hsec Hss Hst Hst8 Hnch Hpi Hpab'
                Hna Hna' Hcur Hcur' Hmx ltac:(lia) Hbsl Hbsl' H16 H16' H24a H24a' APPr APPs ARs
                D1 D2 D3 D4 D5 D6 D7 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11
                ltac:(apply (wr_grows _ M2 MB _ _ G W2)) ltac:(apply (wr_grows _ M2 MB _ _ G W7))
                ltac:(apply (wr_grows _ M2 MB _ _ G W5)) ltac:(apply (wr_grows _ M2 MB _ _ G W6))) as RUN9.
  match type of RUN9 with msteps _ _ (mkst ?R _ _ _) => exists R end.
  split; [ | repeat match goal with |- _ /\ _ => split end ].
  - eapply msteps_trans; [exact RUNB|]. unfold sec_postB_mem. subst MB rb. exact RUN9.
  - unfold rb. gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - gres. reflexivity. - gres. reflexivity. - gres. reflexivity. - gres. reflexivity.
  - unfold rb. gres. exact H4.
  - unfold rb. gres. reflexivity.
  - unfold rb. gres. reflexivity.
  - unfold rb. gres. reflexivity.
Qed.
End FPX.
