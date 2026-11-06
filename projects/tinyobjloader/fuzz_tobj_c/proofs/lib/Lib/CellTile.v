(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "sstate"; "cell"; "valuation"; "cell_holds"; "eval"; "mkCell"; "sv_eqb"; "c_off"; "c_val"; "c_width"; "cell_wf"; "smatch"; "SLit"; "covered"; "mem_match"; "mkObj"; "ob_base"; "ob_cells"; "ob_dflt"; "ob_hi"; "ob_lo"; "obj_holds"; "obj_range"; "obj_wf"; "ss_objs"; "SAlu"; "dflt_writable"; "enc_bytes"; "ss_next"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "N"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "iff"; "@Corelib.Init.Datatypes"; "bool"; "option"; "false"; "Some"; "andb"; "nat"; "true"; "list"; "cons"; "prod"; "app"; "None"; "S"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "le"; "pow"; "lt"; "mul"; "eqb"; "shiftr"; "add"; "leb"; "ltb"; "of_nat"; "to_nat"; "sub"; "@LinuxProcessSemantics.Riscv.Instr"; "aluop"; "mulop"; "ALU_SRL"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.CellTile"; "byte_val_ok"; "tile_obj"; "bytes_present"; "recell_nth"; "recell_at"; "tile_at"; "is_byte_cell"; "recell"; "tiles_at"; "@Corelib.Lists.ListDef"; "Forall"; "firstn"; "skipn"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "same_atoms"; "set_objs"; "@Stdlib.Lists.List"; "nth_error"; "forallb"; "In"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@Corelib.Init.Peano"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3 SymBytes.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition byte_val_ok (v : sv) (t : Z) (e : sv) : bool := ltac2:(tb__ "0|16|
S0S26Le;Ve;S1fS28Lz;S20S28Li;M0S40S0S0S40S26Lop;M1R3S28S28S28S28S28S28S0S26Lb;M2R1S1fS2aS2aS2aS8R3Vv;A2S38R1S37Z8M3Vt;A2A2A2S3bZ0M4Vt;A2A2S3cVt;G3A2A2Ls;M5G0S40S0S0S28Lb0;La;M6Lop0;M7G7S41G6Lop0;M8G8S26S21S0S28La;Lw;Lsgn;S20S0S1fS28Lk;Li;Ll;M9X0x8S28S28S28X40xaLb;Lv';Lop;S40S0S0S28Lb;La;MaLop;S41GaLop;MbGbS26S21S0S26S26Lsgn;R3S28S21S26Lw;R2S28S20S20S26Lp;R1S20S28Lp0;S20S20S26Lp0;R1S20S28Lp1;S20S20S26Lp1;R1S20S28Lp2;S20S20S26Lp2;R1S20S28Lp3;McGcS0S26Lv';R5S1fS2aS8R6Vv;A2S38Vt;G4A2MdA2MeLz;S20GeLi;S40S0S0G1R3S2aS8R8Vv;A2GdA2MfGfGfGfGfGfG2R1G5S20S2aS8R9Vv;A2GdA2Li;S40S0S0S2aS8RbVv;A2GdA2M10Lb0;La;M11Lop0;M12G12S41G11Lop0;M13G13S26S21S0G10La;Lw0;Lsgn0;S20S0S1fG10Lk;Li;Ll;X0x8GfGfGfX40xaLb;Lv';Lop;S40S0S0GfLb;La;M14Lop;S41G14Lop;M15G15S26S21S0GfLa;Lw0;Lsgn0;S20S0S1fGfLk;Li;Ll;X0x8X20x3Lp2;S28X20x3Lp1;S28X20x3Lp0;S28X20x3Lp;X21x2X26x2Lv';Lw;Lsgn;G9X0x8").

Definition is_byte_cell (off v : sv) (t : Z) (c : cell) : bool := ltac2:(tb__ "0|0|
S2aS2aS38SbVc;A1Z1A2S27S1fA1S26Lx;S57S9Vc;A1Voff;A2S1fS38R1Vt;A2Ld;S28X27x2A2S49Vv;Vt;SaVc;A1A3A2").

Fixpoint bytes_present (cells : list cell) (off v : sv) (t : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => existsb (is_byte_cell off v t) cells && bytes_present cells off v (t + 1) n'
  end.

Definition tile_obj (o : sobj) (off : sv) (k : Z) (v : sv) : option sobj := ltac2:(tb__ "0|3|
S26S27S1A1L_;S2aS2aS2aS3cZ0M0Vk;A2S3bVk;Z8A2A2S1cS14Vo;A1M1A1A2S4bS13Vo;A1M2Voff;Vv;G0S3eVk;A1A5A2S29S1S11S12Vo;A1S16Vo;A1S15Vo;A1S2eS3S7Voff;Vk;Vv;A3G2A3G1A5A2S31S1A1X26x2").

Definition tile_at (S : sstate) (i : nat) (off : sv) (k : Z) (v : sv) : option sstate := ltac2:(tb__ "0|4|
S27S1A1S27S2A1M0Lx;M1S59S1S1aVS;A1M2Vi;A3S1G1S4aR1Voff;Vk;Vv;A4S1S26G0L_;ScS1eVS;A1S7Voff;Vk;Vv;A3A2S29S2S58VS;S30S1S53S1Vi;G2A3S2eS1R1S54S1S32Vi;A1G2A3A3A3A2A2S31S2A1M3X26x2Lo';G3X27x2Lo;G3X27x2").

Fixpoint tiles_at (S : sstate) (ts : list (nat * sv * Z * sv)) : option sstate :=
  match ts with
  | [] => Some S
  | (i, off, k, v) :: rest => match tile_at S i off k v with Some S' => tiles_at S' rest | None => None end
  end.

Section T.
Variable segs : list Segment.

Lemma Z_to_bv8_mod : ltac2:(tb__ "0|2|
S1fS1fS22S1fS33R2S35Z2Z8A2M0A2S33R1G0A2A3S22S45Q8M1A1S44G1R3A2S44G1R2A2A3F_;Fb;Fa;").
Proof using .
  intros a b H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8). exact H.
Qed.

Lemma srl_lit_unsigned : ltac2:(tb__ "0|1|
S4S0S1fS23S34Z0R1A2S36R1Z40A2A2S22S1fS43Q40M0S6R4S1bS42R3SeR2A1A3A2A2S39S43G0S6R4R3A2A2R2A2A3F_;Fs;Fv;Frho;").
Proof using .
  intros rho v s Hs. cbn [eval]. rewrite srl_unsigned. f_equal.
  rewrite Z.mod_small by lia. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma byte_val_ok_sound : ltac2:(tb__ "0|2|
S4S0S1fS0S22S26S49R3R2R1A3S2cA3S22S45Q8M0A1S44G0S43Q40M1S6R5R2A2A2A2S44G0S39S43G1S6R5R4A2A2S37Z8R3A2A2A2A3F_;Fe;Ft;Fv;Frho;").
Proof using .
  intros rho v t e H.
  assert (SRL : forall v' s, sv_eqb v' v && (s =? 8 * t) && (0 <=? t) && (t <? 8) = true ->
            bv_unsigned (eval rho (SAlu ALU_SRL v' (SLit s))) = Z.shiftr (bv_unsigned (eval rho v)) (8 * t)).
  { intros v' s X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X X2]. apply andb_prop in X as [X0 X1].
    apply sv_eqb_sound in X0. apply Z.eqb_eq in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. subst v' s.
    apply srl_lit_unsigned. lia. }
  destruct e as [| |op a b| | | |sgn w a|]; cbn [byte_val_ok] in H; try discriminate.
  - destruct op; try discriminate. destruct b; try discriminate. rewrite (SRL _ _ H). reflexivity.
  - destruct sgn; [discriminate|]. destruct w as [|p]; [discriminate|].
    destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct p as [p|p|]; try discriminate.
    assert (E8 : forall x, bv_unsigned (eval rho (SExt false 8 x)) = bv_unsigned (eval rho x) mod 2 ^ 8).
    { intros x. cbn [eval]. rewrite U_zext_w by (cbn; lia). reflexivity. }
    apply Z_to_bv8_mod. rewrite E8, Z.mod_mod by lia.
    assert (DFLT : sv_eqb a v && (t =? 0) = true -> (bv_unsigned (eval rho a)) mod 2 ^ 8 = (bv_unsigned (eval rho v) ≫ (8 * t)) mod 2 ^ 8).
    { intros X. apply andb_prop in X as [X0 X1]. apply sv_eqb_sound in X0. apply Z.eqb_eq in X1. subst a t.
      rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity. }
    destruct a as [| |op a1 b1| | | | |]; try (exact (DFLT H)).
    destruct op; try (exact (DFLT H)). destruct b1; try (exact (DFLT H)).
    rewrite (SRL _ _ H). reflexivity.
Qed.

Lemma nth_enc_bytes : ltac2:(tb__ "0|3|
S2bS45Q40M0A1S2bS5fR1R3A2S22S45Q8M1A1M2S55G2R2S1dR4R3A2S44G1Z0A2A4S44G1S39S43G0R3A2S37Z8S3dR2A1A2A2A2A3F_;Ft;Fw;Fk;").
Proof using .
  intros k w. unfold enc_bytes. generalize (bv_unsigned w) as z. intros z t. revert k z.
  induction t as [|t IH]; intros [|k] z Ht; try lia.
  - cbn [Z_to_le_bytes nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. reflexivity.
  - cbn [Z_to_le_bytes nth]. rewrite (IH k) by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.

Lemma is_byte_cell_spec : ltac2:(tb__ "0|0|
S0S0S1fS3S22S26S4fR4R3R2R1A4S2cA3S23S22S1fSbR2A1Z1A3S23S22S27S1fA1S57S9R2A1R5A2S29S1fR3A2A3S22S26S49R4R3SaR2A1A3S2cA3A2A2F_;Fc;Ft;Fv;Foff;").
Proof using .
  intros off v t c H. unfold is_byte_cell in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply Z.eqb_eq in H1. destruct (same_atoms (c_off c) off) as [d|]; [|discriminate]. apply Z.eqb_eq in H2. subst d. auto.
Qed.

Lemma bytes_present_spec : ltac2:(tb__ "0|0|
S2dS3A1S0S0S2bS1fS1fS22S26S4bR6R5R4R2R3A5S2cA3S23S34R3R2A2S36R2S3aR3S3dR4A1A2A2A2S24S3S3S23S5bS3R1R9A3S23S22S1fSbR1A1Z1A3S23S22S27S1fA1S57S9R1A1R8A2S29S1fR4A2A3S22S26S49R7R4SaR1A1A3S2cA3A2A2A2Lc;A2F_;F_;Ft;Ft0;Fn;Fv;Foff;Fcells;").
Proof using .
  intros cells off v n. induction n as [|n IH]; intros t0 t H Ht; [lia|].
  cbn [bytes_present] in H. apply andb_prop in H as [H0 H1].
  destruct (Z.eq_dec t t0) as [->|Hne].
  - apply existsb_exists in H0 as (c & Hin & Hc). exists c. split; [exact Hin|]. apply is_byte_cell_spec. exact Hc.
  - apply (IH (t0 + 1)); [exact H1 | lia].
Qed.

Lemma byte_val_ok_t : ltac2:(tb__ "0|0|
S0S1fS0S22S26S49R3R2R1A3S2cA3S23S34Z0R3A2S36R3Z8A2A2F_;Fe;Ft;Fv;").
Proof using .
  intros v t e H.
  assert (A : forall v' s, sv_eqb v' v && (s =? 8 * t) && (0 <=? t) && (t <? 8) = true -> 0 <= t < 8).
  { intros v' s X. apply andb_prop in X as [X X3]. apply andb_prop in X as [X X2]. apply Z.leb_le in X2. apply Z.ltb_lt in X3. lia. }
  destruct e as [| |op a b| | | |sgn w a|]; cbn [byte_val_ok] in H; try discriminate.
  - destruct op; try discriminate. destruct b; try discriminate. eauto.
  - destruct sgn; [discriminate|]. destruct w as [|p]; [discriminate|].
    destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate.
    destruct p as [p|p|]; try discriminate.
    assert (DFLT : sv_eqb a v && (t =? 0) = true -> 0 <= t < 8).
    { intros X. apply andb_prop in X as [_ X1]. apply Z.eqb_eq in X1. lia. }
    destruct a as [| |op a1 b1| | | | |]; try (exact (DFLT H)).
    destruct op; try (exact (DFLT H)). destruct b1; try (exact (DFLT H)). eauto.
Qed.

Lemma tile_cell_holds : ltac2:(tb__ "0|3|
S4S0S1fS1fS48S2dS3A1S0S1fS0S23S36Z0M0R2A2S34R2Z8A2A2S36S3fR7R8A2S35Z2M1Z3fA2A2S34G0S3aS43Q40M2S6RbRaA2A2R9A2A2S34S3aS43G2S6RcRbA2A2R9A2S35G1Z40A2A2S52S3S5RdRcRbRaR9A5R8A3S22S26S4bR9R8R6G0S3eR7A1A5S2cA3S5RfReRdRcRbS7R9R8R7A3A6F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fcells;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms cells off k v Hk Hw Hb0 Hb1 HC HP.
  assert (BY : forall t, 0 <= t < k -> exists c, In c cells /\ c_width c = 1 /\ same_atoms (c_off c) off = Some t
                                          /\ byte_val_ok v t (c_val c) = true).
  { intros t Ht. apply (bytes_present_spec cells off v (Z.to_nat k) 0); [exact HP | lia]. }
  destruct (BY 0 ltac:(lia)) as (c0 & Hin0 & Hw0 & Hs0 & Hv0).
  pose proof (proj1 (Forall_forall _ _) HC c0 Hin0) as (A0 & B0 & R0).
  assert (E0 : soff rho off = soff rho (c_off c0)).
  { unfold soff. rewrite (same_atoms_eq rho _ _ Hs0). reflexivity. }
  assert (OFF : forall t c, 0 <= t < k -> In c cells -> c_width c = 1 -> same_atoms (c_off c) off = Some t ->
                soff rho (c_off c) = soff rho off + t).
  { intros t c Ht Hin Hwc Hs. pose proof (proj1 (Forall_forall _ _) HC c Hin) as (A & B & _).
    rewrite Hwc in B. rewrite (soff_diff_lit rho (c_off c) off t lo hi Hs); [| lia | rewrite E0; lia | exact Hw].
    rewrite snorm_small by lia. reflexivity. }
  unfold cell_holds. cbn [c_off c_width c_val].
  destruct (BY (k - 1) ltac:(lia)) as (cl & Hinl & Hwl & Hsl & Hvl).
  pose proof (proj1 (Forall_forall _ _) HC cl Hinl) as (Al & Bl & _). rewrite Hwl in Bl.
  rewrite (OFF (k - 1) cl ltac:(lia) Hinl Hwl Hsl) in Al, Bl.
  split; [rewrite E0; exact A0|]. split; [lia|].
  apply rd_bytes_of_nth.
  - unfold enc_bytes. apply length_Z_to_le_bytes.
  - unfold oaddr. rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_small by (rewrite E0; lia). rewrite Z2Nat.id by lia. rewrite E0 in *. lia.
  - intros j Hj. destruct (BY (Z.of_nat j) ltac:(lia)) as (c & Hin & Hwc & Hs & Hv).
    pose proof (proj1 (Forall_forall _ _) HC c Hin) as (A & B & R). rewrite Hwc in R. change (Z.to_nat 1) with 1%nat in R.
    rewrite (OFF (Z.of_nat j) c ltac:(lia) Hin Hwc Hs) in R.
    cbn [rd_bytes] in R. destruct (rd ms (oaddr rho base (soff rho off + Z.of_nat j))) as [b|] eqn:Rb; [|discriminate].
    cbn in R. injection R as Eb.
    rewrite (nth_enc_bytes (Z.to_nat k) (eval rho v) j Hj).
    replace (Z_to_bv 64 (bv_unsigned (oaddr rho base (soff rho off)) + Z.of_nat j)) with (oaddr rho base (soff rho off + Z.of_nat j)).
    + rewrite Rb, Eb. f_equal. unfold enc_bytes. cbn [Z_to_le_bytes].
      rewrite (byte_val_ok_sound rho v (Z.of_nat j) (c_val c) Hv). reflexivity.
    + unfold oaddr. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      rewrite (Z.mod_small (bv_unsigned (eval rho base) + soff rho off)) by (rewrite E0; lia). f_equal. lia.
Qed.

Lemma tile_obj_holds : ltac2:(tb__ "0|0|
S4S48S1S0S1fS0S1S22S27S1A1S4aR5R4R3R2A4S29S1R1A2A3S17Vsegs;R8R7R6A4S17Vsegs;R9R8R3A4F_;F_;Fo';Fv;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k v o' HT (Hb & Hwv & Hc & Hd & Hi). unfold tile_obj in HT.
  destruct ((0 <? k) && (k <=? 8) && dflt_writable (ob_dflt o) && bytes_present (ob_cells o) off v 0 (Z.to_nat k)) eqn:E; [|discriminate].
  injection HT as <-. apply andb_prop in E as [E HP]. apply andb_prop in E as [E _]. apply andb_prop in E as [E1 E2].
  apply Z.ltb_lt in E1. apply Z.leb_le in E2.
  unfold obj_holds, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [exact Hwv|]. split; [|split; [|exact Hi]].
  - constructor; [|exact Hc]. eapply tile_cell_holds; [lia | lia | lia | lia | exact Hc | exact HP].
  - intros off0 Hoff Hncov. apply (Hd off0 Hoff). intros Hcov. apply Hncov.
    unfold covered in *. apply Exists_cons_tl. exact Hcov.
Qed.

Lemma obj_range_tile : ltac2:(tb__ "0|0|
S4S1S0S1fS0S1S22S27S1A1S4aR5R4R3R2A4S29S1R1A2A3S22S2fS1fS1fA2S18R7R2A2S18R7R6A2A3F_;Fo';Fv;Fk;Foff;Fo;Frho;").
Proof using .
  intros rho o off k v o' HT. unfold tile_obj in HT.
  destruct ((0 <? k) && (k <=? 8) && dflt_writable (ob_dflt o) && bytes_present (ob_cells o) off v 0 (Z.to_nat k)); [|discriminate].
  injection HT as <-. reflexivity.
Qed.

Lemma mem_match_tile : ltac2:(tb__ "0|1|
S4S48S2dS1A1M0S1G0S0S1fS0S1S22S27S1A1S4aR6R4R3R2A4S29S1R1A2A3S10Vsegs;RaS30S1R8S2eS1R7R6A3A3R9A4S10Vsegs;RbS30S1R9S2eS1R3R7A3A3RaA4F_;F_;Fo';Fv;Fk;Foff;FL2;Fo;FL1;Fms;Frho;").
Proof using .
  intros rho ms L1 o L2 off k v o' HT (Hall & Hpd & Hfr).
  assert (RNG : forall rho', map (obj_range rho') (L1 ++ o' :: L2) = map (obj_range rho') (L1 ++ o :: L2)).
  { intros rho'. rewrite !map_app. cbn [map]. rewrite (obj_range_tile rho' o off k v o' HT). reflexivity. }
  split; [|split].
  - rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
    inversion B; subst. constructor; [|assumption]. eapply tile_obj_holds; eauto.
  - apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNG. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
  - unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
    rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; [|assumption].
    rewrite <- (obj_range_tile rho o off k v o' HT). assumption.
Qed.

Lemma split_at_nth' {A} : ltac2:(tb__ "0|1|
S2dVA;A1M0S2bVA;S22S27VA;A1S59VA;R3R2A3S29VA;R1A2A3S22G0R4S30VA;S53VA;R3R4A3S2eVA;R2S54VA;S32R3A1R4A3A3A3A3F_;Fx;Fi;Fl;").
Proof using .
  intros l i. revert l. induction i as [|i IH]; intros [|y l] x H; cbn in *; try discriminate.
  - injection H as <-. reflexivity.
  - f_equal. exact (IH l x H).
Qed.

Lemma obj_wf_tile : ltac2:(tb__ "0|0|
S20S1S0S1fS0S1S22S27S1A1S4aR5R4R3R2A4S29S1R1A2A3S22S26ScR7S7R5R4R3A3A2S2cA3S22S26S19R8R7A2S2cA3S22S26S19R9R4A2S2cA3F_;F_;F_;Fo';Fv;Fk;Foff;Fo;Fn;").
Proof using .
  intros n o off k v o' HT Hc Hw. unfold tile_obj in HT.
  destruct ((0 <? k) && (k <=? 8) && dflt_writable (ob_dflt o) && bytes_present (ob_cells o) off v 0 (Z.to_nat k)); [|discriminate].
  injection HT as <-. unfold obj_wf in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
  apply andb_prop in Hw as [Hw Hd]. apply andb_prop in Hw as [Hw Hcs]. rewrite Hw, Hc, Hcs, Hd. reflexivity.
Qed.

Theorem smatch_tile : ltac2:(tb__ "0|0|
S4S2S2bS0S1fS0S2S2fS2dS5eA1S5dA2S22S27S2A1S4eR7R6R5R4R3A5S29S2R2A2A3SdVsegs;R9R8R2A4SdVsegs;RaR4R3A4F_;F_;Fw;FS';Fv;Fk;Foff;Fi;FS;Frho;").
Proof using .
  intros rho S i off k v S' [tr [ms md]] HT Hsm. unfold tile_at in HT.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (tile_obj o off k v) as [o'|] eqn:Ho; [|discriminate].
  destruct (cell_wf (ss_next S) (mkCell off k v)) eqn:Hc; [|discriminate]. injection HT as <-.
  pose proof Hsm as (Hwf & Hpc & Hsvc & Hidle & Hrom & Hro & Hregs & Hfregs & Hfcsr & Hresv & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  apply (smatch_set_objs_next segs rho S _ (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) (ss_next S) (ss_lenient S)).
  - destruct S; exact Hsm.
  - rewrite (split_at_nth' (ss_objs S) i o Hi) in Hmem. eapply mem_match_tile; eauto.
  - unfold swf in *. cbn [ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    apply andb_prop in Hwf as [Hwf Hf]. apply andb_prop in Hwf as [Hwf Hobjs]. rewrite Hwf, Hf.
    rewrite (split_at_nth' (ss_objs S) i o Hi) in Hobjs. rewrite forallb_app in Hobjs |- *.
    apply andb_prop in Hobjs as [H1 H2]. cbn [forallb] in H2 |- *. apply andb_prop in H2 as [H2 H3].
    rewrite H1, H3, (obj_wf_tile _ _ _ _ _ _ Ho Hc H2). reflexivity.
Qed.

Lemma SPJ_tile : ltac2:(tb__ "0|0|
S47S4S2S2bS0S1fS0S2S56S22S27S2A1S4eR7R6R5R4R3A5S29S2R2A2A3S46Vsegs;RaR8R9R2A5S46Vsegs;RbR4RaR3A5F_;F_;Fw;FS';Fv;Fk;Foff;Fi;FS;Frho;FJ;").
Proof using . intros J rho S i off k v S' w HT [Hsm HJ]. split; [eapply smatch_tile; eauto | exact HJ]. Qed.

Lemma SPJ_tiles : ltac2:(tb__ "0|0|
S47S4S2dS2fS2fS2fS2bS0A2S1fA2S0A2A1S2S2S56S22S27S2A1S51R3R4A2S29S2R2A2A3S46Vsegs;R7R4R6R2A5S46Vsegs;R8R4R7R3A5F_;F_;Fw;FS';FS;Fts;Frho;FJ;").
Proof using .
  intros J rho ts. induction ts as [|[[[i off] k] v] rest IH]; intros S S' w HT Hw; cbn [tiles_at] in HT.
  - injection HT as <-. exact Hw.
  - destruct (tile_at S i off k v) as [S1|] eqn:E; [|discriminate]. eapply IH; [exact HT|]. eapply SPJ_tile; eauto.
Qed.
End T.

Definition recell (c : cell) (z' : Z) : option cell := ltac2:(tb__ "0|8|
S0S27S3A1M0Lx;SaVc;A1S1fS26G0L_;S2aS2aS3cZ0SbVc;A1M1A2S3bG1Z8M2A2A2S38S33R1S35Z2S37G2G1A2A2M3A2S33Vz';G3A2A2A2S29S3S7S9Vc;A1G1SeVz';A1A3A2S31S3A1M4X26x2Lz;S20G4Li;S40S0S0G4Lb;La;M5Lop;M6G6S41G5Lop;M7G7S26S21S0G4La;Lw;Lsgn;S20S0S1fG4Lk;Li;Ll;X0x8").

Fixpoint recell_nth (cells : list cell) (j : nat) (z' : Z) : option (list cell) :=
  match cells, j with
  | [], _ => None
  | c :: r, O => match recell c z' with Some c' => Some (c' :: r) | None => None end
  | c :: r, S j' => match recell_nth r j' z' with Some r' => Some (c :: r') | None => None end
  end.

Definition recell_at (S : sstate) (i j : nat) (z' : Z) : option sstate := ltac2:(tb__ "0|4|
S27S1A1S27S2A1M0Lx;S59S1S1aVS;A1M1Vi;A3S1S27S2dS3A1M2A1G0Lx;S4cS13R1A1Vj;Vz';A3G2S29S2S58VS;S30S1S53S1Vi;G1A3S2eS1S11S12R2A1S16R2A1S15R2A1R1S14R2A1A5S54S1S32Vi;A1G1A3A3A3A2A2Lcells';S31S2A1M3X27x2Lo;G3X27x2").

Section RC.
Variable segs : list Segment.

Lemma shiftr8_mod : ltac2:(tb__ "0|1|
S1fS1fS36Z0R1A2S22S1fS33S39R3Z8M0A2R2A2S33S39S33R3S37S35Z2G0A2R2A2A2G0A2R2A2A3F_;FM;Fz;").
Proof using .
  intros z M HM. rewrite !Z.shiftr_div_pow2 by lia.
  set (B := 2 ^ 8 * M).
  assert (HB : 0 < B) by (subst B; lia).
  pose proof (Z.div_mod z B ltac:(lia)) as E. pose proof (Z.mod_pos_bound z B HB) as R.
  set (q := z / B) in *. set (r := z mod B) in *.
  assert (E1 : z / 2 ^ 8 = q * M + r / 2 ^ 8).
  { rewrite E. subst B. replace (2 ^ 8 * M * q + r) with ((q * M) * 2 ^ 8 + r) by lia.
    rewrite Z.div_add_l by lia. reflexivity. }
  rewrite E1. rewrite Z.add_comm, Z.mod_add by lia. reflexivity.
Qed.

Lemma mod_pow2_mono' : ltac2:(tb__ "0|2|
S1fS1fS1fS23S34Z0R2A2S34R2R1A2A2S22S1fS33S33R4S35Z2M0R2A2A2S35G0R3A2M1A2S33R4G1A2A3F_;Fb;Fa;Fx;").
Proof using . intros x a b H. apply Z.mod_mod_divide. exists (2 ^ (b - a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma Z_to_le_bytes_mod : ltac2:(tb__ "0|0|
S2bS1fS22S2dS45Q8A1A1S5cR2R1A2S5cR2S33R1S35Z2S37Z8S3dR2A1A2A2A2A2A3Fz;Fk;").
Proof using .
  induction k as [|k IH]; intros z; [reflexivity|].
  cbn [Z_to_le_bytes].
  assert (P8 : 2 ^ (8 * Z.of_nat (S k)) = 2 ^ 8 * 2 ^ (8 * Z.of_nat k)).
  { rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
  pose proof (Z.pow_pos_nonneg 2 (8 * Z.of_nat k) ltac:(lia) ltac:(lia)) as PK.
  f_equal.
  - apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
    symmetry. apply mod_pow2_mono'. lia.
  - rewrite (IH (Z.shiftr z 8)), (IH (Z.shiftr (z mod 2 ^ (8 * Z.of_nat (S k))) 8)). f_equal.
    rewrite P8. apply shiftr8_mod. exact PK.
Qed.

Lemma recell_holds : ltac2:(tb__ "0|0|
S4S0S1fS1fS48S3S1fS3S22S27S3A1S50R3R2A2S29S3R1A2A3S5R9R8R7R6R5R4A6S5RaR9R8R7R6R3A6F_;F_;Fc';Fz';Fc;Fms;Fhi;Flo;Fbase;Frho;").
Proof using .
  intros rho base lo hi ms c z' c' H (A & B & R). unfold recell in H.
  destruct (c_val c) as [z| | | | | | |] eqn:Ev; try discriminate.
  destruct ((0 <? c_width c) && (c_width c <=? 8) && (z mod 2 ^ (8 * c_width c) =? z' mod 2 ^ (8 * c_width c))) eqn:C; [|discriminate].
  injection H as <-. apply andb_prop in C as [C E]. apply andb_prop in C as [C1 C2]. apply Z.ltb_lt in C1. apply Z.leb_le in C2. apply Z.eqb_eq in E.
  unfold cell_holds in *. cbn [c_off c_width c_val] in *. split; [exact A|]. split; [exact B|].
  rewrite R. f_equal. unfold enc_bytes. cbn [eval]. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
  rewrite (Z_to_le_bytes_mod (Z.to_nat (c_width c)) (z mod 2 ^ 64)), (Z_to_le_bytes_mod (Z.to_nat (c_width c)) (z' mod 2 ^ 64)).
  rewrite Z2Nat.id by lia. f_equal. rewrite !mod_pow2_mono' by lia. exact E.
Qed.

Lemma recell_nth_spec : ltac2:(tb__ "0|1|
S2dS3A1M0S2bS1fG0S22S27G0A1S4cR4R3R2A3S29G0R1A2A3S4S0S1fS1fS48S23S52S3S5R5R4R3R2R1A5RaA3S52S3S5R6R5R4R3R2A5R8A3F_;S1fS25SfR6R8R1A3SfR6RbR1A3A2Foff;A2Fms;Fhi;Flo;Fbase;Frho;F_;Fcells';Fz';Fj;Fcells;").
Proof using .
  induction cells as [|c r IH]; intros [|j] z' cells' H rho base lo hi ms; cbn [recell_nth] in H; try discriminate.
  - destruct (recell c z') as [c'|] eqn:E; [|discriminate]. injection H as <-. split.
    + intros HF. inversion HF; subst. constructor; [eapply recell_holds; eauto | assumption].
    + intros off. unfold covered. rewrite !Exists_cons. unfold in_cell.
      unfold recell in E. destruct (c_val c); try discriminate.
      destruct ((0 <? c_width c) && (c_width c <=? 8) && (z mod 2 ^ (8 * c_width c) =? z' mod 2 ^ (8 * c_width c))); [|discriminate].
      injection E as <-. cbn [c_off c_width]. tauto.
  - destruct (recell_nth r j z') as [r'|] eqn:E; [|discriminate]. injection H as <-. split.
    + intros HF. inversion HF; subst. constructor; [assumption|]. exact (proj1 (IH j z' r' E rho base lo hi ms) ltac:(assumption)).
    + intros off. unfold covered. rewrite !Exists_cons. pose proof (proj2 (IH j z' r' E rho base lo hi ms) off) as X. unfold covered in X. tauto.
Qed.

Lemma recell_nth_wf : ltac2:(tb__ "0|1|
S20S2dS3A1M0S2bS1fG0S22S27G0A1S4cR4R3R2A3S29G0R1A2A3S22S26S5aS3ScR6A1R5A3S2cA3S22S26S5aS3ScR7A1R3A3S2cA3F_;F_;Fcells';Fz';Fj;Fcells;Fn;").
Proof using .
  intros n cells. induction cells as [|c r IH]; intros [|j] z' cells' H Hw; cbn [recell_nth] in H; try discriminate;
    cbn [forallb] in Hw; apply andb_prop in Hw as [H1 H2].
  - destruct (recell c z') as [c'|] eqn:E; [|discriminate]. injection H as <-. cbn [forallb]. rewrite H2, andb_true_r.
    unfold recell in E. destruct (c_val c) eqn:Ev; try discriminate.
    destruct ((0 <? c_width c) && (c_width c <=? 8) && (z mod 2 ^ (8 * c_width c) =? z' mod 2 ^ (8 * c_width c))); [|discriminate].
    injection E as <-. unfold cell_wf in *. cbn [c_off c_width c_val]. rewrite Ev in H1. cbn [sv_below] in H1.
    rewrite andb_true_r in H1. rewrite H1. reflexivity.
  - destruct (recell_nth r j z') as [r'|] eqn:E; [|discriminate]. injection H as <-. cbn [forallb]. rewrite H1. exact (IH j z' r' E H2).
Qed.

Theorem smatch_recell : ltac2:(tb__ "0|0|
S4S2S2bS2bS1fS2S2fS2dS5eA1S5dA2S22S27S2A1S4dR6R5R4R3A4S29S2R2A2A3SdVsegs;R8R7R2A4SdVsegs;R9R4R3A4F_;F_;Fw;FS';Fz';Fj;Fi;FS;Frho;").
Proof using .
  intros rho S i j z' S' [tr [ms md]] H Hsm. unfold recell_at in H.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (recell_nth (ob_cells o) j z') as [cells'|] eqn:Hc; [|discriminate]. injection H as <-.
  pose proof Hsm as (Hwf & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) cells' (ob_dflt o)).
  apply (smatch_set_objs_next segs rho S _ (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) (ss_next S) (ss_lenient S)).
  - destruct S; exact Hsm.
  - rewrite (split_at_nth' (ss_objs S) i o Hi) in Hmem. destruct Hmem as (Hall & Hpd & Hfr).
    assert (RNG : forall rho', map (obj_range rho') (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S))
                              = map (obj_range rho') (firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S))).
    { intros rho'. rewrite !map_app. reflexivity. }
    split; [|split].
    + rewrite !Forall_app in Hall |- *. destruct Hall as (A & B). split; [exact A|].
      apply Forall_cons_iff in B as [Ho Brest]. constructor; [|exact Brest].
      destruct Ho as (H1 & H2 & H3 & H4 & H5).
      destruct (recell_nth_spec (ob_cells o) j z' cells' Hc rho (ob_base o) (obj_lo_of rho o) (obj_hi_of rho o) ms) as [HC HCOV].
      unfold obj_holds. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. unfold obj_lo_of, obj_hi_of in *. cbn [ob_lo ob_hi] in *.
      split; [exact H1|]. split; [exact H2|]. split; [exact (HC H3)|]. split; [|exact H5].
      intros off Hoff Hncov. apply (H4 off Hoff). intros Hcov. apply Hncov. apply (proj2 (HCOV off)). exact Hcov.
    + apply (proj2 (pairwise_disjoint_pdr rho _)). rewrite RNG. apply (proj1 (pairwise_disjoint_pdr rho _)). exact Hpd.
    + unfold mem_frame, outside_all in *. intros a Ha. apply Hfr.
      rewrite Forall_app in Ha |- *. destruct Ha as [Ha1 Ha2]. split; [exact Ha1|]. inversion Ha2; subst. constructor; assumption.
  - unfold swf in *. cbn [ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    apply andb_prop in Hwf as [Hwf Hf]. apply andb_prop in Hwf as [Hwf Hobjs]. rewrite Hwf, Hf.
    rewrite (split_at_nth' (ss_objs S) i o Hi) in Hobjs. rewrite forallb_app in Hobjs |- *.
    apply andb_prop in Hobjs as [X1 X2]. cbn [forallb] in X2 |- *. apply andb_prop in X2 as [X2 X3].
    rewrite X1, X3. replace (obj_wf (ss_next S) o') with true; [reflexivity|]. symmetry.
    unfold obj_wf in *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
    apply andb_prop in X2 as [X2 Xd]. apply andb_prop in X2 as [X2 Xc]. rewrite X2, Xd, (recell_nth_wf _ _ _ _ _ Hc Xc). reflexivity.
Qed.

Lemma SPJ_recell : ltac2:(tb__ "0|0|
S47S4S2S2bS2bS1fS2S56S22S27S2A1S4dR6R5R4R3A4S29S2R2A2A3S46Vsegs;R9R7R8R2A5S46Vsegs;RaR4R9R3A5F_;F_;Fw;FS';Fz';Fj;Fi;FS;Frho;FJ;").
Proof using . intros J rho S i j z' S' w H [Hsm HJ]. split; [eapply smatch_recell; eauto | exact HJ]. Qed.
End RC.
