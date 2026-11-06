(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sstate"; "cell"; "sobj"; "valuation"; "ss_next"; "c_off"; "c_width"; "c_val"; "smatch"; "SLit"; "eval"; "ob_cells"; "ss_facts"; "ss_objs"; "ss_pc"; "ss_regs"; "sv_below"; "SVar"; "cell_holds"; "mkCell"; "agree_below"; "dflt_writable"; "mkObj"; "mkSS"; "ob_base"; "ob_dflt"; "ob_hi"; "ob_lo"; "rw"; "sprop"; "ss_fcsr"; "ss_fregs"; "ss_lenient"; "ss_resv"; "@Corelib.Init.Datatypes"; "option"; "cons"; "list"; "Some"; "bool"; "nat"; "nil"; "None"; "app"; "true"; "S"; "prod"; "andb"; "false"; "@Corelib.Init.Logic"; "eq"; "and"; "ex"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Stdlib.ZArith.BinInt.Z"; "pow"; "add"; "le"; "mul"; "lt"; "of_nat"; "eqb"; "modulo"; "shiftr"; "sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.HdrPack"; "byte_of"; "find_bcell"; "pack4_rho"; "pack4_word"; "pack4_Z"; "pack4_at"; "pack4_vals_obj"; "bump"; "is_bcell"; "pack4_vals"; "pack4_obj"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "same_atoms"; "set_objs"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "bv"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Lists.ListDef"; "nth"; "firstn"; "skipn"; "Forall"; "@Stdlib.Lists.List"; "In"; "nth_error"; "find"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCall"; "rho_set_rw"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "stableJ"; "@Stdlib.PArith.BinPos.Pos"; "succ"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG SymSummary Glue3 SymBytes SymCall.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CellTile.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition is_bcell (off : sv) (t : Z) (c : cell) : bool := ltac2:(tb__ "0|0|
S2fS3cS7Vc;A1Z1A2S23S34A1S27Lx;S4bS6Vc;A1Voff;A2S34S3cR1Vt;A2Ld;S30X23x2A2").

Definition find_bcell (cells : list cell) (off : sv) (t : Z) : option sv := ltac2:(tb__ "0|0|
S23S2A1S23S0A1Lx;S56S2S48Voff;Vt;A2Vcells;A3S2S26S0S8R1A1A2Lc;S2aS0A1X23x2").

Definition pack4_vals_obj (o : sobj) (off : sv) : option (list sv) := ltac2:(tb__ "0|4|
S23S0A1S23S25S0A1M0A1Lx;M1S41ScVo;A1M2Voff;Z0A3S0G1S41G2Voff;Z1A3S0G1S41G2Voff;Z2A3S0G1S41G2Voff;Z3A3S0S26G0S24S0R4S24S0R3S24S0R2S24S0R1S29S0A1A3A3A3A3A2Le3;S2aG0A1M3X23x2Le2;G3X23x2Le1;G3X23x2Le0;G3X23x2").

Definition pack4_obj (o : sobj) (off : sv) (x : positive) : option sobj := ltac2:(tb__ "0|4|
S23S25S0A1M0A1S23S3A1M1Lx;S46Vo;Voff;A2G0S27G1L_;S16S1aVo;A1M2A1S26S3S17S19Vo;A1S1cVo;A1S1bVo;A1S24S2S14Voff;Z4S12Vx;A1A3ScVo;A1A3G2A5A2S2aS3A1M3X27x2Ll;G3X23x2").

Definition pack4_vals (S : sstate) (i : nat) (off : sv) : option (list sv) := ltac2:(tb__ "0|1|
S23S3A1S23S25S0A1M0A1Lx;S55S3SeVS;A1Vi;A3S3S46R1Voff;A2Lo;S2aG0A1X23x2").

Definition bump (S : sstate) : sstate := ltac2:(tb__ "0|0|
S18SfVS;A1S10VS;A1S20VS;A1S1fVS;A1S22VS;A1SeVS;A1SdVS;A1S5dS5VS;A1A1S21VS;A1A9").

Definition pack4_at (S : sstate) (i : nat) (off : sv) : option sstate := ltac2:(tb__ "0|5|
S23S3A1S23S1A1M0Lx;M1S55S3SeVS;A1M2Vi;A3S3G1S4aR1Voff;S5VS;A1M3A3S3S27G0L_;S11G3Voff;A2S26S1S4cS47VS;A1S2bS3S51S3Vi;G2A3S2bS3S24S3R1S29S3A1A3S52S3S2dVi;A1G2A3A3A3A2A2S2aS1A1M4X27x2Lo';G4X23x2Lo;G4X23x2").

Definition byte_of (rho : valuation) (e : sv) : Z := ltac2:(tb__ "0|0|
S3dS4dQ40SbVrho;Ve;A2A2S36Z2Z8A2A2").
Definition pack4_Z (rho : valuation) (es : list sv) : Z := ltac2:(tb__ "0|3|
S25S0A1M0S34Les;Ves;Z0M1S0G0G0S34Ll;R1G1S0G0G0S34Ll0;R1G1S0G0G0S34Ll1;R1G1S0G0G0S34Ll2;R1S37S37S37S40Vrho;R8A2S39S36Z2M2Z8A2S40Vrho;R6A2A2A2S39S36G2Z10A2S40Vrho;R4A2A2A2S39S36G2Z18A2S40Vrho;R2A2A2A2S0G0G1Ll3;Ls;X25x2Ll2;Le3;X25x2Ll1;Le2;X25x2Ll0;Le1;X25x2Ll;Le0;X25x2").
Definition pack4_word (rho : valuation) (es : list sv) : word := Z_to_bv 64 (pack4_Z rho es).
Definition pack4_rho (rho : valuation) (S : sstate) (es : list sv) : valuation := ltac2:(tb__ "0|0|
S59Vrho;S5VS;A1S43Vrho;Ves;A2A3").

Section P.
Variable segs : list Segment.

Lemma byte_of_range : ltac2:(tb__ "0|1|
S4S0S32S38Z0S40R2R1A2M0A2S3aG0S36Z2Z8A2A2A2Fe;Frho;").
Proof using . intros. unfold byte_of. apply Z.mod_pos_bound. lia. Qed.

Lemma pack4_Z_range : ltac2:(tb__ "0|1|
S4S0S0S0S0S32S38Z0S44R5S24S0R4S24S0R3S24S0R2S24S0R1S29S0A1A3A3A3A3A2M0A2S3aG0S36Z2Z20A2A2A2Fe3;Fe2;Fe1;Fe0;Frho;").
Proof using .
  intros. cbn [pack4_Z].
  pose proof (byte_of_range rho e0). pose proof (byte_of_range rho e1).
  pose proof (byte_of_range rho e2). pose proof (byte_of_range rho e3). lia.
Qed.

Lemma pack4_word_unsigned : ltac2:(tb__ "0|1|
S4S0S0S0S0S31S34S4dQ40S43R5S24S0R4S24S0R3S24S0R2S24S0R1S29S0A1A3A3A3A3M0A2A2S44R5G0A2A3Fe3;Fe2;Fe1;Fe0;Frho;").
Proof using .
  intros. unfold pack4_word. rewrite Z_to_bv_unsigned. pose proof (pack4_Z_range rho e0 e1 e2 e3).
  unfold bv_wrap. rewrite Z.mod_small; [reflexivity|]. change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma pack4_byte : ltac2:(tb__ "0|2|
S4S0S0S0S0S28S4fR1U4A2S31S34S3dS3eS44R7S24S0R6S24S0R5S24S0R4S24S0R3S29S0A1A3A3A3A3M0A2S39Z8M1S3bR2A1A2A2S36Z2G1A2A2S40R7S50S0R2G0SaZ0A1A4A2A3F_;Ft;Fe3;Fe2;Fe1;Fe0;Frho;").
Proof using .
  intros rho e0 e1 e2 e3 t Ht. cbn [pack4_Z].
  pose proof (byte_of_range rho e0) as R0. pose proof (byte_of_range rho e1) as R1.
  pose proof (byte_of_range rho e2) as R2. pose proof (byte_of_range rho e3) as R3.
  set (b0 := byte_of rho e0) in *. set (b1 := byte_of rho e1) in *. set (b2 := byte_of rho e2) in *. set (b3 := byte_of rho e3) in *.
  destruct t as [|[|[|[|t]]]]; try lia; cbn [nth Z.of_nat Z.mul Pos.mul Pos.of_succ_nat]; rewrite Z.shiftr_div_pow2 by lia.
  - rewrite Z.pow_0_r, Z.div_1_r. replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with (b0 + (b1 + 2 ^ 8 * b2 + 2 ^ 16 * b3) * 2 ^ 8) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
  - replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with (b0 + (b1 + (b2 + 2 ^ 8 * b3) * 2 ^ 8) * 2 ^ 8) by lia.
    change (2 ^ Z.pos (8 * 1)) with (2 ^ 8). rewrite Z.div_add by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_l, Z_mod_plus_full. apply Z.mod_small. lia.
  - replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with ((b0 + 2 ^ 8 * b1) + (b2 + b3 * 2 ^ 8) * 2 ^ 16) by lia.
    change (2 ^ Z.pos (8 * 2)) with (2 ^ 16). rewrite Z.div_add by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_l, Z_mod_plus_full. apply Z.mod_small. lia.
  - replace (b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2 + 2 ^ 24 * b3) with ((b0 + 2 ^ 8 * b1 + 2 ^ 16 * b2) + b3 * 2 ^ 24) by lia.
    change (2 ^ Z.pos (8 * 3)) with (2 ^ 24). rewrite Z.div_add by lia. rewrite Z.div_small by lia.
    rewrite Z.add_0_l. apply Z.mod_small. lia.
Qed.

Lemma is_bcell_spec : ltac2:(tb__ "0|0|
S0S34S2S31S27S48R3R2R1A3S2cA3S32S31S34S7R2A1Z1A3S31S23S34A1S4bS6R2A1R4A2S26S34R3A2A3A2F_;Fc;Ft;Foff;").
Proof using .
  intros off t c H. unfold is_bcell in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  destruct (same_atoms (c_off c) off) as [d|]; [|discriminate]. apply Z.eqb_eq in H2. subst d. auto.
Qed.

Lemma find_bcell_spec : ltac2:(tb__ "0|0|
S25S2A1S0S34S0S31S23S0A1S41R4R3R2A3S26S0R1A2A3S33S2S2S32S54S2R1R6A3S32S31S34S7R1A1Z1A3S32S31S23S34A1S4bS6R1A1R5A2S26S34R4A2A3S31S0S8R1A1R3A3A2A2A2Lc;A2F_;Fe;Ft;Foff;Fcells;").
Proof using .
  intros cells off t e H. unfold find_bcell in H.
  destruct (List.find (is_bcell off t) cells) as [c|] eqn:F; [|discriminate]. injection H as <-.
  apply find_some in F as [Hin Hc]. apply is_bcell_spec in Hc as [A B]. exists c. auto.
Qed.

Lemma pack4_vals_obj_spec : ltac2:(tb__ "0|1|
S3S0S25S0A1M0S31S23G0A1S46R3R2A2S26G0R1A2A3S33S0S0S33S0S0S33S0S0S33S0S0S32S31G0R6S24S0R4S24S0R3S24S0R2S24S0R1S29S0A1A3A3A3A3A3S28S4fR1U4A2S33S2S2S32S54S2R1ScRbA1A3S32S31S34S7R1A1Z1A3S32S31S23S34A1S4bS6R1A1RaA2S26S34S3bR3A1A2A3S31S0S8R1A1S50S0R3R9SaZ0A1A4A3A2A2A2Lc;A2F_;Ft;A2Le3;A2Le2;A2Le1;A2Le0;A2F_;Fes;Foff;Fo;").
Proof using .
  intros o off es H. unfold pack4_vals_obj in H.
  destruct (find_bcell (ob_cells o) off 0) as [e0|] eqn:F0; [|discriminate].
  destruct (find_bcell (ob_cells o) off 1) as [e1|] eqn:F1; [|discriminate].
  destruct (find_bcell (ob_cells o) off 2) as [e2|] eqn:F2; [|discriminate].
  destruct (find_bcell (ob_cells o) off 3) as [e3|] eqn:F3; [|discriminate]. injection H as <-.
  exists e0, e1, e2, e3. split; [reflexivity|]. intros t Ht.
  destruct t as [|[|[|[|t]]]]; try lia; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ].
  - destruct (find_bcell_spec _ _ _ _ F0) as (c & A & B & C & D). exists c; auto.
  - destruct (find_bcell_spec _ _ _ _ F1) as (c & A & B & C & D). exists c; auto.
  - destruct (find_bcell_spec _ _ _ _ F2) as (c & A & B & C & D). exists c; auto.
  - destruct (find_bcell_spec _ _ _ _ F3) as (c & A & B & C & D). exists c; auto.
Qed.

Lemma pack4_cell_holds : ltac2:(tb__ "0|5|
S4S35S4eQ40M0A1M1S0S34S34S5eS25S2A1S0S0S0S0S0S3aS3fR8R9A2S36Z2M2Z3fA2A2S38Z0M3S37S4dG0SbReRbA2A2RaA2A2S38S37S4dG0SbRfRcA2A2RaA2S36G2Z40A2A2S53S2S13R10RdRcRbRaA5R9A3S28S4fR1U4A2S33S2S2S32S54S2R1RdA3S32S31S34S7R1A1Z1A3S32S31S23S34A1S4bS6R1A1RcA2S26S34S3bR3A1A2A3S31S0S8R1A1S50S0R3S24S0RbS24S0RaS24S0R9S24S0R8S29S0A1M4A3A3A3A3SaG3A1A4A3A2A2A2Lc;A2F_;Ft;S31G1R10S43R12S24S0R9S24S0R8S24S0R7S24S0R6G4A3A3A3A3A2A3S31S27S11R12R10A2S2cA3S31S27S11R13RcA2S2cA3S13S59R15R14R13A3R12R11R10RfS14RdZ4S12R14A1A3A6F_;F_;F_;F_;F_;F_;F_;F_;Fe3;Fe2;Fe1;Fe0;Foff;Fcells;Fms;Fhi;Flo;Fbase;FW;Fx;Frho;").
Proof using .
  intros rho x W base lo hi ms cells off e0 e1 e2 e3 Hw Hb0 Hb1 HC BY HW Hbb Hob.
  set (rho' := rho_set_rw rho x W).
  assert (AG : agree_below x rho rho') by (apply agree_below_set_rw; lia).
  assert (Ebase : eval rho' base = eval rho base) by (symmetry; eapply eval_agree; eauto).
  assert (Eoff : soff rho' off = soff rho off) by (eapply soff_agree; [exact AG | exact Hob]).
  destruct (BY 0%nat ltac:(lia)) as (c0 & Hin0 & Hw0 & Hs0 & Hv0).
  pose proof (proj1 (Forall_forall _ _) HC c0 Hin0) as (A0 & B0 & R0).
  assert (E0 : soff rho off = soff rho (c_off c0)).
  { unfold soff. rewrite (same_atoms_eq rho _ _ Hs0). reflexivity. }
  assert (OFF : forall t c, (t < 4)%nat -> In c cells -> c_width c = 1 -> same_atoms (c_off c) off = Some (Z.of_nat t) ->
                soff rho (c_off c) = soff rho off + Z.of_nat t).
  { intros t c Ht Hin Hwc Hs. pose proof (proj1 (Forall_forall _ _) HC c Hin) as (A & B & _).
    rewrite Hwc in B. rewrite (soff_diff_lit rho (c_off c) off (Z.of_nat t) lo hi Hs); [| lia | rewrite E0; lia | exact Hw].
    rewrite snorm_small by lia. reflexivity. }
  unfold cell_holds. cbn [c_off c_width c_val]. rewrite Eoff. unfold oaddr. rewrite Ebase.
  destruct (BY 3%nat ltac:(lia)) as (cl & Hinl & Hwl & Hsl & Hvl).
  pose proof (proj1 (Forall_forall _ _) HC cl Hinl) as (Al & Bl & _). rewrite Hwl in Bl.
  rewrite (OFF 3%nat cl ltac:(lia) Hinl Hwl Hsl) in Al, Bl.
  split; [rewrite E0; exact A0|]. split; [cbn in Bl |- *; lia|].
  apply rd_bytes_of_nth.
  - unfold enc_bytes. apply length_Z_to_le_bytes.
  - rewrite Z_to_bv_unsigned. unfold bv_wrap. rewrite two64, Z.mod_small by (rewrite E0; lia). cbn [Z.to_nat Z.of_nat Pos.to_nat] in *. rewrite E0 in *. cbn. lia.
  - intros j Hj. change (Z.to_nat 4) with 4%nat in Hj.
    destruct (BY j Hj) as (c & Hin & Hwc & Hs & Hv).
    pose proof (proj1 (Forall_forall _ _) HC c Hin) as (A & B & R). rewrite Hwc in R. change (Z.to_nat 1) with 1%nat in R.
    rewrite (OFF j c Hj Hin Hwc Hs) in R.
    cbn [rd_bytes] in R. unfold oaddr in R.
    destruct (rd ms (Z_to_bv 64 (bv_unsigned (eval rho base) + (soff rho off + Z.of_nat j)))) as [b|] eqn:Rb; [|discriminate].
    cbn in R. injection R as Eb.
    change (Z.to_nat 4) with 4%nat. rewrite (nth_enc_bytes 4 (eval rho' (SVar x)) j Hj).
    replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned (eval rho base) + soff rho off)) + Z.of_nat j))
      with (Z_to_bv 64 (bv_unsigned (eval rho base) + (soff rho off + Z.of_nat j))).
    + rewrite Rb, Eb. f_equal. unfold enc_bytes. cbn [Z_to_le_bytes].
      cbn [eval]. subst rho'. rewrite rho_set_rw_at. rewrite HW. rewrite pack4_word_unsigned.
      apply Z_to_bv8_mod. rewrite (pack4_byte rho e0 e1 e2 e3 j Hj). rewrite Hv. unfold byte_of. reflexivity.
    + apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite two64.
      rewrite (Z.mod_small (bv_unsigned (eval rho base) + soff rho off)) by (rewrite E0; lia). f_equal. lia.
Qed.

Lemma split_at_nth'' {A} : ltac2:(tb__ "0|1|
S25VA;A1M0S28VA;S31S23VA;A1S55VA;R3R2A3S26VA;R1A2A3S31G0R4S2bVA;S51VA;R3R4A3S24VA;R2S52VA;S2dR3A1R4A3A3A3A3F_;Fx;Fi;Fl;").
Proof using .
  intros l i. revert l. induction i as [|i IH]; intros [|y l] x H; cbn in *; try discriminate.
  - injection H as <-. reflexivity.
  - f_equal. exact (IH l x H).
Qed.

Lemma smatch_bump : ltac2:(tb__ "0|0|
S4S1S2eS25S58A1S57A2S9Vsegs;R3R2R1A4S9Vsegs;R4S47R3A1R2A4F_;Fw;FS;Frho;").
Proof using .
  intros rho S [tr [ms md]] Hsm. unfold bump.
  apply (smatch_set_objs_next segs rho S _ (ss_objs S) (Pos.succ (ss_next S)) (ss_lenient S)).
  - destruct S; exact Hsm.
  - pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). exact Hmem.
  - apply swf_mono_next; [lia|]. exact (proj1 Hsm).
Qed.

Theorem smatch_pack4 : ltac2:(tb__ "0|1|
S4S1S28S0S1S25S0A1M0S2eS25S58A1S57A2S31S23S1A1S45R6R5R4A3S26S1R3A2A3S31S23G0A1S49R7R6R5A3S26G0R3A2A3S9Vsegs;R9R8R3A4S9Vsegs;S42RaR9R5A3R6R4A4F_;F_;F_;Fw;Fes;FS';Foff;Fi;FS;Frho;").
Proof using .
  intros rho S i off S' es [tr [ms md]] HP HV Hsm.
  unfold pack4_at in HP. unfold pack4_vals in HV.
  destruct (nth_error (ss_objs S) i) as [o|] eqn:Hi; [|discriminate].
  destruct (pack4_obj o off (ss_next S)) as [o'|] eqn:Ho; [|discriminate].
  destruct (sv_below (ss_next S) off) eqn:Hob; [|discriminate]. injection HP as <-.
  unfold pack4_obj in Ho. rewrite HV in Ho.
  destruct (dflt_writable (ob_dflt o)) eqn:Hdw; [|discriminate]. injection Ho as <-.
  destruct (pack4_vals_obj_spec o off es HV) as (e0 & e1 & e2 & e3 & -> & BY).
  set (nx := ss_next S). set (rho' := pack4_rho rho S [e0; e1; e2; e3]).
  assert (AG : agree_below nx rho rho') by (unfold rho', pack4_rho; apply agree_below_set_rw; lia).
  pose proof (smatch_agree segs rho rho' S _ AG Hsm) as Hsm'.
  pose proof (smatch_bump rho' S _ Hsm') as HsmB.
  pose proof Hsm as (Hwf & _). pose proof (swf_objs S Hwf) as Hwfo.
  rewrite (split_at_nth'' (ss_objs S) i o Hi) in Hwfo. rewrite forallb_app in Hwfo. apply andb_prop in Hwfo as [Hwf1 Hwf2].
  cbn [forallb] in Hwf2. apply andb_prop in Hwf2 as [Hwfo Hwf3].
  set (o' := mkObj (ob_base o) (ob_lo o) (ob_hi o) (mkCell off 4 (SVar nx) :: ob_cells o) (ob_dflt o)).

  pose proof HsmB as (HwfB & _ & _ & _ & _ & _ & _ & _ & _ & _ & HmemB & _). cbn [fst snd cfg_ms cfg_model] in HmemB.
  assert (EQB : ss_objs (bump S) = firstn i (ss_objs S) ++ o :: skipn (Datatypes.S i) (ss_objs S)).
  { unfold bump. cbn [ss_objs]. apply split_at_nth''. exact Hi. }
  assert (Hoh : obj_holds segs rho ms o).
  { pose proof Hsm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hmem & _). cbn [fst snd cfg_ms cfg_model] in Hmem.
    eapply mem_match_nth; [exact Hmem | exact Hi]. }
  assert (Hoh' : obj_holds segs rho' ms o').
  { destruct Hoh as (H1 & H2 & H3 & H4 & H5).
    destruct (obj_wf_parts nx o Hwfo) as (Wb & Wlo & Whi & Wcells).
    pose proof (eval_agree nx rho rho' _ AG Wb) as Eb.
    pose proof (soff_agree nx rho rho' _ AG Wlo) as Elo. pose proof (soff_agree nx rho rho' _ AG Whi) as Ehi.
    unfold obj_holds, obj_lo_of, obj_hi_of in *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
    rewrite <- Eb, Elo, Ehi.
    split; [exact H1|]. split; [exact H2|]. split; [|split].
    - constructor.
      + eapply (pack4_cell_holds rho nx (pack4_word rho [e0; e1; e2; e3]) (ob_base o) _ _ ms (ob_cells o) off e0 e1 e2 e3);
          [ pose proof H2 as _; lia | lia | lia | exact H3 | exact BY | reflexivity | exact Wb | exact Hob].
      + apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) H3 c Hin) as Hc.
        pose proof (proj1 (forallb_forall _ _) Wcells c Hin) as Wc. unfold cell_wf in Wc.
        apply andb_prop in Wc as [Wc Wv]. apply andb_prop in Wc as [_ Wo].
        unfold cell_holds in *. unfold oaddr in *. rewrite <- Eb. rewrite (soff_agree nx rho rho' _ AG Wo). rewrite <- (eval_agree nx rho rho' _ AG Wv). exact Hc.
    - intros off0 Hoff Hncov.
      assert (Hn2 : ~ covered rho (ob_cells o) off0).
      { intros C. apply Hncov. unfold covered in *. apply Exists_cons_tl. apply (proj2 (covered_agree nx rho rho' (ob_cells o) off0 AG Wcells)). exact C. }
      specialize (H4 off0 Hoff Hn2). pose proof AG as (_ & HL & _).
      destruct (ob_dflt o); cbn in *; rewrite <- ?HL; exact H4.
    - eapply dflt_inv_agree; [exact AG | apply obj_wf_dflt; exact Hwfo | exact H5]. }
  unfold set_objs. cbn [bump ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient].
  assert (RNG : obj_range rho' o' = obj_range rho' o) by reflexivity.
  pose proof (smatch_set_objs_next segs rho' (bump S) _ (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)) (Pos.succ nx) (ss_lenient S) HsmB) as X.
  unfold bump in X. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient] in X. cbn [app]. cbn [app] in X.
  apply X.
  - rewrite EQB in HmemB.
    change (firstn i (ss_objs S) ++ o' :: skipn (Datatypes.S i) (ss_objs S)) with (firstn i (ss_objs S) ++ [o'] ++ skipn (Datatypes.S i) (ss_objs S)).
    apply mem_match_replace with (o := o).
    + exact HmemB.
    + constructor; [exact Hoh'|]. constructor.
    + destruct HmemB as (_ & Hpd & _). apply pairwise_disjoint_pdr in Hpd.
      rewrite !map_app in Hpd |- *. cbn [map app] in Hpd |- *. rewrite RNG. exact Hpd.
    + intros x. split.
      * intros Hx. exists o'. split; [cbn; auto|]. rewrite RNG. exact Hx.
      * intros (o'' & Hin'' & Hx). destruct Hin'' as [<-|[]]. rewrite RNG in Hx. exact Hx.
  - pose proof (swf_objs_replace (bump S) (firstn i (ss_objs S)) o (skipn (Datatypes.S i) (ss_objs S)) [o'] HwfB EQB) as W.
    unfold set_objs, bump in W. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next ss_lenient app] in W.
    apply W. cbn [forallb]. rewrite andb_true_r.
    unfold obj_wf in *. subst o'. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt forallb].
    pose proof (obj_wf_mono nx (Pos.succ nx) o ltac:(lia) Hwfo) as Wm. unfold obj_wf in Wm.
    apply andb_prop in Wm as [Wm Wd]. apply andb_prop in Wm as [Wm Wcs]. subst nx. rewrite Wm, Wcs, Wd.
    replace (cell_wf (Pos.succ (ss_next S)) (mkCell off 4 (SVar (ss_next S)))) with true; [reflexivity|]. symmetry.
    unfold cell_wf. cbn [c_off c_width c_val]. rewrite (sv_below_mono (ss_next S) (Pos.succ (ss_next S)) off ltac:(lia) Hob).
    cbn [sv_below]. replace (ss_next S <? Pos.succ (ss_next S))%positive with true; [reflexivity|]. symmetry. apply Pos.ltb_lt. lia.
Qed.

Lemma pack4_rho_nx : ltac2:(tb__ "0|0|
S4S1S25S0A1S31S4eQ40A1S1dS42R3R2R1A3S5R2A1A2S43R3R1A2A3Fes;FS;Frho;").
Proof using . intros. unfold pack4_rho. apply rho_set_rw_at. Qed.
Lemma pack4_rho_agree : ltac2:(tb__ "0|0|
S4S1S25S0A1S15S5R2A1R3S42R3R2R1A3A3Fes;FS;Frho;").
Proof using . intros. unfold pack4_rho. apply agree_below_set_rw. lia. Qed.
Lemma pack4_next : ltac2:(tb__ "0|0|
S1S28S0S1S31S23S1A1S45R4R3R2A3S26S1R1A2A3S32S31S35S5R2A1S5dS5R5A1A1A3S32S31S25S1eA1SdR2A1SdR5A1A3S32S31S25S0A1S10R2A1S10R5A1A3S31S34SfR2A1SfR5A1A3A2A2A2F_;FS';Foff;Fi;FS;").
Proof using .
  intros S i off S' H. unfold pack4_at in H.
  destruct (nth_error (ss_objs S) i); [|discriminate]. destruct (pack4_obj _ _ _); [|discriminate].
  destruct (sv_below _ _); [|discriminate]. injection H as <-. repeat split; reflexivity.
Qed.

Lemma SPJ_pack4 : ltac2:(tb__ "0|1|
S5bS4S1S28S0S1S25S0A1M0S5fS31S23S1A1S45R6R5R4A3S26S1R3A2A3S31S23G0A1S49R7R6R5A3S26G0R3A2A3S5cS5R8A1RaA2S5aVsegs;RbR9RaR4A5S5aVsegs;RcR7S42RbRaR6A3R5A5F_;F_;F_;F_;Fw;Fes;FS';Foff;Fi;FS;Frho;FJ;").
Proof using .
  intros J rho S i off S' es w HP HV HJ [Hsm HK]. split.
  - eapply smatch_pack4; eauto.
  - eapply HJ; [apply pack4_rho_agree | exact HK].
Qed.

End P.
