(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "not"; "or"; "ex"; "iff"; "@Corelib.Numbers.BinNums"; "Z"; "positive"; "@Corelib.Init.Datatypes"; "bool"; "list"; "true"; "nat"; "option"; "length"; "Some"; "false"; "prod"; "None"; "fst"; "pair"; "snd"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "Z_to_bv"; "bv_extract"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "sobj"; "cell"; "sprop"; "valuation"; "soff"; "obj_holds"; "sstate"; "enc_bytes"; "ob_dflt"; "obj_wf"; "sv_below"; "eval"; "ob_base"; "holds"; "obj_hi_of"; "obj_lo_of"; "obj_range"; "oaddr"; "odefault"; "c_width"; "dflt_writable"; "ss_objs"; "SLit"; "mkCell"; "rom_ok"; "ss_next"; "swf"; "tfact"; "c_off"; "c_val"; "dflt_inv"; "fldv"; "mem_match"; "ranges_disjoint"; "ro_clear"; "ss_facts"; "tf_holds"; "DArr"; "DUnknown"; "ext_low"; "is_arr"; "rd"; "rd_bytes"; "smatch"; "ss_pc"; "cell_wf"; "dflt_wf"; "mkObj"; "ob_cells"; "ob_hi"; "ob_lo"; "pairwise_disjoint"; "ro_addr"; "ss_resv"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "of_nat"; "pow"; "to_nat"; "modulo"; "mul"; "opp"; "sub"; "to_N"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "machine_state"; "ms_mem"; "ms_rom"; "write_to_mem"; "wview"; "store_ok"; "@Stdlib.Lists.List"; "nth_error"; "In"; "@Corelib.Init.Peano"; "lt"; "le"; "@Corelib.Lists.ListDef"; "Forall"; "nth"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "mk_addk"; "obj_store_d"; "cell_rel"; "crel"; "obj_store"; "snorm"; "store_cells"; "CDisj"; "CLit"; "arr_after_store"; "get_reg"; "list_set"; "list_upd"; "lit_overlaps"; "mk_alu"; "msz"; "set_objs"; "sym_store"; "tf_mentions"; "CRExact"; "CRNone"; "cell_read"; "flds_apart"; "immI"; "instr_at"; "mk_ext"; "narrow"; "prove_sprop"; "read_cells"; "set_pc"; "store_xs"; "tf_inst"; "@LinuxProcessSemantics.LinuxProcessSem.BvBase"; "Z_to_le_bytes"; "@LinuxProcessSemantics.Riscv.Instr"; "msize"; "ALU_SRL"; "instr"; "Store"; "@Corelib.Init.Nat"; "add"; "@Stdlib.NArith.BinNat.N"; "mul"; "of_nat"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "mkCfg"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundW.W"; "obj_with_dflt"; "@LinuxProcessSemantics.Riscv.Sem"; "low32"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundI"; "next_rel"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundM"; "pdr"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymLin SymSoundM.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section W.
Variable segs : list Segment.

Lemma write_to_mem_out : ltac2:(tb__ "0|6|
S9S15Q8A1M0A1S15Q40M1A1M2ScG0A1M3F_;G2G2S50S51S16G1R2A2M4S53SdG0R4A2A1A2S54Z2Z40A2A2S2S1S50S16G1R3A2M5G4A2S52G4S51G5S53SdG0R5A2A1A2A2A2A1S0G3S5eR5R4R6R3A4R5R3A1A3F_;F_;Fx;Fa;Fm;Fbs;").
Proof using .
  induction bs as [|b rest IH]; intros m a x Hnw Hout; [reflexivity|].
  cbn [write_to_mem length] in *. rewrite Nat2Z.inj_succ in *.
  destruct rest as [|b' rest'].
  - cbn. unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned a)) as [E|E]; [|reflexivity].
    exfalso. apply Hout. cbn [length Z.of_nat]. lia.
  - rewrite IH.
    + unfold bv_eqb. destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned a)) as [E|E]; [|reflexivity].
      exfalso. apply Hout. lia.
    + rewrite u_add1; [|cbn [length] in Hnw; lia]. cbn [length] in *. lia.
    + rewrite u_add1; [|cbn [length] in Hnw; lia]. cbn [length] in *. intros H. apply Hout. lia.
Qed.

Lemma write_to_mem_in : ltac2:(tb__ "0|5|
S9S15Q8M0A1M1A1S15Q40M2A1M3ScG1A1M4F_;G3SbS50S51S16G2R2A2S53SdG1R4A2A1A2S54Z2Z40A2A2S63R2SdG1R5A2A2S0G4S5eR5R4R6S17G2S51S16G2R4A2S53R3A1A2A2A4SeG1S66G1R3R6S17G0Z0A2A4A2A3F_;F_;Fj;Fa;Fm;Fbs;").
Proof using .
  induction bs as [|b rest IH]; intros m a j Hnw Hj; cbn [length] in *; [lia|].
  rewrite Nat2Z.inj_succ in Hnw. cbn [write_to_mem].
  destruct j as [|j].
  - cbn [nth Z.of_nat]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
    destruct rest as [|b' rest'].
    + cbn. unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
    + rewrite write_to_mem_out.
      * unfold bv_eqb. rewrite Z.eqb_refl. reflexivity.
      * rewrite u_add1; [cbn [length] in *; lia | cbn [length] in *; lia].
      * rewrite u_add1; [| cbn [length] in *; lia]. lia.
  - cbn [nth]. rewrite Nat2Z.inj_succ.
    replace (bv_unsigned a + Z.succ (Z.of_nat j)) with (bv_unsigned (a + 1)%bv + Z.of_nat j)
      by (rewrite u_add1; lia).
    apply IH; [rewrite u_add1; lia | lia].
Qed.

Lemma store_bytes_enc : ltac2:(tb__ "0|5|
S88S15Q40M0A1S0S9S15Q8M1A1A1M2S88G2Lsz;R2S87U1S16G1S18G0Q0M3G1R1A4A2A2S87U2S16Q10M4S18G0G3G4R1A4A2A2S87U4S16Q20S94R1A1A2A2S87U8S16G0R1A2A2X88x4S21S55S76R2A1A1R1A2A3Fv;Fsz;").
Proof using .
  intros sz v. unfold enc_bytes. destruct sz.
  - change (Z.to_nat (msz SZ1)) with 1%nat. rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap.
    change (bv_modulus 8) with (2 ^ (8 * Z.of_nat 1)). apply Z_to_le_bytes_mod.
  - change (Z.to_nat (msz SZ2)) with 2%nat. rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap.
    change (bv_modulus 16) with (2 ^ (8 * Z.of_nat 2)). apply Z_to_le_bytes_mod.
  - change (Z.to_nat (msz SZ4)) with 4%nat. unfold low32. rewrite bv_extract_unsigned, Z.shiftr_0_r. unfold bv_wrap.
    change (bv_modulus 32) with (2 ^ (8 * Z.of_nat 4)). apply Z_to_le_bytes_mod.
  - reflexivity.
Qed.

Lemma rd_unchanged : ltac2:(tb__ "0|2|
S5bS5bS15Q40A1M0S0ScS15Q8A1A1M1S5cR2R1A2S5cR3R1A2A3S0G0G1F_;S5dR3A1S5dR4A1A3S0G1S43R4R3A2S43R5R3A2A3F_;F_;Fx;Fms';Fms;").
Proof using . intros ms ms' x Hm Hr. unfold rd, ms_read_byte. rewrite Hm, Hr. reflexivity. Qed.

Lemma rd_bytes_unchanged : ltac2:(tb__ "0|6|
S5bS5bS15Q40M0A1M1SbS0G1ScS15Q8A1M2A1M3F_;S5dR3A1S5dR4A1A3S50S51S16G0R3A2S53R2A1M4A2S54Z2Z40A2A2SbS63R1R4A2S0G3S5cR7S17G0S51S16G0R6A2G4A2A2M5A2S5cR8G5A2A3F_;Fj;S0ScS9G2A1A1S44R6R5R4A3S44R7R5R4A3A3F_;F_;F_;Fk;Fa;Fms';Fms;").
Proof using .
  intros ms ms' a k Hr. revert a. induction k as [|k IH]; intros a Hnw Hall; [reflexivity|].
  cbn. rewrite (rd_unchanged ms ms' a).
  - destruct k as [|k'].
    + reflexivity.
    + rewrite IH; [reflexivity | |].
      * rewrite u_add1; [| rewrite Nat2Z.inj_succ in Hnw; lia]. rewrite Nat2Z.inj_succ in Hnw. lia.
      * intros j Hj. rewrite u_add1 by (rewrite Nat2Z.inj_succ in Hnw; lia).
        specialize (Hall (S j) ltac:(lia)). rewrite Nat2Z.inj_succ in Hall.
        replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.succ (Z.of_nat j)) by lia. exact Hall.
  - specialize (Hall 0%nat ltac:(lia)). cbn [Z.of_nat] in Hall. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in Hall. exact Hall.
  - exact Hr.
Qed.

Lemma store_cells_spec : ltac2:(tb__ "0|7|
S9S1cA1S9S1bA1M0S19S6S1bS62S1bR1S12G0S8S6dR5R4R3R2A4A3A3S4S1bS1bS1S62S1bR1R6A3S3S1S0S6aS69R7R5R4R1A4S6eA3S0S1bR3R1A3A2S3S4S6S6S1S0S6aS69R8R6R5R2A4S6fR1A1A3M1S1S0S8S74R1S2dR2A1M2R5A3M3SfA3S0S1bR4R2A3A2A2Ld;A2S3S4S6S6S1G1S1S0S8G3SaA3M4S1S52R1Z0A2S0S1bR4S31S36R2A1S58R1A1S37R2A1M5A3A3A2A2A2Ld;A2S4S6S6S1G1S1G4S1S52R5S51R1G2A2M6A2S0S1bR4S31S67R6R5A2S59G6R5A2S75S89G5S30S57Z8S59R5R1A2A2A1A3A3A3A2A2A2Ld;A2A2A2A2A2Lc;A2F_;Fc';Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c rest IH]; intros c' Hin; cbn [store_cells] in Hin; [destruct Hin|].
  destruct (store_cells facts rest off k) as [rest' taint] eqn:E. cbn [fst] in IH.
  Local Ltac rest_case IH Hin := destruct (IH _ Hin) as (c0 & Hc0 & R); exists c0; split; [right; exact Hc0 | exact R].
  destruct (cell_rel facts off k c) as [d| |] eqn:Hcr; cbn [fst] in Hin.
  - destruct (lit_overlaps d (c_width c) k) eqn:Ho; cbn [fst] in Hin.
    + apply in_app_or in Hin as [Hin|Hin].
      * destruct (d <? 0) eqn:E1; [|destruct Hin]. apply Z.ltb_lt in E1. destruct Hin as [<-|[]].
        exists c. split; [left; reflexivity|]. right; right; left. exists d. auto.
      * apply in_app_or in Hin as [Hin|Hin].
        -- destruct (k <? d + c_width c) eqn:E2; [|destruct Hin]. apply Z.ltb_lt in E2. destruct Hin as [<-|[]].
           exists c. split; [left; reflexivity|]. right; right; right. exists d. auto.
        -- rest_case IH Hin.
    + destruct Hin as [<-|Hin]; [|rest_case IH Hin].
      exists c. split; [left; reflexivity|]. right; left. exists d. auto.
  - destruct Hin as [<-|Hin]; [|rest_case IH Hin].
    exists c. split; [left; reflexivity|]. left. auto.
  - rest_case IH Hin.
Qed.

Lemma store_cells_notaint : ltac2:(tb__ "0|4|
S9S1cA1S9S1bA1M0S19S6S1bS0S8S14G0S8S6dR5R4R3R2A4A3SfA3S62S1bR2R5A3S12G0S8S6dR7R6R5R4A4A3G0S3S1S0S6aS69R8R6R5R4A4S6eA3S62S1bR4R1A3A2S4S6S6S1S0S6aS69R9R7R6R5A4S6fR1A1A3S3S1S0S8S74R1S2dR5A1M1R6A3M2SfA3S62S1bR5R2A3A2S1S0S8G2SaA3S1S52R1Z0A2S62S1bS31S36R6A1S58R2A1S37R6A1M3A3R3A3F_;S52R6S51R1G1A2A2S62S1bS31S67R8R7A2S59S51R2S2dR6A1A2R7A2S75S89G3S30S57Z8S59R7R2A2A2A1A3A3R3A3F_;A2A2A2A2Ld;A2A2Tcells';F_;F_;Fc;Fk;Foff;Fcells;Ffacts;").
Proof using .
  intros facts cells off k. induction cells as [|c0 rest IH]; intros c Ht Hin; [destruct Hin|].
  cbn [store_cells] in Ht |- *.
  destruct (store_cells facts rest off k) as [rest' taint] eqn:E. cbn [fst snd] in IH.
  assert (SUB : forall x, In x rest' -> In x (fst (let '(r, t) := (rest', taint) in
            match cell_rel facts off k c0 with
            | CLit d => if lit_overlaps d (c_width c0) k
                        then ((if d <? 0 then [mkCell (c_off c0) (- d) (c_val c0)] else [])
                              ++ (if k <? d + c_width c0
                                  then [mkCell (mk_addk off k) (d + c_width c0 - k) (mk_alu ALU_SRL (c_val c0) (SLit (8 * (k - d))))]
                                  else []) ++ r, t)
                        else (c0 :: r, t)
            | CDisj => (c0 :: r, t)
            | CUnk => (r, true)
            end))).
  { intros x Hx. destruct (cell_rel facts off k c0) as [d| |]; cbn [fst].
    - destruct (lit_overlaps d (c_width c0) k); cbn [fst]; [|right; exact Hx].
      apply in_or_app. right. apply in_or_app. right. exact Hx.
    - right. exact Hx.
    - exact Hx. }
  assert (Ht' : taint = false).
  { destruct (cell_rel facts off k c0) as [d| |]; cbn [snd] in Ht.
    - destruct (lit_overlaps d (c_width c0) k); cbn [snd] in Ht; exact Ht.
    - exact Ht.
    - discriminate. }
  destruct Hin as [E0|Hin].
  - subst c0. destruct (cell_rel facts off k c) as [d| |] eqn:Hcr; cbn [fst snd] in Ht |- *.
    + right. exists d. split; [reflexivity|].
      destruct (lit_overlaps d (c_width c) k) eqn:Ho; cbn [fst].
      * right. split; [reflexivity|]. split.
        -- intros Hd. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt d 0) Hd). left. reflexivity.
        -- intros Hk. apply in_or_app. right. apply in_or_app. left. rewrite (proj2 (Z.ltb_lt _ _) Hk). left. reflexivity.
      * left. split; [reflexivity|]. left. reflexivity.
    + left. split; [reflexivity|]. left. reflexivity.
    + discriminate.
  - destruct (IH c Ht' Hin) as [[Hcr HinR] | (d & Hcr & R)].
    + left. split; [exact Hcr|]. apply SUB. exact HinR.
    + right. exists d. split; [exact Hcr|].
      destruct R as [[Ho HinR] | (Ho & R1 & R2)].
      * left. split; [exact Ho | apply SUB; exact HinR].
      * right. split; [exact Ho|]. split; intros H; apply SUB; auto.
Qed.

Lemma write_to_mem_grows : ltac2:(tb__ "0|4|
S9S15Q8A1M0A1S15Q40A1M1ScG0A1M2Fx;G1G1S2S0G2R3R1A1S11G0A1M3A3A1S2S0G2S5eR4R3R5R2A4G3A3A1F_;Fx;Fa;Fm;Fbs;").
Proof using .
  induction bs as [|b rest IH]; intros m a x Hx; cbn; [exact Hx|].
  apply IH. destruct (bv_eqb x a); [discriminate | exact Hx].
Qed.

Lemma write_to_mem_keeps_none : ltac2:(tb__ "0|4|
S9S15Q8A1M0A1S15Q40A1M1ScG0A1M2F_;G1G1S0G2S5eR3R2R4R1A4S11G0A1M3A3S0G2R4R2A1G3A3F_;Fx;Fa;Fm;Fbs;").
Proof using .
  intros bs m a x H. destruct (m x) eqn:E; [|reflexivity].
  exfalso. apply (write_to_mem_grows bs m a x); [rewrite E; discriminate | exact H].
Qed.

Lemma wview_mono : ltac2:(tb__ "0|5|
S15Q40A1M0ScS15Q8A1M1A1M2Fx;M3G3G0G0S2S0G2R4R1A1S11G1A1M4A3A1S2S0G2R4R2A1G4A3A1F_;Fy;S2S0G2S5fVsegs;R4R2A3G4A3A1S2S0G2S5fVsegs;R4R3A3G4A3A1F_;F_;Fx;Fm';Fm;").
Proof using .
  intros m m' x Hg Hx. unfold wview in *.
  destruct (m' x) as [b'|] eqn:E'; [discriminate|].
  destruct (m x) as [b|] eqn:E.
  - exfalso. apply (Hg x); [rewrite E; discriminate | exact E'].
  - exact Hx.
Qed.

Lemma snorm_id : ltac2:(tb__ "0|1|
S6S1S50S58S54Z2Z3fA2M0A1R1A2S52R1G0A2A2S0S6S6cR2A1R2A3F_;Fz;").
Proof using .
  intros z Hz. unfold snorm.
  destruct (Z.lt_ge_cases z 0).
  - replace (z mod 2 ^ 64) with (z + 2 ^ 64).
    2:{ symmetry. replace z with ((z + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec (z + 2 ^ 64) (2 ^ 63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia.
Qed.

Lemma snorm_of_mod : ltac2:(tb__ "0|0|
S6S0S6S6cS56R1S54Z2Z40A2A2A1S6cR1A1A3Fz;").
Proof using . intros z. unfold snorm. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma soff_mk_addk : ltac2:(tb__ "0|2|
S1dS19S6S1S50S58S54Z2Z3fA2M0A1S51S1eR3R2A2R1A2M1A2S52G1G0A2A2S0S6S1eR4S67R3R2A2A2S51S1eR4R3A2R2A2A3F_;Fk;Fe;Frho;").
Proof using .
  intros rho e k H. unfold soff at 1. rewrite mk_addk_sound, bv_add_Z, signed_lit.
  rewrite <- (snorm_id (soff rho e + k)) by exact H.
  rewrite <- (snorm_of_mod (bv_unsigned (eval rho e) + k)), <- (snorm_of_mod (soff rho e + k)).
  f_equal. change (bv_unsigned (eval rho e)) with (U rho e).
  rewrite <- (soff_mod rho e). apply Zplus_mod_idemp_l.
Qed.

Lemma obj_holds_store : ltac2:(tb__ "0|1|
S1dS7S5bS5bS1aS9S1cA1S19S6S19S32Vsegs;R7A2S65S1cS27RaA1R5A3S1fVsegs;RbR9R7A4S0S8S23RbR8A2SaA3S0S8S2eS22R9A1A1SaA3S0S8S42S22RaA1A1SfA3S50S29RfRbA2S1eRfR9A2A2S50S51S1eR10RaA2R9A2S28R10RcA2A2S52Z0RaA2S50RbZ8A2S0S15Q40A1ScS15Q8A1A1F_;M0S5dR10A1S5dR11A1A3S0G0S5cR11A1S5eS5cR12A1S2bR14S26R10A1S1eR14ReA2A3S21S55RdA1S25R14RcA2A2A3A3S1fVsegs;R15R12S6bR10R11RfReRdA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Ffacts;Fo;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o facts off k v Hrom Hf Hoh Howf Hdw Hna Hlo Hhi Hk Hk8 Hr Hm.
  pose proof Hoh as (Hb & Hw0 & Hcells & Hd & Hdl).
  assert (Hw : forall off0, obj_lo_of rho o <= off0 < obj_hi_of rho o ->
               wview segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off0)) <> None)
    by (intros off0 Hoff0; apply Hw0; [exact Hoff0 | exact Hdw]).
  set (A := soff rho off) in *.
  unfold obj_lo_of, obj_hi_of in *.
  pose proof (soff_range rho (ob_hi o)) as Rhi. pose proof (soff_range rho (ob_lo o)) as Rlo.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) A) = bv_unsigned (eval rho (ob_base o)) + A)
    by (apply oaddr_unsigned; lia).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  assert (Hout : forall off', ~ (A <= off' < A + k) -> 0 <= bv_unsigned (eval rho (ob_base o)) + off' < 2 ^ 64 ->
            ms_mem ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off')) = ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off'))).
  { intros off' Hoff' Hrange. rewrite Hm. apply write_to_mem_out.
    - rewrite Ha, Hlen, Z2Nat.id by lia. lia.
    - rewrite Ha, Hlen, Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia. }
  assert (Hrdu : forall off' k', soff rho (ob_lo o) <= off' -> off' + k' <= soff rho (ob_hi o) -> 0 < k' ->
            (off' + k' <= A \/ A + k <= off') ->
            rd_bytes ms' (oaddr rho (ob_base o) off') (Z.to_nat k') = rd_bytes ms (oaddr rho (ob_base o) off') (Z.to_nat k')).
  { intros off' k' H1 H2 H3 H4. apply rd_bytes_unchanged; [exact Hr| |].
    - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hout; lia. }

  assert (Hrd' : forall off', soff rho (ob_lo o) <= off' < soff rho (ob_hi o) ->
            exists b, rd ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off')) = Some b).
  { intros off' Hoff'. destruct (obj_byte_readable segs rho ms o off' n Hrom Howf Hoh Hoff') as [b Hbb].
    unfold rd, ms_read_byte in *. rewrite Hr.
    destruct (ms_mem ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off'))) as [b'|] eqn:E'; [eexists; reflexivity|].
    rewrite Hm in E'. apply write_to_mem_keeps_none in E'. rewrite E' in Hbb. exists b. exact Hbb. }
  unfold obj_store. destruct (store_cells facts (ob_cells o) off k) as [cells' taint] eqn:Esc.
  unfold obj_holds, obj_lo_of, obj_hi_of. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  split; [exact Hb|]. split.
  { intros off' Hoff' _. rewrite Hm.
    apply wview_mono with (m := ms_mem ms); [|apply Hw; exact Hoff'].
    intros y Hy. apply write_to_mem_grows. exact Hy. }
  split.
  { constructor.
    -
      unfold cell_holds. cbn [c_off c_width c_val]. fold A. split; [lia|]. split; [lia|].
      apply rd_bytes_of_nth; [exact Hlen | rewrite Ha, Z2Nat.id by lia; lia |].
      intros j Hj. unfold rd, ms_read_byte. rewrite Hm, Ha.
      rewrite <- Ha at 1. rewrite write_to_mem_in; [reflexivity | rewrite Ha, Hlen, Z2Nat.id by lia; lia | rewrite Hlen; exact Hj].
    - apply Forall_forall. intros c' Hin'.
      assert (Hin0 : In c' (fst (store_cells facts (ob_cells o) off k))) by (rewrite Esc; exact Hin').
      destruct (store_cells_spec _ _ _ _ _ Hin0) as (c & Hin & Hcase).
      destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as Hch. pose proof Hch as (B1 & B2 & Brd).
      assert (DISJ : (A + k <= soff rho (c_off c) \/ soff rho (c_off c) + c_width c <= A) ->
                     cell_holds rho (ob_base o) (soff rho (ob_lo o)) (soff rho (ob_hi o)) ms' c).
      { intros HD. unfold cell_holds in *. rewrite Hrdu; [exact Hch | lia | lia | lia | lia]. }
      destruct Hcase as [[Hcr ->] | [(d & Hcr & Ho & ->) | [(d & Hcr & Ho & Hdn & ->) | (d & Hcr & Ho & Hkd & ->)]]].
      + apply DISJ. exact (cell_rel_disj_sound segs rho facts ms o off k c Hf Hoh Hin Hlo Hhi ltac:(lia) Hcr).
      + apply DISJ. pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply Bool.andb_false_iff in Ho.
        destruct Ho as [Ho|Ho]; [apply Z.ltb_ge in Ho | apply Z.ltb_ge in Ho]; lia.
      +
        pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        unfold cell_holds. cbn [c_off c_width c_val]. split; [lia|]. split; [lia|].
        rewrite Hrdu by lia.
        rewrite (obj_read_cell segs rho ms o c (soff rho (c_off c)) (- d) Hoh Hin C2) by lia.
        rewrite Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned. reflexivity.
      +
        pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        assert (Eo : soff rho (mk_addk off k) = A + k) by (unfold A; apply soff_mk_addk; lia).
        unfold cell_holds. cbn [c_off c_width c_val]. rewrite Eo. split; [lia|]. split; [lia|].
        rewrite Hrdu by lia.
        rewrite (obj_read_cell segs rho ms o c (A + k) (d + c_width c - k) Hoh Hin C2) by lia.
        f_equal. f_equal. apply bv_eq. rewrite mk_alu_sound.
        change (eval rho (SLit (8 * (k - d)))) with (Z_to_bv 64 (8 * (k - d))).
        rewrite srl_lit_unsigned by lia.
        rewrite Z_to_bv_unsigned. replace (A + k - soff rho (c_off c)) with (k - d) by lia. apply bv_wrap_small. rewrite two64.
        pose proof (urange (eval rho (c_val c))) as Hu. rewrite Z.shiftr_div_pow2 by lia.
        split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
        assert (1 <= 2 ^ (8 * (k - d))) by (apply Z.pow_le_mono_r with (a:=2) (b:=0); lia). nia. }
  split.
  2:{ destruct taint; [exact I |]. destruct (ob_dflt o); cbn in Hdl |- *; try exact Hdl; try exact I. discriminate Hna. }
  intros off' Hoff' Hcov.
  assert (Hnot : ~ (A <= off' < A + k)).
  { intros Hx. apply Hcov. unfold covered. apply Exists_cons_hd. unfold in_cell. cbn [c_off c_width]. fold A. lia. }
  pose proof (covered_cons rho _ _ _ Hcov) as Hcov'.
  destruct taint.
  -   cbn. apply Hrd'. exact Hoff'.
  -
    assert (Hold : ~ covered rho (ob_cells o) off').
    { intros Hc. apply Hcov'. unfold covered in Hc |- *. apply Exists_exists in Hc as (c & Hin & Hic).
      assert (Ht : snd (store_cells facts (ob_cells o) off k) = false) by (rewrite Esc; reflexivity).
      pose proof (store_cells_notaint facts (ob_cells o) off k c Ht Hin) as K. cbn zeta in K. rewrite Esc in K. cbn [fst] in K.
      pose proof (proj1 (Forall_forall _ _) Hcells c Hin) as (B1 & B2 & _).
      destruct (obj_wf_cell _ _ _ Howf Hin) as (C1 & C2 & C3 & C4).
      unfold in_cell in Hic. apply Exists_exists.
      destruct K as [[Hcr HinK] | (d & Hcr & [[Ho HinK] | (Ho & R1 & R2)])].
      + exists c. split; [exact HinK | exact Hic].
      + exists c. split; [exact HinK | exact Hic].
      + pose proof (cell_rel_lit_sound segs rho facts ms o off k c d Hf Hoh Hin Hlo Hhi ltac:(lia) ltac:(lia) Hcr) as E.
        fold A in E. unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
        destruct (Z.lt_ge_cases off' A) as [Hlt|Hge].
        * exists (mkCell (c_off c) (- d) (c_val c)). split; [apply R1; lia|]. unfold in_cell. cbn [c_off c_width]. lia.
        * eexists. split; [apply R2; lia|]. unfold in_cell. cbn [c_off c_width].
          rewrite (soff_mk_addk rho off k) by (fold A; lia). fold A. lia. }
    specialize (Hd off' Hoff' Hold).
    destruct (ob_dflt o); cbn in Hd |- *.
    + destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hout; lia | exact Hr].
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + destruct Hd as [Hnone Hib]. split; [|exact Hib]. rewrite Hout by lia. exact Hnone.
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + rewrite (rd_unchanged ms ms'); [exact Hd | apply Hout; lia | exact Hr].
    + discriminate Hna.
Qed.

Lemma dflt_inv_unchanged : ltac2:(tb__ "0|3|
S1dS2cS6S6S6S5bS5bS0S15Q40M0A1ScS15Q8A1A1M1F_;S5dR1A1S5dR2A1A3S6S1S50R6R1A2S52R1R5A2A2S0G1S5cR4S17G0S51R8R2A2A2M2A2S5cR5G2A2A3F_;Foff';S50Z0S51R7R6A2A2S50S51R8R6A2S54Z2Z40A2A2S38RbRaR9R8R7R6A6S38RcRbRaR9R8R6A6F_;F_;F_;F_;F_;Fms';Fms;Fhi;Flo;Fb;Fd;Frho;").
Proof using .
  intros rho d b lo hi ms ms' Hr Hsame Hb1 Hb2 H. destruct d; cbn in H |- *; try exact H.
  destruct H as (He & Hf & Hfit & Hall). split; [exact He|]. split; [exact Hf|]. split; [exact Hfit|].
  intros k Hk. apply (elem_holds_rd_ext rho ms ms'); [|exact (Hall k Hk)].
  intros i f Hi. pose proof (proj1 (Forall_forall _ _) Hf f (nth_error_In _ _ Hi)) as (F0 & F1 & F2).
  pose proof (urange (eval rho cnt)) as Hc.
  assert (Hel : esz * k + esz <= esz * bv_unsigned (eval rho cnt)).
  { rewrite <- Z.mul_succ_r. apply Z.mul_le_mono_nonneg_l; lia. }
  assert (Hkn : 0 <= esz * k) by (apply Z.mul_nonneg_nonneg; lia).
  apply rd_bytes_unchanged; [exact Hr | |].
  - rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia).
    replace (b + lo + esz * k + fst f + Z.of_nat j) with (b + (lo + esz * k + fst f + Z.of_nat j)) by lia.
    apply Hsame. lia.
Qed.

Lemma obj_holds_frame : ltac2:(tb__ "0|5|
S1dS7S5bS5bS1aS15Q40M0A1M1S9S15Q8A1M2A1S0G1ScG2A1F_;M3S5dR4A1S5dR5A1A3S0G3S5cR5A1S5eS5cR6A1R3R2A3A3S50S51S16G0R4A2S53SdG2R3A2A1A2S54Z2Z40A2A2S3bS13S6S6S16G0R5A2M4S51G4S53SdG2R4A2A1A2A4S2aRaR6A2A2S0S8S23RaR7A2SaA3S1fVsegs;RcRaR8A4S1fVsegs;RdRaR9A4F_;F_;F_;F_;F_;F_;Fbs;Fa;Fo2;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o2 a bs Hr Hm Hnw Hdisj Hwf2 (Hb & Hw & Hc & Hd & Hdl).
  unfold obj_range, ranges_disjoint in Hdisj. cbn [fst snd] in Hdisj.
  unfold obj_lo_of, obj_hi_of in *.
  assert (Hsame : forall off', soff rho (ob_lo o2) <= off' < soff rho (ob_hi o2) ->
            ms_mem ms' (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o2)) + off')) =
            ms_mem ms (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o2)) + off'))).
  { intros off' Hoff'. rewrite Hm. apply write_to_mem_out; [exact Hnw|].
    rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia. }
  unfold obj_holds, obj_lo_of, obj_hi_of.
  split; [exact Hb|]. split.
  { intros off' Hoff' Hdw. unfold wview. rewrite Hsame by exact Hoff'. apply Hw; [exact Hoff' | exact Hdw]. }
  split.
  { apply Forall_forall. intros c Hin. pose proof (proj1 (Forall_forall _ _) Hc c Hin) as (B1 & B2 & Hch).
    destruct (obj_wf_cell _ _ _ Hwf2 Hin) as (C1 & C2 & C3 & C4).
    unfold cell_holds in *. split; [exact B1|]. split; [exact B2|]. rewrite <- Hch. apply rd_bytes_unchanged; [exact Hr | |].
    - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
    - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hsame. lia. }
  split; [| eapply dflt_inv_unchanged; [exact Hr | exact Hsame | lia | lia | exact Hdl]].
  intros off' Hoff' Hcov. specialize (Hd off' Hoff' Hcov).
  destruct (ob_dflt o2); cbn in Hd |- *.
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [Hnone Hib]. split; [|exact Hib]. rewrite Hsame by lia. exact Hnone.
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - rewrite (rd_unchanged ms ms'); [exact Hd | apply Hsame; lia | exact Hr].
  - destruct Hd as [b Hbb]. exists b. rewrite (rd_unchanged ms ms'); [exact Hbb | apply Hsame; lia | exact Hr].
Qed.

Lemma store_ok_of_writable : ltac2:(tb__ "0|4|
S15Q40M0A1M1ScS15Q8A1M2A1M3F_;G1SbS50S51S16G0R2A2S53R1A1A2S54Z2Z40A2A2SbS63R1R3A2S2S0G3S5fVsegs;R6S17G0S51S16G0R5A2S53R2A1A2A2A3S11G2A1A3A1F_;Fj;S0S8S60Vsegs;R5R4R3A4SaA3F_;F_;Fn;Fa;Fm;").
Proof using .
  intros m a n. revert a. induction n as [|n IH]; intros a Hnw Hall; [reflexivity|].
  cbn [store_ok]. pose proof (Hall 0%nat ltac:(lia)) as H0. cbn [Z.of_nat] in H0.
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0.
  destruct (wview segs m a) as [b|]; [|exfalso; apply H0; reflexivity].
  destruct n as [|n']; [reflexivity|].
  rewrite Nat2Z.inj_succ in Hnw.
  apply IH.
  - rewrite u_add1; lia.
  - intros j Hj. rewrite u_add1 by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.succ (Z.of_nat j)) by lia.
    rewrite <- Nat2Z.inj_succ. apply Hall. lia.
Qed.

Lemma obj_store_ok : ltac2:(tb__ "0|0|
S1dS5bS1aS6S6S1fVsegs;R5R4R3A4S0S8S2eS22R4A1A1SaA3S50S29R7R5A2R4A2S50S51R5R4A2S28R8R6A2A2S52Z0R5A2S0S8S60Vsegs;S5cR9A1S2bRaS26R8A1R7A3S55R6A1A4SaA3F_;F_;F_;F_;F_;Fk;Foff;Fo;Fms;Frho;").
Proof using .
  intros rho ms o off k (Hb & Hw & _ & _ & _) Hdw Hlo Hhi Hk.
  apply store_ok_of_writable.
  - rewrite oaddr_unsigned by lia. rewrite Z2Nat.id by lia. lia.
  - intros j Hj. rewrite oaddr_unsigned by lia. rewrite <- Z.add_assoc. apply Hw; [lia | exact Hdw].
Qed.

Lemma ro_addr_wview : ltac2:(tb__ "0|2|
S15Q40A1M0ScS15Q8A1A1M1F_;G0S0S8S4eVsegs;R1A2SaA3S0G1S5fVsegs;R3R2A3R3R2A1A3F_;Fa;Fm;").
Proof using .
  intros m a H. unfold ro_addr in H. unfold wview. destruct (m a); [reflexivity|].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
  destruct (seg_writable seg); [discriminate|reflexivity].
Qed.

Lemma ro_clear_store : ltac2:(tb__ "0|1|
S1dS5bS5bS1aS6S6S9S15Q8A1M0A1S3cVsegs;R6A2S1fVsegs;R8R7R5A4S0S8S2eS22R6A1A1SaA3S50S29RaR7A2R6A2S50S51R7R6A2S28RbR8A2A2S52Z0R7A2S0SbSdG0R7A2S55R8A1A3S0S15Q40A1ScG0A1F_;S5cRcA1S5eS5cRdA1S2bReS26RbA1RaA3R8A3A3S3cVsegs;RdA2F_;F_;F_;F_;F_;F_;F_;F_;Fbs;Fk;Foff;Fo;Fms';Fms;Frho;").
Proof using .
  intros rho ms ms' o off k bs Hroc (Hb & Hw0 & _ & _ & _) Hdw Hlo Hhi Hk Hlen Hm x Hro.
  assert (Hw : forall off0, obj_lo_of rho o <= off0 < obj_hi_of rho o ->
               wview segs (ms_mem ms) (Z_to_bv 64 (bv_unsigned (eval rho (ob_base o)) + off0)) <> None)
    by (intros off0 Hoff0; apply Hw0; [exact Hoff0 | exact Hdw]).
  rewrite Hm.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) off) = bv_unsigned (eval rho (ob_base o)) + off)
    by (apply oaddr_unsigned; lia).
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (eval rho (ob_base o)) + off)) as [Hlt|Hge].
  { rewrite write_to_mem_out; [apply Hroc; exact Hro | rewrite Ha, Hlen, Z2Nat.id; lia | rewrite Ha, Hlen, Z2Nat.id by lia; lia]. }
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (eval rho (ob_base o)) + off + k)) as [Hlt2|Hge2].
  - exfalso. specialize (Hw (bv_unsigned x - bv_unsigned (eval rho (ob_base o))) ltac:(lia)).
    replace (bv_unsigned (eval rho (ob_base o)) + (bv_unsigned x - bv_unsigned (eval rho (ob_base o))))
      with (bv_unsigned x) in Hw by lia.
    rewrite Z_to_bv_bv_unsigned in Hw. rewrite ro_addr_wview in Hw by exact Hro.
    apply Hw. apply Hroc. exact Hro.
  - rewrite write_to_mem_out; [apply Hroc; exact Hro | rewrite Ha, Hlen, Z2Nat.id; lia | rewrite Ha, Hlen, Z2Nat.id by lia; lia].
Qed.

Lemma list_upd_is_set : forall {A} (l : list A) n f x,
  nth_error l n = Some x -> list_upd l n f = list_set l n (f x).
Proof using .
  induction l as [|h t IH]; intros n f x H; destruct n; cbn in *; try discriminate.
  - inversion H. reflexivity.
  - rewrite (IH _ _ _ H). reflexivity.
Qed.

Lemma In_list_set : forall {A} (l : list A) n y x,
  In x (list_set l n y) -> x = y \/ exists m, m <> n /\ nth_error l m = Some x.
Proof using .
  induction l as [|h t IH]; intros n y x Hin; cbn in Hin; [destruct Hin|].
  destruct n as [|n].
  - destruct Hin as [<-|Hin]; [left; reflexivity|]. right.
    destruct (In_nth_error _ _ Hin) as [m Hm]. exists (S m). split; [lia|]. exact Hm.
  - destruct Hin as [<-|Hin].
    + right. exists 0%nat. split; [lia|]. reflexivity.
    + destruct (IH _ _ _ Hin) as [->|(m & Hne & Hm)]; [left; reflexivity|].
      right. exists (S m). split; [lia|]. exact Hm.
Qed.

Lemma pdr_nth : ltac2:(tb__ "0|3|
S9S10S6S6A2M0A1SbSbG0G0S96R5A1S0ScG0A1M1S61G0R6R5A3SeG0R3A2M2A3S0G1S61G0R7R5A3G2A3S2S0SbR7R6A3A1S3bR6R5A2F_;F_;F_;F_;Frj;Fri;Fj;Fi;Frs;").
Proof using .
  induction rs as [|r rest IH]; intros i j ri rj Hp Hi Hj Hne; [destruct i; discriminate|].
  destruct Hp as [Hf Hp]. destruct i as [|i], j as [|j]; cbn in Hi, Hj; try lia.
  - inversion Hi; subst. apply nth_error_In in Hj. exact (proj1 (Forall_forall _ _) Hf rj Hj).
  - inversion Hj; subst. apply nth_error_In in Hi. pose proof (proj1 (Forall_forall _ _) Hf ri Hi) as H.
    unfold ranges_disjoint in *. lia.
  - eapply IH; eauto.
Qed.

Lemma pairwise_disjoint_nth : ltac2:(tb__ "0|2|
S1dS9S1aA1SbSbS1aS1aS4dR6R5A2S0ScS1aA1M0S61S1aR6R5A3SeS1aR3A2M1A3S0G0S61S1aR7R5A3G1A3S2S0SbR7R6A3A1S3bS2aRaR6A2S2aRaR5A2A2F_;F_;F_;F_;Foj;Foi;Fj;Fi;Fobjs;Frho;").
Proof using .
  intros rho objs i j oi oj Hpd Hi Hj Hne. apply pairwise_disjoint_pdr in Hpd.
  eapply (pdr_nth _ i j); [exact Hpd | rewrite nth_error_map, Hi; reflexivity | rewrite nth_error_map, Hj; reflexivity | exact Hne].
Qed.

Lemma obj_range_store : ltac2:(tb__ "0|0|
S1dS9S1cA1S1aS19S6S19S0S10S6S6A2S2aR6S6bR5R4R3R2R1A5A2S2aR6R4A2A3Fv;Fk;Foff;Fo;Ffacts;Frho;").
Proof using .
  intros. unfold obj_store. destruct (store_cells facts (ob_cells o) off k) as [cells' taint]. reflexivity.
Qed.

Definition obj_with_dflt (o : sobj) (d : odefault) : sobj := ltac2:(tb__ "0|0|
S49S26Vo;A1S4cVo;A1S4bVo;A1S4aVo;A1Vd;A5").

Lemma obj_holds_arr_weaken : ltac2:(tb__ "0|0|
S1dS5bS1aS1fVsegs;R3R2R1A4S0S8S42S22R2A1A1SaA3S1fVsegs;R5R4S93R3S40A2A4F_;F_;Fo;Fms;Frho;").
Proof using .
  intros rho ms o (Hb & Hw & Hc & Hd & Hdl) Ha.
  unfold obj_holds, obj_with_dflt, obj_lo_of, obj_hi_of in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  split; [exact Hb|]. split; [intros off Hoff _; apply Hw; [exact Hoff|]; destruct (ob_dflt o); try reflexivity; discriminate Ha|].
  split; [exact Hc|]. split; [|exact I].
  intros off Hoff Hcov. specialize (Hd off Hoff Hcov). destruct (ob_dflt o); try discriminate Ha. cbn in Hd |- *. exact Hd.
Qed.

Lemma obj_wf_with_dflt : ltac2:(tb__ "0|0|
S7S1aS2cS0S8S23R3R2A2SaA3S0S8S48R4R2A2SaA3S0S8S23R5S93R4R3A2A2SaA3F_;F_;Fd;Fo;Fn;").
Proof using .
  intros n o d H Hd. unfold obj_wf, obj_with_dflt in *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt].
  apply andb_prop in H as [H _]. rewrite H, Hd. reflexivity.
Qed.

Lemma prove_sprop_sound : ltac2:(tb__ "0|0|
S1dS9S1cA1S1cS65S1cS27R3A1R2A3S0S8S82R3R2A2SaA3S27R5R3A2F_;F_;Fp;Ffacts;Frho;").
Proof using .
  intros rho facts p Hf H. unfold prove_sprop in H. apply Bool.orb_prop in H as [H|H].
  - apply existsb_exists in H as (q & Hin & Heq). apply sprop_eqb_sound in Heq. subst q.
    exact (proj1 (Forall_forall _ _) Hf p Hin).
  - destruct p; try discriminate; cbn.
    + pose proof (uleq_sound rho facts a 1 b Hf H). unfold U in *. lia.
    + pose proof (uleq_sound rho facts a 0 b Hf H). unfold U in *. lia.
Qed.

Lemma fldv_list_set : ltac2:(tb__ "0|1|
S9S15Q40A1M0A1SbG0SbS63R3SdG0R4A2A2S0G0S39S72G0R5R4R3A4R2A2S8G0L_;S97R2R4A2R3S39R5R2A2X8x2A3F_;Fj;Fw;Fi;Fvals;").
Proof using . intros. unfold fldv. apply nth_list_set. assumption. Qed.

Lemma tf_holds_set_other : ltac2:(tb__ "0|1|
S1dS9S15Q40A1M0A1SbG0S35S63R3SdG0R4A2A2S0S8S79R4R2A2SfA3S5S3eR7S72G0R6R5R4A4R3A3S3eR7R6R3A3A2F_;F_;Ft;Fw;Fi;Fvals;Frho;").
Proof using .
  intros rho vals i w t Hi Hm. destruct t; cbn in Hm |- *; rewrite !fldv_list_set by exact Hi.
  - destruct (Nat.eqb_spec i0 i); [subst; rewrite Nat.eqb_refl in Hm; discriminate|]. tauto.
  - destruct (Nat.eqb_spec i0 i); [subst; rewrite Nat.eqb_refl in Hm; discriminate|]. tauto.
  - apply Bool.orb_false_iff in Hm as [H1 H2].
    destruct (Nat.eqb_spec i0 i); [subst; rewrite Nat.eqb_refl in H1; discriminate|].
    destruct (Nat.eqb_spec j i); [subst; rewrite Nat.eqb_refl in H2; discriminate|]. tauto.
Qed.

Lemma tf_inst_complete : ltac2:(tb__ "0|1|
S1dS9S19A1S9S15Q40A1M0A1S35SbS0S8S79R1R2A2SaA3S0G0S25R6S66S19R2R5S30Z0A1A4A2S39R4R2A2A3F_;Fj;S65S1cS27R5A1S86R4R2A2A3S3eR6R4R3A3F_;F_;Ft;Fvals;Fxs;Frho;").
Proof using .
  intros rho xs vals t Hxs H. destruct t as [st i sx e|st i sx e|st i j e]; cbn [tf_inst] in H; cbn.
  - inversion H as [|p l Hp _]; subst. pose proof (Hxs i ltac:(cbn; apply Nat.eqb_refl)) as Xi.
    destruct st; cbn in Hp |- *; rewrite extsv_sound, Xi in Hp; exact Hp.
  - inversion H as [|p l Hp _]; subst. pose proof (Hxs i ltac:(cbn; apply Nat.eqb_refl)) as Xi.
    destruct st; cbn in Hp |- *; rewrite extsv_sound, Xi in Hp; exact Hp.
  - inversion H as [|p l Hp Hrest]; subst. inversion Hrest as [|p2 l2 Hp2 Hrest2]; subst.
    pose proof (Hxs i ltac:(cbn; rewrite Nat.eqb_refl; reflexivity)) as Xi.
    pose proof (Hxs j ltac:(cbn; rewrite Nat.eqb_refl; apply Bool.orb_true_r)) as Xj.
    cbn [holds eval] in Hp2. rewrite Xi, Xj in Hp2.
    pose proof (urange (fldv vals i)) as Hi. pose proof (urange (fldv vals j)) as Hj.
    assert (Hsum : bv_unsigned (eval rho (SAlu ALU_ADD (nth i xs (SLit 0)) (nth j xs (SLit 0)))) = bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j)).
    { cbn [eval]. rewrite Xi, Xj. unfold alu64, alu in Hp2 |- *. rewrite bv_add_unsigned in Hp2 |- *. unfold bv_wrap in Hp2 |- *. rewrite two64 in Hp2 |- *.
      destruct (Z.lt_ge_cases (bv_unsigned (fldv vals i) + bv_unsigned (fldv vals j)) (2 ^ 64)) as [Hlt|Hge].
      - apply Z.mod_small. lia.
      - exfalso. rewrite <- (Z.mod_add _ (-1)) in Hp2 by lia. rewrite Z.mod_small in Hp2 by lia. lia. }
    destruct st; cbn [sp_rel holds] in Hp; cbn [zrel]; rewrite Hsum in Hp; exact Hp.
Qed.

Lemma ext_low_false_unsigned : ltac2:(tb__ "0|1|
SbS15Q40M0A1S64R2U8A2S0S6S16G0S41SfS8dQ8S8eR3A1A2R2A3A2S56S16G0R2A2S54Z2S57Z8S53R3A1A2A2A2A3F_;Fv;Fk;").
Proof using .
  intros k v Hk. unfold ext_low, zext. rewrite bv_zero_extend_unsigned', bv_extract_unsigned.
  change (Z.of_N 0) with 0. rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
  replace (Z.of_N (8 * N.of_nat k)) with (8 * Z.of_nat k) by lia.
  pose proof (urange v). pose proof (Z.mod_pos_bound (bv_unsigned v) (2 ^ (8 * Z.of_nat k)) ltac:(apply Z.pow_pos_nonneg; lia)).
  apply Z.mod_small. change (2 ^ Z.of_N 64) with (2 ^ 64).
  assert (2 ^ (8 * Z.of_nat k) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma enc_bytes_low : ltac2:(tb__ "0|1|
SbS15Q40A1S64R2U8A2S0S9S15Q8M0A1A1S21R3S41SfS8dG0S8eR3A1A2R2A3A2S21R3R2A2A3F_;Fv;Fk;").
Proof using .
  intros k v Hk. unfold enc_bytes. rewrite ext_low_false_unsigned by exact Hk. apply Z_to_le_bytes_mod.
Qed.

Lemma enc_bytes_inj_low : ltac2:(tb__ "0|3|
SbS15Q40M0A1M1G1S0S9S15Q8A1A1S21R3R2A2S21R3R1A2A3S0S6S56S16G0R3A2S54Z2S57Z8S53R4A1A2A2M2A2S56S16G0R2A2G2A2A3F_;Fb;Fa;Fk;").
Proof using .
  intros k a b H. unfold enc_bytes in H.
  pose proof (urange a). pose proof (urange b).
  rewrite <- (bytes_le_to_Z_Z_to_le_bytes k (bv_unsigned a)) by lia.
  rewrite <- (bytes_le_to_Z_Z_to_le_bytes k (bv_unsigned b)) by lia. rewrite H. reflexivity.
Qed.

Lemma flds_apart_sound : ltac2:(tb__ "0|2|
S9S10S6S6A2M0A1SbS6S6SbG0S0S8S7dR6R5R4R3A4SaA3S0ScG0A1S61G0R7R3A3SeG0R2A2A3S2S0SbR4R7A3A1S3S50S51S12S6S6R4A3M1S14S6S6R4A3A2R7A2S50S51R7R6A2G1A2A2F_;F_;F_;Ff;Fj;Fk;Fc;Fi;Fflds;").
Proof using .
  intros flds i c k j f H Hj Hne. unfold flds_apart in H.
  assert (Hin : In (j, f) (combine (seq 0 (length flds)) flds)).
  { assert (G : forall start (l : list (Z * Z)) jj x, nth_error l jj = Some x -> In ((start + jj)%nat, x) (combine (seq start (length l)) l)).
    { intros start l. revert start. induction l as [|y t IH]; intros start jj x Hx; [destruct jj; discriminate|].
      destruct jj as [|jj]; cbn in Hx |- *.
      - injection Hx as <-. left. rewrite Nat.add_0_r. reflexivity.
      - right. replace (start + Datatypes.S jj)%nat with (Datatypes.S start + jj)%nat by lia. apply IH. exact Hx. }
    exact (G 0%nat flds j f Hj). }
  pose proof (proj1 (forallb_forall _ _) H _ Hin) as X. cbn [fst snd] in X.
  apply Bool.orb_prop in X as [X|X]; [apply Nat.eqb_eq in X; lia|].
  apply Bool.orb_prop in X as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma store_xs_spec : ltac2:(tb__ "0|4|
S9S1cA1S9S1bA1S19S9S10S6S6A2M0A1SbS19S6SbS8F_;SbS9S19A1M1S0ScG1A1S85RaR9R8R7R6R5R4R3R2A9SeG1R1A2A3S1S0SbSdS19R2A2SdG0R8A2A3S1SbS63R1SdG0R9A2A2S0SbS8cR5R2A2R9A3S0S19S66S19R3R5S30Z0A1M2A4S81ReR8R9A3A3F_;F_;Fjj;SbG0S0ScG0A1S61G0RaR2A3SeG0R1A2A3S2S0SbS8cR6R3A2RaA3A1S0S8R8S8cR7R4A2A1SaA3S4S19S19S1S0S7cS83R11R10S67RfS12S6S6R5A3A2S14S6S6R5A3M3S7bA5S7aR1A1A3S0S19S66S19R6R8G2A4S80SfS8dQ8S5aG3A1A2R1A3A3A2Lcv;A2F_;F_;F_;Ff;Fjj;A2A2F_;Fxs;Fj0;Fneed;Fk;Fv;Fi;Ffl;Foff0;Fcells;Ffacts;").
Proof using .
  intros facts cells off0 fl i v k need. induction fl as [|f rest IH]; intros j0 xs H; cbn [store_xs] in H.
  - injection H as <-. split; [reflexivity|]. split; [intros; cbn in *; lia | intros jj f' Hjj; destruct jj; discriminate].
  - destruct (if Nat.eqb j0 i then Some (narrow facts k v)
              else if need j0 then fld_cached facts cells off0 f else Some (SLit 0)) as [x|] eqn:Ex; [|discriminate].
    destruct (store_xs facts cells off0 rest i v k need (Datatypes.S j0)) as [xs'|] eqn:Er; [|discriminate].
    injection H as <-. destruct (IH (Datatypes.S j0) xs' Er) as (L & A & B).
    split; [cbn; rewrite L; reflexivity|]. split.
    + intros jj Hjj Heq. destruct jj as [|jj]; cbn [nth].
      * rewrite Nat.add_0_r in Heq. subst j0. rewrite Nat.eqb_refl in Ex. injection Ex as <-. reflexivity.
      * apply A; [cbn in Hjj; lia | lia].
    + intros jj f' Hjj Hne Hneed. destruct jj as [|jj]; cbn [nth]; cbn in Hjj.
      * injection Hjj as <-. rewrite Nat.add_0_r in Hne, Hneed.
        destruct (Nat.eqb_spec j0 i); [lia|]. rewrite Hneed in Ex. unfold fld_cached in Ex.
        destruct (read_cells facts cells (mk_addk off0 (fst f)) (snd f) CRNone) eqn:Erc; try discriminate.
        injection Ex as <-. exists v0. auto.
      * replace (j0 + Datatypes.S jj)%nat with (Datatypes.S j0 + jj)%nat in * by lia. apply B; assumption.
Qed.

Lemma arr_after_store_sound : ltac2:(tb__ "0|2|
S1dS7S5bS5bS1aS9S1cA1S19S6S19S6S19S9S10S6S6A2A1S9S35A1S32Vsegs;RbA2S65S1cS27ReA1R9A3S1fVsegs;RfRdRbA4S0S8S23RfRcA2SaA3S0S2cS22RdA1S3fR8R7R6R5A4A3S50S29R12ReA2S1eR12RcA2A2S50S51S1eR13RdA2RcA2S28R13RfA2A2S52Z0RdA2S50ReZ8A2S0S15Q40M0A1ScS15Q8A1A1F_;M1S5dR13A1S5dR14A1A3S0G1S5cR14A1S5eS5cR15A1S2bR17S26R13A1S1eR17R11A2A3S21S55R10A1S25R17RfA2A2A3A3S0S2cS70R13R14R12R11R10RfReRdRcA9S22R14A1A3S38R19S3fR10RfReRdA4S16G0S25R19S26R15A1A2A2S29R19R15A2S28R19R15A2R16A6F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Ftmpl;Fflds;Fcnt;Fesz;Fv;Fk;Foff;Ffacts;Fo;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o facts off k v esz cnt flds tmpl Hrom Hf Hoh Howf Hd Hlo Hhi Hk Hk8 Hr Hm Has.
  pose proof Hoh as (HB & HW & HC & HD & HDL). rewrite Hd in HDL. cbn [dflt_inv] in HDL.
  destruct HDL as (Hesz0 & Hflds & Hfit & Helems). destruct HB as (HB1 & HB2 & HB3 & HB4).
  set (b := bv_unsigned (eval rho (ob_base o))) in *.
  set (lo := obj_lo_of rho o) in *. set (hi := obj_hi_of rho o) in *.
  set (A := soff rho off) in *.
  pose proof (urange (eval rho cnt)) as Hcu. set (N := bv_unsigned (eval rho cnt)) in *.
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) A) = b + A) by (unfold b; apply oaddr_unsigned; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia).
  assert (Hout : forall off', ~ (A <= off' < A + k) -> 0 <= b + off' < 2 ^ 64 ->
            ms_mem ms' (Z_to_bv 64 (b + off')) = ms_mem ms (Z_to_bv 64 (b + off'))).
  { intros off' Hoff' Hrange. rewrite Hm. apply write_to_mem_out.
    - rewrite Ha, Hlen, Z2Nat.id by lia. lia.
    - rewrite Ha, Hlen, Z2Nat.id by lia. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; lia). lia. }

  assert (KEEP : forall kk, 0 <= kk < N -> (lo + esz * kk + esz <= A \/ A + k <= lo + esz * kk) ->
            elem_holds rho ms' (b + lo + esz * kk) flds tmpl).
  { intros kk Hkk Hdis. apply (elem_holds_rd_ext rho ms ms'); [|exact (Helems kk Hkk)].
    intros i f Hi. pose proof (proj1 (Forall_forall _ _) Hflds f (nth_error_In _ _ Hi)) as (F0 & F1 & F2).
    assert (Hel : esz * kk + esz <= esz * N) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hkn : 0 <= esz * kk) by (apply Z.mul_nonneg_nonneg; lia).
    apply rd_bytes_unchanged; [exact Hr | |].
    - rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia).
      rewrite Z2Nat.id by lia. unfold lo, hi, obj_lo_of, obj_hi_of in *. lia.
    - intros j Hj. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia).
      replace (b + lo + esz * kk + fst f + Z.of_nat j) with (b + (lo + esz * kk + fst f + Z.of_nat j)) by lia.
      apply Hout; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia. }
  unfold arr_after_store in Has.
  destruct (lin_decomp facts (mk_alu ALU_SUB off (ob_lo o)) esz) as [[idx c]|] eqn:Hdec; [|rewrite Hd in Has; discriminate].
  destruct (lin_decomp_sound rho facts _ esz idx c Hf Hdec) as (Hesz & Hc & HU).
  cbn [dflt_inv]. split; [exact Hesz0|]. split; [exact Hflds|]. split; [exact Hfit|].

  match type of Has with (if ?beyond then _ else _) = _ => destruct beyond eqn:Hbey end.
  -
    destruct (same_atoms idx cnt) as [dlt|] eqn:Hsa; [|discriminate].
    apply andb_prop in Hbey as [Hd0 Hd1]. apply Z.leb_le in Hd0. apply Z.ltb_lt in Hd1.
    pose proof (same_atoms_sound rho idx cnt dlt Hsa) as Hidx.
    assert (HAlo : A - lo = esz * (N + dlt) + c).
    { assert (E : (A - lo) mod 2 ^ 64 = (esz * U rho idx + c) mod 2 ^ 64).
      { rewrite <- HU. unfold U at 1. rewrite mk_alu_sound, sub_val.
        change (bv_unsigned (eval rho off)) with (U rho off). change (bv_unsigned (eval rho (ob_lo o))) with (U rho (ob_lo o)).
        rewrite <- (soff_mod rho off), <- (soff_mod rho (ob_lo o)). unfold A, lo, obj_lo_of. rewrite <- Zminus_mod. reflexivity. }
      rewrite Hidx in E. unfold U, N in *.
      assert (E2 : (esz * ((bv_unsigned (eval rho cnt) + dlt) mod 2 ^ 64) + c) mod 2 ^ 64
                   = (esz * (bv_unsigned (eval rho cnt) + dlt) + c) mod 2 ^ 64).
      { rewrite <- (Zplus_mod_idemp_l (esz * ((bv_unsigned (eval rho cnt) + dlt) mod 2 ^ 64))).
        rewrite mul_mod_idemp. apply Zplus_mod_idemp_l. }
      rewrite E2 in E.
      rewrite (Z.mod_small (A - lo)) in E by (unfold A, lo, hi, obj_lo_of, obj_hi_of in *; lia).
      assert (Hnn : 0 <= esz * (bv_unsigned (eval rho cnt) + dlt)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (Hup : esz * (bv_unsigned (eval rho cnt) + dlt) + c < 2 ^ 64).
      { rewrite Z.mul_add_distr_l. unfold lo, hi, obj_lo_of, obj_hi_of in *. clear - Hd1 HB4 Hfit Hesz. lia. }
      rewrite Z.mod_small in E by lia. exact E. }
    intros kk Hkk. apply KEEP; [exact Hkk|]. left.
    assert (esz * kk + esz <= esz * N) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; lia).
    assert (esz * N <= esz * (N + dlt)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  -
    clear Hbey.
    destruct (fld_index flds c k) as [i|] eqn:Hfi; [|rewrite Hd in Has; discriminate].
    set (off0 := mk_addk off (- c)) in Has.
    set (need := fun j => existsb (fun t => tf_mentions i t && tf_mentions j t) tmpl) in Has.
    destruct (store_xs facts (ob_cells o) off0 flds i v k need 0) as [xs|] eqn:Hxs; [|rewrite Hd in Has; discriminate].
    match type of Has with (if ?cond then _ else _) = _ => destruct cond eqn:Hcond; [|rewrite Hd in Has; discriminate] end.
    clear Has. apply andb_prop in Hcond as [Hcond Htm]. apply andb_prop in Hcond as [Hul Hap].
    pose proof (uleq_sound rho facts idx 1 cnt Hf Hul) as Hidx. unfold U in Hidx. fold N in Hidx.
    pose proof (fld_index_sound flds c k i Hfi) as Hfld.
    pose proof (proj1 (Forall_forall _ _) Hflds _ (nth_error_In _ _ Hfld)) as Hfok. unfold fld_ok in Hfok. cbn [fst snd] in Hfok.
    destruct Hfok as (Hc0 & Hck & Hk1248).
    set (K := bv_unsigned (eval rho idx)) in *.
    assert (Hmul : esz * K + esz <= esz * N) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; [lia|]; unfold K; lia).
    assert (HKnn : 0 <= esz * K) by (apply Z.mul_nonneg_nonneg; [lia | unfold K; apply (proj1 (urange _))]).
    assert (HA : A = lo + esz * K + c).
    { unfold A, lo, hi, obj_lo_of, obj_hi_of in *.
      eapply (arr_offset_eq rho off (ob_lo o) esz idx c K (ob_hi o) k HU); [lia | lia | reflexivity | exact Hlo | exact Hhi | lia | lia | lia]. }
    intros kk Hkk.
    destruct (Z.eq_dec kk K) as [->|Hne].
    2:{ apply KEEP; [exact Hkk|].
        destruct (Z.lt_ge_cases kk K).
        - left. assert (esz * kk + esz <= esz * K) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; lia). lia.
        - right. assert (esz * K + esz <= esz * kk) by (rewrite <- Z.mul_succ_r; apply Z.mul_le_mono_nonneg_l; lia). lia. }

    destruct (Helems K ltac:(unfold K in *; lia)) as (vals & Hvlen & Hvrd & Hvt).
    set (w := ext_low false (8 * N.of_nat (Z.to_nat k))%N (eval rho v)).
    exists (list_set vals i w).
    assert (HiL : (i < length vals)%nat) by (rewrite Hvlen; eapply nth_error_Some; congruence).
    split; [rewrite list_set_length; exact Hvlen|].
    destruct (store_xs_spec facts (ob_cells o) off0 flds i v k need 0%nat xs Hxs) as (Lxs & Xi & Xo).
    assert (FLD : forall j f, nth_error flds j = Some f ->
              rd_bytes ms' (Z_to_bv 64 (b + lo + esz * K + fst f)) (Z.to_nat (snd f)) = Some (enc_bytes (Z.to_nat (snd f)) (fldv (list_set vals i w) j))
              /\ bv_unsigned (fldv (list_set vals i w) j) < 2 ^ (8 * snd f)).
    { intros j f Hj. rewrite fldv_list_set by exact HiL.
      pose proof (proj1 (Forall_forall _ _) Hflds f (nth_error_In _ _ Hj)) as (F0 & F1 & F2).
      destruct (Nat.eqb_spec j i) as [->|Hji].
      - rewrite Hfld in Hj. injection Hj as <-. cbn [fst snd]. split.
        +
          unfold w. rewrite enc_bytes_low by lia.
          replace (Z_to_bv 64 (b + lo + esz * K + c)) with (oaddr rho (ob_base o) A).
          2:{ unfold oaddr. f_equal. unfold b. lia. }
          apply rd_bytes_of_nth; [exact Hlen | rewrite Ha, Z2Nat.id by lia; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia |].
          intros jj Hjj. unfold rd, ms_read_byte. rewrite Hm, Hr, Ha. rewrite <- Ha at 1.
          rewrite write_to_mem_in; [reflexivity | rewrite Ha, Hlen, Z2Nat.id by lia; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia | rewrite Hlen; exact Hjj].
        + unfold w. rewrite ext_low_false_unsigned by lia. rewrite Z2Nat.id by lia.
          apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
      - destruct (Hvrd j f Hj) as [R V]. split; [|exact V]. rewrite <- R.
        pose proof (flds_apart_sound flds i c k j f Hap Hj Hji) as Hdis.
        apply rd_bytes_unchanged; [exact Hr | |].
        + rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia).
          rewrite Z2Nat.id by lia. unfold lo, hi, obj_lo_of, obj_hi_of in *. lia.
        + intros jj Hjj. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite two64; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia).
          replace (b + lo + esz * K + fst f + Z.of_nat jj) with (b + (lo + esz * K + fst f + Z.of_nat jj)) by lia.
          apply Hout; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia. }
    split; [exact FLD|].

    apply Forall_forall. intros t Hin.
    destruct (tf_mentions i t) eqn:Hmi.
    2:{ apply (proj2 (tf_holds_set_other rho vals i w t HiL Hmi)). exact (proj1 (Forall_forall _ _) Hvt t Hin). }
    pose proof (proj1 (forallb_forall _ _) Htm t Hin) as Hpt. cbn beta in Hpt. rewrite Hmi in Hpt. cbn [negb orb] in Hpt.
    apply (tf_inst_complete rho xs).
    2:{ apply Forall_forall. intros p Hp. eapply prove_sprop_sound; [exact Hf|]. exact (proj1 (forallb_forall _ _) Hpt p Hp). }
    intros j Hmj. rewrite fldv_list_set by exact HiL.
    destruct (k_cases k Hk1248) as (_ & _ & Hkn8 & Hw8 & _).
    destruct (Nat.eqb_spec j i) as [->|Hji].
    + rewrite (Xi i ltac:(lia) ltac:(lia)). unfold w. rewrite (narrow_sound rho facts k v Hf ltac:(lia)), Hw8. reflexivity.
    + destruct (Nat.lt_ge_cases j (length flds)) as [Hjl|Hjl].
      2:{ rewrite nth_overflow by (rewrite Lxs; lia). unfold fldv. rewrite nth_overflow by lia. reflexivity. }
      assert (Hneed : need j = true).
      { unfold need. apply existsb_exists. exists t. split; [exact Hin|]. rewrite Hmi, Hmj. reflexivity. }
      destruct (nth_error flds j) as [f|] eqn:Hj; [|exfalso; exact (proj2 (nth_error_Some flds j) Hjl Hj)].
      destruct (Xo j f Hj ltac:(lia) Hneed) as (cv & Hrc & ->).
      pose proof (proj1 (Forall_forall _ _) Hflds f (nth_error_In _ _ Hj)) as (F0 & F1 & F2).
      destruct (read_cells_exact _ _ _ _ CRNone _ I Hrc) as (c' & Hin' & Hcv & Hcw & Hcr).
      destruct (obj_wf_cell _ _ _ Howf Hin') as (C1 & C2 & C3 & C4).

      assert (Hoffj : soff rho (mk_addk off0 (fst f)) = lo + esz * K + fst f).
      { pose proof (soff_range rho off). pose proof (soff_range rho (ob_lo o)). pose proof (soff_range rho (ob_hi o)).
        assert (R1 : soff rho off0 = lo + esz * K).
        { unfold off0. rewrite soff_mk_addk; [unfold A in HA; lia|]. unfold A, lo, hi, obj_lo_of, obj_hi_of in *. lia. }
        rewrite soff_mk_addk; [lia|]. rewrite R1. unfold lo, hi, obj_lo_of, obj_hi_of in *. lia. }
      pose proof (cell_rel_lit_sound segs rho facts ms o (mk_addk off0 (fst f)) (snd f) c' 0 Hf Hoh Hin'
                    ltac:(rewrite Hoffj; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia)
                    ltac:(rewrite Hoffj; unfold lo, hi, obj_lo_of, obj_hi_of in *; lia)
                    ltac:(lia) ltac:(lia) Hcr) as Ec.
      rewrite Hoffj, Z.add_0_r in Ec.
      pose proof (obj_read_cell segs rho ms o c' (soff rho (c_off c')) (snd f) Hoh Hin' C2 ltac:(lia) ltac:(rewrite Hcw; lia) ltac:(lia)) as Rc.
      rewrite Z.sub_diag, Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_bv_unsigned, Hcv in Rc.
      unfold oaddr in Rc. rewrite Ec in Rc.
      destruct (Hvrd j f Hj) as [Rv Vv]. unfold b in Rv.
      replace (bv_unsigned (eval rho (ob_base o)) + lo + esz * K + fst f) with (bv_unsigned (eval rho (ob_base o)) + (lo + esz * K + fst f)) in Rv by lia.
      rewrite Rc in Rv. injection Rv as Henc.
      apply enc_bytes_inj_low in Henc. replace (Z.of_nat (Z.to_nat (snd f))) with (snd f) in Henc by (clear -F2; lia).
      rewrite (Z.mod_small (bv_unsigned (fldv vals j))) in Henc by (pose proof (urange (fldv vals j)); lia).
      apply bv_eq. rewrite mk_ext_sound.
      replace (8 * Z.to_N (snd f))%N with (8 * N.of_nat (Z.to_nat (snd f)))%N by lia.
      rewrite ext_low_false_unsigned by lia. rewrite Z2Nat.id by lia. exact Henc.
Qed.

Lemma arr_after_store_cases : ltac2:(tb__ "0|1|
S9S1cA1S1aS19S6S19S6S19S9S10S6S6A2A1S9S35A1S3S0S2cS70R9R8R7R6R5R4R3R2R1A9M0S40A3S0S2cG0S22R8A1A3A2Ftmpl;Fflds;Fcnt;Fesz;Fv;Fk;Foff;Fo;Ffacts;").
Proof using .
  intros. unfold arr_after_store.
  destruct (lin_decomp facts (mk_alu ALU_SUB off (ob_lo o)) esz) as [[idx c]|]; [|left; reflexivity].
  match goal with |- context [if ?b then ob_dflt o else _] => destruct b; [right; reflexivity|] end.
  destruct (fld_index flds c k) as [i|]; [|left; reflexivity].
  destruct (store_xs _ _ _ _ _ _ _ _ _) as [xs|]; [|left; reflexivity].
  match goal with |- context [if ?b then ob_dflt o else _] => destruct b; [right; reflexivity | left; reflexivity] end.
Qed.

Lemma obj_holds_store_d : ltac2:(tb__ "0|1|
S1dS7S5bS5bS1aS9S1cA1S19S6S19S32Vsegs;R7A2S65S1cS27RaA1R5A3S1fVsegs;RbR9R7A4S0S8S23RbR8A2SaA3S0S8S2eS22R9A1A1SaA3S50S29ReRaA2S1eReR8A2A2S50S51S1eRfR9A2R8A2S28RfRbA2A2S52Z0R9A2S50RaZ8A2S0S15Q40A1ScS15Q8A1A1F_;M0S5dRfA1S5dR10A1A3S0G0S5cR10A1S5eS5cR11A1S2bR13S26RfA1S1eR13RdA2A3S21S55RcA1S25R13RbA2A2A3A3S1fVsegs;R14R11S68RfR10ReRdRcA5A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Ffacts;Fo;Fms';Fms;Fn;Frho;").
Proof using .
  intros rho n ms ms' o facts off k v Hrom Hf Hoh Howf Hdw Hlo Hhi Hk Hk8 Hr Hm.
  unfold obj_store_d. destruct (ob_dflt o) eqn:Hd.
  1-5: apply (obj_holds_store rho n ms ms'); rewrite ?Hd; auto.

  pose proof (obj_holds_arr_weaken rho ms o Hoh ltac:(rewrite Hd; reflexivity)) as Hoh0.
  pose proof (obj_wf_with_dflt n o DUnknown Howf eq_refl) as Howf0.
  pose proof (obj_holds_store rho n ms ms' (obj_with_dflt o DUnknown) facts off k v Hrom Hf Hoh0 Howf0 eq_refl eq_refl Hlo Hhi Hk Hk8 Hr Hm) as H1.
  pose proof (arr_after_store_sound rho n ms ms' o facts off k v esz cnt flds tmpl Hrom Hf Hoh Howf Hd Hlo Hhi Hk Hk8 Hr Hm) as HARR.
  destruct (arr_after_store_cases facts o off k v esz cnt flds tmpl) as [E|E]; rewrite E; [clear HARR | specialize (HARR E); rewrite Hd].
  all: unfold obj_store, obj_with_dflt in H1 |- *; cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in H1 |- *.
  all: destruct (store_cells facts (ob_cells o) off k) as [cells' taint].
  all: destruct H1 as (A1 & A2 & A3 & A4 & _).
  all: unfold obj_holds, obj_lo_of, obj_hi_of in *; cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  all: split; [exact A1|]; split; [intros off0 H0 _; apply A2; [exact H0|]; destruct taint; reflexivity|]; split; [exact A3|].
  - split; [|exact I]. intros off0 H0 Hc0. specialize (A4 off0 H0 Hc0). destruct taint; exact A4.
  - split; [|exact HARR]. intros off0 H0 Hc0. specialize (A4 off0 H0 Hc0). destruct taint; exact A4.
Qed.

Lemma obj_range_store_d : ltac2:(tb__ "0|0|
S1dS9S1cA1S1aS19S6S19S0S10S6S6A2S2aR6S68R5R4R3R2R1A5A2S2aR6R4A2A3Fv;Fk;Foff;Fo;Ffacts;Frho;").
Proof using .
  intros. unfold obj_store_d, obj_store. destruct (store_cells facts (ob_cells o) off k) as [cells' taint].
  destruct (ob_dflt o); reflexivity.
Qed.

Lemma mem_match_store : ltac2:(tb__ "0|1|
S1dS20S5bS5bSbS1aS19S6S19S32Vsegs;R7A2S0S8S34R9A1SaA3S65S1cS27RbA1S3dRaA1A3S3aVsegs;RcS2fRbA1RaA4S0ScS1aA1S61S1aS2fRcA1R9A3SeS1aR8A2A3S0S8S2eS22R9A1A1SaA3S50S29RfRaA2S1eRfR9A2A2S50S51S1eR10RaA2R9A2S28R10RbA2A2S52Z0RaA2S50RbZ8A2S0S15Q40A1ScS15Q8A1A1F_;M0S5dR10A1S5dR11A1A3S0G0S5cR11A1S5eS5cR12A1S2bR14S26RfA1S1eR14ReA2A3S21S55RdA1S25R14RcA2A2A3A3S3aVsegs;R15S73S1aS2fR14A1R11S1aS68S3dR15A1R1R10RfReA5Lo1;A4R12A4F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Fn;Fms';Fms;FS;Frho;").
Proof using .
  intros rho S ms ms' n o off k v Hrom Hwf Hf Hmm Hnth Hdw Hlo Hhi Hk Hk8 Hr Hm.
  rewrite (list_upd_is_set _ _ _ _ Hnth).
  pose proof (mem_match_nth segs _ _ _ _ _ Hmm Hnth) as Hoh.
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  destruct Hmm as (Hall & Hpd & Hfr).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  pose proof (proj1 Hoh) as HB. unfold obj_lo_of, obj_hi_of in *.
  assert (Ha : bv_unsigned (oaddr rho (ob_base o) (soff rho off)) = bv_unsigned (eval rho (ob_base o)) + soff rho off).
  { apply oaddr_unsigned. lia. }
  split; [|split].
  - apply Forall_forall. intros o2 Hin2.
    destruct (In_list_set _ _ _ _ Hin2) as [-> | (m & Hne & Hm2)].
    + eapply obj_holds_store_d; eauto.
    + eapply (obj_holds_frame rho (ss_next S)); [exact Hr | exact Hm | rewrite Ha, Hlen, Z2Nat.id by lia; lia | | eapply swf_obj_nth; eauto | ].
      * pose proof (pairwise_disjoint_nth rho _ _ _ _ _ Hpd Hnth Hm2 ltac:(lia)) as D.
        unfold obj_range, obj_lo_of, obj_hi_of in D |- *. unfold ranges_disjoint in D |- *. cbn [fst snd] in D |- *.
        rewrite Ha, Hlen, Z2Nat.id by lia. lia.
      * exact (proj1 (Forall_forall _ _) Hall o2 (nth_error_In _ _ Hm2)).
  - eapply pairwise_disjoint_set; [exact Hnth | apply obj_range_store_d | exact Hpd].
  - intros a Ha'. apply (proj1 (outside_all_set rho (ss_objs S) n o (obj_store_d (ss_facts S) o off k v) a Hnth (obj_range_store_d _ _ _ _ _ _))) in Ha'.
    rewrite Hm. rewrite write_to_mem_out.
    + apply Hfr. exact Ha'.
    + rewrite Ha, Hlen, Z2Nat.id by lia. lia.
    + rewrite Ha, Hlen, Z2Nat.id by lia.
      pose proof (proj1 (Forall_forall _ _) Ha' o (nth_error_In _ _ Hnth)) as Ho. cbn in Ho.
      unfold obj_range, obj_lo_of, obj_hi_of in Ho. cbn [fst snd] in Ho. lia.
Qed.

Lemma cell_wf_intro : ltac2:(tb__ "0|0|
S7S1bS52Z0S2dR1A1A2S50S2dR2A1Z8A2S0S8S24R4S36R3A1A2SaA3S0S8S24R5S37R4A1A2SaA3S0S8S47R6R5A2SaA3F_;F_;F_;F_;Fc;Fn;").
Proof using .
  intros. unfold cell_wf. rewrite H1, H2.
  rewrite (proj2 (Z.ltb_lt 0 (c_width c))) by lia. rewrite (proj2 (Z.leb_le (c_width c) 8)) by lia. reflexivity.
Qed.

Lemma obj_wf_store : ltac2:(tb__ "0|0|
S7S9S1cA1S1aS19S6S19S0S8S23R6R4A2SaA3S0S8S24R7R4A2SaA3S0S8S24R8R3A2SaA3S52Z0R5A2S50R6Z8A2S0S8S23RbS6bRaR9R8R7R6A5A2SaA3F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Ffacts;Fn;").
Proof using .
  intros n facts o off k v Hwf Hoff Hv Hk Hk8.
  destruct (obj_wf_parts _ _ Hwf) as (Hb & Hlo & Hhi & Hcells).
  pose proof (obj_wf_dflt _ _ Hwf) as Hdwf.
  unfold obj_store. destruct (store_cells facts (ob_cells o) off k) as [cells' taint] eqn:Esc.
  unfold obj_wf. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt]. rewrite Hb, Hlo, Hhi. cbn [andb forallb].
  rewrite (ltac:(destruct taint; [reflexivity | exact Hdwf]) : dflt_wf n (if taint then DUnknown else ob_dflt o) = true).
  rewrite Bool.andb_true_r.
  apply andb_true_intro. split.
  - apply cell_wf_intro; cbn; auto.
  - apply forallb_forall. intros c' Hin'.
    assert (Hin0 : In c' (fst (store_cells facts (ob_cells o) off k))) by (rewrite Esc; exact Hin').
    destruct (store_cells_spec _ _ _ _ _ Hin0) as (c & Hin & Hcase).
    destruct (obj_wf_cell _ _ _ Hwf Hin) as (C1 & C2 & C3 & C4).
    destruct Hcase as [[Hcr ->] | [(d & Hcr & Ho & ->) | [(d & Hcr & Ho & Hdn & ->) | (d & Hcr & Ho & Hkd & ->)]]].
    + exact (proj1 (forallb_forall _ _) Hcells c Hin).
    + exact (proj1 (forallb_forall _ _) Hcells c Hin).
    + unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
      apply cell_wf_intro; cbn; auto; lia.
    + unfold lit_overlaps in Ho. apply andb_prop in Ho as [HoA HoB]. apply Z.ltb_lt in HoA. apply Z.ltb_lt in HoB.
      apply cell_wf_intro; cbn [c_off c_width c_val]; try lia.
      * apply mk_addk_below. exact Hoff.
      * apply mk_alu_below; [exact C4 | reflexivity].
Qed.

Lemma obj_wf_store_d : ltac2:(tb__ "0|0|
S7S9S1cA1S1aS19S6S19S0S8S23R6R4A2SaA3S0S8S24R7R4A2SaA3S0S8S24R8R3A2SaA3S52Z0R5A2S50R6Z8A2S0S8S23RbS68RaR9R8R7R6A5A2SaA3F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Ffacts;Fn;").
Proof using .
  intros n facts o off k v Hwf Hoff Hv Hk Hk8.
  pose proof (obj_wf_store n facts o off k v Hwf Hoff Hv Hk Hk8) as H.
  pose proof (obj_wf_dflt _ _ Hwf) as Hdwf.
  unfold obj_store_d. destruct (ob_dflt o) eqn:Hd; try exact H.
  unfold obj_wf in H |- *. cbn [ob_base ob_lo ob_hi ob_cells ob_dflt] in *.
  apply andb_prop in H as [H _]. rewrite H. cbn [andb].
  destruct (arr_after_store_cases facts o off k v esz cnt flds tmpl) as [E|E]; rewrite E; [reflexivity|]. rewrite Hd. exact Hdwf.
Qed.

Lemma forallb_list_upd : forall {A} (f : A -> bool) (g : A -> A) l n,
  forallb f l = true -> (forall x, In x l -> f x = true -> f (g x) = true) -> forallb f (list_upd l n g) = true.
Proof using .
  induction l as [|h t IH]; intros n Hl Hg; [reflexivity|].
  cbn in Hl. apply andb_prop in Hl as [Hh Ht]. destruct n; cbn.
  - rewrite (Hg h (or_introl eq_refl) Hh), Ht. reflexivity.
  - rewrite Hh. cbn. apply IH; [exact Ht|]. intros x Hx. apply Hg. right. exact Hx.
Qed.

Lemma swf_store : ltac2:(tb__ "0|0|
S20SbS1aS19S6S19S0S8S34R6A1SaA3S0ScS1aA1S61S1aS2fR7A1R6A3SeS1aR5A2A3S0S8S24S33R8A1R5A2SaA3S0S8S24S33R9A1R4A2SaA3S52Z0R6A2S50R7Z8A2S0S8S34S77RcS73S1aS2fRcA1RbS1aS68S3dRdA1R1RaR9R8A5Lo1;A4A2A1SaA3F_;F_;F_;F_;F_;F_;Fv;Fk;Foff;Fo;Fn;FS;").
Proof using .
  intros S n o off k v Hwf Hnth Hoff Hv Hk Hk8.
  rewrite (list_upd_is_set _ _ _ _ Hnth).
  pose proof (swf_obj_nth _ _ _ Hwf Hnth) as Howf.
  unfold swf in Hwf |- *. unfold set_objs. cbn [ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next] in *.
  repeat (apply andb_prop in Hwf; destruct Hwf as [Hwf ?]).
  repeat (apply andb_true_intro; split); try assumption.
  apply forallb_list_set; [assumption|]. apply obj_wf_store_d; assumption.
Qed.

Lemma sym_store_sound : ltac2:(tb__ "0|6|
S20S19S6S19S20S1dS9S92A1M0S5bS91S0ScS20A1S78R9R8R7R6A4SeS20R5A2A3S45Vsegs;R5RaS13G0S8fR4S90R3R2A2A4A4S0S8S24S33RbA1RaA2SaA3S0S8S24S33RcA1R9A2SaA3S3S0S6RbZ1A3S3S0S6RbZ2A3S3S0S6RbZ4A3S0S6RbZ8A3A2A2A2S25R9RdA2S15Q40A1M1S21S55RdA1S25RaRcA2A2S9S15Q8A1M2A1S1S0S8S60Vsegs;S5cR9A1R2S55ReA1A4SaA3S4S9S1aA1M3G3S1S0S20RdS77R11R1A2M4A3S1S0S8S34G4A1SaA3S5bS0G1ScG2A1F_;M5S5dR1A1S5dRbA1A3S0G5S5cR2A1S5eS5cRcA1R5R4A3A3S1S3cVsegs;R3A2S3aVsegs;RfR4R3A4A2F_;F_;Fms';A2A2Lobjs';A2A2Tbs;Ta;F_;F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fv;Fk;Fae;FS;").
Proof using .
  intros S ae k v S' rho tr ms md Hst Hsm Hae Hv Hk.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  destruct (k_cases k Hk) as (Hk0 & Hk8 & Hkn & Hw & Hwpos).
  assert (Hlen : length (enc_bytes (Z.to_nat k) (eval rho v)) = Z.to_nat k) by apply enc_bytes_length.
  unfold sym_store in Hst.
  destruct (find_obj (ss_objs S) (ss_facts S) ae k 0) as [[[n o] off]|] eqn:Hfo; [|discriminate].
  destruct (dflt_writable (ob_dflt o)) eqn:Hdw; [|discriminate].
  inversion Hst; subst S'; clear Hst.
  destruct (find_obj_sound segs rho S tr ms md ae k n o off Hsm0 Hk0 Hfo)
    as (Hnth & Hoh & Howf & Hro & Hib & HU & Hea & Hlo & Hhi).
  pose proof (rel_offset_below (ss_next S) (ob_base o) ae off Hae (proj1 (obj_wf_parts _ _ Howf)) Hro) as Hoff.
  cbn zeta. rewrite Hea. split.
  { eapply obj_store_ok; eauto. }
  eexists. split; [reflexivity|]. split.
  { eapply swf_store; eauto. }
  intros ms' Hr Hm. split.
  + eapply (ro_clear_store rho ms ms' o (soff rho off) k); eauto.
  + eapply mem_match_store; eauto.
Qed.

Lemma case_store : ltac2:(tb__ "0|2|
S20S88S15Q5A1M0G0S15QcA1S20S1dS9S92A1M1S5bS91S0ScS8aA1S7fVsegs;S46RaA1A2SeS8aS8bR9R8R7R6A4A2A3S0ScS19A1S4fRbA1S11S19A1A3S0ScS20A1S78RcS67S71RcRaA2S7eR8A1A2S76RbA1S71RcR9A2A4SeS20R7A2A3S45Vsegs;R7RdS13G1S8fR6S90R5R4A2A4A4S95Vsegs;ReS84R9S51S46ReA1Z4A2A2R8R7R6R5A7F_;F_;F_;F_;Fmd;Fms;Ftr;Frho;FS';Fimm;Frs2;Frs1;Fsz;FS;").
Proof using .
  intros S sz rs1 rs2 imm S' rho tr ms md Hi Hresv Hst Hsm.
  pose proof Hsm as Hsm0.
  destruct Hsm as (Hwf & Hpc & Hpend & Hhalt & Hrom & Hroc & Hregs & Hfregs & Hfcsr & Hresvm & Hmem & Hfacts).
  cbn [fst snd cfg_ms cfg_model] in *.
  assert (Hae : sv_below (ss_next S) (mk_addk (get_reg S rs1) (immI imm)) = true) by (apply mk_addk_below, get_reg_below; exact Hwf).
  assert (Hv : sv_below (ss_next S) (get_reg S rs2) = true) by (apply get_reg_below; exact Hwf).
  destruct (sym_store_sound S _ (msz sz) _ S' rho tr ms md Hst Hsm0 Hae Hv (msz_cases sz)) as (Hok & objs' & ES & Hwf' & Hpost).
  subst S'. cbn zeta in Hok, Hpost.
  assert (Haddr : (rget (core_of ms) rs1 + sext 64 imm)%bv = eval rho (mk_addk (get_reg S rs1) (immI imm))).
  { rewrite (rget_match segs rho S tr ms md rs1 Hsm0). change (sext 64 imm) with (Z_to_bv 64 (immI imm)).
    rewrite <- mk_addk_sound. reflexivity. }
  assert (Hresv0 : ms_resv ms = None).
  { unfold resv_match in Hresvm. rewrite Hresv in Hresvm. destruct (ms_resv ms); [destruct Hresvm|reflexivity]. }
  set (a := eval rho (mk_addk (get_reg S rs1) (immI imm))) in *.
  set (bs := enc_bytes (Z.to_nat (msz sz)) (eval rho (get_reg S rs2))) in *.
  set (m' := write_to_mem (ms_mem ms) a bs).
  set (ms1 := ms_of ms (with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)) m').
  destruct (Hpost ms1 eq_refl eq_refl) as [Hroc1 Hmem1].
  eapply next_rel_same_rho with (ms' := ms1).
  - rewrite (step_instr_at segs ms (ss_pc S) _ Hpc Hi ltac:(discriminate)).
    change (exec (Z_to_bv 64 4) (Store sz rs1 rs2 imm) (core_of ms))
      with (store_val sz (rget (core_of ms) rs1 + sext 64 imm)%bv (rget (core_of ms) rs2)
              (EDone (inval_resv (rget (core_of ms) rs1 + sext 64 imm)%bv
                        (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))))).
    rewrite Haddr. rewrite (rget_match segs rho S tr ms md rs2 Hsm0).
    assert (Hinv : inval_resv a (with_pc (c_pc (core_of ms) + Z_to_bv 64 4)%bv (core_of ms))
                   = with_pc (Z_to_bv 64 (ss_pc S + 4)) (core_of ms)).
    { unfold inval_resv, with_pc, with_resv, core_of. cbn. rewrite Hresv0.
      change (ms_pc_val ms) with (ms_pc ms). rewrite Hpc, pc_plus'. reflexivity. }
    destruct sz; cbn [store_val interp_eff0 width_bytes].
    + change (Z.to_nat (msz SZ1)) with 1%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ1 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ2)) with 2%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ2 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ4)) with 4%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ4 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
    + change (Z.to_nat (msz SZ8)) with 8%nat in Hok. rewrite Hok, Hinv.
      pose proof (store_bytes_enc SZ8 (eval rho (get_reg S rs2))) as E. cbn [msz msize_bytes] in E. rewrite E. reflexivity.
  - cbn. lia.
  - unfold smatch. cbn [fst snd cfg_ms cfg_model set_pc set_objs ss_pc ss_regs ss_fregs ss_fcsr ss_resv ss_objs ss_facts ss_next].
    split; [rewrite swf_set_pc; exact Hwf' |].
    split; [reflexivity | split; [reflexivity | split; [exact Hhalt | split; [exact Hrom | split; [exact Hroc1|]]]]].
    split; [exact Hregs|]. split; [exact Hfregs|]. split; [exact Hfcsr|].
    split; [unfold resv_match; rewrite Hresv; cbn; rewrite Hresv0; exact I|].
    split; [exact Hmem1 | exact Hfacts].
Qed.

End W.
