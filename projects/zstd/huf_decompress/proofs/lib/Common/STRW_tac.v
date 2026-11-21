(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (mc_read1, mc_read4, mc_store_ok and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import STRW_merge.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_STRW_tac () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Mem8bytes_atC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef5skipnC47Corelib5Lists7ListDef6firstnI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02c59OSSVerify5KrLib6Common8STRW_tac8ld_factsC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00C46Stdlib5Lists4List9nth_errorK47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=ov_read_bytesK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltK47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC59OSSVerify5KrLib6Common6StrFun:window_nthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indK46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib3Arr9u8ro_readC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2ex00C47Corelib4Init5Logic7f_equalC47Corelib4Init3Nat3minC46Stdlib5Lists4List=length_firstnC47Corelib4Init3Nat3subC46Stdlib5Lists4List<length_skipnC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8min_specK46Stdlib9micromega7EnvRing5PExpr04C59OSSVerify5KrLib3Lib3Mem=bytes_at_readC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun:window_subC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3subC56Stdlib6ZArith4Znat5Nat2Z;inj_sub_maxC56Stdlib5Arith8PeanoNat3Nat3minC56Stdlib6ZArith4Znat5Nat2Z7inj_minC59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun6copiedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common8STRW_tac8st_factsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic8iff_reflC59OSSVerify5KrLib6Common6StrFun@u8arr_store_ok_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1c59OSSVerify5KrLib6Common8STRW_tac;mc_store_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareC59OSSVerify5KrLib3Lib3MemDbytes_at_write_otherC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFunAu8arr_write_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;copied_updZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

(* [comment removed for export] *)
Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

(* [comment removed for export] *)
Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

(* [comment removed for export] *)
Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)
Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
  (0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
  eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
  rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
  intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
  assert (L : (Z.to_nat base + kw <= length src)%nat).
  { apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
  exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
  - apply (bytes_at_read segs m S src i 4 SRC); lia.
  - eapply window_sub; eauto; lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
  intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
  intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
         (Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
  pose proof (proj1 CP) as Lbs.
  assert (SOK : store_ok segs m1 a (length xs) = true).
  { rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
  subst a. split; [|split; [|split; [|split; [|split]]]].
  - apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
  - apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
  - apply (f_equal (@length byte)) in CP || idtac.
    rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
    rewrite Hl, Hxs. eapply window_sub; eauto; lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
Qed.

(* [comment removed for export] *)
Ltac ld1 HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
                  ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
    zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
  end end.

(* [comment removed for export] *)
Ltac ld4 HW c w :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
    destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
      as [w [RD [Ew Lw]]];
    cbn [firstn skipn] in Ew;
    zstep; try clear RD
  end end.

(* [comment removed for export] *)
Ltac zify_bytes :=
  repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch type of b with
      | byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
      end
  end.
Ltac solve_le K :=
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
  cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
  zify_bytes;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
  lazymatch K with
  | 0%Z => idtac
  | _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
               | rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
  end;
  Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)
Ltac by_le K :=
  symmetry;
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first
    [ lazymatch goal with
      | |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
          lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
      | |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
          lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
      | |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
          lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
      | |- le1 (sext _ _) = _ => apply lwb0
      end
    | solve_le K ].

(* [comment removed for export] *)
Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

(* [comment removed for export] *)
Ltac cst HW c k bytes_tac :=
  lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

(* [comment removed for export] *)
Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

(* [comment removed for export] *)
Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

(* [comment removed for export] *)
Ltac cp_norm P' :=
  lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

(* [comment removed for export] *)
Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
    (m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
  bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
  mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

(* [comment removed for export] *)
Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

(* [comment removed for export] *)
Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

(* [comment removed for export] *)
Ltac finish2 :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

(* [comment removed for export] *)
Ltac mc_fin :=
  lazymatch goal with
  | DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
      let E := fresh "E" in
      pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
      apply rw_cells_of_u8arr in DST; rewrite L in DST
  end;
  finish2.

(* [comment removed for export] *)
Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := zstep; fix_lit_store.
