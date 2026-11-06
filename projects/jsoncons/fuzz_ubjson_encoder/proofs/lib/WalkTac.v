(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_WalkTac () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics5Riscv7Prelude6bv_eqbc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7WalkTac8wf_chainC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7WalkTac7wf_lookC13~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec;bv_eqb_reflC13~~~C47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec6regupdC13~~~I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions5bv_eqC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z6eqb_eqC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec9getr_sameC13~~~C47Corelib4Init5Logic8eq_ind_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec:getr_otherC13~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib4Init5Logic4True01I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec5v_addC13~~~C56Stdlib6ZArith6BinInt1Z7add_0_l".
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint wf_chain (l : list (reg * word)) (R : bvmap 5 word) : bvmap 5 word :=
  match l with nil => R | cons (r, v) l' => regupd (wf_chain l' R) r v end.
Fixpoint wf_look (l : list (reg * word)) (r : reg) : option word :=
  match l with nil => None | cons (r', v) l' => if bv_eqb r r' then Some v else wf_look l' r end.
Lemma wf_getr_chain : forall l R r, bv_eqb r 0 = false ->
  getr (wf_chain l R) r = match wf_look l r with Some v => v | None => getr R r end.
Proof.
ltac2:(KReplay.run1 (kr_t_WalkTac ()) [] "p'0h01Eh11rh22Hrh31Hh41Rh51lh61nh73Hr0h81bi001bh92b1h:2b2h;1mh<2E2h=2IHh>1ah?1eh@2r'hA1vi011vi021pi031xp;1p;2p;3p;6p;4p;9p;5g0000j18Tg000Uj1STg001:j1>Tg001Xj15Tg002;R0j2RTg002[j1OTg003;j2MTg003gj3JTg004Jj31Tg0057j23Tg006Bj22Tg007Jj29Tg008Tj30Tg008nj2BTg009Hj1QTg009hj3@Tg00:Hj6;Tg00:dj2?Tg00<3j2LTg00<Rj1=Tg00<kj3<Tg00>5R1j1ITg00>Wj2HTg00?9j26Tg00?cj3GTg00@Gj2ATg00@dj2FTg00ADj4KTg00BQl9Ej6NTg00Boj5DTg00D=j4CTg00D]j5PTg00E?R2f0R3g00E_R430p=4g00F?R59023p=:g00F_R6f1R7;03p=7g00G=#8R8#S#>R9#5R:%88#8#8#8#8#>#5R8'RR;#OR<P;1M98R=g00Gbg00H@R>5J9R?9193#4R@f3RAf2RB'3/27P1P8P819A7P312B7RCn10110300021010100508[^1:]4RDX5<1B8C%Q;RE/3B/27P1P8P819E7P3PCn10110300021010100508eX2@X1:X4=P0P:P8f5R0f4RE5@;RF/3B/27P1P8P819F7P3PCn10110300021010100508\@^1:^4=\D^5<P3A0:7?RFP:PBP@X1:P7P?P3E;A19??RG#4P2PG%43X82RGP3P51?9?E;A0254RHP2P5P2p-0P3g00H\g00I8RIn0110000020000X?2P>P4P3E;PI1LI3b3RIb2b2W0%=FRFePFf7R4919BP21B23f8R>919A=023P2f:RJ9190=023f9RK/34f;RL;<Jf6RM'2P1P8P8P2%I8P71H8J19KMRNn0100000020000P3124MROn10110300021010100508]0P7A19EKRP#:g00IURQ%53RR%57RSg00J3RT%5B?07316AB16A7'7RU[16B716B3'7%5A?0B7[RV%5E?0AB\UAGB73P3n2001000000120000000W:W9W6PV^:S^9R^6QP3P9PMPLPT1A73#:17B7[RT17731AB7#:RQ[17AB\Q1F73P7n2001000000120000000X;6X66PT^;6^66P31694R6f<RT,69RQPBO3176QP3b0b3O4b3A0:0JRQP:PLf>R6919B#:f=RR/3Lf?;<6/2A=086]0^7F^2@X1:A19L?#4A0:T?#=A19RR#:13TJP6PRP7CKW0W7W2PMP3P0PEP7M9Eb3W0%4PP813>MR>/20P1P8P8PNP3POn101103000210101009083X88P4PMP0PEO3A<>JK/20P>PJPKP0P:PMA193T#4X1:P7PLP3E;A19LL#4P2A19TTPGP3P51?9TE;PHPIb0b0X<Q%=QeDDENW0n0110000020100P3O1b0b8b7P:P8PMP0CC=@;ERE/3B/27P1P8P819E7P3PCn10110300021010100508eX2@X1:X4=X=DX5<XA8X@:P7P3O2n2001102010121100100X>;P3DPW5o"). Qed.
Ltac wf_chain_list RS := lazymatch RS with regupd ?R' ?r' ?v => let l := wf_chain_list R' in constr:(cons (r', v) l) | _ => constr:(@nil (reg * word)) end.
Ltac wf_chain_base RS := lazymatch RS with regupd ?R' _ _ => wf_chain_base R' | _ => RS end.
Ltac wf_find RS r := lazymatch RS with
  | regupd ?R' ?r' ?v => let b := eval vm_compute in (bv_eqb r r') in
      lazymatch b with true => v | false => wf_find R' r end
  | _ => constr:(getr RS r) end.
Ltac wf_gres_one :=
  match goal with
  | |- context [getr (regupd ?R0 ?r' ?v0) ?r] =>
      let RS := constr:(regupd R0 r' v0) in
      let z := eval vm_compute in (bv_eqb r 0) in
      lazymatch z with
      | true => change (getr RS r) with (Z_to_bv 64 0)
      | false =>
          let l := wf_chain_list RS in let B := wf_chain_base RS in
          let val := wf_find RS r in
          let H := fresh "gH" in
          pose proof (wf_getr_chain l B r (@eq_refl bool false) : getr RS r = val) as H;
          rewrite H; clear H
      end
  end.
Ltac gres_old :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ].
Ltac gres :=
  repeat wf_gres_one;
  lazymatch goal with |- context [getr (regupd _ _ _) _] => gres_old | _ => idtac end;
  lazymatch goal with |- context [getr _ 0%bv] => rewrite ?getr_zero | _ => idtac end.
Section FPX_1. Context {fx : PropExec.FPState}. Context {bmK : BMode}.   (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma v_add_0_r : forall x : word, v_add x (Z_to_bv 64 0) = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WalkTac ()) ["FPX_1"] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg001:j1>Tg001Xj12Tg00?9j20Tg00JNj24Tg008Tj31Tg00?cj3;Tg00K4j29Tg00KZj28Tg00LMj37Tg00M9j26Tg00BQj65Tg00Mhj2:Tg00NEj1=Tg00Nfj2<Tg00G=#3#3#3#3#3#3#>R0#2R1g00F_R2f0R3,00R41403f1R5511X32g00IUR6%23R7%25R8g00J3f2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00GbR6,:4%=4E51406,<3=113eW5o"). Qed.

Lemma v_add_0_l : forall x : word, v_add (Z_to_bv 64 0) x = x.
Proof.
ltac2:(KReplay.run1 (kr_t_WalkTac ()) ["FPX_1"] "h02b1h12b2h21nh31zh41Hh51xp;1p;2p;3p;6g0000j13Tg001:j1>Tg001Xj12Tg00?9j20Tg00JNj24Tg008Tj31Tg00?cj3;Tg00K4j29Tg00KZj28Tg00LMj37Tg00M9j26Tg00BQj65Tg00Mhj2:Tg00Ooj1=Tg00Nfj2<Tg00G=#3#3#3#3#3#3#>R0#2R1g00F_R2f0R3,00R41403f1R5511X32g00IUR6%23R7%25R8g00J3f2R9#2?153f3R:/0910:5512R;[10951093512%2:?195[R<f4#2?1:9\;A;953P3n2001000000120000000W1W0W2P<^18^07^26P3P01005R6,40R7P5P2190610099123X321805970610071606E5O4b4g00GbR6/:4%=4E51406/<3=113eW5o"). Qed.
End FPX_1.


(* [comment removed for export] *)
Ltac is_pos_lit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_pos_lit q
  | xI ?q => is_pos_lit q
  end.
Ltac is_Z_lit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => is_pos_lit p
  | Zneg ?p => is_pos_lit p
  end.

(* [comment removed for export] *)
Ltac val_lit v :=
  lazymatch v with
  | Z_to_bv 64 ?z => tryif is_Z_lit z then fail else wlit_closed v
  | @BV _ _ _ => fail
  | _ => wlit_closed v
  end.

(* [comment removed for export] *)
Ltac vals_lit :=
  repeat match goal with
         | |- context [regupd _ _ ?v] => val_lit v
         end.

(* [comment removed for export] *)
Ltac vnorm := gres; imm_norm;
  lazymatch goal with |- context [v_addi _ 0%Z] => rewrite ?v_addi_0 | _ => idtac end;
  lazymatch goal with |- context [v_add _ (Z_to_bv 64 0)] => rewrite ?v_add_0_r | _ => idtac end;
  lazymatch goal with |- context [v_add (Z_to_bv 64 0) _] => rewrite ?v_add_0_l | _ => idtac end;
  vals_lit.

(* [comment removed for export] *)
Ltac stepn F D :=
  lazymatch type of D with
  | decode_any _ = Some (Jal _ _, _) => stepj F D; vnorm
  | _ => stepi F D; vnorm
  end.

(* [comment removed for export] *)
Ltac vres := gres; imm_norm; rewrite ?v_addi_0; first [ reflexivity | bveq | idtac ].
Ltac stepv F D v := stepiv F D v vres.

(* [comment removed for export] *)
Ltac stepb_tk F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_tk
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_tk
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_tk
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_tk
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_tk
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_tk
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

Ltac stepb_ft F D tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Branch BC_EQ _ _ _, _)  => eapply step_beq_ft
    | decode_any _ = Some (Branch BC_NE _ _ _, _)  => eapply step_bne_ft
    | decode_any _ = Some (Branch BC_LT _ _ _, _)  => eapply step_blt_ft
    | decode_any _ = Some (Branch BC_GE _ _ _, _)  => eapply step_bge_ft
    | decode_any _ = Some (Branch BC_LTU _ _ _, _) => eapply step_bltu_ft
    | decode_any _ = Some (Branch BC_GEU _ _ _, _) => eapply step_bgeu_ft
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; tac ]
  | step_simpl; vnorm ].

(* [comment removed for export] *)
Ltac cond_compute :=
  idtac;
  lazymatch goal with
  | |- ?g => check_closed_term g; vm_compute; reflexivity
  end.

(* [comment removed for export] *)
Ltac stepb F D :=
  first [ stepb_tk F D ltac:(cond_compute) | stepb_ft F D ltac:(cond_compute) ].

(* [comment removed for export] *)
Ltac stepret F D k tac :=
  stepjr F D k ltac:(gres; tac);
  imm_norm;
  try lazymatch goal with
      | Hk : ret_ok k |- _ => rewrite (Hk : v_jalr k 0 = k)
      | Hk : v_jalr k 0 = k |- _ => rewrite Hk
      end;
  try (wlit (v_jalr k 0)).

(* [comment removed for export] *)
Ltac stepsd F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | eapply step_sd_at with (a := aa) (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; first [ reflexivity | assumption | f_equal; lia | bveq ]
    | gres; first [ reflexivity | assumption | symmetry; assumption ]
    | oktac ]
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepld F D vv rtac :=
  chain_step;
  [ reflexivity
  | eapply step_ld with (v := vv);
    [ exact F | reflexivity | exact D
    | gres; imm_norm; rewrite ?v_addi_0; sp_norm; rtac
    | first [ apply bytes_le_to_Z_8 | reflexivity ] ]
  | step_simpl; vnorm ].
