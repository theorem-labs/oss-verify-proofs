(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib GrayLib LeptStructs LeptExec DitherLib DitherLib2.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].

Ltac dl_nia := lia.   (* [comment removed for export] *)
Ltac dl_an :=
  rewrite ?dl_addi0; rewrite ?dl_add; rewrite ?dl_addw by lia; rewrite ?dl_zext32 by lia;
  rewrite ?dl_sllw by dl_nia; rewrite ?dl_mulw by dl_nia; rewrite ?dl_add;
  rewrite ?dl_max0 by lia; rewrite ?dl_sltu0 by lia; rewrite ?dl_slt_true by lia; rewrite ?dl_slt_false by lia; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_xor3 by lia; rewrite ?dl_bitword by lia; rewrite ?dl_dibitword by lia; rewrite ?dl_bitword_w by lia; rewrite ?dl_dibitword_w by lia; rewrite ?dl_mulc by dl_nia; rewrite ?dl_add; rewrite ?zbv_addi.

(* [comment removed for export] *)
Ltac dl_bytea_spec :=
  repeat match goal with
  | |- context [bytea ?p] =>
      let q := fresh "q" in let r := fresh "r" in let E1 := fresh "E" in let E2 := fresh "E" in let E3 := fresh "E" in
      destruct (bytea_spec p) as (q & r & E1 & E2 & E3); rewrite E3
  end.
Ltac dl_lia := first [ lia | (dl_bytea_spec; lia) ].
Ltac dl_arith := dl_an; dl_bytea_spec; rewrite ?u_Z2bv by lia; lia.

Ltac dl_sub_norm := repeat match goal with |- context [(?a + Z.neg ?p)%Z] => change (a + Z.neg p)%Z with (a - Z.pos p)%Z end.
Ltac dl_zeq := first [ reflexivity | lia | (unfold bytea; lia) | (f_equal; lia) | (unfold bytea; f_equal; lia) ].

Ltac dl_addr regs :=
  unfold adenot; cbn [a_base a_off edenot ev ex_env vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  dl_an; first [ reflexivity | (f_equal; dl_zeq) ].

Ltac dl_in := cbn [In Z.of_nat Pos.of_succ_nat Pos.succ]; repeat (first [ left; solve [f_equal; dl_zeq] | right ]).

Ltac dl_frame regs :=
  cbn [mem_denot s_log e_addr e_width e_val];
  repeat (eapply mframe_wword; [ | dl_addr regs | dl_lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | dl_in ]);
  apply mframe_refl.

(* [comment removed for export] *)
Ltac dl_guard :=
  dl_an; rewrite ?dl_seqz by dl_lia; rewrite ?dl_sltu0 by dl_lia; rewrite ?dl_xor10; rewrite ?dl_xor11; rewrite ?dl_xor01;
  rewrite ?dl_and3 by first [ dl_lia | (apply dl_al4; assumption) | assumption ];
  cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts;
  rewrite ?bv_signed_Zs by dl_lia; rewrite ?u_Z2bv by dl_lia;
  first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge
        | (apply negb_true_iff; first [apply Z.eqb_neq | apply Z.ltb_ge])
        | (apply negb_false_iff; first [apply Z.eqb_eq | apply Z.ltb_lt]) ];
  dl_lia.

(* [comment removed for export] *)
Ltac dl_side regs :=
  lazymatch goal with
  | |- store_ok _ _ _ _ = true =>
      dl_an; dl_sub_norm;
      (* [comment removed for export] *)
      first [ match goal with H : store_ok _ _ (Z_to_bv 64 ?z) ?n = true |- store_ok _ _ (Z_to_bv 64 ?z) ?n = true => exact H end
            | match goal with H : store_ok _ _ (Z_to_bv 64 ?z') ?n = true |- store_ok _ _ (Z_to_bv 64 ?z) ?n = true =>
                replace z with z' by dl_zeq; exact H end ]
  | |- exists bs, rdn _ _ _ _ = Some bs /\ _ =>
      eapply dl_read; [ dl_an; dl_sub_norm; reflexivity | | reflexivity ];
      first [ match goal with H : rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b |- rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b => exact H end
            | match goal with H : rdn _ _ (Z_to_bv 64 ?z') ?n = Some ?b |- rdn _ _ (Z_to_bv 64 ?z) ?n = Some ?b =>
                replace z with z' by dl_zeq; exact H end ]
  | |- branch_taken _ _ _ = _ => first [ assumption | ex_br | dl_guard ]
  | |- _ => first [ dl_arith | idtac ]
  end.

Ltac dl_reg regs HR' :=
  lazymatch goal with
  | |- getr _ ?k = _ =>
      rewrite (reg_val _ _ _ k HR');
      match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
      cbn [edenot ev ex_env vals_ev map app ex_regs_list nth Nat.add];
      repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
      dl_an; first [ reflexivity | (f_equal; dl_zeq) | (apply dl_srl32_eq; lia) ]
  end.

(* [comment removed for export] *)
Ltac dl_sc_prep regs :=
  unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev ex_env vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  rewrite ?ex_ptr_val, ?zbv_addi.
Ltac dl_run fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn 64%nat) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in let Hlf := fresh "Hlf" in
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; dl_sc_prep regs; dl_side regs
              | destruct (run_sound segs fuel stops scr pc sr kn 64%nat ss' scs scr' E base rom regs
                          (eq_refl _) HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc Hlf ]
          end
      end
    end
  end.

(* [comment removed for export] *)
Ltac dl_get :=
  first [ eassumption
        | match goal with AG : regs_agree _ ?R ?R' |- getr ?R' ?r = _ => rewrite (AG r) by StartupTac.notin_list; dl_get end ].
Ltac dl_in0 := cbn [In]; repeat (first [ left; reflexivity | right ]).
Ltac dl_incl := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<- | Hx]; [dl_in0 |]); destruct Hx.

(* [comment removed for export] *)
Ltac dl_saved regs :=
  cbn [mem_denot s_log e_addr e_width e_val edenot ev ex_env vals_ev map app ex_regs_list nth Nat.add];
  repeat first [ (eapply dl_rdn_hit; [ dl_addr regs | dl_lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia ])
               | (eapply dl_rdn_skip; [ dl_addr regs | dl_lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | dl_lia
                                        | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | ]) ].

(* [comment removed for export] *)
Ltac dl_mem_norm1 regs :=
  cbn [mem_denot s_log e_addr e_width e_val];
  unfold adenot; cbn [a_base a_off edenot ev ex_env vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  dl_an; dl_sub_norm.
(* [comment removed for export] *)
Ltac dl_mem_norm regs :=
  lazymatch goal with
  | |- context [mem_denot ?E ?m ?l] =>
      let MM := fresh "MM" in let M2 := fresh "M2" in let EQ := fresh "EQ" in
      set (MM := mem_denot E m l);
      evar (M2 : word -> option byte);
      assert (EQ : MM = M2) by (unfold MM, M2; dl_mem_norm1 regs; reflexivity);
      rewrite EQ; unfold M2; clear EQ M2 MM
  | |- _ => idtac
  end.
Ltac dl_in1 := cbn [In Z.of_nat Pos.of_succ_nat Pos.succ]; first [ solve [repeat (first [ left; reflexivity | right ])] | dl_in ].
Ltac dl_frame0 :=
  repeat (apply mframe_wword0; [ | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | dl_in1 ]);
  apply mframe_refl.
Ltac dl_saved0 :=
  repeat match goal with
  | |- rdn _ (wbytes _ (Z_to_bv 64 ?za) _) (Z_to_bv 64 ?z) _ = _ =>
      first [ (constr_eq za z; apply dl_rdn_hit0; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia)
            | (apply dl_rdn_skip0; [ cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; dl_lia | ]) ]
  end.
