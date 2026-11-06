(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import
ExitSim PropExec CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim
DrainSim StoreOk Footprint SymExec StepTac ShapeAlg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__SymTac () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.State."; "LinuxProcessSemantics.Riscv.Instr."; "LinuxProcessSemantics.Riscv.Prelude."; "LinuxProcessSemantics.Riscv.Sem."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CatSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ExitSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.MmapSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.ShapeAlg."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.StreamSim."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymExec."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.SymTac.WithFP1."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1None"; "1list"; "1nat"; "1nil"; "1option"; "1prod"; "2eq"; "3Z"; "0E"; "0LH"; "4Segment"; "5machine_state"; "6SpuriousCfg"; "6mkCfg"; "7Model"; "7m_halted"]; ["7m_vm_lazy"; "8ALU_ADD"; "9bvmap"; "9sext"; ":alu32"; ":alu64"; ":low32"; ";msteps"; "<to_exit"; "=mmap_model"; ">v_addi"; ">v_addiw"; ">v_lw"; "?TSet"; "?realizes"; "@lh_next"]; ["@to_wr"; "AELit"; "AEVar"; "ASA"; "ASBLit"; "ASBVar"; "Aadenot"; "Abdenot"; "Aedenot"; "Aenv"; "Aexpr"; "Aregs_ok"; "Bpins_ok"; "Bsr_pins"; "Cadd"; "0T"]; ["0a"; "0bs"; "0code"; "0i"; "0k"; "0model"; "0ms"; "0ms'"; "0n"; "0ps"; "0regs"; "0scfg"; "0segs"; "0sr"; "DZ_to_bv"; "Dbv"]; ["Dbv_unsigned"; "0x"; "0z"]]).
Section WithFP1.
Context {fx : FPState}.
Fixpoint sr_pins (ps : list (reg * expr)) (sr : list expr) : list expr :=
match ps with
| [] => sr
| (r, e) :: rest => sr_pins rest (sr_upd sr (ridx r) e)
end.
Definition pins_ok (E : env) (regs : bvmap 5 word) (ps : list (reg * expr))
: Prop :=
Forall (fun p => getr regs (fst p) = edenot E (snd p)) ps.
Lemma regs_ok_pins : ltac2:(TCodec.tc2 tcn__SymTac "Q1&Q9'1'5'QOy5%211'Q:%5221%711%813&ByR0%911%3291&Q;r4r2r1%43321&Q<r5%23156r6&Q=%1249r3%<3421p061p0:1pSF@1pSLE1pSDG1pBQ01").
Proof.
intros E ps. induction ps as [|[r e] rest IH]; intros sr regs Hr Hp;
[exact Hr|].
unfold pins_ok in Hp. inversion Hp as [|p ps' Hh Ht Heq]; subst.
cbn [fst snd] in Hh. cbn [sr_pins].
apply IH; [apply regs_ok_pin; [exact Hr | exact Hh] | exact Ht].
Qed.
Lemma alu64_add_0 : ltac2:(TCodec.tc2 tcn__SymTac "='QOyR0%211'6&E(Ar1&QNz%2281%63541%83915pT4:1").
Proof.
intro x. rewrite alu_add. change (v_add x (Z_to_bv 64 0)) with (v_addi x 0).
apply v_addi_0.
Qed.
Lemma aluw_add_0 : ltac2:(TCodec.tc2 tcn__SymTac "E'QOyR0%211'6&CyQ0&D(A&Fr1%211&QNz%22<1%611%93851%<3;?1&L%119%@3A31pT4B1").
Proof.
intro x. rewrite low32_lit.
change (Z_to_bv 32 0) with (@Z_to_bv 32 0).
rewrite alu32_add_0. apply b_lw_val.
Qed.
Lemma aluw_addi_lit : ltac2:(TCodec.tc2 tcn__SymTac "G'QOyR0%211'7'6&CyQ0&D(A&Fr2%211&QNr1%22=1%611%93851%<3;@1&K%1296%@3B31pS:B1pS2D1").
Proof.
intros a k. apply bv_eq. unfold v_addiw.
rewrite sext32_unsigned, !Z_to_bv_unsigned. f_equal.
change (alu32 ALU_ADD (low32 a) (low32 (Z_to_bv 64 k)))
with (low32 a + low32 (Z_to_bv 64 k)).
rewrite bv_add_unsigned, !low32_unsigned, Z_to_bv_unsigned.
rewrite bv_swrap_wrap', bv_swrap_add_idemp_l.
rewrite (bv_wrap_bv_wrap 32 64 k) by lia.
rewrite bv_swrap_add_idemp_r. reflexivity.
Qed.
Lemma bdenot_var : ltac2:(TCodec.tc2 tcn__SymTac "@&Q9'2'6'QOyR0%211&Q7r2(Q5r1%211%5241%513%;3821pSB=1pB?1").
Proof. reflexivity. Qed.
Lemma bdenot_lit : ltac2:(TCodec.tc2 tcn__SymTac ">&Q9'6'QOyR0%211&Q7r1(Q4%3221&QNz%2281%;3841pB=1").
Proof. reflexivity. Qed.
Lemma edenot_lit : ltac2:(TCodec.tc2 tcn__SymTac "A&Q9'7'6'QOyR0%211&Q8r2(Q1r1%211%5241&QN%1294%<3931pT6>1pB@1").
Proof. reflexivity. Qed.
Lemma edenot_var : ltac2:(TCodec.tc2 tcn__SymTac "@&Q9'2'6'QOyR0%211&Q8r2(Q2r1%211%5241%513%;3821pSB=1pB?1").
Proof. reflexivity. Qed.
Lemma v_addi_Z : ltac2:(TCodec.tc2 tcn__SymTac "B'QOyR0%211'7'6&Jr2r1%3221&QN&Q>&R0%12;6%3216%52=1%;3=71pS8=1pT4?1").
Proof. reflexivity. Qed.
Lemma adenot_var : ltac2:(TCodec.tc2 tcn__SymTac "K&Q9'2'7'6'QOyR0%211&Q6r3(Q3(Q5r2%211r1%5221%8271&QN&Q>&R0%;18%22?1%4218%62A1%D3A81pS:F1pSBH1pBJ1").
Proof. reflexivity. Qed.
Lemma adenot_lit : ltac2:(TCodec.tc2 tcn__SymTac "B&Q9'7'6'QOyR0%211&Q6r2(Q3(Q4r1%3221%6251&QN%12:4%=3:31pS:?1pBA1").
Proof.
intros E k. unfold adenot. cbn [a_base a_off bdenot].
rewrite v_addi_Z, u_Z_to_bv64_0; f_equal; lia.
Qed.
End WithFP1.
Ltac sym_env_cbn :=
cbn [Eplus Nat.ltb Nat.leb Nat.sub Nat.add Z.of_nat nth app fst snd
a_base a_off e_addr e_width e_val].
Ltac sym_env_norm :=
sym_env_cbn;
rewrite ?adenot_var, ?adenot_lit, ?bdenot_var, ?bdenot_lit,
?edenot_lit, ?edenot_var, ?u_Z_to_bv64_0;
sym_env_cbn;
repeat match goal with
| |- context [getr ?rs (Z_to_bv 5 ?z)] =>
let u := eval vm_compute in z in
let l := constr:(@BV 5 u ltac:(vm_compute; exact I)) in
replace (Z_to_bv 5 z) with l by (apply bv_eq; vm_compute; reflexivity)
end.
Section WithFP3.
Context {fx : FPState}.
End WithFP3.
Ltac sym_z_lit k :=
lazymatch k with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac sym_z_norm :=
repeat match goal with
| |- context [Z_to_bv 64 (0 + ?k)] =>
sym_z_lit k; replace (0 + k)%Z with k by lia
| |- context [Z_to_bv 64 (?a - ?k1 + ?k2)] =>
sym_z_lit k1; sym_z_lit k2;
let v := eval vm_compute in (k1 - k2)%Z in
replace (a - k1 + k2)%Z with (a - v)%Z by lia
| |- context [Z_to_bv 64 (?a + ?k1 + ?k2)] =>
sym_z_lit k1; sym_z_lit k2;
let v := eval vm_compute in (k1 + k2)%Z in
replace (a + k1 + k2)%Z with (a + v)%Z by lia
| |- context [Z_to_bv 64 (?a + Zneg ?p)] =>
replace (a + Zneg p)%Z with (a - Zpos p)%Z by lia
end.
Ltac sym_addr_norm :=
imm_norm; rewrite ?v_addi_Z; sym_env_norm; u_norm; sym_z_norm.
Section WithFP6.
Context {fx : FPState}.
End WithFP6.
Ltac sym_lit_norm :=
repeat match goal with
| |- context [wbytes ?m (Z_to_bv 64 ?z) ?bs] =>
lazymatch z with
| Zpos _ =>
let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
replace (Z_to_bv 64 z) with l by bveq
end
| |- context [word_to_le_bytes ?n (Z_to_bv 64 ?z)] =>
lazymatch z with
| Zpos _ =>
let l := constr:(@BV 64 z ltac:(vm_compute; exact I)) in
replace (Z_to_bv 64 z) with l by bveq
end
end.
Section WithFP7.
Context {fx : FPState}.
End WithFP7.
Ltac sym_norm :=
cbn [edenot sr_get nth ridx s_regs s_pc s_log s_next branch_taken];
rewrite ?alu64_add_0, ?aluw_add_0;
rewrite ?aluw_addi_lit;
rewrite ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor,
?alu_slt, ?alu_sltu, ?alu_sll, ?alu_srl, ?alu_sra;
rewrite ?v_add_lit, ?v_sub_lit;
sym_addr_norm.
Section WithFP8.
Context {fx : FPState}.
End WithFP8.
Ltac sym_mem_norm :=
cbn [mem_denot e_addr e_width e_val];
sym_norm; sym_lit_norm.
Section WithFP9.
Context {fx : FPState}.
Lemma msteps_to_exit : ltac2:(TCodec.tc2 tcn__SymTac "G'1':%211'QOyR0%211';'Gr4r2r1%43321'Hr5%23165r6%43138p031p071pS@=1pS>>1pS6@1pSJD1").
Proof.
intros segs code ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH]; [auto|].
intro He. eapply te_step; eauto.
Qed.
Lemma msteps_to_wr : ltac2:(TCodec.tc2 tcn__SymTac "L'1':%211';!p021'QOy8%211%911'Gr5r2r1%43321'Q0r6r4%342716r7%541493p031p081pS@D1pS>E1pS4@1pDE1pSJI1").
Proof.
intros segs LH bs ms ms' H; induction H as [|ms ms1 ms2 Hp Hs Hms IH];
[auto|].
intro Hw. eapply StreamSim.twr_step; eauto.
Qed.
Lemma msteps_lh_next : ltac2:(TCodec.tc2 tcn__SymTac "F'1':%211';!p021'Gr4r2r1%43321&Or5%23165r6%43138p031p071pS@?1pS>@1pD?1pSJC1").
Proof.
intros segs LH ms ms' H (m & Hm & HL). exists m. split; [|exact HL].
eapply msteps_trans; eauto.
Qed.
End WithFP9.
Ltac sym_halted :=
solve [ reflexivity
| eassumption
| (rewrite ?MmapSim.mmap_model_halted, ?MmapSim.munmap_model_halted;
solve [ reflexivity | eassumption ])
| (cbn [cfg_model m_halted]; autorewrite with model; solve [ reflexivity | eassumption ]) ].
Ltac sym_no_lazy :=
cbn [cfg_model];
repeat first
[ rewrite MmapSim.mmap_model_lazy
| apply MmapSim.munmap_model_no_lazy ];
solve [ reflexivity | eassumption ].
Section WithFP10.
Context {fx : FPState}.
End WithFP10.
Ltac chain_mst :=
first [ eapply CatSim.msteps_to_wexit
| eapply MmapSim.msteps_twm
| eapply MmapSim.msteps_twm_tail
| eapply MmapSim.msteps_tmw
| eapply StreamSim.msteps_to_rd
| eapply msteps_to_wr
| eapply WallSim.msteps_to_wall_tail
| eapply WallSim.msteps_to_wallexit
| eapply DrainSim.msteps_to_rd
| eapply DrainSim.msteps_to_out
| eapply msteps_to_exit
| eapply msteps_lh_next
| (eapply ShapeAlg.rz_msteps; [ sym_halted | sym_no_lazy | | ])
| eapply msteps_trans ].
Section WithFP11.
Context {fx : FPState}.
Lemma chain_mst_realizes : ltac2:(TCodec.tc2 tcn__SymTac "QD'1':%211'<';'>&M'6'4'QOyR0%211%411&?r2%211(0%116%;3631'5%1299%E11&@r3%211(3%116%D3631'Gr8r6r5%43321'Nr9(=%1265r4%544921r:%52;:%84271:p041p0;1p0A1p0K1pS0Q81pS<Q:1pS@Q<1pS>Q=1pSHQ?1pSJQA1").
Proof.
intros segs scfg ms ms' model T Hh Hlazy Hms Hr.
chain_mst; [exact Hms | exact Hr].
Qed.
Lemma chain_mst_realizes_mmap : ltac2:(TCodec.tc2 tcn__SymTac "QI'1':%211'<';'>'QOyR0%211&M'6'4%114&?r4%211(0%119%83631'5%12<<%E11&@r5%211(3%116%A3631'Gr:r8r7%43321'Nr;(=&Ir6%231?7%4291%746;1Jr<%63;5<%82>1%;43:1Ep051p0>1p0D1p0N1pS0Q81pSBQ:1pS2Q;1pS<Q?1pS@QA1pS>QB1pSHQD1pSJQF1").
Proof.
intros segs scfg ms ms' model a n T Hh Hlazy Hms Hr.
chain_mst; [exact Hms | exact Hr].
Qed.
End WithFP11.
Ltac sym_close :=
first [ reflexivity
| (f_equal; lia)
| (apply bv_eq; u_norm; lia)
| bveq ].
Ltac sym_regs H :=
getr_resolve; regupd_resolve;
rewrite <- ?getr_nz by reg_neq_tac;
rewrite ?(H _);
repeat match goal with
| |- context [sr_get ?a ?b] =>
let v := eval vm_compute in (sr_get a b) in change (sr_get a b) with v
end;
sym_norm.
Section WithFP13.
Context {fx : FPState}.
End WithFP13.
Ltac sym_reg H R r v tac :=
assert (getr R r = v) by (sym_regs H; tac).
Section WithFP14.
Context {fx : FPState}.
End WithFP14.
Ltac list_len l :=
lazymatch l with
| nil => constr:(0%nat)
| @cons _ _ ?t => let n := list_len t in constr:(S n)
end.
Section WithFP15.
Context {fx : FPState}.
End WithFP15.
Ltac sym_pc_Z :=
lazymatch goal with
| |- context [ mkst ?r ?p ?m ?ro ] =>
lazymatch p with
| Z_to_bv 64 _ => idtac
| _ => check_closed_term p;
let u := vm_eval (bv_unsigned p) in
replace p with (Z_to_bv 64 u) by bveq
end
end.
Section WithFP16.
Context {fx : FPState}.
End WithFP16.
Ltac sym_pc_lit :=
try lazymatch goal with
| |- context [ mkst ?r ?p ?m ?ro ] => wlit p
end.
Section WithFP17.
Context {fx : FPState}.
End WithFP17.
Ltac sym_sc_auto :=
first [ reflexivity | (repeat split; lia) ].
Section WithFP18.
Context {fx : FPState}.
End WithFP18.
Ltac sym_pin_auto :=
first
[ reflexivity
| multimatch goal with
| H : regs_ok _ _ _ |- _ =>
sym_regs H; first [ reflexivity | (f_equal; lia) | (apply bv_eq; u_norm; lia) ]
end ].
Section WithFP19.
Context {fx : FPState}.
End WithFP19.
Ltac sym_block segs fuel dirs rds ps pvals rvals R H :=
sym_pc_Z;
lazymatch goal with
| |- context [ mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom ] =>
let k := list_len pvals in
let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
let EE := constr:(Eplus regs (pvals ++ rvals)) in
let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
let Hsc := fresh "Hsc" in
let Hst := fresh "Hst" in
let Hms := fresh "Hms" in
let Heq := fresh "Heq" in
let Hlf := fresh "Hlf" in
let msx := fresh "msx" in
assert (Hsc : scs_denot segs mem EE scs);
[ unfold scs_denot;
repeat first [ apply Forall_nil | apply Forall_cons ];
cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
try sym_norm; try sym_sc_auto
| assert (Hst : st_ok EE mem rom ss0 (mkst regs (Z_to_bv 64 pc) mem rom));
[ exists regs; split;
[ reflexivity
| split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
unfold pins_ok;
repeat first [ apply Forall_nil | apply Forall_cons ];
cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
| destruct (sym_exec_sound segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
ltac:(vm_compute; reflexivity) Hsc Hst)
as (msx & Hms & (R & Heq & H & Hlf));
clear Hsc Hst;
chain_mst; [ exact Hms | ];
rewrite Heq; clear Heq Hms msx;
cbn [s_pc s_log]; try sym_mem_norm;
norm_pc; sym_pc_lit ] ]
end.
Section WithFP20.
Context {fx : FPState}.
End WithFP20.
Ltac sym_block_ex segs ms fuel dirs rds ps pvals rvals R H Hms :=
lazymatch ms with
| mkst ?regs (Z_to_bv 64 ?pc) ?mem ?rom =>
let k := list_len pvals in
let ss0 := constr:(SS pc (sr_pins ps sr_id) (@nil sentry) (32 + k)%nat) in
let EE := constr:(Eplus regs (pvals ++ rvals)) in
let ss1 := eval vm_compute in (fst (sym_exec segs fuel dirs rds ss0 [])) in
let scs := eval vm_compute in (snd (sym_exec segs fuel dirs rds ss0 [])) in
let Hsc := fresh "Hsc" in
let Hst := fresh "Hst" in
assert (Hsc : scs_denot segs mem EE scs);
[ unfold scs_denot;
repeat first [ apply Forall_nil | apply Forall_cons ];
cbv beta iota delta [sc_denot sc_flat adenot bdenot a_base a_off];
try sym_norm; try sym_sc_auto
| assert (Hst : st_ok EE mem rom ss0 ms);
[ exists regs; split;
[ reflexivity
| split; [ apply regs_ok_pins; [ apply regs_ok_Eplus | ] | exact I ] ];
unfold pins_ok;
repeat first [ apply Forall_nil | apply Forall_cons ];
cbn [fst snd edenot]; sym_env_norm; try sym_pin_auto
| destruct (sym_exec_ex segs fuel dirs rds ss0 [] ss1 scs EE mem rom _
ltac:(vm_compute; reflexivity) Hsc Hst)
as (R & H & Hms);
clear Hsc Hst;
cbn [s_pc s_regs s_log mem_denot] in Hms ] ]
end.
Section WithFP21.
Context {fx : FPState}.
End WithFP21.
Ltac sym_chain Hms :=
sym_pc_Z; chain_mst; [ exact Hms | ]; norm_pc; sym_pc_lit.
