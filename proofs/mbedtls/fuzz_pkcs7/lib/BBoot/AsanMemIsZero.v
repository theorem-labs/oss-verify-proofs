(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import SumsLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import Sums_code.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemIsZero () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa24"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa28"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa2c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa30"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa34"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa38"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa3c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa40"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa44"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa48"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa4c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa50"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa54"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa58"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa5c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa60"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa64"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa68"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa6c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa70"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa74"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa78"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa7c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa80"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa84"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa88"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa8c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa90"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa94"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa98"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aa9c"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aaa0"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aaa4"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aaa8"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aaac"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aab0"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aab4"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aab8"; "RocqVerifyHarness.AgentSubmission.BBoot.Sums_code.W_7aabc"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_andi"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regset"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.regs_agree"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.regupd"; "Stdlib.Lists.List.In"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.ret_ok"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.ABoot.CatSim.msteps"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "MEMISZERO.mem1"; "memisz_clob'"; "MEMISZERO.dAE"; "Stdlib.ZArith.BinInt.Z.mul"; "MEMISZERO.dAB"; "Stdlib.ZArith.BinInt.Z.min"; "memisz_clob"; "RocqVerifyHarness.AgentSubmission.ABoot.SumsLib.code_at"; "memisz_words"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "asan_mem_is_zero_entry"].


(* [comment removed for export] *)
Definition memisz_words : list (bv 32) := ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "(0.(1.&20.)$2.(0.(1.&20.)$3.(0.(1.&20.)$4.(0.(1.&20.)$5.(0.(1.&20.)$6.(0.(1.&20.)$7.(0.(1.&20.)$8.(0.(1.&20.)$9.(0.(1.&20.)$:.(0.(1.&20.)$;.(0.(1.&20.)$<.(0.(1.&20.)$=.(0.(1.&20.)$>.(0.(1.&20.)$?.(0.(1.&20.)$10.(0.(1.&20.)$11.(0.(1.&20.)$12.(0.(1.&20.)$13.(0.(1.&20.)$14.(0.(1.&20.)$15.(0.(1.&20.)$16.(0.(1.&20.)$17.(0.(1.&20.)$18.(0.(1.&20.)$19.(0.(1.&20.)$1:.(0.(1.&20.)$1;.(0.(1.&20.)$1<.(0.(1.&20.)$1=.(0.(1.&20.)$1>.(0.(1.&20.)$1?.(0.(1.&20.)$20.(0.(1.&20.)$21.(0.(1.&20.)$22.(0.(1.&20.)$23.(0.(1.&20.)$24.(0.(1.&20.)$25.(0.(1.&20.)$26.(0.(1.&20.)$27.(0.(1.&20.)$28.(29.(1.&20.)))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition memisz_clob : list reg := [10; 11; 12; 13; 14; 15; 16].
(* [comment removed for export] *)
Definition memisz_clob' : list reg := [1; 2; 10; 11; 12; 13; 14; 15; 16].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_m8 : forall a, (0 <= a < 2 ^ 64)%Z -> Z.land a (2 ^ 64 - 2 ^ 3) = (a - a mod 8)%Z.
Proof.
  intros a Ha.
  replace (2 ^ 64 - 2 ^ 3)%Z with (Z.ldiff (Z.ones 64) (Z.ones 3)).
  2:{ rewrite Z.ldiff_land, <- Z.sub_land_same_l, Z.land_ones by lia.
      rewrite Z.ones_mod_pow2 by lia. rewrite !Z.ones_equiv. lia. }
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia.
  rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod a (2 ^ 3) ltac:(lia)). change (2 ^ 3)%Z with 8%Z in *. lia.
Qed.

(* [comment removed for export] *)
Lemma v_andi_m8 : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pa,(1.&40.)Pd,$2:.P,(2;.(2<.=(2=.(2>.&40.R2.)R1.))(2?.(2=.(2>.&40.R2.)R1.)(30.+2.+40.)))(31.(1.&40.)(32.(33.R3.R2.)-8.)(33.R3.(34.R2.(35.(2=.(2>.&40.R3.)R2.)+8.))))")
(* [comment removed for export] *).
Proof.
  intros a d Hd. unfold v_andi, at_. f_equal.
  change (bv_wrap 64 (-8)) with (2 ^ 64 - 2 ^ 3)%Z.
  rewrite u_Z2bv by lia. rewrite land_m8 by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_all1 : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Psegs,(36.$37.)Pm,P,(1.&40.)(38.(1.&8.))Pn,$39.Pa,(1.&40.)Pb,(1.&8.)P,(2<.(2=.(2>.&40.R2.)(3:.R3.))(30.+2.+40.))P,Px,(1.&40.)P,(2;.(2<.(2>.&40.R4.)(2>.&40.R1.))(2?.(2>.&40.R1.)(2=.(2>.&40.R4.)(3:.R5.))))(31.(38.(36.(1.&8.)))(3;.R8.R7.R2.#1.)(3<.(36.(1.&8.))(0.(1.&8.)R4.(29.(1.&8.)))))(31.(38.(36.(1.&8.)))(3;.R7.R6.R4.R5.)(3<.(36.(1.&8.))(3=.(1.&8.)R3.R5.)))")
(* [comment removed for export] *).
Proof.
  intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
  pose proof (Hall a ltac:(lia)) as R. cbn [rdn repeat] in R |- *.
  destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
  injection R as ->.
  destruct n as [|n'].
  - reflexivity.
  - assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
    rewrite (IH (a + 1) b) by (rewrite Hu1; first [lia | intros x Hx; apply Hall; lia]).
    reflexivity.
Qed.

Lemma regs_agree_upd_same : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "PC,$3>.Pregs,(3?.&5.(1.&40.))Pregs',(3?.&5.(1.&40.))Pr,(1.&5.)Pv,(1.&40.)P,(40.R5.R4.R3.)P,(31.(1.&40.)(41.R5.R3.)R2.)P,(42.(31.(1.&5.)R4.(43.&5.=$44.)))(40.R8.R7.(45.R6.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros C regs regs' r v AG Hv Hnz x Hx.
  destruct (decide (x = r)) as [->|Hne].
  - rewrite getr_same by exact Hnz. symmetry. exact Hv.
  - rewrite getr_other by exact Hne. apply AG, Hx.
Qed.

(* [comment removed for export] *)
Lemma regs_agree_strengthen : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pl,(36.(1.&5.))Pl',(36.(1.&5.))Pregs,(3?.&5.(1.&40.))Pregs',(3?.&5.(1.&40.))P,(40.Lr,(1.&5.)(46.(1.&5.)R1.R4.)R2.R1.)P,Pr,(1.&5.)P,(46.(1.&5.)R1.R5.)P,(42.(46.(1.&5.)R2.R7.))(31.(1.&40.)(41.R5.R3.)(41.R6.R3.))(40.Lr,(1.&5.)(46.(1.&5.)R1.R7.)R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros l l' regs regs' AG E r Hr.
  destruct (In_dec (fun x y : reg => decide (x = y)) r l') as [Hin|Hnin].
  - apply E; assumption.
  - apply AG, Hnin.
Qed.

Section MEMISZERO.
  Variable segs : list Segment.
  Variable base : word.
  Variable mem : word -> option byte.
  Variables beg sp : word.
  Variable N : Z.            (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Hypothesis HCODE : code_at segs base 0 memisz_words.
  Hypothesis HN : (0 <= N <= 2 ^ 40)%Z.
  Hypothesis Hnw : (bv_unsigned beg + N + 8 <= 2 ^ 64)%Z.
  Hypothesis Hsp : (16 <= bv_unsigned sp)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-8)) 8 = true.
  Hypothesis Hdisj : (bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg)%Z.
  Hypothesis Hz : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pa,(1.&40.)P,(2;.(2<.(2>.&40.Vbeg,)(2>.&40.R1.))(2?.(2>.&40.R1.)(2=.(2>.&40.Vbeg,)VN,)))(31.(38.(36.(1.&8.)))(3;.Vsegs,Vmem,R2.#1.)(3<.(36.(1.&8.))(0.(1.&8.)(47.&8.=)(29.(1.&8.)))))")
(* [comment removed for export] *).

  #[local] Abbreviation B := (bv_unsigned beg).
  #[local] Abbreviation Z0 := (Z_to_bv 64 0).
  #[local] Abbreviation CL := (fun r => In r memisz_clob').
  (* [comment removed for export] *)
  Definition dAB : Z := 7 - (B + 7) mod 8.
  Definition dAE : Z := N - (B + N) mod 8.
  (* [comment removed for export] *)
  Definition mem1 (ra : word) : word -> option byte := wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ra).

  #[using="Type"] Lemma dAB_range : (0 <= dAB <= 7)%Z.
  Proof. unfold dAB. pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). lia. Qed.

  #[using="sp HN Hsp"] Lemma dAE_range : (N - 7 <= dAE <= N)%Z /\ (0 <= B + dAE)%Z.
  Proof.
    unfold dAE. pose proof (u64_range beg). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
    pose proof (Z.div_mod (B + N) 8 ltac:(lia)). nia.
  Qed.

  (* [comment removed for export] *)
  #[using="Hnw Hsp Hdisj Hz"] Lemma rd1 : forall ra j, (0 <= j < N)%Z -> rdn segs (mem1 ra) (at_ beg j) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros ra j Hj. pose proof (u64_range beg). pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out; rewrite ?length_N_to_le_bytes, ?at_u; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.
    apply Hz. rewrite at_u; lia.
  Qed.

  #[using="Hnw Hsp Hdisj Hz"] Lemma rd8 : forall ra j, (0 <= j)%Z -> (j + 8 <= N)%Z -> rdn segs (mem1 ra) (at_ beg j) 8 = Some (zeros 8).
  Proof.
    intros ra j Hj H8. pose proof (u64_range beg). unfold zeros. apply rdn_all1; [rewrite at_u; cbn; lia|].
    intros x Hx. rewrite at_u in Hx by lia. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx.
    replace x with (at_ beg (bv_unsigned x - B)).
    - apply rd1. lia.
    - unfold at_. rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. f_equal. lia.
  Qed.

  #[using="Hsp"] Lemma rd_ra : forall ra, rdn segs (mem1 ra) (at_ sp (-8)) 8 = Some (word_to_le_bytes 8 ra).
  Proof. intros ra. unfold mem1. apply rdn_wbytes_hit8. pose proof (u64_range sp). rewrite at_u; lia. Qed.

  Ltac get_code :=
    let HC := fresh "HC" in
    pose proof HCODE as HC; cbn [code_at memisz_words Z.add Pos.add Pos.succ] in HC;
    destruct HC as (C0 & C4 & C8 & C12 & C16 & C20 & C24 & C28 & C32 & C36 & C40 & C44 & C48 & C52 & C56
                    & C60 & C64 & C68 & C72 & C76 & C80 & C84 & C88 & C92 & C96 & C100 & C104 & C108 & C112
                    & C116 & C120 & C124 & C128 & C132 & C136 & C140 & C144 & C148 & C152 & _).

  (* [comment removed for export] *)
  Ltac mlbu F D :=
    chain_step; [reflexivity
      | eapply step_lbu with (b := Z_to_bv 8 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd1; lia]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac mld F D :=
    chain_step; [reflexivity
      | eapply step_ld with (bs := zeros 8) (v := Z_to_bv 64 0);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; apply rd8; lia
        | reflexivity]
      | step_simpl]; vn.

  Ltac ra_solve :=
    repeat (first [ apply regs_agree_upd; [in_list|]
                  | apply regs_agree_upd_same; [| rwH; rewrite ?at_0; reflexivity | let X := fresh in intros X; discriminate X] ]);
    first [apply regs_agree_refl | assumption].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE Hsp"] Lemma fin_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(48.R1.)P,(31.(1.&40.)(41.R3.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R4.(43.&5.+;.$44.))(47.&40.=))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R6.(33.Vbase,+8<.)(4=.R5.)Vrom,)(4;.$4<.R1.R5.(4=.R5.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R6.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R5.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H2 H11. pose proof (u64_range sp).
    eexists. split; [|split; [|split; [|split]]].
    - an C140 D_7aab0.                            (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (v := ret);
          [exact C144 | reflexivity | exact D_7aab4
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; apply rd_ra
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                         (* [comment removed for export] *)
      an C148 D_7aab8.                            (* [comment removed for export] *)
      aret C152 D_7aabc ret.
      apply mst_refl.
    - unfold memisz_clob'. solve_regs_agree.
    - gres. reflexivity.
    - gres. rewrite ?at_0. reflexivity.
    - gres. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma ep_loop : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pi,$39.Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)Pq,$2:.Pcnt,$2:.P,(48.R3.)P,(31.(1.&40.)(41.R5.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R6.(43.&5.+;.$44.))(47.&40.=))P,(31.(1.&40.)(41.R7.(43.&5.+<.$44.))(33.Vbeg,R5.))P,(31.(1.&40.)(41.R8.(43.&5.+>.$44.))(47.&40.R5.))P,(2<.=R7.)P,(2<.+1.R7.)P,(2<.(2=.R9.R8.)VN,)P,(31.$2:.(3:.R=.)(34.R9.+1.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R>.(33.Vbase,+78.)(4=.R=.)Vrom,)(4;.$4<.R1.R=.(4=.R=.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R>.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R=.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range beg) as Hb.
    induction i as [|i IH]; intros regs ret q cnt Hret H2 H11 H12 H14 Hq Hc Hqc Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_7aa9c.                      (* [comment removed for export] *)
          av C124 D_7aaa0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).  (* [comment removed for export] *)
          an C128 D_7aaa4.                        (* [comment removed for export] *)
          an C132 D_7aaa8.                        (* [comment removed for export] *)
          ab_ft C136 D_7aaac ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg (q + 1)
                         /\ getr r 14 = Z_to_bv 64 (cnt - 1) /\ regs_agree CL regs r)).
      + eexists. split.
        * mlbu C120 D_7aa9c.
          av C124 D_7aaa0 (Z_to_bv 64 (cnt - 1)) ltac:(unfold v_addi; unorm; f_equal; lia).
          an C128 D_7aaa4.
          an C132 D_7aaa8.
          ab_tk C136 D_7aaac ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
        destruct (IH r1 ret (q + 1)%Z (cnt - 1)%Z Hret R2 R11 R12 R14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma tail_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(48.R1.)P,(31.(1.&40.)(41.R3.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R4.(43.&5.+:.$44.))Vbeg,)P,(31.(1.&40.)(41.R5.(43.&5.+;.$44.))(47.&40.=))P,(31.(1.&40.)(41.R6.(43.&5.+<.$44.))(33.Vbeg,$4?.))P,(31.(1.&40.)(41.R7.(43.&5.+>.$44.))(33.Vbeg,VN,))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R9.(33.Vbase,+6<.)(4=.R8.)Vrom,)(4;.$4<.R1.R8.(4=.R8.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R9.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R8.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    destruct (Z.lt_ge_cases dAE 0) as [Hneg|Hnn].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C108 D_7aa90 ltac:(rewrite <- (at_0 beg) at 2; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R11 & AG).
        destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.lt_ge_cases dAE N) as [Hlt|Hge].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 120) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = Z_to_bv 64 (N - dAE) /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_7aa90 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_ft C112 D_7aa94 ltac:(condz).                              (* [comment removed for export] *)
             av C116 D_7aa98 (Z_to_bv 64 (N - dAE)) ltac:(unfold v_sub, at_; unorm; f_equal; lia).  (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R11 & R12 & R14 & AG).
          destruct (ep_loop (Z.to_nat (N - dAE - 1)) r1 ret dAE (N - dAE) Hret R2 R11 R12 R14
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 140) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 11 = Z0 /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C108 D_7aa90 ltac:(rewrite <- (at_0 beg) at 2; condz).  (* [comment removed for export] *)
             ab_tk C112 D_7aa94 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; apply regs_agree_refl.
        * cbv beta. intros r1 (R2 & R11 & AG).
          destruct (fin_run r1 ret Hret R2 R11) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma w_loop : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pi,$39.Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)Pp,$2:.P,(48.R2.)P,(31.(1.&40.)(41.R4.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R5.(43.&5.+:.$44.))Vbeg,)P,(31.(1.&40.)(41.R6.(43.&5.+;.$44.))(47.&40.=))P,(31.(1.&40.)(41.R7.(43.&5.+<.$44.))(33.Vbeg,$4?.))P,(31.(1.&40.)(41.R8.(43.&5.+>.$44.))(33.Vbeg,VN,))P,(31.(1.&40.)(41.R9.(43.&5.+?.$44.))(33.Vbeg,R7.))P,(2<.=R8.)P,(2<.(2=.R9.+8.)$4?.)P,(31.$2:.(50.(3:.R=.)+8.)(34.(34.$4?.R:.)+8.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R>.(33.Vbase,+5<.)(4=.R=.)Vrom,)(4;.$4<.R1.R=.(4=.R=.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R>.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R=.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE.
    induction i as [|i IH]; intros regs ret p Hret H2 H10 H11 H12 H14 H15 Hp Hp8 Hi.
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_7aa80.                        (* [comment removed for export] *)
          an C96 D_7aa84.                         (* [comment removed for export] *)
          an C100 D_7aa88.                        (* [comment removed for export] *)
          ab_ft C104 D_7aa8c ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg (p + 8) /\ regs_agree CL regs r)).
      + eexists. split.
        * mld C92 D_7aa80.
          an C96 D_7aa84.
          an C100 D_7aa88.
          ab_tk C104 D_7aa8c ltac:(condz).        (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (IH r1 ret (p + 8)%Z Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma mid_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(48.R1.)P,(31.(1.&40.)(41.R3.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R4.(43.&5.+:.$44.))Vbeg,)P,(31.(1.&40.)(41.R5.(43.&5.+;.$44.))(47.&40.=))P,(31.(1.&40.)(41.R6.(43.&5.+<.$44.))(33.Vbeg,$4?.))P,(31.(1.&40.)(41.R7.(43.&5.+>.$44.))(33.Vbeg,VN,))P,(31.(1.&40.)(41.R8.(43.&5.+?.$44.))(33.Vbeg,$51.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R:.(33.Vbase,+58.)(4=.R9.)Vrom,)(4;.$4<.R1.R9.(4=.R9.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R:.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R9.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H2 H10 H11 H12 H14 H15.
    pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    destruct (Z.lt_ge_cases dAB dAE) as [Hlt|Hge].
    - (* [comment removed for export] *)
      assert (Hi : exists i : nat, (Z.of_nat i * 8 = dAE - dAB - 8)%Z).
      { unfold dAB, dAE in *.
        pose proof (Z.div_mod (B + 7) 8 ltac:(lia)). pose proof (Z.div_mod (B + N) 8 ltac:(lia)).
        pose proof (Z.mod_pos_bound (B + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (B + N) 8 ltac:(lia)).
        exists (Z.to_nat ((B + N) / 8 - (B + 7) / 8 - 1)). nia. }
      destruct Hi as (i & Hi).
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 92) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_ft C88 D_7aa7c ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
        destruct (w_loop i r1 ret dAB Hret R2 R10 R11 R12 R14 R15 ltac:(lia) ltac:(lia) Hi)
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 108) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C88 D_7aa7c ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post; apply regs_agree_refl.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & AG).
        destruct (tail_run r1 ret Hret R2 R10 R11 R12 R14) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hdisj Hz"] Lemma pro_loop : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pi,$39.Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)Pj,$2:.P,(48.R2.)P,(31.(1.&40.)(41.R4.(43.&5.+2.$44.))(33.Vsp,-10.))P,(31.(1.&40.)(41.R5.(43.&5.+:.$44.))Vbeg,)P,(31.(1.&40.)(41.R6.(43.&5.+;.$44.))(47.&40.=))P,(31.(1.&40.)(41.R7.(43.&5.+<.$44.))(33.Vbeg,$4?.))P,(31.(1.&40.)(41.R8.(43.&5.+=.$44.))(33.Vbeg,(2=.R6.+1.)))P,(31.(1.&40.)(41.R9.(43.&5.+>.$44.))(33.Vbeg,VN,))P,(31.(1.&40.)(41.R:.(43.&5.+?.$44.))(33.Vbeg,$51.))P,(2<.=R9.)P,(2?.R:.$51.)P,(2?.R;.VN,)P,(31.$2:.(3:.R?.)(34.(34.(52.$51.VN,)+1.)R<.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R10.(33.Vbase,+40.)(4=.R?.)Vrom,)(4;.$4<.R1.R?.(4=.R?.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$4>.)R10.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R?.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. pose proof (u64_range beg) as Hb. pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    induction i as [|i IH]; intros regs ret j Hret H2 H10 H11 H12 H13 H14 H15 Hj HjA HjN Hi.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (j + 1) dAB) as [HA|HA].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_7aa64.                      (* [comment removed for export] *)
             mlbu C68 D_7aa68.                    (* [comment removed for export] *)
             an C72 D_7aa6c.                      (* [comment removed for export] *)
             ab_tk C76 D_7aa70 ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- an C64 D_7aa64.                      (* [comment removed for export] *)
             mlbu C68 D_7aa68.                    (* [comment removed for export] *)
             an C72 D_7aa6c.                      (* [comment removed for export] *)
             ab_ft C76 D_7aa70 ltac:(condz).      (* [comment removed for export] *)
             an C80 D_7aa74.                      (* [comment removed for export] *)
             ab_ft C84 D_7aa78 ltac:(condz).      (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. solve_regs_agree.
        * cbv beta. intros r1 (R2 & R10 & R11 & R12 & R14 & R15 & AG).
          destruct (mid_run r1 ret Hret R2 R10 R11 R12 R14 R15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 13 = at_ beg (j + 1 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                         /\ regs_agree CL regs r)).
      + eexists. split.
        * an C64 D_7aa64.
          mlbu C68 D_7aa68.
          an C72 D_7aa6c.
          ab_ft C76 D_7aa70 ltac:(condz).         (* [comment removed for export] *)
          an C80 D_7aa74.
          ab_tk C84 D_7aa78 ltac:(condz).         (* [comment removed for export] *)
          apply mst_refl.
        * post. unfold memisz_clob'. solve_regs_agree.
      + cbv beta. intros r1 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG).
        destruct (IH r1 ret (j + 1)%Z Hret R2 R10 R11 R12 R13 R14 R15 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
          as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="HCODE HN Hnw Hsp Hstk Hdisj Hz"] Theorem mem_is_zero_run : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(48.R1.)P,(31.(1.&40.)(41.R3.(43.&5.+1.$44.))R2.)P,(31.(1.&40.)(41.R4.(43.&5.+2.$44.))Vsp,)P,(31.(1.&40.)(41.R5.(43.&5.+:.$44.))Vbeg,)P,(31.(1.&40.)(41.R6.(43.&5.+;.$44.))(47.&40.VN,))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.Vsegs,(4;.$4<.R8.(33.Vbase,=)Vmem,Vrom,)(4;.$4<.R1.R7.(4=.R7.)Vrom,))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$53.)R8.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))Vsp,)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R7.))))))")
(* [comment removed for export] *).
  Proof.
    get_code. intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range beg) as Hb. pose proof (u64_range sp) as Hs.
    pose proof dAE_range as HdAE. pose proof dAB_range as HdAB.
    (* [comment removed for export] *)
    eapply (runs_trans segs _ (fun r => mkst r (at_ base 48) (mem1 ret) rom)
             (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                       /\ getr r 13 = Z_to_bv 64 N /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                       /\ regs_agree CL regs r)).
    { eexists. split.
      - an C0 D_7aa24.                            (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_sd_at with (a := at_ sp (-8)) (v := ret);
            [exact C4 | reflexivity | exact D_7aa28
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; reflexivity
            | gres; rwH; reflexivity
            | exact Hstk]
          | step_simpl]; change (wbytes mem (at_ sp (-8)) (word_to_le_bytes 8 ret)) with (mem1 ret); vn.
                                                  (* [comment removed for export] *)
        an C8 D_7aa2c.                            (* [comment removed for export] *)
        an C12 D_7aa30.                           (* [comment removed for export] *)
        an C16 D_7aa34.                           (* [comment removed for export] *)
        an C20 D_7aa38.                           (* [comment removed for export] *)
        ab_ft C24 D_7aa3c ltac:(condz).           (* [comment removed for export] *)
        an C28 D_7aa40.                           (* [comment removed for export] *)
        av C32 D_7aa44 (at_ beg N) ltac:(apply v_add_at; lia).              (* [comment removed for export] *)
        an C36 D_7aa48.                           (* [comment removed for export] *)
        av C40 D_7aa4c (at_ beg dAB) ltac:(rewrite v_andi_m8 by lia; unfold dAB; f_equal; lia).  (* [comment removed for export] *)
        av C44 D_7aa50 (at_ beg dAE) ltac:(rewrite v_andi_m8 by lia; unfold dAE; reflexivity).    (* [comment removed for export] *)
        apply mst_refl.
      - post. unfold memisz_clob'. solve_regs_agree. }
    cbv beta. intros r0 (R2 & R10 & R11 & R12 & R13 & R14 & R15 & AG0).
    (* [comment removed for export] *)
    enough (G : exists regs',
      msteps segs (mkst r0 (at_ base 48) (mem1 ret) rom) (mkst regs' ret (mem1 ret) rom)
      /\ regs_agree CL regs regs' /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = sp /\ getr regs' 1 = ret).
    { destruct G as (r' & RUN & AG & P10 & P2 & P1). exists r'. split; [exact RUN|]. split; [|repeat split; assumption].
      apply (regs_agree_strengthen memisz_clob memisz_clob'); [exact AG|].
      intros r Hr Hnr. unfold memisz_clob', memisz_clob in *. cbn [In] in Hr.
      destruct Hr as [<-|[<-|Hr]]; [rewrite P1, H1; reflexivity | rewrite P2, H2; reflexivity |].
      exfalso. apply Hnr. cbn [In]. tauto. }
    destruct (Z.eq_dec dAB 0) as [HA0|HA0].
    - (* [comment removed for export] *)
      eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
               (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                         /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
      + eexists. split.
        * ab_tk C48 D_7aa54 ltac:(rewrite <- (at_0 beg) at 1; condz).   (* [comment removed for export] *)
          apply mst_refl.
        * post; exact AG0.
      + cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
        destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
        split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
    - destruct (Z.eq_dec N 0) as [HN0|HN0].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 88) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_7aa54 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_tk C52 D_7aa58 ltac:(condz).                              (* [comment removed for export] *)
             apply mst_refl.
          -- post; exact AG0.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S14 & S15 & AG).
          destruct (mid_run r1 ret Hret S2 S10 S11 S12 S14 S15) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
      + (* [comment removed for export] *)
        eapply (runs_trans segs _ (fun r => mkst r (at_ base 64) (mem1 ret) rom)
                 (fun r => getr r 2 = at_ sp (-16) /\ getr r 10 = beg /\ getr r 11 = Z0 /\ getr r 12 = at_ beg dAE
                           /\ getr r 13 = at_ beg (0 + 1) /\ getr r 14 = at_ beg N /\ getr r 15 = at_ beg dAB
                           /\ regs_agree CL regs r)).
        * eexists. split.
          -- ab_ft C48 D_7aa54 ltac:(rewrite <- (at_0 beg) at 1; condz).  (* [comment removed for export] *)
             ab_ft C52 D_7aa58 ltac:(condz).                              (* [comment removed for export] *)
             an C56 D_7aa5c.                                              (* [comment removed for export] *)
             an C60 D_7aa60.                                              (* [comment removed for export] *)
             apply mst_refl.
          -- post. unfold memisz_clob'. ra_chain.
        * cbv beta. intros r1 (S2 & S10 & S11 & S12 & S13 & S14 & S15 & AG).
          destruct (pro_loop (Z.to_nat (Z.min dAB N - 1)) r1 ret 0 Hret S2 S10 S11 S12 S13 S14 S15
                      ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2 & P). exists r2.
          split; [exact RUN | split; [eapply regs_agree_trans; eassumption | exact P]].
  Qed.
End MEMISZERO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma slot_at : forall sp : word, (16 <= bv_unsigned sp)%Z ->
  at_ sp (-8) = Z_to_bv 64 (bv_unsigned sp - 8).
Proof. intros sp Hsp. unfold at_. f_equal; lia. Qed.

Theorem mem_is_zero_summary : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Psegs,(36.$37.)Pbase,(1.&40.)Pmem,P,(1.&40.)(38.(1.&8.))Pbeg,(1.&40.)Psp,(1.&40.)PN,$2:.Prom,P,(1.&40.)(38.(1.&8.))Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(54.R9.R8.=$55.)P,(2;.(2<.=R5.)(2<.R5.(30.+2.+28.)))P,(2<.(2=.(2=.(2>.&40.R8.)R6.)+8.)(30.+2.+40.))P,(2<.+10.(2>.&40.R8.))P,(31.$56.(57.R=.R;.(47.&40.(34.(2>.&40.R9.)+8.))#8.)$58.)P,(59.(2<.(2=.(2>.&40.R;.)R9.)(34.(2>.&40.R:.)+8.))(2<.(2>.&40.R:.)(2>.&40.R;.)))P,Pa,(1.&40.)P,(2;.(2<.(2>.&40.R=.)(2>.&40.R1.))(2?.(2>.&40.R1.)(2=.(2>.&40.R=.)R;.)))(31.(38.(36.(1.&8.)))(3;.R11.R?.R2.#1.)(3<.(36.(1.&8.))(0.(1.&8.)(47.&8.=)(29.(1.&8.)))))P,(48.R8.)P,(31.(1.&40.)(41.R:.(43.&5.+1.$44.))R9.)P,(31.(1.&40.)(41.R;.(43.&5.+2.$44.))R>.)P,(31.(1.&40.)(41.R<.(43.&5.+:.$44.))R10.)P,(31.(1.&40.)(41.R=.(43.&5.+;.$44.))(47.&40.R?.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.R16.(4;.$4<.R?.R15.R14.R10.)(4;.$4<.R1.R>.(5:.R14.(47.&40.(34.(2>.&40.R12.)+8.))(5;.#8.R>.))R10.))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$53.)R?.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))R12.)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R>.))))))")
(* [comment removed for export] *).
Proof.
  intros segs base mem beg sp N rom regs ret HC HN Hnw Hsp Hstk Hdisj Hz.
  rewrite <- (slot_at sp Hsp) in Hstk |- *. rewrite <- (at_0 base).
  apply (mem_is_zero_run segs base mem beg sp N rom HC HN Hnw Hsp Hstk Hdisj Hz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.

(* [comment removed for export] *)
Definition asan_mem_is_zero_entry : word := 0x7af88.

Lemma asan_mem_is_zero_code :
  code_at AsanUbsan.M.loaded_segments asan_mem_is_zero_entry 0 memisz_words.
Proof. unfold memisz_words. code_at_vm. Qed.

Theorem asan_mem_is_zero : ltac2:(CDefT.buildp (gd_tbl_AsanMemIsZero ()) "Pmem,P,(1.&40.)(38.(1.&8.))Pbeg,(1.&40.)Psp,(1.&40.)PN,$2:.Prom,P,(1.&40.)(38.(1.&8.))Pregs,(3?.&5.(1.&40.))Pret,(1.&40.)P,(2;.(2<.=R4.)(2<.R4.(30.+2.+28.)))P,(2<.(2=.(2=.(2>.&40.R7.)R5.)+8.)(30.+2.+40.))P,(2<.+10.(2>.&40.R7.))P,(31.$56.(57.$5<.R:.(47.&40.(34.(2>.&40.R8.)+8.))#8.)$58.)P,(59.(2<.(2=.(2>.&40.R:.)R8.)(34.(2>.&40.R9.)+8.))(2<.(2>.&40.R9.)(2>.&40.R:.)))P,Pa,(1.&40.)P,(2;.(2<.(2>.&40.R<.)(2>.&40.R1.))(2?.(2>.&40.R1.)(2=.(2>.&40.R<.)R:.)))(31.(38.(36.(1.&8.)))(3;.$5<.R>.R2.#1.)(3<.(36.(1.&8.))(0.(1.&8.)(47.&8.=)(29.(1.&8.)))))P,(48.R7.)P,(31.(1.&40.)(41.R9.(43.&5.+1.$44.))R8.)P,(31.(1.&40.)(41.R:.(43.&5.+2.$44.))R=.)P,(31.(1.&40.)(41.R;.(43.&5.+:.$44.))R?.)P,(31.(1.&40.)(41.R<.(43.&5.+;.$44.))(47.&40.R>.))(49.(3?.&5.(1.&40.))Lregs',(3?.&5.(1.&40.))(2;.(4:.$5<.(4;.$4<.R>.$5=.R13.R?.)(4;.$4<.R1.R=.(5:.R13.(47.&40.(34.(2>.&40.R11.)+8.))(5;.#8.R=.))R?.))(2;.(40.Lr,(1.&5.)(46.(1.&5.)R1.$53.)R>.R1.)(2;.(31.(1.&40.)(41.R1.(43.&5.+:.$44.))(47.&40.+1.))(2;.(31.(1.&40.)(41.R1.(43.&5.+2.$44.))R11.)(31.(1.&40.)(41.R1.(43.&5.+1.$44.))R=.))))))")
(* [comment removed for export] *).
Proof.
  intros mem beg sp N rom regs ret.
  apply (mem_is_zero_summary _ _ mem beg sp N rom regs ret asan_mem_is_zero_code).
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
