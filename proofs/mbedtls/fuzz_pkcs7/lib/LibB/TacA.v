(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Export StepA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Export ARt.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_TacA () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.LibA.ALazy.asan_layout"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.acc_ok"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.write_to_mem"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_layout"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.zcells"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma acc_ok_shadow1C : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "PL,$0.PCS,P,$1.SpPE,$1.PA,$1.Pk,$1.Pc,$1.P,(2.R6.R5.)P,(3.R6.R4.R3.)P,(4.(5.R5.R3.)(6.R3.(7.R5.R4.)))P,(8.$1.R7.(9.R9.R4.))(:.R:.R9.(;.(<.(=.&40.)$>.)(?.(=.&40.)$>.(10.&40.R8.)#1.)(11.(<.(=.&40.)$>.))))")
(* [comment removed for export] *).
Proof.
  intros L CS E A k c OK H Hc HS.
  destruct OK as (C1 & _). destruct (C1 c (H c Hc)) as (R0 & R1 & R2 & _).
  eapply acc_ok_shadow1; [exact H| exact Hc|]. rewrite unsigned_lit by lia. exact HS.
Qed.

Lemma acc_ok_shadowC : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "PL,$0.PCS,P,$1.SpPE,$1.Pn,$>.PA,$1.Pk,$1.Pc,$1.P,(2.R7.R6.)P,(3.R7.R4.R3.)P,(5.R5.R3.)P,(6.(7.R4.(12.+8.(13.(14.R7.)+1.)))(7.R6.R5.))P,(8.$1.(15.R5.+8.)=)P,(16.#1.R9.)P,(8.$1.R;.(9.R=.R7.))(:.R>.R=.(;.(<.(=.&40.)$>.)(?.(=.&40.)$>.(10.&40.R<.)R;.)(11.(<.(=.&40.)$>.))))")
(* [comment removed for export] *).
Proof.
  intros L CS E n A k c OK H H1 H2 Hal Hn HS.
  destruct OK as (C1 & _). destruct (C1 c (H c ltac:(lia))) as (R0 & R1 & R2 & _).
  eapply acc_ok_shadow; [exact H| exact H1| exact H2| exact Hal|]. rewrite unsigned_lit by lia. exact HS.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac merge_cut_aevtA segs P ::=
  lazymatch goal with
  | |- aevtA _ (HK _ ?R ?HIA ?h) _ _ => eapply (aevtA_cut_evtA_HK segs R HIA h P)
  | |- aevtA _ (KF _ ?R ?HIA ?h ?mo0) _ _ => eapply (aevtA_cut_evtA_KF segs R HIA h mo0 P)
  end.

(* [comment removed for export] *)
Ltac apply_step_lemmaA ::=
  lazymatch goal with
  | |- evtA _ _ _ _ _ => eapply evtA_step
  | |- aevtA _ (HK _ _ _ _) _ _ => eapply aevtA_step_HK
  | |- aevtA _ (KF _ _ _ _ _) _ _ => eapply aevtA_step_KF
  | |- aevtA _ _ _ _ => eapply aevtA_step; [ eassumption | eassumption | | | ]
  | |- ?g => fail "apply_step_lemmaA: goal is neither evtA nor aevtA"
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bytes_at_write_other0 : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "Psegs,(17.$18.)Pm,P,(=.&40.)(19.(=.&8.))Pa,$1.Pbs,(17.(=.&8.))Pc,$1.Pcs,(17.(=.&8.))P,(1:.R6.R5.R2.R1.)P,(5.=R5.)P,(5.(7.R6.(14.(1;.(=.&8.)R5.)))(1<.+2.+40.))P,(1=.(8.$1.(14.(1;.(=.&8.)R4.))=)(1=.(5.(7.R5.(14.(1;.(=.&8.)R4.)))R7.)(5.(7.R7.(14.(1;.(=.&8.)R6.)))R5.)))(1:.R:.(1>.R9.(1?.R8.)R7.)R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros segs m a bs c cs H Ha Hl [E|D].
  - destruct cs; [| cbn in E; lia]. destruct H as (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi; cbn in Hi; lia.
  - apply bytes_at_write_other; assumption.
Qed.

Ltac is_shadow_addr E := let c := shadow_client_of E in idtac.

(* [comment removed for export] *)
Ltac store_is_shadow a := lazymatch a with context [Z.shiftr _ 3] => idtac end.
Ltac base_is_shadow A := lazymatch A with context [Z.shiftr _ 3] => idtac end.

(* [comment removed for export] *)
Ltac apart_cs A2 n2 a len :=
  let c := shadow_client_of a in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_client_shadow L CS A2 n2 c a len OK); [ solve_crange | solve_crange | shadow_addr_eq | qlia | qlia ]
  end.
(* [comment removed for export] *)
Ltac apart_sc A2 n2 a len :=
  let c := shadow_client_of A2 in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_shadow_client L CS a len c A2 n2 OK); [ solve_crange | solve_crange | shadow_addr_eq | qlia | qlia ]
  end.
(* [comment removed for export] *)
Ltac apart_ss A2 n2 a len :=
  let c1 := shadow_client_of a in let c2 := shadow_client_of A2 in
  apply (apart_shadow_shadow _ c2 n2 c1 len A2 a); [ qlia | qlia | pqlia | shadow_addr_eq | shadow_addr_eq ].

(* [comment removed for export] *)
Ltac keep_disj1 D := repeat match goal with H : _ \/ _ |- _ => lazymatch H with D => fail | _ => clear H end end.
Ltac lia1 D := keep_disj1 D; clear_mods; lia.
Ltac mentions T x := lazymatch T with context [x] => idtac end.
(* [comment removed for export] *)
Ltac lia_2bases b1 b2 :=
  match goal with
  | D : ?X \/ ?Y |- _ => mentions (X \/ Y) b1; mentions (X \/ Y) b2; solve [ lia1 D ]
  end.
(* [comment removed for export] *)
Ltac apart_cc A2 n2 a len :=
  first [ assumption
        | solve [ clear; lia ]
        | let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2
        | pqlia ].

(* [comment removed for export] *)
Ltac solve_apart :=
  lazymatch goal with
  | |- ?A2 + ?n2 <= ?a \/ ?a + ?len <= ?A2 =>
      tryif store_is_shadow a
      then (tryif base_is_shadow A2 then apart_ss A2 n2 a len else apart_cs A2 n2 a len)
      else (tryif base_is_shadow A2 then apart_sc A2 n2 a len else apart_cc A2 n2 a len)
  end.
(* [comment removed for export] *)
Ltac solve_apart0 :=
  lazymatch goal with
  | |- ?n = 0 \/ ?A2 + _ <= ?a \/ _ =>
      first [ assumption
            | (tryif store_is_shadow a then fail else (tryif base_is_shadow A2 then fail else
                 first [ solve [ clear; lia ]
                       | let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2
                       | lazymatch n with context [length ?cs] => let b2 := base_of a in lia_2bases (length cs) b2 end
                       | pqlia ]))
            | right; solve_apart
            | (* [comment removed for export] *)
              lazymatch n with
              | context [length ?cs] => destruct cs; [ left; reflexivity | right; cbn [length] in *; solve_apart ]
              end ]
  | |- _ => solve_apart
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac norm_hst :=
  repeat match goal with
  | E : htop _ _ _ _ = htop _ _ _ _ |- _ => progress rewrite E
  | E : hstkhi _ _ _ _ = hstkhi _ _ _ _ |- _ => progress rewrite E
  | E : hcs _ _ _ _ = _ |- _ => progress rewrite E
  end.

Ltac solve_hm_shadow_range_core Hx :=
  first [ match goal with H : forall y, _ -> (_ <= y < _) \/ in_block _ y |- _ => apply H; clear - Hx; lia end
        | left; clear_disj; lia
        | right; match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; clear_disj; lia] end ].
Ltac solve_hm_shadow_range :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx;
  first [ solve_hm_shadow_range_core Hx | progress norm_hst; solve_hm_shadow_range_core Hx ].

(* [comment removed for export] *)
Ltac simpl_sizes_in H :=
  rewrite ?app_length in H; bn_sizes_in H;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H;
  rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1 in H.
Ltac sf_a0 ::= first [ assumption | qlia ].
Ltac sf_al ::= first [ assumption | simpl_sizes; first [ assumption | qlia ] ].

(* [comment removed for export] *)
Ltac store_bounds Ha Hl CR a bs :=
  tryif store_is_shadow a
  then (let c := shadow_client_of a in
        match goal with
        | OK : cs_ok ?L ?CS |- _ =>
            let Hb := fresh "Hb" in
            try (assert (CR : crange CS c (8 * Z.of_nat (length bs))) by (simpl_sizes; cbn [Z.mul Pos.mul]; solve_crange); simpl_sizes_in CR; cbn [Z.mul Pos.mul] in CR);
            pose proof (shadow_store_bounds L CS c (length bs) a OK) as Hb;
            simpl_sizes_in Hb; cbn [Z.mul Pos.mul] in Hb;
            destruct (Hb ltac:(solve_crange) ltac:(cbn; clear; lia) ltac:(shadow_addr_eq)) as [Ha Hl]; clear Hb
        end)
  else (try (assert (Ha : (0 <= a)%Z) by qlia);
        try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; first [assumption | qlia]));
        try match goal with
            | OK : cs_ok ?L ?CS |- _ => assert (CR : crange CS a (Z.of_nat (length bs))) by (simpl_sizes; solve_crange); simpl_sizes_in CR
            end).

Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | sf_a0 | sf_al | cbn [inside]; simpl_sizes; first [ qlia | slia ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | sf_a0 | sf_al ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in let CR := fresh "CRst" in
  try store_bounds Ha Hl CR a bs;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other0 segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart0 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | qlia | simpl_sizes; qlia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | qlia | simpl_sizes; qlia | simpl_sizes; pqlia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  (* [comment removed for export] *)
  | H : HM segs ?R ?HIA ?h ?LB ?LF m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (hm_write_shadow segs R HIA h LB LF m c a bs) in H;
                    [ | simpl_sizes; solve_hm_shadow_range | shadow_addr_eq | sf_a0 | sf_al ])
              else (apply (hm_write segs R HIA h LB LF m a bs) in H; [ | simpl_sizes; solve_client_wrange | sf_a0 | sf_al ])
            | idtac "note: could not carry HM across the store (dropping):" H; clear H ]
  | H : presW segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    first [ match goal with SF : shadow_free _ LB LF SSP _ ?C ?n |- _ =>
                              apply (presW_store_shadow_cov segs R HIA h LB LF SP SSP W m0 m c a bs C n) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact SF | qlia | simpl_sizes; qlia ] end
                          | apply (presW_store_shadow_stack segs R HIA h LB LF SP SSP W m0 m c a bs) in H;
                            [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | qlia | simpl_sizes; qlia ]
                          | match goal with FR : fresh_apart _ LB LF ?N ?k, AP : forall B j, In (B, j) LF -> _ |- _ =>
                              apply (presW_store_shadow_fresh segs R HIA h LB LF SP SSP W m0 m c a bs N k) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact FR | exact AP | qlia | simpl_sizes; qlia | qlia ] end ])
              else first [ match goal with WC : wcover _ LB LF SP W ?A ?n |- _ =>
                             apply (presW_store_cov segs R HIA h LB LF SP SSP W m0 m a bs A n) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact WC | qlia | simpl_sizes; qlia ] end
                         | apply (presW_store_out segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | cbn [inside]; simpl_sizes; qlia ]
                         | apply (presW_store_stack segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | qlia | simpl_sizes; qlia ]
                         | match goal with FR : fresh_apart _ LB LF ?N ?k |- _ =>
                             apply (presW_store_fresh segs R HIA h LB LF SP SSP W m0 m a bs N k) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact FR | qlia | simpl_sizes; qlia | qlia ] end ]
            | idtac "note: could not carry presW across the store (dropping):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (abase_shadow_store_at segs L CS m c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | shadow_addr_eq ])
              else (apply (abase_frame segs L CS OK m a bs) in H; [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | sf_a0 | sf_al ])
            | idtac "note: could not carry abase across the store (dropping):" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (aobj_shadow_store_at segs L CS m A n c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (aobj_frame segs L CS OK m A n a bs) in H; [ | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry aobj across the store (dropping):" H; clear H ]
  | H : sshad segs ?L m ?lo ?hi, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (sshad_shadow_store_at segs L CS m lo hi c a bs OK) in H;
                    [ | solve_crange | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (sshad_frame segs L CS m lo hi a bs OK) in H; [ | solve_crange | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry sshad across the store (dropping):" H; clear H ]
  end;
  try clear Ha; try clear Hl; try clear CR.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma land_align_down : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
  Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
  intros x j Hx Hj.
  replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
  2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
      unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
      replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
      replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
      rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
  rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
  rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

Lemma land_m32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x - x mod 32.
Proof. intros. change 18446744073709551584 with (2^64 - 2^5). rewrite land_align_down by lia. reflexivity. Qed.
Lemma land_m16 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551600 = x - x mod 16.
Proof. intros. change 18446744073709551600 with (2^64 - 2^4). rewrite land_align_down by lia. reflexivity. Qed.

(* [comment removed for export] *)
Ltac align32 e v :=
  let H := fresh "H" v in
  rewrite (land_m32 e) in * by lia;
  remember (e - e mod 32) as v eqn:H in *.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_cshd_range :=
  let c := fresh "c" in let Hc := fresh "Hc" in
  intros c Hc; cbn;
  first [ left; split; qlia
        | right; right; left;
          match goal with HIn : In (?FB, ?n) ?LF |- in_block ?LF _ => exists (FB, n); split; [exact HIn| cbn; qlia] end
        | right; left;
          match goal with HIn : In (?A, ?n) ?LB |- in_block ?LB _ => exists (A, n); split; [exact HIn| cbn; qlia] end ].

(* [comment removed for export] *)
Ltac solve_cs_top := first [ assumption | (intros ?x ?Hx; eapply hcs_below_top; exact Hx) ].

(* [comment removed for export] *)
Ltac solve_incl :=
  let b := fresh "b" in let Hb := fresh "Hb" in
  intros b Hb; first [ exact Hb | right; exact Hb | right; right; exact Hb | apply fdata_cons_sub; exact Hb
                     | apply fdata_cons_sub; right; exact Hb ].   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac solve_outside_incl :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; first [ exact I | exact Hx | cbn [outside] in Hx |- *; clear - Hx; lia ].

(* [comment removed for export] *)
Ltac solve_wcover :=
  lazymatch goal with
  | |- wcover ?L ?LB ?LF ?SP ?W ?a ?n =>
      first [ match goal with WC : wcover L LB LF SP W ?A ?k |- _ => apply (wcover_sub L LB LF SP W A k a n WC); [ qlia | qlia ] end
            | apply wcover_inside; cbn [inside]; qlia
            | match goal with WL : wlow _ LB LF |- _ => apply (wcover_of_wlow _ LB LF SP W a n WL); [ qlia | qlia ] end
            | match goal with FR : fresh_apart _ LB LF ?N ?k |- _ => apply (wcover_fresh _ LB LF SP W a n N k FR); [ qlia | qlia | qlia ] end
            | apply wcover_nil; qlia ]
  end.
Ltac solve_wcover_list :=
  repeat (apply Forall_cons; [ cbn [fst snd]; solve_wcover | ]); apply Forall_nil.

Ltac presA_transport HP :=
  lazymatch type of HP with
  | presW ?segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m ?m' =>
      let HP' := fresh "HPA" in pose proof (presW_presA segs R HIA h LB LF SP SSP W m m' HP) as HP'; presA_transport HP'; clear HP'
  | presA ?segs ?R ?LB ?LF ?SP ?SSP ?TOP ?W ?m ?m' =>
    repeat match goal with
    | H : presW segs R ?HIA ?h ?LB0 ?LF0 ?SP0 ?SSP0 ?W0 ?m0 m |- _ =>
        first [ apply (presW_call segs R HIA h LB0 LF0 SP0 SSP0 W0 m0 m m' LB LF SP SSP TOP W) in H;
                [ | exact HP | solve_incl | solve_incl | qlia | qlia | qlia | solve_outside_incl ]
              | idtac "note: could not compose presW with the callee's presA (dropping):" H; clear H ]
    | H : rw_cells segs m (Z.shiftr ?B 3 + al_sb ?AL) ?cs, OK : cs_ok ?AL ?CS |- _ =>
        first [ apply (presA_shadow_cells_sh segs R CS LB LF SP SSP TOP W m m' B cs OK) in H;
                [ | simpl_sizes; solve_crange | qlia | qlia | exact HP | simpl_sizes; solve_cshd_range ]
              | idtac "note: dropping shadow chunk across call:" H; clear H ]
    | H : rw_cells segs m ?A ?cs |- _ =>
        first [ apply (presA_rw_cells segs R LB LF SP SSP TOP W m m' A cs HP) in H;
                [ | simpl_sizes; solve_client_range | cbn [disjoint_from]; simpl_sizes; qlia ]
              | idtac "note: dropping (not client memory / inside footprint) across call:" H; clear H ]
    | H : ro_cells segs m ?A ?cs |- _ =>
        first [ apply (presA_ro_cells segs R LB LF SP SSP TOP W m m' A cs HP) in H;
                [ | simpl_sizes; solve_client_range | cbn [disjoint_from]; simpl_sizes; qlia ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : bytes_at segs m ?A ?bs |- _ =>
        first [ apply (presA_bytes_at0 segs R LB LF SP SSP TOP W m m' A bs HP) in H;
                [ | first [ right; split; [ simpl_sizes; solve_client_range | cbn [disjoint_from]; simpl_sizes; qlia ]
                          | destruct bs; [ left; reflexivity
                                         | right; cbn [length] in *; split; [ solve_client_range | cbn [disjoint_from]; qlia ] ] ] ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : u8arr segs m ?A ?xs |- _ =>
        first [ apply (presA_u8arr segs R LB LF SP SSP TOP W m m' A xs HP) in H;
                [ | simpl_sizes; solve_client_range | cbn [disjoint_from]; simpl_sizes; qlia ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : stk segs m ?lo ?hi |- _ =>
        first [ apply (presA_stk segs R LB LF SP SSP TOP W m m' lo hi HP) in H; [ | qlia | cbn [disjoint_from]; qlia ]
              | idtac "note: dropping stk across call:" H; clear H ]
    | H : aobj segs ?AL ?CS m ?A ?n, OK : cs_ok ?AL ?CS |- _ =>
        first [ apply (presA_aobj0 segs R CS LB LF SP SSP TOP W m m' A n OK HP) in H;
                [ | solve_cs_top
                  | first [ right; split; [ solve_client_range | qlia ]
                          | lazymatch n with
                            | Z.of_nat (length ?bs) =>
                                destruct bs; [ left; cbn; lia | right; cbn [length] in *; split; [ solve_client_range | qlia ] ]
                            end ] ]
              | idtac "note: dropping aobj across call:" H; clear H ]
    | H : sshad segs ?AL m ?lo ?hi |- _ =>
        first [ apply (presA_sshad segs R LB LF SP SSP TOP W m m' lo hi HP) in H; [ | qlia | qlia ]
              | idtac "note: dropping sshad across call:" H; clear H ]
    | H : abase segs _ m |- _ => clear H
    | H : auar segs _ _ m |- _ => clear H
    | H : wr_at segs m _ _ |- _ => clear H
    | H : mem_inv segs m |- _ => clear H
    end
  end.

(* [comment removed for export] *)
Ltac post_rt :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO; cbv beta in PO;
  destruct_exs PO;
  let E := fresh "E" in destruct PO as [E PO]; subst ms';
  try destruct_ands PO;
  try (lazymatch goal with
  | |- _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ])
  end).

(* [comment removed for export] *)
Tactic Notation "callrt" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- evtA ?segs _ _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evtA_cut; [ apptac | unfold call_postA; rewrite ?(unsigned_lit e) by qlia; post_rt ]
  end.

(* [comment removed for export] *)
Lemma stk_slot : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "Psegs,(17.$18.)Pm,P,(=.&40.)(19.(=.&8.))Plo,$1.Phi,$1.Pa,$1.Pn,$>.P,(20.R6.R5.R4.R3.)P,(5.R5.R3.)P,(5.(7.R4.(14.R3.))R5.)(21.(17.(=.&8.))Ljunk,(17.(=.&8.))(22.R:.R9.R6.(;.$23.(24.R5.R1.)(11.$23.))))")
(* [comment removed for export] *).
Proof.
  intros segs m lo hi a n ST H1 H2.
  destruct (stk_split segs m lo (a + Z.of_nat n) hi ST ltac:(lia)) as [ST1 _].
  destruct (stk_carve segs m lo (a + Z.of_nat n) n ST1 ltac:(lia)) as [_ [junk FR]].
  exists junk. replace (a + Z.of_nat n - Z.of_nat n) with a in FR by lia. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma client_wrange_sp_mono : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "PL,$25.PLB,(17.$26.)PSP,$1.PSP',$1.PTOP,$1.PA,$1.Pn,$1.P,(5.R4.R5.)P,(27.R8.R7.R6.R4.R3.R2.)(27.R9.R8.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros L LB SP SP' TOP A n HS H a Ha. destruct (H a Ha) as [X|[X|X]]; [left; lia| right; left; exact X| right; right; exact X].
Qed.
Lemma client_range_sp_mono : forall L LB SP SP' A n,
  SP' <= SP -> client_range L LB SP A n -> client_range L LB SP' A n.
Proof.
  intros L LB SP SP' A n HS H a Ha. destruct (H a Ha) as [X|[X|X]]; [left; lia| right; left; exact X| right; right; exact X].
Qed.

(* [comment removed for export] *)
Ltac solve_sub ::=
  first [ assumption
        | (intros ? Hb; exact Hb)
        | (intros ? Hb; apply fdata_cons_sub; exact Hb)
        | (intros ? Hb; solve [ auto 6 using in_cons, in_or_app with nocore ])
        | (intros ? Hb; apply in_or_app; right; solve [ exact Hb | apply in_or_app; right; exact Hb ])
        | (intros ? Hb; right; solve [ exact Hb | apply in_or_app; right; exact Hb ]) ].

Ltac solve_w_nonempty ::= repeat (apply Forall_cons; [ cbn [fst snd]; qlia | ]); apply Forall_nil.

Ltac solve_client_wrange_core :=
  first [ apply client_wrange_stack; [dlia | dlia]
        | match goal with H : In (?B, ?j) ?LBx |- client_wrange ?L ?LBx ?SP ?TOP ?a ?k =>
            apply (client_wrange_block L LBx SP TOP a k B j H); dlia end
        | eapply client_wrange_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange ?L ?LB0 ?SP ?TOP ?A ?n |- client_wrange _ _ _ _ ?a ?k =>
            eapply (client_wrange_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ] end
        | match goal with H : client_wrange ?L ?LB0 ?SP0 ?TOP ?A ?n |- client_wrange _ _ ?SP _ ?a ?k =>
            eapply (client_wrange_inside L LB0 _ SP TOP A n a k (client_wrange_sp_mono L LB0 SP0 SP TOP A n ltac:(dlia) H));
            [ solve_sub | dlia | dlia ] end ].
Ltac solve_client_wrange ::= first [ solve_client_wrange_core | progress norm_hst; solve_client_wrange_core ].

Ltac solve_client_range ::=
  first [ apply client_range_stack; dlia
        | match goal with H : In (?B, ?j) ?LBx |- client_range ?L ?LBx ?SP ?a ?k =>
            apply (client_range_block L LBx SP a k B j H); dlia end
        | eapply client_range_block; [ eassumption | dlia | dlia ]
        | eapply client_range_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange ?L ?LB0 ?SP ?TOP ?A ?n |- client_range _ _ _ ?a ?k =>
            first [ eapply (client_range_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ]
                  | eapply (client_range_wsep L LB0 _ SP TOP _ A n H); [ solve_sub | pqlia ] ] end
        | match goal with H : client_range ?L ?LB0 ?lo ?A ?n |- client_range _ _ _ ?A ?n =>
            eapply (client_range_sep L LB0 _ lo _ A n H); [ solve_sub | pqlia ] end
        | match goal with H : client_range ?L ?LB0 ?lo ?A ?n |- client_range _ _ ?SP ?a ?k =>
            eapply (client_range_sep L LB0 _ lo SP a k); [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply H; dlia | solve_sub | pqlia ] end ].

Ltac solve_w_writable :=
  repeat (apply Forall_cons; [ cbn [fst snd]; apply w_writable_of_client_wrange; solve_client_wrange | ]); apply Forall_nil.

(* [comment removed for export] *)
Ltac transport_after_callA segs m m' MU ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  let WM := lazymatch goal with WM : wmono segs m m' |- _ => WM end in
  repeat match goal with
  | H : rw_cells segs m (Z.shiftr ?B 3 + al_sb ?L) ?cs, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (shadow_cells_munch segs L CS W m m' B cs OK) in H;
              [ | solve_w_client | solve_w_nonempty | simpl_sizes; solve_crange | qlia | cbn; clear; lia | exact MU | exact WM ]
            | idtac "note: dropping shadow chunk across call:" H; clear H ]
  | H : sshad segs ?L m ?lo ?hi, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (sshad_munch segs L CS W m m' lo hi OK) in H; [ | solve_w_client | solve_crange | exact MU | exact WM ]
            | idtac "note: dropping sshad across call:" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (aobj_munch segs L CS OK W m m' A n) in H; [ | solve_w_client | exact MU ]
            | idtac "note: dropping aobj (callee footprint not provably client):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ apply (abase_munch segs L CS OK W m m') in H; [ | solve_w_client | solve_w_nonempty | exact MU ]
            | idtac "note: dropping abase across call:" H; clear H ]
  | H : HM segs ?R ?HIA ?h ?LB ?LF m |- _ =>
      (* [comment removed for export] *)
      first [ apply (hm_munch segs R HIA h LB LF W m m') in H; [ | exact MU | exact WM | solve_w_writable ]
            | idtac "note: dropping HM across call:" H; clear H ]
  | H : presW segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W0 ?m0 m |- _ =>
      first [ apply (presW_munch segs R HIA h LB LF SP SSP W0 m0 m m' W) in H; [ | exact MU | exact WM | solve_w_client | solve_wcover_list ]
            | idtac "note: dropping presW across call:" H; clear H ]
  end.

(* [comment removed for export] *)
Tactic Notation "callxA_sp" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- evtA ?segs _ _ _ (MS _ _ _ _ _ ?m _) =>
      eapply evtA_cut;
      [ apptac
      | lazymatch goal with |- forall x, ?P x -> _ => let h := head_of P in try unfold h end;
        rewrite ?(unsigned_lit e) by qlia; post_callA segs m ]
  end.

(* [comment removed for export] *)
Tactic Notation "frame_aobj" constr(FSH) constr(A) constr(n) "as" ident(H) :=
  lazymatch type of FSH with
  | rw_cells ?segs ?m (Z.shiftr ?FB 3 + al_sb ?L) ?cs =>
      match goal with
      | OK : cs_ok L ?CS |- _ =>
          let d := addr_diff A FB in
          let g0 := eval vm_compute in (Z.to_nat (d / 8)) in
          pose proof (aobj_of_zero_shadow_sh segs L CS m FB cs A g0 n OK FSH
                        ltac:(solve_crange) ltac:(qlia) ltac:(qlia) ltac:(lia)
                        ltac:(let i := fresh "i" in let Hi := fresh "Hi" in
                              intros i Hi;
                              do 8 (destruct i as [|i]; [reflexivity| try (exfalso; clear - Hi; lia)]);
                              exfalso; clear - Hi; lia)) as H;
          let z := eval vm_compute in (8 * Z.of_nat n)%Z in change (8 * Z.of_nat n)%Z with z in H
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma bytes_at_transport0 : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "Psegs,(17.$18.)PW,(17.$28.)Pm,P,(=.&40.)(19.(=.&8.))Pm',P,(=.&40.)(19.(=.&8.))PA,$1.Pbs,(17.(=.&8.))P,(1:.R6.R4.R2.R1.)P,(29.R6.R5.R4.)P,(1=.(8.$>.(1;.(=.&8.)R3.)#0.)(2:.R7.R4.(14.(1;.(=.&8.)R3.))))(1:.R9.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros segs W m m' A bs H MU [E|D].
  - destruct bs; [| cbn in E; lia]. destruct H as (H0 & H1 & _). split; [exact H0|]. split; [exact H1|]. intros i Hi; cbn in Hi; lia.
  - eapply bytes_at_transport; eauto.
Qed.

(* [comment removed for export] *)
Ltac solve_disjoint := cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; repeat split; pqlia.

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport0 segs W m m' A2 bs2) in H;
              [ | exact MU
                | first [ right; solve_disjoint
                        | destruct bs2; [ left; reflexivity | right; cbn [length] in *; solve_disjoint ] ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | cbn [disjoint_from]; repeat split; qlia ]
            | clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; pqlia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac store_bounds Ha Hl CR a bs ::=
  tryif store_is_shadow a
  then (let c := shadow_client_of a in
        match goal with
        | OK : cs_ok ?L ?CS |- _ =>
            let Hb := fresh "Hb" in
            try (assert (CR : crange CS c (8 * Z.of_nat (length bs))) by (simpl_sizes; cbn [Z.mul Pos.mul]; solve_crange); simpl_sizes_in CR; cbn [Z.mul Pos.mul] in CR);
            pose proof (shadow_store_bounds L CS c (length bs) a OK) as Hb;
            simpl_sizes_in Hb; cbn [Z.mul Pos.mul] in Hb;
            destruct (Hb ltac:(solve_crange) ltac:(cbn; clear; lia) ltac:(shadow_addr_eq)) as [Ha Hl]; clear Hb
        end)
  else (try (assert (Ha : (0 <= a)%Z) by qlia);
        try (assert (Hl : (a + Z.of_nat (length bs) <= 2^64)%Z) by (simpl_sizes; first [assumption | qlia]));
        try match goal with
            | OK : cs_ok ?L ?CS |- _ => assert (CR : crange CS a (Z.of_nat (length bs))) by (simpl_sizes; solve_crange); simpl_sizes_in CR
            end).

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac note_crange CS A n :=
  first [ lazymatch goal with _ : crange CS A n |- _ => idtac end
        | let H := fresh "CRG" in
          assert (H : crange CS A n) by solve_crange ].
Ltac chunk_sizeZ cs := eval cbv in (Z.of_nat (cells_size cs)).
Ltac note_chunk_cranges segs m :=
  lazymatch goal with
  | OK : cs_ok ?L ?CS |- _ =>
      repeat match goal with
      | H : rw_cells segs m ?A ?cs |- _ =>
          tryif base_is_shadow A then fail else
          (let n := chunk_sizeZ cs in
           lazymatch goal with
           | _ : crange CS A n |- _ => fail
           | _ => let G := fresh "CRG" in assert (G : crange CS A n) by solve_crange
           end)
      | H : ro_cells segs m ?A ?cs |- _ =>
          (let n := chunk_sizeZ cs in
           lazymatch goal with
           | _ : crange CS A n |- _ => fail
           | _ => let G := fresh "CRG" in assert (G : crange CS A n) by solve_crange
           end)
      end
  | _ => idtac
  end.

Ltac apart_cs A2 n2 a len ::=
  let c := shadow_client_of a in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_client_shadow L CS A2 n2 c a len OK); [ solve_crange | solve_crange | shadow_addr_eq | clear; lia | clear; lia ]
  end.
Ltac apart_sc A2 n2 a len ::=
  let c := shadow_client_of A2 in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_shadow_client L CS a len c A2 n2 OK); [ solve_crange | solve_crange | shadow_addr_eq | clear; lia | clear; lia ]
  end.

(* [comment removed for export] *)
Ltac footprint_work segs m a bs :=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | sf_a0 | sf_al | cbn [inside]; simpl_sizes; first [ qlia | slia ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | sf_a0 | sf_al ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.
Ltac footprint_after_store segs m a bs ::= idtac.

Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in let CR := fresh "CRst" in
  try store_bounds Ha Hl CR a bs;
  (tryif store_is_shadow a then note_chunk_cranges segs m else idtac);
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other0 segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart0 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | qlia | simpl_sizes; qlia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | qlia | simpl_sizes; qlia | simpl_sizes; pqlia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  (* [comment removed for export] *)
  | H : HM segs ?R ?HIA ?h ?LB ?LF m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (hm_write_shadow segs R HIA h LB LF m c a bs) in H;
                    [ | simpl_sizes; solve_hm_shadow_range | shadow_addr_eq | sf_a0 | sf_al ])
              else (apply (hm_write segs R HIA h LB LF m a bs) in H; [ | simpl_sizes; solve_client_wrange | sf_a0 | sf_al ])
            | idtac "note: could not carry HM across the store (dropping):" H; clear H ]
  | H : presW segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    first [ match goal with SF : shadow_free _ LB LF SSP _ ?C ?n |- _ =>
                              apply (presW_store_shadow_cov segs R HIA h LB LF SP SSP W m0 m c a bs C n) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact SF | qlia | simpl_sizes; qlia ] end
                          | apply (presW_store_shadow_stack segs R HIA h LB LF SP SSP W m0 m c a bs) in H;
                            [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | qlia | simpl_sizes; qlia ]
                          | match goal with FR : fresh_apart _ LB LF ?N ?k, AP : forall B j, In (B, j) LF -> _ |- _ =>
                              apply (presW_store_shadow_fresh segs R HIA h LB LF SP SSP W m0 m c a bs N k) in H;
                              [ | qlia | shadow_addr_eq | qlia | simpl_sizes; solve_crange | exact FR | exact AP | qlia | simpl_sizes; qlia | qlia ] end ])
              else first [ match goal with WC : wcover _ LB LF SP W ?A ?n |- _ =>
                             apply (presW_store_cov segs R HIA h LB LF SP SSP W m0 m a bs A n) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact WC | qlia | simpl_sizes; qlia ] end
                         | apply (presW_store_out segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | cbn [inside]; simpl_sizes; qlia ]
                         | apply (presW_store_stack segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | qlia | simpl_sizes; qlia ]
                         | match goal with FR : fresh_apart _ LB LF ?N ?k |- _ =>
                             apply (presW_store_fresh segs R HIA h LB LF SP SSP W m0 m a bs N k) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact FR | qlia | simpl_sizes; qlia | qlia ] end ]
            | idtac "note: could not carry presW across the store (dropping):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (abase_shadow_store_at segs L CS m c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | shadow_addr_eq ])
              else (apply (abase_frame segs L CS OK m a bs) in H; [ | simpl_sizes; solve_crange | simpl_sizes; clear; lia | sf_a0 | sf_al ])
            | idtac "note: could not carry abase across the store (dropping):" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (aobj_shadow_store_at segs L CS m A n c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (aobj_frame segs L CS OK m A n a bs) in H; [ | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry aobj across the store (dropping):" H; clear H ]
  | H : sshad segs ?L m ?lo ?hi, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (sshad_shadow_store_at segs L CS m lo hi c a bs OK) in H;
                    [ | solve_crange | simpl_sizes; solve_crange | qlia | simpl_sizes; clear; lia | simpl_sizes; pqlia | shadow_addr_eq ])
              else (apply (sshad_frame segs L CS m lo hi a bs OK) in H; [ | solve_crange | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry sshad across the store (dropping):" H; clear H ]
  end;
  footprint_work segs m a bs;
  try clear Ha; try clear Hl; try clear CR.


(* [comment removed for export] *)
Ltac cw_by_inside H :=
  lazymatch goal with |- client_wrange ?L ?LBF ?SP ?TOP ?a ?k =>
  lazymatch type of H with client_wrange _ ?LB0 ?SP0 _ ?A ?n =>
    first [ eapply (client_wrange_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ]
          | eapply (client_wrange_inside L LB0 _ SP TOP A n a k (client_wrange_sp_mono L LB0 SP0 SP TOP A n ltac:(dlia) H)); [ solve_sub | dlia | dlia ] ]
  end end.
Ltac cr_by_inside H :=
  lazymatch goal with |- client_range ?L ?LBF ?SP ?a ?k =>
  lazymatch type of H with
  | client_wrange _ ?LB0 ?SP0 ?TOP ?A ?n =>
    first [ eapply (client_range_inside L LB0 _ SP TOP A n a k H); [ solve_sub | dlia | dlia ]
          | eapply (client_range_wsep L LB0 _ SP0 TOP _ A n H); [ solve_sub | pqlia ] ]
  | client_range _ ?LB0 ?lo ?A ?n =>
    first [ eapply (client_range_sep L LB0 _ lo SP a k); [ let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; apply H; dlia | solve_sub | pqlia ] ]
  end end.

Ltac solve_client_wrange_core ::=
  lazymatch goal with |- client_wrange ?L ?LBF ?SP ?TOP ?a ?k =>
  let b := base_of a in
  first [ match goal with
          | H : client_wrange L _ _ _ b _ |- _ => cw_by_inside H
          | H : client_wrange L _ _ _ (b + _) _ |- _ => cw_by_inside H
          end
        | apply client_wrange_stack; [dlia | dlia]
        | match goal with H : In (?B, ?j) LBF |- _ => apply (client_wrange_block L LBF SP TOP a k B j H); dlia end
        | eapply client_wrange_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange L _ _ _ _ _ |- _ => cw_by_inside H end ]
  end.

Ltac solve_client_range_core :=
  lazymatch goal with |- client_range ?L ?LBF ?SP ?a ?k =>
  let b := base_of a in
  first [ match goal with
          | H : client_wrange L _ _ _ b _ |- _ => cr_by_inside H
          | H : client_range L _ _ b _ |- _ => cr_by_inside H
          | H : client_wrange L _ _ _ (b + _) _ |- _ => cr_by_inside H
          | H : client_range L _ _ (b + _) _ |- _ => cr_by_inside H
          end
        | apply client_range_stack; dlia
        | match goal with H : In (?B, ?j) LBF |- _ => apply (client_range_block L LBF SP a k B j H); dlia end
        | eapply client_range_block; [ eassumption | dlia | dlia ]
        | eapply client_range_block; [ eauto using in_eq, in_cons | dlia | dlia ]
        | match goal with H : client_wrange L _ _ _ _ _ |- _ => cr_by_inside H end
        | match goal with H : client_range L _ _ _ _ |- _ => cr_by_inside H end ]
  end.


(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac solve_disjoint ::= cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; repeat split;
  first [ assumption | solve [ clear; lia ]
        | lazymatch goal with |- ?A2 + _ <= ?a \/ _ => let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2 end
        | pqlia ].

Ltac transport_after_call segs m m' MU WM ::=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport0 segs W m m' A2 bs2) in H;
              [ | exact MU
                | first [ right; solve_disjoint
                        | destruct bs2; [ left; reflexivity | right; cbn [length] in *; solve_disjoint ] ] ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport segs W m m' A2 xs) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_transport segs W m m' A2 xs) in H; [ | exact MU | solve_disjoint ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | solve_disjoint ]
            | idtac "note: dropping stk across call (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken W Wq m m'); [ unfold sub_fp; cbn [outside]; intros; pqlia | exact MU ] ]
            | fail 100 "callee footprint not inside caller footprint" ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac solve_client_wrange ::= first [ solve_client_wrange_core | progress norm_hst; solve_client_wrange_core ].
Ltac solve_client_range ::= first [ solve_client_range_core | progress norm_hst; solve_client_range_core ].


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sshad_of_chunk_sh : ltac2:(CDefT.buildp (gd_tbl_TacA ()) "Psegs,(17.$18.)PAL,$0.Pm,P,(=.&40.)(19.(=.&8.))Pn,$>.PB,$1.Pcs,(17.$23.)P,(22.R6.R4.(7.(2;.R2.+3.)(2<.R5.))R1.)P,(8.(17.$23.)R2.(2=.R4.))P,(8.$1.(15.R4.+8.)=)P,(5.=R5.)(2>.R:.R9.R8.R6.(7.R6.(12.+8.(14.R7.))))")
(* [comment removed for export] *).
Proof.
  intros segs AL m n B cs H -> HB H0.
  replace (Z.shiftr B 3 + al_sb AL) with (shadow_of AL B) in H
    by (unfold shadow_of; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; lia).
  apply sshad_of_chunk; assumption.
Qed.

(* [comment removed for export] *)
Lemma store_ok_of_rw1 : forall segs m p old,
  rw_cells segs m p [C1 old] -> store_ok segs m (Z_to_bv 64 p) 1 = true.
Proof.
  intros segs m p old H. pose proof (rw_cells_bound segs m p [C1 old] H) as B. cbn in B.
  destruct H as [_ W]. replace (Z_to_bv 64 p) with (wa (p + 0)) by (unfold wa; f_equal; lia).
  eapply (wr_at_store_ok segs m p 1 0 1); [exact W| lia| cbn; lia].
Qed.

(* [comment removed for export] *)
Ltac fake_free_done p HS :=
  lazymatch goal with
  | |- _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) (seg_rom ?segs)) =>
      change (write_to_mem m a bs) with (write_to_mem m (wa p) [Z_to_bv 8 0]);
      (try lazymatch goal with HI : mem_inv segs m |- _ =>
         apply (mem_inv_store segs m (wa p) [Z_to_bv 8 0]) in HI; [| exact HS] end);
      clear HS;
      transport_chunks segs m p [Z_to_bv 8 0];
      let m' := fresh "m" in
      remember (write_to_mem m (wa p) [Z_to_bv 8 0]) as m' eqn:Heqm; clear Heqm; try clear m
  end.


(* [comment removed for export] *)
Ltac solve_disjoint0 := cbn [disjoint_from]; simpl_sizes; first [ exact I | repeat split; first [ assumption | solve [clear; lia] | qlia | pqlia ] ].

Ltac presA_transport HP ::=
  lazymatch type of HP with
  | presW ?segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m ?m' =>
      let HP' := fresh "HPA" in pose proof (presW_presA segs R HIA h LB LF SP SSP W m m' HP) as HP'; presA_transport HP'; clear HP'
  | presA ?segs ?R ?LB ?LF ?SP ?SSP ?TOP ?W ?m ?m' =>
    repeat match goal with
    | H : presW segs R ?HIA ?h ?LB0 ?LF0 ?SP0 ?SSP0 ?W0 ?m0 m |- _ =>
        first [ apply (presW_call segs R HIA h LB0 LF0 SP0 SSP0 W0 m0 m m' LB LF SP SSP TOP W) in H;
                [ | exact HP | solve_incl | solve_incl | qlia | qlia | qlia | solve_outside_incl ]
              | idtac "note: could not compose presW with the callee's presA (dropping):" H; clear H ]
    | H : rw_cells segs m (Z.shiftr ?B 3 + al_sb ?AL) ?cs, OK : cs_ok ?AL ?CS |- _ =>
        first [ apply (presA_shadow_cells_sh segs R CS LB LF SP SSP TOP W m m' B cs OK) in H;
                [ | simpl_sizes; solve_crange | qlia | qlia | exact HP | simpl_sizes; solve_cshd_range ]
              | idtac "note: dropping shadow chunk across call:" H; clear H ]
    | H : rw_cells segs m ?A ?cs |- _ =>
        first [ apply (presA_rw_cells segs R LB LF SP SSP TOP W m m' A cs HP) in H;
                [ | simpl_sizes; solve_client_range | solve_disjoint0 ]
              | idtac "note: dropping (not client memory / inside footprint) across call:" H; clear H ]
    | H : ro_cells segs m ?A ?cs |- _ =>
        first [ apply (presA_ro_cells segs R LB LF SP SSP TOP W m m' A cs HP) in H;
                [ | simpl_sizes; solve_client_range | solve_disjoint0 ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : bytes_at segs m ?A ?bs |- _ =>
        first [ apply (presA_bytes_at0 segs R LB LF SP SSP TOP W m m' A bs HP) in H;
                [ | first [ right; split; [ simpl_sizes; solve_client_range | solve_disjoint0 ]
                          | let NE := fresh "NE" in
                            destruct (PeanoNat.Nat.eq_dec (length bs) 0) as [?|NE];
                            [ left; assumption
                            | right; split;
                              [ simpl_sizes; solve_client_range | solve_disjoint0 ] ] ] ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : u8arr segs m ?A ?xs |- _ =>
        first [ apply (presA_u8arr segs R LB LF SP SSP TOP W m m' A xs HP) in H;
                [ | simpl_sizes; solve_client_range | solve_disjoint0 ]
              | idtac "note: dropping across call:" H; clear H ]
    | H : stk segs m ?lo ?hi |- _ =>
        first [ apply (presA_stk segs R LB LF SP SSP TOP W m m' lo hi HP) in H; [ | qlia | solve_disjoint0 ]
              | idtac "note: dropping stk across call:" H; clear H ]
    | H : aobj segs ?AL ?CS m ?A ?n, OK : cs_ok ?AL ?CS |- _ =>
        first [ apply (presA_aobj0 segs R CS LB LF SP SSP TOP W m m' A n OK HP) in H;
                [ | solve_cs_top
                  | first [ right; split; [ solve_client_range | qlia ]
                          | lazymatch n with
                            | Z.of_nat (length ?bs) =>
                                let NE := fresh "NE" in
                                let EQ0 := fresh "EQ" in
                                destruct (PeanoNat.Nat.eq_dec (length bs) 0) as [EQ0|NE];
                                [ left; clear - EQ0; lia | right; split; [ solve_client_range | qlia ] ]
                            end ] ]
              | idtac "note: dropping aobj across call:" H; clear H ]
    | H : sshad segs ?AL m ?lo ?hi |- _ =>
        first [ apply (presA_sshad segs R LB LF SP SSP TOP W m m' lo hi HP) in H; [ | qlia | qlia ]
              | idtac "note: dropping sshad across call:" H; clear H ]
    | H : abase segs _ m |- _ => clear H
    | H : auar segs _ _ m |- _ => clear H
    | H : wr_at segs m _ _ |- _ => clear H
    | H : mem_inv segs m |- _ => clear H
    end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac dt_sae :=
  lazymatch goal with
  | H : ?x = shadow_of ?L ?c |- ?x = shadow_of ?L ?c => exact H
  | _ => shadow_addr_eq
  end.
Ltac dt_cm8 :=
  lazymatch goal with
  | H : ?c mod 8 = 0 |- ?c mod 8 = 0 => exact H
  | _ => qlia
  end.

Ltac apart_cs A2 n2 a len ::=
  let c := shadow_client_of a in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_client_shadow L CS A2 n2 c a len OK);
      [ solve_crange | solve_crange | dt_sae | first [ dt_pos_lit | clear; lia ] | first [ dt_pos_lit | clear; lia ] ]
  end.
Ltac apart_sc A2 n2 a len ::=
  let c := shadow_client_of A2 in
  match goal with
  | OK : cs_ok ?L ?CS |- _ =>
      apply (apart_shadow_client L CS a len c A2 n2 OK);
      [ solve_crange | solve_crange | shadow_addr_eq | first [ dt_pos_lit | clear; lia ] | first [ dt_pos_lit | clear; lia ] ]
  end.
Ltac apart_ss A2 n2 a len ::=
  let c1 := shadow_client_of a in let c2 := shadow_client_of A2 in
  apply (apart_shadow_shadow _ c2 n2 c1 len A2 a); [ qlia | dt_cm8 | pqlia | shadow_addr_eq | dt_sae ].
Ltac apart_cc A2 n2 a len ::=
  first [ assumption
        | dt_apart_sb
        | solve [ clear; lia ]
        | let b1 := base_of A2 in let b2 := base_of a in lia_2bases b1 b2
        | pqlia ].

(* [comment removed for export] *)
Ltac dt_store_cache SAE CM8 a :=
  tryif store_is_shadow a
  then (let c := shadow_client_of a in
        lazymatch goal with
        | OK : cs_ok ?L ?CS |- _ =>
            try (assert (SAE : a = shadow_of L c) by shadow_addr_eq);
            try (assert (CM8 : c mod 8 = 0) by qlia)
        | _ => idtac
        end)
  else idtac.

Ltac transport_chunks segs m a bs ::=
  let Ha := fresh "Ha_st" in let Hl := fresh "Hl_st" in let CR := fresh "CRst" in
  let SAE := fresh "SAEst" in let CM8 := fresh "CM8st" in
  try store_bounds Ha Hl CR a bs;
  (tryif store_is_shadow a then note_chunk_cranges segs m else idtac);
  dt_store_cache SAE CM8 a;
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other0 segs m a bs A2 bs2) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart0 ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8arr segs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u32arr segs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u64arr segs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : u8ro segs m ?A2 ?xs |- _ =>
      first [ apply (u8ro_frame segs m A2 xs a bs) in H;
              [ | sf_a0 | sf_al | simpl_sizes; simpl_arr_sizes; solve_apart ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : HEAP _ _ ?HI ?h ?LB m ?mo |- _ =>
      first [ eapply (heap_write segs _ HI h LB m mo _ a bs) in H;
              [ | eassumption | simpl_sizes; solve_client_wrange | qlia | simpl_sizes; qlia ]
            | idtac "note: could not carry HEAP across the store (dropping):" H; clear H ]
  | H : pristine ?lo ?hi ?E m |- _ =>
      first [ apply (pristine_write lo hi E m a bs) in H;
              [ | lia | simpl_sizes; lia | intros; simpl_sizes; lia ]
            | idtac "note: could not carry pristine across the store (dropping):" H; clear H ]
  | H : statics_ok segs ?L m |- _ =>
      first [ apply (statics_ok_write segs L m a bs) in H;
              [ | qlia | simpl_sizes; qlia | simpl_sizes; pqlia ]
            | idtac "note: could not carry statics_ok across the store (dropping):" H; clear H ]
  (* [comment removed for export] *)
  | H : HM segs ?R ?HIA ?h ?LB ?LF m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (hm_write_shadow segs R HIA h LB LF m c a bs) in H;
                    [ | simpl_sizes; solve_hm_shadow_range | dt_sae | sf_a0 | sf_al ])
              else (apply (hm_write segs R HIA h LB LF m a bs) in H; [ | simpl_sizes; solve_client_wrange | sf_a0 | sf_al ])
            | idtac "note: could not carry HM across the store (dropping):" H; clear H ]
  | H : presW segs ?R ?HIA ?h ?LB ?LF ?SP ?SSP ?W ?m0 m |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    first [ match goal with SF : shadow_free _ LB LF SSP _ ?C ?n |- _ =>
                              apply (presW_store_shadow_cov segs R HIA h LB LF SP SSP W m0 m c a bs C n) in H;
                              [ | qlia | dt_sae | dt_cm8 | simpl_sizes; solve_crange | exact SF | qlia | simpl_sizes; qlia ] end
                          | apply (presW_store_shadow_stack segs R HIA h LB LF SP SSP W m0 m c a bs) in H;
                            [ | qlia | dt_sae | dt_cm8 | simpl_sizes; solve_crange | qlia | simpl_sizes; qlia ]
                          | match goal with FR : fresh_apart _ LB LF ?N ?k, AP : forall B j, In (B, j) LF -> _ |- _ =>
                              apply (presW_store_shadow_fresh segs R HIA h LB LF SP SSP W m0 m c a bs N k) in H;
                              [ | qlia | dt_sae | dt_cm8 | simpl_sizes; solve_crange | exact FR | exact AP | qlia | simpl_sizes; qlia | qlia ] end ])
              else first [ match goal with WC : wcover _ LB LF SP W ?A ?n |- _ =>
                             apply (presW_store_cov segs R HIA h LB LF SP SSP W m0 m a bs A n) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact WC | qlia | simpl_sizes; qlia ] end
                         | apply (presW_store_out segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | cbn [inside]; simpl_sizes; qlia ]
                         | apply (presW_store_stack segs R HIA h LB LF SP SSP W m0 m a bs) in H;
                           [ | simpl_sizes; solve_crange | sf_a0 | sf_al | qlia | simpl_sizes; qlia ]
                         | match goal with FR : fresh_apart _ LB LF ?N ?k |- _ =>
                             apply (presW_store_fresh segs R HIA h LB LF SP SSP W m0 m a bs N k) in H;
                             [ | simpl_sizes; solve_crange | sf_a0 | sf_al | exact FR | qlia | simpl_sizes; qlia | qlia ] end ]
            | idtac "note: could not carry presW across the store (dropping):" H; clear H ]
  | H : abase segs ?L m, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (abase_shadow_store_at segs L CS m c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | simpl_sizes; first [ dt_pos_lit | clear; lia ] | dt_sae ])
              else (apply (abase_frame segs L CS OK m a bs) in H; [ | simpl_sizes; solve_crange | simpl_sizes; first [ dt_pos_lit | clear; lia ] | sf_a0 | sf_al ])
            | idtac "note: could not carry abase across the store (dropping):" H; clear H ]
  | H : aobj segs ?L ?CS m ?A ?n, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (aobj_shadow_store_at segs L CS m A n c a bs OK) in H;
                    [ | simpl_sizes; solve_crange | dt_cm8 | simpl_sizes; first [ dt_pos_lit | clear; lia ] | simpl_sizes; pqlia | dt_sae ])
              else (apply (aobj_frame segs L CS OK m A n a bs) in H; [ | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry aobj across the store (dropping):" H; clear H ]
  | H : sshad segs ?L m ?lo ?hi, OK : cs_ok ?L ?CS |- _ =>
      first [ tryif store_is_shadow a
              then (let c := shadow_client_of a in
                    apply (sshad_shadow_store_at segs L CS m lo hi c a bs OK) in H;
                    [ | solve_crange | simpl_sizes; solve_crange | dt_cm8 | simpl_sizes; first [ dt_pos_lit | clear; lia ] | simpl_sizes; pqlia | dt_sae ])
              else (apply (sshad_frame segs L CS m lo hi a bs OK) in H; [ | solve_crange | simpl_sizes; solve_crange | sf_a0 | sf_al ])
            | idtac "note: could not carry sshad across the store (dropping):" H; clear H ]
  end;
  footprint_work segs m a bs;
  try clear Ha; try clear Hl; try clear CR; try clear SAE; try clear CM8.
