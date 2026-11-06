(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_La0bg A_World A_Img A_Cocsh A_Tac.

Module A_CrcKit.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_La0bg A_World A_Img A_Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition CRC_FRAME := 128%Z.
Definition CRC_TAB : Z := 0x24800.      (* [comment removed for export] *)
Definition CRC_BRAID : Z := 0x24d00.    (* [comment removed for export] *)
Definition X2N_TAB_A : Z := 0x26100.    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma crc_tab_at : forall m, mem_inv rsegs m ->
  exists tab, Z.of_nat (length tab) = 1024%Z /\ bytes_at rsegs m 0x24800 tab.
Proof.
  intros m MI.
  set (bs := match image_bytes rsegs 0x24800 1024%nat with Some bs => bs | None => [] end).
  assert (HL : Z.of_nat (length bs) = 1024%Z) by (vm_compute; reflexivity).
  exists bs. split; [exact HL|].
  apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | lia | rewrite HL; lia].
Qed.

Lemma crc_braid_at : forall m, mem_inv rsegs m ->
  exists tab, Z.of_nat (length tab) = 4096%Z /\ bytes_at rsegs m 0x24d00 tab.
Proof.
  intros m MI.
  set (bs := match image_bytes rsegs 0x24d00 4096%nat with Some bs => bs | None => [] end).
  assert (HL : Z.of_nat (length bs) = 4096%Z) by (vm_compute; reflexivity).
  exists bs. split; [exact HL|].
  apply (ro_table_at rsegs m); [exact MI | vm_compute; reflexivity | lia | rewrite HL; lia].
Qed.

Section CEIL.
  Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Lemma crc_tab_shadow : forall v, cenv v -> bytes_at rsegs v (sh 0x24800) (repeat (Z_to_bv 8 0) 128).
  Proof.
    intros v [CH _]. change (repeat (Z_to_bv 8 0) 128) with (shpat 1024).
    exact (global_shadow_pat v 0x24800 1024 1280 CH ltac:(gdesc_in)).
  Qed.
  Lemma crc_braid_shadow : forall v, cenv v -> bytes_at rsegs v (sh 0x24d00) (repeat (Z_to_bv 8 0) 512).
  Proof.
    intros v [CH _]. change (repeat (Z_to_bv 8 0) 512) with (shpat 4096).
    exact (global_shadow_pat v 0x24d00 4096 5120 CH ltac:(gdesc_in)).
  Qed.
  Lemma x2n_tab_shadow : forall v, cenv v -> bytes_at rsegs v (sh 0x26100) (repeat (Z_to_bv 8 0) 16).
  Proof.
    intros v [CH _]. change (repeat (Z_to_bv 8 0) 16) with (shpat 128).
    exact (global_shadow_pat v 0x26100 128 160 CH ltac:(gdesc_in)).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac shadow_addrc SRC k :=
  lazymatch goal with
  | |- context [Z_to_bv 64 (Z.shiftr ?X 3 + ?off)] => idtac
  | |- context [Z_to_bv 64 (?off + Z.shiftr ?X 3)] => rewrite (Z.add_comm off (Z.shiftr X 3))
  end;
  shadow_addr SRC k.

(* [comment removed for export] *)
Ltac shadow_slow_j U :=
  zstep;
  let K2 := fresh "KS2" in
  first [ zstep; if_cases K2; zify_cond K2 | zstep; zstep; if_cases K2; zify_cond K2 ];
  [ first [ shadow_dead | (zstep; shadow_join U) ] | first [ shadow_dead | (zstep; shadow_join U) ] ].

(* [comment removed for export] *)
Ltac shadow_chkj SRC k U :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
Tactic Notation "shadow_chkj_gen" constr(SRC) constr(k) constr(U) integer(n) :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
Tactic Notation "shadow_rechkj_gen" constr(SRC) constr(X) constr(k) constr(U) integer(n) :=
  shadow_addr_at SRC X k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slow_j U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
Ltac lit0 := try change (sxb (Z_to_bv 8 0)) with (Z_to_bv 64 0); try change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
Ltac chk_branch :=
  let K := fresh "KS" in
  zstep; if_cases K; zify_cond K;
  [ first [ shadow_fast K; clear K | (exfalso; lia) ]
  | first [ shadow_fast K; clear K | (exfalso; lia) ] ];
  shadow_cleanup.
(* [comment removed for export] *)
Ltac tchk SRC k := zstep; zstep; shadow_addr SRC k; zstep; lit0; chk_branch.
Tactic Notation "tchk_gen" constr(SRC) constr(k) integer(n) :=
  zstep; zstep; shadow_addr SRC k; zstep; lit0; do n zstep; chk_branch.

(* [comment removed for export] *)
Lemma lxor8_range : forall x y, (0 <= x < 256)%Z -> (0 <= y < 256)%Z -> (0 <= Z.lxor x y <= 255)%Z.
Proof. intros x y Hx Hy. pose proof (lxor_bound 8 x y ltac:(lia) ltac:(change (2^8)%Z with 256%Z; lia) ltac:(change (2^8)%Z with 256%Z; lia)). change (2^8)%Z with 256%Z in H. lia. Qed.
Ltac tidx :=
  crc_arith_prep;
  repeat match goal with |- context [Z.lxor ?x ?y] =>
    let R := fresh "JXR" in
    assert (R : (0 <= Z.lxor x y <= 255)%Z)
      by (apply (lxor8_range x y); first [apply byte_range | lia | (pose proof (byte_range); lia)]);
    let j := fresh "jx" in set (j := Z.lxor x y) in *; clearbody j
  end.
End A_CrcKit.


Module A_cro3f.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_World A_Cocsh A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hot_qset := lazymatch goal with |- evt _ ?Q _ => lazymatch Q with (fun _ => _) => set (hotQ := Q) | _ => idtac end | |- _ => idtac end.
Ltac hot_qend := lazymatch goal with |- evt _ ?Q _ => first [ is_var Q; subst Q | idtac ] | |- ?Q _ => first [ is_var Q; subst Q; cbv beta | idtac ] | |- _ => idtac end.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section Tail.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m mc : word -> option byte) (lo : Z) (junk : list byte).
  Variables (B : Z) (inp tab : list byte) (P NP : Z).
  (* [comment removed for export] *)
  Variables (g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g30 g31 : word).
  Hypothesis MUc : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m mc.
  Hypothesis WMc : wmono rsegs m mc.
  Hypothesis MIc : mem_inv rsegs mc.
  Hypothesis STc : stk rsegs mc lo (bv_unsigned sp + -128).
  Hypothesis LO : (lo + 128 <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LJ : length junk = 24%nat.
  Hypothesis FRc : rw_cells rsegs mc (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INPc : bytes_at rsegs mc B inp.
  Hypothesis TABc : bytes_at rsegs mc 0x24800 tab.
  Hypothesis TL : Z.of_nat (length tab) = 1024%Z.
  Hypothesis SHB : bytes_at rsegs mc (sh P) (shpat NP).
  Hypothesis SHB' : (P mod 8 = 0 /\ 0 <= P /\ P <= B /\ B + Z.of_nat (length inp) <= P + NP /\ P + NP <= alloc_ceiling)%Z.
  Hypothesis SHT : bytes_at rsegs mc (sh 0x24800) (repeat (Z_to_bv 8 0) 128).
  Hypothesis LL : (Z.of_nat (length inp) < 2^64)%Z.

  Notation L := (Z.of_nat (length inp)).
  Notation POST := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None 128 lo m).
  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Notation AT pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 g8 g9 x10 x11 x12 x13 x14 SOFF (Z_to_bv 64 0x24800) x17
            g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 g30 g31)
        F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  #[using="INPc mc"] Lemma B_bound : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INPc). Qed.

  (* [comment removed for export] *)
  #[using="FRc LJ LO STc MIc WMc MUc P tab inp junk"] Lemma epilogue : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29,
    evt rsegs POST (AT 0x91c6c x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29).
  Proof.
    intros. unfold leaf_post.
    pose proof MUc as MU. pose proof WMc as WM. pose proof FRc as FR. pose proof STc as STK. pose proof MIc as MI.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    replace (bv_unsigned sp - 128)%Z with (bv_unsigned sp + -128)%Z by lia.
    hot_qset.
    do 14 zstep.
    release_frame FR STK (bv_unsigned sp).
    zstep.
    all: hot_qend. finish.
  Qed.

  (* [comment removed for export] *)
  #[using="FRc LJ LO STc MIc WMc MUc P tab inp junk"] Lemma fold_exit : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29,
    evt rsegs POST (AT 0x91c60 x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29).
  Proof. intros. pose proof MIc as MI. do 3 zstep. apply epilogue. Qed.

  (* [comment removed for export] *)
  #[using="SHT SHB' SHB TL TABc INPc FRc LJ LO STc MIc WMc MUc NP P tab junk Clg"] Lemma tail1 : forall (k : nat) (i n : Z) x1 x5 x6 x7 x13 x14 x17 x28 x29,
    (k = Z.to_nat n)%nat -> (0 <= i)%Z -> (1 <= n)%Z -> (i + n <= L)%Z ->
    evt rsegs POST (AT 0x91bec x1 x5 x6 x7 (Z_to_bv 64 (B + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 n) x13 x14 x17 x28 x29).
  Proof.
    induction k as [|k IH]; intros i n x1 x5 x6 x7 x13 x14 x17 x28 x29 Hk Hi Hn HiL; [lia|].
    pose proof B_bound as BB. pose proof MIc as MI. pose proof TL as TL'. pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof alloc_ceiling_num as ACV.
    (* [comment removed for export] *)
    shadow_chkj SHB 1%Z 14%Z.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    tidx. tchk SHT 4%Z.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    all: lazymatch type of K with
         | _ = _ => (* [comment removed for export] *) zstep; apply fold_exit
         | _ => replace (B + i + 1)%Z with (B + (i + 1))%Z by lia; apply (IH (i + 1)%Z (n + -1)%Z x1); lia
         end.
  Qed.

  (* [comment removed for export] *)
  #[using="LL SHT SHB' SHB TL TABc INPc FRc LJ LO STc MIc WMc MUc NP P tab junk Clg"] Lemma tail_entry : forall (i ea er : Z) x1 x5 x6 x7 x10 x13 x14 x17 x28 x29,
    (0 <= i <= L)%Z -> (ea = B + i)%Z -> (er = L - i)%Z ->
    evt rsegs POST (AT 0x91be4 x1 x5 x6 x7 x10 (Z_to_bv 64 ea) (Z_to_bv 64 er) x13 x14 x17 x28 x29).
  Proof.
    intros i ea er x1 x5 x6 x7 x10 x13 x14 x17 x28 x29 Hi -> ->.
    pose proof B_bound as BB. pose proof MIc as MI.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K; try rewrite Z.mod_small in K by (clear - LL Hi; lia).
    all: lazymatch type of K with
         | _ = _ => apply fold_exit
         | _ => (* [comment removed for export] *) zstep; apply (tail1 (Z.to_nat (L - i)) i (L - i)%Z x1); clear - LL Hi K; lia
         end.
  Qed.

  (* [comment removed for export] *)
  Local Ltac unit8 :=
    zstep; shadow_chkj_gen SHB 1%Z 29%Z 1; gen_loads;
    cstep; zstep; zstep; gen_lxor; zstep; zstep; zstep; zstep;
    tidx; tchk SHT 4%Z.

  (* [comment removed for export] *)
  #[using="LL SHT SHB' SHB TL TABc INPc FRc LJ LO STc MIc WMc MUc NP P tab junk Clg"] Lemma loop8 : forall (k : nat) (ib t esh er : Z) x1 x10 x13 x14 x17 x28 x29,
    (k = Z.to_nat (L - ib - t))%nat -> (0 <= ib)%Z -> (0 <= t)%Z -> (ib + t + 8 <= L)%Z ->
    (esh = (B + ib + t) / 8 + 2147450880)%Z -> (er = L - ib - t)%Z ->
    evt rsegs POST (AT 0x918d4 x1 (Z_to_bv 64 t) (Z_to_bv 64 esh) (Z_to_bv 64 7)
                       x10 (Z_to_bv 64 (B + ib)) (Z_to_bv 64 er) x13 x14 x17 x28 x29).
  Proof.
    induction k as [k IH] using lt_wf_ind; intros ib t esh er x1 x10 x13 x14 x17 x28 x29 Hk Hib Ht HL -> ->.
    pose proof B_bound as BB. pose proof MIc as MI. pose proof TL as TL'. pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof alloc_ceiling_num as ACV. pose proof LL as LL'.
    (* [comment removed for export] *)
    shadow_rechkj_gen SHB (B + ib + t)%Z 1%Z 14%Z 1.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. zstep. tidx. tchk SHT 4%Z.
    (* [comment removed for export] *)
    unit8. unit8. unit8. unit8. unit8. unit8. unit8.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. zstep. gen_lxor. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    all: lazymatch type of K with
         | (_ <= 7)%Z => (* [comment removed for export] *) zstep; apply (tail_entry (ib + t + 8)%Z); clear - K Hib Ht HL; lia
         | _ => (* [comment removed for export] *) zstep; apply (IH (Z.to_nat (L - ib - (t + 8))) ltac:(clear - K Hib Ht HL Hk; lia) ib (t + 8)%Z _ _ x1); clear - K Hib Ht HL;
                first [lia | Z.div_mod_to_equations; lia]
         end.
  Qed.

  (* [comment removed for export] *)
  #[using="LL SHT SHB' SHB TL TABc INPc FRc LJ LO STc MIc WMc MUc NP P tab junk Clg"] Lemma sec_tail : forall (i ea er : Z) x1 x5 x6 x7 x10 x13 x14 x17 x28 x29,
    (0 <= i <= L)%Z -> (ea = B + i)%Z -> (er = L - i)%Z ->
    evt rsegs POST (AT 0x918bc x1 x5 x6 x7 x10 (Z_to_bv 64 ea) (Z_to_bv 64 er) x13 x14 x17 x28 x29).
  Proof.
    intros i ea er x1 x5 x6 x7 x10 x13 x14 x17 x28 x29 Hi -> ->.
    pose proof B_bound as BB. pose proof MIc as MI. pose proof LL as LL'.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K; try rewrite Z.mod_small in K by (clear - LL Hi; lia).
    all: lazymatch type of K with
         | (_ < 8)%Z => apply (tail_entry i); clear - Hi; lia
         | _ => (* [comment removed for export] *)
                zstep; zstep; zstep; zstep;
                apply (loop8 (Z.to_nat (L - i - 0)) i 0%Z _ _ x1); clear - Hi K; rewrite ?Z.shiftr_div_pow2 by lia;
                first [lia | Z.div_mod_to_equations; lia]
         end.
  Qed.
End Tail.
End A_cro3f.


Module A_crtab.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_World A_Cocsh A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_cro3f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@Hq; @BB; @SZ; @SR; @KS; @TL'; @HqL; @LJ; @P0; @HREM; @PHI; @PCE; @ACV; @H; @H0; @H1; @H2; @H3; @H4; @H5; @H6; @H7; @H8; @H9; @H10; @H11; @H12; @H13; @H14; @H15; @H16; @H17; @H18])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section Tail.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m mc : word -> option byte) (lo : Z) (junk : list byte).
  Variables (B : Z) (inp tab : list byte) (P NP : Z).
  (* [comment removed for export] *)
  Variables (g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 g30 g31 : word).
  Hypothesis MUc : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m mc.
  Hypothesis WMc : wmono rsegs m mc.
  Hypothesis MIc : mem_inv rsegs mc.
  Hypothesis STc : stk rsegs mc lo (bv_unsigned sp + -128).
  Hypothesis LO : (lo + 128 <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LJ : length junk = 24%nat.
  Hypothesis FRc : rw_cells rsegs mc (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INPc : bytes_at rsegs mc B inp.
  Hypothesis TABc : bytes_at rsegs mc 0x24800 tab.
  Hypothesis TL : Z.of_nat (length tab) = 1024%Z.
  Hypothesis SHB : bytes_at rsegs mc (sh P) (shpat NP).
  Hypothesis SHB' : (P mod 8 = 0 /\ 0 <= P /\ P <= B /\ B + Z.of_nat (length inp) <= P + NP /\ P + NP <= alloc_ceiling)%Z.
  Hypothesis SHT : bytes_at rsegs mc (sh 0x24800) (repeat (Z_to_bv 8 0) 128).
  Hypothesis LL : (Z.of_nat (length inp) < 2^64)%Z.

  Notation L := (Z.of_nat (length inp)).
  Notation POST := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None 128 lo m).
  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Notation AT pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 g8 g9 x10 x11 x12 x13 x14 SOFF (Z_to_bv 64 0x24800) x17
            g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 g30 g31)
        F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  #[using="INPc mc"] Lemma B_bound : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INPc). Qed.


  (* [comment removed for export] *)
  Local Ltac wround :=
    zstep; zstep; zstep; tidx; tchk SHT 4%Z; cstep; zstep; zstep; zstep; gen_lxor; zstep; lit_branch.
  (* [comment removed for export] *)
  Local Ltac wloop := wround; wround; wround; wround; zstep.
  (* [comment removed for export] *)
  Local Ltac wnext U :=
    zstep; shadow_chk SHB 4%Z U; cstep; zstep; gen_lxor; zstep; gen_lxor; zstep.

  (* [comment removed for export] *)
  #[using="LL SHT SHB' SHB TL TABc INPc FRc LJ LO STc MIc WMc MUc NP P tab junk Clg"] Lemma last_block : forall (q ea : Z) x1 x5 x6 (x7 : word) x10 x12 (x13 : word) x14 x17 x28 x29,
    (0 <= q)%Z -> (q + 20 <= L)%Z -> ((B + q) mod 4 = 0)%Z ->
    ((bv_unsigned x7 - 20 * bv_unsigned x13) mod 2^64 = L - (q + 20))%Z -> (ea = B + q)%Z ->
    evt rsegs POST (AT 0x916a4 x1 x5 x6 x7 x10 (Z_to_bv 64 ea) x12 x13 x14 x17 x28 x29).
  Proof.
    intros until x29. intros Hq HqL AL4 HREM ->.
    pose proof B_bound as BB. pose proof MIc as MI. pose proof TL as TL'. pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof alloc_ceiling_num as ACV. pose proof LL as LL'.
    pose proof (bv_unsigned_in_range _ x7) as R7. pose proof (bv_unsigned_in_range _ x13) as R13.
    unfold bv_modulus in R7, R13. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R7, R13.
    (* [comment removed for export] *)
    shadow_chk SHB 4%Z 12%Z.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 (bv_unsigned x13 * 18446744073709551596 + bv_unsigned x7)) with (Z_to_bv 64 (L - (q + 20)))
      by (apply Z_to_bv_eqm; rewrite <- HREM;
          replace (bv_unsigned x13 * 18446744073709551596 + bv_unsigned x7)%Z
             with ((bv_unsigned x7 - 20 * bv_unsigned x13) + bv_unsigned x13 * 2^64)%Z by lia;
          rewrite Z.mod_add by lia; rewrite Zmod_mod; reflexivity).
    zstep. gen_lxor. zstep.
    (* [comment removed for export] *)
    wloop.
    (* [comment removed for export] *)
    wnext 7%Z. wloop.
    (* [comment removed for export] *)
    wnext 7%Z. wloop.
    (* [comment removed for export] *)
    wnext 6%Z. wloop.
    (* [comment removed for export] *)
    wnext 5%Z. wloop.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    eapply sec_tail with (i := (q + 20)%Z) (B := B) (inp := inp) (tab := tab) (P := P) (NP := NP) (junk := junk) (m := m) (lo := lo);
      try eassumption; clear - Hq HqL; lia.
  Qed.
End Tail.
End A_crtab.


Module A_crgv7.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_World A_Cocsh A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)

Section Braid.
  Context {Clg : Ceiling}.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (mc : word -> option byte) (tabb : list byte).
  Hypothesis MIc : mem_inv rsegs mc.
  Hypothesis TABB : bytes_at rsegs mc 0x24d00 tabb.
  Hypothesis TLB : Z.of_nat (length tabb) = 4096%Z.
  Hypothesis SHBR : bytes_at rsegs mc (sh 0x24d00) (repeat (Z_to_bv 8 0) 512).

  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Notation ATI pc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 SOFF (Z_to_bv 64 0x24800) x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 0x24d00))
        F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac clr := repeat match goal with H : (0 <= ?x <= 255)%Z |- _ => clear H; try clear x end.
  Local Ltac iround0 := zstep; zstep; zstep; zstep; zstep; zstep; tidx; tchk SHBR 4%Z.
  Local Ltac iround1 := zstep; zstep; zstep; zstep; zstep; zstep; tidx; tchk_gen SHBR 4%Z 1; gen_loads.

  (* [comment removed for export] *)
  #[using="SHBR TLB TABB MIc tabb"] Lemma braid_inner : forall (Q : machine_state -> Prop)
      x1 x5 x6 x7 x8 x9 x10 x11 x14 x17 x18 x19 x20 x21 x23 x24 x25 x26 x27 x28 x29 x30,
    (forall y1 y5 y6 y8 y9 y12 y13 y14 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29,
        evt rsegs Q (ATI 0x915cc y1 y5 y6 x7 y8 y9 x10 x11 y12 y13 y14 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 x30)) ->
    evt rsegs Q (ATI 0x91478 x1 x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 0) (Z_to_bv 64 8) x14 x17 x18 x19 x20 x21 (Z_to_bv 64 3) x23 x24 x25 x26 x27 x28 x29 x30).
  Proof.
    intros until x30. intros K.
    pose proof MIc as MI. pose proof TLB as TLB'.
    (* [comment removed for export] *)
    iround0. iround1. iround1. iround1. iround1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. cstep. clr. zstep. zstep. zstep. zstep. zstep. gen_lxor. zstep. lit_branch.
    (* [comment removed for export] *)
    zstep.
    iround0. iround1. iround1. iround1. iround1.
    zstep. zstep. zstep. cstep. clr. zstep. zstep. zstep. zstep. zstep. gen_lxor. zstep. lit_branch.
    zstep.
    iround0. iround1. iround1. iround1. iround1.
    zstep. zstep. zstep. cstep. clr. zstep. zstep. zstep. zstep. zstep. gen_lxor. zstep. lit_branch.
    apply K.
  Qed.
End Braid.
End A_crgv7.


Module A_crcyr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ATac AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_CrcLib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_World A_Cocsh A_Tac.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_cro3f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_crtab OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_crgv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma frame24 : forall (v : mem) A (j8 : list byte) (w1 w2 : word) rest,
  rw_cells rsegs v A (CB 8 j8 :: C8 w1 :: C8 w2 :: rest) ->
  exists junk, length junk = 24%nat /\ rw_cells rsegs v A (CB 24 junk :: rest).
Proof.
  intros v A j8 w1 w2 rest H.
  apply (proj1 (rw_cells_app rsegs v A [CB 8 j8; C8 w1; C8 w2] rest)) in H as [H1 H2].
  destruct (rw_cells_forget _ _ _ _ H1) as [junk HJ]. cbn [cells_size csize Nat.add] in HJ, H2.
  exists junk. split; [exact (rw_CB_length _ _ _ _ _ HJ)|].
  apply (proj2 (rw_cells_app rsegs v A [CB 24 junk] rest)). split; [exact HJ|]. cbn [cells_size csize Nat.add]. exact H2.
Qed.

Section Braid.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m mc : word -> option byte) (lo : Z) (j8 : list byte) (blks : Z).
  Variables (B : Z) (inp tab tabb : list byte) (P NP : Z).
  Hypothesis MUc : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m mc.
  Hypothesis WMc : wmono rsegs m mc.
  Hypothesis MIc : mem_inv rsegs mc.
  Hypothesis STc : stk rsegs mc lo (bv_unsigned sp + -128).
  Hypothesis LO : (lo + 128 <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis FRB : rw_cells rsegs mc (bv_unsigned sp + -128)
    [CB 8 j8; C8 (Z_to_bv 64 (20 * blks)); C8 (Z_to_bv 64 blks); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INPc : bytes_at rsegs mc B inp.
  Hypothesis TABc : bytes_at rsegs mc 0x24800 tab.
  Hypothesis TL : Z.of_nat (length tab) = 1024%Z.
  Hypothesis TABB : bytes_at rsegs mc 0x24d00 tabb.
  Hypothesis TLB : Z.of_nat (length tabb) = 4096%Z.
  Hypothesis SHB : bytes_at rsegs mc (sh P) (shpat NP).
  Hypothesis SHB' : (P mod 8 = 0 /\ 0 <= P /\ P <= B /\ B + Z.of_nat (length inp) <= P + NP /\ P + NP <= alloc_ceiling)%Z.
  Hypothesis SHT : bytes_at rsegs mc (sh 0x24800) (repeat (Z_to_bv 8 0) 128).
  Hypothesis SHBR : bytes_at rsegs mc (sh 0x24d00) (repeat (Z_to_bv 8 0) 512).
  Hypothesis LL : (Z.of_nat (length inp) < 2^64)%Z.
  Hypothesis BLK : (0 <= blks /\ 20 * blks < 2^64)%Z.

  Notation L := (Z.of_nat (length inp)).
  Notation POST := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None 128 lo m).
  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Notation ATB pc x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 SOFF (Z_to_bv 64 0x24800) x17
            x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 0x24d00))
        F (Z_to_bv 64 pc) fc None mc (seg_rom rsegs)).

  #[using="INPc mc"] Lemma B_boundB : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INPc). Qed.

  (* [comment removed for export] *)
  Local Ltac bunit := zstep; gen_lxor; zstep; zstep; zstep; tidx; tchk_gen SHBR 4%Z 1; gen_loads.
  Local Ltac clr := repeat match goal with H : (0 <= ?x <= 255)%Z |- _ => clear H; try clear x end.

  (* [comment removed for export] *)
  #[using="BLK LL SHBR SHT SHB' SHB TLB TABB TL TABc INPc FRB LO STc MIc WMc MUc NP P tabb tab j8 Clg"] Lemma braid_outer : forall (n : nat) (c i0 : Z) x1 x5 x6 x8 x9 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29,
    (1 <= n)%nat -> (0 <= i0)%Z -> (i0 <= c)%Z -> ((B + c) mod 4 = 0)%Z -> ((B + i0) mod 4 = 0)%Z ->
    (c + 20 * Z.of_nat n + 20 <= i0 + 20 * blks)%Z -> (i0 + 20 * blks <= L)%Z ->
    evt rsegs POST (ATB 0x91344 x1 x5 x6 (Z_to_bv 64 (L - i0)) x8 x9 (Z_to_bv 64 (B + c)) (Z_to_bv 64 (B + i0)) x12 x13 x14 x17
                        x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 (Z_to_bv 64 (Z.of_nat n))).
  Proof.
    induction n as [|n IH]; intros until x29; intros Hn Hi0 Hc AL4 AL0 HCN HL; [lia|].
    pose proof B_boundB as BB. pose proof MIc as MI. pose proof TL as TL'. pose proof TLB as TLB'. pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof alloc_ceiling_num as ACV. pose proof LL as LL'. pose proof BLK as BLK'.
    (* [comment removed for export] *)
    shadow_chkj SHB 4%Z 13%Z.
    (* [comment removed for export] *)
    zstep. shadow_chkj_gen SHB 4%Z 8%Z 1. gen_loads.
    zstep. shadow_chkj_gen SHB 4%Z 8%Z 1. gen_loads.
    zstep. shadow_chkj_gen SHB 4%Z 8%Z 1. gen_loads.
    zstep. shadow_chkj_gen SHB 4%Z 8%Z 1. gen_loads.
    (* [comment removed for export] *)
    bunit. bunit. bunit. bunit. bunit.
    (* [comment removed for export] *)
    zstep. cstep. clr. zstep. zstep.
    (* [comment removed for export] *)
    eapply (braid_inner sp gp tp F fc mc tabb MIc TABB TLB SHBR). intros.
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_cases K; zify_cond K.
    all: lazymatch type of K with
         | _ = _ => (* [comment removed for export] *)
             zstep; zstep; zstep; zstep; zstep;
             destruct (frame24 mc _ j8 _ _ _ FRB) as (jk24 & LJ & FRc);
             eapply last_block with (q := (i0 + 20 * blks - 20)%Z) (B := B) (inp := inp) (tab := tab) (P := P) (NP := NP) (junk := jk24) (m := m) (lo := lo);
             try eassumption;
             [ clear - Hi0 Hc HCN | clear - K Hn HCN HL | clear - AL0; Z.div_mod_to_equations; lia
             | rewrite !unsigned_lit by (clear - Hi0 BLK' BB LL' HL; lia); rewrite Z.mod_small by (clear - Hi0 BLK' BB LL' HL K Hn HCN; lia); clear - Hi0 HL; lia
             | clear - Hi0 BLK' ];
             lia
         | _ => (* [comment removed for export] *) zstep;
             replace (Z_to_bv 64 (B + c + 20)) with (Z_to_bv 64 (B + (c + 20))) by (f_equal; lia);
             replace (Z_to_bv 64 (Z.of_nat (S n) + -1)) with (Z_to_bv 64 (Z.of_nat n)) by (f_equal; lia);
             apply (IH (c + 20)%Z i0); clear - K Hn Hi0 Hc AL4 AL0 HCN HL; try lia; Z.div_mod_to_equations; lia
         end.
  Qed.
End Braid.
End A_crcyr.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_CrcKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_cro3f OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_crtab OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_crgv7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_crc32.A_crcyr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.flia ::= first [ assumption | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.slim; lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_CrcLib.crc_arith_prep; lia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Lemma land3_mod : forall x, Z.land x 3 = (x mod 4)%Z.
Proof. intros x. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Section Entry.
  Context {Clg : Ceiling}.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m m1 : word -> option byte) (lo : Z) (junk : list byte).
  Variables (B : Z) (inp tab tabb : list byte) (P NP : Z).
  (* [comment removed for export] *)
  Variables (g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : word).
  Hypothesis MU1 : munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m m1.
  Hypothesis WM1 : wmono rsegs m m1.
  Hypothesis MI1 : mem_inv rsegs m1.
  Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -128).
  Hypothesis LO : (lo + 128 <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LJ : length junk = 24%nat.
  Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -128)
    [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis INP1 : bytes_at rsegs m1 B inp.
  Hypothesis TAB1 : bytes_at rsegs m1 0x24800 tab.
  Hypothesis TL : Z.of_nat (length tab) = 1024%Z.
  Hypothesis TABB1 : bytes_at rsegs m1 0x24d00 tabb.
  Hypothesis TLB : Z.of_nat (length tabb) = 4096%Z.
  Hypothesis SHB : bytes_at rsegs m1 (sh P) (shpat NP).
  Hypothesis SHB' : (P mod 8 = 0 /\ 0 <= P /\ P <= B /\ B + Z.of_nat (length inp) <= P + NP /\ P + NP <= alloc_ceiling)%Z.
  Hypothesis SHT : bytes_at rsegs m1 (sh 0x24800) (repeat (Z_to_bv 8 0) 128).
  Hypothesis SHBR : bytes_at rsegs m1 (sh 0x24d00) (repeat (Z_to_bv 8 0) 512).
  Hypothesis LL : (Z.of_nat (length inp) < 2^64)%Z.

  Notation L := (Z.of_nat (length inp)).
  Notation POST := (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc None 128 lo m).
  Notation SOFF := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Notation ATE pc x1 x5 x6 x7 x10 x11 x12 x13 x14 x17 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 g8 g9 x10 x11 x12 x13 x14 SOFF (Z_to_bv 64 0x24800) x17
            g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)).

  #[using="INP1 m1"] Lemma B_boundE : (0 <= B /\ B + L <= 2^64)%Z.
  Proof. exact (bytes_at_bound _ _ _ _ INP1). Qed.

  (* [comment removed for export] *)
  #[using="LL SHBR SHT SHB' SHB TLB TABB1 TL TAB1 INP1 FR1 LJ CEIL LO ST1 MI1 WM1 MU1 NP P tabb tab junk Clg"] Lemma setup : forall (i0 : Z) x1 x5 x6 x10 x12 x13 x14 x17 x28 x29 x30 x31,
    (0 <= i0 <= 3)%Z -> (23 <= L)%Z -> ((B + i0) mod 4 = 0)%Z ->
    evt rsegs POST (ATE 0x91300 x1 x5 x6 (Z_to_bv 64 (L - i0)) x10 (Z_to_bv 64 (B + i0)) x12 x13 x14 x17 x28 x29 x30 x31).
  Proof.
    intros until x31. intros Hi0 HL AL0.
    pose proof B_boundE as BB. pose proof LL as LL'. pose proof alloc_ceiling_num as ACV. pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof MU1 as MU. pose proof WM1 as WM. pose proof MI1 as MI. pose proof ST1 as ST. pose proof FR1 as FR.
    pose proof INP1 as INPc. pose proof TAB1 as TABc. pose proof TABB1 as TABBc. pose proof SHB as SHBc. pose proof SHT as SHTc. pose proof SHBR as SHBRc.
    clear MU1 WM1 MI1 ST1 FR1 INP1 TAB1 TABB1 SHB SHT SHBR.
    (* [comment removed for export] *)
    assert (ET : sh 149504 = 2147469568%Z) by reflexivity.
    assert (EBR : sh 150784 = 2147469728%Z) by reflexivity.
    pose proof (shpat_sh_boundL (Clg:=Clg) P NP ltac:(clear - P0; lia) ltac:(clear - P0 PLO PHI BB; lia) ltac:(clear - PCE; lia)) as SHPB. rewrite SHMAX_val in SHPB.
    assert (LT128 : Z.of_nat (length (repeat (Z_to_bv 8 0) 128)) = 128%Z) by reflexivity.
    assert (LT512 : Z.of_nat (length (repeat (Z_to_bv 8 0) 512)) = 512%Z) by reflexivity.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    rewrite (div20_form (L - i0)) by (clear - Hi0 HL LL'; lia).
    set (blks := ((L - i0) / 20)%Z).
    assert (Hb : (1 <= blks /\ 20 * blks <= L - i0)%Z) by (subst blks; clear - Hi0 HL; Z.div_mod_to_equations; lia).
    clearbody blks.
    (* [comment removed for export] *)
    zstep. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      eapply last_block with (q := i0) (B := B) (inp := inp) (tab := tab) (P := P) (NP := NP) (junk := junk) (m := m) (lo := lo);
        try eassumption.
      all: lazymatch goal with
           | |- (_ mod 2 ^ 64 = _)%Z => rewrite !unsigned_lit by (clear - Hi0 HL LL' Hb K BB; lia); rewrite Z.mod_small by (clear - Hi0 HL LL' Hb K BB; lia); clear - K; lia
           | |- _ => first [clear - Hi0 Hb K HL; lia | clear - AL0; Z.div_mod_to_equations; lia]
           end.
    - (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with FRx : rw_cells _ ?mx (bv_unsigned sp + -128) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
        replace (Z_to_bv 64 (blks * 20)) with (Z_to_bv 64 (20 * blks)) in FRx by (f_equal; lia) end.
      replace (Z_to_bv 64 (blks + -1)) with (Z_to_bv 64 (Z.of_nat (Z.to_nat (blks - 1)))) by (f_equal; clear - Hb; lia).
      eapply braid_outer with (n := Z.to_nat (blks - 1)) (c := i0) (i0 := i0) (blks := blks) (B := B) (inp := inp) (tab := tab) (tabb := tabb)
                               (P := P) (NP := NP) (m := m) (lo := lo);
        try eassumption.
      all: first [ clear - Hb K Hi0 HL LL'; lia | clear - AL0; Z.div_mod_to_equations; lia ].
  Qed.

  (* [comment removed for export] *)
  #[using="LL SHBR SHT SHB' SHB TLB TABB1 TL TAB1 INP1 FR1 LJ CEIL LO ST1 MI1 WM1 MU1 NP P tabb tab junk Clg"] Lemma align_loop : forall (k : nat) (i : Z) x1 x5 x6 x7 x13 x17 x28 x29 x30 x31,
    (4 - (B + i) mod 4 <= Z.of_nat k)%Z -> ((B + i) mod 4 <> 0)%Z -> (0 <= i)%Z -> (i + (4 - (B + i) mod 4) <= 3)%Z -> (23 <= L)%Z ->
    evt rsegs POST (ATE 0x91274 x1 x5 x6 x7 (Z_to_bv 64 (B + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (L - i)) x13 (Z_to_bv 64 1) x17 x28 x29 x30 x31).
  Proof.
    induction k as [|k IH]; intros until x31; intros Hk Hal Hi Hi3 HL.
    { exfalso. pose proof (Z.mod_pos_bound (B + i) 4 ltac:(lia)). lia. }
    pose proof B_boundE as BB. pose proof MI1 as MI. pose proof TL as TL'. pose proof LL as LL'. pose proof alloc_ceiling_num as ACV.
    pose proof SHB' as (PAL & P0 & PLO & PHI & PCE).
    pose proof (Z.mod_pos_bound (B + i) 4 ltac:(lia)) as Hm4.
    (* [comment removed for export] *)
    shadow_chkj SHB 1%Z 5%Z.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. zstep. tidx. tchk SHT 4%Z.
    (* [comment removed for export] *)
    cstep. zstep. zstep. zstep. gen_lxor. zstep.
    (* [comment removed for export] *)
    zstep. if_cases K1; zify_cond K1.
    all: lazymatch type of K1 with
         | _ = _ => exfalso; revert K1 Hi Hi3 HL LL' Hm4; clear; intros; rewrite ?Z.mod_small in K1 by lia; lia
         | _ => idtac
         end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; rewrite land3_mod in K2.
    all: lazymatch type of K2 with
         | _ = _ => (* [comment removed for export] *)
             zstep;
             replace (B + i + 1)%Z with (B + (i + 1))%Z in * by lia;
             replace (L - i + -1)%Z with (L - (i + 1))%Z by lia;
             apply setup; [ revert K2 Hal Hi Hi3 Hm4; clear; intros; Z.div_mod_to_equations; lia | exact HL
                          | revert K2 Hal Hi Hi3 Hm4; clear; intros; Z.div_mod_to_equations; lia ]
         | _ => (* [comment removed for export] *)
             replace (B + i + 1)%Z with (B + (i + 1))%Z in * by lia;
             replace (L - i + -1)%Z with (L - (i + 1))%Z by lia;
             apply IH; revert K2 Hk Hal Hi Hi3 Hm4 HL; clear; intros; try lia; Z.div_mod_to_equations; lia
         end.
  Qed.
End Entry.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Spec.
  Context {Clg : Ceiling}.

  (* [comment removed for export] *)
  Lemma crc32_z_ok :
    forall (B : Z) (inp : list byte) (lo : Z),
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (v : mem),
      a1 = Z_to_bv 64 B -> bv_unsigned a2 = Z.of_nat (length inp) ->
      (B = 0 \/ (bytes_at rsegs v B inp /\ shadowed LPA v B (Z.of_nat (length inp))))%Z ->
      cenv v ->
      stk rsegs v lo (bv_unsigned sp) -> (lo + CRC_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
      mem_inv rsegs v ->
      evt rsegs (leaf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (if Z.eqb B 0 then Some 0%Z else None) CRC_STACK lo v)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x91200) fc None v (seg_rom rsegs)).
  Proof.
    intros until v. intros A1 LEN HB CE ST LO CEIL MI. unfold CRC_STACK in *. subst a1.
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z v) as MU. pose proof (wmono_refl rsegs v) as WM.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a2) as R2; unfold inr64 in R2.
    pose proof alloc_ceiling_num as ACV.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    (* [comment removed for export] *)
    pose proof (map_cells_of_consts v (proj1 CE)) as MC. open_map_cells MC. clear Gmb Cmb Gme Cme Ghe Che.
    destruct (crc_tab_at v MI) as (tab & TL & TAB). destruct (crc_braid_at v MI) as (tabb & TLB & TABB).
    pose proof (crc_tab_shadow v CE) as SHT. pose proof (crc_braid_shadow v CE) as SHBR.
    assert (ET : sh 149504 = 2147469568%Z) by reflexivity.
    assert (EBR : sh 150784 = 2147469728%Z) by reflexivity.
    assert (LT128 : Z.of_nat (length (repeat (Z_to_bv 8 0) 128)) = 128%Z) by reflexivity.
    assert (LT512 : Z.of_nat (length (repeat (Z_to_bv 8 0) 512)) = 512%Z) by reflexivity.
    (* [comment removed for export] *)
    carve_frame 128%nat ST.
    do 14 zstep.
    (* [comment removed for export] *)
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. zstep.
      replace (bv_unsigned sp - 128)%Z with (bv_unsigned sp + -128)%Z in MU by lia.
      do 14 zstep.
      lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -128) _, STq : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        release_frame FRq STq (bv_unsigned sp) end.
      zstep. destruct (Z.eqb B 0).
      all: apply evt_done; hnf; repeat (lazymatch goal with |- ex _ => eexists end).
      all: try exact (Z_to_bv 64 0).   (* [comment removed for export] *)
      all: split; [reflexivity|]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
           first [assumption | replace (bv_unsigned sp - 128)%Z with (bv_unsigned sp + -128)%Z by lia; assumption].
    - (* [comment removed for export] *)
      destruct HB as [B0 | [INP SHD]]; [exfalso; subst B; apply K; reflexivity|].
      assert (NZ : B <> 0%Z) by (intros E; subst B; apply K; reflexivity).
      rewrite (proj2 (Z.eqb_neq B 0) NZ).
      pose proof (bytes_at_bound _ _ _ _ INP) as BB.
      assert (LL : (Z.of_nat (length inp) < 2^64)%Z) by (clear - BB NZ; lia).
      destruct SHD as (P & NP & SHB & PAL & P0 & PLO & PHI & PCE).
      pose proof (shpat_sh_boundL (Clg:=Clg) P NP P0 ltac:(clear - P0 PLO PHI BB; lia) PCE) as SHPB. rewrite SHMAX_val in SHPB.
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
        assert (INP1 : bytes_at rsegs mq B inp)
          by (eapply (bytes_at_munch LPA); [exact INP| exact MU| intros a Ha; cbn; clear - Ha PHI PCE CEIL LO; lia]);
        assert (SHB1 : bytes_at rsegs mq (sh P) (shpat NP))
          by (eapply (bytes_at_munch LPA); [exact SHB| exact MU| intros a Ha; cbn; clear - Ha SHPB CEIL LO ACV; lia])
      end.
      clear INP SHB.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
        lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -128) (CB 24 ?jk :: _) |- _ =>
          pose proof (proj1 (proj1 (proj1 FRq)) : length jk = 24%nat) as LJ;
          eapply sec_tail with (i := 0%Z) (B := B) (inp := inp) (tab := tab) (P := P) (NP := NP) (junk := jk) (m := v) (lo := lo) end;
          try eassumption; try (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption); clear - BB LEN K1 R2; try lia.
      + (* [comment removed for export] *)
        zstep. zstep. if_cases K2; zify_cond K2; rewrite land3_mod in K2.
        * (* [comment removed for export] *)
          zstep.
          replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
          replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 0)) by (f_equal; lia).
          lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -128) (CB 24 ?jk :: _) |- _ =>
            pose proof (proj1 (proj1 (proj1 FRq)) : length jk = 24%nat) as LJ;
            eapply setup with (B := B) (inp := inp) (tab := tab) (tabb := tabb) (P := P) (NP := NP) (junk := jk) (m := v) (lo := lo) end;
            try eassumption; try (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption).
          all: first [ clear - BB LEN K1 K2 R2; rewrite ?Z.add_0_r; try lia; Z.div_mod_to_equations; lia | idtac ].
        * (* [comment removed for export] *)
          zstep. zstep.
          replace a2 with (Z_to_bv 64 (Z.of_nat (length inp) - 0)) by (rewrite Z.sub_0_r, <- LEN; apply Z_to_bv_bv_unsigned).
          replace (Z_to_bv 64 B) with (Z_to_bv 64 (B + 0)) by (f_equal; lia).
          lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -128) (CB 24 ?jk :: _) |- _ =>
            pose proof (proj1 (proj1 (proj1 FRq)) : length jk = 24%nat) as LJ;
            eapply align_loop with (k := 4%nat) (B := B) (inp := inp) (tab := tab) (tabb := tabb) (P := P) (NP := NP) (junk := jk) (m := v) (lo := lo) end;
            try eassumption; try (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption).
          all: first [ clear - BB LEN K1 K2 R2; rewrite ?Z.add_0_r in *; pose proof (Z.mod_pos_bound B 4 ltac:(lia)); try lia; Z.div_mod_to_equations; lia | idtac ].
  Qed.

  (* [comment removed for export] *)
  Theorem crc32_ok : crc32_stmt.
  Proof.
    intros B inp lo. intros until v. intros A1 LEN HB CE ST LO CEIL MI.
    pose proof (munch_refl [(bv_unsigned sp - CRC_STACK, bv_unsigned sp)]%Z v) as MU. pose proof (wmono_refl rsegs v) as WM.
    pose proof (zr_word a2) as R2; unfold inr64 in R2.
    unfold crc32_entry. do 3 zstep.
    eapply crc32_z_ok; try eassumption.
    rewrite unsigned_lit by (clear - R2; Z.div_mod_to_equations; lia). exact LEN.
  Qed.
End Spec.
