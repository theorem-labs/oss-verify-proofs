(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpii0.

Module AIcpwd0.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import AIcpm9j.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@Creal; @Ggot]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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

Definition set_shadow_00_entry : Z := 0x5a940.
Definition set_shadow_f8_entry : Z := 0x5aa60.

Definition set_shadow_cells (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa8b90 [C8 (Z_to_bv 64 0xaaa18)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)].     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition set_shadow_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) (repeat (Z_to_bv 8 v) (Z.to_nat (bv_unsigned a1)))].

Lemma set_shadow_00_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk] ->
  set_shadow_cells m ->
  mem_inv rsegs m ->
  evt rsegs (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 0 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a940) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST [Ggot Creal] MI.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  do 5 zstep.
  zstep. call memset_spec. 1:{ exact DST. } 1:{ eassumption. }
  change ((bv_unsigned (Z_to_bv 64 0)) mod 256)%Z with 0%Z in POST.
  finish.
Qed.

Lemma set_shadow_f8_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte),
  rw_cells rsegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a1)) junk] ->
  set_shadow_cells m ->
  mem_inv rsegs m ->
  evt rsegs (set_shadow_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 248 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5aa60) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros DST [Ggot Creal] MI.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a1)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  do 5 zstep.
  zstep. call memset_spec. 1:{ exact DST. } 1:{ eassumption. }
  change ((bv_unsigned (Z_to_bv 64 248)) mod 256)%Z with 248%Z in POST.
  finish.
Qed.
End AIcpwd0.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpya4 AIcp3q7 AIcp2kv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2 AIcpinq.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpii0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpwd0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpinq.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.

Module AIcp7wx.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@AFA; @AFB; @LOLE'; @CEIL; @CV; @Hc; @Hj; @SB; @I31; @K2; @ESL; @H; @H0; @HS2; @ESF; @RB; @H4; @H5; @K3; @SFB; @LSI; @RSI; @NGA; @A0R; @SPR; @SHhi; @LBR; @K; @QH4; @QH3; @QH2; @QH1; @SHBhi; @LB; @HS1; @H14; @H15; @NGB; @H9; @H10; @K0; @K1; @SEPB; @SEPA; @K4; @LBA; @H19; @H20; @K8])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (lo : Z)
            (i : nat) (c1 c2 : Z).
  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation I := (Z.of_nat i).
  Notation POST := (strcmp_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs (char_cmp c1 c2) lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -104)
                          [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2192) [CB 2088 fjunk]).
  Hypothesis LOLE : (lo + STRCMP_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis C1R : (0 <= c1 < 256)%Z.
  Hypothesis C2R : (0 <= c2 < 256)%Z.
  Hypothesis I31 : (I + 1 <= 2^31)%Z.
  Notation SEPAt := ((A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPBt := ((B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z) (only parsing).

  Section Facts.
    Variables (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word).
    Notation LBAt := ((lastbA = 0 \/ ((I + A) mod 8 < lastbA <= 7))%Z) (only parsing).
    Notation LBBt := ((lastbB = 0 \/ ((I + B) mod 8 < lastbB <= 7))%Z) (only parsing).
    Hypothesis AFA : (0 <= A /\ A + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis AFB : (0 <= B /\ B + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis IRA : inmem_range A (I + 1).
    Hypothesis IRB : inmem_range B (I + 1).
    Hypothesis NGA : ((I + A) / 8 - A / 8 = Z.of_nat ngA)%Z.
    Hypothesis NGB : ((I + B) / 8 - B / 8 = Z.of_nat ngB)%Z.
    Hypothesis LSI : (I + 1 <= Z.of_nat (length ls))%Z.
    Hypothesis RSI : (I + 1 <= Z.of_nat (length rs))%Z.

    Section Phase1.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis LS1 : bytes_at rsegs m1 A ls.
      Hypothesis RS1 : bytes_at rsegs m1 B rs.
      Hypothesis CI : ro_cells rsegs m1 0xb5898 [C1 (Z_to_bv 8 1)].
      Hypothesis Gcf : ro_cells rsegs m1 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)].
      Hypothesis Cssc : ro_cells rsegs m1 0x1467dd [C1 (Z_to_bv 8 0)].
      Hypothesis Cisc : ro_cells rsegs m1 0x1467e2 [C1 (Z_to_bv 8 1)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHB1 : bytes_at rsegs m1 (B / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]).
      Hypothesis QBB1 : bytes_at rsegs m1 (sha B - sha B mod 8) (le8 w1B).
      Hypothesis QBB2 : bytes_at rsegs m1 (sha (I + B) - sha (I + B) mod 8) (le8 w2B).

      Hypothesis SHA1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]).
      Hypothesis QBA1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1A).
      Hypothesis QBA2 : bytes_at rsegs m1 (sha (I + A) - sha (I + A) mod 8) (le8 w2A).

      Section SlowA.
        Variables (sf sl : Z) (x1 x5 x6 x7 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31 : word).
        Hypothesis SEPA : SEPAt. Hypothesis SEPB : SEPBt. Hypothesis LBB : LBBt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngA)%Z.
        Notation AT pc x10 x12 x13 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
                   x10 (Z_to_bv 64 sl) x12 x13 x14 x15 x16 x17 a0 ra (Z_to_bv 64 (I + 1)) (Z_to_bv 64 I) (Z_to_bv 64 (I + 1)) s7
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 c1) (Z_to_bv 64 c2) (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="LBB SEPB SEPA QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI NGB IRB AFB AFA w2B w1B lastbB ngB I31 C2R C1R CEIL LOLE Clg"] Lemma sc_slowA_end : forall x10 x13, evt rsegs POST (AT 0x481d0 x10 (Z_to_bv 64 0) x13).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply sc_p2; try eassumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF LBB SEPB SEPA SHA1 QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI NGB IRB AFB AFA w2B w1B lastbB lastbA ngB I31 C2R C1R CEIL LOLE Clg"] Lemma sc_slowA_loop : forall (c : nat) (j : Z) x10 x13,
          Z.to_nat (Z.of_nat ngA - j) = c -> (0 <= j < Z.of_nat ngA)%Z -> x10 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x481c0 x10 (Z_to_bv 64 0) x13).
        Proof.
          induction c as [|c IH]; intros j x10 x13 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHA1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHA1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngA lastbA (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngA)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply sc_slowA_end.
        Qed.
      End SlowA.

      (* [comment removed for export] *)
      #[using="QBA2 QBA1 SHA1 QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI LSI NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA I31 C2R C1R CEIL LOLE Clg"] Lemma sc_p1 : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x28 x29 x30 x31,
        SEPAt -> SEPBt -> LBAt -> LBBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
                   x10 x11 x12 x13 x14 x15 x16 x17 a0 ra (Z_to_bv 64 (I + 1)) x21 x22 s7
                   (Z_to_bv 64 0x1466e8) (Z_to_bv 64 c1) (Z_to_bv 64 c2) (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
            F (Z_to_bv 64 0x47f28) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPA SEPB LBA LBB. pose proof LOLE as LOLE'. unfold STRCMP_ICPT_STACK in LOLE'.
        unfold STRCMP_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
        pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
        pose proof (bytes_at_bound _ _ _ _ LS1) as LB. pose proof (bytes_at_bound _ _ _ _ RS1) as RB.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (I + A) - sha (I + A) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha B - sha B mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (I + B) - sha (I + B) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHA1 as SH. remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHB1 as SHB. remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
        assert (SHBhi : (B / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
        { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBA1 as QB1. pose proof QBA2 as QB2. pose proof QBB1 as QB3. pose proof QBB2 as QB4.
        zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
        zstep. zstep. zstep.
        zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          zstep. zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRA
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngA, lastbA; subst sbs; split;
                 [replace (A + (I + 1) - 1)%Z with (I + A)%Z by lia; exact NGA| split; [exact SH| replace (A + (I + 1) - 1)%Z with (I + A)%Z by lia; exact LBA]]
            | |- _ => rewrite ?unsigned_lit by lia; first [ lazymatch goal with |- context [Z.land] => mlia end | lia | mlia ]   (* [comment removed for export] *)
            end).
          zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
          subst sbs sbsB. eapply sc_p2; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (I + A) 3 <= I + A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbA < 128)%Z) by (hs_lbr lastbA).
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ngA) (Z_to_bv 8 lastbA)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (I + A) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngA lastbA ngA), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (I + A) lastbA) by (first [exact LBA | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (I + A) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngA)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsB.
            zstep. if_cases K8; zify_cond K8.
            * eapply sc_slowA_end; eassumption.
            * eapply sc_slowA_loop with (j := 0%Z); try eassumption; try reflexivity;
              try (lazymatch goal with |- @eq word _ _ => fail | |- @eq (bv _) _ _ => fail | _ => lia end).   (* [comment removed for export] *)
              f_equal; lia.
          + subst sbs sbsB. eapply sc_p2; try eassumption.
      Qed.
    End Phase1.
  End Facts.
End S.
End AIcp7wx.

Module AIcp8zl.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.RA_s5ib.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcppc0 AIcpzt2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcppc0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma strchr_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  let A := bv_unsigned a0 in let c := ((bv_unsigned a1) mod 256)%Z in
  bytes_at rsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m -> strchr_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRCHR_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= lo \/ bv_unsigned sp <= A)%Z ->
  (c <> 0)%Z -> (0 < A)%Z ->
  (Z.of_nat (length str) + 1 <= 2^31)%Z ->
  range_ok m A (Z.of_nat (length str) + 1) ->
  evt rsegs (strchr_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 c str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x478e8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros STR NONUL PAD MI CELLS ST LOLE CEIL SEP CNZ APOS L31 RA.
  pose proof LOLE as LOLE'. unfold STRCHR_ICPT_STACK in LOLE'.
  (first [ dand6 CELLS as CI Creal Gcf Cssc Cisc MC | destruct CELLS as (CI & Creal & Gcf & Cssc & Cisc & MC) ]). unfold asan_inited_cell in CI. pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned sp - STRCHR_ICPT_STACK, bv_unsigned sp)]%Z m) as MU. unfold STRCHR_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
  pose proof (bytes_at_bound _ _ _ _ STR) as LB. rewrite length_app in LB. cbn [length] in LB.
  pose proof SEP as SEP'. rewrite length_app in SEP'. cbn [length] in SEP'.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (Z.mod_pos_bound (bv_unsigned a1) 256 ltac:(lia)) as CB.
  set (c := ((bv_unsigned a1) mod 256)%Z) in *.
  set (i := strchrnul_idx c str). pose proof (strchrnul_idx_le c str) as IL. fold i in IL.
  (* [comment removed for export] *)
  (first [ pose proof ((range_ok_prefix m _ _ (Z.of_nat i + 1) RA ltac:(lia))) as dR_2; dand4 dR_2 as IR SOK QW1 QW2 | pose proof (range_ok_prefix m _ _ (Z.of_nat i + 1) RA ltac:(lia)) as (IR & SOK & QW1 & QW2) ]).
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat i + 1 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  replace (bv_unsigned a0 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a0)%Z in QW2 by lia.
  destruct (mapped8_le8 _ _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
  destruct (mapped8_le8 _ _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (Z.of_nat i + bv_unsigned a0) - sha (Z.of_nat i + bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  (first [ dex2 SOK as ng lastb; dand3 SOK as NG SH LBl | dand5 SOK as ng lastb NG SH LBl | destruct SOK as (ng & lastb & NG & SH & LBl) ]).
  replace (bv_unsigned a0 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a0)%Z in NG, LBl by lia.
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (SI : (Z.of_nat i + 1 <= Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)))%Z) by (rewrite length_app; cbn [length]; lia).
  (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  freeze STR; freeze CI; freeze Creal; freeze Gcf; freeze Cssc; freeze Cisc; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
  freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SH; freeze QB1; freeze QB2.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  carve_frame 72%nat ST. carve_frame 2072%nat ST.
  do 12 zstep.
  thaw STR MUp WM; thaw CI MUp WM; thaw Creal MUp WM; thaw Gcf MUp WM; thaw Cssc MUp WM; thaw Cisc MUp WM;
  thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SH MUp WM; thaw QB1 MUp WM; thaw QB2 MUp WM.
  clear MUp.
  zstep. zstep.
  zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
  zstep. if_cases K0; zify_cond K0. { deadK K0. }
  zstep. call_lit tryinit_spec by (idtac;
    lazymatch goal with
    | |- asan_inited_cell _ => exact CI
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
    | |- mem_inv _ _ => eassumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  zstep. zstep. zstep. zstep. zstep.
  zstep. call_lit strchr_spec by (idtac;
    lazymatch goal with
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
    | |- bytes_at _ _ _ _ => exact STR
    | |- ~ In _ _ => exact NONUL
    | |- mem_inv _ _ => eassumption
    | |- (_ mod 256 <> 0)%Z => exact CNZ
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  unfold strchr_val. fold c. replace (c =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact CNZ).
  zstep. if_cases K1; zify_cond K1. { deadK K1. }
  zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K2; zify_cond K2. { deadK K2. }
  zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
  zstep. if_cases K3; zify_cond K3. { deadK K3. }
  subst sbs.
  assert (RES : (strchr_res (bv_unsigned a0) c str = 0%Z /\ i = length str)
              \/ (strchr_res (bv_unsigned a0) c str = bv_unsigned a0 + Z.of_nat i /\ (i < length str)%nat)%Z).
  { unfold strchr_res. subst i. unfold strchrnul_idx. destruct (find_byte c str) as [k|] eqn:E.
    - right. (first [ pose proof ((find_byte_Some _ _ _ E)) as dR_4; dand3 dR_4 as Hk _ _ | destruct (find_byte_Some _ _ _ E) as (Hk & _ & _) ]). split; [reflexivity| exact Hk].
    - left. split; reflexivity. }
  destruct RES as [[RV Hi] | [RV Hi]]; rewrite RV.
  - (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
    zstep. zstep.
    zstep. call istrlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ eassumption. }
    zstep. zstep.
    rewrite <- Hi.
    eapply sr_phase; try eassumption; try reflexivity; try lia.
  - (* [comment removed for export] *)
    zstep. if_cases K4; zify_cond K4. { deadK K4. }
    zstep. zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (Z.of_nat i) by lia.
    eapply sr_phase; try eassumption; try reflexivity; try lia.
Qed.

End CEIL.
End AIcp8zl.

Module AIcpa09.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpzt2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpzt2.AIcpzur OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcp7wx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dl_first | tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strcmp_sign (s1 s2 : list byte) : Z :=
  match strcmp_stop (s1 ++ [Z_to_bv 8 0]) (s2 ++ [Z_to_bv 8 0]) with
  | Some (_, c1, c2) => char_cmp c1 c2
  | None => 0%Z
  end.

Lemma char_cmp_zero_iff : forall c1 c2, char_cmp c1 c2 = 0%Z <-> c1 = c2.
Proof.
  intros c1 c2. unfold char_cmp.
  destruct (Z.ltb_spec0 c1 c2); [split; [discriminate| lia]|].
  destruct (Z.ltb_spec0 c2 c1); [split; [discriminate| lia]|]. split; [lia| reflexivity].
Qed.

Lemma strcmp_stop_cstr_any : forall s1 s2,
  ~ In (Z_to_bv 8 0) s1 -> ~ In (Z_to_bv 8 0) s2 ->
  exists i c1 c2, (forall j1 j2, strcmp_stop (s1 ++ Z_to_bv 8 0 :: j1) (s2 ++ Z_to_bv 8 0 :: j2) = Some (i, c1, c2))
    /\ ((i <= length s1)%nat /\ (i <= length s2)%nat /\ (0 <= c1 < 256)%Z /\ (0 <= c2 < 256)%Z)
    /\ (char_cmp c1 c2 = 0%Z <-> s1 = s2).
Proof.
  induction s1 as [|x s1 IH]; intros s2 N1 N2.
  - destruct s2 as [|y s2].
    + exists 0%nat, 0%Z, 0%Z. split; [intros; reflexivity|]. split; [cbn; lia|]. rewrite char_cmp_zero_iff. split; [reflexivity| lia].
    + assert (Y : bv_unsigned y <> 0%Z).
      { intros E. apply N2. left. apply bv_eq. rewrite E. reflexivity. }
      pose proof (bv_unsigned_in_range _ y) as RY. unfold bv_modulus in RY. change (2 ^ Z.of_N 8)%Z with 256%Z in RY.
      exists 0%nat, 0%Z, (bv_unsigned y). split; [intros; reflexivity|]. split; [cbn; lia|].
      rewrite char_cmp_zero_iff. split; [lia| discriminate].
  - assert (X : bv_unsigned x <> 0%Z).
    { intros E. apply N1. left. apply bv_eq. rewrite E. reflexivity. }
    pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX. change (2 ^ Z.of_N 8)%Z with 256%Z in RX.
    assert (X0 : (bv_unsigned x =? 0)%Z = false) by (apply Z.eqb_neq; exact X).
    destruct s2 as [|y s2].
    + exists 0%nat, (bv_unsigned x), 0%Z. split.
      { intros. cbn -[Z.eqb]. rewrite X0. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z. rewrite X0. reflexivity. }
      split; [cbn; lia|]. rewrite char_cmp_zero_iff. split; [lia| discriminate].
    + pose proof (bv_unsigned_in_range _ y) as RY. unfold bv_modulus in RY. change (2 ^ Z.of_N 8)%Z with 256%Z in RY.
      destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|NE].
      * (first [ pose proof ((IH s2)) as dR_1; dex3 dR_1 as i c1 c2; dand3 dR_1 as Hs (L1 & L2 & R1 & R2) Hiff | pose proof ((IH s2)) as dR_1; dand6 dR_1 as i c1 c2 Hs (L1 & L2 & R1 & R2) Hiff | destruct (IH s2) as (i & c1 & c2 & Hs & (L1 & L2 & R1 & R2) & Hiff) ]).
        { intros Hin. apply N1. right. exact Hin. } { intros Hin. apply N2. right. exact Hin. }
        exists (S i), c1, c2. split.
        { intros j1 j2. cbn -[Z.eqb]. rewrite X0. rewrite (proj2 (Z.eqb_eq _ _) E). cbn. rewrite Hs. reflexivity. }
        split; [cbn; lia|]. rewrite Hiff. split.
        -- intros ->. f_equal. apply bv_eq. exact E.
        -- intros Heq. injection Heq as _ H2. exact H2.
      * exists 0%nat, (bv_unsigned x), (bv_unsigned y). split.
        { intros j1 j2. cbn -[Z.eqb]. rewrite X0.
          replace (bv_unsigned x =? bv_unsigned y)%Z with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. }
        split; [cbn; lia|]. rewrite char_cmp_zero_iff. split; [lia|].
        intros Heq. injection Heq as H1 _. subst. lia.
Qed.

(* [comment removed for export] *)
Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (lo : Z)
            (i : nat) (c1 c2 : Z).
  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation I := (Z.of_nat i).
  Notation POST := (strcmp_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs (char_cmp c1 c2) lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -104)
                          [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2192) [CB 2088 fjunk]).
  Hypothesis LOLE : (lo + STRCMP_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis C1R : (0 <= c1 < 256)%Z.
  Hypothesis C2R : (0 <= c2 < 256)%Z.
  Hypothesis I31 : (I + 1 <= 2^31)%Z.
  Notation SEPAt := ((A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPBt := ((B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z) (only parsing).

  Section Facts.
    Variables (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word).
    Notation LBAt := ((lastbA = 0 \/ ((I + A) mod 8 < lastbA <= 7))%Z) (only parsing).
    Notation LBBt := ((lastbB = 0 \/ ((I + B) mod 8 < lastbB <= 7))%Z) (only parsing).
    Hypothesis AFA : (0 <= A /\ A + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis AFB : (0 <= B /\ B + I + 1 + 8 <= 0x800000000000)%Z.
    Hypothesis IRA : inmem_range A (I + 1).
    Hypothesis IRB : inmem_range B (I + 1).
    Hypothesis NGA : ((I + A) / 8 - A / 8 = Z.of_nat ngA)%Z.
    Hypothesis NGB : ((I + B) / 8 - B / 8 = Z.of_nat ngB)%Z.
    Hypothesis LSI : (I + 1 <= Z.of_nat (length ls))%Z.
    Hypothesis RSI : (I + 1 <= Z.of_nat (length rs))%Z.

    Section Loop.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis LS1 : bytes_at rsegs m1 A ls.
      Hypothesis RS1 : bytes_at rsegs m1 B rs.
      Hypothesis CI : ro_cells rsegs m1 0xb5898 [C1 (Z_to_bv 8 1)].
      Hypothesis Gcf : ro_cells rsegs m1 0xa8b60 [C8 (Z_to_bv 64 0x1466e8)].
      Hypothesis Cssc : ro_cells rsegs m1 0x1467dd [C1 (Z_to_bv 8 0)].
      Hypothesis Cisc : ro_cells rsegs m1 0x1467e2 [C1 (Z_to_bv 8 1)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHB1 : bytes_at rsegs m1 (B / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]).
      Hypothesis QBB1 : bytes_at rsegs m1 (sha B - sha B mod 8) (le8 w1B).
      Hypothesis QBB2 : bytes_at rsegs m1 (sha (I + B) - sha (I + B) mod 8) (le8 w2B).

      Hypothesis SHA1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]).
      Hypothesis QBA1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1A).
      Hypothesis QBA2 : bytes_at rsegs m1 (sha (I + A) - sha (I + A) mod 8) (le8 w2A).
      Hypothesis STOP : strcmp_stop ls rs = Some (i, c1, c2).

      Notation AT pc j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 :=
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a1
                 x10 x11 x12 x13 x14 x15 x16 x17 a0 ra j s5 s6 s7 s8 x25 x26 (Z_to_bv 64 (bv_unsigned sp + -2176)) x28 x29 x30 x31)
            F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

      (* [comment removed for export] *)
      #[using="QBA2 QBA1 SHA1 QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI LSI NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA I31 C2R C1R CEIL LOLE Clg"] Lemma sc_exit : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
        SEPAt -> SEPBt -> LBAt -> LBBt ->
        evt rsegs POST (AT 0x47f18 (Z_to_bv 64 (I + 1)) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 c1) (Z_to_bv 64 c2) x28 x29 x30 x31).
      Proof.
        intros until x31. intros SEPA SEPB LBA LBB. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
        zstep. if_cases K; zify_cond K. { exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. lia. }
        eapply sc_p1; try eassumption.
      Qed.

      (* [comment removed for export] *)
      #[using="STOP QBA2 QBA1 SHA1 QBB2 QBB1 SHB1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Cisc Cssc Gcf CI RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk RSI LSI NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA I31 C2R C1R CEIL LOLE Clg"] Lemma sc_loop : forall (c j : nat) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31,
        (i - j = c)%nat -> (j <= i)%nat ->
        SEPAt -> SEPBt -> LBAt -> LBBt ->
        evt rsegs POST (AT 0x47efc (Z_to_bv 64 (Z.of_nat j)) x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31).
      Proof.
        induction c as [|c IH]; intros j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 Hc Hj SEPA SEPB LBA LBB;
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
          pose proof (bytes_at_bound _ _ _ _ LS1) as LB; pose proof (bytes_at_bound _ _ _ _ RS1) as RB;
          destruct (strcmp_stop_nth _ _ _ _ _ STOP) as [(a & b & Ha & Hb & Hca & Hcb & Hend) Hpre].
        - (* [comment removed for export] *)
          assert (E : j = i) by lia. subst j.
          pose proof (u8ro_read rsegs m1 A ls I a (Z_to_bv 64 (A + I)) LS1 ltac:(rewrite Nat2Z.id; exact Ha) ltac:(lia) eq_refl) as RD1.
          pose proof (u8ro_read rsegs m1 B rs I b (Z_to_bv 64 (B + I)) RS1 ltac:(rewrite Nat2Z.id; exact Hb) ltac:(lia) eq_refl) as RD2.
          pose proof (bv_unsigned_in_range _ a) as AR. pose proof (bv_unsigned_in_range _ b) as BR.
          unfold bv_modulus in AR, BR. change (2 ^ Z.of_N 8)%Z with 256%Z in AR, BR.
          zstep. zstep. cbv beta. zstep. zstep. cbv beta. zstep.
          rewrite Hca, Hcb.
          zstep. if_cases K1; zify_cond K1.
          + apply sc_exit; assumption.
          + zstep. if_cases K2; zify_cond K2. { exfalso. lia. }
            apply sc_exit; assumption.
        - (* [comment removed for export] *)
          (first [ pose proof ((Hpre j ltac:(lia))) as dR_3; dex2 dR_3 as a' b'; dand4 dR_3 as Ha' Hb' Heq Hnz | pose proof ((Hpre j ltac:(lia))) as dR_3; dand6 dR_3 as a' b' Ha' Hb' Heq Hnz | destruct (Hpre j ltac:(lia)) as (a' & b' & Ha' & Hb' & Heq & Hnz) ]).
          pose proof (u8ro_read rsegs m1 A ls (Z.of_nat j) a' (Z_to_bv 64 (A + Z.of_nat j)) LS1 ltac:(rewrite Nat2Z.id; exact Ha') ltac:(lia) eq_refl) as RD1.
          pose proof (u8ro_read rsegs m1 B rs (Z.of_nat j) b' (Z_to_bv 64 (B + Z.of_nat j)) RS1 ltac:(rewrite Nat2Z.id; exact Hb') ltac:(lia) eq_refl) as RD2.
          pose proof (bv_unsigned_in_range _ a') as AR. pose proof (bv_unsigned_in_range _ b') as BR.
          unfold bv_modulus in AR, BR. change (2 ^ Z.of_N 8)%Z with 256%Z in AR, BR.
          pose proof (nth_error_lt _ _ _ Ha') as JL.
          zstep. zstep. cbv beta. zstep. zstep. cbv beta. zstep.
          zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
          zstep. if_cases K2; zify_cond K2. 2:{ exfalso. lia. }
          replace (Z.of_nat j + 1)%Z with (Z.of_nat (S j)) by lia.
          eapply (IH (S j)); try assumption; lia.
      Qed.
    End Loop.
  End Facts.
End S.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma strcmp_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str1 str2 j1 j2 : list byte) (lo : Z),
  let A := bv_unsigned a0 in let B := bv_unsigned a1 in
  let ls := str1 ++ Z_to_bv 8 0 :: j1 in let rs := str2 ++ Z_to_bv 8 0 :: j2 in
  bytes_at rsegs m A ls -> bytes_at rsegs m B rs ->
  ~ In (Z_to_bv 8 0) str1 -> ~ In (Z_to_bv 8 0) str2 ->
  mem_inv rsegs m -> strcmp_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + STRCMP_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z ->
  (B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z ->
  (Z.of_nat (length str1) + 1 <= 2^31)%Z ->
  range_ok m A (Z.of_nat (length str1) + 1) -> range_ok m B (Z.of_nat (length str2) + 1) ->
  evt rsegs (strcmp_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs (strcmp_sign str1 str2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x478e4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros LS RS N1 N2 MI CELLS ST LOLE CEIL SEPA SEPB L31 RA RB.
  pose proof LOLE as LOLE'. unfold STRCMP_ICPT_STACK in LOLE'.
  pose proof CELLS as CELLS'. open_strcmp_cells CELLS'. clear CELLS MC.
  pose proof (munch_refl [(bv_unsigned sp - STRCMP_ICPT_STACK, bv_unsigned sp)]%Z m) as MU. unfold STRCMP_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
  pose proof (bytes_at_bound _ _ _ _ LS) as LB. pose proof (bytes_at_bound _ _ _ _ RS) as RB0.
  rewrite length_app in LB, RB0. cbn [length] in LB, RB0.
  pose proof SEPA as SEPA'. pose proof SEPB as SEPB'. rewrite length_app in SEPA', SEPB'. cbn [length] in SEPA', SEPB'.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  (first [ pose proof ((strcmp_stop_cstr_any str1 str2 N1 N2)) as dR_4; dex3 dR_4 as i c1 c2; dand3 dR_4 as STOPf (L1 & L2 & C1R & C2R) Hiff | pose proof ((strcmp_stop_cstr_any str1 str2 N1 N2)) as dR_4; dand6 dR_4 as i c1 c2 STOPf (L1 & L2 & C1R & C2R) Hiff | destruct (strcmp_stop_cstr_any str1 str2 N1 N2) as (i & c1 & c2 & STOPf & (L1 & L2 & C1R & C2R) & Hiff) ]).
  pose proof (STOPf j1 j2) as STOP.
  replace (strcmp_sign str1 str2) with (char_cmp c1 c2) by (unfold strcmp_sign; rewrite (STOPf [] []); reflexivity).
  (* [comment removed for export] *)
  (first [ pose proof ((range_ok_prefix m _ _ (Z.of_nat i + 1) RA ltac:(lia))) as dR_5; dand4 dR_5 as IRA SOKA QWA1 QWA2 | pose proof (range_ok_prefix m _ _ (Z.of_nat i + 1) RA ltac:(lia)) as (IRA & SOKA & QWA1 & QWA2) ]).
  (first [ pose proof ((range_ok_prefix m _ _ (Z.of_nat i + 1) RB ltac:(lia))) as dR_6; dand4 dR_6 as IRB SOKB QWB1 QWB2 | pose proof (range_ok_prefix m _ _ (Z.of_nat i + 1) RB ltac:(lia)) as (IRB & SOKB & QWB1 & QWB2) ]).
  assert (AFA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat i + 1 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
  assert (AFB : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + Z.of_nat i + 1 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
  replace (bv_unsigned a0 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a0)%Z in QWA2 by lia.
  replace (bv_unsigned a1 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a1)%Z in QWB2 by lia.
  destruct (mapped8_le8 _ _ QWA1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1A QBA1].
  destruct (mapped8_le8 _ _ QWA2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2A QBA2].
  destruct (mapped8_le8 _ _ QWB1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1B QBB1].
  destruct (mapped8_le8 _ _ QWB2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2B QBB2].
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (Z.of_nat i + bv_unsigned a0) - sha (Z.of_nat i + bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH3 : (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH4 : (sha (Z.of_nat i + bv_unsigned a1) - sha (Z.of_nat i + bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  (first [ dex2 SOKA as ngA lastbA; dand3 SOKA as NGA SHA LBA | dand5 SOKA as ngA lastbA NGA SHA LBA | destruct SOKA as (ngA & lastbA & NGA & SHA & LBA) ]). (first [ dex2 SOKB as ngB lastbB; dand3 SOKB as NGB SHB LBB | dand5 SOKB as ngB lastbB NGB SHB LBB | destruct SOKB as (ngB & lastbB & NGB & SHB & LBB) ]).
  replace (bv_unsigned a0 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a0)%Z in NGA, LBA by lia.
  replace (bv_unsigned a1 + (Z.of_nat i + 1) - 1)%Z with (Z.of_nat i + bv_unsigned a1)%Z in NGB, LBB by lia.
  remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbsA eqn:EsbsA.
  remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
  assert (SHAhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbsA) <= 0x100080000000)%Z).
  { subst sbsA. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (SHBhi : (bv_unsigned a1 / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
  { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  freeze LS; freeze RS; freeze CI; freeze Gcf; freeze Cssc; freeze Cisc; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
  freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SHA; freeze SHB; freeze QBA1; freeze QBA2; freeze QBB1; freeze QBB2.
  pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MUp.
  carve_frame 104%nat ST. carve_frame 2088%nat ST.
  do 16 zstep.
  thaw LS MUp WM; thaw RS MUp WM; thaw CI MUp WM; thaw Gcf MUp WM; thaw Cssc MUp WM; thaw Cisc MUp WM;
  thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SHA MUp WM; thaw SHB MUp WM; thaw QBA1 MUp WM; thaw QBA2 MUp WM; thaw QBB1 MUp WM; thaw QBB2 MUp WM.
  clear MUp.
  do 3 zstep.
  zstep. call_lit tryinit_spec by (idtac;
    lazymatch goal with
    | |- asan_inited_cell _ => exact CI
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
    | |- mem_inv _ _ => eassumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
  do 3 zstep.
  subst sbsA sbsB.
  assert (LSI : (Z.of_nat i + 1 <= Z.of_nat (length (str1 ++ Z_to_bv 8 0 :: j1)))%Z) by (rewrite length_app; cbn [length]; lia).
  assert (RSI : (Z.of_nat i + 1 <= Z.of_nat (length (str2 ++ Z_to_bv 8 0 :: j2)))%Z) by (rewrite length_app; cbn [length]; lia).
  assert (I31 : (Z.of_nat i + 1 <= 2^31)%Z) by lia.
  change (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat 0)).
  eapply (sc_loop _ _ _ _ _ _ a0 a1); try eassumption; try reflexivity;
    lazymatch goal with
    | |- (_ <= _)%Z => lia | |- (_ < _)%Z => lia | |- (_ <= _)%nat => lia | |- (_ /\ _) => lia
    | |- ?g => idtac "LEFTOVER" g
    end.
Qed.

End CEIL.
End AIcpa09.

Module AIcpisb.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp3q7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
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
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LEN; @AFS; @AFD; @Hc; @Hj; @SB; @ESL; @A1R; @A0R; @HS2; @ESF; @LOLE'; @A2R; @CEIL; @SFB; @CV; @SPR; @K3; @LBR; @K; @H; @K1; @N32; @SEPD; @K4; @HS1; @LBS; @LB1; @SHhi; @K8])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)

Section Proofs2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte) (lo : Z).
  Notation A := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation N := (bv_unsigned a2).
  Notation POST := (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).
  (* [comment removed for export] *)
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -72)
                          [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2072 fjunk]).
  Hypothesis LOLE : (lo + ASAN_MEMCPY_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LEN : length src = Z.to_nat N.
  Hypothesis N32 : (N < 2^32)%Z.
  (* [comment removed for export] *)
  Notation SEPDt := ((A + N <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPSt := ((S + N <= lo \/ bv_unsigned sp <= S)%Z) (only parsing).
  Notation DISJt := ((S + N <= A \/ A + N <= S)%Z) (only parsing).

  Section Facts.
    (* [comment removed for export] *)
    Variables (ngS ngD : nat) (lastbS lastbD : Z) (w1S w2S w1D w2D : word).
    Notation LBSt := ((lastbS = 0 \/ ((S + N - 1) mod 8 < lastbS <= 7))%Z) (only parsing).
    Notation LBDt := ((lastbD = 0 \/ ((A + N - 1) mod 8 < lastbD <= 7))%Z) (only parsing).
    Hypothesis AFS : (0 <= S /\ S + N + 8 <= 0x800000000000)%Z.
    Hypothesis AFD : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis IRS : inmem_range S N.
    Hypothesis IRD : inmem_range A N.
    Hypothesis NGS : ((S + N - 1) / 8 - S / 8 = Z.of_nat ngS)%Z.
    Hypothesis NGD : ((A + N - 1) / 8 - A / 8 = Z.of_nat ngD)%Z.

    Section Phase1.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - ASAN_MEMCPY_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis DST1 : rw_cells rsegs m1 A [CB (Z.to_nat N) junk].
      Hypothesis SRC1 : bytes_at rsegs m1 S src.
      Hypothesis Creal1 : ro_cells rsegs m1 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHD1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngD ++ [Z_to_bv 8 lastbD]).
      Hypothesis QBD1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1D).
      Hypothesis QBD2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2D).
      Hypothesis SHS1 : bytes_at rsegs m1 (S / 8 + shadow_off) (zeros ngS ++ [Z_to_bv 8 lastbS]).
      Hypothesis QBS1 : bytes_at rsegs m1 (sha S - sha S mod 8) (le8 w1S).
      Hypothesis QBS2 : bytes_at rsegs m1 (sha (S + N + -1) - sha (S + N + -1) mod 8) (le8 w2S).

      Section SlowS.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x17 x18 x22 x23 x28 x29 x30 x31 : word).
        Hypothesis SEPD : SEPDt. Hypothesis SEPS : SEPSt. Hypothesis DISJ : DISJt. Hypothesis LBD : LBDt.
        Hypothesis ESF : (sf = S / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngS)%Z.
        Notation AT pc x13 x15 x16 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 x18 (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2144))
                   (Z_to_bv 64 (S + N + -1)) (Z_to_bv 64 (N + -65)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="LBD DISJ SEPS SEPD QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk NGD IRD AFD AFS w2D w1D lastbD ngD N32 LEN CEIL LOLE junk Clg"] Lemma mc_slowS_end : forall x13 x16, evt rsegs POST (AT 0x57880 x13 (Z_to_bv 64 0) x16).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply mc_p2; try eassumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF LBD DISJ SEPS SEPD SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk NGD IRD AFD AFS w2D w1D lastbD lastbS ngD N32 LEN CEIL LOLE junk Clg"] Lemma mc_slowS_loop : forall (c : nat) (j : Z) x13 x16,
          Z.to_nat (Z.of_nat ngS - j) = c -> (0 <= j < Z.of_nat ngS)%Z -> x13 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x57870 x13 (Z_to_bv 64 0) x16).
        Proof.
          induction c as [|c IH]; intros j x13 x16 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHS1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (S / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHS1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngS lastbS (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngS)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply mc_slowS_end.
        Qed.
      End SlowS.

      (* [comment removed for export] *)
      #[using="QBS2 QBS1 SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk NGD NGS IRD IRS AFD AFS w2D w1D w2S w1S ngD ngS N32 LEN CEIL LOLE junk Clg"] Lemma mc_p1 : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31,
        SEPDt -> SEPSt -> DISJt -> LBSt -> LBDt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2144))
                   (Z_to_bv 64 (S + N)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x57558) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPD SEPS DISJ LBS LBD. pose proof LOLE as LOLE'. unfold ASAN_MEMCPY_STACK in LOLE'.
        unfold ASAN_MEMCPY_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
        pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
        assert (QH1 : (sha S - sha S mod 8 + Z.of_nat (length (le8 w1S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (S + N + -1) - sha (S + N + -1) mod 8 + Z.of_nat (length (le8 w2S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHS1 as SH. remember (zeros ngS ++ [Z_to_bv 8 lastbS]) as sbs eqn:Esbs.
        assert (SHhi : (S / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHD1 as SHD. remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbsD eqn:EsbsD.
        assert (SHDhi : (A / 8 + shadow_off + Z.of_nat (length sbsD) <= 0x100080000000)%Z).
        { subst sbsD. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBS1 as QB1. pose proof QBS2 as QB2. pose proof QBD1 as QB3. pose proof QBD2 as QB4.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3.
          + (* [comment removed for export] *)
            do 5 zstep.
            zstep. call_lit region_is_poisoned_spec by (idtac;
              lazymatch goal with
              | |- map_cells _ => repeat (split; [assumption|]); assumption
              | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
              | |- mem_inv _ _ => eassumption
              | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRS
              | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngS, lastbS; subst sbs; split; [exact NGS| split; [exact SH| exact LBS]]
              | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
              end).
            do 4 zstep.
            zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
            subst sbsD. eapply mc_p2; try eassumption.
          + (* [comment removed for export] *)
            zstep. subst sbsD. eapply mc_p2; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr S 3 <= S)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (S + N + -1) 3 <= S + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbS < 128)%Z) by (hs_lbr lastbS).
            pose proof (u8ro_read rsegs _ (S / 8 + shadow_off) _ (Z.of_nat ngS) (Z_to_bv 8 lastbS)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngS lastbS ngS), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (S + N + -1) lastbS) by
              (first [destruct LBS as [LB0|LB1]; [left; exact LB0| right;
                 replace (S + N + -1)%Z with (S + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + S / 8)%Z). set (sl := (2147450880 + (S + N + -1) / 8)%Z).
            assert (ESF : (sf = S / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngS)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsD.
            zstep. if_cases K8; zify_cond K8.
            * eapply mc_slowS_end; eassumption.
            * eapply mc_slowS_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbsD. eapply mc_p2; try eassumption.
      Qed.
    End Phase1.
  End Facts.
End Proofs2.

End AIcpisb.

Module AIcpnl3.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp3q7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpnnp.AIcpisb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
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
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
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
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac zero_tail N0 K2 K3 K5 K6 :=
  zstep; rewrite zb_lxor_ones by lia;
  zstep; if_cases K2; zify_cond K2; [exfalso; lia|];
  zstep; zstep;
  zstep; if_cases K3; zify_cond K3; [| exfalso; rewrite N0 in K3; try (generalize alloc_ceiling_val); clear -K3; try pose proof alloc_ceiling_val; cbv in K3; first [lia | discriminate]];
  zstep; if_cases K5; zify_cond K5; [exfalso; lia|];
  zstep;
  zstep; rewrite zb_lxor_ones by lia;
  zstep; if_cases K6; zify_cond K6; [exfalso; lia|];
  zstep;
  let K7 := fresh "K" in let K8 := fresh "K" in
  zstep; if_cases K7; zify_cond K7; [| exfalso; rewrite N0 in K7; try (generalize alloc_ceiling_val); clear -K7; try pose proof alloc_ceiling_val; cbv in K7; first [lia | discriminate]];
  zstep; if_cases K8; zify_cond K8; [exfalso; lia|];
  zstep.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma asan_memcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte) (lo : Z),
  let A := bv_unsigned a0 in let S := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m S src -> length src = Z.to_nat N ->
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  (S + N <= A \/ A + N <= S)%Z ->
  mem_inv rsegs m ->
  asan_memcpy_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + ASAN_MEMCPY_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + N <= lo \/ bv_unsigned sp <= A)%Z -> (S + N <= lo \/ bv_unsigned sp <= S)%Z ->
  (N < 2^32)%Z ->
  (N = 0%Z \/ (range_ok m S N /\ range_ok m A N)) ->
  evt rsegs (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x574fc) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros SRC LEN DST DISJ MI CELLS ST LOLE CEIL SEPD SEPS N32 RNG.
  pose proof LOLE as LOLE'. unfold ASAN_MEMCPY_STACK in LOLE'.
  (first [ dand4 CELLS as Gric Cric Creal MC | destruct CELLS as (Gric & Cric & Creal & MC) ]). pose proof MC as MC'. open_map_cells MC'.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - ASAN_MEMCPY_STACK, bv_unsigned sp)]%Z m) as MU.
  unfold ASAN_MEMCPY_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (NW : (bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z).
  { destruct RNG as [N0|((IR1 & _) & (IR2 & _))]; [rewrite N0; lia| unfold inmem_range in IR1, IR2; lia]. }
  destruct RNG as [N0 | (RS & RD)].
  { (* [comment removed for export] *)
    freeze DST; freeze SRC; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
    freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 72%nat ST. carve_frame 2072%nat ST.
    do 12 zstep.
    thaw DST MUp WM; thaw SRC MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
    thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM. clear MUp.
    do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
    do 4 zstep.
    zstep. if_cases Ka; zify_cond Ka.
    - zero_tail N0 K2 K3 K5 K6. eapply mc_tail; try eassumption.
    - zstep. if_cases Kb; zify_cond Kb.
      + zero_tail N0 K2 K3 K5 K6. eapply mc_tail; try eassumption.
      + zstep. if_cases Kc; zify_cond Kc. { exfalso. lia. }
        zero_tail N0 K2 K3 K5 K6. eapply mc_tail; try eassumption. }
  (* [comment removed for export] *)
  (first [ dand4 RS as IRS SOKS QWS1 QWS2 | destruct RS as (IRS & SOKS & QWS1 & QWS2) ]). (first [ dand4 RD as IRD SOKD QWD1 QWD2 | destruct RD as (IRD & SOKD & QWD1 & QWD2) ]).
  assert (AFS : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRS; lia).
  assert (AFD : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRD; lia).
  destruct (mapped8_le8 m _ QWS1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1S QBS1].
  destruct (mapped8_le8 m _ QWS2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2S QBS2].
  destruct (mapped8_le8 m _ QWD1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1D QBD1].
  destruct (mapped8_le8 m _ QWD2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2D QBD2].
  replace (bv_unsigned a1 + bv_unsigned a2 - 1)%Z with (bv_unsigned a1 + bv_unsigned a2 + -1)%Z in QBS2 by lia.
  replace (bv_unsigned a0 + bv_unsigned a2 - 1)%Z with (bv_unsigned a0 + bv_unsigned a2 + -1)%Z in QBD2 by lia.
  assert (QH1 : (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w1S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH3 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH4 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  (first [ dex2 SOKS as ngS lastbS; dand3 SOKS as NGS SHS LBS | dand5 SOKS as ngS lastbS NGS SHS LBS | destruct SOKS as (ngS & lastbS & NGS & SHS & LBS) ]). (first [ dex2 SOKD as ngD lastbD; dand3 SOKD as NGD SHD LBD | dand5 SOKD as ngD lastbD NGD SHD LBD | destruct SOKD as (ngD & lastbD & NGD & SHD & LBD) ]).
  remember (zeros ngS ++ [Z_to_bv 8 lastbS]) as sbsS eqn:EsbsS.
  remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbsD eqn:EsbsD.
  assert (SHShi : (bv_unsigned a1 / 8 + shadow_off + Z.of_nat (length sbsS) <= 0x100080000000)%Z).
  { subst sbsS. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (SHDhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbsD) <= 0x100080000000)%Z).
  { subst sbsD. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  freeze DST; freeze SRC; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
  freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SHS; freeze SHD; freeze QBS1; freeze QBS2; freeze QBD1; freeze QBD2.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  carve_frame 72%nat ST. carve_frame 2072%nat ST.
  do 12 zstep.
  thaw DST MUp WM; thaw SRC MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
  thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SHS MUp WM; thaw SHD MUp WM; thaw QBS1 MUp WM; thaw QBS2 MUp WM; thaw QBD1 MUp WM; thaw QBD2 MUp WM. clear MUp.
  do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
  do 4 zstep.
  zstep. if_cases Ka; zify_cond Ka.
  - subst sbsS sbsD. eapply mc_p1; try eassumption.
  - zstep. if_cases Kb; zify_cond Kb.
    + subst sbsS sbsD. eapply mc_p1; try eassumption.
    + zstep. if_cases Kc; zify_cond Kc. { exfalso. lia. }
      subst sbsS sbsD. eapply mc_p1; try eassumption.
Qed.

End CEIL.
End AIcpnl3.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Lemma ro_C8_of_bytes : forall (m : word -> option byte) A v,
  bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v H. split; [exact (conj I I)|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact H. Qed.

Lemma ro_C1_of_bytes : forall (m : word -> option byte) A b,
  bytes_at rsegs m A [b] -> ro_cells rsegs m A [C1 b].
Proof. intros m A b H. split; [exact (conj I I)|]. exact H. Qed.

(* [comment removed for export] *)
Lemma ro_C1_of_nth : forall (m : word -> option byte) A bs (k : nat) b,
  bytes_at rsegs m A bs -> nth_error bs k = Some b -> ro_cells rsegs m (A + Z.of_nat k) [C1 b].
Proof.
  intros m A bs k b H Hn. pose proof (nth_error_lt _ _ _ Hn) as Hk. (first [ dand3 H as H0 H1 H2 | destruct H as (H0 & H1 & H2) ]).
  split; [exact (conj I I)|]. split; [lia|]. split; [cbn [cells_bytes cbytes app length]; lia|].
  intros i Hi. cbn [cells_bytes cbytes app length] in Hi. destruct i; [|lia].
  cbn. rewrite Z.add_0_r. rewrite (H2 k Hk). exact Hn.
Qed.

Lemma map_cells_of_bytes : forall m : word -> option byte,
  bytes_at rsegs m 0xa8b70 (le8 (Z_to_bv 64 0xb4bb8)) ->
  bytes_at rsegs m 0xb4bb8 (le8 (Z_to_bv 64 0x7fff8000)) ->
  bytes_at rsegs m 0xa8b78 (le8 (Z_to_bv 64 0xb58a8)) ->
  bytes_at rsegs m 0xb58a8 (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m 0xa8b80 (le8 (Z_to_bv 64 0xb58b0)) ->
  bytes_at rsegs m 0xb58b0 (le8 (Z_to_bv 64 0)) ->
  bytes_at rsegs m 0xa8b88 (le8 (Z_to_bv 64 0xb58a0)) ->
  bytes_at rsegs m 0xb58a0 (le8 (Z_to_bv 64 0x7fffffffffff)) ->
  map_cells m.
Proof. intros. repeat (split; [apply ro_C8_of_bytes; assumption|]). apply ro_C8_of_bytes; assumption. Qed.

(* [comment removed for export] *)
Lemma strlen_icpt_cells_of_bytes : forall (m : word -> option byte) (cf : list byte),
  bytes_at rsegs m 0xb5898 [Z_to_bv 8 1] ->
  bytes_at rsegs m 0xaa8a8 (le8 (Z_to_bv 64 0xa22c4)) ->
  bytes_at rsegs m 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)) ->
  bytes_at rsegs m 0x1466e8 cf -> nth_error cf 251 = Some (Z_to_bv 8 1) ->
  map_cells m ->
  strlen_icpt_cells m.
Proof.
  intros m cf H1 H2 H3 H4 Hn MC. split; [apply asan_inited_cell_of_bytes; exact H1|].
  split; [apply ro_C8_of_bytes; exact H2|]. split; [apply ro_C8_of_bytes; exact H3|].
  split; [|exact MC]. change 0x1467e3%Z with (0x1466e8 + Z.of_nat 251)%Z. eapply ro_C1_of_nth; eassumption.
Qed.

(* [comment removed for export] *)
Lemma ro_C1C1_of_nth : forall (m : word -> option byte) A bs (k : nat) b0 b1,
  bytes_at rsegs m A bs -> nth_error bs k = Some b0 -> nth_error bs (S k) = Some b1 ->
  ro_cells rsegs m (A + Z.of_nat k) [C1 b0; C1 b1].
Proof.
  intros m A bs k b0 b1 H H0 H1. pose proof (nth_error_lt _ _ _ H1) as Hk. (first [ dand3 H as Ha Hl H2 | destruct H as (Ha & Hl & H2) ]).
  split; [exact (conj I (conj I I))|]. split; [lia|]. split; [cbn [cells_bytes cbytes app length]; lia|].
  intros i Hi. cbn [cells_bytes cbytes app length] in Hi.
  destruct i as [|[|i]]; [| |lia]; cbn [cells_bytes cbytes app nth_error].
  - rewrite Z.add_0_r. rewrite (H2 k) by lia. exact H0.
  - replace (A + Z.of_nat k + Z.of_nat 1)%Z with (A + Z.of_nat (S k))%Z by lia. rewrite (H2 (S k)) by lia. exact H1.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mic_cells_of_bytes : forall (m : word -> option byte) (cf : list byte),
  bytes_at rsegs m 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)) ->
  bytes_at rsegs m 0x1466e8 cf -> nth_error cf 254 = Some (Z_to_bv 8 1) -> nth_error cf 255 = Some (Z_to_bv 8 1) ->
  bytes_at rsegs m 0xb5898 [Z_to_bv 8 1] ->
  bytes_at rsegs m 0xaa8c0 (le8 (Z_to_bv 64 0xa1b5c)) -> bytes_at rsegs m 0xaa8c8 (le8 (Z_to_bv 64 0xa1a8c)) ->
  map_cells m -> mic_cells m.
Proof.
  intros m cf G CF N4 N5 CI R1 R2 MC. split; [apply ro_C8_of_bytes; exact G|].
  split; [change 0x1467e6%Z with (0x1466e8 + Z.of_nat 254)%Z; eapply ro_C1C1_of_nth; eassumption|].
  split; [apply asan_inited_cell_of_bytes; exact CI|]. split; [apply ro_C8_of_bytes; exact R1|].
  split; [apply ro_C8_of_bytes; exact R2| exact MC].
Qed.

(* [comment removed for export] *)
Lemma strcmp_icpt_cells_of_bytes : forall (m : word -> option byte) (cf : list byte),
  bytes_at rsegs m 0xb5898 [Z_to_bv 8 1] ->
  bytes_at rsegs m 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)) ->
  bytes_at rsegs m 0x1466e8 cf -> nth_error cf 245 = Some (Z_to_bv 8 0) -> nth_error cf 250 = Some (Z_to_bv 8 1) ->
  map_cells m -> strcmp_icpt_cells m.
Proof.
  intros m cf CI G CF N1 N2 MC. split; [apply asan_inited_cell_of_bytes; exact CI|]. split; [apply ro_C8_of_bytes; exact G|].
  split; [change 0x1467dd%Z with (0x1466e8 + Z.of_nat 245)%Z; eapply ro_C1_of_nth; eassumption|].
  split; [change 0x1467e2%Z with (0x1466e8 + Z.of_nat 250)%Z; eapply ro_C1_of_nth; eassumption| exact MC].
Qed.

(* [comment removed for export] *)
Lemma strchr_icpt_cells_of_bytes : forall (m : word -> option byte) (cf : list byte),
  bytes_at rsegs m 0xb5898 [Z_to_bv 8 1] ->
  bytes_at rsegs m 0xaa8b8 (le8 (Z_to_bv 64 0xa2088)) ->
  bytes_at rsegs m 0xa8b60 (le8 (Z_to_bv 64 0x1466e8)) ->
  bytes_at rsegs m 0x1466e8 cf -> nth_error cf 245 = Some (Z_to_bv 8 0) -> nth_error cf 253 = Some (Z_to_bv 8 1) ->
  map_cells m -> strchr_icpt_cells m.
Proof.
  intros m cf CI R G CF N1 N2 MC. split; [apply asan_inited_cell_of_bytes; exact CI|]. split; [apply ro_C8_of_bytes; exact R|].
  split; [apply ro_C8_of_bytes; exact G|].
  split; [change 0x1467dd%Z with (0x1466e8 + Z.of_nat 245)%Z; eapply ro_C1_of_nth; eassumption|].
  split; [change 0x1467e5%Z with (0x1466e8 + Z.of_nat 253)%Z; eapply ro_C1_of_nth; eassumption| exact MC].
Qed.

(* [comment removed for export] *)
Lemma strcpy_icpt_cells_of_bytes : forall (m : word -> option byte) (af : list byte),
  bytes_at rsegs m 0xb5898 [Z_to_bv 8 1] ->
  bytes_at rsegs m 0xa8b68 (le8 (Z_to_bv 64 0xb23b8)) ->
  bytes_at rsegs m 0xb23b8 af -> nth_error af 29 = Some (Z_to_bv 8 1) ->
  bytes_at rsegs m 0xaa9b8 (le8 (Z_to_bv 64 0xa21dc)) ->
  map_cells m -> strcpy_icpt_cells m.
Proof.
  intros m af CI G AF N1 R MC. split; [apply asan_inited_cell_of_bytes; exact CI|]. split; [apply ro_C8_of_bytes; exact G|].
  split; [change 0xb23d5%Z with (0xb23b8 + Z.of_nat 29)%Z; eapply ro_C1_of_nth; eassumption|].
  split; [apply ro_C8_of_bytes; exact R| exact MC].
Qed.
