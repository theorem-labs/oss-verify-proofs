(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_Scan_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNotJ.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgNot.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Module G_shgetc_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_Scan_iface.G_shgetc_A.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNotJ. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNot. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.   
(* [comment removed for export] *)

Import ListNotations.
Module H4S.
  Import Ltac2.
  Ltac2 prune_share () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_share1 () : unit := Control.enter prune_share.
End H4S.

(* [comment removed for export] *)
Definition shgetc_B_prog (B B_memchr B_memcpy : Z) : RStep.ptree :=
  PNode 80%Z
  (PNode 40%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4032 4
        (PJ_Store_SZ8_nnn 4 2 1 56 4
        (PJ_Store_SZ8_nnn 8 2 8 48 4
        (PJ_Store_SZ8_nnn 12 2 9 40 4
        (PJ_Store_SZ8_nnn 16 2 18 32 4
        (PJ_Store_SZ8_nnn 20 2 19 24 4
        (PJ_Store_SZ8_nnn 24 2 20 16 4
        (PJ_Store_SZ8_nnn 28 2 21 8 4
        (PJ_OpImm_ALU_ADD_nnn 32 20 12 0 4
        (PJ_OpImm_ALU_ADD_nnn 36 19 11 0 4 nil)))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 40 8 10 0 4
        (PJ_Load_SZ8_true_nnn 44 9 10 152 4
        (PJ_OpImm_ALU_ADD_nnn 48 18 12 256 4
        (PJ_OpImm_ALU_ADD_nnn 52 10 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 56 11 0 0 4
        (PJ_OpImm_ALU_ADD_nnn 60 12 18 0 4
        (PJ_Jal_nt 64 1 (jimm21 (B_memchr - (B + 64))) 4
        (PJ_Branch_BC_EQ_nnn 68 10 0 8 4
        (PJ_Op_ALU_SUB_nnn 72 18 10 9 4
        (PJ_OpImm_ALU_ADD_nnn 76 21 18 0 4 nil))))))))))))
  (PNode 120%Z
    (PLeaf
        (PJ_Branch_BC_LTU_nnn 80 18 20 8 4
        (PJ_OpImm_ALU_ADD_nnn 84 21 20 0 4
        (PJ_OpImm_ALU_ADD_nnn 88 10 19 0 4
        (PJ_OpImm_ALU_ADD_nnn 92 11 9 0 4
        (PJ_OpImm_ALU_ADD_nnn 96 12 21 0 4
        (PJ_Jal_nt 100 1 (jimm21 (B_memcpy - (B + 100))) 4
        (PJ_Op_ALU_ADD_nnn 104 10 9 21 4
        (PJ_Op_ALU_ADD_nnn 108 9 9 18 4
        (PJ_Store_SZ8_nnn 112 8 10 8 4
        (PJ_Store_SZ8_nnn 116 8 9 16 4 nil)))))))))))
    (PLeaf
        (PJ_Store_SZ8_nnn 120 8 9 152 4
        (PJ_OpImm_ALU_ADD_nnn 124 10 21 0 4
        (PJ_Load_SZ8_true_nnn 128 1 2 56 4
        (PJ_Load_SZ8_true_nnn 132 8 2 48 4
        (PJ_Load_SZ8_true_nnn 136 9 2 40 4
        (PJ_Load_SZ8_true_nnn 140 18 2 32 4
        (PJ_Load_SZ8_true_nnn 144 19 2 24 4
        (PJ_Load_SZ8_true_nnn 148 20 2 16 4
        (PJ_Load_SZ8_true_nnn 152 21 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 156 2 2 64 4
        (PJ_Jalr_nnn 160 0 1 0 4 nil))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_shgetc_B (IMG : RImg) := shgetc_B_prog (sym 0x1d2c8) (sym 0x21268) (sym 0x21334).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_shgetc_B : CodeAtT img_segs (sym 0x1d2c8) (PROGAT_CODE_shgetc_B IMG)}.
  Context {RB_shgetc_B : RelCode (sym 0x1d2c8) 164}.
  Context {RN_B_memchr_1d2c8 : RelNear (sym 0x1d2c8) (sym 0x21268)}.
  Context {RN_B_memcpy_1d2c8 : RelNear (sym 0x1d2c8) (sym 0x21334)}.
  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_memchr : memchr_contract}.
  Context {SPEC_memcpy : memcpy_contract}.
  Collection ImgHyps := IMG CODE_shgetc_B RB_shgetc_B RN_B_memchr_1d2c8 RN_B_memcpy_1d2c8 RS_22e18 rp_22e18 RS_34288 rp_34288 SPEC_memchr SPEC_memcpy.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.

Local Ltac h4_prune_share := ltac2:(H4S.prune_share1 ()).
Local Ltac share_tier := solve [ sf_unhide; h4_prune_share; Zify.zify; xlia zchecker ].
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | share_tier | tlia | split; [ tlia | exact I ] ].
Open Scope Z_scope.
Open Scope bv_scope.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. intros. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
  intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. (nelim IN 3%nat; intros c E INc).
  pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
  pose proof (f_equal bv_unsigned E) as E2. rewrite !Shgetc_lemmas.unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells img_segs m A [CB 1 bs] -> exists b, rw_cells img_segs m A [CB 1 [b]].
Proof.
  intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
  destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells img_segs m A cs -> rw_cells img_segs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells img_segs m A (CB 0 [] :: cs) -> rw_cells img_segs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

(* [comment removed for export] *)
Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [] m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ bytes_at img_segs m' A buf.
Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
  bytes_at img_segs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv img_segs m ->
  evt img_segs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21268)) fc None m (seg_rom img_segs)).
Proof.
  intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply SPEC_memchr with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
  intros ms' P. unfold G_memchr.memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ rw_cells img_segs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at img_segs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at img_segs m Src src -> length src = Z.to_nat N -> rw_cells img_segs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv img_segs m ->
  evt img_segs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (sym 0x21334)) fc None m (seg_rom img_segs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply SPEC_memcpy with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold G_memcpy.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 64) (q)
    /\ rw_cells img_segs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
    /\ rw_cells img_segs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at img_segs m' T (zbytes txt).

Definition sread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
  rw_cells img_segs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at img_segs m T (zbytes txt) -> rw_cells img_segs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom img_segs)).

Lemma sread_spec : sread_stmt.
Proof.
  unfold sread_stmt. intros until shc. intros FC TXT Hp Hoff BY DC T0 T1 Rrp Rre Rsh SEP1 SEP2 SEP3 ST SPLO SPF SPF2 SPD SPD2 SPT Q0 Q1 MI.
  pose proof (munch_refl [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  (nelim TXT 5%nat; intros Htxt NZ BYT AL L256).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  unfold STRING_READ, M64 in *. unfold zlength in *. pose_word_ranges.
  zs. carve_frame 64%nat ST.
  do 10 zs.
  (* [comment removed for export] *)
  set (k := Z.to_nat off).
  assert (SPLIT : zbytes txt = firstn k (zbytes pre) ++ (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post)).
  { rewrite Htxt, zbytes_app. cbn [zbytes map]. rewrite app_assoc. f_equal. rewrite zbytes_skipn. symmetry. apply firstn_skipn. }
  assert (LK : length (firstn k (zbytes pre)) = k) by (rewrite firstn_length, zbytes_length; lia).
  pose proof BY as BY2. rewrite SPLIT in BY2. apply bytes_at_app in BY2. destruct BY2 as [_ BY2]. rewrite LK in BY2.
  replace (T + Z.of_nat k)%Z with (T + off)%Z in BY2 by lia.
  assert (LSK : length (zbytes (skipn k pre)) = (length pre - k)%nat) by (rewrite zbytes_length, skipn_length; lia).
  zs. zs. zs. zs. zs.
  zs. callw (eapply memchr_callv; [exact BY2 | apply memchr_ok_cstr; [apply nonul_pos; apply Forall_skipn'; exact NZ | rewrite LSK, zbytes_length; clear -AL LT3 Hoff Hp T0; Z.div_mod_to_equations; lia ] | lia | lia | lia | hyp]).
  replace (memchr_res (T + off) 0 257 (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post)) with (T + p)%Z in *.
  2:{ rewrite memchr_res_cstr by (apply nonul_pos; apply Forall_skipn'; exact NZ). rewrite LSK.
      destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257); lia. }
  clear POST.
  zs. br10 K0. zs. zs. zs. brf K1.
  - (* [comment removed for export] *)
    assert (Eo : off = p) by lia. replace (T + p - (T + off))%Z with 0%Z by lia.
    zs. zs. zs. zs. callw (eapply memcpy_callv with (src := []) (junk := []);
      [ apply (proj1 (proj1 (bytes_at_app img_segs _ (T + off) [] _) BY2)) | reflexivity | apply (proj1 (proj1 (G_fwritex.rw_cells_app img_segs _ D [CB 0 []] _) (rw_cells_CB0 _ _ _ DC))) | lia | lia | lia | lia | hyp ]).
    clear PC POST. replace (T + off + 0)%Z with (T + p)%Z by lia.
    do 15 zs.
    release_frame FR ST q.
    apply evt_done. unfold sread_post, sread_len. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [unfold ss_cells, w0; rewrite Z.add_0_r; subst off; hyp|]. split; [hyp | hyp].
  - (* [comment removed for export] *)
    assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
    { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
      rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
    pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
    replace (T + p - (T + off))%Z with (p - off)%Z by lia.
    zs. zs. zs. zs. zs. callw (eapply memcpy_callv with (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]);
      [ apply (proj1 (proj1 (bytes_at_app img_segs _ (T + off) [_] _) BY2)) | reflexivity | exact DC | lia | lia | lia | lia | hyp ]).
    clear POST.
    do 15 zs.
    replace (T + off + (p - off))%Z with (T + p)%Z in * by lia.
    release_frame FR ST q.
    apply evt_done. unfold sread_post, sread_len. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [unfold ss_cells, w0; hyp|]. split; [hyp | hyp].
Qed.

(* [comment removed for export] *)
Definition sread_spec_c : Prop := sread_stmt.
Lemma sread_spec_c_ok : sread_spec_c.
Proof. exact sread_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
Existing Class sread_spec_c.
End G_shgetc_B.

(* [comment removed for export] *)
Module G_shgetc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
Export G_shgetc_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNot. Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.   
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
(* [comment removed for export] *)
 Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgNotJ.
Module H4S.
  Import Ltac2.
  Ltac2 prune_share () : unit :=
    let gv := SF2.vars_of [] (Control.goal ()) in
    SF2.prune_with (fun ty => SF2.meets (SF2.vars_of [] ty) gv).
  Ltac2 prune_share1 () : unit := Control.enter prune_share.
End H4S.

(* [comment removed for export] *)
Definition shgetc_prog (B got_ssp B_1e040 B_toread B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 100%Z
  (PNode 48%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4064 4
        (PJ_Store_SZ8_nnn 4 2 1 24 4
        (PJ_Store_SZ8_nnn 8 2 8 16 4
        (PJ_Store_SZ8_nnn 12 2 9 8 4
        (PJ_OpImm_ALU_ADD_nnn 16 8 10 0 4
        (PJ_Load_SZ8_true_nnn 20 11 10 8 4
        (PJ_Load_SZ8_true_nnn 24 10 10 88 4
        (PJ_Load_SZ8_true_nnn 28 12 8 192 4
        (PJ_Load_SZ8_true_nnn 32 9 8 200 4
        (PJ_Op_ALU_SUB_nnn 36 13 11 10 4
        (PJ_Op_ALU_ADD_nnn 40 9 13 9 4
        (PJ_Branch_BC_EQ_nnn 44 12 0 8 4 nil)))))))))))))
    (PLeaf
        (PJ_Branch_BC_GE_nnn 48 9 12 108 4
        (PJ_OpImm_ALU_ADD_nnn 52 10 8 0 4
        (PJ_Jal_nt 56 1 (jimm21 (B_1e040 - (B + 56))) 4
        (PJ_Branch_BC_LT_nnn 60 10 0 88 4
        (PJ_Load_SZ8_true_nnn 64 13 8 192 4
        (PJ_Load_SZ8_true_nnn 68 11 8 8 4
        (PJ_Load_SZ8_true_nnn 72 12 8 16 4
        (PJ_OpImm_ALU_ADD_nnn 76 9 9 1 4
        (PJ_Branch_BC_EQ_nnn 80 13 0 20 4
        (PJ_Op_ALU_SUB_nnn 84 14 12 11 4
        (PJ_Op_ALU_SUB_nnn 88 13 13 9 4
        (PJ_Branch_BC_GE_nnn 92 13 14 8 4
        (PJ_Op_ALU_ADD_nnn 96 12 11 13 4 nil)))))))))))))))
  (PNode 148%Z
    (PLeaf
        (PJ_Load_SZ8_true_nnn 100 13 8 88 4
        (PJ_Op_ALU_SUB_nnn 104 14 13 11 4
        (PJ_Op_ALU_ADD_nnn 108 14 9 14 4
        (PJ_Store_SZ8_nnn 112 8 12 184 4
        (PJ_Store_SZ8_nnn 116 8 14 200 4
        (PJ_Branch_BC_LTU_nnn 120 13 11 8 4
        (PJ_Store_SZ1_nnn 124 11 10 4095 4
        (PJ_Load_SZ8_true_nnn 128 1 2 24 4
        (PJ_Load_SZ8_true_nnn 132 8 2 16 4
        (PJ_Load_SZ8_true_nnn 136 9 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 140 2 2 32 4
        (PJ_Jalr_nnn 144 0 1 0 4 nil)))))))))))))
    (PLeaf
        (PJ_Load_SZ8_true_nnn 148 10 8 88 4
        (PJ_Load_SZ8_true_nnn 152 11 8 8 4
        (PJ_Op_ALU_SUB_nnn 156 10 10 11 4
        (PJ_Op_ALU_ADD_nnn 160 9 9 10 4
        (PJ_OpImm_ALU_ADD_nnn 164 10 0 4095 4
        (PJ_Store_SZ8_nnn 168 8 11 184 4
        (PJ_Store_SZ8_nnn 172 8 10 192 4
        (PJ_Store_SZ8_nnn 176 8 9 200 4
        (PJ_Load_SZ8_true_nnn 180 1 2 24 4
        (PJ_Load_SZ8_true_nnn 184 8 2 16 4
        (PJ_Load_SZ8_true_nnn 188 9 2 8 4
        (PJ_OpImm_ALU_ADD_nnn 192 2 2 32 4
        (PJ_Jalr_nnn 196 0 1 0 4 nil))))))))))))))).
(* [comment removed for export] *)
Definition shgetc_prog_1 (B got_ssp B_1e040 B_toread B_stack_chk_fail : Z) : RStep.ptree :=
  PNode 68%Z
  (PNode 32%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 0 2 2 4032 4
        (PJ_Store_SZ8_nnn 4 2 1 56 4
        (PJ_Store_SZ8_nnn 8 2 8 48 4
        (PJ_Store_SZ8_nnn 12 2 9 40 4
        (PJ_Store_SZ8_nnn 16 2 18 32 4
        (PJ_Store_SZ8_nnn 20 2 19 24 4
        (PJ_OpImm_ALU_ADD_nnn 24 9 10 0 4
        (PJ_Auipc_nt 28 10 (hi20 (got_ssp - (B + 28))) 4 nil)))))))))
    (PLeaf
        (PJ_Load_SZ8_true_nnt 32 18 10 (lo12 (got_ssp - (B + 28))) 4
        (PJ_Load_SZ8_true_nnn 36 10 18 0 4
        (PJ_Store_SZ8_nnn 40 2 10 16 4
        (PJ_OpImm_ALU_ADD_nnn 44 10 9 0 4
        (PJ_Jal_nt 48 1 (jimm21 (B_toread - (B + 48))) 4
        (PJ_OpImm_ALU_ADD_nnn 52 8 0 4095 4
        (PJ_Branch_BC_NE_nnn 56 10 0 36 4
        (PJ_Load_SZ8_true_nnn 60 13 9 64 4
        (PJ_OpImm_ALU_ADD_nnn 64 11 2 15 4 nil)))))))))))
  (PNode 104%Z
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 68 12 0 1 4
        (PJ_OpImm_ALU_ADD_nnn 72 19 0 1 4
        (PJ_OpImm_ALU_ADD_nnn 76 10 9 0 4
        (PJ_Jalr_nnn 80 1 13 0 4
        (PJ_Branch_BC_NE_nnn 84 10 19 8 4
        (PJ_Load_SZ1_false_nnn 88 8 2 15 4
        (PJ_Load_SZ8_true_nnn 92 10 18 0 4
        (PJ_Load_SZ8_true_nnn 96 11 2 16 4
        (PJ_Branch_BC_NE_nnn 100 10 11 36 4 nil))))))))))
    (PLeaf
        (PJ_OpImm_ALU_ADD_nnn 104 10 8 0 4
        (PJ_Load_SZ8_true_nnn 108 1 2 56 4
        (PJ_Load_SZ8_true_nnn 112 8 2 48 4
        (PJ_Load_SZ8_true_nnn 116 9 2 40 4
        (PJ_Load_SZ8_true_nnn 120 18 2 32 4
        (PJ_Load_SZ8_true_nnn 124 19 2 24 4
        (PJ_OpImm_ALU_ADD_nnn 128 2 2 64 4
        (PJ_Jalr_nnn 132 0 1 0 4
        (PJ_Jal_nt 136 1 (jimm21 (B_stack_chk_fail - (B + 136))) 4 nil))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_shgetc (IMG : RImg) := shgetc_prog (sym 0x1df78) (sym 0x22e18) (sym 0x1e040) (sym 0x1deac) (sym 0x15f04).
Definition PROGAT_CODE_shgetc_1 (IMG : RImg) := shgetc_prog_1 (sym 0x1e040) (sym 0x22e18) (sym 0x1e040) (sym 0x1deac) (sym 0x15f04).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_shgetc : CodeAtT img_segs (sym 0x1df78) (PROGAT_CODE_shgetc IMG)}.
  Context {RB_shgetc : RelCode (sym 0x1df78) 200}.
  Context {CODE_shgetc_1 : CodeAtT img_segs (sym 0x1e040) (PROGAT_CODE_shgetc_1 IMG)}.
  Context {RB_shgetc_1 : RelCode (sym 0x1e040) 140}.
  Local Notation GLRN a b := (RelNear (sym a) (sym b)) (only parsing). Local Notation GLRS a := (RelSym (sym a)) (only parsing). Context {RN_B_1e040_1df78 : GLRN 0x1df78 0x1e040}.
  Context {RN_B_toread_1df78 : GLRN 0x1df78 0x1deac}.
  Context {RN_B_stack_chk_fail_1df78 : GLRN 0x1df78 0x15f04}.
  Context {RN_B_1e040_1e040 : GLRN 0x1e040 0x1e040}.
  Context {RN_B_toread_1e040 : GLRN 0x1e040 0x1deac}.
  Context {RN_B_stack_chk_fail_1e040 : GLRN 0x1e040 0x15f04}.
  Context {RS_got_ssp : GLRS 0x22e18}.
  Context {RS_34288 : GLRS 0x34288}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_toread_spec : toread_spec_c}.
  Context {SPEC_sread_spec : sread_spec_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Context {RC_string_read : RelCode (sym 0x1d2c8) 164}.
  Collection ImgHyps := IMG CODE_shgetc RB_shgetc CODE_shgetc_1 RB_shgetc_1 RN_B_1e040_1df78 RN_B_toread_1df78 RN_B_stack_chk_fail_1df78 RN_B_1e040_1e040 RN_B_toread_1e040 RN_B_stack_chk_fail_1e040 RS_got_ssp RS_34288 rp_34288 SPEC_toread_spec SPEC_sread_spec RL0_0 rl0_0 RC_string_read.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].

Local Ltac h4_prune_share := ltac2:(H4S.prune_share1 ()).
Local Ltac share_tier := solve [ sf_unhide; h4_prune_share; Zify.zify; xlia zchecker ].
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | share_tier | tlia | split; [ tlia | exact I ] ].


Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 128) (q)
    /\ rw_cells img_segs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
    /\ bytes_at img_segs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells img_segs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 128 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 128)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom img_segs)).

Lemma uflow_spec : uflow_stmt.
Proof.
  unfold uflow_stmt. intros until canary. intros FC Hmode TXT Hp Hoff BY [SSP1 SSP2] T0 T1 Rrp Rre Rsh SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof (munch_refl [(q - 128, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof TXT as TXT'. (nelim TXT' 5%nat; intros Htxt NZ BYT AL L256).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add ss_cells] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  unfold UFLOW, got_ssp, ssp_guard, M64 in *. unfold zlength in *. pose_word_ranges.
  zs. carve_frame 64%nat ST.
  do 6 zs.
  zs. zs. zs. zs. zs.
  pose proof SPEC_toread_spec as TRS. unfold toread_stmt in TRS.
  destruct (stk_split _ _ _ (q - 80)%Z _ ST ltac:(lia)) as [ST1 ST2].
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  zs. callw (eapply TRS; [hyp | exact Hmode | lia | lia | lia | lia | lia | replace (q + -64 - 16)%Z with (q - 80)%Z by lia; exact ST2 | lia | lia | lia | lia | lia | hyp]).
  rename POST into FC1. rename PC into ST2. replace (q + -64 - 16)%Z with (q - 80)%Z in ST2 by lia. unfold ss_cells, w0, STRING_READ in FC1.
  (* [comment removed for export] *)
  lazymatch goal with FR' : rw_cells _ ?mc (q + -64)%Z (CB 16 ?bs :: ?rest) |- _ =>
    pose proof (rw_cells_split_CB img_segs mc (q + -64)%Z [] 16 bs rest [15; 1]%nat FR' eq_refl) as FR2; clear FR'; cbn [mk_CB_cells app] in FR2;
    pose proof (proj1 (G_fwritex.rw_cells_app img_segs mc (q + -64)%Z [_] _) FR2) as [J15 FR3]; clear FR2;
    pose proof (proj1 (G_fwritex.rw_cells_app img_segs mc _ [_] _) FR3) as [DC0 FR]; clear FR3 end.
  cbn [cells_size csize Nat.add] in DC0, FR.
  lazymatch type of DC0 with rw_cells _ _ ?a _ => replace a with (q + -49)%Z in DC0 by lia end.
  lazymatch type of FR with rw_cells _ _ ?a _ => replace a with (q + -48)%Z in FR by lia end.
  destruct (rw_cells_CB1 _ _ _ DC0) as [dj DC]. clear DC0.
  zs. zs. br10 K0.
  zs. zs. zs. zs. zs.
  pose proof (stk_merge _ _ _ _ _ ST1 ST2 ltac:(lia)) as ST3. clear ST1 ST2.
  pose proof SPEC_sread_spec as SRS. unfold sread_stmt, STRING_READ in SRS.
  zs. replace (ret_pc (Z_to_bv 64 (sym 0x1d2c8))) with (Z_to_bv 64 (sym 0x1d2c8)) by (symmetry; apply ret_pc_sym; arel_side).
  callw (eapply SRS with (off := off) (pre := pre) (post := post);
    [unfold ss_cells, w0; hyp | exact TXT | exact Hp | exact Hoff | hyp | replace (q + -64 + 15)%Z with (q + -49)%Z by lia; exact DC | lia | lia | lia | lia | lia
    | lia | unfold zlength; lia | unfold zlength; lia
    | replace (q + -64 - 64)%Z with (q - 128)%Z by lia; exact ST3 | lia | lia | lia | lia | lia | unfold zlength; lia | lia | lia | hyp ]).
  rename PC into ST. replace (q + -64 - 64)%Z with (q - 128)%Z in ST by lia. rename PC1 into DC2. rename POST into BY3. rename PC0 into FC2.
  assert (Rch : (0 <= znth txt off < 256)%Z).
  { destruct (Z.lt_ge_cases off (Z.of_nat (length txt))).
    - apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia.
    - rewrite znth_ge by (unfold zlength; lia). lia. }
  unfold sread_len, uflow_res in *. destruct (Z.ltb_spec0 off p).
  - zs. br10 K1. zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt off)) by lia.
    do 3 zs. br10 K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_post, uflow_res, sread_len. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
  - zs. br01 K1.
    do 3 zs. br10 K2; try (exfalso; apply K2; reflexivity).
    do 8 zs.
    release_frame J15 ST (q + -49)%Z. release_frame DC2 ST (q + -48)%Z. release_frame FR ST q.
    apply evt_done. unfold uflow_post, uflow_res, sread_len. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC2|]. split; [exact BY3|]. split; [exact SSP1 | exact SSP2].
Qed.

(* [comment removed for export] *)
Definition uflow_spec_c : Prop := uflow_stmt.
Lemma uflow_spec_c_ok : uflow_spec_c.
Proof. exact uflow_spec. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - 160) q
    /\ rw_cells img_segs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
    /\ bytes_at img_segs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells img_segs m Fp (rf_cells T p w f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom img_segs)).

Lemma shgetc_spec : shgetc_stmt.
Proof.
  unfold shgetc_stmt. intros until canary. intros FC ST0 Hn Hbuf Hrp Hw Hc0 TXT Hp BY [SSP1 SSP2] T0 T1 SEP3 ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof (munch_refl [(q - 160, q); (Fp, Fp + 232)]%Z m) as MU. pose proof (wmono_refl img_segs m) as WM.
  pose proof TXT as TXT'. (nelim TXT' 5%nat; intros Htxt NZ BYT AL L256).
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  destruct f as [buf rpos cnt0 n st sn]. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in *. subst st n buf.
  unfold rf_cells, rf_rend in FC. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg] in FC.
  assert (J4 : length (j_pad0 ssJ) = 4%nat /\ length (j_pad1 ssJ) = 4%nat) by (split; reflexivity).
  cbn [ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  pose proof (rw_cells_bound _ _ _ _ FC) as B. cbn [cells_size csize Nat.add] in B.
  unfold SHGETC, got_ssp, ssp_guard, STRING_READ, M64 in *. unfold zlength in *.
  assert (Roff : (0 <= rpos <= p)%Z) by (destruct w; subst rpos; lia).
  zs. carve_frame 32%nat ST.
  do 10 zs.
  (* [comment removed for export] *)
  assert (EOFT : forall m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) j8 she shl shc cnt,
    cnt = (p - cnt0)%Z ->
    mem_inv img_segs m1 -> munch [(q - 160, q); (Fp, Fp + 232)]%Z m m1 -> wmono img_segs m m1 ->
    stk img_segs m1 (q - 160) (q + -32) ->
    rw_cells img_segs m1 (q + -32) [CB 8 j8; C8 s1; C8 s0; C8 ra] ->
    rw_cells img_segs m1 Fp (rf_cells_raw T p true (mkSh txt p cnt0 p true true) ssJ she shl shc) ->
    bytes_at img_segs m1 T (zbytes txt) -> rw_cells img_segs m1 (sym 0x22e18) [C8 (Z_to_bv 64 (sym 0x34288))] -> rw_cells img_segs m1 (sym 0x34288) [C8 canary] ->
    sh_getc {| sh_buf := txt; sh_rpos := rpos; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} = ((-1)%Z, mkSh txt p cnt0 p true true) ->
    evt img_segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p
                 {| sh_buf := txt; sh_rpos := rpos; sh_cnt0 := cnt0; sh_n := p; sh_stdio := true; sh_shlim_neg := sn |} txt canary m)
      (MS (mkR x1 (Z_to_bv 64 (q + -32)) gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 cnt) (Z_to_bv 64 T) (Z_to_bv 64 (T + p)) x12 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1df78 + 156)) fc None m1 (seg_rom img_segs))).
  { clear FC MI MU WM ST FR BY SSP1 SSP2.
    intros m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 j8 she shl shc cnt Ecnt MI MU WM ST FR FC BY SSP1 SSP2 EG. subst cnt.
    unfold rf_cells_raw, rf_rend in FC.
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
    do 11 zs.
    release_frame FR ST q.
    apply evt_done. unfold shgetc_post. rewrite EG. cbn [fst snd].
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
             unfold STRING_READ, M64. replace (- cnt0)%Z with (p - cnt0 + (T - (T + p)))%Z by lia. hyp. }
    split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2]. }
  destruct sn.
  - (* [comment removed for export] *)
    assert (Ew : w = true) by (destruct w; [reflexivity | destruct (Hw eq_refl) as [_ X]; discriminate X]). subst w. cbn in Hrp. subst rpos.
    replace (if true then 18446744073709551615%Z else 0%Z) with 18446744073709551615%Z in * by reflexivity.
    replace (if true then (T + p)%Z else T) with (T + p)%Z in * by reflexivity.
    zs. br10 K1; try (exfalso; clear -K1; lia).
    zs. br01 K2.
    eapply EOFT; try hyp; try glia.
    all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
    all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
         unfold STRING_READ, M64; hyp.
  - (* [comment removed for export] *)
    replace (if false then 18446744073709551615%Z else 0%Z) with 0%Z in * by reflexivity.
    pose proof uflow_spec as UFS. unfold uflow_stmt, got_ssp, ssp_guard, UFLOW in UFS.
    destruct w.
    + (* [comment removed for export] *)
      cbn in Hrp. subst rpos.
      replace (if true then (T + p)%Z else T) with (T + p)%Z in * by reflexivity.
      zs. br01 K1; try (exfalso; clear -K1; lia).
      zs. zs.
      callw (eapply UFS with (off := p) (pre := pre) (post := post) (p := p);
        [ unfold ss_cells, w0, zero4, STRING_READ, M64; hyp
        | right; reflexivity | exact TXT | exact Hp | | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | | | | | | 
        | replace (q + -32 - 128)%Z with (q - 160)%Z by lia; hyp | | | | | | | | | | hyp ]; unfold zlength; lia).
      rename PC into ST. replace (q + -32 - 128)%Z with (q - 160)%Z in ST by lia. rename PC0 into FC. clear BY SSP1 SSP2. rename PC1 into BY. destruct POST as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      unfold uflow_res, sread_len in *. replace (p <? p) with false in * by (symmetry; apply Z.ltb_irrefl).
      replace (T + p + 0)%Z with (T + p)%Z in FC by lia. unfold ss_cells, w0, zero4 in FC.
      zs. br01 K2; try (exfalso; clear -K2; lia).
      zs. zs.
      eapply EOFT; try hyp; try glia.
      all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; rewrite Z.eqb_refl; reflexivity).
      all: unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
           unfold STRING_READ, M64 in *; hyp.
    + (* [comment removed for export] *)
      destruct (Hw eq_refl) as [Ec0 _]. subst rpos cnt0.
      replace (if false then (T + p)%Z else T) with T in * by reflexivity.
      assert (Rch : (0 <= znth txt 0 < 256)%Z).
      { destruct (Z.lt_ge_cases 0 (Z.of_nat (length txt))).
        - apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia.
        - rewrite znth_ge by (unfold zlength; lia). lia. }
      zs. br01 K1; try (exfalso; clear -K1; lia).
      zs. zs.
      callw (eapply UFS with (off := 0%Z) (pre := pre) (post := post) (p := p);
        [ rewrite (Z.add_0_r T); unfold ss_cells, w0, zero4, STRING_READ, M64; hyp
        | right; reflexivity | exact TXT | exact Hp | | hyp | unfold ssp_cells, got_ssp, ssp_guard; split; hyp | | | | | | 
        | replace (q + -32 - 128)%Z with (q - 160)%Z by lia; hyp | | | | | | | | | | hyp ]; unfold zlength; lia).
      rename PC into ST. replace (q + -32 - 128)%Z with (q - 160)%Z in ST by lia. rename PC0 into FC. clear BY SSP1 SSP2. rename PC1 into BY. destruct POST as [SSP1 SSP2]. unfold got_ssp, ssp_guard in SSP1, SSP2.
      unfold uflow_res, sread_len in *. unfold ss_cells, w0, zero4 in FC.
      destruct (Z.ltb_spec0 0 p).
      * (* [comment removed for export] *)
        replace (T + 0 + 1)%Z with (T + 1)%Z in FC by lia.
        zs. br10 K2; try (exfalso; clear -K2 Rch; lia).
        do 5 zs. br01 K3; try (exfalso; clear -K3; lia).
        do 5 zs. zs. br01 K4; try (exfalso; clear -K4; lia).
        do 5 zs.
        release_frame FR ST q.
        apply evt_done. unfold shgetc_post. unfold sh_getc. cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0 fst snd].
        replace (0 =? p) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb fst snd sh_stdio sh_rpos sh_n sh_buf sh_cnt0 sh_shlim_neg].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
        split. { unfold rf_cells, rf_rend. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale].
                 unfold STRING_READ, M64 in *. hyp_cells. }
        split; [exact BY|]. unfold ssp_cells, got_ssp, ssp_guard. split; [exact SSP1 | exact SSP2].
      * (* [comment removed for export] *)
        assert (Ep : p = 0%Z) by lia.
        replace (0 <? p) with false in * by (symmetry; apply Z.ltb_ge; lia).
        replace (T + 0 + 0)%Z with (T + p)%Z in FC by lia.
        zs. br01 K2; try (exfalso; clear -K2; lia).
        zs. zs.
        replace (T + 0 + 0)%Z with (T + p)%Z by lia.
        eapply EOFT; try hyp; try glia.
        all: try (unfold sh_getc; cbn [sh_stdio sh_rpos sh_n negb sh_buf sh_cnt0]; replace (0 =? p) with true by (symmetry; apply Z.eqb_eq; lia); rewrite <- Ep; reflexivity).
        all: rewrite <- ?Ep; unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
             unfold STRING_READ, M64 in *; hyp.
Qed.

(* [comment removed for export] *)
Definition shgetc_spec_c : Prop := shgetc_stmt.
Lemma shgetc_spec_c_ok : shgetc_spec_c.
Proof. exact shgetc_spec. Qed.


End Img.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
Existing Class uflow_spec_c.
Existing Class shgetc_spec_c.
End G_shgetc.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_rscan_lib.
Module G_rfile.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls G_shgetc.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_rscan_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.  
Import ListNotations.
Open Scope Z_scope.

Definition rfile_prog (B : Z) : RStep.prog := [].

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
Definition PROGAT_CODE_rfile (IMG : RImg) := rfile_prog (sym 0x1df78).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_rfile : CodeAt img_segs (sym 0x1df78) (PROGAT_CODE_rfile IMG)}.
  Context {RB_rfile : RelCode (sym 0x1df78) 0}.
  Context {SPEC_shgetc_spec : shgetc_spec_c}.
  Collection ImgHyps := IMG CODE_rfile RB_rfile SPEC_shgetc_spec.



(* [comment removed for export] *)
Definition RFJ (T : Z) (txt : list Z) (p : Z) (w : bool) (J : rfj) (kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
  (sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\
                        (w = false -> sh_rpos f = 0 /\ sh_cnt0 f = 0 /\ sh_shlim_neg f = false) /\ J = ssJ)%Z.

Section RF.
  Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
  Hypothesis Hp : 0 <= p < zlength txt.
  Hypothesis Hnul : znth txt p = 0.
  Hypothesis T0 : 4096 <= T.
  Hypothesis T1 : T + 2^41 <= 2^63.

  Notation RFI := (RFJ T txt p true J).

  Lemma RFI_ok : forall kmin c f, RFI kmin c f -> sh_ok T txt f.
  Proof. intros kmin c f (OK & _). exact OK. Qed.

  Lemma RFI_rpos : forall kmin c f, RFI kmin c f -> 0 <= sh_rpos f <= p + 1.
  Proof.
    intros kmin c f nelH_; (nelim nelH_ 6%nat; intros OK Rc CC KM NS SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    destruct (sh_stdio f) eqn:ES; [(nelim (SS eq_refl) 3%nat; intros N1 N2 _); lia | (nelim (NS eq_refl) 3%nat; intros N1 N2 N3); lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_fast : forall kmin c f, RFI kmin c f ->
    T + sh_rpos f <> rf_rend T p true f ->
    sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) NE. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
    destruct (sh_stdio f) eqn:ES; cbn [negb].
    - (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). rewrite N1.
      destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
    - reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_fast_lt : forall kmin c f, RFI kmin c f -> c <> 0 ->
    T + sh_rpos f <> rf_rend T p true f -> 0 <= sh_rpos f < zlength txt.
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
    - (nelim (SS eq_refl) 4%nat; intros N1 N2 N3 _). lia.
    - (nelim (NS eq_refl) 3%nat; intros N1 N2 N3). specialize (N3 Hc). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_getc_slow : forall kmin c f, RFI kmin c f ->
    T + sh_rpos f = rf_rend T p true f ->
    sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = p /\ 0 <= sh_cnt0 f <= sh_rpos f.
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) E. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
    - (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). repeat split; try assumption; unfold M64 in E; lia.
    - exfalso. unfold M64 in E. lia.
  Qed.

  Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
                                 try lazymatch goal with |- (_ -> _) => intro end).

  Lemma RFI_getc : forall kmin c f, RFI kmin c f -> c <> 0 -> RFI (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hc. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst). unfold zlength in *.
    assert (R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256).
    { intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply Shgetc_lemmas.znth_In'. unfold zlength. lia. }
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct st; cbn [negb].
    - (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). subst n.
      destruct (Z.eqb_spec rpos p) as [E|NE]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      + unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
      + pose proof (R0 rpos ltac:(lia)).
        assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
        unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
    - (nelim (NS eq_refl) 3%nat; intros N1 N2 N3). specialize (N3 Hc). subst sn. cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
      unfold zlength. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. crush.
      all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
  Qed.

  Lemma RFI_unget : forall kmin c f, RFI kmin c f -> 1 <= kmin -> RFI (kmin - 1) c (sh_unget f).
  Proof.
    intros kmin c f (OK & Rc & CC & KM & NS & SS) Hk. (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    - destruct st.
      + (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). specialize (N3 eq_refl). crush.
      + destruct (NS eq_refl) as (N1 & _). discriminate N1.
    - specialize (KM eq_refl). destruct st.
      + (nelim (SS eq_refl) 5%nat; intros N1 N2 N3 N4 N5). crush.
      + (nelim (NS eq_refl) 3%nat; intros N1 N2 N3). crush.
  Qed.

  (* [comment removed for export] *)
  Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
  Proof. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
  Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
    sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
  Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.
(* [comment removed for export] *)

Open Scope bv_scope.
(* [comment removed for export] *)
Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells img_segs m Fp (rf_cells T p true f J) ->
  RFJ T txt p true J kmin c f ->
  (T + sh_rpos f = rf_rend T p true f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom img_segs)).
Proof.
  intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof RJ as RJ'. (nelim RJ' 6%nat; intros OK Rc CC KM NS SS).
  assert (Hp2 : (0 <= p < zlength txt)%Z).
  { (nelim TXT 5%nat; intros Htxt _ _ _ _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
  (nelim (rf_getc_slow T txt p J Hp2 T1 kmin c f RJ SLOW) 5%nat; intros ST0 EJ Hn Hrp Hc0).
  subst J.
  eapply SPEC_shgetc_spec with (w := true) (pre := pre) (post := post); try eassumption; try lia.
  all: try (destruct OK as (Hbuf & _); exact Hbuf).
  all: try (cbn; exact Hrp).
  all: try (intros X; discriminate X).
Qed.

(* [comment removed for export] *)
Definition shgetc_callJ_c : Prop := forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells img_segs m Fp (rf_cells T p true f J) ->
  RFJ T txt p true J kmin c f ->
  (T + sh_rpos f = rf_rend T p true f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom img_segs)).
Lemma shgetc_callJ_c_ok : shgetc_callJ_c.
Proof. exact shgetc_callJ. Qed.


End Img.

(* [comment removed for export] *)
Existing Class shgetc_callJ_c.
End G_rfile.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require Import G_memcpy G_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G Require G_fmt_fp_lib.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.G.G_fmt_fp_lib.G_fmt_fp_calls.
Import G_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_rscan_lib.
Import G_rfile.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
 From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNot. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RegFold. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require RProgAt. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require JunkAbs.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache. From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc Require Import RProgNotJ.

(* [comment removed for export] *)
Definition scanexp_prog (B K_10408 B_shgetc : Z) : RStep.ptree :=
  PNode 312%Z
  (PNode 156%Z
    (PNode 76%Z
      (PNode 36%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 0 2 2 4016 4
            (PJ_Store_SZ8_nnn 4 2 1 72 4
            (PJ_Store_SZ8_nnn 8 2 8 64 4
            (PJ_Store_SZ8_nnn 12 2 9 56 4
            (PJ_Store_SZ8_nnn 16 2 18 48 4
            (PJ_Store_SZ8_nnn 20 2 19 40 4
            (PJ_Store_SZ8_nnn 24 2 20 32 4
            (PJ_Store_SZ8_nnn 28 2 21 24 4
            (PJ_Store_SZ8_nnn 32 2 22 16 4 nil))))))))))
        (PLeaf
            (PJ_Store_SZ8_nnn 36 2 23 8 4
            (PJ_OpImm_ALU_ADD_nnn 40 8 10 0 4
            (PJ_Load_SZ8_true_nnn 44 10 10 8 4
            (PJ_Load_SZ8_true_nnn 48 12 8 184 4
            (PJ_OpImm_ALU_ADD_nnn 52 9 11 0 4
            (PJ_Branch_BC_EQ_nnn 56 10 12 28 4
            (PJ_OpImm_ALU_ADD_nnn 60 11 10 1 4
            (PJ_Store_SZ8_nnn 64 8 11 8 4
            (PJ_Load_SZ1_false_nnn 68 18 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 72 10 0 43 4 nil))))))))))))
      (PNode 116%Z
        (PLeaf
            (PJ_Branch_BC_NE_nnn 76 18 10 28 4
            (PJ_Jal_nn 80 0 32 4
            (PJ_OpImm_ALU_ADD_nnn 84 10 8 0 4
            (PJ_Jal_nt 88 1 (jimm21 (B_shgetc - (B + 88))) 4
            (PJ_OpImm_ALU_ADD_nnn 92 18 10 0 4
            (PJ_OpImm_ALU_ADD_nnn 96 10 0 43 4
            (PJ_Branch_BC_EQ_nnn 100 18 10 12 4
            (PJ_OpImm_ALU_ADD_nnn 104 10 0 45 4
            (PJ_Branch_BC_NE_nnn 108 18 10 48 4
            (PJ_Load_SZ8_true_nnn 112 10 8 8 4 nil)))))))))))
        (PLeaf
            (PJ_Load_SZ8_true_nnn 116 11 8 184 4
            (PJ_OpImm_ALU_ADD_nnn 120 19 18 4051 4
            (PJ_Branch_BC_EQ_nnn 124 10 11 44 4
            (PJ_OpImm_ALU_ADD_nnn 128 11 10 1 4
            (PJ_Store_SZ8_nnn 132 8 11 8 4
            (PJ_Load_SZ1_false_nnn 136 18 10 0 4
            (PJ_OpImm_ALU_SLTU_nnn 140 20 19 1 4
            (PJ_OpImm32_nnn 144 10 18 4038 4
            (PJ_Branch_BC_NE_nnn 148 9 0 44 4
            (PJ_Jal_nn 152 0 72 4 nil)))))))))))))
    (PNode 232%Z
      (PNode 192%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 156 20 0 0 4
            (PJ_OpImm32_nnn 160 10 18 4038 4
            (PJ_Jal_nn 164 0 60 4
            (PJ_OpImm_ALU_ADD_nnn 168 10 8 0 4
            (PJ_Jal_nt 172 1 (jimm21 (B_shgetc - (B + 172))) 4
            (PJ_OpImm_ALU_ADD_nnn 176 18 10 0 4
            (PJ_OpImm_ALU_SLTU_nnn 180 20 19 1 4
            (PJ_OpImm32_nnn 184 10 10 4038 4
            (PJ_Branch_BC_EQ_nnn 188 9 0 36 4 nil))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 192 11 0 4085 4
            (PJ_Branch_BC_LTU_nnn 196 11 10 28 4
            (PJ_Load_SZ8_true_nnn 200 10 8 192 4
            (PJ_Branch_BC_LT_nnn 204 10 0 28 4
            (PJ_Load_SZ8_true_nnn 208 10 8 8 4
            (PJ_OpImm_ALU_ADD_nnn 212 10 10 4095 4
            (PJ_Store_SZ8_nnn 216 8 10 8 4
            (PJ_Jal_nn 220 0 12 4
            (PJ_OpImm_ALU_ADD_nnn 224 11 0 4086 4
            (PJ_Branch_BC_GEU_nnn 228 10 11 36 4 nil))))))))))))
      (PNode 272%Z
        (PLeaf
            (PJ_Load_SZ8_true_nnn 232 10 8 192 4
            (PJ_OpImm_ALU_ADD_nnn 236 9 0 4095 4
            (PJ_ShiftImm_ALU_SLL_nnn 240 9 9 63 4
            (PJ_Branch_BC_LT_nnn 244 10 0 332 4
            (PJ_Load_SZ8_true_nnn 248 10 8 8 4
            (PJ_OpImm_ALU_ADD_nnn 252 10 10 4095 4
            (PJ_Store_SZ8_nnn 256 8 10 8 4
            (PJ_Jal_nn 260 0 316 4
            (PJ_OpImm32_nnn 264 10 18 4048 4
            (PJ_OpImm_ALU_ADD_nnn 268 9 0 0 4 nil)))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 272 21 0 9 4
            (PJ_Branch_BC_LTU_nnn 276 21 10 272 4
            (PJ_OpImm_ALU_ADD_nnn 280 22 0 10 4
            (PJ_Lui_nn 284 10 52429 4
            (PJ_OpImm32_nnn 288 23 10 3276 4
            (PJ_Load_SZ8_true_nnn 292 10 8 8 4
            (PJ_Load_SZ8_true_nnn 296 11 8 184 4
            (PJ_Branch_BC_EQ_nnn 300 10 11 40 4
            (PJ_OpImm_ALU_ADD_nnn 304 11 10 1 4
            (PJ_Store_SZ8_nnn 308 8 11 8 4 nil))))))))))))))
  (PNode 468%Z
    (PNode 388%Z
      (PNode 348%Z
        (PLeaf
            (PJ_Load_SZ1_false_nnn 312 19 10 0 4
            (PJ_Mul_M_MUL_nnn 316 10 9 22 4
            (PJ_Op_ALU_ADD_nnn 320 18 18 10 4
            (PJ_OpImm32_nnn 324 10 19 4048 4
            (PJ_OpImm32_nnn 328 9 18 4048 4
            (PJ_Branch_BC_GEU_nnn 332 21 10 40 4
            (PJ_Jal_nn 336 0 44 4
            (PJ_OpImm_ALU_ADD_nnn 340 10 8 0 4
            (PJ_Jal_nt 344 1 (jimm21 (B_shgetc - (B + 344))) 4 nil))))))))))
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 348 19 10 0 4
            (PJ_Mul_M_MUL_nnn 352 10 9 22 4
            (PJ_Op_ALU_ADD_nnn 356 18 18 10 4
            (PJ_OpImm32_nnn 360 10 19 4048 4
            (PJ_OpImm32_nnn 364 9 18 4048 4
            (PJ_Branch_BC_LTU_nnn 368 21 10 12 4
            (PJ_OpImm_ALU_ADD_nnn 372 18 19 0 4
            (PJ_Branch_BC_LT_nnn 376 9 23 8108 4
            (PJ_OpImm_ALU_ADD_nnn 380 18 0 9 4
            (PJ_Branch_BC_LTU_nnn 384 18 10 164 4 nil))))))))))))
      (PNode 428%Z
        (PLeaf
            (PJ_Auipc_nt 388 10 (hi20 (K_10408 - (B + 388))) 4
            (PJ_Load_SZ8_true_nnt 392 21 10 (lo12 (K_10408 - (B + 388))) 4
            (PJ_OpImm_ALU_ADD_nnn 396 22 0 10 4
            (PJ_Load_SZ8_true_nnn 400 10 8 8 4
            (PJ_Load_SZ8_true_nnn 404 11 8 184 4
            (PJ_Branch_BC_EQ_nnn 408 10 11 40 4
            (PJ_OpImm_ALU_ADD_nnn 412 11 10 1 4
            (PJ_Store_SZ8_nnn 416 8 11 8 4
            (PJ_Load_SZ1_false_nnn 420 10 10 0 4
            (PJ_Mul_M_MUL_nnn 424 11 9 22 4 nil)))))))))))
        (PLeaf
            (PJ_Op_ALU_ADD_nnn 428 19 19 11 4
            (PJ_OpImm32_nnn 432 11 10 4048 4
            (PJ_OpImm_ALU_ADD_nnn 436 9 19 4048 4
            (PJ_Branch_BC_GEU_nnn 440 18 11 36 4
            (PJ_Jal_nn 444 0 40 4
            (PJ_OpImm_ALU_ADD_nnn 448 10 8 0 4
            (PJ_Jal_nt 452 1 (jimm21 (B_shgetc - (B + 452))) 4
            (PJ_Mul_M_MUL_nnn 456 11 9 22 4
            (PJ_Op_ALU_ADD_nnn 460 19 19 11 4
            (PJ_OpImm32_nnn 464 11 10 4048 4 nil)))))))))))))
    (PNode 544%Z
      (PNode 504%Z
        (PLeaf
            (PJ_OpImm_ALU_ADD_nnn 468 9 19 4048 4
            (PJ_Branch_BC_LTU_nnn 472 18 11 12 4
            (PJ_OpImm_ALU_ADD_nnn 476 19 10 0 4
            (PJ_Branch_BC_LT_nnn 480 9 21 8112 4
            (PJ_OpImm_ALU_ADD_nnn 484 10 0 9 4
            (PJ_Branch_BC_LTU_nnn 488 10 11 60 4
            (PJ_OpImm_ALU_ADD_nnn 492 18 0 10 4
            (PJ_Jal_nn 496 0 20 4
            (PJ_OpImm_ALU_ADD_nnn 500 10 8 0 4 nil))))))))))
        (PLeaf
            (PJ_Jal_nt 504 1 (jimm21 (B_shgetc - (B + 504))) 4
            (PJ_OpImm32_nnn 508 10 10 4048 4
            (PJ_Branch_BC_GEU_nnn 512 10 18 36 4
            (PJ_Load_SZ8_true_nnn 516 10 8 8 4
            (PJ_Load_SZ8_true_nnn 520 11 8 184 4
            (PJ_Branch_BC_EQ_nnn 524 10 11 8168 4
            (PJ_OpImm_ALU_ADD_nnn 528 11 10 1 4
            (PJ_Store_SZ8_nnn 532 8 11 8 4
            (PJ_Load_SZ1_false_nnn 536 10 10 0 4
            (PJ_OpImm32_nnn 540 10 10 4048 4 nil))))))))))))
      (PNode 584%Z
        (PLeaf
            (PJ_Branch_BC_LTU_nnn 544 10 18 8164 4
            (PJ_Load_SZ8_true_nnn 548 10 8 192 4
            (PJ_Branch_BC_LT_nnn 552 10 0 16 4
            (PJ_Load_SZ8_true_nnn 556 10 8 8 4
            (PJ_OpImm_ALU_ADD_nnn 560 10 10 4095 4
            (PJ_Store_SZ8_nnn 564 8 10 8 4
            (PJ_Branch_BC_EQ_nnn 568 20 0 8 4
            (PJ_Op_ALU_SUB_nnn 572 9 0 9 4
            (PJ_OpImm_ALU_ADD_nnn 576 10 9 0 4
            (PJ_Load_SZ8_true_nnn 580 1 2 72 4 nil)))))))))))
        (PLeaf
            (PJ_Load_SZ8_true_nnn 584 8 2 64 4
            (PJ_Load_SZ8_true_nnn 588 9 2 56 4
            (PJ_Load_SZ8_true_nnn 592 18 2 48 4
            (PJ_Load_SZ8_true_nnn 596 19 2 40 4
            (PJ_Load_SZ8_true_nnn 600 20 2 32 4
            (PJ_Load_SZ8_true_nnn 604 21 2 24 4
            (PJ_Load_SZ8_true_nnn 608 22 2 16 4
            (PJ_Load_SZ8_true_nnn 612 23 2 8 4
            (PJ_OpImm_ALU_ADD_nnn 616 2 2 80 4
            (PJ_Jalr_nnn 620 0 1 0 4 nil)))))))))))))).

(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step2_with rp rpm vh ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_with rp rpm vh.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.step_ecall ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep_ecall.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_load.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.solve_cond ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asolve_cond.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.step ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.stepz_fast ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.astep2_fast.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SysStep.sys_nret ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.asys_nret.
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.post_call segs m ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.apost_call segs m.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.simp_regs ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RegFold.simp_regs_f.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.RTac.find_t_eval k t ::= OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.RProgAt.find_t_eval_at k t.
Definition PROGAT_CODE_scanexp (IMG : RImg) := scanexp_prog (sym 0x1fe6c) (sym 0x10408) (sym 0x1df78).
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::=
  OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.RL.Reloc.JunkAbs.split_for_access_abs H segs m A cs kn n.
Section Img.
  Context {IMG : RImg}.
  Context {CODE_scanexp : CodeAtT img_segs (sym 0x1fe6c) (PROGAT_CODE_scanexp IMG)}.
  Context {RB_scanexp : RelCode (sym 0x1fe6c) 624}.
  Context {RO_10408 : RoB img_segs (sym 0x10408) ([BV 8 174; BV 8 71; BV 8 225; BV 8 122; BV 8 20; BV 8 174; BV 8 71; BV 8 1])}.
  Context {RN_B_shgetc_1fe6c : RelNear (sym 0x1fe6c) (sym 0x1df78)}.
  Context {RS_K_10408 : RelSym (sym 0x10408)}.
  Context {RS_22e18 : RelSym (sym 0x22e18)}.
  Let rp_22e18 : (0 <= sym 0x22e18 /\ sym 0x22e18 < 2^30)%Z := @rel_sym_pf _ RS_22e18.
  Context {RS_34288 : RelSym (sym 0x34288)}.
  Let rp_34288 : (0 <= sym 0x34288 /\ sym 0x34288 < 2^30)%Z := @rel_sym_pf _ RS_34288.
  Context {SPEC_shgetc_callJ : shgetc_callJ_c}.
  Context {RL0_0 : ZFact (sym 0x22e18 + 8 <= sym 0x34288)%Z}.
  Let rl0_0 : (sym 0x22e18 + 8 <= sym 0x34288)%Z := @zfact_pf _ RL0_0.
  Collection ImgHyps := IMG CODE_scanexp RB_scanexp RO_10408 RN_B_shgetc_1fe6c RS_K_10408 RS_22e18 rp_22e18 RS_34288 rp_34288 SPEC_shgetc_callJ RL0_0 rl0_0.


Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
Local Ltac sc_clear := repeat match goal with H : sc_dj _ _ _ _ |- _ => clear H | H : sc_in _ _ _ |- _ => clear H
  | H : sc_no _ _ _ _ |- _ => clear H | H : sc_noin _ _ _ |- _ => clear H end.
(* [comment removed for export] *)
Local Ltac gonly_lia := let HI := fresh "HI" in pose proof I as HI; clear - HI; Zify.zify; xlia zchecker.
Local Ltac gonly_refute := lazymatch goal with |- ?G => assert (~ G) by gonly_lia end.
Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | tlia | split; [ tlia | exact I ] ].
(* [comment removed for export] *)
Local Ltac flia ::= first [ assumption | slim; lia ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.

  (* [comment removed for export] *)
Local Ltac brf K := if_cases K; zify_cond K; try (rewrite ?signed_of_Z in K by lia).
Local Ltac brsf K := if_cases K; rewrite ?bv_lts_0_lit, ?bv_lts_lit in K by lia;
    repeat first [apply (proj1 (Bool.negb_true_iff _)) in K | apply (proj1 (Bool.negb_false_iff _)) in K];
    first [apply Z.ltb_lt in K | apply Z.ltb_ge in K | idtac].
Local Ltac br10 K := brf K; [ exfalso; lia | ].
Local Ltac br01 K := brf K; [ | exfalso; lia ].
  (* [comment removed for export] *)
Local Ltac zsimp_in_w H :=
    try (match type of H with
         | context [v_sltu _ _] => idtac | context [v_slt _ _] => idtac
         | context [v_sltiu _ _] => idtac | context [v_slti _ _] => idtac end;
         rewrite ?v_sltu_b2z, ?v_slt_b2z, ?v_sltiu_b2z, ?v_slti_b2z in H);
    try (match type of H with context [zxb] => cbv delta [zxb] in H end);
    zb_fold_lits_in H;
    repeat match type of H with
    | context [bv_unsigned (Z_to_bv 64 ?e)] => zs_wrap_in e H
    | _ => progress (zs_idioms_in H)
    end; zb_fold_lits_in H.
Local Ltac brfw K := if_cases K; rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in K;
    unfold bv_eqb, bv_ltu, bv_lts, bv_leu in K; fold_lit_ux_in K; zsimp_in_w K; zify_bool K;
    try (rewrite ?signed_of_Z in K by lia).
(* [comment removed for export] *)
Local Ltac lia_goal_g P := lazymatch P with
  | (_ < _)%Z => idtac | (_ <= _)%Z => idtac | (_ > _)%Z => idtac | (_ >= _)%Z => idtac
  | (_ < _)%nat => idtac | (_ <= _)%nat => idtac | (_ > _)%nat => idtac | (_ >= _)%nat => idtac
  | @eq Z _ _ => idtac | @eq nat _ _ => idtac | @eq bool _ _ => idtac | @eq N _ _ => idtac
  | ?A /\ ?B => lia_goal_g A; lia_goal_g B | ?A \/ ?B => lia_goal_g A; lia_goal_g B | ?A -> ?B => lia_goal_g B | ~ _ => idtac
  | ?A <-> ?B => lia_goal_g A; lia_goal_g B | False => idtac | True => idtac
  end.
Local Ltac glia := lazymatch goal with |- ?G => lia_goal_g G end; lia.
Definition SCANEXP : Z := (sym 0x1fe6c).
Definition SCANEXP_DEPTH : Z := 240.

Lemma isdigitc_iff : forall c, (-2^31 < c < 2^31)%Z -> isdigitc c = true <-> (48 <= c <= 57)%Z.
Proof. intros c Hc. unfold isdigitc, u32. rewrite Z.ltb_lt. split; intros H; Z.div_mod_to_equations; lia. Qed.
Lemma isdigitc_t : forall c, (-2^31 < c < 2^31)%Z -> (48 <= c <= 57)%Z -> isdigitc c = true.
Proof. intros. apply (proj2 (isdigitc_iff c ltac:(lia))). lia. Qed.
Lemma isdigitc_f : forall c, (-2^31 < c < 2^31)%Z -> ~ (48 <= c <= 57)%Z -> isdigitc c = false.
Proof. intros c Hc H. destruct (isdigitc c) eqn:E; [|reflexivity]. exfalso. apply H. apply (proj1 (isdigitc_iff c Hc)). exact E. Qed.

(* [comment removed for export] *)
Definition scanexp_tail (fuelc : nat) (neg c : Z) (f : shfile) : option (shfile * Z) :=
  if negb (isdigitc c) then Some (sh_unget f, LLONG_MIN_) else
  match scanexp_l1_loop fuelc (0%Z, c, f) with
  | None => None
  | Some (x, c, f) =>
    match scanexp_l2_loop fuelc (x, c, f) with
    | None => None
    | Some (y, c, f) =>
      match scanexp_l3_loop fuelc (c, f) with
      | None => None
      | Some (c, f) => Some (sh_unget f, if nz neg then (- y)%Z else y)
      end end end.

Lemma scanexp_eq : forall fuelc f pok,
  scanexp fuelc f pok =
  (let '(c, f) := sh_getc f in
   let '(neg, c, f) :=
     (if ((c =? 43) || (c =? 45))%Z then
        let neg := b2z (c =? 45)%Z in
        let '(c, f) := sh_getc f in
        let f := if negb (isdigitc c) && nz pok then sh_unget f else f in (neg, c, f)
      else (0%Z, c, f)) in
   scanexp_tail fuelc neg c f).
Proof.
  intros fuelc f pok. unfold scanexp, scanexp_tail.
  destruct (sh_getc f) as [c1 f1].
  destruct (if ((c1 =? 43) || (c1 =? 45))%Z then _ else _) as [[neg c2] f2]. reflexivity.
Qed.

Definition scanexp_rpost (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (J : rfj) (txt : list Z) (canary : word) (fR : shfile) (e10 : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' k' c',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 e10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom img_segs)
    /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m m' /\ wmono img_segs m m' /\ mem_inv img_segs m'
    /\ stk img_segs m' (q - SCANEXP_DEPTH) q
    /\ rw_cells img_segs m' Fp (rf_cells T p true fR J)
    /\ RFJ T txt p true J k' c' fR /\ (1 <= k')%Z
    /\ bytes_at img_segs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition scanexp_rstmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z),
  scanexp fuelc f0 pok = Some (fR, e10) ->
  rw_cells img_segs m Fp (rf_cells T p true f0 J) -> RFJ T txt p true J kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
  (sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre) ->
  Forall (fun c => 0 <= c < 256)%Z txt -> (0 <= p < zlength txt)%Z -> znth txt p = 0%Z ->
  bytes_at img_segs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk img_segs m (q - SCANEXP_DEPTH) q -> (4096 <= q - SCANEXP_DEPTH)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= pok <= 1)%Z -> (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv img_segs m ->
  evt img_segs (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SCANEXP) fc None m (seg_rom img_segs)).

Section Scanexp.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (pok : Z) (fuelc : nat) (f0 : shfile) (kmin0 c0 : Z) (fR : shfile) (e10 : Z).
  Hypothesis HM : scanexp fuelc f0 pok = Some (fR, e10).
  Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
  Hypothesis SPLO : (4096 <= q - SCANEXP_DEPTH)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
  Hypothesis SPT : (T + zlength txt <= q - SCANEXP_DEPTH \/ q <= T)%Z.
  Hypothesis SG1 : (ssp_guard + 8 <= q - SCANEXP_DEPTH)%Z.
  Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
  Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
  Hypothesis Hpok : (0 <= pok <= 1)%Z.
  Hypothesis Q0 : (0 <= q)%Z.
  Hypothesis Q1 : (q < 2^63)%Z.
  (* [comment removed for export] *)
  Local Ltac sec_tier := solve [ rewrite ?zbytes_length; let HI := fresh "HI" in pose proof I as HI;
                                 clear - HI Hp T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1;
                                 unfold zlength, SCANEXP_DEPTH, got_ssp, ssp_guard, sf_hide in *; Zify.zify; xlia zchecker ].
  Local Ltac tslia ::= first [ exact I | gonly_lia | gonly_refute; fail 1 | sec_tier | tlia | split; [ tlia | exact I ] ].

  Notation POST := (scanexp_rpost ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p J txt canary fR e10 m0).
  Notation SPv := (Z_to_bv 64 (q + -80)).
  Notation RFJ' := (RFJ T txt p true J).
  Definition frame (j8 : list byte) : list cell := [CB 8 j8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Definition finv (m : word -> option byte) (j8 : list byte) : Prop :=
    mem_inv img_segs m /\ munch [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0 m /\ wmono img_segs m0 m
    /\ rw_cells img_segs m (q + -80) (frame j8) /\ stk img_segs m (q - SCANEXP_DEPTH) (q + -80)
    /\ bytes_at img_segs m T (zbytes txt) /\ ssp_cells m canary.
  Ltac dest_finv H := (nelim H 7%nat; intros MI MU WM FR ST BY [SSP1 SSP2]); unfold frame in FR; unfold SCANEXP_DEPTH in MU, ST;
    unfold got_ssp, ssp_guard in SSP1, SSP2;
    try (let LTX := fresh "LTX" in assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length; unfold zlength in * ).
  Ltac mk_finv := unfold finv, frame, SCANEXP_DEPTH, ssp_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; hyp.

  (* [comment removed for export] *)
  Lemma stdio_getc : forall f, sh_stdio (snd (sh_getc f)) = sh_stdio f.
  Proof. intros f. unfold sh_getc. destruct (sh_stdio f); cbn [negb]; [destruct (_ =? _); reflexivity | reflexivity]. Qed.
  Lemma stdio_unget : forall f, sh_stdio (sh_unget f) = sh_stdio f.
  Proof. intros f. unfold sh_unget. destruct (sh_shlim_neg f); reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_ret : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c fX,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true fX J) -> RFJ' k c fX -> (1 <= k)%Z -> fX = fR ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 e10) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 576)) fc None m (seg_rom img_segs)).
  Proof.
    intros until fX. intros FI FC RJ Hk EX. subst fX. dest_finv FI. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    do 12 zs.
    release_frame FR ST q.
    apply evt_done. unfold scanexp_rpost, SCANEXP_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC|]. split; [exact RJ|]. split; [exact Hk|]. split; [exact BY | split; [exact SSP1 | exact SSP2]].
  Qed.

  Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.

  (* [comment removed for export] *)
  Lemma L_end : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (v neg : Z),
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    (0 <= neg <= 1)%Z -> (-2^63 <= v < 2^63)%Z ->
    fR = sh_unget f -> e10 = (if nz neg then - v else v)%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 v) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 548)) fc None m (seg_rom img_segs)).
  Proof using Hp SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT T0 T1 pre ImgHyps.
    intros until neg. intros FI FC RJ Hk Rneg Rv HfR He.
    pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof RJ as RJ2. (nelim RJ2 6%nat; intros OK Rc CC KM NS SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
    pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
    destruct (sh_shlim_neg f) eqn:SN.
    - (* [comment removed for export] *)
      rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br01 K1.
      zs. brf K2.
      + assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
        eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
        replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
        eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
    - (* [comment removed for export] *)
      rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br10 K1.
      zs. zs. zs.
      zs. brf K2.
      + assert (Ee : e10 = v) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia). rewrite <- Ee.
        eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + zs. assert (Ee : e10 = (- v)%Z) by (rewrite He; unfold nz; destruct (Z.eqb_spec neg 0); cbn; lia).
        replace (Z_to_bv 64 (0 - Z.land v 18446744073709551615)%Z) with (Z_to_bv 64 e10) by (apply Z_to_bv_eqm; rewrite Ee, land_W64; Z.div_mod_to_equations; lia).
        eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
        unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  (* [comment removed for export] *)
  Lemma L_ND : forall m j8 (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    fR = sh_unget f -> e10 = LLONG_MIN_ ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 232)) fc None m (seg_rom img_segs)).
  Proof using Hp SEP SG1 SG2 SG3 SPF SPF2 SPLO SPT T0 T1 pre ImgHyps.
    intros until f. intros FI FC RJ Hk HfR He.
    pose proof FI as FI'. dest_finv FI'. unfold SCANEXP_DEPTH in SPLO, SPT, SG1. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof RJ as RJ2. (nelim RJ2 6%nat; intros OK Rc CC KM NS SS). (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst).
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia). unfold M64 in RR.
    pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
    destruct (sh_shlim_neg f) eqn:SN.
    - rewrite (rf_unget_nop f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. zs. zs. br01 K1.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
      eapply L_ret; [exact FI | | exact RJu | lia | symmetry; exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
    - rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. zs. zs. br10 K1.
      zs. zs. zs. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 e10) by (rewrite He; apply Z_to_bv_eqm; vm_compute; reflexivity).
      eapply L_ret; [mk_finv | | exact RJu | lia | symmetry; exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  Ltac plia := unfold zlength, got_ssp, ssp_guard in *; lia.
  Ltac unfold_fc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  (* [comment removed for export] *)
  Ltac post_getc :=
    match goal with H : ssp_cells ?m' _ |- _ =>
      repeat match goal with H2 : rw_cells _ _ (sym 0x22e18) _ |- _ => clear H2 | H2 : rw_cells _ _ (sym 0x34288) _ |- _ => clear H2 end;
      destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
    match goal with H : stk _ ?m' (q + -80 - 160)%Z _ |- _ =>
      replace (q + -80 - 160)%Z with (q - 240)%Z in H by lia;
      try match goal with H2 : stk _ _ (q - 240)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
    repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.
  (* [comment removed for export] *)
  Ltac site_facts FC RJ k c f :=
    unfold SCANEXP_DEPTH in SPLO, SPT, SG1; unfold got_ssp, ssp_guard in SG1, SG2, SG3;
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; (nelim RJ2 6%nat; intros OK Rc CC KM NS SS); (nelim OK 6%nat; intros Hbuf Rl Rr Rc0 Rn Rst);
    assert (RR : (0 <= rf_rend T p true f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp k c f RJ) as Rrp.

  (* [comment removed for export] *)
  Lemma L_L3 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (y neg cX : Z) fX,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z ->
    scanexp_l3_loop n (sh_getc f) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y else y)%Z -> (0 <= neg <= 1)%Z -> (-2^63 <= y < 2^63)%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 10) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 516)) fc None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc HL HfR He Rneg Ry.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    rewrite (surjective_pairing (sh_getc f)) in HL. cbn [scanexp_l3_loop scanexp_l3_body] in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 10) x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 516)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros. rewrite (isdigitc_t (fst (sh_getc f))) in HL by lia.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x19' x21' x22' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10' x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) x21' x22' x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 548)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros. rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. injection HL as E1 E2. subst cX fX.
      eapply L_end with (k := (k + 1)%Z); try eassumption; try glia. }
    clear IH HL.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br01 K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply SPEC_shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. fixw2. zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read img_segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. fixw2. zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  Definition LM : Z := 92233720368547758.
  Lemma LM_eq : Z.quot LLONG_MAX_ 100 = LM. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_L2 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x28 x29 x30 x31 : word) x1 k c f (y neg y2 c2 : Z) f2 n3 cX fX,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= y < LM)%Z ->
    scanexp_l2_loop n (y, c, f) = Some (y2, c2, f2) ->
    scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 y) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 9) (Z_to_bv 64 c) (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 400)) fc None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc Hy HL HL3 HfR He Rneg. pose proof Hy as Hy0. unfold LM in Hy.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    cbn [scanexp_l2_loop scanexp_l2_cond scanexp_l2_body] in HL. rewrite (isdigitc_t c), LM_eq in HL by lia.
    replace (y <? LM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hy0)). cbn [andb] in HL.
    rewrite (surjective_pairing (sh_getc f)) in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    set (y' := (10 * y + c - 48)%Z) in HL.
    assert (Ry' : (0 <= y' <= 10 * LM - 1)%Z) by (unfold y', LM in *; lia).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x12' x13' x14' x15' x16' x17' x19' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 9) x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 476)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      pose proof FI2 as FI'. dest_finv FI'. unfold LM in *.
      zs. zs. brsf K.
      - eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia.
      - destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
        rewrite LM_eq in HL. replace (y' <? LM) with false in HL by (symmetry; apply Z.ltb_ge; unfold LM; lia). rewrite Bool.andb_false_r in HL.
        injection HL as E1 E2 E3. subst y2 c2 f2.
        destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_t (fst (sh_getc f))) in HL3 by lia.
        zs. zs. br10 K2; try (exfalso; mlia2). zs. zs.
        eapply L_L3 with (k := (k + 1)%Z); try eassumption; unfold LM in *; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x10' x12' x13' x14' x15' x16' x17' x18' x19' x23' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 y') x10' (Z_to_bv 64 (fst (sh_getc f) - 48)) x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 LM) (Z_to_bv 64 10) x23' s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 484)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst y2 c2 f2.
      destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
      injection HL3 as E4 E5. subst cX fX.
      pose proof FI2 as FI'. dest_finv FI'.
      zs. zs. brfw K2; try (exfalso; mlia2).
      eapply L_end with (k := (k + 1)%Z); try eassumption; unfold LM in *; try glia. }
    clear IH HL HL3.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br01 K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply SPEC_shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. zs. zs. fixw2. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
      let v := getreg 11%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
      zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read img_segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. zs. fixw2. zs.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 y') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small y) by lia; lia).
      let v := getreg 11%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
      zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  Definition IM : Z := 214748364.
  Lemma IM_eq : Z.quot INT_MAX_ 10 = IM. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma L_L1 : forall n m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word) x1 k c f (x neg xv c1 : Z) f1 n2 y2 c2 f2 n3 cX fX,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (48 <= c <= 57)%Z -> (0 <= x < IM)%Z ->
    scanexp_l1_loop n (x, c, f) = Some (xv, c1, f1) ->
    scanexp_l2_loop n2 (xv, c1, f1) = Some (y2, c2, f2) ->
    scanexp_l3_loop n3 (c2, f2) = Some (cX, fX) ->
    fR = sh_unget fX -> e10 = (if nz neg then - y2 else y2)%Z -> (0 <= neg <= 1)%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 x) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 292)) fc None m (seg_rom img_segs)).
  Proof.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc Hx HL HL2 HL3 HfR He Rneg. pose proof Hx as Hx0. unfold IM in Hx.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    cbn [scanexp_l1_loop scanexp_l1_cond scanexp_l1_body] in HL. rewrite (isdigitc_t c), IM_eq in HL by lia.
    replace (x <? IM) with true in HL by (symmetry; apply Z.ltb_lt; exact (proj2 Hx0)). cbn [andb] in HL.
    rewrite (surjective_pairing (sh_getc f)) in HL.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    set (x' := (10 * x + c - 48)%Z) in HL.
    assert (Rx' : (0 <= x' < 2^31)%Z) by (unfold x' in *; lia).
    assert (DIG : (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
                 x18' (Z_to_bv 64 (fst (sh_getc f))) (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 372)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      pose proof FI2 as FI'. dest_finv FI'. unfold IM in *.
      zs. zs. brsf K.
      - eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (k + 1)%Z (fst (sh_getc f)) (snd (sh_getc f))); try eassumption; try glia.
      - destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
        rewrite IM_eq in HL. replace (x' <? IM) with false in HL by (symmetry; apply Z.ltb_ge; unfold IM; lia). rewrite Bool.andb_false_r in HL.
        injection HL as E1 E2 E3. subst xv c1 f1.
        zs. zs. br10 K2; try (exfalso; mlia2). zs. zs. zs.
        eapply L_L2 with (k := (k + 1)%Z); try eassumption; unfold LM; try glia. }
    assert (ND : ~ (48 <= fst (sh_getc f) <= 57)%Z -> forall m2 j8' (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x18' x19' x28' x29' x30' x31' : word) x1',
      finv m2 j8' -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f)) J) ->
      evt img_segs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 Fp) (Z_to_bv 64 x') (Z_to_bv 64 (fst (sh_getc f) - 48)) x11' x12' x13' x14' x15' x16' x17'
                 x18' x19' (Z_to_bv 64 neg) (Z_to_bv 64 9) (Z_to_bv 64 10) (Z_to_bv 64 IM) s8 s9 s10 s11 x28' x29' x30' x31')
            F (Z_to_bv 64 (sym 0x1fe6c + 380)) fc None m2 (seg_rom img_segs))).
    { intros Hd. intros until x1'. intros FI2 FC2.
      destruct n as [|n']; [discriminate HL|]. cbn [scanexp_l1_loop scanexp_l1_cond] in HL.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL by lia. cbn [andb] in HL. injection HL as E1 E2 E3. subst xv c1 f1.
      destruct n2 as [|n2']; [discriminate HL2|]. cbn [scanexp_l2_loop scanexp_l2_cond] in HL2.
      rewrite (isdigitc_f (fst (sh_getc f))) in HL2 by lia. cbn [andb] in HL2. injection HL2 as E4 E5 E6. subst y2 c2 f2.
      destruct n3 as [|n3']; [discriminate HL3|]. cbn [scanexp_l3_loop scanexp_l3_body] in HL3. rewrite (isdigitc_f (fst (sh_getc f))) in HL3 by lia.
      injection HL3 as E7 E8. subst cX fX.
      pose proof FI2 as FI'. dest_finv FI'.
      zs. zs. brfw K2; try (exfalso; mlia2).
      eapply L_end with (k := (k + 1)%Z); try eassumption; try glia. }
    clear IH HL HL2 HL3.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br01 K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply SPEC_shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      zs. zs. zs. zs. fixw2. zs. fixw2.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
      let v := getreg 10%Z in replace v with (Z_to_bv 64 (fst (sh_getc f) - 48)) by reflexivity.
      zs. brfw K2.
      + (* [comment removed for export] *) eapply ND; [mlia2 | mk_finv | exact FC].
      + eapply DIG; [mlia2 | mk_finv | exact FC].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read img_segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. zs. fixw2. zs. fixw2.
      let v := getreg 9%Z in replace v with (Z_to_bv 64 x') by (apply Z_to_bv_eqm; f_equal; rewrite ?land_W64; rewrite ?(Z.mod_small x) by lia; lia).
      let v := getreg 10%Z in replace v with (Z_to_bv 64 (znth txt (sh_rpos f) - 48)) by reflexivity.
      zs. brfw K2.
      + eapply DIG; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
      + zs. eapply ND; [mlia2 | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells].
  Qed.

  (* [comment removed for export] *)
  Lemma L_E4 : forall m j8 (x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
    scanexp_tail fuelc neg c f = Some (fR, e10) -> (0 <= neg <= 1)%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 224)) fc None m (seg_rom img_segs)).
  Proof.
    intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg.
    pose proof FI as FI'. dest_finv FI'. unfold scanexp_tail in HT.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      rewrite (isdigitc_t c) in HT by mlia2. cbn [negb] in HT.
      destruct (scanexp_l1_loop fuelc (0%Z, c, f)) as [[[xv c1] f1]|] eqn:HL1; [|discriminate HT].
      destruct (scanexp_l2_loop fuelc (xv, c1, f1)) as [[[y2 c2] f2]|] eqn:HL2; [|discriminate HT].
      destruct (scanexp_l3_loop fuelc (c2, f2)) as [[cX fX]|] eqn:HL3; [|discriminate HT].
      injection HT as E1 E2.
      zs. fixw2. zs. zs. zs. brfw K2; try (exfalso; mlia2).
      zs. zs. zs.
      eapply L_L1 with (k := k); try eassumption; unfold IM; try glia; try mlia2. all: symmetry; assumption.
    - (* [comment removed for export] *)
      rewrite (isdigitc_f c) in HT by mlia2. cbn [negb] in HT. injection HT as E1 E2.
      eapply L_ND; try eassumption; try glia. all: symmetry; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma L_C4 : forall m j8 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f (neg : Z),
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (3 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z ->
    scanexp_tail fuelc neg c (if negb (isdigitc c) && nz pok then sh_unget f else f) = Some (fR, e10) ->
    (0 <= neg <= 1)%Z -> pok <> 0%Z ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) (Z_to_bv 64 (c - 58)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 (Z_to_bv 64 neg) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 192)) fc None m (seg_rom img_segs)).
  Proof.
    intros until neg. intros FI FC RJ Hk Hst Hc HT Rneg Hpk.
    replace (nz pok) with true in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [lia|reflexivity]).
    pose proof FI as FI'. dest_finv FI'.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      rewrite (isdigitc_t c) in HT by mlia2. cbn [negb andb] in HT.
      eapply L_E4; try eassumption; try glia.
    - (* [comment removed for export] *)
      rewrite (isdigitc_f c) in HT by mlia2. cbn [negb andb] in HT.
      site_facts FC RJ k c f.
      pose proof (RFI_unget T txt p J Hp k c f RJ ltac:(lia)) as RJu.
      pose proof (stdio_unget f) as Hstu. rewrite Hst in Hstu.
      destruct (sh_shlim_neg f) eqn:SN.
      + rewrite (rf_unget_nop f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br01 K1. 
        eapply L_ND with (k := (k - 1)%Z); try eassumption; try glia.
        all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
      + rewrite (rf_unget_eq f SN) in *. unfold_fc2 FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br10 K1.
        zs. zs. zs. zs.
        eapply L_ND with (k := (k - 1)%Z); try eassumption; try glia.
        all: try (unfold scanexp_tail in HT; rewrite (isdigitc_f c) in HT by mlia2; cbn [negb] in HT; injection HT as E1 E2; symmetry; assumption).
        1: mk_finv.
        unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  (* [comment removed for export] *)
  Lemma L_SGN : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (c = 43 \/ c = 45)%Z ->
    scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
        (if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 112)) fc None m (seg_rom img_segs)).
  Proof.
    intros until f. intros FI FC RJ Hk Hst Hc HT.
    pose proof (RFI_getc T txt p J BYT Hp Hnul k c f RJ ltac:(lia)) as RJ1.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    assert (Rneg : (0 <= b2z (c =? 45)%Z <= 1)%Z) by (unfold b2z; destruct (c =? 45)%Z; lia).
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T p true f)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. zs. br01 K.
      (nelim (rf_getc_slow T txt p J Hp T1 k c f RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      zs. zs. callw (eapply SPEC_shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
      zs. zs. zs. fixw2.
      let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
      zs. brf K2.
      + (* [comment removed for export] *) eapply L_E4 with (k := (k + 1)%Z); try eassumption; try glia. 1: mk_finv.
        replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
      + eapply L_C4 with (k := (k + 1)%Z); try eassumption; try glia; try mlia2. mk_finv.
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp k c f RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp k c f RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read img_segs _ T (zbytes txt) (sh_rpos f) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs. zs. fixw2.
      let v := getreg 20%Z in replace v with (Z_to_bv 64 (b2z (c =? 45)%Z)) by (destruct Hc as [-> | ->]; reflexivity).
      zs. brf K2.
      + (* [comment removed for export] *) eapply L_C4 with (k := (k + 1)%Z); try eassumption; try glia; try mlia2.
        1: mk_finv. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
      + zs. eapply L_E4 with (k := (k + 1)%Z); try eassumption; try glia.
        1: mk_finv. 1: unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells.
        replace (nz pok) with false in HT by (unfold nz; destruct (Z.eqb_spec pok 0); [reflexivity|mlia2]). rewrite Bool.andb_false_r in HT. exact HT.
  Qed.

  (* [comment removed for export] *)
  Lemma L_6c : forall m j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1 k c f,
    finv m j8 -> rw_cells img_segs m Fp (rf_cells T p true f J) -> RFJ' k c f -> (2 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (-1 <= c < 256)%Z -> c <> 43%Z ->
    (c = 45%Z -> scanexp_tail fuelc (b2z (c =? 45)%Z) (fst (sh_getc f))
        (if negb (isdigitc (fst (sh_getc f))) && nz pok then sh_unget (snd (sh_getc f)) else snd (sh_getc f)) = Some (fR, e10)) ->
    (c <> 45%Z -> scanexp_tail fuelc 0%Z c f = Some (fR, e10)) ->
    evt img_segs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 c) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 (sym 0x1fe6c + 104)) fc None m (seg_rom img_segs)).
  Proof.
    intros until f. intros FI FC RJ Hk Hst Hc H43 H45 Hother.
    pose proof FI as FI'. dest_finv FI'.
    zs. zs. brfw K.
    - (* [comment removed for export] *)
      zs. zs. fixw2. zs.
      eapply L_E4 with (k := k) (neg := 0%Z); try eassumption; try glia. apply Hother. mlia2.
    - eapply L_SGN with (k := k); try eassumption; try glia. 1: right; mlia2. apply H45. mlia2.
  Qed.

  Lemma L_main : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells img_segs m0 Fp (rf_cells T p true f0 J) -> RFJ' kmin0 c0 f0 -> (1 <= kmin0)%Z -> c0 <> 0%Z ->
    bytes_at img_segs m0 T (zbytes txt) -> ssp_cells m0 canary ->
    stk img_segs m0 (q - SCANEXP_DEPTH) q -> mem_inv img_segs m0 ->
    evt img_segs POST
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SCANEXP) fc None m0 (seg_rom img_segs)).
  Proof.
    intros until t6. intros FC RJ Hk Hc0nz BY [SSP1 SSP2] ST MI.
    pose proof (munch_refl [(q - SCANEXP_DEPTH, q); (Fp, Fp + 232)]%Z m0) as MU. pose proof (wmono_refl img_segs m0) as WM.
    unfold SCANEXP, SCANEXP_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
    assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length. unfold zlength in *.
    pose proof HM as HT. rewrite scanexp_eq, (surjective_pairing (sh_getc f0)) in HT. cbn beta iota zeta in HT.
    pose proof (RFI_getc T txt p J BYT Hp Hnul kmin0 c0 f0 RJ Hc0nz) as RJ1.
    pose proof (stdio_getc f0) as Hst1.
    assert (Rc' : (-1 <= fst (sh_getc f0) < 256)%Z) by ((nelim RJ1 3%nat; intros _ R _); exact R).
    (* [comment removed for export] *)
    assert (JS : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
      finv m2 j8 -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
      (fst (sh_getc f0) = 43 \/ fst (sh_getc f0) = 45)%Z ->
      evt img_segs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 (sym 0x1fe6c + 112)) fc None m2 (seg_rom img_segs))).
    { intros until x1. intros FI2 FC2 H4345.
      eapply L_SGN with (k := (kmin0 + 1)%Z); try eassumption; try glia.
      replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
        by (symmetry; destruct H4345 as [E|E]; rewrite E; reflexivity).
      rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT. }
    assert (J6 : forall m2 j8 (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x28 x29 x30 x31 : word) x1,
      finv m2 j8 -> rw_cells img_segs m2 Fp (rf_cells T p true (snd (sh_getc f0)) J) ->
      (fst (sh_getc f0) <> 43)%Z ->
      evt img_segs POST
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 pok) x10 x11 x12 x13 x14 x15 x16 x17
                 (Z_to_bv 64 (fst (sh_getc f0))) x19 x20 x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 (sym 0x1fe6c + 104)) fc None m2 (seg_rom img_segs))).
    { intros until x1. intros FI2 FC2 H43.
      eapply L_6c with (k := (kmin0 + 1)%Z); try eassumption; try glia.
      - intros E45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with true in HT
          by (symmetry; rewrite E45; reflexivity).
        rewrite (surjective_pairing (sh_getc (snd (sh_getc f0)))) in HT. cbn beta iota zeta in HT. exact HT.
      - intros N45. replace (((fst (sh_getc f0) =? 43) || (fst (sh_getc f0) =? 45))%Z) with false in HT
          by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; assumption).
        cbn beta iota zeta in HT. exact HT. }
    site_facts FC RJ kmin0 c0 f0.
    zs. carve_frame 80%nat ST.
    do 9 zs.
    zs.
    destruct (Z.eq_dec (T + sh_rpos f0) (rf_rend T p true f0)) as [SLOW|FAST].
    - (* [comment removed for export] *)
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. zs. br01 K.
      (nelim (rf_getc_slow T txt p J Hp T1 kmin0 c0 f0 RJ SLOW) 5%nat; intros STD EJ Hn Hrp Hc0).
      destruct (ST0 STD) as [TXT Hpre].
      zs. zs. callw (eapply SPEC_shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rewrite <- EJ in H; rename H into FC end.
      zs. zs. zs. brfw K2.
      + eapply JS; [mk_finv | exact FC | left; mlia2].
      + eapply J6; [mk_finv | exact FC | mlia2].
    - (* [comment removed for export] *)
      pose proof (rf_getc_fast_lt T txt p J Hp kmin0 c0 f0 RJ ltac:(lia) FAST) as LT.
      rewrite (rf_getc_fast T txt p J Hp kmin0 c0 f0 RJ FAST) in *. cbn [fst snd] in *.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f0)) ltac:(apply Shgetc_lemmas.znth_In'; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. zs. br10 K.
      zs. zs.
      pose proof (u8ro_read img_segs _ T (zbytes txt) (sh_rpos f0) _ _ BY (Shgetc_lemmas.zbytes_nth txt (sh_rpos f0) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (Shgetc_lemmas.unsigned_lit8 (znth txt (sh_rpos f0))) by lia. clear RDb.
      zs. zs. brf K2.
      + eapply J6; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | mlia2].
      + zs. eapply JS; [mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | left; mlia2].
  Qed.
End Scanexp.

Lemma scanexp_rspec : scanexp_rstmt.
Proof.
  unfold scanexp_rstmt. intros.
  eapply L_main; eassumption.
Qed.

(* [comment removed for export] *)
Definition scanexp_rspec_c : Prop := scanexp_rstmt.
Lemma scanexp_rspec_c_ok : scanexp_rspec_c.
Proof. exact scanexp_rspec. Qed.


End Img.
(* [comment removed for export] *)
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ =>
      replace cs with cs' by (repeat (reflexivity || lazymatch goal with |- @eq Z _ _ => fail | _ => f_equal end); lia); exact H end
  end.

(* [comment removed for export] *)
Existing Class scanexp_rspec_c.
