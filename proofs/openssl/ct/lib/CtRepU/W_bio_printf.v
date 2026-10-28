(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition BIO_PRINTF : Z := 0x10df8c.
Definition BIO_VPRINTF : Z := 0x10dfd0.
(* [comment removed for export] *)
Definition BIO_PRINTF_STACK : Z := 672 + VSN_DEPTH.

(* [comment removed for export] *)
Definition printf_call_ok (m : mem) (lo q A : Z) (fmt : list Z) (slots : list word) (args : list parg) (o : list Z) : Prop :=
  bytes_at ctusegs m A (zb fmt) /\ Forall (fun c => 0 <= c < 256) fmt /\ pass1x_ok fmt = true
  /\ (65536 <= A /\ A + zlength fmt <= STATIC_SPLIT)
  /\ (forall m', munch [(lo, q)] m m' -> args_ok 0 0 0 m' lo (q - 672) 0 slots args)
  /\ printf_modelx OUT_sn OUTFP_sn fmt args [] = ITree.Ret (Ok (zlength o, o))
  /\ fp_callsx (length fmt) fmt args = []
  /\ (length o < 512)%nat.

Definition bio_printf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (W : list (Z * Z)) (canary : word) (r : Z) (fin : mem -> Prop) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             Ft (ret_pc ra) fc' None m' (seg_rom ctusegs)
    /\ munch ((lo, bv_unsigned sp) :: W) m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
    /\ stk ctusegs m' lo (bv_unsigned sp) /\ ssp_cells m' canary /\ fin m'.

(* [comment removed for export] *)
Lemma BIO_printf_null_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (out pv nw A lo : Z) (canary : word) (fmt : list Z) (args : list parg) (o : list Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> (lo <= bv_unsigned sp - BIO_PRINTF_STACK)%Z -> (bv_unsigned sp < 2^63)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  ssp_cells m canary -> frm0 fc ->
  rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw) -> obj_range out BIO_SIZE lo -> (out mod 8 = 0)%Z -> (0 <= nw < 2^64)%Z ->
  null_meth_cells m ->
  printf_call_ok m lo (bv_unsigned sp) A fmt [a2; a3; a4; a5; a6; a7] args o ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 A ->
  evt ctusegs (bio_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo [(out, out + 128)] canary (zlength o)
                 (fun m' => rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + zlength o))) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BIO_PRINTF) fc None m (seg_rom ctusegs)).
Proof.
  intros until o. intros ST MI GLO LO SP63 SP16 [SSP1 SSP2] FRM HO HOLO HOAL NW [HM1 HM2] (HF & FB & P1 & AR & AOK & MODEL & FPC & OLEN) -> ->.
  pose proof HOLO as HOLO'. unfold obj_range in HOLO'.
  unfold BIO_PRINTF_STACK, VSN_DEPTH, BIO_PRINTF, GLOBALS_TOP, BIO_SIZE, STATIC_SPLIT in *.
  pose proof (munch_refl [(lo, bv_unsigned sp); (out, out + 128)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as MU1.   (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (SEPO : out + 128 <= lo \/ bv_unsigned sp <= out) by lia.
  pose proof (bytes_at_bound _ _ _ _ HF) as FBD. unfold zb in FBD. rewrite length_map in FBD.
  assert (SEPF : A + Z.of_nat (length (zb fmt)) <= lo \/ bv_unsigned sp <= A) by (unfold zb; rewrite length_map; unfold zlength in AR; lia).
  unfold got_ssp in SSP1. unfold ssp_guard in SSP2.
  assert (SEPG : 3271976 + 8 <= lo \/ bv_unsigned sp <= 3271976) by lia.
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.
  unfold NULL_METHOD in HM1, HM2. change (2978032 + 16) with 2978048 in HM1. change (2978032 + 48) with 2978080 in HM2.
  unfold BWRITE_CONV, NULL_WRITE, NULL_PUTS, MallocRep.wz in HM1, HM2.
  assert (SEPM : 2978032 + 72 <= lo \/ bv_unsigned sp <= 2978032) by lia.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HO.
  (* [comment removed for export] *)
  carve_frame 80%nat ST. do 4 zstep. do 6 zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 592%nat ST. do 9 zstep. do 3 zstep. zstep. zstep. (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  name_mem m1.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB ctusegs m1 _ [] 520 _ _ [8; 512]%nat) in FR0; [| reflexivity]. cbn [mk_CB_cells app] in FR0.
  lazymatch type of FR0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0] (c1 :: rest)) FR0) as [FRa FRb]; clear FR0;
    pose proof (proj1 (rw_cells_app m1 _ [c1] rest) FRb) as [FRD FRc]; clear FRb end.
  cbn [cells_size csize Nat.add] in FRD, FRc.
  replace (bv_unsigned sp + -672 + Z.of_nat 8) with (bv_unsigned sp + -664) in FRD by lia.
  replace (bv_unsigned sp + -672 + Z.of_nat 8 + Z.of_nat 512) with (bv_unsigned sp + -152) in FRc by lia.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    pose proof (proj1 (rw_cells_app m1 _ [c0; c1; c2; c3] rest) FR) as [FRp HVA]; clear FR end.
  cbn [cells_size csize Nat.add] in HVA. replace (bv_unsigned sp + -80 + Z.of_nat 32) with (bv_unsigned sp + -48) in HVA by lia.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -672)) = bv_unsigned sp + -672) by (apply unsigned_lit; lia).
  pose proof vsnprintf_proof as VS. unfold vsnprintf_stmt in VS.
  eapply evt_cut.
  { lazymatch type of FRD with rw_cells _ _ _ [CB _ ?jd] =>
    eapply (VS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              (bv_unsigned sp + -664) 512 A (bv_unsigned sp + -48) 512%nat jd fmt [a2; a3; a4; a5; a6; a7] args lo canary (zlength o) o) end;
    rewrite ?ESP;
      [reflexivity| reflexivity| reflexivity| reflexivity| exact FRD| exact HF| exact FB| exact P1
      | exact (proj2 (proj1 HVA))
      | intros m' MU'; apply AOK; eapply munch_trans; [exact MU1| eapply munch_weaken; [| exact MU']; unfold VSN_W, sub_fp; cbn [outside]; intros y Hy; lia]
      | exact MODEL| exact FPC| exact OLEN| unfold zlength; lia| lia
      | exact ST| unfold VSN_DEPTH; lia| unfold GLOBALS_TOP; lia| lia
      | split; [exact SSP1| exact SSP2]| eassumption| exact FRM
      | lia| unfold STATIC_SPLIT; lia| lia| change (zlength [a2; a3; a4; a5; a6; a7]) with 6; lia
      | lia| change (zlength [a2; a3; a4; a5; a6; a7]) with 6; lia| unfold GLOBALS_TOP; lia]. }
  clear VS FRD. post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo (bv_unsigned sp + -672) |- _ => rename H into ST end.
  match goal with H : frm0 _ |- _ => rename H into FRM' end.
  match goal with H : forall k : reg, _ -> reg_get _ k = reg_get F k |- _ => rename H into FREG end.
  match goal with H : ssp_cells _ canary |- _ => destruct H as [SSP1' SSP2'] end.
  name_mem m2.
  assert (OZ : 0 <= zlength o < 512) by (unfold zlength; clear - OLEN; lia).
  (* [comment removed for export] *)
  zstep. zstep. if_cases K; zify_cond K; [exfalso; clear - K OZ; lia| try clear K].
  zstep. zstep. if_cases K; zify_cond K; [| exfalso; clear - K OZ; rewrite ?unsigned_lit in K by lia; lia]. try clear K.
  zstep. zstep. zstep. (* [comment removed for export] *)
  name_mem m3. clear MU1.
  assert (TAILK : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m4,
    munch [(bv_unsigned sp + -672 - 144, bv_unsigned sp + -672); (out, out + 128)]%Z m3 m4 -> wmono ctusegs m3 m4 -> mem_inv ctusegs m4 ->
    stk ctusegs m4 lo (bv_unsigned sp + -672) ->
    rw_cells ctusegs m4 out (bio_null_cells NULL_METHOD pv (nw + zlength o)) ->
    evt ctusegs (bio_printf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo [(out, out + 128)] canary (zlength o)
                   (fun m' => rw_cells ctusegs m' out (bio_null_cells NULL_METHOD pv (nw + zlength o))) m)
      (MS (mkR (Z_to_bv 64 1106080) (Z_to_bv 64 (bv_unsigned sp + -672)) gp tp t0' t1' t2' (Z_to_bv 64 (bv_unsigned sp + -80)) (Z_to_bv 64 out)
               (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 512) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          x13 (Z_to_bv 64 1106080) x14 None m4 (seg_rom ctusegs))).
  { intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m4 MU4 WM4 MI4 ST4 HO4.
    clear ST HO. transport_after_call ctusegs m3 m4 MU4 WM4. clear MU4 WM4.
    match goal with H : rw_cells ctusegs m4 (bv_unsigned sp + -664) _ |- _ => rename H into FRD end.
    (* [comment removed for export] *)
    replace (bv_unsigned sp + -152) with (bv_unsigned sp + -664 + Z.of_nat 512) in FRc by lia.
    pose proof (proj2 (rw_cells_app m4 _ _ _) (conj FRD FRc)) as FRDc. cbn [app] in FRDc. clear FRD FRc.
    replace (bv_unsigned sp + -664) with (bv_unsigned sp + -672 + Z.of_nat 8) in FRDc by lia.
    pose proof (proj2 (rw_cells_app m4 _ _ _) (conj FRa FRDc)) as FR0. cbn [app] in FR0. clear FRa FRDc.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp + -80 + Z.of_nat 32) in HVA by lia.
    pose proof (proj2 (rw_cells_app m4 _ _ _) (conj FRp HVA)) as FR. cbn [app] in FR. clear FRp HVA.
    zstep. zstep. do 7 zstep. zstep. release_frame FR0 ST4 (bv_unsigned sp + -80). zstep.
    replace (ret_pc (Z_to_bv 64 1105856)) with (Z_to_bv 64 1105856) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. release_frame FR ST4 (bv_unsigned sp). zstep.
    apply evt_done. unfold bio_printf_post.
    do 14 eexists. exists x13, x14. eexists. split; [reflexivity|].
    split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact FRM'|]. split; [exact FREG|].
    split; [exact ST4|]. split; [split; assumption| exact HO4]. }
  destruct o as [|c o'] eqn:Eo.
  - (* [comment removed for export] *)
    eapply evt_cut; [eapply BIO_write_zero_spec; [eassumption| reflexivity]|].
    intros ms' PO. destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & -> & MUc & WMc & MIc).
    replace (ret_pc (Z_to_bv 64 1106080)) with (Z_to_bv 64 1106080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    cbn [zlength length Z.of_nat] in TAILK |- *. eapply (TAILK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4).
    + eapply munch_weaken; [| exact MUc]. unfold sub_fp. cbn [outside]. intros y Hy. exact I.
    + exact WMc. + exact MIc.
    + eapply stk_transport_disjoint; [exact ST| exact MUc| exact WMc| exact I].
    + rewrite Z.add_0_r. unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz. eapply rw_cells_transport; [exact HO| exact MUc| exact WMc| exact I].
  - rewrite <- Eo in *.
    eapply evt_cut.
    { eapply BIO_write_null_spec with (lo := lo) (out := out) (dlen := zlength o);
        [rewrite ESP; exact ST| eassumption| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_WRITE_NULL_STACK; lia
        | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
        | exact HO| exact HOLO| exact HOAL| exact NW| split; [exact HM1| exact HM2]| reflexivity| reflexivity
        | clear - OZ Eo; subst o; unfold zlength in *; cbn [length] in *; lia]. }
    intros ms' PO. destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & -> & MUc & WMc & MIc & STc & HOc).
    rewrite ?ESP in MUc, STc.
    replace (ret_pc (Z_to_bv 64 1106080)) with (Z_to_bv 64 1106080) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply (TAILK _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4); [exact MUc| exact WMc| exact MIc| exact STc| exact HOc].
Qed.
End WithCeiling0.
