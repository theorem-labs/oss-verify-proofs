(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Decode Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import STRW_tac.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface ECH_AImg F_time AsAuxv.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_rip N6_strlen F_strspn.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import InNth.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Lemma au64s_read : forall m A ws (i : Z) w a,
  bytes_at asegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes asegs m a 8 = Some (le8 w).
Proof.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read asegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amo_aligned_Z : forall wd z, 0 <= z < 2^64 -> z mod amo_bytes wd = 0 -> amo_aligned wd (Z_to_bv 64 z) = true.
Proof. intros wd z Hz Hm. unfold amo_aligned. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.
Ltac amo_fix :=
  repeat match goal with
  | |- context [amo_aligned ?wd (Z_to_bv 64 ?z)] =>
      rewrite (amo_aligned_Z wd z) by (first [cbn [amo_bytes]; lia | cbn [amo_bytes]; nia]); cbn [negb]
  end;
  repeat match goal with
  | |- context [Z.eqb ?x ?x] => rewrite (Z.eqb_refl x)
  end;
  cbv beta iota delta [amo_val inval_resv with_resv c_resv].
Ltac astep_core segs R F pc fc rv m ro :=
  let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch fw with
  | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i; exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          amo_fix; simp_regs;
          try solve_load; try solve_store; reflexivity
        | simp_regs; vnorm_for i; mem_after_store_opt; post_step i ]
      | None => fail "undecodable instruction at" pc
      end
  | None => fail "no instruction at" pc
  end.
Ltac astep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => astep_core segs R F pc fc rv m ro
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition vdsosym_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp).

Lemma vdsosym_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo B : Z),
  aauxv_ok m B -> bv_unsigned sp <= B ->
  stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv asegs m ->
  evt asegs (vdsosym_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_vdsosym) fc None m (seg_rom asegs)).
Proof.
  intros until B. intros AUX HB ST CLO LO MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & x25 & x0 & AVC & AVL & AB & BAV & AVH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & X25 & X0).
  acb; unfold AAUXV_CELL in *. unfold wz in AVC.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  unfold P_vdsosym.
  (* [comment removed for export] *)
  step. carve_frame 112%nat ST. do 13 step.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  Ltac key_ld i key HB addr :=
    let RD := fresh "RD" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (au64s_read mX _ _ i (wz key) (Z_to_bv 64 addr) HB eq_refl ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end;
    step; try clear RD.
  key_ld 0 3 AVL av.
  (* [comment removed for export] *)
  step. change (bv_eqb (wz 3) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  Ltac skip key i nkey HB avv :=
    step; change (bv_eqb (wz key) (Z_to_bv 64 33)) with false; cbv iota;
    step;
    key_ld i nkey HB (avv + 8 * i)%Z;
    step; change (negb (bv_eqb (wz nkey) (Z_to_bv 64 0))) with true; cbv iota.
  skip 3 2 4 AVL av. skip 4 4 5 AVL av. skip 5 6 16 AVL av. skip 16 8 6 AVL av. skip 6 10 11 AVL av.
  skip 11 12 12 AVL av. skip 12 14 23 AVL av. skip 23 16 25 AVL av.
  (* [comment removed for export] *)
  step. change (bv_eqb (wz 25) (Z_to_bv 64 33)) with false. cbv iota.
  step. key_ld 18 0 AVL (av + 8 * 18)%Z.
  step. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  step.
  (* [comment removed for export] *)
  do 17 step.
  release_frame FR ST (bv_unsigned sp).
  unfold vdsosym_post. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cgt_init_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-38)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 144, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp) /\ rw_cells asegs m' A_vdso_func [C8 (Z_to_bv 64 0)].

Lemma cgt_init_spec : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo B : Z),
  aauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells asegs m A_vdso_func [C8 (Z_to_bv 64 P_cgt_init)] ->
  stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 144 -> mem_inv asegs m ->
  evt asegs (cgt_init_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_cgt_init) fc None m (seg_rom asegs)).
Proof.
  intros until B. intros AUX HB VF ST CLO LO MI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  acb; unfold A_vdso_func, P_cgt_init in *.
  pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (0x5edf88, 0x5edf88 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  step. carve_frame 32%nat ST. do 9 step.
  (* [comment removed for export] *)
  step.
  assert (AUX1 : aauxv_ok m0 B).
  { eapply aauxv_ok_frame; [exact AUX| exact MU| exact WM|].
    constructor; [apply aauxv_win_ok_stack; lia|]. constructor; [| constructor]. apply aauxv_win_ok_low; [lia | unfold A_vdso_func in *; lia | unfold AAUXV_CELL; cbn; lia]. }
  eapply evt_cut.
  { eapply (vdsosym_spec _ _ gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 lo B AUX1);
      rewrite ?unsigned_lit by lia; [lia| exact ST| exact CLO| lia| exact MI]. }
  intros ms1 PV. unfold vdsosym_post in PV.
  destruct PV as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m1 & -> & MU1 & WM1 & MI1 & ST1).
  rewrite unsigned_lit in MU1, ST1 by lia.
  replace (ret_pc (Z_to_bv 64 5694760)) with (Z_to_bv 64 5694760) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (FR1 : rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 s1; C8 s0; C8 ra]).
  { eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]. cbn. lia. }
  assert (VF1 : rw_cells asegs m1 6217608 [C8 (Z_to_bv 64 5694716)]).
  { eapply rw_cells_transport; [exact VF| exact MU1| exact WM1|]. cbn. lia. }
  assert (MU' : munch [(bv_unsigned sp - 144, bv_unsigned sp); (6217608, 6217608 + 8)]%Z m m1).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros x Hx. cbn in Hx |- *. lia. }
  assert (WM' : wmono asegs m m1) by (eapply wmono_trans; [exact WM| exact WM1]).
  clear MU WM MU1 WM1 FR VF MI ST AUX AUX1.
  (* [comment removed for export] *)
  step. step. step. step. step.
  (* [comment removed for export] *)
  astep. step. if_false. astep. step. if_false. step. if_true.
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  lazymatch goal with H : rw_cells asegs ?mX (bv_unsigned sp + -32) _, S : stk asegs ?mX lo _ |- _ => release_frame H S (bv_unsigned sp) end.
  unfold cgt_init_post, A_vdso_func. finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ATS : Z := 2192.   (* [comment removed for export] *)
Definition APAT : Z := 0xaaaaaaaaaaaaaaaa.   (* [comment removed for export] *)

Definition atime_front_post (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word) (F : bvmap 5 word) (fc : bv 32)
    (lo can : Z) (errv : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (x1 x5 x6 x7 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word) m1 (junk16 junk8 junkA junkB : list byte),
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0)
                  (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2192)) x12 x13 x14 x15 x16 (Z_to_bv 64 113)
                  s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x56e494) fc None m1 (seg_rom asegs)
    /\ rw_cells asegs m1 (bv_unsigned sp + -2192) [CB 16 junk16; C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 0x1ac30c)]
    /\ rw_cells asegs m1 (bv_unsigned sp + -2224) [CB 8 junk8; C8 (Z_to_bv 64 ACANARY_CELL); C8 (Z_to_bv 64 (bv_unsigned sp + -80)); C8 (Z_to_bv 64 0x570ba8)]
    /\ rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 2064 junkA; C8 (Z_to_bv 64 APAT); CB 8 junkB; C8 s6; C8 s5; C8 s4v; C8 s3; C8 s2; C8 s1v; C8 s0v; C8 rav]
    /\ rw_cells asegs m1 A_vdso_func [C8 (Z_to_bv 64 0)]
    /\ rw_cells asegs m1 AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] /\ rw_cells asegs m1 ACANARY_CELL [C8 (Z_to_bv 64 can)]
    /\ rw_cells asegs m1 (errno_addr tp) [C4 errv]
    /\ munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -2224) /\ ACONST m1 /\ aauxv_ok m1 (bv_unsigned sp).

Lemma atime_front : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (lo B vf can : Z) (errv : word),
  aauxv_ok m B -> bv_unsigned sp <= B ->
  rw_cells asegs m A_vdso_func [C8 (Z_to_bv 64 vf)] -> (vf = 0 \/ vf = P_cgt_init) ->
  rw_cells asegs m AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] -> rw_cells asegs m ACANARY_CELL [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
  rw_cells asegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 ATP ->
  stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - ATIME_STACK -> mem_inv asegs m -> a0 = Z_to_bv 64 0 ->
  ACONST m ->
  evt asegs (atime_front_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 s4 F fc lo can errv m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 P_time) fc None m (seg_rom asegs)).
Proof.
  intros until errv. intros AUX HB VF HVF GOT CAN CANR ERR TP ST CLO LO MI A0 AC. subst a0.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  acb. unfold A_vdso_func, P_cgt_init, AGOT_SSP_CELL, ACANARY_CELL, P_time, ATIME_STACK in *.
  assert (ETP : errno_addr tp = AERRNO) by (rewrite TP; unfold errno_addr, ATP, AERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR. unfold AERRNO, ATP in ERR.
  destruct (ACONST_layout m AC) as (G1 & K1 & G2 & G3 & G4 & K4).
  assert (C5 : rw_cells asegs m AINITED_CELL [Cells.C1 (Z_to_bv 8 1); Cells.C1 (Z_to_bv 8 1)]) by (eapply ACONST_cell; [exact AC| in_nth]). unfold AINITED_CELL in C5.
  pose proof (ACONST_cell m ATIMEP_CELL _ AC ltac:(in_nth)) as CT. unfold ATIMEP_CELL, AREAL_TIME, wz in CT.
  pose proof (munch_refl [(bv_unsigned sp - 8192, bv_unsigned sp); (0x5edf88, 0x5edf88 + 8)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  step.
  (* [comment removed for export] *)
  step. carve_frame 2144%nat ST. do 8 step. step. step. step.
  (* [comment removed for export] *)
  destruct (stk_split asegs _ _ (bv_unsigned sp + -2144 - 16) _ ST ltac:(lia)) as [STlo SThi].
  zstep. call2 tryinit_body; try eassumption; rewrite ?unsigned_lit by lia; [exact SThi | lia |].
  try rewrite unsigned_lit in * by lia.
  match goal with Hhi : stk asegs ?mx (bv_unsigned sp + -2144 - 16) (bv_unsigned sp + -2144),
                  Hlo : stk asegs ?mx lo (bv_unsigned sp + -2144 - 16) |- _ =>
    pose proof (stk_merge asegs _ _ _ _ Hlo Hhi ltac:(lia)) as ST; clear Hlo Hhi end.
  (* [comment removed for export] *)
  zstep. if_cases K0; [exfalso; revert K0; vm_compute; discriminate|]. clear K0.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (RO : ro_cells asegs mX 0x10640 [C8 (Z_to_bv 64 APAT)]);
    [ lazymatch goal with MIx : mem_inv asegs mX |- _ =>
        pose proof (ro_cells_image asegs mX 0x10640 (le8 (Z_to_bv 64 APAT)) MIx ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO0 end;
      destruct RO0 as [_ RB]; split; [cbn; repeat split; exact I | exact RB] |] end.
  step. step.
  (* [comment removed for export] *)
  step. step. step. step. step.
  (* [comment removed for export] *)
  step. carve_frame 48%nat ST. do 10 lstep.
  (* [comment removed for export] *)
  step. lstep. carve_frame 32%nat ST. do 7 lstep.
  assert (AW : Forall aconst_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z).
  { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    constructor; [| constructor].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
      AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
  assert (AXW : Forall (aauxv_win_ok B) [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z).
  { constructor; [apply aauxv_win_ok_stack; lia|]. constructor; [| constructor].
    apply aauxv_win_ok_low; [exact (aauxv_ok_bounds _ _ AUX)| lia| left; unfold AAUXV_CELL; lia]. }
  assert (FIN : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j16 j8 jA jB : list byte) mX,
    rw_cells asegs mX (bv_unsigned sp + -2192) [CB 16 j16; C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 1753868)] ->
    rw_cells asegs mX (bv_unsigned sp + -2224) [CB 8 j8; C8 (Z_to_bv 64 12590288); C8 (Z_to_bv 64 (bv_unsigned sp + -80)); C8 (Z_to_bv 64 5704616)] ->
    rw_cells asegs mX (bv_unsigned sp + -2144) [CB 2064 jA; C8 (Z_to_bv 64 APAT); CB 8 jB; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells asegs mX 6217608 [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs mX 6199192 [C8 (Z_to_bv 64 12590288)] -> rw_cells asegs mX 12590288 [C8 (Z_to_bv 64 can)] ->
    rw_cells asegs mX (12459152 - 164) [C4 errv] ->
    munch [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z m mX -> wmono asegs m mX -> mem_inv asegs mX ->
    stk asegs mX lo (bv_unsigned sp + -2224) ->
    evt asegs (atime_front_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 ra s0 s1 s4 F fc lo can errv m)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0) x10 x11 x12 x13 x14 x15 x16 x17
               s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 5694600) fc None mX (seg_rom asegs))).
  { intros. (* [comment removed for export] *)
    step. step. step. apply evt_done. unfold atime_front_post, A_vdso_func, AGOT_SSP_CELL, ACANARY_CELL, ATIME_STACK.
    do 18 eexists. split; [reflexivity|].
    repeat (split; [eassumption|]).
    split. { rewrite TP. unfold errno_addr, ATP. rewrite unsigned_lit by lia. eassumption. }
    repeat (split; [eassumption|]).
    split. { eapply ACONST_frame; [exact AC| eassumption| eassumption| exact AW]. }
    eapply aauxv_ok_weaken; [eapply aauxv_ok_frame; [exact AUX| eassumption| eassumption| exact AXW] |].
    pose proof (aauxv_ok_bounds _ _ AUX). lia. }
  destruct HVF as [-> | ->].
  - (* [comment removed for export] *)
    step. if_true. eapply FIN; eassumption.
  - (* [comment removed for export] *)
    step. if_false. step. step. step.
    assert (AUX0 : aauxv_ok m1 B) by (eapply aauxv_ok_frame; [exact AUX| exact MU| exact WM| exact AXW]).
    eapply evt_cut.
    { eapply (cgt_init_spec _ _ gp tp t0 t1 t2 _ _ _ _ _ a3 a4 a5 a6 a7 s2 s3 _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo B AUX0);
        rewrite ?unsigned_lit by lia; [lia| unfold A_vdso_func, P_cgt_init; exact VF| exact ST| exact CLO| lia| eassumption]. }
    intros ms1 PG. unfold cgt_init_post, A_vdso_func in PG.
    destruct PG as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MU1 & WM1 & MI1 & ST1 & VF1).
    rewrite unsigned_lit in MU1, ST1 by lia.
    replace (ret_pc (Z_to_bv 64 5694580)) with (Z_to_bv 64 5694580) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    lazymatch type of FR0 with rw_cells _ _ ?A ?cs =>
      assert (FRa : rw_cells asegs m2 A cs) by (eapply rw_cells_transport; [exact FR0| exact MU1| exact WM1|]; cbn; lia) end.
    lazymatch type of FR1 with rw_cells _ _ ?A ?cs =>
      assert (FRb : rw_cells asegs m2 A cs) by (eapply rw_cells_transport; [exact FR1| exact MU1| exact WM1|]; cbn; lia) end.
    lazymatch type of FR with rw_cells _ _ ?A ?cs =>
      assert (FRc : rw_cells asegs m2 A cs) by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1|]; cbn; lia) end.
    assert (GOT1 : rw_cells asegs m2 6199192 [C8 (Z_to_bv 64 12590288)]) by (eapply rw_cells_transport; [exact GOT| exact MU1| exact WM1|]; cbn; lia).
    assert (CAN1 : rw_cells asegs m2 12590288 [C8 (Z_to_bv 64 can)]) by (eapply rw_cells_transport; [exact CAN| exact MU1| exact WM1|]; cbn; lia).
    assert (ERR1 : rw_cells asegs m2 (12459152 - 164) [C4 errv]) by (eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]; cbn; lia).
    assert (MU' : munch [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z m m2).
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. intros xq Hxq. cbn in Hxq |- *. lia. }
    assert (WM' : wmono asegs m m2) by (eapply wmono_trans; [exact WM| exact WM1]).
    clear MU WM MU1 WM1 FR FR0 FR1 GOT CAN ERR VF ST AUX0.
    repeat match goal with H : mem_inv asegs m1 |- _ => clear H | H : chunk_disj _ _ _ _ |- _ => clear H | H : chunk_in _ _ _ |- _ => clear H
                         | H : rw_cells asegs m1 _ _ |- _ => clear H | H : ro_cells asegs m1 _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    step. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
    step. step. if_cases K3; zify_cond K3. 2:{ exfalso. revert K3. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
    eapply FIN; eassumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition atime_back_post (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word) (F : bvmap 5 word) (fc : bv 32)
    (lo B : Z) (errv : word) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 (tv : word) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v tv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4v s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ ACONST m'
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv] /\ aauxv_ok m' B
    /\ munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m0 m' /\ wmono asegs m0 m'
    /\ rw_cells asegs m' A_vdso_func [C8 (Z_to_bv 64 0)].

Lemma atime_back : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x28 x29 x30 x31 : word)
    (sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 m1 : mem) (lo B can : Z) (errv : word) (bs j16 j8 jA jB : list byte),
  length bs = 16%nat ->
  rw_cells asegs m1 (bv_unsigned sp + -2192) [CB 16 j16; C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 0x1ac30c)] ->
  rw_cells asegs m1 (bv_unsigned sp + -2224) [CB 8 j8; C8 (Z_to_bv 64 ACANARY_CELL); C8 (Z_to_bv 64 (bv_unsigned sp + -80)); C8 (Z_to_bv 64 0x570ba8)] ->
  rw_cells asegs m1 (bv_unsigned sp + -2144) [CB 2064 jA; C8 (Z_to_bv 64 APAT); CB 8 jB; C8 s6; C8 s5; C8 s4v; C8 s3; C8 s2; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m1 A_vdso_func [C8 (Z_to_bv 64 0)] ->
  rw_cells asegs m1 AGOT_SSP_CELL [C8 (Z_to_bv 64 ACANARY_CELL)] -> rw_cells asegs m1 ACANARY_CELL [C8 (Z_to_bv 64 can)] -> 0 <= can < 2^64 ->
  rw_cells asegs m1 (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 ATP ->
  munch [(bv_unsigned sp - ATIME_STACK, bv_unsigned sp); (A_vdso_func, A_vdso_func + 8)]%Z m0 m1 -> wmono asegs m0 m1 -> mem_inv asegs m1 ->
  stk asegs m1 lo (bv_unsigned sp + -2224) -> aceil <= lo -> lo <= bv_unsigned sp - ATIME_STACK ->
  ACONST m0 -> aauxv_ok m0 B -> bv_unsigned sp <= B ->
  evt asegs (atime_back_post sp gp tp s2 s3 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v s4v F fc lo B errv m0)
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2224)) gp tp x5 x6 x7 (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 0)
                (Z_to_bv 64 0) (Z_to_bv 64 (bv_unsigned sp + -2192)) x12 x13 x14 x15 x16 (Z_to_bv 64 113)
                s2 s3 (Z_to_bv 64 APAT) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x56e498) fc None (write_to_mem m1 (Z_to_bv 64 (bv_unsigned sp + -2192)) bs) (seg_rom asegs)).
Proof.
  intros until jB. intros L16 FR0 FRb FRc VF GOT CAN CANR ERR TP MU WM MI ST CLO LO AC AUX HB.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  acb. unfold A_vdso_func, AGOT_SSP_CELL, ACANARY_CELL, ATIME_STACK in *.
  assert (ETP : errno_addr tp = AERRNO) by (rewrite TP; unfold errno_addr, ATP, AERRNO; rewrite unsigned_lit by lia; reflexivity).
  rewrite ETP in ERR. unfold AERRNO, ATP in ERR.
  (* [comment removed for export] *)
  destruct (proj1 (rw_cells_app asegs m1 _ [CB 16 j16] [C8 (Z_to_bv 64 can); C8 (Z_to_bv 64 0); C8 sp; C8 (Z_to_bv 64 1753868)]) FR0) as [FR16 FRr].
  cbn [cells_size csize Nat.add] in FRr. replace (bv_unsigned sp + -2192 + Z.of_nat 16) with (bv_unsigned sp + -2176) in FRr by lia. clear FR0.
  sys_mem_write. rewrite L16 in FR16. change (16 - 16)%nat with 0%nat in FR16.
  assert (AW : Forall aconst_ok [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z).
  { constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia|].
    constructor; [| constructor].
    apply aconst_ok_intro; unfold ASHBASE_CELL, AMEMCPYP_CELL, AINITED_CELL, AHIEND_CELL, ADYING_CELL, APGSZ_CELL, ACANPOISON_CELL, AF_DCO_CELL, AVERBOSITY_CELL,
      AREAL_TLSGA_CELL, ATSD_CELL, AREGISTERED_CELL, ACOVFLAG_CELL, sh, AIMG_LO, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
  assert (AXW : Forall (aauxv_win_ok B) [(bv_unsigned sp - 8192, bv_unsigned sp); (6217608, 6217608 + 8)]%Z).
  { constructor; [apply aauxv_win_ok_stack; lia|]. constructor; [| constructor].
    apply aauxv_win_ok_low; [exact (aauxv_ok_bounds _ _ AUX)| lia| left; unfold AAUXV_CELL; lia]. }
  (* [comment removed for export] *)
  step. step. step. if_cases K1; zify_cond K1. 2:{ exfalso. revert K1. rewrite ?unsigned_lit_wrap. vm_compute. discriminate. }
  (* [comment removed for export] *)
  step. step. step. step. step.
  if_true. step.
  try (replace (ret_pc (Z_to_bv 64 5694644)) with (Z_to_bv 64 5694644) by (symmetry; apply ret_pc_even; [lia| reflexivity])).
  (* [comment removed for export] *)
  step. step. step. step. step. step.
  try (replace (ret_pc (Z_to_bv 64 5704616)) with (Z_to_bv 64 5704616) by (symmetry; apply ret_pc_even; [lia| reflexivity])).
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. revert K2. rewrite ?unsigned_lit_wrap. clear - SPR CLO LO ACEILB. intros K2. lia. }
  step. step. step. step. if_cases KC; zify_cond KC. { exfalso. apply KC. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. step. step.
  try (replace (ret_pc (Z_to_bv 64 1753868)) with (Z_to_bv 64 1753868) by (symmetry; apply ret_pc_even; [lia| reflexivity])).
  (* [comment removed for export] *)
  step. if_true. step. do 8 step. step. step.
  release_frame FRb ST (bv_unsigned sp + -2192). release_frame FR16 ST (bv_unsigned sp + -2176).
  release_frame FRr ST (bv_unsigned sp + -2144). release_frame FRc ST (bv_unsigned sp).
  apply evt_done. unfold atime_back_post, A_vdso_func, ATIME_STACK. do 16 eexists. split; [reflexivity|].
  split; [exact MI|]. split; [exact ST|].
  split. { eapply ACONST_frame; [exact AC| exact MU| exact WM| exact AW]. }
  split. { rewrite TP. unfold errno_addr, ATP. rewrite unsigned_lit by lia. exact ERR. }
  split. { eapply aauxv_ok_frame; [exact AUX| exact MU| exact WM| exact AXW]. }
  split; [exact MU|]. split; [exact WM| exact VF].
Qed.
End HCW.
