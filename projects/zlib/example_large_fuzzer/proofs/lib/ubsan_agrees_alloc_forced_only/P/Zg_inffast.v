(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_pro Zg_inffast_exit Zg_inffast_copy Zg_inffast_model Zg_inffast_win Zg_inffast_dist Zg_inffast_len Zg_inffast_loop.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem RefInffast_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem inflate_fast_proof : inflate_fast_stmt.
Proof.
  intros X s c r ra x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m HMEM XO HRS HT FOK.
  pose proof HMEM as (_ & _ & _ & _ & _ & _ & MU & WM). cbn [w_s w_c w_r] in MU, WM.
  pose proof HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  pose proof HRS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6). ix_open XO.
  set (sv := mkFS ra x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27).
  (* [comment removed for export] *)
  eapply evt_cut; [eapply (ff_prologue X s c r); eassumption|].
  intros ms1 (y1 & y7 & y21 & y25 & y26 & y27 & m1 & -> & MU1 & WM1 & MI1 & HM1 & FRM1 & STK1 & Gl1 & Gw1). fold sv in HM1.
  (* [comment removed for export] *)
  assert (FI0 : FINV X s c (ff0_of s c)).
  { unfold FINV, ff0_of. cbn [f_bits f_hold f_in f_out f_ob]. rewrite <- Q5, <- Q6 in *. rewrite Q3 in *.
    repeat (split; [lia|]). exact Bout. }
  set (N := 8 * ic_avail_in c + ic_avail_out c + 80).
  assert (LOK : loop_ok (ffx_of s c r) s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) N (ff0_of s c) = true)
    by (rewrite <- ff_ok_loop_ok; exact FOK).
  eapply evt_cut; [eapply (Zg_inffast_loop.ff_loop X s c r sv (Z.to_nat N) N (ff0_of s c) _ _ _ _ _ _ m1 XO HRS HT FI0 HM1 ltac:(lia) LOK)|].
  intros ms2 LP. unfold loop_post in LP.
  destruct (ffL (ffx_of s c r) s N (ff0_of s c)) as [f' mm] eqn:EL.
  destruct LP as (z1 & z5 & z7 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m2 & -> & MU2 & WM2 & MI2 & HM2 & FI2 & XOK).
  (* [comment removed for export] *)
  destruct FRM1 as (jf & FRM1). unfold iframe_cells in FRM1. unfold ffWb in MU2. unfold ff_sp in *.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  eapply rw_cells_transport in FRM1; [| exact MU2| exact WM2| cbn [disjoint_from]; cells_cbv; slia].
  eapply stk_transport_disjoint in STK1; [| exact MU2| exact WM2| cbn [disjoint_from]; slia].
  eapply (ilens_munch m1 m2 (ix_L X) s) in Gl1; [| exact MU2| exact WM2| cbn [disjoint_from]; slia].
  eapply (iwork_munch m1 m2 (ix_L X) s) in Gw1; [| exact MU2| exact WM2| cbn [disjoint_from]; slia].
  assert (MU02 : munch (ix_W X) (ix_m0 X) m2).
  { eapply munch_trans; [| eapply munch_weaken; [|exact MU2]; unfold sub_fp, ix_W; cbn [outside]; intros; lia].
    eapply munch_trans; [exact MU| eapply munch_weaken; [|exact MU1]; unfold sub_fp, ix_W; cbn [outside]; intros; lia]. }
  assert (WM02 : wmono psegs (ix_m0 X) m2) by (eapply wmono_trans; [eapply wmono_trans; [exact WM| exact WM1]| exact WM2]).
  (* [comment removed for export] *)
  eapply evt_mono; [eapply (ff_exit X s c r sv f' mm); first [eassumption | exists jf; unfold iframe_cells; exact FRM1]|].
  intros ms3 (w5 & w6 & w7 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w28 & w29 & w30 & w31 & m3 & -> & MU3 & WM3 & MI3 & HIM).
  (* [comment removed for export] *)
  unfold inflate_fast_post. subst sv. cbn [fs_ra fs_x8 fs_x9 fs_x18 fs_x19 fs_x20 fs_x21 fs_x22 fs_x23 fs_x24 fs_x25 fs_x26 fs_x27].
  do 16 eexists. split; [reflexivity|].
  assert (EIF : inflate_fast (mkW s c r) = ff_post s c r (ffx_of s c r) (ff_fin f') mm).
  { rewrite inflate_fast_eq. rewrite ff_loop_ffL. fold N. rewrite EL. reflexivity. }
  rewrite EIF. split; [exact HIM|].
  destruct FI2 as (Gb & Gh & Gin & Gout & Gob & Gbytes).
  unfold ff_post, ff_fin; destruct mm as [[md [g|]]|];
    cbn [w_c ic_input ic_outbuf ic_next_out icset_outbuf icset_next_in icset_next_out icset_avail_in icset_avail_out icset_msg
         f_ob f_out f_in f_bits f_hold fset_in fset_bits fset_hold];
    (split; [reflexivity|]); (split; [exact Gob|]); (split; [lia|]); exact Gbytes.
Qed.
