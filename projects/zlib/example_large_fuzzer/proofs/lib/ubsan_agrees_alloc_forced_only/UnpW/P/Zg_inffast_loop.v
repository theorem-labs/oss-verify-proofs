(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_pure2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs Zg_inffast_exit Zg_inffast_copy. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Zg_inffast_model. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Zg_inffast_win Zg_inffast_dist Zg_inffast_len.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section LOOP.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave).
Local Notation xx := (ffx_of s c r).

(* [comment removed for export] *)
Definition loop_post (me : mem) (res : ffs * option (Z * option Z)) : machine_state -> Prop :=
  fun ms' => let '(f', mm) := res in
    exists x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
      ms' = FFX X s c r f' x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m'
      /\ munch (ffWb X) me m' /\ wmono psegs me m' /\ mem_inv psegs m'
      /\ FFMg X s c sv (brk_s s mm) (brk_c c mm) f' m' /\ FINV X s c f' /\ exit_ok f' = true.

Lemma ff_loop : forall k n f (x1 x7 x21 x25 x26 x27 : word) m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f -> FFM X s c sv f m ->
  n <= Z.of_nat k ->
  loop_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) n f = true ->
  evt psegs (loop_post m (ffL xx s n f)) (FFL X s c r f PC_FF_LOOP x1 x7 x21 x25 x26 x27 m).
Proof.
  intros k; induction k as [|k IH]; intros n f x1 x7 x21 x25 x26 x27 m XO HRS HT FI HM Hn LOK.
  { rewrite loop_ok_le0 in LOK by lia. discriminate LOK. }
  destruct (Z.le_gt_cases n 0) as [Hle|Hgt]; [rewrite loop_ok_le0 in LOK by lia; discriminate LOK|].
  rewrite loop_ok_step in LOK by lia. rewrite ffL_step by lia.
  destruct (trip_ok xx s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s)) f) eqn:TOK; [|discriminate LOK].
  pose proof (FFM_split X s c sv f m HM) as [HS HC]. pose proof HT as HT'.
  destruct HT' as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  ffx_pose HRS HT. ix_open XO. pose proof HRS as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  eapply evt_cut; [eapply (ff_head X s c r sv f x1 x7 x21 x25 x26 x27 m m XO HRS HT FI HS (munch_refl _ _) (wmono_refl _ _) HC TOK)|].
  intros ms' TP. destruct (fast_trip xx s f) as [f'|f' md g].
  - (* [comment removed for export] *)
    destruct TP as (y1 & y7 & y21 & y25 & y26 & y27 & m' & -> & MU & WM & MI' & HM' & FI').
    pose proof FI' as (Gb & Gh & Gin & Gout & Gob & Gbytes).
    unfold FFL, ff_sp, PC_FF_COND. zs. br_cases Kin.
    + (* [comment removed for export] *)
      replace (f_in f' <? x_last xx) with false in LOK |- * by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in LOK |- *.
      apply evt_done. unfold loop_post. do 20 eexists. split; [eapply FFX_intro; reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact HM'|]. split; [exact FI'| exact LOK].
    + replace (f_in f' <? x_last xx) with true in LOK |- * by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in LOK |- *.
      zs. br_cases Kout.
      * (* [comment removed for export] *)
        replace (f_out f' <? x_end xx) with true in LOK |- * by (symmetry; apply Z.ltb_lt; lia).
        eapply evt_mono.
        -- eapply evt_eq; [| eapply (IH (n - 1) f' _ _ _ _ _ _ m'); first [eassumption | lia] ].
           eapply FFL_intro2; fnorm; ffreg.
        -- intros ms2 LP. unfold loop_post in LP |- *. destruct (ffL xx s (n - 1) f') as [f2 mm].
           destruct LP as (z1 & z5 & z7 & z8 & z9 & z18 & z19 & z20 & z21 & z22 & z23 & z24 & z25 & z26 & z27 & z28 & z29 & z30 & z31 & m2 & -> & MU2 & WM2 & MI2 & HM2 & FI2 & XOK).
           do 20 eexists. split; [reflexivity|].
           split; [eapply munch_trans; [exact MU| exact MU2]|]. split; [eapply wmono_trans; [exact WM| exact WM2]|].
           split; [exact MI2|]. split; [exact HM2|]. split; [exact FI2| exact XOK].
      * (* [comment removed for export] *)
        replace (f_out f' <? x_end xx) with false in LOK |- * by (symmetry; apply Z.ltb_ge; lia).
        zs.
        apply evt_done. unfold loop_post. do 20 eexists. split; [eapply FFX_intro; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact HM'|]. split; [exact FI'| exact LOK].
  - (* [comment removed for export] *)
    destruct TP as (y1 & y5 & y7 & y8 & y9 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27 & y28 & y29 & y30 & y31 & m' & -> & MU & WM & MI' & HM' & FI').
    apply evt_done. unfold loop_post. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact HM'|]. split; [exact FI'| exact LOK].
Qed.
End LOOP.
