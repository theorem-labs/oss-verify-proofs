From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim Monad Stdio Driver.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import STRW_tac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7A0 Require Import RDriverA_main.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.

Definition RATEXITA : Z := 0x955d0.
Definition RATXA_CALLFN : Z := 0x95694.

Definition atxA_W (usp : Z) : list ivl :=
  [(usp - 48, usp); (0x607608, 0x60760c); (0x607628, 0x607630); (0x607728, 0x607730)]%Z.

Definition atxA_cells1 (p3 p4 : list byte) (f1 : word) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p3; C4 z64; C4 (Z_to_bv 64 1); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 RATXA_CALLFN); C8 f1].

Definition atxA_cells2 (p3 p4 : list byte) : list cell :=
  [C1 (Z_to_bv 8 0); CB 3 p3; C4 z64; C4 (Z_to_bv 64 2); CB 4 p4; C8 (Z_to_bv 64 0x607618); C8 z64; C8 (Z_to_bv 64 RATXA_CALLFN);
   C8 (Z_to_bv 64 RATXA_CALLFN)].

Definition ratexitA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo g : Z) (p3 p4 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (atxA_W (bv_unsigned sp)) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' 0x607600 (atxA_cells2 p3 p4)
    /\ rw_cells asegs m' 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 (Z_to_bv 64 g)].

Ltac ax_lstep := lstep; try (first [if_true | if_false]).

Ltac ax_norm1 :=
  first
  [ match goal with |- context [sx32 ?x] =>
      let v := eval vm_compute in (bv_unsigned (sx32 x)) in is_zlit_term v;
      replace (sx32 x) with (Z_to_bv 64 v) by (vm_compute; reflexivity) end
  | match goal with |- context [sxb ?x] =>
      let v := eval vm_compute in (bv_unsigned (sxb x)) in is_zlit_term v;
      replace (sxb x) with (Z_to_bv 64 v) by (vm_compute; reflexivity) end
  | match goal with |- context [bv_swrap 32 ?e] =>
      let v := eval vm_compute in (bv_swrap 32 e) in is_zlit_term v;
      change (bv_swrap 32 e) with v end ].

Ltac ax_norm := repeat ax_norm1.

Ltac ax_step := first [ ax_lstep | progress ax_norm; first [ if_true | if_false | ax_lstep ] ].

Ltac ax_at_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc _) _ _ _ _) => idtac
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail 0 "atexitA walk stopped at" pc
  end.

Lemma ratexitA_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo g : Z) (p3 p4 : list byte) (f1 x1 : word)
    (cdt thr sec : byte) (tm1 : word),
  stk asegs m lo (bv_unsigned sp) ->
  rw_cells asegs m 0x607600 (atxA_cells1 p3 p4 f1) ->
  rw_cells asegs m 0x607720 [C8 (Z_to_bv 64 0x75abc); C8 x1] ->
  rw_cells asegs m 0x607840 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 g -> (0 <= g < 2^64)%Z ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x608000 <= lo)%Z ->
  evt asegs (ratexitA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo g p3 p4 m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RATEXITA) fc None m (seg_rom asegs)).
Proof.
  intros until tm1. intros ST ATX ATA LCH MI -> Hg LO LOLO.
  unfold RATEXITA, atxA_cells1, RATXA_CALLFN in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl (atxA_W (bv_unsigned sp)) m) as MU. unfold atxA_W in MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  repeat ax_step.
  ax_at_ret.
  lazymatch goal with FRx : rw_cells asegs _ (bv_unsigned sp + -48)%Z _, STx : stk asegs _ lo _ |- _ =>
    release_frame FRx STx (bv_unsigned sp) end.
  apply evt_done. unfold ratexitA_post. repeat (lazymatch goal with |- ex _ => eexists end).
  split; [cbv delta [mkR]; reflexivity|].
  split; [unfold atxA_W; exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split.
  - unfold atxA_cells2, RATXA_CALLFN.
    lazymatch goal with H : rw_cells asegs _ 0x607600%Z _ |- _ => exact H end.
  - lazymatch goal with H : rw_cells asegs _ 0x607720%Z _ |- _ => exact H end.
Qed.

Definition ratexitA_exitc_post (t : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (atxA_W (bv_unsigned sp)) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ EXITC2 t m'.

Ltac ax_tr AG A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; cbn in Ha |- *; repeat split; lia].

Lemma ratexitA_exitc : forall (t : Z) ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  EXITC t m -> rw_cells asegs m 0x5e6b94 [C1 (Z_to_bv 8 0)] ->
  stk asegs m lo (bv_unsigned sp) -> mem_inv asegs m ->
  a0 = Z_to_bv 64 0x86484 ->
  (lo <= bv_unsigned sp - 48)%Z -> (0x608000 <= lo)%Z ->
  evt asegs (ratexitA_exitc_post t ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 RATEXITA) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros EX ICB ST MI -> LO LOLO.
  destruct EX as (A1 & A2 & (p3 & p4 & A3) & A3b & A3c & (cdt & thr & sec & tm1 & A4) & A5 & A6 & A8 & (dso & A9) & A10 & A11 & A12 & A13).
  eapply evt_mono.
  { apply (ratexitA_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x86484) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      F fc m lo 0x86484 p3 p4 z64 z64 cdt thr sec tm1);
      first [exact ST | exact A3 | exact A3b | exact A4 | exact MI | reflexivity | lia]. }
  intros ms' PO. unfold ratexitA_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & X1 & X2).
  unfold ratexitA_exitc_post. exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  unfold atxA_W in MU. pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
  unfold EXITC2.
  split; [ax_tr AG A1|]. split; [ax_tr AG A2|]. split; [exists p3, p4; exact X1|]. split; [exact X2|]. split; [ax_tr AG A3c|].
  split; [exists cdt, thr, sec, tm1; ax_tr AG A4|].
  split; [ax_tr AG A5|]. split; [ax_tr AG A6|]. split; [ax_tr AG A8|].
  split; [exists dso; ax_tr AG A9|]. split; [ax_tr AG A10|]. split; [ax_tr AG A11|]. split; [ax_tr AG A12|].
  split; [ax_tr AG A13| ax_tr AG ICB].
Qed.
