(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_pure Z_infl_c_pure Z_infl_c_tab Zg_infl_iface Zg_inffast_defs.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInffast_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition brk_s (s : inflate_state) (mm : option (Z * option Z)) : inflate_state :=
  match mm with Some (md, _) => iset_mode s md | None => s end.
Definition brk_c (c : icall) (mm : option (Z * option Z)) : icall :=
  match mm with Some (_, Some g) => icset_msg c g | _ => c end.

Definition TPOST (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave) (me : mem) (res : fstep) : machine_state -> Prop :=
  match res with
  | FCont f' => fun ms' => exists x1 x7 x21 x25 x26 x27 m',
      ms' = FFL X s c r f' PC_FF_COND x1 x7 x21 x25 x26 x27 m'
      /\ munch (ffWb X) me m' /\ wmono psegs me m' /\ mem_inv psegs m' /\ FFM X s c sv f' m' /\ FINV X s c f'
  | FBreak f' md g => fun ms' => exists x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
      ms' = FFX X s c r f' x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m'
      /\ munch (ffWb X) me m' /\ wmono psegs me m' /\ mem_inv psegs m'
      /\ FFMg X s c sv (brk_s s (Some (md, g))) (brk_c c (Some (md, g))) f' m' /\ FINV X s c f'
  end.

Lemma land7_mod8 : forall b, 0 <= b -> Z.land b 7 = b mod 8.
Proof. intros b Hb. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma shiftr3_div8 : forall b, 0 <= b -> Z.shiftr b 3 = b / 8.
Proof. intros b Hb. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.

Lemma ff_giveback_bits : forall b, 0 <= b <= 63 -> wrap32 (b - Z.shiftl (Z.shiftr b 3) 3) = Z.land b 7.
Proof.
  intros b Hb. rewrite land7_mod8, Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
  rewrite wrap32_id by (Z.div_mod_to_equations; lia). Z.div_mod_to_equations. lia.
Qed.
Lemma ff_avail_if : forall a l k, (if a <? l then k + (l - a) else k - (a - l)) = l - a + k.
Proof. intros a l k. destruct (a <? l); lia. Qed.

Definition ff_exit_post (X : ictx) (w : iw) (sv : ffsave) (m : mem) : machine_state -> Prop :=
  fun ms' => exists x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR (fs_ra sv) (wz (bv_unsigned (ix_sp X) + -240)) (ix_gp X) (ix_tp X) x5 x6 x7 (fs_x8 sv) (fs_x9 sv) x10 x11 x12 x13 x14 x15 x16 x17
                 (fs_x18 sv) (fs_x19 sv) (fs_x20 sv) (fs_x21 sv) (fs_x22 sv) (fs_x23 sv) (fs_x24 sv) (fs_x25 sv) (fs_x26 sv) (fs_x27 sv) x28 x29 x30 x31)
             (ix_F X) (ret_pc (fs_ra sv)) (ix_fc X) None m' (seg_rom psegs)
    /\ munch [(il_S (ix_L X), il_S (ix_L X) + 40); (il_As (ix_L X) + 96, il_As (ix_L X) + 108)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ IMEM X (LOAD w) m'.

Local Ltac exit_walk FR ZS GA :=
  do 11 zs.

Lemma ff_exit : forall (X : ictx) s c r sv f mm (x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f -> exit_ok f = true ->
  FFMg X s c sv (brk_s s mm) (brk_c c mm) f m ->
  iframe X r m -> stk psegs m (ix_lo X) (ff_sp X) -> ilens m (ix_L X) s -> iwork m (ix_L X) s ->
  munch (ix_W X) (ix_m0 X) m -> wmono psegs (ix_m0 X) m ->
  evt psegs (ff_exit_post X (LOAD (ff_post s c r (ffx_of s c r) (ff_fin f) mm)) sv m)
    (FFX X s c r f x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m).
Proof.
  intros X s c r sv f mm x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m XO HRS HT FI XOK HM FRM STK Gl Gw MU WM.
  ffx_pose HRS HT.
  destruct HRS as (E1 & E2 & E3 & E4 & E5 & E6).
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  rewrite <- E1, <- E2, <- E3, <- E4 in *. clear E1 E2 E3 E4.
  destruct FI as (Fb & Fh & Fin & Fout & Fob & Fbytes).
  unfold exit_ok in XOK. apply Z.leb_le in XOK. rewrite shiftr3_div8 in XOK by lia.
  destruct HM as (FR & GA & GT & ZS & Gc & Gwin & IN & OUT & MI & ARRS & LAY).
  destruct FRM as (jf0 & jf1 & jf & FRM). unfold iframe_cells in FRM. unfold ix_W in MU. unfold iin in IN. unfold iout in OUT.
  ix_open XO. unfold FFX, PC_FF_EXIT, ff_sp in *. unfold ff_frame_cells in FR.
  assert (RH64 : 0 <= f_hold f < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 Fh)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (f_ob f)) (f_out f) ltac:(cbn [ic_outbuf icset_outbuf]; lia)) as LOB.
  apply (f_equal Z.of_nat) in LOB.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 40); (il_As (ix_L X) + 96, il_As (ix_L X) + 108)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.

  destruct mm as [[md [g|]]|]; cbn [brk_s brk_c] in GA, ZS; open_isA GA; open_izs ZS;
    (zs; rewrite srliw3_small by lia; pose proof (conj (Z.div_pos (f_bits f) 8 ltac:(lia) ltac:(lia)) (Z.div_lt_upper_bound (f_bits f) 8 8 ltac:(lia) ltac:(lia))) as RQ;
     set (q := f_bits f / 8) in *;
     do 10 zs; rewrite clang_mask32 by (rewrite land7_mod8 by lia; Z.div_mod_to_equations; lia);
     do 6 zs; do 14 zs; release_frame FR STK (bv_unsigned (ix_sp X) + -240); zs;
     itr_groups MUf WMf;
     apply evt_done; unfold ff_exit_post; do 16 eexists; split; [reflexivity|];
     split; [exact MUf|]; split; [exact WMf|]; split; [assumption|];
     unfold ff_post, LOAD; cbn [w_s w_c w_r];
     unfold ff_fin; cbn [f_in f_out f_hold f_bits f_ob fset_in fset_bits fset_hold];
     rewrite ff_giveback_bits, zmask_ones, shiftr3_div8, !ff_avail_if by (rewrite ?land7_mod8 by lia; Z.div_mod_to_equations; lia); fold q;
     apply IMEM_intro; inorm;
     [ exists jf0, jf1, jf; unfold iframe_cells; inorm; exact FRM
     | exact STK
     | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
     | constructor; inorm;
       [ unfold isA, isA_cells; inorm; close_cells GA
       | unfold isT, isT_cells; inorm; exact GT
       | unfold ilens; inorm; exact Gl | unfold iwork; inorm; exact Gw | unfold icodes; inorm; exact Gc
       | unfold iwin; inorm; unfold iwin in Gwin; exact Gwin
       | unfold iarrs; inorm; exact ARRS | unfold ilay_ok; inorm; exact LAY ]
     | exact IN
     | unfold iout; erewrite iout_bytes_ext by reflexivity; exact OUT
     | assumption | exact MU | exact WM ]).
  all: rewrite le4_swrap32_add; do 3 f_equal; lia.
Qed.

Definition ff_brk_post (X : ictx) (s : inflate_state) (c : icall) (r : iregs) (sv : ffsave) (f : ffs) (mm : option (Z * option Z)) (m : mem)
  : machine_state -> Prop :=
  fun ms' => exists x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m',
    ms' = FFX X s c r f x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m'
    /\ munch [(il_S (ix_L X) + 48, il_S (ix_L X) + 56); (il_As (ix_L X) + 8, il_As (ix_L X) + 12)] m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ FFMg X s c sv (brk_s s mm) (brk_c c mm) f m'.

Local Ltac brk_open XO HT HM c f :=
  let ARRS := fresh "ARRS" in let LAY := fresh "LAY" in let LIN := fresh "LIN" in let LOB := fresh "LOB" in
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas);
  destruct HM as (FR & GA & GT & ZS & Gc & Gwin & IN & OUT & MI & ARRS & LAY);
  unfold iin in IN; unfold iout in OUT; ix_open XO; unfold FFL, ff_sp in *; unfold ff_frame_cells in FR; open_isA GA; open_izs ZS;
  lazymatch goal with X : ictx |- _ =>
    pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN;
    pose proof (iout_bytes_length (ix_rest0 X) (icset_outbuf c (f_ob f)) (f_out f) ltac:(cbn [ic_outbuf icset_outbuf]; lia)) as LOB;
    apply (f_equal Z.of_nat) in LOB
  end.

Local Ltac brk_close FR GA GT ZS Gc Gwin IN OUT ARRS LAY MUf WMf :=
  itr_groups MUf WMf; apply evt_done; unfold ff_brk_post; do 20 eexists; split; [eapply FFX_intro; reflexivity|];
  split; [exact MUf|]; split; [exact WMf|]; split; [assumption|];
  unfold FFMg; cbn [brk_s brk_c]; inorm;
  split; [unfold ff_frame_cells; exact FR|]; split; [unfold isA, isA_cells; inorm; close_cells GA|]; split; [exact GT|];
  split; [eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS|];
  split; [exact Gc|]; split; [exact Gwin|]; split; [exact IN|]; split; [exact OUT|]; split; [assumption|]; split; [exact ARRS| exact LAY].

Lemma ff_brk1 : forall (X : ictx) s c r sv f here (x1 x7 x21 x26 x27 : word) m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f -> FFM X s c sv f m ->
  evt psegs (ff_brk_post X s c r sv f (if negb (Z.land (code_op here) 32 =? 0) then Some (TYPE, None)
                                      else Some (BAD, Some MSG_ff_invalid_literal_length_code)) m)
    (FFL X s c r f PC_FF_BRK1 x1 x7 x21 (wz (code_op here)) x26 x27 m).
Proof.
  intros X s c r sv f here x1 x7 x21 x26 x27 m XO HRS HT FI HM. ffx_pose HRS HT. destruct FI as (Fb & Fh & Fin & Fout & Fob & Fbytes). brk_open XO HT HM c f.
  pose proof (code_op_range here) as ROP.
  pose proof (munch_refl [(il_S (ix_L X) + 48, il_S (ix_L X) + 56); (il_As (ix_L X) + 8, il_As (ix_L X) + 12)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  unfold PC_FF_BRK1. do 2 zs. br_cases K.
  -
    replace (Z.land (code_op here) 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    do 4 zs. brk_close FR GA GT ZS Gc Gwin IN OUT ARRS LAY MUf WMf.
  - replace (Z.land (code_op here) 32 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    do 7 zs. brk_close FR GA GT ZS Gc Gwin IN OUT ARRS LAY MUf WMf.
Qed.

Lemma ff_brk2 : forall (X : ictx) s c r sv f (x1 x7 x21 x25 x26 x27 : word) m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f -> FFM X s c sv f m ->
  evt psegs (ff_brk_post X s c r sv f (Some (BAD, Some MSG_ff_invalid_distance_code)) m)
    (FFL X s c r f PC_FF_BRK2 x1 x7 x21 x25 x26 x27 m).
Proof.
  intros X s c r sv f x1 x7 x21 x25 x26 x27 m XO HRS HT FI HM. ffx_pose HRS HT. destruct FI as (Fb & Fh & Fin & Fout & Fob & Fbytes). brk_open XO HT HM c f.
  pose proof (munch_refl [(il_S (ix_L X) + 48, il_S (ix_L X) + 56); (il_As (ix_L X) + 8, il_As (ix_L X) + 12)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  unfold PC_FF_BRK2. do 6 zs. brk_close FR GA GT ZS Gc Gwin IN OUT ARRS LAY MUf WMf.
Qed.

Lemma ff_brk3 : forall (X : ictx) s c r sv f (x1 x7 x21 x25 x26 x27 : word) m,
  ix_ok X -> ff_restored s c r -> ff_typed X s c r -> FINV X s c f -> FFM X s c sv f m ->
  evt psegs (ff_brk_post X s c r sv f (Some (BAD, Some MSG_ff_invalid_distance_too_far_back)) m)
    (FFL X s c r f PC_FF_BRK3 x1 x7 x21 x25 x26 x27 m).
Proof.
  intros X s c r sv f x1 x7 x21 x25 x26 x27 m XO HRS HT FI HM. ffx_pose HRS HT. destruct FI as (Fb & Fh & Fin & Fout & Fob & Fbytes). brk_open XO HT HM c f.
  pose proof (munch_refl [(il_S (ix_L X) + 48, il_S (ix_L X) + 56); (il_As (ix_L X) + 8, il_As (ix_L X) + 12)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  unfold PC_FF_BRK3. do 7 zs. brk_close FR GA GT ZS Gc Gwin IN OUT ARRS LAY MUf WMf.
Qed.
