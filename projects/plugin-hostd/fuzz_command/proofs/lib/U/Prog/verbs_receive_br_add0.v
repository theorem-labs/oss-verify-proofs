From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Reusable Require Import YM05 YL0i YL00 YL01 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Contract MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require FrameAPI.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import Verbs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require CTypeFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require VerbsRun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import KindB RecInv RecInvU VerbsB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_c verbs_receive_since.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_rel verbs_receive_st verbs_receive_step.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_call verbs_receive_route.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br verbs_receive_br2 sup_pool_config_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require VerbsMem rec_shape_of_c RecKindB reply rec_shape_of.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require verbs_receive_disp atoi_c sup_reply_code_c.
Import ListNotations.
Local Open Scope Z_scope.

From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import verbs_receive_br_pool verbs_receive_br_broad strcmp_c strncmp_c sup_add_c descriptors_add_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require ZBridge.
Local Open Scope Z_scope.

Ltac not_cond :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      replace c with false;
      [ cbv iota
      | symmetry; unfold bv_ltu; rewrite ?unsigned_lit_wrap;
        rewrite ?ZBridge.zb_lxor_ones by (Z.div_mod_to_equations; lia);
        apply Z.ltb_ge; Z.div_mod_to_equations; lia ]
  end.

Lemma add_prefix_walk : forall p w k,
  length p = S k -> Forall (fun b : byte => bv_unsigned b <> 0) p ->
  exists v, strncmp_walk (w ++ [Z_to_bv 8 0]) (p ++ [Z_to_bv 8 0]) k = Some v /\
    -256 < v < 256 /\ (v =? 0) = has_prefix p w.
Proof.
  induction p as [|b p IH]; intros w k LP NP; [discriminate|].
  inversion NP as [|? ? NB NPS]; subst.
  pose proof (bv_unsigned_in_range 8 b) as RB. change (bv_modulus 8) with 256 in RB.
  destruct w as [|a w].
  - cbn [app strncmp_walk]. exists (- bv_unsigned b).
    split; [f_equal; lia|]. split; [lia|].
    unfold has_prefix. cbn [length Nat.leb andb]. apply Z.eqb_neq. lia.
  - pose proof (bv_unsigned_in_range 8 a) as RA. change (bv_modulus 8) with 256 in RA.
    cbn [app strncmp_walk]. rewrite (proj2 (Z.eqb_neq _ _) NB).
    destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [EQ|NE].
    + assert (NA : (bv_unsigned a =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite NA. cbn [orb negb]. destruct k as [|k].
      * destruct p; cbn [length] in LP; [|discriminate].
        cbn [Nat.eqb]. exists 0. split; [f_equal; lia|]. split; [lia|].
        unfold has_prefix. cbn [length Nat.leb firstn list_eqb]. rewrite EQ, !Z.eqb_refl. reflexivity.
      * cbn [Nat.eqb]. destruct (IH w k ltac:(cbn [length] in LP; lia) NPS) as (v & HV & RV & QV).
        exists v. split; [exact HV|]. split; [exact RV|]. rewrite QV.
        unfold has_prefix. cbn [length Nat.leb firstn list_eqb]. rewrite EQ, !Z.eqb_refl. reflexivity.
    + cbn [negb orb]. rewrite !orb_true_r. exists (bv_unsigned a - bv_unsigned b).
      split; [reflexivity|]. split; [lia|].
      assert (EZ : (bv_unsigned a - bv_unsigned b =? 0) = false) by (apply Z.eqb_neq; lia).
      rewrite EZ. unfold has_prefix. cbn [length Nat.leb firstn list_eqb].
      rewrite (proj2 (Z.eqb_neq _ _) NE), andb_false_l, andb_false_r. reflexivity.
Qed.

Lemma add_prefix : forall w,
  exists v, strncmp_model (w ++ [Z_to_bv 8 0]) (place_pool_prefix ++ [Z_to_bv 8 0]) 5 = Some v /\
    -256 < v < 256 /\ (v =? 0) = has_prefix place_pool_prefix w.
Proof.
  intros w. apply (add_prefix_walk place_pool_prefix w 4); vm_compute; repeat constructor; discriminate.
Qed.

Lemma add_place : strcmp_contract -> strncmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) p3 w,
  bv_unsigned sp < 2^63 -> mem_inv rsegs m -> bytes_at rsegs m (bv_unsigned sp + 32) (le8 p3) ->
  bytes_at rsegs m (bv_unsigned p3) (w ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) w ->
  evt rsegs (fun ms' => exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR x1 sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
      s2 s3 (if is_placement_m w then p3 else Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 (if is_placement_m w then 0x1779c else 0x17784)) fc None m' (seg_rom rsegs) /\
    munch [] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x17730) fc None m (seg_rom rsegs)).
Proof.
  intros SCMP NCMP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p3 w HSP MI HB HW NZ.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  pose proof (verbs_receive_disp.read_all _ _ _ HB) as RD. rewrite length_le8 in RD.
  do 3 zstep. cond_by false.
  do 5 zstep.
  eapply evt_cut.
  { eapply SCMP with (sx := w) (sy := place_own).
    - exact HW.
    - exact NZ.
    - refine (proj1 (verbs_receive_disp.img_str _ _ _ MI _)); vm_compute; reflexivity.
    - apply verbs_receive_disp.nz_lit. vm_compute. reflexivity. }
  intros ms' (r & y11 & y12 & y13 & -> & EQ). verbs_receive_disp.fix_ret.
  zstep. rewrite (verbs_receive_disp.scmp_eqb _ _ _ EQ).
  destruct (list_eqb w place_own) eqn:OWN; cbv iota.
  - apply evt_done. unfold is_placement_m. rewrite OWN. cbn [orb]. do 17 eexists.
    split; [reflexivity|]. split; [apply munch_refl|apply wmono_refl].
  - do 4 zstep. eapply evt_cut.
    { eapply SCMP with (sx := w) (sy := place_default).
      - exact HW.
      - exact NZ.
      - refine (proj1 (verbs_receive_disp.img_str _ _ _ MI _)); vm_compute; reflexivity.
      - apply verbs_receive_disp.nz_lit. vm_compute. reflexivity. }
    intros ms' (r' & z11 & z12 & z13 & -> & EQ'). verbs_receive_disp.fix_ret.
    zstep. rewrite (verbs_receive_disp.scmp_eqb _ _ _ EQ').
    destruct (list_eqb w place_default) eqn:DEF; cbv iota.
    + apply evt_done. unfold is_placement_m. rewrite OWN, DEF. cbn [orb]. do 17 eexists.
      split; [reflexivity|]. split; [apply munch_refl|apply wmono_refl].
    + do 5 zstep. destruct (add_prefix w) as (v & CMP & VR & VZ).
      eapply evt_cut.
      { eapply NCMP with (ls := w ++ [Z_to_bv 8 0]) (rs := place_pool_prefix ++ [Z_to_bv 8 0]) (v := v).
        - exact HW.
        - refine (proj1 (verbs_receive_disp.img_str _ _ _ MI _)); vm_compute; reflexivity.
        - exact CMP.
        - exact MI. }
      intros ms' (u5 & u6 & u7 & u11 & u12 & u13 & u14 & u15 & u16 & u17 & u28 & u29 & u30 & u31 & m' & -> & MU & WM & _).
      verbs_receive_disp.fix_ret. zstep. rewrite verbs_receive_disp.eqb_small by exact VR. rewrite VZ.
      destruct (has_prefix place_pool_prefix w) eqn:POOL; cbv iota.
      * apply evt_done. unfold is_placement_m. rewrite OWN, DEF, POOL. cbn [orb]. do 17 eexists.
        split; [reflexivity|]. split; [exact MU|exact WM].
      * zstep. apply evt_done. unfold is_placement_m. rewrite OWN, DEF, POOL. cbn [orb]. do 17 eexists.
        split; [reflexivity|]. split; [exact MU|exact WM].
Qed.

Definition add_tokptr (tk : list (list byte)) (ps : list word) (p : word) (w : option (list byte)) : Prop :=
  (p = Z_to_bv 64 0 /\ w = None) \/
  exists j x, nth_error ps j = Some p /\ nth_error tk j = Some x /\ w = Some x.

Definition add_inputs (tk : list (list byte)) (ps : list word) (pp cp : word) : Prop :=
  exists pl cl, add_m atoi_c.atoi_val (tl tk) = SAdd (nth 1 tk []) (atoi_c.atoi_val (nth 2 tk [])) pl cl /\
    add_tokptr tk ps pp pl /\ add_tokptr tk ps cp cl.

Definition add_keep (R0 R : bvmap 5 word) : Prop :=
  forall r, In r [2;3;4;8;9;18;21;25;26;27] -> reg_get R (Z_to_bv 5 r) = reg_get R0 (Z_to_bv 5 r).

Definition add_parse_post tk ps R0 F fc m (ms : machine_state) : Prop :=
  exists R pc m', ms = MS R F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs) /\
    munch [] m m' /\ wmono rsegs m m' /\ add_keep R0 R /\
    ((pc = 0x17834 /\ add_inputs tk ps (reg_get R 20) (reg_get R 19)) \/
     ((pc = 0x17a88 \/ pc = 0x178a4) /\ add_m atoi_c.atoi_val (tl tk) = reject)).

Ltac add_keep_tac :=
  intros r Hr; cbn [In] in Hr;
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; reflexivity.

Ltac add_parse_fin pc :=
  apply evt_done; unfold add_parse_post; eexists; exists pc; eexists;
  split; [reflexivity|]; split; [apply munch_refl|]; split; [apply wmono_refl|];
  split; [unfold add_keep; add_keep_tac|].

Lemma add_parse_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) v u i x rest ps,
  let tk := v :: u :: i :: x :: rest in
  s3 = verbs_receive_disp.ntokw tk -> s5 = verbs_receive_disp.ntokw tk ->
  s6 = Z_to_bv 64 (Z.of_nat (length tk) - 1) -> (length tk <= 64)%nat -> length ps = length tk -> bv_unsigned sp < 2^63 ->
  (forall j, (j < length ps)%nat -> bytes_at rsegs m (bv_unsigned sp + 8 + 8 * Z.of_nat j) (le8 (nth j ps (Z_to_bv 64 0)))) ->
  evt rsegs
    (add_parse_post tk ps
      (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
      s2 s3 (if is_placement_m x then nth 3 ps (Z_to_bv 64 0) else Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 (if is_placement_m x then 0x1779c else 0x17784)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m v u i x rest ps tk E3 E5 E6 NL PL HSP HB. subst s3 s5 s6. unfold tk in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  assert (EP3 : nth_error ps 3 = Some (nth 3 ps (Z_to_bv 64 0))) by (apply nth_error_nth'; cbn [length] in PL; lia).
  destruct (is_placement_m x) eqn:PX; cbv iota.
  - do 3 zstep. cond_by false. do 2 zstep. unfold bv_ltu. rewrite !unsigned_lit by (cbn [length] in *; lia).
    destruct rest as [|y rest].
    + rewrite (proj2 (Z.ltb_lt _ _)) by (cbn [length]; lia). zstep. add_parse_fin 0x17834. left. split; [reflexivity|].
      unfold add_inputs. exists (Some x), None. split; [cbn [tl nth add_m]; rewrite PX; reflexivity|].
      split; [right; exists 3%nat, x; repeat split; assumption || reflexivity|left; split; reflexivity].
    + destruct rest as [|z rest].
      * rewrite (proj2 (Z.ltb_ge _ _)) by (cbn [length]; lia). do 4 zstep. not_cond. do 2 zstep.
        unfold bv_ltu, verbs_receive_disp.ntokw. rewrite !unsigned_lit by (cbn [length] in *; lia).
        rewrite (proj2 (Z.ltb_ge _ _)) by (cbn [length]; lia).
        pose proof (verbs_receive_disp.read_all _ _ _ (HB 4%nat ltac:(cbn [length] in PL; lia))) as RD.
        rewrite length_le8 in RD. replace (bv_unsigned sp + 8 + 8 * Z.of_nat 4) with (bv_unsigned sp + 40) in RD by lia.
        do 3 zstep. add_parse_fin 0x17834. left. split; [reflexivity|].
        unfold add_inputs. exists (Some x), (Some y). split; [cbn [tl nth add_m]; rewrite PX; reflexivity|].
        split; right; [exists 3%nat, x|exists 4%nat, y]; repeat split; try reflexivity; try exact EP3.
        apply nth_error_nth'; cbn [length] in PL; lia.
      * rewrite (proj2 (Z.ltb_ge _ _)) by (cbn [length]; lia). do 4 zstep. not_cond. do 2 zstep.
        unfold bv_ltu, verbs_receive_disp.ntokw. rewrite !unsigned_lit by (cbn [length] in *; lia).
        rewrite (proj2 (Z.ltb_lt _ _)) by (cbn [length]; lia).
        add_parse_fin 0x178a4. right. split; [right; reflexivity|]. reflexivity.
  - do 6 zstep. not_cond. do 2 zstep. unfold bv_ltu, verbs_receive_disp.ntokw. rewrite !unsigned_lit by (cbn [length] in *; lia).
    destruct rest as [|y rest].
    + rewrite (proj2 (Z.ltb_ge _ _)) by (cbn [length]; lia).
      pose proof (verbs_receive_disp.read_all _ _ _ (HB 3%nat ltac:(cbn [length] in PL; lia))) as RD.
      rewrite length_le8 in RD. replace (bv_unsigned sp + 8 + 8 * Z.of_nat 3) with (bv_unsigned sp + 32) in RD by lia.
      do 3 zstep. add_parse_fin 0x17834. left. split; [reflexivity|].
      unfold add_inputs. exists None, (Some x). split; [cbn [tl nth add_m]; rewrite PX; reflexivity|].
      split; [left; split; reflexivity|right; exists 3%nat, x; repeat split; assumption || reflexivity].
    + rewrite (proj2 (Z.ltb_lt _ _)) by (cbn [length]; lia).
      add_parse_fin 0x178a4. right. split; [right; reflexivity|].
      destruct rest; cbn [tl add_m]; rewrite ?PX; reflexivity.
Qed.

Lemma add_parse_change : forall tk ps R0 R1 F fc m0 m1 ms,
  add_keep R0 R1 -> munch [] m0 m1 -> wmono rsegs m0 m1 ->
  add_parse_post tk ps R1 F fc m1 ms -> add_parse_post tk ps R0 F fc m0 ms.
Proof.
  intros tk ps R0 R1 F fc m0 m1 ms KP MU WM (R & pc & m' & E & MU' & WM' & KP' & H).
  exists R, pc, m'. split; [exact E|]. split; [eapply munch_trans; eassumption|].
  split; [eapply wmono_trans; eassumption|]. split; [|exact H].
  intros r HR. rewrite (KP' r HR). exact (KP r HR).
Qed.

Lemma add_kparse : strcmp_contract -> strncmp_contract ->
  forall (tk : list (list byte)) ps
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  s3 = verbs_receive_disp.ntokw tk -> s5 = verbs_receive_disp.ntokw tk ->
  s6 = Z_to_bv 64 (Z.of_nat (length tk) - 1) -> (1 <= length tk <= 64)%nat -> length ps = length tk ->
  bv_unsigned sp < 2^63 -> mem_inv rsegs m ->
  (forall j, (j < length ps)%nat -> bytes_at rsegs m (bv_unsigned sp + 8 + 8 * Z.of_nat j) (le8 (nth j ps (Z_to_bv 64 0)))) ->
  (forall j, (j < length tk)%nat -> VerbsMem.cstr0_at m (bv_unsigned (nth j ps (Z_to_bv 64 0))) (nth j tk [])) ->
  evt rsegs
    (add_parse_post tk ps
      (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x176d4) fc None m (seg_rom rsegs)).
Proof.
  intros SCMP NCMP tk ps ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m E3 E5 E6 NL PL HSP MI HB HW. subst s3 s5 s6.
  do 2 zstep. unfold bv_ltu. rewrite !unsigned_lit by lia.
  destruct (1 <? Z.of_nat (length tk) - 1) eqn:GT; cbv beta iota delta [negb].
  - apply Z.ltb_lt in GT. do 2 zstep. rewrite verbs_receive_disp.eqb_ntokw by lia.
    destruct (Z.of_nat (length tk) =? 3) eqn:EQ3; cbv beta iota delta [negb].
    + apply Z.eqb_eq in EQ3. do 3 zstep. add_parse_fin 0x17834. left. split; [reflexivity|].
      destruct (pool_len3 tk ltac:(lia)) as (v & u & i & ->).
      unfold add_inputs. exists None, None. split; [reflexivity|]. split; left; split; reflexivity.
    + apply Z.eqb_neq in EQ3.
      destruct tk as [|v [|u [|i [|x rest]]]]; cbn [length] in GT, EQ3; try lia.
      destruct (HW 3%nat ltac:(cbn [length]; lia)) as [HW3 NZ3].
      assert (HB3 : bytes_at rsegs m (bv_unsigned sp + 32) (le8 (nth 3 ps (Z_to_bv 64 0)))).
      { replace (bv_unsigned sp + 32) with (bv_unsigned sp + 8 + 8 * Z.of_nat 3) by lia.
        apply HB. cbn [length] in PL. lia. }
      eapply evt_cut; [eapply (add_place SCMP NCMP); [exact HSP|exact MI|exact HB3|exact HW3|apply verbs_receive_disp.nz_notin; exact NZ3]|].
      intros ms' (x1 & x5 & x6 & x7 & x10 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM).
      eapply evt_mono.
      { eapply add_parse_tail with (v := v) (u := u) (i := i) (x := x) (rest := rest) (ps := ps);
          [reflexivity|reflexivity|reflexivity|exact (proj2 NL)|exact PL|exact HSP|].
        intros j HJ. eapply bytes_at_transport; [exact (HB j HJ)|exact MU|exact I]. }
      intros ms HQ. eapply add_parse_change; [|exact MU|exact WM|exact HQ]. unfold add_keep; add_keep_tac.
  - apply Z.ltb_ge in GT. add_parse_fin 0x17a88. right. split; [left; reflexivity|].
    destruct tk as [|v [|u [|i rest]]]; cbn [length] in *; try lia; reflexivity.
Qed.

Lemma add_katoi : atoi_c.atoi_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) p1 p2 w,
  bv_unsigned sp < 2^63 -> mem_inv rsegs m -> bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1) ->
  bytes_at rsegs m (bv_unsigned sp + 24) (le8 p2) ->
  bytes_at rsegs m (bv_unsigned p2) (w ++ [Z_to_bv 8 0]) ->
  evt rsegs (fun ms' => exists x5 x6 x7 x14 x15 x16 x17 x28 x29 x30 x31 m',
    ms' = MS (mkR (Z_to_bv 64 0x1786c) sp gp tp x5 x6 x7 s0 s1 p1 (Z_to_bv 64 (atoi_c.atoi_val w)) s4 s3 x14 x15 x16 x17
      s2 s3 s4 p1 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x16000) fc None m' (seg_rom rsegs) /\
    munch [] m m' /\ wmono rsegs m m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x17834) fc None m (seg_rom rsegs)).
Proof.
  intros AT ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 p2 w HSP MI HB1 HB2 HW.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  pose proof (verbs_receive_disp.read_all _ _ _ HB1) as RD1. rewrite length_le8 in RD1.
  pose proof (verbs_receive_disp.read_all _ _ _ HB2) as RD2. rewrite length_le8 in RD2.
  do 3 zstep. cond_by false.
  do 3 zstep.
  replace (bv_unsigned sp + 8 <? 18446744073709551600) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [Z.b2z]. change (Z.lxor 1 1) with 0. cond_by false.
  do 3 zstep. replace p2 with (Z_to_bv 64 (bv_unsigned p2)) by apply Z_to_bv_bv_unsigned.
  eapply evt_cut; [eapply AT; [exact HW|exact MI]|].
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & _).
  verbs_receive_disp.fix_ret. do 5 zstep. apply evt_done. do 12 eexists.
  split; [reflexivity|]. split; [exact MU|exact WM].
Qed.

Lemma add_digits_range : forall s n, -2^31 <= n < 2^31 -> -2^31 <= sup_reply_code_c.atoi_digits n s < 2^31.
Proof.
  induction s as [|b s IH]; intros n H; cbn [sup_reply_code_c.atoi_digits]; [exact H|].
  destruct ((48 <=? bv_unsigned b) && (bv_unsigned b <=? 57)); [apply IH, CTypeFacts.swrap32_range|exact H].
Qed.

Lemma add_reply_range : forall x, -2^31 <= sup_reply_code_c.reply_code x < 2^31.
Proof.
  intros x. unfold sup_reply_code_c.reply_code. destruct (list_eq_dec _ _ _); [|lia].
  generalize (skipn 5 x). intros s. induction s as [|b s IH]; cbn [sup_reply_code_c.atoi_musl]; [lia|].
  destruct (((9 <=? bv_unsigned b) && (bv_unsigned b <=? 13)) || (bv_unsigned b =? 32)); [exact IH|].
  destruct (bv_unsigned b =? 45); [apply add_digits_range; lia|].
  destruct (bv_unsigned b =? 43); apply CTypeFacts.swrap32_range.
Qed.

Lemma add_lts : forall z, -2^31 <= z < 2^31 -> bv_lts (Z_to_bv 64 z) (Z_to_bv 64 0) = (z <? 0).
Proof.
  intros z H. unfold bv_lts. rewrite !Z_to_bv_signed. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 64) with 9223372036854775808.
  change (bv_modulus 64) with 18446744073709551616.
  rewrite !Z.mod_small by lia. f_equal; lia.
Qed.

Lemma add_kreply : sup_reply_code_c.sup_reply_code_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) p1 x lo,
  bv_unsigned sp < 2^63 -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo + 32 <= bv_unsigned sp -> 0x107da <= lo ->
  bv_unsigned a0 <> 0 -> bytes_at rsegs m (bv_unsigned a0) (x ++ [Z_to_bv 8 0]) -> no0 x ->
  bv_unsigned a0 + Z.of_nat (length x) + 1 <= lo ->
  bytes_at rsegs m (bv_unsigned sp + 16) (le8 p1) ->
  evt rsegs (fun ms' => exists R pc m', ms' = MS R F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs) /\
    munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    add_keep (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) R /\
    reg_get R 19 = a0 /\
    ((pc = 0x178b0 /\ sup_reply_code_c.reply_code x < 0) \/
     (pc = 0x1721c /\ 0 <= sup_reply_code_c.reply_code x /\ reg_get R 1 = Z_to_bv 64 0x17890 /\ reg_get R 10 = p1)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 0x1786c) fc None m (seg_rom rsegs)).
Proof.
  intros RC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m p1 x lo HSP MI ST LO LI NZ HX NX OX HB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2^64) in RSP.
  zstep. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  rewrite (proj2 (Z.eqb_neq _ _) NZ). do 2 zstep.
  eapply evt_cut.
  { eapply RC with (lo := lo) (x := x); try eassumption.
    - left. unfold sup_reply_code_c.SUP_REPLY_CODE_FRAME. lia.
    - apply verbs_receive_disp.img_bytes; [exact MI|vm_compute; reflexivity].
    - left. unfold sup_reply_code_c.RESP_LIT, sup_reply_code_c.SUP_REPLY_CODE_FRAME. lia. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & _).
  verbs_receive_disp.fix_ret. zstep. rewrite add_lts by apply add_reply_range.
  destruct (sup_reply_code_c.reply_code x <? 0) eqn:NEG; cbv iota.
  - apply Z.ltb_lt in NEG. apply evt_done. eexists; exists 0x178b0; eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [unfold add_keep; add_keep_tac|]. split; [reflexivity|]. left. split; [reflexivity|exact NEG].
  - apply Z.ltb_ge in NEG.
    assert (HB' : bytes_at rsegs m' (bv_unsigned sp + 16) (le8 p1)).
    { eapply bytes_at_transport; [exact HB|exact MU|]. cbn [disjoint_from]. split; [right; lia|exact I]. }
    pose proof (verbs_receive_disp.read_all _ _ _ HB') as RD. rewrite length_le8 in RD.
    do 3 zstep. cond_by false. do 2 zstep. apply evt_done. eexists; exists 0x1721c; eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
    split; [unfold add_keep; add_keep_tac|]. split; [reflexivity|]. right. repeat split; try reflexivity; exact NEG.
Qed.

Lemma add_kjump : forall (R F : bvmap 5 word) fc m,
  evt rsegs (fun ms' => ms' = MS R F (Z_to_bv 64 0x178b0) fc None m (seg_rom rsegs))
    (MS R F (Z_to_bv 64 0x17890) fc None m (seg_rom rsegs)).
Proof. intros. zstep. apply evt_done. reflexivity. Qed.
