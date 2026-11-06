From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YK11.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strlen_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma ub_roc4 : forall m A v, bytes_at rsegs m A (le4 v) -> ro_cells rsegs m A [C4 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma ub_roc8 : forall m A v, bytes_at rsegs m A (le8 v) -> ro_cells rsegs m A [C8 v].
Proof. intros m A v HB. split; [cbn; tauto | cbn [cells_bytes cbytes]; rewrite app_nil_r; exact HB]. Qed.

Lemma ub_ne0 : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> z <> 0 -> bv_eqb (Z_to_bv 64 z) (Z_to_bv 64 0) = false.
Proof.
  intros z Hz Hn. unfold bv_eqb. rewrite !Z_to_bv_unsigned. apply Z.eqb_neq.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite (Z.mod_small 0) by lia.
  intros E. apply Z.mod_divide in E; [|lia]. destruct E as [q Hq]. nia.
Qed.

Lemma ub_sx32_small : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ub_swrap_small : forall z, 0 <= z < 2 ^ 31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.

Ltac ub_fixS :=
  repeat match goal with |- context [Z_to_bv 64 (?x + -128 + 128)] => replace (x + -128 + 128) with x by lia end.

Ltac ub_lits :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => is_Zlit z;
      let w := eval vm_compute in (bv_unsigned (sx32 (Z_to_bv 64 z))) in
      replace (sx32 (Z_to_bv 64 z)) with (Z_to_bv 64 w) by (apply bv_eq; vm_compute; reflexivity)
  | |- context [zx32 (Z_to_bv 64 ?z)] => is_Zlit z;
      let w := eval vm_compute in (bv_unsigned (zx32 (Z_to_bv 64 z))) in
      replace (zx32 (Z_to_bv 64 z)) with (Z_to_bv 64 w) by (apply bv_eq; vm_compute; reflexivity)
  end.

Ltac ub_cond := unfold_cond; rewrite ?unsigned_lit by lia; fold_lit_ux; solve_cond_rec.

Ltac ub_cf H :=
  zify_cond H; unfold zxb in H; rewrite ?unsigned_lit in H by lia;
  try (apply andb_false_iff in H; destruct H as [H|H]; zify_bool H);
  try (apply andb_true_iff in H; destruct H as [H ?]; zify_bool H).

Ltac ub_zl := first [ lia | Z.div_mod_to_equations; lia ].

Ltac ub_br :=
  lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end;
  ub_lits;
  repeat match goal with H : bv_eqb ?x ?y = _ |- context [bv_eqb ?x ?y] => rewrite H end;
  cbn [negb];
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true by (symmetry; first [reflexivity | assumption | ub_cond]); cbv iota
            | replace c with false by (symmetry; first [reflexivity | assumption | ub_cond]); cbv iota
            | let H := fresh "HC" in if_cases H; ub_cf H; try (exfalso; ub_zl) ]
  | _ => idtac
  end.

Lemma ub_land7 : forall v, 0 <= v < 2 ^ 64 -> v mod 8 = 0 -> Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 v)) 7) = Z_to_bv 64 0.
Proof.
  intros v Hv Hm. rewrite unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia.
  change (2 ^ 3) with 8. rewrite Hm. reflexivity.
Qed.

Ltac ub_until pc :=
  repeat lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail
  | |- context [Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 ?v)) 7)] =>
      rewrite (ub_land7 v) by first [lia | assumption]
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => ub_br
  | _ => step
  end.

Ltac ub_gv :=
  lazymatch goal with |- getr ?X ?k = _ => change (getr X k) with (reg_get X k) end;
  simp_regs; rewrite ?ub_sx32_small by lia;
  first [ reflexivity | f_equal; lia
        | rewrite ?unsigned_lit by lia; rewrite ?ub_swrap_small by lia; first [ reflexivity | f_equal; lia ] ].

Definition ub_tail_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S pc t : Z) (A1 A2 : word -> Prop) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 pc) fc None m' (seg_rom rsegs) /\
    munch [(S + -128, S)] m m' /\ wmono rsegs m m' /\ A1 a1 /\ A2 a2.

Ltac ub_tail_done :=
  apply evt_done; unfold ub_tail_post; ub_fixS;
  do 15 eexists; split; [reflexivity|];
  split; [eassumption|]; split; [eassumption|]; split; first [reflexivity | exact I].

Lemma ub_seg_lit : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S t v pretty d k lit n : Z) (junk : list byte),
  (k = 0 /\ lit = 0x102ed /\ n = 4) \/ (k = 1 /\ lit = 0x10298 /\ n = 5) \/ (k = 2 /\ lit = 0x10349 /\ n = 4) ->
  0x40000 <= S + -128 -> S <= 2 ^ 63 -> 0 <= t < 2 ^ 64 -> 0 < v -> v mod 8 = 0 -> v + 56 <= 2 ^ 64 ->
  v + 56 <= S + -128 \/ S <= v -> 0 <= d < 2 ^ 64 ->
  rw_cells rsegs m (S + -128) [CB 128 junk] ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 k)) ->
  mem_inv rsegs m ->
  evt rsegs (ub_tail_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S 0x154b8 t
               (fun a1 => a1 = Z_to_bv 64 lit) (fun a2 => a2 = Z_to_bv 64 n))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 d)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S t v pretty d k lit n junk
    Hk HS1 HS2 Ht Hv0 Hv7 Hv64 Hv Hd FR TY HI.
  apply ub_roc4 in TY.
  assert (HM : munch [(S + -128, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  destruct Hk as [(-> & -> & ->)|[(-> & -> & ->)|(-> & -> & ->)]]; ub_until 0x154b8; ub_tail_done.
Qed.

Lemma ub_seg_str : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S t v pretty d s : Z) (junk : list byte),
  0x40000 <= S + -128 -> S <= 2 ^ 63 -> 0 <= t < 2 ^ 64 -> 0 < v -> v mod 8 = 0 -> v + 56 <= 2 ^ 64 ->
  v + 56 <= S + -128 \/ S <= v -> 0 <= d < 2 ^ 64 -> 0 <= s < 2 ^ 64 ->
  rw_cells rsegs m (S + -128) [CB 128 junk] ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 4)) -> bytes_at rsegs m (v + 16) (le8 (Z_to_bv 64 s)) ->
  mem_inv rsegs m ->
  evt rsegs (ub_tail_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S 0x158d4 t
               (fun a1 => a1 = Z_to_bv 64 s) (fun _ => True))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 d)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S t v pretty d s junk
    HS1 HS2 Ht Hv0 Hv7 Hv64 Hv Hd Hs FR TY ST HI.
  apply ub_roc4 in TY. apply ub_roc8 in ST.
  assert (HM : munch [(S + -128, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  ub_until 0x158d4. ub_tail_done.
Qed.

Lemma ub_seg_num : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S t v pretty d s : Z) (cs sl junk : list byte),
  strlen_contract ->
  0x40000 <= S + -128 -> S <= 2 ^ 63 -> 0 <= t < 2 ^ 64 -> 0 < v -> v mod 8 = 0 -> v + 56 <= 2 ^ 64 ->
  v + 56 <= S + -128 \/ S <= v -> 0 <= d < 2 ^ 64 -> 0 <= s ->
  rw_cells rsegs m (S + -128) [CB 128 junk] ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 3)) -> bytes_at rsegs m (v + 16) (le8 (Z_to_bv 64 s)) ->
  bytes_at rsegs m s (cs ++ Z_to_bv 8 0 :: sl) -> ~ In (Z_to_bv 8 0) cs ->
  (- (s + Z.of_nat (length cs) + 1)) mod 8 <= Z.of_nat (length sl) ->
  s + Z.of_nat (length cs) + 1 + Z.of_nat (length sl) <= S + -128 ->
  mem_inv rsegs m ->
  evt rsegs (ub_tail_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S 0x154b8 t
               (fun a1 => a1 = Z_to_bv 64 s) (fun a2 => a2 = Z_to_bv 64 (Z.of_nat (length cs))))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 d)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S t v pretty d s cs sl junk
    HSTR HS1 HS2 Ht Hv0 Hv7 Hv64 Hv Hd Hs FR TY ST HB HZ HA HD HI.
  unfold strlen_contract, STRLEN in HSTR.
  pose proof (bytes_at_bound rsegs m s _ HB) as HBb. rewrite length_app in HBb. cbn [length] in HBb.
  apply ub_roc4 in TY. apply ub_roc8 in ST.
  assert (HM : munch [(S + -128, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  ub_until 0x22a54.
  lazymatch goal with HM0 : munch _ m ?mm, HW0 : wmono _ m ?mm |- _ =>
    eapply evt_cut;
    [ eapply HSTR with (str := cs) (slack := sl);
        [rewrite unsigned_lit by lia; exact HB | exact HZ | rewrite unsigned_lit by lia; exact HA | assumption]
    | intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI & _);
      subst ms';
      rewrite ret_pc_even by first [lia | reflexivity];
      pose proof (rw_cells_transport rsegs [] _ m' _ _ FR MU WM I) as FR';
      assert (HM' : munch [(S + -128, S)] m m')
        by (eapply munch_trans; [exact HM0 | eapply munch_weaken; [|exact MU]; intros x _; exact I]);
      assert (HW' : wmono rsegs m m') by (eapply wmono_trans; [exact HW0 | exact WM]);
      clear FR HM0 HW0 HB ST TY HI ]
  end.
  ub_until 0x154b8. ub_tail_done.
Qed.

Definition ub_open_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (S t v d pretty lit : Z) (ms' : machine_state) : Prop :=
  exists (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte) (j0 j1 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x15654) (Z_to_bv 64 (S + -128)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 v)
                  (Z_to_bv 64 t) (Z_to_bv 64 lit) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                  (Z_to_bv 64 1) (Z_to_bv 64 pretty) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x154b8) fc None m' (seg_rom rsegs) /\
    munch [(S + -128, S)] m m' /\ wmono rsegs m m' /\
    rw_cells rsegs m' (S + -128)
      [CB 8 j0; C8 (Z_to_bv 64 d); CB 8 j1; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3;
       C8 s2; C8 s1; C8 s0; C8 ra].

Lemma ub_seg_open : forall (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (S t v pretty d k : Z) (junk : list byte),
  k = 5 \/ k = 6 ->
  0x40000 <= S + -128 -> S <= 2 ^ 63 -> 0 <= t < 2 ^ 64 -> 0 < v -> v mod 8 = 0 -> v + 56 <= 2 ^ 64 ->
  v + 56 <= S + -128 \/ S <= v -> 0 <= d < 2 ^ 64 ->
  rw_cells rsegs m (S + -128) [CB 128 junk] ->
  bytes_at rsegs m v (le4 (Z_to_bv 64 k)) ->
  mem_inv rsegs m ->
  evt rsegs (ub_open_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m S t v d pretty
               (if k =? 6 then 0x1041a else 0x10333))
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 d)
             a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x155ac) fc None m (seg_rom rsegs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m S t v pretty d k junk
    Hk HS1 HS2 Ht Hv0 Hv7 Hv64 Hv Hd FR TY HI.
  apply ub_roc4 in TY.
  assert (HM : munch [(S + -128, S)] m m) by apply munch_refl.
  assert (HW : wmono rsegs m m) by apply wmono_refl.
  destruct Hk as [->| ->]; ub_until 0x154b8;
    (apply evt_done; unfold ub_open_post; do 15 eexists; split; [reflexivity|];
     split; [eassumption|]; split; [eassumption|]; eassumption).
Qed.
