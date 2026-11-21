(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_st4 Z_tr_fb1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition blR (L : dlay) (sp : word) (last bufp mb r BV : Z) (s : deflate_state) (w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  tfR L sp last (ds_d_max_code s) bufp ra gp tp t0 t1 t2 (wz (dl_As L + 2750)) w (wz (ds_l_max_code s)) (wz 14) (wz (Z_BL_ORDER + r)) (wz (Z_BL_ORDER + (mb + 1)))
      (wz 16) (wz BV) s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Definition tfb_blo_iter_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb r : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 w pcx m',
    ms' = MS (blR L sp last bufp mb (r + 1) BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1bac0 /\ r + 1 <> mb + 1) \/ (pcx = 0x1bb34 /\ r + 1 = mb + 1)).

Ltac blo_fin MU WM GA GD Gpend LOW SIDE RW :=
  apply evt_done; unfold tfb_blo_iter_post, blR, tfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV, Z_BL_ORDER; RW; do 6 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_blo_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r V : Z) (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bdl (arr_get bl_order_a r) ->
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= r <= mb -> mb <= 18 ->
  0 <= V < 65536 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt psegs (tfb_blo_iter_post L s sp last bufp mb r (sbF_PB PB PD BB BV V 3) (sbF_PD PD BV 3) (sbF_BB BB BV V 3) (sbF_BV BV 3)
                ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (blR L sp last bufp mb r BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bac0) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros EV EMH HW MI LAY RDB Rr Rmb RV RBV RPD ROOM. unfold blR, tfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (bl_order_bound r) as Ro.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI (arr_get bl_order_a r) ltac:(lia)) as [_ RDl]. rewrite <- EV in RDl.
  pose proof (u8ro_read psegs m Z_BL_ORDER (av8 bl_order_a 19) r _ (wa (Z_BL_ORDER + r)) (rod_bl_order m MI)
                (av8_nth bl_order_a 19 r ltac:(lia)) ltac:(lia) eq_refl) as RDo.
  unfold Z_BL_ORDER in *.
  replace (dl_As L + 2748 + 4 * arr_get bl_order_a r + 2) with (dl_As L + 2750 + arr_get bl_order_a r * 4) in RDl by lia.
  zsb. rewrite (bv8_small (arr_get bl_order_a r)) by lia.
  zs2. shl_norm. zs2. zs2. rewrite (zx16_small V) by lia. clear EV.
  zs2. zs2. sb_or w1 LO BB (exact HW).
  zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. zs2. replace (74816 + r + 1) with (74816 + (r + 1)) by lia.
    zstep. br_cases K2.
    + blo_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
    + blo_fin MU WM GA GD Gpend ltac:(exact LO) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_ge _ _)) by lia).
  - (* [comment removed for export] *)
    sbf_b0 L Gpend PB PD (nbv BB BV V) LO.
    sbf_b1 L Gpend GD PB PD (nbv BB BV V) LO.
    zs2. zs2. zs2. rewrite srlw_val16 by lia.
    zs2. zs2. zs2. zs2. reg_as (BV + -13) (BV + 3 - 16). replace (74816 + r + 1) with (74816 + (r + 1)) by lia.
    zstep. br_cases K2.
    + blo_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(left) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
    + blo_fin MU WM GA GD Gpend ltac:(apply lo16_unsigned_wz) ltac:(right) ltac:(rewrite !(proj2 (Z.ltb_lt _ _)) by lia).
Qed.

Lemma bl_calls_S : forall s r k, bl_calls s r (S k) = (arr_get (ds_bl_tree_dl s) (arr_get bl_order_a r), 3) :: bl_calls s (r + 1) k.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition tfb_blo_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (R : deflate_state)
    (ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 w PB' PD' BB' BV' m',
    ms' = MS (blR L sp last bufp mb (mb + 1) BV' s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bb34) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' w (wz BV') /\ bv_unsigned w mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma tfb_blo_loop : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wcell w : word)
    (ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wcell (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= r -> Z.of_nat (S k) = mb + 1 - r -> mb <= 18 ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bdl i < 65536) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  evt psegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (blR L sp last bufp mb r BV s w ra gp tp t0 t1 t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bac0) fc None m (seg_rom psegs)).
Proof.
  induction k as [|k IH]; intros until m; intros Ebdl EMH HW MI LAY MU WM RDB Rr Ek Rmb RBd RBV RPD HSB ER.
  all: pose proof (bl_order_bound r) as Ro.
  all: rewrite bl_calls_S in HSB, ER; rewrite <- Ebdl in HSB, ER.
  all: apply sbs_ok_cons_flat in HSB; destruct HSB as (_ & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wcell w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [bl_calls sbs_run] in ER. replace (r + 1) with (mb + 1) by lia.
    apply evt_done. unfold tfb_blo_post. do 9 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia].
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wcell w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with H : EM ?mm _ _ _ _ ?wc _, HB : bv_unsigned ?wc mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s bfc bdl sp last bufp mb (r + 1) R m0); [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| exact Rmb| exact RBd
        | apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia| exact HSB2| exact ER] end.
Qed.
