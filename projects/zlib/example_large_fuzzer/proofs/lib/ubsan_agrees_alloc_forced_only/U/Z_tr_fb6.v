(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_cb4 Z_tr_cb5 Z_tr_st4 Z_tr_fb1 Z_tr_fb4 Z_tr_fb5 Z_tr_st7.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel FlushBlockModel TreesTab RefFlushBlk12.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

Lemma sx16_small : forall v, 0 <= v < 32768 -> sx16 (wz v) = wz v.
Proof.
  intros v Hv. unfold sx16. f_equal. rewrite Z_to_bv_small by (unfold bv_modulus; cbn; lia).
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn -[Z.add Z.sub Z.modulo]. rewrite Z.mod_small by lia. lia.
Qed.

Definition ublR (L : dlay) (sp : word) (last bufp mb k r BV : Z) (s : deflate_state) (w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz k) (wz (ds_l_max_code s + 1)) (wz (dl_As L + 2748)) (wz 14) (wz 31)
       (wz (18446744073709551615 - (dl_As L + 2748))) (wz (Z_BL_ORDER + r)) (wz 16) (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6.

Definition tfb_blo_iter_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb k r : Z) (PB : arr) (PD BB BV : Z)
    (ra gp tp s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 w pcx m',
    ms' = MS (ublR L sp last bufp mb (k - 1) (r + 1) BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ EM m' L s PB PD w (wz BV) /\ bv_unsigned w mod 2^16 = BB mod 2^16
    /\ ((pcx = 0x1cc64 /\ k - 1 <> 0) \/ (pcx = 0x1cd4c /\ k - 1 = 0)).

Ltac blo_fin MU WM GA GD Gpend DEC LOW SIDE :=
  apply evt_done; unfold tfb_blo_iter_post, ublR, utfR, sbF_PB, sbF_PD, sbF_BB, sbF_BV, Z_BL_ORDER; DEC; do 7 eexists;
  split; [reflexivity|]; split; [exact MU|]; split; [exact WM|]; split; [eassumption|]; split; [close_EM GA GD Gpend|]; split; [LOW|];
  SIDE; split; [reflexivity| lia].

Lemma tfb_blo_iter : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb k r V : Z) (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  V = arr_get bdl (arr_get bl_order_a r) ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 -> 0 <= r <= mb -> mb <= 18 -> 1 <= k < 2^31 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  0 <= V < 16 -> 0 <= BV <= 16 -> 0 <= PD -> (13 < BV -> PD + 2 <= 65536) ->
  evt usegs (tfb_blo_iter_post L s sp last bufp mb k r (sbF_PB PB PD BB BV V 3) (sbF_PD PD BV 3) (sbF_BB BB BV V 3) (sbF_BV BV 3)
                ra gp tp s7 s8 s9 s10 s11 t6 F fc m)
      (MS (ublR L sp last bufp mb k r BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1cc64) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros EV EMH HW MI LAY RDB Rr Rmb Rk Rlm Rdm RV RBV RPD ROOM. unfold ublR, utfR.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (bl_order_bound r) as Ro.
  lay_open LAY. open_EM EMH.
  destruct (RDB m (munch_refl _ _) (wmono_refl _ _) MI (arr_get bl_order_a r) ltac:(lia)) as [_ RDl]. rewrite <- EV in RDl.
  pose proof (u8ro_read usegs m Z_BL_ORDER (av8 bl_order_a 19) r _ (wa (Z_BL_ORDER + r)) (rod_bl_order m MI)
                (av8_nth bl_order_a 19 r ltac:(lia)) ltac:(lia) eq_refl) as RDo.
  unfold Z_BL_ORDER in *.
  zsb. rewrite (bv8_small (arr_get bl_order_a r)) by lia.
  zs2. shl_norm.
  replace (dl_As L + 2748 + 4 * arr_get bl_order_a r + 2) with (dl_As L + 2748 + arr_get bl_order_a r * 4 + 2) in RDl by lia.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    ustep TF_TRAP. ustep TF_TRAP. zs2. zs. rewrite (sx16_small V) by lia.
    zs. zs. sb_or w1 LO BB (exact HW).
    zstep. zs2. zstep. zstep. zs2. zs2. replace (74816 + r + 1) with (74816 + (r + 1)) by lia. reg_as (k + -1) (k - 1).
    zstep. br_cases_s K2.
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(right).
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_ge (16 - 3) BV)) by lia) ltac:(exact LO) ltac:(left).
  - (* [comment removed for export] *)
    ustep TF_TRAP. ustep TF_TRAP. zs2. zs. rewrite (zx16_small V) by lia. zs2. zs2. shl_g0. ustep TF_TRAP.
    zs. zs. zs. zs. sb_or w1 LO BB (exact HW).
    zs. zs. zstep. zs.
    uwalk 0x1ccc4 TF_TRAP. at_pc 0x1ccc4.
    pb_store Gpend PB 65536 (dl_Ab L) PD (wrap8 (Z.land (nbv BB BV V) 255)) ltac:(apply lo8_wrap8_land; exact LO).
    zs. zs. rd_c2 GD 55%nat 1. zsb. zs. zs. zs.
    uwalk 0x1ccf8 TF_TRAP. at_pc 0x1ccf8.
    pb_store Gpend (arr_set PB PD (wrap8 (Z.land (nbv BB BV V) 255))) 65536 (dl_Ab L) (PD + 1) (wrap8 (Z.shiftr (wrap16 (nbv BB BV V)) 8)) ltac:(apply hi8_lo16; exact LO).
    uwalk 0x1cd14 TF_TRAP. at_pc 0x1cd14.
    zs2. rewrite srlw_val16 by lia.
    pose proof (shiftr_wrap16_range V (16 - BV) ltac:(lia)) as RSH.
    zs2. zstep. zstep. br_true. zstep. zs2. zs2. replace (74816 + r + 1) with (74816 + (r + 1)) by lia. reg_as (k + -1) (k - 1). reg_as (BV + -13) (BV + 3 - 16).
   
    zstep. br_cases_s K2.
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(right).
    + blo_fin MU WM GA GD Gpend ltac:(rewrite !(proj2 (Z.ltb_lt (16 - 3) BV)) by lia) ltac:(apply lo16_unsigned_wz) ltac:(left).
Qed.

Lemma bl_calls_S : forall s r k, bl_calls s r (S k) = (arr_get (ds_bl_tree_dl s) (arr_get bl_order_a r), 3) :: bl_calls s (r + 1) k.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition tfb_blo_post (L : dlay) (s : deflate_state) (sp : word) (last bufp mb : Z) (R : deflate_state)
    (ra gp tp s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t2 t3 t4 t5 w PB' PD' BB' BV' m',
    ms' = MS (ublR L sp last bufp mb 0 (mb + 1) BV' s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1cd4c) fc None m' (seg_rom usegs)
    /\ munch (Wem L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ EM m' L s PB' PD' w (wz BV') /\ bv_unsigned w mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV' /\ 0 <= BV' <= 16 /\ 0 <= PD'.

Lemma tfb_blo_loop : forall (k : nat) (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb r : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= r -> Z.of_nat (S k) = mb + 1 - r -> mb <= 18 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s r (S k)) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m0)
      (MS (ublR L sp last bufp mb (Z.of_nat (S k)) r BV s w ra gp tp t2 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1cc64) fc None m (seg_rom usegs)).
Proof.
  induction k as [|k IH]; intros until m; intros Ebdl EMH HW MI LAY MU WM RDB Rr Ek Rmb Rlm Rdm RBd RBV RPD HSB ER.
  all: pose proof (bl_order_bound r) as Ro.
  all: rewrite bl_calls_S in HSB, ER; rewrite <- Ebdl in HSB, ER.
  all: apply sbs_ok_cons_flat in HSB; destruct HSB as (_ & ROOM & HSB2); rewrite sbs_run_cons_flat in ER.
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb (Z.of_nat 1) r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wbb w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ lia. } 1:{ exact Rlm. } 1:{ exact Rdm. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    cbn [bl_calls sbs_run] in ER. replace (r + 1) with (mb + 1) by lia. change (Z.of_nat 1 - 1) with 0.
    apply evt_done. unfold tfb_blo_post. do 10 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
    split; [exact ER|]. split; [apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia].
  - call (tfb_blo_iter L s bfc bdl sp last bufp mb (Z.of_nat (S (S k))) r (arr_get bdl (arr_get bl_order_a r)) PB PD BB BV wbb w).
    1:{ reflexivity. } 1:{ exact EMH. } 1:{ exact HW. } 1:{ exact MI. } 1:{ exact LAY. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. }
    1:{ lia. } 1:{ exact Rmb. } 1:{ lia. } 1:{ exact Rlm. } 1:{ exact Rdm. } 1:{ apply RBd. lia. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM; lia. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    replace (Z.of_nat (S (S k)) - 1) with (Z.of_nat (S k)) by lia.
    match goal with H : EM ?mm _ _ _ _ ?wc _, HB : bv_unsigned ?wc mod _ = _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH L s bfc bdl sp last bufp mb (r + 1) R m0); [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| exact Rmb| exact Rlm| exact Rdm| exact RBd
        | apply sbF_BV_range; [exact RBV| lia]| pose proof (sbF_PD_range PD BV 3 RPD); lia| exact HSB2| exact ER] end.
Qed.

(* [comment removed for export] *)
Lemma tfb_dyn_hdr2 : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last bufp mb : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV : Z) (wbb w : word)
    (ra gp tp t2 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned w mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono usegs m0 m ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> 0 <= mb <= 18 ->
  0 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  R = sbs_run (upd4 s PB PD BB BV) (bl_calls s 0 (Z.to_nat (mb + 1))) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m0)
      (MS (utfR L sp last (ds_d_max_code s) bufp ra gp tp w (wz BV) t2 (wz (mb + 1)) (wz (ds_l_max_code s + 1)) a2 a3 a4 a5 a6 a7 (wz 0) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x1cc34) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ebdl EMH HW MI LAY MU WM RDB Rmb Rlm Rdm RBd RBV RPD HSB ER. unfold utfR.
  pose proof LAY as LAY'. lay_open LAY'.
  zs2. reg_as (dl_As L + 2047 + 701) (dl_As L + 2748). do 3 zs2. zs2. rewrite zb_lxor_ones by lia. do 3 zs2.
  destruct (Z.to_nat (mb + 1)) as [|k] eqn:En; [lia|].
  replace (wz 74816) with (wz (Z_BL_ORDER + 0)) by reflexivity. reg_as (mb + 1) (Z.of_nat (S k)).
  eapply (tfb_blo_loop k L s bfc bdl sp last bufp mb 0 R m0 PB PD BB BV wbb w);
    [exact Ebdl| exact EMH| exact HW| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact Rlm| exact Rdm| exact RBd| exact RBV| exact RPD| exact HSB| exact ER].
Qed.

(* [comment removed for export] *)
Lemma tfb_dyn_hdr : forall (L : dlay) (s : deflate_state) (bfc bdl : arr) (sp : word) (last len bufp mb : Z) (R : deflate_state)
    (PB : arr) (PD BB BV : Z) (wbb : word) (hB1 hB2 hB3 : list byte)
    (ra gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  bdl = ds_bl_tree_dl s ->
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv usegs m -> dlay_ok L ->
  rw_cells usegs m (dl_As L + 2904) (dsB_cells L s hB1 hB2 hB3) ->
  ct_readable (Wem L) m (dl_As L + 2748) bfc bdl 39 ->
  0 <= last <= 1 -> 256 <= ds_l_max_code s < 573 -> 0 <= ds_d_max_code s < 61 -> 3 <= mb <= 18 ->
  (forall i, 0 <= i < 19 -> 0 <= arr_get bdl i < 16) ->
  0 <= BV <= 16 -> 0 <= PD ->
  sbs_ok 65536 (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  R = sbs_run (upd4 s PB PD BB BV) (hd_calls last s mb) ->
  evt usegs (tfb_blo_post L s sp last bufp mb R ra gp tp s7 s8 s9 s10 s11 t6 F fc m)
      (MS (utfR L sp last len bufp ra gp tp t0 t1 t2 (wz mb) (wz BV) a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1c7e0) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros Ebdl EMH HBB MI LAY GB RDB Rl Rlm Rdm Rmb RBd RBV RPD HSB ER.
  pose proof (munch_refl (Wem L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb. pose proof (dlay_ranges _ LAY) as (Rs & _ & _ & _ & Rb & _).
  unfold dsB_cells in GB. unfold hd_calls in HSB, ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM1 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM2 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM3 & HSB). rewrite sbs_run_cons_flat in ER.
  apply sbs_ok_cons_flat in HSB. destruct HSB as (_ & ROOM4 & HSB). rewrite sbs_run_cons_flat in ER.
  pose proof (sbF_BV_range BV 3 RBV ltac:(lia)) as RBV1. pose proof (sbF_BV_range _ 5 RBV1 ltac:(lia)) as RBV2.
  pose proof (sbF_BV_range _ 5 RBV2 ltac:(lia)) as RBV3. pose proof (sbF_BV_range _ 4 RBV3 ltac:(lia)) as RBV4.
  assert (RPD1 : 0 <= sbF_PD PD BV 3) by (apply sbF_PD_nonneg; exact RPD).
  assert (RPD2 : 0 <= sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) by (apply sbF_PD_nonneg; exact RPD1).
  assert (RPD3 : 0 <= sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) by (apply sbF_PD_nonneg; exact RPD2).
  assert (RPD4 : 0 <= sbF_PD (sbF_PD (sbF_PD (sbF_PD PD BV 3) (sbF_BV BV 3) 5) (sbF_BV (sbF_BV BV 3) 5) 5) (sbF_BV (sbF_BV (sbF_BV BV 3) 5) 5) 4) by (apply sbF_PD_nonneg; exact RPD3).
  call (tfb_d1 L s sp last len bufp mb PB PD BB BV wbb).
  1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact Rl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ intros; apply ROOM1; lia. } 1:{ lia. }
  match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    call (tfb_d2 L s sp last len bufp mb pb pd bb bv0 (sbF_BV BV 3) wc hB1 hB2 hB3);
    [exact H| exact HB| eassumption| exact LAY| exact GB| exact Rlm| exact Rdm| exact RBV1| lia| intros; apply ROOM2; lia|] end.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> X2]|[-> X2]] end.
  - (* [comment removed for export] *)
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3k L s sp last bufp mb pb pd bb bv wc wc);
      [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM4; lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
  - (* [comment removed for export] *)
    match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (tfb_d3f L s sp last bufp mb pb pd bb bv wc wc);
      [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM3; lia| lia|] end.
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X3]|[-> X3]] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4k L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
    + match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        call (tfb_d4f L s sp last bufp mb pb pd bb bv wc wc);
        [exact H| exact HB| eassumption| exact LAY| lia| lia| lia| lia| apply ROOM4; lia| lia|] end.
      match goal with H : EM ?mm _ _ ?pb ?pd ?wc (wz ?bv0), HB : bv_unsigned ?wc mod _ = ?bb mod _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply (tfb_dyn_hdr2 L s bfc bdl sp last bufp mb R m pb pd bb bv0 wc wc);
        [exact Ebdl| exact H| exact HB| eassumption| exact LAY| exact MU| exact WM| exact RDB| lia| lia| lia| exact RBd| exact RBV4| exact RPD4| exact HSB| exact ER] end.
Qed.
