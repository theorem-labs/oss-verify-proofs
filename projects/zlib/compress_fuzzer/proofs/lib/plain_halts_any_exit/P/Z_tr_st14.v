(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_cb3 Z_tr_cb4 Z_tr_st1 Z_tr_st12 Z_tr_st13.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Trees SendModel BitsModel BitsModel2 FillWinModel TrSmallModel TreeModel RefSendTree3 RefSendTree4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition st_loop_post (L : dlay) (s : deflate_state) (T mc : Z) (R : deflate_state)
    (ra sp gp tp s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists n' nl' s0 s1 s2 s3 s4 s5 s6 s7 s8 wbb PB' PD' BB' BV' m',
    ms' = MS (stR L T (mc + 1) n' nl' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) F (wz 0x1ccfc) fc None m' (seg_rom psegs)
    /\ munch (Wem L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ EM m' L s PB' PD' wbb (wz BV') /\ bv_unsigned wbb mod 2^16 = BB' mod 2^16
    /\ R = upd4 s PB' PD' BB' BV'.

Lemma st_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (tfc tdl bfc bdl : arr) (T N mc : Z) (R : deflate_state) (m0 : mem)
    (PB : arr) (PD BB BV n prevlen nextlen count mx mn : Z) (wbb : word)
    (ra sp gp tp s0 s2 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  EM m L s PB PD wbb (wz BV) -> bv_unsigned wbb mod 2^16 = BB mod 2^16 -> mem_inv psegs m -> dlay_ok L ->
  munch (Wem L) m0 m -> wmono psegs m0 m ->
  ct_readable (Wem L) m0 T tfc tdl N -> tdl = tree_dl s t -> 0 < T -> T + 4 * N < 2^63 -> mc + 1 < N -> N <= 573 ->
  ct_readable (Wem L) m0 (dl_As L + 2748) bfc bdl 39 -> bfc = ds_bl_tree_fc s -> bdl = ds_bl_tree_dl s ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get bfc i < 65536) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get tdl i <= 15) -> (forall i, 0 <= i < N -> 0 <= arr_get tdl i < 65536) ->
  0 <= n <= mc -> nextlen = arr_get tdl n -> Z.of_nat (S f) = mc + 1 - n ->
  0 <= BV <= 16 -> 0 <= PD -> 0 <= count < mx -> (mx = 138 \/ mx = 6 \/ mx = 7) -> (mn = 3 \/ mn = 4) -> -1 <= prevlen <= 15 ->
  R = send_tree_loop (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  send_tree_ok 65536 (S f) (upd4 s PB PD BB BV) t mc n prevlen nextlen count mx mn ->
  evt psegs (st_loop_post L s T mc R ra sp gp tp s9 s10 s11 F fc m0)
      (MS (stR L T (mc + 1) n nextlen ra sp gp tp s0 (wz count) s2 (wz mx) (wz mn) (wz prevlen) s6 s7 s8 s9 s10 s11) F (wz 0x1c858) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros EMH HBB MI LAY MU WM RDT Etdl RT1 RT2 RmcN RN RDB Ebfc Ebdl RBf RTl RTn Rn Enl Ef RBV RPD Rc Rmx Rmn Rpl ER OK.
  - call (st_iter L s t tfc tdl bfc bdl T N mc n 0%nat R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [exfalso; lia|].
    match goal with E : R = send_tree_loop 0 _ _ _ _ _ _ _ _ _ |- _ => rewrite send_loop_0 in E; rename E into ER' end.
    apply evt_done. unfold st_loop_post. do 17 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact ER'].
  - call (st_iter L s t tfc tdl bfc bdl T N mc n (S f) R m PB PD BB BV prevlen nextlen count mx mn wbb).
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Etdl. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RmcN. } 1:{ exact RN. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| apply sub_fp_refl]. } 1:{ exact Ebfc. } 1:{ exact Ebdl. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. }
    1:{ exact Rn. } 1:{ exact Enl. } 1:{ exact RBV. } 1:{ exact RPD. } 1:{ exact Rc. } 1:{ exact Rmx. } 1:{ exact Rmn. } 1:{ exact Rpl. } 1:{ exact ER. } 1:{ exact OK. }
    match goal with H : _ \/ _ |- _ => destruct H as [[-> X]|[-> X]] end; [|exfalso; lia].
    match goal with E : R = send_tree_loop (S f) _ _ _ _ _ _ _ _ _, O : send_tree_ok _ (S f) _ _ _ _ _ _ _ _ _ |- _ =>
      eapply (IH L s t tfc tdl bfc bdl T N mc R m0); [eassumption| eassumption| eassumption| exact LAY| exact MU| exact WM| exact RDT| exact Etdl| exact RT1| exact RT2
        | exact RmcN| exact RN| exact RDB| exact Ebfc| exact Ebdl| exact RBf| exact RTl| exact RTn| lia| reflexivity| lia| assumption| assumption| assumption| assumption| assumption| assumption
        | exact E| exact O] end.
Qed.

Definition Z_SEND_TREE : Z := 0x1c7b8.
Definition tsz (t : tree_id) : Z := match t with TL => 573 | TD => 61 | TB => 39 end.

Lemma tree_readable : forall (W : list ivl) (m : mem) (L : dlay) (s : deflate_state) (t : tree_id),
  dlt m L s -> ddt m L s -> dbt m L s -> disjoint_from W (dl_As L + 212) 2692 ->
  ct_readable W m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsz t).
Proof.
  intros W m L s t Glt Gdt Gbt D. destruct t; cbn [toff tree_fc tree_dl tsz].
  - eapply ct_readable_rw; [exact Glt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gdt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
  - eapply ct_readable_rw; [exact Gbt| lia| lia|]. revert D. clear. induction W as [|[a b] W IH]; cbn [disjoint_from]; [tauto|]. intros [D1 D2]. split; [lia| apply IH; exact D2].
Qed.

Definition send_tree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom psegs)
    /\ munch (cbW L lo sp) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ stk psegs m' lo (bv_unsigned sp)
    /\ DST m' L (send_tree s t mc).

Lemma send_tree_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (mc lo : Z)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
  DST m L s -> mem_inv psegs m ->
  stk psegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 80 -> dlay_below L lo (bv_unsigned sp) ->
  0 <= mc -> mc + 1 < tsz t ->
  (forall i, 0 <= i < 39 -> 0 <= arr_get (ds_bl_tree_fc s) i < 65536) ->
  (forall i, 0 <= i <= mc -> 0 <= arr_get (tree_dl s t) i <= 15) -> (forall i, 0 <= i < tsz t -> 0 <= arr_get (tree_dl s t) i < 65536) ->
  BINV 65536 s -> send_tree_safe 65536 s t mc ->
  a0 = wz (dl_As L) -> a1 = wz (dl_As L + toff t) -> a2 = wz mc ->
  evt psegs (send_tree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc L s t mc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_SEND_TREE) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros ST MI STK LO BEL Rmc RmcN RBf RTl RTn BI SAFE -> -> ->. unfold Z_SEND_TREE.
  pose proof BI as (RBV & RBB & RPD).
  pose proof (munch_refl (cbW L lo sp) m) as MU. pose proof (wmono_refl psegs m) as WM.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MUs.
  open_DST ST. lay_open LAY. below_open BEL. pose proof (ln_pend _ LENS) as LNP.
  pose proof (lo_sb _ LAY) as SEPsb. unfold apart in SEPsb.
  assert (RDT : ct_readable (cbW L lo sp) m (dl_As L + toff t) (tree_fc s t) (tree_dl s t) (tsz t)) by (apply tree_readable; [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RDB : ct_readable (cbW L lo sp) m (dl_As L + 2748) (ds_bl_tree_fc s) (ds_bl_tree_dl s) 39) by (apply (tree_readable _ m L s TB); [exact Glt| exact Gdt| exact Gbt| cbn [disjoint_from]; lia]).
  assert (RtN : tsz t <= 573 /\ 212 <= toff t /\ toff t + 4 * tsz t <= 2904) by (destruct t; cbn [tsz toff]; lia).
  pose proof (RTn 0 ltac:(lia)) as Rnl0.
  unfold send_tree_safe, RefSendTree4.OK, RefSendTree3.cnts0, Len in SAFE. replace (mc + 1 - 0) with (mc + 1) in SAFE by lia.
  carve_frame 80%nat STK.
  zstep. br_false.
  do 10 zstep.
  mv_group dsA_munch GA MUs WM. mv_group dsD_munch GD MUs WM. mv_group dpend_munch Gpend MUs WM. clear MUs.
  lazymatch goal with MIc : mem_inv psegs ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => destruct (RDT mc MU WM MIc 0 ltac:(lia)) as [_ RDl0] end.
  replace (dl_As L + toff t + 4 * 0 + 2) with (dl_As L + toff t + 2) in RDl0 by lia.
  pose proof (EM_of_groups _ _ _ GA GD Gpend LNP) as EMH. clear GA GD Gpend.
  assert (HBB : bv_unsigned (wz (ds_bi_buf s)) mod 2^16 = ds_bi_buf s mod 2^16) by apply lo16_unsigned_wz.
  assert (EX0 : upd4 s (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) = s) by apply upd4_self.
  zs2. zs2. rewrite (zx16_small (arr_get (tree_dl s t) 0)) by lia. zs2. zs2. zs2. zs2.
  zstep. br_cases_s K0.
  -
    rewrite (proj2 (Z.eqb_eq _ _) K0) in SAFE. cbn [fst snd] in SAFE. rewrite K0 in SAFE.
    rewrite K0. change (Z.b2z (0 <? 0)) with 0.
    do 16 zs2.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) 0 0 138 3) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsz t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) 0 0 138 3 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ symmetry; exact K0. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ left; reflexivity. } 1:{ left; reflexivity. } 1:{ lia. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_eq _ _) K0), K0, En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold stR. do 11 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
  -
    rewrite (proj2 (Z.eqb_neq _ _) K0) in SAFE. cbn [fst snd] in SAFE.
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia. change (Z.b2z true) with 1.
    do 17 zs2.
    destruct (Z.to_nat (mc + 1)) as [|f] eqn:En; [lia|].
    remember (send_tree_loop (S f) s t mc 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4) as R eqn:ER.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
      call (st_loop f L s t (tree_fc s t) (tree_dl s t) (ds_bl_tree_fc s) (ds_bl_tree_dl s) (dl_As L + toff t) (tsz t) mc R mcur
                    (ds_pending_buf s) (ds_pending s) (ds_bi_buf s) (ds_bi_valid s) 0 (-1) (arr_get (tree_dl s t) 0) 0 7 4 (wz (ds_bi_buf s))) end.
    1:{ exact EMH. } 1:{ exact HBB. } 1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ lia. } 1:{ lia. } 1:{ exact RmcN. } 1:{ lia. }
    1:{ eapply ct_readable_rebase; [exact RDB| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact RBf. } 1:{ exact RTl. } 1:{ exact RTn. } 1:{ lia. } 1:{ reflexivity. } 1:{ lia. }
    1:{ exact RBV. } 1:{ lia. } 1:{ lia. } 1:{ right; right; reflexivity. } 1:{ right; reflexivity. } 1:{ lia. }
    1:{ rewrite EX0. exact ER. } 1:{ rewrite EX0. exact SAFE. }
    match goal with E : R = upd4 s ?pb ?pd ?bb ?bv |- _ =>
      assert (EQF : send_tree s t mc = upd4 s pb pd bb bv);
      [ unfold send_tree, Len; rewrite (proj2 (Z.eqb_neq _ _) K0), En; rewrite <- ER; exact E |] end.
    match goal with H : EM ?mm _ _ _ _ _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof H as EMf end. pose proof EMf as (_ & _ & _ & LNF).
    match goal with HB : bv_unsigned ?wb mod _ = ?bb mod _ |- _ => lazymatch type of EMf with EM _ _ _ _ _ wb _ =>
      destruct (EM_to_groups _ _ _ _ _ _ _ bb _ EMf (le2_wz_mod _ _ HB) eq_refl) as (HA & HD & HP) end end.
    unfold stR. do 11 zstep.
    release_frame FR STK (bv_unsigned sp).
    apply evt_done. unfold send_tree_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
    rewrite EQF. tr_groups MU WM.
    cb_close HA HD HP GB GC Glt Gdt Gbt Gblc Gheap Gdep Gwin Gprev Ghead LENS LAY. close_lens_sbF LENS.
Qed.
