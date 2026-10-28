(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Walk. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_small R_m2s R_thread R_cache_defs R_prim_defs R_unwind_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Definition zal (k x r : Z) : Prop := (x mod k = r)%Z.
Local Lemma zal_ex : forall k x r : Z, (0 < k)%Z -> (x mod k = r)%Z -> exists q, x = (k * q + r)%Z.
Proof. intros k x r Hk H. exists (x / k)%Z. rewrite <- H. apply Z.div_mod. lia. Qed.
Local Ltac zlit x := lazymatch x with Zpos _ => idtac | Z0 => idtac | Zneg _ => idtac end.
Local Ltac zget_mod t :=
  lazymatch type of t with
  | (?x mod ?k = ?r)%Z => let H' := fresh "Hzm" in pose proof t as H'
  | ?A /\ ?B => first [ zget_mod constr:(proj1 t) | zget_mod constr:(proj2 t) ]
  end.
Local Ltac zhide :=
  repeat match goal with
  | H : context [(?x mod ?k)%Z] |- _ => zlit x; zlit k; let v := eval cbv in (x mod k)%Z in change (x mod k)%Z with v in H
  end;
  repeat match goal with
  | H : (?x mod ?k = ?r)%Z |- _ =>
      let q := fresh "zq" in let Hq := fresh "Hzq" in
      destruct (zal_ex k x r (eq_refl : (0 < k)%Z) H) as [q Hq]; change (zal k x r) in H
  | H : context [(?x mod ?k = ?r)%Z] |- _ =>
      lazymatch type of H with (_ mod _ = _)%Z => fail | _ => idtac end;
      (try zget_mod H); change (x mod k = r)%Z with (zal k x r) in H
  end;
  repeat match goal with
  | H : context [(2 ^ ?k)%Z] |- _ => let T := type of H in zify_arith_prop T;
      let v := eval cbv in (2 ^ k)%Z in lazymatch v with Zpos _ => change (2 ^ k)%Z with v in H end
  end.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call ctasegs m mm MU WM end end.
Open Scope bv_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition uwf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (B lo : Z) (tr : list Z) (tb : list word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom ctasegs)
    /\ munch [(B + 8, B + 12); (B + 16, B + 2056); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m m' /\ wmono ctasegs m m'
    /\ mem_inv ctasegs m'
    /\ rw_cells ctasegs m' (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))]
    /\ u64arr ctasegs m' (B + 16) (wr_trace tr tb)
    /\ stk ctasegs m' lo (bv_unsigned sp).

Section UWF.
Variables (ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : mem) (B pc top maxd lo : Z) (tb : list word).
Hypothesis HB : (0 <= B /\ B + 2056 <= 2^63)%Z.
Hypothesis Hpc : (0 <= pc < 2^64)%Z.
Hypothesis Htop : (0 <= top < 2^64)%Z.
Hypothesis Hmaxd : (2 <= maxd <= 255)%Z.
Hypothesis Htb : length tb = 255%nat.
Hypothesis HLO : (lo <= bv_unsigned sp - 64)%Z.
Hypothesis HSP : (bv_unsigned sp <= B)%Z.

Definition uwf_Q (tr : list Z) : machine_state -> Prop :=
  uwf_post ra sp gp tp s0o s1o s2o s3o s4o s5o s6o s7 s8 s9 s10 s11 F fc B lo tr tb m0.

(* [comment removed for export] *)
Lemma uwf_exit : forall tr ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 t3 t4 t5 t6 (m : mem),
  (Z.of_nat (length tr) <= 255)%Z ->
  rw_cells ctasegs m (bv_unsigned sp - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk ctasegs m lo (bv_unsigned sp - 64) ->
  rw_cells ctasegs m (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length tr)))] ->
  u64arr ctasegs m (B + 16) (wr_trace tr tb) ->
  munch [(B + 8, B + 12); (B + 16, B + 2056); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m0 m -> wmono ctasegs m0 m ->
  mem_inv ctasegs m ->
  evt ctasegs (uwf_Q tr)
    (MS (mkR ra' (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10
             s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1e6b24) fc None m (seg_rom ctasegs)).
Proof.
  intros until m. intros Hl FR ST SZ TB MU WM MI.
  zhide.
  do 9 zstep.
  replace (bv_unsigned sp - 64 + 64)%Z with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp).
  zstep.
  finish.
Qed.

Definition uwf_W : list (Z * Z) := [(B + 8, B + 12); (B + 16, B + 2056); (bv_unsigned sp - 64, bv_unsigned sp)]%Z.

(* [comment removed for export] *)
Lemma uwf_loop : forall (ch : list (Z * Z)) f acc tr t0 t1 t2 a6 a7 t3 t4 t5 t6 (m : mem),
  uw_loop pc 4096 (top - 16) maxd ch f acc = Some tr ->
  (1 <= Z.of_nat (length acc) <= maxd)%Z -> (4096 <= top)%Z ->
  chain_cells uwf_W m0 f ch ->
  rw_cells ctasegs m (bv_unsigned sp - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
  stk ctasegs m lo (bv_unsigned sp - 64) ->
  rw_cells ctasegs m (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length acc)))] ->
  u64arr ctasegs m (B + 16) (wr_trace acc tb) ->
  munch uwf_W m0 m -> wmono ctasegs m0 m -> mem_inv ctasegs m ->
  evt ctasegs (uwf_Q tr)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0 t1 t2 (Z_to_bv 64 maxd) (Z_to_bv 64 (top - 16))
             (Z_to_bv 64 B) (Z_to_bv 64 pc) (Z_to_bv 64 f) (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16))
             (Z_to_bv 64 (Z.of_nat (length acc))) a6 a7 (Z_to_bv 64 0x701ae0) s3o s4o s5o s6o s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1e6ae8) fc None m (seg_rom ctasegs)).
Proof.
  induction ch as [|[ra0 fp] ch IH]; intros f acc tr t0 t1 t2 a6 a7 t3 t4 t5 t6 m HU Hl HT4 CC FR ST SZ TB MU WM MI;
    [cbn in HU; discriminate|].
  cbn [uw_loop] in HU. destruct CC as (RC & (Hra & Hfp & Hf) & HD & CC).
  unfold uwf_W in *.
  pose proof (wr_trace_length acc tb ltac:(lia)) as TL.
  zhide.
  zstep.
  destruct (Z.leb_spec maxd (Z.of_nat (length acc))) as [C1|C1].
  - ifT. injection HU as <-. eapply uwf_exit; eassumption || lia.
  - ifF.
    pose proof (rw_cells_transport ctasegs _ m0 m _ _ RC MU WM HD) as RCm.
    zstep. zstep.
    destruct (Z.ltb_spec ra0 4096) as [C2|C2].
    + ifT. injection HU as <-. eapply uwf_exit; eassumption || lia.
    + ifF.
      (* [comment removed for export] *)
      assert (K : forall acc' (m1 : mem) t0' a7',
        acc' = (if ra0 =? pc then acc else acc ++ [ra0]) ->
        rw_cells ctasegs m1 (bv_unsigned sp - 64) [C8 s6o; C8 s5o; C8 s4o; C8 s3o; C8 s2o; C8 s1o; C8 s0o; C8 ra] ->
        stk ctasegs m1 lo (bv_unsigned sp - 64) ->
        rw_cells ctasegs m1 (B + 8) [C4 (Z_to_bv 64 (Z.of_nat (length acc')))] ->
        u64arr ctasegs m1 (B + 16) (wr_trace acc' tb) ->
        rw_cells ctasegs m1 (f + -16) [C8 (Z_to_bv 64 fp); C8 (Z_to_bv 64 ra0)] ->
        munch [(B + 8, B + 12); (B + 16, B + 2056); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m0 m1 -> wmono ctasegs m0 m1 ->
        mem_inv ctasegs m1 ->
        evt ctasegs (uwf_Q tr)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp t0' t1 t2 (Z_to_bv 64 maxd) (Z_to_bv 64 (top - 16))
                   (Z_to_bv 64 B) (Z_to_bv 64 pc) (Z_to_bv 64 f) (Z_to_bv 64 4096) (Z_to_bv 64 (B + 16))
                   (Z_to_bv 64 (Z.of_nat (length acc'))) (Z_to_bv 64 ra0) a7' (Z_to_bv 64 0x701ae0) s3o s4o s5o s6o
                   s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x1e6b0c) fc None m1 (seg_rom ctasegs))).
      { intros acc' m1 t0' a7' Eacc FR1 ST1 SZ1 TB1 RC1 MU1 WM1 MI1.
        rewrite <- Eacc in HU.
        assert (Hl' : (1 <= Z.of_nat (length acc') <= maxd)%Z).
        { subst acc'. destruct (ra0 =? pc); [lia| rewrite app_length; cbn [length]; lia]. }
        zstep. zstep.
        destruct (Z.leb_spec fp f) as [C3|C3].
        - ifT. unfold fr_ok in HU. rewrite (proj2 (Z.ltb_ge f fp)) in HU by lia. cbn [andb] in HU. injection HU as <-.
          eapply uwf_exit; eassumption || lia.
        - ifF. zstep.
          destruct (Z.leb_spec (top - 16) fp) as [C4|C4].
          + ifT. unfold fr_ok in HU. rewrite (proj2 (Z.ltb_lt f fp)), (proj2 (Z.ltb_ge fp (top - 16))) in HU by lia.
            cbn [andb] in HU. injection HU as <-. eapply uwf_exit; eassumption || lia.
          + ifF. zstep. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z.
            zstep. zstep.
            destruct (Z.eqb_spec (fp mod 8) 0) as [C5|C5].
            * ifT. unfold fr_ok in HU. rewrite (proj2 (Z.ltb_lt f fp)), (proj2 (Z.ltb_lt fp (top - 16))), C5 in HU by lia.
              cbn [andb Z.eqb] in HU.
              eapply IH; eassumption || lia.
            * ifF. unfold fr_ok in HU. rewrite (proj2 (Z.ltb_lt f fp)), (proj2 (Z.ltb_lt fp (top - 16))),
                (proj2 (Z.eqb_neq (fp mod 8) 0)) in HU by lia.
              cbn [andb] in HU. injection HU as <-. eapply uwf_exit; eassumption || lia. }
      zstep.
      destruct (Z.eqb_spec ra0 pc) as [C6|C6].
      * ifT. subst ra0. eapply K; try eassumption. reflexivity.
      * ifF.
        pose proof HD as HD'. cbn [disjoint_from] in HD'.
        do 4 zstep.
        rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
        replace (B + 16 + Z.of_nat (length acc) * 8)%Z with (B + 16 + 8 * Z.of_nat (length acc))%Z by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          match goal with TB0 : u64arr ctasegs mm (B + 16) _ |- _ =>
            pose proof (u64arr_store_ok ctasegs mm (B + 16) _ (Z.of_nat (length acc))
                          (Z_to_bv 64 (B + 16 + 8 * Z.of_nat (length acc))) TB0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO;
            zstep;
            pose proof (u64arr_write ctasegs mm (B + 16) _ (Z.of_nat (length acc)) (Z_to_bv 64 ra0) TB0 ltac:(lia)) as TB';
            clear TB0 end end.
        store_done.
        rewrite Nat2Z.id, wr_trace_snoc in TB' by lia.
        replace (Z.of_nat (length acc) + 1)%Z with (Z.of_nat (length (acc ++ [ra0]))) in *
          by (rewrite app_length; cbn [length]; lia).
        eapply K with (acc' := acc ++ [ra0]); try eassumption.
        first [ reflexivity | rewrite (proj2 (Z.eqb_neq ra0 pc)) by lia; reflexivity ].
Qed.
End UWF.

Definition uwf_entry_W (B sp : Z) : list (Z * Z) := [(B + 8, B + 12); (B + 16, B + 2056); (sp - 64, sp)]%Z.

(* [comment removed for export] *)
Lemma unwindfast_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (B pc bp top bot maxd lo : Z) (ch : list (Z * Z)) (tb : list word) (szw : word)
    (tr : list Z),
  (0 <= B /\ B + 2056 <= 2^63)%Z -> (0 <= pc < 2^64)%Z -> (0 <= bp < 2^64)%Z -> (0 <= bot < top)%Z -> (top < 2^64)%Z ->
  (2 <= maxd <= 255)%Z -> length tb = 255%nat ->
  unwind_trace pc 4096 bot top maxd bp ch = Some tr ->
  chain_cells (uwf_entry_W B (bv_unsigned sp)) m bp ch ->
  rw_cells ctasegs m 0x5a9218 [C8 (Z_to_bv 64 0x701ae0)] -> rw_cells ctasegs m 0x701ae0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells ctasegs m (B + 8) [C4 szw] -> u64arr ctasegs m (B + 16) tb ->
  stk ctasegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 64)%Z -> (bv_unsigned sp <= B)%Z -> (0xbcb000 <= lo)%Z ->
  mem_inv ctasegs m ->
  evt ctasegs (uwf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc B lo tr tb m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 pc) (Z_to_bv 64 bp) (Z_to_bv 64 top) (Z_to_bv 64 bot)
             (Z_to_bv 64 maxd) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 unwindfast_entry) fc None m (seg_rom ctasegs)).
Proof.
  intros until tr. intros HB Hpc Hbp Hbt Htop Hmaxd Htb HTR CC G1 G3 SZ TB ST HLO HSP HIMG MI.
  unfold unwindfast_entry, uwf_entry_W in *.
  pose proof (munch_refl [(B + 8, B + 12); (B + 16, B + 2056); (bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl ctasegs m) as WM.
  apply box in CC.
  carve_frame 64%nat ST.
  zhide.
  zidle_begin sp 64%Z MUz WMz.
  do 8 zstep.
  zidle_end MUz WMz.
  do 1 zstep.
  do 4 zstep.
  change 4294967295%Z with (Z.ones 32). rewrite Z.land_ones, Z.mod_small by lia.
  zstep. ifF.
  do 3 zstep. zstep. ifF.
  do 3 zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    match goal with TB0 : u64arr ctasegs mm (B + 16) _ |- _ =>
      pose proof (u64arr_store_ok ctasegs mm (B + 16) _ 0 (Z_to_bv 64 (B + 16)) TB0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as SO;
      zstep;
      pose proof (u64arr_write ctasegs mm (B + 16) _ 0 (Z_to_bv 64 pc) TB0 ltac:(lia)) as TB';
      clear TB0 end end.
  replace (B + 16 + 8 * 0)%Z with (B + 16)%Z in TB' by lia.
  store_done.
  rewrite (wr_trace_one pc tb) in TB' by lia.
  replace (bv_unsigned sp + -64)%Z with (bv_unsigned sp - 64)%Z in * by lia.
  zstep.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 12)%Z with 4096%Z.
  unfold unwind_trace in HTR.
  destruct (Z.eqb_spec (top / 4096) 0) as [T0|T0].
  - ifF. zstep. injection HTR as <-.
    eapply uwf_exit with (m0 := m) (tb := tb) (B := B) (lo := lo); try eassumption; cbn [length Z.of_nat]; lia.
  - ifT.
    assert (T4 : (4096 <= top)%Z).
    { destruct (Z.lt_ge_cases top 4096) as [Hlt|Hge]; [| exact Hge]. exfalso. apply T0. apply Z.div_small. lia. }
    zstep. ifF.
    zstep.
    destruct (Z.leb_spec bp bot) as [C1|C1].
    + ifT. unfold fr_ok in HTR. rewrite (proj2 (Z.ltb_ge bot bp)) in HTR by lia. cbn [andb] in HTR. injection HTR as <-.
      eapply uwf_exit with (m0 := m) (tb := tb) (B := B) (lo := lo); try eassumption; cbn [length Z.of_nat]; lia.
    + ifF. do 2 zstep.
      replace (top + -16)%Z with (top - 16)%Z by lia.
      destruct (Z.leb_spec (top - 16) bp) as [C2|C2].
      * ifT. unfold fr_ok in HTR. rewrite (proj2 (Z.ltb_lt bot bp)), (proj2 (Z.ltb_ge bp (top - 16))) in HTR by lia.
        cbn [andb] in HTR. injection HTR as <-.
        eapply uwf_exit with (m0 := m) (tb := tb) (B := B) (lo := lo); try eassumption; cbn [length Z.of_nat]; lia.
      * ifF. zstep. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3)%Z with 8%Z.
        zstep.
        destruct (Z.eqb_spec (bp mod 8) 0) as [C3|C3].
        -- ifF. do 2 zstep.
           unfold fr_ok in HTR. rewrite (proj2 (Z.ltb_lt bot bp)), (proj2 (Z.ltb_lt bp (top - 16))), C3 in HTR by lia.
           cbn [andb Z.eqb] in HTR.
           eapply uwf_loop with (m0 := m) (tb := tb) (B := B) (lo := lo) (maxd := maxd) (top := top) (acc := [pc]) (f := bp)
             (ch := ch) (tr := tr); try eassumption; try lia.
           all: first [ exact (unbox _ CC) | (cbn [length Z.of_nat]; lia) ].
        -- ifT. unfold fr_ok in HTR. rewrite (proj2 (Z.ltb_lt bot bp)), (proj2 (Z.ltb_lt bp (top - 16))),
             (proj2 (Z.eqb_neq (bp mod 8) 0)) in HTR by lia.
           cbn [andb] in HTR. injection HTR as <-.
           eapply uwf_exit with (m0 := m) (tb := tb) (B := B) (lo := lo); try eassumption; cbn [length Z.of_nat]; lia.
Qed.
