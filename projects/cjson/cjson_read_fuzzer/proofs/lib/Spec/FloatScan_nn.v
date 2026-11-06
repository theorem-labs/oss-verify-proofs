(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Bool.
From Stdlib Require List.
From Stdlib Require Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.Riscv Require Fpu.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Module FloatScan_split.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import ListNotations.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Fpu LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fmodl_scale (sx : Z) (st : Z * Z * Z) : Z :=
  let '(xhi, xlo, ex) := st in
  if ex <=? 0 then
    let ux := mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor (ex + 120) sx) 0xffff) 48)) xlo in
    f128_mul ux C_2PM120
  else
    mk128 (Z.lor (Z.land xhi 0x0000ffffffffffff) (Z.shiftl (Z.land (Z.lor ex sx) 0xffff) 48)) xlo.

(* [comment removed for export] *)
Definition fmodl_K2 (sx : Z) (st : Z * Z * Z) : option Z :=
  match fmodl_norm_loop 130%nat st with
  | None => None
  | Some st' => Some (fmodl_scale sx st')
  end.

(* [comment removed for export] *)
Definition fmodl_fin (x yhi ylo : Z) (xhi xlo : Z) : (Z * Z) + Z :=
  let hi := u64 (xhi - yhi) in
  let lo := u64 (xlo - ylo) in
  let hi := if xlo <? ylo then u64 (hi - 1) else hi in
  if Z.shiftr hi 63 =? 0 then
    if Z.lor hi lo =? 0 then inr (let t := f128_of_i32 0 in f128_mul t x)
    else inl (hi, lo)
  else inl (xhi, xlo).

(* [comment removed for export] *)
Definition fmodl_K1 (x yhi ylo sx : Z) (res : (Z * Z * Z) + Z) : option Z :=
  match res with
  | inr v => Some v
  | inl (xhi, xlo, ex) =>
    match fmodl_fin x yhi ylo xhi xlo with
    | inr v => Some v
    | inl (xhi, xlo) => fmodl_K2 sx (xhi, xlo, ex)
    end
  end.

Lemma m_fmodl_split : forall x y,
  m_fmodl x y =
  let uxhi := hi64 x in let uxlo := lo64 x in
  let uyhi := hi64 y in let uylo := lo64 y in
  let ex := Z.land (Z.shiftr uxhi 48) 0x7fff in
  let ey := Z.land (Z.shiftr uyhi 48) 0x7fff in
  let sx := Z.land (Z.shiftr uxhi 48) 0x8000 in
  let t := f128_of_i32 0 in
  if (f128_le y t =? 0) || (m_fpclassifyl y =? 0) || (ex =? 0x7fff) then
    let t := f128_mul x y in Some (f128_div t t)
  else
  let ux := mk128 (Z.land uxhi 0x7fffffffffffffff) uxlo in
  let uy := mk128 (Z.land uyhi 0x7fffffffffffffff) uylo in
  if f128_le ux uy <=? 0 then
    if f128_le ux uy =? 0 then let t := f128_of_i32 0 in Some (f128_mul t x) else Some x
  else
  let '(ux, ex) := if ex =? 0 then
      let ux := f128_mul ux C_2P120 in (ux, Z.shiftr (hi64 ux) 48 - 120) else (ux, ex) in
  let '(uy, ey) := if ey =? 0 then
      let uy := f128_mul uy C_2P120 in (uy, Z.shiftr (hi64 uy) 48 - 120) else (uy, ey) in
  let xhi := Z.lor (Z.land (hi64 ux) 0x0000ffffffffffff) (2^48) in
  let yhi := Z.lor (Z.land (hi64 uy) 0x0000ffffffffffff) (2^48) in
  let xlo := lo64 ux in
  let ylo := lo64 uy in
  match fmodl_sub_loop (S (Z.to_nat (ex - ey))) x yhi ylo ey (xhi, xlo, ex) with
  | None => None
  | Some res => fmodl_K1 x yhi ylo sx res
  end.
Proof.
  intros x y. unfold m_fmodl. cbv zeta.
  destruct (_ || _ || _); [reflexivity|].
  destruct (f128_le _ _ <=? 0); [reflexivity|].
  destruct (Z.land (Z.shiftr (hi64 x) 48) 32767 =? 0), (Z.land (Z.shiftr (hi64 y) 48) 32767 =? 0);
  (destruct (fmodl_sub_loop _ _ _ _ _ _) as [[[[xhi xlo] ex]|v]|]; [|reflexivity|reflexivity]);
  unfold fmodl_K1, fmodl_fin, fmodl_K2, fmodl_scale; cbv zeta;
  (destruct (Z.shiftr _ 63 =? 0); [destruct (Z.lor _ _ =? 0); [reflexivity|]|]);
  (destruct (fmodl_norm_loop _ _) as [[[xhi2 xlo2] ex2]|]; [|reflexivity]); destruct (ex2 <=? 0); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fmodl_sub_loop_step : forall n x yhi ylo ey xhi xlo ex,
  fmodl_sub_loop (S n) x yhi ylo ey (xhi, xlo, ex) =
  if ey <? ex then
    match fmodl_sub_body x yhi ylo (xhi, xlo, ex) with
    | inl st' => fmodl_sub_loop n x yhi ylo ey st'
    | inr r => Some (inr r)
    end
  else Some (inl (xhi, xlo, ex)).
Proof. reflexivity. Qed.

Lemma fmodl_norm_loop_step : forall n xhi xlo ex,
  fmodl_norm_loop (S n) (xhi, xlo, ex) =
  if Z.shiftr xhi 48 =? 0 then fmodl_norm_loop n (fmodl_norm_body (xhi, xlo, ex)) else Some (xhi, xlo, ex).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DecfloatK.
  Variables (fuelc : nat) (bits emin sign pok : Z).
  Let emax := - emin - bits + 3.
  Let zero0 := f128_of_i32 0.

  (* [comment removed for export] *)
  Definition dfK_dn (f : shfile) (rp a z e2 : Z) (x : list Z) : option (shfile * Z) :=
    match df_dn_loop FUEL_SCALE (mkDS rp a z e2 x 0) with
    | None => None
    | Some (mkDS rp a z e2 x i) =>
      match df_final a z x e2 bits emin sign emax zero0 zero0 with
      | None => None
      | Some y => Some (f, y)
      end
    end.

  Definition dfK_up (f : shfile) (rp a z e2 : Z) (x : list Z) : option (shfile * Z) :=
    match df_up_loop FUEL_SCALE (mkUS rp a z e2 x) with
    | None => None
    | Some (mkUS rp a z e2 x) => dfK_dn f rp a z e2 x
    end.

  (* [comment removed for export] *)
  Definition dfK_al (f : shfile) (rp z : Z) (x : list Z) : option (shfile * Z) :=
    match (if nz (Z.rem rp 9) then
             let rpm9 := if 0 <=? rp then Z.rem rp 9 else Z.rem rp 9 + 9 in
             let p10 := znth p10s (8 - rpm9) in
             match df_al_loop FUEL_RING p10 z (mkAL 0 0 rp 0 x) with
             | None => None
             | Some (mkAL _ a rp carry x) =>
               let '(z, x) := if nz carry then (z + 1, zupd x z carry) else (z, x) in
               Some (a, z, rp + (9 - rpm9), x)
             end
           else Some (0, z, rp, x)) with
    | None => None
    | Some (a, z, rp, x) => dfK_up f rp a z 0 x
    end.

  Definition dfK_tz (f : shfile) (rp k : Z) (x : list Z) : option (shfile * Z) :=
    match df_tz_loop FUEL_RING x k with
    | None => None
    | Some z => dfK_al f rp z x
    end.

  (* [comment removed for export] *)
  Definition dfK_mid (f : shfile) (rp lnz k : Z) (x : list Z) : option (shfile * Z) :=
    let x0 := znth x 0 in
    match (if (lnz <? 9) && (lnz <=? rp) && (rp <? 18) then
             if rp =? 9 then
               Some (inr (f, f128_mul (f128_of_i32 sign) (f128_of_u32 x0)))
             else if rp <? 9 then
               Some (inr (f, f128_div (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (8 - rp)))))
             else
               let bitlim := bits - 3 * (rp - 9) in
               if (30 <? bitlim) || (Z.shiftr x0 bitlim =? 0) then
                 Some (inr (f, f128_mul (f128_mul (f128_of_i32 sign) (f128_of_u32 x0)) (f128_of_i32 (znth p10s (rp - 10)))))
               else Some (inl tt)
           else Some (inl tt)) with
    | None => None
    | Some (inr r) => Some r
    | Some (inl _) => dfK_tz f rp k x
    end.

  (* [comment removed for export] *)
  Definition dfK_pad (f : shfile) (lrp lnz j k : Z) (x : list Z) : option (shfile * Z) :=
    match (if nz j then
             match df_pad_loop 10%nat k (j, x) with
             | None => None
             | Some (j, x) => Some (k + 1, x)
             end
           else Some (k, x)) with
    | None => None
    | Some (k, x) => dfK_mid f (s32 lrp) lnz k x
    end.

  (* [comment removed for export] *)
  Definition dfK_rng (f : shfile) (lrp dc lnz j k : Z) (x : list Z) : option (shfile * Z) :=
    let x0 := znth x 0 in
    if x0 =? 0 then
      Some (f, f128_of_d (bv_unsigned (fmul_d RNE (fcvt_d_w RNE (Z_to_bv 64 sign)) D_ZERO)))
    else if (lrp =? dc) && (dc <? 10) && ((30 <? bits) || (Z.shiftr x0 bits =? 0)) then
      Some (f, f128_mul (f128_of_i32 sign) (f128_of_u32 x0))
    else if Z.quot (- emin) 2 <? lrp then
      Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MAX) C_LDBL_MAX)
    else if lrp <? emin - 2 * LDBL_MANT_DIG_ then
      Some (f, f128_mul (f128_mul (f128_of_i32 sign) C_LDBL_MIN) C_LDBL_MIN)
    else dfK_pad f lrp lnz j k x.

  (* [comment removed for export] *)
  Definition dfK_exp (s : st_dig) : option (shfile * Z) :=
    let 'mkDL f c j k lrp dc lnz gotdig gotrad x := s in
    let lrp := if nz gotrad then lrp else dc in
    match (if nz gotdig && (Z.lor c 32 =? 101) then
             match scanexp fuelc f pok with
             | None => None
             | Some (f, e10) =>
               if e10 =? LLONG_MIN_ then
                 if nz pok then Some (inl (sh_unget f, lrp + 0))
                 else Some (inr (sh_lim0 f, f128_of_i32 0))
               else Some (inl (f, lrp + e10))
             end
           else Some (inl ((if 0 <=? c then sh_unget f else f), lrp))) with
    | None => None
    | Some (inr r) => Some r
    | Some (inl (f, lrp)) =>
      if negb (nz gotdig) then Some (sh_lim0 f, f128_of_i32 0)
      else dfK_rng f lrp dc lnz j k x
    end.

  Definition dfK_dig (s : st_dig) : option (shfile * Z) :=
    match df_dig_loop fuelc s with
    | None => None
    | Some s' => dfK_exp s'
    end.

  (* [comment removed for export] *)
  Definition dfK_rz (gotdig c : Z) (f : shfile) : option (shfile * Z) :=
    match (if c =? 46 then
             let '(c, f) := sh_getc f in
             match df_rz_loop fuelc (gotdig, 0, c, f) with
             | None => None
             | Some (gotdig, lrp, c, f) => Some (gotdig, 1, lrp, c, f)
             end
           else Some (gotdig, 0, 0, c, f)) with
    | None => None
    | Some (gotdig, gotrad, lrp, c, f) =>
      dfK_dig (mkDL f c 0 0 lrp 0 0 gotdig gotrad (zupd (zrepeat 0 KMAX) 0 0))
    end.

  Lemma decfloat_split : forall f c,
    decfloat fuelc f c bits emin sign pok =
    match df_lz_loop fuelc (0, c, f) with
    | None => None
    | Some (gotdig, c, f) => dfK_rz gotdig c f
    end.
  Proof.
    intros f c. unfold decfloat, dfK_rz, dfK_dig, dfK_exp, dfK_rng, dfK_pad, dfK_mid, dfK_tz, dfK_al, dfK_up, dfK_dn.
    subst emax zero0.
    destruct (df_lz_loop _ _) as [[[gotdig c1] f1]|]; [|reflexivity].
    destruct (if c1 =? 46 then _ else _) as [[[[[gd gr] lrp] c2] f2]|]; [|reflexivity].
    destruct (df_dig_loop _ _) as [[f3 c3 j k lrp3 dc lnz gotdig3 gotrad3 x]|]; [|reflexivity].
    cbv beta iota zeta.
    destruct (if nz gotdig3 && _ then _ else _) as [[[f4 lrp4]|r]|]; [| reflexivity | reflexivity].
    destruct (negb (nz gotdig3)); [reflexivity|].
    destruct (znth x 0 =? 0); [reflexivity|].
    destruct (_ && _ && _); [reflexivity|].
    destruct (_ <? lrp4); [reflexivity|].
    destruct (lrp4 <? _); [reflexivity|].
    destruct (if nz j then _ else _) as [[k5 x5]|]; [|reflexivity].
    cbv beta iota zeta.
    destruct (if (lnz <? 9) && _ && _ then _ else _) as [[u|r]|]; [| reflexivity | reflexivity].
    destruct (df_tz_loop _ _ _) as [z|]; [|reflexivity].
    destruct (if nz (Z.rem _ 9) then _ else _) as [[[[a6 z6] rp6] x6]|]; [|reflexivity].
    destruct (df_up_loop _ _) as [[rp7 a7 z7 e27 x7]|]; [|reflexivity].
    destruct (df_dn_loop _ _) as [[rp8 a8 z8 e28 x8 i8]|]; [|reflexivity].
    reflexivity.
  Qed.
End DecfloatK.
End FloatScan_split.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require FmtFp_facts3.
Module FloatScan_junk.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps FloatScan_split.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.FmtFp_facts3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition JQ (f f' : shfile) : Prop :=
  sh_rpos f' = sh_rpos f /\ sh_cnt0 f' = sh_cnt0 f /\ sh_n f' = sh_n f /\
  sh_stdio f = true /\ sh_stdio f' = true /\ sh_shlim_neg f' = sh_shlim_neg f /\
  sh_rpos f <= sh_n f /\
  (forall i, i < sh_n f -> znth (sh_buf f') i = znth (sh_buf f) i).

Lemma JQ_getc : forall f f', JQ f f' ->
  fst (sh_getc f') = fst (sh_getc f) /\ JQ (snd (sh_getc f)) (snd (sh_getc f')).
Proof.
  intros f f' (A & B & C & D & E & G & R & Q).
  destruct f as [buf rpos cnt0 n st sn], f' as [buf' rpos' cnt0' n' st' sn']. cbn in *. subst.
  unfold sh_getc. cbn. destruct (Z.eqb_spec rpos n) as [->|NE]; cbn.
  - split; [reflexivity|]. unfold JQ; cbn. repeat split; try reflexivity; try lia. exact Q.
  - split; [apply Q; lia|]. unfold JQ; cbn. repeat split; try reflexivity; try lia. exact Q.
Qed.

Lemma JQ_unget : forall f f', JQ f f' -> JQ (sh_unget f) (sh_unget f').
Proof.
  intros f f' (A & B & C & D & E & G & R & Q).
  destruct f as [buf rpos cnt0 n st sn], f' as [buf' rpos' cnt0' n' st' sn']. cbn in *. subst.
  unfold sh_unget. cbn. destruct sn; cbn; unfold JQ; cbn; repeat split; try reflexivity; try lia; exact Q.
Qed.

Lemma JQ_lim0 : forall f f', JQ f f' -> JQ (sh_lim0 f) (sh_lim0 f').
Proof.
  intros f f' (A & B & C & D & E & G & R & Q).
  destruct f as [buf rpos cnt0 n st sn], f' as [buf' rpos' cnt0' n' st' sn']. cbn in *. subst.
  unfold sh_lim0, JQ; cbn. repeat split; try reflexivity; try lia. exact Q.
Qed.

Lemma JQ_cnt : forall f f', JQ f f' -> sh_cnt f' = sh_cnt f.
Proof. intros f f' (A & B & _). unfold sh_cnt. rewrite A, B. reflexivity. Qed.

Lemma JQ_unget_loop : forall k f f', JQ f f' -> JQ (fs_unget_loop k f) (fs_unget_loop k f').
Proof. induction k as [|k IH]; intros f f' J; cbn; [exact J|]. apply IH. apply JQ_unget. exact J. Qed.

(* [comment removed for export] *)
Lemma JQ_getc_eq : forall f f', JQ f f' ->
  exists c g g', sh_getc f = (c, g) /\ sh_getc f' = (c, g') /\ JQ g g'.
Proof.
  intros f f' J. destruct (JQ_getc f f' J) as [E J'].
  destruct (sh_getc f) as [c g] eqn:E1, (sh_getc f') as [c' g'] eqn:E2. cbn in E, J'. subst c'.
  exists c, g, g'. repeat split; try reflexivity. all: apply J'.
Qed.

Ltac jgetc J E1 E2 J' :=
  let c := fresh "c" in let g := fresh "g" in let g' := fresh "g'" in
  destruct (JQ_getc_eq _ _ J) as (c & g & g' & E1 & E2 & J').

(* [comment removed for export] *)

Lemma fs_ws_sim : forall n n' f f' c g, (n <= n')%nat -> JQ f f' -> fs_ws_loop n f = Some (c, g) ->
  exists g', fs_ws_loop n' f' = Some (c, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' f f' c g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [fs_ws_loop] in H |- *.
  jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
  destruct (m_isspace _).
  - eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <-. eexists. split; [reflexivity | exact J1].
Qed.

Lemma fs_inf_sim : forall n i c f f' i2 c2 g, JQ f f' -> fs_inf_loop n (i, c, f) = Some (i2, c2, g) ->
  exists g', fs_inf_loop n (i, c, f') = Some (i2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros i c f f' i2 c2 g J H; [discriminate H|].
  cbn [fs_inf_loop] in H |- *. unfold fs_inf_cond in *.
  destruct ((i <? 8) && _).
  - unfold fs_inf_body in *. destruct (i <? 7).
    + jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [exact J1 | exact H].
    + eapply IH; [exact J | exact H].
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma fs_nan_sim : forall n i c f f' i2 c2 g, JQ f f' -> fs_nan_loop n (i, c, f) = Some (i2, c2, g) ->
  exists g', fs_nan_loop n (i, c, f') = Some (i2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros i c f f' i2 c2 g J H; [discriminate H|].
  cbn [fs_nan_loop] in H |- *. unfold fs_nan_cond in *.
  destruct ((i <? 3) && _).
  - unfold fs_nan_body in *. destruct (i <? 2).
    + jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [exact J1 | exact H].
    + eapply IH; [exact J | exact H].
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma fs_par_sim : forall n n' i f f' i2 c2 g, (n <= n')%nat -> JQ f f' -> fs_par_loop n (i, f) = Some (i2, c2, g) ->
  exists g', fs_par_loop n' (i, f') = Some (i2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' i f f' i2 c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [fs_par_loop] in H |- *. unfold fs_par_body in *.
  jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
  destruct (_ || _ || _ || _).
  - eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J1].
Qed.

Lemma scanexp_l1_sim : forall n n' x c f f' x2 c2 g, (n <= n')%nat -> JQ f f' ->
  scanexp_l1_loop n (x, c, f) = Some (x2, c2, g) ->
  exists g', scanexp_l1_loop n' (x, c, f') = Some (x2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' x c f f' x2 c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [scanexp_l1_loop] in H |- *. unfold scanexp_l1_cond, scanexp_l1_body in *.
  destruct (isdigitc c && _).
  - jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma scanexp_l2_sim : forall n n' x c f f' x2 c2 g, (n <= n')%nat -> JQ f f' ->
  scanexp_l2_loop n (x, c, f) = Some (x2, c2, g) ->
  exists g', scanexp_l2_loop n' (x, c, f') = Some (x2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' x c f f' x2 c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [scanexp_l2_loop] in H |- *. unfold scanexp_l2_cond, scanexp_l2_body in *.
  destruct (isdigitc c && _).
  - jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma scanexp_l3_sim : forall n n' c f f' c2 g, (n <= n')%nat -> JQ f f' ->
  scanexp_l3_loop n (c, f) = Some (c2, g) ->
  exists g', scanexp_l3_loop n' (c, f') = Some (c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' c f f' c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [scanexp_l3_loop] in H |- *. unfold scanexp_l3_body in *.
  destruct (isdigitc c).
  - jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma scanexp_sim : forall n n' f f' pok g e, (n <= n')%nat -> JQ f f' ->
  scanexp n f pok = Some (g, e) -> exists g', scanexp n' f' pok = Some (g', e) /\ JQ g g'.
Proof.
  intros n n' f f' pok g e Hn J H. unfold scanexp in *.
  jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
  (* [comment removed for export] *)
  match type of H with context [if ?b then _ else _] =>
    let SG := fresh "SG" in destruct b eqn:SG end.
  all: cycle 1.
  - (* [comment removed for export] *)
    destruct (negb (isdigitc _)).
    + injection H as <- <-. eexists. split; [reflexivity | apply JQ_unget; exact J1].
    + destruct (scanexp_l1_loop n _) as [[[xa ca] fa]|] eqn:L1; [|discriminate H].
      destruct (scanexp_l1_sim _ n' _ _ _ _ _ _ _ Hn J1 L1) as [fa' [-> Ja]].
      destruct (scanexp_l2_loop n _) as [[[xb cb] fb]|] eqn:L2; [|discriminate H].
      destruct (scanexp_l2_sim _ n' _ _ _ _ _ _ _ Hn Ja L2) as [fb' [-> Jb]].
      destruct (scanexp_l3_loop n _) as [[cc fcc]|] eqn:L3; [|discriminate H].
      destruct (scanexp_l3_sim _ n' _ _ _ _ _ Hn Jb L3) as [fc' [-> Jc]].
      injection H as <- <-. eexists. split; [reflexivity | apply JQ_unget; exact Jc].
  - (* [comment removed for export] *)
    jgetc J1 E3 E4 J2. rewrite E3 in H. rewrite E4.
    set (h := if negb (isdigitc _) && nz pok then sh_unget _ else _) in H.
    set (h' := if negb (isdigitc _) && nz pok then sh_unget _ else _).
    assert (Jh : JQ h h') by (subst h h'; destruct (negb _ && nz pok); [apply JQ_unget; exact J2 | exact J2]).
    clearbody h h'.
    destruct (negb (isdigitc _)).
    + injection H as <- <-. eexists. split; [reflexivity | apply JQ_unget; exact Jh].
    + destruct (scanexp_l1_loop n _) as [[[xa ca] fa]|] eqn:L1; [|discriminate H].
      destruct (scanexp_l1_sim _ n' _ _ _ _ _ _ _ Hn Jh L1) as [fa' [-> Ja]].
      destruct (scanexp_l2_loop n _) as [[[xb cb] fb]|] eqn:L2; [|discriminate H].
      destruct (scanexp_l2_sim _ n' _ _ _ _ _ _ _ Hn Ja L2) as [fb' [-> Jb]].
      destruct (scanexp_l3_loop n _) as [[cc fcc]|] eqn:L3; [|discriminate H].
      destruct (scanexp_l3_sim _ n' _ _ _ _ _ Hn Jb L3) as [fc' [-> Jc]].
      injection H as <- <-. eexists. split; [reflexivity | apply JQ_unget; exact Jc].
Qed.

Lemma df_lz_sim : forall n n' gd c f f' gd2 c2 g, (n <= n')%nat -> JQ f f' ->
  df_lz_loop n (gd, c, f) = Some (gd2, c2, g) ->
  exists g', df_lz_loop n' (gd, c, f') = Some (gd2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' gd c f f' gd2 c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [df_lz_loop] in H |- *. unfold df_lz_body in *.
  destruct (c =? 48).
  - jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

Lemma df_rz_sim : forall n n' gd l c f f' gd2 l2 c2 g, (n <= n')%nat -> JQ f f' ->
  df_rz_loop n (gd, l, c, f) = Some (gd2, l2, c2, g) ->
  exists g', df_rz_loop n' (gd, l, c, f') = Some (gd2, l2, c2, g') /\ JQ g g'.
Proof.
  induction n as [|n IH]; intros n' gd l c f f' gd2 l2 c2 g Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. cbn [df_rz_loop] in H |- *. unfold df_rz_body in *.
  destruct (c =? 48).
  - jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2. eapply IH; [| exact J1 | exact H]. lia.
  - injection H as <- <- <- <-. eexists. split; [reflexivity | exact J].
Qed.

(* [comment removed for export] *)
Definition dl_setf (s : st_dig) (f : shfile) : st_dig :=
  mkDL f (dl_c s) (dl_j s) (dl_k s) (dl_lrp s) (dl_dc s) (dl_lnz s) (dl_gotdig s) (dl_gotrad s) (dl_x s).

Lemma df_dig_sim : forall n n' s f' s2, (n <= n')%nat -> JQ (dl_f s) f' ->
  df_dig_loop n s = Some s2 ->
  exists g', df_dig_loop n' (dl_setf s f') = Some (dl_setf s2 g') /\ JQ (dl_f s2) g'.
Proof.
  induction n as [|n IH]; intros n' s f' s2 Hn J H; [discriminate H|].
  destruct n' as [|n']; [lia|]. destruct s as [f c j k lrp dc lnz gd gr x]. cbn [dl_f] in J.
  cbn [df_dig_loop] in H |- *. unfold df_dig_cond, dl_setf in *. cbn [dl_c dl_f dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in *.
  destruct (isdigitc c || (c =? 46)).
  - unfold df_dig_body in *. cbn [dl_c dl_f dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in *.
    destruct (c =? 46).
    + destruct (nz gr).
      * injection H as <-. exists f'. split; [reflexivity | exact J].
      * jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
        exact (IH n' (mkDL _ _ _ _ _ _ _ _ _ _) _ _ ltac:(lia) J1 H).
    + destruct (k <? KMAX - 3).
      * jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
        destruct (j + 1 =? 9); exact (IH n' (mkDL _ _ _ _ _ _ _ _ _ _) _ _ ltac:(lia) J1 H).
      * jgetc J E1 E2 J1. rewrite E1 in H. rewrite E2.
        destruct (negb (c =? 48)); exact (IH n' (mkDL _ _ _ _ _ _ _ _ _ _) _ _ ltac:(lia) J1 H).
  - injection H as <-. exists f'. split; [reflexivity | exact J].
Qed.

(* [comment removed for export] *)
Lemma dfK_rng_file : forall bits emin sign f f' lrp dc lnz j k x,
  dfK_rng bits emin sign f' lrp dc lnz j k x =
  match dfK_rng bits emin sign f lrp dc lnz j k x with Some (_, y) => Some (f', y) | None => None end.
Proof.
  intros. unfold dfK_rng.
  destruct (znth x 0 =? 0); [reflexivity|].
  destruct (_ && _ && _); [reflexivity|].
  destruct (_ <? lrp); [reflexivity|].
  destruct (lrp <? _); [reflexivity|].
  unfold dfK_pad. destruct (if nz j then _ else _) as [[k1 x1]|]; [|reflexivity].
  unfold dfK_mid. cbv beta iota zeta.
  destruct ((lnz <? 9) && (lnz <=? s32 lrp) && (s32 lrp <? 18)).
  1: destruct (s32 lrp =? 9); [reflexivity|]; destruct (s32 lrp <? 9); [reflexivity|]; destruct (_ || _); [reflexivity|].
  all: unfold dfK_tz; destruct (df_tz_loop _ _ _) as [z|]; [|reflexivity].
  all: unfold dfK_al; destruct (if nz (Z.rem _ 9) then _ else _) as [[[[a2 z2] rp2] x2]|]; [|reflexivity].
  all: unfold dfK_up; destruct (df_up_loop _ _) as [[rp3 a3 z3 e3 x3]|]; [|reflexivity].
  all: unfold dfK_dn; cbv beta iota zeta; destruct (df_dn_loop _ _) as [[rp4 a4 z4 e4 x4 i4]|]; [|reflexivity].
  all: destruct (df_final _ _ _ _ _ _ _ _ _ _); reflexivity.
Qed.

Lemma dfK_exp_sim : forall n n' bits emin sign pok s f' g y, (n <= n')%nat -> JQ (dl_f s) f' ->
  dfK_exp n bits emin sign pok s = Some (g, y) ->
  exists g', dfK_exp n' bits emin sign pok (dl_setf s f') = Some (g', y) /\ JQ g g'.
Proof.
  intros n n' bits emin sign pok s f' g y Hn J H.
  destruct s as [f4 c4 j4 k4 lrp4 dc4 lnz4 gd4 gr4 x4]. unfold dl_setf in *. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in *.
  unfold dfK_exp in *.
  (* [comment removed for export] *)
  assert (K : forall h h' lrp,
    JQ h h' ->
    (if negb (nz gd4) then Some (sh_lim0 h, f128_of_i32 0) else dfK_rng bits emin sign h lrp dc4 lnz4 j4 k4 x4) = Some (g, y) ->
    exists g', (if negb (nz gd4) then Some (sh_lim0 h', f128_of_i32 0) else dfK_rng bits emin sign h' lrp dc4 lnz4 j4 k4 x4) = Some (g', y) /\ JQ g g').
  { intros h h' lrp Jh Hh. destruct (negb (nz gd4)).
    - injection Hh as <- <-. eexists. split; [reflexivity | apply JQ_lim0; exact Jh].
    - rewrite (dfK_rng_file bits emin sign h h'). rewrite Hh. eexists. split; [reflexivity|].
      pose proof (dfK_rng_file bits emin sign h h lrp dc4 lnz4 j4 k4 x4) as X. rewrite Hh in X. cbv beta iota in X.
      injection X as ->. exact Jh. }
  destruct (nz gd4 && (Z.lor c4 32 =? 101)).
  - destruct (scanexp n f4 pok) as [[f5 e10]|] eqn:SE; [|discriminate H].
    destruct (scanexp_sim _ n' _ _ _ _ _ Hn J SE) as [f5' [-> J5]].
    destruct (e10 =? LLONG_MIN_).
    + destruct (nz pok).
      * exact (K _ _ _ (JQ_unget _ _ J5) H).
      * injection H as <- <-. eexists. split; [reflexivity | apply JQ_lim0; exact J5].
    + exact (K _ _ _ J5 H).
  - eapply K; [| exact H]. destruct (0 <=? c4); [apply JQ_unget; exact J | exact J].
Qed.

Lemma decfloat_sim : forall n n' f f' c bits emin sign pok g y, (n <= n')%nat -> JQ f f' ->
  decfloat n f c bits emin sign pok = Some (g, y) ->
  exists g', decfloat n' f' c bits emin sign pok = Some (g', y) /\ JQ g g'.
Proof.
  intros n n' f f' c bits emin sign pok g y Hn J H. rewrite decfloat_split in H |- *.
  destruct (df_lz_loop n _) as [[[gd1 c1] f1]|] eqn:LZ; [|discriminate H].
  destruct (df_lz_sim _ n' _ _ _ _ _ _ _ Hn J LZ) as [f1' [-> J1]].
  unfold dfK_rz in *.
  assert (DIG : forall gd gr lrp c2 h h', JQ h h' ->
    dfK_dig n bits emin sign pok (mkDL h c2 0 0 lrp 0 0 gd gr (zupd (zrepeat 0 KMAX) 0 0)) = Some (g, y) ->
    exists g', dfK_dig n' bits emin sign pok (mkDL h' c2 0 0 lrp 0 0 gd gr (zupd (zrepeat 0 KMAX) 0 0)) = Some (g', y) /\ JQ g g').
  { intros gd gr lrp c2 h h' Jh Hh. unfold dfK_dig in *.
    destruct (df_dig_loop n _) as [s4|] eqn:DG; [|discriminate Hh].
    destruct (df_dig_sim n n' (mkDL h c2 0 0 lrp 0 0 gd gr (zupd (zrepeat 0 KMAX) 0 0)) h' s4 Hn Jh DG) as [f4' [E4 J4]]. unfold dl_setf in E4 at 1. cbn [dl_f dl_c dl_j dl_k dl_lrp dl_dc dl_lnz dl_gotdig dl_gotrad dl_x] in E4.
    rewrite E4. eapply dfK_exp_sim; [exact Hn | exact J4 | exact Hh]. }
  destruct (c1 =? 46).
  - jgetc J1 E1 E2 J2. rewrite E1 in H. rewrite E2.
    destruct (df_rz_loop n _) as [[[[gd3 l3] c3] f3]|] eqn:RZ; [|discriminate H].
    destruct (df_rz_sim _ n' _ _ _ _ _ _ _ _ _ Hn J2 RZ) as [f3' [-> J3]].
    exact (DIG _ _ _ _ _ _ J3 H).
  - exact (DIG _ _ _ _ _ _ J1 H).
Qed.

Lemma floatscan_sim : forall n n' f f' prec pok g y, (n <= n')%nat -> JQ f f' ->
  floatscan n f prec pok = Some (g, y) -> exists g', floatscan n' f' prec pok = Some (g', y) /\ JQ g g'.
Proof.
  intros n n' f f' prec pok g y Hn J H. unfold floatscan in *.
  destruct (if prec =? 0 then _ else _) as [[bits emin]|].
  2:{ injection H as <- <-. eexists. split; [reflexivity | exact J]. }
  destruct (fs_ws_loop n f) as [[c1 f1]|] eqn:WS; [|discriminate H].
  destruct (fs_ws_sim _ n' _ _ _ _ Hn J WS) as [f1' [-> J1]].
  (* [comment removed for export] *)
  assert (SG : forall sg c2 h h', JQ h h' ->
    (let '(sign, c, f0) := (sg, c2, h) in
     match fs_inf_loop 9 (0, c, f0) with
     | Some (i, c0, f2) =>
         if (i =? 3) || (i =? 8) || (3 <? i) && nz pok
         then Some (if negb (i =? 8) then if nz pok then fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f2) else sh_unget f2 else f2, if 0 <? sign then C_INF else C_NINF)
         else
          match (if i =? 0 then fs_nan_loop 4 (0, c0, f2) else Some (i, c0, f2)) with
          | Some (i0, c3, f3) =>
              if i0 =? 3
              then
               let '(c4, f4) := sh_getc f3 in
                if negb (c4 =? 40) then Some (sh_unget f4, C_NAN)
                else
                 match fs_par_loop n (1, f4) with
                 | Some (i1, c5, f5) =>
                     if c5 =? 41 then Some (f5, C_NAN)
                     else if negb (nz pok) then Some (sh_lim0 (sh_unget f5), f128_of_i32 0) else Some (fs_unget_loop (Z.to_nat i1) (sh_unget f5), C_NAN)
                 | None => None
                 end
              else if nz i0 then Some (sh_lim0 (sh_unget f3), f128_of_i32 0)
              else if c3 =? 48 then let '(c4, f4) := sh_getc f3 in if Z.lor c4 32 =? 120 then None else decfloat n (sh_unget f4) 48 bits emin sign pok
              else decfloat n f3 c3 bits emin sign pok
          | None => None
          end
     | None => None
     end) = Some (g, y) ->
    exists g',
    (let '(sign, c, f0) := (sg, c2, h') in
     match fs_inf_loop 9 (0, c, f0) with
     | Some (i, c0, f2) =>
         if (i =? 3) || (i =? 8) || (3 <? i) && nz pok
         then Some (if negb (i =? 8) then if nz pok then fs_unget_loop (Z.to_nat (i - 3)) (sh_unget f2) else sh_unget f2 else f2, if 0 <? sign then C_INF else C_NINF)
         else
          match (if i =? 0 then fs_nan_loop 4 (0, c0, f2) else Some (i, c0, f2)) with
          | Some (i0, c3, f3) =>
              if i0 =? 3
              then
               let '(c4, f4) := sh_getc f3 in
                if negb (c4 =? 40) then Some (sh_unget f4, C_NAN)
                else
                 match fs_par_loop n' (1, f4) with
                 | Some (i1, c5, f5) =>
                     if c5 =? 41 then Some (f5, C_NAN)
                     else if negb (nz pok) then Some (sh_lim0 (sh_unget f5), f128_of_i32 0) else Some (fs_unget_loop (Z.to_nat i1) (sh_unget f5), C_NAN)
                 | None => None
                 end
              else if nz i0 then Some (sh_lim0 (sh_unget f3), f128_of_i32 0)
              else if c3 =? 48 then let '(c4, f4) := sh_getc f3 in if Z.lor c4 32 =? 120 then None else decfloat n' (sh_unget f4) 48 bits emin sign pok
              else decfloat n' f3 c3 bits emin sign pok
          | None => None
          end
     | None => None
     end) = Some (g', y) /\ JQ g g').
  { intros sg c2 h h' Jh Hh. cbv beta iota in Hh |- *.
    destruct (fs_inf_loop 9 (0, c2, h)) as [[[i c3] h3]|] eqn:INF; [|discriminate Hh].
    destruct (fs_inf_sim _ _ _ _ _ _ _ _ Jh INF) as [h3' [-> J3]].
    destruct ((i =? 3) || (i =? 8) || (3 <? i) && nz pok).
    { injection Hh as <- <-. eexists. split; [reflexivity|].
      destruct (negb (i =? 8)); [|exact J3]. destruct (nz pok); [apply JQ_unget_loop|]; apply JQ_unget; exact J3. }
    assert (REST : forall i0 c4 h4 h4', JQ h4 h4' ->
      (if i0 =? 3 then
         let '(c5, f5) := sh_getc h4 in
         if negb (c5 =? 40) then Some (sh_unget f5, C_NAN)
         else match fs_par_loop n (1, f5) with
              | Some (i1, c6, f6) => if c6 =? 41 then Some (f6, C_NAN) else if negb (nz pok) then Some (sh_lim0 (sh_unget f6), f128_of_i32 0) else Some (fs_unget_loop (Z.to_nat i1) (sh_unget f6), C_NAN)
              | None => None end
       else if nz i0 then Some (sh_lim0 (sh_unget h4), f128_of_i32 0)
       else if c4 =? 48 then let '(c5, f5) := sh_getc h4 in if Z.lor c5 32 =? 120 then None else decfloat n (sh_unget f5) 48 bits emin sg pok
       else decfloat n h4 c4 bits emin sg pok) = Some (g, y) ->
      exists g',
      (if i0 =? 3 then
         let '(c5, f5) := sh_getc h4' in
         if negb (c5 =? 40) then Some (sh_unget f5, C_NAN)
         else match fs_par_loop n' (1, f5) with
              | Some (i1, c6, f6) => if c6 =? 41 then Some (f6, C_NAN) else if negb (nz pok) then Some (sh_lim0 (sh_unget f6), f128_of_i32 0) else Some (fs_unget_loop (Z.to_nat i1) (sh_unget f6), C_NAN)
              | None => None end
       else if nz i0 then Some (sh_lim0 (sh_unget h4'), f128_of_i32 0)
       else if c4 =? 48 then let '(c5, f5) := sh_getc h4' in if Z.lor c5 32 =? 120 then None else decfloat n' (sh_unget f5) 48 bits emin sg pok
       else decfloat n' h4' c4 bits emin sg pok) = Some (g', y) /\ JQ g g').
    { clear Hh. intros i0 c4 h4 h4' J4f Hh.
      destruct (i0 =? 3).
      { jgetc J4f E1 E2 J5. rewrite E1 in Hh. rewrite E2.
        lazymatch goal with |- context [negb (?cc =? 40)] => destruct (negb (cc =? 40)) end.
        { injection Hh as <- <-. eexists. split; [reflexivity | apply JQ_unget; exact J5]. }
        destruct (fs_par_loop n _) as [[[i1 c5] h5]|] eqn:PAR; [|discriminate Hh].
        destruct (fs_par_sim _ n' _ _ _ _ _ _ Hn J5 PAR) as [h5' [-> J6]].
        destruct (c5 =? 41). { injection Hh as <- <-. eexists. split; [reflexivity | exact J6]. }
        destruct (negb (nz pok)); injection Hh as <- <-; eexists; (split; [reflexivity|]).
        - apply JQ_lim0. apply JQ_unget. exact J6.
        - apply JQ_unget_loop. apply JQ_unget. exact J6. }
      destruct (nz i0). { injection Hh as <- <-. eexists. split; [reflexivity | apply JQ_lim0; apply JQ_unget; exact J4f]. }
      destruct (c4 =? 48).
      - jgetc J4f E1 E2 J5. rewrite E1 in Hh. rewrite E2.
        lazymatch goal with |- context [Z.lor ?cc 32 =? 120] => destruct (Z.lor cc 32 =? 120) end; [discriminate Hh|].
        eapply decfloat_sim; [exact Hn | apply JQ_unget; exact J5 | exact Hh].
      - eapply decfloat_sim; [exact Hn | exact J4f | exact Hh]. }
    revert Hh. destruct (i =? 0).
    + destruct (fs_nan_loop 4 (0, c3, h3)) as [[[i0 c4] h4]|] eqn:NN; intros Hh; [|discriminate Hh].
      destruct (fs_nan_sim _ _ _ _ _ _ _ _ J3 NN) as [h4' [-> J4]]. exact (REST _ _ _ _ J4 Hh).
    + intros Hh. exact (REST _ _ _ _ J3 Hh). }
  destruct ((c1 =? 43) || (c1 =? 45)).
  - jgetc J1 E1 E2 J2. rewrite E1 in H. rewrite E2. exact (SG _ _ _ _ J2 H).
  - exact (SG _ _ _ _ J1 H).
Qed.

(* [comment removed for export] *)
Lemma strlen_loop_first0' : forall fuel s n p,
  0 <= n <= p -> (forall i, n <= i < p -> znth s i <> 0) -> znth s p = 0 -> (Z.to_nat (p - n) < fuel)%nat ->
  strlen_loop fuel s n = Some p.
Proof.
  induction fuel as [|fuel IH]; intros s n p Hn Hnz Hp Hf; [lia|].
  cbn [strlen_loop]. destruct (Z.eq_dec n p) as [->|NE].
  - rewrite Hp. reflexivity.
  - unfold nz. destruct (Z.eqb_spec (znth s n) 0) as [E|NE']; [exfalso; exact (Hnz n ltac:(lia) E)|]. cbn [negb].
    apply IH; [lia | intros i Hi; apply Hnz; lia | exact Hp | lia].
Qed.

Lemma numch_range : forall c, is_numch c = true -> 43 <= c <= 57 \/ c = 69 \/ c = 101.
Proof.
  intros c X. unfold is_numch in X.
  repeat (apply Bool.orb_true_iff in X; destruct X as [X|X]); try (apply Z.eqb_eq in X; lia).
  apply andb_true_iff in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.

Lemma znth_In'' : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec0 i 0); [lia|].
  apply nth_In. lia.
Qed.
Lemma znth_pre : forall (t rest : list Z) i, 0 <= i < Z.of_nat (length t) -> znth (t ++ rest) i = znth t i.
Proof. intros. apply znth_app_l. unfold zlength. lia. Qed.
Lemma znth_at_len : forall (t rest : list Z), znth (t ++ 0 :: rest) (Z.of_nat (length t)) = 0.
Proof. intros. rewrite znth_app_r by (unfold zlength; lia). unfold zlength. rewrite Z.sub_diag. reflexivity. Qed.

(* [comment removed for export] *)
Lemma sscanf_junk_fwd : forall t junk r, Forall (fun c => is_numch c = true) t ->
  scan_sscanf_lg (t ++ [0]) = Some r -> scan_sscanf_lg (t ++ 0 :: junk) = Some r.
Proof.
  intros t junk r NUM H. unfold scan_sscanf_lg in *.
  set (p := Z.of_nat (length t)) in *.
  assert (NZ : forall s, forall i, 0 <= i < p -> znth (t ++ s) i <> 0).
  { intros s i Hi E. subst p. rewrite znth_pre in E by lia.
    assert (IN : In (znth t i) t) by (apply znth_In''; unfold zlength; lia).
    pose proof (numch_range _ (proj1 (Forall_forall _ _) NUM _ IN)). lia. }
  rewrite (strlen_loop_first0' _ _ 0 p) in H; [| lia | intros; apply NZ; lia | apply znth_at_len | unfold fuel_of; rewrite length_app; cbn; lia].
  rewrite (strlen_loop_first0' _ _ 0 p); [| lia | intros; apply NZ; lia | apply znth_at_len | unfold fuel_of; rewrite length_app; cbn; lia].
  set (f0 := sh_lim0 (mkSh (t ++ [0]) 0 0 p true false)) in H.
  set (f0' := sh_lim0 (mkSh (t ++ 0 :: junk) 0 0 p true false)).
  assert (J0 : JQ f0 f0').
  { subst f0 f0'. unfold JQ, sh_lim0; cbn. repeat split; try reflexivity; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i 0) as [NEG|NN].
    - unfold znth. destruct (Z.ltb_spec i 0); [reflexivity | lia].
    - rewrite !znth_pre by lia. reflexivity. }
  assert (FU : (fuel_of (t ++ [0%Z]) <= fuel_of (t ++ 0%Z :: junk))%nat) by (unfold fuel_of; rewrite !length_app; cbn; lia).
  destruct (fs_ws_loop _ f0) as [[c1 f1]|] eqn:WS; [|discriminate H].
  destruct (fs_ws_sim _ _ _ _ _ _ FU J0 WS) as [f1' [-> J1]].
  pose proof (JQ_lim0 _ _ (JQ_unget _ _ J1)) as J2.
  jgetc J2 E1 E2 J3. rewrite E1 in H. rewrite E2.
  destruct (_ <? 0); [exact H|].
  pose proof (JQ_unget _ _ J3) as J4.
  destruct (floatscan _ _ 1 0) as [[h y]|] eqn:FS; [|discriminate H].
  destruct (floatscan_sim _ _ _ _ _ _ _ _ FU J4 FS) as [h' [-> J5]].
  rewrite (JQ_cnt _ _ J5). exact H.
Qed.

Theorem sscanf_junk : forall t junk, Forall (fun c => is_numch c = true) t ->
  scan_sscanf_lg (t ++ 0 :: junk) = scan_sscanf_lg (t ++ [0]).
Proof.
  intros t junk NUM.
  destruct (scan_sscanf_lg (t ++ [0])) as [r|] eqn:H.
  - exact (sscanf_junk_fwd t junk r NUM H).
  - exfalso. refine (scan_sscanf_lg_total_gen t _ _ H).
    + apply Forall_forall. intros c IN. pose proof (numch_range _ (proj1 (Forall_forall _ _) NUM _ IN)). lia.
    + apply Forall_forall. intros c IN. pose proof (numch_range _ (proj1 (Forall_forall _ _) NUM _ IN)). lia.
Qed.

(* [comment removed for export] *)
Example sscanf_junk_probe1 : scan_sscanf_lg ([49; 46; 53] ++ 0 :: [55; 120; 0])%Z = scan_sscanf_lg ([49; 46; 53] ++ [0])%Z.
Proof. vm_compute. reflexivity. Qed.
Example sscanf_junk_probe2 : scan_sscanf_lg ([45; 50; 101; 43; 57] ++ 0 :: [49; 50])%Z = scan_sscanf_lg ([45; 50; 101; 43; 57] ++ [0])%Z.
Proof. vm_compute. reflexivity. Qed.
End FloatScan_junk.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloatProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloatProps2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFpDig.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SF_ClassDiv.
Module SF_ClassConv.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import LinuxProcessSemantics.Riscv.Fpu LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.SoftFloatProps3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_Class OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassMul.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

Definition sgn_bit (sign : Z) : Z := if sign =? 1 then 0 else 1.

Lemma sgn_bit_range : forall sign, 0 <= sgn_bit sign <= 1.
Proof. intros. unfold sgn_bit. destruct (_ =? _); lia. Qed.

Section signed.
  Variable sign : Z.
  Hypothesis SGN : sign = 1 \/ sign = -1.

  Lemma of_i32_sign : f128_of_i32 sign = f128_pack (sgn_bit sign) 16383 0.
  Proof. destruct SGN as [-> | ->]; vm_compute; reflexivity. Qed.

  Let signd := fcvt_d_w RNE (Z_to_bv 64 sign).

  Lemma sign_zero_ext : f128_of_d (bv_unsigned (fmul_d RNE signd D_ZERO)) = f128_pack (sgn_bit sign) 0 0.
  Proof. subst signd. destruct SGN as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma quarter_ext : f128_of_d (bv_unsigned (fmul_d RNE D_025 signd)) = f128_pack (sgn_bit sign) 16381 0.
  Proof. subst signd. destruct SGN as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma half_sign_ext : f128_of_d (bv_unsigned (fmul_d RNE D_05 signd)) = f128_pack (sgn_bit sign) 16382 0.
  Proof. subst signd. destruct SGN as [-> | ->]; vm_compute; reflexivity. Qed.

  Lemma threeq_ext : f128_of_d (bv_unsigned (fmul_d RNE D_075 signd)) = f128_pack (sgn_bit sign) 16382 (2^111).
  Proof. subst signd. destruct SGN as [-> | ->]; vm_compute; reflexivity. Qed.
End signed.

(* [comment removed for export] *)
Definition scalbn_one_ok (n : Z) : bool :=
  f128_of_d (bv_unsigned (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) n)) =? f128_pack 0 (16383 + n) 0.

Lemma scalbn_one_table : forallb scalbn_one_ok (map Z.of_nat (seq 60 166)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma scalbn_one_ext : forall n, 60 <= n <= 225 ->
  f128_of_d (bv_unsigned (m_scalbn (fcvt_d_w RNE (Z_to_bv 64 1)) n)) = f128_pack 0 (16383 + n) 0.
Proof.
  intros n Hn. pose proof scalbn_one_table as T. rewrite forallb_forall in T.
  specialize (T n). unfold scalbn_one_ok in T. apply Z.eqb_eq. apply T.
  apply in_map_iff. exists (Z.to_nat n). split; [lia|]. apply in_seq. lia.
Qed.

(* [comment removed for export] *)
Lemma of_u32_class : forall u, 0 <= u < 2^32 ->
  exists E T, f128_of_u32 u = f128_pack 0 E T /\ packed 0 E T /\ ((E = 0 /\ T = 0) \/ 16383 <= E <= 16414).
Proof.
  intros u Hu. destruct (Z.eq_dec u 0) as [->|NZ].
  - exists 0, 0. rewrite f128_of_u32_zero. split; [reflexivity|]. split; [constructor; lia| left; lia].
  - set (L := Z.log2 u).
    assert (HL : 2^L <= u < 2^(L+1)). { subst L. destruct (Z.log2_spec u ltac:(lia)). rewrite Z.add_1_r. lia. }
    assert (HL0 : 0 <= L) by (subst L; apply Z.log2_nonneg).
    assert (HL1 : L <= 31). { destruct (Z.le_gt_cases L 31); [lia|]. assert (2^32 <= 2^L) by (apply Z.pow_le_mono_r; lia). lia. }
    clearbody L. exists (16383 + L), (u * 2^(112 - L) - 2^112).
    rewrite (f128_of_u32_val u L) by lia. split; [reflexivity|].
    assert (LO : 2^112 <= u * 2^(112 - L)).
    { replace (2^112) with (2^L * 2^(112-L)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). apply Z.mul_le_mono_nonneg_r; lia. }
    assert (HI : u * 2^(112 - L) < 2^113).
    { apply (Z.lt_le_trans _ (2^(L+1) * 2^(112-L))); [apply Z.mul_lt_mono_pos_r; lia|].
      rewrite <- Z.pow_add_r by lia. apply Z.eq_le_incl. f_equal. lia. }
    split; [constructor; lia| right; lia].
Qed.

(* [comment removed for export] *)
Definition p10_ok (k : Z) : bool :=
  let v := f128_of_i32 (znth p10s k) in
  let E := v / 2^112 in let T := v mod 2^112 in
  (0 <=? v) && (v <? 2^127) && (16386 <=? E) && (E <=? 16409).

Lemma p10_table : forallb p10_ok [0; 1; 2; 3; 4; 5; 6; 7] = true.
Proof. vm_compute. reflexivity. Qed.

Lemma of_i32_p10_class : forall k, 0 <= k <= 7 ->
  exists E T, f128_of_i32 (znth p10s k) = f128_pack 0 E T /\ packed 0 E T /\ 16386 <= E <= 16409.
Proof.
  intros k Hk. pose proof p10_table as TB. rewrite forallb_forall in TB.
  specialize (TB k ltac:(cbn; lia)). unfold p10_ok in TB. cbv zeta in TB.
  apply andb_prop in TB. destruct TB as [TB B4]. apply andb_prop in TB. destruct TB as [TB B3].
  apply andb_prop in TB. destruct TB as [B1 B2].
  apply Z.leb_le in B1. apply Z.ltb_lt in B2. apply Z.leb_le in B3. apply Z.leb_le in B4.
  set (v := f128_of_i32 (znth p10s k)) in *. clearbody v.
  exists (v / 2^112), (v mod 2^112). unfold f128_pack. split; [dlia|]. split; [constructor; dlia| lia].
Qed.
End SF_ClassConv.

(* [comment removed for export] *)
Module SF_ClassMisc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.SoftFloatProps3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_Class OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassMul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassAdd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

(* [comment removed for export] *)
Definition NNres (x : Z) : Prop := exists s E T, x = f128_pack s E T /\ packed s E T /\ nn128 E T.

Lemma NNres_pack : forall s E T, packed s E T -> nn128 E T -> NNres (f128_pack s E T).
Proof. intros. exists s, E, T. auto. Qed.

(* [comment removed for export] *)
Lemma C_2P16383_eq : C_2P16383 = f128_pack 0 32766 0. Proof. reflexivity. Qed.
Lemma C_2PM16269_eq : C_2PM16269 = f128_pack 0 114 0. Proof. reflexivity. Qed.
Lemma C_ONE_eq : C_ONE = f128_pack 0 16383 0. Proof. reflexivity. Qed.
Lemma C_LDBL_MAX_eq : C_LDBL_MAX = f128_pack 0 32766 (2^112 - 1). Proof. reflexivity. Qed.
Lemma C_LDBL_MIN_eq : C_LDBL_MIN = f128_pack 0 1 0. Proof. reflexivity. Qed.
Lemma C_LDBL_EPS_eq : C_LDBL_EPS = f128_pack 0 16271 0. Proof. reflexivity. Qed.
Lemma C_INF_eq : C_INF = f128_pack 0 32767 0. Proof. reflexivity. Qed.
Lemma C_NINF_eq : C_NINF = f128_pack 1 32767 0. Proof. reflexivity. Qed.
Lemma one_ext_eq : f128_of_d (bv_unsigned D_ONE) = f128_pack 0 16383 0. Proof. vm_compute. reflexivity. Qed.
Lemma half_ext_eq : f128_of_d (bv_unsigned D_05) = f128_pack 0 16382 0. Proof. vm_compute. reflexivity. Qed.
Lemma f128_of_i32_0 : f128_of_i32 0 = f128_pack 0 0 0. Proof. reflexivity. Qed.
Lemma f128_of_i32_1 : f128_of_i32 1 = f128_pack 0 16383 0. Proof. vm_compute. reflexivity. Qed.
Lemma f128_of_i32_m1 : f128_of_i32 (-1) = f128_pack 1 16383 0. Proof. vm_compute. reflexivity. Qed.
Lemma f128_of_i32_2 : f128_of_i32 2 = f128_pack 0 16384 0. Proof. vm_compute. reflexivity. Qed.
Lemma two_over_eps : f128_div (f128_of_i32 2) C_LDBL_EPS = f128_pack 0 16496 0. Proof. vm_compute. reflexivity. Qed.

Lemma packed_const : forall s E T, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= T < 2^112 -> packed s E T.
Proof. intros; constructor; lia. Qed.

(* [comment removed for export] *)
Lemma m_scalbnl_class : forall s E T n, packed s E T -> nn128 E T -> NNres (m_scalbnl (f128_pack s E T) n).
Proof.
  intros s E T n PK NN. unfold m_scalbnl.
  assert (MULC : forall s1 E1 T1 Ec, packed s1 E1 T1 -> nn128 E1 T1 -> 1 <= Ec <= 32766 ->
            NNres (f128_mul (f128_pack s1 E1 T1) (f128_pack 0 Ec 0))).
  { intros s1 E1 T1 Ec P1 N1 HEc.
    destruct (f128_mul_class s1 E1 T1 0 Ec 0 P1 ltac:(constructor; lia) N1 ltac:(intros X; lia)) as [E' [T' (E2 & P2 & N2 & _)]];
      [intros _ [? ?]; lia| intros; lia|].
    rewrite E2. apply NNres_pack; assumption. }
  (* [comment removed for export] *)
  match goal with |- NNres (let '(x, n0) := ?p in _) =>
    assert (RED : exists x' n', p = (x', n') /\ NNres x' /\ -16382 <= n' <= 16383) end.
  { rewrite C_2P16383_eq, C_2PM16269_eq.
    destruct (Z.ltb_spec 16383 n).
    - destruct (MULC s E T 32766 PK NN ltac:(lia)) as [s1 [E1 [T1 (-> & P1 & N1)]]].
      destruct (Z.ltb_spec 16383 (n - 16383)).
      + destruct (MULC s1 E1 T1 32766 P1 N1 ltac:(lia)) as [s2 [E2 [T2 (-> & P2 & N2)]]].
        eexists _, _. split; [reflexivity|]. split; [apply NNres_pack; assumption|]. destruct (Z.ltb_spec 16383 (n - 16383 - 16383)); lia.
      + eexists _, _. split; [reflexivity|]. split; [apply NNres_pack; assumption| lia].
    - destruct (Z.ltb_spec n (-16382)).
      + destruct (MULC s E T 114 PK NN ltac:(lia)) as [s1 [E1 [T1 (-> & P1 & N1)]]].
        destruct (Z.ltb_spec (n + (16382 - 113)) (-16382)).
        * destruct (MULC s1 E1 T1 114 P1 N1 ltac:(lia)) as [s2 [E2 [T2 (-> & P2 & N2)]]].
          eexists _, _. split; [reflexivity|]. split; [apply NNres_pack; assumption|]. destruct (Z.ltb_spec (n + (16382 - 113) + (16382 - 113)) (-16382)); lia.
        * eexists _, _. split; [reflexivity|]. split; [apply NNres_pack; assumption| lia].
      + eexists _, _. split; [reflexivity|]. split; [apply NNres_pack; assumption| lia]. }
  destruct RED as [x' [n' (-> & [s1 [E1 [T1 (-> & P1 & N1)]]] & Hn')]].
  rewrite one_ext_eq. rewrite f128_pack_hi, f128_pack_lo by (constructor; lia).
  change (Z.land (0 * 2 ^ 63 + 16383 * 2 ^ 48 + 0 / 2 ^ 64) 0x0000ffffffffffff) with 0.
  change 0xffff with (2^16 - 1). rewrite land_ones_mod, (Z.mod_small (0x3fff + n')) by lia.
  rewrite Z.shiftl_mul_pow2, Z.lor_0_l by lia. change (0 mod 2^64) with 0. rewrite mk128_val by lia.
  replace ((16383 + n') * 2 ^ 48 * 2 ^ 64 + 0) with (f128_pack 0 (16383 + n') 0) by (unfold f128_pack; lia).
  apply MULC; auto; lia.
Qed.

(* [comment removed for export] *)
Lemma abs_hi_pack : forall s E T, packed s E T ->
  Z.land (hi64 (f128_pack s E T)) 0x7fffffffffffffff = E * 2^48 + T / 2^64.
Proof.
  intros s E T PK. pose proof PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  rewrite f128_pack_hi by assumption. change 0x7fffffffffffffff with ABS_HI. apply hiword_abs; lia.
Qed.

Lemma m_fabsl_pack : forall s E T, packed s E T -> m_fabsl (f128_pack s E T) = f128_pack 0 E T.
Proof.
  intros s E T PK. pose proof PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold m_fabsl. rewrite abs_hi_pack, f128_pack_lo by assumption. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma land_top63 : forall x, 0 <= x < 2^64 -> Z.land x (2^63) = (x / 2^63) * 2^63.
Proof.
  intros x Hx. assert (Q : 0 <= x / 2^63 <= 1) by dlia.
  apply Z.bits_inj'. intros i Hi.
  rewrite Z.land_spec, Z.pow2_bits_eqb, Z.mul_pow2_bits by lia.
  destruct (Z.eqb_spec 63 i) as [<-|NE].
  - rewrite Bool.andb_true_r. change (63 - 63) with 0. rewrite !Z.testbit_odd. rewrite Z.shiftr_0_r, Z.shiftr_div_pow2 by lia.
    reflexivity.
  - rewrite Bool.andb_false_r. destruct (Z.lt_ge_cases i 63).
    + symmetry. apply Z.testbit_neg_r. lia.
    + symmetry. destruct (Z.eq_dec (x / 2^63) 0) as [E|E]; [rewrite E; apply Z.bits_0|].
      replace (x / 2^63) with 1 by lia. apply Z.bits_above_log2; [lia|]. cbn. lia.
Qed.

Lemma m_copysignl_pack : forall s E T s2 E2 T2, packed s E T -> packed s2 E2 T2 ->
  m_copysignl (f128_pack s E T) (f128_pack s2 E2 T2) = f128_pack s2 E T.
Proof.
  intros s E T s2 E2 T2 PK PK2. pose proof PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  pose proof PK2 as [Hs2 HE2 HT2]. pose proof (T_split T2 HT2) as (Hth2 & Htl2 & ET2).
  unfold m_copysignl. rewrite abs_hi_pack, f128_pack_lo, f128_pack_hi by assumption.
  change 0x8000000000000000 with (2^63). rewrite land_top63 by lia.
  replace ((s2 * 2 ^ 63 + E2 * 2 ^ 48 + T2 / 2 ^ 64) / 2 ^ 63) with s2 by dlia.
  rewrite lor_low_high by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.
End SF_ClassMisc.

(* [comment removed for export] *)
Module SF_ClassFmod.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.SoftFloatProps3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps FloatScan_split OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_Class OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassMul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassAdd SF_ClassMisc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma u64_range : forall x, 0 <= u64 x < 2^64.
Proof. intros. unfold u64. apply Z.mod_pos_bound. lia. Qed.

(* [comment removed for export] *)
Lemma f128_le_zero_pos : forall E T, packed 0 E T -> E <= 32766 -> (E <> 0 \/ T <> 0) ->
  f128_le (f128_pack 0 0 0) (f128_pack 0 E T) = -1.
Proof.
  intros E T PK HE NZ. destruct PK as [_ HE' HT].
  pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold f128_le.
  rewrite !f128_pack_hi, !f128_pack_lo by (constructor; lia).
  change (0 mod 2^64) with 0. replace (0 * 2 ^ 63 + 0 * 2 ^ 48 + 0 / 2 ^ 64) with 0 by reflexivity.
  rewrite (hiword_abs 0 E (T / 2^64)) by lia.
  change (Z.land 0 ABS_HI) with 0.
  change (if 0 =? INF_HI then negb (0 =? 0) else INF_HI <? 0) with false.
  rewrite inf_hi_eq.
  replace (E * 2 ^ 48 + T / 2 ^ 64 =? 32767 * 2 ^ 48) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (32767 * 2 ^ 48 <? E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.ltb_ge; lia).
  cbv iota.
  rewrite !Z.lor_0_r. rewrite lor_eqb0 by lia.
  replace ((T mod 2 ^ 64 =? 0) && (E * 2 ^ 48 + T / 2 ^ 64 =? 0)) with false.
  2:{ symmetry. apply Bool.andb_false_iff. destruct (Z.eq_dec (T mod 2^64) 0); [right| left]; apply Z.eqb_neq; lia. }
  rewrite Z.land_0_r. change (negb (is_neg64 0)) with true.
  destruct (Z.eqb_spec 0 (0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64)) as [E0|E0].
  - replace (0 <? T mod 2^64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - rewrite lt_s64_val by lia.
    replace (2 ^ 63 <=? 0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with false by (symmetry; apply Z.leb_gt; lia).
    change (2^63 <=? 0) with false. cbv iota.
    replace (0 <? 0 * 2 ^ 63 + E * 2 ^ 48 + T / 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma m_fpclassifyl_normal : forall s E T, packed s E T -> 1 <= E <= 32766 -> m_fpclassifyl (f128_pack s E T) = 4.
Proof.
  intros s E T PK HE. destruct PK as [Hs HE' HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  unfold m_fpclassifyl. rewrite f128_pack_hi by (constructor; lia).
  change 0x7fff with 32767. rewrite hiword_expfield by lia.
  replace (E =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (E =? 32767) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma fmodl_sub_loop_class : forall fuel x yhi ylo ey xhi xlo ex res,
  0 <= xhi < 2^64 -> 0 <= xlo < 2^64 ->
  fmodl_sub_loop fuel x yhi ylo ey (xhi, xlo, ex) = Some res ->
  match res with
  | inr v => v = f128_mul (f128_of_i32 0) x
  | inl (h, l, e) => 0 <= h < 2^64 /\ 0 <= l < 2^64 /\ Z.min ex ey <= e <= ex
  end.
Proof.
  induction fuel as [|fuel IH]; intros x yhi ylo ey xhi xlo ex res Hh Hl E; [discriminate E|].
  rewrite fmodl_sub_loop_step in E.
  destruct (Z.ltb_spec ey ex) as [LT|GE].
  - unfold fmodl_sub_body in E.
    destruct (Z.shiftr _ 63 =? 0).
    + destruct (Z.lor _ _ =? 0).
      * injection E as <-. reflexivity.
      * specialize (IH x yhi ylo ey _ _ (ex - 1) res (u64_range _) (u64_range _) E).
        destruct res as [[[h l] e]|v]; [lia| exact IH].
    + specialize (IH x yhi ylo ey _ _ (ex - 1) res (u64_range _) (u64_range _) E).
      destruct res as [[[h l] e]|v]; [lia| exact IH].
  - injection E as <-. lia.
Qed.

(* [comment removed for export] *)
Lemma fmodl_norm_loop_class : forall fuel h l e h' l' e',
  0 <= h < 2^64 -> 0 <= l < 2^64 ->
  fmodl_norm_loop fuel (h, l, e) = Some (h', l', e') ->
  0 <= h' < 2^64 /\ 0 <= l' < 2^64 /\ e - Z.of_nat fuel < e' <= e.
Proof.
  induction fuel as [|fuel IH]; intros h l e h' l' e' Hh Hl E; [discriminate E|].
  rewrite fmodl_norm_loop_step in E.
  destruct (Z.shiftr h 48 =? 0).
  - unfold fmodl_norm_body in E. specialize (IH _ _ (e - 1) h' l' e' (u64_range _) (u64_range _) E). lia.
  - injection E as <- <- <-. lia.
Qed.

(* [comment removed for export] *)
Lemma land_bit15 : forall s E, 0 <= s <= 1 -> 0 <= E < 2^15 -> Z.land (s * 2^15 + E) (2^15) = s * 2^15.
Proof.
  intros s E Hs HE. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 15 i) as [<-|NE].
  - rewrite Bool.andb_true_r, !Z.testbit_odd, !Z.shiftr_div_pow2 by lia.
    replace ((s * 2 ^ 15 + E) / 2 ^ 15) with s by dlia. replace (s * 2^15 / 2^15) with s by dlia. reflexivity.
  - rewrite Bool.andb_false_r, Z.mul_pow2_bits by lia. symmetry.
    destruct (Z.lt_ge_cases i 15); [apply Z.testbit_neg_r; lia|].
    assert (D : s = 0 \/ s = 1) by lia. destruct D as [-> | ->]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia| cbn; lia].
Qed.

Lemma fmodl_scale_pos : forall s E th h l e, 0 <= s <= 1 -> 0 <= E <= 32767 -> 0 <= th < 2^48 ->
  1 <= e <= 32766 -> 0 <= h < 2^64 -> 0 <= l < 2^64 ->
  fmodl_scale (Z.land (Z.shiftr (s * 2^63 + E * 2^48 + th) 48) 32768) (h, l, e) = f128_pack s e ((h mod 2^48) * 2^64 + l).
Proof.
  intros s E th h l e Hs HE Hth He Hh Hl.
  unfold fmodl_scale. replace (e <=? 0) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite shiftr_div by lia.
  replace ((s * 2 ^ 63 + E * 2 ^ 48 + th) / 2 ^ 48) with (s * 2^15 + E) by dlia.
  change 32768 with (2^15). rewrite land_bit15 by lia.
  rewrite (lor_low_high s e 15) by lia.
  change 0xffff with (2^16 - 1). rewrite land_ones_mod, (Z.mod_small (s * 2^15 + e)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change 0x0000ffffffffffff with (2^48 - 1). rewrite land_ones_mod by lia.
  pose proof (Z.mod_pos_bound h (2^48) ltac:(lia)) as HM.
  replace ((s * 2 ^ 15 + e) * 2 ^ 48) with ((s * 2 ^ 15 + e) * 2 ^ 48) by lia.
  rewrite (lor_low_high (s * 2^15 + e) (h mod 2^48) 48) by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

Lemma abs_repack : forall s E T, packed s E T ->
  mk128 (Z.land (s * 2^63 + E * 2^48 + T / 2^64) 9223372036854775807) (T mod 2^64) = f128_pack 0 E T.
Proof.
  intros s E T PK. destruct PK as [Hs HE HT]. pose proof (T_split T HT) as (Hth & Htl & ET).
  change 9223372036854775807 with ABS_HI. rewrite hiword_abs by lia. rewrite mk128_val by lia. unfold f128_pack. lia.
Qed.

(* [comment removed for export] *)
Lemma Some_inj1 : forall (a b : Z), Some a = Some b -> a = b.
Proof. intros a b H. injection H. auto. Qed.

Theorem m_fmodl_class : forall L sx Ex Tx sy Ey Ty r,
  packed sx Ex Tx -> packed sy Ey Ty ->
  ((Ex = 0 /\ Tx = 0) \/ (L <= Ex <= 32766)) -> L <= Ey <= 32766 -> 130 <= L ->
  m_fmodl (f128_pack sx Ex Tx) (f128_pack sy Ey Ty) = Some r ->
  exists s' E' T', r = f128_pack s' E' T' /\ packed s' E' T' /\ nn128 E' T'
    /\ ((E' = 0 /\ T' = 0) \/ (L - 129 <= E' <= Z.max Ex Ey)).
Proof.
  intros L sx Ex Tx sy Ey Ty r PX PY CX CY HL FM.
  pose proof PX as [Hsx HEx HTx]. pose proof PY as [Hsy HEy HTy].
  pose proof (T_split Tx HTx) as (Hthx & Htlx & ETx). pose proof (T_split Ty HTy) as (Hthy & Htly & ETy).
  rewrite m_fmodl_split in FM. cbv zeta in FM.
  rewrite !f128_pack_hi, !f128_pack_lo in FM by assumption.
  change 0x7fff with 32767 in FM. rewrite !hiword_expfield in FM by lia.
  (* [comment removed for export] *)
  replace (f128_le (f128_pack sy Ey Ty) (f128_of_i32 0) =? 0) with false in FM.
  2:{ replace (f128_of_i32 0) with 0 by reflexivity. assert (D : sy = 0 \/ sy = 1) by lia. destruct D as [-> | ->].
      - rewrite f128_le_pos_zero; [reflexivity| exact PY| lia| lia].
      - rewrite f128_le_neg_zero; [reflexivity| exact PY| lia| lia]. }
  rewrite (m_fpclassifyl_normal sy Ey Ty PY) in FM by lia.
  replace (Ex =? 32767) with false in FM by (symmetry; apply Z.eqb_neq; lia). cbn [orb Z.eqb] in FM.
  rewrite (abs_repack sx Ex Tx PX), (abs_repack sy Ey Ty PY) in FM.
  (* [comment removed for export] *)
  assert (ZX : exists s', f128_mul (f128_of_i32 0) (f128_pack sx Ex Tx) = f128_pack s' 0 0 /\ 0 <= s' <= 1).
  { rewrite f128_of_i32_0. exists (Z.lxor sx 0). rewrite (f128_mul_zero 0 0 0 sx Ex Tx); [| constructor; lia| exact PX| lia| lia| lia| lia| lia].
    split; [reflexivity|]. rewrite Z.lxor_0_r. lia. }
  destruct ZX as [sz [EZ Hsz]].
  destruct (f128_le (f128_pack 0 Ex Tx) (f128_pack 0 Ey Ty) <=? 0) eqn:LE.
  { destruct (_ =? 0).
    - injection FM as <-. exists sz, 0, 0. split; [exact EZ|]. split; [constructor; lia|]. split; [intros E; lia| left; lia].
    - injection FM as <-. exists sx, Ex, Tx. split; [reflexivity|]. split; [exact PX|]. split; [intros E; lia|]. destruct CX; [left; lia| right; lia]. }
  (* [comment removed for export] *)
  assert (NX : L <= Ex <= 32766).
  { destruct CX as [[-> ->]|CX]; [| exact CX]. exfalso.
    rewrite (f128_le_zero_pos Ey Ty) in LE; [discriminate LE| constructor; lia| lia| lia]. }
  replace (Ex =? 0) with false in FM by (symmetry; apply Z.eqb_neq; lia).
  replace (Ey =? 0) with false in FM by (symmetry; apply Z.eqb_neq; lia).
  match type of FM with match fmodl_sub_loop ?n ?x ?yh ?yl ?ey (?xh, ?xl, ?ex) with _ => _ end = _ =>
    pose proof (fmodl_sub_loop_class n x yh yl ey xh xl ex) as SL;
    destruct (fmodl_sub_loop n x yh yl ey (xh, xl, ex)) as [res|]; [| discriminate FM] end.
  specialize (SL res).
  assert (RXH : forall E T, packed 0 E T -> 0 <= Z.lor (Z.land (hi64 (f128_pack 0 E T)) 281474976710655) (2 ^ 48) < 2^64).
  { intros E T PK. apply lor_bound; [lia| | lia]. change 281474976710655 with (2^48 - 1). rewrite land_ones_mod by lia.
    pose proof (Z.mod_pos_bound (hi64 (f128_pack 0 E T)) (2^48)). lia. }
  specialize (SL (RXH Ex Tx ltac:(constructor; lia)) ltac:(apply lo64_range) eq_refl).
  destruct res as [[[h l] e]|v].
  - destruct SL as (Rh & Rl & Re). unfold fmodl_K1 in FM.
    unfold fmodl_fin in FM.
    destruct (Z.shiftr _ 63 =? 0).
    + destruct (Z.lor _ _ =? 0).
      * injection FM as <-. exists sz, 0, 0. split; [exact EZ|]. split; [constructor; lia|]. split; [intros E; lia| left; lia].
      * revert FM.
        match goal with |- fmodl_K2 ?sxx (?h2, ?l2, e) = Some r -> _ =>
          intros FM; unfold fmodl_K2 in FM;
          pose proof (fmodl_norm_loop_class 130 h2 l2 e) as NL;
          destruct (fmodl_norm_loop 130 (h2, l2, e)) as [[[h' l'] e']|]; [| discriminate FM] end.
        specialize (NL h' l' e' ltac:(destruct (l <? _); apply u64_range) (u64_range _) eq_refl). destruct NL as (Rh' & Rl' & Re').
        apply Some_inj1 in FM. subst r. rewrite fmodl_scale_pos by (try lia; change (Z.of_nat 130) with 130 in Re'; lia).
        pose proof (Z.mod_pos_bound h' (2^48) ltac:(lia)).
        eexists sx, e', _. split; [reflexivity|]. split; [constructor; lia|]. split; [intros E; exfalso; change (Z.of_nat 130) with 130 in Re'; lia|].
        right. change (Z.of_nat 130) with 130 in Re'. lia.
    + revert FM.
      match goal with |- fmodl_K2 ?sxx (?h2, ?l2, e) = Some r -> _ =>
        intros FM; unfold fmodl_K2 in FM;
        pose proof (fmodl_norm_loop_class 130 h2 l2 e) as NL;
        destruct (fmodl_norm_loop 130 (h2, l2, e)) as [[[h' l'] e']|]; [| discriminate FM] end.
      specialize (NL h' l' e' Rh Rl eq_refl). destruct NL as (Rh' & Rl' & Re').
      apply Some_inj1 in FM. subst r. rewrite fmodl_scale_pos by (try lia; change (Z.of_nat 130) with 130 in Re'; lia).
      pose proof (Z.mod_pos_bound h' (2^48) ltac:(lia)).
      eexists sx, e', _. split; [reflexivity|]. split; [constructor; lia|]. split; [intros E; exfalso; change (Z.of_nat 130) with 130 in Re'; lia|].
      right. change (Z.of_nat 130) with 130 in Re'. lia.
  - unfold fmodl_K1 in FM. injection FM as <-. rewrite SL. exists sz, 0, 0. split; [exact EZ|]. split; [constructor; lia|]. split; [intros E; lia| left; lia].
Qed.
End SF_ClassFmod.

(* [comment removed for export] *)
Module SF_ClassAlg.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Bool.Bool Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.FP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloatProps2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.SoftFloatProps3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_Class OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassMul OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassAdd SF_ClassMisc SF_ClassFmod OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv SF_ClassConv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition CLS (L H : Z) (x : Z) : Prop :=
  exists s E T, x = f128_pack s E T /\ packed s E T /\ ((E = 0 /\ T = 0) \/ (L <= E <= H)).

Lemma cls_weaken : forall L H L' H' x, CLS L H x -> L' <= L -> H <= H' -> CLS L' H' x.
Proof. intros L H L' H' x [s [E [T (-> & P & C)]]] HL HH. exists s, E, T. split; [reflexivity|]. split; [exact P| lia]. Qed.

Lemma cls_pack : forall L H s E T, packed s E T -> L <= E <= H -> CLS L H (f128_pack s E T).
Proof. intros. exists s, E, T. auto. Qed.

Lemma cls_zero : forall L H s, 0 <= s <= 1 -> CLS L H (f128_pack s 0 0).
Proof. intros. exists s, 0, 0. split; [reflexivity|]. split; [constructor; lia| left; lia]. Qed.

Lemma cls_nn : forall L H x, CLS L H x -> H <= 32766 -> NNres x.
Proof. intros L H x [s [E [T (-> & P & C)]]] HH. exists s, E, T. split; [reflexivity|]. split; [exact P|]. intros E32. lia. Qed.

Lemma cls_add : forall L1 H1 L2 H2 a b, CLS L1 H1 a -> CLS L2 H2 b ->
  117 <= Z.min L1 L2 -> Z.max H1 H2 <= 32766 ->
  CLS (Z.min L1 L2 - 115) (Z.max H1 H2 + 2) (f128_add a b).
Proof.
  intros L1 H1 L2 H2 a b [sa [Ea [Ta (-> & PA & CA)]]] [sb [Eb [Tb (-> & PB & CB)]]] HL HH.
  destruct (f128_add_class (Z.min L1 L2) (Z.max H1 H2) sa Ea Ta sb Eb Tb PA PB) as [s' [E' [T' (E1 & P1 & N1 & B1)]]]; try lia.
  exists s', E', T'. auto.
Qed.

Lemma cls_sub : forall L1 H1 L2 H2 a b, CLS L1 H1 a -> CLS L2 H2 b ->
  117 <= Z.min L1 L2 -> Z.max H1 H2 <= 32766 ->
  CLS (Z.min L1 L2 - 115) (Z.max H1 H2 + 2) (f128_sub a b).
Proof.
  intros L1 H1 L2 H2 a b [sa [Ea [Ta (-> & PA & CA)]]] [sb [Eb [Tb (-> & PB & CB)]]] HL HH.
  destruct (f128_sub_class (Z.min L1 L2) (Z.max H1 H2) sa Ea Ta sb Eb Tb PA PB) as [s' [E' [T' (E1 & P1 & N1 & B1)]]]; try lia.
  exists s', E', T'. auto.
Qed.

Lemma cls_mul : forall L1 H1 L2 H2 a b, CLS L1 H1 a -> CLS L2 H2 b ->
  1 <= L1 -> 1 <= L2 -> H1 <= 32766 -> H2 <= 32766 -> 16384 <= L1 + L2 -> H1 + H2 <= 49147 ->
  CLS (L1 + L2 - 16383) (H1 + H2 - 16381) (f128_mul a b).
Proof.
  intros L1 H1 L2 H2 a b [sa [Ea [Ta (-> & PA & CA)]]] [sb [Eb [Tb (-> & PB & CB)]]] HL1 HL2 HH1 HH2 HS1 HS2.
  pose proof PA as [? ? ?]. pose proof PB as [? ? ?].
  destruct CA as [[EA0 TA0]|CA].
  { exists (Z.lxor sb sa), 0, 0. rewrite (f128_mul_zero sa Ea Ta sb Eb Tb PA PB); try lia.
    split; [reflexivity|]. split; [constructor; pose proof (xorbit01 sa sb); lia| left; lia]. }
  destruct CB as [[EB0 TB0]|CB].
  { exists (Z.lxor sb sa), 0, 0. rewrite (f128_mul_zero sa Ea Ta sb Eb Tb PA PB); try lia.
    split; [reflexivity|]. split; [constructor; pose proof (xorbit01 sa sb); lia| left; lia]. }
  destruct (f128_mul_class sa Ea Ta sb Eb Tb PA PB) as [E' [T' (E1 & P1 & N1 & B1 & B2)]]; [intros E; lia| intros E; lia| intros; lia| intros; lia|].
  exists (Z.lxor sb sa), E', T'. split; [exact E1|]. split; [exact P1|]. right.
  specialize (B1 ltac:(lia) ltac:(lia)). specialize (B2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cls_div : forall L1 H1 L2 H2 a b, CLS L1 H1 a -> (exists E T, b = f128_pack 0 E T /\ packed 0 E T /\ L2 <= E <= H2) ->
  1 <= L1 -> 1 <= L2 -> H1 <= 32766 -> H2 <= 32766 -> -16000 <= L1 - H2 -> H1 - L2 <= 16000 ->
  CLS (16381 + L1 - H2) (16384 + H1 - L2) (f128_div a b).
Proof.
  intros L1 H1 L2 H2 a b [sa [Ea [Ta (-> & PA & CA)]]] [Eb [Tb (-> & PB & CB)]] HL1 HL2 HH1 HH2 HD1 HD2.
  destruct CA as [[EA0 TA0]|CA].
  - (* [comment removed for export] *)
    pose proof PA as [Hsa HEa HTa]. pose proof PB as [Hsb HEb HTb].
    pose proof (T_split Tb HTb) as (Hthb & Htlb & ETb).
    subst Ea Ta. exists (Z.lxor 0 sa), 0, 0.
    split.
    2:{ pose proof (xorbit01 sa 0 Hsa ltac:(lia)). split; [constructor; lia| left; lia]. }
    unfold f128_div. rewrite !f128_pack_hi, !f128_pack_lo by assumption.
    rewrite !hiword_exp by lia. rewrite Z.shiftr_lxor, !hiword_sign by lia.
    pose proof (xorbit01 sa 0 Hsa ltac:(lia)) as Hx0.
    rewrite (shl64_small (Z.lxor 0 sa) 63) by lia.
    rewrite !hiword_frac by lia.
    change EXPK with (2^64 - 32767). change EXPK2 with (2^64 - 32766).
    rewrite !add64_val. change ((0 + (2^64 - 32767)) mod 2^64 <? 2^64 - 32766) with true. cbn [orb negb].
    assert (NA : nn128 0 0) by (intros E; lia). assert (NB : nn128 Eb Tb) by (intros E; lia).
    rewrite (nan_test_false sa 0 0 PA NA), (nan_test_false 0 Eb Tb PB NB).
    rewrite (inf_test sa 0 0 PA NA), (inf_test' 0 Eb Tb PB NB).
    rewrite (zero_test sa 0 0 PA), (zero_test 0 Eb Tb PB).
    cbn [Z.eqb andb]. replace (Eb =? 32767) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (Eb =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb].
    rewrite zero_pack by lia. reflexivity.
  - destruct (f128_div_class sa Ea Ta 0 Eb Tb PA PB) as [E' [T' (E1 & P1 & N1 & B1)]]; try lia.
    exists (Z.lxor 0 sa), E', T'. split; [exact E1|]. split; [exact P1|]. right. lia.
Qed.

Lemma cls_fmodl : forall L1 H1 L2 H2 x y r, CLS L1 H1 x -> (exists s E T, y = f128_pack s E T /\ packed s E T /\ L2 <= E <= H2) ->
  130 <= Z.min L1 L2 -> Z.max H1 H2 <= 32766 ->
  m_fmodl x y = Some r -> CLS (Z.min L1 L2 - 129) (Z.max H1 H2) r.
Proof.
  intros L1 H1 L2 H2 x y r [sx [Ex [Tx (-> & PX & CX)]]] [sy [Ey [Ty (-> & PY & CY)]]] HL HH FM.
  destruct (m_fmodl_class (Z.min L1 L2) sx Ex Tx sy Ey Ty r PX PY ltac:(destruct CX; [left; lia| right; lia]) ltac:(lia) ltac:(lia) FM)
    as [s' [E' [T' (-> & P1 & N1 & B1)]]].
  exists s', E', T'. split; [reflexivity|]. split; [exact P1|]. destruct B1; [left; lia| right]. destruct CX; lia.
Qed.

Lemma cls_fabsl : forall L H x, CLS L H x -> CLS L H (m_fabsl x).
Proof. intros L H x [s [E [T (-> & P & C)]]]. rewrite m_fabsl_pack by assumption. exists 0, E, T. split; [reflexivity|]. destruct P; split; [constructor; lia| exact C]. Qed.

Lemma cls_copysignl : forall L H x y, CLS L H x -> NNres y -> CLS L H (m_copysignl x y).
Proof.
  intros L H x y [s [E [T (-> & P & C)]]] [s2 [E2 [T2 (-> & P2 & _)]]]. rewrite m_copysignl_pack by assumption.
  exists s2, E, T. split; [reflexivity|]. destruct P, P2; split; [constructor; lia| exact C].
Qed.

Lemma cls_scalbnl_nn : forall L H x n, CLS L H x -> H <= 32766 -> NNres (m_scalbnl x n).
Proof. intros L H x n [s [E [T (-> & P & C)]]] HH. apply m_scalbnl_class; [exact P|]. intros E32. lia. Qed.
End SF_ClassAlg.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Fpu Sem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import FP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat SoftFloatProps SoftFloatProps2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FmtFpDig.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FmtFpDig.SoftFloatProps3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import FmtFpDig FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan.DoubleOps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SF_ClassDiv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_Class.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SF_ClassDiv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassMul.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SF_ClassDiv.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SF_ClassDiv.SF_ClassAdd.
Import SF_ClassMisc.
Import SF_ClassFmod.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import SF_ClassDiv.
Import SF_ClassConv.
Import SF_ClassAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import FmtFp_facts3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require NumFacts.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Opaque f128_mul f128_add f128_sub f128_div f128_of_d f128_to_d f128_le f128_ge f128_of_u32 f128_of_i32 m_fmodl m_scalbnl m_scalbn m_copysignl m_fabsl.

(* [comment removed for export] *)
Lemma sext32_mod : forall u, sext32 u = sext32 (u mod 2^32).
Proof. intros. unfold sext32. rewrite <- !Z.land_ones by lia. change M32 with (Z.ones 32). rewrite <- Z.land_assoc, Z.land_diag. reflexivity. Qed.
Lemma f128_of_u32_mod : forall u, f128_of_u32 u = f128_of_u32 (u mod 2^32).
Proof. intros. Local Transparent f128_of_u32. unfold f128_of_u32. rewrite (sext32_mod u). reflexivity. Qed.
Lemma cls_of_u32 : forall u, CLS 16383 16414 (f128_of_u32 u).
Proof.
  intros u. rewrite f128_of_u32_mod. destruct (of_u32_class (u mod 2^32) ltac:(apply Z.mod_pos_bound; lia)) as [E [T (E1 & P1 & C1)]].
  rewrite E1. exists 0, E, T. auto.
Qed.

Lemma C_1E9_eq : C_1E9 = f128_pack 0 16412 T9. Proof. reflexivity. Qed.
Lemma cls_1e9 : CLS 16412 16412 C_1E9.
Proof. rewrite C_1E9_eq. apply cls_pack; [apply packed_const; try lia; pose proof T9_range; lia| lia]. Qed.

(* [comment removed for export] *)
Lemma df_asm_nn : forall fuel a s, (0 <= as_i s <= 4)%Z ->
  CLS (15900 - 100 * as_i s) (16420 + 40 * as_i s) (as_y s) ->
  forall s', df_asm_loop fuel a s = Some s' -> as_i s' = 4 /\ CLS 15500 16580 (as_y s').
Proof.
  induction fuel as [|fuel IH]; intros a s Hi Hy s' E; [discriminate E|].
  cbn [df_asm_loop] in E. unfold LD_B1B_DIG in E.
  destruct (Z.ltb_spec (as_i s) 4) as [LT|GE].
  - apply (IH a (df_asm_body a s)); [| | exact E].
    + unfold df_asm_body. destruct (_ =? _); cbn [as_i]; lia.
    + unfold df_asm_body. destruct (Z.land (a + as_i s) MASK =? as_z s); cbn [as_i as_y];
      (eapply cls_weaken;
        [ eapply cls_add; [eapply cls_mul; [apply cls_1e9| exact Hy| lia| lia| lia| lia| lia| lia] | apply cls_of_u32 | lia | lia]
        | lia | lia ]).
  - injection E as <-. split; [lia|]. eapply cls_weaken; [exact Hy| lia| lia].
Qed.

Lemma cls_f128_of_i32_0 : forall L H, CLS L H (f128_of_i32 0).
Proof. intros. rewrite f128_of_i32_0. apply cls_zero. lia. Qed.

Lemma df_final_nn : forall a z x e2 sign emax y, sign = 1 \/ sign = -1 ->
  df_final a z x e2 53 (-1074) sign emax (f128_of_i32 0) (f128_of_i32 0) = Some y -> NNres y.
Proof.
  intros a z x e2 sign emax y SGN DF.
  unfold df_final in DF.
  match type of DF with context [df_asm_loop 5 a ?s0] =>
    pose proof (df_asm_nn 5 a s0 ltac:(cbn; lia) ltac:(cbn [as_i as_y]; apply cls_f128_of_i32_0)) as AS;
    destruct (df_asm_loop 5 a s0) as [[i y1 z1 x1]|]; [| discriminate DF] end.
  specialize (AS _ eq_refl). cbn [as_i as_y] in AS. destruct AS as [-> Y1].
  cbv zeta in DF.
  rewrite (of_i32_sign sign SGN) in DF.
  (* [comment removed for export] *)
  assert (YS : CLS 15500 16582 (f128_mul y1 (f128_pack (sgn_bit sign) 16383 0))).
  { eapply cls_weaken; [eapply cls_mul; [exact Y1| apply (cls_pack 16383 16383); [apply packed_const; pose proof (sgn_bit_range sign); lia| lia] | lia| lia| lia| lia| lia| lia] | lia| lia]. }
  set (ysg := f128_mul y1 (f128_pack (sgn_bit sign) 16383 0)) in *.
  (* [comment removed for export] *)
  change LDBL_MANT_DIG_ with 113 in DF.
  set (bb := 113 + e2 - -1074) in DF.
  match type of DF with (let '(bits, _) := ?c in _) = _ =>
    assert (BITS : exists bits den, c = (bits, den) /\ 0 <= bits <= 53)
      by (destruct (bb <? 53) eqn:B1; [destruct (bb <? 0) eqn:B2|]; eexists _, _; (split; [reflexivity|]);
          first [lia | apply Z.ltb_lt in B1; apply Z.ltb_ge in B2; lia]);
    destruct BITS as [bits [den [EB Hbits]]]; rewrite EB in DF end.
  cbv beta iota in DF.
  replace (bits <? 113) with true in DF by (symmetry; apply Z.ltb_lt; lia). cbv iota in DF.
  rewrite !scalbn_one_ext in DF by lia.
  (* [comment removed for export] *)
  match type of DF with context [m_fmodl ysg ?t] =>
    destruct (m_fmodl ysg t) as [frac|] eqn:FR; [| discriminate DF] end.
  assert (FRC : CLS 15371 16582 frac).
  { eapply cls_weaken; [eapply (cls_fmodl 15500 16582 16443 16496); [exact YS| | lia| lia| exact FR] | lia| lia].
    eexists 0, _, 0. split; [reflexivity|]. split; [apply packed_const; lia| lia]. }
  clear FR.
  set (bias := m_copysignl (f128_pack 0 (16383 + (2 * 113 - bits - 1)) 0) ysg) in DF.
  assert (BI : CLS 16555 16608 bias).
  { apply cls_copysignl; [apply cls_pack; [apply packed_const; lia| lia] | eapply cls_nn; [exact YS| lia]]. }
  set (y2 := f128_add (f128_sub ysg frac) bias) in DF.
  assert (Y2 : CLS 15141 16610 y2).
  { eapply cls_weaken; [eapply cls_add; [eapply cls_sub; [exact YS| exact FRC| lia| lia] | exact BI| lia| lia] | lia| lia]. }
  cbv beta iota in DF.
  (* [comment removed for export] *)
  match type of DF with (match ?fx with Some frac0 => _ | None => None end) = Some y =>
    assert (FX : forall fr3, fx = Some fr3 -> CLS 15141 16586 fr3);
    [ intros fr3 EFX | destruct fx as [fr3|] eqn:EF3; [| discriminate DF]; specialize (FX fr3 eq_refl) ] end.
  { revert EFX.
    match goal with |- context [match ?od with Some d => f128_add frac (f128_of_d (bv_unsigned d)) | None => frac end] =>
      assert (OD : CLS 15256 16584 (match od with Some d => f128_add frac (f128_of_d (bv_unsigned d)) | None => frac end));
      [| set (frac2 := match od with Some d => _ | None => _ end) in *; clearbody frac2 ] end.
    { assert (E25 := quarter_ext sign SGN). assert (E5 := half_sign_ext sign SGN). assert (E75 := threeq_ext sign SGN).
      pose proof (sgn_bit_range sign) as SB.
      repeat match goal with |- context [if ?c then _ else _] => destruct c end;
        try (rewrite E25 || rewrite E5 || rewrite E75);
        first [ eapply cls_weaken; [eapply cls_add; [exact FRC| apply (cls_pack 16381 16382); [apply packed_const; lia| lia] | lia| lia] | lia| lia]
              | eapply cls_weaken; [exact FRC| lia| lia] ]. }
    destruct (negb (Z.land (a + 4) MASK =? z1)).
    - destruct (2 <=? 113 - bits).
      + destruct (m_fmodl frac2 (f128_of_i32 1)) as [rr|]; [| discriminate].
        destruct (f128_le rr 0 =? 0); intros E; injection E as <-.
        * rewrite C_ONE_eq. eapply cls_weaken; [eapply cls_add; [exact OD| apply (cls_pack 16383 16383); [apply packed_const; lia| lia] | lia| lia] | lia| lia].
        * eapply cls_weaken; [exact OD| lia| lia].
      + intros E; injection E as <-. eapply cls_weaken; [exact OD| lia| lia].
    - intros E; injection E as <-. eapply cls_weaken; [exact FRC| lia| lia]. }
  set (y4 := f128_sub (f128_add y2 fr3) bias) in DF.
  assert (Y4 : CLS 14911 16614 y4).
  { eapply cls_weaken; [eapply cls_sub; [eapply cls_add; [exact Y2| exact FX| lia| lia] | exact BI| lia| lia] | lia| lia]. }
  rewrite half_ext_eq in DF.
  assert (Y5 : CLS 14910 16615 (f128_mul y4 (f128_pack 0 16382 0))).
  { eapply cls_weaken; [eapply cls_mul; [exact Y4| apply (cls_pack 16382 16382); [apply packed_const; lia| lia] | lia| lia| lia| lia| lia| lia] | lia| lia]. }
  match type of DF with (let '(_, _) := ?p in _) = _ =>
    assert (FIN : exists yf ef, p = (yf, ef) /\ CLS 14910 16615 yf)
      by (repeat match goal with |- context [if ?c then _ else _] => destruct c end; eexists _, _; (split; [reflexivity|]);
          first [exact Y5 | eapply cls_weaken; [exact Y4| lia| lia]]);
    destruct FIN as [yf [ef [EF CY]]]; rewrite EF in DF end.
  cbv beta iota in DF. apply Some_inj1 in DF. subst y. eapply cls_scalbnl_nn; [exact CY| lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma df_p4_nn : forall f a z e2 rp x sign emax r, sign = 1 \/ sign = -1 ->
  df_p4 f a z e2 rp x 53 (-1074) sign emax (f128_of_i32 0) (f128_of_i32 0) = Some r -> NNres (snd r).
Proof.
  intros f a z e2 rp x sign emax r SGN E. unfold df_p4 in E.
  destruct (df_tz_loop FUEL_RING x z) as [z1|]; [| discriminate E].
  match type of E with (match ?al with Some _ => _ | None => None end) = _ =>
    destruct al as [[[[a2 z2] rp2] x2]|]; [| discriminate E] end.
  destruct (df_up_loop FUEL_SCALE (mkUS rp2 a2 z2 e2 x2)) as [[rp3 a3 z3 e3 x3]|]; [| discriminate E].
  destruct (df_dn_loop FUEL_SCALE (mkDS rp3 a3 z3 e3 x3 0)) as [[rp4 a4 z4 e4 x4 i4]|]; [| discriminate E].
  match type of E with (match ?fin with Some _ => _ | None => None end) = _ =>
    destruct fin as [y|] eqn:DF; [| discriminate E] end.
  injection E as <-. cbn [snd]. eapply df_final_nn; [exact SGN| exact DF].
Qed.

Lemma sf_xf_normal : forall sign x0, sign = 1 \/ sign = -1 -> 10^8 <= x0 < 10^9 ->
  exists E' T', f128_mul (f128_of_i32 sign) (f128_of_u32 x0) = f128_pack (sgn_bit sign) E' T'
    /\ packed (sgn_bit sign) E' T' /\ 16409 <= E' <= 16414.
Proof.
  intros sign x0 SGN Hx0. rewrite (of_i32_sign sign SGN).
  set (L := Z.log2 x0).
  assert (HL : 2^L <= x0 < 2^(L+1)). { subst L. destruct (Z.log2_spec x0 ltac:(lia)). rewrite Z.add_1_r. lia. }
  assert (HL26 : 26 <= L <= 29).
  { subst L. split.
    - replace 26 with (Z.log2 (2^26)) by reflexivity. apply Z.log2_le_mono. change (2^26) with 67108864. lia.
    - apply Z.lt_succ_r. apply Z.log2_lt_pow2; [lia|]. change (2 ^ Z.succ 29) with 1073741824. lia. }
  clearbody L.
  rewrite (f128_of_u32_val x0 L) by lia.
  assert (LO : 2^112 <= x0 * 2^(112 - L)).
  { replace (2^112) with (2^L * 2^(112-L)) by (rewrite <- Z.pow_add_r by lia; f_equal; lia). apply Z.mul_le_mono_nonneg_r; lia. }
  assert (HI : x0 * 2^(112 - L) < 2^113).
  { apply (Z.lt_le_trans _ (2^(L+1) * 2^(112-L))); [apply Z.mul_lt_mono_pos_r; lia|].
    rewrite <- Z.pow_add_r by lia. apply Z.eq_le_incl. f_equal. lia. }
  pose proof (sgn_bit_range sign) as SB.
  destruct (f128_mul_class (sgn_bit sign) 16383 0 0 (16383 + L) (x0 * 2 ^ (112 - L) - 2 ^ 112)
              ltac:(constructor; lia) ltac:(constructor; lia) ltac:(intros E; lia) ltac:(intros E; lia) ltac:(intros; lia) ltac:(intros; lia))
    as [E' [T' (E1 & P1 & N1 & B1 & B2)]].
  rewrite Z.lxor_0_l in E1, P1.
  exists E', T'. split; [exact E1|]. split; [exact P1|].
  specialize (B1 ltac:(lia) ltac:(lia)). specialize (B2 ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma div_by_zero_inf : forall sa Ea Ta, packed sa Ea Ta -> 1 <= Ea <= 32766 ->
  f128_div (f128_pack sa Ea Ta) (f128_pack 0 0 0) = f128_pack (Z.lxor 0 sa) 32767 0.
Proof.
  intros sa Ea Ta PA HEa. pose proof PA as [Hsa HEa' HTa]. pose proof (T_split Ta HTa) as (Htha & Htla & ETa).
  assert (PB : packed 0 0 0) by (constructor; lia).
  Local Transparent f128_div.
  unfold f128_div. rewrite !f128_pack_hi, !f128_pack_lo by assumption.
  rewrite !hiword_exp by lia. rewrite Z.shiftr_lxor, !hiword_sign by lia.
  pose proof (xorbit01 sa 0 Hsa ltac:(lia)) as Hx.
  rewrite (shl64_small (Z.lxor 0 sa) 63) by lia.
  rewrite !hiword_frac by lia.
  change EXPK with (2^64 - 32767). change EXPK2 with (2^64 - 32766).
  rewrite !add64_val. rewrite (Z.mod_small (Ea + _)) by lia.
  replace (Ea + (2 ^ 64 - 32767) <? 2 ^ 64 - 32766) with false by (symmetry; apply Z.ltb_ge; lia).
  change ((0 + (2 ^ 64 - 32767)) mod 2 ^ 64 <=? 2 ^ 64 - 32767) with true. cbn [orb negb].
  assert (NA : nn128 Ea Ta) by (intros E; lia). assert (NB : nn128 0 0) by (intros E; lia).
  rewrite (nan_test_false sa Ea Ta PA NA), (nan_test_false 0 0 0 PB NB).
  rewrite (inf_test sa Ea Ta PA NA), (inf_test' 0 0 0 PB NB).
  rewrite (zero_test sa Ea Ta PA), (zero_test 0 0 0 PB).
  replace (Ea =? 32767) with false by (symmetry; apply Z.eqb_neq; lia).
  replace (Ea =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [Z.eqb andb negb].
  apply inf_pack. lia.
Qed.

Lemma df_p3_nn : forall f k lrp lnz x sign emax r, sign = 1 \/ sign = -1 -> 10^8 <= znth x 0 < 10^9 ->
  df_p3 f k lrp lnz x 53 (-1074) sign emax (f128_of_i32 0) (f128_of_i32 0) = Some r -> NNres (snd r).
Proof.
  intros f k lrp lnz x sign emax r SGN X0 E. unfold df_p3 in E. cbv zeta in E.
  pose proof (sgn_bit_range sign) as SB.
  destruct (sf_xf_normal sign (znth x 0) SGN X0) as [Et [Tt (ET & PT & BT)]].
  destruct ((lnz <? 9) && (lnz <=? s32 lrp) && (s32 lrp <? 18)).
  - destruct (Z.eqb_spec (s32 lrp) 9).
    { injection E as <-. cbn [snd]. rewrite ET. apply NNres_pack; [exact PT| intros E32; lia]. }
    destruct (Z.ltb_spec (s32 lrp) 9).
    { injection E as <-. cbn [snd]. rewrite ET.
      destruct (Z.le_gt_cases 1 (s32 lrp)) as [R1|R0].
      - destruct (of_i32_p10_class (8 - s32 lrp) ltac:(lia)) as [Ep [Tp (EP & PP & BP)]]. rewrite EP.
        destruct (f128_div_class (sgn_bit sign) Et Tt 0 Ep Tp PT PP) as [E' [T' (E1 & P1 & N1 & B1)]]; try lia.
        rewrite E1. apply NNres_pack; assumption.
      - rewrite (znth_ge p10s (8 - s32 lrp)) by (change (zlength p10s) with 8; lia). rewrite f128_of_i32_0.
        rewrite (div_by_zero_inf _ Et Tt PT) by lia. rewrite Z.lxor_0_l. apply NNres_pack; [constructor; lia| intros _; reflexivity]. }
    destruct ((30 <? 53 - 3 * (s32 lrp - 9)) || (Z.shiftr (znth x 0) (53 - 3 * (s32 lrp - 9)) =? 0)).
    { injection E as <-. cbn [snd]. rewrite ET.
      destruct (Z.le_gt_cases (s32 lrp - 10) 7) as [R1|R0].
      - destruct (of_i32_p10_class (s32 lrp - 10) ltac:(lia)) as [Ep [Tp (EP & PP & BP)]]. rewrite EP.
        destruct (f128_mul_class (sgn_bit sign) Et Tt 0 Ep Tp PT PP ltac:(intros E32; lia) ltac:(intros E32; lia) ltac:(intros; lia) ltac:(intros; lia))
          as [E' [T' (E1 & P1 & N1 & _)]].
        rewrite E1. apply NNres_pack; assumption.
      - rewrite (znth_ge p10s (s32 lrp - 10)) by (change (zlength p10s) with 8; lia). rewrite f128_of_i32_0.
        rewrite (f128_mul_zero (sgn_bit sign) Et Tt 0 0 0 PT ltac:(constructor; lia)) by lia.
        rewrite Z.lxor_0_l. apply NNres_pack; [constructor; lia| intros E32; lia]. }
    eapply df_p4_nn; [exact SGN| exact E].
  - eapply df_p4_nn; [exact SGN| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma df_p2_nn : forall f lrp j k dc lnz x sign emax r, sign = 1 \/ sign = -1 -> P2pre j k x ->
  df_p2 f lrp j k dc lnz x 53 (-1074) sign emax (f128_of_i32 0) (f128_of_i32 0) = Some r -> NNres (snd r).
Proof.
  intros f lrp j k dc lnz x sign emax r SGN (Hj & Hk & LX & WX & DS) E.
  pose proof (sgn_bit_range sign) as SB.
  unfold df_p2 in E.
  destruct (Z.eqb_spec (znth x 0) 0) as [X0|X0].
  { injection E as <-. cbn [snd]. rewrite (sign_zero_ext sign SGN). apply NNres_pack; [constructor; lia| intros E32; lia]. }
  destruct (_ && _ && _).
  { injection E as <-. cbn [snd]. rewrite (of_i32_sign sign SGN).
    pose proof (cls_of_u32 (znth x 0)) as XF.
    eapply (cls_nn _ _); [eapply cls_mul; [apply (cls_pack 16383 16383); [apply packed_const; lia| lia] | exact XF | lia| lia| lia| lia| lia| lia] | lia]. }
  change (Z.quot (- -1074) 2) with 537 in E. change (-1074 - 2 * LDBL_MANT_DIG_) with (-1300) in E.
  rewrite (of_i32_sign sign SGN), C_LDBL_MAX_eq, C_LDBL_MIN_eq in E.
  destruct (Z.ltb_spec 537 lrp).
  { injection E as <-. cbn [snd].
    destruct (f128_mul_class (sgn_bit sign) 16383 0 0 32766 (2^112 - 1) ltac:(constructor; lia) ltac:(constructor; lia)
                ltac:(intros E32; lia) ltac:(intros E32; lia) ltac:(intros; lia) ltac:(intros; lia)) as [E1 [T1 (EQ1 & P1 & N1 & _ & L1)]].
    rewrite EQ1. specialize (L1 ltac:(lia) ltac:(lia) ltac:(lia)).
    destruct (f128_mul_class (Z.lxor 0 (sgn_bit sign)) E1 T1 0 32766 (2^112 - 1) P1 ltac:(constructor; lia) N1 ltac:(intros E32; lia)
                ltac:(intros _ [? ?]; lia) ltac:(intros; lia)) as [E2 [T2 (EQ2 & P2 & N2 & _)]].
    rewrite EQ2. apply NNres_pack; assumption. }
  destruct (Z.ltb_spec lrp (-1300)).
  { injection E as <-. cbn [snd].
    destruct (f128_mul_class (sgn_bit sign) 16383 0 0 1 0 ltac:(constructor; lia) ltac:(constructor; lia)
                ltac:(intros E32; lia) ltac:(intros E32; lia) ltac:(intros; lia) ltac:(intros; lia)) as [E1 [T1 (EQ1 & P1 & N1 & B1 & _)]].
    rewrite EQ1. specialize (B1 ltac:(lia) ltac:(lia)).
    destruct (f128_mul_class (Z.lxor 0 (sgn_bit sign)) E1 T1 0 1 0 P1 ltac:(constructor; lia) N1 ltac:(intros E32; lia)
                ltac:(intros E32; exfalso; lia) ltac:(intros ? [? ?]; lia)) as [E2 [T2 (EQ2 & P2 & N2 & _)]].
    rewrite EQ2. apply NNres_pack; assumption. }
  destruct DS as [D1 D2].
  destruct (nz j) eqn:NJ.
  - assert (J1 : 1 <= j). { unfold nz in NJ. destruct (Z.eqb_spec j 0); [discriminate NJ| lia]. }
    destruct (df_pad_total k j x ltac:(unfold KMAX in *; lia)) as [j' [x' (EP & (Hj' & L' & W' & A' & B') & J9)]].
    { unfold PADI. split; [lia|]. split; [exact LX|]. split; [exact WX|]. split.
      - intros K0. apply (proj2 (D1 K0)). lia.
      - intros; reflexivity. }
    rewrite EP in E. eapply df_p3_nn; [exact SGN| | exact E].
    subst j'. destruct (Z.eq_dec k 0) as [K0|K0].
    + specialize (A' K0). replace (9 - 1) with 8 in A' by lia. exact A'.
    + rewrite B' by lia. apply D2. lia.
  - assert (J0 : j = 0). { unfold nz in NJ. destruct (Z.eqb_spec j 0); [lia| discriminate NJ]. }
    assert (K1 : 1 <= k). { destruct (Z.eq_dec k 0) as [K0|]; [|lia]. exfalso. apply X0. apply (proj1 (D1 K0)). exact J0. }
    eapply df_p3_nn; [exact SGN| apply D2; lia| exact E].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma decfloat_total_nn : df_p2_total_stmt ->
  forall fuelc f c sign pok, sign = 1 \/ sign = -1 ->
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) -> 0 <= sh_rpos f ->
  zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f) ->
  exists f' y, decfloat fuelc f c 53 (-1074) sign pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f') /\ NNres y.
Proof.
  intros HP2 fuelc f c sign pok SGN W HB BC CI R0 FU NS.
  assert (NZ0 : NNres (f128_of_i32 0)) by (rewrite f128_of_i32_0; apply NNres_pack; [constructor; lia| intros E; lia]).
  pose proof (sh_N_le f W) as NL.
  rewrite decfloat_eq. cbv zeta.
  assert (HI0 : LZI f c f). { unfold LZI. split; [exact W|]. split; [apply sh_same_refl|]. split; [lia|]. split; [exact CI| exact BC]. }
  assert (LNN : 0 <= zlength (sh_buf f)) by (unfold zlength; lia).
  assert (M0 : cm c f < Z.of_nat fuelc). { unfold cm. destruct (contb c); lia. }
  destruct (df_lz_total fuelc f 0 c f HB HI0 M0) as [g1 [c1 [f1 (E1 & HI1 & N48 & M1)]]]. rewrite E1.
  (* [comment removed for export] *)
  match goal with |- context [match ?e with Some _ => _ | None => None end] =>
    assert (HR : exists g2 gr lrp c2 f2, e = Some (g2, gr, lrp, c2, f2) /\ LZI f c2 f2 /\ c2 <> 48 /\ (gr = 0 -> c2 <> 46) /\ (gr = 0 \/ gr = 1) /\ cm c2 f2 <= cm c f)
  end.
  { destruct (Z.eqb_spec c1 46) as [E46|N46].
    - destruct (sh_getc f1) as [c1' f1'] eqn:G.
      assert (CC : contc c1) by (subst; unfold contc; lia).
      destruct (LZI_read f c1 f1 c1' f1' HB HI1 CC G) as [HI1' M1'].
      destruct (df_rz_total fuelc f g1 0 c1' f1' HB HI1' ltac:(lia)) as [g2 [l2 [c2 [f2 (E2 & HI2 & N48' & M2)]]]].
      rewrite E2. eexists _, _, _, _, _. split; [reflexivity|]. split; [exact HI2|]. split; [exact N48'|]. split; [intros; lia|]. split; [lia|lia].
    - eexists _, _, _, _, _. split; [reflexivity|]. split; [exact HI1|]. split; [exact N48|]. split; [intros _; exact N46|]. split; [lia|lia]. }
  destruct HR as [g2 [gr [lrp [c2 [f2 (-> & HI2 & N48' & N46 & GR & M2)]]]]].
  destruct HI2 as (W2 & SM2 & R2 & CI2 & BC2).
  (* [comment removed for export] *)
  set (x0 := zupd (zrepeat 0 KMAX) 0 0).
  assert (DI0 : DI f (mkDL f2 c2 0 0 lrp 0 0 g2 gr x0)).
  { apply DI_intro; try assumption; try lia.
    - unfold KMAX; lia.
    - subst x0. rewrite zlength_zupd. apply zlength_zrepeat. unfold KMAX; lia.
    - subst x0. apply W32_zupd; [apply W32_zrepeat| lia].
    - unfold DSH. subst x0. rewrite znth_zupd_eq by (rewrite zlength_zrepeat; unfold KMAX; lia). split; [|intros; lia]. intros _. split; [reflexivity| intros; lia].
    - intros _. split; [exact N48'|]. intros GZ. apply N46. unfold nz in GZ. destruct (Z.eqb_spec gr 0); [assumption| discriminate GZ]. }
  destruct (df_dig_total fuelc f _ HB DI0 BC2 ltac:(cbn [dl_c dl_f]; lia)) as [s3 (E3 & HI3 & BC3 & X3)].
  rewrite E3. destruct s3 as [f3 c3 j3 k3 lrp3 dc3 lnz3 gd3 gr3 x3]. cbn [dl_c dl_f] in *.
  destruct HI3 as (W3 & SM3 & R3 & CI3 & Hj3 & Hk3 & LX3 & WX3 & DS3 & _). cbn [dl_f dl_c dl_j dl_k dl_x dl_gotrad] in *.
  assert (P2 : P2pre j3 k3 x3) by (unfold P2pre; tauto).
  destruct SM3 as (B3 & S3 & C03 & N3 & n3).
  assert (CLOSE : forall f' lrp',
    sh_wf f' -> sh_buf f' = sh_buf f -> sh_stdio f' = sh_stdio f -> (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f') ->
    exists f'' y, (if negb (nz gd3) then Some (sh_lim0 f', f128_of_i32 0)
                   else df_p2 f' lrp' j3 k3 dc3 lnz3 x3 53 (-1074) sign (- -1074 - 53 + 3) (f128_of_i32 0) (f128_of_i32 0)) = Some (f'', y)
      /\ sh_wf f'' /\ sh_buf f'' = sh_buf f /\ sh_stdio f'' = sh_stdio f /\ (sh_stdio f = false -> sh_cnt0 f'' <= sh_rpos f'') /\ NNres y).
  { intros f' lrp' W' B' S' NS'. destruct (negb (nz gd3)).
    - eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. split; [assumption|]. split; [assumption|]. split; [intros; lia| exact NZ0].
    - destruct (HP2 f' lrp' j3 k3 dc3 lnz3 x3 sign (- -1074 - 53 + 3) (f128_of_i32 0) (f128_of_i32 0) P2) as [y Ey].
      pose proof (df_p2_nn _ _ _ _ _ _ _ _ _ _ SGN P2 Ey) as NY. cbn [snd] in NY.
      rewrite Ey. eexists _, _. split; [reflexivity|]. auto. }
  (* [comment removed for export] *)
  destruct (nz gd3 && (Z.lor c3 32 =? 101)) eqn:EX.
  - apply andb_prop in EX. destruct EX as [_ EX]. pose proof (lor32_101_cont c3 EX) as CC3. specialize (CI3 CC3).
    destruct (scanexp_total fuelc f3 pok W3 ltac:(lia) ltac:(rewrite B3; lia)) as [f4 [e10 (E4 & W4 & SM4 & R4)]].
    rewrite E4. destruct SM4 as (B4 & S4 & C04 & N4 & n4).
    destruct (e10 =? LLONG_MIN_).
    + destruct (nz pok).
      * destruct (sh_unget_facts f4 W4) as (W5 & SM5 & R5). destruct SM5 as (B5 & S5 & C05 & N5 & n5).
        apply CLOSE; [exact W5| congruence| congruence|]. intros ST. rewrite C05, C04, C03. specialize (R4 ltac:(congruence)). specialize (NS ST). lia.
      * eexists _, _. split; [reflexivity|]. split; [now apply sh_lim0_wf|]. unfold sh_lim0; cbn. split; [congruence|]. split; [congruence|]. split; [intros; lia| exact NZ0].
    + apply CLOSE; [exact W4| congruence| congruence|]. intros ST. rewrite C04, C03. specialize (R4 ltac:(congruence)). specialize (NS ST). lia.
  - destruct (0 <=? c3).
    + destruct (sh_unget_facts f3 W3) as (W5 & SM5 & R5). destruct SM5 as (B5 & S5 & C05 & N5 & n5).
      apply CLOSE; [exact W5| congruence| congruence|]. intros ST. rewrite C05, C03. specialize (NS ST). lia.
    + apply CLOSE; [exact W3| congruence| congruence|]. intros ST. rewrite C03. specialize (NS ST). lia.
Qed.

Theorem decfloat_total_all_nn : forall fuelc f c sign pok, sign = 1 \/ sign = -1 ->
  sh_wf f -> BB f -> bchar c -> (contc c -> sh_rpos f <= sh_N f) -> 0 <= sh_rpos f ->
  zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f) ->
  exists f' y, decfloat fuelc f c 53 (-1074) sign pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f') /\ NNres y.
Proof. apply decfloat_total_nn. apply df_p2_total. apply df_p3_total. apply df_p4_total. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NNB (f : shfile) : Prop := forall i, znth (sh_buf f) i <> 110 /\ znth (sh_buf f) i <> 78.

Lemma NNB_of : forall f l, sh_buf f = l ++ [0] -> Forall (fun c => c <> 110 /\ c <> 78) l -> NNB f.
Proof.
  intros f l E F i. rewrite E. destruct (read_char_cases l i) as [->|I]; [lia|].
  rewrite Forall_forall in F. apply F. exact I.
Qed.

Definition not_n_ok (c : Z) : bool := (c =? 78) || (c =? 110) || negb (Z.lor c 32 =? 110).
Lemma not_n_table : forallb not_n_ok (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma nan_test_false_char : forall c, bchar c -> c <> 110 -> c <> 78 -> (Z.lor c 32 =? 110) = false.
Proof.
  intros c Hc N1 N2. destruct (Z.eq_dec c (-1)) as [->|NM]; [reflexivity|].
  pose proof not_n_table as T. rewrite forallb_forall in T.
  specialize (T c ltac:(apply in_map_iff; exists (Z.to_nat c); split; [unfold bchar in Hc; lia| apply in_seq; unfold bchar in Hc; lia])).
  unfold not_n_ok in T.
  replace (c =? 78) with false in T by (symmetry; apply Z.eqb_neq; lia).
  replace (c =? 110) with false in T by (symmetry; apply Z.eqb_neq; lia).
  cbn [orb] in T. destruct (Z.lor c 32 =? 110); [discriminate T| reflexivity].
Qed.

Lemma fs_ws_loop_char : forall fuel f c f', fs_ws_loop fuel f = Some (c, f') ->
  (c = -1 \/ exists i, c = znth (sh_buf f) i) /\ sh_buf f' = sh_buf f.
Proof.
  induction fuel as [|fuel IH]; intros f c f' E; [discriminate E|].
  cbn [fs_ws_loop] in E. destruct (sh_getc f) as [c0 f0] eqn:G.
  pose proof (sh_getc_char f) as CH. rewrite G in CH. cbn [fst snd] in CH.
  pose proof (sh_getc_buf f) as HB. rewrite G in HB. cbn [snd] in HB.
  destruct (m_isspace c0).
  - destruct (IH f0 c f' E) as [HC HB']. rewrite HB in HC, HB'. split; [exact HC| exact HB'].
  - injection E as <- <-. split; [| exact HB]. destruct CH as [(-> & _)|(-> & _)]; [left; reflexivity| right; eexists; reflexivity].
Qed.

Lemma fs_nan_loop_stop0 : forall c g, (Z.lor c 32 =? 110) = false -> fs_nan_loop 4 (0, c, g) = Some (0, c, g).
Proof. intros c g H. cbn [fs_nan_loop]. unfold fs_nan_cond. change (znth str_nan 0) with 110. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma floatscan_total_nn : forall fuelc f pok,
  sh_wf f -> BB f -> NX f -> NNB f -> 0 <= sh_rpos f -> zlength (sh_buf f) + 2 <= Z.of_nat fuelc ->
  (sh_stdio f = false -> sh_cnt0 f <= sh_rpos f) ->
  exists f' y, floatscan fuelc f 1 pok = Some (f', y)
    /\ sh_wf f' /\ sh_buf f' = sh_buf f /\ sh_stdio f' = sh_stdio f
    /\ (sh_stdio f = false -> sh_cnt0 f' <= sh_rpos f') /\ NNres y.
Proof.
  intros fuelc f pok W HB HN HNN R FU NS.
  assert (NZ0 : NNres (f128_of_i32 0)) by (rewrite f128_of_i32_0; apply NNres_pack; [constructor; lia| intros E; lia]).
  pose proof (sh_N_le f W) as NL.
  unfold floatscan. change (1 =? 0) with false. change (1 =? 1) with true. cbn iota. change (-1021 - 53) with (-1074).
  destruct (fs_ws_total fuelc f W HB R FU) as [c1 [f1 (E1 & W1 & S1 & B1 & SP1 & R1 & CI1 & NS1 & CR1 & _)]].
  destruct (fs_ws_loop_char _ _ _ _ E1) as [HC1 _]. rewrite E1.
  destruct S1 as (Bf1 & St1 & C01 & N1 & n1).
  assert (NOTN : forall c, bchar c -> (c = -1 \/ exists i, c = znth (sh_buf f) i) -> (Z.lor c 32 =? 110) = false).
  { intros c Hc [->|[i ->]]; [reflexivity|]. destruct (HNN i) as [A1 A2]. apply nan_test_false_char; [exact Hc| exact A1| exact A2]. }
  assert (BB1 : BB f1) by (intros i; rewrite Bf1; apply HB).
  assert (NX1 : NX f1) by (intros i; rewrite Bf1; apply HN).
  (* [comment removed for export] *)
  set (sg := if (c1 =? 43) || (c1 =? 45) then _ else _).
  assert (SG : exists sign c2 f2, sg = (sign, c2, f2) /\ sh_wf f2 /\ sh_same f f2 /\ bchar c2 /\ (contc c2 -> sh_rpos f2 <= sh_N f2)
            /\ 0 <= sh_rpos f2 /\ (sh_stdio f = false -> sh_cnt0 f + 1 <= sh_rpos f2) /\ (contc c2 -> 1 <= sh_rpos f2)
            /\ (sign = 1 \/ sign = -1) /\ (Z.lor c2 32 =? 110) = false).
  { subst sg. destruct ((c1 =? 43) || (c1 =? 45)) eqn:SGN.
    - assert (CC1 : contc c1). { unfold contc. destruct (Z.eqb_spec c1 43); [subst; lia|]. destruct (Z.eqb_spec c1 45); [subst; lia| discriminate SGN]. }
      specialize (CI1 CC1). cbv zeta.
      destruct (sh_getc f1) as [c2 f2] eqn:G2.
      destruct (sh_getc_facts f1 c2 f2 G2 W1) as (W2 & B2 & S2 & C02 & N2 & n2 & RP2 & CT2 & SH2).
      eexists _, _, _. split; [reflexivity|]. split; [exact W2|]. split.
      { eapply sh_same_trans; [| eapply sh_same_getc; eauto]. unfold sh_same; auto. }
      split; [eapply getc_bchar; eauto|]. split; [intros CC; destruct (CT2 CC); rewrite N2; lia|]. split; [lia|].
      split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } split. { intros CC. destruct (CT2 CC). lia. }
      split. { destruct (c1 =? 45); cbn; lia. }
      apply NOTN; [eapply getc_bchar; eauto|]. destruct SH2 as [(-> & _)|(-> & _)]; [left; reflexivity| right]. rewrite Bf1. eexists; reflexivity.
    - eexists _, _, _. split; [reflexivity|]. split; [exact W1|]. split; [unfold sh_same; auto|]. split; [exact B1|]. split; [exact CI1|]. split; [lia|].
      split. { intros ST. specialize (NS ST). specialize (NS1 ST). lia. } split. { intros CC. specialize (CR1 CC). lia. }
      split; [lia|]. apply NOTN; [exact B1| exact HC1]. }
  destruct SG as [sign [c2 [f2 (-> & W2 & S2 & B2 & CI2 & R2 & NS2 & CR2 & SGN & NC2)]]].
  destruct S2 as (Bf2 & St2 & C02 & N2 & n2).
  assert (BB2 : BB f2) by (intros i; rewrite Bf2; apply HB).
  assert (NX2 : NX f2) by (intros i; rewrite Bf2; apply HN).
  pose proof (sh_N_le f2 W2) as NL2.
  (* [comment removed for export] *)
  destruct (fs_inf_total f2 c2 W2 BB2 B2 CI2) as [[[i3 c3] f3] (E3 & (Hi3 & W3 & S3 & B3 & CI3 & R3 & NS3) & C3)]. rewrite E3.
  destruct S3 as (Bf3 & St3 & C03 & N3 & n3).
  assert (UNG : forall g n, sh_wf g -> sh_stdio g = sh_stdio f -> (sh_stdio f = false -> sh_rpos (fs_unget_loop n g) = sh_rpos g - Z.of_nat n)).
  { intros g n Wg Sg ST. destruct (fs_unget_loop_facts n g) as (_ & _ & _ & _ & _ & _ & _ & E). apply E.
    unfold sh_wf in Wg. rewrite Sg, ST in Wg. tauto. }
  destruct ((i3 =? 3) || (i3 =? 8) || ((3 <? i3) && nz pok)) eqn:INF.
  { (* [comment removed for export] *)
    match goal with |- exists f' y, Some (?g, _) = Some (f', y) /\ _ => set (g' := g) end.
    assert (HG : sh_wf g' /\ sh_buf g' = sh_buf f /\ sh_stdio g' = sh_stdio f /\ (sh_stdio f = false -> sh_cnt0 g' <= sh_rpos g')).
    { subst g'. destruct (negb (i3 =? 8)) eqn:N8.
      - destruct (sh_unget_facts f3 W3) as (W4 & S4 & R4). destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
        assert (U4 : sh_stdio f = false -> sh_rpos (sh_unget f3) = sh_rpos f3 - 1).
        { intros ST. apply sh_unget_rpos_nonstdio. unfold sh_wf in W3. rewrite St3, St2, ST in W3. tauto. }
        destruct (nz pok).
        + destruct (fs_unget_loop_facts (Z.to_nat (i3 - 3)) (sh_unget f3)) as (N5 & C05 & St5 & Bf5 & G5 & n5 & R5 & E5).
          split; [apply fs_unget_loop_wf; exact W4|]. split; [congruence|]. split; [congruence|].
          intros ST. rewrite C05, C04, C03. rewrite (UNG (sh_unget f3) _ W4 ltac:(congruence) ST), (U4 ST), (NS3 ltac:(congruence)).
          rewrite Z2Nat.id by lia. specialize (NS2 ST).
          assert (i3 <> 8). { intros ->. discriminate N8. } lia.
        + split; [exact W4|]. split; [congruence|]. split; [congruence|].
          intros ST. rewrite C04, C03, (U4 ST), (NS3 ltac:(congruence)). specialize (NS2 ST). lia.
      - split; [exact W3|]. split; [congruence|]. split; [congruence|]. intros ST. rewrite C03, (NS3 ltac:(congruence)). specialize (NS2 ST). lia. }
    destruct HG as (HG1 & HG2 & HG3 & HG4). eexists _, _. split; [reflexivity|].
    split; [exact HG1|]. split; [exact HG2|]. split; [exact HG3|]. split; [exact HG4|].
    destruct (0 <? sign); [rewrite C_INF_eq| rewrite C_NINF_eq]; apply NNres_pack; (constructor; lia) || (intros _; reflexivity). }
  (* [comment removed for export] *)
  set (nn := if i3 =? 0 then fs_nan_loop 4 (0, c3, f3) else Some (i3, c3, f3)).
  assert (NN : exists i4 c4 f4, nn = Some (i4, c4, f4) /\ 0 <= i4 <= 8 /\ sh_wf f4 /\ sh_same f2 f4 /\ bchar c4 /\ (contc c4 -> sh_rpos f4 <= sh_N f4)
            /\ sh_rpos f2 <= sh_rpos f4 /\ (sh_stdio f = false -> sh_rpos f4 <= sh_rpos f2 + i4) /\ (i4 = 0 -> contc c4 -> 1 <= sh_rpos f4) /\ i4 <> 3).
  { subst nn. destruct (Z.eqb_spec i3 0) as [I0|I0].
    - subst i3. destruct (fs_inf_loop_i0 _ _ _ _ _ E3) as [-> ->].
      rewrite (fs_nan_loop_stop0 c2 f2 NC2).
      eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W2|]. split; [apply sh_same_refl|]. split; [exact B2|]. split; [exact CI2|].
      split; [lia|]. split; [intros ST; lia|]. split; [intros _; exact CR2| lia].
    - eexists _, _, _. split; [reflexivity|]. split; [lia|]. split; [exact W3|]. split; [unfold sh_same; auto|]. split; [exact B3|]. split; [exact CI3|].
      split; [lia|]. split; [intros ST; rewrite (NS3 ltac:(congruence)); lia|]. split; [intros; lia|].
      intros ->. cbn in INF. discriminate INF. }
  destruct NN as [i4 [c4 [f4 (-> & Hi4 & W4 & S4 & B4 & CI4 & R4 & NS4 & I40 & I43)]]].
  destruct S4 as (Bf4 & St4 & C04 & N4 & n4).
  assert (BB4 : BB f4) by (intros i; rewrite Bf4, Bf2; apply HB).
  assert (NX4 : NX f4) by (intros i; rewrite Bf4, Bf2; apply HN).
  pose proof (sh_N_le f4 W4) as NL4.
  destruct (Z.eqb_spec i4 3) as [I3|I3]; [exfalso; exact (I43 I3)|].
  destruct (nz i4) eqn:NZ4.
  { eexists _, _. split; [reflexivity|]. split; [apply sh_lim0_wf; now apply sh_unget_wf|].
    unfold sh_lim0; cbn. rewrite sh_unget_buf, sh_unget_stdio. split; [congruence|]. split; [congruence|]. split; [intros; lia| exact NZ0]. }
  assert (I40' : i4 = 0). { unfold nz in NZ4. destruct (Z.eqb_spec i4 0); [assumption| discriminate NZ4]. }
  specialize (I40 I40').
  destruct (Z.eqb_spec c4 48) as [C48|C48].
  - destruct (sh_getc f4) as [c5 f5] eqn:G5.
    destruct (sh_getc_facts f4 c5 f5 G5 W4) as (W5 & B5 & S5 & C05 & N5 & n5 & RP5 & CT5 & SH5).
    rewrite (hex_test_false f4 c5 f5 W4 BB4 NX4 G5).
    destruct (sh_unget_facts f5 W5) as (W6 & S6 & R6). destruct S6 as (Bf6 & St6 & C06 & N6 & n6).
    assert (CC4 : contc c4) by (subst; unfold contc; lia). specialize (CI4 CC4). specialize (I40 CC4).
    destruct (decfloat_total_all_nn fuelc (sh_unget f5) 48 sign pok SGN W6) as [f' [y (E & W' & B' & S' & NS' & NY)]].
    + intros i. rewrite Bf6, B5, Bf4, Bf2. apply HB.
    + unfold bchar. lia.
    + intros _. destruct (sh_unget_shape f5) as [(L & EU)|(L & EU & _)].
      * rewrite EU. clear - W5 L. unfold sh_wf in W5. unfold sh_N. destruct (sh_stdio f5) eqn:ST5; [lia|]. destruct W5 as [_ W5b]. congruence.
      * rewrite EU, sh_unget_N, N5. lia.
    + lia.
    + rewrite Bf6, B5, Bf4, Bf2. exact FU.
    + intros ST. rewrite St6 in ST. rewrite C06, C05, C04, C02. rewrite sh_unget_rpos_nonstdio. 2:{ unfold sh_wf in W5. rewrite ST in W5. tauto. }
      rewrite (nonstdio_read f4 c5 f5 W4 ltac:(congruence) G5). specialize (NS2 ltac:(congruence)). lia.
    + rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
      split; [| exact NY]. intros ST. apply NS'. congruence.
  - destruct (decfloat_total_all_nn fuelc f4 c4 sign pok SGN W4 BB4 B4 CI4 ltac:(lia)) as [f' [y (E & W' & B' & S' & NS' & NY)]].
    + rewrite Bf4, Bf2. exact FU.
    + intros ST. rewrite C04, C02. specialize (NS2 ltac:(congruence)). lia.
    + rewrite E. eexists _, _. split; [reflexivity|]. split; [exact W'|]. split; [congruence|]. split; [congruence|].
      split; [| exact NY]. intros ST. apply NS'. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem scan_strtod_not_nan : forall l vd c,
  Forall (fun ch => FmtFp_facts3.is_numch ch = true) l ->
  scan_strtod (l ++ [0]) = Some (vd, c) ->
  0 <= vd < 2^64 /\ fp_is_nan fmt_double vd = false.
Proof.
  intros l vd c HF E. unfold scan_strtod in E.
  set (f0 := mkSh (l ++ [0]) 0 0 0 false false) in E.
  assert (W0 : sh_wf f0). { unfold sh_wf; cbn. split; [exists l; reflexivity| reflexivity]. }
  assert (HB : Forall (fun c => 0 <= c < 256) l).
  { eapply Forall_impl; [| exact HF]. intros a Ha. exact (NumFacts.is_numch_byte a Ha). }
  assert (HX : Forall (fun c => c <> 120 /\ c <> 88) l).
  { eapply Forall_impl; [| exact HF]. intros a Ha. exact (NumFacts.is_numch_nox a Ha). }
  assert (HN : Forall (fun c => c <> 110 /\ c <> 78) l).
  { eapply Forall_impl; [| exact HF]. intros a Ha. pose proof (FloatScan_junk.numch_range a Ha). lia. }
  destruct (floatscan_total_nn (fuel_of (l ++ [0])) f0 1 W0) as [f' [y (E' & W' & B' & S' & NS' & NY)]].
  - eapply BB_of_bytes; [reflexivity| exact HB].
  - eapply NX_of; [reflexivity| exact HX].
  - eapply NNB_of; [reflexivity| exact HN].
  - cbn. lia.
  - rewrite fuel_of_val. cbn [sh_buf f0]. lia.
  - cbn. intros; lia.
  - rewrite E' in E. injection E as <- _.
    destruct NY as [s [E0 [T0 (-> & PK & NN)]]]. apply f128_to_d_not_nan; assumption.
Qed.
