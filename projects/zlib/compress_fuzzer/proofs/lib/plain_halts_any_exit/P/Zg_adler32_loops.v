(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_kit Z_dview Z_dkit Z_adler32 Zg_adler32_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZChecksum ZChkArith ZChkAdl AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac br_norm K := zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite ?land_ones64 in K by lia.
Ltac br_true := let K := fresh "K" in if_cases K; br_norm K; [clear K | exfalso; lia].
Ltac br_false := let K := fresh "K" in if_cases K; br_norm K; [exfalso; lia | clear K].
Ltac br_cases K := if_cases K; br_norm K.

Definition PC_AZ_FIN : Z := 0x1a474.
Definition PC_AZ_MOD : Z := 0x1a430.
Definition PC_AZ_TAIL : Z := 0x1a410.
Definition PC_AZ_TAIL1 : Z := 0x1a414.
Definition PC_AZ_BYTES : Z := 0x1a418.
Definition PC_AZ_DO16 : Z := 0x1a344.
Definition PC_AZ_NMAX : Z := 0x1a208.
Definition PC_AZ_IN16 : Z := 0x1a21c.
Definition PC_AZ_SHORT : Z := 0x1a14c.

Definition az_frame (s0 s1 s2 : word) (j : list byte) : list cell := [CB 8 j; C8 s2; C8 s1; C8 s0].

Definition az_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v lo : Z) (m0 : mem) : machine_state -> Prop := adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo m0.

Lemma shl16_small : forall b, 0 <= b < 2 ^ 48 -> b ≪ 16 mod 18446744073709551616 = b * 2 ^ 16.
Proof. intros b Hb. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

Lemma az_fin : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q8 q9 q10 q11 q12 a5 a6 a7 q18 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (a b lo : Z) (j : list byte),
  rw_cells psegs m (bv_unsigned sp + -32) (az_frame s0 s1 s2 j) ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 ->
  0 <= a < 2^16 -> 0 <= b < 2^16 ->
  mem_inv psegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono psegs m0 m ->
  evt psegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.lor (b * 2 ^ 16) a) lo m0)
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) a5 a6 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_FIN) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros FR STK LO SP63 Ha Hb MI MU WM.
  unfold PC_AZ_FIN, az_frame in *. do 2 zs. rewrite shl16_small by lia.
  do 4 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold az_post, adler32_postS. do 14 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact STK].
Qed.

Ltac az_magic MI :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let bs := eval vm_compute in (option.default [] (image_bytes psegs 0x10690 8)) in
    let RO := fresh "ROM" in
    assert (RO : ro_cells psegs mm 0x10690 [CB (length bs) bs])
      by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
    cbn [length] in RO end.

Definition azq (x : Z) : Z := Z.shiftr (x * 4223091239536077) 64.

Lemma az_red_core : forall x, 0 <= x < RLIM ->
  x - Z.shiftr (Z.shiftr (x - azq x) 1 + azq x) 15 * 65521 = x mod ABASE.
Proof.
  intros x Hx. pose proof (RT_div x Hx) as E. unfold RT, RH, RD, RQ, AMAGIC_IMAGE in E. unfold azq.
  change (983265 * 4294967296 + 221234637) with 4223091239536077 in E.
  rewrite (Z.add_comm (Z.shiftr (x - _) 1)). rewrite E.
  rewrite (Z.mod_eq x ABASE) by (unfold ABASE; lia). unfold ABASE. lia.
Qed.

Lemma az_red1 : forall x, 0 <= x < RLIM ->
  x - (Z.shiftr ((Z.shiftr (x - (azq x) mod 18446744073709551616) 1 + azq x) mod 18446744073709551616) 15 * 65521) mod 18446744073709551616
  = x mod ABASE.
Proof.
  intros x Hx. pose proof (RQ_bound x Hx) as Q. pose proof (RH_bound x Hx) as R. pose proof (RT_bound x Hx) as T.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Q, R, T. change (983265 * 4294967296 + 221234637) with 4223091239536077 in Q, R, T.
  fold (azq x) in Q, R, T. rewrite (Z.add_comm (azq x)) in T. unfold RLIM in *.
  rewrite (Z.mod_small (azq x)) by lia.
  rewrite (Z.mod_small (Z.shiftr (x - azq x) 1 + azq x)) by lia.
  rewrite (Z.mod_small (_ * 65521)) by lia.
  apply az_red_core. unfold RLIM. lia.
Qed.

Lemma az_red2 : forall x, 0 <= x < RLIM ->
  x - Z.shiftr ((Z.shiftr (x - (azq x) mod 18446744073709551616) 1 + azq x) mod 18446744073709551616) 15 * 65521
  = x mod ABASE.
Proof.
  intros x Hx. pose proof (RQ_bound x Hx) as Q. pose proof (RH_bound x Hx) as R. pose proof (RT_bound x Hx) as T.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Q, R, T. change (983265 * 4294967296 + 221234637) with 4223091239536077 in Q, R, T.
  fold (azq x) in Q, R, T. rewrite (Z.add_comm (azq x)) in T. unfold RLIM in *.
  rewrite (Z.mod_small (azq x)) by lia.
  rewrite (Z.mod_small (Z.shiftr (x - azq x) 1 + azq x)) by lia.
  apply az_red_core. unfold RLIM. lia.
Qed.

Lemma az_mod : forall (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q8 q9 q11 q12 a5 a6 a7 q18 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (a b lo : Z) (j : list byte),
  rw_cells psegs m (bv_unsigned sp + -32) (az_frame s0 s1 s2 j) ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 ->
  0 <= a < RLIM -> 0 <= b < RLIM ->
  mem_inv psegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono psegs m0 m ->
  evt psegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE)) lo m0)
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 q8 q9 (wz 66008) q11 q12 (wz b) (wz a) a5 a6 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_MOD) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros FR STK LO SP63 Ha Hb MI MU WM.
  unfold PC_AZ_MOD, RLIM in *. az_magic MI.
  pose proof (RQ_bound a Ha) as Qa. pose proof (RQ_bound b Hb) as Qb.
  pose proof (RH_bound a Ha) as Ha2. pose proof (RH_bound b Hb) as Hb2.
  pose proof (RT_bound a Ha) as Ta. pose proof (RT_bound b Hb) as Tb.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Qa, Qb, Ha2, Hb2, Ta, Tb.
  change (983265 * 4294967296 + 221234637) with 4223091239536077 in *.
  do 3 zs. do 14 zs. fold (azq a) (azq b). rewrite ?az_red1, ?az_red2 by (unfold RLIM; lia).
  pose proof (Z.mod_pos_bound a ABASE ltac:(unfold ABASE; lia)) as Ma. pose proof (Z.mod_pos_bound b ABASE ltac:(unfold ABASE; lia)) as Mb.
  unfold ABASE in Ma, Mb.
  eapply (az_fin ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold ABASE; lia].
Qed.

Lemma bZ_cons : forall c d, bZ (c :: d) = bv_unsigned c :: bZ d.
Proof. reflexivity. Qed.

Lemma az_bytes : forall (d : list byte) (ra sp' gp tp t0 t1 t2 q8 q9 q10 x11 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x16 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b : Z),
  bytes_at psegs m p d -> d <> [] -> 0 <= p -> p + Z.of_nat (length d) < 2^63 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists x11' x16',
      ms' = MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 x11' (wz (p + Z.of_nat (length d))) (wz (snd (adl_raw (bZ d) a b))) (wz (fst (adl_raw (bZ d) a b)))
                   (wz (p + Z.of_nat (length d))) x16' a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PC_AZ_MOD) fc None m (seg_rom psegs))
    (MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 x11 (wz (p + Z.of_nat (length d))) (wz b) (wz a) (wz p) x16 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_BYTES) fc None m (seg_rom psegs)).
Proof.
  induction d as [|c d IH]; intros until b; intros BY NE Hp Hl MI; [congruence|].
  cbn [length] in Hl, BY |- *. rewrite Nat2Z.inj_succ in *.
  pose proof (u8ro_read psegs m p (c :: d) 0 c (wa (p + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
  replace (p + 0) with p in RD by lia.
  pose proof (bv_unsigned_in_range 8 c) as RC. change (bv_modulus 8) with 256 in RC.
  assert (BY' : bytes_at psegs m (p + 1) d).
  { change (c :: d) with ([c] ++ d) in BY. apply bytes_at_app in BY. exact (proj2 BY). }
  unfold PC_AZ_BYTES. do 5 zs.
  replace (wz (a + bv_unsigned c + b)) with (wz (b + (a + bv_unsigned c))) by (f_equal; lia).
  rewrite bZ_cons, adl_raw_cons.
  destruct d as [|c2 d2].
  -
    cbn [length] in *. replace (Z.succ (Z.of_nat 0)) with 1 in * by reflexivity. zs. br_false.
    apply evt_done. do 2 eexists. cbn [bZ map adl_raw fst snd]. reflexivity.
  - pose proof (Nat2Z.is_nonneg (length d2)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_true.
    replace (p + Z.succ (Z.succ (Z.of_nat (length d2)))) with (p + 1 + Z.succ (Z.of_nat (length d2))) by lia.
    apply IH; [exact BY' | discriminate | lia | lia | exact MI].
Qed.

Lemma Forall_bZ : forall d, Forall (fun b => 0 <= b < 256) (bZ d).
Proof.
  induction d as [|c d IH]; [constructor|]. rewrite bZ_cons. constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 8 c) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

Lemma adl_bnd : forall d u v U V N, 0 <= u <= U -> 0 <= v <= V -> Z.of_nat (length d) <= N ->
  0 <= fst (adl_raw (bZ d) u v) <= U + 255 * N /\ 0 <= snd (adl_raw (bZ d) u v) <= V + N * (U + 255 * N).
Proof.
  intros d u v U V N Hu Hv HN.
  destruct (adl_raw_bound (bZ d) u v (Forall_bZ d) ltac:(lia) ltac:(lia)) as [H1 H2]. rewrite bZ_length in H1, H2.
  set (n := Z.of_nat (length d)) in *. assert (Hn : 0 <= n <= N) by lia.
  assert (M1 : 255 * n <= 255 * N) by lia.
  assert (M2 : n * (u + 255 * n) <= N * (U + 255 * N)) by (apply Z.mul_le_mono_nonneg; lia).
  lia.
Qed.

Lemma az_tail1 : forall (d : list byte) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q8 q9 x11 x16 a7 q18 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells psegs m (bv_unsigned sp + -32) (az_frame s0 s1 s2 j) ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 ->
  bytes_at psegs m p d -> d <> [] -> Z.of_nat (length d) <= 15 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a <= 2^32 -> 0 <= b <= 2^39 ->
  mem_inv psegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono psegs m0 m ->
  evt psegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 q8 q9 (wz 66008) x11 (wz (Z.of_nat (length d))) (wz b) (wz a) (wz p) x16 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_TAIL1) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY NE LE Hp Hl Ha Hb MI MU WM.
  destruct (adl_bnd d a b (2^32) (2^39) 15 ltac:(lia) ltac:(lia) LE) as [B1 B2].
  unfold PC_AZ_TAIL1. zs.
  eapply evt_cut.
  { eapply evt_eq; [| eapply (az_bytes d); [exact BY | exact NE | lia | lia | exact MI]]. reflexivity. }
  intros ms' (x11' & x16' & ->).
  eapply az_mod; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold RLIM; lia].
Qed.

Lemma az_tail : forall (d : list byte) (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (q8 q9 x11 x16 a7 q18 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells psegs m (bv_unsigned sp + -32) (az_frame s0 s1 s2 j) ->
  stk psegs m lo (bv_unsigned sp + -32) -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp < 2^63 ->
  bytes_at psegs m p d -> Z.of_nat (length d) <= 15 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a <= 2^32 -> 0 <= b <= 2^39 ->
  mem_inv psegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono psegs m0 m ->
  evt psegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR ra (wz (bv_unsigned sp + -32)) gp tp t0 t1 t2 q8 q9 (wz 66008) x11 (wz (Z.of_nat (length d))) (wz b) (wz a) (wz p) x16 a7 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_TAIL) fc None m (seg_rom psegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY LE Hp Hl Ha Hb MI MU WM.
  unfold PC_AZ_TAIL. destruct d as [|c d].
  - cbn [length Z.of_nat]. zs. br_true. cbn [bZ map adl_raw fst snd].
    eapply az_mod; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold RLIM; lia].
  - pose proof (Nat2Z.is_nonneg (length d)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_false. replace (Z.succ (Z.of_nat (length d))) with (Z.of_nat (length (c :: d))) by (cbn [length]; lia).
    eapply az_tail1; first [exact FR | exact STK | exact BY | discriminate | exact MI | exact MU | exact WM | cbn [length]; lia].
Qed.

Ltac get_x13 R := lazymatch R with TNode (TNode _ (Some _) (TNode _ (Some _) (TNode _ (Some ?v) _))) None _ => v end.
Ltac get_x14 R := lazymatch R with TNode _ None (TNode _ (Some _) (TNode _ (Some _) (TNode _ (Some ?v) _))) => v end.
Lemma TNode_eq3 : forall {A} (l l' r r' : tree A) (v v' : option A),
  l = l' -> v = v' -> r = r' -> TNode l v r = TNode l' v' r'.
Proof. intros; subst; reflexivity. Qed.
Lemma Some_eq1 : forall {A} (x y : A), x = y -> Some x = Some y.
Proof. intros; subst; reflexivity. Qed.
Lemma wz_eq1 : forall x y, x = y -> wz x = wz y.
Proof. intros; subst; reflexivity. Qed.
Lemma MS_eq2 : forall r r' (F : bvmap 5 word) (pc pc' : word) (fc : bv 32) rv (m : mem) ro,
  r = r' -> pc = pc' -> MS r F pc fc rv m ro = MS r' F pc' fc rv m ro.
Proof. intros; subst; reflexivity. Qed.

Ltac zreg_eq :=
  lazymatch goal with
  | |- ?x = ?y =>
      first [ constr_eq x y; reflexivity
            | is_evar x; reflexivity
            | is_evar y; reflexivity
            | lazymatch goal with
              | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => apply MS_eq2; zreg_eq
              | |- TNode _ _ _ = TNode _ _ _ => apply TNode_eq3; zreg_eq
              | |- Some _ = Some _ => apply Some_eq1; zreg_eq
              | |- Z_to_bv _ _ = Z_to_bv _ _ => apply wz_eq1;
                   first [ lia
                         | lazymatch goal with |- ?u = ?v => is_Zlit u; first [is_Zlit v | unfold v] end; reflexivity
                         | cbn [fst snd adl_raw map bZ app]; lia ]
              | |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => unfold mkR; zreg_eq
              | |- _ = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => unfold mkR; zreg_eq
              end ]
  end.

Ltac set_acc A B :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let va := get_x14 R in let vb := get_x13 R in
    replace va with (wz A) by (cbn [bZ map adl_raw fst snd]; f_equal; lia);
    replace vb with (wz B) by (cbn [bZ map adl_raw fst snd]; f_equal; lia) end.

Ltac az_rd BY p i :=
  let RD := fresh "RD" in
  pose proof (u8ro_read psegs _ p _ i _ (wa (p + i)) BY eq_refl ltac:(lia) eq_refl) as RD;
  try (replace (p + 0) with p in RD by lia).

Lemma az_blk16 : forall (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (rest : list byte)
    (ra sp' gp tp t0 t1 t2 q8 q9 q10 x16 x17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b n : Z),
  bytes_at psegs m p (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::rest) ->
  0 <= p -> p + 16 < 2^63 -> mem_inv psegs m ->
  let ab := adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b in
  evt psegs (fun ms' => exists x16' x17' t0' t1',
      ms' = MS (mkR ra sp' gp tp t0' t1' t2 q8 q9 q10 (wz 15) (wz (n - 16)) (wz (snd ab)) (wz (fst ab)) (wz (p + 16)) x16' x17' q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x1a40c) fc None m (seg_rom psegs))
    (MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 (wz 15) (wz n) (wz b) (wz a) (wz p) x16 x17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_DO16) fc None m (seg_rom psegs)).
Proof.
  intros until n; intros BY Hp Hl MI. cbv zeta.
  az_rd BY p 0. az_rd BY p 1. az_rd BY p 2. az_rd BY p 3. az_rd BY p 4. az_rd BY p 5. az_rd BY p 6. az_rd BY p 7.
  az_rd BY p 8. az_rd BY p 9. az_rd BY p 10. az_rd BY p 11. az_rd BY p 12. az_rd BY p 13. az_rd BY p 14. az_rd BY p 15.
  unfold PC_AZ_DO16. do 50 zs. cbv beta.
  set_acc (fst (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b))
          (snd (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b)).
  apply evt_done. do 4 eexists. zreg_eq.
Qed.

Lemma firstn_blk : forall (q : nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (d : list byte),
  firstn (S q * 16) (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::d)
  = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15] ++ firstn (q * 16) d.
Proof. reflexivity. Qed.
Lemma firstn_blk0 : forall (d : list byte), firstn (0 * 16) d = [].
Proof. reflexivity. Qed.
Lemma bZ_app : forall xs ys, bZ (xs ++ ys) = bZ xs ++ bZ ys.
Proof. intros. unfold bZ. apply map_app. Qed.

Lemma az_do16 : forall (q : nat) (d : list byte)
    (ra sp' gp tp t0 t1 t2 q8 q9 q10 x16 x17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b n : Z),
  bytes_at psegs m p d -> (1 <= q)%nat -> 16 * Z.of_nat q <= Z.of_nat (length d) -> Z.of_nat (length d) = n -> n < 16 * Z.of_nat q + 16 ->
  0 <= p -> p + n < 2^63 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists x16' x17' t0' t1',
      ms' = MS (mkR ra sp' gp tp t0' t1' t2 q8 q9 q10 (wz 15) (wz (n - 16 * Z.of_nat q))
                   (wz (snd (adl_raw (bZ (firstn (q * 16) d)) a b))) (wz (fst (adl_raw (bZ (firstn (q * 16) d)) a b)))
                   (wz (p + 16 * Z.of_nat q)) x16' x17' q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz PC_AZ_TAIL) fc None m (seg_rom psegs))
    (MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 (wz 15) (wz n) (wz b) (wz a) (wz p) x16 x17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz PC_AZ_DO16) fc None m (seg_rom psegs)).
Proof.
  induction q as [|q IH]; intros until n; intros BY Hq Hlo Hn Hhi Hp Hl MI; [lia|].
  rewrite Nat2Z.inj_succ in *.
  do 16 (let c := fresh "c" in destruct d as [|c d]; [cbn [length] in Hlo; lia|]).
  cbn [length] in Hlo, Hn. rewrite !Nat2Z.inj_succ in Hlo, Hn.
  assert (BY' : bytes_at psegs m (p + 16) d).
  { lazymatch type of BY with bytes_at _ _ _ (?a0::?a1::?a2::?a3::?a4::?a5::?a6::?a7::?a8::?a9::?a10::?a11::?a12::?a13::?a14::?a15::d) =>
      change (bytes_at psegs m p ([a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] ++ d)) in BY end.
    pose proof (proj2 (proj1 (bytes_at_app _ _ _ _ _) BY)) as H. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H. }
  rewrite firstn_blk, bZ_app, adl_raw_app'.
  eapply evt_cut; [eapply az_blk16; [exact BY | lia | lia | exact MI] |].
  intros ms' (x16' & x17' & t0' & t1' & ->).
  zs. destruct (Nat.eq_dec q 0) as [->|NZ].
  - br_false. rewrite firstn_blk0. cbn [bZ map adl_raw]. apply evt_done. do 4 eexists. zreg_eq.
  - br_true.
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let va := get_x14 R in let vb := get_x13 R in
      lazymatch va with Z_to_bv _ ?A => lazymatch vb with Z_to_bv _ ?B =>
        eapply evt_mono; [eapply (IH d) with (p := p + 16) (a := A) (b := B) (n := n - 16);
                          [exact BY' | lia | lia | lia | lia | lia | lia | exact MI] |] end end end.
    intros ms' (x16'' & x17'' & t0'' & t1'' & ->). do 4 eexists. zreg_eq.
Qed.

Lemma az_iblk16 : forall (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (rest : list byte)
    (ra sp' gp tp t0 t1 t2 q8 q9 q10 q11 q12 q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b e : Z),
  bytes_at psegs m p (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::rest) ->
  0 <= p -> p + 16 < 2^63 -> mem_inv psegs m ->
  let ab := adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b in
  evt psegs (fun ms' => exists q8' q9' q18' t6',
      ms' = MS (mkR ra sp' gp tp t0 t1 t2 q8' q9' q10 q11 q12 (wz (snd ab)) (wz (fst ab)) q15 q16 q17 q18' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (wz e) (wz (p + 16)) t6')
               F (wz 0x1a2e0) fc None m (seg_rom psegs))
    (MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (wz e) (wz p) t6)
        F (wz PC_AZ_IN16) fc None m (seg_rom psegs)).
Proof.
  intros until e; intros BY Hp Hl MI. cbv zeta.
  az_rd BY p 0. az_rd BY p 1. az_rd BY p 2. az_rd BY p 3. az_rd BY p 4. az_rd BY p 5. az_rd BY p 6. az_rd BY p 7.
  az_rd BY p 8. az_rd BY p 9. az_rd BY p 10. az_rd BY p 11. az_rd BY p 12. az_rd BY p 13. az_rd BY p 14. az_rd BY p 15.
  unfold PC_AZ_IN16. do 49 zs. cbv beta.
  set_acc (fst (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b))
          (snd (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b)).
  apply evt_done. do 4 eexists. zreg_eq.
Qed.

Lemma az_in16 : forall (j : nat) (d : list byte)
    (ra sp' gp tp t0 t1 t2 q8 q9 q10 q11 q12 q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b : Z),
  bytes_at psegs m p d -> (1 <= j)%nat -> 16 * Z.of_nat j <= Z.of_nat (length d) ->
  0 <= p -> p + Z.of_nat (length d) < 2^63 -> mem_inv psegs m ->
  evt psegs (fun ms' => exists q8' q9' q18' t6',
      ms' = MS (mkR ra sp' gp tp t0 t1 t2 q8' q9' q10 q11 q12
                   (wz (snd (adl_raw (bZ (firstn (j * 16) d)) a b))) (wz (fst (adl_raw (bZ (firstn (j * 16) d)) a b)))
                   q15 q16 q17 q18' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (wz (p + 16 * Z.of_nat j)) (wz (p + 16 * Z.of_nat j)) t6')
               F (wz 0x1a2e4) fc None m (seg_rom psegs))
    (MS (mkR ra sp' gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) q15 q16 q17 q18 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (wz (p + 16 * Z.of_nat j)) (wz p) t6)
        F (wz PC_AZ_IN16) fc None m (seg_rom psegs)).
Proof.
  induction j as [|j IH]; intros until b; intros BY Hj Hlo Hp Hl MI; [lia|].
  rewrite Nat2Z.inj_succ in *.
  do 16 (let c := fresh "c" in destruct d as [|c d]; [cbn [length] in Hlo; lia|]).
  cbn [length] in Hlo, Hl. rewrite !Nat2Z.inj_succ in Hlo, Hl.
  assert (BY' : bytes_at psegs m (p + 16) d).
  { lazymatch type of BY with bytes_at _ _ _ (?a0::?a1::?a2::?a3::?a4::?a5::?a6::?a7::?a8::?a9::?a10::?a11::?a12::?a13::?a14::?a15::d) =>
      change (bytes_at psegs m p ([a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] ++ d)) in BY end.
    pose proof (proj2 (proj1 (bytes_at_app _ _ _ _ _) BY)) as H. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H. }
  rewrite firstn_blk, bZ_app, adl_raw_app'.
  eapply evt_cut; [eapply az_iblk16; [exact BY | lia | lia | exact MI] |].
  intros ms' (q8' & q9' & q18' & t6' & ->).
  zs. destruct (Nat.eq_dec j 0) as [->|NZ].
  - br_false. rewrite firstn_blk0. cbn [bZ map adl_raw]. apply evt_done. do 4 eexists. zreg_eq.
  - br_true.
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let va := get_x14 R in let vb := get_x13 R in
      lazymatch va with Z_to_bv _ ?A => lazymatch vb with Z_to_bv _ ?B =>
        eapply evt_mono; [eapply evt_eq; [| eapply (IH d) with (p := p + 16) (a := A) (b := B);
                          [exact BY' | lia | lia | lia | lia | exact MI]]; zreg_eq |] end end end.
    intros ms' (q8'' & q9'' & q18'' & t6'' & ->). do 4 eexists. zreg_eq.
Qed.

