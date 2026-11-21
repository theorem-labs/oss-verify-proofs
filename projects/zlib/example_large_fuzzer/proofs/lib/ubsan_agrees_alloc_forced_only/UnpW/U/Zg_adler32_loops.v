(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_adler32.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_dkit Z_ukit Z_adler32 Zg_adler32_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZChecksum ZChkArith ZChkAdl AdlerModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma land_ones64 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Ltac br_norm K := zify_cond K; rewrite ?unsigned_lit in K by lia; rewrite ?land_ones64 in K by lia.
Ltac br_true := let K := fresh "K" in if_cases K; br_norm K; [clear K | exfalso; lia].
Ltac br_false := let K := fresh "K" in if_cases K; br_norm K; [exfalso; lia | clear K].
Ltac br_cases K := if_cases K; br_norm K.

Definition PC_AZ_FIN : Z := 0x1b280.      (* [comment removed for export] *)
Definition PC_AZ_MOD : Z := 0x1b238.      (* [comment removed for export] *)
Definition PC_AZ_TAIL : Z := 0x1b214.     (* [comment removed for export] *)
Definition PC_AZ_TAIL1 : Z := 0x1b218.
Definition PC_AZ_BYTES : Z := 0x1b21c.    (* [comment removed for export] *)
Definition PC_AZ_DO16 : Z := 0x1b100.     (* [comment removed for export] *)
Definition PC_AZ_NMAX : Z := 0x1af48.     (* [comment removed for export] *)
Definition PC_AZ_IN16 : Z := 0x1af60.     (* [comment removed for export] *)
Definition PC_AZ_SHORT : Z := 0x1ae44.
Definition AZ_TRAP : Z := 0x1b2c4.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition az_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition az_frame (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j : list byte) : list cell := CB 24 j :: az_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

(* [comment removed for export] *)
Definition az_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v lo : Z) (m0 : mem) : machine_state -> Prop := adler32_postS ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v lo m0.

Lemma shl16_small : forall b, 0 <= b < 2 ^ 48 -> b ≪ 16 mod 18446744073709551616 = b * 2 ^ 16.
Proof. intros b Hb. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mod_small. lia. Qed.

(* [comment removed for export] *)
Ltac az_epilogue FR STK sp := do 14 zs; release_frame FR STK (bv_unsigned sp); zs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma az_fin : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 q11 q12 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  0 <= a < 2^16 -> 0 <= b < 2^16 ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.lor (b * 2 ^ 16) a) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_FIN) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 Ha Hb MI MU WM.
  unfold PC_AZ_FIN, az_frame, az_saved in *. do 2 zs. rewrite shl16_small by lia.
  az_epilogue FR STK sp.
  apply evt_done. unfold az_post, adler32_postS. do 14 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI| exact STK].
Qed.

(* [comment removed for export] *)
Ltac az_magic MI :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    let bs := eval vm_compute in (option.default [] (image_bytes usegs 0x106b0 8)) in
    let RO := fresh "ROM" in
    assert (RO : ro_cells usegs mm 0x106b0 [CB (length bs) bs])
      by (apply ro_cells_image; [exact MI| vm_compute; reflexivity| lia| cbn; lia]);
    cbn [length] in RO end.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma az_mod : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 q11 q12 q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  0 <= a < RLIM -> 0 <= b < RLIM ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z.lor ((b mod ABASE) * 2 ^ 16) (a mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 q11 q12 (wz b) (wz a) q15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_MOD) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 Ha Hb MI MU WM.
  unfold PC_AZ_MOD, RLIM in *.
  pose proof (RQ_bound a Ha) as Qa. pose proof (RQ_bound b Hb) as Qb.
  pose proof (RH_bound a Ha) as Ha2. pose proof (RH_bound b Hb) as Hb2.
  pose proof (RT_bound a Ha) as Ta. pose proof (RT_bound b Hb) as Tb.
  unfold RT, RH, RD, RQ, AMAGIC_IMAGE in Qa, Qb, Ha2, Hb2, Ta, Tb.
  change (983265 * 4294967296 + 221234637) with 4223091239536077 in *.
  zs. az_magic MI. zs. do 16 zs. fold (azq a) (azq b). rewrite ?az_red1, ?az_red2 by (unfold RLIM; lia).
  pose proof (Z.mod_pos_bound a ABASE ltac:(unfold ABASE; lia)) as Ma. pose proof (Z.mod_pos_bound b ABASE ltac:(unfold ABASE; lia)) as Mb.
  unfold ABASE in Ma, Mb.
  eapply (az_fin ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11); first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold ABASE; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
  pose proof (u8ro_read usegs _ p _ i _ (wa (p + i)) BY eq_refl ltac:(lia) eq_refl) as RD;
  try (replace (p + 0) with p in RD by lia).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bZ_cons : forall c d, bZ (c :: d) = bv_unsigned c :: bZ d.
Proof. reflexivity. Qed.

Lemma az_bytes : forall (d : list byte) (q1 sp' gp tp t0 t1 t2 q8 q9 x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b : Z),
  bytes_at usegs m p d -> d <> [] -> 0 <= p -> p + Z.of_nat (length d) < 2^63 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists x15',
      ms' = MS (mkR q1 sp' gp tp t0 t1 t2 q8 q9 (wz (-1)) (wz (p + Z.of_nat (length d))) (wz 0) (wz (snd (adl_raw (bZ d) a b))) (wz (fst (adl_raw (bZ d) a b)))
                   x15' q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6) F (wz PC_AZ_MOD) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp t0 t1 t2 q8 q9 (wz (-1)) (wz p) (wz (Z.of_nat (length d))) (wz b) (wz a) x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_BYTES) fc None m (seg_rom usegs)).
Proof.
  induction d as [|c d IH]; intros until b; intros BY NE Hp Hl MI; [congruence|].
  cbn [length] in Hl, BY |- *. rewrite Nat2Z.inj_succ in *.
  pose proof (u8ro_read usegs m p (c :: d) 0 c (wa (p + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
  replace (p + 0) with p in RD by lia.
  pose proof (bv_unsigned_in_range 8 c) as RC. change (bv_modulus 8) with 256 in RC.
  assert (BY' : bytes_at usegs m (p + 1) d).
  { change (c :: d) with ([c] ++ d) in BY. apply bytes_at_app in BY. exact (proj2 BY). }
  unfold PC_AZ_BYTES. ustep AZ_TRAP. do 5 zs.
  replace (wz (a + bv_unsigned c + b)) with (wz (b + (a + bv_unsigned c))) by (f_equal; lia).
  rewrite bZ_cons, adl_raw_cons.
  destruct d as [|c2 d2].
  - cbn [length] in *. replace (Z.succ (Z.of_nat 0)) with 1 in * by reflexivity. zs. br_false.
    apply evt_done. eexists. cbn [bZ map adl_raw fst snd]. replace (1 + -1) with 0 by reflexivity. reflexivity.
  - pose proof (Nat2Z.is_nonneg (length d2)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_true.
    eapply evt_mono; [eapply evt_eq; [| eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (p + 1) (a + bv_unsigned c) (b + (a + bv_unsigned c)));
                      [exact BY' | discriminate | lia | lia | exact MI]]; zreg_eq |].
    intros ms' (x15' & ->). eexists. zreg_eq.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma az_tail1 : forall (d : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  bytes_at usegs m p d -> d <> [] -> Z.of_nat (length d) <= 15 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a <= 2^32 -> 0 <= b <= 2^39 ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 (wz p) (wz (Z.of_nat (length d))) (wz b) (wz a) x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_TAIL1) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY NE LE Hp Hl Ha Hb MI MU WM.
  destruct (adl_bnd d a b (2^32) (2^39) 15 ltac:(lia) ltac:(lia) LE) as [B1 B2].
  unfold PC_AZ_TAIL1. zs.
  eapply evt_cut.
  { eapply evt_eq; [| eapply (az_bytes d); [exact BY | exact NE | lia | lia | exact MI]]. reflexivity. }
  intros ms' (x15' & ->).
  eapply az_mod; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold RLIM; lia].
Qed.

Lemma az_tail : forall (d : list byte) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (q1 t0 t1 t2 q8 q9 q10 x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m0 : mem) (p a b lo : Z) (j : list byte),
  rw_cells usegs m (bv_unsigned sp + -128) (az_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 j) ->
  stk usegs m lo (bv_unsigned sp + -128) -> lo <= bv_unsigned sp - 128 -> bv_unsigned sp < 2^63 ->
  bytes_at usegs m p d -> Z.of_nat (length d) <= 15 -> 0 <= p -> p + Z.of_nat (length d) < 2^63 ->
  0 <= a <= 2^32 -> 0 <= b <= 2^39 ->
  mem_inv usegs m -> munch [(lo, bv_unsigned sp)] m0 m -> wmono usegs m0 m ->
  evt usegs (az_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (Z.lor ((snd (adl_raw (bZ d) a b) mod ABASE) * 2 ^ 16) (fst (adl_raw (bZ d) a b) mod ABASE)) lo m0)
    (MS (mkR q1 (wz (bv_unsigned sp + -128)) gp tp t0 t1 t2 q8 q9 q10 (wz p) (wz (Z.of_nat (length d))) (wz b) (wz a) x15 q16 q17 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 t3 t4 t5 t6)
        F (wz PC_AZ_TAIL) fc None m (seg_rom usegs)).
Proof.
  intros until j. intros FR STK LO SP63 BY LE Hp Hl Ha Hb MI MU WM.
  unfold PC_AZ_TAIL. destruct d as [|c d].
  - cbn [length Z.of_nat]. zs. br_true. cbn [bZ map adl_raw fst snd].
    eapply az_mod; first [exact FR | exact STK | exact MI | exact MU | exact WM | unfold RLIM; lia].
  - pose proof (Nat2Z.is_nonneg (length d)) as L2. cbn [length] in *. rewrite !Nat2Z.inj_succ in *.
    zs. br_false. replace (Z.succ (Z.of_nat (length d))) with (Z.of_nat (length (c :: d))) by (cbn [length]; lia).
    eapply az_tail1; first [exact FR | exact STK | exact BY | discriminate | exact MI | exact MU | exact WM | cbn [length]; lia].
Qed.

(* [comment removed for export] *)
Lemma firstn_blk : forall (q : nat) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (d : list byte),
  firstn (S q * 16) (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::d)
  = [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15] ++ firstn (q * 16) d.
Proof. reflexivity. Qed.
Lemma firstn_blk0 : forall (d : list byte), firstn (0 * 16) d = [].
Proof. reflexivity. Qed.
Lemma bZ_app : forall xs ys, bZ (xs ++ ys) = bZ xs ++ bZ ys.
Proof. intros. unfold bZ. apply map_app. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma az_blk16 : forall (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (rest : list byte)
    (q1 sp' gp tp q22 q23 q24 q25 q26 q27 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b n : Z),
  bytes_at usegs m p (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::rest) ->
  0 <= p -> p + 16 < 2^63 -> mem_inv usegs m ->
  let ab := adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b in
  evt usegs (fun ms' => exists q23' q24' q25',
      ms' = MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz (p + 16)) (wz (n - 16)) (wz (snd ab)) (wz (fst ab))
                   (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) (wz 15) (wz (p + 16)) q23' q24' q25' q26 q27 (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
               F (wz 0x1b20c) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz p) (wz n) (wz b) (wz a)
             (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) (wz 15) q22 q23 q24 q25 q26 q27 (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
        F (wz PC_AZ_DO16) fc None m (seg_rom usegs)).
Proof.
  intros until n; intros BY Hp Hl MI. cbv zeta.
  az_rd BY p 0. az_rd BY p 1. az_rd BY p 2. az_rd BY p 3. az_rd BY p 4. az_rd BY p 5. az_rd BY p 6. az_rd BY p 7.
  az_rd BY p 8. az_rd BY p 9. az_rd BY p 10. az_rd BY p 11. az_rd BY p 12. az_rd BY p 13. az_rd BY p 14. az_rd BY p 15.
  unfold PC_AZ_DO16. do 16 (ustep AZ_TRAP). do 51 zs. cbv beta.
  set_acc (fst (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b))
          (snd (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b)).
  apply evt_done. do 3 eexists. zreg_eq.
Qed.

(* [comment removed for export] *)
Lemma az_do16 : forall (q : nat) (d : list byte)
    (q1 sp' gp tp q22 q23 q24 q25 q26 q27 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b n : Z),
  bytes_at usegs m p d -> (1 <= q)%nat -> 16 * Z.of_nat q <= Z.of_nat (length d) -> Z.of_nat (length d) = n -> n < 16 * Z.of_nat q + 16 ->
  0 <= p -> p + n < 2^63 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists q23' q24' q25',
      ms' = MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz (p + 16 * Z.of_nat q)) (wz (n - 16 * Z.of_nat q))
                   (wz (snd (adl_raw (bZ (firstn (q * 16) d)) a b))) (wz (fst (adl_raw (bZ (firstn (q * 16) d)) a b)))
                   (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) (wz 15) (wz (p + 16 * Z.of_nat q)) q23' q24' q25' q26 q27 (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
               F (wz 0x1b210) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) (wz p) (wz n) (wz b) (wz a)
             (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) (wz 15) q22 q23 q24 q25 q26 q27 (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
        F (wz PC_AZ_DO16) fc None m (seg_rom usegs)).
Proof.
  induction q as [|q IH]; intros until n; intros BY Hq Hlo Hn Hhi Hp Hl MI; [lia|].
  rewrite Nat2Z.inj_succ in *.
  do 16 (let c := fresh "c" in destruct d as [|c d]; [cbn [length] in Hlo; lia|]).
  cbn [length] in Hlo, Hn. rewrite !Nat2Z.inj_succ in Hlo, Hn.
  assert (BY' : bytes_at usegs m (p + 16) d).
  { lazymatch type of BY with bytes_at _ _ _ (?a0::?a1::?a2::?a3::?a4::?a5::?a6::?a7::?a8::?a9::?a10::?a11::?a12::?a13::?a14::?a15::d) =>
      change (bytes_at usegs m p ([a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] ++ d)) in BY end.
    pose proof (proj2 (proj1 (bytes_at_app _ _ _ _ _) BY)) as H. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H. }
  rewrite firstn_blk, bZ_app, adl_raw_app'.
  eapply evt_cut; [eapply az_blk16; [exact BY | lia | lia | exact MI] |].
  intros ms' (q23' & q24' & q25' & ->).
  zs. destruct (Nat.eq_dec q 0) as [->|NZ].
  - br_false. rewrite firstn_blk0. cbn [bZ map adl_raw]. apply evt_done. do 3 eexists. zreg_eq.
  - br_true.
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let va := get_x14 R in let vb := get_x13 R in
      lazymatch va with Z_to_bv _ ?A => lazymatch vb with Z_to_bv _ ?B =>
        eapply evt_mono; [eapply (IH d) with (p := p + 16) (a := A) (b := B) (n := n - 16);
                          [exact BY' | lia | lia | lia | lia | lia | lia | exact MI] |] end end end.
    intros ms' (q23'' & q24'' & q25'' & ->). do 3 eexists. zreg_eq.
Qed.

(* [comment removed for export] *)
Lemma bv_swrap32_eqm : forall a b, (a - b) mod 2^32 = 0 -> bv_swrap 32 a = bv_swrap 32 b.
Proof.
  intros a b H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (2 ^ 32) with 4294967296 in H. change (4294967296 / 2) with 2147483648. Z.div_mod_to_equations. lia.
Qed.
Lemma swrap32_cnt : forall c, - 2^31 <= c < 2^31 - 1 -> bv_swrap 32 (c mod 18446744073709551616 + 1) = c + 1.
Proof.
  intros c Hc. rewrite (bv_swrap32_eqm _ (c + 1)); [apply bv_swrap32_id; lia|].
  replace (c mod 18446744073709551616 + 1 - (c + 1)) with (- (c - c mod 18446744073709551616)) by lia.
  rewrite (Z_div_mod_eq_full c 18446744073709551616) at 1.
  replace (18446744073709551616 * (c / 18446744073709551616) + c mod 18446744073709551616 - c mod 18446744073709551616)
    with ((c / 18446744073709551616) * 4294967296 * 4294967296) by lia.
  rewrite <- Z.mul_opp_l. change (2 ^ 32) with 4294967296. apply Z.mod_mul.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma az_iblk16 : forall (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 : byte) (rest : list byte)
    (q1 sp' gp tp q11 q12 q21 q22 q23 q24 q25 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b c : Z),
  bytes_at usegs m p (c0::c1::c2::c3::c4::c5::c6::c7::c8::c9::c10::c11::c12::c13::c14::c15::rest) ->
  0 <= p -> p + 16 < 2^63 -> - 2^31 < c < 2^31 - 1 -> mem_inv usegs m ->
  let ab := adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b in
  evt usegs (fun ms' => exists q1' q21' q22' q25',
      ms' = MS (mkR q1' sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) q11 q12 (wz (snd ab)) (wz (fst ab))
                   (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21' q22' q23 q24 q25' (wz (p + 16)) (wz (c + 1)) (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
               F (wz 0x1b068) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) q11 q12 (wz b) (wz a)
             (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21 q22 q23 q24 q25 (wz p) (wz c) (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
        F (wz PC_AZ_IN16) fc None m (seg_rom usegs)).
Proof.
  intros until c; intros BY Hp Hl Hc MI. cbv zeta.
  az_rd BY p 0. az_rd BY p 1. az_rd BY p 2. az_rd BY p 3. az_rd BY p 4. az_rd BY p 5. az_rd BY p 6. az_rd BY p 7.
  az_rd BY p 8. az_rd BY p 9. az_rd BY p 10. az_rd BY p 11. az_rd BY p 12. az_rd BY p 13. az_rd BY p 14. az_rd BY p 15.
  unfold PC_AZ_IN16. do 16 (ustep AZ_TRAP). do 50 zs. cbv beta. rewrite (swrap32_cnt c) by lia.
  set_acc (fst (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b))
          (snd (adl_raw (bZ [c0;c1;c2;c3;c4;c5;c6;c7;c8;c9;c10;c11;c12;c13;c14;c15]) a b)).
  apply evt_done. do 4 eexists. zreg_eq.
Qed.

(* [comment removed for export] *)
Lemma az_in16 : forall (j : nat) (d : list byte)
    (q1 sp' gp tp q11 q12 q21 q22 q23 q24 q25 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (p a b : Z),
  bytes_at usegs m p d -> (1 <= j <= 347)%nat -> 16 * Z.of_nat j <= Z.of_nat (length d) ->
  0 <= p -> p + Z.of_nat (length d) < 2^63 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists q1' q21' q22' q25',
      ms' = MS (mkR q1' sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) q11 q12
                   (wz (snd (adl_raw (bZ (firstn (j * 16) d)) a b))) (wz (fst (adl_raw (bZ (firstn (j * 16) d)) a b)))
                   (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21' q22' q23 q24 q25' (wz (p + 16 * Z.of_nat j)) (wz 0) (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
               F (wz 0x1b06c) fc None m (seg_rom usegs))
    (MS (mkR q1 sp' gp tp (wz (-6)) (wz (-7)) (wz (-8)) (wz (-13)) (wz (-14)) (wz (-1)) q11 q12 (wz b) (wz a)
             (wz (-3)) (wz (-4)) (wz (-5)) (wz (-15)) (wz (-16)) (wz (-17)) q21 q22 q23 q24 q25 (wz p) (wz (- Z.of_nat j)) (wz (-9)) (wz (-10)) (wz (-11)) (wz (-12)))
        F (wz PC_AZ_IN16) fc None m (seg_rom usegs)).
Proof.
  induction j as [|j IH]; intros until b; intros BY Hj Hlo Hp Hl MI; [lia|].
  rewrite Nat2Z.inj_succ in *.
  do 16 (let c := fresh "c" in destruct d as [|c d]; [cbn [length] in Hlo; lia|]).
  cbn [length] in Hlo, Hl. rewrite !Nat2Z.inj_succ in Hlo, Hl.
  assert (BY' : bytes_at usegs m (p + 16) d).
  { lazymatch type of BY with bytes_at _ _ _ (?a0::?a1::?a2::?a3::?a4::?a5::?a6::?a7::?a8::?a9::?a10::?a11::?a12::?a13::?a14::?a15::d) =>
      change (bytes_at usegs m p ([a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a11;a12;a13;a14;a15] ++ d)) in BY end.
    pose proof (proj2 (proj1 (bytes_at_app _ _ _ _ _) BY)) as H. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in H. exact H. }
  rewrite firstn_blk, bZ_app, adl_raw_app'.
  eapply evt_cut; [eapply az_iblk16; [exact BY | lia | lia | lia | exact MI] |].
  intros ms' (q1' & q21' & q22' & q25' & ->).
  zs. destruct (Nat.eq_dec j 0) as [->|NZ].
  - br_false. rewrite firstn_blk0. cbn [bZ map adl_raw]. apply evt_done. do 4 eexists. zreg_eq.
  - br_true.
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let va := get_x14 R in let vb := get_x13 R in
      lazymatch va with Z_to_bv _ ?A => lazymatch vb with Z_to_bv _ ?B =>
        eapply evt_mono; [eapply evt_eq; [| eapply (IH d) with (p := p + 16) (a := A) (b := B);
                          [exact BY' | lia | lia | lia | lia | exact MI]]; zreg_eq |] end end end.
    intros ms' (q1'' & q21'' & q22'' & q25'' & ->). do 4 eexists. zreg_eq.
Qed.
