(* talk, PLAIN build: the two straight-line pieces of the walk that write the frame.
   P_pro   0x156e4 .. 0x15718: addi sp, sp, -0x90 and the thirteen `sd` of ra, s0 .. s11.
   P_spill 0x158a0 .. 0x158f0: the RTM_NEWLINK arm's set-up and its five `sd` into [SP-144, SP-104)
           (talk_defs spill_cells). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem talk_defs talk_kit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Import Tac.
Local Open Scope Z_scope.

Lemma P_pro : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP : Z) (jl jh : list byte),
  sp = Z_to_bv 64 SP -> 144 <= SP < 2 ^ 63 ->
  rw_cells rsegs m (SP + -144) [CB 40 jl] -> rw_cells rsegs m (SP + -104) [CB 104 jh] ->
  mem_inv rsegs m ->
  (forall m', munch [(SP + -144, SP)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (SP + -144) [CB 40 jl] ->
     rw_cells rsegs m' (SP + -104) (saved_cells ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     evt rsegs Q
       (MS (mkR ra (Z_to_bv 64 (SP + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x1571c) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x156e4) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SP jl jh -> HSP FL FH MI K.
  pose proof (munch_refl [(SP + -144, SP)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  do 14 step.
  apply K; assumption.
Qed.

Lemma tp_flag : forall p n, 0 <= p < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  Z_to_bv 64 (Z.land (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 p)))
                     (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 n)))) = Z_to_bv 64 (flagz p n).
Proof.
  intros p n Hp Hn. unfold v_sltu, c_ltu. rewrite !tk_ltu by lia. unfold flagz.
  destruct (Z.ltb_spec 0 p); destruct (Z.ltb_spec 0 n); destruct (Z.eqb_spec p 0); destruct (Z.eqb_spec n 0);
    try lia; cbn [orb]; rewrite ?unsigned_lit by lia; reflexivity.
Qed.

Lemma P_spill : forall (Q : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (SP B off ml KD KN AD AN : Z) (j : list byte),
  sp = Z_to_bv 64 (SP + -144) -> 144 <= SP <= 2 ^ 63 ->
  s6 = Z_to_bv 64 B -> a7 = Z_to_bv 64 off -> s7 = Z_to_bv 64 ml ->
  s1 = Z_to_bv 64 KD -> s3 = Z_to_bv 64 KN -> s0 = Z_to_bv 64 AD -> s2 = Z_to_bv 64 AN ->
  0 <= B < 2 ^ 63 -> 0 <= off < 2 ^ 32 -> 0 <= ml < 2 ^ 32 ->
  0 <= KD < 2 ^ 64 -> 0 <= KN < 2 ^ 64 -> 0 <= AD < 2 ^ 64 -> 0 <= AN < 2 ^ 64 ->
  rw_cells rsegs m (SP + -144) [CB 40 j] -> mem_inv rsegs m ->
  (forall m' a0' a1' a2' a3',
     munch [(SP + -144, SP + -104)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
     rw_cells rsegs m' (SP + -144) (spill_cells AN B KN AD KD) ->
     evt rsegs Q
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 3)
                a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (ml - 32)) s8 (Z_to_bv 64 0x1fffc) s10 (Z_to_bv 64 (off + 32))
                t3 t4 t5 t6)
           F (Z_to_bv 64 0x158f4) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x158a0) fc None m (seg_rom rsegs)).
Proof.
  intros Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m SP B off ml KD KN AD AN j -> HSP -> -> -> -> -> -> -> HB HO HM HKD HKN HAD HAN FL MI K.
  pose proof (munch_refl [(SP + -144, SP + -104)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  do 21 step.
  replace (Z_to_bv 64 (ml + -32)) with (Z_to_bv 64 (ml - 32)) by (f_equal; lia).
  match goal with H : rw_cells rsegs ?mm (SP + -144) ?cs |- _ =>
    assert (E : cs = spill_cells AN B KN AD KD); [|rewrite E in H] end.
  { unfold spill_cells. rewrite !alu_sltu, !tp_flag by lia.
    replace (AN + -1) with (AN - 1) by lia. replace (KN + -1) with (KN - 1) by lia. reflexivity. }
  apply K; assumption.
Qed.
