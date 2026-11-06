From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells diginet_scribble_text_c.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_text.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import diginet_scribble_text_lem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require ZBridge.
Import ListNotations.
Open Scope Z_scope.

(** ---- bytes and the image's code forms ---- *)

Lemma b8_byte : forall b : byte, b8 (bv_unsigned b) = b.
Proof. intros b. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma zb_cons : forall (x : byte) l, zb (x :: l) = bv_unsigned x :: zb l.
Proof. reflexivity. Qed.

Lemma lts_shl56_check :
  codec_text.all_from (fun x => Bool.eqb (bv_lts (Z_to_bv 64 (Z.shiftl x 56)) (Z_to_bv 64 0)) (128 <=? x)) 0 256 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lts_shl56 : forall b : byte,
  bv_lts (Z_to_bv 64 (Z.shiftl (bv_unsigned b) 56)) (Z_to_bv 64 0) = (128 <=? bv_unsigned b).
Proof.
  intros b. apply Bool.eqb_prop. apply (codec_text.all_from_spec _ 256 0 lts_shl56_check).
  pose proof (byte_range b). lia.
Qed.

Section Walk.
  Variables (ra sp gp tp s0 s1 a0 a1 a2 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n : Z) (tb : list byte).
  Hypothesis HA0 : bv_unsigned a0 <> 0.
  Hypothesis HTZ : In (b8 0) tb.
  Hypothesis HA1 : bv_unsigned a1 <> 0.
  Hypothesis HA2 : bv_unsigned a2 = n.
  Hypothesis HDJ : disj (bv_unsigned a0) (Z.of_nat (length tb)) (bv_unsigned a1) n.

  Notation TX := (bv_unsigned a0).
  Notation OX := (bv_unsigned a1).
  (** The register a4 holds ~a1 for the pointer-overflow checks of out + o. *)
  Notation NOT := (18446744073709551615 - bv_unsigned a1).

  Definition INV (m1 : word -> option byte) (ob : list byte) : Prop :=
    bytes_at rsegs m1 TX tb /\ u8arr rsegs m1 OX ob /\ length ob = Z.to_nat n /\
    mem_inv rsegs m1 /\ munch [(OX, OX + n)] m m1 /\ wmono rsegs m m1.

  Definition POSTv (ov : list Z) (r : Z) : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a0' a1' a3' a4' a5' a6' a7' t3' t4' t5' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2 a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch [(OX, OX + n)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      a0' = Z_to_bv 64 r /\ rw_cells rsegs m' OX [CB (Z.to_nat n) (bz ov)].

  Lemma inv_store : forall m1 ob o b, INV m1 ob -> 0 <= o < n ->
    INV (write_to_mem m1 (wa (OX + o)) [b]) (upd ob (Z.to_nat o) b).
  Proof.
    intros m1 ob o b (TBi & OUTi & LEN & MI & MU & WM) Ho.
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (u8arr_store_ok rsegs m1 _ ob o _ OUTi ltac:(rewrite LEN; lia) eq_refl) as HS.
    unfold disj in HDJ.
    split; [apply bytes_at_write_other; [exact TBi | lia | cbn; lia | cbn; lia]|].
    split; [apply u8arr_write; [exact OUTi | rewrite LEN; lia]|].
    split; [rewrite upd_length; exact LEN|].
    split; [apply mem_inv_store; [exact MI | exact HS]|].
    split; [apply munch_write; [exact MU | lia | cbn; lia | cbn [inside]; cbn; lia]|].
    apply wmono_write. exact WM.
  Qed.

  Lemma out_store_ok : forall m1 ob o, INV m1 ob -> 0 <= o < n -> store_ok rsegs m1 (wa (OX + o)) 1 = true.
  Proof.
    intros m1 ob o (TBi & OUTi & LEN & _) Ho.
    exact (u8arr_store_ok rsegs m1 _ ob o _ OUTi ltac:(rewrite LEN; lia) eq_refl).
  Qed.

  Lemma text_read : forall m1 ob j b, INV m1 ob -> nth_error tb j = Some b ->
    ov_read_bytes rsegs m1 (wa (TX + Z.of_nat j)) 1 = Some [b].
  Proof.
    intros m1 ob j b (TBi & _) E.
    apply (u8ro_read rsegs m1 (bv_unsigned a0) tb (Z.of_nat j) b); [exact TBi | rewrite Nat2Z.id; exact E | lia | reflexivity].
  Qed.

  (** The return at 0x15e4c. *)
  Lemma fin : forall m1 ov r x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30,
    INV m1 (bz ov) -> x10 = Z_to_bv 64 r ->
    evt rsegs (POSTv ov r)
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 a2 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x15e4c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros m1 ov r x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30 (TBi & OUTi & LEN & MI & MU & WM) ->.
    zstep.
    apply rw_cells_of_u8arr in OUTi. rewrite LEN in OUTi.
    finish.
    all: reflexivity.
  Qed.

  (** The pad loop at 0x15e38: out[o] := ' ' while o < n (a1 = out + o, a3 = ' '). *)
  Lemma padloop : forall k o q ov r m1 ob x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30,
    Z.to_nat (n - o) = k -> 0 <= o < n -> INV m1 ob -> length q = Z.to_nat o -> firstn (Z.to_nat o) ob = bz q ->
    x10 = Z_to_bv 64 r -> x11 = Z_to_bv 64 (OX + o) -> x13 = Z_to_bv 64 32 -> x14 = Z_to_bv 64 NOT ->
    x15 = Z_to_bv 64 o -> ov = q ++ repeat 0x20 (Z.to_nat (n - o)) ->
    evt rsegs (POSTv ov r)
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 a2 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x15e38) fc None m1 (seg_rom rsegs)).
  Proof.
    induction k as [|k IH]; intros o q ov r m1 ob x5 x6 x7 x10 x11 x13 x14 x15 x16 x17 x28 x29 x30
                                   Hk Ho I Hl Hp -> -> -> -> -> Hov; [lia|].
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & MI & MU & WM).
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
    pose proof (out_store_ok m1 ob o I0 Ho) as HS.
    zstep. if_cases K; zify_cond K; [rewrite ?unsigned_lit in K by lia; exfalso; lia|].
    zstep. zstep. rewrite (le1_lit 32).
    pose proof (inv_store m1 ob o (Z_to_bv 8 32) I0 Ho) as I2. unfold wa in I2.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (OX + o)) [Z_to_bv 8 32]) in *. clearbody m2.
    clear TBi OUTi MI MU WM HS I0.
    pose proof (Hp_snoc ob o (Z_to_bv 8 32) (bz q) ltac:(lia) ltac:(lia) Hp) as Hp2.
    replace (bz q ++ [Z_to_bv 8 32]) with (bz (q ++ [0x20])) in Hp2 by (unfold bz; rewrite map_app; reflexivity).
    assert (KN : Z.to_nat (n - o) = S (Z.to_nat (n - (o + 1)))) by lia.
    rewrite KN in Hov. cbn [repeat] in Hov.
    zstep. zstep. if_cases K2; zify_cond K2.
    - rewrite HA2 in K2.
      eapply (IH (o + 1) (q ++ [0x20])); try reflexivity; try exact I2; try exact Hp2; try lia.
      + rewrite length_app. cbn. lia.
      + f_equal. lia.
      + rewrite Hov, <- app_assoc. reflexivity.
    - (* o + 1 = n: return *)
      rewrite HA2 in K2. assert (o + 1 = n) by lia.
      rewrite firstn_all2 in Hp2 by (rewrite upd_length, LEN; lia). rewrite Hp2 in I2.
      eapply fin; [ | reflexivity].
      replace (Z.to_nat (n - (o + 1))) with 0%nat in Hov by lia. cbn [repeat] in Hov.
      rewrite Hov. exact I2.
  Qed.

  (** The pad at 0x15e2c. *)
  Lemma pad : forall o q ov r m1 ob x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30,
    0 <= o <= n -> INV m1 ob -> length q = Z.to_nat o -> firstn (Z.to_nat o) ob = bz q ->
    x10 = Z_to_bv 64 r -> x14 = Z_to_bv 64 NOT -> x15 = Z_to_bv 64 o ->
    ov = q ++ repeat 0x20 (Z.to_nat (n - o)) ->
    evt rsegs (POSTv ov r)
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 a1 a2 x13 x14 x15 x16 x17
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
          F (Z_to_bv 64 0x15e2c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros o q ov r m1 ob x5 x6 x7 x10 x13 x14 x15 x16 x17 x28 x29 x30 Ho I Hl Hp -> -> -> Hov.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & MI & MU & WM).
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    zstep. if_cases K; zify_cond K; rewrite ?HA2 in K.
    - assert (o = n) by lia. subst o.
      rewrite firstn_all2 in Hp by lia. rewrite Hp in I0.
      eapply fin; [ | reflexivity].
      replace (Z.to_nat (n - n)) with 0%nat in Hov by lia. cbn [repeat] in Hov. rewrite app_nil_r in Hov.
      rewrite Hov. exact I0.
    - zstep. zstep.
      eapply (padloop (Z.to_nat (n - o)) o q); try reflexivity; try exact I0; try exact Hp; try lia; try exact Hov.
  Qed.

  Definition HEADP (k : nat) : Prop :=
    forall i o pre ov r m1 ob x7 x10 x15 x28 x29 x30,
      (length tb - i = k)%nat ->
      INV m1 ob -> 0 <= o <= n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
      In (b8 0) (skipn i tb) ->
      x10 = Z_to_bv 64 (Z.of_nat i) -> x15 = Z_to_bv 64 o -> x28 = Z_to_bv 64 0 ->
      ov = pre ++ fst (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      r = Z.of_nat i + snd (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra sp gp tp (Z_to_bv 64 49) (Z_to_bv 64 57) x7 s0 s1 x10 a1 a2 a0 (Z_to_bv 64 NOT) x15
                 (Z_to_bv 64 (TX + 1)) (Z_to_bv 64 46) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x15d9c) fc None m1 (seg_rom rsegs)).

  (** The end of an iteration at 0x15e04, after the store: advance i by d and o by one. *)
  Lemma tail : forall k, (forall k', (k' < k)%nat -> HEADP k') ->
    forall i o pre ov r m1 ob d x7 x28 x29 x30,
      (length tb - i = k)%nat -> (1 <= d <= 2)%nat ->
      INV m1 ob -> 0 <= o < n -> length pre = Z.to_nat (o + 1) -> firstn (Z.to_nat (o + 1)) ob = bz pre ->
      In (b8 0) (skipn (i + d) tb) -> x7 = Z_to_bv 64 (Z.of_nat d) ->
      ov = pre ++ fst (scr_lib (zb (skipn (i + d) tb)) (Z.to_nat (n - (o + 1)))) ->
      r = Z.of_nat (i + d) + snd (scr_lib (zb (skipn (i + d) tb)) (Z.to_nat (n - (o + 1)))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra sp gp tp (Z_to_bv 64 49) (Z_to_bv 64 57) x7 s0 s1 (Z_to_bv 64 (Z.of_nat i)) a1 a2 a0
                 (Z_to_bv 64 NOT) (Z_to_bv 64 o) (Z_to_bv 64 (TX + 1)) (Z_to_bv 64 46)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x15e04) fc None m1 (seg_rom rsegs)).
  Proof.
    intros k IH i o pre ov r m1 ob d x7 x28 x29 x30 Hk Hd I Ho Hl Hp HZ -> Hov Hr.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ TBi) as TBB.
    assert (Hlt : (i + d < length tb)%nat) by (eapply In_skipn_lt; exact HZ).
    zstep. zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - pose proof (IH (length tb - (i + d))%nat ltac:(lia)) as IH'. unfold HEADP in IH'.
      eapply (IH' (i + d)%nat (o + 1) pre); try reflexivity; try exact I0; try exact Hp; try exact HZ; try lia;
        try exact Hov; try exact Hr.
      + f_equal. lia.
      + rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
    - exfalso. rewrite ?unsigned_lit in K by lia. lia.
  Qed.

  (** The store of byte v at out[o] after o < n: the new memory has INV and out's prefix grows by v. *)
  Ltac store_out m1 ob o pre v I0 Ho Hl Hp :=
    let I2 := fresh "I2" in let Hp2 := fresh "Hp2" in let m2 := fresh "m2" in
    pose proof (inv_store m1 ob o (Z_to_bv 8 v) I0 Ho) as I2; unfold wa in I2;
    set (m2 := write_to_mem m1 (Z_to_bv 64 (bv_unsigned a1 + o)) [Z_to_bv 8 v]) in *; clearbody m2;
    pose proof (Hp_snoc ob o (Z_to_bv 8 v) (bz pre) ltac:(destruct I0 as (_ & _ & LEN0 & _); lia) ltac:(lia) Hp) as Hp2;
    replace (bz pre ++ [Z_to_bv 8 v]) with (bz (pre ++ [v])) in Hp2 by (unfold bz; rewrite map_app; reflexivity).

  (** The path at 0x15de8 for a byte that does not start a '.' + digit pair: the byte below 0x80, else '?'. *)
  Lemma other : forall k, (forall k', (k' < k)%nat -> HEADP k') ->
    forall i o pre ov r m1 ob b x7 x28 x29 x30,
      (length tb - i = k)%nat ->
      INV m1 ob -> 0 <= o < n -> length pre = Z.to_nat o -> firstn (Z.to_nat o) ob = bz pre ->
      In (b8 0) (skipn (i + 1) tb) ->
      scr_lib (zb (skipn i tb)) (Z.to_nat (n - o)) =
        ((if bv_unsigned b <? 0x80 then bv_unsigned b else 0x3f)
           :: fst (scr_lib (zb (skipn (i + 1) tb)) (Z.to_nat (n - (o + 1)))),
         snd (scr_lib (zb (skipn (i + 1) tb)) (Z.to_nat (n - (o + 1)))) + 1) ->
      x7 = zxb b ->
      ov = pre ++ fst (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      r = Z.of_nat i + snd (scr_lib (zb (skipn i tb)) (Z.to_nat (n - o))) ->
      evt rsegs (POSTv ov r)
        (MS (mkR ra sp gp tp (Z_to_bv 64 49) (Z_to_bv 64 57) x7 s0 s1 (Z_to_bv 64 (Z.of_nat i)) a1 a2 a0
                 (Z_to_bv 64 NOT) (Z_to_bv 64 o) (Z_to_bv 64 (TX + 1)) (Z_to_bv 64 46)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
            F (Z_to_bv 64 0x15de8) fc None m1 (seg_rom rsegs)).
  Proof.
    intros k IH i o pre ov r m1 ob b x7 x28 x29 x30 Hk I Ho Hl Hp HZ SPEC -> Hov Hr.
    rewrite SPEC in Hov, Hr. cbn [fst snd] in Hov, Hr. clear SPEC.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & MI & MU & WM).
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1.
    pose proof (byte_range b) as Rb.
    pose proof (out_store_ok m1 ob o I0 Ho) as HS.
    zstep. if_cases K; zify_cond K; [rewrite ?unsigned_lit in K by lia; exfalso; lia|].
    zstep. zstep. rewrite lts_shl56.
    destruct (Z.leb_spec 128 (bv_unsigned b)) as [Hhi|Hlo]; cbn [negb].
    - rewrite (proj2 (Z.ltb_ge _ _) Hhi) in Hov.
      zstep. zstep. zstep. rewrite (le1_lit 63).
      store_out m1 ob o pre 63 I0 Ho Hl Hp.
      zstep.
      eapply (tail k IH i o (pre ++ [63]) ov r _ _ 1%nat); try reflexivity; try exact I2; try exact Hp2; try exact HZ; try lia.
      all: first [ rewrite length_app; cbn; lia | rewrite Hov, <- app_assoc; reflexivity | rewrite Hr; lia ].
    - rewrite (proj2 (Z.ltb_lt _ _) Hlo) in Hov.
      zstep. zstep. rewrite (le1_lit (bv_unsigned b)).
      store_out m1 ob o pre (bv_unsigned b) I0 Ho Hl Hp.
      zstep.
      eapply (tail k IH i o (pre ++ [bv_unsigned b]) ov r _ _ 1%nat); try reflexivity; try exact I2; try exact Hp2;
        try exact HZ; try lia.
      all: first [ rewrite length_app; cbn; lia | rewrite Hov, <- app_assoc; reflexivity | rewrite Hr; lia ].
  Qed.

  Lemma head : forall k, HEADP k.
  Proof.
    intros k. induction k as [k IH] using lt_wf_ind. unfold HEADP.
    intros i o pre ov r m1 ob x7 x10 x15 x28 x29 x30 Hk I Ho Hl Hp HZ -> -> -> Hov Hr.
    pose proof I as I0. destruct I as (TBi & OUTi & LEN & MI & MU & WM).
    pose proof (bytes_at_bound _ _ _ _ TBi) as TBB.
    pose proof (u8arr_bound _ _ _ _ OUTi) as OB. rewrite LEN in OB.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. pose proof (bv_unsigned_in_range 64 a2) as Ra2.
    assert (Hi : (i < length tb)%nat) by (eapply In_skipn_lt; exact HZ).
    set (b := nth i tb (b8 0)).
    pose proof (nth_error_nth' tb i (b8 0) Hi) as Eb. fold b in Eb.
    pose proof (byte_range b) as Rb.
    pose proof (text_read m1 ob i b I0 Eb) as HR.
    assert (SK0 : zb (skipn i tb) = bv_unsigned b :: zb (skipn (S i) tb)).
    { rewrite (skipn_nth_cons tb i (b8 0) Hi). reflexivity. }
    zstep. zstep. zstep. if_cases K; zify_cond K; rewrite ?u_zxb in K.
    - (* the terminator: pad *)
      rewrite SK0, K, scr_zero in Hov, Hr. cbn [fst snd] in Hov, Hr.
      eapply (pad o pre); try exact I0; try exact Hp; try reflexivity; try lia; try exact Hov.
      rewrite Hr. f_equal. lia.
    - zstep. if_cases K2; zify_cond K2; rewrite ?HA2 in K2.
      + (* o = n: nothing more to write *)
        assert (o = n) by lia. subst o.
        replace (Z.to_nat (n - n)) with 0%nat in Hov, Hr by lia. rewrite scr_lib_0 in Hov, Hr. cbn [fst snd] in Hov, Hr.
        eapply (pad n pre); try exact I0; try exact Hp; try reflexivity; try lia.
        * rewrite Hr. f_equal. lia.
        * rewrite Hov. replace (Z.to_nat (n - n)) with 0%nat by lia. reflexivity.
      + assert (HZ1 : In (b8 0) (skipn (S i) tb)).
        { rewrite (skipn_nth_cons tb i (b8 0) Hi) in HZ. fold b in HZ. destruct HZ as [H0|H0]; [|exact H0].
          exfalso. apply K. rewrite H0. reflexivity. }
        assert (Hi1 : (S i < length tb)%nat) by (eapply In_skipn_lt; exact HZ1).
        set (b2 := nth (S i) tb (b8 0)).
        pose proof (nth_error_nth' tb (S i) (b8 0) Hi1) as E2. fold b2 in E2.
        pose proof (byte_range b2) as Rb2.
        assert (SK1 : zb (skipn (i + 1) tb) = bv_unsigned b2 :: zb (skipn (i + 2) tb)).
        { replace (i + 1)%nat with (S i) by lia. rewrite (skipn_nth_cons tb (S i) (b8 0) Hi1). fold b2.
          replace (i + 2)%nat with (S (S i)) by lia. reflexivity. }
        assert (SK : zb (skipn i tb) = bv_unsigned b :: bv_unsigned b2 :: zb (skipn (i + 2) tb)).
        { rewrite SK0, <- SK1. f_equal. f_equal. f_equal. lia. }
        assert (KN : Z.to_nat (n - o) = S (Z.to_nat (n - (o + 1)))) by lia.
        pose proof (scr_step (bv_unsigned b) (bv_unsigned b2) (zb (skipn (i + 2) tb)) (Z.to_nat (n - (o + 1))) K) as STEP.
        rewrite <- SK, <- KN, <- SK1 in STEP.
        assert (Ho' : 0 <= o < n) by lia.
        pose proof (out_store_ok m1 ob o I0 Ho') as HS.
        zstep. zstep. if_false.
        zstep. if_cases K4; zify_cond K4; rewrite ?unsigned_lit in K4 by lia.
        * (* the byte is not '.' *)
          rewrite (proj2 (Z.eqb_neq _ _) K4) in STEP. cbn [andb] in STEP.
          eapply (other k IH i o pre ov r m1 ob b); try reflexivity; try eassumption; try lia.
          all: replace (i + 1)%nat with (S i) by lia; exact HZ1.
        * (* '.': look at the next byte *)
          rewrite (proj2 (Z.eqb_eq _ _) K4) in STEP. cbn [andb] in STEP.
          pose proof (text_read m1 ob (S i) b2 I0 E2) as HR2.
          zstep. zstep. if_cases K5; zify_cond K5; [exfalso; rewrite ?unsigned_lit in K5 by lia; lia|].
          zstep. zstep. if_cases K6; zify_cond K6; rewrite ?unsigned_lit in K6 by lia.
          -- (* below '1' *)
             rewrite (proj2 (Z.leb_gt _ _) K6) in STEP. cbn [andb] in STEP.
             eapply (other k IH i o pre ov r m1 ob b); try reflexivity; try eassumption; try lia.
             all: replace (i + 1)%nat with (S i) by lia; exact HZ1.
          -- zstep. if_cases K7; zify_cond K7; [exfalso; rewrite ?unsigned_lit in K7 by lia; lia|].
             zstep. if_cases K8; zify_cond K8; rewrite ?unsigned_lit in K8 by lia.
             ++ (* above '9' *)
                rewrite (proj2 (Z.leb_le 49 (bv_unsigned b2)) ltac:(lia)), (proj2 (Z.leb_gt _ _) K8) in STEP. cbn [andb] in STEP.
                eapply (other k IH i o pre ov r m1 ob b); try reflexivity; try eassumption; try lia.
                all: replace (i + 1)%nat with (S i) by lia; exact HZ1.
             ++ (* '.' and a digit 1..9 *)
                rewrite (proj2 (Z.leb_le 49 (bv_unsigned b2)) ltac:(lia)), (proj2 (Z.leb_le (bv_unsigned b2) 57) ltac:(lia)) in STEP.
                cbn [andb] in STEP. rewrite STEP in Hov, Hr. cbn [fst snd] in Hov, Hr.
                assert (HZ2 : In (b8 0) (skipn (i + 2) tb)).
                { rewrite (skipn_nth_cons tb (S i) (b8 0) Hi1) in HZ1. fold b2 in HZ1.
                  destruct HZ1 as [H0|H0].
                  - exfalso. rewrite H0 in K6. change (bv_unsigned (b8 0)) with 0 in K6. lia.
                  - replace (i + 2)%nat with (S (S i)) by lia. exact H0. }
                zstep. if_cases K9; zify_cond K9; [exfalso; rewrite ?unsigned_lit in K9 by lia; lia|].
                zstep. zstep. zstep. rewrite (le1_lit (bv_unsigned b2 + -26)).
                store_out m1 ob o pre (bv_unsigned b2 + -26) I0 Ho' Hl Hp.
                zstep. zstep.
                eapply (tail k IH i o (pre ++ [bv_unsigned b2 + -26]) ov r _ _ 2%nat); try reflexivity; try exact I2;
                  try exact Hp2; try exact HZ2; try lia.
                all: first [ rewrite length_app; cbn; lia | rewrite Hov, <- app_assoc; reflexivity | rewrite Hr; lia ].
  Qed.

  (** The entry at 0x15d70: the NULL tests and the loop's registers. *)
  Lemma entry : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 : word) (oj : list byte),
    bytes_at rsegs m TX tb -> rw_cells rsegs m OX [CB (Z.to_nat n) oj] -> mem_inv rsegs m ->
    evt rsegs (POSTv (fst (scribble_text_spec (zb tb) n)) (snd (scribble_text_spec (zb tb) n)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x15d70) fc None m (seg_rom rsegs)).
  Proof.
    intros t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 oj TB OUT MI.
    unfold scribble_text_spec.
    pose proof (munch_refl [(OX, OX + n)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2.
    assert (LEN : length oj = Z.to_nat n) by (destruct OUT as [[[Hw _] _] _]; exact Hw).
    apply u8arr_of_rw_cells in OUT.
    assert (I : INV m oj) by (unfold INV; split; [exact TB|]; split; [exact OUT|]; split; [exact LEN|];
                              split; [exact MI|]; split; [exact MU|exact WM]).
    zstep. if_cases K; zify_cond K; [exfalso; lia|].
    zstep. zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite ZBridge.zb_lxor_ones by (change (bv_modulus 64) with (2 ^ 64) in Ra1; lia).
    eapply (head (length tb - 0) 0%nat 0 []); try exact I; try reflexivity; try lia.
    - cbn [skipn]. exact HTZ.
    - cbn [skipn app]. replace (n - 0) with n by lia. reflexivity.
    - cbn [skipn]. replace (n - 0) with n by lia. reflexivity.
  Qed.

End Walk.

Theorem diginet_scribble_text_holds : diginet_scribble_text_contract.
Proof.
  unfold diginet_scribble_text_contract, DIGINET_SCRIBBLE_TEXT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m n tb oj PRE.
  unfold diginet_scribble_text_pre in PRE.
  destruct PRE as (A0 & [TB TZ] & A1 & A2 & OUT & DJ & MI).
  eapply entry; eassumption.
Qed.
