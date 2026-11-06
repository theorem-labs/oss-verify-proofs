From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_next_lib rd_u32_c rd32f_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import USegR.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PWalk.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* Segment W of the fuzz_pcap ubsan slot (entry_fn 0x12c4c): from the walk's end (K5, 0x1304c) through the
   end loop 0x13114-0x1319c (the incl field read by check_1 = rd32 at 0x131a8) to the call of
   pcap_source_close (0x13600, ra 0x1306c). The file F is at b, its length n = flen F at 0x2eca0, c0 at sp_h,
   the sw cell at sp_h + 56; the chain model is the plain one (pcap_source_struct_next, PWalkDef, PWalk). *)

(* The 4 bytes F[k .. k+3] at b + k. *)
Lemma bytes_at_sub4 : forall m b (F : list byte) k, bytes_at rsegs m b F -> 0 <= k -> k + 4 <= flen F ->
  bytes_at rsegs m (b + k)
    [nth (Z.to_nat k) F (Z_to_bv 8 0); nth (Z.to_nat (k + 1)) F (Z_to_bv 8 0);
     nth (Z.to_nat (k + 2)) F (Z_to_bv 8 0); nth (Z.to_nat (k + 3)) F (Z_to_bv 8 0)].
Proof.
  intros m b F k (Hb & Hl & Hr) Hk HK. unfold flen in HK.
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  replace (b + k + Z.of_nat i) with (b + Z.of_nat (Z.to_nat k + i)) by lia.
  rewrite Hr by lia.
  rewrite (nth_error_nth' F (Z_to_bv 8 0)) by lia.
  destruct i as [|[|[|[|i]]]]; cbn [nth_error]; try lia; f_equal; f_equal; lia.
Qed.

(* check_1's value on the record's incl field F[e+8 .. e+11] with the sw cell swz is incl. *)
Lemma rd_val_incl : forall (F : list byte) sw e swz, (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  rd_val (Z_to_bv 64 swz) (nth (Z.to_nat (e + 8)) F (Z_to_bv 8 0)) (nth (Z.to_nat (e + 8 + 1)) F (Z_to_bv 8 0))
    (nth (Z.to_nat (e + 8 + 2)) F (Z_to_bv 8 0)) (nth (Z.to_nat (e + 8 + 3)) F (Z_to_bv 8 0)) = incl sw F e.
Proof. intros F sw e swz HS ->. destruct HS as [-> | ->]; reflexivity. Qed.

Lemma lor_ones64 : forall x, 0 <= x < 2 ^ 64 -> Z.lor (Z.ones 64) x = Z.ones 64.
Proof.
  intros x Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [L|L].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    pose proof (proj1 (Z.log2_lt_pow2 x 64 ltac:(lia)) ltac:(lia)). lia.
Qed.

Ltac ret_lit :=
  lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
    replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Ltac l_done := apply evt_done; do 9 eexists; reflexivity.

(* The end loop from its head 0x1311c at record e of the skips chain to Q: it leaves at 0x13060 with
   s6 = want_of Q; N bounds the number of records left. *)
Lemma ubs_W_loop : forall (N : nat) (F : list byte) (sw : bool) (e Q cap c0 b swz sp_h : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  rd32f_contract ->
  (Z.to_nat (flen F - e) < N)%nat -> skips sw F cap e Q ->
  bv_unsigned sp = sp_h -> s9 = wz e -> 0 <= e < flen F -> flen F < 2 ^ 26 -> a0 = wz (flen F) ->
  s2 = wz 1 -> s3 = wz (-9) ->
  s0 = wz b -> b <> 0 -> b + flen F < 2 ^ 63 -> bytes_at rsegs m b F ->
  s1 = wz cap -> cap = 8 * c0 -> 0 <= c0 < 256 -> bytes_at rsegs m sp_h (le8 (wz c0)) ->
  s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) -> bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (flen F))) ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
  evt rsegs
    (fun ms' => exists (ra' a0' a1' a2' a3' a4' a5' s4' s9' : word),
       ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4' s5
                     (wz (want_of sw F cap Q)) s7 s8 s9' s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x414)%Z)) fc None m
                (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x4d0)%Z)) fc None m (seg_rom rsegs)).
Proof.
  induction N as [|N IH];
    intros F sw e Q cap c0 b swz sp_h ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
      s10 s11 t3 t4 t5 t6 FR fc m RD HN HS HSP ES9 HE H26 EA0 ES2 ES3 ES0 HB0 HBN HF ES1 HC HC0 HCB ES10 HFL
      HSWB HSW ESW; [lia|].
  subst s9 a0 s2 s3 s0 s1 s10 sp_h.
  pose proof (bytes_at_ov8 _ _ _ HFL) as RFL.
  assert (RC : ov_read_bytes rsegs m sp 8 = Some (le8 (wz c0)))
    by (rewrite <- (bytes_at_ov8 _ _ _ HCB); f_equal; unfold wa; symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (bytes_at_ov4 _ _ _ HSWB) as RSW.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as HFB. change (Z.of_nat (length F)) with (flen F) in HFB.
  pose proof (bytes_at_bound rsegs _ _ _ HSWB) as HSPB. rewrite length_le4 in HSPB.
  unfold wz in *.
  assert (E1 : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  assert (E2 : bv_unsigned (Z_to_bv 64 (flen F)) = flen F) by (apply unsigned_lit; lia).
  assert (E3 : bv_unsigned (Z_to_bv 64 (e + 16)) = e + 16) by (apply unsigned_lit; lia).
  assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 cap) = cap) by (apply unsigned_lit; lia).
  assert (ECZ : bv_unsigned (Z_to_bv 64 c0) = c0) by (apply unsigned_lit; lia).
  assert (EEB : bv_unsigned (Z_to_bv 64 (e + b)) = e + b) by (apply unsigned_lit; lia).
  step. rewrite ?E1. step. step.
  destruct (Z_lt_le_dec (flen F) (e + 16)) as [C1|C1].
  { assert (K : kind sw F cap e = KCutH) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. if_true. replace (want_of sw F cap e) with (-1) by (unfold want_of; rewrite K; reflexivity).
    l_done. }
  if_false. step. rewrite ?E1, ?EB. step. if_false. step. step.
  rep_reg 11 (Z_to_bv 64 1)
    ltac:(unfold v_sltiu; rewrite EEB; change (bv_wrap 64 1) with 1; rewrite (proj2 (Z.ltb_ge _ _)) by lia;
          reflexivity).
  step. if_false. step. if_false. step. if_false.
  step. rep_reg 11 (Z_to_bv 64 swz) ltac:(destruct HSW as [-> | ->]; reflexivity).
  step. step.
  rep_reg 10 (Z_to_bv 64 (b + (e + 8))) ltac:(f_equal; lia).
  unfold rd32f_contract, RD32F in RD.
  eapply evt_cut.
  { eapply RD; rewrite unsigned_lit by lia; [lia | exact (bytes_at_sub4 m b F (e + 8) HF ltac:(lia) ltac:(lia))]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & ->).
  rewrite (rd_val_incl F sw e swz HSW ESW). ret_lit. unfold wz.
  pose proof (pw_hw_range sw F e 8) as RI. change (hw sw F e 8) with (incl sw F e) in RI.
  step.
  destruct (Z.eq_dec (incl sw F e) 0) as [I0|I0].
  { (* KEmpty: go on at e + 16 *)
    assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl sw F e))) (Z_to_bv 64 0) = true)
      by (rewrite eqb_swrap0 by lia; apply Z.eqb_eq; exact I0).
    rewrite C; cbv iota.
    assert (K : kind sw F cap e = KEmpty) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_empty_inv sw F cap e Q HS K) as HS'.
    step. step. step.
    destruct (Z.eq_dec (e + 16) (flen F)) as [C2|C2].
    - assert (K2 : kind sw F cap (e + 16) = KEnd) by (unfold kind; rewrite C2, Z.sub_diag; reflexivity).
      pose proof (skips_exit sw F cap (e + 16) Q HS' ltac:(rewrite K2; discriminate)
                    ltac:(rewrite K2; discriminate)) as EQ.
      subst Q. replace (want_of sw F cap (e + 16)) with 0 by (unfold want_of; rewrite K2; reflexivity).
      if_false. step. step. l_done.
    - if_true. eapply (IH F sw (e + 16) Q cap c0 b swz (bv_unsigned sp)); try reflexivity; try eassumption; lia. }
  assert (C : bv_eqb (Z_to_bv 64 (bv_swrap 32 (incl sw F e))) (Z_to_bv 64 0) = false)
    by (rewrite eqb_swrap0 by lia; apply Z.eqb_neq; exact I0).
  rewrite C; cbv iota.
  step. step. rewrite zx32_val, uns_swrap_mod32_0 by lia.
  assert (EI : bv_unsigned (Z_to_bv 64 (incl sw F e)) = incl sw F e) by (apply unsigned_lit; lia).
  assert (E4 : bv_unsigned (Z_to_bv 64 (e + 16 + incl sw F e)) = e + 16 + incl sw F e) by (apply unsigned_lit; lia).
  step.
  destruct (Z_le_gt_dec (incl sw F e) cap) as [CI|CI].
  { (* incl <= cap: KFit or KCutFit *)
    if_true. step. step. rewrite ?E3, ?EI. step. step. step. step.
    destruct (Z_le_gt_dec (e + 16 + incl sw F e) (flen F)) as [CF|CF].
    - assert (K : kind sw F cap e = KFit) by (unfold kind; bool_dec; reflexivity).
      pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
      subst Q. replace (want_of sw F cap e) with (incl sw F e) by (unfold want_of; rewrite K; reflexivity).
      assert (SL : v_sltu (Z_to_bv 64 (flen F)) (Z_to_bv 64 (e + 16 + incl sw F e)) = Z_to_bv 64 0)
        by (unfold v_sltu, c_ltu, bv_ltu; rewrite E2, E4; rewrite (proj2 (Z.ltb_ge _ _)) by lia; reflexivity).
      rewrite SL, EI.
      rep_reg 22 (Z_to_bv 64 (incl sw F e))
        ltac:(change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 0)))) with 0; rewrite Z.lor_0_l;
              reflexivity).
      l_done.
    - assert (K : kind sw F cap e = KCutFit) by (unfold kind; bool_dec; reflexivity).
      pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
      subst Q. replace (want_of sw F cap e) with (-1) by (unfold want_of; rewrite K; reflexivity).
      assert (SL : v_sltu (Z_to_bv 64 (flen F)) (Z_to_bv 64 (e + 16 + incl sw F e)) = Z_to_bv 64 1)
        by (unfold v_sltu, c_ltu, bv_ltu; rewrite E2, E4; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
      rewrite SL, EI.
      rep_reg 22 (Z_to_bv 64 (-1))
        ltac:(apply Z_to_bv_eqm; change (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 1)))) with (Z.ones 64);
              rewrite lor_ones64 by lia; reflexivity).
      l_done. }
  (* incl > cap *)
  if_false. step. step.
  destruct (Z.eq_dec c0 0) as [D0|D0].
  { assert (K : kind sw F cap e = KBig0) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. replace (want_of sw F cap e) with (-1) by (unfold want_of; rewrite K; reflexivity).
    if_true. l_done. }
  if_false. step. step. rewrite ?E3, ?EI. step.
  destruct (Z_lt_le_dec (flen F) (e + 16 + incl sw F e)) as [CB|CB].
  { assert (K : kind sw F cap e = KCutBig) by (unfold kind; bool_dec; reflexivity).
    pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. replace (want_of sw F cap e) with (-1) by (unfold want_of; rewrite K; reflexivity).
    if_true. l_done. }
  (* KBig: go on after the record *)
  assert (K : kind sw F cap e = KBig) by (unfold kind; bool_dec; reflexivity).
  pose proof (skips_big_inv sw F cap e Q HS K) as HS'.
  if_false. step. step. step.
  destruct (Z.eq_dec (e + 16 + incl sw F e) (flen F)) as [C2|C2].
  { assert (K2 : kind sw F cap (e + 16 + incl sw F e) = KEnd) by (unfold kind; rewrite C2, Z.sub_diag; reflexivity).
    pose proof (skips_exit sw F cap _ Q HS' ltac:(rewrite K2; discriminate) ltac:(rewrite K2; discriminate)) as EQ.
    subst Q. replace (want_of sw F cap (e + 16 + incl sw F e)) with 0 by (unfold want_of; rewrite K2; reflexivity).
    if_false. step. step. l_done. }
  if_true. eapply (IH F sw (e + 16 + incl sw F e) Q cap c0 b swz (bv_unsigned sp)); try reflexivity; try eassumption;
    lia.
Qed.

(* Segment W, from K5 (0x1304c: s5 = the walk's last answer a, s9 = the file position e after the walk) to the
   call of pcap_source_close (0x13600, ra 0x1306c). The first record Q of the skips chain from e is not a fit,
   so a = want_of Q is 0 or -1 and the test a >= -1 (0x13050) holds; the end loop computes want_of Q
   (0 at once when e = n), so the test a = want (0x13060) holds: no branch to 0x131a0 or 0x131a4. *)
Lemma ubs_W_x :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (F : list byte) (sw : bool)
         (sp_h a e Q cap c0 b swz : Z),
    rd32f_contract ->
    bv_unsigned sp = sp_h ->
    s5 = wz a -> a = want_of sw F cap Q -> kind sw F cap Q <> KFit ->
    s9 = wz e -> 0 <= e <= flen F -> skips sw F cap e Q ->
    s0 = wz b -> b <> 0 -> b + flen F < 2 ^ 63 -> bytes_at rsegs m b F ->
    s1 = wz cap -> cap = 8 * c0 -> 0 <= c0 < 256 -> bytes_at rsegs m sp_h (le8 (wz c0)) ->
    s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) -> bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (flen F))) ->
    bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) -> (swz = 0 \/ swz = 1) -> sw = (swz =? 1) ->
    flen F < 2 ^ 26 ->
    evt rsegs
      (fun ms' => exists (a1' a2' a3' a4' a5' s2' s3' s4' s9' : word),
         ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) sp gp tp t0 t1 t2 s0 s1 (wz (sp_h + 48)) a1' a2' a3' a4' a5' a6 a7
                       s2' s3' s4' s5 (wz a) s7 s8 s9' s10 s11 t3 t4 t5 t6) FR (Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close)) fc None m
                  (seg_rom rsegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    FR fc m F sw sp_h a e Q cap c0 b swz RD HSP ES5 EA KQ ES9 HE HS ES0 HB0 HBN HF ES1 HC HC0 HCB ES10 HFL
    HSWB HSW ESW H26.
  subst sp_h s5 s9 s0 s1 s10.
  pose proof (bytes_at_ov8 _ _ _ HFL) as RFL.
  pose proof (bytes_at_bound rsegs _ _ _ HF) as HFB. change (Z.of_nat (length F)) with (flen F) in HFB.
  destruct (kind_nfit sw F cap Q KQ) as [EW HN]. rewrite EW, <- EA in HN.
  unfold wz in *.
  assert (C0 : bv_lts (Z_to_bv 64 a) (Z_to_bv 64 (-1)) = false) by (destruct HN as [-> | ->]; reflexivity).
  step. step. rewrite C0; cbv iota. clear C0.
  assert (EE : bv_unsigned (Z_to_bv 64 e) = e) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 (flen F)) = flen F) by (apply unsigned_lit; lia).
  step. step.
  destruct (Z.eq_dec e (flen F)) as [PE|PE].
  - assert (K : kind sw F cap e = KEnd) by (unfold kind; rewrite PE, Z.sub_diag; reflexivity).
    pose proof (skips_exit sw F cap e Q HS ltac:(rewrite K; discriminate) ltac:(rewrite K; discriminate)) as EQ.
    subst Q. assert (A0 : a = 0) by (rewrite EA; unfold want_of; rewrite K; reflexivity). clear EA. subst a.
    if_false. step. step. if_false. step. step.
    apply evt_done. do 9 eexists. reflexivity.
  - if_true. step.
    assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
    rep_reg 18 (Z_to_bv 64 1)
      ltac:(unfold v_sltu, c_ltu, bv_ltu; rewrite EB; change (bv_unsigned (Z_to_bv 64 0)) with 0;
            rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    step.
    eapply evt_cut.
    { eapply (ubs_W_loop (S (Z.to_nat (flen F - e))) F sw e Q cap c0 b swz (bv_unsigned sp));
        try reflexivity; try eassumption; lia. }
    intros ms' (ra' & a0' & a1' & a2' & a3' & a4' & a5' & s4' & s9' & ->).
    rewrite <- EA. unfold wz.
    step. if_false. step. step.
    apply evt_done. do 9 eexists. reflexivity.
Qed.
