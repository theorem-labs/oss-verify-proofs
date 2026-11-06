From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require StrFun.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.U.Prog Require Import codec_cells
  check_personality_c codec_main_inv codec_main_lib.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(** Eight bytes read as the little-endian word they spell. *)
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat ->
  le8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. rewrite <- store_bytes_8'. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 (bytes_le_to_Z bs)) with (bytes_le_to_Z bs mod 2 ^ 64).
  rewrite (Z_to_le_bytes_mod 8 (bytes_le_to_Z bs) 64) by (change (Z.of_nat 8) with 8; lia).
  pose proof (StrFun.Z_to_le_bytes_to_Z bs) as H. rewrite Hl in H. exact H.
Qed.

(** The frame at 0x13368 as the prologue and the setup leave it: the three spilled constants, the
    data pointer at sp - 200, and the rest still the caller's bytes, cut into the regions of [fr]. *)
Lemma entry_frame : forall E m1 (a b z : list byte) (cur : word),
  rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416)
    ([CB 8 a; C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff); CB 184 b; C8 cur;
      CB 88 z] ++ saved E) ->
  exists kc nl u0 pj tj plj, fr E m1 kc cur nl u0 pj tj plj.
Proof.
  intros E m1 a b z cur H.
  change (rw_cells rsegs m1 (bv_unsigned (c_sp E) + -416)
    ([CB 8 a] ++ [C8 (Z_to_bv 64 0x990); C8 (Z_to_bv 64 0x5cb0); C8 (Z_to_bv 64 0xffff)] ++
     [CB 184 b] ++ [C8 cur] ++ [CB 88 z] ++ saved E)) in H.
  apply rw_cells_app_split in H. destruct H as [H0 H]. cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned (c_sp E) + -416 + Z.of_nat 8) with (bv_unsigned (c_sp E) + -408) in H by lia.
  apply rw_cells_app_split in H. destruct H as [H8 H]. cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned (c_sp E) + -408 + Z.of_nat 24) with (bv_unsigned (c_sp E) + -384) in H by lia.
  apply rw_cells_app_split in H. destruct H as [HK H]. cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned (c_sp E) + -384 + Z.of_nat 184) with (bv_unsigned (c_sp E) + -200) in H by lia.
  apply rw_cells_app_split in H. destruct H as [HC H]. cbn [cells_size csize Nat.add] in H.
  replace (bv_unsigned (c_sp E) + -200 + Z.of_nat 8) with (bv_unsigned (c_sp E) + -192) in H by lia.
  apply rw_cells_app_split in H. destruct H as [HZ HSV]. cbn [cells_size csize Nat.add] in HSV.
  replace (bv_unsigned (c_sp E) + -192 + Z.of_nat 88) with (bv_unsigned (c_sp E) + -104) in HSV by lia.
  assert (Lz : length z = 88%nat) by (pose proof HZ as [[[W _] _] _]; exact W).
  destruct (rw_cells_CB_split m1 _ 88 8 z Lz ltac:(lia) HZ) as [HNL HZ1].
  change (88 - 8)%nat with 80%nat in HZ1.
  replace (bv_unsigned (c_sp E) + -192 + Z.of_nat 8) with (bv_unsigned (c_sp E) + -184) in HZ1 by lia.
  assert (L1 : length (skipn 8 z) = 80%nat) by (rewrite length_skipn; lia).
  destruct (rw_cells_CB_split m1 _ 80 5 (skipn 8 z) L1 ltac:(lia) HZ1) as [HPD HZ2].
  change (80 - 5)%nat with 75%nat in HZ2.
  replace (bv_unsigned (c_sp E) + -184 + Z.of_nat 5) with (bv_unsigned (c_sp E) + -179) in HZ2 by lia.
  assert (L2 : length (skipn 5 (skipn 8 z)) = 75%nat) by (rewrite length_skipn; lia).
  destruct (rw_cells_CB_split m1 _ 75 65 (skipn 5 (skipn 8 z)) L2 ltac:(lia) HZ2) as [HTX HPL].
  change (75 - 65)%nat with 10%nat in HPL.
  replace (bv_unsigned (c_sp E) + -179 + Z.of_nat 65) with (bv_unsigned (c_sp E) + -114) in HPL by lia.
  assert (L8 : length (firstn 8 z) = 8%nat) by (rewrite length_firstn; lia).
  assert (HNL' : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -192)
                   [C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 z)))]).
  { apply (rw_cells_same_bytes m1 _ [CB 8 (firstn 8 z)]).
    - exact (conj I I).
    - cbn [cells_bytes cbytes]. rewrite le8_of_bytes by exact L8. reflexivity.
    - reflexivity.
    - exact HNL. }
  assert (HIN : rw_cells rsegs m1 (bv_unsigned (c_sp E) + -200)
                  ([C8 cur] ++ [C8 (Z_to_bv 64 (bytes_le_to_Z (firstn 8 z)))])).
  { apply rw_cells_app_join; [exact HC|]. cbn [cells_size csize Nat.add].
    replace (bv_unsigned (c_sp E) + -200 + Z.of_nat 8) with (bv_unsigned (c_sp E) + -192) by lia.
    exact HNL'. }
  exists [CB 184 b], (Z_to_bv 64 (bytes_le_to_Z (firstn 8 z))), a, (firstn 5 (skipn 8 z)),
    (firstn 65 (skipn 5 (skipn 8 z))), (skipn 65 (skipn 5 (skipn 8 z))).
  exact (conj eq_refl (conj H0 (conj H8 (conj HK (conj HIN (conj HPD (conj HTX (conj HPL HSV)))))))).
Qed.

(** 0x132b8-0x13364: the prologue, the return of fuzz_codec.c:564 when size >= 2^26, the
    check_personality call, the store of in.p, the return of :568 when size is 0, and the setup of
    the nine loop registers and the three spilled constants. *)
Lemma codec_main_entry : seg_entry_stmt.
Proof.
  unfold seg_entry_stmt.
  intros [ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p F fc m lo data] ENV CHK EXIT LOOP.
  cenv_cbn.
  pose proof ENV as ENV0.
  unfold env_ok in ENV. cenv_cbn.
  destruct ENV as (_ & HMI0 & ST0 & HLO & _ & _ & _ & _ & _ & DJR).
  unfold exit_ok in EXIT. unfold loop_ok in LOOP. cenv_cbn.
  unfold check_personality_contract, CHECK_PERSONALITY, CHECK_PERSONALITY_DEPTH in CHK.
  unfold entry_ok. cenv_cbn.
  intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HN.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Rsp, Ra1.
  pose proof ST0 as (Hlo0 & _).
  assert (U416 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -416)) = bv_unsigned sp + -416)
    by (apply u_frame; lia).
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?Fm ?pc ?fcv ?rv m ?ro) =>
      cut (forall m1, m1 = m -> evt sg Q (MS R Fm pc fcv rv m1 ro));
      [ intros G; exact (G m eq_refl) | intros m1 Em ]
  end.
  assert (MU : munch [(bv_unsigned sp - 640, bv_unsigned sp)] m m1) by (rewrite Em; apply munch_refl).
  assert (WM : wmono rsegs m m1) by (rewrite Em; apply wmono_refl).
  assert (HMI : mem_inv rsegs m1) by (rewrite Em; exact HMI0).
  assert (ST : stk rsegs m1 lo (bv_unsigned sp)) by (rewrite Em; exact ST0).
  clear Em HMI0 ST0.
  carve_frame 416%nat ST.
  (* 0x132b8-0x132f8: the frame, the 13 saves, s5 := size, a1 := size >> 26, beqz. *)
  do 17 zstep.
  if_cases EBIG.
  2: { (* 0x132fc: size >= 2^26, return 0. *)
       zstep.
       eapply EXIT with (cs := [CB 312 _]); [reflexivity | exact FR | exact ST | exact MU | exact WM | exact HMI]. }
  (* 0x13300-0x13304: s0 := data, check_personality(). *)
  zstep. zstep.
  call CHK.
  { unfold check_personality_pre, CHECK_PERSONALITY_DEPTH. rewrite U416.
    refine (conj (relro_at _ _ ENV0 MU) (conj _ (conj HMI (conj ST _)))); unfold disj in *; lia. }
  match goal with H : stk _ _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite U416 in H; rename H into ST2 end.
  match goal with H : mem_inv rsegs _ |- _ => rename H into HMI2 end.
  (* 0x13308-0x1330c: in.p := data, bnez size. *)
  zstep. zstep.
  if_cases G.
  2: { (* 0x13310: size = 0, return 0. *)
       zstep.
       eapply EXIT with (cs := [CB 216 _; C8 _; CB 88 _]);
         [reflexivity | exact FR | exact ST2 | exact MU | exact WM | exact HMI2]. }
  zify_cond G.
  (* 0x13314-0x13364: the loop registers and the three spilled constants. *)
  do 21 zstep.
  lazymatch type of ENV0 with
  | env_ok ?E => destruct (entry_frame E _ _ _ _ _ FR) as (kc & nl & u0 & pj & tj & plj & FRM)
  end.
  eapply LOOP with (cur := p) (nl := nl) (rem := a1) (kc := kc) (u0 := u0) (pj := pj) (tj := tj)
    (plj := plj) (c := 0) (ops := 0);
    [ lia | lia | lia | lia | lia | lia | exact FRM | exact ST2 | exact MU | exact WM | exact HMI2 ].
Qed.
