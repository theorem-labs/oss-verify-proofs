(** check_csv of the UBSan image (0x14864, 436 bytes, 109 instructions) against U/Prog/check_csv_c.v, from
    bcmp_contract. The entry 0x14864 .. 0x148d4 makes the 144-byte frame, saves ra and s0-s9 and sets the loop's
    constants; then the three passes of the loop over closed_list (U/Prog/ccsv_pass.v), split on bits 0, 1 and 2 of
    the mask: after them want's first |L| bytes are csv_bytes L, L = csv_list mask, and t6 = |L|; then the tail
    (U/Prog/ccsv_tail.v): len = |L|, bcmp of buf and want over min(|L|, buflen - 1) bytes, buf's NUL, the return. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import RateCfg RateCsv.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import bcmp_c check_csv_c ccsv_lemmas ccsv_pass ccsv_tail.
Import ListNotations.
Open Scope Z_scope.

(** csv_list by the three bits of the mask. *)
Lemma ccsv_list3 : forall M, csv_list M =
  let p1 := if Z.testbit M 0 then CSV_44K1 else [] in
  let p2 := if Z.testbit M 1 then p1 ++ match p1 with [] => [] | _ :: _ => [44] end ++ CSV_48K else p1 in
  if Z.testbit M 2 then p2 ++ match p2 with [] => [] | _ :: _ => [44] end ++ CSV_96K else p2.
Proof. intros M. reflexivity. Qed.

(** One pass (lemma L of U/Prog/ccsv_pass.v) from hd_mem HM, bit equation B; HM' names the next head's hd_mem. *)
Ltac pass_to L lo m B HM HM' :=
  eapply (L _ _ lo m); [lia | lia | lia | exact B | exact HM |]; intros ? ? ? ? ? ? ? ? ? HM'.

(** After pass 2: the tail, with want's prefix P = csv_list mask (bits b0, b1, b2). *)
Ltac leaf BC P HM b0 b1 b2 :=
  eapply (ccsv_fin BC P);
  [ rewrite ccsv_list3; cbv zeta; rewrite b0, b1, b2; reflexivity
  | reflexivity | assumption | assumption | assumption | assumption | lia | lia | lia | exact HM ].

Theorem check_csv_holds : bcmp_contract -> check_csv_contract.
Proof.
  intros BC. unfold check_csv_contract, CHECK_CSV, CHECK_CSV_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  cbv zeta. intros HL Hn H0 Hpos Hdj ST HK HW MI.
  assert (Ea2 : a2 = Z_to_bv 64 (Z.of_nat (length (csv_list (bv_unsigned a3)))))
    by (rewrite <- HL; symmetry; apply Z_to_bv_lit_self).
  subst a2. clear HL HW.
  pose proof (Z_to_bv_lit_self sp) as Esp.
  set (Sp := bv_unsigned sp) in *. rewrite <- Esp. clearbody Sp. clear Esp.
  pose proof (proj1 ST) as Hlo. pose proof (proj1 (proj2 ST)) as Hhi.
  lazymatch goal with
  | |- evt _ _ ?ms => change (evt rsegs (ccsv_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Sp F fc m lo) ms)
  end.
  pose proof (munch_refl [(Sp + -144, Sp)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  carve_frame 144%nat ST.
  (* 0x14864 .. 0x148d4: frame, saves, s1 = len, s0 = buf, i = n = 0, the constants *)
  do 29 step.
  norm_lits.
  apply (rw_cells_split_CB rsegs _ _ [] 56 _ _ [8; 8; 40]%nat) in FR; [| reflexivity].
  cbn [app mk_CB_cells] in FR.
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM0 : hd_mem Sp lo m mm [] (ccsv_saves ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9))
        by (unfold hd_mem, ccsv_saves, wcells; cbn [app]; do 3 eexists;
            split; [exact FR | split; [exact ST | split; [exact MU | split; [exact WM | exact MI]]]])
  end.
  clear FR ST MU WM MI.
  (* the passes i = 0, 1, 2 *)
  destruct (Z.testbit (bv_unsigned a3) 0) eqn:B0.
  - pass_to ccsv_set0 lo m B0 HM0 HM1.
    destruct (Z.testbit (bv_unsigned a3) 1) eqn:B1.
    + pass_to ccsv_set1b lo m B1 HM1 HM2.
      destruct (Z.testbit (bv_unsigned a3) 2) eqn:B2.
      * pass_to ccsv_set2d lo m B2 HM2 HM3.
        leaf BC (CSV_44K1 ++ [44] ++ CSV_48K ++ [44] ++ CSV_96K) HM3 B0 B1 B2.
      * pass_to (ccsv_skip2 (CSV_44K1 ++ [44] ++ CSV_48K) 11) lo m B2 HM2 HM3.
        leaf BC (CSV_44K1 ++ [44] ++ CSV_48K) HM3 B0 B1 B2.
    + pass_to (ccsv_skip1 CSV_44K1 5) lo m B1 HM1 HM2.
      destruct (Z.testbit (bv_unsigned a3) 2) eqn:B2.
      * pass_to ccsv_set2b lo m B2 HM2 HM3.
        leaf BC (CSV_44K1 ++ [44] ++ CSV_96K) HM3 B0 B1 B2.
      * pass_to (ccsv_skip2 CSV_44K1 5) lo m B2 HM2 HM3.
        leaf BC CSV_44K1 HM3 B0 B1 B2.
  - pass_to (ccsv_skip0 [] 0) lo m B0 HM0 HM1.
    destruct (Z.testbit (bv_unsigned a3) 1) eqn:B1.
    + pass_to ccsv_set1a lo m B1 HM1 HM2.
      destruct (Z.testbit (bv_unsigned a3) 2) eqn:B2.
      * pass_to ccsv_set2c lo m B2 HM2 HM3.
        leaf BC (CSV_48K ++ [44] ++ CSV_96K) HM3 B0 B1 B2.
      * pass_to (ccsv_skip2 CSV_48K 5) lo m B2 HM2 HM3.
        leaf BC CSV_48K HM3 B0 B1 B2.
    + pass_to (ccsv_skip1 [] 0) lo m B1 HM1 HM2.
      destruct (Z.testbit (bv_unsigned a3) 2) eqn:B2.
      * pass_to ccsv_set2a lo m B2 HM2 HM3.
        leaf BC CSV_96K HM3 B0 B1 B2.
      * pass_to (ccsv_skip2 [] 0) lo m B2 HM2 HM3.
        leaf BC (@nil Z) HM3 B0 B1 B2.
Qed.
