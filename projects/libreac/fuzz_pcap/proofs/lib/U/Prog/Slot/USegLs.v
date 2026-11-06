From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Cells Exec Frame Step Tac Bytes ZBridge Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel pcap_source_next_lib rd_u32_c rd32f_c bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require Import pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require Import PWalkDef PWalk.
Import ListNotations.
Open Scope Z_scope.

(* Helpers of the ubsan record loop (USegL.v) and its skip loop 0x12e78-0x12eb8 by induction on skips. *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

(* `not s4,s0` leaves the complement in the form of xori. *)
Lemma ul_not_word : forall x : word, Z_to_bv 64 (Z.lxor (bv_unsigned x) 18446744073709551615) = bv_not x.
Proof.
  intros x. pose proof (zr_word x) as R. unfold inr64 in R.
  apply bv_eq. rewrite bv_not_unsigned, Z_to_bv_unsigned. rewrite lnot_mod64 by exact R.
  change (bv_wrap 64 (Z.lnot (bv_unsigned x) mod 2 ^ 64)) with ((Z.lnot (bv_unsigned x) mod 2 ^ 64) mod 2 ^ 64).
  change (bv_wrap 64 (Z.lnot (bv_unsigned x))) with (Z.lnot (bv_unsigned x) mod 2 ^ 64).
  apply Zmod_mod.
Qed.

Lemma ul_not_uns : forall b, 0 <= b < 2 ^ 64 -> bv_unsigned (bv_not (Z_to_bv 64 b)) = 18446744073709551615 - b.
Proof.
  intros b Hb. rewrite <- ul_not_word. rewrite (unsigned_lit b) by lia. rewrite zb_lxor_ones by lia.
  apply unsigned_lit. lia.
Qed.

Lemma ul_sx32_01 : forall z, (z = 0 \/ z = 1) -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z [-> | ->]; reflexivity. Qed.

Lemma ul_sx32 : forall z, 0 <= z < 2 ^ 31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. rewrite swrap32_eq.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma ul_sx32_sw : forall z, 0 <= z < 2 ^ 64 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 (bv_swrap 32 z).
Proof. intros z Hz. unfold sx32. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma ul_ro : forall m A c, bytes_at rsegs m A (cbytes c) -> cell_wf c -> ro_cells rsegs m A [c].
Proof. intros m A c H W. split; [split; [exact W | exact I] |]. cbn [cells_bytes]. rewrite app_nil_r. exact H. Qed.

(* Pieces of the file copy. *)
Lemma ul_F4 : forall m b (Fc : list byte) j A, bytes_at rsegs m b Fc -> A = b + j -> 0 <= j ->
  j + 4 <= Z.of_nat (length Fc) ->
  bytes_at rsegs m A [nth (Z.to_nat j) Fc (Z_to_bv 8 0); nth (Z.to_nat (j + 1)) Fc (Z_to_bv 8 0);
                      nth (Z.to_nat (j + 2)) Fc (Z_to_bv 8 0); nth (Z.to_nat (j + 3)) Fc (Z_to_bv 8 0)].
Proof.
  intros m b Fc j A (H0 & H1 & H) -> Hj Hl. split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi.
  replace (b + j + Z.of_nat i) with (b + Z.of_nat (Z.to_nat j + i)) by lia. rewrite H by lia.
  rewrite (nth_error_nth' Fc (Z_to_bv 8 0)) by lia.
  destruct i as [|[|[|[|i]]]]; cbn [nth_error]; try lia; repeat f_equal; lia.
Qed.

Lemma ul_bytes_sub : forall m a bs (k n : nat) A, bytes_at rsegs m a bs -> A = a + Z.of_nat k ->
  (k + n <= length bs)%nat -> bytes_at rsegs m A (firstn n (skipn k bs)).
Proof.
  intros m a bs k n A H -> Hl. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn in H. replace (Nat.min k (length bs)) with k in H by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

(* The value of check_1 (rd32 at 0x131a8) on four bytes of the file copy is the chain model's hw. *)
Lemma ul_rd_hw : forall swz (Fc : list byte) q j, (swz = 0 \/ swz = 1) ->
  rd_val (Z_to_bv 64 swz) (nth (Z.to_nat (q + j)) Fc (Z_to_bv 8 0)) (nth (Z.to_nat (q + j + 1)) Fc (Z_to_bv 8 0))
    (nth (Z.to_nat (q + j + 2)) Fc (Z_to_bv 8 0)) (nth (Z.to_nat (q + j + 3)) Fc (Z_to_bv 8 0)) =
  hw (swz =? 1) Fc q j.
Proof.
  intros swz Fc q j [-> | ->].
  - unfold rd_val. change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
    change (0 =? 1) with false. unfold rd_le, hw, w32le, fb. reflexivity.
  - unfold rd_val. change (bv_eqb (Z_to_bv 64 1) (Z_to_bv 64 0)) with false. cbv iota.
    change (1 =? 1) with true. unfold rd_le, hw, w32le, fb. reflexivity.
Qed.

Lemma ul_rd32 : rd32f_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fc : list byte) (b swz q j : Z),
  a0 = Z_to_bv 64 (b + q + j) -> a1 = Z_to_bv 64 swz -> (swz = 0 \/ swz = 1) ->
  bytes_at rsegs m b Fc -> 0 <= q + j -> q + j + 4 <= Z.of_nat (length Fc) -> 0 < b ->
  evt rsegs
    (fun ms' => exists a1' a2' a3' a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (bv_swrap 32 (hw (swz =? 1) Fc q j))) a1' a2' a3' a4' a5'
                     a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr Symbols.Ubsan.s_rd32)) fc None m (seg_rom rsegs)).
Proof.
  intros RD ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m Fc b swz q j E0 E1 HSW HB Hq Hl Hb.
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB.
  subst a0 a1. unfold rd32f_contract, RD32F in RD.
  eapply evt_mono; [eapply RD | ].
  - rewrite unsigned_lit by lia. lia.
  - rewrite unsigned_lit by lia. apply (ul_F4 m b Fc (q + j) (b + q + j) HB); lia.
  - intros ms' (a1' & a2' & a3' & a4' & a5' & ->). exists a1', a2', a3', a4', a5'.
    unfold wz. rewrite ul_rd_hw by exact HSW. reflexivity.
Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Ltac rd_post := let ms' := fresh "ms'" in intros ms' (? & ? & ? & ? & ? & ->); fix_ret.

(* Branch conditions: literals folded, the other unsigned values unwrapped by lia from the context. *)
Ltac unwrap :=
  repeat match goal with
  | |- context [sx32 (Z_to_bv 64 ?z)] => rewrite (ul_sx32 z) by lia
  | |- context [bv_unsigned (bv_not (Z_to_bv 64 ?z))] => rewrite (ul_not_uns z) by lia
  | |- context [bv_unsigned (zxb ?c)] => rewrite (zxb_val c)
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (unsigned_lit z) by lia
  end.
Ltac uc := unfold_cond; fold_lit_ux; unwrap; solve_cond_rec.
Ltac ifc v :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with v; [cbv iota | symmetry; uc]
  end.

(* Facts of the record kinds the skip loop meets. *)
Ltac kind_inv H :=
  revert H; unfold kind, flen, incl;
  repeat match goal with
  | |- context [if (?x =? ?y) then _ else _] => destruct (Z.eqb_spec x y)
  | |- context [if (?x <? ?y) then _ else _] => destruct (Z.ltb_spec x y)
  | |- context [if (?x <=? ?y) then _ else _] => destruct (Z.leb_spec x y)
  end; let K := fresh "Hk" in intros K; cbv iota in K; try discriminate K.

Lemma ul_kind_empty : forall sw Fc cap q, kind sw Fc cap q = KEmpty ->
  16 <= Z.of_nat (length Fc) - q /\ incl sw Fc q = 0.
Proof. intros sw Fc cap q HK. pose proof (pw_hw_range sw Fc q 8) as R. unfold incl in *. kind_inv HK; lia. Qed.

Lemma ul_kind_big : forall sw Fc cap q, kind sw Fc cap q = KBig ->
  16 <= Z.of_nat (length Fc) - q /\ cap < incl sw Fc q /\ q + 16 + incl sw Fc q <= Z.of_nat (length Fc).
Proof. intros sw Fc cap q HK. pose proof (pw_hw_range sw Fc q 8) as R. unfold incl in *. kind_inv HK; lia. Qed.

(* The skip loop 0x12e78-0x12eb8 (fuzz/fuzz_pcap.c:151-161): it passes the records of kind KEmpty and KBig and
   stops at the record Q of kind KFit, where it jumps to 0x12ebc. *)
Lemma ubs_L_skip : forall (sw : bool) (Fc : list byte) (cap q Q : Z), rd32f_contract -> skips sw Fc cap q Q ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (sp_h b swz : Z),
  bv_unsigned sp = sp_h -> s9 = wz q -> s8 = wz (q + 16) -> s0 = wz b -> s1 = wz cap -> s2 = wz (-8) ->
  s4 = bv_not (wz b) -> s10 = wz (symaddr Symbols.Ubsan.s_g_file_len) -> sw = (swz =? 1) -> (swz = 0 \/ swz = 1) ->
  0 <= q -> 0 <= cap <= 2040 -> kind sw Fc cap Q = KFit ->
  Z.of_nat (length Fc) < 2 ^ 26 -> b <> 0 -> b + Z.of_nat (length Fc) < 2 ^ 63 ->
  bytes_at rsegs m b Fc -> bytes_at rsegs m (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (Z.of_nat (length Fc)))) ->
  bytes_at rsegs m (sp_h + 56) (le4 (wz swz)) ->
  evt rsegs
    (fun ms' => exists ra' a0' a1' a2' a3' a4' a5' : word,
       ms' = MS (mkR ra' sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 (wz (incl sw Fc Q)) s4 s5
                     (wz (bv_swrap 32 (incl sw Fc Q))) (wz (b + Q)) (wz (Q + 16)) (wz Q) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x270)%Z)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x22c)%Z)) fc None m (seg_rom rsegs)).
Proof.
  intros sw Fc cap q Q RD SK. induction SK as [q K1 K2|q Q KE SK IH|q Q KB SK IH];
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m sp_h b swz HSP E9 E8 E0 E1 E2 E4 E10 ESW HSW Hq HC KQ HN Hb HBN HB HBL H56;
  subst sp_h s9 s8 s0 s1 s2 s4 s10; unfold wz in *;
  pose proof (bytes_at_bound rsegs _ _ _ HB) as BB;
  pose proof (kind_fit _ _ _ _ KQ) as (_ & _ & _ & KQ1 & KQ2); unfold flen in KQ1;
  pose proof (pw_hw_range sw Fc q 8) as RI; change (hw sw Fc q 8) with (incl sw Fc q) in RI;
  pose proof (ul_ro _ _ (C4 (Z_to_bv 64 swz)) H56 I) as R56;
  pose proof (ul_ro _ _ (C8 (Z_to_bv 64 (Z.of_nat (length Fc)))) HBL I) as RL;
  pose proof (zr_word sp) as Rsp; unfold inr64 in Rsp.
  (* skips_stop: the record at q is KFit *)
  1: assert (LQ : q <= q) by lia.
  2: pose proof (ul_kind_empty _ _ _ _ KE) as (KE1 & KE2); pose proof (skips_le _ _ _ _ _ SK) as LQ.
  3: pose proof (ul_kind_big _ _ _ _ KB) as (KB1 & KB2 & KB3); pose proof (skips_le _ _ _ _ _ SK) as LQ.
  all: step; ifc false; step; step; ifc false; do 3 step;
    (eapply evt_cut;
     [ eapply (ul_rd32 RD) with (Fc := Fc) (b := b) (swz := swz) (q := q) (j := 8);
       first [ assumption | (apply ul_sx32_01; assumption) | reflexivity | (f_equal; lia) | lia ]
     | rd_post ]);
    rewrite <- ESW; change (hw sw Fc q 8) with (incl sw Fc q);
    do 3 step; rewrite zx32_val, uns_swrap_mod32_0 by lia;
    step; rewrite eqb_swrap0 by lia.
  - rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv iota. step. ifc true.
    apply evt_done. do 7 eexists. reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _)) by lia. cbv iota.
    do 5 step. ifc false. step.
    eapply IH; first [ reflexivity | exact ESW | exact HSW | exact KQ | exact HB | exact HBL | exact H56
                     | (f_equal; lia) | lia ].
  - rewrite (proj2 (Z.eqb_neq _ _)) by lia. cbv iota. step. ifc false.
    do 5 step. ifc false. step.
    eapply IH; first [ reflexivity | exact ESW | exact HSW | exact KQ | exact HB | exact HBL | exact H56
                     | (f_equal; lia) | lia ].
Qed.

Lemma ul_sh32 : forall I, 0 <= I < 2 ^ 32 ->
  Z_to_bv 64 (I * 2 ^ 32) = Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 (bv_swrap 32 I))) 32).
Proof.
  intros I HI. apply bv_eq.
  rewrite (unsigned_lit_wrap (I * 2 ^ 32)), (unsigned_lit_wrap (Z.shiftl _ 32)). rewrite Z.shiftl_mul_pow2 by lia.
  replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
  rewrite !Z.mul_mod_distr_r by lia. rewrite uns_swrap_mod32_0 by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Ltac zx_eq := rewrite zx32_val; f_equal; rewrite uns_mod32, swrap_add_mod32; rewrite Z.mod_small by lia; lia.

(* Lists of the record: the file copy's bytes and the record buffer. *)
Lemma ul_mcm_firstn : forall n (l r : list byte), (n <= length l)%nat -> (n <= length r)%nat ->
  firstn n l = firstn n r -> memcmp_model l r n = Some 0.
Proof.
  induction n as [|n IH]; intros [|x l] [|y r] Hl Hr E; cbn [length firstn] in *; try lia; try reflexivity.
  injection E as Exy E. subst y. cbn [memcmp_model]. rewrite Z.eqb_refl. cbv iota. apply IH; [lia | lia | exact E].
Qed.

Lemma ul_mcm_pre : forall (P X : list byte) n, length P = n -> memcmp_model (P ++ X) P n = Some 0.
Proof.
  intros P X n H. apply ul_mcm_firstn; [rewrite length_app; lia | lia |].
  rewrite firstn_rec by exact H. rewrite firstn_all2 by lia. reflexivity.
Qed.

Lemma ul_rec_raw_len : forall sw Fc Q, 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  length (rec_raw sw Fc Q) = Z.to_nat (incl sw Fc Q).
Proof.
  intros sw Fc Q HQ HL. pose proof (incl_nonneg sw Fc Q). unfold rec_raw. rewrite length_firstn, length_skipn. lia.
Qed.

Lemma ul_rb_untag : forall sw Fc Q, tagged sw Fc Q = false -> rec_bytes sw Fc Q = rec_raw sw Fc Q.
Proof. intros sw Fc Q T. unfold rec_bytes. cbv zeta. rewrite T. reflexivity. Qed.

Lemma ul_rb_tag : forall sw Fc Q, tagged sw Fc Q = true ->
  rec_bytes sw Fc Q = firstn 12 (rec_raw sw Fc Q) ++ firstn (Z.to_nat (incl sw Fc Q - 16)) (skipn 16 (rec_raw sw Fc Q)) ++
                      skipn (Z.to_nat (incl sw Fc Q - 4)) (rec_raw sw Fc Q).
Proof. intros sw Fc Q T. unfold rec_bytes. cbv zeta. rewrite T. reflexivity. Qed.

Lemma ul_rec_bytes_len : forall sw Fc Q, 0 <= Q -> Q + 16 + incl sw Fc Q <= Z.of_nat (length Fc) ->
  (length (rec_bytes sw Fc Q) <= Z.to_nat (incl sw Fc Q))%nat.
Proof.
  intros sw Fc Q HQ HL. pose proof (ul_rec_raw_len sw Fc Q HQ HL) as LR.
  destruct (tagged sw Fc Q) eqn:T.
  - assert (T18 : 18 <= incl sw Fc Q).
    { unfold tagged in T. apply andb_prop in T as [T _]. apply andb_prop in T as [T _]. apply Z.leb_le in T. exact T. }
    rewrite (ul_rb_tag sw Fc Q T). rewrite !length_app, !length_firstn, !length_skipn, LR. lia.
  - rewrite (ul_rb_untag sw Fc Q T), LR. lia.
Qed.
