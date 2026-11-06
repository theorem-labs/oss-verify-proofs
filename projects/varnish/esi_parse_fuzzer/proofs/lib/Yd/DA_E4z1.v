(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AGlofzw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Ey6n DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import ExN ExW.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@Cbase; @Ccan; @Cinit; @Creal; @Crep; @Cthr; @REC; @RECB]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stepobi.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.astep_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.azstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stepobi.af_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)

Definition LOOP_HEAD : Z := 0x45528.
Definition AFTER_MEMSET : Z := 0x45510.
Definition LOOP_END : Z := 0x4572c.

(* [comment removed for export] *)
Definition grec_ok (r : grec) : Prop :=
  g_beg r mod 32 = 0 /\ 0x10000 <= g_beg r /\ g_beg r + g_size_rz r <= IMGHI /\ 0 <= g_size r <= g_size_rz r
  /\ g_size_rz r mod 32 = 0 /\ 0 < g_size_rz r < 0x80000
  /\ (g_beg r + g_size_rz r <= GMETA \/ GMETA + 64 * Z.of_nat GCOUNT <= g_beg r)
  /\ (g_odr r = 2^64 - 1 \/ ODRLO <= g_odr r < ODRHI).

Lemma grec_ok_of_b : forall r, grec_okb r = true -> grec_ok r.
Proof.
  intros r H. unfold grec_okb in H. unfold grec_ok, IMGHI, GMETA, GCOUNT, ODRLO, ODRHI in *.
  repeat (apply andb_prop in H as [H ?X]).
  apply Z.eqb_eq in H. apply Z.leb_le in X8. apply Z.leb_le in X7. apply Z.leb_le in X6. apply Z.leb_le in X5.
  apply Z.eqb_eq in X4. apply Z.ltb_lt in X3. apply Z.ltb_lt in X2.
  apply Bool.orb_prop in X0. apply Bool.orb_prop in X.
  assert (D1 : g_beg r + g_size_rz r <= 711712 \/ 711712 + 64 * Z.of_nat 259%nat <= g_beg r)
    by (destruct X0 as [X0|X0]; apply Z.leb_le in X0; lia).
  assert (D2 : g_odr r = 2^64 - 1 \/ 6191744 <= g_odr r < 6191810).
  { destruct X as [X|X]; [left; apply Z.eqb_eq in X; exact X| right].
    apply andb_prop in X as [X9 X10]. apply Z.leb_le in X9. apply Z.ltb_lt in X10. lia. }
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
Qed.

Lemma g_has_odr_false : forall r, grec_ok r -> g_has_odr r = false -> g_odr r = 2^64 - 1.
Proof.
  intros r OK Hh. unfold g_has_odr in Hh. apply andb_false_iff in Hh. unfold grec_ok, ODRLO, ODRHI in OK.
  destruct Hh as [Hh|Hh]; apply Bool.negb_false_iff in Hh; apply Z.eqb_eq in Hh; lia.
Qed.
Lemma g_has_odr_true : forall r, grec_ok r -> g_has_odr r = true -> ODRLO <= g_odr r < ODRHI.
Proof.
  intros r OK Hh. unfold g_has_odr in Hh. apply andb_prop in Hh as [H1 H2]. unfold grec_ok in OK.
  apply Bool.negb_true_iff in H1. apply Z.eqb_neq in H1. lia.
Qed.

(* [comment removed for export] *)
Lemma ro_cells_byte_of : forall m A cs k b,
  ro_cells rsegs m A cs -> nth_error (cells_bytes cs) k = Some b ->
  ro_cells rsegs m (A + Z.of_nat k) [C1 b].
Proof.
  intros m A cs k b [Hwf (Ha & Hl & Hb)] Hk.
  assert (Hlen : (k < length (cells_bytes cs))%nat).
  { apply (proj1 (nth_error_Some (cells_bytes cs) k)). rewrite Hk. discriminate. }
  split; [cbn; exact (conj I I)|].
  split; [lia|]. split; [cbn [cells_bytes cbytes app length]; lia|].
  intros i Hi. cbn [cells_bytes cbytes app length] in Hi. cbn [cells_bytes cbytes app].
  replace i with 0%nat by lia. cbn [nth_error]. rewrite Z.add_0_r. rewrite <- Hk. apply Hb. exact Hlen.
Qed.

Lemma grec_byte16 : forall m P r,
  ro_cells rsegs m P (grec_cells r) -> ro_cells rsegs m (P + 16) [C1 (Z_to_bv 8 (g_size_rz r mod 256))].
Proof.
  intros m P r H. apply (ro_cells_byte_of m P (grec_cells r) 16). exact H.
  cbn [grec_cells cells_bytes cbytes app nth_error le8]. unfold le8, word_to_le_bytes. cbn [Z_to_le_bytes app nth_error]. f_equal.
  rewrite Z_to_bv_unsigned. change (bv_wrap 64 (g_size_rz r)) with (g_size_rz r mod 2^64).
  apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8). cbn [Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  rewrite (Z.mod_mod_divide _ (2^64) (2^8)) by (exists (2^56); reflexivity).
  change 256 with (2^8). rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition body1_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : grec) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s0' m',
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (Z_to_bv 64 AFTER_MEMSET) fc None m' (seg_rom rsegs)
    /\ munch [(gsh (g_beg r), gsh (g_beg r) + g_size_rz r / 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ rw_cells rsegs m' (gsh (g_beg r)) [CB (Z.to_nat (g_size_rz r / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (g_size_rz r / 8)))].

Section Body1.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (r : grec) (P k : Z) (shjunk : list byte).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ROK : grec_ok r.
  Hypothesis PLO : 0xadc20 <= P.
  Hypothesis PHI : P + 64 <= 0xb1ce0.   (* [comment removed for export] *)
  Hypothesis S1 : s1 = Z_to_bv 64 0x146ee8.
  Hypothesis S2 : s2 = Z_to_bv 64 2.
  Hypothesis S4 : s4 = Z_to_bv 64 P.
  Hypothesis S7 : s7 = Z_to_bv 64 0xab038.
  Hypothesis S9 : s9 = Z_to_bv 64 0xb2bb8.
  Hypothesis S10 : s10 = Z_to_bv 64 0xb53b8.
  Hypothesis Crep : ro_cells rsegs m 0xb2bd0 [C4 (Z_to_bv 64 1)].
  Hypothesis Cthr : ro_cells rsegs m 0x146f60 [C8 (Z_to_bv 64 18446744073709551615)].
  Hypothesis Cbase : ro_cells rsegs m 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
  Hypothesis Cinit : ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)].
  Hypothesis Ccan : ro_cells rsegs m 0xb4c1c [C1 (Z_to_bv 8 1)].
  Hypothesis Creal : ro_cells rsegs m 0xab038 [C8 (Z_to_bv 64 0xa25c8)].
  Hypothesis REC : ro_cells rsegs m P (grec_cells r).
  Hypothesis SH : rw_cells rsegs m (gsh (g_beg r)) [CB (Z.to_nat (g_size_rz r / 8)) shjunk].

  #[using="SH REC Creal Ccan Cinit Cbase Cthr Crep S10 S9 S7 S4 S2 S1 ROK MI shjunk P"] Lemma unreg_body1 :
    evt rsegs (body1_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LOOP_HEAD) fc None m (seg_rom rsegs)).
  Proof.
    pose proof (grec_byte16 m P r REC) as RECB.
    subst s1 s2 s4 s7 s9 s10. unfold LOOP_HEAD.
    pose proof ROK as OK. unfold grec_ok, IMGHI, GMETA, GCOUNT, ODRLO, ODRHI in OK.
    (first [ dand8 OK as Ob32 Oblo Obhi Osz Orz32 Orz Ometa Oodr | destruct OK as (Ob32 & Oblo & Obhi & Osz & Orz32 & Orz & Ometa & Oodr) ]).
    unfold grec_cells in REC.
    assert (L7 : Z.land (g_beg r) 7 = 0) by (apply land7_of_mod8; lia).
    assert (L7b : Z.land (g_size_rz r mod 256) 7 = 0) by (apply land7_of_mod8; lia).
    pose proof (munch_refl [(gsh (g_beg r), gsh (g_beg r) + g_size_rz r / 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    run_to 0x45564. at_pc 0x45564. azstep. br_taken. at_pc 0x45648.
    (* [comment removed for export] *)
    azstep. rewrite L7. run_to 0x45654. azstep. rewrite (unsigned_lit8 (g_size_rz r mod 256)) by lia. rewrite L7b.
    (* [comment removed for export] *)
    run_to 0x45694. at_pc 0x45694.
    assert (E1 : Z.shiftr (g_beg r) 3 = g_beg r / 8) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
    assert (E2 : Z.shiftr (g_beg r + g_size_rz r + -8) 3 = g_beg r / 8 + g_size_rz r / 8 - 1).
    { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. lia. }
    rewrite E1, E2. clear E1 E2.
    match goal with |- context [Z_to_bv 64 (?x mod 18446744073709551616 - ?y mod 18446744073709551616)] =>
      replace (Z_to_bv 64 (x mod 18446744073709551616 - y mod 18446744073709551616)) with (Z_to_bv 64 (g_size_rz r / 8)) by word_eq_tac end.
    replace (Z_to_bv 64 (2147450880 + g_beg r / 8)) with (Z_to_bv 64 (gsh (g_beg r))) by (unfold gsh; f_equal; lia).
    azstep. br_taken. at_pc 0x45504.
    azstep. azstep. azstep. at_pc 0xa25c8.
    call memset_spec_z. 1:{ exact SH. } 1: lia. 1: lia. 1:{ unfold gsh; lia. } 1:{ exact MI. }
    unfold body1_post, AFTER_MEMSET. finish.
  Qed.
End Body1.

(* [comment removed for export] *)
Definition next_pc (k : Z) : Z := if Z.eqb k 1 then LOOP_END else LOOP_HEAD.

Definition body2_post (sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (P k : Z) (W : list (Z * Z)) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (P + 64)) s5 s6 s7 s8 s9 s10
                  (Z_to_bv 64 (k - 1)) t3' t4' t5' t6')
             F (Z_to_bv 64 (next_pc k)) fc None m' (seg_rom rsegs)
    /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section Body2.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (r : grec) (P k : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ROK : grec_ok r.
  Hypothesis PLO : 0xadc20 <= P.
  Hypothesis PHI : P + 64 <= 0xb1ce0.   (* [comment removed for export] *)
  Hypothesis K1 : 1 <= k <= 259.
  Hypothesis S2 : s2 = Z_to_bv 64 2.
  Hypothesis S4 : s4 = Z_to_bv 64 P.
  Hypothesis S11 : s11 = Z_to_bv 64 k.
  Hypothesis REC : ro_cells rsegs m P (grec_cells r).

  #[using="REC S11 S4 S2 K1 ROK MI"] Lemma unreg_body2_noodr : g_has_odr r = false ->
    evt rsegs (body2_post sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 F fc P k [] m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFTER_MEMSET) fc None m (seg_rom rsegs)).
  Proof.
    intros Hno. pose proof (g_has_odr_false r ROK Hno) as Hodr.
    subst s2 s4 s11. unfold AFTER_MEMSET. unfold grec_cells in REC.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. rewrite Hodr. azstep. azstep. if_false. azstep. azstep. at_pc 0x45524.
    azstep. if_cases K; zify_cond K.
    - unfold body2_post, next_pc. replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia). unfold LOOP_END. finish.
    - unfold body2_post, next_pc. replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia). unfold LOOP_HEAD. finish.
  Qed.

  #[using="REC S11 S4 S2 K1 PHI ROK MI"] Lemma unreg_body2_odr : forall b, g_has_odr r = true ->
    rw_cells rsegs m (g_odr r) [C1 b] ->
    evt rsegs (fun ms' => body2_post sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 F fc P k [(g_odr r, g_odr r + 1)] m ms'
                         /\ rw_cells rsegs (ms_mem ms') (g_odr r) [C1 (Z_to_bv 8 0)])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFTER_MEMSET) fc None m (seg_rom rsegs)).
  Proof.
    intros b Hyes OD. pose proof (g_has_odr_true r ROK Hyes) as Hodr. unfold ODRLO, ODRHI in Hodr.
    subst s2 s4 s11. unfold AFTER_MEMSET. unfold grec_cells in REC.
    pose proof (munch_refl [(g_odr r, g_odr r + 1)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
    azstep. azstep. azstep. br_taken. at_pc 0x455dc.
    azstep. azstep. azstep. at_pc 0x455e8.
    azstep. if_cases K; zify_cond K.
    - apply evt_done. split; [| cbn [ms_mem]; assumption].
      unfold body2_post, next_pc. replace (k =? 1) with false by (symmetry; apply Z.eqb_neq; lia). unfold LOOP_HEAD.
      hot_eexists_all. split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    - azstep. apply evt_done. split; [| cbn [ms_mem]; assumption].
      unfold body2_post, next_pc. replace (k =? 1) with true by (symmetry; apply Z.eqb_eq; lia). unfold LOOP_END.
      hot_eexists_all. split; [reflexivity|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
End Body2.

(* [comment removed for export] *)
Definition odrW (r : grec) : list (Z * Z) := if g_has_odr r then [(g_odr r, g_odr r + 1)] else [].
Definition godr1 (m : word -> option byte) (r : grec) : Prop := g_has_odr r = true -> exists b, rw_cells rsegs m (g_odr r) [C1 b].

Lemma unreg_body2 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : grec) (P k : Z),
  mem_inv rsegs m -> grec_ok r -> 0xadc20 <= P -> P + 64 <= 0xb1ce0 -> 1 <= k <= 259 ->
  s2 = Z_to_bv 64 2 -> s4 = Z_to_bv 64 P -> s11 = Z_to_bv 64 k ->
  ro_cells rsegs m P (grec_cells r) -> godr1 m r ->
  evt rsegs (fun ms' => body2_post sp gp tp s0 s1 s2 s3 s5 s6 s7 s8 s9 s10 F fc P k (odrW r) m ms' /\ godr1 (ms_mem ms') r)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 AFTER_MEMSET) fc None m (seg_rom rsegs)).
Proof.
  intros until k. intros MI ROK PLO PHI K1 S2 S4 S11 REC GO. unfold odrW, godr1 in *.
  destruct (g_has_odr r) eqn:HO.
  - destruct (GO eq_refl) as [b OD].
    eapply evt_mono. { eapply unreg_body2_odr; eassumption. }
    intros ms' [PO OD']. split; [exact PO|]. intros _. exists (Z_to_bv 8 0). exact OD'.
  - eapply evt_mono. { eapply unreg_body2_noodr; eassumption. }
    intros ms' PO. split; [exact PO|]. intros; discriminate.
Qed.

Lemma gdisj_shadow : forall r r2, grec_ok r -> grec_ok r2 -> gdisjb r r2 = true ->
  disjoint_from [(gsh (g_beg r), gsh (g_beg r) + g_size_rz r / 8)] (gsh (g_beg r2)) (g_size_rz r2 / 8).
Proof.
  intros r r2 OK OK2 D. unfold grec_ok in OK, OK2. unfold gdisjb in D. apply andb_prop in D as [D _].
  apply Bool.orb_prop in D. cbn [disjoint_from]. split; [|exact I]. unfold gsh.
  destruct D as [D|D]; apply Z.leb_le in D; [right|left].
  - (* [comment removed for export] *)
    assert (g_beg r / 8 + g_size_rz r / 8 <= g_beg r2 / 8) by (Z.div_mod_to_equations; lia). lia.
  - assert (g_beg r2 / 8 + g_size_rz r2 / 8 <= g_beg r / 8) by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma gdisj_odr : forall r r2, gdisjb r r2 = true -> g_has_odr r = true -> g_has_odr r2 = true -> g_odr r2 <> g_odr r.
Proof.
  intros r r2 D H1 H2. unfold gdisjb in D. apply andb_prop in D as [_ D]. rewrite H1, H2 in D. cbn in D.
  apply Bool.negb_true_iff in D. apply Z.eqb_neq in D. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uconsts (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xb2bd0 [C4 (Z_to_bv 64 1)] /\ ro_cells rsegs m 0x146f60 [C8 (Z_to_bv 64 18446744073709551615)]
  /\ ro_cells rsegs m 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)] /\ ro_cells rsegs m 0xb6098 [C1 (Z_to_bv 8 1)]
  /\ ro_cells rsegs m 0xb4c1c [C1 (Z_to_bv 8 1)] /\ ro_cells rsegs m 0xab038 [C8 (Z_to_bv 64 0xa25c8)].
(* [comment removed for export] *)
Definition godrs (m : word -> option byte) (l : list grec) : Prop :=
  Forall (fun r => g_has_odr r = true -> exists b, rw_cells rsegs m (g_odr r) [C1 b]) l.
(* [comment removed for export] *)
Definition META_SH : Z := 0x8000db84.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition WL : list (Z * Z) := [(0x7fffa000, 0x8000db84); (0x8000e39c, 0x800c8c00); (0x5e7a80, 0x5e7ac2)].
(* [comment removed for export] *)

Lemma ro_cells_app_inv : forall m A cs1 cs2,
  ro_cells rsegs m A (cs1 ++ cs2) -> ro_cells rsegs m A cs1 /\ ro_cells rsegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2 [Hwf Hb]. apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [B1 B2].
  rewrite cells_bytes_length in B2 by exact W1.
  split; split; assumption.
Qed.

Lemma gsepb_app : forall l1 l2, gsepb (l1 ++ l2) = true -> gsepb l2 = true.
Proof. induction l1 as [|r l1 IH]; intros l2 H; [exact H|]. cbn [gsepb app] in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma gtab_suffix_facts : forall done r rest, gtab = done ++ r :: rest ->
  grec_ok r /\ Forall (fun r2 => gdisjb r r2 = true) rest /\ Forall grec_ok rest
  /\ (length done + S (length rest) = 259)%nat.
Proof.
  intros done r rest E.
  pose proof gtab_ok as OK. pose proof gtab_sep as SEP. pose proof gtab_length as LEN. rewrite E in OK, SEP, LEN.
  rewrite forallb_app in OK. apply andb_prop in OK as [_ OK]. cbn [forallb] in OK. apply andb_prop in OK as [OKr OKrest].
  apply gsepb_app in SEP. cbn [gsepb] in SEP. apply andb_prop in SEP as [SEPr _].
  rewrite length_app in LEN. cbn [length] in LEN. unfold GCOUNT in LEN.
  split; [apply grec_ok_of_b; exact OKr|]. split.
  - apply Forall_forall. intros x Hx. exact (proj1 (forallb_forall _ _) SEPr x Hx).
  - split; [|lia]. apply Forall_forall. intros x Hx. apply grec_ok_of_b. exact (proj1 (forallb_forall _ _) OKrest x Hx).
Qed.

(* [comment removed for export] *)
Lemma uconsts_transport : forall W m m', munch W m m' ->
  (forall A n, A + n <= 0x200000 -> disjoint_from W A n) -> uconsts m -> uconsts m'.
Proof.
  (intros W m m' MU HD; (first [ intro dR_7; dand6 dR_7 as C1 C2 C3 C4 C5 C6 | intros (C1 & C2 & C3 & C4 & C5 & C6) ])). unfold uconsts.
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; (eapply ro_cells_transport; [eassumption | exact MU | apply HD; cbn; lia]).
Qed.

Lemma gshadows_transport : forall W m m' l bss, munch W m m' -> wmono rsegs m m' ->
  Forall (fun r2 => disjoint_from W (gsh (g_beg r2)) (g_size_rz r2 / 8)) l ->
  Forall grec_ok l ->
  gshadows m l bss -> gshadows m' l bss.
Proof.
  intros W m m' l bss MU WM HD OK G. unfold gshadows in *.
  revert bss G. induction l as [|r l IH]; intros bss G; inversion G; subst; constructor.
  - eapply rw_cells_transport; [eassumption | exact MU | exact WM |].
    cbn [gchunk cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id. 2:{ inversion OK; subst. unfold grec_ok in *. apply Z.div_pos; lia. }
    inversion HD; subst. assumption.
  - apply IH; [inversion HD; subst; assumption | inversion OK; subst; assumption | assumption].
Qed.

Lemma godrs_transport : forall W m m' l, munch W m m' -> wmono rsegs m m' ->
  Forall (fun r2 => g_has_odr r2 = true -> disjoint_from W (g_odr r2) 1) l ->
  godrs m l -> godrs m' l.
Proof.
  intros W m m' l MU WM HD G. unfold godrs in *. rewrite Forall_forall in *.
  intros r Hr Ho. destruct (G r Hr Ho) as [b Hb]. exists b.
  eapply rw_cells_transport; [exact Hb | exact MU | exact WM | exact (HD r Hr Ho)].
Qed.

Definition loop_post (sp gp tp s1 s2 s3 s5 s6 s7 s8 s9 s10 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s0' m',
    ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 (GMETA + 64 * 259)) s5 s6 s7 s8 s9 s10
                  (Z_to_bv 64 0) t3' t4' t5' t6')
             F (Z_to_bv 64 0x4572c) fc None m' (seg_rom rsegs)
    /\ munch [(0x7fffa000, 0x8000db84); (0x8000e39c, 0x800c8c00); (0x5e7a80, 0x5e7ac2)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Lemma unreg_loop : forall rest done bss
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  gtab = done ++ rest -> rest <> [] ->
  mem_inv rsegs m -> uconsts m ->
  s1 = Z_to_bv 64 0x146ee8 -> s2 = Z_to_bv 64 2 -> s4 = Z_to_bv 64 (GMETA + 64 * Z.of_nat (length done)) ->
  s7 = Z_to_bv 64 0xab038 -> s9 = Z_to_bv 64 0xb2bb8 -> s10 = Z_to_bv 64 0xb53b8 ->
  s11 = Z_to_bv 64 (Z.of_nat (length rest)) ->
  ro_cells rsegs m (GMETA + 64 * Z.of_nat (length done)) (gtab_cells rest) ->
  gshadows m rest bss -> godrs m rest ->
  evt rsegs (loop_post sp gp tp s1 s2 s3 s5 s6 s7 s8 s9 s10 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 LOOP_HEAD) fc None m (seg_rom rsegs)).
Proof.
  induction rest as [|r rest IH]; intros done bss ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m E NE MI UC S1 S2 S4 S7 S9 S10 S11 TAB GS GO; [congruence|].
  (first [ pose proof ((gtab_suffix_facts done r rest E)) as dR_2; dand4 dR_2 as OKr SEPr OKrest LEN | destruct (gtab_suffix_facts done r rest E) as (OKr & SEPr & OKrest & LEN) ]).
  pose proof OKr as OK'. unfold grec_ok, IMGHI, GMETA, GCOUNT, ODRLO, ODRHI in OK'.
  (* [comment removed for export] *)
  cbn [gtab_cells] in TAB. apply ro_cells_app_inv in TAB as [REC TAB']. 
  change (cells_size (grec_cells r)) with 64%nat in TAB'.
  unfold gshadows in GS. inversion GS as [|r_ bs_ rest_ bss' SH GS' E1 E2]; subst. fold (gshadows m rest bss') in GS'.
  assert (GO' : godrs m rest) by (inversion GO; assumption).
  assert (GOr : g_has_odr r = true -> exists b, rw_cells rsegs m (g_odr r) [C1 b]) by (inversion GO; assumption).
  (first [ dand6 UC as U1 U2 U3 U4 U5 U6 | destruct UC as (U1 & U2 & U3 & U4 & U5 & U6) ]).
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply unreg_body1 with (r := r) (P := GMETA + 64 * Z.of_nat (length done));
      try eassumption; try reflexivity; unfold GMETA; cbn [length] in LEN; try lia. }
  intros ms1 PO1. (first [ dex18 PO1 as ra1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 s01 m1; dand5 PO1 as -> MU1 WM1 MI1 SH1 | dand23 PO1 as ra1 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 s01 m1 -> MU1 WM1 MI1 SH1 | destruct PO1 as (ra1 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & s01 & m1 & -> & MU1 & WM1 & MI1 & SH1) ]).
  (* [comment removed for export] *)
  assert (HDimg1 : forall A n, A + n <= 0x60a000 -> disjoint_from [(gsh (g_beg r), gsh (g_beg r) + g_size_rz r / 8)] A n).
  { intros A n H. cbn [disjoint_from]. unfold gsh. split; [|exact I]. left. Z.div_mod_to_equations. lia. }
  cbn [length] in LEN.
  assert (UC1 : uconsts m1).
  { eapply (uconsts_transport _ m m1 MU1); [intros; apply HDimg1; lia|]. exact (conj U1 (conj U2 (conj U3 (conj U4 (conj U5 U6))))). }
  assert (REC1 : ro_cells rsegs m1 (GMETA + 64 * Z.of_nat (length done)) (grec_cells r)).
  { eapply ro_cells_transport; [exact REC | exact MU1 |]. apply HDimg1. cbn [grec_cells cells_size csize Nat.add]. unfold GMETA. lia. }
  assert (TAB1 : ro_cells rsegs m1 (GMETA + 64 * Z.of_nat (length done) + Z.of_nat 64) (gtab_cells rest)).
  { eapply ro_cells_transport; [exact TAB' | exact MU1 |]. apply HDimg1. rewrite gtab_cells_size. unfold GMETA. lia. }
  assert (GS1 : gshadows m1 rest bss').
  { eapply gshadows_transport; [exact MU1 | exact WM1 | | exact OKrest | exact GS'].
    apply Forall_forall. intros r2 Hr2. apply gdisj_shadow; [exact OKr | exact (proj1 (Forall_forall _ _) OKrest r2 Hr2) | exact (proj1 (Forall_forall _ _) SEPr r2 Hr2)]. }
  assert (GO1 : godrs m1 rest).
  { eapply godrs_transport; [exact MU1 | exact WM1 | | exact GO'].
    apply Forall_forall. intros r2 Hr2 Ho2. apply HDimg1. pose proof (g_has_odr_true r2 (proj1 (Forall_forall _ _) OKrest r2 Hr2) Ho2). unfold ODRHI in *. lia. }
  assert (GOr1 : godr1 m1 r).
  { intros Ho. destruct (GOr Ho) as [b OD]. exists b. eapply rw_cells_transport; [exact OD | exact MU1 | exact WM1 |].
    apply HDimg1. cbn [cells_size csize Nat.add]. pose proof (g_has_odr_true r OKr Ho). unfold ODRHI in *. lia. }
  clear U1 U2 U3 U4 U5 U6 GS GS' GO GO' GOr SH HDimg1 REC TAB'.
  (* [comment removed for export] *)
  eapply evt_cut.
  { eapply unreg_body2 with (r := r) (P := GMETA + 64 * Z.of_nat (length done)) (k := Z.of_nat (S (length rest)));
      try eassumption; try reflexivity; unfold GMETA; try lia. }
  intros ms2 [PO2 GOr2]. (first [ dex17 PO2 as ra2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2; dand4 PO2 as -> MU2 WM2 MI2 | dand21 PO2 as ra2 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 m2 -> MU2 WM2 MI2 | destruct PO2 as (ra2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & y8 & y9 & y10 & y11 & y12 & y13 & y14 & m2 & -> & MU2 & WM2 & MI2) ]).
  cbn [ms_mem] in GOr2.
  (* [comment removed for export] *)
  assert (HDimg2 : forall A n, A + n <= ODRLO -> disjoint_from (odrW r) A n).
  { intros A n H. unfold odrW. destruct (g_has_odr r) eqn:Ho; cbn [disjoint_from]; [|exact I].
    split; [|exact I]. left. pose proof (g_has_odr_true r OKr Ho). lia. }
  assert (UC2 : uconsts m2) by (eapply (uconsts_transport _ m1 m2 MU2); [intros; apply HDimg2; unfold ODRLO; lia| exact UC1]).
  assert (TAB2 : ro_cells rsegs m2 (GMETA + 64 * Z.of_nat (length done) + Z.of_nat 64) (gtab_cells rest)).
  { eapply ro_cells_transport; [exact TAB1 | exact MU2 |]. apply HDimg2. rewrite gtab_cells_size. unfold GMETA, ODRLO. lia. }
  assert (GS2 : gshadows m2 rest bss').
  { eapply gshadows_transport; [exact MU2 | exact WM2 | | exact OKrest | exact GS1].
    apply Forall_forall. intros r2 Hr2. unfold odrW. destruct (g_has_odr r) eqn:Ho; cbn [disjoint_from]; [|exact I]. split; [|exact I].
    right. pose proof (g_has_odr_true r OKr Ho). pose proof (proj1 (Forall_forall _ _) OKrest r2 Hr2) as OK2. unfold grec_ok, gsh, ODRLO, ODRHI in *.
    Z.div_mod_to_equations. lia. }
  assert (GO2 : godrs m2 rest).
  { eapply godrs_transport; [exact MU2 | exact WM2 | | exact GO1].
    apply Forall_forall. intros r2 Hr2 Ho2. unfold odrW. destruct (g_has_odr r) eqn:Ho; cbn [disjoint_from]; [|exact I]. split; [|exact I].
    pose proof (gdisj_odr r r2 (proj1 (Forall_forall _ _) SEPr r2 Hr2) Ho Ho2). lia. }
  clear UC1 GS1 GO1 GOr1 REC1 TAB1 HDimg2.
  (* [comment removed for export] *)
  assert (MU12 : munch WL m m2); unfold WL.
  { eapply munch_trans.
    - eapply munch_weaken; [|exact MU1]. unfold sub_fp, WL. cbn [outside]. unfold gsh, LOWSH_LO, LOWSH_HI, META_SH. intros x Hx.
      assert (g_beg r / 8 + g_size_rz r / 8 <= 711712 / 8 \/ 728288 / 8 <= g_beg r / 8) by (Z.div_mod_to_equations; lia).
      Z.div_mod_to_equations. lia.
    - eapply munch_weaken; [|exact MU2]. unfold sub_fp, WL, odrW. destruct (g_has_odr r) eqn:Ho; cbn [outside]; [|tauto].
      pose proof (g_has_odr_true r OKr Ho). unfold LOWSH_LO, LOWSH_HI, META_SH, ODRLO, ODRHI in *. intros x Hx. lia. }
  pose proof (wmono_trans rsegs m m1 m2 WM1 WM2) as WM12.
  destruct rest as [|r' rest'].
  - (* [comment removed for export] *)
    apply evt_done. unfold loop_post, next_pc, LOOP_END. cbn [length] in LEN.
    replace (Z.of_nat (S (length [])) =? 1) with true by reflexivity.
    replace (Z.of_nat (S (length [])) - 1) with 0 by reflexivity.
    replace (GMETA + 64 * Z.of_nat (length done) + 64) with (GMETA + 64 * 259) by lia.
    hot_eexists_all. split; [reflexivity|]. split; [exact MU12|]. split; [exact WM12| exact MI2].
  - (* [comment removed for export] *)
    unfold next_pc. replace (Z.of_nat (S (length (r' :: rest'))) =? 1) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
    eapply evt_mono.
    { eapply (IH (done ++ [r]) bss'); try reflexivity.
      - rewrite <- app_assoc. exact E.
      - discriminate.
      - exact MI2.
      - exact UC2.
      - f_equal. rewrite length_app. cbn [length]. lia.
      - f_equal. cbn [length]. lia.
      - replace (GMETA + 64 * Z.of_nat (length (done ++ [r]))) with (GMETA + 64 * Z.of_nat (length done) + Z.of_nat 64)
          by (rewrite length_app; cbn [length]; lia). exact TAB2.
      - exact GS2.
      - exact GO2. }
    intros ms3 PO3. unfold loop_post in *.
    (first [ dex18 PO3 as ra3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 s03 m3; dand4 PO3 as -> MU3 WM3 MI3 | dand22 PO3 as ra3 z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 s03 m3 -> MU3 WM3 MI3 | destruct PO3 as (ra3 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & z14 & s03 & m3 & -> & MU3 & WM3 & MI3) ]).
    hot_eexists_all. split; [reflexivity|].
    split; [exact (munch_trans _ _ _ _ MU12 MU3)|]. split; [exact (wmono_trans rsegs _ _ _ WM12 WM3)| exact MI3].
Qed.
