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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition strcmp_entry := 0x2b60c%Z.

Definition strcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (ls rs : list byte) (v : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 v) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ bytes_at rsegs m' (bv_unsigned a0) ls /\ bytes_at rsegs m' (bv_unsigned a1) rs.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v : Z).
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis LS : bytes_at rsegs m (bv_unsigned a0) ls.
  Hypothesis RS : bytes_at rsegs m (bv_unsigned a1) rs.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono rsegs m m := wmono_refl rsegs m.

  Notation A := (bv_unsigned a0).
  Notation B := (bv_unsigned a1).
  Notation POST := (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).
  (* [comment removed for export] *)
  Notation ST pc x10 x11 x12 x13 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  #[using="RS LS m"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  (* [comment removed for export] *)
  Lemma walk_at : forall i r, strcmp_walk (skipn i ls) (skipn i rs) = Some r ->
    exists a b, nth_error ls i = Some a /\ nth_error rs i = Some b /\
      (if ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%Z%bool
       then r = (bv_unsigned a - bv_unsigned b)%Z
       else strcmp_walk (skipn (S i) ls) (skipn (S i) rs) = Some r).
  Proof.
    intros i r H.
    destruct (skipn i ls) as [|a l'] eqn:EL; [cbn in H; discriminate|].
    destruct (skipn i rs) as [|b r'] eqn:ER; [cbn in H; discriminate|].
    apply skipn_cons_nth in EL. apply skipn_cons_nth in ER. destruct EL as [Hna ->]. destruct ER as [Hnb ->].
    exists a, b. split; [exact Hna|]. split; [exact Hnb|].
    cbn [strcmp_walk] in H.
    destruct ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%Z%bool; [congruence| exact H].
  Qed.

  (* [comment removed for export] *)
  #[using="WM MU RS LS MI"] Lemma strcmp_ret : forall (a b : byte) x10 x11,
    v = (bv_unsigned a - bv_unsigned b)%Z ->
    evt rsegs POST (ST 0x2b63c x10 x11 (Z_to_bv 64 (bv_unsigned a)) (Z_to_bv 64 (bv_unsigned b))).
  Proof.
    intros a b x10 x11 Hv. pose proof (byte_range a). pose proof (byte_range b).
    zstep. zstep. subst v. finish.
  Qed.

  (* [comment removed for export] *)
  #[using="WM MU RS LS MI"] Lemma strcmp_loop : forall (k : nat) (i : Z) x12 x13,
    (0 <= i)%Z -> (length ls - Z.to_nat i = k)%nat ->
    strcmp_walk (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) = Some v ->
    evt rsegs POST (ST 0x2b624 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) x12 x13).
  Proof.
    induction k as [|k IH]; intros i x12 x13 Hi Hk HW; pose proof bounds as BD;
      (first [ pose proof ((walk_at _ _ HW)) as dR_1; dex2 dR_1 as a b; dand3 dR_1 as Hna Hnb HC | pose proof ((walk_at _ _ HW)) as dR_1; dand5 dR_1 as a b Hna Hnb HC | destruct (walk_at _ _ HW) as (a & b & Hna & Hnb & HC) ]);
      pose proof (nth_error_lt _ _ _ Hna); pose proof (nth_error_lt _ _ _ Hnb); [exfalso; lia|].
    pose proof (byte_range a). pose proof (byte_range b).
    pose proof (u8ro_read rsegs m A ls i a _ LS Hna ltac:(lia) eq_refl) as RD1.
    pose proof (u8ro_read rsegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD2.
    zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
    - (* [comment removed for export] *) rewrite Kz in HC. cbn [Z.eqb orb] in HC. apply strcmp_ret. rewrite Kz. exact HC.
    - zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_eq _ _) Ke) in HC. cbn [orb negb] in HC.
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
        apply (IH (i + 1)%Z); try lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HC.
      + rewrite (proj2 (Z.eqb_neq _ _) Kz) in HC.
        replace (negb (bv_unsigned a =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Ke).
        cbn [orb] in HC. apply strcmp_ret. exact HC.
  Qed.

  #[using="WM MU RS LS MI"] Lemma strcmp_body :
    strcmp_walk ls rs = Some v ->
    evt rsegs POST (ST 0x2b60c a0 a1 a2 a3).
  Proof.
    intros HM; pose proof bounds as BD.
    rewrite <- (skipn_O ls), <- (skipn_O rs) in HM.
    (first [ pose proof ((walk_at _ _ HM)) as dR_2; dex2 dR_2 as a b; dand3 dR_2 as Hna Hnb HC | pose proof ((walk_at _ _ HM)) as dR_2; dand5 dR_2 as a b Hna Hnb HC | destruct (walk_at _ _ HM) as (a & b & Hna & Hnb & HC) ]).
    pose proof (nth_error_lt _ _ _ Hna). pose proof (nth_error_lt _ _ _ Hnb). pose proof (byte_range a). pose proof (byte_range b).
    pose proof (u8ro_read rsegs m A ls 0 a a0 LS Hna ltac:(lia) (eq_sym (Z_to_bv_plus0 a0))) as RD1.
    pose proof (u8ro_read rsegs m B rs 0 b a1 RS Hnb ltac:(lia) (eq_sym (Z_to_bv_plus0 a1))) as RD2.
    zstep. zstep. zstep. if_cases Kz; zify_cond Kz.
    - rewrite Kz in HC. cbn [Z.eqb orb] in HC. apply strcmp_ret. rewrite Kz. exact HC.
    - zstep. if_cases Ke; zify_cond Ke.
      + rewrite (proj2 (Z.eqb_neq _ _) Kz) in HC.
        replace (negb (bv_unsigned a =? bv_unsigned b))%Z with true in HC by (symmetry; apply negb_true_iff, Z.eqb_neq; exact Ke).
        cbn [orb] in HC. apply strcmp_ret. exact HC.
      + rewrite (proj2 (Z.eqb_neq _ _) Kz), (proj2 (Z.eqb_eq _ _) Ke) in HC. cbn [orb negb] in HC.
        zstep. zstep.
        apply (strcmp_loop (length ls - 1) 1); try lia. cbn [Z.to_nat Pos.to_nat]. exact HC.
  Qed.
End Proofs.

Lemma strcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  strcmp_walk ls rs = Some v ->
  mem_inv rsegs m ->
  evt rsegs (strcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2b60c) fc None m (seg_rom rsegs)).
Proof. intros until v. intros LS RS HM MI. apply strcmp_body; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
