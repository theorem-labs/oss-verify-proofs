(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require ImgA.

Module RA_mnbf.
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition memcmp_entry := 0xa2194%Z.
Definition bcmp_entry := 0xa20c4%Z.

(* [comment removed for export] *)
Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
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
  Notation n := (bv_unsigned a2).
  Notation POST := (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m).
  (* [comment removed for export] *)
  Notation ST pc x10 x11 x12 x13 x14 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x10 x11 x12 x13 x14 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).

  #[using="RS LS m"] Lemma bounds : (0 <= A /\ A + Z.of_nat (length ls) <= 2^64 /\ 0 <= B /\ B + Z.of_nat (length rs) <= 2^64)%Z.
  Proof. pose proof (bytes_at_bound _ _ _ _ LS). pose proof (bytes_at_bound _ _ _ _ RS). lia. Qed.

  (* [comment removed for export] *)
  #[using="WM MU RS LS MI"] Lemma memcmp_loop : forall (k' : nat) (i : Z) x13 x14,
    (0 <= i)%Z -> (Z.of_nat (S k') < 2^64)%Z ->
    memcmp_model (skipn (Z.to_nat i) ls) (skipn (Z.to_nat i) rs) (S k') = Some v ->
    evt rsegs POST (ST 0xa2198 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat (S k'))) x13 x14).
  Proof.
    induction k' as [|k' IH]; intros i x13 x14 Hi Hk HW; pose proof bounds as BD;
      cbn [memcmp_model] in HW;
      (destruct (skipn (Z.to_nat i) ls) as [|a l'] eqn:EL; [discriminate|]);
      (destruct (skipn (Z.to_nat i) rs) as [|b r'] eqn:ER; [discriminate|]);
      apply skipn_cons_nth in EL; apply skipn_cons_nth in ER; destruct EL as [Hna ->]; destruct ER as [Hnb ->];
      pose proof (nth_error_lt _ _ _ Hna); pose proof (nth_error_lt _ _ _ Hnb); pose proof (byte_range a); pose proof (byte_range b);
      pose proof (u8ro_read rsegs m A ls i a _ LS Hna ltac:(lia) eq_refl) as RD1;
      pose proof (u8ro_read rsegs m B rs i b _ RS Hnb ltac:(lia) eq_refl) as RD2.
    - zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      + (* [comment removed for export] *) rewrite (proj2 (Z.eqb_neq _ _) Ke) in HW. injection HW as <-.
        zstep. zstep. finish.
      + rewrite (proj2 (Z.eqb_eq _ _) Ke) in HW. injection HW as <-.
        zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz. { exfalso. cbn in Kz. lia. }
        zstep. zstep. finish.
    - zstep. zstep. zstep. if_cases Ke; zify_cond Ke.
      + (* [comment removed for export] *) rewrite (proj2 (Z.eqb_neq _ _) Ke) in HW. injection HW as <-.
        zstep. zstep. finish.
      + rewrite (proj2 (Z.eqb_eq _ _) Ke) in HW.
        zstep. zstep. zstep. zstep. if_cases Kz; zify_cond Kz. 2:{ exfalso. lia. }
        replace (A + i + 1)%Z with (A + (i + 1))%Z by lia. replace (B + i + 1)%Z with (B + (i + 1))%Z by lia.
        replace (Z.of_nat (S (S k')) + -1)%Z with (Z.of_nat (S k')) by lia.
        apply (IH (i + 1)%Z); try lia. replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. exact HW.
  Qed.

  #[using="WM MU RS LS MI"] Lemma memcmp_body :
    memcmp_model ls rs (Z.to_nat n) = Some v ->
    evt rsegs POST (ST 0xa2194 a0 a1 a2 a3 a4).
  Proof.
    intros HM; pose proof bounds as BD.
    pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
    zstep. if_cases K0; zify_cond K0.
    - rewrite K0 in HM. cbn in HM. injection HM as <-. zstep. zstep. finish.
    - destruct (Z.to_nat n) as [|k'] eqn:En; [exfalso; lia|].
      eapply evt_eq.
      2:{ apply (memcmp_loop k' 0 a3 a4); try lia. cbn [Z.to_nat skipn]. exact HM. }
      unfold mkR. rewrite !Z_to_bv_plus0. repeat f_equal. rewrite <- En, Z2Nat.id by lia. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

End Proofs.

Lemma memcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v : Z),
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  mem_inv rsegs m ->
  evt rsegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 ls rs v m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xa2194) fc None m (seg_rom rsegs)).
Proof. intros until v. intros LS RS HM MI. apply memcmp_body; assumption. Qed.

(* [comment removed for export] *)
End RA_mnbf.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.ImgA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.RA_mnbf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp2kv.

Module AIcp4te.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp2kv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@AFA; @AFB; @REALR; @RSTK80; @LOLE'; @CEIL; @CV; @N1; @Hc; @Hj; @SB; @H; @ESL; @H0; @HS2; @RB; @ESF; @H4; @H5; @K3; @SFB; @NGA; @A2R; @SPR; @SHhi; @LBR; @K; @H9; @H10; @QH4; @QH3; @QH2; @QH1; @SHBhi; @LB; @HS1; @H19; @H20; @H14; @H15; @NGB; @K1; @N32; @SEPB; @SEPA; @K4; @LBA; @LB1; @K8])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Section MIC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (real RSTK : Z).
  Hypothesis REALR : (0 <= real < 2^64)%Z.
  Hypothesis REALE : (real mod 2 = 0)%Z.
  Hypothesis RSTK80 : (80 <= RSTK)%Z.
  Hypothesis REALC : mic_real_contract real RSTK.

  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ls rs : list byte) (v lo : Z).
  Notation A := (bv_unsigned a2).
  Notation B := (bv_unsigned a3).
  Notation N := (bv_unsigned a4).
  Notation POST := (mic_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 a3 ls rs v lo RSTK m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -104)
                          [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2192) [CB 2088 fjunk]).
  Hypothesis LOLE : (lo + (2192 + RSTK) <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis HM : memcmp_model ls rs (Z.to_nat N) = Some v.
  Hypothesis N32 : (N < 2^32)%Z.
  Notation SEPAt := ((A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPBt := ((B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z) (only parsing).

  Section Facts.
    (* [comment removed for export] *)
    Variables (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word).
    Notation LBAt := ((lastbA = 0 \/ ((A + N - 1) mod 8 < lastbA <= 7))%Z) (only parsing).
    Notation LBBt := ((lastbB = 0 \/ ((B + N - 1) mod 8 < lastbB <= 7))%Z) (only parsing).
    Hypothesis AFA : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis AFB : (0 <= B /\ B + N + 8 <= 0x800000000000)%Z.
    Hypothesis IRA : inmem_range A N.
    Hypothesis IRB : inmem_range B N.
    Hypothesis NGA : ((A + N - 1) / 8 - A / 8 = Z.of_nat ngA)%Z.
    Hypothesis NGB : ((B + N - 1) / 8 - B / 8 = Z.of_nat ngB)%Z.
    Hypothesis N1 : (1 <= N)%Z.

    Section Phase1.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(bv_unsigned sp - (2192 + RSTK), bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2192).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis LS1 : bytes_at rsegs m1 A ls.
      Hypothesis RS1 : bytes_at rsegs m1 B rs.
      Hypothesis Gcf : ro_cells rsegs m1 0xa9180 [C8 (Z_to_bv 64 0x146ee8)].
      Hypothesis Ccf : ro_cells rsegs m1 0x146fe6 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)].
      Hypothesis CI : ro_cells rsegs m1 0xb6098 [C1 (Z_to_bv 8 1)].
      Hypothesis Crm : ro_cells rsegs m1 0xaaee0 [C8 (Z_to_bv 64 0xa2194)].
      Hypothesis Crb : ro_cells rsegs m1 0xaaee8 [C8 (Z_to_bv 64 0xa20c4)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa9190 [C8 (Z_to_bv 64 0xb53b8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb53b8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa9198 [C8 (Z_to_bv 64 0xb60a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb60a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa91a0 [C8 (Z_to_bv 64 0xb60b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb60b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa91a8 [C8 (Z_to_bv 64 0xb60a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb60a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHA1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]).
      Hypothesis QBA1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1A).
      Hypothesis QBA2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2A).
      Hypothesis SHB1 : bytes_at rsegs m1 (B / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]).
      Hypothesis QBB1 : bytes_at rsegs m1 (sha B - sha B mod 8) (le8 w1B).
      Hypothesis QBB2 : bytes_at rsegs m1 (sha (B + N + -1) - sha (B + N + -1) mod 8) (le8 w2B).


      Section SlowA.
        Variables (sf sl : Z) (x1 x5 x6 x7 x10 x15 x16 x17 x22 x26 x28 x29 x30 x31 : word).
        Hypothesis SEPA : SEPAt. Hypothesis SEPB : SEPBt. Hypothesis LBA : LBAt. Hypothesis LBB : LBBt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngA)%Z.
        Notation AT pc x11 x13 x14 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4
                   x10 x11 (Z_to_bv 64 sl) x13 x14 x15 x16 x17 a3 ra a2 (Z_to_bv 64 real) x22 (Z_to_bv 64 (bv_unsigned sp + -2176))
                   (Z_to_bv 64 0x146ee8) (Z_to_bv 64 (N + -65)) x26 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="LBB LBA SEPB SEPA QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A lastbB lastbA ngB ngA N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_slowA_end : forall x11 x14, evt rsegs POST (AT 0x48c5c x11 (Z_to_bv 64 0) x14).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply mic_p2; try eassumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF LBB LBA SEPB SEPA QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A lastbB lastbA ngB N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_slowA_loop : forall (c : nat) (j : Z) x11 x14,
          Z.to_nat (Z.of_nat ngA - j) = c -> (0 <= j < Z.of_nat ngA)%Z -> x11 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x48c4c x11 (Z_to_bv 64 0) x14).
        Proof.
          induction c as [|c IH]; intros j x11 x14 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHA1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHA1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngA lastbA (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngA)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply mic_slowA_end.
        Qed.
      End SlowA.

      (* [comment removed for export] *)
      #[using="QBB2 QBB1 SHB1 QBA2 QBA1 SHA1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Crb Crm CI Ccf Gcf RS1 LS1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGB NGA IRB IRA AFB AFA w2B w1B w2A w1A ngB ngA N32 HM CEIL LOLE REALC RSTK80 REALE REALR Clg"] Lemma mic_p1 : forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x25 x26 x28 x29 x30 x31,
        SEPAt -> SEPBt -> LBAt -> LBBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp x5 x6 x7 sp a4
                   x10 x11 x12 x13 x14 x15 x16 x17 a3 ra a2 (Z_to_bv 64 real) x22 (Z_to_bv 64 (bv_unsigned sp + -2176))
                   (Z_to_bv 64 0x146ee8) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x48844) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPA SEPB LBA LBB. pose proof LOLE as LOLE'.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a2) as A2R; unfold inr64 in A2R. pose proof (zr_word a3) as A3R; unfold inr64 in A3R.
        pose proof (zr_word a4) as A4R; unfold inr64 in A4R. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
        pose proof (bytes_at_bound _ _ _ _ LS1) as LB. pose proof (bytes_at_bound _ _ _ _ RS1) as RB.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha B - sha B mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (B + N + -1) - sha (B + N + -1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHA1 as SH. remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHB1 as SHB. remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
        assert (SHBhi : (B / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
        { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBA1 as QB1. pose proof QBA2 as QB2. pose proof QBB1 as QB3. pose proof QBB2 as QB4.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          do 3 zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRA
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngA, lastbA; subst sbs; split; [exact NGA| split; [exact SH| exact LBA]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          zstep. zstep.
          zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
          subst sbs sbsB. eapply mic_p2; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + N + -1) 3 <= A + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbA < 128)%Z) by (hs_lbr lastbA).
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ngA) (Z_to_bv 8 lastbA)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngA lastbA ngA), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + N + -1) lastbA) by
              (first [destruct LBA as [LB0|LB1]; [left; exact LB0| right;
                 replace (A + N + -1)%Z with (A + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + N + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngA)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsB.
            zstep. if_cases K8; zify_cond K8.
            * eapply mic_slowA_end; eassumption.
            * eapply mic_slowA_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs sbsB. eapply mic_p2; try eassumption.
      Qed.
    End Phase1.
  End Facts.
End MIC.
End AIcp4te.


Module AIcp1os.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp2kv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp4te.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dl_first | tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] ].
(* [comment removed for export] *)

Section MIC.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (real RSTK : Z).
  Hypothesis REALR : (0 <= real < 2^64)%Z.
  Hypothesis REALE : (real mod 2 = 0)%Z.
  Hypothesis RSTK80 : (80 <= RSTK)%Z.
  Hypothesis REALC : mic_real_contract real RSTK.

  (* [comment removed for export] *)
  Local Ltac zero_tail N0 :=
    let K2 := fresh "K" in let K3 := fresh "K" in let K5 := fresh "K" in let K6 := fresh "K" in let K7 := fresh "K" in let K8 := fresh "K" in
    zstep; rewrite zb_lxor_ones by lia;
    zstep; if_cases K2; zify_cond K2; [exfalso; lia|];
    zstep; zstep;
    zstep; if_cases K3; zify_cond K3; [| exfalso; rewrite N0 in K3; try (generalize alloc_ceiling_val); clear -K3; try pose proof alloc_ceiling_val; cbv in K3; first [lia | discriminate]];
    zstep; if_cases K5; zify_cond K5; [exfalso; lia|];
    zstep;
    zstep; rewrite zb_lxor_ones by lia;
    zstep; if_cases K6; zify_cond K6; [exfalso; lia|];
    zstep;
    zstep; if_cases K7; zify_cond K7; [| exfalso; rewrite N0 in K7; try (generalize alloc_ceiling_val); clear -K7; try pose proof alloc_ceiling_val; cbv in K7; first [lia | discriminate]];
    zstep; if_cases K8; zify_cond K8; [exfalso; lia|];
    zstep.

  #[using="REALC RSTK80 REALE REALR"] Lemma mic_body : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
      (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
    let A := bv_unsigned a2 in let B := bv_unsigned a3 in let N := bv_unsigned a4 in
    bytes_at rsegs m A ls -> bytes_at rsegs m B rs ->
    memcmp_model ls rs (Z.to_nat N) = Some v ->
    mem_inv rsegs m -> mic_cells m ->
    stk rsegs m lo (bv_unsigned sp) -> (lo + (2192 + RSTK) <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
    (A + Z.of_nat (length ls) <= lo \/ bv_unsigned sp <= A)%Z ->
    (B + Z.of_nat (length rs) <= lo \/ bv_unsigned sp <= B)%Z ->
    (N < 2^32)%Z ->
    (N = 0%Z \/ (range_ok m A N /\ range_ok m B N)) ->
    evt rsegs (mic_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 a3 ls rs v lo RSTK m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 real) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x487d0) fc None m (seg_rom rsegs)).
  Proof.
    intros until lo. cbv zeta. intros LS RS HM MI CELLS ST LOLE CEIL SEPA SEPB N32 RNG.
    pose proof CELLS as CELLS'. open_mic_cells CELLS'.
    pose proof (munch_refl [(bv_unsigned sp - (2192 + RSTK), bv_unsigned sp)]%Z m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    pose proof (zr_word a2) as A2R; unfold inr64 in A2R. pose proof (zr_word a3) as A3R; unfold inr64 in A3R.
    pose proof (zr_word a4) as A4R; unfold inr64 in A4R. pose proof (zr_word ra) as RAR; unfold inr64 in RAR.
    pose proof (bytes_at_bound _ _ _ _ LS) as LB. pose proof (bytes_at_bound _ _ _ _ RS) as RB.
    assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
    assert (NW : (bv_unsigned a2 + bv_unsigned a4 < 2^64 /\ bv_unsigned a3 + bv_unsigned a4 < 2^64)%Z).
    { destruct RNG as [N0|((IR1 & _) & (IR2 & _))]; [rewrite N0; lia| unfold inmem_range in IR1, IR2; lia]. }
    destruct (Z.eq_dec (bv_unsigned a4) 0) as [N0 | NZ].
    { (* [comment removed for export] *)
      freeze LS; freeze RS; freeze Gcf; freeze Ccf; freeze CI; freeze Crm; freeze Crb; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
      freeze Gme; freeze Cme; freeze Ghe; freeze Che. clear CELLS MC.
      pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MUp.
      carve_frame 104%nat ST. carve_frame 2088%nat ST.
      do 16 zstep.
      thaw LS MUp WM; thaw RS MUp WM; thaw Gcf MUp WM; thaw Ccf MUp WM; thaw CI MUp WM; thaw Crm MUp WM; thaw Crb MUp WM;
      thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM.
      clear MUp.
      do 5 zstep.
      zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
      zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
      zstep. zstep.
      zstep. if_cases K0'; zify_cond K0'. { exfalso. try (generalize alloc_ceiling_val); clear -K0'; try pose proof alloc_ceiling_val. lia. }
      zero_tail N0. eapply mic_tail; try eassumption; try solve_mic_cells. left; exact N0. }
    (* [comment removed for export] *)
    destruct RNG as [N0 | (RA & RB2)]; [exfalso; lia|].
    assert (N1 : (1 <= bv_unsigned a4)%Z) by lia.
    (first [ dand4 RA as IRA SOKA QWA1 QWA2 | destruct RA as (IRA & SOKA & QWA1 & QWA2) ]). (first [ dand4 RB2 as IRB SOKB QWB1 QWB2 | destruct RB2 as (IRB & SOKB & QWB1 & QWB2) ]).
    assert (AFA : (0 <= bv_unsigned a2 /\ bv_unsigned a2 + bv_unsigned a4 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
    assert (AFB : (0 <= bv_unsigned a3 /\ bv_unsigned a3 + bv_unsigned a4 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
    destruct (mapped8_le8 _ _ QWA1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1A QBA1].
    destruct (mapped8_le8 _ _ QWA2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2A QBA2].
    destruct (mapped8_le8 _ _ QWB1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1B QBB1].
    destruct (mapped8_le8 _ _ QWB2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2B QBB2].
    replace (bv_unsigned a2 + bv_unsigned a4 - 1)%Z with (bv_unsigned a2 + bv_unsigned a4 + -1)%Z in QBA2 by lia.
    replace (bv_unsigned a3 + bv_unsigned a4 - 1)%Z with (bv_unsigned a3 + bv_unsigned a4 + -1)%Z in QBB2 by lia.
    assert (QH1 : (sha (bv_unsigned a2) - sha (bv_unsigned a2) mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (bv_unsigned a2 + bv_unsigned a4 + -1) - sha (bv_unsigned a2 + bv_unsigned a4 + -1) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH3 : (sha (bv_unsigned a3) - sha (bv_unsigned a3) mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH4 : (sha (bv_unsigned a3 + bv_unsigned a4 + -1) - sha (bv_unsigned a3 + bv_unsigned a4 + -1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    (first [ dex2 SOKA as ngA lastbA; dand3 SOKA as NGA SHA LBA | dand5 SOKA as ngA lastbA NGA SHA LBA | destruct SOKA as (ngA & lastbA & NGA & SHA & LBA) ]). (first [ dex2 SOKB as ngB lastbB; dand3 SOKB as NGB SHB LBB | dand5 SOKB as ngB lastbB NGB SHB LBB | destruct SOKB as (ngB & lastbB & NGB & SHB & LBB) ]).
    remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbsA eqn:EsbsA.
    remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
    assert (SHAhi : (bv_unsigned a2 / 8 + shadow_off + Z.of_nat (length sbsA) <= 0x100080000000)%Z).
    { subst sbsA. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    assert (SHBhi : (bv_unsigned a3 / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
    { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    freeze LS; freeze RS; freeze Gcf; freeze Ccf; freeze CI; freeze Crm; freeze Crb; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
    freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SHA; freeze SHB; freeze QBA1; freeze QBA2; freeze QBB1; freeze QBB2. clear CELLS MC.
    pose proof (munch_refl [(bv_unsigned sp - 2192, bv_unsigned sp)]%Z m) as MUp.
    carve_frame 104%nat ST. carve_frame 2088%nat ST.
    do 16 zstep.
    thaw LS MUp WM; thaw RS MUp WM; thaw Gcf MUp WM; thaw Ccf MUp WM; thaw CI MUp WM; thaw Crm MUp WM; thaw Crb MUp WM;
    thaw Gsh MUp WM; thaw Csh MUp WM; thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
    thaw SHA MUp WM; thaw SHB MUp WM; thaw QBA1 MUp WM; thaw QBA2 MUp WM; thaw QBB1 MUp WM; thaw QBB2 MUp WM.
    clear MUp.
    do 5 zstep.
    zstep. zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
    zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. zstep.
    zstep. if_cases K0'; zify_cond K0'. { exfalso. try (generalize alloc_ceiling_val); clear -K0'; try pose proof alloc_ceiling_val. lia. }
    subst sbsA sbsB. eapply mic_p1; try eassumption.
  Qed.
End MIC.
End AIcp1os.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp2kv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp4te OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpoo5.AIcp1os.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LOLE; @SPR; @LO0; @A2R; @CEIL; @H; @Q1; @Q2; @Q3; @Q4; @N0; @IRA; @IRB; @K0; @K1; @SEPA; @SEPB; @NZ; @A0R; @A1R; @N32; @IR])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)

Definition memcmp_icpt_entry : Z := 0x49064.
Definition bcmp_icpt_entry : Z := 0x47a10.
Definition MEMCMP_ICPT_STACK : Z := 2320.
Definition BCMP_ICPT_STACK : Z := 4560.

(* [comment removed for export] *)
Lemma range_ok_repack : forall (m : word -> option byte) a n (ng : nat) (lastb : Z) (w1 w2 : word),
  inmem_range a n -> (1 <= n)%Z ->
  ((a + n - 1) / 8 - a / 8 = Z.of_nat ng)%Z ->
  bytes_at rsegs m (a / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]) ->
  (lastb = 0 \/ ((a + n - 1) mod 8 < lastb <= 7))%Z ->
  bytes_at rsegs m (sha a - sha a mod 8) (le8 w1) ->
  bytes_at rsegs m (sha (a + n + -1) - sha (a + n + -1) mod 8) (le8 w2) ->
  range_ok m a n.
Proof.
  intros m a n ng lastb w1 w2 IR N1 NG SH LB Q1 Q2.
  assert (AF : (0 <= a /\ a + n + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  split; [exact IR|]. split; [exists ng, lastb; split; [exact NG| split; [exact SH| exact LB]]|].
  split; [eapply bytes_at_mapped8; [exact Q1| unfold sha, shadow_off; mlia]|].
  replace (a + n - 1)%Z with (a + n + -1)%Z by lia.
  eapply bytes_at_mapped8; [exact Q2| unfold sha, shadow_off; mlia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma ra_memcmp_real : mic_real_contract 0xa2194 80.
Proof.
  unfold mic_real_contract. intros until lo. intros LS RS HM MI CELLS ST LOLE CEIL SEPA SEPB N32 RNG.
  eapply evt_mono.
  { eapply (memcmp_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v);
      [exact LS| exact RS| exact HM| exact MI]. }
  intros ms' PO. unfold memcmp_post in PO. unfold mic_real_post.
  (first [ dex15 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m'; dand6 PO as E MU WM MI' LS' RS' | dand21 PO as x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 m' E MU WM MI' LS' RS' | destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & E & MU & WM & MI' & LS' & RS') ]).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m'.
  split; [exact E|]. split.
  { eapply munch_weaken; [|exact MU]. intros x _. exact I. }
  split; [exact WM|]. split; [exact MI'|]. split.
  { eapply stk_transport_disjoint; [exact ST| exact MU| exact WM| exact I]. }
  split; [exact LS'| exact RS'].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma memcmp_icpt_spec : mic_real_contract 0x49064 2320.
Proof.
  unfold mic_real_contract. intros until lo. intros LS RS HM MI CELLS ST LOLE CEIL SEPA SEPB N32 RNG.
  pose proof CELLS as CELLS'. open_mic_cells CELLS'. clear CELLS MC.
  pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (bytes_at_bound _ _ _ _ LS) as LB. pose proof (bytes_at_bound _ _ _ _ RS) as RB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (RNGX : exists (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word),
            bv_unsigned a2 = 0%Z \/
            (inmem_range (bv_unsigned a0) (bv_unsigned a2) /\ inmem_range (bv_unsigned a1) (bv_unsigned a2) /\
             ((bv_unsigned a0 + bv_unsigned a2 - 1) / 8 - bv_unsigned a0 / 8 = Z.of_nat ngA)%Z /\
             ((bv_unsigned a1 + bv_unsigned a2 - 1) / 8 - bv_unsigned a1 / 8 = Z.of_nat ngB)%Z /\
             (lastbA = 0 \/ ((bv_unsigned a0 + bv_unsigned a2 - 1) mod 8 < lastbA <= 7))%Z /\
             (lastbB = 0 \/ ((bv_unsigned a1 + bv_unsigned a2 - 1) mod 8 < lastbB <= 7))%Z /\
             bytes_at rsegs m (bv_unsigned a0 / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]) /\
             bytes_at rsegs m (bv_unsigned a1 / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]) /\
             bytes_at rsegs m (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8) (le8 w1A) /\
             bytes_at rsegs m (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8) (le8 w2A) /\
             bytes_at rsegs m (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8) (le8 w1B) /\
             bytes_at rsegs m (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8) (le8 w2B))).
  { destruct RNG as [N0 | ((IRA & SOKA & QWA1 & QWA2) & (IRB & SOKB & QWB1 & QWB2))].
    - exists 0%nat, 0%nat, 0%Z, 0%Z, (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). left. exact N0.
    - assert (AFA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
      assert (AFB : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
      destruct (mapped8_le8 _ _ QWA1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1A QBA1].
      destruct (mapped8_le8 _ _ QWA2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2A QBA2].
      destruct (mapped8_le8 _ _ QWB1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1B QBB1].
      destruct (mapped8_le8 _ _ QWB2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2B QBB2].
      (first [ dex2 SOKA as ngA lastbA; dand3 SOKA as NGA SHA LBA | dand5 SOKA as ngA lastbA NGA SHA LBA | destruct SOKA as (ngA & lastbA & NGA & SHA & LBA) ]). (first [ dex2 SOKB as ngB lastbB; dand3 SOKB as NGB SHB LBB | dand5 SOKB as ngB lastbB NGB SHB LBB | destruct SOKB as (ngB & lastbB & NGB & SHB & LBB) ]).
      exists ngA, ngB, lastbA, lastbB, w1A, w2A, w1B, w2B. right.
      replace (bv_unsigned a0 + bv_unsigned a2 + -1)%Z with (bv_unsigned a0 + bv_unsigned a2 - 1)%Z by lia.
      replace (bv_unsigned a1 + bv_unsigned a2 + -1)%Z with (bv_unsigned a1 + bv_unsigned a2 - 1)%Z by lia.
      repeat (split; [assumption|]). assumption. }
  clear RNG. (first [ dex8 RNGX as ngA ngB lastbA lastbB w1A w2A w1B w2B | dand9 RNGX as ngA ngB lastbA lastbB w1A w2A w1B w2B RNGX | destruct RNGX as (ngA & ngB & lastbA & lastbB & w1A & w2A & w1B & w2B & RNGX) ]).
  (* [comment removed for export] *)
  assert (CASES : bv_unsigned a2 = 0%Z /\ True \/ bv_unsigned a2 <> 0%Z) by lia.
  destruct RNGX as [N0 | (IRA & IRB & NGA & NGB & LBA & LBB & SHA & SHB & QBA1 & QBA2 & QBB1 & QBB2)].
  - (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 8 zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
    zstep. zstep. zstep.
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. cbv in K1. lia. }
    do 5 zstep.
    zstep. call_lit (mic_body 0xa2194 80 ltac:(lia) ltac:(reflexivity) ltac:(lia) ra_memcmp_real) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
      | |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
      | |- memcmp_model _ _ _ = _ => exact HM
      | |- mem_inv _ _ => eassumption
      | |- mic_cells _ => solve_mic_cells
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- (_ = 0%Z \/ _) => left; exact N0
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    do 5 zstep. zstep.
    lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end. finish.
  - (* [comment removed for export] *)
    assert (AFA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
    assert (AFB : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
    pose proof (bytes_at_bound _ _ _ _ QBA1) as Q1. pose proof (bytes_at_bound _ _ _ _ QBA2) as Q2.
    pose proof (bytes_at_bound _ _ _ _ QBB1) as Q3. pose proof (bytes_at_bound _ _ _ _ QBB2) as Q4.
    rewrite length_le8 in Q1, Q2, Q3, Q4.
    assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH3 : (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH4 : (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbsA eqn:EsbsA.
    remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
    assert (SHAhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbsA) <= 0x100080000000)%Z).
    { subst sbsA. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    assert (SHBhi : (bv_unsigned a1 / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
    { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    carve_frame 48%nat ST.
    do 8 zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
    zstep. zstep. zstep.
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. cbv in K1. lia. }
    do 5 zstep.
    subst sbsA sbsB.
    zstep. call_lit (mic_body 0xa2194 80 ltac:(lia) ltac:(reflexivity) ltac:(lia) ra_memcmp_real) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
      | |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
      | |- memcmp_model _ _ _ = _ => exact HM
      | |- mem_inv _ _ => eassumption
      | |- mic_cells _ => solve_mic_cells
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- (_ = 0%Z \/ _) => destruct (Z.eq_dec (bv_unsigned a2) 0) as [E0|NZ]; [left; exact E0| right; split;
             [ eapply (range_ok_repack _ _ _ ngA lastbA w1A w2A); try eassumption; lia
             | eapply (range_ok_repack _ _ _ ngB lastbB w1B w2B); try eassumption; lia ] ]
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    do 5 zstep. zstep.
    lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end. finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bcmp_real : mic_real_contract 0xa20c4 2320.
Proof.
  unfold mic_real_contract. intros until lo. intros LS RS HM MI CELLS ST LOLE CEIL SEPA SEPB N32 RNG.
  pose proof (munch_refl [(bv_unsigned sp - 2320, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  zstep. zstep.
  eapply memcmp_icpt_spec; eassumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bcmp_icpt_spec : mic_real_contract 0x47a10 4560.
Proof.
  unfold mic_real_contract. intros until lo. intros LS RS HM MI CELLS ST LOLE CEIL SEPA SEPB N32 RNG.
  pose proof CELLS as CELLS'. open_mic_cells CELLS'. clear CELLS MC.
  pose proof (munch_refl [(bv_unsigned sp - 4560, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (bytes_at_bound _ _ _ _ LS) as LB. pose proof (bytes_at_bound _ _ _ _ RS) as RB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  assert (RNGX : exists (ngA ngB : nat) (lastbA lastbB : Z) (w1A w2A w1B w2B : word),
            bv_unsigned a2 = 0%Z \/
            (inmem_range (bv_unsigned a0) (bv_unsigned a2) /\ inmem_range (bv_unsigned a1) (bv_unsigned a2) /\
             ((bv_unsigned a0 + bv_unsigned a2 - 1) / 8 - bv_unsigned a0 / 8 = Z.of_nat ngA)%Z /\
             ((bv_unsigned a1 + bv_unsigned a2 - 1) / 8 - bv_unsigned a1 / 8 = Z.of_nat ngB)%Z /\
             (lastbA = 0 \/ ((bv_unsigned a0 + bv_unsigned a2 - 1) mod 8 < lastbA <= 7))%Z /\
             (lastbB = 0 \/ ((bv_unsigned a1 + bv_unsigned a2 - 1) mod 8 < lastbB <= 7))%Z /\
             bytes_at rsegs m (bv_unsigned a0 / 8 + shadow_off) (zeros ngA ++ [Z_to_bv 8 lastbA]) /\
             bytes_at rsegs m (bv_unsigned a1 / 8 + shadow_off) (zeros ngB ++ [Z_to_bv 8 lastbB]) /\
             bytes_at rsegs m (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8) (le8 w1A) /\
             bytes_at rsegs m (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8) (le8 w2A) /\
             bytes_at rsegs m (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8) (le8 w1B) /\
             bytes_at rsegs m (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8) (le8 w2B))).
  { destruct RNG as [N0 | ((IRA & SOKA & QWA1 & QWA2) & (IRB & SOKB & QWB1 & QWB2))].
    - exists 0%nat, 0%nat, 0%Z, 0%Z, (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0). left. exact N0.
    - assert (AFA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
      assert (AFB : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
      destruct (mapped8_le8 _ _ QWA1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1A QBA1].
      destruct (mapped8_le8 _ _ QWA2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2A QBA2].
      destruct (mapped8_le8 _ _ QWB1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1B QBB1].
      destruct (mapped8_le8 _ _ QWB2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2B QBB2].
      (first [ dex2 SOKA as ngA lastbA; dand3 SOKA as NGA SHA LBA | dand5 SOKA as ngA lastbA NGA SHA LBA | destruct SOKA as (ngA & lastbA & NGA & SHA & LBA) ]). (first [ dex2 SOKB as ngB lastbB; dand3 SOKB as NGB SHB LBB | dand5 SOKB as ngB lastbB NGB SHB LBB | destruct SOKB as (ngB & lastbB & NGB & SHB & LBB) ]).
      exists ngA, ngB, lastbA, lastbB, w1A, w2A, w1B, w2B. right.
      replace (bv_unsigned a0 + bv_unsigned a2 + -1)%Z with (bv_unsigned a0 + bv_unsigned a2 - 1)%Z by lia.
      replace (bv_unsigned a1 + bv_unsigned a2 + -1)%Z with (bv_unsigned a1 + bv_unsigned a2 - 1)%Z by lia.
      repeat (split; [assumption|]). assumption. }
  clear RNG. (first [ dex8 RNGX as ngA ngB lastbA lastbB w1A w2A w1B w2B | dand9 RNGX as ngA ngB lastbA lastbB w1A w2A w1B w2B RNGX | destruct RNGX as (ngA & ngB & lastbA & lastbB & w1A & w2A & w1B & w2B & RNGX) ]).
  (* [comment removed for export] *)
  assert (CASES : bv_unsigned a2 = 0%Z /\ True \/ bv_unsigned a2 <> 0%Z) by lia.
  destruct RNGX as [N0 | (IRA & IRB & NGA & NGB & LBA & LBB & SHA & SHB & QBA1 & QBA2 & QBB1 & QBB2)].
  - (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 8 zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
    zstep. zstep. zstep.
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. cbv in K1. lia. }
    do 5 zstep.
    zstep. call_lit (mic_body 0xa20c4 2320 ltac:(lia) ltac:(reflexivity) ltac:(lia) bcmp_real) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
      | |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
      | |- memcmp_model _ _ _ = _ => exact HM
      | |- mem_inv _ _ => eassumption
      | |- mic_cells _ => solve_mic_cells
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- (_ = 0%Z \/ _) => left; exact N0
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    do 5 zstep. zstep.
    lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end. finish.
  - (* [comment removed for export] *)
    assert (AFA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRA; lia).
    assert (AFB : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRB; lia).
    pose proof (bytes_at_bound _ _ _ _ QBA1) as Q1. pose proof (bytes_at_bound _ _ _ _ QBA2) as Q2.
    pose proof (bytes_at_bound _ _ _ _ QBB1) as Q3. pose proof (bytes_at_bound _ _ _ _ QBB2) as Q4.
    rewrite length_le8 in Q1, Q2, Q3, Q4.
    assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH2 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2A)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH3 : (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w1B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    assert (QH4 : (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2B)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
    remember (zeros ngA ++ [Z_to_bv 8 lastbA]) as sbsA eqn:EsbsA.
    remember (zeros ngB ++ [Z_to_bv 8 lastbB]) as sbsB eqn:EsbsB.
    assert (SHAhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbsA) <= 0x100080000000)%Z).
    { subst sbsA. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    assert (SHBhi : (bv_unsigned a1 / 8 + shadow_off + Z.of_nat (length sbsB) <= 0x100080000000)%Z).
    { subst sbsB. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
    zstep. (* [comment removed for export] *)
    carve_frame 48%nat ST.
    do 8 zstep.
    zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ eassumption. }
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
    zstep. zstep. zstep.
    zstep. call_lit tryinit_spec by (idtac;
      lazymatch goal with
      | |- asan_inited_cell _ => exact CI
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. zstep.
    zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. cbv in K1. lia. }
    do 5 zstep.
    subst sbsA sbsB.
    zstep. call_lit (mic_body 0xa20c4 2320 ltac:(lia) ltac:(reflexivity) ltac:(lia) bcmp_real) by (idtac;
      lazymatch goal with
      | |- bytes_at _ _ (bv_unsigned a0) _ => exact LS
      | |- bytes_at _ _ (bv_unsigned a1) _ => exact RS
      | |- memcmp_model _ _ _ = _ => exact HM
      | |- mem_inv _ _ => eassumption
      | |- mic_cells _ => solve_mic_cells
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; eassumption
      | |- (_ = 0%Z \/ _) => destruct (Z.eq_dec (bv_unsigned a2) 0) as [E0|NZ]; [left; exact E0| right; split;
             [ eapply (range_ok_repack _ _ _ ngA lastbA w1A w2A); try eassumption; lia
             | eapply (range_ok_repack _ _ _ ngB lastbB w1B w2B); try eassumption; lia ] ]
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    do 5 zstep. zstep.
    lazymatch goal with ST' : stk rsegs _ lo _ |- _ => release_frame FR ST' (bv_unsigned sp) end. finish.
Qed.

End CEIL.
